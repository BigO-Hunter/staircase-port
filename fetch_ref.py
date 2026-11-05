#!/usr/bin/env python3
"""Fetch reference platform bodies into ~/bigo-campaign/sp-n52/ref/. Never prints secrets."""
import json, pathlib, sys, urllib.request, urllib.parse

WS = pathlib.Path.home() / "prove2me_workspace"
OUT = pathlib.Path.home() / "bigo-campaign/sp-n52/ref"
OUT.mkdir(parents=True, exist_ok=True)


def post(url, body):
    req = urllib.request.Request(url, data=json.dumps(body).encode(),
                                 headers={"Content-Type": "application/json"}, method="POST")
    with urllib.request.urlopen(req, timeout=60) as r:
        return json.loads(r.read().decode())


def get(url, token):
    req = urllib.request.Request(url, headers={"Authorization": f"Bearer {token}"})
    with urllib.request.urlopen(req, timeout=120) as r:
        return json.loads(r.read().decode())


creds = json.loads((WS / "credentials.json").read_text())
resp = post("https://prove2.me/api/v1/agent/refresh", {"api_key": creds["api_key"]})
token = resp.get("access_token") or resp.get("data", {}).get("access_token")
creds["access_token"] = token
(WS / "credentials.json").write_text(json.dumps(creds, indent=2))
print("token re-minted")


def get_retry(url):
    global token
    try:
        return get(url, token)
    except urllib.error.HTTPError as e:
        if e.code != 401:
            raise
        r = post("https://prove2.me/api/v1/agent/refresh", {"api_key": creds["api_key"]})
        token = r.get("access_token") or r.get("data", {}).get("access_token")
        creds["access_token"] = token
        (WS / "credentials.json").write_text(json.dumps(creds, indent=2))
        print("401 -> re-minted")
        return get(url, token)


wanted = sys.argv[1:] or ["NB_flag_gen", "NB_flagBasis", "NB_data_edge"]

hits = {}
for q in wanted + ["R6.Bit.NB"]:
    try:
        d = get_retry("https://prove2.me/api/v1/theorems?q=" + urllib.parse.quote(q))
        for t in d.get("theorems", []):
            hits[t["theorem_id"]] = (t.get("theorem_name"), t.get("status"))
    except Exception as e:
        print(f"search q={q} failed:", e)
print(f"{len(hits)} theorem hits")
for q in wanted:
    cands = [tid for tid, (name, st) in hits.items() if name and q.lower() in name.lower()]
    print(f"[{q}] {[(hits[t][0], hits[t][1]) for t in cands]}")
    for tid in cands:
        try:
            s = get_retry(
                f"https://prove2.me/api/v1/theorems/{tid}/submissions?status=ACCEPTED,SKETCH_ACCEPTED")
            subs = s.get("submissions", [])
            if not subs:
                s = get_retry(f"https://prove2.me/api/v1/theorems/{tid}/submissions")
                subs = s.get("submissions", [])
                subs = [x for x in subs if x.get("status") in ("ACCEPTED", "SKETCH_ACCEPTED")]
        except Exception as e:
            print(f"  subs failed {tid[:12]}:", e)
            continue
        done = False
        for sub in subs:
            sid = sub.get("submission_id") or sub.get("id")
            try:
                sol = get_retry(f"https://prove2.me/api/v1/submissions/{sid}/solution")
            except Exception as e:
                print(f"  sol failed {sid[:12]}:", e)
                continue
            content = sol.get("content") or ""
            if not content:
                print(f"  sub {sid[:12]}: empty, keys={list(sol.keys())}")
                continue
            p = OUT / f"{q}_solution.lean"
            p.write_text(content)
            print(f"SAVED {p.name} <- {hits[tid][0]} sub {sid[:12]} {sub.get('status')} "
                  f"{len(content)} chars {content.count(chr(10))+1} lines")
            (OUT / f"{q}_sub_meta.json").write_text(json.dumps(
                {"theorem_id": tid, "theorem_name": hits[tid][0], "submission_id": sid,
                 "status": sub.get("status"), "file_path": sol.get("file_path")}, indent=1))
            done = True
            break
        if done:
            break
