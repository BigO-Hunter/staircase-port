#!/usr/bin/env python3
"""Fetch exact formal_statements of isPiv_rank1_lower / isPiv_mid / edge_of_pivs from
prove2.me search results (statements come inline; no solution-file fetches needed).
Token re-minted via POST /agent/refresh; written back to credentials.json. NEVER prints secrets.
401 -> re-mint + retry once. Saves to /private/tmp/staircase-port/extract/statements/*.json"""
import json, pathlib, sys, urllib.request, urllib.parse, urllib.error

WS = pathlib.Path.home() / "prove2me_workspace"
OUT = pathlib.Path("/private/tmp/staircase-port/extract/statements")
OUT.mkdir(parents=True, exist_ok=True)
creds = json.loads((WS / "credentials.json").read_text())

def post(url, body):
    req = urllib.request.Request(url, data=json.dumps(body).encode(),
                                 headers={"Content-Type": "application/json"}, method="POST")
    with urllib.request.urlopen(req, timeout=60) as r:
        return json.loads(r.read().decode())

def mint():
    resp = post("https://prove2.me/api/v1/agent/refresh", {"api_key": creds["api_key"]})
    tok = resp.get("access_token") or resp.get("data", {}).get("access_token")
    if not tok:
        print("REFRESH FAILED (keys only):", list(resp)); sys.exit(1)
    creds["access_token"] = tok
    (WS / "credentials.json").write_text(json.dumps(creds, indent=2))
    return tok

def get(url, token):
    req = urllib.request.Request(url, headers={"Authorization": f"Bearer {token}"})
    with urllib.request.urlopen(req, timeout=120) as r:
        return json.loads(r.read().decode())

token = mint()
QUERIES = ["isPiv_rank1_lower", "isPiv_mid", "edge_of_pivs", "isPiv_side", "data_edge"]
found = {}
for q in QUERIES:
    url = "https://prove2.me/api/v1/theorems?q=" + urllib.parse.quote(q)
    for attempt in (0, 1):
        try:
            d = get(url, token)
            break
        except urllib.error.HTTPError as e:
            if e.code == 401 and attempt == 0:
                token = mint()
                continue
            print(f"q={q} FAILED {e.code}"); d = None; break
    if not d:
        continue
    for t in d.get("theorems", []):
        name = t.get("theorem_name") or ""
        if any(s in name for s in QUERIES):
            found[name] = {"theorem_id": t.get("theorem_id"), "status": t.get("status"),
                           "formal_statement": t.get("formal_statement", "")}

(OUT / "pivot_statements.json").write_text(json.dumps(found, indent=2))
for name, v in sorted(found.items()):
    fs = v["formal_statement"]
    print(f"{name} [{v['status']}] {v['theorem_id'][:12]} stmt_chars={len(fs)}")
