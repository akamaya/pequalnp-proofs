# P=NP solver tools

開発専用の `solver-tools` ブランチ。提出用の `main` や upstream にはマージしないこと。
このブランチの作業ツリーには自動証明ツールだけを置く。公開forkなので認証情報、ログ、RAGインデックス、未提出の証明は登録しない。

## 初回 (WSL)
```bash
git clone --single-branch --branch solver-tools https://github.com/akamaya/pequalnp-proofs.git "$HOME/dev/pequalnp-tools" && bash "$HOME/dev/pequalnp-tools/install.sh"
```

## 更新 (実行中の探索を終了してから)
```bash
git -C "$HOME/dev/pequalnp-tools" pull --ff-only && bash "$HOME/dev/pequalnp-tools/install.sh"
```

既存の `~/dev/LeanDojo-v2` にバージョン付きファイルと固定名のエントリポイントをコピーする。変更のある既存ファイルはバックアップする。既存venv、RAG、ログ、公式スクリプト、認証環境変数は変更しない。公式スクリプト `pnp_current.sh` は従来どおり upstream から管理する。

## 現行版

- LLM + RAG: `leandojo_local_smoke.py` (v25)
- 自動問題取得・専用ソルバー・提出: `pnp_autorun.py` (v6)
- 真理値表ソルバー: `pnp_table_solve_v2.py`
- グラフソルバー: `pnp_graph_solve_v1.py` と依存モジュール
- 証明エクスポート: `leandojo_export_proof_v3.py`
- 証明監査: `pnp_proof_audit_v1.py`

## 確認

```bash
python3 "$HOME/dev/LeanDojo-v2/pnp_autorun.py" --self-test
```

```bash
cd "$HOME/dev/pequalnp-proofs/lean" && lake env "$HOME/dev/LeanDojo-v2/.venv/bin/python" -u "$HOME/dev/LeanDojo-v2/leandojo_local_smoke.py" --engine-test-only
```

既存の実行コマンドはバージョン付きファイル名を固定名に変更するだけで利用できる。自動提出は従来どおり明示的な --submit を要する。SATソルバーは今後の開発対象で、初回コミットには含まれない。RAG構築ツール・インデックス・公式提出スクリプトは既存環境を利用する。

## SAT探索（実験版、v1）

`pnp_sat_solve_v1.py` は公式 `PEqualNP.Defs.LratEncoding.enc2` のPython移植。
非空グラフの単調辺関数を対象に、最小真入力と極大偽入力のみを使う。
SATモデルは全入力で独立検査する。UNSATはソルバー結果でありLean証明ではない。
L-meta-2260の構造仮定は未符号化。一般回路のSAT結果だけでは当該定理への反例とはならない。

既存のLLM探索と並行して、専用venvで実行できる。install.sh は不要。

```bash
cd "$HOME/dev/pequalnp-tools" && python3 -m venv .venv-sat && .venv-sat/bin/python -m pip install python-sat
```

```bash
cd "$HOME/dev/pequalnp-tools" && nice -n 10 .venv-sat/bin/python -u pnp_sat_solve_v1.py --self-test --seconds 10
```

```bash
cd "$HOME/dev/pequalnp-tools" && nice -n 10 .venv-sat/bin/python -u pnp_sat_solve_v1.py --case l2260 --gates 21 --seconds 30 --solver g4
```

TIMEOUT は正常な未解決終了。--no-lex で公式 enc と比較可能。
--full-rows で全真理値表、--dimacs FILE でCNF保存、--json-out FILE で結果保存。
この版はLinux/WSL向けで、PythonのforkプロセスによりSAT探索時間を制限する。
実行環境での自己テストを先に行うこと。LRAT生成・Lean照合・公式提出は未実装。

## SAT v2（比較実験）

v1の36ケースはWSLで全てPASS。L-meta-2260 (21 gates, enc2, Glucose4) は40 rows、207518 clauses、max var 362095、CNF build 0.309 s、30 s TIMEOUT。

v2は変数番号を連続化する dense、セレクタに exactly-one を加える onehot、さらに TopForm と相互に依存する2個の junk AND を制約する topform の3プロファイル。topform は定理の全仮定ではなく一部のみを符号化する。SATの回路は全真理値表と構造を独立に検査する。いずれも証明書のLean照合は未実装。dense以外は追加制約の正当性を正式証明する必要がある。

```bash
git -C "$HOME/dev/pequalnp-tools" pull --ff-only && cd "$HOME/dev/pequalnp-tools" && nice -n 10 .venv-sat/bin/python -u pnp_sat_solve_v2.py --self-test --seconds 10
```

```bash
cd "$HOME/dev/pequalnp-tools" && nice -n 10 .venv-sat/bin/python -u pnp_sat_solve_v2.py --case l2260 --gates 21 --compare --seconds 10 --solver g4
```

6パターンを順番に実行。全てTIMEOUTなら約1分強。v1は変更しない。v2の実機テストは未実施。
