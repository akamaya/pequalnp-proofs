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

## SAT v3（L-meta-2260の構造制約と途中統計）

v2実機テスト26ケースPASS。21ゲート、40入力行では6方式すべて10秒TIMEOUT。dense/enc2は3561変数、207518節、dense/encは3561変数、67083節。topform/encは3750変数、83845節。

v3の star プロファイルは v2 topform に h4 (OR到達入力とstar側条件)、h5 (Ustarの辺ごとのjunkへのOR到達と真理値)、h7 (削除後のグラフの頂点被覆)、h6の弱い版 (非負のorN\\lam項を省略) を追加。IsLeastAOの最小性そのものとh6の完全版は未符号化。SAT時は全真理値表とこれらの構造制約を独立評価する。UNSATは実験結果のみ。Lean証明書は未実装。

```bash
git -C "$HOME/dev/pequalnp-tools" pull --ff-only && cd "$HOME/dev/pequalnp-tools" && nice -n 10 .venv-sat/bin/python -u pnp_sat_solve_v3.py --self-test --seconds 10
```

```bash
cd "$HOME/dev/pequalnp-tools" && nice -n 10 .venv-sat/bin/python -u pnp_sat_solve_v3.py --case l2260 --gates 21 --compare --seconds 20
```

比較はtopform/star × Glucose4/CaDiCaL、encのみ、各20秒。conf_budget/solve_limitedによる途中統計をTIMEOUT時にも保持する。ソルバーによって対応状況は異なる。v3は実機未検証。v1/v2は変更しない。

## SAT v4（h6 完全版）

v3 WSL self-test PASS。20秒比較は全てTIMEOUT。衝突回数 topform/g4=362830, topform/cadical195=208305, star/g4=283199, star/cadical195=149215。衝突回数は解決までの進捗率ではない。

v4 full は orN, lam, orN\\lam の厳密なカウントを h6 に追加する。OR closure は始点のゲート自身を含み、ORのみ通過する。単一入力の側を厳密に判定し、lam の所属を双方向に符号化。SAT時は独立評価でも検査する。既知回路のh6境界とlamの正の所属の強制モデルテストを追加した。v4はWSL未検証。

```bash
git -C "$HOME/dev/pequalnp-tools" pull --ff-only && cd "$HOME/dev/pequalnp-tools" && nice -n 10 .venv-sat/bin/python -u pnp_sat_solve_v4.py --self-test --seconds 10
```

```bash
cd "$HOME/dev/pequalnp-tools" && nice -n 10 .venv-sat/bin/python -u pnp_sat_solve_v4.py --case l2260 --gates 21 --profile full --no-lex --seconds 60 --solver g4 --chunk 20000
```

--compare は star/full × g4/cadical195。--chunk は各 solve_limited の衝突予算。IsLeastAOの最小性そのものと、Lean側の符号化の正当性・UNSAT証明書検証は未実装。v1〜v3は変更しない。
