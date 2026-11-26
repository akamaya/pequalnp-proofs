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

## SAT v5（並列 cube-and-conquer / checkpoint）

v4 WSL自己テストPASS。L-meta-2260 full/enc, g4, chunk=20000, 60秒TIMEOUT。13063変数、162365節、構築0.365秒、58.086秒時点で572947 conflicts / 204337742 propagations。

v5はv4のCNFをそのまま使用し、正確に2個のdirty ANDがあることを利用して、後方のdirty gateの位置で20個に分割（21スロットの場合）。--split pair なら210個。全cubeをUNSATと判定した場合のみ全体UNSATとする。個々のcubeにunit clausesを加え、CPUプロセスを並列実行する。チェックポイントはCNFとcube定義のSHA256で照合し、UNSAT済みcubeをスキップする。TIMEOUTは次回に最初から再探索（学習節の保存なし）。SAT時はv4独立検査を行う。チェックポイントは信頼済みの自分の実験ファイルだけを使うこと。Lean証明書ではない。

```bash
git -C "$HOME/dev/pequalnp-tools" pull --ff-only && cd "$HOME/dev/pequalnp-tools" && nice -n 10 .venv-sat/bin/python -u pnp_sat_solve_v5.py --self-test --seconds 10
```

```bash
cd "$HOME/dev/pequalnp-tools" && nice -n 10 .venv-sat/bin/python -u pnp_sat_solve_v5.py --case l2260 --gates 21 --jobs 4 --seconds 8 --checkpoint sat-results/l2260-v5-second.json
```

同じコマンドで再開。--seconds を増やす、--solver cadical195 に変えることは可能。split/profile/lexを変更する場合は別checkpointを使う。v5実機テスト未実施。提出用mainとv1〜v4は変更しない。

## SAT v6（最小回路の冗長ゲート排除）

v5実測: 21ゲート / second分割20個 / 4並列 / 8秒ずつ、41.508秒。second-20のみUNSAT、19個TIMEOUT。

v6では IsLeastAO の必要条件を追加。ANDだけ、またはORだけを通る依存経路で比較可能な2入力を同時に読むゲートは、吸収律により片方の入力へ置換できるので最小回路には存在しない。--prune absorb-dup は同一演算・同一入力対の重複ゲートも排除。--prune none はv5相当。既知の最小回路が残ること、直接/間接吸収と重複回路が排除されることを確認する自己テストを追加。Leanでの正当性の形式化は未実施。

```bash
git -C "$HOME/dev/pequalnp-tools" pull --ff-only && cd "$HOME/dev/pequalnp-tools" && nice -n 10 .venv-sat/bin/python -u pnp_sat_solve_v6.py --self-test --seconds 10
```

```bash
cd "$HOME/dev/pequalnp-tools" && nice -n 10 .venv-sat/bin/python -u pnp_sat_solve_v6.py --case l2260 --gates 21 --jobs 4 --seconds 8 --prune absorb --checkpoint sat-results/l2260-v6-absorb.json
```

```bash
cd "$HOME/dev/pequalnp-tools" && nice -n 10 .venv-sat/bin/python -u pnp_sat_solve_v6.py --case l2260 --gates 21 --jobs 4 --seconds 8 --prune absorb-dup --checkpoint sat-results/l2260-v6-absorb-dup.json
```

CNF変更のためv5のcheckpointを流用しない。v6はWSL未検証。探索結果は実験用で、Lean証明書ではない。

## SAT v7（TopForm 出力OR網の除去）

v6実測: absorb 185980節 / 13945変数、42.002秒、1/20 UNSAT。absorb-dup 250310節 / 13945変数、42.490秒、1/20 UNSAT。排除できたのはいずれもsecond-20のみ。v6自己テストPASS。

v7は最小TopForm AO2回路を対象に、clean ORによる出力網をSAT探索から除き、top ANDの個数kで分割する。非空単純グラフの辺関数では入力自身はcleanでない。clean ORの両入力はcleanなので、ORをたどるとtop ANDに達する。TopFormと全ゲートの出力到達性から、これらのclean ORおよびtop ANDはANDの入力側に存在しない。最小回路の出力OR網はk-1ゲートに置換可能であり、残りのゲートを並べ替え、末尾にk個のtop ANDを置く。出力OR網はSATモデル復元時に追加する。21ゲートならk=1..10、内部スロット数=22-k。h6のサイズ項にk-1を加算して計算する。v4の独立検証を復元した全回路に対して実行する。

この正規化とCNFの健全性はまだLeanで証明していない。UNSATは実験結果のみ。v7実機未検証。v1〜v6および提出用mainは変更しない。

```bash
git -C "$HOME/dev/pequalnp-tools" pull --ff-only && cd "$HOME/dev/pequalnp-tools" && nice -n 10 .venv-sat/bin/python -u pnp_sat_solve_v7.py --self-test --seconds 10
```

```bash
cd "$HOME/dev/pequalnp-tools" && nice -n 10 .venv-sat/bin/python -u pnp_sat_solve_v7.py --case l2260 --gates 21 --jobs 4 --seconds 20 --checkpoint sat-results/l2260-v7-tops.json
```

k=10から1へ探索。既定は追加のv6冗長ゲート制約なし。UNSAT済みのkは同じcheckpointで再実行時にスキップする。TIMEOUTは再探索。--top-count K で個別ケースの実験が可能（checkpointなし）。チェックポイントは信頼済みの実験ファイルのみ使うこと。

## SAT v8（private edge / 境界真理値表による意味的冗長性排除）

v7 WSL実測: self-test PASS、21ゲート、4並列、20秒ずつ、50.39秒。k=10 UNSAT (0.102秒, 67619節)、k=9 UNSAT (8.918秒, 76155節)、k=1..8 TIMEOUT。

v8はv7の縮約CNFに最小回路の必要条件を追加する。privateモード: 各top ANDは他のtop ANDが真にならない固有の辺入力を少なくとも1つ持つ。そうでなければ出力ORから取り除いて小さい回路にできる。semanticモード（既定）: さらに各実ゲートの二つの入力が境界真理値表上で両方向に異なる行を持つことを要求。比較可能なら片方の入力でゲートを置換でき、最小真行・極大偽行で同じ出力となる単調回路は全入力で同じ辺関数を計算する。noneは追加制約なし。Leanでの正当性の形式化は未実施。v8実機未検証。

```bash
git -C "$HOME/dev/pequalnp-tools" pull --ff-only && cd "$HOME/dev/pequalnp-tools" && nice -n 10 .venv-sat/bin/python -u pnp_sat_solve_v8.py --self-test --seconds 10
```

```bash
cd "$HOME/dev/pequalnp-tools" && nice -n 10 .venv-sat/bin/python -u pnp_sat_solve_v8.py --case l2260 --gates 21 --jobs 4 --seconds 30 --mode semantic --seed-v7 sat-results/l2260-v7-tops.json --checkpoint sat-results/l2260-v8-semantic.json
```

v7のチェックポイントはfingerprintを照合したうえでUNSATのみ引継ぎ可能（CNFに制約を追加してもUNSATは維持）。証明書を検証した結果ではなく、信頼済みのローカル実験結果である。TIMEOUTは最初から探索。v1〜v7と提出用mainは変更しない。

## SAT v9（2個のjunk ANDを名前付き原子に分離）

v8 WSL self-test PASS、v7のk=9,10を継承し、k=1..8は全て30秒TIMEOUT。62.052秒。追加のprivate edge/semantic制約による新規UNSATは得られなかった。

v9は別のCNF符号化。OR回路をn個の入力と2個のjunk ANDを原子とする集合の和集合DAGとして表現する。ORゲートごとの40行の真理値評価を省き、2+k個のANDにだけ行値を持つ。ORの配線は依然探索する。junk0の入力集合はjunk原子を含めず、junk1はjunk0のみを含められ、少なくとも片側がjunk0を含む。これにより循環を防ぐ。top ANDは末尾に置き、出力OR網は復元する。

h4の各starから中心を1個選べばstarEdgesの頂点被覆となるのでh7のSAT変数は不要。内部ORは全てdirty。active OR数をm、top AND数をk、centreless数をc、Lambda数をl、被覆辺数をb、全辺数をEとすると、h6は base+k+c+m-l <= 2k+1+m+E-b、すなわち c+b-l <= k+1+E-base。L-meta-2260では c+b <= k+l。LambdaのOR到達は出力側から逆方向に厳密に符号化。復元回路はv4の全真理値表・構造検査に渡す。

v9はv7/v8のCNFとは別物なのでcheckpointは引き継がない。既知のh6境界・Lambda所属の強制モデルと小規模SAT/UNSATの自己テストを追加。実機未検証、正規化と符号化のLean形式化は未完成、UNSATは実験結果のみ。

```bash
git -C "$HOME/dev/pequalnp-tools" pull --ff-only && cd "$HOME/dev/pequalnp-tools" && nice -n 10 .venv-sat/bin/python -u pnp_sat_solve_v9.py --self-test --seconds 10
```

```bash
cd "$HOME/dev/pequalnp-tools" && nice -n 10 .venv-sat/bin/python -u pnp_sat_solve_v9.py --case l2260 --gates 21 --jobs 4 --seconds 30 --checkpoint sat-results/l2260-v9.json
```

v1〜v8と提出用mainは変更しない。

### v9 修正: 未使用ゲート (2026-11-26)

初回WSL自己テストでは、出力に到達しない2個のjunk ANDを持つ3ゲート回路がSATとなり、期待したUNSATと一致しなかった。出力関数の独立検証は正常だったが、最小回路に必要な全実ゲートの使用条件が符号化から抜けていた。修正版では両junkおよび全active ORに直接のreaderを要求し、復元回路の出力coneも独立検査する。報告された3ゲート回路を固定した回帰テストを追加。元のUNSAT期待値は変更しない。修正版はWSL未検証。旧v9のcheckpointは互換性なし。
