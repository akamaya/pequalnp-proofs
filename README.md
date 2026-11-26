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

## SAT v10（OR集合の正規順序と包含冗長性）

修正v9の本番実測: 60.513秒、k=1,2,3,9,10 UNSAT（各0.069,0.717,11.195,0.787,0.066秒）、k=4..8 TIMEOUT。修正v9自己テストの再実行ログは未確認。

v10はv9と同じ符号化に、private edge、OR/ANDの2入力support集合が互いに包含されない制約、OR supportの厳密な昇順を追加する。最小回路では同じsupportのORは重複なので不要。ORからORへの依存はsupportの真包含を伴うため、整数maskの昇順にORスロットを並べ替えられる。--mode none/private/antichain/canonical（既定canonical）で比較可能。独立検査と比較器の64組全数テスト、冗長な強制モデルの拒否、非包含の強制モデルの受理を追加した。旧v9の回帰テストもmode noneで実行する。

```bash
git -C "$HOME/dev/pequalnp-tools" pull --ff-only && cd "$HOME/dev/pequalnp-tools" && nice -n 10 .venv-sat/bin/python -u pnp_sat_solve_v10.py --self-test --seconds 10
```

```bash
cd "$HOME/dev/pequalnp-tools" && nice -n 10 .venv-sat/bin/python -u pnp_sat_solve_v10.py --case l2260 --gates 21 --jobs 4 --seconds 60 --seed-v9 sat-results/l2260-v9.json --checkpoint sat-results/l2260-v10-canonical.json
```

v9のfingerprintが一致した場合だけUNSATを引継ぐ。v10実機未検証。チェックポイントは自己の信頼済み実験結果に限定。正規化・最小性制約のLean形式化とUNSAT証明書は未完成。v1〜v9と提出用mainは変更しない。

## SAT v11（内部OR実数による分割）

v10 WSL self-test PASS、canonical / g4 / 4並列 / 60秒ずつ、120.483秒。k=4..8全てTIMEOUT、v9から継承した5ケースのみUNSAT。正規順序化の効果は確認できなかった。

v11はv9のCNFに戻り、active ORが末尾連続である性質から実際の内部OR数r=0..(21-2k-1)で排他的・網羅的に分割する。各部分問題は最大2個のunit clauseの追加のみ。k=4..8なら45 cube。v9のfingerprintが一致した場合、既存のk=1,2,3,9,10のUNSATは引継ぎ可能。小さいrから探索し、初回はCaDiCaLを使用。checkpointは各cubeの結果を保存し、同じファイルでsolver/secondsを変えて再試行できる。TIMEOUTの学習節は保持しない。

```bash
git -C "$HOME/dev/pequalnp-tools" pull --ff-only && cd "$HOME/dev/pequalnp-tools" && nice -n 10 .venv-sat/bin/python -u pnp_sat_solve_v11.py --self-test --seconds 10
```

```bash
cd "$HOME/dev/pequalnp-tools" && nice -n 10 .venv-sat/bin/python -u pnp_sat_solve_v11.py --case l2260 --gates 21 --jobs 4 --seconds 5 --solver cadical195 --seed-v9 sat-results/l2260-v9.json --checkpoint sat-results/l2260-v11-exact.json
```

v11実機未検証。全分割UNSATでもLeanでの正規化・符号化・証明書の検証が必要。v1〜v10、提出用main、実行中LLMは変更しない。

## SAT v12（OR配線を探索しないsupport-only緩和）

v11 WSL self-test PASS。CaDiCaL/5秒/4並列: 45分割中18 UNSAT、27 TIMEOUT (39.465秒)。Glucose4/10秒/4並列: 残り27分割中1 UNSAT (k=7,r=3)、26 TIMEOUT (71.52秒)。全100分割では継承55+新規19=74 UNSAT。

v12は各ANDの2入力を13ビットのsupport集合で直接表現し、OR DAGの接続を探索しない。各集合の大きさはr+1以下、異なる非単元supportの個数はOR予算r以下。Lambdaになり得ない必須ORの個数を数え、h6のLambda数の上限をさらに絞る。最小性の必要条件としてoperand supportの非包含とtopの固有辺を要求。全入力と構造制約を独立評価する。RELAXED_SATは実際のOR DAGが存在することを意味せず、反例ではない。UNSATの場合のみ、未形式化の縮約を前提に対応する回路候補を排除できる。

v11のfingerprintを照合してUNSATを引継ぎ、未解決の各kについて最大OR予算で緩和を解く。最大予算でUNSATならそれ以下の予算も排除できる。自己テストは既知のsupport候補の受理、予算不足・緩和h6違反の拒否、3bit比較器の全数検査。v12は実機未検証。

```bash
git -C "$HOME/dev/pequalnp-tools" pull --ff-only && cd "$HOME/dev/pequalnp-tools" && nice -n 10 .venv-sat/bin/python -u pnp_sat_solve_v12.py --self-test
```

```bash
cd "$HOME/dev/pequalnp-tools" && nice -n 10 .venv-sat/bin/python -u pnp_sat_solve_v12.py --case l2260 --gates 21 --jobs 4 --seconds 20 --seed-v11 sat-results/l2260-v11-exact.json --checkpoint sat-results/l2260-v12-relax.json
```

v12のcheckpointを再開する際は同じseed-v11を指定し、seedのUNSAT集合が変化した場合は別checkpointを使用。Lean形式化・UNSAT証明書は未完成。v1〜v11と提出用mainは変更しない。

## SAT v13（support CEGAR / UNSAT coreによる精密化）

v12実測: k=5,6,7 RELAXED_SAT、k=4,8 TIMEOUT。新規UNSATなし (20.975秒)。v11 CaDiCaL 60秒再探索: (k,r)=(8,3),(5,4),(4,4) UNSAT、23分割残り (387.171秒)。全100分割中77 UNSAT。v12自己テスト結果は未確認。

v13はsupport-only緩和とv9の実配線SATを接続する。外側で候補supportを生成し、内側で固定supportから実際のOR DAGを探索。内側UNSATならassumption coreを外側の変数へ写像して否定節を追加する。内側のAND入力順とtop順の対称性制約は解除し、外側のsupport順との不一致による誤排除を防ぐ。追加の下限: 任意のroot Sについて |S|-1個のORが必要であり、Sに含まれない異なる複合rootはそれぞれ別のORを必要とする。これを外側で符号化する。

外側UNSATなら対象ケースを排除。内側SATなら復元回路の全入力・構造を検証するが、最小性そのものは未検証。TIMEOUTでも報告済みcore節をcheckpointに保存し、同一fingerprintで再開する。ソルバー内部の学習節そのものは保存しない。checkpointは信頼済みローカル実験に限る。v13実機未検証、Leanによる縮約・符号化・証明書検証は未完成。

```bash
git -C "$HOME/dev/pequalnp-tools" pull --ff-only && cd "$HOME/dev/pequalnp-tools" && nice -n 10 .venv-sat/bin/python -u pnp_sat_solve_v13.py --self-test
```

```bash
cd "$HOME/dev/pequalnp-tools" && nice -n 10 .venv-sat/bin/python -u pnp_sat_solve_v13.py --case l2260 --gates 21 --jobs 4 --seconds 60 --seed-v11 sat-results/l2260-v11-exact.json --checkpoint sat-results/l2260-v13-cegar.json
```

同じseedとcheckpointで再実行するとcoreを引継ぐ。v1〜v12、提出用mainは変更しない。

## SAT v14（v13の同一入力制約修正・checkpoint移行）

v13 WSL自己テストは失敗。AND入力のsource順序制約の解除時に、同じsourceを2回読むことの禁止まで解除していた。報告された3ゲートのSAT witnessは同一入力ANDを2個含む非最小回路だった。v14では順序のみ解除し、各ANDの同一source禁止を復元、報告モデルの回帰テストを追加。元の期待値は変更しない。

v13本番: k=4 は外側緩和だけでUNSAT (26.953秒、candidate=0、cut=0)、k=5は3 cut、k=6は9 cut、k=7,8は初回探索中TIMEOUT。全100分割中暫定85排除、15残り。v14の外側CNFと変数番号はv13と同一、内側は同一source禁止の追加だけなので、v13のUNSAT coreは引き続き有効。fingerprintを照合してUNSAT/TIMEOUTとcutを移行する。旧SAT/ERRORは移行しない。

```bash
git -C "$HOME/dev/pequalnp-tools" pull --ff-only && cd "$HOME/dev/pequalnp-tools" && nice -n 10 .venv-sat/bin/python -u pnp_sat_solve_v14.py --self-test
```

```bash
cd "$HOME/dev/pequalnp-tools" && nice -n 10 .venv-sat/bin/python -u pnp_sat_solve_v14.py --case l2260 --gates 21 --jobs 4 --seconds 180 --seed-v11 sat-results/l2260-v11-exact.json --seed-v13 sat-results/l2260-v13-cegar.json --checkpoint sat-results/l2260-v14-cegar.json
```

v14は実機未検証。v13の元ファイルおよびv11/v13のcheckpointは変更しない。結果は実験用で、Leanによる形式的証明・証明書検証は未完成。

## v14 180秒実測と証明書用CNFの出力

v14 WSL本番: k=8 は外側のみUNSAT (137.703秒, candidate=0, cut=0)。k=5,6,7はTIMEOUT、保存cutはそれぞれ9,216,3、合計228。v11継承分を含め100分割中86排除、14残り。自己テスト再実行のログは未確認。次はv14を同一checkpointで再開し、探索予算を増やす。ソルバー内部学習節は引き継がないが、報告済みcutは引き継ぐ。

```bash
cd "$HOME/dev/pequalnp-tools" && nice -n 10 .venv-sat/bin/python -u pnp_sat_solve_v14.py --case l2260 --gates 21 --jobs 3 --seconds 600 --seed-v11 sat-results/l2260-v11-exact.json --seed-v13 sat-results/l2260-v13-cegar.json --checkpoint sat-results/l2260-v14-cegar.json
```

pnp_sat_export_v1.py は既存のv9/v11/v14 checkpointのfingerprintとCNFの節数・変数数を照合し、排除済みの式をDIMACSに出力する。v9の全予算UNSAT、v11の個別UNSAT、v14のcutなし外側UNSATのみを出力する。現ログからは20式（全予算7式、個別13式）で86分割をカバーする見込み。manifest.jsonに各CNFのSHA256とカバー範囲を記録。cut依存UNSATの証明書連結は未実装。出力はsat-results以下、提出用mainには触れない。

```bash
git -C "$HOME/dev/pequalnp-tools" pull --ff-only && cd "$HOME/dev/pequalnp-tools" && .venv-sat/bin/python -u pnp_sat_export_v1.py --self-test && .venv-sat/bin/python -u pnp_sat_export_v1.py
```

exportは実機未検証。これは証明書作成前のCNF保存であり、UNSATの証明書を生成・検証する機能ではない。別途proof-producing SAT solver、証明書検査、Leanでの元定理からの縮約証明が必要。

## SAT v15（OR集合の実現可能性による事前排除）

v14 WSL self-test PASS。600秒再探索では新規UNSATなし、k=5/6/7の累積cutは49/1457/9、合計1515（新規1287）。100分割中86排除・14残り。k=5は内側探索、k=7は外側探索が主なボトルネック。

v15はv14と同じ外側/内側CNFを使い、候補supportの抽象OR DAGが予算内で構築できるか先に調べる。各異なる複合supportに1個のORが必要であり、任意の複合supportは2個の真部分集合の和集合に分解できる必要がある。原子は無料。全分解を探索し、予算内の抽象DAGが存在しないことを確定できた場合だけ、不可能なroot集合（greedyで縮小）から外側cutを作る。Lambda、junk順序等を無視した緩和なので、可能と判定しても従来の内側SATで検証する。探索ノード上限や最大集合サイズを超えた場合も内側SATへ送る。pnp_or_budget_v1.pyの自己テストは4原子の独立全列挙による1160条件と一致（開発環境）。v15全体のWSL実行は未検証。

```bash
git -C "$HOME/dev/pequalnp-tools" pull --ff-only && cd "$HOME/dev/pequalnp-tools" && nice -n 10 .venv-sat/bin/python -u pnp_sat_solve_v15.py --self-test
```

```bash
cd "$HOME/dev/pequalnp-tools" && nice -n 10 .venv-sat/bin/python -u pnp_sat_solve_v15.py --case l2260 --gates 21 --jobs 3 --seconds 600 --outer-for 7=g4 --inner-for 5=cadical195 --seed-v11 sat-results/l2260-v11-exact.json --seed-v14 sat-results/l2260-v14-cegar.json --checkpoint sat-results/l2260-v15-cegar.json
```

k=6は従来のCaDiCaL外側/Glucose4内側、k=7のみ外側をGlucose4、k=5のみ内側をCaDiCaLで比較する。fingerprintを照合してv14のUNSATとcutを継承。v14のcheckpointは変更しない。prefilter_rejected, prefilter_unknown, prefilter_seconds, inner_candidatesは今回の探索中の集計であり、cut_countは継承を含む。v15の新規cutに対応する形式的証明・証明書は未作成。既存v9/v11/v14のcutなしUNSAT用のexportは別途実行可能。提出用mainは変更しない。

## SAT v16（射影によるOR予算cutの一般化）

v15 WSL self-test PASS。600秒/3並列: k=5/6/7 の新規cut 18540/2021/19、累計18589/3478/28、合計22095。新規候補20580件はすべてOR予算prefilterで排除、内側SAT呼び出し0件。新規UNSATなし、86/100分割排除、14分割残り。候補排除件数は前回の16倍だが、探索空間の残り割合とは一致しない。

v16では、OR DAGの全supportを原子集合Pに射影しても和集合演算が保存され、空集合・単元集合・重複集合の除去によりOR個数が増えない性質を使う。既存の不可能root coreから無関係な原子を除き、さらに原子を1個ずつ除いても予算不足が確定する場合だけ除く。射影後のroot要求に対応するリテラルだけをcutにするため、完全一致のcutより一般化できる。探索上限でUNKNOWNの場合は除去しない。4原子の独立列挙から射影cutに一致する全補完を検査する自己テストを追加。prefilterで不可能と確定した候補は全真理値表の再評価を省き、内側SATへ渡す候補だけ従来の独立評価を行う。最終SAT witnessの独立検証は変更なし。

```bash
git -C "$HOME/dev/pequalnp-tools" pull --ff-only && cd "$HOME/dev/pequalnp-tools" && nice -n 10 .venv-sat/bin/python -u pnp_sat_solve_v16.py --self-test
```

```bash
cd "$HOME/dev/pequalnp-tools" && nice -n 10 .venv-sat/bin/python -u pnp_sat_solve_v16.py --case l2260 --gates 21 --jobs 3 --seconds 600 --outer-for 7=g4 --inner-for 5=cadical195 --seed-v11 sat-results/l2260-v11-exact.json --seed-v15 sat-results/l2260-v15-cegar.json --checkpoint sat-results/l2260-v16-cegar.json
```

v15とCNFおよび変数番号は同じで、fingerprint照合後に旧cutとUNSATを移行する。projected_literals/full_root_literalsは新規prefilter cutの総リテラル数と、同じroot集合の完全一致cutの場合の総リテラル数。追加の射影探索がCPU時間を増やす可能性もあるので実測比較する。v16自己テスト・本番は未実行。Lean形式化・証明書は未完成。v15以前と提出用mainは変更しない。

## SAT v17（外側・内側CNFの統合）

v16 WSL本番600秒/3並列: k=5/6/7の新規cutは20747/480/0、累計39336/3958/28、計43322。新規候補21227はすべてprefilterで排除、内側SAT呼び出しなし。射影cutのリテラル削減はk=5で25.48%、k=6で31.52%。新規UNSATなし、14分割未解決。v16自己テストのログは未確認。k=7は候補生成も0件。

v17はv14の正確なOR DAG oracleとsupport緩和CNFのsupport変数を同一変数に写像し、単一のSATソルバーで連言を解く。v16のfingerprintを照合してcutを共有変数に再配置し、解決済みkも継承する。light（既定）はv12の緩和、strongはv14の追加OR下限制約も含む。両モードとも最小性の必要条件を保持し、SATなら復元回路の全入力と構造を独立検証する。自己テストは既知の強制witness、cutの符号・変数対応、両モードのSAT/UNSATを検査する。新たな候補別cutの追加は行わず、TIMEOUT時は内部学習節を保存しない。

```bash
git -C "$HOME/dev/pequalnp-tools" pull --ff-only && cd "$HOME/dev/pequalnp-tools" && nice -n 10 .venv-sat/bin/python -u pnp_sat_solve_v17.py --self-test --seconds 10
```

```bash
cd "$HOME/dev/pequalnp-tools" && nice -n 10 .venv-sat/bin/python -u pnp_sat_solve_v17.py --case l2260 --gates 21 --jobs 3 --seconds 600 --solver cadical195 --solver-for 7=g4 --outer-mode light --seed-v11 sat-results/l2260-v11-exact.json --seed-v16 sat-results/l2260-v16-cegar.json --checkpoint sat-results/l2260-v17-light.json
```

同じseed/モードでのみ同一checkpointを使用する。v17は実機未検証。旧cutの数学的妥当性・縮約・証明書のLean形式化は未完成。v16以前のコード・checkpointおよび提出用mainは変更しない。

## SAT v18（重複制約を除いたcompact SAT）

v17 WSL light/600秒/3並列: k=5,6,7全TIMEOUT、CNF節数117387/91706/98341、変数数16355/19731/23231、14分割残り。v17自己テストのログは未確認。

v18はv14の正確なOR DAG oracleを直接使い、v16の43322 cutをsupport変数へ写像する。v12のグラフ関数、h4/h5/h6、OR予算等の重複制約を取り除く。最小性に必要なsupport非包含、topの固有辺、supportによるAND入力順とtop順は維持する。固有辺評価には正例だけを追加。比較器は各bitにつき1個の変数と6節のmajorityを使用する。compact既定、canonicalはOR supportの厳密昇順も追加。旧cutの変数番号を照合する。自己テストは比較器全数検査、固定witness、cut写像、非包含制約、SAT/UNSATを含む。v18実機未検証。

```bash
git -C "$HOME/dev/pequalnp-tools" pull --ff-only && cd "$HOME/dev/pequalnp-tools" && nice -n 10 .venv-sat/bin/python -u pnp_sat_solve_v18.py --self-test --seconds 10
```

```bash
cd "$HOME/dev/pequalnp-tools" && nice -n 10 .venv-sat/bin/python -u pnp_sat_solve_v18.py --case l2260 --gates 21 --jobs 3 --seconds 600 --solver cadical195 --solver-for 7=g4 --outer-mode compact --seed-v11 sat-results/l2260-v11-exact.json --seed-v16 sat-results/l2260-v16-cegar.json --checkpoint sat-results/l2260-v18-compact.json
```

v17同様、TIMEOUT時にSAT内部学習節は保存しない。既存コード・checkpoint・提出用mainは変更しない。Lean縮約・証明書検証は未完成。
