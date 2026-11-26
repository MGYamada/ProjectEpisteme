# alg-d source index: 「全ての概念はKan拡張である」, Chapters 0–2

This index fixes the source versions used by the Category track. Each row is one written document listed under Chapters 0–2 of [the alg-d.com index](https://alg-d.com/math/kan_extension/). The index page and every PDF were retrieved on **2026-11-26**. The SHA-256 hash identifies the exact file that was read. When a PDF changes, add a row for the new version and re-review the affected ledger entries. Keep the old row.

The index page states three global conventions. Categories are locally small unless stated otherwise. The axiom of choice is used without comment. The notes are meant to be read in order. The page does not mention universes. The page marks revisions as 更新 (mathematical content changed), 修正 (non-mathematical text changed), and 微修正 (minor wording fixes).

Each PDF numbers its items with one counter shared across kinds (定理, 命題, 補題, 系, 例) and displayed equation labels. Definitions (`定義.`) are unnumbered. The "Numbered" column is the largest number used in the PDF. "Definitions" counts `定義.` blocks only. The Chapter 0–1 counts are confirmed by their ledgers, and `checks/ledger.py` compares each ledger header with this index. The Chapter 2 counts come from extracted PDF text and are confirmed when that chapter is cataloged. Definitions introduced in prose are counted in the ledgers. In Chapters 0–1 the only exercises are two unnumbered 練習問題 at the end of commutative_diagram.pdf (`ALGD-C0-CDIAG-E01`, `-E02`). Chapter 2 will be checked for exercises when it is cataloged.

The ledger IDs have the form `ALGD-C<chapter>-<SLUG>-<nn>`. See the [Category strategy](Project_Episteme_Category_Strategy.md#4-source-ids).

## Chapter 0: 圏論入門 (introduction)

| Slug | File | Title | English working title | Printed date | Index-page date | Pages | Numbered | Definitions | SHA-256 |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| INTRO | [intro.pdf](https://alg-d.com/math/kan_extension/intro.pdf) | 圏論とは何か | What is category theory | 2026-03-30 | 2026-03-30 更新 | 15 | 32 | 5 | `0415d3f07bb499a69730019b32b643010a1c8ab75ab83b280cb58474fb304092` |
| CDIAG | [commutative_diagram.pdf](https://alg-d.com/math/kan_extension/commutative_diagram.pdf) | 可換図式について | On commutative diagrams | 2026-06-30 | 2026-05-14 追加, 2026-06-30 更新 | 6 | 3 | 1 | `ebde6b7a4d02777c385bd1ba2f533274e9d30e2f921e7daaa329abf84c66fb5b` |
| CONSTR | [construction.pdf](https://alg-d.com/math/kan_extension/construction.pdf) | 圏の構成例 | Constructions of categories | 2026-07-01 | 2025-08-17 更新, 2026-07-01 微修正 | 5 | 12 | 6 | `768f1096fdc77529a64edbdc907489711b8fc8fd531a2fc9d0985c02282844a7` |
| UNIV | [universality.pdf](https://alg-d.com/math/kan_extension/universality.pdf) | 普遍性 | Universality | 2026-04-20 | 2026-04-20 修正 | 17 | 14 | 5 | `b8f17b83d325b59ed39837013be30902da08413d7b4fe08850b1053a3dd062f3` |
| SHEAF | [sheaf.pdf](https://alg-d.com/math/kan_extension/sheaf.pdf) | 例：位相空間上の層 | Example: sheaves on a topological space | 2026-08-16 | 2026-04-20 修正, 2026-08-16 微修正 | 6 | 8 | 3 | `83e9658eedafb2f5414a3f0e9786d71e20a07f2889df1cc92f59eb9b831d3a73` |
| DUAL | [dual.pdf](https://alg-d.com/math/kan_extension/dual.pdf) | 双対 | Duality | 2026-05-12 | 2026-05-12 修正 | 9 | 20 | 6 | `36de3e4f62c7a1c6e03fa1e998d74adaf89286cc4de349685219a34939100be5` |
| EQUIV | [equivalence.pdf](https://alg-d.com/math/kan_extension/equivalence.pdf) | 自然変換・圏同値 | Natural transformations and equivalence of categories | 2026-08-08 | 2026-05-12 修正, 2026-08-08 微修正 | 15 | 20 | 7 | `9a3449da461c857326afe97fa9bfcfbb41c5febad1a4a552daf99730347bf934` |
| FUNDGPD | [fundamental_groupoid.pdf](https://alg-d.com/math/kan_extension/fundamental_groupoid.pdf) | 例: 基本亜群 | Example: the fundamental groupoid | 2026-05-12 | 2026-05-12 修正 | 5 | 11 | 5 | `2fd1421bdf84953a398ef37d1ed5c42bc52f0fafa57465b26b06851ed3699acc` |

## Chapter 1: 圏論 (category theory)

| Slug | File | Title | English working title | Printed date | Index-page date | Pages | Numbered | Definitions | SHA-256 |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| NAT | [nat.pdf](https://alg-d.com/math/kan_extension/nat.pdf) | 自然変換・関手圏 | Natural transformations and functor categories | 2026-05-14 | 2025-08-16 更新, 2026-05-14 修正 | 14 | 13 | 0 | `9d4c2b4fe05ca20b15ff041fe3884756138a3e76492d12f54da8597fabf61fb1` |
| YONEDA | [yoneda.pdf](https://alg-d.com/math/kan_extension/yoneda.pdf) | 米田の補題 | The Yoneda lemma | 2026-05-14 | 2023-08-20 更新, 2026-05-14 修正 | 8 | 11 | 0 | `277839b95dbff53e75197c012d304eea500f6944ca34786dbf3951937f10f586` |
| COMMA | [comma.pdf](https://alg-d.com/math/kan_extension/comma.pdf) | コンマ圏 | Comma categories | 2026-08-16 | 2026-06-27 修正, 2026-08-16 微修正 | 5 | 8 | 1 | `bf4af11c17b03c64f2f0bb99066b7e3cb16e0a60cc50d5fc15b089566eb2b2ac` |
| LIMIT | [limit.pdf](https://alg-d.com/math/kan_extension/limit.pdf) | 極限 | Limits | 2026-06-27 | 2025-08-17 更新, 2026-06-27 修正 | 29 | 33 | 6 | `ee08a3577452cbb06886c7b0c513844a18cc5ba7af517ee5ee2b93bd87c5cca2` |
| ADJOINT | [adjoint.pdf](https://alg-d.com/math/kan_extension/adjoint.pdf) | 随伴関手 | Adjoint functors | 2026-06-29 | 2025-08-17 更新, 2026-06-29 修正 | 38 | 56 | 4 | `8b0c83b4b42c888fa87737d0e7cb32205a7ba62463f3a4e90fff083d4d5ede95` |

## Chapter 2: 全ての概念はKan拡張である (all concepts are Kan extensions)

| Slug | File | Title | English working title | Printed date | Index-page date | Pages | Numbered | Definitions | SHA-256 |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| KAN | [kan_extension.pdf](https://alg-d.com/math/kan_extension/kan_extension.pdf) | Kan拡張 | Kan extensions | 2026-09-11 | 2026-07-17 修正, 2026-09-11 微修正 | 52 | 54 | 6 | `72fb7c6c1ef47cf9f45a38e71bc2196bcebc7163594158be8ea9e3fcaf88ef66` |
| SIMPLEX | [simplex.pdf](https://alg-d.com/math/kan_extension/simplex.pdf) | 例：単体的集合 | Example: simplicial sets | 2026-10-18 | 2026-10-18 更新 | 56 | 49 | 10 | `728b18894d57b7471bec403811b6cfa6f93cc79de302e08e2d67b2210989a894` |
| AFT | [aft.pdf](https://alg-d.com/math/kan_extension/aft.pdf) | 随伴関手定理 | Adjoint functor theorems | 2026-07-16 | 2026-07-16 修正 | 21 | 24 | 9 | `05fbabffc4936126fc619d6090383175028c0491793f7a2e44ea84068608f635` |
| SHEAF2 | [sheaf_kan_extension.pdf](https://alg-d.com/math/kan_extension/sheaf_kan_extension.pdf) | 例：位相空間上の層 その2 | Example: sheaves on a topological space, part 2 | 2026-07-22 | 2025-11-28 更新, 2026-07-22 修正 | 18 | 24 | 2 | `abb57620ed58bd0842f0f0bed9c031f3abe16114df46770bd0680b783e74075b` |
| LOG | [log.pdf](https://alg-d.com/math/kan_extension/log.pdf) | 圏の「対数」 | The "logarithm" of a category | 2026-08-08 | 2021-04-02 更新, 2026-08-08 微修正 | 5 | 8 | 2 | `f5b97ba38438507d607cfda5022d253ae12c366d6c53bd38a8b0caa4d3073ae7` |
| FILTERED | [filtered.pdf](https://alg-d.com/math/kan_extension/filtered.pdf) | フィルター圏 | Filtered categories | 2026-08-11 | 2026-08-11 修正 | 16 | 15 | 9 | `3bf65b1477ec69092f0319f0afe5b6239eea76daa390748f5c7395ed05108495` |
| END | [end.pdf](https://alg-d.com/math/kan_extension/end.pdf) | エンド | Ends | 2026-09-11 | 2026-01-06 更新, 2026-09-11 微修正 | 10 | 9 | 5 | `d4f708874a371b1769860c2601661a4731191e7a5f608f9494838d758e1096f4` |
| COYONEDA | [coyoneda.pdf](https://alg-d.com/math/kan_extension/coyoneda.pdf) | 余米田の補題 | The co-Yoneda lemma | 2026-09-11 | 2026-09-11 更新 | 3 | 2 | 0 | `30850e653487e8b8e2aabf41f9a7df4dc11c713c12db17db36a921ea18925753` |
| PROF | [profunctor.pdf](https://alg-d.com/math/kan_extension/profunctor.pdf) | ココンマ圏とprofunctor | Cocomma categories and profunctors | 2026-08-13 | 2026-08-13 修正 | 28 | 13 | 4 | `aa3a5613d08d63180c9baef015cad182d98400ff99a92306da084cd4e534fb48` |
| ISBELL | [isbell.pdf](https://alg-d.com/math/kan_extension/isbell.pdf) | Isbell双対 | Isbell duality | 2026-08-08 | 2026-08-08 修正 | 3 | 3 | 0 | `3603a963d89ab12a01fccd1f827283282c1464e8db073676c64c90189e0e72a8` |

## Supplementary (outside the chapter lists)

| Slug | File | Title | English working title | Printed date | Index-page date | Pages | Numbered | Definitions | SHA-256 |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| KANSHORT | [kan_extension_short.pdf](https://alg-d.com/math/kan_extension/kan_extension_short.pdf) | 可能な限り最短でKan拡張に到達する | Reaching Kan extensions as quickly as possible | 2026-07-17 | 2026-07-17 更新 | 30 | 29 | 9 | `410c45dfa33b6a76eae8620112e8ae04138c6a5560d4fb9a619cf9744939e965` |

KANSHORT is linked from the announcement block of the index page, not from a chapter. It is not part of the Chapter 0–2 completion criterion. Its items should point to the same Lean declarations as the corresponding Chapter 1–2 items, using the ID prefix `ALGD-SUP-KANSHORT`.

## Totals

| Scope | Documents | Pages | Numbered (max) | `定義.` blocks |
| --- | --- | --- | --- | --- |
| Chapter 0 | 8 | 78 | 120 | 38 |
| Chapter 1 | 5 | 94 | 121 | 11 |
| Chapter 2 | 10 | 212 | 201 | 47 |
| Chapters 0–2 | 23 | 384 | 442 | 96 |
| Supplementary | 1 | 30 | 29 | 9 |

The numbered totals include displayed equation labels that share the counter. The ledgers record how many numbers are items and how many are equation labels.

Later chapters on the index page are outside the current scope: 第3章 2圏, 第4章 豊穣圏, 第5章 formal category theory, 第6章 各点Kan拡張, 第7章 ∞圏, 第8章 高次元圏, 第9章 トポス. The retrieved copy of the index page was cut off inside Chapter 9, so chapters after it were not seen.
