<link rel="stylesheet" href="{{site.github.url}}/css/tpp2019.css" charset="utf-8">

# The 15th Theorem Proving and Provers meeting (TPP 2019)

TPP (Theorem Proving and Provers) ミーティングは，
2005年から年に1回開催され，
定理証明系を作っている人から使う側の人まで幅広い人たちが集まり，
様々な側面からの話をしてアイディアの交換をしてきたものです．

ミーティング期間中の討論を大切にしたいと考えていますので，
出来上がった仕事の講演だけでなく，進行中の仕事，未完成の仕事についての講演も歓迎します．
参加者には可能な限りご講演いただくことを期待しています．

TPP is a series of annual meetings for developers as well as users of theorem provers.
Discussions from various aspects and exchanges of ideas have taken place in the past meetings since 2005.

We regard the discussions during the meeting to be most important.
As such, not only the talks about completed work, but those about ongoing 
work and half-baked work are also welcome.
We hope all participants would consider giving a talk.


## 開催日程 / Date

2019年11月18日(月), 19日(火) / Mon. 18th to Tue. 19th, November.

## 会場 / Venue

国立情報学研究所（学術総合センター）19階 1901,1902,1903会議室 /
National Institute of Informatics (National Center of Sciences) 19th floor, Rooms 1901, 1902, 1903

## 住所 / Address

〒101-8430 東京都千代田区一ツ橋2-1-2 / 2-1-2 Hitotsubashi, Chiyoda-ku, Tokyo 101-8430
[アクセス](https://www.nii.ac.jp/about/access/) / [Access](https://www.nii.ac.jp/en/about/access/)

<a name="party" />
## 懇親会 / Dinner Party

日時: 11/18夕方 / Time: 18th Mon. evening

会場 / Place: TBA

## 幹事 / Organizer

山田晃久 (国立情報学研究所, ERATO蓮尾メタ数理システムデザインプロジェクト) /
Akihisa YAMADA (ERATO HASUO Metamathematics for Systems Design Project, NII)

Email: akihisayamada&lt;at&gt;nii.ac.jp

## 参加申し込み / Registration

11/8(金)までに / Please register by 8th November from

<span style="font-size:150%">
[こちらから / here](https://docs.google.com/forms/d/e/1FAIpQLSdApuGxfoZVQhFbDOeik1rLsnffh7b58e5hwV0o8cKylaXYCw/viewform)
</span>

## プログラム / Technical Program

### Nov. 18

* 14:00 **Opening; On TPP Mark 2019**<br/>
  Akihisa Yamada @ NII

* 14:30 **TPP Mark 2019 in CafeOBJ** (45min)<br/>
  二木厚吉 (FUTATSUGI,Kokichi) @ 北陸先端大／産総研 (JAIST/AIST)<br/>
  Modeling, specification, and verification of TPP Mark 2019 problem in CafeOBJ Specification Verification System is presented.  Some comments on recent advances in CafeOBJ's Specification Verification (i.e. theorem proving) with equational reduction/rewriting are also given.

* 15:15 Break (15min)

* 15:30 **定理間の類似度の定式化について(Work in Progress)** (30min)<br/>
  中正 和久 (なかしょう かずひさ) @ 山口大学<br/>
  近年の形式化数学ライブラリの大規模化により，ライブラリ中の定理検索に対するニーズが高まっている．定理は同値な変形によってその表現を大きく変化させるため，パターンマッチングによる検索では多くの検索漏れが生じてしまう．これを解決するには，定理間に類似度指標を導入し，それに準ずる検索アルゴリズムを開発することが求められる．本発表では「定理Aに対する定理Bの論理的な類似度」を「定理Aを仮定して定理Bを導く最短証明の情報量」として定式化する．発表者は，この定式化によって定理間に擬距離を導入し，自動定理証明や定理の検索・分類・クラスタリング，ライブラリの正規化などに応用することを目指している．

* 16:00 **Isabelle/HOL を用いたユークリッド原論の定理証明** (30min)<br/>
  岩間詞也 @ 甲南大学大学院 自然科学研究科 知能情報学専攻<br/>
  Isabelle を用いて，ユークリッド原論の第 1 巻および第 2 巻の証明を行った. 本稿で示したユークリッド幾何学への利用には定義, 公理, 公準および証明の済んだ命題などを適した形に関数化する ことが必要であった. 

* 16:30 **Mizarにおける楕円曲線の形式化** (30min)<br/>
  布田 裕一 @ 東京工科大学<br/>
  楕円曲線は、公開鍵暗号や符号で利用され重要な数学の要素となっている。発表者らは、形式検証システムMizarにおいて、有限体上の楕円曲線の形式化を進めている。本発表では、楕円曲線に関して形式化を実施した内容について報告する。具体的には、有限素体、射影座標、射影座標を用いた楕円曲線の点の集合と個数(濃度)、楕円曲線の演算(加算／2倍算)の公式や演算の特性(可換性など)を形式化した結果を示す。

* 17:00 Break (15min)

* 17:15 **IFPと、その並列プログラム抽出への拡張** (45min~)<br/>
  立木　秀樹 @ 京都大学　人間・環境学研究科<br/>
  IFP (Intuitionistic Fixedpoint Logic) は、Ulrich Berger が中心となって開発した、プログラム抽出を目的とした、直観主義一階述語論理を strictly positive な inductive/coinductive な述語定義に拡張した体系です。この体系では、実数などの公理に基づいて抽象的な（すなわち、データ表現を明示的に扱わない）証明を行い、そこからデータ表現とプログラムの両方を抽出します。IFP の一つの特徴として、Haskell のプログラムが抽出でき、引数によっては停止しない部分関数のプログラムを抽出できることがあります。この講演では、複数の部分関数をAmbオペレータにより並列実行してできた全域的なプログラムを抽出できるようにIFPを拡張した論理体系を紹介します。時間があれば、実数のグレイコード表現から符号付2進表現への変換プログラムの抽出への応用についても述べます。

* 18:30 **Dinner Party**

### Nov. 19

* 10:00 **ペトリネットにおける停止性判定の形式化** (30min)<br/>
  稲垣 衛 @ 千葉大学大学院融合理工学府, 山本光晴 @ 千葉大学大学院理学研究院<br/>
  ペトリネットはシステムのモデル化に使用される有向２部グラフであり、並行的、
非同期的、非決定的動作の記述に使われる。我々のグループの既存研究ではCoq/
SSReflectを用いて、対象とするペトリネットにおいてKarp-Miller木を構成する
関数を定義し、それを用いてペトリネットが被覆性を有するか否かを判定する決
定手続きを形式化した。本発表では、ペトリネットの性質のうち、停止性を同じ
くKarp-Miller木を用いて判定する手続きを形式化し、被覆性判定の形式化と比
較した結果を述べる。

* 10:30 **Towards Verification of Event-B Models in Coq** (30min)<br/>
  Tsutomu Kobayashi @ Japan Science and Technology Agency

* 11:00 Break (15min)

* 11:15 **A linear time algorithm for automatic generation of multiplicative planar proof nets (tentative)** (45min)<br/>
  Satoshi Matsuoka @ AIST<br/>

* 12:00 Lunch break (1hour 30min)

* 13:30 **Horn Clauses in Hybrid-Dynamic First-Order Logic** (45min)<br/>
  Daniel GAINA @ Institute of Mathematics for Industry (IMI), Kyushu University<br/>
  We propose a hybrid-dynamic first-order logic as a formal foundation for specifying and reasoning about reconfigurable systems.As the name suggests, the formalism we develop extends (many-sorted) first-order logic with features that are common to hybrid logics and to dynamic logics.This provides certain key advantages for dealing with reconfigurable systems, such as: (a) a signature of nominals, including operation and relation symbols, that allows references to specific possible worlds / system configurations -- as in the case of hybrid logics; (b) distinguished signatures of rigid and flexible symbols, where the rigid symbols are interpreted uniformly across possible worlds; this supports a rigid form of quantification, which ensures that variables have the same interpretation regardless of the possible world where they are evaluated; (c) hybrid terms, which increase the expressive power of the logic in the context of rigid symbols; and (d) modal operators over dynamic-logic actions, which are defined as regular expressions over binary nominal relations. We then study Horn clauses in this hybrid-dynamic logic, and develop a series of results that lead to an initial-semantics theorem for arbitrary sets of clauses.This shows that a significant fragment of hybrid-dynamic first-order logic has good computational properties, and can serve as a basis for defining executable languages for reconfigurable systems.

* 14:15 **Experience Report: Type-Driven Development of Certified Tree Algorithms in Coq** (45min)<br/>
  QI Xuanrui @ 名古屋大学大学院多元数理科学研究科<br/>
  This talk is a report on, as well as a defense of the usefulness of dependent types for developing provably correct programs. We believe that dependent types—and dependently-typed programming in Coq in particular—could allow for faster and safer development. There are already several accounts about the utility of dependent types in practical program development, and in real-world applications. Here we add to these accounts by outlining our experience in developing tree algorithms for succinct data structures and proving them with the help of dependent types.<br/>
  This is joint work with Reynald Affeldt, Jacques Garrigue and Kazunari Tanaka. The talk was previously given at the Coq Workshop 2019 in Portland, Oregon, and will be given in English.

* 15:00 Break (15min)

* 15:15 **Formal Verifications of Call-by-Need and Call-by-Name Evaluations with Mutual Recursion** (30min)<br/>
  水野雅之 @ 東北大学<br/>
  For non-strict languages, the equivalence between the high-level
specification (call-by-name) and the actual implementation
(call-by-need) is of foundational interest. Launchbury showed the
adequacy of his call-by-need natural semantics with respect to
call-by-name denotational semantics. Ariola and Felleisen proved the
correspondence---based on term graphs---between call-by-name and
(their definition of) call-by-need reductions. However, mutual
recursion was challenging for the latter formalism.<br/>
  In this presentation, we give simpler proofs---solely based on finite
terms and operational semantics---of the correspondence among
Launchbury's call-by-need natural semantics and 3 styles of
call-by-name natural semantics of lambda-calculus with mutually
recursive bindings, and formalize them in the proof assistant Coq.

* 15:45 **Validating Mathematical Structures** (30-45min)<br/>
  坂口和彦 @ 筑波大学<br/>
  On formalizing nontrivial mathematical definitions and proofs with proof assistants, it is necessary to have a good infrastructure to support the users. The key ingredient of the infrastructure is the hierarchy of mathematical structures, that allows for the sharing of notations and theories to avoid repeating similar definitions and proofs, and supports automated inference to make inheritance/subtyping of structures implicit. The packed classes method is a generic design pattern to define and combine mathematical structures in a dependent type theory with records. The Coq proof assistant has mechanisms to enable automated structure inference and subtyping in packed classes, that is, implicit coercions and canonical structures. These ingredients have been successfully used to prove nontrivial mathematical proofs, in particular, the Odd Order Theorem. In spite of its success, the packed classes method is hard to master for library designers and requires a substantial amount of work, because of poor support for packed classes by the Coq system. In this paper, we propose a thorough analysis of the packed classes method, in particular some invariants of hierarchies that are necessary to make the packed classes method work well, and propose tools to support its large scale deployment by checking these invariants.

* 16:30 **potential talk slot**

* 17:30 *Closing*

## TPPmark 

計算可能性を形式化するための土台をみんなで考えてみるというのはいかがでしょうか．
ただ教科書的な題材では面白くないかもしれませんので，少しひねくれたものになっています．
解答はオーガナイザーまでお送りください．部分解・アップデートも歓迎します．
/
How about collectively think of a foundation for formalizing computability?
As the textbook theme might be boring to you, below offers a slightly screwed up setting.
Solutions should be send to the organizer. Partial solutions and updates are welcome.

1. Cyclicテープ上で動くチューリングマシンの概念を形式的に定義してください．
Cyclicテープとは固定長のテープで，両端がつながったものです．
ベースとなるチューリングマシンの定義は問いません．/
Please formally define a notion of Turing machines that manipulate cyclic tapes.
A cyclic tape is a fixed-length tape whose both ends are connected to each other.
You can base on any paper definition of Turing machines.

2. その1ステップ計算を定義してください．/
Please define their one-step computation.

3. マシンが与えられた入力テープに対して停止するという述語を定義してください．/
Please define the predicate that a machine halts on a given input tape.

4. 長さ・内容不明のcyclicテープを入力し，テープをゼロクリアして停止するマシンを与えてください．テープ長の最小値を仮定してかまいません．このパズルは私が以前 Vincent van Oostrom先生より頂いたものです．/
Please define a machine that, given an input cyclic tape of unknown size and content, clears the tape and halts. You may assume a minimum length on input tapes.
This puzzle was given to me by Vincent van Oostrom.

5. そのマシンに具体なテープを与え，動きを例示してください．/ Please demonstrate how your machine above works on a concrete tape example.

6. (任意) そのマシンが任意のcyclicテープに対して停止し，結果のテープがクリアされていることを証明してください．/
(Optional) Please prove that your machine halts and resulting tape is cleared for any input cyclic tape.

## これまでのTPP / Past TPPs
[TPP2018](https://ksk.github.io/tpp2018/) /
[TPP2017](https://aigarashi.github.io/TPP2017/) /
[TPP2016](http://pllab.is.ocha.ac.jp/~asai/tpp2016/) /
[TPP2015](https://sites.google.com/a/progsci.info.kanagawa-u.ac.jp/tpp2015/) /
[TPP2014](http://imi.kyushu-u.ac.jp/lasm/tpp2014/) /
[TPP2013](http://shirodanuki.cs.shinshu-u.ac.jp/TPP/) /
[TPP2012](http://www.math.s.chiba-u.ac.jp/tpp2012/) /
[TPP2011](http://staff.aist.go.jp/reynald.affeldt/tpp2011/) /
[TPP2010](http://www.math.nagoya-u.ac.jp/~garrigue/tpp10/) /
[TPP2009](http://ist.ksc.kwansei.ac.jp/~ktaka/TPP09/TPP09.html) /
[TPP2008](http://www.score.cs.tsukuba.ac.jp/~minamide/tpp/) /
[TPP2007](http://www.score.cs.tsukuba.ac.jp/~minamide/tpp/tpp07/index.html) /
[TPP2006](http://www.jaist.ac.jp/joint-workshop/TPSmeeting/2006_11/program.html) /
[TPP2005](http://www.jaist.ac.jp/joint-workshop/TPSmeeting/2005_11/program.html)

