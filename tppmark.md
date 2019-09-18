計算可能性を形式化するための土台をみんなで考えてみるというのはいかがでしょうか．
ただ教科書的な題材では面白くないかもしれませんので，少しひねくれたものになっています．
解答はオーガナイザーまでお送りください．部分解・アップデートも歓迎します．
/
How about collectivly think of a foundation for formalizing computability?
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

3. マシンが与えられた入力テープに対して停止するという術語を定義してください．/
Please define the predicate that a machine halts on a given input tape.

4. 長さ・内容不明のサイクリックテープを入力し，テープをゼロクリアして停止するマシンを与えてください．テープ長の最小値を仮定してかまいません．このパズルは私が以前 Vincent van Oostrom先生より頂いたものです．/
Please define a machine that, given an input cyclic tape of unknown size and content, clears the tape and halts. You may assume a minimum length on input tapes.
This puzzle was given to me by Vincent van Oostrom.

5. テープの具体例を与え，2.1のマシンの動きを例示してください．/ Please demonstrate how your machine of 2.1. works on a concrete tape example.

6. (任意) 余力があれば，2.1で定義したマシンが，任意の入力に対して停止することを証明してください．