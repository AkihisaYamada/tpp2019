/-
Copyright (c) 2019 Makoto Kanazawa. All rights reserved.

Authors: Makoto Kanazawa
Solution to TPPmark (TPP 2019) (https://akihisayamada.github.io/tpp2019/)
lean_version = "3.4.2"
mathlib = {git = "https://github.com/leanprover-community/mathlib", 
rev = "09fd631bed2af3ea89b11fdff6112a606de44d09"}
-/
import data.fintype data.list -- from mathlib

namespace CTM

open nat

lemma iterate_bnot (n : ℕ) (b : bool) : iterate bnot (n+n) b = b :=
nat.rec_on n
(rfl)
(assume n ih,
calc iterate bnot ((n+1)+(n+1)) b = iterate bnot (n+n+2) b : by simp
... = iterate bnot (n+n) (bnot (bnot b)) : rfl
... = iterate bnot (n+n) b : by rw bnot_bnot
... = b : ih)

open list

section 
universe u
variable {α : Type u}

lemma init_cons (a : α) : ∀ {l : list α}, l ≠ [] → init (a::l) = a::init l
| []      := (assume h, absurd rfl h)
| (b::l₁) := assume h, show init (a::b::l₁) = a::init (b::l₁), from rfl

lemma init_append (l : list α) (a : α) : init (l++[a]) = l :=
list.rec_on l
(rfl)
(assume b l₁ ih,
have l₁++[a] ≠ [], from append_ne_nil_of_ne_nil_right _ _ (λ h, list.no_confusion h),
  calc init (b::l₁++[a]) = init (b::(l₁++[a])) : by simp
  ... = b::init(l₁++[a]) : init_cons _ this
  ... = b::l₁ : by rw ih
)

/- The following two functions rotate a given list. -/
def forward : list α → list α
| nil    := nil
| (a::l) := l++[a]

def backward : list α → list α
| nil    := nil
| (a::l) := (last (a::l) (λ h, list.no_confusion h))::(init (a::l))

lemma backward_eq_last_init_of_ne_nil : 
  ∀ (l : list α) (h : l ≠ []), backward l = last l h::(init l)
| []      h := absurd rfl h
| (a::l₁) h := rfl

lemma backward_append_eq_cons (l : list α) (a : α) : 
backward (l++[a]) = a::l :=
have l++[a] ≠ [], from 
  append_ne_nil_of_ne_nil_right _ _ (λ h, list.no_confusion h),
calc backward (l++[a]) = (last (l++[a]) _)::(init (l++[a])) : 
    backward_eq_last_init_of_ne_nil _ 
    (append_ne_nil_of_ne_nil_right l [a] (λ h, list.no_confusion h))
  ... = a::l : by rw [last_append l this, init_append l a]

end

section
@[derive decidable_eq]
inductive symbol : Type
| A : symbol
| B : symbol -- B is blank
-- C : symbol  -- could add more symbols if desired

open symbol

instance symbol_inhabited : inhabited symbol := inhabited.mk B

-- To make it possible to show configurations with #eval.
private def symbol.repr : symbol → string
| A := "A"
| B := "B"

instance symbol_has_repr : has_repr symbol := 
⟨symbol.repr⟩

/-
A cyclic tape is represented by a list, with the head of the list 
corresponding to the scanned square.  When the head of a Turing machine moves
left or right, the tape is rotated by one of the functions backward and 
forward defined above.
-/
notation `tape` := list symbol

notation `blank` n := repeat B n -- blank tape of length n

def scanned (l : tape) := head l
def rest (l : tape) := tail l

end

inductive dir | L | R | S
open dir

def move : dir → tape → tape
| L := backward
| R := forward
| S := λ x, x

section
variable α : Type
variables [fintype α] [decidable_eq α]

-- 1. The definition of a Turing machine
structure TM :=
(start : α)
(accept: α)
(reject : α)
(δ : α → symbol → symbol × α × dir)

notation `configuration` α := (α × tape)

end

section
variable {α : Type}
variables [fintype α] [decidable_eq α]

-- 2. A one-step computation of a Turing machine
def next (M : TM α) (c : configuration α) : configuration α :=
-- if (c.1 = M.accept ∨ c.1 = M.reject) then c else
let (q, t) := c in
let (s₁, q₁, d) := M.δ q (scanned t) in
(q₁, move d (s₁::(rest t)))

def steps (M : TM α) (n : ℕ) (c : configuration α) : configuration α :=
iterate (next M) n c

lemma steps_add (M : TM α) (m n : ℕ) (c : configuration α): 
  steps M (m + n) c = steps M m (steps M n c) :=
iterate_add (next M) m n c

def trace (M : TM α) : ℕ → (configuration α) → list (configuration α)
| 0     c := [c]
| (m+1) c := let c₁ := next M c in (c::(trace m c₁))

def halts_in (M : TM α) (m : ℕ) (c : configuration α) : Prop :=
(steps M m c).1 = M.accept

-- 3. The definition of the halting predicate
def halts (M : TM α) (tp : tape) : Prop :=
∃ m, halts_in M m (M.start, tp)

def clears_and_halts_in (M : TM α) (m : ℕ) (c : configuration α) : Prop :=
let n := length c.2 in steps M m c = (M.accept, blank n)

instance (M : TM α) (m : ℕ) (c : configuration α) :
  decidable (clears_and_halts_in M m c) := prod.decidable_eq _ _

def clears_and_halts (M : TM α) (tp : tape) : Prop :=
∃ m, clears_and_halts_in M m (M.start, tp)

end

/-
4. A Turing machine that, given an input cyclic tape of unknown size and 
content, clears the tape and halts.
-/
section eraser

@[derive decidable_eq]
inductive state : Type
| Start
| Right (twoAs : bool) (parity : bool) 
| Shift (parity : bool)
| Left (parity : bool)
| Accept 
| Reject -- not used

/- Meanings of the states
parity -- the parity of the distance traveled right from the origin
Start -- write an A at the origin and move right
Right twoAs -- move right until an A is found; 
  delete the found A if it's not the one placed at the origin (i.e., if twoAs = tt)
Shift -- shift A one square to the left
Left -- move left until an A is found; 
  when an A is found and the parity is odd, then the A has been shifted and
  consequently is the only remaining A, in which case delete A and accept; 
  otherwise there are at least two As left, so let twoAs := tt
-/

open state
-- Adapted from https://leanprover-community.github.io/archive/113488general/71488fintypefromenumeratedtype.html
def state.of_fin : fin 11 → state
| ⟨0, _⟩ := Start
| ⟨1, _⟩ := Right ff ff
| ⟨2, _⟩ := Right ff tt
| ⟨3, _⟩ := Shift ff
| ⟨4, _⟩ := Shift tt
| ⟨5, _⟩ := Left ff
| ⟨6, _⟩ := Left tt
| ⟨7, _⟩ := Right tt ff
| ⟨8, _⟩ := Right tt tt
| ⟨9, _⟩ := Accept
| _ := Reject

instance : fintype state :=
fintype.of_surjective state.of_fin 
(λ x, state.cases_on x
(exists.intro 0 rfl)
(λ twoAs parity, match twoAs, parity with
| ff, ff := exists.intro 1 rfl
| ff, tt := exists.intro 2 rfl
| tt, ff := exists.intro 7 rfl
| tt, tt := exists.intro 8 rfl
end )
(λ parity, match parity with
| ff := exists.intro 3 rfl
| tt := exists.intro 4 rfl
end )
(λ parity, match parity with
| ff := exists.intro 5 rfl
| tt := exists.intro 6 rfl
end )
(exists.intro 9 rfl)
(exists.intro 10 rfl) )

-- To make it possible to show configurations with #eval.
private def state.repr : state → string
| Start := "Start"
| (Right twoAs parity) := 
    "Right "++(has_repr.repr twoAs)++" "++(has_repr.repr parity)
| (Shift parity) := "Shift "++(has_repr.repr parity)
| (Left parity) := "Left "++(has_repr.repr parity)
| Accept := "Accept"
| Reject := "Reject"

instance state_has_repr : has_repr state :=
⟨state.repr⟩

open symbol

def eraser : TM state :=
{start := Start, accept := Accept, reject := Reject, 
δ := λ q s,
match q, s with
| Start, _ := (A, Right ff ff, R)
| (Right twoAs parity), A := 
    match twoAs with 
    | ff := (B, Shift (!parity), L) 
    | tt := (B, Right ff (!parity), R) 
    end
| (Right twoAs parity), _ := (B, Right twoAs (!parity), R)
| (Shift parity), A := 
    match parity with 
    | ff := (B, Accept, S) 
    | tt := (A, Right ff ff, R) 
    end
| (Shift parity), _ := (A, Left (!parity), L)
| (Left parity), A := 
    match parity with 
    | ff := (B, Accept, S) 
    | tt := (A, Right tt ff, R) 
    end
| (Left parity), _ := (B, Left (!parity), L)
| Accept, _ := (B, Accept, S)
| _, A := (A, Reject, S) -- not used
| _, B := (B, Reject, S) -- not used
end
}

-- 5. Traces of computation of the machine on concrete input tapes
section examples

#reduce trace eraser 18 (Start, [A,A,B,A])
/- 
[
(Start, [A, A, B, A]), 
(Right ff ff, [A, B, A, A]), 
(Shift tt, [A, B, B, A]), 
(Right ff ff, [B, B, A, A]), 
(Right ff tt, [B, A, A, B]), 
(Right ff ff, [A, A, B, B]), 
(Shift tt, [B, B, A, B]), 
(Left ff, [B, A, B, A]), 
(Left tt, [A, B, A, B]), 
(Right tt ff, [B, A, B, A]), 
(Right tt tt, [A, B, A, B]), 
(Right ff ff, [B, A, B, B]), 
(Right ff tt, [A, B, B, B]), 
(Shift ff, [B, B, B, B]), 
(Left tt, [B, A, B, B]), 
(Left ff, [B, B, A, B]), 
(Left tt, [B, B, B, A]), 
(Left ff, [A, B, B, B]), 
(Accept, [B, B, B, B])
]
-/

#reduce steps eraser 18 (Start, [A,A,B,A])

#reduce trace eraser 30 (Start, [A,B,A,B,B,A,B])
#eval to_bool (clears_and_halts_in eraser 29 (Start, [A,B,A,B,B,A,B]))
#eval to_bool (clears_and_halts_in eraser 30 (Start, [A,B,A,B,B,A,B]))

#reduce trace eraser 48 (Start, [A,B,A,B,B,A,B,A,B])

-- #reduce trace eraser 68 (Start, [A,B,A,B,B,A,B,A,B,A]) -- timeout
#eval trace eraser 68 (Start, [A,B,A,B,B,A,B,A,B,A])
#eval to_bool (clears_and_halts_in eraser 67 (Start, [A,B,A,B,B,A,B,A,B,A]))
#eval to_bool (clears_and_halts_in eraser 68 (Start, [A,B,A,B,B,A,B,A,B,A]))

#eval trace eraser 80 (Start, [A,B,A,B,B,A,A,A,B,A])

#reduce trace eraser 4 (Start, [A])
#reduce trace eraser 4 (Start, [B])

#reduce trace eraser 8 (Start, [A,A])
#reduce trace eraser 6 (Start, [A,B])
#reduce trace eraser 8 (Start, [B,A])
#reduce trace eraser 6 (Start, [B,B])

end examples

lemma Left_on_B (n : ℕ) (a : symbol) : 
  ∀ (parity : bool) (l : tape), 
    steps eraser (n+1) (Left parity, B::(l++(a::(blank n)))) = 
      (Left (iterate bnot (n+1) parity), a::(blank (n+1))++l) :=
nat.rec_on n
(assume parity l,
  calc steps eraser 1 (Left parity, B::(l++(a::(blank 0)))) = 
      next eraser (Left parity, B::(l++(a::[]))) : rfl
    ... = (Left (!parity), backward (B::(l++(a::[])))) : rfl
    ... = (Left (!parity), backward ((B::l)++[a])) : by simp
    ... = (Left (!parity), a::B::l) : by rw backward_append_eq_cons
    ... = (Left (!parity), a::(blank 1)++l) : by simp
    ... = (Left (iterate bnot 1 parity), a::(blank 1)++l) : rfl )
(assume n ih,
  assume parity l,
  have h₁ : cons B (l++(a::(blank (n+1)))) = (B::l)++(a::blank n)++[B], from
    calc cons B (l++(a::(blank (n+1)))) = 
        B::(l++(a::((blank n)++(blank 1)))) : by rw repeat_add
      ... = B::(l++(a::((blank n)++[B]))) : rfl
      ... = (B::l)++(a::blank n)++[B] : by simp ,
  have h₂ : a::(blank (n+1))++(B::l) = a::(blank (n+2))++l, from
    calc a::(blank (n+1))++(B::l) = a::((blank (n+1))++[B])++l : by simp
      ... = a::((blank (n+1))++(blank 1))++l : rfl
      ... = a::(blank (n+2))++l : by rw repeat_add B (n+1) 1 ,
  calc steps eraser (n+2) (Left parity, B::(l++(a::(blank (n+1))))) =
      steps eraser (n+1) 
        (next eraser (Left parity, B::(l++(a::(blank (n+1)))))) : rfl
    ... = steps eraser (n+1) 
        (Left (!parity), backward (B::(l++(a::(blank (n+1)))))) : rfl
    ... = steps eraser (n+1) 
        (Left (!parity), backward ((B::l)++(a::blank n)++[B])) : by rw h₁
    ... = steps eraser (n+1) (Left (!parity), B::((B::l)++(a::blank n))) :
      by rw backward_append_eq_cons
    ... = (Left (iterate bnot (n+1) (!parity)), a::(blank (n+1))++(B::l)) :
      by rw ih (!parity) (B::l)
    ... = (Left (iterate bnot (n+2) parity), a::(blank (n+1))++(B::l)) : rfl
    ... = (Left (iterate bnot (n+2) parity), a::(blank (n+2))++l) : 
      by rw h₂ )

/- #print Left_on_B -/

lemma Right_on_B (twoAs : bool) (n : ℕ) : ∀ (parity : bool) (l : tape), 
  steps eraser n (Right twoAs parity, (blank n)++l) = 
    (Right twoAs (iterate bnot n parity), l++(blank n)) :=
nat.rec_on n
(assume parity l,
  calc steps eraser 0 (Right twoAs parity, (blank 0)++l) = 
      (Right twoAs parity, l) : rfl
    ... = (Right twoAs (iterate bnot 0 parity), l++(blank 0)) : by simp )
(assume n ih,
  assume parity l,
  calc steps eraser (n+1) (Right twoAs parity, (blank (n+1))++l) =
      steps eraser n (next eraser (Right twoAs parity, (blank (n+1))++l)) : rfl
    ... = steps eraser n (Right twoAs (!parity), ((blank n)++l)++[B]) : rfl
    ... = steps eraser n (Right twoAs (!parity), (blank n)++(l++[B])) : 
      by simp
    ... = (Right twoAs (iterate bnot n (!parity)), l++[B]++(blank n)) :
      by rw ih (!parity) (l++[B])
    ... = (Right twoAs (iterate bnot (n+1) parity), l++(blank (n+1))) : by simp )

/- #print Right_on_B -/

lemma count_A_succ (l : tape) : ∀ m : ℕ, count A l = m+1 → 
  ∃ (n : ℕ) (l₁ : tape), l = (blank n)++(A::l₁) ∧ count A l₁ = m :=
list.rec_on l
(assume m h,
  have count A [] = 0, from rfl,
  have m+1 = 0, from h ▸ this,
  absurd this (succ_ne_zero _) )
(assume a l₂ ih,
  symbol.cases_on a
  (assume m h, -- a = A
    have count A (A::l₂) = (count A l₂) + 1, from count_cons_self A l₂,
    have m+1 = (count A l₂) + 1, from h ▸ this,
    have h₁ : m = count A l₂, from add_right_cancel this,
    have h₂ : cons A l₂ = (blank 0)++(A::l₂), from rfl,
    ⟨0, l₂, h₂, eq.symm h₁⟩ )
  (assume m h, -- a = B
    have count A (B::l₂) = count A l₂, 
      from count_cons_of_ne (λ h, symbol.no_confusion h) l₂,
    have count A l₂ = m+1, from eq.symm (h ▸ this),
    exists.elim (ih m this)
    (assume n h₁,
      exists.elim h₁
      (assume l₁ h₂,
        have cons B l₂ = (blank (n+1))++A::l₁, from 
          calc cons B l₂ = cons B (((blank n)++A::l₁)) : h₂.left ▸ rfl
            ... = (B::(blank n))++A::l₁ : by rw cons_append
            ... = (blank (n+1))++A::l₁ : rfl ,
        ⟨n+1, l₁, this, h₂.right⟩ ) ) ) )

/- #print count_A_succ -/

lemma count_A_zero (l : tape) : count A l = 0 → l = blank (length l) :=
list.rec_on l
(assume h, rfl)
(assume a l₁ ih,
  symbol.cases_on a
  (assume h, -- a = A
    have count A (A::l₁) = (count A l₁) + 1, from rfl,
    have 0 = (count A l₁) + 1, from h ▸ this,
    absurd this (λ h, nat.no_confusion h) )
  (assume h, -- a = B
    have count A (B::l₁) = (count A l₁), from rfl,
    have count A l₁ = 0, from this ▸ h,
    have l₁ = blank (length l₁), from ih this,
    calc cons B l₁ = B::blank (length l₁) : this ▸ rfl
      ... = blank ((length l₁)+1) : rfl
      ... = blank (length (B::l₁)) : rfl ) )

/- #print count_A_zero -/

lemma last_A (m n : ℕ) : m+n ≠ 0 → 
  steps eraser (m+n*2+3) 
  (Right ff (iterate bnot (m+1) tt), (blank n)++A::(blank m)) = 
  (Accept, blank (m+n+1)) :=
assume : m+n ≠ 0,
have ∃ p : ℕ, m+n = p+1, from exists_eq_succ_of_ne_zero this,
exists.elim this 
(assume p (h : m+n = p+1),
have h₁ : steps eraser n
  (Right ff (iterate bnot (m+1) tt), (blank n)++A::(blank m)) = 
    (Right ff (iterate bnot (m+n+1) tt), A::(blank p)++[B]), from
  calc steps eraser n 
    (Right ff (iterate bnot (m+1) tt), (blank n)++A::(blank m)) = 
    (Right ff (iterate bnot n (iterate bnot (m+1) tt)), A::(blank m)++(blank n)) : 
      Right_on_B ff n (iterate bnot (m+1) tt) (A::(blank m))
    ... = (Right ff (iterate bnot (n+(m+1)) tt), A::(blank m)++(blank n)) : 
      by rw ←iterate_add
    ... = (Right ff (iterate bnot (m+n+1) tt), A::((blank m)++(blank n))) : by simp 
    ... = (Right ff (iterate bnot (m+n+1) tt), A::(blank (m+n))) : 
      by rw repeat_add
    ... = (Right ff (iterate bnot (m+n+1) tt), A::(blank p+1)) : by rw h
    ... = (Right ff (iterate bnot (m+n+1) tt), A::((blank p)++(blank 1))) : 
      by rw repeat_add
    ... = (Right ff (iterate bnot (m+n+1) tt), A::(blank p)++[B]) : by simp ,
have h₂ : next eraser (Right ff (iterate bnot (m+n+1) tt), A::(blank p)++[B]) =
    (Shift (iterate bnot (m+n+2) tt), B::(blank p)++[B]), from
  calc next eraser (Right ff (iterate bnot (m+n+1) tt), A::(blank p)++[B]) =
    (Shift (!(iterate bnot (m+n+1) tt)), backward (B::(blank p)++[B])) : rfl
    ... = (Shift (!(iterate bnot (m+n+1) tt)), B::B::(blank p)) : 
      by rw backward_append_eq_cons 
    ... = (Shift (!(iterate bnot (m+n+1) tt)), B::(blank (p+1))) : rfl
    ... = (Shift (!(iterate bnot (m+n+1) tt)), B::(blank p)++[B]) : 
      by rw repeat_add; simp
    ... = (Shift (iterate bnot (m+n+2) tt), B::(blank p)++[B]) : 
      by rw ←iterate_succ' bnot (m+n+1) tt,
have h₃ : next eraser (Shift (iterate bnot (m+n+2) tt), B::(blank p)++[B]) =
  (Left (iterate bnot (m+n+3) tt), B::A::(blank p)), from
  calc next eraser (Shift (iterate bnot (m+n+2) tt), B::(blank p)++[B]) =
    (Left (!(iterate bnot (m+n+2) tt)), backward (A::(blank p)++[B])) : rfl
    ... = (Left (!(iterate bnot (m+n+2) tt)), B::(A::(blank p))) : 
      by rw backward_append_eq_cons
    ... = (Left (iterate bnot (m+n+3) tt), B::A::(blank p)) : 
      by rw ←iterate_succ' bnot (m+n+2) tt ,
have h₄ : steps eraser (m+n) (Left (iterate bnot (m+n+3) tt), B::(A::(blank p))) = 
    (Left ff, A::(blank (m+n))), from
  calc steps eraser (m+n) (Left (iterate bnot (m+n+3) tt), B::(A::(blank p))) = 
    steps eraser (p+1) (Left (iterate bnot (m+n+3) tt), B::(A::(blank p))) : by rw h
    ... = (Left (iterate bnot (p+1) (iterate bnot (m+n+3) tt)), 
        A::(blank (p+1))++[]) :
      Left_on_B p A (iterate bnot (m+n+3) tt) []
    ... = (Left (iterate bnot (p+1) (iterate bnot (m+n+3) tt)), A::(blank (p+1))) : 
      by rw append_nil 
    ... = (Left (iterate bnot (m+n) (iterate bnot (m+n+3) tt)), A::(blank (m+n))) : 
      by rw h
    ... = (Left (iterate bnot ((m+n)+(m+n+3)) tt), A::(blank (m+n))) :
      by rw ←(iterate_add bnot (m+n) (m+n+3) tt)
    ... = (Left (iterate bnot ((m+n)+(m+n)+3) tt), A::(blank (m+n))) : by simp
    ... = (Left (iterate bnot ((m+n)+(m+n)) ff), A::(blank (m+n))) : rfl
    ... = (Left ff, A::(blank (m+n))) : by rw iterate_bnot ,
have h₅ : next eraser (Left ff, A::(blank (m+n))) = (Accept, blank (m+n+1)), 
  from rfl ,
have m+n*2+3 = 1+(m+n)+1+1+n, from
  calc m+n*2+3 = m+(0+n+n)+3 : rfl
    ... = 1+(m+n)+1+1+n : by simp,
calc steps eraser (m+n*2+3) 
  (Right ff (iterate bnot (m+1) tt), (blank n)++(A::(blank m))) = 
    steps eraser (1+(m+n)+1+1+n) 
      (Right ff (iterate bnot (m+1) tt), (blank n)++(A::(blank m))) : by rw this
  ... = steps eraser (1+(m+n)+1+1) (steps eraser n
      (Right ff (iterate bnot (m+1) tt), (blank n)++(A::(blank m)))) : 
    by rw steps_add 
  ... = steps eraser (1+(m+n)+1+1) 
      (Right ff (iterate bnot (m+n+1) tt), A::(blank p)++[B]) : by rw h₁
  ... = steps eraser (1+(m+n)+1) (next eraser 
      (Right ff (iterate bnot (m+n+1) tt), A::(blank p)++[B])) : rfl
  ... = steps eraser (1+(m+n)+1) 
      (Shift (iterate bnot (m+n+2) tt), B::(blank p)++[B]) :
    by rw h₂
  ... = steps eraser (1+(m+n)) 
      (next eraser (Shift (iterate bnot (m+n+2) tt), B::(blank p)++[B])) : rfl
  ... = steps eraser (1+(m+n)) 
      (Left (iterate bnot (m+n+3) tt), B::(A::(blank p))) : 
    by rw h₃
  ... = steps eraser 1 
      (steps eraser (m+n) (Left (iterate bnot (m+n+3) tt), B::(A::(blank p)))) :
    by rw steps_add
  ... = steps eraser 1 (Left ff, A::(blank (m+n))) : by rw h₄
  ... = next eraser (Left ff, A::(blank (m+n))) : rfl
  ... = (Accept, blank (m+n+1)) : h₅ )

/- #print last_A -/

lemma more_than_one_A (m n : ℕ) (l : tape) : 
steps eraser (m*2+n*3+2)
(Right ff (iterate bnot (m+1) tt), (blank n)++(A::l++A::(blank m))) = 
  (Right ff (iterate bnot (m+n+1) tt), B::l++A::(blank m+n)) :=
have m+n = 0 ∨ m+n ≠ 0, from decidable.em (m+n = 0),
or.elim this
(assume : m+n = 0,
  have hm0n0 : m = 0 ∧ n = 0, from eq_zero_of_add_eq_zero ‹m+n = 0›,
  calc steps eraser (m*2+n*3+2)
      (Right ff (iterate bnot (m+1) tt), (blank n)++(A::l++A::(blank m))) =
      steps eraser (0*2+0*3+2) 
      (Right ff (iterate bnot (0+1) tt), (blank 0)++(A::l++A::(blank 0))) : 
      by rw [hm0n0.left, hm0n0.right]
    ... = steps eraser 2 (Right ff ff, A::l++[A]) : by simp
    ... = next eraser (next eraser (Right ff ff, A::l++[A])) : rfl
    ... = next eraser (Shift tt, backward (B::l++[A])) : rfl
    ... = next eraser (Shift tt, A::B::l) : by rw backward_append_eq_cons
    ... = (Right ff ff, B::l++[A]) : rfl
    ... = (Right ff (iterate bnot (m+n+1) tt), B::l++A::(blank m+n)) : 
      by rw [hm0n0.left, hm0n0.right]; simp )
(assume : m+n ≠ 0,
  have ∃ p : ℕ, m+n = p+1, from exists_eq_succ_of_ne_zero this,
  exists.elim this
  (assume p (h : m+n = p+1),
    have h₁ : steps eraser n 
      (Right ff (iterate bnot (m+1) tt), (blank n)++(A::l++A::(blank m))) =
      (Right ff (iterate bnot (m+n+1) tt), A::l++A::(blank p)++[B]), from
    calc steps eraser n 
      (Right ff (iterate bnot (m+1) tt), (blank n)++(A::l++A::(blank m))) =
      (Right ff (iterate bnot n (iterate bnot (m+1) tt)), 
      A::l++A::(blank m)++(blank n)) :
        Right_on_B ff n (iterate bnot (m+1) tt) (A::l++A::(blank m))
      ... = (Right ff (iterate bnot (n+(m+1)) tt), A::l++A::(blank m)++(blank n)) :
        by rw ←iterate_add
      ... = (Right ff (iterate bnot (m+n+1) tt), A::l++A::((blank m)++(blank n))) : 
        by simp
      ... = (Right ff (iterate bnot (m+n+1) tt), A::l++A::(blank (m+n))) : 
        by rw repeat_add 
      ... = (Right ff (iterate bnot (m+n+1) tt), A::l++A::(blank (p+1))) : by rw h
      ... = (Right ff (iterate bnot (m+n+1) tt), A::l++A::((blank p)++(blank 1))) :
        by rw repeat_add
      ... = (Right ff (iterate bnot (m+n+1) tt), A::l++A::(blank p)++[B]) : by simp ,
    have h₂ : next eraser 
      (Right ff (iterate bnot (m+n+1) tt), A::l++A::(blank p)++[B]) =
        (Shift (iterate bnot (m+n+2) tt), B::B::l++A::(blank p)), from
      calc next eraser (Right ff (iterate bnot (m+n+1) tt), A::l++A::(blank p)++[B]) =
          (Shift (!(iterate bnot (m+n+1) tt)), backward (B::l++A::(blank p)++[B])) : rfl
        ... = (Shift (!(iterate bnot (m+n+1) tt)), B::(B::l++A::(blank p))) : 
          by rw backward_append_eq_cons
        ... = (Shift (iterate bnot (m+n+2) tt), B::(B::l++A::(blank p))) : 
          by rw ←iterate_succ' bnot _ ,
    have p = 0 ∨ p ≠ 0, from decidable.em (p = 0),
    have h₃ : steps eraser ((m+n)*2+1) 
      (Shift (iterate bnot (m+n+2) tt), B::B::l++A::(blank p)) = 
      (Right ff (iterate bnot (m+n+1) tt), B::l++A::(blank m+n)), from
    or.elim this
    (assume : p = 0,
      have m+n = 1, from zero_add 1 ▸ ‹p = 0› ▸ h,
      have h₄ : next eraser (Shift (iterate bnot 3 tt), B::B::l++[A]) =
        (Left tt, A::A::B::l), from 
      calc next eraser (Shift (iterate bnot 3 tt), B::B::l++[A]) =
          (Left (!(iterate bnot 3 tt)), backward (A::B::l++[A])) : rfl
        ... = (Left tt, A::A::B::l) : by rw backward_append_eq_cons; simp ,
      have h₅ : next eraser (Left tt, A::A::B::l) = (Right tt ff, A::B::l++[A]), 
        from rfl,
      have h₆ : next eraser (Right tt ff, A::B::l++[A]) = 
        (Right ff tt, B::l++[A]++[B]), by refl; simp,
      calc steps eraser ((m+n)*2+1) 
        (Shift (iterate bnot (m+n+2) tt), B::B::l++A::(blank p)) = 
        steps eraser 3 (Shift (iterate bnot 3 tt), B::B::l++[A]) : 
          by rw [‹m+n = 1›, ‹p = 0›]; simp
        ... = next eraser (next eraser (next eraser 
            (Shift (iterate bnot 3 tt), B::B::l++[A]))) : rfl
        ... = (Right ff tt, B::l++[A]++[B]) : by rw [h₄, h₅, h₆]
        ... = (Right ff (iterate bnot (1+1) tt), B::l++A::(blank 1)) : by simp
        ... = (Right ff (iterate bnot (m+n+1) tt), B::l++A::(blank (m+n))) : 
          by rw ‹m+n = 1› )
    (assume : p ≠ 0,
      have ∃ q : ℕ, p = q+1, from exists_eq_succ_of_ne_zero this,
      exists.elim this
      (assume q, assume : p = q+1,
        have h₄ : next eraser 
          (Shift (iterate bnot (m+n+2) tt), B::B::l++A::(blank p)) =
          (Left (iterate bnot (m+n+3) tt), B::A::B::l++A::(blank q)), from
          calc next eraser 
            (Shift (iterate bnot (m+n+2) tt), B::B::l++A::(blank p)) =
            next eraser (Shift (iterate bnot (m+n+2) tt), B::B::l++A::(blank (q+1))) :
              by rw ‹p = q+1›
            ... = next eraser 
                (Shift (iterate bnot (m+n+2) tt), B::B::l++A::(blank q)++[B]) :
              by rw repeat_add; simp
            ... = (Left (!(iterate bnot (m+n+2) tt)), 
                backward (A::B::l++A::(blank q)++[B])) : 
              rfl
            ... = (Left (iterate bnot (m+n+3) tt), B::(A::B::l++A::(blank q))) : 
              by rw [backward_append_eq_cons, ←iterate_succ' bnot _ _]
            ... = (Left (iterate bnot (m+n+3) tt), B::A::B::l++A::(blank q)) : 
              by simp ,
        have h₅ : steps eraser p 
          (Left (iterate bnot (m+n+3) tt), B::A::B::l++A::(blank q)) =
          (Left tt, A::(blank p)++A::B::l), from
          calc steps eraser p 
            (Left (iterate bnot (m+n+3) tt), B::A::B::l++A::(blank q)) =
            steps eraser (q+1) 
            (Left (iterate bnot (m+n+3) tt), B::(A::B::l++A::(blank q))) : 
              by rw ‹p = q+1›; simp
            ... = (Left (iterate bnot (q+1) (iterate bnot (m+n+3) tt)), 
                A::(blank q+1)++A::B::l) :
              by rw Left_on_B q A (iterate bnot (m+n+3) tt) (A::B::l)
            ... = (Left (iterate bnot (p+(m+n)+3) tt), A::(blank p)++A::B::l) :
              by rw [←‹p = q+1›, ←iterate_add bnot _ _ _]; simp
            ... = (Left (iterate bnot (p+p+4) tt), A::(blank p)++A::B::l) :
              by rw ‹m+n = p+1›; simp
            ... = (Left (iterate bnot (p+p) tt), A::(blank p)++A::B::l) : rfl
            ... = (Left tt, A::(blank p)++A::B::l) : by rw iterate_bnot ,
        have h₆ : next eraser (Left tt, A::(blank p)++A::B::l) = 
          (Right tt ff, (blank p)++(A::B::l++[A])), from
          calc next eraser (Left tt, A::(blank p)++A::B::l) = 
            (Right tt ff, (blank p)++A::B::l++[A]) : rfl
            ... = (Right tt ff, (blank p)++(A::B::l++[A])) : by simp ,
        have h₇ : steps eraser p (Right tt ff, (blank p)++(A::B::l++[A])) = 
          (Right tt (iterate bnot p ff), A::B::l++[A]++(blank p)), 
          from Right_on_B tt p ff (A::B::l++[A]) ,
        have h₈ : next eraser 
          (Right tt (iterate bnot p ff), A::B::l++[A]++(blank p)) = 
          (Right ff (iterate bnot (m+n+1) tt), B::l++A::(blank (m+n))), from
          calc next eraser (Right tt (iterate bnot p ff), A::B::l++[A]++(blank p)) =
            (Right ff (!(iterate bnot p ff)), B::l++[A]++(blank p)++[B]) : rfl
            ... = (Right ff (iterate bnot (p+1) ff), B::l++[A]++(blank p)++[B]) :
              by rw ←iterate_succ' bnot p _ 
            ... = (Right ff (iterate bnot (p+1) ff), B::l++[A]++(blank (p+1))) :
              by rw repeat_add B; simp
            ... = (Right ff (iterate bnot (m+n) ff), B::l++[A]++(blank (m+n))) : 
              by rw ←‹m+n = p+1›
            ... = (Right ff (iterate bnot (m+n+1) tt), B::l++[A]++(blank (m+n))) : 
              rfl 
            ... = (Right ff (iterate bnot (m+n+1) tt), B::l++A::(blank (m+n))) : 
              by simp ,
        calc steps eraser ((m+n)*2+1) 
          (Shift (iterate bnot (m+n+2) tt), B::B::l++A::(blank p)) =
          steps eraser ((p+1)*2+1) 
          (Shift (iterate bnot (m+n+2) tt), B::B::l++A::(blank p)) :
            by rw ‹m+n = p+1›
          ... = steps eraser (0+(p+1)+(p+1)+1) 
              (Shift (iterate bnot (m+n+2) tt), B::B::l++A::(blank p)) :
            rfl
          ... = steps eraser (1+p+1+p+1) 
              (Shift (iterate bnot (m+n+2) tt), B::B::l++A::(blank p)) : 
            by simp
          ... = steps eraser (1+p+1+p) 
              (next eraser 
              (Shift (iterate bnot (m+n+2) tt), B::B::l++A::(blank p))) : 
            rfl
          ... = steps eraser (1+p+1+p) 
              (Left (iterate bnot (m+n+3) tt), B::A::B::l++A::(blank q)) :
            by rw h₄
          ... = steps eraser (1+p+1) (steps eraser p
              (Left (iterate bnot (m+n+3) tt), B::A::B::l++A::(blank q))) : 
            by rw steps_add
          ... = steps eraser (1+p+1) (Left tt, A::(blank p)++A::B::l) : by rw h₅
          ... = steps eraser (1+p) (next eraser (Left tt, A::(blank p)++A::B::l)) : 
            rfl
          ... = steps eraser (1+p) (Right tt ff, (blank p)++(A::B::l++[A])) : 
            by rw h₆
          ... = steps eraser 1 (steps eraser p 
              (Right tt ff, (blank p)++(A::B::l++[A]))) : 
            by rw steps_add
          ... = steps eraser 1 
              (Right tt (iterate bnot p ff), A::B::l++[A]++(blank p)) : 
            by rw h₇
          ... = next eraser 
              (Right tt (iterate bnot p ff), A::B::l++[A]++(blank p)) : rfl
          ... = (Right ff (iterate bnot (m+n+1) tt), B::l++A::(blank (m+n))) : 
            by rw h₈ ) ) ,
      have m*2+n*3+2 = (m+n)*2+1+1+n, from
        calc m*2+n*3+2 = (0+m+m)+(0+n+n+n)+2 : rfl
          ... = (0+(m+n)+(m+n))+1+1+n : by simp
          ... = (m+n)*2+1+1+n : rfl,
      calc steps eraser (m*2+n*3+2)
        (Right ff (iterate bnot (m+1) tt), (blank n)++(A::l++A::(blank m))) = 
          steps eraser ((m+n)*2+1+1+n)
          (Right ff (iterate bnot (m+1) tt), (blank n)++(A::l++A::(blank m))) : 
          by rw this
        ... = steps eraser ((m+n)*2+1) (steps eraser 1 (steps eraser n 
            (Right ff (iterate bnot (m+1) tt), (blank n)++(A::l++A::(blank m))))) : 
          by rw [steps_add, steps_add]
        ... = steps eraser ((m+n)*2+1) (steps eraser 1 
            (Right ff (iterate bnot (m+n+1) tt), A::l++A::(blank p)++[B])) : 
          by rw h₁
        ... = steps eraser ((m+n)*2+1) (next eraser
            (Right ff (iterate bnot (m+n+1) tt), A::l++A::(blank p)++[B])) : rfl
        ... = steps eraser ((m+n)*2+1) 
            (Shift (iterate bnot (m+n+2) tt), B::B::l++A::(blank p)) : by rw h₂
        ... = (Right ff (iterate bnot (m+n+1) tt), B::l++A::(blank m+n)) : 
          by rw h₃ ) )

-- #print more_than_one_A

lemma any_number_of_As (k : ℕ) : ∀ (l : tape) (m : ℕ), count A l = k → 
  ∃ t : ℕ, steps eraser t (Right ff (iterate bnot (m+1) tt), l++A::(blank m)) = 
  (Accept, blank (m+(length l)+1)) :=
nat.rec_on k
(assume l m (h : count A l = 0),
  have h₁ : l = blank (length l), from count_A_zero l h,
  have h₂ : l++A::(blank m) = (blank (length l))++A::(blank m), 
    from h₁ ▸ eq.refl (l++A::(blank m)),
  or.elim (decidable.em (m+(length l) = 0))
  (assume h₃ : m+(length l) = 0,
    have h₄ : m = 0 ∧ length l = 0, from eq_zero_of_add_eq_zero h₃, 
    have h₅ : l++A::(blank m) = [A], from
      calc l++A::(blank m) = (blank (length l))++A::(blank m) : h₂
        ... = (blank 0)++A::(blank 0) : by rw [h₄.left, h₄.right]
        ... = [A] : by simp ,
    have m+(length l)+1 = 1, from eq.symm h₃ ▸ eq.refl (0+1),
    have h₆ : (blank (m+(length l)+1)) = [B], from
      calc (blank (m+(length l)+1)) = (blank 1) : by rw this
        ... = [B] : rfl ,
    have steps eraser 4 (Right ff (iterate bnot (m+1) tt), l++A::(blank m)) = 
      (Accept, blank (m+(length l)+1)), from
      calc steps eraser 4 (Right ff (iterate bnot (m+1) tt), l++A::(blank m)) = 
          steps eraser 4 (Right ff ff, l++A::(blank m)) : by rw h₄.left; simp
        ... = steps eraser 4 (Right ff ff, [A]) : by rw h₅
        ... = (Accept, [B]) : rfl
        ... = (Accept, blank (m+(length l)+1)) : by rw h₆ ,
    show ∃ t : ℕ, steps eraser t 
      (Right ff (iterate bnot (m+1) tt), l++A::(blank m)) = 
      (Accept, blank (m+(length l)+1)), from exists.intro 4 this )
  (assume h₃ : m+(length l) ≠ 0,
    have steps eraser (m+(length l)*2+3) 
      (Right ff (iterate bnot (m+1) tt), l++A::(blank m)) =
      (Accept, blank (m+(length l)+1)), from 
      calc steps eraser (m+(length l)*2+3) 
          (Right ff (iterate bnot (m+1) tt), l++A::(blank m)) =
          steps eraser (m+(length l)*2+3) 
          (Right ff (iterate bnot (m+1) tt), (blank (length l))++A::(blank m)) : 
          by rw h₂ 
        ... = (Accept, blank (m+(length l)+1)) : last_A m (length l) h₃ ,
    show ∃ t : ℕ, steps eraser t 
      (Right ff (iterate bnot (m+1) tt), l++A::(blank m)) = 
      (Accept, blank (m+(length l)+1)), 
      from exists.intro (m+(length l)*2+3) this ) )
(assume k₁ ih,
  assume l m (h : count A l = k₁+1),
  have ∃ (n : ℕ) (l₁ : tape), l = (blank n)++(A::l₁) ∧ count A l₁ = k₁, 
    from count_A_succ l k₁ h,
  exists.elim this (assume n h₁, 
  exists.elim h₁ (assume l₁ (h₂ : l = (blank n)++(A::l₁) ∧ count A l₁ = k₁),
    have h₃ : length (A::l₁) = (length l₁)+1, from rfl,
    have h₄ : length (blank n) = n, from length_repeat B n,
    have h₅ : length l = n+(length l₁)+1, from 
      calc length l = length ((blank n)++(A::l₁)) : by rw h₂.left
        ... = length (blank n) + length (A::l₁) : length_append _ _
        ... = n+(length l₁)+1 : by rw [h₃, h₄]; simp ,
    have h₆ : steps eraser (m*2+n*3+2) 
      (Right ff (iterate bnot (m+1) tt), l++A::(blank m)) 
      = (Right ff (iterate bnot (m+n+1) tt), B::l₁++A::(blank m+n)), from 
      calc steps eraser (m*2+n*3+2) 
        (Right ff (iterate bnot (m+1) tt), l++A::(blank m)) = 
          steps eraser (m*2+n*3+2) 
            (Right ff (iterate bnot (m+1) tt), (blank n)++(A::l₁)++A::(blank m)) :
          by rw h₂.left
        ... = steps eraser (m*2+n*3+2)
            (Right ff (iterate bnot (m+1) tt), (blank n)++(A::l₁++A::(blank m))) :
          by simp
        ... = (Right ff (iterate bnot (m+n+1) tt), B::l₁++A::(blank m+n)) : 
          more_than_one_A m n l₁ ,
    have h₇ : count A (B::l₁) = k₁, from h₂.right ▸ rfl,
    have h₈ : length (B::l₁) = (length l₁)+1, from rfl,
    have h₉ : ∃ t₁ : ℕ, steps eraser t₁ 
      (Right ff (iterate bnot (m+n+1) tt), B::l₁++A::(blank m+n)) = 
      (Accept, blank (m+n+(length (B::l₁))+1)), from ih (B::l₁) (m+n) h₇,
    exists.elim h₉ (assume t₁ h₁₀,
      have h₁₁ : steps eraser t₁ 
        (Right ff (iterate bnot (m+n+1) tt), B::l₁++A::(blank m+n)) =
        (Accept, blank (m+(length l)+1)), from
        calc steps eraser t₁ 
          (Right ff (iterate bnot (m+n+1) tt), B::l₁++A::(blank m+n)) =
          (Accept, blank (m+n+(length (B::l₁))+1)) : h₁₀
          ... = (Accept, blank (m+(n+(length l₁)+1)+1)) : by rw h₈; simp
          ... = (Accept, blank (m+(length l)+1)) : by rw h₅ ,
      have h₁₂ : steps eraser (t₁+(m*2+n*3+2)) 
        (Right ff (iterate bnot (m+1) tt), l++A::(blank m)) =
          (Accept, blank (m+(length l)+1)), from
        calc steps eraser (t₁+(m*2+n*3+2)) 
          (Right ff (iterate bnot (m+1) tt), l++A::(blank m)) =
          steps eraser t₁ (steps eraser (m*2+n*3+2)
          (Right ff (iterate bnot (m+1) tt), l++A::(blank m))) : by rw steps_add
          ... = steps eraser t₁ 
              (Right ff (iterate bnot (m+n+1) tt), B::l₁++A::(blank m+n)) : by rw h₆
          ... = (Accept, blank (m+(length l)+1)) : h₁₁ ,
      show ∃ t : ℕ, steps eraser t 
        (Right ff (iterate bnot (m+1) tt), l++A::(blank m)) = 
          (Accept, blank (m+(length l)+1)), 
        from exists.intro (t₁+(m*2+n*3+2)) h₁₂ ) ) ) )

-- #print any_number_of_As

/- 
6. A proof that the Turing machine, given any input tape, clears the tape and
halts.
-/
theorem clears_and_halts_on_all_tapes (l : tape) : length l ≠ 0 → 
  clears_and_halts eraser l :=
list.cases_on l
(assume h : length [] ≠ 0,
  have length [] = 0, from rfl,
  absurd this h )
(assume a l₁,
  assume h,
  have h₁ : next eraser (Start, a::l₁) = (Right ff ff, l₁++[A]), from 
    symbol.cases_on a rfl rfl,
  have ∃ t, steps eraser t (Right ff (iterate bnot 1 tt), l₁++A::(blank 0)) =
    (Accept, blank (0+(length l₁)+1)), 
      from any_number_of_As (count A l₁) l₁ 0 rfl,
  exists.elim this
  (assume t h₂,
    have 0+(length l₁)+1 = (length l₁)+1, by simp,
    have steps eraser t (Right ff ff, l₁++[A]) = (Accept, blank ((length l₁)+1)),
      from this ▸ h₂,
    have steps eraser (t+1) (Start, a::l₁) = (Accept, blank (length (a::l₁))), from
      calc steps eraser t (next eraser (Start, a::l₁)) = 
          steps eraser t (next eraser (Start, a::l₁)) : rfl
        ... = steps eraser t (Right ff ff, l₁++[A]) : by rw h₁
        ... = (Accept, blank ((length l₁)+1)) : this
        ... = (Accept, blank (length (a::l₁))) : rfl ,
    exists.intro (t+1) this ) )

-- #print clears_and_halts_on_all_tapes

end eraser

end CTM
