/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Coxeter.Dihedral
public import TauCeti.GroupTheory.Coxeter.Length

/-!
# The exchange condition characterizes Coxeter systems

Let `cs : CoxeterSystem M W` be a Coxeter system and `φ : W →* G` a homomorphism of groups, so
that the images `φ (s i)` of the simple reflections are involutions satisfying the braid
relations of `M`. Let `ℓ g` be the least number of letters of a word whose image is `g`. Suppose
that

* each product `φ (s i) * φ (s i')` has order exactly `M i i'`, and
* the images satisfy the **exchange condition**: if a word `ω` of least length spells `g` and
  `ℓ (g * φ (s i)) ≤ ℓ g`, then `g * φ (s i)` is spelled by `ω` with one of its letters deleted.

Then `φ` is injective (`CoxeterSystem.injective_of_exchange`) and preserves lengths
(`CoxeterSystem.length_eq_of_exchange`), so `G` is the Coxeter group of `M`, with the images of the
simple reflections as generators; `CoxeterSystem.ofExchange` is that Coxeter system on `G`. This
is the characterization of Coxeter systems by the exchange condition (Bourbaki, Chapter IV, §1,
no. 6, Theorem 1).

The exchange condition is stated with `≤` as in Bourbaki: no parity of lengths in `G` is assumed,
so the hypothesis covers multiplications that do not change the length, and the conclusion rules
them out. Where lengths change by exactly one under multiplication by a generator, as for the Weyl
group of a root system, the two forms agree.

## The argument

Call a word *minimal* if it has least length among the words with the same image in `G`. The core
statement is that two minimal words of the same length with the same image have the same product
in `W`. It is proved by induction on the length, following Humphreys.

If the two words end with the same letter, cancel it. Otherwise they end with letters `p ≠ q`, and
the exchange condition applied to the first word `x` and the letter `q` deletes one letter of `x`.
Unless the deleted letter is the first one, the result followed by `q` shares its first letter
with `x` and its last letter with the second word, and induction concludes. If the first letter is
deleted, `x` may be replaced by `x.tail ++ [q]`, which ends with the alternating pair `p q`;
repeating with the roles of `p` and `q` exchanged, the suffix alternating between them lengthens
until the two words are the two alternating words of their common length `m`. Their images agree,
so `(φ (s q) * φ (s p)) ^ m = 1` by `CoxeterSystem.wordProd_alternatingWord_eq_mul_pow`, and
`M q p` divides `m`, while reducedness of the alternating word
bounds `m` by `M q p`. Hence `m = M q p`, and the two words have the same product in `W` by the
braid relation.

The core statement then shows that a word reduced in `W` is minimal: at the first letter where a
prefix stops being minimal, the exchange condition would produce a shorter word with the same
product. In particular a word reduced in `W` whose image is `1` is empty, so `φ` is injective.

## Main definitions

* `CoxeterSystem.ofExchange`: the Coxeter system on a group whose generators satisfy the exchange
  condition.

## Main results

* `CoxeterSystem.length_eq_of_exchange`: a homomorphism satisfying the exchange condition
  preserves lengths.
* `CoxeterSystem.injective_of_exchange`: a homomorphism satisfying the exchange condition is
  injective.
* `CoxeterSystem.ofExchange_simple`, `CoxeterSystem.ofExchange_wordProd` and
  `CoxeterSystem.length_ofExchange`: the simple reflections, the products of words, and the length
  function of `CoxeterSystem.ofExchange`.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Chapter IV, §1, nos. 5--6.
* J. E. Humphreys, *Reflection Groups and Coxeter Groups*, Cambridge Studies in Advanced
  Mathematics 29 (1990), Section 1.9.
-/

public section

namespace CoxeterSystem

variable {B W G : Type*} [Group W] [Group G] {M : CoxeterMatrix B} (cs : CoxeterSystem M W)

local prefix:100 "s " => cs.simple
local prefix:100 "π " => cs.wordProd

section Exchange

variable {cs} (φ : W →* G) (ℓ : G → ℕ)

/-- If `φ` identifies `a` with `b * s i`, it identifies `a * s i` with `b`. -/
private theorem map_mul_simple_eq {a b : W} {i : B} (h : φ a = φ (b * s i)) :
    φ (a * s i) = φ b := by
  rw [map_mul, h, ← map_mul, simple_mul_simple_cancel_right]

/-- A word is at least as long as the length of its image. -/
private theorem length_le
    (hℓ : ∀ g, IsLeast {n | ∃ ω : List B, φ (π ω) = g ∧ ω.length = n} (ℓ g)) (ω : List B) :
    ℓ (φ (π ω)) ≤ ω.length :=
  (hℓ _).2 ⟨ω, rfl, rfl⟩

/-- A prefix of a minimal word is minimal. -/
private theorem minimal_left
    (hℓ : ∀ g, IsLeast {n | ∃ ω : List B, φ (π ω) = g ∧ ω.length = n} (ℓ g))
    {ω₁ ω₂ : List B} (h : ℓ (φ (π (ω₁ ++ ω₂))) = (ω₁ ++ ω₂).length) :
    ℓ (φ (π ω₁)) = ω₁.length := by
  obtain ⟨ω, hω, hlen⟩ := (hℓ (φ (π ω₁))).1
  have hle := length_le φ ℓ hℓ (ω ++ ω₂)
  rw [cs.wordProd_append, map_mul, hω, ← map_mul, ← cs.wordProd_append, h] at hle
  simp only [List.length_append] at hle
  exact le_antisymm (length_le φ ℓ hℓ ω₁) (by omega)

/-- A suffix of a minimal word is minimal. -/
private theorem minimal_right
    (hℓ : ∀ g, IsLeast {n | ∃ ω : List B, φ (π ω) = g ∧ ω.length = n} (ℓ g))
    {ω₁ ω₂ : List B} (h : ℓ (φ (π (ω₁ ++ ω₂))) = (ω₁ ++ ω₂).length) :
    ℓ (φ (π ω₂)) = ω₂.length := by
  obtain ⟨ω, hω, hlen⟩ := (hℓ (φ (π ω₂))).1
  have hle := length_le φ ℓ hℓ (ω₁ ++ ω)
  rw [cs.wordProd_append, map_mul, hω, ← map_mul, ← cs.wordProd_append, h] at hle
  simp only [List.length_append] at hle
  exact le_antisymm (length_le φ ℓ hℓ ω₂) (by omega)

/-- A minimal word is reduced in `W`. -/
private theorem isReduced_of_minimal
    (hℓ : ∀ g, IsLeast {n | ∃ ω : List B, φ (π ω) = g ∧ ω.length = n} (ℓ g))
    {ω : List B} (h : ℓ (φ (π ω)) = ω.length) : cs.IsReduced ω := by
  obtain ⟨ω', hω', heq⟩ := cs.exists_isReduced (π ω)
  have hle := length_le φ ℓ hℓ ω'
  rw [← heq, h] at hle
  have hge := cs.length_wordProd_le ω
  have hω'len := hω'.eq
  rw [← heq] at hω'len
  rw [IsReduced]
  omega

/-- The statement proved by induction on `r`: minimal words of length `r` with the same image have
the same product. -/
private def WordsAgree (r : ℕ) : Prop :=
  ∀ x y : List B, x.length = r → y.length = r → ℓ (φ (π x)) = r → φ (π x) = φ (π y) →
    π x = π y

/-- Cancel a common last letter. -/
private theorem wordsAgree_append_singleton
    (hℓ : ∀ g, IsLeast {n | ∃ ω : List B, φ (π ω) = g ∧ ω.length = n} (ℓ g))
    {r : ℕ} (ih : WordsAgree (cs := cs) φ ℓ r) {x y : List B} {a : B}
    (hx : x.length = r) (hy : y.length = r) (hmin : ℓ (φ (π (x ++ [a]))) = r + 1)
    (heq : φ (π (x ++ [a])) = φ (π (y ++ [a]))) :
    π (x ++ [a]) = π (y ++ [a]) := by
  have heq' : φ (π x) = φ (π y) := by
    simpa only [cs.wordProd_append, map_mul, mul_left_inj] using heq
  have hmin' : ℓ (φ (π x)) = r := by
    rw [← hx]
    exact minimal_left (ω₂ := [a]) φ ℓ hℓ
      (by rw [List.length_append, hx, List.length_singleton]; exact hmin)
  rw [cs.wordProd_append, cs.wordProd_append, ih x y hx hy hmin' heq']

/-- Cancel a common first letter. -/
private theorem wordsAgree_cons
    (hℓ : ∀ g, IsLeast {n | ∃ ω : List B, φ (π ω) = g ∧ ω.length = n} (ℓ g))
    {r : ℕ} (ih : WordsAgree (cs := cs) φ ℓ r) {x y : List B} {a : B}
    (hx : x.length = r) (hy : y.length = r) (hmin : ℓ (φ (π (a :: x))) = r + 1)
    (heq : φ (π (a :: x)) = φ (π (a :: y))) :
    π (a :: x) = π (a :: y) := by
  have heq' : φ (π x) = φ (π y) := by
    simpa only [cs.wordProd_cons, map_mul, mul_right_inj] using heq
  have hmin' : ℓ (φ (π x)) = r := by
    rw [← hx]
    exact minimal_right (ω₁ := [a]) φ ℓ hℓ
      (by rw [List.singleton_append, List.length_cons, hx]; exact hmin)
  rw [cs.wordProd_cons, cs.wordProd_cons, ih x y hx hy hmin' heq']

/-- **The exchange step.** For minimal words `x` and `y ++ [q]` of length `r + 1` with the same
image, either they have the same product, or `x.tail ++ [q]` is a word with the same image as `x`
and the same product as `y ++ [q]`. -/
private theorem exchange_step
    (hℓ : ∀ g, IsLeast {n | ∃ ω : List B, φ (π ω) = g ∧ ω.length = n} (ℓ g))
    (hexch : ∀ (ω : List B) (i : B), ℓ (φ (π ω)) = ω.length →
      ℓ (φ (π ω * s i)) ≤ ω.length → ∃ j < ω.length, φ (π (ω.eraseIdx j)) = φ (π ω * s i))
    {r : ℕ} (ih : WordsAgree (cs := cs) φ ℓ r) {x y : List B} {q : B}
    (hx : x.length = r + 1) (hy : y.length = r) (hmin : ℓ (φ (π x)) = r + 1)
    (heq : φ (π x) = φ (π (y ++ [q]))) :
    π x = π (y ++ [q]) ∨
      φ (π (x.tail ++ [q])) = φ (π x) ∧ π (x.tail ++ [q]) = π (y ++ [q]) := by
  have hdesc : φ (π x * s q) = φ (π y) :=
    map_mul_simple_eq φ (by rwa [cs.wordProd_append, cs.wordProd_singleton] at heq)
  have hle : ℓ (φ (π x * s q)) ≤ x.length := by
    rw [hdesc, hx]
    exact (hy ▸ length_le φ ℓ hℓ y).trans (Nat.le_succ r)
  obtain ⟨j, hj, hjeq⟩ := hexch x q (hmin.trans hx.symm) hle
  -- The word `x` with its `j`-th letter deleted and `q` appended has the same image as `x`.
  have hc : φ (π (x.eraseIdx j ++ [q])) = φ (π x) := by
    rw [cs.wordProd_append, cs.wordProd_singleton]
    exact map_mul_simple_eq φ hjeq
  have hlen : (x.eraseIdx j).length = r := by
    rw [List.length_eraseIdx_of_lt hj, hx, Nat.add_sub_cancel]
  -- It ends with the same letter as `y ++ [q]`, so it has the same product.
  have hcy : π (x.eraseIdx j ++ [q]) = π (y ++ [q]) :=
    wordsAgree_append_singleton φ ℓ hℓ ih hlen hy (by rw [hc, hmin]) (hc.trans heq)
  rcases j with _ | j
  · exact Or.inr ⟨by simpa using hc, by simpa using hcy⟩
  · -- Otherwise the deleted letter is not the first one, which is then shared with `x`.
    obtain ⟨a, x', rfl⟩ := List.exists_cons_of_length_eq_add_one hx
    have hx' : x'.length = r := by simpa using hx
    have hj' : j < x'.length := by simpa using hj
    have hlen' : (x'.eraseIdx j ++ [q]).length = r := by
      rw [List.length_append, List.length_eraseIdx_of_lt hj', hx', List.length_singleton]
      omega
    left
    rw [← hcy, List.eraseIdx_cons_succ, List.cons_append]
    exact wordsAgree_cons φ ℓ hℓ ih hx' hlen' hmin (by simpa using hc.symm)

/-- **The alternating case.** Two alternating words of the same positive length with the same
image, one of them minimal, have the same product: their common length is the order of the
rotation, so they are the two sides of a braid relation. -/
private theorem wordProd_alternatingWord_eq_of_minimal
    (horder : ∀ i i', orderOf (φ (s i) * φ (s i')) = M i i')
    (hℓ : ∀ g, IsLeast {n | ∃ ω : List B, φ (π ω) = g ∧ ω.length = n} (ℓ g))
    {p q : B} {m : ℕ} (hm : 0 < m)
    (hmin : ℓ (φ (π (alternatingWord q p m))) = m)
    (heq : φ (π (alternatingWord q p m)) = φ (π (alternatingWord p q m))) :
    π (alternatingWord q p m) = π (alternatingWord p q m) := by
  have hpow : (φ (s q) * φ (s p)) ^ m = 1 := by
    have h := congrArg φ (cs.wordProd_alternatingWord_eq_mul_pow q p m)
    rwa [map_mul, heq, map_pow, map_mul, left_eq_mul] at h
  have hdvd : M q p ∣ m := horder q p ▸ orderOf_dvd_of_pow_eq_one hpow
  have hM : M q p ≠ 0 := by
    rintro h
    rw [h, zero_dvd_iff] at hdvd
    omega
  have hred := isReduced_of_minimal (ω := alternatingWord q p m) φ ℓ hℓ
    (by rw [length_alternatingWord]; exact hmin)
  have hle : m ≤ M q p := by
    by_contra hlt
    exact cs.not_isReduced_alternatingWord q p hM (by omega) hred
  have hmM : m = M q p := le_antisymm hle (Nat.le_of_dvd hm hdvd)
  have h := cs.wordProd_braidWord_eq q p
  simp only [braidWord] at h
  rwa [M.symmetric p q, ← hmM] at h

/-- **The alternating induction.** A minimal word `u ++ alternatingWord q p (r + 1 - n)` with
`n = u.length` has the same product as any word `y ++ [q]` of the same length with the same
image. The induction is on `n`: the exchange step either concludes or lengthens the alternating
suffix by one letter, with the roles of `p` and `q` exchanged. -/
private theorem alternating_induction
    (horder : ∀ i i', orderOf (φ (s i) * φ (s i')) = M i i')
    (hℓ : ∀ g, IsLeast {n | ∃ ω : List B, φ (π ω) = g ∧ ω.length = n} (ℓ g))
    (hexch : ∀ (ω : List B) (i : B), ℓ (φ (π ω)) = ω.length →
      ℓ (φ (π ω * s i)) ≤ ω.length → ∃ j < ω.length, φ (π (ω.eraseIdx j)) = φ (π ω * s i))
    {r : ℕ} (ih : WordsAgree (cs := cs) φ ℓ r) :
    ∀ n ≤ r, ∀ (u : List B) (p q : B), u.length = n → ∀ y : List B, y.length = r →
      ℓ (φ (π (u ++ alternatingWord q p (r + 1 - n)))) = r + 1 →
      φ (π (u ++ alternatingWord q p (r + 1 - n))) = φ (π (y ++ [q])) →
      π (u ++ alternatingWord q p (r + 1 - n)) = π (y ++ [q]) := by
  intro n
  induction n with
  | zero =>
    intro _ u p q hu y hy hmin heq
    rw [List.length_eq_zero_iff.mp hu, List.nil_append, Nat.sub_zero] at hmin heq ⊢
    rcases exchange_step φ ℓ hℓ hexch ih (by simp) hy hmin heq with h | ⟨hφ, hπ⟩
    · exact h
    · -- The rotated word is the other alternating word of the same length.
      have hrot : (alternatingWord q p (r + 1)).tail ++ [q] = alternatingWord p q (r + 1) := by
        rw [alternatingWord_succ' q p, List.tail_cons, alternatingWord_succ,
          List.concat_eq_append]
      rw [hrot] at hφ hπ
      rw [← hπ]
      exact wordProd_alternatingWord_eq_of_minimal φ ℓ horder hℓ (Nat.succ_pos r) hmin hφ.symm
  | succ n ihn =>
    intro hn u p q hu y hy hmin heq
    obtain ⟨a, u', rfl⟩ := List.exists_cons_of_length_eq_add_one hu
    have hu' : u'.length = n := by simpa using hu
    obtain ⟨k, hk⟩ : ∃ k, r + 1 - (n + 1) = k + 1 := ⟨r - n - 1, by omega⟩
    have hkn : r + 1 - n = k + 2 := by omega
    rw [hk] at hmin heq ⊢
    have hxlen : (a :: u' ++ alternatingWord q p (k + 1)).length = r + 1 := by
      simp only [List.length_append, List.length_cons, length_alternatingWord, hu']
      omega
    rcases exchange_step φ ℓ hℓ hexch ih hxlen hy hmin heq with h | ⟨hφ, hπ⟩
    · exact h
    · -- The rotated word lengthens the alternating suffix, with `p` and `q` exchanged.
      have hrot : (a :: u' ++ alternatingWord q p (k + 1)).tail ++ [q] =
          u' ++ alternatingWord p q (r + 1 - n) := by
        rw [hkn, List.cons_append, List.tail_cons, List.append_assoc,
          alternatingWord_succ p q, List.concat_eq_append]
      -- The word itself ends with `p`.
      have hlast : a :: u' ++ alternatingWord q p (k + 1) =
          (a :: u' ++ alternatingWord p q k) ++ [p] := by
        rw [alternatingWord_succ, List.concat_eq_append, List.append_assoc]
      have hzlen : (a :: u' ++ alternatingWord p q k).length = r := by
        simp only [List.length_append, List.length_cons, length_alternatingWord, hu']
        omega
      rw [hrot] at hφ hπ
      have h := ihn (by omega) u' q p hu' _ hzlen (by rw [hφ, hmin])
        (hφ.trans (congrArg (fun z ↦ φ (π z)) hlast))
      rw [← hπ, h, ← hlast]

/-- **Minimal words of the same length with the same image have the same product.** -/
private theorem wordsAgree
    (horder : ∀ i i', orderOf (φ (s i) * φ (s i')) = M i i')
    (hℓ : ∀ g, IsLeast {n | ∃ ω : List B, φ (π ω) = g ∧ ω.length = n} (ℓ g))
    (hexch : ∀ (ω : List B) (i : B), ℓ (φ (π ω)) = ω.length →
      ℓ (φ (π ω * s i)) ≤ ω.length → ∃ j < ω.length, φ (π (ω.eraseIdx j)) = φ (π ω * s i))
    (r : ℕ) : WordsAgree (cs := cs) φ ℓ r := by
  induction r with
  | zero =>
    intro x y hx hy _ _
    rw [List.length_eq_zero_iff.mp hx, List.length_eq_zero_iff.mp hy]
  | succ r ih =>
    intro x y hx hy hmin heq
    rcases List.eq_nil_or_concat' x with rfl | ⟨x', p, rfl⟩
    · simp at hx
    rcases List.eq_nil_or_concat' y with rfl | ⟨y', q, rfl⟩
    · simp at hy
    have hx' : x'.length = r := by simpa using hx
    have hy' : y'.length = r := by simpa using hy
    by_cases hpq : p = q
    · subst hpq
      exact wordsAgree_append_singleton φ ℓ hℓ ih hx' hy' hmin heq
    · have h := alternating_induction φ ℓ horder hℓ hexch ih r le_rfl x' p q hx' y' hy'
      rw [Nat.add_sub_cancel_left] at h
      exact h hmin heq

/-- **A word reduced in `W` is minimal.** At the first letter where a prefix stops being minimal,
the exchange condition would produce a shorter word with the same product in `W`. -/
private theorem minimal_of_isReduced
    (horder : ∀ i i', orderOf (φ (s i) * φ (s i')) = M i i')
    (hℓ : ∀ g, IsLeast {n | ∃ ω : List B, φ (π ω) = g ∧ ω.length = n} (ℓ g))
    (hexch : ∀ (ω : List B) (i : B), ℓ (φ (π ω)) = ω.length →
      ℓ (φ (π ω * s i)) ≤ ω.length → ∃ j < ω.length, φ (π (ω.eraseIdx j)) = φ (π ω * s i))
    {ω : List B} (hω : cs.IsReduced ω) : ℓ (φ (π ω)) = ω.length := by
  induction ω using List.reverseRecOn with
  | nil => exact le_antisymm (length_le φ ℓ hℓ []) (Nat.zero_le _)
  | append_singleton ω i ih =>
    have hω' : cs.IsReduced ω := by
      simpa using hω.take ω.length
    have hmin := ih hω'
    refine le_antisymm (length_le φ ℓ hℓ _) (not_lt.mp fun hlt ↦ ?_)
    rw [List.length_append, List.length_singleton, Nat.lt_succ_iff, cs.wordProd_append,
      cs.wordProd_singleton] at hlt
    obtain ⟨j, hj, hjeq⟩ := hexch ω i hmin hlt
    -- The word `ω` with its `j`-th letter deleted and `i` appended has the same image as `ω`.
    have hc : φ (π (ω.eraseIdx j ++ [i])) = φ (π ω) := by
      rw [cs.wordProd_append, cs.wordProd_singleton]
      exact map_mul_simple_eq φ hjeq
    have hlen : (ω.eraseIdx j ++ [i]).length = ω.length := by
      rw [List.length_append, List.length_eraseIdx_of_lt hj, List.length_singleton]
      omega
    have hπ := wordsAgree φ ℓ horder hℓ hexch ω.length ω _ rfl hlen hmin hc.symm
    -- So `ω ++ [i]` has the same product as the shorter word `ω.eraseIdx j`.
    have hshort : π (ω ++ [i]) = π (ω.eraseIdx j) := by
      simp [cs.wordProd_append, hπ]
    have hred := hω.eq
    have hle := cs.length_wordProd_le (ω.eraseIdx j)
    rw [← hshort, hred, List.length_eraseIdx_of_lt hj, List.length_append,
      List.length_singleton] at hle
    omega

/-- **A homomorphism satisfying the exchange condition preserves lengths.** Let `φ : W →* G` be a
homomorphism out of a Coxeter group such that each `φ (s i) * φ (s i')` has order `M i i'`, let
`ℓ g` be the least length of a word whose image is `g`, and suppose that the images of the simple
reflections satisfy the exchange condition: whenever a word `ω` of least length spells `g` and
`ℓ (g * φ (s i)) ≤ ℓ g`, deleting some letter of `ω` spells `g * φ (s i)`. Then
`ℓ (φ w) = cs.length w`. -/
theorem length_eq_of_exchange
    (horder : ∀ i i', orderOf (φ (s i) * φ (s i')) = M i i')
    (hℓ : ∀ g, IsLeast {n | ∃ ω : List B, φ (π ω) = g ∧ ω.length = n} (ℓ g))
    (hexch : ∀ (ω : List B) (i : B), ℓ (φ (π ω)) = ω.length →
      ℓ (φ (π ω * s i)) ≤ ω.length → ∃ j < ω.length, φ (π (ω.eraseIdx j)) = φ (π ω * s i))
    (w : W) : ℓ (φ w) = cs.length w := by
  obtain ⟨ω, hω, rfl⟩ := cs.exists_isReduced w
  rw [minimal_of_isReduced φ ℓ horder hℓ hexch hω, hω.eq]

/-- **A homomorphism satisfying the exchange condition is injective.** This is the statement that
the braid relations are the only relations among the generators `φ (s i)`: under the hypotheses of
`CoxeterSystem.length_eq_of_exchange`, an element of `W` with trivial image has length `0`. -/
theorem injective_of_exchange
    (horder : ∀ i i', orderOf (φ (s i) * φ (s i')) = M i i')
    (hℓ : ∀ g, IsLeast {n | ∃ ω : List B, φ (π ω) = g ∧ ω.length = n} (ℓ g))
    (hexch : ∀ (ω : List B) (i : B), ℓ (φ (π ω)) = ω.length →
      ℓ (φ (π ω * s i)) ≤ ω.length → ∃ j < ω.length, φ (π (ω.eraseIdx j)) = φ (π ω * s i)) :
    Function.Injective φ := by
  refine (injective_iff_map_eq_one φ).2 fun w hw ↦ ?_
  have hlen := length_eq_of_exchange φ ℓ horder hℓ hexch w
  have hℓ1 : ℓ 1 = 0 := le_antisymm (by simpa using length_le φ ℓ hℓ []) (Nat.zero_le _)
  rw [hw, hℓ1, eq_comm, length_eq_zero_iff] at hlen
  exact hlen

/-- A homomorphism satisfying the exchange condition is surjective: every element of `G` is
spelled by a word. -/
private theorem surjective_of_exchange
    (hℓ : ∀ g, IsLeast {n | ∃ ω : List B, φ (π ω) = g ∧ ω.length = n} (ℓ g)) :
    Function.Surjective φ := fun g ↦ by
  obtain ⟨ω, hω, -⟩ := (hℓ g).1
  exact ⟨π ω, hω⟩

variable (cs) in
/-- **The Coxeter system defined by the exchange condition.** Under the hypotheses of
`CoxeterSystem.length_eq_of_exchange`, the homomorphism `φ : W →* G` is an isomorphism, and
transporting `cs` along it makes `G` a Coxeter group whose simple reflections are the images
`φ (s i)` (`CoxeterSystem.ofExchange_simple`) and whose length function is `ℓ`
(`CoxeterSystem.length_ofExchange`). -/
noncomputable def ofExchange
    (horder : ∀ i i', orderOf (φ (s i) * φ (s i')) = M i i')
    (hℓ : ∀ g, IsLeast {n | ∃ ω : List B, φ (π ω) = g ∧ ω.length = n} (ℓ g))
    (hexch : ∀ (ω : List B) (i : B), ℓ (φ (π ω)) = ω.length →
      ℓ (φ (π ω * s i)) ≤ ω.length → ∃ j < ω.length, φ (π (ω.eraseIdx j)) = φ (π ω * s i)) :
    CoxeterSystem M G :=
  cs.map (MulEquiv.ofBijective φ
    ⟨injective_of_exchange φ ℓ horder hℓ hexch, surjective_of_exchange φ ℓ hℓ⟩)

/-- The simple reflections of `CoxeterSystem.ofExchange` are the images of those of `cs`. -/
@[simp]
theorem ofExchange_simple
    (horder : ∀ i i', orderOf (φ (s i) * φ (s i')) = M i i')
    (hℓ : ∀ g, IsLeast {n | ∃ ω : List B, φ (π ω) = g ∧ ω.length = n} (ℓ g))
    (hexch : ∀ (ω : List B) (i : B), ℓ (φ (π ω)) = ω.length →
      ℓ (φ (π ω * s i)) ≤ ω.length → ∃ j < ω.length, φ (π (ω.eraseIdx j)) = φ (π ω * s i))
    (i : B) : (cs.ofExchange φ ℓ horder hℓ hexch).simple i = φ (s i) := by
  rw [ofExchange, map_simple]
  exact MulEquiv.ofBijective_apply _ _ _

/-- A word for `CoxeterSystem.ofExchange` spells the image of the word for `cs`. -/
@[simp]
theorem ofExchange_wordProd
    (horder : ∀ i i', orderOf (φ (s i) * φ (s i')) = M i i')
    (hℓ : ∀ g, IsLeast {n | ∃ ω : List B, φ (π ω) = g ∧ ω.length = n} (ℓ g))
    (hexch : ∀ (ω : List B) (i : B), ℓ (φ (π ω)) = ω.length →
      ℓ (φ (π ω * s i)) ≤ ω.length → ∃ j < ω.length, φ (π (ω.eraseIdx j)) = φ (π ω * s i))
    (ω : List B) : (cs.ofExchange φ ℓ horder hℓ hexch).wordProd ω = φ (π ω) := by
  rw [ofExchange, wordProd_map]
  exact MulEquiv.ofBijective_apply _ _ _

/-- The length function of `CoxeterSystem.ofExchange` is `ℓ`. -/
@[simp]
theorem length_ofExchange
    (horder : ∀ i i', orderOf (φ (s i) * φ (s i')) = M i i')
    (hℓ : ∀ g, IsLeast {n | ∃ ω : List B, φ (π ω) = g ∧ ω.length = n} (ℓ g))
    (hexch : ∀ (ω : List B) (i : B), ℓ (φ (π ω)) = ω.length →
      ℓ (φ (π ω * s i)) ≤ ω.length → ∃ j < ω.length, φ (π (ω.eraseIdx j)) = φ (π ω * s i))
    (g : G) : (cs.ofExchange φ ℓ horder hℓ hexch).length g = ℓ g := by
  set cs' := cs.ofExchange φ ℓ horder hℓ hexch
  have hw := ofExchange_wordProd φ ℓ horder hℓ hexch
  refine ((hℓ g).unique ⟨?_, ?_⟩).symm
  · obtain ⟨ω, hω, rfl⟩ := cs'.exists_isReduced g
    exact ⟨ω, (hw ω).symm, hω.eq.symm⟩
  · rintro n ⟨ω, rfl, rfl⟩
    rw [← hw]
    exact cs'.length_wordProd_le ω

end Exchange

end CoxeterSystem
