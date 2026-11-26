/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Ring
public import TauCeti.NumberTheory.DirichletCharacter.Even

/-!
# Orthogonality for even characters against a series

Summing the twists `∑' n, χ n * a n` of a summable series `a` over the even nontrivial Dirichlet
characters `χ` of a level `q` restricts `a` to the residue classes `n ≡ ±1 mod q`, up to the
contribution of the trivial character. This is the analytic form of the pointwise orthogonality
`DirichletCharacter.sum_even_ne_one_apply` of `TauCeti.NumberTheory.DirichletCharacter.Even`.

## Main statements

* `DirichletCharacter.sum_even_ne_one_tsum_mul`: above level two, summing the twists
  `∑' n, χ n * a n` of a summable series over the even nontrivial characters of level `q` gives
  `φ(q) / 2` times the sum of `a` over `n ≡ ±1 mod q`, minus its sum over `n` coprime to `q`.
  At a prime level `φ(q) / 2 = (q - 1) / 2`.

## References

* W. Luo, Z. Rudnick and P. Sarnak, *On Selberg's eigenvalue conjecture*, Geom. Funct. Anal. 5
  (1995), 387–401, equations (3.11) and (3.12), for the twisted sums over even nontrivial
  characters.
-/

public section

namespace DirichletCharacter

variable {R : Type*} [NormedField R] [CompleteSpace R] {q : ℕ}
  [HasEnoughRootsOfUnity R (Monoid.exponent (ZMod q)ˣ)]

open Finset

open scoped Classical in
/-- **Orthogonality for even nontrivial characters, against a series.** Above level two,
summing the twists `∑' n, χ n * a n` of a summable series over the even nontrivial characters `χ`
of level `q` gives `φ(q) / 2` times the sum of `a` over `n ≡ ±1 mod q`, minus the sum of `a` over
all `n` coprime to `q`. The first term includes the contribution of the trivial character, and
the second removes it. At a prime level `φ(q) / 2 = (q - 1) / 2`. -/
theorem sum_even_ne_one_tsum_mul (hq : 2 < q) {a : ℕ → R} (ha : Summable a) :
    ∑ χ : DirichletCharacter R q with χ.Even ∧ χ ≠ 1, ∑' n : ℕ, χ n * a n =
      ((q.totient / 2 : ℕ) : R) *
          ∑' n, {m : ℕ | (m : ZMod q) = 1 ∨ (m : ZMod q) = -1}.indicator a n -
        ∑' n, {m : ℕ | m.Coprime q}.indicator a n := by
  have : NeZero q := ⟨by omega⟩
  have : Fact (2 < q) := ⟨hq⟩
  -- Each twist is a finite combination of the restrictions of `a` to residue classes.
  have hsum (χ : DirichletCharacter R q) : Summable fun n : ℕ ↦ χ n * a n := by
    have h : (fun n : ℕ ↦ χ n * a n) =
        fun n ↦ ∑ r : ZMod q, χ r * {m : ℕ | (m : ZMod q) = r}.indicator a n := by
      ext n
      simp [Set.indicator_apply]
    rw [h]
    exact summable_sum fun r _ ↦ (ha.indicator _).mul_left _
  rw [← Summable.tsum_finsetSum fun χ _ ↦ hsum χ]
  simp_rw [← Finset.sum_mul, sum_even_ne_one, sum_even_apply hq]
  rw [← tsum_mul_left, ← Summable.tsum_sub ((ha.indicator _).mul_left _) (ha.indicator _)]
  refine tsum_congr fun n ↦ ?_
  have hne : (1 : ZMod q) ≠ -1 := ZMod.neg_one_ne_one.symm
  by_cases hu : IsUnit (n : ZMod q)
  · rw [MulChar.one_apply hu, Set.indicator_of_mem (s := {m : ℕ | m.Coprime q})
      ((ZMod.isUnit_iff_coprime n q).mp hu)]
    by_cases h1 : (n : ZMod q) = 1
    · simp [h1, hne, sub_mul]
    · by_cases h2 : (n : ZMod q) = -1
      · simp [h2, hne.symm, sub_mul]
      · simp [h1, h2]
  · have h1 : n ∉ {m : ℕ | (m : ZMod q) = 1 ∨ (m : ZMod q) = -1} := by
      rintro (h | h) <;> exact hu (h ▸ by simp)
    rw [MulChar.map_nonunit _ hu, Set.indicator_of_notMem h1, Set.indicator_of_notMem
      (s := {m : ℕ | m.Coprime q}) fun h ↦ hu ((ZMod.isUnit_iff_coprime n q).mpr h)]
    obtain ⟨hn1, hn2⟩ := not_or.mp h1
    simp [hn1, hn2]

end DirichletCharacter
