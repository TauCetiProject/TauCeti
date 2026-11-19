/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.RingTheory.Algebraic.Defs
public import TauCeti.Computability.AutomaticSequence.Kernel
public import TauCeti.RingTheory.PowerSeries.Cartier
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import TauCeti.RingTheory.Algebraic.LinearIndependent

/-!
# Power series with automatic coefficients are algebraic

Let `K` be a finite field with `q` elements. If the coefficient sequence of a power series
`f ∈ K⟦X⟧` is `q`-automatic, then `f` is algebraic over `K[X]`
(`PowerSeries.isAlgebraic_of_isAutomatic_coeff`); if the `q`-kernel of the coefficients has `m`
elements, `f` is a root of a nonzero polynomial over `K[X]` of degree at most `q ^ m - 1`
(`PowerSeries.exists_natDegree_le_aeval_eq_zero_of_isAutomatic_coeff`). This is the direction
"automatic implies algebraic" of Christol's theorem.

The proof works with any finite set `T` of power series containing `f` and stable under the Cartier
operators `Λ_r = PowerSeries.cartier K q r`, `r < q`
(`PowerSeries.exists_natDegree_le_aeval_eq_zero_of_finite_cartier_stable`); the generating series of
the `q`-kernel form such a set. Let `M_j` be the `K[X]`-span of the powers `h ^ q ^ j`, `h ∈ T`.
Every `h ∈ T` is `∑_{r < q} X ^ r (Λ_r h) ^ q`, and raising this to the power `q ^ j`, a ring
endomorphism of `K⟦X⟧`, shows `M_j ≤ M_{j + 1}`
(`PowerSeries.pow_card_pow_mem_span_of_cartier_stable` in `TauCeti.RingTheory.PowerSeries.Cartier`).
So the `m + 1` series `f ^ q ^ j`, `j ≤ m`, lie in `M_m`, which is spanned by `m = |T|` elements;
they are therefore linearly dependent over `K[X]`. A relation `∑_{j ≤ m} cⱼ f ^ q ^ j = 0` with
some `cⱼ ≠ 0` is `f` times the value at `f` of the nonzero polynomial
`∑_{j ≤ m} cⱼ T ^ (q ^ j - 1)`
(`TauCeti.exists_natDegree_le_aeval_eq_zero_of_sum_smul_pow_pow_eq_zero` in
`TauCeti.RingTheory.Algebraic.LinearIndependent`).

## Main results

* `PowerSeries.exists_natDegree_le_aeval_eq_zero_of_finite_cartier_stable`: a power series lying in
  a finite Cartier-stable set `T` is a root of a nonzero polynomial of degree at most
  `q ^ |T| - 1`.
* `PowerSeries.exists_natDegree_le_aeval_eq_zero_of_isAutomatic_coeff`: the same, with `|T|`
  the size of the `q`-kernel, for a power series with `q`-automatic coefficients.
* `PowerSeries.isAlgebraic_of_isAutomatic_coeff`: a power series over `K` with `q`-automatic
  coefficients is algebraic over `K[X]`.

## References

* A. Bridy, *Automatic sequences and curves over finite fields*, Algebra & Number Theory 11
  (2017), Section 2.3, Proposition 2.13 and its proof.
* G. Christol, T. Kamae, M. Mendès France, G. Rauzy, *Suites algébriques, automates et
  substitutions*, Bull. Soc. Math. France 108 (1980), Section 5, Theorem 1.
-/

public section

open Polynomial
open scoped PowerSeries

namespace PowerSeries

variable {K : Type*} [Field K] [Fintype K]

/-- Over a finite field `K` with `q` elements, let `T` be a finite set of power series that is
stable under the Cartier operators `cartier K q r` with `r < q`. Every `f ∈ T` is a root of a
nonzero polynomial over `K[X]` of degree at most `q ^ |T| - 1`. -/
theorem exists_natDegree_le_aeval_eq_zero_of_finite_cartier_stable {T : Set K⟦X⟧}
    (hT : T.Finite) {f : K⟦X⟧} (hf : f ∈ T)
    (hTq : ∀ h ∈ T, ∀ r < Fintype.card K, cartier K (Fintype.card K) r h ∈ T) :
    ∃ P : Polynomial K[X], P ≠ 0 ∧ P.natDegree ≤ Fintype.card K ^ T.ncard - 1 ∧
      Polynomial.aeval f P = 0 := by
  classical
  set q := Fintype.card K
  set m := T.ncard
  have hq : 2 ≤ q := Fintype.one_lt_card
  have hm : 0 < m := (Set.ncard_pos hT).mpr ⟨f, hf⟩
  -- The `m + 1` series `f ^ q ^ j`, `j ≤ m`, lie in `M m`, which has at most `m` generators.
  have hdep : ¬ LinearIndependent K[X] fun j : Fin (m + 1) ↦ f ^ q ^ (j : ℕ) := by
    intro hli
    have hspan : Set.range (fun j : Fin (m + 1) ↦ f ^ q ^ (j : ℕ)) ⊆
        Submodule.span K[X] (hT.toFinset.image (· ^ q ^ m) : Set K⟦X⟧) := by
      rintro _ ⟨j, rfl⟩
      rw [Finset.coe_image, Set.Finite.coe_toFinset]
      exact pow_card_pow_mem_span_of_cartier_stable hTq hf (Nat.lt_succ_iff.mp j.isLt)
    have hcard := linearIndependent_le_span' _ hli _ hspan
    rw [Cardinal.mk_fintype, Nat.cast_le] at hcard
    simp only [Fintype.card_fin, Finset.coe_sort_coe, Fintype.card_coe] at hcard
    have := (Finset.card_image_le (s := hT.toFinset) (f := (· ^ q ^ m))).trans_eq
      (Set.ncard_eq_toFinset_card T hT).symm
    omega
  obtain ⟨c, hc, i, hi⟩ := Fintype.not_linearIndependent_iff.mp hdep
  by_cases hf0 : f = 0
  · refine ⟨Polynomial.X, Polynomial.X_ne_zero, ?_, by simp [hf0]⟩
    rw [Polynomial.natDegree_X]
    have := Nat.pow_le_pow_right (by omega : 0 < q) hm
    rw [pow_one] at this
    omega
  exact TauCeti.exists_natDegree_le_aeval_eq_zero_of_sum_smul_pow_pow_eq_zero hq hi hf0 hc

/-- Over a finite field `K` with `q` elements, a power series whose coefficient sequence is
`q`-automatic is a root of a nonzero polynomial over `K[X]` of degree at most `q ^ m - 1`, where
`m` is the number of elements of the `q`-kernel of the coefficient sequence. -/
theorem exists_natDegree_le_aeval_eq_zero_of_isAutomatic_coeff {f : K⟦X⟧}
    (hf : TauCeti.IsAutomatic (Fintype.card K) fun n ↦ coeff n f) :
    ∃ P : Polynomial K[X], P ≠ 0 ∧
      P.natDegree ≤ Fintype.card K ^ (TauCeti.kernel (Fintype.card K) fun n ↦ coeff n f).ncard - 1 ∧
      Polynomial.aeval f P = 0 := by
  set q := Fintype.card K
  have hker := hf.finite_kernel
  -- The generating series of the elements of the kernel form a finite Cartier-stable set.
  obtain ⟨P, hP, hdeg, hPf⟩ := exists_natDegree_le_aeval_eq_zero_of_finite_cartier_stable
    (hker.image mk) (f := f) ⟨_, TauCeti.self_mem_kernel _ _, by ext; simp⟩ <| by
      rintro _ ⟨b, hb, rfl⟩ r hr
      refine ⟨_, TauCeti.kernel_subset hb (TauCeti.apply_mul_add_mem_kernel hr), ?_⟩
      ext n
      simp
  refine ⟨P, hP, hdeg.trans <| Nat.sub_le_sub_right ?_ 1, hPf⟩
  exact Nat.pow_le_pow_right Fintype.card_pos (Set.ncard_image_le hker)

/-- **Automatic power series are algebraic.** Over a finite field `K` with `q` elements, a power
series whose coefficient sequence is `q`-automatic is algebraic over `K[X]`. -/
theorem isAlgebraic_of_isAutomatic_coeff {f : K⟦X⟧}
    (hf : TauCeti.IsAutomatic (Fintype.card K) fun n ↦ coeff n f) : IsAlgebraic K[X] f :=
  let ⟨P, hP, _, hPf⟩ := exists_natDegree_le_aeval_eq_zero_of_isAutomatic_coeff hf
  ⟨P, hP, hPf⟩

/-- The series `∑ X ^ (2 n)` over `𝔽₂`, whose coefficients are periodic, is algebraic. -/
example : IsAlgebraic (ZMod 2)[X] (mk fun n ↦ if Even n then (1 : ZMod 2) else 0) := by
  refine isAlgebraic_of_isAutomatic_coeff ?_
  simp only [coeff_mk, ZMod.card]
  exact TauCeti.isAutomatic_of_eventually_periodic (N := 0) two_pos fun n _ ↦ by
    simp [Nat.even_add]

end PowerSeries
