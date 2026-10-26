/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.LevelOne.PeriodPolynomial.Finrank
import TauCeti.LinearAlgebra.Trace.Exchange
import TauCeti.LinearAlgebra.Trace.Idempotent
import TauCeti.LinearAlgebra.Trace.Submodule

/-!
# The dimensions of the even and odd period-polynomial spaces

For positive even `w`, the even part of `W_w` has dimension one greater than the odd part.
Together with the total dimension, this identifies their dimensions with those of modular
forms and cusp forms of weight `w + 2`. These are the separate dimension counts needed to
turn the even and odd period maps into the Eichler–Shimura isomorphisms.

The calculation is algebraic. The swap `J : P(X,Y) ↦ P(Y,X)` preserves both
`A = ker(1 + S)` and `B = ker(1 + U + U²)`. Its traces on `A` and `B` vanish, while its
ambient trace is one. Inclusion-exclusion gives trace `-1` on `W_w = A ∩ B`. On `W_w`,
the swap is the negative of the parity involution, so the parity trace is one.

## Main results

* `finrank_evenPeriodPolynomials_eq_finrank_oddPeriodPolynomials_add_one`: the algebraic
  dimension difference over a characteristic-zero field, in positive even degree.
* `finrank_evenPeriodPolynomials_eq_finrank_modularForm` and
  `finrank_oddPeriodPolynomials_eq_finrank_cuspForm`: the individual dimension comparisons
  over `ℂ`, in every degree.

## References

* W. Kohnen and D. Zagier, *Modular forms with rational periods*, §1.
* A. Popa and D. Zagier, *An elementary proof of the Eichler–Selberg trace formula*,
  J. Reine Angew. Math. **762** (2020), 105–122, §2.
-/

public noncomputable section

open Matrix MvPolynomial MulOpposite ModularGroup Module Polynomial
open scoped MatrixGroups

namespace TauCeti

variable {K : Type*} [Field K] {w : ℕ}

private abbrev sAction (K : Type*) [CommRing K] (w : ℕ) :
    Module.End K (homogeneousSubmodule (Fin 2) K w) :=
  binaryFormRep K w (op (S : Matrix (Fin 2) (Fin 2) ℤ))

private abbrev uAction (K : Type*) [CommRing K] (w : ℕ) :
    Module.End K (homogeneousSubmodule (Fin 2) K w) :=
  binaryFormRep K w (op ((T * S : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ))

private abbrev swapAction (K : Type*) [CommRing K] (w : ℕ) :
    Module.End K (homogeneousSubmodule (Fin 2) K w) :=
  binaryFormRep K w (op !![0, 1; 1, 0])

private lemma swap_commute_s (hw : Even w) : Commute (sAction K w) (swapAction K w) := by
  unfold sAction swapAction Commute SemiconjBy
  simp only [← map_mul, ← op_mul]
  have h : (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℤ) * (S : Matrix (Fin 2) (Fin 2) ℤ) =
      -((S : Matrix (Fin 2) (Fin 2) ℤ) * !![0, 1; 1, 0]) := by decide
  rw [h, binaryFormRep_op_neg_of_even hw]

private lemma swap_mul_u (hw : Even w) :
    swapAction K w * uAction K w = uAction K w ^ 2 * swapAction K w := by
  unfold swapAction uAction
  simp only [← map_mul, ← map_pow, ← op_mul, ← op_pow]
  have h : ((T * S : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * !![0, 1; 1, 0] =
      -(!![0, 1; 1, 0] * (((T * S : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) ^ 2)) := by decide
  rw [h, binaryFormRep_op_neg_of_even hw]

private lemma swap_mul_u_sq (hw : Even w) :
    swapAction K w * uAction K w ^ 2 = uAction K w * swapAction K w := by
  unfold swapAction uAction
  simp only [← map_mul, ← map_pow, ← op_mul, ← op_pow]
  have h : (((T * S : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) ^ 2) * !![0, 1; 1, 0] =
      -(!![0, 1; 1, 0] * ((T * S : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) := by decide
  rw [h, binaryFormRep_op_neg_of_even hw]

private lemma swap_commute_sum_u (hw : Even w) :
    Commute (1 + uAction K w + uAction K w ^ 2) (swapAction K w) := by
  let : IsCancelAdd (Module.End K (homogeneousSubmodule (Fin 2) K w)) :=
    AddCancelMonoid.toIsCancelAdd (Module.End K (homogeneousSubmodule (Fin 2) K w))
  have h₁ := swap_mul_u (K := K) hw
  have h₂ := swap_mul_u_sq (K := K) hw
  unfold Commute SemiconjBy
  linear_combination (norm := noncomm_ring) -h₁ - h₂

private lemma swap_traces (hw : Even w) :
    LinearMap.trace K _ (swapAction K w) = 1 ∧
    LinearMap.trace K _ (sAction K w * swapAction K w) = 1 ∧
    LinearMap.trace K _ (uAction K w * swapAction K w) = 1 ∧
    LinearMap.trace K _ (uAction K w ^ 2 * swapAction K w) = 1 := by
  obtain ⟨m, hm⟩ := hw
  have hw : w = 2 * m := by omega
  dsimp [sAction, uAction, swapAction]
  simp only [← map_mul, ← map_pow, ← op_mul, ← op_pow]
  simp [trace_binaryFormRep_eq_dickson_eval, hw, Matrix.det_fin_two, Matrix.trace_fin_two, sq]

private lemma swap_preserves_ker {c : Module.End K (homogeneousSubmodule (Fin 2) K w)}
    (hc : Commute c (swapAction K w)) :
    ∀ x ∈ LinearMap.ker c, swapAction K w x ∈ LinearMap.ker c := by
  intro x hx
  rw [LinearMap.mem_ker] at hx ⊢
  rw [← Module.End.mul_apply, hc.eq, Module.End.mul_apply, hx, map_zero]

private lemma swap_preserves_a (hw : Even w) :
    ∀ x ∈ LinearMap.ker (1 + sAction K w),
      swapAction K w x ∈ LinearMap.ker (1 + sAction K w) :=
  swap_preserves_ker ((Commute.one_left _).add_left (swap_commute_s hw))

private lemma swap_preserves_b (hw : Even w) :
    ∀ x ∈ LinearMap.ker (1 + uAction K w + uAction K w ^ 2),
      swapAction K w x ∈ LinearMap.ker (1 + uAction K w + uAction K w ^ 2) :=
  swap_preserves_ker (swap_commute_sum_u hw)

variable [CharZero K]

private lemma trace_swap_a (hw : Even w) :
    LinearMap.trace K _ ((swapAction K w).restrict (swap_preserves_a hw)) = 0 := by
  let : IsCancelAdd (Module.End K (homogeneousSubmodule (Fin 2) K w)) :=
    AddCancelMonoid.toIsCancelAdd (Module.End K (homogeneousSubmodule (Fin 2) K w))
  have hs := binaryFormRep_S_sq_of_even (R := K) hw
  have hc : (1 + sAction K w) * (1 + sAction K w) =
      (2 : K) • (1 + sAction K w) := by
    rw [Algebra.smul_def, map_ofNat]
    linear_combination (norm := noncomm_ring) hs
  have h := LinearMap.trace_sub_mul_eq_mul_trace_restrict_ker hc
    ((Commute.one_left _).add_left (swap_commute_s hw)) (swap_preserves_a hw)
  have heq : ((2 : K) • 1 - (1 + sAction K w)) * swapAction K w =
      swapAction K w - sAction K w * swapAction K w := by
    ext1 x
    simp only [Module.End.mul_apply, LinearMap.sub_apply, LinearMap.smul_apply,
      LinearMap.add_apply, Module.End.one_apply]
    module
  have ht := (LinearMap.trace K (homogeneousSubmodule (Fin 2) K w)).map_sub
    (swapAction K w) (sAction K w * swapAction K w)
  rw [heq, ht, (swap_traces hw).1, (swap_traces hw).2.1] at h
  linear_combination -h / 2

private lemma trace_swap_b (hw : Even w) :
    LinearMap.trace K _ ((swapAction K w).restrict (swap_preserves_b hw)) = 0 := by
  let : IsCancelAdd (Module.End K (homogeneousSubmodule (Fin 2) K w)) :=
    AddCancelMonoid.toIsCancelAdd (Module.End K (homogeneousSubmodule (Fin 2) K w))
  have hu := binaryFormRep_U_pow_three_of_even (R := K) hw
  have hc : (1 + uAction K w + uAction K w ^ 2) * (1 + uAction K w + uAction K w ^ 2) =
      (3 : K) • (1 + uAction K w + uAction K w ^ 2) := by
    rw [Algebra.smul_def, map_ofNat]
    linear_combination (norm := noncomm_ring) 2 * hu + uAction K w * hu
  have h := LinearMap.trace_sub_mul_eq_mul_trace_restrict_ker hc
    (swap_commute_sum_u hw) (swap_preserves_b hw)
  have heq : ((3 : K) • 1 - (1 + uAction K w + uAction K w ^ 2)) * swapAction K w =
      (2 : K) • swapAction K w - uAction K w * swapAction K w -
        uAction K w ^ 2 * swapAction K w := by
    ext1 x
    simp only [Module.End.mul_apply, LinearMap.sub_apply, LinearMap.smul_apply,
      LinearMap.add_apply, Module.End.one_apply]
    module
  have ht := (LinearMap.trace K (homogeneousSubmodule (Fin 2) K w)).map_sub
    ((2 : K) • swapAction K w - uAction K w * swapAction K w)
    (uAction K w ^ 2 * swapAction K w)
  have ht' := (LinearMap.trace K (homogeneousSubmodule (Fin 2) K w)).map_sub
    ((2 : K) • swapAction K w) (uAction K w * swapAction K w)
  rw [heq, ht, ht', map_smul, (swap_traces hw).1,
    (swap_traces hw).2.2.1, (swap_traces hw).2.2.2] at h
  simp only [smul_eq_mul] at h
  linear_combination -h / 3

omit [CharZero K] in
private lemma swap_preserves_w (hw : Even w) :
    ∀ x ∈ periodPolynomials K w, swapAction K w x ∈ periodPolynomials K w := by
  intro x hx
  rw [periodPolynomials_def] at hx ⊢
  exact ⟨swap_preserves_a hw x hx.1, swap_preserves_b hw x hx.2⟩

private def swapOnPeriods (hw : Even w) : Module.End K (periodPolynomials K w) :=
  (swapAction K w).restrict (swap_preserves_w hw)

private lemma trace_swapOnPeriods (hw : Even w) (hw₀ : w ≠ 0) :
    LinearMap.trace K _ (swapOnPeriods (K := K) hw) = -1 := by
  have ht := _root_.LinearMap.trace_restrict_add_trace_restrict_eq_trace_add_trace_restrict_inf
    (codisjoint_ker_one_add_S_ker_one_add_U_add_U_sq (K := K) hw hw₀)
    (swapAction K w) (swap_preserves_a hw) (swap_preserves_b hw)
  rw [trace_swap_a hw, trace_swap_b hw, (swap_traces hw).1] at ht
  have he := _root_.LinearMap.trace_restrict_congr (periodPolynomials_def (R := K) (w := w))
    (swapAction K w) (swap_preserves_w hw)
    (fun x hx ↦ ⟨swap_preserves_a hw x hx.1, swap_preserves_b hw x hx.2⟩)
  rw [swapOnPeriods, he]
  linear_combination -ht

omit [CharZero K] in
private lemma swapOnPeriods_sq (hw : Even w) : swapOnPeriods (K := K) hw ^ 2 = 1 := by
  have hJ : swapAction K w * swapAction K w = 1 := by
    unfold swapAction
    rw [← map_mul, ← op_mul]
    have h : (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℤ) * !![0, 1; 1, 0] = 1 := by decide
    rw [h, op_one, map_one]
  ext1 P
  apply Subtype.ext
  simpa [swapOnPeriods, LinearMap.restrict, Module.End.mul_apply, pow_two] using
    congrArg (fun L : Module.End K (homogeneousSubmodule (Fin 2) K w) ↦ L P) hJ

omit [CharZero K] in
private lemma parity_eq_neg_swap (P : periodPolynomials K w) :
    binaryFormRep K w (op !![-1, 0; 0, 1]) P = -swapAction K w P := by
  have h : swapAction K w * sAction K w = binaryFormRep K w (op !![-1, 0; 0, 1]) := by
    unfold swapAction sAction
    rw [← map_mul, ← op_mul]
    congr 2
    decide
  have hS := eq_neg_of_add_eq_zero_right (mem_periodPolynomials_iff.mp P.2).1
  rw [← h, Module.End.mul_apply, hS, map_neg]

omit [CharZero K] in
private lemma finrank_ker_one_add_swapOnPeriods (hw : Even w) :
    finrank K (LinearMap.ker (1 + swapOnPeriods (K := K) hw)) =
      finrank K (evenPeriodPolynomials K w) := by
  have he : LinearMap.ker (1 + swapOnPeriods (K := K) hw) =
      (evenPeriodPolynomials K w).comap (periodPolynomials K w).subtype := by
    ext P
    rw [LinearMap.mem_ker, Submodule.mem_comap, Submodule.subtype_apply,
      mem_evenPeriodPolynomials_iff, and_iff_right P.2, parity_eq_neg_swap]
    rw [← Subtype.val_inj]
    simp only [LinearMap.add_apply, Module.End.one_apply, Submodule.coe_add,
      ZeroMemClass.coe_zero, swapOnPeriods, LinearMap.coe_restrict_apply]
    exact ⟨fun h ↦ neg_eq_iff_eq_neg.mpr (eq_neg_of_add_eq_zero_right h),
      fun h ↦ add_eq_zero_iff_eq_neg.mpr h.symm⟩
  rw [he]
  have hle : evenPeriodPolynomials K w ≤ periodPolynomials K w := by
    rw [evenPeriodPolynomials_def]
    exact inf_le_left
  exact (Submodule.comapSubtypeEquivOfLe hle).finrank_eq

private lemma finrank_even_add_finrank_odd :
    finrank K (evenPeriodPolynomials K w) + finrank K (oddPeriodPolynomials K w) =
      finrank K (periodPolynomials K w) := by
  let : Invertible (2 : K) := invertibleOfNonzero two_ne_zero
  have h := Submodule.finrank_sup_add_finrank_inf_eq
    (evenPeriodPolynomials K w) (oddPeriodPolynomials K w)
  rw [evenPeriodPolynomials_sup_oddPeriodPolynomials,
    (disjoint_evenPeriodPolynomials_oddPeriodPolynomials
      (mul_right_injective₀ (two_ne_zero : (2 : K) ≠ 0))).eq_bot, finrank_bot, add_zero] at h
  exact h.symm

/-- In positive even degree, the even period-polynomial space has dimension one greater
than the odd space, over any characteristic-zero field. -/
theorem finrank_evenPeriodPolynomials_eq_finrank_oddPeriodPolynomials_add_one
    (hw : Even w) (hw₀ : w ≠ 0) :
    finrank K (evenPeriodPolynomials K w) = finrank K (oddPeriodPolynomials K w) + 1 := by
  have h := LinearMap.two_mul_finrank_ker_one_add_of_sq_eq_one
    (K := K) (M := periodPolynomials K w) (swapOnPeriods_sq (K := K) hw)
  rw [finrank_ker_one_add_swapOnPeriods, trace_swapOnPeriods hw hw₀] at h
  have hdim : 2 * finrank K (evenPeriodPolynomials K w) =
      finrank K (periodPolynomials K w) + 1 := by
    apply Nat.cast_injective (R := K)
    push_cast
    linear_combination h
  have hsum := finrank_even_add_finrank_odd (K := K) (w := w)
  omega

private lemma parity_dimensions_complex (w : ℕ) :
    finrank ℂ (evenPeriodPolynomials ℂ w) = finrank ℂ (ModularForm 𝒮ℒ (w + 2 : ℕ)) ∧
    finrank ℂ (oddPeriodPolynomials ℂ w) = finrank ℂ (CuspForm 𝒮ℒ (w + 2 : ℕ)) := by
  have hsum := finrank_even_add_finrank_odd (K := ℂ) (w := w)
  have htotal := finrank_periodPolynomials_eq_finrank_modularForm_add_finrank_cuspForm w
  rcases Nat.even_or_odd w with hw | hw
  · rcases eq_or_ne w 0 with rfl | hw₀
    · rw [periodPolynomials_zero, finrank_bot] at hsum htotal
      omega
    · have hdiff := finrank_evenPeriodPolynomials_eq_finrank_oddPeriodPolynomials_add_one
        (K := ℂ) hw hw₀
      have : FiniteDimensional ℂ (CuspForm 𝒮ℒ (w + 2 : ℕ)) :=
        .of_injective _ CuspForm.toModularFormₗ_injective
      have hMS := ModularForm.rank_eq_one_add_rank_cuspForm (k := w + 2) (by omega)
        (hw.add even_two)
      rw [← finrank_eq_rank, ← finrank_eq_rank] at hMS
      norm_cast at hMS
      omega
  · rw [periodPolynomials_eq_bot_of_odd (mul_right_injective₀ two_ne_zero) hw, finrank_bot]
      at hsum htotal
    omega

/-- The even period polynomials of degree `w` have the dimension of the level-one
modular forms of weight `w + 2`, including degree zero and odd degrees. -/
theorem finrank_evenPeriodPolynomials_eq_finrank_modularForm (w : ℕ) :
    finrank ℂ (evenPeriodPolynomials ℂ w) = finrank ℂ (ModularForm 𝒮ℒ (w + 2 : ℕ)) :=
  (parity_dimensions_complex w).1

/-- The odd period polynomials of degree `w` have the dimension of the level-one
cusp forms of weight `w + 2`, including degree zero and odd degrees. -/
theorem finrank_oddPeriodPolynomials_eq_finrank_cuspForm (w : ℕ) :
    finrank ℂ (oddPeriodPolynomials ℂ w) = finrank ℂ (CuspForm 𝒮ℒ (w + 2 : ℕ)) :=
  (parity_dimensions_complex w).2

end TauCeti
