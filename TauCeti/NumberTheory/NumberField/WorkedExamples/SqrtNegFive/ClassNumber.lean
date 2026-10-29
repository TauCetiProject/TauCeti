/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.QuadraticAlgebra.Int
public import Mathlib.NumberTheory.NumberField.ClassNumber
public import TauCeti.NumberTheory.NumberField.Quadratic.Model
import TauCeti.Algebra.QuadraticAlgebra.Discriminant
import TauCeti.NumberTheory.Multiquadratic.MinusFive.ClassNumber
import TauCeti.NumberTheory.NumberField.ClassNumber.RingEquiv
import TauCeti.NumberTheory.NumberField.Quadratic.ClassNumber
import TauCeti.NumberTheory.NumberField.Quadratic.PrimeDecomposition
import TauCeti.NumberTheory.NumberField.WorkedExamples.SqrtNegFive.Norm

/-!
# The class group of `ℚ(√-5)` and the failure of unique factorization in `ℤ[√-5]`

This file specializes the class-number interfaces of the model `QuadraticAlgebra ℚ (-5) 0` of
`ℚ(√-5)`, whose ring of integers is `ℤ[√-5] = QuadraticAlgebra ℤ (-5) 0` since `-5 ≢ 1 (mod 4)`.

* The class number is `2`. This consumes the Minkowski computation
  `TauCeti.NumberField.classNumber_eq_two_of_minpoly_eq_X_sq_add_five`, valid for every
  presentation of `ℚ(√-5)` by an integral generator of minimal polynomial `X² + 5`: the
  discriminant is `-20`, the Minkowski bound is below `3`, and the prime above `2` is not
  principal. The generator `√-5` of the model supplies the presentation.
* The prime `𝔭 = (2, √-5 - 1)` above `2` is not principal, while `𝔭² = (2)`
  (`QuadraticAlgebra.span_two_integralSqrt_sub_one_sq_eq_span_two`). Hence its class generates the
  class group, of order two: every ideal `I` is principal, or `I 𝔭` is.
* `ℤ[√-5]` is not a unique factorization domain, by the explicit factorizations
  `2 · 3 = (1 + √-5)(1 - √-5)`: the element `2` is irreducible, since `ℤ[√-5]` has no element of
  norm `2`, but it is not prime, since it divides neither `1 + √-5` nor `1 - √-5`. Equivalently,
  the class number is not `1`.

## Main results

* `TauCeti.NumberField.SqrtNegFive.classNumber_eq_two`: the class number of `ℚ(√-5)` is `2`.
* `TauCeti.NumberField.SqrtNegFive.natCard_classGroup_eq_two`: `ℤ[√-5]` has two ideal classes.
* `TauCeti.NumberField.SqrtNegFive.not_isPrincipal_span_two_omega_sub_one`,
  `TauCeti.NumberField.SqrtNegFive.not_isPrincipal_span_two_integralSqrt_sub_one`: the prime
  above `2` is not principal, in `ℤ[√-5]` and in the ring of integers.
* `TauCeti.NumberField.SqrtNegFive.isPrincipal_or_isPrincipal_mul`: every ideal `I` of the ring
  of integers is principal or has `I 𝔭` principal.
* `TauCeti.NumberField.SqrtNegFive.irreducible_two`, `not_prime_two`, `two_mul_three_eq`: the
  non-unique factorization `2 · 3 = (1 + √-5)(1 - √-5)` in `ℤ[√-5]`.
* `TauCeti.NumberField.SqrtNegFive.not_uniqueFactorizationMonoid`,
  `not_uniqueFactorizationMonoid_ringOfIntegers`: neither `ℤ[√-5]` nor `𝓞 ℚ(√-5)` is a unique
  factorization domain.

## References

* D. A. Cox, *Primes of the Form x² + ny²*, §5.
-/

public section

open NumberField QuadraticAlgebra
open scoped NumberField nonZeroDivisors

namespace TauCeti.NumberField.SqrtNegFive

/-- The radicand `-5` is not a square, so `QuadraticAlgebra ℚ (-5) 0` is the field `ℚ(√-5)`. The
instance carries an explicit, radicand-specific name, so that it does not collide with analogous
instances for other radicands. -/
instance fact_not_isSquare_neg_five : Fact (¬ IsSquare (-5 : ℤ)) :=
  ⟨not_isSquare_of_neg (by norm_num)⟩

/-- The discriminant `-20` of `X² + 5` is not a square, so `ℤ[√-5] = QuadraticAlgebra ℤ (-5) 0`
is a domain. -/
instance fact_not_isSquare_discr_neg_five : Fact (¬ IsSquare (discr (-5 : ℤ) 0)) :=
  ⟨not_isSquare_of_neg (by norm_num [discr_def])⟩

private theorem squarefree_neg_five : Squarefree (-5 : ℤ) :=
  (Int.prime_iff_natAbs_prime.mpr (by simpa using Nat.prime_five)).squarefree

private theorem neg_five_emod_four : (-5 : ℤ) % 4 = 3 := by decide

/-! ### Class number two -/

/-- **The class number of `ℚ(√-5)` is `2`**, by the Minkowski computation for the presentation of
`ℚ(√-5)` by its generator `√-5`, of minimal polynomial `X² + 5`. -/
theorem classNumber_eq_two : classNumber (QuadraticAlgebra ℚ ((-5 : ℤ) : ℚ) 0) = 2 :=
  classNumber_eq_two_of_minpoly_eq_X_sq_add_five minpoly_integralSqrt_omega
    adjoin_integralSqrt_omega

/-- **`ℤ[√-5]` has two ideal classes**: it is the ring of integers of `ℚ(√-5)`. -/
theorem natCard_classGroup_eq_two : Nat.card (ClassGroup (QuadraticAlgebra ℤ (-5) 0)) = 2 :=
  (natCard_classGroup_eq_classNumber_of_mod_four_ne_one squarefree_neg_five (by decide)).trans
    classNumber_eq_two

/-- **The prime of `ℤ[√-5]` above `2` is not principal**: the maximal ideal `(2, √-5 - 1)` has no
single generator. -/
theorem not_isPrincipal_span_two_omega_sub_one :
    ¬ (Ideal.span {(2 : QuadraticAlgebra ℤ (-5) 0), ω - 1}).IsPrincipal := by
  -- a generator `α` has norm dividing `N(2) = 4` and `N(√-5 - 1) = 6`, hence dividing `2`
  rintro ⟨α, hα⟩
  rw [Ideal.submodule_span_eq] at hα
  have hmax : (Ideal.span {(2 : QuadraticAlgebra ℤ (-5) 0), ω - 1}).IsMaximal := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    simpa using isMaximal_span_natCast_omega_sub (p := 2) (a := -5) (b := 0) (r := 1)
      (by norm_num)
  have hdvd {x : QuadraticAlgebra ℤ (-5) 0}
      (hx : x ∈ Ideal.span {(2 : QuadraticAlgebra ℤ (-5) 0), ω - 1}) : α.norm ∣ x.norm := by
    rw [hα, Ideal.mem_span_singleton] at hx
    exact map_dvd QuadraticAlgebra.norm hx
  have h4 : (2 : QuadraticAlgebra ℤ (-5) 0).norm = 4 := by simp [norm_eq]
  have h6 : (ω - 1 : QuadraticAlgebra ℤ (-5) 0).norm = 6 := by simp [norm_eq]
  have h2 := hdvd (x := 2) (Ideal.subset_span (by simp))
  have hω := hdvd (x := ω - 1) (Ideal.subset_span (by simp))
  rw [h4] at h2
  rw [h6] at hω
  have hu : IsUnit α := isUnit_of_norm_dvd_two (by simpa using dvd_sub hω h2)
  apply hmax.ne_top
  rw [hα, Ideal.span_singleton_eq_top]
  exact hu

/-- **The prime of `𝓞 ℚ(√-5)` above `2` is not principal.** It is the image of
`(2, √-5 - 1) ⊆ ℤ[√-5]` under the identification `ℤ[√-5] ≃ 𝓞 ℚ(√-5)`. -/
theorem not_isPrincipal_span_two_integralSqrt_sub_one :
    ¬ (Ideal.span {(2 : 𝓞 (QuadraticAlgebra ℚ ((-5 : ℤ) : ℚ) 0)),
      integralSqrt (omega_sq_eq_algebraMap_int (d := -5)) - 1}).IsPrincipal := by
  intro h
  have h' := h.map_ringHom (ringOfIntegersEquiv squarefree_neg_five (by decide))
  rw [Ideal.map_span, Set.image_pair, map_ofNat, map_sub, map_one,
    ← ringOfIntegersEquiv_symm_omega squarefree_neg_five (by decide),
    AlgEquiv.apply_symm_apply] at h'
  exact not_isPrincipal_span_two_omega_sub_one h'

/-- **The class group of `ℚ(√-5)` has order two, generated by the prime above `2`.** For
`𝔭 = (2, √-5 - 1)`, every ideal `I` of `𝓞 ℚ(√-5)` is principal or has `I 𝔭` principal. Both cases
occur, since `𝔭` itself is not principal (`not_isPrincipal_span_two_integralSqrt_sub_one`) while
`𝔭² = (2)` is. -/
theorem isPrincipal_or_isPrincipal_mul (I : Ideal (𝓞 (QuadraticAlgebra ℚ ((-5 : ℤ) : ℚ) 0))) :
    I.IsPrincipal ∨ (I * Ideal.span {(2 : 𝓞 (QuadraticAlgebra ℚ ((-5 : ℤ) : ℚ) 0)),
      integralSqrt (omega_sq_eq_algebraMap_int (d := -5)) - 1}).IsPrincipal := by
  set 𝔭 := Ideal.span {(2 : 𝓞 (QuadraticAlgebra ℚ ((-5 : ℤ) : ℚ) 0)),
    integralSqrt (omega_sq_eq_algebraMap_int (d := -5)) - 1}
  rcases eq_or_ne I ⊥ with rfl | hI
  · exact .inl bot_isPrincipal
  have h𝔭sq : 𝔭 ^ 2 = Ideal.span {2} :=
    span_two_integralSqrt_sub_one_sq_eq_span_two squarefree_neg_five neg_five_emod_four
  have h𝔭 : 𝔭 ≠ ⊥ := by
    rintro h
    rw [h, sq, Ideal.bot_mul, eq_comm, Ideal.span_singleton_eq_bot] at h𝔭sq
    exact two_ne_zero h𝔭sq
  have hI0 : I ∈ (Ideal _)⁰ := mem_nonZeroDivisors_of_ne_zero hI
  have h𝔭0 : 𝔭 ∈ (Ideal _)⁰ := mem_nonZeroDivisors_of_ne_zero h𝔭
  -- the class of `𝔭` is nontrivial, and its square is trivial
  have hc𝔭 : ClassGroup.mk0 ⟨𝔭, h𝔭0⟩ ≠ 1 := fun h ↦
    not_isPrincipal_span_two_integralSqrt_sub_one ((ClassGroup.mk0_eq_one_iff h𝔭0).mp h)
  have hc𝔭sq : ClassGroup.mk0 ⟨𝔭, h𝔭0⟩ ^ 2 = 1 := by
    rw [← map_pow, ClassGroup.mk0_eq_one_iff, SubmonoidClass.mk_pow]
    simp only [h𝔭sq]
    infer_instance
  -- a group of order two consists of `1` and the class of `𝔭`
  have hclass : ∀ C : ClassGroup (𝓞 (QuadraticAlgebra ℚ ((-5 : ℤ) : ℚ) 0)),
      C = 1 ∨ C = ClassGroup.mk0 ⟨𝔭, h𝔭0⟩ := by
    obtain ⟨_, -, huniq⟩ := (Nat.card_eq_two_iff'
      (1 : ClassGroup (𝓞 (QuadraticAlgebra ℚ ((-5 : ℤ) : ℚ) 0)))).mp <| by
      rw [Nat.card_eq_fintype_card]
      exact classNumber_eq_two
    exact fun C ↦ or_iff_not_imp_left.mpr fun hC ↦ (huniq C hC).trans (huniq _ hc𝔭).symm
  rcases hclass (ClassGroup.mk0 ⟨I, hI0⟩) with h | h
  · exact .inl ((ClassGroup.mk0_eq_one_iff hI0).mp h)
  · refine .inr ((ClassGroup.mk0_eq_one_iff (mul_mem_nonZeroDivisors.mpr ⟨hI0, h𝔭0⟩)).mp ?_)
    rw [← Submonoid.mk_mul_mk _ _ _ hI0 h𝔭0, map_mul, h, ← sq, hc𝔭sq]

/-! ### Failure of unique factorization -/

/-- The two factorizations `2 · 3 = (1 + √-5)(1 - √-5)` of `6` in `ℤ[√-5]`. -/
theorem two_mul_three_eq : (2 * 3 : QuadraticAlgebra ℤ (-5) 0) = (1 + ω) * (1 - ω) := by
  ext <;> simp

/-- **`2` is irreducible in `ℤ[√-5]`.** -/
theorem irreducible_two : Irreducible (2 : QuadraticAlgebra ℤ (-5) 0) := by
  refine irreducible_iff.mpr ⟨fun h ↦ ?_, fun x y hxy ↦ ?_⟩
  · rw [isUnit_iff_norm_isUnit, Int.isUnit_iff, norm_eq] at h
    simp at h
  · -- the norms of `x` and `y` multiply to `4`, and neither is `2`
    have h4 : x.norm * y.norm = 4 := by
      rw [← map_mul, ← hxy, norm_eq]
      simp
    have hx := norm_nonneg_of_discr_nonpos (by norm_num [discr_def]) x
    have hy := norm_nonneg_of_discr_nonpos (by norm_num [discr_def]) y
    have hx2 := norm_ne_two x
    have hy2 := norm_ne_two y
    have hle : x.norm ≤ 4 := Int.le_of_dvd (by norm_num) ⟨y.norm, h4.symm⟩
    have h1 : x.norm ∣ 2 ∨ y.norm ∣ 2 := by
      interval_cases x.norm
      · omega
      · exact .inl (one_dvd _)
      · omega
      · omega
      · exact .inr ⟨2, by omega⟩
    exact h1.imp isUnit_of_norm_dvd_two isUnit_of_norm_dvd_two

/-- **`2` is not prime in `ℤ[√-5]`**: it divides `(1 + √-5)(1 - √-5) = 6`, but neither
`1 + √-5` nor `1 - √-5`. -/
theorem not_prime_two : ¬ Prime (2 : QuadraticAlgebra ℤ (-5) 0) := by
  intro h
  have hodd {z : QuadraticAlgebra ℤ (-5) 0} (hz : z.im = 1 ∨ z.im = -1) : ¬ 2 ∣ z := by
    rintro ⟨w, rfl⟩
    simp only [im_mul] at hz
    simp at hz
    omega
  rcases h.dvd_or_dvd ⟨3, two_mul_three_eq.symm⟩ with h' | h'
  · exact hodd (by simp) h'
  · exact hodd (by simp) h'

/-- **Unique factorization fails in `ℤ[√-5]`**: the irreducible element `2` is not prime. -/
theorem not_uniqueFactorizationMonoid : ¬ UniqueFactorizationMonoid (QuadraticAlgebra ℤ (-5) 0) :=
  fun _ ↦ not_prime_two (UniqueFactorizationMonoid.irreducible_iff_prime.mp irreducible_two)

/-- **Unique factorization fails in the ring of integers of `ℚ(√-5)`**: its class number is `2`,
not `1`. -/
theorem not_uniqueFactorizationMonoid_ringOfIntegers :
    ¬ UniqueFactorizationMonoid (𝓞 (QuadraticAlgebra ℚ ((-5 : ℤ) : ℚ) 0)) := by
  rw [← classNumber_eq_one_iff_uniqueFactorizationMonoid, classNumber_eq_two]
  decide

end TauCeti.NumberField.SqrtNegFive
