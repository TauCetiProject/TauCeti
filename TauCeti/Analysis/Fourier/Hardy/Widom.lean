/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fourier.Hardy.Compact
public import TauCeti.Analysis.InnerProductSpace.HilbertBasis.FiniteSection.Reflection

/-!
# Widom's identity for finite Toeplitz sections

Let `Pₙ` be the orthogonal projection onto the first `n + 1` Hardy basis vectors, `Wₙ` the finite
reflection reversing those coordinates, `Tₙ(a) = Pₙ T_a Pₙ` the zero-extended finite section of
the Toeplitz operator `T_a`, and `C_a` the classical Hankel operator with matrix `â(i + j + 1)`.
Widom's identity expresses the finite section of a product symbol through the product of the
finite sections and two Hankel corrections, one at each end of the finite matrix:

  `Tₙ(ab) = Tₙ(a) Tₙ(b) + Pₙ C_a C_(b(-t)) Pₙ + Wₙ C_(a(-t)) C_b Wₙ`.

The first correction is the compression of the infinite product defect `T_(ab) - T_a T_b`. The
second comes from the coordinates beyond `n`: the off-diagonal corners of `T_a` and `T_b`
factor as `Pₙ T_a (1 - Pₙ) = Wₙ C_(a(-t)) (S†)ⁿ⁺¹` and `(1 - Pₙ) T_b Pₙ = Sⁿ⁺¹ C_b Wₙ` through
powers of the forward shift `S`, and `(S†)ⁿ⁺¹ Sⁿ⁺¹ = 1`.

For a continuous right symbol both Hankel corrections are compact, so the product of two finite
Toeplitz sections has the form `Pₙ (T_(ab) + K) Pₙ + Wₙ L Wₙ` with compact `K` and `L`
independent of `n`. This is the shape of the elements of the algebra of finite sections with
continuous symbols, whose two strong limits detect the stability of the finite-section method.

## Main results

* `TauCeti.finiteProjection_comp_toeplitz_comp_id_sub_finiteProjection`,
  `TauCeti.id_sub_finiteProjection_comp_toeplitz_comp_finiteProjection`: the two off-diagonal
  corners of a Toeplitz operator relative to `Pₙ`, as reflected classical Hankel operators.
* `TauCeti.zeroExtendedFiniteSection_toeplitz_mul`: Widom's identity.
* `TauCeti.exists_isCompactOperator_zeroExtendedFiniteSection_toeplitz_comp_toLp`: products of
  finite Toeplitz sections with a continuous factor have compact boundary remainders.

## References

* H. Widom, *Asymptotic behavior of block Toeplitz matrices and determinants. II*,
  Adv. Math. **21** (1976), 1–29.
* A. Böttcher and B. Silbermann, *Introduction to Large Truncated Toeplitz Matrices*,
  for the identity in the form used here and its role in the finite-section method.
-/

public section

noncomputable section

open MeasureTheory
open scoped ENNReal InnerProductSpace

namespace TauCeti

/-- **The lower corner of a Toeplitz operator.** The block of `T_b` from the first `n + 1`
coordinates to the coordinates beyond `n` is `(1 - Pₙ) T_b Pₙ = Sⁿ⁺¹ C_b Wₙ`, where `S` is the
forward shift. Both sides have matrix entries `b̂(i - j)` for `j ≤ n < i` and vanish
elsewhere. -/
theorem id_sub_finiteProjection_comp_toeplitz_comp_finiteProjection
    (b : Lp ℂ ∞ (AddCircle.haarAddCircle (T := 1))) (n : ℕ) :
    (ContinuousLinearMap.id ℂ HardySpace - hardyBasis.finiteProjection n) ∘L toeplitz b ∘L
        hardyBasis.finiteProjection n =
      toeplitz (fourierLp (T := 1) ∞ ((n + 1 : ℕ) : ℤ)) ∘L classicalHankel b ∘L
        hardyBasis.finiteReflection n := by
  apply hardyBasis.ext_inner_apply hardyBasis
  intro i j
  simp only [ContinuousLinearMap.comp_apply]
  rw [← ContinuousLinearMap.adjoint_inner_left (toeplitz _), adjoint_toeplitz, star_fourierLp,
    toeplitz_fourierLp_neg_natCast_hardyBasis, sub_apply,
    ContinuousLinearMap.id_apply, inner_sub_right,
    ← ContinuousLinearMap.adjoint_inner_left (hardyBasis.finiteProjection n),
    HilbertBasis.adjoint_finiteProjection]
  by_cases hj : j ≤ n
  · rw [HilbertBasis.finiteReflection_basis_of_le _ _ hj]
    by_cases hi : i ≤ n
    · simp [show i < n + 1 by omega, show j < n + 1 by omega, show ¬ n + 1 ≤ i by omega]
    · simp only [HilbertBasis.finiteProjection_basis, show ¬ i < n + 1 by omega,
        show j < n + 1 by omega, ite_true, ite_false, show n + 1 ≤ i by omega, inner_zero_left,
        sub_zero, inner_hardyBasis_toeplitz_hardyBasis,
        inner_hardyBasis_classicalHankel_hardyBasis]
      congr 1
      omega
  · rw [HilbertBasis.finiteReflection_basis_eq_zero _ _ (by omega)]
    simp [show ¬ j < n + 1 by omega]

/-- **The upper corner of a Toeplitz operator.** The block of `T_a` from the coordinates beyond
`n` to the first `n + 1` coordinates is `Pₙ T_a (1 - Pₙ) = Wₙ C_(a(-t)) (S†)ⁿ⁺¹`, where `S†`
is the backward shift. Both sides have matrix entries `â(i - j)` for `i ≤ n < j` and vanish
elsewhere. -/
theorem finiteProjection_comp_toeplitz_comp_id_sub_finiteProjection
    (a : Lp ℂ ∞ (AddCircle.haarAddCircle (T := 1))) (n : ℕ) :
    hardyBasis.finiteProjection n ∘L toeplitz a ∘L
        (ContinuousLinearMap.id ℂ HardySpace - hardyBasis.finiteProjection n) =
      hardyBasis.finiteReflection n ∘L classicalHankel (Lp.compMeasurePreserving (fun t ↦ -t)
        (Measure.measurePreserving_neg AddCircle.haarAddCircle) a) ∘L
          toeplitz (fourierLp (T := 1) ∞ (-((n + 1 : ℕ) : ℤ))) := by
  simpa only [ContinuousLinearMap.adjoint_comp, LinearIsometryEquiv.map_sub,
    ContinuousLinearMap.adjoint_id,
    HilbertBasis.adjoint_finiteProjection, HilbertBasis.adjoint_finiteReflection,
    adjoint_toeplitz, adjoint_classicalHankel, star_fourierLp, star_star,
    ContinuousLinearMap.comp_assoc] using congrArg ContinuousLinearMap.adjoint
      (id_sub_finiteProjection_comp_toeplitz_comp_finiteProjection (star a) n)

/-- The ring identity behind Widom's formula: splitting `A B` through `1 = P + (1 - P)`, the
off-diagonal corners `P A (1 - P)` and `(1 - P) B P` factor through `U` and `S`, and `U S = 1`
cancels them. -/
private theorem mul_add_mul_eq_of_corner {R : Type*} [Ring R] {P A B C D W X Y U S : R}
    (hP : P * P = P) (hA : P * (A * (1 - P)) = W * (X * U))
    (hB : (1 - P) * (B * P) = S * (Y * W)) (hU : U * S = 1) :
    P * ((A * B + C * D) * P) =
      P * (A * P) * (P * (B * P)) + P * (C * (D * P)) + W * (X * (Y * W)) := by
  have hP' (Z : R) : P * (P * Z) = P * Z := by rw [← mul_assoc, hP]
  have hQ' (Z : R) : (1 - P) * ((1 - P) * Z) = (1 - P) * Z := by
    rw [← mul_assoc, (IsIdempotentElem.one_sub hP).eq]
  have hUS (Z : R) : U * (S * Z) = Z := by rw [← mul_assoc, hU, one_mul]
  have hsplit : P * (A * (B * P)) =
      P * (A * P) * (P * (B * P)) + P * (A * (1 - P)) * ((1 - P) * (B * P)) := by
    simp only [mul_assoc, hP', hQ']
    rw [← mul_add, ← mul_add, ← add_mul, add_sub_cancel, one_mul]
  rw [add_mul, mul_add, mul_assoc A, hsplit, hA, hB]
  simp only [mul_assoc, hUS]
  abel

/-- **Widom's identity.** For essentially bounded symbols `a` and `b`, the zero-extended finite
sections `Tₙ(·) = Pₙ T_(·) Pₙ` satisfy

  `Tₙ(ab) = Tₙ(a) Tₙ(b) + Pₙ C_a C_(b(-t)) Pₙ + Wₙ C_(a(-t)) C_b Wₙ`,

where `C` is the classical Hankel operator, `a(-t)` is the reflected symbol, and `Wₙ` reverses
the first `n + 1` Hardy coordinates. -/
theorem zeroExtendedFiniteSection_toeplitz_mul
    (a b : Lp ℂ ∞ (AddCircle.haarAddCircle (T := 1))) (n : ℕ) :
    (toeplitz (a * b)).zeroExtendedFiniteSection hardyBasis n =
      (toeplitz a).zeroExtendedFiniteSection hardyBasis n ∘L
          (toeplitz b).zeroExtendedFiniteSection hardyBasis n +
        hardyBasis.finiteProjection n ∘L classicalHankel a ∘L
          classicalHankel (Lp.compMeasurePreserving (fun t ↦ -t)
            (Measure.measurePreserving_neg AddCircle.haarAddCircle) b) ∘L
              hardyBasis.finiteProjection n +
        hardyBasis.finiteReflection n ∘L
          classicalHankel (Lp.compMeasurePreserving (fun t ↦ -t)
            (Measure.measurePreserving_neg AddCircle.haarAddCircle) a) ∘L
              classicalHankel b ∘L hardyBasis.finiteReflection n := by
  have hT : toeplitz (a * b) = toeplitz a ∘L toeplitz b +
      classicalHankel a ∘L classicalHankel (Lp.compMeasurePreserving (fun t ↦ -t)
        (Measure.measurePreserving_neg AddCircle.haarAddCircle) b) := by
    rw [(sub_eq_iff_eq_add (G := HardySpace →L[ℂ] HardySpace)).mp
      (toeplitz_comp_sub_toeplitz_eq_neg_classicalHankel_comp_classicalHankel a b)]
    abel
  have hA := finiteProjection_comp_toeplitz_comp_id_sub_finiteProjection a n
  have hB := id_sub_finiteProjection_comp_toeplitz_comp_finiteProjection b n
  have hU := toeplitz_fourierLp_neg_natCast_comp_natCast (n + 1)
  have hP := hardyBasis.finiteProjection_comp_self n
  rw [ContinuousLinearMap.zeroExtendedFiniteSection_eq,
    ContinuousLinearMap.zeroExtendedFiniteSection_eq,
    ContinuousLinearMap.zeroExtendedFiniteSection_eq, hT]
  simp only [← ContinuousLinearMap.one_def, ← ContinuousLinearMap.mul_def] at hA hB hU hP ⊢
  exact mul_add_mul_eq_of_corner hP hA hB hU

/-- **Products of finite Toeplitz sections.** If `g` is continuous, the product of the finite
sections of `T_a` and `T_g` differs from the finite section of `T_(ag)` by the compression of a
compact operator `K` and the reflection `Wₙ L Wₙ` of a compact operator `L`, with `K` and `L`
independent of `n`:

  `Tₙ(a) Tₙ(g) = Pₙ (T_(ag) + K) Pₙ + Wₙ L Wₙ`.

Explicitly `K = -C_a C_(g(-t))` and `L = -C_(a(-t)) C_g`, by Widom's identity
`TauCeti.zeroExtendedFiniteSection_toeplitz_mul`. -/
theorem exists_isCompactOperator_zeroExtendedFiniteSection_toeplitz_comp_toLp
    (a : Lp ℂ ∞ (AddCircle.haarAddCircle (T := 1))) (g : C(UnitAddCircle, ℂ)) :
    ∃ K L : HardySpace →L[ℂ] HardySpace, IsCompactOperator K ∧ IsCompactOperator L ∧
      ∀ n : ℕ, (toeplitz a).zeroExtendedFiniteSection hardyBasis n ∘L
          (toeplitz (ContinuousMap.toLp ∞ (AddCircle.haarAddCircle (T := 1)) ℂ g)
            ).zeroExtendedFiniteSection hardyBasis n =
        (toeplitz (a * ContinuousMap.toLp ∞ (AddCircle.haarAddCircle (T := 1)) ℂ g) +
            K).zeroExtendedFiniteSection hardyBasis n +
          hardyBasis.finiteReflection n ∘L L ∘L hardyBasis.finiteReflection n := by
  set b := ContinuousMap.toLp ∞ (AddCircle.haarAddCircle (T := 1)) ℂ g
  refine ⟨-(classicalHankel a ∘L classicalHankel (Lp.compMeasurePreserving (fun t ↦ -t)
      (Measure.measurePreserving_neg AddCircle.haarAddCircle) b)),
    -(classicalHankel (Lp.compMeasurePreserving (fun t ↦ -t)
      (Measure.measurePreserving_neg AddCircle.haarAddCircle) a) ∘L classicalHankel b), ?_, ?_,
    fun n ↦ ?_⟩
  · rw [← hardyFlip_comp_hankel]
    exact (((isCompactOperator_hankel_toLp g).clm_comp _).clm_comp _).neg
  · exact ((isCompactOperator_classicalHankel_toLp g).clm_comp _).neg
  · rw [ContinuousLinearMap.zeroExtendedFiniteSection_add, zeroExtendedFiniteSection_toeplitz_mul,
      ContinuousLinearMap.zeroExtendedFiniteSection_eq (-_)]
    simp only [ContinuousLinearMap.comp_neg, ContinuousLinearMap.neg_comp,
      ContinuousLinearMap.comp_assoc]
    abel

end TauCeti
