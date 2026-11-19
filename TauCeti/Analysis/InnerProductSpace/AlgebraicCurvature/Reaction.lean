/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import TauCeti.Analysis.InnerProductSpace.AlgebraicCurvature.Basic

/-!
# The reaction tensor of a four-tensor

Under Ricci flow, written in a moving orthonormal frame (Uhlenbeck's trick), the curvature
four-tensor evolves by a heat equation `Dₜ Rm = Δ Rm + Q(Rm)` whose reaction term `Q` is a
quadratic expression in the curvature. In an orthonormal basis
`(eᵢ)` of a finite-dimensional real inner product space, with `rᵢⱼₖₗ = r(eᵢ, eⱼ, eₖ, eₗ)`, it reads
`Q(r)ᵢⱼₖₗ = ∑ₚ,q rᵢⱼₚq rₖₗₚq + 2 ∑ₚ,q rᵢₚₖq rⱼₚₗq - 2 ∑ₚ,q rᵢₚₗq rⱼₚₖq`.
This file defines `TauCeti.FourTensor.reactionTensor r` by this formula in the standard
orthonormal basis and proves that the same contraction computes it in every orthonormal basis,
so it is an invariant of the inner product space.

The main result is that `Q` maps algebraic curvature tensors to algebraic curvature tensors. The
pair symmetries and the first Bianchi identity of `Q(r)` are not visible term by term: neither
the first sum nor the last two sums alone satisfy the Bianchi identity. The proof rewrites the
first sum, using the Bianchi identity of `r`, through the single contraction
`C(a, b, c, d) = ∑ₚ,q r(a, eₚ, b, e_q) r(c, eₚ, d, e_q)`, after which
`Q(r)(u, v, z, w) = 2 (C(u, v, z, w) - C(v, u, z, w) + C(u, z, v, w) - C(u, w, v, z))`, and every
identity follows from the two symmetries `C(a, b, c, d) = C(c, d, a, b) = C(b, a, d, c)`.

The reaction tensor is equivariant under linear isometric equivalences and homogeneous of degree
two. It is the diagonal `Q(r) = B(r, r)` of a bilinear map of the finite-dimensional space of
four-tensors, hence smooth and locally Lipschitz, as the reaction ODE `dR/dt = Q(R)` requires.
On the constant-curvature tensor `r₁` of the unit sphere it is `Q(r₁) = 2 (n - 1) r₁` in
dimension `n`, which is the reaction term of the round sphere's curvature under Ricci flow.

## Main definitions

* `TauCeti.FourTensor.reactionTensor`: the reaction tensor `Q(r)` of a four-tensor `r`.
* `TauCeti.FourTensor.reactionBilin`: its polarization, the continuous bilinear map `B` of
  four-tensors with `Q(r) = B(r, r)`.

## Main statements

* `TauCeti.FourTensor.reactionTensor_apply_orthonormalBasis`: the defining contraction holds in
  every orthonormal basis.
* `TauCeti.FourTensor.reactionTensor_eq_reactionBilin` and
  `TauCeti.FourTensor.reactionBilin_apply_orthonormalBasis`: `Q(r) = B(r, r)`, and `B` is the
  polarized contraction in every orthonormal basis.
* `TauCeti.FourTensor.reactionTensor_mem`: `Q` preserves `algebraicCurvatureSubmodule`.
* `TauCeti.FourTensor.reactionTensor_compContinuousLinearMap_linearIsometryEquiv`: `Q` is
  equivariant under linear isometric equivalences.
* `TauCeti.FourTensor.reactionTensor_smul`: `Q(c • r) = c ^ 2 • Q(r)`, with
  `TauCeti.FourTensor.reactionTensor_zero` and `TauCeti.FourTensor.reactionTensor_neg`.
* `TauCeti.FourTensor.contDiff_reactionTensor` and
  `TauCeti.FourTensor.locallyLipschitz_reactionTensor`: `Q` is smooth and locally Lipschitz.
* `TauCeti.FourTensor.reactionTensor_constantCurvature`: `Q(r₁) = 2 (n - 1) r₁`.

## References

* S. Brendle and R. Schoen, *Manifolds with 1/4-pinched curvature are space forms*,
  J. Amer. Math. Soc. 22 (2009), Section 2.
* R. S. Hamilton, *Four-manifolds with positive curvature operator*, J. Differential Geom. 24
  (1986).
-/

public section

open LinearMap (BilinForm)
open scoped InnerProductSpace

noncomputable section

namespace TauCeti

namespace FourTensor

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

section Sum

variable {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ V)

/-- The polarized reaction contraction of `r` and `s` at `(u, v, z, w)` in an orthonormal basis
`b`; the reaction contraction of `r` is the case `s = r`. -/
private def reactionSum (r s : FourTensor V) (u v z w : V) : ℝ :=
  (∑ p, ∑ q, r ![u, v, b p, b q] * s ![z, w, b p, b q]) +
    2 * (∑ p, ∑ q, r ![u, b p, z, b q] * s ![v, b p, w, b q]) -
    2 * (∑ p, ∑ q, r ![u, b p, w, b q] * s ![v, b p, z, b q])

section Linearity

variable (r s : FourTensor V) (u v z w x y : V) (t : ℝ)

private theorem reactionSum_add_first :
    reactionSum b r s (x + y) v z w = reactionSum b r s x v z w + reactionSum b r s y v z w := by
  simp only [reactionSum, apply_add_first, add_mul, Finset.sum_add_distrib]
  ring

private theorem reactionSum_add_second :
    reactionSum b r s u (x + y) z w = reactionSum b r s u x z w + reactionSum b r s u y z w := by
  simp only [reactionSum, apply_add_first, apply_add_second, add_mul, mul_add,
    Finset.sum_add_distrib]
  ring

private theorem reactionSum_add_third :
    reactionSum b r s u v (x + y) w = reactionSum b r s u v x w + reactionSum b r s u v y w := by
  simp only [reactionSum, apply_add_first, apply_add_third, add_mul, mul_add,
    Finset.sum_add_distrib]
  ring

private theorem reactionSum_add_fourth :
    reactionSum b r s u v z (x + y) = reactionSum b r s u v z x + reactionSum b r s u v z y := by
  simp only [reactionSum, apply_add_second, apply_add_third, add_mul, mul_add,
    Finset.sum_add_distrib]
  ring

private theorem reactionSum_smul_first :
    reactionSum b r s (t • x) v z w = t * reactionSum b r s x v z w := by
  simp only [reactionSum, apply_smul_first, mul_assoc, ← Finset.mul_sum]
  ring

private theorem reactionSum_smul_second :
    reactionSum b r s u (t • x) z w = t * reactionSum b r s u x z w := by
  simp only [reactionSum, apply_smul_first, apply_smul_second, mul_assoc, mul_left_comm _ t,
    ← Finset.mul_sum]
  ring

private theorem reactionSum_smul_third :
    reactionSum b r s u v (t • x) w = t * reactionSum b r s u v x w := by
  simp only [reactionSum, apply_smul_first, apply_smul_third, mul_assoc, mul_left_comm _ t,
    ← Finset.mul_sum]
  ring

private theorem reactionSum_smul_fourth :
    reactionSum b r s u v z (t • x) = t * reactionSum b r s u v z x := by
  simp only [reactionSum, apply_smul_second, apply_smul_third, mul_assoc, mul_left_comm _ t,
    ← Finset.mul_sum]
  ring


private theorem reactionSum_add_left (r' : FourTensor V) :
    reactionSum b (r + r') s u v z w = reactionSum b r s u v z w + reactionSum b r' s u v z w := by
  simp only [reactionSum, add_apply, add_mul, Finset.sum_add_distrib]
  ring

private theorem reactionSum_add_right (s' : FourTensor V) :
    reactionSum b r (s + s') u v z w = reactionSum b r s u v z w + reactionSum b r s' u v z w := by
  simp only [reactionSum, add_apply, mul_add, Finset.sum_add_distrib]
  ring

private theorem reactionSum_smul_left :
    reactionSum b (t • r) s u v z w = t * reactionSum b r s u v z w := by
  simp only [reactionSum, smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum]
  ring

private theorem reactionSum_smul_right :
    reactionSum b r (t • s) u v z w = t * reactionSum b r s u v z w := by
  simp only [reactionSum, smul_apply, smul_eq_mul, mul_left_comm _ t, ← Finset.mul_sum]
  ring

end Linearity

section Bianchi

variable {r : FourTensor V}

/-- The first Bianchi identity solved for its first term:
`r(a, c, d, e) = r(a, d, c, e) - r(c, d, a, e)`. -/
private theorem IsAlgebraicCurvature.apply_eq_sub (hr : IsAlgebraicCurvature r) (a c d e : V) :
    r ![a, c, d, e] = r ![a, d, c, e] - r ![c, d, a, e] := by
  linear_combination hr.cyclic_eq_zero a c d e - hr.antisymm_first d a c e

/-- The contraction `C(a, c, d, e) = ∑ₚ,q r(a, eₚ, c, e_q) r(d, eₚ, e, e_q)`, through which the
reaction contraction of an algebraic curvature tensor is written. -/
private def crossSum (r : FourTensor V) (a c d e : V) : ℝ :=
  ∑ p, ∑ q, r ![a, b p, c, b q] * r ![d, b p, e, b q]

private theorem crossSum_swap_pairs (r : FourTensor V) (a c d e : V) :
    crossSum b r a c d e = crossSum b r d e a c := by
  simp only [crossSum, mul_comm (r ![a, _, c, _])]

private theorem crossSum_swap_entries (hr : IsAlgebraicCurvature r) (a c d e : V) :
    crossSum b r a c d e = crossSum b r c a e d := by
  rw [crossSum, crossSum, Finset.sum_comm]
  simp only [hr.swap_pairs c, hr.swap_pairs e]

/-- Using the Bianchi identity twice, the first sum of the reaction contraction is
`2 (C(u, v, z, w) - C(v, u, z, w))`. -/
private theorem sum_sum_apply_mul_apply_eq_crossSum (hr : IsAlgebraicCurvature r) (u v z w : V) :
    ∑ p, ∑ q, r ![u, v, b p, b q] * r ![z, w, b p, b q] =
      2 * (crossSum b r u v z w - crossSum b r v u z w) := by
  have hz : ∑ p, ∑ q, r ![u, v, b p, b q] * r ![w, b p, z, b q] =
      -∑ p, ∑ q, r ![u, v, b p, b q] * r ![z, b p, w, b q] := by
    rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun p _ ↦ ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun q _ ↦ ?_
    rw [hr.antisymm_last u v, hr.swap_pairs w]
    ring
  calc ∑ p, ∑ q, r ![u, v, b p, b q] * r ![z, w, b p, b q]
      = ∑ p, ∑ q, r ![u, v, b p, b q] * r ![z, b p, w, b q] -
          ∑ p, ∑ q, r ![u, v, b p, b q] * r ![w, b p, z, b q] := by
        simp only [hr.apply_eq_sub z w, mul_sub, Finset.sum_sub_distrib]
    _ = 2 * ∑ p, ∑ q, r ![u, v, b p, b q] * r ![z, b p, w, b q] := by rw [hz]; ring
    _ = 2 * (crossSum b r u v z w - crossSum b r v u z w) := by
        simp only [hr.apply_eq_sub u v, sub_mul, Finset.sum_sub_distrib, crossSum]

/-- The reaction contraction of an algebraic curvature tensor through `C`:
`Q(r)(u, v, z, w) = 2 (C(u, v, z, w) - C(v, u, z, w) + C(u, z, v, w) - C(u, w, v, z))`. -/
private theorem reactionSum_eq_crossSum (hr : IsAlgebraicCurvature r) (u v z w : V) :
    reactionSum b r r u v z w =
      2 * (crossSum b r u v z w - crossSum b r v u z w + crossSum b r u z v w -
        crossSum b r u w v z) := by
  rw [reactionSum, sum_sum_apply_mul_apply_eq_crossSum b hr]
  simp only [crossSum]
  ring

/-- The reaction contraction of an algebraic curvature tensor has the four symmetries of an
algebraic curvature tensor. -/
private theorem isAlgebraicCurvature_reactionSum (hr : IsAlgebraicCurvature r) :
    (∀ u v z w, reactionSum b r r u v z w = -reactionSum b r r v u z w) ∧
    (∀ u v z w, reactionSum b r r u v z w = -reactionSum b r r u v w z) ∧
    (∀ u v z w, reactionSum b r r u v z w = reactionSum b r r z w u v) ∧
    (∀ u v z w,
      reactionSum b r r u v z w + reactionSum b r r v z u w + reactionSum b r r z u v w = 0) := by
  have hC := crossSum_swap_pairs b r
  have hC' := crossSum_swap_entries b hr
  refine ⟨fun u v z w ↦ ?_, fun u v z w ↦ ?_, fun u v z w ↦ ?_, fun u v z w ↦ ?_⟩ <;>
    simp only [reactionSum_eq_crossSum b hr]
  · linear_combination 2 * hC u z v w + 2 * hC v z u w
  · linear_combination 2 * hC' u v z w + 2 * hC' u v w z
  · linear_combination 2 * hC u v z w + 2 * hC' u v w z + 2 * hC w z u v + 2 * hC' u z v w +
      2 * hC z v w u + 2 * hC' w u z v
  · linear_combination 2 * hC u v z w + 2 * hC v z u w + 2 * hC z u v w

end Bianchi

section ConstantCurvature

/-- The contraction `C` of the constant-curvature tensor:
`C(a, c, d, e) = (n - 2) ⟪a, c⟫ ⟪d, e⟫ + ⟪a, d⟫ ⟪c, e⟫`. -/
private theorem crossSum_constantCurvature [FiniteDimensional ℝ V] (a c d e : V) :
    crossSum b (constantCurvature V) a c d e =
      ((Fintype.card ι : ℝ) - 2) * ⟪a, c⟫_ℝ * ⟪d, e⟫_ℝ + ⟪a, d⟫_ℝ * ⟪c, e⟫_ℝ := by
  have hq (p : ι) : ∑ q, constantCurvature V ![a, b p, c, b q] *
      constantCurvature V ![d, b p, e, b q] =
        ⟪a, c⟫_ℝ * ⟪d, e⟫_ℝ - ⟪a, c⟫_ℝ * (⟪d, b p⟫_ℝ * ⟪b p, e⟫_ℝ) -
          ⟪d, e⟫_ℝ * (⟪a, b p⟫_ℝ * ⟪b p, c⟫_ℝ) + ⟪a, d⟫_ℝ * (⟪c, b p⟫_ℝ * ⟪b p, e⟫_ℝ) := by
    have h₁ : ⟪b p, b p⟫_ℝ = 1 := by
      rw [real_inner_self_eq_norm_sq, b.orthonormal.1 p, one_pow]
    calc ∑ q, constantCurvature V ![a, b p, c, b q] * constantCurvature V ![d, b p, e, b q]
        = ∑ q, (⟪a, c⟫_ℝ * ⟪d, e⟫_ℝ * (⟪b p, b q⟫_ℝ * ⟪b q, b p⟫_ℝ) -
            ⟪a, c⟫_ℝ * ⟪b p, e⟫_ℝ * (⟪d, b q⟫_ℝ * ⟪b q, b p⟫_ℝ) -
            ⟪d, e⟫_ℝ * ⟪b p, c⟫_ℝ * (⟪a, b q⟫_ℝ * ⟪b q, b p⟫_ℝ) +
            ⟪b p, c⟫_ℝ * ⟪b p, e⟫_ℝ * (⟪a, b q⟫_ℝ * ⟪b q, d⟫_ℝ)) :=
          Finset.sum_congr rfl fun q _ ↦ by
            simp only [constantCurvature_apply, real_inner_comm (b q)]
            ring
      _ = _ := by
          simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
            b.sum_inner_mul_inner, h₁, real_inner_comm c (b p)]
          ring
  rw [crossSum, Finset.sum_congr rfl fun p _ ↦ hq p]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    b.sum_inner_mul_inner, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  ring

end ConstantCurvature

end Sum

variable [FiniteDimensional ℝ V]

section BasisIndependence

/-- The bilinear form `(x, y) ↦ r(u, v, x, y)`. -/
private def sliceLast (r : FourTensor V) (u v : V) : BilinForm ℝ V :=
  LinearMap.mk₂ ℝ (fun x y ↦ r ![u, v, x, y])
    (fun _ _ _ ↦ apply_add_third ..) (fun _ _ _ ↦ apply_smul_third ..)
    (fun _ _ _ ↦ apply_add_fourth ..) (fun _ _ _ ↦ apply_smul_fourth ..)

/-- The bilinear form `(x, y) ↦ r(u, x, z, y)`. -/
private def sliceAlternate (r : FourTensor V) (u z : V) : BilinForm ℝ V :=
  LinearMap.mk₂ ℝ (fun x y ↦ r ![u, x, z, y])
    (fun _ _ _ ↦ apply_add_second ..) (fun _ _ _ ↦ apply_smul_second ..)
    (fun _ _ _ ↦ apply_add_fourth ..) (fun _ _ _ ↦ apply_smul_fourth ..)

/-- The polarized reaction contraction does not depend on the orthonormal basis. -/
private theorem reactionSum_eq {ι κ : Type*} [Fintype ι] [Fintype κ]
    (b : OrthonormalBasis ι ℝ V) (b' : OrthonormalBasis κ ℝ V) (r s : FourTensor V)
    (u v z w : V) : reactionSum b r s u v z w = reactionSum b' r s u v z w := by
  have h₁ := b.sum_sum_apply_mul_apply_eq b' (sliceLast r u v) (sliceLast s z w)
  have h₂ := b.sum_sum_apply_mul_apply_eq b' (sliceAlternate r u z) (sliceAlternate s v w)
  have h₃ := b.sum_sum_apply_mul_apply_eq b' (sliceAlternate r u w) (sliceAlternate s v z)
  simp only [sliceLast, sliceAlternate, LinearMap.mk₂_apply] at h₁ h₂ h₃
  rw [reactionSum, reactionSum, h₁, h₂, h₃]

end BasisIndependence

section Polarization

/-- The polarized reaction tensor of `r` and `s`, the four-tensor of the polarized reaction
contraction in the standard orthonormal basis. -/
private def reactionPair (r s : FourTensor V) : FourTensor V :=
  let f : MultilinearMap (RingHom.id ℝ) (fun _ : Fin 4 ↦ V) ℝ :=
    MultilinearMap.mk'
      (fun m ↦ reactionSum (stdOrthonormalBasis ℝ V) r s (m 0) (m 1) (m 2) (m 3))
      (fun m i x y ↦ by
        fin_cases i <;>
          simp [reactionSum_add_first, reactionSum_add_second, reactionSum_add_third,
            reactionSum_add_fourth])
      (fun m i c x ↦ by
        fin_cases i <;>
          simp [reactionSum_smul_first, reactionSum_smul_second, reactionSum_smul_third,
            reactionSum_smul_fourth])
  { f with cont := f.continuous_of_finiteDimensional }

private theorem reactionPair_apply {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ V)
    (r s : FourTensor V) (u v z w : V) :
    reactionPair r s ![u, v, z, w] = reactionSum b r s u v z w :=
  reactionSum_eq (stdOrthonormalBasis ℝ V) b r s u v z w

/-- The polarized reaction tensor as a bilinear map. -/
private def reactionBilinₗ : FourTensor V →ₗ[ℝ] FourTensor V →ₗ[ℝ] FourTensor V :=
  LinearMap.mk₂ ℝ reactionPair
    (fun r r' s ↦ by ext m; exact reactionSum_add_left _ r s _ _ _ _ r')
    (fun t r s ↦ by ext m; exact reactionSum_smul_left _ r s _ _ _ _ t)
    (fun r s s' ↦ by ext m; exact reactionSum_add_right _ r s _ _ _ _ s')
    (fun t r s ↦ by ext m; exact reactionSum_smul_right _ r s _ _ _ _ t)

variable (V) in
/-- The polarization of the reaction tensor: the continuous bilinear map `B` of four-tensors with
`B(r, r) = Q(r)`. In an orthonormal basis `(eᵢ)`,
`B(r, s)ᵢⱼₖₗ = ∑ₚ,q rᵢⱼₚq sₖₗₚq + 2 ∑ₚ,q rᵢₚₖq sⱼₚₗq - 2 ∑ₚ,q rᵢₚₗq sⱼₚₖq`; see
`TauCeti.FourTensor.reactionBilin_apply_orthonormalBasis`. -/
def reactionBilin : FourTensor V →L[ℝ] FourTensor V →L[ℝ] FourTensor V :=
  LinearMap.toContinuousLinearMap (𝕜 := ℝ) (E := FourTensor V)
      (F' := FourTensor V →L[ℝ] FourTensor V)
    ((LinearMap.toContinuousLinearMap (𝕜 := ℝ) (E := FourTensor V)
      (F' := FourTensor V)).toLinearMap ∘ₗ reactionBilinₗ)

private theorem reactionBilin_apply (r s : FourTensor V) :
    reactionBilin V r s = reactionPair r s := by
  simp only [reactionBilin, reactionBilinₗ, LinearMap.coe_toContinuousLinearMap',
    LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, LinearMap.mk₂_apply]

/-- In every orthonormal basis `(eᵢ)` the polarization of the reaction tensor is the contraction
`B(r, s)(u, v, z, w) = ∑ₚ,q r(u, v, eₚ, e_q) s(z, w, eₚ, e_q)
  + 2 ∑ₚ,q r(u, eₚ, z, e_q) s(v, eₚ, w, e_q) - 2 ∑ₚ,q r(u, eₚ, w, e_q) s(v, eₚ, z, e_q)`. -/
theorem reactionBilin_apply_orthonormalBasis {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ V) (r s : FourTensor V) (u v z w : V) :
    reactionBilin V r s ![u, v, z, w] =
      (∑ p, ∑ q, r ![u, v, b p, b q] * s ![z, w, b p, b q]) +
        2 * (∑ p, ∑ q, r ![u, b p, z, b q] * s ![v, b p, w, b q]) -
        2 * (∑ p, ∑ q, r ![u, b p, w, b q] * s ![v, b p, z, b q]) := by
  rw [reactionBilin_apply]
  exact reactionPair_apply b r s u v z w

end Polarization

/-- The reaction tensor `Q(r)` of a four-tensor `r` on a finite-dimensional real inner product
space: in an orthonormal basis `(eᵢ)`, with `rᵢⱼₖₗ = r(eᵢ, eⱼ, eₖ, eₗ)`,
`Q(r)ᵢⱼₖₗ = ∑ₚ,q rᵢⱼₚq rₖₗₚq + 2 ∑ₚ,q rᵢₚₖq rⱼₚₗq - 2 ∑ₚ,q rᵢₚₗq rⱼₚₖq`.
It is the reaction term of the evolution `Dₜ Rm = Δ Rm + Q(Rm)` of the curvature four-tensor under
Ricci flow in a moving orthonormal frame. It is defined in the standard orthonormal basis; by
`TauCeti.FourTensor.reactionTensor_apply_orthonormalBasis` every orthonormal basis gives the same
tensor. -/
def reactionTensor (r : FourTensor V) : FourTensor V :=
  reactionPair r r

/-- The reaction tensor is the diagonal of its polarization: `Q(r) = B(r, r)`. -/
theorem reactionTensor_eq_reactionBilin (r : FourTensor V) :
    reactionTensor r = reactionBilin V r r := by
  rw [reactionTensor, reactionBilin_apply]

private theorem reactionTensor_apply_eq_reactionSum {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ V) (r : FourTensor V) (u v z w : V) :
    reactionTensor r ![u, v, z, w] = reactionSum b r r u v z w :=
  reactionPair_apply b r r u v z w

/-- In every orthonormal basis `(eᵢ)` the reaction tensor is the contraction
`Q(r)(u, v, z, w) = ∑ₚ,q r(u, v, eₚ, e_q) r(z, w, eₚ, e_q)
  + 2 ∑ₚ,q r(u, eₚ, z, e_q) r(v, eₚ, w, e_q) - 2 ∑ₚ,q r(u, eₚ, w, e_q) r(v, eₚ, z, e_q)`. -/
theorem reactionTensor_apply_orthonormalBasis {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ V) (r : FourTensor V) (u v z w : V) :
    reactionTensor r ![u, v, z, w] =
      (∑ p, ∑ q, r ![u, v, b p, b q] * r ![z, w, b p, b q]) +
        2 * (∑ p, ∑ q, r ![u, b p, z, b q] * r ![v, b p, w, b q]) -
        2 * (∑ p, ∑ q, r ![u, b p, w, b q] * r ![v, b p, z, b q]) :=
  reactionTensor_apply_eq_reactionSum b r u v z w

/-- The reaction tensor is a smooth map of four-tensors: it is the diagonal of a bilinear map
of the finite-dimensional space of four-tensors. -/
theorem contDiff_reactionTensor {n : WithTop ℕ∞} :
    ContDiff ℝ n (reactionTensor : FourTensor V → FourTensor V) := by
  simp only [funext reactionTensor_eq_reactionBilin]
  exact (reactionBilin V).contDiff.clm_apply contDiff_id

/-- The reaction tensor is locally Lipschitz, the regularity under which the reaction ODE
`dR/dt = Q(R)` is uniquely solvable. -/
theorem locallyLipschitz_reactionTensor :
    LocallyLipschitz (reactionTensor : FourTensor V → FourTensor V) :=
  contDiff_reactionTensor.locallyLipschitz

/-- The reaction tensor of an algebraic curvature tensor is an algebraic curvature tensor. -/
theorem IsAlgebraicCurvature.reactionTensor {r : FourTensor V} (hr : IsAlgebraicCurvature r) :
    IsAlgebraicCurvature (reactionTensor r) := by
  obtain ⟨h₁, h₂, h₃, h₄⟩ := isAlgebraicCurvature_reactionSum (stdOrthonormalBasis ℝ V) hr
  simp only [← reactionTensor_apply_eq_reactionSum] at h₁ h₂ h₃ h₄
  exact ⟨h₁, h₂, h₃, h₄⟩

/-- The reaction tensor maps the submodule of algebraic curvature tensors to itself. -/
theorem reactionTensor_mem {r : FourTensor V} (hr : r ∈ algebraicCurvatureSubmodule V) :
    reactionTensor r ∈ algebraicCurvatureSubmodule V :=
  mem_algebraicCurvatureSubmodule.2 (mem_algebraicCurvatureSubmodule.1 hr).reactionTensor

/-- The reaction tensor is equivariant under linear isometric equivalences: the reaction tensor
of the pullback of `r` by `e` is the pullback of the reaction tensor of `r`. -/
theorem reactionTensor_compContinuousLinearMap_linearIsometryEquiv {W : Type*}
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W] (e : W ≃ₗᵢ[ℝ] V)
    (r : FourTensor V) :
    reactionTensor (r.compContinuousLinearMap fun _ ↦ e.toLinearIsometry.toContinuousLinearMap) =
      (reactionTensor r).compContinuousLinearMap
        fun _ ↦ e.toLinearIsometry.toContinuousLinearMap := by
  refine ext_vec fun u v z w ↦ ?_
  let b := stdOrthonormalBasis ℝ W
  rw [compContinuousLinearMap_apply_vec, reactionTensor_apply_eq_reactionSum b,
    reactionTensor_apply_eq_reactionSum (b.map e)]
  simp only [reactionSum, compContinuousLinearMap_apply_vec, OrthonormalBasis.map_apply,
    LinearIsometry.coe_toContinuousLinearMap, LinearIsometryEquiv.coe_toLinearIsometry]

/-- The reaction tensor is homogeneous of degree two: `Q(c • r) = c ^ 2 • Q(r)`. -/
@[simp]
theorem reactionTensor_smul (c : ℝ) (r : FourTensor V) :
    reactionTensor (c • r) = c ^ 2 • reactionTensor r := by
  rw [reactionTensor_eq_reactionBilin, reactionTensor_eq_reactionBilin, map_smul,
    map_smul, smul_apply, smul_smul, sq]

/-- The reaction tensor vanishes at zero. -/
@[simp]
theorem reactionTensor_zero : reactionTensor (0 : FourTensor V) = 0 := by
  simpa using reactionTensor_smul 0 (0 : FourTensor V)

/-- The reaction tensor is even: `Q(-r) = Q(r)`. -/
@[simp]
theorem reactionTensor_neg (r : FourTensor V) : reactionTensor (-r) = reactionTensor r := by
  rw [← neg_one_smul ℝ r, reactionTensor_smul, neg_one_sq, one_smul]

/-- The reaction tensor of the constant-curvature tensor `r₁` of the unit sphere is
`Q(r₁) = 2 (n - 1) r₁` in dimension `n`. -/
@[simp]
theorem reactionTensor_constantCurvature :
    reactionTensor (constantCurvature V) =
      (2 * ((Module.finrank ℝ V : ℝ) - 1)) • constantCurvature V := by
  refine ext_vec fun u v z w ↦ ?_
  let b := stdOrthonormalBasis ℝ V
  rw [smul_apply, reactionTensor_apply_eq_reactionSum b,
    reactionSum_eq_crossSum b isAlgebraicCurvature_constantCurvature]
  simp only [crossSum_constantCurvature b, Fintype.card_fin, constantCurvature_apply, smul_eq_mul,
    real_inner_comm u v, real_inner_comm z w]
  ring

end FourTensor

end TauCeti
