/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import TauCeti.Analysis.InnerProductSpace.AlgebraicCurvature.ExteriorSquare
public import TauCeti.Analysis.InnerProductSpace.AlgebraicCurvature.Reaction.Basic
public import TauCeti.Analysis.InnerProductSpace.ExteriorPower.Bracket
import TauCeti.Analysis.InnerProductSpace.ExteriorPower.SymmetricProduct
import TauCeti.Analysis.InnerProductSpace.ExteriorPower.Trace
import TauCeti.LinearAlgebra.ExteriorPower.Basic

/-!
# The sharp product and the operator form of the curvature reaction

Let `V` be a finite-dimensional real inner product space. Identify `⋀² V` with the orthogonal Lie
algebra `so(V)` as in `TauCeti.bivectorAd`, whose bracket is the linear map
`ad : ⋀² (⋀² V) → ⋀² V`. For two endomorphisms `R, S` of `⋀² V`, Böhm and Wilking define the
*sharp product*

`R # S = ad ∘ (R ∧ S) ∘ ad*`,

where `R ∧ S = exteriorPower.symmMap₂ R S` acts on `⋀² (⋀² V)` by
`(R ∧ S)(X ∧ Y) = ½ (R X ∧ S Y + S X ∧ R Y)`; this is `TauCeti.bivectorSharp R S`, and
`R# = R # R = ad ∘ ⋀² R ∘ ad*`. Through the adjoint formula `ad* (u ∧ v) = ∑ₚ (u ∧ eₚ) ∧ (v ∧ eₚ)`
the sharp product becomes a contraction over an orthonormal basis `(eₚ)`
(`TauCeti.inner_bivectorSharp_self_ιMulti`, polarized in `TauCeti.inner_bivectorSharp_ιMulti`):

`⟪R# (u ∧ v), z ∧ w⟫ = ∑ₚ ∑_q (⟪R (u ∧ eₚ), z ∧ e_q⟫ ⟪R (v ∧ eₚ), w ∧ e_q⟫
  - ⟪R (u ∧ eₚ), w ∧ e_q⟫ ⟪R (v ∧ eₚ), z ∧ e_q⟫)`.

For the bivector operator `R = curvatureEndomorphism r` of a bivector-symmetric four-tensor `r`
(in particular of an algebraic curvature tensor) these are exactly the last two sums of the
reaction tensor `Q(r)` of the Ricci-flow curvature equation, while its first sum is the square of
`R`. This gives the operator form of the reaction term
(`TauCeti.FourTensor.IsBivectorSymmetric.curvatureEndomorphism_reactionTensor`),

`curvatureEndomorphism (Q(r)) = 2 (R² + R#)`,

and its polarization `curvatureEndomorphism (Q(r, s)) = R S + S R + 2 R # S`. On the identity
curvature operator `I`, the curvature operator of the unit sphere, this pins the normalization
`I# = (n - 2) I` (`TauCeti.bivectorSharp_id_id`).

## Main definitions

* `TauCeti.bivectorSharp`: the sharp product `R # S = ad ∘ (R ∧ S) ∘ ad*`.

## Main results

* `TauCeti.inner_bivectorSharp_ιMulti` and `TauCeti.inner_bivectorSharp_self_ιMulti`: the sharp
  product as a contraction in an orthonormal basis.
* `TauCeti.FourTensor.IsBivectorSymmetric.inner_curvatureEndomorphism_mul_ιMulti`: the product of
  two bivector operators in coordinates.
* `TauCeti.FourTensor.IsBivectorSymmetric.curvatureEndomorphism_reactionBilinear` and
  `TauCeti.FourTensor.IsBivectorSymmetric.curvatureEndomorphism_reactionTensor`:
  `Q(r, s) = R S + S R + 2 R # S` and `Q(r) = 2 (R² + R#)` on the operator side.
* `TauCeti.adjoint_bivectorSharp`, `LinearMap.IsSymmetric.bivectorSharp`,
  `TauCeti.bivectorSharp_rankOne_self`, and
  `LinearIsometryEquiv.bivectorSharp_conj_exteriorPower_map`:
  adjoint commutation, symmetry preservation, rank-one vanishing, and `O(V)`-equivariance of
  `bivectorSharp`.
* `LinearMap.IsSymmetric.reactionBilinear_ofExteriorEnd`,
  `LinearMap.IsSymmetric.reactionTensor_ofExteriorEnd`,
  `TauCeti.FourTensor.IsAlgebraicCurvatureEndomorphism.mul_add_mul_add_two_smul_bivectorSharp`,
  and `TauCeti.FourTensor.IsAlgebraicCurvatureEndomorphism.two_smul_mul_add_bivectorSharp`:
  the `ofExteriorEnd` reaction identities and closure of `Sym²_B(⋀²V)`.
* `TauCeti.bivectorSharp_id_id`: `I# = (n - 2) I`.

## References

* R. S. Hamilton, *Four-manifolds with positive curvature operator*, J. Differential Geom. 24
  (1986), 153–179, Section 2.
* C. Böhm and B. Wilking, *Manifolds with positive curvature operators are space forms*,
  Ann. of Math. 167 (2008), 1079–1097, Section 2.
-/

public section

open exteriorPower
open scoped RealInnerProductSpace

noncomputable section

namespace TauCeti

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- The **sharp product** of Böhm and Wilking, `R # S = ad ∘ (R ∧ S) ∘ ad*`, for endomorphisms
`R, S` of `⋀² V ≅ so(V)`. Here `ad = TauCeti.bivectorAd` is the bracket of `so(V)` and
`R ∧ S = exteriorPower.symmMap₂ R S`. Its diagonal `R # R` is the operator `R#` of the
curvature reaction `Q(R) = 2 (R² + R#)`. -/
def bivectorSharp :
    Module.End ℝ (⋀[ℝ]^2 V) →ₗ[ℝ] Module.End ℝ (⋀[ℝ]^2 V) →ₗ[ℝ] Module.End ℝ (⋀[ℝ]^2 V) :=
  symmMap₂.compr₂ (LinearMap.llcomp ℝ _ _ _ bivectorAd ∘ₗ
    LinearMap.lcomp ℝ _ (LinearMap.adjoint bivectorAd))

/-- `R # S = ad ∘ (R ∧ S) ∘ ad*`. -/
theorem bivectorSharp_apply (R S : Module.End ℝ (⋀[ℝ]^2 V)) :
    bivectorSharp R S = bivectorAd ∘ₗ symmMap₂ R S ∘ₗ LinearMap.adjoint bivectorAd :=
  (rfl)

/-- The sharp product is symmetric. -/
theorem bivectorSharp_comm (R S : Module.End ℝ (⋀[ℝ]^2 V)) :
    bivectorSharp R S = bivectorSharp S R := by
  rw [bivectorSharp_apply, bivectorSharp_apply, symmMap₂_comm]

/-- `R# = ad ∘ ⋀² R ∘ ad*`. -/
theorem bivectorSharp_self (R : Module.End ℝ (⋀[ℝ]^2 V)) :
    bivectorSharp R R = bivectorAd ∘ₗ map 2 R ∘ₗ LinearMap.adjoint bivectorAd := by
  rw [bivectorSharp_apply, symmMap₂_self]

/-- Taking the adjoint commutes with `TauCeti.bivectorSharp`. -/
@[simp]
theorem adjoint_bivectorSharp (R S : Module.End ℝ (⋀[ℝ]^2 V)) :
    (bivectorSharp R S).adjoint = bivectorSharp R.adjoint S.adjoint := by
  rw [bivectorSharp_apply, bivectorSharp_apply, LinearMap.adjoint_comp, LinearMap.adjoint_comp,
    LinearMap.adjoint_adjoint, adjoint_symmMap₂, LinearMap.comp_assoc]

/-- Quadratic expansion of `TauCeti.bivectorSharp` on a sum of endomorphisms. -/
theorem bivectorSharp_add_self (R S : Module.End ℝ (⋀[ℝ]^2 V)) :
    bivectorSharp (R + S) (R + S) =
      bivectorSharp R R + (2 : ℝ) • bivectorSharp R S + bivectorSharp S S := by
  simp only [map_add, LinearMap.add_apply, bivectorSharp_comm S R, two_smul]
  abel

/-- Every rank-one operator `ξ ↦ ⟪α, ξ⟫ • α` on `⋀[ℝ]^2 V` has vanishing `#`-square. -/
@[simp]
theorem bivectorSharp_rankOne_self (α : ⋀[ℝ]^2 V) :
    bivectorSharp (InnerProductSpace.rankOne ℝ α α).toLinearMap
        (InnerProductSpace.rankOne ℝ α α).toLinearMap = 0 := by
  have hmap : map 2 (InnerProductSpace.rankOne ℝ α α).toLinearMap = 0 :=
    linearMap_ext_inner_ιMulti_two fun X Y Z W ↦ by
      rw [map_apply_ιMulti_two, inner_ιMulti_two]
      simp only [ContinuousLinearMap.coe_coe, InnerProductSpace.rankOne_apply,
        real_inner_smul_left, LinearMap.zero_apply, inner_zero_left]
      ring
  rw [bivectorSharp_self, hmap, LinearMap.zero_comp, LinearMap.comp_zero]

/-- **`R#` in an orthonormal basis.** For every orthonormal basis `(eₚ)` of `V`,
`⟪R# (u ∧ v), z ∧ w⟫ = ∑ₚ ∑_q (⟪R (u ∧ eₚ), z ∧ e_q⟫ ⟪R (v ∧ eₚ), w ∧ e_q⟫
  - ⟪R (u ∧ eₚ), w ∧ e_q⟫ ⟪R (v ∧ eₚ), z ∧ e_q⟫)`. -/
theorem inner_bivectorSharp_self_ιMulti {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ V)
    (R : Module.End ℝ (⋀[ℝ]^2 V)) (u v z w : V) :
    ⟪bivectorSharp R R (ιMulti ℝ 2 ![u, v]), ιMulti ℝ 2 ![z, w]⟫ =
      ∑ p, ∑ q,
        (⟪R (ιMulti ℝ 2 ![u, b p]), ιMulti ℝ 2 ![z, b q]⟫ *
            ⟪R (ιMulti ℝ 2 ![v, b p]), ιMulti ℝ 2 ![w, b q]⟫ -
          ⟪R (ιMulti ℝ 2 ![u, b p]), ιMulti ℝ 2 ![w, b q]⟫ *
            ⟪R (ιMulti ℝ 2 ![v, b p]), ιMulti ℝ 2 ![z, b q]⟫) := by
  rw [bivectorSharp_self, LinearMap.comp_apply, LinearMap.comp_apply,
    ← LinearMap.adjoint_inner_right, adjoint_bivectorAd_ιMulti b, adjoint_bivectorAd_ιMulti b,
    map_sum, sum_inner]
  refine Finset.sum_congr rfl fun p _ ↦ ?_
  rw [inner_sum]
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  rw [map_apply_ιMulti_two, inner_ιMulti_two]

/-- **The sharp product in an orthonormal basis.** For every orthonormal basis `(eₚ)` of `V`,
`⟪(R # S)(u ∧ v), z ∧ w⟫` is half the sum over `p, q` of
`⟪R (u ∧ eₚ), z ∧ e_q⟫ ⟪S (v ∧ eₚ), w ∧ e_q⟫ - ⟪R (u ∧ eₚ), w ∧ e_q⟫ ⟪S (v ∧ eₚ), z ∧ e_q⟫` and of
the same expression with `R` and `S` interchanged. -/
theorem inner_bivectorSharp_ιMulti {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ V)
    (R S : Module.End ℝ (⋀[ℝ]^2 V)) (u v z w : V) :
    ⟪bivectorSharp R S (ιMulti ℝ 2 ![u, v]), ιMulti ℝ 2 ![z, w]⟫ =
      (1 / 2 : ℝ) * ∑ p, ∑ q,
        (⟪R (ιMulti ℝ 2 ![u, b p]), ιMulti ℝ 2 ![z, b q]⟫ *
            ⟪S (ιMulti ℝ 2 ![v, b p]), ιMulti ℝ 2 ![w, b q]⟫ -
          ⟪R (ιMulti ℝ 2 ![u, b p]), ιMulti ℝ 2 ![w, b q]⟫ *
            ⟪S (ιMulti ℝ 2 ![v, b p]), ιMulti ℝ 2 ![z, b q]⟫ +
          ⟪S (ιMulti ℝ 2 ![u, b p]), ιMulti ℝ 2 ![z, b q]⟫ *
            ⟪R (ιMulti ℝ 2 ![v, b p]), ιMulti ℝ 2 ![w, b q]⟫ -
          ⟪S (ιMulti ℝ 2 ![u, b p]), ιMulti ℝ 2 ![w, b q]⟫ *
            ⟪R (ιMulti ℝ 2 ![v, b p]), ιMulti ℝ 2 ![z, b q]⟫) := by
  -- Polarize the diagonal formula.
  have hpol : bivectorSharp R S = (1 / 2 : ℝ) •
      (bivectorSharp (R + S) (R + S) - bivectorSharp R R - bivectorSharp S S) := by
    rw [bivectorSharp_add_self]
    module
  rw [hpol, LinearMap.smul_apply, LinearMap.sub_apply, LinearMap.sub_apply, real_inner_smul_left,
    inner_sub_left, inner_sub_left, inner_bivectorSharp_self_ιMulti b,
    inner_bivectorSharp_self_ιMulti b, inner_bivectorSharp_self_ιMulti b, ← Finset.sum_sub_distrib,
    ← Finset.sum_sub_distrib]
  congr 1
  refine Finset.sum_congr rfl fun p _ ↦ ?_
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  simp only [LinearMap.add_apply, inner_add_left]
  ring

end TauCeti

namespace LinearIsometryEquiv

open exteriorPower TauCeti

/-- Conjugating two endomorphisms of `⋀[ℝ]^2 V` by the exterior square of a linear isometric
equivalence commutes with `TauCeti.bivectorSharp`. -/
theorem bivectorSharp_conj_exteriorPower_map {W V : Type*}
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (e : W ≃ₗᵢ[ℝ] V) (R S : Module.End ℝ (⋀[ℝ]^2 V)) :
    bivectorSharp
        (map 2 e.symm.toLinearMap ∘ₗ R ∘ₗ map 2 e.toLinearMap)
        (map 2 e.symm.toLinearMap ∘ₗ S ∘ₗ map 2 e.toLinearMap) =
      map 2 e.symm.toLinearMap ∘ₗ bivectorSharp R S ∘ₗ map 2 e.toLinearMap := by
  rw [bivectorSharp_apply, bivectorSharp_apply, ← map_comp_symmMap₂, ← symmMap₂_comp_map]
  calc
    bivectorAd ∘ₗ
        (map 2 (map 2 e.symm.toLinearMap) ∘ₗ (symmMap₂ R S ∘ₗ map 2 (map 2 e.toLinearMap))) ∘ₗ
          LinearMap.adjoint bivectorAd
        = (bivectorAd ∘ₗ map 2 (map 2 e.symm.toLinearMap)) ∘ₗ symmMap₂ R S ∘ₗ
            (map 2 (map 2 e.toLinearMap) ∘ₗ LinearMap.adjoint bivectorAd) := by
          simp only [LinearMap.comp_assoc]
    _ = (map 2 e.symm.toLinearMap ∘ₗ bivectorAd) ∘ₗ symmMap₂ R S ∘ₗ
            (LinearMap.adjoint bivectorAd ∘ₗ map 2 e.toLinearMap) := by
          rw [← e.symm.exteriorPower_map_comp_bivectorAd,
            ← e.adjoint_bivectorAd_comp_exteriorPower_map]
    _ = map 2 e.symm.toLinearMap ∘ₗ
            (bivectorAd ∘ₗ symmMap₂ R S ∘ₗ LinearMap.adjoint bivectorAd) ∘ₗ
              map 2 e.toLinearMap := by
          simp only [LinearMap.comp_assoc]

end LinearIsometryEquiv

namespace LinearMap.IsSymmetric

open TauCeti

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- The `#` product of two symmetric endomorphisms of `⋀[ℝ]^2 V` is symmetric. -/
theorem bivectorSharp {R S : Module.End ℝ (⋀[ℝ]^2 V)} (hR : R.IsSymmetric) (hS : S.IsSymmetric) :
    (TauCeti.bivectorSharp R S).IsSymmetric :=
  (LinearMap.isSymmetric_iff_isSelfAdjoint _).mpr <| by
    simp only [IsSelfAdjoint, LinearMap.star_eq_adjoint, TauCeti.adjoint_bivectorSharp,
      hR.adjoint_eq, hS.adjoint_eq]

end LinearMap.IsSymmetric

namespace TauCeti

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

namespace FourTensor

/-- **The product of two bivector operators in coordinates.** Let `R` and `S` be the bivector
operators of a bivector-symmetric four-tensor `r` and of a four-tensor `s` antisymmetric in each
pair. For every orthonormal basis `(eₚ)` of `V`,
`⟪R (S (u ∧ v)), z ∧ w⟫ = ½ ∑ₚ ∑_q s(u, v, eₚ, e_q) r(z, w, eₚ, e_q)`. -/
theorem IsBivectorSymmetric.inner_curvatureEndomorphism_mul_ιMulti {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ V) {r s : FourTensor V} (hr : IsBivectorSymmetric r)
    (hs₁ : ∀ u v z w, s ![u, v, z, w] = -s ![v, u, z, w])
    (hs₂ : ∀ u v z w, s ![u, v, z, w] = -s ![u, v, w, z]) (u v z w : V) :
    ⟪(curvatureEndomorphism r * curvatureEndomorphism s) (ιMulti ℝ 2 ![u, v]),
        ιMulti ℝ 2 ![z, w]⟫ =
      (1 / 2 : ℝ) * ∑ p, ∑ q, s ![u, v, b p, b q] * r ![z, w, b p, b q] := by
  have h := b.sum_sum_inner_ιMulti_two_mul_inner_ιMulti_two
    (curvatureEndomorphism s (ιMulti ℝ 2 ![u, v])) (curvatureEndomorphism r (ιMulti ℝ 2 ![z, w]))
  simp only [inner_curvatureEndomorphism_ιMulti_of_antisymm hs₁ hs₂,
    hr.inner_curvatureEndomorphism_ιMulti] at h
  rw [mul_apply_eq_comp, hr.isSymmetric_curvatureEndomorphism, h]
  ring

/-- **The polarized reaction tensor on the operator side.** For bivector-symmetric four-tensors
`r` and `s` with bivector operators `R` and `S`, the bivector operator of `Q(r, s)` is
`R S + S R + 2 R # S`. -/
theorem IsBivectorSymmetric.curvatureEndomorphism_reactionBilinear {r s : FourTensor V}
    (hr : IsBivectorSymmetric r) (hs : IsBivectorSymmetric s) :
    curvatureEndomorphism (FourTensor.reactionBilinear V r s) =
      curvatureEndomorphism r * curvatureEndomorphism s +
        curvatureEndomorphism s * curvatureEndomorphism r +
        (2 : ℝ) • bivectorSharp (curvatureEndomorphism r) (curvatureEndomorphism s) := by
  let b := stdOrthonormalBasis ℝ V
  refine linearMap_ext_inner_ιMulti_two fun u v z w ↦ ?_
  rw [(hr.reactionBilinear hs).inner_curvatureEndomorphism_ιMulti,
    reactionBilinear_apply_orthonormalBasis b, LinearMap.add_apply, LinearMap.add_apply,
    LinearMap.smul_apply, inner_add_left, inner_add_left, real_inner_smul_left,
    hr.inner_curvatureEndomorphism_mul_ιMulti b hs.antisymm_first hs.antisymm_last,
    hs.inner_curvatureEndomorphism_mul_ιMulti b hr.antisymm_first hr.antisymm_last,
    inner_bivectorSharp_ιMulti b]
  simp only [hr.inner_curvatureEndomorphism_ιMulti, hs.inner_curvatureEndomorphism_ιMulti,
    Finset.sum_add_distrib, Finset.sum_sub_distrib]
  ring

/-- **The reaction tensor on the operator side**, `Q(R) = 2 (R² + R#)`: for a bivector-symmetric
four-tensor `r`, in particular an algebraic curvature tensor, with bivector operator `R`, the
bivector operator of the reaction tensor `Q(r)` is `2 (R² + R#)`. -/
theorem IsBivectorSymmetric.curvatureEndomorphism_reactionTensor {r : FourTensor V}
    (hr : IsBivectorSymmetric r) :
    curvatureEndomorphism (reactionTensor r) =
      (2 : ℝ) • (curvatureEndomorphism r * curvatureEndomorphism r +
        bivectorSharp (curvatureEndomorphism r) (curvatureEndomorphism r)) := by
  rw [← reactionBilinear_self, hr.curvatureEndomorphism_reactionBilinear hr]
  module

end FourTensor

end TauCeti

namespace LinearMap.IsSymmetric

open TauCeti TauCeti.FourTensor

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- **Polarized bivector-operator identity**: for symmetric endomorphisms `R, S` of `⋀[ℝ]^2 V`,
`reactionBilinear V (ofExteriorEnd R) (ofExteriorEnd S)` equals
`ofExteriorEnd (R * S + S * R + 2 • TauCeti.bivectorSharp R S)`. -/
theorem reactionBilinear_ofExteriorEnd {R S : Module.End ℝ (⋀[ℝ]^2 V)}
    (hR : R.IsSymmetric) (hS : S.IsSymmetric) :
    reactionBilinear V (ofExteriorEnd R) (ofExteriorEnd S) =
      ofExteriorEnd (R * S + S * R + (2 : ℝ) • TauCeti.bivectorSharp R S) := by
  have hr : IsBivectorSymmetric (ofExteriorEnd R) :=
    (isBivectorSymmetric_ofExteriorEnd_iff R).mpr hR
  have hs : IsBivectorSymmetric (ofExteriorEnd S) :=
    (isBivectorSymmetric_ofExteriorEnd_iff S).mpr hS
  refine (hr.reactionBilinear hs).ofExteriorEnd_curvatureEndomorphism.symm.trans ?_
  rw [hr.curvatureEndomorphism_reactionBilinear hs, curvatureEndomorphism_ofExteriorEnd,
    curvatureEndomorphism_ofExteriorEnd]

/-- **Bivector-operator identity**
`Q(ofExteriorEnd R) = ofExteriorEnd (2 • (R * R + TauCeti.bivectorSharp R R))` for any symmetric
endomorphism `R` of `⋀[ℝ]^2 V`. -/
theorem reactionTensor_ofExteriorEnd {R : Module.End ℝ (⋀[ℝ]^2 V)} (hR : R.IsSymmetric) :
    reactionTensor (ofExteriorEnd R) =
      ofExteriorEnd ((2 : ℝ) • (R * R + TauCeti.bivectorSharp R R)) := by
  rw [← reactionBilinear_self, reactionBilinear_ofExteriorEnd hR hR]
  congr 1
  module

end LinearMap.IsSymmetric

namespace TauCeti.FourTensor.IsAlgebraicCurvatureEndomorphism

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- `IsAlgebraicCurvatureEndomorphism` is closed under the polarized Hamilton reaction
`R * S + S * R + 2 • TauCeti.bivectorSharp R S`. -/
theorem mul_add_mul_add_two_smul_bivectorSharp {R S : Module.End ℝ (⋀[ℝ]^2 V)}
    (hR : IsAlgebraicCurvatureEndomorphism R) (hS : IsAlgebraicCurvatureEndomorphism S) :
    IsAlgebraicCurvatureEndomorphism (R * S + S * R + (2 : ℝ) • bivectorSharp R S) := by
  rw [← isAlgebraicCurvature_ofExteriorEnd_iff,
    ← LinearMap.IsSymmetric.reactionBilinear_ofExteriorEnd hR.isSymmetric hS.isSymmetric]
  exact ((isAlgebraicCurvature_ofExteriorEnd_iff R).mpr hR).reactionBilinear
    ((isAlgebraicCurvature_ofExteriorEnd_iff S).mpr hS)

/-- `IsAlgebraicCurvatureEndomorphism` is closed under Hamilton's quadratic operator
`2 • (R * R + TauCeti.bivectorSharp R R)`. -/
theorem two_smul_mul_add_bivectorSharp {R : Module.End ℝ (⋀[ℝ]^2 V)}
    (hR : IsAlgebraicCurvatureEndomorphism R) :
    IsAlgebraicCurvatureEndomorphism ((2 : ℝ) • (R * R + bivectorSharp R R)) := by
  rw [← isAlgebraicCurvature_ofExteriorEnd_iff,
    ← LinearMap.IsSymmetric.reactionTensor_ofExteriorEnd hR.isSymmetric]
  exact ((isAlgebraicCurvature_ofExteriorEnd_iff R).mpr hR).reactionTensor

end TauCeti.FourTensor.IsAlgebraicCurvatureEndomorphism

namespace TauCeti

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- **The normalization `I# = (n - 2) I`**: on the identity curvature operator `I` of `⋀² V`, the
curvature operator of the unit sphere, the sharp product is `(n - 2) I` with `n = dim V`. -/
@[simp] theorem bivectorSharp_id_id :
    bivectorSharp (LinearMap.id : Module.End ℝ (⋀[ℝ]^2 V)) LinearMap.id =
      ((Module.finrank ℝ V : ℝ) - 2) • LinearMap.id := by
  have h := (FourTensor.isAlgebraicCurvature_constantCurvature (V := V)).isBivectorSymmetric
    |>.curvatureEndomorphism_reactionTensor
  rw [FourTensor.reactionTensor_constantCurvature, map_smul,
    FourTensor.curvatureEndomorphism_constantCurvature, Module.End.mul_eq_comp,
    LinearMap.id_comp] at h
  linear_combination (norm := module) (-(2 : ℝ)⁻¹) • h

end TauCeti
