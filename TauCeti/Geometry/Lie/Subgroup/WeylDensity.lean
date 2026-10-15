/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.Subgroup.LieAlgebra
public import TauCeti.Geometry.Lie.Adjoint.Representation.Basic
public import TauCeti.LinearAlgebra.Determinant.Quotient
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# The Weyl density of a subgroup

For a subgroup `K` of a finite-dimensional real Lie group `G`, the adjoint action of `K`
preserves the Lie algebra `𝔨 = Lie(K)`, so for `t ∈ K` the endomorphism `Ad t⁻¹ - 1` of `𝔤`
descends to the quotient `𝔤 ⧸ 𝔨`. The **Weyl density** of `K` at `t` is the absolute value of
the determinant of that quotient endomorphism,
`weylDensity K t = |det ((Ad t⁻¹ - 1) on 𝔤 ⧸ 𝔨)|`.
For a maximal torus `T` of a compact connected group it is the density `∏_{α > 0} |1 - α(t)⁻¹|²`
of the Weyl integration formula; this file defines it for every subgroup and proves that it is
continuous, which is what the integral against it needs.

## Main definitions

* `TauCeti.Lie.weylDensity`: the Weyl density of a subgroup.

## Main results

* `TauCeti.Lie.weylDensity_eq_abs_det_compression`: the Weyl density is the absolute determinant
  of the compression of `Ad t⁻¹ - 1` to any complement of `Lie(K)`
  (`LinearMap.det_mapQ_of_isCompl`).
* `TauCeti.Lie.continuous_weylDensity`: the Weyl density is continuous.

## References

* T. Bröcker and T. tom Dieck, *Representations of Compact Lie Groups*, Springer GTM 98 (1985),
  Chapter IV, "The Maximal Torus of a Compact Lie Group".
-/

public section

noncomputable section

namespace TauCeti.Lie

open scoped ContDiff Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [FiniteDimensional ℝ E] [LieGroup I ∞ G] [T2Space G]

attribute [local instance] LieGroup.minSmoothnessThree
attribute [local instance] ContMDiffMul.boundarylessManifold

noncomputable local instance : FiniteDimensional ℝ (LeftInvariantDerivation I G) :=
  finiteDimensional_leftInvariantDerivation
    (ContMDiffMul.isInteriorPoint (I := I) (n := ∞) (by simp) (1 : G))

/-- **The Weyl density** of a subgroup `K` at `t ∈ K`: the absolute determinant of the
endomorphism of `𝔤 ⧸ Lie(K)` induced by `Ad t⁻¹ - 1`. -/
def weylDensity (K : Subgroup G) (t : K) : ℝ :=
  |LinearMap.det
    (Submodule.mapQ _ _ ((Ad (I := I) ((t : G)⁻¹)).toLinearEquiv.toLinearMap - LinearMap.id)
      (lieSubalgebraOfSubgroup_le_comap_Ad_sub_id (K.inv_mem t.2)))|

theorem weylDensity_def (K : Subgroup G) (t : K) :
    weylDensity (I := I) K t =
      |LinearMap.det
        (Submodule.mapQ _ _
          ((Ad (I := I) ((t : G)⁻¹)).toLinearEquiv.toLinearMap - LinearMap.id)
          (lieSubalgebraOfSubgroup_le_comap_Ad_sub_id (K.inv_mem t.2)))| := by
  rw [weylDensity]

@[simp]
theorem weylDensity_nonneg (K : Subgroup G) (t : K) : 0 ≤ weylDensity (I := I) K t := by
  rw [weylDensity]
  exact abs_nonneg _

/-- **The Weyl density as a determinant on a complement**: for any complement `q` of `Lie(K)`,
`weylDensity K t` is the absolute determinant of the compression of `Ad t⁻¹ - 1` to `q`. -/
theorem weylDensity_eq_abs_det_compression (K : Subgroup G)
    {q : Submodule ℝ (LeftInvariantDerivation I G)}
    (hq : IsCompl (lieSubalgebraOfSubgroup (I := I) K).toSubmodule q) (t : K) :
    weylDensity (I := I) K t =
      |LinearMap.det (q.projectionOnto _ hq.symm ∘ₗ
        ((Ad (I := I) ((t : G)⁻¹)).toLinearEquiv.toLinearMap - LinearMap.id) ∘ₗ q.subtype)| := by
  rw [weylDensity, LinearMap.det_mapQ_of_isCompl hq]

/-- **The Weyl density of `K` is a continuous function on `K`.** -/
@[fun_prop]
theorem continuous_weylDensity (K : Subgroup G) : Continuous (weylDensity (I := I) K) := by
  -- On a complement `q` of `Lie(K)` the density is the absolute determinant of the compression of
  -- `Ad t⁻¹ - 1` to `q`; the compression depends continuously on `t` because the adjoint action
  -- does, and the determinant is continuous on the endomorphisms of `q`.
  obtain ⟨q, hq⟩ := exists_isCompl (lieSubalgebraOfSubgroup (I := I) K).toSubmodule
  -- The compression of `Ad t⁻¹ - 1` to the complement `q`, as a continuous endomorphism.
  let c : K → q →L[ℝ] q := fun t =>
    LinearMap.toContinuousLinearMap (q.projectionOnto _ hq.symm ∘ₗ
      ((Ad (I := I) ((t : G)⁻¹)).toLinearEquiv.toLinearMap - LinearMap.id) ∘ₗ q.subtype)
  have hfun : weylDensity (I := I) K =
      fun t => |LinearMap.det ((c t : q →L[ℝ] q) : q →ₗ[ℝ] q)| := by
    funext t
    rw [weylDensity_eq_abs_det_compression K hq, LinearMap.coe_toContinuousLinearMap]
  rw [hfun]
  refine continuous_abs.comp (ContinuousLinearMap.continuous_det.comp ?_)
  rw [continuous_clm_apply]
  intro x
  simp only [c, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_comp, Function.comp_apply,
    Submodule.coe_subtype, LinearMap.sub_apply, LinearEquiv.coe_coe, LieEquiv.coe_toLinearEquiv,
    LinearMap.id_apply]
  have hproj : Continuous (q.projectionOnto _ hq.symm) :=
    (q.projectionOnto _ hq.symm).continuous_of_finiteDimensional
  refine hproj.comp (Continuous.sub ?_ continuous_const)
  have hAd : Continuous fun p : G × LeftInvariantDerivation I G => Ad (I := I) p.1 p.2 :=
    (contMDiff_Ad_apply (I := I) (G := G)).continuous
  let _ : IsTopologicalGroup G := topologicalGroup_of_lieGroup I ∞
  exact hAd.comp (continuous_subtype_val.inv.prodMk continuous_const)

end TauCeti.Lie
