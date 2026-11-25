/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.SmoothSingular.Chains
public import Mathlib.Topology.Instances.AddCircle.Real
import TauCeti.Geometry.Manifold.DifferentialForm.Continuity
import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Chart
import TauCeti.MeasureTheory.Integral.ShrinkingAffineImage
import TauCeti.Topology.Circle.AddCircle

/-!
# Forms with integer integrals over all smooth simplices

A continuous real `p`-form `φ` with `p ≥ 1` on a boundaryless manifold whose integral over every
smooth singular `p`-simplex is an integer vanishes
(`TauCeti.RoughForm.eq_zero_of_forall_integral_eq_intCast`).

Consequently two smooth forms of positive degree whose integrals over every smooth singular chain
with integer coefficients agree modulo `ℤ` are equal
(`TauCeti.SmoothForm.eq_of_forall_coe_integrationCochain_eq`). This is the uniqueness of the
curvature of a differential character. The hypothesis `p ≥ 1` is needed, since in degree `0` the
integral over a point is evaluation, and a nonzero constant integer function has integer integrals.
The comparison modulo `ℤ` uses that a real number vanishes in `ℝ/ℤ` exactly when it is an integer
(`UnitAddCircle.coe_eq_zero_iff`).

## Implementation notes

The proof is local. Read `φ` in the extended chart at `x`, where it is the continuous coordinate
expression `Φ = φ.inChartAt x` on the model space, and take the affine simplices
`y ↦ c + t • L y` in that chart, centred at the chart image `c` of `x`, for a linear map
`L : ℝᵖ → E` and a small real `t`. The integral of `φ` over such a simplex is `tᵖ` times
the integral of `Φ (c + t • L y)` on the vectors `L eᵢ` over `Δᵖ`, and the latter tends to
`vol Δᵖ · Φ c (L e)` as `t → 0` (`IsCompact.tendsto_setIntegral_add_smul`). An integer of
absolute value less than `1` is `0`, so if `Φ c (L e)` were nonzero, then for small nonzero `t`
the integral would be an integer that is neither `0` nor of absolute value at least `1`. Hence
`Φ c` vanishes on every tuple of vectors, and `Φ c = φ x`
(`TauCeti.RoughForm.inChartAt_extChartAt_self`).

## References

* J. Cheeger and J. Simons, *Differential characters and geometric invariants*, Geometry and
  Topology (College Park, 1983/84), Lecture Notes in Math. 1167, Springer, 1985, §1, where the
  curvature of a differential character is shown to be unique.
-/

public section

noncomputable section

open Set Filter MeasureTheory Topology
open scoped Manifold ContDiff

namespace TauCeti

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] {p : ℕ}

namespace RoughForm

section Affine

variable (x : M) (L : EuclideanSpace ℝ (Fin p) →L[ℝ] E) (t : ℝ)

/-- The affine map `y ↦ c + t • L y` into the chart at `x`, followed by the inverse chart, is smooth
on the points that the affine map sends into the interior of the chart target. -/
private theorem contMDiffOn_extChartAt_symm_comp_affine :
    ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) I ∞
      ((extChartAt I x).symm ∘ fun y ↦ extChartAt I x x + t • L y)
      ((fun y ↦ extChartAt I x x + t • L y) ⁻¹' interior (extChartAt I x).target) :=
  (contMDiffOn_extChartAt_symm x).comp
    (contDiff_const.add (contDiff_const.smul L.contDiff)).contMDiff.contMDiffOn
    fun _ hy ↦ (interior_subset : interior (extChartAt I x).target ⊆ _) hy

/-- The smooth simplex `y ↦ (extChartAt I x).symm (c + t • L y)`, for `c` the chart image of `x`,
when the affine map sends `Δᵖ` into the interior of the chart target. -/
private def affineChartSimplex
    (hΔ : ∀ y ∈ fullSimplex p, extChartAt I x x + t • L y ∈ interior (extChartAt I x).target) :
    SmoothSimplex I M p :=
  SmoothSimplex.ofContMDiffOn (contMDiffOn_extChartAt_symm_comp_affine x L t)
    ((isOpen_interior.preimage
      (continuous_const.add (continuous_const.smul L.continuous))).mem_nhdsSet.mpr hΔ)

/-- The integral of a form over `affineChartSimplex` is `tᵖ` times the integral over `Δᵖ` of the
form read in the chart, along the affine map, on the vectors `L eᵢ`. -/
private theorem integral_affineChartSimplex (φ : RoughForm I M ℝ p)
    (hΔ : ∀ y ∈ fullSimplex p, extChartAt I x x + t • L y ∈ interior (extChartAt I x).target) :
    (affineChartSimplex x L t hΔ).integral φ =
      t ^ p * ∫ y in fullSimplex p,
        φ.inChartAt x (extChartAt I x x + t • L y) fun i ↦ L (EuclideanSpace.single i 1) := by
  rw [affineChartSimplex, SmoothSimplex.integral_ofContMDiffOn, ← integral_const_mul]
  refine setIntegral_congr_fun (isClosed_fullSimplex p).measurableSet fun y hy ↦ ?_
  have hA : HasFDerivAt (fun y ↦ extChartAt I x x + t • L y) (t • L) y :=
    (t • L).hasFDerivAt.const_add _
  have hu : MDifferentiableAt 𝓘(ℝ, E) I (extChartAt I x).symm (extChartAt I x x + t • L y) :=
    ((contMDiffOn_extChartAt_symm (n := ∞) x).contMDiffAt
      (mem_interior_iff_mem_nhds.mp (hΔ y hy))).mdifferentiableAt (by simp)
  rw [mpullback_comp_apply_of_hasFDerivAt hA hu,
    mpullback_extChartAt_symm_eq_inChartAt φ x
      (interior_mono (extChartAt_target_subset_range x) (hΔ y hy))]
  refine (ContinuousAlternatingMap.compContinuousLinearMap_apply _ _ _).trans ?_
  refine ((φ.inChartAt x (extChartAt I x x + t • L y)).map_smul_univ (fun _ ↦ t)
    fun i ↦ L (EuclideanSpace.single i 1)).trans ?_
  simp [Finset.prod_const]

end Affine

/-- The key local step: the form read in the chart at an interior point `x` vanishes at the chart
image of `x` on every tuple `L eᵢ`, if the integral of the form over every smooth simplex is an
integer. -/
private theorem inChartAt_extChartAt_self_apply_eq_zero (hp : p ≠ 0) {φ : RoughForm I M ℝ p}
    (hφ : IsSmoothForm I 0 φ) (h : ∀ σ : SmoothSimplex I M p, ∃ n : ℤ, σ.integral φ = n) {x : M}
    (hx : I.IsInteriorPoint x) (L : EuclideanSpace ℝ (Fin p) →L[ℝ] E) :
    φ.inChartAt x (extChartAt I x x) (fun i ↦ L (EuclideanSpace.single i 1)) = 0 := by
  set c := extChartAt I x x
  set T := interior (extChartAt I x).target
  set Φ : E → E [⋀^Fin p]→L[ℝ] ℝ := φ.inChartAt x
  set w : Fin p → E := fun i ↦ L (EuclideanSpace.single i 1)
  set G : ℝ → ℝ := fun t ↦ ∫ y in fullSimplex p, Φ (c + t • L y) w
  have hcT : c ∈ T := I.isInteriorPoint_iff.mp hx
  have hw : Continuous fun A : E [⋀^Fin p]→L[ℝ] ℝ ↦ A w :=
    (ContinuousAlternatingMap.apply ℝ E ℝ w).continuous
  have hlim : Tendsto G (𝓝 0) (𝓝 (volume.real (fullSimplex p) * Φ c w)) := by
    simpa only [smul_eq_mul] using (isCompact_fullSimplex p).tendsto_setIntegral_add_smul
      (isClosed_fullSimplex p).measurableSet L.continuous (Φ := fun z ↦ Φ z w)
      (Filter.mem_of_superset (isOpen_interior.mem_nhds hcT) fun z hz ↦ hw.continuousAt.comp
        ((hφ.continuousOn_inChartAt x).continuousAt (mem_interior_iff_mem_nhds.mp hz)))
  have hvol : 0 < volume.real (fullSimplex p) :=
    ENNReal.toReal_pos
      (Measure.measure_pos_of_nonempty_interior _ (nonempty_interior_fullSimplex p)).ne'
      (isCompact_fullSimplex p).measure_lt_top.ne
  -- If `Φ c w ≠ 0`, then for small `t ≠ 0` the integral of `φ` over the affine simplex, which is
  -- `tᵖ G t`, is a nonzero integer of absolute value `< 1`.
  by_contra hne
  have hsmall : Tendsto (fun t ↦ |t ^ p * G t|) (𝓝 0) (𝓝 0) := by
    simpa only [zero_pow hp, zero_mul, abs_zero, Function.comp_def] using
      (continuous_abs.tendsto _).comp (((continuous_pow p).tendsto 0).mul hlim)
  obtain ⟨t, ht0, hΔ, hGt, hlt⟩ :=
    ((eventually_mem_nhdsWithin (s := {(0 : ℝ)}ᶜ)).and
      ((((isCompact_fullSimplex p).eventually_forall_add_smul_mem L.continuous
        (isOpen_interior.mem_nhds hcT)).and
        ((hlim.eventually_ne (mul_ne_zero hvol.ne' hne)).and
          (hsmall.eventually (gt_mem_nhds one_pos)))).filter_mono nhdsWithin_le_nhds)).exists
  obtain ⟨n, hn⟩ := h (affineChartSimplex x L t hΔ)
  rw [integral_affineChartSimplex] at hn
  have hn0 : n = 0 := Int.abs_lt_one_iff.mp (by exact_mod_cast hn ▸ hlt)
  rw [hn0, Int.cast_zero] at hn
  exact mul_ne_zero (pow_ne_zero p ht0) hGt hn

/-- **A continuous form with integer integrals over all smooth simplices vanishes.** On a
boundaryless manifold, a continuous real `p`-form with `p ≠ 0` whose integral over every smooth
singular `p`-simplex is an integer is zero. -/
theorem eq_zero_of_forall_integral_eq_intCast [BoundarylessManifold I M] (hp : p ≠ 0)
    {φ : RoughForm I M ℝ p} (hφ : IsSmoothForm I 0 φ)
    (h : ∀ σ : SmoothSimplex I M p, ∃ n : ℤ, σ.integral φ = n) : φ = 0 := by
  funext x
  have hx : I.IsInteriorPoint x := BoundarylessManifold.isInteriorPoint
  refine ContinuousAlternatingMap.ext fun v ↦ ?_
  -- Every tuple `v` of vectors is `(L e₁, …, L eₚ)` for the linear map `L : ℝᵖ → E` sending the
  -- standard basis to `v`.
  let L : EuclideanSpace ℝ (Fin p) →L[ℝ] E :=
    LinearMap.toContinuousLinearMap ((EuclideanSpace.basisFun (Fin p) ℝ).toBasis.constr ℝ v)
  have hL : (fun i ↦ L (EuclideanSpace.single i 1)) = v := by
    funext i
    have h := (EuclideanSpace.basisFun (Fin p) ℝ).toBasis.constr_basis ℝ v i
    rwa [OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply] at h
  rw [← inChartAt_extChartAt_self φ x, ← hL]
  exact inChartAt_extChartAt_self_apply_eq_zero hp hφ h hx L

end RoughForm

section Uniqueness

variable {M : Type} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M]

/-- **Curvatures of differential characters are unique.** On a boundaryless manifold, two smooth
forms of positive degree whose integrals over every smooth singular integral chain agree modulo
`ℤ` are equal. -/
theorem SmoothForm.eq_of_forall_coe_integrationCochain_eq {p : ℕ} (hp : p ≠ 0)
    {φ ψ : SmoothForm I M ℝ p}
    (h : ∀ c : ((smoothSingularSubcomplex I M : SSet).chainComplex (ModuleCat.of ℤ ℤ)).X p,
      ((integrationCochain φ.val).hom c : UnitAddCircle) = (integrationCochain ψ.val).hom c) :
    φ = ψ := by
  have hφ : IsSmoothForm I 0 φ.val := φ.isSmoothForm.of_le (by simp)
  have hψ : IsSmoothForm I 0 ψ.val := ψ.isSmoothForm.of_le (by simp)
  refine Subtype.ext (sub_eq_zero.mp (RoughForm.eq_zero_of_forall_integral_eq_intCast hp
    (hφ.add hψ.neg) fun σ ↦ ?_))
  -- Test `h` on the chain of the simplex `σ` with coefficient `1`.
  have hσ := h (((smoothSingularSubcomplex I M : SSet).ιChainComplex
    (R := ModuleCat.of ℤ ℤ) σ).hom 1)
  rw [integrationCochain_ιChainComplex, integrationCochain_ιChainComplex, one_smul,
    one_smul, ← sub_eq_zero, ← AddCircle.coe_sub, UnitAddCircle.coe_eq_zero_iff] at hσ
  rwa [sub_eq_add_neg, SmoothSimplex.integral_add σ hφ hψ.neg, SmoothSimplex.integral_neg,
    ← sub_eq_add_neg]

end Uniqueness

end TauCeti
