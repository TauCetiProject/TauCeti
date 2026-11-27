/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Boundary.Charts
public import TauCeti.Geometry.Manifold.Boundary.InwardFlow
import TauCeti.Geometry.Manifold.Boundary.Derivative
import TauCeti.Geometry.Manifold.IntegralCurve.Interval
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Boundary

/-!
# The flow-out of the boundary is a local diffeomorphism

Let `M` be a smooth Hausdorff manifold modeled on the Euclidean half-space `𝓡∂ (n + 1)` and `v` a
smooth vector field on `M` pointing inward at a boundary point `a`. Let `Φ x t` be a forward flow
of `v` from the boundary, as given by `TauCeti.exists_contMDiffOn_boundaryFlow`: for boundary
points `x` near `a` and small times `t ≥ 0`, the curve `s ↦ Φ x s` starts at `x` and is an
integral curve of `v` on `[0, t]`. Then the **flow-out** of the boundary,
`(x, t) ↦ Φ x t` on `∂M × [0, ∞)`, is a smooth local diffeomorphism at `(a, 0)`
(`TauCeti.isLocalDiffeomorphAt_flowOut_boundary`). Here `∂M` carries the manifold structure of
`TauCeti.isManifold_boundary`, and the time parameter is the half-line `EuclideanHalfSpace 1`, so
that `∂M × [0, ∞)` is a manifold with boundary over `(𝓡 n).prod (𝓡∂ 1)`.

In the preferred chart at `a` the flow `Φ` is the forward part of the local flow `Ψ` of the
coordinate field extended across the boundary hyperplane
(`TauCeti.exists_contDiffOn_chartFlow_of_isOutwardPointing_neg`), by uniqueness of integral curves.
The flow-out is read in charts as `(y, t) ↦ Ψ y t` on the coordinate hyperplane, which is defined
and smooth at negative times too. Its derivative at `(a, 0)` is `(y', t') ↦ y' + t' w`, for `w` the
coordinate field at `a`; it is injective since `w` points strictly inward. The zeroth coordinate of
`Ψ y t` increases strictly with `t` and vanishes at `t = 0`, so the flow-out sends exactly the
nonnegative times into the half-space. The inverse function theorem at boundary points,
`TauCeti.isLocalDiffeomorphAt_of_injective_fderiv_of_mem_range_iff`, then applies. The boundaryless
analogue, for complete fields and immersed hypersurfaces, is
`TauCeti.isLocalDiffeomorph_globalFlow_comp`.

This is the local ingredient of the flow construction of a smooth collar (Hirsch, *Differential
Topology*, Chapter 4, Theorem 6.1; Lee, *Introduction to Smooth Manifolds*, Theorem 9.25), whose
other ingredients are the injectivity of the flow-out (`TauCeti.injOn_flowOut_boundary`) and a
smooth depth (`TauCeti.exists_contMDiffMap_depth_boundaryFlow`).

## Main results

* `TauCeti.isLocalDiffeomorphAt_flowOut_boundary`: the flow-out of the boundary along an inward
  field is a smooth local diffeomorphism at each point `(a, 0)` of the zero slice at which the
  field points inward.

## References

* M. Hirsch, *Differential Topology*, Springer GTM 33 (1976), Chapter 4, Theorem 6.1.
* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013), Theorems 9.20
  and 9.25.
-/

public section

open Filter Function Manifold Set Topology
open scoped ContDiff Manifold

namespace TauCeti

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace (n + 1)) M]

/-- The flow-out `(y, s) ↦ Ψ (L y) (s 0)` of the coordinate hyperplane, for `L` its
parametrization, factors through the continuous linear map `(y, s) ↦ (L y, s 0)`. -/
private theorem flowOut_euclideanHalfSpaceBoundaryParam_eq_comp
    (Ψ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ → EuclideanSpace ℝ (Fin (n + 1))) :
    (fun q : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin 1) ↦
      Ψ (euclideanHalfSpaceBoundaryParam n q.1) (q.2 0)) =
      (fun q : EuclideanSpace ℝ (Fin (n + 1)) × ℝ ↦ Ψ q.1 q.2) ∘
        (euclideanHalfSpaceBoundaryParam n).prodMap (EuclideanSpace.proj (0 : Fin 1)) := by
  funext q
  simp only [comp_apply, ContinuousLinearMap.coe_prodMap', Prod.map_apply', PiLp.proj_apply]

/-- **The derivative of the flow-out of the coordinate hyperplane.** Let `Ψ z t` be differentiable
at `(L y₀, 0)`, `L` the parametrization of the coordinate hyperplane, with `Ψ z 0 = z`, and let the
velocity `w₀` of `t ↦ Ψ (L y₀) t` at `t = 0` have positive zeroth coordinate. Then the flow-out
`(y, s) ↦ Ψ (L y) (s 0)` of the hyperplane has injective derivative at `(y₀, 0)`: the derivative
is `(y', s') ↦ L y' + s' 0 • w₀`, and `w₀` is transverse to the hyperplane. -/
private theorem injective_fderiv_flowOut_euclideanHalfSpaceBoundaryParam
    {Ψ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ → EuclideanSpace ℝ (Fin (n + 1))}
    {w₀ : EuclideanSpace ℝ (Fin (n + 1))} {y₀ : EuclideanSpace ℝ (Fin n)}
    (hΨ : DifferentiableAt ℝ (fun q : EuclideanSpace ℝ (Fin (n + 1)) × ℝ ↦ Ψ q.1 q.2)
      (euclideanHalfSpaceBoundaryParam n y₀, 0))
    (hΨ0 : ∀ z, Ψ z 0 = z) (hw : HasDerivAt (Ψ (euclideanHalfSpaceBoundaryParam n y₀)) w₀ 0)
    (hw0 : 0 < w₀ 0) :
    Injective (fderiv ℝ (fun q : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin 1) ↦
      Ψ (euclideanHalfSpaceBoundaryParam n q.1) (q.2 0)) (y₀, 0)) := by
  let L := euclideanHalfSpaceBoundaryParam n
  -- The flow-out factors through `π : (y, s) ↦ (L y, s 0)`.
  let π := L.prodMap (EuclideanSpace.proj (0 : Fin 1))
  have hπ (q : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin 1)) : π q = (L q.1, q.2 0) := by
    simp only [π, ContinuousLinearMap.coe_prodMap', Prod.map_apply', PiLp.proj_apply]
  set D := fderiv ℝ (fun q : EuclideanSpace ℝ (Fin (n + 1)) × ℝ ↦ Ψ q.1 q.2) (L y₀, 0)
  -- `D` is the identity on the first factor, since `Ψ z 0 = z`, and sends `(0, 1)` to `w₀`.
  have hDinl (z : EuclideanSpace ℝ (Fin (n + 1))) : D (z, 0) = z := by
    have h := hΨ.hasFDerivAt.comp (L y₀) (hasFDerivAt_prodMk_left (𝕜 := ℝ) (L y₀) (0 : ℝ))
    have hid : (fun q : EuclideanSpace ℝ (Fin (n + 1)) × ℝ ↦ Ψ q.1 q.2) ∘ (fun z ↦ (z, 0)) =
        id := funext hΨ0
    rw [hid] at h
    exact (DFunLike.congr_fun ((hasFDerivAt_id (L y₀)).unique h) z).symm
  have hDinr : D (0, 1) = w₀ :=
    (hΨ.hasFDerivAt.comp (0 : ℝ) (hasFDerivAt_prodMk_right (𝕜 := ℝ) (L y₀) (0 : ℝ))).hasDerivAt
      |>.unique hw
  have hDπ (q : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin 1)) :
      D (π q) = L q.1 + q.2 0 • w₀ := by
    rw [hπ, show (L q.1, q.2 0) = (L q.1, (0 : ℝ)) +
      q.2 0 • ((0 : EuclideanSpace ℝ (Fin (n + 1))), (1 : ℝ)) by simp, map_add, map_smul, hDinl,
      hDinr]
  have hΨπ : HasFDerivAt (fun q : EuclideanSpace ℝ (Fin (n + 1)) × ℝ ↦ Ψ q.1 q.2) D
      (π (y₀, 0)) := by
    rw [hπ, PiLp.zero_apply]
    exact hΨ.hasFDerivAt
  have hd : HasFDerivAt (fun q : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin 1) ↦
      Ψ (L q.1) (q.2 0)) (D.comp π) (y₀, 0) := by
    rw [flowOut_euclideanHalfSpaceBoundaryParam_eq_comp]
    exact hΨπ.comp (y₀, 0) π.hasFDerivAt
  rw [hd.fderiv]
  rintro ⟨y₁, s₁⟩ ⟨y₂, s₂⟩ h
  have h₁ : L y₁ + s₁ 0 • w₀ = L y₂ + s₂ 0 • w₀ := by
    simpa only [ContinuousLinearMap.comp_apply, hDπ] using h
  -- The zeroth coordinate recovers the normal component, and `L` is injective.
  have hs : s₁ 0 = s₂ 0 := by
    have h0 := congrArg (fun z : EuclideanSpace ℝ (Fin (n + 1)) ↦ z 0) h₁
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, L,
      euclideanHalfSpaceBoundaryParam_apply_zero, zero_add] at h0
    exact mul_right_cancel₀ hw0.ne' h0
  rw [hs, add_left_inj] at h₁
  refine Prod.ext (euclideanHalfSpaceBoundaryParam_injective n h₁) ?_
  ext i
  rw [Subsingleton.elim i 0]
  exact hs

/-- The extended chart of `∂M × [0, ∞)` at `(a, t₀)` reads `(x, t) ↦ (extChartAt a x, t)`. -/
private theorem extChartAt_boundary_prod_euclideanHalfSpace_apply
    (a : ↥((𝓡∂ (n + 1)).boundary M)) (t₀ : EuclideanHalfSpace 1)
    (p : ↥((𝓡∂ (n + 1)).boundary M) × EuclideanHalfSpace 1) :
    extChartAt ((𝓡 n).prod (𝓡∂ 1)) (a, t₀) p = (extChartAt (𝓡 n) a p.1, p.2.val) := by
  simp only [extChartAt_prod, PartialEquiv.prod_coe, extChartAt_self_apply,
    modelWithCornersEuclideanHalfSpace_apply]

variable [IsManifold (𝓡∂ (n + 1)) ∞ M]

variable [T2Space M]

/-- Near `(a, 0)`, the flow-out `(x, t) ↦ Φ x t` of the boundary agrees with the chart flow `Ψ`
at `a` read back on `M`: both are integral curves of `v` from `x`. -/
private theorem eventually_flowOut_eq_extChartAt_symm (v : (x : M) → TangentSpace (𝓡∂ (n + 1)) x)
    (hv : ContMDiff (𝓡∂ (n + 1)) (𝓡∂ (n + 1)).tangent ∞
      (fun x ↦ (⟨x, v x⟩ : TangentBundle (𝓡∂ (n + 1)) M)))
    {a : ↥((𝓡∂ (n + 1)).boundary M)} {W : Set (M × ℝ)} (hW : W ∈ 𝓝 ((a : M), (0 : ℝ)))
    {Φ : M → ℝ → M}
    (hΦ : ∀ x ∈ (𝓡∂ (n + 1)).boundary M, ∀ t, (x, t) ∈ W → 0 ≤ t →
      Φ x 0 = x ∧ IsMIntegralCurveOn (Φ x) v (Icc 0 t))
    {Ψ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ → EuclideanSpace ℝ (Fin (n + 1))}
    {U : Set (EuclideanSpace ℝ (Fin (n + 1)))} (hU : U ∈ 𝓝 (extChartAt (𝓡∂ (n + 1)) (a : M) a))
    {ε : ℝ} (hε : 0 < ε) (hΨ0 : ∀ z, Ψ z 0 = z)
    (hΨcurve : ∀ z ∈ U, 0 ≤ z 0 →
      IsMIntegralCurveOn ((extChartAt (𝓡∂ (n + 1)) (a : M)).symm ∘ Ψ z) v (Ico 0 ε)) :
    ∀ᶠ p : ↥((𝓡∂ (n + 1)).boundary M) × EuclideanHalfSpace 1 in 𝓝 (a, 0),
      Φ p.1 (p.2.val 0) = (extChartAt (𝓡∂ (n + 1)) (a : M)).symm
        (Ψ (extChartAt (𝓡∂ (n + 1)) (a : M) p.1) (p.2.val 0)) := by
  let φ := extChartAt (𝓡∂ (n + 1)) (a : M)
  have hfst : Continuous fun p : ↥((𝓡∂ (n + 1)).boundary M) × EuclideanHalfSpace 1 ↦ (p.1 : M) :=
    continuous_subtypeVal.comp continuous_fst
  have hcont : ContinuousAt (fun p : ↥((𝓡∂ (n + 1)).boundary M) × EuclideanHalfSpace 1 ↦
      ((p.1 : M), p.2.val 0)) (a, 0) :=
    (hfst.prodMk ((EuclideanSpace.proj (0 : Fin 1)).continuous.comp
      (continuous_subtypeVal.comp continuous_snd))).continuousAt
  have hφc : ContinuousAt (fun p : ↥((𝓡∂ (n + 1)).boundary M) × EuclideanHalfSpace 1 ↦
      φ p.1) (a, 0) :=
    ContinuousAt.comp (f := fun p : ↥((𝓡∂ (n + 1)).boundary M) × EuclideanHalfSpace 1 ↦ (p.1 : M))
      (continuousAt_extChartAt (a : M)) hfst.continuousAt
  filter_upwards [hcont.preimage_mem_nhds (inter_mem hW (prod_mem_nhds univ_mem (Iio_mem_nhds hε))),
    hfst.continuousAt.preimage_mem_nhds (extChartAt_source_mem_nhds (I := 𝓡∂ (n + 1)) (a : M)),
    hφc.preimage_mem_nhds hU] with p hpW hpφ hpU
  obtain ⟨x, τ⟩ := p
  simp only [mem_preimage, mem_inter_iff, mem_prod, mem_univ, mem_Iio, true_and] at hpW hpφ
  have hτ : 0 ≤ τ.val 0 := τ.property
  have hφx0 : 0 ≤ φ x 0 := by
    have h := extChartAt_target_subset_range (I := 𝓡∂ (n + 1)) (a : M) (φ.map_source hpφ)
    rwa [range_modelWithCornersEuclideanHalfSpace] at h
  -- Both curves from `x` are integral curves of `v` on `[0, τ]`, hence equal there.
  obtain ⟨hΦx0, hΦx⟩ := hΦ x x.property (τ.val 0) hpW.1 hτ
  have heq := hΦx.eqOn_of_isPreconnected
    ((hΨcurve _ hpU hφx0).mono (Icc_subset_Ico_right hpW.2)) isPreconnected_Icc
    (left_mem_Icc.2 hτ) (fun s _ ↦ (hv _).of_le (by simp))
    (by rw [hΦx0, comp_apply, hΨ0, φ.left_inv hpφ])
  exact heq (right_mem_Icc.2 hτ)

/-- **The flow-out of the boundary is a local diffeomorphism.** Let `v` be a smooth vector field
on a Hausdorff manifold modeled on `𝓡∂ (n + 1)`, pointing inward at a boundary point `a`, and let
`Φ x t` be such that for every boundary point `x` and time `t ≥ 0` with `(x, t)` in a
neighbourhood `W` of `(a, 0)`, the curve `s ↦ Φ x s` starts at `x` and is an integral curve of `v`
on `[0, t]`. Then the flow-out `(x, t) ↦ Φ x t` on `∂M × [0, ∞)` is a smooth local diffeomorphism
at `(a, 0)`. -/
theorem isLocalDiffeomorphAt_flowOut_boundary (v : (x : M) → TangentSpace (𝓡∂ (n + 1)) x)
    (hv : ContMDiff (𝓡∂ (n + 1)) (𝓡∂ (n + 1)).tangent ∞
      (fun x ↦ (⟨x, v x⟩ : TangentBundle (𝓡∂ (n + 1)) M)))
    {a : ↥((𝓡∂ (n + 1)).boundary M)} (ha : IsOutwardPointing (a : M) (-v a))
    {W : Set (M × ℝ)} (hW : W ∈ 𝓝 ((a : M), (0 : ℝ))) {Φ : M → ℝ → M}
    (hΦ : ∀ x ∈ (𝓡∂ (n + 1)).boundary M, ∀ t, (x, t) ∈ W → 0 ≤ t →
      Φ x 0 = x ∧ IsMIntegralCurveOn (Φ x) v (Icc 0 t)) :
    IsLocalDiffeomorphAt ((𝓡 n).prod (𝓡∂ 1)) (𝓡∂ (n + 1)) ∞
      (fun p : ↥((𝓡∂ (n + 1)).boundary M) × EuclideanHalfSpace 1 ↦ Φ p.1 (p.2.val 0))
      (a, 0) := by
  let _ := isManifold_boundary (n := n) (k := ∞) M
  set p₀ : ↥((𝓡∂ (n + 1)).boundary M) × EuclideanHalfSpace 1 := (a, 0)
  let φ := extChartAt (𝓡∂ (n + 1)) (a : M)
  obtain ⟨Ψ, U, hU, ε, hε, hΨ, hΨ0, hmono, -, hΨcurve, w₀, hw, hw0⟩ :=
    exists_contDiffOn_chartFlow_of_isOutwardPointing_neg v hv.contMDiffOn univ_mem ha
  -- The flow-out read in charts is `(y, s) ↦ Ψ (L y) (s 0)`, for `L` the boundary
  -- parametrization: the chart flow `Ψ` composed with `π : (y, s) ↦ (L y, s 0)`.
  let L := euclideanHalfSpaceBoundaryParam n
  let π := L.prodMap (EuclideanSpace.proj (0 : Fin 1))
  have hπ (q : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin 1)) : π q = (L q.1, q.2 0) := by
    simp only [π, ContinuousLinearMap.coe_prodMap', Prod.map_apply', PiLp.proj_apply]
  have hg : ContDiffOn ℝ ∞ ((fun q : EuclideanSpace ℝ (Fin (n + 1)) × ℝ ↦ Ψ q.1 q.2) ∘ π)
      (π ⁻¹' (interior U ×ˢ Ioo (-ε) ε)) :=
    hΨ.comp π.contDiff.contDiffOn fun q hq ↦ ⟨interior_subset hq.1, hq.2⟩
  -- `(0 : EuclideanHalfSpace 1).val` is `0` by definition of its `Zero` instance.
  have hp₀ : extChartAt ((𝓡 n).prod (𝓡∂ 1)) p₀ p₀ = (extChartAt (𝓡 n) a a, 0) := by
    rw [extChartAt_boundary_prod_euclideanHalfSpace_apply]
    rfl
  have hLa : L (extChartAt (𝓡 n) a a) = φ a := boundaryParam_extChartAt (mem_extChartAt_source a)
  have hΦa : Φ (p₀.1 : M) (p₀.2.val 0) = a := (hΦ a a.property 0 (mem_of_mem_nhds hW) le_rfl).1
  refine isLocalDiffeomorphAt_of_injective_fderiv_of_mem_range_iff hg
    ((isOpen_interior.prod isOpen_Ioo).preimage π.continuous) ?_ (by simp) ?_ (by simp)
    (fun q hq ↦ ?_) ?_ ?_
  · rw [hp₀, mem_preimage, hπ, PiLp.zero_apply, hLa]
    exact ⟨mem_interior_iff_mem_nhds.2 hU, by simpa using neg_lt_zero.2 hε, by simpa using hε⟩
  · rw [hp₀, ← flowOut_euclideanHalfSpaceBoundaryParam_eq_comp]
    rw [← hLa] at hw hU
    exact injective_fderiv_flowOut_euclideanHalfSpaceBoundaryParam
      ((hΨ.contDiffAt (prod_mem_nhds hU (Ioo_mem_nhds (neg_lt_zero.2 hε) hε))).differentiableAt
        (by simp)) hΨ0 hw hw0
  · -- The zeroth coordinate of `Ψ (L y) s` has the sign of `s`.
    rw [mem_preimage, hπ, mem_prod] at hq
    have hle := (hmono (L q.1) (interior_subset hq.1)).le_iff_le ⟨neg_lt_zero.2 hε, hε⟩ hq.2
    simp only [hΨ0, euclideanHalfSpaceBoundaryParam_apply_zero, L] at hle
    simp only [range_modelWithCornersEuclideanHalfSpace, ModelWithCorners.range_prod,
      modelWithCornersSelf_coe, range_id, mem_prod, mem_univ, true_and, mem_ofPred_eq,
      comp_apply, hπ]
    exact hle
  · simp only [comp_apply, hp₀, hπ, PiLp.zero_apply, hLa, hΦa]
    exact hΨ0 _
  · simp only [hΦa]
    filter_upwards [eventually_flowOut_eq_extChartAt_symm v hv hW hΦ hU hε hΨ0 hΨcurve,
      (continuous_subtypeVal.comp continuous_fst).continuousAt.preimage_mem_nhds
        (extChartAt_source_mem_nhds (I := 𝓡∂ (n + 1)) (a : M))] with p hp hpφ
    have hxφ : p.1 ∈ (extChartAt (𝓡 n) a).source := by
      rw [extChartAt_source, boundaryChartedSpace_chartAt_source]
      rw [mem_preimage, extChartAt_source] at hpφ
      exact hpφ
    rw [hp, extChartAt_boundary_prod_euclideanHalfSpace_apply]
    simp only [comp_apply, hπ, boundaryParam_extChartAt hxφ, L]

end TauCeti
