/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Boundary.DefiningFunction.Basic
import Mathlib.Geometry.Manifold.Algebra.LieGroup
import Mathlib.Geometry.Manifold.Algebra.Structures
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import TauCeti.Analysis.Calculus.Hadamard.HalfSpace

/-!
# Comparing two boundary defining functions

Let `ρ` and `ρ'` be boundary defining functions on the same open set `U` of a smooth manifold `M`
modelled on the half-space `𝓡∂ (n + 1)` (`TauCeti.IsBoundaryDefiningFunctionOn`). Then
`ρ' = u ρ` on `U` for a function `u` that is smooth and positive on `U`, and at each boundary point
`q ∈ U` the differentials satisfy `dρ'_q = u(q) dρ_q`
(`TauCeti.IsBoundaryDefiningFunctionOn.exists_eq_mul`). For a Riemannian metric this says
`u = |dρ'| / |dρ|` on the boundary
(`TauCeti.IsBoundaryDefiningFunctionOn.exists_eq_mul_norm_div_norm`, in
`Riemannian/InwardUnitNormal.lean`). Global boundary defining functions are the case `U = univ`.

On the interior `u = ρ' / ρ`. Near each point `q₀ ∈ U`, Hadamard division in the preferred
half-space chart at `q₀` (`TauCeti.exists_contDiffOn_eq_smul_of_eq_zero`) writes `ρ = x⁰ G` and
`ρ' = x⁰ G'` for the normal coordinate `x⁰` of the chart and functions `G`, `G'` smooth near `q₀`,
and then `u = G' / G` near `q₀`. At a boundary point `q` the product rule gives `dρ_q = G(q) dx⁰_q`,
so `G(q) ≠ 0`, and `u(q) = dρ'_q(v) / dρ_q(v)` for every inward vector `v`, which is positive by the
sign test.

## Main declarations

* `TauCeti.IsBoundaryDefiningFunctionOn.exists_eq_mul`: the comparison of two boundary defining
  functions on the same open set.

## References

* G. Uhlmann, A. Vasy, *The inverse problem for the local geodesic ray transform*, Invent. Math.
  205 (2016), 83–120, Section 1 (the boundary defining function `ρ`).
-/

public section

noncomputable section

open Set Filter Function
open scoped Manifold Topology ContDiff

namespace TauCeti

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace (n + 1)) M]
  [IsManifold (𝓡∂ (n + 1)) ∞ M]

namespace IsBoundaryDefiningFunctionOn

variable {ρ ρ' : M → ℝ} {U : Set M}

/-- **Hadamard division in a half-space chart.** Near a point `q₀` of its domain, a boundary
defining function is the product of the normal coordinate `x⁰` of the preferred chart at `q₀` with
a smooth function. -/
private theorem exists_eq_normal_mul (hρ : IsBoundaryDefiningFunctionOn n ρ U) {q₀ : M}
    (hq₀U : q₀ ∈ U) :
    ∃ G : M → ℝ, ∃ N, IsOpen N ∧ q₀ ∈ N ∧
      N ⊆ U ∩ (chartAt (EuclideanHalfSpace (n + 1)) q₀).source ∧
      ContMDiffOn (𝓡∂ (n + 1)) 𝓘(ℝ) ∞ G N ∧
      ∀ y ∈ N, ρ y = (chartAt (EuclideanHalfSpace (n + 1)) q₀ y).val 0 * G y := by
  set e := chartAt (EuclideanHalfSpace (n + 1)) q₀
  set φ := extChartAt (𝓡∂ (n + 1)) q₀
  let ℓ : EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] ℝ := EuclideanSpace.proj 0
  have hφ (y : M) : ℓ (φ y) = (e y).val 0 := by simp [ℓ, φ, e]
  have hrange : range (𝓡∂ (n + 1)) = {y | 0 ≤ ℓ y} := by
    rw [range_modelWithCornersEuclideanHalfSpace]
    ext y
    simp [ℓ]
  -- `ρ` read in the chart is smooth on the chart target over `U`.
  set T := φ.target ∩ φ.symm ⁻¹' U
  have hT : T ∈ 𝓝[range (𝓡∂ (n + 1))] φ q₀ := by
    refine inter_mem (extChartAt_target_mem_nhdsWithin q₀) ?_
    have h := extChartAt_preimage_mem_nhdsWithin (I := 𝓡∂ (n + 1)) (s := univ) (x := q₀) (t := U)
      (by rw [nhdsWithin_univ]; exact hρ.isOpen.mem_nhds hq₀U)
    rwa [preimage_univ, univ_inter] at h
  have hf : ContDiffOn ℝ ∞ (ρ ∘ φ.symm) T := contMDiffOn_iff_contDiffOn.1 <|
    hρ.contMDiffOn.comp ((contMDiffOn_extChartAt_symm q₀).mono inter_subset_left) fun _ hy ↦ hy.2
  obtain ⟨s, hs, hqs, hsT⟩ := mem_nhdsWithin.1 hT
  have hsT' : {y | 0 ≤ ℓ y} ∩ s ⊆ T := fun y hy ↦ hsT ⟨hy.2, hrange ▸ hy.1⟩
  -- `ρ` read in the chart vanishes on the boundary hyperplane.
  have h0 (y) (hy : y ∈ s) (hy0 : ℓ y = 0) : (ρ ∘ φ.symm) y = 0 := by
    have hyT : y ∈ T := hsT' ⟨hy0.ge, hy⟩
    have hsrc : φ.symm y ∈ e.source := by
      simpa [φ, e, extChartAt_source (I := 𝓡∂ (n + 1))] using φ.map_target hyT.1
    refine hρ.eq_zero _ hyT.2 ((ModelWithCorners.mem_boundary_euclideanHalfSpace_iff hsrc).mpr ?_)
    rw [← hφ, φ.right_inv hyT.1, hy0]
  obtain ⟨g, t, ht, hqt, hg, hfg⟩ :=
    exists_contDiffOn_eq_smul_of_eq_zero (k := ⊤) (hs.mem_nhds hqs)
      (by simpa using hf.mono hsT') h0
  have hsrc : φ.source = e.source := extChartAt_source (I := 𝓡∂ (n + 1)) q₀
  have hH {y : M} (hy : y ∈ φ.source) : φ y ∈ {y | 0 ≤ ℓ y} :=
    hrange ▸ extChartAt_target_subset_range q₀ (φ.map_source hy)
  refine ⟨g ∘ φ, (φ.source ∩ φ ⁻¹' t) ∩ U,
    ((continuousOn_extChartAt q₀).isOpen_inter_preimage (isOpen_extChartAt_source q₀) ht).inter
      hρ.isOpen, ⟨⟨mem_extChartAt_source q₀, hqt⟩, hq₀U⟩,
    fun y hy ↦ ⟨hy.2, hsrc ▸ hy.1.1⟩, ?_, fun y hy ↦ ?_⟩
  · refine hg.contMDiffOn.comp ((contMDiffOn_extChartAt (n := ∞)).mono
      fun y hy ↦ hsrc ▸ hy.1.1) fun y hy ↦ ⟨hH hy.1.1, hy.1.2⟩
  · have h := hfg (φ y) ⟨hH hy.1.1, hy.1.2⟩
    rw [comp_apply, φ.left_inv hy.1.1, hφ, smul_eq_mul] at h
    exact h

variable (n) in
/-- The inward vector `e₀` of the preferred chart at `x`, as a tangent vector at `x`. -/
private def inwardBasisVector (x : M) : TangentSpace (𝓡∂ (n + 1)) x :=
  EuclideanSpace.single 0 1

variable (n) in
/-- The ratio `ρ' / ρ` of two functions on the interior, extended to the boundary by the ratio
`dρ'(e₀) / dρ(e₀)` of their derivatives along the inward vector `e₀` of the preferred chart. -/
private def ratio (ρ ρ' : M → ℝ) (x : M) : ℝ := by
  classical
  exact if x ∈ (𝓡∂ (n + 1)).interior M then ρ' x / ρ x else
    mvfderiv (𝓡∂ (n + 1)) ρ' x (inwardBasisVector n x) /
      mvfderiv (𝓡∂ (n + 1)) ρ x (inwardBasisVector n x)

omit [IsManifold (𝓡∂ (n + 1)) ∞ M] in
private theorem ratio_of_mem_interior {x : M} (hx : x ∈ (𝓡∂ (n + 1)).interior M) :
    ratio n ρ ρ' x = ρ' x / ρ x := by
  simp [ratio, hx]

omit [IsManifold (𝓡∂ (n + 1)) ∞ M] in
private theorem ratio_of_mem_boundary {x : M} (hx : x ∈ (𝓡∂ (n + 1)).boundary M) :
    ratio n ρ ρ' x =
      mvfderiv (𝓡∂ (n + 1)) ρ' x (inwardBasisVector n x) /
        mvfderiv (𝓡∂ (n + 1)) ρ x (inwardBasisVector n x) := by
  have hnot : x ∉ (𝓡∂ (n + 1)).interior M :=
    fun hi ↦ (ModelWithCorners.disjoint_interior_boundary (I := 𝓡∂ (n + 1))).ne_of_mem hi hx rfl
  simp [ratio, hnot]

omit [IsManifold (𝓡∂ (n + 1)) ∞ M] in
/-- At a boundary point of its domain, a boundary defining function has positive derivative along
the inward vector `e₀` of the preferred chart. -/
private theorem mvfderiv_inwardBasisVector_pos (hρ : IsBoundaryDefiningFunctionOn n ρ U) {x : M}
    (hxU : x ∈ U) (hx : x ∈ (𝓡∂ (n + 1)).boundary M) :
    0 < mvfderiv (𝓡∂ (n + 1)) ρ x (inwardBasisVector n x) :=
  (hρ.isOutwardPointing_neg_iff_mvfderiv_pos hxU hx _).mp (isOutwardPointing_neg_single_zero hx)

/-- Near a point `x` of its domain where `σ = x⁰ H`, for the normal coordinate `x⁰` of the
preferred chart at `x` and `H` smooth, the differential of `σ` at a boundary point `y` is
`H(y) dx⁰_y`. -/
private theorem mvfderiv_eq_smul_normal {x : M} {σ H : M → ℝ} {V : Set M} (hV : IsOpen V)
    (hH : ContMDiffOn (𝓡∂ (n + 1)) 𝓘(ℝ) ∞ H V)
    (hσH : ∀ y ∈ V, σ y = (chartAt (EuclideanHalfSpace (n + 1)) x y).val 0 * H y) {y : M}
    (hyV : y ∈ V) (hye : y ∈ (chartAt (EuclideanHalfSpace (n + 1)) x).source)
    (hy : y ∈ (𝓡∂ (n + 1)).boundary M) :
    mvfderiv (𝓡∂ (n + 1)) σ y =
      H y • mvfderiv (𝓡∂ (n + 1)) (fun z ↦ (chartAt (EuclideanHalfSpace (n + 1)) x z).val 0) y := by
  have hnc := isBoundaryDefiningFunctionOn_normal
    (IsManifold.chart_mem_maximalAtlas (I := 𝓡∂ (n + 1)) (n := ∞) x)
  have heq : σ =ᶠ[𝓝 y] (fun z ↦ (chartAt (EuclideanHalfSpace (n + 1)) x z).val 0) * H := by
    filter_upwards [hV.mem_nhds hyV] with z hz
    exact hσH z hz
  rw [heq.mvfderiv_eq, mvfderiv_mul (hnc.mdifferentiableAt hye)
    ((hH.contMDiffAt (hV.mem_nhds hyV)).mdifferentiableAt (by simp)),
    hnc.eq_zero y hye hy, zero_smul, zero_add]

/-- Near a point `x` of `U`, the ratio of two boundary defining functions on `U` is the smooth
function `G' / G`, for their factors `ρ = x⁰ G` and `ρ' = x⁰ G'` in the preferred chart at `x`. -/
private theorem contMDiffAt_ratio (hρ : IsBoundaryDefiningFunctionOn n ρ U)
    (hρ' : IsBoundaryDefiningFunctionOn n ρ' U) {x : M} (hx : x ∈ U) :
    ContMDiffAt (𝓡∂ (n + 1)) 𝓘(ℝ) ∞ (ratio n ρ ρ') x := by
  obtain ⟨G, N, hN, hxN, hNU, hG, hρG⟩ := hρ.exists_eq_normal_mul hx
  obtain ⟨G', N', hN', hxN', -, hG', hρG'⟩ := hρ'.exists_eq_normal_mul hx
  set e := chartAt (EuclideanHalfSpace (n + 1)) x
  have hnc := isBoundaryDefiningFunctionOn_normal
    (IsManifold.chart_mem_maximalAtlas (I := 𝓡∂ (n + 1)) (n := ∞) x)
  have hkey (y : M) (hy : y ∈ N ∩ N') : G y ≠ 0 ∧ ratio n ρ ρ' y = (G' / G) y := by
    have hyU : y ∈ U := (hNU hy.1).1
    have hye : y ∈ e.source := (hNU hy.1).2
    rcases (𝓡∂ (n + 1)).isInteriorPoint_or_isBoundaryPoint y with hyi | hyb
    · -- On the interior, `ρ' / ρ = (x⁰ G') / (x⁰ G)`.
      have hpos := hρ.pos y hyU hyi
      rw [hρG y hy.1] at hpos
      refine ⟨right_ne_zero_of_mul hpos.ne', ?_⟩
      rw [ratio_of_mem_interior hyi, hρG y hy.1, hρG' y hy.2,
        mul_div_mul_left _ _ (left_ne_zero_of_mul hpos.ne'), Pi.div_apply]
    · -- On the boundary, `dρ = G dx⁰` and `dρ' = G' dx⁰`.
      have hd := mvfderiv_eq_smul_normal hN hG hρG hy.1 hye hyb
      have hd' := mvfderiv_eq_smul_normal hN' hG' hρG' hy.2 hye hyb
      have hwρ := hρ.mvfderiv_inwardBasisVector_pos hyU hyb
      have hwnc := hnc.mvfderiv_inwardBasisVector_pos hye hyb
      rw [hd, smul_apply, smul_eq_mul] at hwρ
      refine ⟨left_ne_zero_of_mul hwρ.ne', ?_⟩
      -- `ratio` divides the derivatives on the inward basis vector; the `•` there is on the
      -- tangent space `ℝ`, i.e. multiplication.
      rw [ratio_of_mem_boundary hyb, hd, hd', smul_apply, smul_apply]
      exact mul_div_mul_right (G' y) (G y) hwnc.ne'
  have hd : ContMDiffOn (𝓡∂ (n + 1)) 𝓘(ℝ) ∞ (G' / G) (N ∩ N') :=
    (hG'.mono inter_subset_right).div₀ (hG.mono inter_subset_left) fun y hy ↦ (hkey y hy).1
  refine (hd.contMDiffAt ((hN.inter hN').mem_nhds ⟨hxN, hxN'⟩)).congr_of_eventuallyEq ?_
  filter_upwards [(hN.inter hN').mem_nhds ⟨hxN, hxN'⟩] with y hy
  exact (hkey y hy).2

/-- **Comparison of boundary defining functions.** Two boundary defining functions `ρ`, `ρ'` on the
same open set `U` satisfy `ρ' = u ρ` on `U` for a function `u` smooth and positive on `U`, and
`dρ'_q = u(q) dρ_q` at the boundary points `q ∈ U`. -/
theorem exists_eq_mul (hρ : IsBoundaryDefiningFunctionOn n ρ U)
    (hρ' : IsBoundaryDefiningFunctionOn n ρ' U) :
    ∃ u : M → ℝ, ContMDiffOn (𝓡∂ (n + 1)) 𝓘(ℝ) ∞ u U ∧ (∀ x ∈ U, 0 < u x) ∧
      (∀ x ∈ U, ρ' x = u x * ρ x) ∧
      ∀ q ∈ U, q ∈ (𝓡∂ (n + 1)).boundary M →
        mvfderiv (𝓡∂ (n + 1)) ρ' q = u q • mvfderiv (𝓡∂ (n + 1)) ρ q := by
  have hmul (x : M) (hx : x ∈ U) : ρ' x = ratio n ρ ρ' x * ρ x := by
    rcases (𝓡∂ (n + 1)).isInteriorPoint_or_isBoundaryPoint x with hi | hb
    · rw [ratio_of_mem_interior hi, div_mul_cancel₀ _ (hρ.pos x hx hi).ne']
    · rw [hρ.eq_zero x hx hb, hρ'.eq_zero x hx hb, mul_zero]
  have hsmooth : ContMDiffOn (𝓡∂ (n + 1)) 𝓘(ℝ) ∞ (ratio n ρ ρ') U :=
    fun x hx ↦ (contMDiffAt_ratio hρ hρ' hx).contMDiffWithinAt
  refine ⟨ratio n ρ ρ', hsmooth, fun x hx ↦ ?_, hmul, fun q hqU hq ↦ ?_⟩
  · rcases (𝓡∂ (n + 1)).isInteriorPoint_or_isBoundaryPoint x with hi | hb
    · rw [ratio_of_mem_interior hi]
      exact div_pos (hρ'.pos x hx hi) (hρ.pos x hx hi)
    · rw [ratio_of_mem_boundary hb]
      exact div_pos (hρ'.mvfderiv_inwardBasisVector_pos hx hb)
        (hρ.mvfderiv_inwardBasisVector_pos hx hb)
  · -- Differentiate `ρ' = u ρ` at `q`, where `ρ` vanishes.
    have heq : ρ' =ᶠ[𝓝 q] ratio n ρ ρ' * ρ := by
      filter_upwards [hρ.isOpen.mem_nhds hqU] with y hy
      exact hmul y hy
    rw [heq.mvfderiv_eq, mvfderiv_mul
      ((hsmooth.contMDiffAt (hρ.isOpen.mem_nhds hqU)).mdifferentiableAt (by simp))
      (hρ.mdifferentiableAt hqU), hρ.eq_zero q hqU hq, zero_smul, add_zero]

end IsBoundaryDefiningFunctionOn

end TauCeti
