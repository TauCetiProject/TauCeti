/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.RegularValue.Rank
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
import TauCeti.Analysis.Calculus.ConstantRank

/-!
# Constant rank coordinates on manifolds

A map of locally constant rank from a finite-dimensional boundaryless real or complex manifold
to a boundaryless Banach manifold is linear in suitable smooth local coordinates. The linear map
can be taken to be the manifold derivative at the centre. Choosing bases adapted to its kernel
and image gives the usual normal form `(u, v) ↦ (u, 0)`.

`ContMDiffOn.exists_openPartialHomeomorph_comp_eq_mfderiv_comp` supplies these coordinates,
including their smooth inverses, on an open neighbourhood where the rank does not exceed the
rank at the centre. `ContMDiffOn.exists_openPartialHomeomorph_apply_eq_iff_mem_ker` identifies
the level set through the centre with the kernel of the derivative in these coordinates.
These local descriptions are the input for constructing constant-rank level submanifolds.
Neither the source nor the target manifold needs to be Hausdorff or second-countable.
The normal-form equation uses `tangentSpaceCastModel` to identify the derivative's tangent fibres
with the coordinate model spaces; it does not rely on implicit type-synonym conversions.

The construction transports `ContDiffOn.exists_openPartialHomeomorph_comp_eq_fderiv_comp`
through extended charts, using `TauCeti.mfderivRank_eq_finrank_range_fderivWithin` to transfer
the rank hypothesis.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, second edition, Springer GTM 218 (2013),
  Theorem 4.12 (the rank theorem).
-/

public section

open Set Filter Manifold
open scoped Topology ContDiff

variable {𝕜 E F H G M N : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]
  [TopologicalSpace H] [TopologicalSpace G]
  {I : ModelWithCorners 𝕜 E H} [I.Boundaryless]
  {J : ModelWithCorners 𝕜 F G} [J.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N] [ChartedSpace G N]
  {n : ℕ∞ω} [IsManifold I n M] [IsManifold J n N]
  {f : M → N} {U : Set M} {x : M}

/-- **The manifold constant rank theorem.** A `C^n` map, `1 ≤ n`, whose rank on an open
neighbourhood does not exceed its rank at the centre is its derivative in suitable `C^n` local
coordinates centred at zero. The coordinate neighbourhood lies inside the prescribed open set.
No separation or countability hypotheses on the manifolds are required. -/
theorem ContMDiffOn.exists_openPartialHomeomorph_comp_eq_mfderiv_comp
    (hf : ContMDiffOn I J n f U) (hU : IsOpen U) (hx : x ∈ U) (hn : 1 ≤ n)
    (hrank : ∀ y ∈ U, TauCeti.mfderivRank I J f y ≤ TauCeti.mfderivRank I J f x) :
    ∃ (φ : OpenPartialHomeomorph M E) (ψ : OpenPartialHomeomorph N F),
      x ∈ φ.source ∧ φ.source ⊆ U ∧ φ x = 0 ∧
      ContMDiffOn I 𝓘(𝕜, E) n φ φ.source ∧
      ContMDiffOn 𝓘(𝕜, E) I n φ.symm φ.target ∧
      ψ (f x) = 0 ∧ ContMDiffOn J 𝓘(𝕜, F) n ψ ψ.source ∧
      ContMDiffOn 𝓘(𝕜, F) J n ψ.symm ψ.target ∧
      MapsTo f φ.source ψ.source ∧
      ∀ y ∈ φ.source, ψ (f y) = tangentSpaceCastModel J (f x)
        (mfderiv I J f x ((tangentSpaceCastModel I x).symm (φ y))) := by
  have hn0 : n ≠ 0 := ne_of_gt (zero_lt_one.trans_le hn)
  have : IsManifold I 1 M := .of_le hn
  have : IsManifold J 1 N := .of_le hn
  let e₀ := TauCeti.extChartPartialDiffeomorph I n x
  let c₀ := TauCeti.extChartPartialDiffeomorph J n (f x)
  let e := e₀.toOpenPartialHomeomorph
  let c := c₀.toOpenPartialHomeomorph
  have he : (e : M → E) = extChartAt I x :=
    TauCeti.coe_extChartPartialDiffeomorph I n x
  have hc : (c : N → F) = extChartAt J (f x) :=
    TauCeti.coe_extChartPartialDiffeomorph J n (f x)
  have hei : (e.symm : E → M) = (extChartAt I x).symm := by
    funext z
    exact TauCeti.extChartPartialDiffeomorph_symm_apply I n x z
  have hxe : x ∈ e.source := (TauCeti.mem_extChartPartialDiffeomorph_source I n x).mpr
    BoundarylessManifold.isInteriorPoint
  have hfc : f x ∈ c.source := (TauCeti.mem_extChartPartialDiffeomorph_source J n (f x)).mpr
    BoundarylessManifold.isInteriorPoint
  let g := c ∘ f ∘ e.symm
  have hg : g = extChartAt J (f x) ∘ f ∘ (extChartAt I x).symm := by
    dsimp only [g]
    rw [hc, hei]
  let s := e.target ∩ e.symm ⁻¹' (U ∩ f ⁻¹' c.source)
  have hs : IsOpen s := e.continuousOn_symm.isOpen_inter_preimage e.open_target
    (hf.continuousOn.isOpen_inter_preimage hU c.open_source)
  have hxs : e x ∈ s := ⟨e.map_source hxe, by
    simpa only [mem_preimage, mem_inter_iff, e.left_inv hxe] using And.intro hx hfc⟩
  have hgs : ContDiffOn 𝕜 n g s := by
    exact contMDiffOn_iff_contDiffOn.mp (c₀.contMDiffOn.comp
      (hf.comp (e₀.symm.contMDiffOn.mono (inter_subset_left : s ⊆ e.target))
        (fun y (hy : y ∈ s) ↦ hy.2.1)) (fun y (hy : y ∈ s) ↦ hy.2.2))
  -- At every point of `s`, the preferred extended charts compute the same rank.
  have hrg (z : E) (hz : z ∈ s) :
      Module.finrank 𝕜 (LinearMap.range (fderiv 𝕜 g z).toLinearMap) =
        TauCeti.mfderivRank I J f (e.symm z) := by
    have hez : e.symm z ∈ (chartAt H x).source := by
      have h := e.map_target hz.1
      have h' := (TauCeti.extChartPartialDiffeomorph_source I n x ▸ h).1
      rw [extChartAt_source] at h'
      exact h'
    have hcz : f (e.symm z) ∈ (chartAt G (f x)).source := by
      have h' := (TauCeti.extChartPartialDiffeomorph_source J n (f x) ▸ hz.2.2).1
      rw [extChartAt_source] at h'
      exact h'
    have h := TauCeti.mfderivRank_eq_finrank_range_fderivWithin
      ((hf.contMDiffAt (hU.mem_nhds hz.2.1)).mdifferentiableAt hn0) hez hcz
    rw [I.range_eq_univ, fderivWithin_univ] at h
    have hz' : extChartAt I x (e.symm z) = z := by
      rw [← he]
      exact e.right_inv hz.1
    rw [hz'] at h
    rw [hg]
    exact h.symm
  have hD : fderiv 𝕜 g (e x) = (tangentSpaceCastModel J (f x)).toContinuousLinearMap ∘L
      mfderiv I J f x ∘L (tangentSpaceCastModel I x).symm.toContinuousLinearMap := by
    rw [((hf.contMDiffAt (hU.mem_nhds hx)).mdifferentiableAt hn0).mfderiv_abuse,
      I.range_eq_univ, fderivWithin_univ, hg, he]
    -- The canonical tangent/model identifications are the identity on underlying vectors.
    rfl
  obtain ⟨Φ, Ψ, hxΦ, hΦs, hΦx, -, hΦ, hΦi, hΨx, -, hΨ, hΨi, hmap, hlin⟩ :=
    hgs.exists_openPartialHomeomorph_comp_eq_fderiv_comp hs hxs hn (fun z hz ↦ by
      rw [hrg z hz, hrg (e x) hxs, e.left_inv hxe]
      exact hrank _ hz.2.1)
  -- Restrict the target coordinates to the original chart. The source chart already lands
  -- in it because `s` was chosen to impose that condition.
  let φ := e.trans Φ
  let ψ := c.trans Ψ
  have hgx : g (e x) = c (f x) := by simp only [g, Function.comp_apply, e.left_inv hxe]
  have hsource (y : M) (hy : y ∈ φ.source) : e.symm (e y) = y := e.left_inv hy.1
  have hφU : φ.source ⊆ U := fun y hy ↦ by
    have h := (hΦs hy.2).2.1
    simpa only [OpenPartialHomeomorph.symm_symm, hsource y hy] using h
  have hmaps : MapsTo f φ.source ψ.source := by
    intro y hy
    have hc' := (hΦs hy.2).2.2
    simp only [OpenPartialHomeomorph.symm_symm, hsource y hy, mem_preimage] at hc'
    refine ⟨hc', ?_⟩
    have hg' : g (e y) = c (f y) := by
      simp only [g, Function.comp_apply, hsource y hy]
    simpa only [OpenPartialHomeomorph.symm_symm, mem_preimage, hg'] using hmap hy.2
  refine ⟨φ, ψ, ⟨hxe, hxΦ⟩, hφU, hΦx,
    hΦ.contMDiffOn.comp (e₀.contMDiffOn.mono inter_subset_left) inter_subset_right,
    (e₀.symm.contMDiffOn.comp (hΦi.contMDiffOn.mono inter_subset_left) inter_subset_right),
    by simpa only [ψ, OpenPartialHomeomorph.coe_trans, Function.comp_apply, hgx] using hΨx,
    hΨ.contMDiffOn.comp (c₀.contMDiffOn.mono inter_subset_left) inter_subset_right,
    (c₀.symm.contMDiffOn.comp (hΨi.contMDiffOn.mono inter_subset_left) inter_subset_right),
    hmaps, fun y hy ↦ ?_⟩
  have h := hlin (e y) hy.2
  rw [hD] at h
  simpa only [φ, ψ, OpenPartialHomeomorph.coe_trans, Function.comp_apply, g,
    hsource y hy, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe] using h

/-- **Constant rank level coordinates.** Near the centre, the level set of a constant-rank map
is carried by a smooth coordinate chart onto the kernel of the derivative, intersected with the
chart target. The chart and its inverse have the same regularity as the map. -/
theorem ContMDiffOn.exists_openPartialHomeomorph_apply_eq_iff_mem_ker
    (hf : ContMDiffOn I J n f U) (hU : IsOpen U) (hx : x ∈ U) (hn : 1 ≤ n)
    (hrank : ∀ y ∈ U, TauCeti.mfderivRank I J f y ≤ TauCeti.mfderivRank I J f x) :
    ∃ φ : OpenPartialHomeomorph M E,
      x ∈ φ.source ∧ φ.source ⊆ U ∧ φ x = 0 ∧
      ContMDiffOn I 𝓘(𝕜, E) n φ φ.source ∧
      ContMDiffOn 𝓘(𝕜, E) I n φ.symm φ.target ∧
      ∀ y ∈ φ.source, f y = f x ↔
        (tangentSpaceCastModel I x).symm (φ y) ∈ (mfderiv I J f x).ker := by
  obtain ⟨φ, ψ, hxφ, hφU, hφx, hφ, hφi, hψx, -, -, hmap, hlin⟩ :=
    hf.exists_openPartialHomeomorph_comp_eq_mfderiv_comp hU hx hn hrank
  refine ⟨φ, hxφ, hφU, hφx, hφ, hφi, fun y hy ↦ ?_⟩
  rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe]
  have hzero (v : TangentSpace J (f x)) :
      tangentSpaceCastModel J (f x) v = 0 ↔ v = 0 :=
    (tangentSpaceCastModel J (f x)).map_eq_zero_iff
  rw [← hzero, ← hlin y hy, ← hψx]
  exact (ψ.injOn.eq_iff (hmap hy) (hmap hxφ)).symm
