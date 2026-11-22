/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Smooth
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
import TauCeti.Analysis.Calculus.ParametricIntegral.Segment
import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Chart
import TauCeti.Geometry.Manifold.DifferentialForm.Regularity
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# Smooth families of primitives of exact one-forms

Let `M` be a manifold and `P` a manifold of parameters, both possibly with boundary or
corners, and let `B` be a `C^r` one-form on `M × P`. For each `p ∈ P` its *slice*
`β_p = B (·, p) ((·, 0))` is the one-form on `M` obtained by feeding `B` the tangent vectors of `M`.
If every slice is exact, then the slices have primitives depending on `p` as smoothly as `B` does:
there is a `C^r` function `F` on `M × P` with `d (F (·, p)) = β_p` for every `p`, normalized by
`F (x₀, p) = 0` at a chosen base point (`TauCeti.exists_contMDiff_mvfderiv_eq_of_forall_exists`).
Two primitives of `β_p` differ by a constant on each connected component of `M`, so when `M` is
connected `F (·, p)` is the unique primitive of `β_p` vanishing at `x₀`; the content of the
theorem is its joint regularity. This is
the smooth selection of primitives along a smooth path of exact forms needed, for instance, to
produce a jointly smooth Hamiltonian `H_t` from the exact contraction forms `ι_(X_t) ω` of a
symplectic isotopy.

The proof is local in the parameter and needs no paths from the base point. Fix `x₁ ∈ M` and
`p₁ ∈ P`, and read `B` in the product chart at `(x₁, p₁)`. On the convex set `s` where a small ball
about the chart point of `x₁` meets the model range, the fundamental theorem of calculus along
segments expresses `F (x, p) - F (x₁, p)` as the integral of the chart expression of `β_p` along
the segment from the chart point of `x₁` to that of `x`
(`StarConvex.sub_eq_intervalIntegral_lineMap_apply`). This segment integral is jointly `C^r` in the
point and the parameter (`Convex.contDiffOn_intervalIntegral_lineMap_apply`). Hence, for a base
point `c`, the set of points `x₁` for which `p ↦ F (x₁, p) - F (c, p)` is `C^r` is open and closed;
it contains `c`, so it contains the connected component of `c`. Normalizing the primitives at a
chosen point of each connected component, which is constant on the preconnected neighbourhoods
of the local formula, the local formula then gives joint regularity at every point.

## Main results

* `TauCeti.exists_contMDiff_mvfderiv_eq_of_forall_exists`: a `C^r` family of exact one-forms has
  a `C^r` family of primitives vanishing at a base point.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Theorem 11.49 and Chapter 17.
* D. McDuff and D. Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford University Press,
  2017, Section 10.2 (smooth choice of Hamiltonians for a symplectic isotopy with exact contraction
  forms).
-/

public section

noncomputable section

open Set Filter Metric AffineMap
open scoped Manifold ContDiff Topology

namespace TauCeti

variable {E H M G HP P V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace HP]
  {IP : ModelWithCorners ℝ G HP} [TopologicalSpace P] [ChartedSpace HP P] [IsManifold IP ∞ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The spatial part of a one-form on `E × G`: its restriction to `E × {0}`, as a linear map on
`E`. -/
private def spatialCLM : ((E × G) [⋀^Fin 1]→L[ℝ] V) →L[ℝ] (E →L[ℝ] V) :=
  ((ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ) (E := E) (F := V)
      (0 : Fin 1)).symm.toContinuousLinearEquiv : (E [⋀^Fin 1]→L[ℝ] V) →L[ℝ] (E →L[ℝ] V)).comp
    (ContinuousAlternatingMap.compContinuousLinearMapCLM (ContinuousLinearMap.inl ℝ E G))

private theorem spatialCLM_apply (φ : (E × G) [⋀^Fin 1]→L[ℝ] V) (v : E) :
    spatialCLM φ v = φ ![(v, (0 : G))] := by
  simp [spatialCLM, ContinuousAlternatingMap.ofSubsingletonLIE_symm_apply, Function.comp_def,
    Matrix.vec_single_eq_const]

/-- The slice of `B` at `p`, read in the chart at `x₁`, is the spatial part of the chart
expression of `B` in the product chart at `(x₁, p₁)`, at the chart point of `p`. -/
private theorem spatialCLM_inChartAt_apply (B : RoughForm (I.prod IP) (M × P) V 1)
    (x₁ : M) (p₁ : P) {p : P} (hp : p ∈ (extChartAt IP p₁).source) {y : E}
    (hy : y ∈ (extChartAt I x₁).target) (v : E) :
    spatialCLM (B.inChartAt (x₁, p₁) (y, extChartAt IP p₁ p)) v =
      B ((extChartAt I x₁).symm y, p)
        ![(mfderivWithin 𝓘(ℝ, E) I (extChartAt I x₁).symm (range I) y v, (0 : G))] := by
  set c := extChartAt I x₁
  set d := extChartAt IP p₁
  -- Read the slice of `B` through the pullback along `ι x = (x, p)`: in the chart at `x₁` it is
  -- the chart expression of `B` at `(y, d p)` composed with the inclusion `v ↦ (v, 0)`.
  set ι : M → M × P := fun x ↦ (x, p)
  have hι : MDifferentiableAt I (I.prod IP) ι (c.symm y) :=
    mdifferentiableAt_id.prodMk mdifferentiableAt_const
  have hsrc : ι (c.symm y) ∈ (extChartAt (I.prod IP) (x₁, p₁)).source := by
    rw [extChartAt_prod, PartialEquiv.prod_source]
    exact ⟨c.map_target hy, hp⟩
  have hpull := RoughForm.inChartAt_mpullback_eq_compContinuousLinearMap B x₁ (x₁, p₁) hy hι hsrc
  have hpt : extChartAt (I.prod IP) (x₁, p₁) (ι (c.symm y)) = (y, d p) := by
    rw [extChartAt_prod, PartialEquiv.prod_coe]
    exact Prod.ext (c.right_inv hy) rfl
  have hfd : fderivWithin ℝ (extChartAt (I.prod IP) (x₁, p₁) ∘ ι ∘ c.symm) (range I) y =
      ContinuousLinearMap.inl ℝ E G := by
    have heq : extChartAt (I.prod IP) (x₁, p₁) ∘ ι ∘ c.symm =ᶠ[𝓝[range I] y]
        fun y' ↦ (y', d p) := by
      filter_upwards [extChartAt_target_mem_nhdsWithin_of_mem hy] with y' hy'
      simp only [Function.comp_apply, extChartAt_prod, PartialEquiv.prod_coe, ι]
      exact Prod.ext (c.right_inv hy') rfl
    rw [heq.fderivWithin_eq (by simp only [Function.comp_apply]; exact hpt)]
    exact ((hasFDerivAt_id y).prodMk (hasFDerivAt_const (d p) y)).hasFDerivWithinAt.fderivWithin
      (I.uniqueDiffOn _ (extChartAt_target_subset_range x₁ hy))
  rw [hpt, hfd] at hpull
  have hev : (mpullback I (I.prod IP) ι B).inChartAt x₁ y ![v] =
      B.inChartAt (x₁, p₁) (y, d p) ![(v, (0 : G))] := by
    rw [hpull, ContinuousAlternatingMap.compContinuousLinearMap_apply]
    congr 1
    funext i
    fin_cases i
    rfl
  rw [RoughForm.inChartAt_apply, mpullback_apply] at hev
  rw [spatialCLM_apply, ← hev]
  congr 1
  funext i
  fin_cases i
  simp only [ι, mfderiv_prod_left, Matrix.cons_val_fin_one, c, extChartAt_coe_symm]
  -- `inl w = (w, 0)`, up to the tangent-space synonyms.
  exact ContinuousLinearMap.inl_apply _

/-- In the product chart at `(x₁, p₁)`, the derivative within the model range of a primitive `f` of
the slice of `B` at `p`, read in the chart at `x₁`, is the spatial part of the chart expression of
`B` at the chart point of `p`. -/
private theorem hasFDerivWithinAt_comp_extChartAt_symm
    {B : RoughForm (I.prod IP) (M × P) V 1} {f : M → V} {p : P}
    (hf : MDifferentiable I 𝓘(ℝ, V) f)
    (hfB : ∀ (x : M) (v : E), mvfderiv I f x v = B (x, p) ![(v, (0 : G))])
    (x₁ : M) (p₁ : P) (hp : p ∈ (extChartAt IP p₁).source) {y : E}
    (hy : y ∈ (extChartAt I x₁).target) :
    HasFDerivWithinAt (f ∘ (extChartAt I x₁).symm)
      (spatialCLM (B.inChartAt (x₁, p₁) (y, extChartAt IP p₁ p))) (range I) y := by
  set c := extChartAt I x₁
  have hψ : MDifferentiableWithinAt 𝓘(ℝ, E) I c.symm (range I) y :=
    mdifferentiableWithinAt_extChartAt_symm hy
  have hu : UniqueMDiffWithinAt 𝓘(ℝ, E) (range I) y :=
    (I.uniqueDiffOn.uniqueDiffWithinAt (extChartAt_target_subset_range x₁ hy)).uniqueMDiffWithinAt
  have hd := mfderiv_comp_mfderivWithin (I := 𝓘(ℝ, E)) (I' := I) (I'' := 𝓘(ℝ, V)) y
    (hf (c.symm y)) hψ hu
  have hdiff : DifferentiableWithinAt ℝ (f ∘ c.symm) (range I) y :=
    mdifferentiableWithinAt_iff_differentiableWithinAt.mp ((hf _).comp_mdifferentiableWithinAt y hψ)
  convert hdiff.hasFDerivWithinAt using 1
  ext v
  have hchain : fderivWithin ℝ (f ∘ c.symm) (range I) y v =
      mvfderiv I f (c.symm y) (mfderivWithin 𝓘(ℝ, E) I c.symm (range I) y v) := by
    rw [mvfderiv_apply_eq_mfderiv_apply]
    -- `mfderivWithin` between normed spaces with their self models is `fderivWithin`, up to the
    -- tangent-space synonyms.
    exact DFunLike.congr_fun (mfderivWithin_eq_fderivWithin.symm.trans hd) v
  rw [hchain, spatialCLM_inChartAt_apply B x₁ p₁ hp hy]
  exact (hfB (c.symm y) (mfderivWithin 𝓘(ℝ, E) I c.symm (range I) y v)).symm

/-- The spatial part of the chart expression of a `C^r` one-form on `M × P` is `C^r` on the target
of the product chart. -/
private theorem contDiffOn_spatialCLM_inChartAt {r : ℕ∞} {B : RoughForm (I.prod IP) (M × P) V 1}
    (hB : IsSmoothForm (I.prod IP) r B) (z₀ : M × P) :
    ContDiffOn ℝ r (fun w ↦ spatialCLM (B.inChartAt z₀ w))
      (extChartAt (I.prod IP) z₀).target := by
  have : IsManifold (I.prod IP) ((r : WithTop ℕ∞) + 1) (M × P) :=
    IsManifold.of_le (n := ∞) (by exact_mod_cast le_top)
  refine (spatialCLM (E := E) (G := G) (V := V)).contDiff.comp_contDiffOn fun w hw ↦ ?_
  exact (B.contDiffWithinAt_inChartAt_of_contDiffWithinAt_inChartAt hw
    (mem_extChartAt_source _) (hB.contDiffWithinAt_inChartAt_self _)).mono
      (extChartAt_target_subset_range z₀)

/-- **The local formula** at `(x₁, p₁)`, for a ball of radius `ε` about the chart point of `x₁`
whose intersection with the model range lies in the chart target: for parameters near `p₁`, the
difference `f p x - f p x₁` of the primitives of the slices of `B` is a `C^r` function of
`(x, p)`, namely the segment integral of the chart expression of the slice from the chart point of
`x₁` to that of `x`. -/
private theorem exists_eq_sub_of_slices_of_ball {r : ℕ∞} {B : RoughForm (I.prod IP) (M × P) V 1}
    (hB : IsSmoothForm (I.prod IP) r B) [CompleteSpace V] {f : P → M → V}
    (hf : ∀ p, MDifferentiable I 𝓘(ℝ, V) (f p))
    (hfB : ∀ (p : P) (x : M) (v : E), mvfderiv I (f p) x v = B (x, p) ![(v, (0 : G))])
    {x₁ : M} {ε : ℝ} (hε : 0 < ε)
    (hεs : ball (extChartAt I x₁ x₁) ε ∩ range I ⊆ (extChartAt I x₁).target) (p₁ : P) :
    ∃ W : Set P, IsOpen W ∧ p₁ ∈ W ∧ ∃ g : M × P → V, ContMDiffOn (I.prod IP) 𝓘(ℝ, V) r g
      (((extChartAt I x₁).source ∩ extChartAt I x₁ ⁻¹' ball (extChartAt I x₁ x₁) ε) ×ˢ W) ∧
        ∀ x ∈ (extChartAt I x₁).source ∩ extChartAt I x₁ ⁻¹' ball (extChartAt I x₁ x₁) ε,
          ∀ p ∈ W, f p x - f p x₁ = g (x, p) := by
  set c := extChartAt I x₁
  set d := extChartAt IP p₁
  obtain ⟨δ, hδ, hδs⟩ :=
    Metric.mem_nhdsWithin_iff.mp (extChartAt_target_mem_nhdsWithin (I := IP) p₁)
  set s : Set E := ball (c x₁) ε ∩ range I
  set u : Set G := ball (d p₁) δ ∩ range IP
  have hs : Convex ℝ s := (convex_ball _ _).inter I.convex_range
  have hu : Convex ℝ u := (convex_ball _ _).inter IP.convex_range
  have hcs : c x₁ ∈ s := ⟨mem_ball_self hε, extChartAt_target_subset_range x₁
    (mem_extChartAt_target x₁)⟩
  set D : E × G → E →L[ℝ] V := fun w ↦ spatialCLM (B.inChartAt (x₁, p₁) w)
  have hD : ContDiffOn ℝ r D (s ×ˢ u) := (contDiffOn_spatialCLM_inChartAt hB (x₁, p₁)).mono <| by
    rw [extChartAt_prod, PartialEquiv.prod_target]
    exact prod_mono hεs hδs
  set Q : E × G → V := fun w ↦ ∫ τ in (0 : ℝ)..1, D (lineMap (c x₁) w.1 τ, w.2) (w.1 - c x₁)
  have hsu : UniqueDiffOn ℝ s := by
    simpa only [s, inter_comm] using I.uniqueDiffOn.inter (isOpen_ball (x := c x₁) (ε := ε))
  have huu : UniqueDiffOn ℝ u := by
    simpa only [u, inter_comm] using IP.uniqueDiffOn.inter (isOpen_ball (x := d p₁) (ε := δ))
  have hQ : ContDiffOn ℝ r Q (s ×ˢ u) :=
    hs.contDiffOn_intervalIntegral_lineMap_apply hsu hcs hu huu hD
  refine ⟨d.source ∩ d ⁻¹' ball (d p₁) δ, isOpen_extChartAt_preimage' p₁ isOpen_ball,
    ⟨mem_extChartAt_source p₁, mem_ball_self hδ⟩, fun z ↦ Q (extChartAt (I.prod IP) (x₁, p₁) z),
    ?_, fun x hx p hp ↦ ?_⟩
  · -- `Q` read through the product chart is `C^r`.
    refine hQ.contMDiffOn.comp ((contMDiffOn_extChartAt (n := r)).mono fun z hz ↦ ?_)
      fun z hz ↦ ?_
    · rw [← extChartAt_source (I := I.prod IP), extChartAt_prod, PartialEquiv.prod_source]
      exact ⟨hz.1.1, hz.2.1⟩
    · rw [extChartAt_prod, PartialEquiv.prod_coe]
      exact ⟨⟨hz.1.2, extChartAt_target_subset_range x₁ (c.map_source hz.1.1)⟩,
        ⟨hz.2.2, extChartAt_target_subset_range p₁ (d.map_source hz.2.1)⟩⟩
  · -- The fundamental theorem of calculus along the segment from `c x₁` to `c x`.
    have hdp : d p ∈ u := ⟨hp.2, extChartAt_target_subset_range p₁ (d.map_source hp.1)⟩
    have hDp : ContinuousOn (fun y ↦ D (y, d p)) s :=
      hD.continuousOn.comp (continuousOn_id.prodMk continuousOn_const) fun y hy ↦ ⟨hy, hdp⟩
    have hg (y : E) (hy : y ∈ s) : HasFDerivWithinAt (f p ∘ c.symm) (D (y, d p)) s y :=
      (hasFDerivWithinAt_comp_extChartAt_symm (hf p) (hfB p) x₁ p₁ hp.1 (hεs hy)).mono
        inter_subset_right
    have h := hs.starConvex hcs |>.sub_eq_intervalIntegral_lineMap_apply hDp hg
      ⟨hx.2, extChartAt_target_subset_range x₁ (c.map_source hx.1)⟩
    simp only [Function.comp_apply, c.left_inv hx.1, c.left_inv (mem_extChartAt_source x₁)] at h
    rw [h, extChartAt_prod, PartialEquiv.prod_coe]

/-- **The local formula.** Near `x₁`, uniformly for parameters near any `p₁`, the difference
`f p x - f p x₁` of the primitives of the slices of `B` is a `C^r` function of `(x, p)`. The
neighbourhood of `x₁` is preconnected and does not depend on `p₁`. -/
private theorem exists_eq_sub_of_slices {r : ℕ∞} {B : RoughForm (I.prod IP) (M × P) V 1}
    (hB : IsSmoothForm (I.prod IP) r B) [CompleteSpace V] {f : P → M → V}
    (hf : ∀ p, MDifferentiable I 𝓘(ℝ, V) (f p))
    (hfB : ∀ (p : P) (x : M) (v : E), mvfderiv I (f p) x v = B (x, p) ![(v, (0 : G))])
    (x₁ : M) :
    ∃ U : Set M, IsOpen U ∧ IsPreconnected U ∧ x₁ ∈ U ∧ ∀ p₁ : P, ∃ W : Set P, IsOpen W ∧
      p₁ ∈ W ∧ ∃ g : M × P → V, ContMDiffOn (I.prod IP) 𝓘(ℝ, V) r g (U ×ˢ W) ∧
        ∀ x ∈ U, ∀ p ∈ W, f p x - f p x₁ = g (x, p) := by
  obtain ⟨ε, hε, hεs⟩ :=
    Metric.mem_nhdsWithin_iff.mp (extChartAt_target_mem_nhdsWithin (I := I) x₁)
  set c := extChartAt I x₁
  -- The neighbourhood is the image under the inverse chart of the convex set `ball ∩ range I`.
  have himage : c.source ∩ c ⁻¹' ball (c x₁) ε = c.symm '' (ball (c x₁) ε ∩ range I) := by
    have hsub : c.source ∩ c ⁻¹' ball (c x₁) ε ⊆ c ⁻¹' range I := fun x hx ↦
      extChartAt_target_subset_range x₁ (c.map_source hx.1)
    rw [c.symm_image_eq_source_inter_preimage hεs, Set.preimage_inter, ← Set.inter_assoc,
      Set.inter_eq_left.2 hsub]
  refine ⟨_, isOpen_extChartAt_preimage' x₁ isOpen_ball, ?_,
    ⟨mem_extChartAt_source x₁, mem_ball_self hε⟩, exists_eq_sub_of_slices_of_ball hB hf hfB hε hεs⟩
  rw [himage]
  exact ((convex_ball _ _).inter I.convex_range).isPreconnected.image _
    ((continuousOn_extChartAt_symm x₁).mono hεs)

omit [IsManifold I ∞ M] [IsManifold IP ∞ P] in
/-- If the local formula at `x₁` holds on an open set `U` containing `x`, then the primitive at
`x₁` is a `C^r` function of the parameter exactly when the primitive at `x` is. -/
private theorem contMDiff_sub_iff_of_eq_sub {r : ℕ∞} {f : P → M → V} {x₀ x₁ x : M} {U : Set M}
    (hUo : IsOpen U) (hx : x ∈ U) (hU : ∀ p₁ : P, ∃ W : Set P, IsOpen W ∧ p₁ ∈ W ∧
      ∃ g : M × P → V, ContMDiffOn (I.prod IP) 𝓘(ℝ, V) r g (U ×ˢ W) ∧
        ∀ x ∈ U, ∀ p ∈ W, f p x - f p x₁ = g (x, p)) :
    ContMDiff IP 𝓘(ℝ, V) r (fun p ↦ f p x₁ - f p x₀) ↔
      ContMDiff IP 𝓘(ℝ, V) r (fun p ↦ f p x - f p x₀) := by
  have key (p₁ : P) : ∃ g : P → V, ContMDiffAt IP 𝓘(ℝ, V) r g p₁ ∧
      ∀ᶠ p in 𝓝 p₁, f p x - f p x₀ = (f p x₁ - f p x₀) + g p := by
    obtain ⟨W, hW, hpW, g, hg, hfg⟩ := hU p₁
    refine ⟨fun p ↦ g (x, p), ?_, ?_⟩
    · exact (hg.contMDiffAt (prod_mem_nhds (hUo.mem_nhds hx) (hW.mem_nhds hpW))).comp p₁
        (contMDiffAt_const.prodMk contMDiffAt_id)
    · filter_upwards [hW.mem_nhds hpW] with p hp
      rw [← hfg x hx p hp]
      abel
  refine ⟨fun h₁ p₁ ↦ ?_, fun h p₁ ↦ ?_⟩
  · obtain ⟨g, hg, hfg⟩ := key p₁
    exact ((h₁ p₁).add hg).congr_of_eventuallyEq hfg
  · obtain ⟨g, hg, hfg⟩ := key p₁
    refine ((h p₁).sub hg).congr_of_eventuallyEq ?_
    filter_upwards [hfg] with p hp
    rw [hp]
    abel

/-- On the connected component of a base point `c`, the primitive at `x` differs from the
primitive at `c` by a `C^r` function of the parameter: the points where this holds form an open
and closed set containing `c`. -/
private theorem contMDiff_sub_of_mem_connectedComponent {r : ℕ∞}
    {B : RoughForm (I.prod IP) (M × P) V 1} (hB : IsSmoothForm (I.prod IP) r B) [CompleteSpace V]
    {f : P → M → V} (hf : ∀ p, MDifferentiable I 𝓘(ℝ, V) (f p))
    (hfB : ∀ (p : P) (x : M) (v : E), mvfderiv I (f p) x v = B (x, p) ![(v, (0 : G))])
    {c x : M} (hx : x ∈ connectedComponent c) :
    ContMDiff IP 𝓘(ℝ, V) r fun p ↦ f p x - f p c := by
  have hloc := exists_eq_sub_of_slices hB hf hfB
  set S : Set M := {x | ContMDiff IP 𝓘(ℝ, V) r fun p ↦ f p x - f p c}
  have hclopen : IsClopen S := by
    refine ⟨isOpen_compl_iff.mp (isOpen_iff_forall_mem_open.mpr fun x₁ hx₁ ↦ ?_),
      isOpen_iff_forall_mem_open.mpr fun x₁ hx₁ ↦ ?_⟩
    · obtain ⟨U, hUo, -, hx₁U, hU⟩ := hloc x₁
      exact ⟨U, fun x hx hxS ↦ hx₁ ((contMDiff_sub_iff_of_eq_sub hUo hx hU).mpr hxS), hUo, hx₁U⟩
    · obtain ⟨U, hUo, -, hx₁U, hU⟩ := hloc x₁
      exact ⟨U, fun x hx ↦ (contMDiff_sub_iff_of_eq_sub hUo hx hU).mp hx₁, hUo, hx₁U⟩
  have hc : c ∈ S := by
    simp only [S, Set.mem_ofPred_eq, sub_self]
    exact contMDiff_const
  exact hclopen.connectedComponent_subset hc hx

/-- **Primitives normalized on each connected component.** There is a `C^r` function on `M × P`
which near every point of each slice `M × {p}` differs from the primitive `f p` by a constant: the
primitives normalized at a chosen base point of each connected component. -/
private theorem exists_contMDiff_eventuallyEq_sub {r : ℕ∞}
    {B : RoughForm (I.prod IP) (M × P) V 1} (hB : IsSmoothForm (I.prod IP) r B) [CompleteSpace V]
    {f : P → M → V} (hf : ∀ p, MDifferentiable I 𝓘(ℝ, V) (f p))
    (hfB : ∀ (p : P) (x : M) (v : E), mvfderiv I (f p) x v = B (x, p) ![(v, (0 : G))]) :
    ∃ F : M × P → V, ContMDiff (I.prod IP) 𝓘(ℝ, V) r F ∧
      ∀ (p : P) (x : M), ∃ c : V, (fun y ↦ F (y, p)) =ᶠ[𝓝 x] fun y ↦ f p y - c := by
  have hloc := exists_eq_sub_of_slices hB hf hfB
  -- A base point of each connected component, depending only on the component.
  let rep : M → M := fun x ↦ Quotient.out (ConnectedComponents.mk x)
  have hrep_eq {x y : M} (h : y ∈ connectedComponent x) : rep y = rep x :=
    congrArg Quotient.out (ConnectedComponents.coe_eq_coe'.2 h)
  have hmem_rep (x : M) : x ∈ connectedComponent (rep x) :=
    ConnectedComponents.coe_eq_coe'.1 (Quotient.out_eq _).symm
  refine ⟨fun z ↦ f z.2 z.1 - f z.2 (rep z.1), ?_, fun p x ↦ ⟨f p (rep x), ?_⟩⟩
  · -- Near `(x₁, p₁)` the base point is constant, and the normalized primitive is its value at
    -- `x₁` plus the local formula.
    rintro ⟨x₁, p₁⟩
    obtain ⟨U, hUo, hUc, hx₁U, hU⟩ := hloc x₁
    obtain ⟨W, hW, hpW, g, hg, hfg⟩ := hU p₁
    have hmem : U ×ˢ W ∈ 𝓝 (x₁, p₁) := prod_mem_nhds (hUo.mem_nhds hx₁U) (hW.mem_nhds hpW)
    have h₁ : ContMDiffAt (I.prod IP) 𝓘(ℝ, V) r
        (fun z : M × P ↦ f z.2 x₁ - f z.2 (rep x₁)) (x₁, p₁) :=
      (contMDiff_sub_of_mem_connectedComponent hB hf hfB (hmem_rep x₁) p₁).comp (x₁, p₁)
        contMDiffAt_snd
    refine (h₁.add (hg.contMDiffAt hmem)).congr_of_eventuallyEq ?_
    filter_upwards [hmem] with ⟨x, p⟩ hz
    rw [Pi.add_apply, ← hfg x hz.1 p hz.2, hrep_eq (hUc.subset_connectedComponent hx₁U hz.1)]
    abel
  · obtain ⟨U, hUo, hUc, hxU, -⟩ := hloc x
    filter_upwards [hUo.mem_nhds hxU] with y hy
    rw [hrep_eq (hUc.subset_connectedComponent hxU hy)]

/-- **Smooth families of primitives.** Let `B` be a `C^r` one-form on `M × P` such that for every
parameter `p` the slice `v ↦ B (x, p) (v, 0)` is the differential of a differentiable function on
`M`. Then there is a `C^r` function `F` on `M × P` whose restriction to every slice `M × {p}` is a
primitive of the slice of `B`, normalized by `F (x₀, p) = 0`. The manifold `M` need not be
connected. Both manifolds may have boundary or corners, and the coefficient space is any Banach
space. -/
theorem exists_contMDiff_mvfderiv_eq_of_forall_exists [CompleteSpace V]
    {r : ℕ∞} {B : RoughForm (I.prod IP) (M × P) V 1} (hB : IsSmoothForm (I.prod IP) r B)
    (hexact : ∀ p : P, ∃ f : M → V, MDifferentiable I 𝓘(ℝ, V) f ∧
      ∀ (x : M) (v : E), mvfderiv I f x v = B (x, p) ![(v, (0 : G))])
    (x₀ : M) :
    ∃ F : M × P → V, ContMDiff (I.prod IP) 𝓘(ℝ, V) r F ∧ (∀ p, F (x₀, p) = 0) ∧
      ∀ (p : P) (x : M) (v : E),
        mvfderiv I (fun y ↦ F (y, p)) x v = B (x, p) ![(v, (0 : G))] := by
  choose f hf hfB using hexact
  obtain ⟨F₀, hF₀, hF₀f⟩ := exists_contMDiff_eventuallyEq_sub hB hf hfB
  -- Subtracting the value at `x₀`, a function of the parameter alone, keeps each slice a
  -- primitive.
  refine ⟨fun z ↦ F₀ z - F₀ (x₀, z.2),
    hF₀.sub (hF₀.comp (contMDiff_const.prodMk contMDiff_snd)), fun p ↦ sub_self _,
    fun p x v ↦ ?_⟩
  obtain ⟨c, hc⟩ := hF₀f p x
  have heq : (fun y ↦ F₀ (y, p) - F₀ (x₀, p)) =ᶠ[𝓝 x] fun y ↦ f p y + -(c + F₀ (x₀, p)) := by
    filter_upwards [hc] with y hy
    rw [hy]
    abel
  refine (DFunLike.congr_fun heq.mvfderiv_eq v).trans ?_
  rw [mvfderiv_add_const]
  exact hfB p x v

end TauCeti
