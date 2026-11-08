/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Immersion.Differential
public import TauCeti.Geometry.Manifold.IsManifold.InteriorChart
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
import Mathlib.Analysis.LocallyConvex.SeparatingDual
import TauCeti.Geometry.Manifold.Boundary.Basic
import TauCeti.Geometry.Manifold.MFDeriv.ModelChart

/-!
# Immersions at interior points of manifolds with boundary

`ContMDiffOn.isImmersionAt_of_hasLeftInverse_mfderiv` turns a split differential into the
immersion normal form for maps between *boundaryless* manifolds. This file proves the same
criterion for manifolds modelled on arbitrary models with corners, at a point `x` which is an
interior point of the source and whose image `f x` is an interior point of the target.

The immersion normal form of a map `f` asks for charts of the maximal atlases in which `f` reads
as `u ↦ L (u, 0)` for a continuous linear equivalence `L`. Read in the preferred extended charts,
`f` becomes a map `g` between open subsets of the model vector spaces, and the boundaryless
criterion gives `g` a normal form in charts of these vector spaces. Those charts need not take
values in the ranges of the models, so they cannot directly be pulled back to charts of the
manifolds. They are first recentred: an affine change of the source chart moves the point to a
prescribed nonzero point `a`, and an affine change of the target chart, whose linear part is a
continuous linear automorphism carrying `L (a, 0)` to a prescribed nonzero point `b`, keeps the
normal form linear. Choosing `a` and `b` in the interiors of the ranges of the models, and
shrinking the charts there, the charts become charts of the manifolds through the inverse of
`ModelWithCorners.interiorChart`
(`OpenPartialHomeomorph.trans_interiorChart_symm_mem_maximalAtlas`).

The hypothesis that the source model space is nontrivial cannot be dropped: a map from a point
to an interior point of a half-space has no normal form in this sense, since the normal form
sends the image point to `L (0, 0) = 0`, a boundary point of the half-space.

## Main results

* `Manifold.IsImmersionAtOfComplement.of_writtenInExtChartAt_of_isInteriorPoint`: a normal form
  of `f` read in the preferred extended charts is a normal form of `f`, with the same complement,
  at an interior point mapped to an interior point.
* `ContMDiffOn.isImmersionAt_of_hasLeftInverse_mfderiv_of_isInteriorPoint`: a `C^n` map, `1 ≤ n`,
  whose manifold derivative at an interior point has a continuous linear left inverse is an
  immersion there, provided the image point is interior.
* `ContMDiffOn.isImmersionAt_of_injective_mfderiv_of_isInteriorPoint`: the same with an injective
  manifold derivative, for a finite-dimensional target model.

## References

* M. Hirsch, *Differential Topology*, Springer GTM 33 (1976), Chapter 1, §3 (the local immersion
  theorem) and §4 (manifolds with boundary).
-/

public section

noncomputable section

open Set Function Topology Manifold
open scoped ContDiff Manifold

namespace Manifold.IsImmersionAtOfComplement

variable {𝕜 : Type*} [RCLike 𝕜]
  {E E' F : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {n : ℕ∞ω} {g : E → E'} {p : E}

/-- **Recentring an immersion normal form between vector spaces.** If `g` has an immersion normal
form at `p`, then for all nonzero `a` and `b` there are charts `σ` near `p` and `ρ` near `g p` of
the maximal atlases, sending `p` to `a` and `g p` to `b`, in which `g` reads as `u ↦ L (u, 0)` for a
continuous linear equivalence `L`. The charts are those of the normal form followed by affine
changes of coordinates. -/
private theorem exists_affine_recentred_charts
    (h : IsImmersionAtOfComplement F 𝓘(𝕜, E) 𝓘(𝕜, E') n g p) {a : E} {b : E'} (ha : a ≠ 0)
    (hb : b ≠ 0) :
    ∃ (σ : OpenPartialHomeomorph E E) (ρ : OpenPartialHomeomorph E' E') (L : (E × F) ≃L[𝕜] E'),
      σ ∈ IsManifold.maximalAtlas 𝓘(𝕜, E) n E ∧ ρ ∈ IsManifold.maximalAtlas 𝓘(𝕜, E') n E' ∧
      p ∈ σ.source ∧ σ p = a ∧ g p ∈ ρ.source ∧ ρ (g p) = b ∧
      ∀ u ∈ σ.target, ρ (g (σ.symm u)) = L (u, 0) := by
  set σ₀ := h.domChart
  set ρ₀ := h.codChart
  have hp : p ∈ σ₀.source := h.mem_domChart_source
  -- The normal form, read without the trivial extensions by the identity model.
  have hW : ∀ u ∈ σ₀.target, ρ₀ (g (σ₀.symm u)) = h.equiv (u, 0) := fun u hu ↦ by
    simpa using h.writtenInCharts (by simpa using hu)
  have hgp : ρ₀ (g p) = h.equiv (σ₀ p, 0) := by
    simpa [σ₀.left_inv hp] using hW _ (σ₀.map_source hp)
  -- The linear part of the recentred target chart carries `L (a, 0)` to `b`.
  obtain ⟨A, hA⟩ : ∃ A : E' ≃L[𝕜] E', A (h.equiv (a, 0)) = b :=
    SeparatingDual.exists_continuousLinearEquiv_apply_eq
      (by rw [Ne, ← map_zero h.equiv, h.equiv.injective.eq_iff]; simp [ha]) hb
  -- The affine changes of coordinates `u ↦ u + (a - σ₀ p)` and `v ↦ A (v - ρ₀ (g p)) + b`.
  let T₁ : E ≃ₜ E := Homeomorph.addRight (a - σ₀ p)
  let T₂ : E' ≃ₜ E' :=
    (Homeomorph.addRight (-ρ₀ (g p))).trans (A.toHomeomorph.trans (Homeomorph.addRight b))
  have hT₂ (v : E') : T₂ v = A (v - ρ₀ (g p)) + b := by simp [T₂, sub_eq_add_neg]
  have hT₂symm : ⇑T₂.symm = fun v ↦ A.symm (v - b) + ρ₀ (g p) := funext fun v ↦ by
    apply T₂.injective
    rw [Homeomorph.apply_symm_apply, hT₂]
    simp
  have hT₁ : ContDiff 𝕜 n T₁ := by
    simp only [T₁, Homeomorph.coe_addRight]
    fun_prop
  have hT₁' : ContDiff 𝕜 n T₁.symm := by
    simp only [T₁, Homeomorph.addRight_symm, Homeomorph.coe_addRight]
    fun_prop
  have hT₂' : ContDiff 𝕜 n T₂ := by
    rw [funext hT₂]
    fun_prop
  have hT₂'' : ContDiff 𝕜 n T₂.symm := by
    rw [hT₂symm]
    fun_prop
  refine ⟨σ₀.transHomeomorph T₁, ρ₀.transHomeomorph T₂, h.equiv.trans A,
    by rw [OpenPartialHomeomorph.transHomeomorph_eq_trans]
       exact TauCeti.trans_mem_maximalAtlas_of_contDiffAt h.domChart_mem_maximalAtlas
         (fun _ _ ↦ hT₁.contDiffAt) (fun _ _ ↦ hT₁'.contDiffAt),
    by rw [OpenPartialHomeomorph.transHomeomorph_eq_trans]
       exact TauCeti.trans_mem_maximalAtlas_of_contDiffAt h.codChart_mem_maximalAtlas
         (fun _ _ ↦ hT₂'.contDiffAt) (fun _ _ ↦ hT₂''.contDiffAt),
    hp, by simp [T₁],
    h.source_subset_preimage_source hp, by simp [hT₂], fun u hu ↦ ?_⟩
  -- In the new charts, the normal form of `g` is recentred by linearity.
  have hu' : u + (σ₀ p - a) ∈ σ₀.target := by
    simpa [T₁, Homeomorph.addRight_symm] using hu
  have key : ((u + (σ₀ p - a), 0) : E × F) - (σ₀ p, 0) = (u, 0) - (a, 0) := by
    simp only [Prod.mk_sub_mk, sub_zero, Prod.mk.injEq, and_true]
    abel
  simp only [OpenPartialHomeomorph.transHomeomorph_apply,
    OpenPartialHomeomorph.transHomeomorph_symm_apply, Function.comp_apply, T₁,
    Homeomorph.addRight_symm, Homeomorph.coe_addRight, neg_sub]
  rw [hT₂, hW _ hu', hgp, ← map_sub, key, map_sub, map_sub, hA]
  simp

/-- **Recentring and shrinking an immersion normal form between vector spaces.** If `g` has an
immersion normal form at `p`, then for all nonzero `a` and `b` and open neighbourhoods `U` of `a`
and `V` of `b` there are charts `σ` near `p` and `ρ` near `g p` of the maximal atlases, sending `p`
to `a` and `g p` to `b`, in which `g` reads as `u ↦ L (u, 0)` for a continuous linear equivalence
`L`, and such that `σ` takes values in `U` and `L (u, 0) ∈ V` for every `u` in the target of `σ`. -/
private theorem exists_recentred_charts
    (h : IsImmersionAtOfComplement F 𝓘(𝕜, E) 𝓘(𝕜, E') n g p) {a : E} {b : E'} (ha : a ≠ 0)
    (hb : b ≠ 0) {U : Set E} {V : Set E'} (hU : IsOpen U) (haU : a ∈ U) (hV : IsOpen V)
    (hbV : b ∈ V) :
    ∃ (σ : OpenPartialHomeomorph E E) (ρ : OpenPartialHomeomorph E' E') (L : (E × F) ≃L[𝕜] E'),
      σ ∈ IsManifold.maximalAtlas 𝓘(𝕜, E) n E ∧ ρ ∈ IsManifold.maximalAtlas 𝓘(𝕜, E') n E' ∧
      p ∈ σ.source ∧ σ p = a ∧ g p ∈ ρ.source ∧ ρ (g p) = b ∧
      σ.target ⊆ U ∧ (∀ u ∈ σ.target, L (u, 0) ∈ V) ∧
      ∀ u ∈ σ.target, ρ (g (σ.symm u)) = L (u, 0) := by
  obtain ⟨σ₁, ρ, L, hσ₁, hρ, hp, hσ₁p, hgρ, hρg, hW⟩ := h.exists_affine_recentred_charts ha hb
  -- Shrink the source chart to the points it sends to `U` with normal form in `V`.
  let O := U ∩ (fun u ↦ L (u, 0)) ⁻¹' V
  have hO : IsOpen O := hU.inter (hV.preimage (by fun_prop))
  have hLa : L (a, 0) = b := by
    rw [← hρg, ← hσ₁p, ← hW _ (σ₁.map_source hp), σ₁.left_inv hp]
  have hpO : σ₁ p ∈ O := ⟨hσ₁p ▸ haU, by simpa [O, hσ₁p, hLa] using hbV⟩
  have hσt : (σ₁.restr (σ₁.source ∩ σ₁ ⁻¹' O)).target ⊆ σ₁.target ∩ O := fun u hu ↦ by
    rw [σ₁.restr_target, (σ₁.isOpen_inter_preimage hO).interior_eq] at hu
    exact ⟨hu.1, by simpa [σ₁.right_inv hu.1] using hu.2.2⟩
  refine ⟨σ₁.restr (σ₁.source ∩ σ₁ ⁻¹' O), ρ, L,
    restr_mem_maximalAtlas _ hσ₁ (σ₁.isOpen_inter_preimage hO), hρ, ?_, hσ₁p, hgρ, hρg,
    fun u hu ↦ (hσt hu).2.1, fun u hu ↦ (hσt hu).2.2, fun u hu ↦ by simpa using hW u (hσt hu).1⟩
  rw [σ₁.restr_source' _ (σ₁.isOpen_inter_preimage hO)]
  exact ⟨hp, hp, hpO⟩

end Manifold.IsImmersionAtOfComplement

namespace Manifold.IsImmersionAtOfComplement

variable {𝕜 : Type*} [RCLike 𝕜]
  {E E' F H G M N : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [TopologicalSpace H] [TopologicalSpace G]
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 E' G}
  [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N] [ChartedSpace G N]
  {n : ℕ∞ω} {f : M → N} {x : M}

/-- **Immersion normal forms at interior points.** Let `x` be an interior point of `M` which `f`
maps to an interior point of `N`, and let `f` be continuous at `x`. An immersion normal form of `f`
read in the preferred extended charts, a map between open subsets of the model vector spaces, is
an immersion normal form of `f` itself, with the same complement. The models may have boundary or
corners; the source model space must be nontrivial. -/
theorem of_writtenInExtChartAt_of_isInteriorPoint [Nontrivial E] [IsManifold I n M]
    [IsManifold J n N] (hf : ContinuousAt f x) (hx : I.IsInteriorPoint x)
    (hfx : J.IsInteriorPoint (f x))
    (h : IsImmersionAtOfComplement F 𝓘(𝕜, E) 𝓘(𝕜, E') n (writtenInExtChartAt I J x f)
      (extChartAt I x x)) :
    IsImmersionAtOfComplement F I J n f x := by
  set g := writtenInExtChartAt I J x f
  set p := extChartAt I x x
  have hgp : g p = extChartAt J (f x) (f x) := by simp [g, p, writtenInExtChartAt]
  -- Recentre the normal form of `g` at nonzero points of the interiors of the model ranges.
  have : Nontrivial E' := h.equiv.symm.toEquiv.nontrivial
  have := Module.punctured_nhds_neBot 𝕜 E p
  have := Module.punctured_nhds_neBot 𝕜 E' (extChartAt J (f x) (f x))
  obtain ⟨a, ha, ha0⟩ :=
    (infinite_of_mem_nhds p (isOpen_interior.mem_nhds hx)).nontrivial.exists_ne 0
  obtain ⟨b, hb, hb0⟩ :=
    (infinite_of_mem_nhds _ (isOpen_interior.mem_nhds hfx)).nontrivial.exists_ne 0
  obtain ⟨σ, ρ, L, hσ, hρ, hpσ, hσp, hgρ, hρg, hσI, hLJ, hW⟩ :=
    h.exists_recentred_charts ha0 hb0 isOpen_interior ha isOpen_interior hb
  -- The preferred extended charts on interior points, followed by the recentred charts, are
  -- charts of the maximal atlases once read back through the interior charts of the models.
  set Φ := TauCeti.extChartPartialDiffeomorph I n x
  set Ψ := TauCeti.extChartPartialDiffeomorph J n (f x)
  set e := Φ.toOpenPartialHomeomorph.trans σ
  set e' := Ψ.toOpenPartialHomeomorph.trans ρ
  have hΦx : x ∈ Φ.source := (TauCeti.mem_extChartPartialDiffeomorph_source I n x).2 hx
  have hΨx : f x ∈ Ψ.source := (TauCeti.mem_extChartPartialDiffeomorph_source J n (f x)).2 hfx
  have hΦ : ⇑Φ.toOpenPartialHomeomorph = extChartAt I x :=
    TauCeti.coe_extChartPartialDiffeomorph I n x
  have hΦsymm : ⇑Φ.toOpenPartialHomeomorph.symm = (extChartAt I x).symm :=
    funext (TauCeti.extChartPartialDiffeomorph_symm_apply I n x)
  have hΨ : ⇑Ψ.toOpenPartialHomeomorph = extChartAt J (f x) :=
    TauCeti.coe_extChartPartialDiffeomorph J n (f x)
  -- In the recentred charts, `f` reads as `g` read in `σ` and `ρ`.
  have he'f (u : E) : e' (f (e.symm u)) = ρ (g (σ.symm u)) := by
    simp only [e, e', OpenPartialHomeomorph.coe_trans, OpenPartialHomeomorph.coe_trans_symm,
      Function.comp_apply, hΦsymm, hΨ, g, writtenInExtChartAt]
  have hex : e x = a := by
    simp only [e, OpenPartialHomeomorph.coe_trans, Function.comp_apply, hΦ, hσp, p]
  have he'x : e' (f x) = b := by
    simp only [e', OpenPartialHomeomorph.coe_trans, Function.comp_apply, hΨ, ← hgp, hρg]
  refine mk_of_continuousAt hf L (e.trans I.interiorChart.symm) (e'.trans J.interiorChart.symm)
    ⟨⟨hΦx, by rw [mem_preimage, OpenPartialHomeomorph.symm_symm, hΦ]; exact hpσ⟩,
      by rwa [mem_preimage, OpenPartialHomeomorph.symm_symm, hex,
        OpenPartialHomeomorph.symm_source, ModelWithCorners.interiorChart_target]⟩
    ⟨⟨hΨx, by rw [mem_preimage, OpenPartialHomeomorph.symm_symm, hΨ, ← hgp]; exact hgρ⟩,
      by rwa [mem_preimage, OpenPartialHomeomorph.symm_symm, he'x,
        OpenPartialHomeomorph.symm_source, ModelWithCorners.interiorChart_target]⟩
    (Φ.trans_trans_interiorChart_symm_mem_maximalAtlas hσ)
    (Ψ.trans_trans_interiorChart_symm_mem_maximalAtlas hρ) fun v hv ↦ ?_
  -- A point of the chart target is `I z` for a point `I z` of the target of `σ`, where `f` reads as
  -- the normal form of `g`.
  rw [OpenPartialHomeomorph.extend_target'] at hv
  obtain ⟨z, hz, rfl⟩ := hv
  have hzσ : I z ∈ σ.target := by
    have hze : I z ∈ e.target := by
      simpa only [mem_preimage, OpenPartialHomeomorph.symm_symm,
        ModelWithCorners.interiorChart_coe] using hz.2
    exact hze.1
  simp only [Function.comp_apply, OpenPartialHomeomorph.extend_coe_symm,
    OpenPartialHomeomorph.extend_coe, ModelWithCorners.left_inv,
    OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm, OpenPartialHomeomorph.coe_trans,
    OpenPartialHomeomorph.symm_symm, ModelWithCorners.interiorChart_coe,
    ModelWithCorners.interiorChart_coe_symm]
  rw [he'f, hW _ hzσ, J.right_inv (interior_subset (hLJ _ hzσ))]

end Manifold.IsImmersionAtOfComplement

section Criterion

variable {𝕜 : Type*} [RCLike 𝕜]
  {E E' H G M N : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] [CompleteSpace E']
  [TopologicalSpace H] [TopologicalSpace G]
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 E' G}
  [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N] [ChartedSpace G N]
  {n : ℕ∞ω} [Nontrivial E] [IsManifold I n M] [IsManifold J n N]
  {f : M → N} {s : Set M} {x : M}

/-- A `C^n` map on an open set, `1 ≤ n`, is an immersion at an interior point `x` mapped to an
interior point, as soon as its manifold derivative at `x` admits a continuous linear left inverse.
The models may have boundary or corners; the source model space must be nontrivial. -/
theorem ContMDiffOn.isImmersionAt_of_hasLeftInverse_mfderiv_of_isInteriorPoint
    (hf : ContMDiffOn I J n f s) (hs : IsOpen s) (hx : x ∈ s) (hn : 1 ≤ n)
    (hxi : I.IsInteriorPoint x) (hfxi : J.IsInteriorPoint (f x))
    (hdf : (mfderiv I J f x).HasLeftInverse) :
    IsImmersionAt I J n f x := by
  have hn0 : n ≠ 0 := by rintro rfl; simp at hn
  have hfx : ContMDiffAt I J n f x := hf.contMDiffAt (hs.mem_nhds hx)
  -- Read `f` in the preferred extended charts, on an open set of interior chart coordinates.
  let t := interior (extChartAt I x).target ∩
    (extChartAt I x).symm ⁻¹' (s ∩ f ⁻¹' (extChartAt J (f x)).source)
  have ht : IsOpen t :=
    ((continuousOn_extChartAt_symm x).mono interior_subset).isOpen_inter_preimage isOpen_interior
      (hf.continuousOn.isOpen_inter_preimage hs (isOpen_extChartAt_source (f x)))
  have hpt : extChartAt I x x ∈ t := by
    refine ⟨mem_interior_iff_mem_nhds.2
      (TauCeti.ModelWithCorners.extChartAt_target_mem_nhds_of_isInteriorPoint hn0 x
        (mem_extChartAt_source x) hxi), ?_⟩
    simp [hx]
  have hft : ContDiffOn 𝕜 n (writtenInExtChartAt I J x f) t :=
    ((contMDiffOn_iff.mp hf).2 x (f x)).mono fun _ hu ↦ ⟨interior_subset hu.1, hu.2⟩
  -- At an interior point the manifold derivative is the derivative in charts.
  have hderiv : fderiv 𝕜 (writtenInExtChartAt I J x f) (extChartAt I x x) = mfderiv I J f x := by
    rw [(hfx.mdifferentiableAt hn0).mfderiv_abuse,
      fderivWithin_of_mem_nhds (mem_interior_iff_mem_nhds.1 hxi)]
  have h := (hft.isImmersionAt_of_hasLeftInverse ht hpt hn (hderiv ▸ hdf))
  exact (IsImmersionAtOfComplement.of_writtenInExtChartAt_of_isInteriorPoint hfx.continuousAt hxi
    hfxi h.isImmersionAtOfComplement_complement).isImmersionAt

omit [CompleteSpace E'] in
/-- For a finite-dimensional target model, a `C^n` map on an open set, `1 ≤ n`, is an immersion at
an interior point `x` mapped to an interior point, as soon as its manifold derivative at `x` is
injective. -/
theorem ContMDiffOn.isImmersionAt_of_injective_mfderiv_of_isInteriorPoint
    [FiniteDimensional 𝕜 E'] (hf : ContMDiffOn I J n f s) (hs : IsOpen s) (hx : x ∈ s)
    (hn : 1 ≤ n) (hxi : I.IsInteriorPoint x) (hfxi : J.IsInteriorPoint (f x))
    (hdf : Injective (mfderiv I J f x)) :
    IsImmersionAt I J n f x := by
  have : FiniteDimensional 𝕜 E :=
    FiniteDimensional.of_injective (mfderiv I J f x).toLinearMap hdf
  have : CompleteSpace E' := FiniteDimensional.complete 𝕜 E'
  exact hf.isImmersionAt_of_hasLeftInverse_mfderiv_of_isInteriorPoint hs hx hn hxi hfxi
    (ContinuousLinearMap.HasLeftInverse.of_injective_of_finiteDimensional hdf)

end Criterion
