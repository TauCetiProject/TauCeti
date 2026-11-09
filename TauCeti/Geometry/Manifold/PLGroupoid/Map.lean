/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.LocalInvariantProperties
public import TauCeti.Geometry.Manifold.PLGroupoid.Basic

/-!
# Piecewise-linear maps between PL manifolds

A PL manifold is a charted space `M` over `H` with `HasGroupoid M (PLGroupoid I)`
(`TauCeti.PLGroupoid`). This file defines the maps between such spaces that are piecewise linear,
in the same way as Mathlib defines `ContMDiff` from `ContDiffWithinAt`: a map is PL at a point when
it is continuous there and, read in the preferred charts at the point and at its image and then in
the model vector spaces through `I` and `I'`, it is piecewise affine on a neighbourhood of the point
(`TauCeti.IsPLWithinAt`).

The property in the model, `TauCeti.PLWithinAtProp`, is local and invariant under the PL groupoids
in the source and in the target (`TauCeti.plWithinAtProp_localInvariantProp`), so Mathlib's theory
of local invariant properties applies. In particular, on PL manifolds the preferred charts can be
replaced by any charts of the maximal PL atlases
(`TauCeti.isPLMapAt_iff_of_mem_maximalAtlas`): being PL is a property of the PL structures, not of
the chosen atlases. Charts of the maximal PL atlas and their inverses are PL
(`TauCeti.isPLMapAt_of_mem_maximalAtlas`, `TauCeti.isPLMapAt_symm_of_mem_maximalAtlas`), so are the
identity and constant maps, PL maps compose (`TauCeti.IsPLMapAt.comp`), and between real normed
spaces with their trivial charts the PL maps are exactly the maps piecewise linear on the whole
space (`TauCeti.isPLMap_iff_isPLOn_univ`).

The construction and the proof of `TauCeti.plWithinAtProp_localInvariantProp` follow Mathlib's
`ContDiffWithinAtProp` and `contDiffWithinAt_localInvariantProp`
(`Mathlib/Geometry/Manifold/ContMDiff/Defs.lean`), by Sébastien Gouëzel and Floris van Doorn.

## Main definitions

* `TauCeti.PLWithinAtProp I I' f s x`: the map `f : H → H'` of model spaces is piecewise linear
  within `s` at `x` when read in the model vector spaces.
* `TauCeti.IsPLMapAt I I' f x`: the map `f : M → M'` is continuous at `x` and piecewise linear near
  `x` when read in charts.
* `TauCeti.IsPLMap I I' f`: the map `f : M → M'` is piecewise linear at every point.

## Main results

* `TauCeti.plWithinAtProp_localInvariantProp`: piecewise linearity in the model is a local property
  invariant under the PL groupoids.
* `TauCeti.isPLMapAt_iff`: the defining condition, in the preferred charts.
* `TauCeti.isPLMapAt_iff_of_mem_maximalAtlas`: the same condition in any charts of the maximal PL
  atlases.
* `TauCeti.isPLMapAt_of_mem_maximalAtlas`, `TauCeti.isPLMapAt_symm_of_mem_maximalAtlas`: charts
  of the maximal PL atlas and their inverses are PL.
* `TauCeti.isPLMap_id`, `TauCeti.isPLMap_const`, `TauCeti.IsPLMapAt.comp`, `TauCeti.IsPLMap.comp`:
  identities and constant maps are PL, and PL maps compose.
* `TauCeti.isPLMap_iff_isPLOn_univ`: a map between real normed spaces is a PL map exactly
  when it is piecewise linear on the whole space.

## References

* C. P. Rourke, B. J. Sanderson, *Introduction to Piecewise-Linear Topology*, Springer (1972),
  Chapter 1, for PL maps and PL manifolds.
-/

public section

open Set Filter Topology ChartedSpace StructureGroupoid StructureGroupoid.LocalInvariantProp
open scoped Manifold

namespace TauCeti

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H)
  {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  (I' : ModelWithCorners ℝ E' H')
  {E'' H'' : Type*} [NormedAddCommGroup E''] [NormedSpace ℝ E''] [TopologicalSpace H'']
  (I'' : ModelWithCorners ℝ E'' H'')
  {M M' M'' : Type*} [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace M']
  [ChartedSpace H' M'] [TopologicalSpace M''] [ChartedSpace H'' M'']

/-! ### The property in the model spaces -/

/-- A map `f : H → H'` between model spaces is piecewise linear within `s` at `x` when
`I' ∘ f ∘ I.symm`, its reading in the model vector spaces, is piecewise linear within
`I.symm ⁻¹' s ∩ range I` at `I x`. This is the property lifted to charted spaces to define PL maps,
as `ContDiffWithinAtProp` is for `ContMDiff`. -/
def PLWithinAtProp (f : H → H') (s : Set H) (x : H) : Prop :=
  IsPLWithinAt (I' ∘ f ∘ I.symm) (I.symm ⁻¹' s ∩ range I) (I x)

/-- The identity of a model space is piecewise linear everywhere. -/
theorem plWithinAtProp_id (x : H) : PLWithinAtProp I I id univ x :=
  ((ContinuousAffineMap.id ℝ E).isPLWithinAt _ _).congr
    (fun y hy => by simp [I.right_inv hy.2]) (by simp)

/-- **Piecewise linearity is a local invariant property**: in the model it is local, and invariant
under the PL groupoids of the source and of the target. So it lifts to charted spaces, where it
does not depend on the charts of the maximal PL atlases used to read it. -/
theorem plWithinAtProp_localInvariantProp :
    (PLGroupoid I).LocalInvariantProp (PLGroupoid I') (PLWithinAtProp I I') where
  is_local {s x u f} u_open xu := by
    have hset : I.symm ⁻¹' (s ∩ u) ∩ range I = I.symm ⁻¹' s ∩ range I ∩ I.symm ⁻¹' u := by
      simp only [inter_right_comm, preimage_inter]
    have hu : I.symm ⁻¹' u ∈ 𝓝 (I x) := by
      refine I.continuous_symm.continuousAt.preimage_mem_nhds ?_
      rw [I.left_inv]
      exact u_open.mem_nhds xu
    rw [PLWithinAtProp, PLWithinAtProp, hset]
    exact (isPLWithinAt_inter hu).symm
  right_invariance' {s x f e} he hx h := by
    rw [PLWithinAtProp] at h ⊢
    -- Precompose with the reading of `e.symm`, which is PL on the trace of its target.
    have hpt : I x = (I ∘ e.symm ∘ I.symm) (I (e x)) := by simp only [hx, mfld_simps]
    rw [hpt] at h
    have hg : IsPLWithinAt (I ∘ e.symm ∘ I.symm)
        (I.symm ⁻¹' e.target ∩ range I ∩ I.symm ⁻¹' (e.symm ⁻¹' s)) (I (e x)) :=
      ((mem_PLGroupoid_iff I).1 he).2.isPLWithinAt (by simp only [hx, mfld_simps]) |>.mono
        inter_subset_left
    have hcomp := h.comp hg fun y hy => by
      simp only [mfld_simps] at hy ⊢
      exact hy.2
    refine (hcomp.congr (fun y hy => ?_) ?_).mono_of_mem_nhdsWithin ?_
    · simp only [mfld_simps] at hy ⊢
    · simp only [hx, mfld_simps]
    · refine mem_nhdsWithin.2 ⟨I.symm ⁻¹' e.target, e.open_target.preimage I.continuous_symm, by
        simp_rw [mem_preimage, I.left_inv, e.mapsTo hx], ?_⟩
      mfld_set_tac
  congr_of_forall {s x f g} h hx hf := by
    apply hf.congr
    · intro y hy
      simp only [mfld_simps] at hy
      simp only [h, hy, mfld_simps]
    · simp only [hx, mfld_simps]
  left_invariance' {s x f e'} he' hs hx h := by
    rw [PLWithinAtProp] at h ⊢
    have hpt : (I' ∘ f ∘ I.symm) (I x) ∈ I'.symm ⁻¹' e'.source ∩ range I' := by
      simp only [hx, mfld_simps]
    have := ((mem_PLGroupoid_iff I').1 he').1.isPLWithinAt hpt
    convert this.comp h _
    · ext y
      simp only [mfld_simps]
    · intro y hy
      simp only [mfld_simps] at hy
      simpa only [hy, mfld_simps] using hs hy.1

/-! ### PL maps between charted spaces -/

/-- A map `f : M → M'` between charted spaces is *piecewise linear at* `x` when it is continuous at
`x` and, read in the preferred charts at `x` and at `f x` and then in the model vector spaces, it is
piecewise linear near `x` (`TauCeti.isPLMapAt_iff`). On PL manifolds any charts of the maximal PL
atlases may be used instead (`TauCeti.isPLMapAt_iff_of_mem_maximalAtlas`). -/
def IsPLMapAt (f : M → M') (x : M) : Prop :=
  LiftPropAt (PLWithinAtProp I I') f x

/-- A map `f : M → M'` between charted spaces is *piecewise linear* when it is piecewise linear at
every point. -/
def IsPLMap (f : M → M') : Prop :=
  LiftProp (PLWithinAtProp I I') f

variable {I I' I''}

/-- A map is PL at `x` exactly when it is continuous at `x` and its reading in the preferred charts
and the model vector spaces is piecewise linear near the image of `x`. -/
theorem isPLMapAt_iff {f : M → M'} {x : M} :
    IsPLMapAt I I' f x ↔ ContinuousAt f x ∧
      IsPLWithinAt (I' ∘ chartAt H' (f x) ∘ f ∘ (chartAt H x).symm ∘ I.symm) (range I)
        (I (chartAt H x x)) := by
  rw [IsPLMapAt, liftPropAt_iff, PLWithinAtProp, preimage_univ, univ_inter]
  -- The two readings differ only in the bracketing of `∘`.
  rfl

/-- A map is PL exactly when it is PL at every point. -/
theorem isPLMap_iff_forall_isPLMapAt {f : M → M'} : IsPLMap I I' f ↔ ∀ x, IsPLMapAt I I' f x :=
  Iff.rfl

/-- A PL map is PL at every point. -/
theorem IsPLMap.isPLMapAt {f : M → M'} (h : IsPLMap I I' f) (x : M) : IsPLMapAt I I' f x :=
  h x

/-- A map PL at a point is continuous there. -/
theorem IsPLMapAt.continuousAt {f : M → M'} {x : M} (h : IsPLMapAt I I' f x) : ContinuousAt f x :=
  (isPLMapAt_iff.1 h).1

/-- A PL map is continuous. -/
theorem IsPLMap.continuous {f : M → M'} (h : IsPLMap I I' f) : Continuous f :=
  continuous_iff_continuousAt.2 fun x => (h.isPLMapAt x).continuousAt

/-- **Chart independence.** A map is PL at `x` exactly when it is continuous at `x` and its reading
in any charts `e` at `x` and `e'` at `f x` of the maximal PL atlases is piecewise linear near
`I (e x)`. -/
theorem isPLMapAt_iff_of_mem_maximalAtlas {f : M → M'} {x : M} {e : OpenPartialHomeomorph M H}
    {e' : OpenPartialHomeomorph M' H'} (he : e ∈ (PLGroupoid I).maximalAtlas M) (hx : x ∈ e.source)
    (he' : e' ∈ (PLGroupoid I').maximalAtlas M') (hy : f x ∈ e'.source) :
    IsPLMapAt I I' f x ↔ ContinuousAt f x ∧
      IsPLWithinAt (I' ∘ e' ∘ f ∘ e.symm ∘ I.symm) (range I) (I (e x)) := by
  rw [IsPLMapAt, LiftPropAt, (plWithinAtProp_localInvariantProp I I').liftPropWithinAt_indep_chart
    he hx he' hy, continuousWithinAt_univ, PLWithinAtProp, preimage_univ, preimage_univ, univ_inter]
  -- The two readings differ only in the bracketing of `∘`.
  rfl

/-- The identity of a charted space is PL. -/
theorem isPLMap_id : IsPLMap I I (id : M → M) :=
  (plWithinAtProp_localInvariantProp I I).liftProp_id (plWithinAtProp_id I)

/-- A constant map is PL. -/
theorem isPLMap_const (c : M') : IsPLMap I I' fun _ : M => c := by
  refine fun x => isPLMapAt_iff.2 ⟨continuousAt_const, ?_⟩
  refine ((ContinuousAffineMap.const ℝ E (I' (chartAt H' c c))).isPLWithinAt _ _).congr
    (fun _ _ => ?_) ?_ <;> simp

/-- A chart of the maximal PL atlas is PL on its source. -/
theorem isPLMapAt_of_mem_maximalAtlas {e : OpenPartialHomeomorph M H}
    (he : e ∈ (PLGroupoid I).maximalAtlas M) {x : M}
    (hx : x ∈ e.source) : IsPLMapAt I I e x :=
  (plWithinAtProp_localInvariantProp I I).liftPropAt_of_mem_maximalAtlas (plWithinAtProp_id I)
    he hx

/-- The inverse of a chart of the maximal PL atlas is PL on its target. -/
theorem isPLMapAt_symm_of_mem_maximalAtlas {e : OpenPartialHomeomorph M H}
    (he : e ∈ (PLGroupoid I).maximalAtlas M) {x : H}
    (hx : x ∈ e.target) : IsPLMapAt I I e.symm x :=
  (plWithinAtProp_localInvariantProp I I).liftPropAt_symm_of_mem_maximalAtlas
    (plWithinAtProp_id I) he hx

/-- **PL maps compose**: if `f` is PL at `x` and `g` is PL at `f x`, then `g ∘ f` is PL at `x`. -/
theorem IsPLMapAt.comp {g : M' → M''} {f : M → M'} {x : M} (hg : IsPLMapAt I' I'' g (f x))
    (hf : IsPLMapAt I I' f x) : IsPLMapAt I I'' (g ∘ f) x := by
  rw [isPLMapAt_iff] at hf hg ⊢
  obtain ⟨hfc, hf⟩ := hf
  obtain ⟨hgc, hg⟩ := hg
  refine ⟨hgc.comp hfc, ?_⟩
  set c := chartAt H x
  set d := chartAt H' (f x)
  -- Near `I (c x)`, the points whose chart preimages `f` carries into the source of `d`.
  set T := range I ∩ I.symm ⁻¹' (c.target ∩ c.symm ⁻¹' (f ⁻¹' d.source))
  have hT : T ∈ 𝓝[range I] (I (c x)) := by
    refine inter_mem_nhdsWithin _ (I.continuous_symm.continuousAt.preimage_mem_nhds ?_)
    rw [I.left_inv]
    refine inter_mem (c.open_target.mem_nhds (mem_chart_target H x))
      ((c.continuousAt_symm (mem_chart_target H x)).preimage_mem_nhds ?_)
    rw [c.left_inv (mem_chart_source H x)]
    exact hfc.preimage_mem_nhds (d.open_source.mem_nhds (mem_chart_source H' (f x)))
  have hpt : (I' ∘ d ∘ f ∘ c.symm ∘ I.symm) (I (c x)) = I' (d (f x)) := by
    simp [c, mem_chart_source]
  rw [← hpt] at hg
  refine ((hg.comp (hf.mono inter_subset_left) fun _ _ => mem_range_self _).congr
    (fun y hy => ?_) ?_).mono_of_mem_nhdsWithin hT
  · simp [d.left_inv hy.2.2]
  · simp [c, d, mem_chart_source]

/-- **PL maps compose.** -/
theorem IsPLMap.comp {g : M' → M''} {f : M → M'} (hg : IsPLMap I' I'' g) (hf : IsPLMap I I' f) :
    IsPLMap I I'' (g ∘ f) :=
  fun x => IsPLMapAt.comp (hg (f x)) (hf x)

/-- Between real normed spaces with their trivial charts, the PL maps are exactly the maps
piecewise linear on the whole space. -/
theorem isPLMap_iff_isPLOn_univ {f : E → E'} :
    IsPLMap 𝓘(ℝ, E) 𝓘(ℝ, E') f ↔ IsPLOn f univ := by
  simp only [IsPLMap, liftProp_iff, PLWithinAtProp, mfld_simps]
  refine ⟨fun h => isPLOn_iff_forall_isPLWithinAt.2 fun x _ => h.2 x, fun h =>
    ⟨continuousOn_univ.1 h.continuousOn, fun x => h.isPLWithinAt (mem_univ x)⟩⟩

end TauCeti
