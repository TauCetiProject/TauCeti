/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Compactification.OnePoint.Basic
public import Mathlib.Topology.Maps.Proper.Basic

/-!
# Collapsing the complement of an open subspace onto the point at infinity

Let `e : X → M` be an open embedding and `g : X → V` a map. The **collapse** of `M` along `e`
and `g` is the map `M → OnePoint V` that sends `e x` to `g x` and every point outside the range
of `e` to `∞` (`TauCeti.onePointCollapse`). When `M` is Hausdorff and `g` is proper, it is
continuous (`TauCeti.continuous_onePointCollapse`): the preimage of the complement of a compact
set `K ⊆ V` is the complement of the compact, hence closed, set `e (g⁻¹ K)`.

This is the topological core of the Pontryagin–Thom construction, where `e` is a framed tubular
neighbourhood `S × ℝᵏ → M` of a compact submanifold `S` and `g` is the projection to `ℝᵏ`, which
is proper because `S` is compact. The collapse depends continuously on a parameter: if the open
embeddings `e t` are the slices of an open embedding `(t, x) ↦ (t, e t x)` of `T × X` into
`T × M`, the collapses along them form a continuous map on `T × M`
(`TauCeti.continuous_onePointCollapse_slice`). Taking `T` to be the unit interval, this is the
source of homotopies between collapse maps.

## Main declarations

* `TauCeti.onePointCollapse e g`: the collapse of `M` onto `OnePoint V` along `e` and `g`.
* `TauCeti.onePointCollapse_apply`, `TauCeti.onePointCollapse_eq_infty_iff`: its values.
* `TauCeti.preimage_onePointCollapse`: the preimage of a set not containing `∞`.
* `TauCeti.continuous_onePointCollapse`: continuity for an open embedding `e` into a Hausdorff
  space and a proper map `g`.
* `TauCeti.continuous_onePointCollapse_slice`: continuity of a family of collapses.

## References

* J. W. Milnor, *Topology from the Differentiable Viewpoint*, University Press of Virginia,
  1965, §7 (the Pontryagin construction).
-/

public section

open Function Set Topology OnePoint

namespace TauCeti

variable {X M V W : Type*}

/-- The collapse of `M` onto the one-point compactification of `V` along `e : X → M` and
`g : X → V`: the point `e x` goes to `g x`, and every point outside the range of `e` goes to `∞`.
It is meaningful for injective `e`, and continuous for an open embedding `e` into a Hausdorff
space and a proper map `g` (`TauCeti.continuous_onePointCollapse`). -/
noncomputable def onePointCollapse (e : X → M) (g : X → V) : M → OnePoint V :=
  extend e (fun x ↦ (g x : OnePoint V)) fun _ ↦ ∞

variable {e : X → M} {g : X → V}

@[simp]
theorem onePointCollapse_apply (he : Injective e) (g : X → V) (x : X) :
    onePointCollapse e g (e x) = g x :=
  he.extend_apply _ _ x

@[simp]
theorem onePointCollapse_of_notMem_range {m : M} (hm : m ∉ range e) :
    onePointCollapse e g m = ∞ :=
  extend_apply' _ _ m hm

/-- The collapse sends exactly the points outside the range of `e` to `∞`. -/
theorem onePointCollapse_eq_infty_iff (he : Injective e) {m : M} :
    onePointCollapse e g m = ∞ ↔ m ∉ range e := by
  refine ⟨?_, onePointCollapse_of_notMem_range⟩
  rintro h ⟨x, rfl⟩
  simp [he] at h

/-- The collapse sends `m` to the point `v` of `V` exactly when `m = e x` with `g x = v`. -/
theorem onePointCollapse_eq_coe_iff (he : Injective e) {m : M} {v : V} :
    onePointCollapse e g m = v ↔ ∃ x, g x = v ∧ e x = m := by
  by_cases hm : m ∈ range e
  · obtain ⟨x, rfl⟩ := hm
    simp [he, he.eq_iff]
  · rw [onePointCollapse_of_notMem_range hm]
    exact ⟨fun h ↦ (coe_ne_infty v h.symm).elim, fun ⟨x, _, hx⟩ ↦ (hm ⟨x, hx⟩).elim⟩

/-- The preimage under the collapse of a set `s` not containing `∞` is the image under `e` of the
preimage of `s` under `g`. -/
theorem preimage_onePointCollapse (he : Injective e) {s : Set (OnePoint V)} (hs : ∞ ∉ s) :
    onePointCollapse e g ⁻¹' s = e '' (g ⁻¹' ((↑) ⁻¹' s)) := by
  ext m
  by_cases hm : m ∈ range e
  · obtain ⟨x, rfl⟩ := hm
    simp [he, he.mem_set_image]
  · simp only [mem_preimage, onePointCollapse_of_notMem_range hm, hs, false_iff]
    exact fun ⟨x, _, hx⟩ ↦ hm ⟨x, hx⟩

/-- The range of `e` is the preimage under the collapse of the points of `V`. -/
theorem preimage_onePointCollapse_range_coe (he : Injective e) :
    onePointCollapse e g ⁻¹' range ((↑) : V → OnePoint V) = range e := by
  rw [preimage_onePointCollapse he (by simp), preimage_range, preimage_univ, image_univ]

/-- Postcomposing the collapse along `e` and `g` with the extension `OnePoint.map φ` of a map
`φ : V → W` is the collapse along `e` and `φ ∘ g`. -/
theorem map_onePointCollapse (he : Injective e) (φ : V → W) (m : M) :
    OnePoint.map φ (onePointCollapse e g m) = onePointCollapse e (φ ∘ g) m := by
  by_cases hm : m ∈ range e
  · obtain ⟨x, rfl⟩ := hm
    simp [he]
  · simp [onePointCollapse_of_notMem_range hm]

/-- Reparametrizing the domain of `e` and `g` by a bijection does not change the collapse. -/
theorem onePointCollapse_comp {Y : Type*} (he : Injective e) {φ : Y → X} (hφ : Bijective φ) :
    onePointCollapse (e ∘ φ) (g ∘ φ) = onePointCollapse e g := by
  ext1 m
  by_cases hm : m ∈ range e
  · obtain ⟨x, rfl⟩ := hm
    obtain ⟨y, rfl⟩ := hφ.2 x
    exact (onePointCollapse_apply (he.comp hφ.1) (g ∘ φ) y).trans
      (onePointCollapse_apply he g (φ y)).symm
  · rw [onePointCollapse_of_notMem_range hm, onePointCollapse_of_notMem_range]
    rwa [range_comp, hφ.2.range_eq, image_univ]

/-- The collapse along the slices `x ↦ e (t, x)` of a map `e : T × X → M`, as a function of
`(t, m)`, is the collapse of `T × M` along `(t, x) ↦ (t, e (t, x))`. -/
theorem onePointCollapse_slice_eq {T : Type*} {e : T × X → M} {g : T × X → V}
    (he : Injective fun q : T × X ↦ (q.1, e q)) (p : T × M) :
    onePointCollapse (fun x ↦ e (p.1, x)) (fun x ↦ g (p.1, x)) p.2 =
      onePointCollapse (fun q : T × X ↦ (q.1, e q)) g p := by
  have hslice : Injective fun x ↦ e (p.1, x) := fun x y h ↦
    (Prod.ext_iff.1 (he (Prod.ext rfl h : ((p.1, x).1, e (p.1, x)) = ((p.1, y).1, e (p.1, y))))).2
  obtain ⟨t, m⟩ := p
  by_cases hm : m ∈ range fun x ↦ e (t, x)
  · obtain ⟨x, rfl⟩ := hm
    rw [onePointCollapse_apply hslice]
    exact (onePointCollapse_apply he g (t, x)).symm
  · rw [onePointCollapse_of_notMem_range hm, onePointCollapse_of_notMem_range]
    rintro ⟨⟨t', x⟩, h⟩
    obtain ⟨rfl, rfl⟩ := Prod.ext_iff.1 h
    exact hm ⟨x, rfl⟩

variable [TopologicalSpace X] [TopologicalSpace M] [TopologicalSpace V]

/-- **Continuity of the collapse.** For an open embedding `e` into a Hausdorff space and a proper
map `g`, the collapse of `M` onto `OnePoint V` along `e` and `g` is continuous. -/
theorem continuous_onePointCollapse [T2Space M] (he : IsOpenEmbedding e) (hg : IsProperMap g) :
    Continuous (onePointCollapse e g) := by
  refine continuous_def.2 fun s hs ↦ ?_
  by_cases hinf : ∞ ∈ s
  · -- The complement of the preimage is the image of a compact set, hence closed.
    have hc : (onePointCollapse e g ⁻¹' s)ᶜ = e '' (g ⁻¹' ((↑) ⁻¹' s : Set V)ᶜ) := by
      rw [← preimage_compl, preimage_onePointCollapse he.injective (by simpa), preimage_compl]
    rw [← isClosed_compl_iff, hc]
    exact ((hg.isCompact_preimage ((isOpen_iff_of_mem' hinf).1 hs).1).image
      he.continuous).isClosed
  · rw [preimage_onePointCollapse he.injective hinf]
    exact he.isOpenMap _ (((isOpen_iff_of_notMem hinf).1 hs).preimage hg.continuous)

/-- **Continuity of a family of collapses.** If `(t, x) ↦ (t, e (t, x))` is an open embedding of
`T × X` into the Hausdorff space `T × M` and `g` is proper, then the collapses along the slices
`x ↦ e (t, x)` and `x ↦ g (t, x)` depend continuously on `(t, m)`. -/
theorem continuous_onePointCollapse_slice {T : Type*} [TopologicalSpace T] [T2Space T]
    [T2Space M] {e : T × X → M} {g : T × X → V}
    (he : IsOpenEmbedding fun q : T × X ↦ (q.1, e q)) (hg : IsProperMap g) :
    Continuous fun p : T × M ↦ onePointCollapse (fun x ↦ e (p.1, x)) (fun x ↦ g (p.1, x)) p.2 := by
  simp_rw [onePointCollapse_slice_eq he.injective]
  exact continuous_onePointCollapse he hg

end TauCeti
