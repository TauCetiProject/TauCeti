/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Analysis.Normed.Ring.Lemmas
public import TauCeti.Topology.ContinuousOn.ClosedGraph
public import TauCeti.Topology.UnitInterval.Basic

/-!
# Closures of bands and band interpolation maps

A *band* over a set `s ⊆ X` is the region between two real functions on `s`: Mathlib's open
`regionBetween φ φ' s`, and its closed counterpart `TauCeti.closedRegionBetween φ φ' s`. Bands
and graphs over the simplices of a base triangulation are the cells of the prismatic
decomposition in Łojasiewicz's triangulation of semianalytic sets. This file develops the
elementary endpoint calculus which glues the cell maps of that construction.

* `TauCeti.closure_regionBetween`: if `φ < φ'` on `s` and both are continuous on `closure s`, then
  the closure of the open band over `s` is the closed band over `closure s`.
  `TauCeti.closure_regionBetween_of_closure_graphOn_eq` states this, following Łojasiewicz, for
  endpoint functions whose graph closures are bounded single-valued functions on `closure s`.
* `TauCeti.regionBetweenMap g φ φ' ψ ψ'`: over a base map `g`, the map interpolating affinely
  between the fibres `[φ x, φ' x]` and `[ψ (g x), ψ' (g x)]`, lower endpoint to lower endpoint.
  A collapsed fibre `φ x = φ' x` is sent to `(g x, ψ (g x))`, so for ordered endpoints a source
  fibre is mapped onto its target fibre when it is nondegenerate, or when both fibres collapse.
* Graph and restriction compatibility: the band map restricts to the graph maps of its endpoints
  (`TauCeti.image_regionBetweenMap_graphOn_lower`, `TauCeti.image_regionBetweenMap_graphOn_upper`)
  and depends only on the data over the points it is evaluated at
  (`TauCeti.eqOn_regionBetweenMap`). It maps closed bands to closed bands and open bands to open
  bands, and the band map of an inverse base map is its inverse
  (`TauCeti.bijOn_regionBetweenMap`, `TauCeti.bijOn_regionBetweenMap_regionBetween`).
* `TauCeti.continuousOn_regionBetweenMap`: the band map is continuous on the closed band whenever
  the base and endpoint maps are continuous and every collapsed source fibre lies over a collapsed
  target fibre.

## References

* S. Łojasiewicz, *Triangulation of semi-analytic sets*, Ann. Scuola Norm. Sup. Pisa (3) **18**
  (1964), 449–474, §2, Lemmas 11, 12 and 14.
-/

public section

open Filter Set Topology

namespace TauCeti

section closedRegionBetween

variable {α : Type*}

/-- The closed region between two real-valued functions on a set: the points `(x, t)` with
`x ∈ s` and `f x ≤ t ≤ g x`. This is the closed counterpart of `regionBetween f g s`. -/
def closedRegionBetween (f g : α → ℝ) (s : Set α) : Set (α × ℝ) :=
  {p : α × ℝ | p.1 ∈ s ∧ p.2 ∈ Icc (f p.1) (g p.1)}

@[simp]
theorem mem_closedRegionBetween {f g : α → ℝ} {s : Set α} {p : α × ℝ} :
    p ∈ closedRegionBetween f g s ↔ p.1 ∈ s ∧ p.2 ∈ Icc (f p.1) (g p.1) :=
  Iff.rfl

theorem regionBetween_subset_closedRegionBetween (f g : α → ℝ) (s : Set α) :
    regionBetween f g s ⊆ closedRegionBetween f g s :=
  fun _ hp ↦ ⟨hp.1, Ioo_subset_Icc_self hp.2⟩

/-- The closed region between a function and itself is its graph. -/
@[simp]
theorem closedRegionBetween_self (f : α → ℝ) (s : Set α) :
    closedRegionBetween f f s = s.graphOn f := by
  ext ⟨x, t⟩
  simp [le_antisymm_iff, and_comm]

/-- The region between two functions only depends on their values on the base set. -/
theorem regionBetween_congr {f f' g g' : α → ℝ} {s : Set α} (hf : EqOn f f' s)
    (hg : EqOn g g' s) : regionBetween f g s = regionBetween f' g' s := by
  ext ⟨x, t⟩
  exact and_congr_right fun hx ↦ by rw [hf hx, hg hx]

/-- The closed region between two functions only depends on their values on the base set. -/
theorem closedRegionBetween_congr {f f' g g' : α → ℝ} {s : Set α} (hf : EqOn f f' s)
    (hg : EqOn g g' s) : closedRegionBetween f g s = closedRegionBetween f' g' s := by
  ext ⟨x, t⟩
  simp only [mem_closedRegionBetween]
  exact and_congr_right fun hx ↦ by rw [hf hx, hg hx]

/-- The closed region between two functions continuous on a closed set is closed. -/
theorem isClosed_closedRegionBetween [TopologicalSpace α] {f g : α → ℝ} {s : Set α}
    (hs : IsClosed s) (hf : ContinuousOn f s) (hg : ContinuousOn g s) :
    IsClosed (closedRegionBetween f g s) := by
  have hs' : IsClosed (s ×ˢ (univ : Set ℝ)) := hs.prod isClosed_univ
  have hfst : MapsTo Prod.fst (s ×ˢ (univ : Set ℝ)) s := fun _ hp ↦ hp.1
  have h₁ := hs'.isClosed_le (hf.comp continuousOn_fst hfst) continuousOn_snd
  have h₂ := hs'.isClosed_le continuousOn_snd (hg.comp continuousOn_fst hfst)
  convert h₁.inter h₂ using 1
  ext ⟨x, t⟩
  simp only [mem_closedRegionBetween, mem_Icc, mem_inter_iff, mem_ofPred_eq, mem_prod, mem_univ,
    and_true, Function.comp_apply]
  tauto

/-- **Łojasiewicz's band closure lemma**, for endpoints continuous on the closure of the base:
if `f < g` on `s`, then the closure of the open band between `f` and `g` over `s` is the closed
band over `closure s`. -/
theorem closure_regionBetween [TopologicalSpace α] {f g : α → ℝ} {s : Set α}
    (hf : ContinuousOn f (closure s)) (hg : ContinuousOn g (closure s))
    (hfg : ∀ x ∈ s, f x < g x) :
    closure (regionBetween f g s) = closedRegionBetween f g (closure s) := by
  have hsub : closedRegionBetween f g s ⊆ closedRegionBetween f g (closure s) :=
    fun p hp ↦ ⟨subset_closure hp.1, hp.2⟩
  refine (closure_minimal ((regionBetween_subset_closedRegionBetween f g s).trans hsub)
    (isClosed_closedRegionBetween isClosed_closure hf hg)).antisymm ?_
  -- Every point of the closed band is a limit of points `(x, f x + c * (g x - f x))` with
  -- `x ∈ s` and `0 < c < 1`, which lie in the open band.
  set H : α × ℝ → α × ℝ := fun p ↦ (p.1, f p.1 + p.2 * (g p.1 - f p.1))
  have hcl : closure (s ×ˢ Ioo (0 : ℝ) 1) = closure s ×ˢ Icc 0 1 := by
    rw [closure_prod_eq, closure_Ioo zero_ne_one]
  have hfst : MapsTo Prod.fst (closure (s ×ˢ Ioo (0 : ℝ) 1)) (closure s) := by
    rw [hcl]
    exact fun _ hp ↦ hp.1
  have hH : ContinuousOn H (closure (s ×ˢ Ioo (0 : ℝ) 1)) :=
    continuousOn_fst.prodMk ((hf.comp continuousOn_fst hfst).add
      (continuousOn_snd.mul ((hg.comp continuousOn_fst hfst).sub (hf.comp continuousOn_fst hfst))))
  have himage : H '' (s ×ˢ Ioo 0 1) ⊆ regionBetween f g s := by
    rintro _ ⟨⟨x, c⟩, ⟨hx, hc₀, hc₁⟩, rfl⟩
    have hpos : 0 < g x - f x := sub_pos.mpr (hfg x hx)
    refine ⟨hx, ?_, ?_⟩
    · simpa [H] using mul_pos hc₀ hpos
    · simp only [H]
      nlinarith
  rintro ⟨x, t⟩ ⟨hx, hft, htg⟩
  have hc := sub_div_sub_mem_unitInterval hft htg
  refine closure_mono himage (hH.image_closure ⟨(x, (t - f x) / (g x - f x)), ?_, ?_⟩)
  · rw [hcl]
    exact ⟨hx, hc⟩
  · rcases (hft.trans htg).eq_or_lt with hfgx | hfgx
    · simp [H, ← hfgx, le_antisymm hft (hfgx ▸ htg)]
    · simp [H, div_mul_cancel₀ _ (sub_pos.mpr hfgx).ne']

/-- **Łojasiewicz's band closure lemma**: if `f < g` on `s` and the closures of the graphs of
`f` and `g` over `s` are the graphs over `closure s` of bounded functions `F` and `G`, then the
closure of the open band between `f` and `g` over `s` is the closed band between `F` and `G` over
`closure s`. -/
theorem closure_regionBetween_of_closure_graphOn_eq [TopologicalSpace α] {f g F G : α → ℝ}
    {s : Set α} (hF : closure (s.graphOn f) = (closure s).graphOn F)
    (hG : closure (s.graphOn g) = (closure s).graphOn G)
    (hFb : Bornology.IsBounded (F '' closure s)) (hGb : Bornology.IsBounded (G '' closure s))
    (hfg : ∀ x ∈ s, f x < g x) :
    closure (regionBetween f g s) = closedRegionBetween F G (closure s) := by
  have heq {f F : α → ℝ} (h : closure (s.graphOn f) = (closure s).graphOn F) : EqOn f F s :=
    fun x hx ↦ ((mem_graphOn.mp (h ▸ subset_closure (mem_graphOn.mpr ⟨hx, rfl⟩) :
      (x, f x) ∈ (closure s).graphOn F)).2).symm
  have hcont {f F : α → ℝ} (h : closure (s.graphOn f) = (closure s).graphOn F)
      (hb : Bornology.IsBounded (F '' closure s)) : ContinuousOn F (closure s) :=
    continuousOn_of_isClosed_graphOn (h ▸ isClosed_closure) hb.isCompact_closure
      ((mapsTo_image F _).mono_right subset_closure)
  rw [regionBetween_congr (heq hF) (heq hG)]
  exact closure_regionBetween (hcont hF hFb) (hcont hG hGb) fun x hx ↦
    heq hF hx ▸ heq hG hx ▸ hfg x hx

end closedRegionBetween

section regionBetweenMap

variable {X Y : Type*}

/-- The band interpolation map over a base map `g : X → Y`, from the band between `φ` and `φ'`
to the band between `ψ` and `ψ'`. It sends `(x, t)` to `(g x, s)` where
`s = ψ (g x) + (t - φ x) / (φ' x - φ x) * (ψ' (g x) - ψ (g x))`. If `φ x < φ' x` and
`ψ (g x) ≤ ψ' (g x)`, it maps the fibre `[φ x, φ' x]` affinely onto `[ψ (g x), ψ' (g x)]`. When the
source endpoints coincide, the quotient is `0` and the point is sent to `(g x, ψ (g x))`
(`regionBetweenMap_of_eq`), so a collapsed source fibre is mapped onto its target fibre only when
that collapses too. -/
noncomputable def regionBetweenMap (g : X → Y) (φ φ' : X → ℝ) (ψ ψ' : Y → ℝ) (p : X × ℝ) :
    Y × ℝ :=
  (g p.1, ψ (g p.1) + (p.2 - φ p.1) / (φ' p.1 - φ p.1) * (ψ' (g p.1) - ψ (g p.1)))

variable {g : X → Y} {g' : Y → X} {φ φ' : X → ℝ} {ψ ψ' : Y → ℝ} {s : Set X} {t : Set Y}

theorem regionBetweenMap_apply (g : X → Y) (φ φ' : X → ℝ) (ψ ψ' : Y → ℝ) (x : X) (r : ℝ) :
    regionBetweenMap g φ φ' ψ ψ' (x, r) =
      (g x, ψ (g x) + (r - φ x) / (φ' x - φ x) * (ψ' (g x) - ψ (g x))) :=
  (rfl)

@[simp]
theorem regionBetweenMap_fst (p : X × ℝ) : (regionBetweenMap g φ φ' ψ ψ' p).1 = g p.1 :=
  (rfl)

/-- Over a collapsed fibre `φ x = φ' x`, the band map is the graph map of the lower target
endpoint. -/
@[simp]
theorem regionBetweenMap_of_eq {x : X} (h : φ x = φ' x) (r : ℝ) :
    regionBetweenMap g φ φ' ψ ψ' (x, r) = (g x, ψ (g x)) := by
  simp [regionBetweenMap_apply, h]

@[simp]
theorem regionBetweenMap_lower (x : X) :
    regionBetweenMap g φ φ' ψ ψ' (x, φ x) = (g x, ψ (g x)) := by
  simp [regionBetweenMap_apply]

/-- The band map sends the upper source endpoint to the upper target endpoint, provided a
collapsed source fibre lies over a collapsed target fibre. -/
@[simp]
theorem regionBetweenMap_upper {x : X} (h : φ x = φ' x → ψ (g x) = ψ' (g x)) :
    regionBetweenMap g φ φ' ψ ψ' (x, φ' x) = (g x, ψ' (g x)) := by
  by_cases hx : φ x = φ' x
  · rw [← hx, regionBetweenMap_lower, h hx]
  · simp [regionBetweenMap_apply, div_self (sub_ne_zero.mpr (Ne.symm hx))]

/-- On the graph of the lower source endpoint, the band map is the graph map of the lower target
endpoint over `g`. -/
theorem image_regionBetweenMap_graphOn_lower (g : X → Y) (φ φ' : X → ℝ) (ψ ψ' : Y → ℝ)
    (s : Set X) : regionBetweenMap g φ φ' ψ ψ' '' s.graphOn φ = (g '' s).graphOn ψ := by
  simp only [graphOn, image_image, regionBetweenMap_lower]

/-- On the graph of the upper source endpoint, the band map is the graph map of the upper target
endpoint over `g`, provided collapsed source fibres lie over collapsed target fibres. -/
theorem image_regionBetweenMap_graphOn_upper
    (h : ∀ x ∈ s, φ x = φ' x → ψ (g x) = ψ' (g x)) :
    regionBetweenMap g φ φ' ψ ψ' '' s.graphOn φ' = (g '' s).graphOn ψ' := by
  simp only [graphOn, image_image]
  exact image_congr fun x hx ↦ regionBetweenMap_upper (h x hx)

/-- **Restriction compatibility**: over a set `s` on which two sets of base and endpoint data
agree, their band maps agree. -/
theorem eqOn_regionBetweenMap {g₁ g₂ : X → Y} {φ₁ φ₁' φ₂ φ₂' : X → ℝ} {ψ₁ ψ₁' ψ₂ ψ₂' : Y → ℝ}
    (hg : EqOn g₁ g₂ s) (hφ : EqOn φ₁ φ₂ s) (hφ' : EqOn φ₁' φ₂' s) (hψ : EqOn ψ₁ ψ₂ (g₁ '' s))
    (hψ' : EqOn ψ₁' ψ₂' (g₁ '' s)) :
    EqOn (regionBetweenMap g₁ φ₁ φ₁' ψ₁ ψ₁') (regionBetweenMap g₂ φ₂ φ₂' ψ₂ ψ₂')
      (Prod.fst ⁻¹' s) := by
  rintro ⟨x, r⟩ (hx : x ∈ s)
  simp only [regionBetweenMap_apply, ← hg hx, hφ hx, hφ' hx, hψ (mem_image_of_mem g₁ hx),
    hψ' (mem_image_of_mem g₁ hx)]

/-- The band map sends the closed band over `s` into the closed band over `t`. -/
theorem mapsTo_regionBetweenMap_closedRegionBetween (hg : MapsTo g s t)
    (hψ : ∀ y ∈ t, ψ y ≤ ψ' y) :
    MapsTo (regionBetweenMap g φ φ' ψ ψ') (closedRegionBetween φ φ' s)
      (closedRegionBetween ψ ψ' t) := by
  rintro ⟨x, r⟩ ⟨hx, hφr, hrφ⟩
  obtain ⟨hc₀, hc₁⟩ := sub_div_sub_mem_unitInterval hφr hrφ
  have hd : 0 ≤ ψ' (g x) - ψ (g x) := sub_nonneg.mpr (hψ _ (hg hx))
  refine ⟨hg hx, ?_, ?_⟩
  · simpa [regionBetweenMap_apply] using mul_nonneg hc₀ hd
  · simp only [regionBetweenMap_apply]
    nlinarith

/-- The band map sends the open band over `s` into the open band over `t`. -/
theorem mapsTo_regionBetweenMap_regionBetween (hg : MapsTo g s t) (hψ : ∀ y ∈ t, ψ y < ψ' y) :
    MapsTo (regionBetweenMap g φ φ' ψ ψ') (regionBetween φ φ' s) (regionBetween ψ ψ' t) := by
  rintro ⟨x, r⟩ ⟨hx, hφr, hrφ⟩
  have hc₀ : 0 < (r - φ x) / (φ' x - φ x) :=
    div_pos (sub_pos.mpr hφr) (sub_pos.mpr (hφr.trans hrφ))
  have hc₁ : (r - φ x) / (φ' x - φ x) < 1 :=
    (div_lt_one (sub_pos.mpr (hφr.trans hrφ))).mpr (sub_lt_sub_right hrφ _)
  have hd : 0 < ψ' (g x) - ψ (g x) := sub_pos.mpr (hψ _ (hg hx))
  refine ⟨hg hx, ?_, ?_⟩
  · simpa [regionBetweenMap_apply] using mul_pos hc₀ hd
  · simp only [regionBetweenMap_apply]
    nlinarith

/-- The band map over a left inverse `g'` of `g`, with source and target endpoints exchanged,
undoes the band map over `g` on the fibre over `x`, provided the source fibre over `x` collapses
whenever the target fibre over `g x` does. -/
theorem regionBetweenMap_regionBetweenMap {x : X} {r : ℝ} (hx : g' (g x) = x)
    (hcollapse : ψ (g x) = ψ' (g x) → φ x = φ' x) (hr : r ∈ Icc (φ x) (φ' x)) :
    regionBetweenMap g' ψ ψ' φ φ' (regionBetweenMap g φ φ' ψ ψ' (x, r)) = (x, r) := by
  by_cases hφ : φ x = φ' x
  · rw [regionBetweenMap_of_eq hφ, regionBetweenMap_lower, hx, le_antisymm (hφ ▸ hr.2) hr.1]
  · have hφ₀ : φ' x - φ x ≠ 0 := sub_ne_zero.mpr (Ne.symm hφ)
    have hψ₀ : ψ' (g x) - ψ (g x) ≠ 0 := sub_ne_zero.mpr (Ne.symm (hφ ∘ hcollapse))
    simp only [regionBetweenMap_apply, hx, add_sub_cancel_left, Prod.mk.injEq, true_and]
    field_simp
    ring

/-- If `g'` and `g` are inverse on `s` and `t`, `g'` maps `t` to `s`, and a source fibre collapses
exactly when the target fibre over it does, then the band maps over `g` and `g'` are inverse on
the closed bands. -/
theorem invOn_regionBetweenMap (h : InvOn g' g s t) (hg' : MapsTo g' t s)
    (hcollapse : ∀ x ∈ s, φ x = φ' x ↔ ψ (g x) = ψ' (g x)) :
    InvOn (regionBetweenMap g' ψ ψ' φ φ') (regionBetweenMap g φ φ' ψ ψ')
      (closedRegionBetween φ φ' s) (closedRegionBetween ψ ψ' t) := by
  refine ⟨fun ⟨x, r⟩ ⟨hx, hr⟩ ↦
    regionBetweenMap_regionBetweenMap (h.1 hx) (hcollapse x hx).mpr hr,
    fun ⟨y, r⟩ ⟨hy, hr⟩ ↦ regionBetweenMap_regionBetweenMap (h.2 hy) ?_ hr⟩
  have hy' := hcollapse _ (hg' hy)
  rw [(h.2 hy : g (g' y) = y)] at hy'
  exact hy'.mp

/-- If `g` is a bijection from `s` to `t` with inverse `g'`, the endpoints are ordered, and a
source fibre collapses exactly when the target fibre over it does, then the band map is a
bijection between the closed bands. -/
theorem bijOn_regionBetweenMap (h : InvOn g' g s t) (hg : MapsTo g s t) (hg' : MapsTo g' t s)
    (hφ : ∀ x ∈ s, φ x ≤ φ' x) (hψ : ∀ y ∈ t, ψ y ≤ ψ' y)
    (hcollapse : ∀ x ∈ s, φ x = φ' x ↔ ψ (g x) = ψ' (g x)) :
    BijOn (regionBetweenMap g φ φ' ψ ψ') (closedRegionBetween φ φ' s)
      (closedRegionBetween ψ ψ' t) :=
  (invOn_regionBetweenMap h hg' hcollapse).bijOn
    (mapsTo_regionBetweenMap_closedRegionBetween hg hψ)
    (mapsTo_regionBetweenMap_closedRegionBetween hg' hφ)

/-- If `g` is a bijection from `s` to `t` with inverse `g'` and the endpoints are strictly
ordered, then the band map is a bijection between the open bands. -/
theorem bijOn_regionBetweenMap_regionBetween (h : InvOn g' g s t) (hg : MapsTo g s t)
    (hg' : MapsTo g' t s) (hφ : ∀ x ∈ s, φ x < φ' x) (hψ : ∀ y ∈ t, ψ y < ψ' y) :
    BijOn (regionBetweenMap g φ φ' ψ ψ') (regionBetween φ φ' s) (regionBetween ψ ψ' t) :=
  ((invOn_regionBetweenMap h hg' fun x hx ↦
      iff_of_false (hφ x hx).ne (hψ _ (hg hx)).ne).mono
    (regionBetween_subset_closedRegionBetween φ φ' s)
    (regionBetween_subset_closedRegionBetween ψ ψ' t)).bijOn
    (mapsTo_regionBetweenMap_regionBetween hg hψ) (mapsTo_regionBetweenMap_regionBetween hg' hφ)

variable [TopologicalSpace X] [TopologicalSpace Y]

/-- **Continuity of the closed-band map**: if the base map and the endpoints are continuous and
every collapsed source fibre lies over a collapsed target fibre, then the band map is continuous on
the closed band. -/
theorem continuousOn_regionBetweenMap (hg : ContinuousOn g s) (hφ : ContinuousOn φ s)
    (hφ' : ContinuousOn φ' s) (hψ : ContinuousOn ψ t) (hψ' : ContinuousOn ψ' t)
    (hgst : MapsTo g s t) (hcollapse : ∀ x ∈ s, φ x = φ' x → ψ (g x) = ψ' (g x)) :
    ContinuousOn (regionBetweenMap g φ φ' ψ ψ') (closedRegionBetween φ φ' s) := by
  set D := closedRegionBetween φ φ' s
  have hfst : MapsTo Prod.fst D s := fun _ hp ↦ hp.1
  have hg₁ : ContinuousOn (fun p : X × ℝ ↦ g p.1) D := hg.comp continuousOn_fst hfst
  have hψ₁ : ContinuousOn (fun p : X × ℝ ↦ ψ (g p.1)) D := hψ.comp hg₁ (hgst.comp hfst)
  have hψ₁' : ContinuousOn (fun p : X × ℝ ↦ ψ' (g p.1)) D := hψ'.comp hg₁ (hgst.comp hfst)
  have hmap : regionBetweenMap g φ φ' ψ ψ' = fun p : X × ℝ ↦
      (g p.1, ψ (g p.1) + (p.2 - φ p.1) / (φ' p.1 - φ p.1) * (ψ' (g p.1) - ψ (g p.1))) :=
    funext fun p ↦ regionBetweenMap_apply g φ φ' ψ ψ' p.1 p.2
  rw [hmap]
  rintro ⟨x, r⟩ hp
  refine (hg₁ _ hp).prodMk ?_
  by_cases hx : φ x = φ' x
  · -- Over a collapsed fibre the normalized height stays in `[0, 1]` while the target width
    -- tends to `0`, so the second coordinate tends to `ψ (g x)`.
    have hwidth : Tendsto (fun p : X × ℝ ↦ ψ' (g p.1) - ψ (g p.1)) (𝓝[D] (x, r)) (𝓝 0) := by
      simpa [hcollapse x hp.1 hx] using (hψ₁' _ hp).tendsto.sub (hψ₁ _ hp).tendsto
    have hbdd : IsBoundedUnder (· ≤ ·) (𝓝[D] (x, r))
        (norm ∘ fun p : X × ℝ ↦ (p.2 - φ p.1) / (φ' p.1 - φ p.1)) := by
      refine isBoundedUnder_of_eventually_le (a := 1) (eventually_nhdsWithin_of_forall ?_)
      rintro ⟨y, u⟩ ⟨-, hu⟩
      obtain ⟨hc₀, hc₁⟩ := sub_div_sub_mem_unitInterval hu.1 hu.2
      rwa [Function.comp_apply, Real.norm_eq_abs, abs_of_nonneg hc₀]
    have := (hψ₁ _ hp).tendsto.add (isBoundedUnder_le_mul_tendsto_zero hbdd hwidth)
    simpa [ContinuousWithinAt, hx] using this
  · have hφ₁ : ContinuousOn (fun p : X × ℝ ↦ φ p.1) D := hφ.comp continuousOn_fst hfst
    have hφ₁' : ContinuousOn (fun p : X × ℝ ↦ φ' p.1) D := hφ'.comp continuousOn_fst hfst
    exact (hψ₁ _ hp).add ((((continuousOn_snd _ hp).sub (hφ₁ _ hp)).div
      ((hφ₁' _ hp).sub (hφ₁ _ hp)) (sub_ne_zero.mpr (Ne.symm hx))).mul
      ((hψ₁' _ hp).sub (hψ₁ _ hp)))

end regionBetweenMap

end TauCeti
