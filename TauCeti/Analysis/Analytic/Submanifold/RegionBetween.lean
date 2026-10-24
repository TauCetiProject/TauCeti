/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Analytic.Submanifold.Graph
public import TauCeti.Topology.Order.RegionBetween

/-!
# Band maps between analytic submanifolds

The band interpolation map `TauCeti.regionBetweenMap g φ φ' ψ ψ'` sends the band between `φ` and
`φ'` over a base `S` affinely, fibre by fibre, to the band between `ψ` and `ψ'` over a base `T`,
above a base map `g : S → T`. This file reads it in the cylinder coordinates `Fin.cons t x` of
analytic submanifolds of `ℝⁿ⁺¹` (`TauCeti.IsAnalyticSubmanifold.cylinder`,
`TauCeti.IsAnalyticSubmanifold.between`, `TauCeti.IsAnalyticSubmanifold.graph`) and proves that
it is analytic. When the base map `g` is a bijection from `S` to `T` with inverse `g'`, both
analytic, and the endpoints are analytic, the band map is an analytic isomorphism between the open
bands (for strictly ordered endpoints) and between the endpoint graphs (for the upper graphs,
when a source fibre collapses exactly over a collapsed target fibre). That is, it is a bijection,
analytic on the source submanifold, whose inverse is the band map over `g'` with the endpoints
exchanged, which is analytic on the target submanifold by the same results.

Graphs and open bands over the simplices of a base triangulation are the cells of the prismatic
decomposition in Łojasiewicz's triangulation of semianalytic sets; these analytic isomorphisms
transfer them to the rectilinear cells.

## Main declarations

* `TauCeti.consRegionBetweenMap g φ φ' ψ ψ'`: the band map in cylinder coordinates.
* `TauCeti.analyticOnSubmanifold_consRegionBetweenMap`: the band map is analytic on every analytic
  submanifold lying over the base on which the source fibres do not collapse.
* `TauCeti.invOn_consRegionBetweenMap_regionBetween`,
  `TauCeti.bijOn_consRegionBetweenMap_regionBetween` and
  `TauCeti.analyticOnSubmanifold_consRegionBetweenMap_regionBetween`: the band map is an analytic
  isomorphism of open bands.
* `TauCeti.invOn_consRegionBetweenMap_graph_lower`,
  `TauCeti.bijOn_consRegionBetweenMap_graph_lower` and
  `TauCeti.analyticOnSubmanifold_consRegionBetweenMap_graph_lower`, and their `_upper`
  counterparts: the band map is an analytic isomorphism of the endpoint graphs.

## References

* S. Łojasiewicz, *Triangulation of semi-analytic sets*, Ann. Scuola Norm. Sup. Pisa (3) **18**
  (1964), 449–474, §2, Lemma 13.
-/

public section

open Set

namespace TauCeti

variable {n m d d' k : ℕ} {S : Set (Fin n → ℝ)} {T : Set (Fin m → ℝ)}
  {g : (Fin n → ℝ) → Fin m → ℝ} {g' : (Fin m → ℝ) → Fin n → ℝ}
  {φ φ' : (Fin n → ℝ) → ℝ} {ψ ψ' : (Fin m → ℝ) → ℝ}

/-- The band interpolation map `TauCeti.regionBetweenMap g φ φ' ψ ψ'` read in the cylinder
coordinates `Fin.cons t x` of analytic submanifolds, in which the height `t` is coordinate zero
and the base point `x` is the tail. -/
noncomputable def consRegionBetweenMap (g : (Fin n → ℝ) → Fin m → ℝ) (φ φ' : (Fin n → ℝ) → ℝ)
    (ψ ψ' : (Fin m → ℝ) → ℝ) (v : Fin (n + 1) → ℝ) : Fin (m + 1) → ℝ :=
  Fin.cons (regionBetweenMap g φ φ' ψ ψ' (Fin.tail v, v 0)).2
    (regionBetweenMap g φ φ' ψ ψ' (Fin.tail v, v 0)).1

@[simp]
theorem consRegionBetweenMap_cons (t : ℝ) (x : Fin n → ℝ) :
    consRegionBetweenMap g φ φ' ψ ψ' (Fin.cons t x) =
      Fin.cons (regionBetweenMap g φ φ' ψ ψ' (x, t)).2 (g x) := by
  simp [consRegionBetweenMap]

theorem consRegionBetweenMap_apply (v : Fin (n + 1) → ℝ) :
    consRegionBetweenMap g φ φ' ψ ψ' v = Fin.cons
      (ψ (g (Fin.tail v)) + (v 0 - φ (Fin.tail v)) / (φ' (Fin.tail v) - φ (Fin.tail v)) *
        (ψ' (g (Fin.tail v)) - ψ (g (Fin.tail v)))) (g (Fin.tail v)) := by
  simp [consRegionBetweenMap, regionBetweenMap_apply]

@[simp]
theorem consRegionBetweenMap_zero (v : Fin (n + 1) → ℝ) :
    consRegionBetweenMap g φ φ' ψ ψ' v 0 = (regionBetweenMap g φ φ' ψ ψ' (Fin.tail v, v 0)).2 := by
  simp [consRegionBetweenMap]

@[simp]
theorem tail_consRegionBetweenMap (v : Fin (n + 1) → ℝ) :
    Fin.tail (consRegionBetweenMap g φ φ' ψ ψ' v) = g (Fin.tail v) := by
  simp [consRegionBetweenMap]

/-- On the graph of the lower source endpoint, the band map is the graph map of the lower target
endpoint over `g`. -/
theorem consRegionBetweenMap_of_eq_lower {v : Fin (n + 1) → ℝ} (hv : v 0 = φ (Fin.tail v)) :
    consRegionBetweenMap g φ φ' ψ ψ' v = Fin.cons (ψ (g (Fin.tail v))) (g (Fin.tail v)) := by
  simp [consRegionBetweenMap, hv]

/-- On the graph of the upper source endpoint, the band map is the graph map of the upper target
endpoint over `g`, provided the source fibre collapses only over a collapsed target fibre. -/
theorem consRegionBetweenMap_of_eq_upper {v : Fin (n + 1) → ℝ} (hv : v 0 = φ' (Fin.tail v))
    (h : φ (Fin.tail v) = φ' (Fin.tail v) → ψ (g (Fin.tail v)) = ψ' (g (Fin.tail v))) :
    consRegionBetweenMap g φ φ' ψ ψ' v = Fin.cons (ψ' (g (Fin.tail v))) (g (Fin.tail v)) := by
  simp [consRegionBetweenMap, hv, regionBetweenMap_upper h]

/-- The band map over a left inverse `g'` of `g`, with source and target endpoints exchanged,
undoes the band map over `g` on the closed fibre over `Fin.tail v`, provided this fibre collapses
whenever the target fibre over it does. -/
theorem consRegionBetweenMap_consRegionBetweenMap {v : Fin (n + 1) → ℝ}
    (hv : g' (g (Fin.tail v)) = Fin.tail v)
    (hcollapse : ψ (g (Fin.tail v)) = ψ' (g (Fin.tail v)) → φ (Fin.tail v) = φ' (Fin.tail v))
    (hr : v 0 ∈ Icc (φ (Fin.tail v)) (φ' (Fin.tail v))) :
    consRegionBetweenMap g' ψ ψ' φ φ' (consRegionBetweenMap g φ φ' ψ ψ' v) = v := by
  have h := regionBetweenMap_regionBetweenMap (ψ' := ψ') hv hcollapse hr
  simp only [consRegionBetweenMap, Fin.tail_cons, Fin.cons_zero, Prod.mk.eta, h,
    Fin.cons_self_tail]

/-! ### Bijectivity -/

/-- If `g'` and `g` are inverse bijections between `S` and `T` and the endpoints are strictly
ordered, then the band maps over `g` and `g'` are inverse between the open bands. -/
theorem invOn_consRegionBetweenMap_regionBetween (h : InvOn g' g S T) (hg : MapsTo g S T)
    (hg' : MapsTo g' T S) (hφ : ∀ x ∈ S, φ x < φ' x) (hψ : ∀ y ∈ T, ψ y < ψ' y) :
    InvOn (consRegionBetweenMap g' ψ ψ' φ φ') (consRegionBetweenMap g φ φ' ψ ψ')
      {v | Fin.tail v ∈ S ∧ φ (Fin.tail v) < v 0 ∧ v 0 < φ' (Fin.tail v)}
      {w | Fin.tail w ∈ T ∧ ψ (Fin.tail w) < w 0 ∧ w 0 < ψ' (Fin.tail w)} :=
  ⟨fun _ hv ↦ consRegionBetweenMap_consRegionBetweenMap (h.1 hv.1)
      (fun hc ↦ absurd hc (hψ _ (hg hv.1)).ne) ⟨hv.2.1.le, hv.2.2.le⟩,
    fun _ hw ↦ consRegionBetweenMap_consRegionBetweenMap (h.2 hw.1)
      (fun hc ↦ absurd hc (hφ _ (hg' hw.1)).ne) ⟨hw.2.1.le, hw.2.2.le⟩⟩

/-- The band map sends the open band over `S` into the open band over `T`. -/
theorem mapsTo_consRegionBetweenMap_regionBetween (hg : MapsTo g S T)
    (hψ : ∀ y ∈ T, ψ y < ψ' y) :
    MapsTo (consRegionBetweenMap g φ φ' ψ ψ')
      {v | Fin.tail v ∈ S ∧ φ (Fin.tail v) < v 0 ∧ v 0 < φ' (Fin.tail v)}
      {w | Fin.tail w ∈ T ∧ ψ (Fin.tail w) < w 0 ∧ w 0 < ψ' (Fin.tail w)} := by
  intro v hv
  have h := mapsTo_regionBetweenMap_regionBetween (φ := φ) (φ' := φ') hg hψ
    (x := (Fin.tail v, v 0)) hv
  simpa [consRegionBetweenMap, regionBetween] using h

/-- If `g` is a bijection from `S` to `T` with inverse `g'` and the endpoints are strictly
ordered, then the band map is a bijection between the open bands. -/
theorem bijOn_consRegionBetweenMap_regionBetween (h : InvOn g' g S T) (hg : MapsTo g S T)
    (hg' : MapsTo g' T S) (hφ : ∀ x ∈ S, φ x < φ' x) (hψ : ∀ y ∈ T, ψ y < ψ' y) :
    BijOn (consRegionBetweenMap g φ φ' ψ ψ')
      {v | Fin.tail v ∈ S ∧ φ (Fin.tail v) < v 0 ∧ v 0 < φ' (Fin.tail v)}
      {w | Fin.tail w ∈ T ∧ ψ (Fin.tail w) < w 0 ∧ w 0 < ψ' (Fin.tail w)} :=
  (invOn_consRegionBetweenMap_regionBetween h hg hg' hφ hψ).bijOn
    (mapsTo_consRegionBetweenMap_regionBetween hg hψ)
    (mapsTo_consRegionBetweenMap_regionBetween hg' hφ)

/-- If `g'` and `g` are inverse on `S` and `T`, then the band maps over `g` and `g'` are inverse
between the graphs of the lower endpoints. -/
theorem invOn_consRegionBetweenMap_graph_lower (h : InvOn g' g S T) :
    InvOn (consRegionBetweenMap g' ψ ψ' φ φ') (consRegionBetweenMap g φ φ' ψ ψ')
      {v | Fin.tail v ∈ S ∧ v 0 = φ (Fin.tail v)} {w | Fin.tail w ∈ T ∧ w 0 = ψ (Fin.tail w)} := by
  refine ⟨fun v hv ↦ ?_, fun w hw ↦ ?_⟩
  · rw [consRegionBetweenMap_of_eq_lower hv.2, consRegionBetweenMap_cons, regionBetweenMap_lower,
      (h.1 hv.1 : g' (g (Fin.tail v)) = Fin.tail v), ← hv.2, Fin.cons_self_tail]
  · rw [consRegionBetweenMap_of_eq_lower hw.2, consRegionBetweenMap_cons, regionBetweenMap_lower,
      (h.2 hw.1 : g (g' (Fin.tail w)) = Fin.tail w), ← hw.2, Fin.cons_self_tail]

/-- The band map sends the graph of the lower source endpoint over `S` into the graph of the lower
target endpoint over `T`. -/
theorem mapsTo_consRegionBetweenMap_graph_lower (hg : MapsTo g S T) :
    MapsTo (consRegionBetweenMap g φ φ' ψ ψ') {v | Fin.tail v ∈ S ∧ v 0 = φ (Fin.tail v)}
      {w | Fin.tail w ∈ T ∧ w 0 = ψ (Fin.tail w)} := fun v hv ↦ by
  rw [consRegionBetweenMap_of_eq_lower hv.2]
  exact ⟨by simpa using hg hv.1, by simp⟩

/-- If `g` is a bijection from `S` to `T` with inverse `g'`, then the band map is a bijection
between the graphs of the lower endpoints. -/
theorem bijOn_consRegionBetweenMap_graph_lower (h : InvOn g' g S T) (hg : MapsTo g S T)
    (hg' : MapsTo g' T S) :
    BijOn (consRegionBetweenMap g φ φ' ψ ψ') {v | Fin.tail v ∈ S ∧ v 0 = φ (Fin.tail v)}
      {w | Fin.tail w ∈ T ∧ w 0 = ψ (Fin.tail w)} :=
  (invOn_consRegionBetweenMap_graph_lower h).bijOn (mapsTo_consRegionBetweenMap_graph_lower hg)
    (mapsTo_consRegionBetweenMap_graph_lower hg')

/-- If `g'` and `g` are inverse on `S` and `T`, `g'` maps `T` to `S`, and a source fibre
collapses exactly when the target fibre over it does, then the band maps over `g` and `g'` are
inverse between the graphs of the upper endpoints. -/
theorem invOn_consRegionBetweenMap_graph_upper (h : InvOn g' g S T) (hg' : MapsTo g' T S)
    (hcollapse : ∀ x ∈ S, φ x = φ' x ↔ ψ (g x) = ψ' (g x)) :
    InvOn (consRegionBetweenMap g' ψ ψ' φ φ') (consRegionBetweenMap g φ φ' ψ ψ')
      {v | Fin.tail v ∈ S ∧ v 0 = φ' (Fin.tail v)}
      {w | Fin.tail w ∈ T ∧ w 0 = ψ' (Fin.tail w)} := by
  refine ⟨fun v hv ↦ ?_, fun w hw ↦ ?_⟩
  · have hx : g' (g (Fin.tail v)) = Fin.tail v := h.1 hv.1
    rw [consRegionBetweenMap_of_eq_upper hv.2 (hcollapse _ hv.1).mp,
      consRegionBetweenMap_of_eq_upper (by simp) (by simpa [hx] using (hcollapse _ hv.1).mpr)]
    simp [hx, ← hv.2]
  · have hy : g (g' (Fin.tail w)) = Fin.tail w := h.2 hw.1
    have hc := hcollapse _ (hg' hw.1)
    rw [hy] at hc
    rw [consRegionBetweenMap_of_eq_upper hw.2 hc.mpr,
      consRegionBetweenMap_of_eq_upper (by simp) (by simpa [hy] using hc.mp)]
    simp [hy, ← hw.2]

/-- The band map sends the graph of the upper source endpoint over `S` into the graph of the upper
target endpoint over `T`, provided collapsed source fibres lie over collapsed target fibres. -/
theorem mapsTo_consRegionBetweenMap_graph_upper (hg : MapsTo g S T)
    (hcollapse : ∀ x ∈ S, φ x = φ' x → ψ (g x) = ψ' (g x)) :
    MapsTo (consRegionBetweenMap g φ φ' ψ ψ') {v | Fin.tail v ∈ S ∧ v 0 = φ' (Fin.tail v)}
      {w | Fin.tail w ∈ T ∧ w 0 = ψ' (Fin.tail w)} := fun v hv ↦ by
  rw [consRegionBetweenMap_of_eq_upper hv.2 (hcollapse _ hv.1)]
  exact ⟨by simpa using hg hv.1, by simp⟩

/-- If `g` is a bijection from `S` to `T` with inverse `g'` and a source fibre collapses exactly
when the target fibre over it does, then the band map is a bijection between the graphs of the
upper endpoints. -/
theorem bijOn_consRegionBetweenMap_graph_upper (h : InvOn g' g S T) (hg : MapsTo g S T)
    (hg' : MapsTo g' T S) (hcollapse : ∀ x ∈ S, φ x = φ' x ↔ ψ (g x) = ψ' (g x)) :
    BijOn (consRegionBetweenMap g φ φ' ψ ψ') {v | Fin.tail v ∈ S ∧ v 0 = φ' (Fin.tail v)}
      {w | Fin.tail w ∈ T ∧ w 0 = ψ' (Fin.tail w)} := by
  refine (invOn_consRegionBetweenMap_graph_upper h hg' hcollapse).bijOn
    (mapsTo_consRegionBetweenMap_graph_upper hg fun x hx ↦ (hcollapse x hx).mp)
    (mapsTo_consRegionBetweenMap_graph_upper hg' fun y hy ↦ ?_)
  have hc := hcollapse _ (hg' hy)
  rw [(h.2 hy : g (g' y) = y)] at hc
  exact hc.mpr

/-! ### Analyticity -/

/-- The projection `Fin.tail` of cylinder coordinates onto the base is analytic on every analytic
submanifold. The continuous linear map `Pi.compRightL ℝ _ Fin.succ` is `Fin.tail` by definition of
`Fin.tail`. -/
private theorem analyticOnSubmanifold_tail {A : Set (Fin (n + 1) → ℝ)}
    (hA : IsAnalyticSubmanifold k A) :
    AnalyticOnSubmanifold k (Fin.tail : (Fin (n + 1) → ℝ) → Fin n → ℝ) A :=
  ((Pi.compRightL ℝ (fun _ ↦ ℝ) Fin.succ).analyticOnNhd A).analyticOnSubmanifold hA

/-- **The band map is analytic.** If the base map `g` and the endpoints are analytic, then the band
map is analytic on every analytic submanifold `A` of `ℝⁿ⁺¹` lying over `S` on which the source
fibres do not collapse. -/
theorem analyticOnSubmanifold_consRegionBetweenMap {A : Set (Fin (n + 1) → ℝ)}
    (hA : IsAnalyticSubmanifold k A) (hAS : MapsTo Fin.tail A S)
    (hg : AnalyticOnSubmanifold d g S) (hφ : AnalyticOnSubmanifold d φ S)
    (hφ' : AnalyticOnSubmanifold d φ' S) (hψ : AnalyticOnSubmanifold d' ψ T)
    (hψ' : AnalyticOnSubmanifold d' ψ' T) (hgST : MapsTo g S T)
    (hne : ∀ v ∈ A, φ (Fin.tail v) ≠ φ' (Fin.tail v)) :
    AnalyticOnSubmanifold k (consRegionBetweenMap g φ φ' ψ ψ') A := by
  have htail := analyticOnSubmanifold_tail hA
  have hgA := hg.comp htail hAS
  rw [hA.analyticOnSubmanifold_iff]
  intro v hv e he hve
  -- Read every ingredient of the band map in the chart `e` of `A`.
  have h₀ := (((ContinuousLinearMap.proj 0).analyticOnNhd A).analyticOnSubmanifold hA
    |>.analyticAt_chart hv he hve)
  have hg₀ := hgA.analyticAt_chart hv he hve
  have hφ₀ := (hφ.comp htail hAS).analyticAt_chart hv he hve
  have hφ₀' := (hφ'.comp htail hAS).analyticAt_chart hv he hve
  have hψ₀ := (hψ.comp hgA (hgST.comp hAS)).analyticAt_chart hv he hve
  have hψ₀' := (hψ'.comp hgA (hgST.comp hAS)).analyticAt_chart hv he hve
  have hden : φ' (Fin.tail (e.symm (firstCoords ℝ k (n + 1) (firstCoords ℝ (n + 1) k (e v))))) -
      φ (Fin.tail (e.symm (firstCoords ℝ k (n + 1) (firstCoords ℝ (n + 1) k (e v))))) ≠ 0 := by
    rw [he.symm_firstCoords_firstCoords_apply hve hv]
    exact sub_ne_zero.mpr (hne v hv).symm
  have hcons := ((Fin.consEquivL ℝ fun _ : Fin (m + 1) ↦ ℝ).analyticAt _).comp
    ((hψ₀.add (((h₀.sub hφ₀).div (hφ₀'.sub hφ₀) hden).mul (hψ₀'.sub hψ₀))).prod hg₀)
  convert hcons using 1
  ext u i
  simp [consRegionBetweenMap_apply, Fin.consEquivL_apply]

/-- **The band map is analytic on the open band.** If the base map `g` and the endpoints are
analytic, then the band map is analytic on the open band between `φ` and `φ'` over `S`. -/
theorem analyticOnSubmanifold_consRegionBetweenMap_regionBetween
    (hS : IsAnalyticSubmanifold d S) (hg : AnalyticOnSubmanifold d g S)
    (hφ : AnalyticOnSubmanifold d φ S) (hφ' : AnalyticOnSubmanifold d φ' S)
    (hψ : AnalyticOnSubmanifold d' ψ T) (hψ' : AnalyticOnSubmanifold d' ψ' T)
    (hgST : MapsTo g S T) :
    AnalyticOnSubmanifold (d + 1) (consRegionBetweenMap g φ φ' ψ ψ')
      {v | Fin.tail v ∈ S ∧ φ (Fin.tail v) < v 0 ∧ v 0 < φ' (Fin.tail v)} := by
  rcases eq_empty_or_nonempty
      {v : Fin (n + 1) → ℝ | Fin.tail v ∈ S ∧ φ (Fin.tail v) < v 0 ∧ v 0 < φ' (Fin.tail v)} with
    hempty | hne
  · rw [hempty]
    exact analyticOnSubmanifold_iff.2 fun _ h ↦ h.elim
  exact analyticOnSubmanifold_consRegionBetweenMap
    (hS.between hφ.continuousOn hφ'.continuousOn hne) (fun _ hv ↦ hv.1) hg hφ hφ' hψ hψ' hgST
    fun _ hv ↦ (hv.2.1.trans hv.2.2).ne

/-- The band map is analytic on the graph of the lower source endpoint, where it is the graph map
of the lower target endpoint over `g`. -/
theorem analyticOnSubmanifold_consRegionBetweenMap_graph_lower (hS : IsAnalyticSubmanifold d S)
    (hg : AnalyticOnSubmanifold d g S) (hφ : AnalyticOnSubmanifold d φ S)
    (hψ : AnalyticOnSubmanifold d' ψ T) (hgST : MapsTo g S T) :
    AnalyticOnSubmanifold d (consRegionBetweenMap g φ φ' ψ ψ')
      {v | Fin.tail v ∈ S ∧ v 0 = φ (Fin.tail v)} := by
  have hA := hS.graph hφ
  have hAS : MapsTo Fin.tail {v : Fin (n + 1) → ℝ | Fin.tail v ∈ S ∧ v 0 = φ (Fin.tail v)} S :=
    fun _ hv ↦ hv.1
  have hgA := hg.comp (analyticOnSubmanifold_tail hA) hAS
  refine (((Fin.consEquivL ℝ fun _ : Fin (m + 1) ↦ ℝ).analyticOnNhd univ).comp_analyticOnSubmanifold
    ((hψ.comp hgA (hgST.comp hAS)).prod hgA) (mapsTo_univ _ _)).congr fun v hv ↦ ?_
  ext i
  simp [consRegionBetweenMap_of_eq_lower hv.2, Fin.consEquivL_apply]

/-- The band map is analytic on the graph of the upper source endpoint, where it is the graph map
of the upper target endpoint over `g`, provided collapsed source fibres lie over collapsed target
fibres. -/
theorem analyticOnSubmanifold_consRegionBetweenMap_graph_upper (hS : IsAnalyticSubmanifold d S)
    (hg : AnalyticOnSubmanifold d g S) (hφ' : AnalyticOnSubmanifold d φ' S)
    (hψ' : AnalyticOnSubmanifold d' ψ' T) (hgST : MapsTo g S T)
    (hcollapse : ∀ x ∈ S, φ x = φ' x → ψ (g x) = ψ' (g x)) :
    AnalyticOnSubmanifold d (consRegionBetweenMap g φ φ' ψ ψ')
      {v | Fin.tail v ∈ S ∧ v 0 = φ' (Fin.tail v)} := by
  have hA := hS.graph hφ'
  have hAS : MapsTo Fin.tail {v : Fin (n + 1) → ℝ | Fin.tail v ∈ S ∧ v 0 = φ' (Fin.tail v)} S :=
    fun _ hv ↦ hv.1
  have hgA := hg.comp (analyticOnSubmanifold_tail hA) hAS
  refine (((Fin.consEquivL ℝ fun _ : Fin (m + 1) ↦ ℝ).analyticOnNhd univ).comp_analyticOnSubmanifold
    ((hψ'.comp hgA (hgST.comp hAS)).prod hgA) (mapsTo_univ _ _)).congr fun v hv ↦ ?_
  ext i
  simp [consRegionBetweenMap_of_eq_upper hv.2 (hcollapse _ hv.1), Fin.consEquivL_apply]

end TauCeti
