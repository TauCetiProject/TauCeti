/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.Constructions
public import Mathlib.Analysis.Analytic.Polynomial
public import Mathlib.Topology.OpenPartialHomeomorph.IsImage
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.OpenPartialHomeomorph.Continuity

/-!
# Analytic submanifolds of `𝕜ⁿ` and analytic functions on them

A subset `S` of `𝕜ⁿ` is a `d`-dimensional *analytic submanifold* if it can be straightened near
each of its points by an analytic change of coordinates of the ambient space: around every
`x ∈ S` there is an open partial homeomorphism `e` of `𝕜ⁿ`, analytic with analytic inverse, which
maps `e.source ∩ S` onto the points of `e.target` whose coordinates of index at least `d` vanish.
Such an `e` is an *analytic chart* of `S` (`TauCeti.IsAnalyticChart`).

A function `f` on `𝕜ⁿ` is *analytic on* the `d`-dimensional submanifold `S` if near each point of
`S` its coordinate expression `u ↦ f (e.symm (u, 0))` in an analytic chart, a function of the first
`d` coordinates `u ∈ 𝕜ᵈ`, is analytic (`TauCeti.AnalyticOnSubmanifold`). Only the values of `f`
on `S` matter. Analyticity does not depend on the chart: once the coordinate expression is
analytic in one chart, it is analytic in every chart around the point, since the transition
between two charts is analytic. This is what makes the notion usable: analytic functions on `S`
are closed under composition with analytic maps of the values, under pairing, and under
composition with analytic maps from `S` into another analytic submanifold. Submanifolds restrict
to nonempty relatively open subsets, analytic functions restrict to arbitrary relatively open
subsets, and analyticity of functions is a local property.

Over `ℝ`, analytic submanifolds are the cells over which McCallum's and Lazard's projection
theorems lift cylindrical decompositions: the lifting theorems assert that, over such a cell, the
ordered real roots of suitable polynomials are analytic functions on the cell.

## Implementation notes

The coordinate maps `TauCeti.firstCoords 𝕜 d n : 𝕜ᵈ → 𝕜ⁿ` and `TauCeti.firstCoords 𝕜 n d` are
defined without the hypothesis `d ≤ n`, so that charts and analytic functions make sense for every
`d`; the hypothesis `d ≤ n` is part of `TauCeti.IsAnalyticSubmanifold`.

## Main declarations

* `TauCeti.firstCoords 𝕜 m k`: the linear map `𝕜ᵐ → 𝕜ᵏ` copying the first `min m k`
  coordinates. It includes `𝕜ᵈ` in `𝕜ⁿ` as the first `d` coordinates and projects back.
* `TauCeti.IsAnalyticChart d S e`: `e` is an analytic chart of `S` in dimension `d`.
* `TauCeti.IsAnalyticSubmanifold d S`: `S` is a `d`-dimensional analytic submanifold.
* `TauCeti.AnalyticOnSubmanifold d f S`: `f` is analytic on `S` in dimension `d`.
* `TauCeti.AnalyticOnSubmanifold.analyticAt_chart`: independence of the chart.
* `TauCeti.AnalyticOnSubmanifold.analyticOnNhd`: the coordinate expression in any chart is
  analytic on the open set of `𝕜ᵈ` where it is defined.
* `AnalyticOnNhd.analyticOnSubmanifold`, `AnalyticOnNhd.comp_analyticOnSubmanifold`,
  `TauCeti.AnalyticOnSubmanifold.prod`, `TauCeti.AnalyticOnSubmanifold.comp`: ambient analytic
  functions, compositions and pairs.
* `TauCeti.IsAnalyticSubmanifold.inter`, `TauCeti.AnalyticOnSubmanifold.inter`,
  `TauCeti.analyticOnSubmanifold_of_locally_analyticOnSubmanifold`: restriction to relatively
  open subsets (nonempty ones, for submanifolds), and locality.
* `TauCeti.AnalyticOnSubmanifold.exists_analyticAt_eqOn`,
  `TauCeti.AnalyticOnSubmanifold.exists_analyticOnNhd_eqOn`: local ambient analytic extensions.
* `TauCeti.AnalyticOnSubmanifold.continuousOn`: intrinsic analytic functions are continuous.
* `TauCeti.IsAnalyticSubmanifold.of_isOpen_preimage_val`: nonempty relatively open subsets.
* `TauCeti.isAnalyticSubmanifold_coordSubspace`, `IsOpen.isAnalyticSubmanifold`,
  `TauCeti.isAnalyticSubmanifold_singleton`: coordinate subspaces, open sets and points.

## References

* S. G. Krantz and H. R. Parks, *A Primer of Real Analytic Functions*, second edition,
  Birkhäuser, 2002, Chapter 2 (real analytic submanifolds).
* S. McCallum, [*An improved projection operation for cylindrical algebraic
  decomposition*](https://doi.org/10.1007/978-3-7091-9459-1_12), 1998 (analytic delineability
  over analytic submanifolds).
-/

public section

open Set Filter Topology

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E F : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F] {m n d d' : ℕ}

/-! ### Leading coordinates -/

variable (𝕜) in
/-- `TauCeti.firstCoords 𝕜 m k v` is the vector of `𝕜ᵏ` whose coordinate of index `i` is that of
`v ∈ 𝕜ᵐ` when `i < m`, and zero otherwise. For `d ≤ n`, `firstCoords 𝕜 d n` includes `𝕜ᵈ` in `𝕜ⁿ`
as the subspace of the first `d` coordinates, and `firstCoords 𝕜 n d` is the projection onto
these coordinates. -/
def firstCoords (m k : ℕ) : (Fin m → 𝕜) →L[𝕜] Fin k → 𝕜 :=
  ContinuousLinearMap.pi fun i ↦ if h : i.val < m then ContinuousLinearMap.proj ⟨i, h⟩ else 0

@[simp]
theorem firstCoords_apply (v : Fin m → 𝕜) (i : Fin n) :
    firstCoords 𝕜 m n v i = if h : i.val < m then v ⟨i, h⟩ else 0 := by
  unfold firstCoords
  split_ifs <;> simp [*]

/-- The coordinates of index at least `m` of `firstCoords 𝕜 m n v` vanish. -/
theorem firstCoords_apply_of_le (v : Fin m → 𝕜) {i : Fin n} (hi : m ≤ i.val) :
    firstCoords 𝕜 m n v i = 0 := by
  simp [hi.not_gt]

/-- Projecting `𝕜ᵈ ⊆ 𝕜ⁿ` back to its first `d` coordinates is the identity. -/
@[simp]
theorem firstCoords_firstCoords_of_le (h : d ≤ n) (u : Fin d → 𝕜) :
    firstCoords 𝕜 n d (firstCoords 𝕜 d n u) = u := by
  ext j
  simp [j.isLt, j.isLt.trans_le h]

/-- A vector of `𝕜ⁿ` whose coordinates of index at least `d` vanish is recovered from its first
`d` coordinates. -/
theorem firstCoords_firstCoords_of_forall {y : Fin n → 𝕜} (hy : ∀ i : Fin n, d ≤ i.val → y i = 0) :
    firstCoords 𝕜 d n (firstCoords 𝕜 n d y) = y := by
  ext i
  by_cases hi : i.val < d
  · simp [hi]
  · simp [hi, hy i (not_lt.1 hi)]

/-! ### Analytic charts -/

variable {S T U : Set (Fin n → 𝕜)} {e : OpenPartialHomeomorph (Fin n → 𝕜) (Fin n → 𝕜)}
  {x : Fin n → 𝕜}

/-- An *analytic chart* of `S ⊆ 𝕜ⁿ` in dimension `d` is an open partial homeomorphism `e` of `𝕜ⁿ`,
analytic on its source with inverse analytic on its target, which straightens `S`: it maps
`e.source ∩ S` onto the points of `e.target` whose coordinates of index at least `d` vanish. -/
structure IsAnalyticChart (d : ℕ) (S : Set (Fin n → 𝕜))
    (e : OpenPartialHomeomorph (Fin n → 𝕜) (Fin n → 𝕜)) : Prop where
  /-- The chart is analytic on its source. -/
  analyticOnNhd : AnalyticOnNhd 𝕜 e e.source
  /-- The inverse of the chart is analytic on its target. -/
  analyticOnNhd_symm : AnalyticOnNhd 𝕜 e.symm e.target
  /-- The chart maps the part of `S` in its source onto the points of its target whose
  coordinates of index at least `d` vanish. -/
  isImage : e.IsImage S {y | ∀ i : Fin n, d ≤ i.val → y i = 0}

namespace IsAnalyticChart

/-- A point of the source of an analytic chart lies in `S` exactly when the coordinates of index
at least `d` of its image vanish. -/
theorem mem_iff (he : IsAnalyticChart d S e) (hx : x ∈ e.source) :
    x ∈ S ↔ ∀ i : Fin n, d ≤ i.val → e x i = 0 :=
  (he.isImage.apply_mem_iff hx).symm

/-- An analytic chart of `S` is an analytic chart of every set with the same points in its
source. -/
theorem congr_set (he : IsAnalyticChart d S e) (h : e.source ∩ S = e.source ∩ T) :
    IsAnalyticChart d T e :=
  ⟨he.analyticOnNhd, he.analyticOnNhd_symm,
    .of_preimage_eq (h ▸ he.isImage.preimage_eq)⟩

/-- The restriction of an analytic chart of `S` to an open set is an analytic chart of `S`. -/
theorem restrOpen (he : IsAnalyticChart d S e) (hU : IsOpen U) :
    IsAnalyticChart d S (e.restrOpen U hU) := by
  refine ⟨he.analyticOnNhd.mono inter_subset_left,
    he.analyticOnNhd_symm.mono inter_subset_left, fun x hx ↦ ?_⟩
  simpa using he.isImage hx.1

/-- The restriction of an analytic chart of `S` to an open set `U` is an analytic chart of
`S ∩ U`. -/
theorem restrOpen_inter (he : IsAnalyticChart d S e) (hU : IsOpen U) :
    IsAnalyticChart d (S ∩ U) (e.restrOpen U hU) :=
  (he.restrOpen hU).congr_set <| by
    ext
    simp only [OpenPartialHomeomorph.restrOpen_source, mem_inter_iff]
    tauto

/-- An analytic chart of `S ∩ U` whose source lies in `U` is an analytic chart of `S`. -/
theorem of_inter (he : IsAnalyticChart d (S ∩ U) e) (hU : e.source ⊆ U) :
    IsAnalyticChart d S e :=
  he.congr_set <| by
    ext x
    simp only [mem_inter_iff]
    exact ⟨fun h ↦ ⟨h.1, h.2.1⟩, fun h ↦ ⟨h.1, h.2, hU h.1⟩⟩

variable (he : IsAnalyticChart d S e) (hx : x ∈ e.source) (hxS : x ∈ S)
include he hx hxS

/-- The image of a point of `S` by an analytic chart is determined by its first `d`
coordinates. -/
theorem firstCoords_firstCoords_apply :
    firstCoords 𝕜 d n (firstCoords 𝕜 n d (e x)) = e x :=
  firstCoords_firstCoords_of_forall ((he.mem_iff hx).1 hxS)

/-- A point of `S` is recovered from the first `d` coordinates of its image by an analytic
chart. -/
theorem symm_firstCoords_firstCoords_apply :
    e.symm (firstCoords 𝕜 d n (firstCoords 𝕜 n d (e x))) = x := by
  rw [he.firstCoords_firstCoords_apply hx hxS, e.left_inv hx]

/-- The local parametrization `u ↦ e.symm (u, 0)` of `S` by an analytic chart is analytic at the
coordinates of each point of `S` in the source. -/
theorem analyticAt_symm_firstCoords :
    AnalyticAt 𝕜 (fun u ↦ e.symm (firstCoords 𝕜 d n u)) (firstCoords 𝕜 n d (e x)) :=
  (he.analyticOnNhd_symm _ (e.map_source hx)).comp_of_eq ((firstCoords 𝕜 d n).analyticAt _)
    (he.firstCoords_firstCoords_apply hx hxS)

/-- Near the coordinates of a point of `S`, the local parametrization `u ↦ e.symm (u, 0)` by an
analytic chart takes values in the part of `S` in the source of the chart. -/
theorem eventually_symm_firstCoords_mem :
    ∀ᶠ u in 𝓝 (firstCoords 𝕜 n d (e x)), e.symm (firstCoords 𝕜 d n u) ∈ e.source ∩ S := by
  have hcont := (firstCoords 𝕜 d n).continuous.continuousAt (x := firstCoords 𝕜 n d (e x))
  have ht : firstCoords 𝕜 d n ⁻¹' e.target ∈ 𝓝 (firstCoords 𝕜 n d (e x)) := by
    refine hcont.preimage_mem_nhds (e.open_target.mem_nhds ?_)
    rw [he.firstCoords_firstCoords_apply hx hxS]
    exact e.map_source hx
  filter_upwards [ht] with u hu
  refine ⟨e.map_target hu, (he.mem_iff (e.map_target hu)).2 fun i hi ↦ ?_⟩
  rw [e.right_inv hu]
  exact firstCoords_apply_of_le u hi

end IsAnalyticChart

/-- Let `e'` be an analytic chart of `T` in dimension `d'`. If `φ` is analytic at `u₀`, takes
values in `T` near `u₀`, and `φ u₀` lies in the source of `e'`, and if the coordinate expression of
`g` in `e'` is analytic at the coordinates of `φ u₀`, then `g ∘ φ` is analytic at `u₀`. -/
theorem IsAnalyticChart.analyticAt_comp {T : Set (Fin m → 𝕜)}
    {e' : OpenPartialHomeomorph (Fin m → 𝕜) (Fin m → 𝕜)} {g : (Fin m → 𝕜) → E} {φ : F → Fin m → 𝕜}
    {u₀ : F} (he' : IsAnalyticChart d' T e') (hφ : AnalyticAt 𝕜 φ u₀) (h₀ : φ u₀ ∈ e'.source)
    (hT : ∀ᶠ u in 𝓝 u₀, φ u ∈ T) (hg : AnalyticAt 𝕜 (fun v ↦ g (e'.symm (firstCoords 𝕜 d' m v)))
      (firstCoords 𝕜 m d' (e' (φ u₀)))) :
    AnalyticAt 𝕜 (g ∘ φ) u₀ := by
  -- the coordinates of `φ` in the chart `e'` are analytic
  have hτ : AnalyticAt 𝕜 (fun u ↦ firstCoords 𝕜 m d' (e' (φ u))) u₀ :=
    ((firstCoords 𝕜 m d').analyticAt _).comp ((he'.analyticOnNhd _ h₀).comp hφ)
  refine (hg.comp_of_eq hτ rfl).congr ?_
  filter_upwards [hT, hφ.continuousAt.preimage_mem_nhds (e'.open_source.mem_nhds h₀)] with u hu hu'
  simp only [Function.comp_apply]
  rw [he'.symm_firstCoords_firstCoords_apply hu' hu]

/-! ### Analytic submanifolds -/

/-- A set `S ⊆ 𝕜ⁿ` is a `d`-dimensional *analytic submanifold* if it is nonempty, `d ≤ n`, and
every point of `S` lies in the source of an analytic chart of `S` in dimension `d`. -/
structure IsAnalyticSubmanifold (d : ℕ) (S : Set (Fin n → 𝕜)) : Prop where
  /-- An analytic submanifold is nonempty. -/
  nonempty : S.Nonempty
  /-- The dimension of an analytic submanifold is at most that of the ambient space. -/
  le : d ≤ n
  /-- Every point of an analytic submanifold lies in the source of an analytic chart. -/
  exists_isAnalyticChart : ∀ x ∈ S, ∃ e, x ∈ e.source ∧ IsAnalyticChart d S e

/-- The subspace of the first `d` coordinates of `𝕜ⁿ` is a `d`-dimensional analytic
submanifold. -/
theorem isAnalyticSubmanifold_coordSubspace (h : d ≤ n) :
    IsAnalyticSubmanifold d {y : Fin n → 𝕜 | ∀ i : Fin n, d ≤ i.val → y i = 0} := by
  refine ⟨⟨0, fun _ _ ↦ rfl⟩, h, fun x _ ↦ ⟨OpenPartialHomeomorph.refl _, mem_univ x, ?_⟩⟩
  exact ⟨analyticOnNhd_id, analyticOnNhd_id, fun x _ ↦ Iff.rfl⟩

/-- A nonempty open subset of `𝕜ⁿ` is an `n`-dimensional analytic submanifold. -/
theorem _root_.IsOpen.isAnalyticSubmanifold (hU : IsOpen U) (hne : U.Nonempty) :
    IsAnalyticSubmanifold n U := by
  refine ⟨hne, le_rfl, fun x hx ↦ ⟨(OpenPartialHomeomorph.refl _).restrOpen U hU, ⟨trivial, hx⟩,
    ⟨analyticOnNhd_id, analyticOnNhd_id, fun y hy ↦ ?_⟩⟩⟩
  simpa [fun i : Fin n ↦ i.isLt.not_ge] using hy.2

/-- A point of `𝕜ⁿ` is a `0`-dimensional analytic submanifold. -/
theorem isAnalyticSubmanifold_singleton (a : Fin n → 𝕜) : IsAnalyticSubmanifold 0 {a} := by
  refine ⟨singleton_nonempty a, n.zero_le, fun x _ ↦
    ⟨(Homeomorph.addRight (-a)).toOpenPartialHomeomorph, mem_univ x, ?_⟩⟩
  refine ⟨fun _ _ ↦ analyticAt_id.add analyticAt_const,
    fun _ _ ↦ analyticAt_id.add analyticAt_const, fun y _ ↦ ?_⟩
  simp [← sub_eq_add_neg, sub_eq_zero, funext_iff]

/-- The intersection of an analytic submanifold with an open set meeting it is an analytic
submanifold of the same dimension. -/
theorem IsAnalyticSubmanifold.inter (hS : IsAnalyticSubmanifold d S) (hU : IsOpen U)
    (hne : (S ∩ U).Nonempty) : IsAnalyticSubmanifold d (S ∩ U) := by
  refine ⟨hne, hS.le, fun x hx ↦ ?_⟩
  obtain ⟨e, hxe, he⟩ := hS.exists_isAnalyticChart x hx.1
  exact ⟨e.restrOpen U hU, ⟨hxe, hx.2⟩, he.restrOpen_inter hU⟩

/-- A nonempty relatively open subset of an analytic submanifold is an analytic submanifold
of the same dimension. Relative openness is expressed using the subtype topology. -/
theorem IsAnalyticSubmanifold.of_isOpen_preimage_val (hS : IsAnalyticSubmanifold d S)
    (hTS : T ⊆ S) (hT : IsOpen (Subtype.val ⁻¹' T : Set S)) (hne : T.Nonempty) :
    IsAnalyticSubmanifold d T := by
  obtain ⟨U, hU, hUT⟩ := isOpen_induced_iff.mp hT
  have h : S ∩ U = T := by
    ext x
    constructor
    · rintro ⟨hxS, hxU⟩
      exact (Set.ext_iff.mp hUT ⟨x, hxS⟩).mp hxU
    · intro hxT
      exact ⟨hTS hxT, (Set.ext_iff.mp hUT ⟨x, hTS hxT⟩).mpr hxT⟩
  simpa only [h] using hS.inter hU (h.symm ▸ hne)

/-! ### Analytic functions on analytic submanifolds -/

/-- A function `f` on `𝕜ⁿ` is *analytic on* `S` in dimension `d` if every point `x ∈ S` lies in the
source of an analytic chart `e` of `S` in which the coordinate expression `u ↦ f (e.symm (u, 0))`,
a function of `u ∈ 𝕜ᵈ`, is analytic at the first `d` coordinates of `e x`. By
`TauCeti.AnalyticOnSubmanifold.analyticAt_chart`, the coordinate expression is then analytic in
every analytic chart around `x`. -/
def AnalyticOnSubmanifold (d : ℕ) (f : (Fin n → 𝕜) → E) (S : Set (Fin n → 𝕜)) : Prop :=
  ∀ x ∈ S, ∃ e : OpenPartialHomeomorph (Fin n → 𝕜) (Fin n → 𝕜), x ∈ e.source ∧
    IsAnalyticChart d S e ∧
      AnalyticAt 𝕜 (fun u ↦ f (e.symm (firstCoords 𝕜 d n u))) (firstCoords 𝕜 n d (e x))

/-- A function is analytic on `S` exactly when it has an analytic coordinate expression in
some analytic chart around every point of `S`. -/
theorem analyticOnSubmanifold_iff {f : (Fin n → 𝕜) → E} :
    AnalyticOnSubmanifold d f S ↔
      ∀ x ∈ S, ∃ e : OpenPartialHomeomorph (Fin n → 𝕜) (Fin n → 𝕜), x ∈ e.source ∧
        IsAnalyticChart d S e ∧
          AnalyticAt 𝕜 (fun u ↦ f (e.symm (firstCoords 𝕜 d n u)))
            (firstCoords 𝕜 n d (e x)) :=
  Iff.rfl

variable {f g : (Fin n → 𝕜) → E}

namespace AnalyticOnSubmanifold

/-- **Independence of the chart.** If `f` is analytic on `S`, its coordinate expression in every
analytic chart of `S` is analytic at the coordinates of every point of `S` in the source. -/
theorem analyticAt_chart (hf : AnalyticOnSubmanifold d f S) (hx : x ∈ S)
    (he : IsAnalyticChart d S e) (hxe : x ∈ e.source) :
    AnalyticAt 𝕜 (fun u ↦ f (e.symm (firstCoords 𝕜 d n u))) (firstCoords 𝕜 n d (e x)) := by
  obtain ⟨e', hxe', he', hf'⟩ := hf x hx
  -- compose the coordinate expression of `f` in `e'` with the parametrization of `S` by `e`
  have hx' := he.symm_firstCoords_firstCoords_apply hxe hx
  exact he'.analyticAt_comp (he.analyticAt_symm_firstCoords hxe hx) (by rwa [hx'])
    ((he.eventually_symm_firstCoords_mem hxe hx).mono fun _ hu ↦ hu.2) (by rwa [hx'])

/-- **Analyticity in coordinates.** If `f` is analytic on a set `S` in dimension `d ≤ n`, its
coordinate expression `u ↦ f (e.symm (u, 0))` in any analytic chart `e` of `S` is analytic on the
open subset of `𝕜ᵈ` where it is defined. -/
theorem analyticOnNhd (hf : AnalyticOnSubmanifold d f S) (he : IsAnalyticChart d S e)
    (hd : d ≤ n) : AnalyticOnNhd 𝕜 (fun u ↦ f (e.symm (firstCoords 𝕜 d n u)))
      (firstCoords 𝕜 d n ⁻¹' e.target) := by
  intro u hu
  have hxS : e.symm (firstCoords 𝕜 d n u) ∈ S :=
    (he.mem_iff (e.map_target hu)).2 fun i hi ↦ by
      rw [e.right_inv hu]
      exact firstCoords_apply_of_le u hi
  simpa [e.right_inv hu, hd] using hf.analyticAt_chart hxS he (e.map_target hu)

/-- Analyticity on `S` only depends on the values on `S`. -/
theorem congr (hf : AnalyticOnSubmanifold d f S) (hfg : EqOn f g S) :
    AnalyticOnSubmanifold d g S := by
  intro x hx
  obtain ⟨e, hxe, he, hf'⟩ := hf x hx
  refine ⟨e, hxe, he, hf'.congr ?_⟩
  filter_upwards [he.eventually_symm_firstCoords_mem hxe hx] with u hu
  exact hfg hu.2

/-- A function analytic on a submanifold has an ambient extension analytic at each point.
The extension agrees with the function on the submanifold in an open neighborhood. -/
theorem exists_analyticAt_eqOn (hf : AnalyticOnSubmanifold d f S) (hx : x ∈ S) :
    ∃ U, IsOpen U ∧ x ∈ U ∧ ∃ g : (Fin n → 𝕜) → E,
      AnalyticAt 𝕜 g x ∧ EqOn f g (S ∩ U) := by
  obtain ⟨e, hxe, he, hf'⟩ := hf x hx
  let g := fun y ↦ f (e.symm (firstCoords 𝕜 d n (firstCoords 𝕜 n d (e y))))
  have hτ : AnalyticAt 𝕜 (fun y ↦ firstCoords 𝕜 n d (e y)) x :=
    ((firstCoords 𝕜 n d).analyticAt _).comp (he.analyticOnNhd _ hxe)
  refine ⟨e.source, e.open_source, hxe, g, hf'.comp_of_eq hτ rfl, fun y hy ↦ ?_⟩
  dsimp [g]
  rw [he.symm_firstCoords_firstCoords_apply hy.2 hy.1]

/-- A function analytic on a submanifold of dimension `d ≤ n` has an ambient analytic
extension on an open neighborhood of each point. -/
theorem exists_analyticOnNhd_eqOn (hf : AnalyticOnSubmanifold d f S) (hd : d ≤ n) (hx : x ∈ S) :
    ∃ U, IsOpen U ∧ x ∈ U ∧ ∃ g : (Fin n → 𝕜) → E,
      AnalyticOnNhd 𝕜 g U ∧ EqOn f g (S ∩ U) := by
  obtain ⟨e, hxe, he, _⟩ := hf x hx
  let P := (firstCoords 𝕜 d n).comp (firstCoords 𝕜 n d)
  let U := e.source ∩ e ⁻¹' (P ⁻¹' e.target)
  have hU : IsOpen U := e.isOpen_inter_preimage (e.open_target.preimage P.continuous)
  have hxU : x ∈ U := by
    refine ⟨hxe, ?_⟩
    -- `P` is the projection onto the chart's tangent coordinates.
    change firstCoords 𝕜 d n (firstCoords 𝕜 n d (e x)) ∈ e.target
    rw [he.firstCoords_firstCoords_apply hxe hx]
    exact e.map_source hxe
  let g := fun y ↦ f (e.symm (firstCoords 𝕜 d n (firstCoords 𝕜 n d (e y))))
  refine ⟨U, hU, hxU, g, ?_, fun y hy ↦ ?_⟩
  · intro y hy
    have hτ : AnalyticAt 𝕜 (fun z ↦ firstCoords 𝕜 n d (e z)) y :=
      ((firstCoords 𝕜 n d).analyticAt _).comp (he.analyticOnNhd _ hy.1)
    exact (hf.analyticOnNhd he hd _ hy.2).comp_of_eq hτ rfl
  · dsimp [g]
    rw [he.symm_firstCoords_firstCoords_apply hy.2.1 hy.1]

/-- A function analytic on a submanifold is continuous on it. -/
theorem continuousOn (hf : AnalyticOnSubmanifold d f S) : ContinuousOn f S := by
  intro x hx
  obtain ⟨U, hU, hxU, g, hg, hfg⟩ := hf.exists_analyticAt_eqOn hx
  refine hg.continuousAt.continuousWithinAt.congr_of_eventuallyEq ?_ (hfg ⟨hx, hxU⟩)
  filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (hU.mem_nhds hxU)] with y hy hyU
  exact hfg ⟨hy, hyU⟩

/-- The restriction of an analytic function on `S` to the intersection of `S` with an open set is
analytic. -/
theorem inter (hf : AnalyticOnSubmanifold d f S) (hU : IsOpen U) :
    AnalyticOnSubmanifold d f (S ∩ U) := by
  intro x hx
  obtain ⟨e, hxe, he, hf'⟩ := hf x hx.1
  exact ⟨e.restrOpen U hU, ⟨hxe, hx.2⟩, he.restrOpen_inter hU, by simpa using hf'⟩

/-- A pair of analytic functions on `S` is analytic on `S`. -/
theorem prod {g : (Fin n → 𝕜) → F} (hf : AnalyticOnSubmanifold d f S)
    (hg : AnalyticOnSubmanifold d g S) : AnalyticOnSubmanifold d (fun x ↦ (f x, g x)) S := by
  intro x hx
  obtain ⟨e, hxe, he, hf'⟩ := hf x hx
  exact ⟨e, hxe, he, hf'.prod (hg.analyticAt_chart hx he hxe)⟩

/-- **Composition.** If `f` is analytic on `S` and maps `S` into a set `T`, and `g` is analytic on
`T` in dimension `d'`, then `g ∘ f` is analytic on `S`. No hypothesis on `T` is needed: `g` being
analytic on `T` already provides analytic charts of `T` around the values of `f`. -/
theorem comp {T : Set (Fin m → 𝕜)} {g : (Fin m → 𝕜) → E} {f : (Fin n → 𝕜) → Fin m → 𝕜}
    (hg : AnalyticOnSubmanifold d' g T) (hf : AnalyticOnSubmanifold d f S) (h : MapsTo f S T) :
    AnalyticOnSubmanifold d (g ∘ f) S := by
  intro x hx
  obtain ⟨e, hxe, he, hf'⟩ := hf x hx
  obtain ⟨e', hxe', he', hg'⟩ := hg (f x) (h hx)
  have hfx : f (e.symm (firstCoords 𝕜 d n (firstCoords 𝕜 n d (e x)))) = f x := by
    rw [he.symm_firstCoords_firstCoords_apply hxe hx]
  exact ⟨e, hxe, he, he'.analyticAt_comp hf' (by rwa [hfx])
    ((he.eventually_symm_firstCoords_mem hxe hx).mono fun _ hu ↦ h hu.2) (by rwa [hfx])⟩

end AnalyticOnSubmanifold

/-- On a set with analytic charts around each point, a function is analytic in dimension `d`
exactly when its coordinate expression in every analytic chart is analytic at the coordinates of
every point of the set in the source. -/
theorem IsAnalyticSubmanifold.analyticOnSubmanifold_iff (hS : IsAnalyticSubmanifold d S) :
    AnalyticOnSubmanifold d f S ↔ ∀ x ∈ S, ∀ e, IsAnalyticChart d S e → x ∈ e.source →
      AnalyticAt 𝕜 (fun u ↦ f (e.symm (firstCoords 𝕜 d n u))) (firstCoords 𝕜 n d (e x)) := by
  refine ⟨fun hf x hx e he hxe ↦ hf.analyticAt_chart hx he hxe, fun h x hx ↦ ?_⟩
  obtain ⟨e, hxe, he⟩ := hS.exists_isAnalyticChart x hx
  exact ⟨e, hxe, he, h x hx e he hxe⟩

/-- Analyticity on `S` only depends on the values on `S`. -/
theorem analyticOnSubmanifold_congr (hfg : EqOn f g S) :
    AnalyticOnSubmanifold d f S ↔ AnalyticOnSubmanifold d g S :=
  ⟨fun hf ↦ hf.congr hfg, fun hg ↦ hg.congr hfg.symm⟩

/-- **Locality.** A function analytic on a neighbourhood in `S` of each point of `S` is analytic
on `S`. -/
theorem analyticOnSubmanifold_of_locally_analyticOnSubmanifold
    (h : ∀ x ∈ S, ∃ U, IsOpen U ∧ x ∈ U ∧ AnalyticOnSubmanifold d f (S ∩ U)) :
    AnalyticOnSubmanifold d f S := by
  intro x hx
  obtain ⟨U, hU, hxU, hf⟩ := h x hx
  obtain ⟨e, hxe, he, hf'⟩ := hf x ⟨hx, hxU⟩
  exact ⟨e.restrOpen U hU, ⟨hxe, hxU⟩,
    (he.restrOpen hU).of_inter inter_subset_right, by simpa using hf'⟩

/-- A function analytic at each point of an analytic submanifold `S` of `𝕜ⁿ`, as a function on
`𝕜ⁿ`, is analytic on `S`. -/
theorem _root_.AnalyticOnNhd.analyticOnSubmanifold (hf : AnalyticOnNhd 𝕜 f S)
    (hS : IsAnalyticSubmanifold d S) : AnalyticOnSubmanifold d f S := by
  intro x hx
  obtain ⟨e, hxe, he⟩ := hS.exists_isAnalyticChart x hx
  exact ⟨e, hxe, he, (hf x hx).comp_of_eq (he.analyticAt_symm_firstCoords hxe hx)
    (he.symm_firstCoords_firstCoords_apply hxe hx)⟩

/-- The coefficients of a polynomial with multivariate polynomial coefficients, specialized
by evaluation on an analytic submanifold, are intrinsically analytic. -/
theorem IsAnalyticSubmanifold.analyticOnSubmanifold_coeff_map_eval
    (hS : IsAnalyticSubmanifold d S) (p : Polynomial (MvPolynomial (Fin n) 𝕜)) (j : ℕ) :
    AnalyticOnSubmanifold d (fun x ↦ (p.map (MvPolynomial.eval x)).coeff j) S := by
  simp only [Polynomial.coeff_map]
  exact ((AnalyticOnNhd.eval_continuousLinearMap
    (ContinuousLinearMap.id 𝕜 (Fin n → 𝕜)) (p.coeff j)).mono
      (Set.subset_univ S)).analyticOnSubmanifold hS

/-- The composition of an analytic function on `S` with a function analytic on a set containing
its values on `S` is analytic on `S`. -/
theorem _root_.AnalyticOnNhd.comp_analyticOnSubmanifold {g : E → F} {t : Set E}
    (hg : AnalyticOnNhd 𝕜 g t) (hf : AnalyticOnSubmanifold d f S) (h : MapsTo f S t) :
    AnalyticOnSubmanifold d (g ∘ f) S := by
  intro x hx
  obtain ⟨e, hxe, he, hf'⟩ := hf x hx
  refine ⟨e, hxe, he, (hg (f x) (h hx)).comp_of_eq hf' ?_⟩
  rw [he.symm_firstCoords_firstCoords_apply hxe hx]

end TauCeti
