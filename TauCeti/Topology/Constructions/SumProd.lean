/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.ClusterPt
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.Order.OrderClosed

/-!
# Interiors and fibres in product spaces

A subset of a product has empty interior if its vertical fibres over a dense set of base
points have empty interior. This lets fibrewise empty-interior results apply to subsets of
arbitrary topological products, without countability, separation, or finite-dimensionality
assumptions on either factor.
In particular, graphs with values in a space without isolated points have empty interior.
The interior of the preimage of a set under a projection is the preimage of its interior
(`TauCeti.interior_preimage_fst`, `TauCeti.interior_preimage_snd`), so the vertical and
horizontal lines through non-isolated points have empty interior.

The file also records the underlying function of the homeomorphism between functions on a
sum type and pairs of functions, and identifies a disjoint union of copies of one space, indexed by
a discrete space, with a product (`Homeomorph.sigmaEquivProd`).

Finally, a function on a product that is eventually constant near a point has eventually constant
slices through that point (`Filter.EventuallyEq.prodMk_right_nhds`,
`Filter.EventuallyEq.prodMk_left_nhds`). A map on `α × β`, with `α` linearly ordered, that is
equal to `(s, t) ↦ g t` on a closed half-space `s ≤ a` or `s ≥ a` agrees with it near every point
of the open half-space (`TauCeti.eventuallyEq_comp_snd_of_lt`,
`TauCeti.eventuallyEq_comp_snd_of_gt`). A function on a product that is continuous at every
point of the graph of a map over a set, where the map is continuous, restricts to a continuous map
on that graph (`TauCeti.continuousOn_comp_prodMk_of_continuousAt`,
`TauCeti.continuous_comp_prodMk_of_continuousAt`). A map of `X × Y` continuous on `univ ×ˢ S`
and sending it into `univ ×ˢ S'` restricts to a continuous map `X × S → X' × S'`
(`ContinuousOn.continuous_restrict_univ_prod`).
-/

public section

open Filter Set Topology

/-- The sum-to-product homeomorphism has the same underlying function as the corresponding
coordinate equivalence. -/
theorem Homeomorph.coe_sumArrowHomeomorphProdArrow {X ι ι' : Type*} [TopologicalSpace X] :
    ⇑(sumArrowHomeomorphProdArrow (X := X) (ι := ι) (ι' := ι')) =
      ⇑(Equiv.sumArrowEquivProdArrow ι ι' X) := (rfl)

/-- A disjoint union of copies of `X` indexed by a discrete space `ι` is homeomorphic to the
product `ι × X`. -/
def Homeomorph.sigmaEquivProd (ι X : Type*) [TopologicalSpace ι] [DiscreteTopology ι]
    [TopologicalSpace X] : (Σ _ : ι, X) ≃ₜ ι × X where
  toEquiv := Equiv.sigmaEquivProd ι X
  continuous_toFun := continuous_sigma fun i ↦ Continuous.prodMk_right i
  continuous_invFun := continuous_prod_of_discrete_left.2 fun i ↦
    continuous_sigmaMk (σ := fun _ : ι ↦ X) (i := i)

/-- `Homeomorph.sigmaEquivProd` sends the point `x` of the copy of index `i` to `(i, x)`. -/
@[simp]
theorem Homeomorph.sigmaEquivProd_apply {ι X : Type*} [TopologicalSpace ι] [DiscreteTopology ι]
    [TopologicalSpace X] (p : Σ _ : ι, X) : Homeomorph.sigmaEquivProd ι X p = (p.1, p.2) :=
  (rfl)

/-- The inverse of `Homeomorph.sigmaEquivProd` sends `(i, x)` to the point `x` of the copy of
index `i`. -/
@[simp]
theorem Homeomorph.sigmaEquivProd_symm_apply {ι X : Type*} [TopologicalSpace ι]
    [DiscreteTopology ι] [TopologicalSpace X] (p : ι × X) :
    (Homeomorph.sigmaEquivProd ι X).symm p = ⟨p.1, p.2⟩ :=
  (rfl)

/-- If `f` is eventually constant near `(x, y)`, then its slice `y' ↦ f (x, y')` is eventually
equal to `f (x, y)` near `y`. -/
theorem Filter.EventuallyEq.prodMk_right_nhds {X Y A : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {f : X × Y → A} {x : X} {y : Y} {a : A} (h : f =ᶠ[𝓝 (x, y)] fun _ ↦ a) :
    (fun y' ↦ f (x, y')) =ᶠ[𝓝 y] fun _ ↦ f (x, y) := by
  rw [h.self_of_nhds]
  exact h.comp_tendsto ((Continuous.prodMk_right x).tendsto y)

/-- If `f` is eventually constant near `(x, y)`, then its slice `x' ↦ f (x', y)` is eventually
equal to `f (x, y)` near `x`. -/
theorem Filter.EventuallyEq.prodMk_left_nhds {X Y A : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {f : X × Y → A} {x : X} {y : Y} {a : A} (h : f =ᶠ[𝓝 (x, y)] fun _ ↦ a) :
    (fun x' ↦ f (x', y)) =ᶠ[𝓝 x] fun _ ↦ f (x, y) := by
  rw [h.self_of_nhds]
  exact h.comp_tendsto ((Continuous.prodMk_left y).tendsto x)

/-- A map `f : X × Y → X' × Y'` that is continuous on `univ ×ˢ S` and sends it into
`univ ×ˢ S'` restricts to a continuous map `X × S → X' × S'`. -/
theorem ContinuousOn.continuous_restrict_univ_prod {X Y X' Y' : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [TopologicalSpace X'] [TopologicalSpace Y'] {S : Set Y} {S' : Set Y'}
    {f : X × Y → X' × Y'} (hf : ContinuousOn f (univ ×ˢ S))
    (hmaps : ∀ x : X × S, (f (x.1, x.2)).2 ∈ S') :
    Continuous fun x : X × S ↦ ((f (x.1, x.2)).1, (⟨(f (x.1, x.2)).2, hmaps x⟩ : S')) := by
  have h := hf.comp_continuous (continuous_fst.prodMk (continuous_subtypeVal.comp continuous_snd))
    fun x ↦ ⟨mem_univ _, x.2.property⟩
  exact (continuous_fst.comp h).prodMk ((continuous_snd.comp h).subtype_mk hmaps)

namespace TauCeti

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- If `F` is continuous at every point `(x, u x)` with `x ∈ s` and `u` is continuous on `s`,
then `x ↦ F (x, u x)` is continuous on `s`. -/
theorem continuousOn_comp_prodMk_of_continuousAt {Z : Type*} [TopologicalSpace Z]
    {F : X × Y → Z} {u : X → Y} {s : Set X} (hF : ∀ x ∈ s, ContinuousAt F (x, u x))
    (hu : ContinuousOn u s) : ContinuousOn (fun x ↦ F (x, u x)) s :=
  fun x hx ↦ (hF x hx).comp₂_continuousWithinAt continuousWithinAt_id (hu x hx)

/-- If `F` is continuous at every point `(x, u x)` of the graph of a continuous map `u`, then
`x ↦ F (x, u x)` is continuous. -/
theorem continuous_comp_prodMk_of_continuousAt {Z : Type*} [TopologicalSpace Z] {F : X × Y → Z}
    {u : X → Y} (hF : ∀ x, ContinuousAt F (x, u x)) (hu : Continuous u) :
    Continuous fun x ↦ F (x, u x) :=
  continuousOn_univ.1 <|
    continuousOn_comp_prodMk_of_continuousAt (fun x _ ↦ hF x) hu.continuousOn

/-- If `f (s, t) = g t` for `s ≤ a`, then `f` agrees with `(s, t) ↦ g t` near every point with
`s < a`. -/
theorem eventuallyEq_comp_snd_of_lt {α E : Type*} [TopologicalSpace α] [LinearOrder α]
    [OrderClosedTopology α] {f : α × Y → E} {g : Y → E} {a : α}
    (h : ∀ s ≤ a, ∀ t, f (s, t) = g t) {z : α × Y} (hz : z.1 < a) :
    f =ᶠ[𝓝 z] fun w ↦ g w.2 :=
  Filter.eventually_of_mem ((isOpen_lt continuous_fst continuous_const).mem_nhds
    (show z ∈ {w : α × Y | w.1 < a} from hz)) fun w hw ↦ h w.1 (le_of_lt hw) w.2

/-- If `f (s, t) = g t` for `s ≥ a`, then `f` agrees with `(s, t) ↦ g t` near every point with
`s > a`. -/
theorem eventuallyEq_comp_snd_of_gt {α E : Type*} [TopologicalSpace α] [LinearOrder α]
    [OrderClosedTopology α] {f : α × Y → E} {g : Y → E} {a : α}
    (h : ∀ s, a ≤ s → ∀ t, f (s, t) = g t) {z : α × Y} (hz : a < z.1) :
    f =ᶠ[𝓝 z] fun w ↦ g w.2 :=
  Filter.eventually_of_mem ((isOpen_lt continuous_const continuous_fst).mem_nhds
    (show z ∈ {w : α × Y | a < w.1} from hz)) fun w hw ↦ h w.1 (le_of_lt hw) w.2

/-- A subset of a product has empty interior if its vertical fibres over a dense set of base
points have empty interior. -/
theorem interior_eq_empty_of_dense_setOf_interior_preimage_prodMk_eq_empty {s : Set (X × Y)}
    (hs : Dense {x | interior (Prod.mk x ⁻¹' s) = ∅}) : interior s = ∅ := by
  by_contra h
  obtain ⟨_, hx, ⟨x, y⟩, hxy, rfl⟩ := hs.exists_mem_open (isOpenMap_fst _ isOpen_interior)
    ((ne_empty_iff_nonempty.mp h).image _)
  exact hx.le (preimage_interior_subset_interior_preimage (Continuous.prodMk_right x) hxy)

/-- A subset of a product has empty interior if every vertical fibre has empty interior. -/
theorem interior_eq_empty_of_forall_interior_preimage_prodMk_eq_empty {s : Set (X × Y)}
    (hs : ∀ x, interior (Prod.mk x ⁻¹' s) = ∅) : interior s = ∅ :=
  interior_eq_empty_of_dense_setOf_interior_preimage_prodMk_eq_empty <| by simp [hs]

/-- A graph with values in a space without isolated points has empty interior, even when
neither the function nor its domain is open or continuous. -/
@[simp]
theorem _root_.Set.interior_graphOn [∀ y : Y, NeBot (𝓝[≠] y)] (s : Set X) (f : X → Y) :
    interior (s.graphOn f) = ∅ := by
  refine interior_eq_empty_of_forall_interior_preimage_prodMk_eq_empty fun x ↦ ?_
  have hsub : Prod.mk x ⁻¹' s.graphOn f ⊆ {f x} := fun y hy ↦ (mem_graphOn.mp hy).2.symm
  simpa using interior_mono hsub

/-- The interior of the preimage of a set under the first projection is the preimage of its
interior. -/
theorem interior_preimage_fst (s : Set X) :
    interior (Prod.fst ⁻¹' s : Set (X × Y)) = Prod.fst ⁻¹' interior s :=
  (isOpenMap_fst.preimage_interior_eq_interior_preimage continuous_fst s).symm

/-- The interior of the preimage of a set under the second projection is the preimage of its
interior. -/
theorem interior_preimage_snd (s : Set Y) :
    interior (Prod.snd ⁻¹' s : Set (X × Y)) = Prod.snd ⁻¹' interior s :=
  (isOpenMap_snd.preimage_interior_eq_interior_preimage continuous_snd s).symm

/-- A vertical line `{x} × Y` through a non-isolated point `x` has empty interior. -/
theorem interior_preimage_fst_singleton (x : X) [NeBot (𝓝[≠] x)] :
    interior (Prod.fst ⁻¹' {x} : Set (X × Y)) = ∅ := by
  rw [interior_preimage_fst, interior_singleton, preimage_empty]

/-- A horizontal line `X × {y}` through a non-isolated point `y` has empty interior. -/
theorem interior_preimage_snd_singleton (y : Y) [NeBot (𝓝[≠] y)] :
    interior (Prod.snd ⁻¹' {y} : Set (X × Y)) = ∅ := by
  rw [interior_preimage_snd, interior_singleton, preimage_empty]

end TauCeti
