/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Geometry.Manifold.Diffeomorph
public import TauCeti.GroupTheory.Perm.Basic
public import TauCeti.Geometry.Manifold.Instances.Comap
public import TauCeti.Topology.ConnectedComponents
public import TauCeti.Topology.Constructions.FiniteGluing

/-!
# Prestable complex curves

A compact nodal complex curve is assembled from smooth pieces: take a compact complex curve `Σ`,
its *normalization*, choose finitely many pairs of distinct points of `Σ`, the two *flags* (or
branches) of each node, and identify the two points of each pair. A *prestable curve* also
carries ordered distinct marked points away from the flags, and is required to be connected.
The normalization itself may be disconnected; its connected components are the normalized
components of the curve. Since `Σ` is compact and locally connected, it has finitely many of
them. A self-node is a pair of flags lying on the same component.

This file sets up that carrier.

* `TauCeti.PrestableCurve ι` is the structure of a prestable curve with marked points indexed by
  `ι`. Its node data is the involution `pairing` of the normalization exchanging the two flags of
  each node and fixing every other point; the flags are the finitely many points it moves.
* `TauCeti.PrestableCurve.Carrier` is the underlying topological space of the curve, the quotient
  of the normalization identifying each flag with its partner, and `PrestableCurve.proj` is the
  normalization map. The carrier is compact, Hausdorff and connected.
* `TauCeti.PrestableCurve.nodes` is the finite set of nodes, the image of the flags, and
  `TauCeti.PrestableCurve.smoothLocus` is its open complement.
* The smooth locus carries the complex structure transported from the complement of the flags
  in the normalization, and `TauCeti.PrestableCurve.smoothLocusDiffeomorph` is the normalization
  map on that complement, a biholomorphism onto the smooth locus. The marked points lie in the
  smooth locus (`TauCeti.PrestableCurve.markPoint`).
* `TauCeti.PrestableCurve.ComponentAdj` is the adjacency of the dual graph on the components of
  the normalization, and `TauCeti.PrestableCurve.reflTransGen_componentAdj` says that the dual
  graph is connected, since the curve is: any two components are joined by a chain of
  components, consecutive ones carrying the two flags of a node. The equivalence of the two
  conditions is the general `Setoid.preconnectedSpace_quotient_iff`.
* `TauCeti.PrestableCurve.ofSmooth` is a smooth connected curve with no nodes, and
  `TauCeti.PrestableCurve.selfNode` is the irreducible curve obtained from a connected curve by
  gluing two of its points to a single node.

Stability is not imposed: rational components with at most two special points and unmarked
elliptic components are allowed, as they are needed for moduli of maps.

## References

* Joel W. Robbin and Dietmar A. Salamon, *A construction of the Deligne–Mumford orbifold*,
  J. Eur. Math. Soc. 8 (2006), 611–699, for nodal Riemann surfaces presented as smooth surfaces
  with marked points and a fixed-point-free involution of a finite set of nodal points.
-/

public noncomputable section

open Set Topology TopologicalSpace
open scoped Manifold ContDiff

namespace TauCeti

universe u v

/-- A compact prestable nodal complex curve with marked points indexed by `ι`.

It is given by its normalization, a compact complex curve whose connected components are the
normalized components of the curve, together with the involution `pairing` exchanging the two
flags of each node and fixing every other point. The flags are the finitely many points moved by
`pairing`; a node is a pair of distinct flags, possibly on the same component. The marked points
are distinct and are not flags, and the curve obtained by identifying each flag with its partner
is connected. -/
structure PrestableCurve (ι : Type v) where
  /-- The normalization of the curve, a compact complex curve which may be disconnected. -/
  Normalization : Type u
  /-- The topology of the normalization. -/
  [topologicalSpace : TopologicalSpace Normalization]
  /-- The complex charts of the normalization. -/
  [chartedSpace : ChartedSpace ℂ Normalization]
  /-- The normalization is a complex manifold. -/
  [isManifold : IsManifold 𝓘(ℂ) ω Normalization]
  /-- The normalization is compact. -/
  [compactSpace : CompactSpace Normalization]
  /-- The normalization is Hausdorff. -/
  [t2Space : T2Space Normalization]
  /-- The involution exchanging the two flags of each node and fixing every other point. -/
  pairing : Normalization → Normalization
  /-- The pairing is an involution. -/
  pairing_involutive : Function.Involutive pairing
  /-- There are only finitely many flags. -/
  finite_setOf_pairing_ne : {x | pairing x ≠ x}.Finite
  /-- The marked points, which are distinct. -/
  mark : ι ↪ Normalization
  /-- No marked point is a flag. -/
  pairing_mark (i : ι) : pairing (mark i) = mark i
  /-- The curve obtained by identifying each flag with its partner is connected. -/
  connectedSpace :
    ConnectedSpace (Quotient (Equiv.Perm.SameCycle.setoid (pairing_involutive.toPerm pairing)))

namespace PrestableCurve

variable {ι : Type v} (C : PrestableCurve.{u} ι)

instance : TopologicalSpace C.Normalization := C.topologicalSpace
instance : ChartedSpace ℂ C.Normalization := C.chartedSpace
instance : IsManifold 𝓘(ℂ) ω C.Normalization := C.isManifold
instance : CompactSpace C.Normalization := C.compactSpace
instance : T2Space C.Normalization := C.t2Space

instance : LocallyConnectedSpace C.Normalization := ChartedSpace.locallyConnectedSpace ℂ _

/-! ### Flags -/

/-- The flags of the curve: the points of the normalization lying over a node. -/
def flags : Set C.Normalization :=
  {x | C.pairing x ≠ x}

variable {C}

theorem mem_flags {x : C.Normalization} : x ∈ C.flags ↔ C.pairing x ≠ x :=
  Iff.rfl

@[simp]
theorem pairing_pairing (x : C.Normalization) : C.pairing (C.pairing x) = x :=
  C.pairing_involutive x

/-- The partner of a flag is a flag. -/
@[simp]
theorem pairing_mem_flags {x : C.Normalization} : C.pairing x ∈ C.flags ↔ x ∈ C.flags := by
  simp only [mem_flags, pairing_pairing, ne_eq]
  exact not_congr eq_comm

theorem pairing_eq_self_of_notMem_flags {x : C.Normalization} (hx : x ∉ C.flags) :
    C.pairing x = x :=
  not_not.1 hx

variable (C)

theorem finite_flags : C.flags.Finite :=
  C.finite_setOf_pairing_ne

/-- No marked point is a flag. -/
theorem mark_notMem_flags (i : ι) : C.mark i ∉ C.flags :=
  fun h ↦ h (C.pairing_mark i)

/-! ### The carrier -/

/-- The equivalence relation on the normalization identifying each flag with its partner. -/
def nodeSetoid : Setoid C.Normalization :=
  Equiv.Perm.SameCycle.setoid (C.pairing_involutive.toPerm C.pairing)

variable {C} in
theorem nodeSetoid_iff {x y : C.Normalization} : C.nodeSetoid x y ↔ x = y ∨ x = C.pairing y :=
  sameCycle_toPerm_iff C.pairing C.pairing_involutive x y

/-- The relation `nodeSetoid` relates distinct points only if they are flags. -/
theorem mem_flags_of_nodeSetoid ⦃x y : C.Normalization⦄ (hxy : C.nodeSetoid x y) (hne : x ≠ y) :
    x ∈ C.flags := by
  rcases nodeSetoid_iff.1 hxy with h | h
  · exact absurd h hne
  · rw [mem_flags, h, pairing_pairing]
    exact fun h' ↦ hne (h.trans h'.symm)

/-- The underlying topological space of the curve: the normalization with each flag identified
with its partner. -/
def Carrier : Type u :=
  Quotient C.nodeSetoid

instance : TopologicalSpace C.Carrier :=
  inferInstanceAs (TopologicalSpace (Quotient C.nodeSetoid))

instance : CompactSpace C.Carrier :=
  inferInstanceAs (CompactSpace (Quotient C.nodeSetoid))

instance : T2Space C.Carrier :=
  Setoid.t2Space_quotient C.nodeSetoid C.finite_flags C.mem_flags_of_nodeSetoid

instance : ConnectedSpace C.Carrier :=
  C.connectedSpace

/-- The normalization map, sending a point of the normalization to its image in the curve. -/
def proj : C.Normalization → C.Carrier :=
  Quotient.mk C.nodeSetoid

theorem isQuotientMap_proj : IsQuotientMap C.proj :=
  isQuotientMap_quotient_mk'

@[continuity, fun_prop]
theorem continuous_proj : Continuous C.proj :=
  continuous_quotient_mk'

theorem surjective_proj : Function.Surjective C.proj :=
  Quotient.mk_surjective

/-- The normalization map is closed. -/
theorem isClosedMap_proj : IsClosedMap C.proj :=
  Setoid.isClosedMap_quotient_mk C.nodeSetoid C.finite_flags C.mem_flags_of_nodeSetoid

variable {C} in
/-- Two points of the normalization have the same image exactly when they are equal or are the two
flags of a node. -/
theorem proj_eq_proj_iff {x y : C.Normalization} : C.proj x = C.proj y ↔ x = y ∨ x = C.pairing y :=
  Quotient.eq.trans nodeSetoid_iff

@[simp]
theorem proj_pairing (x : C.Normalization) : C.proj (C.pairing x) = C.proj x :=
  proj_eq_proj_iff.2 (Or.inr rfl)

/-- The normalization is nonempty, since the curve is. -/
instance : Nonempty C.Normalization :=
  (nonempty_quotient_iff C.nodeSetoid).1 (inferInstanceAs (Nonempty C.Carrier))

/-! ### Nodes and the smooth locus -/

/-- The nodes of the curve: the images of the flags. -/
def nodes : Set C.Carrier :=
  C.proj '' C.flags

theorem finite_nodes : C.nodes.Finite :=
  C.finite_flags.image C.proj

theorem isClosed_nodes : IsClosed C.nodes :=
  C.finite_nodes.isClosed

variable {C} in
/-- A point of the normalization lies over a node exactly when it is a flag. -/
@[simp]
theorem proj_mem_nodes_iff {x : C.Normalization} : C.proj x ∈ C.nodes ↔ x ∈ C.flags := by
  refine ⟨?_, mem_image_of_mem C.proj⟩
  rintro ⟨y, hy, hyx⟩
  rcases proj_eq_proj_iff.1 hyx with rfl | rfl
  exacts [hy, pairing_mem_flags.1 hy]

/-- The smooth locus of the curve: the open complement of the nodes. -/
def smoothLocus : Opens C.Carrier :=
  ⟨C.nodesᶜ, C.isClosed_nodes.isOpen_compl⟩

variable {C} in
@[simp]
theorem mem_smoothLocus {q : C.Carrier} : q ∈ C.smoothLocus ↔ q ∉ C.nodes :=
  Iff.rfl

/-- The complement of the flags, the open part of the normalization mapped onto the smooth
locus. -/
def smoothNormalization : Opens C.Normalization :=
  ⟨C.flagsᶜ, C.finite_flags.isClosed.isOpen_compl⟩

variable {C} in
@[simp]
theorem mem_smoothNormalization {x : C.Normalization} :
    x ∈ C.smoothNormalization ↔ x ∉ C.flags :=
  Iff.rfl

/-- The normalization map restricted to the complement of the flags is an open embedding. -/
theorem isOpenEmbedding_proj_smoothNormalization :
    IsOpenEmbedding fun x : C.smoothNormalization ↦ C.proj x :=
  Setoid.isOpenEmbedding_domRestrict_quotient_mk C.nodeSetoid C.finite_flags
    C.mem_flags_of_nodeSetoid

theorem range_proj_smoothNormalization :
    range (fun x : C.smoothNormalization ↦ C.proj x) = C.smoothLocus := by
  exact (image_eq_range _ _).symm.trans
    (Setoid.image_quotient_mk_compl C.nodeSetoid C.mem_flags_of_nodeSetoid)

/-- The normalization map is a homeomorphism from the complement of the flags onto the smooth
locus. -/
def smoothLocusHomeomorph : C.smoothNormalization ≃ₜ C.smoothLocus :=
  C.isOpenEmbedding_proj_smoothNormalization.isEmbedding.toHomeomorph.trans
    (Homeomorph.setCongr C.range_proj_smoothNormalization)

@[simp]
theorem coe_smoothLocusHomeomorph (x : C.smoothNormalization) :
    (C.smoothLocusHomeomorph x : C.Carrier) = C.proj x :=
  (rfl)

/-! ### The complex structure on the smooth locus -/

/-- The complex charts of the smooth locus, transported from the complement of the flags along
the normalization map. -/
instance : ChartedSpace ℂ C.smoothLocus :=
  C.smoothLocusHomeomorph.symm.isLocalHomeomorph.chartedSpaceComap

/-- The smooth locus of the curve is a complex manifold. -/
instance : IsManifold 𝓘(ℂ) ω C.smoothLocus :=
  C.smoothLocusHomeomorph.symm.isLocalHomeomorph.isManifold_chartedSpaceComap

/-- The normalization map is a biholomorphism from the complement of the flags onto the smooth
locus. -/
def smoothLocusDiffeomorph : C.smoothNormalization ≃ₘ^ω⟮𝓘(ℂ), 𝓘(ℂ)⟯ C.smoothLocus where
  toEquiv := C.smoothLocusHomeomorph.toEquiv
  contMDiff_toFun :=
    (C.smoothLocusHomeomorph.symm.isLocalHomeomorph.contMDiff_chartedSpaceComap_iff.2
      ⟨C.smoothLocusHomeomorph.continuous,
        contMDiff_id.congr C.smoothLocusHomeomorph.symm_apply_apply⟩)
  contMDiff_invFun := C.smoothLocusHomeomorph.symm.isLocalHomeomorph.contMDiff_chartedSpaceComap

@[simp]
theorem coe_smoothLocusDiffeomorph (x : C.smoothNormalization) :
    (C.smoothLocusDiffeomorph x : C.Carrier) = C.proj x :=
  (rfl)

@[simp]
theorem smoothLocusDiffeomorph_toHomeomorph :
    C.smoothLocusDiffeomorph.toHomeomorph = C.smoothLocusHomeomorph :=
  (rfl)

/-! ### Marked points -/

/-- The `i`-th marked point of the curve, a point of the smooth locus. -/
def markPoint (i : ι) : C.smoothLocus :=
  C.smoothLocusDiffeomorph ⟨C.mark i, C.mark_notMem_flags i⟩

@[simp]
theorem coe_markPoint (i : ι) : (C.markPoint i : C.Carrier) = C.proj (C.mark i) :=
  (rfl)

/-- The marked points of the curve are distinct. -/
theorem markPoint_injective : Function.Injective C.markPoint := fun _ _ h ↦
  C.mark.injective (congrArg Subtype.val (C.smoothLocusDiffeomorph.injective h))

/-! ### Connectedness and the dual graph -/

/-- Two connected components of the normalization are adjacent when the first carries a flag whose
partner lies on the second: they are joined by an edge of the dual graph. A component carrying
both flags of a self-node is adjacent to itself. -/
def ComponentAdj (a b : ConnectedComponents C.Normalization) : Prop :=
  ∃ x ∈ C.flags, ConnectedComponents.mk x = a ∧ ConnectedComponents.mk (C.pairing x) = b

variable {C} in
theorem componentAdj_iff {a b : ConnectedComponents C.Normalization} :
    C.ComponentAdj a b ↔
      ∃ x ∈ C.flags, ConnectedComponents.mk x = a ∧ ConnectedComponents.mk (C.pairing x) = b :=
  Iff.rfl

variable {C} in
theorem ComponentAdj.symm {a b : ConnectedComponents C.Normalization} (h : C.ComponentAdj a b) :
    C.ComponentAdj b a := by
  obtain ⟨x, hx, rfl, rfl⟩ := h
  exact ⟨C.pairing x, pairing_mem_flags.2 hx, rfl, by rw [pairing_pairing]⟩

/-- **Connectedness of the dual graph.** Any two connected components of the normalization are
joined by a finite chain of components, consecutive ones carrying the two flags of a node. -/
theorem reflTransGen_componentAdj (a b : ConnectedComponents C.Normalization) :
    Relation.ReflTransGen C.ComponentAdj a b := by
  have : PreconnectedSpace (Quotient C.nodeSetoid) := inferInstanceAs (PreconnectedSpace C.Carrier)
  refine Relation.reflTransGen_closed ?_ a b
    (C.nodeSetoid.reflTransGen_of_preconnectedSpace_quotient a b)
  rintro a b ⟨x, y, hxy, rfl, rfl⟩
  rcases nodeSetoid_iff.1 hxy with rfl | rfl
  · exact Relation.ReflTransGen.refl
  by_cases hy : y ∈ C.flags
  · exact Relation.ReflTransGen.single (ComponentAdj.symm ⟨y, hy, rfl, rfl⟩)
  · rw [pairing_eq_self_of_notMem_flags hy]

/-! ### Examples -/

section Examples

variable (X : Type u) [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
  [CompactSpace X] [T2Space X] [ConnectedSpace X]

/-- A compact connected complex curve with marked points, as a prestable curve without nodes. -/
abbrev ofSmooth (mark : ι ↪ X) : PrestableCurve.{u} ι where
  Normalization := X
  pairing := id
  pairing_involutive _ := rfl
  finite_setOf_pairing_ne := by simp
  mark := mark
  pairing_mark _ := rfl
  connectedSpace := inferInstance

@[simp]
theorem flags_ofSmooth (mark : ι ↪ X) : (ofSmooth X mark).flags = ∅ :=
  eq_empty_iff_forall_notMem.2 fun _ hx ↦ hx rfl

@[simp]
theorem nodes_ofSmooth (mark : ι ↪ X) : (ofSmooth X mark).nodes = ∅ := by
  rw [nodes, flags_ofSmooth, image_empty]

variable {X} [DecidableEq X]

/-- The irreducible curve obtained from a compact connected complex curve by gluing two points
`p` and `q` to a single node, with marked points away from `p` and `q`. When `p = q` nothing is
glued. -/
abbrev selfNode {p q : X} (mark : ι ↪ X) (hp : ∀ i, mark i ≠ p)
    (hq : ∀ i, mark i ≠ q) : PrestableCurve.{u} ι where
  Normalization := X
  pairing := Equiv.swap p q
  pairing_involutive := Equiv.swap_apply_self p q
  finite_setOf_pairing_ne := (Set.toFinite {p, q}).subset fun _ hx ↦ by
    simpa using Equiv.eq_or_eq_of_swap_apply_ne_self hx
  mark := mark
  pairing_mark i := Equiv.swap_apply_of_ne_of_ne (hp i) (hq i)
  connectedSpace := inferInstance

variable {p q : X} (mark : ι ↪ X) (hp : ∀ i, mark i ≠ p) (hq : ∀ i, mark i ≠ q)

/-- The flags of the self-node curve are the two glued points. -/
@[simp]
theorem flags_selfNode (hpq : p ≠ q) : (selfNode mark hp hq).flags = {p, q} := by
  ext x
  simp [flags, Equiv.swap_apply_ne_self_iff, hpq]

/-- The self-node curve has a single node. -/
theorem nodes_selfNode (hpq : p ≠ q) :
    (selfNode mark hp hq).nodes = {(selfNode mark hp hq).proj p} := by
  have h : (selfNode mark hp hq).proj q = (selfNode mark hp hq).proj p := by
    simpa using proj_pairing (selfNode mark hp hq) p
  rw [nodes, flags_selfNode mark hp hq hpq, image_pair, h, pair_eq_singleton]

end Examples

end PrestableCurve

end TauCeti
