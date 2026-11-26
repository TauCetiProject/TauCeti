/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.Quasicategory.Nerve
public import TauCeti.AlgebraicTopology.Quasicategory.CoCartesian
public import TauCeti.AlgebraicTopology.Quasicategory.Postcomposition
public import TauCeti.AlgebraicTopology.SimplicialSet.WeakEquivalence
public import TauCeti.CategoryTheory.Category.Pointed.Fin

/-!
# `∞`-operads

An `∞`-operad is a map `p : O^⊗ ⟶ N(Fin_*)` to the nerve of the category `TauCeti.FinPointed` of
finite pointed sets `⟨n⟩ = Fin (n + 1)` such that

1. `p` is an inner fibration;
2. every inert map `⟨m⟩ ⟶ ⟨n⟩` lifts to a `p`-coCartesian edge with any specified source over
   `⟨m⟩`;
3. every family `c₁, …, cₙ` of *colors*, vertices over `⟨1⟩`, is reached from a single vertex `y`
   over `⟨n⟩` by `p`-coCartesian lifts `y ⟶ cᵢ` of the inert projections `ρ i : ⟨n⟩ ⟶ ⟨1⟩`;
4. for such lifts, every vertex `x` and every edge `e : p x ⟶ p y` of `N(Fin_*)`, postcomposition
   with the lifts is a weak equivalence `Hom^R(x, y)_e ⟶ ∏ᵢ Hom^R(x, cᵢ)_{ρ i ∘ e}` from the
   space of maps lying over `e` to the product of the spaces of maps lying over the composites.

Here `Hom^R_X(x, y)_e`, the fiber over `e` of the map of right mapping spaces
`Hom^R_X(x, y) ⟶ Hom^R_S(p x, p y)` induced by `p : X ⟶ S`, is the space of maps from `x` to `y`
lying over `e` (`SSet.rightMappingSpaceOver`). For a base which is the nerve of a category,
postcomposition with an edge `g` of `X` (`SSet.rightMappingSpace.postcomp`) restricts to these
spaces (`SSet.rightMappingSpaceOver.postcomp`), since the right mapping spaces of a nerve are
discrete.

Condition 4 is asked for every choice of the lifts in condition 3. Lifts of `ρ i` with the same
source are unique up to equivalence, so asking it for one choice amounts to the same condition,
but that comparison is not proved here. The map in condition 4 is built from the postcomposition
maps `SSet.rightMappingSpace.postcomp`, which are well defined up to homotopy.

The vertex `y` of condition 3 represents the tuple `(c₁, …, cₙ)`, and the multi-operations from
`(c₁, …, cₙ)` to a color `z` are the maps `y ⟶ z` lying over the fold map `⟨n⟩ ⟶ ⟨1⟩`
(`SSet.InertProjectionLifts.mulSpace`). Condition 4 is the requirement that a map into a tuple is
a tuple of maps; for `n = 0` it says that the spaces of maps into a vertex over `⟨0⟩` are
contractible.

A map of `∞`-operads from `p` to `q` is a map over `N(Fin_*)` sending the `p`-coCartesian edges
lying over inert maps to `q`-coCartesian edges (`SSet.InfinityOperad.Hom`). Between symmetric
monoidal quasicategories these are the lax symmetric monoidal functors.

## Main definitions

* `TauCeti.FinPointed.vertex n`: the vertex `⟨n⟩` of `N(Fin_*)`.
* `SSet.InertProjectionLifts p n y`: `p`-coCartesian lifts `y ⟶ cᵢ` of the inert projections
  `ρ i : ⟨n⟩ ⟶ ⟨1⟩`, with their colors `cᵢ`.
* `SSet.InertProjectionLifts.segalMap`: the map `Hom^R(x, y)_e ⟶ ∏ᵢ Hom^R(x, cᵢ)_{ρ i ∘ e}`.
* `SSet.InertProjectionLifts.mulSpace`: the space of multi-operations from the colors `cᵢ` to a
  color `z`.
* `SSet.InfinityOperad p`: the map `p : O^⊗ ⟶ N(Fin_*)` is an `∞`-operad.
* `SSet.InfinityOperad.Hom p q`: maps of `∞`-operads, with their identities, composites,
  underlying maps of colors and action on multi-operation spaces.

## Main results

* `SSet.InfinityOperad.of_isIso`: an isomorphism onto `N(Fin_*)` is an `∞`-operad; for instance
  the identity of `N(Fin_*)`, the commutative `∞`-operad.
* `SSet.not_infinityOperad_of_not_nonempty`: the empty simplicial set over `N(Fin_*)` is not an
  `∞`-operad, since it has no vertex representing the empty tuple of colors.

## References

* J. Lurie, *Higher Algebra*, Definition 2.1.1.10, Remark 2.1.1.17 (multimorphism spaces) and
  Definition 2.1.2.7 (maps of `∞`-operads).
-/

public section

universe u

open CategoryTheory Limits HomotopicalAlgebra Opposite Simplicial TauCeti

open scoped SSet.modelCategoryQuillen

/-- The vertex `⟨n⟩` of the nerve `N(Fin_*)` of `FinPointed`. -/
abbrev TauCeti.FinPointed.vertex (n : FinPointed.{u}) : (nerve FinPointed.{u}) _⦋0⦌ :=
  nerveEquiv.symm n

namespace SSet

variable {X Y Z : SSet.{u}}

/-! ### Lifts of the inert projections -/

/-- `p`-coCartesian lifts `y ⟶ cᵢ` of the inert projections `ρ i : ⟨n⟩ ⟶ ⟨1⟩`, starting at a
vertex `y` over `⟨n⟩`. They exhibit `y` as the tuple of the colors `cᵢ`, which lie over `⟨1⟩`
(`SSet.InertProjectionLifts.app_color`). -/
structure InertProjectionLifts (p : X ⟶ nerve FinPointed.{u}) (n : FinPointed.{u})
    (y : X _⦋0⦌) where
  /-- The vertex `y` lies over `⟨n⟩`. -/
  app_eq : p.app _ y = n.vertex
  /-- The color `cᵢ`, the target of the `i`-th lift. -/
  color : Fin n.len → X _⦋0⦌
  /-- The lift `y ⟶ cᵢ` of the inert projection `ρ i`. -/
  edge (i : Fin n.len) : Edge y (color i)
  isCoCartesian (i : Fin n.len) : (edge i).IsCoCartesian p
  map_edge (i : Fin n.len) : ((edge i).map p).edge = (nerve.edgeMk (FinPointed.ρ i)).edge

namespace InertProjectionLifts

variable {p : X ⟶ nerve FinPointed.{u}} {n : FinPointed.{u}} {y : X _⦋0⦌}
  (L : InertProjectionLifts p n y)

/-- The colors of lifts of the inert projections lie over `⟨1⟩`. -/
lemma app_color (i : Fin n.len) : p.app _ (L.color i) = (FinPointed.mk 1).vertex := by
  rw [← ((L.edge i).map p).tgt_eq, L.map_edge i]
  exact (nerve.edgeMk _).tgt_eq

/-- The image of the `i`-th lift in `N(Fin_*)` is an inert map. -/
lemma inert_map_edge (i : Fin n.len) : FinPointed.inert ((L.edge i).map p).edge.hom := by
  rw [L.map_edge i, nerve.edgeMk_edge, FinPointed.inert_iff]
  exact FinPointed.isInert_ρ i

/-- The map `Hom^R_X(x, y)_e ⟶ ∏ᵢ Hom^R_X(x, cᵢ)_{ρ i ∘ e}` given by postcomposition with the
lifts `y ⟶ cᵢ` of the inert projections, for a vertex `x` and an edge `e : p x ⟶ p y`. Its
components are `SSet.rightMappingSpaceOver.postcomp`. -/
noncomputable def segalMap [InnerFibration p] (x : X _⦋0⦌) (e : Edge (p.app _ x) (p.app _ y)) :
    (rightMappingSpaceOver p e : SSet.{u}) ⟶
      ∏ᶜ fun i : Fin n.len ↦ (rightMappingSpaceOver p
        (nerve.homEquiv.symm (nerve.homEquiv e ≫ nerve.homEquiv ((L.edge i).map p))) : SSet.{u}) :=
  haveI := quasicategory_of_innerFibration p
  Pi.lift fun i ↦ rightMappingSpaceOver.postcomp (L.edge i) (Equiv.apply_symm_apply _ _).symm

@[reassoc (attr := simp)]
lemma segalMap_π [InnerFibration p] (x : X _⦋0⦌) (e : Edge (p.app _ x) (p.app _ y))
    (i : Fin n.len) :
    L.segalMap x e ≫ Pi.π _ i =
      haveI := quasicategory_of_innerFibration p
      rightMappingSpaceOver.postcomp (L.edge i) (Equiv.apply_symm_apply _ _).symm := by
  simp [segalMap]

/-- The space `Mul({cᵢ}, z)` of multi-operations from the colors `cᵢ` to a color `z`: the space of
maps `y ⟶ z` lying over the fold map `⟨n⟩ ⟶ ⟨1⟩`. -/
def mulSpace {z : X _⦋0⦌} (hz : p.app _ z = (FinPointed.mk 1).vertex) :
    (X.rightMappingSpace y z : SSet.{u}).Subcomplex :=
  rightMappingSpaceOver p ((nerve.edgeMk (FinPointed.fold n)).ofEq L.app_eq.symm hz.symm)

/-- `Mul({cᵢ}, z)` is the fiber `Hom^R_X(y, z)_e` of `SSet.rightMappingSpaceOver` over the fold
edge `e : p y ⟶ p z`, so the fiber API (membership, the range criterion, functoriality) applies to
it. -/
lemma mulSpace_def {z : X _⦋0⦌} (hz : p.app _ z = (FinPointed.mk 1).vertex) :
    L.mulSpace hz =
      rightMappingSpaceOver p ((nerve.edgeMk (FinPointed.fold n)).ofEq L.app_eq.symm hz.symm) := by
  rw [mulSpace]

/-- A vertex of `Hom^R_X(y, z)` is a multi-operation exactly when it lies over the fold map. -/
lemma mem_mulSpace_obj₀_iff {z : X _⦋0⦌} (hz : p.app _ z = (FinPointed.mk 1).vertex)
    (s : (X.rightMappingSpace y z : SSet.{u}) _⦋0⦌) :
    s ∈ (L.mulSpace hz).obj (op ⦋0⦌) ↔
      ((rightMappingSpace.obj₀Equiv s).map p).edge = (nerve.edgeMk (FinPointed.fold n)).edge := by
  rw [mulSpace_def, rightMappingSpaceOver.mem_obj₀_iff]
  exact ⟨fun h ↦ by rw [h]; rfl, fun h ↦ Edge.ext h⟩

end InertProjectionLifts

/-! ### `∞`-operads -/

/-- An `∞`-operad: a map `p : O^⊗ ⟶ N(Fin_*)` which is an inner fibration, along which inert
maps have coCartesian lifts with specified source, such that every family of colors is the
family of targets of coCartesian lifts of the inert projections `ρ i` from a single vertex, and
such that postcomposition with such lifts gives weak equivalences
`Hom^R(x, y)_e ⟶ ∏ᵢ Hom^R(x, cᵢ)_{ρ i ∘ e}` (`SSet.InertProjectionLifts.segalMap`). -/
class InfinityOperad (p : X ⟶ nerve FinPointed.{u}) : Prop extends InnerFibration p where
  exists_isCoCartesian_lift_of_inert {x : X _⦋0⦌} {t : (nerve FinPointed.{u}) _⦋0⦌}
    (e : Edge (p.app _ x) t) (he : FinPointed.inert e.edge.hom) :
    ∃ (y : X _⦋0⦌) (f : Edge x y), f.IsCoCartesian p ∧ (f.map p).edge = e.edge
  exists_inertProjectionLifts (n : FinPointed.{u}) (c : Fin n.len → X _⦋0⦌)
    (hc : ∀ i, p.app _ (c i) = (FinPointed.mk 1).vertex) :
    ∃ (y : X _⦋0⦌) (L : InertProjectionLifts p n y), L.color = c
  weakEquivalence_segalMap {n : FinPointed.{u}} {y : X _⦋0⦌} (L : InertProjectionLifts p n y)
    (x : X _⦋0⦌) (e : Edge (p.app _ x) (p.app _ y)) : WeakEquivalence (L.segalMap x e)

attribute [instance] InfinityOperad.weakEquivalence_segalMap

namespace InfinityOperad

/-- An isomorphism `p : X ⟶ N(Fin_*)` is an `∞`-operad: its right mapping spaces are those of
`N(Fin_*)`, so its spaces of maps lying over an edge are points. For instance the identity of
`N(Fin_*)`, the commutative `∞`-operad, is an `∞`-operad. -/
instance of_isIso (p : X ⟶ nerve FinPointed.{u}) [IsIso p] : InfinityOperad p where
  toInnerFibration := inferInstance
  exists_isCoCartesian_lift_of_inert e _ := CoCartesianFibration.exists_isCoCartesian_lift e
  exists_inertProjectionLifts n c hc :=
    ⟨(inv p).app _ n.vertex,
      { app_eq := by simp
        color := c
        edge i := ((nerve.edgeMk (FinPointed.ρ i)).map (inv p)).ofEq rfl
          ((congrArg ((inv p).app _) (hc i)).symm.trans (by simp))
        isCoCartesian _ := Edge.isCoCartesian_of_isIso _ _
        -- The edge is the image of the edge of `N(Fin_*)` under the inverse of `p`.
        map_edge _ := ConcreteCategory.congr_hom (NatTrans.congr_app (IsIso.inv_hom_id p) _) _ },
      rfl⟩
  weakEquivalence_segalMap {n y} L x e := by
    -- The spaces of maps lying over an edge are fibers of isomorphisms, hence terminal.
    have hT : IsTerminal (∏ᶜ fun i : Fin n.len ↦ (rightMappingSpaceOver p
        (nerve.homEquiv.symm (nerve.homEquiv e ≫ nerve.homEquiv ((L.edge i).map p))) : SSet.{u})) :=
      IsTerminal.ofUniqueHom
        (fun _ ↦ Pi.lift fun _ ↦ (rightMappingSpaceOver.isTerminalOfIsIso p _).from _)
        fun _ _ ↦ Pi.hom_ext _ _ fun _ ↦ (rightMappingSpaceOver.isTerminalOfIsIso p _).hom_ext _ _
    have : IsIso (L.segalMap x e) :=
      isIso_of_isTerminal (rightMappingSpaceOver.isTerminalOfIsIso p e) hT _
    infer_instance

end InfinityOperad

/-- A simplicial set without vertices is not an `∞`-operad over any map to `N(Fin_*)`: the empty
family of colors is not represented by a vertex over `⟨0⟩`. -/
lemma not_infinityOperad_of_not_nonempty (hX : ¬ X.Nonempty) (p : X ⟶ nerve FinPointed.{u}) :
    ¬ InfinityOperad p := fun h ↦
  have ⟨y, _⟩ := h.exists_inertProjectionLifts (.mk 0) (fun i ↦ i.elim0) fun i ↦ i.elim0
  hX ⟨y⟩

/-! ### Maps of `∞`-operads -/

namespace InfinityOperad

variable (p : X ⟶ nerve FinPointed.{u}) (q : Y ⟶ nerve FinPointed.{u})
  (r : Z ⟶ nerve FinPointed.{u})

/-- A map of `∞`-operads from `p : O^⊗ ⟶ N(Fin_*)` to `q : O'^⊗ ⟶ N(Fin_*)`: a map
`O^⊗ ⟶ O'^⊗` over `N(Fin_*)` sending the `p`-coCartesian edges lying over inert maps to
`q`-coCartesian edges. Between symmetric monoidal quasicategories, these are the lax symmetric
monoidal functors. -/
@[ext]
structure Hom where
  /-- The underlying map `O^⊗ ⟶ O'^⊗`. -/
  hom : X ⟶ Y
  hom_comp : hom ≫ q = p
  isCoCartesian_map {x y : X _⦋0⦌} (f : Edge x y) (hf : f.IsCoCartesian p)
    (hinert : FinPointed.inert (f.map p).edge.hom) : (f.map hom).IsCoCartesian q

attribute [reassoc (attr := simp)] Hom.hom_comp

namespace Hom

/-- The identity map of `∞`-operads. -/
def id : Hom p p where
  hom := 𝟙 X
  hom_comp := Category.id_comp p
  isCoCartesian_map f hf _ := hf.of_edge_eq (by simp)

@[simp]
lemma id_hom : (id p).hom = 𝟙 X :=
  (rfl)

variable {p q r}

/-- A map of `∞`-operads preserves the image in `N(Fin_*)` of each simplex. -/
@[simp]
lemma app_hom_app (F : Hom p q) {k : SimplexCategoryᵒᵖ} (σ : X.obj k) :
    q.app k (F.hom.app k σ) = p.app k σ := by
  rw [← ConcreteCategory.comp_apply, ← NatTrans.comp_app, F.hom_comp]

/-- The composite of two maps of `∞`-operads. -/
def comp (F : Hom p q) (G : Hom q r) : Hom p r where
  hom := F.hom ≫ G.hom
  hom_comp := by simp
  isCoCartesian_map f hf hinert := by
    refine (G.isCoCartesian_map _ (F.isCoCartesian_map f hf hinert) ?_).of_edge_eq (by simp)
    rwa [Edge.map_edge, Edge.map_edge, app_hom_app]

@[simp]
lemma comp_hom (F : Hom p q) (G : Hom q r) : (F.comp G).hom = F.hom ≫ G.hom :=
  (rfl)

@[simp]
lemma id_comp (F : Hom p q) : (id p).comp F = F :=
  Hom.ext (Category.id_comp _)

@[simp]
lemma comp_id (F : Hom p q) : F.comp (id q) = F :=
  Hom.ext (Category.comp_id _)

lemma comp_assoc {W : SSet.{u}} {s : W ⟶ nerve FinPointed.{u}} (F : Hom p q) (G : Hom q r)
    (H : Hom r s) : (F.comp G).comp H = F.comp (G.comp H) :=
  Hom.ext (Category.assoc _ _ _)

/-- The underlying functor `O_⟨1⟩ ⟶ O'_⟨1⟩` of a map of `∞`-operads, on the quasicategories of
colors. -/
abbrev underlying (F : Hom p q) :
    (fiber p (FinPointed.mk 1).vertex : SSet) ⟶ (fiber q (FinPointed.mk 1).vertex : SSet) :=
  fiber.map F.hom F.hom_comp _

/-- The underlying functor of a composite is the composite of the underlying functors. -/
@[simp]
lemma comp_underlying (F : Hom p q) (G : Hom q r) :
    (F.comp G).underlying = F.underlying ≫ G.underlying :=
  fiber.map_comp _ _ _ _ _

variable {n : FinPointed.{u}} {y : X _⦋0⦌}

/-- A map of `∞`-operads sends lifts of the inert projections to lifts of the inert projections,
so it sends the vertex representing a tuple of colors to the vertex representing the tuple of
their images. -/
def mapInertProjectionLifts (F : Hom p q) (L : InertProjectionLifts p n y) :
    InertProjectionLifts q n (F.hom.app _ y) where
  app_eq := by rw [app_hom_app, L.app_eq]
  color i := F.hom.app _ (L.color i)
  edge i := (L.edge i).map F.hom
  isCoCartesian i := F.isCoCartesian_map _ (L.isCoCartesian i) (L.inert_map_edge i)
  map_edge i := by rw [← L.map_edge i, Edge.map_edge, Edge.map_edge, Edge.map_edge,
    app_hom_app]

@[simp]
lemma mapInertProjectionLifts_color (F : Hom p q) (L : InertProjectionLifts p n y)
    (i : Fin n.len) : (F.mapInertProjectionLifts L).color i = F.hom.app _ (L.color i) :=
  (rfl)

@[simp]
lemma mapInertProjectionLifts_edge (F : Hom p q) (L : InertProjectionLifts p n y)
    (i : Fin n.len) : ((F.mapInertProjectionLifts L).edge i).edge = ((L.edge i).map F.hom).edge :=
  (rfl)

/-- The action of a map of `∞`-operads on multi-operation spaces, from
`Mul({cᵢ}, z)` to `Mul({F cᵢ}, F z)`: the restriction of the map of right mapping spaces. -/
def mapMulSpace (F : Hom p q) (L : InertProjectionLifts p n y) {z : X _⦋0⦌}
    (hz : p.app _ z = (FinPointed.mk 1).vertex) :
    (L.mulSpace hz : SSet.{u}) ⟶
      ((F.mapInertProjectionLifts L).mulSpace ((app_hom_app F z).trans hz) : SSet.{u}) :=
  rightMappingSpaceOver.map F.hom F.hom_comp rfl

@[reassoc (attr := simp)]
lemma mapMulSpace_ι (F : Hom p q) (L : InertProjectionLifts p n y) {z : X _⦋0⦌}
    (hz : p.app _ z = (FinPointed.mk 1).vertex) :
    F.mapMulSpace L hz ≫ ((F.mapInertProjectionLifts L).mulSpace _).ι =
      (L.mulSpace hz).ι ≫ rightMappingSpace.map y z F.hom :=
  rightMappingSpaceOver.map_ι _ _ _

end Hom

end InfinityOperad

end SSet
