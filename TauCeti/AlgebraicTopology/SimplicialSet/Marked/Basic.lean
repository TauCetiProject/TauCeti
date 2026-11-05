/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Basic
public import Mathlib.CategoryTheory.Adjunction.FullyFaithful

/-!
# Marked simplicial sets

A *marked simplicial set* is a simplicial set `X` together with a set of edges of `X`, the
*marked* edges, which contains every degenerate edge. A morphism of marked simplicial sets is a
morphism of simplicial sets sending marked edges to marked edges. Marked simplicial sets are the
underlying objects of the marked models for Cartesian and coCartesian fibrations, and of the
marked categorical model of quasicategories, in which a fibrant object is a quasicategory marked
at its equivalences.

Every simplicial set `X` carries a smallest marking `X♭`, in which only the degenerate edges are
marked, and a largest marking `X♯`, in which every edge is marked. These are the left and right
adjoints of the forgetful functor to simplicial sets, and both are fully faithful.

## Main definitions

* `TauCeti.MarkedSSet`: the category of marked simplicial sets.
* `TauCeti.MarkedSSet.forget`: the forgetful functor to simplicial sets.
* `TauCeti.MarkedSSet.flat`: the functor `X ↦ X♭`, marking only the degenerate edges.
* `TauCeti.MarkedSSet.sharp`: the functor `X ↦ X♯`, marking every edge.
* `TauCeti.MarkedSSet.ofEdges X S`: the simplicial set `X` marked at the edges in `S` and at its
  degenerate edges.
* `TauCeti.MarkedSSet.flatForgetAdj`, `TauCeti.MarkedSSet.forgetSharpAdj`: the adjunctions
  `(-)♭ ⊣ forget ⊣ (-)♯`.

## References

* J. Lurie, *Higher Topos Theory*, Definition 3.1.0.1.
-/

public section

open CategoryTheory Opposite Simplicial

universe u

namespace TauCeti

/-- A marked simplicial set: a simplicial set together with a set of marked edges containing
every degenerate edge. -/
structure MarkedSSet where
  /-- The underlying simplicial set. -/
  toSSet : SSet.{u}
  /-- The marked edges. -/
  marked : Set (toSSet _⦋1⦌)
  σ_mem_marked (x : toSSet _⦋0⦌) : toSSet.σ 0 x ∈ marked

namespace MarkedSSet

attribute [simp] σ_mem_marked

/-- A morphism of marked simplicial sets: a morphism of the underlying simplicial sets sending
marked edges to marked edges. -/
@[ext]
structure Hom (X Y : MarkedSSet.{u}) where
  /-- The underlying morphism of simplicial sets. -/
  hom : X.toSSet ⟶ Y.toSSet
  map_mem_marked ⦃e : X.toSSet _⦋1⦌⦄ (he : e ∈ X.marked) : hom.app _ e ∈ Y.marked

instance : Category MarkedSSet.{u} where
  Hom := Hom
  id X := ⟨𝟙 _, fun _ he ↦ he⟩
  comp f g := ⟨f.hom ≫ g.hom, fun _ he ↦ g.map_mem_marked (f.map_mem_marked he)⟩

variable {X Y Z : MarkedSSet.{u}}

@[ext]
lemma hom_ext {f g : X ⟶ Y} (h : f.hom = g.hom) : f = g :=
  Hom.ext h

@[simp]
lemma hom_id (X : MarkedSSet.{u}) : Hom.hom (𝟙 X) = 𝟙 X.toSSet :=
  (rfl)

@[simp, reassoc]
lemma hom_comp (f : X ⟶ Y) (g : Y ⟶ Z) : (f ≫ g).hom = f.hom ≫ g.hom :=
  (rfl)

/-- A morphism of marked simplicial sets sends marked edges to marked edges. -/
lemma map_mem_marked (f : X ⟶ Y) {e : X.toSSet _⦋1⦌} (he : e ∈ X.marked) :
    f.hom.app _ e ∈ Y.marked :=
  Hom.map_mem_marked f he

/-- An isomorphism of marked simplicial sets from an isomorphism of the underlying simplicial sets
which preserves and reflects the marked edges. -/
def isoMk (e : X.toSSet ≅ Y.toSSet) (he : ∀ x, e.hom.app _ x ∈ Y.marked ↔ x ∈ X.marked) :
    X ≅ Y where
  hom := ⟨e.hom, fun x hx ↦ (he x).2 hx⟩
  inv := ⟨e.inv, fun y hy ↦ by
    rw [← he]
    simpa using hy⟩
  hom_inv_id := by ext : 1; exact e.hom_inv_id
  inv_hom_id := by ext : 1; exact e.inv_hom_id

@[simp]
lemma isoMk_hom_hom (e : X.toSSet ≅ Y.toSSet)
    (he : ∀ x, e.hom.app _ x ∈ Y.marked ↔ x ∈ X.marked) : (isoMk e he).hom.hom = e.hom :=
  (rfl)

@[simp]
lemma isoMk_inv_hom (e : X.toSSet ≅ Y.toSSet)
    (he : ∀ x, e.hom.app _ x ∈ Y.marked ↔ x ∈ X.marked) : (isoMk e he).inv.hom = e.inv :=
  (rfl)

/-- An isomorphism of marked simplicial sets preserves and reflects the marked edges. -/
@[simp]
lemma mem_marked_iff_of_iso (e : X ≅ Y) (x : X.toSSet _⦋1⦌) :
    e.hom.hom.app _ x ∈ Y.marked ↔ x ∈ X.marked := by
  refine ⟨fun h ↦ ?_, map_mem_marked e.hom⟩
  have hx := congrArg (fun f ↦ f.hom.app (op ⦋1⦌) x) e.hom_inv_id
  simp only [hom_comp, hom_id, NatTrans.comp_app, NatTrans.id_app, types_comp_apply,
    types_id_apply] at hx
  simpa [hx] using map_mem_marked e.inv h

/-- The forgetful functor from marked simplicial sets to simplicial sets. -/
@[expose, simps]
def forget : MarkedSSet.{u} ⥤ SSet.{u} where
  obj X := X.toSSet
  map f := f.hom

instance : forget.{u}.Faithful where
  map_injective h := hom_ext h

section flat

/-- The functor `X ↦ X♭` marking only the degenerate edges of a simplicial set. -/
@[expose, simps obj_toSSet map_hom]
def flat : SSet.{u} ⥤ MarkedSSet.{u} where
  obj X :=
    { toSSet := X
      marked := Set.range (X.σ 0)
      σ_mem_marked x := ⟨x, rfl⟩ }
  map {X Y} f := ⟨f, by
    rintro _ ⟨x, rfl⟩
    exact ⟨f.app _ x, (SSet.σ_naturality_apply f 0 x).symm⟩⟩

/-- The marked edges of `X♭` are the degenerate edges of `X`. -/
@[simp]
lemma mem_flat_marked_iff {X : SSet.{u}} {e : X _⦋1⦌} :
    e ∈ (flat.obj X).marked ↔ ∃ x, X.σ 0 x = e :=
  Iff.rfl

/-- A morphism of simplicial sets into a marked simplicial set sends degenerate edges to marked
edges. -/
lemma map_σ_mem_marked {X : SSet.{u}} (f : X ⟶ Y.toSSet) (x : X _⦋0⦌) :
    f.app _ (X.σ 0 x) ∈ Y.marked := by
  rw [SSet.σ_naturality_apply]
  exact Y.σ_mem_marked _

/-- A morphism of simplicial sets `X ⟶ Y` is a morphism of marked simplicial sets `X♭ ⟶ Y`:
it sends degenerate edges to degenerate, hence marked, edges. -/
def fromFlat {X : SSet.{u}} (f : X ⟶ Y.toSSet) : flat.obj X ⟶ Y :=
  ⟨f, by
    rintro _ ⟨x, rfl⟩
    exact map_σ_mem_marked f x⟩

@[simp]
lemma fromFlat_hom {X : SSet.{u}} (f : X ⟶ Y.toSSet) : (fromFlat f).hom = f :=
  (rfl)

/-- The marking `(-)♭` is left adjoint to the forgetful functor. -/
def flatForgetAdj : flat.{u} ⊣ forget.{u} :=
  Adjunction.mkOfHomEquiv
    { homEquiv X Y :=
        { toFun f := f.hom
          invFun := fromFlat
          left_inv _ := rfl
          right_inv _ := rfl } }

@[simp]
lemma flatForgetAdj_homEquiv_apply {X : SSet.{u}} (f : flat.obj X ⟶ Y) :
    flatForgetAdj.homEquiv X Y f = f.hom :=
  (rfl)

@[simp]
lemma flatForgetAdj_homEquiv_symm_apply {X : SSet.{u}} (f : X ⟶ Y.toSSet) :
    (flatForgetAdj.homEquiv X Y).symm f = fromFlat f :=
  (rfl)

/-- The functor `(-)♭` is fully faithful. -/
def fullyFaithfulFlat : flat.{u}.FullyFaithful where
  preimage f := f.hom

instance : flat.{u}.Full :=
  fullyFaithfulFlat.full

instance : flat.{u}.Faithful :=
  fullyFaithfulFlat.faithful

end flat

section ofEdges

/-- The simplicial set `X` marked at the edges in `S` and at its degenerate edges. -/
abbrev ofEdges (X : SSet.{u}) (S : Set (X _⦋1⦌)) : MarkedSSet.{u} where
  toSSet := X
  marked := Set.range (X.σ 0) ∪ S
  σ_mem_marked x := Or.inl ⟨x, rfl⟩

/-- The marked edges of `ofEdges X S` are the degenerate edges of `X` and the edges in `S`.
Since `ofEdges` is reducible, `simp` already rewrites this membership with `Set.mem_union` and
`Set.mem_range`, so this lemma is not tagged `@[simp]`. -/
lemma mem_ofEdges_marked_iff {X : SSet.{u}} {S : Set (X _⦋1⦌)} {e : X _⦋1⦌} :
    e ∈ (ofEdges X S).marked ↔ (∃ x, X.σ 0 x = e) ∨ e ∈ S :=
  Iff.rfl

/-- A morphism of simplicial sets out of `X` which sends the edges in `S` to marked edges, as a
morphism of marked simplicial sets out of `ofEdges X S`. -/
def ofEdgesHom {X : SSet.{u}} {S : Set (X _⦋1⦌)} {Y : MarkedSSet.{u}} (f : X ⟶ Y.toSSet)
    (hf : ∀ e ∈ S, f.app _ e ∈ Y.marked) : ofEdges X S ⟶ Y :=
  ⟨f, by
    rintro e (⟨x, rfl⟩ | he)
    · exact map_σ_mem_marked f x
    · exact hf e he⟩

@[simp]
lemma ofEdgesHom_hom {X : SSet.{u}} {S : Set (X _⦋1⦌)} {Y : MarkedSSet.{u}} (f : X ⟶ Y.toSSet)
    (hf : ∀ e ∈ S, f.app _ e ∈ Y.marked) : (ofEdgesHom f hf).hom = f :=
  (rfl)

end ofEdges

section sharp

/-- The functor `X ↦ X♯` marking every edge of a simplicial set. -/
@[expose, simps obj_toSSet map_hom]
def sharp : SSet.{u} ⥤ MarkedSSet.{u} where
  obj X :=
    { toSSet := X
      marked := Set.univ
      σ_mem_marked _ := Set.mem_univ _ }
  map f := ⟨f, fun _ _ ↦ Set.mem_univ _⟩

/-- Every edge of `X♯` is marked. -/
@[simp]
lemma mem_sharp_marked {X : SSet.{u}} (e : X _⦋1⦌) : e ∈ (sharp.obj X).marked :=
  Set.mem_univ e

/-- A morphism of simplicial sets `X ⟶ Y` is a morphism of marked simplicial sets `X ⟶ Y♯`. -/
@[expose]
def toSharp {Y : SSet.{u}} (f : X.toSSet ⟶ Y) : X ⟶ sharp.obj Y :=
  ⟨f, fun _ _ ↦ mem_sharp_marked _⟩

@[simp]
lemma toSharp_hom {Y : SSet.{u}} (f : X.toSSet ⟶ Y) : (toSharp f).hom = f :=
  (rfl)

/-- The marking `(-)♯` is right adjoint to the forgetful functor. -/
def forgetSharpAdj : forget.{u} ⊣ sharp.{u} :=
  Adjunction.mkOfHomEquiv
    { homEquiv X Y :=
        { toFun := toSharp
          invFun f := f.hom
          left_inv _ := rfl
          right_inv _ := rfl } }

@[simp]
lemma forgetSharpAdj_homEquiv_apply {Y : SSet.{u}} (f : X.toSSet ⟶ Y) :
    forgetSharpAdj.homEquiv X Y f = toSharp f :=
  (rfl)

@[simp]
lemma forgetSharpAdj_homEquiv_symm_apply {Y : SSet.{u}} (f : X ⟶ sharp.obj Y) :
    (forgetSharpAdj.homEquiv X Y).symm f = f.hom :=
  (rfl)

/-- The functor `(-)♯` is fully faithful. -/
def fullyFaithfulSharp : sharp.{u}.FullyFaithful where
  preimage f := f.hom

instance : sharp.{u}.Full :=
  fullyFaithfulSharp.full

instance : sharp.{u}.Faithful :=
  fullyFaithfulSharp.faithful

end sharp

/-- The natural transformation `X♭ ⟶ X♯`, the identity on underlying simplicial sets. -/
@[expose]
def flatToSharp : flat.{u} ⟶ sharp.{u} where
  app X := toSharp (𝟙 X)

@[simp]
lemma flatToSharp_app_hom (X : SSet.{u}) : (flatToSharp.app X).hom = 𝟙 (flat.obj X).toSSet :=
  (rfl)

end MarkedSSet

end TauCeti
