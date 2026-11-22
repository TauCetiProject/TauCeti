/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.DoldKan.Equivalence
public import Mathlib.AlgebraicTopology.DoldKan.HomotopyEquivalence
public import TauCeti.AlgebraicTopology.DoldKan.Monoidal
public import TauCeti.AlgebraicTopology.SimplicialObject.ChainHomotopy
public import TauCeti.AlgebraicTopology.SimplicialObject.Cylinder
import TauCeti.Algebra.Homology.Homotopy

/-!
# Simplicial homotopies and chain homotopies across the Dold–Kan correspondence

In an idempotent-complete preadditive category `C` with finite coproducts, the Dold–Kan equivalence
(`CategoryTheory.Idempotents.DoldKan.equivalence`) identifies combinatorial simplicial homotopies
`CategoryTheory.SimplicialObject.Homotopy f g` with chain homotopies on alternating face map
complexes or normalized chain complexes (Dold–Puppe, Satz 3.31).

While `SimplicialObject.Homotopy.toChainHomotopy` holds in any preadditive category, the converse
constructs an internal chain map `K[(cylinder C).obj X] ⟶ K[Y]` restricting along `cylinderι₀` and
`cylinderι₁` to `K.map f` and `K.map g`, restricts it to `Idempotents.DoldKan.N`, pulls it back
along the full faithfulness of `N` to a simplicial morphism `(cylinder C).obj X ⟶ Y`, and applies
`Homotopy.ofCylinderHom`.

## Main definitions and results

* `Idempotents.DoldKan.homotopyEquivNAlternatingFaceMapComplex`: chain homotopy equivalence
  `N.obj X ≃ K[X]` in any pseudoabelian category with finite coproducts.
* `SimplicialObject.Homotopy.ofAlternatingFaceMapComplexHomotopy`, `ofNHomotopy`,
  `ofNormalizedMooreComplexHomotopy`: lifting chain homotopies to simplicial homotopies.
* `SimplicialObject.nonempty_homotopy_iff_alternatingFaceMapComplex`, `nonempty_homotopy_iff_N`,
  `nonempty_homotopy_iff_normalizedMooreComplex`: Dold–Puppe, Satz 3.31.
* `SimplicialObject.HomotopyEquiv.toNHomotopyEquiv`,
  `SimplicialObject.HomotopyEquiv.ofAlternatingFaceMapComplexHomotopyEquiv`,
  `SimplicialObject.homotopyEquivalences_alternatingFaceMapComplex_map_iff`: normalized-chain
  counterpart and lifting chain homotopy equivalences to simplicial homotopy equivalences.
* `Idempotents.DoldKan.Γ.mapHomotopy`, `Idempotents.DoldKan.Γ.mapHomotopyEquiv`: the inverse
  Dold–Kan functor `Γ` preserves homotopies and homotopy equivalences.

## References

* A. Dold and D. Puppe, *Homologie nicht-additiver Funktoren. Anwendungen*, Ann. Inst. Fourier 11
  (1961), 201–312, §3.31.
* P. G. Goerss and J. F. Jardine, *Simplicial Homotopy Theory*, Chapter III, Corollary 2.16.
-/

public noncomputable section

universe v u

open CategoryTheory Limits Opposite SimplexCategory AlgebraicTopology AlgebraicTopology.DoldKan
open scoped Simplicial DoldKan

namespace CategoryTheory.Idempotents.DoldKan

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteCoproducts C]
  [IsIdempotentComplete C]

/-- In an idempotent-complete preadditive category with finite coproducts, the inclusion
`inclusionN.app X` and projection `PInftyToN.app X` form a chain homotopy equivalence between the
normalized chains `N.obj X` and the alternating face map complex `K[X]`. -/
def homotopyEquivNAlternatingFaceMapComplex (X : SimplicialObject C) :
    HomotopyEquiv (N.obj X) ((alternatingFaceMapComplex C).obj X) where
  hom := inclusionN.app X
  inv := PInftyToN.app X
  homotopyHomInvId := Homotopy.ofEq (inclusionN_app_comp_PInftyToN_app X)
  homotopyInvHomId :=
    (Homotopy.ofEq (PInftyToN_app_comp_inclusionN_app X)).trans (homotopyPInftyToId X)

@[simp]
lemma homotopyEquivNAlternatingFaceMapComplex_hom (X : SimplicialObject C) :
    (homotopyEquivNAlternatingFaceMapComplex X).hom = inclusionN.app X := (rfl)

@[simp]
lemma homotopyEquivNAlternatingFaceMapComplex_inv (X : SimplicialObject C) :
    (homotopyEquivNAlternatingFaceMapComplex X).inv = PInftyToN.app X := (rfl)

end CategoryTheory.Idempotents.DoldKan

namespace CategoryTheory.SimplicialObject

section CylinderChainMap

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteCoproducts C]

/-- Degree-`(i, j)` component of the null-homotopy correction for `cylinderChainMap`: it equals
`H.hom i j` on the constant-`1` summand `α.toOrderHom 0 = 1` (i.e. `const ⦋i⦌ ⦋1⦌ 1`) and `0` on
all other summands. -/
private def cylinderNullHomotopyTerm {X Y : SimplicialObject C} {f g : X ⟶ Y}
    (H : _root_.Homotopy ((alternatingFaceMapComplex C).map f)
      ((alternatingFaceMapComplex C).map g))
    (i j : ℕ) :
    ((alternatingFaceMapComplex C).obj ((cylinder C).obj X)).X i ⟶
      ((alternatingFaceMapComplex C).obj Y).X j :=
  cylinderDesc fun α ↦ if α.toOrderHom 0 = 1 then H.hom i j else 0

/-- Explicit chain map `K[(cylinder C).obj X] ⟶ K[Y]` associated to a chain homotopy
`H : Homotopy ((alternatingFaceMapComplex C).map f) ((alternatingFaceMapComplex C).map g)`,
defined as `K.map (cylinderπ.app X ≫ f) - nullHomotopicMap (cylinderNullHomotopyTerm H)`. Its
restrictions along `cylinderι₀` and `cylinderι₁` recover `K.map f` and `K.map g`. -/
private def cylinderChainMap {X Y : SimplicialObject C} {f g : X ⟶ Y}
    (H : _root_.Homotopy ((alternatingFaceMapComplex C).map f)
      ((alternatingFaceMapComplex C).map g)) :
    (alternatingFaceMapComplex C).obj ((cylinder C).obj X) ⟶
      (alternatingFaceMapComplex C).obj Y :=
  (alternatingFaceMapComplex C).map ((cylinderπ C).app X ≫ f) -
    _root_.Homotopy.nullHomotopicMap (cylinderNullHomotopyTerm H)

@[reassoc]
private lemma alternatingFaceMapComplex_map_cylinderι₀_comp_cylinderChainMap
    {X Y : SimplicialObject C} {f g : X ⟶ Y}
    (H : _root_.Homotopy ((alternatingFaceMapComplex C).map f)
      ((alternatingFaceMapComplex C).map g)) :
    (alternatingFaceMapComplex C).map ((cylinderι₀ C).app X) ≫ cylinderChainMap H =
      (alternatingFaceMapComplex C).map f := by
  have hnull : (alternatingFaceMapComplex C).map ((cylinderι₀ C).app X) ≫
      _root_.Homotopy.nullHomotopicMap (cylinderNullHomotopyTerm H) = 0 := by
    rw [_root_.Homotopy.comp_nullHomotopicMap]
    have hzero : (fun i j ↦
        ((alternatingFaceMapComplex C).map ((cylinderι₀ C).app X)).f i ≫
          cylinderNullHomotopyTerm H i j) = 0 := by
      ext i j
      simp [cylinderNullHomotopyTerm, SimplexCategory.const_apply]
    rw [hzero]
    ext n
    simp [_root_.Homotopy.nullHomotopicMap]
  rw [cylinderChainMap, Preadditive.comp_sub, hnull, sub_zero, ← Functor.map_comp,
    ← Category.assoc, ← NatTrans.comp_app, cylinderι₀_comp_cylinderπ, NatTrans.id_app,
    Category.id_comp]

@[reassoc]
private lemma alternatingFaceMapComplex_map_cylinderι₁_comp_cylinderChainMap
    {X Y : SimplicialObject C} {f g : X ⟶ Y}
    (H : _root_.Homotopy ((alternatingFaceMapComplex C).map f)
      ((alternatingFaceMapComplex C).map g)) :
    (alternatingFaceMapComplex C).map ((cylinderι₁ C).app X) ≫ cylinderChainMap H =
      (alternatingFaceMapComplex C).map g := by
  have hnull : (alternatingFaceMapComplex C).map ((cylinderι₁ C).app X) ≫
      _root_.Homotopy.nullHomotopicMap (cylinderNullHomotopyTerm H) =
      _root_.Homotopy.nullHomotopicMap H.hom := by
    rw [_root_.Homotopy.comp_nullHomotopicMap]
    congr 1
    ext i j
    simp [cylinderNullHomotopyTerm, SimplexCategory.const_apply]
  rw [cylinderChainMap, Preadditive.comp_sub, hnull, ← Functor.map_comp, ← Category.assoc,
    ← NatTrans.comp_app, cylinderι₁_comp_cylinderπ, NatTrans.id_app, Category.id_comp,
    ← H.eq_sub_nullHomotopicMap]

end CylinderChainMap

section Pseudoabelian

open Idempotents.DoldKan

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteCoproducts C]
  [IsIdempotentComplete C]

namespace Homotopy

/-- In an idempotent-complete preadditive category with finite coproducts, any chain homotopy
between `(alternatingFaceMapComplex C).map f` and `(alternatingFaceMapComplex C).map g` lifts to a
combinatorial simplicial homotopy `Homotopy f g` (Dold–Puppe, Satz 3.31). -/
def ofAlternatingFaceMapComplexHomotopy {X Y : SimplicialObject C} {f g : X ⟶ Y}
    (H : _root_.Homotopy ((alternatingFaceMapComplex C).map f)
      ((alternatingFaceMapComplex C).map g)) :
    Homotopy f g := by
  let hN : (N (C := C)).FullyFaithful :=
    (equivalence (C := C)).fullyFaithfulFunctor.ofIso (CategoryTheory.eqToIso equivalence_functor)
  let Ψ : N.obj ((cylinder C).obj X) ⟶ N.obj Y :=
    inclusionN.app ((cylinder C).obj X) ≫ cylinderChainMap H ≫ PInftyToN.app Y
  let Φ : (cylinder C).obj X ⟶ Y := hN.preimage Ψ
  have hΦ : N.map Φ = Ψ := hN.map_preimage Ψ
  refine ofCylinderHom Φ ?_ ?_ <;>
    · apply hN.map_injective
      rw [Functor.map_comp, hΦ]
      dsimp [Ψ]
      rw [inclusionN.naturality_assoc]
      first
        | rw [alternatingFaceMapComplex_map_cylinderι₀_comp_cylinderChainMap_assoc]
        | rw [alternatingFaceMapComplex_map_cylinderι₁_comp_cylinderChainMap_assoc]
      rw [PInftyToN.naturality, inclusionN_app_comp_PInftyToN_app_assoc]

/-- A simplicial homotopy `Homotopy f g` induces a chain homotopy between `N.map f` and `N.map g`
for the pseudoabelian normalized chain functor `Idempotents.DoldKan.N`. -/
def toNHomotopy {X Y : SimplicialObject C} {f g : X ⟶ Y} (h : Homotopy f g) :
    _root_.Homotopy (N.map f) (N.map g) :=
  h.toChainHomotopy.compLeftRightOfEq (inclusionN.app X) (PInftyToN.app Y)
    (N_map_eq_inclusionN_comp_PInftyToN f) (N_map_eq_inclusionN_comp_PInftyToN g)

/-- Any chain homotopy between `N.map f` and `N.map g` lifts to a simplicial homotopy
`Homotopy f g`. -/
def ofNHomotopy {X Y : SimplicialObject C} {f g : X ⟶ Y}
    (H : _root_.Homotopy (N.map f) (N.map g)) : Homotopy f g :=
  ofAlternatingFaceMapComplexHomotopy <|
    ((homotopyPInftyToId X).compRightId _).symm.trans <|
      (H.compLeftRightOfEq (PInftyToN.app X) (inclusionN.app Y)
        (PInfty_comp_alternatingFaceMapComplex_map_eq f)
        (PInfty_comp_alternatingFaceMapComplex_map_eq g)).trans
        ((homotopyPInftyToId X).compRightId _)

end Homotopy

/-- **Dold–Puppe, Satz 3.31** (alternating face map complex form): two morphisms `f, g : X ⟶ Y` of
simplicial objects in an idempotent-complete preadditive category with finite coproducts are
simplicially homotopic if and only if their alternating face map complex morphisms are chain
homotopic. -/
theorem nonempty_homotopy_iff_alternatingFaceMapComplex {X Y : SimplicialObject C}
    (f g : X ⟶ Y) :
    Nonempty (Homotopy f g) ↔
      Nonempty (_root_.Homotopy ((alternatingFaceMapComplex C).map f)
        ((alternatingFaceMapComplex C).map g)) :=
  ⟨fun ⟨h⟩ ↦ ⟨h.toChainHomotopy⟩, fun ⟨H⟩ ↦ ⟨Homotopy.ofAlternatingFaceMapComplexHomotopy H⟩⟩

/-- **Dold–Puppe, Satz 3.31** (normalized chain complex form): two morphisms `f, g : X ⟶ Y` of
simplicial objects in an idempotent-complete preadditive category with finite coproducts are
simplicially homotopic if and only if their normalized chain morphisms `N.map f` and `N.map g` are
chain homotopic. -/
theorem nonempty_homotopy_iff_N {X Y : SimplicialObject C} (f g : X ⟶ Y) :
    Nonempty (Homotopy f g) ↔ Nonempty (_root_.Homotopy (N.map f) (N.map g)) :=
  ⟨fun ⟨h⟩ ↦ ⟨h.toNHomotopy⟩, fun ⟨H⟩ ↦ ⟨Homotopy.ofNHomotopy H⟩⟩

namespace HomotopyEquiv

/-- A combinatorial simplicial homotopy equivalence induces a chain homotopy equivalence on
pseudoabelian normalized chain complexes `Idempotents.DoldKan.N`. -/
def toNHomotopyEquiv {X Y : SimplicialObject C} (e : HomotopyEquiv X Y) :
    _root_.HomotopyEquiv (N.obj X) (N.obj Y) where
  hom := N.map e.hom
  inv := N.map e.inv
  homotopyHomInvId :=
    (_root_.Homotopy.ofEq (N.map_comp e.hom e.inv).symm).trans <|
      e.homotopyHomInvId.toNHomotopy.trans <|
        _root_.Homotopy.ofEq (N.map_id X)
  homotopyInvHomId :=
    (_root_.Homotopy.ofEq (N.map_comp e.inv e.hom).symm).trans <|
      e.homotopyInvHomId.toNHomotopy.trans <|
        _root_.Homotopy.ofEq (N.map_id Y)

@[simp]
lemma toNHomotopyEquiv_hom {X Y : SimplicialObject C} (e : HomotopyEquiv X Y) :
    e.toNHomotopyEquiv.hom = N.map e.hom := (rfl)

@[simp]
lemma toNHomotopyEquiv_inv {X Y : SimplicialObject C} (e : HomotopyEquiv X Y) :
    e.toNHomotopyEquiv.inv = N.map e.inv := (rfl)

/-- A chain homotopy equivalence `e` between `K[X]` and `K[Y]` whose forward morphism is `K.map f`
lifts to a simplicial homotopy equivalence `HomotopyEquiv X Y` with forward morphism `f`. -/
def ofAlternatingFaceMapComplexHomotopyEquiv {X Y : SimplicialObject C} (f : X ⟶ Y)
    (e : _root_.HomotopyEquiv ((alternatingFaceMapComplex C).obj X)
      ((alternatingFaceMapComplex C).obj Y))
    (he : e.hom = (alternatingFaceMapComplex C).map f) :
    HomotopyEquiv X Y := by
  let hN : (N (C := C)).FullyFaithful :=
    (equivalence (C := C)).fullyFaithfulFunctor.ofIso (CategoryTheory.eqToIso equivalence_functor)
  let gN : N.obj Y ⟶ N.obj X := inclusionN.app Y ≫ e.inv ≫ PInftyToN.app X
  let g : Y ⟶ X := hN.preimage gN
  have hg : N.map g = gN := hN.map_preimage gN
  refine
    { hom := f
      inv := g
      homotopyHomInvId := Homotopy.ofNHomotopy <|
        e.homotopyHomInvId.compLeftRightOfEq (inclusionN.app X) (PInftyToN.app X) ?_ ?_
      homotopyInvHomId := Homotopy.ofNHomotopy <|
        e.homotopyInvHomId.compLeftRightOfEq (inclusionN.app Y) (PInftyToN.app Y) ?_ ?_ }
  · rw [Functor.map_comp, hg]; dsimp [gN]
    rw [inclusionN.naturality_assoc, ← he, Category.assoc]
  · rw [Category.id_comp, inclusionN_app_comp_PInftyToN_app, Functor.map_id]
  · rw [Functor.map_comp, hg]; dsimp [gN]
    rw [Category.assoc, Category.assoc, ← PInftyToN.naturality, ← he, Category.assoc]
  · rw [Category.id_comp, inclusionN_app_comp_PInftyToN_app, Functor.map_id]

@[simp]
lemma ofAlternatingFaceMapComplexHomotopyEquiv_hom {X Y : SimplicialObject C} (f : X ⟶ Y)
    (e : _root_.HomotopyEquiv ((alternatingFaceMapComplex C).obj X)
      ((alternatingFaceMapComplex C).obj Y))
    (he : e.hom = (alternatingFaceMapComplex C).map f) :
    (ofAlternatingFaceMapComplexHomotopyEquiv f e he).hom = f := (rfl)

end HomotopyEquiv

/-- A morphism `f : X ⟶ Y` of simplicial objects in an idempotent-complete preadditive category
with finite coproducts induces a chain homotopy equivalence on alternating face map complexes if
and only if `f` is the forward morphism of a simplicial homotopy equivalence. -/
theorem homotopyEquivalences_alternatingFaceMapComplex_map_iff
    {X Y : SimplicialObject C} (f : X ⟶ Y) :
    HomologicalComplex.homotopyEquivalences C (.down ℕ) ((alternatingFaceMapComplex C).map f) ↔
      ∃ e : HomotopyEquiv X Y, e.hom = f :=
  ⟨fun ⟨e, he⟩ ↦ ⟨HomotopyEquiv.ofAlternatingFaceMapComplexHomotopyEquiv f e he, rfl⟩,
    fun ⟨e, h⟩ ↦ h ▸ e.homotopyEquivalences_alternatingFaceMapComplex_map⟩

end Pseudoabelian

section Abelian

variable {A : Type u} [Category.{v} A] [Abelian A]

namespace Homotopy

/-- A simplicial homotopy `Homotopy f g` in an abelian category induces a chain homotopy on
normalized Moore complexes. -/
def toNormalizedMooreComplexHomotopy {X Y : SimplicialObject A} {f g : X ⟶ Y} (h : Homotopy f g) :
    _root_.Homotopy ((normalizedMooreComplex A).map f) ((normalizedMooreComplex A).map g) :=
  h.toNHomotopy.compLeftRightOfEq
    (Abelian.DoldKan.comparisonN.hom.app X) (Abelian.DoldKan.comparisonN.inv.app Y)
    (NatIso.naturality_2 Abelian.DoldKan.comparisonN f).symm
    (NatIso.naturality_2 Abelian.DoldKan.comparisonN g).symm

/-- A chain homotopy on normalized Moore complexes lifts to a simplicial homotopy `Homotopy f g`. -/
def ofNormalizedMooreComplexHomotopy {X Y : SimplicialObject A} {f g : X ⟶ Y}
    (H : _root_.Homotopy ((normalizedMooreComplex A).map f) ((normalizedMooreComplex A).map g)) :
    Homotopy f g :=
  ofNHomotopy <|
    H.compLeftRightOfEq
      (Abelian.DoldKan.comparisonN.inv.app X) (Abelian.DoldKan.comparisonN.hom.app Y)
      (NatIso.naturality_1 Abelian.DoldKan.comparisonN f).symm
      (NatIso.naturality_1 Abelian.DoldKan.comparisonN g).symm

end Homotopy

/-- **Dold–Puppe, Satz 3.31** (abelian normalized Moore complex form): two morphisms of simplicial
objects in an abelian category are simplicially homotopic if and only if their normalized Moore
complex morphisms are chain homotopic. -/
theorem nonempty_homotopy_iff_normalizedMooreComplex {X Y : SimplicialObject A} (f g : X ⟶ Y) :
    Nonempty (Homotopy f g) ↔
      Nonempty (_root_.Homotopy ((normalizedMooreComplex A).map f)
        ((normalizedMooreComplex A).map g)) :=
  ⟨fun ⟨h⟩ ↦ ⟨h.toNormalizedMooreComplexHomotopy⟩,
    fun ⟨H⟩ ↦ ⟨Homotopy.ofNormalizedMooreComplexHomotopy H⟩⟩

end Abelian

end CategoryTheory.SimplicialObject

namespace CategoryTheory.Idempotents.DoldKan

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteCoproducts C]
  [IsIdempotentComplete C]

/-- The inverse Dold–Kan functor `Γ : ChainComplex C ℕ ⥤ SimplicialObject C` carries chain
homotopies to combinatorial simplicial homotopies. -/
def Γ.mapHomotopy {K L : ChainComplex C ℕ} {φ ψ : K ⟶ L} (H : Homotopy φ ψ) :
    SimplicialObject.Homotopy (Γ.map φ) (Γ.map ψ) :=
  SimplicialObject.Homotopy.ofNHomotopy <|
    H.compLeftRightOfEq ((η (C := C)).hom.app K) ((η (C := C)).inv.app L)
      (NatIso.naturality_2 (η (C := C)) φ).symm
      (NatIso.naturality_2 (η (C := C)) ψ).symm

/-- Two chain maps `φ, ψ : K ⟶ L` are chain homotopic if and only if `Γ.map φ` and `Γ.map ψ` are
simplicially homotopic. -/
theorem nonempty_homotopy_Γ_map_iff {K L : ChainComplex C ℕ} (φ ψ : K ⟶ L) :
    Nonempty (SimplicialObject.Homotopy (Γ.map φ) (Γ.map ψ)) ↔ Nonempty (Homotopy φ ψ) :=
  ⟨fun ⟨h⟩ ↦ ⟨h.toNHomotopy.compLeftRightOfEq ((η (C := C)).inv.app K) ((η (C := C)).hom.app L)
      (NatIso.naturality_1 (η (C := C)) φ).symm
      (NatIso.naturality_1 (η (C := C)) ψ).symm⟩,
    fun ⟨H⟩ ↦ ⟨Γ.mapHomotopy H⟩⟩

/-- The inverse Dold–Kan functor `Γ` carries chain homotopy equivalences to simplicial homotopy
equivalences. -/
def Γ.mapHomotopyEquiv {K L : ChainComplex C ℕ} (e : HomotopyEquiv K L) :
    SimplicialObject.HomotopyEquiv (Γ.obj K) (Γ.obj L) where
  hom := Γ.map e.hom
  inv := Γ.map e.inv
  homotopyHomInvId :=
    ((Γ.mapHomotopy e.homotopyHomInvId).congrLeft (Γ.map_comp e.hom e.inv)).congrRight
      (Γ.map_id K)
  homotopyInvHomId :=
    ((Γ.mapHomotopy e.homotopyInvHomId).congrLeft (Γ.map_comp e.inv e.hom)).congrRight
      (Γ.map_id L)

@[simp]
lemma Γ.mapHomotopyEquiv_hom {K L : ChainComplex C ℕ} (e : HomotopyEquiv K L) :
    (Γ.mapHomotopyEquiv e).hom = Γ.map e.hom := (rfl)

@[simp]
lemma Γ.mapHomotopyEquiv_inv {K L : ChainComplex C ℕ} (e : HomotopyEquiv K L) :
    (Γ.mapHomotopyEquiv e).inv = Γ.map e.inv := (rfl)

end CategoryTheory.Idempotents.DoldKan
