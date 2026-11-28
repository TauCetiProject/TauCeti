/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.IsConnected
public import Mathlib.CategoryTheory.Limits.Shapes.Terminal
public import Mathlib.Topology.Homotopy.Contractible
public import TauCeti.AlgebraicTopology.ClassifyingSpace.Category.Basic
public import TauCeti.AlgebraicTopology.SimplicialSet.Nerve.NatTrans
public import TauCeti.AlgebraicTopology.SimplicialSet.Realization.Prism

/-!
# Homotopies of classifying spaces induced by natural transformations

A natural transformation `η : F ⟶ G` between functors `F G : C ⥤ D` induces a homotopy
`η.classifyingSpaceHomotopy` from `BF` to `BG`: the realization of the simplicial homotopy of
nerves `CategoryTheory.NatTrans.nerveHomotopy`. Its track at the vertex `[c]` of an object `c` is
the edge path of `η.app c` (`CategoryTheory.NatTrans.classifyingSpaceHomotopy_apply_vertex`).

Natural transformations need not have invertible components, and homotopy is symmetric, so
functors joined by a zigzag of natural transformations, in either direction, have homotopic
classifying spaces (`CategoryTheory.Functor.classifyingSpaceMap_homotopic_of_zigzag`). Hence:

* an adjunction `L ⊣ R` makes `BL` and `BR` mutually inverse homotopy equivalences, through its
  unit and counit (`CategoryTheory.Adjunction.classifyingSpaceHomotopyEquiv`), and so does an
  equivalence of categories (`CategoryTheory.Equivalence.classifyingSpaceHomotopyEquiv`);
* a category in which the identity functor is joined by a zigzag to a constant functor has a
  contractible classifying space
  (`TauCeti.CategoryTheory.contractibleSpace_classifyingSpace_of_zigzag`), as the classifying space
  of a constant functor is constant (`CategoryTheory.Functor.classifyingSpaceMap_const`). In
  particular this holds for a category with a terminal or an initial object
  (`CategoryTheory.Limits.IsTerminal.contractibleSpace_classifyingSpace`,
  `CategoryTheory.Limits.IsInitial.contractibleSpace_classifyingSpace`). The empty category has
  neither, and its classifying space is empty.

## References

* D. Quillen, *Higher algebraic K-theory: I*, Lecture Notes in Math. 341 (1973), §1, Prop. 2 and
  its Corollaries 1 and 2.
* C. A. Weibel, *The K-book*, Grad. Stud. Math. 145 (2013), Chapter IV, 3.2, Example 3.2.1 and
  Example 3.2.2.
-/

public section

open CategoryTheory Simplicial unitInterval TauCeti.CategoryTheory classifyingSpace

universe v u

namespace CategoryTheory.NatTrans

variable {C D : Type u} [Category.{v} C] [Category.{v} D] {F G : C ⥤ D}

/-- The homotopy from `BF` to `BG` induced by a natural transformation `η : F ⟶ G`: the
realization of the simplicial homotopy of nerves given by `η`. -/
noncomputable def classifyingSpaceHomotopy (η : F ⟶ G) :
    TopCat.Homotopy F.classifyingSpaceMap G.classifyingSpaceMap :=
  η.nerveHomotopy.toTop

/-- The homotopy induced by `η` is the realization of the simplicial homotopy of nerves
`η.nerveHomotopy`. -/
theorem classifyingSpaceHomotopy_def (η : F ⟶ G) :
    η.classifyingSpaceHomotopy = η.nerveHomotopy.toTop :=
  (rfl)

/-- The homotopy induced by `η` moves the vertex `[c]` along the edge path of `η.app c`. -/
@[simp]
theorem classifyingSpaceHomotopy_apply_vertex (η : F ⟶ G) (t : I) (c : C) :
    η.classifyingSpaceHomotopy (t, vertex c) = edge (η.app c) t := by
  -- Over the vertex `[c]` the triangulated cylinder traces the vertical edge `{c} × Δ[1]`, which
  -- the simplicial homotopy sends to the edge `η.app c`, whose path is `edge (η.app c)`.
  rw [classifyingSpaceHomotopy_def, SSet.Homotopy.toTop_apply, vertex,
    SSet.toTopPoint_eq_toTopObjMk (X := nerve C) (nerveEquiv.symm c) default,
    SSet.toTopCylinder_toTopObjMk_verticalEdge (X := nerve C) (nerveEquiv.symm c) default t,
    SSet.toTop_map_toTopObjMk, nerveHomotopy_h_app_verticalEdge, edge_eq_toTopPath]
  exact (SSet.Edge.toTopPath_apply _ t).symm

end CategoryTheory.NatTrans

namespace CategoryTheory.Functor

variable {C D : Type u} [Category.{v} C] [Category.{v} D]

/-- Functors joined by a zigzag of natural transformations have homotopic classifying spaces. -/
theorem classifyingSpaceMap_homotopic_of_zigzag {F G : C ⥤ D} (h : Zigzag F G) :
    F.classifyingSpaceMap.hom.Homotopic G.classifyingSpaceMap.hom := by
  induction h with
  | refl => exact .refl _
  | tail _ hzag ih =>
    obtain ⟨⟨η⟩⟩ | ⟨⟨η⟩⟩ := hzag
    exacts [ih.trans ⟨η.classifyingSpaceHomotopy⟩, ih.trans ⟨η.classifyingSpaceHomotopy.symm⟩]

/-- The classifying space of the constant functor at `d` is the constant map at the vertex
`[d]`. -/
@[simp]
theorem classifyingSpaceMap_const (d : D) :
    ((Functor.const C).obj d).classifyingSpaceMap.hom = ContinuousMap.const _ (vertex d) := by
  have h : ((Functor.const C).obj d).classifyingSpaceMap =
      TopCat.ofHom (ContinuousMap.const _ (vertex d)) := by
    refine SSet.toTop_hom_ext fun n x w ↦ ?_
    -- The image of every simplex is the degenerate simplex at `d`. Both are strings of identity
    -- arrows of `d`, and so are the `eqToHom`s between their (definitionally equal) objects.
    have hx : (nerveMap ((Functor.const C).obj d)).app _ x =
        (nerve D).map (SimplexCategory.const ⦋n⦌ ⦋0⦌ 0).op (nerveEquiv.symm d) :=
      Functor.ext (fun _ ↦ rfl) (fun _ _ _ ↦ (by simp : 𝟙 d = 𝟙 d ≫ 𝟙 d ≫ 𝟙 d))
    rw [SSet.toTop_map_toTopObjMk, hx,
      SSet.toTopObjMk_map (X := nerve D) _ (nerveEquiv.symm d) w]
    exact (SSet.toTopPoint_eq_toTopObjMk _ _).symm
  rw [h, TopCat.hom_ofHom]

end CategoryTheory.Functor

namespace CategoryTheory.Adjunction

variable {C D : Type u} [Category.{v} C] [Category.{v} D] {L : C ⥤ D} {R : D ⥤ C}

/-- An adjunction `L ⊣ R` makes the classifying spaces `BL` and `BR` mutually inverse homotopy
equivalences, through the homotopies induced by its unit and counit. -/
noncomputable def classifyingSpaceHomotopyEquiv (adj : L ⊣ R) :
    ContinuousMap.HomotopyEquiv (classifyingSpace C) (classifyingSpace D) where
  toFun := L.classifyingSpaceMap.hom
  invFun := R.classifyingSpaceMap.hom
  left_inv := by
    have := adj.unit.classifyingSpaceHomotopy.symm
    rw [Functor.classifyingSpaceMap_comp, Functor.classifyingSpaceMap_id] at this
    exact ⟨this⟩
  right_inv := by
    have := adj.counit.classifyingSpaceHomotopy
    rw [Functor.classifyingSpaceMap_comp, Functor.classifyingSpaceMap_id] at this
    exact ⟨this⟩

/-- The homotopy equivalence of an adjunction `L ⊣ R` is `BL`. -/
@[simp]
lemma classifyingSpaceHomotopyEquiv_apply (adj : L ⊣ R) (x : classifyingSpace C) :
    adj.classifyingSpaceHomotopyEquiv x = L.classifyingSpaceMap.hom x :=
  (rfl)

/-- The homotopy inverse of the homotopy equivalence of an adjunction `L ⊣ R` is `BR`. -/
@[simp]
lemma classifyingSpaceHomotopyEquiv_symm_apply (adj : L ⊣ R) (y : classifyingSpace D) :
    adj.classifyingSpaceHomotopyEquiv.symm y = R.classifyingSpaceMap.hom y :=
  (rfl)

end CategoryTheory.Adjunction

namespace CategoryTheory.Equivalence

variable {C D : Type u} [Category.{v} C] [Category.{v} D]

/-- An equivalence of categories `e : C ≌ D` induces a homotopy equivalence of classifying spaces
with underlying map `B(e.functor)` and homotopy inverse `B(e.inverse)`. -/
noncomputable def classifyingSpaceHomotopyEquiv (e : C ≌ D) :
    ContinuousMap.HomotopyEquiv (classifyingSpace C) (classifyingSpace D) :=
  e.toAdjunction.classifyingSpaceHomotopyEquiv

/-- The homotopy equivalence of an equivalence of categories `e` is `B(e.functor)`. -/
@[simp]
lemma classifyingSpaceHomotopyEquiv_apply (e : C ≌ D) (x : classifyingSpace C) :
    e.classifyingSpaceHomotopyEquiv x = e.functor.classifyingSpaceMap.hom x :=
  (rfl)

/-- The homotopy inverse of the homotopy equivalence of an equivalence of categories `e` is
`B(e.inverse)`. -/
@[simp]
lemma classifyingSpaceHomotopyEquiv_symm_apply (e : C ≌ D) (y : classifyingSpace D) :
    e.classifyingSpaceHomotopyEquiv.symm y = e.inverse.classifyingSpaceMap.hom y :=
  (rfl)

end CategoryTheory.Equivalence

namespace TauCeti.CategoryTheory

variable {C : Type u} [Category.{v} C]

/-- A category whose identity functor is joined by a zigzag of natural transformations to the
constant functor at some object has a contractible classifying space. -/
theorem contractibleSpace_classifyingSpace_of_zigzag {c : C}
    (h : Zigzag (𝟭 C) ((Functor.const C).obj c)) : ContractibleSpace (classifyingSpace C) := by
  have hc := Functor.classifyingSpaceMap_homotopic_of_zigzag h
  rw [Functor.classifyingSpaceMap_id, Functor.classifyingSpaceMap_const, TopCat.hom_id] at hc
  have : Nonempty C := ⟨c⟩
  exact (contractible_iff_id_nullhomotopic _).2 ⟨vertex c, hc⟩

end TauCeti.CategoryTheory

namespace CategoryTheory.Limits

open TauCeti.CategoryTheory

variable {C : Type u} [Category.{v} C]

/-- A category with a terminal object has a contractible classifying space: the arrows to the
terminal object form a natural transformation from the identity functor to a constant functor. -/
theorem IsTerminal.contractibleSpace_classifyingSpace {t : C} (ht : IsTerminal t) :
    ContractibleSpace (classifyingSpace C) :=
  contractibleSpace_classifyingSpace_of_zigzag (c := t)
    (Zigzag.of_hom { app := ht.from, naturality _ _ _ := ht.hom_ext _ _ })

/-- A category with an initial object has a contractible classifying space: the arrows from the
initial object form a natural transformation from a constant functor to the identity functor. -/
theorem IsInitial.contractibleSpace_classifyingSpace {i : C} (hi : IsInitial i) :
    ContractibleSpace (classifyingSpace C) :=
  contractibleSpace_classifyingSpace_of_zigzag (c := i)
    (Zigzag.of_inv { app := hi.to, naturality _ _ _ := hi.hom_ext _ _ })

/-- A category with a terminal object has a contractible classifying space. -/
instance [HasTerminal C] : ContractibleSpace (classifyingSpace C) :=
  terminalIsTerminal.contractibleSpace_classifyingSpace

/-- A category with an initial object has a contractible classifying space. -/
instance [HasInitial C] : ContractibleSpace (classifyingSpace C) :=
  initialIsInitial.contractibleSpace_classifyingSpace

end CategoryTheory.Limits
