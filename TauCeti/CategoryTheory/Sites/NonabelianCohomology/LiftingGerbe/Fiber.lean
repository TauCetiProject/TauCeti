/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic
public import TauCeti.CategoryTheory.Sites.NonabelianCohomology.Map
public import TauCeti.CategoryTheory.Sites.NonabelianCohomology.Torsor.Map

/-!
# The groupoid of lifts of a torsor

For a homomorphism `φ : B ⟶ D` of sheaves of groups and a `D`-torsor `P`,
`Torsor.LiftingFiber φ P` is the groupoid of `B`-torsors equipped with an isomorphism from
their extension of structure group to `P`. It is the costructured-arrow category of
`Torsor.mapFunctor φ` at `P`; all its structure arrows are automatically invertible.

The projection is `CostructuredArrow.proj _ P`. An arrow `f : L ⟶ M` has underlying
`B`-torsor morphism `f.left`, and `CostructuredArrow.w f` states the compatibility with the
structure isomorphisms. Use `CostructuredArrow.homMk` and `CostructuredArrow.isoMk` to
construct arrows and isomorphisms. An isomorphism of target torsors induces the equivalence
`CostructuredArrow.mapIso`.

Nonemptiness is equivalent to the class of `P` belonging to the image on nonabelian `H¹`.
In particular the trivial torsor lifts, and every torsor lifts along a split homomorphism.

## References

J. S. Milne, *Étale Cohomology*, IV §2, p. 9, and Olsson's stack lectures,
Remark 31.8, for the groupoid of lifts underlying a lifting gerbe.
-/

public noncomputable section

open CategoryTheory Opposite

universe w v u

namespace CategoryTheory.Sheaf.Torsor

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasWeakSheafify J (Type w)] [J.WEqualsLocallyBijective (Type w)]
  {B D : Sheaf J GrpCat.{w}}

/-- The groupoid of lifts of a `D`-torsor through `φ : B ⟶ D`: objects are `B`-torsors `Q`
with an isomorphism `Q.map φ ≅ P`, and arrows are equivariant isomorphisms commuting with it. -/
abbrev LiftingFiber (φ : B ⟶ D) (P : Torsor D) := CostructuredArrow (mapFunctor φ) P

namespace LiftingFiber

variable (φ : B ⟶ D) (P : Torsor D)

/-- Every arrow in the fibre is invertible. -/
instance : IsGroupoid (LiftingFiber φ P) :=
  isGroupoid_of_reflects_iso (CostructuredArrow.proj _ _)

/-- A lift exists exactly when the torsor class is in the image of extension of structure group. -/
theorem nonempty_iff :
    Nonempty (LiftingFiber φ P) ↔ NonabelianH1.mk P ∈ Set.range (NonabelianH1.map φ) := by
  constructor
  · rintro ⟨L⟩
    exact ⟨NonabelianH1.mk L.left, (NonabelianH1.map_mk φ L.left).trans
      (NonabelianH1.mk_eq_mk_of_hom L.hom)⟩
  · rintro ⟨c, hc⟩
    obtain ⟨Q, rfl⟩ := NonabelianH1.mk_surjective c
    obtain ⟨α⟩ := NonabelianH1.mk_eq_mk_iff.mp ((NonabelianH1.map_mk φ Q).symm.trans hc)
    exact ⟨CostructuredArrow.mk α.hom⟩

/-- The trivial torsor has the lift given by the trivial `B`-torsor. -/
def trivial : LiftingFiber φ (Torsor.trivial D) :=
  CostructuredArrow.mk <| (Torsor.trivial B).mapLift
    ((sheafCompose J (forget GrpCat.{w})).map φ)
    fun U g p ↦ map_mul (φ.hom.app U).hom g p

@[simp]
lemma trivial_left : (trivial φ).left = Torsor.trivial B := (rfl)

/-- The chosen trivial lift extends the underlying coefficient homomorphism. -/
@[simp]
lemma toMap_trivial_hom :
    (trivial φ).left.toMap φ ≫ (trivial φ).hom.hom =
      eqToHom (congrArg Torsor.sheaf (trivial_left φ)) ≫
        (sheafCompose J (forget GrpCat.{w})).map φ := by
  exact (Torsor.trivial B).toMap_mapLift _ _

/-- Every torsor lifts along a homomorphism with a specified right inverse. -/
theorem nonempty_of_split (s : D ⟶ B) (hs : s ≫ φ = 𝟙 D) :
    Nonempty (LiftingFiber φ P) := by
  apply (nonempty_iff φ P).mpr
  refine ⟨NonabelianH1.map s (NonabelianH1.mk P), ?_⟩
  rw [NonabelianH1.map_map, hs, NonabelianH1.map_id]
  rfl

end LiftingFiber

end CategoryTheory.Sheaf.Torsor
