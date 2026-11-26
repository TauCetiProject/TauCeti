/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Functor.ReflectsIso.Jointly
public import Mathlib.CategoryTheory.Sites.CoversTop.Basic
public import Mathlib.CategoryTheory.Sites.Over

/-!
# Common refinements and joint faithfulness for covering families

Given two families of objects `X₁` and `X₂` that cover the terminal object of a site, this file
constructs a third covering family each of whose members maps to a member of `X₁` and to a member
of `X₂`. It also shows that for any family `Y` covering the terminal object of `(C, J)`, the
restriction functors `J.overPullback A (Y i) : Sheaf J A ⥤ Sheaf (J.over (Y i)) A` are jointly
faithful (and therefore jointly reflect epimorphisms) for any coefficient category `A`. For sieves
on a single object, the intersection of a finite family of covering sieves is covering
(`CategoryTheory.GrothendieckTopology.iInf_covering`).

## Main declarations

* `CategoryTheory.GrothendieckTopology.iInf_covering`,
  `CategoryTheory.GrothendieckTopology.iInf_covering_iff`: the intersection of a finite family of
  sieves is covering if and only if every member is.
* `CategoryTheory.GrothendieckTopology.CoversTop.CommonRefinement`: a covering family together
  with arrows from each of its members to a member of each of two given families.
* `CategoryTheory.GrothendieckTopology.CoversTop.commonRefinement`: a common refinement of two
  families covering the terminal object.
* `CategoryTheory.GrothendieckTopology.CoversTop.jointlyFaithful_overPullback` and
  `CategoryTheory.GrothendieckTopology.CoversTop.jointlyReflectEpimorphisms_overPullback`:
  restrictions to slice sites over a covering family are jointly faithful and jointly reflect
  epimorphisms.
-/

public section

open CategoryTheory

universe w u v

namespace CategoryTheory.GrothendieckTopology

variable {C : Type u} [Category.{v} C]

/-- The intersection of a finite family of covering sieves is covering. -/
theorem iInf_covering (J : GrothendieckTopology C) {ι : Type*} [Finite ι] {X : C}
    {R : ι → Sieve X} (hR : ∀ i, R i ∈ J X) : ⨅ i, R i ∈ J X := by
  cases nonempty_fintype ι
  simpa [Finset.inf_eq_iInf] using Finset.inf_induction (p := (· ∈ J X)) (J.top_mem X)
    (fun _ h₁ _ h₂ ↦ J.intersection_covering h₁ h₂) fun i (_ : i ∈ Finset.univ) ↦ hR i

/-- The intersection of a finite family of sieves is covering if and only if every member is. -/
@[simp]
theorem iInf_covering_iff (J : GrothendieckTopology C) {ι : Type*} [Finite ι] {X : C}
    {R : ι → Sieve X} : ⨅ i, R i ∈ J X ↔ ∀ i, R i ∈ J X :=
  ⟨fun h i ↦ J.superset_covering (iInf_le R i) h, J.iInf_covering⟩

end CategoryTheory.GrothendieckTopology

namespace CategoryTheory.GrothendieckTopology.CoversTop

variable {C : Type u} [Category.{v} C]

/-- A common refinement of two covering families.

Each object in the refined family admits arrows to one member of each original family. -/
structure CommonRefinement (J : GrothendieckTopology C) {I₁ I₂ : Type*}
    (X₁ : I₁ → C) (X₂ : I₂ → C) where
  /-- The indexing type of the common refinement. -/
  I : Type w
  /-- The objects in the common refinement. -/
  X : I → C
  /-- The member of the first covering family above each refined object. -/
  leftIndex : I → I₁
  /-- The arrow from each refined object to its member of the first covering family. -/
  left : ∀ i, X i ⟶ X₁ (leftIndex i)
  /-- The member of the second covering family above each refined object. -/
  rightIndex : I → I₂
  /-- The arrow from each refined object to its member of the second covering family. -/
  right : ∀ i, X i ⟶ X₂ (rightIndex i)
  /-- The refined family covers the top. -/
  coversTop : J.CoversTop X

/-- A common refinement of two families covering the terminal object.

The refined family consists of all objects admitting an arrow to a member of each original
family, so it is indexed by a type in the universe of the objects of `C`. -/
noncomputable def commonRefinement {I₁ I₂ : Type*} {X₁ : I₁ → C} {X₂ : I₂ → C}
    {J : GrothendieckTopology C} (h₁ : J.CoversTop X₁) (h₂ : J.CoversTop X₂) :
    CommonRefinement.{u} J X₁ X₂ where
  I := {W : C // (∃ i, Nonempty (W ⟶ X₁ i)) ∧ ∃ j, Nonempty (W ⟶ X₂ j)}
  X := Subtype.val
  leftIndex w := w.property.1.choose
  left w := w.property.1.choose_spec.some
  rightIndex w := w.property.2.choose
  right w := w.property.2.choose_spec.some
  coversTop A := J.superset_covering (fun Z _ hZ ↦ ⟨⟨Z, hZ⟩, ⟨𝟙 Z⟩⟩)
    (J.intersection_covering (h₁ A) (h₂ A))

/-- If `Y : I → C` covers the terminal object for `J`, then the restriction functors
`J.overPullback A (Y i) : Sheaf J A ⥤ Sheaf (J.over (Y i)) A` are jointly faithful for any
coefficient category `A`. -/
theorem jointlyFaithful_overPullback {I : Type*} {Y : I → C} {J : GrothendieckTopology C}
    (hY : J.CoversTop Y) (A : Type*) [Category* A] :
    JointlyFaithful (fun i ↦ J.overPullback A (Y i)) where
  map_injective {F G φ ψ} h := by
    ext ⟨W⟩
    refine G.property.hom_ext (hY.cover W) _ _ ?_
    rintro ⟨Z, a, ⟨i, ⟨b⟩⟩⟩
    have hi : φ.hom.app (Opposite.op Z) = ψ.hom.app (Opposite.op Z) :=
      congr(($(h i)).hom.app (Opposite.op (Over.mk b)))
    rw [← φ.hom.naturality, ← ψ.hom.naturality, hi]

/-- If `Y : I → C` covers the terminal object for `J`, then the restriction functors
`J.overPullback A (Y i) : Sheaf J A ⥤ Sheaf (J.over (Y i)) A` jointly reflect epimorphisms for any
coefficient category `A`. -/
theorem jointlyReflectEpimorphisms_overPullback {I : Type*} {Y : I → C}
    {J : GrothendieckTopology C} (hY : J.CoversTop Y) (A : Type*) [Category* A] :
    JointlyReflectEpimorphisms (fun i ↦ J.overPullback A (Y i)) :=
  (hY.jointlyFaithful_overPullback A).jointlyReflectEpimorphisms

end CategoryTheory.GrothendieckTopology.CoversTop
