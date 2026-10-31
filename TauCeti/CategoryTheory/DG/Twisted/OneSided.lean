/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.DG.Twisted.Triangulated
public import Mathlib.CategoryTheory.Triangulated.Subcategory

/-!
# One-sided twisted objects and the pretriangulated envelope

A twisted object `(⊕ᵢ Xᵢ, δ)` of the additive closure of a differential graded category is
**one-sided** when its twisting matrix is strictly triangular for some grading of its summands by
natural numbers: there is a function `level` on the summands such that the entry `δᵢⱼ` of `δ`
from `Xᵢ` to `Xⱼ` vanishes whenever `level i ≤ level j`
(`TauCeti.DGTwistedObject.IsOneSided`).  So `δ` only lowers the level, and in particular has no
diagonal entries.  The entries of `δ` lie in different Hom complexes, so this is a dependent
analogue of Mathlib's `Matrix.BlockTriangular` rather than an instance of it.  Over the additive
closure of the shift closure of a DG category `C`, the one-sided twisted objects
`(⊕ᵢ Xᵢ[rᵢ], δ)` are the one-sided twisted complexes of Bondal and Kapranov, the objects of the
pretriangulated envelope `pretr(C)`.

The homotopy category `H⁰` of all twisted objects of the additive closure of the shift closure of
`C` is triangulated (`TauCeti.DGTwistedObject.isTriangulated`), with the cone triangles
`P ⟶ Q ⟶ cone u ⟶ P⟦1⟧` as distinguished triangles.  This file shows that the one-sided twisted
objects form a **triangulated subcategory** of `H⁰`, in the sense of Mathlib's
`CategoryTheory.ObjectProperty.IsTriangulated`
(`TauCeti.DGTwistedObject.isTriangulated_oneSided`):

* the twisted object with no summands is one-sided, and is a zero object of `H⁰`;
* the shift `(⊕ᵢ Xᵢ[rᵢ + n], δ)` of a one-sided twisted object is one-sided, for the same levels;
* the extension of two one-sided twisted objects along any closed degree-one morphism is
  one-sided, by placing every summand of the quotient above every summand of the sub-object; in
  particular the cone `Q ⊕ P⟦1⟧` of a closed degree-zero morphism `P ⟶ Q` of one-sided twisted
  objects is one-sided.

The third object of a distinguished triangle whose first two objects are one-sided is therefore
isomorphic to a one-sided twisted object: a distinguished triangle is isomorphic to the cone
triangle of any closed representative of its first morphism.  Every twisted object with zero
twist, such as the image of an object `X` of `C` as the one-term sum `X[0]`, is one-sided.

Mathlib then equips the full subcategory `(TauCeti.DGTwistedObject.oneSided R C).FullSubcategory`,
the homotopy category `H⁰(pretr C)` of the pretriangulated envelope, with a triangulated structure
whose inclusion into `H⁰` is a triangulated functor.

## Main definitions

* `TauCeti.DGTwistedObject.IsOneSided`: a twisted object of an additive closure whose twisting
  matrix is strictly triangular for some levels of its summands.
* `TauCeti.DGTwistedObject.oneSided`: the one-sided twisted objects of the additive closure of
  the shift closure, as a property of objects of the homotopy category.

## Main results

* `TauCeti.DGTwistedObject.IsOneSided.extension`: extensions of one-sided twisted objects are
  one-sided.
* `TauCeti.DGTwistedObject.IsOneSided.shift` and `TauCeti.DGTwistedObject.IsOneSided.cone`:
  shifts and cones of one-sided twisted objects are one-sided.
* `TauCeti.DGTwistedObject.isTriangulated_oneSided`: the one-sided twisted objects form a
  triangulated subcategory of the homotopy category of twisted objects.

## References

* A. I. Bondal and M. M. Kapranov, *Enhanced triangulated categories*, Section 1.
* V. Drinfeld, *DG quotients of DG categories*, Section 2.4.
-/

public section

open CategoryTheory Limits Pretriangulated

namespace TauCeti

universe v u

namespace DGTwistedObject

/- `matrixEquiv` is a local name for `TauCeti.DGAdditiveClosure.dgHomEquiv`, which identifies a
morphism of the additive closure with its matrix of entries; the unqualified name `dgHomEquiv`
refers to `TauCeti.DGTwistedObject.dgHomEquiv` in this namespace. -/
open DGAdditiveClosure renaming dgHomEquiv → matrixEquiv

variable {R : Type v} [CommRing R]

/-! ### One-sided twisted objects of an additive closure -/

section additiveClosure

variable {E : Type u} [DGCategory R E]

/-- A twisted object `(⊕ᵢ Xᵢ, δ)` of the additive closure is **one-sided** when its twisting
matrix is strictly triangular for some levels of its summands: there is a function `level` from
the summands to `ℕ` such that the entry `δᵢⱼ : Xᵢ ⟶ Xⱼ` vanishes whenever
`level i ≤ level j`. -/
def IsOneSided (P : DGTwistedObject R (DGAdditiveClosure E)) : Prop :=
  ∃ level : P.obj.ι → ℕ, ∀ i j, level i ≤ level j → matrixEquiv R _ _ 1 P.twist i j = 0

/-- The defining property of a one-sided twisted object: its twisting matrix vanishes on every entry
which does not lower the level, for some levels of its summands. -/
theorem isOneSided_iff (P : DGTwistedObject R (DGAdditiveClosure E)) :
    P.IsOneSided ↔
      ∃ level : P.obj.ι → ℕ, ∀ i j, level i ≤ level j → matrixEquiv R _ _ 1 P.twist i j = 0 :=
  Iff.rfl

/-- The twisting matrix of a one-sided twisted object has no diagonal entries. -/
theorem IsOneSided.dgHomEquiv_twist_self {P : DGTwistedObject R (DGAdditiveClosure E)}
    (hP : P.IsOneSided) (i : P.obj.ι) : matrixEquiv R _ _ 1 P.twist i i = 0 := by
  obtain ⟨level, h⟩ := hP
  exact h i i le_rfl

/-- A twisted object with no summands is one-sided. -/
theorem isOneSided_of_isEmpty (P : DGTwistedObject R (DGAdditiveClosure E)) [IsEmpty P.obj.ι] :
    P.IsOneSided :=
  ⟨fun _ ↦ 0, fun i ↦ isEmptyElim i⟩

/-- An object of the additive closure with the zero twist is a one-sided twisted object. -/
theorem isOneSided_ofObj (M : DGAdditiveClosure E) : (ofObj R M).IsOneSided :=
  ⟨fun _ ↦ 0, fun i j _ ↦ by simp⟩

/-- **Extensions of one-sided twisted objects are one-sided**: if `P` and `Q` are one-sided, so is
the extension `(P ⊕ Q, δ)` along any closed degree-one morphism `Q ⟶ P`.  The levels of the
summands of `P` are kept, and those of the summands of `Q` are raised above all of them, so that
the off-diagonal block of `δ`, which runs from `Q` to `P`, lowers the level. -/
theorem IsOneSided.extension {P Q : DGTwistedObject R (DGAdditiveClosure E)}
    (hP : P.IsOneSided) (hQ : Q.IsOneSided) {g : DGHom R 1 Q P} (hg : dgDifferential R 1 g = 0) :
    (DGTwistedObject.extension P Q g hg).IsOneSided := by
  obtain ⟨levelP, hlevelP⟩ := hP
  obtain ⟨levelQ, hlevelQ⟩ := hQ
  -- A bound `N` for the levels of the summands of `P`, which the summands of `Q` are placed above.
  obtain ⟨N, hN⟩ : ∃ N, ∀ i, levelP i < N :=
    ⟨Finset.univ.sup levelP + 1, fun i ↦ Nat.lt_succ_of_le (Finset.le_sup (Finset.mem_univ i))⟩
  refine ⟨Sum.elim levelP fun j ↦ levelQ j + N, ?_⟩
  rintro (i | i) (j | j) h <;> simp only [Sum.elim_inl, Sum.elim_inr] at h
  · simpa using hlevelP i j h
  · simp
  · have := hN j
    omega
  · simpa using hlevelQ i j (by omega)

end additiveClosure

/-! ### Shifts and cones -/

section shiftClosure

variable {C : Type u} [DGCategory R C]

/-- **Shifts of one-sided twisted objects are one-sided**: shifting every summand by `n` does not
change the entries of the twisting matrix, so the same levels work. -/
theorem IsOneSided.shift {P : DGTwistedObject R (DGAdditiveClosure (DGShiftClosure C))}
    (hP : P.IsOneSided) (n : ℤ) : ((shiftFunctor R n).obj P).IsOneSided := by
  obtain ⟨level, h⟩ := hP
  refine ⟨level, fun i j hij ↦ ?_⟩
  rw [dgHomEquiv_twist_shiftFunctor_obj, h i j hij, map_zero]

/-- **Cones of morphisms of one-sided twisted objects are one-sided**: the cone `Q ⊕ P⟦1⟧` of a
closed degree-zero morphism `P ⟶ Q` is the extension of the one-sided twisted objects `Q` and
`P⟦1⟧`. -/
theorem IsOneSided.cone {P Q : DGTwistedObject R (DGAdditiveClosure (DGShiftClosure C))}
    (hP : P.IsOneSided) (hQ : Q.IsOneSided) {u : DGHom R 0 P Q} (hu : dgDifferential R 0 u = 0) :
    (DGTwistedObject.cone u hu).IsOneSided :=
  hQ.extension (hP.shift 1) _

/-! ### The triangulated subcategory of one-sided twisted objects -/

open DGHomotopyCategory

variable (R C) in
/-- The **one-sided twisted objects** of the additive closure of the shift closure of `C`, as a
property of objects of the homotopy category of twisted objects.  The full subcategory it defines
is the homotopy category `H⁰(pretr C)` of the pretriangulated envelope of Bondal and Kapranov. -/
def oneSided :
    ObjectProperty
      (DGHomotopyCategory R (DGTwistedObject R (DGAdditiveClosure (DGShiftClosure C)))) :=
  fun X ↦ (underlying R X).IsOneSided

/-- An object of the homotopy category is one-sided when its underlying twisted object is. -/
theorem oneSided_iff
    (X : DGHomotopyCategory R (DGTwistedObject R (DGAdditiveClosure (DGShiftClosure C)))) :
    oneSided R C X ↔ (underlying R X).IsOneSided :=
  Iff.rfl

@[simp]
theorem oneSided_of_iff (P : DGTwistedObject R (DGAdditiveClosure (DGShiftClosure C))) :
    oneSided R C (of R P) ↔ P.IsOneSided := by
  rw [oneSided_iff, underlying_of]

/-- The one-sided twisted objects contain a zero object of the homotopy category: the twisted
object with no summands. -/
instance : (oneSided R C).ContainsZero where
  exists_zero :=
    let P := ofObj R (⟨PEmpty, PEmpty.elim⟩ : DGAdditiveClosure (DGShiftClosure C))
    ⟨_, isZero_of_isEmpty P, isOneSided_of_isEmpty P⟩

/-- The one-sided twisted objects are stable under the shifts of the homotopy category. -/
instance : (oneSided R C).IsStableUnderShift ℤ where
  isStableUnderShiftBy n := ⟨fun X hX ↦ by
    rw [ObjectProperty.prop_shift_iff, ← of_underlying R X, shiftFunctor_obj_of, oneSided_of_iff]
    exact ((oneSided_iff X).mp hX).shift n⟩

/-- **The third object of a distinguished triangle whose first two objects are one-sided is
isomorphic to a one-sided twisted object**: the triangle is isomorphic to the cone triangle of a
closed representative of its first morphism, and that cone is one-sided. -/
instance : (oneSided R C).IsTriangulatedClosed₃ where
  ext₃' T hT h₁ h₂ := by
    obtain ⟨X₁, X₂, X₃, f, g, h⟩ := T
    obtain ⟨P, rfl⟩ := of_surjective R X₁
    obtain ⟨Q, rfl⟩ := of_surjective R X₂
    obtain ⟨u, hu, rfl⟩ := exists_homOf_eq R f
    have hu' : dgDifferential R 0 u = 0 := (mem_dgCycles R).mp hu
    obtain ⟨e, -, -⟩ := exists_iso_of_arrow_iso (coneTriangle u hu') _
      (coneTriangle_mem_distinguishedTriangles u hu') hT (Iso.refl _)
    exact ⟨_, ((oneSided_of_iff P).mp h₁).cone ((oneSided_of_iff Q).mp h₂) hu',
      ⟨(Triangle.π₃.mapIso e).symm⟩⟩

/-- **The one-sided twisted objects form a triangulated subcategory** of the homotopy category of
twisted objects: they contain a zero object, are stable under shifts, and are closed under
extensions up to isomorphism.  Its full subcategory, the homotopy category of the pretriangulated
envelope, is therefore triangulated. -/
instance isTriangulated_oneSided : (oneSided R C).IsTriangulated where
  toIsTriangulatedClosed₂ := .of_isTriangulatedClosed₃

end shiftClosure

end DGTwistedObject

end TauCeti
