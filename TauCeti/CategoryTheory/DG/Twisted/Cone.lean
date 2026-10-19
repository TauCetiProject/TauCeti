/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.DG.ShiftClosure.Basic
public import TauCeti.CategoryTheory.DG.Twisted.Extension

/-!
# The cone of a closed morphism as a twisted object

For a closed degree-zero morphism `f : X ⟶ Y` of a differential graded category `C`, the cone
`TauCeti.DGTwistedObject.cone f` is the twisted object `(Y[0] ⊕ X[1], δ)` of the additive closure
of the shift closure of `C` whose twisting matrix has a single nonzero entry, `f` itself, in the
block from `X[1]` to `Y[0]`.  Since `Hom(X[1], Y[0]) = Hom(X, Y)[-1]` in the shift closure, a
degree-zero morphism `X ⟶ Y` is a degree-one morphism `X[1] ⟶ Y[0]`
(`TauCeti.DGTwistedObject.coneMorphism`), and it is closed when `f` is.  The cone is the extension
of `X[1]` by `Y[0]` along this morphism (see `TauCeti/CategoryTheory/DG/Twisted/Extension.lean`),
which supplies its Maurer–Cartan equation, the closed degree-zero morphisms
`Y[0] ⟶ cone f ⟶ X[1]` with zero composite, and their graded splitting.

## Main definitions

* `TauCeti.DGTwistedObject.shiftedObj`: the one-term twisted object `X[r]` with zero twist.
* `TauCeti.DGTwistedObject.coneMorphism`: a degree-zero morphism `X ⟶ Y` as a degree-one
  morphism `X[1] ⟶ Y[0]`.
* `TauCeti.DGTwistedObject.cone`: the cone of a closed degree-zero morphism.

## Main results

* `TauCeti.DGTwistedObject.dgDifferential_coneMorphism`: the degree-one morphism underlying a
  closed morphism is closed.
* `TauCeti.DGTwistedObject.dgHomEquiv_twist_cone_inr_inl`: the block of the twisting matrix of
  the cone from `X[1]` to `Y[0]` is `f`; the other three blocks vanish.

## References

* A. I. Bondal and M. M. Kapranov, *Enhanced triangulated categories*, Section 1.
* V. Drinfeld, *DG quotients of DG categories*, Section 2.4.
-/

public section

open CategoryTheory

namespace TauCeti

universe v u

namespace DGTwistedObject

variable (R : Type v) [CommRing R] {C : Type u} [DGCategory R C]

/- `matrixEquiv` is a local name for `TauCeti.DGAdditiveClosure.dgHomEquiv`, which identifies a
morphism of the additive closure with its matrix of entries; the unqualified name `dgHomEquiv`
refers to `TauCeti.DGTwistedObject.dgHomEquiv` in this namespace. -/
open DGAdditiveClosure renaming dgHomEquiv → matrixEquiv

/-- The one-term twisted object `X[r]` of the additive closure of the shift closure of `C`, with
zero twist. -/
noncomputable abbrev shiftedObj (X : C) (r : ℤ) :
    DGTwistedObject R (DGAdditiveClosure (DGShiftClosure C)) :=
  ofObj R ⟨PUnit, fun _ ↦ ⟨X, r⟩⟩

/-- A degree-zero morphism `f : X ⟶ Y` of `C`, as a degree-one morphism `X[1] ⟶ Y[0]` of
one-term twisted objects. -/
noncomputable def coneMorphism {X Y : C} (f : DGHom R 0 X Y) :
    DGHom R 1 (shiftedObj R X 1) (shiftedObj R Y 0) :=
  embeddingHomEquiv R _ _ 1 (DGAdditiveClosure.embeddingHomEquiv R _ _ 1
    ((DGShiftClosure.dgHomEquiv R ⟨X, 1⟩ ⟨Y, 0⟩ 1).symm (castDeg R (by dsimp only; omega) f)))

/-- The underlying morphism of `X` to `Y` of `TauCeti.DGTwistedObject.coneMorphism` is the
original morphism. -/
@[simp]
theorem dgHomEquiv_coneMorphism {X Y : C} (f : DGHom R 0 X Y) (u u' : PUnit) :
    DGShiftClosure.dgHomEquiv R ⟨X, 1⟩ ⟨Y, 0⟩ 1
        (matrixEquiv R _ _ 1 (dgHomEquiv R _ _ 1 (coneMorphism R f)) u u') =
      castDeg R (by dsimp only; omega) f := by
  rw [coneMorphism, dgHomEquiv_embeddingHomEquiv, DGAdditiveClosure.dgHomEquiv_embeddingHomEquiv,
    LinearEquiv.apply_symm_apply]

variable {R} in
/-- The degree-one morphism `X[1] ⟶ Y[0]` underlying a closed morphism `f : X ⟶ Y` is closed. -/
theorem dgDifferential_coneMorphism {X Y : C} {f : DGHom R 0 X Y}
    (hf : dgDifferential R 0 f = 0) : dgDifferential R 1 (coneMorphism R f) = 0 := by
  rw [coneMorphism, ← embeddingHomEquiv_dgDifferential,
    ← DGAdditiveClosure.embeddingHomEquiv_dgDifferential]
  suffices h : dgDifferential R 1 ((DGShiftClosure.dgHomEquiv R ⟨X, 1⟩ ⟨Y, 0⟩ 1).symm
      (castDeg R (by dsimp only; omega) f)) = 0 by
    rw [h, map_zero, map_zero]
  apply (DGShiftClosure.dgHomEquiv R ⟨X, 1⟩ ⟨Y, 0⟩ (1 + 1)).injective
  rw [DGShiftClosure.dgHomEquiv_dgDifferential, LinearEquiv.apply_symm_apply, map_zero,
    d_castDeg R (a := 0) (a' := 0 + 1) (by dsimp only; omega) (by dsimp only; omega), hf,
    map_zero, smul_zero]

variable {R} in
/-- The **cone** of a closed degree-zero morphism `f : X ⟶ Y` of `C`: the twisted object
`(Y[0] ⊕ X[1], δ)` of the additive closure of the shift closure of `C` whose twisting matrix has
`f` as its only nonzero entry, from `X[1]` to `Y[0]`. -/
noncomputable abbrev cone {X Y : C} (f : DGHom R 0 X Y) (hf : dgDifferential R 0 f = 0) :
    DGTwistedObject R (DGAdditiveClosure (DGShiftClosure C)) :=
  extension (shiftedObj R Y 0) (shiftedObj R X 1) (coneMorphism R f)
    (dgDifferential_coneMorphism hf)

section cone

variable {X Y : C} (f : DGHom R 0 X Y) (hf : dgDifferential R 0 f = 0)

/-- The block of the twisting matrix of the cone from `X[1]` to `Y[0]` is `f`. -/
theorem dgHomEquiv_twist_cone_inr_inl (u u' : PUnit) :
    DGShiftClosure.dgHomEquiv R ⟨X, 1⟩ ⟨Y, 0⟩ 1
        (matrixEquiv R _ _ 1 (cone f hf).twist (.inr u) (.inl u')) =
      castDeg R (by dsimp only; omega) f := by
  rw [dgHomEquiv_extensionTwist_inr_inl]
  exact dgHomEquiv_coneMorphism R f u u'

/-- The block of the twisting matrix of the cone on `Y[0]` vanishes. -/
@[simp↓]
theorem dgHomEquiv_twist_cone_inl_inl (u u' : PUnit) :
    matrixEquiv R _ _ 1 (cone f hf).twist (.inl u) (.inl u') = 0 := by
  rw [dgHomEquiv_extensionTwist_inl_inl, map_zero, Pi.zero_apply, Pi.zero_apply]

/-- The block of the twisting matrix of the cone from `Y[0]` to `X[1]` vanishes. -/
@[simp↓]
theorem dgHomEquiv_twist_cone_inl_inr (u u' : PUnit) :
    matrixEquiv R _ _ 1 (cone f hf).twist (.inl u) (.inr u') = 0 := by
  rw [dgHomEquiv_extensionTwist_inl_inr]

/-- The block of the twisting matrix of the cone on `X[1]` vanishes. -/
@[simp↓]
theorem dgHomEquiv_twist_cone_inr_inr (u u' : PUnit) :
    matrixEquiv R _ _ 1 (cone f hf).twist (.inr u) (.inr u') = 0 := by
  rw [dgHomEquiv_extensionTwist_inr_inr, map_zero, Pi.zero_apply, Pi.zero_apply]

end cone

end DGTwistedObject

end TauCeti
