/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.Isometry.Basic

/-!
# Isometry classes of integral lattices

The isometry classes of integral lattices in a rational vector space `V` form the quotient
`IsometryQuotient V` of `IntegralLattice V` by isometry. Transport along a rational linear
equivalence `V ≃ W` identifies the isometry classes in `V` with those in `W`.

## Main definitions

* `TauCeti.IntegralLattice.isometrySetoid`: isometry of integral lattices in `V`.
* `TauCeti.IntegralLattice.IsometryQuotient`: the isometry classes of integral lattices in `V`.
* `TauCeti.IntegralLattice.isometryClass`: the class `cls L` of a lattice.
* `TauCeti.IntegralLattice.isometryQuotientEquiv`: transport of classes along an ambient linear
  equivalence.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms*, §102A, for classes of lattices.
-/

public section

namespace TauCeti.IntegralLattice

universe u v

variable {V : Type u} {W : Type v} [AddCommGroup V] [Module ℚ V] [AddCommGroup W] [Module ℚ W]

section IsometryQuotient

variable (V) in
/-- Isometry of integral lattices in a fixed rational space, as an equivalence relation. -/
def isometrySetoid : Setoid (IntegralLattice V) where
  r L M := Nonempty (Isometry L M)
  iseqv := ⟨fun L ↦ ⟨Isometry.refl L⟩, fun ⟨e⟩ ↦ ⟨e.symm⟩, fun ⟨e⟩ ⟨f⟩ ↦ ⟨e.trans f⟩⟩

/-- Two lattices are related by `isometrySetoid` exactly when they are isometric. -/
theorem isometrySetoid_apply {L M : IntegralLattice V} :
    isometrySetoid V L M ↔ Nonempty (Isometry L M) :=
  Iff.rfl

variable (V) in
/-- The isometry classes of integral lattices in a rational space `V`. -/
abbrev IsometryQuotient : Type u := Quotient (isometrySetoid V)

/-- The isometry class `cls L` of an integral lattice. -/
def isometryClass (L : IntegralLattice V) : IsometryQuotient V :=
  Quotient.mk _ L

/-- Two lattices have the same isometry class exactly when they are isometric. -/
@[simp]
theorem isometryClass_eq_isometryClass_iff {L M : IntegralLattice V} :
    L.isometryClass = M.isometryClass ↔ Nonempty (Isometry L M) :=
  Quotient.eq

/-- Isometric lattices have the same isometry class. -/
theorem Isometry.isometryClass_eq {L M : IntegralLattice V} (e : Isometry L M) :
    L.isometryClass = M.isometryClass :=
  isometryClass_eq_isometryClass_iff.mpr ⟨e⟩

/-- Every isometry class is the class of a lattice. -/
theorem isometryClass_surjective :
    Function.Surjective (isometryClass : IntegralLattice V → IsometryQuotient V) :=
  Quotient.mk_surjective

/-- A chosen representative of an isometry class has that class. -/
@[simp]
theorem isometryClass_out (c : IsometryQuotient V) : c.out.isometryClass = c :=
  Quotient.out_eq c

/-- An isometry between the chosen representatives of two isometry classes shows that the classes
are equal. -/
theorem IsometryQuotient.eq_of_isometry_out {c d : IsometryQuotient V} (e : Isometry c.out d.out) :
    c = d := by
  rw [← isometryClass_out c, ← isometryClass_out d]
  exact e.isometryClass_eq

/-- Transport along a rational linear equivalence `V ≃ W` identifies the isometry classes of
integral lattices in `V` with those in `W`. -/
noncomputable def isometryQuotientEquiv (f : V ≃ₗ[ℚ] W) :
    IsometryQuotient V ≃ IsometryQuotient W where
  toFun := Quotient.map (·.transport f) fun M N ⟨e⟩ ↦
    ⟨((M.transportIsometry f).symm.trans e).trans (N.transportIsometry f)⟩
  invFun := Quotient.map (·.transport f.symm) fun M N ⟨e⟩ ↦
    ⟨((M.transportIsometry f.symm).symm.trans e).trans (N.transportIsometry f.symm)⟩
  left_inv c := by
    obtain ⟨M, rfl⟩ := isometryClass_surjective c
    exact (((M.transportIsometry f).trans
      ((M.transport f).transportIsometry f.symm)).isometryClass_eq).symm
  right_inv c := by
    obtain ⟨M, rfl⟩ := isometryClass_surjective c
    exact (((M.transportIsometry f.symm).trans
      ((M.transport f.symm).transportIsometry f)).isometryClass_eq).symm

/-- `isometryQuotientEquiv f` sends the class of `M` to the class of its transport along `f`. -/
@[simp]
theorem isometryQuotientEquiv_isometryClass (f : V ≃ₗ[ℚ] W) (M : IntegralLattice V) :
    isometryQuotientEquiv f M.isometryClass = (M.transport f).isometryClass :=
  (rfl)

/-- The inverse of `isometryQuotientEquiv f` sends the class of `M` to the class of its transport
along `f.symm`. -/
@[simp]
theorem isometryQuotientEquiv_symm_isometryClass (f : V ≃ₗ[ℚ] W) (M : IntegralLattice W) :
    (isometryQuotientEquiv f).symm M.isometryClass = (M.transport f.symm).isometryClass :=
  (rfl)

/-- The transport along `f` of the representative of a class is isometric to the representative
of the transported class. -/
theorem IsometryQuotient.nonempty_isometry_transport_out (c : IsometryQuotient V)
    (f : V ≃ₗ[ℚ] W) : Nonempty (Isometry (c.out.transport f) (isometryQuotientEquiv f c).out) := by
  rw [← isometryClass_eq_isometryClass_iff, isometryClass_out,
    ← isometryQuotientEquiv_isometryClass, isometryClass_out]

end IsometryQuotient

end TauCeti.IntegralLattice
