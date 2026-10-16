/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.RootLattice.TypeE.Basic
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.E8.Lattice

/-!
# The roots and kissing number of the integral E₈ lattice

The norm-two shell of `typeE₈RootLattice` consists of exactly 240 vectors, and its kissing
number is 240. The equivalence `typeE₈RootEquiv` identifies this actual lattice shell with
the indices of the existing Bourbaki root enumeration. It supplies both explicit vectors
and exhaustion, so computations on the roots can use finite indices without replacing the
lattice by a separate coordinate model.

The enumeration `DynkinType.e8Coroot` is expressed in the simple-coroot basis. In the
simply laced type E₈ these are also simple-root coordinates, and the integral Cartan norm
agrees with the rational norm of the lattice. We reuse `DynkinType.exists_e8Coroot_eq` for
completeness rather than recounting the Euclidean roots.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate VII.
* J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, Chapter 4, §8.
-/

public section

namespace TauCeti.IntegralLattice

open _root_.Matrix

/-- The `i`-th root of the integral E₈ lattice, in the existing Bourbaki enumeration. -/
noncomputable def typeE₈RootVector (i : Fin 240) : typeE₈RootLattice :=
  ⟨fun j ↦ (DynkinType.e8Coroot i j : ℚ),
    (mem_typeE₈RootLattice_carrier_iff _).mpr fun j ↦ ⟨DynkinType.e8Coroot i j, rfl⟩⟩

/-- The coordinates of a root vector are those of the existing simple-coroot enumeration. -/
@[simp]
theorem typeE₈RootVector_apply (i : Fin 240) (j : Fin 8) :
    (typeE₈RootVector i : Fin 8 → ℚ) j = (DynkinType.e8Coroot i j : ℚ) :=
  (rfl)

/-- Every enumerated E₈ root has norm two. -/
@[simp]
theorem norm_typeE₈RootVector (i : Fin 240) :
    typeE₈RootLattice.norm (typeE₈RootVector i) = 2 := by
  rw [typeE₈RootVector, norm_typeE₈RootLattice_intCast, ← DynkinType.e8Root_apply,
    DynkinType.e8Root_dotProduct_coroot]
  norm_num

/-- The Bourbaki simple-root indices give the simple roots of the integral lattice. -/
@[simp]
theorem typeE₈RootVector_e8SimpleIndex (i : Fin 8) :
    (typeE₈RootVector (DynkinType.e8SimpleIndex i) : Fin 8 → ℚ) = typeE₈SimpleRoot i := by
  ext j
  simp [DynkinType.coroot_e8SimpleIndex, Pi.single_apply]

/-- Distinct root indices give distinct lattice vectors. -/
theorem typeE₈RootVector_injective : Function.Injective typeE₈RootVector := by
  intro i j h
  apply DynkinType.e8Coroot.injective
  ext k
  have hk := congrArg (fun x : typeE₈RootLattice ↦ (x : Fin 8 → ℚ) k) h
  simpa using hk

/-- A lattice vector has norm two exactly when it is one of the enumerated E₈ roots. -/
theorem norm_typeE₈RootLattice_eq_two_iff (x : typeE₈RootLattice) :
    typeE₈RootLattice.norm x = 2 ↔ ∃ i, typeE₈RootVector i = x := by
  constructor
  · intro hx
    choose v hv using (mem_typeE₈RootLattice_carrier_iff _).mp x.property
    have hcast : (fun j ↦ (v j : ℚ)) = (x : Fin 8 → ℚ) := funext hv
    have hnorm : (v ᵥ* CartanMatrix.E 8) ⬝ᵥ v = 2 := by
      apply Int.cast_injective (α := ℚ)
      simpa [← norm_typeE₈RootLattice_intCast, hcast] using hx
    obtain ⟨i, hi⟩ := DynkinType.exists_e8Coroot_eq hnorm
    refine ⟨i, Subtype.ext ?_⟩
    ext j
    rw [typeE₈RootVector_apply, hi, hv]
  · rintro ⟨i, rfl⟩
    exact norm_typeE₈RootVector i

/-- The 240 root indices enumerate the actual norm-two shell of the integral E₈ lattice. -/
noncomputable def typeE₈RootEquiv : Fin 240 ≃ typeE₈RootLattice.vectorsOfNorm 2 :=
  Equiv.ofBijective
    (fun i ↦ ⟨typeE₈RootVector i, mem_vectorsOfNorm.mpr (norm_typeE₈RootVector i)⟩)
    ⟨fun _ _ h ↦ typeE₈RootVector_injective (congrArg Subtype.val h), fun x ↦ by
      obtain ⟨i, hi⟩ := (norm_typeE₈RootLattice_eq_two_iff x.1).mp
        (mem_vectorsOfNorm.mp x.2)
      exact ⟨i, Subtype.ext hi⟩⟩

/-- The shell equivalence sends each index to its enumerated root vector. -/
@[simp]
theorem typeE₈RootEquiv_apply (i : Fin 240) :
    (typeE₈RootEquiv i : typeE₈RootLattice) = typeE₈RootVector i :=
  (rfl)

/-- The integral E₈ lattice has exactly 240 vectors of norm two. -/
@[simp]
theorem representationNumber_typeE₈RootLattice_two :
    typeE₈RootLattice.representationNumber 2 = 240 := by
  rw [representationNumber_def, ← Nat.card_coe_set_eq,
    ← Nat.card_congr typeE₈RootEquiv]
  simp

/-- The kissing number of the integral E₈ lattice is 240. -/
@[simp]
theorem kissingNumber_typeE₈RootLattice : typeE₈RootLattice.kissingNumber = 240 := by
  rw [kissingNumber_eq_representationNumber (by simp [minimum_typeE₈RootLattice]),
    minimum_typeE₈RootLattice]
  exact representationNumber_typeE₈RootLattice_two

end TauCeti.IntegralLattice
