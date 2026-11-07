/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Datum
public import TauCeti.LinearAlgebra.Basis.DiagonalTorus.CharacterMap

/-!
# Restriction between the tori of Chevalley data

For Chevalley data `D` and `E` with `Λ(E) ≤ Λ(D)`, restriction of characters gives a map
`Hom(Λ(D), Aˣ) → Hom(Λ(E), Aˣ)`. Here `torusRestriction` writes this map in the two chosen
weight-lattice bases. Its character equation and its compatibility with integral cocharacters
are the torus input for comparing the groups constructed from different admissible lattices.
In particular, a simple-coroot functional has the same value after restriction.

Restriction composes, commutes with scalar extension, and is an equivalence when the lattices
are equal. It is surjective when the units of the value ring are divisible, but no surjectivity
is asserted over an arbitrary field. The tori here have their actual character lattices, not
necessarily the full weight lattice. No comparison of the ambient point groups is assumed.

The construction uses `TauCeti.torusPointMap` and its contravariant composition law.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 3, Lemma 28(c) and Corollary 5 to
  Theorem 4′.
* J. C. Jantzen, *Representations of Algebraic Groups*, II.1.
-/

public section

namespace TauCeti.DynkinType.ChevalleyDatum

variable {t : DynkinType} {ht : t.Valid}
  (D E F : ChevalleyDatum t ht)

/-- Inclusion of weight lattices, in the chosen bases of the two Chevalley data. Its direction
is opposite to the induced map on torus points. -/
noncomputable def weightLatticeInclusion (h : E.weightLattice ≤ D.weightLattice) :
    (Fin t.rank → ℤ) →ₗ[ℤ] (Fin t.rank → ℤ) :=
  D.weightLatticeBasis.equivFun.toLinearMap ∘ₗ Submodule.inclusion h ∘ₗ
    E.weightLatticeBasis.equivFun.symm.toLinearMap

/-- Inclusion carries the coordinates of a character to its coordinates in the larger lattice. -/
@[simp]
theorem weightLatticeInclusion_repr (h : E.weightLattice ≤ D.weightLattice)
    (χ : E.weightLattice) :
    D.weightLatticeInclusion E h (E.weightLatticeBasis.repr χ) =
      D.weightLatticeBasis.repr (Submodule.inclusion h χ) := by
  simp [weightLatticeInclusion]

/-- A coordinate character of the smaller torus is the corresponding lattice basis vector,
read in the larger lattice. -/
@[simp]
theorem weightLatticeInclusion_single (h : E.weightLattice ≤ D.weightLattice)
    (i : Fin t.rank) :
    D.weightLatticeInclusion E h (Pi.single i 1) =
      D.weightLatticeBasis.repr (Submodule.inclusion h (E.weightLatticeBasis i)) := by
  simpa only [Module.Basis.repr_self, Finsupp.single_eq_pi_single]
    using D.weightLatticeInclusion_repr E h (E.weightLatticeBasis i)

/-- The lattice map underlying torus restriction is injective. -/
theorem weightLatticeInclusion_injective (h : E.weightLattice ≤ D.weightLattice) :
    Function.Injective (D.weightLatticeInclusion E h) :=
  D.weightLatticeBasis.equivFun.injective.comp
    ((Submodule.inclusion_injective h).comp E.weightLatticeBasis.equivFun.symm.injective)

/-- Restricting a lattice to itself gives the identity in coordinates. -/
@[simp]
theorem weightLatticeInclusion_refl :
    D.weightLatticeInclusion D le_rfl = LinearMap.id := by
  ext χ i
  simp [weightLatticeInclusion, Submodule.inclusion_apply, Pi.single_apply, eq_comm]

/-- Coordinate inclusions compose along a chain of weight lattices. -/
theorem weightLatticeInclusion_trans (h : E.weightLattice ≤ D.weightLattice)
    (k : F.weightLattice ≤ E.weightLattice) :
    D.weightLatticeInclusion F (k.trans h) =
      (D.weightLatticeInclusion E h) ∘ₗ (E.weightLatticeInclusion F k) := by
  ext χ i
  simp [weightLatticeInclusion, Submodule.inclusion_apply]

variable {A B : Type*} [CommRing A] [CommRing B]

/-- Restriction from the actual torus of `D` to that of `E`, on parameters in their respective
weight-lattice bases. -/
noncomputable def torusRestriction (h : E.weightLattice ≤ D.weightLattice) :
    (Fin t.rank → Aˣ) →* (Fin t.rank → Aˣ) :=
  torusPointMap (D.weightLatticeInclusion E h)

/-- Torus restriction is the point map dual to inclusion of the actual character lattices. -/
theorem torusRestriction_def (h : E.weightLattice ≤ D.weightLattice) :
    D.torusRestriction E (A := A) h = torusPointMap (D.weightLatticeInclusion E h) :=
  (rfl)

/-- Evaluate a character of the smaller lattice after restricting a torus point. -/
@[simp]
theorem torusCharacter_torusRestriction (h : E.weightLattice ≤ D.weightLattice)
    (s : Fin t.rank → Aˣ) (χ : E.weightLattice) :
    torusCharacter (D.torusRestriction E h s) (E.weightLatticeBasis.repr χ) =
      torusCharacter s (D.weightLatticeBasis.repr (Submodule.inclusion h χ)) := by
  rw [torusRestriction_def, torusCharacter_torusPointMap, weightLatticeInclusion_repr]

/-- Restriction to the same weight lattice with the same basis is the identity. -/
@[simp]
theorem torusRestriction_refl :
    D.torusRestriction D (A := A) le_rfl = MonoidHom.id _ := by
  simp [torusRestriction]

/-- Restriction is contravariant in inclusions of weight lattices. -/
theorem torusRestriction_trans (h : E.weightLattice ≤ D.weightLattice)
    (k : F.weightLattice ≤ E.weightLattice) :
    D.torusRestriction F (A := A) (k.trans h) =
      (E.torusRestriction F k).comp (D.torusRestriction E h) := by
  rw [torusRestriction_def, weightLatticeInclusion_trans, torusPointMap_comp]
  rfl

/-- Restriction commutes with changing the value ring. -/
@[simp]
theorem map_torusRestriction (h : E.weightLattice ≤ D.weightLattice) (f : A →+* B)
    (s : Fin t.rank → Aˣ) :
    D.torusRestriction E h (fun i => Units.map (f : A →* B) (s i)) =
      fun i => Units.map (f : A →* B) (D.torusRestriction E h s i) := by
  ext i
  simp [torusRestriction, torusPointMap_apply, map_torusCharacter]

/-- Restriction preserves the value of every integral cocharacter defined on the ambient weight
lattice. In particular this applies to the simple-coroot coordinate functionals. -/
@[simp]
theorem torusRestriction_cocharacter (h : E.weightLattice ≤ D.weightLattice)
    (ψ : (Fin t.rank → ℤ) →ₗ[ℤ] ℤ) (a : Aˣ) :
    D.torusRestriction E h (fun j => a ^ ψ (D.weightLatticeBasis j)) =
      fun i => a ^ ψ (E.weightLatticeBasis i) := by
  funext i
  rw [torusRestriction_def, torusPointMap_apply, torusCharacter_def]
  simp_rw [← zpow_mul]
  rw [Finset.prod_zpow_eq_zpow_sum, weightLatticeInclusion_single]
  congr 1
  have hi := congrArg (fun x : D.weightLattice => ψ x)
    (D.weightLatticeBasis.sum_repr (Submodule.inclusion h (E.weightLatticeBasis i)))
  simp only [Submodule.coe_sum, Submodule.coe_smul, map_sum, map_smul,
    smul_eq_mul, Submodule.coe_inclusion] at hi
  simpa only [mul_comm] using hi

/-- If the value ring has divisible units, every torus point of the smaller lattice extends
to the larger lattice. No such assertion holds for general fields. -/
theorem torusRestriction_surjective [RootableBy Aˣ ℕ]
    (h : E.weightLattice ≤ D.weightLattice) :
    Function.Surjective (D.torusRestriction E (A := A) h) :=
  torusPointMap_surjective_of_injective (D.weightLatticeInclusion_injective E h)

/-- Equal weight lattices give equivalent tori, even when their chosen bases differ. -/
noncomputable def torusEquivOfWeightLatticeEq (h : D.weightLattice = E.weightLattice) :
    (Fin t.rank → Aˣ) ≃* (Fin t.rank → Aˣ) where
  toFun := D.torusRestriction E h.ge
  invFun := E.torusRestriction D h.le
  left_inv s := by
    have e := D.torusRestriction_trans E D (A := A) h.ge h.le
    simpa using (DFunLike.congr_fun e s).symm
  right_inv s := by
    have e := E.torusRestriction_trans D E (A := A) h.le h.ge
    simpa using (DFunLike.congr_fun e s).symm
  map_mul' := (D.torusRestriction E h.ge).map_mul

/-- The equal-lattice equivalence is restriction in the forward direction. -/
@[simp]
theorem torusEquivOfWeightLatticeEq_apply (h : D.weightLattice = E.weightLattice)
    (s : Fin t.rank → Aˣ) :
    D.torusEquivOfWeightLatticeEq E h s = D.torusRestriction E h.ge s :=
  (rfl)

/-- The inverse equivalence restricts in the reverse direction. -/
theorem torusEquivOfWeightLatticeEq_symm_apply (h : D.weightLattice = E.weightLattice)
    (s : Fin t.rank → Aˣ) :
    (D.torusEquivOfWeightLatticeEq E h).symm s = E.torusRestriction D h.le s :=
  (rfl)

end TauCeti.DynkinType.ChevalleyDatum
