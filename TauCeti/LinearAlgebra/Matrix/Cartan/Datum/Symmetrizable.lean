/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.Cartan.Datum.Constructions
public import TauCeti.LinearAlgebra.Matrix.Cartan.Datum.Hom
public import TauCeti.LinearAlgebra.Matrix.Cartan.Symmetrizable

/-!
# Symmetrizable matrix data of Cartan data

Every `TauCeti.CartanDatum` carries a generalized Cartan matrix `cartan i j = ⟨αⱼ, hᵢ⟩` and a
positive symmetrizer `dᵢ`, which assemble into a `TauCeti.SymmetrizableDatum` by forgetting the
weight and coweight lattices (`TauCeti.CartanDatum.toSymmetrizableDatum`). Conversely, a
nonsingular `TauCeti.SymmetrizableDatum` on a finite index type determines its simply connected
`TauCeti.CartanDatum` (`TauCeti.SymmetrizableDatum.simplyConnectedCartanDatum`).

Dividing the symmetrizer of a `TauCeti.CartanDatum` on a finite index type by the greatest common
divisor of its entries leaves the lattices, pairing, roots, coroots and reflections unchanged
(`TauCeti.CartanDatum.normalizeSymmetrizer`), matching
`TauCeti.SymmetrizableDatum.normalizeSymmetrizer` on the underlying matrix datum.

## Main definitions

* `TauCeti.CartanDatum.toSymmetrizableDatum`: the underlying `SymmetrizableDatum` of a
  `CartanDatum`.
* `TauCeti.CartanDatum.normalizeSymmetrizer`: the same `CartanDatum` with its symmetrizer divided
  by the greatest common divisor of its entries.
* `TauCeti.SymmetrizableDatum.simplyConnectedCartanDatum`: the simply connected `CartanDatum` of a
  nonsingular `SymmetrizableDatum`.
-/

public section

namespace TauCeti

namespace CartanDatum

variable {ι X Y X' Y' : Type*} [AddCommGroup X] [AddCommGroup Y]
  [AddCommGroup X'] [AddCommGroup Y'] (D : CartanDatum ι X Y)

/-- The underlying `SymmetrizableDatum` of a Cartan datum, retaining its Cartan matrix and
symmetrizer while forgetting the lattices. -/
def toSymmetrizableDatum : SymmetrizableDatum ι where
  cartan := D.cartan
  diag := D.cartan_apply_self
  offDiag_nonpos _ _ hij := D.cartan_nonpos hij
  zero_comm := D.cartan_eq_zero_iff
  symmetrizer := D.symmetrizer
  symmetrizer_pos := D.symmetrizer_pos
  symmetrizes := D.symmetrizer_mul_cartan

@[simp]
lemma toSymmetrizableDatum_cartan : D.toSymmetrizableDatum.cartan = D.cartan := (rfl)

@[simp]
lemma toSymmetrizableDatum_symmetrizer :
    D.toSymmetrizableDatum.symmetrizer = D.symmetrizer := (rfl)

/-- A morphism of Cartan data preserves the underlying `SymmetrizableDatum`. -/
lemma Hom.toSymmetrizableDatum_eq {D : CartanDatum ι X Y} {D' : CartanDatum ι X' Y'}
    (f : Hom D D') : D'.toSymmetrizableDatum = D.toSymmetrizableDatum := by
  ext : 1
  · exact f.cartan_eq
  · exact f.symmetrizer_eq

section Normalize

variable [Fintype ι]

/-- The Cartan datum with the same weight and coweight lattices, pairing, roots and coroots as `D`,
and with the symmetrizer divided by the greatest common divisor of its entries. -/
def normalizeSymmetrizer : CartanDatum ι X Y where
  pairing := D.pairing
  root := D.root
  coroot := D.coroot
  linearIndependent_root := D.linearIndependent_root
  linearIndependent_coroot := D.linearIndependent_coroot
  pairing_root_coroot_self := D.pairing_root_coroot_self
  pairing_root_coroot_nonpos := D.pairing_root_coroot_nonpos
  symmetrizer i := D.symmetrizer i / Finset.univ.gcd D.symmetrizer
  symmetrizer_pos i := by
    simpa using D.toSymmetrizableDatum.normalizeSymmetrizer.symmetrizer_pos i
  symmetrizer_mul_pairing i j := by
    simpa using D.toSymmetrizableDatum.normalizeSymmetrizer.symmetrizes i j

@[simp]
lemma normalizeSymmetrizer_pairing : D.normalizeSymmetrizer.pairing = D.pairing := (rfl)

@[simp]
lemma normalizeSymmetrizer_root : D.normalizeSymmetrizer.root = D.root := (rfl)

@[simp]
lemma normalizeSymmetrizer_coroot : D.normalizeSymmetrizer.coroot = D.coroot := (rfl)

@[simp]
lemma normalizeSymmetrizer_symmetrizer (i : ι) :
    D.normalizeSymmetrizer.symmetrizer i = D.symmetrizer i / Finset.univ.gcd D.symmetrizer :=
  (rfl)

@[simp]
lemma cartan_normalizeSymmetrizer : D.normalizeSymmetrizer.cartan = D.cartan := by
  ext i j
  rw [cartan_apply, cartan_apply]
  rfl

@[simp]
lemma toSymmetrizableDatum_normalizeSymmetrizer :
    D.normalizeSymmetrizer.toSymmetrizableDatum = D.toSymmetrizableDatum.normalizeSymmetrizer := by
  ext <;> simp

@[simp]
lemma reflection_normalizeSymmetrizer (i : ι) :
    D.normalizeSymmetrizer.reflection i = D.reflection i := by
  ext x
  simp [reflection_apply]

@[simp]
lemma coreflection_normalizeSymmetrizer (i : ι) :
    D.normalizeSymmetrizer.coreflection i = D.coreflection i := by
  ext y
  simp [coreflection_apply]

/-- Scaling the normalized simple toral direction by the greatest common divisor of the symmetrizer
recovers the original simple toral direction. -/
lemma gcd_symmetrizer_smul_simpleTorus_normalizeSymmetrizer (i : ι) :
    Finset.univ.gcd D.symmetrizer • D.normalizeSymmetrizer.simpleTorus i = D.simpleTorus i := by
  have hd := D.toSymmetrizableDatum.symmetrizer_eq_gcd_mul_normalizeSymmetrizer i
  simp only [toSymmetrizableDatum_symmetrizer,
    SymmetrizableDatum.normalizeSymmetrizer_symmetrizer] at hd
  rw [simpleTorus_def, simpleTorus_def, normalizeSymmetrizer_coroot, smul_smul,
    normalizeSymmetrizer_symmetrizer, ← hd]

end Normalize

end CartanDatum

namespace SymmetrizableDatum

open Module

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (A : SymmetrizableDatum ι)

/-- The simply connected Cartan datum associated to a nonsingular `SymmetrizableDatum`, on the
coweight lattice `ℤ^ι` and its dual weight lattice `Hom(ℤ^ι, ℤ)`. -/
def simplyConnectedCartanDatum (hdet : A.cartan.det ≠ 0) :
    CartanDatum ι (Dual ℤ (ι → ℤ)) (ι → ℤ) :=
  CartanDatum.simplyConnected A.cartan A.symmetrizer A.diag A.offDiag_nonpos
    A.symmetrizer_pos A.symmetrizes hdet

@[simp]
lemma simplyConnectedCartanDatum_pairing_apply (hdet : A.cartan.det ≠ 0)
    (x : Dual ℤ (ι → ℤ)) (y : ι → ℤ) :
    (A.simplyConnectedCartanDatum hdet).pairing x y = x y := by
  simp [simplyConnectedCartanDatum]

@[simp]
lemma simplyConnectedCartanDatum_coroot (hdet : A.cartan.det ≠ 0) (i : ι) :
    (A.simplyConnectedCartanDatum hdet).coroot i = Pi.single i 1 := by
  simp [simplyConnectedCartanDatum]

@[simp]
lemma simplyConnectedCartanDatum_symmetrizer (hdet : A.cartan.det ≠ 0) :
    (A.simplyConnectedCartanDatum hdet).symmetrizer = A.symmetrizer := by
  simp [simplyConnectedCartanDatum]

@[simp]
lemma cartan_simplyConnectedCartanDatum (hdet : A.cartan.det ≠ 0) :
    (A.simplyConnectedCartanDatum hdet).cartan = A.cartan :=
  CartanDatum.cartan_simplyConnected A.cartan A.symmetrizer A.diag A.offDiag_nonpos
    A.symmetrizer_pos A.symmetrizes hdet

@[simp]
lemma toSymmetrizableDatum_simplyConnectedCartanDatum (hdet : A.cartan.det ≠ 0) :
    (A.simplyConnectedCartanDatum hdet).toSymmetrizableDatum = A := by
  ext <;> simp

end SymmetrizableDatum

end TauCeti
