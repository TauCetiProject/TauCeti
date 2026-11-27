/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import TauCeti.GroupTheory.SpecificGroups.Dihedral.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination

/-!
# The two lattices of the order-three type at `2`

Let `ℚ₄` be the unramified quadratic extension of `ℚ₂` and `χ'` a character of `G_{ℚ₄}` of
order three and niveau two, normalised by `χ'(Art(2)) = 1`, with values in `𝒪 = ℤ₃[ζ]`,
`ζ² + ζ + 1 = 0`. The induced representation `Ind χ'` of `G_{ℚ₂}` is the *order-three
type at `2`* of Dieulefait and Pacetti (Lemma 2.3). It factors through the Galois group of a
dihedral extension of order six, in which a tame inertia generator `σ` maps to an element of
order three and the Frobenius lift `Frob₂` to an involution with `Frob₂ σ Frob₂⁻¹ = σ²`. So it
is a representation of `DihedralGroup 3`, with `σ ↦ r 1` and `Frob₂ ↦ sr 0`.

Its two stable lattices used by Dieulefait and Pacetti are written down here over an arbitrary
commutative ring `R` containing an element `ζ` with `ζ² + ζ + 1 = 0`:

* the *standard lattice* `L₀`, on which `σ ↦ diag(ζ, ζ²)` and `Frob₂ ↦ (0, 1; 1, 0)`
  (`TauCeti.OrderThreeType.standardRep`);
* the *adapted lattice* `L₁ = 𝒪(e₁ + e₂) ⊕ 𝒪πe₂`, `π = ζ - 1`, on which
  `σ ↦ (ζ, 0; ζ, ζ²)` and `Frob₂ ↦ (1, π; 0, -1)` (`TauCeti.OrderThreeType.adaptedRep`).

The matrix `P = (1, 0; 1, π)` of the inclusion `L₁ ⊆ L₀` intertwines them, and when `π` is
invertible (over the fraction field) it conjugates one into the other, so `L₁` is a second
lattice in the same representation. Both constructions commute with every ring homomorphism.

Under a ring homomorphism sending `ζ` to `1`, which forces `3 = 0`, the two reductions differ:
inertia acts trivially on `L₀/πL₀`, while on `L₁/πL₁` it acts by the nontrivial unipotent
`(1, 0; 1, 1)` and `Frob₂` acts by `diag(1, -1)`; over a field the inertia invariants have
dimension two and one. Conversely, over a field of characteristic three, let `S` be a unipotent
matrix and `F` an invertible matrix with `F S F⁻¹ = S²`, the images of `σ` and `Frob₂` under a
residual representation of the tame quotient at `2`. If `S = 1` and `F` has eigenvalues `±γ`,
then `F` is conjugate to `γ` times the reduced Frobenius of `L₀`. If `S ≠ 1`, then `(S, F)` is
simultaneously conjugate to the reduction of `L₁` with `Frob₂` multiplied by a unit scalar. This
is the choice of lattice in the proof of Lemma 2.3.

## Main definitions

* `TauCeti.OrderThreeType.standardRep`: the action on the standard lattice `L₀`.
* `TauCeti.OrderThreeType.adaptedRep`: the action on the adapted lattice `L₁`.
* `TauCeti.OrderThreeType.latticeInclusion`: the matrix `(1, 0; 1, ζ - 1)` of `L₁ ⊆ L₀`.

## Main statements

* `TauCeti.OrderThreeType.standardRep_mul_latticeInclusion`: the inclusion is equivariant.
* `TauCeti.OrderThreeType.adaptedRep_eq_inv_mul_mul`: when `ζ - 1` is a unit the two
  representations are conjugate.
* `TauCeti.OrderThreeType.map_comp_standardRep`, `TauCeti.OrderThreeType.map_comp_adaptedRep`:
  compatibility with change of coefficients, in particular with reduction modulo `π`.
* `TauCeti.OrderThreeType.trace_standardRep_sr`, `TauCeti.OrderThreeType.trace_adaptedRep_sr`:
  every Frobenius lift has trace zero on both lattices.
* `TauCeti.OrderThreeType.finrank_ker_standardRep_r_one_sub_one`,
  `TauCeti.OrderThreeType.finrank_ker_adaptedRep_r_one_sub_one`: the reduced inertia invariants
  have dimension two on `L₀` and one on `L₁`.
* `TauCeti.OrderThreeType.exists_conj_standardRep`,
  `TauCeti.OrderThreeType.exists_conj_adaptedRep`: the selection of the lattice whose reduction
  realises a given residual representation.

## References

* L. V. Dieulefait and A. M. Pacetti, *A simplified proof of Serre's conjectures*,
  arXiv:2108.07577v2, Lemma 2.3 and its proof.
-/

public section

open Matrix DihedralGroup

namespace TauCeti.OrderThreeType

section Lattices

variable {R : Type*} [CommRing R] {ζ : R}

/-- The inertia matrix `diag(ζ, ζ²)` of the standard lattice, with inverse `diag(ζ², ζ)`. -/
private def stdInertia (hζ : ζ ^ 2 + ζ + 1 = 0) : GL (Fin 2) R where
  val := !![ζ, 0; 0, ζ ^ 2]
  inv := !![ζ ^ 2, 0; 0, ζ]
  val_inv := by
    ext i j; fin_cases i <;> fin_cases j <;> simp <;> grind
  inv_val := by
    ext i j; fin_cases i <;> fin_cases j <;> simp <;> grind

/-- The Frobenius matrix `(0, 1; 1, 0)` of the standard lattice, an involution. -/
private def stdFrob : GL (Fin 2) R where
  val := !![0, 1; 1, 0]
  inv := !![0, 1; 1, 0]
  val_inv := by ext i j; fin_cases i <;> fin_cases j <;> simp
  inv_val := by ext i j; fin_cases i <;> fin_cases j <;> simp

/-- The inertia matrix `(ζ, 0; ζ, ζ²)` of the adapted lattice, with inverse `(ζ², 0; -ζ, ζ)`. -/
private def adaptedInertia (hζ : ζ ^ 2 + ζ + 1 = 0) : GL (Fin 2) R where
  val := !![ζ, 0; ζ, ζ ^ 2]
  inv := !![ζ ^ 2, 0; -ζ, ζ]
  val_inv := by
    ext i j; fin_cases i <;> fin_cases j <;> simp <;> grind
  inv_val := by
    ext i j; fin_cases i <;> fin_cases j <;> simp <;> grind

/-- The Frobenius matrix `(1, ζ - 1; 0, -1)` of the adapted lattice, an involution. -/
private def adaptedFrob (ζ : R) : GL (Fin 2) R where
  val := !![1, ζ - 1; 0, -1]
  inv := !![1, ζ - 1; 0, -1]
  val_inv := by ext i j; fin_cases i <;> fin_cases j <;> simp
  inv_val := by ext i j; fin_cases i <;> fin_cases j <;> simp

private lemma stdFrob_mul_self : (stdFrob : GL (Fin 2) R) * stdFrob = 1 :=
  Units.ext <| by ext i j; fin_cases i <;> fin_cases j <;> simp [stdFrob]

private lemma stdInertia_pow_three (hζ : ζ ^ 2 + ζ + 1 = 0) : stdInertia hζ ^ 3 = 1 :=
  Units.ext <| by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [stdInertia, pow_succ] <;>
      grind

private lemma stdFrob_mul_stdInertia_mul_stdFrob (hζ : ζ ^ 2 + ζ + 1 = 0) :
    stdFrob * stdInertia hζ * stdFrob = stdInertia hζ ^ 2 :=
  Units.ext <| by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [stdFrob, stdInertia, pow_succ]
    grind

private lemma adaptedFrob_mul_self : adaptedFrob ζ * adaptedFrob ζ = 1 :=
  Units.ext <| by ext i j; fin_cases i <;> fin_cases j <;> simp [adaptedFrob]

private lemma adaptedInertia_pow_three (hζ : ζ ^ 2 + ζ + 1 = 0) : adaptedInertia hζ ^ 3 = 1 :=
  Units.ext <| by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [adaptedInertia, pow_succ] <;>
      grind

private lemma adaptedFrob_mul_adaptedInertia_mul_adaptedFrob (hζ : ζ ^ 2 + ζ + 1 = 0) :
    adaptedFrob ζ * adaptedInertia hζ * adaptedFrob ζ = adaptedInertia hζ ^ 2 :=
  Units.ext <| by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [adaptedFrob, adaptedInertia, pow_succ] <;>
      grind

/-- The **standard lattice** `L₀ = 𝒪e₁ ⊕ 𝒪e₂` of the order-three type at `2`, as a
representation of `DihedralGroup 3`: the rotation `r 1` (a tame inertia generator) acts by
`diag(ζ, ζ²)` and the reflection `sr 0` (a Frobenius lift) by `(0, 1; 1, 0)`. -/
def standardRep (hζ : ζ ^ 2 + ζ + 1 = 0) : DihedralGroup 3 →* GL (Fin 2) R :=
  dihedralHom (s := stdFrob) (t := stdFrob * stdInertia hζ) stdFrob_mul_self
    (by rw [← mul_assoc, stdFrob_mul_stdInertia_mul_stdFrob, ← pow_succ, stdInertia_pow_three])
    (by rw [← mul_assoc, stdFrob_mul_self, one_mul, stdInertia_pow_three])

/-- The **adapted lattice** `L₁ = 𝒪(e₁ + e₂) ⊕ 𝒪πe₂`, `π = ζ - 1`, of the order-three type at
`2`, as a representation of `DihedralGroup 3` in the basis `e₁ + e₂, πe₂`: the rotation `r 1`
acts by `(ζ, 0; ζ, ζ²)` and the reflection `sr 0` by `(1, π; 0, -1)`. -/
def adaptedRep (hζ : ζ ^ 2 + ζ + 1 = 0) : DihedralGroup 3 →* GL (Fin 2) R :=
  dihedralHom (s := adaptedFrob ζ) (t := adaptedFrob ζ * adaptedInertia hζ) adaptedFrob_mul_self
    (by
      rw [← mul_assoc, adaptedFrob_mul_adaptedInertia_mul_adaptedFrob, ← pow_succ,
        adaptedInertia_pow_three])
    (by rw [← mul_assoc, adaptedFrob_mul_self, one_mul, adaptedInertia_pow_three])

private lemma standardRep_r (hζ : ζ ^ 2 + ζ + 1 = 0) (i : ZMod 3) :
    standardRep hζ (r i) = stdInertia hζ ^ (ZMod.cast i : ℤ) := by
  rw [standardRep, dihedralHom_r, ← mul_assoc, stdFrob_mul_self, one_mul]

private lemma standardRep_sr (hζ : ζ ^ 2 + ζ + 1 = 0) (i : ZMod 3) :
    standardRep hζ (sr i) = stdFrob * stdInertia hζ ^ (ZMod.cast i : ℤ) := by
  rw [standardRep, dihedralHom_sr, ← mul_assoc, stdFrob_mul_self, one_mul]

private lemma adaptedRep_r (hζ : ζ ^ 2 + ζ + 1 = 0) (i : ZMod 3) :
    adaptedRep hζ (r i) = adaptedInertia hζ ^ (ZMod.cast i : ℤ) := by
  rw [adaptedRep, dihedralHom_r, ← mul_assoc, adaptedFrob_mul_self, one_mul]

private lemma adaptedRep_sr (hζ : ζ ^ 2 + ζ + 1 = 0) (i : ZMod 3) :
    adaptedRep hζ (sr i) = adaptedFrob ζ * adaptedInertia hζ ^ (ZMod.cast i : ℤ) := by
  rw [adaptedRep, dihedralHom_sr, ← mul_assoc, adaptedFrob_mul_self, one_mul]

/-- A tame inertia generator acts on the standard lattice by `diag(ζ, ζ²)`. -/
@[simp]
theorem standardRep_r_one (hζ : ζ ^ 2 + ζ + 1 = 0) :
    (standardRep hζ (r 1) : Matrix (Fin 2) (Fin 2) R) = !![ζ, 0; 0, ζ ^ 2] := by
  rw [standardRep_r, ZMod.cast_eq_val, ZMod.val_one, Nat.cast_one, zpow_one]
  simp [stdInertia]

/-- A Frobenius lift acts on the standard lattice by `(0, 1; 1, 0)`. -/
@[simp]
theorem standardRep_sr_zero (hζ : ζ ^ 2 + ζ + 1 = 0) :
    (standardRep hζ (sr 0) : Matrix (Fin 2) (Fin 2) R) = !![0, 1; 1, 0] := by
  rw [standardRep_sr]
  simp [stdFrob]

/-- A tame inertia generator acts on the adapted lattice by `(ζ, 0; ζ, ζ²)`. -/
@[simp]
theorem adaptedRep_r_one (hζ : ζ ^ 2 + ζ + 1 = 0) :
    (adaptedRep hζ (r 1) : Matrix (Fin 2) (Fin 2) R) = !![ζ, 0; ζ, ζ ^ 2] := by
  rw [adaptedRep_r, ZMod.cast_eq_val, ZMod.val_one, Nat.cast_one, zpow_one]
  simp [adaptedInertia]

/-- A Frobenius lift acts on the adapted lattice by `(1, ζ - 1; 0, -1)`. -/
@[simp]
theorem adaptedRep_sr_zero (hζ : ζ ^ 2 + ζ + 1 = 0) :
    (adaptedRep hζ (sr 0) : Matrix (Fin 2) (Fin 2) R) = !![1, ζ - 1; 0, -1] := by
  rw [adaptedRep_sr]
  simp [adaptedFrob]

/-- Every Frobenius lift `sr i` is conjugate to `sr 0` by the rotation `r i`: in
`DihedralGroup 3`, `r i * sr 0 * (r i)⁻¹ = sr (-2 * i) = sr i`. -/
private lemma r_mul_sr_zero_mul_inv (i : ZMod 3) : r i * sr 0 * (r i)⁻¹ = sr i := by
  rw [r_mul_sr, inv_r, sr_mul_r]
  congr 1
  revert i
  decide

/-- The matrix `(1, 0; 1, ζ - 1)` of the inclusion of the adapted lattice `L₁` into the standard
lattice `L₀`: its columns are the coordinates of `e₁ + e₂` and `πe₂` in the basis `e₁, e₂`. -/
def latticeInclusion (ζ : R) : Matrix (Fin 2) (Fin 2) R :=
  !![1, 0; 1, ζ - 1]

/-- The index of `L₁` in `L₀` is generated by `π = ζ - 1`. -/
@[simp]
theorem det_latticeInclusion (ζ : R) : (latticeInclusion ζ).det = ζ - 1 := by
  simp [latticeInclusion, det_fin_two_of]

private lemma semiconjBy_latticeInclusion (hζ : ζ ^ 2 + ζ + 1 = 0) (g : DihedralGroup 3) :
    SemiconjBy (latticeInclusion ζ) (adaptedRep hζ g : Matrix (Fin 2) (Fin 2) R)
      (standardRep hζ g) := by
  have hD : SemiconjBy (latticeInclusion ζ) (adaptedInertia hζ : Matrix (Fin 2) (Fin 2) R)
      (stdInertia hζ) := by
    unfold SemiconjBy
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [latticeInclusion, adaptedInertia, stdInertia] <;> grind
  have hF : SemiconjBy (latticeInclusion ζ) (adaptedFrob ζ : Matrix (Fin 2) (Fin 2) R)
      ((stdFrob : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) := by
    unfold SemiconjBy
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [latticeInclusion, adaptedFrob, stdFrob]
  rcases g with i | i
  · rw [standardRep_r, adaptedRep_r]
    exact hD.units_zpow_right _
  · rw [standardRep_sr, adaptedRep_sr, Units.val_mul, Units.val_mul]
    exact hF.mul_right (hD.units_zpow_right _)

/-- **The inclusion `L₁ ⊆ L₀` is equivariant**: `latticeInclusion ζ` intertwines the adapted and
the standard lattice. -/
theorem standardRep_mul_latticeInclusion (hζ : ζ ^ 2 + ζ + 1 = 0) (g : DihedralGroup 3) :
    (standardRep hζ g : Matrix (Fin 2) (Fin 2) R) * latticeInclusion ζ =
      latticeInclusion ζ * adaptedRep hζ g :=
  (semiconjBy_latticeInclusion hζ g).eq.symm

/-- **`L₁` is a lattice in the same representation.** When `π = ζ - 1` is invertible, as over
the fraction field of `ℤ₃[ζ]`, the adapted representation is the standard one conjugated by
`latticeInclusion ζ`. -/
theorem adaptedRep_eq_inv_mul_mul (hζ : ζ ^ 2 + ζ + 1 = 0) (hπ : IsUnit (ζ - 1))
    (g : DihedralGroup 3) :
    (adaptedRep hζ g : Matrix (Fin 2) (Fin 2) R) =
      (latticeInclusion ζ)⁻¹ * standardRep hζ g * latticeInclusion ζ := by
  have h : IsUnit (latticeInclusion ζ).det := by rwa [det_latticeInclusion]
  rw [mul_assoc, standardRep_mul_latticeInclusion, ← mul_assoc, nonsing_inv_mul _ h, one_mul]

/-- Every Frobenius lift acts on the standard lattice with trace zero. -/
@[simp]
theorem trace_standardRep_sr (hζ : ζ ^ 2 + ζ + 1 = 0) (i : ZMod 3) :
    (standardRep hζ (sr i) : Matrix (Fin 2) (Fin 2) R).trace = 0 := by
  rw [← r_mul_sr_zero_mul_inv, map_mul, map_mul, map_inv, Units.val_mul, Units.val_mul,
    trace_units_conj, standardRep_sr_zero, trace_fin_two_of, add_zero]

/-- Every Frobenius lift acts on the adapted lattice with trace zero. -/
@[simp]
theorem trace_adaptedRep_sr (hζ : ζ ^ 2 + ζ + 1 = 0) (i : ZMod 3) :
    (adaptedRep hζ (sr i) : Matrix (Fin 2) (Fin 2) R).trace = 0 := by
  rw [← r_mul_sr_zero_mul_inv, map_mul, map_mul, map_inv, Units.val_mul, Units.val_mul,
    trace_units_conj, adaptedRep_sr_zero, trace_fin_two_of, add_neg_cancel]

end Lattices

section BaseChange

variable {R S : Type*} [CommRing R] [CommRing S] {ζ : R} {ξ : S}

private lemma map_stdInertia (f : R →+* S) (hf : f ζ = ξ) (hζ : ζ ^ 2 + ζ + 1 = 0)
    (hξ : ξ ^ 2 + ξ + 1 = 0) :
    Matrix.GeneralLinearGroup.map f (stdInertia hζ) = stdInertia hξ := by
  subst hf
  ext i j
  fin_cases i <;> fin_cases j <;> simp [stdInertia]

private lemma map_stdFrob (f : R →+* S) :
    Matrix.GeneralLinearGroup.map f (stdFrob : GL (Fin 2) R) = stdFrob := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [stdFrob]

private lemma map_adaptedInertia (f : R →+* S) (hf : f ζ = ξ) (hζ : ζ ^ 2 + ζ + 1 = 0)
    (hξ : ξ ^ 2 + ξ + 1 = 0) :
    Matrix.GeneralLinearGroup.map f (adaptedInertia hζ) = adaptedInertia hξ := by
  subst hf
  ext i j
  fin_cases i <;> fin_cases j <;> simp [adaptedInertia]

private lemma map_adaptedFrob (f : R →+* S) (hf : f ζ = ξ) :
    Matrix.GeneralLinearGroup.map f (adaptedFrob ζ) = adaptedFrob ξ := by
  subst hf
  ext i j
  fin_cases i <;> fin_cases j <;> simp [adaptedFrob]

/-- The standard lattice commutes with change of coefficients along any ring homomorphism `f`;
for `f ζ = 1` this is its reduction modulo `π`. -/
theorem map_comp_standardRep (f : R →+* S) (hf : f ζ = ξ) (hζ : ζ ^ 2 + ζ + 1 = 0)
    (hξ : ξ ^ 2 + ξ + 1 = 0) :
    (Matrix.GeneralLinearGroup.map f).comp (standardRep hζ) = standardRep hξ := by
  ext1 g
  rcases g with i | i
  · rw [MonoidHom.comp_apply, standardRep_r, standardRep_r, map_zpow,
      map_stdInertia f hf hζ hξ]
  · rw [MonoidHom.comp_apply, standardRep_sr, standardRep_sr, map_mul, map_zpow, map_stdFrob,
      map_stdInertia f hf hζ hξ]

/-- The adapted lattice commutes with change of coefficients along any ring homomorphism `f`;
for `f ζ = 1` this is its reduction modulo `π`. -/
theorem map_comp_adaptedRep (f : R →+* S) (hf : f ζ = ξ) (hζ : ζ ^ 2 + ζ + 1 = 0)
    (hξ : ξ ^ 2 + ξ + 1 = 0) :
    (Matrix.GeneralLinearGroup.map f).comp (adaptedRep hζ) = adaptedRep hξ := by
  ext1 g
  rcases g with i | i
  · rw [MonoidHom.comp_apply, adaptedRep_r, adaptedRep_r, map_zpow,
      map_adaptedInertia f hf hζ hξ]
  · rw [MonoidHom.comp_apply, adaptedRep_sr, adaptedRep_sr, map_mul, map_zpow,
      map_adaptedFrob f hf, map_adaptedInertia f hf hζ hξ]

end BaseChange

/-! ### The reductions modulo `π`

Where `ζ` becomes `1`, so that `3 = 0`, the two lattices are the representations at `ζ = 1`
(`TauCeti.OrderThreeType.map_comp_standardRep`, `TauCeti.OrderThreeType.map_comp_adaptedRep`).
Inertia acts trivially on the reduction of `L₀` and by the nontrivial unipotent `(1, 0; 1, 1)`
on that of `L₁`. -/

section Reduction

variable {R : Type*} [CommRing R]

/-- **Inertia acts trivially on `L₀/πL₀`.** -/
@[simp]
theorem standardRep_r_eq_one (h : (1 : R) ^ 2 + 1 + 1 = 0) (i : ZMod 3) :
    standardRep h (r i) = 1 := by
  have h1 : stdInertia h = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [stdInertia]
  rw [standardRep_r, h1, one_zpow]

variable {k : Type*} [Field k]

/-- Over a field in which `ζ = 1`, the inertia invariants of the reduction of the standard
lattice are two-dimensional. -/
theorem finrank_ker_standardRep_r_one_sub_one (h : (1 : k) ^ 2 + 1 + 1 = 0) :
    Module.finrank k
      (LinearMap.ker (toLin' ((standardRep h (r 1) : Matrix (Fin 2) (Fin 2) k) - 1))) = 2 := by
  rw [standardRep_r_eq_one, Units.val_one, sub_self, map_zero, LinearMap.ker_zero, finrank_top,
    Module.finrank_fin_fun]

/-- Over a field in which `ζ = 1`, the inertia invariants of the reduction of the adapted
lattice are one-dimensional, spanned by the second basis vector `πe₂`. -/
theorem finrank_ker_adaptedRep_r_one_sub_one (h : (1 : k) ^ 2 + 1 + 1 = 0) :
    Module.finrank k
      (LinearMap.ker (toLin' ((adaptedRep h (r 1) : Matrix (Fin 2) (Fin 2) k) - 1))) = 1 := by
  have hker : LinearMap.ker (toLin' ((adaptedRep h (r 1) : Matrix (Fin 2) (Fin 2) k) - 1)) =
      k ∙ Pi.single 1 1 := by
    ext v
    simp only [LinearMap.mem_ker, toLin'_apply, adaptedRep_r_one, Submodule.mem_span_singleton]
    constructor
    · intro hv
      have h0 : v 0 = 0 := by simpa [mulVec, dotProduct, Fin.sum_univ_two] using congrFun hv 1
      refine ⟨v 1, ?_⟩
      ext j
      fin_cases j <;> simp [h0]
    · rintro ⟨a, rfl⟩
      ext j
      fin_cases j <;> simp [mulVec, dotProduct, Fin.sum_univ_two]
  rw [hker, finrank_span_singleton (by simp)]

/-- **Selecting `L₀`.** Over a field in which `ζ = 1`, a Frobenius `F` with eigenvalues `γ` and
`-γ` (trace `0`, determinant `-γ²`) is conjugate to the reduction of the standard lattice's
Frobenius twisted by `γ`. Together with the trivial inertia action on `L₀/πL₀`
(`TauCeti.OrderThreeType.standardRep_r_eq_one`), the reduction of `L₀` twisted by the unramified
character `Frob₂ ↦ γ` realises every residual representation of the tame quotient at `2` on which
inertia acts trivially and `Frob₂` has eigenvalues `±γ`. -/
theorem exists_conj_standardRep (h : (1 : k) ^ 2 + 1 + 1 = 0) (F : GL (Fin 2) k) (γ : kˣ)
    (htr : (F : Matrix (Fin 2) (Fin 2) k).trace = 0)
    (hdet : (F : Matrix (Fin 2) (Fin 2) k).det = -(γ : k) ^ 2) :
    ∃ B : GL (Fin 2) k,
      B * F * B⁻¹ = Matrix.GeneralLinearGroup.scalar (Fin 2) γ * standardRep h (sr 0) := by
  suffices ∃ Q : GL (Fin 2) k,
      F * Q = Q * (Matrix.GeneralLinearGroup.scalar (Fin 2) γ * standardRep h (sr 0)) by
    obtain ⟨Q, hQ⟩ := this
    exact ⟨Q⁻¹, by rw [inv_inv, mul_assoc, hQ, ← mul_assoc, inv_mul_cancel, one_mul]⟩
  have h2 : (2 : k) ≠ 0 := fun h2 => one_ne_zero (by linear_combination h - h2)
  have hγ : (γ : k) ≠ 0 := γ.ne_zero
  obtain ⟨a, b, c, d, hF⟩ : ∃ a b c d : k, (F : Matrix (Fin 2) (Fin 2) k) = !![a, b; c, d] :=
    ⟨_, _, _, _, eta_fin_two _⟩
  rw [hF, trace_fin_two_of] at htr
  rw [hF, det_fin_two_of] at hdet
  -- The columns `v` and `F v / γ` form the required basis whenever `v` is not an eigenvector.
  have key (x y : k) (hxy : x * (c * x + d * y) - y * (a * x + b * y) ≠ 0) :
      ∃ Q : GL (Fin 2) k,
        F * Q = Q * (Matrix.GeneralLinearGroup.scalar (Fin 2) γ * standardRep h (sr 0)) := by
    refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero
      !![x, (a * x + b * y) / γ; y, (c * x + d * y) / γ] ?_, ?_⟩
    · rw [det_fin_two_of]
      contrapose hxy
      field_simp at hxy
      linear_combination hxy
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [hF, ← smul_eq_diagonal_mul] <;> field_simp
      · linear_combination (-x) * hdet + (a * x + b * y) * htr
      · linear_combination (-y) * hdet + (c * x + d * y) * htr
  by_cases hc : c = 0
  · by_cases hb : b = 0
    · subst hb hc
      refine key 1 1 ?_
      have ha : a ≠ 0 := by
        rintro rfl
        exact hγ (pow_eq_zero_iff two_ne_zero |>.mp (by linear_combination hdet))
      have hd : d = -a := by linear_combination htr
      subst hd
      intro h'
      exact mul_ne_zero h2 ha (by linear_combination -h')
    · exact key 0 1 (by simpa using hb)
  · exact key 1 0 (by simpa using hc)

/-- A nontrivial square-zero perturbation `S` of the identity is conjugate to the inertia matrix
`(1, 0; 1, 1)` of `L₁/πL₁`. -/
private lemma exists_mul_eq_mul_adaptedRep_r_one (h : (1 : k) ^ 2 + 1 + 1 = 0)
    {S : GL (Fin 2) k} (hS : ((S : Matrix (Fin 2) (Fin 2) k) - 1) ^ 2 = 0) (hS1 : S ≠ 1) :
    ∃ Q : GL (Fin 2) k, S * Q = Q * adaptedRep h (r 1) := by
  obtain ⟨a, b, c, d, hSm⟩ : ∃ a b c d : k,
      (S : Matrix (Fin 2) (Fin 2) k) = !![1 + a, b; c, 1 + d] :=
    ⟨S 0 0 - 1, S 0 1, S 1 0, S 1 1 - 1, by rw [eta_fin_two (S : Matrix (Fin 2) (Fin 2) k)]; simp⟩
  have hn : (S : Matrix (Fin 2) (Fin 2) k) - 1 = !![a, b; c, d] := by
    rw [hSm]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  rw [hn, sq, mul_fin_two] at hS
  have h00 : a * a + b * c = 0 := by simpa using congrFun (congrFun hS 0) 0
  have h10 : c * a + d * c = 0 := by simpa using congrFun (congrFun hS 1) 0
  have h11 : c * b + d * d = 0 := by simpa using congrFun (congrFun hS 1) 1
  by_cases hc : c = 0
  · subst hc
    have ha : a = 0 := mul_self_eq_zero.mp (by simpa using h00)
    have hd : d = 0 := mul_self_eq_zero.mp (by simpa using h11)
    subst ha hd
    have hb : b ≠ 0 := by
      rintro rfl
      exact hS1 (Units.ext (by rw [hSm]; simp [one_fin_two]))
    refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero !![0, b; 1, 0] (by simpa using hb), ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hSm]
  · refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero !![1, a; 0, c] (by simpa using hc), ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hSm]
    · linear_combination h00
    · linear_combination h10

/-- A Frobenius `F` satisfying the tame relation `F D F⁻¹ = D²` with the reduced inertia
`D = (1, 0; 1, 1)` of `L₁` is, after a conjugation commuting with `D`, a scalar multiple of the
reduced Frobenius `diag(1, -1)`. -/
private lemma exists_commute_adaptedRep_r_one (h : (1 : k) ^ 2 + 1 + 1 = 0) {F : GL (Fin 2) k}
    (hF : F * adaptedRep h (r 1) = adaptedRep h (r 1) ^ 2 * F) :
    ∃ (u : kˣ) (Q : GL (Fin 2) k), adaptedRep h (r 1) * Q = Q * adaptedRep h (r 1) ∧
      F * Q = Q * (Matrix.GeneralLinearGroup.scalar (Fin 2) u * adaptedRep h (sr 0)) := by
  obtain ⟨p, q, x, t, hFm⟩ : ∃ p q x t : k, (F : Matrix (Fin 2) (Fin 2) k) = !![p, q; x, t] :=
    ⟨_, _, _, _, eta_fin_two _⟩
  have hF' := congrArg Units.val hF
  simp only [Units.val_mul, adaptedRep_r_one, hFm, sq] at hF'
  have hq : q = 0 := by simpa using congrFun (congrFun hF' 0) 0
  have ht : t = 2 * p := by
    have e := congrFun (congrFun hF' 1) 0
    simp at e
    linear_combination e
  subst hq ht
  have hp : p ≠ 0 := by
    rintro rfl
    exact F.det_ne_zero (by simp [hFm])
  refine ⟨Units.mk0 p hp,
    Matrix.GeneralLinearGroup.mkOfDetNeZero !![1, 0; -x / p, 1] (by simp), ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> simp
    ring
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [hFm, ← smul_eq_diagonal_mul] <;> field_simp
    · ring
    · linear_combination h

/-- **Selecting `L₁`.** Over a field in which `ζ = 1`, let `S` be a nontrivial unipotent
(`(S - 1)² = 0`, `S ≠ 1`) and `F` an invertible matrix with `F S F⁻¹ = S²`, the image of a tame
inertia generator and of `Frob₂` under a residual representation of the tame quotient at `2`.
Then `(S, F)` is simultaneously conjugate to the reduction of the adapted lattice twisted by an
unramified scalar `u`: `S` to `(1, 0; 1, 1)` and `F` to `u • diag(1, -1)`. The standard lattice
cannot serve here, since inertia acts trivially on its reduction
(`TauCeti.OrderThreeType.standardRep_r_eq_one`). -/
theorem exists_conj_adaptedRep (h : (1 : k) ^ 2 + 1 + 1 = 0) {S F : GL (Fin 2) k}
    (hS : ((S : Matrix (Fin 2) (Fin 2) k) - 1) ^ 2 = 0) (hS1 : S ≠ 1) (hFS : F * S = S ^ 2 * F) :
    ∃ (u : kˣ) (B : GL (Fin 2) k), B * S * B⁻¹ = adaptedRep h (r 1) ∧
      B * F * B⁻¹ = Matrix.GeneralLinearGroup.scalar (Fin 2) u * adaptedRep h (sr 0) := by
  obtain ⟨Q₁, hQ₁⟩ := exists_mul_eq_mul_adaptedRep_r_one h hS hS1
  set D := adaptedRep h (r 1)
  have hS' : S = Q₁ * D * Q₁⁻¹ := by rw [← hQ₁, mul_inv_cancel_right]
  have hF' : Q₁⁻¹ * F * Q₁ * D = D ^ 2 * (Q₁⁻¹ * F * Q₁) :=
    calc Q₁⁻¹ * F * Q₁ * D = Q₁⁻¹ * (F * S) * Q₁ := by rw [hS']; group
      _ = Q₁⁻¹ * (S ^ 2 * F) * Q₁ := by rw [hFS]
      _ = D ^ 2 * (Q₁⁻¹ * F * Q₁) := by rw [hS', conj_pow]; group
  obtain ⟨u, Q₂, hD, hQ₂⟩ := exists_commute_adaptedRep_r_one h hF'
  refine ⟨u, (Q₁ * Q₂)⁻¹, ?_, ?_⟩
  · rw [inv_inv, hS', _root_.mul_inv_rev]
    calc Q₂⁻¹ * Q₁⁻¹ * (Q₁ * D * Q₁⁻¹) * (Q₁ * Q₂) = Q₂⁻¹ * (D * Q₂) := by group
      _ = D := by rw [hD, inv_mul_cancel_left]
  · rw [inv_inv, _root_.mul_inv_rev]
    calc Q₂⁻¹ * Q₁⁻¹ * F * (Q₁ * Q₂) = Q₂⁻¹ * (Q₁⁻¹ * F * Q₁ * Q₂) := by group
      _ = _ := by rw [hQ₂, inv_mul_cancel_left]

end Reduction

end TauCeti.OrderThreeType
