/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.SymplecticLattice.Basic
import TauCeti.LinearAlgebra.BilinearForm.BaseChange

/-!
# Dual indices of symplectic lattices

The standard symplectic plane, with Gram matrix `!![0, 1; -1, 0]`, has dual index one and is
self-dual at every prime. The rank-four lattice with alternating blocks of weights `1` and `d` has
dual index `d²`, so for `d ≠ 0` it is self-dual exactly at the primes not dividing `d`. The zero
lattice has dual index one. The pairing `(x, y) ↦ x * y` on `ℤ` is not alternating, so it is not
a symplectic lattice; alternation is part of the definition, not a consequence of
nondegeneracy.
-/

public section

open Matrix

namespace TauCeti.Examples

/-- The Gram matrix of the standard symplectic plane. -/
abbrev symplecticPlaneGram : Matrix (Fin 2) (Fin 2) ℤ := !![0, 1; -1, 0]

theorem isAlt_toBilin'_symplecticPlaneGram : (Matrix.toBilin' symplecticPlaneGram).IsAlt :=
  fun x ↦ by
    simp [Matrix.toBilin'_apply', dotProduct, Fin.sum_univ_two]
    ring

/-- The standard symplectic plane `ℤ²` with `⟨e, f⟩ = 1`. -/
noncomputable def symplecticPlane : SymplecticOLattice ℤ (Fin 2 → ℤ) :=
  .ofIsAlt (Matrix.toBilin' symplecticPlaneGram) isAlt_toBilin'_symplecticPlaneGram
    (by
      rw [LinearMap.BilinForm.nondegenerate_baseChange_iff (A := ℚ) _ (Pi.basisFun ℤ (Fin 2)),
        LinearMap.BilinForm.nondegenerate_iff_det_ne_zero (Pi.basisFun ℤ (Fin 2)),
        LinearMap.BilinForm.toMatrix_basisFun, LinearMap.BilinForm.toMatrix'_toBilin']
      simp [det_fin_two])

/-- The standard symplectic plane is self-dual: its dual index is one. -/
theorem symplecticPlane_dualIndex : symplecticPlane.dualIndex = 1 := by
  rw [symplecticPlane.dualIndex_eq_natAbs_det (Pi.basisFun ℤ (Fin 2)), symplecticPlane,
    SymplecticOLattice.ofIsAlt_form, LinearMap.BilinForm.toMatrix_basisFun,
    LinearMap.BilinForm.toMatrix'_toBilin']
  simp [det_fin_two]

/-- The standard symplectic plane is self-dual at every prime. -/
theorem symplecticPlane_isSelfDualAt {p : ℕ} (hp : p.Prime) : symplecticPlane.IsSelfDualAt p :=
  symplecticPlane.isSelfDualAt_of_not_dvd_dualIndex (symplecticPlane_dualIndex ▸ hp.not_dvd_one)

/-- The Gram matrix of the rank-four lattice with alternating blocks of weights `1` and `d`. -/
abbrev weightedGram (d : ℤ) : Matrix (Fin 4) (Fin 4) ℤ :=
  !![0, 1, 0, 0; -1, 0, 0, 0; 0, 0, 0, d; 0, 0, -d, 0]

theorem det_weightedGram (d : ℤ) : (weightedGram d).det = d ^ 2 := by
  simp [det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
  ring

theorem isAlt_toBilin'_weightedGram (d : ℤ) : (Matrix.toBilin' (weightedGram d)).IsAlt :=
  fun x ↦ by
    simp [Matrix.toBilin'_apply', dotProduct, Fin.sum_univ_four]
    ring

/-- The rank-four symplectic lattice with alternating blocks of weights `1` and `d ≠ 0`. -/
noncomputable def weightedLattice (d : ℤ) (hd : d ≠ 0) : SymplecticOLattice ℤ (Fin 4 → ℤ) :=
  .ofIsAlt (Matrix.toBilin' (weightedGram d))
    (isAlt_toBilin'_weightedGram d)
    (by
      rw [LinearMap.BilinForm.nondegenerate_baseChange_iff (A := ℚ) _ (Pi.basisFun ℤ (Fin 4)),
        LinearMap.BilinForm.nondegenerate_iff_det_ne_zero (Pi.basisFun ℤ (Fin 4)),
        LinearMap.BilinForm.toMatrix_basisFun, LinearMap.BilinForm.toMatrix'_toBilin',
        det_weightedGram]
      exact pow_ne_zero 2 hd)

/-- The lattice with blocks of weights `1` and `d` has dual index `d²`. -/
theorem weightedLattice_dualIndex (d : ℤ) (hd : d ≠ 0) :
    (weightedLattice d hd).dualIndex = d.natAbs ^ 2 := by
  rw [(weightedLattice d hd).dualIndex_eq_natAbs_det (Pi.basisFun ℤ (Fin 4)), weightedLattice,
    SymplecticOLattice.ofIsAlt_form, LinearMap.BilinForm.toMatrix_basisFun,
    LinearMap.BilinForm.toMatrix'_toBilin', det_weightedGram, Int.natAbs_pow]

/-- The lattice with blocks of weights `1` and `d` is self-dual exactly at the primes not
dividing `d`. -/
theorem weightedLattice_isSelfDualAt_iff (d : ℤ) (hd : d ≠ 0) {p : ℕ} (hp : p.Prime) :
    (weightedLattice d hd).IsSelfDualAt p ↔ ¬(p : ℤ) ∣ d := by
  rw [SymplecticOLattice.isSelfDualAt_iff_not_dvd_dualIndex _ hp, weightedLattice_dualIndex,
    (Nat.prime_iff.1 hp).dvd_pow_iff_dvd two_ne_zero, Int.natCast_dvd]

/-- The zero lattice `ℤ⁰` has dual index one. -/
theorem zeroLattice_dualIndex : (SymplecticOLattice.zero ℤ (Fin 0 → ℤ)).dualIndex = 1 :=
  SymplecticOLattice.dualIndex_zero

/-- The product pairing on `ℤ` is not alternating, so it does not define a symplectic lattice. -/
theorem not_isAlt_mul : ¬(LinearMap.mul ℤ ℤ).IsAlt := fun h ↦ by
  simpa using h 1

end TauCeti.Examples
