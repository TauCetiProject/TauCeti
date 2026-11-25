/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Matrix.ColumnRowPartitioned
public import TauCeti.Analysis.Complex.SiegelUpperHalfSpace
import Mathlib.LinearAlgebra.Matrix.Integer

/-!
# Period matrices and the symplectic action on the fibres of the Siegel family

For `Ω` in the Siegel upper half space `H_g`, the fibre of the Siegel family over `Ω` is the torus
`ℂ^g / (ℤ^g + Ω ℤ^g)`, whose lattice is the image of the **period map**
`Π_Ω : ℤ^g × ℤ^g → ℂ^g`, `(a, b) ↦ Ω a + b`. In matrix form `Π_Ω` is the `g × 2g` matrix
`[Ω 1]` (`TauCeti.siegelPeriodMatrix`).

An integral symplectic matrix `M = [[A, B], [C, D]]` acts on `H_g` by `Ω ↦ M · Ω`
(`TauCeti.siegelAction`), on the fibres by the linear maps `R_M(Ω) = (C Ω + D)⁻ᵀ`
(`TauCeti.siegelFibreMap`), and on the lattice `ℤ^{2g}` by `ρ(M) = M⁻ᵀ`
(`TauCeti.siegelLatticeMap`). This file proves that these three actions are compatible: the
**period-equivariance law** `R_M(Ω) Π_Ω(v) = Π_{M · Ω}(M⁻ᵀ v)`
(`TauCeti.siegelFibreMap_mulVec_siegelPeriodMatrix_mulVec`), and the **cocycle law**
`R_{M N}(Ω) = R_M(N · Ω) R_N(Ω)` (`TauCeti.siegelFibreMap_mul`), with `ρ` multiplicative
(`TauCeti.siegelLatticeMap_mul`). The proof of equivariance is the identity
`[Ω 1] Mᵀ = [(A Ω + B)ᵀ (C Ω + D)ᵀ]` for symmetric `Ω`, combined with the symmetry of `M · Ω`.

## Main definitions

* `TauCeti.siegelPeriodMatrix Ω`: the period matrix `[Ω 1]`.
* `TauCeti.siegelFibreMap M Ω`: the fibre map `R_M(Ω) = (C Ω + D)⁻ᵀ`.
* `TauCeti.siegelLatticeMap M`: the lattice action `ρ(M) = M⁻ᵀ`.

## Main results

* `TauCeti.siegelPeriodMatrix_mulVec_sumElim`: `Π_Ω(a, b) = Ω a + b`.
* `TauCeti.siegelPeriodMatrix_mul_transpose`: `[Ω 1] Mᵀ = [(A Ω + B)ᵀ (C Ω + D)ᵀ]` for symmetric
  `Ω`.
* `TauCeti.siegelFibreMap_mul_siegelPeriodMatrix`: `R_M(Ω) Π_Ω = Π_{M · Ω} M⁻ᵀ` for symplectic `M`
  and `Ω ∈ H_g`, and its vector form `TauCeti.siegelFibreMap_mulVec_siegelPeriodMatrix_mulVec`.
* `TauCeti.siegelFibreMap_mul`: the cocycle law `R_{M N}(Ω) = R_M(N · Ω) R_N(Ω)`.
* `TauCeti.siegelLatticeMap_mul`: `ρ(M N) = ρ(M) ρ(N)`.

## References

* Faltings–Chai, I.6, pp. 29–30, for the Siegel space and the action of `Sp_{2g}(ℤ)`.
-/

public section

open Matrix

namespace TauCeti

variable {g : ℕ}

/-- The **period matrix** `Π_Ω = [Ω 1]` of a complex `g × g` matrix `Ω`: the `g × 2g` matrix of the
period map `(a, b) ↦ Ω a + b`, whose image is the lattice `ℤ^g + Ω ℤ^g`. -/
def siegelPeriodMatrix (Ω : Matrix (Fin g) (Fin g) ℂ) : Matrix (Fin g) (Fin g ⊕ Fin g) ℂ :=
  fromCols Ω 1

theorem siegelPeriodMatrix_def (Ω : Matrix (Fin g) (Fin g) ℂ) :
    siegelPeriodMatrix Ω = fromCols Ω 1 :=
  (rfl)

/-- The period map sends `(a, b)` to `Ω a + b`. -/
@[simp]
theorem siegelPeriodMatrix_mulVec_sumElim (Ω : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℂ) :
    siegelPeriodMatrix Ω *ᵥ Sum.elim a b = Ω *ᵥ a + b := by
  rw [siegelPeriodMatrix_def, fromCols_mulVec_sumElim, one_mulVec]

/-- The **fibre map** `R_M(Ω) = (C Ω + D)⁻ᵀ` of an integral block matrix `M = [[A, B], [C, D]]` at
`Ω`: the linear map from the fibre over `Ω` to the fibre over `M · Ω`. -/
noncomputable def siegelFibreMap (M : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ)
    (Ω : Matrix (Fin g) (Fin g) ℂ) : Matrix (Fin g) (Fin g) ℂ :=
  (siegelFactor M Ω)⁻¹ᵀ

theorem siegelFibreMap_def (M : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ)
    (Ω : Matrix (Fin g) (Fin g) ℂ) : siegelFibreMap M Ω = (siegelFactor M Ω)⁻¹ᵀ :=
  (rfl)

/-- The **lattice action** `ρ(M) = M⁻ᵀ` of an integral matrix on `ℤ^{2g}`. -/
noncomputable def siegelLatticeMap (M : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ) :
    Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ :=
  M⁻¹ᵀ

theorem siegelLatticeMap_def (M : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ) :
    siegelLatticeMap M = M⁻¹ᵀ :=
  (rfl)

@[simp]
theorem siegelFibreMap_one (Ω : Matrix (Fin g) (Fin g) ℂ) : siegelFibreMap 1 Ω = 1 := by
  rw [siegelFibreMap_def, siegelFactor_one, inv_one, transpose_one]

@[simp]
theorem siegelLatticeMap_one :
    siegelLatticeMap (1 : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ) = 1 := by
  rw [siegelLatticeMap_def, inv_one, transpose_one]

/-- `ρ` is multiplicative: `(M N)⁻ᵀ = M⁻ᵀ N⁻ᵀ`. -/
theorem siegelLatticeMap_mul (M N : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ) :
    siegelLatticeMap (M * N) = siegelLatticeMap M * siegelLatticeMap N := by
  rw [siegelLatticeMap_def, siegelLatticeMap_def, siegelLatticeMap_def, Matrix.mul_inv_rev,
    transpose_mul]

/-- For symplectic `M`, `ρ(M) = M⁻ᵀ` is a left inverse of `Mᵀ`. -/
theorem siegelLatticeMap_mul_transpose {M : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ}
    (hM : M ∈ symplecticGroup (Fin g) ℤ) : Mᵀ * siegelLatticeMap M = 1 := by
  rw [siegelLatticeMap_def, ← transpose_mul, nonsing_inv_mul _ (SymplecticGroup.symplectic_det hM),
    transpose_one]

/-- **The cocycle law** `R_{M N}(Ω) = R_M(N · Ω) R_N(Ω)` for symplectic `N` and `Ω` in the Siegel
space. -/
theorem siegelFibreMap_mul {M N : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ}
    {Ω : Matrix (Fin g) (Fin g) ℂ} (hN : N ∈ symplecticGroup (Fin g) ℤ)
    (hΩ : Ω ∈ SiegelUpperHalfSpace g) :
    siegelFibreMap (M * N) Ω = siegelFibreMap M (siegelAction N Ω) * siegelFibreMap N Ω := by
  rw [siegelFibreMap_def, siegelFactor_mul hN hΩ, Matrix.mul_inv_rev, transpose_mul,
    siegelFibreMap_def, siegelFibreMap_def]

/-- For symplectic `M` and `Ω` in the Siegel space, the fibre map is invertible. -/
theorem isUnit_det_siegelFibreMap {M : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ}
    {Ω : Matrix (Fin g) (Fin g) ℂ} (hM : M ∈ symplecticGroup (Fin g) ℤ)
    (hΩ : Ω ∈ SiegelUpperHalfSpace g) : IsUnit (siegelFibreMap M Ω).det := by
  rw [siegelFibreMap_def, det_transpose]
  exact isUnit_nonsing_inv_det _ (isUnit_det_siegelFactor hM hΩ)

/-- **The period matrix times `Mᵀ`.** For a symmetric `Ω` and an integral block matrix
`M = [[A, B], [C, D]]`, `[Ω 1] Mᵀ = [(A Ω + B)ᵀ (C Ω + D)ᵀ]`. -/
theorem siegelPeriodMatrix_mul_transpose (M : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ)
    {Ω : Matrix (Fin g) (Fin g) ℂ} (hΩ : Ωᵀ = Ω) :
    siegelPeriodMatrix Ω * (M.map ((↑) : ℤ → ℂ))ᵀ =
      fromCols (siegelNumerator M Ω)ᵀ (siegelFactor M Ω)ᵀ := by
  rw [← fromBlocks_toBlocks (M.map ((↑) : ℤ → ℂ)), fromBlocks_transpose, siegelPeriodMatrix_def,
    fromCols_mul_fromBlocks, siegelNumerator_def, siegelFactor_def, transpose_add, transpose_mul,
    transpose_add, transpose_mul, hΩ, Matrix.one_mul, Matrix.one_mul]

/-- **Period equivariance, matrix form with `Mᵀ`.** For symplectic `M` and `Ω` in the Siegel space,
`R_M(Ω) Π_Ω Mᵀ = Π_{M · Ω}`. -/
theorem siegelFibreMap_mul_siegelPeriodMatrix_mul_transpose
    {M : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ} {Ω : Matrix (Fin g) (Fin g) ℂ}
    (hM : M ∈ symplecticGroup (Fin g) ℤ) (hΩ : Ω ∈ SiegelUpperHalfSpace g) :
    siegelFibreMap M Ω * siegelPeriodMatrix Ω * (M.map ((↑) : ℤ → ℂ))ᵀ =
      siegelPeriodMatrix (siegelAction M Ω) := by
  rw [Matrix.mul_assoc, siegelPeriodMatrix_mul_transpose M (SiegelUpperHalfSpace.transpose_eq hΩ),
    mul_fromCols, siegelFibreMap_def, ← transpose_mul, ← transpose_mul,
    mul_nonsing_inv _ (isUnit_det_siegelFactor hM hΩ), transpose_one, ← siegelAction_def,
    transpose_siegelAction hM hΩ, siegelPeriodMatrix_def]

/-- **Period equivariance**, matrix form: for symplectic `M` and `Ω` in the Siegel space,
`R_M(Ω) Π_Ω = Π_{M · Ω} ρ(M)` with `ρ(M) = M⁻ᵀ`. -/
theorem siegelFibreMap_mul_siegelPeriodMatrix {M : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ}
    {Ω : Matrix (Fin g) (Fin g) ℂ} (hM : M ∈ symplecticGroup (Fin g) ℤ)
    (hΩ : Ω ∈ SiegelUpperHalfSpace g) :
    siegelFibreMap M Ω * siegelPeriodMatrix Ω =
      siegelPeriodMatrix (siegelAction M Ω) * (siegelLatticeMap M).map ((↑) : ℤ → ℂ) := by
  rw [← siegelFibreMap_mul_siegelPeriodMatrix_mul_transpose hM hΩ, Matrix.mul_assoc,
    ← transpose_map, ← Matrix.map_mul_intCast, siegelLatticeMap_mul_transpose hM,
    Matrix.map_one _ Int.cast_zero Int.cast_one, Matrix.mul_one]

/-- **Period equivariance** `R_M(Ω) Π_Ω(v) = Π_{M · Ω}(M⁻ᵀ v)` for symplectic `M`, `Ω` in the
Siegel space and a lattice vector `v ∈ ℤ^{2g}`. -/
theorem siegelFibreMap_mulVec_siegelPeriodMatrix_mulVec
    {M : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ} {Ω : Matrix (Fin g) (Fin g) ℂ}
    (hM : M ∈ symplecticGroup (Fin g) ℤ) (hΩ : Ω ∈ SiegelUpperHalfSpace g)
    (v : Fin g ⊕ Fin g → ℤ) :
    siegelFibreMap M Ω *ᵥ (siegelPeriodMatrix Ω *ᵥ ((↑) ∘ v)) =
      siegelPeriodMatrix (siegelAction M Ω) *ᵥ ((↑) ∘ (siegelLatticeMap M *ᵥ v)) := by
  rw [mulVec_mulVec, siegelFibreMap_mul_siegelPeriodMatrix hM hΩ, ← mulVec_mulVec]
  congr 1
  funext i
  simpa using (RingHom.map_mulVec (Int.castRingHom ℂ) (siegelLatticeMap M) v i).symm

end TauCeti
