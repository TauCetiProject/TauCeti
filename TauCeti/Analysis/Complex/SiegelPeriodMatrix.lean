/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Matrix.ColumnRowPartitioned
public import TauCeti.Analysis.Complex.SiegelUpperHalfSpace
import Mathlib.LinearAlgebra.Matrix.Integer
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import TauCeti.LinearAlgebra.SymplecticGroup

/-!
# Period matrices and the symplectic action on the fibres of the Siegel family

For `Ω` in the Siegel upper half space `H_g`, the fibre of the Siegel family over `Ω` is the torus
`ℂ^g / (ℤ^g + Ω ℤ^g)`, whose lattice is the image of the **period map**
`Π_Ω : ℤ^g × ℤ^g → ℂ^g`, `(a, b) ↦ Ω a + b`. In matrix form `Π_Ω` is the `g × 2g` matrix
`[Ω 1]` (`TauCeti.siegelPeriodMatrix`).

An integral symplectic matrix `M = [[A, B], [C, D]]` acts on `H_g` by `Ω ↦ M · Ω`
(`TauCeti.siegelAction`), on the fibres by the linear maps `R_M(Ω) = (C Ω + D)⁻ᵀ`
(`TauCeti.siegelFiberMap`), and on the lattice `ℤ^{2g}` by `ρ(M) = M⁻ᵀ`
(`TauCeti.siegelLatticeMap`). This file proves that these three actions are compatible: the
**period-equivariance law** `R_M(Ω) Π_Ω(v) = Π_{M · Ω}(M⁻ᵀ v)`
(`TauCeti.siegelFiberMap_mulVec_siegelPeriodMatrix_mulVec`), and the **cocycle law**
`R_{M N}(Ω) = R_M(N · Ω) R_N(Ω)` (`TauCeti.siegelFiberMap_mul`), with `ρ` multiplicative
(`TauCeti.siegelLatticeMap_mul`). The proof of equivariance is the identity
`[Ω 1] Mᵀ = [(A Ω + B)ᵀ (C Ω + D)ᵀ]` for symmetric `Ω`, combined with the symmetry of `M · Ω`.

## Main definitions

* `TauCeti.siegelPeriodMatrix Ω`: the period matrix `[Ω 1]`.
* `TauCeti.siegelFiberMap M Ω`: the fibre map `R_M(Ω) = (C Ω + D)⁻ᵀ`.
* `TauCeti.siegelLatticeMap M`: the lattice action `ρ(M) = M⁻ᵀ`.

## Main results

* `TauCeti.siegelPeriodMatrix_mulVec_sumElim`: `Π_Ω(a, b) = Ω a + b`.
* `TauCeti.siegelPeriodMatrix_mul_transpose`: `[Ω 1] Mᵀ = [(A Ω + B)ᵀ (C Ω + D)ᵀ]` for symmetric
  `Ω`.
* `TauCeti.siegelFiberMap_mul_siegelPeriodMatrix`: `R_M(Ω) Π_Ω = Π_{M · Ω} M⁻ᵀ` for symplectic `M`
  and `Ω ∈ H_g`, and its vector form `TauCeti.siegelFiberMap_mulVec_siegelPeriodMatrix_mulVec`.
* `TauCeti.siegelFiberMap_mul_of_isUnit`: the cocycle law `R_{M N}(Ω) = R_M(N · Ω) R_N(Ω)` when
  `C_N Ω + D_N` is invertible, and `TauCeti.siegelFiberMap_mul` for symplectic `N` and `Ω ∈ H_g`.
* `TauCeti.siegelFiberMap_mul_transpose_siegelFactor_of_isUnit` and
  `TauCeti.transpose_siegelFactor_mul_siegelFiberMap_of_isUnit`: `R_M(Ω)` is the two-sided
  inverse of `(C Ω + D)ᵀ` when `C Ω + D` is invertible.
* `TauCeti.siegelLatticeMap_mul`: `ρ(M N) = ρ(M) ρ(N)`.
* `TauCeti.siegelLatticeMap_mem_symplecticGroup`: `ρ(M)` is symplectic for symplectic `M`.

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
`Ω`, where `⁻¹` is `Matrix.nonsing_inv`. It is defined for every integral `M`, but it is the
invertible linear map from the fibre over `Ω` to the fibre over `M · Ω` only for symplectic `M` and
`Ω ∈ H_g` (see `TauCeti.isUnit_det_siegelFiberMap` and the period-equivariance theorems below);
otherwise `C Ω + D` may be singular, and then this matrix is `0`. -/
noncomputable def siegelFiberMap (M : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ)
    (Ω : Matrix (Fin g) (Fin g) ℂ) : Matrix (Fin g) (Fin g) ℂ :=
  (siegelFactor M Ω)⁻¹ᵀ

theorem siegelFiberMap_def (M : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ)
    (Ω : Matrix (Fin g) (Fin g) ℂ) : siegelFiberMap M Ω = (siegelFactor M Ω)⁻¹ᵀ :=
  (rfl)

/-- The **lattice action** `ρ(M) = M⁻ᵀ` on `ℤ^{2g}`, where `⁻¹` is `Matrix.nonsing_inv` over `ℤ`.
It is the inverse transpose of `M`, and so an automorphism of `ℤ^{2g}`, only for unimodular (for
instance symplectic) `M`; otherwise `M⁻¹ = 0` and so `ρ(M) = 0`. -/
noncomputable def siegelLatticeMap (M : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ) :
    Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ :=
  M⁻¹ᵀ

theorem siegelLatticeMap_def (M : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ) :
    siegelLatticeMap M = M⁻¹ᵀ :=
  (rfl)

@[simp]
theorem siegelFiberMap_one (Ω : Matrix (Fin g) (Fin g) ℂ) : siegelFiberMap 1 Ω = 1 := by
  rw [siegelFiberMap_def, siegelFactor_one, inv_one, transpose_one]

@[simp]
theorem siegelLatticeMap_one :
    siegelLatticeMap (1 : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ) = 1 := by
  rw [siegelLatticeMap_def, inv_one, transpose_one]

/-- The fibre map of a translation `[[1, B], [0, 1]]` is the identity. -/
@[simp]
theorem siegelFiberMap_translation (B : Matrix (Fin g) (Fin g) ℤ) (Ω : Matrix (Fin g) (Fin g) ℂ) :
    siegelFiberMap (fromBlocks 1 B 0 1) Ω = 1 := by
  rw [siegelFiberMap_def, siegelFactor_translation, inv_one, transpose_one]

/-- The lattice action of a translation `[[1, B], [0, 1]]` is `[[1, 0], [-Bᵀ, 1]]`. -/
@[simp]
theorem siegelLatticeMap_translation (B : Matrix (Fin g) (Fin g) ℤ) :
    siegelLatticeMap (fromBlocks 1 B 0 1) = fromBlocks 1 0 (-Bᵀ) 1 := by
  simp [siegelLatticeMap_def, inv_fromBlocks_zero₂₁_of_isUnit_iff 1 B 1 Iff.rfl,
    fromBlocks_transpose]

/-- `ρ` is multiplicative: `(M N)⁻ᵀ = M⁻ᵀ N⁻ᵀ`. -/
theorem siegelLatticeMap_mul (M N : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ) :
    siegelLatticeMap (M * N) = siegelLatticeMap M * siegelLatticeMap N := by
  rw [siegelLatticeMap_def, siegelLatticeMap_def, siegelLatticeMap_def, Matrix.mul_inv_rev,
    transpose_mul]

/-- For unimodular `M`, `ρ(M) = M⁻ᵀ` is a right inverse of `Mᵀ`. -/
theorem transpose_mul_siegelLatticeMap {M : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ}
    (hM : IsUnit M.det) : Mᵀ * siegelLatticeMap M = 1 := by
  rw [siegelLatticeMap_def, ← transpose_mul, nonsing_inv_mul _ hM, transpose_one]

/-- For unimodular `M`, `ρ(M) = M⁻ᵀ` is a left inverse of `Mᵀ`. -/
theorem siegelLatticeMap_mul_transpose {M : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ}
    (hM : IsUnit M.det) : siegelLatticeMap M * Mᵀ = 1 := by
  rw [siegelLatticeMap_def, ← transpose_mul, mul_nonsing_inv _ hM, transpose_one]

/-- For unimodular `M`, the lattice action `ρ(M)` is unimodular. -/
theorem isUnit_det_siegelLatticeMap {M : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ}
    (hM : IsUnit M.det) : IsUnit (siegelLatticeMap M).det := by
  rw [siegelLatticeMap_def, det_transpose]
  exact isUnit_nonsing_inv_det _ hM

/-- For symplectic `M`, the lattice action `ρ(M) = M⁻ᵀ` is symplectic. -/
theorem siegelLatticeMap_mem_symplecticGroup {M : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ}
    (hM : M ∈ symplecticGroup (Fin g) ℤ) : siegelLatticeMap M ∈ symplecticGroup (Fin g) ℤ :=
  SymplecticGroup.transpose_nonsing_inv_mem hM

/-- **The cocycle law** `R_{M N}(Ω) = R_M(N · Ω) R_N(Ω)`, whenever `j(N, Ω) = C_N Ω + D_N` is
invertible. -/
theorem siegelFiberMap_mul_of_isUnit {M N : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ}
    {Ω : Matrix (Fin g) (Fin g) ℂ} (hN : IsUnit (siegelFactor N Ω).det) :
    siegelFiberMap (M * N) Ω = siegelFiberMap M (siegelAction N Ω) * siegelFiberMap N Ω := by
  rw [siegelFiberMap_def, siegelFactor_mul_of_isUnit hN, Matrix.mul_inv_rev, transpose_mul,
    siegelFiberMap_def, siegelFiberMap_def]

/-- **The cocycle law** `R_{M N}(Ω) = R_M(N · Ω) R_N(Ω)` for symplectic `N` and `Ω` in the Siegel
space. -/
theorem siegelFiberMap_mul {M N : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ}
    {Ω : Matrix (Fin g) (Fin g) ℂ} (hN : N ∈ symplecticGroup (Fin g) ℤ)
    (hΩ : Ω ∈ SiegelUpperHalfSpace g) :
    siegelFiberMap (M * N) Ω = siegelFiberMap M (siegelAction N Ω) * siegelFiberMap N Ω :=
  siegelFiberMap_mul_of_isUnit (isUnit_det_siegelFactor hN hΩ)

/-- For symplectic `M` and `Ω` in the Siegel space, the fibre map is invertible. -/
theorem isUnit_det_siegelFiberMap {M : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ}
    {Ω : Matrix (Fin g) (Fin g) ℂ} (hM : M ∈ symplecticGroup (Fin g) ℤ)
    (hΩ : Ω ∈ SiegelUpperHalfSpace g) : IsUnit (siegelFiberMap M Ω).det := by
  rw [siegelFiberMap_def, det_transpose]
  exact isUnit_nonsing_inv_det _ (isUnit_det_siegelFactor hM hΩ)

/-- When `j(M, Ω) = C Ω + D` is invertible, `R_M(Ω) = j(M, Ω)⁻ᵀ` is a left inverse of
`j(M, Ω)ᵀ`. -/
theorem siegelFiberMap_mul_transpose_siegelFactor_of_isUnit
    {M : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ} {Ω : Matrix (Fin g) (Fin g) ℂ}
    (hM : IsUnit (siegelFactor M Ω).det) : siegelFiberMap M Ω * (siegelFactor M Ω)ᵀ = 1 := by
  rw [siegelFiberMap_def, ← transpose_mul, mul_nonsing_inv _ hM, transpose_one]

/-- When `j(M, Ω) = C Ω + D` is invertible, `R_M(Ω) = j(M, Ω)⁻ᵀ` is a right inverse of
`j(M, Ω)ᵀ`. -/
theorem transpose_siegelFactor_mul_siegelFiberMap_of_isUnit
    {M : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ} {Ω : Matrix (Fin g) (Fin g) ℂ}
    (hM : IsUnit (siegelFactor M Ω).det) : (siegelFactor M Ω)ᵀ * siegelFiberMap M Ω = 1 := by
  rw [siegelFiberMap_def, ← transpose_mul, nonsing_inv_mul _ hM, transpose_one]

/-- For symplectic `M` and `Ω` in the Siegel space, `R_M(Ω) j(M, Ω)ᵀ = 1`. -/
theorem siegelFiberMap_mul_transpose_siegelFactor {M : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ}
    {Ω : Matrix (Fin g) (Fin g) ℂ} (hM : M ∈ symplecticGroup (Fin g) ℤ)
    (hΩ : Ω ∈ SiegelUpperHalfSpace g) : siegelFiberMap M Ω * (siegelFactor M Ω)ᵀ = 1 :=
  siegelFiberMap_mul_transpose_siegelFactor_of_isUnit (isUnit_det_siegelFactor hM hΩ)

/-- For symplectic `M` and `Ω` in the Siegel space, `j(M, Ω)ᵀ R_M(Ω) = 1`. -/
theorem transpose_siegelFactor_mul_siegelFiberMap {M : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ}
    {Ω : Matrix (Fin g) (Fin g) ℂ} (hM : M ∈ symplecticGroup (Fin g) ℤ)
    (hΩ : Ω ∈ SiegelUpperHalfSpace g) : (siegelFactor M Ω)ᵀ * siegelFiberMap M Ω = 1 :=
  transpose_siegelFactor_mul_siegelFiberMap_of_isUnit (isUnit_det_siegelFactor hM hΩ)

/-- For symplectic `M` and `Ω` in the Siegel space, the fibre map sends `(A Ω + B)ᵀ` to
`(M · Ω)ᵀ = M · Ω`. -/
theorem siegelFiberMap_mul_transpose_siegelNumerator
    {M : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ} {Ω : Matrix (Fin g) (Fin g) ℂ}
    (hM : M ∈ symplecticGroup (Fin g) ℤ) (hΩ : Ω ∈ SiegelUpperHalfSpace g) :
    siegelFiberMap M Ω * (siegelNumerator M Ω)ᵀ = siegelAction M Ω := by
  rw [← transpose_siegelAction hM hΩ, siegelAction_def, transpose_mul, siegelFiberMap_def]

/-- **The period matrix times `Mᵀ`.** For a symmetric `Ω` and an integral block matrix
`M = [[A, B], [C, D]]`, `[Ω 1] Mᵀ = [(A Ω + B)ᵀ (C Ω + D)ᵀ]`. -/
theorem siegelPeriodMatrix_mul_transpose (M : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ)
    {Ω : Matrix (Fin g) (Fin g) ℂ} (hΩ : Ωᵀ = Ω) :
    siegelPeriodMatrix Ω * (M.map ((↑) : ℤ → ℂ))ᵀ =
      fromCols (siegelNumerator M Ω)ᵀ (siegelFactor M Ω)ᵀ := by
  conv_lhs => rw [← fromBlocks_toBlocks (M.map ((↑) : ℤ → ℂ))]
  simp only [siegelPeriodMatrix_def, siegelNumerator_def, siegelFactor_def, fromBlocks_transpose,
    fromCols_mul_fromBlocks, transpose_add, transpose_mul, hΩ, Matrix.one_mul]

/-- **Period equivariance, matrix form with `Mᵀ`.** For symplectic `M` and `Ω` in the Siegel space,
`R_M(Ω) Π_Ω Mᵀ = Π_{M · Ω}`. -/
theorem siegelFiberMap_mul_siegelPeriodMatrix_mul_transpose
    {M : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ} {Ω : Matrix (Fin g) (Fin g) ℂ}
    (hM : M ∈ symplecticGroup (Fin g) ℤ) (hΩ : Ω ∈ SiegelUpperHalfSpace g) :
    siegelFiberMap M Ω * siegelPeriodMatrix Ω * (M.map ((↑) : ℤ → ℂ))ᵀ =
      siegelPeriodMatrix (siegelAction M Ω) := by
  -- `R_M(Ω) = j(M, Ω)⁻ᵀ` cancels `j(M, Ω)ᵀ`, and turns `(A Ω + B)ᵀ` into `(M · Ω)ᵀ = M · Ω`.
  rw [Matrix.mul_assoc, siegelPeriodMatrix_mul_transpose M (SiegelUpperHalfSpace.transpose_eq hΩ),
    mul_fromCols, siegelFiberMap_mul_transpose_siegelFactor hM hΩ,
    siegelFiberMap_mul_transpose_siegelNumerator hM hΩ, siegelPeriodMatrix_def]

/-- **Period equivariance**, matrix form: for symplectic `M` and `Ω` in the Siegel space,
`R_M(Ω) Π_Ω = Π_{M · Ω} ρ(M)` with `ρ(M) = M⁻ᵀ`. -/
theorem siegelFiberMap_mul_siegelPeriodMatrix {M : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ}
    {Ω : Matrix (Fin g) (Fin g) ℂ} (hM : M ∈ symplecticGroup (Fin g) ℤ)
    (hΩ : Ω ∈ SiegelUpperHalfSpace g) :
    siegelFiberMap M Ω * siegelPeriodMatrix Ω =
      siegelPeriodMatrix (siegelAction M Ω) * (siegelLatticeMap M).map ((↑) : ℤ → ℂ) := by
  rw [← siegelFiberMap_mul_siegelPeriodMatrix_mul_transpose hM hΩ, Matrix.mul_assoc,
    ← transpose_map, ← Matrix.map_mul_intCast,
    transpose_mul_siegelLatticeMap (SymplecticGroup.symplectic_det hM),
    Matrix.map_one _ Int.cast_zero Int.cast_one, Matrix.mul_one]

/-- **Period equivariance** `R_M(Ω) Π_Ω(v) = Π_{M · Ω}(M⁻ᵀ v)` for symplectic `M`, `Ω` in the
Siegel space and a lattice vector `v ∈ ℤ^{2g}`. -/
theorem siegelFiberMap_mulVec_siegelPeriodMatrix_mulVec
    {M : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ} {Ω : Matrix (Fin g) (Fin g) ℂ}
    (hM : M ∈ symplecticGroup (Fin g) ℤ) (hΩ : Ω ∈ SiegelUpperHalfSpace g)
    (v : Fin g ⊕ Fin g → ℤ) :
    siegelFiberMap M Ω *ᵥ (siegelPeriodMatrix Ω *ᵥ ((↑) ∘ v)) =
      siegelPeriodMatrix (siegelAction M Ω) *ᵥ ((↑) ∘ (siegelLatticeMap M *ᵥ v)) := by
  rw [mulVec_mulVec, siegelFiberMap_mul_siegelPeriodMatrix hM hΩ, ← mulVec_mulVec]
  congr 1
  funext i
  simpa using (RingHom.map_mulVec (Int.castRingHom ℂ) (siegelLatticeMap M) v i).symm

end TauCeti
