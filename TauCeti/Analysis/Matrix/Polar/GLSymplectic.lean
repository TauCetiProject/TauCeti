/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.Polar.Deformation
public import TauCeti.Analysis.Matrix.Polar.Symplectic
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Symplectic.Levi
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Symplectic.Sum

/-!
# The polar factors of an invertible real symplectic matrix

By `TauCeti/Analysis/Matrix/Polar/Symplectic.lean`, both polar factors of a real symplectic matrix
`A = P U` are symplectic. This file packages that fact for the symplectic subgroup
`TauCeti.GLSymplectic` of the general linear group: the polar deformation `P ^ (1 - t) U` of
`Matrix.GeneralLinearGroup.polarDeformation` stays in `TauCeti.GLSymplectic`, and the orthogonal
polar factor is a continuous map from `TauCeti.GLSymplectic` to its orthogonal elements, which is
the identity on them, turns direct sums into direct sums, and sends the Levi element
`diag(A, A⁻ᵀ)` to `diag(U, U)` for the orthogonal polar factor `U` of `A`.

## Main definitions

* `TauCeti.GLSymplectic.polarUnitary`: the orthogonal polar factor of a symplectic matrix.
* `TauCeti.GLSymplectic.polarHomotopy`: the polar deformation, as a homotopy through symplectic
  matrices from the identity to the orthogonal polar factor.

## Main results

* `TauCeti.GLSymplectic.polarDeformation_mem`: the polar deformation stays symplectic.
* `TauCeti.GLSymplectic.polarUnitary_inclusion`: an orthogonal symplectic matrix is its own
  orthogonal polar factor.
* `TauCeti.GLSymplectic.continuous_polarUnitary`: the orthogonal polar factor is continuous.
* `TauCeti.GLSymplectic.coe_polarUnitary_sum`: the orthogonal polar factor of a direct sum is the
  direct sum of the orthogonal polar factors.
* `TauCeti.GLSymplectic.coe_polarUnitary_leviHom`: the orthogonal polar factor of
  `diag(A, A⁻ᵀ)` is `diag(U, U)`, for the orthogonal polar factor `U` of `A`.

## References

* Dusa McDuff and Dietmar Salamon, *Introduction to Symplectic Topology*, third edition, Oxford
  Graduate Texts in Mathematics 27, Oxford University Press, 2017, Section 2.2 (Proposition 2.2.11
  for the polar decomposition of symplectic matrices).
-/

public section

open Matrix Matrix.GeneralLinearGroup
open scoped MatrixOrder unitInterval

namespace TauCeti.GLSymplectic

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The polar deformation `P ^ (1 - t) U` of a symplectic matrix `A = P U` stays symplectic at
every real time. -/
theorem polarDeformation_mem {A : GL (n ⊕ n) ℝ} (hA : A ∈ GLSymplectic n ℝ) (t : ℝ) :
    polarDeformation A t ∈ GLSymplectic n ℝ := by
  rw [mem_iff_mem_symplecticGroup] at hA ⊢
  rw [coe_polarDeformation]
  exact Submonoid.mul_mem _ (SymplecticGroup.rpow_mem
    (nonneg_iff_posSemidef.1 (CFC.sqrt_nonneg _)) (SymplecticGroup.sqrt_mul_star_mem hA) _)
    (SymplecticGroup.polarUnitary_mem hA)

/-- The orthogonal polar factor `U` of a symplectic matrix `A = P U`, as an orthogonal symplectic
matrix. -/
noncomputable def polarUnitary (A : GLSymplectic n ℝ) :
    ↥(GLSymplectic n ℝ ⊓ unitarySubgroup (GL (n ⊕ n) ℝ)) :=
  ⟨Unitary.toUnits (Units.polarUnitary (A : GL (n ⊕ n) ℝ)),
    mem_iff_mem_symplecticGroup.2 (SymplecticGroup.polarUnitary_mem
      (mem_iff_mem_symplecticGroup.1 A.property)), by simp [Units.unitary_eq]⟩

/-- The orthogonal polar factor, as a matrix, is the unitary polar factor `Units.polarUnitary`. -/
@[simp]
theorem coe_polarUnitary (A : GLSymplectic n ℝ) :
    ((polarUnitary A : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ) =
      Units.polarUnitary (A : GL (n ⊕ n) ℝ) :=
  (rfl)

/-- An orthogonal symplectic matrix is its own orthogonal polar factor. -/
@[simp]
theorem polarUnitary_inclusion (U : ↥(GLSymplectic n ℝ ⊓ unitarySubgroup (GL (n ⊕ n) ℝ))) :
    polarUnitary (Subgroup.inclusion inf_le_left U) = U := by
  have hU : ((U : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ) ∈
      unitary (Matrix (n ⊕ n) (n ⊕ n) ℝ) := by
    simpa [mem_unitarySubgroup_iff, Units.unitary_eq] using (Subgroup.mem_inf.1 U.property).2
  have h := Units.polarUnitary_eq_of_mul_eq (U : GL (n ⊕ n) ℝ) zero_le_one
    (v := ⟨_, hU⟩) (one_mul _)
  refine Subtype.ext (Units.ext ?_)
  rw [coe_polarUnitary, Subgroup.coe_inclusion, h]

/-- The orthogonal polar factor depends continuously on the symplectic matrix. -/
theorem continuous_polarUnitary :
    Continuous (polarUnitary : GLSymplectic n ℝ → _) := by
  have h := (polarHomotopy (n ⊕ n) ℝ).continuous.comp
    (continuous_const.prodMk continuous_id : Continuous fun A : GL (n ⊕ n) ℝ ↦ ((1 : I), A))
  simp only [Function.comp_def, polarHomotopy_apply, Set.Icc.coe_one, polarDeformation_one] at h
  exact (h.comp continuous_subtypeVal).subtype_mk _

/-- The orthogonal polar factor of a symplectic matrix depends continuously on it, as a
symplectic matrix. -/
theorem continuous_inclusion_polarUnitary :
    Continuous fun A : GLSymplectic n ℝ ↦ Subgroup.inclusion inf_le_left (polarUnitary A) :=
  continuous_induced_rng.2 ((continuous_subtypeVal.comp continuous_polarUnitary).congr fun _ ↦
    (Subgroup.coe_inclusion _ _).symm)

/-- The **symplectic polar homotopy** `(t, A) ↦ P ^ (1 - t) U` of a symplectic matrix `A = P U`:
it contracts the positive factor through symplectic matrices, from the identity to the orthogonal
polar factor. -/
noncomputable def polarHomotopy :
    ContinuousMap.Homotopy (ContinuousMap.id (GLSymplectic n ℝ))
      ⟨fun A ↦ Subgroup.inclusion inf_le_left (polarUnitary A),
        continuous_inclusion_polarUnitary⟩ where
  toFun p := ⟨polarDeformation (p.2 : GL (n ⊕ n) ℝ) p.1, polarDeformation_mem p.2.property _⟩
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    have h := (Matrix.GeneralLinearGroup.polarHomotopy (n ⊕ n) ℝ).continuous.comp
      (continuous_fst.prodMk (continuous_subtypeVal.comp continuous_snd) :
        Continuous fun p : I × GLSymplectic n ℝ ↦ (p.1, (p.2 : GL (n ⊕ n) ℝ)))
    simpa only [Function.comp_def, polarHomotopy_apply] using h
  map_zero_left A := Subtype.ext (by simp)
  map_one_left A := Subtype.ext (Units.ext (by simp))

/-- The symplectic polar homotopy evaluates to the polar deformation. -/
@[simp]
theorem coe_polarHomotopy_apply (p : I × GLSymplectic n ℝ) :
    ((polarHomotopy p : GLSymplectic n ℝ) : GL (n ⊕ n) ℝ) =
      polarDeformation (p.2 : GL (n ⊕ n) ℝ) p.1 := by
  rfl

/-- The orthogonal polar factor of a direct sum is the direct sum of the orthogonal polar
factors. -/
theorem coe_polarUnitary_sum {m : Type*} [Fintype m] [DecidableEq m] (A : GLSymplectic n ℝ)
    (B : GLSymplectic m ℝ) :
    ((polarUnitary (sum (A, B)) : GL ((n ⊕ m) ⊕ (n ⊕ m)) ℝ) :
      Matrix ((n ⊕ m) ⊕ (n ⊕ m)) ((n ⊕ m) ⊕ (n ⊕ m)) ℝ) =
      symplecticSum ((polarUnitary A : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ)
        ((polarUnitary B : GL (m ⊕ m) ℝ) : Matrix (m ⊕ m) (m ⊕ m) ℝ) := by
  have hU : symplecticSum ((Units.polarUnitary (A : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) _ ℝ))
      (Units.polarUnitary (B : GL (m ⊕ m) ℝ) : Matrix (m ⊕ m) _ ℝ) ∈
        unitary (Matrix ((n ⊕ m) ⊕ (n ⊕ m)) ((n ⊕ m) ⊕ (n ⊕ m)) ℝ) :=
    symplecticSum_mem_unitaryGroup (Units.polarUnitary _).property (Units.polarUnitary _).property
  have hP : 0 ≤ symplecticSum
      (CFC.sqrt (((A : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ) *
        star ((A : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ)))
      (CFC.sqrt (((B : GL (m ⊕ m) ℝ) : Matrix (m ⊕ m) (m ⊕ m) ℝ) *
        star ((B : GL (m ⊕ m) ℝ) : Matrix (m ⊕ m) (m ⊕ m) ℝ))) :=
    nonneg_iff_posSemidef.2 ((nonneg_iff_posSemidef.1 (CFC.sqrt_nonneg _)).symplecticSum
      (nonneg_iff_posSemidef.1 (CFC.sqrt_nonneg _)))
  have h := Units.polarUnitary_eq_of_mul_eq (sum (A, B) : GL ((n ⊕ m) ⊕ (n ⊕ m)) ℝ) hP
    (v := ⟨_, hU⟩)
    (by rw [coe_sum, ← symplecticSum_mul, Units.sqrt_mul_star_mul_polarUnitary,
      Units.sqrt_mul_star_mul_polarUnitary])
  rw [coe_polarUnitary, coe_polarUnitary, coe_polarUnitary, h]

/-- **The polar decomposition on the Levi subgroup.** If `A = P U` is the polar decomposition of
`A`, then `diag(A, A⁻ᵀ) = diag(P, P⁻ᵀ) diag(U, U)` is that of `diag(A, A⁻ᵀ)`: its orthogonal polar
factor is `diag(U, U)`. -/
theorem coe_polarUnitary_leviHom (A : GL n ℝ) :
    ((polarUnitary (leviHom A) : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ) =
      fromBlocks (Units.polarUnitary A : Matrix n n ℝ) 0 0 (Units.polarUnitary A) := by
  set P := CFC.sqrt ((A : Matrix n n ℝ) * star (A : Matrix n n ℝ))
  set U := Units.polarUnitary A
  have hPU : P * (U : Matrix n n ℝ) = A := Units.sqrt_mul_star_mul_polarUnitary A
  have hU : (U : Matrix n n ℝ) * star (U : Matrix n n ℝ) = 1 :=
    Unitary.mul_star_self_of_mem U.property
  -- The polar decomposition of `A⁻ᵀ` is `P⁻ᵀ U`, as the entrywise conjugate of `U` is `U` over `ℝ`.
  have hAinv : (inverseTranspose A : Matrix n n ℝ) = P⁻¹ᵀ * (U : Matrix n n ℝ) := by
    rw [← Units.sqrt_mul_star_mul_polarUnitary (inverseTranspose A), sqrt_inverseTranspose,
      polarUnitary_inverseTranspose, UnitaryGroup.map_star_coe,
      show (star : ℝ → ℝ) = id from funext star_trivial, Matrix.map_id]
  have hW : fromBlocks (U : Matrix n n ℝ) 0 0 (U : Matrix n n ℝ) ∈
      unitaryGroup (n ⊕ n) ℝ := by
    rw [mem_unitaryGroup_iff, star_eq_conjTranspose, fromBlocks_conjTranspose, fromBlocks_multiply,
      ← star_eq_conjTranspose, hU]
    simp
  have hQ : 0 ≤ fromBlocks P 0 0 P⁻¹ᵀ := by
    have hP : P.PosDef := posDef_sqrt_mul_star A
    rw [nonneg_iff_posSemidef]
    let _ : Invertible P := hP.isUnit.invertible
    simpa using (PosDef.fromBlocks₁₁ (0 : Matrix n n ℝ) P⁻¹ᵀ hP).2
      (by simpa using hP.inv.transpose.posSemidef)
  rw [coe_polarUnitary, Units.polarUnitary_eq_of_mul_eq _ hQ (v := ⟨_, hW⟩) (by
    rw [coe_leviHom, fromBlocks_multiply, hPU, ← coe_inverseTranspose, hAinv]
    simp)]

end TauCeti.GLSymplectic
