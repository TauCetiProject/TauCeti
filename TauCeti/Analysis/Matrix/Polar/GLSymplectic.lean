/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.Polar.Deformation
public import TauCeti.Analysis.Matrix.Polar.Symplectic
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Symplectic.Sum

/-!
# The polar factors of an invertible real symplectic matrix

By `TauCeti/Analysis/Matrix/Polar/Symplectic.lean`, both polar factors of a real symplectic matrix
`A = P U` are symplectic. This file packages that fact for the symplectic subgroup
`TauCeti.GLSymplectic` of the general linear group: the polar deformation `P ^ (1 - t) U` of
`Matrix.GeneralLinearGroup.polarDeformation` stays in `TauCeti.GLSymplectic`, and the orthogonal
polar factor is a continuous map from `TauCeti.GLSymplectic` to its orthogonal elements, which is
the identity on them and turns direct sums into direct sums.

## Main definitions

* `TauCeti.GLSymplectic.polarUnitary`: the orthogonal polar factor of a symplectic matrix.

## Main results

* `TauCeti.GLSymplectic.polarDeformation_mem`: the polar deformation stays symplectic.
* `TauCeti.GLSymplectic.polarUnitary_inclusion`: an orthogonal symplectic matrix is its own
  orthogonal polar factor.
* `TauCeti.GLSymplectic.continuous_polarUnitary`: the orthogonal polar factor is continuous.
* `TauCeti.GLSymplectic.coe_polarUnitary_sum`: the orthogonal polar factor of a direct sum is the
  direct sum of the orthogonal polar factors.

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
      (mem_iff_mem_symplecticGroup.1 A.2)), by simp [Units.unitary_eq]⟩

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
    simpa [mem_unitarySubgroup_iff, Units.unitary_eq] using (Subgroup.mem_inf.1 U.2).2
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
  exact (h.comp continuous_subtype_val).subtype_mk _

/-- The orthogonal polar factor of a symplectic matrix depends continuously on it, as a
symplectic matrix. -/
theorem continuous_inclusion_polarUnitary :
    Continuous fun A : GLSymplectic n ℝ ↦ Subgroup.inclusion inf_le_left (polarUnitary A) :=
  continuous_induced_rng.2 ((continuous_subtype_val.comp continuous_polarUnitary).congr fun _ ↦
    (Subgroup.coe_inclusion _ _).symm)

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
    symplecticSum_mem_unitaryGroup (Units.polarUnitary _).2 (Units.polarUnitary _).2
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

end TauCeti.GLSymplectic
