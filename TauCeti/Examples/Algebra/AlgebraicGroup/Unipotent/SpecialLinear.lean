/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.SpecialLinear.StandardComodule
public import TauCeti.Algebra.AlgebraicGroup.Unipotent.Comodule

/-!
# Check: the special linear group is not unipotent

For `n ≥ 2`, `SL_n` over any field `k` is not unipotent in the comodule sense
`TauCeti.unipotentCommHopfAlgProperty`. Its standard representation `kⁿ` is simple
(`TauCeti.SpecialLinear.instIsSimpleOrderSubcomodule`), so a nonzero fixed vector would make every
vector fixed, hence fixed by every `k`-point; but the transvection `1 + E₀₁` is a `k`-point of
`SL_n` moving `e₁`. This holds over every field, including `𝔽₂`.

Over `ℚ`, the point `diag(2, 1/2)` of `SL₂` (Mathlib's `Matrix.SpecialLinearGroup.diag2`)
satisfies that `diag(2, 1/2) - 1` is invertible
(`TauCeti.Examples.UnipotentSpecialLinear.isUnit_diag_two_half_sub_one`).
-/

public section

namespace TauCeti.Examples.UnipotentSpecialLinear

open TauCeti Comodule

universe u

variable (k : Type u) [Field k]

attribute [local instance] SpecialLinear.standardComodule

/-- **`SL_n` is not unipotent** for `n ≥ 2`, over every field. -/
theorem not_unipotent_specialLinear {n : ℕ} (hn : 2 ≤ n) :
    ¬ unipotentCommHopfAlgProperty k (SpecialLinear.coordinateHopfAlgebra k n) := by
  intro hH
  have : NeZero n := ⟨by omega⟩
  -- The fixed subcomodule of the simple standard comodule is nonzero, hence everything.
  have htop : fixedSubcomodule k (SpecialLinear.coordinateHopfAlgebra k n) (Fin n → k) = ⊤ :=
    (eq_bot_or_eq_top _).resolve_left (hasNonzeroFixedVector_iff_fixedSubcomodule_ne_bot.mp
      (unipotentCommHopfAlgProperty.hasNonzeroFixedVector
        (H := SpecialLinear.coordinateHopfAlgebra k n) hH))
  -- The transvection `1 + E₀₁` as a `k`-point of `SL_n`.
  let i : Fin n := ⟨0, by omega⟩
  let j : Fin n := ⟨1, by omega⟩
  have hij : i ≠ j := by simp [i, j, Fin.ext_iff]
  let t := Matrix.SpecialLinearGroup.transvection hij (1 : k)
  let g := (SpecialLinear.pointsMulEquiv (R := k) (A := k) n).symm t
  have hfix := basePointsRepresentation_eq_of_coact_eq_tmul_one (R := k)
    (H := SpecialLinear.coordinateHopfAlgebra k n) (Pi.single j 1 : Fin n → k)
    (mem_fixedSubcomodule.mp (htop ▸ Subcomodule.mem_top _)) g
  rw [SpecialLinear.basePointsRepresentation_eq_mulVec, MulEquiv.apply_symm_apply,
    ← Matrix.smul_eq_mulVec, ← Matrix.SpecialLinearGroup.smul_def,
    Matrix.SpecialLinearGroup.transvection_smul_single_snd] at hfix
  simpa [hij] using congrFun hfix i

/-- For the point `diag(2, 1/2)` of `SL₂(ℚ)`, the matrix `diag(2, 1/2) - 1` is invertible. -/
theorem isUnit_diag_two_half_sub_one :
    IsUnit ((Matrix.SpecialLinearGroup.diag2 (2 : ℚ) two_ne_zero : Matrix (Fin 2) (Fin 2) ℚ) -
      1) := by
  rw [Matrix.SpecialLinearGroup.diag2_coe, Matrix.isUnit_iff_isUnit_det, ← Matrix.diagonal_one,
    Matrix.diagonal_sub, Matrix.det_diagonal]
  norm_num [Fin.prod_univ_two]

/-- `SL₂` is not unipotent over `ℚ`. -/
example : ¬ unipotentCommHopfAlgProperty ℚ (SpecialLinear.coordinateHopfAlgebra ℚ 2) :=
  not_unipotent_specialLinear ℚ le_rfl

end TauCeti.Examples.UnipotentSpecialLinear
