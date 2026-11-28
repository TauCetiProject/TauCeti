/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.SpecialLinear.Derived
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
(`TauCeti.Examples.UnipotentSpecialLinear.isUnit_diag_two_half_sub_one`), so it fixes no nonzero
vector of the standard representation `ℚ²`
(`TauCeti.Examples.UnipotentSpecialLinear.eq_zero_of_diag_two_half_mulVec_eq`); an `example`
below uses this for a second proof that `SL₂` is not unipotent over `ℚ`.

The character test for unipotence is one-way: a connected unipotent group has no nontrivial
character, but `SL₂` has none either (`TauCeti.SpecialLinear.groupLike_eq_one`, from the
derived subgroup), and it is not unipotent
(`TauCeti.Examples.UnipotentSpecialLinear.not_unipotent_specialLinear`); an `example` below
records the two facts together.
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
    (fixedSubcomodule_eq_top_iff.mp htop _) g
  rw [SpecialLinear.basePointsRepresentation_eq_mulVec] at hfix
  simpa [g, t, Matrix.SpecialLinearGroup.transvection_coe, Matrix.add_mulVec, hij] using
    congrFun hfix i

/-- For the point `diag(2, 1/2)` of `SL₂(ℚ)`, the matrix `diag(2, 1/2) - 1` is invertible. -/
theorem isUnit_diag_two_half_sub_one :
    IsUnit ((Matrix.SpecialLinearGroup.diag2 (2 : ℚ) two_ne_zero : Matrix (Fin 2) (Fin 2) ℚ) -
      1) := by
  rw [Matrix.isUnit_iff_isUnit_det]
  norm_num [Matrix.SpecialLinearGroup.diag2_coe', Matrix.det_fin_two]

/-- The point `diag(2, 1/2)` of `SL₂(ℚ)` fixes no nonzero vector of `ℚ²`. -/
theorem eq_zero_of_diag_two_half_mulVec_eq {v : Fin 2 → ℚ}
    (hv : (Matrix.SpecialLinearGroup.diag2 (2 : ℚ) two_ne_zero :
      Matrix (Fin 2) (Fin 2) ℚ).mulVec v = v) : v = 0 := by
  have h : ((Matrix.SpecialLinearGroup.diag2 (2 : ℚ) two_ne_zero : Matrix (Fin 2) (Fin 2) ℚ) -
      1).mulVec v = 0 := by
    rw [Matrix.sub_mulVec, hv, Matrix.one_mulVec, sub_self]
  exact (Matrix.mulVec_injective_iff_isUnit.mpr isUnit_diag_two_half_sub_one)
    (h.trans (Matrix.mulVec_zero _).symm)

/-- **`SL₂` is not unipotent over `ℚ`, through the point `diag(2, 1/2)`**: a unipotent group would
fix a nonzero vector of the standard representation `ℚ²`, but `diag(2, 1/2)` fixes none. -/
example :
    ¬ unipotentCommHopfAlgProperty ℚ (SpecialLinear.coordinateHopfAlgebra ℚ 2) := by
  intro hH
  obtain ⟨v, hv0, hv⟩ := hasNonzeroFixedVector_iff.mp
    (unipotentCommHopfAlgProperty.hasNonzeroFixedVector
      (H := SpecialLinear.coordinateHopfAlgebra ℚ 2) (M := Fin 2 → ℚ) hH)
  let g := (SpecialLinear.pointsMulEquiv (R := ℚ) (A := ℚ) 2).symm
    (Matrix.SpecialLinearGroup.diag2 (2 : ℚ) two_ne_zero)
  have hfix := basePointsRepresentation_eq_of_coact_eq_tmul_one (R := ℚ)
    (H := SpecialLinear.coordinateHopfAlgebra ℚ 2) v hv g
  rw [SpecialLinear.basePointsRepresentation_eq_mulVec] at hfix
  exact hv0 (eq_zero_of_diag_two_half_mulVec_eq (by simpa [g] using hfix))

/-- **The character test for unipotence is one-way.** Over every field, `SL₂` has no nontrivial
character (every group-like element of its coordinate ring is `1`), yet it is not unipotent. -/
example :
    (∀ x : GroupLike k (SpecialLinear.coordinateHopfAlgebra k 2), x = 1) ∧
      ¬ unipotentCommHopfAlgProperty k (SpecialLinear.coordinateHopfAlgebra k 2) :=
  ⟨SpecialLinear.groupLike_eq_one k 2, not_unipotent_specialLinear k le_rfl⟩

end TauCeti.Examples.UnipotentSpecialLinear
