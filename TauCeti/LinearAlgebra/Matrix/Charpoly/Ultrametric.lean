/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
public import TauCeti.Analysis.Normed.Field.UnitsBall
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import TauCeti.Algebra.Polynomial.Eval.Nonarchimedean

/-!
# Eigenvalues of integral matrices over an ultrametric normed field

Let `K` be an ultrametric normed field and `A` a square matrix whose entries lie in the closed
unit ball of `K`. The characteristic polynomial of `A` is monic with coefficients in the closed
unit ball, so its roots, the eigenvalues of `A` in `K`, lie in the closed unit ball as well. For a
scalar `c`, the eigenvalues of `1 + c • A` are `1 + c μ` for the eigenvalues `μ` of `A`, so they lie
within distance `‖c‖` of one.

This is the eigenvalue bound for congruence matrices: over `ℚ_[p]` or an algebraic closure of it,
every eigenvalue `ν` of a matrix in `1 + p ^ a M_n(ℤ_p)` satisfies `|ν - 1| ≤ p ^ (-a)`. When
`‖c‖ ^ (p - 1) < ‖p‖ < 1`, as for `c = p ^ a` with `p ≥ 3, a ≥ 1` or `p = 2, a ≥ 2` over `ℚ_[p]`,
all eigenvalues of `1 + c • A` lie in the torsion-free group `TauCeti.unitsBallSubgroup` of units
near one, and so they generate a torsion-free group. This is the step of Borel's congruence
argument that makes congruence subgroups at one prime neat (see Milne, *Introduction to Shimura
varieties*, §3, Proposition 3.5).

## Main results

* `Matrix.norm_le_one_of_mem_spectrum`: eigenvalues of a matrix with entries in the closed unit
  ball lie in the closed unit ball.
* `Matrix.norm_sub_one_le_of_mem_spectrum_one_add_smul`: every eigenvalue `ν` of `1 + c • A`
  satisfies `‖ν - 1‖ ≤ ‖c‖`.
* `Matrix.isMulTorsionFree_closure_spectrum_one_add_smul`: if `‖c‖ ^ (p - 1) < ‖p‖ < 1` for a
  prime `p`, the eigenvalues of `1 + c • A` generate a torsion-free subgroup of `Kˣ`.
-/

public section

namespace Matrix

variable {n K : Type*} [Fintype n] [DecidableEq n] [NormedField K] [IsUltrametricDist K]
  {A : Matrix n n K}

/-- The eigenvalues of a matrix with entries in the closed unit ball of an ultrametric normed field
lie in the closed unit ball. -/
theorem norm_le_one_of_mem_spectrum (hA : ∀ i j, ‖A i j‖ ≤ 1) {μ : K} (hμ : μ ∈ spectrum K A) :
    ‖μ‖ ≤ 1 := by
  -- `μ` is a root of the characteristic polynomial of `A` viewed over the closed unit ball, which
  -- is monic, so `μ` is integral over the closed unit ball.
  let B : Matrix n n (Subring.unitClosedBall K) :=
    of fun i j ↦ ⟨A i j, Subring.mem_unitClosedBall.2 (hA i j)⟩
  have hB : B.map (Subring.unitClosedBall K).subtype = A := by
    ext i j
    simp [B]
  have hint : IsIntegral (Subring.unitClosedBall K) μ := by
    refine ⟨B.charpoly, B.charpoly_monic, ?_⟩
    rw [← Polynomial.eval_map, Algebra.algebraMap_ofSubring, ← charpoly_map, hB]
    exact mem_spectrum_iff_isRoot_charpoly.1 hμ
  exact IsUltrametricDist.isNonarchimedean_norm.apply_le_one_of_isIntegral_of_isPowMul norm_nonneg
    norm_mul_le (fun x m _ ↦ norm_pow x m) (fun r ↦ Subring.mem_unitClosedBall.1 r.property) hint

/-- **Eigenvalues of congruence matrices.** If the entries of `A` lie in the closed unit ball of
an ultrametric normed field, every eigenvalue `ν` of `1 + c • A` satisfies `‖ν - 1‖ ≤ ‖c‖`. -/
theorem norm_sub_one_le_of_mem_spectrum_one_add_smul (hA : ∀ i j, ‖A i j‖ ≤ 1) {c ν : K}
    (hν : ν ∈ spectrum K (1 + c • A)) : ‖ν - 1‖ ≤ ‖c‖ := by
  have h : ν - 1 ∈ spectrum K (c • A) := by
    rwa [← spectrum.add_mem_add_iff (s := 1), sub_add_cancel, map_one]
  rcases eq_or_ne c 0 with rfl | hc
  · rw [zero_smul, spectrum.mem_iff, sub_zero] at h
    rw [norm_zero, norm_le_zero_iff, sub_eq_zero]
    by_contra hne
    exact h ((sub_ne_zero.2 hne).isUnit.map _)
  · have hμ : c⁻¹ * (ν - 1) ∈ spectrum K A := by
      refine spectrum.smul_mem_smul_iff (r := Units.mk0 c hc).1 ?_
      simpa [Units.smul_def, mul_inv_cancel_left₀ hc] using h
    calc ‖ν - 1‖ = ‖c‖ * ‖c⁻¹ * (ν - 1)‖ := by rw [← norm_mul, mul_inv_cancel_left₀ hc]
      _ ≤ ‖c‖ := mul_le_of_le_one_right (norm_nonneg _) (norm_le_one_of_mem_spectrum hA hμ)

/-- **Congruence matrices have torsion-free eigenvalue groups.** Let `p` be a prime of norm less
than one in an ultrametric normed field `K`, let `A` have entries in the closed unit ball, and let
`‖c‖ ^ (p - 1) < ‖p‖`. Then the units of `K` that are eigenvalues of `1 + c • A` generate a
torsion-free subgroup of `Kˣ`. Over `ℚ_[p]` and its extensions this applies to `c = p ^ a` with
`a ≥ 1` for odd `p` and with `a ≥ 2` for `p = 2`. -/
theorem isMulTorsionFree_closure_spectrum_one_add_smul {p : ℕ} (hp : p.Prime)
    (hpK : ‖(p : K)‖ < 1) (hA : ∀ i j, ‖A i j‖ ≤ 1) {c : K} (hc : ‖c‖ ^ (p - 1) < ‖(p : K)‖) :
    IsMulTorsionFree (Subgroup.closure {u : Kˣ | (u : K) ∈ spectrum K (1 + c • A)}) := by
  -- The radius `r = ‖p‖ ^ (1 / (p - 1))` satisfies `‖c‖ < r ≤ 1` and `r ^ (p - 1) = ‖p‖`.
  have hp₁ : p - 1 ≠ 0 := Nat.sub_ne_zero_of_lt hp.one_lt
  set r := ‖(p : K)‖ ^ ((p - 1 : ℕ) : ℝ)⁻¹
  have hr : r ^ (p - 1) = ‖(p : K)‖ := Real.rpow_inv_natCast_pow (norm_nonneg _) hp₁
  have hcr : ‖c‖ < r := (pow_lt_pow_iff_left₀ (norm_nonneg _)
    (Real.rpow_nonneg (norm_nonneg _) _) hp₁).1 (by rwa [hr])
  have hr₀ : 0 < r := (norm_nonneg c).trans_lt hcr
  have hr₁ : r ≤ 1 := Real.rpow_le_one (norm_nonneg _) hpK.le (by positivity)
  have hle : Subgroup.closure {u : Kˣ | (u : K) ∈ spectrum K (1 + c • A)} ≤
      TauCeti.unitsBallSubgroup K hr₀ hr₁ :=
    (Subgroup.closure_le _).2 fun u hu ↦ TauCeti.mem_unitsBallSubgroup.2
      ((norm_sub_one_le_of_mem_spectrum_one_add_smul hA hu).trans_lt hcr)
  have := TauCeti.isMulTorsionFree_unitsBallSubgroup hp hpK hr₀ hr₁ hr.le
  exact Function.Injective.isMulTorsionFree (Subgroup.inclusion hle)
    (Subgroup.inclusion_injective hle)

end Matrix
