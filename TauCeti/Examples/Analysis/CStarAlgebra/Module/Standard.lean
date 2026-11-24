/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.l2Space
public import TauCeti.Analysis.CStarAlgebra.CompactOperator
public import TauCeti.Analysis.CStarAlgebra.Module.Standard
import Mathlib.Analysis.PSeries
import TauCeti.Analysis.Normed.Lp.Diagonal.Positive

/-!
# Strictness of the Banach `ℓ²` inclusion into `StandardHilbertModule K(ℓ²(ℕ, ℂ))`

For a C⋆-algebra `A`, the Banach `ℓ²` space `lp (fun _ : ℕ ↦ A) 2` of sequences whose squared
coordinate norms are summable (`Summable (fun n ↦ ‖x n‖ ^ 2)`) includes contractively and
injectively with dense range into `TauCeti.StandardHilbertModule A` via
`TauCeti.HilbertDirectSum.ofLp`. Following Lance (*Hilbert C⋆-Modules*, Chapter 1, p. 7), this
file shows that the inclusion is not surjective in general: for the nonunital C⋆-algebra
`TauCeti.compactOperatorStarSubalgebra ℂ ℓ^2(ℕ, ℂ)` of compact operators on `ℓ²(ℕ, ℂ)`, the
sequence `a n = (√(n + 1))⁻¹ • P_n` of scaled rank-one coordinate projections satisfies
`∑' n, star (a n) * a n = diag((n + 1)⁻¹)` unconditionally in operator norm, yet
`∑ n, ‖a n‖ ^ 2 = ∑ n, (n + 1)⁻¹` diverges.

## Main declarations

* `TauCeti.StandardHilbertModule.exists_notMem_range_ofLp_compactOperator`: existence of an element
  of `StandardHilbertModule K(ℓ²(ℕ, ℂ))` outside `Set.range (HilbertDirectSum.ofLp _ _)`.
* `TauCeti.StandardHilbertModule.not_surjective_ofLp_compactOperator`: non-surjectivity of
  `HilbertDirectSum.ofLp` on `K(ℓ²(ℕ, ℂ))`.

## References

* E. Christopher Lance, *Hilbert C⋆-Modules: A Toolkit for Operator Algebraists*, Chapter 1,
  pp. 6–7.
* Iain Raeburn and Dana P. Williams, *Morita Equivalence and Continuous-Trace C⋆-Algebras*,
  Example 2.14.
-/

public section

noncomputable section

open Filter Topology MulOpposite
open scoped lp ENNReal NNReal

namespace TauCeti.StandardHilbertModule

private theorem antitone_inv_add_one :
    Antitone (fun n : ℕ ↦ (⟨((n : ℝ) + 1)⁻¹, by positivity⟩ : ℝ≥0)) := fun m n hmn ↦
  Subtype.mk_le_mk.mpr <| inv_anti₀ (by positivity) (by exact_mod_cast Nat.add_le_add_right hmn 1)

private abbrev harmonicDiag : ℓ^∞(ℕ, ℂ) :=
  lp.ofAntitone ℂ antitone_inv_add_one

private theorem tendsto_norm_harmonicDiag :
    Tendsto (fun n : ℕ ↦ ‖harmonicDiag n‖) cofinite (𝓝 0) := by
  rw [Nat.cofinite_eq_atTop]
  refine tendsto_one_div_add_atTop_nhds_zero_nat.congr fun n ↦ ?_
  rw [one_div]
  exact (lp.norm_ofAntitone_apply ℂ antitone_inv_add_one n).symm

private def harmonicCoord (n : ℕ) :
    TauCeti.compactOperatorStarSubalgebra ℂ ℓ^2(ℕ, ℂ) :=
  ⟨lp.diagonalCLM (p := 2) (lp.single ∞ n (((√((n : ℝ) + 1))⁻¹ : ℝ) : ℂ)),
    TauCeti.mem_compactOperatorStarSubalgebra_iff.mpr <|
      lp.isCompactOperator_diagonalCLM _ <| tendsto_nhds_of_eventually_eq <|
        eventually_cofinite.mpr <| (Set.finite_singleton n).subset fun i hi ↦ by
          by_contra hne
          rw [Set.mem_singleton_iff] at hne
          exact hi (by simp [hne])⟩

@[simp]
private theorem coe_harmonicCoord (n : ℕ) :
    (harmonicCoord n : ℓ^2(ℕ, ℂ) →L[ℂ] ℓ^2(ℕ, ℂ)) =
      lp.diagonalCLM (p := 2) (lp.single ∞ n (((√((n : ℝ) + 1))⁻¹ : ℝ) : ℂ)) := (rfl)

private theorem star_mul_self_harmonicCoord (n : ℕ) :
    ((star (harmonicCoord n) * harmonicCoord n :
        TauCeti.compactOperatorStarSubalgebra ℂ ℓ^2(ℕ, ℂ)) :
      ℓ^2(ℕ, ℂ) →L[ℂ] ℓ^2(ℕ, ℂ)) =
      lp.diagonalCLM (p := 2) (lp.single ∞ n (harmonicDiag n)) := by
  set e : ℓ^∞(ℕ, ℂ) := lp.single ∞ n (((√((n : ℝ) + 1))⁻¹ : ℝ) : ℂ) with ← he
  have hself : IsSelfAdjoint (lp.diagonalCLM (p := 2) e) :=
    (lp.isSelfAdjoint_diagonalCLM_iff e).mpr fun i ↦ by
      by_cases hi : i = n
      · subst i; simp [e]
      · simp [e, Pi.single_eq_of_ne hi]
  have he_sq : e * e = lp.single ∞ n (harmonicDiag n) := by
    refine lp.ext (funext fun i ↦ ?_)
    have hmul : (e * e) i = e i * e i := congrFun (lp.infty_coeFn_mul e e) i
    rw [hmul]
    by_cases hi : i = n
    · subst i
      have hpos : 0 ≤ (n : ℝ) + 1 := by positivity
      simp only [e, lp.single_apply_self, ← Complex.ofReal_mul]
      rw [← mul_inv, Real.mul_self_sqrt hpos]
      exact (lp.ofAntitone_apply ℂ antitone_inv_add_one n).symm
    · simp [e, Pi.single_eq_of_ne hi]
  simp only [MulMemClass.coe_mul, StarMemClass.coe_star, coe_harmonicCoord, he, hself.star_eq,
    ContinuousLinearMap.mul_def, ← lp.diagonalCLM_mul, he_sq]

private theorem hasSum_star_mul_self_harmonicCoord :
    HasSum (fun n ↦ star (harmonicCoord n) * harmonicCoord n)
      (⟨lp.diagonalCLM (p := 2) harmonicDiag,
        TauCeti.mem_compactOperatorStarSubalgebra_iff.mpr
          (lp.isCompactOperator_diagonalCLM harmonicDiag tendsto_norm_harmonicDiag)⟩ :
        TauCeti.compactOperatorStarSubalgebra ℂ ℓ^2(ℕ, ℂ)) := by
  rw [HasSum, SummationFilter.unconditional_filter, tendsto_subtype_rng]
  refine (lp.tendsto_diagonalTruncation (p := 2) harmonicDiag tendsto_norm_harmonicDiag).congr'
    (Eventually.of_forall fun s ↦ ?_)
  simp [lp.diagonalTruncation_eq_diagonalCLM, star_mul_self_harmonicCoord]

private theorem norm_harmonicCoord_sq (n : ℕ) :
    ‖harmonicCoord n‖ ^ 2 = 1 / ((n + 1 : ℕ) : ℝ) := by
  simp [lp.norm_single ENNReal.zero_lt_top, Real.sq_sqrt (x := (n : ℝ) + 1) (by positivity),
    one_div]

/-- For the C⋆-algebra `K(ℓ²(ℕ, ℂ))` of compact operators on `ℓ²(ℕ, ℂ)`, there exists a vector in
`StandardHilbertModule K(ℓ²(ℕ, ℂ))` outside the range of the Banach `ℓ²` inclusion
`HilbertDirectSum.ofLp`. -/
theorem exists_notMem_range_ofLp_compactOperator :
    ∃ x : StandardHilbertModule
        (TauCeti.compactOperatorStarSubalgebra ℂ ℓ^2(ℕ, ℂ)),
      x ∉ Set.range
        (HilbertDirectSum.ofLp
          (TauCeti.compactOperatorStarSubalgebra ℂ ℓ^2(ℕ, ℂ))ᵐᵒᵖ
          (fun _ : ℕ ↦ TauCeti.compactOperatorStarSubalgebra ℂ ℓ^2(ℕ, ℂ))) := by
  refine ⟨mkOfSummable harmonicCoord hasSum_star_mul_self_harmonicCoord.summable, ?_⟩
  rw [HilbertDirectSum.mem_range_ofLp_iff, memℓp_two_iff]
  intro hmem
  simp_rw [mkOfSummable_apply, norm_harmonicCoord_sq] at hmem
  exact Real.not_summable_one_div_natCast ((summable_nat_add_iff 1).mp hmem)

/-- The contractive injective inclusion with dense range
`lp (fun _ : ℕ ↦ K(ℓ²)) 2 →L[ℂ] StandardHilbertModule K(ℓ²)` is not surjective. -/
theorem not_surjective_ofLp_compactOperator :
    ¬ Function.Surjective
      (HilbertDirectSum.ofLp
        (TauCeti.compactOperatorStarSubalgebra ℂ ℓ^2(ℕ, ℂ))ᵐᵒᵖ
        (fun _ : ℕ ↦ TauCeti.compactOperatorStarSubalgebra ℂ ℓ^2(ℕ, ℂ))) := by
  intro hsurj
  obtain ⟨x, hx⟩ := exists_notMem_range_ofLp_compactOperator
  exact hx (hsurj x)

end TauCeti.StandardHilbertModule

end
