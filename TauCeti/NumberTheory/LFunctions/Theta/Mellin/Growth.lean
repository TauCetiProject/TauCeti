/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LFunctions.Theta.Mellin.Pair
public import TauCeti.NumberTheory.LSeries.MellinGrowth

/-!
# Order-one and vertical-strip growth of lattice Mellin completions

For a number field `K`, a unit fundamental domain `D` of the norm-one archimedean hypersurface,
and a full `ℤ`-lattice `L` (including any ideal lattice `idealLattice K I`), both
`mellinKernel D L` and its Euclidean dual `mellinKernel D⁻¹ (mixedDual K L)` satisfy
stretched-exponential bounds around `mellinConstant K`
(`exists_norm_mellinKernel_sub_mellinConstant_le_on_Ici`). Feeding these tails into the
split-Mellin adapter of `TauCeti.NumberTheory.LSeries.MellinGrowth` supplies the finite-order and
vertical-strip growth inputs needed for Phragmén-Lindelöf convexity and Hadamard factorization of
completed partial zeta, Dedekind zeta, and Hecke L-functions built from lattice Mellin completions:
* for `(mellinKernelFEPair hD L).toWeakFEPair.Λ₀`: global `exp (C (1 + ‖s‖) log (2 + ‖s‖))`
  bounds, order at most one (`OrderLE _ 1`), uniform boundedness on every closed vertical strip,
  and polynomial `HasVerticalStripGrowth`;
* for `(mellinKernelFEPair hD L).entireΛ` and the critical-strip `s / 2`-normalized pole-cleared
  completion `mellinKernelEntireCompletion`: global logarithmic-exponential bounds,
  `OrderLE _ 1`, `IsFiniteOrder`, and `HasVerticalStripGrowth`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §5.
* H. Iwaniec and E. Kowalski, *Analytic Number Theory*, Chapter 5.
-/

public section

noncomputable section

open Asymptotics Filter MeasureTheory NumberField NumberField.InfinitePlace
  NumberField.mixedEmbedding NumberField.Units TauCeti.NumberField.mixedEmbedding Set Real
open scoped Pointwise Topology nonZeroDivisors

namespace TauCeti.LFunctions

variable {K : Type*} [Field K] [NumberField K]

/-! ### Split-Mellin growth of `mellinKernelFEPair` -/

open scoped Classical in
private theorem exists_isBigO_mellinKernelFEPair_f_sub {D : Set (realSpace K)}
    (hD : IsUnitFundamentalDomain K D) (L : Submodule ℤ (mixedSpace K)) [DiscreteTopology L]
    [IsZLattice ℝ L] :
    ∃ c > 0, ∃ α : ℝ, 0 < α ∧
      (fun u ↦ (mellinKernelFEPair hD L).f u - (mellinKernelFEPair hD L).f₀) =O[atTop]
        fun u ↦ exp (-c * u ^ α) := by
  obtain ⟨c, hc, C, -, hf⟩ := exists_norm_mellinKernel_sub_mellinConstant_le_on_Ici hD L one_pos
  refine ⟨c, hc, (Module.finrank ℚ K : ℝ)⁻¹,
    inv_pos.mpr (Nat.cast_pos.mpr (Module.finrank_pos (R := ℚ) (M := K))),
    IsBigO.of_bound C ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with u hu
  simpa only [mellinKernelFEPair_f, mellinKernelFEPair_f₀,
    indicator_of_mem (mem_Ioi.mpr (zero_lt_one.trans_le hu)), Real.norm_eq_abs,
    abs_of_pos (exp_pos _)] using hf u hu

open scoped Classical in
/-- The entire part `Λ₀` of Hecke's lattice Mellin pair satisfies a global
logarithmic-exponential norm bound. -/
theorem exists_norm_mellinKernelFEPair_Λ₀_le_exp_mul_log {D : Set (realSpace K)}
    (hD : IsUnitFundamentalDomain K D) (L : Submodule ℤ (mixedSpace K)) [DiscreteTopology L]
    [IsZLattice ℝ L] :
    ∃ C > 0, ∀ s : ℂ, ‖(mellinKernelFEPair hD L).toWeakFEPair.Λ₀ s‖ ≤
      exp (C * (1 + ‖s‖) * log (2 + ‖s‖)) := by
  obtain ⟨c₁, hc₁, α₁, hα₁, hf⟩ := exists_isBigO_mellinKernelFEPair_f_sub hD L
  obtain ⟨c₂, hc₂, α₂, hα₂, hg⟩ := exists_isBigO_mellinKernelFEPair_f_sub hD.inv (mixedDual K L)
  simp only [← mellinKernelFEPair_symm hD L, FEPairWithLevel.symm_f, FEPairWithLevel.symm_f₀] at hg
  exact (mellinKernelFEPair hD L).exists_norm_toWeakFEPair_Λ₀_le_exp_mul_log
    hc₁ hα₁ hc₂ hα₂ hf hg

open scoped Classical in
/-- The entire part `Λ₀` of Hecke's lattice Mellin pair has order at most one. -/
theorem orderLE_mellinKernelFEPair_Λ₀ {D : Set (realSpace K)}
    (hD : IsUnitFundamentalDomain K D) (L : Submodule ℤ (mixedSpace K)) [DiscreteTopology L]
    [IsZLattice ℝ L] :
    OrderLE (mellinKernelFEPair hD L).toWeakFEPair.Λ₀ 1 := by
  obtain ⟨C, _, hC⟩ := exists_norm_mellinKernelFEPair_Λ₀_le_exp_mul_log hD L
  exact orderLE_one_of_norm_le_exp_mul_log hC

open scoped Classical in
/-- The entire part `Λ₀` of Hecke's lattice Mellin pair is bounded on every closed vertical strip
`a ≤ Re s ≤ b`. -/
theorem exists_norm_mellinKernelFEPair_Λ₀_le_of_re_mem_Icc {D : Set (realSpace K)}
    (hD : IsUnitFundamentalDomain K D) (L : Submodule ℤ (mixedSpace K)) [DiscreteTopology L]
    [IsZLattice ℝ L] (a b : ℝ) :
    ∃ M, ∀ s : ℂ, s.re ∈ Icc a b → ‖(mellinKernelFEPair hD L).toWeakFEPair.Λ₀ s‖ ≤ M := by
  obtain ⟨c₁, hc₁, α₁, hα₁, hf⟩ := exists_isBigO_mellinKernelFEPair_f_sub hD L
  obtain ⟨c₂, hc₂, α₂, hα₂, hg⟩ := exists_isBigO_mellinKernelFEPair_f_sub hD.inv (mixedDual K L)
  simp only [← mellinKernelFEPair_symm hD L, FEPairWithLevel.symm_f, FEPairWithLevel.symm_f₀] at hg
  exact (mellinKernelFEPair hD L).exists_norm_toWeakFEPair_Λ₀_le_of_re_mem_Icc
    hc₁ hα₁ hc₂ hα₂ hf hg a b

open scoped Classical in
/-- The entire part `Λ₀` of Hecke's lattice Mellin pair has polynomial vertical-strip growth. -/
theorem hasVerticalStripGrowth_mellinKernelFEPair_Λ₀ {D : Set (realSpace K)}
    (hD : IsUnitFundamentalDomain K D) (L : Submodule ℤ (mixedSpace K)) [DiscreteTopology L]
    [IsZLattice ℝ L] :
    HasVerticalStripGrowth (mellinKernelFEPair hD L).toWeakFEPair.Λ₀ :=
  hasVerticalStripGrowth_of_forall_bound
    (exists_norm_mellinKernelFEPair_Λ₀_le_of_re_mem_Icc hD L)

open scoped Classical in
/-- The pole-cleared entire completion `(mellinKernelFEPair hD L).entireΛ` satisfies a global
`exp (C (1 + ‖s‖) log (2 + ‖s‖))` norm bound. -/
theorem exists_norm_mellinKernelFEPair_entireΛ_le_exp_mul_log {D : Set (realSpace K)}
    (hD : IsUnitFundamentalDomain K D) (L : Submodule ℤ (mixedSpace K)) [DiscreteTopology L]
    [IsZLattice ℝ L] :
    ∃ C > 0, ∀ s : ℂ, ‖(mellinKernelFEPair hD L).entireΛ s‖ ≤
      exp (C * (1 + ‖s‖) * log (2 + ‖s‖)) := by
  rw [← FEPairWithLevel.toWeakFEPair_entireΛ]
  exact (mellinKernelFEPair hD L).toWeakFEPair.exists_norm_entireΛ_le_exp_mul_log_of_Λ₀
    (exists_norm_mellinKernelFEPair_Λ₀_le_exp_mul_log hD L)

open scoped Classical in
/-- The pole-cleared entire completion `(mellinKernelFEPair hD L).entireΛ` has order at most one. -/
theorem orderLE_mellinKernelFEPair_entireΛ {D : Set (realSpace K)}
    (hD : IsUnitFundamentalDomain K D) (L : Submodule ℤ (mixedSpace K)) [DiscreteTopology L]
    [IsZLattice ℝ L] :
    OrderLE (mellinKernelFEPair hD L).entireΛ 1 := by
  obtain ⟨C, _, hC⟩ := exists_norm_mellinKernelFEPair_entireΛ_le_exp_mul_log hD L
  exact orderLE_one_of_norm_le_exp_mul_log hC

open scoped Classical in
/-- The pole-cleared entire completion `(mellinKernelFEPair hD L).entireΛ` has finite order. -/
theorem isFiniteOrder_mellinKernelFEPair_entireΛ {D : Set (realSpace K)}
    (hD : IsUnitFundamentalDomain K D) (L : Submodule ℤ (mixedSpace K)) [DiscreteTopology L]
    [IsZLattice ℝ L] :
    IsFiniteOrder (mellinKernelFEPair hD L).entireΛ :=
  (orderLE_mellinKernelFEPair_entireΛ hD L).isFiniteOrder

open scoped Classical in
/-- The pole-cleared entire completion `(mellinKernelFEPair hD L).entireΛ` has polynomial
vertical-strip growth on every closed vertical strip. -/
theorem hasVerticalStripGrowth_mellinKernelFEPair_entireΛ {D : Set (realSpace K)}
    (hD : IsUnitFundamentalDomain K D) (L : Submodule ℤ (mixedSpace K)) [DiscreteTopology L]
    [IsZLattice ℝ L] :
    HasVerticalStripGrowth (mellinKernelFEPair hD L).entireΛ := by
  rw [← FEPairWithLevel.toWeakFEPair_entireΛ]
  exact (mellinKernelFEPair hD L).toWeakFEPair.hasVerticalStripGrowth_entireΛ_of_Λ₀
    (hasVerticalStripGrowth_mellinKernelFEPair_Λ₀ hD L)

/-! ### Growth of the critical-strip `s / 2` pole-cleared lattice completion -/

open scoped Classical in
/-- `mellinKernelEntireCompletion` satisfies a global `exp (C (1 + ‖s‖) log (2 + ‖s‖))` norm
bound. -/
theorem exists_norm_mellinKernelEntireCompletion_le_exp_mul_log {D : Set (realSpace K)}
    (hD : IsUnitFundamentalDomain K D) (L : Submodule ℤ (mixedSpace K)) [DiscreteTopology L]
    [IsZLattice ℝ L] :
    ∃ C > 0, ∀ s : ℂ, ‖mellinKernelEntireCompletion hD L s‖ ≤
      exp (C * (1 + ‖s‖) * log (2 + ‖s‖)) := by
  obtain ⟨C₀, hC₀, hb⟩ := exists_norm_comp_mul_add_le_exp_mul_log
    (exists_norm_mellinKernelFEPair_entireΛ_le_exp_mul_log hD L) (1 / 2) 0
  refine ⟨C₀ + 2 * 4, by positivity, fun s ↦ ?_⟩
  have hhalf : (1 / 2 : ℂ) * s + 0 = s / 2 := by ring
  rw [mellinKernelEntireCompletion_def, norm_mul]
  have hnorm4 : ‖(4 : ℂ)‖ = 4 := by norm_num
  rw [hnorm4, ← hhalf]
  exact (mul_le_mul_of_nonneg_left (hb s) (by positivity)).trans
    (Real.mul_exp_mul_one_add_mul_log_two_add_le (by positivity) (norm_nonneg s))

open scoped Classical in
/-- `mellinKernelEntireCompletion` has order at most one. -/
theorem orderLE_mellinKernelEntireCompletion {D : Set (realSpace K)}
    (hD : IsUnitFundamentalDomain K D) (L : Submodule ℤ (mixedSpace K)) [DiscreteTopology L]
    [IsZLattice ℝ L] :
    OrderLE (mellinKernelEntireCompletion hD L) 1 := by
  obtain ⟨C, _, hC⟩ := exists_norm_mellinKernelEntireCompletion_le_exp_mul_log hD L
  exact orderLE_one_of_norm_le_exp_mul_log hC

open scoped Classical in
/-- `mellinKernelEntireCompletion` has finite order. -/
theorem isFiniteOrder_mellinKernelEntireCompletion {D : Set (realSpace K)}
    (hD : IsUnitFundamentalDomain K D) (L : Submodule ℤ (mixedSpace K)) [DiscreteTopology L]
    [IsZLattice ℝ L] :
    IsFiniteOrder (mellinKernelEntireCompletion hD L) :=
  (orderLE_mellinKernelEntireCompletion hD L).isFiniteOrder

open scoped Classical in
/-- `mellinKernelEntireCompletion` has polynomial vertical-strip growth on every closed vertical
strip. -/
theorem hasVerticalStripGrowth_mellinKernelEntireCompletion {D : Set (realSpace K)}
    (hD : IsUnitFundamentalDomain K D) (L : Submodule ℤ (mixedSpace K)) [DiscreteTopology L]
    [IsZLattice ℝ L] :
    HasVerticalStripGrowth (mellinKernelEntireCompletion hD L) := by
  have heq : ∀ s, mellinKernelEntireCompletion hD L s =
      4 * (mellinKernelFEPair hD L).entireΛ (((1 / 2 : ℝ) : ℂ) * s + 0) := fun s ↦ by
    rw [mellinKernelEntireCompletion_def]
    congr 2
    push_cast
    ring
  rw [hasVerticalStripGrowth_congr heq]
  exact ((hasVerticalStripGrowth_mellinKernelFEPair_entireΛ hD L).comp_ofReal_mul_add (1 / 2) 0
    |>.const_mul 4)

end TauCeti.LFunctions
