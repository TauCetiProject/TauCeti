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

Over any bounded measurable subset `D` of the norm-one archimedean hypersurface of a number field
`K`, the lattice Mellin kernel `f_D(L, u)` of a full `ℤ`-lattice `L` is continuous on `(0, ∞)` and
approaches `(2 ^ r₂ / w) vol(D)` with an eventual `O(exp (-c u ^ (1 / [K : ℚ])))` error
(`exists_norm_mellinKernel_sub_le`). Combining continuity on `[1, ∞)` with the stretched-exponential
promotion of `TauCeti.Analysis.MellinTransform.Growth` upgrades this eventual estimate to a global
bound on `[1, ∞)` (`exists_norm_mellinKernel_sub_le_on_Ici`).

When `D` is a unit fundamental domain, both `mellinKernel D L` and its Euclidean dual
`mellinKernel D⁻¹ (mixedDual K L)` satisfy stretched-exponential bounds on `(1, ∞)` around
`mellinConstant K`. Feeding these bounds into the split-Mellin adapter of
`TauCeti.NumberTheory.LSeries.MellinGrowth` establishes for every number field `K`, unit
fundamental domain `D`, and full lattice `L` (including any ideal lattice `idealLattice K I`):
* global `exp (C (1 + ‖s‖) log (2 + ‖s‖))` bounds, order at most one (`OrderLE _ 1`), finite order
  (`IsFiniteOrder`), and polynomial `HasVerticalStripGrowth` for
  `(mellinKernelFEPair hD L).entireΛ`;
* the critical-strip `s / 2`-normalized pole-cleared completion `mellinKernelEntireCompletion`,
  which agrees with `s (s - 1) (mellinKernelFEPair hD L).Λ (s / 2)` off `{0, 1}`, takes the
  nonzero value `2 * mellinConstant K` at both `0` and `1`, satisfies the global `s ↔ 1 - s`
  functional equation against `(D⁻¹, L^∨)` (and against `(traceShift K · D⁻¹, σ(I^∨))` for ideal
  lattices), and has order at most one and polynomial vertical-strip growth.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §5.
* H. Iwaniec and E. Kowalski, *Analytic Number Theory*, Chapter 5.
-/

public section

noncomputable section

open Filter MeasureTheory NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
  NumberField.Units TauCeti.NumberField.mixedEmbedding Set Real
open scoped Pointwise Topology nonZeroDivisors

namespace TauCeti.LFunctions

variable {K : Type*} [Field K] [NumberField K]

/-! ### Uniform stretched-exponential bounds on `[1, ∞)` and `(1, ∞)` -/

open scoped Classical in
/-- Over any bounded measurable set `D` of parameters, `mellinKernel D L` minus its asymptotic
constant `(2 ^ r₂ / w) vol(D)` satisfies a stretched-exponential bound with exponent
`[K : ℚ]⁻¹` on all of `[1, ∞)`. -/
theorem exists_norm_mellinKernel_sub_le_on_Ici {D : Set (realSpace K)} (hDm : MeasurableSet D)
    (hD : Bornology.IsBounded D) (L : Submodule ℤ (mixedSpace K)) [DiscreteTopology L]
    [IsZLattice ℝ L] :
    ∃ c > 0, ∃ C ≥ 0, ∀ u ∈ Ici (1 : ℝ),
      ‖mellinKernel D L u - (2 : ℂ) ^ nrComplexPlaces K / (torsionOrder K : ℂ) *
          ((surfaceHaar K).real (Subtype.val ⁻¹' D) : ℂ)‖ ≤
        C * exp (-c * u ^ (Module.finrank ℚ K : ℝ)⁻¹) := by
  obtain ⟨c, hc, C₀, _, hev⟩ := exists_norm_mellinKernel_sub_le hDm hD L
  have hcont : ContinuousOn
      (fun u ↦ mellinKernel D L u - (2 : ℂ) ^ nrComplexPlaces K / (torsionOrder K : ℂ) *
        ((surfaceHaar K).real (Subtype.val ⁻¹' D) : ℂ)) (Ici 1) :=
    ((continuousOn_mellinKernel hDm hD L).mono (Ici_subset_Ioi.mpr zero_lt_one)).sub
      continuousOn_const
  obtain ⟨C, hC, hbound⟩ := exists_norm_le_mul_exp_neg_mul_rpow_Ici_of_eventually hcont hev
  exact ⟨c, hc, C, hC, hbound⟩

open scoped Classical in
/-- Over a unit fundamental domain `D`, `mellinKernel D L - mellinConstant K` satisfies a
stretched-exponential bound with exponent `[K : ℚ]⁻¹` on all of `[1, ∞)`. -/
theorem exists_norm_mellinKernel_sub_mellinConstant_le_on_Ici {D : Set (realSpace K)}
    (hD : IsUnitFundamentalDomain K D) (L : Submodule ℤ (mixedSpace K)) [DiscreteTopology L]
    [IsZLattice ℝ L] :
    ∃ c > 0, ∃ C ≥ 0, ∀ u ∈ Ici (1 : ℝ),
      ‖mellinKernel D L u - mellinConstant K‖ ≤
        C * exp (-c * u ^ (Module.finrank ℚ K : ℝ)⁻¹) := by
  have hcst : (mellinConstant K : ℂ) = (2 : ℂ) ^ nrComplexPlaces K / (torsionOrder K : ℂ) *
      ((surfaceHaar K).real (Subtype.val ⁻¹' D) : ℂ) := by
    rw [mellinConstant_eq_mul_surfaceHaar_real hD]
    push_cast
    rfl
  simpa only [hcst] using exists_norm_mellinKernel_sub_le_on_Ici hD.measurableSet hD.isBounded L

open scoped Classical in
/-- Strict-ray form of `exists_norm_mellinKernel_sub_mellinConstant_le_on_Ici` on `(1, ∞)`. -/
theorem exists_norm_mellinKernel_sub_mellinConstant_le_on_Ioi {D : Set (realSpace K)}
    (hD : IsUnitFundamentalDomain K D) (L : Submodule ℤ (mixedSpace K)) [DiscreteTopology L]
    [IsZLattice ℝ L] :
    ∃ c > 0, ∃ C ≥ 0, ∀ u ∈ Ioi (1 : ℝ),
      ‖mellinKernel D L u - mellinConstant K‖ ≤
        C * exp (-c * u ^ (Module.finrank ℚ K : ℝ)⁻¹) := by
  obtain ⟨c, hc, C, hC, hb⟩ := exists_norm_mellinKernel_sub_mellinConstant_le_on_Ici hD L
  exact ⟨c, hc, C, hC, fun u hu ↦ hb u (mem_Ici.mpr hu.le)⟩

/-! ### Split-Mellin growth of `mellinKernelFEPair` -/

open scoped Classical in
/-- The entire part `Λ₀` of Hecke's lattice Mellin pair satisfies a global
logarithmic-exponential norm bound. -/
theorem exists_norm_mellinKernelFEPair_Λ₀_le_exp_mul_log {D : Set (realSpace K)}
    (hD : IsUnitFundamentalDomain K D) (L : Submodule ℤ (mixedSpace K)) [DiscreteTopology L]
    [IsZLattice ℝ L] :
    ∃ C > 0, ∀ s : ℂ, ‖(mellinKernelFEPair hD L).toWeakFEPair.Λ₀ s‖ ≤
      exp (C * (1 + ‖s‖) * log (2 + ‖s‖)) := by
  have hα : (0 : ℝ) < (Module.finrank ℚ K : ℝ)⁻¹ :=
    inv_pos.mpr (Nat.cast_pos.mpr (Module.finrank_pos (R := ℚ) (M := K)))
  obtain ⟨c₁, hc₁, C₁, hC₁, hf⟩ := exists_norm_mellinKernel_sub_mellinConstant_le_on_Ioi hD L
  obtain ⟨c₂, hc₂, C₂, hC₂, hg⟩ :=
    exists_norm_mellinKernel_sub_mellinConstant_le_on_Ioi hD.inv (mixedDual K L)
  refine (mellinKernelFEPair hD L).exists_norm_toWeakFEPair_Λ₀_le_exp_mul_log
    hC₁ hc₁ hα hC₂ hc₂ hα (fun u hu ↦ ?_) (fun u hu ↦ ?_)
  · simpa only [mellinKernelFEPair_f, mellinKernelFEPair_f₀,
      indicator_of_mem (mem_Ioi.mpr (zero_lt_one.trans hu))] using hf u hu
  · simpa only [mellinKernelFEPair_g, mellinKernelFEPair_g₀,
      indicator_of_mem (mem_Ioi.mpr (zero_lt_one.trans hu))] using hg u hu

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
  have hα : (0 : ℝ) < (Module.finrank ℚ K : ℝ)⁻¹ :=
    inv_pos.mpr (Nat.cast_pos.mpr (Module.finrank_pos (R := ℚ) (M := K)))
  obtain ⟨c₁, hc₁, C₁, -, hf⟩ := exists_norm_mellinKernel_sub_mellinConstant_le_on_Ioi hD L
  obtain ⟨c₂, hc₂, C₂, -, hg⟩ :=
    exists_norm_mellinKernel_sub_mellinConstant_le_on_Ioi hD.inv (mixedDual K L)
  refine (mellinKernelFEPair hD L).exists_norm_toWeakFEPair_Λ₀_le_of_re_mem_Icc
    (C₁ := C₁) (C₂ := C₂) hc₁ hα hc₂ hα (fun u hu ↦ ?_) (fun u hu ↦ ?_) a b
  · simpa only [mellinKernelFEPair_f, mellinKernelFEPair_f₀,
      indicator_of_mem (mem_Ioi.mpr (zero_lt_one.trans hu))] using hf u hu
  · simpa only [mellinKernelFEPair_g, mellinKernelFEPair_g₀,
      indicator_of_mem (mem_Ioi.mpr (zero_lt_one.trans hu))] using hg u hu

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

/-! ### Critical-strip `s / 2` pole-cleared lattice completion -/

open scoped Classical in
/-- **Critical-strip pole-cleared completion** of a lattice Mellin pair:
`4 * (mellinKernelFEPair hD L).entireΛ (s / 2)`. Away from `0` and `1` it equals
`s * (s - 1) * (mellinKernelFEPair hD L).Λ (s / 2)`, while at `0` and `1` it takes the nonzero
removable value `2 * mellinConstant K`. -/
def mellinKernelEntireCompletion {D : Set (realSpace K)} (hD : IsUnitFundamentalDomain K D)
    (L : Submodule ℤ (mixedSpace K)) [DiscreteTopology L] [IsZLattice ℝ L] (s : ℂ) : ℂ :=
  4 * (mellinKernelFEPair hD L).entireΛ (s / 2)

open scoped Classical in
theorem mellinKernelEntireCompletion_def {D : Set (realSpace K)}
    (hD : IsUnitFundamentalDomain K D) (L : Submodule ℤ (mixedSpace K)) [DiscreteTopology L]
    [IsZLattice ℝ L] (s : ℂ) :
    mellinKernelEntireCompletion hD L s = 4 * (mellinKernelFEPair hD L).entireΛ (s / 2) := (rfl)

open scoped Classical in
/-- `mellinKernelEntireCompletion` is entire on `ℂ`. -/
theorem differentiable_mellinKernelEntireCompletion {D : Set (realSpace K)}
    (hD : IsUnitFundamentalDomain K D) (L : Submodule ℤ (mixedSpace K)) [DiscreteTopology L]
    [IsZLattice ℝ L] :
    Differentiable ℂ (mellinKernelEntireCompletion hD L) :=
  ((mellinKernelFEPair hD L).differentiable_entireΛ.comp
    (differentiable_id.div_const 2)).const_mul 4

open scoped Classical in
@[simp]
theorem mellinKernelEntireCompletion_zero {D : Set (realSpace K)}
    (hD : IsUnitFundamentalDomain K D) (L : Submodule ℤ (mixedSpace K)) [DiscreteTopology L]
    [IsZLattice ℝ L] :
    mellinKernelEntireCompletion hD L 0 = 2 * (mellinConstant K : ℂ) := by
  rw [mellinKernelEntireCompletion_def, zero_div, mellinKernelFEPair_entireΛ_zero]
  ring

open scoped Classical in
@[simp]
theorem mellinKernelEntireCompletion_one {D : Set (realSpace K)}
    (hD : IsUnitFundamentalDomain K D) (L : Submodule ℤ (mixedSpace K)) [DiscreteTopology L]
    [IsZLattice ℝ L] :
    mellinKernelEntireCompletion hD L 1 = 2 * (mellinConstant K : ℂ) := by
  rw [mellinKernelEntireCompletion_def, mellinKernelFEPair_entireΛ_half]
  ring

open scoped Classical in
/-- Away from `0` and `1`, `mellinKernelEntireCompletion` equals
`s * (s - 1) * (mellinKernelFEPair hD L).Λ (s / 2)`. -/
theorem mellinKernelEntireCompletion_eq_mul_Λ {D : Set (realSpace K)}
    (hD : IsUnitFundamentalDomain K D) (L : Submodule ℤ (mixedSpace K)) [DiscreteTopology L]
    [IsZLattice ℝ L] {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) :
    mellinKernelEntireCompletion hD L s =
      s * (s - 1) * (mellinKernelFEPair hD L).Λ (s / 2) := by
  have hs0 : s / 2 ≠ 0 := div_ne_zero h0 two_ne_zero
  have hs1 : s / 2 ≠ 1 / 2 := fun h ↦ h1 ((div_left_inj₀ two_ne_zero).mp h)
  rw [mellinKernelEntireCompletion_def, mellinKernelFEPair_entireΛ_eq_mul_Λ hD L hs0 hs1]
  ring

open scoped Classical in
/-- Global `s ↔ 1 - s` functional equation of `mellinKernelEntireCompletion`. -/
theorem mellinKernelEntireCompletion_one_sub {D : Set (realSpace K)}
    (hD : IsUnitFundamentalDomain K D) (L : Submodule ℤ (mixedSpace K)) [DiscreteTopology L]
    [IsZLattice ℝ L] (s : ℂ) :
    mellinKernelEntireCompletion hD L (1 - s) =
      mellinKernelEntireCompletion hD.inv (mixedDual K L) s := by
  have harg : (1 - s) / 2 = (1 / 2 : ℂ) - s / 2 := by ring
  rw [mellinKernelEntireCompletion_def, mellinKernelEntireCompletion_def, harg,
    mellinKernelFEPair_entireΛ_eq hD L, sub_sub_cancel]

open scoped Classical in
/-- Global `s ↔ 1 - s` functional equation of `mellinKernelEntireCompletion` for an ideal lattice
`σ(I)` and its trace dual `σ(J)`. -/
theorem mellinKernelEntireCompletion_idealLattice_one_sub
    {I J : (FractionalIdeal (𝓞 K)⁰ K)ˣ}
    (hJ : (J : FractionalIdeal (𝓞 K)⁰ K) =
      FractionalIdeal.dual ℤ ℚ (I : FractionalIdeal (𝓞 K)⁰ K))
    {D : Set (realSpace K)} (hD : IsUnitFundamentalDomain K D) (s : ℂ) :
    mellinKernelEntireCompletion hD (idealLattice K I) (1 - s) =
      mellinKernelEntireCompletion (hD.inv.mul traceShift_mem_normOneSurface)
        (idealLattice K J) s := by
  have harg : (1 - s) / 2 = (1 / 2 : ℂ) - s / 2 := by ring
  rw [mellinKernelEntireCompletion_def, mellinKernelEntireCompletion_def, harg,
    mellinKernelFEPair_idealLattice_entireΛ_eq hJ hD, sub_sub_cancel]

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
  refine ⟨C₀ + 8, by positivity, fun s ↦ ?_⟩
  have hhalf : (1 / 2 : ℂ) * s + 0 = s / 2 := by ring
  rw [mellinKernelEntireCompletion_def, norm_mul]
  have hnorm4 : ‖(4 : ℂ)‖ = 4 := by norm_num
  rw [hnorm4, ← hhalf]
  calc 4 * ‖(mellinKernelFEPair hD L).entireΛ ((1 / 2 : ℂ) * s + 0)‖
      ≤ exp (8 * ((1 + ‖s‖) * log (2 + ‖s‖))) *
          exp (C₀ * (1 + ‖s‖) * log (2 + ‖s‖)) := by
        refine mul_le_mul ?_ (hb s) (norm_nonneg _) (exp_pos _).le
        have hW := one_half_le_one_add_mul_log_two_add (norm_nonneg s)
        exact (by linarith [add_one_le_exp (4 : ℝ)] : (4 : ℝ) ≤ exp 4).trans
          (exp_le_exp.mpr (by nlinarith))
    _ = exp ((C₀ + 8) * (1 + ‖s‖) * log (2 + ‖s‖)) := by
        rw [← exp_add]
        congr 1
        ring

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
