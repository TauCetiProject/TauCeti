/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Lp.Diagonal.Positive
public import TauCeti.Analysis.OperatorIdeal.Family.DixmierTrace.Linear
import Mathlib.Analysis.PSeries
import Mathlib.Data.Nat.Log
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# Dixmier measurability, singularity, and diagonal models

An operator `T : E →L[ℂ] E` on a complex Hilbert space is **Dixmier measurable**
(`TauCeti.IsDixmierMeasurable`) when it belongs to the logarithmic ideal `L^(1,∞)` and all complex
Dixmier traces `Tr_ω(T)` (`TauCeti.complexDixmierTrace`) associated to dilation-invariant
generalized limits `ω` agree.

We establish the algebraic closure properties of Dixmier-measurable operators, bundle the
Dixmier-measurable subspace of `E →L[ℂ] E` (`TauCeti.dixmierMeasurableSubmodule`, lying between the
trace class and `L^(1,∞)`), and prove that ordinary convergence of the logarithmic means
`T.kyFanLogMean` is a sufficient condition for Dixmier measurability (on the positive cone for any
limit, and for arbitrary operators when the logarithmic means tend to `0`, covering trace-class and
finite-rank operators).

On `ℓ²(ℕ, ℂ)` we construct the three benchmark diagonal phenomena for Dixmier traces: the positive
harmonic diagonal operator `diag((j + 1)⁻¹)` in `L^(1,∞)` is Dixmier measurable with trace `1`, yet
is both the operator-norm limit and the Loewner least upper bound of positive finite-rank
truncations of trace `0`; `diag(((j + 1) log(j + 2))⁻¹)` is positive in `L^(1,∞) \ L¹` with
vanishing Dixmier trace; and there exists a positive diagonal operator in `L^(1,∞)` that is not
Dixmier measurable.

## Main declarations

* `TauCeti.IsDixmierMeasurable`: membership in `L^(1,∞)` together with invariance of `Tr_ω(T)`
  across dilation-invariant `ω`.
* `TauCeti.dixmierMeasurableSubmodule`: the `ℂ`-submodule of Dixmier-measurable operators in
  `E →L[ℂ] E`, satisfying `L¹ ≤ M ≤ L^(1,∞)`.
* `TauCeti.isDixmierMeasurable_of_isPositive_of_tendsto_kyFanLogMean`,
  `TauCeti.isDixmierMeasurable_of_tendsto_kyFanLogMean_zero`: ordinary convergence of logarithmic
  means implies Dixmier measurability.
* `TauCeti.harmonicDiagonalCLM`,
  `TauCeti.exists_monotone_tendsto_isLUB_complexDixmierTrace_eq_zero_ne`: the harmonic diagonal
  model and singularity / Loewner non-normality of `Tr_ω`.
* `TauCeti.exists_isPositive_mem_logarithmic_notMem_traceClass_complexDixmierTrace_eq_zero`:
  positive operator in `L^(1,∞) \ L¹` with vanishing Dixmier trace.
* `TauCeti.exists_isPositive_mem_logarithmic_not_isDixmierMeasurable`: positive operator in
  `L^(1,∞)` that is not Dixmier measurable.

## References

* J. Dixmier, *Existence de traces non normales*, C. R. Acad. Sci. Paris Sér. A-B 262 (1966),
  A1107–A1108.
* A. Connes, *Noncommutative Geometry*, Academic Press, 1994, Chapter IV, §2.β.
* F. Sukochev, D. Zanin, *ζ-function and heat kernel formulae*, J. Funct. Anal. 260 (2011),
  2451–2482.
-/

public section

open Filter Topology

open scoped lp NNReal ENNReal ComplexStarModule BoundedContinuousFunction

namespace TauCeti

open ContinuousLinearMap OperatorIdealFamily

/-! ### Dixmier measurability and sufficient conditions -/

section Measurable

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- An operator `T : E →L[ℂ] E` is **Dixmier measurable** when it belongs to the logarithmic ideal
`L^(1,∞)` and all complex Dixmier traces `Tr_ω(T)` associated to dilation-invariant generalized
limits `ω` coincide. -/
def IsDixmierMeasurable (T : E →L[ℂ] E) : Prop :=
  T ∈ ((logarithmic ℂ).operatorGauge E E).finiteSubmodule ∧
    ∀ ⦃ω₁ ω₂ : GeneralizedLimit⦄, ω₁.IsDilationInvariant → ω₂.IsDilationInvariant →
      complexDixmierTrace ω₁ T = complexDixmierTrace ω₂ T

/-- Definitional characterization of `TauCeti.IsDixmierMeasurable`. -/
theorem isDixmierMeasurable_iff {T : E →L[ℂ] E} :
    IsDixmierMeasurable T ↔
      T ∈ ((logarithmic ℂ).operatorGauge E E).finiteSubmodule ∧
        ∀ ⦃ω₁ ω₂ : GeneralizedLimit⦄, ω₁.IsDilationInvariant → ω₂.IsDilationInvariant →
          complexDixmierTrace ω₁ T = complexDixmierTrace ω₂ T :=
  Iff.rfl

/-- Every Dixmier-measurable operator belongs to the logarithmic ideal `L^(1,∞)`. -/
theorem IsDixmierMeasurable.mem_finiteSubmodule {T : E →L[ℂ] E} (h : IsDixmierMeasurable T) :
    T ∈ ((logarithmic ℂ).operatorGauge E E).finiteSubmodule := h.1

/-- Any two dilation-invariant generalized limits assign the same complex Dixmier trace to a
Dixmier-measurable operator. -/
theorem IsDixmierMeasurable.complexDixmierTrace_eq {T : E →L[ℂ] E} (h : IsDixmierMeasurable T)
    {ω₁ ω₂ : GeneralizedLimit} (h₁ : ω₁.IsDilationInvariant) (h₂ : ω₂.IsDilationInvariant) :
    complexDixmierTrace ω₁ T = complexDixmierTrace ω₂ T := h.2 h₁ h₂

/-- `T` is Dixmier measurable if and only if `T` belongs to `L^(1,∞)` and there is a single complex
number assigned to `T` by every dilation-invariant generalized limit. -/
theorem isDixmierMeasurable_iff_exists_eq {T : E →L[ℂ] E} :
    IsDixmierMeasurable T ↔
      T ∈ ((logarithmic ℂ).operatorGauge E E).finiteSubmodule ∧
        ∃ z : ℂ, ∀ ⦃ω : GeneralizedLimit⦄, ω.IsDilationInvariant → complexDixmierTrace ω T = z := by
  refine and_congr_right fun _ ↦
    ⟨fun h ↦ ?_, fun ⟨z, hz⟩ ω₁ ω₂ h₁ h₂ ↦ (hz h₁).trans (hz h₂).symm⟩
  obtain ⟨ω₀, hω₀⟩ := GeneralizedLimit.exists_isDilationInvariant
  exact ⟨complexDixmierTrace ω₀ T, fun ω hω ↦ h hω hω₀⟩

/-- On positive operators, Dixmier measurability is membership in `L^(1,∞)` together with agreement
of the real-valued `dixmierTrace` across all dilation-invariant generalized limits. -/
theorem isDixmierMeasurable_iff_of_isPositive {T : E →L[ℂ] E} (hT : T.IsPositive) :
    IsDixmierMeasurable T ↔
      T ∈ ((logarithmic ℂ).operatorGauge E E).finiteSubmodule ∧
        ∀ ⦃ω₁ ω₂ : GeneralizedLimit⦄, ω₁.IsDilationInvariant → ω₂.IsDilationInvariant →
          dixmierTrace ω₁ T = dixmierTrace ω₂ T := by
  simp [IsDixmierMeasurable, complexDixmierTrace_of_isPositive _ hT]

/-- For a positive operator whose logarithmic means converge in the ordinary sense to `L`, every
generalized limit gives `Tr_ω(T) = L`. -/
theorem complexDixmierTrace_eq_of_isPositive_of_tendsto_kyFanLogMean (ω : GeneralizedLimit)
    {T : E →L[ℂ] E} (hT : T.IsPositive) {L : ℝ} (hlim : Tendsto T.kyFanLogMean atTop (𝓝 L)) :
    complexDixmierTrace ω T = L := by
  rw [complexDixmierTrace_of_isPositive ω hT, dixmierTrace_eq_of_tendsto ω hlim]

/-- **Ordinary convergence of the logarithmic means implies Dixmier measurability** for positive
operators. -/
theorem isDixmierMeasurable_of_isPositive_of_tendsto_kyFanLogMean {T : E →L[ℂ] E}
    (hT : T.IsPositive) {L : ℝ} (hlim : Tendsto T.kyFanLogMean atTop (𝓝 L)) :
    IsDixmierMeasurable T :=
  ⟨(mem_finiteSubmodule_logarithmic_iff_bddAbove T).2 hlim.bddAbove_range, fun ω₁ ω₂ _ _ ↦ by
    rw [complexDixmierTrace_eq_of_isPositive_of_tendsto_kyFanLogMean ω₁ hT hlim,
      complexDixmierTrace_eq_of_isPositive_of_tendsto_kyFanLogMean ω₂ hT hlim]⟩

/-- For any operator whose logarithmic means converge to `0`, every dilation-invariant Dixmier
trace vanishes. -/
theorem complexDixmierTrace_eq_zero_of_tendsto_kyFanLogMean_zero {ω : GeneralizedLimit}
    (hω : ω.IsDilationInvariant) {T : E →L[ℂ] E} (hlim : Tendsto T.kyFanLogMean atTop (𝓝 0)) :
    complexDixmierTrace ω T = 0 :=
  norm_le_zero_iff.1
    ((norm_complexDixmierTrace_le_dixmierTrace hω T).trans_eq (dixmierTrace_eq_of_tendsto ω hlim))

/-- Ordinary convergence of the logarithmic means to `0` implies Dixmier measurability for an
arbitrary bounded operator. -/
theorem isDixmierMeasurable_of_tendsto_kyFanLogMean_zero {T : E →L[ℂ] E}
    (hlim : Tendsto T.kyFanLogMean atTop (𝓝 0)) : IsDixmierMeasurable T :=
  ⟨(mem_finiteSubmodule_logarithmic_iff_bddAbove T).2 hlim.bddAbove_range, fun _ _ h₁ h₂ ↦
    (complexDixmierTrace_eq_zero_of_tendsto_kyFanLogMean_zero h₁ hlim).trans
      (complexDixmierTrace_eq_zero_of_tendsto_kyFanLogMean_zero h₂ hlim).symm⟩

/-- Trace-class operators are Dixmier measurable (with Dixmier trace `0`). -/
theorem isDixmierMeasurable_of_mem_traceClass {T : E →L[ℂ] E}
    (hT : T ∈ ((traceClass ℂ).operatorGauge E E).finiteSubmodule) : IsDixmierMeasurable T :=
  isDixmierMeasurable_of_tendsto_kyFanLogMean_zero
    (tendsto_kyFanLogMean_of_summable ((mem_finiteSubmodule_traceClass_iff T).1 hT))

/-- Finite-rank operators are Dixmier measurable (with Dixmier trace `0`). -/
theorem isDixmierMeasurable_of_rank_le {T : E →L[ℂ] E} {n : ℕ} (hT : T.rank ≤ n) :
    IsDixmierMeasurable T :=
  ⟨mem_finiteSubmodule_logarithmic_of_rank_le hT, fun ω₁ ω₂ _ _ ↦ by
    rw [complexDixmierTrace_eq_zero_of_rank_le ω₁ hT, complexDixmierTrace_eq_zero_of_rank_le ω₂ hT]⟩

/-- Every commutator `A T - T A` with `T ∈ L^(1,∞)` is Dixmier measurable (with trace `0`). -/
theorem isDixmierMeasurable_comp_sub_comp (A : E →L[ℂ] E) {T : E →L[ℂ] E}
    (hT : T ∈ ((logarithmic ℂ).operatorGauge E E).finiteSubmodule) :
    IsDixmierMeasurable (A ∘L T - T ∘L A) :=
  ⟨Submodule.sub_mem _ ((logarithmic ℂ).comp_left_mem_finiteSubmodule A hT)
      ((logarithmic ℂ).comp_right_mem_finiteSubmodule hT A), fun _ _ h₁ h₂ ↦ by
    rw [complexDixmierTrace_comp_sub_comp_eq_zero h₁ A hT,
      complexDixmierTrace_comp_sub_comp_eq_zero h₂ A hT]⟩

/-- The zero operator is Dixmier measurable. -/
@[simp]
theorem isDixmierMeasurable_zero : IsDixmierMeasurable (0 : E →L[ℂ] E) :=
  ⟨Submodule.zero_mem _, fun _ _ _ _ ↦ by simp⟩

/-- Dixmier measurability is preserved under negation. -/
theorem IsDixmierMeasurable.neg {T : E →L[ℂ] E} (h : IsDixmierMeasurable T) :
    IsDixmierMeasurable (-T) := ⟨Submodule.neg_mem _ h.1, fun _ _ h₁ h₂ ↦ by simp [h.2 h₁ h₂]⟩

/-- Negating an operator preserves Dixmier measurability. -/
@[simp]
theorem isDixmierMeasurable_neg_iff {T : E →L[ℂ] E} :
    IsDixmierMeasurable (-T) ↔ IsDixmierMeasurable T :=
  ⟨fun h ↦ neg_neg T ▸ h.neg, IsDixmierMeasurable.neg⟩

/-- Dixmier measurability is preserved under `star`. -/
theorem IsDixmierMeasurable.star {T : E →L[ℂ] E} (h : IsDixmierMeasurable T) :
    IsDixmierMeasurable (star T) :=
  ⟨(star_mem_finiteSubmodule_iff T).2 h.1, fun _ _ h₁ h₂ ↦ by simp [h.2 h₁ h₂]⟩

/-- Taking `star` preserves Dixmier measurability. -/
@[simp]
theorem isDixmierMeasurable_star_iff {T : E →L[ℂ] E} :
    IsDixmierMeasurable (star T) ↔ IsDixmierMeasurable T :=
  ⟨fun h ↦ star_star T ▸ h.star, IsDixmierMeasurable.star⟩

/-- Dixmier measurability is preserved under taking the Hilbert-space adjoint. -/
theorem IsDixmierMeasurable.adjoint {T : E →L[ℂ] E} (h : IsDixmierMeasurable T) :
    IsDixmierMeasurable (adjoint T) := h.star

/-- Dixmier measurability is preserved under complex scalar multiplication. -/
theorem IsDixmierMeasurable.smul {T : E →L[ℂ] E} (h : IsDixmierMeasurable T) (c : ℂ) :
    IsDixmierMeasurable (c • T) :=
  ⟨Submodule.smul_mem _ c h.1, fun _ _ h₁ h₂ ↦ by
    rw [complexDixmierTrace_smul h₁, complexDixmierTrace_smul h₂, h.2 h₁ h₂]⟩

/-- Dixmier measurability is closed under addition. -/
theorem IsDixmierMeasurable.add {S T : E →L[ℂ] E} (hS : IsDixmierMeasurable S)
    (hT : IsDixmierMeasurable T) : IsDixmierMeasurable (S + T) :=
  ⟨Submodule.add_mem _ hS.1 hT.1, fun _ _ h₁ h₂ ↦ by
    rw [complexDixmierTrace_add h₁ hS.1 hT.1, complexDixmierTrace_add h₂ hS.1 hT.1,
      hS.2 h₁ h₂, hT.2 h₁ h₂]⟩

/-- Dixmier measurability is closed under subtraction. -/
theorem IsDixmierMeasurable.sub {S T : E →L[ℂ] E} (hS : IsDixmierMeasurable S)
    (hT : IsDixmierMeasurable T) : IsDixmierMeasurable (S - T) :=
  sub_eq_add_neg S T ▸ hS.add hT.neg

/-- A bounded operator is Dixmier measurable whenever the four positive parts `(ℜ T)⁺`, `(ℜ T)⁻`,
`(ℑ T)⁺`, `(ℑ T)⁻` of its real and imaginary parts are Dixmier measurable. -/
theorem isDixmierMeasurable_of_parts {T : E →L[ℂ] E}
    (hre_pos : IsDixmierMeasurable (ℜ T : E →L[ℂ] E)⁺)
    (hre_neg : IsDixmierMeasurable (ℜ T : E →L[ℂ] E)⁻)
    (him_pos : IsDixmierMeasurable (ℑ T : E →L[ℂ] E)⁺)
    (him_neg : IsDixmierMeasurable (ℑ T : E →L[ℂ] E)⁻) : IsDixmierMeasurable T := by
  rw [← realPart_add_I_smul_imaginaryPart T,
    ← CFC.posPart_sub_negPart (ℜ T : E →L[ℂ] E) (ℜ T).2,
    ← CFC.posPart_sub_negPart (ℑ T : E →L[ℂ] E) (ℑ T).2]
  exact (hre_pos.sub hre_neg).add ((him_pos.sub him_neg).smul Complex.I)

/-- Conjugation by a linear isometric equivalence preserves Dixmier measurability. -/
@[simp]
theorem isDixmierMeasurable_conj_linearIsometryEquiv_iff (e : E ≃ₗᵢ[ℂ] F) (T : E →L[ℂ] E) :
    IsDixmierMeasurable (e.conjStarAlgEquiv T) ↔ IsDixmierMeasurable T := by
  simp only [IsDixmierMeasurable, conjStarAlgEquiv_mem_finiteSubmodule_logarithmic_iff,
    complexDixmierTrace_conj_linearIsometryEquiv]

/-- Unitary conjugation preserves Dixmier measurability. -/
@[simp]
theorem isDixmierMeasurable_unitary_conj_iff (u : unitary (E →L[ℂ] E)) (T : E →L[ℂ] E) :
    IsDixmierMeasurable ((u : E →L[ℂ] E) ∘L T ∘L star (u : E →L[ℂ] E)) ↔
      IsDixmierMeasurable T :=
  isDixmierMeasurable_conj_linearIsometryEquiv_iff (Unitary.linearIsometryEquiv u) T

/-- The `ℂ`-submodule of Dixmier-measurable operators in `E →L[ℂ] E`. -/
def dixmierMeasurableSubmodule (E : Type*)
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] : Submodule ℂ (E →L[ℂ] E) where
  carrier := {T | IsDixmierMeasurable T}
  zero_mem' := isDixmierMeasurable_zero
  add_mem' hS hT := hS.add hT
  smul_mem' c _ hT := hT.smul c

/-- Membership in `TauCeti.dixmierMeasurableSubmodule` is `TauCeti.IsDixmierMeasurable`. -/
@[simp]
theorem mem_dixmierMeasurableSubmodule_iff {T : E →L[ℂ] E} :
    T ∈ dixmierMeasurableSubmodule E ↔ IsDixmierMeasurable T := Iff.rfl

variable (E) in
/-- The Dixmier-measurable operators form a submodule of the logarithmic ideal `L^(1,∞)`. -/
theorem dixmierMeasurableSubmodule_le_logarithmic :
    dixmierMeasurableSubmodule E ≤ ((logarithmic ℂ).operatorGauge E E).finiteSubmodule :=
  fun _ hT ↦ hT.mem_finiteSubmodule

variable (E) in
/-- Every trace-class operator lies in `TauCeti.dixmierMeasurableSubmodule`. -/
theorem finiteSubmodule_traceClass_le_dixmierMeasurableSubmodule :
    ((traceClass ℂ).operatorGauge E E).finiteSubmodule ≤ dixmierMeasurableSubmodule E :=
  fun _ hT ↦ isDixmierMeasurable_of_mem_traceClass hT

end Measurable

/-! ### Diagonal models on `ℓ²(ℕ, ℂ)` and singularity / non-normality -/

section DiagonalModels

private theorem nonneg_ofAntitone_apply {c : ℕ → ℝ≥0} (hc : Antitone c) :
    open ComplexOrder in ∀ n, 0 ≤ lp.ofAntitone ℂ hc n :=
  open ComplexOrder in fun _ ↦ RCLike.nonneg_iff.2 ⟨by simp, by simp⟩

private theorem isPositive_diagonalCLM_ofAntitone {c : ℕ → ℝ≥0} (hc : Antitone c) :
    (lp.diagonalCLM (p := 2) (lp.ofAntitone ℂ hc)).IsPositive :=
  open ComplexOrder in (lp.isPositive_diagonalCLM_iff _).2 (nonneg_ofAntitone_apply hc)

private theorem sum_range_succ_inv_le_one_add_log (N : ℕ) :
    ∑ j ∈ Finset.range (N + 1), ((j : ℝ) + 1)⁻¹ ≤ 1 + Real.log ((N : ℝ) + 2) := by
  simpa [harmonic] using (harmonic_le_one_add_log (N + 1)).trans
    (add_le_add_right (Real.log_le_log (by positivity) (by push_cast; linarith)) 1)

/-! #### 1. The harmonic diagonal model and non-normality -/

private theorem harmonicEntry_antitone : Antitone fun j : ℕ ↦ ((j : ℝ≥0) + 1)⁻¹ :=
  fun _ _ hij ↦ inv_anti₀ (by positivity) (by gcongr)

private noncomputable def harmonicSeq : ℓ^∞(ℕ, ℂ) := lp.ofAntitone ℂ harmonicEntry_antitone

/-- The **harmonic diagonal operator** `diag((j + 1)⁻¹)` on `ℓ²(ℕ, ℂ)`: the canonical positive
Dixmier-measurable operator in `L^(1,∞)` with Dixmier trace `1`. -/
noncomputable def harmonicDiagonalCLM : ℓ^2(ℕ, ℂ) →L[ℂ] ℓ^2(ℕ, ℂ) :=
  lp.diagonalCLM (p := 2) harmonicSeq

/-- Coordinate formula for `TauCeti.harmonicDiagonalCLM`. -/
@[simp]
theorem harmonicDiagonalCLM_apply (x : ℓ^2(ℕ, ℂ)) (j : ℕ) :
    harmonicDiagonalCLM x j = ((j : ℂ) + 1)⁻¹ * x j := by simp [harmonicDiagonalCLM, harmonicSeq]

private theorem kyFanGauge_harmonicDiagonalCLM (k : ℕ) :
    (harmonicDiagonalCLM.kyFanGauge k : ℝ) = ∑ j ∈ Finset.range k, ((j : ℝ) + 1)⁻¹ := by
  simp [harmonicDiagonalCLM, harmonicSeq]

/-- The harmonic diagonal operator is positive on `ℓ²(ℕ, ℂ)`. -/
theorem isPositive_harmonicDiagonalCLM : harmonicDiagonalCLM.IsPositive :=
  isPositive_diagonalCLM_ofAntitone harmonicEntry_antitone

/-- Every generalized limit assigns real Dixmier trace `1` to `TauCeti.harmonicDiagonalCLM`. -/
@[simp]
theorem dixmierTrace_harmonicDiagonalCLM (ω : GeneralizedLimit) :
    dixmierTrace ω harmonicDiagonalCLM = 1 :=
  dixmierTrace_diagonalCLM_eq_one ω harmonicSeq fun j ↦ by
    simpa [harmonicSeq] using lp.norm_ofAntitone_apply ℂ harmonicEntry_antitone j

/-- The harmonic diagonal operator belongs to the logarithmic ideal `L^(1,∞)`. -/
theorem harmonicDiagonalCLM_mem_logarithmic :
    harmonicDiagonalCLM ∈ ((logarithmic ℂ).operatorGauge ℓ^2(ℕ, ℂ) ℓ^2(ℕ, ℂ)).finiteSubmodule := by
  refine (mem_finiteSubmodule_logarithmic_iff_bddAbove _).2 ⟨1 + (Real.log 2)⁻¹, ?_⟩
  rintro _ ⟨N, rfl⟩
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hlogN : Real.log 2 ≤ Real.log ((N : ℝ) + 2) := Real.log_le_log two_pos (by linarith)
  calc harmonicDiagonalCLM.kyFanLogMean N
      ≤ (1 + Real.log ((N : ℝ) + 2)) / Real.log ((N : ℝ) + 2) := by
        rw [kyFanLogMean_def, kyFanGauge_harmonicDiagonalCLM]
        exact div_le_div_of_nonneg_right (sum_range_succ_inv_le_one_add_log N)
          (hlog2.trans_le hlogN).le
    _ = (Real.log ((N : ℝ) + 2))⁻¹ + 1 := by
        rw [add_div, one_div, div_self (hlog2.trans_le hlogN).ne']
    _ ≤ 1 + (Real.log 2)⁻¹ := by linarith [inv_anti₀ hlog2 hlogN]

/-- Every generalized limit assigns complex Dixmier trace `1` to `TauCeti.harmonicDiagonalCLM`. -/
@[simp]
theorem complexDixmierTrace_harmonicDiagonalCLM (ω : GeneralizedLimit) :
    complexDixmierTrace ω harmonicDiagonalCLM = 1 := by
  rw [complexDixmierTrace_of_isPositive ω isPositive_harmonicDiagonalCLM,
    dixmierTrace_harmonicDiagonalCLM, Complex.ofReal_one]

/-- The harmonic diagonal operator is Dixmier measurable. -/
theorem isDixmierMeasurable_harmonicDiagonalCLM : IsDixmierMeasurable harmonicDiagonalCLM :=
  ⟨harmonicDiagonalCLM_mem_logarithmic, fun _ _ _ _ ↦ by simp⟩

/-- **Singularity and non-normality of the Dixmier trace.** The positive finite-rank coordinate
truncations `Sₙ` of `TauCeti.harmonicDiagonalCLM` form a monotone sequence of positive operators in
`L^(1,∞)` converging to `harmonicDiagonalCLM` in operator norm and having `harmonicDiagonalCLM` as
their least upper bound in the Loewner order, yet `Tr_ω(Sₙ) = 0` for every `n` and `ω` while
`Tr_ω(harmonicDiagonalCLM) = 1`. -/
theorem exists_monotone_tendsto_isLUB_complexDixmierTrace_eq_zero_ne :
    ∃ (S : ℕ → ℓ^2(ℕ, ℂ) →L[ℂ] ℓ^2(ℕ, ℂ)) (T : ℓ^2(ℕ, ℂ) →L[ℂ] ℓ^2(ℕ, ℂ)),
      T ∈ ((logarithmic ℂ).operatorGauge ℓ^2(ℕ, ℂ) ℓ^2(ℕ, ℂ)).finiteSubmodule ∧
      T.IsPositive ∧ IsDixmierMeasurable T ∧ (∀ n, (S n).IsPositive) ∧
      Monotone S ∧ Tendsto S atTop (𝓝 T) ∧ IsLUB (Set.range S) T ∧
      (∀ n (ω : GeneralizedLimit), complexDixmierTrace ω (S n) = 0) ∧
      (∀ ω : GeneralizedLimit, complexDixmierTrace ω T = 1) := by
  open ComplexOrder in
  have hd_nonneg : ∀ j, 0 ≤ harmonicSeq j := nonneg_ofAntitone_apply harmonicEntry_antitone
  have hd_tendsto : Tendsto (fun j ↦ ‖harmonicSeq j‖) atTop (𝓝 0) := by
    have hnorm : (fun j ↦ ‖harmonicSeq j‖) = fun j : ℕ ↦ ((j : ℝ) + 1)⁻¹ := funext fun j ↦ by
      simpa [harmonicSeq] using lp.norm_ofAntitone_apply ℂ harmonicEntry_antitone j
    rw [hnorm]; simpa only [one_div] using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  exact ⟨fun n ↦ lp.diagonalTruncation (p := 2) harmonicSeq (Finset.range n), harmonicDiagonalCLM,
    harmonicDiagonalCLM_mem_logarithmic, isPositive_harmonicDiagonalCLM,
    isDixmierMeasurable_harmonicDiagonalCLM,
    fun n ↦ (lp.isPositive_diagonalTruncation_iff _ _).2 fun i _ ↦ hd_nonneg i,
    fun m n hmn ↦ lp.diagonalTruncation_mono hd_nonneg (Finset.range_mono hmn),
    lp.tendsto_diagonalTruncation_range harmonicSeq hd_tendsto,
    lp.isLUB_range_diagonalTruncation_range hd_nonneg,
    fun n ω ↦ complexDixmierTrace_eq_zero_of_rank_le ω
      (lp.rank_diagonalTruncation_range_le harmonicSeq n), complexDixmierTrace_harmonicDiagonalCLM⟩

/-! #### 2. Zero Dixmier trace outside the trace class -/

private noncomputable def invMulLogSeq (j : ℕ) : ℝ := (((j : ℝ) + 1) * Real.log ((j : ℝ) + 2))⁻¹

private theorem invMulLogSeq_nonneg (j : ℕ) : 0 ≤ invMulLogSeq j :=
  inv_nonneg.2 (mul_nonneg (by positivity) (Real.log_natCast_add_pos one_lt_two j).le)

private theorem invMulLogSeq_antitone : Antitone invMulLogSeq := fun i j hij ↦ by
  have hi2 : (0 : ℝ) < Real.log ((i : ℝ) + 2) := Real.log_natCast_add_pos one_lt_two i
  exact inv_anti₀ (mul_pos (by positivity) hi2) (mul_le_mul
    (by exact_mod_cast Nat.add_le_add_right hij 1)
    (Real.log_le_log (by positivity) (by exact_mod_cast Nat.add_le_add_right hij 2))
    hi2.le (by positivity))

private noncomputable def invMulLogNNSeq (j : ℕ) : ℝ≥0 := ⟨invMulLogSeq j, invMulLogSeq_nonneg j⟩
@[simp] private theorem coe_invMulLogNNSeq (j : ℕ) : (invMulLogNNSeq j : ℝ) = invMulLogSeq j := rfl
private theorem invMulLogNNSeq_antitone : Antitone invMulLogNNSeq := invMulLogSeq_antitone

private theorem not_summable_invMulLogSeq : ¬ Summable invMulLogSeq := fun hsum ↦ by
  have hshift : Summable (fun k : ℕ ↦ (2 : ℝ) ^ (k + 1) * invMulLogSeq (2 ^ (k + 1))) :=
    (summable_nat_add_iff 1).2 <| (summable_condensed_iff_of_nonneg invMulLogSeq_nonneg
      fun _ _ _ hmn ↦ invMulLogSeq_antitone hmn).2 hsum
  have hdom : Summable (fun k : ℕ ↦ (2⁻¹ : ℝ) * (((k + 2 : ℕ) : ℝ))⁻¹) := by
    refine Summable.of_nonneg_of_le (fun _ ↦ by positivity) (fun k ↦ ?_) hshift
    set m := k + 1
    have hm2 : 2 ≤ 2 ^ m := by
      simpa using Nat.pow_le_pow_right (by positivity : 0 < 2) (Nat.succ_pos k)
    have hpow2 : (((2 ^ m : ℕ) : ℝ) + 2) ≤ (2 : ℝ) ^ (m + 1) := by
      exact_mod_cast (by rw [pow_succ (a := 2) (n := m)]; omega : 2 ^ m + 2 ≤ 2 ^ (m + 1))
    have hlog2 : Real.log 2 ≤ 1 := by
      linarith [Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < 2)]
    have hlog_le : Real.log (((2 ^ m : ℕ) : ℝ) + 2) ≤ ((k + 2 : ℕ) : ℝ) :=
      (Real.log_le_log (by positivity) hpow2).trans <| by
        rw [Real.log_pow]
        exact (mul_le_of_le_one_right (by positivity) hlog2).trans_eq (by simp [m, add_assoc])
    have hdenom : (((2 ^ m : ℕ) : ℝ) + 1) * Real.log (((2 ^ m : ℕ) : ℝ) + 2) ≤
        (2 * (2 : ℝ) ^ m) * ((k + 2 : ℕ) : ℝ) :=
      mul_le_mul (by exact_mod_cast (by omega : 2 ^ m + 1 ≤ 2 * 2 ^ m)) hlog_le
        (Real.log_natCast_add_pos one_lt_two (2 ^ m)).le (by positivity)
    have hinv := inv_anti₀
      (mul_pos (by positivity) (Real.log_natCast_add_pos one_lt_two (2 ^ m))) hdenom
    refine (le_of_eq ?_).trans (mul_le_mul_of_nonneg_left hinv (by positivity))
    have h2m : (2 : ℝ) ^ m ≠ 0 := by positivity
    field_simp [h2m]
  exact Real.not_summable_natCast_inv <| (summable_nat_add_iff 2).1 <|
    (hdom.mul_left 2).congr fun k ↦ by rw [← mul_assoc, mul_inv_cancel₀ two_ne_zero, one_mul]

/-- On the tail `[K, N + 1)`, bounding `(log (j + 2))⁻¹ ≤ (log (K + 2))⁻¹` dominates `invMulLogSeq`
by `(log (K + 2))⁻¹` times the harmonic sum `∑_{j < N + 1} (j + 1)⁻¹`. -/
private theorem sum_Ico_invMulLogSeq_le (K N : ℕ) :
    ∑ j ∈ Finset.Ico K (N + 1), invMulLogSeq j ≤
      (Real.log ((K : ℝ) + 2))⁻¹ * (1 + Real.log ((N : ℝ) + 2)) := by
  have hδpos : 0 ≤ (Real.log ((K : ℝ) + 2))⁻¹ :=
    inv_nonneg.2 (Real.log_natCast_add_pos one_lt_two K).le
  calc ∑ j ∈ Finset.Ico K (N + 1), invMulLogSeq j
      ≤ ∑ j ∈ Finset.Ico K (N + 1), (Real.log ((K : ℝ) + 2))⁻¹ * ((j : ℝ) + 1)⁻¹ :=
        Finset.sum_le_sum fun j hj ↦ by
          rw [invMulLogSeq, mul_inv, mul_comm]
          exact mul_le_mul_of_nonneg_right (inv_anti₀ (Real.log_natCast_add_pos one_lt_two K)
            (Real.log_le_log (by positivity)
              (by exact_mod_cast Nat.add_le_add_right (Finset.mem_Ico.1 hj).1 2))) (by positivity)
    _ ≤ (Real.log ((K : ℝ) + 2))⁻¹ * ∑ j ∈ Finset.range (N + 1), ((j : ℝ) + 1)⁻¹ := by
        rw [← Finset.mul_sum]
        exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum_of_subset_of_nonneg
          (fun j hj ↦ Finset.mem_range.2 (Finset.mem_Ico.1 hj).2) fun _ _ _ ↦ by positivity) hδpos
    _ ≤ (Real.log ((K : ℝ) + 2))⁻¹ * (1 + Real.log ((N : ℝ) + 2)) :=
        mul_le_mul_of_nonneg_left (sum_range_succ_inv_le_one_add_log N) hδpos

private theorem tendsto_kyFanLogMean_invMulLogSeq :
    Tendsto (lp.diagonalCLM (p := 2) (lp.ofAntitone ℂ invMulLogNNSeq_antitone)).kyFanLogMean
      atTop (𝓝 0) := by
  set T := lp.diagonalCLM (p := 2) (lp.ofAntitone ℂ invMulLogNNSeq_antitone) with hT
  refine tendsto_order.2 ⟨fun b hb ↦ Eventually.of_forall fun N ↦
    hb.trans_le (T.kyFanLogMean_nonneg N), fun ε hε ↦ ?_⟩
  -- Choose a cutoff `K` with `δ = (log (K + 2))⁻¹ < ε / 2`; the fixed head sum `C` over `j < K`
  -- plus `δ` becomes `< (ε / 2) log (N + 2)` once `N` is large.
  obtain ⟨K, hK⟩ := ((Real.tendsto_log_natCast_add_atTop 2).inv_tendsto_atTop.eventually
    (gt_mem_nhds (half_pos hε))).exists
  set C := ∑ j ∈ Finset.range K, invMulLogSeq j
  set δ := (Real.log ((K : ℝ) + 2))⁻¹
  have herr : Tendsto (fun N : ℕ ↦ (C + δ) / Real.log ((N : ℝ) + 2)) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using
      (Real.tendsto_log_natCast_add_atTop 2).inv_tendsto_atTop.const_mul (C + δ)
  filter_upwards [eventually_ge_atTop K, herr.eventually (gt_mem_nhds (half_pos hε))]
    with N hKN herrN
  have hNK : K ≤ N + 1 := hKN.trans (Nat.le_succ N)
  have hlogN : 0 < Real.log ((N : ℝ) + 2) := Real.log_natCast_add_pos one_lt_two N
  -- Split `K_(N+1)(T)` into the head `[0, K)` and the tail `[K, N + 1)`, bounded via
  -- `sum_Ico_invMulLogSeq_le`.
  have hmean : T.kyFanLogMean N ≤ (C + δ) / Real.log ((N : ℝ) + 2) + δ := by
    have hKsum : (T.kyFanGauge (N + 1) : ℝ) = ∑ j ∈ Finset.range (N + 1), invMulLogSeq j := by
      simp [hT]
    rw [kyFanLogMean_def, hKsum, ← Finset.sum_range_add_sum_Ico _ hNK, div_le_iff₀ hlogN, add_mul,
      div_mul_cancel₀ _ hlogN.ne']
    linarith [sum_Ico_invMulLogSeq_le K N]
  have hδlt : δ < ε / 2 := hK
  linarith

/-- **A positive operator in `L^(1,∞) \ L¹` with vanishing Dixmier trace.** On `ℓ²(ℕ, ℂ)` there
exists a positive Dixmier-measurable operator in `L^(1,∞)` that is not trace class yet satisfies
`dixmierTrace ω T = 0` and `complexDixmierTrace ω T = 0` for every generalized limit `ω`. -/
theorem exists_isPositive_mem_logarithmic_notMem_traceClass_complexDixmierTrace_eq_zero :
    ∃ T : ℓ^2(ℕ, ℂ) →L[ℂ] ℓ^2(ℕ, ℂ), T.IsPositive ∧
      T ∈ ((logarithmic ℂ).operatorGauge ℓ^2(ℕ, ℂ) ℓ^2(ℕ, ℂ)).finiteSubmodule ∧
      T ∉ ((traceClass ℂ).operatorGauge ℓ^2(ℕ, ℂ) ℓ^2(ℕ, ℂ)).finiteSubmodule ∧
      IsDixmierMeasurable T ∧ (∀ ω : GeneralizedLimit, dixmierTrace ω T = 0) ∧
      (∀ ω : GeneralizedLimit, complexDixmierTrace ω T = 0) := by
  set T := lp.diagonalCLM (p := 2) (lp.ofAntitone ℂ invMulLogNNSeq_antitone) with hT
  have hpos : T.IsPositive := isPositive_diagonalCLM_ofAntitone invMulLogNNSeq_antitone
  have hlim : Tendsto T.kyFanLogMean atTop (𝓝 0) := tendsto_kyFanLogMean_invMulLogSeq
  have hnot_tc : T ∉ ((traceClass ℂ).operatorGauge ℓ^2(ℕ, ℂ) ℓ^2(ℕ, ℂ)).finiteSubmodule := by
    rw [mem_finiteSubmodule_traceClass_iff, ← NNReal.summable_coe]
    simpa only [hT, lp.singularValue_diagonalCLM_ofAntitone, coe_invMulLogNNSeq] using
      not_summable_invMulLogSeq
  refine ⟨T, hpos, (mem_finiteSubmodule_logarithmic_iff_bddAbove T).2 hlim.bddAbove_range, hnot_tc,
    isDixmierMeasurable_of_isPositive_of_tendsto_kyFanLogMean hpos hlim,
    fun ω ↦ dixmierTrace_eq_of_tendsto ω hlim, fun ω ↦ ?_⟩
  rw [complexDixmierTrace_of_isPositive ω hpos, dixmierTrace_eq_of_tendsto ω hlim,
    Complex.ofReal_zero]

/-! #### 3. Dependence on the dilation-invariant generalized limit -/

private def lacunaryScale (m : ℕ) : ℕ := 2 ^ (8 ^ m)
private def lacunaryStage (j : ℕ) : ℕ := Nat.log 8 (Nat.log 2 (max j 2))

private theorem lacunaryScale_strictMono : StrictMono lacunaryScale :=
  (pow_right_strictMono₀ one_lt_two).comp (pow_right_strictMono₀ (by norm_num : 1 < 8))

private theorem lacunaryScale_mono : Monotone lacunaryScale := lacunaryScale_strictMono.monotone

private theorem two_le_lacunaryScale (m : ℕ) : 2 ≤ lacunaryScale m := by
  simpa [lacunaryScale] using
    Nat.pow_le_pow_right (by positivity : 0 < 2) (Nat.one_le_pow m 8 (by positivity))

private theorem lacunaryStage_mono : Monotone lacunaryStage := fun _ _ hij ↦
  Nat.log_mono_right (Nat.log_mono_right (max_le_max_right 2 hij))

private theorem lacunaryStage_lacunaryScale (m : ℕ) : lacunaryStage (lacunaryScale m) = m := by
  rw [lacunaryStage, max_eq_left (two_le_lacunaryScale m), lacunaryScale,
    Nat.log_pow one_lt_two, Nat.log_pow (by norm_num : 1 < 8)]

private theorem lacunaryScale_lacunaryStage_le {j : ℕ} (hj : 2 ≤ j) :
    lacunaryScale (lacunaryStage j) ≤ j := by
  rw [lacunaryStage, max_eq_left hj, lacunaryScale]
  have hu : 1 ≤ Nat.log 2 j := Nat.le_log_of_pow_le one_lt_two (by simpa using hj)
  exact (Nat.pow_le_pow_right (by positivity : 0 < 2)
    (Nat.pow_log_le_self 8 (by omega))).trans (Nat.pow_log_le_self 2 (by omega))

private theorem lt_lacunaryScale_lacunaryStage_succ (j : ℕ) :
    j < lacunaryScale (lacunaryStage j + 1) :=
  ((le_max_left j 2).trans_lt (Nat.lt_pow_succ_log_self one_lt_two (max j 2))).trans_le <|
    Nat.pow_le_pow_right (by positivity : 0 < 2) <|
      Nat.succ_le_of_lt (Nat.lt_pow_succ_log_self (by norm_num : 1 < 8) (Nat.log 2 (max j 2)))

private noncomputable def oscSeq (j : ℕ) : ℝ :=
  if Even (lacunaryStage j) then ((j : ℝ) + 1)⁻¹
  else ((lacunaryScale (lacunaryStage j + 1) : ℝ) + 1)⁻¹

private theorem oscSeq_nonneg (j : ℕ) : 0 ≤ oscSeq j := by unfold oscSeq; split_ifs <;> positivity

private theorem oscSeq_le_inv (j : ℕ) : oscSeq j ≤ ((j : ℝ) + 1)⁻¹ := by
  unfold oscSeq; split_ifs
  · exact le_rfl
  · have := lt_lacunaryScale_lacunaryStage_succ j
    exact inv_anti₀ (by positivity) (by exact_mod_cast (by omega : j + 1 ≤ _ + 1))

private theorem inv_lacunaryScale_succ_le_oscSeq (j : ℕ) :
    ((lacunaryScale (lacunaryStage j + 1) : ℝ) + 1)⁻¹ ≤ oscSeq j := by
  unfold oscSeq; split_ifs
  · have := lt_lacunaryScale_lacunaryStage_succ j
    exact inv_anti₀ (by positivity) (by exact_mod_cast (by omega : j + 1 ≤ _ + 1))
  · exact le_rfl

private theorem oscSeq_antitone : Antitone oscSeq := fun i j hij ↦ by
  rcases (lacunaryStage_mono hij).eq_or_lt with heq | hlt
  · unfold oscSeq; rw [heq]; split_ifs
    · exact inv_anti₀ (by positivity) (by exact_mod_cast Nat.add_le_add_right hij 1)
    · exact le_rfl
  · have hj2 : 2 ≤ j := by
      by_contra! hlt2
      exact hlt.ne (by simp [lacunaryStage, max_eq_right (hij.trans hlt2.le), max_eq_right hlt2.le])
    have hscale : lacunaryScale (lacunaryStage i + 1) ≤ j :=
      (lacunaryScale_mono (Nat.succ_le_of_lt hlt)).trans (lacunaryScale_lacunaryStage_le hj2)
    exact (oscSeq_le_inv j).trans <|
      (inv_anti₀ (by positivity) (by exact_mod_cast Nat.add_le_add_right hscale 1)).trans
        (inv_lacunaryScale_succ_le_oscSeq i)

private noncomputable def oscNNSeq (j : ℕ) : ℝ≥0 := ⟨oscSeq j, oscSeq_nonneg j⟩
@[simp] private theorem coe_oscNNSeq (j : ℕ) : (oscNNSeq j : ℝ) = oscSeq j := rfl
private theorem oscNNSeq_antitone : Antitone oscNNSeq := oscSeq_antitone

private theorem pow_seven_mul_le_lacunaryScale_div {m S k : ℕ} (hk : 0 < k) (hkS : k ≤ S)
    (hS : S ≤ 2 ^ (8 ^ m)) : 2 ^ (7 * 8 ^ m) ≤ lacunaryScale (m + 1) / k :=
  (Nat.le_div_iff_mul_le hk).2 <| (Nat.mul_le_mul_left _ (hkS.trans hS)).trans_eq
    (by rw [lacunaryScale, ← pow_add]; congr 1; rw [pow_succ]; ring)

private theorem seven_mul_le_log_lacunaryScale_div {m S k : ℕ} {c : ℝ} (hc : 0 ≤ c) (hk : 0 < k)
    (hkS : k ≤ S) (hS : S ≤ 2 ^ (8 ^ m)) :
    7 * ((8 : ℝ) ^ m * Real.log 2) ≤ Real.log (((lacunaryScale (m + 1) / k : ℕ) : ℝ) + c) := by
  have h1 : ((2 : ℝ) ^ (7 * 8 ^ m)) ≤ ((lacunaryScale (m + 1) / k : ℕ) : ℝ) := by
    exact_mod_cast pow_seven_mul_le_lacunaryScale_div hk hkS hS
  calc 7 * ((8 : ℝ) ^ m * Real.log 2)
      = Real.log ((2 : ℝ) ^ (7 * 8 ^ m)) := by rw [Real.log_pow]; push_cast; ring
    _ ≤ Real.log (((lacunaryScale (m + 1) / k : ℕ) : ℝ) + c) :=
        Real.log_le_log (by positivity) (by linarith)

private theorem harmonic_lacunaryScale_le (m : ℕ) :
    (harmonic (lacunaryScale m) : ℝ) ≤ 1 + (8 : ℝ) ^ m * Real.log 2 :=
  (harmonic_le_one_add_log _).trans_eq (by simp [lacunaryScale, Real.log_pow])

private theorem oscDiag_kyFanLogMean_le_one_third {S r k : ℕ} (hk : 0 < k) (hkS : k ≤ S)
    (hS : S ≤ 2 ^ (8 ^ (2 * r + 1))) (hZ : 2 ≤ (8 : ℝ) ^ (2 * r + 1) * Real.log 2) :
    (lp.diagonalCLM (p := 2) (lp.ofAntitone ℂ oscNNSeq_antitone)).kyFanLogMean
      (lacunaryScale (2 * r + 2) / k) ≤ 1 / 3 := by
  set T := lp.diagonalCLM (p := 2) (lp.ofAntitone ℂ oscNNSeq_antitone) with hT
  set q := lacunaryScale (2 * r + 2) / k
  set Z := (8 : ℝ) ^ (2 * r + 1) * Real.log 2
  have hlogq : 0 < Real.log ((q : ℝ) + 2) := Real.log_natCast_add_pos one_lt_two q
  have hlogq_ge : 7 * Z ≤ Real.log ((q : ℝ) + 2) :=
    seven_mul_le_log_lacunaryScale_div (m := 2 * r + 1) zero_le_two hk hkS hS
  have hpart1 : ∑ j ∈ Finset.range (lacunaryScale (2 * r + 1)), oscSeq j ≤ 1 + Z :=
    (Finset.sum_le_sum fun j _ ↦ oscSeq_le_inv j).trans
      (by simpa [harmonic] using harmonic_lacunaryScale_le (2 * r + 1))
  have hpart2 : ∑ j ∈ Finset.Ico (lacunaryScale (2 * r + 1)) (lacunaryScale (2 * r + 2) + 1),
      oscSeq j ≤ 1 := by
    have hval : oscSeq (lacunaryScale (2 * r + 1)) =
        ((lacunaryScale (2 * r + 2) : ℝ) + 1)⁻¹ := by simp [oscSeq, lacunaryStage_lacunaryScale]
    have hcard : (Finset.Ico (lacunaryScale (2 * r + 1)) (lacunaryScale (2 * r + 2) + 1)).card ≤
        lacunaryScale (2 * r + 2) + 1 := by rw [Nat.card_Ico]; omega
    refine (Finset.sum_le_sum fun j hj ↦ hval ▸ oscSeq_antitone (Finset.mem_Ico.1 hj).1).trans ?_
    rw [Finset.sum_const, nsmul_eq_mul]
    exact (mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (by positivity)).trans_eq
      (mul_inv_cancel₀ (by positivity))
  have hsum : (T.kyFanGauge (q + 1) : ℝ) ≤ 2 + Z := by
    have hKsum : (T.kyFanGauge (q + 1) : ℝ) = ∑ j ∈ Finset.range (q + 1), oscSeq j := by simp [hT]
    rw [hKsum]
    refine (Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.range_mono (Nat.add_le_add_right (Nat.div_le_self _ _) 1))
      fun _ _ _ ↦ oscSeq_nonneg _).trans ?_
    have hle : lacunaryScale (2 * r + 1) ≤ lacunaryScale (2 * r + 2) + 1 :=
      (lacunaryScale_mono (by omega : 2 * r + 1 ≤ 2 * r + 2)).trans (Nat.le_succ _)
    rw [← Finset.sum_range_add_sum_Ico _ hle]; linarith
  rw [kyFanLogMean_def, div_le_iff₀ hlogq]; linarith

private theorem lacunaryStage_eq_of_mem_Ico {m j : ℕ}
    (hj : j ∈ Finset.Ico (lacunaryScale m) (lacunaryScale (m + 1))) :
    lacunaryStage j = m := by
  obtain ⟨hj1, hj2⟩ := Finset.mem_Ico.1 hj
  refine le_antisymm (Nat.lt_add_one_iff.1 ?_)
    (lacunaryStage_lacunaryScale m ▸ lacunaryStage_mono hj1)
  by_contra! hge
  exact hj2.not_ge <| (lacunaryScale_mono hge).trans
    (lacunaryScale_lacunaryStage_le ((two_le_lacunaryScale m).trans hj1))

private theorem oscSeq_eq_inv_of_mem_Ico {r j : ℕ}
    (hj : j ∈ Finset.Ico (lacunaryScale (2 * r)) (lacunaryScale (2 * r + 1))) :
    oscSeq j = ((j : ℝ) + 1)⁻¹ := by simp [oscSeq, lacunaryStage_eq_of_mem_Ico hj]

/-- On the even stage `[lacunaryScale (2 * r), q)` with `q ≤ lacunaryScale (2 * r + 1)`, every index
lies in stage `2 * r`, where `oscSeq j = (j + 1)⁻¹`, so the block sum equals
`H_q - H_(lacunaryScale (2 * r))`. -/
private theorem sum_Ico_oscSeq_eq_harmonic_sub {r q : ℕ} (hBq : lacunaryScale (2 * r) ≤ q)
    (hqB : q ≤ lacunaryScale (2 * r + 1)) :
    ∑ j ∈ Finset.Ico (lacunaryScale (2 * r)) q, oscSeq j =
      (harmonic q : ℝ) - (harmonic (lacunaryScale (2 * r)) : ℝ) := by
  have hcongr : ∑ j ∈ Finset.Ico (lacunaryScale (2 * r)) q, oscSeq j =
      ∑ j ∈ Finset.Ico (lacunaryScale (2 * r)) q, ((j : ℝ) + 1)⁻¹ :=
    Finset.sum_congr rfl fun j hj ↦ oscSeq_eq_inv_of_mem_Ico <|
      Finset.mem_Ico.2 ⟨(Finset.mem_Ico.1 hj).1, (Finset.mem_Ico.1 hj).2.trans_le hqB⟩
  have hsplit := Finset.sum_range_add_sum_Ico (fun j : ℕ ↦ ((j : ℝ) + 1)⁻¹) hBq
  have hharm (m : ℕ) : (harmonic m : ℝ) = ∑ j ∈ Finset.range m, ((j : ℝ) + 1)⁻¹ := by
    simp [harmonic]
  rw [hcongr, hharm, hharm]; linarith

private theorem one_half_le_oscDiag_kyFanLogMean {S r k : ℕ} (hk : 0 < k) (hkS : k ≤ S)
    (hS : S ≤ 2 ^ (8 ^ (2 * r))) (hY : 1 + Real.log 2 ≤ (8 : ℝ) ^ (2 * r) * Real.log 2) :
    1 / 2 ≤ (lp.diagonalCLM (p := 2) (lp.ofAntitone ℂ oscNNSeq_antitone)).kyFanLogMean
      (lacunaryScale (2 * r + 1) / k) := by
  set T := lp.diagonalCLM (p := 2) (lp.ofAntitone ℂ oscNNSeq_antitone) with hT
  set q := lacunaryScale (2 * r + 1) / k
  set Y := (8 : ℝ) ^ (2 * r) * Real.log 2
  have hlogq : 0 < Real.log ((q : ℝ) + 2) := Real.log_natCast_add_pos one_lt_two q
  -- Locate `q` inside the even block `[lacunaryScale (2 * r), lacunaryScale (2 * r + 1)]`, with
  -- `log (q + 1) ≥ 7 Y` dominating the preceding prefix bound `1 + Y`.
  have hBq : lacunaryScale (2 * r) ≤ q :=
    (Nat.pow_le_pow_right (by positivity : 0 < 2) (by omega : 8 ^ (2 * r) ≤ 7 * 8 ^ (2 * r))).trans
      (pow_seven_mul_le_lacunaryScale_div (m := 2 * r) hk hkS hS)
  have hlogq1_ge : 7 * Y ≤ Real.log ((q : ℝ) + 1) :=
    seven_mul_le_log_lacunaryScale_div (m := 2 * r) zero_le_one hk hkS hS
  have hlogq2_le : Real.log ((q : ℝ) + 2) ≤ Real.log 2 + Real.log ((q : ℝ) + 1) :=
    (Real.log_le_log (by positivity) (by exact_mod_cast (by omega : q + 2 ≤ 2 * (q + 1)))).trans_eq
      (Real.log_mul (by positivity) (by positivity))
  -- Lower-bound `K_(q+1)(T)` by the harmonic block `[lacunaryScale (2 * r), q)`, which contributes
  -- `H_q - H_(lacunaryScale (2 * r)) ≥ log (q + 1) - (1 + Y)`.
  have hIco_eq := sum_Ico_oscSeq_eq_harmonic_sub hBq (Nat.div_le_self _ _)
  have hharm_low : Real.log ((q : ℝ) + 1) ≤ (harmonic q : ℝ) := by
    simpa using log_add_one_le_harmonic q
  have hharm_up := harmonic_lacunaryScale_le (2 * r)
  have hgauge_ge : Real.log ((q : ℝ) + 1) - (1 + Y) ≤ (T.kyFanGauge (q + 1) : ℝ) := by
    have hKsum : (T.kyFanGauge (q + 1) : ℝ) = ∑ j ∈ Finset.range (q + 1), oscSeq j := by simp [hT]
    rw [hKsum]
    refine (by linarith : Real.log ((q : ℝ) + 1) - (1 + Y) ≤
      ∑ j ∈ Finset.Ico (lacunaryScale (2 * r)) q, oscSeq j).trans ?_
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (fun j hj ↦ Finset.mem_range.2 ((Finset.mem_Ico.1 hj).2.trans_le (Nat.le_succ q)))
      fun _ _ _ ↦ oscSeq_nonneg _
  rw [kyFanLogMean_def, le_div_iff₀ hlogq]; linarith [Real.log_pos one_lt_two]

/-- **Non-uniqueness of the Dixmier trace (`ω`-dependence).** On `ℓ²(ℕ, ℂ)` there exists a
positive diagonal operator in `L^(1,∞)` that is not Dixmier measurable: two dilation-invariant
generalized limits assign it strictly different Dixmier traces. -/
theorem exists_isPositive_mem_logarithmic_not_isDixmierMeasurable :
    ∃ T : ℓ^2(ℕ, ℂ) →L[ℂ] ℓ^2(ℕ, ℂ), T.IsPositive ∧
      T ∈ ((logarithmic ℂ).operatorGauge ℓ^2(ℕ, ℂ) ℓ^2(ℕ, ℂ)).finiteSubmodule ∧
      ¬ IsDixmierMeasurable T := by
  set T := lp.diagonalCLM (p := 2) (lp.ofAntitone ℂ oscNNSeq_antitone) with hT
  have hpos : T.IsPositive := isPositive_diagonalCLM_ofAntitone oscNNSeq_antitone
  have hmem : T ∈ ((logarithmic ℂ).operatorGauge ℓ^2(ℕ, ℂ) ℓ^2(ℕ, ℂ)).finiteSubmodule := by
    obtain ⟨C, hC⟩ := (mem_finiteSubmodule_logarithmic_iff_bddAbove harmonicDiagonalCLM).1
      harmonicDiagonalCLM_mem_logarithmic
    refine (mem_finiteSubmodule_logarithmic_iff_bddAbove T).2 ⟨C, Set.forall_mem_range.2 fun N ↦ ?_⟩
    refine le_trans ?_ (hC ⟨N, rfl⟩)
    have hKsum : (T.kyFanGauge (N + 1) : ℝ) = ∑ j ∈ Finset.range (N + 1), oscSeq j := by simp [hT]
    rw [kyFanLogMean_def, kyFanLogMean_def, hKsum, kyFanGauge_harmonicDiagonalCLM]
    exact div_le_div_of_nonneg_right (Finset.sum_le_sum fun j _ ↦ oscSeq_le_inv j)
      (Real.log_natCast_add_pos one_lt_two N).le
  obtain ⟨g, hg⟩ := exists_coe_eq_kyFanLogMean hmem
  have hlin (b : ℕ) : Tendsto (fun r : ℕ ↦ 2 * r + b) atTop atTop :=
    tendsto_atTop_atTop.2 fun M ↦ ⟨M, fun r hr ↦ by omega⟩
  have hpow (b : ℕ) : Tendsto (fun r : ℕ ↦ 2 ^ (8 ^ (2 * r + b))) atTop atTop :=
    lacunaryScale_strictMono.tendsto_atTop.comp (hlin b)
  have hreal (b : ℕ) : Tendsto (fun r : ℕ ↦ (8 : ℝ) ^ (2 * r + b) * Real.log 2) atTop atTop :=
    ((tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 8)).comp (hlin b)).atTop_mul_const
      (Real.log_pos one_lt_two)
  obtain ⟨ω₁, hω₁, hle⟩ := GeneralizedLimit.exists_isDilationInvariant_apply_le (g := g)
    (c := 1 / 3) fun S _ ↦ Filter.frequently_atTop.2 fun M ↦ by
      obtain ⟨r, hM, hS, hZ⟩ :=
        ((lacunaryScale_strictMono.tendsto_atTop.eventually_ge_atTop M).and
          (((hpow 1).eventually_ge_atTop S).and ((hreal 1).eventually_ge_atTop 2))).exists
      exact ⟨lacunaryScale (2 * r + 2), hM.trans (lacunaryScale_mono (by omega)),
        fun k hk hkS ↦ (congrFun hg _).trans_le (oscDiag_kyFanLogMean_le_one_third hk hkS hS hZ)⟩
  obtain ⟨ω₂, hω₂, hge⟩ := GeneralizedLimit.exists_isDilationInvariant_le_apply (g := g)
    (c := 1 / 2) fun S _ ↦ Filter.frequently_atTop.2 fun M ↦ by
      obtain ⟨r, hM, hS, hY⟩ :=
        ((lacunaryScale_strictMono.tendsto_atTop.eventually_ge_atTop M).and
          (((hpow 0).eventually_ge_atTop S).and
            ((hreal 0).eventually_ge_atTop (1 + Real.log 2)))).exists
      simp only [add_zero] at hS hY
      exact ⟨lacunaryScale (2 * r + 1), hM.trans (lacunaryScale_mono (by omega)),
        fun k hk hkS ↦ (one_half_le_oscDiag_kyFanLogMean hk hkS hS hY).trans_eq
          (congrFun hg _).symm⟩
  refine ⟨T, hpos, hmem, fun hmeas ↦ ?_⟩
  have heq := ((isDixmierMeasurable_iff_of_isPositive hpos).1 hmeas).2 hω₁ hω₂
  rw [dixmierTrace_eq_apply ω₁ g hg, dixmierTrace_eq_apply ω₂ g hg] at heq; linarith

end DiagonalModels

end TauCeti
