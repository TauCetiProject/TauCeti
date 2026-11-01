/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Order.GeneralizedLimit
public import TauCeti.Analysis.OperatorIdeal.ApproximationNumber.Diagonal
public import TauCeti.Analysis.OperatorIdeal.ApproximationNumber.Isometry
public import TauCeti.Analysis.OperatorIdeal.ApproximationNumber.Modulus
public import TauCeti.Analysis.OperatorIdeal.Family.Logarithmic
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# Dixmier traces

Let `ω` be a generalized limit on bounded real sequences (`TauCeti.GeneralizedLimit`). The
*Dixmier trace* of an operator `T` in the logarithmic ideal `L^(1,∞)` is the generalized limit of
its logarithmic Ky Fan means,

`Tr_ω(T) = Lim_ω ((log (1 + N))⁻¹ ∑_(j < N) aⱼ(T))`,

where `aⱼ(T)` are the approximation numbers of `T`. The means are indexed from `N = 1`: the
sequence `ContinuousLinearMap.kyFanLogMean T` takes the value
`(log (N + 2))⁻¹ K_(N+1)(T)` at `N`, matching the indexing of the logarithmic gauge. An operator
lies in `L^(1,∞)` exactly when these means are bounded, and outside `L^(1,∞)` the definition takes
the junk value `0`.

For a positive operator `T` this is Dixmier's trace `Tr_ω(T)`. The means only see approximation
numbers, so for a general operator the value is `Tr_ω(|T|)` (`TauCeti.dixmierTrace_modulus`).

The properties proved here hold for every generalized limit `ω`. The functional `Tr_ω` is
nonnegative, bounded by the logarithmic gauge, positively homogeneous and subadditive. It is
monotone under Ky Fan domination, hence invariant under adjoints, moduli and unitary changes of
coordinates, and `Tr_ω(A T B) ≤ ‖A‖ Tr_ω(T) ‖B‖`. It vanishes on trace-class operators, and when
the logarithmic means converge, `Tr_ω(T)` is their limit for every `ω`. The diagonal operator with
approximation numbers `1 / (j + 1)` has Dixmier trace `1`, by the logarithmic growth of the
harmonic numbers.

Additivity on positive operators, `Tr_ω(S + T) = Tr_ω(S) + Tr_ω(T)`, needs in addition that `ω`
is dilation invariant (`TauCeti.GeneralizedLimit.IsDilationInvariant`), together with the
superadditivity `K_N(S) + K_N(T) ≤ K_(2N)(S + T)` of the Ky Fan sums of positive operators.

## Main declarations

* `ContinuousLinearMap.kyFanLogMean`: the logarithmic Ky Fan means `(log (N + 2))⁻¹ K_(N+1)(T)`.
* `TauCeti.OperatorIdealFamily.mem_finiteSubmodule_logarithmic_iff_bddAbove`: membership in
  `L^(1,∞)` is boundedness of the logarithmic means.
* `TauCeti.dixmierTrace`: the Dixmier trace `Tr_ω`.
* `TauCeti.dixmierTrace_eq_apply`: `Tr_ω(T) = ω f` for the bounded sequence `f` of logarithmic
  means.
* `TauCeti.dixmierTrace_eq_of_tendsto`: convergent logarithmic means give `Tr_ω(T)` their limit.
* `TauCeti.dixmierTrace_smul`, `TauCeti.dixmierTrace_add_le`: positive homogeneity and
  subadditivity.
* `TauCeti.dixmierTrace_le_of_forall_kyFanGauge_le`, `TauCeti.dixmierTrace_comp_comp_le`:
  monotonicity under Ky Fan domination and the two-sided ideal bound.
* `TauCeti.dixmierTrace_eq_zero_of_mem_traceClass`: `Tr_ω` vanishes on trace-class operators.
* `TauCeti.dixmierTrace_eq_one_of_singularValue_eq`: approximation numbers `1 / (j + 1)` give
  Dixmier trace `1`.

## References

* J. Dixmier, *Existence de traces non normales*, C. R. Acad. Sci. Paris Sér. A-B 262 (1966),
  A1107–A1108.
* A. Connes, *Noncommutative Geometry*, Academic Press, 1994, Chapter IV, §2.β.
-/

public section

open Filter Topology

open scoped NNReal ENNReal lp BoundedContinuousFunction

/-- The logarithmic weights `log (N + 2)` are positive. -/
private theorem log_natCast_add_two_pos (N : ℕ) : 0 < Real.log (N + 2) :=
  Real.log_pos (by linarith [N.cast_nonneg (α := ℝ)])

/-- The logarithmic weights `log (N + 2)` tend to infinity. -/
private theorem tendsto_log_natCast_add_two :
    Tendsto (fun N : ℕ ↦ Real.log (N + 2)) atTop atTop :=
  Real.tendsto_log_atTop.comp (tendsto_atTop_add_const_right atTop 2 tendsto_natCast_atTop_atTop)

namespace ContinuousLinearMap

section Seminormed

variable {𝕜 E F G H : Type*} [NontriviallyNormedField 𝕜]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]
  [SeminormedAddCommGroup G] [NormedSpace 𝕜 G] [SeminormedAddCommGroup H] [NormedSpace 𝕜 H]

/-- The **logarithmic Ky Fan means** of `T`. The value at `N` is `(log (N + 2))⁻¹ K_(N+1)(T)`,
the mean `(log (1 + M))⁻¹ ∑_(j < M) aⱼ(T)` at `M = N + 1 ≥ 1`. -/
noncomputable def kyFanLogMean (T : E →L[𝕜] F) (N : ℕ) : ℝ :=
  T.kyFanGauge (N + 1) / Real.log (N + 2)

/-- Unfolding lemma for `ContinuousLinearMap.kyFanLogMean`. -/
theorem kyFanLogMean_def (T : E →L[𝕜] F) (N : ℕ) :
    T.kyFanLogMean N = T.kyFanGauge (N + 1) / Real.log (N + 2) :=
  (rfl)

/-- The logarithmic means are nonnegative. -/
theorem kyFanLogMean_nonneg (T : E →L[𝕜] F) (N : ℕ) : 0 ≤ T.kyFanLogMean N :=
  div_nonneg (NNReal.coe_nonneg _) (log_natCast_add_two_pos N).le

/-- The logarithmic means are homogeneous: those of `c T` are `‖c‖` times those of `T`. -/
@[simp]
theorem kyFanLogMean_smul (c : 𝕜) (T : E →L[𝕜] F) (N : ℕ) :
    (c • T).kyFanLogMean N = ‖c‖ * T.kyFanLogMean N := by
  simp [kyFanLogMean_def, mul_div_assoc]

/-- The logarithmic means of the zero operator vanish. -/
@[simp]
theorem kyFanLogMean_zero : (0 : E →L[𝕜] F).kyFanLogMean = 0 :=
  funext fun N ↦ by simpa using kyFanLogMean_smul (0 : 𝕜) (0 : E →L[𝕜] F) N

/-- Ky Fan domination `Kₖ(S) ≤ Kₖ(T)` passes to the logarithmic means. -/
theorem kyFanLogMean_le_of_forall_kyFanGauge_le {S : G →L[𝕜] H} {T : E →L[𝕜] F}
    (h : ∀ k, S.kyFanGauge k ≤ T.kyFanGauge k) (N : ℕ) : S.kyFanLogMean N ≤ T.kyFanLogMean N := by
  rw [kyFanLogMean_def, kyFanLogMean_def]
  gcongr
  · exact (log_natCast_add_two_pos N).le
  · exact h (N + 1)

/-- Operators with the same approximation numbers have the same logarithmic means. -/
theorem SameSingularValues.kyFanLogMean_eq {S : G →L[𝕜] H} {T : E →L[𝕜] F}
    (h : SameSingularValues S T) : S.kyFanLogMean = T.kyFanLogMean :=
  funext fun N ↦ by rw [kyFanLogMean_def, kyFanLogMean_def, h.kyFanGauge_eq]

/-- The two-sided ideal inequality for the logarithmic means. -/
theorem kyFanLogMean_comp_comp_le (A : G →L[𝕜] H) (T : F →L[𝕜] G) (B : E →L[𝕜] F) (N : ℕ) :
    (A ∘L T ∘L B).kyFanLogMean N ≤ ‖A‖ * T.kyFanLogMean N * ‖B‖ := by
  rw [kyFanLogMean_def, kyFanLogMean_def, mul_div_assoc', div_mul_eq_mul_div]
  gcongr
  · exact (log_natCast_add_two_pos N).le
  · exact_mod_cast kyFanGauge_comp_comp_le A T B (N + 1)

/-- The logarithmic means of a trace-class operator tend to zero: its Ky Fan sums are bounded by
`∑ⱼ aⱼ(T)` while `log (N + 2)` tends to infinity. -/
theorem tendsto_kyFanLogMean_of_summable {T : E →L[𝕜] F} (hT : Summable T.singularValue) :
    Tendsto T.kyFanLogMean atTop (𝓝 0) := by
  have hlim :=
    tendsto_log_natCast_add_two.inv_tendsto_atTop.const_mul (∑' j, (T.singularValue j : ℝ))
  rw [mul_zero] at hlim
  refine squeeze_zero T.kyFanLogMean_nonneg (fun N ↦ ?_) hlim
  rw [kyFanLogMean_def, div_eq_mul_inv]
  refine mul_le_mul_of_nonneg_right ?_ (inv_nonneg.2 (log_natCast_add_two_pos N).le)
  rw [kyFanGauge_def, NNReal.coe_sum]
  exact (NNReal.summable_coe.2 hT).sum_le_tsum _ fun j _ ↦ NNReal.coe_nonneg _

end Seminormed

/-- The logarithmic means are subadditive: `(S + T)` has means at most the sum of those of `S`
and `T`, by the Ky Fan triangle inequality. -/
theorem kyFanLogMean_add_le {𝕜 E F : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] (S T : E →L[𝕜] F) (N : ℕ) :
    (S + T).kyFanLogMean N ≤ S.kyFanLogMean N + T.kyFanLogMean N := by
  rw [kyFanLogMean_def, kyFanLogMean_def, kyFanLogMean_def, ← add_div]
  gcongr
  · exact (log_natCast_add_two_pos N).le
  · exact_mod_cast kyFanGauge_add_le S T (N + 1)

end ContinuousLinearMap

namespace TauCeti

variable {𝕜 E F G H : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]

open ContinuousLinearMap

namespace OperatorIdealFamily

/-- Each logarithmic mean is bounded by the logarithmic gauge. -/
theorem ofReal_kyFanLogMean_le_gauge_logarithmic (T : E →L[𝕜] F) (N : ℕ) :
    ENNReal.ofReal (T.kyFanLogMean N) ≤ (logarithmic 𝕜).gauge T := by
  rw [gauge_logarithmic, kyFanLogMean_def,
    ENNReal.ofReal_div_of_pos (log_natCast_add_two_pos N),
    ENNReal.ofReal_coe_nnreal]
  exact le_iSup (fun N : ℕ ↦ (T.kyFanGauge (N + 1) : ℝ≥0∞) /
    ENNReal.ofReal (Real.log (N + 2))) N

/-- For `T` in `L^(1,∞)`, each logarithmic mean is at most `‖T‖_(1,∞)`. -/
theorem kyFanLogMean_le_toReal_gauge_logarithmic {T : E →L[𝕜] F}
    (hT : T ∈ ((logarithmic 𝕜).operatorGauge E F).finiteSubmodule) (N : ℕ) :
    T.kyFanLogMean N ≤ ((logarithmic 𝕜).gauge T).toReal := by
  rw [OperatorGauge.mem_finiteSubmodule, operatorGauge_apply] at hT
  exact (ENNReal.ofReal_le_iff_le_toReal hT.ne).1 (ofReal_kyFanLogMean_le_gauge_logarithmic T N)

/-- **Membership in `L^(1,∞)` by the logarithmic means.** An operator lies in the logarithmic
ideal exactly when its logarithmic Ky Fan means are bounded. -/
theorem mem_finiteSubmodule_logarithmic_iff_bddAbove (T : E →L[𝕜] F) :
    T ∈ ((logarithmic 𝕜).operatorGauge E F).finiteSubmodule ↔
      BddAbove (Set.range T.kyFanLogMean) := by
  refine ⟨fun hT ↦ ⟨_, Set.forall_mem_range.2 (kyFanLogMean_le_toReal_gauge_logarithmic hT)⟩,
    fun ⟨C, hC⟩ ↦ (mem_finiteSubmodule_logarithmic_iff T).2 ⟨C, fun N ↦ ?_⟩⟩
  cases N with
  | zero => simp
  | succ N =>
    have hN := Set.forall_mem_range.1 hC N
    rw [kyFanLogMean_def, div_le_iff₀ (log_natCast_add_two_pos N)] at hN
    convert hN using 3
    push_cast
    ring

/-- The logarithmic means of a member of `L^(1,∞)` form a bounded sequence. -/
theorem exists_coe_eq_kyFanLogMean {T : E →L[𝕜] F}
    (hT : T ∈ ((logarithmic 𝕜).operatorGauge E F).finiteSubmodule) :
    ∃ f : ℕ →ᵇ ℝ, ⇑f = T.kyFanLogMean :=
  ⟨BoundedContinuousFunction.ofNormedAddCommGroupDiscrete T.kyFanLogMean
    ((logarithmic 𝕜).gauge T).toReal fun N ↦ by
      rw [Real.norm_of_nonneg (T.kyFanLogMean_nonneg N)]
      exact kyFanLogMean_le_toReal_gauge_logarithmic hT N, rfl⟩

end OperatorIdealFamily

open OperatorIdealFamily

open Classical in
/-- The **Dixmier trace** `Tr_ω(T) = Lim_ω ((log (1 + N))⁻¹ ∑_(j < N) aⱼ(T))` of an operator `T`
in the logarithmic ideal `L^(1,∞)`, for a generalized limit `ω`. For positive `T` this is
Dixmier's trace; in general it is the Dixmier trace of the modulus `|T|`. Outside `L^(1,∞)` the
value is `0`. -/
noncomputable def dixmierTrace (ω : GeneralizedLimit) (T : E →L[𝕜] F) : ℝ :=
  if hT : T ∈ ((logarithmic 𝕜).operatorGauge E F).finiteSubmodule then
    ω (exists_coe_eq_kyFanLogMean hT).choose
  else 0

variable (ω : GeneralizedLimit)

/-- **Characterization of the Dixmier trace.** If the logarithmic means of `T` form the bounded
sequence `f`, then `Tr_ω(T) = ω f`. -/
theorem dixmierTrace_eq_apply {T : E →L[𝕜] F} (f : ℕ →ᵇ ℝ) (hf : ⇑f = T.kyFanLogMean) :
    dixmierTrace ω T = ω f := by
  have hT : T ∈ ((logarithmic 𝕜).operatorGauge E F).finiteSubmodule := by
    rw [mem_finiteSubmodule_logarithmic_iff_bddAbove, ← hf]
    exact ⟨‖f‖, Set.forall_mem_range.2 fun N ↦ (le_abs_self _).trans (f.norm_coe_le_norm N)⟩
  rw [dixmierTrace, dite_eq_left hT]
  congr 1
  ext N
  rw [(exists_coe_eq_kyFanLogMean hT).choose_spec, hf]

/-- Outside `L^(1,∞)` the Dixmier trace takes the junk value `0`. -/
theorem dixmierTrace_of_notMem {T : E →L[𝕜] F}
    (hT : T ∉ ((logarithmic 𝕜).operatorGauge E F).finiteSubmodule) : dixmierTrace ω T = 0 :=
  dite_eq_right hT

/-- The Dixmier trace is nonnegative. -/
theorem dixmierTrace_nonneg (T : E →L[𝕜] F) : 0 ≤ dixmierTrace ω T := by
  by_cases hT : T ∈ ((logarithmic 𝕜).operatorGauge E F).finiteSubmodule
  · obtain ⟨f, hf⟩ := exists_coe_eq_kyFanLogMean hT
    rw [dixmierTrace_eq_apply ω f hf]
    exact ω.le_apply_of_eventually_le (Eventually.of_forall fun N ↦ hf ▸ T.kyFanLogMean_nonneg N)
  · rw [dixmierTrace_of_notMem ω hT]

/-- The Dixmier trace is at most the logarithmic gauge: `Tr_ω(T) ≤ ‖T‖_(1,∞)`. -/
theorem dixmierTrace_le_toReal_gauge_logarithmic (T : E →L[𝕜] F) :
    dixmierTrace ω T ≤ ((logarithmic 𝕜).gauge T).toReal := by
  by_cases hT : T ∈ ((logarithmic 𝕜).operatorGauge E F).finiteSubmodule
  · obtain ⟨f, hf⟩ := exists_coe_eq_kyFanLogMean hT
    rw [dixmierTrace_eq_apply ω f hf]
    exact ω.apply_le_of_eventually_le
      (Eventually.of_forall fun N ↦ hf ▸ kyFanLogMean_le_toReal_gauge_logarithmic hT N)
  · rw [dixmierTrace_of_notMem ω hT]
    exact ENNReal.toReal_nonneg

/-- The Dixmier trace is at least the `liminf` of the logarithmic means. -/
theorem liminf_kyFanLogMean_le_dixmierTrace {T : E →L[𝕜] F}
    (hT : T ∈ ((logarithmic 𝕜).operatorGauge E F).finiteSubmodule) :
    liminf T.kyFanLogMean atTop ≤ dixmierTrace ω T := by
  obtain ⟨f, hf⟩ := exists_coe_eq_kyFanLogMean hT
  rw [dixmierTrace_eq_apply ω f hf, ← hf]
  exact ω.liminf_le_apply f

/-- The Dixmier trace is at most the `limsup` of the logarithmic means. -/
theorem dixmierTrace_le_limsup_kyFanLogMean {T : E →L[𝕜] F}
    (hT : T ∈ ((logarithmic 𝕜).operatorGauge E F).finiteSubmodule) :
    dixmierTrace ω T ≤ limsup T.kyFanLogMean atTop := by
  obtain ⟨f, hf⟩ := exists_coe_eq_kyFanLogMean hT
  rw [dixmierTrace_eq_apply ω f hf, ← hf]
  exact ω.apply_le_limsup f

/-- **Convergent logarithmic means.** If the logarithmic means of `T` converge to `L`, then `T`
lies in `L^(1,∞)` and every Dixmier trace of `T` equals `L`. -/
theorem dixmierTrace_eq_of_tendsto {T : E →L[𝕜] F} {L : ℝ}
    (h : Tendsto T.kyFanLogMean atTop (𝓝 L)) : dixmierTrace ω T = L := by
  obtain ⟨f, hf⟩ := exists_coe_eq_kyFanLogMean
    ((mem_finiteSubmodule_logarithmic_iff_bddAbove T).2 h.bddAbove_range)
  rw [dixmierTrace_eq_apply ω f hf]
  exact ω.map_of_tendsto (hf ▸ h)

/-- **Positive homogeneity.** `Tr_ω(c T) = ‖c‖ Tr_ω(T)`. -/
@[simp]
theorem dixmierTrace_smul (c : 𝕜) (T : E →L[𝕜] F) :
    dixmierTrace ω (c • T) = ‖c‖ * dixmierTrace ω T := by
  rcases eq_or_ne c 0 with rfl | hc
  · rw [norm_zero, zero_mul, dixmierTrace_eq_apply ω 0 (funext fun N ↦ by simp), map_zero]
  by_cases hT : T ∈ ((logarithmic 𝕜).operatorGauge E F).finiteSubmodule
  · obtain ⟨f, hf⟩ := exists_coe_eq_kyFanLogMean hT
    rw [dixmierTrace_eq_apply ω f hf, dixmierTrace_eq_apply ω (‖c‖ • f)
      (funext fun N ↦ by simp [hf]), map_smul, smul_eq_mul]
  · have hcT : c • T ∉ ((logarithmic 𝕜).operatorGauge E F).finiteSubmodule := fun h ↦
      hT (by simpa [hc] using Submodule.smul_mem _ c⁻¹ h)
    rw [dixmierTrace_of_notMem ω hT, dixmierTrace_of_notMem ω hcT, mul_zero]

/-- The Dixmier trace of the zero operator vanishes. -/
@[simp]
theorem dixmierTrace_zero : dixmierTrace ω (0 : E →L[𝕜] F) = 0 := by
  simpa using dixmierTrace_smul ω (0 : 𝕜) (0 : E →L[𝕜] F)

/-- **Subadditivity.** `Tr_ω(S + T) ≤ Tr_ω(S) + Tr_ω(T)` for `S` and `T` in `L^(1,∞)`. -/
theorem dixmierTrace_add_le {S T : E →L[𝕜] F}
    (hS : S ∈ ((logarithmic 𝕜).operatorGauge E F).finiteSubmodule)
    (hT : T ∈ ((logarithmic 𝕜).operatorGauge E F).finiteSubmodule) :
    dixmierTrace ω (S + T) ≤ dixmierTrace ω S + dixmierTrace ω T := by
  obtain ⟨f, hf⟩ := exists_coe_eq_kyFanLogMean hS
  obtain ⟨g, hg⟩ := exists_coe_eq_kyFanLogMean hT
  obtain ⟨h, hh⟩ := exists_coe_eq_kyFanLogMean (Submodule.add_mem _ hS hT)
  rw [dixmierTrace_eq_apply ω f hf, dixmierTrace_eq_apply ω g hg, dixmierTrace_eq_apply ω h hh,
    ← map_add]
  refine OrderHomClass.mono ω fun N ↦ ?_
  simpa [hf, hg, hh] using kyFanLogMean_add_le S T N

/-- **Monotonicity under Ky Fan domination.** If `T` lies in `L^(1,∞)` and `Kₖ(S) ≤ Kₖ(T)` for
every `k`, then `Tr_ω(S) ≤ Tr_ω(T)`. The operators may act between different spaces. -/
theorem dixmierTrace_le_of_forall_kyFanGauge_le {S : G →L[𝕜] H} {T : E →L[𝕜] F}
    (hT : T ∈ ((logarithmic 𝕜).operatorGauge E F).finiteSubmodule)
    (h : ∀ k, S.kyFanGauge k ≤ T.kyFanGauge k) : dixmierTrace ω S ≤ dixmierTrace ω T := by
  have hle := kyFanLogMean_le_of_forall_kyFanGauge_le h
  have hS : S ∈ ((logarithmic 𝕜).operatorGauge G H).finiteSubmodule := by
    obtain ⟨C, hC⟩ := (mem_finiteSubmodule_logarithmic_iff_bddAbove T).1 hT
    exact (mem_finiteSubmodule_logarithmic_iff_bddAbove S).2
      ⟨C, Set.forall_mem_range.2 fun N ↦ (hle N).trans (hC ⟨N, rfl⟩)⟩
  obtain ⟨f, hf⟩ := exists_coe_eq_kyFanLogMean hS
  obtain ⟨g, hg⟩ := exists_coe_eq_kyFanLogMean hT
  rw [dixmierTrace_eq_apply ω f hf, dixmierTrace_eq_apply ω g hg]
  exact OrderHomClass.mono ω fun N ↦ by simpa [hf, hg] using hle N

/-- Operators with the same approximation numbers have the same Dixmier trace. -/
theorem dixmierTrace_eq_of_sameSingularValues {S : G →L[𝕜] H} {T : E →L[𝕜] F}
    (h : SameSingularValues S T) : dixmierTrace ω S = dixmierTrace ω T := by
  by_cases hT : T ∈ ((logarithmic 𝕜).operatorGauge E F).finiteSubmodule
  · obtain ⟨f, hf⟩ := exists_coe_eq_kyFanLogMean hT
    rw [dixmierTrace_eq_apply ω f hf, dixmierTrace_eq_apply ω f (hf.trans h.kyFanLogMean_eq.symm)]
  · have hS : S ∉ ((logarithmic 𝕜).operatorGauge G H).finiteSubmodule := by
      rwa [mem_finiteSubmodule_logarithmic_iff_bddAbove, h.kyFanLogMean_eq,
        ← mem_finiteSubmodule_logarithmic_iff_bddAbove]
    rw [dixmierTrace_of_notMem ω hS, dixmierTrace_of_notMem ω hT]

/-- **Adjoint invariance.** `Tr_ω(T†) = Tr_ω(T)`. -/
@[simp]
theorem dixmierTrace_adjoint (T : E →L[𝕜] F) : dixmierTrace ω (adjoint T) = dixmierTrace ω T :=
  dixmierTrace_eq_of_sameSingularValues ω ((sameSingularValues_iff _ _).2 (singularValue_adjoint T))

/-- **Modulus invariance.** `Tr_ω(|T|) = Tr_ω(T)`: the Dixmier trace of an operator is that of its
modulus. -/
@[simp]
theorem dixmierTrace_modulus (T : E →L[𝕜] F) : dixmierTrace ω T.modulus = dixmierTrace ω T :=
  dixmierTrace_eq_of_sameSingularValues ω (sameSingularValues_modulus T)

/-- **Unitary invariance.** The Dixmier trace is invariant under linear isometric changes of
coordinates on the source and the target. -/
@[simp]
theorem dixmierTrace_comp_linearIsometryEquiv (T : E →L[𝕜] F) (e : G ≃ₗᵢ[𝕜] E)
    (f : F ≃ₗᵢ[𝕜] H) :
    dixmierTrace ω (f.toLinearIsometry.toContinuousLinearMap ∘L T ∘L
      e.toLinearIsometry.toContinuousLinearMap) = dixmierTrace ω T :=
  dixmierTrace_eq_of_sameSingularValues ω (sameSingularValues_comp_linearIsometryEquiv T e f)

/-- **The two-sided ideal bound.** `Tr_ω(A T B) ≤ ‖A‖ Tr_ω(T) ‖B‖` for `T` in `L^(1,∞)`. -/
theorem dixmierTrace_comp_comp_le (A : G →L[𝕜] H) {T : F →L[𝕜] G} (B : E →L[𝕜] F)
    (hT : T ∈ ((logarithmic 𝕜).operatorGauge F G).finiteSubmodule) :
    dixmierTrace ω (A ∘L T ∘L B) ≤ ‖A‖ * dixmierTrace ω T * ‖B‖ := by
  have hle := kyFanLogMean_comp_comp_le A T B
  obtain ⟨g, hg⟩ := exists_coe_eq_kyFanLogMean hT
  have hATB : A ∘L T ∘L B ∈ ((logarithmic 𝕜).operatorGauge E H).finiteSubmodule := by
    obtain ⟨C, hC⟩ := (mem_finiteSubmodule_logarithmic_iff_bddAbove T).1 hT
    refine (mem_finiteSubmodule_logarithmic_iff_bddAbove _).2
      ⟨‖A‖ * C * ‖B‖, Set.forall_mem_range.2 fun N ↦ (hle N).trans ?_⟩
    gcongr
    exact hC ⟨N, rfl⟩
  obtain ⟨f, hf⟩ := exists_coe_eq_kyFanLogMean hATB
  rw [dixmierTrace_eq_apply ω f hf, dixmierTrace_eq_apply ω g hg, mul_right_comm, ← smul_eq_mul,
    ← map_smul]
  refine OrderHomClass.mono ω fun N ↦ ?_
  simpa [hf, hg, mul_right_comm] using hle N

/-- **Dixmier traces vanish on the trace class.** -/
theorem dixmierTrace_eq_zero_of_mem_traceClass {T : E →L[𝕜] F}
    (hT : T ∈ ((traceClass 𝕜).operatorGauge E F).finiteSubmodule) : dixmierTrace ω T = 0 :=
  dixmierTrace_eq_of_tendsto ω
    (tendsto_kyFanLogMean_of_summable ((mem_finiteSubmodule_traceClass_iff T).1 hT))

/-- **Dixmier traces vanish on finite-rank operators.** -/
theorem dixmierTrace_eq_zero_of_rank_le {T : E →L[𝕜] F} {n : ℕ} (hT : T.rank ≤ n) :
    dixmierTrace ω T = 0 :=
  dixmierTrace_eq_zero_of_mem_traceClass ω <| (mem_finiteSubmodule_traceClass_iff T).2 <|
    (T.nuclearENorm_ne_top_iff_summable).1 (T.nuclearENorm_ne_top_of_rank_le hT)

/-- **The harmonic model.** An operator with approximation numbers `aⱼ(T) = 1 / (j + 1)` has
Dixmier trace `1` for every generalized limit `ω`: its Ky Fan sums are the harmonic numbers, which
grow like `log N`. -/
theorem dixmierTrace_eq_one_of_singularValue_eq {T : E →L[𝕜] F}
    (hT : ∀ j, T.singularValue j = ((j : ℝ≥0) + 1)⁻¹) : dixmierTrace ω T = 1 := by
  refine dixmierTrace_eq_of_tendsto ω ?_
  have hK (N : ℕ) : (T.kyFanGauge (N + 1) : ℝ) = harmonic (N + 1) := by
    simp [kyFanGauge_def, hT, harmonic]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (by simpa using tendsto_log_natCast_add_two.inv_tendsto_atTop.const_add 1)
    (fun N ↦ ?_) (fun N ↦ ?_)
  · -- `log (N + 2) ≤ H_(N+1)`.
    have hpos := log_natCast_add_two_pos N
    rw [kyFanLogMean_def, hK, le_div_iff₀ hpos, one_mul]
    simpa [add_assoc, one_add_one_eq_two] using log_add_one_le_harmonic (N + 1)
  · -- `H_(N+1) ≤ 1 + log (N + 1) ≤ 1 + log (N + 2)`.
    have hpos := log_natCast_add_two_pos N
    have hH : (harmonic (N + 1) : ℝ) ≤ 1 + Real.log (N + 2) :=
      (harmonic_le_one_add_log (N + 1)).trans (by
        gcongr
        push_cast
        linarith)
    rw [kyFanLogMean_def, hK, div_le_iff₀ hpos]
    calc (harmonic (N + 1) : ℝ) ≤ 1 + Real.log (N + 2) := hH
      _ = _ := by field_simp; ring

/-- The bounded sequence `j ↦ 1 / (j + 1)`. -/
private def harmonicDiagonal : ℓ^∞(ℕ, 𝕜) :=
  ⟨fun j ↦ ((j : 𝕜) + 1)⁻¹, memℓp_infty ⟨1, by
    rintro _ ⟨j, rfl⟩
    dsimp only
    rw [← Nat.cast_add_one, norm_inv, RCLike.norm_natCast]
    exact inv_le_one_of_one_le₀ (by simp)⟩⟩

private theorem norm_harmonicDiagonal (j : ℕ) :
    ‖(harmonicDiagonal (𝕜 := 𝕜)) j‖ = ((j : ℝ) + 1)⁻¹ := by
  simp only [harmonicDiagonal, norm_inv]
  rw [← Nat.cast_add_one, RCLike.norm_natCast, Nat.cast_add_one]

/-- **A Dixmier trace equal to `1`.** On `ℓ²(ℕ, 𝕜)`, the diagonal operator with coefficients
`1 / (j + 1)` has Dixmier trace `1` for every generalized limit `ω`. -/
theorem exists_dixmierTrace_diagonalCLM_eq_one :
    ∃ d : ℓ^∞(ℕ, 𝕜), (∀ j, d j = ((j : 𝕜) + 1)⁻¹) ∧
      ∀ ω : GeneralizedLimit, dixmierTrace ω (lp.diagonalCLM (p := 2) d) = 1 := by
  refine ⟨harmonicDiagonal, fun j ↦ rfl, fun ω ↦ dixmierTrace_eq_one_of_singularValue_eq ω
    fun j ↦ ?_⟩
  have hanti : Antitone fun j ↦ ‖(harmonicDiagonal (𝕜 := 𝕜)) j‖ := fun i j hij ↦ by
    simp only [norm_harmonicDiagonal]
    gcongr
  rw [lp.singularValue_diagonalCLM _ hanti, ← NNReal.coe_inj, coe_nnnorm, norm_harmonicDiagonal]
  push_cast
  rfl

end TauCeti
