/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.OperatorIdeal.ApproximationNumber.Isometry
public import TauCeti.Analysis.OperatorIdeal.Family.KyFan.Dominance
public import Mathlib.Topology.ContinuousMap.Bounded.Normed
public import TauCeti.Analysis.SpecialFunctions.Log.NatCastAdd

/-!
# The logarithmic operator ideal `L^(1,∞)`

The logarithmic ideal (the Marcinkiewicz or Dixmier–Macaev ideal) `L^(1,∞)` consists of the
operators whose Ky Fan sums `K_N(T) = a₀(T) + ⋯ + a_(N-1)(T)` of approximation numbers grow at most
logarithmically. Its gauge is

`‖T‖_(1,∞) = sup_(N ≥ 1) (log (1 + N))⁻¹ ∑_(j < N) aⱼ(T)`,

with value `∞` outside the ideal. This is the domain of the Dixmier traces: on a positive
endomorphism `T` in the ideal, a Dixmier trace is a generalized limit of the logarithmic means
`(log (1 + N))⁻¹ K_N(T)`, and it extends linearly to all endomorphisms in the ideal.

The four operator-ideal laws follow from those of the Ky Fan gauges, each of which is subadditive,
homogeneous and satisfies the two-sided ideal inequality. The gauge dominates the operator norm
because its first term is `‖T‖ / log 2` and `log 2 ≤ 1`. The gauge is not the extension of a
symmetric gauge in the sense of `TauCeti.SymmetricGauge`, which is normalized to take the value `1`
on a sequence with a single entry `1`; here that value is `1 / log 2`.

Since the gauge is a supremum of continuous functions of `T`, it is lower semicontinuous, so the
normed carriers of the family are complete; it is monotone for Ky Fan domination and hence
invariant under adjoints. Members of the ideal are compact, since `(N + 1) a_N(T) ≤ K_(N+1)(T)`
forces `a_N(T) = O(log N / N)`. Trace-class operators, and in particular finite-rank operators,
lie in the ideal.

## Main declarations

* `TauCeti.OperatorIdealFamily.logarithmic`: the logarithmic operator-ideal family `L^(1,∞)`.
* `TauCeti.OperatorIdealFamily.gauge_logarithmic_le_iff`: `‖T‖_(1,∞) ≤ C` exactly when
  `K_N(T) ≤ C log (1 + N)` for every `N`.
* `TauCeti.OperatorIdealFamily.mem_finiteSubmodule_logarithmic_iff`: membership in `L^(1,∞)` is
  logarithmic growth of the Ky Fan sums.
* `ContinuousLinearMap.kyFanLogMean`: the logarithmic Ky Fan means `(log (N + 2))⁻¹ K_(N+1)(T)`.
* `TauCeti.OperatorIdealFamily.mem_finiteSubmodule_logarithmic_iff_bddAbove`: membership in
  `L^(1,∞)` is boundedness of the logarithmic means.
* `TauCeti.OperatorIdealFamily.isCompactOperator_of_mem_finiteSubmodule_logarithmic`: members of
  `L^(1,∞)` are compact.
* `TauCeti.OperatorIdealFamily.finiteSubmodule_traceClass_le_logarithmic`: trace-class operators
  lie in `L^(1,∞)`.
* `TauCeti.SymmetricOperatorIdealFamily.logarithmic`: the adjoint-invariant diagonal family.

## References

* A. Connes, *Noncommutative Geometry*, Academic Press, 1994, Chapter IV, §2.β.
* A. Connes, H. Moscovici, *The local index formula in noncommutative geometry*, Geom. Funct. Anal.
  5 (1995), §1.
-/

public section

open Filter Topology

open scoped ENNReal NNReal BoundedContinuousFunction

universe u v w

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
  div_nonneg (NNReal.coe_nonneg _) (Real.log_natCast_add_pos one_lt_two N).le

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
  · exact (Real.log_natCast_add_pos one_lt_two N).le
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
  · exact (Real.log_natCast_add_pos one_lt_two N).le
  · exact_mod_cast kyFanGauge_comp_comp_le A T B (N + 1)

/-- The logarithmic means of a trace-class operator tend to zero: its Ky Fan sums are bounded by
`∑ⱼ aⱼ(T)` while `log (N + 2)` tends to infinity. -/
theorem tendsto_kyFanLogMean_of_summable {T : E →L[𝕜] F} (hT : Summable T.singularValue) :
    Tendsto T.kyFanLogMean atTop (𝓝 0) := by
  have hlim := (Real.tendsto_log_natCast_add_atTop 2).inv_tendsto_atTop.const_mul
    (∑' j, (T.singularValue j : ℝ))
  rw [mul_zero] at hlim
  refine squeeze_zero T.kyFanLogMean_nonneg (fun N ↦ ?_) hlim
  rw [kyFanLogMean_def, div_eq_mul_inv]
  refine mul_le_mul_of_nonneg_right ?_ (inv_nonneg.2 (Real.log_natCast_add_pos one_lt_two N).le)
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
  · exact (Real.log_natCast_add_pos one_lt_two N).le
  · exact_mod_cast kyFanGauge_add_le S T (N + 1)

end ContinuousLinearMap

namespace TauCeti

namespace OperatorIdealFamily

/-- The weights `log (N + 2)` of the logarithmic gauge are nonzero. -/
private theorem ofReal_log_add_two_ne_zero (N : ℕ) : ENNReal.ofReal (Real.log (N + 2)) ≠ 0 :=
  (ENNReal.ofReal_pos.2 (Real.log_natCast_add_pos one_lt_two N)).ne'

variable (𝕜 : Type u) [RCLike 𝕜]

/-- The **logarithmic operator-ideal family** `L^(1,∞)`, with gauge
`sup_(N ≥ 1) (log (1 + N))⁻¹ ∑_(j < N) aⱼ(T)`. The supremum is indexed by `N + 1` for `N : ℕ`. -/
noncomputable def logarithmic : OperatorIdealFamily.{u, v, w} 𝕜 where
  gauge T := ⨆ N : ℕ, (T.kyFanGauge (N + 1) : ℝ≥0∞) / ENNReal.ofReal (Real.log (N + 2))
  gauge_add_le S T := iSup_le fun N ↦
    calc ((S + T).kyFanGauge (N + 1) : ℝ≥0∞) / ENNReal.ofReal (Real.log (N + 2))
        ≤ ((S.kyFanGauge (N + 1) : ℝ≥0∞) + T.kyFanGauge (N + 1)) /
            ENNReal.ofReal (Real.log (N + 2)) := by
          gcongr
          exact_mod_cast S.kyFanGauge_add_le T (N + 1)
      _ = (S.kyFanGauge (N + 1) : ℝ≥0∞) / ENNReal.ofReal (Real.log (N + 2)) +
            (T.kyFanGauge (N + 1) : ℝ≥0∞) / ENNReal.ofReal (Real.log (N + 2)) :=
          ENNReal.add_div
      _ ≤ _ := add_le_add (le_iSup_of_le N le_rfl) (le_iSup_of_le N le_rfl)
  gauge_smul c T := by
    simp only [ContinuousLinearMap.kyFanGauge_smul, ENNReal.coe_mul, enorm_eq_nnnorm,
      ENNReal.mul_iSup, mul_div_assoc]
  enorm_le_gauge T := by
    refine le_iSup_of_le 0 ?_
    have hlog : ENNReal.ofReal (Real.log ((0 : ℕ) + 2)) ≤ 1 := by
      rw [ENNReal.ofReal_le_one]
      norm_num
      linarith [Real.log_le_sub_one_of_pos (zero_lt_two' ℝ)]
    rw [zero_add, ContinuousLinearMap.kyFanGauge_one, ← enorm_eq_nnnorm]
    exact (ENNReal.le_div_iff_mul_le (Or.inl (ofReal_log_add_two_ne_zero 0))
      (Or.inl ENNReal.ofReal_ne_top)).2
      (mul_le_of_le_one_right' hlog)
  gauge_comp_le L A R := iSup_le fun N ↦
    calc ((L ∘L A ∘L R).kyFanGauge (N + 1) : ℝ≥0∞) / ENNReal.ofReal (Real.log (N + 2))
        ≤ ((‖L‖₊ * A.kyFanGauge (N + 1) * ‖R‖₊ : ℝ≥0) : ℝ≥0∞) /
            ENNReal.ofReal (Real.log (N + 2)) := by
          gcongr
          exact L.kyFanGauge_comp_comp_le A R (N + 1)
      _ = ‖L‖ₑ * ((A.kyFanGauge (N + 1) : ℝ≥0∞) / ENNReal.ofReal (Real.log (N + 2))) *
            ‖R‖ₑ := by
          simp only [ENNReal.coe_mul, enorm_eq_nnnorm, div_eq_mul_inv]
          ring
      _ ≤ _ := by
          gcongr
          exact le_iSup_of_le N le_rfl

variable {𝕜}
variable {E : Type v} {F : Type w}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- The logarithmic gauge is the supremum over `N ≥ 1` of `K_N(T) / log (1 + N)`, indexed by
`N + 1`. -/
@[simp]
theorem gauge_logarithmic (T : E →L[𝕜] F) :
    (logarithmic.{u, v, w} 𝕜).gauge T =
      ⨆ N : ℕ, (T.kyFanGauge (N + 1) : ℝ≥0∞) / ENNReal.ofReal (Real.log (N + 2)) := (rfl)

/-- **The logarithmic growth bound.** `‖T‖_(1,∞) ≤ C` exactly when `K_N(T) ≤ C log (1 + N)` for
every `N`. -/
theorem gauge_logarithmic_le_iff {T : E →L[𝕜] F} {C : ℝ≥0∞} :
    (logarithmic.{u, v, w} 𝕜).gauge T ≤ C ↔
      ∀ N : ℕ, (T.kyFanGauge N : ℝ≥0∞) ≤ C * ENNReal.ofReal (Real.log (1 + N)) := by
  have key (N : ℕ) : (T.kyFanGauge (N + 1) : ℝ≥0∞) / ENNReal.ofReal (Real.log (N + 2)) ≤ C ↔
      (T.kyFanGauge (N + 1) : ℝ≥0∞) ≤ C * ENNReal.ofReal (Real.log (1 + (N + 1 : ℕ))) := by
    have hN : (1 : ℝ) + (N + 1 : ℕ) = N + 2 := by push_cast; ring
    rw [hN]
    exact ENNReal.div_le_iff (ofReal_log_add_two_ne_zero N) ENNReal.ofReal_ne_top
  rw [gauge_logarithmic, iSup_le_iff]
  simp_rw [key]
  refine ⟨fun h N ↦ ?_, fun h N ↦ h (N + 1)⟩
  cases N with
  | zero => simp
  | succ N => exact h N

/-- The Ky Fan sums of `T` grow at most like `‖T‖_(1,∞) log (1 + N)`. -/
theorem kyFanGauge_le_gauge_logarithmic_mul (T : E →L[𝕜] F) (N : ℕ) :
    (T.kyFanGauge N : ℝ≥0∞) ≤
      (logarithmic.{u, v, w} 𝕜).gauge T * ENNReal.ofReal (Real.log (1 + N)) :=
  gauge_logarithmic_le_iff.1 le_rfl N

/-- **The approximation-number bound.** `(N + 1) a_N(T) ≤ ‖T‖_(1,∞) log (N + 2)`, so the
approximation numbers of a member of `L^(1,∞)` are `O(log N / N)`. -/
theorem mul_singularValue_le_gauge_logarithmic_mul (T : E →L[𝕜] F) (N : ℕ) :
    ((N : ℝ≥0∞) + 1) * T.singularValue N ≤
      (logarithmic.{u, v, w} 𝕜).gauge T * ENNReal.ofReal (Real.log (N + 2)) := by
  have hN : (1 : ℝ) + (N + 1 : ℕ) = N + 2 := by push_cast; ring
  calc ((N : ℝ≥0∞) + 1) * T.singularValue N ≤ T.kyFanGauge (N + 1) := by
        exact_mod_cast T.mul_singularValue_le_kyFanGauge_succ N
    _ ≤ _ := hN ▸ kyFanGauge_le_gauge_logarithmic_mul T (N + 1)

/-- **Membership in `L^(1,∞)`.** An operator lies in the logarithmic ideal exactly when its Ky Fan
sums grow at most logarithmically, `∑_(j < N) aⱼ(T) ≤ C log (1 + N)`. -/
theorem mem_finiteSubmodule_logarithmic_iff (T : E →L[𝕜] F) :
    T ∈ ((logarithmic.{u, v, w} 𝕜).operatorGauge E F).finiteSubmodule ↔
      ∃ C : ℝ, ∀ N : ℕ, (T.kyFanGauge N : ℝ) ≤ C * Real.log (1 + N) := by
  have hlog (N : ℕ) : 0 ≤ Real.log (1 + N) :=
    Real.log_nonneg (by linarith [N.cast_nonneg (α := ℝ)])
  rw [OperatorGauge.mem_finiteSubmodule, operatorGauge_apply]
  constructor
  · intro h
    refine ⟨((logarithmic.{u, v, w} 𝕜).gauge T).toReal, fun N ↦ ?_⟩
    have hK := kyFanGauge_le_gauge_logarithmic_mul T N
    rw [← ENNReal.ofReal_toReal h.ne, ← ENNReal.ofReal_mul ENNReal.toReal_nonneg,
      ← ENNReal.ofReal_coe_nnreal] at hK
    exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg ENNReal.toReal_nonneg (hlog N))).1 hK
  · rintro ⟨C, hC⟩
    refine (gauge_logarithmic_le_iff.2 fun N ↦ ?_).trans_lt (ENNReal.ofReal_lt_top (r := C))
    rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul' (hlog N)]
    exact ENNReal.ofReal_le_ofReal (hC N)

/-- Each logarithmic mean is bounded by the logarithmic gauge. -/
theorem ofReal_kyFanLogMean_le_gauge_logarithmic (T : E →L[𝕜] F) (N : ℕ) :
    ENNReal.ofReal (T.kyFanLogMean N) ≤ (logarithmic 𝕜).gauge T := by
  rw [gauge_logarithmic, ContinuousLinearMap.kyFanLogMean_def,
    ENNReal.ofReal_div_of_pos (Real.log_natCast_add_pos one_lt_two N),
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
    rw [ContinuousLinearMap.kyFanLogMean_def,
      div_le_iff₀ (Real.log_natCast_add_pos one_lt_two N)] at hN
    convert hN using 3
    push_cast
    ring

/-- Operators with the same approximation numbers lie in `L^(1,∞)` simultaneously, even across
different Hilbert-space universes. -/
theorem _root_.ContinuousLinearMap.SameSingularValues.mem_finiteSubmodule_logarithmic_iff
    {G H : Type*} [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    {S : G →L[𝕜] H} {T : E →L[𝕜] F} (h : ContinuousLinearMap.SameSingularValues S T) :
    S ∈ ((logarithmic 𝕜).operatorGauge G H).finiteSubmodule ↔
      T ∈ ((logarithmic 𝕜).operatorGauge E F).finiteSubmodule := by
  rw [mem_finiteSubmodule_logarithmic_iff_bddAbove, mem_finiteSubmodule_logarithmic_iff_bddAbove,
    h.kyFanLogMean_eq]

/-- Conjugation by a linear isometric equivalence preserves membership in `L^(1,∞)`, even across
different Hilbert-space universes. -/
theorem _root_.LinearIsometryEquiv.conjStarAlgEquiv_mem_finiteSubmodule_logarithmic_iff
    (e : E ≃ₗᵢ[𝕜] F) (T : E →L[𝕜] E) :
    e.conjStarAlgEquiv T ∈ ((logarithmic 𝕜).operatorGauge F F).finiteSubmodule ↔
      T ∈ ((logarithmic 𝕜).operatorGauge E E).finiteSubmodule :=
  (ContinuousLinearMap.sameSingularValues_comp_linearIsometryEquiv T e.symm
    e).mem_finiteSubmodule_logarithmic_iff

/-- An operator whose logarithmic means are bounded by a bounded sequence lies in `L^(1,∞)`. -/
theorem mem_finiteSubmodule_logarithmic_of_forall_kyFanLogMean_le {T : E →L[𝕜] F} (g : ℕ →ᵇ ℝ)
    (h : ∀ N, T.kyFanLogMean N ≤ g N) :
    T ∈ ((logarithmic 𝕜).operatorGauge E F).finiteSubmodule :=
  (mem_finiteSubmodule_logarithmic_iff_bddAbove T).2 ⟨‖g‖, Set.forall_mem_range.2 fun N ↦
    (h N).trans ((le_abs_self _).trans (g.norm_coe_le_norm N))⟩

/-- The logarithmic means of a member of `L^(1,∞)` form a bounded sequence. -/
theorem exists_coe_eq_kyFanLogMean {T : E →L[𝕜] F}
    (hT : T ∈ ((logarithmic 𝕜).operatorGauge E F).finiteSubmodule) :
    ∃ f : ℕ →ᵇ ℝ, ⇑f = T.kyFanLogMean :=
  ⟨BoundedContinuousFunction.ofNormedAddCommGroupDiscrete T.kyFanLogMean
    ((logarithmic 𝕜).gauge T).toReal fun N ↦ by
      rw [Real.norm_of_nonneg (T.kyFanLogMean_nonneg N)]
      exact kyFanLogMean_le_toReal_gauge_logarithmic hT N, rfl⟩

/-- **Members of `L^(1,∞)` are compact.** Their approximation numbers are `O(log N / N)`, so they
tend to zero. -/
theorem isCompactOperator_of_mem_finiteSubmodule_logarithmic {T : E →L[𝕜] F}
    (hT : T ∈ ((logarithmic.{u, v, w} 𝕜).operatorGauge E F).finiteSubmodule) :
    IsCompactOperator T := by
  obtain ⟨C, hC⟩ := (mem_finiteSubmodule_logarithmic_iff T).1 hT
  refine ContinuousLinearMap.isCompactOperator_of_tendsto_singularValue
    (NNReal.tendsto_coe.1 ?_)
  have hlim : Tendsto (fun N : ℕ ↦ C * (Real.log (N + 2) / (N + 1))) atTop (𝓝 0) := by
    have h := (Real.tendsto_pow_log_div_mul_add_atTop 1 (-1) 1 one_ne_zero).comp
      (tendsto_atTop_add_const_right atTop 2 tendsto_natCast_atTop_atTop)
    have h' := h.const_mul C
    simp only [Function.comp_def, pow_one, one_mul, mul_zero] at h'
    refine h'.congr fun N ↦ ?_
    ring
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun N ↦ (T.singularValue N).2) fun N ↦ ?_
  -- `(N + 1) a_N(T) ≤ K_(N+1)(T) ≤ C log (N + 2)`.
  have hK : ((N : ℝ) + 1) * T.singularValue N ≤ C * Real.log (N + 2) := by
    have h1 := hC (N + 1)
    have h2 : ((N : ℝ) + 1) * T.singularValue N ≤ T.kyFanGauge (N + 1) := by
      exact_mod_cast T.mul_singularValue_le_kyFanGauge_succ N
    have h3 : (1 : ℝ) + (N + 1) = N + 2 := by ring
    push_cast at h1
    rw [h3] at h1
    linarith
  rw [mul_div_assoc', le_div_iff₀ (by positivity)]
  linarith

/-- **Trace-class operators lie in `L^(1,∞)`**, with `‖T‖_(1,∞) ≤ ‖T‖₁ / log 2`. -/
theorem gauge_logarithmic_le_gauge_traceClass_div (T : E →L[𝕜] F) :
    (logarithmic.{u, v, w} 𝕜).gauge T ≤
      (traceClass.{u, v, w} 𝕜).gauge T / ENNReal.ofReal (Real.log 2) := by
  rw [gauge_traceClass]
  refine iSup_le fun N ↦ ENNReal.div_le_div (T.kyFanGauge_le_nuclearENorm (N + 1)) ?_
  refine ENNReal.ofReal_le_ofReal (Real.log_le_log two_pos ?_)
  linarith [N.cast_nonneg (α := ℝ)]

variable (E F) in
/-- **Inclusion of the trace class in `L^(1,∞)`.** -/
theorem finiteSubmodule_traceClass_le_logarithmic :
    ((traceClass.{u, v, w} 𝕜).operatorGauge E F).finiteSubmodule ≤
      ((logarithmic.{u, v, w} 𝕜).operatorGauge E F).finiteSubmodule := by
  intro T hT
  rw [OperatorGauge.mem_finiteSubmodule, operatorGauge_apply] at hT ⊢
  refine (gauge_logarithmic_le_gauge_traceClass_div T).trans_lt (ENNReal.div_lt_top hT.ne ?_)
  simpa using Real.log_pos one_lt_two

/-- **Finite-rank operators lie in `L^(1,∞)`.** -/
theorem mem_finiteSubmodule_logarithmic_of_rank_le {T : E →L[𝕜] F} {n : ℕ} (hT : T.rank ≤ n) :
    T ∈ ((logarithmic.{u, v, w} 𝕜).operatorGauge E F).finiteSubmodule :=
  finiteSubmodule_traceClass_le_logarithmic E F <| (mem_finiteSubmodule_traceClass_iff T).2 <|
    (T.nuclearENorm_ne_top_iff_summable).1 (T.nuclearENorm_ne_top_of_rank_le hT)

/-- The logarithmic gauge is lower semicontinuous in the operator-norm topology. -/
theorem lowerSemicontinuous_gauge_logarithmic :
    LowerSemicontinuous fun T : E →L[𝕜] F ↦ (logarithmic.{u, v, w} 𝕜).gauge T :=
  lowerSemicontinuous_iSup fun N ↦
    ((ENNReal.continuous_div_const _ (ofReal_log_add_two_ne_zero N)).comp
        (ENNReal.continuous_coe.comp
          (ContinuousLinearMap.continuous_kyFanGauge (N + 1)))).lowerSemicontinuous

/-- The logarithmic operator-ideal family has complete normed carriers. -/
instance logarithmic_isComplete : (logarithmic.{u, v, w} 𝕜).IsComplete :=
  isComplete_of_lowerSemicontinuous fun _ _ _ _ _ _ _ _ ↦ lowerSemicontinuous_gauge_logarithmic

/-- The logarithmic family is Ky Fan dominant: its gauge is a supremum of Ky Fan sums with fixed
weights. -/
instance isKyFanDominant_logarithmic : (logarithmic.{u, v, w} 𝕜).IsKyFanDominant where
  gauge_le_of_forall_kyFanGauge_le h := iSup_mono fun N ↦ by
    gcongr
    exact h (N + 1)

end OperatorIdealFamily

namespace SymmetricOperatorIdealFamily

/-- The adjoint-invariant diagonal-universe logarithmic family `L^(1,∞)`. -/
noncomputable def logarithmic (𝕜 : Type u) [RCLike 𝕜] :
    SymmetricOperatorIdealFamily.{u, v} 𝕜 where
  toOperatorIdealFamily := OperatorIdealFamily.logarithmic.{u, v, v} 𝕜
  gauge_adjoint T := OperatorIdealFamily.gauge_adjoint _ T

/-- The underlying rectangular family of the symmetric logarithmic family. -/
@[simp]
theorem logarithmic_toOperatorIdealFamily (𝕜 : Type u) [RCLike 𝕜] :
    (logarithmic.{u, v} 𝕜).toOperatorIdealFamily = OperatorIdealFamily.logarithmic.{u, v, v} 𝕜 :=
  (rfl)

end SymmetricOperatorIdealFamily

end TauCeti
