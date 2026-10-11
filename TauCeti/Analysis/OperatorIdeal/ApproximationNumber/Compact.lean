/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
public import TauCeti.Analysis.Normed.Operator.Compact.FiniteRank
public import TauCeti.Analysis.OperatorIdeal.ApproximationNumber.Basic

/-!
# Approximation numbers, rank, and compactness

The approximation numbers `aₙ(T)` of a bounded linear map `T : E →L[𝕜] F` measure its distance
to the maps of rank at most `n`. This file relates their vanishing and their decay to rank,
finite-rank approximability and compactness.

* Over a complete field, `aₙ(T) = 0` exactly when `rank T ≤ n`. The maps of rank greater than
  `n` form an open set, so a limit of maps of rank at most `n` again has rank at most `n`. No
  finite dimension is needed.
* `aₙ(T) → 0` exactly when `T` is the operator-norm limit of a sequence `(Rₙ)` with
  `rank Rₙ ≤ n`.
* Over a locally compact field and with a complete target, such a limit is a compact operator.
* Conversely, a compact operator into an inner product space satisfies `aₙ(T) → 0`: the image of
  the unit ball is covered by finitely many `ε`-balls, and composing `T` with the orthogonal
  projection onto the span of their centres gives a finite-rank map within `ε` of `T`. The target
  need not be complete.

Combining the two directions, a bounded operator into a Hilbert space is compact exactly when its
approximation numbers tend to zero.

## Main declarations

* `ContinuousLinearMap.singularValue_eq_zero_iff_rank_le`: `aₙ(T) = 0 ↔ rank T ≤ n`.
* `ContinuousLinearMap.tendsto_singularValue_nhds_zero_iff`: `aₙ(T) → 0` exactly when `T` is
  a limit of maps `Rₙ` with `rank Rₙ ≤ n`.
* `ContinuousLinearMap.isCompactOperator_of_tendsto_singularValue`: if `aₙ(T) → 0` and the
  target is complete, `T` is compact.
* `IsCompactOperator.tendsto_singularValue`: a compact operator into an inner product space has
  `aₙ(T) → 0`.
* `ContinuousLinearMap.isCompactOperator_iff_tendsto_singularValue`: an operator into a Hilbert
  space is compact exactly when `aₙ(T) → 0`.

## References

* A. Pietsch, *Eigenvalues and s-Numbers*, Cambridge Studies in Advanced Mathematics 13,
  Cambridge University Press (1987), §2.2.
* I. C. Gohberg, M. G. Krein, *Introduction to the Theory of Linear Nonselfadjoint Operators*,
  Translations of Mathematical Monographs 18, AMS (1969), Chapter II, §2.
-/

public section

open Filter
open scoped NNReal Topology

namespace ContinuousLinearMap

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- **Finite-rank approximation.** The approximation numbers of `T` tend to zero exactly when `T`
is the operator-norm limit of a sequence of bounded maps `Rₙ` with `rank Rₙ ≤ n`. -/
theorem tendsto_singularValue_nhds_zero_iff {T : E →L[𝕜] F} :
    Tendsto T.singularValue atTop (𝓝 0) ↔
      ∃ R : ℕ → E →L[𝕜] F, (∀ n, (R n).rank ≤ n) ∧ Tendsto R atTop (𝓝 T) := by
  constructor
  · intro h
    -- Choose `Rₙ` of rank at most `n` with `‖T - Rₙ‖ < aₙ(T) + 1 / (n + 1)`.
    choose R hR hRT using fun n : ℕ ↦ exists_rank_le_nnnorm_sub_lt
      (lt_add_of_pos_right (T.singularValue n) (by positivity : (0 : ℝ≥0) < 1 / ((n : ℝ≥0) + 1)))
    have hlim : Tendsto (fun n : ℕ ↦ T.singularValue n + 1 / ((n : ℝ≥0) + 1)) atTop (𝓝 0) := by
      simpa using h.add tendsto_one_div_add_atTop_nhds_zero_nat
    refine ⟨R, hR, tendsto_iff_norm_sub_tendsto_zero.mpr ?_⟩
    refine squeeze_zero (fun _ ↦ norm_nonneg _) (fun n ↦ ?_) (NNReal.tendsto_coe.mpr hlim)
    rw [norm_sub_rev]
    exact_mod_cast (hRT n).le
  · rintro ⟨R, hR, hRT⟩
    have hnorm : Tendsto (fun n ↦ ‖T - R n‖₊) atTop (𝓝 0) := by
      rw [← NNReal.tendsto_coe]
      simpa [norm_sub_rev] using tendsto_iff_norm_sub_tendsto_zero.mp hRT
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hnorm
      (fun _ ↦ zero_le) fun n ↦ T.singularValue_le_nnnorm_sub (hR n)

end ContinuousLinearMap

namespace ContinuousLinearMap

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- **Rank characterization.** Over a complete field, `aₙ(T) = 0` exactly when `rank T ≤ n`: a map
approximated arbitrarily well by maps of rank at most `n` has rank at most `n` itself. -/
theorem singularValue_eq_zero_iff_rank_le {T : E →L[𝕜] F} {n : ℕ} :
    T.singularValue n = 0 ↔ T.rank ≤ n := by
  refine ⟨fun h ↦ ?_, singularValue_eq_zero_of_rank_le⟩
  by_contra hlt
  have hT : ((n + 1 : ℕ) : Cardinal) ≤ T.rank := by
    rw [Nat.cast_succ, ← Cardinal.succ_natCast]
    exact Order.succ_le_of_lt (not_le.mp hlt)
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp (isOpen_setOfPred_nat_le_rank (n + 1)) T hT
  obtain ⟨R, hR, hRT⟩ :=
    exists_rank_le_nnnorm_sub_lt (T := T) (n := n) (c := ⟨ε, hε.le⟩) (by rw [h]; exact_mod_cast hε)
  have hRε : R ∈ Metric.ball T ε := by
    rw [Metric.mem_ball, dist_eq_norm, norm_sub_rev]
    exact_mod_cast hRT
  have hcard : ((n + 1 : ℕ) : Cardinal) ≤ n := (hball hRε).trans hR
  exact absurd (Nat.cast_le.mp hcard) (by omega)

end ContinuousLinearMap

namespace ContinuousLinearMap

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [LocallyCompactSpace 𝕜]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [CompleteSpace F]

/-- **Approximability implies compactness.** Over a locally compact field, a bounded map into a
Banach space whose approximation numbers tend to zero is a compact operator. -/
theorem isCompactOperator_of_tendsto_singularValue {T : E →L[𝕜] F}
    (h : Tendsto T.singularValue atTop (𝓝 0)) : IsCompactOperator T := by
  obtain ⟨R, hR, hRT⟩ := tendsto_singularValue_nhds_zero_iff.mp h
  refine isCompactOperator_of_tendsto hRT (.of_forall fun n ↦ ?_)
  have : Module.Finite 𝕜 (LinearMap.range (R n : E →ₗ[𝕜] F)) :=
    Module.rank_lt_aleph0_iff.mp ((hR n).trans_lt (Cardinal.natCast_lt_aleph0))
  exact LinearMap.HasFiniteRange.isCompactOperator (Module.Finite.iff_fg.mp this)

end ContinuousLinearMap

section InnerProductSpace

variable {𝕜 E F : Type*} [RCLike 𝕜] [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- **Compactness implies approximability on an inner product space target.** The approximation
numbers of a compact operator into an inner product space tend to zero. The target need not be
complete. -/
theorem IsCompactOperator.tendsto_singularValue {T : E →L[𝕜] F} (hT : IsCompactOperator T) :
    Tendsto T.singularValue atTop (𝓝 0) := by
  -- For every `ε > 0` some approximation number of `T` is at most `ε`.
  have key (ε : ℝ) (hε : 0 < ε) : ∃ N, (T.singularValue N : ℝ) ≤ ε := by
    -- Cover the image of the closed unit ball by finitely many `ε`-balls centred in `t`.
    obtain ⟨K, hK, hTK⟩ := hT.image_closedBall_subset_compact 1
    obtain ⟨t, -, ht, hKt⟩ := hK.finite_cover_balls hε
    -- Project onto the span `V` of the centres; the composite `P_V ∘ T` has finite rank.
    set V := Submodule.span 𝕜 t
    have : FiniteDimensional 𝕜 V := FiniteDimensional.span_of_finite 𝕜 ht
    set R := V.starProjection.comp T
    have hR : R.rank ≤ Module.finrank 𝕜 V := by
      refine (Submodule.rank_mono ?_).trans_eq (Module.finrank_eq_rank 𝕜 V).symm
      refine (LinearMap.range_comp_le_range _ _).trans ?_
      simp
    refine ⟨Module.finrank 𝕜 V, (NNReal.coe_le_coe.mpr (T.singularValue_le_nnnorm_sub hR)).trans ?_⟩
    refine ContinuousLinearMap.opNorm_le_of_unit_norm hε.le fun x hx ↦ ?_
    obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp (hKt (hTK ⟨x, by simp [hx], rfl⟩))
    have hyV : y ∈ V := Submodule.subset_span hy
    calc ‖(T - R) x‖ = Metric.infDist (T x) V := by
          simp [R, ← dist_eq_norm, Submodule.dist_starProjection_eq_infDist]
      _ ≤ dist (T x) y := Metric.infDist_le_dist_of_mem hyV
      _ ≤ ε := (Metric.mem_ball.mp hxy).le
  refine (tendsto_order.mpr ⟨fun _ ha ↦ (not_lt_zero ha).elim, fun b hb ↦ ?_⟩)
  obtain ⟨N, hN⟩ := key (b / 2) (by positivity)
  refine eventually_atTop.mpr ⟨N, fun n hn ↦ ?_⟩
  have : (T.singularValue n : ℝ) ≤ b / 2 :=
    (NNReal.coe_le_coe.mpr (T.antitone_singularValue hn)).trans hN
  exact NNReal.coe_lt_coe.mp (this.trans_lt (half_lt_self (NNReal.coe_pos.mpr hb)))

/-- **Compactness characterization on a Hilbert space target.** A bounded operator into a
Hilbert space is compact exactly when its approximation numbers tend to zero. -/
theorem ContinuousLinearMap.isCompactOperator_iff_tendsto_singularValue [CompleteSpace F]
    {T : E →L[𝕜] F} : IsCompactOperator T ↔ Tendsto T.singularValue atTop (𝓝 0) :=
  ⟨IsCompactOperator.tendsto_singularValue, isCompactOperator_of_tendsto_singularValue⟩

end InnerProductSpace
