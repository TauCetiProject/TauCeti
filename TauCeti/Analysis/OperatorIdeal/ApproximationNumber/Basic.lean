/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.NNNorm
public import Mathlib.LinearAlgebra.Dimension.DivisionRing
public import Mathlib.LinearAlgebra.Dimension.LinearMap
public import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# Approximation numbers of bounded operators

For a bounded linear map `T : E →L[𝕜] F` between seminormed spaces, the `n`-th approximation
number `aₙ(T)` is the distance in operator norm from `T` to the bounded maps of rank at most `n`:
`aₙ(T) = inf {‖T - R‖ : rank R ≤ n}`. The indexing is zero-based, so `a₀(T) = ‖T‖`. On
finite-dimensional Hilbert spaces the approximation numbers are the singular values, and in
general they are the basic `s`-number sequence measuring how well `T` is approximated by
finite-rank maps.

The sequence is `ContinuousLinearMap.singularValue T : ℕ → ℝ≥0`. This file proves its
elementary calculus: the infimum characterization, antitonicity, the bound by the operator norm,
the additive and multiplicative index laws `a_{m+n}(S + T) ≤ aₘ(S) + aₙ(T)` and
`a_{m+n}(S T) ≤ aₘ(S) aₙ(T)`, the two-sided ideal inequality `aₙ(A T B) ≤ ‖A‖ aₙ(T) ‖B‖`, scalar
homogeneity, and Lipschitz continuity in operator norm. It also defines the Ky Fan gauge
`Kₖ(T) = ∑_{n<k} aₙ(T)`, the prefix sums from which the Ky Fan operator ideals are built.

No completeness, finite dimension, or inner product is assumed: the scalars form any nontrivially
normed field and the spaces are seminormed. Spaces in different universes are allowed, so the
laws apply to rectangular maps.

## Main declarations

* `ContinuousLinearMap.singularValue`: the approximation numbers `aₙ(T)`.
* `ContinuousLinearMap.isGLB_singularValue`: `aₙ(T)` is the infimum of `‖T - R‖` over bounded
  maps `R` of rank at most `n`.
* `ContinuousLinearMap.singularValue_zero`: `a₀(T) = ‖T‖`.
* `ContinuousLinearMap.antitone_singularValue`: `n ↦ aₙ(T)` is antitone.
* `ContinuousLinearMap.singularValue_add_index_le`: `a_{m+n}(S + T) ≤ aₘ(S) + aₙ(T)`.
* `ContinuousLinearMap.singularValue_comp_add_le_mul`: `a_{m+n}(S T) ≤ aₘ(S) aₙ(T)`.
* `ContinuousLinearMap.singularValue_comp_comp_le`: `aₙ(A T B) ≤ ‖A‖ aₙ(T) ‖B‖`.
* `ContinuousLinearMap.singularValue_smul`: `aₙ(c T) = ‖c‖ aₙ(T)`.
* `ContinuousLinearMap.lipschitzWith_singularValue`: `T ↦ aₙ(T)` is `1`-Lipschitz.
* `ContinuousLinearMap.kyFanGauge`: the Ky Fan gauge `Kₖ(T) = ∑_{n<k} aₙ(T)`.

## References

* A. Pietsch, *Eigenvalues and s-Numbers*, Cambridge Studies in Advanced Mathematics 13,
  Cambridge University Press (1987), §§2.2–2.3.
* I. C. Gohberg, M. G. Krein, *Introduction to the Theory of Linear Nonselfadjoint Operators*,
  Translations of Mathematical Monographs 18, AMS (1969), Chapter II.
-/

public section

open scoped NNReal

namespace ContinuousLinearMap

variable {𝕜 E F G H : Type*} [NontriviallyNormedField 𝕜]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]
  [SeminormedAddCommGroup G] [NormedSpace 𝕜 G] [SeminormedAddCommGroup H] [NormedSpace 𝕜 H]

/-! ### The approximation numbers -/

/-- The `n`-th approximation number `aₙ(T)` of a bounded linear map `T`: the infimum of the
operator norms `‖T - R‖` over all bounded linear maps `R` of rank at most `n`. The indexing is
zero-based, so `a₀(T) = ‖T‖` (`singularValue_zero`).

On finite-dimensional Hilbert spaces these are the singular values of `T`. -/
noncomputable def singularValue (T : E →L[𝕜] F) (n : ℕ) : ℝ≥0 :=
  ⨅ R : {R : E →L[𝕜] F // R.rank ≤ n}, ‖T - R.1‖₊

/-- `aₙ(T)` is the infimum of `‖T - R‖` over the bounded maps `R` of rank at most `n`. -/
theorem singularValue_def (T : E →L[𝕜] F) (n : ℕ) :
    T.singularValue n = ⨅ R : {R : E →L[𝕜] F // R.rank ≤ n}, ‖T - R.1‖₊ := by
  rw [singularValue]

private instance (n : ℕ) : Nonempty {R : E →L[𝕜] F // R.rank ≤ n} :=
  ⟨⟨0, by simp⟩⟩

/-- **Approximation upper bound.** Every bounded map of rank at most `n` bounds `aₙ(T)`. -/
theorem singularValue_le_nnnorm_sub (T : E →L[𝕜] F) {n : ℕ} {R : E →L[𝕜] F} (hR : R.rank ≤ n) :
    T.singularValue n ≤ ‖T - R‖₊ := by
  unfold singularValue
  exact ciInf_le (f := fun R : {R : E →L[𝕜] F // R.rank ≤ n} ↦ ‖T - R.1‖₊)
    (OrderBot.bddBelow _) ⟨R, hR⟩

/-- **Lower-bound characterization.** `c ≤ aₙ(T)` exactly when `c ≤ ‖T - R‖` for every bounded
map `R` of rank at most `n`. -/
theorem le_singularValue_iff {T : E →L[𝕜] F} {n : ℕ} {c : ℝ≥0} :
    c ≤ T.singularValue n ↔ ∀ R : E →L[𝕜] F, R.rank ≤ n → c ≤ ‖T - R‖₊ := by
  unfold singularValue
  exact le_ciInf_iff (f := fun R : {R : E →L[𝕜] F // R.rank ≤ n} ↦ ‖T - R.1‖₊)
    (OrderBot.bddBelow _) |>.trans Subtype.forall

/-- **Infimum formula.** `aₙ(T)` is the greatest lower bound of the operator norms `‖T - R‖`
over the bounded maps `R` of rank at most `n`. -/
theorem isGLB_singularValue (T : E →L[𝕜] F) (n : ℕ) :
    IsGLB {x | ∃ R : E →L[𝕜] F, R.rank ≤ n ∧ ‖T - R‖₊ = x} (T.singularValue n) := by
  refine ⟨?_, fun c hc ↦ le_singularValue_iff.mpr fun R hR ↦ hc ⟨R, hR, rfl⟩⟩
  rintro _ ⟨R, hR, rfl⟩
  exact T.singularValue_le_nnnorm_sub hR

/-- **Near-best approximants.** If `aₙ(T) < c`, some bounded map of rank at most `n` lies within
operator-norm distance `c` of `T`. -/
theorem exists_rank_le_nnnorm_sub_lt {T : E →L[𝕜] F} {n : ℕ} {c : ℝ≥0}
    (h : T.singularValue n < c) : ∃ R : E →L[𝕜] F, R.rank ≤ n ∧ ‖T - R‖₊ < c := by
  unfold singularValue at h
  obtain ⟨⟨R, hR⟩, hlt⟩ := exists_lt_of_ciInf_lt h
  exact ⟨R, hR, hlt⟩

/-- **Best approximants.** A bounded map of rank at most `n` that is at least as close to `T` as
every other such map attains the infimum: its distance to `T` is `aₙ(T)`. -/
theorem singularValue_eq_nnnorm_sub {T R : E →L[𝕜] F} {n : ℕ} (hR : R.rank ≤ n)
    (hmin : ∀ R' : E →L[𝕜] F, R'.rank ≤ n → ‖T - R‖₊ ≤ ‖T - R'‖₊) :
    T.singularValue n = ‖T - R‖₊ :=
  (T.singularValue_le_nnnorm_sub hR).antisymm (le_singularValue_iff.mpr hmin)

/-- The approximation numbers are bounded by the operator norm. -/
theorem singularValue_le_nnnorm (T : E →L[𝕜] F) (n : ℕ) : T.singularValue n ≤ ‖T‖₊ := by
  simpa using T.singularValue_le_nnnorm_sub (R := 0) (by simp)

/-- **Zeroth approximation number.** `a₀(T) = ‖T‖`, since only the zero map has rank `0`. -/
@[simp]
theorem singularValue_zero (T : E →L[𝕜] F) : T.singularValue 0 = ‖T‖₊ := by
  refine (T.singularValue_le_nnnorm 0).antisymm (le_singularValue_iff.mpr fun R hR ↦ ?_)
  have hR0 : (R : E →ₗ[𝕜] F) = 0 := LinearMap.range_eq_bot.mp <|
    Submodule.rank_eq_zero.mp (le_antisymm (by exact_mod_cast hR) bot_le)
  simp [coe_injective (hR0.trans toLinearMap_zero.symm)]

/-- The approximation numbers form an antitone sequence. -/
theorem antitone_singularValue (T : E →L[𝕜] F) : Antitone T.singularValue :=
  fun _ _ hmn ↦ le_singularValue_iff.mpr fun _ hR ↦
    T.singularValue_le_nnnorm_sub (hR.trans (by exact_mod_cast hmn))

/-- The approximation numbers of the zero map vanish. -/
@[simp]
theorem zero_singularValue (n : ℕ) : (0 : E →L[𝕜] F).singularValue n = 0 :=
  le_antisymm (by simpa using (0 : E →L[𝕜] F).singularValue_le_nnnorm n) bot_le

/-- **Mixed-index additive inequality.** `a_{m+n}(S + T) ≤ aₘ(S) + aₙ(T)`. -/
theorem singularValue_add_index_le (S T : E →L[𝕜] F) (m n : ℕ) :
    (S + T).singularValue (m + n) ≤ S.singularValue m + T.singularValue n :=
  NNReal.le_iInf_add_iInf fun R₁ R₂ ↦
    ((S + T).singularValue_le_nnnorm_sub (R := R₁.1 + R₂.1) <| by
      rw [Nat.cast_add]
      exact (LinearMap.rank_add_le _ _).trans (add_le_add R₁.2 R₂.2)).trans <| by
      rw [add_sub_add_comm]
      exact nnnorm_add_le _ _

/-- **Perturbative triangle bound.** `aₙ(S + T) ≤ aₙ(S) + ‖T‖`. -/
theorem singularValue_add_le (S T : E →L[𝕜] F) (n : ℕ) :
    (S + T).singularValue n ≤ S.singularValue n + ‖T‖₊ := by
  simpa using S.singularValue_add_index_le T n 0

/-- **Lipschitz bound at a fixed index.** `|aₙ(S) - aₙ(T)| ≤ ‖S - T‖`. -/
theorem abs_singularValue_sub_singularValue_le (S T : E →L[𝕜] F) (n : ℕ) :
    |(S.singularValue n : ℝ) - T.singularValue n| ≤ ‖S - T‖ := by
  have key (S T : E →L[𝕜] F) : (S.singularValue n : ℝ) ≤ T.singularValue n + ‖S - T‖ := by
    have := T.singularValue_add_le (S - T) n
    rw [add_sub_cancel] at this
    exact_mod_cast this
  rw [abs_sub_le_iff]
  exact ⟨sub_le_iff_le_add'.mpr (key S T), sub_le_iff_le_add'.mpr (norm_sub_rev T S ▸ key T S)⟩

/-- **Lipschitz continuity.** At each index, `T ↦ aₙ(T)` is `1`-Lipschitz in operator norm. -/
theorem lipschitzWith_singularValue (n : ℕ) :
    LipschitzWith 1 fun T : E →L[𝕜] F ↦ T.singularValue n :=
  LipschitzWith.of_dist_le_mul fun S T ↦ by
    simpa [NNReal.dist_eq, dist_eq_norm] using abs_singularValue_sub_singularValue_le S T n

/-- **Norm continuity.** At each index, `T ↦ aₙ(T)` is continuous in operator norm. -/
@[fun_prop]
theorem continuous_singularValue (n : ℕ) : Continuous fun T : E →L[𝕜] F ↦ T.singularValue n :=
  (lipschitzWith_singularValue n).continuous

/-- Postcomposition with a bounded map scales approximation numbers by at most its norm. -/
theorem singularValue_comp_le_left (A : F →L[𝕜] G) (T : E →L[𝕜] F) (n : ℕ) :
    (A.comp T).singularValue n ≤ ‖A‖₊ * T.singularValue n := by
  unfold singularValue
  rw [NNReal.mul_iInf]
  refine le_ciInf fun R ↦ ?_
  have hR := (LinearMap.lift_rank_comp_le_right (R.1 : E →ₗ[𝕜] F) (A : F →ₗ[𝕜] G)).trans
    (Cardinal.lift_le.mpr R.2)
  rw [Cardinal.lift_natCast, Cardinal.lift_le_nat_iff] at hR
  refine ((A.comp T).singularValue_le_nnnorm_sub (R := A.comp R.1) hR).trans ?_
  rw [← comp_sub]
  exact opNNNorm_comp_le _ _

/-- Precomposition with a bounded map scales approximation numbers by at most its norm. -/
theorem singularValue_comp_le_right (T : F →L[𝕜] G) (B : E →L[𝕜] F) (n : ℕ) :
    (T.comp B).singularValue n ≤ T.singularValue n * ‖B‖₊ := by
  unfold singularValue
  rw [NNReal.iInf_mul]
  refine le_ciInf fun R ↦ ((T.comp B).singularValue_le_nnnorm_sub (R := R.1.comp B)
    ((LinearMap.rank_comp_le_left _ _).trans R.2)).trans ?_
  rw [← sub_comp]
  exact opNNNorm_comp_le _ _

/-- **Two-sided ideal inequality.** `aₙ(A T B) ≤ ‖A‖ aₙ(T) ‖B‖`. -/
theorem singularValue_comp_comp_le (A : G →L[𝕜] H) (T : F →L[𝕜] G) (B : E →L[𝕜] F) (n : ℕ) :
    (A.comp (T.comp B)).singularValue n ≤ ‖A‖₊ * T.singularValue n * ‖B‖₊ :=
  (A.singularValue_comp_le_left _ n).trans <| by
    rw [mul_assoc]
    gcongr
    exact T.singularValue_comp_le_right B n

/-- **Mixed-index product inequality.** `a_{m+n}(S T) ≤ aₘ(S) aₙ(T)`. -/
theorem singularValue_comp_add_le_mul (S : F →L[𝕜] G) (T : E →L[𝕜] F) (m n : ℕ) :
    (S.comp T).singularValue (m + n) ≤ S.singularValue m * T.singularValue n := by
  unfold singularValue
  rw [NNReal.iInf_mul]
  refine le_ciInf fun R₁ ↦ ?_
  rw [NNReal.mul_iInf]
  refine le_ciInf fun R₂ ↦ ?_
  -- `S T - (R₁ T + (S - R₁) R₂) = (S - R₁)(T - R₂)`, and the subtracted map has rank `≤ m + n`.
  have h₂ := (LinearMap.lift_rank_comp_le_right (R₂.1 : E →ₗ[𝕜] F)
    ((S - R₁.1 : F →L[𝕜] G) : F →ₗ[𝕜] G)).trans (Cardinal.lift_le.mpr R₂.2)
  rw [Cardinal.lift_natCast, Cardinal.lift_le_nat_iff] at h₂
  have hrank : (R₁.1.comp T + (S - R₁.1).comp R₂.1).rank ≤ ↑(m + n) := by
    rw [Nat.cast_add]
    exact (LinearMap.rank_add_le _ _).trans
      (add_le_add ((LinearMap.rank_comp_le_left _ _).trans R₁.2) h₂)
  refine ((S.comp T).singularValue_le_nnnorm_sub hrank).trans ?_
  have : S.comp T - (R₁.1.comp T + (S - R₁.1).comp R₂.1) = (S - R₁.1).comp (T - R₂.1) := by
    simp only [comp_sub, sub_comp]
    abel
  rw [this]
  exact opNNNorm_comp_le _ _

/-- **Scalar homogeneity.** `aₙ(c T) = ‖c‖ aₙ(T)`. -/
@[simp]
theorem singularValue_smul (c : 𝕜) (T : E →L[𝕜] F) (n : ℕ) :
    (c • T).singularValue n = ‖c‖₊ * T.singularValue n := by
  have hle (c : 𝕜) (T : E →L[𝕜] F) : (c • T).singularValue n ≤ ‖c‖₊ * T.singularValue n := by
    unfold singularValue
    rw [NNReal.mul_iInf]
    refine le_ciInf fun R ↦ ((c • T).singularValue_le_nnnorm_sub (R := c • R.1)
      ((Submodule.rank_mono (LinearMap.range_smul_le_range _ c)).trans R.2)).trans ?_
    rw [← smul_sub]
    exact nnnorm_smul_le _ _
  refine (hle c T).antisymm ?_
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  calc ‖c‖₊ * T.singularValue n = ‖c‖₊ * (c⁻¹ • c • T).singularValue n := by
        rw [inv_smul_smul₀ hc]
    _ ≤ ‖c‖₊ * (‖c⁻¹‖₊ * (c • T).singularValue n) := by gcongr; exact hle _ _
    _ = (c • T).singularValue n := by
        rw [← mul_assoc, nnnorm_inv, mul_inv_cancel₀ (nnnorm_ne_zero_iff.mpr hc), one_mul]

/-! ### The Ky Fan gauge -/

/-- The Ky Fan gauge `Kₖ(T) = ∑_{n<k} aₙ(T)`: the sum of the first `k` approximation numbers
of `T`. -/
noncomputable def kyFanGauge (T : E →L[𝕜] F) (k : ℕ) : ℝ≥0 :=
  ∑ n ∈ Finset.range k, T.singularValue n

/-- `Kₖ(T)` is the sum of the approximation numbers `aₙ(T)` for `n < k`. -/
theorem kyFanGauge_def (T : E →L[𝕜] F) (k : ℕ) :
    T.kyFanGauge k = ∑ n ∈ Finset.range k, T.singularValue n := by
  rw [kyFanGauge]

/-- The empty Ky Fan gauge vanishes. -/
@[simp]
theorem kyFanGauge_zero (T : E →L[𝕜] F) : T.kyFanGauge 0 = 0 := by
  simp [kyFanGauge]

/-- Each Ky Fan gauge adds the next approximation number to the previous one. -/
theorem kyFanGauge_succ (T : E →L[𝕜] F) (k : ℕ) :
    T.kyFanGauge (k + 1) = T.kyFanGauge k + T.singularValue k :=
  Finset.sum_range_succ _ _

/-- The first Ky Fan gauge is the operator norm: `K₁(T) = ‖T‖`. -/
@[simp]
theorem kyFanGauge_one (T : E →L[𝕜] F) : T.kyFanGauge 1 = ‖T‖₊ := by
  simp [kyFanGauge_succ]

/-- The Ky Fan gauge is monotone in the number of summands. -/
theorem monotone_kyFanGauge (T : E →L[𝕜] F) : Monotone T.kyFanGauge :=
  fun _ _ hkl ↦ Finset.sum_le_sum_of_subset (Finset.range_mono hkl)

/-- **Ky Fan lower comparison.** For `0 < k`, `‖T‖ ≤ Kₖ(T)`. -/
theorem nnnorm_le_kyFanGauge (T : E →L[𝕜] F) {k : ℕ} (hk : 0 < k) : ‖T‖₊ ≤ T.kyFanGauge k :=
  T.kyFanGauge_one ▸ T.monotone_kyFanGauge hk

/-- **Ky Fan upper comparison.** `Kₖ(T) ≤ k ‖T‖`. -/
theorem kyFanGauge_le_mul_nnnorm (T : E →L[𝕜] F) (k : ℕ) : T.kyFanGauge k ≤ k * ‖T‖₊ := by
  simpa [kyFanGauge] using
    Finset.sum_le_sum fun n (_ : n ∈ Finset.range k) ↦ T.singularValue_le_nnnorm n

/-- **Ky Fan homogeneity.** `Kₖ(c T) = ‖c‖ Kₖ(T)`. -/
@[simp]
theorem kyFanGauge_smul (c : 𝕜) (T : E →L[𝕜] F) (k : ℕ) :
    (c • T).kyFanGauge k = ‖c‖₊ * T.kyFanGauge k := by
  simp [kyFanGauge, Finset.mul_sum]

/-- **Ky Fan two-sided ideal inequality.** `Kₖ(A T B) ≤ ‖A‖ Kₖ(T) ‖B‖`. -/
theorem kyFanGauge_comp_comp_le (A : G →L[𝕜] H) (T : F →L[𝕜] G) (B : E →L[𝕜] F) (k : ℕ) :
    (A.comp (T.comp B)).kyFanGauge k ≤ ‖A‖₊ * T.kyFanGauge k * ‖B‖₊ := by
  simp only [kyFanGauge, Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_le_sum fun n _ ↦ singularValue_comp_comp_le A T B n

end ContinuousLinearMap
