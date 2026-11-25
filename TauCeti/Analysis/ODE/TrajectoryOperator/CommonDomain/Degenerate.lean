/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.ODE.TrajectoryOperator.CommonDomain.Fredholm
import TauCeti.Analysis.Calculus.BumpFunction.Escaping
import TauCeti.Analysis.Normed.Operator.ClosedRange
import TauCeti.Analysis.Sobolev.GraphStep.Coordinates
import TauCeti.MeasureTheory.Function.LocallyIntegrable
import TauCeti.MeasureTheory.Function.Lp.Norm

/-!
# The trajectory operator over a common domain with a degenerate limit is not Fredholm

Let `ι : D →L[ℝ] H` map a Banach space `D` into a Banach space `H`, and let `A` be an essentially
bounded family of operators `D →L[ℝ] H`, given as a class `AL` in `L∞(ℝ, D →L[ℝ] H)`. The
operator `D_A u = (ι ∘ u)' + A(s) u(s)` from `L²(ℝ, D) ∩ W^{1,2}(ℝ, H)` to `L²(ℝ, H)` is
`TauCeti.WeakDerivStep.familyDomainTrajectoryOperator ι AL`. A typical case is the linearized
Floer operator, where `A(s) = J₀ ∂ₜ + S(s, t)` acts on paths in `t`, with `D = H¹` and `H = L²`.

If `A(s) a → 0` at `+∞` or at `-∞` for some `a ≠ 0`, for instance because `A` converges to an
operator `B` with `B a = 0`, then `D_A` is not Fredholm
(`TauCeti.WeakDerivStep.not_isFredholm_familyDomainTrajectoryOperator_of_tendsto_atTop` and
`..._atBot`). No symmetry of `A`, compactness of `ι` or injectivity of `ι` is needed. In particular,
if `A(s) x → B x` at an end for every `x` and `D_A` is Fredholm, then `B` is injective
(`TauCeti.WeakDerivStep.injective_of_isFredholm_familyDomainTrajectoryOperator_of_tendsto_atTop`
and `..._atBot`).

The proof constructs an escaping approximate kernel, as in the case of bounded operators on one
Banach space (`TauCeti.Analysis.ODE.TrajectoryOperator.Degenerate`). Take smooth compactly supported
profiles `φₙ` on `ℝ`, with `∫ φₙ² = 1` and `∫ φₙ'² → 0`, pairwise disjoint supports, and supports
escaping to the end at which `A(s) a` tends to `0`
(`TauCeti.exists_seq_contDiff_hasCompactSupport_escaping_atTop`). The paths
`uₙ = φₙ • a` (`TauCeti.WeakDerivStep.smulRightBaseW1pL`) are bounded in the graph norm, and
`D_A uₙ = φₙ' • ι a + φₙ • A(s) a` tends to `0` in `L²`, while `‖uₙ - uₘ‖_{L²(ℝ, D)} = √2 ‖a‖` for
`n ≠ m`. A Fredholm operator has closed range and finite-dimensional complemented kernel, so a
bounded sequence on which it tends to `0` has a convergent subsequence
(`ContinuousLinearMap.tendsto_subseq_of_cauchySeq_comp`), so its terms cannot stay a fixed distance
apart (`ContinuousLinearMap.not_cauchySeq_comp_of_le_dist`); the terms of `uₙ` do.

Combined with the Fredholm theorem
`TauCeti.WeakDerivStep.isFredholm_familyDomainTrajectoryOperator`, this characterizes the Fredholm
property for a compact `ι`: if `A` converges in norm to limits `B±` at `±∞` that are `ι`-symmetric
and Fredholm of index zero, as for self-adjoint operators with compact resolvent, and `A(s) - B⁺`
is bounded through `ι` on every bounded interval, then `D_A` is Fredholm exactly when both limits
are invertible
(`TauCeti.WeakDerivStep.isFredholm_familyDomainTrajectoryOperator_iff`).

## Main results

* `TauCeti.WeakDerivStep.not_isFredholm_familyDomainTrajectoryOperator_of_tendsto_atTop` and
  `TauCeti.WeakDerivStep.not_isFredholm_familyDomainTrajectoryOperator_of_tendsto_atBot`:
  a nonzero `a` with `A(s) a → 0` at an end shows that `D_A` is not Fredholm.
* `TauCeti.WeakDerivStep.injective_of_isFredholm_familyDomainTrajectoryOperator_of_tendsto_atTop`
  and
  `TauCeti.WeakDerivStep.injective_of_isFredholm_familyDomainTrajectoryOperator_of_tendsto_atBot`:
  if `D_A` is Fredholm, then every pointwise limit of `A` at an end is injective.
* `TauCeti.WeakDerivStep.isFredholm_familyDomainTrajectoryOperator_iff`: for compact `ι`, `A`
  converging in norm to `ι`-symmetric Fredholm limits of index zero, and `A(s) - B⁺` bounded
  through `ι` on bounded intervals, `D_A` is Fredholm iff both limits are invertible.

## References

* J. Robbin and D. Salamon, *The spectral flow and the Maslov index*, Bull. London Math. Soc.
  **27** (1995), 1–33, Theorem A (the operator `d/ds + A(s)` is Fredholm exactly when the limits
  are invertible).
* D. Salamon, *Lectures on Floer homology*, IAS/Park City Math. Ser. **7** (1999), Lecture 2.
-/

public section

noncomputable section

namespace TauCeti.WeakDerivStep

open Filter _root_.MeasureTheory Set TopologicalSpace
open scoped ENNReal Topology Distributions InnerProductSpace

local notation "μ₀" => (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))

section Banach

variable {D H : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D] [CompleteSpace D]
  [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H] {ι : D →L[ℝ] H}
  {A : ℝ → D →L[ℝ] H} {AL : Lp (D →L[ℝ] H) ∞ μ₀}

omit [CompleteSpace D] in
/-- The squared `L²` norm of `D_A` on the mode `φ • a` of a test function `φ` is at most
`2 ‖ι a‖² ∫ φ'² + 2 ε² ∫ φ²` when `‖A(s) a‖ ≤ ε` on the support of `φ`. -/
private theorem norm_familyDomainTrajectoryOperator_smulRightBaseW1pL_sq_le
    (hAL : AL =ᵐ[μ₀] A) (a : D) (φ : 𝓓((⊤ : Opens ℝ), ℝ)) {ε : ℝ}
    (hA : ∀ s, φ s ≠ 0 → ‖A s a‖ ≤ ε) :
    ‖familyDomainTrajectoryOperator ι AL
        (smulRightBaseW1pL ι a (W1p.ofTestFunctionₗ volume ⊤ 2 φ))‖ ^ 2 ≤
      2 * ‖ι a‖ ^ 2 * (∫ s, deriv φ s ^ 2) + 2 * ε ^ 2 * ∫ s, φ s ^ 2 := by
  have hint :=
    φ.continuous.integrable_sq_of_hasCompactSupport (μ := volume) φ.hasCompactSupport
  have hintd := φ.contDiff.integrable_deriv_sq_of_hasCompactSupport (μ := volume)
    φ.hasCompactSupport (by simp)
  have hle : ∀ᵐ s ∂μ₀, ‖familyDomainTrajectoryOperator ι AL
      (smulRightBaseW1pL ι a (W1p.ofTestFunctionₗ volume ⊤ 2 φ)) s‖ ^ 2 ≤
        2 * ‖ι a‖ ^ 2 * deriv φ s ^ 2 + 2 * ε ^ 2 * φ s ^ 2 := by
    filter_upwards [familyDomainTrajectoryOperator_smulRightBaseW1pL_ae ι AL a
        (W1p.ofTestFunctionₗ volume ⊤ 2 φ), hAL,
      ae_restrict_of_ae (W1p.gradient_ofTestFunctionₗ_top_ae (mu := volume) (p := 2) φ),
      ae_restrict_of_ae (W1p.value_ofTestFunctionₗ_top_ae (mu := volume) (p := 2) φ)]
      with s hs hAs hg hv
    rw [hs, hAs, hg, hv, gradient_eq_deriv', RCLike.inner_apply,
      RCLike.conj_to_real, one_mul]
    refine ((pow_le_pow_left₀ (norm_nonneg _) (norm_add_le _ _) 2).trans add_sq_le).trans ?_
    simp only [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    have hε : φ s ^ 2 * ‖A s a‖ ^ 2 ≤ φ s ^ 2 * ε ^ 2 := by
      by_cases h0 : φ s = 0
      · simp [h0]
      · exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hA s h0) 2)
          (sq_nonneg _)
    linarith
  rw [← Lp.integral_norm_sq_eq_norm_sq]
  refine (integral_mono_ae (Lp.memLp _).norm.integrable_sq
    ((hintd.const_mul _).add (hint.const_mul _)).restrict hle).trans_eq ?_
  rw [Opens.coe_top, Measure.restrict_univ]
  simp only [Pi.add_apply]
  rw [integral_add (hintd.const_mul _) (hint.const_mul _), integral_const_mul, integral_const_mul]

omit [CompleteSpace D] in
/-- The squared graph norm of the mode `φ • a` of a test function `φ` is at most
`‖φ ↦ φ • a‖² (∫ φ² + ∫ φ'²)`. -/
private theorem norm_smulRightBaseW1pL_ofTestFunctionₗ_sq_le (ι : D →L[ℝ] H) (a : D)
    (φ : 𝓓((⊤ : Opens ℝ), ℝ)) :
    ‖smulRightBaseW1pL ι a (W1p.ofTestFunctionₗ volume ⊤ 2 φ)‖ ^ 2 ≤
      ‖smulRightBaseW1pL (mu := (volume : Measure ℝ)) (Omega := ⊤) (p := 2) ι a‖ ^ 2 *
        ((∫ s, φ s ^ 2) + ∫ s, deriv φ s ^ 2) := by
  have hw : ‖W1p.ofTestFunctionₗ volume ⊤ 2 φ‖ ^ 2 = (∫ s, φ s ^ 2) + ∫ s, deriv φ s ^ 2 := by
    rw [W1p.norm_sq_eq_norm_value_sq_add_norm_gradient_sq,
      W1p.norm_value_ofTestFunctionₗ_top_sq, W1p.norm_gradient_ofTestFunctionₗ_top_sq]
    simp only [← norm_deriv_eq_norm_fderiv, Real.norm_eq_abs, sq_abs]
  rw [← hw, ← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (ContinuousLinearMap.le_opNorm _ _) 2

omit [CompleteSpace D] in
/-- The modes `φ • a` and `ψ • a` of test functions with disjoint supports are at squared `L²`
distance `(∫ φ² + ∫ ψ²) ‖a‖²`. -/
private theorem norm_prev_smulRightBaseW1pL_sub_sq (ι : D →L[ℝ] H) (a : D)
    {φ ψ : 𝓓((⊤ : Opens ℝ), ℝ)} (hdisj : ∀ s, φ s * ψ s = 0) :
    ‖prev _ (smulRightBaseW1pL ι a (W1p.ofTestFunctionₗ volume ⊤ 2 φ)) -
        prev _ (smulRightBaseW1pL ι a (W1p.ofTestFunctionₗ volume ⊤ 2 ψ))‖ ^ 2 =
      ((∫ s, φ s ^ 2) + ∫ s, ψ s ^ 2) * ‖a‖ ^ 2 := by
  simp only [← prevL_apply, ← map_sub]
  rw [prevL_apply, norm_prev_smulRightBaseW1pL_ofTestFunctionₗ_sq, FunLike.coe_sub,
    integral_congr_ae (g := fun s ↦ φ s ^ 2 + ψ s ^ 2) (.of_forall fun s ↦ by
      simp only [Pi.sub_apply]
      linear_combination (-2) * hdisj s),
    integral_add (φ.continuous.integrable_sq_of_hasCompactSupport φ.hasCompactSupport)
      (ψ.continuous.integrable_sq_of_hasCompactSupport ψ.hasCompactSupport)]

/-- **The escaping approximate kernel.** Let `φₙ` be smooth compactly supported functions with
`∫ φₙ² = 1`, `∫ φₙ'² → 0` and pairwise disjoint supports, and suppose that `‖A(s) a‖ ≤ εₙ` on the
support of `φₙ`, with `εₙ → 0` and `a ≠ 0`. Then the paths `φₙ • a` show that `D_A` is not
Fredholm. -/
private theorem not_isFredholm_familyDomainTrajectoryOperator_of_seq (hAL : AL =ᵐ[μ₀] A)
    {a : D} (ha : a ≠ 0) {φ : ℕ → ℝ → ℝ} (hφ : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (φ n))
    (hφc : ∀ n, HasCompactSupport (φ n)) (hφ1 : ∀ n, ∫ s, φ n s ^ 2 = 1)
    (hφ' : Tendsto (fun n ↦ ∫ s, deriv (φ n) s ^ 2) atTop (𝓝 0))
    (hdisj : ∀ m n, m ≠ n → ∀ s, φ m s * φ n s = 0) {ε : ℕ → ℝ} (hε : Tendsto ε atTop (𝓝 0))
    (hA : ∀ n s, φ n s ≠ 0 → ‖A s a‖ ≤ ε n) :
    ¬ (familyDomainTrajectoryOperator (p := 2) ι AL).IsFredholm := by
  intro hF
  let ψ (n : ℕ) : 𝓓((⊤ : Opens ℝ), ℝ) := ⟨φ n, hφ n, hφc n, subset_univ _⟩
  have hψ (n : ℕ) : (ψ n : ℝ → ℝ) = φ n := TestFunction.coe_mk
  let x (n : ℕ) := smulRightBaseW1pL ι a (W1p.ofTestFunctionₗ volume ⊤ 2 (ψ n))
  set T := familyDomainTrajectoryOperator (p := 2) ι AL
  set C := ‖smulRightBaseW1pL (mu := (volume : Measure ℝ)) (Omega := ⊤) (p := 2) ι a‖
  -- The paths `φₙ • a` are bounded in the graph norm.
  obtain ⟨B, hB⟩ := hφ'.bddAbove_range
  have hbdd : Bornology.IsBounded (Set.range x) := by
    refine isBounded_iff_forall_norm_le.2
      ⟨C ^ 2 * (1 + B) + 1, Set.forall_mem_range.2 fun n ↦ ?_⟩
    have hx := norm_smulRightBaseW1pL_ofTestFunctionₗ_sq_le ι a (ψ n)
    rw [hψ, hφ1] at hx
    have hB' : C ^ 2 * (1 + ∫ s, deriv (φ n) s ^ 2) ≤ C ^ 2 * (1 + B) :=
      mul_le_mul_of_nonneg_left (by linarith [hB (Set.mem_range_self n)]) (sq_nonneg _)
    nlinarith [sq_nonneg (‖x n‖ - 1), norm_nonneg (x n)]
  -- The operator tends to `0` along them.
  have hTx : Tendsto (T ∘ x) atTop (𝓝 0) := by
    have hbound : Tendsto (fun n ↦ 2 * ‖ι a‖ ^ 2 * (∫ s, deriv (φ n) s ^ 2) + 2 * ε n ^ 2 * 1)
        atTop (𝓝 0) := by
      simpa using (hφ'.const_mul (2 * ‖ι a‖ ^ 2)).add ((hε.pow 2).const_mul 2)
    have hsq : Tendsto (fun n ↦ ‖T (x n)‖ ^ 2) atTop (𝓝 0) :=
      squeeze_zero (fun _ ↦ by positivity) (fun n ↦ by
        simpa only [hψ, hφ1] using
          norm_familyDomainTrajectoryOperator_smulRightBaseW1pL_sq_le hAL a (ψ n)
            (fun s hs ↦ hA n s (by rwa [hψ] at hs))) hbound
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simpa [Function.comp_def, Real.sqrt_sq (norm_nonneg _)] using
      (Real.continuous_sqrt.tendsto 0).comp hsq
  -- A Fredholm operator would give a convergent subsequence, but distinct paths stay `√2 ‖a‖`
  -- apart in `L²(ℝ, D)`.
  refine T.not_cauchySeq_comp_of_le_dist hF.isClosed_range hF.finite_ker hF.closedComplemented_ker
    (prevL _).continuous hbdd (norm_pos_iff.2 ha) (fun i j hij ↦ ?_) hTx.cauchySeq
  have h := norm_prev_smulRightBaseW1pL_sub_sq ι a (φ := ψ i) (ψ := ψ j) fun s ↦ by
    simpa only [hψ] using hdisj i j hij s
  rw [hψ, hψ, hφ1, hφ1] at h
  rw [prevL_apply, prevL_apply, dist_eq_norm]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1
    (by linarith [sq_nonneg ‖a‖])

/-- **A degenerate limit at `+∞` destroys the Fredholm property.** If `A(s) a → 0` as `s → ∞` for
some `a ≠ 0`, for instance because `A` tends to an operator `B` with `B a = 0`, then
`u ↦ (ι ∘ u)' + A u` from `L²(ℝ, D) ∩ W^{1,2}(ℝ, H)` to `L²(ℝ, H)` is not Fredholm. The
coefficient of the operator is any `L∞` class `AL` of `A`. -/
theorem not_isFredholm_familyDomainTrajectoryOperator_of_tendsto_atTop (hAL : AL =ᵐ[μ₀] A)
    {a : D} (ha : a ≠ 0) (hAa : Tendsto (fun s ↦ A s a) atTop (𝓝 0)) :
    ¬ (familyDomainTrajectoryOperator (p := 2) ι AL).IsFredholm := by
  have hS (n : ℕ) : ∃ S, ∀ s ≥ S, ‖A s a‖ ≤ 1 / ((n : ℝ) + 1) :=
    eventually_atTop.1 ((tendsto_zero_iff_norm_tendsto_zero.1 hAa).eventually
      (eventually_le_nhds (by positivity)))
  choose S hS using hS
  obtain ⟨φ, hφ, hφc, hφ1, hφ', hφS, hdisj⟩ :=
    exists_seq_contDiff_hasCompactSupport_escaping_atTop S
  exact not_isFredholm_familyDomainTrajectoryOperator_of_seq hAL ha hφ hφc hφ1 hφ' hdisj
    tendsto_one_div_add_atTop_nhds_zero_nat fun n s hs ↦ hS n s (hφS n s hs)

/-- **A degenerate limit at `-∞` destroys the Fredholm property.** If `A(s) a → 0` as `s → -∞` for
some `a ≠ 0`, for instance because `A` tends to an operator `B` with `B a = 0`, then
`u ↦ (ι ∘ u)' + A u` from `L²(ℝ, D) ∩ W^{1,2}(ℝ, H)` to `L²(ℝ, H)` is not Fredholm. The
coefficient of the operator is any `L∞` class `AL` of `A`. -/
theorem not_isFredholm_familyDomainTrajectoryOperator_of_tendsto_atBot (hAL : AL =ᵐ[μ₀] A)
    {a : D} (ha : a ≠ 0) (hAa : Tendsto (fun s ↦ A s a) atBot (𝓝 0)) :
    ¬ (familyDomainTrajectoryOperator (p := 2) ι AL).IsFredholm := by
  have hS (n : ℕ) : ∃ S, ∀ s ≤ S, ‖A s a‖ ≤ 1 / ((n : ℝ) + 1) :=
    eventually_atBot.1 ((tendsto_zero_iff_norm_tendsto_zero.1 hAa).eventually
      (eventually_le_nhds (by positivity)))
  choose S hS using hS
  obtain ⟨φ, hφ, hφc, hφ1, hφ', hφS, hdisj⟩ :=
    exists_seq_contDiff_hasCompactSupport_escaping_atBot S
  exact not_isFredholm_familyDomainTrajectoryOperator_of_seq hAL ha hφ hφc hφ1 hφ' hdisj
    tendsto_one_div_add_atTop_nhds_zero_nat fun n s hs ↦ hS n s (hφS n s hs)

/-- **A Fredholm trajectory operator has an injective limit at `+∞`.** If `A(s) x → B x` as
`s → ∞` for every `x` and `u ↦ (ι ∘ u)' + A u` is Fredholm, then `B` is injective. -/
theorem injective_of_isFredholm_familyDomainTrajectoryOperator_of_tendsto_atTop
    (hAL : AL =ᵐ[μ₀] A) {B : D →L[ℝ] H} (hAB : ∀ x, Tendsto (fun s ↦ A s x) atTop (𝓝 (B x)))
    (hF : (familyDomainTrajectoryOperator (p := 2) ι AL).IsFredholm) : Function.Injective B := by
  intro x y hxy
  by_contra hne
  have h := hAB (x - y)
  rw [map_sub, hxy, sub_self] at h
  exact not_isFredholm_familyDomainTrajectoryOperator_of_tendsto_atTop hAL (sub_ne_zero.2 hne) h hF

/-- **A Fredholm trajectory operator has an injective limit at `-∞`.** If `A(s) x → B x` as
`s → -∞` for every `x` and `u ↦ (ι ∘ u)' + A u` is Fredholm, then `B` is injective. -/
theorem injective_of_isFredholm_familyDomainTrajectoryOperator_of_tendsto_atBot
    (hAL : AL =ᵐ[μ₀] A) {B : D →L[ℝ] H} (hAB : ∀ x, Tendsto (fun s ↦ A s x) atBot (𝓝 (B x)))
    (hF : (familyDomainTrajectoryOperator (p := 2) ι AL).IsFredholm) : Function.Injective B := by
  intro x y hxy
  by_contra hne
  have h := hAB (x - y)
  rw [map_sub, hxy, sub_self] at h
  exact not_isFredholm_familyDomainTrajectoryOperator_of_tendsto_atBot hAL (sub_ne_zero.2 hne) h hF

end Banach

section Hilbert

variable {D H : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D] [CompleteSpace D]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] {ι : D →L[ℝ] H}
  {A : ℝ → D →L[ℝ] H} {AL : Lp (D →L[ℝ] H) ∞ μ₀} {Bbot Btop : D →L[ℝ] H}

/-- **The Fredholm criterion of Robbin and Salamon over a compactly embedded domain.** Let `ι` be
compact, and let `A(s)` converge to `ι`-symmetric operators `Bbot` at `-∞` and `Btop` at `∞` that
are Fredholm of index zero, differing from `Btop` on every bounded interval by operators bounded
through `ι`. Then `u ↦ (ι ∘ u)' + A u` from `L²(ℝ, D) ∩ W^{1,2}(ℝ, H)` to `L²(ℝ, H)` is Fredholm
if and only if both limits are invertible. -/
theorem isFredholm_familyDomainTrajectoryOperator_iff (hι : IsCompactOperator ι)
    (hSymmbot : ∀ x y : D, ⟪Bbot x, ι y⟫_ℝ = ⟪ι x, Bbot y⟫_ℝ) (hBbotF : Bbot.IsFredholm)
    (hBbot : Bbot.index = 0)
    (hSymmtop : ∀ x y : D, ⟪Btop x, ι y⟫_ℝ = ⟪ι x, Btop y⟫_ℝ) (hBtopF : Btop.IsFredholm)
    (hBtop : Btop.index = 0)
    (hAL : AL =ᵐ[μ₀] A) (hbot : Tendsto A atBot (𝓝 Bbot)) (htop : Tendsto A atTop (𝓝 Btop))
    (hc : ∀ T, ∃ c, ∀ᵐ s ∂volume, s ∈ Ioo (-T) T → ∀ x, ‖(A s - Btop) x‖ ≤ c * ‖ι x‖) :
    (familyDomainTrajectoryOperator (p := 2) ι AL).IsFredholm ↔
      Bbot.IsInvertible ∧ Btop.IsInvertible := by
  refine ⟨fun hF ↦ ⟨?_, ?_⟩, fun ⟨hb, ht⟩ ↦
    isFredholm_familyDomainTrajectoryOperator hι hSymmbot hb hSymmtop ht hAL hbot htop hc⟩
  · exact hBbotF.isInvertible_of_injective_of_index_eq_zero
      (injective_of_isFredholm_familyDomainTrajectoryOperator_of_tendsto_atBot hAL
        (fun x ↦ ((ContinuousLinearMap.apply ℝ H x).continuous.tendsto _).comp hbot) hF) hBbot
  · exact hBtopF.isInvertible_of_injective_of_index_eq_zero
      (injective_of_isFredholm_familyDomainTrajectoryOperator_of_tendsto_atTop hAL
        (fun x ↦ ((ContinuousLinearMap.apply ℝ H x).continuous.tendsto _).comp htop) hF) hBtop

end Hilbert

end TauCeti.WeakDerivStep
