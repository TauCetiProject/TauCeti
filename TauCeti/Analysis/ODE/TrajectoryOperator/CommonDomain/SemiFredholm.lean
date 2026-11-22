/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.ODE.TrajectoryOperator.CommonDomain.Family
public import TauCeti.Analysis.Sobolev.GraphStep.AubinLions
import TauCeti.Analysis.Normed.Operator.Compact.Estimate
import TauCeti.Analysis.Sobolev.Leibniz
import TauCeti.Analysis.SpecialFunctions.SmoothTransition
import TauCeti.MeasureTheory.Function.Lp.Multiplication

/-!
# The semi-Fredholm estimate for the trajectory operator over a compactly embedded domain

Let `ι : D →L[ℝ] H` embed a Banach space `D` into a Hilbert space `H`, and let
`A : ℝ → (D →L[ℝ] H)` be an essentially bounded family of operators, given as a class `AL` in
`L∞(ℝ, D →L[ℝ] H)`. The operator `D_A u = (ι ∘ u)' + A(s) u(s)` from `L²(ℝ, D) ∩ W^{1,2}(ℝ, H)`
to `L²(ℝ, H)` is `TauCeti.WeakDerivStep.familyDomainTrajectoryOperator ι AL`. A typical case is
the linearized Floer operator on a strip or a cylinder in a unitary trivialization, where
`A(s) = J₀ ∂ₜ + S(s, t)` acts on loops or paths in `t`, with `D = H¹` and `H = L²`.

Suppose that `A(s)` converges to invertible `ι`-symmetric operators `B₋` and `B₊`
(`⟪B x, ι y⟫ = ⟪ι x, B y⟫`) as `s → -∞` and `s → ∞`, and that `A(s)` differs from `B₊` by an
operator of lower order, bounded through `ι`: `‖(A(s) - B₊) x‖ ≤ c ‖ι x‖` for almost every `s`.
For `A(s) = J₀ ∂ₜ + S(s, t)` and `B₊ = J₀ ∂ₜ + S₊(t)` this is the bound of the multiplication
operator `S(s, ·) - S₊` on `L²`. Then the semi-Fredholm estimate

`‖u‖ ≤ C (‖D_A u‖ + ‖ι ∘ u‖_{L²((-T, T), H)})`

holds on the whole graph space, for some `C` and `T`
(`exists_forall_norm_le_mul_norm_familyDomainTrajectoryOperator_add_norm_restrictBaseL`).
When `ι` is a compact operator, restricting `ι ∘ u` to `(-T, T)` is compact on the graph space by
the Aubin–Lions lemma `TauCeti.WeakDerivStep.isCompactOperator_restrictBaseL_compLpL`, so Peetre's
lemma gives that `D_A` has finite-dimensional kernel
(`TauCeti.WeakDerivStep.finiteDimensional_ker_familyDomainTrajectoryOperator`) and closed range
(`TauCeti.WeakDerivStep.isClosed_range_familyDomainTrajectoryOperator`). These are the first two
of the three properties making `D_A` Fredholm; the finite dimension of its cokernel is not proved
here.

The estimate is spliced from three pieces by smooth cutoffs `χ₋`, `χ₀ = 1 - χ₋ - χ₊` and `χ₊`
supported in `(-∞, -a]`, `[-a - 1, a + 1]` and `[a, ∞)`. Multiplying a path by a cutoff `χ`
changes `D_A` by the commutator term `χ' (ι ∘ u)`, which lives on the window where `χ'` is
supported. On the two ends, `A(s)` is close to `B±`, and the estimate without error term holds for
paths supported there
(`exists_forall_norm_le_mul_norm_familyDomainTrajectoryOperator_of_tendsto_atTop` and its `atBot`
version). In the middle, `D_A` differs from the invertible autonomous operator of
`B₊` by `A(s) - B₊`, whose action on a path supported in the window is bounded by `c` times the
`L²` norm of `ι ∘ u` there.

## Main results

* `exists_forall_norm_le_mul_norm_familyDomainTrajectoryOperator_add_norm_restrictBaseL`: the
  semi-Fredholm estimate with the window error term.
* `TauCeti.WeakDerivStep.finiteDimensional_ker_familyDomainTrajectoryOperator`: for compact `ι`,
  the kernel of `D_A` is finite dimensional.
* `TauCeti.WeakDerivStep.isClosed_range_familyDomainTrajectoryOperator`: for compact `ι`, the range
  of `D_A` is closed.

## References

* J. Robbin and D. Salamon, *The spectral flow and the Maslov index*, Bull. London Math. Soc.
  **27** (1995), 1–33, §3 (the estimate `‖u‖ ≤ C (‖D_A u‖ + ‖u‖_{L²((-T, T), H)})` for a family
  of self-adjoint operators over a compactly embedded domain).
* D. Salamon, *Lectures on Floer homology*, IAS/Park City Math. Ser. **7** (1999), Lecture 2
  (the operators `∂ₛ + J₀ ∂ₜ + S(s, t)` and their Fredholm theory).
-/

public section

noncomputable section

namespace TauCeti.WeakDerivStep

open Filter _root_.MeasureTheory Set TopologicalSpace
open scoped ENNReal InnerProductSpace Topology ContDiff

local notation "μ₀" => (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))

variable {D H : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D] [CompleteSpace D]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] {ι : D →L[ℝ] H}

/-- Almost everywhere for `μ₀` is almost everywhere on the line. -/
private theorem ae_top_iff {P : ℝ → Prop} : (∀ᵐ s ∂μ₀, P s) ↔ ∀ᵐ s ∂volume, P s := by simp

/-! ### The window term -/

omit [CompleteSpace D] in
/-- An `L²` path bounded pointwise by `c ‖ι (u s)‖` and vanishing off the window `(-b, b)` has norm
at most `c` times the `L²` norm of `ι ∘ u` on the window. -/
private theorem norm_le_mul_norm_restrictBaseL {b c : ℝ} (hc : 0 ≤ c)
    (u : WeakDerivStep volume ⊤ 2 (ι.compLpL 2 μ₀)) {f : Lp H 2 μ₀}
    (hf : ∀ᵐ s ∂volume, ‖f s‖ ≤ c * ‖ι (prev _ u s)‖)
    (hf₀ : ∀ᵐ s ∂volume, s ∉ Ioo (-b) b → f s = 0) :
    ‖f‖ ≤ c * ‖restrictBaseL (ι.compLpL 2 μ₀) (V := ⟨Ioo (-b) b, isOpen_Ioo⟩) le_top u‖ := by
  have hμW : Measure.restrict μ₀ (Ioo (-b) b) = volume.restrict (Ioo (-b) b) := by simp
  -- The `L²` norm of `f` is its `L²` norm on the window, where it is dominated by `ι ∘ u`.
  have hind : (f : ℝ → H) =ᵐ[μ₀] (Ioo (-b) b).indicator f := by
    filter_upwards [ae_top_iff.2 hf₀] with s hs
    by_cases hsW : s ∈ Ioo (-b) b
    · rw [indicator_of_mem hsW]
    · rw [indicator_of_notMem hsW, hs hsW]
  have hR : ∀ᵐ s ∂volume.restrict (Ioo (-b) b), ‖f s‖ ≤
      c * ‖restrictBaseL (ι.compLpL 2 μ₀) (V := ⟨Ioo (-b) b, isOpen_Ioo⟩) le_top u s‖ := by
    have h₂ := ae_restrict_of_ae (s := Ioo (-b) b) (ι.coeFn_compLpL (μ := μ₀) (prev _ u))
    rw [hμW] at h₂
    filter_upwards [restrictBaseL_apply_ae (V := ⟨Ioo (-b) b, isOpen_Ioo⟩) _ le_top u, h₂,
      ae_restrict_of_ae hf] with s h₁ h₂ h₃
    rwa [h₁, h₂]
  have hle := eLpNorm_le_mul_eLpNorm_of_ae_le_mul
    ((Lp.aestronglyMeasurable f).restrict.mono_measure (by rw [hμW])) hR 2
  rw [Lp.norm_def, Lp.norm_def, eLpNorm_congr_ae hind,
    eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_Ioo.nullMeasurableSet, hμW]
  refine (ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (Lp.eLpNorm_ne_top _))
    hle).trans_eq ?_
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hc]

/-! ### Multiplication by a cutoff -/

/-- The `L∞` class of a bounded continuous function on the line. -/
private def linftyOf {f : ℝ → ℝ} (hf : Continuous f) {C : ℝ} (hC : ∀ s, |f s| ≤ C) :
    Lp ℝ ∞ μ₀ :=
  (memLp_top_of_bound hf.aestronglyMeasurable C (ae_of_all _ hC)).toLp f

private theorem linftyOf_ae {f : ℝ → ℝ} (hf : Continuous f) {C : ℝ} (hC : ∀ s, |f s| ≤ C) :
    ⇑(linftyOf hf hC) =ᵐ[μ₀] f :=
  MemLp.coeFn_toLp _

/-- Multiplication by the `L∞` class of `f` acts by `s ↦ f s • g s`. -/
private theorem multiplicationOperator_linftyOf_ae {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : ℝ → ℝ} (hf : Continuous f) {C : ℝ} (hC : ∀ s, |f s| ≤ C)
    (g : Lp E 2 μ₀) :
    ⇑(Lp.multiplicationOperator (linftyOf hf hC) g) =ᵐ[μ₀] fun s ↦ f s • g s := by
  filter_upwards [Lp.multiplicationOperator_ae (linftyOf hf hC) g, linftyOf_ae hf hC]
    with s h₁ h₂
  rw [h₁, h₂]

variable {χ : ℝ → ℝ} {C₀ C₁ : ℝ}

/-- The value `χ u` of the product of a path with a smooth cutoff `χ`. -/
private def cutoffPrev (hχ : ContDiff ℝ ∞ χ) (h₀ : ∀ s, |χ s| ≤ C₀)
    (u : WeakDerivStep volume ⊤ 2 (ι.compLpL 2 μ₀)) : Lp D 2 μ₀ :=
  Lp.multiplicationOperator (linftyOf hχ.continuous h₀) (prev _ u)

/-- The derivative `χ (ι ∘ u)' + χ' (ι ∘ u)` of the product of a path with a smooth cutoff `χ`. -/
private def cutoffDeriv (hχ : ContDiff ℝ ∞ χ) (h₀ : ∀ s, |χ s| ≤ C₀)
    (h₁ : ∀ s, |deriv χ s| ≤ C₁) (u : WeakDerivStep volume ⊤ 2 (ι.compLpL 2 μ₀)) :
    Lp H 2 μ₀ :=
  Lp.multiplicationOperator (linftyOf hχ.continuous h₀)
      ((ContinuousLinearMap.apply ℝ H (1 : ℝ)).compLpL 2 μ₀ (weakFDeriv _ u)) +
    Lp.multiplicationOperator (linftyOf (hχ.continuous_deriv (by simp)) h₁)
      (ι.compLpL 2 μ₀ (prev _ u))

omit [CompleteSpace D] in
private theorem cutoffDeriv_ae (hχ : ContDiff ℝ ∞ χ) (h₀ : ∀ s, |χ s| ≤ C₀)
    (h₁ : ∀ s, |deriv χ s| ≤ C₁) (u : WeakDerivStep volume ⊤ 2 (ι.compLpL 2 μ₀)) :
    ⇑(cutoffDeriv hχ h₀ h₁ u) =ᵐ[μ₀]
      fun s ↦ χ s • weakFDeriv _ u s 1 + deriv χ s • ι (prev _ u s) := by
  filter_upwards [Lp.coeFn_add (Lp.multiplicationOperator (linftyOf hχ.continuous h₀)
        ((ContinuousLinearMap.apply ℝ H (1 : ℝ)).compLpL 2 μ₀ (weakFDeriv _ u)))
        (Lp.multiplicationOperator (linftyOf (hχ.continuous_deriv (by simp)) h₁)
          (ι.compLpL 2 μ₀ (prev _ u))),
      multiplicationOperator_linftyOf_ae hχ.continuous h₀
        ((ContinuousLinearMap.apply ℝ H (1 : ℝ)).compLpL 2 μ₀ (weakFDeriv _ u)),
      multiplicationOperator_linftyOf_ae (hχ.continuous_deriv (by simp)) h₁
        (ι.compLpL 2 μ₀ (prev _ u)),
      (ContinuousLinearMap.apply ℝ H (1 : ℝ)).coeFn_compLpL (weakFDeriv _ u),
      ι.coeFn_compLpL (prev _ u)] with s h₁ h₂ h₃ h₄ h₅
  rw [cutoffDeriv, h₁, Pi.add_apply, h₂, h₃, h₄, h₅, ContinuousLinearMap.apply_apply]

omit [CompleteSpace D] in
/-- **The Leibniz rule on the graph space.** For a smooth cutoff `χ`, the path `ι ∘ (χ u)` has
weak derivative `χ (ι ∘ u)' + χ' (ι ∘ u)`. -/
private theorem hasWeakLineDerivOn_cutoff (hχ : ContDiff ℝ ∞ χ) (h₀ : ∀ s, |χ s| ≤ C₀)
    (h₁ : ∀ s, |deriv χ s| ≤ C₁) (u : WeakDerivStep volume ⊤ 2 (ι.compLpL 2 μ₀)) :
    HasWeakLineDerivOn volume ⊤ (ι.compLpL 2 μ₀ (cutoffPrev hχ h₀ u))
      (cutoffDeriv hχ h₀ h₁ u) 1 := by
  have h := ((hasWeakFDerivOn_base_prev _ u).hasWeakLineDerivOn 1).contDiffOn_smul hχ.contDiffOn
  refine (h.congr_ae ?_).congr_ae_deriv ?_
  · filter_upwards [ι.coeFn_compLpL (cutoffPrev hχ h₀ u),
      multiplicationOperator_linftyOf_ae hχ.continuous h₀ (prev _ u),
      ι.coeFn_compLpL (prev _ u)] with s h₁ h₂ h₃
    rw [h₁, cutoffPrev, h₂, h₃, map_smul]
  · filter_upwards [cutoffDeriv_ae hχ h₀ h₁ u, ι.coeFn_compLpL (prev _ u)] with s h₁ h₂
    rw [h₁, h₂, fderiv_apply_one_eq_deriv]

/-- The product `χ u` of a path `u` of the graph space with a smooth cutoff `χ`. -/
private def cutoffMul (hχ : ContDiff ℝ ∞ χ) (h₀ : ∀ s, |χ s| ≤ C₀) (h₁ : ∀ s, |deriv χ s| ≤ C₁)
    (u : WeakDerivStep volume ⊤ 2 (ι.compLpL 2 μ₀)) :
    WeakDerivStep volume ⊤ 2 (ι.compLpL 2 μ₀) :=
  mkLine _ _ _ (hasWeakLineDerivOn_cutoff hχ h₀ h₁ u)

omit [CompleteSpace D] in
private theorem prev_cutoffMul_ae (hχ : ContDiff ℝ ∞ χ) (h₀ : ∀ s, |χ s| ≤ C₀)
    (h₁ : ∀ s, |deriv χ s| ≤ C₁) (u : WeakDerivStep volume ⊤ 2 (ι.compLpL 2 μ₀)) :
    ⇑(prev _ (cutoffMul hχ h₀ h₁ u)) =ᵐ[μ₀] fun s ↦ χ s • prev _ u s := by
  rw [cutoffMul, prev_mkLine, cutoffPrev]
  exact multiplicationOperator_linftyOf_ae hχ.continuous h₀ (prev _ u)

omit [CompleteSpace D] in
/-- **The commutator of `D_A` with a cutoff.** `D_A (χ u) = χ D_A u + χ' (ι ∘ u)`. -/
private theorem familyDomainTrajectoryOperator_cutoffMul (hχ : ContDiff ℝ ∞ χ)
    (h₀ : ∀ s, |χ s| ≤ C₀) (h₁ : ∀ s, |deriv χ s| ≤ C₁) (AL : Lp (D →L[ℝ] H) ∞ μ₀)
    (u : WeakDerivStep volume ⊤ 2 (ι.compLpL 2 μ₀)) :
    familyDomainTrajectoryOperator ι AL (cutoffMul hχ h₀ h₁ u) =
      Lp.multiplicationOperator (linftyOf hχ.continuous h₀)
          (familyDomainTrajectoryOperator ι AL u) +
        Lp.multiplicationOperator (linftyOf (hχ.continuous_deriv (by simp)) h₁)
          (ι.compLpL 2 μ₀ (prev _ u)) := by
  refine Lp.ext ?_
  filter_upwards [familyDomainTrajectoryOperator_apply_ae ι AL (cutoffMul hχ h₀ h₁ u),
    weakFDeriv_mkLine_apply_one_ae _ _ _ (hasWeakLineDerivOn_cutoff hχ h₀ h₁ u),
    prev_cutoffMul_ae hχ h₀ h₁ u, cutoffDeriv_ae hχ h₀ h₁ u,
    Lp.coeFn_add (Lp.multiplicationOperator (linftyOf hχ.continuous h₀)
        (familyDomainTrajectoryOperator ι AL u))
      (Lp.multiplicationOperator (linftyOf (hχ.continuous_deriv (by simp)) h₁)
        (ι.compLpL 2 μ₀ (prev _ u))),
    multiplicationOperator_linftyOf_ae hχ.continuous h₀ (familyDomainTrajectoryOperator ι AL u),
    multiplicationOperator_linftyOf_ae (hχ.continuous_deriv (by simp)) h₁
      (ι.compLpL 2 μ₀ (prev _ u)),
    ι.coeFn_compLpL (prev _ u), familyDomainTrajectoryOperator_apply_ae ι AL u]
    with s hD hW hP hd hadd hm hm' hι hDu
  rw [hD, hP, cutoffMul, hW, hd, hadd, Pi.add_apply, hm, hm', hι, hDu, map_smul, smul_add]
  abel

omit [CompleteSpace D] in
/-- **The error of a cutoff.** If `|χ| ≤ 1`, `|χ'| ≤ C₁` and `χ'` vanishes off the window
`(-b, b)`, then `‖D_A (χ u)‖ ≤ ‖D_A u‖ + C₁ ‖ι ∘ u‖_{L²((-b, b), H)}`. -/
private theorem norm_familyDomainTrajectoryOperator_cutoffMul_le (hχ : ContDiff ℝ ∞ χ)
    (h₀ : ∀ s, |χ s| ≤ 1) (h₁ : ∀ s, |deriv χ s| ≤ C₁) {b : ℝ}
    (hχ' : ∀ s ∉ Ioo (-b) b, deriv χ s = 0) (AL : Lp (D →L[ℝ] H) ∞ μ₀)
    (u : WeakDerivStep volume ⊤ 2 (ι.compLpL 2 μ₀)) :
    ‖familyDomainTrajectoryOperator ι AL (cutoffMul hχ h₀ h₁ u)‖ ≤
      ‖familyDomainTrajectoryOperator ι AL u‖ +
        C₁ * ‖restrictBaseL (ι.compLpL 2 μ₀) (V := ⟨Ioo (-b) b, isOpen_Ioo⟩) le_top u‖ := by
  have hC₁ : 0 ≤ C₁ := (abs_nonneg _).trans (h₁ 0)
  rw [familyDomainTrajectoryOperator_cutoffMul]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · refine (Lp.norm_le_mul_norm_of_ae_le_mul (c := 1) ?_).trans_eq (one_mul _)
    filter_upwards [multiplicationOperator_linftyOf_ae hχ.continuous h₀
      (familyDomainTrajectoryOperator ι AL u)] with s hs
    rw [hs, norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (h₀ s) (norm_nonneg _)
  · have hm := ae_top_iff.1 (multiplicationOperator_linftyOf_ae
      (hχ.continuous_deriv (by simp)) h₁ (ι.compLpL 2 μ₀ (prev _ u)))
    have hι := ae_top_iff.1 (ι.coeFn_compLpL (μ := μ₀) (prev _ u))
    refine norm_le_mul_norm_restrictBaseL hC₁ u ?_ ?_
    · filter_upwards [hm, hι] with s hs hιs
      rw [hs, hιs, norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (h₁ s) (norm_nonneg _)
    · filter_upwards [hm] with s hs hsW
      rw [hs, hχ' s hsW, zero_smul]

/-! ### The cutoffs at the two ends -/

/-- The cutoff `s ↦ ψ (s - a)` of the positive end, built from the smooth transition `ψ`; the cutoff
of the negative end is `s ↦ ψ (-s - a)`. -/
private def endCutoff (a s : ℝ) : ℝ := Real.smoothTransition (s - a)

private theorem contDiff_endCutoff (a : ℝ) : ContDiff ℝ ∞ (endCutoff a) :=
  Real.smoothTransition.contDiff.comp (by fun_prop)

private theorem contDiff_endCutoff_neg (a : ℝ) : ContDiff ℝ ∞ fun s ↦ endCutoff a (-s) :=
  (contDiff_endCutoff a).comp contDiff_neg

private theorem endCutoff_eq_zero {a s : ℝ} (h : s ≤ a) : endCutoff a s = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

private theorem endCutoff_eq_one {a s : ℝ} (h : a + 1 ≤ s) : endCutoff a s = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

private theorem abs_endCutoff_le_one (a s : ℝ) : |endCutoff a s| ≤ 1 :=
  Real.smoothTransition.abs_le_one _

private theorem deriv_endCutoff (a s : ℝ) :
    deriv (endCutoff a) s = deriv Real.smoothTransition (s - a) := by
  have h := ((hasDerivAt_id s).sub_const a).smoothTransition
  unfold endCutoff
  simpa using h.deriv

private theorem deriv_endCutoff_neg (a s : ℝ) :
    deriv (fun s ↦ endCutoff a (-s)) s = -deriv Real.smoothTransition (-s - a) := by
  have h := ((hasDerivAt_neg s).sub_const a).smoothTransition
  simpa [endCutoff] using h.deriv

private theorem abs_deriv_endCutoff_le {L : ℝ} (hL : ∀ t, ‖deriv Real.smoothTransition t‖ ≤ L)
    (a s : ℝ) : |deriv (endCutoff a) s| ≤ L := by
  rw [deriv_endCutoff]; exact hL _

private theorem abs_deriv_endCutoff_neg_le {L : ℝ}
    (hL : ∀ t, ‖deriv Real.smoothTransition t‖ ≤ L) (a s : ℝ) :
    |deriv (fun s ↦ endCutoff a (-s)) s| ≤ L := by
  rw [deriv_endCutoff_neg, abs_neg]; exact hL _

/-- The derivative of the transition `ψ (t - a)` vanishes off `(a, a + 1)`. -/
private theorem deriv_smoothTransition_sub_eq_zero {a t : ℝ} (h : t ∉ Ioo a (a + 1)) :
    deriv Real.smoothTransition (t - a) = 0 := by
  rcases not_and_or.1 h with h | h
  · exact Real.smoothTransition.deriv_of_nonpos (by linarith [not_lt.1 h])
  · exact Real.smoothTransition.deriv_of_one_le (by linarith [not_lt.1 h])

private theorem deriv_endCutoff_eq_zero {a s : ℝ} (ha : 0 ≤ a) (hs : s ∉ Ioo (-(a + 2)) (a + 2)) :
    deriv (endCutoff a) s = 0 := by
  rw [deriv_endCutoff]
  exact deriv_smoothTransition_sub_eq_zero fun h ↦ hs ⟨by linarith [h.1], by linarith [h.2]⟩

private theorem deriv_endCutoff_neg_eq_zero {a s : ℝ} (ha : 0 ≤ a)
    (hs : s ∉ Ioo (-(a + 2)) (a + 2)) :
    deriv (fun s ↦ endCutoff a (-s)) s = 0 := by
  rw [deriv_endCutoff_neg, neg_eq_zero]
  exact deriv_smoothTransition_sub_eq_zero fun h ↦ hs ⟨by linarith [h.2], by linarith [h.1]⟩

/-- For `a ≥ 0` the two end cutoffs have disjoint supports, so the middle weight
`1 - ψ (-s - a) - ψ (s - a)` lies in `[0, 1]`. -/
private theorem abs_one_sub_endCutoff_neg_sub_endCutoff_le_one {a : ℝ} (ha : 0 ≤ a) (s : ℝ) :
    |1 - endCutoff a (-s) - endCutoff a s| ≤ 1 := by
  rcases le_total s 0 with hs | hs
  · rw [endCutoff_eq_zero (by linarith : s ≤ a)]
    have := Real.smoothTransition.nonneg (-s - a); have := Real.smoothTransition.le_one (-s - a)
    rw [abs_le, endCutoff]; constructor <;> linarith
  · rw [endCutoff_eq_zero (by linarith : -s ≤ a)]
    have := Real.smoothTransition.nonneg (s - a); have := Real.smoothTransition.le_one (s - a)
    rw [abs_le, endCutoff]; constructor <;> linarith

/-- The middle weight `1 - ψ (-s - a) - ψ (s - a)` vanishes off `(-(a + 2), a + 2)`. -/
private theorem one_sub_endCutoff_neg_sub_endCutoff_eq_zero {a s : ℝ} (ha : 0 ≤ a)
    (hs : s ∉ Ioo (-(a + 2)) (a + 2)) : 1 - endCutoff a (-s) - endCutoff a s = 0 := by
  rcases not_and_or.1 hs with h | h
  · rw [endCutoff_eq_zero (by linarith [not_lt.1 h] : s ≤ a),
      endCutoff_eq_one (by linarith [not_lt.1 h])]
    ring
  · rw [endCutoff_eq_zero (by linarith [not_lt.1 h] : -s ≤ a),
      endCutoff_eq_one (by linarith [not_lt.1 h])]
    ring

/-! ### The middle piece -/

variable {B Bbot Btop : D →L[ℝ] H} {A : ℝ → D →L[ℝ] H} {AL : Lp (D →L[ℝ] H) ∞ μ₀} {c : ℝ}

/-- **The estimate on a window.** Let `A(s)` differ from an invertible `ι`-symmetric `B` by at most
`c ‖ι x‖`, with `c ≥ 0`. A path `w = φ u`, for a weight `|φ| ≤ 1` vanishing off the window
`(-b, b)`, satisfies `‖w‖ ≤ M (‖D_A w‖ + c ‖ι ∘ u‖_{L²((-b, b), H)})` with `M = √(1 + ‖B⁻¹‖²)`. -/
private theorem norm_le_of_ae_prev_eq_smul (hSymm : ∀ x y : D, ⟪B x, ι y⟫_ℝ = ⟪ι x, B y⟫_ℝ)
    (hB : B.IsInvertible) (hAL : AL =ᵐ[μ₀] A) (hc₀ : 0 ≤ c)
    (hc : ∀ᵐ s ∂volume, ∀ x, ‖(A s - B) x‖ ≤ c * ‖ι x‖) {b : ℝ} {φ : ℝ → ℝ}
    (hφ : ∀ s, |φ s| ≤ 1) (hφ₀ : ∀ s ∉ Ioo (-b) b, φ s = 0)
    {u w : WeakDerivStep volume ⊤ 2 (ι.compLpL 2 μ₀)}
    (hw : ∀ᵐ s ∂volume, prev _ w s = φ s • prev _ u s) :
    ‖w‖ ≤ √(1 + ‖B.inverse‖ ^ 2) * (‖familyDomainTrajectoryOperator ι AL w‖ +
      c * ‖restrictBaseL (ι.compLpL 2 μ₀) (V := ⟨Ioo (-b) b, isOpen_Ioo⟩) le_top u‖) := by
  -- `D_A w - D_B w = (A - B) w` is bounded by `c ‖ι ∘ u‖` on the window and vanishes off it.
  have hdiff : ‖familyDomainTrajectoryOperator ι AL w - domainTrajectoryOperator ι B w‖ ≤
      c * ‖restrictBaseL (ι.compLpL 2 μ₀) (V := ⟨Ioo (-b) b, isOpen_Ioo⟩) le_top u‖ := by
    rw [← familyDomainTrajectoryOperator_toLp_const, ← sub_apply,
      familyDomainTrajectoryOperator_sub, ContinuousLinearMap.comp_apply, prevL_apply]
    have hm := ae_top_iff.1 (Lp.operatorMultiplication_ae
      (AL - (memLp_top_const (μ := μ₀) B).toLp _) (prev _ w))
    have hs := ae_top_iff.1 (Lp.coeFn_sub AL ((memLp_top_const (μ := μ₀) B).toLp _))
    have hk := ae_top_iff.1 ((memLp_top_const (μ := μ₀) B).coeFn_toLp)
    refine norm_le_mul_norm_restrictBaseL hc₀ u ?_ ?_
    · filter_upwards [hm, hs, hk, ae_top_iff.1 hAL, hc, hw] with s h₁ h₂ h₃ h₄ h₅ h₆
      rw [h₁, h₂, Pi.sub_apply, h₃, h₄, h₆, map_smul, norm_smul, Real.norm_eq_abs]
      exact (mul_le_mul (hφ s) (h₅ _) (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
    · filter_upwards [hm, hw] with s h₁ h₂ hsW
      rw [h₁, h₂, hφ₀ s hsW, zero_smul, map_zero]
  refine (norm_le_sqrt_one_add_sq_mul_norm_domainTrajectoryOperator hSymm hB w).trans ?_
  gcongr
  have := norm_sub_norm_le (domainTrajectoryOperator ι B w) (familyDomainTrajectoryOperator ι AL w)
  rw [norm_sub_rev] at this
  linarith

omit [CompleteSpace D] in
/-- **An end piece.** If `‖w‖ ≤ C ‖D_A w‖` for every path `w` vanishing on `S`, then a path
`w = φ u` with `φ = 0` on `S` and `‖D_A w‖ ≤ X` satisfies `‖w‖ ≤ max C 0 * X`. -/
private theorem norm_le_max_mul_of_ae_prev_eq_smul {S : Set ℝ} {C X : ℝ}
    (hC : ∀ w : WeakDerivStep volume ⊤ 2 (ι.compLpL 2 μ₀),
      (∀ᵐ s ∂volume, s ∈ S → prev _ w s = 0) → ‖w‖ ≤ C * ‖familyDomainTrajectoryOperator ι AL w‖)
    {φ : ℝ → ℝ} (hφ : ∀ s ∈ S, φ s = 0) {u w : WeakDerivStep volume ⊤ 2 (ι.compLpL 2 μ₀)}
    (hw : ∀ᵐ s ∂volume, prev _ w s = φ s • prev _ u s)
    (hX : ‖familyDomainTrajectoryOperator ι AL w‖ ≤ X) : ‖w‖ ≤ max C 0 * X := by
  refine (hC w ?_).trans ((mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)).trans
    (mul_le_mul_of_nonneg_left hX (le_max_right _ _)))
  filter_upwards [hw] with s hs hsS
  rw [hs, hφ s hsS, zero_smul]

omit [CompleteSpace D] in
/-- The middle piece `u - w₁ - w₂` of the paths `w₁ = φ u` and `w₂ = ψ u` is `(1 - φ - ψ) u`. -/
private theorem ae_prev_sub_sub_eq_smul {φ ψ : ℝ → ℝ}
    {u w₁ w₂ : WeakDerivStep volume ⊤ 2 (ι.compLpL 2 μ₀)}
    (h₁ : ∀ᵐ s ∂volume, prev _ w₁ s = φ s • prev _ u s)
    (h₂ : ∀ᵐ s ∂volume, prev _ w₂ s = ψ s • prev _ u s) :
    ∀ᵐ s ∂volume, prev _ (u - w₁ - w₂) s = (1 - φ s - ψ s) • prev _ u s := by
  filter_upwards [ae_top_iff.1 (Lp.coeFn_sub (prev _ u - prev _ w₁) (prev _ w₂)),
    ae_top_iff.1 (Lp.coeFn_sub (prev _ u) (prev _ w₁)), h₁, h₂] with s hs hs' hs₁ hs₂
  rw [← prevL_apply, map_sub, map_sub, prevL_apply, prevL_apply, prevL_apply, hs, Pi.sub_apply,
    hs', Pi.sub_apply, hs₁, hs₂, sub_smul, sub_smul, one_smul]

/-! ### The estimate -/

/-- **Splicing the three pieces.** Let `D_A` satisfy `‖w‖ ≤ C₊ ‖D_A w‖` for the paths vanishing on
`(-∞, T₊)` and `‖w‖ ≤ C₋ ‖D_A w‖` for those vanishing on `(T₋, ∞)`, and let `A(s)` differ from an
invertible `ι`-symmetric `B` by at most `c ‖ι x‖`. For `a ≥ max T₊ (-T₋) 0`, cutting a path `u` by
`ψ (s - a)`, `ψ (-s - a)` and the rest bounds it by `‖D_A u‖` and the `L²` norm `R` of `ι ∘ u` on
`(-(a + 2), a + 2)`. -/
private theorem norm_le_of_end_estimates (hSymm : ∀ x y : D, ⟪B x, ι y⟫_ℝ = ⟪ι x, B y⟫_ℝ)
    (hB : B.IsInvertible) (hAL : AL =ᵐ[μ₀] A) (hc₀ : 0 ≤ c)
    (hc : ∀ᵐ s ∂volume, ∀ x, ‖(A s - B) x‖ ≤ c * ‖ι x‖) {Ctop Cbot Ttop Tbot a L : ℝ}
    (hCtop : ∀ w : WeakDerivStep volume ⊤ 2 (ι.compLpL 2 μ₀),
      (∀ᵐ s ∂volume, s < Ttop → prev _ w s = 0) →
        ‖w‖ ≤ Ctop * ‖familyDomainTrajectoryOperator ι AL w‖)
    (hCbot : ∀ w : WeakDerivStep volume ⊤ 2 (ι.compLpL 2 μ₀),
      (∀ᵐ s ∂volume, Tbot < s → prev _ w s = 0) →
        ‖w‖ ≤ Cbot * ‖familyDomainTrajectoryOperator ι AL w‖)
    (ha₀ : 0 ≤ a) (haT : Ttop ≤ a) (haT' : -Tbot ≤ a)
    (hL : ∀ t, ‖deriv Real.smoothTransition t‖ ≤ L)
    (u : WeakDerivStep volume ⊤ 2 (ι.compLpL 2 μ₀)) :
    ‖u‖ ≤ (max Ctop 0 + max Cbot 0) * (‖familyDomainTrajectoryOperator ι AL u‖ + L *
        ‖restrictBaseL (ι.compLpL 2 μ₀) (V := ⟨Ioo (-(a + 2)) (a + 2), isOpen_Ioo⟩) le_top u‖) +
      √(1 + ‖B.inverse‖ ^ 2) * (3 * ‖familyDomainTrajectoryOperator ι AL u‖ + (2 * L + c) *
        ‖restrictBaseL (ι.compLpL 2 μ₀) (V := ⟨Ioo (-(a + 2)) (a + 2), isOpen_Ioo⟩) le_top u‖) := by
  set R := ‖restrictBaseL (ι.compLpL 2 μ₀) (V := ⟨Ioo (-(a + 2)) (a + 2), isOpen_Ioo⟩) le_top u‖
  set N := ‖familyDomainTrajectoryOperator ι AL u‖
  have h₁top := abs_deriv_endCutoff_le hL a
  have h₁bot := abs_deriv_endCutoff_neg_le hL a
  set wtop := cutoffMul (contDiff_endCutoff a) (abs_endCutoff_le_one a) h₁top u
  set wbot := cutoffMul (contDiff_endCutoff_neg a) (fun s ↦ abs_endCutoff_le_one a (-s)) h₁bot u
  have hptop := ae_top_iff.1 (prev_cutoffMul_ae (contDiff_endCutoff a) (abs_endCutoff_le_one a)
    h₁top u)
  have hpbot := ae_top_iff.1 (prev_cutoffMul_ae (contDiff_endCutoff_neg a)
    (fun s ↦ abs_endCutoff_le_one a (-s)) h₁bot u)
  -- The two ends `w₊ = ψ (s - a) u` and `w₋ = ψ (-s - a) u`.
  have hDtop : ‖familyDomainTrajectoryOperator ι AL wtop‖ ≤ N + L * R :=
    norm_familyDomainTrajectoryOperator_cutoffMul_le _ _ h₁top
      (fun _ ↦ deriv_endCutoff_eq_zero ha₀) _ u
  have hDbot : ‖familyDomainTrajectoryOperator ι AL wbot‖ ≤ N + L * R :=
    norm_familyDomainTrajectoryOperator_cutoffMul_le _ _ h₁bot
      (fun _ ↦ deriv_endCutoff_neg_eq_zero ha₀) _ u
  have hwtop := norm_le_max_mul_of_ae_prev_eq_smul (S := Iio Ttop) hCtop
    (fun s hs ↦ endCutoff_eq_zero (by linarith [mem_Iio.1 hs])) hptop hDtop
  have hwbot := norm_le_max_mul_of_ae_prev_eq_smul (S := Ioi Tbot) hCbot
    (fun s hs ↦ endCutoff_eq_zero (by linarith [mem_Ioi.1 hs])) hpbot hDbot
  -- The middle `u - w₋ - w₊ = (1 - ψ (-s - a) - ψ (s - a)) u`.
  have hw₀ := norm_le_of_ae_prev_eq_smul hSymm hB hAL hc₀ hc
    (abs_one_sub_endCutoff_neg_sub_endCutoff_le_one ha₀)
    (fun _ ↦ one_sub_endCutoff_neg_sub_endCutoff_eq_zero ha₀) (ae_prev_sub_sub_eq_smul hpbot hptop)
  have hD₀ : ‖familyDomainTrajectoryOperator ι AL (u - wbot - wtop)‖ ≤ 3 * N + 2 * L * R := by
    rw [map_sub, map_sub]
    linarith [norm_sub_le (familyDomainTrajectoryOperator ι AL u -
      familyDomainTrajectoryOperator ι AL wbot) (familyDomainTrajectoryOperator ι AL wtop),
      norm_sub_le (familyDomainTrajectoryOperator ι AL u)
        (familyDomainTrajectoryOperator ι AL wbot)]
  have htri : ‖u‖ ≤ ‖wbot‖ + ‖u - wbot - wtop‖ + ‖wtop‖ := by
    calc ‖u‖ = ‖wbot + (u - wbot - wtop) + wtop‖ := by congr 1; abel
      _ ≤ _ := (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
  have hM := mul_le_mul_of_nonneg_left hD₀ (Real.sqrt_nonneg (1 + ‖B.inverse‖ ^ 2))
  nlinarith

/-- **The semi-Fredholm estimate for the trajectory operator over a common domain.** Let `A(s)`
converge to invertible `ι`-symmetric operators `Bbot` and `Btop` at `-∞` and `∞`, and differ from
`Btop` by an operator bounded through `ι`: `‖(A(s) - Btop) x‖ ≤ c ‖ι x‖` for almost every `s`.
Then there are `C` and `T` with

`‖u‖ ≤ C (‖(ι ∘ u)' + A u‖ + ‖ι ∘ u‖_{L²((-T, T), H)})`

for every `u ∈ L²(ℝ, D) ∩ W^{1,2}(ℝ, H)`. -/
theorem exists_forall_norm_le_mul_norm_familyDomainTrajectoryOperator_add_norm_restrictBaseL
    (hSymmbot : ∀ x y : D, ⟪Bbot x, ι y⟫_ℝ = ⟪ι x, Bbot y⟫_ℝ) (hBbot : Bbot.IsInvertible)
    (hSymmtop : ∀ x y : D, ⟪Btop x, ι y⟫_ℝ = ⟪ι x, Btop y⟫_ℝ) (hBtop : Btop.IsInvertible)
    (hAL : AL =ᵐ[μ₀] A) (hbot : Tendsto A atBot (𝓝 Bbot)) (htop : Tendsto A atTop (𝓝 Btop))
    (hc : ∀ᵐ s ∂volume, ∀ x, ‖(A s - Btop) x‖ ≤ c * ‖ι x‖) :
    ∃ C T : ℝ, ∀ u : WeakDerivStep volume ⊤ 2 (ι.compLpL 2 μ₀),
      ‖u‖ ≤ C * (‖familyDomainTrajectoryOperator ι AL u‖ +
        ‖restrictBaseL (ι.compLpL 2 μ₀) (V := ⟨Ioo (-T) T, isOpen_Ioo⟩) le_top u‖) := by
  obtain ⟨Cbot, Tbot, hCbot⟩ :=
    exists_forall_norm_le_mul_norm_familyDomainTrajectoryOperator_of_tendsto_atBot
      hSymmbot hBbot hAL hbot
  obtain ⟨Ctop, Ttop, hCtop⟩ :=
    exists_forall_norm_le_mul_norm_familyDomainTrajectoryOperator_of_tendsto_atTop
      hSymmtop hBtop hAL htop
  obtain ⟨L, hL⟩ := Real.smoothTransition.exists_forall_norm_deriv_le
  have hL₀ : 0 ≤ L := (norm_nonneg _).trans (hL 0)
  have hc' : ∀ᵐ s ∂volume, ∀ x, ‖(A s - Btop) x‖ ≤ max c 0 * ‖ι x‖ := by
    filter_upwards [hc] with s hs x
    exact (hs x).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  set a := max (max Ttop (-Tbot)) 0
  set K := max Ctop 0 + max Cbot 0
  set M := √(1 + ‖Btop.inverse‖ ^ 2)
  refine ⟨K * (1 + L) + M * (3 + 2 * L + max c 0), a + 2, fun u ↦ ?_⟩
  have h := norm_le_of_end_estimates hSymmtop hBtop hAL (le_max_right c 0) hc' hCtop hCbot
    (le_max_right _ _) ((le_max_left _ _).trans (le_max_left _ _))
    ((le_max_right _ _).trans (le_max_left _ _)) hL u
  -- Every coefficient is at most the constant, since all the terms are nonnegative.
  have hK : 0 ≤ K := add_nonneg (le_max_right _ _) (le_max_right _ _)
  have hM : 0 ≤ M := Real.sqrt_nonneg _
  have hN := norm_nonneg (familyDomainTrajectoryOperator ι AL u)
  have hR := norm_nonneg
    (restrictBaseL (ι.compLpL 2 μ₀) (V := ⟨Ioo (-(a + 2)) (a + 2), isOpen_Ioo⟩) le_top u)
  nlinarith [mul_nonneg (mul_nonneg hK hL₀) hN, mul_nonneg hK hR,
    mul_nonneg (mul_nonneg hM hL₀) hN, mul_nonneg (mul_nonneg hM (le_max_right c 0)) hN,
    mul_nonneg hM hR]

/-- The semi-Fredholm estimate in the form of Peetre's lemma: for compact `ι`, there is a compact
operator `K` on the graph space with `‖u‖ ≤ C ‖D_A u‖ + ‖K u‖`. -/
private theorem exists_isCompactOperator_and_norm_le (hι : IsCompactOperator ι)
    (hSymmbot : ∀ x y : D, ⟪Bbot x, ι y⟫_ℝ = ⟪ι x, Bbot y⟫_ℝ) (hBbot : Bbot.IsInvertible)
    (hSymmtop : ∀ x y : D, ⟪Btop x, ι y⟫_ℝ = ⟪ι x, Btop y⟫_ℝ) (hBtop : Btop.IsInvertible)
    (hAL : AL =ᵐ[μ₀] A) (hbot : Tendsto A atBot (𝓝 Bbot)) (htop : Tendsto A atTop (𝓝 Btop))
    (hc : ∀ᵐ s ∂volume, ∀ x, ‖(A s - Btop) x‖ ≤ c * ‖ι x‖) :
    ∃ (T C : ℝ) (K : WeakDerivStep volume ⊤ 2 (ι.compLpL 2 μ₀) →L[ℝ]
      Lp H 2 (volume.restrict (Ioo (-T) T))), IsCompactOperator K ∧
        ∀ u, ‖u‖ ≤ C * ‖familyDomainTrajectoryOperator ι AL u‖ + ‖K u‖ := by
  obtain ⟨C, T, hC⟩ :=
    exists_forall_norm_le_mul_norm_familyDomainTrajectoryOperator_add_norm_restrictBaseL
      hSymmbot hBbot hSymmtop hBtop hAL hbot htop hc
  set R := restrictBaseL (ι.compLpL 2 μ₀) (V := ⟨Ioo (-T) T, isOpen_Ioo⟩) le_top
  refine ⟨T, C, C • R, ?_, fun u ↦ ?_⟩
  · rw [FunLike.coe_smul]
    exact (isCompactOperator_restrictBaseL_compLpL hι _).smul C
  · rw [smul_apply, norm_smul, Real.norm_eq_abs]
    linarith [hC u, mul_le_mul_of_nonneg_right (le_abs_self C) (norm_nonneg (R u))]

/-- **The kernel of the trajectory operator over a compactly embedded domain is finite
dimensional.** Under the hypotheses of
`exists_forall_norm_le_mul_norm_familyDomainTrajectoryOperator_add_norm_restrictBaseL`, if moreover
`ι` is a compact operator, the kernel of `u ↦ (ι ∘ u)' + A u` on `L²(ℝ, D) ∩ W^{1,2}(ℝ, H)` is
finite dimensional. -/
theorem finiteDimensional_ker_familyDomainTrajectoryOperator (hι : IsCompactOperator ι)
    (hSymmbot : ∀ x y : D, ⟪Bbot x, ι y⟫_ℝ = ⟪ι x, Bbot y⟫_ℝ) (hBbot : Bbot.IsInvertible)
    (hSymmtop : ∀ x y : D, ⟪Btop x, ι y⟫_ℝ = ⟪ι x, Btop y⟫_ℝ) (hBtop : Btop.IsInvertible)
    (hAL : AL =ᵐ[μ₀] A) (hbot : Tendsto A atBot (𝓝 Bbot)) (htop : Tendsto A atTop (𝓝 Btop))
    (hc : ∀ᵐ s ∂volume, ∀ x, ‖(A s - Btop) x‖ ≤ c * ‖ι x‖) :
    FiniteDimensional ℝ (familyDomainTrajectoryOperator (p := 2) ι AL).ker := by
  obtain ⟨T, C, K, hK, hCK⟩ := exists_isCompactOperator_and_norm_le hι hSymmbot hBbot hSymmtop
    hBtop hAL hbot htop hc
  exact (familyDomainTrajectoryOperator ι AL).finiteDimensional_ker_of_compact_estimate hK hCK

/-- **The range of the trajectory operator over a compactly embedded domain is closed.** Under the
hypotheses of
`exists_forall_norm_le_mul_norm_familyDomainTrajectoryOperator_add_norm_restrictBaseL`, if moreover
`ι` is a compact operator, the range of `u ↦ (ι ∘ u)' + A u` from `L²(ℝ, D) ∩ W^{1,2}(ℝ, H)` to
`L²(ℝ, H)` is closed. -/
theorem isClosed_range_familyDomainTrajectoryOperator (hι : IsCompactOperator ι)
    (hSymmbot : ∀ x y : D, ⟪Bbot x, ι y⟫_ℝ = ⟪ι x, Bbot y⟫_ℝ) (hBbot : Bbot.IsInvertible)
    (hSymmtop : ∀ x y : D, ⟪Btop x, ι y⟫_ℝ = ⟪ι x, Btop y⟫_ℝ) (hBtop : Btop.IsInvertible)
    (hAL : AL =ᵐ[μ₀] A) (hbot : Tendsto A atBot (𝓝 Bbot)) (htop : Tendsto A atTop (𝓝 Btop))
    (hc : ∀ᵐ s ∂volume, ∀ x, ‖(A s - Btop) x‖ ≤ c * ‖ι x‖) :
    IsClosed ((familyDomainTrajectoryOperator (p := 2) ι AL).range : Set (Lp H 2 μ₀)) := by
  obtain ⟨T, C, K, hK, hCK⟩ := exists_isCompactOperator_and_norm_le hι hSymmbot hBbot hSymmtop
    hBtop hAL hbot htop hc
  exact (familyDomainTrajectoryOperator ι AL).isClosed_range_of_compact_estimate hK hCK

end TauCeti.WeakDerivStep
