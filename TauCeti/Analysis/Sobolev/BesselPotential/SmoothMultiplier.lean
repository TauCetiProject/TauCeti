/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.Sobolev
import TauCeti.Analysis.Calculus.IteratedFDeriv.FDerivApply
import TauCeti.Analysis.Distribution.TemperateGrowth
import TauCeti.Analysis.Distribution.TemperedDistribution.SmulLeft

/-!
# Multiplication by functions with bounded derivatives on `H^{k,p}(ℝⁿ)`

Let `g` be a scalar function of temperate growth whose iterated derivatives of order at most `k` are
bounded. For `1 < p < ∞`, multiplication by `g` maps the Bessel-potential space `H^{k,p}` of
integer order `k` into itself: if a tempered distribution `f` lies in `H^{k,p}`, then so does
`g f` (`TemperedDistribution.MemSobolev.smulLeftCLM_of_norm_iteratedFDeriv_le`). Here `g f` is
Mathlib's `TemperedDistribution.smulLeftCLM`.

Unlike multiplication by Schwartz functions, the multiplier need not decay. Typical examples are
smooth functions which outside a ball agree with a winding phase `(z / |z|) ^ m` or with a
coefficient of the angular form `dθ`, such as the reference fields of framed vortices on the plane.
These multipliers appear in the linear terms of nonlinear field equations on affine Sobolev spaces
centred at such a reference field.

The proof is by induction on `k`. At order zero, `H^{0,p} = Lᵖ` and a bounded `g` multiplies
`Lᵖ` into itself (`TemperedDistribution.MemSobolev.smulLeftCLM_of_norm_le`). At order `k + 1`, a
distribution lies in `H^{k+1,p}` exactly when it lies in `Lᵖ` and its directional derivatives lie
in `H^{k,p}` (`TemperedDistribution.memSobolev_natCast_add_one_iff`, which uses `1 < p < ∞`). By
the Leibniz rule (`TemperedDistribution.lineDerivOp_smulLeftCLM`)
`∂_v (g f) = (∂_v g) f + g ∂_v f`, and both terms are of order `k`: `∂_v g` has bounded derivatives
up to order `k` and `f ∈ H^{k,p}`, while `∂_v f ∈ H^{k,p}`.

## Main results

* `TemperedDistribution.MemSobolev.smulLeftCLM_of_norm_le`: a bounded function of temperate
  growth multiplies `H^{0,p}` into itself, for every `1 ≤ p ≤ ∞`.
* `TemperedDistribution.MemSobolev.smulLeftCLM_of_norm_iteratedFDeriv_le`: a function of temperate
  growth with bounded derivatives up to order `k` multiplies `H^{k,p}` into itself, for
  `1 < p < ∞`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  AMS, 2010, §5.2.3, Theorem 1 (the Leibniz formula for weak derivatives).
-/

public section

namespace TemperedDistribution

open MeasureTheory
open scoped SchwartzMap LineDeriv ENNReal

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **A bounded multiplier acts on `H^{0,p} = Lᵖ`.** If `g` has temperate growth and is bounded,
then `g f ∈ H^{0,p}` for every `f ∈ H^{0,p}`. -/
theorem MemSobolev.smulLeftCLM_of_norm_le [NormedSpace ℂ F] [CompleteSpace F] {g : E → ℂ}
    (hg : g.HasTemperateGrowth) {C : ℝ} (hC : ∀ x, ‖g x‖ ≤ C) {f : 𝓢'(E, F)}
    (hf : MemSobolev 0 p f) : MemSobolev 0 p (smulLeftCLM F g f) := by
  obtain ⟨f', rfl⟩ := memSobolev_zero_iff.1 hf
  have hg' : MemLp g ⊤ volume :=
    memLp_top_of_bound hg.1.continuous.aestronglyMeasurable C (ae_of_all _ hC)
  rw [← Lp.toTemperedDistribution_smul_eq (r := p) hg hg']
  exact memSobolev_zero_iff.2 ⟨_, rfl⟩

variable [InnerProductSpace ℂ F] [CompleteSpace F]

/-- **Multipliers with bounded derivatives act on `H^{k,p}`.** Let `1 < p < ∞` and let `g` be a
function of temperate growth whose iterated derivatives of order at most `k` are bounded. Then
`g f ∈ H^{k,p}` for every `f ∈ H^{k,p}`. -/
theorem MemSobolev.smulLeftCLM_of_norm_iteratedFDeriv_le (hp : 1 < p) (hp_top : p ≠ ∞) {k : ℕ}
    {g : E → ℂ} (hg : g.HasTemperateGrowth)
    (hbd : ∀ n ≤ k, ∃ C, ∀ x, ‖iteratedFDeriv ℝ n g x‖ ≤ C) {f : 𝓢'(E, F)}
    (hf : MemSobolev k p f) : MemSobolev k p (smulLeftCLM F g f) := by
  induction k generalizing g f with
  | zero =>
    obtain ⟨C, hC⟩ := hbd 0 le_rfl
    rw [Nat.cast_zero] at hf ⊢
    exact hf.smulLeftCLM_of_norm_le hg (C := C) (fun x ↦ by simpa using hC x)
  | succ k ih =>
    rw [Nat.cast_succ] at hf ⊢
    have hf' := (memSobolev_natCast_add_one_iff hp hp_top).1 hf
    refine (memSobolev_natCast_add_one_iff hp hp_top).2 ⟨?_, fun v ↦ ?_⟩
    · obtain ⟨C, hC⟩ := hbd 0 (by omega)
      exact hf'.1.smulLeftCLM_of_norm_le hg (C := C) (fun x ↦ by simpa using hC x)
    -- `∂_v (g f) = (∂_v g) f + g ∂_v f`, and `∂_v g` has bounded derivatives up to order `k`.
    have hbd' : ∀ n ≤ k, ∃ C, ∀ x, ‖iteratedFDeriv ℝ n (fun y ↦ fderiv ℝ g y v) x‖ ≤ C := by
      intro n hn
      obtain ⟨C, hC⟩ := hbd (n + 1) (by omega)
      exact ⟨C * ‖v‖, fun x ↦ (hg.1.norm_iteratedFDeriv_fderiv_apply_le
        (by simp) v x).trans (by gcongr; exact hC x)⟩
    rw [lineDerivOp_smulLeftCLM hg]
    exact (ih (hg.fderiv_apply v) hbd' (hf.mono_of_one_lt hp hp_top (by linarith))).add
      (ih hg (fun n hn ↦ hbd n (by omega)) (hf'.2 v))

end TemperedDistribution
