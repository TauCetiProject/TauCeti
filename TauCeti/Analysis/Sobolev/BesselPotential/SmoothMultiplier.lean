/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.Sobolev
import TauCeti.Analysis.Calculus.IteratedFDeriv.FDerivApply
import TauCeti.Analysis.Distribution.TemperateGrowth
import TauCeti.Analysis.Distribution.TemperedDistribution.Lp
import TauCeti.Analysis.Distribution.TemperedDistribution.SmulLeft

/-!
# Multiplication by functions with bounded derivatives on `H^{k,p}(ℝⁿ)`

Let `g` be a scalar function of temperate growth whose iterated derivatives of order at most `|k|`
are bounded. For `1 < p < ∞`, multiplication by `g` maps the Bessel-potential space `H^{k,p}` of
integer order `k`, positive or negative, into itself: if a tempered distribution `f` lies in
`H^{k,p}`, then so does `g f`. For `k ≥ 0` this is
`TemperedDistribution.MemSobolev.smulLeftCLM_of_norm_iteratedFDeriv_le`, and for negative orders
`TemperedDistribution.MemSobolev.smulLeftCLM_of_norm_iteratedFDeriv_le_neg`. Here `g f` is
Mathlib's `TemperedDistribution.smulLeftCLM`.

Unlike multiplication by Schwartz functions, the multiplier need not decay. Typical examples are
smooth functions which outside a ball agree with a winding phase `(z / |z|) ^ m` or with a
coefficient of the angular form `dθ`, such as the reference fields of framed vortices on the plane.
These multipliers appear in the linear terms of nonlinear field equations on affine Sobolev spaces
centred at such a reference field. The same applies to scalar coefficients with bounded
derivatives, such as the coefficients of a differential operator; matrix-valued multipliers such
as changes of frame are not treated here.

Both proofs are by induction on `k`, starting from `H^{0,p} = Lᵖ`, which a bounded `g` multiplies
into itself (`TemperedDistribution.MemSobolev.smulLeftCLM_of_norm_le`). Going up, a distribution
lies in `H^{k+1,p}` exactly when it lies in `Lᵖ` and its directional derivatives lie in `H^{k,p}`
(`TemperedDistribution.memSobolev_natCast_add_one_iff`, which uses `1 < p < ∞`). By the Leibniz
rule (`TemperedDistribution.lineDerivOp_smulLeftCLM`) `∂_v (g f) = (∂_v g) f + g ∂_v f`, and both
terms are of order `k`: `∂_v g` has bounded derivatives up to order `k` and `f ∈ H^{k,p}`, while
`∂_v f ∈ H^{k,p}`. Going down, a distribution lies in `H^{-k-1,p}` exactly when it is
`u + ∑ᵢ ∂ᵢ wᵢ` with `u` and `wᵢ` in `H^{-k,p}` (`TemperedDistribution.memSobolev_sub_one_iff`).
The Leibniz rule turns `g f` into `g u - ∑ᵢ (∂ᵢ g) wᵢ + ∑ᵢ ∂ᵢ (g wᵢ)`, again of this form.

## Main results

* `TemperedDistribution.MemSobolev.smulLeftCLM_of_norm_le`: a bounded function of temperate
  growth multiplies `H^{0,p}` into itself, for every `1 ≤ p ≤ ∞`.
* `TemperedDistribution.MemSobolev.smulLeftCLM_of_norm_iteratedFDeriv_le`: a function of temperate
  growth with bounded derivatives up to order `k` multiplies `H^{k,p}` into itself, for
  `1 < p < ∞`.
* `TemperedDistribution.MemSobolev.smulLeftCLM_schwartzMap`: in particular a Schwartz function
  multiplies `H^{k,p}` into itself.
* `TemperedDistribution.MemSobolev.smulLeftCLM_of_norm_iteratedFDeriv_le_neg`: the same for the
  negative order `H^{-k,p}`.
* `TemperedDistribution.MemSobolev.smulLeftCLM_of_norm_iteratedFDeriv_le_intCast`: the two
  combined, for `H^{k,p}` with `k ∈ ℤ` and bounded derivatives up to order `|k|`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  AMS, 2010, §5.2.3, Theorem 1 (the Leibniz formula for weak derivatives).
* J. Bergh and J. Löfström, *Interpolation Spaces*, Springer, 1976, §6.2 (the Bessel-potential
  spaces `H^{s,p}` and the isomorphisms `J^r : H^{s,p} → H^{s-r,p}`).
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
  obtain ⟨v, hv, -⟩ := Lp.exists_smulLeftCLM_toTemperedDistribution_eq_and_norm_le hg hC f'
  rw [hv]
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
    rw [lineDerivOp_smulLeftCLM hg]
    exact (ih (hg.fderiv_apply v) (hg.1.exists_bound_iteratedFDeriv_fderiv_apply (by simp) hbd v)
      (hf.mono_of_one_lt hp hp_top (by linarith))).add
      (ih hg (fun n hn ↦ hbd n (by omega)) (hf'.2 v))

/-- **Schwartz multipliers act on `H^{k,p}`.** For `1 < p < ∞`, multiplication by a Schwartz
function maps `H^{k,p}` into itself. -/
theorem MemSobolev.smulLeftCLM_schwartzMap (hp : 1 < p) (hp_top : p ≠ ∞) {k : ℕ} (ψ : 𝓢(E, ℂ))
    {f : 𝓢'(E, F)} (hf : MemSobolev k p f) : MemSobolev k p (smulLeftCLM F ψ f) :=
  hf.smulLeftCLM_of_norm_iteratedFDeriv_le hp hp_top ψ.hasTemperateGrowth
    fun i _ ↦ ⟨_, ψ.norm_iteratedFDeriv_le_seminorm ℝ i⟩

/-- **Multipliers with bounded derivatives act on `H^{-k,p}`.** Let `1 < p < ∞` and let `g` be a
function of temperate growth whose iterated derivatives of order at most `k` are bounded. Then
`g f ∈ H^{-k,p}` for every `f ∈ H^{-k,p}`. -/
theorem MemSobolev.smulLeftCLM_of_norm_iteratedFDeriv_le_neg (hp : 1 < p) (hp_top : p ≠ ∞)
    {k : ℕ} {g : E → ℂ} (hg : g.HasTemperateGrowth)
    (hbd : ∀ n ≤ k, ∃ C, ∀ x, ‖iteratedFDeriv ℝ n g x‖ ≤ C) {f : 𝓢'(E, F)}
    (hf : MemSobolev (-k) p f) : MemSobolev (-k) p (smulLeftCLM F g f) := by
  induction k generalizing g f with
  | zero =>
    obtain ⟨C, hC⟩ := hbd 0 le_rfl
    rw [Nat.cast_zero, neg_zero] at hf ⊢
    exact hf.smulLeftCLM_of_norm_le hg (C := C) (fun x ↦ by simpa using hC x)
  | succ k ih =>
    have hk : -((k + 1 : ℕ) : ℝ) = -k - 1 := by push_cast; ring
    rw [hk] at hf ⊢
    -- Write `f = u + ∑ᵢ ∂ᵢ wᵢ` with `u` and `wᵢ` in `H^{-k,p}`. Then
    -- `g f = g u + ∑ᵢ (∂ᵢ (g wᵢ) - (∂ᵢ g) wᵢ)`, each of whose terms lies in `H^{-k-1,p}`.
    have hbd' : ∀ n ≤ k, ∃ C, ∀ x, ‖iteratedFDeriv ℝ n g x‖ ≤ C := fun n hn ↦ hbd n (by omega)
    obtain ⟨u, w, hu, hw, rfl⟩ :=
      (memSobolev_sub_one_iff hp hp_top (stdOrthonormalBasis ℝ E)).1 hf
    refine (memSobolev_sub_one_iff hp hp_top (stdOrthonormalBasis ℝ E)).2
      ⟨smulLeftCLM F g u - ∑ i, smulLeftCLM F (fun x ↦ fderiv ℝ g x (stdOrthonormalBasis ℝ E i))
        (w i), fun i ↦ smulLeftCLM F g (w i), ?_, fun i ↦ ih hg hbd' (hw i), ?_⟩
    · exact (ih hg hbd' hu).sub (MemSobolev.sum fun i _ ↦ ih (hg.fderiv_apply _)
        (hg.1.exists_bound_iteratedFDeriv_fderiv_apply (by simp) hbd _) (hw i))
    · simp only [map_add, map_sum, lineDerivOp_smulLeftCLM hg]
      rw [Finset.sum_add_distrib]
      abel

/-- **Multipliers with bounded derivatives act on `H^{k,p}` for every integer `k`.** Let
`1 < p < ∞` and let `g` be a function of temperate growth whose iterated derivatives of order at
most `|k|` are bounded. Then `g f ∈ H^{k,p}` for every `f ∈ H^{k,p}`. -/
theorem MemSobolev.smulLeftCLM_of_norm_iteratedFDeriv_le_intCast (hp : 1 < p) (hp_top : p ≠ ∞)
    {k : ℤ} {g : E → ℂ} (hg : g.HasTemperateGrowth)
    (hbd : ∀ n ≤ k.natAbs, ∃ C, ∀ x, ‖iteratedFDeriv ℝ n g x‖ ≤ C) {f : 𝓢'(E, F)}
    (hf : MemSobolev k p f) : MemSobolev k p (smulLeftCLM F g f) := by
  obtain ⟨k, rfl | rfl⟩ := k.eq_nat_or_neg
  · exact_mod_cast hf.smulLeftCLM_of_norm_iteratedFDeriv_le hp hp_top hg (by simpa using hbd)
  · push_cast at hf ⊢
    exact hf.smulLeftCLM_of_norm_iteratedFDeriv_le_neg hp hp_top hg (by simpa using hbd)

end TemperedDistribution
