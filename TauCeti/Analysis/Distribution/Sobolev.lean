/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.Sobolev
import TauCeti.Analysis.Fourier.MihlinHormander
import TauCeti.Analysis.SpecialFunctions.JapaneseBracket.Deriv
import TauCeti.Analysis.SpecialFunctions.Pow.Bounds

/-!
# Bessel-potential regularity from first derivatives

For `1 < p < ∞`, a tempered distribution lies in Mathlib's Bessel-potential space `H^{s+1,p}`
exactly when it and all its first directional derivatives lie in `H^{s,p}`. Mathlib proves the
inclusion `H^{s+1,2} ⊆ H^{s,2}` and that derivatives map `H^{s,2}` to `H^{s-1,2}`
(`TemperedDistribution.MemSobolev.mono`, `TemperedDistribution.MemSobolev.lineDerivOp`) by
Plancherel, since for `p = 2` every bounded symbol is a multiplier. For other `p`, the symbols
involved, `(1 + ‖ξ‖ ^ 2) ^ (-t / 2)` with `t ≥ 0` and `⟪ξ, v⟫ (1 + ‖ξ‖ ^ 2) ^ (-1 / 2)`, are
symbols of order `0` (`TauCeti.exists_norm_iteratedFDeriv_one_add_norm_sq_rpow_le`,
`TauCeti.exists_norm_iteratedFDeriv_inner_mul_one_add_norm_sq_rpow_le`), so they satisfy
Mihlin's condition, and the Mihlin–Hörmander multiplier theorem makes them bounded on `Lᵖ`
(`TauCeti.exists_fourierMultiplierCLM_eq_and_norm_le_of_norm_iteratedFDeriv_le`). The converse
direction needs the derivatives only along an orthonormal basis: `J¹ f = J⁻¹ (J² f)` with
`J² = 1 - (2π)⁻² Δ`.

Use the regularity criteria to characterize Sobolev membership through directional derivatives,
either in all directions or along an orthonormal basis. The order-two operator identity relates
the Bessel potential to the Laplacian, with the factor `2π` from Mathlib's Fourier normalization.

## Main declarations

* `TemperedDistribution.besselPotential_two_eq_sub_laplacian`: the Bessel potential of order `2`
  is `1 - (2π)⁻² Δ`.
* `TemperedDistribution.MemSobolev.sum`: `H^{s,p}` is closed under finite sums.
* `TemperedDistribution.MemSobolev.smul_of_tower`: `H^{s,p}` is closed under scalar
  multiplication by scalars acting through `ℂ`, such as real numbers.
* `TemperedDistribution.MemSobolev.fourierMultiplierCLM_of_norm_iteratedFDeriv_le`: for
  `1 < p < ∞`, Fourier multipliers whose symbols satisfy Mihlin's condition map `H^{s,p}` to
  `H^{s,p}`.
* `MemSobolev.fourierMultiplierCLM_ofReal_of_norm_iteratedFDeriv_le_one_add_norm_sq_rpow`: for
  `1 < p < ∞`, real symbols of order `0`, whose `k`-th derivatives are bounded by
  `C_k (1 + ‖x‖ ^ 2) ^ (-k / 2)`, map `H^{s,p}` to `H^{s,p}`.
* `TemperedDistribution.MemSobolev.mono_of_one_lt`: `H^{s,p} ⊆ H^{s',p}` for `s' ≤ s`.
* `TemperedDistribution.MemSobolev.lineDerivOp_of_one_lt`: `∂_m` maps `H^{s,p}` to `H^{s-1,p}`.
* `TemperedDistribution.memSobolev_add_one_of_lineDerivOp`: if `f` and its derivatives along an
  orthonormal basis lie in `H^{s,p}`, then `f` lies in `H^{s+1,p}`.
* `TemperedDistribution.memSobolev_add_one_iff`: `f ∈ H^{s+1,p}` exactly when `f ∈ H^{s,p}` and
  `∂_m f ∈ H^{s,p}` for every direction `m`.
* `TemperedDistribution.memSobolev_natCast_add_one_iff`: at a natural order `k`,
  `f ∈ H^{k+1,p}` exactly when `f ∈ H^{0,p}` and `∂_m f ∈ H^{k,p}` for every direction `m`.

## References

* M. Taylor, *Partial Differential Equations I*, Chapter 4, §1.
* E. M. Stein, *Singular Integrals and Differentiability Properties of Functions*, Chapter V, §3
  (the Bessel-potential spaces `ℒᵖ_k` and their characterization by derivatives).
-/

public section

namespace TemperedDistribution

open MeasureTheory Module
open scoped Real Laplacian LineDeriv SchwartzMap ENNReal NNReal

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F]

section normed

variable [NormedSpace ℂ F]

/-- The Bessel potential of order `2` is `1 - (2π)⁻² Δ`. The factor `(2π)⁻²` comes from
Mathlib's normalisation of the Fourier transform. -/
theorem besselPotential_two_eq_sub_laplacian (f : 𝓢'(E, F)) :
    besselPotential E F 2 f = f - ((2 * π) ^ 2)⁻¹ • Δ f := by
  -- The Bessel symbol of order `2` is `1 + ‖x‖²`, so the Bessel potential splits as the
  -- identity plus the Fourier multiplier with symbol `‖x‖²`.
  have hsymb : (fun x : E ↦ (((1 + ‖x‖ ^ 2) ^ ((2 : ℝ) / 2) : ℝ) : ℂ)) =
      (fun _ ↦ (1 : ℂ)) + fun x ↦ ((‖x‖ ^ 2 : ℝ) : ℂ) := by
    ext x
    norm_num
  have hsplit : besselPotential E F 2 f =
      f + fourierMultiplierCLM F (fun x : E ↦ ((‖x‖ ^ 2 : ℝ) : ℂ)) f := by
    rw [besselPotential, hsymb, fourierMultiplierCLM_apply,
      smulLeftCLM_add (by fun_prop) (by fun_prop)]
    simp [fourierMultiplierCLM_apply]
  -- Mathlib writes `Δ` as the Fourier multiplier with symbol `-(2π)² ‖x‖²`.
  have hΔ : ((2 * π) ^ 2)⁻¹ • Δ f =
      -fourierMultiplierCLM F (fun x : E ↦ ((‖x‖ ^ 2 : ℝ) : ℂ)) f := by
    rw [laplacian_eq_fourierMultiplierCLM, smul_smul, mul_neg,
      inv_mul_cancel₀ (by positivity), neg_one_smul]
  rw [hsplit, hΔ, sub_neg_eq_add]

variable [CompleteSpace F]

/-- A finite sum of tempered distributions in `H^{s,p}` lies in `H^{s,p}`. -/
theorem MemSobolev.sum {ι : Type*} {t : Finset ι} {s : ℝ} {p : ENNReal} [Fact (1 ≤ p)]
    {g : ι → 𝓢'(E, F)} (hg : ∀ i ∈ t, MemSobolev s p (g i)) : MemSobolev s p (∑ i ∈ t, g i) :=
  Finset.sum_induction g (MemSobolev s p) (fun _ _ => MemSobolev.add)
    (memSobolev_fun_zero E F s p) hg

/-- `H^{s,p}` is closed under scalar multiplication by any scalars acting on tempered
distributions through `ℂ`, such as real numbers. -/
theorem MemSobolev.smul_of_tower {R : Type*} [SMul R ℂ] [SMul R 𝓢'(E, F)]
    [IsScalarTower R ℂ 𝓢'(E, F)] {s : ℝ} {p : ENNReal} [Fact (1 ≤ p)] (c : R) {f : 𝓢'(E, F)}
    (hf : MemSobolev s p f) : MemSobolev s p (c • f) := by
  rw [← smul_one_smul ℂ c f]
  exact hf.smul _

end normed

section inner

variable [InnerProductSpace ℂ F] [CompleteSpace F] {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **Mihlin multipliers act on `H^{s,p}`.** For `1 < p < ∞`, the Fourier multiplier with a symbol
of temperate growth satisfying Mihlin's condition of order `N`, `2N > dim E`, maps `H^{s,p}` to
`H^{s,p}`. For `p = 2` every bounded symbol does (`MemSobolev.fourierMultiplierCLM_of_bounded`). -/
theorem MemSobolev.fourierMultiplierCLM_of_norm_iteratedFDeriv_le (hp : 1 < p)
    (hp_top : p ≠ ∞) {s : ℝ} {f : 𝓢'(E, F)} (hf : MemSobolev s p f) {g : E → ℂ}
    (hg : g.HasTemperateGrowth) {N : ℕ} (hN : finrank ℝ E < 2 * N) {A : ℝ≥0}
    (hgA : ∀ k ≤ N, ∀ ξ ≠ 0, ‖iteratedFDeriv ℝ k g ξ‖ ≤ A / ‖ξ‖ ^ k) :
    MemSobolev s p (fourierMultiplierCLM F g f) := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · -- On the zero space every symbol is constant.
    have hconst : g = fun _ ↦ g 0 := funext fun x ↦ congrArg g (Subsingleton.elim x 0)
    rw [hconst, fourierMultiplierCLM_const]
    exact hf.smul (g 0)
  -- Fourier multipliers commute, so the Bessel potential of `T_g f` is `T_g` applied to the
  -- `Lᵖ` function `J^s f`, an `Lᵖ` function by the Mihlin–Hörmander theorem.
  obtain ⟨f', hf'⟩ := hf
  obtain ⟨C, hC⟩ :=
    TauCeti.exists_fourierMultiplierCLM_eq_and_norm_le_of_norm_iteratedFDeriv_le (F := F) hN hp
      hp_top
  obtain ⟨g', hg', -⟩ := hC hg hgA f'
  refine ⟨g', ?_⟩
  rw [besselPotential, fourierMultiplierCLM_fourierMultiplierCLM_apply hg (by fun_prop),
    mul_comm, ← fourierMultiplierCLM_fourierMultiplierCLM_apply (by fun_prop) hg,
    ← besselPotential, hf', hg']

/-- **Order-zero real symbols act on `H^{s,p}`.** For `1 < p < ∞`, the Fourier multiplier with a
real symbol `g` of order `0` in Hörmander's sense, `‖D^k g x‖ ≤ C_k (1 + ‖x‖ ^ 2) ^ (-k / 2)` for
every `k`, maps `H^{s,p}` to `H^{s,p}`. This is the Japanese-bracket form of Mihlin's condition in
`MemSobolev.fourierMultiplierCLM_of_norm_iteratedFDeriv_le`. -/
theorem MemSobolev.fourierMultiplierCLM_ofReal_of_norm_iteratedFDeriv_le_one_add_norm_sq_rpow
    (hp : 1 < p) (hp_top : p ≠ ∞) {s : ℝ} {f : 𝓢'(E, F)} (hf : MemSobolev s p f) {g : E → ℝ}
    (hg : g.HasTemperateGrowth)
    (hgk : ∀ k : ℕ, ∃ C, ∀ x, ‖iteratedFDeriv ℝ k g x‖ ≤ C * (1 + ‖x‖ ^ 2) ^ (-(k : ℝ) / 2)) :
    MemSobolev s p (fourierMultiplierCLM F (fun x ↦ (g x : ℂ)) f) := by
  choose C hC using hgk
  set N := finrank ℝ E + 1
  refine hf.fourierMultiplierCLM_of_norm_iteratedFDeriv_le hp hp_top (by fun_prop) (N := N)
    (by omega) (A := ∑ k ∈ Finset.range (N + 1), ‖C k‖₊) fun k hk ξ hξ ↦ ?_
  have hreal : ‖iteratedFDeriv ℝ k (fun x ↦ (g x : ℂ)) ξ‖ = ‖iteratedFDeriv ℝ k g ξ‖ :=
    Complex.ofRealLI.norm_iteratedFDeriv_comp_left hg.1.contDiffAt (mod_cast le_top)
  have hCk : ‖C k‖ ≤ ∑ k ∈ Finset.range (N + 1), ‖C k‖₊ := by
    exact_mod_cast Finset.single_le_sum (f := fun k ↦ ‖C k‖₊) (fun i _ ↦ bot_le)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hk))
  rw [hreal, ← mul_one_div]
  calc ‖iteratedFDeriv ℝ k g ξ‖ ≤ ‖C k‖ * (1 + ‖ξ‖ ^ 2) ^ (-(k : ℝ) / 2) :=
        (hC k ξ).trans (by gcongr; exact Real.le_norm_self _)
    _ ≤ _ := by
        gcongr
        exact Real.one_add_sq_rpow_neg_le (norm_pos_iff.mpr hξ) k

/-- For `1 < p < ∞`, `H^{s,p}` is contained in `H^{s',p}` whenever `s' ≤ s`. For `p = 2` this is
`MemSobolev.mono`. -/
theorem MemSobolev.mono_of_one_lt (hp : 1 < p) (hp_top : p ≠ ∞) {s s' : ℝ} (h : s' ≤ s)
    {f : 𝓢'(E, F)} (hf : MemSobolev s p f) : MemSobolev s' p f := by
  rw [← sub_add_cancel s' s, ← memSobolev_besselPotential_iff, besselPotential]
  refine hf.fourierMultiplierCLM_ofReal_of_norm_iteratedFDeriv_le_one_add_norm_sq_rpow hp hp_top
    (by fun_prop) fun k ↦ ?_
  -- The symbol `(1 + ‖x‖ ^ 2) ^ ((s' - s) / 2)` has nonpositive order.
  obtain ⟨C, hC⟩ := TauCeti.exists_norm_iteratedFDeriv_one_add_norm_sq_rpow_le (E := E)
    ((s' - s) / 2) k
  refine ⟨|C|, fun x ↦ (hC x).trans ?_⟩
  gcongr
  · exact le_abs_self C
  · exact le_add_of_nonneg_right (by positivity)
  · linarith

/-- For `1 < p < ∞`, the directional derivative maps `H^{s,p}` to `H^{s-1,p}`. For `p = 2` this is
`MemSobolev.lineDerivOp`. -/
theorem MemSobolev.lineDerivOp_of_one_lt (hp : 1 < p) (hp_top : p ≠ ∞) {s : ℝ} {f : 𝓢'(E, F)}
    (hf : MemSobolev s p f) {m : E} : MemSobolev (s - 1) p (∂_{m} f) := by
  rw [SubNegMonoid.sub_eq_add_neg s 1, add_comm, ← memSobolev_besselPotential_iff,
    besselPotential_neg_one_lineDerivOp_eq f]
  refine (hf.fourierMultiplierCLM_ofReal_of_norm_iteratedFDeriv_le_one_add_norm_sq_rpow hp hp_top
    (by fun_prop) fun k ↦ ?_).smul _
  -- The symbol `⟪x, m⟫ (1 + ‖x‖ ^ 2) ^ (-1 / 2)` has order `0`.
  obtain ⟨C, hC⟩ := TauCeti.exists_norm_iteratedFDeriv_inner_mul_one_add_norm_sq_rpow_le m
    (-1 / 2) k
  refine ⟨C, fun x ↦ (hC x).trans_eq ?_⟩
  ring_nf

/-- For `1 < p < ∞`, a tempered distribution in `H^{s,p}` whose derivatives along an orthonormal
basis lie in `H^{s,p}` lies in `H^{s+1,p}`. -/
theorem memSobolev_add_one_of_lineDerivOp (hp : 1 < p) (hp_top : p ≠ ∞) {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ E) {s : ℝ} {f : 𝓢'(E, F)} (hf : MemSobolev s p f)
    (hdf : ∀ i, MemSobolev s p (∂_{b i} f)) : MemSobolev (s + 1) p f := by
  -- With `J^r` the Bessel potential of order `r`, membership of `f` in `H^{s+1,p}` is membership
  -- of `J¹ f = J⁻¹ (J² f)` in `H^{s,p}`, and `J² f = f - (2π)⁻² ∑ᵢ ∂ᵢ ∂ᵢ f`. The operator `J⁻¹`
  -- maps `f` and each `∂ᵢ ∂ᵢ f` into `H^{s,p}`.
  have hJ : besselPotential E F 1 f = besselPotential E F (-1) f -
      ((2 * π) ^ 2)⁻¹ • ∑ i, besselPotential E F (-1) (∂_{b i} (∂_{b i} f)) := by
    calc besselPotential E F 1 f
        = besselPotential E F (-1) (besselPotential E F 2 f) := by
          rw [besselPotential_besselPotential_apply]
          norm_num
      _ = _ := by
          rw [besselPotential_two_eq_sub_laplacian, laplacian_eq_sum b, map_sub,
            ContinuousLinearMap.map_smul_of_tower, map_sum]
  rw [add_comm, ← memSobolev_besselPotential_iff, hJ, RCLike.real_smul_eq_coe_smul (K := ℂ)]
  refine MemSobolev.sub ?_ (MemSobolev.smul _ (MemSobolev.sum fun i _ => ?_))
  · rw [memSobolev_besselPotential_iff]
    exact hf.mono_of_one_lt hp hp_top (by linarith)
  · rw [memSobolev_besselPotential_iff, neg_add_eq_sub]
    exact (hdf i).lineDerivOp_of_one_lt hp hp_top

/-- For `1 < p < ∞`, a tempered distribution lies in `H^{s+1,p}` exactly when it and all its
first directional derivatives lie in `H^{s,p}`. -/
theorem memSobolev_add_one_iff (hp : 1 < p) (hp_top : p ≠ ∞) {s : ℝ} {f : 𝓢'(E, F)} :
    MemSobolev (s + 1) p f ↔ MemSobolev s p f ∧ ∀ m : E, MemSobolev s p (∂_{m} f) := by
  refine ⟨fun hf => ⟨hf.mono_of_one_lt hp hp_top (by linarith), fun m => by
      simpa using hf.lineDerivOp_of_one_lt hp hp_top (m := m)⟩,
    fun h => memSobolev_add_one_of_lineDerivOp hp hp_top (stdOrthonormalBasis ℝ E) h.1
      fun i => h.2 _⟩

/-- For `1 < p < ∞` and a natural order `k`, a tempered distribution lies in `H^{k+1,p}` exactly
when it lies in `H^{0,p}` and all its first directional derivatives lie in `H^{k,p}`. -/
theorem memSobolev_natCast_add_one_iff (hp : 1 < p) (hp_top : p ≠ ∞) {k : ℕ} {f : 𝓢'(E, F)} :
    MemSobolev ((k : ℝ) + 1) p f ↔ MemSobolev 0 p f ∧ ∀ m : E, MemSobolev k p (∂_{m} f) := by
  induction k generalizing f with
  | zero => simpa using memSobolev_add_one_iff hp hp_top (s := 0) (f := f)
  | succ k ih =>
      -- `H^{k+1,p}` is `H^{0,p}` together with `H^{k,p}` for the derivatives, and the latter is
      -- implied by `H^{k+1,p}` for the derivatives.
      rw [Nat.cast_succ, memSobolev_add_one_iff hp hp_top, ih]
      exact ⟨fun h => ⟨h.1.1, h.2⟩,
        fun h => ⟨⟨h.1, fun m => (h.2 m).mono_of_one_lt hp hp_top (by linarith)⟩, h.2⟩⟩

end inner

end TemperedDistribution
