/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.Sobolev
import TauCeti.Analysis.Distribution.TemperedDistribution.Lp
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
* `TemperedDistribution.sobolevSubmodule`: `H^{s,p}` as a complex submodule of tempered
  distributions.
* `TemperedDistribution.realSobolevSubmodule`: the real `Lᵖ` functions whose complexification
  lies in `H^{s,p}`, as a real submodule of `Lᵖ`.
* `TemperedDistribution.realSobolevFunctions`: the pointwise representatives of these, as a real
  submodule of the functions `E → ℝ`.
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

/-- An `Lᵖ` function that agrees almost everywhere with a smooth compactly supported function lies
in every Bessel-potential space `H^{s,p}`. -/
theorem memSobolev_of_ae_eq_of_hasCompactSupport {s : ℝ} {p : ENNReal} [Fact (1 ≤ p)]
    {u : E → F} (hu : ContDiff ℝ (⊤ : ℕ∞) u) (hc : HasCompactSupport u)
    {v : Lp F p (volume : Measure E)} (hv : v =ᵐ[volume] u) : MemSobolev s p (v : 𝓢'(E, F)) := by
  have hv' : v = (hc.toSchwartzMap hu).toLp p := by
    refine Lp.ext (hv.trans ?_)
    filter_upwards [(hc.toSchwartzMap hu).coeFn_toLp p] with x hx
    simp [hx]
  rw [hv', Lp.toTemperedDistribution_toLp_eq (p := p)]
  exact (hc.toSchwartzMap hu).memSobolev

variable (E F) in
/-- The tempered distributions in the Bessel-potential space `H^{s,p}`, as a complex submodule of
`𝓢'(E, F)`. This is the image in `𝓢'(E, F)` of Mathlib's bundled `BesselPotentialSpace`. -/
def sobolevSubmodule (s : ℝ) (p : ENNReal) [Fact (1 ≤ p)] : Submodule ℂ 𝓢'(E, F) where
  carrier := {f | MemSobolev s p f}
  add_mem' := MemSobolev.add
  zero_mem' := memSobolev_fun_zero E F s p
  smul_mem' c _ h := h.smul c

/-- Membership in `sobolevSubmodule` is `MemSobolev`. -/
@[simp]
theorem mem_sobolevSubmodule {s : ℝ} {p : ENNReal} [Fact (1 ≤ p)] {f : 𝓢'(E, F)} :
    f ∈ sobolevSubmodule E F s p ↔ MemSobolev s p f :=
  Iff.rfl

variable (E) in
/-- The real `Lᵖ` functions whose complexified tempered distribution lies in the
Bessel-potential space `H^{s,p}`, as a real submodule of `Lᵖ`. -/
noncomputable def realSobolevSubmodule (s : ℝ) (p : ENNReal) [Fact (1 ≤ p)] :
    Submodule ℝ (Lp ℝ p (volume : Measure E)) :=
  ((sobolevSubmodule E ℂ s p).restrictScalars ℝ).comap
    (((Lp.toTemperedDistributionCLM ℂ (volume : Measure E) p).restrictScalars ℝ).toLinearMap ∘ₗ
      Complex.ofRealCLM.compLpₗ (p := p) (μ := (volume : Measure E)))

/-- A real `Lᵖ` function lies in `realSobolevSubmodule` exactly when its complexification lies
in `H^{s,p}`. -/
theorem mem_realSobolevSubmodule {s : ℝ} {p : ENNReal} [Fact (1 ≤ p)]
    {u : Lp ℝ p (volume : Measure E)} :
    u ∈ realSobolevSubmodule E s p ↔
      MemSobolev s p (Lp.toTemperedDistribution (Complex.ofRealCLM.compLp u)) :=
  Iff.rfl

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

section realFunctions

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

variable (E) in
/-- The real functions on `E` that agree almost everywhere with an element of
`realSobolevSubmodule E s p`: the pointwise representatives of real `H^{s,p}` functions.
Membership only depends on the function up to a null set
(`mem_realSobolevFunctions_of_ae_eq`). -/
def realSobolevFunctions (s : ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)] : Submodule ℝ (E → ℝ) where
  carrier := {f | ∃ u ∈ realSobolevSubmodule E s p, u =ᵐ[volume] f}
  add_mem' := by
    rintro f g ⟨u, hu, huf⟩ ⟨v, hv, hvg⟩
    refine ⟨u + v, add_mem hu hv, ?_⟩
    filter_upwards [Lp.coeFn_add u v, huf, hvg] with x h h₁ h₂
    rw [h, Pi.add_apply, h₁, h₂, Pi.add_apply]
  zero_mem' := ⟨0, zero_mem _, Lp.coeFn_zero ℝ p volume⟩
  smul_mem' := by
    rintro c f ⟨u, hu, huf⟩
    refine ⟨c • u, Submodule.smul_mem _ c hu, ?_⟩
    filter_upwards [Lp.coeFn_smul c u, huf] with x h h'
    rw [h, Pi.smul_apply, h', Pi.smul_apply]

/-- A real function lies in `realSobolevFunctions E s p` exactly when it agrees almost everywhere
with a real `Lᵖ` function whose complexification lies in `H^{s,p}`. -/
theorem mem_realSobolevFunctions {s : ℝ} {f : E → ℝ} :
    f ∈ realSobolevFunctions E s p ↔
      ∃ u : Lp ℝ p (volume : Measure E), u =ᵐ[volume] f ∧
        MemSobolev s p (Lp.toTemperedDistribution (Complex.ofRealCLM.compLp u)) :=
  exists_congr fun _ ↦ and_comm

/-- The values of an element of `realSobolevSubmodule E s p` lie in `realSobolevFunctions E s p`. -/
theorem coeFn_mem_realSobolevFunctions {s : ℝ} {u : Lp ℝ p (volume : Measure E)}
    (hu : u ∈ realSobolevSubmodule E s p) : (u : E → ℝ) ∈ realSobolevFunctions E s p :=
  ⟨u, hu, .rfl⟩

/-- Membership in `realSobolevFunctions E s p` is invariant under almost-everywhere equality. -/
theorem mem_realSobolevFunctions_of_ae_eq {s : ℝ} {f g : E → ℝ}
    (hf : f ∈ realSobolevFunctions E s p) (hfg : f =ᵐ[volume] g) :
    g ∈ realSobolevFunctions E s p :=
  let ⟨u, hu, huf⟩ := hf
  ⟨u, hu, huf.trans hfg⟩

/-- For `1 < p < ∞`, the real `H^{s,p}` functions decrease as the order increases. -/
theorem realSobolevFunctions_mono (hp : 1 < p) (hp_top : p ≠ ∞) {s s' : ℝ} (h : s' ≤ s) :
    realSobolevFunctions E s p ≤ realSobolevFunctions E s' p :=
  fun _ ⟨u, hu, huf⟩ ↦ ⟨u, MemSobolev.mono_of_one_lt hp hp_top h hu, huf⟩

/-- A smooth compactly supported real function lies in every real Bessel-potential space. -/
theorem mem_realSobolevFunctions_of_hasCompactSupport {f : E → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f) (s : ℝ) :
    f ∈ realSobolevFunctions E s p := by
  have hm : MemLp f p volume := hf.continuous.memLp_of_hasCompactSupport hc
  refine ⟨hm.toLp _, ?_, hm.coeFn_toLp⟩
  refine memSobolev_of_ae_eq_of_hasCompactSupport (u := fun x ↦ (f x : ℂ))
    (Complex.ofRealCLM.contDiff.comp hf) (hc.comp_left Complex.ofReal_zero) ?_
  filter_upwards [Complex.ofRealCLM.coeFn_compLp (hm.toLp _), hm.coeFn_toLp] with x h₁ h₂
  simp [h₁, h₂]

end realFunctions

end TemperedDistribution
