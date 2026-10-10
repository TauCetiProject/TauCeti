/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.Sobolev

/-!
# Bessel-potential regularity from first derivatives

For `p = 2`, a tempered distribution lies in Mathlib's Bessel-potential space `H^{s+1}` exactly
when it and all its first directional derivatives lie in `H^s`. One direction is Mathlib's
`TemperedDistribution.MemSobolev.lineDerivOp` together with `TemperedDistribution.MemSobolev.mono`.
This file proves the other direction, which needs the derivatives only along an orthonormal
basis.

The proof writes the Bessel potential of order `2` as `1 - (2π)⁻² Δ`, with `Δ` the sum of the
second derivatives along the basis, and applies the Bessel potential of order `-1` to both
sides. The `2π` comes from Mathlib's normalisation of the Fourier transform.

## Main declarations

* `TemperedDistribution.besselPotential_two_eq_sub_laplacian`: the Bessel potential of order `2`
  is `1 - (2π)⁻² Δ`.
* `TemperedDistribution.MemSobolev.sum`: `H^{s,p}` is closed under finite sums.
* `TemperedDistribution.memSobolev_add_one_of_lineDerivOp`: if `f` and its derivatives along an
  orthonormal basis lie in `H^s`, then `f` lies in `H^{s+1}`.
* `TemperedDistribution.memSobolev_add_one_iff`: `f ∈ H^{s+1}` exactly when `f ∈ H^s` and
  `∂_m f ∈ H^s` for every direction `m`.
* `TemperedDistribution.memSobolev_natCast_add_one_iff`: at a natural order `k`, `f ∈ H^{k+1}`
  exactly when `f ∈ H^0` and `∂_m f ∈ H^k` for every direction `m`.

## References

* M. Taylor, *Partial Differential Equations I*, Chapter 4, §1.
-/

public section

namespace TemperedDistribution

open MeasureTheory
open scoped Real Laplacian LineDeriv SchwartzMap

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

end normed

section inner

variable [InnerProductSpace ℂ F] [CompleteSpace F]

/-- A tempered distribution in `H^s` whose derivatives along an orthonormal basis lie in `H^s`
lies in `H^{s+1}`. -/
theorem memSobolev_add_one_of_lineDerivOp {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E)
    {s : ℝ} {f : 𝓢'(E, F)} (hf : MemSobolev s 2 f) (hdf : ∀ i, MemSobolev s 2 (∂_{b i} f)) :
    MemSobolev (s + 1) 2 f := by
  -- With `J^r` the Bessel potential of order `r`, membership of `f` in `H^{s+1}` is membership
  -- of `J¹ f = J⁻¹ (J² f)` in `H^s`, and `J² f = f - (2π)⁻² ∑ᵢ ∂ᵢ ∂ᵢ f`. The operator `J⁻¹`
  -- maps `f` and each `∂ᵢ ∂ᵢ f` into `H^s`.
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
    exact hf.mono (by linarith)
  · rw [memSobolev_besselPotential_iff, neg_add_eq_sub]
    exact (hdf i).lineDerivOp

/-- A tempered distribution lies in `H^{s+1}` exactly when it and all its first directional
derivatives lie in `H^s`. -/
theorem memSobolev_add_one_iff {s : ℝ} {f : 𝓢'(E, F)} :
    MemSobolev (s + 1) 2 f ↔ MemSobolev s 2 f ∧ ∀ m : E, MemSobolev s 2 (∂_{m} f) := by
  refine ⟨fun hf => ⟨hf.mono (by linarith), fun m => by simpa using hf.lineDerivOp (m := m)⟩,
    fun h => memSobolev_add_one_of_lineDerivOp (stdOrthonormalBasis ℝ E) h.1 fun i => h.2 _⟩

/-- At a natural order `k`, a tempered distribution lies in `H^{k+1}` exactly when it lies in
`H^0` and all its first directional derivatives lie in `H^k`. -/
theorem memSobolev_natCast_add_one_iff {k : ℕ} {f : 𝓢'(E, F)} :
    MemSobolev ((k : ℝ) + 1) 2 f ↔ MemSobolev 0 2 f ∧ ∀ m : E, MemSobolev k 2 (∂_{m} f) := by
  induction k generalizing f with
  | zero => simpa using memSobolev_add_one_iff (s := 0) (f := f)
  | succ k ih =>
      -- `H^{k+1}` is `H^0` together with `H^k` for the derivatives, and the latter is implied by
      -- `H^{k+1}` for the derivatives.
      rw [Nat.cast_succ, memSobolev_add_one_iff, ih]
      exact ⟨fun h => ⟨h.1.1, h.2⟩,
        fun h => ⟨⟨h.1, fun m => (h.2 m).mono (by linarith)⟩, h.2⟩⟩

end inner

end TemperedDistribution
