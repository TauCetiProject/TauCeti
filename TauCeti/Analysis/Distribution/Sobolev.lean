/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.Sobolev

/-!
# Bessel regularity from directional derivatives

For a tempered distribution, membership in `H^{s+1,2}` is equivalent to membership in
`H^{s,2}` of the distribution and its derivatives along an orthonormal basis. This provides
the inductive characterization needed to compare Bessel-potential spaces with spaces
defined by integer-order weak derivatives.

The identity for the order-two Bessel potential retains Mathlib's Fourier normalization:
it is `1 - (2π)⁻² Δ`.

Use `TauCeti.besselPotential_two_eq f` for the operator identity and
`TauCeti.memSobolev_add_one_iff f b s` for the regularity criterion.

## References

* M. Taylor, *Partial Differential Equations I*, Chapter 4.
* Mathlib's `TemperedDistribution.MemSobolev.lineDerivOp` (directional-derivative regularity)
  and `TemperedDistribution.memSobolev_besselPotential_iff` (Bessel-potential regularity shift).
-/

public section

namespace TauCeti

open MeasureTheory TemperedDistribution FourierTransform
open scoped SchwartzMap LineDeriv Laplacian Real

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F]

section Normed

variable [NormedSpace ℂ F]

/-- The order-two Bessel potential is `1 - (2π)⁻² Δ`, with Mathlib's Fourier convention. -/
theorem besselPotential_two_eq (f : TemperedDistribution E F) :
    besselPotential E F 2 f = f - ((2 * π) ^ 2)⁻¹ • Δ f := by
  have hπ : (2 * π) ^ 2 ≠ 0 := by positivity
  rw [laplacian_eq_fourierMultiplierCLM, smul_smul]
  simp only [inv_mul_cancel₀ hπ, mul_neg, neg_smul, sub_neg_eq_add]
  have hweight : (fun x : E => Complex.ofReal ((1 + ‖x‖ ^ 2) ^ ((2 : ℝ) / 2))) =
      (fun _ => (1 : ℂ)) + (fun x => Complex.ofReal (‖x‖ ^ 2)) := by
    ext x
    simp
  rw [besselPotential, hweight]
  simp only [fourierMultiplierCLM_apply, one_smul]
  rw [smulLeftCLM_add (by fun_prop) (by fun_prop)]
  simp

end Normed

variable [InnerProductSpace ℂ F] [CompleteSpace F]

/-- A tempered distribution has one more Bessel derivative exactly when it and its
directional derivatives along an orthonormal basis have the original regularity. -/
theorem memSobolev_add_one_iff {ι : Type*} [Fintype ι]
    (f : TemperedDistribution E F) (b : OrthonormalBasis ι ℝ E) (s : ℝ) :
    MemSobolev (s + 1) 2 f ↔
      MemSobolev s 2 f ∧ ∀ i, MemSobolev s 2 (∂_{b i} f) := by
  classical
  constructor
  · intro h
    exact ⟨h.mono (by linarith), fun i => by simpa using h.lineDerivOp (m := b i)⟩
  · rintro ⟨hf, hd⟩
    have hΔ : MemSobolev (s - 1) 2 (Δ f) := by
      rw [laplacian_eq_sum b]
      exact Finset.induction_on Finset.univ
        (by simp)
        (fun i t hi ht => by
          rw [Finset.sum_insert hi]
          exact (hd i).lineDerivOp.add ht)
    have hlow : MemSobolev s 2 (besselPotential E F (-1) f) := by
      rw [memSobolev_besselPotential_iff]
      exact hf.mono (by linarith)
    have hhigh : MemSobolev s 2 (besselPotential E F (-1) (Δ f)) := by
      rw [memSobolev_besselPotential_iff]
      convert hΔ using 1; ring
    have h := hlow.sub (hhigh.smul (((2 * π) ^ 2)⁻¹ : ℝ))
    rw [← map_smul, ← map_sub] at h
    simp only [Complex.coe_smul] at h
    rw [← besselPotential_two_eq, besselPotential_besselPotential_apply,
      memSobolev_besselPotential_iff] at h
    convert h using 1; ring

end TauCeti
