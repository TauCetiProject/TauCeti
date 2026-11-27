/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fourier.Torus.FourierCoeff
public import TauCeti.Analysis.InnerProductSpace.Euclidean.IntegerPoints

/-!
# Periodic Bessel-potential spaces

On the torus `𝕋ᵈ = UnitAddTorus d` the Bessel potential `J^s` of order `s : ℝ` multiplies the
Fourier coefficients by `⟨n⟩^s = (1 + ‖n‖²)^{s/2}`. For `1 ≤ p ≤ ∞`, a formal Fourier series
`c : ℤᵈ → ℂ` lies in the **periodic Bessel-potential space** `H^{s,p}(𝕋ᵈ)`
(`TauCeti.UnitAddTorus.MemSobolev s p c`) when `J^s c` is the Fourier series of a function in
`Lᵖ(𝕋ᵈ)`: some `f ∈ Lᵖ(𝕋ᵈ)` has `f̂(n) = ⟨n⟩^s c(n)` for every `n`.

As in `TauCeti.UnitAddTorus.MemBesov`, `Lᵖ(𝕋ᵈ)` is taken for the product of the Haar probability
measures on the circle factors.

## Main declarations

* `TauCeti.UnitAddTorus.MemSobolev`: the predicate `c ∈ H^{s,p}(𝕋ᵈ)`, closed under the linear
  operations.
* `TauCeti.UnitAddTorus.memSobolev_zero_iff`: `H^{0,p}(𝕋ᵈ)` consists of the coefficient sequences
  of the functions in `Lᵖ(𝕋ᵈ)`.

The inclusions `B^s_{p,1}(𝕋ᵈ) ⊆ H^{s,p}(𝕋ᵈ) ⊆ B^s_{p,∞}(𝕋ᵈ)` and their consequences are in
`TauCeti.Analysis.Sobolev.Torus.Besov`.

## References

* H.-J. Schmeisser and H. Triebel, *Topics in Fourier Analysis and Function Spaces*, Wiley, 1987,
  Chapter 3 (the periodic Besov and Bessel-potential spaces).
-/

public section

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace TauCeti.UnitAddTorus

open _root_.UnitAddTorus

variable {d : Type*} [Fintype d]

-- Mathlib's monomials `mFourierLp` and the periodic Littlewood–Paley blocks live on `Lᵖ` for the
-- product of the Haar probability measures on the circle factors, given by this instance; use it
-- here so that `H^{s,p}(𝕋ᵈ)` is built on that same space.
attribute [local instance 2000] instMeasureSpaceUnitAddCircle

/-- A formal Fourier series with coefficients `c : ℤᵈ → ℂ` lies in the **periodic
Bessel-potential space** `H^{s,p}(𝕋ᵈ)` if multiplying its coefficients by the Bessel weight
`(1 + ‖n‖²)^{s/2}` gives the Fourier coefficients of a function in `Lᵖ(𝕋ᵈ)`. -/
def MemSobolev (s : ℝ) (p : ℝ≥0∞) (c : (d → ℤ) → ℂ) : Prop :=
  ∃ f : Lp ℂ p (volume : Measure (UnitAddTorus d)),
    ∀ n, mFourierCoeff f n = (((1 + ‖latticePoint n‖ ^ 2) ^ (s / 2) : ℝ) : ℂ) * c n

variable {s : ℝ} {p : ℝ≥0∞} {c c' : (d → ℤ) → ℂ}

theorem memSobolev_def :
    MemSobolev s p c ↔ ∃ f : Lp ℂ p (volume : Measure (UnitAddTorus d)),
      ∀ n, mFourierCoeff f n = (((1 + ‖latticePoint n‖ ^ 2) ^ (s / 2) : ℝ) : ℂ) * c n :=
  Iff.rfl

/-- `H^{0,p}(𝕋ᵈ)` consists of the coefficient sequences of the functions in `Lᵖ(𝕋ᵈ)`. -/
theorem memSobolev_zero_iff :
    MemSobolev 0 p c ↔ ∃ f : Lp ℂ p (volume : Measure (UnitAddTorus d)), mFourierCoeff f = c := by
  simp [memSobolev_def, funext_iff]

theorem MemSobolev.zero : MemSobolev s p (0 : (d → ℤ) → ℂ) :=
  ⟨0, fun n ↦ by
    -- The zero class is the zero function almost everywhere, whose coefficients are integrals of
    -- zero.
    rw [Pi.zero_apply, mul_zero, mFourierCoeff_congr_ae (Lp.coeFn_zero ℂ p volume)]
    simp [mFourierCoeff]⟩

section Linear

variable [Fact (1 ≤ p)]

theorem MemSobolev.add (hc : MemSobolev s p c) (hc' : MemSobolev s p c') :
    MemSobolev s p (c + c') := by
  obtain ⟨f, hf⟩ := hc
  obtain ⟨f', hf'⟩ := hc'
  refine ⟨f + f', fun n ↦ ?_⟩
  rw [← mFourierCoeffCLM_apply, map_add, mFourierCoeffCLM_apply, mFourierCoeffCLM_apply, hf, hf',
    Pi.add_apply, mul_add]

theorem MemSobolev.smul (hc : MemSobolev s p c) (a : ℂ) : MemSobolev s p (a • c) := by
  obtain ⟨f, hf⟩ := hc
  refine ⟨a • f, fun n ↦ ?_⟩
  rw [← mFourierCoeffCLM_apply, map_smul, mFourierCoeffCLM_apply, hf, Pi.smul_apply, smul_eq_mul,
    smul_eq_mul, mul_left_comm]

theorem MemSobolev.neg (hc : MemSobolev s p c) : MemSobolev s p (-c) := by
  simpa using hc.smul (-1)

theorem MemSobolev.sub (hc : MemSobolev s p c) (hc' : MemSobolev s p c') :
    MemSobolev s p (c - c') := by
  simpa [sub_eq_add_neg] using hc.add hc'.neg

end Linear

end TauCeti.UnitAddTorus
