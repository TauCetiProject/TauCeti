/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.FunctionalSpaces.BesovSpace.Product
public import TauCeti.Analysis.FunctionalSpaces.TimeWeighted

/-!
# The Bony product in time-weighted Besov spaces

For `α < 0 < β` with `α + β > 0`, the spatial Bony product
`TauCeti.BesovSpace.smulL : B^α_{p₁,q₁} × B^β_{p₂,q₂} →L[ℂ] B^α_{r,q₁}` acts pointwise on
time-weighted continuous functions (`TauCeti.TimeWeighted.bilinear`), mapping
`C_{η₁}((0, T]; B^α_{p₁,q₁}) × C_{η₂}((0, T]; B^β_{p₂,q₂})` into
`C_{η₁ + η₂}((0, T]; B^α_{r,q₁})` with a uniform norm bound independent of the integrability
exponents, `T`, `η₁`, and `η₂`.

## Main declarations

* `TauCeti.BesovSpace.exists_norm_timeWeighted_bilinear_smulL_apply_apply_le`: for
  `u ∈ C_{η₁}((0, T]; B^α_{p₁,q₁})` and `v ∈ C_{η₂}((0, T]; B^β_{p₂,q₂})`, the pointwise
  product `t ↦ u t v t` (`TauCeti.TimeWeighted.bilinear` applied to `smulL`) lies in
  `C_{η₁ + η₂}((0, T]; B^α_{r,q₁})`, with `sup_t t^{η₁ + η₂} ‖u t v t‖ ≤ C ‖u‖ ‖v‖` for a constant
  `C` depending only on `φ`, `α`, and `β`, not on the exponents, `T`, `η₁`, or `η₂`.

## References

* G. Da Prato and A. Debussche, *Strong solutions to the stochastic quantization equations*, Ann.
  Probab. **31** (2003), 1900–1916.
* J.-C. Mourrat and H. Weber, *Global well-posedness of the dynamic `Φ⁴` model in the plane*, Ann.
  Probab. **45** (2017), 2398–2476.
* H. Bahouri, J.-Y. Chemin and R. Danchin, *Fourier Analysis and Nonlinear Partial Differential
  Equations*, Grundlehren der mathematischen Wissenschaften 343, Springer, 2011, §2.8.
-/

public section

noncomputable section

open MeasureTheory
open scoped ENNReal

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

namespace TauCeti.BesovSpace

variable {φ : ContDiffBump (0 : E)} {α β : ℝ}

variable (F φ) in
/-- **The product estimate in time-weighted spaces.** For `α < 0 < α + β` there is `C ≥ 0`,
depending only on `φ`, `α` and `β`, such that for all exponents with `1/r = 1/p₁ + 1/p₂`, all
`T, η₁, η₂ : ℝ`, all `u ∈ C_{η₁}((0, T]; B^α_{p₁,q₁})` and all `v ∈ C_{η₂}((0, T]; B^β_{p₂,q₂})`,
the pointwise product `t ↦ u t v t` in `C_{η₁ + η₂}((0, T]; B^α_{r,q₁})` satisfies
`sup_{0 < t ≤ T} t^{η₁ + η₂} ‖u t v t‖ ≤ C ‖u‖ ‖v‖`. On the Hölder–Zygmund scale this is the
product `C_{η₁}((0, T]; 𝒞^α) × C_{η₂}((0, T]; 𝒞^β) → C_{η₁ + η₂}((0, T]; 𝒞^α)`. -/
theorem exists_norm_timeWeighted_bilinear_smulL_apply_apply_le (hα : α < 0) (hαβ : 0 < α + β) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {p₁ p₂ r q₁ q₂ : ℝ≥0∞} [Fact (1 ≤ p₁)] [Fact (1 ≤ p₂)] [Fact (1 ≤ r)]
      [Fact (1 ≤ q₁)] [Fact (1 ≤ q₂)] [p₁.HolderTriple p₂ r] (T η₁ η₂ : ℝ)
      (u : TimeWeighted T η₁ (BesovSpace ℂ φ α p₁ q₁))
      (v : TimeWeighted T η₂ (BesovSpace F φ β p₂ q₂)),
      ‖TimeWeighted.bilinear T η₁ η₂ (smulL r hα hαβ) u v‖ ≤ C * ‖u‖ * ‖v‖ := by
  obtain ⟨C, hC, h⟩ := exists_norm_smulL_apply_le F φ hα hαβ
  refine ⟨C, hC, fun {p₁ p₂ r q₁ q₂} _ _ _ _ _ _ T η₁ η₂ u v ↦ ?_⟩
  have hB : ‖smulL (φ := φ) (F := F) (p₁ := p₁) (p₂ := p₂) (q₁ := q₁) (q₂ := q₂) r hα hαβ‖ ≤ C :=
    ContinuousLinearMap.opNorm_le_bound₂ _ hC h
  calc ‖TimeWeighted.bilinear T η₁ η₂ (smulL r hα hαβ) u v‖
      ≤ ‖smulL (φ := φ) (F := F) (p₁ := p₁) (p₂ := p₂) (q₁ := q₁) (q₂ := q₂) r hα hαβ‖ * ‖u‖ *
          ‖v‖ :=
        TimeWeighted.norm_bilinear_apply_apply_le _ u v
    _ ≤ C * ‖u‖ * ‖v‖ := by gcongr

end TauCeti.BesovSpace
