/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Wkp.Classical
public import TauCeti.Analysis.Sobolev.Wkp.Contraction.Basic
import TauCeti.MeasureTheory.Function.Lp.Basic

/-!
# Classical `ContDiffOn` comparison lemmas for iterated directional derivatives

If a Sobolev function `u ∈ W^{k+j+1,p}(Ω)` is represented almost everywhere on `Ω` by a `C^{j+1}`
function `f`, then its `(j + 1)`-fold bundled directional derivative
`TauCeti.Wkp.iteratedLineDerivL k (j + 1) m u` agrees almost everywhere on `Ω` with the classical
directional derivative `x ↦ iteratedFDeriv ℝ (j + 1) f x m`
(`TauCeti.Wkp.value_iteratedLineDerivL_succ_ae_eq_of_contDiffOn`), without requiring higher
smoothness of `f` than `C^{j+1}`.

## Main declarations

* `TauCeti.Wkp.iteratedLineDerivZeroL_succ_ae_eq_of_contDiffOn`: `ContDiffOn` identification for
  `iteratedLineDerivZeroL`.
* `TauCeti.Wkp.value_iteratedLineDerivL_succ_ae_eq_of_contDiffOn`: general-order `ContDiffOn`
  identification for `iteratedLineDerivL`.
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory TopologicalSpace
open scoped ENNReal InnerProductSpace ContDiff

namespace Wkp

section Classical

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure]
  {Omega : Opens E} {p : ENNReal} [Fact (1 ≤ p)]

/-- If `u ∈ W^{j+1,p}(Ω)` is represented on `Ω` by a `C^{j+1}` function `f`, then
`iteratedLineDerivZeroL (j + 1) m u` agrees almost everywhere on `Ω` with
`x ↦ iteratedFDeriv ℝ (j + 1) f x m`. -/
theorem iteratedLineDerivZeroL_succ_ae_eq_of_contDiffOn (j : ℕ) (u : Wkp mu Omega p (j + 1))
    (m : Fin (j + 1) → E) {f : E → ℝ} (hf : ContDiffOn ℝ (j + 1) f Omega)
    (hu : (value (j + 1) u : E → ℝ) =ᵐ[mu.restrict Omega] f) :
    (iteratedLineDerivZeroL (j + 1) m u : E → ℝ) =ᵐ[mu.restrict Omega]
      fun x => iteratedFDeriv ℝ (j + 1) f x m := by
  rw [iteratedLineDerivZeroL_succ_apply]
  filter_upwards [(IteratedGradient.evalL j m).coeFn_compLp (iteratedGradient j u),
    iteratedGradient_ae_eq_of_contDiffOn j u hf hu] with x hx hgx
  rw [hx, hgx, IteratedGradient.evalL_iteratedGradientChain]

/-- General-order form of `TauCeti.Wkp.iteratedLineDerivZeroL_succ_ae_eq_of_contDiffOn`: only
`C^{j+1}` regularity of `f` on `Ω` is required, even when `u` lies in `W^{k+j+1,p}(Ω)`. -/
theorem value_iteratedLineDerivL_succ_ae_eq_of_contDiffOn (k j : ℕ)
    (u : Wkp mu Omega p (k + (j + 1))) (m : Fin (j + 1) → E) {f : E → ℝ}
    (hf : ContDiffOn ℝ (j + 1) f Omega)
    (hu : (value (k + (j + 1)) u : E → ℝ) =ᵐ[mu.restrict Omega] f) :
    (value k (iteratedLineDerivL k (j + 1) m u) : E → ℝ) =ᵐ[mu.restrict Omega]
      fun x => iteratedFDeriv ℝ (j + 1) f x m := by
  let u₀ := toOrderL (Nat.le_add_left (j + 1) k) u
  have hu₀ : (value (j + 1) u₀ : E → ℝ) =ᵐ[mu.restrict Omega] f := by
    rwa [value_toOrderL]
  rw [value_iteratedLineDerivL_eq_iteratedLineDerivZeroL]
  exact iteratedLineDerivZeroL_succ_ae_eq_of_contDiffOn j u₀ m hf hu₀

end Classical

end Wkp

end TauCeti
