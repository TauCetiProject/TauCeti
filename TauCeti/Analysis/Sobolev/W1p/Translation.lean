/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.W1p.Basic
import TauCeti.Analysis.Sobolev.WeakDeriv.Translation
import TauCeti.MeasureTheory.Function.Lp.Translation

/-!
# Local translations of `W^{1,p}` functions

This file packages translation by a vector as an element of `W^{1,p}` on any smaller open set
whose translate stays inside the original domain. Translation commutes with the weak gradient.

## Main declarations

* `TauCeti.W1p.translate`: local translation from `W^{1,p}(Ω)` to `W^{1,p}(V)` when
  `V + h ⊆ Ω`.
* `TauCeti.W1p.value_translate_ae`: the value of a local translation.
* `TauCeti.W1p.gradient_translate_ae`: the weak gradient of a local translation.
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory Set TopologicalSpace
open scoped ENNReal Gradient InnerProductSpace

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure]
  {Omega : Opens E} {p : ENNReal} [Fact (1 ≤ p)]

/-- **Local translation of a Sobolev function.** If `x + h ∈ Ω` for every `x ∈ V`, this is the
element of `W^{1,p}(V)` represented by `x ↦ u (x + h)`. Its weak gradient is represented by
`x ↦ ∇u (x + h)`; see `W1p.value_translate_ae` and `W1p.gradient_translate_ae`.

Unlike extension by zero, local translation needs no boundary condition: the explicit inclusion
`V + h ⊆ Ω` ensures that only values inside the original domain are used. -/
def W1p.translate {Omega V : Opens E} {h : E} (hVO : MapsTo (· + h) V Omega)
    (u : W1p mu Omega p) : W1p mu V p := by
  let hv : MemLp (fun x => W1p.value u (x + h)) p (mu.restrict V) :=
    MeasureTheory.MemLp.comp_add_right_restrict_of_mapsTo (Lp.memLp (W1p.value u)) hVO
  let hg : MemLp (fun x => W1p.gradient u (x + h)) p (mu.restrict V) :=
    MeasureTheory.MemLp.comp_add_right_restrict_of_mapsTo (Lp.memLp (W1p.gradient u)) hVO
  let value := hv.toLp (fun x => W1p.value u (x + h))
  let gradient := hg.toLp (fun x => W1p.gradient u (x + h))
  refine W1p.mk value gradient ?_
  have hweak := (W1p.hasWeakFDerivOn u).comp_add_right hVO
  refine hweak.congr_ae hv.coeFn_toLp.symm |>.congr_ae_deriv ?_
  filter_upwards [hg.coeFn_toLp] with x hx
  rw [hx]

/-- Local translation is represented almost everywhere by precomposition with `x ↦ x + h`. -/
theorem W1p.value_translate_ae {Omega V : Opens E} {h : E}
    (hVO : MapsTo (· + h) V Omega) (u : W1p mu Omega p) :
    W1p.value (W1p.translate hVO u) =ᵐ[mu.restrict V] fun x => W1p.value u (x + h) := by
  simp only [W1p.translate, W1p.value_mk]
  exact MemLp.coeFn_toLp _

/-- The weak gradient of a local translation is represented almost everywhere by the translated
weak gradient. -/
theorem W1p.gradient_translate_ae {Omega V : Opens E} {h : E}
    (hVO : MapsTo (· + h) V Omega) (u : W1p mu Omega p) :
    W1p.gradient (W1p.translate hVO u) =ᵐ[mu.restrict V]
      fun x => W1p.gradient u (x + h) := by
  simp only [W1p.translate, W1p.gradient_mk]
  exact MemLp.coeFn_toLp _

end TauCeti
