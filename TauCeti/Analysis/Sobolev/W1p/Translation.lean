/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.W1p.Basic
public import TauCeti.Analysis.Sobolev.W1p.Zero
import TauCeti.Analysis.Sobolev.W1p.MeasurePreserving
import TauCeti.Analysis.Sobolev.WeakDeriv.Translation
import TauCeti.MeasureTheory.Function.Lp.Translation

/-!
# Local translations of `W^{1,p}` functions

This file packages translation by a vector as an element of `W^{1,p}` on any smaller open set
whose translate stays inside the original domain. Translation commutes with the weak gradient,
and on a domain mapped onto itself by the translation it preserves zero boundary values.

## Main declarations

* `TauCeti.W1p.translate`: local translation from `W^{1,p}(Ω)` to `W^{1,p}(V)` when
  `V + h ⊆ Ω`.
* `TauCeti.W1p.value_translate_ae`: the value of a local translation.
* `TauCeti.W1p.gradient_translate_ae`: the weak gradient of a local translation.
* `TauCeti.W1p.translate_mem_w1p0Submodule`: translation preserves `W^{1,p}_0(Ω)` when it maps
  `Ω` onto itself.
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

/-- **Translation preserves zero boundary values.** If translation by `h` maps `Ω` onto itself,
that is `x + h ∈ Ω ↔ x ∈ Ω`, then for `p < ∞` the translate `x ↦ u (x + h)` of
`u ∈ W^{1,p}_0(Ω)` again lies in `W^{1,p}_0(Ω)`. A half-space, for instance, is mapped onto itself
by every translation parallel to its boundary. -/
theorem W1p.translate_mem_w1p0Submodule (hp : p ≠ ∞) {h : E} (hVO : MapsTo (· + h) Omega Omega)
    (hΩ : ∀ x, x + h ∈ Omega → x ∈ Omega) {u : W1p mu Omega p}
    (hu : u ∈ w1p0Submodule mu Omega p) :
    W1p.translate hVO u ∈ w1p0Submodule mu Omega p := by
  have hUV : (Omega : Set E) = (· + h) ⁻¹' Omega :=
    Subset.antisymm (fun x hx => hVO hx) fun x hx => hΩ x hx
  have hl : LocallyLipschitzOn (Omega : Set E) (· + h) :=
    (isometry_add_right h).lipschitzWith.locallyLipschitz.locallyLipschitzOn
  have hM : ∀ x ∈ (Omega : Set E), ‖fderiv ℝ (· + h) x‖ ≤ 1 := fun x _ => by
    rw [fderiv_add_const, fderiv_fun_id]
    exact ContinuousLinearMap.norm_id_le
  -- The translate is the composition with the measure-preserving homeomorphism `x ↦ x + h`.
  have heq : W1p.translate hVO u =
      W1p.compMeasurePreservingL (measurePreserving_add_right mu h) hUV hl hM u :=
    W1p.ext_value (Lp.ext ((W1p.value_translate_ae _ u).trans
      (W1p.value_compMeasurePreservingL_ae _ hUV hl hM u).symm))
  rw [heq]
  exact W1p.compMeasurePreservingL_mem_w1p0Submodule hp (Homeomorph.addRight h).isProperMap
    (measurePreserving_add_right mu h) hUV hl hM hu

end TauCeti
