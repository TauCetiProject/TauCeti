/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.BesselPotential.Basic
public import TauCeti.Analysis.Distribution.Sobolev
import TauCeti.Analysis.Sobolev.Wkp.Density
import TauCeti.Analysis.Sobolev.Wkp.Multiplication
import TauCeti.MeasureTheory.Function.Lp.CastMeasure

/-!
# Nondecaying smooth multipliers on integer-order Bessel-potential spaces

A smooth real coefficient with bounded derivatives through order `k` preserves `H^{k,p}`
for `1 < p < ∞`. In contrast to multiplication by a test function, the coefficient need not
vanish at infinity. This is needed when a differential equation is expanded about a smooth
background which is not itself integrable.

The result uses the whole-space equality `W^{k,p}_0 = W^{k,p}`, the bounded multiplier
`TauCeti.Wkp0.contDiffSMulL`, and the weak-derivative/Bessel-potential comparison. It provides
an actual `Lᵖ` representative of the product, not merely a distributional existence statement.
Only derivatives through the specified integer order are required to be bounded. No bound in
the Bessel-potential norm, or statement for noninteger orders, is asserted here.

## References

* L. C. Evans, *Partial Differential Equations*, §5.2.3 and §5.3.2.
* E. M. Stein, *Singular Integrals and Differentiability Properties of Functions*, Chapter V, §3.
-/

public section

namespace TemperedDistribution

open MeasureTheory TauCeti
open scoped ContDiff

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E]

/-- A smooth real coefficient whose derivatives through order `k` are bounded preserves
integer-order `H^{k,p}`. The product has a real `Lᵖ` representative with the asserted Sobolev
regularity. The coefficient need not decay or be integrable. -/
theorem exists_mem_realSobolevSubmodule_ae_eq_mul_of_bounded_derivatives
    {p : ENNReal} [Fact (1 ≤ p)] (hp : 1 < p) (hp_top : p ≠ ⊤) (k : ℕ)
    {ψ : E → ℝ} (hψ : ContDiff ℝ ∞ ψ) {M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ j ≤ k, ∀ x, ‖iteratedFDeriv ℝ j ψ x‖ ≤ M)
    {u : Lp ℝ p (volume : Measure E)} (hu : u ∈ realSobolevSubmodule E k p) :
    ∃ v : Lp ℝ p (volume : Measure E), v ∈ realSobolevSubmodule E k p ∧
      (v : E → ℝ) =ᵐ[volume] fun x ↦ ψ x * u x := by
  obtain ⟨w, hw⟩ := (Lp.memSobolev_natCast_iff_exists_wkp_value_eq hp hp_top k u).mp
    (mem_realSobolevSubmodule.mp hu)
  have hw₀ : w ∈ wkp0Submodule (volume : Measure E) ⊤ p k := by
    rw [wkp0Submodule_top_eq_top hp_top]
    trivial
  let v₀ := Wkp0.contDiffSMulL k hψ ⟨w, hw₀⟩
  -- The weak-Sobolev value uses volume restricted to the whole space. Transport the
  -- measure explicitly; its chosen Lᵖ representative is unchanged by this transport.
  have hvolume : (volume : Measure E).restrict (⊤ : TopologicalSpace.Opens E) = volume := by
    simp
  let v : Lp ℝ p (volume : Measure E) := castLpₗᵢ (𝕜 := ℝ) hvolume (Wkp.value k v₀.val)
  have hvval (x : E) : v x = Wkp.value k v₀.val x := coeFn_castLpₗᵢ hvolume _ x
  have hv : (v : E → ℝ) =ᵐ[volume] fun x ↦ ψ x * Wkp.value k w x := by
    have h := Wkp0.value_contDiffSMulL_ae (mu := (volume : Measure E)) (Omega := ⊤)
      (p := p) k hψ hM (fun j hj x _ ↦ hbound j hj x) ⟨w, hw₀⟩
    have h' := (ae_restrict_iff' (⊤ : TopologicalSpace.Opens E).isOpen.measurableSet).mp h
    filter_upwards [h'] with x hx
    exact (hvval x).trans (hx (Set.mem_univ x))
  refine ⟨v, mem_realSobolevSubmodule.mpr ?_, ?_⟩
  · apply (Lp.memSobolev_natCast_iff_exists_wkp_value_eq hp hp_top k v).mpr
    exact ⟨v₀.val, Filter.Eventually.of_forall fun x ↦ (hvval x).symm⟩
  · filter_upwards [hv, hw] with x hvx hwx
    rw [hvx, hwx]

end TemperedDistribution
