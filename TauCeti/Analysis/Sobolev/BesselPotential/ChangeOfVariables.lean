/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.BesselPotential.Basic
public import TauCeti.Analysis.Sobolev.Wkp.ChangeOfVariables
import TauCeti.MeasureTheory.Function.Lp.CastMeasure

/-!
# Changes of variables in integer-order Bessel-potential spaces

For `1 < p < ∞` and a natural order `k`, the real Bessel-potential functions
`TemperedDistribution.realSobolevFunctions E k p` are preserved by precomposition with a change of
variables of order `k` of the whole space (`TauCeti.Wkp.IsChangeOfVariables`): a `Cᵏ`
injective map with bounded derivatives of orders `1` through `k` and Jacobian determinant bounded
away from zero. In particular they are invariant under translations and under linear
automorphisms of `E`.

The proof passes through the weak-derivative Sobolev space `W^{k,p}(E)`, which has the same real
elements by Calderón's theorem (`MeasureTheory.Lp.memSobolev_natCast_iff_exists_wkp_value_eq`), and
on which precomposition is the bounded operator `TauCeti.Wkp.compL`.

## Main results

* `TemperedDistribution.comp_mem_realSobolevFunctions_natCast`: precomposition with a change of
  variables of order `k`.
* `TemperedDistribution.comp_add_mem_realSobolevFunctions_natCast`: translations.
* `TemperedDistribution.comp_continuousLinearEquiv_mem_realSobolevFunctions_natCast`: linear
  automorphisms.
-/

public section

noncomputable section

namespace TemperedDistribution

open MeasureTheory TauCeti TopologicalSpace
open scoped ENNReal

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **Changes of variables in `H^{k,p}`.** For `1 < p < ∞` and a natural order `k`, precomposition
with a change of variables of order `k` of the whole space preserves the real Bessel-potential
functions of order `k`. -/
theorem comp_mem_realSobolevFunctions_natCast (hp : 1 < p) (hp_top : p ≠ ∞) {k : ℕ}
    {Φ : E → E} {L c : ℝ} (hΦ : Wkp.IsChangeOfVariables k ⊤ ⊤ Φ L c) {f : E → ℝ}
    (hf : f ∈ realSobolevFunctions E k p) :
    (fun x ↦ f (Φ x)) ∈ realSobolevFunctions E k p := by
  obtain ⟨u, huf, hu⟩ := mem_realSobolevFunctions.1 hf
  have hvolume : (volume : Measure E) = volume.restrict ((⊤ : Opens E) : Set E) := by simp
  -- Pass to `W^{k,p}`, precompose there with `Φ`, and return to `H^{k,p}`.
  obtain ⟨w, hw⟩ := (Lp.memSobolev_natCast_iff_exists_wkp_value_eq hp hp_top k u).1 hu
  set w' := Wkp.compL (mu := volume) hΦ hp_top w
  set u' : Lp ℝ p (volume : Measure E) := castLpₗᵢ (𝕜 := ℝ) hvolume.symm (Wkp.value k w')
  have hu' : (u' : E → ℝ) = Wkp.value k w' := funext (coeFn_castLpₗᵢ hvolume.symm _)
  refine mem_realSobolevFunctions.2 ⟨u', ?_,
    (Lp.memSobolev_natCast_iff_exists_wkp_value_eq hp hp_top k u').2
      ⟨w', .of_forall fun x ↦ by rw [hu']⟩⟩
  have hae : ae (volume.restrict ((⊤ : Opens E) : Set E)) = ae (volume : Measure E) := by
    rw [← hvolume]
  have hcomp := Wkp.value_compL_ae (mu := volume) hΦ hp_top w
  have hpull := hΦ.ae_comp (mu := volume) (P := fun y ↦ Wkp.value k w y = f y) <| by
    rw [hae]
    filter_upwards [hw, huf] with y h₁ h₂
    rw [h₁, h₂]
  rw [Filter.EventuallyEq, hae] at hcomp
  rw [hae] at hpull
  filter_upwards [hcomp, hpull] with x h₁ h₂
  rw [hu', h₁, h₂]

/-- For `1 < p < ∞` and a natural order `k`, the real Bessel-potential functions of order `k` are
invariant under translation. -/
theorem comp_add_mem_realSobolevFunctions_natCast (hp : 1 < p) (hp_top : p ≠ ∞) {k : ℕ}
    (a : E) {f : E → ℝ} (hf : f ∈ realSobolevFunctions E k p) :
    (fun x ↦ f (x + a)) ∈ realSobolevFunctions E k p :=
  comp_mem_realSobolevFunctions_natCast hp hp_top
    (Wkp.IsChangeOfVariables.add_const a (Set.mapsTo_univ _ _)) hf

/-- For `1 < p < ∞` and a natural order `k`, the real Bessel-potential functions of order `k` are
invariant under linear automorphisms of `E`. -/
theorem comp_continuousLinearEquiv_mem_realSobolevFunctions_natCast (hp : 1 < p)
    (hp_top : p ≠ ∞) {k : ℕ} (e : E ≃L[ℝ] E) {f : E → ℝ}
    (hf : f ∈ realSobolevFunctions E k p) :
    (fun x ↦ f (e x)) ∈ realSobolevFunctions E k p :=
  comp_mem_realSobolevFunctions_natCast hp hp_top
    (Wkp.IsChangeOfVariables.continuousLinearEquiv e (Set.mapsTo_univ _ _)) hf

end TemperedDistribution
