/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.BesselPotential.Basic
public import TauCeti.Analysis.Sobolev.BesselPotential.Inclusion
import TauCeti.Analysis.Sobolev.WeakDeriv.TemperedDistribution

/-!
# The directional derivative on Bessel-potential spaces, and real-valued elements

A continuous linear operator `A` on tempered distributions that maps `H^{s,p}(E, F)` into
`H^{r,p}(E, G)` is automatically bounded between these Banach spaces, by the closed graph theorem;
`BesselPotentialSpace.mapCLM` bundles such restrictions. This file applies the construction to the
directional derivative `∂_v : H^{s+1,p}(E, F) → H^{s,p}(E, F)` for `1 < p < ∞`
(`BesselPotentialSpace.lineDerivCLM`). Combined with
`TemperedDistribution.MemSobolev.smulLeftCLM_of_norm_iteratedFDeriv_le`, `mapCLM` likewise yields
multiplication by a function with bounded derivatives as a bounded operator on `H^{k,p}`; these
are the linear building blocks of differential operators with nondecaying smooth coefficients on
the Sobolev scale.

For `s ≥ 0` an element `u` of `H^{s,p}(E)` is an `Lᵖ` function, `BesselPotentialSpace.inclusionLp`.
The second part of the file describes the operators on these functions when `u` is real-valued:

* a real function `f` lies in `realSobolevFunctions E s p` exactly when `f`, viewed as a complex
  function, is almost everywhere the `Lᵖ` function of some `u ∈ H^{s,p}(E)`
  (`TemperedDistribution.mem_realSobolevFunctions_iff_exists_inclusionLp_ae_eq`);
* if moreover `f` is `C¹`, `1 < p < ∞` and `u ∈ H^{s+1,p}(E)`, then the `Lᵖ` function of `∂_v u`
  is almost everywhere the classical derivative `x ↦ fderiv ℝ f x v`
  (`BesselPotentialSpace.coeFn_inclusionLp_lineDerivCLM_ae_eq`);
* if `w` has the tempered distribution `g u` for a bounded function `g` of temperate growth, then
  the `Lᵖ` function of `w` is almost everywhere `g` times that of `u`
  (`BesselPotentialSpace.coeFn_inclusionLp_ae_eq_smul_of_toDistr_eq_smulLeftCLM`).

## Main declarations

* `BesselPotentialSpace.lineDerivCLM`: the directional derivative
  `H^{s+1,p}(E, F) →L[ℂ] H^{s,p}(E, F)` for `1 < p < ∞`.
-/

public section

noncomputable section

open MeasureTheory TemperedDistribution
open scoped ENNReal SchwartzMap BesselPotentialSpace LineDeriv

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

namespace BesselPotentialSpace

section lineDerivCLM

variable [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F] {s : ℝ} {p : ℝ≥0∞}
  [Fact (1 ≤ p)]

/-- **The directional derivative on the Sobolev scale.** For `1 < p < ∞`, the derivative `∂_v` in
the direction `v`, as a bounded operator `H^{s+1,p}(E, F) →L[ℂ] H^{s,p}(E, F)`
(`TemperedDistribution.MemSobolev.lineDerivOp_of_one_lt`). -/
def lineDerivCLM (hp : 1 < p) (hp_top : p ≠ ∞) (v : E) :
    H^{s + 1, p}(E, F) →L[ℂ] H^{s, p}(E, F) :=
  mapCLM (LineDeriv.lineDerivOpCLM ℂ 𝓢'(E, F) v) fun u ↦ by
    simpa using u.memSobolev_toDistr.lineDerivOp_of_one_lt hp hp_top (m := v)

/-- `lineDerivCLM hp hp_top v` acts on the underlying tempered distributions by `∂_v`. -/
@[simp]
theorem toDistr_lineDerivCLM (hp : 1 < p) (hp_top : p ≠ ∞) (v : E) (u : H^{s + 1, p}(E, F)) :
    (lineDerivCLM hp hp_top v u).toDistr = ∂_{v} u.toDistr := by
  simp [lineDerivCLM]

end lineDerivCLM

end BesselPotentialSpace

/-! ### Real-valued elements -/

namespace TemperedDistribution

/-- **Real Sobolev functions are elements of `H^{s,p}(E)`.** For `s ≥ 0`, a real function `f` lies
in `realSobolevFunctions E s p` exactly when the complex function `x ↦ (f x : ℂ)` is almost
everywhere the `Lᵖ` function of an element of `H^{s,p}(E)`. -/
theorem mem_realSobolevFunctions_iff_exists_inclusionLp_ae_eq {s : ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hs : 0 ≤ s) {f : E → ℝ} :
    f ∈ realSobolevFunctions E s p ↔
      ∃ u : H^{s, p}(E), ⇑(BesselPotentialSpace.inclusionLp hs u) =ᵐ[volume]
        fun x ↦ (f x : ℂ) := by
  constructor
  · rintro hf
    obtain ⟨u, huf, hu⟩ := mem_realSobolevFunctions.1 hf
    refine ⟨hu.toBesselPotentialSpace, ?_⟩
    rw [(BesselPotentialSpace.inclusionLp_eq_iff hs (f := Complex.ofRealCLM.compLp u)).2 (by simp)]
    filter_upwards [Complex.ofRealCLM.coeFn_compLp (p := p) (μ := volume) u, huf]
      with x h h'
    rw [h, Complex.ofRealCLM_apply, h']
  · rintro ⟨u, hu⟩
    refine mem_realSobolevFunctions_of_ae_eq_ofReal ?_ hu
    rw [BesselPotentialSpace.toTemperedDistribution_inclusionLp]
    exact u.memSobolev_toDistr

end TemperedDistribution

namespace BesselPotentialSpace

/-- **Classical derivatives of real elements of `H^{s+1,p}`.** For `1 < p < ∞` and `s ≥ 0`, if the
`Lᵖ` function of `u ∈ H^{s+1,p}(E)` is almost everywhere a real `C¹` function `f`, then the `Lᵖ`
function of the derivative `∂_v u ∈ H^{s,p}(E)` is almost everywhere its classical derivative
`x ↦ fderiv ℝ f x v`. -/
theorem coeFn_inclusionLp_lineDerivCLM_ae_eq {s : ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : 1 < p)
    (hp_top : p ≠ ∞) (hs : 0 ≤ s) {f : E → ℝ} (hf : ContDiff ℝ 1 f) {u : H^{s + 1, p}(E)}
    (hu : ⇑(inclusionLp (by linarith) u) =ᵐ[volume] fun x ↦ (f x : ℂ)) (v : E) :
    ⇑(inclusionLp hs (lineDerivCLM hp hp_top v u)) =ᵐ[volume] fun x ↦ (fderiv ℝ f x v : ℂ) := by
  have hmem := (mem_realSobolevFunctions_iff_exists_inclusionLp_ae_eq (by linarith)).2 ⟨u, hu⟩
  obtain ⟨u₀, hu₀f, -⟩ := mem_realSobolevFunctions.1 hmem
  obtain ⟨u', hu'f, -⟩ := mem_realSobolevFunctions.1
    (fderiv_apply_mem_realSobolevFunctions hp hp_top hs hf hmem v)
  -- The tempered distribution of `u` is that of the real function `u₀`.
  have hu₀ : u.toDistr = Lp.toTemperedDistribution (Complex.ofRealCLM.compLp u₀) := by
    rw [← toTemperedDistribution_inclusionLp (by linarith : 0 ≤ s + 1)]
    congr 1
    refine Lp.ext ?_
    filter_upwards [Complex.ofRealCLM.coeFn_compLp (p := p) (μ := volume) u₀, hu₀f, hu]
      with x h h' h''
    rw [h'', h, Complex.ofRealCLM_apply, h']
  have hd : inclusionLp hs (lineDerivCLM hp hp_top v u) = Complex.ofRealCLM.compLp u' := by
    rw [inclusionLp_eq_iff, toDistr_lineDerivCLM, hu₀,
      TauCeti.lineDerivOp_toTemperedDistribution_ofReal_eq_of_contDiff hf hu₀f hu'f]
  filter_upwards [Complex.ofRealCLM.coeFn_compLp (p := p) (μ := volume) u', hu'f] with x h h'
  rw [hd, h, Complex.ofRealCLM_apply, h']

variable [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F] {r s : ℝ} {p : ℝ≥0∞}
  [Fact (1 ≤ p)]

/-- **Multiplication by a bounded function on `Lᵖ` functions.** For `r, s ≥ 0`, if
`w ∈ H^{r,p}(E, F)` has the tempered distribution `g u` of `u ∈ H^{s,p}(E, F)`, for a bounded
function `g` of temperate growth, then the `Lᵖ` function of `w` is almost everywhere `g` times
that of `u`. -/
theorem coeFn_inclusionLp_ae_eq_smul_of_toDistr_eq_smulLeftCLM (hr : 0 ≤ r) (hs : 0 ≤ s)
    {g : E → ℂ} (hg : g.HasTemperateGrowth) {C : ℝ} (hC : ∀ x, ‖g x‖ ≤ C)
    {u : H^{s, p}(E, F)} {w : H^{r, p}(E, F)} (hw : w.toDistr = smulLeftCLM F g u.toDistr) :
    ⇑(inclusionLp hr w) =ᵐ[volume] fun x ↦ g x • inclusionLp hs u x := by
  have hmem : MemLp g ⊤ (volume : Measure E) :=
    memLp_top_of_bound hg.1.continuous.aestronglyMeasurable C (ae_of_all _ hC)
  have h : inclusionLp hr w = hmem.toLp g • inclusionLp hs u := by
    rw [inclusionLp_eq_iff, Lp.toTemperedDistribution_smul_eq hg hmem, hw,
      toTemperedDistribution_inclusionLp]
  filter_upwards [Lp.coeFn_lpSMul (p := ⊤) (q := p) (r := p) (hmem.toLp g) (inclusionLp hs u),
    hmem.coeFn_toLp] with x h₁ h₂
  rw [h, h₁, Pi.smul_apply', h₂]

end BesselPotentialSpace
