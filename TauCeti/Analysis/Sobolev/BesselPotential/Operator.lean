/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.BesselPotential.Basic
public import TauCeti.Analysis.Sobolev.BesselPotential.Inclusion

/-!
# Bounded operators on Bessel-potential spaces from operators on tempered distributions

A continuous linear operator `A` on tempered distributions that maps `H^{s,p}(E, F)` into
`H^{r,p}(E, G)` is automatically bounded between these Banach spaces, by the closed graph theorem
(`BesselPotentialSpace.continuous_of_continuous_toDistr`). This file bundles such restrictions
(`BesselPotentialSpace.mapCLM`) and applies the construction to the directional derivative
`∂_v : H^{s+1}(E, F) → H^s(E, F)` (`BesselPotentialSpace.lineDerivCLM`). With
`TemperedDistribution.MemSobolev.smulLeftCLM_of_norm_iteratedFDeriv_le` it also gives
multiplication by a function with bounded derivatives as a bounded operator on `H^{k,p}`.
These are the linear building blocks of differential operators with nondecaying smooth
coefficients on the Sobolev scale, and polynomial field equations built from them and the products
`BesselPotentialSpace.mulCLM` are smooth maps between Bessel-potential spaces.

For `s ≥ 0` an element `u` of `H^{s}(E)` is an `L²` function, `BesselPotentialSpace.inclusionLp`.
The second part of the file describes the operators on these functions when `u` is real-valued:

* a real function `f` lies in `realSobolevFunctions E s p` exactly when `f`, viewed as a complex
  function, is almost everywhere the `Lᵖ` function of some `u ∈ H^{s,p}(E)`
  (`TemperedDistribution.mem_realSobolevFunctions_iff_exists_inclusionLp_ae_eq`);
* if moreover `f` is `C¹` and `u ∈ H^{s+1}(E)`, then the `L²` function of `∂_v u` is almost
  everywhere the classical derivative `x ↦ fderiv ℝ f x v`
  (`BesselPotentialSpace.coeFn_inclusionLp_lineDerivCLM_ae_eq`);
* if `w` has the tempered distribution `g u` for a bounded function `g` of temperate growth, then
  the `L²` function of `w` is almost everywhere `g` times that of `u`
  (`BesselPotentialSpace.coeFn_inclusionLp_ae_eq_smul_of_toDistr_eq_smulLeftCLM`).

## Main declarations

* `BesselPotentialSpace.mapCLM`: the restriction `H^{s,p}(E, F) →L[ℂ] H^{r,p}(E, G)` of an operator
  on tempered distributions that maps `H^{s,p}` into `H^{r,p}`.
* `BesselPotentialSpace.lineDerivCLM`: the directional derivative `H^{s+1}(E, F) →L[ℂ] H^s(E, F)`.
-/

public section

noncomputable section

open MeasureTheory TemperedDistribution
open scoped ENNReal SchwartzMap BesselPotentialSpace LineDeriv

variable {E F G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

namespace BesselPotentialSpace

section mapCLM

variable [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [NormedSpace ℂ G] [CompleteSpace G] {r s : ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **Restriction of an operator on tempered distributions to Bessel-potential spaces.** A
continuous linear map `A : 𝓢'(E, F) →L[ℂ] 𝓢'(E, G)` that maps `H^{s,p}(E, F)` into
`H^{r,p}(E, G)` restricts to a bounded operator between these spaces; its continuity is the
closed graph theorem. The restriction keeps the action of `A` on the underlying tempered
distributions (`BesselPotentialSpace.toDistr_mapCLM`). -/
def mapCLM (A : 𝓢'(E, F) →L[ℂ] 𝓢'(E, G)) (hA : ∀ u : H^{s, p}(E, F), MemSobolev r p (A u.toDistr)) :
    H^{s, p}(E, F) →L[ℂ] H^{r, p}(E, G) :=
  let L : H^{s, p}(E, F) →ₗ[ℂ] H^{r, p}(E, G) :=
    { toFun u := (hA u).toBesselPotentialSpace
      map_add' u v := ext (by simp)
      map_smul' c u := ext (by simp) }
  { L with
    cont := continuous_of_continuous_toDistr (L.restrictScalars ℝ) <|
      (A.continuous.comp continuous_toDistr).congr fun u ↦ by simp [L] }

/-- `mapCLM A hA` acts on the underlying tempered distributions by `A`. -/
@[simp]
theorem toDistr_mapCLM (A : 𝓢'(E, F) →L[ℂ] 𝓢'(E, G))
    (hA : ∀ u : H^{s, p}(E, F), MemSobolev r p (A u.toDistr)) (u : H^{s, p}(E, F)) :
    (mapCLM A hA u).toDistr = A u.toDistr :=
  MemSobolev.toBesselPotentialSpace_toDistr _

end mapCLM

section lineDerivCLM

variable [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F] {s : ℝ}

/-- **The directional derivative on the Sobolev scale.** The derivative `∂_v` in the direction
`v`, as a bounded operator `H^{s+1}(E, F) →L[ℂ] H^s(E, F)`
(`TemperedDistribution.MemSobolev.lineDerivOp`). -/
def lineDerivCLM (v : E) : H^{s + 1}(E, F) →L[ℂ] H^{s}(E, F) :=
  mapCLM (LineDeriv.lineDerivOpCLM ℂ 𝓢'(E, F) v) fun u ↦ by
    simpa using u.memSobolev_toDistr.lineDerivOp (m := v)

/-- `lineDerivCLM v` acts on the underlying tempered distributions by `∂_v`. -/
@[simp]
theorem toDistr_lineDerivCLM (v : E) (u : H^{s + 1}(E, F)) :
    (lineDerivCLM v u).toDistr = ∂_{v} u.toDistr := by
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
    -- The real part of the `Lᵖ` function of `u` is a real `Lᵖ` representative of `f`.
    set w := BesselPotentialSpace.inclusionLp hs u
    have hre : ⇑(Complex.reCLM.compLp w) =ᵐ[volume] f := by
      filter_upwards [Complex.reCLM.coeFn_compLp (p := p) (μ := volume) w, hu] with x h h'
      rw [h, Complex.reCLM_apply, h', Complex.ofReal_re]
    have hw : Complex.ofRealCLM.compLp (Complex.reCLM.compLp w) = w := by
      refine Lp.ext ?_
      filter_upwards [Complex.ofRealCLM.coeFn_compLp (p := p) (μ := volume)
        (Complex.reCLM.compLp w), hre, hu] with x h h' h''
      rw [h, Complex.ofRealCLM_apply, h', h'']
    refine mem_realSobolevFunctions.2 ⟨Complex.reCLM.compLp w, hre, ?_⟩
    rw [hw, BesselPotentialSpace.toTemperedDistribution_inclusionLp]
    exact u.memSobolev_toDistr

end TemperedDistribution

namespace BesselPotentialSpace

/-- **Classical derivatives of real elements of `H^{s+1}`.** For `s ≥ 0`, if the `L²` function of
`u ∈ H^{s+1}(E)` is almost everywhere a real `C¹` function `f`, then the `L²` function of the
derivative `∂_v u ∈ H^s(E)` is almost everywhere its classical derivative `x ↦ fderiv ℝ f x v`. -/
theorem coeFn_inclusionLp_lineDerivCLM_ae_eq {s : ℝ} (hs : 0 ≤ s) {f : E → ℝ}
    (hf : ContDiff ℝ 1 f) {u : H^{s + 1}(E)}
    (hu : ⇑(inclusionLp (by linarith) u) =ᵐ[volume] fun x ↦ (f x : ℂ)) (v : E) :
    ⇑(inclusionLp hs (lineDerivCLM v u)) =ᵐ[volume] fun x ↦ (fderiv ℝ f x v : ℂ) := by
  have hmem := (mem_realSobolevFunctions_iff_exists_inclusionLp_ae_eq (by linarith)).2 ⟨u, hu⟩
  obtain ⟨u₀, hu₀f, -⟩ := mem_realSobolevFunctions.1 hmem
  obtain ⟨u', hu'f, -⟩ := mem_realSobolevFunctions.1
    (fderiv_apply_mem_realSobolevFunctions (by norm_num) (by norm_num) hs hf hmem v)
  -- The tempered distribution of `u` is that of the real function `u₀`.
  have hu₀ : u.toDistr = Lp.toTemperedDistribution (Complex.ofRealCLM.compLp u₀) := by
    rw [← toTemperedDistribution_inclusionLp (by linarith : 0 ≤ s + 1)]
    congr 1
    refine Lp.ext ?_
    filter_upwards [Complex.ofRealCLM.coeFn_compLp (p := 2) (μ := volume) u₀, hu₀f, hu]
      with x h h' h''
    rw [h'', h, Complex.ofRealCLM_apply, h']
  have hd : inclusionLp hs (lineDerivCLM v u) = Complex.ofRealCLM.compLp u' := by
    rw [inclusionLp_eq_iff, toDistr_lineDerivCLM, hu₀,
      TauCeti.lineDerivOp_toTemperedDistribution_ofReal_eq_of_contDiff hf hu₀f hu'f]
  filter_upwards [Complex.ofRealCLM.coeFn_compLp (p := 2) (μ := volume) u', hu'f] with x h h'
  rw [hd, h, Complex.ofRealCLM_apply, h']

variable [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F] {r s : ℝ} {p : ℝ≥0∞}
  [Fact (1 ≤ p)]

/-- **Multiplication by a bounded function on `L²` functions.** For `r, s ≥ 0`, if
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
