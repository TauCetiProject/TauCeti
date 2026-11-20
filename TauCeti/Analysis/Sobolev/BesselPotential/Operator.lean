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
(`BesselPotentialSpace.lineDerivCLM`) and to the Laplacian `Δ : H^s(E, F) → H^{s-2}(E, F)` on the
`L²` scale (`BesselPotentialSpace.laplacianCLM`). Combined with
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
* if `f` is `C²` and `u ∈ H^{s+2}(E)`, then the `L²` function of `Δu` is almost everywhere the
  classical Laplacian `Δf` (`BesselPotentialSpace.coeFn_inclusionLp_laplacianCLM_ae_eq`);
* if `w` has the tempered distribution `g u` for a bounded function `g` of temperate growth, then
  the `Lᵖ` function of `w` is almost everywhere `g` times that of `u`
  (`BesselPotentialSpace.coeFn_inclusionLp_ae_eq_smul_of_toDistr_eq_smulLeftCLM`).

## Main declarations

* `BesselPotentialSpace.lineDerivCLM`: the directional derivative
  `H^{s+1,p}(E, F) →L[ℂ] H^{s,p}(E, F)` for `1 < p < ∞`.
* `BesselPotentialSpace.laplacianCLM`: the Laplacian `H^s(E, F) →L[ℂ] H^{s-2}(E, F)`.
-/

public section

noncomputable section

open MeasureTheory TemperedDistribution
open scoped ENNReal SchwartzMap BesselPotentialSpace LineDeriv Laplacian

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

section laplacianCLM

variable [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F] {r s : ℝ}

/-- **The Laplacian on the `L²` Sobolev scale.** The Laplacian `Δ` of tempered distributions, as a
bounded operator `H^s(E, F) →L[ℂ] H^r(E, F)` for `r = s - 2`
(`TemperedDistribution.MemSobolev.laplacian`). The target order is any `r` equal to `s - 2`, so
that it can be stated in the form a caller needs, for instance `H^2 → H^0`. -/
def laplacianCLM (h : r = s - 2) : H^{s}(E, F) →L[ℂ] H^{r}(E, F) :=
  mapCLM (LineDeriv.laplacianCLM ℂ E 𝓢'(E, F)) fun u ↦ by
    rw [TemperedDistribution.laplacianCLM_apply, h]
    exact u.memSobolev_toDistr.laplacian

/-- `laplacianCLM h` acts on the underlying tempered distributions by `Δ`. -/
@[simp]
theorem toDistr_laplacianCLM (h : r = s - 2) (u : H^{s}(E, F)) :
    (laplacianCLM h u).toDistr = Δ u.toDistr := by
  simp [laplacianCLM]

end laplacianCLM

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

/-- **The classical Laplacian of real elements of `H^{s+2}`.** For `s ≥ 0`, if the `L²` function
of `u ∈ H^t(E)`, `t = s + 2`, is almost everywhere a real `C²` function `f`, then the `L²` function
of `Δu ∈ H^s(E)` is almost everywhere the classical Laplacian `Δf`. -/
theorem coeFn_inclusionLp_laplacianCLM_ae_eq {s t : ℝ} (hs : 0 ≤ s) (ht : s = t - 2) {f : E → ℝ}
    (hf : ContDiff ℝ 2 f) {u : H^{t}(E)}
    (hu : ⇑(inclusionLp (by linarith) u) =ᵐ[volume] fun x ↦ (f x : ℂ)) :
    ⇑(inclusionLp hs (laplacianCLM ht u)) =ᵐ[volume] fun x ↦ (Δ f x : ℂ) := by
  set b := stdOrthonormalBasis ℝ E
  set u' : H^{s + 1 + 1}(E) := u.copy (s + 1 + 1) (by linarith)
  set D : E → H^{s + 1}(E) →L[ℂ] H^{s}(E) :=
    lineDerivCLM ENNReal.one_lt_two ENNReal.ofNat_ne_top
  set D' : E → H^{s + 1 + 1}(E) →L[ℂ] H^{s + 1}(E) :=
    lineDerivCLM ENNReal.one_lt_two ENNReal.ofNat_ne_top
  have hu' : ⇑(inclusionLp (by linarith) u') =ᵐ[volume] fun x ↦ (f x : ℂ) := by
    have h : inclusionLp (by linarith : (0 : ℝ) ≤ s + 1 + 1) u' = inclusionLp (by linarith) u := by
      rw [inclusionLp_eq_iff, toTemperedDistribution_inclusionLp]
      exact (toDistr_copy u (by linarith : t = s + 1 + 1)).symm
    rwa [h]
  -- Each second derivative `∂_{b i} ∂_{b i} u` is the classical one.
  have hd (i : _) : ⇑(inclusionLp hs (D (b i) (D' (b i) u'))) =ᵐ[volume]
      fun x ↦ (fderiv ℝ (fun y ↦ fderiv ℝ f y (b i)) x (b i) : ℂ) :=
    coeFn_inclusionLp_lineDerivCLM_ae_eq ENNReal.one_lt_two ENNReal.ofNat_ne_top hs
      ((hf.fderiv_right le_rfl).clm_apply contDiff_const)
      (coeFn_inclusionLp_lineDerivCLM_ae_eq ENNReal.one_lt_two ENNReal.ofNat_ne_top (by linarith)
        (hf.of_le one_le_two) hu' (b i)) (b i)
  -- `Δu` is the sum of the second derivatives `∂_{b i} ∂_{b i} u`.
  have hsum : laplacianCLM ht u = ∑ i, D (b i) (D' (b i) u') := by
    refine ext ?_
    have hmap (S : Finset _) : (∑ i ∈ S, D (b i) (D' (b i) u')).toDistr =
        ∑ i ∈ S, (D (b i) (D' (b i) u')).toDistr := by
      induction S using Finset.induction_on with
      | empty => rfl
      | insert a S ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, toDistr_add, ih]
    rw [hmap, toDistr_laplacianCLM, TemperedDistribution.laplacian_eq_sum b]
    have hcopy : u'.toDistr = u.toDistr := toDistr_copy u (by linarith)
    simp only [D, D', toDistr_lineDerivCLM, hcopy]
  rw [hsum, map_sum]
  filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ
      fun i ↦ inclusionLp hs (D (b i) (D' (b i) u')),
    ae_all_iff.2 hd] with x h₁ h₂
  rw [h₁, InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis f b, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [h₂ i, iteratedFDeriv_two_apply, fderiv_clm_apply
    ((hf.fderiv_right le_rfl).differentiable one_ne_zero x) (differentiableAt_const _)]
  simp

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
