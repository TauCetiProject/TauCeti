/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.CompactSupport
public import TauCeti.Analysis.Sobolev.W1p.Density
public import TauCeti.Analysis.Sobolev.W1p.Extension
public import TauCeti.Analysis.Sobolev.W1p.Restriction

/-!
# Compactly supported Sobolev functions have zero boundary values

`W^{1,p}_0(Ω)` is the closure of the test functions `C_c^∞(Ω)` in `W^{1,p}(Ω)`, the Sobolev form
of the homogeneous Dirichlet condition.  Deciding that a given function lies in it is, in
general, a boundary question.  This file settles the case in which there is no boundary to
answer for: if `u ∈ W^{1,p}(Ω)` vanishes almost everywhere outside a **compact** `K ⊆ Ω`, then

`u ∈ W^{1,p}_0(Ω)`.

Only the value component is assumed to vanish; the gradient then vanishes off `K` by itself,
because a Sobolev function that vanishes on an open set has vanishing weak gradient there
(`TauCeti.W1p.gradient_ae_eq_zero_of_value_ae_eq_zero`).

## The argument

Extending `u` by zero gives a genuine element of `W^{1,p}(ℝⁿ)`
(`TauCeti.HasWeakFDerivOn.indicator_of_isCompact`), which is where the compact support is used:
for a general `u ∈ W^{1,p}(Ω)` the zero-extension need not be weakly differentiable at all.  On
the whole space every Sobolev function is a limit of test functions
(`TauCeti.W1p.mem_w1p0Submodule_top`), but those test functions are supported anywhere in `ℝⁿ`,
so they do not exhibit `u` as a limit of test functions *on `Ω`*.  Multiplying by a cutoff `χ`
which is `1` on `K` and compactly supported inside `Ω` repairs that: it leaves the extension of
`u` unchanged, while carrying every test function on `ℝⁿ` to a test function on `Ω`.  Since
`W^{1,p}_0(Ω)` is closed, the limit stays in it, and restricting the extension back to `Ω` gives
`u` itself.  This step uses only that the cutoff is bounded, with bounded gradient, and supported
in `Ω` (`TauCeti.W1p.restrictL_contDiffSMul_mem_w1p0Submodule`).

## Consequences

`TauCeti.W1p.contDiffSMul_mem_w1p0Submodule_of_hasCompactSupport` is the form localization
arguments use: multiplying *any* `u ∈ W^{1,p}(Ω)` by a smooth cutoff compactly supported in `Ω`
produces an element of `W^{1,p}_0(Ω)`.  The companion
`TauCeti.W1p.contDiffSMul_mem_w1p0Submodule` needs `u` to lie in `W^{1,p}_0(Ω)` already, which is
exactly what the compact support replaces here.  This is the localization step of Meyers--Serrin
density and of interior estimates.

`TauCeti.W1p.restrictL_contDiffSMul_mem_w1p0Submodule` needs no compact support, only a function
given on the whole space: for `w ∈ W^{1,p}(ℝⁿ)` and a bounded smooth `ψ` with
bounded gradient and `tsupport ψ ⊆ Ω`, the restriction of `ψ w` to `Ω` lies in `W^{1,p}_0(Ω)`.
Neither `ψ` nor `w` need have compact support, so it applies to unbounded `Ω` such as a half-space.

## Main declarations

* `TauCeti.W1p.mem_w1p0Submodule_of_isCompact`: a compactly supported Sobolev function has zero
  boundary values.
* `TauCeti.W1p.contDiffSMul_mem_w1p0Submodule_of_hasCompactSupport`: multiplication by a
  compactly supported cutoff lands in `W^{1,p}_0(Ω)`.
* `TauCeti.W1p.restrictL_contDiffSMul_mem_w1p0Submodule`: a whole-space Sobolev function times a
  bounded cutoff supported in `Ω`, restricted to `Ω`, lies in `W^{1,p}_0(Ω)`.
* `TauCeti.W1p.value_extendByZeroL_contDiffSMul_ae` and
  `TauCeti.W1p.gradient_extendByZeroL_contDiffSMul_ae`: the value and weak gradient of a cutoff
  product extended by zero to the whole space.
* `TauCeti.W1p.exists_top_value_gradient_ae_eq_on_of_isCompact`: near a compact subset of `Ω`,
  a function in `W^{1,p}(Ω)` agrees in value and gradient with one in `W^{1,p}(ℝⁿ)`.

## References

L. C. Evans, *Partial Differential Equations*, §5.3.3; H. Brezis, *Functional Analysis,
Sobolev Spaces and Partial Differential Equations*, Lemma 9.5.
-/

public section

noncomputable section

open MeasureTheory Set TopologicalSpace Filter Topology

open scoped ContDiff Distributions ENNReal Gradient InnerProductSpace

namespace TauCeti

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure]
  {Omega : Opens E} {p : ENNReal} [Fact (1 ≤ p)] {K : Set E}

/-! ### Zero boundary values -/

/-- **A whole-space Sobolev function cut off inside `Ω` has zero boundary values on `Ω`.**  Let
`w ∈ W^{1,p}(ℝⁿ)`, `1 ≤ p < ∞`, and let `ψ` be smooth with `|ψ| ≤ M`, `‖∇ψ‖ ≤ M` and
`tsupport ψ ⊆ Ω`.  Then the restriction of `ψ w` to `Ω` lies in `W^{1,p}_0(Ω)`.

Neither `ψ` nor `w` is assumed compactly supported: `w` is a limit of test functions on the whole
space, and the cutoff carries each of them to a test function on `Ω`. -/
theorem W1p.restrictL_contDiffSMul_mem_w1p0Submodule (hp : p ≠ (∞ : ℝ≥0∞)) {psi : E → ℝ}
    (hpsi : ContDiff ℝ ∞ psi) {M : ℝ} (hM : 0 ≤ M)
    (hpsiM : ∀ x ∈ (⊤ : Opens E), |psi x| ≤ M) (hgradM : ∀ x ∈ (⊤ : Opens E), ‖∇ psi x‖ ≤ M)
    (hts : tsupport psi ⊆ (Omega : Set E)) (w : W1p mu ⊤ p) :
    W1p.restrictL le_top (W1p.contDiffSMul psi hpsi hM hpsiM hgradM w) ∈
      w1p0Submodule mu Omega p := by
  -- The functions with this property form a closed set containing every test function.
  have hclosed : IsClosed {v : W1p mu ⊤ p | W1p.restrictL le_top
      (W1p.contDiffSMulL psi hpsi hM hpsiM hgradM v) ∈ w1p0Submodule mu Omega p} :=
    (w1p0Submodule mu Omega p).isClosed.preimage
      ((W1p.restrictL le_top).comp (W1p.contDiffSMulL psi hpsi hM hpsiM hgradM)).continuous
  suffices htest : ∀ phi : 𝓓((⊤ : Opens E), ℝ), W1p.restrictL le_top
      (W1p.contDiffSMulL psi hpsi hM hpsiM hgradM (W1p.ofTestFunctionₗ mu ⊤ p phi)) ∈
        w1p0Submodule mu Omega p by
    have hmem := w1p0Submodule_subset_of_isClosed hclosed
      (fun phi => by rw [mem_ofPred_eq]; exact htest phi) (W1p.mem_w1p0Submodule_top hp w)
    rw [mem_ofPred_eq, W1p.contDiffSMulL_apply] at hmem
    exact hmem
  intro phi
  -- The cutoff of a test function on the whole space is a test function on `Ω`.
  let Phi : 𝓓((⊤ : Opens E), ℝ) := ⟨psi * (phi : E → ℝ), hpsi.mul phi.contDiff,
    phi.hasCompactSupport.mul_left, by simp⟩
  let Psi : 𝓓(Omega, ℝ) := ⟨psi * (phi : E → ℝ), hpsi.mul phi.contDiff,
    phi.hasCompactSupport.mul_left, tsupport_mul_subset_left.trans hts⟩
  have hPhi : (Phi : E → ℝ) = psi * (phi : E → ℝ) := TestFunction.coe_mk
  have hPsi : (Psi : E → ℝ) = psi * (phi : E → ℝ) := TestFunction.coe_mk
  have hres : W1p.restrictL le_top (W1p.ofTestFunctionₗ mu ⊤ p Phi) =
      W1p.ofTestFunctionₗ mu Omega p Psi := by
    refine W1p.ext_value (Lp.ext ?_)
    have hmono : ae (mu.restrict (Omega : Set E)) ≤ ae (mu.restrict ((⊤ : Opens E) : Set E)) :=
      ae_mono (Measure.restrict_mono (SetLike.coe_subset_coe.mpr le_top) le_rfl)
    filter_upwards [W1p.value_restrictL_ae (mu := mu) (p := p) (le_top : Omega ≤ ⊤) _,
      (testFunctionLp_apply_ae (mu := mu) p Phi).filter_mono hmono,
      testFunctionLp_apply_ae (mu := mu) p Psi] with x h1 h2 h3
    rw [h1, W1p.value_ofTestFunctionₗ, h2, W1p.value_ofTestFunctionₗ, h3, hPhi, hPsi]
  rw [W1p.contDiffSMulL_apply, W1p.contDiffSMul_ofTestFunctionₗ hpsi hM hpsiM hgradM phi Phi hPhi,
    hres]
  exact W1p.ofTestFunctionₗ_mem_w1p0Submodule Psi

/-- **A compactly supported Sobolev function lies in `W^{1,p}_0(Ω)`.**  If `u ∈ W^{1,p}(Ω)`
vanishes almost everywhere outside a compact `K ⊆ Ω`, then `u` is a `W^{1,p}`-limit of test
functions on `Ω`.

No regularity of `∂Ω` is assumed, and none is needed: the hypothesis keeps `u` away from the
boundary, so a cutoff can separate it from `∂Ω`. -/
theorem W1p.mem_w1p0Submodule_of_isCompact (hp : p ≠ (∞ : ℝ≥0∞)) {u : W1p mu Omega p}
    (hK : IsCompact K) (hKO : K ⊆ (Omega : Set E))
    (hu : ∀ᵐ x ∂mu.restrict (Omega : Set E), x ∉ K → W1p.value u x = 0) :
    u ∈ w1p0Submodule mu Omega p := by
  have hmeas : MeasurableSet (Omega : Set E) := Omega.isOpen.measurableSet
  have hsub : (Omega : Set E) ⊆ ((⊤ : Opens E) : Set E) := by simp
  have humu : ∀ᵐ x ∂mu, x ∈ (Omega : Set E) → x ∉ K → W1p.value u x = 0 :=
    (ae_restrict_iff' hmeas).1 hu
  -- the weak gradient vanishes off `K` as well, because `u` vanishes on the open set `Ω \ K`
  have hgrad : ∀ᵐ x ∂mu.restrict (Omega : Set E), x ∉ K → W1p.gradient u x = 0 := by
    set V : Opens E := ⟨(Omega : Set E) \ K, Omega.isOpen.sdiff hK.isClosed⟩
    have hVmeas : MeasurableSet (V : Set E) := V.isOpen.measurableSet
    have hvalV : ∀ᵐ x ∂mu.restrict (V : Set E), W1p.value u x = 0 := by
      rw [ae_restrict_iff' hVmeas]
      filter_upwards [humu] with x hx hxV
      exact hx hxV.1 hxV.2
    have hgradV := (ae_restrict_iff' hVmeas).1
      (W1p.gradient_ae_eq_zero_of_value_ae_eq_zero (V := V) Set.sdiff_subset hvalV)
    rw [ae_restrict_iff' hmeas]
    filter_upwards [hgradV] with x hx hxO hxK
    exact hx ⟨hxO, hxK⟩
  -- the zero-extension of `u` to the whole space is again a Sobolev function
  have hweak : HasWeakFDerivOn mu ⊤
      ((extendByZeroLpₗᵢ ℝ mu hmeas hsub (W1p.value u) : E → ℝ))
      (fun x => innerSL ℝ (extendByZeroLpₗᵢ ℝ mu hmeas hsub (W1p.gradient u) x)) := by
    have hU : ∀ᵐ x ∂mu.restrict (Omega : Set E), x ∉ K →
        innerSL ℝ (W1p.gradient u x) = 0 := by
      filter_upwards [hgrad] with x hx hxK
      rw [hx hxK, map_zero]
    refine (((W1p.hasWeakFDerivOn u).indicator_of_isCompact hK hKO hu hU).congr_ae
      (coeFn_extendByZeroLpₗᵢ ℝ hmeas hsub (W1p.value u)).symm).congr_ae_deriv ?_
    filter_upwards [coeFn_extendByZeroLpₗᵢ ℝ hmeas hsub (W1p.gradient u)] with x hx
    rw [hx]
    by_cases hxO : x ∈ (Omega : Set E) <;> simp [hxO]
  set w : W1p mu (⊤ : Opens E) p :=
    W1p.mk (extendByZeroLpₗᵢ ℝ mu hmeas hsub (W1p.value u))
      (extendByZeroLpₗᵢ ℝ mu hmeas hsub (W1p.gradient u)) hweak with hwdef
  have hvalw : ⇑(W1p.value w) =ᵐ[mu.restrict ((⊤ : Opens E) : Set E)]
      (Omega : Set E).indicator (W1p.value u : E → ℝ) := by
    rw [hwdef, W1p.value_mk]
    exact coeFn_extendByZeroLpₗᵢ ℝ hmeas hsub (W1p.value u)
  -- a smooth cutoff, equal to one on `K` and compactly supported inside `Ω`
  obtain ⟨chi, M, hchi, -, hchi_one_nhds, hchi_cpt, hchi_ts, hM0, hchiM_all,
    hchigradM_all⟩ := hK.exists_contDiff_cutoff_with_bounds Omega.isOpen hKO
  have hchi_one : ∀ x ∈ K, chi x = 1 := fun x hx => by
    have hx' : x ∈ chi ⁻¹' ({1} : Set ℝ) := interior_subset (hchi_one_nhds hx)
    exact hx'
  have hchiM : ∀ x ∈ ((⊤ : Opens E) : Set E), |chi x| ≤ M := fun x _ => hchiM_all x
  have hchigradM : ∀ x ∈ ((⊤ : Opens E) : Set E), ‖∇ chi x‖ ≤ M :=
    fun x _ => hchigradM_all x
  -- the cutoff leaves the extension unchanged
  have hLw : W1p.contDiffSMul chi hchi hM0 hchiM hchigradM w = w := by
    refine W1p.ext_value (Lp.ext ?_)
    filter_upwards [W1p.value_contDiffSMul_ae hchi hM0 hchiM hchigradM w, hvalw,
      humu.filter_mono (ae_mono Measure.restrict_le_self)] with x h1 h2 h3
    rw [h1]
    by_cases hxK : x ∈ K
    · rw [hchi_one x hxK]
      simp
    · have hzero : W1p.value w x = 0 := by
        rw [h2]
        by_cases hxO : x ∈ (Omega : Set E)
        · rw [indicator_of_mem hxO, h3 hxO hxK]
        · rw [indicator_of_notMem hxO]
      rw [hzero, smul_zero]
  -- so the extension is a cutoff product, whose restriction to `Ω` is `u`
  have hmem := W1p.restrictL_contDiffSMul_mem_w1p0Submodule hp hchi hM0 hchiM hchigradM hchi_ts w
  have hwu : W1p.restrictL le_top w = u := by
    refine W1p.ext_value (Lp.ext ?_)
    filter_upwards [W1p.value_restrictL_ae le_top w,
      hvalw.filter_mono (ae_mono (Measure.restrict_mono hsub le_rfl)), ae_restrict_mem hmeas]
      with x h1 h2 hx
    rw [h1, h2, indicator_of_mem hx]
  rwa [hLw, hwu] at hmem

/-! ### Multiplication by a compactly supported cutoff -/

/-- **Multiplying by a cutoff compactly supported in `Ω` lands in `W^{1,p}_0(Ω)`.**  Unlike
`TauCeti.W1p.contDiffSMul_mem_w1p0Submodule`, nothing is assumed about the boundary behaviour of
`u`: the support of `ψ` keeps the product away from `∂Ω`.  This is the localization device that
turns a statement about `W^{1,p}(Ω)` into one about the test-function closure. -/
theorem W1p.contDiffSMul_mem_w1p0Submodule_of_hasCompactSupport (hp : p ≠ (∞ : ℝ≥0∞))
    {psi : E → ℝ}
    (hpsi : ContDiff ℝ ∞ psi) {M : ℝ} (hM : 0 ≤ M) (hpsiM : ∀ x ∈ Omega, |psi x| ≤ M)
    (hgradM : ∀ x ∈ Omega, ‖∇ psi x‖ ≤ M) (hcpt : HasCompactSupport psi)
    (hts : tsupport psi ⊆ (Omega : Set E)) (u : W1p mu Omega p) :
    W1p.contDiffSMul psi hpsi hM hpsiM hgradM u ∈ w1p0Submodule mu Omega p := by
  refine W1p.mem_w1p0Submodule_of_isCompact hp hcpt hts ?_
  filter_upwards [W1p.value_contDiffSMul_ae hpsi hM hpsiM hgradM u] with x hx hxK
  rw [hx, image_eq_zero_of_notMem_tsupport hxK, zero_smul]

/-! ### Localisation to the whole space -/

/-- **The value of an extended cutoff product.** For `ψ` smooth and `u ∈ W^{1,p}(Ω)` with
`ψ u ∈ W^{1,p}_0(Ω)`, the extension of `ψ u` by zero to the whole space is `ψ u` on `Ω` and
vanishes off `Ω`. -/
theorem W1p.value_extendByZeroL_contDiffSMul_ae {psi : E → ℝ} (hpsi : ContDiff ℝ ∞ psi) {M : ℝ}
    (hM : 0 ≤ M) (hpsiM : ∀ x ∈ Omega, |psi x| ≤ M) (hgradM : ∀ x ∈ Omega, ‖∇ psi x‖ ≤ M)
    (u : W1p mu Omega p)
    (hw : W1p.contDiffSMul psi hpsi hM hpsiM hgradM u ∈ w1p0Submodule mu Omega p) :
    ∀ᵐ x ∂mu, W1p.value (W1p0.extendByZeroL le_top ⟨_, hw⟩ : W1p mu ⊤ p) x =
      (Omega : Set E).indicator (fun y => psi y * W1p.value u y) x := by
  have hOmega := Omega.isOpen.measurableSet
  have h2 := (coeFn_extendByZeroLpₗᵢ ℝ (μ := mu) hOmega
    (SetLike.coe_subset_coe.mpr (le_top : Omega ≤ ⊤))
    (W1p.value (W1p.contDiffSMul psi hpsi hM hpsiM hgradM u))).filter_mono
      (ae_mono (by rw [Opens.coe_top, Measure.restrict_univ]))
  have h3 := (ae_restrict_iff' hOmega).1 (W1p.value_contDiffSMul_ae hpsi hM hpsiM hgradM u)
  filter_upwards [h2, h3] with x hx2 hx3
  rw [W1p0.value_extendByZeroL, hx2]
  by_cases hxO : x ∈ (Omega : Set E)
  · rw [indicator_of_mem hxO, indicator_of_mem hxO, hx3 hxO, smul_eq_mul]
  · rw [indicator_of_notMem hxO, indicator_of_notMem hxO]

/-- **The Leibniz rule for an extended cutoff product.** For `ψ` smooth and `u ∈ W^{1,p}(Ω)`
with `ψ u ∈ W^{1,p}_0(Ω)`, the extension of `ψ u` by zero to the whole space has weak gradient
`ψ ∇u + u ∇ψ` on `Ω` and `0` off `Ω`. -/
theorem W1p.gradient_extendByZeroL_contDiffSMul_ae {psi : E → ℝ} (hpsi : ContDiff ℝ ∞ psi)
    {M : ℝ} (hM : 0 ≤ M) (hpsiM : ∀ x ∈ Omega, |psi x| ≤ M)
    (hgradM : ∀ x ∈ Omega, ‖∇ psi x‖ ≤ M) (u : W1p mu Omega p)
    (hw : W1p.contDiffSMul psi hpsi hM hpsiM hgradM u ∈ w1p0Submodule mu Omega p) :
    ∀ᵐ x ∂mu, W1p.gradient (W1p0.extendByZeroL le_top ⟨_, hw⟩ : W1p mu ⊤ p) x =
      (Omega : Set E).indicator
        (fun y => psi y • W1p.gradient u y + W1p.value u y • ∇ psi y) x := by
  have hOmega := Omega.isOpen.measurableSet
  have h2 := (coeFn_extendByZeroLpₗᵢ ℝ (μ := mu) hOmega
    (SetLike.coe_subset_coe.mpr (le_top : Omega ≤ ⊤))
    (W1p.gradient (W1p.contDiffSMul psi hpsi hM hpsiM hgradM u))).filter_mono
      (ae_mono (by rw [Opens.coe_top, Measure.restrict_univ]))
  have h3 := (ae_restrict_iff' hOmega).1 (W1p.gradient_contDiffSMul_ae hpsi hM hpsiM hgradM u)
  filter_upwards [h2, h3] with x hx2 hx3
  rw [W1p0.gradient_extendByZeroL, hx2]
  by_cases hxO : x ∈ (Omega : Set E)
  · rw [indicator_of_mem hxO, indicator_of_mem hxO, hx3 hxO]
  · rw [indicator_of_notMem hxO, indicator_of_notMem hxO]

/-- **Localisation to the whole space.** For `1 ≤ p < ∞`, a Sobolev function `u ∈ W^{1,p}(Ω)`
agrees, in value and in gradient, almost everywhere on any compact `S ⊆ Ω` with some
`w ∈ W^{1,p}(ℝⁿ)`. One may take for `w` the product of `u` with a smooth cutoff equal to one near
`S` and compactly supported in `Ω`, extended by zero. -/
theorem W1p.exists_top_value_gradient_ae_eq_on_of_isCompact (hp : p ≠ (∞ : ENNReal))
    (u : W1p mu Omega p) {S : Set E}
    (hS : IsCompact S) (hSO : S ⊆ Omega) :
    ∃ w : W1p mu ⊤ p, (∀ᵐ x ∂mu, x ∈ S → W1p.value w x = W1p.value u x) ∧
      ∀ᵐ x ∂mu, x ∈ S → W1p.gradient w x = W1p.gradient u x := by
  -- A smooth cutoff, equal to one near `S` and compactly supported in `Ω`.
  obtain ⟨chi, M, hchi, -, hchi_one, hchi_cpt, hchi_ts, hM0, hchiM_all, hchigradM_all⟩ :=
    hS.exists_contDiff_cutoff_with_bounds Omega.isOpen hSO
  have hchiM : ∀ x ∈ (Omega : Set E), |chi x| ≤ M := fun x _ => hchiM_all x
  have hchigradM : ∀ x ∈ (Omega : Set E), ‖∇ chi x‖ ≤ M := fun x _ => hchigradM_all x
  -- Near `S` the cutoff is one and its gradient vanishes.
  have hchi_S : ∀ x ∈ S, chi x = 1 ∧ ∇ chi x = 0 := fun x hx => by
    have hev : chi =ᶠ[𝓝 x] fun _ => (1 : ℝ) :=
      Filter.mem_of_superset (mem_interior_iff_mem_nhds.1 (hchi_one hx)) fun y hy => hy
    refine ⟨hev.eq_of_nhds, ?_⟩
    rw [_root_.gradient, hev.fderiv_eq, fderiv_const_apply, map_zero]
  -- The cutoff product lies in `W^{1,p}_0(Ω)`, so it extends by zero to the whole space.
  have hw0 := W1p.contDiffSMul_mem_w1p0Submodule_of_hasCompactSupport hp hchi hM0 hchiM
    hchigradM hchi_cpt hchi_ts u
  refine ⟨(W1p0.extendByZeroL (p := p) (Omega := Omega) le_top ⟨_, hw0⟩).1, ?_, ?_⟩
  · filter_upwards [W1p.value_extendByZeroL_contDiffSMul_ae hchi hM0 hchiM hchigradM u hw0]
      with x hx hxS
    rw [hx, indicator_of_mem (hSO hxS), (hchi_S x hxS).1, one_mul]
  · filter_upwards [W1p.gradient_extendByZeroL_contDiffSMul_ae hchi hM0 hchiM hchigradM u hw0]
      with x hx hxS
    rw [hx, indicator_of_mem (hSO hxS), (hchi_S x hxS).1, (hchi_S x hxS).2, one_smul,
      smul_zero, add_zero]

end TauCeti
