/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.CompactSupport
public import TauCeti.Analysis.Sobolev.W1p.Density
public import TauCeti.Analysis.Sobolev.W1p.Extension

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
`u` unchanged, while carrying every test function on `ℝⁿ` into the image of `C_c^∞(Ω)`.  Since
that image is closed — extension by zero is an isometry of `W^{1,p}_0(Ω)` onto its image — the
limit stays in it, and restricting the isometry back gives `u` itself.

## Consequences

`TauCeti.W1p.contDiffSMul_mem_w1p0Submodule_of_hasCompactSupport` is the form localization
arguments use: multiplying *any* `u ∈ W^{1,p}(Ω)` by a smooth cutoff compactly supported in `Ω`
produces an element of `W^{1,p}_0(Ω)`.  The companion
`TauCeti.W1p.contDiffSMul_mem_w1p0Submodule` needs `u` to lie in `W^{1,p}_0(Ω)` already, which is
exactly what the compact support replaces here.  This is the localization step of Meyers--Serrin
density and of interior estimates.

## Main declarations

* `TauCeti.W1p.mem_w1p0Submodule_of_isCompact`: a compactly supported Sobolev function has zero
  boundary values.
* `TauCeti.W1p.contDiffSMul_mem_w1p0Submodule_of_hasCompactSupport`: multiplication by a
  compactly supported cutoff lands in `W^{1,p}_0(Ω)`.

## References

L. C. Evans, *Partial Differential Equations*, §5.3.3; H. Brezis, *Functional Analysis,
Sobolev Spaces and Partial Differential Equations*, Lemma 9.5.
-/

public section

noncomputable section

open MeasureTheory Set TopologicalSpace

open scoped ContDiff Distributions ENNReal Gradient InnerProductSpace

namespace TauCeti

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure]
  {Omega : Opens E} {p : ENNReal} [Fact (1 ≤ p)] {K : Set E}

/-! ### Zero boundary values -/

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
  obtain ⟨chi, hchi, hchi_range, hchi_one_nhds, hchi_cpt, hchi_ts⟩ :=
    hK.exists_contDiff_cutoff Omega.isOpen hKO
  have hchi_mem : ∀ x, chi x ∈ Icc (0 : ℝ) 1 := fun x => hchi_range (mem_range_self x)
  have hchi_one : ∀ x ∈ K, chi x = 1 := fun x hx => by
    have hx' : x ∈ chi ⁻¹' ({1} : Set ℝ) := interior_subset (hchi_one_nhds hx)
    exact hx'
  obtain ⟨C, hC⟩ := (hchi.continuous_fderiv (by simp)).norm.bddAbove_range_of_hasCompactSupport
    ((hchi_cpt.fderiv ℝ).norm)
  set M : ℝ := max 1 C
  have hM0 : (0 : ℝ) ≤ M := le_trans zero_le_one (le_max_left _ _)
  have hchiM : ∀ x ∈ ((⊤ : Opens E) : Set E), |chi x| ≤ M := fun x _ => by
    rw [abs_of_nonneg (hchi_mem x).1]
    exact le_trans (hchi_mem x).2 (le_max_left _ _)
  have hchigradM : ∀ x ∈ ((⊤ : Opens E) : Set E), ‖∇ chi x‖ ≤ M := fun x _ => by
    rw [_root_.gradient, LinearIsometryEquiv.norm_map]
    exact le_trans (hC ⟨x, rfl⟩) (le_max_right _ _)
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
  -- the image of `W^{1,p}_0(Ω)` under extension by zero is closed
  have hcomplete : CompleteSpace (W1p0 mu Omega p) :=
    (w1p0Submodule mu Omega p).isClosed.completeSpace_coe
  set F : W1p0 mu Omega p →L[ℝ] W1p mu (⊤ : Opens E) p :=
    (w1p0Submodule mu (⊤ : Opens E) p).toSubmodule.subtypeL.comp
      (W1p0.extendByZeroL (le_top : Omega ≤ ⊤)) with hFdef
  have hFiso : Isometry F :=
    AddMonoidHomClass.isometry_of_norm F fun z => W1p0.norm_extendByZeroL le_top z
  have hclosed : IsClosed (Set.range F) := hFiso.isClosedEmbedding.isClosed_range
  -- every test function on `ℝⁿ`, cut off, comes from a test function on `Ω`
  have htest : ∀ phi : 𝓓((⊤ : Opens E), ℝ),
      W1p.ofTestFunctionₗ mu (⊤ : Opens E) p phi ∈
        W1p.contDiffSMulL chi hchi hM0 hchiM hchigradM ⁻¹' Set.range F := by
    intro phi
    obtain ⟨Psi, hPsi⟩ : ∃ Psi : 𝓓(Omega, ℝ), (Psi : E → ℝ) = chi * (phi : E → ℝ) :=
      ⟨⟨chi * (phi : E → ℝ), hchi.mul phi.contDiff, hchi_cpt.mul_right,
        tsupport_mul_subset_left.trans hchi_ts⟩, rfl⟩
    have hcoe : ((TestFunction.monoCLM ℝ Psi : 𝓓((⊤ : Opens E), ℝ)) : E → ℝ)
        = chi * (phi : E → ℝ) := by
      rw [TestFunction.monoCLM_apply, ← hPsi]
      simp
    refine ⟨⟨W1p.ofTestFunctionₗ mu Omega p Psi, W1p.ofTestFunctionₗ_mem_w1p0Submodule Psi⟩, ?_⟩
    rw [W1p.contDiffSMulL_apply,
      W1p.contDiffSMul_ofTestFunctionₗ hchi hM0 hchiM hchigradM phi
        (TestFunction.monoCLM ℝ Psi) hcoe]
    refine Subtype.ext ?_
    rw [hFdef]
    simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtypeL,
      Submodule.coe_subtype]
    rw [W1p0.coe_extendByZeroL]
    exact Sobolev1JetLp.extendByZeroₗᵢ_ofTestFunctionₗ le_top Psi
  -- the extension is therefore the zero-extension of a function in `W^{1,p}_0(Ω)`
  have hwmem : w ∈ Set.range F := by
    have hmem := w1p0Submodule_subset_of_isClosed
      (hclosed.preimage (W1p.contDiffSMulL chi hchi hM0 hchiM hchigradM).continuous) htest
      (W1p.mem_w1p0Submodule_top hp w)
    rw [Set.mem_preimage, W1p.contDiffSMulL_apply, hLw] at hmem
    exact hmem
  obtain ⟨z, hz⟩ := hwmem
  have hvalz : W1p.value (z : W1p mu Omega p) = W1p.value u := by
    have h1 : W1p.value (F z) =
        extendByZeroLpₗᵢ ℝ mu hmeas hsub (W1p.value (z : W1p mu Omega p)) :=
      W1p0.value_extendByZeroL le_top z
    rw [hz, hwdef, W1p.value_mk] at h1
    exact (extendByZeroLpₗᵢ ℝ mu hmeas hsub).injective h1.symm
  exact W1p.ext_value hvalz ▸ z.2

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

end TauCeti
