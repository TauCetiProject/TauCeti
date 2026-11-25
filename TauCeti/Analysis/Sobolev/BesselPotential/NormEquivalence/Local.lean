/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.BesselPotential.Local
public import TauCeti.Analysis.Sobolev.Wkp.Basic
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import TauCeti.Analysis.Distribution.ComplexPairing
import TauCeti.Analysis.Distribution.TestFunction.PartitionOfUnity
import TauCeti.Analysis.Sobolev.BesselPotential.NormEquivalence.Basic
import TauCeti.Analysis.Sobolev.Wkp.Extension
import TauCeti.Analysis.Sobolev.Wkp.Gluing
import TauCeti.Analysis.Sobolev.Wkp.Leibniz
import TauCeti.MeasureTheory.Function.LocallyIntegrable

/-!
# Local `W^{k,p}` regularity is local `H^{k,p}` regularity

Let `f` be a real function, locally integrable on an open subset `Ω` of a finite-dimensional real
inner product space `E`, and let `1 < p < ∞` and `k` be a natural number. The distribution of `f`
is `H^{k,p}` near a point `x` (`Distribution.IsLocallyMemSobolevAt`) exactly when `f` agrees, on
some open neighbourhood `U ⊆ Ω` of `x`, with the value of an element of the weak-derivative Sobolev
space `W^{k,p}(U)` (`Distribution.isLocallyMemSobolevAt_ofFun_iff_exists_wkp`). This is the local
form of Calderón's theorem `MeasureTheory.Lp.memSobolev_natCast_iff_exists_wkp_value_eq`, which
compares the two scales on the whole space.

Over a compact set `K ⊆ Ω` the local pieces glue: the distribution of `f` is `H^{k,p}` near every
point of `K` exactly when `f` agrees with an element of `W^{k,p}(U)` on a single open
neighbourhood `U ⊆ Ω` of `K` (`Distribution.forall_isLocallyMemSobolevAt_ofFun_iff_exists_wkp`).
For `p = 2` the same holds for the Fourier description `Distribution.IsLocallySobolevAt` of being
`H^k` near a point (`Distribution.isLocallySobolevAt_ofFun_iff_exists_wkp`,
`Distribution.forall_isLocallySobolevAt_ofFun_iff_exists_wkp`).

These are the chart-level statements through which Sobolev sections of a vector bundle, defined by
weak derivatives of their chart readings, are compared with the Bessel-potential Sobolev spaces
of distributions on the bundle tests, whose localizations are cut-off distributions on the chart
images.

## The argument

For a test function `φ`, the cut-off distribution `φ T` of the distribution `T` of `f` is the
tempered distribution of the function `φ f` (`Distribution.cutoffTempered_ofFun_eq`), and
conversely an `Lᵖ` function with that tempered distribution is `φ f` almost everywhere
(`Distribution.ae_eq_of_cutoffTempered_ofFun_eq`).

* If `T` is `H^{k,p}` near `x`, take a real cutoff `χ` equal to one on an open neighbourhood `V`
  of `x`. Then `χ T` lies in `H^{k,p} ⊆ Lᵖ`, so it is the tempered distribution of the `Lᵖ`
  function `χ f`, and Calderón's theorem gives an element of `W^{k,p}(E)` with value `χ f`. Its
  restriction to `V` has value `f`.
* If `f` is the value of `w ∈ W^{k,p}(U)`, then for a real test function `χ` supported in `U` the
  product `χ w` extended by zero lies in `W^{k,p}(E)`, so `χ f` lies in `H^{k,p}`. A complex test
  function is split into its real and imaginary parts.
-/

public section

noncomputable section

open MeasureTheory Filter Set TopologicalSpace Complex TestFunction
open scoped ENNReal Topology ContDiff Distributions SchwartzMap

namespace Distribution

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {Ω : Opens E}

section Cutoff

variable {f : E → ℂ}

/-- The cut-off `φ T` of the distribution `T` of a locally integrable function `f`, evaluated on a
Schwartz function `ψ`, is the integral of `ψ φ f`. -/
theorem cutoffTempered_ofFun_apply (hf : LocallyIntegrableOn f Ω) (φ : 𝓓(Ω, ℂ)) (ψ : 𝓢(E, ℂ)) :
    (ofFun Ω f volume ⊤).cutoffTempered φ ψ = ∫ x, ψ x * (φ x * f x) := by
  rw [cutoffTempered_def, complexPairing_ofFun hf]
  congr 1
  ext x
  simp only [bilinLeftCLM_apply, ContinuousLinearMap.mul_apply']
  ring

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The cut-off `φ T` of the distribution `T` of a locally integrable function `f` is the tempered
distribution of any `Lᵖ` function agreeing almost everywhere with `φ f`. -/
theorem cutoffTempered_ofFun_eq (hf : LocallyIntegrableOn f Ω) (φ : 𝓓(Ω, ℂ))
    {g : Lp ℂ p (volume : Measure E)} (hg : g =ᵐ[volume] fun x ↦ φ x * f x) :
    (ofFun Ω f volume ⊤).cutoffTempered φ = (g : 𝓢'(E, ℂ)) := by
  ext ψ
  rw [cutoffTempered_ofFun_apply hf, Lp.toTemperedDistribution_apply]
  refine integral_congr_ae ?_
  filter_upwards [hg] with x hx
  rw [hx, smul_eq_mul]

/-- An `Lᵖ` function whose tempered distribution is the cut-off `φ T` of the distribution `T` of a
locally integrable function `f` agrees almost everywhere with `φ f`. -/
theorem ae_eq_of_cutoffTempered_ofFun_eq (hf : LocallyIntegrableOn f Ω) (φ : 𝓓(Ω, ℂ))
    {g : Lp ℂ p (volume : Measure E)}
    (hg : (ofFun Ω f volume ⊤).cutoffTempered φ = (g : 𝓢'(E, ℂ))) :
    g =ᵐ[volume] fun x ↦ φ x * f x := by
  have hφf : Integrable (fun x ↦ φ x * f x) volume :=
    hf.integrable_smul_left_of_hasCompactSupport φ.continuous.continuousOn φ.hasCompactSupport
      φ.tsupport_subset
  refine ae_eq_of_integral_contDiff_smul_eq ((Lp.memLp g).locallyIntegrable Fact.out)
    hφf.locallyIntegrable fun χ hχ hχc ↦ ?_
  -- Test both sides against the complexification of `χ`, a Schwartz function.
  have hχ' : ContDiff ℝ ∞ fun x ↦ (χ x : ℂ) := ofRealCLM.contDiff.comp hχ
  have h := congrArg (fun T : 𝓢'(E, ℂ) ↦ T ((hχc.comp_left ofReal_zero).toSchwartzMap hχ')) hg
  simp only [cutoffTempered_ofFun_apply hf, Lp.toTemperedDistribution_apply,
    HasCompactSupport.toSchwartzMap_toFun] at h
  simp only [real_smul]
  exact h.symm

end Cutoff

variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {f : E → ℝ}

/-- If `f` agrees on `U` with an element of `W^{k,p}(U)` and `χ` is a real test function supported
in `U`, then `χ f` is an `Lᵖ` function in `H^{k,p}(E)`. -/
private theorem exists_memSobolev_mul_of_wkp (hp : 1 < p) (hp_top : p ≠ ⊤) {k : ℕ} {U : Opens E}
    {w : TauCeti.Wkp (volume : Measure E) U p k}
    (hw : (TauCeti.Wkp.value k w : E → ℝ) =ᵐ[volume.restrict U] f) {χ : E → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ) (hχU : tsupport χ ⊆ U) :
    ∃ g : Lp ℂ p (volume : Measure E), (g =ᵐ[volume] fun x ↦ (χ x : ℂ) * f x) ∧
      TemperedDistribution.MemSobolev k p (g : 𝓢'(E, ℂ)) := by
  obtain ⟨w₁, hw₁⟩ := TauCeti.Wkp.exists_value_ae_eq_mul_of_hasCompactSupport k hχ hχc w
  -- `χ w` vanishes off the support of `χ`, so it extends by zero to the whole space.
  obtain ⟨w₂, hw₂⟩ := TauCeti.Wkp.exists_value_ae_eq_indicator_of_isClosed (V := ⊤)
    (isClosed_tsupport χ) (fun x hx ↦ hχU hx.2) k w₁ (by
      filter_upwards [hw₁] with x hx hxK
      rw [hx, image_eq_zero_of_notMem_tsupport hxK, zero_mul])
  obtain ⟨g, hg, hgS⟩ := TauCeti.Wkp.exists_memSobolev_value_smul hp hp_top k w₂ (1 : ℂ)
  refine ⟨g, ?_, hgS⟩
  replace hw₂ := hw₂.filter_mono (by rw [Measure.restrict_coe_opens_top])
  have hU : MeasurableSet (U : Set E) := U.isOpen.measurableSet
  filter_upwards [hg, hw₂, (ae_restrict_iff' hU).1 hw₁, (ae_restrict_iff' hU).1 hw]
    with x h₁ h₂ h₃ h₄
  rw [h₁, h₂]
  by_cases hx : x ∈ (U : Set E)
  · simp [indicator_of_mem hx, h₃ hx, h₄ hx]
  · simp [indicator_of_notMem hx, image_eq_zero_of_notMem_tsupport fun h ↦ hx (hχU h)]

/-- **Local `W^{k,p}` regularity is local `H^{k,p}` regularity.** Let `1 < p < ∞` and let `f` be a
real function locally integrable on `Ω`. The distribution of `f` is `H^{k,p}` near `x` exactly
when `f` agrees, on some open neighbourhood `U ⊆ Ω` of `x`, with the value of an element of
`W^{k,p}(U)`. -/
theorem isLocallyMemSobolevAt_ofFun_iff_exists_wkp (hp : 1 < p) (hp_top : p ≠ ⊤) (k : ℕ)
    (hf : LocallyIntegrableOn f Ω) {x : E} :
    (ofFun Ω (fun y ↦ (f y : ℂ)) volume ⊤).IsLocallyMemSobolevAt k p x ↔
      ∃ U : Opens E, x ∈ U ∧ (U : Set E) ⊆ Ω ∧ ∃ w : TauCeti.Wkp (volume : Measure E) U p k,
        (TauCeti.Wkp.value k w : E → ℝ) =ᵐ[volume.restrict U] f := by
  have hf' : LocallyIntegrableOn (fun y ↦ (f y : ℂ)) Ω := fun y hy ↦
    let ⟨t, ht, hi⟩ := hf y hy
    ⟨t, ht, hi.ofReal⟩
  constructor
  · intro h
    obtain ⟨U, hU, hUΩ, hT⟩ := isLocallyMemSobolevAt_iff.1 h
    obtain ⟨χ, V, hVo, hxV, hχ1, hχU⟩ :=
      exists_eqOn_one_tsupport_subset (𝕜 := ℝ) (n := ⊤) hU (hUΩ (mem_of_mem_nhds hU))
    set χc : 𝓓(Ω, ℂ) := postcompCLM (𝕜 := ℝ) ofRealCLM χ
    have hS := hT χc ((tsupport_comp_subset (g := ofRealCLM) (by simp) χ).trans hχU)
    -- `χ T` lies in `H^{k,p} ⊆ Lᵖ`, so it is the tempered distribution of `χ f`.
    obtain ⟨g, hg⟩ := TemperedDistribution.memSobolev_zero_iff.1
      (hS.mono_of_one_lt hp hp_top (Nat.cast_nonneg k))
    have hgf := ae_eq_of_cutoffTempered_ofFun_eq hf' χc hg
    obtain ⟨w₀, hw₀⟩ := (hg ▸ hS).exists_wkp_value_ae_eq_comp hp hp_top reCLM
    have hVU : V ⊆ U := fun y hy ↦ hχU (subset_tsupport _ (by simp [hχ1 hy]))
    let V' : Opens E := ⟨V, hVo⟩
    refine ⟨V', hxV, hVU.trans hUΩ, TauCeti.Wkp.restrictL (le_top : V' ≤ ⊤) k w₀, ?_⟩
    filter_upwards [TauCeti.Wkp.value_restrictL_ae (le_top : V' ≤ ⊤) k w₀,
      ae_restrict_of_ae hw₀, ae_restrict_of_ae hgf,
      ae_restrict_mem V'.isOpen.measurableSet] with y h₁ h₂ h₃ hyV
    rw [h₁, h₂, h₃]
    simp [χc, hχ1 hyV]
  · rintro ⟨U, hxU, hUΩ, w, hw⟩
    refine isLocallyMemSobolevAt_iff.2 ⟨U, U.isOpen.mem_nhds hxU, hUΩ, fun φ hφ ↦ ?_⟩
    -- Split `φ` into its real and imaginary parts, real test functions supported in `U`.
    set φr : 𝓓(Ω, ℝ) := postcompCLM (𝕜 := ℝ) reCLM φ
    set φi : 𝓓(Ω, ℝ) := postcompCLM (𝕜 := ℝ) imCLM φ
    have hsupp (L : ℂ →L[ℝ] ℝ) : tsupport (postcompCLM (𝕜 := ℝ) L φ) ⊆ U :=
      (tsupport_comp_subset (map_zero L) φ).trans hφ
    have hpart (ψ : 𝓓(Ω, ℝ)) (hψ : tsupport ψ ⊆ U) :
        TemperedDistribution.MemSobolev k p
          ((ofFun Ω (fun y ↦ (f y : ℂ)) volume ⊤).cutoffTempered
            (postcompCLM (𝕜 := ℝ) ofRealCLM ψ)) := by
      obtain ⟨g, hg, hgS⟩ :=
        exists_memSobolev_mul_of_wkp hp hp_top hw ψ.contDiff ψ.hasCompactSupport hψ
      rwa [cutoffTempered_ofFun_eq hf' _ hg]
    have hφ' : φ = postcompCLM (𝕜 := ℝ) ofRealCLM φr + I • postcompCLM (𝕜 := ℝ) ofRealCLM φi := by
      ext y
      change φ y = (postcompCLM (𝕜 := ℝ) ofRealCLM φr) y + I • (postcompCLM (𝕜 := ℝ) ofRealCLM φi) y
      simp only [φr, φi, postcompCLM_apply, Function.comp_apply, ofRealCLM_apply, reCLM_apply,
        imCLM_apply, smul_eq_mul]
      rw [mul_comm]
      exact (re_add_im (φ y)).symm
    rw [hφ', cutoffTempered_add_cutoff, cutoffTempered_smul_cutoff]
    exact (hpart φr (hsupp reCLM)).add ((hpart φi (hsupp imCLM)).smul I)

/-- **Local `W^{k,p}` regularity over a compact set.** Let `1 < p < ∞`, let `f` be a real function
locally integrable on `Ω`, and let `K ⊆ Ω` be compact. The distribution of `f` is `H^{k,p}` near
every point of `K` exactly when `f` agrees, on some open neighbourhood `U ⊆ Ω` of `K`, with the
value of an element of `W^{k,p}(U)`. -/
theorem forall_isLocallyMemSobolevAt_ofFun_iff_exists_wkp (hp : 1 < p) (hp_top : p ≠ ⊤) (k : ℕ)
    (hf : LocallyIntegrableOn f Ω) {K : Set E} (hK : IsCompact K) :
    (∀ x ∈ K, (ofFun Ω (fun y ↦ (f y : ℂ)) volume ⊤).IsLocallyMemSobolevAt k p x) ↔
      ∃ U : Opens E, K ⊆ U ∧ (U : Set E) ⊆ Ω ∧ ∃ w : TauCeti.Wkp (volume : Measure E) U p k,
        (TauCeti.Wkp.value k w : E → ℝ) =ᵐ[volume.restrict U] f := by
  constructor
  · intro h
    choose! V hxV hVΩ w hw using fun x hx ↦
      (isLocallyMemSobolevAt_ofFun_iff_exists_wkp hp hp_top k hf).1 (h x hx)
    obtain ⟨t, hKt⟩ := hK.elim_nhds_subcover' (fun x _ ↦ (V x : Set E))
      fun x hx ↦ (V x).isOpen.mem_nhds (hxV x hx)
    -- Glue the local pieces, which agree on overlaps since they all have value `f`.
    let c : { x // x ∈ t } → E := fun i ↦ i.val.val
    have hc (i : { x // x ∈ t }) : c i ∈ K := i.val.property
    let W := fun i ↦ V (c i)
    let U : Opens E := ⨆ i, W i
    obtain ⟨v, hv, -⟩ := TauCeti.Wkp.exists_glue_of_restrictL_eq (Omega := U)
      (fun i ↦ le_iSup W i) le_rfl k (fun i ↦ w (c i)) fun i j ↦ by
        refine TauCeti.Wkp.ext k (Lp.ext ?_)
        filter_upwards [TauCeti.Wkp.value_restrictL_ae (inf_le_left : W i ⊓ W j ≤ W i) k (w (c i)),
          TauCeti.Wkp.value_restrictL_ae (inf_le_right : W i ⊓ W j ≤ W j) k (w (c j)),
          ae_restrict_of_ae_restrict_of_subset inter_subset_left (hw _ (hc i)),
          ae_restrict_of_ae_restrict_of_subset inter_subset_right (hw _ (hc j))]
          with y h₁ h₂ h₃ h₄
        rw [h₁, h₂, h₃, h₄]
    refine ⟨U, fun x hx ↦ ?_, (iSup_le fun i ↦ hVΩ _ (hc i) : U ≤ Ω), v, ?_⟩
    · obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.1 (hKt hx)
      exact Opens.mem_iSup.2 ⟨⟨y, hy⟩, hxy⟩
    · refine Filter.Eventually.filter_mono (by rw [Opens.coe_iSup])
        ((ae_restrict_iUnion_iff _ _).2 fun i ↦ ?_)
      filter_upwards [(TauCeti.Wkp.value_restrictL_ae (le_iSup W i) k v).symm, hw _ (hc i)]
        with y h₁ h₂
      rw [h₁, hv i, h₂]
  · rintro ⟨U, hKU, hUΩ, w, hw⟩ x hx
    exact (isLocallyMemSobolevAt_ofFun_iff_exists_wkp hp hp_top k hf).2
      ⟨U, hKU hx, hUΩ, w, hw⟩

/-- **Local `W^{k,2}` regularity is local `H^k` regularity.** A real function `f` locally
integrable on `Ω` has a distribution that is `H^k` near `x`, in the Fourier sense of
`Distribution.IsLocallySobolevAt`, exactly when `f` agrees, on some open neighbourhood `U ⊆ Ω` of
`x`, with the value of an element of `W^{k,2}(U)`. -/
theorem isLocallySobolevAt_ofFun_iff_exists_wkp (k : ℕ) (hf : LocallyIntegrableOn f Ω) {x : E} :
    (ofFun Ω (fun y ↦ (f y : ℂ)) volume ⊤).IsLocallySobolevAt k x ↔
      ∃ U : Opens E, x ∈ U ∧ (U : Set E) ⊆ Ω ∧ ∃ w : TauCeti.Wkp (volume : Measure E) U 2 k,
        (TauCeti.Wkp.value k w : E → ℝ) =ᵐ[volume.restrict U] f := by
  rw [← isLocallyMemSobolevAt_two_iff]
  exact isLocallyMemSobolevAt_ofFun_iff_exists_wkp ENNReal.one_lt_two ENNReal.ofNat_ne_top k hf

/-- **Local `W^{k,2}` regularity over a compact set.** A real function `f` locally integrable on
`Ω` has a distribution that is `H^k` near every point of a compact `K ⊆ Ω` exactly when `f`
agrees, on some open neighbourhood `U ⊆ Ω` of `K`, with the value of an element of
`W^{k,2}(U)`. -/
theorem forall_isLocallySobolevAt_ofFun_iff_exists_wkp (k : ℕ) (hf : LocallyIntegrableOn f Ω)
    {K : Set E} (hK : IsCompact K) :
    (∀ x ∈ K, (ofFun Ω (fun y ↦ (f y : ℂ)) volume ⊤).IsLocallySobolevAt k x) ↔
      ∃ U : Opens E, K ⊆ U ∧ (U : Set E) ⊆ Ω ∧ ∃ w : TauCeti.Wkp (volume : Measure E) U 2 k,
        (TauCeti.Wkp.value k w : E → ℝ) =ᵐ[volume.restrict U] f := by
  simp_rw [← isLocallyMemSobolevAt_two_iff]
  exact forall_isLocallyMemSobolevAt_ofFun_iff_exists_wkp ENNReal.one_lt_two
    ENNReal.ofNat_ne_top k hf hK

end Distribution
