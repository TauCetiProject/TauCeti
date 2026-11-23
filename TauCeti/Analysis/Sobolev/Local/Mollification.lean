/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.TestFunction.Inner
public import TauCeti.Analysis.Distribution.TestFunction.LineDeriv
public import TauCeti.Analysis.Sobolev.Local.Basic
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import TauCeti.Analysis.Calculus.BumpFunction.Convolution
import TauCeti.Analysis.Sobolev.Local.Morrey.Higher
import TauCeti.Analysis.Sobolev.Local.SobolevEmbedding
import TauCeti.Analysis.Sobolev.Mollification.Basic
import TauCeti.Analysis.Sobolev.WeakDeriv.Symmetry
import TauCeti.MeasureTheory.Function.Lp.ApproximateIdentity

/-!
# Local mollification pairings and rough-coefficient commutators on planar domains

Let `Ω ⊆ ℂ` be open. Given a locally bounded map `f ∈ L^∞_loc(Ω; F)` with weak Fréchet derivative
`Df ∈ Lᵖ_loc(Ω; ℂ →L[ℝ] F)` (`1 ≤ p ≤ ∞`) and a compact subset `K ⊆ Ω`, convolving a cutoff of `f`
with a shrinking sequence of normalized smooth bumps produces `C^∞` maps `fn n : ℂ → F` whose
pairings and directional-derivative pairings through any continuous bilinear map
`B : F →L[ℝ] G →L[ℝ] H` against test-function-weighted fields supported in `K` converge to those
of `f` and `Df` (`TauCeti.exists_contDiff_tendsto_integral_smul_bilin_of_hasWeakFDerivOn`).

On a finite-dimensional real inner product space `V`, specializing to an operator field
`J ∈ W^{1,p}_loc(Ω; V →L[ℝ] V)` with `2 < p ≤ ∞` (so `J ∈ L^∞_loc(Ω)` by Morrey's embedding) yields:

* `TauCeti.exists_testFunction_tendsto_integral_inner_of_hasWeakFDerivOn`: for `1/p + 1/q ≤ 1`,
  `α ∈ 𝓓(Ω, ℝ)` and `v : V`, smooth vector test functions `Ψ n = α • (J_n)* v ∈ 𝓓(Ω, V)` whose
  directional-derivative pairings against `w ∈ L^q_loc(Ω)` and value pairings against locally
  integrable `w` converge to the corresponding pairings of `J` and `DJ`.
* `TauCeti.integral_inner_fderiv_add_integral_inner_eq_of_hasWeakFDerivOn`: the mixed-derivative
  commutator identity
  `∫ ⟪∂_u φ, J (∂_v ξ)⟫ + ∫ ⟪φ, (∂_u J) (∂_v ξ)⟫ = ∫ ⟪∂_v φ, J (∂_u ξ)⟫ + ∫ ⟪φ, (∂_v J) (∂_u ξ)⟫`
  for `J ∈ W^{1,p}_loc(Ω)`, `ξ ∈ W^{1,q}_loc(Ω)` (`2 < p ≤ ∞`, `1/p + 1/q ≤ 1`), `u, v ∈ ℂ`, and
  `φ ∈ 𝓓(Ω, V)`, without assuming second weak derivatives of `ξ`.

## References

* L. C. Evans, *Partial Differential Equations*, second edition, Section 5.3.1.
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B.4 (Lemma B.4.6 and Proposition B.4.9).
-/

public noncomputable section

open Filter LineDeriv MeasureTheory Set TopologicalSpace
open scoped ContDiff Convolution Distributions ENNReal InnerProductSpace Topology

namespace TauCeti

/-! ### Bilinear mollified pairings -/

section BilinMollification

variable {F G H : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
  {Ω : Opens ℂ} {p : ℝ≥0∞}

/-- Local mollification of a bounded map `f ∈ L^∞_loc(Ω; F)` with weak derivative
`Df ∈ Lᵖ_loc(Ω; ℂ →L[ℝ] F)` (`1 ≤ p ≤ ∞`) near a compact subset `K ⊆ Ω`: produces `C^∞` maps
`fn n : ℂ → F` such that, for every scalar test function `α ∈ 𝓓(Ω, ℝ)` with `tsupport α ⊆ K`, the
`α`-weighted bilinear pairings against any `g ∈ L¹_loc(Ω; G)` and the `α`-weighted
directional-derivative pairings against any `g ∈ L^{p'}_loc(Ω; G)` converge to those of `f` and
`Df` (without requiring `g` itself to be supported in `K`). -/
theorem exists_contDiff_tendsto_integral_smul_bilin_of_hasWeakFDerivOn
    (B : F →L[ℝ] G →L[ℝ] H) (hp1 : 1 ≤ p)
    {f : ℂ → F} {Df : ℂ → ℂ →L[ℝ] F}
    (hfi : MemLpLoc ∞ Ω f) (hDf : HasWeakFDerivOn volume Ω f Df) (hDfp : MemLpLoc p Ω Df)
    {K : Set ℂ} (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    ∃ fn : ℕ → ℂ → F,
      (∀ n, ContDiff ℝ ∞ (fn n)) ∧
      (∀ (α : 𝓓(Ω, ℝ)), tsupport (α : ℂ → ℝ) ⊆ K →
        ∀ {g : ℂ → G}, LocallyIntegrableOn g Ω →
          Tendsto (fun n => ∫ z, (α : ℂ → ℝ) z • B (fn n z) (g z)) atTop
            (𝓝 (∫ z, (α : ℂ → ℝ) z • B (f z) (g z)))) ∧
      (∀ (u : ℂ) (α : 𝓓(Ω, ℝ)), tsupport (α : ℂ → ℝ) ⊆ K →
        ∀ {g : ℂ → G}, MemLpLoc p.conjExponent Ω g →
          Tendsto (fun n => ∫ z, (α : ℂ → ℝ) z • B (fderiv ℝ (fn n) z u) (g z)) atTop
            (𝓝 (∫ z, (α : ℂ → ℝ) z • B (Df z u) (g z)))) := by
  obtain ⟨W, hKW, hWΩ, hWc⟩ := Opens.exists_between_and_isCompact_closure hK hKΩ
  obtain ⟨W', hWW', hW'Ω, hW'c⟩ := Opens.exists_between_and_isCompact_closure hWc hWΩ
  obtain ⟨φ, hφ, hsupp⟩ := ContDiffBump.exists_seq_sub_tsupport_subset (μ := volume) hWc hWW'
  have hW'm := W'.isOpen.measurableSet.nullMeasurableSet (μ := volume)
  let U : ℂ → F := (W' : Set ℂ).indicator f
  have hU_mem (r : ℝ≥0∞) : MemLp U r volume :=
    (memLp_indicator_iff_restrict hW'm).2
      ((hfi.mono_exponent le_top).memLp_restrict_of_isCompact_closure hW'c hW'Ω)
  let fn : ℕ → ℂ → F :=
    fun n => (φ n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] U
  have hfn_smooth (n : ℕ) : ContDiff ℝ ∞ (fn n) :=
    (φ n).hasCompactSupport_normed.contDiff_convolution_left _ (φ n).contDiff_normed
      ((hU_mem p).locallyIntegrable hp1)
  refine ⟨fn, hfn_smooth, fun α hαK {g} hg =>
      B.tendsto_integral_smul_bilin_normed_convolution_indicator hφ (hU_mem ∞)
        α.contDiff.continuous α.hasCompactSupport
        ((hαK.trans hKW).trans (subset_closure.trans hWW'))
        (memLpLoc_iff.1 ((memLpLoc_one_iff_locallyIntegrableOn Ω.isOpen.isLocallyClosed).2 hg) _
          α.tsupport_subset α.hasCompactSupport.isCompact),
    fun u α hαK {g} hg => ?_⟩
  have : p.HolderConjugate p.conjExponent := .conjExponent hp1
  have hU'u : MemLp ((W' : Set ℂ).indicator fun z => Df z u) p volume :=
    (memLp_indicator_iff_restrict hW'm).2
      ((hDfp.clm_comp (ContinuousLinearMap.apply ℝ F u)).memLp_restrict_of_isCompact_closure
        hW'c hW'Ω)
  refine (B.tendsto_integral_smul_bilin_normed_convolution_indicator hφ hU'u
    α.contDiff.continuous α.hasCompactSupport
    ((hαK.trans hKW).trans (subset_closure.trans hWW'))
    (memLpLoc_iff.1 hg _ α.tsupport_subset α.hasCompactSupport.isCompact)).congr fun n =>
      integral_congr_ae (.of_forall fun z => ?_)
  by_cases hz : z ∈ tsupport (α : ℂ → ℝ)
  · have hDfu := (hDf.mono (subset_closure.trans hW'Ω)).hasWeakLineDerivOn u
    rw [hDfu.indicator.convolution_eq_apply_fderiv_convolution
      (L := ContinuousLinearMap.id ℝ F) ((hU_mem p).locallyIntegrable hp1)
      (φ n).contDiff_normed (φ n).hasCompactSupport_normed (hsupp n z (hKW (hαK hz)))]
    rfl
  · simp only [image_eq_zero_of_notMem_tsupport hz, zero_smul]

end BilinMollification

/-! ### Adjoint test-function pairings and mixed-derivative commutator -/

section AdjointAndCommutator

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  {Ω : Opens ℂ} {p q : ℝ≥0∞} {J : ℂ → V →L[ℝ] V} {DJ : ℂ → ℂ →L[ℝ] V →L[ℝ] V}

variable [FiniteDimensional ℝ V]

/-- Local mollification of `J ∈ W^{1,p}_loc(Ω)` (`2 < p ≤ ∞`, `1/p + 1/q ≤ 1`) applied in the form
`(α z) • J_n(z)* v`: produces vector test functions `Ψ n ∈ 𝓓(Ω, V)` whose directional-derivative
pairings against `w ∈ L^q_loc(Ω)` and value pairings against locally integrable `w` on `Ω`
converge to the corresponding pairings of `J` and `DJ`. -/
theorem exists_testFunction_tendsto_integral_inner_of_hasWeakFDerivOn (hp : 2 < p)
    (hpq : p⁻¹ + q⁻¹ ≤ 1) (hJ : MemWkpLoc p Ω 1 J) (hDJ : HasWeakFDerivOn volume Ω J DJ)
    (α : 𝓓(Ω, ℝ)) (v : V) :
    ∃ Ψ : ℕ → 𝓓(Ω, V),
      (∀ (u : ℂ) {w : ℂ → V}, MemLpLoc q Ω w →
        Tendsto (fun n => ∫ z, ⟪fderiv ℝ (Ψ n : ℂ → V) z u, w z⟫_ℝ) atTop
          (𝓝 ((∫ z, (∂_{u} α : 𝓓(Ω, ℝ)) z * ⟪v, J z (w z)⟫_ℝ) +
            ∫ z, (α : ℂ → ℝ) z * ⟪v, DJ z u (w z)⟫_ℝ))) ∧
      (∀ {w : ℂ → V}, LocallyIntegrableOn w Ω →
        Tendsto (fun n => ∫ z, ⟪(Ψ n : ℂ → V) z, w z⟫_ℝ) atTop
          (𝓝 (∫ z, (α : ℂ → ℝ) z * ⟪v, J z (w z)⟫_ℝ))) := by
  have hp1 : 1 < p := ENNReal.one_lt_two.trans hp
  have hq1 : 1 ≤ q := ENNReal.inv_le_one.1 (le_add_self.trans hpq)
  have hp'_le_q : p.conjExponent ≤ q := by
    have : p.HolderConjugate p.conjExponent := .conjExponent hp1.le
    rw [← ENNReal.inv_le_inv, ← ENNReal.HolderConjugate.one_sub_inv p p.conjExponent]
    exact ENNReal.le_sub_of_add_le_left (ENNReal.inv_ne_top.2 (zero_lt_one.trans hp1).ne') hpq
  let B : (V →L[ℝ] V) →L[ℝ] V →L[ℝ] ℝ :=
    (ContinuousLinearMap.compL ℝ V V ℝ (innerSL ℝ v)).comp (ContinuousLinearMap.id ℝ (V →L[ℝ] V))
  obtain ⟨Jn, hJn_smooth, hlim_J, hlim_DJ⟩ :=
    exists_contDiff_tendsto_integral_smul_bilin_of_hasWeakFDerivOn B hp1.le (hJ.memLpLoc_top hp)
      hDJ (hJ.memLpLoc_of_hasWeakFDerivOn hDJ) α.hasCompactSupport.isCompact α.tsupport_subset
  refine ⟨fun n => TestFunction.smulAdjointTestFunction (hJn_smooth n) α v,
    fun u {w} hw => ?_, fun {w} hw => ?_⟩
  · have h1 := hlim_J (∂_{u} α) (α.tsupport_lineDerivOp_subset u)
      (hw.locallyIntegrableOn hq1 Ω.isOpen.isLocallyClosed)
    have h2 := hlim_DJ u α Subset.rfl (hw.mono_exponent hp'_le_q)
    simpa only [B, ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
      ContinuousLinearMap.compL_apply, innerSL_apply_apply, smul_eq_mul] using
      (h1.add h2).congr fun n =>
        (TestFunction.integral_inner_fderiv_smul_adjoint_eq (hJn_smooth n) α v u
          (hw.locallyIntegrableOn hq1 Ω.isOpen.isLocallyClosed)).symm
  · simpa only [B, ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
      ContinuousLinearMap.compL_apply, innerSL_apply_apply, smul_eq_mul] using
      (hlim_J α Subset.rfl hw).congr fun n =>
        integral_congr_ae (.of_forall fun z => by simp [B])

/-- Scalar test-function form of the commutator identity for `J ∈ W^{1,p}_loc(Ω)` and
`ξ ∈ W^{1,q}_loc(Ω)` (`2 < p ≤ ∞`, `1/p + 1/q ≤ 1`) in directions `u, v ∈ ℂ`. -/
private theorem integral_mul_inner_clm_apply_comm_scalar (hp : 2 < p)
    (hpq : p⁻¹ + q⁻¹ ≤ 1) (hJ : MemWkpLoc p Ω 1 J) (hDJ : HasWeakFDerivOn volume Ω J DJ)
    {ξ : ℂ → V} {Dξ : ℂ → ℂ →L[ℝ] V} (hDξ : HasWeakFDerivOn volume Ω ξ Dξ)
    (hDξq : MemLpLoc q Ω Dξ) (u v : ℂ) (α : 𝓓(Ω, ℝ)) (x : V) :
    (∫ z, (∂_{u} α : 𝓓(Ω, ℝ)) z * ⟪x, J z (Dξ z v)⟫_ℝ) +
        (∫ z, (α : ℂ → ℝ) z * ⟪x, DJ z u (Dξ z v)⟫_ℝ) =
      (∫ z, (∂_{v} α : 𝓓(Ω, ℝ)) z * ⟪x, J z (Dξ z u)⟫_ℝ) +
        ∫ z, (α : ℂ → ℝ) z * ⟪x, DJ z v (Dξ z u)⟫_ℝ := by
  obtain ⟨Ψ, hderiv, -⟩ :=
    exists_testFunction_tendsto_integral_inner_of_hasWeakFDerivOn hp hpq hJ hDJ α x
  have hw (w : ℂ) : MemLpLoc q Ω (fun z => Dξ z w) :=
    hDξq.clm_comp (ContinuousLinearMap.apply ℝ V w)
  exact tendsto_nhds_unique (hderiv u (hw v))
    ((hderiv v (hw u)).congr fun n => (hDξ.integral_inner_fderiv_comm u v (Ψ n)).symm)

/-- **Mixed-derivative commutator with a Sobolev coefficient.** If `2 < p ≤ ∞`, `1/p + 1/q ≤ 1`,
`J ∈ W^{1,p}_loc(Ω)` has weak derivative `DJ` and `ξ ∈ W^{1,q}_loc(Ω)` has weak derivative `Dξ`,
then for any directions `u, v ∈ ℂ` and every test function `φ ∈ 𝓓(Ω, V)`,
`∫ ⟪∂_u φ, J (∂_v ξ)⟫ + ∫ ⟪φ, (∂_u J) (∂_v ξ)⟫ = ∫ ⟪∂_v φ, J (∂_u ξ)⟫ + ∫ ⟪φ, (∂_v J) (∂_u ξ)⟫`. -/
theorem integral_inner_fderiv_add_integral_inner_eq_of_hasWeakFDerivOn (hp : 2 < p)
    (hpq : p⁻¹ + q⁻¹ ≤ 1) (hJ : MemWkpLoc p Ω 1 J) (hDJ : HasWeakFDerivOn volume Ω J DJ)
    {ξ : ℂ → V} {Dξ : ℂ → ℂ →L[ℝ] V} (hDξ : HasWeakFDerivOn volume Ω ξ Dξ)
    (hDξq : MemLpLoc q Ω Dξ) (u v : ℂ) (φ : 𝓓(Ω, V)) :
    (∫ z, ⟪fderiv ℝ (φ : ℂ → V) z u, J z (Dξ z v)⟫_ℝ) +
        (∫ z, ⟪(φ : ℂ → V) z, DJ z u (Dξ z v)⟫_ℝ) =
      (∫ z, ⟪fderiv ℝ (φ : ℂ → V) z v, J z (Dξ z u)⟫_ℝ) +
        ∫ z, ⟪(φ : ℂ → V) z, DJ z v (Dξ z u)⟫_ℝ := by
  let b := stdOrthonormalBasis ℝ V
  let α : Fin (Module.finrank ℝ V) → 𝓓(Ω, ℝ) :=
    fun i => TestFunction.postcompCLM (innerSL ℝ (b i)) φ
  have hloc := Ω.isOpen.isLocallyClosed
  have hDJp : MemLpLoc p Ω DJ := hJ.memLpLoc_of_hasWeakFDerivOn hDJ
  have hα_deriv (i : Fin (Module.finrank ℝ V)) (w : ℂ) (z : ℂ) :
      (∂_{w} (α i) : 𝓓(Ω, ℝ)) z = ⟪b i, fderiv ℝ (φ : ℂ → V) z w⟫_ℝ := by
    simp [α, TestFunction.lineDeriv_eq_fderiv]
  have hparseval (x y : V) : ⟪x, y⟫_ℝ = ∑ i, ⟪b i, x⟫_ℝ * ⟪b i, y⟫_ℝ := by
    rw [← b.sum_inner_mul_inner x y]
    exact Finset.sum_congr rfl fun i _ => by rw [real_inner_comm]
  have hsum_val {w : ℂ → V} (hw : LocallyIntegrableOn w Ω) :
      ∫ z, ⟪(φ : ℂ → V) z, w z⟫_ℝ = ∑ i, ∫ z, (α i : ℂ → ℝ) z * ⟪b i, w z⟫_ℝ := by
    rw [← integral_finsetSum _ fun i _ => (α i).integrable_mul_inner hw (b i)]
    exact integral_congr_ae (.of_forall fun z => hparseval ((φ : ℂ → V) z) (w z))
  have hsum_deriv (d : ℂ) {w : ℂ → V} (hw : LocallyIntegrableOn w Ω) :
      ∫ z, ⟪fderiv ℝ (φ : ℂ → V) z d, w z⟫_ℝ =
        ∑ i, ∫ z, (∂_{d} (α i) : 𝓓(Ω, ℝ)) z * ⟪b i, w z⟫_ℝ := by
    rw [← integral_finsetSum _ fun i _ => (∂_{d} (α i)).integrable_mul_inner hw (b i)]
    exact integral_congr_ae (.of_forall fun z => by
      dsimp only; simpa only [hα_deriv] using hparseval (fderiv ℝ (φ : ℂ → V) z d) (w z))
  have hADξ {A : ℂ → V →L[ℝ] V} (hA : MemLpLoc p Ω A) (d : ℂ) :
      LocallyIntegrableOn (fun z => A z (Dξ z d)) Ω :=
    hA.locallyIntegrableOn_clm_apply (hDξq.clm_comp (ContinuousLinearMap.apply ℝ V d)) hpq hloc
  have hDJu (d : ℂ) : MemLpLoc p Ω (fun z => DJ z d) :=
    hDJp.clm_comp (ContinuousLinearMap.apply ℝ (V →L[ℝ] V) d)
  rw [hsum_deriv u (hADξ hJ.memLpLoc v), hsum_val (hADξ (hDJu u) v),
    hsum_deriv v (hADξ hJ.memLpLoc u), hsum_val (hADξ (hDJu v) u),
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ =>
    integral_mul_inner_clm_apply_comm_scalar hp hpq hJ hDJ hDξ hDξq u v (α i) (b i)

end AdjointAndCommutator

end TauCeti
