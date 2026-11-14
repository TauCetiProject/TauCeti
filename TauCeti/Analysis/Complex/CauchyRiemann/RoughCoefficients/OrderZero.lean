/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.BumpFunction.Convolution
public import TauCeti.Analysis.Complex.CauchyRiemann.RoughCoefficients.Weak
public import TauCeti.Analysis.InnerProductSpace.Laplacian.Basic
import TauCeti.Analysis.Complex.Wirtinger.DivergenceLaplace
import TauCeti.Analysis.Distribution.TestFunction.Inner
import TauCeti.Analysis.Distribution.TestFunction.LineDeriv
import TauCeti.Analysis.Sobolev.Local.Multiplication
import TauCeti.Analysis.Sobolev.Local.SobolevEmbedding
import TauCeti.Analysis.Sobolev.Mollification.Basic
import TauCeti.Data.ENNReal.Inv
import TauCeti.MeasureTheory.Function.Lp.ApproximateIdentity

/-!
# Order-zero interior regularity for Cauchy–Riemann equations with Sobolev coefficients

Let `Ω ⊆ ℂ` be open, write `z = s + i t`, and let `V` be a finite-dimensional real inner product
space. For `2 < p < ∞`, an almost complex structure `J ∈ W^{1,p}_loc(Ω; V →L[ℝ] V)` satisfying
`J² = -1` almost everywhere on `Ω` with weak derivative `DJ`, and a zeroth-order coefficient
`S ∈ Lᵖ_loc(Ω; V →L[ℝ] V)`, consider a weak solution `ξ` of

`∂_s ξ + J ∂_t ξ + S ξ = η`

in the sense of `TauCeti.IsWeakCRSolution q Ω J DJ S ξ η`. When `1/p + 1/q < 1`, this file proves
interior regularity at order zero (McDuff–Salamon, Lemma B.4.6):

1. *Reduction to the divergence-form Laplace equation*
   (`TauCeti.IsWeakCRSolution.integral_laplacian_smul_eq`). When `η ∈ Lᵗ_loc(Ω)` for some `t > 1`,
   for every real test function `ψ` on `Ω`, `Δ ξ = ∂_s f + ∂_t g` weakly on `Ω` with
   `f = η - S ξ + (∂_t J) ξ` and `g = -J η + J S ξ - (∂_s J) ξ`.
   The proof tests the weak equation against `(∂_s ψ) • v` and against the smooth test functions
   `-(∂_t ψ) • J_nᵀ v` obtained by mollifying `J` near `tsupport ψ`. Passing to the limit cancels
   the mixed second derivatives of `ψ` and uses `(∂_t J) J + J (∂_t J) = 0`, obtained by
   differentiating `J² = -1` weakly.
2. *Single Hölder step* (`TauCeti.IsWeakCRSolution.memWkpLoc_one_of_inv_add_inv_le`). If
   `1 < r < ∞`, `1/p + 1/q ≤ 1/r` and `η ∈ Lʳ_loc(Ω)`, then `f, g ∈ Lʳ_loc(Ω)`, so divergence-form
   Laplace regularity (`TauCeti.memWkpLoc_one_of_forall_integral_laplacian_smul_eq`) puts `ξ` in
   `W^{1,r}_loc(Ω)`.
3. *Bootstrap across the Sobolev exponent ladder*
   (`TauCeti.IsWeakCRSolution.memWkpLoc_one_of_memLpLoc`). If `1/p + 1/q < 1`, `1 < s ≤ p` and
   `η ∈ Lˢ_loc(Ω)`, alternating the single Hölder step with the two-dimensional Sobolev embedding
   decreases `1/q` by `1/2 - 1/p > 0` at each subcritical step until the product exponent exceeds
   `2`, where `W^{1,r}_loc ⊂ L^∞_loc` finishes in one more step and yields `ξ ∈ W^{1,s}_loc(Ω)`.
   In particular `ξ ∈ W^{1,q}_loc(Ω)` when `q ≤ p` and `η ∈ L^q_loc(Ω)`
   (`TauCeti.IsWeakCRSolution.memWkpLoc_one_of_le`), and `ξ ∈ W^{1,p}_loc(Ω)` when `η ∈ Lᵖ_loc(Ω)`
   (`TauCeti.IsWeakCRSolution.memWkpLoc_one`).

The strict inequality `1/p + 1/q < 1`, that is `q > p / (p - 1)`, is sharp for this route: at the
conjugate exponent `1/p + 1/q = 1` the product exponent is `r = 1`, where Calderón–Zygmund
estimates for the Cauchy transform fail (`TauCeti.productExponent_conjugate`).

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
   Appendix B.4 (Lemma B.4.4 and Lemma B.4.6).
-/

public noncomputable section

open Complex Filter Laplacian LineDeriv MeasureTheory Set TopologicalSpace
open scoped ContDiff Convolution Distributions ENNReal InnerProductSpace NNReal Topology

namespace TauCeti

/-! ### Weakly differentiating `J² = -1` and passing mollified pairings to the limit -/

section NormedSpace

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {Ω : Opens ℂ} {p : ℝ≥0∞} {J : ℂ → V →L[ℝ] V} {DJ : ℂ → ℂ →L[ℝ] V →L[ℝ] V}

/-- Differentiating `J ∘ J = -1` weakly on `Ω` gives `(DJ · v) ∘ J + J ∘ (DJ · v) = 0` almost
everywhere on `Ω` for every direction `v ∈ ℂ`. The endpoint `p = ⊤` is included by passing locally
to `min p 3`. -/
theorem HasWeakFDerivOn.ae_apply_add_apply_eq_zero_of_comp_self_eq_neg_id
    (hDJ : HasWeakFDerivOn volume Ω J DJ) (hp : 2 < p) (hJ : MemWkpLoc p Ω 1 J)
    (hJsq : ∀ᵐ z ∂volume.restrict Ω, (J z).comp (J z) = -ContinuousLinearMap.id ℝ V) (v : ℂ) :
    ∀ᵐ z ∂volume.restrict Ω, ∀ w : V, DJ z v (J z w) + J z (DJ z v w) = 0 := by
  have : CompleteSpace V := FiniteDimensional.completeSpace ℝ V
  let p₀ : ℝ≥0 := (min p 3).toNNReal
  have hp₀_coe : (p₀ : ℝ≥0∞) = min p 3 :=
    ENNReal.coe_toNNReal (ne_top_of_le_ne_top ENNReal.ofNat_ne_top (min_le_right p 3))
  have hp₀ : 2 < (p₀ : ℝ≥0∞) :=
    hp₀_coe ▸ lt_min hp (by exact_mod_cast (by norm_num : 2 < 3))
  have hJ₀ : MemWkpLoc p₀ Ω 1 J := hJ.mono_exponent (hp₀_coe.le.trans (min_le_left p 3))
  have hp₀' : 2 < p₀ := by exact_mod_cast hp₀
  have hp₀1 : 1 < p₀ := one_lt_two.trans hp₀'
  have hDJp₀ : MemLpLoc p₀ Ω DJ := hJ₀.memLpLoc_of_hasWeakFDerivOn hDJ
  have hprod := hDJ.bilin_of_memLpLoc (ContinuousLinearMap.compL ℝ V V V) hp₀' hp₀1 le_rfl
    ((hJ₀.memLpLoc_top hp₀).mono_exponent le_top) hDJp₀ hDJ hJ₀.memLpLoc hDJp₀
  have hconst : HasWeakFDerivOn volume Ω (fun _ : ℂ => -ContinuousLinearMap.id ℝ V) 0 :=
    hasWeakFDerivOn_iff.2 fun u => by
      simpa using hasWeakLineDerivOn_const (μ := volume) (Ω := Ω) (v := u)
        (-ContinuousLinearMap.id ℝ V)
  filter_upwards [(hprod.congr_ae hJsq).ae_eq hconst] with z hz w
  simpa using congr($(congr($hz v)) w)

end NormedSpace

section MollifiedPairing

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  {Ω : Opens ℂ} {p : ℝ≥0∞} {J : ℂ → V →L[ℝ] V} {DJ : ℂ → ℂ →L[ℝ] V →L[ℝ] V}

/-- Pairing a mollified operator field `(φ i).normed volume ⋆ U` (`U ∈ Lˢ(ℂ)`, `1 < s < ∞`) against
a compactly supported vector field `α • w` with `w ∈ L^{s'}` on `tsupport α` converges along `l` to
the pairing of `U` when `(φ i).rOut → 0`. -/
private theorem tendsto_integral_mul_inner_normed_convolution_apply {I : Type*} {l : Filter I}
    {s : ℝ≥0∞} (hs1 : 1 < s) (hs_top : s ≠ ⊤) {φ : I → ContDiffBump (0 : ℂ)}
    (hφ : Tendsto (fun i => (φ i).rOut) l (𝓝 0)) {U : ℂ → V →L[ℝ] V} (hU : MemLp U s volume)
    {α : ℂ → ℝ} (hα : Continuous α) (hαc : HasCompactSupport α)
    {w : ℂ → V} (hw : MemLp w s.conjExponent (volume.restrict (tsupport α))) (v : V) :
    Tendsto (fun i => ∫ z, α z *
        ⟪v, (((φ i).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] U) z) (w z)⟫_ℝ)
      l (𝓝 (∫ z, α z * ⟪v, U z (w z)⟫_ℝ)) := by
  let s' := s.conjExponent
  have : Fact (1 ≤ s) := ⟨hs1.le⟩
  have : s.HolderConjugate s' := ENNReal.HolderConjugate.conjExponent hs1.le
  have : Fact (1 ≤ s') := ⟨ENNReal.HolderConjugate.one_le s' s⟩
  -- `α • w` vanishes outside `tsupport α` and is bounded by `sup |α| • w` on `tsupport α`, so it
  -- belongs to `L^{s'}(ℂ)` globally.
  have hαw_ind : (fun z => α z • w z) = (tsupport α).indicator (fun z => α z • w z) := by
    ext z
    by_cases hz : z ∈ tsupport α
    · simp [hz]
    · simp [hz, image_eq_zero_of_notMem_tsupport hz]
  have hαw_on : MemLp (fun z => α z • w z) s' (volume.restrict (tsupport α)) := by
    obtain ⟨C, hC⟩ := hαc.isCompact.exists_bound_of_continuousOn hα.continuousOn
    exact (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] V →L[ℝ] V).memLp_of_bilin s'
      (memLp_top_of_bound hα.aestronglyMeasurable.restrict C
        ((ae_restrict_iff' (isClosed_tsupport α).measurableSet).2 (.of_forall hC))) hw
  have hαw : MemLp (fun z => α z • w z) s' volume := by
    rw [hαw_ind]
    exact (memLp_indicator_iff_restrict (isClosed_tsupport α).measurableSet.nullMeasurableSet).2
      hαw_on
  let B : (V →L[ℝ] V) →L[ℝ] V →L[ℝ] ℝ :=
    (ContinuousLinearMap.compL ℝ V V ℝ (innerSL ℝ v)).comp (ContinuousLinearMap.id ℝ (V →L[ℝ] V))
  have hB (A : V →L[ℝ] V) (x : V) : B A x = ⟪v, A x⟫_ℝ := rfl
  let L : Lp (V →L[ℝ] V) s volume →L[ℝ] ℝ :=
    (B.lpPairing volume s s').flip (hαw.toLp (fun z => α z • w z))
  have hpair (g : Lp (V →L[ℝ] V) s volume) (G : ℂ → V →L[ℝ] V) (hg : g =ᵐ[volume] G) :
      L g = ∫ z, α z * ⟪v, G z (w z)⟫_ℝ := by
    dsimp only [L]
    rw [ContinuousLinearMap.flip_apply, ContinuousLinearMap.lpPairing_eq_integral]
    refine integral_congr_ae ?_
    filter_upwards [hg, hαw.coeFn_toLp] with z hGz hwz
    simp only [hGz, hwz, hB, map_smul, inner_smul_right]
  have hlim := L.continuous.tendsto (hU.toLp U) |>.comp (tendsto_normedBumpLp hs_top hφ (hU.toLp U))
  have hpair_i (i : I) : L (normedBumpLp hs_top (φ i) volume (hU.toLp U)) =
      ∫ z, α z *
        ⟪v, (((φ i).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] U) z) (w z)⟫_ℝ :=
    hpair _ _ (normedBumpLp_ae_eq_convolution hs_top (φ i) hU)
  simpa only [Function.comp_def, hpair_i, hpair _ _ hU.coeFn_toLp] using hlim

/-- Local mollification of a bounded `W^{1,p}_loc(Ω)` operator field near a compact subset `K ⊆ Ω`:
produces `C^∞` maps `Jn n` whose pairings and derivative pairings against fields supported in `K`
converge to those of `J` and `DJ`. -/
private theorem exists_contDiff_tendsto_integral_mul_inner_of_hasWeakFDerivOn
    (hp1 : 1 < p) (hp_top : p ≠ ⊤)
    (hJi : MemLpLoc ∞ Ω J) (hDJ : HasWeakFDerivOn volume Ω J DJ) (hDJp : MemLpLoc p Ω DJ)
    {K : Set ℂ} (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    ∃ Jn : ℕ → ℂ → V →L[ℝ] V,
      (∀ n, ContDiff ℝ ∞ (Jn n)) ∧
      (∀ {s : ℝ≥0∞}, 1 < s → s ≠ ⊤ → ∀ (α : 𝓓(Ω, ℝ)), tsupport (α : ℂ → ℝ) ⊆ K →
        ∀ {w : ℂ → V}, MemLpLoc s Ω w → ∀ (v : V),
          Tendsto (fun n => ∫ z, (α : ℂ → ℝ) z * ⟪v, Jn n z (w z)⟫_ℝ) atTop
            (𝓝 (∫ z, (α : ℂ → ℝ) z * ⟪v, J z (w z)⟫_ℝ))) ∧
      (∀ (u : ℂ) (α : 𝓓(Ω, ℝ)), tsupport (α : ℂ → ℝ) ⊆ K →
        ∀ {w : ℂ → V}, MemLpLoc p.conjExponent Ω w → ∀ (v : V),
          Tendsto (fun n => ∫ z, (α : ℂ → ℝ) z * ⟪v, fderiv ℝ (Jn n) z u (w z)⟫_ℝ) atTop
            (𝓝 (∫ z, (α : ℂ → ℝ) z * ⟪v, DJ z u (w z)⟫_ℝ))) := by
  -- Choose nested open neighbourhoods `K ⊆ W ⊂⊂ W' ⊂⊂ Ω` and bump kernels `φ n` with
  -- `W - tsupport (φ n) ⊆ W'`, then extend `J` by zero outside `W'`.
  obtain ⟨W, hKW, hWΩ, hWc⟩ := Opens.exists_between_and_isCompact_closure hK hKΩ
  obtain ⟨W', hWW', hW'Ω, hW'c⟩ := Opens.exists_between_and_isCompact_closure hWc hWΩ
  obtain ⟨φ, hφ, hsupp⟩ := ContDiffBump.exists_seq_sub_tsupport_subset (μ := volume) hWc hWW'
  have hW'm := W'.isOpen.measurableSet.nullMeasurableSet (μ := volume)
  have hJW'_top : MemLp J ∞ (volume.restrict W') :=
    (memLpLoc_iff.1 hJi _ hW'Ω hW'c).mono_measure (Measure.restrict_mono subset_closure le_rfl)
  have hW'_fin : volume (W' : Set ℂ) < ⊤ :=
    (measure_mono subset_closure).trans_lt hW'c.measure_lt_top
  have hJW'_mem (r : ℝ≥0∞) : MemLp J r (volume.restrict W') := by
    have : IsFiniteMeasure (volume.restrict (W' : Set ℂ)) := isFiniteMeasure_restrict.2 hW'_fin.ne
    exact hJW'_top.mono_exponent le_top
  let U : ℂ → V →L[ℝ] V := (W' : Set ℂ).indicator J
  have hU_mem (r : ℝ≥0∞) : MemLp U r volume := (memLp_indicator_iff_restrict hW'm).2 (hJW'_mem r)
  let Jn : ℕ → ℂ → V →L[ℝ] V :=
    fun n => (φ n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] U
  have hJn_smooth (n : ℕ) : ContDiff ℝ ∞ (Jn n) :=
    (φ n).hasCompactSupport_normed.contDiff_convolution_left _ (φ n).contDiff_normed
      ((hU_mem p).locallyIntegrable hp1.le)
  refine ⟨Jn, hJn_smooth, ?_, ?_⟩
  · -- Value pairings converge in `L^{s'}(ℂ)` since `U ∈ L^r(ℂ)` for every finite `r`.
    intro s hs1 hs_top α hαK w hw v
    have hs'_gt : 1 < s.conjExponent :=
      ENNReal.lt_add_right ENNReal.one_ne_top
        (ENNReal.inv_ne_zero.2 (ne_top_of_le_ne_top hs_top tsub_le_self))
    have hs'_top : s.conjExponent ≠ ⊤ :=
      ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, ENNReal.inv_ne_top.2 (tsub_pos_of_lt hs1).ne'⟩
    have hαW' : tsupport (α : ℂ → ℝ) ⊆ W' := (hαK.trans hKW).trans (subset_closure.trans hWW')
    have hw_s : MemLp w s.conjExponent.conjExponent (volume.restrict (tsupport (α : ℂ → ℝ))) := by
      have : s.conjExponent.HolderConjugate s := (ENNReal.HolderConjugate.conjExponent hs1.le).symm
      rw [ENNReal.HolderConjugate.conjExponent_eq (p := s.conjExponent) (q := s)]
      exact memLpLoc_iff.1 hw _ (hαK.trans hKΩ) α.hasCompactSupport.isCompact
    refine (tendsto_integral_mul_inner_normed_convolution_apply hs'_gt hs'_top hφ
      (hU_mem s.conjExponent) α.contDiff.continuous α.hasCompactSupport hw_s v).trans_eq
      (congrArg 𝓝 (integral_congr_ae (.of_forall fun z => ?_)))
    by_cases hz : z ∈ tsupport (α : ℂ → ℝ)
    · simp only [U, indicator_of_mem (hαW' hz)]
    · simp only [image_eq_zero_of_notMem_tsupport hz, zero_mul]
  · -- On `W`, `fderiv ℝ (Jn n) · u` equals the convolution of `(W').indicator (DJ · u)`, so
    -- derivative pairings converge in `Lᵖ(ℂ)`.
    intro u α hαK w hw v
    let U'u : ℂ → V →L[ℝ] V := (W' : Set ℂ).indicator fun z => DJ z u
    have hDJu_loc : MemLpLoc p Ω (fun z => DJ z u) :=
      hDJp.clm_comp (ContinuousLinearMap.apply ℝ (V →L[ℝ] V) u)
    have hU'u : MemLp U'u p volume :=
      (memLp_indicator_iff_restrict hW'm).2
        ((memLpLoc_iff.1 hDJu_loc _ hW'Ω hW'c).mono_measure
          (Measure.restrict_mono subset_closure le_rfl))
    have hfderiv_Jn (n : ℕ) {z : ℂ} (hz : z ∈ (W : Set ℂ)) :
        fderiv ℝ (Jn n) z u =
          (((φ n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] U'u) z) := by
      have hDJu : HasWeakLineDerivOn volume W' J (fun z => DJ z u) u :=
        (hDJ.mono (subset_closure.trans hW'Ω)).hasWeakLineDerivOn u
      exact (hDJu.indicator.convolution_eq_apply_fderiv_convolution
        (L := ContinuousLinearMap.id ℝ (V →L[ℝ] V)) ((hU_mem p).locallyIntegrable hp1.le)
        (φ n).contDiff_normed (φ n).hasCompactSupport_normed (hsupp n z hz)).symm
    have hαW' : tsupport (α : ℂ → ℝ) ⊆ W' := (hαK.trans hKW).trans (subset_closure.trans hWW')
    have hw_p' : MemLp w p.conjExponent (volume.restrict (tsupport (α : ℂ → ℝ))) :=
      memLpLoc_iff.1 hw _ (hαK.trans hKΩ) α.hasCompactSupport.isCompact
    refine ((tendsto_integral_mul_inner_normed_convolution_apply hp1 hp_top hφ hU'u
      α.contDiff.continuous α.hasCompactSupport hw_p' v).congr fun n =>
      integral_congr_ae (.of_forall fun z => ?_)).trans_eq
      (congrArg 𝓝 (integral_congr_ae (.of_forall fun z => ?_)))
    · by_cases hz : z ∈ tsupport (α : ℂ → ℝ)
      · rw [hfderiv_Jn n (hKW (hαK hz))]
      · simp only [image_eq_zero_of_notMem_tsupport hz, zero_mul]
    · by_cases hz : z ∈ tsupport (α : ℂ → ℝ)
      · simp only [U'u, indicator_of_mem (hαW' hz)]
      · simp only [image_eq_zero_of_notMem_tsupport hz, zero_mul]

/-- Expanding the directional derivative of the vector test function `z ↦ α z • F(z)* v` against a
locally `L^q` field `w` splits into the `∂_u α` and `∂_u F` terms. -/
private theorem integral_inner_fderiv_smul_adjoint_eq {q : ℝ≥0∞} (hq1 : 1 ≤ q)
    {F : ℂ → V →L[ℝ] V} (hF : ContDiff ℝ ∞ F) (α : 𝓓(Ω, ℝ)) (v : V) (u : ℂ) {w : ℂ → V}
    (hw : MemLpLoc q Ω w) :
    let adjV : (V →L[ℝ] V) →L[ℝ] V :=
      (ContinuousLinearMap.apply ℝ V v).comp
        ((ContinuousLinearMap.adjoint : (V →L[ℝ] V) ≃ₗᵢ⋆[ℝ] (V →L[ℝ] V)).toContinuousLinearEquiv
          |> ContinuousLinearEquiv.toContinuousLinearMap)
    let Ψ : 𝓓(Ω, V) := ⟨fun z => (α : ℂ → ℝ) z • adjV (F z),
      α.contDiff.smul (adjV.contDiff.comp hF), α.hasCompactSupport.smul_right,
      (tsupport_smul_subset_left (α : ℂ → ℝ) _).trans α.tsupport_subset⟩
    ∫ z, ⟪fderiv ℝ (Ψ : ℂ → V) z u, w z⟫_ℝ =
      (∫ z, (∂_{u} α : 𝓓(Ω, ℝ)) z * ⟪v, F z (w z)⟫_ℝ) +
        ∫ z, (α : ℂ → ℝ) z * ⟪v, fderiv ℝ F z u (w z)⟫_ℝ := by
  intro adjV Ψ
  have hloc := Ω.isOpen.isLocallyClosed
  have htop_q : (⊤ : ℝ≥0∞)⁻¹ + q⁻¹ ≤ 1 := by simpa using ENNReal.inv_le_one.2 hq1
  let αu : 𝓓(Ω, ℝ) := ∂_{u} α
  have hi1 := αu.integrable_mul_inner
    ((hF.continuous.continuousOn.memLpLoc (p := ⊤)).locallyIntegrableOn_clm_apply hw htop_q hloc) v
  have hF1 : ContDiff ℝ 1 F := hF.of_le (WithTop.coe_le_coe.2 (le_top : (1 : ℕ∞) ≤ ⊤))
  have hDF_c : Continuous fun z => fderiv ℝ F z u :=
    (ContinuousLinearMap.apply ℝ (V →L[ℝ] V) u).continuous.comp (hF1.continuous_fderiv one_ne_zero)
  have hi2 := α.integrable_mul_inner
    ((hDF_c.continuousOn.memLpLoc (p := ⊤)).locallyIntegrableOn_clm_apply hw htop_q hloc) v
  have hcoe : (Ψ : ℂ → V) = (α : ℂ → ℝ) • (adjV ∘ F) := by ext z; simp [Ψ]
  rw [← integral_add hi1 hi2]
  refine integral_congr_ae (.of_forall fun z => ?_)
  have h1 := (α.contDiff.differentiable (by simp) z).hasFDerivAt
  have h2 := adjV.hasFDerivAt.comp z ((hF.differentiable (by simp) z).hasFDerivAt)
  dsimp only
  rw [hcoe, (h1.smul h2).fderiv]
  simp only [αu, TestFunction.lineDerivOp_apply_eq_fderiv α u z, adjV, add_apply,
    ContinuousLinearMap.smulRight_apply, smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.apply_apply, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
    ContinuousLinearEquiv.coe_coe, Function.comp_apply, inner_add_left, inner_smul_left,
    RCLike.conj_to_real, ContinuousLinearMap.adjoint_inner_left]
  ring

end MollifiedPairing

/-! ### Reduction to the divergence-form Laplace equation -/

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {Ω : Opens ℂ} {p q r s : ℝ≥0∞}
  {J S : ℂ → V →L[ℝ] V} {DJ : ℂ → ℂ →L[ℝ] V →L[ℝ] V} {ξ η : ℂ → V}

/-- Local mollification of `J ∈ W^{1,p}_loc(Ω)` (`2 < p < ∞`, `1/p + 1/q < 1`) applied in the form
`(α z) • J_n(z)* v`: produces vector test functions `Ψ n ∈ 𝓓(Ω, V)` whose directional-derivative
pairings against `w ∈ L^q_loc(Ω)` and value pairings against `w ∈ L^r_loc(Ω)` (`1 < r < ∞`)
converge to the corresponding pairings of `J` and `DJ`. -/
theorem exists_testFunction_tendsto_integral_inner_of_hasWeakFDerivOn (hp : 2 < p) (hp_top : p ≠ ⊤)
    (hpq : p⁻¹ + q⁻¹ < 1) (hJ : MemWkpLoc p Ω 1 J) (hDJ : HasWeakFDerivOn volume Ω J DJ)
    (α : 𝓓(Ω, ℝ)) (v : V) :
    ∃ Ψ : ℕ → 𝓓(Ω, V),
      (∀ (u : ℂ) {w : ℂ → V}, MemLpLoc q Ω w →
        Tendsto (fun n => ∫ z, ⟪fderiv ℝ (Ψ n : ℂ → V) z u, w z⟫_ℝ) atTop
          (𝓝 ((∫ z, (∂_{u} α : 𝓓(Ω, ℝ)) z * ⟪v, J z (w z)⟫_ℝ) +
            ∫ z, (α : ℂ → ℝ) z * ⟪v, DJ z u (w z)⟫_ℝ))) ∧
      (∀ {r : ℝ≥0∞}, 1 < r → r ≠ ⊤ → ∀ {w : ℂ → V}, MemLpLoc r Ω w →
        Tendsto (fun n => ∫ z, ⟪(Ψ n : ℂ → V) z, w z⟫_ℝ) atTop
          (𝓝 (∫ z, (α : ℂ → ℝ) z * ⟪v, J z (w z)⟫_ℝ))) := by
  have hp1 : 1 < p := (by exact_mod_cast one_lt_two : (1 : ℝ≥0∞) < 2).trans hp
  have hq1 : 1 < q := ENNReal.inv_lt_one.1 (lt_of_le_of_lt le_add_self hpq)
  have hp'_le_q : p.conjExponent ≤ q := by
    have : Fact (1 ≤ p) := ⟨hp1.le⟩
    rw [← ENNReal.inv_le_inv, ← ENNReal.HolderConjugate.one_sub_inv p p.conjExponent]
    exact ENNReal.le_sub_of_add_le_left (ENNReal.inv_ne_top.2 (zero_lt_one.trans hp1).ne') hpq.le
  have hq_min_gt : 1 < min q p := lt_min hq1 hp1
  have hq_min_top : min q p ≠ ⊤ := ne_top_of_le_ne_top hp_top (min_le_right q p)
  obtain ⟨Jn, hJn_smooth, hlim_J, hlim_DJ⟩ :=
    exists_contDiff_tendsto_integral_mul_inner_of_hasWeakFDerivOn hp1 hp_top (hJ.memLpLoc_top hp)
      hDJ (hJ.memLpLoc_of_hasWeakFDerivOn hDJ) α.hasCompactSupport.isCompact α.tsupport_subset
  let adjV : (V →L[ℝ] V) →L[ℝ] V :=
    (ContinuousLinearMap.apply ℝ V v).comp
      ((ContinuousLinearMap.adjoint : (V →L[ℝ] V) ≃ₗᵢ⋆[ℝ] (V →L[ℝ] V)).toContinuousLinearEquiv
        |> ContinuousLinearEquiv.toContinuousLinearMap)
  let Ψ : ℕ → 𝓓(Ω, V) := fun n =>
    ⟨fun z => (α : ℂ → ℝ) z • adjV (Jn n z),
      α.contDiff.smul (adjV.contDiff.comp (hJn_smooth n)),
      α.hasCompactSupport.smul_right,
      (tsupport_smul_subset_left (α : ℂ → ℝ) _).trans α.tsupport_subset⟩
  refine ⟨Ψ, fun u {w} hw => ?_, fun {r} hr_gt hr_top {w} hw => ?_⟩
  · exact ((hlim_J hq_min_gt hq_min_top (∂_{u} α) (α.tsupport_lineDerivOp_subset u)
        (hw.mono_exponent (min_le_left q p)) v).add
      (hlim_DJ u α Subset.rfl (hw.mono_exponent hp'_le_q) v)).congr fun n =>
        (integral_inner_fderiv_smul_adjoint_eq hq1.le (hJn_smooth n) α v u hw).symm
  · refine (hlim_J hr_gt hr_top α Subset.rfl hw v).congr fun n =>
      integral_congr_ae (.of_forall fun z => ?_)
    simp only [Ψ, adjV, TestFunction.coe_mk, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.apply_apply, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
      ContinuousLinearEquiv.coe_coe, inner_smul_left, RCLike.conj_to_real,
      ContinuousLinearMap.adjoint_inner_left]

namespace IsWeakCRSolution

/-- Testing `∂_s ξ + J ∂_t ξ + S ξ = η` against `(∂_s ψ) • v` gives the `∂_s² ψ` and mixed
`∂_s ∂_t ψ` terms of the divergence-form Laplace identity. -/
private theorem integral_test_lineDeriv_one (hpq : p⁻¹ + q⁻¹ ≤ 1)
    (hc : IsSobolevCRCoefficients p Ω J DJ S) (hsol : IsWeakCRSolution q Ω J DJ S ξ η)
    (ψ : 𝓓(Ω, ℝ)) (v : V) :
    (-∫ z, (∂_{(1 : ℂ)} (∂_{(1 : ℂ)} ψ) : 𝓓(Ω, ℝ)) z * ⟪v, ξ z⟫_ℝ) -
      (∫ z, (∂_{(1 : ℂ)} (∂_{(I : ℂ)} ψ) : 𝓓(Ω, ℝ)) z * ⟪v, J z (ξ z)⟫_ℝ) -
      (∫ z, (∂_{(1 : ℂ)} ψ : 𝓓(Ω, ℝ)) z * ⟪v, DJ z I (ξ z)⟫_ℝ) +
      (∫ z, (∂_{(1 : ℂ)} ψ : 𝓓(Ω, ℝ)) z * ⟪v, S z (ξ z)⟫_ℝ) =
      ∫ z, (∂_{(1 : ℂ)} ψ : 𝓓(Ω, ℝ)) z * ⟪v, η z⟫_ℝ := by
  let ψs : 𝓓(Ω, ℝ) := ∂_{(1 : ℂ)} ψ
  let L : ℝ →L[ℝ] V := (ContinuousLinearMap.id ℝ ℝ).smulRight v
  let Φ₁ : 𝓓(Ω, V) := TestFunction.postcompCLM L ψs
  have hΦ₁_fderiv (u : ℂ) (z : ℂ) :
      fderiv ℝ (Φ₁ : ℂ → V) z u = (∂_{u} ψs : 𝓓(Ω, ℝ)) z • v := by
    rw [← TestFunction.lineDerivOp_apply_eq_fderiv, TestFunction.lineDerivOp_eq_lineDerivCLM ℝ,
      TestFunction.lineDerivCLM_postcompCLM]
    simp [L, ← TestFunction.lineDerivOp_eq_lineDerivCLM ℝ]
  have hderiv (u : ℂ) (w : ℂ → V) :
      ∫ z, ⟪fderiv ℝ (Φ₁ : ℂ → V) z u, w z⟫_ℝ = ∫ z, (∂_{u} ψs : 𝓓(Ω, ℝ)) z * ⟪v, w z⟫_ℝ :=
    integral_congr_ae (.of_forall fun z => by
      dsimp only; rw [hΦ₁_fderiv u z, inner_smul_left, RCLike.conj_to_real])
  have hval (w : ℂ → V) :
      ∫ z, ⟪(Φ₁ : ℂ → V) z, w z⟫_ℝ = ∫ z, (ψs : ℂ → ℝ) z * ⟪v, w z⟫_ℝ :=
    integral_congr_ae (.of_forall fun z => by simp [Φ₁, L, inner_smul_left])
  have hmain := (hc.integral_inner_crFormalAdjoint_eq_terms hpq hsol.memLpLoc Φ₁).symm.trans
    (hsol.integral_inner_crFormalAdjoint Φ₁)
  rwa [hderiv 1 ξ, hderiv I, ← TestFunction.lineDerivOp_comm ψ 1 I, hval, hval, hval] at hmain

/-- Testing `∂_s ξ + J ∂_t ξ + S ξ = η` against `(∂_t ψ) • J_nᵀ v`, passing to the limit as the
mollifier radius tends to zero, and simplifying `J² = -1` and `(∂_t J) J + J (∂_t J) = 0` gives the
`∂_t² ψ` and mixed `∂_t ∂_s ψ` terms of the divergence-form Laplace identity. -/
private theorem integral_test_mollified_adjoint (hp : 2 < p) (hp_top : p ≠ ⊤)
    (hpq : p⁻¹ + q⁻¹ < 1) {r₀ : ℝ≥0∞} (hr₀_gt : 1 < r₀) (hr₀_top : r₀ ≠ ⊤)
    (hJ : MemWkpLoc p Ω 1 J) (hJi : MemLpLoc ∞ Ω J)
    (hc : IsSobolevCRCoefficients p Ω J DJ S)
    (hJsq : ∀ᵐ z ∂volume.restrict Ω, (J z).comp (J z) = -ContinuousLinearMap.id ℝ V)
    (hDJI : MemLpLoc p Ω (fun z => DJ z I))
    (hSξ_r₀ : MemLpLoc r₀ Ω (fun z => S z (ξ z)))
    (hDJIξ_r₀ : MemLpLoc r₀ Ω (fun z => DJ z I (ξ z)))
    (hsol : IsWeakCRSolution q Ω J DJ S ξ η) (hη : MemLpLoc r₀ Ω η)
    (ψ : 𝓓(Ω, ℝ)) (v : V) :
    (∫ z, (∂_{(1 : ℂ)} (∂_{(I : ℂ)} ψ) : 𝓓(Ω, ℝ)) z * ⟪v, J z (ξ z)⟫_ℝ) +
      (∫ z, (∂_{(I : ℂ)} ψ : 𝓓(Ω, ℝ)) z * ⟪v, DJ z 1 (ξ z)⟫_ℝ) -
      (∫ z, (∂_{(I : ℂ)} (∂_{(I : ℂ)} ψ) : 𝓓(Ω, ℝ)) z * ⟪v, ξ z⟫_ℝ) -
      (∫ z, (∂_{(I : ℂ)} ψ : 𝓓(Ω, ℝ)) z * ⟪v, J z (S z (ξ z))⟫_ℝ) =
      -∫ z, (∂_{(I : ℂ)} ψ : 𝓓(Ω, ℝ)) z * ⟪v, J z (η z)⟫_ℝ := by
  have hξq : MemLpLoc q Ω ξ := hsol.memLpLoc
  have hJξq : MemLpLoc q Ω (fun z => J z (ξ z)) := hJi.clm_apply hξq (by simp)
  have hloc := Ω.isOpen.isLocallyClosed
  let ψt : 𝓓(Ω, ℝ) := ∂_{(I : ℂ)} ψ
  obtain ⟨Ψ, hderiv, hval⟩ :=
    exists_testFunction_tendsto_integral_inner_of_hasWeakFDerivOn hp hp_top hpq hJ
      hc.hasWeakFDerivOn ψt v
  have hlim_lhs := (((hderiv 1 hξq).neg.sub (hderiv I hJξq)).sub
    (hval hr₀_gt hr₀_top hDJIξ_r₀)).add (hval hr₀_gt hr₀_top hSξ_r₀)
  have hlhs_eq (n : ℕ) :=
    (hc.integral_inner_crFormalAdjoint_eq_terms hpq.le hξq (Ψ n)).symm.trans
      (hsol.integral_inner_crFormalAdjoint (Ψ n))
  have heq₂ := tendsto_nhds_unique (hlim_lhs.congr hlhs_eq) (hval hr₀_gt hr₀_top hη)
  have hJJ_eq : ∫ z, (∂_{(I : ℂ)} ψt : 𝓓(Ω, ℝ)) z * ⟪v, J z (J z (ξ z))⟫_ℝ =
      -∫ z, (∂_{(I : ℂ)} ψt : 𝓓(Ω, ℝ)) z * ⟪v, ξ z⟫_ℝ := by
    rw [← integral_neg]
    refine integral_congr_ae ?_
    filter_upwards [ae_imp_of_ae_restrict hJsq] with z hz
    by_cases hzΩ : z ∈ (Ω : Set ℂ)
    · have hJz : J z (J z (ξ z)) = -ξ z := by simpa using congr($(hz hzΩ) (ξ z))
      rw [hJz, inner_neg_right, mul_neg]
    · simp [image_eq_zero_of_notMem_tsupport
        fun h => hzΩ ((∂_{(I : ℂ)} ψt : 𝓓(Ω, ℝ)).tsupport_subset h)]
  have hDJI_cancel : (∫ z, (ψt : ℂ → ℝ) z * ⟪v, DJ z I (J z (ξ z))⟫_ℝ) +
      ∫ z, (ψt : ℂ → ℝ) z * ⟪v, J z (DJ z I (ξ z))⟫_ℝ = 0 := by
    have hiA := ψt.integrable_mul_inner
      ((hDJI.clm_apply (r := (p⁻¹ + q⁻¹)⁻¹) hJξq (by simp)).locallyIntegrableOn
        (ENNReal.one_le_inv.2 hpq.le) hloc) v
    have hiB := ψt.integrable_mul_inner
      ((hJi.clm_apply hDJIξ_r₀ (by simp)).locallyIntegrableOn hr₀_gt.le hloc) v
    rw [← integral_add hiA hiB]
    refine integral_eq_zero_of_ae ?_
    filter_upwards [ae_imp_of_ae_restrict
      (hc.hasWeakFDerivOn.ae_apply_add_apply_eq_zero_of_comp_self_eq_neg_id hp hJ hJsq I)] with z hz
    simp only [Pi.zero_apply]
    by_cases hzΩ : z ∈ (Ω : Set ℂ)
    · rw [← mul_add, ← inner_add_right, hz hzΩ (ξ z), inner_zero_right, mul_zero]
    · simp [image_eq_zero_of_notMem_tsupport fun h => hzΩ (ψt.tsupport_subset h)]
  linarith

omit [FiniteDimensional ℝ V] in
/-- Linearity helper splitting `∫ ⟪v, α • (w₁ - w₂ + w₃)⟫` into three scalar-test-function inner
integrals when `w₁, w₂, w₃ ∈ L^{r₀}_loc(Ω)`. -/
private theorem integral_inner_smul_sub_add {r₀ : ℝ≥0∞} (hr₀ : 1 ≤ r₀) (α : 𝓓(Ω, ℝ)) (v : V)
    {w₁ w₂ w₃ : ℂ → V} (h₁ : MemLpLoc r₀ Ω w₁) (h₂ : MemLpLoc r₀ Ω w₂) (h₃ : MemLpLoc r₀ Ω w₃) :
    ∫ z, ⟪v, (α : ℂ → ℝ) z • (w₁ z - w₂ z + w₃ z)⟫_ℝ =
      (∫ z, (α : ℂ → ℝ) z * ⟪v, w₁ z⟫_ℝ) - (∫ z, (α : ℂ → ℝ) z * ⟪v, w₂ z⟫_ℝ) +
        ∫ z, (α : ℂ → ℝ) z * ⟪v, w₃ z⟫_ℝ := by
  have hloc := Ω.isOpen.isLocallyClosed
  have mk {w : ℂ → V} (hw : MemLpLoc r₀ Ω w) :=
    α.integrable_mul_inner (hw.locallyIntegrableOn hr₀ hloc) v
  have h12 : Integrable (fun z =>
      (α : ℂ → ℝ) z * ⟪v, w₁ z⟫_ℝ - (α : ℂ → ℝ) z * ⟪v, w₂ z⟫_ℝ) := (mk h₁).sub (mk h₂)
  have hcongr : (fun z => ⟪v, (α : ℂ → ℝ) z • (w₁ z - w₂ z + w₃ z)⟫_ℝ) =
      fun z => ((α : ℂ → ℝ) z * ⟪v, w₁ z⟫_ℝ - (α : ℂ → ℝ) z * ⟪v, w₂ z⟫_ℝ) +
        (α : ℂ → ℝ) z * ⟪v, w₃ z⟫_ℝ := by
    ext z; simp only [inner_smul_right, inner_add_right, inner_sub_right]; ring
  rw [hcongr, integral_add h12 (mk h₃), integral_sub (mk h₁) (mk h₂)]

/-- **Reduction of the weak Cauchy–Riemann equation to divergence-form Laplace.** Let `2 < p < ∞`
and `1/p + 1/q < 1`, let `J ∈ W^{1,p}_loc(Ω)` satisfy `J² = -1` almost everywhere on `Ω` with weak
derivative `DJ`, let `S ∈ Lᵖ_loc(Ω)`, and let `ξ` solve `∂_s ξ + J ∂_t ξ + S ξ = η` weakly on `Ω`
with `η ∈ Lᵗ_loc(Ω)` for some `t > 1`. Then for every real test function `ψ` on `Ω`,

`∫ Δψ • ξ = -∫ (∂_s ψ • (η - S ξ + (∂_t J) ξ) + ∂_t ψ • (-J η + J S ξ - (∂_s J) ξ))`. -/
theorem integral_laplacian_smul_eq (hp : 2 < p) (hp_top : p ≠ ⊤) (hpq : p⁻¹ + q⁻¹ < 1)
    {t : ℝ≥0∞} (ht : 1 < t)
    (hJ : MemWkpLoc p Ω 1 J) (hDJ : HasWeakFDerivOn volume Ω J DJ)
    (hJsq : ∀ᵐ z ∂volume.restrict Ω, (J z).comp (J z) = -ContinuousLinearMap.id ℝ V)
    (hS : MemLpLoc p Ω S) (hsol : IsWeakCRSolution q Ω J DJ S ξ η) (hη : MemLpLoc t Ω η)
    (ψ : 𝓓(Ω, ℝ)) :
    ∫ z, Δ (ψ : ℂ → ℝ) z • ξ z =
      -∫ z, (fderiv ℝ (ψ : ℂ → ℝ) z 1 • (η z - S z (ξ z) + DJ z I (ξ z)) +
        fderiv ℝ (ψ : ℂ → ℝ) z I • (-J z (η z) + J z (S z (ξ z)) - DJ z 1 (ξ z))) := by
  -- Choose a finite common exponent `r₀ > 1` into which `η`, `S ξ`, and `(DJ · u) ξ` all map.
  set q₁ : ℝ≥0∞ := min q p
  have hpq₁ : p⁻¹ + q₁⁻¹ < 1 := ENNReal.inv_add_inv_min_lt_one hp hpq
  set r₀ : ℝ≥0∞ := min t (min 2 (p⁻¹ + q₁⁻¹)⁻¹)
  have hr₀_gt : 1 < r₀ :=
    lt_min ht (lt_min (by exact_mod_cast one_lt_two) (by simpa using ENNReal.inv_lt_inv.2 hpq₁))
  have hr₀_top : r₀ ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofNat_ne_top
    ((min_le_right _ _).trans (min_le_left _ _))
  have hr₀_le : r₀ ≤ (p⁻¹ + q₁⁻¹)⁻¹ := (min_le_right _ _).trans (min_le_right _ _)
  have hpq₁_r₀ : p⁻¹ + q₁⁻¹ ≤ r₀⁻¹ := by simpa only [inv_inv] using ENNReal.inv_le_inv.2 hr₀_le
  have hsol₁ : IsWeakCRSolution q₁ Ω J DJ S ξ η := hsol.mono_exponent (min_le_left q p)
  have hξq₁ : MemLpLoc q₁ Ω ξ := hsol₁.memLpLoc
  have hJi : MemLpLoc ∞ Ω J := hJ.memLpLoc_top hp
  have hDJp : MemLpLoc p Ω DJ := hJ.memLpLoc_of_hasWeakFDerivOn hDJ
  have hc : IsSobolevCRCoefficients p Ω J DJ S := ⟨hDJ, hJ.memLpLoc, hDJp, hS⟩
  have hDJ1 : MemLpLoc p Ω (fun z => DJ z 1) :=
    hDJp.clm_comp (ContinuousLinearMap.apply ℝ (V →L[ℝ] V) 1)
  have hDJI : MemLpLoc p Ω (fun z => DJ z I) :=
    hDJp.clm_comp (ContinuousLinearMap.apply ℝ (V →L[ℝ] V) I)
  have hη_r₀ : MemLpLoc r₀ Ω η := hη.mono_exponent (min_le_left _ _)
  have hSξ_r₀ := hS.clm_apply hξq₁ hpq₁_r₀
  have hDJIξ_r₀ := hDJI.clm_apply hξq₁ hpq₁_r₀
  have hDJ1ξ_r₀ := hDJ1.clm_apply hξq₁ hpq₁_r₀
  have hJ_r₀ {w : ℂ → V} (hw : MemLpLoc r₀ Ω w) : MemLpLoc r₀ Ω (fun z => J z (w z)) :=
    hJi.clm_apply hw (by simp)
  -- Local integrability of the divergence-form right-hand sides `f` and `g`, and expansion of `Δψ`.
  set f : ℂ → V := fun z => η z - S z (ξ z) + DJ z I (ξ z)
  set g : ℂ → V := fun z => -J z (η z) + J z (S z (ξ z)) - DJ z 1 (ξ z)
  have hloc := Ω.isOpen.isLocallyClosed
  have hf_loc : LocallyIntegrableOn f Ω :=
    ((hη_r₀.sub hSξ_r₀).add hDJIξ_r₀).locallyIntegrableOn hr₀_gt.le hloc
  have hg_loc : LocallyIntegrableOn g Ω :=
    (((hJ_r₀ hη_r₀).neg.add (hJ_r₀ hSξ_r₀)).sub hDJ1ξ_r₀).locallyIntegrableOn hr₀_gt.le hloc
  have hξ_loc := hξq₁.locallyIntegrableOn (ENNReal.inv_le_one.1 (le_add_self.trans hpq₁.le)) hloc
  let ψs : 𝓓(Ω, ℝ) := ∂_{(1 : ℂ)} ψ
  let ψt : 𝓓(Ω, ℝ) := ∂_{(I : ℂ)} ψ
  let ψss : 𝓓(Ω, ℝ) := ∂_{(1 : ℂ)} ψs
  let ψtt : 𝓓(Ω, ℝ) := ∂_{(I : ℂ)} ψt
  have hψs_coe (z : ℂ) : (ψs : ℂ → ℝ) z = fderiv ℝ (ψ : ℂ → ℝ) z 1 :=
    TestFunction.lineDerivOp_apply_eq_fderiv ψ 1 z
  have hψt_coe (z : ℂ) : (ψt : ℂ → ℝ) z = fderiv ℝ (ψ : ℂ → ℝ) z I :=
    TestFunction.lineDerivOp_apply_eq_fderiv ψ I z
  have hΔ_coe (z : ℂ) : Δ (ψ : ℂ → ℝ) z = (ψss : ℂ → ℝ) z + (ψtt : ℂ → ℝ) z := by
    rw [← TestFunction.laplacianCLM_apply]
    simp [ψss, ψtt, ψs, ψt, laplacianCLM_eq_sum Complex.orthonormalBasisOneI, Fin.sum_univ_two]
  have hint_lhs : Integrable (fun z => Δ (ψ : ℂ → ℝ) z • ξ z) :=
    ((ψss.integrable_smul hξ_loc).add (ψtt.integrable_smul hξ_loc)).congr
      (.of_forall fun z => by simp [hΔ_coe, add_smul])
  have hint_rhs : Integrable (fun z =>
      fderiv ℝ (ψ : ℂ → ℝ) z 1 • f z + fderiv ℝ (ψ : ℂ → ℝ) z I • g z) :=
    (integrable_fderiv_smul_of_locallyIntegrableOn hf_loc ψ 1).add
      (integrable_fderiv_smul_of_locallyIntegrableOn hg_loc ψ I)
  -- Test against each vector `v ∈ V` by combining the `(∂_s ψ) • v` and `-(∂_t ψ) • J_nᵀ v`
  -- identities; the mixed `∂_s ∂_t ψ` integrals cancel.
  refine ext_inner_left ℝ fun v => ?_
  rw [← integral_inner hint_lhs v, inner_neg_right, ← integral_inner hint_rhs v]
  have heq₁ := hsol₁.integral_test_lineDeriv_one hpq₁.le hc ψ v
  have heq₂ := hsol₁.integral_test_mollified_adjoint hp hp_top hpq₁ hr₀_gt hr₀_top
    hJ hJi hc hJsq hDJI hSξ_r₀ hDJIξ_r₀ hη_r₀ ψ v
  have hΔ_int : ∫ z, ⟪v, Δ (ψ : ℂ → ℝ) z • ξ z⟫_ℝ =
      (∫ z, (ψss : ℂ → ℝ) z * ⟪v, ξ z⟫_ℝ) + ∫ z, (ψtt : ℂ → ℝ) z * ⟪v, ξ z⟫_ℝ := by
    rw [← integral_add (ψss.integrable_mul_inner hξ_loc v) (ψtt.integrable_mul_inner hξ_loc v)]
    exact integral_congr_ae (.of_forall fun z => by
      dsimp only; rw [hΔ_coe z, inner_smul_right, add_mul])
  have hfg_int : ∫ z, ⟪v, fderiv ℝ (ψ : ℂ → ℝ) z 1 • f z + fderiv ℝ (ψ : ℂ → ℝ) z I • g z⟫_ℝ =
      ((∫ z, (ψs : ℂ → ℝ) z * ⟪v, η z⟫_ℝ) - (∫ z, (ψs : ℂ → ℝ) z * ⟪v, S z (ξ z)⟫_ℝ) +
        (∫ z, (ψs : ℂ → ℝ) z * ⟪v, DJ z I (ξ z)⟫_ℝ)) +
      ((∫ z, (ψt : ℂ → ℝ) z * ⟪v, J z (S z (ξ z))⟫_ℝ) -
        (∫ z, (ψt : ℂ → ℝ) z * ⟪v, J z (η z)⟫_ℝ) +
        (-∫ z, (ψt : ℂ → ℝ) z * ⟪v, DJ z 1 (ξ z)⟫_ℝ)) := by
    have hg_eq (z : ℂ) : g z = J z (S z (ξ z)) - J z (η z) + -DJ z 1 (ξ z) := by dsimp [g]; abel
    have h1 : Integrable (fun z => ⟪v, fderiv ℝ (ψ : ℂ → ℝ) z 1 • f z⟫_ℝ) :=
      (innerSL ℝ v).integrable_comp (integrable_fderiv_smul_of_locallyIntegrableOn hf_loc ψ 1)
    have h2 : Integrable (fun z => ⟪v, fderiv ℝ (ψ : ℂ → ℝ) z I • g z⟫_ℝ) :=
      (innerSL ℝ v).integrable_comp (integrable_fderiv_smul_of_locallyIntegrableOn hg_loc ψ I)
    simp only [inner_add_right]
    rw [integral_add h1 h2]
    simp only [← hψs_coe, ← hψt_coe, hg_eq]
    rw [integral_inner_smul_sub_add hr₀_gt.le ψs v hη_r₀ hSξ_r₀ hDJIξ_r₀,
      integral_inner_smul_sub_add (w₃ := fun z => -DJ z 1 (ξ z)) hr₀_gt.le ψt v
        (hJ_r₀ hSξ_r₀) (hJ_r₀ hη_r₀) hDJ1ξ_r₀.neg]
    simp only [inner_neg_right, mul_neg, integral_neg]
  rw [hΔ_int, hfg_int]
  linarith

/-! ### Single Hölder step and order-zero Sobolev iteration -/

/-- **Single Hölder step at order zero** (McDuff–Salamon, Lemma B.4.6). If `2 < p < ∞`,
`1 < r < ∞`, `1/p + 1/q ≤ 1/r`, `J ∈ W^{1,p}_loc(Ω)` satisfies `J² = -1` almost everywhere on `Ω`
with weak derivative `DJ`, `S ∈ Lᵖ_loc(Ω)`, `ξ` solves `∂_s ξ + J ∂_t ξ + S ξ = η` weakly in
`L^q_loc(Ω)`, and `η ∈ Lʳ_loc(Ω)`, then `ξ ∈ W^{1,r}_loc(Ω)`. The exponent `q = ∞` is included. -/
theorem memWkpLoc_one_of_inv_add_inv_le (hp : 2 < p) (hp_top : p ≠ ⊤) (hr : 1 < r)
    (hr_top : r ≠ ⊤) (hpqr : p⁻¹ + q⁻¹ ≤ r⁻¹)
    (hJ : MemWkpLoc p Ω 1 J) (hDJ : HasWeakFDerivOn volume Ω J DJ)
    (hJsq : ∀ᵐ z ∂volume.restrict Ω, (J z).comp (J z) = -ContinuousLinearMap.id ℝ V)
    (hS : MemLpLoc p Ω S) (hsol : IsWeakCRSolution q Ω J DJ S ξ η) (hη : MemLpLoc r Ω η) :
    MemWkpLoc r Ω 1 ξ := by
  have hpq : p⁻¹ + q⁻¹ < 1 := hpqr.trans_lt (by simpa using ENNReal.inv_lt_inv.2 hr)
  have hJi : MemLpLoc ∞ Ω J := hJ.memLpLoc_top hp
  have hDJp : MemLpLoc p Ω DJ := hJ.memLpLoc_of_hasWeakFDerivOn hDJ
  have hSξ := hS.clm_apply hsol.memLpLoc hpqr
  have hDJIξ := (hDJp.clm_comp (ContinuousLinearMap.apply ℝ (V →L[ℝ] V) I)).clm_apply
    hsol.memLpLoc hpqr
  have hDJ1ξ := (hDJp.clm_comp (ContinuousLinearMap.apply ℝ (V →L[ℝ] V) 1)).clm_apply
    hsol.memLpLoc hpqr
  have hf := (hη.sub hSξ).add hDJIξ
  have hg := ((hJi.clm_apply hη (by simp)).neg.add (hJi.clm_apply hSξ (by simp))).sub hDJ1ξ
  have hξ_loc := hsol.memLpLoc.locallyIntegrableOn
    (ENNReal.inv_le_one.1 (le_add_self.trans hpq.le)) Ω.isOpen.isLocallyClosed
  exact memWkpLoc_one_of_forall_integral_laplacian_smul_eq hr hr_top hξ_loc hf hg
    (hsol.integral_laplacian_smul_eq hp hp_top hpq hr hJ hDJ hJsq hS hη)

/-- Once `ξ` reaches `W^{1,r}_loc` for some `r > 2`, the `L^∞` Sobolev embedding puts `ξ` in
`L^∞_loc`, and one more application of `memWkpLoc_one_of_inv_add_inv_le` reaches `W^{1,s}_loc`. -/
private theorem memWkpLoc_one_of_two_lt (hr : 2 < r) (hp : 2 < p) (hp_top : p ≠ ⊤)
    (hs1 : 1 < s) (hsp : s ≤ p)
    (hJ : MemWkpLoc p Ω 1 J) (hDJ : HasWeakFDerivOn volume Ω J DJ)
    (hJsq : ∀ᵐ z ∂volume.restrict Ω, (J z).comp (J z) = -ContinuousLinearMap.id ℝ V)
    (hS : MemLpLoc p Ω S) (hsol : IsWeakCRSolution q Ω J DJ S ξ η) (hη : MemLpLoc s Ω η)
    (hξr : MemWkpLoc r Ω 1 ξ) : MemWkpLoc s Ω 1 ξ :=
  (hsol.of_memLpLoc (hξr.memLpLoc_top hr)).memWkpLoc_one_of_inv_add_inv_le hp hp_top hs1
    (ne_top_of_le_ne_top hp_top hsp) (by simpa using ENNReal.inv_le_inv.2 hsp) hJ hDJ hJsq hS hη

/-- Subcritical step (`1 < r₁ < 2`) of the order-zero ladder: for `1/r₁ = 1/p + 1/t`, the critical
two-dimensional Sobolev embedding `W^{1,r₁}_loc ⊂ L^{t'}_loc` decreases `1/t` by `1/2 - 1/p`. -/
private theorem memWkpLoc_one_subcritical_step {p t r₁ : ℝ≥0} (hp_inv : (p : ℝ)⁻¹ < 2⁻¹)
    (hpt : (p : ℝ)⁻¹ + (t : ℝ)⁻¹ < 1)
    (hr₁_coe : (r₁ : ℝ) = ((p : ℝ)⁻¹ + (t : ℝ)⁻¹)⁻¹) (hr₁_gt1 : 1 < (r₁ : ℝ))
    (hlt2 : (r₁ : ℝ) < 2) (hsolt : IsWeakCRSolution t Ω J DJ S ξ η)
    (hξ_r₁ : MemWkpLoc r₁ Ω 1 ξ) :
    ∃ t' : ℝ≥0, (0 : ℝ) < t' ∧ (p : ℝ)⁻¹ + (t' : ℝ)⁻¹ < 1 ∧
      (t' : ℝ)⁻¹ = (t : ℝ)⁻¹ - (2⁻¹ - (p : ℝ)⁻¹) ∧ IsWeakCRSolution t' Ω J DJ S ξ η := by
  have hr₁_pos : (0 : ℝ) < r₁ := zero_lt_one.trans hr₁_gt1
  set b' : ℝ := (r₁ : ℝ)⁻¹ - 2⁻¹
  have hb'_pos : 0 < b' := sub_pos.2 ((inv_lt_inv₀ zero_lt_two hr₁_pos).2 hlt2)
  have hb'_eq : b' = (t : ℝ)⁻¹ - (2⁻¹ - (p : ℝ)⁻¹) := by
    dsimp only [b']; rw [hr₁_coe, inv_inv]; ring
  let t' : ℝ≥0 := ⟨b'⁻¹, by positivity⟩
  have ht'_coe : (t' : ℝ) = b'⁻¹ := NNReal.coe_mk b'⁻¹ (by positivity)
  have ht'_pos : (0 : ℝ) < t' := by rw [ht'_coe]; positivity
  have ht'_inv : (t' : ℝ)⁻¹ = b' := by rw [ht'_coe, inv_inv]
  have hr₁_le_t' : r₁ ≤ t' := by
    rw [← NNReal.coe_le_coe]
    exact (inv_le_inv₀ ht'_pos hr₁_pos).1 (by rw [ht'_inv]; dsimp [b']; linarith)
  have hξ_t' : MemLpLoc t' Ω ξ :=
    hξ_r₁.memLpLoc_of_inv_sub_inv_le (by exact_mod_cast hr₁_gt1.le) hr₁_le_t'
      (by rw [ht'_inv]; dsimp [b']; linarith)
  refine ⟨t', ht'_pos, ?_, ht'_inv.trans hb'_eq, hsolt.of_memLpLoc hξ_t'⟩
  rw [ht'_inv, hb'_eq]; linarith

/-- Critical case (`r₁ = 2`) of the order-zero ladder: `W^{1,2}_loc` embeds into every finite
`L^{t*}_loc`; choosing `1/t* = (1/2 - 1/p) / 2` makes the next product exponent exceed `2`, where
`memWkpLoc_one_of_two_lt` finishes. -/
private theorem memWkpLoc_one_critical_case {p s r₁ : ℝ≥0} (hp : 2 < (p : ℝ≥0∞))
    (hs1 : 1 < (s : ℝ≥0∞)) (hsp : (s : ℝ≥0∞) ≤ p) (hrs : (r₁ : ℝ) < s) (heq2 : (r₁ : ℝ) = 2)
    (hJ : MemWkpLoc p Ω 1 J) (hDJ : HasWeakFDerivOn volume Ω J DJ)
    (hJsq : ∀ᵐ z ∂volume.restrict Ω, (J z).comp (J z) = -ContinuousLinearMap.id ℝ V)
    (hS : MemLpLoc p Ω S) (hsol : IsWeakCRSolution q Ω J DJ S ξ η) (hη : MemLpLoc s Ω η)
    (hξ_r₁ : MemWkpLoc r₁ Ω 1 ξ) : MemWkpLoc s Ω 1 ξ := by
  have hpR : (2 : ℝ) < p := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < p := by linarith
  have hp_inv : (p : ℝ)⁻¹ < 2⁻¹ := (inv_lt_inv₀ hp0 zero_lt_two).2 hpR
  set a : ℝ := 2⁻¹ - (p : ℝ)⁻¹
  have ha : 0 < a := sub_pos.2 hp_inv
  let t_star : ℝ≥0 := ⟨(a / 2)⁻¹, by positivity⟩
  have ht_star_coe : (t_star : ℝ) = (a / 2)⁻¹ := NNReal.coe_mk (a / 2)⁻¹ (by positivity)
  have ht_star_pos : (0 : ℝ) < t_star := by rw [ht_star_coe]; positivity
  have ht_star_inv : (t_star : ℝ)⁻¹ = a / 2 := by rw [ht_star_coe, inv_inv]
  have hr₁_le_star : r₁ ≤ t_star := by
    rw [← NNReal.coe_le_coe, heq2]
    exact (inv_le_inv₀ ht_star_pos zero_lt_two).1
      (by rw [ht_star_inv]; dsimp [a]; linarith [inv_pos.2 hp0])
  have hξ_star : MemLpLoc t_star Ω ξ :=
    hξ_r₁.memLpLoc_of_inv_sub_inv_le (by rw [← NNReal.coe_le_coe, heq2]; norm_num) hr₁_le_star
      (by rw [heq2, ht_star_inv]; linarith)
  set r₂_real : ℝ := min (s : ℝ) ((p : ℝ)⁻¹ + a / 2)⁻¹
  have hr₂_gt2 : 2 < r₂_real := lt_min (heq2 ▸ hrs)
    ((lt_inv_comm₀ zero_lt_two (by positivity)).2 (by dsimp [a]; linarith [hp_inv]))
  let r₂ : ℝ≥0 := ⟨r₂_real, by positivity⟩
  have hr₂_coe : (r₂ : ℝ) = r₂_real := NNReal.coe_mk r₂_real (by positivity)
  have hr₂_pos : (0 : ℝ) < r₂ := by rw [hr₂_coe]; positivity
  have hpqr₂ : (p : ℝ≥0∞)⁻¹ + (t_star : ℝ≥0∞)⁻¹ ≤ (r₂ : ℝ≥0∞)⁻¹ :=
    (ENNReal.coe_inv_add_inv_le_inv_iff (by exact_mod_cast hp0.ne')
      (by exact_mod_cast ht_star_pos.ne') (by exact_mod_cast hr₂_pos.ne')).2 <| by
        rw [ht_star_inv, hr₂_coe]
        exact (le_inv_comm₀ (by positivity) (by positivity)).2 (min_le_right _ _)
  have hξ_r₂ : MemWkpLoc r₂ Ω 1 ξ :=
    (hsol.of_memLpLoc hξ_star).memWkpLoc_one_of_inv_add_inv_le hp ENNReal.coe_ne_top
      (by
        rw [← ENNReal.coe_one, ENNReal.coe_lt_coe, ← NNReal.coe_lt_coe, NNReal.coe_one, hr₂_coe]
        linarith)
      ENNReal.coe_ne_top hpqr₂ hJ hDJ hJsq hS
      (hη.mono_exponent
        (by rw [ENNReal.coe_le_coe, ← NNReal.coe_le_coe, hr₂_coe]; exact min_le_left _ _))
  exact memWkpLoc_one_of_two_lt
    (by rw [← ENNReal.coe_ofNat, ENNReal.coe_lt_coe, ← NNReal.coe_lt_coe, hr₂_coe]; exact hr₂_gt2)
    hp ENNReal.coe_ne_top hs1 hsp hJ hDJ hJsq hS hsol hη hξ_r₂

/-- **Order-zero interior regularity** (McDuff–Salamon, Lemma B.4.6). Let `2 < p < ∞`,
`1/p + 1/q < 1` and `1 < s ≤ p`. If `J ∈ W^{1,p}_loc(Ω)` satisfies `J² = -1` almost everywhere on
`Ω` with weak derivative `DJ`, `S ∈ Lᵖ_loc(Ω)`, `ξ` solves `∂_s ξ + J ∂_t ξ + S ξ = η` weakly in
`L^q_loc(Ω)`, and `η ∈ Lˢ_loc(Ω)`, then `ξ ∈ W^{1,s}_loc(Ω)`. -/
theorem memWkpLoc_one_of_memLpLoc (hp : 2 < p) (hp_top : p ≠ ⊤) (hpq : p⁻¹ + q⁻¹ < 1)
    (hs1 : 1 < s) (hsp : s ≤ p)
    (hJ : MemWkpLoc p Ω 1 J) (hDJ : HasWeakFDerivOn volume Ω J DJ)
    (hJsq : ∀ᵐ z ∂volume.restrict Ω, (J z).comp (J z) = -ContinuousLinearMap.id ℝ V)
    (hS : MemLpLoc p Ω S) (hsol : IsWeakCRSolution q Ω J DJ S ξ η) (hη : MemLpLoc s Ω η) :
    MemWkpLoc s Ω 1 ξ := by
  have hs_top : s ≠ ⊤ := ne_top_of_le_ne_top hp_top hsp
  have hq₀_top : min q p ≠ ⊤ := ne_top_of_le_ne_top hp_top (min_le_right q p)
  have hsol₀ : IsWeakCRSolution (min q p) Ω J DJ S ξ η := hsol.mono_exponent (min_le_left q p)
  have hpq₀ : p⁻¹ + (min q p)⁻¹ < 1 := ENNReal.inv_add_inv_min_lt_one hp hpq
  generalize hq₀_def : min q p = q₀
  rw [hq₀_def] at hq₀_top hsol₀ hpq₀
  lift q₀ to ℝ≥0 using hq₀_top
  lift p to ℝ≥0 using hp_top
  lift s to ℝ≥0 using hs_top
  have hpR : (2 : ℝ) < p := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < p := by linarith
  have hp_inv : (p : ℝ)⁻¹ < 2⁻¹ := (inv_lt_inv₀ hp0 zero_lt_two).2 hpR
  have hs1R : (1 : ℝ) < s := by exact_mod_cast hs1
  have hq₀_pos : (0 : ℝ) < q₀ := by
    by_contra hle
    simp [NNReal.coe_eq_zero.1 (le_antisymm (not_lt.1 hle) q₀.coe_nonneg)] at hpq₀
  have hpq₀R : (p : ℝ)⁻¹ + (q₀ : ℝ)⁻¹ < 1 :=
    (ENNReal.coe_inv_add_inv_lt_one_iff (by exact_mod_cast hp0.ne')
      (by exact_mod_cast hq₀_pos.ne')).1 hpq₀
  set a : ℝ := 2⁻¹ - (p : ℝ)⁻¹
  have ha : 0 < a := sub_pos.2 hp_inv
  suffices ∀ (n : ℕ) (t : ℝ≥0), (0 : ℝ) < t → (p : ℝ)⁻¹ + (t : ℝ)⁻¹ < 1 →
      (t : ℝ)⁻¹ ≤ n * a → IsWeakCRSolution t Ω J DJ S ξ η → MemWkpLoc s Ω 1 ξ from
    this ⌈(q₀ : ℝ)⁻¹ / a⌉₊ q₀ hq₀_pos hpq₀R ((div_le_iff₀ ha).1 (Nat.le_ceil _)) hsol₀
  intro n
  induction n with
  | zero => intro t ht0 _ htn _; linarith [inv_pos.2 ht0]
  | succ n ih =>
    intro t ht0 hpt htn hsolt
    set r_prod : ℝ := ((p : ℝ)⁻¹ + (t : ℝ)⁻¹)⁻¹
    have hr_prod_gt : 1 < r_prod := (one_lt_inv₀ (by positivity)).2 hpt
    rcases le_or_gt (s : ℝ) r_prod with hsr | hrs
    · exact hsolt.memWkpLoc_one_of_inv_add_inv_le hp ENNReal.coe_ne_top hs1 ENNReal.coe_ne_top
        ((ENNReal.coe_inv_add_inv_le_inv_iff (by exact_mod_cast hp0.ne')
          (by exact_mod_cast ht0.ne') (by exact_mod_cast (zero_lt_one.trans hs1R).ne')).2
            ((le_inv_comm₀ (by positivity) (zero_lt_one.trans hs1R)).2 hsr))
        hJ hDJ hJsq hS hη
    · let r₁ : ℝ≥0 := ⟨r_prod, by positivity⟩
      have hr₁_coe : (r₁ : ℝ) = r_prod := NNReal.coe_mk r_prod (by positivity)
      have hr₁_pos : (0 : ℝ) < r₁ := by rw [hr₁_coe]; positivity
      have hξ_r₁ : MemWkpLoc r₁ Ω 1 ξ :=
        hsolt.memWkpLoc_one_of_inv_add_inv_le hp ENNReal.coe_ne_top
          (by
            rw [← ENNReal.coe_one, ENNReal.coe_lt_coe, ← NNReal.coe_lt_coe, NNReal.coe_one, hr₁_coe]
            exact hr_prod_gt)
          ENNReal.coe_ne_top
          ((ENNReal.coe_inv_add_inv_le_inv_iff (by exact_mod_cast hp0.ne')
            (by exact_mod_cast ht0.ne') (by exact_mod_cast hr₁_pos.ne')).2
              (by simp [hr₁_coe, r_prod]))
          hJ hDJ hJsq hS
          (hη.mono_exponent
            (by rw [ENNReal.coe_le_coe, ← NNReal.coe_le_coe, hr₁_coe]; exact hrs.le))
      rcases lt_trichotomy (r₁ : ℝ) 2 with hlt2 | heq2 | hgt2
      · obtain ⟨t', ht'0, hpt', ht'_eq, hsolt'⟩ :=
          memWkpLoc_one_subcritical_step hp_inv hpt hr₁_coe (hr₁_coe ▸ hr_prod_gt) hlt2 hsolt hξ_r₁
        refine ih t' ht'0 hpt' ?_ hsolt'
        have hstep : ((n + 1 : ℕ) : ℝ) * a = (n : ℝ) * a + (2⁻¹ - (p : ℝ)⁻¹) := by
          dsimp only [a]; push_cast; ring
        rw [ht'_eq]
        linarith [htn, hstep]
      · exact memWkpLoc_one_critical_case hp hs1 hsp (hr₁_coe ▸ hrs) heq2 hJ hDJ hJsq hS hsolt hη
          hξ_r₁
      · exact memWkpLoc_one_of_two_lt
          (by rw [← ENNReal.coe_ofNat, ENNReal.coe_lt_coe, ← NNReal.coe_lt_coe]; exact hgt2)
          hp ENNReal.coe_ne_top hs1 hsp hJ hDJ hJsq hS hsolt hη hξ_r₁

/-- **Order-zero interior regularity at the solution's exponent.** If `2 < p < ∞`,
`1/p + 1/q < 1`, `q ≤ p`, `J ∈ W^{1,p}_loc(Ω)` with `J² = -1` almost everywhere on `Ω`,
`S ∈ Lᵖ_loc(Ω)`, and `ξ` solves `∂_s ξ + J ∂_t ξ + S ξ = η` weakly in `L^q_loc(Ω)` with
`η ∈ L^q_loc(Ω)`, then `ξ ∈ W^{1,q}_loc(Ω)`. -/
theorem memWkpLoc_one_of_le (hp : 2 < p) (hp_top : p ≠ ⊤) (hpq : p⁻¹ + q⁻¹ < 1) (hqp : q ≤ p)
    (hJ : MemWkpLoc p Ω 1 J) (hDJ : HasWeakFDerivOn volume Ω J DJ)
    (hJsq : ∀ᵐ z ∂volume.restrict Ω, (J z).comp (J z) = -ContinuousLinearMap.id ℝ V)
    (hS : MemLpLoc p Ω S) (hsol : IsWeakCRSolution q Ω J DJ S ξ η) (hη : MemLpLoc q Ω η) :
    MemWkpLoc q Ω 1 ξ :=
  hsol.memWkpLoc_one_of_memLpLoc hp hp_top hpq
    (ENNReal.inv_lt_one.1 (lt_of_le_of_lt le_add_self hpq)) hqp hJ hDJ hJsq hS hη

/-- **Order-zero interior regularity at the coefficient exponent.** If `2 < p < ∞`,
`1/p + 1/q < 1`, `J ∈ W^{1,p}_loc(Ω)` with `J² = -1` almost everywhere on `Ω`, `S ∈ Lᵖ_loc(Ω)`,
and `ξ` solves `∂_s ξ + J ∂_t ξ + S ξ = η` weakly in `L^q_loc(Ω)` with `η ∈ Lᵖ_loc(Ω)`, then
`ξ ∈ W^{1,p}_loc(Ω)`. -/
theorem memWkpLoc_one (hp : 2 < p) (hp_top : p ≠ ⊤) (hpq : p⁻¹ + q⁻¹ < 1)
    (hJ : MemWkpLoc p Ω 1 J) (hDJ : HasWeakFDerivOn volume Ω J DJ)
    (hJsq : ∀ᵐ z ∂volume.restrict Ω, (J z).comp (J z) = -ContinuousLinearMap.id ℝ V)
    (hS : MemLpLoc p Ω S) (hsol : IsWeakCRSolution q Ω J DJ S ξ η) (hη : MemLpLoc p Ω η) :
    MemWkpLoc p Ω 1 ξ :=
  hsol.memWkpLoc_one_of_memLpLoc hp hp_top hpq
    ((by exact_mod_cast one_lt_two : (1 : ℝ≥0∞) < 2).trans hp) le_rfl hJ
    hDJ hJsq hS hη

end IsWeakCRSolution

end TauCeti
