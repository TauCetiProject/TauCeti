/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Wirtinger.TestBound
public import TauCeti.Analysis.Complex.Wirtinger.Weak
public import TauCeti.Analysis.Sobolev.Local.Norm
public import TauCeti.Analysis.Sobolev.TestFunctionLp.Representation
public import TauCeti.Analysis.Sobolev.WeakDeriv.Local
import TauCeti.Analysis.Complex.OperatorNorm
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# Interior regularity for the distributional Cauchy–Riemann equation

Let `F` be a finite-dimensional complex inner product space and `1 < p < ∞`. If `u : ℂ → F` is
locally `Lᵖ` on an open set `Ω` and its distributional derivative `\bar∂u` is locally `Lᵖ`, then
`u` lies in `W^{1,p}_loc(Ω)`. If `\bar∂u` lies in `W^{k,p}_loc(Ω)`, then `u` lies in
`W^{k+1,p}_loc(Ω)`. For every compact `K ⊆ Ω` the interior estimate
`‖u‖_{W^{k+1,p}(V)} ≤ C (‖\bar∂u‖_{W^{k,p}(Ω')} + ‖u‖_{Lᵖ(Ω')})` holds on an open
neighbourhood `V` of `K`, for an open `Ω'` containing `V` with compact closure in `Ω`. In the
first-order estimate for the derivative, the solution may instead be measured in any larger
exponent `r ≥ p`, including infinity. The `Lᵖ` norm of `u` cannot be dropped from the estimate:
the identity map solves `\bar∂u = 0` and has nonzero derivative.

The first-order statement combines two existing results. The interior test bound for the
distributional equation controls each directional distributional derivative by the conjugate
`Lᵠ` norm of the test function. The `Lᵖ` dual representation then turns each such bound into an
`Lᵖ` weak derivative, coordinatewise in a real basis of `F`. Local weak derivatives glue to a
weak derivative on `Ω`. The induction on the order, for both regularity and the estimate, uses
that a weak directional derivative of a solution solves the differentiated equation.

## Main results

* `HasWeakConjWirtingerDerivOn.weakLineDeriv`: a weak directional derivative of a solution solves
  the differentiated equation.
* `exists_hasWeakFDerivOn_eLpNorm_le_of_hasWeakConjWirtingerDerivOn_of_le`: the weak derivative
  exists near a compact set, with an `Lᵖ` bound, for an `Lʳ` solution on a fixed open set.
* `HasWeakConjWirtingerDerivOn.memWkpLoc_one`: local `W^{1,p}` regularity.
* `HasWeakConjWirtingerDerivOn.memWkpLoc_succ`: local `W^{k+1,p}` regularity for every `k`.
* `exists_eLpNorm_le_of_hasWeakConjWirtingerDerivOn_of_le` and
  `exists_eLpNorm_le_of_hasWeakConjWirtingerDerivOn`: the first-order interior estimate.
* `exists_eLpNormWkp_le_of_hasWeakConjWirtingerDerivOn`: the interior `W^{k+1,p}` estimate.
* `not_exists_eLpNorm_le_eLpNorm_conjWirtingerDeriv`: the estimate fails without the `Lᵖ` norm of
  the solution.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B.
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory TopologicalSpace ContinuousLinearMap Complex Set Filter LineDeriv
open scoped ContDiff Distributions ENNReal NNReal

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]
  {p : ℝ≥0∞}

/-- **Interior `W^{1,p}` estimate with a fixed outer domain.** For `1 < p < ∞`, an `Lʳ` solution
of `\bar∂u = f` on `U` with `f ∈ Lᵖ(U)` and `p ≤ r ≤ ∞` has a weak derivative on an open
neighbourhood `V` of a compact `K ⊆ U`, bounded in `Lᵖ(V)` by `‖f‖_{Lᵖ(U)} + ‖u‖_{Lʳ(U)}`.
The neighbourhood and the constant do not depend on `u` and `f`. -/
theorem exists_hasWeakFDerivOn_eLpNorm_le_of_hasWeakConjWirtingerDerivOn_of_le
    (hp : 1 < p) (hp_top : p ≠ ⊤) {r : ℝ≥0∞} (hpr : p ≤ r) {U : Opens ℂ} {K : Set ℂ}
    (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ V : Opens ℂ, K ⊆ V ∧ IsCompact (closure (V : Set ℂ)) ∧ closure (V : Set ℂ) ⊆ U ∧
      ∃ C : ℝ≥0, ∀ u f : ℂ → F, MemLp u r (volume.restrict U) →
        MemLp f p (volume.restrict U) → HasWeakConjWirtingerDerivOn volume U u f →
        ∃ D : ℂ → ℂ →L[ℝ] F, HasWeakFDerivOn volume V u D ∧
          eLpNorm D p (volume.restrict V) ≤
            C * (eLpNorm f p (volume.restrict U) + eLpNorm u r (volume.restrict U)) := by
  have := FiniteDimensional.complete ℂ F
  have : Fact (1 ≤ p) := ⟨hp.le⟩
  have : Fact (1 ≤ p.conjExponent) := ⟨ENNReal.HolderConjugate.one_le _ p⟩
  have hq : 1 < p.conjExponent :=
    (ENNReal.HolderConjugate.lt_top_iff_one_lt p _).1 hp_top.lt_top
  have hq_top : p.conjExponent ≠ ⊤ := ((ENNReal.HolderConjugate.lt_top_iff_one_lt _ p).2 hp).ne
  obtain ⟨V, hKV, hVc, hVU, C, hC⟩ :=
    exists_enorm_integral_lineDeriv_smul_le_of_integral_conjWirtingerDeriv_eq_of_le
      (F := F) (q := p.conjExponent) hp hp_top hpr hK hKU
  obtain ⟨C₀, hC₀⟩ := exists_eLpNorm_le_hasWeakLineDerivOn_of_enorm_integral_lineDeriv_smul_le
    (μ := volume) (Ω := V) (G := F) (p := p) hq hq_top
  refine ⟨V, hKV, hVc, hVU, 2 * (C₀ * C), fun u f hu hf h => ?_⟩
  set A := eLpNorm f p (volume.restrict U) + eLpNorm u r (volume.restrict U)
  have hA : (C : ℝ≥0∞) * A ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.coe_ne_top (ENNReal.add_ne_top.2 ⟨hf.eLpNorm_ne_top,
      hu.eLpNorm_ne_top⟩)
  have hUeq (φ : 𝓓(U, ℝ)) :
      (∫ z, lineDeriv ℝ (φ : ℂ → ℝ) z 1 • u z) +
        I • (∫ z, lineDeriv ℝ (φ : ℂ → ℝ) z I • u z) =
          -(2 : ℝ) • (∫ z, (φ : ℂ → ℝ) z • f z) := by
    -- The test bound states the equation with the real scalar `-2`; the weak predicate uses
    -- its complex cast, so the two agree by `Complex.coe_smul`.
    rw [h.integral_lineDeriv_smul_add_I_smul_eq_neg_two_smul_integral_smul φ,
      ← Complex.coe_smul]
    norm_num
  have hVU' : (V : Set ℂ) ⊆ U := subset_closure.trans hVU
  have hloc : LocallyIntegrableOn u V volume := h.locallyIntegrableOn.mono_set hVU'
  have hdir (v : ℂ) (hv : ‖v‖ₑ = 1) : ∃ g : ℂ → F, HasWeakLineDerivOn volume V u g v ∧
      eLpNorm g p (volume.restrict V) ≤ C₀ * (C * A) :=
    hC₀ u hloc v _ hA fun φ => (hC u f hu hf hUeq φ v).trans_eq (by rw [hv, mul_one])
  obtain ⟨g₁, hg₁, hg₁n⟩ := hdir 1 (by simp)
  obtain ⟨gI, hgI, hgIn⟩ := hdir I (by simp [enorm_eq_nnnorm])
  let D : ℂ → ℂ →L[ℝ] F := fun z => reCLM.smulRight (g₁ z) + imCLM.smulRight (gI z)
  have hD1 (z : ℂ) : D z 1 = g₁ z := by simp [D]
  have hDI (z : ℂ) : D z I = gI z := by simp [D]
  refine ⟨D, Complex.basisOneI.hasWeakFDerivOn_of_forall hloc fun i => ?_, ?_⟩
  · fin_cases i
    · simpa [hD1] using hg₁
    · simpa [hDI] using hgI
  · have hm₁ := hg₁.locallyIntegrableOn_deriv.aestronglyMeasurable
    have hmI := hgI.locallyIntegrableOn_deriv.aestronglyMeasurable
    have hmD : AEStronglyMeasurable D (volume.restrict V) :=
      ((smulRightL ℝ ℂ F reCLM).continuous.comp_aestronglyMeasurable hm₁).add
        ((smulRightL ℝ ℂ F imCLM).continuous.comp_aestronglyMeasurable hmI)
    calc eLpNorm D p (volume.restrict V)
        ≤ eLpNorm (fun z => ‖g₁ z‖ + ‖gI z‖) p (volume.restrict V) := by
          refine eLpNorm_mono_real hmD fun z => ?_
          refine (norm_add_le _ _).trans_eq ?_
          simp [norm_smulRight_apply]
      _ ≤ eLpNorm (fun z => ‖g₁ z‖) p (volume.restrict V) +
          eLpNorm (fun z => ‖gI z‖) p (volume.restrict V) :=
          eLpNorm_add_le (f := fun z => ‖g₁ z‖) (g := fun z => ‖gI z‖) Fact.out
      _ ≤ C₀ * (C * A) + C₀ * (C * A) :=
          add_le_add ((eLpNorm_norm _ hm₁).trans_le hg₁n) ((eLpNorm_norm _ hmI).trans_le hgIn)
      _ = ↑(2 * (C₀ * C)) * A := by push_cast; ring

/-- **Local `W^{1,p}` regularity for `\bar∂`.** For `1 < p < ∞`, a locally `Lᵖ` function whose
distributional `\bar∂` derivative is locally `Lᵖ` on an open set lies in `W^{1,p}_loc` there.
No weak derivative of the solution is assumed. -/
theorem HasWeakConjWirtingerDerivOn.memWkpLoc_one (hp : 1 < p) (hp_top : p ≠ ⊤) {Ω : Opens ℂ}
    {u f : ℂ → F} (hu : MemLpLoc p Ω u) (hf : MemLpLoc p Ω f)
    (h : HasWeakConjWirtingerDerivOn volume Ω u f) : MemWkpLoc p Ω 1 u := by
  have := FiniteDimensional.complete ℂ F
  have hloc (K : Set ℂ) (hK : IsCompact K) (hKΩ : K ⊆ Ω) : ∃ V : Opens ℂ, K ⊆ V ∧ V ≤ Ω ∧
      ∃ D : ℂ → ℂ →L[ℝ] F, HasWeakFDerivOn volume V u D ∧ MemLp D p (volume.restrict V) := by
    obtain ⟨W, hW, hKW, hWΩ, hWc⟩ := exists_open_between_and_isCompact_closure hK Ω.isOpen hKΩ
    obtain ⟨V, hKV, -, hVW, C, hC⟩ :=
      exists_hasWeakFDerivOn_eLpNorm_le_of_hasWeakConjWirtingerDerivOn_of_le (F := F)
        (U := ⟨W, hW⟩) hp hp_top le_rfl hK hKW
    have hu' := hu.memLp_of_closure_subset hWc hWΩ
    have hf' := hf.memLp_of_closure_subset hWc hWΩ
    have hWΩ' : (⟨W, hW⟩ : Opens ℂ) ≤ Ω := subset_closure.trans hWΩ
    obtain ⟨D, hD, hDn⟩ := hC u f hu' hf' (h.mono hWΩ')
    have hDp : MemLp D p (volume.restrict V) := hDn.trans_lt (ENNReal.mul_lt_top
      ENNReal.coe_lt_top (ENNReal.add_lt_top.2 ⟨hf'.eLpNorm_lt_top, hu'.eLpNorm_lt_top⟩))
    exact ⟨V, hKV, (subset_closure.trans hVW).trans hWΩ', D, hD, hDp⟩
  obtain ⟨D, hD⟩ := exists_hasWeakFDerivOn_iff_locally.2 fun x hx => by
    obtain ⟨V, hxV, -, D, hD, -⟩ := hloc {x} isCompact_singleton (singleton_subset_iff.2 hx)
    exact ⟨V, hxV rfl, D, hD⟩
  refine memWkpLoc_succ_iff_of_isOpen.2
    ⟨hu, D, hD, memWkpLoc_zero_iff.2 (memLpLoc_iff.2 fun K hKΩ hK => ?_)⟩
  obtain ⟨V, hKV, hVΩ, D', hD', hD'p⟩ := hloc K hK hKΩ
  exact (hD'p.ae_eq ((hD.mono hVΩ).ae_eq hD').symm).mono_measure
    (Measure.restrict_mono hKV le_rfl)

/-- **Local `W^{k+1,p}` regularity for `\bar∂`.** For `1 < p < ∞` and every `k`, a locally `Lᵖ`
function whose distributional `\bar∂` derivative lies in `W^{k,p}_loc` on an open set lies in
`W^{k+1,p}_loc` there. -/
theorem HasWeakConjWirtingerDerivOn.memWkpLoc_succ (hp : 1 < p) (hp_top : p ≠ ⊤) {Ω : Opens ℂ}
    {k : ℕ} {u f : ℂ → F} (hu : MemLpLoc p Ω u) (hf : MemWkpLoc p Ω k f)
    (h : HasWeakConjWirtingerDerivOn volume Ω u f) : MemWkpLoc p Ω (k + 1) u := by
  have := FiniteDimensional.complete ℂ F
  induction k generalizing u f with
  | zero => exact h.memWkpLoc_one hp hp_top hu (memWkpLoc_zero_iff.1 hf)
  | succ k ih =>
    obtain ⟨Df, hDf, hDfk⟩ := hf.exists_weakFDeriv_of_isOpen
    obtain ⟨D, hD, hDp⟩ :=
      (h.memWkpLoc_one hp hp_top hu hf.memLpLoc).exists_weakFDeriv_of_isOpen
    have hv (w : ℂ) : MemWkpLoc p Ω (k + 1) (fun z => D z w) :=
      ih ((memWkpLoc_zero_iff.1 hDp).clm_comp (apply ℝ F w)) (hDfk.clm_comp (apply ℝ F w))
        (h.weakLineDeriv (hD.hasWeakLineDerivOn w) (hDf.hasWeakLineDerivOn w))
    refine memWkpLoc_succ_iff_of_isOpen.2 ⟨hu, D, hD, ?_⟩
    rw [fun_eq_smulRightL_reCLM_add_smulRightL_imCLM D]
    exact ((hv 1).clm_comp _).add ((hv I).clm_comp _)

/-- **Interior `W^{1,p}` estimate for `\bar∂`.** For `1 < p < ∞`, `p ≤ r ≤ ∞` and a compact
`K ⊆ Ω`, there are an open `Ω'` with `K ⊆ Ω'` and compact closure in `Ω`, and a constant `C`,
such that every weak derivative `D` of a locally `Lʳ` solution of `\bar∂u = f` with locally `Lᵖ`
source satisfies `‖D‖_{Lᵖ(K)} ≤ C (‖f‖_{Lᵖ(Ω')} + ‖u‖_{Lʳ(Ω')})`. Such a `D` exists by
`HasWeakConjWirtingerDerivOn.memWkpLoc_one`. -/
theorem exists_eLpNorm_le_of_hasWeakConjWirtingerDerivOn_of_le (hp : 1 < p) (hp_top : p ≠ ⊤)
    {r : ℝ≥0∞} (hpr : p ≤ r) {Ω : Opens ℂ} {K : Set ℂ} (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    ∃ Ω' : Opens ℂ, K ⊆ Ω' ∧ IsCompact (closure (Ω' : Set ℂ)) ∧ closure (Ω' : Set ℂ) ⊆ Ω ∧
      ∃ C : ℝ≥0, ∀ (u f : ℂ → F) (D : ℂ → ℂ →L[ℝ] F), MemLpLoc r Ω u → MemLpLoc p Ω f →
        HasWeakConjWirtingerDerivOn volume Ω u f → HasWeakFDerivOn volume Ω u D →
        eLpNorm D p (volume.restrict K) ≤
          C * (eLpNorm f p (volume.restrict Ω') + eLpNorm u r (volume.restrict Ω')) := by
  have := FiniteDimensional.complete ℂ F
  obtain ⟨W, hW, hKW, hWΩ, hWc⟩ := exists_open_between_and_isCompact_closure hK Ω.isOpen hKΩ
  obtain ⟨V, hKV, -, hVW, C, hC⟩ :=
    exists_hasWeakFDerivOn_eLpNorm_le_of_hasWeakConjWirtingerDerivOn_of_le (F := F)
      (U := ⟨W, hW⟩) hp hp_top hpr hK hKW
  have hWΩ' : (⟨W, hW⟩ : Opens ℂ) ≤ Ω := subset_closure.trans hWΩ
  refine ⟨⟨W, hW⟩, hKW, hWc, hWΩ, C, fun u f D hu hf h hD => ?_⟩
  obtain ⟨D', hD', hD'n⟩ := hC u f (hu.memLp_of_closure_subset hWc hWΩ)
    (hf.memLp_of_closure_subset hWc hWΩ) (h.mono hWΩ')
  have hVΩ : V ≤ Ω := (subset_closure.trans hVW).trans hWΩ'
  calc eLpNorm D p (volume.restrict K) ≤ eLpNorm D p (volume.restrict V) :=
        eLpNorm_mono_measure _ (Measure.restrict_mono hKV le_rfl)
    _ = eLpNorm D' p (volume.restrict V) := eLpNorm_congr_ae ((hD.mono hVΩ).ae_eq hD')
    _ ≤ _ := hD'n

/-- **Interior `W^{1,p}` estimate for `\bar∂`**, with the solution measured in `Lᵖ`:
`‖D‖_{Lᵖ(K)} ≤ C (‖f‖_{Lᵖ(Ω')} + ‖u‖_{Lᵖ(Ω')})` for an open `Ω'` between `K` and `Ω`. -/
theorem exists_eLpNorm_le_of_hasWeakConjWirtingerDerivOn (hp : 1 < p) (hp_top : p ≠ ⊤)
    {Ω : Opens ℂ} {K : Set ℂ} (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    ∃ Ω' : Opens ℂ, K ⊆ Ω' ∧ IsCompact (closure (Ω' : Set ℂ)) ∧ closure (Ω' : Set ℂ) ⊆ Ω ∧
      ∃ C : ℝ≥0, ∀ (u f : ℂ → F) (D : ℂ → ℂ →L[ℝ] F), MemLpLoc p Ω u → MemLpLoc p Ω f →
        HasWeakConjWirtingerDerivOn volume Ω u f → HasWeakFDerivOn volume Ω u D →
        eLpNorm D p (volume.restrict K) ≤
          C * (eLpNorm f p (volume.restrict Ω') + eLpNorm u p (volume.restrict Ω')) :=
  exists_eLpNorm_le_of_hasWeakConjWirtingerDerivOn_of_le hp hp_top le_rfl hK hKΩ

/-- The `Lᵖ` norm of the solution cannot be dropped from the interior estimate. On a set `K` of
positive measure, no constant bounds the weak derivative of every solution by its
`\bar∂` derivative alone: the identity map has `\bar∂ z = 0` and derivative the identity. -/
theorem not_exists_eLpNorm_le_eLpNorm_conjWirtingerDeriv (hp : p ≠ 0) {Ω Ω' : Opens ℂ}
    {K : Set ℂ} (hK : volume K ≠ 0) :
    ¬ ∃ C : ℝ≥0, ∀ (u f : ℂ → ℂ) (D : ℂ → ℂ →L[ℝ] ℂ),
      HasWeakConjWirtingerDerivOn volume Ω u f → HasWeakFDerivOn volume Ω u D →
        eLpNorm D p (volume.restrict K) ≤ C * eLpNorm f p (volume.restrict Ω') := by
  rintro ⟨C, hC⟩
  have hderiv : fderiv ℝ (id : ℂ → ℂ) = fun _ => ContinuousLinearMap.id ℝ ℂ :=
    funext fun _ => fderiv_id
  have hconst : LocallyIntegrableOn (fderiv ℝ (id : ℂ → ℂ)) Ω volume := by
    rw [hderiv]
    exact locallyIntegrableOn_const (ContinuousLinearMap.id ℝ ℂ)
  have hid : HasWeakFDerivOn volume Ω (id : ℂ → ℂ) (fun _ => ContinuousLinearMap.id ℝ ℂ) := by
    rw [← hderiv]
    exact hasWeakFDerivOn_of_differentiableOn hconst fun x _ => differentiableAt_id
  have hle := hC id 0 _ differentiableOn_id.hasWeakConjWirtingerDerivOn_zero hid
  rw [eLpNorm_zero, mul_zero, nonpos_iff_eq_zero] at hle
  have hae := (eLpNorm_eq_zero_iff (ε := ℂ →L[ℝ] ℂ) (μ := volume.restrict K)
    (f := fun _ => ContinuousLinearMap.id ℝ ℂ) hp).1 hle
  have : (ae (volume.restrict K)).NeBot := ae_neBot.2 (by simpa using hK)
  obtain ⟨z, hz⟩ := hae.exists
  have h1 := ContinuousLinearMap.ext_iff.1 hz 1
  simp at h1

/-- The interior `W^{k+1,p}` estimate with the norm taken on the compact set itself, whose
derivatives are only seen on its interior. -/
private theorem exists_eLpNormWkp_compact_le_of_hasWeakConjWirtingerDerivOn (hp : 1 < p)
    (hp_top : p ≠ ⊤) (k : ℕ) {Ω : Opens ℂ} {K : Set ℂ} (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    ∃ Ω' : Opens ℂ, K ⊆ Ω' ∧ IsCompact (closure (Ω' : Set ℂ)) ∧ closure (Ω' : Set ℂ) ⊆ Ω ∧
      ∃ C : ℝ≥0, ∀ u f : ℂ → F, MemLpLoc p Ω u → MemWkpLoc p Ω k f →
        HasWeakConjWirtingerDerivOn volume Ω u f →
        eLpNormWkp p K (k + 1) u ≤
          C * (eLpNormWkp p Ω' k f + eLpNorm u p (volume.restrict Ω')) := by
  have := FiniteDimensional.complete ℂ F
  have hint : Opens.interior K ≤ Ω := fun x hx => hKΩ (interior_subset hx)
  induction k generalizing K with
  | zero =>
    obtain ⟨Ω', hKΩ', hΩ'c, hΩ'Ω, C, hC⟩ :=
      exists_eLpNorm_le_of_hasWeakConjWirtingerDerivOn (F := F) hp hp_top hK hKΩ
    refine ⟨Ω', hKΩ', hΩ'c, hΩ'Ω, C + 1, fun u f hu hf h => ?_⟩
    have hf₀ := memWkpLoc_zero_iff.1 hf
    obtain ⟨D, hD, -⟩ := (h.memWkpLoc_one hp hp_top hu hf₀).exists_weakFDeriv_of_isOpen
    calc eLpNormWkp p K (0 + 1) u
        ≤ eLpNorm u p (volume.restrict K) + eLpNormWkp p K 0 D :=
          eLpNormWkp_succ_le (hD.mono hint)
      _ ≤ eLpNorm u p (volume.restrict Ω') +
          C * (eLpNorm f p (volume.restrict Ω') + eLpNorm u p (volume.restrict Ω')) := by
          rw [eLpNormWkp_zero]
          gcongr ?_ + ?_
          · exact eLpNorm_mono_measure _ (Measure.restrict_mono hKΩ' le_rfl)
          · exact hC u f D hu hf₀ h hD
      _ ≤ ↑(C + 1) * (eLpNormWkp p Ω' 0 f + eLpNorm u p (volume.restrict Ω')) := by
          rw [eLpNormWkp_zero]
          exact (add_le_add (le_add_self : eLpNorm u p (volume.restrict Ω') ≤
            eLpNorm f p (volume.restrict Ω') + eLpNorm u p (volume.restrict Ω')) le_rfl).trans_eq
            (by push_cast; ring)
  | succ k ih =>
    -- The induction hypothesis bounds the directional derivatives `D·w` on `K` by data on `Ω₁`;
    -- the first-order estimate on `closure Ω₁` bounds `D` there by data on `Ω₂`.
    obtain ⟨Ω₁, hKΩ₁, hΩ₁c, hΩ₁Ω, C₁, hC₁⟩ := ih hK hKΩ hint
    obtain ⟨Ω₂, hΩ₁Ω₂, hΩ₂c, hΩ₂Ω, C₀, hC₀⟩ :=
      exists_eLpNorm_le_of_hasWeakConjWirtingerDerivOn (F := F) hp hp_top hΩ₁c hΩ₁Ω
    let a : ℂ → (ℂ →L[ℝ] F) →L[ℝ] F := fun w => apply ℝ F w
    let L₁ := smulRightL ℝ ℂ F reCLM
    let L₂ := smulRightL ℝ ℂ F imCLM
    let B : ℝ≥0 := ‖L₁‖₊ * ‖a 1‖₊ + ‖L₂‖₊ * ‖a I‖₊
    have hKΩ₂ : K ⊆ Ω₂ := hKΩ₁.trans (subset_closure.trans hΩ₁Ω₂)
    have hΩ₂Ω' : Ω₂ ≤ Ω := subset_closure.trans hΩ₂Ω
    refine ⟨Ω₂, hKΩ₂, hΩ₂c, hΩ₂Ω, 1 + B * (C₁ * (1 + C₀)), fun u f hu hf h => ?_⟩
    obtain ⟨Df, hDf, hDfk⟩ := hf.exists_weakFDeriv_of_isOpen
    obtain ⟨D, hD, hDp⟩ :=
      (h.memWkpLoc_one hp hp_top hu hf.memLpLoc).exists_weakFDeriv_of_isOpen
    -- `X` and `Y` are the two terms of the right-hand side on `Ω₂`.
    set X := eLpNormWkp p Ω₂ (k + 1) f with hX
    set Y := eLpNorm u p (volume.restrict Ω₂)
    have hfX : eLpNorm f p (volume.restrict Ω₂) ≤ X := eLpNorm_le_eLpNormWkp
    have hDfX : eLpNormWkp p Ω₁ k Df ≤ X := by
      refine (eLpNormWkp_mono_set (subset_closure.trans hΩ₁Ω₂)).trans ?_
      rw [hX, eLpNormWkp_succ_eq_of_hasWeakFDerivOn (hDf.mono hΩ₂Ω')]
      exact le_add_self
    have hDY : eLpNorm D p (volume.restrict Ω₁) ≤ C₀ * (X + Y) := by
      refine (eLpNorm_mono_measure _ (Measure.restrict_mono subset_closure le_rfl)).trans ?_
      refine (hC₀ u f D hu hf.memLpLoc h hD).trans ?_
      gcongr
    -- Each directional derivative `D·w` solves the differentiated equation, so the induction
    -- hypothesis applies to it.
    have hdir (w : ℂ) : eLpNormWkp p K (k + 1) (fun z => D z w) ≤
        ‖a w‖ₑ * (C₁ * (1 + C₀) * (X + Y)) := by
      have hDw : eLpNorm (fun z => D z w) p (volume.restrict Ω₁) ≤
          ‖a w‖ₑ * eLpNorm D p (volume.restrict Ω₁) := by
        have := eLpNormWkp_clm_comp_le (p := p) (U := Ω₁) (k := 0) (f := D) (a w)
        rw [eLpNormWkp_zero, eLpNormWkp_zero] at this
        exact this
      calc eLpNormWkp p K (k + 1) (fun z => D z w)
          ≤ C₁ * (eLpNormWkp p Ω₁ k (fun z => Df z w) +
              eLpNorm (fun z => D z w) p (volume.restrict Ω₁)) :=
            hC₁ _ _ ((memWkpLoc_zero_iff.1 hDp).clm_comp (a w)) (hDfk.clm_comp (a w))
              (h.weakLineDeriv (hD.hasWeakLineDerivOn w) (hDf.hasWeakLineDerivOn w))
        _ ≤ C₁ * (‖a w‖ₑ * X + ‖a w‖ₑ * (C₀ * (X + Y))) := by
            refine mul_le_mul_right (add_le_add ?_ ?_) _
            · exact (eLpNormWkp_clm_comp_le (f := Df) (a w)).trans (by gcongr)
            · exact hDw.trans (by gcongr)
        _ ≤ C₁ * (‖a w‖ₑ * (X + Y) + ‖a w‖ₑ * (C₀ * (X + Y))) := by
            gcongr
            exact le_self_add
        _ = ‖a w‖ₑ * (C₁ * (1 + C₀) * (X + Y)) := by ring
    -- `D` is reassembled from `D·1` and `D·I`, and the constants are collected into `B`.
    have hDeq : D = (fun z => L₁ (D z 1)) + fun z => L₂ (D z I) :=
      fun_eq_smulRightL_reCLM_add_smulRightL_imCLM D
    have hB : ‖L₁‖ₑ * (‖a 1‖ₑ * (C₁ * (1 + C₀) * (X + Y))) +
        ‖L₂‖ₑ * (‖a I‖ₑ * (C₁ * (1 + C₀) * (X + Y))) = ↑(B * (C₁ * (1 + C₀))) * (X + Y) := by
      simp only [B, enorm_eq_nnnorm]
      push_cast
      ring
    calc eLpNormWkp p K (k + 1 + 1) u
        ≤ eLpNorm u p (volume.restrict K) + eLpNormWkp p K (k + 1) D :=
          eLpNormWkp_succ_le (hD.mono hint)
      _ ≤ Y + (‖L₁‖ₑ * (‖a 1‖ₑ * (C₁ * (1 + C₀) * (X + Y))) +
          ‖L₂‖ₑ * (‖a I‖ₑ * (C₁ * (1 + C₀) * (X + Y)))) := by
          gcongr ?_ + ?_
          · exact eLpNorm_mono_measure _ (Measure.restrict_mono hKΩ₂ le_rfl)
          · rw [hDeq]
            refine (eLpNormWkp_add_le hp.le).trans (add_le_add ?_ ?_)
            · exact (eLpNormWkp_clm_comp_le L₁).trans (by gcongr; exact hdir 1)
            · exact (eLpNormWkp_clm_comp_le L₂).trans (by gcongr; exact hdir I)
      _ ≤ ↑(1 + B * (C₁ * (1 + C₀))) * (X + Y) := by
          rw [hB]
          exact (add_le_add (le_add_self : Y ≤ X + Y) le_rfl).trans_eq (by push_cast; ring)

/-- **Interior `W^{k+1,p}` estimate for `\bar∂`.** For `1 < p < ∞`, every `k` and a compact
`K ⊆ Ω`, there are opens `V ⊆ Ω'` with `K ⊆ V`, `Ω'` of compact closure in `Ω`, and a constant
`C`, such that every locally `Lᵖ` solution of `\bar∂u = f` with `f ∈ W^{k,p}_loc(Ω)` satisfies
`‖u‖_{W^{k+1,p}(V)} ≤ C (‖f‖_{W^{k,p}(Ω')} + ‖u‖_{Lᵖ(Ω')})`. Since `V` is an open neighbourhood
of `K`, the weak derivatives are controlled on all of `K`. -/
theorem exists_eLpNormWkp_le_of_hasWeakConjWirtingerDerivOn (hp : 1 < p) (hp_top : p ≠ ⊤)
    (k : ℕ) {Ω : Opens ℂ} {K : Set ℂ} (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    ∃ V Ω' : Opens ℂ, K ⊆ V ∧ (V : Set ℂ) ⊆ Ω' ∧ IsCompact (closure (Ω' : Set ℂ)) ∧
      closure (Ω' : Set ℂ) ⊆ Ω ∧ ∃ C : ℝ≥0, ∀ u f : ℂ → F, MemLpLoc p Ω u →
        MemWkpLoc p Ω k f → HasWeakConjWirtingerDerivOn volume Ω u f →
        eLpNormWkp p V (k + 1) u ≤
          C * (eLpNormWkp p Ω' k f + eLpNorm u p (volume.restrict Ω')) := by
  obtain ⟨W, hW, hKW, hWΩ, hWc⟩ := exists_open_between_and_isCompact_closure hK Ω.isOpen hKΩ
  obtain ⟨Ω', hWΩ', hΩ'c, hΩ'Ω, C, hC⟩ :=
    exists_eLpNormWkp_compact_le_of_hasWeakConjWirtingerDerivOn (F := F) hp hp_top k hWc hWΩ
  exact ⟨⟨W, hW⟩, Ω', hKW, subset_closure.trans hWΩ', hΩ'c, hΩ'Ω, C,
    fun u f hu hf h => (eLpNormWkp_mono_set subset_closure).trans (hC u f hu hf h)⟩

end TauCeti
