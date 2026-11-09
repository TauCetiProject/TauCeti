/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Wirtinger.TestBound
public import TauCeti.Analysis.Complex.Wirtinger.Weak
public import TauCeti.Analysis.Sobolev.Local.Basic
public import TauCeti.Analysis.Sobolev.TestFunctionLp.Representation
public import TauCeti.Analysis.Sobolev.WeakDeriv.Local
import TauCeti.Analysis.Distribution.TestFunction.LineDeriv
import TauCeti.Analysis.Sobolev.WeakDeriv.Coordinates
import Mathlib.Analysis.Complex.OperatorNorm
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# Interior regularity for the distributional Cauchy–Riemann equation

Let `F` be a finite-dimensional complex inner product space and `1 < p < ∞`. If `u : ℂ → F` is
locally `Lᵖ` on an open set `Ω` and its distributional derivative `\bar∂u` is locally `Lᵖ`, then
`u` lies in `W^{1,p}_loc(Ω)`. If `\bar∂u` lies in `W^{k,p}_loc(Ω)`, then `u` lies in
`W^{k+1,p}_loc(Ω)`. The first-order interior estimate
`‖Du‖_{Lᵖ(K)} ≤ C (‖\bar∂u‖_{Lᵖ(Ω')} + ‖u‖_{Lᵖ(Ω')})` holds on every compact `K ⊆ Ω`, for an open
`Ω'` with `K ⊆ Ω'` and compact closure in `Ω`. The solution may instead be measured in any larger
exponent `r ≥ p`, including infinity. The `Lᵖ` norm of `u` cannot be dropped from the estimate:
the identity map solves `\bar∂u = 0` and has nonzero derivative.

The first-order statement combines two existing results. The interior test bound for the
distributional equation controls each directional distributional derivative by the conjugate
`Lᵠ` norm of the test function. The `Lᵖ` dual representation then turns each such bound into an
`Lᵖ` weak derivative, coordinatewise in a real basis of `F`. Local weak derivatives glue to a
weak derivative on `Ω`. The induction on the order uses that a weak directional derivative of a
solution solves the differentiated equation.

## Main results

* `HasWeakConjWirtingerDerivOn.weakLineDeriv`: a weak directional derivative of a solution solves
  the differentiated equation.
* `exists_hasWeakFDerivOn_eLpNorm_le_of_hasWeakConjWirtingerDerivOn_of_le`: the weak derivative
  exists near a compact set, with an `Lᵖ` bound, for an `Lʳ` solution on a fixed open set.
* `HasWeakConjWirtingerDerivOn.memWkpLoc_one`: local `W^{1,p}` regularity.
* `HasWeakConjWirtingerDerivOn.memWkpLoc_succ`: local `W^{k+1,p}` regularity for every `k`.
* `exists_eLpNorm_le_of_hasWeakConjWirtingerDerivOn_of_le` and
  `exists_eLpNorm_le_of_hasWeakConjWirtingerDerivOn`: the first-order interior estimate.
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

section Differentiated

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
  {μ : Measure ℂ} {Ω : Opens ℂ} {u f u' f' : ℂ → F} {v : ℂ}

/-- A weak directional derivative of a solution of `\bar∂u = f` solves the differentiated
equation `\bar∂(∂ᵥu) = ∂ᵥf`. No other derivative of `u` or `f` is assumed. -/
theorem HasWeakConjWirtingerDerivOn.weakLineDeriv (h : HasWeakConjWirtingerDerivOn μ Ω u f)
    (hu : HasWeakLineDerivOn μ Ω u u' v) (hf : HasWeakLineDerivOn μ Ω f f' v) :
    HasWeakConjWirtingerDerivOn μ Ω u' f' := by
  refine hasWeakConjWirtingerDerivOn_iff.2
    ⟨h.completeSpace, hu.locallyIntegrableOn_deriv, hf.locallyIntegrableOn_deriv, fun φ => ?_⟩
  have hw (w : ℂ) : ∫ z, lineDeriv ℝ (φ : ℂ → ℝ) z w • u' z ∂μ =
      -∫ z, lineDeriv ℝ (∂_{v} φ : 𝓓(Ω, ℝ)) z w • u z ∂μ := by
    calc ∫ z, lineDeriv ℝ (φ : ℂ → ℝ) z w • u' z ∂μ
        = ∫ z, (∂_{w} φ : 𝓓(Ω, ℝ)) z • u' z ∂μ := by
          simp only [TestFunction.lineDerivOp_apply]
      _ = -∫ z, lineDeriv ℝ (∂_{w} φ : 𝓓(Ω, ℝ)) z v • u z ∂μ := by
          rw [hu.integral_lineDeriv_smul_eq_neg_integral_smul, neg_neg]
      _ = _ := by simp only [TestFunction.lineDeriv_lineDerivOp_comm φ w v]
  have hfv : ∫ z, (∂_{v} φ : 𝓓(Ω, ℝ)) z • f z ∂μ = -∫ z, (φ : ℂ → ℝ) z • f' z ∂μ := by
    simpa only [TestFunction.lineDerivOp_apply] using
      hf.integral_lineDeriv_smul_eq_neg_integral_smul φ
  have hφ := h.integral_lineDeriv_smul_add_I_smul_eq_neg_two_smul_integral_smul (∂_{v} φ)
  rw [hw 1, hw I, smul_neg, ← neg_add, hφ, hfv]
  module

end Differentiated

/-- Coordinatewise `Lᵖ` representation of a directional distributional derivative with a
conjugate `Lᵠ` test bound, for finite-dimensional real coefficients. The constant depends only
on the coefficient space and the exponents. -/
private theorem exists_hasWeakLineDerivOn_eLpNorm_le {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    [p.HolderConjugate q] (hq : 1 < q) (hq_top : q ≠ ⊤) :
    ∃ C : ℝ≥0, ∀ (V : Opens ℂ) (u : ℂ → E), LocallyIntegrableOn u V volume →
      ∀ (v : ℂ) (M : ℝ≥0∞), M ≠ ⊤ →
      (∀ φ : 𝓓(V, ℝ), ‖∫ z, lineDeriv ℝ (φ : ℂ → ℝ) z v • u z‖ₑ ≤
        M * eLpNorm (φ : ℂ → ℝ) q volume) →
      ∃ g : ℂ → E, HasWeakLineDerivOn volume V u g v ∧
        eLpNorm g p (volume.restrict V) ≤ C * M := by
  classical
  have := FiniteDimensional.complete ℝ E
  let b := Module.finBasis ℝ E
  let c : Fin (Module.finrank ℝ E) → E →L[ℝ] ℝ := fun i => LinearMap.toContinuousLinearMap
    (b.coord i)
  refine ⟨∑ i, ‖c i‖₊ * ‖b i‖₊, fun V u hu v M hM hbound => ?_⟩
  have hcu (i) : LocallyIntegrableOn (fun z => c i (u z)) V volume :=
    (c i).locallyIntegrableOn_comp hu
  have hscalar (i) : ∃ g : Lp ℝ p (volume.restrict (V : Set ℂ)), ‖g‖ ≤ ‖c i‖ * M.toReal ∧
      HasWeakLineDerivOn volume V (fun z => c i (u z)) g v := by
    refine exists_norm_le_hasWeakLineDerivOn_of_abs_integral_lineDeriv_mul_le_eLpNorm hq hq_top
      (hcu i) v (by positivity) fun φ => ?_
    have hφ : eLpNorm (φ : ℂ → ℝ) q volume ≠ ⊤ :=
      (φ.continuous.memLp_of_hasCompactSupport φ.hasCompactSupport).eLpNorm_ne_top
    have hint : ∫ z, lineDeriv ℝ (φ : ℂ → ℝ) z v * c i (u z) =
        c i (∫ z, lineDeriv ℝ (φ : ℂ → ℝ) z v • u z) := by
      rw [← (c i).integral_comp_comm (integrable_lineDeriv_smul_of_locallyIntegrableOn hu φ v)]
      simp only [map_smul, smul_eq_mul]
    have hreal : ‖∫ z, lineDeriv ℝ (φ : ℂ → ℝ) z v • u z‖ ≤
        M.toReal * (eLpNorm (φ : ℂ → ℝ) q volume).toReal := by
      rw [← ENNReal.toReal_mul, ← toReal_enorm]
      exact ENNReal.toReal_mono (ENNReal.mul_ne_top hM hφ) (hbound φ)
    rw [hint, ← Real.norm_eq_abs, mul_assoc]
    exact ((c i).le_opNorm _).trans (mul_le_mul_of_nonneg_left hreal (norm_nonneg _))
  choose g hgn hg using hscalar
  let G : ℂ → E := fun z => ∑ i, (g i : ℂ → ℝ) z • b i
  refine ⟨G, ?_, ?_⟩
  · refine (hasWeakLineDerivOn_iff_coordinates b).2 fun i => ?_
    refine (hg i).congr_ae_deriv (Eventually.of_forall fun z => ?_)
    simp [G, Finsupp.single_apply]
  · have hG : G = ∑ i, fun z => (g i : ℂ → ℝ) z • b i := by
      funext z
      simp [G, Finset.sum_apply]
    rw [hG]
    refine (eLpNorm_sum_le Fact.out).trans ?_
    push_cast
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun i _ => ?_
    have hmeas : AEStronglyMeasurable (fun z => (g i : ℂ → ℝ) z • b i)
        (volume.restrict (V : Set ℂ)) :=
      (Lp.aestronglyMeasurable (g i)).smul_const _
    calc eLpNorm (fun z => (g i : ℂ → ℝ) z • b i) p (volume.restrict (V : Set ℂ))
        ≤ ‖b i‖₊ * eLpNorm (g i : ℂ → ℝ) p (volume.restrict (V : Set ℂ)) :=
          eLpNorm_le_mul_eLpNorm_of_ae_le_mul' hmeas
            (Eventually.of_forall fun z => by rw [enorm_smul, mul_comm]; rfl) p
      _ ≤ ‖b i‖₊ * (‖c i‖₊ * M) := by
          gcongr
          rw [← Lp.enorm_def, ← ofReal_norm, ← ENNReal.ofReal_toReal hM,
            ← ENNReal.ofReal_coe_nnreal (p := ‖c i‖₊), ← ENNReal.ofReal_mul (by positivity)]
          exact ENNReal.ofReal_le_ofReal (hgn i)
      _ = ↑(‖c i‖₊ * ‖b i‖₊) * M := by push_cast; ring

/-- Membership in `Lᵖ` on an open set with compact closure inside `Ω`, from local membership. -/
private theorem MemLpLoc.memLp_of_closure_subset {r : ℝ≥0∞} {Ω W : Set ℂ} {E : Type*}
    [NormedAddCommGroup E] {u : ℂ → E}
    (hu : MemLpLoc r Ω u) (hWc : IsCompact (closure W)) (hWΩ : closure W ⊆ Ω) :
    MemLp u r (volume.restrict W) :=
  (memLpLoc_iff.1 hu _ hWΩ hWc).mono_measure (Measure.restrict_mono subset_closure le_rfl)

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
  obtain ⟨C₀, hC₀⟩ := exists_hasWeakLineDerivOn_eLpNorm_le (E := F) (p := p) hq hq_top
  refine ⟨V, hKV, hVc, hVU, 2 * (C₀ * C), fun u f hu hf h => ?_⟩
  set A := eLpNorm f p (volume.restrict U) + eLpNorm u r (volume.restrict U)
  have hA : (C : ℝ≥0∞) * A ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.coe_ne_top (ENNReal.add_ne_top.2 ⟨hf.eLpNorm_ne_top,
      hu.eLpNorm_ne_top⟩)
  have hUeq (φ : 𝓓(U, ℝ)) :
      (∫ z, lineDeriv ℝ (φ : ℂ → ℝ) z 1 • u z) +
        I • (∫ z, lineDeriv ℝ (φ : ℂ → ℝ) z I • u z) =
          -(2 : ℝ) • (∫ z, (φ : ℂ → ℝ) z • f z) := by
    rw [h.integral_lineDeriv_smul_add_I_smul_eq_neg_two_smul_integral_smul φ,
      show (-(2 : ℂ)) = ((-(2 : ℝ) : ℝ) : ℂ) by push_cast; rfl, Complex.coe_smul]
  have hVU' : (V : Set ℂ) ⊆ U := subset_closure.trans hVU
  have hloc : LocallyIntegrableOn u V volume := h.locallyIntegrableOn.mono_set hVU'
  have hdir (v : ℂ) (hv : ‖v‖ₑ = 1) : ∃ g : ℂ → F, HasWeakLineDerivOn volume V u g v ∧
      eLpNorm g p (volume.restrict V) ≤ C₀ * (C * A) :=
    hC₀ V u hloc v _ hA fun φ => (hC u f hu hf hUeq φ v).trans_eq (by rw [hv, mul_one])
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
`W^{k+1,p}_loc` there. Each weak derivative of the solution solves the differentiated
equation, so the order rises by induction. -/
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
    have hDeq : D = fun z => smulRightL ℝ ℂ F reCLM (D z 1) + smulRightL ℝ ℂ F imCLM (D z I) := by
      funext z
      refine ContinuousLinearMap.coe_injective (Complex.basisOneI.ext fun i => ?_)
      fin_cases i <;> simp
    refine memWkpLoc_succ_iff_of_isOpen.2 ⟨hu, D, hD, ?_⟩
    rw [hDeq]
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

end TauCeti
