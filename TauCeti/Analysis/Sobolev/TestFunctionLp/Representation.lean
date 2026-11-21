/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.TestFunctionLp.Basic
public import TauCeti.MeasureTheory.Function.Lp.Dual
import TauCeti.MeasureTheory.Function.LocallyIntegrable
import TauCeti.Analysis.Sobolev.WeakDeriv.Coordinates
import TauCeti.MeasureTheory.Function.Lp.FiniteDimensional
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

/-!
# Weak derivatives from `Lᵠ` test bounds

For conjugate exponents `1 < p, q < ∞`, a distributional directional derivative bounded by
the `Lᵠ` norm of test functions is represented by an `Lᵖ` weak derivative, with the same
bound. This applies to locally integrable functions without assuming differentiability or a
weak derivative in advance. For a finite-dimensional real codomain the same holds coordinatewise,
with a constant depending only on the codomain. The proof extends the distributional functional
from the image of test functions in `Lᵠ` by Hahn–Banach, then uses the integral representation
of the dual.

The result assumes σ-finiteness on the open domain. The Hilbert-space theorem in
`TestFunctionLp/Basic` remains available without that measure hypothesis.

On a finite-dimensional real inner product space `E` of dimension `d`, the same duality represents
functionals bounded by the gradient: a linear functional `ℓ` on the test functions of `Ω` with
`|ℓ φ| ≤ M ‖∇φ‖_{Lᵠ}` is `φ ↦ ∫_Ω ⟪H, ∇φ⟫` for a field `H ∈ Lᵖ(Ω; E)` with `‖H‖_{Lᵖ} ≤ d² M`
(`TauCeti.exists_memLp_forall_eq_integral_inner_gradient_of_abs_le`), that is, `ℓ = -div H` in the
sense of distributions. The functional extends by Hahn–Banach through the partial derivatives
`φ ↦ (⟪bᵢ, ∇φ⟫)ᵢ` into `(Lᵠ(Ω))ᵈ`, and the dual of `(Lᵠ(Ω))ᵈ` is `(Lᵖ(Ω))ᵈ`.

## References

* L. C. Evans, *Partial Differential Equations*, second edition, §5.8.2.
* G. P. Galdi, *An Introduction to the Mathematical Theory of the Navier–Stokes Equations*, 2nd ed.,
  Springer, 2011, Section III.3.
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory Set TopologicalSpace Filter
open scoped ContDiff Distributions ENNReal NNReal

section LineDeriv

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [OpensMeasurableSpace E] {μ : Measure E} [IsFiniteMeasureOnCompacts μ]
  {Ω : Opens E} [IsLocallyFiniteMeasure (μ.restrict Ω)]
  [SigmaFinite (μ.restrict Ω)] {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
  [p.HolderConjugate q]

/-- A distributional directional derivative bounded by the conjugate `Lᵠ` test norm is an
`Lᵖ` weak derivative with that bound. No regularity of `u` beyond local integrability is needed. -/
theorem exists_norm_le_hasWeakLineDerivOn_of_abs_integral_lineDeriv_mul_le_eLpNorm {u : E → ℝ}
    (hq : 1 < q) (hq_top : q ≠ ⊤) (hu : LocallyIntegrableOn u Ω μ) (v : E)
    {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ φ : 𝓓(Ω, ℝ),
      |∫ x, lineDeriv ℝ (φ : E → ℝ) x v * u x ∂μ| ≤ C * (eLpNorm (φ : E → ℝ) q μ).toReal) :
    ∃ g : Lp ℝ p (μ.restrict Ω), ‖g‖ ≤ C ∧ HasWeakLineDerivOn μ Ω u g v := by
  obtain ⟨Λ, hΛnorm, hΛφ⟩ :=
    exists_dual_norm_le_of_abs_integral_lineDeriv_mul_le_eLpNorm hu v hC hbound
  let g := (Lp.dualEquiv ℝ (μ.restrict Ω) p q hq hq_top).symm (-Λ)
  refine ⟨g, ?_, ?_⟩
  · simpa only [g, LinearIsometryEquiv.norm_map, norm_neg] using hΛnorm
  · refine hasWeakLineDerivOn_iff_testFunction.2
      ⟨inferInstance, hu, Lp.locallyIntegrableOn g Fact.out, fun φ => ?_⟩
    have hpair : ∫ x in Ω, g x * testFunctionLp (mu := μ) q φ x ∂μ =
        -Λ (testFunctionLp (mu := μ) q φ) := by
      dsimp only [g]
      rw [Lp.integral_dualEquiv_symm_mul, neg_apply]
    have hrepr : ∫ x, (φ : E → ℝ) x • g x ∂μ = -(∫ x, lineDeriv ℝ (φ : E → ℝ) x v * u x ∂μ) := by
      rw [← setIntegral_smul_eq_integral_smul φ]
      calc ∫ x in Ω, (φ : E → ℝ) x • g x ∂μ =
          ∫ x in Ω, g x * testFunctionLp (mu := μ) q φ x ∂μ := by
             apply integral_congr_ae
             filter_upwards [testFunctionLp_apply_ae (mu := μ) q φ] with x hx
             simp [hx, mul_comm]
           _ = _ := hpair.trans (congrArg Neg.neg (hΛφ φ))
    rw [hrepr, neg_neg]
    simp only [smul_eq_mul]

/-- **Vector-valued `Lᵖ` representation.** For a finite-dimensional real codomain, a
distributional directional derivative bounded by `M` times the conjugate `Lᵠ` test norm is an
`Lᵖ` weak derivative of norm at most `C * M`. The constant depends only on the codomain. -/
theorem exists_eLpNorm_le_hasWeakLineDerivOn_of_enorm_integral_lineDeriv_smul_le {G : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G] (hq : 1 < q)
    (hq_top : q ≠ ⊤) :
    ∃ C : ℝ≥0, ∀ u : E → G, LocallyIntegrableOn u Ω μ → ∀ (v : E) (M : ℝ≥0∞), M ≠ ⊤ →
      (∀ φ : 𝓓(Ω, ℝ), ‖∫ x, lineDeriv ℝ (φ : E → ℝ) x v • u x ∂μ‖ₑ ≤
        M * eLpNorm (φ : E → ℝ) q μ) →
      ∃ g : E → G, HasWeakLineDerivOn μ Ω u g v ∧ eLpNorm g p (μ.restrict Ω) ≤ C * M := by
  classical
  have := FiniteDimensional.completeSpace ℝ G
  let b := Module.finBasis ℝ G
  let c : Fin (Module.finrank ℝ G) → G →L[ℝ] ℝ := fun i => LinearMap.toContinuousLinearMap
    (b.coord i)
  refine ⟨∑ i, ‖c i‖₊ * ‖b i‖₊, fun u hu v M hM hbound => ?_⟩
  have hcu (i) : LocallyIntegrableOn (fun z => c i (u z)) Ω μ :=
    (c i).locallyIntegrableOn_comp hu
  have hscalar (i) : ∃ g : Lp ℝ p (μ.restrict (Ω : Set E)), ‖g‖ ≤ ‖c i‖ * M.toReal ∧
      HasWeakLineDerivOn μ Ω (fun z => c i (u z)) g v := by
    refine exists_norm_le_hasWeakLineDerivOn_of_abs_integral_lineDeriv_mul_le_eLpNorm hq hq_top
      (hcu i) v (by positivity) fun φ => ?_
    have hφ : eLpNorm (φ : E → ℝ) q μ ≠ ⊤ :=
      (φ.continuous.memLp_of_hasCompactSupport φ.hasCompactSupport).eLpNorm_ne_top
    have hint : ∫ z, lineDeriv ℝ (φ : E → ℝ) z v * c i (u z) ∂μ =
        c i (∫ z, lineDeriv ℝ (φ : E → ℝ) z v • u z ∂μ) := by
      rw [← (c i).integral_comp_comm (integrable_lineDeriv_smul_of_locallyIntegrableOn hu φ v)]
      simp only [map_smul, smul_eq_mul]
    have hreal : ‖∫ z, lineDeriv ℝ (φ : E → ℝ) z v • u z ∂μ‖ ≤
        M.toReal * (eLpNorm (φ : E → ℝ) q μ).toReal := by
      rw [← ENNReal.toReal_mul, ← toReal_eNorm]
      exact ENNReal.toReal_mono (ENNReal.mul_ne_top hM hφ) (hbound φ)
    rw [hint, ← Real.norm_eq_abs, mul_assoc]
    exact ((c i).le_opNorm _).trans (mul_le_mul_of_nonneg_left hreal (norm_nonneg _))
  choose g hgn hg using hscalar
  let w : E → G := fun z => ∑ i, (g i : E → ℝ) z • b i
  refine ⟨w, ?_, ?_⟩
  · refine (hasWeakLineDerivOn_iff_coordinates b).2 fun i => ?_
    refine (hg i).congr_ae_deriv (Eventually.of_forall fun z => ?_)
    simp [w, Finsupp.single_apply]
  · have hw : w = ∑ i, fun z => (g i : E → ℝ) z • b i := by
      funext z
      simp [w, Finset.sum_apply]
    rw [hw]
    refine (eLpNorm_sum_le Fact.out).trans ?_
    push_cast
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun i _ => ?_
    have hmeas : AEStronglyMeasurable (fun z => (g i : E → ℝ) z • b i)
        (μ.restrict (Ω : Set E)) :=
      (Lp.aestronglyMeasurable (g i)).smul_const _
    calc eLpNorm (fun z => (g i : E → ℝ) z • b i) p (μ.restrict (Ω : Set E))
        ≤ ‖b i‖₊ * eLpNorm (g i : E → ℝ) p (μ.restrict (Ω : Set E)) :=
          eLpNorm_le_mul_eLpNorm_of_ae_le_mul' hmeas
            (Eventually.of_forall fun z => by rw [eNorm_smul, mul_comm, eNorm_eq_nnNorm]) p
      _ ≤ ‖b i‖₊ * (‖c i‖₊ * M) := by
          gcongr
          calc eLpNorm (g i : E → ℝ) p (μ.restrict (Ω : Set E))
              = ENNReal.ofReal ‖g i‖ := by simp [← Lp.eNorm_def]
            _ ≤ ENNReal.ofReal (‖c i‖ * M.toReal) := ENNReal.ofReal_le_ofReal (hgn i)
            _ = ‖c i‖₊ * M := by simp [ENNReal.ofReal_mul, hM, eNorm_eq_nnNorm]
      _ = ↑(‖c i‖₊ * ‖b i‖₊) * M := by push_cast; ring

end LineDeriv

section Gradient

open Module
open scoped Gradient InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {Ω : Opens E}

variable [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [IsFiniteMeasureOnCompacts μ]
  {p q : ℝ≥0∞}

/-- The partial derivatives `⟪bᵢ, ∇φ⟫` of a test function along an orthonormal basis, as a linear
map into `(Lᵠ(Ω))ᵈ`. -/
private def partialDerivativesLp (b : OrthonormalBasis (Fin (finrank ℝ E)) ℝ E) :
    𝓓(Ω, ℝ) →ₗ[ℝ] (Fin (finrank ℝ E) → Lp ℝ q (μ.restrict Ω)) :=
  LinearMap.pi fun i => (testFunctionLpₗ μ Ω q).comp
    (TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ (b i)).toLinearMap

private theorem partialDerivativesLp_apply_ae (b : OrthonormalBasis (Fin (finrank ℝ E)) ℝ E)
    (φ : 𝓓(Ω, ℝ)) (i : Fin (finrank ℝ E)) :
    ∀ᵐ x ∂μ.restrict Ω, partialDerivativesLp (μ := μ) (q := q) b φ i x =
      ⟪b i, ∇ (φ : E → ℝ) x⟫_ℝ := by
  filter_upwards [testFunctionLp_apply_ae (mu := μ) q
    (TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ (b i) φ)] with x hx
  simp only [partialDerivativesLp, LinearMap.pi_apply, LinearMap.coe_comp, Function.comp_apply,
    testFunctionLpₗ_apply, ContinuousLinearMap.coe_coe]
  rw [hx, lineDerivCLM_apply_eq_inner]

/-- The `Lᵠ` norm of the gradient of a test function is at most `d` times the norm of its
partial derivatives in `(Lᵠ(Ω))ᵈ`. -/
private theorem toReal_eLpNorm_gradient_le [Fact (1 ≤ q)]
    (b : OrthonormalBasis (Fin (finrank ℝ E)) ℝ E) (φ : 𝓓(Ω, ℝ)) :
    (eLpNorm (∇ (φ : E → ℝ)) q μ).toReal ≤
      finrank ℝ E * ‖partialDerivativesLp (μ := μ) (q := q) b φ‖ := by
  set T := partialDerivativesLp (μ := μ) (q := q) b
  have hDnorm (i : Fin (finrank ℝ E)) :
      ‖T φ i‖ₑ = eLpNorm (fun x => ⟪b i, ∇ (φ : E → ℝ) x⟫_ℝ) q μ := by
    simp only [T, partialDerivativesLp, LinearMap.pi_apply, LinearMap.coe_comp,
      Function.comp_apply, testFunctionLpₗ_apply, ContinuousLinearMap.coe_coe]
    rw [enorm_testFunctionLp_eq_eLpNorm]
    congr 1
    funext x
    exact lineDerivCLM_apply_eq_inner φ (b i) x
  have h := b.toBasis.eLpNorm_le_sum_enorm_mul_eLpNorm_coord (p := q) (μ := μ)
    (continuous_gradient_testFunction φ).aestronglyMeasurable
  have hb (i : Fin (finrank ℝ E)) : ‖b i‖ₑ = 1 := by
    rw [← ofReal_norm, b.orthonormal.1 i, ENNReal.ofReal_one]
  simp only [OrthonormalBasis.coe_toBasis, hb, one_mul,
    OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.repr_apply_apply,
    Basis.coord_apply] at h
  simp_rw [← hDnorm] at h
  have hfin : ∀ i ∈ Finset.univ, ‖T φ i‖ₑ ≠ ⊤ := fun i _ => eNorm_ne_top
  calc (eLpNorm (∇ (φ : E → ℝ)) q μ).toReal ≤ (∑ i, ‖T φ i‖ₑ).toReal :=
        ENNReal.toReal_mono (ENNReal.sum_ne_top.2 hfin) h
    _ = ∑ i, ‖T φ i‖ := by
        rw [ENNReal.toReal_sum hfin]
        simp only [toReal_eNorm]
    _ ≤ ∑ _i : Fin (finrank ℝ E), ‖T φ‖ := Finset.sum_le_sum fun i _ => norm_le_pi_norm (T φ) i
    _ = finrank ℝ E * ‖T φ‖ := by simp

/-- **Hahn–Banach for gradient bounds.** A linear functional on test functions bounded by `M`
times the `Lᵠ` norm of the gradient extends to a continuous functional on `(Lᵠ(Ω))ᵈ`, of norm at
most `d M`, through the partial derivatives. -/
private theorem exists_dual_comp_partialDerivativesLp_eq [Fact (1 ≤ q)]
    (b : OrthonormalBasis (Fin (finrank ℝ E)) ℝ E) (ℓ : 𝓓(Ω, ℝ) →ₗ[ℝ] ℝ) {M : ℝ} (hM : 0 ≤ M)
    (hℓ : ∀ φ : 𝓓(Ω, ℝ), |ℓ φ| ≤ M * (eLpNorm (∇ (φ : E → ℝ)) q μ).toReal) :
    ∃ Λ : StrongDual ℝ (Fin (finrank ℝ E) → Lp ℝ q (μ.restrict Ω)), ‖Λ‖ ≤ finrank ℝ E * M ∧
      ∀ φ, Λ (partialDerivativesLp (μ := μ) (q := q) b φ) = ℓ φ := by
  set T := partialDerivativesLp (μ := μ) (q := q) b
  have hbound (φ : 𝓓(Ω, ℝ)) : |ℓ φ| ≤ finrank ℝ E * M * ‖T φ‖ :=
    (hℓ φ).trans (by
      rw [mul_comm (finrank ℝ E : ℝ) M, mul_assoc]; gcongr; exact toReal_eLpNorm_gradient_le b φ)
  have hker : LinearMap.ker T.rangeRestrict ≤ LinearMap.ker ℓ := by
    rw [LinearMap.ker_rangeRestrict]
    intro φ hφ
    have h := hbound φ
    rw [LinearMap.mem_ker.mp hφ, norm_zero, mul_zero] at h
    exact LinearMap.mem_ker.mpr (abs_nonpos_iff.mp h)
  let f₀ : LinearMap.range T →ₗ[ℝ] ℝ :=
    T.rangeRestrict.liftOfSurjective T.surjective_rangeRestrict ⟨ℓ, hker⟩
  have hf₀_apply (φ : 𝓓(Ω, ℝ)) : f₀ (T.rangeRestrict φ) = ℓ φ :=
    LinearMap.equivOfSurjective_apply T.surjective_rangeRestrict hker
  have hf₀ : ∀ s, ‖f₀ s‖ ≤ finrank ℝ E * M * ‖s‖ := by
    intro s
    obtain ⟨φ, rfl⟩ := T.surjective_rangeRestrict s
    rw [hf₀_apply, Real.norm_eq_abs, ← Submodule.norm_coe, LinearMap.codRestrict_apply]
    exact hbound φ
  obtain ⟨Λ, hΛ, hΛnorm⟩ := exists_extension_norm_eq _ (f₀.mkContinuous (finrank ℝ E * M) hf₀)
  refine ⟨Λ, hΛnorm.trans_le (LinearMap.mkContinuous_norm_le _ (by positivity) hf₀),
    fun φ => ?_⟩
  have h := hΛ (T.rangeRestrict φ)
  simpa only [LinearMap.codRestrict_apply, LinearMap.mkContinuous_apply, hf₀_apply] using h

/-- **Functionals bounded by the gradient are divergences.** Let `1 < q < ∞` and let `p` be its
conjugate exponent. If a linear functional `ℓ` on the test functions of `Ω` satisfies
`|ℓ φ| ≤ M ‖∇φ‖_{L^q}`, then `ℓ φ = ∫_Ω ⟪H, ∇φ⟫` for a field `H ∈ Lᵖ(Ω; E)` with
`‖H‖_{Lᵖ(Ω)} ≤ d² M`, where `d` is the dimension. In other words `ℓ = -div H` in the sense of
distributions. -/
theorem exists_memLp_forall_eq_integral_inner_gradient_of_abs_le [SigmaFinite (μ.restrict Ω)]
    [Fact (1 ≤ p)] [Fact (1 ≤ q)] [p.HolderConjugate q] (hq : 1 < q) (hq_top : q ≠ ⊤)
    (ℓ : 𝓓(Ω, ℝ) →ₗ[ℝ] ℝ) {M : ℝ} (hM : 0 ≤ M)
    (hℓ : ∀ φ : 𝓓(Ω, ℝ), |ℓ φ| ≤ M * (eLpNorm (∇ (φ : E → ℝ)) q μ).toReal) :
    ∃ H : E → E, MemLp H p (μ.restrict Ω) ∧
      eLpNorm H p (μ.restrict Ω) ≤ (finrank ℝ E : ℝ≥0∞) ^ 2 * ENNReal.ofReal M ∧
      ∀ φ : 𝓓(Ω, ℝ), ℓ φ = ∫ x in Ω, ⟪H x, ∇ (φ : E → ℝ) x⟫_ℝ ∂μ := by
  set b := stdOrthonormalBasis ℝ E
  obtain ⟨Λ, hΛ, hΛT⟩ := exists_dual_comp_partialDerivativesLp_eq (μ := μ) (q := q) b ℓ hM hℓ
  obtain ⟨H, hH, hHnorm, hHΛ⟩ := Lp.exists_memLp_forall_dual_pi_apply_eq (p := p) hq hq_top b Λ
  rw [Fintype.card_fin] at hHnorm
  refine ⟨H, hH, ?_, fun φ => ?_⟩
  · calc eLpNorm H p (μ.restrict Ω) ≤ finrank ℝ E * ENNReal.ofReal ‖Λ‖ := hHnorm
      _ ≤ finrank ℝ E * ENNReal.ofReal (finrank ℝ E * M) := by gcongr
      _ = (finrank ℝ E : ℝ≥0∞) ^ 2 * ENNReal.ofReal M := by
          rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast, sq, mul_assoc]
  -- `∑ᵢ ⟪H, bᵢ⟫ ⟪bᵢ, ∇φ⟫ = ⟪H, ∇φ⟫`.
  have hint (i : Fin (finrank ℝ E)) : Integrable (fun x => ⟪H x, b i⟫_ℝ *
      partialDerivativesLp (μ := μ) (q := q) b φ i x) (μ.restrict Ω) :=
    (((innerSL ℝ).flip (b i)).comp_memLp' hH).integrable_mul (Lp.memLp _)
  rw [← hΛT φ, hHΛ, ← integral_finsetSum _ fun i _ => hint i]
  refine integral_congr_ae ?_
  filter_upwards [ae_all_iff.2 fun i => partialDerivativesLp_apply_ae (μ := μ) (q := q) b φ i]
    with x hx
  simp only [hx]
  exact b.sum_inner_mul_inner (H x) (∇ (φ : E → ℝ) x)

end Gradient

end TauCeti
