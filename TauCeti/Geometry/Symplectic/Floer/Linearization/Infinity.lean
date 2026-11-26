/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Linearization.Pullback
public import TauCeti.Analysis.Complex.RealChart
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Conformal
import Mathlib.Analysis.Calculus.Deriv.Inv
import TauCeti.Analysis.Complex.HolomorphicFunctions.Lp.Removable
import TauCeti.MeasureTheory.Measure.Lebesgue.Complex

/-!
# Square-integrable solutions of the formal adjoint at the point at infinity

On the Riemann sphere, read in the coordinate `w ∈ ℂ ≅ ℝ × ℝ`, Floer data that are a fixed
`ω`-invariant complex structure `J₀` and the zero perturbation near `w = ∞` have the formal adjoint
`D^* η = -ω♭ (∂s ξ - J₀ ∂t ξ)`, `ξ = ω♭⁻¹ ∘ η`
(`TauCeti.SymplecticForm.floerLinearizationAdjoint_const_eq_neg_flatEquiv`), a Cauchy–Riemann
operator. The cokernel of the linearized operator `D_u : W^{1,2} → L²` of the sphere consists of
square-integrable covector fields `η` with `D^* η = 0` in the weak sense. Near the point at infinity
a covector field `η` is read in the chart `ζ = w⁻¹` as the `(0, 1)`-form
`η' = η (ζ⁻¹) ∘ (a + b J₀)` (`TauCeti.Floer.covectorPullback` along
`TauCeti.Complex.realChart (·⁻¹)`), where `a + i b = -ζ⁻²` is the derivative of the inversion. The
point `ζ = 0` is not in the domain of `η'`. This file proves that it is removable: if `η` is
differentiable with `D^* η = 0` on `|w| > T` and `‖η‖²` is integrable there, then `η'` extends
smoothly across `ζ = 0`
(`exists_contDiffOn_eq_covectorPullback_inv_of_floerLinearizationAdjoint_eq_zero`, in the
namespace `TauCeti.SymplecticForm`).
The hypotheses are pointwise: `η` is differentiable and solves `D^* η = 0` classically. A
cokernel element is only a weak `L²` solution, so the theorem applies to it once it is known to be
differentiable near infinity; that interior regularity is not proved here. The semi-Fredholm
estimate of the formal adjoint on the sphere
(`TauCeti.Geometry.Symplectic.Floer.SemiFredholm.Sphere`) is stated for compactly supported
fields, and applying it to cokernel elements through cutoffs near infinity needs both that
regularity and the extension across infinity proved here.

The proof complexifies `η`. For a vector `x`, the complex function
`G_x(w) = η(w) x - i η(w) (J₀ x)` is holomorphic where `D^* η = 0`: the equation says
`∂s η = -(∂t η) ∘ J₀`
(`fderiv_apply_eq_neg_fderiv_apply_apply_of_floerLinearizationAdjoint_eq_zero`, in the namespace
`TauCeti.SymplecticForm`), which is the Cauchy–Riemann equation for `G_x`. The map
`θ ↦ θ x - i θ (J₀ x)` is complex linear for the action `θ ↦ θ ∘ J₀` of `i` on covectors, so the
complexification of `η'` at `x` is `-ζ⁻² G_x(ζ⁻¹)`. Since `‖G_x‖ ≤ C ‖η‖` is square-integrable
near infinity, the `L²` removable singularity theorem at infinity
(`TauCeti.HolomorphicFunctions.exists_differentiableOn_eq_inv_sq_smul_comp_inv`) extends it
holomorphically across `ζ = 0`. The real parts at the vectors of a basis then reassemble the
extension of `η'`.

## Main results

* `exists_contDiffOn_eq_covectorPullback_inv_of_floerLinearizationAdjoint_eq_zero`, in the
  namespace `TauCeti.SymplecticForm`: square-integrable solutions of the formal adjoint near
  infinity extend smoothly across infinity.

## References

* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, 2nd ed., Section 3.1
  and Appendix C, on the Fredholm theory of real Cauchy–Riemann operators on closed surfaces.
-/

public section

open Filter Metric Set Topology MeasureTheory

namespace TauCeti.SymplecticForm

open Floer

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {J₀ : AlmostComplexStructure V}

/-- The complexification `θ ↦ θ x - i θ (J₀ x)` of covectors at a vector `x`. It is complex
linear for the action `θ ↦ θ ∘ J₀` of `i`. -/
private noncomputable def covectorComplexify (J₀ : AlmostComplexStructure V) (x : V) :
    (V →L[ℝ] ℝ) →L[ℝ] ℂ :=
  Complex.ofRealCLM.comp (ContinuousLinearMap.apply ℝ ℝ x) -
    Complex.I • Complex.ofRealCLM.comp (ContinuousLinearMap.apply ℝ ℝ (J₀ x))

private theorem covectorComplexify_apply (x : V) (θ : V →L[ℝ] ℝ) :
    covectorComplexify J₀ x θ = (θ x : ℂ) - Complex.I * (θ (J₀ x) : ℂ) := by
  simp [covectorComplexify]

private theorem re_covectorComplexify (x : V) (θ : V →L[ℝ] ℝ) :
    (covectorComplexify J₀ x θ).re = θ x := by
  simp [covectorComplexify_apply]

variable [FiniteDimensional ℝ V]

private theorem covectorComplexify_comp_smul_add_smul (x : V) (θ : V →L[ℝ] ℝ) (a b : ℝ) :
    covectorComplexify J₀ x
        (θ.comp (a • (1 : V →L[ℝ] V) + b • J₀.toLinearMap.toContinuousLinearMap)) =
      ⟨a, b⟩ * covectorComplexify J₀ x θ := by
  have hJ : J₀.toLinearMap (J₀.toLinearMap x) = -x := J₀.apply_apply x
  apply Complex.ext
  · simp [covectorComplexify_apply]
  · simp [covectorComplexify_apply, hJ]
    ring

variable {ω : SymplecticForm V}

/-- Where a covector field is annihilated by the formal adjoint of constant data, its
complexification at any vector is holomorphic. -/
private theorem differentiableAt_covectorComplexify (hJ₀ : ω.Invariant J₀) (u : ℝ × ℝ → V)
    {η : ℝ × ℝ → V →L[ℝ] ℝ} {w : ℂ} (hη : DifferentiableAt ℝ η (Complex.equivRealProdCLM w))
    (hD : ω.floerLinearizationAdjoint (fun _ _ ↦ J₀.toLinearMap.toContinuousLinearMap)
      (fun _ _ ↦ 0) (fun _ _ ↦ 0) u η (Complex.equivRealProdCLM w) = 0) (x : V) :
    DifferentiableAt ℂ (fun w ↦ covectorComplexify J₀ x (η (Complex.equivRealProdCLM w))) w := by
  have hfd : HasFDerivAt (fun w ↦ covectorComplexify J₀ x (η (Complex.equivRealProdCLM w)))
      ((covectorComplexify J₀ x).comp ((fderiv ℝ η (Complex.equivRealProdCLM w)).comp
        (Complex.equivRealProdCLM : ℂ →L[ℝ] ℝ × ℝ))) w :=
    (covectorComplexify J₀ x).hasFDerivAt.comp w
      (hη.hasFDerivAt.comp w Complex.equivRealProdCLM.hasFDerivAt)
  rw [differentiableAt_complex_iff_differentiableAt_real, hfd.fderiv]
  refine ⟨hfd.differentiableAt, ?_⟩
  have h₁ := fderiv_apply_eq_neg_fderiv_apply_apply_of_floerLinearizationAdjoint_eq_zero hJ₀ u hD x
  have h₂ :=
    fderiv_apply_eq_neg_fderiv_apply_apply_of_floerLinearizationAdjoint_eq_zero hJ₀ u hD (J₀ x)
  rw [AlmostComplexStructure.apply_apply, map_neg, neg_neg] at h₂
  have hI : Complex.equivRealProdCLM Complex.I = (0, 1) := by simp
  have hone : Complex.equivRealProdCLM 1 = (1, 0) := by simp
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe, hI, hone,
    covectorComplexify_apply, h₁, h₂, smul_eq_mul]
  apply Complex.ext <;> simp

omit [FiniteDimensional ℝ V] in
/-- Near infinity, the complexification at any vector of a square-integrable field is
square-integrable. -/
private theorem integrableOn_sq_norm_covectorComplexify {η : ℝ × ℝ → V →L[ℝ] ℝ} {T : ℝ}
    (hη : ∀ z : ℝ × ℝ, T < ‖Complex.equivRealProdCLM.symm z‖ → DifferentiableAt ℝ η z)
    (hL2 : IntegrableOn (fun z ↦ ‖η z‖ ^ 2) {z | T < ‖Complex.equivRealProdCLM.symm z‖})
    (x : V) :
    IntegrableOn (fun w ↦ ‖covectorComplexify J₀ x (η (Complex.equivRealProdCLM w))‖ ^ 2)
      {w | T < ‖w‖} := by
  set e := Complex.equivRealProdCLM
  have hopen : IsOpen {w : ℂ | T < ‖w‖} := isOpen_lt continuous_const continuous_norm
  have hL2' : IntegrableOn (fun w ↦ ‖η (e w)‖ ^ 2) {w : ℂ | T < ‖w‖} := by
    have h := (Complex.volume_preserving_equiv_real_prod.integrableOn_comp_preimage
      Complex.measurableEquivRealProd.measurableEmbedding (f := fun z ↦ ‖η z‖ ^ 2)
      (s := {z | T < ‖e.symm z‖})).2 hL2
    have hpre : (e : ℂ → ℝ × ℝ) ⁻¹' {z | T < ‖e.symm z‖} = {w : ℂ | T < ‖w‖} := by
      ext w
      simp only [mem_preimage, mem_ofPred_eq, ContinuousLinearEquiv.symm_apply_apply]
    rwa [Complex.coe_measurableEquivRealProd_eq_equivRealProdCLM, hpre] at h
  have hcont : ContinuousOn (fun w ↦ covectorComplexify J₀ x (η (e w))) {w | T < ‖w‖} :=
    fun w hw ↦ ((covectorComplexify J₀ x).continuous.continuousAt.comp
      ((hη (e w) (by simpa using hw)).continuousAt.comp
        e.continuous.continuousAt)).continuousWithinAt
  refine (hL2'.const_mul (‖covectorComplexify J₀ x‖ ^ 2)).mono' ?_ ?_
  · exact (hcont.norm.pow 2).aestronglyMeasurable hopen.measurableSet
  · refine (ae_restrict_iff' hopen.measurableSet).2 (Eventually.of_forall fun w _ ↦ ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), ← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) ((covectorComplexify J₀ x).le_opNorm _) 2

/-- The complexification of the pullback of a covector field along the inversion is
`-ζ⁻²` times the complexification of the field at `ζ⁻¹`. -/
private theorem covectorComplexify_covectorPullback_inv (u : ℝ × ℝ → V) (η : ℝ × ℝ → V →L[ℝ] ℝ)
    {ζ : ℝ × ℝ} (hζ : Complex.equivRealProdCLM.symm ζ ≠ 0) (x : V) :
    covectorComplexify J₀ x (covectorPullback (TauCeti.Complex.realChart (·⁻¹))
        (fun _ _ ↦ J₀.toLinearMap.toContinuousLinearMap) u η ζ) =
      -((Complex.equivRealProdCLM.symm ζ) ^ 2)⁻¹ *
        covectorComplexify J₀ x (η (Complex.equivRealProdCLM (Complex.equivRealProdCLM.symm ζ)⁻¹))
    := by
  set e := Complex.equivRealProdCLM
  set q := e.symm ζ
  have hφ : fderiv ℝ (TauCeti.Complex.realChart (·⁻¹)) ζ stdComplexLineReal = e (-(q ^ 2)⁻¹) := by
    rw [TauCeti.Complex.fderiv_realChart_apply (hasDerivAt_inv hζ), stdComplexLineReal_eq]
    simp [e, q]
  rw [covectorPullback_apply, hφ, TauCeti.Complex.realChart_apply,
    covectorComplexify_comp_smul_add_smul]
  -- The coefficient `⟨a, b⟩` rebuilt from the components of `e (-(q²)⁻¹)` is `-(q²)⁻¹`.
  rw [Complex.equivRealProdCLM_apply, Complex.eta]

/-- **Square-integrable solutions of the formal adjoint extend across infinity.** Let `J₀` be an
`ω`-invariant complex structure, and let `η` be a covector field, differentiable on `|w| > T` and
annihilated there by the formal adjoint `D^*` of the constant data `J₀` with zero perturbation, with
`‖η‖²` integrable on `|w| > T`. Then `η` read as a `(0, 1)`-form in the chart `ζ = w⁻¹` of the
point at infinity, `η' = TauCeti.Floer.covectorPullback (realChart (·⁻¹)) J₀ u η`, agrees off
`ζ = 0` with a field that is smooth on the whole disc `|ζ| < T⁻¹`. The statement has content only
for `0 < T`: for `T ≤ 0` Lean's `T⁻¹ ≤ 0` makes that disc empty. -/
theorem exists_contDiffOn_eq_covectorPullback_inv_of_floerLinearizationAdjoint_eq_zero
    (hJ₀ : ω.Invariant J₀) (u : ℝ × ℝ → V) {η : ℝ × ℝ → V →L[ℝ] ℝ} {T : ℝ}
    (hη : ∀ z : ℝ × ℝ, T < ‖Complex.equivRealProdCLM.symm z‖ → DifferentiableAt ℝ η z)
    (hD : ∀ z : ℝ × ℝ, T < ‖Complex.equivRealProdCLM.symm z‖ →
      ω.floerLinearizationAdjoint (fun _ _ ↦ J₀.toLinearMap.toContinuousLinearMap)
        (fun _ _ ↦ 0) (fun _ _ ↦ 0) u η z = 0)
    (hL2 : IntegrableOn (fun z ↦ ‖η z‖ ^ 2) {z | T < ‖Complex.equivRealProdCLM.symm z‖}) :
    ∃ η₀ : ℝ × ℝ → V →L[ℝ] ℝ,
      ContDiffOn ℝ (⊤ : ℕ∞) η₀ {ζ | ‖Complex.equivRealProdCLM.symm ζ‖ < T⁻¹} ∧
      ∀ ζ : ℝ × ℝ, ‖Complex.equivRealProdCLM.symm ζ‖ < T⁻¹ →
        Complex.equivRealProdCLM.symm ζ ≠ 0 →
        η₀ ζ = covectorPullback (TauCeti.Complex.realChart (·⁻¹))
          (fun _ _ ↦ J₀.toLinearMap.toContinuousLinearMap) u η ζ := by
  set e := Complex.equivRealProdCLM
  have hGd (x : V) :
      DifferentiableOn ℂ (fun w ↦ covectorComplexify J₀ x (η (e w))) {w | T < ‖w‖} :=
    fun w hw ↦ by
      have hw' : T < ‖e.symm (e w)‖ := by simpa using hw
      exact (differentiableAt_covectorComplexify hJ₀ u (hη _ hw') (hD _ hw')
        x).differentiableWithinAt
  choose g hgd hgeq using fun x ↦
    HolomorphicFunctions.exists_differentiableOn_eq_inv_sq_smul_comp_inv (hGd x)
      (integrableOn_sq_norm_covectorComplexify hη hL2 x)
  set b := Module.finBasis ℝ V
  refine ⟨fun ζ ↦ ∑ k, (-(g (b k) (e.symm ζ)).re) • LinearMap.toContinuousLinearMap (b.coord k),
    ?_, fun ζ hζ hζ0 ↦ ?_⟩
  · have hmaps : MapsTo e.symm {ζ | ‖e.symm ζ‖ < T⁻¹} (ball 0 T⁻¹) := fun ζ hζ ↦ by
      simpa using hζ
    refine ContDiffOn.sum fun k _ ↦ ?_
    exact (Complex.reCLM.contDiff.comp_contDiffOn ((((hgd (b k)).contDiffOn
      isOpen_ball).restrict_scalars ℝ).comp e.symm.contDiff.contDiffOn hmaps)).neg.smul
      contDiffOn_const
  refine ContinuousLinearMap.coe_injective (b.ext fun k ↦ ?_)
  -- At each basis vector, `η'` is minus the real part of the extension `g`.
  have hk : covectorPullback (TauCeti.Complex.realChart (·⁻¹))
      (fun _ _ ↦ J₀.toLinearMap.toContinuousLinearMap) u η ζ (b k) =
        -(g (b k) (e.symm ζ)).re := by
    rw [← re_covectorComplexify (J₀ := J₀), covectorComplexify_covectorPullback_inv u η hζ0]
    simp only [hgeq (b k) _ (by simpa using hζ) hζ0, smul_eq_mul, neg_mul, Complex.neg_re, e]
  simp [hk, Module.Basis.coord_apply, Finsupp.single_apply]

end TauCeti.SymplecticForm
