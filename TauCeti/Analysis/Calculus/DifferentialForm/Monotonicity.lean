/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.DifferentialForm.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.Topology.Algebra.Module.FiniteDimensionBilinear
public import TauCeti.Analysis.InnerProductSpace.AlternatingForm
public import TauCeti.Analysis.InnerProductSpace.HodgeStar.Kahler.Hermitian
public import TauCeti.Analysis.InnerProductSpace.HodgeStar.Kahler.Wedge
public import TauCeti.Geometry.Symplectic.CompatibleMetric
public import TauCeti.Geometry.Symplectic.Liouville.Linear
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import TauCeti.Analysis.Calculus.DifferentialForm.Basic
import TauCeti.Analysis.Calculus.DifferentialForm.Integral
import TauCeti.Analysis.InnerProductSpace.HodgeStar.AlternatingForm
import TauCeti.Analysis.Normed.Group.CompactSupport
import TauCeti.Analysis.Normed.Module.Alternating.Wedge.Uncurry

/-!
# The monotonicity identity for closed two-forms on a Hermitian four-space

Let `V` be a four-dimensional real inner product space with an orthogonal complex structure `J`,
oriented as a complex space, and let `ω` be its Kähler form, `ω(u, w) = ⟪J u, w⟫`
(`TauCeti.AlmostComplexStructure.kahlerForm`). For a closed two-form `F` on `V` and a radial
cutoff `x ↦ φ(‖x‖²)`, this file proves

`∫ φ(‖x‖²) ⟪ω, F⟫ = ∫ φ'(‖x‖²) (F(x, J x) - ‖x‖² ⟪ω, F⟫)`

(`TauCeti.integral_mul_inner_kahlerForm_eq`), where `⟪ω, F⟫` is the inner product of two-forms,
so that `F ∧ ω = ⟪ω, F⟫ vol`. This is the integrated form of Stokes' theorem on balls behind
Taubes's monotonicity formula for the defect energy of large-parameter Seiberg–Witten solutions.
The radial primitive `λₓ(v) = ω(x, v) / 2` of `ω` (`ContinuousLinearMap.liouvilleFormCLM`) has
`dλ = ω`, and integration by parts moves the derivative onto the cutoff:
`∫ φ(‖x‖²) dλ ∧ F = ∫ λ ∧ d(φ(‖x‖²) F) = ∫ λ ∧ dφ(‖x‖²) ∧ F` for closed `F`. With
`dφ(‖x‖²) = 2 φ'(‖x‖²) ⟪x, ·⟫` the four-form on the right is
`φ'(‖x‖²) (J x)^♭ ∧ x^♭ ∧ F = φ'(‖x‖²) ⟪⋆(J x ∧ x), F⟫ vol`, and
`⋆(x ∧ J x) = ‖x‖² ω - x ∧ J x` (`TauCeti.AlmostComplexStructure.hodgeStar_ιMulti_apply`): for
a unit vector `x` the star is the complex line orthogonal to `x` and `J x`.

As `φ` approaches the indicator of `[0, σ²]`, the left side tends to `∫_{B_σ} ⟪ω, F⟫` and the
right side to `σ / 2` times the integral over the sphere `∂B_σ` of `F(u, J u)`, for `u` a unit
vector spanning, with `J u`, the complex line orthogonal to the radial one. The value `F(u, J u)`
is the Hermitian part `B(u, u)` of `F` (`TauCeti.AlmostComplexStructure.hermitianForm`), at most
`⟪ω, F⟫ / 2 + ‖F⁻‖ / √2` for the anti-self-dual part `F⁻`
(`TauCeti.AlmostComplexStructure.abs_hermitianForm_apply_self_sub_le`). Hence, for a cutoff
nonincreasing on `[0, ∞)` (`TauCeti.integral_mul_inner_kahlerForm_le`),

`∫ φ(‖x‖²) ⟪ω, F⟫ ≤ ∫ (-φ'(‖x‖²)) ‖x‖² (⟪ω, F⟫ / 2 + ‖F⁻‖ / √2)`.

For the real curvature `F = i F_a` of a large-parameter Seiberg–Witten solution in a flat chart,
`⟪ω, F⟫ / 2` is `(r / 8) (1 - |α|² + |β|²)` up to the forcing term
(`TauCeti.SeibergWitten.inner_div_two_eq_of_add_hodgeStar_eq`). Taubes's coarse estimates for
the anti-self-dual part `F⁻`, which are not formalized here, then bound the right side by the
defect energy. The resulting differential inequality for the defect energy `E(σ)` of the balls
`B_σ` is the hypothesis
`E(σ) ≤ (σ / 2) (1 + C σ) (1 + C₁ r^(-1/2)) E'(σ) + K σ⁴`
of `TauCeti.exists_forall_ofReal_mul_sq_le_measure_closedBall_of_ae_le`, where the factor
`1 + C σ` accounts for the curvature of the metric. This file proves the flat-chart (`C = 0`)
cutoff analogue of that inequality before the anti-self-dual estimates are applied; neither those
estimates nor the passage from cutoffs to balls is made here.

Integrals are against the volume of `V`; the orientation of `V` is the one of a positively
oriented unitary frame `e`, `J e₀ = e₁`, `J e₂ = e₃`.

## Main results

* `TauCeti.integral_mul_inner_kahlerForm_eq`: the monotonicity identity.
* `TauCeti.integral_mul_inner_kahlerForm_le`: the monotonicity inequality for nonincreasing
  cutoffs.

## References

* C. H. Taubes, *SW ⇒ Gr: from the Seiberg–Witten equations to pseudo-holomorphic curves*,
  J. Amer. Math. Soc. 9 (1996), 845–918.
-/

public section

noncomputable section

open Module exteriorPower MeasureTheory ContinuousAlternatingMap Filter
open scoped RealInnerProductSpace

namespace TauCeti

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

namespace AlmostComplexStructure

/-- **The radial primitive of the Kähler form**: for an orthogonal `J`, the one-form
`λₓ(v) = ω(x, v) / 2 = ⟪J x, v⟫ / 2` (`ContinuousLinearMap.liouvilleFormCLM`) has `dλ = ω`. -/
theorem extDeriv_liouvilleFormCLM_symplecticForm {J : AlmostComplexStructure V}
    (hJ : ∀ v w, ⟪J v, J w⟫ = ⟪v, w⟫) (x : V) :
    extDeriv (ContinuousLinearMap.liouvilleFormCLM
      (J.symplecticForm hJ).toBilinForm.toContinuousBilinearMap) x =
        alternatingFormEquiv V 2 J.kahlerForm := by
  ext v
  have hv : v = ![v 0, v 1] := (FinVec.etaExpand_eq v).symm
  rw [ContinuousLinearMap.extDeriv_liouvilleFormCLM_apply_of_skew _ two_ne_zero
    (fun v w ↦ by simp [real_inner_comm w, inner_apply_left hJ]) x v,
    alternatingFormEquiv_apply, hv, inner_kahlerForm_ιMulti hJ]
  simp

end AlmostComplexStructure

variable [Fact (finrank ℝ V = 4)]
  {e : OrthonormalBasis (Fin 4) ℝ V} {J : AlmostComplexStructure V} {o : Orientation ℝ V (Fin 4)}
  (h₀ : J (e 0) = e 1) (h₂ : J (e 2) = e 3) (hkl : 2 + 2 = finrank ℝ V)
  (he : e.toBasis.orientation = o)

open AlmostComplexStructure

variable [MeasurableSpace V] [BorelSpace V]

include h₀ h₂ in
/-- **The monotonicity identity.** For a closed `C¹` two-form `F` on a Hermitian four-space and
a compactly supported `C¹` function `φ`,

`∫ φ(‖x‖²) ⟪ω, F⟫ = ∫ φ'(‖x‖²) (F(x, J x) - ‖x‖² ⟪ω, F⟫)`,

where `ω` is the Kähler form and `F` is paired with `ω` as a two-vector. -/
theorem integral_mul_inner_kahlerForm_eq {F : V → V [⋀^Fin 2]→L[ℝ] ℝ} (hF : ContDiff ℝ 1 F)
    (hdF : ∀ x, extDeriv F x = 0) {φ : ℝ → ℝ} (hφ : ContDiff ℝ 1 φ)
    (hφc : HasCompactSupport φ) :
    ∫ x, φ (‖x‖ ^ 2) * ⟪J.kahlerForm, (alternatingFormEquiv V 2).symm (F x)⟫ =
      ∫ x, deriv φ (‖x‖ ^ 2) * (F x ![x, J x] -
        ‖x‖ ^ 2 * ⟪J.kahlerForm, (alternatingFormEquiv V 2).symm (F x)⟫) := by
  have hJ := inner_apply_apply_of_orthonormalBasis h₀ h₂
  have hkl : 2 + 2 = finrank ℝ V := (Fact.out : finrank ℝ V = 4).symm
  -- The radial primitive `λₓ(v) = ω(x, v) / 2` of the Kähler form, with `dλ = ω`.
  set B := (J.symplecticForm hJ).toBilinForm.toContinuousBilinearMap
  have hB (v w : V) : B v w = ⟪J v, w⟫ := by simp [B]
  set lam := ContinuousLinearMap.liouvilleFormCLM B
  -- The cutoff `g(x) = φ(‖x‖²)`, with `dg = 2 φ'(‖x‖²) ⟪x, ·⟫`, so
  -- `λ ∧ dg = φ'(‖x‖²) (J x)^♭ ∧ x^♭`.
  set g : V → ℝ := fun x ↦ φ (‖x‖ ^ 2)
  have hg : ContDiff ℝ 1 g := hφ.comp (contDiff_norm_sq ℝ)
  have hdg (x : V) : wedge (lam x) (ofSubsingleton ℝ V ℝ (0 : Fin 1) (fderiv ℝ g x)) =
      deriv φ (‖x‖ ^ 2) • wedge (ofSubsingleton ℝ V ℝ (0 : Fin 1) (innerSL ℝ (J x)))
        (ofSubsingleton ℝ V ℝ (0 : Fin 1) (innerSL ℝ x)) := by
    have hd : HasFDerivAt g (deriv φ (‖x‖ ^ 2) • (2 • innerSL ℝ x)) x :=
      (hφ.differentiable one_ne_zero _).hasDerivAt.comp_hasFDerivAt x
        (hasStrictFDerivAt_norm_sq x).hasFDerivAt
    rw [hd.fderiv]
    ext v
    rw [show v = ![v 0, v 1] from (FinVec.etaExpand_eq v).symm]
    simp only [wedge_apply_one_one, ContinuousLinearMap.liouvilleFormCLM_apply, hB, lam,
      ofSubsingleton_apply_apply, _root_.smul_apply, coe_innerSL_apply, smul_eq_mul, nsmul_eq_mul,
      Matrix.cons_val_fin_one, Nat.cast_ofNat, coe_smul, Pi.smul_apply]
    ring
  -- Integration by parts, `∫ dλ ∧ g F = ∫ λ ∧ d(g F)`, with `d(g F) = dg ∧ F` as `dF = 0`.
  have h := e.toBasis.integral_extDeriv_wedge_eq_integral_wedge_extDeriv (k := 1) (l := 2)
    (φ := lam) (ψ := g • F) (by norm_num) lam.contDiff (hg.smul hF)
    (hφc.comp_norm_sq).smul_right
  rw [OrthonormalBasis.addHaar_eq_volume] at h
  have hc (h' : 4 = 2 + 2) : (⇑e.toBasis ∘ Fin.cast h') = e ∘ finCongr (hkl.trans Fact.out) :=
    funext fun _ ↦ by simp
  rw [pow_one, neg_neg, one_mul] at h
  refine (integral_congr_ae (Eventually.of_forall fun x ↦ ?_)).trans
    (h.trans (integral_congr_ae (Eventually.of_forall fun x ↦ ?_)))
  · rw [hc, extDeriv_liouvilleFormCLM_symplecticForm hJ, Pi.smul_apply', wedge_smul_right,
      ContinuousAlternatingMap.smul_apply, smul_eq_mul,
      wedge_alternatingFormEquiv_kahlerForm_apply h₀ h₂ hkl]
  · dsimp only
    rw [extDeriv_function_smul (hg.differentiable one_ne_zero x) (hF.differentiable one_ne_zero x),
      hdF, smul_zero, zero_add]
    have hA : alternatizeUncurryFin ((fderiv ℝ g x).smulRight (F x)) =
        wedge (ofSubsingleton ℝ V ℝ (0 : Fin 1) (fderiv ℝ g x)) (F x) := by
      ext v
      rw [alternatizeUncurryFin_smulRight_apply_eq_wedge, Fin.cast_refl, Function.comp_id]
    have hassoc := wedge_assoc (lam x) (ofSubsingleton ℝ V ℝ (0 : Fin 1) (fderiv ℝ g x)) (F x)
      (e ∘ finCongr (hkl.trans Fact.out))
    have hcast : (e ∘ finCongr (hkl.trans Fact.out) : Fin (1 + (1 + 2)) → V) =
        (e ∘ finCongr (hkl.trans Fact.out)) ∘ Fin.cast (Nat.add_assoc 1 1 2).symm :=
      funext fun _ ↦ by simp
    rw [hc, hA, hcast, ← hassoc, hdg, wedge_smul_left, ContinuousAlternatingMap.smul_apply,
      smul_eq_mul, wedge_wedge_ofSubsingleton_innerSL_apply h₀ h₂ hkl]

include h₀ h₂ hkl he in
/-- **The monotonicity inequality.** For a closed `C¹` two-form `F` on a Hermitian four-space and
a compactly supported `C¹` function `φ` nonincreasing on `[0, ∞)`,

`∫ φ(‖x‖²) ⟪ω, F⟫ ≤ ∫ (-φ'(‖x‖²)) ‖x‖² (⟪ω, F⟫ / 2 + ‖F⁻‖ / √2)`,

where `ω` is the Kähler form, `F` is paired with `ω` as a two-vector and
`F⁻ = (F - ⋆F) / 2` is its anti-self-dual part. -/
theorem integral_mul_inner_kahlerForm_le {F : V → V [⋀^Fin 2]→L[ℝ] ℝ} (hF : ContDiff ℝ 1 F)
    (hdF : ∀ x, extDeriv F x = 0) {φ : ℝ → ℝ} (hφ : ContDiff ℝ 1 φ)
    (hφc : HasCompactSupport φ) (hφ' : ∀ t, 0 ≤ t → deriv φ t ≤ 0) :
    ∫ x, φ (‖x‖ ^ 2) * ⟪J.kahlerForm, (alternatingFormEquiv V 2).symm (F x)⟫ ≤
      ∫ x, -deriv φ (‖x‖ ^ 2) * ‖x‖ ^ 2 *
        (⟪J.kahlerForm, (alternatingFormEquiv V 2).symm (F x)⟫ / 2 +
          ‖(2⁻¹ : ℝ) • ((alternatingFormEquiv V 2).symm (F x) -
            o.hodgeStar hkl ((alternatingFormEquiv V 2).symm (F x)))‖ / √2) := by
  rw [integral_mul_inner_kahlerForm_eq h₀ h₂ hF hdF hφ hφc]
  -- Both integrands are continuous and vanish outside the support of `x ↦ φ'(‖x‖²)`.
  have := hφ.continuous_deriv le_rfl
  have hcc : HasCompactSupport fun x : V ↦ deriv φ (‖x‖ ^ 2) := hφc.deriv.comp_norm_sq
  have hFc := hF.continuous
  have hJc : Continuous fun x : V ↦ J x := J.toLinearMap.continuous_of_finiteDimensional
  have hF₂ : Continuous fun x ↦ (alternatingFormEquiv V 2).symm (F x) :=
    (alternatingFormEquiv V 2).symm.toLinearMap.continuous_of_finiteDimensional.comp hFc
  have hS : Continuous fun x ↦ o.hodgeStar hkl ((alternatingFormEquiv V 2).symm (F x)) :=
    (o.hodgeStar hkl).toLinearMap.continuous_of_finiteDimensional.comp hF₂
  refine integral_mono (Continuous.integrable_of_hasCompactSupport (by fun_prop) hcc.mul_right)
    (Continuous.integrable_of_hasCompactSupport (by fun_prop) hcc.neg.mul_right.mul_right)
    fun x ↦ ?_
  set F₂ := (alternatingFormEquiv V 2).symm (F x)
  -- Pointwise, `F(x, J x) = B(x, x) ≥ (⟪ω, F⟫ / 2 - ‖F⁻‖ / √2) ‖x‖²`.
  have hBx : J.hermitianForm F₂ x x = F x ![x, J x] := by
    rw [hermitianForm_apply_self, inner_alternatingFormEquiv_symm_ιMulti]
  have hb := (abs_le.1 (abs_hermitianForm_apply_self_sub_le h₀ h₂ hkl he F₂ x)).1
  rw [hBx] at hb
  have hd : 0 ≤ -deriv φ (‖x‖ ^ 2) := neg_nonneg.2 (hφ' _ (by positivity))
  nlinarith [mul_le_mul_of_nonneg_left hb hd]

end TauCeti
