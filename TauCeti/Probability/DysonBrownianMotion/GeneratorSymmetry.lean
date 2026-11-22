/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import TauCeti.Probability.DysonBrownianMotion.Lyapunov
public import TauCeti.Probability.RandomMatrices.BetaEnsemble.Hermite
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import TauCeti.Analysis.Calculus.FDeriv.DiagonalQuadratic
import TauCeti.Topology.Constructions.Pi

/-!
# Symmetry of the Ornstein–Uhlenbeck Dyson generator for the Hermite beta weight

The Ornstein–Uhlenbeck Dyson system of size `n` and parameter `β` adds the confining drift
`-xᵢ / 2` to the Dyson system, so its generator is
`dysonOUGenerator β n f x = (β n)⁻¹ ∑ᵢ ∂ᵢ² f x + ∑ᵢ (dysonDrift n x i - xᵢ / 2) ∂ᵢ f x`.
Off the collision hyperplanes the Hermite beta weight
`p x = exp (-(β n / 4) ∑ᵢ xᵢ²) ∏_{i<j} |xᵢ - xⱼ| ^ β` is
`exp (β logVandermonde n x - (β n / 4) ∑ᵢ xᵢ²)`, so its logarithmic gradient is `β n` times the
drift: `∂ᵢ p = β n (dysonDrift n x i - xᵢ / 2) p` (`hasFDerivAt_hermiteBetaWeight`). Hence the
generator is in divergence form, `p · dysonOUGenerator β n f = (β n)⁻¹ ∑ᵢ ∂ᵢ (p ∂ᵢ f)`
(`hermiteBetaWeight_mul_dysonOUGenerator`).

Integrating by parts against test functions `f` that are `C²` with compact support off the
collision hyperplanes gives the Dirichlet form identity
`∫ g · dysonOUGenerator β n f · p = -(β n)⁻¹ ∫ ⟨∇g, ∇f⟩ p`
for every `g` that is `C¹` off the collision hyperplanes, with no boundary terms because `f`
vanishes near the walls (`integral_mul_dysonOUGenerator_mul_hermiteBetaWeight`). For the Hermite
beta ensemble this says that the generator is symmetric
(`integral_mul_dysonOUGenerator_hermiteBetaEnsemble_comm`) and annihilates the ensemble,
`∫ dysonOUGenerator β n f d(hermiteBetaEnsemble β n) = 0`
(`integral_dysonOUGenerator_hermiteBetaEnsemble`): the ensemble is infinitesimally invariant for the
Ornstein–Uhlenbeck Dyson system, tested on functions supported off the collision hyperplanes.
Passing from this to invariance of the law of the process needs the stochastic dynamics and is
not done here.

## Main declarations

* `TauCeti.Probability.dysonOUGenerator`: the Ornstein–Uhlenbeck Dyson generator, with
  `TauCeti.Probability.dysonOUGenerator_eq_dysonGenerator_sub`.
* `TauCeti.Probability.hermiteBetaWeight_eq_exp_logVandermonde`,
  `TauCeti.Probability.contDiffAt_hermiteBetaWeight` and
  `TauCeti.Probability.hasFDerivAt_hermiteBetaWeight`: the weight off the collision hyperplanes.
* `TauCeti.Probability.hermiteBetaWeight_mul_dysonOUGenerator`: the divergence form.
* `TauCeti.Probability.integral_mul_dysonOUGenerator_mul_hermiteBetaWeight` and
  `TauCeti.Probability.integral_mul_dysonOUGenerator_hermiteBetaEnsemble`: integration by parts.
* `TauCeti.Probability.integral_mul_dysonOUGenerator_hermiteBetaEnsemble_comm` and
  `TauCeti.Probability.integral_dysonOUGenerator_hermiteBetaEnsemble`: symmetry and infinitesimal
  invariance.

## References

* G. W. Anderson, A. Guionnet, O. Zeitouni, *An Introduction to Random Matrices*, Cambridge
  University Press, 2010, §4.3.1 and the proof of Lemma 4.3.17.
-/

public section

open MeasureTheory Filter Topology
open ContinuousLinearMap (proj)

namespace TauCeti.Probability

variable {β : ℝ} {n : ℕ}

/-! ### The Ornstein–Uhlenbeck Dyson generator -/

/-- **The generator of the Ornstein–Uhlenbeck Dyson system** of size `n` and parameter `β`, applied
to `f : (Fin n → ℝ) → ℝ` at `x`: the diffusion term `(β n)⁻¹ ∑ᵢ ∂ᵢ² f x` plus the transport term
`∑ᵢ (dysonDrift n x i - xᵢ / 2) ∂ᵢ f x`. Partial derivatives are those of `fderiv` along the
coordinate vectors `Pi.single i 1`, as for `dysonGenerator`. -/
noncomputable def dysonOUGenerator (β : ℝ) (n : ℕ) (f : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) : ℝ :=
  (β * n)⁻¹ * ∑ i, fderiv ℝ (fderiv ℝ f) x (Pi.single i 1) (Pi.single i 1) +
    ∑ i, (dysonDrift n x i - x i / 2) * fderiv ℝ f x (Pi.single i 1)

/-- Unfolding `dysonOUGenerator`. -/
theorem dysonOUGenerator_def (f : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) :
    dysonOUGenerator β n f x =
      (β * n)⁻¹ * ∑ i, fderiv ℝ (fderiv ℝ f) x (Pi.single i 1) (Pi.single i 1) +
        ∑ i, (dysonDrift n x i - x i / 2) * fderiv ℝ f x (Pi.single i 1) :=
  (rfl)

/-- The Ornstein–Uhlenbeck Dyson generator is the Dyson generator plus the transport term of the
confining drift `-xᵢ / 2`. -/
theorem dysonOUGenerator_eq_dysonGenerator_sub (f : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) :
    dysonOUGenerator β n f x =
      dysonGenerator β n f x - ∑ i, x i / 2 * fderiv ℝ f x (Pi.single i 1) := by
  simp only [dysonOUGenerator_def, dysonGenerator_def, sub_mul, Finset.sum_sub_distrib]
  ring

/-- The Ornstein–Uhlenbeck Dyson generator of `f` vanishes outside the closed support of `f`. -/
theorem dysonOUGenerator_of_notMem_tsupport {f : (Fin n → ℝ) → ℝ} {x : Fin n → ℝ}
    (hx : x ∉ tsupport f) : dysonOUGenerator β n f x = 0 := by
  have h₂ : fderiv ℝ (fderiv ℝ f) x = 0 :=
    fderiv_of_notMem_tsupport ℝ fun h ↦ hx (tsupport_fderiv_subset ℝ h)
  simp [dysonOUGenerator_def, fderiv_of_notMem_tsupport ℝ hx, h₂]

/-! ### The Hermite beta weight off the collision hyperplanes -/

/-- Off the collision hyperplanes, the Hermite beta weight is
`exp (β ∑_{i<j} log (xᵢ - xⱼ) - (β n / 4) ∑ᵢ xᵢ²)`. -/
theorem hermiteBetaWeight_eq_exp_logVandermonde {x : Fin n → ℝ} (hx : Function.Injective x) :
    hermiteBetaWeight β n x = Real.exp (β * logVandermonde n x - β * n / 4 * ∑ i, x i ^ 2) := by
  rw [hermiteBetaWeight_def, logVandermonde_def, sub_eq_neg_add, Real.exp_add, neg_mul]
  congr 1
  rw [Finset.mul_sum, Real.exp_sum]
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  rw [Finset.mul_sum, Real.exp_sum]
  refine Finset.prod_congr rfl fun j hj ↦ ?_
  rw [Real.rpow_def_of_pos (abs_pos.2 (sub_ne_zero.2 (hx.ne (Finset.mem_Ioi.1 hj).ne))),
    Real.log_abs, mul_comm]

/-- Near a configuration with distinct coordinates, the Hermite beta weight agrees with
`exp (β logVandermonde n y - (β n / 4) ∑ᵢ yᵢ²)`. -/
private theorem hermiteBetaWeight_eventuallyEq_exp {x : Fin n → ℝ} (hx : Function.Injective x) :
    hermiteBetaWeight β n =ᶠ[𝓝 x]
      fun y ↦ Real.exp (β * logVandermonde n y - β * n / 4 * ∑ i, y i ^ 2) :=
  mem_of_superset (TauCeti.isOpen_setOf_injective.mem_nhds hx) fun _ hy ↦
    hermiteBetaWeight_eq_exp_logVandermonde hy

/-- The Hermite beta weight is smooth of every order off the collision hyperplanes. -/
theorem contDiffAt_hermiteBetaWeight {x : Fin n → ℝ} (hx : Function.Injective x)
    {k : WithTop ℕ∞} : ContDiffAt ℝ k (hermiteBetaWeight β n) x := by
  refine ContDiffAt.congr_of_eventuallyEq ?_ (hermiteBetaWeight_eventuallyEq_exp hx)
  exact (((contDiffAt_logVandermonde hx).const_smul β).sub ((ContDiffAt.sum fun i _ ↦
    (contDiffAt_apply ℝ (fun _ ↦ ℝ) i x).pow 2).const_smul (β * n / 4))).exp

/-- **The gradient of the Hermite beta weight.** Off the collision hyperplanes,
`∂ᵢ p = β n (dysonDrift n x i - xᵢ / 2) p` for the Hermite beta weight `p`: its logarithmic
gradient is `β n` times the Ornstein–Uhlenbeck Dyson drift. -/
theorem hasFDerivAt_hermiteBetaWeight {x : Fin n → ℝ} (hx : Function.Injective x) :
    HasFDerivAt (hermiteBetaWeight β n)
      (∑ i, (β * n * (dysonDrift n x i - x i / 2) * hermiteBetaWeight β n x) •
        (proj i : (Fin n → ℝ) →L[ℝ] ℝ)) x := by
  have h := (((hasFDerivAt_logVandermonde hx).const_smul β).sub
    ((hasFDerivAt_sum_sq x).const_smul (β * n / 4))).exp
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    ← hermiteBetaWeight_eq_exp_logVandermonde hx] at h
  refine (h.congr_of_eventuallyEq (hermiteBetaWeight_eventuallyEq_exp hx)).congr_fderiv ?_
  refine ContinuousLinearMap.ext fun v ↦ ?_
  simp only [smul_eq_mul, smul_apply, sub_apply, sum_apply, ContinuousLinearMap.proj_apply,
    Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ ↦ by ring

/-! ### The divergence form of the generator -/

/-- The derivative of `y ↦ p y ∂ᵢ f y` at a configuration with distinct coordinates, along the
coordinate vector `eᵢ`, for the Hermite beta weight `p` and `f` twice differentiable at `x`. -/
private theorem fderiv_hermiteBetaWeight_mul_fderiv_apply {f : (Fin n → ℝ) → ℝ}
    {x : Fin n → ℝ} (hx : Function.Injective x) (hf : ContDiffAt ℝ 2 f x) (i : Fin n) :
    fderiv ℝ (fun y ↦ hermiteBetaWeight β n y * fderiv ℝ f y (Pi.single i 1)) x
        (Pi.single i 1) =
      hermiteBetaWeight β n x * fderiv ℝ (fderiv ℝ f) x (Pi.single i 1) (Pi.single i 1) +
        fderiv ℝ f x (Pi.single i 1) *
          (β * n * (dysonDrift n x i - x i / 2) * hermiteBetaWeight β n x) := by
  have hd : HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) x) x :=
    ((hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by simp)).hasFDerivAt
  have h := (hasFDerivAt_hermiteBetaWeight (β := β) hx).fun_mul
    (hd.clm_apply (hasFDerivAt_const (Pi.single i (1 : ℝ)) x))
  rw [h.fderiv]
  simp [Pi.single_apply]

/-- **The divergence form of the Ornstein–Uhlenbeck Dyson generator.** At a configuration with
distinct coordinates, for the Hermite beta weight `p` and `f` twice differentiable there,
`p · dysonOUGenerator β n f = (β n)⁻¹ ∑ᵢ ∂ᵢ (p ∂ᵢ f)`. -/
theorem hermiteBetaWeight_mul_dysonOUGenerator (hβ : β ≠ 0) {f : (Fin n → ℝ) → ℝ}
    {x : Fin n → ℝ} (hx : Function.Injective x) (hf : ContDiffAt ℝ 2 f x) :
    hermiteBetaWeight β n x * dysonOUGenerator β n f x =
      (β * n)⁻¹ * ∑ i, fderiv ℝ (fun y ↦ hermiteBetaWeight β n y * fderiv ℝ f y (Pi.single i 1))
        x (Pi.single i 1) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [dysonOUGenerator_def]
  have : β * n ≠ 0 := mul_ne_zero hβ (Nat.cast_ne_zero.2 hn.ne')
  simp_rw [fderiv_hermiteBetaWeight_mul_fderiv_apply hx hf, dysonOUGenerator_def,
    Finset.sum_add_distrib, mul_add, Finset.mul_sum]
  congr 1
  · exact Finset.sum_congr rfl fun i _ ↦ by ring
  · refine Finset.sum_congr rfl fun i _ ↦ ?_
    field_simp

/-! ### Integration by parts -/

/-- The flux `y ↦ p y ∂ᵢ f y` is supported in the closed support of `f`. -/
private theorem tsupport_hermiteBetaWeight_mul_fderiv_subset (f : (Fin n → ℝ) → ℝ) (i : Fin n) :
    tsupport (fun y ↦ hermiteBetaWeight β n y * fderiv ℝ f y (Pi.single i 1)) ⊆ tsupport f := by
  refine closure_minimal (fun y hy ↦ ?_) (isClosed_tsupport f)
  refine support_fderiv_subset ℝ fun h ↦ hy ?_
  simp [show fderiv ℝ f y = 0 from h]

/-- The flux `y ↦ p y ∂ᵢ f y` of a `C²` function `f` is `C¹` off the collision hyperplanes. -/
private theorem contDiffOn_hermiteBetaWeight_mul_fderiv {f : (Fin n → ℝ) → ℝ}
    (hf : ContDiff ℝ 2 f) (i : Fin n) :
    ContDiffOn ℝ 1 (fun y ↦ hermiteBetaWeight β n y * fderiv ℝ f y (Pi.single i 1))
      {x | Function.Injective x} := fun y hy ↦
  ((contDiffAt_hermiteBetaWeight hy).mul
    ((hf.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const).contDiffAt).contDiffWithinAt

/-- If the closed support of `f` avoids the collision hyperplanes, the flux `y ↦ p y ∂ᵢ f y` of a
`C²` function `f` is differentiable everywhere. -/
private theorem differentiableAt_hermiteBetaWeight_mul_fderiv {f : (Fin n → ℝ) → ℝ}
    (hf : ContDiff ℝ 2 f) (hfD : tsupport f ⊆ {x | Function.Injective x}) (i : Fin n)
    (y : Fin n → ℝ) :
    DifferentiableAt ℝ (fun y ↦ hermiteBetaWeight β n y * fderiv ℝ f y (Pi.single i 1)) y := by
  by_cases hy : y ∈ tsupport f
  · exact ((contDiffOn_hermiteBetaWeight_mul_fderiv hf i).contDiffAt
      (TauCeti.isOpen_setOf_injective.mem_nhds (hfD hy))).differentiableAt one_ne_zero
  · have h := (notMem_tsupport_iff_eventuallyEq.1 fun h ↦
      hy (tsupport_hermiteBetaWeight_mul_fderiv_subset (β := β) f i h))
    exact (differentiableAt_const (0 : ℝ)).congr_of_eventuallyEq h

/-- The three products entering the integration by parts of `g` against the flux
`V = p ∂ᵢ f` are integrable: `∂ᵢ g · V`, `g · ∂ᵢ V` and `g · V`. -/
private theorem integrable_flux {f g : (Fin n → ℝ) → ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hfD : tsupport f ⊆ {x | Function.Injective x})
    (hg : ContDiffOn ℝ 1 g {x | Function.Injective x}) (i : Fin n) :
    (Integrable fun x ↦ fderiv ℝ g x (Pi.single i 1) *
        (hermiteBetaWeight β n x * fderiv ℝ f x (Pi.single i 1))) ∧
      (Integrable fun x ↦ g x * fderiv ℝ
        (fun y ↦ hermiteBetaWeight β n y * fderiv ℝ f y (Pi.single i 1)) x (Pi.single i 1)) ∧
      (Integrable fun x ↦ g x * (hermiteBetaWeight β n x * fderiv ℝ f x (Pi.single i 1))) := by
  set V : (Fin n → ℝ) → ℝ := fun y ↦ hermiteBetaWeight β n y * fderiv ℝ f y (Pi.single i 1)
  have hD : IsOpen {x : Fin n → ℝ | Function.Injective x} := TauCeti.isOpen_setOf_injective
  have hVs : Function.support V ⊆ tsupport f :=
    (subset_tsupport V).trans (tsupport_hermiteBetaWeight_mul_fderiv_subset f i)
  have hV : ContDiffOn ℝ 1 V {x | Function.Injective x} :=
    contDiffOn_hermiteBetaWeight_mul_fderiv hf i
  have hV' : ContinuousOn (fun x ↦ fderiv ℝ V x (Pi.single i 1)) {x | Function.Injective x} :=
    (hV.continuousOn_fderiv_of_isOpen hD le_rfl).clm_apply continuousOn_const
  have hg' : ContinuousOn (fun x ↦ fderiv ℝ g x (Pi.single i 1)) {x | Function.Injective x} :=
    (hg.continuousOn_fderiv_of_isOpen hD le_rfl).clm_apply continuousOn_const
  -- Each product is continuous off the collision hyperplanes and supported in the compact set
  -- `tsupport f`, which avoids them.
  have hint {h : (Fin n → ℝ) → ℝ} (hh : ContinuousOn h {x | Function.Injective x})
      (hs : Function.support h ⊆ tsupport f) : Integrable h :=
    (integrableOn_iff_integrable_of_support_subset hs).1 ((hh.mono hfD).integrableOn_compact hfc)
  refine ⟨hint (hg'.mul hV.continuousOn) ((Function.support_mul_subset_right _ _).trans hVs),
    hint (hg.continuousOn.mul hV') ((Function.support_mul_subset_right _ _).trans fun x hx ↦ ?_),
    hint (hg.continuousOn.mul hV.continuousOn)
      ((Function.support_mul_subset_right _ _).trans hVs)⟩
  refine tsupport_hermiteBetaWeight_mul_fderiv_subset (β := β) f i
    (support_fderiv_subset ℝ fun h ↦ hx ?_)
  simp [show fderiv ℝ V x = 0 from h]

/-- Integration by parts of `g` against one flux term `∂ᵢ (p ∂ᵢ f)`. -/
private theorem integral_mul_fderiv_hermiteBetaWeight_mul_fderiv {f g : (Fin n → ℝ) → ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hfD : tsupport f ⊆ {x | Function.Injective x})
    (hg : ContDiffOn ℝ 1 g {x | Function.Injective x}) (i : Fin n) :
    ∫ x, g x * fderiv ℝ (fun y ↦ hermiteBetaWeight β n y * fderiv ℝ f y (Pi.single i 1)) x
        (Pi.single i 1) =
      -∫ x, fderiv ℝ g x (Pi.single i 1) *
        (hermiteBetaWeight β n x * fderiv ℝ f x (Pi.single i 1)) := by
  obtain ⟨h₁, h₂, h₃⟩ := integrable_flux (β := β) hf hfc hfD hg i
  refine integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable h₁ h₂ h₃ (fun x hx ↦ ?_)
    (fun x _ ↦ differentiableAt_hermiteBetaWeight_mul_fderiv hf hfD i x)
  have hx' := hfD (tsupport_hermiteBetaWeight_mul_fderiv_subset f i hx)
  exact (hg.differentiableOn one_ne_zero x hx').differentiableAt
    (TauCeti.isOpen_setOf_injective.mem_nhds hx')

/-- **Integration by parts for the Ornstein–Uhlenbeck Dyson generator.** Let `f` be `C²` with
compact support avoiding the collision hyperplanes, and let `g` be `C¹` off the collision
hyperplanes. Then, against the Hermite beta weight `p`,
`∫ g · dysonOUGenerator β n f · p = -(β n)⁻¹ ∫ (∑ᵢ ∂ᵢ g ∂ᵢ f) p`. -/
theorem integral_mul_dysonOUGenerator_mul_hermiteBetaWeight (hβ : β ≠ 0)
    {f g : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hfD : tsupport f ⊆ {x | Function.Injective x})
    (hg : ContDiffOn ℝ 1 g {x | Function.Injective x}) :
    ∫ x, g x * dysonOUGenerator β n f x * hermiteBetaWeight β n x =
      -(β * n)⁻¹ * ∫ x, (∑ i, fderiv ℝ g x (Pi.single i 1) * fderiv ℝ f x (Pi.single i 1)) *
        hermiteBetaWeight β n x := by
  -- Pointwise, the integrand is `(β n)⁻¹ ∑ᵢ g ∂ᵢ (p ∂ᵢ f)`: by the divergence form on the
  -- collision-free set, and because both sides vanish outside the closed support of `f`.
  have hpt : ∀ x, g x * dysonOUGenerator β n f x * hermiteBetaWeight β n x =
      (β * n)⁻¹ * ∑ i, g x * fderiv ℝ
        (fun y ↦ hermiteBetaWeight β n y * fderiv ℝ f y (Pi.single i 1)) x (Pi.single i 1) := by
    intro x
    by_cases hx : x ∈ tsupport f
    · rw [mul_assoc, mul_comm (dysonOUGenerator β n f x),
        hermiteBetaWeight_mul_dysonOUGenerator hβ (hfD hx) hf.contDiffAt, ← Finset.mul_sum]
      ring
    · have h : ∀ i, fderiv ℝ (fun y ↦ hermiteBetaWeight β n y * fderiv ℝ f y (Pi.single i 1))
          x = 0 := fun i ↦ fderiv_of_notMem_tsupport ℝ fun h ↦
        hx (tsupport_hermiteBetaWeight_mul_fderiv_subset f i h)
      simp [dysonOUGenerator_of_notMem_tsupport hx, h]
  rw [integral_congr_ae (.of_forall hpt), integral_const_mul,
    integral_finsetSum _ fun i _ ↦ (integrable_flux (β := β) hf hfc hfD hg i).2.1]
  simp_rw [integral_mul_fderiv_hermiteBetaWeight_mul_fderiv hf hfc hfD hg, Finset.sum_neg_distrib,
    ← integral_finsetSum _ fun i _ ↦ (integrable_flux (β := β) hf hfc hfD hg i).1, mul_neg,
    neg_mul, Finset.sum_mul]
  congr 2
  exact integral_congr_ae (.of_forall fun x ↦ Finset.sum_congr rfl fun i _ ↦ by ring)

/-! ### The Hermite beta ensemble -/

/-- **Integration by parts against the Hermite beta ensemble.** Let `f` be `C²` with compact
support avoiding the collision hyperplanes, and let `g` be `C¹` off the collision hyperplanes.
Then `∫ g · dysonOUGenerator β n f = -(β n)⁻¹ ∫ ∑ᵢ ∂ᵢ g ∂ᵢ f` against `hermiteBetaEnsemble β n`. -/
theorem integral_mul_dysonOUGenerator_hermiteBetaEnsemble
    {f g : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hfD : tsupport f ⊆ {x | Function.Injective x})
    (hg : ContDiffOn ℝ 1 g {x | Function.Injective x}) :
    ∫ x, g x * dysonOUGenerator β n f x ∂hermiteBetaEnsemble β n =
      -(β * n)⁻¹ * ∫ x, ∑ i, fderiv ℝ g x (Pi.single i 1) * fderiv ℝ f x (Pi.single i 1)
        ∂hermiteBetaEnsemble β n := by
  -- For `β = 0` and `n ≠ 0` the ensemble is the zero measure; for `n = 0` both sides vanish.
  rcases eq_or_ne β 0 with rfl | hβ
  · rcases eq_or_ne n 0 with rfl | hn
    · simp [dysonOUGenerator_def]
    · simp [hermiteBetaEnsemble_zero_left hn]
  have key := integral_mul_dysonOUGenerator_mul_hermiteBetaWeight hβ hf hfc hfD hg
  simp_rw [integral_hermiteBetaEnsemble_eq_integral_smul, hermiteBetaPDFReal_def, smul_eq_mul,
    mul_assoc, integral_const_mul]
  simp_rw [mul_comm (hermiteBetaWeight β n _)]
  rw [key]
  ring

/-- **The Ornstein–Uhlenbeck Dyson generator is symmetric for the Hermite beta ensemble**: for
`C²` functions `f` and `g` with compact supports avoiding the collision hyperplanes,
`∫ g · dysonOUGenerator β n f = ∫ f · dysonOUGenerator β n g`. -/
theorem integral_mul_dysonOUGenerator_hermiteBetaEnsemble_comm
    {f g : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hfD : tsupport f ⊆ {x | Function.Injective x}) (hg : ContDiff ℝ 2 g)
    (hgc : HasCompactSupport g) (hgD : tsupport g ⊆ {x | Function.Injective x}) :
    ∫ x, g x * dysonOUGenerator β n f x ∂hermiteBetaEnsemble β n =
      ∫ x, f x * dysonOUGenerator β n g x ∂hermiteBetaEnsemble β n := by
  rw [integral_mul_dysonOUGenerator_hermiteBetaEnsemble hf hfc hfD
      (hg.of_le one_le_two).contDiffOn,
    integral_mul_dysonOUGenerator_hermiteBetaEnsemble hg hgc hgD
      (hf.of_le one_le_two).contDiffOn]
  simp_rw [mul_comm (fderiv ℝ g _ _)]

/-- **Infinitesimal invariance of the Hermite beta ensemble** for the Ornstein–Uhlenbeck Dyson
system: for every `C²` function `f` with compact support avoiding the collision hyperplanes,
`∫ dysonOUGenerator β n f d(hermiteBetaEnsemble β n) = 0`. -/
theorem integral_dysonOUGenerator_hermiteBetaEnsemble {f : (Fin n → ℝ) → ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hfD : tsupport f ⊆ {x | Function.Injective x}) :
    ∫ x, dysonOUGenerator β n f x ∂hermiteBetaEnsemble β n = 0 := by
  simpa using integral_mul_dysonOUGenerator_hermiteBetaEnsemble hf hfc hfD
    (g := fun _ ↦ 1) contDiffOn_const

end TauCeti.Probability
