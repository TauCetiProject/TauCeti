/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.Measure.Haar.Basic
public import Mathlib.Topology.Algebra.Module.Determinant
public import TauCeti.Analysis.Distribution.TemperateGrowth
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.MeasureTheory.Function.Jacobian
import TauCeti.Analysis.Calculus.ContDiff.FaaDiBruno
import TauCeti.Analysis.Calculus.FDeriv.Equiv
import TauCeti.Topology.Algebra.Module.Determinant

/-!
# Pushforward of Schwartz densities along a change of variables

Let `φ : E ≃ E` be a bijection of a finite-dimensional real normed space such that `φ` and `φ⁻¹`
both have temperate growth: they are smooth and all their derivatives grow at most polynomially.
Examples are diffeomorphisms whose derivatives of positive order, and those of their inverses, are
bounded, and polynomial automorphisms such as the shear `(x, y) ↦ (x, y + x³)` of `ℝ²`.

The **pushforward** of a Schwartz function `f`, regarded as a density, is

`(φ_* f)(y) = |det Dφ⁻¹(y)| f(φ⁻¹ y)`.

It is a continuous linear map of Schwartz space (`SchwartzMap.pushforwardCLM`): composition with
`φ⁻¹` is Mathlib's `SchwartzMap.compCLM`, and the Jacobian factor has temperate growth. By the
change of variables formula it is the transpose of composition with `φ`:

`∫ (φ_* f)(y) • u(y) dμ(y) = ∫ f(x) • u(φ x) dμ(x)`

for every function `u` and every additive Haar measure `μ`
(`SchwartzMap.integral_pushforwardCLM_smul`). This is how tempered distributions are pulled back
along `φ`, by transposition.

The pushforward is functorial: `(χ ∘ φ)_* = χ_* ∘ φ_*` by the chain rule for the Jacobian
determinant (`SchwartzMap.pushforwardCLM_trans`), and the identity pushes forward to the identity
(`SchwartzMap.pushforwardCLM_refl`). Multiplication by `g ∘ φ` before the pushforward is
multiplication by `g` after it (`SchwartzMap.pushforwardCLM_smulLeftCLM`).

On a real inner product space, composition with `φ` is also the transpose of the pushforward for
the sesquilinear `L²` pairing, `∫ ⟪w ∘ φ, v⟫ = ∫ ⟪w, φ_* v⟫`
(`SchwartzMap.integral_inner_compCLM_eq`), and when `|det Dφ⁻¹| ≤ M` composition with `φ` is
bounded on `L²`: `∫ ‖u ∘ φ‖² ≤ M ∫ ‖u‖²` (`SchwartzMap.integral_norm_comp_sq_le`). The
derivatives of `u ∘ g` along an orthonormal basis `b` follow the chain rule
`∂_{bᵢ} (u ∘ g) = ∑ⱼ ⟪bⱼ, Dg(·) bᵢ⟫ (∂_{bⱼ} u) ∘ g` (`SchwartzMap.lineDerivOp_compCLM`). When the
derivatives of positive order of `g` are bounded, so are all derivatives of the coefficients
`⟪bⱼ, Dg(·) bᵢ⟫` (`Function.HasTemperateGrowth.exists_norm_iteratedFDeriv_inner_fderiv_apply_le`),
and when those of `φ⁻¹` are bounded, so are all derivatives of the Jacobian factor `|det Dφ⁻¹|`
(`Function.HasTemperateGrowth.exists_norm_iteratedFDeriv_abs_det_fderiv_symm_le`). These are the
inputs of the Sobolev estimates for changes of variables in
`TauCeti.Analysis.Sobolev.BesselPotential.ChangeOfVariables`.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, §6.1 and §7.1.
-/

public noncomputable section

open MeasureTheory

namespace SchwartzMap

variable (𝕜 : Type*) {E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace 𝕜 F]
  {φ : E ≃ E}

/-- The **pushforward of Schwartz densities** along a bijection `φ` such that `φ` and `φ⁻¹` have
temperate growth: `(φ_* f)(y) = |det Dφ⁻¹(y)| f(φ⁻¹ y)`, as a continuous linear map of Schwartz
space. It is the transpose of composition with `φ`
(`SchwartzMap.integral_pushforwardCLM_smul`). -/
def pushforwardCLM (φ : E ≃ E) (hφ : (φ : E → E).HasTemperateGrowth)
    (hψ : (φ.symm : E → E).HasTemperateGrowth) : 𝓢(E, F) →L[𝕜] 𝓢(E, F) :=
  smulLeftCLM F (fun y ↦ ((|(fderiv ℝ φ.symm y).det| : ℝ) : 𝕜)) ∘L
    compCLM 𝕜 hψ (hφ.exists_norm_le_of_leftInverse φ.right_inv)

@[simp]
theorem pushforwardCLM_apply (hφ : (φ : E → E).HasTemperateGrowth)
    (hψ : (φ.symm : E → E).HasTemperateGrowth) (f : 𝓢(E, F)) (y : E) :
    pushforwardCLM 𝕜 φ hφ hψ f y = ((|(fderiv ℝ φ.symm y).det| : ℝ) : 𝕜) • f (φ.symm y) := by
  rw [pushforwardCLM, ContinuousLinearMap.comp_apply,
    smulLeftCLM_apply_apply (g := fun y ↦ ((|(fderiv ℝ φ.symm y).det| : ℝ) : 𝕜))
      ((RCLike.hasTemperateGrowth_ofReal 𝕜).comp (hφ.abs_det_fderiv_symm hψ)), compCLM_apply,
    Function.comp_apply]

/-- **The pushforward is the transpose of composition.** For every function `u` and every
additive Haar measure `μ`, `∫ (φ_* f)(y) • u(y) dμ(y) = ∫ f(x) • u(φ x) dμ(x)`. No integrability
is needed: both sides are the two sides of the change of variables formula. -/
theorem integral_pushforwardCLM_smul {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedSpace 𝕜 G] [IsScalarTower ℝ 𝕜 G] [MeasurableSpace E] [BorelSpace E] (μ : Measure E)
    [μ.IsAddHaarMeasure] (hφ : (φ : E → E).HasTemperateGrowth)
    (hψ : (φ.symm : E → E).HasTemperateGrowth) (f : 𝓢(E, 𝕜)) (u : E → G) :
    ∫ y, pushforwardCLM 𝕜 φ hφ hψ f y • u y ∂μ = ∫ x, f x • u (φ x) ∂μ := by
  have hcv := integral_image_eq_integral_abs_det_fderiv_smul μ MeasurableSet.univ
    (fun y _ ↦ (hψ.1.differentiable (by simp) y).hasFDerivAt.hasFDerivWithinAt)
    φ.symm.injective.injOn fun x ↦ f x • u (φ x)
  rw [Set.image_univ_of_surjective φ.symm.surjective] at hcv
  simp only [Measure.restrict_univ, Equiv.apply_symm_apply] at hcv
  rw [hcv]
  congr 1 with y
  rw [pushforwardCLM_apply, smul_assoc, RCLike.real_smul_eq_coe_smul (K := 𝕜)]

/-- **Functoriality of the pushforward**: `(χ ∘ φ)_* = χ_* ∘ φ_*`, by the chain rule for the
Jacobian determinant. -/
theorem pushforwardCLM_trans {χ : E ≃ E} (hφ : (φ : E → E).HasTemperateGrowth)
    (hψ : (φ.symm : E → E).HasTemperateGrowth) (hχ : (χ : E → E).HasTemperateGrowth)
    (hχs : (χ.symm : E → E).HasTemperateGrowth) (h₁ : (φ.trans χ : E → E).HasTemperateGrowth)
    (h₂ : ((φ.trans χ).symm : E → E).HasTemperateGrowth) :
    pushforwardCLM 𝕜 (φ.trans χ) h₁ h₂ (F := F) =
      pushforwardCLM 𝕜 χ hχ hχs ∘L pushforwardCLM 𝕜 φ hφ hψ := by
  ext f y
  have hd : fderiv ℝ ((φ.trans χ).symm) y = fderiv ℝ φ.symm (χ.symm y) ∘L fderiv ℝ χ.symm y :=
    fderiv_comp y (hψ.1.differentiable (by simp) _) (hχs.1.differentiable (by simp) _)
  rw [ContinuousLinearMap.comp_apply, pushforwardCLM_apply, pushforwardCLM_apply,
    pushforwardCLM_apply, hd, ContinuousLinearMap.det_comp, abs_mul, RCLike.ofReal_mul, mul_comm,
    mul_smul, Equiv.symm_trans_apply]

/-- The pushforward along the identity is the identity. -/
@[simp]
theorem pushforwardCLM_refl (h₁ : (Equiv.refl E : E → E).HasTemperateGrowth)
    (h₂ : ((Equiv.refl E).symm : E → E).HasTemperateGrowth) :
    pushforwardCLM 𝕜 (Equiv.refl E) h₁ h₂ (F := F) = ContinuousLinearMap.id 𝕜 _ := by
  ext f y
  simp

/-- Multiplying by `g ∘ φ` and then pushing forward along `φ` is pushing forward and then
multiplying by `g`. -/
theorem pushforwardCLM_smulLeftCLM (hφ : (φ : E → E).HasTemperateGrowth)
    (hψ : (φ.symm : E → E).HasTemperateGrowth) {g : E → 𝕜} (hg : g.HasTemperateGrowth)
    (f : 𝓢(E, F)) :
    pushforwardCLM 𝕜 φ hφ hψ (smulLeftCLM F (g ∘ φ) f) =
      smulLeftCLM F g (pushforwardCLM 𝕜 φ hφ hψ f) := by
  ext y
  rw [pushforwardCLM_apply, smulLeftCLM_apply_apply (hg.comp hφ), smulLeftCLM_apply_apply hg,
    pushforwardCLM_apply, Function.comp_apply, Equiv.apply_symm_apply, smul_comm]

section InnerProduct

open scoped RealInnerProductSpace LineDeriv ContDiff

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℂ F] {g : E → E}

omit [NormedSpace ℂ F] in
/-- The coefficient `x ↦ ⟪w, Dg(x) v⟫` of the chain rule, as a complex function, is the
composition of `Dg` with a continuous linear functional. -/
private theorem coeff_eq (v w : E) :
    (fun x ↦ ((⟪w, fderiv ℝ g x v⟫ : ℝ) : ℂ)) =
      ((Complex.ofRealCLM.comp (innerSL ℝ w)).comp (ContinuousLinearMap.apply ℝ E v)) ∘
        fderiv ℝ g := by
  funext x
  simp

omit [NormedSpace ℂ F] in
/-- The coefficient `x ↦ ⟪w, Dg(x) v⟫` of the chain rule has temperate growth. -/
theorem _root_.Function.HasTemperateGrowth.inner_fderiv_apply (hg : g.HasTemperateGrowth)
    (v w : E) : (fun x ↦ ((⟪w, fderiv ℝ g x v⟫ : ℝ) : ℂ)).HasTemperateGrowth := by
  rw [coeff_eq]
  exact (ContinuousLinearMap.hasTemperateGrowth _).comp hg.fderiv

omit [NormedSpace ℂ F] in
/-- If the derivatives of `g` of positive order are bounded, then so are all derivatives of the
chain-rule coefficient `x ↦ ⟪w, Dg(x) v⟫`. -/
theorem _root_.Function.HasTemperateGrowth.exists_norm_iteratedFDeriv_inner_fderiv_apply_le
    (hg : g.HasTemperateGrowth) (hb : ∀ n, ∃ C, ∀ x, ‖iteratedFDeriv ℝ (n + 1) g x‖ ≤ C)
    (v w : E) (n : ℕ) :
    ∃ C, ∀ x, ‖iteratedFDeriv ℝ n (fun x ↦ ((⟪w, fderiv ℝ g x v⟫ : ℝ) : ℂ)) x‖ ≤ C := by
  obtain ⟨C, hC⟩ := hb n
  set L := (Complex.ofRealCLM.comp (innerSL ℝ w)).comp (ContinuousLinearMap.apply ℝ E v)
  refine ⟨‖L‖ * C, fun x ↦ ?_⟩
  rw [coeff_eq]
  refine (L.norm_iteratedFDeriv_comp_left hg.fderiv.1.contDiffAt (by simp)).trans ?_
  rw [norm_iteratedFDeriv_fderiv]
  exact mul_le_mul_of_nonneg_left (hC x) (norm_nonneg _)

/-- **The chain rule on Schwartz functions.** For a map `g` of temperate growth, polynomially
bounded below, and an orthonormal basis `b`, the derivative of `u ∘ g` along `bᵢ` is
`∑ⱼ ⟪bⱼ, Dg(·) bᵢ⟫ (∂_{bⱼ} u) ∘ g`. -/
theorem lineDerivOp_compCLM {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E)
    (hg : g.HasTemperateGrowth) (hg' : ∃ (k : ℕ) (C : ℝ), ∀ x, ‖x‖ ≤ C * (1 + ‖g x‖) ^ k)
    (u : 𝓢(E, F)) (i : ι) :
    ∂_{b i} (compCLM ℂ hg hg' u) =
      ∑ j, smulLeftCLM F (fun x ↦ ((⟪b j, fderiv ℝ g x (b i)⟫ : ℝ) : ℂ))
        (compCLM ℂ hg hg' (∂_{b j} u)) := by
  ext x
  rw [lineDerivOp_apply_eq_fderiv, sum_apply]
  simp only [smulLeftCLM_apply_apply (hg.inner_fderiv_apply _ _), compCLM_apply]
  rw [fderiv_comp x u.differentiableAt (hg.1.differentiable (by simp) x),
    ContinuousLinearMap.comp_apply]
  conv_lhs => rw [← b.sum_repr' (fderiv ℝ g x (b i))]
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [map_smul, Complex.coe_smul, Function.comp_apply, lineDerivOp_apply_eq_fderiv]

variable [FiniteDimensional ℝ E] {φ : E ≃ E}

omit [NormedSpace ℂ F] in
/-- If `φ` and `φ⁻¹` have temperate growth and the derivatives of `φ⁻¹` of positive order are
bounded, then the Jacobian factor `|det Dφ⁻¹|` has bounded derivatives of every order. -/
theorem _root_.Function.HasTemperateGrowth.exists_norm_iteratedFDeriv_abs_det_fderiv_symm_le
    (hφ : (φ : E → E).HasTemperateGrowth) (hψ : (φ.symm : E → E).HasTemperateGrowth)
    (hb : ∀ n, ∃ C, ∀ x, ‖iteratedFDeriv ℝ (n + 1) φ.symm x‖ ≤ C) (n : ℕ) :
    ∃ C, ∀ y, ‖iteratedFDeriv ℝ n (fun y ↦ ((|(fderiv ℝ φ.symm y).det| : ℝ) : ℂ)) y‖ ≤ C := by
  set d : E → ℝ := fun y ↦ (fderiv ℝ φ.symm y).det
  -- The determinant of the bounded smooth map `Dφ⁻¹` has bounded derivatives.
  obtain ⟨C, hC⟩ := ContinuousLinearMap.hasTemperateGrowth_det.1.exists_norm_iteratedFDeriv_comp_le
    hψ.fderiv.1 (fun m ↦ (hb m).imp fun C hC x ↦ by rw [norm_iteratedFDeriv_fderiv]; exact hC x) n
  -- `det Dφ⁻¹` has no zeros, hence a constant sign `ε`, and `|det Dφ⁻¹| = ε det Dφ⁻¹`.
  have h0 (y : E) : d y ≠ 0 := fun h ↦ by
    have h1 := φ.det_fderiv_symm_mul_det_fderiv (hφ.1.differentiable (by simp) (φ.symm y))
      (hψ.1.differentiable (by simp) y)
    rw [show (fderiv ℝ φ.symm y).det = d y from rfl, h, zero_mul] at h1
    exact zero_ne_one h1
  have hcont : Continuous d := hψ.det_fderiv.1.continuous
  obtain ⟨ε, hε⟩ : ∃ ε : ℝ, ∀ y, |d y| = ε * d y := by
    rcases (h0 0).lt_or_gt with hneg | hpos
    · refine ⟨-1, fun y ↦ ?_⟩
      have : d y < 0 := by
        by_contra! hy
        obtain ⟨z, hz⟩ := intermediate_value_univ 0 y hcont ⟨hneg.le, hy⟩
        exact h0 z hz
      simp [abs_of_neg this]
    · refine ⟨1, fun y ↦ ?_⟩
      have : 0 < d y := by
        by_contra! hy
        obtain ⟨z, hz⟩ := intermediate_value_univ y 0 hcont ⟨hy, hpos.le⟩
        exact h0 z hz
      simp [abs_of_pos this]
  have hJ : (fun y ↦ ((|(fderiv ℝ φ.symm y).det| : ℝ) : ℂ)) =
      (ε • Complex.ofRealCLM) ∘ ((fun A : E →L[ℝ] E ↦ A.det) ∘ fderiv ℝ φ.symm) := by
    funext y
    simp only [Function.comp_apply, smul_apply, Complex.ofRealCLM_apply,
      Complex.real_smul]
    rw [show (fderiv ℝ φ.symm y).det = d y from rfl, hε y]
    push_cast
    rfl
  refine ⟨‖ε • Complex.ofRealCLM‖ * C, fun y ↦ ?_⟩
  rw [hJ]
  exact ((ε • Complex.ofRealCLM).norm_iteratedFDeriv_comp_left
    ((ContinuousLinearMap.hasTemperateGrowth_det.1.comp hψ.fderiv.1).contDiffAt) (by simp)).trans
    (mul_le_mul_of_nonneg_left (hC y) (norm_nonneg _))

variable [MeasurableSpace E] [BorelSpace E]

omit [NormedSpace ℂ F] in
/-- **Change of variables in `L²`.** If `φ⁻¹` is smooth and `|det Dφ⁻¹| ≤ M`, then
`∫ ‖u ∘ φ‖² ≤ M ∫ ‖u‖²` for Schwartz functions `u`. -/
theorem integral_norm_comp_sq_le [NormedSpace ℝ F] (hψ : (φ.symm : E → E).HasTemperateGrowth)
    {M : ℝ} (hM : ∀ y, |(fderiv ℝ φ.symm y).det| ≤ M) (u : 𝓢(E, F)) :
    ∫ x, ‖u (φ x)‖ ^ 2 ≤ M * ∫ x, ‖u x‖ ^ 2 := by
  have hcv := integral_image_eq_integral_abs_det_fderiv_smul volume MeasurableSet.univ
    (fun y _ ↦ (hψ.1.differentiable (by simp) y).hasFDerivAt.hasFDerivWithinAt)
    φ.symm.injective.injOn fun x ↦ ‖u (φ x)‖ ^ 2
  rw [Set.image_univ_of_surjective φ.symm.surjective] at hcv
  simp only [Measure.restrict_univ, Equiv.apply_symm_apply, smul_eq_mul] at hcv
  rw [hcv, ← integral_const_mul]
  refine integral_mono_of_nonneg (.of_forall fun y ↦ by positivity)
    (((u.memLp 2).integrable_norm_pow two_ne_zero).const_mul M) (.of_forall fun y ↦ ?_)
  exact mul_le_mul_of_nonneg_right (hM y) (by positivity)

open scoped InnerProductSpace in
/-- **Composition with `φ` is the transpose of the pushforward of densities** for the `L²` pairing:
`∫ ⟪w ∘ φ, v⟫ = ∫ ⟪w, φ_* v⟫`, where `(φ_* v)(y) = |det Dφ⁻¹(y)| v(φ⁻¹ y)`. -/
theorem integral_inner_compCLM_eq {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    (hφ : (φ : E → E).HasTemperateGrowth) (hψ : (φ.symm : E → E).HasTemperateGrowth)
    (w v : 𝓢(E, F)) :
    ∫ x, ⟪compCLM ℂ hφ (hψ.exists_norm_le_of_leftInverse φ.left_inv) w x, v x⟫_ℂ =
      ∫ y, ⟪w y, pushforwardCLM ℂ φ hφ hψ v y⟫_ℂ := by
  have hcv := integral_image_eq_integral_abs_det_fderiv_smul volume MeasurableSet.univ
    (fun y _ ↦ (hψ.1.differentiable (by simp) y).hasFDerivAt.hasFDerivWithinAt)
    φ.symm.injective.injOn fun x ↦ ⟪w (φ x), v x⟫_ℂ
  rw [Set.image_univ_of_surjective φ.symm.surjective] at hcv
  simp only [Measure.restrict_univ, Equiv.apply_symm_apply] at hcv
  simp only [compCLM_apply, Function.comp_apply, pushforwardCLM_apply, inner_smul_right]
  rw [hcv]
  congr 1 with y

end InnerProduct

end SchwartzMap
