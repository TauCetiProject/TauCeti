/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Measure.Haar.Basic
public import Mathlib.Topology.Algebra.Module.Determinant
public import TauCeti.Analysis.Distribution.TemperateGrowth
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.LocallyConvex.SeparatingDual
import TauCeti.Analysis.Distribution.SchwartzSpace.Deriv
import TauCeti.MeasureTheory.Function.Jacobian.Equiv
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
multiplication by `g` after it (`SchwartzMap.pushforwardCLM_smulLeftCLM`), and continuous
real-linear maps on the values commute with the pushforward
(`SchwartzMap.pushforwardCLM_postcompCLM`).

The pushforward of a derivative is a sum of derivatives of pushforwards: for a basis `b` of `E`,

`φ_* (∂_v f) = ∑ᵢ ∂_{bᵢ} (φ_* (cᵢ f))`, where `Dφ(x) v = ∑ᵢ cᵢ(x) bᵢ`

(`SchwartzMap.pushforwardCLM_lineDerivOp`). This is the transpose of the chain rule
`∂_v (u ∘ φ)(x) = ∑ᵢ cᵢ(x) (∂_{bᵢ} u)(φ x)` (`SchwartzMap.lineDerivOp_compCLM_apply`), and it gives
the chain rule for the pullback of tempered distributions. It is proved by pairing both sides with
test functions and integrating by parts for scalar-valued `f`; the Jacobian factor of the
pushforward is never differentiated. Vector-valued `f` reduce to the real-valued case by applying
continuous linear functionals to the values.

Composition with `φ` is also the transpose of the pushforward for the sesquilinear `L²` pairing,
`∫ ⟪w ∘ φ, v⟫ dμ = ∫ ⟪w, φ_* v⟫ dμ` (`SchwartzMap.integral_inner_compCLM_eq`), an input of the
Sobolev estimates for changes of variables in
`TauCeti.Analysis.Sobolev.BesselPotential.ChangeOfVariables`.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, §6.1 and §7.1.
-/

public noncomputable section

open MeasureTheory
open scoped ContDiff LineDeriv

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
  have hcv := TauCeti.integral_comp_equiv_eq_integral_abs_det_fderiv_symm_smul μ
    (hψ.1.differentiable (by simp)) fun y ↦ f (φ.symm y) • u y
  simp only [Equiv.symm_apply_apply] at hcv
  rw [hcv]
  congr 1 with y
  rw [pushforwardCLM_apply, smul_assoc, RCLike.real_smul_eq_coe_smul (K := 𝕜)]

open scoped InnerProductSpace in
/-- **Composition with `φ` is the transpose of the pushforward of densities** for the `L²` pairing:
`∫ ⟪w ∘ φ, v⟫ dμ = ∫ ⟪w, φ_* v⟫ dμ` for every additive Haar measure `μ`, where
`(φ_* v)(y) = |det Dφ⁻¹(y)| v(φ⁻¹ y)`. -/
theorem integral_inner_compCLM_eq {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]
    (hφ : (φ : E → E).HasTemperateGrowth) (hψ : (φ.symm : E → E).HasTemperateGrowth)
    (w v : 𝓢(E, F)) :
    ∫ x, ⟪compCLM ℂ hφ (hψ.exists_norm_le_of_leftInverse φ.left_inv) w x, v x⟫_ℂ ∂μ =
      ∫ y, ⟪w y, pushforwardCLM ℂ φ hφ hψ v y⟫_ℂ ∂μ := by
  have hcv := TauCeti.integral_comp_equiv_eq_integral_abs_det_fderiv_symm_smul μ
    (hψ.1.differentiable (by simp)) fun y ↦ ⟪w y, v (φ.symm y)⟫_ℂ
  simp only [Equiv.symm_apply_apply] at hcv
  simp only [compCLM_apply, Function.comp_apply, pushforwardCLM_apply, inner_smul_right, hcv,
    RCLike.real_smul_eq_coe_mul (K := ℂ)]

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

/-- Pushing forward commutes with applying a continuous real-linear map to the values, because
the Jacobian factor is real. -/
theorem pushforwardCLM_postcompCLM {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    [IsScalarTower ℝ 𝕜 F] (L : F →L[ℝ] G)
    (hφ : (φ : E → E).HasTemperateGrowth) (hψ : (φ.symm : E → E).HasTemperateGrowth)
    (f : 𝓢(E, F)) :
    (pushforwardCLM 𝕜 φ hφ hψ f).postcompCLM L = pushforwardCLM ℝ φ hφ hψ (f.postcompCLM L) := by
  ext y
  rw [postcompCLM_apply, pushforwardCLM_apply, pushforwardCLM_apply, postcompCLM_apply,
    ← RCLike.real_smul_eq_coe_smul (K := 𝕜), map_smul, RCLike.ofReal_real_eq_id, id_eq]

section LineDeriv

variable {ι : Type*} [Fintype ι]

omit [FiniteDimensional ℝ E] in
/-- **The chain rule for composition with `φ`.** If `Dφ(x) v = ∑ᵢ cᵢ(x) bᵢ` in a basis `b`, then
`∂_v (u ∘ φ)(x) = ∑ᵢ cᵢ(x) (∂_{bᵢ} u)(φ x)`. -/
theorem lineDerivOp_compCLM_apply [IsScalarTower ℝ 𝕜 F] (b : Module.Basis ι ℝ E)
    (hφ : (φ : E → E).HasTemperateGrowth) (hψ : (φ.symm : E → E).HasTemperateGrowth)
    (u : 𝓢(E, F)) (v x : E) :
    ∂_{v} (compCLM 𝕜 hφ (hψ.exists_norm_le_of_leftInverse φ.left_inv) u) x =
      ∑ i, ((b.repr (fderiv ℝ φ x v) i : ℝ) : 𝕜) • (∂_{b i} u) (φ x) := by
  rw [lineDerivOp_apply_eq_fderiv, compCLM_apply,
    fderiv_comp x u.differentiableAt (hφ.1.differentiable (by simp) x),
    ContinuousLinearMap.comp_apply]
  calc fderiv ℝ u (φ x) (fderiv ℝ φ x v)
      = fderiv ℝ u (φ x) (∑ i, b.repr (fderiv ℝ φ x v) i • b i) := by rw [b.sum_repr]
    _ = _ := by
      simp only [map_sum, map_smul, RCLike.real_smul_eq_coe_smul (K := 𝕜),
        lineDerivOp_apply_eq_fderiv]

/-- The pushforward formula for a derivative, paired with a Schwartz function `u`: both sides are
`-∫ f x ∂_v (u ∘ φ)(x) dx` after the change of variables and integration by parts. -/
private theorem integral_pushforwardCLM_lineDerivOp_mul [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure] (b : Module.Basis ι ℝ E)
    (hφ : (φ : E → E).HasTemperateGrowth) (hψ : (φ.symm : E → E).HasTemperateGrowth)
    (f u : 𝓢(E, 𝕜)) (v : E) :
    ∫ y, pushforwardCLM 𝕜 φ hφ hψ (∂_{v} f) y * u y ∂μ =
      ∫ y, (∑ i, ∂_{b i} (pushforwardCLM 𝕜 φ hφ hψ
        (smulLeftCLM 𝕜 (fun x ↦ ((b.repr (fderiv ℝ φ x v) i : ℝ) : 𝕜)) f))) y * u y ∂μ := by
  set w : 𝓢(E, 𝕜) := compCLM 𝕜 hφ (hψ.exists_norm_le_of_leftInverse φ.left_inv) u
  set c : ι → E → 𝕜 := fun i x ↦ ((b.repr (fderiv ℝ φ x v) i : ℝ) : 𝕜)
  have hc (i : ι) : (c i).HasTemperateGrowth := hφ.basis_repr_fderiv_apply b v i
  have hint (i : ι) : Integrable (fun x ↦ c i x * f x * (∂_{b i} u) (φ x)) μ := by
    refine ((smulLeftCLM 𝕜 (c i) f).integrable (μ := μ)).mul_bdd
      ((∂_{b i} u).continuous.comp hφ.1.continuous).aestronglyMeasurable
      (c := SchwartzMap.seminorm ℝ 0 0 (∂_{b i} u)) (.of_forall fun x ↦ norm_le_seminorm ℝ _ _)
      |>.congr (.of_forall fun x ↦ ?_)
    simp [smulLeftCLM_apply_apply (hc i)]
  calc ∫ y, pushforwardCLM 𝕜 φ hφ hψ (∂_{v} f) y * u y ∂μ
      = ∫ x, w x * ∂_{v} f x ∂μ := by
        simpa [smul_eq_mul, w, mul_comm] using integral_pushforwardCLM_smul 𝕜 μ hφ hψ (∂_{v} f) u
    _ = -∫ x, ∂_{v} w x * f x ∂μ := integral_mul_lineDerivOp_right_eq_neg_left w f v
    _ = -∑ i, ∫ x, c i x * f x * (∂_{b i} u) (φ x) ∂μ := by
        rw [← integral_finsetSum _ fun i _ ↦ hint i]
        congr 1
        refine integral_congr_ae (.of_forall fun x ↦ ?_)
        simp only [w, lineDerivOp_compCLM_apply 𝕜 b hφ hψ, smul_eq_mul, Finset.sum_mul]
        exact Finset.sum_congr rfl fun i _ ↦ by ring
    _ = -∑ i, ∫ y, pushforwardCLM 𝕜 φ hφ hψ (smulLeftCLM 𝕜 (c i) f) y * ∂_{b i} u y ∂μ := by
        congr 1
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        simpa [smul_eq_mul, smulLeftCLM_apply_apply (hc i)] using
          (integral_pushforwardCLM_smul 𝕜 μ hφ hψ (smulLeftCLM 𝕜 (c i) f)
            (fun y ↦ (∂_{b i} u : 𝓢(E, 𝕜)) y)).symm
    _ = ∑ i, ∫ y, ∂_{b i} (pushforwardCLM 𝕜 φ hφ hψ (smulLeftCLM 𝕜 (c i) f)) y * u y ∂μ := by
        simp only [integral_mul_lineDerivOp_right_eq_neg_left, Finset.sum_neg_distrib, neg_neg]
    _ = _ := by
        rw [← integral_finsetSum _ fun i _ ↦ ?_]
        · simp [Finset.sum_mul, c]
        · exact (∂_{b i} (pushforwardCLM 𝕜 φ hφ hψ (smulLeftCLM 𝕜 (c i) f))).integrable.mul_bdd
            u.continuous.aestronglyMeasurable (c := SchwartzMap.seminorm ℝ 0 0 u)
            (.of_forall fun x ↦ norm_le_seminorm ℝ _ _)

/-- The scalar case of `SchwartzMap.pushforwardCLM_lineDerivOp`, proved by pairing with test
functions. -/
private theorem pushforwardCLM_lineDerivOp_scalar (b : Module.Basis ι ℝ E)
    (hφ : (φ : E → E).HasTemperateGrowth) (hψ : (φ.symm : E → E).HasTemperateGrowth)
    (f : 𝓢(E, 𝕜)) (v : E) :
    pushforwardCLM 𝕜 φ hφ hψ (∂_{v} f) = ∑ i, ∂_{b i} (pushforwardCLM 𝕜 φ hφ hψ
      (smulLeftCLM 𝕜 (fun x ↦ ((b.repr (fderiv ℝ φ x v) i : ℝ) : 𝕜)) f)) := by
  borelize E
  set A := pushforwardCLM 𝕜 φ hφ hψ (∂_{v} f)
  set B := ∑ i, ∂_{b i} (pushforwardCLM 𝕜 φ hφ hψ
      (smulLeftCLM 𝕜 (fun x ↦ ((b.repr (fderiv ℝ φ x v) i : ℝ) : 𝕜)) f))
  -- `A` and `B` have the same integrals against smooth compactly supported functions.
  have hae : ∀ᵐ x ∂(Measure.addHaar : Measure E), A x = B x := by
    refine ae_eq_of_integral_contDiff_smul_eq A.integrable.locallyIntegrable
      B.integrable.locallyIntegrable fun g hg hgc ↦ ?_
    have hg₁ : HasCompactSupport (fun x ↦ (g x : 𝕜)) := hgc.comp_left (by simp)
    have hg₂ : ContDiff ℝ ∞ (fun x ↦ (g x : 𝕜)) := ((RCLike.ofRealCLM (K := 𝕜)).contDiff).comp hg
    set u := hg₁.toSchwartzMap hg₂
    have hu (x : E) : u x = g x := hg₁.toSchwartzMap_toFun hg₂ x
    have := integral_pushforwardCLM_lineDerivOp_mul 𝕜 Measure.addHaar b hφ hψ f u v
    simp only [hu] at this
    simpa only [RCLike.real_smul_eq_coe_mul, mul_comm _ (A _), mul_comm _ (B _)] using this
  ext x
  exact congrFun ((Continuous.ae_eq_iff_eq _ A.continuous B.continuous).1 hae) x

/-- **The pushforward of a derivative.** If `Dφ(x) v = ∑ᵢ cᵢ(x) bᵢ` in a basis `b`, then

`φ_* (∂_v f) = ∑ᵢ ∂_{bᵢ} (φ_* (cᵢ f))`.

This is the transpose of the chain rule `∂_v (u ∘ φ)(x) = ∑ᵢ cᵢ(x) (∂_{bᵢ} u)(φ x)`. -/
theorem pushforwardCLM_lineDerivOp [IsScalarTower ℝ 𝕜 F] (b : Module.Basis ι ℝ E)
    (hφ : (φ : E → E).HasTemperateGrowth) (hψ : (φ.symm : E → E).HasTemperateGrowth)
    (f : 𝓢(E, F)) (v : E) :
    pushforwardCLM 𝕜 φ hφ hψ (∂_{v} f) = ∑ i, ∂_{b i} (pushforwardCLM 𝕜 φ hφ hψ
      (smulLeftCLM F (fun x ↦ ((b.repr (fderiv ℝ φ x v) i : ℝ) : 𝕜)) f)) := by
  -- Apply a real functional `ℓ` to the values and use the real-valued case.
  have hreal := pushforwardCLM_lineDerivOp_scalar ℝ b hφ hψ
  simp only [RCLike.ofReal_real_eq_id, id_eq] at hreal
  ext y
  rw [SeparatingDual.eq_iff_forall_dual_eq (R := ℝ)]
  intro ℓ
  have hsmul (i : ι) :
      (smulLeftCLM F (fun x ↦ ((b.repr (fderiv ℝ φ x v) i : ℝ) : 𝕜)) f).postcompCLM ℓ =
        smulLeftCLM ℝ (fun x ↦ b.repr (fderiv ℝ φ x v) i) (f.postcompCLM ℓ) := by
    ext x
    rw [postcompCLM_apply, smulLeftCLM_apply_apply (hφ.basis_repr_fderiv_apply b v i),
      smulLeftCLM_apply_apply (by simpa using hφ.basis_repr_fderiv_apply (𝕜 := ℝ) b v i),
      postcompCLM_apply, ← RCLike.real_smul_eq_coe_smul (K := 𝕜), map_smul, smul_eq_mul]
  have hlhs : ℓ (pushforwardCLM 𝕜 φ hφ hψ (∂_{v} f) y) =
      pushforwardCLM ℝ φ hφ hψ (∂_{v} (f.postcompCLM ℓ)) y := by
    rw [← postcompCLM_apply ℓ, pushforwardCLM_postcompCLM, lineDerivOp_postcompCLM]
  rw [hlhs, hreal (f.postcompCLM ℓ) v, _root_.sum_apply, _root_.sum_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [← postcompCLM_apply ℓ, ← lineDerivOp_postcompCLM, pushforwardCLM_postcompCLM, hsmul]

end LineDeriv

end SchwartzMap
