/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
public import Mathlib.MeasureTheory.Measure.Haar.Basic
public import Mathlib.Topology.Algebra.Module.Determinant
import Mathlib.Analysis.LocallyConvex.SeparatingDual
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import TauCeti.Analysis.Distribution.SchwartzSpace.Deriv
import TauCeti.Analysis.Distribution.TemperateGrowth
import TauCeti.Topology.Algebra.Module.Determinant

/-!
# Pushforward of Schwartz densities along a change of variables

Let `φ : E ≃ E` be a bijection of a finite-dimensional real normed space such that `φ` and `φ⁻¹`
both have temperate growth: they are smooth and all their derivatives grow at most polynomially.
Examples are diffeomorphisms whose derivatives of positive order, and those of their inverses, are
bounded (`Function.HasTemperateGrowth.of_norm_iteratedFDeriv_le_of_pos`), and polynomial
automorphisms such as the shear `(x, y) ↦ (x, y + x³)` of `ℝ²`.

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
(`SchwartzMap.pushforwardCLM_postcompCLM`). Pushing forward a directional derivative `∂_w f`
expands along any basis `(bᵢ)` of `E` in divergence form (`SchwartzMap.pushforwardCLM_lineDerivOp`),
the dual of the chain rule for composition with `φ` that avoids differentiating `|det Dφ⁻¹|`
explicitly.

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

/-- Two real Schwartz functions that have the same `L²` pairing against every real Schwartz
function are equal. -/
private theorem eq_of_forall_integral_mul_eq [MeasurableSpace E] [BorelSpace E] (μ : Measure E)
    [μ.IsAddHaarMeasure] {s₁ s₂ : 𝓢(E, ℝ)}
    (h : ∀ θ : 𝓢(E, ℝ), ∫ y, s₁ y * θ y ∂μ = ∫ y, s₂ y * θ y ∂μ) : s₁ = s₂ := by
  have hmul_int (f₁ f₂ : 𝓢(E, ℝ)) : Integrable (fun x ↦ f₁ x * f₂ x) μ :=
    (f₁.pairing (ContinuousLinearMap.mul ℝ ℝ) f₂).integrable
  set δ : 𝓢(E, ℝ) := s₁ - s₂
  have hδ0 : ∫ y, δ y * δ y ∂μ = 0 := by
    have hsub : (fun y ↦ δ y * δ y) = fun y ↦ s₁ y * δ y - s₂ y * δ y :=
      funext fun y ↦ sub_mul (s₁ y) (s₂ y) (δ y)
    rw [hsub, integral_sub (hmul_int s₁ δ) (hmul_int s₂ δ), h δ, sub_self]
  have hae : (fun y ↦ δ y * δ y) =ᵐ[μ] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun y ↦ mul_self_nonneg (δ y)) (hmul_int δ δ)).1 hδ0
  have hzero : ∀ y, δ y * δ y = 0 :=
    congrFun (((δ.continuous.mul δ.continuous).ae_eq_iff_eq μ continuous_const).1 hae)
  refine sub_eq_zero.1 ?_
  ext y
  exact mul_self_eq_zero.1 (hzero y)

/-- Real scalar case of `pushforwardCLM_lineDerivOp`, proved by testing against Schwartz functions
via the change of variables formula and integration by parts. -/
private theorem pushforwardCLM_lineDerivOp_real {ι : Type*} [Fintype ι] (b : Module.Basis ι ℝ E)
    (hφ : (φ : E → E).HasTemperateGrowth) (hψ : (φ.symm : E → E).HasTemperateGrowth)
    (f : 𝓢(E, ℝ)) (w : E) :
    pushforwardCLM ℝ φ hφ hψ (∂_{w} f) = ∑ i, ∂_{b i} (pushforwardCLM ℝ φ hφ hψ
      (smulLeftCLM ℝ (fun x ↦ b.coord i (fderiv ℝ φ x w)) f)) := by
  let _ : MeasurableSpace E := borel E
  have : BorelSpace E := ⟨rfl⟩
  let μ : Measure E := b.addHaar
  have ha (i : ι) : (fun x ↦ b.coord i (fderiv ℝ φ x w)).HasTemperateGrowth :=
    (b.coord i).toContinuousLinearMap.hasTemperateGrowth.comp (hφ.fderiv_apply w)
  have hmul_int (s₁ s₂ : 𝓢(E, ℝ)) : Integrable (fun x ↦ s₁ x * s₂ x) μ :=
    (s₁.pairing (ContinuousLinearMap.mul ℝ ℝ) s₂).integrable
  refine eq_of_forall_integral_mul_eq μ fun θ ↦ ?_
  set θφ : 𝓢(E, ℝ) := compCLM ℝ hφ (hψ.exists_norm_le_of_leftInverse φ.left_inv) θ
  have hθφ : ⇑θφ = θ ∘ φ := rfl
  have hchain (x : E) : ∂_{w} θφ x = ∑ i, b.coord i (fderiv ℝ φ x w) * ∂_{b i} θ (φ x) := by
    rw [lineDerivOp_apply_eq_fderiv, hθφ,
      fderiv_comp x θ.differentiableAt (hφ.1.differentiable (by simp) x),
      ContinuousLinearMap.comp_apply]
    conv_lhs => rw [← b.sum_repr (fderiv ℝ φ x w)]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [map_smul, b.coord_apply, smul_eq_mul, lineDerivOp_apply_eq_fderiv]
  have hlhs : ∫ y, pushforwardCLM ℝ φ hφ hψ (∂_{w} f) y * θ y ∂μ =
      -∫ x, f x * ∂_{w} θφ x ∂μ := by
    calc ∫ y, pushforwardCLM ℝ φ hφ hψ (∂_{w} f) y * θ y ∂μ
        = ∫ x, ∂_{w} f x * θφ x ∂μ := by
          simpa only [smul_eq_mul, hθφ, Function.comp_apply] using
            integral_pushforwardCLM_smul ℝ μ hφ hψ (∂_{w} f) θ
      _ = ∫ x, θφ x * ∂_{w} f x ∂μ := integral_congr_ae (.of_forall fun _ ↦ mul_comm _ _)
      _ = -∫ x, ∂_{w} θφ x * f x ∂μ := integral_mul_lineDerivOp_right_eq_neg_left θφ f w (μ := μ)
      _ = -∫ x, f x * ∂_{w} θφ x ∂μ :=
          congrArg Neg.neg (integral_congr_ae (.of_forall fun _ ↦ mul_comm _ _))
  rw [hlhs]
  simp_rw [_root_.sum_apply, Finset.sum_mul]
  rw [integral_finsetSum _ fun i _ ↦ hmul_int _ θ]
  simp_rw [hchain, Finset.mul_sum]
  rw [integral_finsetSum _ fun i _ ↦ ?_, ← Finset.sum_neg_distrib]
  · refine Finset.sum_congr rfl fun i _ ↦ ?_
    set g_i : 𝓢(E, ℝ) := pushforwardCLM ℝ φ hφ hψ
      (smulLeftCLM ℝ (fun x ↦ b.coord i (fderiv ℝ φ x w)) f)
    set dθ : 𝓢(E, ℝ) := ∂_{b i} θ
    symm
    calc ∫ y, ∂_{b i} g_i y * θ y ∂μ
        = ∫ y, θ y * ∂_{b i} g_i y ∂μ := integral_congr_ae (.of_forall fun _ ↦ mul_comm _ _)
      _ = -∫ y, dθ y * g_i y ∂μ :=
          integral_mul_lineDerivOp_right_eq_neg_left θ g_i (b i) (μ := μ)
      _ = -∫ y, g_i y • dθ y ∂μ :=
          congrArg Neg.neg (integral_congr_ae (.of_forall fun _ ↦ mul_comm _ _))
      _ = -∫ x, smulLeftCLM ℝ (fun x ↦ b.coord i (fderiv ℝ φ x w)) f x • dθ (φ x) ∂μ :=
          congrArg Neg.neg (integral_pushforwardCLM_smul ℝ μ hφ hψ _ dθ)
      _ = -∫ x, f x * (b.coord i (fderiv ℝ φ x w) * dθ (φ x)) ∂μ := by
          refine congrArg Neg.neg (integral_congr_ae (.of_forall fun x ↦ ?_))
          dsimp only
          rw [smulLeftCLM_apply_apply (ha i), smul_eq_mul, smul_eq_mul]
          ring
  · refine (hmul_int (smulLeftCLM ℝ (fun x ↦ b.coord i (fderiv ℝ φ x w)) f)
        (compCLM ℝ hφ (hψ.exists_norm_le_of_leftInverse φ.left_inv) (∂_{b i} θ : 𝓢(E, ℝ)))
      ).congr (.of_forall fun x ↦ ?_)
    dsimp only
    rw [smulLeftCLM_apply_apply (ha i), smul_eq_mul, compCLM_apply, Function.comp_apply]
    ring

/-- **Pushforward of a directional derivative (Piola's divergence identity).** Along any basis `b`
of `E`, pushing forward `∂_w f` along `φ` writes it in divergence form:
`φ_* (∂_w f) = ∑ᵢ ∂_{bᵢ} (φ_* (bᵢ^*(Dφ(·) w) • f))`. -/
theorem pushforwardCLM_lineDerivOp [IsScalarTower ℝ 𝕜 F] {ι : Type*} [Fintype ι]
    (b : Module.Basis ι ℝ E) (hφ : (φ : E → E).HasTemperateGrowth)
    (hψ : (φ.symm : E → E).HasTemperateGrowth) (f : 𝓢(E, F)) (w : E) :
    pushforwardCLM 𝕜 φ hφ hψ (∂_{w} f) = ∑ i, ∂_{b i} (pushforwardCLM 𝕜 φ hφ hψ
      (smulLeftCLM F (fun x ↦ ((b.coord i (fderiv ℝ φ x w) : ℝ) : 𝕜)) f)) := by
  have haR (i : ι) : (fun x ↦ b.coord i (fderiv ℝ φ x w)).HasTemperateGrowth :=
    (b.coord i).toContinuousLinearMap.hasTemperateGrowth.comp (hφ.fderiv_apply w)
  have haK (i : ι) : (fun x ↦ ((b.coord i (fderiv ℝ φ x w) : ℝ) : 𝕜)).HasTemperateGrowth :=
    (RCLike.hasTemperateGrowth_ofReal 𝕜).comp (haR i)
  ext y
  rw [SeparatingDual.eq_iff_forall_dual_eq (R := ℝ)]
  intro ℓ
  have hsmul (i : ι) :
      (smulLeftCLM F (fun x ↦ ((b.coord i (fderiv ℝ φ x w) : ℝ) : 𝕜)) f).postcompCLM ℓ =
        smulLeftCLM ℝ (fun x ↦ b.coord i (fderiv ℝ φ x w)) (f.postcompCLM ℓ) := by
    ext x
    rw [postcompCLM_apply, smulLeftCLM_apply_apply (haK i), smulLeftCLM_apply_apply (haR i),
      postcompCLM_apply, ← RCLike.real_smul_eq_coe_smul (K := 𝕜), map_smul, smul_eq_mul]
  have hlhs : ℓ (pushforwardCLM 𝕜 φ hφ hψ (∂_{w} f) y) =
      pushforwardCLM ℝ φ hφ hψ (∂_{w} (f.postcompCLM ℓ)) y := by
    rw [← postcompCLM_apply ℓ, pushforwardCLM_postcompCLM, TauCeti.lineDerivOp_postcompCLM]
  rw [hlhs, pushforwardCLM_lineDerivOp_real b hφ hψ (f.postcompCLM ℓ) w, _root_.sum_apply,
    _root_.sum_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [← postcompCLM_apply ℓ, ← TauCeti.lineDerivOp_postcompCLM, pushforwardCLM_postcompCLM, hsmul]

end SchwartzMap
