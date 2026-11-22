/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialOperator.LaplaceType
public import TauCeti.Geometry.Manifold.DifferentialOperator.Transpose.Existence
public import TauCeti.Geometry.Manifold.Riemannian.DivergenceTheorem
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Support

/-!
# Formal transposes with respect to the Riemannian volume

On a Riemannian manifold `M` without boundary, the Riemannian volume `dV`
(`TauCeti.riemannianVolume`) is the canonical density, and the formal transpose of an operator
`D` on `C^∞(M)` is taken with respect to it: `∫ (D f) g dV = ∫ f (Dᵗ g) dV` whenever `f` or `g`
has compact support (`LinearMap.IsFormalTranspose`). For real functions this is also the formal
adjoint for the `L²(dV)` inner product.

The divergence theorem computes these transposes for operators of order at most one. Writing
`X f = df(X)` for differentiation along a smooth vector field `X`, the product rule
`div (g X) = g div X + X g` gives

`∫ (X f) g dV = -∫ f (X g + (div X) g) dV`

(`TauCeti.Manifold.integral_mvfderiv_mul`), so the transpose of `X + c` is
`-X + (c - div X)` (`LinearMap.isFormalTranspose_vectorFieldDerivation_add_mulLeft`). The
zeroth-order term `-div X` is what distinguishes the transpose from the naive `-X + c`; it vanishes
exactly for divergence-free fields. Since vector fields have transposes of order at most one, every
differential operator of order at most `m` has a formal transpose of order at most `m`
(`LinearMap.formalTranspose_riemannianVolume_mem_differentialOperators`, from
`LinearMap.exists_isFormalTranspose_of_forall_vectorFieldDerivation`). Green's second identity
says that the Laplace–Beltrami operator is its own transpose
(`LinearMap.formalTranspose_smoothLaplaceBeltrami`).

The transpose depends on the density. Every smooth positive density is `e^φ dV` for a smooth
function `φ`, and with respect to it the transpose of `X` acquires the extra term `-(X φ)`
(`LinearMap.isFormalTranspose_vectorFieldDerivation_withDensity_exp`). On the real line with its
Euclidean metric, where `dV = dx` and `div ∂ₓ = 0`, taking `φ = sin` gives the transpose
`-∂ₓ - cos x` of `∂ₓ` for the density `e^(sin x) dx`.

## Main results

* `LinearMap.isFormalTranspose_vectorFieldDerivation`,
  `LinearMap.formalTranspose_vectorFieldDerivation`: the transpose of `X` is `-X - div X`.
* `LinearMap.isFormalTranspose_vectorFieldDerivation_add_mulLeft`,
  `LinearMap.formalTranspose_vectorFieldDerivation_add_mulLeft`: the transpose of `X + c` is
  `-X + (c - div X)`.
* `LinearMap.isFormalTranspose_formalTranspose_riemannianVolume_of_mem_differentialOperators`,
  `LinearMap.formalTranspose_riemannianVolume_mem_differentialOperators`: a differential operator
  of order at most `m` has a formal transpose with respect to `dV`, again of order at most `m`.
* `LinearMap.isFormalTranspose_smoothLaplaceBeltrami`,
  `LinearMap.formalTranspose_smoothLaplaceBeltrami`: the Laplace–Beltrami operator is formally
  self-transpose.
* `LinearMap.isFormalTranspose_vectorFieldDerivation_withDensity_exp`,
  `LinearMap.formalTranspose_vectorFieldDerivation_withDensity_exp`: the transpose of `X` with
  respect to `e^φ dV` is `-X - (div X + X φ)`.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013),
  Chapter 16 (the divergence theorem and Green's identities).
* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018),
  Chapter 2 (the divergence and the Riemannian density).
-/

public section

noncomputable section

open Bundle MeasureTheory TauCeti.Manifold
open scoped ContDiff Manifold

namespace LinearMap

open TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

variable [SigmaCompactSpace M] [MeasurableSpace M] [BorelSpace M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

/-! ### Vector fields and differential operators -/

/-- **The transpose of a vector field.** With respect to the Riemannian volume, the formal
transpose of differentiation along a smooth vector field `X` is `g ↦ -X g - (div X) g`. -/
theorem isFormalTranspose_vectorFieldDerivation
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    (vectorFieldDerivation X : C^∞⟮I, M; ℝ⟯ →ₗ[ℝ] C^∞⟮I, M; ℝ⟯).IsFormalTranspose
      (-(vectorFieldDerivation X : C^∞⟮I, M; ℝ⟯ →ₗ[ℝ] C^∞⟮I, M; ℝ⟯) -
        mulLeft ℝ (smoothDivergence I M X)) (riemannianVolume I M) := by
  rw [isFormalTranspose_iff]
  intro f g hfg
  have h := integral_mvfderiv_mul (f.contMDiff.of_le (by simp)) (g.contMDiff.of_le (by simp))
    (X.contMDiff.of_le (by simp)) hfg
  simp only [Derivation.coeFn_coe, ContMDiffSection.vectorFieldDerivation_apply_apply]
  rw [h, ← integral_neg]
  congr 1 with x
  simp only [LinearMap.sub_apply, LinearMap.neg_apply, mulLeft_apply, ContMDiffMap.coe_sub,
    ContMDiffMap.coe_neg, ContMDiffMap.coe_mul, Pi.sub_apply, Pi.neg_apply, Pi.mul_apply,
    Derivation.coeFn_coe, ContMDiffSection.vectorFieldDerivation_apply_apply,
    smoothDivergence_apply]
  ring

/-- The formal transpose of `X + c`, for a smooth vector field `X` and a smooth function `c`, is
`-X + (c - div X)` with respect to the Riemannian volume. -/
theorem isFormalTranspose_vectorFieldDerivation_add_mulLeft
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (c : C^∞⟮I, M; ℝ⟯) :
    ((vectorFieldDerivation X : C^∞⟮I, M; ℝ⟯ →ₗ[ℝ] C^∞⟮I, M; ℝ⟯) + mulLeft ℝ c).IsFormalTranspose
      (-(vectorFieldDerivation X : C^∞⟮I, M; ℝ⟯ →ₗ[ℝ] C^∞⟮I, M; ℝ⟯) +
        mulLeft ℝ (c - smoothDivergence I M X)) (riemannianVolume I M) := by
  have hX := (vectorFieldDerivation X).mem_differentialOperators_one
  have hm (a : C^∞⟮I, M; ℝ⟯) :=
    differentialOperators_le_succ 0 (mulLeft_mem_differentialOperators_zero (R := ℝ) a)
  have h := (isFormalTranspose_vectorFieldDerivation X).add (isFormalTranspose_mulLeft c)
    (tsupport_differentialOperators_apply_subset hX)
    (tsupport_differentialOperators_apply_subset (hm c))
    (tsupport_differentialOperators_apply_subset (sub_mem (neg_mem hX) (hm _)))
    (tsupport_differentialOperators_apply_subset (hm c))
  convert h using 1
  ext g x
  simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.neg_apply, mulLeft_apply,
    ContMDiffMap.coe_add, ContMDiffMap.coe_sub, ContMDiffMap.coe_neg, ContMDiffMap.coe_mul,
    Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Pi.mul_apply]
  ring

/-- With respect to the Riemannian volume, the formal transpose of differentiation along a smooth
vector field `X` is `-X - div X`. -/
@[simp]
theorem formalTranspose_vectorFieldDerivation (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    (vectorFieldDerivation X : C^∞⟮I, M; ℝ⟯ →ₗ[ℝ] C^∞⟮I, M; ℝ⟯).formalTranspose
        (riemannianVolume I M) =
      -(vectorFieldDerivation X : C^∞⟮I, M; ℝ⟯ →ₗ[ℝ] C^∞⟮I, M; ℝ⟯) -
        mulLeft ℝ (smoothDivergence I M X) :=
  (isFormalTranspose_vectorFieldDerivation X).formalTranspose_eq

/-- With respect to the Riemannian volume, the formal transpose of `X + c` is `-X + (c - div X)`.
-/
@[simp]
theorem formalTranspose_vectorFieldDerivation_add_mulLeft
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (c : C^∞⟮I, M; ℝ⟯) :
    ((vectorFieldDerivation X : C^∞⟮I, M; ℝ⟯ →ₗ[ℝ] C^∞⟮I, M; ℝ⟯) + mulLeft ℝ c).formalTranspose
        (riemannianVolume I M) =
      -(vectorFieldDerivation X : C^∞⟮I, M; ℝ⟯ →ₗ[ℝ] C^∞⟮I, M; ℝ⟯) +
        mulLeft ℝ (c - smoothDivergence I M X) :=
  (isFormalTranspose_vectorFieldDerivation_add_mulLeft X c).formalTranspose_eq

variable {D : C^∞⟮I, M; ℝ⟯ →ₗ[ℝ] C^∞⟮I, M; ℝ⟯}

/-- The transpose of differentiation along a vector field has order at most one. -/
private theorem exists_isFormalTranspose_vectorFieldDerivation
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    ∃ D' ∈ differentialOperators ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ 1,
      (vectorFieldDerivation X : C^∞⟮I, M; ℝ⟯ →ₗ[ℝ] C^∞⟮I, M; ℝ⟯).IsFormalTranspose D'
        (riemannianVolume I M) :=
  ⟨_, sub_mem (neg_mem (Derivation.mem_differentialOperators_one _))
    (differentialOperators_le_succ 0 (mulLeft_mem_differentialOperators_zero _)),
    isFormalTranspose_vectorFieldDerivation X⟩

/-- **Transposes of differential operators.** With respect to the Riemannian volume, every
differential operator on `C^∞(M)` has a formal transpose. -/
theorem isFormalTranspose_formalTranspose_riemannianVolume_of_mem_differentialOperators {m : ℕ}
    (hD : D ∈ differentialOperators ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ m) :
    D.IsFormalTranspose (D.formalTranspose (riemannianVolume I M)) (riemannianVolume I M) := by
  obtain ⟨D', -, h⟩ := exists_isFormalTranspose_of_forall_vectorFieldDerivation
    exists_isFormalTranspose_vectorFieldDerivation hD
  exact h.isFormalTranspose_formalTranspose

/-- With respect to the Riemannian volume, the formal transpose of a differential operator of
order at most `m` has order at most `m`. -/
theorem formalTranspose_riemannianVolume_mem_differentialOperators {m : ℕ}
    (hD : D ∈ differentialOperators ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ m) :
    D.formalTranspose (riemannianVolume I M) ∈
      differentialOperators ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ m := by
  obtain ⟨D', hD', h⟩ := exists_isFormalTranspose_of_forall_vectorFieldDerivation
    exists_isFormalTranspose_vectorFieldDerivation hD
  rwa [h.formalTranspose_eq]

/-! ### The Laplace–Beltrami operator -/

/-- **Green's second identity** as a transpose: the Laplace–Beltrami operator is its own formal
transpose with respect to the Riemannian volume. -/
theorem isFormalTranspose_smoothLaplaceBeltrami :
    (smoothLaplaceBeltrami I M).IsFormalTranspose (smoothLaplaceBeltrami I M)
      (riemannianVolume I M) := by
  rw [isFormalTranspose_iff]
  intro f g hfg
  simp only [smoothLaplaceBeltrami_apply]
  rcases hfg with hf | hg
  · exact (integral_mul_laplaceBeltrami_right_eq_left (f.contMDiff.of_le (by simp)) hf
      (g.contMDiff.of_le (by simp))).symm
  · simp_rw [mul_comm (laplaceBeltrami I f _), mul_comm (f _)]
    exact integral_mul_laplaceBeltrami_right_eq_left (g.contMDiff.of_le (by simp)) hg
      (f.contMDiff.of_le (by simp))

/-- The Laplace–Beltrami operator is formally self-transpose with respect to the Riemannian
volume. -/
@[simp]
theorem formalTranspose_smoothLaplaceBeltrami :
    (smoothLaplaceBeltrami I M).formalTranspose (riemannianVolume I M) =
      smoothLaplaceBeltrami I M :=
  isFormalTranspose_smoothLaplaceBeltrami.formalTranspose_eq

/-! ### Weighted densities -/

/-- **The transpose for a weighted density.** With respect to the density `e^φ dV`, for a smooth
function `φ`, the formal transpose of differentiation along a smooth vector field `X` is
`-X - (div X + X φ)`. -/
theorem isFormalTranspose_vectorFieldDerivation_withDensity_exp
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (φ : C^∞⟮I, M; ℝ⟯) :
    (vectorFieldDerivation X : C^∞⟮I, M; ℝ⟯ →ₗ[ℝ] C^∞⟮I, M; ℝ⟯).IsFormalTranspose
      (-(vectorFieldDerivation X : C^∞⟮I, M; ℝ⟯ →ₗ[ℝ] C^∞⟮I, M; ℝ⟯) -
        mulLeft ℝ (smoothDivergence I M X + vectorFieldDerivation X φ))
      ((riemannianVolume I M).withDensity fun x ↦ ENNReal.ofReal (Real.exp (φ x))) := by
  let ρ : C^∞⟮I, M; ℝ⟯ := ⟨Real.exp ∘ φ, ContDiff.comp_contMDiff Real.contDiff_exp φ.contMDiff⟩
  -- The chain rule `X (e^φ) = e^φ X φ`.
  have hXρ : vectorFieldDerivation X ρ = ρ * vectorFieldDerivation X φ := by
    ext x
    have hφ : MDifferentiableAt I 𝓘(ℝ) φ x := φ.contMDiff.mdifferentiableAt (by simp)
    simp only [ContMDiffSection.vectorFieldDerivation_apply_apply, ContMDiffMap.coe_mul,
      Pi.mul_apply]
    rw [show (ρ : M → ℝ) = Real.exp ∘ φ from ContMDiffMap.coeFn_mk _ _,
      mvfderiv_scalar_comp hφ Real.differentiable_exp.differentiableAt, Real.deriv_exp,
      _root_.smul_apply, smul_eq_mul, Function.comp_apply]
  refine (isFormalTranspose_vectorFieldDerivation X).withDensity (ρ := ρ)
    (fun x ↦ (Real.exp_pos _).le) fun g ↦ ?_
  ext x
  simp only [ContMDiffMap.coe_mul, Pi.mul_apply, LinearMap.sub_apply, LinearMap.neg_apply,
    mulLeft_apply, ContMDiffMap.coe_sub, ContMDiffMap.coe_neg, ContMDiffMap.coe_add,
    Pi.sub_apply, Pi.neg_apply, Pi.add_apply, Derivation.coeFn_coe, Derivation.leibniz, hXρ,
    smul_eq_mul]
  ring

/-- With respect to the density `e^φ dV`, the formal transpose of differentiation along a smooth
vector field `X` is `-X - (div X + X φ)`. -/
@[simp]
theorem formalTranspose_vectorFieldDerivation_withDensity_exp
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (φ : C^∞⟮I, M; ℝ⟯) :
    (vectorFieldDerivation X : C^∞⟮I, M; ℝ⟯ →ₗ[ℝ] C^∞⟮I, M; ℝ⟯).formalTranspose
        ((riemannianVolume I M).withDensity fun x ↦ ENNReal.ofReal (Real.exp (φ x))) =
      -(vectorFieldDerivation X : C^∞⟮I, M; ℝ⟯ →ₗ[ℝ] C^∞⟮I, M; ℝ⟯) -
        mulLeft ℝ (smoothDivergence I M X + vectorFieldDerivation X φ) := by
  have hcont : Continuous fun x ↦ Real.exp (φ x) := Real.continuous_exp.comp φ.contMDiff.continuous
  have := IsLocallyFiniteMeasure.withDensity_ofReal (μ := riemannianVolume I M) hcont
  have : ((riemannianVolume I M).withDensity
      fun x ↦ ENNReal.ofReal (Real.exp (φ x))).IsOpenPosMeasure :=
    (withDensity_absolutelyContinuous'
      (ENNReal.measurable_ofReal.comp hcont.measurable).aemeasurable
      (.of_forall fun x ↦ by simp [Real.exp_pos])).isOpenPosMeasure
  exact (isFormalTranspose_vectorFieldDerivation_withDensity_exp X φ).formalTranspose_eq

end LinearMap
