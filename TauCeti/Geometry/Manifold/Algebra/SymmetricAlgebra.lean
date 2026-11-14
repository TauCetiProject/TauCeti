/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import TauCeti.Geometry.Manifold.Algebra.SmoothFunctions
public import TauCeti.LinearAlgebra.SymmetricAlgebra.Gradient
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-!
# Smooth polynomial evaluations of a symmetric algebra on the continuous dual

Let `E` be a normed vector space over a nontrivially normed field `𝕜`. Every vector `x : E`
defines the continuous linear functional `ContinuousLinearMap.apply 𝕜 𝕜 x : StrongDual 𝕜 E →L[𝕜] 𝕜`,
which is smooth of every order `n : ℕ∞ω`. By the universal property of `SymmetricAlgebra 𝕜 E`,
this linear assignment extends to a `𝕜`-algebra homomorphism

`SymmetricAlgebra.contMDiffEval 𝕜 E n :`
`  SymmetricAlgebra 𝕜 E →ₐ[𝕜] C^n⟮𝓘(𝕜, StrongDual 𝕜 E), StrongDual 𝕜 E; 𝕜⟯`

evaluating each symmetric tensor `p` at a continuous linear form `ξ` by
`SymmetricAlgebra.lift ξ.toLinearMap p`.

When `E` is finite-dimensional over a complete nontrivially normed field `𝕜`, every linear form on
`E` is continuous and `𝕜` is infinite, so `SymmetricAlgebra.contMDiffEval` is injective. Whenever
`E` has a finite basis `b`, the Fréchet derivative of `SymmetricAlgebra.contMDiffEval 𝕜 E n p` at
`ξ` is evaluation at the gradient vector `b.symmetricGradient p ξ.toLinearMap`, and the directional
derivative of `t ↦ SymmetricAlgebra.lift (ξ + t • η) p` at `t = 0` is
`η (b.symmetricGradient p ξ)`.

## Main definitions

* `SymmetricAlgebra.contMDiffEval`: the `𝕜`-algebra homomorphism sending `p : SymmetricAlgebra 𝕜 E`
  to the `C^n` polynomial function `ξ ↦ SymmetricAlgebra.lift ξ.toLinearMap p` on `StrongDual 𝕜 E`.

## Main results

* `SymmetricAlgebra.contMDiffEval_apply`, `SymmetricAlgebra.coe_contMDiffEval_ι`,
  `SymmetricAlgebra.evalAlgHom_comp_contMDiffEval`: pointwise and generator evaluation formulas.
* `SymmetricAlgebra.compRightAlgHom_precomp_comp_contMDiffEval`,
  `SymmetricAlgebra.contMDiffEval_map`: contravariant naturality along a continuous linear map
  `u : E →L[𝕜] F` and its transpose `u.precomp 𝕜 : StrongDual 𝕜 F →L[𝕜] StrongDual 𝕜 E`.
* `SymmetricAlgebra.contMDiffEval_injective`: injectivity for finite-dimensional `E` over a
  complete nontrivially normed field.
* `Module.Basis.hasDerivAt_lift_add_smul`, `Module.Basis.hasDerivAt_lift_add_smul_zero`:
  directional derivative of `t ↦ SymmetricAlgebra.lift (ξ + t • η) p` along an affine line in
  `Module.Dual 𝕜 M`.
* `Module.Basis.hasFDerivAt_lift`, `Module.Basis.hasFDerivAt_contMDiffEval`,
  `Module.Basis.fderiv_contMDiffEval`: Fréchet derivative of polynomial evaluation on
  `StrongDual 𝕜 E`, identified via `ContinuousLinearMap.apply` with `b.symmetricGradient`.

## References

* J. E. Marsden and T. S. Ratiu, *Introduction to Mechanics and Symmetry*, 2nd ed., Springer
  (1999), §10.1 (smooth polynomial functions and functional derivatives on the dual of a Lie
  algebra).
-/

public section

open scoped ContDiff Manifold

namespace SymmetricAlgebra

section Eval

variable (𝕜 E : Type*) [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  (n : ℕ∞ω)

/-- Each vector `x : E` defines a `C^n` linear function `ξ ↦ ξ x` on `StrongDual 𝕜 E`, depending
`𝕜`-linearly on `x`. -/
noncomputable def contMDiffLinearEval :
    E →ₗ[𝕜] C^n⟮𝓘(𝕜, StrongDual 𝕜 E), StrongDual 𝕜 E; 𝕜⟯ where
  toFun x := (ContinuousLinearMap.apply 𝕜 𝕜 x : StrongDual 𝕜 E →L[𝕜] 𝕜)
  map_add' x y := ContMDiffMap.ext fun ξ ↦ map_add ξ x y
  map_smul' r x := ContMDiffMap.ext fun ξ ↦ map_smul ξ r x

@[simp]
theorem coe_contMDiffLinearEval (x : E) :
    ⇑(contMDiffLinearEval 𝕜 E n x) = ContinuousLinearMap.apply 𝕜 𝕜 x :=
  (rfl)

@[simp]
theorem contMDiffLinearEval_apply (x : E) (ξ : StrongDual 𝕜 E) :
    contMDiffLinearEval 𝕜 E n x ξ = ξ x :=
  (rfl)

/-- **Smooth polynomial evaluation on the continuous dual.** Extending `ξ ↦ ξ x` from generators
produces a `𝕜`-algebra homomorphism from `SymmetricAlgebra 𝕜 E` to the `C^n` scalar functions on
`StrongDual 𝕜 E`. -/
noncomputable def contMDiffEval :
    SymmetricAlgebra 𝕜 E →ₐ[𝕜] C^n⟮𝓘(𝕜, StrongDual 𝕜 E), StrongDual 𝕜 E; 𝕜⟯ :=
  lift (contMDiffLinearEval 𝕜 E n)

variable {𝕜 E}

@[simp]
theorem coe_contMDiffEval_ι (x : E) :
    ⇑(contMDiffEval 𝕜 E n (ι 𝕜 E x)) = ContinuousLinearMap.apply 𝕜 𝕜 x := by
  simp [contMDiffEval]

/-- Composing `SymmetricAlgebra.contMDiffEval` with evaluation at `ξ : StrongDual 𝕜 E` recovers the
algebraic evaluation `SymmetricAlgebra.lift ξ.toLinearMap`. -/
@[simp]
theorem evalAlgHom_comp_contMDiffEval (ξ : StrongDual 𝕜 E) :
    (ContMDiffMap.evalAlgHom ξ).comp (contMDiffEval 𝕜 E n) = lift ξ.toLinearMap := by
  ext x
  simp [contMDiffEval]

variable {n}

/-- Evaluating `contMDiffEval 𝕜 E n p` at `ξ : StrongDual 𝕜 E` computes the algebraic evaluation
`SymmetricAlgebra.lift ξ.toLinearMap p`. -/
@[simp]
theorem contMDiffEval_apply (p : SymmetricAlgebra 𝕜 E) (ξ : StrongDual 𝕜 E) :
    contMDiffEval 𝕜 E n p ξ = lift ξ.toLinearMap p := by
  have h := AlgHom.congr_fun (evalAlgHom_comp_contMDiffEval n ξ) p
  rwa [AlgHom.comp_apply, ContMDiffMap.evalAlgHom_apply] at h

/-- **Pointwise contravariant naturality of `contMDiffEval`.** Mapping symmetric tensors along a
continuous linear map `u : E →L[𝕜] F` corresponds to pulling smooth functions back along
`u.precomp 𝕜 : StrongDual 𝕜 F →L[𝕜] StrongDual 𝕜 E`. -/
theorem contMDiffEval_map {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (u : E →L[𝕜] F) (p : SymmetricAlgebra 𝕜 E) (ξ : StrongDual 𝕜 F) :
    contMDiffEval 𝕜 F n (map 𝕜 u.toLinearMap p) ξ = contMDiffEval 𝕜 E n p (ξ.comp u) := by
  simp

/-- Bundled form of `SymmetricAlgebra.contMDiffEval_map` using `ContMDiffMap.compRightAlgHom`. -/
theorem compRightAlgHom_precomp_comp_contMDiffEval {F : Type*} [NormedAddCommGroup F]
    [NormedSpace 𝕜 F] (n : ℕ∞ω) (u : E →L[𝕜] F) :
    (ContMDiffMap.compRightAlgHom 𝕜 𝕜
        ((u.precomp 𝕜 : StrongDual 𝕜 F →L[𝕜] StrongDual 𝕜 E) :
          C^n⟮𝓘(𝕜, StrongDual 𝕜 F), StrongDual 𝕜 F;
            𝓘(𝕜, StrongDual 𝕜 E), StrongDual 𝕜 E⟯)).comp
      (contMDiffEval 𝕜 E n) =
        (contMDiffEval 𝕜 F n).comp (map 𝕜 u.toLinearMap) := by
  refine AlgHom.ext fun p ↦ ?_
  refine (ContMDiffMap.compRightAlgHom_apply 𝕜 _ (contMDiffEval 𝕜 E n p)).trans ?_
  exact ContMDiffMap.ext fun ξ ↦ (contMDiffEval_map u p ξ).symm

/-- **Injectivity of smooth polynomial evaluation.** When `E` is finite-dimensional over a complete
nontrivially normed field `𝕜`, `SymmetricAlgebra.contMDiffEval 𝕜 E n` is injective. -/
theorem contMDiffEval_injective [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E] :
    Function.Injective (contMDiffEval 𝕜 E n) := by
  intro p q hpq
  refine TauCeti.SymmetricAlgebra.eq_of_forall_lift_apply_eq fun f ↦ ?_
  have hf := congr_arg (· f.toContinuousLinearMap) hpq
  simpa using hf

end Eval

end SymmetricAlgebra

namespace Module.Basis

section AffineLineDeriv

variable {𝕜 M ι : Type*} [NontriviallyNormedField 𝕜] [AddCommGroup M] [Module 𝕜 M] [Fintype ι]

/-- **Directional derivative along an affine line of linear forms.** For a finite basis `b` of `M`,
the derivative at `t₀` of `t ↦ SymmetricAlgebra.lift (ξ + t • η) p` is `η` paired with
`b.symmetricGradient p (ξ + t₀ • η)`. -/
theorem hasDerivAt_lift_add_smul (b : Module.Basis ι 𝕜 M) (p : SymmetricAlgebra 𝕜 M)
    (ξ η : Module.Dual 𝕜 M) (t₀ : 𝕜) :
    HasDerivAt (fun t : 𝕜 ↦ SymmetricAlgebra.lift (ξ + t • η) p)
      (η (b.symmetricGradient p (ξ + t₀ • η))) t₀ := by
  induction p using SymmetricAlgebra.induction with
  | algebraMap r =>
    rw [b.symmetricGradient_algebraMap, map_zero]
    simpa only [AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply] using
      hasDerivAt_const t₀ r
  | ι x =>
    rw [b.symmetricGradient_ι]
    simpa only [SymmetricAlgebra.lift_ι_apply, LinearMap.add_apply, LinearMap.smul_apply,
      smul_eq_mul, one_mul, id_eq] using ((hasDerivAt_id t₀).mul_const (η x)).const_add (ξ x)
  | add p q hp hq =>
    rw [b.symmetricGradient_add, map_add]
    simpa only [map_add] using hp.fun_add hq
  | mul p q hp hq =>
    have hmul := hp.fun_mul hq
    simp only [← map_mul] at hmul
    convert hmul using 1
    rw [b.symmetricGradient_mul, map_add, LinearMap.map_smul, LinearMap.map_smul, smul_eq_mul,
      smul_eq_mul]
    ring

/-- At `t = 0`, the directional derivative of `t ↦ SymmetricAlgebra.lift (ξ + t • η) p` is
`η (b.symmetricGradient p ξ)`. -/
theorem hasDerivAt_lift_add_smul_zero (b : Module.Basis ι 𝕜 M) (p : SymmetricAlgebra 𝕜 M)
    (ξ η : Module.Dual 𝕜 M) :
    HasDerivAt (fun t : 𝕜 ↦ SymmetricAlgebra.lift (ξ + t • η) p)
      (η (b.symmetricGradient p ξ)) 0 := by
  simpa using b.hasDerivAt_lift_add_smul p ξ η 0

theorem deriv_lift_add_smul (b : Module.Basis ι 𝕜 M) (p : SymmetricAlgebra 𝕜 M)
    (ξ η : Module.Dual 𝕜 M) (t₀ : 𝕜) :
    deriv (fun t : 𝕜 ↦ SymmetricAlgebra.lift (ξ + t • η) p) t₀ =
      η (b.symmetricGradient p (ξ + t₀ • η)) :=
  (b.hasDerivAt_lift_add_smul p ξ η t₀).deriv

theorem deriv_lift_add_smul_zero (b : Module.Basis ι 𝕜 M) (p : SymmetricAlgebra 𝕜 M)
    (ξ η : Module.Dual 𝕜 M) :
    deriv (fun t : 𝕜 ↦ SymmetricAlgebra.lift (ξ + t • η) p) 0 =
      η (b.symmetricGradient p ξ) :=
  (b.hasDerivAt_lift_add_smul_zero p ξ η).deriv

end AffineLineDeriv

section FDeriv

variable {𝕜 E ι : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [Fintype ι]

/-- **Fréchet derivative of polynomial evaluation on `StrongDual 𝕜 E`.** Under the biduality map
`ContinuousLinearMap.apply 𝕜 𝕜`, the Fréchet derivative at `ξ` of
`η ↦ SymmetricAlgebra.lift η.toLinearMap p` is `b.symmetricGradient p ξ.toLinearMap`. -/
theorem hasFDerivAt_lift (b : Module.Basis ι 𝕜 E) (p : SymmetricAlgebra 𝕜 E)
    (ξ : StrongDual 𝕜 E) :
    HasFDerivAt (fun η : StrongDual 𝕜 E ↦ SymmetricAlgebra.lift η.toLinearMap p)
      (ContinuousLinearMap.apply 𝕜 𝕜 (b.symmetricGradient p ξ.toLinearMap)) ξ := by
  induction p using SymmetricAlgebra.induction with
  | algebraMap r =>
    rw [b.symmetricGradient_algebraMap, map_zero]
    simpa only [AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply] using
      hasFDerivAt_const r ξ
  | ι x =>
    rw [b.symmetricGradient_ι]
    simp_rw [SymmetricAlgebra.lift_ι_apply, ContinuousLinearMap.coe_coe]
    exact (ContinuousLinearMap.apply 𝕜 𝕜 x : StrongDual 𝕜 E →L[𝕜] 𝕜).hasFDerivAt
  | add p q hp hq =>
    rw [b.symmetricGradient_add, map_add]
    simpa only [map_add] using hp.fun_add hq
  | mul p q hp hq =>
    rw [b.symmetricGradient_mul, map_add, map_smul, map_smul]
    simpa only [map_mul] using hp.fun_mul hq

/-- **Fréchet derivative of `SymmetricAlgebra.contMDiffEval`.** -/
theorem hasFDerivAt_contMDiffEval (b : Module.Basis ι 𝕜 E) (n : ℕ∞ω) (p : SymmetricAlgebra 𝕜 E)
    (ξ : StrongDual 𝕜 E) :
    HasFDerivAt (⇑(SymmetricAlgebra.contMDiffEval 𝕜 E n p))
      (ContinuousLinearMap.apply 𝕜 𝕜 (b.symmetricGradient p ξ.toLinearMap)) ξ := by
  have hfun : ⇑(SymmetricAlgebra.contMDiffEval 𝕜 E n p) =
      fun η : StrongDual 𝕜 E ↦ SymmetricAlgebra.lift η.toLinearMap p :=
    funext (SymmetricAlgebra.contMDiffEval_apply p)
  rw [hfun]
  exact b.hasFDerivAt_lift p ξ

theorem fderiv_contMDiffEval (b : Module.Basis ι 𝕜 E) (n : ℕ∞ω) (p : SymmetricAlgebra 𝕜 E)
    (ξ : StrongDual 𝕜 E) :
    fderiv 𝕜 (⇑(SymmetricAlgebra.contMDiffEval 𝕜 E n p)) ξ =
      ContinuousLinearMap.apply 𝕜 𝕜 (b.symmetricGradient p ξ.toLinearMap) :=
  (b.hasFDerivAt_contMDiffEval n p ξ).fderiv

theorem fderiv_contMDiffEval_apply (b : Module.Basis ι 𝕜 E) (n : ℕ∞ω) (p : SymmetricAlgebra 𝕜 E)
    (ξ η : StrongDual 𝕜 E) :
    fderiv 𝕜 (⇑(SymmetricAlgebra.contMDiffEval 𝕜 E n p)) ξ η =
      η (b.symmetricGradient p ξ.toLinearMap) := by
  rw [b.fderiv_contMDiffEval]
  rfl

theorem hasDerivAt_contMDiffEval_add_smul_zero (b : Module.Basis ι 𝕜 E) (n : ℕ∞ω)
    (p : SymmetricAlgebra 𝕜 E) (ξ η : StrongDual 𝕜 E) :
    HasDerivAt (fun t : 𝕜 ↦ SymmetricAlgebra.contMDiffEval 𝕜 E n p (ξ + t • η))
      (η (b.symmetricGradient p ξ.toLinearMap)) 0 := by
  simpa [SymmetricAlgebra.contMDiffEval_apply, ContinuousLinearMap.toLinearMap_add,
    FunLike.coe_smul] using b.hasDerivAt_lift_add_smul_zero p ξ.toLinearMap η.toLinearMap

end FDeriv

end Module.Basis
