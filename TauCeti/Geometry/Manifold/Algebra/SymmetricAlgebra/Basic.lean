/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Algebra.SmoothFunctions
public import TauCeti.LinearAlgebra.SymmetricAlgebra.Evaluation
public import TauCeti.LinearAlgebra.SymmetricAlgebra.Functoriality
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
`E` is continuous and `𝕜` is infinite, so `SymmetricAlgebra.contMDiffEval` is injective.

## Main definitions

* `SymmetricAlgebra.contMDiffLinearEval`: the `𝕜`-linear map sending `x : E` to `ξ ↦ ξ x` in
  `C^n⟮𝓘(𝕜, StrongDual 𝕜 E), StrongDual 𝕜 E; 𝕜⟯`.
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

## References

* J. E. Marsden and T. S. Ratiu, *Introduction to Mechanics and Symmetry*, 2nd ed., Springer
  (1999), §10.1 (smooth polynomial functions on the dual of a Lie algebra).
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
