/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Module.Dual.Functoriality
public import TauCeti.Analysis.Normed.Module.TensorProduct.InjectiveSeminorm

/-!
# Functoriality of the projective and injective tensor products

Bounded operators `f : E →L[𝕜] E'` and `g : F →L[𝕜] F'` induce the operator
`x ⊗ₜ y ↦ f x ⊗ₜ g y` on algebraic tensor products. This file shows that it is bounded, with norm
at most `‖f‖ * ‖g‖`, for both the projective and the injective seminorm. Together with the values
on pure tensors over `ℝ` and `ℂ`, this says that both are uniform cross norms. The induced
operators `ProjectiveTensor.mapL f g` and `InjectiveTensor.mapL f g` respect identities and
composition, and the contraction from the projective to the injective tensor product is natural
with respect to them. Composing the operator that the universal property
`ProjectiveTensor.liftIsometry` attaches to a bilinear map with `ProjectiveTensor.mapL f g`
precomposes that bilinear map with `f` and `g`.

On the dual of `E'`, the operator induced by `map f g u` is
`g ∘L contractStrongDual u ∘L f*`, where `f*` is the adjoint `ContinuousLinearMap.precomp 𝕜 f`
(`TensorProduct.contractStrongDual_map`); with `‖f*‖ ≤ ‖f‖` this gives the injective bound.

## Main definitions

* `TauCeti.ProjectiveTensor.mapL` and `TauCeti.InjectiveTensor.mapL`: the operators induced by a
  pair of bounded operators.

## Main results

* `TensorProduct.projectiveSeminorm_map_le` and `TensorProduct.injectiveSeminorm_map_le`: the
  seminorm of `map f g u` is at most `‖f‖ * ‖g‖` times the seminorm of `u`.
* `TauCeti.ProjectiveTensor.norm_mapL_le` and `TauCeti.InjectiveTensor.norm_mapL_le`:
  `‖mapL f g‖ ≤ ‖f‖ * ‖g‖`.
* `TauCeti.ProjectiveTensor.mapL_comp` and `TauCeti.InjectiveTensor.mapL_comp`: functoriality.
* `TauCeti.ProjectiveTensor.toInjectiveTensor_comp_mapL`: naturality of the contraction from the
  projective to the injective tensor product.

## References

* R. A. Ryan, *Introduction to Tensor Products of Banach Spaces*, Springer, 2002, §§2.1, 3.1.

The construction of `ProjectiveTensor.mapL` follows Mathlib's `PiTensorProduct.mapL` for the
projective seminorm on finite-family tensor products.
-/

public section

open scoped TensorProduct

namespace TensorProduct

variable {𝕜 E E' F F' : Type*} [NontriviallyNormedField 𝕜]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] [SeminormedAddCommGroup E'] [NormedSpace 𝕜 E']
  [SeminormedAddCommGroup F] [NormedSpace 𝕜 F] [SeminormedAddCommGroup F'] [NormedSpace 𝕜 F']

/-- The projective seminorm of `map f g u` is at most `‖f‖ * ‖g‖` times that of `u`. -/
theorem projectiveSeminorm_map_le (f : E →L[𝕜] E') (g : F →L[𝕜] F') (u : E ⊗[𝕜] F) :
    projectiveSeminorm 𝕜 E' F' (map f.toLinearMap g.toLinearMap u) ≤
      ‖f‖ * ‖g‖ * projectiveSeminorm 𝕜 E F u :=
  apply_le_mul_projectiveSeminorm (by positivity) (fun x y ↦
    calc projectiveSeminorm 𝕜 E' F' (map f.toLinearMap g.toLinearMap (x ⊗ₜ y))
        ≤ ‖f x‖ * ‖g y‖ := projectiveSeminorm_tmul_le (f x) (g y)
      _ ≤ (‖f‖ * ‖x‖) * (‖g‖ * ‖y‖) := by gcongr <;> exact ContinuousLinearMap.le_opNorm _ _
      _ = ‖f‖ * ‖g‖ * (‖x‖ * ‖y‖) := by ring) u

/-- The operator on the dual induced by `map f g u` is `g ∘L contractStrongDual u ∘L f*`, where
`f*` is the adjoint of `f`. -/
theorem contractStrongDual_map (f : E →L[𝕜] E') (g : F →L[𝕜] F') (u : E ⊗[𝕜] F) :
    contractStrongDual 𝕜 E' F' (map f.toLinearMap g.toLinearMap u) =
      g ∘L contractStrongDual 𝕜 E F u ∘L
        (ContinuousLinearMap.precomp 𝕜 f : StrongDual 𝕜 E' →L[𝕜] StrongDual 𝕜 E) := by
  induction u with
  | tmul x y => ext φ; simp
  | add u v hu hv => simp [hu, hv, ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_add]

/-- The injective seminorm of `map f g u` is at most `‖f‖ * ‖g‖` times that of `u`. -/
theorem injectiveSeminorm_map_le (f : E →L[𝕜] E') (g : F →L[𝕜] F') (u : E ⊗[𝕜] F) :
    injectiveSeminorm 𝕜 E' F' (map f.toLinearMap g.toLinearMap u) ≤
      ‖f‖ * ‖g‖ * injectiveSeminorm 𝕜 E F u := by
  rw [injectiveSeminorm_apply, injectiveSeminorm_apply, contractStrongDual_map]
  calc ‖g ∘L contractStrongDual 𝕜 E F u ∘L
        (ContinuousLinearMap.precomp 𝕜 f : StrongDual 𝕜 E' →L[𝕜] StrongDual 𝕜 E)‖
      ≤ ‖g‖ * (‖contractStrongDual 𝕜 E F u‖ *
          ‖(ContinuousLinearMap.precomp 𝕜 f : StrongDual 𝕜 E' →L[𝕜] StrongDual 𝕜 E)‖) :=
        (ContinuousLinearMap.opNorm_comp_le _ _).trans
          (by gcongr; exact ContinuousLinearMap.opNorm_comp_le _ _)
    _ ≤ ‖g‖ * (‖contractStrongDual 𝕜 E F u‖ * ‖f‖) := by
        gcongr; exact ContinuousLinearMap.norm_precomp_le f
    _ = ‖f‖ * ‖g‖ * ‖contractStrongDual 𝕜 E F u‖ := by ring

end TensorProduct

namespace TauCeti

variable {𝕜 E E' E'' F F' F'' G : Type*} [NontriviallyNormedField 𝕜]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] [SeminormedAddCommGroup E'] [NormedSpace 𝕜 E']
  [SeminormedAddCommGroup E''] [NormedSpace 𝕜 E'']
  [SeminormedAddCommGroup F] [NormedSpace 𝕜 F] [SeminormedAddCommGroup F'] [NormedSpace 𝕜 F']
  [SeminormedAddCommGroup F''] [NormedSpace 𝕜 F'']
  [SeminormedAddCommGroup G] [NormedSpace 𝕜 G]

namespace ProjectiveTensor

/-- The bounded operator `x ⊗ₜ y ↦ f x ⊗ₜ g y` between projective tensor products induced by
bounded operators `f` and `g`. -/
noncomputable def mapL (f : E →L[𝕜] E') (g : F →L[𝕜] F') :
    ProjectiveTensor 𝕜 E F →L[𝕜] ProjectiveTensor 𝕜 E' F' :=
  LinearMap.mkContinuous ((linearEquiv 𝕜 E' F').symm.toLinearMap ∘ₗ
      _root_.TensorProduct.map f.toLinearMap g.toLinearMap ∘ₗ (linearEquiv 𝕜 E F).toLinearMap)
    (‖f‖ * ‖g‖) fun u ↦ by
      simpa [norm_def] using TensorProduct.projectiveSeminorm_map_le f g u.toTensorProduct

/-- The induced operator acts on the underlying tensor by `TensorProduct.map`. -/
@[simp]
theorem mapL_apply (f : E →L[𝕜] E') (g : F →L[𝕜] F') (u : ProjectiveTensor 𝕜 E F) :
    mapL f g u = ⟨_root_.TensorProduct.map f.toLinearMap g.toLinearMap u.toTensorProduct⟩ := by
  simp [mapL]

/-- The induced operator sends `x ⊗ₜ y` to `f x ⊗ₜ g y`. -/
theorem mapL_tmul (f : E →L[𝕜] E') (g : F →L[𝕜] F') (x : E) (y : F) :
    mapL f g ⟨x ⊗ₜ y⟩ = ⟨f x ⊗ₜ g y⟩ := by
  simp

/-- The operator induced by `f` and `g` on projective tensor products has norm at most
`‖f‖ * ‖g‖`. -/
theorem norm_mapL_le (f : E →L[𝕜] E') (g : F →L[𝕜] F') : ‖mapL f g‖ ≤ ‖f‖ * ‖g‖ :=
  LinearMap.mkContinuous_norm_le _ (by positivity) _

/-- The identity operators induce the identity of the projective tensor product. -/
@[simp]
theorem mapL_id :
    mapL (ContinuousLinearMap.id 𝕜 E) (ContinuousLinearMap.id 𝕜 F) =
      ContinuousLinearMap.id 𝕜 (ProjectiveTensor 𝕜 E F) :=
  continuousLinearMap_ext fun _ _ ↦ by simp

/-- The operator induced on projective tensor products respects composition. -/
theorem mapL_comp (f₂ : E' →L[𝕜] E'') (f₁ : E →L[𝕜] E') (g₂ : F' →L[𝕜] F'') (g₁ : F →L[𝕜] F') :
    mapL (f₂ ∘L f₁) (g₂ ∘L g₁) = mapL f₂ g₂ ∘L mapL f₁ g₁ :=
  continuousLinearMap_ext fun _ _ ↦ by simp

/-- Composing the operator induced by a bilinear map `B` with `mapL f g` gives the operator
induced by `(x, y) ↦ B (f x) (g y)`. -/
theorem liftIsometry_comp_mapL (B : E' →L[𝕜] F' →L[𝕜] G) (f : E →L[𝕜] E') (g : F →L[𝕜] F') :
    liftIsometry 𝕜 E' F' G B ∘L mapL f g = liftIsometry 𝕜 E F G (B.bilinearComp f g) :=
  continuousLinearMap_ext fun x y ↦ by simp

end ProjectiveTensor

namespace InjectiveTensor

/-- The bounded operator `x ⊗ₜ y ↦ f x ⊗ₜ g y` between injective tensor products induced by
bounded operators `f` and `g`. -/
noncomputable def mapL (f : E →L[𝕜] E') (g : F →L[𝕜] F') :
    InjectiveTensor 𝕜 E F →L[𝕜] InjectiveTensor 𝕜 E' F' :=
  LinearMap.mkContinuous ((linearEquiv 𝕜 E' F').symm.toLinearMap ∘ₗ
      _root_.TensorProduct.map f.toLinearMap g.toLinearMap ∘ₗ (linearEquiv 𝕜 E F).toLinearMap)
    (‖f‖ * ‖g‖) fun u ↦ by
      simpa [norm_def] using TensorProduct.injectiveSeminorm_map_le f g u.toTensorProduct

/-- The induced operator acts on the underlying tensor by `TensorProduct.map`. -/
@[simp]
theorem mapL_apply (f : E →L[𝕜] E') (g : F →L[𝕜] F') (u : InjectiveTensor 𝕜 E F) :
    mapL f g u = ⟨_root_.TensorProduct.map f.toLinearMap g.toLinearMap u.toTensorProduct⟩ := by
  simp [mapL]

/-- The induced operator sends `x ⊗ₜ y` to `f x ⊗ₜ g y`. -/
theorem mapL_tmul (f : E →L[𝕜] E') (g : F →L[𝕜] F') (x : E) (y : F) :
    mapL f g ⟨x ⊗ₜ y⟩ = ⟨f x ⊗ₜ g y⟩ := by
  simp

/-- The operator induced by `f` and `g` on injective tensor products has norm at most
`‖f‖ * ‖g‖`. -/
theorem norm_mapL_le (f : E →L[𝕜] E') (g : F →L[𝕜] F') : ‖mapL f g‖ ≤ ‖f‖ * ‖g‖ :=
  LinearMap.mkContinuous_norm_le _ (by positivity) _

/-- The identity operators induce the identity of the injective tensor product. -/
@[simp]
theorem mapL_id :
    mapL (ContinuousLinearMap.id 𝕜 E) (ContinuousLinearMap.id 𝕜 F) =
      ContinuousLinearMap.id 𝕜 (InjectiveTensor 𝕜 E F) :=
  continuousLinearMap_ext fun _ _ ↦ by simp

/-- The operator induced on injective tensor products respects composition. -/
theorem mapL_comp (f₂ : E' →L[𝕜] E'') (f₁ : E →L[𝕜] E') (g₂ : F' →L[𝕜] F'') (g₁ : F →L[𝕜] F') :
    mapL (f₂ ∘L f₁) (g₂ ∘L g₁) = mapL f₂ g₂ ∘L mapL f₁ g₁ :=
  continuousLinearMap_ext fun _ _ ↦ by simp

end InjectiveTensor

/-- The contraction from the projective to the injective tensor product is natural: it
intertwines the operators induced by `f` and `g`. -/
theorem ProjectiveTensor.toInjectiveTensor_comp_mapL (f : E →L[𝕜] E') (g : F →L[𝕜] F') :
    ProjectiveTensor.toInjectiveTensor 𝕜 E' F' ∘L ProjectiveTensor.mapL f g =
      InjectiveTensor.mapL f g ∘L ProjectiveTensor.toInjectiveTensor 𝕜 E F :=
  ProjectiveTensor.continuousLinearMap_ext fun x y ↦ by simp

end TauCeti
