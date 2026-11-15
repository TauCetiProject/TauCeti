/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap

/-!
# Evaluation and transpose identities for strong biduals

For topological modules `E`, `F`, and `G` over a normed field `𝕜` with spaces of continuous linear
maps carrying the topology of bounded convergence, `ContinuousLinearMap.applyₗ G (RingHom.id 𝕜)` is
the canonical evaluation map `E →ₗ[𝕜] (E →L[𝕜] G) →L[𝕜] G`, and `ContinuousLinearMap.precomp G T`
is the transpose `(F →L[𝕜] G) →L[𝕜] E →L[𝕜] G` of `T : E →L[𝕜] F`.

This file records the naturality of `applyₗ` with respect to double transposition `precomp G
(precomp G T)`, extending `ContinuousLinearMap.precomp_precomp_inclusionInDoubleDual` from normed
spaces to arbitrary topological modules, together with the pairing and naturality identities for
topological linear equivalences `e : E ≃L[𝕜] (E →L[𝕜] G) →L[𝕜] G` whose underlying pairing is
evaluation (`∀ x ℓ, e x ℓ = ℓ x`). In particular, `e.arrowCongr (ContinuousLinearEquiv.refl 𝕜 G)`
is the canonical evaluation equivalence of `E →L[𝕜] G`, and its inverse is the transpose
`precomp G e.toContinuousLinearMap`.

## Main results

* `ContinuousLinearMap.comp_precomp_applyₗ` and
  `ContinuousLinearMap.precomp_precomp_comp_applyₗ`: naturality of `applyₗ` under double
  precomposition.
* `ContinuousLinearEquiv.toContinuousLinearMap_arrowCongr_refl` and
  `ContinuousLinearEquiv.toContinuousLinearMap_arrowCongr_refl_symm`: `e.arrowCongr (.refl 𝕜 G)`
  is `precomp G e.symm.toContinuousLinearMap`, and its inverse is
  `precomp G e.toContinuousLinearMap`.
* `ContinuousLinearEquiv.arrowCongr_refl_apply_of_forall_apply_eq` and
  `ContinuousLinearEquiv.toLinearMap_arrowCongr_refl_of_forall_apply_eq`: if `e : E ≃L[𝕜]
  (E →L[𝕜] G) →L[𝕜] G` acts by evaluation, then `e.arrowCongr (.refl 𝕜 G)` is canonical evaluation
  `applyₗ G (RingHom.id 𝕜)` on `E →L[𝕜] G`, so the canonical bidual equivalence of `E →L[𝕜] G` is
  the inverse of the transpose of `e`.
* `ContinuousLinearEquiv.precomp_precomp_comp_eq_comp`: naturality of evaluation equivalences with
  respect to continuous linear maps.
-/

public section

namespace ContinuousLinearMap

variable {𝕜 E F G : Type*} [NormedField 𝕜]
  [AddCommGroup E] [TopologicalSpace E] [Module 𝕜 E] [ContinuousSMul 𝕜 E]
  [AddCommGroup F] [TopologicalSpace F] [Module 𝕜 F] [ContinuousSMul 𝕜 F]
  [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
  [Module 𝕜 G] [ContinuousConstSMul 𝕜 G]

/-- Precomposing evaluation at `x` with the transpose `precomp G T` gives evaluation at `T x`. -/
@[simp]
theorem comp_precomp_applyₗ (T : E →L[𝕜] F) (x : E) :
    (applyₗ G (RingHom.id 𝕜) x).comp (precomp G T) = applyₗ G (RingHom.id 𝕜) (T x) :=
  (rfl)

/-- Double precomposition intertwines the canonical evaluation maps `applyₗ`. -/
theorem precomp_precomp_comp_applyₗ (T : E →L[𝕜] F) :
    (precomp G (precomp G T)).toLinearMap.comp (applyₗ G (RingHom.id 𝕜)) =
      (applyₗ G (RingHom.id 𝕜)).comp T.toLinearMap :=
  (rfl)

end ContinuousLinearMap

namespace ContinuousLinearEquiv

section ArrowCongr

variable {𝕜 E F G : Type*} [NormedField 𝕜]
  [AddCommGroup E] [TopologicalSpace E] [Module 𝕜 E]
  [AddCommGroup F] [TopologicalSpace F] [Module 𝕜 F]
  [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
  [Module 𝕜 G] [ContinuousConstSMul 𝕜 G]

/-- `e.arrowCongr (.refl 𝕜 G)` as a continuous linear map is precomposition with `e.symm`. -/
@[simp]
theorem toContinuousLinearMap_arrowCongr_refl (e : E ≃L[𝕜] F) :
    (e.arrowCongr (ContinuousLinearEquiv.refl 𝕜 G)).toContinuousLinearMap =
      ContinuousLinearMap.precomp G e.symm.toContinuousLinearMap :=
  (rfl)

/-- The inverse of `e.arrowCongr (.refl 𝕜 G)` is precomposition with `e`. -/
theorem toContinuousLinearMap_arrowCongr_refl_symm (e : E ≃L[𝕜] F) :
    (e.arrowCongr (ContinuousLinearEquiv.refl 𝕜 G)).symm.toContinuousLinearMap =
      ContinuousLinearMap.precomp G e.toContinuousLinearMap :=
  (rfl)

omit [AddCommGroup F] [TopologicalSpace F] [Module 𝕜 F] in
/-- If `e : E ≃L[𝕜] (E →L[𝕜] G) →L[𝕜] G` acts by evaluation, then `e.arrowCongr (.refl 𝕜 G)` also
acts by evaluation on `E →L[𝕜] G`. Consequently, when `G = 𝕜`, the canonical bidual equivalence of
`StrongDual 𝕜 E` is the inverse of the strong transpose `precomp 𝕜 e.toContinuousLinearMap`. -/
theorem arrowCongr_refl_apply_of_forall_apply_eq
    (e : E ≃L[𝕜] (E →L[𝕜] G) →L[𝕜] G) (he : ∀ x ℓ, e x ℓ = ℓ x)
    (ℓ : E →L[𝕜] G) (Ψ : (E →L[𝕜] G) →L[𝕜] G) :
    e.arrowCongr (ContinuousLinearEquiv.refl 𝕜 G) ℓ Ψ = Ψ ℓ := by
  rw [arrowCongr_apply, refl_apply, ← he, e.apply_symm_apply]

/-- Naturality of evaluation equivalences: if `e₁` and `e₂` act by evaluation, then the double
transpose `precomp G (precomp G T)` intertwines `e₁` and `e₂` with `T`. -/
theorem precomp_precomp_comp_eq_comp
    (e₁ : E ≃L[𝕜] (E →L[𝕜] G) →L[𝕜] G) (he₁ : ∀ x ℓ, e₁ x ℓ = ℓ x)
    (e₂ : F ≃L[𝕜] (F →L[𝕜] G) →L[𝕜] G) (he₂ : ∀ y m, e₂ y m = m y)
    (T : E →L[𝕜] F) :
    (ContinuousLinearMap.precomp G (ContinuousLinearMap.precomp G T)).comp
        e₁.toContinuousLinearMap =
      e₂.toContinuousLinearMap.comp T := by
  ext x m
  simp [he₁, he₂]

end ArrowCongr

/-- If `e : E ≃L[𝕜] (E →L[𝕜] G) →L[𝕜] G` acts by evaluation, then the underlying linear map of
`e.arrowCongr (.refl 𝕜 G)` is canonical evaluation `applyₗ G (RingHom.id 𝕜)` on `E →L[𝕜] G`, and
its inverse is the transpose `precomp G e.toContinuousLinearMap`. -/
theorem toLinearMap_arrowCongr_refl_of_forall_apply_eq
    {𝕜 E G : Type*} [NormedField 𝕜]
    [AddCommGroup E] [TopologicalSpace E] [Module 𝕜 E]
    [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [Module 𝕜 G] [ContinuousSMul 𝕜 G]
    (e : E ≃L[𝕜] (E →L[𝕜] G) →L[𝕜] G) (he : ∀ x ℓ, e x ℓ = ℓ x) :
    (e.arrowCongr (ContinuousLinearEquiv.refl 𝕜 G)).toLinearMap =
      ContinuousLinearMap.applyₗ G (RingHom.id 𝕜) := by
  ext ℓ Ψ
  exact arrowCongr_refl_apply_of_forall_apply_eq e he ℓ Ψ

end ContinuousLinearEquiv
