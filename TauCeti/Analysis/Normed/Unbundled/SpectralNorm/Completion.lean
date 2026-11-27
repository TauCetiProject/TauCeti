/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Completion
public import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
public import Mathlib.Topology.Algebra.Algebra.Equiv
public import TauCeti.Topology.Algebra.UniformRing

import Mathlib.Topology.MetricSpace.Completion
import TauCeti.Analysis.Normed.Unbundled.SpectralNorm.Basic

/-!
# Algebra isomorphisms of algebraic extensions extend to completions

Let `K` be a complete field with an ultrametric absolute value, and `E`, `E'` normed fields over
`K` with `E` algebraic over `K`. Both norms are spectral norms, so every `K`-algebra isomorphism
`φ : E ≃ₐ[K] E'` is an isometry (`AlgHom.isometry`), and it extends to a continuous `K`-algebra
isomorphism `φ.completion` of the uniform completions. This file develops that extension: it agrees
with `φ` on `E`, is the unique continuous map doing so, is an isometry, and is functorial in `φ`.

Functoriality gives the transport of automorphisms between completions: completing the conjugate
`AlgEquiv.autCongr φ σ` of an automorphism `σ` of `E` gives the conjugate of `σ.completion` by
`φ.completion`. Applied to two algebraic closures of a complete non-archimedean field, this
compares the actions of the absolute Galois group on the two completed algebraic closures.

## Main definitions

* `AlgEquiv.completion φ`: the extension `Completion E ≃A[K] Completion E'` of a `K`-algebra
  isomorphism `φ : E ≃ₐ[K] E'` of normed fields with `E` algebraic over `K`.

## Main results

* `AlgEquiv.completion_coe`: `φ.completion` extends `φ`.
* `AlgEquiv.eq_completion_of_continuous`: it is the unique continuous map extending `φ`.
* `AlgEquiv.isometry_completion`: it is an isometry.
* `AlgEquiv.completion_refl`, `AlgEquiv.completion_trans`, `AlgEquiv.completion_symm`:
  functoriality.
* `AlgEquiv.completion_autCongr`: completion commutes with conjugation.
* `AlgEquiv.coe_completion_restrictScalars`: the extension does not depend on the base field.

## References

* A. J. de Jong and M. van der Put, *Étale cohomology of rigid analytic spaces*, Documenta Math.
  1 (1996), §3.6.
-/

public section

noncomputable section

open UniformSpace

namespace AlgEquiv

variable {K E E' E'' : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [NormedField E] [NormedAlgebra K E] [Algebra.IsAlgebraic K E]
  [NormedField E'] [NormedAlgebra K E'] [NormedField E''] [NormedAlgebra K E'']

/-- The inverse of a `K`-algebra isomorphism of normed fields, algebraic over a complete
ultrametric field `K`, is an isometry. -/
theorem isometry_symm_of_isAlgebraic (φ : E ≃ₐ[K] E') : Isometry φ.symm :=
  φ.toAlgHom.isometry.right_inv φ.apply_symm_apply

/-- The extension `Completion E ≃A[K] Completion E'` of a `K`-algebra isomorphism
`φ : E ≃ₐ[K] E'` of normed fields with `E` algebraic over a complete ultrametric field `K`: the
completion of `φ`, which is an isometry (`AlgHom.isometry`). -/
def completion (φ : E ≃ₐ[K] E') : Completion E ≃A[K] Completion E' where
  toAlgEquiv := Completion.mapAlgEquiv φ φ.toAlgHom.isometry.continuous
    φ.isometry_symm_of_isAlgebraic.continuous
  continuous_toFun := Completion.continuous_mapAlgEquiv φ _ _
  continuous_invFun := Completion.continuous_mapAlgEquiv_symm φ _ _

/-- `φ.completion` is the completion of `φ`. -/
theorem completion_apply (φ : E ≃ₐ[K] E') (x : Completion E) :
    φ.completion x = Completion.map φ x :=
  Completion.mapAlgEquiv_apply φ _ _ x

/-- The inverse of `φ.completion` is the completion of `φ.symm`. -/
theorem completion_symm_apply (φ : E ≃ₐ[K] E') (y : Completion E') :
    φ.completion.symm y = Completion.map φ.symm y :=
  Completion.mapAlgEquiv_symm_apply φ _ _ y

/-- `φ.completion` extends `φ`. -/
@[simp]
theorem completion_coe (φ : E ≃ₐ[K] E') (x : E) : φ.completion x = (φ x : Completion E') :=
  Completion.mapAlgEquiv_coe φ _ _ x

/-- The inverse of `φ.completion` extends `φ.symm`. -/
@[simp]
theorem completion_symm_coe (φ : E ≃ₐ[K] E') (y : E') :
    φ.completion.symm y = (φ.symm y : Completion E) := by
  rw [ContinuousAlgEquiv.symm_apply_eq, completion_coe, apply_symm_apply]

/-- **Uniqueness of the extension**: a continuous map `Completion E → Completion E'` extending
`φ` is `φ.completion`. -/
theorem eq_completion_of_continuous (φ : E ≃ₐ[K] E') {f : Completion E → Completion E'}
    (hf : Continuous f) (h : ∀ x : E, f x = (φ x : Completion E')) : f = φ.completion :=
  Completion.ext hf φ.completion.continuous fun x ↦ by rw [h, completion_coe]

/-- `φ.completion` is an isometry. -/
theorem isometry_completion (φ : E ≃ₐ[K] E') : Isometry φ.completion := by
  have h : ⇑φ.completion = Completion.map φ := funext φ.completion_apply
  rw [h]
  exact φ.toAlgHom.isometry.completion_map

/-- `φ.completion` preserves the norm. -/
@[simp]
theorem norm_completion (φ : E ≃ₐ[K] E') (x : Completion E) : ‖φ.completion x‖ = ‖x‖ := by
  simpa using φ.isometry_completion.norm_map_of_map_zero (map_zero _) x

/-- `φ ↦ φ.completion` is injective: `φ.completion` restricts to `φ` on `E`. -/
theorem completion_injective : Function.Injective (completion (K := K) (E := E) (E' := E')) :=
  fun φ ψ h ↦ ext fun x ↦ Completion.coe_injective E' <| by
    rw [← completion_coe, ← completion_coe, h]

/-- The extension of the identity is the identity. -/
@[simp]
theorem completion_refl :
    (AlgEquiv.refl : E ≃ₐ[K] E).completion = ContinuousAlgEquiv.refl K (Completion E) :=
  ContinuousAlgEquiv.ext (eq_completion_of_continuous _ continuous_id fun _ ↦ rfl).symm

/-- **Functoriality**: the extension of `φ.trans ψ` is `φ.completion.trans ψ.completion`. -/
theorem completion_trans [Algebra.IsAlgebraic K E'] (φ : E ≃ₐ[K] E') (ψ : E' ≃ₐ[K] E'') :
    (φ.trans ψ).completion = φ.completion.trans ψ.completion :=
  ContinuousAlgEquiv.ext <| (eq_completion_of_continuous _
    (ψ.completion.continuous.comp φ.completion.continuous) fun x ↦ by
      rw [Function.comp_apply, completion_coe, completion_coe, trans_apply]).symm

/-- `(φ.trans ψ).completion x = ψ.completion (φ.completion x)`. -/
@[simp]
theorem completion_trans_apply [Algebra.IsAlgebraic K E'] (φ : E ≃ₐ[K] E') (ψ : E' ≃ₐ[K] E'')
    (x : Completion E) : (φ.trans ψ).completion x = ψ.completion (φ.completion x) := by
  rw [completion_trans, ContinuousAlgEquiv.trans_apply]

/-- The inverse of `φ.completion` is the extension of `φ.symm`. -/
@[simp]
theorem completion_symm [Algebra.IsAlgebraic K E'] (φ : E ≃ₐ[K] E') :
    φ.completion.symm = φ.symm.completion :=
  ContinuousAlgEquiv.ext <| funext fun y ↦ by
    rw [completion_symm_apply, completion_apply]

/-- **Transport of automorphisms**: the extension of the conjugate `φ σ φ⁻¹` (an automorphism of
`E'`) of an automorphism `σ` of `E` by `φ : E ≃ₐ[K] E'` is the conjugate of `σ.completion` by
`φ.completion`. -/
theorem completion_autCongr [Algebra.IsAlgebraic K E'] (φ : E ≃ₐ[K] E') (σ : E ≃ₐ[K] E) :
    (autCongr φ σ).completion = φ.completion.symm.trans (σ.completion.trans φ.completion) := by
  rw [autCongr_apply, completion_trans, completion_trans, completion_symm]

/-- `(autCongr φ σ).completion y = φ.completion (σ.completion (φ.completion.symm y))`. -/
theorem completion_autCongr_apply [Algebra.IsAlgebraic K E'] (φ : E ≃ₐ[K] E') (σ : E ≃ₐ[K] E)
    (y : Completion E') :
    (autCongr φ σ).completion y = φ.completion (σ.completion (φ.completion.symm y)) := by
  rw [completion_autCongr, ContinuousAlgEquiv.trans_apply, ContinuousAlgEquiv.trans_apply]

section Tower

variable {L : Type*} [NormedField L] [IsUltrametricDist L] [CompleteSpace L] [Algebra K L]
  [NormedAlgebra L E] [Algebra.IsAlgebraic L E] [NormedAlgebra L E'] [IsScalarTower K L E]
  [IsScalarTower K L E']

/-- **The extension does not depend on the base field.** For a tower `K → L → E`, the extension of
an `L`-algebra isomorphism `φ` computed over `L` is the extension of `φ` viewed as a `K`-algebra
isomorphism. -/
@[simp]
theorem coe_completion_restrictScalars (φ : E ≃ₐ[L] E') :
    ⇑((φ.restrictScalars K).completion) = ⇑φ.completion :=
  funext fun x ↦ by rw [completion_apply, completion_apply, coe_restrictScalars]

end Tower

end AlgEquiv
