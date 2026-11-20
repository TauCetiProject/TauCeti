/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace

import TauCeti.LinearAlgebra.Dual.Lemmas

/-!
# Surjective differentials in local coordinates

A surjective continuous linear map composed with a vector-valued map whose manifold derivative is
surjective has a surjective vector-valued manifold derivative. Composing a local coordinate system
with a projection onto some of its coordinates therefore gives local equations whose differential
is surjective.

Conversely, finitely many scalar functions with linearly independent differentials at a point
keep a surjective joint differential when read through a local diffeomorphism from the model
space, such as the inverse of a smooth chart.
-/

public section

open scoped Manifold

namespace TauCeti

variable {𝕜 E H M F G : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H} [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]

/-- A surjective continuous linear map composed with a map whose manifold derivative at `x` is
surjective has a surjective vector-valued manifold derivative at `x`. No differentiability or
finite-dimensionality assumption is needed. -/
theorem mvfderiv_comp_surjective {f : M → F} {x : M}
    (hf : Function.Surjective (mfderiv I 𝓘(𝕜, F) f x))
    (L : F →L[𝕜] G) (hL : Function.Surjective L) :
    Function.Surjective (mvfderiv I (L ∘ f) x) := by
  by_cases hfd : MDifferentiableAt I 𝓘(𝕜, F) f x
  · rw [mvfderiv_comp x L.mdifferentiableAt hfd, mvfderiv_eq_fderiv, L.fderiv]
    exact hL.comp ((NormedSpace.fromTangentSpace (𝕜 := 𝕜) (f x)).surjective.comp hf)
  -- Without differentiability the derivative is `0`, so `F`, and hence `G`, is the zero space.
  rw [mfderiv_zero_of_not_mdifferentiableAt hfd] at hf
  have : Subsingleton G := ⟨fun a b ↦ by
    obtain ⟨u, rfl⟩ := hL a
    obtain ⟨v, rfl⟩ := hL b
    obtain ⟨_, rfl⟩ := hf u
    obtain ⟨_, rfl⟩ := hf v
    rfl⟩
  exact fun _ ↦ ⟨0, Subsingleton.elim _ _⟩

/-- Finitely many scalar functions with linearly independent differentials at `φ v`, read through a
local diffeomorphism `φ` at `v` from the model space, have a surjective joint derivative at `v`. -/
theorem _root_.IsLocalDiffeomorphAt.surjective_fderiv_pi_comp {ι : Type*} [Finite ι]
    {n : WithTop ℕ∞} {φ : E → M} {v : E} (hφ : IsLocalDiffeomorphAt 𝓘(𝕜, E) I n φ v)
    (hn : n ≠ 0) {ρ : ι → M → 𝕜} (hρ : ∀ i, MDifferentiableAt I 𝓘(𝕜) (ρ i) (φ v))
    (hlin : LinearIndependent 𝕜 fun i ↦ mvfderiv I (ρ i) (φ v)) :
    Function.Surjective (fderiv 𝕜 (fun w i ↦ ρ i (φ w)) v) := by
  let : Fintype ι := Fintype.ofFinite ι
  let ℓ : ι → E →L[𝕜] 𝕜 := fun i ↦ mvfderiv I (ρ i) (φ v)
  let D : E →L[𝕜] E := mfderiv 𝓘(𝕜, E) I φ v
  have hd : HasFDerivAt (fun w i ↦ ρ i (φ w)) ((ContinuousLinearMap.pi ℓ).comp D) v := by
    refine hasFDerivAt_pi'.mpr fun i ↦ ?_
    have h := HasMFDerivAt.comp v (hρ i).hasMFDerivAt (hφ.mdifferentiableAt hn).hasMFDerivAt
    exact hasMFDerivAt_iff_hasFDerivAt.mp h
  rw [hd.fderiv]
  have hpi : Function.Surjective (ContinuousLinearMap.pi ℓ) := by
    have hlin' : LinearIndependent 𝕜 fun i ↦ (ℓ i : E →ₗ[𝕜] 𝕜) :=
      LinearIndependent.map' (v := ℓ) hlin (ContinuousLinearMap.coeLM 𝕜)
        (LinearMap.ker_eq_bot.mpr ContinuousLinearMap.coe_injective)
    intro w
    obtain ⟨u, hu⟩ := LinearIndependent.pi_surjective hlin' w
    exact ⟨u, hu⟩
  -- The differential of a local diffeomorphism is invertible, hence surjective.
  obtain ⟨L, hL⟩ := hφ.isInvertible_mfderiv hn
  refine hpi.comp fun w ↦ ?_
  obtain ⟨u, hu⟩ := L.surjective w
  exact ⟨u, (congrArg (fun f : E →L[𝕜] E ↦ f u) hL).symm.trans hu⟩

/-- Finitely many scalar functions with linearly independent differentials at `e.symm v`, read
in a chart `e` which is `C^n` in both directions, `n ≠ 0`, have a surjective joint derivative
at `v`. -/
theorem _root_.OpenPartialHomeomorph.surjective_fderiv_pi_comp_symm {ι : Type*} [Finite ι]
    {n : WithTop ℕ∞} (e : OpenPartialHomeomorph M E) (hes : ContMDiffOn I 𝓘(𝕜, E) n e e.source)
    (het : ContMDiffOn 𝓘(𝕜, E) I n e.symm e.target) (hn : n ≠ 0) {v : E} (hv : v ∈ e.target)
    {ρ : ι → M → 𝕜} (hρ : ∀ i, MDifferentiableAt I 𝓘(𝕜) (ρ i) (e.symm v))
    (hlin : LinearIndependent 𝕜 fun i ↦ mvfderiv I (ρ i) (e.symm v)) :
    Function.Surjective (fderiv 𝕜 (fun w i ↦ ρ i (e.symm w)) v) := by
  let Φ : PartialDiffeomorph 𝓘(𝕜, E) I E M n :=
    { e.symm.toPartialEquiv with
      open_source := e.open_target
      open_target := e.open_source
      contMDiffOn_toFun := het
      contMDiffOn_invFun := hes }
  exact IsLocalDiffeomorphAt.surjective_fderiv_pi_comp (φ := e.symm)
    (PartialDiffeomorph.isLocalDiffeomorphAt 𝓘(𝕜, E) I n Φ hv) hn hρ hlin

end TauCeti
