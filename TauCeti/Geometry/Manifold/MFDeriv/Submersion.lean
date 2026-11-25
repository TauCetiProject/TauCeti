/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace

import TauCeti.LinearAlgebra.Dual.Lemmas

/-!
# Surjective differentials in local coordinates

A surjective continuous linear map composed with a vector-valued map whose manifold derivative is
surjective has a surjective vector-valued manifold derivative. Composing a local coordinate system
with a projection onto some of its coordinates therefore gives local equations whose differential
is surjective.

Conversely, finitely many scalar functions with linearly independent differentials at a point
keep a surjective joint differential when read through a differentiable map from a normed space
with surjective differential, such as the inverse of a chart differentiable in both directions.
-/

public section

open scoped Manifold Topology

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
map `φ` from a normed space which is differentiable at `v` with surjective differential, have a
surjective joint derivative at `v`. -/
theorem _root_.MDifferentiableAt.surjective_fderiv_pi_comp {ι : Type*} [Finite ι] {φ : F → M}
    {v : F} (hφ : MDifferentiableAt 𝓘(𝕜, F) I φ v)
    (hφs : Function.Surjective (mfderiv 𝓘(𝕜, F) I φ v)) {ρ : ι → M → 𝕜}
    (hlin : LinearIndependent 𝕜 fun i ↦ mvfderiv I (ρ i) (φ v)) :
    Function.Surjective (fderiv 𝕜 (fun w i ↦ ρ i (φ w)) v) := by
  let : Fintype ι := Fintype.ofFinite ι
  let ℓ : ι → E →L[𝕜] 𝕜 := fun i ↦ mvfderiv I (ρ i) (φ v)
  -- Each `ρ i` is differentiable at `φ v`, since otherwise its differential would vanish.
  have hρ (i : ι) : MDifferentiableAt I 𝓘(𝕜) (ρ i) (φ v) := by
    by_contra h
    exact hlin.ne_zero i (by simp [mvfderiv, mfderiv_zero_of_not_mdifferentiableAt h])
  let D : F →L[𝕜] E := mfderiv 𝓘(𝕜, F) I φ v
  have hd : HasFDerivAt (fun w i ↦ ρ i (φ w)) ((ContinuousLinearMap.pi ℓ).comp D) v := by
    refine hasFDerivAt_pi'.mpr fun i ↦ ?_
    have h := HasMFDerivAt.comp v (hρ i).hasMFDerivAt hφ.hasMFDerivAt
    exact hasMFDerivAt_iff_hasFDerivAt.mp h
  rw [hd.fderiv]
  have hpi : Function.Surjective (ContinuousLinearMap.pi ℓ) := by
    have hlin' : LinearIndependent 𝕜 fun i ↦ (ℓ i : E →ₗ[𝕜] 𝕜) :=
      LinearIndependent.map' (v := ℓ) hlin (ContinuousLinearMap.coeLM 𝕜)
        (LinearMap.ker_eq_bot.mpr ContinuousLinearMap.coe_injective)
    intro w
    obtain ⟨u, hu⟩ := LinearIndependent.pi_surjective hlin' w
    exact ⟨u, by simpa only [← ContinuousLinearMap.coe_pi, ContinuousLinearMap.coe_coe] using hu⟩
  exact hpi.comp hφs

/-- Finitely many scalar functions with linearly independent differentials at `e.symm v`, read
in a chart `e` which is differentiable at `e.symm v` and whose inverse is differentiable at `v`,
have a surjective joint derivative at `v`. -/
theorem _root_.OpenPartialHomeomorph.surjective_fderiv_pi_comp_symm {ι : Type*} [Finite ι]
    (e : OpenPartialHomeomorph M E) {v : E} (hv : v ∈ e.target)
    (he : MDifferentiableAt I 𝓘(𝕜, E) e (e.symm v))
    (hes : MDifferentiableAt 𝓘(𝕜, E) I e.symm v) {ρ : ι → M → 𝕜}
    (hlin : LinearIndependent 𝕜 fun i ↦ mvfderiv I (ρ i) (e.symm v)) :
    Function.Surjective (fderiv 𝕜 (fun w i ↦ ρ i (e.symm w)) v) := by
  refine hes.surjective_fderiv_pi_comp (fun w ↦ ⟨mfderiv I 𝓘(𝕜, E) e (e.symm v) w, ?_⟩) hlin
  -- Near `e.symm v` the composite `e.symm ∘ e` is the identity, so `mfderiv e` is a right
  -- inverse of `mfderiv e.symm`.
  have hid : (e.symm ∘ e) =ᶠ[𝓝 (e.symm v)] id :=
    Filter.mem_of_superset (e.open_source.mem_nhds (e.map_target hv)) fun _ hy ↦ e.left_inv hy
  rw [← mfderiv_comp_apply_of_eq (e.symm v) hes he (e.right_inv hv), hid.mfderiv_eq, mfderiv_id]
  -- What remains is `tangentSpaceCast` between tangent spaces of `M`, all equal to `E`, which is
  -- the identity by definition.
  rfl

end TauCeti
