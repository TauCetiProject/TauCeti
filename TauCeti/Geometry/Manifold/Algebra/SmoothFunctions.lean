/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Algebra.SmoothFunctions

/-!
# Algebraic operations on smooth maps

This file complements Mathlib's algebraic structures on spaces of smooth maps with the pointwise
evaluation of finite sums, with the pullback of smooth functions along a smooth map, and with the
transport of pointwise identities between scalar-valued smooth functions to identities in the
algebra of smooth functions.

## Main results

* `ContMDiffMap.coe_sum`: the coercion of a finite sum of smooth maps is the sum of the coercions.
* `ContMDiffMap.compRightAlgHom`: precomposition with a smooth map `φ : N → M`, as an algebra
  homomorphism `C^n⟮I, M; 𝓘(𝕜, A), A⟯ →ₐ[𝕜] C^n⟮J, N; 𝓘(𝕜, A), A⟯`.
* `TauCeti.sub_algebraMap_eq_sum_mul_sub_algebraMap`: the bundled form of a pointwise
  factorization of `g - g x` in the algebra of smooth functions.
-/

public section

open scoped ContDiff Manifold

namespace ContMDiffMap

/-- The coercion of a finite sum of smooth maps into a commutative additive Lie group is the
pointwise sum. -/
@[simp]
theorem coe_sum {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
    {N : Type*} [TopologicalSpace N] [ChartedSpace H N]
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
    {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'} {n : ℕ∞ω}
    {G : Type*} [AddCommMonoid G] [TopologicalSpace G] [ChartedSpace H' G] [ContMDiffAdd I' n G]
    {ι : Type*} (s : Finset ι) (f : ι → C^n⟮I, N; I', G⟯) :
    ⇑(∑ i ∈ s, f i) = ∑ i ∈ s, ⇑(f i) :=
  map_sum coeFnAddMonoidHom f s

section CompRight

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners 𝕜 E' H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace 𝕜 E'']
  {H'' : Type*} [TopologicalSpace H''] {K : ModelWithCorners 𝕜 E'' H''}
  {P : Type*} [TopologicalSpace P] [ChartedSpace H'' P] {n : ℕ∞ω}
  (A : Type*) [NormedRing A] [NormedAlgebra 𝕜 A] [ContMDiffRing 𝓘(𝕜, A) n A]

variable (𝕜) in
/-- Precomposition with a `C^n` map `φ : N → M`, as an algebra homomorphism from the `C^n`
functions on `M` to the `C^n` functions on `N`: the pullback `f ↦ f ∘ φ` of functions along `φ`.
This is the smooth analogue of `ContinuousMap.compRightAlgHom`. -/
def compRightAlgHom (φ : C^n⟮J, N; I, M⟯) :
    C^n⟮I, M; 𝓘(𝕜, A), A⟯ →ₐ[𝕜] C^n⟮J, N; 𝓘(𝕜, A), A⟯ where
  toFun f := f.comp φ
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

@[simp]
theorem compRightAlgHom_apply (φ : C^n⟮J, N; I, M⟯) (f : C^n⟮I, M; 𝓘(𝕜, A), A⟯) :
    compRightAlgHom 𝕜 A φ f = f.comp φ :=
  (rfl)

@[simp]
theorem compRightAlgHom_id :
    compRightAlgHom 𝕜 A (ContMDiffMap.id : C^n⟮I, M; I, M⟯) = AlgHom.id 𝕜 _ :=
  (rfl)

theorem compRightAlgHom_comp (φ : C^n⟮J, N; I, M⟯) (ψ : C^n⟮K, P; J, N⟯) :
    compRightAlgHom 𝕜 A (φ.comp ψ) = (compRightAlgHom 𝕜 A ψ).comp (compRightAlgHom 𝕜 A φ) :=
  (rfl)

end CompRight

end ContMDiffMap

namespace TauCeti

/-- **Hadamard's identity in the algebra of smooth functions.** A pointwise factorization of
`g - g x` through the functions `c i`, with coefficients `a i`, is an identity between the bundled
smooth maps themselves, the constants appearing as the images of `algebraMap`.

This is the pointwise-to-bundled transport: the hypothesis speaks of values, the conclusion of
elements of `C^n⟮I, M; 𝕜⟯`, and the two are related by evaluation being a ring homomorphism. -/
theorem sub_algebraMap_eq_sum_mul_sub_algebraMap {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {n : ℕ∞ω}
    {ι : Type*} [Fintype ι] (x : M) (g : C^n⟮I, M; 𝕜⟯) (a c : ι → C^n⟮I, M; 𝕜⟯)
    (h : ∀ y, g y - g x = ∑ i, a i y * (c i y - c i x)) :
    g - algebraMap 𝕜 C^n⟮I, M; 𝕜⟯ (g x) =
      ∑ i, a i * (c i - algebraMap 𝕜 C^n⟮I, M; 𝕜⟯ (c i x)) := by
  ext y
  calc
    (g - algebraMap 𝕜 C^n⟮I, M; 𝕜⟯ (g x)) y = g y - g x := rfl
    _ = ∑ i, a i y * (c i y - c i x) := h y
    _ = _ := by simp [Algebra.algebraMap_eq_smul_one]

end TauCeti
