/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
public import Mathlib.Geometry.Manifold.Algebra.SmoothFunctions
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-!
# Algebraic operations on smooth maps

This file complements Mathlib's algebraic structures on spaces of smooth maps with the pointwise
evaluation of finite sums, with the iterated derivatives of a difference of `C^n` maps between
normed spaces, and with the transport of pointwise identities between scalar-valued smooth
functions to identities in the algebra of smooth functions.

## Main results

* `ContMDiffMap.coe_sum`: the coercion of a finite sum of smooth maps is the sum of the coercions.
* `ContMDiffMap.iteratedFDeriv_sub_apply`: the iterated derivatives of order at most `n` of a
  difference of `C^n` maps are the differences of their iterated derivatives.
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

/-- The iterated derivatives of order at most `n` of a difference of `C^n` maps between normed
spaces are the differences of their iterated derivatives. -/
theorem iteratedFDeriv_sub_apply {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] {n : ℕ∞ω}
    (u v : C^n⟮𝓘(𝕜, E), E; 𝓘(𝕜, F), F⟯) {i : ℕ} (hi : i ≤ n) (z : E) :
    iteratedFDeriv 𝕜 i ⇑(u - v) z = iteratedFDeriv 𝕜 i u z - iteratedFDeriv 𝕜 i v z := by
  rw [coe_sub, _root_.iteratedFDeriv_sub_apply (u.contMDiff.contDiff.contDiffAt.of_le hi)
    (v.contMDiff.contDiff.contDiffAt.of_le hi)]

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
