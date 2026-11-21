/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Degree.Basic

/-!
# Mapping degree under postcomposition with diffeomorphisms

Postcomposing an arbitrary map `f` between oriented manifolds with a `C^n` diffeomorphism
(`n ≠ 0`) multiplies `degreeAtRegularValue` by the orientation sign of the diffeomorphism at the
target point, without any differentiability assumption on `f`. (Precomposition lemmas are in
`TauCeti.Geometry.Manifold.Degree.Basic`.)

These invariance properties allow smooth-degree computations to rechart the target manifold along a
diffeomorphism, such as `TauCeti.BoundarylessModel.diffeomorph` or
`ContinuousLinearEquiv.toTransContinuousLinearEquiv`, without changing the signed preimage count.

## Main results

* `Diffeomorph.degreeAtRegularValue_diffeomorph_comp_apply`,
  `Diffeomorph.degreeAtRegularValue_diffeomorph_comp`: postcomposing `f` with a diffeomorphism `h`
  multiplies `degreeAtRegularValue` by the orientation sign of `h`.
* `Diffeomorph.degreeAtRegularValue_diffeomorph_comp_apply_of_isOrientationPreservingAt`,
  `Diffeomorph.degreeAtRegularValue_diffeomorph_comp_apply_of_isOrientationReversingAt`: invariance
  and negation of `degreeAtRegularValue` under orientation-preserving or orientation-reversing
  postcomposition.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Chapter 17, section Degree Theory.
* J. W. Milnor, *Topology from the Differentiable Viewpoint*, University Press of Virginia, 1965,
  §5.
-/

public section

noncomputable section

open Function Set TauCeti TauCeti.Manifold.Orientation
open scoped ContDiff Manifold

namespace Diffeomorph

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 1 M]
  {E' H' N : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'} [TopologicalSpace N] [ChartedSpace H' N]
  [IsManifold J 1 N]
  {E'' H'' P : Type*} [NormedAddCommGroup E''] [NormedSpace ℝ E''] [FiniteDimensional ℝ E'']
  [TopologicalSpace H''] {K : ModelWithCorners ℝ E'' H''} [TopologicalSpace P] [ChartedSpace H'' P]
  [IsManifold K 1 P]
  {ι : Type*} [Fintype ι] {n : ℕ∞ω}

/-- **Degree at a value under postcomposition with a diffeomorphism.** Postcomposing `f : M → N`
with a `C^n` diffeomorphism `h : N ≃ₘ^n⟮J, K⟯ P` (`n ≠ 0`) multiplies the signed preimage count
over `y` by the orientation sign of `h` at `y`. -/
theorem degreeAtRegularValue_diffeomorph_comp_apply (h : N ≃ₘ^n⟮J, K⟯ P) (hn : n ≠ 0)
    (o : Manifold.Orientation I M ι) (o' : Manifold.Orientation J N ι)
    (o'' : Manifold.Orientation K P ι) (f : M → N) (y : N) :
    degreeAtRegularValue o o'' (h ∘ f) (h y) =
      orientationSign o' o'' h y * degreeAtRegularValue o o' f y := by
  have hpre : (h ∘ f) ⁻¹' {h y} = f ⁻¹' {y} := by
    ext x
    simp [EquivLike.apply_eq_iff_eq h]
  rw [degreeAtRegularValue_def, degreeAtRegularValue_def, hpre, mul_finsum_mem]
  refine finsum_mem_congr rfl fun x hx ↦ ?_
  rw [h.orientationSign_diffeomorph_comp hn o o' o'' f x, mem_preimage.1 hx]

/-- `Diffeomorph.degreeAtRegularValue_diffeomorph_comp_apply` stated at a point `z` of the
target. -/
theorem degreeAtRegularValue_diffeomorph_comp (h : N ≃ₘ^n⟮J, K⟯ P) (hn : n ≠ 0)
    (o : Manifold.Orientation I M ι) (o' : Manifold.Orientation J N ι)
    (o'' : Manifold.Orientation K P ι) (f : M → N) (z : P) :
    degreeAtRegularValue o o'' (h ∘ f) z =
      orientationSign o' o'' h (h.symm z) * degreeAtRegularValue o o' f (h.symm z) := by
  conv_lhs => rw [← h.apply_symm_apply z]
  exact h.degreeAtRegularValue_diffeomorph_comp_apply hn o o' o'' f (h.symm z)

/-- Postcomposing `f` with a `C^n` diffeomorphism `h` (`n ≠ 0`) that preserves orientations at `y`
leaves the signed preimage count over `y` unchanged. -/
theorem degreeAtRegularValue_diffeomorph_comp_apply_of_isOrientationPreservingAt
    (h : N ≃ₘ^n⟮J, K⟯ P) (hn : n ≠ 0) {o : Manifold.Orientation I M ι}
    {o' : Manifold.Orientation J N ι} {o'' : Manifold.Orientation K P ι} (f : M → N) {y : N}
    (hh : IsOrientationPreservingAt o' o'' h y) :
    degreeAtRegularValue o o'' (h ∘ f) (h y) = degreeAtRegularValue o o' f y := by
  rw [h.degreeAtRegularValue_diffeomorph_comp_apply hn o o' o'' f y,
    orientationSign_of_isOrientationPreservingAt hh, one_mul]

/-- Postcomposing `f` with a `C^n` diffeomorphism `h` (`n ≠ 0`) that reverses orientations at `y`
negates the signed preimage count over `y`. -/
theorem degreeAtRegularValue_diffeomorph_comp_apply_of_isOrientationReversingAt
    (h : N ≃ₘ^n⟮J, K⟯ P) (hn : n ≠ 0) {o : Manifold.Orientation I M ι}
    {o' : Manifold.Orientation J N ι} {o'' : Manifold.Orientation K P ι} (f : M → N) {y : N}
    (hh : IsOrientationReversingAt o' o'' h y) :
    degreeAtRegularValue o o'' (h ∘ f) (h y) = -degreeAtRegularValue o o' f y := by
  rw [h.degreeAtRegularValue_diffeomorph_comp_apply hn o o' o'' f y,
    orientationSign_of_isOrientationReversingAt hh, neg_one_mul]

end Diffeomorph
