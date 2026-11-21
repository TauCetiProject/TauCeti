/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Degree.Basic
import TauCeti.Geometry.Manifold.RegularValue.Diffeomorph

/-!
# Mapping degree under diffeomorphisms

Precomposing or postcomposing an arbitrary map `f` between oriented manifolds with a `C^n`
diffeomorphism (`n ≠ 0`) preserves or negates `degreeAtRegularValue` and `degree` according to
whether the diffeomorphism is orientation-preserving or orientation-reversing, and more generally
postcomposing multiplies `degreeAtRegularValue` by the orientation sign of the diffeomorphism at the
target point, without any differentiability assumption on `f`.

These invariance properties allow smooth-degree computations to rechart the source or target
manifold along a diffeomorphism, such as `TauCeti.BoundarylessModel.diffeomorph` or
`ContinuousLinearEquiv.toTransContinuousLinearEquiv`, without changing the signed preimage count.

## Main results

* `Diffeomorph.degreeAtRegularValue_comp_diffeomorph_of_isOrientationPreservingAt`,
  `Diffeomorph.degreeAtRegularValue_comp_diffeomorph_of_isOrientationReversingAt`,
  `Diffeomorph.degree_comp_diffeomorph_of_isOrientationPreservingAt`,
  `Diffeomorph.degree_comp_diffeomorph_of_isOrientationReversingAt`: precomposing with a `C^n`
  diffeomorphism (`n ≠ 0`) preserves or negates `degreeAtRegularValue` and `degree`.
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

section Precomp

variable {E' H' M' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  [TopologicalSpace M'] [ChartedSpace H' M'] [IsManifold I' 1 M']
  {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  {F G N : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  [TopologicalSpace N] [ChartedSpace G N] [IsManifold J 1 N]
  {ι : Type*} [Fintype ι] {n : ℕ∞ω}

/-- Precomposing with an orientation-preserving `C^n` diffeomorphism (`n ≠ 0`) leaves
`degreeAtRegularValue` unchanged at every point of `N`. -/
theorem degreeAtRegularValue_comp_diffeomorph_of_isOrientationPreservingAt
    (Φ : M' ≃ₘ^n⟮I', I⟯ M) (hn : n ≠ 0)
    {o' : Manifold.Orientation I' M' ι} {o : Manifold.Orientation I M ι}
    (oN : Manifold.Orientation J N ι) (ho : ∀ x, IsOrientationPreservingAt o' o Φ x)
    (f : M → N) (y : N) :
    degreeAtRegularValue o' oN (f ∘ Φ) y = degreeAtRegularValue o oN f y := by
  rw [degreeAtRegularValue_def, degreeAtRegularValue_def, preimage_comp]
  refine finsum_mem_eq_of_bijOn Φ (EquivLike.bijective Φ).bijOn_preimage fun x _ ↦ ?_
  rw [Φ.orientationSign_comp_diffeomorph hn o' o oN f x,
    orientationSign_of_isOrientationPreservingAt (ho x), mul_one]

/-- Precomposing with an orientation-reversing `C^n` diffeomorphism (`n ≠ 0`) negates
`degreeAtRegularValue` at every point of `N`. -/
theorem degreeAtRegularValue_comp_diffeomorph_of_isOrientationReversingAt
    (Φ : M' ≃ₘ^n⟮I', I⟯ M) (hn : n ≠ 0)
    {o' : Manifold.Orientation I' M' ι} {o : Manifold.Orientation I M ι}
    (oN : Manifold.Orientation J N ι) (ho : ∀ x, IsOrientationReversingAt o' o Φ x)
    (f : M → N) (y : N) :
    degreeAtRegularValue o' oN (f ∘ Φ) y = -degreeAtRegularValue o oN f y := by
  have h := Φ.degreeAtRegularValue_comp_diffeomorph_of_isOrientationPreservingAt hn
    (o' := -o') (o := o) oN (fun x ↦ (isOrientationPreservingAt_neg_left o' o Φ x).2 (ho x)) f y
  rwa [degreeAtRegularValue_neg_left, neg_eq_iff_eq_neg] at h

/-- Precomposing with an orientation-preserving `C^n` diffeomorphism (`n ≠ 0`) preserves
`degree`. -/
theorem degree_comp_diffeomorph_of_isOrientationPreservingAt
    (Φ : M' ≃ₘ^n⟮I', I⟯ M) (hn : n ≠ 0)
    {o' : Manifold.Orientation I' M' ι} {o : Manifold.Orientation I M ι}
    (oN : Manifold.Orientation J N ι) (ho : ∀ x, IsOrientationPreservingAt o' o Φ x)
    (f : M → N) :
    degree o' oN (f ∘ Φ) = degree o oN f := by
  have hp : (fun y ↦ IsRegularValue I' J (f ∘ Φ) y) = fun y ↦ IsRegularValue I J f y :=
    funext fun _ ↦ propext (Φ.isRegularValue_comp_iff hn)
  by_cases h : ∃ y, IsRegularValue I J f y
  · have h' : ∃ y, IsRegularValue I' J (f ∘ Φ) y := hp ▸ h
    have hchoose {P Q : N → Prop} (hPQ : P = Q) (hP : ∃ y, P y) (hQ : ∃ y, Q y) :
        hP.choose = hQ.choose := by
      subst hPQ
      rfl
    rw [degree_eq_degreeAtRegularValue_choose h', degree_eq_degreeAtRegularValue_choose h,
      Φ.degreeAtRegularValue_comp_diffeomorph_of_isOrientationPreservingAt hn oN ho,
      hchoose hp h' h]
  · have h' : ¬∃ y, IsRegularValue I' J (f ∘ Φ) y := fun ⟨y, hy⟩ ↦
      h ⟨y, (Φ.isRegularValue_comp_iff hn).1 hy⟩
    rw [degree_eq_zero_of_not_exists h', degree_eq_zero_of_not_exists h]

/-- Precomposing with an orientation-reversing `C^n` diffeomorphism (`n ≠ 0`) negates `degree`. -/
theorem degree_comp_diffeomorph_of_isOrientationReversingAt
    (Φ : M' ≃ₘ^n⟮I', I⟯ M) (hn : n ≠ 0)
    {o' : Manifold.Orientation I' M' ι} {o : Manifold.Orientation I M ι}
    (oN : Manifold.Orientation J N ι) (ho : ∀ x, IsOrientationReversingAt o' o Φ x)
    (f : M → N) :
    degree o' oN (f ∘ Φ) = -degree o oN f := by
  have h := Φ.degree_comp_diffeomorph_of_isOrientationPreservingAt hn
    (o' := -o') (o := o) oN (fun x ↦ (isOrientationPreservingAt_neg_left o' o Φ x).2 (ho x)) f
  rwa [degree_neg_left, neg_eq_iff_eq_neg] at h

end Precomp

section Postcomp

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

end Postcomp

end Diffeomorph
