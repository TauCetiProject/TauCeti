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

Postcomposing an arbitrary map `f` between oriented manifolds with a `C^n` diffeomorphism
(`n ≠ 0`) multiplies `degreeAtRegularValue` by the orientation sign of the diffeomorphism at the
target point, while precomposing with a diffeomorphism that preserves or reverses orientations along
the fibre (respectively everywhere) preserves or negates `degreeAtRegularValue` (respectively
`TauCeti.degree`), without any differentiability assumption on `f`.

These invariance properties allow smooth-degree computations to rechart either manifold along a
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
* `Diffeomorph.degreeAtRegularValue_comp_diffeomorph_of_isOrientationPreservingAt`,
  `Diffeomorph.degreeAtRegularValue_comp_diffeomorph_of_isOrientationReversingAt`: invariance and
  negation of `degreeAtRegularValue` under precomposition preserving or reversing orientations
  along the fibre.
* `Diffeomorph.degree_comp_diffeomorph_of_isOrientationPreservingAt`,
  `Diffeomorph.degree_comp_diffeomorph_of_isOrientationReversingAt`: invariance and negation of
  `TauCeti.degree` under everywhere orientation-preserving or orientation-reversing precomposition.

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

/-- Precomposing `f` with a `C^n` diffeomorphism `h` (`n ≠ 0`) that preserves orientations along
the fibre over `y` leaves the signed preimage count over `y` unchanged. -/
theorem degreeAtRegularValue_comp_diffeomorph_of_isOrientationPreservingAt
    (h : P ≃ₘ^n⟮K, I⟯ M) (hn : n ≠ 0) {o : Manifold.Orientation I M ι}
    {o' : Manifold.Orientation J N ι} {o'' : Manifold.Orientation K P ι} (f : M → N) {y : N}
    (hh : ∀ x, f (h x) = y → IsOrientationPreservingAt o'' o h x) :
    degreeAtRegularValue o'' o' (f ∘ h) y = degreeAtRegularValue o o' f y := by
  rw [degreeAtRegularValue_def, degreeAtRegularValue_def]
  refine finsum_mem_eq_of_bijOn h
    (by rw [preimage_comp]; exact (EquivLike.bijective h).bijOn_preimage) fun x hx ↦ ?_
  rw [h.orientationSign_comp_diffeomorph hn o o' o'' f x,
    orientationSign_of_isOrientationPreservingAt (hh x hx), mul_one]

/-- Precomposing `f` with a `C^n` diffeomorphism `h` (`n ≠ 0`) that reverses orientations along
the fibre over `y` negates the signed preimage count over `y`. -/
theorem degreeAtRegularValue_comp_diffeomorph_of_isOrientationReversingAt
    (h : P ≃ₘ^n⟮K, I⟯ M) (hn : n ≠ 0) {o : Manifold.Orientation I M ι}
    {o' : Manifold.Orientation J N ι} {o'' : Manifold.Orientation K P ι} (f : M → N) {y : N}
    (hh : ∀ x, f (h x) = y → IsOrientationReversingAt o'' o h x) :
    degreeAtRegularValue o'' o' (f ∘ h) y = -degreeAtRegularValue o o' f y := by
  rw [← neg_eq_iff_eq_neg, ← degreeAtRegularValue_neg_left]
  exact h.degreeAtRegularValue_comp_diffeomorph_of_isOrientationPreservingAt hn f
    fun x hx ↦ (isOrientationPreservingAt_neg_left o'' o h x).2 (hh x hx)

/-- Precomposing `f` with an everywhere orientation-preserving `C^n` diffeomorphism `h` (`n ≠ 0`)
leaves `TauCeti.degree` unchanged. -/
theorem degree_comp_diffeomorph_of_isOrientationPreservingAt
    (h : P ≃ₘ^n⟮K, I⟯ M) (hn : n ≠ 0) {o : Manifold.Orientation I M ι}
    {o' : Manifold.Orientation J N ι} {o'' : Manifold.Orientation K P ι} (f : M → N)
    (hh : ∀ x, IsOrientationPreservingAt o'' o h x) :
    degree o'' o' (f ∘ h) = degree o o' f := by
  by_cases hex : ∃ y, IsRegularValue I J f y
  · have hex' : ∃ y, IsRegularValue K J (f ∘ h) y :=
      ⟨hex.choose, (h.isRegularValue_comp_diffeomorph_iff hn f hex.choose).2 hex.choose_spec⟩
    have hchoose : hex'.choose = hex.choose := by
      have hpred : (fun y ↦ IsRegularValue K J (f ∘ h) y) = fun y ↦ IsRegularValue I J f y :=
        funext fun y ↦ propext (h.isRegularValue_comp_diffeomorph_iff hn f y)
      -- `hex'.choose` and `hex.choose` apply `Exists.choose` to equal predicates.
      congr 1
    rw [degree_eq_degreeAtRegularValue_choose hex', degree_eq_degreeAtRegularValue_choose hex,
      hchoose]
    exact h.degreeAtRegularValue_comp_diffeomorph_of_isOrientationPreservingAt hn f
      fun x _ ↦ hh x
  · have hex' : ¬∃ y, IsRegularValue K J (f ∘ h) y := fun ⟨y, hy⟩ ↦
      hex ⟨y, (h.isRegularValue_comp_diffeomorph_iff hn f y).1 hy⟩
    rw [degree_of_not_exists hex', degree_of_not_exists hex]

/-- Precomposing `f` with an everywhere orientation-reversing `C^n` diffeomorphism `h` (`n ≠ 0`)
negates `TauCeti.degree`. -/
theorem degree_comp_diffeomorph_of_isOrientationReversingAt
    (h : P ≃ₘ^n⟮K, I⟯ M) (hn : n ≠ 0) {o : Manifold.Orientation I M ι}
    {o' : Manifold.Orientation J N ι} {o'' : Manifold.Orientation K P ι} (f : M → N)
    (hh : ∀ x, IsOrientationReversingAt o'' o h x) :
    degree o'' o' (f ∘ h) = -degree o o' f := by
  rw [← neg_eq_iff_eq_neg, ← degree_neg_left]
  exact h.degree_comp_diffeomorph_of_isOrientationPreservingAt hn f
    fun x ↦ (isOrientationPreservingAt_neg_left o'' o h x).2 (hh x)

end Diffeomorph
