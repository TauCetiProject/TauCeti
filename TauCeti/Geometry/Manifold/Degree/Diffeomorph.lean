/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Degree.Basic

/-!
# Invariance of mapping degree under diffeomorphisms

For oriented real `C¹` manifolds of the same finite dimension, the orientation sign of a map
composed on either side with a `C^r` diffeomorphism (`r ≠ 0`) is unconditionally the product of the
orientation signs (`Diffeomorph.orientationSign_comp_diffeomorph`,
`Diffeomorph.orientationSign_diffeomorph_comp`). Precomposing `f : M → N` with a source
diffeomorphism `Φ` that preserves (reverses) orientations on the fibre over `y` leaves
`degreeAtRegularValue` at `y` unchanged (negates it), and precomposing with an everywhere
orientation-preserving (reversing) diffeomorphism leaves the global mapping degree `TauCeti.degree`
unchanged (negates it), since regular values are preserved
(`Diffeomorph.isRegularValue_comp_diffeomorph_iff`).

Likewise, postcomposing `f` with a target diffeomorphism `Ψ` multiplies the degree by the
orientation sign of `Ψ` (`Diffeomorph.degreeAtRegularValue_diffeomorph_comp`): the degree of
`Ψ ∘ f` at `Ψ y` equals `orientationSign o' o₁' Ψ y` times the degree of `f` at `y`. In particular,
when `Ψ` preserves (reverses) orientations at `y`, the degree of `Ψ ∘ f` at `Ψ y` equals (is minus)
the degree of `f` at `y`.

## Main results

* `Diffeomorph.degreeAtRegularValue_comp_diffeomorph_of_isOrientationPreservingAt`,
  `Diffeomorph.degreeAtRegularValue_comp_diffeomorph_of_isOrientationReversingAt`,
  `Diffeomorph.degree_comp_diffeomorph_of_isOrientationPreservingAt`,
  `Diffeomorph.degree_comp_diffeomorph_of_isOrientationReversingAt`: invariance of the degree under
  a diffeomorphism of the source.
* `Diffeomorph.degreeAtRegularValue_diffeomorph_comp`,
  `Diffeomorph.degreeAtRegularValue_diffeomorph_comp_of_isOrientationPreservingAt`,
  `Diffeomorph.degreeAtRegularValue_diffeomorph_comp_of_isOrientationReversingAt`: transformation of
  the degree at a value under a diffeomorphism of the target.
-/

public section

noncomputable section

open Function Set TauCeti TauCeti.Manifold.Orientation
open scoped Manifold ContDiff

namespace Diffeomorph

variable {E₁ H₁ M' : Type*} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [FiniteDimensional ℝ E₁]
  [TopologicalSpace H₁] {I' : ModelWithCorners ℝ E₁ H₁} [TopologicalSpace M'] [ChartedSpace H₁ M']
  [IsManifold I' 1 M']
  {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 1 M]
  {E' H' N : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'} [TopologicalSpace N] [ChartedSpace H' N]
  [IsManifold J 1 N]
  {E₂' H₂' N' : Type*} [NormedAddCommGroup E₂'] [NormedSpace ℝ E₂'] [FiniteDimensional ℝ E₂']
  [TopologicalSpace H₂'] {J' : ModelWithCorners ℝ E₂' H₂'} [TopologicalSpace N']
  [ChartedSpace H₂' N'] [IsManifold J' 1 N']
  {ι : Type*} [Fintype ι] {r : ℕ∞ω}

/-- **Diffeomorphism invariance of `degreeAtRegularValue` on the right.** If a `C^r` diffeomorphism
`Φ` (`r ≠ 0`) preserves orientations at every preimage of `y`, then `f ∘ Φ` and `f` have the same
degree at `y`. -/
theorem degreeAtRegularValue_comp_diffeomorph_of_isOrientationPreservingAt (Φ : M' ≃ₘ^r⟮I', I⟯ M)
    (hr : r ≠ 0) {o₁ : Manifold.Orientation I' M' ι} {o : Manifold.Orientation I M ι}
    (o' : Manifold.Orientation J N ι) {f : M → N} {y : N}
    (hΦ : ∀ x, f (Φ x) = y → IsOrientationPreservingAt o₁ o Φ x) :
    degreeAtRegularValue o₁ o' (f ∘ Φ) y = degreeAtRegularValue o o' f y := by
  rw [degreeAtRegularValue_def, degreeAtRegularValue_def]
  refine finsum_mem_eq_of_bijOn Φ ⟨fun x hx ↦ hx, Φ.injective.injOn, fun z hz ↦
    ⟨Φ.symm z, by simpa [Function.comp_apply] using hz, Φ.apply_symm_apply z⟩⟩ fun x hx ↦ ?_
  rw [Φ.orientationSign_comp_diffeomorph hr o₁ o o',
    orientationSign_of_isOrientationPreservingAt (hΦ x hx), mul_one]

/-- If a `C^r` diffeomorphism `Φ` (`r ≠ 0`) reverses orientations at every preimage of `y`, then
precomposing with `Φ` negates `degreeAtRegularValue` at `y`. -/
theorem degreeAtRegularValue_comp_diffeomorph_of_isOrientationReversingAt (Φ : M' ≃ₘ^r⟮I', I⟯ M)
    (hr : r ≠ 0) {o₁ : Manifold.Orientation I' M' ι} {o : Manifold.Orientation I M ι}
    (o' : Manifold.Orientation J N ι) {f : M → N} {y : N}
    (hΦ : ∀ x, f (Φ x) = y → IsOrientationReversingAt o₁ o Φ x) :
    degreeAtRegularValue o₁ o' (f ∘ Φ) y = -degreeAtRegularValue o o' f y := by
  rw [← neg_inj, ← degreeAtRegularValue_neg_left, neg_neg]
  exact Φ.degreeAtRegularValue_comp_diffeomorph_of_isOrientationPreservingAt hr o' fun x hx ↦
    (isOrientationPreservingAt_neg_left o₁ o Φ x).2 (hΦ x hx)

/-- **Diffeomorphism invariance of `degree` on the right.** Precomposing with an everywhere
orientation-preserving `C^r` diffeomorphism (`r ≠ 0`) leaves `TauCeti.degree` unchanged. -/
theorem degree_comp_diffeomorph_of_isOrientationPreservingAt (Φ : M' ≃ₘ^r⟮I', I⟯ M) (hr : r ≠ 0)
    {o₁ : Manifold.Orientation I' M' ι} {o : Manifold.Orientation I M ι}
    (o' : Manifold.Orientation J N ι) (f : M → N)
    (hΦ : ∀ x, IsOrientationPreservingAt o₁ o Φ x) :
    degree o₁ o' (f ∘ Φ) = degree o o' f := by
  have hpred : (fun y ↦ IsRegularValue I' J (f ∘ Φ) y) = fun y ↦ IsRegularValue I J f y :=
    funext fun y ↦ propext (Φ.isRegularValue_comp_diffeomorph_iff hr)
  by_cases h : ∃ y, IsRegularValue I J f y
  · have h' : ∃ y, IsRegularValue I' J (f ∘ Φ) y := by rwa [hpred]
    have hchoose : h'.choose = h.choose := by congr! 1
    rw [degree_eq_degreeAtRegularValue_choose h', degree_eq_degreeAtRegularValue_choose h, hchoose]
    exact Φ.degreeAtRegularValue_comp_diffeomorph_of_isOrientationPreservingAt hr o' fun x _ ↦ hΦ x
  · have h' : ¬∃ y, IsRegularValue I' J (f ∘ Φ) y := by rwa [hpred]
    rw [degree_eq_zero_of_not_exists h', degree_eq_zero_of_not_exists h]

/-- Precomposing with an everywhere orientation-reversing `C^r` diffeomorphism (`r ≠ 0`) negates
`TauCeti.degree`. -/
theorem degree_comp_diffeomorph_of_isOrientationReversingAt (Φ : M' ≃ₘ^r⟮I', I⟯ M) (hr : r ≠ 0)
    {o₁ : Manifold.Orientation I' M' ι} {o : Manifold.Orientation I M ι}
    (o' : Manifold.Orientation J N ι) (f : M → N)
    (hΦ : ∀ x, IsOrientationReversingAt o₁ o Φ x) :
    degree o₁ o' (f ∘ Φ) = -degree o o' f := by
  rw [← neg_inj, ← degree_neg_left, neg_neg]
  exact Φ.degree_comp_diffeomorph_of_isOrientationPreservingAt hr o' f fun x ↦
    (isOrientationPreservingAt_neg_left o₁ o Φ x).2 (hΦ x)

/-- **Diffeomorphism formula for `degreeAtRegularValue` on the left.** Postcomposing an arbitrary
map `f` with a `C^r` diffeomorphism `Ψ` (`r ≠ 0`) multiplies the degree by the orientation sign of
`Ψ`: the degree of `Ψ ∘ f` at `Ψ y` equals `orientationSign o' o₁' Ψ y` times the degree of `f` at
`y`. -/
theorem degreeAtRegularValue_diffeomorph_comp (Ψ : N ≃ₘ^r⟮J, J'⟯ N') (hr : r ≠ 0)
    (o : Manifold.Orientation I M ι) (o' : Manifold.Orientation J N ι)
    (o₁' : Manifold.Orientation J' N' ι) (f : M → N) (y : N) :
    degreeAtRegularValue o o₁' (Ψ ∘ f) (Ψ y) =
      orientationSign o' o₁' Ψ y * degreeAtRegularValue o o' f y := by
  rw [degreeAtRegularValue_def, degreeAtRegularValue_def, mul_finsum_mem]
  have hpre : (Ψ ∘ f) ⁻¹' {Ψ y} = f ⁻¹' {y} :=
    Set.ext fun x ↦ by simp [Function.comp_apply]
  refine finsum_mem_congr hpre fun x hx ↦ ?_
  have hfx : f x = y := hx
  rw [Ψ.orientationSign_diffeomorph_comp hr o o' o₁', hfx]

/-- **Diffeomorphism invariance of `degreeAtRegularValue` on the left.** When a `C^r`
diffeomorphism `Ψ` (`r ≠ 0`) preserves orientations at `y`, the degree of `Ψ ∘ f` at `Ψ y` equals
the degree of `f` at `y`. -/
theorem degreeAtRegularValue_diffeomorph_comp_of_isOrientationPreservingAt (Ψ : N ≃ₘ^r⟮J, J'⟯ N')
    (hr : r ≠ 0) (o : Manifold.Orientation I M ι) {o' : Manifold.Orientation J N ι}
    {o₁' : Manifold.Orientation J' N' ι} (f : M → N) {y : N}
    (hΨ : IsOrientationPreservingAt o' o₁' Ψ y) :
    degreeAtRegularValue o o₁' (Ψ ∘ f) (Ψ y) = degreeAtRegularValue o o' f y := by
  rw [Ψ.degreeAtRegularValue_diffeomorph_comp hr o o' o₁',
    orientationSign_of_isOrientationPreservingAt hΨ, one_mul]

/-- When a `C^r` diffeomorphism `Ψ` (`r ≠ 0`) reverses orientations at `y`, the degree of `Ψ ∘ f`
at `Ψ y` is minus the degree of `f` at `y`. -/
theorem degreeAtRegularValue_diffeomorph_comp_of_isOrientationReversingAt (Ψ : N ≃ₘ^r⟮J, J'⟯ N')
    (hr : r ≠ 0) (o : Manifold.Orientation I M ι) {o' : Manifold.Orientation J N ι}
    {o₁' : Manifold.Orientation J' N' ι} (f : M → N) {y : N}
    (hΨ : IsOrientationReversingAt o' o₁' Ψ y) :
    degreeAtRegularValue o o₁' (Ψ ∘ f) (Ψ y) = -degreeAtRegularValue o o' f y := by
  rw [Ψ.degreeAtRegularValue_diffeomorph_comp hr o o' o₁',
    orientationSign_of_isOrientationReversingAt hΨ, neg_one_mul]

end Diffeomorph
