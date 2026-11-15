/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Degree.Basic

/-!
# Invariance of regular values and mapping degree under diffeomorphisms

Composing a map `f : M → N` between manifolds on either side with a `C^r` diffeomorphism (`r ≠ 0`)
multiplies its manifold derivative by a continuous linear equivalence at every point, with no
differentiability hypothesis on `f` (`Diffeomorph.mfderiv_comp_right`,
`Diffeomorph.mfderiv_comp_left`): where `f` is not differentiable, neither is the composite, and
both derivatives vanish. Consequently, differentiability, invertibility of the manifold derivative,
regular points, and regular values are all preserved under pre- and post-composition with `C^r`
diffeomorphisms (`r ≠ 0`).

For oriented real `C¹` manifolds of the same finite dimension, the orientation sign of a map
composed with a diffeomorphism is unconditionally the product of the orientation signs
(`Diffeomorph.orientationSign_comp_right`, `Diffeomorph.orientationSign_comp_left`). Precomposing
with a diffeomorphism that preserves (reverses) orientations on the fibre over `y` leaves
`degreeAtRegularValue` unchanged (negates it), and precomposing with an everywhere
orientation-preserving (reversing) diffeomorphism leaves the global mapping degree `TauCeti.degree`
unchanged (negates it). Likewise, postcomposing with a target diffeomorphism that preserves
(reverses) orientations at `y` leaves the degree over `y` unchanged (negates it).

## Main results

* `Diffeomorph.mdifferentiableAt_comp_right_iff`, `Diffeomorph.mdifferentiableAt_comp_left_iff`,
  `Diffeomorph.mfderiv_comp_right`, `Diffeomorph.mfderiv_comp_left`: chain rules with a `C^r`
  diffeomorphism (`r ≠ 0`), requiring no differentiability hypothesis on `f`.
* `Diffeomorph.isRegularPoint_comp_right_iff`, `Diffeomorph.isRegularPoint_comp_left_iff`,
  `Diffeomorph.isRegularValue_comp_right_iff`, `Diffeomorph.isRegularValue_comp_left_iff`:
  diffeomorphism invariance of regular points and regular values.
* `Diffeomorph.orientationSign_comp_right`, `Diffeomorph.orientationSign_comp_left`:
  multiplicativity of the orientation sign under composition with a diffeomorphism.
* `Diffeomorph.degreeAtRegularValue_comp_right_of_isOrientationPreservingAt`,
  `Diffeomorph.degreeAtRegularValue_comp_right_of_isOrientationReversingAt`,
  `Diffeomorph.degree_comp_right_of_isOrientationPreservingAt`,
  `Diffeomorph.degree_comp_right_of_isOrientationReversingAt`: invariance of the degree under a
  diffeomorphism of the source.
* `Diffeomorph.degreeAtRegularValue_comp_left_of_isOrientationPreservingAt`,
  `Diffeomorph.degreeAtRegularValue_comp_left_of_isOrientationReversingAt`: invariance of the
  degree at a value under a diffeomorphism of the target.
-/

public section

noncomputable section

open Function Set TauCeti TauCeti.Manifold.Orientation
open scoped Manifold ContDiff

namespace Diffeomorph

section General

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E₁ H₁ M' : Type*} [NormedAddCommGroup E₁] [NormedSpace 𝕜 E₁]
  [TopologicalSpace H₁] {I' : ModelWithCorners 𝕜 E₁ H₁} [TopologicalSpace M'] [ChartedSpace H₁ M']
  {E H M : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} [TopologicalSpace M] [ChartedSpace H M]
  {E' H' N : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  [TopologicalSpace H'] {J : ModelWithCorners 𝕜 E' H'} [TopologicalSpace N] [ChartedSpace H' N]
  {E₂' H₂' N' : Type*} [NormedAddCommGroup E₂'] [NormedSpace 𝕜 E₂']
  [TopologicalSpace H₂'] {J' : ModelWithCorners 𝕜 E₂' H₂'} [TopologicalSpace N']
  [ChartedSpace H₂' N']
  {r : ℕ∞ω}

/-- Precomposing with a `C^r` diffeomorphism (`r ≠ 0`) preserves differentiability at a point. -/
theorem mdifferentiableAt_comp_right_iff (Φ : M' ≃ₘ^r⟮I', I⟯ M) (hr : r ≠ 0) {f : M → N}
    {x : M'} :
    MDifferentiableAt I' J (f ∘ Φ) x ↔ MDifferentiableAt I J f (Φ x) := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.comp x (Φ.contMDiff.mdifferentiableAt hr)⟩
  rw [← Φ.symm_apply_apply x] at h
  have hcomp := h.comp (Φ x) (Φ.symm.contMDiff.mdifferentiableAt hr)
  -- Cancelling `Φ ∘ Φ.symm` identifies `(f ∘ Φ) ∘ Φ.symm` with `f`.
  rwa [show (f ∘ Φ) ∘ Φ.symm = f from funext fun z ↦ by simp] at hcomp

/-- Postcomposing with a `C^r` diffeomorphism (`r ≠ 0`) preserves differentiability at a point. -/
theorem mdifferentiableAt_comp_left_iff (Ψ : N ≃ₘ^r⟮J, J'⟯ N') (hr : r ≠ 0) {f : M → N} {x : M} :
    MDifferentiableAt I J' (Ψ ∘ f) x ↔ MDifferentiableAt I J f x := by
  refine ⟨fun h ↦ ?_, fun h ↦ (Ψ.contMDiff.mdifferentiableAt hr).comp x h⟩
  have hcomp := (Ψ.symm.contMDiff.mdifferentiableAt hr).comp x h
  -- Cancelling `Ψ.symm ∘ Ψ` identifies `Ψ.symm ∘ (Ψ ∘ f)` with `f`.
  rwa [show Ψ.symm ∘ (Ψ ∘ f) = f from funext fun z ↦ by simp] at hcomp

/-- **Unconditional chain rule on the right for a diffeomorphism.** Precomposing an arbitrary map
`f` with a `C^r` diffeomorphism `Φ` (`r ≠ 0`) composes its manifold derivative with `mfderiv Φ`:
where `f` is not differentiable at `Φ x`, neither is `f ∘ Φ` at `x`, and both sides vanish. -/
theorem mfderiv_comp_right (Φ : M' ≃ₘ^r⟮I', I⟯ M) (hr : r ≠ 0) (f : M → N) (x : M') :
    mfderiv I' J (f ∘ Φ) x = (mfderiv I J f (Φ x)).comp (mfderiv I' I Φ x) := by
  by_cases hf : MDifferentiableAt I J f (Φ x)
  · exact mfderiv_comp x hf (Φ.contMDiff.mdifferentiableAt hr)
  · have hf' : ¬ MDifferentiableAt I' J (f ∘ Φ) x := mt (Φ.mdifferentiableAt_comp_right_iff hr).1 hf
    simp [mfderiv_zero_of_not_mdifferentiableAt hf, mfderiv_zero_of_not_mdifferentiableAt hf']

/-- **Unconditional chain rule on the left for a diffeomorphism.** Postcomposing an arbitrary map
`f` with a `C^r` diffeomorphism `Ψ` (`r ≠ 0`) composes its manifold derivative with `mfderiv Ψ`:
where `f` is not differentiable at `x`, neither is `Ψ ∘ f` at `x`, and both sides vanish. -/
theorem mfderiv_comp_left (Ψ : N ≃ₘ^r⟮J, J'⟯ N') (hr : r ≠ 0) (f : M → N) (x : M) :
    mfderiv I J' (Ψ ∘ f) x = (mfderiv J J' Ψ (f x)).comp (mfderiv I J f x) := by
  by_cases hf : MDifferentiableAt I J f x
  · exact mfderiv_comp x (Ψ.contMDiff.mdifferentiableAt hr) hf
  · have hf' : ¬ MDifferentiableAt I J' (Ψ ∘ f) x := mt (Ψ.mdifferentiableAt_comp_left_iff hr).1 hf
    simp [mfderiv_zero_of_not_mdifferentiableAt hf, mfderiv_zero_of_not_mdifferentiableAt hf']

/-- Precomposing with a `C^r` diffeomorphism (`r ≠ 0`) preserves invertibility of the manifold
derivative. -/
theorem isInvertible_mfderiv_comp_right_iff (Φ : M' ≃ₘ^r⟮I', I⟯ M) (hr : r ≠ 0) {f : M → N}
    {x : M'} :
    (mfderiv I' J (f ∘ Φ) x).IsInvertible ↔ (mfderiv I J f (Φ x)).IsInvertible := by
  set e := Φ.mfderivToContinuousLinearEquiv hr x
  refine ⟨?_, fun ⟨e', he'⟩ ↦ ⟨e.trans e', ?_⟩⟩
  · rintro ⟨e', he'⟩
    refine ⟨e.symm.trans e', ContinuousLinearMap.ext fun v ↦ ?_⟩
    have hv := congrArg (fun T ↦ T (e.symm v)) he'
    simpa [Φ.mfderiv_comp_right hr, ← Φ.mfderivToContinuousLinearEquiv_coe hr, e] using hv
  · ext v
    simp [Φ.mfderiv_comp_right hr, ← he', ← Φ.mfderivToContinuousLinearEquiv_coe hr, e]

/-- Postcomposing with a `C^r` diffeomorphism (`r ≠ 0`) preserves invertibility of the manifold
derivative. -/
theorem isInvertible_mfderiv_comp_left_iff (Ψ : N ≃ₘ^r⟮J, J'⟯ N') (hr : r ≠ 0) {f : M → N}
    {x : M} :
    (mfderiv I J' (Ψ ∘ f) x).IsInvertible ↔ (mfderiv I J f x).IsInvertible := by
  set e := Ψ.mfderivToContinuousLinearEquiv hr (f x)
  refine ⟨?_, fun ⟨e', he'⟩ ↦ ⟨e'.trans e, ?_⟩⟩
  · rintro ⟨e', he'⟩
    refine ⟨e'.trans e.symm, ContinuousLinearMap.ext fun v ↦ ?_⟩
    have hv := congrArg (fun T ↦ e.symm (T v)) he'
    simpa [Ψ.mfderiv_comp_left hr, ← Ψ.mfderivToContinuousLinearEquiv_coe hr, e] using hv
  · ext v
    simp [Ψ.mfderiv_comp_left hr, ← he', ← Ψ.mfderivToContinuousLinearEquiv_coe hr, e]

/-- Precomposing with a `C^r` diffeomorphism (`r ≠ 0`) preserves regular points. -/
theorem isRegularPoint_comp_right_iff (Φ : M' ≃ₘ^r⟮I', I⟯ M) (hr : r ≠ 0) {f : M → N} {x : M'} :
    IsRegularPoint I' J (f ∘ Φ) x ↔ IsRegularPoint I J f (Φ x) := by
  rw [isRegularPoint_iff, isRegularPoint_iff, Φ.mfderiv_comp_right hr,
    ContinuousLinearMap.coe_comp, ← Φ.mfderivToContinuousLinearEquiv_coe hr]
  exact EquivLike.surjective_comp (Φ.mfderivToContinuousLinearEquiv hr x) _

/-- Postcomposing with a `C^r` diffeomorphism (`r ≠ 0`) preserves regular points. -/
theorem isRegularPoint_comp_left_iff (Ψ : N ≃ₘ^r⟮J, J'⟯ N') (hr : r ≠ 0) {f : M → N} {x : M} :
    IsRegularPoint I J' (Ψ ∘ f) x ↔ IsRegularPoint I J f x := by
  rw [isRegularPoint_iff, isRegularPoint_iff, Ψ.mfderiv_comp_left hr,
    ContinuousLinearMap.coe_comp, ← Ψ.mfderivToContinuousLinearEquiv_coe hr]
  exact EquivLike.comp_surjective _ (Ψ.mfderivToContinuousLinearEquiv hr (f x))

/-- Precomposing with a `C^r` diffeomorphism (`r ≠ 0`) leaves regular values unchanged. -/
theorem isRegularValue_comp_right_iff (Φ : M' ≃ₘ^r⟮I', I⟯ M) (hr : r ≠ 0) {f : M → N} {y : N} :
    IsRegularValue I' J (f ∘ Φ) y ↔ IsRegularValue I J f y := by
  rw [isRegularValue_iff, isRegularValue_iff]
  refine ⟨fun h x hx ↦ ?_, fun h x hx ↦ (Φ.isRegularPoint_comp_right_iff hr).2 (h (Φ x) hx)⟩
  simpa only [Φ.isRegularPoint_comp_right_iff hr, Φ.apply_symm_apply] using
    h (Φ.symm x) (by simpa [Function.comp_apply] using hx)

/-- Postcomposing with a `C^r` diffeomorphism `Ψ` (`r ≠ 0`) transports regular values along `Ψ`. -/
theorem isRegularValue_comp_left_iff (Ψ : N ≃ₘ^r⟮J, J'⟯ N') (hr : r ≠ 0) {f : M → N} {y : N} :
    IsRegularValue I J' (Ψ ∘ f) (Ψ y) ↔ IsRegularValue I J f y := by
  simp [isRegularValue_iff, Ψ.isRegularPoint_comp_left_iff hr]

end General

section Degree

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

/-- Precomposing an arbitrary map `f` with a `C^r` diffeomorphism `Φ` (`r ≠ 0`) multiplies its
orientation sign by that of `Φ`, with no differentiability hypothesis on `f`. -/
theorem orientationSign_comp_right (Φ : M' ≃ₘ^r⟮I', I⟯ M) (hr : r ≠ 0)
    (o₁ : Manifold.Orientation I' M' ι) (o : Manifold.Orientation I M ι)
    (o' : Manifold.Orientation J N ι) (f : M → N) (x : M') :
    orientationSign o₁ o' (f ∘ Φ) x =
      orientationSign o o' f (Φ x) * orientationSign o₁ o Φ x := by
  by_cases hinv : (mfderiv I J f (Φ x)).IsInvertible
  · exact orientationSign_comp (mdifferentiableAt_of_isInvertible_mfderiv hinv)
      (Φ.contMDiff.mdifferentiableAt hr)
  · have hinv' : ¬ (mfderiv I' J (f ∘ Φ) x).IsInvertible :=
      mt (Φ.isInvertible_mfderiv_comp_right_iff hr).1 hinv
    rw [orientationSign_of_not_isInvertible hinv', orientationSign_of_not_isInvertible hinv,
      zero_mul]

/-- Postcomposing an arbitrary map `f` with a `C^r` diffeomorphism `Ψ` (`r ≠ 0`) multiplies its
orientation sign by that of `Ψ`, with no differentiability hypothesis on `f`. -/
theorem orientationSign_comp_left (Ψ : N ≃ₘ^r⟮J, J'⟯ N') (hr : r ≠ 0)
    (o : Manifold.Orientation I M ι) (o' : Manifold.Orientation J N ι)
    (o₁' : Manifold.Orientation J' N' ι) (f : M → N) (x : M) :
    orientationSign o o₁' (Ψ ∘ f) x =
      orientationSign o' o₁' Ψ (f x) * orientationSign o o' f x := by
  by_cases hinv : (mfderiv I J f x).IsInvertible
  · exact orientationSign_comp (Ψ.contMDiff.mdifferentiableAt hr)
      (mdifferentiableAt_of_isInvertible_mfderiv hinv)
  · have hinv' : ¬ (mfderiv I J' (Ψ ∘ f) x).IsInvertible :=
      mt (Ψ.isInvertible_mfderiv_comp_left_iff hr).1 hinv
    rw [orientationSign_of_not_isInvertible hinv', orientationSign_of_not_isInvertible hinv,
      mul_zero]

/-- **Diffeomorphism invariance of `degreeAtRegularValue` on the right.** If a `C^r` diffeomorphism
`Φ` (`r ≠ 0`) preserves orientations at every preimage of `y`, then `f ∘ Φ` and `f` have the same
degree at `y`. -/
theorem degreeAtRegularValue_comp_right_of_isOrientationPreservingAt (Φ : M' ≃ₘ^r⟮I', I⟯ M)
    (hr : r ≠ 0) {o₁ : Manifold.Orientation I' M' ι} {o : Manifold.Orientation I M ι}
    (o' : Manifold.Orientation J N ι) {f : M → N} {y : N}
    (hΦ : ∀ x, f (Φ x) = y → IsOrientationPreservingAt o₁ o Φ x) :
    degreeAtRegularValue o₁ o' (f ∘ Φ) y = degreeAtRegularValue o o' f y := by
  rw [degreeAtRegularValue_def, degreeAtRegularValue_def]
  refine finsum_mem_eq_of_bijOn Φ ⟨fun x hx ↦ hx, Φ.injective.injOn, fun z hz ↦
    ⟨Φ.symm z, by simpa [Function.comp_apply] using hz, Φ.apply_symm_apply z⟩⟩ fun x hx ↦ ?_
  rw [Φ.orientationSign_comp_right hr o₁ o o',
    orientationSign_of_isOrientationPreservingAt (hΦ x hx), mul_one]

/-- If a `C^r` diffeomorphism `Φ` (`r ≠ 0`) reverses orientations at every preimage of `y`, then
precomposing with `Φ` negates `degreeAtRegularValue` at `y`. -/
theorem degreeAtRegularValue_comp_right_of_isOrientationReversingAt (Φ : M' ≃ₘ^r⟮I', I⟯ M)
    (hr : r ≠ 0) {o₁ : Manifold.Orientation I' M' ι} {o : Manifold.Orientation I M ι}
    (o' : Manifold.Orientation J N ι) {f : M → N} {y : N}
    (hΦ : ∀ x, f (Φ x) = y → IsOrientationReversingAt o₁ o Φ x) :
    degreeAtRegularValue o₁ o' (f ∘ Φ) y = -degreeAtRegularValue o o' f y := by
  rw [← neg_inj, ← degreeAtRegularValue_neg_left, neg_neg]
  exact Φ.degreeAtRegularValue_comp_right_of_isOrientationPreservingAt hr o' fun x hx ↦
    (isOrientationPreservingAt_neg_left o₁ o Φ x).2 (hΦ x hx)

/-- **Diffeomorphism invariance of `degree` on the right.** Precomposing with an everywhere
orientation-preserving `C^r` diffeomorphism (`r ≠ 0`) leaves `TauCeti.degree` unchanged. -/
theorem degree_comp_right_of_isOrientationPreservingAt (Φ : M' ≃ₘ^r⟮I', I⟯ M) (hr : r ≠ 0)
    {o₁ : Manifold.Orientation I' M' ι} {o : Manifold.Orientation I M ι}
    (o' : Manifold.Orientation J N ι) (f : M → N)
    (hΦ : ∀ x, IsOrientationPreservingAt o₁ o Φ x) :
    degree o₁ o' (f ∘ Φ) = degree o o' f := by
  have hpred : (fun y ↦ IsRegularValue I' J (f ∘ Φ) y) = fun y ↦ IsRegularValue I J f y :=
    funext fun y ↦ propext (Φ.isRegularValue_comp_right_iff hr)
  by_cases h : ∃ y, IsRegularValue I J f y
  · have h' : ∃ y, IsRegularValue I' J (f ∘ Φ) y := by rwa [hpred]
    have hchoose : h'.choose = h.choose := by congr! 1
    rw [degree_eq_degreeAtRegularValue_choose h', degree_eq_degreeAtRegularValue_choose h, hchoose]
    exact Φ.degreeAtRegularValue_comp_right_of_isOrientationPreservingAt hr o' fun x _ ↦ hΦ x
  · have h' : ¬∃ y, IsRegularValue I' J (f ∘ Φ) y := by rwa [hpred]
    rw [degree_eq_zero_of_not_exists h', degree_eq_zero_of_not_exists h]

/-- Precomposing with an everywhere orientation-reversing `C^r` diffeomorphism (`r ≠ 0`) negates
`TauCeti.degree`. -/
theorem degree_comp_right_of_isOrientationReversingAt (Φ : M' ≃ₘ^r⟮I', I⟯ M) (hr : r ≠ 0)
    {o₁ : Manifold.Orientation I' M' ι} {o : Manifold.Orientation I M ι}
    (o' : Manifold.Orientation J N ι) (f : M → N)
    (hΦ : ∀ x, IsOrientationReversingAt o₁ o Φ x) :
    degree o₁ o' (f ∘ Φ) = -degree o o' f := by
  rw [← neg_inj, ← degree_neg_left, neg_neg]
  exact Φ.degree_comp_right_of_isOrientationPreservingAt hr o' f fun x ↦
    (isOrientationPreservingAt_neg_left o₁ o Φ x).2 (hΦ x)

/-- **Diffeomorphism invariance of `degreeAtRegularValue` on the left.** Postcomposing with a `C^r`
diffeomorphism `Ψ` (`r ≠ 0`) that preserves orientations at `y` leaves the degree over `y`
unchanged. -/
theorem degreeAtRegularValue_comp_left_of_isOrientationPreservingAt (Ψ : N ≃ₘ^r⟮J, J'⟯ N')
    (hr : r ≠ 0) (o : Manifold.Orientation I M ι) {o' : Manifold.Orientation J N ι}
    {o₁' : Manifold.Orientation J' N' ι} (f : M → N) {y : N}
    (hΨ : IsOrientationPreservingAt o' o₁' Ψ y) :
    degreeAtRegularValue o o₁' (Ψ ∘ f) (Ψ y) = degreeAtRegularValue o o' f y := by
  rw [degreeAtRegularValue_def, degreeAtRegularValue_def]
  have hpre : (Ψ ∘ f) ⁻¹' {Ψ y} = f ⁻¹' {y} :=
    Set.ext fun x ↦ by simp [Function.comp_apply]
  refine finsum_mem_congr hpre fun x hx ↦ ?_
  have hfx : f x = y := hx
  rw [Ψ.orientationSign_comp_left hr o o' o₁', hfx,
    orientationSign_of_isOrientationPreservingAt hΨ, one_mul]

/-- Postcomposing with a `C^r` diffeomorphism `Ψ` (`r ≠ 0`) that reverses orientations at `y`
negates the degree over `y`. -/
theorem degreeAtRegularValue_comp_left_of_isOrientationReversingAt (Ψ : N ≃ₘ^r⟮J, J'⟯ N')
    (hr : r ≠ 0) (o : Manifold.Orientation I M ι) {o' : Manifold.Orientation J N ι}
    {o₁' : Manifold.Orientation J' N' ι} (f : M → N) {y : N}
    (hΨ : IsOrientationReversingAt o' o₁' Ψ y) :
    degreeAtRegularValue o o₁' (Ψ ∘ f) (Ψ y) = -degreeAtRegularValue o o' f y := by
  rw [← neg_inj, ← degreeAtRegularValue_neg_right, neg_neg]
  exact Ψ.degreeAtRegularValue_comp_left_of_isOrientationPreservingAt hr o f
    ((isOrientationPreservingAt_neg_right o' o₁' Ψ y).2 hΨ)

end Degree

end Diffeomorph
