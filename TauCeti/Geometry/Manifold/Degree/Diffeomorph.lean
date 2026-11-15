/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Degree.Basic
public import TauCeti.Geometry.Manifold.Diffeomorph.Basic

/-!
# Regular values, orientation signs, and degrees under diffeomorphisms

Precomposing or postcomposing an arbitrary map `f` between manifolds with a `C^n` diffeomorphism
(`n ≠ 0`) transports regular points, regular values, orientation signs, and regular-value degrees
without any differentiability assumption on `f`: where `f` fails to be differentiable, so does the
composite (`Diffeomorph.mdifferentiableAt_comp_iff`,
`Diffeomorph.mdifferentiableAt_comp_diffeomorph_iff`), and both manifold derivatives vanish.

These invariance properties allow smooth-degree computations to rechart either manifold along a
diffeomorphism, such as `TauCeti.BoundarylessModel.diffeomorph` or
`ContinuousLinearEquiv.toTransContinuousLinearEquiv`, without changing the signed preimage count.

## Main results

* `Diffeomorph.isRegularPoint`, `Diffeomorph.isRegularValue`: every point and value of a `C^n`
  diffeomorphism (`n ≠ 0`) is regular.
* `Diffeomorph.isRegularPoint_diffeomorph_comp`, `Diffeomorph.isRegularPoint_comp_diffeomorph`,
  `Diffeomorph.isRegularValue_diffeomorph_comp_apply`,
  `Diffeomorph.isRegularValue_comp_diffeomorph`: invariance of regular points and regular values
  under postcomposition and precomposition with a diffeomorphism.
* `TauCeti.Manifold.Orientation.orientationSign_diffeomorph_comp`,
  `TauCeti.Manifold.Orientation.orientationSign_comp_diffeomorph`: multiplicativity of the
  orientation sign under composition with a diffeomorphism, with no differentiability hypothesis on
  the other factor.
* `TauCeti.degreeAtRegularValue_diffeomorph_comp_apply`,
  `TauCeti.degreeAtRegularValue_diffeomorph_comp_of_isOrientationPreservingAt`,
  `TauCeti.degreeAtRegularValue_comp_diffeomorph_of_isOrientationPreservingAt`: transformation of
  the signed preimage count under diffeomorphisms of the source and target.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Chapter 17, section Degree Theory.
* J. W. Milnor, *Topology from the Differentiable Viewpoint*, University Press of Virginia, 1965,
  §5.
-/

public section

noncomputable section

open Function Set
open scoped ContDiff Manifold

section Regularity

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners 𝕜 F H'}
  {H'' : Type*} [TopologicalSpace H''] {K : ModelWithCorners 𝕜 G H''}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  {P : Type*} [TopologicalSpace P] [ChartedSpace H'' P]
  {n : ℕ∞ω}

namespace Diffeomorph

/-- Every point is a regular point of a `C^n` diffeomorphism (`n ≠ 0`). -/
theorem isRegularPoint (h : M ≃ₘ^n⟮I, J⟯ N) (hn : n ≠ 0) (x : M) :
    TauCeti.IsRegularPoint I J h x :=
  TauCeti.isRegularPoint_iff.2 (h.isInvertible_mfderiv hn).surjective

/-- Every value is a regular value of a `C^n` diffeomorphism (`n ≠ 0`). -/
theorem isRegularValue (h : M ≃ₘ^n⟮I, J⟯ N) (hn : n ≠ 0) (y : N) :
    TauCeti.IsRegularValue I J h y :=
  TauCeti.isRegularValue_iff.2 fun x _ ↦ h.isRegularPoint hn x

/-- Postcomposing with a `C^n` diffeomorphism (`n ≠ 0`) preserves invertibility of the manifold
derivative, with no differentiability assumption on `f`. -/
@[simp]
theorem isInvertible_mfderiv_diffeomorph_comp (h : M ≃ₘ^n⟮I, J⟯ N) (hn : n ≠ 0)
    (f : P → M) (x : P) :
    (mfderiv K J (h ∘ f) x).IsInvertible ↔ (mfderiv K I f x).IsInvertible := by
  refine ⟨fun hinv ↦ ?_, fun hinv ↦ ?_⟩
  · have h' : (mfderiv K I (h.symm ∘ (h ∘ f)) x).IsInvertible := by
      rw [h.symm.mfderiv_diffeomorph_comp hn]
      exact (h.symm.isInvertible_mfderiv hn).comp hinv
    have heq : (h.symm : N → M) ∘ ((h : M → N) ∘ f) = f := funext fun z ↦ h.symm_apply_apply (f z)
    rwa [heq] at h'
  · rw [h.mfderiv_diffeomorph_comp hn]
    exact (h.isInvertible_mfderiv hn).comp hinv

/-- Precomposing with a `C^n` diffeomorphism (`n ≠ 0`) preserves invertibility of the manifold
derivative at the corresponding point, with no differentiability assumption on `f`. -/
@[simp]
theorem isInvertible_mfderiv_comp_diffeomorph (h : M ≃ₘ^n⟮I, J⟯ N) (hn : n ≠ 0)
    (f : N → P) (x : M) :
    (mfderiv I K (f ∘ h) x).IsInvertible ↔ (mfderiv J K f (h x)).IsInvertible := by
  refine ⟨fun hinv ↦ ?_, fun hinv ↦ ?_⟩
  · have hinv' : (mfderiv I K (f ∘ h) (h.symm (h x))).IsInvertible := by
      rwa [h.symm_apply_apply]
    have h' : (mfderiv J K ((f ∘ h) ∘ h.symm) (h x)).IsInvertible := by
      rw [h.symm.mfderiv_comp_diffeomorph hn]
      exact hinv'.comp (h.symm.isInvertible_mfderiv hn)
    have heq : (f ∘ (h : M → N)) ∘ h.symm = f := funext fun y ↦ congrArg f (h.apply_symm_apply y)
    rwa [heq] at h'
  · rw [h.mfderiv_comp_diffeomorph hn]
    exact hinv.comp (h.isInvertible_mfderiv hn)

/-- Postcomposing with a `C^n` diffeomorphism (`n ≠ 0`) preserves regular points, with no
differentiability assumption on `f`. -/
@[simp]
theorem isRegularPoint_diffeomorph_comp (h : M ≃ₘ^n⟮I, J⟯ N) (hn : n ≠ 0) (f : P → M) (x : P) :
    TauCeti.IsRegularPoint K J (h ∘ f) x ↔ TauCeti.IsRegularPoint K I f x := by
  rw [TauCeti.isRegularPoint_iff, TauCeti.isRegularPoint_iff, h.mfderiv_diffeomorph_comp hn,
    ← h.mfderivToContinuousLinearEquiv_coe hn, ContinuousLinearMap.coe_comp,
    ContinuousLinearEquiv.coe_coe]
  exact EquivLike.comp_surjective _ (h.mfderivToContinuousLinearEquiv hn (f x))

/-- Precomposing with a `C^n` diffeomorphism (`n ≠ 0`) preserves regular points at the
corresponding point, with no differentiability assumption on `f`. -/
@[simp]
theorem isRegularPoint_comp_diffeomorph (h : M ≃ₘ^n⟮I, J⟯ N) (hn : n ≠ 0) (f : N → P) (x : M) :
    TauCeti.IsRegularPoint I K (f ∘ h) x ↔ TauCeti.IsRegularPoint J K f (h x) := by
  rw [TauCeti.isRegularPoint_iff, TauCeti.isRegularPoint_iff, h.mfderiv_comp_diffeomorph hn,
    ← h.mfderivToContinuousLinearEquiv_coe hn, ContinuousLinearMap.coe_comp,
    ContinuousLinearEquiv.coe_coe]
  exact EquivLike.surjective_comp (h.mfderivToContinuousLinearEquiv hn x) _

/-- Under postcomposition with a `C^n` diffeomorphism `h` (`n ≠ 0`), `h y` is a regular value of
`h ∘ f` if and only if `y` is a regular value of `f`. -/
@[simp]
theorem isRegularValue_diffeomorph_comp_apply (h : M ≃ₘ^n⟮I, J⟯ N) (hn : n ≠ 0)
    (f : P → M) (y : M) :
    TauCeti.IsRegularValue K J (h ∘ f) (h y) ↔ TauCeti.IsRegularValue K I f y := by
  simp only [TauCeti.isRegularValue_iff, Function.comp_apply, EquivLike.apply_eq_iff_eq h,
    h.isRegularPoint_diffeomorph_comp hn]

/-- A point `z` of the target is a regular value of `h ∘ f`, for a `C^n` diffeomorphism `h`
(`n ≠ 0`), if and only if `h.symm z` is a regular value of `f`. -/
theorem isRegularValue_diffeomorph_comp (h : M ≃ₘ^n⟮I, J⟯ N) (hn : n ≠ 0) (f : P → M) (z : N) :
    TauCeti.IsRegularValue K J (h ∘ f) z ↔ TauCeti.IsRegularValue K I f (h.symm z) := by
  conv_lhs => rw [← h.apply_symm_apply z]
  exact h.isRegularValue_diffeomorph_comp_apply hn f (h.symm z)

/-- Precomposing with a `C^n` diffeomorphism (`n ≠ 0`) does not change regular values. -/
@[simp]
theorem isRegularValue_comp_diffeomorph (h : M ≃ₘ^n⟮I, J⟯ N) (hn : n ≠ 0) (f : N → P) (y : P) :
    TauCeti.IsRegularValue I K (f ∘ h) y ↔ TauCeti.IsRegularValue J K f y := by
  rw [TauCeti.isRegularValue_iff, TauCeti.isRegularValue_iff]
  refine ⟨fun hy z hz ↦ ?_, fun hy x hx ↦ (h.isRegularPoint_comp_diffeomorph hn f x).2 (hy _ hx)⟩
  rw [← h.apply_symm_apply z] at hz ⊢
  exact (h.isRegularPoint_comp_diffeomorph hn f (h.symm z)).1 (hy (h.symm z) hz)

end Diffeomorph

end Regularity

namespace TauCeti

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

namespace Manifold.Orientation

/-- **Orientation sign under postcomposition with a diffeomorphism.** For a `C^n` diffeomorphism
`h : N ≃ₘ^n⟮J, K⟯ P` (`n ≠ 0`) and an arbitrary map `f : M → N`, the orientation sign of `h ∘ f` at
`x` is the product of the orientation signs, with no differentiability hypothesis on `f`. -/
theorem orientationSign_diffeomorph_comp (h : N ≃ₘ^n⟮J, K⟯ P) (hn : n ≠ 0)
    (o : Manifold.Orientation I M ι) (o' : Manifold.Orientation J N ι)
    (o'' : Manifold.Orientation K P ι) (f : M → N) (x : M) :
    orientationSign o o'' (h ∘ f) x =
      orientationSign o' o'' h (f x) * orientationSign o o' f x := by
  by_cases hinv : (mfderiv I J f x).IsInvertible
  · exact orientationSign_comp (h.mdifferentiable hn (f x))
      (mdifferentiableAt_of_isInvertible_mfderiv hinv)
  · rw [orientationSign_of_not_isInvertible
        ((h.isInvertible_mfderiv_diffeomorph_comp hn f x).not.mpr hinv),
      orientationSign_of_not_isInvertible hinv, mul_zero]

/-- **Orientation sign under precomposition with a diffeomorphism.** For a `C^n` diffeomorphism
`h : P ≃ₘ^n⟮K, I⟯ M` (`n ≠ 0`) and an arbitrary map `f : M → N`, the orientation sign of `f ∘ h` at
`x` is the product of the orientation signs, with no differentiability hypothesis on `f`. -/
theorem orientationSign_comp_diffeomorph (h : P ≃ₘ^n⟮K, I⟯ M) (hn : n ≠ 0)
    (o : Manifold.Orientation I M ι) (o' : Manifold.Orientation J N ι)
    (o'' : Manifold.Orientation K P ι) (f : M → N) (x : P) :
    orientationSign o'' o' (f ∘ h) x =
      orientationSign o o' f (h x) * orientationSign o'' o h x := by
  by_cases hinv : (mfderiv I J f (h x)).IsInvertible
  · exact orientationSign_comp (mdifferentiableAt_of_isInvertible_mfderiv hinv)
      (h.mdifferentiable hn x)
  · rw [orientationSign_of_not_isInvertible
        ((h.isInvertible_mfderiv_comp_diffeomorph hn f x).not.mpr hinv),
      orientationSign_of_not_isInvertible hinv, zero_mul]

end Manifold.Orientation

open Manifold.Orientation

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
  rw [orientationSign_diffeomorph_comp h hn o o' o'' f x, mem_preimage.1 hx]

/-- `TauCeti.degreeAtRegularValue_diffeomorph_comp_apply` stated at a point `z` of the target. -/
theorem degreeAtRegularValue_diffeomorph_comp (h : N ≃ₘ^n⟮J, K⟯ P) (hn : n ≠ 0)
    (o : Manifold.Orientation I M ι) (o' : Manifold.Orientation J N ι)
    (o'' : Manifold.Orientation K P ι) (f : M → N) (z : P) :
    degreeAtRegularValue o o'' (h ∘ f) z =
      orientationSign o' o'' h (h.symm z) * degreeAtRegularValue o o' f (h.symm z) := by
  conv_lhs => rw [← h.apply_symm_apply z]
  exact degreeAtRegularValue_diffeomorph_comp_apply h hn o o' o'' f (h.symm z)

/-- Postcomposing `f` with a `C^n` diffeomorphism `h` (`n ≠ 0`) that preserves orientations at `y`
leaves the signed preimage count over `y` unchanged. -/
theorem degreeAtRegularValue_diffeomorph_comp_of_isOrientationPreservingAt
    (h : N ≃ₘ^n⟮J, K⟯ P) (hn : n ≠ 0) {o : Manifold.Orientation I M ι}
    {o' : Manifold.Orientation J N ι} {o'' : Manifold.Orientation K P ι} (f : M → N) {y : N}
    (hh : IsOrientationPreservingAt o' o'' h y) :
    degreeAtRegularValue o o'' (h ∘ f) (h y) = degreeAtRegularValue o o' f y := by
  rw [degreeAtRegularValue_diffeomorph_comp_apply h hn o o' o'' f y,
    orientationSign_of_isOrientationPreservingAt hh, one_mul]

/-- Postcomposing `f` with a `C^n` diffeomorphism `h` (`n ≠ 0`) that reverses orientations at `y`
negates the signed preimage count over `y`. -/
theorem degreeAtRegularValue_diffeomorph_comp_of_isOrientationReversingAt
    (h : N ≃ₘ^n⟮J, K⟯ P) (hn : n ≠ 0) {o : Manifold.Orientation I M ι}
    {o' : Manifold.Orientation J N ι} {o'' : Manifold.Orientation K P ι} (f : M → N) {y : N}
    (hh : IsOrientationReversingAt o' o'' h y) :
    degreeAtRegularValue o o'' (h ∘ f) (h y) = -degreeAtRegularValue o o' f y := by
  rw [degreeAtRegularValue_diffeomorph_comp_apply h hn o o' o'' f y,
    orientationSign_of_isOrientationReversingAt hh, neg_one_mul]

/-- Precomposing `f` with a `C^n` diffeomorphism `h` (`n ≠ 0`) that preserves orientations along
the fibre over `y` leaves the signed preimage count over `y` unchanged. -/
theorem degreeAtRegularValue_comp_diffeomorph_of_isOrientationPreservingAt
    (h : P ≃ₘ^n⟮K, I⟯ M) (hn : n ≠ 0) {o : Manifold.Orientation I M ι}
    {o' : Manifold.Orientation J N ι} {o'' : Manifold.Orientation K P ι} (f : M → N) {y : N}
    (hh : ∀ x, f (h x) = y → IsOrientationPreservingAt o'' o h x) :
    degreeAtRegularValue o'' o' (f ∘ h) y = degreeAtRegularValue o o' f y := by
  classical
  have hcongr : ∑ᶠ x ∈ (f ∘ h) ⁻¹' {y}, orientationSign o'' o' (f ∘ h) x =
      ∑ᶠ x ∈ (f ∘ h) ⁻¹' {y}, orientationSign o o' f (h x) :=
    finsum_mem_congr rfl fun x hx ↦ by
      rw [orientationSign_comp_diffeomorph h hn o o' o'' f x,
        orientationSign_of_isOrientationPreservingAt (hh x hx), mul_one]
  rw [degreeAtRegularValue_def, hcongr, degreeAtRegularValue_def, finsum_mem_def, finsum_mem_def]
  exact finsum_comp_equiv h.toEquiv (f := fun z ↦ if z ∈ f ⁻¹' {y} then orientationSign o o' f z
    else 0)

/-- Precomposing `f` with a `C^n` diffeomorphism `h` (`n ≠ 0`) that reverses orientations along
the fibre over `y` negates the signed preimage count over `y`. -/
theorem degreeAtRegularValue_comp_diffeomorph_of_isOrientationReversingAt
    (h : P ≃ₘ^n⟮K, I⟯ M) (hn : n ≠ 0) {o : Manifold.Orientation I M ι}
    {o' : Manifold.Orientation J N ι} {o'' : Manifold.Orientation K P ι} (f : M → N) {y : N}
    (hh : ∀ x, f (h x) = y → IsOrientationReversingAt o'' o h x) :
    degreeAtRegularValue o'' o' (f ∘ h) y = -degreeAtRegularValue o o' f y := by
  rw [← neg_eq_iff_eq_neg, ← degreeAtRegularValue_neg_left]
  exact degreeAtRegularValue_comp_diffeomorph_of_isOrientationPreservingAt h hn f
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
      ⟨hex.choose, (h.isRegularValue_comp_diffeomorph hn f hex.choose).2 hex.choose_spec⟩
    have hchoose : hex'.choose = hex.choose := by
      have hpred : (fun y ↦ IsRegularValue K J (f ∘ h) y) = fun y ↦ IsRegularValue I J f y :=
        funext fun y ↦ propext (h.isRegularValue_comp_diffeomorph hn f y)
      -- `hex'.choose` and `hex.choose` apply `Exists.choose` to equal predicates.
      congr 1
    rw [degree_eq_degreeAtRegularValue_choose hex', degree_eq_degreeAtRegularValue_choose hex,
      hchoose]
    exact degreeAtRegularValue_comp_diffeomorph_of_isOrientationPreservingAt h hn f
      fun x _ ↦ hh x
  · have hex' : ¬∃ y, IsRegularValue K J (f ∘ h) y := fun ⟨y, hy⟩ ↦
      hex ⟨y, (h.isRegularValue_comp_diffeomorph hn f y).1 hy⟩
    rw [degree_of_not_exists hex', degree_of_not_exists hex]

/-- Precomposing `f` with an everywhere orientation-reversing `C^n` diffeomorphism `h` (`n ≠ 0`)
negates `TauCeti.degree`. -/
theorem degree_comp_diffeomorph_of_isOrientationReversingAt
    (h : P ≃ₘ^n⟮K, I⟯ M) (hn : n ≠ 0) {o : Manifold.Orientation I M ι}
    {o' : Manifold.Orientation J N ι} {o'' : Manifold.Orientation K P ι} (f : M → N)
    (hh : ∀ x, IsOrientationReversingAt o'' o h x) :
    degree o'' o' (f ∘ h) = -degree o o' f := by
  rw [← neg_eq_iff_eq_neg, ← degree_neg_left]
  exact degree_comp_diffeomorph_of_isOrientationPreservingAt h hn f
    fun x ↦ (isOrientationPreservingAt_neg_left o'' o h x).2 (hh x)

end TauCeti
