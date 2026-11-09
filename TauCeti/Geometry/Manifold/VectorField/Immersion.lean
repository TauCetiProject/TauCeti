/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Immersion
public import TauCeti.Geometry.Manifold.VectorField.Related
import TauCeti.Geometry.Manifold.ContMDiff.LeftInverse

/-!
# Restricting tangent vector fields along immersions

An ambient vector field tangent to an immersion has a unique vector field on its domain that
is related to it. This field is smooth: smoothness can be detected after applying the
differential of the immersion, since in tangent coordinates that differential is a smoothly
varying split injection. No continuity of the lifted field needs to be assumed.

The restriction commutes with Lie brackets. In particular, the bracket of two ambient fields
tangent to the immersion is again tangent to it. These statements apply to immersions with
self-intersections, and require neither manifold to be Hausdorff. For finite regularity, a
`C^n` immersion restricts `C^m` fields when `m + 1 ≤ n`.

The local field-lifting and bracket-tangency theorems apply to any map whose differential at
the base point has a continuous linear left inverse. They require local tangency and the
indicated regularity at that point.

## Main results

* `ContMDiffAt.vectorField_of_mfderiv`: regularity of a field can be tested after a
  split-injective differential.
* `ContMDiffAt.exists_vectorField_mfderiv_eventuallyEq`: a local related field from local
  tangency and a split differential at the point.
* `ContMDiff.existsUnique_vectorField_mfderiv_eq`: construction and uniqueness of the
  related field from tangency.
* `ContMDiffAt.mlieBracket_mem_range_mfderiv`: local tangency and pointwise regularity suffice
  for bracket tangency at the image point.
* `Manifold.IsImmersion.mlieBracket_mem_range_mfderiv`: tangent ambient fields are closed
  under the Lie bracket.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, second edition, Springer GTM 218 (2013),
  Chapter 8 (restriction of tangent vector fields and naturality of the Lie bracket).
-/

public section

open Bundle ContinuousLinearMap Manifold VectorField Filter
open scoped ContDiff Manifold Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners 𝕜 F G}
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  [IsManifold I 1 M] [IsManifold J 1 N]
  {n m : ℕ∞ω}
  {f : M → N} {X : Π x : M, TangentSpace I x} {x₀ : M}

/-- A vector field is `C^m` if its image under the differential of a `C^n` map is `C^m`,
provided `m + 1 ≤ n` and the differential at the point has a continuous linear left inverse. -/
theorem ContMDiffAt.vectorField_of_mfderiv
    (hf : ContMDiffAt I J n f x₀) (hmn : m + 1 ≤ n)
    (hinj : (mfderiv I J f x₀).HasLeftInverse)
    (hX : ContMDiffAt I J.tangent m
      (fun x ↦ (⟨f x, mfderiv I J f x (X x)⟩ : TangentBundle J N)) x₀) :
    ContMDiffAt I I.tangent m (T% X) x₀ := by
  -- In tangent-bundle charts, the differential is a smooth family of split injections.
  have hA := hf.mfderiv_const hmn
  have hx := FiberBundle.mem_baseSet_trivializationAt' (F := E) (E := TangentSpace I) x₀
  have hy := FiberBundle.mem_baseSet_trivializationAt' (F := F) (E := TangentSpace J) (f x₀)
  have hleft : (inTangentCoordinates I J id f (mfderiv I J f) x₀ x₀).HasLeftInverse := by
    rw [inTangentCoordinates, id_eq, inCoordinates_eq hx hy]
    exact ((trivializationAt F (TangentSpace J) (f x₀)).continuousLinearEquivAt 𝕜
      (f x₀) hy).hasLeftInverse.comp
      (hinj.comp ((trivializationAt E (TangentSpace I) x₀).continuousLinearEquivAt 𝕜
        x₀ hx).symm.hasLeftInverse)
  rw [Bundle.contMDiffAt_section]
  apply ContMDiffAt.of_clm_apply (A := inTangentCoordinates I J id f (mfderiv I J f) x₀)
    (hA := hA) (h := hleft)
  refine (Bundle.contMDiffAt_totalSpace.mp hX).2.congr_of_eventuallyEq ?_
  have hsrc := (trivializationAt E (TangentSpace I) x₀).open_baseSet.mem_nhds hx
  have htgt := hf.continuousAt.preimage_mem_nhds
    ((trivializationAt F (TangentSpace J) (f x₀)).open_baseSet.mem_nhds hy)
  -- Applying the coordinate differential to the source coordinates gives the target coordinates.
  filter_upwards [hsrc, htgt] with x hx' hy'
  rw [inTangentCoordinates, id_eq, id_eq, inCoordinates_eq hx' hy']
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    Trivialization.coe_continuousLinearEquivAt_eq,
    Trivialization.symm_continuousLinearEquivAt_eq,
    Trivialization.symmL_apply _ hx', Trivialization.symm_apply_apply_mk _ hx',
    Trivialization.continuousLinearMapAt_apply_of_mem 𝕜 _ hy']

/-- A field that is `C^m` at the image point and tangent along a map near its source point has
a local `C^m` related field when the map is `C^n` there, `m + 1 ≤ n`, and its differential has
a continuous linear left inverse. The relation holds on a neighbourhood of the source point. -/
theorem ContMDiffAt.exists_vectorField_mfderiv_eventuallyEq
    (hf : ContMDiffAt I J n f x₀) (hmn : m + 1 ≤ n)
    (hinj : (mfderiv I J f x₀).HasLeftInverse) {V : Π y : N, TangentSpace J y}
    (hV : ContMDiffAt J J.tangent m (T% V) (f x₀))
    (htan : ∀ᶠ x in 𝓝 x₀, V (f x) ∈ (mfderiv I J f x).range) :
    ∃ X : Π x : M, TangentSpace I x,
      ContMDiffAt I I.tangent m (T% X) x₀ ∧
        ∀ᶠ x in 𝓝 x₀, mfderiv I J f x (X x) = V (f x) := by
  classical
  let X : Π x : M, TangentSpace I x := fun x ↦
    if h : V (f x) ∈ (mfderiv I J f x).range then Classical.choose h else 0
  have hXV : ∀ᶠ x in 𝓝 x₀, mfderiv I J f x (X x) = V (f x) := by
    filter_upwards [htan] with x hx
    dsimp only [X]
    rw [dite_eq_left hx]
    exact Classical.choose_spec hx
  refine ⟨X, hf.vectorField_of_mfderiv hmn hinj ?_, hXV⟩
  have hpush :
      (fun x ↦ (⟨f x, mfderiv I J f x (X x)⟩ : TangentBundle J N)) =ᶠ[𝓝 x₀]
        (T% V) ∘ f := hXV.mono fun x hx ↦ congrArg
          (fun v : TangentSpace J (f x) ↦ (⟨f x, v⟩ : TangentBundle J N)) hx
  exact (hV.comp x₀ (hf.of_le (le_self_add.trans hmn))).congr_of_eventuallyEq hpush

/-- An ambient `C^m` vector field tangent to a `C^n` map with split-injective differential
has a unique `C^m` related vector field on the domain, provided `m + 1 ≤ n`. Tangency means
membership in the differential image, not in the image of the map on points. -/
theorem ContMDiff.existsUnique_vectorField_mfderiv_eq
    (hf : ContMDiff I J n f) (hmn : m + 1 ≤ n)
    (hinj : ∀ x, (mfderiv I J f x).HasLeftInverse)
    {V : Π y : N, TangentSpace J y} (hV : ContMDiff J J.tangent m (T% V))
    (htan : ∀ x, V (f x) ∈ (mfderiv I J f x).range) :
    ∃! X : Π x : M, TangentSpace I x,
      ContMDiff I I.tangent m (T% X) ∧ ∀ x, mfderiv I J f x (X x) = V (f x) := by
  choose X hX hXV using fun x ↦ (hf x).exists_vectorField_mfderiv_eventuallyEq
    hmn (hinj x) (hV (f x)) (.of_forall htan)
  -- Pointwise uniqueness glues the local lifts into a single global field.
  let Y : Π x : M, TangentSpace I x := fun x ↦ X x x
  have hYV (x : M) : mfderiv I J f x (Y x) = V (f x) := (hXV x).self_of_nhds
  have hY : ContMDiff I I.tangent m (T% Y) := by
    intro x
    apply (hX x).congr_of_eventuallyEq
    filter_upwards [hXV x] with z hz
    exact congrArg (fun v : TangentSpace I z ↦ (⟨z, v⟩ : TangentBundle I M))
      ((hinj z).injective ((hYV z).trans hz.symm))
  refine ⟨Y, ⟨hY, hYV⟩, fun Z hZ ↦ ?_⟩
  funext x
  exact (hinj x).injective ((hZ.2 x).trans (hYV x).symm)

section LieBracket

variable [CompleteSpace F]
  [IsManifold I (minSmoothness 𝕜 2) M] [IsManifold J (minSmoothness 𝕜 2) N]

/-- The Lie bracket at an image point is tangent to a map when its differential there has a
continuous linear left inverse, the map is `C²` there, and both ambient fields are `C¹` there
and tangent along the map near the source point. Over fields other than `ℝ` or `ℂ`, the map
must be analytic. No regularity of the fields away from the chosen image point is assumed. -/
theorem ContMDiffAt.mlieBracket_mem_range_mfderiv
    (hf : ContMDiffAt I J n f x₀) (hn : minSmoothness 𝕜 2 ≤ n)
    (hinj : (mfderiv I J f x₀).HasLeftInverse) {V W : Π y : N, TangentSpace J y}
    (hV : ContMDiffAt J J.tangent 1 (T% V) (f x₀))
    (hW : ContMDiffAt J J.tangent 1 (T% W) (f x₀))
    (hVtan : ∀ᶠ x in 𝓝 x₀, V (f x) ∈ (mfderiv I J f x).range)
    (hWtan : ∀ᶠ x in 𝓝 x₀, W (f x) ∈ (mfderiv I J f x).range) :
    mlieBracket J V W (f x₀) ∈ (mfderiv I J f x₀).range := by
  classical
  have h2 : (2 : ℕ∞ω) ≤ n := le_minSmoothness.trans hn
  obtain ⟨X, hX, hXV⟩ := hf.exists_vectorField_mfderiv_eventuallyEq h2 hinj hV hVtan
  obtain ⟨Y, hY, hYW⟩ := hf.exists_vectorField_mfderiv_eventuallyEq h2 hinj hW hWtan
  -- Naturality of the bracket identifies its ambient value with a differential image.
  exact ⟨mlieBracket I X Y x₀, TauCeti.mfderiv_mlieBracket_of_eventually_related hf hn
    (hX.mdifferentiableAt one_ne_zero) (hY.mdifferentiableAt one_ne_zero)
    (hV.mdifferentiableAt one_ne_zero) (hW.mdifferentiableAt one_ne_zero) hXV hYW⟩

namespace Manifold.IsImmersion

/-- The Lie bracket of two `C¹` ambient vector fields tangent to an immersion is again
tangent to it. The immersion must be `C²` over `ℝ` or `ℂ`, and analytic over other fields.
The related fields on the domain are constructed from tangency; their existence and
regularity are not additional hypotheses. -/
theorem mlieBracket_mem_range_mfderiv (hf : IsImmersion I J n f)
    (hn : minSmoothness 𝕜 2 ≤ n) {V W : Π y : N, TangentSpace J y}
    (hV : ContMDiff J J.tangent 1 (T% V)) (hW : ContMDiff J J.tangent 1 (T% W))
    (hVtan : ∀ x, V (f x) ∈ (mfderiv I J f x).range)
    (hWtan : ∀ x, W (f x) ∈ (mfderiv I J f x).range) (x : M) :
    mlieBracket J V W (f x) ∈ (mfderiv I J f x).range := by
  have h2 : (2 : ℕ∞ω) ≤ n := le_minSmoothness.trans hn
  have hn0 : n ≠ 0 := ne_of_gt (lt_of_lt_of_le (by norm_num) h2)
  have hsplit : (mfderiv I J f x).HasLeftInverse :=
    isDiffImmersionAt_iff.mp (hf.isDiffImmersionAt hn0 x)
  exact (hf.contMDiff x).mlieBracket_mem_range_mfderiv hn hsplit (hV _) (hW _)
    (.of_forall hVtan) (.of_forall hWtan)

end Manifold.IsImmersion

end LieBracket
