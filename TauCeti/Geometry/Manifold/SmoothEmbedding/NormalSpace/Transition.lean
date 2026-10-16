/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.SmoothEmbedding.NormalSpace.Trivialization
public import TauCeti.Geometry.Manifold.MFDeriv.Coordinates
import TauCeti.Geometry.Manifold.ContMDiff.QuotientRange

/-!
# Smooth transitions of intrinsic normal coordinates

Fixed complementary coordinates for the normal spaces of an embedding have smooth transition
operators on their overlaps. For a `C^n` embedding the transitions are `C^m` when `m + 1 ≤ n`,
including smooth and analytic orders. The source and ambient manifolds may have corners.

The transition takes a complementary representative in the old ambient tangent chart, changes
ambient tangent coordinates, and projects onto the new complement. We prove regularity both for
this operator formula and for the actual local normal-bundle trivializations. Thus smooth normal
bundle constructions can use the quotient topology and the existing complementary charts without
assuming regularity of their transitions.

The proof uses `ContMDiffAt.mfderiv_inTangentCoordinates`, the quotient-range coordinate calculus,
and Mathlib's regularity of tangent-bundle coordinate changes.

Reference: J. M. Lee, *Introduction to Smooth Manifolds*, second edition, the normal-bundle
construction preceding Theorem 6.24.
-/

public section

noncomputable section

open Set Bundle
open scoped Manifold ContDiff

namespace TauCeti.SmoothEmbedding

variable {𝕜 E F P Q H G M N : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup P] [NormedSpace 𝕜 P]
  [NormedAddCommGroup Q] [NormedSpace 𝕜 Q]
  [TopologicalSpace H] [TopologicalSpace G]
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 F G}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [TopologicalSpace N] [ChartedSpace G N] [IsManifold J 1 N]
  {n : ℕ∞ω}

/-- The operator extending the transition between fixed complementary normal coordinates.
On the common coordinate domain it represents the change from the complement `B` in the tangent
chart at `f x₀` to the complement `C` in the tangent chart at `f x₁`. -/
def normalSpaceTransitionOfComplement (f : SmoothEmbedding I J n M N)
    (x₀ x₁ : M) (B : P →L[𝕜] F) (C : Q →L[𝕜] F) (x : M) : P →L[𝕜] Q :=
  ((inTangentCoordinates I J _root_.id (f : M → N)
    (mfderiv I J (f : M → N)) x₁ x).quotientRangeCoordinate C).comp
      ((((trivializationAt F (TangentSpace J) (f x₀)).coordChangeL 𝕜
        (trivializationAt F (TangentSpace J) (f x₁)) (f x)) : F →L[𝕜] F).comp B)

/-- Evaluate the normal transition by changing the ambient tangent coordinates of a
complementary representative and projecting onto the receiving complement. -/
@[simp]
theorem normalSpaceTransitionOfComplement_apply (f : SmoothEmbedding I J n M N)
    (x₀ x₁ : M) (B : P →L[𝕜] F) (C : Q →L[𝕜] F) (x : M) (w : P) :
    f.normalSpaceTransitionOfComplement x₀ x₁ B C x w =
      (inTangentCoordinates I J _root_.id (f : M → N)
        (mfderiv I J (f : M → N)) x₁ x).quotientRangeCoordinate C
        ((trivializationAt F (TangentSpace J) (f x₀)).coordChangeL 𝕜
          (trivializationAt F (TangentSpace J) (f x₁)) (f x) (B w)) := by
  simp [normalSpaceTransitionOfComplement]

/-- On the overlap, the transition operator is the composition of the intrinsic normal
coordinate equivalences, even when their complementary model spaces differ. -/
theorem normalSpaceTransitionOfComplement_eq_trans (f : SmoothEmbedding I J n M N)
    (hn : n ≠ 0) {x₀ x₁ x : M}
    (hx₀ : x ∈ (chartAt H x₀).source) (hy₀ : f x ∈ (chartAt G (f x₀)).source)
    (hx₁ : x ∈ (chartAt H x₁).source) (hy₁ : f x ∈ (chartAt G (f x₁)).source)
    (B : P →L[𝕜] F) (C : Q →L[𝕜] F)
    (hB : ((inTangentCoordinates I J _root_.id (f : M → N)
      (mfderiv I J (f : M → N)) x₀ x).coprod B).IsInvertible)
    (hC : ((inTangentCoordinates I J _root_.id (f : M → N)
      (mfderiv I J (f : M → N)) x₁ x).coprod C).IsInvertible) :
    f.normalSpaceTransitionOfComplement x₀ x₁ B C x =
      ((f.normalSpaceEquivOfComplement hn hx₀ hy₀ B hB).symm.trans
        (f.normalSpaceEquivOfComplement hn hx₁ hy₁ C hC)).toContinuousLinearMap := by
  ext w
  exact (f.normalSpaceEquivOfComplement_apply_symm_eq_quotientRangeCoordinate_coordChangeL
    hn hx₀ hy₀ hx₁ hy₁ B C hB hC w).symm

/-- Complementary normal transition operators are `C^m` wherever the receiving complement
is valid and the chosen tangent charts are defined. Only the ambient model must be complete;
no finite-dimensionality or metric is required. -/
theorem contMDiffAt_normalSpaceTransitionOfComplement [CompleteSpace F]
    {m : ℕ∞ω} [IsManifold I (m + 1) M] [IsManifold J (m + 1) N]
    (f : SmoothEmbedding I J n M N) (hm : m + 1 ≤ n) {x₀ x₁ x : M}
    (hx₁ : x ∈ (chartAt H x₁).source)
    (hy₀ : f x ∈ (chartAt G (f x₀)).source)
    (hy₁ : f x ∈ (chartAt G (f x₁)).source)
    (B : P →L[𝕜] F) (C : Q →L[𝕜] F)
    (hC : ((inTangentCoordinates I J _root_.id (f : M → N)
      (mfderiv I J (f : M → N)) x₁ x).coprod C).IsInvertible) :
    ContMDiffAt I 𝓘(𝕜, P →L[𝕜] Q) m
      (f.normalSpaceTransitionOfComplement x₀ x₁ B C) x := by
  obtain ⟨e, he⟩ := hC
  have : CompleteSpace (E × Q) :=
    (e.isUniformEmbedding.completeSpace_congr e.surjective).mpr inferInstance
  let := TangentBundle.contMDiffVectorBundle (I := J) (M := N) (n := m)
  have hderiv := f.contMDiff.contMDiffAt.mfderiv_inTangentCoordinates hm hx₁ hy₁
  have hproj := hderiv.quotientRangeCoordinate C ⟨e, he⟩
  have hchange : ContMDiffAt I 𝓘(𝕜, F →L[𝕜] F) m
      (fun y => ((trivializationAt F (TangentSpace J) (f x₀)).coordChangeL 𝕜
        (trivializationAt F (TangentSpace J) (f x₁)) (f y) : F →L[𝕜] F)) x :=
    (f.contMDiff.contMDiffAt.of_le (le_self_add.trans hm)).coordChangeL
      (by simpa using hy₀) (by simpa using hy₁)
  exact hproj.clm_comp (hchange.clm_comp contMDiffAt_const)

section Trivialization

variable (f : SmoothEmbedding I J n M N) (hn : n ≠ 0)
  (x₀ x₁ : M) (U V : Set M) (hUopen : IsOpen U) (hVopen : IsOpen V)
  (hU : U ⊆ (chartAt H x₀).source ∩ f ⁻¹' (chartAt G (f x₀)).source)
  (hV : V ⊆ (chartAt H x₁).source ∩ f ⁻¹' (chartAt G (f x₁)).source)
  (B C : P →L[𝕜] F)
  (hB : ∀ x ∈ U, ((inTangentCoordinates I J _root_.id (f : M → N)
    (mfderiv I J (f : M → N)) x₀ x).coprod B).IsInvertible)
  (hC : ∀ x ∈ V, ((inTangentCoordinates I J _root_.id (f : M → N)
    (mfderiv I J (f : M → N)) x₁ x).coprod C).IsInvertible)
  (hcoordB : Continuous (fun p : U × F ↦
    (inTangentCoordinates I J _root_.id (f : M → N)
      (mfderiv I J (f : M → N)) x₀ p.1).quotientRangeCoordinate B p.2))
  (hcoordC : Continuous (fun p : V × F ↦
    (inTangentCoordinates I J _root_.id (f : M → N)
      (mfderiv I J (f : M → N)) x₁ p.1).quotientRangeCoordinate C p.2))

/-- The transition of the actual quotient-topology normal trivializations is the complementary
normal transition operator. This formula does not require a global normal-bundle atlas. -/
theorem normalSpaceTrivializationOfComplement_coordChangeL {x : M} (hx : x ∈ U ∩ V) :
    letI := f.instTopologicalSpaceNormalBundle (K := P) hn
    ((f.normalSpaceTrivializationOfComplement hn x₀ U hUopen hU B hB hcoordB).coordChangeL 𝕜
      (f.normalSpaceTrivializationOfComplement hn x₁ V hVopen hV C hC hcoordC) x :
        P →L[𝕜] P) = f.normalSpaceTransitionOfComplement x₀ x₁ B C x := by
  let := f.instTopologicalSpaceNormalBundle (K := P) hn
  ext w
  rw [ContinuousLinearEquiv.coe_coe,
    Trivialization.coordChangeL_apply' _ _ (by simpa using hx)]
  rw [normalSpaceTrivializationOfComplement_symm_apply f hn x₀ U hUopen hU B hB hcoordB
    (x, w) hx.1]
  rw [normalSpaceTrivializationOfComplement_apply f hn x₁ V hVopen hV C hC hcoordC
    _ hx.2]
  exact f.normalSpaceEquivOfComplement_apply_symm_eq_quotientRangeCoordinate_coordChangeL
    hn (hU hx.1).1 (hU hx.1).2 (hV hx.2).1 (hV hx.2).2 B C (hB x hx.1) (hC x hx.2) w

/-- The complementary normal trivializations have `C^m` transition operators on their
base-set overlaps for a `C^n` embedding with `m + 1 ≤ n`. This supplies the transition
regularity needed to assemble the intrinsic normal spaces as a smooth vector bundle. -/
theorem contMDiffOn_normalSpaceTrivializationOfComplement_coordChangeL [CompleteSpace F]
    {m : ℕ∞ω} [IsManifold I (m + 1) M] [IsManifold J (m + 1) N] (hm : m + 1 ≤ n) :
    letI := f.instTopologicalSpaceNormalBundle (K := P) hn
    ContMDiffOn I 𝓘(𝕜, P →L[𝕜] P) m
      (fun x =>
        ((f.normalSpaceTrivializationOfComplement hn x₀ U hUopen hU B hB hcoordB).coordChangeL 𝕜
          (f.normalSpaceTrivializationOfComplement hn x₁ V hVopen hV C hC hcoordC) x :
            P →L[𝕜] P)) (U ∩ V) := by
  let := f.instTopologicalSpaceNormalBundle (K := P) hn
  have h : ContMDiffOn I 𝓘(𝕜, P →L[𝕜] P) m
      (f.normalSpaceTransitionOfComplement x₀ x₁ B C) (U ∩ V) := by
    intro x hx
    exact (f.contMDiffAt_normalSpaceTransitionOfComplement hm (hV hx.2).1
      (hU hx.1).2 (hV hx.2).2 B C (hC x hx.2)).contMDiffWithinAt
  exact h.congr fun x hx =>
    f.normalSpaceTrivializationOfComplement_coordChangeL hn x₀ x₁ U V hUopen hVopen
      hU hV B C hB hC hcoordB hcoordC hx

end Trivialization

end TauCeti.SmoothEmbedding
