/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.SmoothEmbedding.NormalSpace.Trivialization
public import TauCeti.Geometry.Manifold.MFDeriv.NormalCoordinates

/-!
# Smooth transitions of intrinsic normal coordinates

Fixed complementary coordinates for the normal spaces of an embedding have smooth transition
operators on their overlaps. When the product of the source and complementary model spaces is
complete, the transitions of a `C^n` embedding are `C^m` when `m + 1 ≤ n`, including smooth
and analytic orders. The source and ambient manifolds may have corners.

The transition takes a complementary representative in the old ambient tangent chart, changes
ambient tangent coordinates, and projects onto the new complement. We identify the transitions of
the actual local normal-bundle trivializations with this operator formula. Thus smooth normal
bundle constructions can use the quotient topology and the existing complementary charts without
assuming regularity of their transitions.

Reference: J. M. Lee, *Introduction to Smooth Manifolds*, second edition, the normal-bundle
construction preceding Theorem 6.24.
-/

public section

noncomputable section

open Set Bundle
open scoped Manifold ContDiff

namespace TauCeti.SmoothEmbedding

variable {𝕜 E F P H G M N : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [TopologicalSpace H] [TopologicalSpace G]
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 F G}
  [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace N] [ChartedSpace G N]
  {n : ℕ∞ω}

section Trivialization

variable [IsManifold I 1 M] [IsManifold J 1 N]
  [TopologicalSpace P] [AddCommGroup P] [Module 𝕜 P]

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
normal transition operator. The complementary model need only be a topological module;
no global normal-bundle atlas is required. -/
theorem normalSpaceTrivializationOfComplement_coordChangeL {x : M} (hx : x ∈ U ∩ V) :
    letI := f.instTopologicalSpaceNormalBundle (K := P) hn
    ((f.normalSpaceTrivializationOfComplement hn x₀ U hUopen hU B hB hcoordB).coordChangeL 𝕜
      (f.normalSpaceTrivializationOfComplement hn x₁ V hVopen hV C hC hcoordC) x :
        P →L[𝕜] P) =
      (inTangentCoordinates I J _root_.id (f : M → N)
        (mfderiv I J (f : M → N)) x₁ x).quotientRangeCoordinate C ∘L
        ((trivializationAt F (TangentSpace J) (f x₀)).coordChangeL 𝕜
          (trivializationAt F (TangentSpace J) (f x₁)) (f x)).toContinuousLinearMap ∘L B := by
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

end Trivialization

section Regularity

variable [NormedAddCommGroup P] [NormedSpace 𝕜 P]

/-- The complementary normal trivializations have `C^m` transition operators on their
base-set overlaps for a `C^n` embedding with `m + 1 ≤ n`, provided the product of the source
and complementary model spaces is complete. This supplies the transition regularity needed
to assemble the intrinsic normal spaces as a smooth vector bundle. -/
theorem contMDiffOn_normalSpaceTrivializationOfComplement_coordChangeL [CompleteSpace (E × P)]
    (f : SmoothEmbedding I J n M N)
    (x₀ x₁ : M) (U V : Set M) (hUopen : IsOpen U) (hVopen : IsOpen V)
    (hU : U ⊆ (chartAt H x₀).source ∩ f ⁻¹' (chartAt G (f x₀)).source)
    (hV : V ⊆ (chartAt H x₁).source ∩ f ⁻¹' (chartAt G (f x₁)).source)
    (B C : P →L[𝕜] F)
    {m : ℕ∞ω} [IsManifold I (m + 1) M] [IsManifold J (m + 1) N] (hm : m + 1 ≤ n) :
    haveI : IsManifold I 1 M := .of_le (n := m + 1) le_add_self
    haveI : IsManifold J 1 N := .of_le (n := m + 1) le_add_self
    have hn : n ≠ 0 := ENat.one_le_iff_ne_zero_withTop.mp ((le_add_left le_rfl).trans hm)
    ∀ (hB : ∀ x ∈ U, ((inTangentCoordinates I J _root_.id (f : M → N)
        (mfderiv I J (f : M → N)) x₀ x).coprod B).IsInvertible)
      (hC : ∀ x ∈ V, ((inTangentCoordinates I J _root_.id (f : M → N)
        (mfderiv I J (f : M → N)) x₁ x).coprod C).IsInvertible)
      (hcoordB : Continuous (fun p : U × F ↦
        (inTangentCoordinates I J _root_.id (f : M → N)
          (mfderiv I J (f : M → N)) x₀ p.1).quotientRangeCoordinate B p.2))
      (hcoordC : Continuous (fun p : V × F ↦
        (inTangentCoordinates I J _root_.id (f : M → N)
          (mfderiv I J (f : M → N)) x₁ p.1).quotientRangeCoordinate C p.2)),
    letI := f.instTopologicalSpaceNormalBundle (K := P) hn
    ContMDiffOn I 𝓘(𝕜, P →L[𝕜] P) m
      (fun x =>
        ((f.normalSpaceTrivializationOfComplement hn x₀ U hUopen hU B hB hcoordB).coordChangeL 𝕜
          (f.normalSpaceTrivializationOfComplement hn x₁ V hVopen hV C hC hcoordC) x :
            P →L[𝕜] P)) (U ∩ V) := by
  have : IsManifold I 1 M := .of_le (n := m + 1) le_add_self
  have : IsManifold J 1 N := .of_le (n := m + 1) le_add_self
  have hn : n ≠ 0 := ENat.one_le_iff_ne_zero_withTop.mp ((le_add_left le_rfl).trans hm)
  dsimp only
  intro hB hC hcoordB hcoordC
  let := f.instTopologicalSpaceNormalBundle (K := P) hn
  have h := f.contMDiff.contMDiffOn.normalQuotientCoordinateChange hm (hUopen.inter hVopen)
    x₀ x₁ B C (fun y hy => (hV hy.2).1) (fun y hy => (hU hy.1).2)
    (fun y hy => (hV hy.2).2) (fun y hy => hC y hy.2)
  exact h.congr fun y hy =>
    f.normalSpaceTrivializationOfComplement_coordChangeL hn x₀ x₁ U V hUopen hVopen
      hU hV B C hB hC hcoordB hcoordC hy

end Regularity

end TauCeti.SmoothEmbedding
