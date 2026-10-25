/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorField.LieBracket
import TauCeti.Geometry.Manifold.VectorField.Regularity

/-!
# Model-space and directional-derivative formulas for the manifold Lie bracket

This file transports Mathlib's normed-space identity `fderivWithin_apply_lieBracket` through a
manifold chart. It identifies the differential of a vector-valued function on the manifold Lie
bracket with the commutator of its directional derivatives. It also records that constant vector
fields on a model space have zero manifold Lie bracket.

The chart argument follows the pullback idiom used for the manifold bracket in
`Mathlib/Geometry/Manifold/VectorField/LieBracket.lean`. The resulting lemma is a general manifold
prerequisite for Deliverable A, Layer 1 of the Lie-groups roadmap.

## Main results

* `TauCeti.mlieBracket_eq_lieBracket`: on a normed space, the manifold Lie bracket is the Lie
  bracket of vector fields on that space.
* `TauCeti.mlieBracket_const_model_space`: constant model-space vector fields have zero
  manifold Lie bracket.
* `mvfderiv_mlieBracket`: a differential sends the manifold bracket to the commutator of
  directional derivatives.
* `TauCeti.eq_mlieBracket_of_mvfderiv_extChartAt`: tested against the extended chart at a point,
  this identity characterises the manifold bracket at that point.
* `VectorField.lieBracketWithin_mpullbackWithin_extChartAt_symm`: at the chart centre, the flat
  bracket of the coordinate expressions of two fields is their manifold bracket.
* `VectorField.lieBracketWithin_neg_right` and `VectorField.mlieBracket_neg_right`: the flat and
  manifold brackets are odd in their second argument.
* `VectorField.jacobi_identity_mlieBracket_apply`: the cyclic Jacobi identity for the manifold
  bracket.
* `VectorField.contMDiff_mlieBracket`: the bracket of two smooth vector fields is smooth.

## References

* `Mathlib/Analysis/Calculus/VectorField.lean`, theorem `fderivWithin_apply_lieBracket`.
* `Mathlib/Geometry/Manifold/VectorField/LieBracket.lean`, for the chart-transport construction.
* [Lie groups and the Lie algebra correspondence roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/LieGroups/README.md),
  Deliverable A, Layer 1.
-/

public section

noncomputable section

open Bundle Filter Manifold VectorField
open scoped ContDiff Manifold Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {n : ℕ∞ω}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

section

variable [IsManifold I (minSmoothness 𝕜 2) M]

namespace TauCeti

/-- Constant vector fields on a normed vector space have zero manifold Lie bracket. -/
@[simp]
theorem mlieBracket_const_model_space (a b x : F) :
    VectorField.mlieBracket 𝓘(𝕜, F) (fun _ : F ↦ a) (fun _ : F ↦ b) x = 0 := by
  let A : ∀ y : F, TangentSpace 𝓘(𝕜, F) y := fun _ ↦ a
  let B : ∀ y : F, TangentSpace 𝓘(𝕜, F) y := fun _ ↦ b
  -- The explicit dependent fields expose the model-space representatives needed by the
  -- ordinary Fréchet derivative formula for the Lie bracket.
  change VectorField.mlieBracket 𝓘(𝕜, F) A B x = 0
  have h := congrFun (VectorField.mlieBracketWithin_eq_lieBracketWithin
    (V := A) (W := B) (s := Set.univ)) x
  rw [VectorField.mlieBracketWithin_univ] at h
  rw [h]
  have hA : fderivWithin 𝕜 A Set.univ x = 0 := by
    -- On the model space, `A` is definitionally the ordinary constant map with value `a`.
    change fderivWithin 𝕜 (fun _ : F ↦ a) Set.univ x = 0
    exact fderivWithin_const_apply (𝕜 := 𝕜) (E := F) (s := Set.univ) (x := x) a
  have hB : fderivWithin 𝕜 B Set.univ x = 0 := by
    -- On the model space, `B` is definitionally the ordinary constant map with value `b`.
    change fderivWithin 𝕜 (fun _ : F ↦ b) Set.univ x = 0
    exact fderivWithin_const_apply (𝕜 := 𝕜) (E := F) (s := Set.univ) (x := x) b
  rw [VectorField.lieBracketWithin, hA, hB]
  -- The tangent space of the model manifold is definitionally its model vector space.
  change (0 : F) - 0 = 0
  simp

/-- On a normed space, the manifold Lie bracket of two vector fields is their Lie bracket as maps
of the space. -/
theorem mlieBracket_eq_lieBracket {V W : ∀ y : F, TangentSpace 𝓘(𝕜, F) y} :
    VectorField.mlieBracket 𝓘(𝕜, F) V W = VectorField.lieBracket 𝕜 V W := by
  rw [← VectorField.mlieBracketWithin_univ, VectorField.mlieBracketWithin_eq_lieBracketWithin]
  exact VectorField.lieBracketWithin_univ

end TauCeti

/-- Let `f` have enough derivatives for symmetry of its second derivative at `x`, and let `V` and
`W` be differentiable vector fields there. Then the differential of `f` on the manifold bracket is
the commutator of its directional derivatives. This is the manifold counterpart of Mathlib's
`fderivWithin_apply_lieBracket`. -/
theorem mvfderiv_mlieBracket {f : M → F} {V W : ∀ x : M, TangentSpace I x} {x : M}
    (hf : CMDiffAt n f x) (hn : minSmoothness 𝕜 2 ≤ n)
    (hV : MDiffAt (fun y ↦ (V y : TangentBundle I M)) x)
    (hW : MDiffAt (fun y ↦ (W y : TangentBundle I M)) x) :
    mvfderiv I f x (mlieBracket I V W x) =
      mvfderiv I (fun y ↦ mvfderiv I f y (W y)) x (V x) -
        mvfderiv I (fun y ↦ mvfderiv I f y (V y)) x (W x) := by
  -- Express the manifold bracket and the outer differential in the chart at `x`.
  rw [← mlieBracketWithin_univ, mlieBracketWithin_apply]
  have hinv :
      (mfderiv% (extChartAt I x) x).inverse =
        mfderiv[Set.range I] (extChartAt I x).symm (extChartAt I x x) := by
    exact ContinuousLinearMap.inverse_eq
      (mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm'
        (mem_extChartAt_source x))
      (mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt'
        (mem_extChartAt_source x))
  rw [hinv]
  -- Normalize the same definitional tangent-space representation before applying the chart chain
  -- rule. The following `change`s only expose applications of that single linear-map identity.
  change (mfderiv% f x) _ = _
  have h2n : (2 : ℕ∞ω) ≤ n :=
    (le_minSmoothness (𝕜 := 𝕜) (n := (2 : ℕ∞ω))).trans hn
  have h1n : (1 : ℕ∞ω) ≤ n := (by norm_num : (1 : ℕ∞ω) ≤ 2).trans h2n
  have hf' : MDiffAt f x := (hf.of_le h2n).mdifferentiableAt (by norm_num)
  have hchain := mfderiv_comp_mfderivWithin_of_eq
    (I := 𝓘(𝕜, E)) (I' := I) (I'' := 𝓘(𝕜, F))
    (f := (extChartAt I x).symm) (g := f) (s := Set.range I)
    hf' (mdifferentiableWithinAt_extChartAt_symm (mem_extChartAt_target x))
    (by apply I.uniqueMDiffOn; exact Set.mem_range_self (f := I) _)
    (extChartAt_to_inv x)
  change @Eq (E →L[𝕜] F) _ _ at hchain
  let Z : E := lieBracketWithin 𝕜
    (mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x).symm V (Set.range I))
    (mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x).symm W (Set.range I))
    ((extChartAt I x).symm ⁻¹' Set.univ ∩ Set.range I) (extChartAt I x x)
  have hchain_apply := congrArg (fun L : E →L[𝕜] F ↦ L Z) hchain
  change _ = (mfderiv% f x) ((mfderiv[Set.range I]
    (extChartAt I x).symm (extChartAt I x x)) Z) at hchain_apply
  change (mfderiv% f x) ((mfderiv[Set.range I]
    (extChartAt I x).symm (extChartAt I x x)) Z) = _
  rw [← hchain_apply]
  rw [mfderivWithin_eq_fderivWithin]
  -- The rewrite leaves `(fromTangentSpace _).symm ∘L fderivWithin … ∘L fromTangentSpace _`,
  -- typed at the `TangentSpace` instances. Mathlib has no evaluation lemma for
  -- `NormedSpace.fromTangentSpace` (it is `tangentSpaceCastModel`, the identity up to those
  -- instances), so no rewrite strips it; the plain `fderivWithin` on `E` is reached by unfolding.
  change (fderivWithin 𝕜 (f ∘ (extChartAt I x).symm) (Set.range I) (extChartAt I x x)) Z = _
  -- Pull the vector fields back and invoke the normed-space bracket identity.
  have hfcoord := contMDiffWithinAt_iff_contDiffWithinAt.mp
    (contMDiffAt_iff_source.mp (hf.of_le hn))
  have hVcoord : DifferentiableWithinAt 𝕜
      (mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x).symm V (Set.range I))
      (Set.range I) (extChartAt I x x) := by
    simpa using (hV.mdifferentiableWithinAt (s := Set.univ))
      |>.differentiableWithinAt_mpullbackWithin_vectorField
  have hWcoord : DifferentiableWithinAt 𝕜
      (mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x).symm W (Set.range I))
      (Set.range I) (extChartAt I x x) := by
    simpa using (hW.mdifferentiableWithinAt (s := Set.univ))
      |>.differentiableWithinAt_mpullbackWithin_vectorField
  -- Identify chart directional derivatives with their manifold counterparts.
  have hf_chart : MDiffAt f ((extChartAt I x).symm (extChartAt I x x)) := by
    simpa only [extChartAt_to_inv] using hf'
  have hVf := TauCeti.mdifferentiableAt_mvfderiv_apply hf hn hV
  have hWf := TauCeti.mdifferentiableAt_mvfderiv_apply hf hn hW
  have hcoordW := (TauCeti.eventuallyEq_fderivWithin_chart_apply_mpullbackWithin
    (I := I) (U := W) hf h1n).fderivWithin_eq
    (𝕜 := 𝕜) (by
      simpa only [Function.comp_apply, extChartAt_to_inv] using
        TauCeti.fderivWithin_chart_apply_mpullbackWithin
          (I := I) (U := W) (mem_extChartAt_target x) hf_chart)
  have hcoordV := (TauCeti.eventuallyEq_fderivWithin_chart_apply_mpullbackWithin
    (I := I) (U := V) hf h1n).fderivWithin_eq
    (𝕜 := 𝕜) (by
      simpa only [Function.comp_apply, extChartAt_to_inv] using
        TauCeti.fderivWithin_chart_apply_mpullbackWithin
          (I := I) (U := V) (mem_extChartAt_target x) hf_chart)
  have houterW := TauCeti.fderivWithin_chart_apply_mpullbackWithin
    (I := I) (p := fun y ↦ mvfderiv I f y (W y)) (U := V)
    (mem_extChartAt_target x) (by simpa only [extChartAt_to_inv] using hWf)
  have houterV := TauCeti.fderivWithin_chart_apply_mpullbackWithin
    (I := I) (p := fun y ↦ mvfderiv I f y (V y)) (U := W)
    (mem_extChartAt_target x) (by simpa only [extChartAt_to_inv] using hVf)
  rw [extChartAt_to_inv] at houterW houterV
  have hZ : Z = lieBracketWithin 𝕜
    (mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x).symm V (Set.range I))
    (mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x).symm W (Set.range I))
    (Set.range I) (extChartAt I x x) := by
    simp only [Z, Set.preimage_univ, Set.univ_inter]
  rw [hZ]
  rw [fderivWithin_apply_lieBracket hfcoord le_rfl I.uniqueDiffOn
    (I.range_subset_closure_interior (Set.mem_range_self (f := I) _))
    (Set.mem_range_self (f := I) _) hWcoord hVcoord]
  rw [hcoordW, hcoordV]
  exact congrArg₂ (· - ·) houterW houterV

namespace TauCeti

/-- A tangent vector `v` at `x` is the Lie bracket of the differentiable vector fields `V` and `W`
at `x` as soon as the differential of the extended chart at `x` sends `v` to the commutator of the
directional derivatives of the chart along `V` and `W`, since that differential is injective. -/
theorem eq_mlieBracket_of_mvfderiv_extChartAt {V W : ∀ y : M, TangentSpace I y} {x : M}
    (hV : MDiffAt (fun y ↦ (V y : TangentBundle I M)) x)
    (hW : MDiffAt (fun y ↦ (W y : TangentBundle I M)) x) {v : TangentSpace I x}
    (hv : mvfderiv I (extChartAt I x) x v =
      mvfderiv I (fun y ↦ mvfderiv I (extChartAt I x) y (W y)) x (V x) -
        mvfderiv I (fun y ↦ mvfderiv I (extChartAt I x) y (V y)) x (W x)) :
    v = mlieBracket I V W x := by
  rw [← mvfderiv_mlieBracket contMDiffAt_extChartAt le_rfl hV hW] at hv
  have : IsManifold I 1 M :=
    .of_le ((show (1 : ℕ∞ω) ≤ 2 by norm_num).trans (le_minSmoothness (𝕜 := 𝕜)))
  obtain ⟨e, he⟩ := isInvertible_mfderiv_extChartAt (I := I) (mem_extChartAt_source x)
  have hinj : Function.Injective (mvfderiv I (extChartAt I x) x) := by
    rw [mvfderiv, ContinuousLinearMap.coe_comp, ← he]
    exact (NormedSpace.fromTangentSpace _).injective.comp e.injective
  exact hinj hv

end TauCeti

end

namespace VectorField

omit [CompleteSpace E] in
/-- At the centre of the preferred chart, the Lie bracket of the inverse-chart pullbacks of two
vector fields is their manifold Lie bracket. -/
theorem lieBracketWithin_mpullbackWithin_extChartAt_symm [IsManifold I 1 M]
    (V W : ∀ y : M, TangentSpace I y) (s : Set M) (x : M) :
    lieBracketWithin 𝕜 (mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x).symm V (Set.range I))
      (mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x).symm W (Set.range I))
      ((extChartAt I x).symm ⁻¹' s ∩ Set.range I) (extChartAt I x x) =
        mlieBracketWithin I V W s x := by
  -- The chart derivative at its centre is the identity of `E`; `TangentSpace I x` is not
  -- syntactically `E`, so the identification is made on the inverse before evaluating it.
  have hinverse : (mfderiv I 𝓘(𝕜, E) (extChartAt I x) x).inverse = ContinuousLinearMap.id 𝕜 E :=
    (congrArg (fun f : E →L[𝕜] E ↦ f.inverse) (mfderiv_extChartAt_self (I := I) (x := x))).trans
      ContinuousLinearMap.inverse_id
  rw [mlieBracketWithin_apply]
  exact (congrArg (fun f : E →L[𝕜] E ↦ f (lieBracketWithin 𝕜 _ _ _ _)) hinverse).symm

omit [CompleteSpace E] in
/-- On a normed space, negating the second vector field negates the Lie bracket at any point where
the set has unique derivatives. -/
theorem lieBracketWithin_neg_right {V W : E → E} {s : Set E} {x : E}
    (hs : UniqueDiffWithinAt 𝕜 s x) :
    lieBracketWithin 𝕜 V (-W) s x = -lieBracketWithin 𝕜 V W s x := by
  rw [lieBracketWithin, lieBracketWithin, fderivWithin_neg hs, Pi.neg_apply, map_neg, neg_apply]
  abel

omit [CompleteSpace E] in
/-- Negating the second vector field negates the manifold Lie bracket. -/
theorem mlieBracket_neg_right {V W : ∀ y : M, TangentSpace I y} {x : M} :
    mlieBracket I V (-W) x = -mlieBracket I V W x := by
  have hs : UniqueDiffWithinAt 𝕜 ((extChartAt I x).symm ⁻¹' Set.univ ∩ Set.range I)
      (extChartAt I x x) := by
    rw [Set.preimage_univ, Set.univ_inter]
    exact I.uniqueDiffOn _ (Set.mem_range_self _)
  rw [← mlieBracketWithin_univ, ← mlieBracketWithin_univ]
  simp only [mlieBracketWithin_apply, mpullbackWithin_neg]
  exact (congrArg _ (lieBracketWithin_neg_right hs)).trans (map_neg _ _)

/-- The **Jacobi identity** for the manifold Lie bracket, in cyclic form:
`[U, [V, W]] + [V, [W, U]] + [W, [U, V]] = 0`. This rearranges Mathlib's Leibniz form
`leibniz_identity_mlieBracket_apply`. -/
theorem jacobi_identity_mlieBracket_apply [IsManifold I (minSmoothness 𝕜 3) M]
    {U V W : ∀ y : M, TangentSpace I y} {x : M}
    (hU : CMDiffAt (minSmoothness 𝕜 2) (T% U) x)
    (hV : CMDiffAt (minSmoothness 𝕜 2) (T% V) x)
    (hW : CMDiffAt (minSmoothness 𝕜 2) (T% W) x) :
    mlieBracket I U (mlieBracket I V W) x + mlieBracket I V (mlieBracket I W U) x +
      mlieBracket I W (mlieBracket I U V) x = 0 := by
  rw [leibniz_identity_mlieBracket_apply hU hV hW,
    mlieBracket_swap_apply (V := mlieBracket I U V), mlieBracket_swap (V := U) (W := W),
    mlieBracket_neg_right]
  abel

/-- The Lie bracket of two smooth vector fields is smooth. -/
theorem contMDiff_mlieBracket [IsRCLikeNormedField 𝕜] [IsManifold I ∞ M]
    {V W : ∀ y : M, TangentSpace I y} (hV : CMDiff ∞ (T% V)) (hW : CMDiff ∞ (T% W)) :
    CMDiff ∞ (T% (mlieBracket I V W)) := by
  let _ : IsManifold I (minSmoothness 𝕜 2) M :=
    IsManifold.of_le (m := minSmoothness 𝕜 2) (n := ∞) (by simp)
  let _ : IsManifold I ((∞ : ℕ∞ω) + 1) M :=
    IsManifold.of_le (m := (∞ : ℕ∞ω) + 1) (n := ∞) (by simp)
  exact ContDiff.mlieBracket_vectorField (m := (⊤ : ℕ∞)) (n := (⊤ : ℕ∞)) hV hW (by simp)

end VectorField
