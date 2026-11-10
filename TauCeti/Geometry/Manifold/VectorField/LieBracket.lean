/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorField.LieBracket
import TauCeti.Geometry.Manifold.MFDeriv.Chart.Basic
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

* `VectorField.mlieBracket_eq_lieBracket`: on a normed space, the manifold Lie bracket is the Lie
  bracket of vector fields on that space.
* `VectorField.mlieBracket_const_model_space`: constant model-space vector fields have zero
  manifold Lie bracket.
* `VectorField.mlieBracket_continuousLinearMap_model_space`: the manifold Lie bracket of the linear
  vector fields `y ↦ A y` and `y ↦ B y` is `x ↦ B (A x) - A (B x)`.
* `mvfderiv_mlieBracket`: a differential sends the manifold bracket to the commutator of
  directional derivatives.
* `TauCeti.eq_mlieBracket_of_mvfderiv_extChartAt`: tested against the extended chart at a point,
  this identity characterises the manifold bracket at that point.
* `VectorField.lieBracketWithin_mpullbackWithin_extChartAt_symm`: at the chart centre, the flat
  bracket of the coordinate expressions of two fields is their manifold bracket.
* `VectorField.lieBracketWithin_neg_right` and `VectorField.mlieBracket_neg_right`: the flat and
  manifold brackets are odd in their second argument.
* `VectorField.mlieBracket_neg_left`: the manifold bracket is odd in its first argument.
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

namespace VectorField

/-- On a normed space, the manifold Lie bracket of two vector fields is their Lie bracket as maps
of the space. -/
theorem mlieBracket_eq_lieBracket {V W : ∀ y : F, TangentSpace 𝓘(𝕜, F) y} :
    VectorField.mlieBracket 𝓘(𝕜, F) V W = VectorField.lieBracket 𝕜 V W := by
  rw [← VectorField.mlieBracketWithin_univ, VectorField.mlieBracketWithin_eq_lieBracketWithin]
  exact VectorField.lieBracketWithin_univ

/-- The manifold Lie bracket of a constant vector field `a` with a vector field `W` on a normed
space is the derivative of `W` in the direction `a`. -/
@[simp]
theorem mlieBracket_const_left_model_space (a : F) (W : ∀ y : F, TangentSpace 𝓘(𝕜, F) y)
    (x : F) :
    VectorField.mlieBracket 𝓘(𝕜, F) (fun _ : F ↦ a) W x = fderiv 𝕜 W x a := by
  let A : ∀ y : F, TangentSpace 𝓘(𝕜, F) y := fun _ ↦ a
  -- The explicit dependent section exposes the model-space representative.
  change VectorField.mlieBracket 𝓘(𝕜, F) A W x = _
  rw [mlieBracket_eq_lieBracket]
  -- The tangent space of the model manifold is definitionally its model vector space.
  change fderiv 𝕜 W x a - fderiv 𝕜 (fun _ : F ↦ a) x (W x) = _
  simp only [fderiv_const_apply, sub_eq_self]
  rfl

/-- Constant vector fields on a normed vector space have zero manifold Lie bracket. -/
@[simp]
theorem mlieBracket_const_model_space (a b x : F) :
    VectorField.mlieBracket 𝓘(𝕜, F) (fun _ : F ↦ a) (fun _ : F ↦ b) x = 0 :=
  (mlieBracket_const_left_model_space a _ x).trans (by simp; rfl)

/-- The manifold Lie bracket of a vector field `V` with a constant vector field `b` on a normed
space is minus the derivative of `V` in the direction `b`. -/
@[simp]
theorem mlieBracket_const_right_model_space (V : ∀ y : F, TangentSpace 𝓘(𝕜, F) y) (b x : F) :
    VectorField.mlieBracket 𝓘(𝕜, F) V (fun _ : F ↦ b) x = -fderiv 𝕜 V x b := by
  let B : ∀ y : F, TangentSpace 𝓘(𝕜, F) y := fun _ ↦ b
  -- The explicit dependent section exposes the model-space representative.
  change VectorField.mlieBracket 𝓘(𝕜, F) V B x = _
  rw [mlieBracket_eq_lieBracket]
  -- The tangent space of the model manifold is definitionally its model vector space.
  change fderiv 𝕜 (fun _ : F ↦ b) x (V x) - fderiv 𝕜 V x b = _
  rw [fderiv_const_apply]
  exact zero_sub _

/-- The manifold Lie bracket of the linear vector fields `y ↦ A y` and `y ↦ B y` on a normed
vector space is the linear vector field `x ↦ B (A x) - A (B x)`. -/
theorem mlieBracket_continuousLinearMap_model_space (A B : F →L[𝕜] F) (x : F) :
    VectorField.mlieBracket 𝓘(𝕜, F) (fun y ↦ A y) (fun y ↦ B y) x = B (A x) - A (B x) := by
  refine (congrFun mlieBracket_eq_lieBracket x).trans ?_
  rw [VectorField.lieBracket, A.fderiv, B.fderiv]

end VectorField

omit [CompleteSpace E] in
/-- The differential of `f` on the manifold bracket, read in the chart at `x`: it is the derivative
of `f` in that chart applied to the flat bracket of the pulled-back vector fields. -/
private theorem mvfderiv_mlieBracket_eq_fderivWithin_lieBracketWithin {f : M → F}
    {V W : ∀ x : M, TangentSpace I x} {x : M} (hf : MDiffAt f x) :
    mvfderiv I f x (mlieBracket I V W x) =
      fderivWithin 𝕜 (f ∘ (extChartAt I x).symm) (Set.range I) (extChartAt I x x)
        (lieBracketWithin 𝕜
          (mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x).symm V (Set.range I))
          (mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x).symm W (Set.range I))
          (Set.range I) (extChartAt I x x)) := by
  -- Express the manifold bracket in the chart at `x`.
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
  have hchain := mfderiv_comp_mfderivWithin_of_eq
    (I := 𝓘(𝕜, E)) (I' := I) (I'' := 𝓘(𝕜, F))
    (f := (extChartAt I x).symm) (g := f) (s := Set.range I)
    hf (mdifferentiableWithinAt_extChartAt_symm (mem_extChartAt_target x))
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
  rw [← hchain_apply, mfderivWithin_eq_fderivWithin]
  -- The rewrite leaves `(fromTangentSpace _).symm ∘L fderivWithin … ∘L fromTangentSpace _`,
  -- typed at the `TangentSpace` instances. Mathlib has no evaluation lemma for
  -- `NormedSpace.fromTangentSpace` (it is `tangentSpaceCastModel`, the identity up to those
  -- instances), so no rewrite strips it; the plain `fderivWithin` on `E` is reached by unfolding.
  change (fderivWithin 𝕜 (f ∘ (extChartAt I x).symm) (Set.range I) (extChartAt I x x)) Z = _
  simp only [Z, Set.preimage_univ, Set.univ_inter]

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
  have h2n : (2 : ℕ∞ω) ≤ n :=
    (le_minSmoothness (𝕜 := 𝕜) (n := (2 : ℕ∞ω))).trans hn
  have hf' : MDiffAt f x := (hf.of_le h2n).mdifferentiableAt (by norm_num)
  rw [mvfderiv_mlieBracket_eq_fderivWithin_lieBracketWithin hf']
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
  rw [fderivWithin_apply_lieBracket hfcoord le_rfl I.uniqueDiffOn
    (I.range_subset_closure_interior (Set.mem_range_self (f := I) _))
    (Set.mem_range_self (f := I) _) hWcoord hVcoord,
    TauCeti.fderivWithin_fderivWithin_chart_apply_mpullbackWithin hf hn hW,
    TauCeti.fderivWithin_fderivWithin_chart_apply_mpullbackWithin hf hn hV]

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
theorem lieBracketWithin_mpullbackWithin_extChartAt_symm
    (V W : ∀ y : M, TangentSpace I y) (s : Set M) (x : M) :
    lieBracketWithin 𝕜 (mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x).symm V (Set.range I))
      (mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x).symm W (Set.range I))
      ((extChartAt I x).symm ⁻¹' s ∩ Set.range I) (extChartAt I x x) =
        mlieBracketWithin I V W s x := by
  -- The chart derivative at its centre is the identity of `E`; `TangentSpace I x` is not
  -- syntactically `E`, so the identification is made on the inverse before evaluating it.
  have hinverse : (mfderiv I 𝓘(𝕜, E) (extChartAt I x) x).inverse = ContinuousLinearMap.id 𝕜 E := by
    rw [TauCeti.mfderiv_extChartAt_eq_id]
    exact ContinuousLinearMap.inverse_id
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

omit [CompleteSpace E] in
/-- Negating the first vector field negates the manifold Lie bracket. -/
theorem mlieBracket_neg_left {V W : ∀ y : M, TangentSpace I y} {x : M} :
    mlieBracket I (-V) W x = -mlieBracket I V W x := by
  rw [mlieBracket_swap_apply, mlieBracket_neg_right, neg_neg, mlieBracket_swap_apply]

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
