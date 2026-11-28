/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.DegreeOne
public import TauCeti.Geometry.Manifold.VectorBundle.Cotangent.Relation
public import TauCeti.Geometry.Manifold.VectorBundle.Translate

/-!
# Fibre translations and the cotangent relation

Let `ρ : Q → B` be a smooth map and `γ` a one-form on `B`. If a covector `p` at `q` is related to a
covector `p'` at `ρ q` by the cotangent relation of `ρ`, that is `p = p' ∘ dρ_q`
(`TauCeti.CotangentBundle.cotangentRel`), then translating `p` by the pullback `ρ^* γ` and `p'` by
`γ` keeps them related
(`TauCeti.CotangentBundle.cotangentRel_vectorBundleTranslateDiffeomorph_mpullback`). This is how a
change of one-form upstairs by a pullback becomes a fibre translation downstairs, as in the change
of connection for cotangent reduction at a nonzero value.

## Main results

* `TauCeti.CotangentBundle.cotangentRel_vectorBundleTranslateDiffeomorph_mpullback`: translation
  by `ρ^* γ` and by `γ` preserves the cotangent relation of `ρ`.
-/

public section

noncomputable section

open Bundle Manifold
open scoped ContDiff Manifold

namespace TauCeti.CotangentBundle

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {Q : Type*} [TopologicalSpace Q] [ChartedSpace H Q]
  [IsManifold I ∞ Q]
  {EB HB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB] [TopologicalSpace HB]
  {IB : ModelWithCorners ℝ EB HB} {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  [IsManifold IB ∞ B] {ρ : Q → B}

/-- **Translation preserves the cotangent relation.** If `(q, p)` is related to `(ρ q, p')`, that
is `p = p' ∘ dρ_q`, then translating `p` by the pullback `ρ^* γ` of a one-form `γ` on `B` and `p'`
by `γ` keeps them related. -/
theorem cotangentRel_vectorBundleTranslateDiffeomorph_mpullback
    (hρs : ContMDiff I IB ∞ ρ) (γ : SmoothForm IB B ℝ 1) {y : CotangentBundle I Q}
    {w : CotangentBundle IB B} (h : cotangentRel I IB ρ y w) :
    cotangentRel I IB ρ (vectorBundleTranslateDiffeomorph
        (SmoothForm.degreeOneEquiv (SmoothForm.mpullback ρ hρs γ))
        (SmoothForm.degreeOneEquiv (SmoothForm.mpullback ρ hρs γ)).contMDiff y)
      (vectorBundleTranslateDiffeomorph (SmoothForm.degreeOneEquiv γ)
        (SmoothForm.degreeOneEquiv γ).contMDiff w) := by
  obtain ⟨q, p⟩ := y
  obtain ⟨b, p'⟩ := w
  obtain rfl : ρ q = b := cotangentRel_proj h
  rw [cotangentRel_mk_iff] at h
  rw [vectorBundleTranslateDiffeomorph_apply, vectorBundleTranslateDiffeomorph_apply,
    cotangentRel_mk_iff, h]
  ext v
  simp [SmoothForm.degreeOneEquiv_apply_apply_vec, Matrix.vec_single_eq_const]

end TauCeti.CotangentBundle
