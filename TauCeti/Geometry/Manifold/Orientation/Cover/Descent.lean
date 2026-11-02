/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Involution
public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.LocalDiffeomorph
public import TauCeti.Geometry.Manifold.Orientation.Cover.Smooth

/-!
# Descent of forms along the orientation double cover

The projection of the orientation double cover of a manifold `M` is a local diffeomorphism whose
fibre through a point `p` is `{p, deck p}`, where `deck` is the orientation-reversing deck
involution. Hence a form on the cover is the pullback of a form on `M` exactly when it is
invariant under `deck`, and for smooth forms the form on `M` can be taken smooth. In particular the
deck-invariant part `(φ + deck⁎φ) / 2` of any form `φ` on the cover descends to `M`.

Since the cover is always orientable, this is how statements about forms on nonorientable
manifolds are reduced to the orientable case: average a form on the cover over the deck
involution, then descend it. This is the descent step in the standard proof that the top
compactly supported de Rham cohomology of a connected nonorientable manifold vanishes.

## Main results

* `TauCeti.Manifold.OrientationCover.exists_mpullback_proj_eq_iff`: a form on the orientation
  cover is a pullback from `M` if and only if it is invariant under the deck involution.
* `TauCeti.Manifold.OrientationCover.exists_smoothForm_mpullback_proj_eq_iff`: the same for
  smooth forms, with a smooth form on `M`.
* `TauCeti.Manifold.OrientationCover.exists_mpullback_proj_eq_invariantPart`: the deck-invariant
  part of every form on the cover descends to `M`.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, second edition, Graduate Texts in
  Mathematics 218, Springer, 2013, Chapter 15, "The Orientation Covering", and the proof of
  Theorem 17.34.
-/

public section

noncomputable section

open scoped ContDiff Manifold

namespace TauCeti.Manifold.OrientationCover

variable {E H M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  {k : ℕ}

/-- The two points of the orientation cover over a point of `M` are related by the deck
involution. -/
private theorem eq_or_exists_deck_eq [IsManifold I 1 M] {p q : OrientationCover I M}
    (h : p.proj = q.proj) :
    p = q ∨ ∃ _ : Unit, VectorBundleOrientationCover.deck p = q :=
  (VectorBundleOrientationCover.eq_or_eq_deck (Fintype.card_fin _) h.symm).imp Eq.symm
    fun h' ↦ ⟨(), h'.symm⟩

section Rough

variable [AddCommGroup F] [Module ℝ F] [TopologicalSpace F] [IsManifold I 1 M]

/-- **Descent along the orientation cover.** A form on the orientation double cover of `M` is
the pullback of a form on `M` if and only if it is invariant under the deck involution. -/
theorem exists_mpullback_proj_eq_iff {φ : RoughForm I (OrientationCover I M) F k} :
    (∃ ψ : RoughForm I M F k, mpullback I I VectorBundleOrientationCover.proj ψ = φ) ↔
      mpullback I I VectorBundleOrientationCover.deck φ = φ := by
  simpa only [forall_const] using
    (isLocalDiffeomorph_proj (I := I) (M := M) (n := 1)).exists_mpullback_eq_iff one_ne_zero
      (σ := fun _ : Unit ↦ VectorBundleOrientationCover.deck)
      (fun _ ↦ contMDiff_deck.mdifferentiable one_ne_zero)
      (fun _ ↦ funext VectorBundleOrientationCover.proj_deck) fun _ _ ↦ eq_or_exists_deck_eq

/-- The deck-invariant part `(φ + deck⁎φ) / 2` of a form `φ` on the orientation double cover of
`M` is the pullback of a form on `M`. -/
theorem exists_mpullback_proj_eq_invariantPart [IsTopologicalAddGroup F]
    [ContinuousConstSMul ℝ F] (φ : RoughForm I (OrientationCover I M) F k) :
    ∃ ψ : RoughForm I M F k, mpullback I I VectorBundleOrientationCover.proj ψ =
      invariantPart VectorBundleOrientationCover.deck φ :=
  exists_mpullback_proj_eq_iff.mpr <| mpullback_invariantPart
    VectorBundleOrientationCover.deck_deck (contMDiff_deck.mdifferentiable one_ne_zero) φ

end Rough

/-- **Descent of smooth forms along the orientation cover.** A smooth form on the orientation
double cover of `M` is the pullback of a smooth form on `M` if and only if it is invariant under
the deck involution. -/
theorem exists_smoothForm_mpullback_proj_eq_iff [NormedAddCommGroup F] [NormedSpace ℝ F]
    [IsManifold I ∞ M] {φ : SmoothForm I (OrientationCover I M) F k} :
    (∃ ψ : SmoothForm I M F k,
        SmoothForm.mpullback VectorBundleOrientationCover.proj contMDiff_proj ψ = φ) ↔
      SmoothForm.mpullback VectorBundleOrientationCover.deck contMDiff_deck φ = φ := by
  simpa only [forall_const] using
    (isLocalDiffeomorph_proj (I := I) (M := M) (n := ∞)).exists_smoothForm_mpullback_eq_iff
      (VectorBundleOrientationCover.surjective_proj (Fintype.card_fin _))
      (σ := fun _ : Unit ↦ VectorBundleOrientationCover.deck) (fun _ ↦ contMDiff_deck)
      (fun _ ↦ funext VectorBundleOrientationCover.proj_deck) fun _ _ ↦ eq_or_exists_deck_eq

end TauCeti.Manifold.OrientationCover
