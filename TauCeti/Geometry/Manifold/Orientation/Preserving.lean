/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Orientation.Basic
public import TauCeti.Geometry.Manifold.IsManifold.Basic
public import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions

/-!
# Orientation behavior of manifold maps

This file records the pointwise interface for a map to preserve or reverse manifold orientations.
The differential is required to be represented by a continuous linear equivalence, and its induced
orientation must agree with the target orientation (or its opposite). These predicates are the local
input for pullback orientations and orientation-sensitive integration.
-/

public section

noncomputable section

open scoped Manifold Topology

namespace TauCeti.Manifold.Orientation

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [FiniteDimensional ℝ E]
  {E' H' M' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  [TopologicalSpace M'] [ChartedSpace H' M'] [FiniteDimensional ℝ E']
  {E'' H'' M'' : Type*} [NormedAddCommGroup E''] [NormedSpace ℝ E'']
  [TopologicalSpace H''] {I'' : ModelWithCorners ℝ E'' H''}
  [TopologicalSpace M''] [ChartedSpace H'' M''] [FiniteDimensional ℝ E'']
  {ι : Type*} [Fintype ι]

/-- A map preserves orientations at `x` when its manifold derivative is an equivalence that maps
`o`'s tangent orientation at `x` to `o'`'s tangent orientation at `f x`. -/
def IsOrientationPreservingAt [IsManifold I 1 M] [IsManifold I' 1 M']
    (o : Manifold.Orientation I M ι) (o' : Manifold.Orientation I' M' ι)
    (f : M → M') (x : M) : Prop :=
  ∃ e : TangentSpace I x ≃L[ℝ] TangentSpace I' (f x),
    (e : TangentSpace I x →L[ℝ] TangentSpace I' (f x)) = mfderiv I I' f x ∧
      _root_.Orientation.map ι e.toLinearEquiv (o.orientationAt x) = o'.orientationAt (f x)

/-- Unfold `IsOrientationPreservingAt` into its derivative witness and orientation equation. -/
theorem isOrientationPreservingAt_iff [IsManifold I 1 M] [IsManifold I' 1 M']
    (o : Manifold.Orientation I M ι) (o' : Manifold.Orientation I' M' ι)
    (f : M → M') (x : M) :
    IsOrientationPreservingAt o o' f x ↔
      ∃ e : TangentSpace I x ≃L[ℝ] TangentSpace I' (f x),
        (e : TangentSpace I x →L[ℝ] TangentSpace I' (f x)) = mfderiv I I' f x ∧
          _root_.Orientation.map ι e.toLinearEquiv (o.orientationAt x) = o'.orientationAt (f x) :=
  Iff.rfl

/-- A map reverses orientations at `x` when its manifold derivative is an equivalence that maps
`o`'s tangent orientation at `x` to the opposite of `o'`'s tangent orientation at `f x`. -/
def IsOrientationReversingAt [IsManifold I 1 M] [IsManifold I' 1 M']
    (o : Manifold.Orientation I M ι) (o' : Manifold.Orientation I' M' ι)
    (f : M → M') (x : M) : Prop :=
  ∃ e : TangentSpace I x ≃L[ℝ] TangentSpace I' (f x),
    (e : TangentSpace I x →L[ℝ] TangentSpace I' (f x)) = mfderiv I I' f x ∧
      _root_.Orientation.map ι e.toLinearEquiv (o.orientationAt x) = -(o'.orientationAt (f x))

/-- Unfold `IsOrientationReversingAt` into its derivative witness and orientation equation. -/
theorem isOrientationReversingAt_iff [IsManifold I 1 M] [IsManifold I' 1 M']
    (o : Manifold.Orientation I M ι) (o' : Manifold.Orientation I' M' ι)
    (f : M → M') (x : M) :
    IsOrientationReversingAt o o' f x ↔
      ∃ e : TangentSpace I x ≃L[ℝ] TangentSpace I' (f x),
        (e : TangentSpace I x →L[ℝ] TangentSpace I' (f x)) = mfderiv I I' f x ∧
          _root_.Orientation.map ι e.toLinearEquiv (o.orientationAt x) =
            -(o'.orientationAt (f x)) :=
  Iff.rfl

/-- Given a continuous linear equivalence representing the derivative, preservation is exactly its
orientation equation. -/
theorem isOrientationPreservingAt_iff_of_coe_eq [IsManifold I 1 M] [IsManifold I' 1 M']
    (o : Manifold.Orientation I M ι) (o' : Manifold.Orientation I' M' ι)
    (f : M → M') (x : M) (e : TangentSpace I x ≃L[ℝ] TangentSpace I' (f x))
    (he : (e : TangentSpace I x →L[ℝ] TangentSpace I' (f x)) = mfderiv I I' f x) :
    IsOrientationPreservingAt o o' f x ↔
      _root_.Orientation.map ι e.toLinearEquiv (o.orientationAt x) = o'.orientationAt (f x) := by
  constructor
  · rintro ⟨e', he', h⟩
    have heq : e' = e := ContinuousLinearEquiv.coe_injective (he'.trans he.symm)
    simpa [heq] using h
  · intro h
    exact ⟨e, he, h⟩

/-- Given a continuous linear equivalence representing the derivative, reversal is exactly its
orientation equation with the opposite target orientation. -/
theorem isOrientationReversingAt_iff_of_coe_eq [IsManifold I 1 M] [IsManifold I' 1 M']
    (o : Manifold.Orientation I M ι) (o' : Manifold.Orientation I' M' ι)
    (f : M → M') (x : M) (e : TangentSpace I x ≃L[ℝ] TangentSpace I' (f x))
    (he : (e : TangentSpace I x →L[ℝ] TangentSpace I' (f x)) = mfderiv I I' f x) :
    IsOrientationReversingAt o o' f x ↔
      _root_.Orientation.map ι e.toLinearEquiv (o.orientationAt x) =
        -(o'.orientationAt (f x)) := by
  constructor
  · rintro ⟨e', he', h⟩
    have heq : e' = e := ContinuousLinearEquiv.coe_injective (he'.trans he.symm)
    simpa [heq] using h
  · intro h
    exact ⟨e, he, h⟩

/-- Given a continuous linear equivalence representing the derivative, every map is either
orientation-preserving or orientation-reversing at the point. -/
theorem isOrientationPreservingAt_or_isOrientationReversingAt [IsManifold I 1 M]
    [IsManifold I' 1 M'] (o : Manifold.Orientation I M ι) (o' : Manifold.Orientation I' M' ι)
    (f : M → M') (x : M) (e : TangentSpace I x ≃L[ℝ] TangentSpace I' (f x))
    (he : (e : TangentSpace I x →L[ℝ] TangentSpace I' (f x)) = mfderiv I I' f x) :
    IsOrientationPreservingAt o o' f x ∨ IsOrientationReversingAt o o' f x := by
  have hcard : Fintype.card ι = Module.finrank ℝ (TangentSpace I' (f x)) := by
    simpa only [TauCeti.finrank_tangentSpace] using o'.card_eq
  rcases _root_.Orientation.eq_or_eq_neg
    (_root_.Orientation.map ι e.toLinearEquiv (o.orientationAt x))
    (o'.orientationAt (f x)) hcard with h | h
  · exact .inl ((isOrientationPreservingAt_iff_of_coe_eq o o' f x e he).2 h)
  · exact .inr ((isOrientationReversingAt_iff_of_coe_eq o o' f x e he).2 h)

/-- An orientation-preserving map has an invertible manifold derivative. -/
theorem IsOrientationPreservingAt.isInvertible_mfderiv [IsManifold I 1 M]
    [IsManifold I' 1 M'] {o : Manifold.Orientation I M ι} {o' : Manifold.Orientation I' M' ι}
    {f : M → M'} {x : M} (h : IsOrientationPreservingAt o o' f x) :
    (mfderiv I I' f x).IsInvertible := by
  obtain ⟨e, he, _⟩ := h
  exact ⟨e, he⟩

/-- An orientation-reversing map has an invertible manifold derivative. -/
theorem IsOrientationReversingAt.isInvertible_mfderiv [IsManifold I 1 M]
    [IsManifold I' 1 M'] {o : Manifold.Orientation I M ι} {o' : Manifold.Orientation I' M' ι}
    {f : M → M'} {x : M} (h : IsOrientationReversingAt o o' f x) :
    (mfderiv I I' f x).IsInvertible := by
  obtain ⟨e, he, _⟩ := h
  exact ⟨e, he⟩

/-- Negating the source orientation exchanges preservation and reversal. -/
@[simp] theorem isOrientationPreservingAt_neg_left
    [IsManifold I 1 M] [IsManifold I' 1 M']
    (o : Manifold.Orientation I M ι) (o' : Manifold.Orientation I' M' ι)
    (f : M → M') (x : M) :
    IsOrientationPreservingAt (-o) o' f x ↔ IsOrientationReversingAt o o' f x := by
  constructor
  · rintro ⟨e, he, h⟩
    refine ⟨e, he, ?_⟩
    rw [orientationAt_neg, _root_.Orientation.map_neg] at h
    have hh := congrArg Neg.neg h
    exact (neg_neg _).symm.trans hh
  · rintro ⟨e, he, h⟩
    refine ⟨e, he, ?_⟩
    rw [orientationAt_neg, _root_.Orientation.map_neg]
    have hh := congrArg Neg.neg h
    exact hh.trans (_root_.neg_neg (o'.orientationAt (f x)))

/-- Negating the target orientation exchanges preservation and reversal. -/
@[simp] theorem isOrientationPreservingAt_neg_right [IsManifold I 1 M] [IsManifold I' 1 M']
    (o : Manifold.Orientation I M ι) (o' : Manifold.Orientation I' M' ι)
    (f : M → M') (x : M) :
    IsOrientationPreservingAt o (-o') f x ↔ IsOrientationReversingAt o o' f x := by
  constructor
  · rintro ⟨e, he, h⟩
    refine ⟨e, he, ?_⟩
    rw [orientationAt_neg] at h
    exact h
  · rintro ⟨e, he, h⟩
    refine ⟨e, he, ?_⟩
    rw [orientationAt_neg]
    exact h

/-- Negating the source orientation exchanges reversal and preservation. -/
@[simp] theorem isOrientationReversingAt_neg_left [IsManifold I 1 M] [IsManifold I' 1 M']
    (o : Manifold.Orientation I M ι) (o' : Manifold.Orientation I' M' ι)
    (f : M → M') (x : M) :
    IsOrientationReversingAt (-o) o' f x ↔ IsOrientationPreservingAt o o' f x := by
  rw [← isOrientationPreservingAt_neg_left, neg_neg]

/-- Negating the target orientation exchanges reversal and preservation. -/
@[simp] theorem isOrientationReversingAt_neg_right [IsManifold I 1 M] [IsManifold I' 1 M']
    (o : Manifold.Orientation I M ι) (o' : Manifold.Orientation I' M' ι)
    (f : M → M') (x : M) :
    IsOrientationReversingAt o (-o') f x ↔ IsOrientationPreservingAt o o' f x := by
  rw [← isOrientationPreservingAt_neg_right, neg_neg]

/-- A map cannot preserve and reverse the same pair of orientations at one point. -/
theorem not_isOrientationPreservingAt_and_isOrientationReversingAt
    [IsManifold I 1 M] [IsManifold I' 1 M']
    (o : Manifold.Orientation I M ι) (o' : Manifold.Orientation I' M' ι)
    (f : M → M') (x : M) :
    ¬(IsOrientationPreservingAt o o' f x ∧ IsOrientationReversingAt o o' f x) := by
  rintro ⟨⟨e, he, h⟩, hrev⟩
  exact Module.Ray.ne_neg_self _
    (h.symm.trans ((isOrientationReversingAt_iff_of_coe_eq o o' f x e he).mp hrev))

/-- The identity map preserves every manifold orientation. -/
@[simp] theorem isOrientationPreservingAt_id [IsManifold I 1 M]
    (o : Manifold.Orientation I M ι) (x : M) :
    IsOrientationPreservingAt (I := I) (I' := I) (M' := M) o o id x := by
  refine ⟨ContinuousLinearEquiv.refl ℝ _, ?_, ?_⟩
  · rw [ContinuousLinearEquiv.coe_refl, mfderiv_id]
  · /- The continuous and plain linear equivalence wrappers share this definitional equality,
      which lets the orientation map use its identity lemma. -/
    have h_refl :
        (ContinuousLinearEquiv.refl ℝ (TangentSpace I x)).toLinearEquiv =
          LinearEquiv.refl ℝ (TangentSpace I x) := rfl
    rw [h_refl, _root_.Orientation.map_refl]
    simp only [Equiv.refl_apply, id_eq]

/-- The identity map reverses an orientation when its target is given the opposite orientation. -/
theorem isOrientationReversingAt_id_neg [IsManifold I 1 M]
    (o : Manifold.Orientation I M ι) (x : M) :
    IsOrientationReversingAt (I := I) (I' := I) (M' := M) o (-o) id x := by
  simp

/-- The composition of two orientation-preserving maps preserves orientations at a point. -/
theorem IsOrientationPreservingAt.comp [IsManifold I 1 M] [IsManifold I' 1 M']
    [IsManifold I'' 1 M''] {o : Manifold.Orientation I M ι}
    {o' : Manifold.Orientation I' M' ι} {o'' : Manifold.Orientation I'' M'' ι}
    {f : M → M'} {g : M' → M''} {x : M}
    (hgg : IsOrientationPreservingAt o' o'' g (f x))
    (hgf : IsOrientationPreservingAt o o' f x) :
    IsOrientationPreservingAt o o'' (g ∘ f) x := by
  obtain ⟨e, he, h⟩ := hgf
  obtain ⟨e', he', h'⟩ := hgg
  have hf := mdifferentiableAt_of_isInvertible_mfderiv ⟨e, he⟩
  have hg := mdifferentiableAt_of_isInvertible_mfderiv ⟨e', he'⟩
  refine ⟨e.trans e', ?_, ?_⟩
  · rw [mfderiv_comp (x := x) hg hf, ← he', ← he]
    exact ContinuousLinearEquiv.comp_coe e e'
  · rw [ContinuousLinearEquiv.trans_toLinearEquiv, _root_.Orientation.map_trans, h, h']
    simp only [Function.comp_apply]

/-- The composition of two orientation-reversing maps preserves orientations at a point. -/
theorem IsOrientationReversingAt.comp [IsManifold I 1 M] [IsManifold I' 1 M']
    [IsManifold I'' 1 M''] {o : Manifold.Orientation I M ι}
    {o' : Manifold.Orientation I' M' ι} {o'' : Manifold.Orientation I'' M'' ι}
    {f : M → M'} {g : M' → M''} {x : M}
    (hgg : IsOrientationReversingAt o' o'' g (f x))
    (hgf : IsOrientationReversingAt o o' f x) :
    IsOrientationPreservingAt o o'' (g ∘ f) x := by
  have hgg' : IsOrientationPreservingAt (-o') o'' g (f x) :=
    (isOrientationPreservingAt_neg_left o' o'' g (f x)).2 hgg
  have hgf' : IsOrientationPreservingAt o (-o') f x :=
    (isOrientationPreservingAt_neg_right o o' f x).2 hgf
  exact IsOrientationPreservingAt.comp hgg' hgf'

/-- Composing an orientation-preserving map after an orientation-reversing map reverses
orientations at a point. -/
theorem IsOrientationPreservingAt.comp_reversing [IsManifold I 1 M] [IsManifold I' 1 M']
    [IsManifold I'' 1 M''] {o : Manifold.Orientation I M ι}
    {o' : Manifold.Orientation I' M' ι} {o'' : Manifold.Orientation I'' M'' ι}
    {f : M → M'} {g : M' → M''} {x : M}
    (hgg : IsOrientationPreservingAt o' o'' g (f x))
    (hgf : IsOrientationReversingAt o o' f x) :
    IsOrientationReversingAt o o'' (g ∘ f) x := by
  have hgg' : IsOrientationPreservingAt (-o') (-o'') g (f x) := by
    simpa only [isOrientationPreservingAt_neg_left, isOrientationReversingAt_neg_right] using hgg
  have hgf' : IsOrientationPreservingAt o (-o') f x :=
    (isOrientationPreservingAt_neg_right o o' f x).2 hgf
  have h := IsOrientationPreservingAt.comp hgg' hgf'
  exact (isOrientationPreservingAt_neg_right o o'' (g ∘ f) x).1 h

/-- Composing an orientation-reversing map after an orientation-preserving map reverses
orientations at a point. -/
theorem IsOrientationReversingAt.comp_preserving [IsManifold I 1 M] [IsManifold I' 1 M']
    [IsManifold I'' 1 M''] {o : Manifold.Orientation I M ι}
    {o' : Manifold.Orientation I' M' ι} {o'' : Manifold.Orientation I'' M'' ι}
    {f : M → M'} {g : M' → M''} {x : M}
    (hgg : IsOrientationReversingAt o' o'' g (f x))
    (hgf : IsOrientationPreservingAt o o' f x) :
    IsOrientationReversingAt o o'' (g ∘ f) x := by
  have hgg' : IsOrientationPreservingAt (-o') o'' g (f x) :=
    (isOrientationPreservingAt_neg_left o' o'' g (f x)).2 hgg
  have hgf' : IsOrientationPreservingAt (-o) (-o') f x := by
    simpa only [isOrientationPreservingAt_neg_left, isOrientationReversingAt_neg_right] using hgf
  have h := IsOrientationPreservingAt.comp hgg' hgf'
  exact (isOrientationPreservingAt_neg_left o o'' (g ∘ f) x).1 h

end TauCeti.Manifold.Orientation
