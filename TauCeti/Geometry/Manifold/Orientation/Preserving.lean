/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Orientation.Basic
public import TauCeti.Geometry.Manifold.IsManifold.Basic
public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
public import TauCeti.Geometry.Diffeomorphism.Group
import TauCeti.Geometry.Manifold.MFDeriv.Chart.Basic
import TauCeti.Geometry.Manifold.MFDeriv.IsInvertible
import TauCeti.Topology.Algebra.Module.Determinant

/-!
# Orientation behavior of manifold maps

This file records the pointwise interface for a map to preserve or reverse manifold orientations.
The differential is required to be represented by a continuous linear equivalence, and its induced
orientation must agree with the target orientation (or its opposite). These predicates are the local
input for pullback orientations and orientation-sensitive integration. A local diffeomorphism at a
point either preserves or reverses orientations there
(`IsLocalDiffeomorphAt.isOrientationPreservingAt_or_isOrientationReversingAt`).
The inverse of a diffeomorphism preserves orientation wherever the diffeomorphism does
(`IsOrientationPreservingAt.diffeomorph_symm`), so a diffeomorphism of `M` preserving an
orientation everywhere has all its integer powers orientation preserving
(`isOrientationPreservingAt_zpow`).

For orientation lifts whose model orientations correspond under a linear equivalence of the model
spaces, the chart signs of the lifts compensate the sign of the coordinate Jacobian of an
orientation-preserving map, read in the source model through that equivalence.

For one-dimensional manifolds modelled on `ℝ` whose orientations are the standard orientation of
`ℝ` at the relevant points, `isOrientationPreservingAt_of_orientationAt_eq` and
`isOrientationReversingAt_of_orientationAt_eq` reduce preservation and reversal to the sign of the
real number by which the derivative multiplies. In particular, translations of `ℝ` preserve its
standard orientation (`isOrientationPreservingAt_add_const`).

On the model space `E` itself, every orientation is constant once the tangent spaces are identified
with `E` (`orientationAt_eq_orientationAt`), so a continuous linear automorphism of `E` preserves
or reverses every orientation of `E` according to the sign of its determinant
(`isOrientationPreservingAt_of_det_pos`, `isOrientationReversingAt_of_det_neg`). In particular
precomposing with an automorphism of negative determinant exchanges preservation and reversal
(`isOrientationPreservingAt_comp_of_det_neg`, `isOrientationReversingAt_comp_of_det_neg`).
More generally, a map with negative derivative determinant reverses orientations at that point
(`isOrientationReversingAt_of_det_fderiv_neg`).

If the derivative carries a tangent basis `b` onto a basis `b'`, then, whether `b` is positively
or negatively oriented, preservation (reversal) means that `b` and `b'` have equal (opposite)
orientation signs (`isOrientationPreservingAt_iff_of_basis`,
`isOrientationReversingAt_iff_of_basis`).
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

/-- Orientation preservation of a map with invertible derivative at `x`, read in the tangent
trivializations at `x` and `b`: the continuous equivalence `T` induced by the derivative `D`
carries the orientation of `x` to that of `g x` exactly when `g` preserves orientation at `x`. -/
theorem isOrientationPreservingAt_iff_map_eq [IsManifold I 1 M] [IsManifold I' 1 M']
    (o : Manifold.Orientation I M ι) (o' : Manifold.Orientation I' M' ι) (g : M → M') (x : M)
    (b : M') (D : TangentSpace I x ≃L[ℝ] TangentSpace I' (g x))
    (hDc : (D : TangentSpace I x →L[ℝ] TangentSpace I' (g x)) = mfderiv I I' g x)
    (hx : x ∈ (trivializationAt E (TangentSpace I) x).baseSet)
    (hp : g x ∈ (trivializationAt E' (TangentSpace I') b).baseSet) :
    IsOrientationPreservingAt o o' g x ↔
      _root_.Orientation.map ι
          (((((trivializationAt E (TangentSpace I) x).continuousLinearEquivAt ℝ x hx).symm.trans
            D).trans ((trivializationAt E' (TangentSpace I') b).continuousLinearEquivAt ℝ (g x)
              hp)).toLinearEquiv)
          ((trivializationAt E (TangentSpace I) x).mapOrientation ι hx (o.orientationAt x)) =
        (trivializationAt E' (TangentSpace I') b).mapOrientation ι hp (o'.orientationAt (g x)) := by
  rw [isOrientationPreservingAt_iff_of_coe_eq o o' _ x D hDc]
  have hmap : _root_.Orientation.map ι
      (((((trivializationAt E (TangentSpace I) x).continuousLinearEquivAt ℝ x hx).symm.trans
        D).trans ((trivializationAt E' (TangentSpace I') b).continuousLinearEquivAt ℝ (g x)
          hp)).toLinearEquiv)
      ((trivializationAt E (TangentSpace I) x).mapOrientation ι hx (o.orientationAt x)) =
      (trivializationAt E' (TangentSpace I') b).mapOrientation ι hp
        (_root_.Orientation.map ι D.toLinearEquiv (o.orientationAt x)) := by
    -- A trivialization's continuous equivalence is the continuous wrapper of its
    -- linear equivalence; identify the wrappers before cancelling orientation transport.
    have he : ((trivializationAt E (TangentSpace I) x).continuousLinearEquivAt ℝ x hx
        ).toLinearEquiv = (trivializationAt E (TangentSpace I) x).linearEquivAt ℝ x hx := rfl
    have he' : ((trivializationAt E' (TangentSpace I') b).continuousLinearEquivAt ℝ (g x) hp
        ).toLinearEquiv = (trivializationAt E' (TangentSpace I') b).linearEquivAt ℝ (g x) hp := rfl
    simp only [ContinuousLinearEquiv.trans_toLinearEquiv,
      _root_.Orientation.map_trans, Bundle.Trivialization.mapOrientation_apply,
      ContinuousLinearEquiv.toLinearEquiv_symm, he, he',
      ← _root_.Orientation.map_symm, Equiv.symm_apply_apply]
  rw [hmap]
  exact ((trivializationAt E' (TangentSpace I') b).mapOrientation ι hp).injective.eq_iff.symm

/-- If the derivative at `x` carries a basis `b` of the tangent space at `x` to the basis `b'` of
the tangent space at `f x`, then `f` preserves orientations at `x` exactly when `b` and `b'` are
both positively or both negatively oriented. -/
theorem isOrientationPreservingAt_iff_of_basis [IsManifold I 1 M] [IsManifold I' 1 M']
    [DecidableEq ι] {o : Manifold.Orientation I M ι} {o' : Manifold.Orientation I' M' ι}
    {f : M → M'} {x : M} (b : Module.Basis ι ℝ (TangentSpace I x))
    (b' : Module.Basis ι ℝ (TangentSpace I' (f x)))
    (hbb' : ∀ i, mfderiv I I' f x (b i) = b' i) :
    IsOrientationPreservingAt o o' f x ↔
      (b.orientation = o.orientationAt x ↔ b'.orientation = o'.orientationAt (f x)) := by
  obtain ⟨e, he, hbe⟩ := exists_coe_eq_mfderiv_of_basis b b' hbb'
  have hmap : _root_.Orientation.map ι e.toLinearEquiv b.orientation = b'.orientation := by
    rw [← Module.Basis.orientation_map, hbe]
  rw [isOrientationPreservingAt_iff_of_coe_eq o o' f x e he]
  rcases (o.orientationAt x).eq_or_eq_neg b.orientation (o.finrank_tangentSpace_eq x).symm with
    h | h
  · rw [h, hmap, iff_true_left rfl]
  · rw [h, _root_.Orientation.map_neg, hmap,
      neg_eq_iff_eq_neg (G := _root_.Orientation ℝ (TangentSpace I' (f x)) ι),
      iff_false_left (Module.Ray.ne_neg_self _),
      ← _root_.Orientation.ne_iff_eq_neg _ _ (o'.finrank_tangentSpace_eq (f x)).symm, Ne]

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

/-- A `C^n` local diffeomorphism at `x`, for `n ≠ 0`, either preserves or reverses orientations at
`x`. -/
theorem _root_.IsLocalDiffeomorphAt.isOrientationPreservingAt_or_isOrientationReversingAt
    [IsManifold I 1 M] [IsManifold I' 1 M'] {n : WithTop ℕ∞} {f : M → M'} {x : M}
    (hf : IsLocalDiffeomorphAt I I' n f x) (hn : n ≠ 0) (o : Manifold.Orientation I M ι)
    (o' : Manifold.Orientation I' M' ι) :
    IsOrientationPreservingAt o o' f x ∨ IsOrientationReversingAt o o' f x :=
  TauCeti.Manifold.Orientation.isOrientationPreservingAt_or_isOrientationReversingAt o o' f x
    (hf.mfderivToContinuousLinearEquiv hn) (hf.mfderivToContinuousLinearEquiv_coe hn)

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

/-- If the derivative at `x` carries a basis `b` of the tangent space at `x` to the basis `b'` of
the tangent space at `f x`, then `f` reverses orientations at `x` exactly when `b'` is negatively
oriented if `b` is positively oriented, and positively oriented if `b` is negatively oriented. -/
theorem isOrientationReversingAt_iff_of_basis [IsManifold I 1 M] [IsManifold I' 1 M']
    [DecidableEq ι] {o : Manifold.Orientation I M ι} {o' : Manifold.Orientation I' M' ι}
    {f : M → M'} {x : M} (b : Module.Basis ι ℝ (TangentSpace I x))
    (b' : Module.Basis ι ℝ (TangentSpace I' (f x)))
    (hbb' : ∀ i, mfderiv I I' f x (b i) = b' i) :
    IsOrientationReversingAt o o' f x ↔
      (b.orientation = o.orientationAt x ↔ b'.orientation = -o'.orientationAt (f x)) := by
  rw [← isOrientationPreservingAt_neg_right, isOrientationPreservingAt_iff_of_basis b b' hbb',
    orientationAt_neg]

/-- A map cannot preserve and reverse the same pair of orientations at one point. -/
theorem not_isOrientationPreservingAt_and_isOrientationReversingAt
    [IsManifold I 1 M] [IsManifold I' 1 M']
    (o : Manifold.Orientation I M ι) (o' : Manifold.Orientation I' M' ι)
    (f : M → M') (x : M) :
    ¬(IsOrientationPreservingAt o o' f x ∧ IsOrientationReversingAt o o' f x) := by
  rintro ⟨⟨e, he, h⟩, hrev⟩
  exact Module.Ray.ne_neg_self _
    (h.symm.trans ((isOrientationReversingAt_iff_of_coe_eq o o' f x e he).mp hrev))

/-- A self-map fixing `x` whose derivative at `x` is the identity preserves every manifold
orientation at `x`. -/
theorem isOrientationPreservingAt_of_apply_eq_of_mfderiv_eq_id [IsManifold I 1 M]
    (o : Manifold.Orientation I M ι) {f : M → M} {x : M} (hx : f x = x)
    (hd : mfderiv I I f x = ContinuousLinearMap.id ℝ (TangentSpace I x)) :
    IsOrientationPreservingAt o o f x := by
  refine ⟨ContinuousLinearEquiv.refl ℝ _, hd.symm, ?_⟩
  -- The continuous and plain linear equivalence wrappers share this definitional equality,
  -- which lets the orientation map use its identity lemma.
  have h_refl :
      (ContinuousLinearEquiv.refl ℝ (TangentSpace I x)).toLinearEquiv =
        LinearEquiv.refl ℝ (TangentSpace I x) := rfl
  /- The orientation at `f x` lives on the tangent space at `f x`; generalize the point to
    substitute `x` for it along `hx`. -/
  have key (y : M) (hy : y = x) : _root_.Orientation.map ι
      (ContinuousLinearEquiv.refl ℝ (TangentSpace I x)).toLinearEquiv (o.orientationAt x) =
        o.orientationAt y := by
    subst hy
    rw [h_refl, _root_.Orientation.map_refl, Equiv.refl_apply]
  exact key _ hx

/-- The identity map preserves every manifold orientation. -/
@[simp] theorem isOrientationPreservingAt_id [IsManifold I 1 M]
    (o : Manifold.Orientation I M ι) (x : M) :
    IsOrientationPreservingAt (I := I) (I' := I) (M' := M) o o id x :=
  isOrientationPreservingAt_of_apply_eq_of_mfderiv_eq_id o rfl mfderiv_id

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

/-- Two orientations of `M'` from which a map preserves orientation at `x`, from the same
orientation of `M`, agree at `f x`. -/
theorem IsOrientationPreservingAt.orientationAt_eq [IsManifold I 1 M] [IsManifold I' 1 M']
    {o : Manifold.Orientation I M ι} {o' o'' : Manifold.Orientation I' M' ι} {f : M → M'}
    {x : M} (h' : IsOrientationPreservingAt o o' f x) (h'' : IsOrientationPreservingAt o o'' f x) :
    o'.orientationAt (f x) = o''.orientationAt (f x) := by
  obtain ⟨D, hD, hDo⟩ := h'
  rwa [← hDo, ← isOrientationPreservingAt_iff_of_coe_eq _ _ _ _ D hD]

/-- A differentiable map `f` preserves orientations at `x` when `g ∘ f` does and `g` preserves
orientations at `f x`. -/
theorem IsOrientationPreservingAt.of_comp [IsManifold I 1 M] [IsManifold I' 1 M']
    [IsManifold I'' 1 M''] {o : Manifold.Orientation I M ι}
    {o' : Manifold.Orientation I' M' ι} {o'' : Manifold.Orientation I'' M'' ι}
    {f : M → M'} {g : M' → M''} {x : M}
    (hgg : IsOrientationPreservingAt o' o'' g (f x))
    (hgf : IsOrientationPreservingAt o o'' (g ∘ f) x) (hf : MDifferentiableAt I I' f x) :
    IsOrientationPreservingAt o o' f x := by
  obtain ⟨e, he, h⟩ := hgf
  obtain ⟨e', he', h'⟩ := hgg
  refine ⟨e.trans e'.symm, ?_, ?_⟩
  · -- `e' ∘ mfderiv f x = mfderiv (g ∘ f) x = e`, so `mfderiv f x = e'⁻¹ ∘ e`.
    have hcomp : (e' : TangentSpace I' (f x) →L[ℝ] TangentSpace I'' (g (f x))).comp
        (mfderiv I I' f x) = (e : TangentSpace I x →L[ℝ] TangentSpace I'' ((g ∘ f) x)) := by
      rw [he', he, mfderiv_comp x (mdifferentiableAt_of_isInvertible_mfderiv ⟨e', he'⟩) hf]
    ext v
    have hv := congrArg (fun L ↦ L v) hcomp
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe] at hv
    simp [← hv]
  · rw [ContinuousLinearEquiv.trans_toLinearEquiv, _root_.Orientation.map_trans, h,
      Function.comp_apply, ← h',
      ContinuousLinearEquiv.toLinearEquiv_symm, ← _root_.Orientation.map_symm,
      Equiv.symm_apply_apply]

/-- The inverse of a `C^n` diffeomorphism `e`, `n ≠ 0`, preserves orientations at `y` when `e`
preserves them at `e.symm y`. -/
theorem IsOrientationPreservingAt.diffeomorph_symm [IsManifold I 1 M] [IsManifold I' 1 M']
    {o : Manifold.Orientation I M ι} {o' : Manifold.Orientation I' M' ι} {n : WithTop ℕ∞}
    {e : M ≃ₘ^n⟮I, I'⟯ M'} {y : M'} (h : IsOrientationPreservingAt o o' e (e.symm y))
    (hn : n ≠ 0) : IsOrientationPreservingAt o' o e.symm y := by
  refine h.of_comp ?_ (e.symm.mdifferentiable hn y)
  have hid : ⇑e ∘ ⇑e.symm = id := funext e.apply_symm_apply
  rw [hid]
  exact isOrientationPreservingAt_id o' y

/-- If a `C^n` diffeomorphism `φ` of `M`, `n ≠ 0`, preserves an orientation `o` at every point,
then so does each of its integer powers `φ ^ k`. -/
theorem isOrientationPreservingAt_zpow [IsManifold I 1 M] {o : Manifold.Orientation I M ι}
    {n : WithTop ℕ∞} {φ : M ≃ₘ^n⟮I, I⟯ M} (h : ∀ x, IsOrientationPreservingAt o o φ x)
    (hn : n ≠ 0) (k : ℤ) (x : M) : IsOrientationPreservingAt o o ⇑(φ ^ k) x := by
  induction k using Int.induction_on generalizing x with
  | zero => exact isOrientationPreservingAt_id o x
  | succ k ih =>
    rw [zpow_add_one, Diffeomorph.coe_mul]
    exact (ih (φ x)).comp (h x)
  | pred k ih =>
    rw [zpow_sub_one, Diffeomorph.coe_mul, Diffeomorph.coe_inv]
    exact (ih _).comp ((h _).diffeomorph_symm hn)

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

section RealLine

variable {N N' : Type*} [TopologicalSpace N] [ChartedSpace ℝ N] [IsManifold 𝓘(ℝ) 1 N]
  [TopologicalSpace N'] [ChartedSpace ℝ N'] [IsManifold 𝓘(ℝ) 1 N']

/-- For orientations of one-dimensional manifolds modelled on `ℝ` which are the standard
orientation of `ℝ` at `x` and at `f x`, a map whose derivative at `x` is multiplication by a
positive real number preserves orientation at `x`. -/
theorem isOrientationPreservingAt_of_orientationAt_eq
    {o : Manifold.Orientation 𝓘(ℝ) N (Fin 1)} {o' : Manifold.Orientation 𝓘(ℝ) N' (Fin 1)}
    {f : N → N'} {x : N} (ho : o.orientationAt x = (Module.Basis.singleton (Fin 1) ℝ).orientation)
    (ho' : o'.orientationAt (f x) = (Module.Basis.singleton (Fin 1) ℝ).orientation) {c : ℝ}
    (hc : 0 < c) (hf : mfderiv 𝓘(ℝ) 𝓘(ℝ) f x = c • ContinuousLinearMap.id ℝ ℝ) :
    IsOrientationPreservingAt o o' f x := by
  -- Tangent spaces of manifolds modelled on `ℝ` are `ℝ`, and the derivative is `c • id`.
  refine (isOrientationPreservingAt_iff_of_coe_eq o o' f x
    (LinearEquiv.smulOfNeZero ℝ ℝ c hc.ne').toContinuousLinearEquiv
    (hf.symm ▸ ContinuousLinearMap.ext fun _ ↦ rfl)).mpr ?_
  rw [ho, ho']
  refine (_root_.Orientation.map_eq_iff_det_pos _ _ (by simp)).mpr ?_
  -- On `ℝ`, the determinant of multiplication by `c` is `c`.
  exact hc.trans_eq ((LinearMap.det_ring (R := ℝ) _).trans (mul_one c)).symm

/-- For orientations of one-dimensional manifolds modelled on `ℝ` which are the standard
orientation of `ℝ` at `x` and at `f x`, a map whose derivative at `x` is multiplication by a
negative real number reverses orientation at `x`. -/
theorem isOrientationReversingAt_of_orientationAt_eq
    {o : Manifold.Orientation 𝓘(ℝ) N (Fin 1)} {o' : Manifold.Orientation 𝓘(ℝ) N' (Fin 1)}
    {f : N → N'} {x : N} (ho : o.orientationAt x = (Module.Basis.singleton (Fin 1) ℝ).orientation)
    (ho' : o'.orientationAt (f x) = (Module.Basis.singleton (Fin 1) ℝ).orientation) {c : ℝ}
    (hc : c < 0) (hf : mfderiv 𝓘(ℝ) 𝓘(ℝ) f x = c • ContinuousLinearMap.id ℝ ℝ) :
    IsOrientationReversingAt o o' f x := by
  -- Tangent spaces of manifolds modelled on `ℝ` are `ℝ`, and the derivative is `c • id`.
  refine (isOrientationReversingAt_iff_of_coe_eq o o' f x
    (LinearEquiv.smulOfNeZero ℝ ℝ c hc.ne).toContinuousLinearEquiv
    (hf.symm ▸ ContinuousLinearMap.ext fun _ ↦ rfl)).mpr ?_
  rw [ho, ho']
  refine (_root_.Orientation.map_eq_neg_iff_det_neg _ _ (by simp)).mpr ?_
  -- On `ℝ`, the determinant of multiplication by `c` is `c`.
  exact ((LinearMap.det_ring (R := ℝ) _).trans (mul_one c)).trans_lt hc

/-- Translations of `ℝ` preserve its standard orientation. -/
theorem isOrientationPreservingAt_add_const (a t : ℝ) :
    IsOrientationPreservingAt real real (· + a) t :=
  isOrientationPreservingAt_of_orientationAt_eq (orientationAt_real t) (orientationAt_real _)
    one_pos (by rw [one_smul]; exact ((hasFDerivAt_id t).add_const a).hasMFDerivAt.mfderiv)

end RealLine

section ModelSpace

/-- The tangent orientation at `x` of an orientation of the model space `E`, read in `E` through
the identification `NormedSpace.fromTangentSpace` of the tangent space at `x` with `E`. -/
private def modelOrientationAt (o : Manifold.Orientation 𝓘(ℝ, E) E ι) (x : E) :
    _root_.Orientation ℝ E ι :=
  _root_.Orientation.map ι (NormedSpace.fromTangentSpace x).toLinearEquiv (o.orientationAt x)

private theorem modelOrientationAt_neg (o : Manifold.Orientation 𝓘(ℝ, E) E ι) (x : E) :
    modelOrientationAt (-o) x = -modelOrientationAt o x := by
  rw [modelOrientationAt, modelOrientationAt, orientationAt_neg, _root_.Orientation.map_neg]

/-- Read in `E`, the constant model orientation is the orientation it is built from. -/
private theorem modelOrientationAt_model (o : _root_.Orientation ℝ E ι)
    (hι : Fintype.card ι = Module.finrank ℝ E) (x : E) :
    modelOrientationAt (model (I := 𝓘(ℝ, E)) o hι) x = o := by
  rw [modelOrientationAt, orientationAt_model]
  -- `NormedSpace.fromTangentSpace x` is the identity of `E`, as the tangent space is `E`.
  exact congrArg (· o) (_root_.Orientation.map_refl (R := ℝ) (M := E) ι)

/-- An orientation of the connected model space `E`, read in `E`, has the same tangent
orientation at any two points. -/
private theorem modelOrientationAt_eq (o : Manifold.Orientation 𝓘(ℝ, E) E ι) (x y : E) :
    modelOrientationAt o x = modelOrientationAt o y := by
  obtain h | h := o.eq_or_eq_neg (model (I := 𝓘(ℝ, E)) (modelOrientationAt o x) o.card_eq)
  · rw [h, modelOrientationAt_model, modelOrientationAt_model]
  · rw [h, modelOrientationAt_neg, modelOrientationAt_neg, modelOrientationAt_model,
      modelOrientationAt_model]

/-- **An orientation of the model space is constant.** An orientation of the connected model space
`E` has the same tangent orientation at any two points, the tangent spaces of `E` all being `E`. -/
theorem orientationAt_eq_orientationAt (o : Manifold.Orientation 𝓘(ℝ, E) E ι) (x y : E) :
    o.orientationAt x = o.orientationAt y :=
  -- `NormedSpace.fromTangentSpace x` and `NormedSpace.fromTangentSpace y` are both the identity
  -- of `E`, so the right side of `modelOrientationAt_eq` is also read through the former.
  (_root_.Orientation.map ι (NormedSpace.fromTangentSpace x).toLinearEquiv).injective
    (modelOrientationAt_eq o x y)

/-- The derivative of a continuous linear automorphism `L` of `E` at `x`, as an equivalence of
tangent spaces: `L` itself, read through the identifications of the tangent spaces with `E`. -/
private def tangentEquiv (L : E ≃L[ℝ] E) (x : E) :
    TangentSpace 𝓘(ℝ, E) x ≃L[ℝ] TangentSpace 𝓘(ℝ, E) (L x) :=
  ((NormedSpace.fromTangentSpace x).trans L).trans (NormedSpace.fromTangentSpace (L x)).symm

omit [FiniteDimensional ℝ E] in
private theorem coe_tangentEquiv (L : E ≃L[ℝ] E) (x : E) :
    (tangentEquiv L x : TangentSpace 𝓘(ℝ, E) x →L[ℝ] TangentSpace 𝓘(ℝ, E) (L x)) =
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) L x := by
  rw [mfderiv_eq_fderiv, L.fderiv]
  ext v
  simp [tangentEquiv]

/-- Read in `E`, the orientation carried along the derivative of `L` is the orientation carried
along `L`. -/
private theorem map_tangentEquiv (o : Manifold.Orientation 𝓘(ℝ, E) E ι) (L : E ≃L[ℝ] E)
    (x : E) :
    _root_.Orientation.map ι (NormedSpace.fromTangentSpace (L x)).toLinearEquiv
        (_root_.Orientation.map ι (tangentEquiv L x).toLinearEquiv (o.orientationAt x)) =
      _root_.Orientation.map ι L.toLinearEquiv (modelOrientationAt o x) := by
  have he : (tangentEquiv L x).toLinearEquiv.trans
      (NormedSpace.fromTangentSpace (L x)).toLinearEquiv =
        (NormedSpace.fromTangentSpace x).toLinearEquiv.trans L.toLinearEquiv := by
    ext v
    simp [tangentEquiv]
  rw [← _root_.Orientation.map_trans, he, _root_.Orientation.map_trans, modelOrientationAt]

/-- A continuous linear automorphism of `E` with positive determinant preserves every orientation
of `E`, at every point. -/
theorem isOrientationPreservingAt_of_det_pos (o : Manifold.Orientation 𝓘(ℝ, E) E ι)
    (L : E ≃L[ℝ] E) (hL : 0 < LinearMap.det (L : E →ₗ[ℝ] E)) (x : E) :
    IsOrientationPreservingAt o o L x := by
  refine (isOrientationPreservingAt_iff_of_coe_eq o o L x _ (coe_tangentEquiv L x)).2 ?_
  rw [← _root_.Orientation.map_eq_iff_det_pos (modelOrientationAt o x) L.toLinearEquiv
    o.card_eq] at hL
  -- Read both sides in `E` through the identification of the tangent space at `L x`.
  apply (_root_.Orientation.map ι (NormedSpace.fromTangentSpace (L x)).toLinearEquiv).injective
  rw [map_tangentEquiv, ← modelOrientationAt, hL, modelOrientationAt_eq o x (L x)]

/-- A continuous linear automorphism of `E` with negative determinant reverses every orientation
of `E`, at every point. -/
theorem isOrientationReversingAt_of_det_neg (o : Manifold.Orientation 𝓘(ℝ, E) E ι)
    (L : E ≃L[ℝ] E) (hL : LinearMap.det (L : E →ₗ[ℝ] E) < 0) (x : E) :
    IsOrientationReversingAt o o L x := by
  refine (isOrientationReversingAt_iff_of_coe_eq o o L x _ (coe_tangentEquiv L x)).2 ?_
  rw [← _root_.Orientation.map_eq_neg_iff_det_neg (modelOrientationAt o x) L.toLinearEquiv
    o.card_eq] at hL
  -- Read both sides in `E` through the identification of the tangent space at `L x`.
  apply (_root_.Orientation.map ι (NormedSpace.fromTangentSpace (L x)).toLinearEquiv).injective
  rw [map_tangentEquiv, _root_.Orientation.map_neg, ← modelOrientationAt, hL,
    modelOrientationAt_eq o x (L x)]

/-- **A negative Jacobian determinant reverses orientation.** A map of a finite-dimensional
real normed space with negative derivative determinant at `v` reverses every orientation there. -/
theorem isOrientationReversingAt_of_det_fderiv_neg (o : Manifold.Orientation 𝓘(ℝ, E) E ι)
    {f : E → E} {v : E} (hdet : (fderiv ℝ f v).det < 0) : IsOrientationReversingAt o o f v := by
  let D : E ≃L[ℝ] E := (fderiv ℝ f v).toContinuousLinearEquivOfDetNeZero hdet.ne
  refine (isOrientationReversingAt_iff_of_coe_eq o o _ v D ?_).mpr ?_
  · rw [mfderiv_eq_fderiv]
    exact (fderiv ℝ f v).coe_toContinuousLinearEquivOfDetNeZero hdet.ne
  · rw [orientationAt_eq_orientationAt o (f v) v]
    exact (_root_.Orientation.map_eq_neg_iff_det_neg _ _ o.card_eq).mpr hdet

/-- Precomposing a map which reverses orientations at `L x` with a continuous linear automorphism
`L` of `E` of negative determinant gives a map which preserves them at `x`. -/
theorem isOrientationPreservingAt_comp_of_det_neg [IsManifold I 1 M]
    {oE : Manifold.Orientation 𝓘(ℝ, E) E ι} {oM : Manifold.Orientation I M ι} {e : E → M}
    {L : E ≃L[ℝ] E} {x : E} (he : IsOrientationReversingAt oE oM e (L x))
    (hL : LinearMap.det (L : E →ₗ[ℝ] E) < 0) :
    IsOrientationPreservingAt oE oM (e ∘ L) x :=
  he.comp (isOrientationReversingAt_of_det_neg oE L hL x)

/-- Precomposing a map which preserves orientations at `L x` with a continuous linear automorphism
`L` of `E` of negative determinant gives a map which reverses them at `x`. -/
theorem isOrientationReversingAt_comp_of_det_neg [IsManifold I 1 M]
    {oE : Manifold.Orientation 𝓘(ℝ, E) E ι} {oM : Manifold.Orientation I M ι} {e : E → M}
    {L : E ≃L[ℝ] E} {x : E} (he : IsOrientationPreservingAt oE oM e (L x))
    (hL : LinearMap.det (L : E →ₗ[ℝ] E) < 0) :
    IsOrientationReversingAt oE oM (e ∘ L) x :=
  he.comp_reversing (isOrientationReversingAt_of_det_neg oE L hL x)

end ModelSpace

section CongrModel

@[simp]
theorem isOrientationPreservingAt_congrModel_left {I J : ModelWithCorners ℝ E H} (h : I = J)
    [IsManifold I 1 M] [IsManifold J 1 M] [IsManifold I' 1 M']
    (o : Orientation I M ι) (o' : Orientation I' M' ι) (f : M → M') (x : M) :
    IsOrientationPreservingAt (o.congrModel h) o' f x ↔ IsOrientationPreservingAt o o' f x := by
  subst h
  rw [congrModel_refl]

@[simp]
theorem isOrientationPreservingAt_congrModel_right {I' J' : ModelWithCorners ℝ E' H'}
    (h : I' = J') [IsManifold I 1 M] [IsManifold I' 1 M'] [IsManifold J' 1 M']
    (o : Orientation I M ι) (o' : Orientation I' M' ι) (f : M → M') (x : M) :
    IsOrientationPreservingAt o (o'.congrModel h) f x ↔ IsOrientationPreservingAt o o' f x := by
  subst h
  rw [congrModel_refl]

@[simp]
theorem isOrientationReversingAt_congrModel_left {I J : ModelWithCorners ℝ E H} (h : I = J)
    [IsManifold I 1 M] [IsManifold J 1 M] [IsManifold I' 1 M']
    (o : Orientation I M ι) (o' : Orientation I' M' ι) (f : M → M') (x : M) :
    IsOrientationReversingAt (o.congrModel h) o' f x ↔ IsOrientationReversingAt o o' f x := by
  subst h
  rw [congrModel_refl]

@[simp]
theorem isOrientationReversingAt_congrModel_right {I' J' : ModelWithCorners ℝ E' H'}
    (h : I' = J') [IsManifold I 1 M] [IsManifold I' 1 M'] [IsManifold J' 1 M']
    (o : Orientation I M ι) (o' : Orientation I' M' ι) (f : M → M') (x : M) :
    IsOrientationReversingAt o (o'.congrModel h) f x ↔ IsOrientationReversingAt o o' f x := by
  subst h
  rw [congrModel_refl]

/-- Casting an orientation along an equality of models gives an orientation preserved by `id`. -/
theorem isOrientationPreservingAt_id_congrModel {I J : ModelWithCorners ℝ E H} (h : I = J)
    [IsManifold I 1 M] [IsManifold J 1 M] (o : Orientation I M ι) (x : M) :
    IsOrientationPreservingAt o (o.congrModel h) id x := by
  simp

end CongrModel

end TauCeti.Manifold.Orientation

namespace TauCeti.Manifold.OrientationLift

variable {E E' H H' M N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 1 M]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'} [TopologicalSpace N] [ChartedSpace H' N]
  [IsManifold J 1 N] {k : ℕ}

open Set

/-- If `f` preserves the orientations of two lifts whose model orientations correspond under a
continuous linear equivalence `C : E ≃ E'` of the model spaces, then the chart signs of the lifts
compensate the sign of the coordinate Jacobian of `f` between any two preferred charts, read in
`E` through `C`. -/
theorem signAt_mul_signAt_mul_det_pos
    (l : OrientationLift I M (Fin k)) (l' : OrientationLift J N (Fin k)) (C : E ≃L[ℝ] E')
    (hl : l'.modelOrientation =
      _root_.Orientation.map (Fin k) C.toLinearEquiv l.modelOrientation)
    {f : M → N} {x : M} (hf : MDifferentiableAt I J f x)
    (ho : Manifold.Orientation.IsOrientationPreservingAt (Manifold.Orientation.mk l)
      (Manifold.Orientation.mk l') f x)
    {β : M} {α : N} (hx : x ∈ (chartAt H β).source) (hfx : f x ∈ (chartAt H' α).source) :
    0 < (l.signAt β x : ℝ) * (l'.signAt α (f x) : ℝ) *
      ((C.symm : E' →L[ℝ] E) ∘L fderivWithin ℝ (extChartAt J α ∘ f ∘ (extChartAt I β).symm)
        (range I) (extChartAt I β x)).det := by
  obtain ⟨e, he, hp⟩ := (Manifold.Orientation.isOrientationPreservingAt_iff _ _ _ _).mp ho
  rw [Manifold.Orientation.orientationAt_mk, Manifold.Orientation.orientationAt_mk] at hp
  -- The tangent spaces are the model spaces `E` and `E'`; restate `hp` there, where the tangent
  -- orientations can be rewritten to the signed model orientations they equal.
  obtain ⟨A, hA⟩ : ∃ A : E ≃ₗ[ℝ] E', A = e.toLinearEquiv := ⟨_, rfl⟩
  replace hp : _root_.Orientation.map (Fin k) A
      (l.orientationAt x : _root_.Orientation ℝ E (Fin k)) =
        (l'.orientationAt (f x) : _root_.Orientation ℝ E' (Fin k)) := by
    subst hA
    exact hp
  rw [orientationAt_eq, orientationAt_eq, chartOrientation_eq_ite, chartOrientation_eq_ite, hl,
    ← _root_.Orientation.intCast_units_smul_eq_ite,
    ← _root_.Orientation.intCast_units_smul_eq_ite] at hp
  have h₁ := (_root_.Orientation.map_units_smul_eq_units_smul_map_iff_det_mul_pos
    l.modelOrientation A C.toLinearEquiv _ _ l.card_eq).mp hp
  have h₂ := l.compatible β x x hx (mem_chart_source H x)
  have h₃ := l'.compatible (f x) α (f x) (mem_chart_source H' (f x)) hfx
  rw [← tangentCoordChange_def] at h₂ h₃
  -- The tangent spaces at `x` and `f x` are the model spaces, so the manifold derivative of `f`
  -- is a map `D : E → E'`, which composes with the tangent coordinate changes.
  obtain ⟨D, hD₀⟩ : ∃ D : E →L[ℝ] E', D = mfderiv I J f x := ⟨_, rfl⟩
  have hD : fderivWithin ℝ (extChartAt J α ∘ f ∘ (extChartAt I β).symm) (range I)
      (extChartAt I β x) = tangentCoordChange J (f x) α (f x) ∘L D ∘L
        tangentCoordChange I β x x := by
    subst hD₀
    exact hf.fderivWithin_extChartAt_comp_extChartAt_symm
      (by simpa only [extChartAt_source] using hx) (by simpa only [extChartAt_source] using hfx)
  -- `e` is the derivative `D`, read as a linear equivalence of the model spaces; this is `rfl`
  -- because `TangentSpace I x` and `TangentSpace J (f x)` are by definition `E` and `E'`.
  have hDA : (D : E →ₗ[ℝ] E') = A := by
    subst hD₀ hA
    rw [← he]
    rfl
  have hdet : ((C.symm : E' →L[ℝ] E) ∘L D).det =
      LinearMap.det (A.trans C.toLinearEquiv.symm).toLinearMap := by
    rw [ContinuousLinearMap.det, ContinuousLinearMap.toLinearMap_comp, hDA, LinearEquiv.coe_trans,
      ← ContinuousLinearEquiv.toLinearEquiv_symm,
      ContinuousLinearEquiv.toLinearMap_toContinuousLinearMap]
  rw [hD, C.det_symm_comp_comp_comp, hdet, signAt_of_mem _ hx, signAt_of_mem _ hfx]
  simp only [Units.coe_map] at h₁
  -- Multiply the three positive quantities; the signs at `x` and at `f x` appear squared.
  have ha := Int.isUnit_mul_self (l.sign x ⟨x, mem_chart_source H x⟩).isUnit
  have hc := Int.isUnit_mul_self (l'.sign (f x) ⟨f x, mem_chart_source H' (f x)⟩).isUnit
  generalize (l.sign x ⟨x, mem_chart_source H x⟩ : ℤ) = a at h₁ h₂ ha
  generalize (l'.sign (f x) ⟨f x, mem_chart_source H' (f x)⟩ : ℤ) = c at h₁ h₃ hc
  have ha' : (a : ℝ) * a = 1 := by exact_mod_cast ha
  have hc' : (c : ℝ) * c = 1 := by exact_mod_cast hc
  have hprod := mul_pos (mul_pos h₁ h₂) h₃
  convert hprod using 1
  linear_combination
    (-((l.sign β ⟨x, hx⟩ : ℤ) : ℝ) * (l'.sign α ⟨f x, hfx⟩ : ℤ) *
      (tangentCoordChange J (f x) α (f x)).det *
      LinearMap.det (A.trans C.toLinearEquiv.symm).toLinearMap *
      (tangentCoordChange I β x x).det) * ((c : ℝ) * c * ha' + hc')

end TauCeti.Manifold.OrientationLift
