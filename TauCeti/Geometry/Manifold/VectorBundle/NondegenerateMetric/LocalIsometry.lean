/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Local
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita.Nondegenerate.Basic

/-!
# Local isometries of nondegenerate metrics

Let `g` and `g'` be smooth symmetric nondegenerate metrics on `M` and `N`, of any signature. A
*local isometry* `f : M → N` from `g` to `g'` is a smooth map whose differential at every point is
invertible and pulls `g'` back to `g`:

`g'_{f x}(df_x v, df_x w) = g_x(v, w)`.

It need not be injective or surjective: a diffeomorphism preserving the metrics is a local
isometry, and so is a covering map whose target metric pulls back to the source metric.

The Levi-Civita connection is natural under local isometries: if `∇` and `∇'` are Levi-Civita
connections of `g` and `g'`, then for a vector field `Y` on `N` differentiable at `f x`,

`df_x (∇_v (f^* Y)) = ∇'_{df_x v} Y`,

where `f^* Y = VectorField.mpullback I J f Y` is the pullback vector field. The proof transports
the Koszul expression along `f` and concludes by the nondegeneracy of `g'`. Since a Levi-Civita
connection of a nondegenerate metric is unique on differentiable vector fields, this determines
how any construction of it behaves under metric-preserving diffeomorphisms.

For metrics coming from Riemannian bundle instances, local isometries are exactly the local
Riemannian isometries `TauCeti.IsLocalRiemannianIsometry`.

## Main definitions and results

In the namespace `TauCeti.Manifold.ContMDiffNondegenerateMetric`:

* `IsLocalIsometry`: a smooth map with invertible differentials pulling one nondegenerate metric
  back to another.
* `IsLocalIsometry.mfderiv_apply_mpullback`: the differential cancels the pullback of a vector
  field.
* `IsLocalIsometry.id` and `IsLocalIsometry.comp`: the identity and composites.
* `isLocalIsometry_ofRiemannianBundle_iff`: for Riemannian metrics, local isometries are the local
  Riemannian isometries.
* `IsLocalIsometry.koszul_mpullback`: the Koszul expression is natural under local isometries.
* `IsLocalIsometry.two_apply_mfderiv_eq_koszul`: the Koszul formula of a Levi-Civita connection of
  the source metric, read in the target through the differential; it needs no connection of the
  target metric.
* `IsLocalIsometry.mfderiv_apply_mpullback_of_isLeviCivitaConnection`: **naturality of
  Levi-Civita connections** under local isometries.
* `IsLocalIsometry.mpullback_apply_mpullback_of_isLeviCivitaConnection`: the vector-field form
  `∇_{f^* Y} (f^* Z) = f^* (∇'_Y Z)`.

## References

* B. O'Neill, *Semi-Riemannian Geometry with Applications to Relativity*, Academic Press, 1983,
  Ch. 3 (isometries preserve Levi-Civita connections).
* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018),
  Prop. 5.13.
* `TauCeti.Geometry.Manifold.Riemannian.Isometry.LeviCivita`: the positive-definite argument
  for local Riemannian isometries, adapted here with the inner product replaced by `g` and
  positivity by nondegeneracy.
-/

public section

open Bundle FiberBundle VectorField
open scoped ContDiff Manifold

noncomputable section

namespace TauCeti.Manifold.ContMDiffNondegenerateMetric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]

/-- A smooth map `f : M → N` is a *local isometry* from the nondegenerate metric `g` on `M` to the
nondegenerate metric `g'` on `N` if its differential at every point is invertible and pulls `g'`
back to `g`. -/
structure IsLocalIsometry (g : ContMDiffNondegenerateMetric (I := I) (M := M))
    (g' : ContMDiffNondegenerateMetric (I := J) (M := N)) (f : M → N) : Prop where
  /-- A local isometry is smooth. -/
  contMDiff : ContMDiff I J ∞ f
  /-- The differential of a local isometry is invertible at every point. -/
  isInvertible_mfderiv (x : M) : (mfderiv I J f x).IsInvertible
  /-- The differential of a local isometry pulls the target metric back to the source metric. -/
  apply_mfderiv (x : M) (v w : TangentSpace I x) :
    g' (f x) (mfderiv I J f x v) (mfderiv I J f x w) = g x v w

namespace IsLocalIsometry

variable {g : ContMDiffNondegenerateMetric (I := I) (M := M)}
  {g' : ContMDiffNondegenerateMetric (I := J) (M := N)} {f : M → N}

/-- The differential of a local isometry sends the pullback of a vector field at `x` to the value
of the field at `f x`. -/
theorem mfderiv_apply_mpullback (hf : g.IsLocalIsometry g' f) (V : Π y : N, TangentSpace J y)
    (x : M) : mfderiv I J f x (mpullback I J f V x) = V (f x) :=
  (hf.isInvertible_mfderiv x).self_apply_inverse _

/-- Pulling back vector fields along a local isometry preserves their pointwise pairing. -/
theorem apply_mpullback (hf : g.IsLocalIsometry g' f) (V W : Π y : N, TangentSpace J y) (x : M) :
    g x (mpullback I J f V x) (mpullback I J f W x) = g' (f x) (V (f x)) (W (f x)) := by
  rw [← hf.apply_mfderiv, hf.mfderiv_apply_mpullback, hf.mfderiv_apply_mpullback]

variable (g) in
/-- The identity map is a local isometry from a nondegenerate metric to itself. -/
protected theorem id : g.IsLocalIsometry g id where
  contMDiff := contMDiff_id
  isInvertible_mfderiv x := by
    rw [mfderiv_id]
    exact ⟨ContinuousLinearEquiv.refl ℝ _, rfl⟩
  apply_mfderiv x v w := by
    simp only [mfderiv_id, ContinuousLinearMap.id_apply, id_eq]

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
  {H'' : Type*} [TopologicalSpace H''] {K : ModelWithCorners ℝ G H''}
  {P : Type*} [TopologicalSpace P] [ChartedSpace H'' P] [IsManifold K ∞ P]
  {g'' : ContMDiffNondegenerateMetric (I := K) (M := P)}

/-- The composite of two local isometries of nondegenerate metrics is a local isometry. -/
protected theorem comp {f' : N → P} (hf' : g'.IsLocalIsometry g'' f')
    (hf : g.IsLocalIsometry g' f) : g.IsLocalIsometry g'' (f' ∘ f) where
  contMDiff := hf'.contMDiff.comp hf.contMDiff
  isInvertible_mfderiv x := by
    rw [mfderiv_comp x (hf'.contMDiff.mdifferentiableAt (by simp))
      (hf.contMDiff.mdifferentiableAt (by simp))]
    exact (hf'.isInvertible_mfderiv (f x)).comp (hf.isInvertible_mfderiv x)
  apply_mfderiv x v w := by
    rw [mfderiv_comp_apply x (hf'.contMDiff.mdifferentiableAt (by simp))
      (hf.contMDiff.mdifferentiableAt (by simp)),
      mfderiv_comp_apply x (hf'.contMDiff.mdifferentiableAt (by simp))
      (hf.contMDiff.mdifferentiableAt (by simp)), Function.comp_apply, hf'.apply_mfderiv,
      hf.apply_mfderiv]

end IsLocalIsometry

/-- For the metrics of smooth Riemannian bundle instances, a local isometry is exactly a local
Riemannian isometry. -/
theorem isLocalIsometry_ofRiemannianBundle_iff
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [RiemannianBundle (fun y : N ↦ TangentSpace J y)]
    [IsContMDiffRiemannianBundle J ∞ F (fun y : N ↦ TangentSpace J y)] {f : M → N} :
    (ofRiemannianBundle I M).IsLocalIsometry (ofRiemannianBundle J N) f ↔
      IsLocalRiemannianIsometry I J f := by
  constructor
  · intro hf
    exact ⟨hf.contMDiff, hf.isInvertible_mfderiv, fun x v w ↦ by
      simpa only [ofRiemannianBundle_apply] using hf.apply_mfderiv x v w⟩
  · intro hf
    exact ⟨hf.contMDiff, hf.isInvertible_mfderiv, fun x v w ↦ by
      simpa only [ofRiemannianBundle_apply] using hf.inner_mfderiv x v w⟩

namespace IsLocalIsometry

variable {g : ContMDiffNondegenerateMetric (I := I) (M := M)}
  {g' : ContMDiffNondegenerateMetric (I := J) (M := N)} {f : M → N}
  {X Y Z : Π y : N, TangentSpace J y} {x : M}

/-- Pulling back a vector field differentiable at `f x` along a local isometry gives a vector
field differentiable at `x`. -/
theorem mdifferentiableAt_mpullback [CompleteSpace E] (hf : g.IsLocalIsometry g' f)
    (hY : MDiffAt (T% Y) (f x)) :
    MDiffAt (T% (mpullback I J f Y)) x :=
  hY.mpullback_vectorField hf.contMDiff.contMDiffAt (hf.isInvertible_mfderiv x) (by simp)

/-- **Naturality of the Koszul expression.** The Koszul expression of `g` on the pullbacks of three
vector fields along a local isometry `f` is the Koszul expression of `g'` on the fields themselves,
evaluated at the image point. -/
theorem koszul_mpullback [CompleteSpace E] (hf : g.IsLocalIsometry g' f)
    (hX : MDiffAt (T% X) (f x)) (hY : MDiffAt (T% Y) (f x)) (hZ : MDiffAt (T% Z) (f x)) :
    g.koszul (mpullback I J f X) (mpullback I J f Y) (mpullback I J f Z) x =
      g'.koszul X Y Z (f x) := by
  have h := koszulBilinear_mpullback (b := g) (b' := g') (hf.contMDiff.contMDiffAt.of_le (by simp))
    hf.isInvertible_mfderiv (fun y v w ↦ (hf.apply_mfderiv y v w).symm)
    (fun _ _ hV hW ↦ g'.mdifferentiableAt_apply hV hW) hX hY hZ
  rw [koszul_apply, koszul_apply]
  simpa only [koszulBilinear_apply] using h

variable [FiniteDimensional ℝ E] {cov : CovariantDerivative I E (fun x : M ↦ TangentSpace I x)}

/-- **The Koszul formula through a local isometry.** Let `∇` be a Levi-Civita connection of `g`
and `f` a local isometry from `g` to `g'`. For vector fields `X`, `Y`, `Z` on `N` differentiable
at `f x` with `X (f x) = df_x v`, `2 g'(df_x (∇_v (f^* Y)), Z)` at `f x` is the Koszul expression
of `g'` on `X`, `Y`, `Z` at `f x`. No Levi-Civita connection of `g'` is needed. -/
theorem two_apply_mfderiv_eq_koszul (hf : g.IsLocalIsometry g' f)
    (h : g.IsLeviCivitaConnection cov) (hX : MDiffAt (T% X) (f x)) (hY : MDiffAt (T% Y) (f x))
    (hZ : MDiffAt (T% Z) (f x)) {v : TangentSpace I x} (hXv : X (f x) = mfderiv I J f x v) :
    2 * g' (f x) (mfderiv I J f x (cov (mpullback I J f Y) x v)) (Z (f x)) =
      g'.koszul X Y Z (f x) := by
  have hXx : mpullback I J f X x = v := by
    rw [mpullback_apply, hXv, (hf.isInvertible_mfderiv x).inverse_apply_self]
  have hk := h.two_apply_eq_koszul (hf.mdifferentiableAt_mpullback hX)
    (hf.mdifferentiableAt_mpullback hY) (hf.mdifferentiableAt_mpullback hZ)
  rw [hf.koszul_mpullback hX hY hZ, hXx] at hk
  rw [← hk, ← hf.apply_mfderiv, hf.mfderiv_apply_mpullback]

variable [FiniteDimensional ℝ F] {cov' : CovariantDerivative J F (fun y : N ↦ TangentSpace J y)}

/-- **Naturality of Levi-Civita connections under local isometries.** If `∇` and `∇'` are
Levi-Civita connections of the nondegenerate metrics `g` and `g'` and `f` is a local isometry from
`g` to `g'`, then `df_x (∇_v (f^* Y)) = ∇'_{df_x v} Y` for every vector field `Y` on `N`
differentiable at `f x`. -/
theorem mfderiv_apply_mpullback_of_isLeviCivitaConnection (hf : g.IsLocalIsometry g' f)
    (h : g.IsLeviCivitaConnection cov) (h' : g'.IsLeviCivitaConnection cov')
    (hY : MDiffAt (T% Y) (f x)) (v : TangentSpace I x) :
    mfderiv I J f x (cov (mpullback I J f Y) x v) = cov' Y (f x) (mfderiv I J f x v) := by
  -- Realize the direction `df_x v` by a vector field on `N` and compare both Koszul formulas.
  set X : Π y : N, TangentSpace J y := extend F (mfderiv I J f x v)
  have hX : MDiffAt (T% X) (f x) := mdifferentiableAt_extend J F _
  have hXv : X (f x) = mfderiv I J f x v := extend_apply_self F _
  refine g'.injective_apply_mdifferentiableAt_vectorField (f x) ?_
  ext Z hZ
  have hk := hf.two_apply_mfderiv_eq_koszul h hX hY hZ hXv
  have hk' := h'.two_apply_eq_koszul hX hY hZ
  rw [hXv] at hk'
  dsimp only
  linarith

/-- The covariant derivative of a pulled-back vector field in a pulled-back direction is the
pullback of the covariant derivative: `∇_{f^* Y} (f^* Z) = f^* (∇'_Y Z)` at `x`, for Levi-Civita
connections `∇` and `∇'` of `g` and `g'` and a local isometry `f` from `g` to `g'`. -/
theorem mpullback_apply_mpullback_of_isLeviCivitaConnection (hf : g.IsLocalIsometry g' f)
    (h : g.IsLeviCivitaConnection cov) (h' : g'.IsLeviCivitaConnection cov')
    (hZ : MDiffAt (T% Z) (f x)) :
    cov (mpullback I J f Z) x (mpullback I J f Y x) =
      mpullback I J f (fun y ↦ cov' Z y (Y y)) x := by
  apply (hf.isInvertible_mfderiv x).injective
  rw [hf.mfderiv_apply_mpullback_of_isLeviCivitaConnection h h' hZ, hf.mfderiv_apply_mpullback,
    hf.mfderiv_apply_mpullback]

end IsLocalIsometry

end TauCeti.Manifold.ContMDiffNondegenerateMetric
