/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Isometry.LeviCivita
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Scalar
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Sectional
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita.Regularity
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Regularity
import TauCeti.Geometry.Manifold.VectorBundle.Section.Extension

/-!
# Curvature under Riemannian isometries

A smooth Riemannian isometry `Φ : M → N` carries the Riemann curvature tensor of `M` to that of
`N`:

`dΦ_x (R(u, v) w) = R(dΦ_x u, dΦ_x v) (dΦ_x w)`

for all tangent vectors `u, v, w` at `x`. Consequently it preserves every curvature quantity built
from the curvature tensor and the metric: the sectional curvature of each tangent two-plane, the
Ricci tensor and the scalar curvature.

These invariants are what constrain an isometry of a homogeneous space that is not a space form.
For example, on `S² × ℝ` the tangent planes of the sphere factor are exactly the planes of
sectional curvature `1`, and the line field tangent to the `ℝ` factor is the kernel of the Ricci
tensor, so the differential of an isometry preserves the product splitting of each tangent space.
Combined with the determination of isometries by their first-order data, this is the input for
identifying the full isometry groups of such model spaces.

The curvature identity follows from the naturality of the Levi-Civita connection
(`TauCeti.RiemannianIsometry.mfderiv_leviCivitaConnection_mpullback`) and of the Lie bracket
(`VectorField.mpullback_mlieBracket`): pulling back three smooth vector fields along `Φ` pulls back
each of the three terms in `R(X, Y) Z = ∇_X ∇_Y Z - ∇_Y ∇_X Z - ∇_[X, Y] Z`.

## Main results

In the namespace `TauCeti.RiemannianIsometry`:

* `mfderiv_curvatureOperator_mpullback`: the curvature operator of pulled-back smooth vector fields
  is the pullback of the curvature operator.
* `mfderiv_curvatureTensor`: **naturality of the Riemann curvature tensor** under Riemannian
  isometries.
* `sectionalCurvature_mfderiv`, `hasSectionalCurvatureAt_map_iff` and
  `hasConstantSectionalCurvature_iff`: isometries preserve sectional curvature.
* `ricciTensor_mfderiv` and `scalarCurvature_map`: isometries preserve the Ricci tensor and the
  scalar curvature.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., GTM 176, 2018, Proposition 7.6
  (naturality of the curvature tensor).
* M. P. do Carmo, *Riemannian Geometry*, Birkhäuser, 1992, Ch. 4, §3.
-/

public section

open Bundle FiberBundle Manifold VectorField CovariantDerivative
open scoped ContDiff Manifold

noncomputable section

namespace TauCeti.RiemannianIsometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]
  [RiemannianBundle (fun y : N ↦ TangentSpace J y)]
  [IsContMDiffRiemannianBundle J ∞ F (fun y : N ↦ TangentSpace J y)]

/-- **Naturality of the curvature operator under Riemannian isometries.** For smooth vector
fields `X`, `Y`, `Z` on `N`, the curvature operator of `M` applied to their pullbacks along `Φ`
is the pullback of the curvature operator of `N`:
`dΦ_x (R(Φ^* X, Φ^* Y) (Φ^* Z) x) = R(X, Y) Z (Φ x)`. -/
theorem mfderiv_curvatureOperator_mpullback (Φ : RiemannianIsometry I J M N)
    {X Y Z : Π y : N, TangentSpace J y} (hX : CMDiff ∞ (T% X)) (hY : CMDiff ∞ (T% Y))
    (hZ : CMDiff ∞ (T% Z)) (x : M) :
    mfderiv I J Φ x ((leviCivitaConnection I M).curvatureOperator
        (mpullback I J Φ X) (mpullback I J Φ Y) (mpullback I J Φ Z) x) =
      (leviCivitaConnection J N).curvatureOperator X Y Z (Φ x) := by
  have hZd : MDiff (T% Z) := hZ.mdifferentiable (by simp)
  -- The inner covariant derivatives `∇_Y Z` and `∇_X Z` are pullbacks of smooth fields.
  have hpull : ∀ {W : Π y : N, TangentSpace J y},
      (fun y ↦ leviCivitaConnection I M (mpullback I J Φ Z) y (mpullback I J Φ W y)) =
        mpullback I J Φ (fun y ↦ leviCivitaConnection J N Z y (W y)) := fun {W} ↦
    funext fun y ↦ Φ.leviCivitaConnection_mpullback_apply_mpullback (hZd (Φ y))
  have hsmooth : ∀ {W : Π y : N, TangentSpace J y}, CMDiff ∞ (T% W) →
      MDiff (T% (fun y ↦ leviCivitaConnection J N Z y (W y))) := fun hW ↦
    -- `simpa` turns `C^∞` into `C^(∞ + 1)`, the regularity `contMDiff_apply` asks of `Z`.
    ((leviCivitaConnection J N).contMDiff_apply hW (by simpa using hZ)).mdifferentiable
      (by simp)
  -- The Lie bracket of pullbacks is the pullback of the Lie bracket.
  have hbracket : mlieBracket I (mpullback I J Φ X) (mpullback I J Φ Y) x =
      mpullback I J Φ (mlieBracket J X Y) x := by
    let _ : IsManifold I (minSmoothness ℝ 2) M := by
      rw [minSmoothness_of_isRCLikeNormedField]; infer_instance
    let _ : IsManifold J (minSmoothness ℝ 2) N := by
      rw [minSmoothness_of_isRCLikeNormedField]; infer_instance
    exact (mpullback_mlieBracket (hX.mdifferentiable (by simp) (Φ x))
      (hY.mdifferentiable (by simp) (Φ x)) (Φ.toDiffeomorph.contMDiff.contMDiffAt)
      (by simp)).symm
  rw [curvatureOperator_apply, curvatureOperator_apply, hpull, hpull, hbracket, map_sub, map_sub,
    Φ.mfderiv_leviCivitaConnection_mpullback (hsmooth hY (Φ x)),
    Φ.mfderiv_leviCivitaConnection_mpullback (hsmooth hX (Φ x)),
    Φ.mfderiv_leviCivitaConnection_mpullback (hZd (Φ x)),
    ← coe_toDiffeomorph Φ,
    Φ.toDiffeomorph.mfderiv_apply_mpullback (by simp),
    Φ.toDiffeomorph.mfderiv_apply_mpullback (by simp),
    Φ.toDiffeomorph.mfderiv_apply_mpullback (by simp)]

variable [T2Space M] [T2Space N]

/-- **Naturality of the Riemann curvature tensor under Riemannian isometries:**
`dΦ_x (R(u, v) w) = R(dΦ_x u, dΦ_x v) (dΦ_x w)`. -/
@[simp]
theorem mfderiv_curvatureTensor (Φ : RiemannianIsometry I J M N) (x : M)
    (u v w : TangentSpace I x) :
    mfderiv I J Φ x ((leviCivitaConnection I M).curvatureTensor x u v w) =
      (leviCivitaConnection J N).curvatureTensor (Φ x) (mfderiv I J Φ x u)
        (mfderiv I J Φ x v) (mfderiv I J Φ x w) := by
  -- Extend the images of `u`, `v`, `w` to smooth vector fields on `N` and pull them back.
  have hext : ∀ u : TangentSpace I x, ∃ X : Π y : N, TangentSpace J y,
      CMDiff ∞ (T% X) ∧ mpullback I J Φ X x = u ∧ X (Φ x) = mfderiv I J Φ x u := fun u ↦ by
    obtain ⟨X, hX, hXu⟩ := exists_contMDiff_section_eq J F (mfderiv I J Φ x u)
    refine ⟨X, hX, ?_, hXu⟩
    apply Φ.mfderiv_injective x
    rw [← coe_toDiffeomorph Φ, Φ.toDiffeomorph.mfderiv_apply_mpullback (by simp)]
    simpa only [coe_toDiffeomorph] using hXu
  have hpull : ∀ {X : Π y : N, TangentSpace J y}, CMDiff ∞ (T% X) →
      CMDiff ∞ (T% (mpullback I J Φ X)) := fun hX ↦
    hX.mpullback_vectorField Φ.toDiffeomorph.contMDiff
      (fun y ↦ Φ.toDiffeomorph.isInvertible_mfderiv (by simp)) (by simp)
  obtain ⟨X, hX, hXu, hXΦ⟩ := hext u
  obtain ⟨Y, hY, hYv, hYΦ⟩ := hext v
  obtain ⟨Z, hZ, hZw, hZΦ⟩ := hext w
  rw [← hXΦ, ← hYΦ, ← hZΦ, curvatureTensor_apply _ _ hX hY hZ, ← hXu, ← hYv, ← hZw,
    curvatureTensor_apply _ _ (hpull hX) (hpull hY) (hpull hZ)]
  exact Φ.mfderiv_curvatureOperator_mpullback hX hY hZ x

/-- A Riemannian isometry preserves the curvature tensor paired with the metric:
`⟪R(dΦ_x u, dΦ_x v) (dΦ_x w), dΦ_x z⟫ = ⟪R(u, v) w, z⟫`. -/
@[simp]
theorem inner_curvatureTensor_mfderiv (Φ : RiemannianIsometry I J M N) (x : M)
    (u v w z : TangentSpace I x) :
    inner ℝ ((leviCivitaConnection J N).curvatureTensor (Φ x) (mfderiv I J Φ x u)
        (mfderiv I J Φ x v) (mfderiv I J Φ x w)) (mfderiv I J Φ x z) =
      inner ℝ ((leviCivitaConnection I M).curvatureTensor x u v w) z := by
  rw [← mfderiv_curvatureTensor, inner_mfderiv]

/-- A Riemannian isometry preserves sectional curvature: the plane spanned by `dΦ_x u` and
`dΦ_x v` has the same sectional curvature as the plane spanned by `u` and `v`. -/
theorem sectionalCurvature_mfderiv (Φ : RiemannianIsometry I J M N) (x : M)
    (u v : TangentSpace I x) :
    (leviCivitaConnection J N).sectionalCurvature (isMetricCompatible_leviCivitaConnection J)
        (Φ x) (mfderiv I J Φ x u) (mfderiv I J Φ x v) =
      (leviCivitaConnection I M).sectionalCurvature (isMetricCompatible_leviCivitaConnection I)
        x u v := by
  rw [sectionalCurvature_apply, sectionalCurvature_apply, Matrix.real_det_gram_fin_two,
    Matrix.real_det_gram_fin_two, inner_curvatureTensor_mfderiv, inner_mfderiv, inner_mfderiv,
    inner_mfderiv]

/-- A Riemannian isometry `Φ` preserves pointwise sectional curvature: `N` has sectional
curvature `k` at `Φ x` exactly when `M` has sectional curvature `k` at `x`. -/
@[simp]
theorem hasSectionalCurvatureAt_map_iff (Φ : RiemannianIsometry I J M N) (x : M) (k : ℝ) :
    (leviCivitaConnection J N).HasSectionalCurvatureAt
        (isMetricCompatible_leviCivitaConnection J) (Φ x) k ↔
      (leviCivitaConnection I M).HasSectionalCurvatureAt
        (isMetricCompatible_leviCivitaConnection I) x k := by
  let e := (Φ.mfderivToLinearIsometryEquiv x).toLinearEquiv
  have he : ∀ u, e u = mfderiv I J Φ x u := Φ.mfderivToLinearIsometryEquiv_apply x
  have hli : ∀ u v : TangentSpace I x,
      LinearIndependent ℝ ![e u, e v] ↔ LinearIndependent ℝ ![u, v] := fun u v ↦ by
    -- `LinearMap.linearIndependent_iff` is stated for a composite `e ∘ f`, so rewrite the
    -- pair of images as the image of the pair.
    have hcomp : e ∘ ![u, v] = ![e u, e v] := by ext i; fin_cases i <;> simp
    rw [← hcomp]
    exact e.toLinearMap.linearIndependent_iff (LinearEquiv.ker e)
  rw [CovariantDerivative.hasSectionalCurvatureAt_iff,
    CovariantDerivative.hasSectionalCurvatureAt_iff]
  constructor
  · intro h u v huv
    rw [← Φ.sectionalCurvature_mfderiv, ← he, ← he]
    exact h _ _ ((hli u v).2 huv)
  · intro h u' v' huv
    obtain ⟨u, rfl⟩ := e.surjective u'
    obtain ⟨v, rfl⟩ := e.surjective v'
    rw [he, he, Φ.sectionalCurvature_mfderiv]
    exact h u v ((hli u v).1 huv)

/-- Riemannian isometric manifolds have the same constant sectional curvatures. -/
theorem hasConstantSectionalCurvature_iff (Φ : RiemannianIsometry I J M N) (k : ℝ) :
    (leviCivitaConnection J N).HasConstantSectionalCurvature
        (isMetricCompatible_leviCivitaConnection J) k ↔
      (leviCivitaConnection I M).HasConstantSectionalCurvature
        (isMetricCompatible_leviCivitaConnection I) k := by
  simp only [CovariantDerivative.hasConstantSectionalCurvature_iff]
  refine ⟨fun h x ↦ (Φ.hasSectionalCurvatureAt_map_iff x k).1 (h (Φ x)), fun h y ↦ ?_⟩
  rw [← Φ.apply_symm_apply y]
  exact (Φ.hasSectionalCurvatureAt_map_iff (Φ.symm y) k).2 (h (Φ.symm y))

/-- A Riemannian isometry preserves the Ricci tensor:
`Ric(dΦ_x u, dΦ_x v) = Ric(u, v)`. -/
theorem ricciTensor_mfderiv (Φ : RiemannianIsometry I J M N) (x : M)
    (u v : TangentSpace I x) :
    (leviCivitaConnection J N).ricciTensor (Φ x) (mfderiv I J Φ x u) (mfderiv I J Φ x v) =
      (leviCivitaConnection I M).ricciTensor x u v := by
  let b := stdOrthonormalBasis ℝ (TangentSpace I x)
  rw [ricciTensor_eq_sum_inner _ x b,
    ricciTensor_eq_sum_inner _ (Φ x) (b.map (Φ.mfderivToLinearIsometryEquiv x))]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [OrthonormalBasis.map_apply, mfderivToLinearIsometryEquiv_apply, ← mfderiv_curvatureTensor,
    inner_mfderiv]

/-- A Riemannian isometry preserves scalar curvature. -/
@[simp]
theorem scalarCurvature_map (Φ : RiemannianIsometry I J M N) (x : M) :
    (leviCivitaConnection J N).scalarCurvature (Φ x) =
      (leviCivitaConnection I M).scalarCurvature x := by
  let b := stdOrthonormalBasis ℝ (TangentSpace I x)
  rw [scalarCurvature_eq_sum _ x b,
    scalarCurvature_eq_sum _ (Φ x) (b.map (Φ.mfderivToLinearIsometryEquiv x))]
  simp only [OrthonormalBasis.map_apply, mfderivToLinearIsometryEquiv_apply, ricciTensor_mfderiv]

end TauCeti.RiemannianIsometry

end
