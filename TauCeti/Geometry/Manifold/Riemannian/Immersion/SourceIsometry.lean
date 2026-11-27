/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Immersion.MeanCurvature
public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Local
public import TauCeti.Geometry.Manifold.Riemannian.Restriction.Basic
import TauCeti.Geometry.Manifold.Riemannian.Isometry.Restriction
import TauCeti.Geometry.Manifold.VectorBundle.SectionAlongMap.Basic
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

/-!
# Precomposition with a local diffeomorphism or local isometry of the source

Let `f : M → N` be a map into a manifold with a covariant derivative `∇` on `TN`, and let
`ψ : M' → M` be `C²` at `x'` with invertible differential near `x'`. The second fundamental form of
`f ∘ ψ` at `x'` is that of `f` at `ψ x'`, read through the differential of `ψ`:
`B^{f ∘ ψ}_{x'}(v, w) = B^f_{ψ x'}(dψ v, dψ w)`; this involves no metric on `M` or `M'`. When `ψ`
is moreover a local Riemannian isometry, the shape operators are conjugate,
`dψ ∘ S^{f ∘ ψ}_ν = S^f_ν ∘ dψ`, and the mean curvature vectors agree:
`H^{f ∘ ψ}(x') = H^f(ψ x')`.

The case of the inclusion `U → M` of an open subset says that the second fundamental form and,
with the restricted metric, the mean curvature vector are local: restricting `f` to `U` does not
change them.

## Main results

* `TauCeti.immersionSecondFundamentalFormAt_comp`:
  `B^{f ∘ ψ}_{x'}(v, w) = B^f_{ψ x'}(dψ v, dψ w)`.
* `TauCeti.IsLocalRiemannianIsometry.mfderiv_immersionShapeOperatorAt_comp`:
  `dψ (S^{f ∘ ψ}_ν v) = S^f_ν (dψ v)`.
* `TauCeti.IsLocalRiemannianIsometry.immersionMeanCurvatureVector_comp`:
  `H^{f ∘ ψ}(x') = H^f(ψ x')`.
* `TauCeti.immersionSecondFundamentalFormAt_comp_subtypeVal`,
  `TauCeti.immersionMeanCurvatureVector_comp_subtypeVal`: restriction to an open subset preserves
  `B` and `H`.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018), Chapter 8
  (the second fundamental form and the mean curvature of a Riemannian submanifold).
-/

public section

open Bundle Manifold Module VectorField
open scoped InnerProductSpace Manifold Topology

namespace TauCeti

open TauCeti.Manifold

variable
  {E H M F G N E' H' M' : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] [TopologicalSpace G]
  {J : ModelWithCorners ℝ F G} [TopologicalSpace N] [ChartedSpace G N]
  [RiemannianBundle (fun y : N ↦ TangentSpace J y)] [IsManifold J 2 N]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E'] [TopologicalSpace H']
  {I' : ModelWithCorners ℝ E' H'} [TopologicalSpace M'] [ChartedSpace H' M'] [IsManifold I' 2 M']
  {cov : CovariantDerivative J F (TangentSpace J : N → Type _)} {f : M → N} {ψ : M' → M}
  {x' : M'}

omit [FiniteDimensional ℝ E] [IsManifold I 2 M] [FiniteDimensional ℝ F] [IsManifold J 2 N]
  [FiniteDimensional ℝ E'] [IsManifold I' 2 M'] in
/-- Precomposition with a map whose differential at `x'` is surjective does not change the normal
space. -/
theorem orthogonalNormalSpace_comp (hf : MDifferentiableAt I J f (ψ x'))
    (hψ : MDifferentiableAt I' I ψ x') (hψ' : Function.Surjective (mfderiv I' I ψ x')) :
    orthogonalNormalSpace I' J (f ∘ ψ) x' = orthogonalNormalSpace I J f (ψ x') := by
  rw [orthogonalNormalSpace_def, orthogonalNormalSpace_def, mfderiv_comp x' hf hψ]
  congr 1
  exact LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.mpr hψ')

/-- **The second fundamental form under precomposition with a local diffeomorphism**: if `ψ` is
`C²` at `x'` and its differential is invertible near `x'`, then
`B^{f ∘ ψ}_{x'}(v, w) = B^f_{ψ x'}(dψ v, dψ w)`. No metric on the source is involved. -/
theorem immersionSecondFundamentalFormAt_comp (hf : ContMDiffAt I J 2 f (ψ x'))
    (hψ : ContMDiffAt I' I 2 ψ x') (hψ' : ∀ᶠ y in 𝓝 x', (mfderiv I' I ψ y).IsInvertible)
    (v w : TangentSpace I' x') :
    immersionSecondFundamentalFormAt cov (f ∘ ψ) x' v w =
      immersionSecondFundamentalFormAt cov f (ψ x') (mfderiv I' I ψ x' v)
        (mfderiv I' I ψ x' w) := by
  have hf1 : MDifferentiableAt I J f (ψ x') := hf.mdifferentiableAt (by norm_num)
  have hψx := hψ'.self_of_nhds
  have hfψ : ContMDiffAt I' J 2 (f ∘ ψ) x' := hf.comp x' hψ
  let V : Π y : M, TangentSpace I y := FiberBundle.extend E (mfderiv I' I ψ x' v)
  let W : Π y : M, TangentSpace I y := FiberBundle.extend E (mfderiv I' I ψ x' w)
  have hV : MDiffAt (T% V) (ψ x') := FiberBundle.mdifferentiableAt_extend I E _
  have hW : MDiffAt (T% W) (ψ x') := FiberBundle.mdifferentiableAt_extend I E _
  have hVψ : V (ψ x') = mfderiv I' I ψ x' v := FiberBundle.extend_apply_self E _
  have hWψ : W (ψ x') = mfderiv I' I ψ x' w := FiberBundle.extend_apply_self E _
  have hVx : mpullback I' I ψ V x' = v := by
    rw [mpullback_apply, hVψ, hψx.inverse_apply_self]
  have hWx : mpullback I' I ψ W x' = w := by
    rw [mpullback_apply, hWψ, hψx.inverse_apply_self]
  let U : Π y : M, TangentSpace J (f y) := fun y ↦ mfderiv I J f y (W y)
  have hU : MDifferentiableAt I 𝓘(ℝ, F) (sectionCoord ℝ (F := F) f U (f (ψ x'))) (ψ x') := by
    have h := hf.contMDiffAt_tangentMap (X := (W (ψ x') : TangentBundle I M)) (m := 1)
      (by norm_num)
    exact mdifferentiableAt_sectionCoord f _ ((h.mdifferentiableAt one_ne_zero).comp (ψ x') hW)
      (FiberBundle.mem_baseSet_trivializationAt F (TangentSpace J) (f (ψ x')))
  have hfn := (contMDiffAt_iff_contMDiffAt_nhds (n := 2) (by simp)).1 hf
  have hψn := (contMDiffAt_iff_contMDiffAt_nhds (n := 2) (by simp)).1 hψ
  have heq : ∀ᶠ p in 𝓝 x', mfderiv I' J (f ∘ ψ) p (mpullback I' I ψ W p) = U (ψ p) := by
    filter_upwards [hψ.continuousAt.tendsto hfn, hψn, hψ'] with p hp hψp hψp'
    rw [mfderiv_comp p (hp.mdifferentiableAt (by norm_num)) (hψp.mdifferentiableAt (by norm_num)),
      ContinuousLinearMap.comp_apply, mpullback_apply, hψp'.self_apply_inverse]
  have hR : immersionSecondFundamentalFormAt cov f (ψ x') (mfderiv I' I ψ x' v)
      (mfderiv I' I ψ x' w) = (orthogonalNormalSpace I J f (ψ x')).starProjection
        (cov.alongMap I f U (ψ x') (V (ψ x'))) := by
    rw [← hVψ, ← hWψ, immersionSecondFundamentalFormAt_apply (cov := cov) hf hV hW,
      immersionSecondFundamentalForm_def]
  have hL : immersionSecondFundamentalFormAt cov (f ∘ ψ) x' v w =
      (orthogonalNormalSpace I' J (f ∘ ψ) x').starProjection
        (cov.alongMap I f U (ψ x') (V (ψ x'))) := by
    have hB := immersionSecondFundamentalFormAt_apply (cov := cov) hfψ
      (hV.mpullback_vectorField hψ hψx (by simp)) (hW.mpullback_vectorField hψ hψx (by simp))
    rw [hVx, hWx] at hB
    rw [hB, immersionSecondFundamentalForm_def, cov.alongMap_congr _ _ heq,
      CovariantDerivative.alongMap_comp cov f U (hψ.mdifferentiableAt (by norm_num)) hf1 hU,
      ContinuousLinearMap.comp_apply, mpullback_apply, hψx.self_apply_inverse]
  have hN := orthogonalNormalSpace_comp hf1 (hψ.mdifferentiableAt (by norm_num)) hψx.bijective.2
  rw [hL, hR]
  congr!

/-! ### Restriction of the second fundamental form to an open subset -/

/-- **The second fundamental form is local**: restricting `f` to an open subset `U` does not
change it. -/
theorem immersionSecondFundamentalFormAt_comp_subtypeVal (U : TopologicalSpace.Opens M) {x : U}
    (hf : ContMDiffAt I J 2 f (x : M)) (v w : TangentSpace I x) :
    immersionSecondFundamentalFormAt cov (f ∘ Subtype.val) x v w =
      immersionSecondFundamentalFormAt (I := I) cov f (x : M) v w := by
  have h := immersionSecondFundamentalFormAt_comp (cov := cov) hf
    contMDiff_subtypeVal.contMDiffAt (Filter.Eventually.of_forall fun y ↦
      ⟨tangentSpaceOpenEquiv (I := I) y, (mfderiv_subtype_val y).symm⟩) v w
  simpa only [mfderiv_subtype_val_apply] using h

/-! ### Precomposition with a local diffeomorphism or local isometry of the source -/

variable [RiemannianBundle (fun y : M ↦ TangentSpace I y)]
  [RiemannianBundle (fun y : M' ↦ TangentSpace I' y)]

namespace IsLocalRiemannianIsometry

/-- **The shape operator under precomposition with a local isometry of the source**: the
differential of `ψ` intertwines the shape operators, `dψ (S^{f ∘ ψ}_ν v) = S^f_ν (dψ v)`. -/
theorem mfderiv_immersionShapeOperatorAt_comp (hψ : IsLocalRiemannianIsometry I' I ψ)
    (hf : ContMDiffAt I J 2 f (ψ x')) (ν : TangentSpace J (f (ψ x'))) (v : TangentSpace I' x') :
    mfderiv I' I ψ x' (immersionShapeOperatorAt (I := I') cov (f ∘ ψ) x' ν v) =
      immersionShapeOperatorAt (I := I) cov f (ψ x') ν (mfderiv I' I ψ x' v) := by
  refine ext_inner_right ℝ fun u ↦ ?_
  obtain ⟨w, rfl⟩ := hψ.mfderiv_surjective x' u
  rw [hψ.inner_mfderiv, inner_immersionShapeOperatorAt, inner_immersionShapeOperatorAt,
    immersionSecondFundamentalFormAt_comp hf (hψ.contMDiff.contMDiffAt.of_le (by simp))
      (.of_forall hψ.isInvertible_mfderiv)]

/-- **The mean curvature vector under precomposition with a local isometry of the source**:
`H^{f ∘ ψ}(x') = H^f(ψ x')`. -/
theorem immersionMeanCurvatureVector_comp (hψ : IsLocalRiemannianIsometry I' I ψ)
    (hf : ContMDiffAt I J 2 f (ψ x')) :
    immersionMeanCurvatureVector (I := I') cov (f ∘ ψ) x' =
      immersionMeanCurvatureVector (I := I) cov f (ψ x') := by
  obtain ⟨e, he⟩ := hψ.exists_linearIsometryEquiv_eq_mfderiv x'
  set b := stdOrthonormalBasis ℝ (TangentSpace I' x')
  have hdim : finrank ℝ E' = finrank ℝ E := e.toLinearEquiv.finrank_eq
  rw [immersionMeanCurvatureVector_eq_sum b, immersionMeanCurvatureVector_eq_sum (b.map e), hdim]
  congr 1
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [immersionSecondFundamentalFormAt_comp hf (hψ.contMDiff.contMDiffAt.of_le (by simp))
    (.of_forall hψ.isInvertible_mfderiv), OrthonormalBasis.map_apply, he]

end IsLocalRiemannianIsometry

/-! ### Restriction of the mean curvature vector to an open subset -/

section Restriction

open scoped TauCeti

/-- **The mean curvature vector is local**: restricting `f` to an open subset `U`, with the
restricted metric, does not change it. -/
theorem immersionMeanCurvatureVector_comp_subtypeVal (U : TopologicalSpace.Opens M) {x : U}
    (hf : ContMDiffAt I J 2 f (x : M)) :
    immersionMeanCurvatureVector (I := I) cov (f ∘ Subtype.val) x =
      immersionMeanCurvatureVector (I := I) cov f (x : M) :=
  (IsLocalRiemannianIsometry.subtype_val (I := I) U).immersionMeanCurvatureVector_comp hf

end Restriction

end TauCeti
