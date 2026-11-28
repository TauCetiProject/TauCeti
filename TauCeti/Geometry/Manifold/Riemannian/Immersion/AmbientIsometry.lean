/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Immersion.MeanCurvature
public import TauCeti.Geometry.Manifold.Riemannian.Isometry.AlongMap
public import TauCeti.Geometry.Manifold.Riemannian.Restriction.Basic
import TauCeti.Geometry.Manifold.MFDeriv.Basic
import TauCeti.Geometry.Manifold.Riemannian.Isometry.Restriction

/-!
# Immersion geometry under ambient isometries

Let `f : M → N` be a map into a Riemannian manifold and `Φ : N → N'` a local Riemannian isometry,
with Levi-Civita connections `∇` on `N` and `∇'` on `N'`. The differential `dΦ` at `f x` carries
the submanifold geometry of `f` at `x` to that of `Φ ∘ f`:

* the tangent and normal splittings: `dΦ` maps `range df_x` and the normal space `ν_f(x)` to
  `range d(Φ ∘ f)_x` and `ν_{Φ ∘ f}(x)`, and commutes with both orthogonal projections
  (`TauCeti.IsLocalRiemannianIsometry.mfderiv_starProjection_range`,
  `TauCeti.IsLocalRiemannianIsometry.mfderiv_starProjection_orthogonalNormalSpace`);
* the second fundamental form, `dΦ (B_f(X, Y)) = B_{Φ ∘ f}(X, Y)`, for fields
  (`TauCeti.IsLocalRiemannianIsometry.mfderiv_immersionSecondFundamentalForm`) and pointwise
  (`TauCeti.IsLocalRiemannianIsometry.mfderiv_immersionSecondFundamentalFormAt`);
* the shape operator and the normal connection of fields along `f`:
  `dΦ (S_ν X) = S'_{dΦ ν} X` and `dΦ (∇^⊥_X ν) = ∇'^⊥_X (dΦ ν)`
  (`TauCeti.IsLocalRiemannianIsometry.mfderiv_immersionShapeOperator`,
  `TauCeti.IsLocalRiemannianIsometry.mfderiv_immersionNormalConnection`);
* the pointwise shape operator and the principal curvatures in the direction `ν` equal those of
  `Φ ∘ f` in the direction `dΦ ν`
  (`TauCeti.IsLocalRiemannianIsometry.immersionShapeOperatorAt_comp`,
  `TauCeti.IsLocalRiemannianIsometry.immersionPrincipalCurvatures_comp`);
* the mean curvature vector, `dΦ H_f = H_{Φ ∘ f}`, so `Φ ∘ f` is minimal at `x` exactly when
  `f` is (`TauCeti.IsLocalRiemannianIsometry.mfderiv_immersionMeanCurvatureVector`,
  `TauCeti.IsLocalRiemannianIsometry.immersionMeanCurvatureVector_comp_eq_zero_iff`), and the
  squared norm of the second fundamental form is unchanged
  (`TauCeti.IsLocalRiemannianIsometry.immersionSecondFundamentalFormNormSq_comp`).

A local Riemannian isometry need not be injective, so this covers ambient isometries and the
inclusion of an open subset of `N` with the restricted metric alike. The input is the naturality
of covariant differentiation along maps,
`TauCeti.IsLocalRiemannianIsometry.mfderiv_alongMap_of_isLeviCivitaConnection`, applied to the
fields `df Y` and `ν` along `f`.

For the inclusion `ι : U → N` of an open subset with the restricted metric, `dι` is the identity
of `T_y N`, so the immersion geometry of a map `φ : M → U` is that of `ι ∘ φ`: the second
fundamental form, shape operator, normal connection, principal curvatures and mean curvature
vector agree (`TauCeti.immersionSecondFundamentalForm_subtypeVal_comp`,
`TauCeti.immersionShapeOperator_subtypeVal_comp`,
`TauCeti.immersionNormalConnection_subtypeVal_comp`,
`TauCeti.immersionSecondFundamentalFormAt_subtypeVal_comp`,
`TauCeti.immersionShapeOperatorAt_subtypeVal_comp`,
`TauCeti.immersionPrincipalCurvatures_subtypeVal_comp`,
`TauCeti.immersionMeanCurvatureVector_subtypeVal_comp`). Restriction of the source to an open
subset is in `TauCeti.Geometry.Manifold.Riemannian.Immersion.SourceIsometry`.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., GTM 176, 2018, Chapter 8, the
  convention reference of the RiemannianGeometry roadmap.
-/

public section

noncomputable section

open Bundle Filter Manifold Module VectorField
open scoped ContDiff InnerProductSpace Manifold Topology

namespace TauCeti

open TauCeti.Manifold

variable
  {E H M F G N F' G' N' : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] [TopologicalSpace G]
  {J : ModelWithCorners ℝ F G} [TopologicalSpace N] [ChartedSpace G N]
  [RiemannianBundle (fun y : N ↦ TangentSpace J y)]
  [NormedAddCommGroup F'] [NormedSpace ℝ F'] [FiniteDimensional ℝ F'] [TopologicalSpace G']
  {J' : ModelWithCorners ℝ F' G'} [TopologicalSpace N'] [ChartedSpace G' N']
  [RiemannianBundle (fun y : N' ↦ TangentSpace J' y)]
  {Φ : N → N'} {f : M → N} {x : M}

namespace IsLocalRiemannianIsometry

/-! ### The tangent and normal splittings -/

section Splitting


/-- `dΦ` commutes with the orthogonal projections onto the tangent spaces `range df_x` and
`range d(Φ ∘ f)_x`. -/
theorem mfderiv_starProjection_range (hΦ : IsLocalRiemannianIsometry J J' Φ)
    (hf : MDifferentiableAt I J f x) (w : TangentSpace J (f x)) :
    mfderiv J J' Φ (f x) ((LinearMap.range (mfderiv I J f x).toLinearMap).starProjection w) =
      (LinearMap.range (mfderiv I J' (Φ ∘ f) x).toLinearMap).starProjection
        (mfderiv J J' Φ (f x) w) := by
  rw [range_mfderiv_comp (hΦ.mdifferentiableAt (f x)) hf]
  exact ((mfderiv J J' Φ (f x)).toLinearMap.isometryOfInner
    (hΦ.inner_mfderiv _)).map_starProjection' _ w

/-- `dΦ` commutes with the orthogonal projections onto the normal spaces `ν_f(x)` and
`ν_{Φ ∘ f}(x)`. -/
theorem mfderiv_starProjection_orthogonalNormalSpace (hΦ : IsLocalRiemannianIsometry J J' Φ)
    (hf : MDifferentiableAt I J f x) (w : TangentSpace J (f x)) :
    mfderiv J J' Φ (f x) ((orthogonalNormalSpace I J f x).starProjection w) =
      (orthogonalNormalSpace I J' (Φ ∘ f) x).starProjection (mfderiv J J' Φ (f x) w) := by
  rw [starProjection_orthogonalNormalSpace, starProjection_orthogonalNormalSpace,
    Submodule.starProjection_orthogonal_val, Submodule.starProjection_orthogonal_val, map_sub,
    hΦ.mfderiv_starProjection_range hf]

/-- `dΦ` maps the normal space of `f` at `x` onto the normal space of `Φ ∘ f` at `x`: a vector
`w` is normal to `f` exactly when `dΦ w` is normal to `Φ ∘ f`. -/
theorem mfderiv_mem_orthogonalNormalSpace_iff (hΦ : IsLocalRiemannianIsometry J J' Φ)
    (hf : MDifferentiableAt I J f x) (w : TangentSpace J (f x)) :
    mfderiv J J' Φ (f x) w ∈ orthogonalNormalSpace I J' (Φ ∘ f) x ↔
      w ∈ orthogonalNormalSpace I J f x := by
  rw [← Submodule.starProjection_eq_self_iff, ← Submodule.starProjection_eq_self_iff,
    ← hΦ.mfderiv_starProjection_orthogonalNormalSpace hf, (hΦ.mfderiv_injective _).eq_iff]

end Splitting

variable [IsManifold I 2 M] [IsManifold J 2 N] [IsManifold J' 2 N']
  [IsContMDiffRiemannianBundle J 1 F (fun y : N ↦ TangentSpace J y)]
  [IsContMDiffRiemannianBundle J' 1 F' (fun y : N' ↦ TangentSpace J' y)]
  {cov : CovariantDerivative J F (fun y : N ↦ TangentSpace J y)}
  {cov' : CovariantDerivative J' F' (fun y : N' ↦ TangentSpace J' y)}

/-! ### The second fundamental form, shape operator and normal connection of fields -/

section Fields

/-- **The second fundamental form under ambient isometries.** For a local Riemannian isometry
`Φ : N → N'`, Levi-Civita connections on `N` and `N'`, a map `f` which is `C²` at `x` and a vector
field `Y` differentiable at `x`, `dΦ (B_f(X, Y)) = B_{Φ ∘ f}(X, Y)` at `x`. -/
theorem mfderiv_immersionSecondFundamentalForm (hΦ : IsLocalRiemannianIsometry J J' Φ)
    (hcov : cov.IsLeviCivitaConnection) (hcov' : cov'.IsLeviCivitaConnection)
    (hf : ContMDiffAt I J 2 f x) (X : Π y : M, TangentSpace I y)
    {Y : Π y : M, TangentSpace I y} (hY : MDiffAt (T% Y) x) :
    mfderiv J J' Φ (f x) (immersionSecondFundamentalForm cov f X Y x) =
      immersionSecondFundamentalForm cov' (Φ ∘ f) X Y x := by
  have hfd : MDifferentiableAt I J f x := hf.mdifferentiableAt (by simp)
  -- Near `x`, the field `d(Φ ∘ f) Y` along `Φ ∘ f` is `dΦ (df Y)`.
  have hfield : ∀ᶠ y in 𝓝 x, mfderiv I J' (Φ ∘ f) y (Y y) =
      mfderiv J J' Φ (f y) (mfderiv I J f y (Y y)) := by
    filter_upwards [(contMDiffAt_iff_contMDiffAt_nhds (by simp)).1 hf] with y hy
    rw [mfderiv_comp y (hΦ.mdifferentiableAt (f y)) (hy.mdifferentiableAt (by simp)),
      ContinuousLinearMap.comp_apply]
  rw [immersionSecondFundamentalForm_def, immersionSecondFundamentalForm_def,
    cov'.alongMap_congr (Φ ∘ f) _ hfield, hΦ.mfderiv_starProjection_orthogonalNormalSpace hfd,
    hΦ.mfderiv_alongMap_of_isLeviCivitaConnection hcov hcov' hfd
      (hf.mdifferentiableAt_sectionCoord_mfderiv_of_mdifferentiableAt le_rfl hY)]

omit [IsManifold I 2 M] in
/-- **The shape operator under ambient isometries.** For a field `ν` along `f` with a
differentiable coordinate reading at `x`, `dΦ (S_ν X) = S'_{dΦ ν} X` at `x`, where `S'` is the
shape operator of `Φ ∘ f`. -/
theorem mfderiv_immersionShapeOperator (hΦ : IsLocalRiemannianIsometry J J' Φ)
    (hcov : cov.IsLeviCivitaConnection) (hcov' : cov'.IsLeviCivitaConnection)
    (hf : MDifferentiableAt I J f x) {ν : Π y : M, TangentSpace J (f y)}
    (hν : MDifferentiableAt I 𝓘(ℝ, F) (sectionCoord ℝ (F := F) f ν (f x)) x)
    (X : Π y : M, TangentSpace I y) :
    mfderiv J J' Φ (f x) (immersionShapeOperator cov f ν X x) =
      immersionShapeOperator cov' (Φ ∘ f) (fun y ↦ mfderiv J J' Φ (f y) (ν y)) X x := by
  rw [immersionShapeOperator_def, immersionShapeOperator_def, map_neg,
    hΦ.mfderiv_starProjection_range hf,
    hΦ.mfderiv_alongMap_of_isLeviCivitaConnection hcov hcov' hf hν]

omit [IsManifold I 2 M] in
/-- **The normal connection under ambient isometries.** For a field `ν` along `f` with a
differentiable coordinate reading at `x`, `dΦ (∇^⊥_X ν) = ∇'^⊥_X (dΦ ν)` at `x`, where `∇'^⊥` is
the normal connection of `Φ ∘ f`. -/
theorem mfderiv_immersionNormalConnection (hΦ : IsLocalRiemannianIsometry J J' Φ)
    (hcov : cov.IsLeviCivitaConnection) (hcov' : cov'.IsLeviCivitaConnection)
    (hf : MDifferentiableAt I J f x) {ν : Π y : M, TangentSpace J (f y)}
    (hν : MDifferentiableAt I 𝓘(ℝ, F) (sectionCoord ℝ (F := F) f ν (f x)) x)
    (X : Π y : M, TangentSpace I y) :
    mfderiv J J' Φ (f x) (immersionNormalConnection cov f ν X x) =
      immersionNormalConnection cov' (Φ ∘ f) (fun y ↦ mfderiv J J' Φ (f y) (ν y)) X x := by
  rw [immersionNormalConnection_def, immersionNormalConnection_def,
    hΦ.mfderiv_starProjection_orthogonalNormalSpace hf,
    hΦ.mfderiv_alongMap_of_isLeviCivitaConnection hcov hcov' hf hν]

end Fields

/-! ### Pointwise invariants -/

section Pointwise

variable [FiniteDimensional ℝ E]

/-- **The pointwise second fundamental form under ambient isometries**: for `f` which is `C²` at
`x`, `dΦ (B_x(v, w)) = B'_x(v, w)`, where `B'` is the second fundamental form of `Φ ∘ f`. -/
theorem mfderiv_immersionSecondFundamentalFormAt (hΦ : IsLocalRiemannianIsometry J J' Φ)
    (hcov : cov.IsLeviCivitaConnection) (hcov' : cov'.IsLeviCivitaConnection)
    (hf : ContMDiffAt I J 2 f x) (v w : TangentSpace I x) :
    mfderiv J J' Φ (f x) (immersionSecondFundamentalFormAt cov f x v w) =
      immersionSecondFundamentalFormAt cov' (Φ ∘ f) x v w := by
  have hΦf : ContMDiffAt I J' 2 (Φ ∘ f) x :=
    (hΦ.contMDiff.contMDiffAt.of_le (by simp)).comp x hf
  have hX := FiberBundle.mdifferentiableAt_extend I E v
  have hY := FiberBundle.mdifferentiableAt_extend I E w
  have h := immersionSecondFundamentalFormAt_apply (cov := cov) hf hX hY
  have h' := immersionSecondFundamentalFormAt_apply (cov := cov') hΦf hX hY
  rw [FiberBundle.extend_apply_self, FiberBundle.extend_apply_self] at h h'
  rw [h, h', hΦ.mfderiv_immersionSecondFundamentalForm hcov hcov' hf _ hY]

/-- The squared norm of the second fundamental form is invariant under ambient isometries. -/
theorem immersionSecondFundamentalFormNormSq_comp [RiemannianBundle (fun y : M ↦ TangentSpace I y)]
    (hΦ : IsLocalRiemannianIsometry J J' Φ)
    (hcov : cov.IsLeviCivitaConnection) (hcov' : cov'.IsLeviCivitaConnection)
    (hf : ContMDiffAt I J 2 f x) :
    immersionSecondFundamentalFormNormSq (I := I) cov' (Φ ∘ f) x =
      immersionSecondFundamentalFormNormSq (I := I) cov f x := by
  set b := stdOrthonormalBasis ℝ (TangentSpace I x)
  rw [immersionSecondFundamentalFormNormSq_eq_sum b, immersionSecondFundamentalFormNormSq_eq_sum b]
  simp only [← hΦ.mfderiv_immersionSecondFundamentalFormAt hcov hcov' hf, hΦ.norm_mfderiv]

variable [RiemannianBundle (fun y : M ↦ TangentSpace I y)]

/-- **The shape operator under ambient isometries**: the pointwise shape operator of `Φ ∘ f` in
the direction `dΦ ν` is the shape operator of `f` in the direction `ν`. -/
theorem immersionShapeOperatorAt_comp (hΦ : IsLocalRiemannianIsometry J J' Φ)
    (hcov : cov.IsLeviCivitaConnection) (hcov' : cov'.IsLeviCivitaConnection)
    (hf : ContMDiffAt I J 2 f x) (ν : TangentSpace J (f x)) :
    immersionShapeOperatorAt (I := I) cov' (Φ ∘ f) x (mfderiv J J' Φ (f x) ν) =
      immersionShapeOperatorAt (I := I) cov f x ν := by
  symm
  rw [eq_immersionShapeOperatorAt_iff]
  intro v w
  rw [inner_immersionShapeOperatorAt, ← hΦ.mfderiv_immersionSecondFundamentalFormAt hcov hcov' hf,
    hΦ.inner_mfderiv]

/-- **The principal curvatures under ambient isometries**: the principal curvatures of `Φ ∘ f` in
the direction `dΦ ν` are those of `f` in the direction `ν`. -/
theorem immersionPrincipalCurvatures_comp (hΦ : IsLocalRiemannianIsometry J J' Φ)
    (hcov : cov.IsLeviCivitaConnection) (hcov' : cov'.IsLeviCivitaConnection)
    (hf : ContMDiffAt I J 2 f x) {m : ℕ} (hm : finrank ℝ E = m) (ν : TangentSpace J (f x)) :
    immersionPrincipalCurvatures I (Φ ∘ f) x
        ((cov'.isTorsionFree_iff_torsion_eq_zero).2 hcov'.torsion) hm (mfderiv J J' Φ (f x) ν) =
      immersionPrincipalCurvatures I f x ((cov.isTorsionFree_iff_torsion_eq_zero).2 hcov.torsion)
        hm ν := by
  have ht := (cov.isTorsionFree_iff_torsion_eq_zero).2 hcov.torsion
  have ht' := (cov'.isTorsionFree_iff_torsion_eq_zero).2 hcov'.torsion
  -- Both lists are the sorted eigenvalues of the same self-adjoint operator.
  have hS := isSymmetric_immersionShapeOperatorAt (I := I) (x := x) ht ν
  let b := (hS.eigenvectorBasis (hm : finrank ℝ (TangentSpace I x) = m)).toBasis
  have hb (i : Fin m) : immersionShapeOperatorAt cov f x ν (b i) =
      hS.eigenvalues (hm : finrank ℝ (TangentSpace I x) = m) i • b i := by
    simpa [b] using hS.apply_eigenvectorBasis hm i
  have hb' (i : Fin m) : immersionShapeOperatorAt cov' (Φ ∘ f) x (mfderiv J J' Φ (f x) ν) (b i) =
      hS.eigenvalues (hm : finrank ℝ (TangentSpace I x) = m) i • b i := by
    rw [hΦ.immersionShapeOperatorAt_comp hcov hcov' hf ν, hb]
  rw [immersionPrincipalCurvatures_eq_of_eigenbasis ht hm ν b (hS.eigenvalues_antitone _) hb,
    immersionPrincipalCurvatures_eq_of_eigenbasis ht' hm _ b (hS.eigenvalues_antitone _) hb']

/-- **The mean curvature vector under ambient isometries**: `dΦ H_f = H_{Φ ∘ f}` at a point where
`f` is `C²`. -/
theorem mfderiv_immersionMeanCurvatureVector (hΦ : IsLocalRiemannianIsometry J J' Φ)
    (hcov : cov.IsLeviCivitaConnection) (hcov' : cov'.IsLeviCivitaConnection)
    (hf : ContMDiffAt I J 2 f x) :
    mfderiv J J' Φ (f x) (immersionMeanCurvatureVector (I := I) cov f x) =
      immersionMeanCurvatureVector (I := I) cov' (Φ ∘ f) x := by
  set b := stdOrthonormalBasis ℝ (TangentSpace I x)
  rw [immersionMeanCurvatureVector_eq_sum b, immersionMeanCurvatureVector_eq_sum b, map_smul,
    map_sum]
  simp only [hΦ.mfderiv_immersionSecondFundamentalFormAt hcov hcov' hf]

/-- **Minimality is invariant under ambient isometries**: `Φ ∘ f` is minimal at `x` exactly when
`f` is. -/
theorem immersionMeanCurvatureVector_comp_eq_zero_iff (hΦ : IsLocalRiemannianIsometry J J' Φ)
    (hcov : cov.IsLeviCivitaConnection) (hcov' : cov'.IsLeviCivitaConnection)
    (hf : ContMDiffAt I J 2 f x) :
    immersionMeanCurvatureVector (I := I) cov' (Φ ∘ f) x = 0 ↔
      immersionMeanCurvatureVector (I := I) cov f x = 0 := by
  rw [← hΦ.mfderiv_immersionMeanCurvatureVector hcov hcov' hf]
  exact map_eq_zero_iff _ (hΦ.mfderiv_injective _)

end Pointwise

end IsLocalRiemannianIsometry

/-! ### Restriction of the ambient manifold to an open subset -/

section AmbientRestriction

open scoped TauCeti

variable [IsManifold I 2 M] [IsManifold J 2 N]
  [IsContMDiffRiemannianBundle J 1 F (fun y : N ↦ TangentSpace J y)]
  {U : TopologicalSpace.Opens N}
  {cov : CovariantDerivative J F (fun y : N ↦ TangentSpace J y)}
  {covU : CovariantDerivative J F (fun y : U ↦ TangentSpace J y)}
  {φ : M → U}

/-- **The second fundamental form is local in the ambient manifold**: for a map `φ` into an open
subset `U ⊆ N` with the restricted metric, `B_{ι ∘ φ}(X, Y) = B_φ(X, Y)`, where `ι : U → N` is the
inclusion. -/
theorem immersionSecondFundamentalForm_subtypeVal_comp (hcov : cov.IsLeviCivitaConnection)
    (hcovU : covU.IsLeviCivitaConnection) (hφ : ContMDiffAt I J 2 φ x)
    (X : Π y : M, TangentSpace I y) {Y : Π y : M, TangentSpace I y} (hY : MDiffAt (T% Y) x) :
    immersionSecondFundamentalForm cov (Subtype.val ∘ φ) X Y x =
      immersionSecondFundamentalForm covU φ X Y x := by
  rw [← (IsLocalRiemannianIsometry.subtype_val (I := J) U).mfderiv_immersionSecondFundamentalForm
    hcovU hcov hφ X hY, mfderiv_subtype_val_apply]

omit [IsManifold I 2 M] in
/-- **The shape operator is local in the ambient manifold**: for a map `φ` into an open subset
`U ⊆ N` and a field `ν` along `φ`, `S^{ι ∘ φ}_ν X = S^φ_ν X`. -/
theorem immersionShapeOperator_subtypeVal_comp (hcov : cov.IsLeviCivitaConnection)
    (hcovU : covU.IsLeviCivitaConnection) (hφ : MDifferentiableAt I J φ x)
    {ν : Π y : M, TangentSpace J (φ y)}
    (hν : MDifferentiableAt I 𝓘(ℝ, F) (sectionCoord ℝ (F := F) φ ν (φ x)) x)
    (X : Π y : M, TangentSpace I y) :
    immersionShapeOperator cov (Subtype.val ∘ φ) ν X x = immersionShapeOperator covU φ ν X x := by
  have h := (IsLocalRiemannianIsometry.subtype_val (I := J) U).mfderiv_immersionShapeOperator
    hcovU hcov hφ hν X
  simp only [mfderiv_subtype_val_apply] at h
  exact h.symm

omit [IsManifold I 2 M] in
/-- **The normal connection is local in the ambient manifold**: for a map `φ` into an open subset
`U ⊆ N` and a field `ν` along `φ`, `∇^{⊥, ι ∘ φ}_X ν = ∇^{⊥, φ}_X ν`. -/
theorem immersionNormalConnection_subtypeVal_comp (hcov : cov.IsLeviCivitaConnection)
    (hcovU : covU.IsLeviCivitaConnection) (hφ : MDifferentiableAt I J φ x)
    {ν : Π y : M, TangentSpace J (φ y)}
    (hν : MDifferentiableAt I 𝓘(ℝ, F) (sectionCoord ℝ (F := F) φ ν (φ x)) x)
    (X : Π y : M, TangentSpace I y) :
    immersionNormalConnection cov (Subtype.val ∘ φ) ν X x =
      immersionNormalConnection covU φ ν X x := by
  have h := (IsLocalRiemannianIsometry.subtype_val (I := J) U).mfderiv_immersionNormalConnection
    hcovU hcov hφ hν X
  simp only [mfderiv_subtype_val_apply] at h
  exact h.symm

variable [FiniteDimensional ℝ E]

/-- **The pointwise second fundamental form is local in the ambient manifold**:
`B^{ι ∘ φ}_x(v, w) = B^φ_x(v, w)` for a map `φ` into an open subset `U ⊆ N`. -/
theorem immersionSecondFundamentalFormAt_subtypeVal_comp (hcov : cov.IsLeviCivitaConnection)
    (hcovU : covU.IsLeviCivitaConnection) (hφ : ContMDiffAt I J 2 φ x) (v w : TangentSpace I x) :
    immersionSecondFundamentalFormAt cov (Subtype.val ∘ φ) x v w =
      immersionSecondFundamentalFormAt covU φ x v w := by
  rw [← (IsLocalRiemannianIsometry.subtype_val (I := J) U).mfderiv_immersionSecondFundamentalFormAt
    hcovU hcov hφ v w, mfderiv_subtype_val_apply]

variable [RiemannianBundle (fun y : M ↦ TangentSpace I y)]

/-- **The pointwise shape operator is local in the ambient manifold**: for a map `φ` into an open
subset `U ⊆ N`, the shape operators of `ι ∘ φ` and `φ` in a normal direction `ν` agree. -/
theorem immersionShapeOperatorAt_subtypeVal_comp (hcov : cov.IsLeviCivitaConnection)
    (hcovU : covU.IsLeviCivitaConnection) (hφ : ContMDiffAt I J 2 φ x)
    (ν : TangentSpace J (φ x)) :
    immersionShapeOperatorAt (I := I) cov (Subtype.val ∘ φ) x ν =
      immersionShapeOperatorAt (I := I) covU φ x ν := by
  have h := (IsLocalRiemannianIsometry.subtype_val (I := J) U).immersionShapeOperatorAt_comp
    hcovU hcov hφ ν
  rwa [mfderiv_subtype_val_apply] at h

/-- **The principal curvatures are local in the ambient manifold**: for a map `φ` into an open
subset `U ⊆ N`, the principal curvatures of `ι ∘ φ` and `φ` in a normal direction `ν` agree. -/
theorem immersionPrincipalCurvatures_subtypeVal_comp (hcov : cov.IsLeviCivitaConnection)
    (hcovU : covU.IsLeviCivitaConnection) (hφ : ContMDiffAt I J 2 φ x) {m : ℕ}
    (hm : finrank ℝ E = m) (ν : TangentSpace J (φ x)) :
    immersionPrincipalCurvatures I (Subtype.val ∘ φ) x
        ((cov.isTorsionFree_iff_torsion_eq_zero).2 hcov.torsion) hm ν =
      immersionPrincipalCurvatures I φ x
        ((covU.isTorsionFree_iff_torsion_eq_zero).2 hcovU.torsion) hm ν := by
  have h := (IsLocalRiemannianIsometry.subtype_val (I := J) U).immersionPrincipalCurvatures_comp
    hcovU hcov hφ hm ν
  rwa [mfderiv_subtype_val_apply] at h

/-- **The mean curvature vector is local in the ambient manifold**: `H_{ι ∘ φ} = H_φ` for a map
`φ` into an open subset `U ⊆ N`. In particular `ι ∘ φ` is minimal at `x` exactly when `φ` is. -/
theorem immersionMeanCurvatureVector_subtypeVal_comp (hcov : cov.IsLeviCivitaConnection)
    (hcovU : covU.IsLeviCivitaConnection) (hφ : ContMDiffAt I J 2 φ x) :
    immersionMeanCurvatureVector (I := I) cov (Subtype.val ∘ φ) x =
      immersionMeanCurvatureVector (I := I) covU φ x := by
  rw [← (IsLocalRiemannianIsometry.subtype_val (I := J) U).mfderiv_immersionMeanCurvatureVector
    hcovU hcov hφ, mfderiv_subtype_val_apply]

end AmbientRestriction

end TauCeti

end
