/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Tangent.Basic
public import TauCeti.Topology.VectorBundle.GrassmannBundle.Map

/-!
# Riemannian isometries act on Grassmann bundles

Let `(M, g)` and `(N, h)` be Riemannian manifolds and
`G_k(M) = grassmannBundle E (TangentSpace I) k` the Grassmann bundle of `k`-planes of the tangent
bundle, whose points are pairs `(x, P)` of a point `x` and a `g_x`-orthogonal projection `P` of
rank `k` of `T_xM`. A smooth Riemannian isometry `Φ : M → N` has differentials
`dΦ_x : T_xM ≃ₗᵢ[ℝ] T_{Φ x}N` (`TauCeti.RiemannianIsometry.mfderivToLinearIsometryEquiv`), which
are continuous in tangent coordinates
(`TauCeti.RiemannianIsometry.continuousAt_inCoordinates_mfderivToLinearIsometryEquiv`) because
`Φ` is `C¹`. Hence `Φ` induces the continuous map

`(x, P) ↦ (Φ x, dΦ_x P dΦ_x⁻¹)`

of Grassmann bundles (`TauCeti.grassmannBundle.map`, `TauCeti.grassmannBundle.continuous_map`),
whose inverse is the map induced by `Φ⁻¹`, since `d(Φ⁻¹)_{Φ x} = dΦ_x⁻¹`. This is the
homeomorphism `TauCeti.RiemannianIsometry.grassmannBundleHomeomorph`, an instance of the
homeomorphism `TauCeti.grassmannBundle.mapHomeomorphOfInverse` induced by mutually inverse maps of
bundles; no compactness, finite dimension or separation is needed. It is functorial: the
identity isometry induces the identity
(`TauCeti.RiemannianIsometry.grassmannBundleHomeomorph_refl`), a composite of isometries induces
the composite (`TauCeti.RiemannianIsometry.grassmannBundleHomeomorph_trans`, by the chain rule),
and the inverse isometry induces the inverse homeomorphism
(`TauCeti.RiemannianIsometry.grassmannBundleHomeomorph_symm`).

Only smooth isometries are covered here, since `TauCeti.RiemannianIsometry` extends a smooth
diffeomorphism; the case of an isometry that is only a `C¹` diffeomorphism is not treated.

## Main declarations

* `TauCeti.RiemannianIsometry.grassmannBundleHomeomorph`: the homeomorphism `G_k(M) ≃ₜ G_k(N)`
  induced by a smooth Riemannian isometry, with `coe_grassmannBundleHomeomorph_apply` and
  `proj_grassmannBundleHomeomorph`.
* `TauCeti.RiemannianIsometry.grassmannBundleHomeomorph_refl`,
  `TauCeti.RiemannianIsometry.grassmannBundleHomeomorph_trans`,
  `TauCeti.RiemannianIsometry.grassmannBundleHomeomorph_symm`: functoriality.

## References

* L. Simon, *Lectures on Geometric Measure Theory*, Proceedings of the Centre for Mathematical
  Analysis, Australian National University 3, 1983, §38.
-/

public section

noncomputable section

open Bundle Manifold ContinuousLinearMap
open scoped ContDiff Manifold Topology

namespace TauCeti.RiemannianIsometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  [RiemannianBundle (fun y : N ↦ TangentSpace J y)]

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
  {H'' : Type*} [TopologicalSpace H''] {K : ModelWithCorners ℝ G H''}
  {P : Type*} [TopologicalSpace P] [ChartedSpace H'' P]
  [RiemannianBundle (fun z : P ↦ TangentSpace K z)]

/-- On the tangent bundle, `(Φ⁻¹, dΦ⁻¹)` undoes `(Φ, dΦ)`, since the differential of `Φ⁻¹` at
`Φ x` inverts the differential of `Φ` at `x`. -/
private theorem mk_symm_mfderivToLinearIsometryEquiv (Φ : RiemannianIsometry I J M N) (x : M)
    (v : TangentSpace I x) :
    (⟨Φ.symm (Φ x), Φ.symm.mfderivToLinearIsometryEquiv (Φ x)
      (Φ.mfderivToLinearIsometryEquiv x v)⟩ : TotalSpace E (TangentSpace I : M → Type _)) =
      ⟨x, v⟩ := by
  refine TotalSpace.ext (Φ.symm_apply_apply x) (heq_of_eq ?_)
  rw [mfderivToLinearIsometryEquiv_apply Φ.symm, ← mfderivToLinearIsometryEquiv_symm_apply,
    LinearIsometryEquiv.symm_apply_apply]

variable [IsManifold I 1 M] [IsManifold J 1 N] [CompleteSpace E] [CompleteSpace F]

variable (k : ℕ) in
/-- **The homeomorphism of Grassmann bundles induced by a smooth Riemannian isometry**
`Φ : M → N`: `(x, P) ↦ (Φ x, dΦ_x P dΦ_x⁻¹)`, with inverse induced by `Φ⁻¹`. -/
def grassmannBundleHomeomorph (Φ : RiemannianIsometry I J M N) :
    grassmannBundle E (TangentSpace I : M → Type _) k ≃ₜ
      grassmannBundle F (TangentSpace J : N → Type _) k :=
  grassmannBundle.mapHomeomorphOfInverse k Φ Φ.mfderivToLinearIsometryEquiv Φ.symm
    Φ.symm.mfderivToLinearIsometryEquiv (mk_symm_mfderivToLinearIsometryEquiv Φ)
    (fun y v ↦ by
      have h := mk_symm_mfderivToLinearIsometryEquiv Φ.symm y v
      rwa [symm_symm] at h)
    (by rw [← coe_toDiffeomorph]; exact Φ.toDiffeomorph.continuous)
    (by rw [← coe_toDiffeomorph]; exact Φ.symm.toDiffeomorph.continuous)
    Φ.continuousAt_inCoordinates_mfderivToLinearIsometryEquiv
    Φ.symm.continuousAt_inCoordinates_mfderivToLinearIsometryEquiv

/-- The induced homeomorphism is the map of Grassmann bundles induced by the differentials. -/
theorem coe_grassmannBundleHomeomorph (Φ : RiemannianIsometry I J M N) :
    (grassmannBundleHomeomorph k Φ : grassmannBundle E (TangentSpace I : M → Type _) k →
      grassmannBundle F (TangentSpace J : N → Type _) k) =
      grassmannBundle.map Φ Φ.mfderivToLinearIsometryEquiv :=
  grassmannBundle.coe_mapHomeomorphOfInverse ..

/-- The induced homeomorphism sends `(x, P)` to `(Φ x, dΦ_x P dΦ_x⁻¹)`. -/
@[simp]
theorem coe_grassmannBundleHomeomorph_apply (Φ : RiemannianIsometry I J M N)
    (p : grassmannBundle E (TangentSpace I : M → Type _) k) :
    (grassmannBundleHomeomorph k Φ p).val =
      ⟨Φ p.val.proj, (Φ.mfderivToLinearIsometryEquiv p.val.proj).conjStarAlgEquiv p.val.snd⟩ := by
  rw [coe_grassmannBundleHomeomorph, grassmannBundle.coe_map_apply]

/-- The induced homeomorphism covers `Φ`. -/
@[simp]
theorem proj_grassmannBundleHomeomorph (Φ : RiemannianIsometry I J M N)
    (p : grassmannBundle E (TangentSpace I : M → Type _) k) :
    grassmannBundle.proj (grassmannBundleHomeomorph k Φ p) = Φ (grassmannBundle.proj p) := by
  rw [coe_grassmannBundleHomeomorph, grassmannBundle.proj_map]

/-- The inverse isometry induces the inverse homeomorphism. -/
@[simp]
theorem grassmannBundleHomeomorph_symm (Φ : RiemannianIsometry I J M N) :
    (grassmannBundleHomeomorph k Φ).symm = grassmannBundleHomeomorph k Φ.symm := by
  refine Homeomorph.ext (congrFun ?_)
  rw [coe_grassmannBundleHomeomorph, grassmannBundleHomeomorph,
    grassmannBundle.coe_mapHomeomorphOfInverse_symm]

variable (I M k) in
/-- The identity isometry induces the identity of the Grassmann bundle. -/
@[simp]
theorem grassmannBundleHomeomorph_refl :
    grassmannBundleHomeomorph k (RiemannianIsometry.refl I M) =
      Homeomorph.refl (grassmannBundle E (TangentSpace I : M → Type _) k) := by
  refine Homeomorph.ext (congrFun ?_)
  rw [Homeomorph.refl_apply, coe_grassmannBundleHomeomorph, ← grassmannBundle.map_id]
  exact grassmannBundle.map_congr fun x v ↦
    TotalSpace.ext (refl_apply I M x) (heq_of_eq (mfderivToLinearIsometryEquiv_refl_apply x v))

/-- **Functoriality**: a composite of isometries induces the composite of the induced
homeomorphisms. -/
theorem grassmannBundleHomeomorph_trans [IsManifold K 1 P] [CompleteSpace G]
    (Φ : RiemannianIsometry I J M N) (Ψ : RiemannianIsometry J K N P) :
    grassmannBundleHomeomorph k (Φ.trans Ψ) =
      (grassmannBundleHomeomorph k Φ).trans (grassmannBundleHomeomorph k Ψ) := by
  refine Homeomorph.ext fun p ↦ ?_
  rw [Homeomorph.trans_apply, coe_grassmannBundleHomeomorph, coe_grassmannBundleHomeomorph,
    coe_grassmannBundleHomeomorph, ← Function.comp_apply (f := grassmannBundle.map Ψ _),
    ← grassmannBundle.map_comp]
  exact congrFun (grassmannBundle.map_congr fun x v ↦ TotalSpace.ext (trans_apply Φ Ψ x)
    (heq_of_eq (mfderivToLinearIsometryEquiv_trans_apply Φ Ψ x v))) p

end TauCeti.RiemannianIsometry
