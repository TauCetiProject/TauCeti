/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.Associated.Basic
public import TauCeti.Topology.VectorBundle.Riemannian.Hermitian
public import Mathlib.Analysis.InnerProductSpace.LinearMap
public import Mathlib.Topology.MetricSpace.IsometricSMul

/-!
# Metrics on associated vector bundles

An isometric linear group action induces a metric on its associated vector bundle. The native
norm and inner product on each fibre retain the existing topology and scalar action. Every
principal frame identifies the model with the fibre by a linear isometry, so the metric does
not depend on the frame. The fibre norm is continuous on the existing total space.

The construction works over both real and complex scalars. In the complex case its inner
product is conjugate-linear in the first slot, as in the model Hermitian space.

## References

* S. Kobayashi and K. Nomizu, *Foundations of Differential Geometry*, volume I, Chapter I, §5.
* I. Kolář, P. W. Michor, J. Slovák, *Natural Operations in Differential Geometry*, §10.7.
-/

public noncomputable section

open Bundle MulOpposite
open scoped InnerProductSpace

namespace TauCeti.AssociatedBundle

variable {𝕜 B G F : Type*}
  [TopologicalSpace B] [Group G] [TopologicalSpace G]
  {P : B → Type*} [TopologicalSpace (TotalSpace G P)] [∀ b, TopologicalSpace (P b)]
  [FiberBundle G P] [∀ b, MulAction Gᵐᵒᵖ (P b)] [PrincipalBundle G P]
  [NormedAddCommGroup F] [DistribMulAction G F] [ContinuousSMul G F]

/-- The normed additive structure of an associated fibre is the model's structure, with
precisely the original fibre topology and addition. -/
instance instNormedAddCommGroup (b : B) : NormedAddCommGroup (AssociatedBundle G P F b) := by
  let k : NormedAddCommGroup (AssociatedBundle G P F b) := inferInstanceAs (NormedAddCommGroup F)
  -- Preserve the existing fibre topology through the normed-group parent projection.
  exact { k with toMetricSpace := k.toMetricSpace.replaceTopology rfl }

variable [hiso : IsIsometricSMul G F]

/-- Every principal frame preserves the norm of the model vector. -/
@[simp]
theorem norm_mk {b : B} (p : P b) (v : F) : ‖mk G p v‖ = ‖v‖ := by
  rw [mk_def]
  -- The fibre synonym carries the model norm by construction, so this is a norm identity in F.
  exact (isometry_smul F _).norm_map_of_map_zero (smul_zero _) v

/-- Associated chart coordinates preserve the fibre norm on their domain. -/
theorem norm_trivializationAt {i b : B} (hb : b ∈ (trivializationAt G P i).baseSet)
    (v : AssociatedBundle G P F b) :
    ‖(trivializationAt F (AssociatedBundle G P F) i ⟨b, v⟩).2‖ = ‖v‖ := by
  obtain ⟨p, w, rfl⟩ := exists_mk v
  rw [trivializationAt_mk_snd hb, norm_mk]
  exact (isometry_smul F _).norm_map_of_map_zero (smul_zero _) w

variable [NontriviallyNormedField 𝕜]

/-- The associated fibre retains the model's normed scalar action and its existing module. -/
instance instNormedSpace [NormedSpace 𝕜 F] [SMulCommClass G 𝕜 F] (b : B) :
    NormedSpace 𝕜 (AssociatedBundle G P F b) where
  -- Keep the existing module parent, which is opaque to importing consumers.
  toModule := instModule b
  norm_smul_le c v := by
    obtain ⟨p, w, rfl⟩ := exists_mk v
    rw [← mk_smul_scalar, norm_mk, norm_mk]
    exact norm_smul_le c w

/-- The scalar norm law is delegated on the associated-fibre presentation, through which
typeclass matching need not unfold the native normed-space instance. -/
instance instNormSMulClass [NormedSpace 𝕜 F] [SMulCommClass G 𝕜 F] (b : B) :
    NormSMulClass 𝕜 (AssociatedBundle G P F b) :=
  @NormedSpace.toNormSMulClass 𝕜 _ _ _ (instNormedSpace b)

variable (𝕜 G) in
/-- A principal frame identifies the model and the associated fibre by a linear isometry. -/
def mkLinearIsometryEquiv [NormedSpace 𝕜 F] [SMulCommClass G 𝕜 F] {b : B} (p : P b) :
    F ≃ₗᵢ[𝕜] AssociatedBundle G P F b where
  toLinearEquiv := (mkContinuousLinearEquiv 𝕜 G p).toLinearEquiv
  norm_map' v := by
    simpa only [ContinuousLinearEquiv.coe_toLinearEquiv, mkContinuousLinearEquiv_apply] using
      norm_mk (G := G) p v

include hiso in
/-- The isometric frame identification is the existing associated class map. -/
@[simp]
theorem mkLinearIsometryEquiv_apply [NormedSpace 𝕜 F] [SMulCommClass G 𝕜 F]
    {b : B} (p : P b) (v : F) :
    mkLinearIsometryEquiv 𝕜 G p v = mk G p v := by
  simp only [mkLinearIsometryEquiv, LinearIsometryEquiv.coe_mk,
    ContinuousLinearEquiv.coe_toLinearEquiv, mkContinuousLinearEquiv_apply]

/-- Forgetting the metric recovers the existing continuous linear frame identification. -/
@[simp]
theorem toContinuousLinearEquiv_mkLinearIsometryEquiv [NormedSpace 𝕜 F]
    [SMulCommClass G 𝕜 F] {b : B} (p : P b) :
    (mkLinearIsometryEquiv (F := F) 𝕜 G p).toContinuousLinearEquiv =
      mkContinuousLinearEquiv 𝕜 G p := by
  ext v
  simp only [LinearIsometryEquiv.coe_toContinuousLinearEquiv, mkLinearIsometryEquiv_apply]
  exact (mkContinuousLinearEquiv_apply (𝕜 := 𝕜) (G := G) p v).symm

/-- Reading a class in a principal frame acts by the principal division element. -/
@[simp]
theorem mkLinearIsometryEquiv_symm_apply_mk [NormedSpace 𝕜 F] [SMulCommClass G 𝕜 F]
    {b : B} (p q : P b) (v : F) :
    (mkLinearIsometryEquiv 𝕜 G p).symm (mk G q v) = PrincipalBundle.division G p q • v := by
  apply (mkLinearIsometryEquiv 𝕜 G p).injective
  simp only [LinearIsometryEquiv.apply_symm_apply, mkLinearIsometryEquiv_apply]
  exact ((mk_eq_mk_iff (p := p) (q := q)).mpr rfl).symm

/-- The associated norm is continuous on the total space for an isometric action. -/
instance instContinuousFiberNorm : ContinuousFiberNorm F (AssociatedBundle G P F) where
  continuous_norm := by
    apply (isOpenQuotientMap_totalSpaceMk_mk G P F).isQuotientMap.continuous_iff.mpr
    simpa only [Function.comp_def, norm_mk] using continuous_norm.comp continuous_snd

variable {𝕜' : Type*} [RCLike 𝕜'] [InnerProductSpace 𝕜' F] [SMulCommClass G 𝕜' F]

/-- The associated Hermitian or real inner product is the model's inner product in its
preferred frame, with the existing norm and module structure. -/
instance instInnerProductSpace (b : B) : InnerProductSpace 𝕜' (AssociatedBundle G P F b) := by
  let k : InnerProductSpace 𝕜' (AssociatedBundle G P F b) :=
    inferInstanceAs (InnerProductSpace 𝕜' F)
  -- The inner product shares the native normed-space and module data above.
  exact { k with toNormedSpace := instNormedSpace (𝕜 := 𝕜') b }

/-- Inner products in every principal frame equal those in the model space. -/
@[simp]
theorem inner_mk {b : B} (p : P b) (v w : F) :
    ⟪mk G p v, mk G p w⟫_𝕜' = ⟪v, w⟫_𝕜' := by
  simpa only [mkLinearIsometryEquiv_apply] using
    LinearIsometryEquiv.inner_map_map (E := F) (E' := AssociatedBundle G P F b)
      (mkLinearIsometryEquiv 𝕜' G p) v w

/-- Associated chart coordinates preserve the Hermitian or real inner product. -/
theorem inner_trivializationAt {i b : B}
    (hb : b ∈ (trivializationAt G P i).baseSet) (v w : AssociatedBundle G P F b) :
    ⟪(trivializationAt F (AssociatedBundle G P F) i ⟨b, v⟩).2,
      (trivializationAt F (AssociatedBundle G P F) i ⟨b, w⟩).2⟫_𝕜' = ⟪v, w⟫_𝕜' := by
  let e := trivializationAt F (AssociatedBundle G P F) i
  let : e.IsLinear 𝕜' := by
    dsimp only [e]
    rw [trivializationAt_eq_localTriv]
    infer_instance
  have hbe : b ∈ e.baseSet := by simpa only [e, baseSet_trivializationAt] using hb
  let L : AssociatedBundle G P F b →ₗᵢ[𝕜'] F :=
    { toLinearMap := (e.linearEquivAt 𝕜' b hbe).toLinearMap
      norm_map' := norm_trivializationAt hb }
  exact L.inner_map_map v w

end TauCeti.AssociatedBundle
