/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.Associated.Basic
public import TauCeti.Topology.FiberBundle.Associated.Map
public import Mathlib.Topology.VectorBundle.Hom

/-!
# Linear intertwiners on associated vector bundles

A continuous linear intertwiner induces continuous linear maps on the fibres of associated
bundles. These are the existing associated maps, now bundled linearly, rather than maps on a
second quotient. In any common principal frame they are exactly the original intertwiner.
In particular they are independent of the frame, respect composition, and induce a continuous
section of the native Hom bundle. Equivariant continuous linear equivalences induce fibrewise
continuous linear equivalences.

This interface lets representation comparisons be used as vector-bundle maps, for example when
identifying different models of a spinor representation. No fibre norm, invariant metric, or
finite-dimensionality is required for the fibre maps. The Hom-bundle assertions assume native
vector-bundle structures on the source and target.

## References

* I. Kolář, P. W. Michor and J. Slovák, *Natural Operations in Differential Geometry*,
  Springer, 1993, §§10.7 and 10.9.
-/

public noncomputable section

open Bundle MulOpposite TauCeti TauCeti.AssociatedBundle
open scoped Topology

variable {𝕜 B G F F' F'' : Type*} [NontriviallyNormedField 𝕜]
  [TopologicalSpace B] [Group G] [TopologicalSpace G]
  {P : B → Type*} [TopologicalSpace (TotalSpace G P)] [∀ b, TopologicalSpace (P b)]
  [FiberBundle G P] [∀ b, MulAction Gᵐᵒᵖ (P b)] [PrincipalBundle G P]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [DistribMulAction G F] [SMulCommClass G 𝕜 F] [ContinuousSMul G F]
  [NormedAddCommGroup F'] [NormedSpace 𝕜 F']
  [DistribMulAction G F'] [SMulCommClass G 𝕜 F'] [ContinuousSMul G F']
  [NormedAddCommGroup F''] [NormedSpace 𝕜 F'']
  [DistribMulAction G F''] [SMulCommClass G 𝕜 F''] [ContinuousSMul G F'']

namespace ContinuousLinearMap

/-- The continuous linear map on associated fibres induced by a continuous linear intertwiner.
It is characterized in every principal frame by `associatedBundleMap_mk`. -/
def associatedBundleMap (f : F →L[𝕜] F')
    (hf : ∀ (g : G) v, f (g • v) = g • f v) (b : B) :
    AssociatedBundle G P F b →L[𝕜] AssociatedBundle G P F' b where
  toFun := TauCeti.AssociatedBundle.map (⟨f, hf⟩ : F →[G] F')
  map_add' v w := by
    obtain ⟨p, v, rfl⟩ := exists_mk v
    obtain ⟨w, rfl⟩ := (mk_bijective (F := F) p).surjective w
    simp only [← mk_add, map_mk]
    exact congrArg (AssociatedBundle.mk G p) (f.map_add v w)
  map_smul' r v := by
    obtain ⟨p, v, rfl⟩ := exists_mk v
    simp only [← mk_smul_scalar, map_mk, RingHom.id_apply]
    exact congrArg (AssociatedBundle.mk G p) (f.map_smul r v)
  cont := by
    let p := (FiberBundle.homeomorphAt G P b).symm 1
    let e := mkContinuousLinearEquiv 𝕜 G (F := F) p
    let e' := mkContinuousLinearEquiv 𝕜 G (F := F') p
    apply (e'.continuous.comp (f.continuous.comp e.symm.continuous)).congr
    intro v
    obtain ⟨w, rfl⟩ := e.surjective v
    simp only [Function.comp_apply, ContinuousLinearEquiv.symm_apply_apply]
    rw [mkContinuousLinearEquiv_apply, mkContinuousLinearEquiv_apply, map_mk]
    rfl

/-- The bundled fibre map is the existing associated map of the intertwiner. -/
theorem associatedBundleMap_apply (f : F →L[𝕜] F')
    (hf : ∀ (g : G) v, f (g • v) = g • f v) {b : B} (v : AssociatedBundle G P F b) :
    f.associatedBundleMap hf b v = TauCeti.AssociatedBundle.map (⟨f, hf⟩ : F →[G] F') v :=
  (rfl)

/-- An intertwiner acts by the original model operator in every principal frame. -/
@[simp]
theorem associatedBundleMap_mk (f : F →L[𝕜] F')
    (hf : ∀ (g : G) v, f (g • v) = g • f v) {b : B} (p : P b) (v : F) :
    f.associatedBundleMap hf b (AssociatedBundle.mk G p v) = AssociatedBundle.mk G p (f v) :=
  map_mk _ p v

/-- The formula in one principal frame uniquely determines the induced linear map. -/
theorem associatedBundleMap_unique (f : F →L[𝕜] F')
    (hf : ∀ (g : G) v, f (g • v) = g • f v) {b : B} (p : P b)
    (T : AssociatedBundle G P F b →L[𝕜] AssociatedBundle G P F' b)
    (hT : ∀ v, T (AssociatedBundle.mk G p v) = AssociatedBundle.mk G p (f v)) :
    T = f.associatedBundleMap hf b := by
  ext v
  obtain ⟨v, rfl⟩ := (mk_bijective p).surjective v
  exact (hT v).trans (f.associatedBundleMap_mk hf p v).symm

/-- Associating the identity intertwiner gives the identity fibre operator. -/
@[simp]
theorem associatedBundleMap_id (b : B) :
    (ContinuousLinearMap.id 𝕜 F).associatedBundleMap (P := P) (fun _ _ ↦ rfl) b =
      ContinuousLinearMap.id 𝕜 (AssociatedBundle G P F b) := by
  ext v
  obtain ⟨p, v, rfl⟩ := exists_mk v
  exact associatedBundleMap_mk _ _ p v

/-- Association preserves composition of continuous linear intertwiners. -/
theorem associatedBundleMap_comp (f : F →L[𝕜] F') (f' : F' →L[𝕜] F'')
    (hf : ∀ (g : G) v, f (g • v) = g • f v)
    (hf' : ∀ (g : G) v, f' (g • v) = g • f' v) (b : B) :
    (f'.comp f).associatedBundleMap (P := P) (fun g v ↦ by simp [hf, hf']) b =
      (f'.associatedBundleMap hf' b).comp (f.associatedBundleMap hf b) := by
  ext v
  obtain ⟨p, v, rfl⟩ := exists_mk v
  simp

end ContinuousLinearMap

namespace ContinuousLinearEquiv

/-- An equivariant continuous linear equivalence induces continuous linear equivalences on
associated fibres, without choosing an invariant metric. -/
def associatedBundleMap (f : F ≃L[𝕜] F')
    (hf : ∀ (g : G) v, f (g • v) = g • f v) (b : B) :
    AssociatedBundle G P F b ≃L[𝕜] AssociatedBundle G P F' b :=
  let hf₀ : ∀ (g : G) v, f.toContinuousLinearMap (g • v) = g • f.toContinuousLinearMap v :=
    fun g v ↦ by simpa only [ContinuousLinearEquiv.coe_coe] using hf g v
  let hf' : ∀ (g : G) v,
      f.symm.toContinuousLinearMap (g • v) = g • f.symm.toContinuousLinearMap v := fun g v ↦ by
    simp only [ContinuousLinearEquiv.coe_coe]
    apply f.injective
    simp only [ContinuousLinearEquiv.apply_symm_apply, hf]
  ContinuousLinearEquiv.equivOfInverse
    (f.toContinuousLinearMap.associatedBundleMap hf₀ b)
    (f.symm.toContinuousLinearMap.associatedBundleMap hf' b)
    (fun v ↦ by
      obtain ⟨p, v, rfl⟩ := exists_mk v
      rw [ContinuousLinearMap.associatedBundleMap_mk, ContinuousLinearMap.associatedBundleMap_mk]
      exact congrArg (AssociatedBundle.mk G p) (f.symm_apply_apply v))
    (fun v ↦ by
      obtain ⟨p, v, rfl⟩ := exists_mk v
      rw [ContinuousLinearMap.associatedBundleMap_mk, ContinuousLinearMap.associatedBundleMap_mk]
      exact congrArg (AssociatedBundle.mk G p) (f.apply_symm_apply v))

/-- The linear operator underlying the associated equivalence is the associated intertwiner. -/
@[simp]
theorem toContinuousLinearMap_associatedBundleMap (f : F ≃L[𝕜] F')
    (hf : ∀ (g : G) v, f (g • v) = g • f v) (b : B) :
    (f.associatedBundleMap (P := P) hf b).toContinuousLinearMap =
      f.toContinuousLinearMap.associatedBundleMap hf b :=
  (rfl)

/-- The induced equivalence applies the model equivalence in any principal frame. -/
@[simp]
theorem associatedBundleMap_mk (f : F ≃L[𝕜] F')
    (hf : ∀ (g : G) v, f (g • v) = g • f v) {b : B} (p : P b) (v : F) :
    f.associatedBundleMap hf b (AssociatedBundle.mk G p v) = AssociatedBundle.mk G p (f v) :=
  f.toContinuousLinearMap.associatedBundleMap_mk hf p v

/-- The inverse associated equivalence applies the inverse model equivalence. -/
@[simp]
theorem associatedBundleMap_symm_mk (f : F ≃L[𝕜] F')
    (hf : ∀ (g : G) v, f (g • v) = g • f v) {b : B} (p : P b) (v : F') :
    (f.associatedBundleMap hf b).symm (AssociatedBundle.mk G p v) =
      AssociatedBundle.mk G p (f.symm v) := by
  apply (f.associatedBundleMap hf b).injective
  simp

end ContinuousLinearEquiv

namespace ContinuousLinearMap

variable [VectorBundle 𝕜 F (AssociatedBundle G P F)]
  [VectorBundle 𝕜 F' (AssociatedBundle G P F')]

/-- In a common preferred chart the associated Hom section has constant coordinate `f`. -/
theorem inCoordinates_associatedBundleMap (f : F →L[𝕜] F')
    (hf : ∀ (g : G) v, f (g • v) = g • f v) {b b₀ : B}
    (hb : b ∈ (trivializationAt G P b₀).baseSet) :
    inCoordinates F (AssociatedBundle G P F) F'
      (AssociatedBundle G P F') b₀ b b₀ b (f.associatedBundleMap hf b) = f := by
  have hbF : b ∈ (trivializationAt F (AssociatedBundle G P F) b₀).baseSet := by
    simpa only [baseSet_trivializationAt] using hb
  have hbF' : b ∈ (trivializationAt F' (AssociatedBundle G P F') b₀).baseSet := by
    simpa only [baseSet_trivializationAt] using hb
  ext v
  rw [inCoordinates_eq hbF hbF']
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    Trivialization.continuousLinearEquivAt_apply,
    Trivialization.continuousLinearEquivAt_symm_apply]
  have h := trivializationAt_totalSpaceMap (⟨f, hf⟩ : F →[G] F') hb
    ((trivializationAt F (AssociatedBundle G P F) b₀).symm b v)
  simp only [totalSpaceMap_apply, ← associatedBundleMap_apply f hf,
    Trivialization.apply_mk_symm _ hbF] at h
  exact congrArg Prod.snd h

/-- A continuous linear intertwiner determines a continuous section of the native Hom bundle. -/
theorem continuous_associatedBundleMap (f : F →L[𝕜] F')
    (hf : ∀ (g : G) v, f (g • v) = g • f v) :
    Continuous (fun b ↦ TotalSpace.mk' (F →L[𝕜] F') b
      (f.associatedBundleMap (P := P) hf b)) := by
  apply continuous_iff_continuousAt.mpr
  intro b₀
  rw [FiberBundle.continuousAt_totalSpace]
  refine ⟨continuousAt_id, ?_⟩
  refine (continuousAt_const (y := f)).congr_of_eventuallyEq ?_
  filter_upwards [(trivializationAt G P b₀).open_baseSet.mem_nhds
    (mem_baseSet_trivializationAt G P b₀)] with b hb
  rw [hom_trivializationAt_apply, inCoordinates_associatedBundleMap f hf hb]

end ContinuousLinearMap
