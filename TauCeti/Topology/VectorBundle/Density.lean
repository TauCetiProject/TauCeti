/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Density.Topology
public import Mathlib.Topology.VectorBundle.Basic
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# The density line of a real vector bundle

The top-dimensional densities on the fibres of a finite-dimensional real vector bundle
form a real line bundle. A bundle chart supplies a basis of the original fibre, and
evaluation on that basis is the density coordinate. Its transition is multiplication
by the absolute determinant of the reverse vector-bundle transition.

The construction follows the vector-prebundle method of Mathlib's bundle of continuous
linear maps, using the intrinsic pointwise topology of the density fibres.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, second edition, Chapter 16, Densities.
-/

public section

noncomputable section

open Bundle Set Topology FiberBundle

variable {B F : Type*} [TopologicalSpace B] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] {V : B → Type*} [∀ x, AddCommGroup (V x)]
  [∀ x, Module ℝ (V x)]
  [TopologicalSpace (TotalSpace F V)]

namespace Bundle.Trivialization

variable (e e' : Trivialization F (π F V)) [e.IsLinear ℝ] [e'.IsLinear ℝ]

open scoped Classical in
/-- Evaluation in the frame of `e`, before the density total space receives its topology. -/
def densityPretrivialization :
    Pretrivialization ℝ (π ℝ (fun x ↦ TauCeti.Density (V x) (Module.finrank ℝ F))) where
  toFun p := ⟨p.proj, p.2 (fun i ↦ e.symm p.proj (Module.finBasis ℝ F i))⟩
  invFun p := ⟨p.1, if hx : p.1 ∈ e.baseSet then
    ((Module.finBasis ℝ F).map (e.linearEquivAt ℝ p.1 hx).symm).density p.2 else 0⟩
  source := Bundle.TotalSpace.proj ⁻¹' e.baseSet
  target := e.baseSet ×ˢ univ
  map_source' := fun _ h ↦ ⟨h, mem_univ _⟩
  map_target' := fun _ h ↦ h.1
  left_inv' := by
    rintro ⟨x, μ⟩ (hx : x ∈ e.baseSet)
    simp only [TotalSpace.mk_inj]
    rw [dite_eq_left hx]
    simpa only [Module.Basis.densityEquiv_apply, Module.Basis.densityEquiv_symm_apply,
      Module.Basis.coe_map, Function.comp_def, Trivialization.linearEquivAt_symm_apply] using
      ((Module.finBasis ℝ F).map (e.linearEquivAt ℝ x hx).symm).densityEquiv.symm_apply_apply μ
  right_inv' := by
    rintro ⟨x, c⟩ ⟨hx, _⟩
    simp only [Prod.mk_right_inj]
    rw [dite_eq_left hx]
    simpa only [Module.Basis.coe_map, Function.comp_def,
      Trivialization.linearEquivAt_symm_apply] using
      ((Module.finBasis ℝ F).map (e.linearEquivAt ℝ x hx).symm).density_apply_self c
  open_target := e.open_baseSet.prod isOpen_univ
  baseSet := e.baseSet
  open_baseSet := e.open_baseSet
  source_eq := (rfl)
  target_eq := (rfl)
  proj_toFun _ _ := (rfl)

instance densityPretrivialization_isLinear : e.densityPretrivialization.IsLinear ℝ where
  linear _ _ := ⟨fun _ _ ↦ rfl, fun _ _ ↦ rfl⟩

@[simp]
theorem densityPretrivialization_baseSet : e.densityPretrivialization.baseSet = e.baseSet := (rfl)

/-- A density coordinate is evaluation on the inverse vector-bundle frame. -/
theorem densityPretrivialization_apply
    (p : TotalSpace ℝ (fun x ↦ TauCeti.Density (V x) (Module.finrank ℝ F))) :
    e.densityPretrivialization p =
      (p.proj, p.2 (fun i ↦ e.symm p.proj (Module.finBasis ℝ F i))) := (rfl)

/-- The inverse chart constructs the density with the prescribed coefficient in its frame. -/
theorem densityPretrivialization_symm_apply {x : B} (hx : x ∈ e.baseSet) (c : ℝ) :
    e.densityPretrivialization.symm x c =
      ((Module.finBasis ℝ F).map (e.linearEquivAt ℝ x hx).symm).density c := by
  let b := (Module.finBasis ℝ F).map (e.linearEquivAt ℝ x hx).symm
  have hc : (e.densityPretrivialization ⟨x, b.density c⟩).2 = c := by
    simpa only [densityPretrivialization_apply, b, Module.Basis.coe_map,
      Function.comp_def, Trivialization.linearEquivAt_symm_apply] using b.density_apply_self c
  have h := e.densityPretrivialization.symm_apply_apply_mk hx (b.density c)
  rw [hc] at h
  exact h

/-- Density transition functions use the determinant of the reverse vector transition. -/
def densityCoordChange (x : B) : ℝ →L[ℝ] ℝ :=
  |((e'.coordChangeL ℝ e x : F →L[ℝ] F) : F →ₗ[ℝ] F).det| •
    ContinuousLinearMap.id ℝ ℝ

omit [FiniteDimensional ℝ F] in
@[simp]
theorem densityCoordChange_apply (x : B) (c : ℝ) :
    e.densityCoordChange e' x c =
      |((e'.coordChangeL ℝ e x : F →L[ℝ] F) : F →ₗ[ℝ] F).det| * c := (rfl)

/-- The determinant expression computes the actual change of density coordinates. -/
theorem densityCoordChange_eq {x : B} (hx : x ∈ e.baseSet ∩ e'.baseSet) (c : ℝ) :
    e.densityCoordChange e' x c =
      (e'.densityPretrivialization ⟨x, e.densityPretrivialization.symm x c⟩).2 := by
  rw [densityPretrivialization_apply, densityPretrivialization_symm_apply e hx.1]
  simp only [Module.Basis.density_apply, densityCoordChange_apply,
    Module.Basis.det_map]
  have ht : (e.linearEquivAt ℝ x hx.1 : V x → F) ∘
      (fun i ↦ e'.symm x (Module.finBasis ℝ F i)) =
      ((e'.coordChangeL ℝ e x : F →L[ℝ] F) : F →ₗ[ℝ] F) ∘ Module.finBasis ℝ F := by
    ext i
    simp [Trivialization.coordChangeL_apply _ _ ⟨hx.2, hx.1⟩,
      Trivialization.linearEquivAt_apply]
  simp only [LinearEquiv.symm_symm]
  rw [ht, Module.Basis.det_comp, Module.Basis.det_self, mul_one]

variable [∀ x, TopologicalSpace (V x)] [FiberBundle F V] [VectorBundle ℝ F V]
  [MemTrivializationAtlas e] [MemTrivializationAtlas e']

omit [FiniteDimensional ℝ F] in
/-- Absolute-determinant transitions vary continuously on chart overlaps. -/
theorem continuousOn_densityCoordChange :
    ContinuousOn (e.densityCoordChange e') (e.baseSet ∩ e'.baseSet) := by
  have h := ContinuousLinearMap.continuous_det.comp_continuousOn
    (continuousOn_coordChange ℝ e' e)
  exact (h.abs.smul continuousOn_const).mono (by intro x hx; exact ⟨hx.2, hx.1⟩)

end Bundle.Trivialization

namespace TauCeti.Density

/-- The vector prebundle whose charts evaluate densities on the vector-bundle frames. -/
def vectorPrebundle (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] (V : B → Type*) [∀ x, AddCommGroup (V x)]
    [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)]
    [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle ℝ F V] :
    VectorPrebundle ℝ ℝ (fun x ↦ Density (V x) (Module.finrank ℝ F)) where
  pretrivializationAtlas := {d | ∃ (e : Trivialization F (π F V))
    (_ : MemTrivializationAtlas e), d = e.densityPretrivialization}
  pretrivialization_linear' := by
    rintro _ ⟨e, he, rfl⟩
    infer_instance
  pretrivializationAt x := (trivializationAt F V x).densityPretrivialization
  mem_base_pretrivializationAt x := mem_baseSet_trivializationAt F V x
  pretrivialization_mem_atlas x := ⟨trivializationAt F V x, inferInstance, rfl⟩
  exists_coordChange := by
    rintro _ ⟨e, he, rfl⟩ _ ⟨e', he', rfl⟩
    exact ⟨e.densityCoordChange e', e.continuousOn_densityCoordChange e',
      fun x hx c ↦ e.densityCoordChange_eq e' hx c⟩
  totalSpaceMk_isInducing := by
    intro x
    let e := trivializationAt F V x
    let hx := mem_baseSet_trivializationAt F V x
    let b := (Module.finBasis ℝ F).map (e.linearEquivAt ℝ x hx).symm
    have h : IsInducing (fun μ : Density (V x) (Module.finrank ℝ F) ↦
        (x, b.densityContinuousLinearEquiv μ)) :=
      isInducing_const_prod.mpr b.densityContinuousLinearEquiv.toHomeomorph.isInducing
    simpa only [Function.comp_def, Trivialization.densityPretrivialization_apply,
      Module.Basis.densityContinuousLinearEquiv_apply, b, e,
      Module.Basis.coe_map, Function.comp_def,
      Trivialization.linearEquivAt_symm_apply] using h

variable (F V) [∀ x, TopologicalSpace (V x)] [FiberBundle F V] [VectorBundle ℝ F V]

/-- A pretrivialization belongs to the density atlas exactly when it comes from a chart
of the original vector bundle. -/
theorem mem_pretrivializationAtlas_iff
    (d : Pretrivialization ℝ (π ℝ (fun x ↦ Density (V x) (Module.finrank ℝ F)))) :
    d ∈ (vectorPrebundle F V).pretrivializationAtlas ↔
      ∃ (e : Trivialization F (π F V)) (_ : MemTrivializationAtlas e),
        d = e.densityPretrivialization := (Iff.rfl)

/-- The density total space topology, induced by evaluation in bundle frames. -/
instance topologicalSpaceTotalSpace :
    TopologicalSpace (TotalSpace ℝ (fun x ↦ Density (V x) (Module.finrank ℝ F))) :=
  (vectorPrebundle F V).totalSpaceTopology

/-- Top-dimensional density fibres form a real line bundle. -/
instance fiberBundle : FiberBundle ℝ (fun x ↦ Density (V x) (Module.finrank ℝ F)) :=
  (vectorPrebundle F V).toFiberBundle

/-- The density line is a real vector bundle with its pointwise fibre structures. -/
instance vectorBundle : VectorBundle ℝ ℝ (fun x ↦ Density (V x) (Module.finrank ℝ F)) :=
  (vectorPrebundle F V).toVectorBundle

end TauCeti.Density

namespace Bundle.Trivialization

variable [∀ x, TopologicalSpace (V x)] [FiberBundle F V] [VectorBundle ℝ F V]
  (e e' : Trivialization F (π F V)) [MemTrivializationAtlas e] [MemTrivializationAtlas e']

/-- The density chart associated with a chart of a finite-dimensional real vector bundle. -/
def density :
    Trivialization ℝ (π ℝ (fun x ↦ TauCeti.Density (V x) (Module.finrank ℝ F))) :=
  (TauCeti.Density.vectorPrebundle F V).trivializationOfMemPretrivializationAtlas
    ⟨e, inferInstance, rfl⟩

instance density_memTrivializationAtlas : MemTrivializationAtlas e.density where
  out := ⟨_, ⟨e, inferInstance, rfl⟩, rfl⟩

@[simp]
theorem density_baseSet : e.density.baseSet = e.baseSet := (rfl)

/-- The density chart reads the value on the inverse model frame. -/
theorem density_apply
    (p : TotalSpace ℝ (fun x ↦ TauCeti.Density (V x) (Module.finrank ℝ F))) :
    e.density p = (p.proj, p.2 (fun i ↦ e.symm p.proj (Module.finBasis ℝ F i))) :=
  e.densityPretrivialization_apply p

/-- The inverse density chart has the prescribed coefficient on the inverse model frame. -/
theorem density_symm_apply {x : B} (hx : x ∈ e.baseSet) (c : ℝ) :
    e.density.symm x c =
      ((Module.finBasis ℝ F).map (e.linearEquivAt ℝ x hx).symm).density c :=
  e.densityPretrivialization_symm_apply hx c

/-- The native density coordinate change is multiplication by the absolute determinant
of the reverse vector-bundle coordinate change. -/
theorem density_coordChangeL {x : B} (hx : x ∈ e.baseSet ∩ e'.baseSet) :
    (e.density.coordChangeL ℝ e'.density x : ℝ →L[ℝ] ℝ) = e.densityCoordChange e' x := by
  apply ContinuousLinearMap.ext
  intro c
  simp only [ContinuousLinearEquiv.coe_coe]
  rw [Trivialization.coordChangeL_apply]
  · exact (e.densityCoordChange_eq e' hx c).symm
  · exact hx

end Bundle.Trivialization

namespace TauCeti.Density

variable [∀ x, TopologicalSpace (V x)] [FiberBundle F V] [VectorBundle ℝ F V]

/-- The preferred density chart is the density chart of the preferred vector-bundle chart. -/
theorem trivializationAt_eq (x : B) :
    trivializationAt ℝ (fun x ↦ Density (V x) (Module.finrank ℝ F)) x =
      (trivializationAt F V x).density := (rfl)

end TauCeti.Density
