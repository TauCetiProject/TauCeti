/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Extension
public import Mathlib.Topology.Algebra.Module.Equiv.Basic

/-!
# The product topology on a cocycle extension

Mathlib's `LieAlgebra.ofTwoCocycle c` carries the topology transported from `L × M`.
Its coordinate equivalence is continuous linear, so the projection has a continuous linear
section and the kernel inclusion is continuous. The bracket is continuous when the bracket
of `L`, the action on `M`, and the cocycle are continuous. For trivial coefficients the
action condition is automatic.

This uses Mathlib's cocycle extension without changing its Lie structure. In particular,
continuity is a property of the given cocycle, not additional data in a new extension carrier.
-/

public section

open Topology LieModule.Cohomology

namespace LieAlgebra

variable {R L M : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]
  [TopologicalSpace L] [TopologicalSpace M] (c : twoCocycle R L M)

/-- The product topology in the coordinates of a cocycle extension. -/
instance ofTwoCocycle.instTopologicalSpace : TopologicalSpace (ofTwoCocycle c) :=
  TopologicalSpace.induced (ofProd c).symm instTopologicalSpaceProd

/-- The coordinates of a cocycle extension as a continuous linear equivalence. -/
def ofProdContinuousLinearEquiv : (L × M) ≃L[R] ofTwoCocycle c where
  __ := ofProdLinearEquiv c
  continuous_toFun := continuous_induced_rng.mpr (by
    simpa only [LinearEquiv.toFun_eq_coe, LinearEquiv.coe_coe,
      coe_ofProdLinearEquiv, Function.comp_def, Equiv.symm_apply_apply] using
      (continuous_id' : Continuous fun p : L × M ↦ p))
  continuous_invFun := by
    simpa only [LinearEquiv.invFun_eq_symm, coe_ofProdLinearEquiv_symm] using
      (continuous_induced_dom : Continuous (ofProd c).symm)

@[simp]
theorem coe_ofProdContinuousLinearEquiv :
    ⇑(ofProdContinuousLinearEquiv c) = ofProd c := by
  simp only [ofProdContinuousLinearEquiv, ContinuousLinearEquiv.coe_mk, coe_ofProdLinearEquiv]

@[simp]
theorem coe_ofProdContinuousLinearEquiv_symm :
    ⇑(ofProdContinuousLinearEquiv c).symm = (ofProd c).symm := by
  rw [← ContinuousLinearEquiv.coe_symm_toLinearEquiv]
  exact coe_ofProdLinearEquiv_symm c

namespace ofTwoCocycle

instance [IsTopologicalAddGroup L] [IsTopologicalAddGroup M] :
    IsTopologicalAddGroup (ofTwoCocycle c) :=
  Topology.IsInducing.isTopologicalAddGroup (ofProdLinearEquiv c).symm.toLinearMap (by
    simpa using (ofProdContinuousLinearEquiv c).symm.toHomeomorph.isInducing)

instance [ContinuousConstSMul R L] [ContinuousConstSMul R M] :
    ContinuousConstSMul R (ofTwoCocycle c) :=
  (ofProdContinuousLinearEquiv c).symm.toHomeomorph.isInducing.continuousConstSMul
    id (fun {_} {_} ↦ map_smul (ofProdContinuousLinearEquiv c).symm _ _)

instance [T2Space L] [T2Space M] : T2Space (ofTwoCocycle c) :=
  (ofProdContinuousLinearEquiv c).symm.toHomeomorph.isEmbedding.t2Space

/-- The continuous linear projection onto the quotient Lie algebra. -/
def projCLM : ofTwoCocycle c →L[R] L :=
  (ContinuousLinearMap.fst R L M).comp (ofProdContinuousLinearEquiv c).symm.toContinuousLinearMap

@[simp]
theorem projCLM_apply (v : ofTwoCocycle c) : projCLM c v = proj c v := by
  simp [projCLM]

/-- The zero-central-coordinate continuous linear section. It need not preserve brackets. -/
def sectionCLM : L →L[R] ofTwoCocycle c :=
  (ofProdContinuousLinearEquiv c).toContinuousLinearMap.comp (ContinuousLinearMap.inl R L M)

@[simp]
theorem sectionCLM_apply (x : L) : sectionCLM c x = ofProd c (x, 0) := by
  simp [sectionCLM]

/-- The continuous linear inclusion of the coefficient module as the kernel. -/
def inclCLM : M →L[R] ofTwoCocycle c :=
  (ofProdContinuousLinearEquiv c).toContinuousLinearMap.comp (ContinuousLinearMap.inr R L M)

@[simp]
theorem inclCLM_apply (m : M) : inclCLM c m = ofProd c (0, m) := by
  simp [inclCLM]

@[simp]
theorem projCLM_comp_sectionCLM : (projCLM c).comp (sectionCLM c) = .id R L := by
  ext x
  simp

/-- The coefficient inclusion has precisely the kernel of the projection as its range. -/
theorem range_inclCLM : (inclCLM c).range = (projCLM c).ker := by
  ext v
  constructor
  · rintro ⟨m, rfl⟩
    simp
  · intro hv
    refine ⟨((ofProd c).symm v).2, ?_⟩
    apply (ofProd c).symm.injective
    simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, projCLM_apply, proj_apply] at hv
    ext <;> simp [hv]

/-- The quotient projection is open for the product topology. -/
theorem isOpenMap_proj : IsOpenMap (proj c) := by
  convert isOpenMap_fst.comp (ofProdContinuousLinearEquiv c).symm.isOpenMap using 1
  ext v
  simp

/-- A cocycle extension has continuous bracket if the base bracket, module action and
cocycle are jointly continuous. -/
theorem continuous_lie [IsTopologicalAddGroup M]
    (hL : Continuous fun p : L × L ↦ ⁅p.1, p.2⁆)
    (hM : Continuous fun p : L × M ↦ ⁅p.1, p.2⁆)
    (hc : Continuous fun p : L × L ↦ (c : twoCochain R L M) p.1 p.2) :
    Continuous fun p : ofTwoCocycle c × ofTwoCocycle c ↦ ⁅p.1, p.2⁆ := by
  let e := ofProdContinuousLinearEquiv c
  have hfst : Continuous fun p : ofTwoCocycle c × ofTwoCocycle c ↦ e.symm p.1 :=
    e.symm.continuous.comp continuous_fst
  have hsnd : Continuous fun p : ofTwoCocycle c × ofTwoCocycle c ↦ e.symm p.2 :=
    e.symm.continuous.comp continuous_snd
  apply e.symm.toHomeomorph.isInducing.continuous_iff.mpr
  simpa only [e, ContinuousLinearEquiv.coe_toHomeomorph,
    coe_ofProdContinuousLinearEquiv_symm, Function.comp_def, bracket_ofTwoCocycle,
    Equiv.symm_apply_apply, Pi.add_apply, Pi.sub_apply, twoCochain_val_apply] using
    (hL.comp (hfst.fst.prodMk hsnd.fst)).prodMk
      (((hc.comp (hfst.fst.prodMk hsnd.fst)).add
        (hM.comp (hfst.fst.prodMk hsnd.snd))).sub
        (hM.comp (hsnd.fst.prodMk hfst.snd)))

section Map

variable {L' M' : Type*} [LieRing L'] [LieAlgebra R L'] [AddCommGroup M'] [Module R M']
  [LieRingModule L' M'] [LieModule R L' M'] [TopologicalSpace L'] [TopologicalSpace M']
  [LieModule.IsTrivial L M] [LieModule.IsTrivial L' M']
  (φ : L →ₗ⁅R⁆ L') (f : M →ₗ[R] M') (c' : twoCocycle R L' M')
  (h : ∀ x y, (c' : twoCochain R L' M') (φ x) (φ y) = f ((c : twoCochain R L M) x y))

/-- A morphism of cocycle central extensions is continuous when its two coordinate maps are. -/
theorem continuous_map (hφ : Continuous φ) (hf : Continuous f) :
    Continuous (map c φ f c' h) := by
  apply (ofProdContinuousLinearEquiv c').symm.toHomeomorph.isInducing.continuous_iff.mpr
  simpa only [ContinuousLinearEquiv.coe_toHomeomorph, coe_ofProdContinuousLinearEquiv_symm,
    Function.comp_def, ofProd_symm_map, Prod.map] using
    (hφ.prodMap hf).comp (ofProdContinuousLinearEquiv c).symm.continuous

end Map

end ofTwoCocycle
end LieAlgebra
