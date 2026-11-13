/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Module.PiTensorProduct.UniversalProperty

/-!
# Scalar units for locally convex projective tensor products

The projective tensor product of the scalar field with a space defined by seminorms is
continuously linearly equivalent to that space. For a complete Hausdorff space the same holds
for the separated completed projective tensor product. Both equivalences send the pure tensor
of a scalar and a vector to their scalar product, and their inverses insert the scalar `1`.

The factors use the native finite-family construction, indexed by `Fin 2`. They have a common
universe because `PiTensorProduct` takes a family of types in one universe. The completed
identification preserves the caller's compatible additive uniformity on the target. The algebraic
construction uses `ProjectiveTensorProduct.liftEquiv`, and the completed construction extends
this continuous linear equivalence through `ContinuousLinearMap.fromCompletion`.

## References

* A. Grothendieck, *Résumé des résultats essentiels dans la théorie des produits tensoriels
  topologiques et des espaces nucléaires* (1952), Chapter I, n° 1, pp. 76–77.
-/

public section

universe u v w

open scoped TensorProduct

namespace TauCeti

/-- The two factors of the scalar unit: the scalar field followed by the vector space. -/
abbrev ScalarUnitFactors (𝕜 E : Type u) : Fin 2 → Type u :=
  fun i => match i.val with | 0 => 𝕜 | _ + 1 => E

-- Direct delegates retain the caller's structures at the two concrete indices.
instance {𝕜 E : Type u} [AddCommGroup 𝕜] [AddCommGroup E] :
    ∀ i, AddCommGroup (ScalarUnitFactors 𝕜 E i)
  | ⟨0, _⟩ => inferInstance
  | ⟨_ + 1, _⟩ => inferInstance

instance {𝕜 E : Type u} [Ring 𝕜] [AddCommGroup E] [Module 𝕜 E] :
    ∀ i, Module 𝕜 (ScalarUnitFactors 𝕜 E i)
  | ⟨0, _⟩ => inferInstance
  | ⟨_ + 1, _⟩ => inferInstance

instance {𝕜 E : Type u} [TopologicalSpace 𝕜] [TopologicalSpace E] :
    ∀ i, TopologicalSpace (ScalarUnitFactors 𝕜 E i)
  | ⟨0, _⟩ => inferInstance
  | ⟨_ + 1, _⟩ => inferInstance

/-- Seminorm indices for the scalar unit: one norm on the field and the given indices on the
vector space. -/
abbrev ScalarUnitIndices (σ : Type v) : Fin 2 → Type v :=
  fun i => match i.val with | 0 => PUnit | _ + 1 => σ

variable {𝕜 E : Type u} [NontriviallyNormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]
variable {σ : Type v} (p : SeminormFamily 𝕜 E σ)

/-- The norm seminorm on the scalar factor together with the given seminorms on the vector
factor. -/
def scalarUnitSeminorms :
    ∀ i, SeminormFamily 𝕜 (ScalarUnitFactors 𝕜 E i) (ScalarUnitIndices σ i)
  | ⟨0, _⟩ => fun _ => normSeminorm 𝕜 𝕜
  | ⟨_ + 1, _⟩ => p

@[simp] theorem scalarUnitSeminorms_zero :
    scalarUnitSeminorms p 0 = fun _ => normSeminorm 𝕜 𝕜 := (rfl)

@[simp] theorem scalarUnitSeminorms_one : scalarUnitSeminorms p 1 = p := (rfl)

section Topology

variable [TopologicalSpace E] (hp : WithSeminorms p)

include hp in
/-- Both factors of the scalar unit carry the topology defined by their seminorm families. -/
theorem scalarUnitSeminorms_withSeminorms : ∀ i, WithSeminorms (scalarUnitSeminorms p i) := by
  intro ⟨n, h⟩
  cases n
  · exact (norm_withSeminorms 𝕜 𝕜).congr_equiv (Equiv.ofUnique PUnit.{v + 1} Unit)
  · exact hp

private def scalarUnitAction [ContinuousSMul 𝕜 E] :
    ContinuousMultilinearMap 𝕜 (ScalarUnitFactors 𝕜 E) E where
  toFun x := x 0 • x 1
  map_update_add' := by
    intro _ m i x y
    fin_cases i <;> simp [add_smul, smul_add]
  map_update_smul' := by
    intro _ m i c x
    fin_cases i <;> simp [smul_smul, mul_comm]
  cont := (continuous_apply 0).smul (continuous_apply 1)

private theorem scalarUnitAction_apply [ContinuousSMul 𝕜 E]
    (x : ∀ i, ScalarUnitFactors 𝕜 E i) : scalarUnitAction x = x 0 • x 1 := (rfl)

namespace ProjectiveTensorProduct

private noncomputable def scalarUnitInsert :
    E →L[𝕜] ProjectiveTensorProduct (scalarUnitSeminorms p) :=
  let t := continuousTprod (scalarUnitSeminorms p) (scalarUnitSeminorms_withSeminorms p hp)
  t.toContinuousLinearMap (Fin.cons 1 fun _ => (0 : E)) 1

private theorem scalarUnitInsert_apply (x : E) :
    scalarUnitInsert p hp x = tprod (scalarUnitSeminorms p) (Fin.cons 1 fun _ => x) := by
  simp only [scalarUnitInsert, ContinuousMultilinearMap.toContinuousLinearMap_apply,
    continuousTprod_apply]
  congr 1
  ext i
  fin_cases i <;> simp

private theorem scalarUnitInsert_smul (a : 𝕜) (x : E) :
    scalarUnitInsert p hp (a • x) =
      tprod (scalarUnitSeminorms p) (Fin.cons a fun _ => x) := by
  rw [map_smul, scalarUnitInsert_apply]
  simpa using ((tprod (scalarUnitSeminorms p)).cons_smul (fun _ => x) a 1).symm

/-- Scalar multiplication identifies the projective tensor of the scalar field and a locally
convex space with that space, before completion. -/
noncomputable def lid : ProjectiveTensorProduct (scalarUnitSeminorms p) ≃L[𝕜] E := by
  letI := hp.isTopologicalAddGroup
  letI := hp.continuousSMul
  let f := liftEquiv (scalarUnitSeminorms p) (scalarUnitSeminorms_withSeminorms p hp)
    p hp scalarUnitAction
  let g := scalarUnitInsert p hp
  have hf_apply (x : ∀ i, ScalarUnitFactors 𝕜 E i) :
      f (tprod (scalarUnitSeminorms p) x) = x 0 • x 1 :=
    by simpa only [tprod_apply, scalarUnitAction_apply] using
      liftEquiv_tprod (scalarUnitSeminorms p)
        (scalarUnitSeminorms_withSeminorms p hp) p hp scalarUnitAction x
  have hgf : g.comp f = ContinuousLinearMap.id 𝕜 _ := by
    apply ContinuousLinearMap.coe_injective
    apply linearMap_ext (scalarUnitSeminorms p)
    intro x
    simp only [ContinuousLinearMap.coe_coe, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply, hf_apply]
    rw [scalarUnitInsert_smul]
    congr 1
    ext i
    fin_cases i <;> simp
  apply ContinuousLinearEquiv.equivOfInverse' f g ?_ hgf
  ext x
  simp [g, scalarUnitInsert_apply, f, scalarUnitAction_apply]

/-- The scalar-unit equivalence sends a pure tensor to scalar multiplication. -/
@[simp] theorem lid_tprod (x : ∀ i, ScalarUnitFactors 𝕜 E i) :
    lid p hp (⟨⨂ₜ[𝕜] i, x i⟩ : ProjectiveTensorProduct (scalarUnitSeminorms p)) =
      x 0 • x 1 := by
  simp only [lid]
  rw [ContinuousLinearEquiv.equivOfInverse'_apply]
  simp only [liftEquiv_tprod, scalarUnitAction_apply]

/-- The inverse scalar-unit equivalence inserts the scalar `1`. -/
@[simp] theorem lid_symm_apply (x : E) :
    (lid p hp).symm x =
      (⟨⨂ₜ[𝕜] i, Fin.cons 1 (fun _ => x) i⟩ :
        ProjectiveTensorProduct (scalarUnitSeminorms p)) := by
  simp only [lid]
  rw [ContinuousLinearEquiv.symm_equivOfInverse', ContinuousLinearEquiv.equivOfInverse'_apply]
  simpa only [tprod_apply] using scalarUnitInsert_apply p hp x

end ProjectiveTensorProduct

end Topology

namespace CompletedProjectiveTensorProduct

variable [UniformSpace E] [IsUniformAddGroup E]
  [T0Space E] [CompleteSpace E]
variable (hp : WithSeminorms p)

/-- The scalar field is a left unit for the completed projective tensor of complete Hausdorff
locally convex spaces, with the caller's compatible additive uniformity. -/
noncomputable def lid : CompletedProjectiveTensorProduct (scalarUnitSeminorms p) ≃L[𝕜] E := by
  letI := hp.continuousSMul
  letI := uniformContinuousConstSMul_of_continuousConstSMul 𝕜 E
  let f := (ProjectiveTensorProduct.lid p hp).toContinuousLinearMap.fromCompletion
  let g := UniformSpace.Completion.toComplL.comp
    (ProjectiveTensorProduct.lid p hp).symm.toContinuousLinearMap
  have hgf : g.comp f = ContinuousLinearMap.id 𝕜 _ := by
    apply continuousLinearMap_ext (scalarUnitSeminorms p)
    intro x
    simp only [f, g, ContinuousLinearMap.comp_apply, UniformSpace.Completion.coe_toComplL,
      ContinuousLinearMap.fromCompletion_apply_coe, ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.symm_apply_apply, ContinuousLinearMap.id_apply]
  apply ContinuousLinearEquiv.equivOfInverse' f g ?_ hgf
  ext x
  simp only [f, g, ContinuousLinearMap.comp_apply, UniformSpace.Completion.coe_toComplL,
    ContinuousLinearMap.fromCompletion_apply_coe, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearMap.id_apply]

/-- The completed scalar-unit equivalence extends the algebraic scalar-unit equivalence. -/
@[simp] theorem lid_coe (z : ProjectiveTensorProduct (scalarUnitSeminorms p)) :
    lid p hp (z : CompletedProjectiveTensorProduct (scalarUnitSeminorms p)) =
      ProjectiveTensorProduct.lid p hp z := by
  let _ := hp.continuousSMul
  let _ := uniformContinuousConstSMul_of_continuousConstSMul 𝕜 E
  simp only [lid]
  rw [ContinuousLinearEquiv.equivOfInverse'_apply]
  exact ContinuousLinearMap.fromCompletion_apply_coe _ z

/-- The completed scalar-unit equivalence sends a pure tensor to scalar multiplication. -/
theorem lid_tprod (x : ∀ i, ScalarUnitFactors 𝕜 E i) :
    lid p hp (tprod (scalarUnitSeminorms p) (scalarUnitSeminorms_withSeminorms p hp) x) =
      x 0 • x 1 := by
  simpa only [tprod_apply, lid_coe, ProjectiveTensorProduct.tprod_apply] using
    ProjectiveTensorProduct.lid_tprod p hp x

/-- The inverse completed scalar-unit equivalence inserts the scalar `1`. -/
@[simp] theorem lid_symm_apply (x : E) :
    (lid p hp).symm x =
      ((⟨⨂ₜ[𝕜] i, Fin.cons 1 (fun _ => x) i⟩ :
        ProjectiveTensorProduct (scalarUnitSeminorms p)) :
          CompletedProjectiveTensorProduct (scalarUnitSeminorms p)) := by
  simp only [lid]
  rw [ContinuousLinearEquiv.symm_equivOfInverse', ContinuousLinearEquiv.equivOfInverse'_apply]
  simp only [ContinuousLinearMap.comp_apply, UniformSpace.Completion.coe_toComplL,
    ContinuousLinearEquiv.coe_coe, ProjectiveTensorProduct.lid_symm_apply]

variable {F : Type u} [AddCommGroup F] [Module 𝕜 F] [UniformSpace F]
  [IsUniformAddGroup F] [T0Space F] [CompleteSpace F]
variable {τ : Type w} (q : SeminormFamily 𝕜 F τ) (hq : WithSeminorms q)

/-- Scalar-unit identifications commute with tensoring the scalar identity and a
seminorm-bounded linear map. The bounds are those of the native completed tensor map. -/
theorem lid_map (f : E →ₗ[𝕜] F)
    (hf : ∀ i, Seminorm.IsBounded (scalarUnitSeminorms p i) (scalarUnitSeminorms q i)
      ((Fin.cons LinearMap.id (fun _ => f) :
        ∀ i, ScalarUnitFactors 𝕜 E i →ₗ[𝕜] ScalarUnitFactors 𝕜 F i) i))
    (z : CompletedProjectiveTensorProduct (scalarUnitSeminorms p)) :
    lid q hq (map (scalarUnitSeminorms p) (scalarUnitSeminorms q)
      (Fin.cons LinearMap.id (fun _ => f)) hf z) = f (lid p hp z) := by
  let fL : E →L[𝕜] F :=
    ⟨f, WithSeminorms.continuous_of_isBounded hp hq f (by
      simpa only [Fin.cons_one, scalarUnitSeminorms_one] using hf 1)⟩
  have h : (lid q hq).toContinuousLinearMap.comp
      (map (scalarUnitSeminorms p) (scalarUnitSeminorms q)
        (Fin.cons LinearMap.id (fun _ => f)) hf) =
      fL.comp (lid p hp).toContinuousLinearMap := by
    apply continuousLinearMap_ext (scalarUnitSeminorms p)
    intro x
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      map_tprod, lid_coe, ProjectiveTensorProduct.lid_tprod,
      Fin.cons_zero, Fin.cons_one, LinearMap.id_apply]
    exact (f.map_smul (x 0) (x 1)).symm
  exact DFunLike.congr_fun h z

end CompletedProjectiveTensorProduct

end TauCeti
