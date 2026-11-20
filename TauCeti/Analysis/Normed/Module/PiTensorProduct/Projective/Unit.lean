/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Module.PiTensorProduct.Projective.Completion

/-!
# Scalar units for locally convex projective tensor products

The projective tensor product of the scalar field with a space defined by seminorms is
continuously linearly equivalent to that space. For a complete Hausdorff space the same holds
for the separated completed projective tensor product. Both equivalences send the pure tensor
of a scalar and a vector to their scalar product, and their inverses insert the scalar `1`.

The factors use the native finite-family construction, indexed by `Fin 2`. They have a common
universe because `PiTensorProduct` takes a family of types in one universe. The completed
identification preserves the caller's compatible additive uniformity on the target. The algebraic
construction uses `ProjectiveTensorProduct.lift` with a constant-one seminorm bound, and the
completed construction extends this continuous linear equivalence through
`ContinuousLinearMap.fromCompletion`.

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

instance {σ : Type v} [Countable σ] : ∀ i, Countable (ScalarUnitIndices σ i)
  | ⟨0, _⟩ => inferInstance
  | ⟨_ + 1, _⟩ => inferInstance

variable {𝕜 E : Type u} [NormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]
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

/-- Pairing the scalar identity with a seminorm-bounded linear map gives a bounded map
on each scalar-unit factor, without any topological assumptions. -/
theorem isBounded_scalarUnitSeminorms_cons {p : SeminormFamily 𝕜 E σ}
    {F : Type u} [AddCommGroup F] [Module 𝕜 F]
    {τ : Type w} {q : SeminormFamily 𝕜 F τ} {f : E →ₗ[𝕜] F}
    (hf : Seminorm.IsBounded p q f) :
    ∀ i, Seminorm.IsBounded (scalarUnitSeminorms p i) (scalarUnitSeminorms q i)
      ((Fin.cons LinearMap.id (fun _ => f) :
        ∀ i, ScalarUnitFactors 𝕜 E i →ₗ[𝕜] ScalarUnitFactors 𝕜 F i) i) := by
  intro i
  fin_cases i
  · intro j
    refine ⟨{PUnit.unit}, 1, ?_⟩
    simp
  · exact hf

section Topology

variable [TopologicalSpace E] (hp : WithSeminorms p)

include hp in
/-- Both factors of the scalar unit carry the topology defined by their seminorm families. -/
theorem withSeminorms_scalarUnitSeminorms : ∀ i, WithSeminorms (scalarUnitSeminorms p i) := by
  intro ⟨n, h⟩
  cases n
  · exact (norm_withSeminorms 𝕜 𝕜).congr_equiv (Equiv.ofUnique PUnit.{v + 1} Unit)
  · exact hp

private def scalarUnitAction :
    MultilinearMap (RingHom.id 𝕜) (ScalarUnitFactors 𝕜 E) E where
  toFun x := x 0 • x 1
  map_update_add' := by
    intro _ m i x y
    fin_cases i <;> simp [add_smul, smul_add]
  map_update_smul' := by
    intro _ m i c x
    fin_cases i <;> simp [smul_smul, mul_comm]

omit [TopologicalSpace E] in
private theorem scalarUnitAction_apply
    (x : ∀ i, ScalarUnitFactors 𝕜 E i) : scalarUnitAction x = x 0 • x 1 := (rfl)

namespace ProjectiveTensorProduct

private noncomputable def scalarUnitInsert :
    E →L[𝕜] ProjectiveTensorProduct (scalarUnitSeminorms p) :=
  let t : ContinuousMultilinearMap 𝕜 (ScalarUnitFactors 𝕜 E)
      (ProjectiveTensorProduct (scalarUnitSeminorms p)) :=
    ⟨tprod (scalarUnitSeminorms p),
      continuous_tprod (scalarUnitSeminorms p) (withSeminorms_scalarUnitSeminorms p hp)⟩
  t.toContinuousLinearMap (Fin.cons 1 fun _ => (0 : E)) 1

private theorem scalarUnitInsert_apply (x : E) :
    scalarUnitInsert p hp x = tprod (scalarUnitSeminorms p) (Fin.cons 1 fun _ => x) := by
  simp only [scalarUnitInsert, ContinuousMultilinearMap.toContinuousLinearMap_apply,
    ← ContinuousMultilinearMap.coe_coe]
  congr 1
  ext i
  fin_cases i <;> simp

private theorem scalarUnitInsert_smul (a : 𝕜) (x : E) :
    scalarUnitInsert p hp (a • x) =
      tprod (scalarUnitSeminorms p) (Fin.cons a fun _ => x) := by
  rw [map_smul, scalarUnitInsert_apply]
  simpa using ((tprod (scalarUnitSeminorms p)).cons_smul (fun _ => x) a 1).symm

private noncomputable def scalarUnitProj :
    ProjectiveTensorProduct (scalarUnitSeminorms p) →L[𝕜] E :=
  ⟨lift (scalarUnitSeminorms p) scalarUnitAction,
    continuous_lift (scalarUnitSeminorms p) p hp scalarUnitAction (by
      intro j
      refine ⟨Fin.cons {PUnit.unit} (fun _ => {j}), 1, ?_⟩
      intro x
      simp [scalarUnitAction_apply, Fin.prod_univ_two, map_smul_eq_mul,
        scalarUnitSeminorms])⟩

private theorem scalarUnitProj_tprod (x : ∀ i, ScalarUnitFactors 𝕜 E i) :
    scalarUnitProj p hp (tprod (scalarUnitSeminorms p) x) = x 0 • x 1 := by
  simp only [scalarUnitProj, ContinuousLinearMap.coe_mk', tprod_apply, lift_tprod,
    scalarUnitAction_apply]

private theorem scalarUnitProj_comp_insert :
    (scalarUnitProj p hp).comp (scalarUnitInsert p hp) = ContinuousLinearMap.id 𝕜 E := by
  ext x
  simp only [ContinuousLinearMap.comp_apply, scalarUnitInsert_apply,
    scalarUnitProj_tprod, Fin.cons_zero, Fin.cons_one, one_smul,
    ContinuousLinearMap.id_apply]

private theorem scalarUnitInsert_comp_proj :
    (scalarUnitInsert p hp).comp (scalarUnitProj p hp) = ContinuousLinearMap.id 𝕜 _ := by
  apply ContinuousLinearMap.coe_injective
  apply linearMap_ext (scalarUnitSeminorms p)
  intro x
  simp only [ContinuousLinearMap.coe_coe, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply, scalarUnitProj_tprod]
  rw [scalarUnitInsert_smul]
  congr 1
  ext i
  fin_cases i <;> simp

/-- Scalar multiplication identifies the projective tensor of the scalar field and a locally
convex space with that space, before completion. -/
noncomputable def lid : ProjectiveTensorProduct (scalarUnitSeminorms p) ≃L[𝕜] E :=
  ContinuousLinearEquiv.ofContinuousLinearMap (scalarUnitProj p hp) (scalarUnitInsert p hp)
    (scalarUnitProj_comp_insert p hp) (scalarUnitInsert_comp_proj p hp)

/-- The scalar-unit equivalence sends a pure tensor to scalar multiplication. -/
@[simp] theorem lid_tprod (x : ∀ i, ScalarUnitFactors 𝕜 E i) :
    lid p hp (⟨⨂ₜ[𝕜] i, x i⟩ : ProjectiveTensorProduct (scalarUnitSeminorms p)) =
      x 0 • x 1 := by
  simp only [lid]
  rw [ContinuousLinearEquiv.coe_ofContinuousLinearMap]
  simpa only [tprod_apply] using scalarUnitProj_tprod p hp x

/-- The inverse scalar-unit equivalence inserts the scalar `1`. -/
@[simp] theorem lid_symm_apply (x : E) :
    (lid p hp).symm x =
      (⟨⨂ₜ[𝕜] i, Fin.cons 1 (fun _ => x) i⟩ :
        ProjectiveTensorProduct (scalarUnitSeminorms p)) := by
  simp only [lid]
  rw [ContinuousLinearEquiv.symm_ofContinuousLinearMap,
    ContinuousLinearEquiv.coe_ofContinuousLinearMap]
  simpa only [tprod_apply] using scalarUnitInsert_apply p hp x

/-- The scalar-unit identification commutes with the algebraic tensor map of the scalar
identity and any linear map. No boundedness or separation hypothesis is required. -/
theorem lid_map {F : Type u} [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F]
    {τ : Type w} (q : SeminormFamily 𝕜 F τ) (hq : WithSeminorms q)
    (f : E →ₗ[𝕜] F) (z : ProjectiveTensorProduct (scalarUnitSeminorms p)) :
    lid q hq (map (scalarUnitSeminorms p) (scalarUnitSeminorms q)
      (Fin.cons LinearMap.id (fun _ => f)) z) = f (lid p hp z) := by
  have h : (lid q hq).toLinearMap.comp
      (map (scalarUnitSeminorms p) (scalarUnitSeminorms q)
        (Fin.cons LinearMap.id (fun _ => f))) = f.comp (lid p hp).toLinearMap := by
    apply linearMap_ext (scalarUnitSeminorms p)
    intro x
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe,
      ContinuousLinearEquiv.coe_toLinearEquiv, tprod_apply, map_tprod, lid_tprod,
      Fin.cons_zero, Fin.cons_one, LinearMap.id_apply]
    exact (f.map_smul (x 0) (x 1)).symm
  exact LinearMap.congr_fun h z

/-- The scalar-unit identification preserves every factor seminorm with constant one,
including seminorms outside the family defining the topology. -/
theorem projectiveSeminormOf_cons_normSeminorm_eq_apply_lid (q : Seminorm 𝕜 E)
    (z : ProjectiveTensorProduct (scalarUnitSeminorms p)) :
    PiTensorProduct.projectiveSeminormOf
      (Fin.cons (normSeminorm 𝕜 𝕜) (fun _ => q)) z.toPiTensorProduct = q (lid p hp z) := by
  have hbound := PiTensorProduct.seminorm_lift_le
    (Fin.cons (normSeminorm 𝕜 𝕜) (fun _ => q)) q scalarUnitAction
    (C := 1) zero_le_one (by
      intro x
      simp [scalarUnitAction_apply, Fin.prod_univ_two, map_smul_eq_mul])
  have hnorm (x : E) : PiTensorProduct.projectiveSeminormOf
      (Fin.cons (normSeminorm 𝕜 𝕜) (fun _ => q))
      (⨂ₜ[𝕜] i, (Fin.cons 1 (fun _ => x) : ∀ i, ScalarUnitFactors 𝕜 E i) i) = q x := by
    apply le_antisymm
    · simpa [Fin.prod_univ_two] using PiTensorProduct.projectiveSeminormOf_tprod_le
        (Fin.cons (normSeminorm 𝕜 𝕜) (fun _ => q))
        (Fin.cons 1 (fun _ => x) : ∀ i, ScalarUnitFactors 𝕜 E i)
    · simpa [scalarUnitAction_apply] using
        hbound (⨂ₜ[𝕜] i, (Fin.cons 1 (fun _ => x) : ∀ i, ScalarUnitFactors 𝕜 E i) i)
  have hz := (lid p hp).symm_apply_apply z
  rw [lid_symm_apply p hp] at hz
  rw [← hz]
  simpa only [lid_tprod, Fin.cons_zero, Fin.cons_one, one_smul] using hnorm (lid p hp z)

/-- Selecting the scalar norm and a finite family of vector seminorms gives exactly the
corresponding supremum seminorm after the scalar-unit identification. -/
theorem seminormFamily_cons_eq_sup_apply_lid (t : Finset σ)
    (z : ProjectiveTensorProduct (scalarUnitSeminorms p)) :
    seminormFamily (scalarUnitSeminorms p) (Fin.cons {PUnit.unit} (fun _ => t)) z =
      t.sup p (lid p hp z) := by
  rw [seminormFamily_apply]
  have h : (fun i => ((Fin.cons {PUnit.unit} (fun _ => t) :
      ∀ i, Finset (ScalarUnitIndices σ i)) i).sup (scalarUnitSeminorms p i)) =
      Fin.cons (normSeminorm 𝕜 𝕜) (fun _ => t.sup p) := by
    funext i
    fin_cases i <;> simp [scalarUnitSeminorms]
  rw [h]
  exact projectiveSeminormOf_cons_normSeminorm_eq_apply_lid p hp (t.sup p) z

end ProjectiveTensorProduct

end Topology

namespace CompletedProjectiveTensorProduct

variable [UniformSpace E] [IsUniformAddGroup E]
  [T0Space E] [CompleteSpace E]
variable (hp : WithSeminorms p)

private noncomputable def scalarUnitProj :
    CompletedProjectiveTensorProduct (scalarUnitSeminorms p) →L[𝕜] E :=
  letI := hp.continuousSMul
  letI := uniformContinuousConstSMul_of_continuousConstSMul 𝕜 E
  (ProjectiveTensorProduct.lid p hp).toContinuousLinearMap.fromCompletion

private theorem scalarUnitProj_apply_coe
    (z : ProjectiveTensorProduct (scalarUnitSeminorms p)) :
    scalarUnitProj p hp (z : CompletedProjectiveTensorProduct (scalarUnitSeminorms p)) =
      ProjectiveTensorProduct.lid p hp z := by
  let _ := hp.continuousSMul
  let _ := uniformContinuousConstSMul_of_continuousConstSMul 𝕜 E
  exact ContinuousLinearMap.fromCompletion_apply_coe _ z

private noncomputable def scalarUnitInsert :
    E →L[𝕜] CompletedProjectiveTensorProduct (scalarUnitSeminorms p) :=
  UniformSpace.Completion.toComplL.comp
    (ProjectiveTensorProduct.lid p hp).symm.toContinuousLinearMap

omit [IsUniformAddGroup E] [T0Space E] [CompleteSpace E] in
private theorem scalarUnitInsert_apply (x : E) :
    scalarUnitInsert p hp x = ((ProjectiveTensorProduct.lid p hp).symm x :
      CompletedProjectiveTensorProduct (scalarUnitSeminorms p)) := by
  simp only [scalarUnitInsert, ContinuousLinearMap.comp_apply,
    UniformSpace.Completion.coe_toComplL, ContinuousLinearEquiv.coe_coe]

private theorem scalarUnitProj_comp_insert :
    (scalarUnitProj p hp).comp (scalarUnitInsert p hp) = ContinuousLinearMap.id 𝕜 E := by
  ext x
  simp [scalarUnitInsert, scalarUnitProj_apply_coe]

private theorem scalarUnitInsert_comp_proj :
    (scalarUnitInsert p hp).comp (scalarUnitProj p hp) = ContinuousLinearMap.id 𝕜 _ := by
  apply continuousLinearMap_ext (scalarUnitSeminorms p)
  intro x
  rw [ContinuousLinearMap.comp_apply, scalarUnitProj_apply_coe, scalarUnitInsert_apply,
    ContinuousLinearEquiv.symm_apply_apply, ContinuousLinearMap.id_apply]

/-- The scalar field is a left unit for the completed projective tensor of complete Hausdorff
locally convex spaces, with the caller's compatible additive uniformity. -/
noncomputable def lid : CompletedProjectiveTensorProduct (scalarUnitSeminorms p) ≃L[𝕜] E :=
  ContinuousLinearEquiv.ofContinuousLinearMap (scalarUnitProj p hp) (scalarUnitInsert p hp)
    (scalarUnitProj_comp_insert p hp) (scalarUnitInsert_comp_proj p hp)

/-- The completed scalar-unit equivalence extends the algebraic scalar-unit equivalence. -/
@[simp] theorem lid_coe (z : ProjectiveTensorProduct (scalarUnitSeminorms p)) :
    lid p hp (z : CompletedProjectiveTensorProduct (scalarUnitSeminorms p)) =
      ProjectiveTensorProduct.lid p hp z :=
  scalarUnitProj_apply_coe p hp z

/-- The completed scalar-unit equivalence sends a pure tensor to scalar multiplication. -/
theorem lid_tprod (x : ∀ i, ScalarUnitFactors 𝕜 E i) :
    lid p hp (tprod (scalarUnitSeminorms p) (withSeminorms_scalarUnitSeminorms p hp) x) =
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
  rw [ContinuousLinearEquiv.symm_ofContinuousLinearMap,
    ContinuousLinearEquiv.coe_ofContinuousLinearMap]
  rw [scalarUnitInsert_apply, ProjectiveTensorProduct.lid_symm_apply]

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
