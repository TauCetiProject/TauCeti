/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.GradedModuleCat.BimoduleTensor.Unit
public import TauCeti.RepresentationTheory.Quiver.Zigzag.Braid.Tensor

/-!
# Unit identifications for the actual graded zigzag bimodule

The existing graded zigzag bimodule is the regular unit for balanced tensor composition.
It is identified with the universe-lifted regular graded unit. The resulting left and
right unit isomorphisms identify the mixed terms in tensor products of braid complexes.
Their pure-tensor formulas express the two restricted enveloping-algebra actions.
The constructions specialize `GradedModuleCat.bimoduleTensorLeftUnitor` and
`GradedModuleCat.bimoduleTensorRightUnitor` using `ULift.moduleEquiv`.
-/

public section

noncomputable section

namespace TauCeti

open CategoryTheory MulOpposite
open scoped TensorProduct

universe u w

variable (k : Type w) [CommRing k] {V : Type u} (G : SimpleGraph V) [Finite V]

local notation "Z" => AlgCat.carrier (zigzagAlgebra k G)
local notation "Γ" => zigzagAlgebraInternalGrading k G

attribute [local instance] zigzagAlgebraIntegerGradedAlgebra

/-- The existing graded zigzag bimodule is the regular graded unit. -/
def zigzagGradedBimoduleUnitIso :
    GradedModuleCat.bimoduleUnit.{0} Γ ≅ zigzagGradedBimodule k G :=
  GradedModuleCat.isoMk
    (ULift.moduleEquiv (R := Z ⊗[k] Zᵐᵒᵖ) (M := zigzagGradedBimodule k G)) fun p x ↦ by
      rw [GradedModuleCat.mem_bimoduleUnit_piece_iff.{0} Γ,
        GradedModuleCat.bimoduleUnitEquiv_symm_apply]
      exact (mem_zigzagBimoduleGrade_iff (d := p) (x := x.down)).symm

@[simp]
theorem zigzagGradedBimoduleUnitIso_hom_apply (x : GradedModuleCat.bimoduleUnit.{0} Γ) :
    (zigzagGradedBimoduleUnitIso k G).hom.hom x = x.down := (rfl)

@[simp]
theorem zigzagGradedBimoduleUnitIso_inv_apply (x : zigzagGradedBimodule k G) :
    (zigzagGradedBimoduleUnitIso k G).inv.hom x = ULift.up x := (rfl)

variable (M : GradedModuleCat.{max u w} (zigzagEnvelopingGrading k G).piece)

/-- Tensoring the actual regular zigzag bimodule on the left preserves a graded bimodule. -/
def zigzagBimoduleLeftUnitor :
    GradedModuleCat.bimoduleTensorObj Γ Γ Γ (zigzagGradedBimodule k G) M ≅ M :=
  ((zigzagBimoduleTensor k G).flip.obj M).mapIso (zigzagGradedBimoduleUnitIso k G).symm ≪≫
    GradedModuleCat.bimoduleTensorLeftUnitor.{0} Γ Γ M

/-- Tensoring the actual regular zigzag bimodule on the right preserves a graded bimodule. -/
def zigzagBimoduleRightUnitor :
    GradedModuleCat.bimoduleTensorObj Γ Γ Γ M (zigzagGradedBimodule k G) ≅ M :=
  ((zigzagBimoduleTensor k G).obj M).mapIso (zigzagGradedBimoduleUnitIso k G).symm ≪≫
    GradedModuleCat.bimoduleTensorRightUnitor.{0} Γ Γ M

@[simp]
theorem zigzagBimoduleLeftUnitor_hom_tmul (z : zigzagGradedBimodule k G) (m : M) :
    (zigzagBimoduleLeftUnitor k G M).hom.hom
      (GradedModuleCat.bimoduleTensorTmul Γ Γ Γ (zigzagGradedBimodule k G) M z m) =
      ((Bimodule.of (AlgHom.id k Z)).symm z ⊗ₜ[k] (1 : Zᵐᵒᵖ)) • m := by
  -- Compute the tensor map induced by transporting the regular unit.
  change (GradedModuleCat.bimoduleTensorMap Γ Γ Γ
      (zigzagGradedBimoduleUnitIso k G).inv (𝟙 M) ≫
    (GradedModuleCat.bimoduleTensorLeftUnitor.{0} Γ Γ M).hom).hom _ = _
  rw [GradedModuleCat.bimoduleTensorLeftUnitor_hom]
  simp only [GradedModuleCat.hom_comp, LinearMap.comp_apply,
    GradedModuleCat.bimoduleTensorMap_tmul Γ Γ Γ
      (zigzagGradedBimoduleUnitIso k G).inv (𝟙 M) z m,
    GradedModuleCat.hom_id, LinearMap.id_apply,
    GradedModuleCat.bimoduleTensorLeftUnitorHom_tmul.{0} Γ Γ M,
    GradedModuleCat.bimoduleUnitEquiv_symm_apply.{0} Γ]
  simp only [zigzagGradedBimoduleUnitIso_inv_apply]

@[simp]
theorem zigzagBimoduleRightUnitor_hom_tmul (m : M) (z : zigzagGradedBimodule k G) :
    (zigzagBimoduleRightUnitor k G M).hom.hom
      (GradedModuleCat.bimoduleTensorTmul Γ Γ Γ M (zigzagGradedBimodule k G) m z) =
      ((1 : Z) ⊗ₜ[k] op ((Bimodule.of (AlgHom.id k Z)).symm z)) • m := by
  -- Compute the tensor map induced by transporting the regular unit.
  change (GradedModuleCat.bimoduleTensorMap Γ Γ Γ (𝟙 M)
      (zigzagGradedBimoduleUnitIso k G).inv ≫
    (GradedModuleCat.bimoduleTensorRightUnitor.{0} Γ Γ M).hom).hom _ = _
  rw [GradedModuleCat.bimoduleTensorRightUnitor_hom]
  simp only [GradedModuleCat.hom_comp, LinearMap.comp_apply,
    GradedModuleCat.bimoduleTensorMap_tmul Γ Γ Γ
      (𝟙 M) (zigzagGradedBimoduleUnitIso k G).inv m z,
    GradedModuleCat.hom_id, LinearMap.id_apply,
    GradedModuleCat.bimoduleTensorRightUnitorHom_tmul.{0} Γ Γ M,
    GradedModuleCat.bimoduleUnitEquiv_symm_apply.{0} Γ]
  simp only [zigzagGradedBimoduleUnitIso_inv_apply]

@[simp]
theorem zigzagBimoduleLeftUnitor_inv_apply (m : M) :
    (zigzagBimoduleLeftUnitor k G M).inv.hom m =
      GradedModuleCat.bimoduleTensorTmul Γ Γ Γ (zigzagGradedBimodule k G) M
        (Bimodule.of (AlgHom.id k Z) 1) m := by
  -- Undo the unit identification after inserting the generic regular unit.
  change ((GradedModuleCat.bimoduleTensorLeftUnitor.{0} Γ Γ M).inv ≫
    GradedModuleCat.bimoduleTensorMap Γ Γ Γ
      (zigzagGradedBimoduleUnitIso k G).hom (𝟙 M)).hom m = _
  rw [GradedModuleCat.bimoduleTensorLeftUnitor_inv]
  simp only [GradedModuleCat.hom_comp, LinearMap.comp_apply,
    GradedModuleCat.bimoduleTensorLeftUnitorInv_apply.{0} Γ Γ M,
    GradedModuleCat.bimoduleTensorMap_tmul Γ Γ Γ
      (zigzagGradedBimoduleUnitIso k G).hom (𝟙 M),
    GradedModuleCat.hom_id, LinearMap.id_apply, zigzagGradedBimoduleUnitIso_hom_apply]
  simp only [GradedModuleCat.bimoduleUnitEquiv_apply.{0} Γ]

@[simp]
theorem zigzagBimoduleRightUnitor_inv_apply (m : M) :
    (zigzagBimoduleRightUnitor k G M).inv.hom m =
      GradedModuleCat.bimoduleTensorTmul Γ Γ Γ M (zigzagGradedBimodule k G) m
        (Bimodule.of (AlgHom.id k Z) 1) := by
  -- Undo the unit identification after inserting the generic regular unit.
  change ((GradedModuleCat.bimoduleTensorRightUnitor.{0} Γ Γ M).inv ≫
    GradedModuleCat.bimoduleTensorMap Γ Γ Γ (𝟙 M)
      (zigzagGradedBimoduleUnitIso k G).hom).hom m = _
  rw [GradedModuleCat.bimoduleTensorRightUnitor_inv]
  simp only [GradedModuleCat.hom_comp, LinearMap.comp_apply,
    GradedModuleCat.bimoduleTensorRightUnitorInv_apply.{0} Γ Γ M,
    GradedModuleCat.bimoduleTensorMap_tmul Γ Γ Γ
      (𝟙 M) (zigzagGradedBimoduleUnitIso k G).hom,
    GradedModuleCat.hom_id, LinearMap.id_apply, zigzagGradedBimoduleUnitIso_hom_apply]
  simp only [GradedModuleCat.bimoduleUnitEquiv_apply.{0} Γ]

/-- The actual left unit identification commutes with graded bimodule maps. -/
@[reassoc (attr := simp)]
theorem zigzagBimoduleLeftUnitor_naturality
    {N : GradedModuleCat.{max u w} (zigzagEnvelopingGrading k G).piece} (f : M ⟶ N) :
    GradedModuleCat.bimoduleTensorMap Γ Γ Γ (𝟙 (zigzagGradedBimodule k G)) f ≫
        (zigzagBimoduleLeftUnitor k G N).hom =
      (zigzagBimoduleLeftUnitor k G M).hom ≫ f := by
  apply GradedModuleCat.bimoduleTensor_hom_ext Γ Γ Γ
  intro z m
  simp only [GradedModuleCat.hom_comp, LinearMap.comp_apply,
    GradedModuleCat.bimoduleTensorMap_tmul, GradedModuleCat.hom_id, LinearMap.id_apply,
    zigzagBimoduleLeftUnitor_hom_tmul k G N,
    zigzagBimoduleLeftUnitor_hom_tmul k G M, map_smul]

/-- The actual right unit identification commutes with graded bimodule maps. -/
@[reassoc (attr := simp)]
theorem zigzagBimoduleRightUnitor_naturality
    {N : GradedModuleCat.{max u w} (zigzagEnvelopingGrading k G).piece} (f : M ⟶ N) :
    GradedModuleCat.bimoduleTensorMap Γ Γ Γ f (𝟙 (zigzagGradedBimodule k G)) ≫
        (zigzagBimoduleRightUnitor k G N).hom =
      (zigzagBimoduleRightUnitor k G M).hom ≫ f := by
  apply GradedModuleCat.bimoduleTensor_hom_ext Γ Γ Γ
  intro m z
  simp only [GradedModuleCat.hom_comp, LinearMap.comp_apply,
    GradedModuleCat.bimoduleTensorMap_tmul, GradedModuleCat.hom_id, LinearMap.id_apply,
    zigzagBimoduleRightUnitor_hom_tmul k G N,
    zigzagBimoduleRightUnitor_hom_tmul k G M, map_smul]

/-- The two unit identifications agree when both factors are the regular bimodule. -/
theorem zigzagBimoduleUnitHom_eq :
    (zigzagBimoduleLeftUnitor k G (zigzagGradedBimodule k G)).hom =
      (zigzagBimoduleRightUnitor k G (zigzagGradedBimodule k G)).hom := by
  apply GradedModuleCat.bimoduleTensor_hom_ext Γ Γ Γ
  intro x y
  rw [zigzagBimoduleLeftUnitor_hom_tmul k G (zigzagGradedBimodule k G) x y,
    zigzagBimoduleRightUnitor_hom_tmul k G (zigzagGradedBimodule k G) x y]
  -- Normalize the exposed graded-bimodule carrier to use the regular action formula.
  change Bimodule (AlgHom.id k Z) at x y
  apply (Bimodule.of (AlgHom.id k Z)).symm.injective
  change (Bimodule.of (AlgHom.id k Z)).symm
      (((Bimodule.of (AlgHom.id k Z)).symm x ⊗ₜ[k] (1 : Zᵐᵒᵖ)) •
        (y : Bimodule (AlgHom.id k Z))) =
    (Bimodule.of (AlgHom.id k Z)).symm
      (((1 : Z) ⊗ₜ[k] op ((Bimodule.of (AlgHom.id k Z)).symm y)) •
        (x : Bimodule (AlgHom.id k Z)))
  simp only [Bimodule.symm_smul, AlgHom.id_apply, unop_one, mul_one, unop_op, one_mul]

end TauCeti
