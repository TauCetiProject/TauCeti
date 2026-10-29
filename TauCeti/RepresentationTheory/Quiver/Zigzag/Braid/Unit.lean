/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.GradedModuleCat.BimoduleTensor.Unit
public import TauCeti.RepresentationTheory.Quiver.Zigzag.Braid.Tensor
public import Mathlib.Algebra.Homology.Homotopy

/-!
# Unit identifications for the actual graded zigzag bimodule

The existing graded zigzag bimodule is the regular unit for balanced tensor composition.
It is identified with the universe-lifted regular graded unit, the unit of the graded
bimodule setting of the zigzag algebra. The resulting left and right unit isomorphisms
identify the mixed terms in tensor products of braid complexes. Their pure-tensor formulas
express the two restricted enveloping-algebra actions. The constructions specialize
`GradedModuleCat.bimoduleTensorLeftUnitor` and `GradedModuleCat.bimoduleTensorRightUnitor`
using `ULift.moduleEquiv`.

The unit complex of the graded bimodule setting of the zigzag algebra, the regular graded
zigzag bimodule in cohomological degree zero, is `zigzagBraidUnitComplex`;
`zigzagBraidUnitComplexHomotopyEquiv` identifies it with the unit complex of that setting.
The `hom` and the `inv` of that equivalence are characterised by
`zigzagBraidUnitComplexHomotopyEquiv_hom` and `zigzagBraidUnitComplexHomotopyEquiv_inv`.
-/

public section

noncomputable section

namespace TauCeti

open CategoryTheory MulOpposite
open scoped TensorProduct

universe u w

variable (k : Type w) [CommRing k] {V : Type u} (G : SimpleGraph V) [Finite V]

local notation "Z" => AlgCat.carrier (zigzagAlgebra k G)
local notation "c" => ComplexShape.up ℤ
local notation "Γ" => zigzagAlgebraInternalGrading k G
local notation "F" => (GradedModuleCat.bimoduleTensor Γ Γ Γ :
  GradedBimoduleCat k Γ ⥤ GradedBimoduleCat k Γ ⥤ GradedBimoduleCat k Γ)

attribute [local instance] zigzagAlgebraIntegerGradedAlgebra

/-- The existing graded zigzag bimodule is the regular graded unit, at the lift universe `w`
of the ground ring. This is the unit of the graded bimodule setting of the zigzag algebra, so
the single isomorphism serves both the unit identifications of the braid complexes and the
unit complex of that setting. -/
def zigzagGradedBimoduleUnitIso :
    GradedModuleCat.bimoduleUnit.{w} Γ ≅ zigzagGradedBimodule k G :=
  GradedModuleCat.isoMk
    (ULift.moduleEquiv (R := Z ⊗[k] Zᵐᵒᵖ) (M := zigzagGradedBimodule k G)) fun p x ↦ by
      rw [GradedModuleCat.mem_bimoduleUnit_piece_iff.{w} Γ,
        GradedModuleCat.bimoduleUnitEquiv_symm_apply]
      exact (mem_zigzagBimoduleGrade_iff (d := p) (x := x.down)).symm

@[simp]
theorem zigzagGradedBimoduleUnitIso_hom_apply (x : GradedModuleCat.bimoduleUnit.{w} Γ) :
    (zigzagGradedBimoduleUnitIso k G).hom.hom x = x.down := (rfl)

@[simp]
theorem zigzagGradedBimoduleUnitIso_inv_apply (x : zigzagGradedBimodule k G) :
    (zigzagGradedBimoduleUnitIso k G).inv.hom x = ULift.up x := (rfl)

/-- The regular graded zigzag bimodule concentrated in cohomological degree zero: the
common target of the two one-sided inverse-product equivalences of the braid family. -/
abbrev zigzagBraidUnitComplex :
    HomologicalComplex (GradedModuleCat.{max u w} (zigzagEnvelopingGrading k G).piece) c :=
  (HomologicalComplex.single (GradedModuleCat.{max u w} (zigzagEnvelopingGrading k G).piece)
    c 0).obj (zigzagGradedBimodule k G)

/-- The regular graded zigzag bimodule is the unit complex of the graded bimodule setting of
the zigzag algebra: the homotopy equivalence between the regular graded bimodule in
cohomological degree zero and the unit complex of that setting. It is the transport of
`zigzagGradedBimoduleUnitIso` to the single-degree complex. -/
def zigzagBraidUnitComplexHomotopyEquiv :
    HomotopyEquiv (zigzagBraidUnitComplex k G)
      (gradedBimoduleUnitComplex k (zigzagAlgebraInternalGrading k G)) :=
  HomotopyEquiv.ofIso
    ((HomologicalComplex.single (GradedModuleCat.{max u w} (zigzagEnvelopingGrading k G).piece)
      c 0).mapIso (zigzagGradedBimoduleUnitIso k G).symm)

-- The characterising lemmas below are written `(rfl)` and not `rfl`: a theorem whose proof is
-- syntactically `rfl` is tagged `@[defeq]`, and the module system refuses to export a
-- `@[defeq]` theorem whose proof needs the body of a definition that is not exposed.

/-- The `hom` of the unit-complex homotopy equivalence of the zigzag setting is the map of
the single-degree complex induced by the inverse of the unit isomorphism. This is the
characterisation that lets a consumer compute the `hom` of the unit comparison. -/
@[simp]
theorem zigzagBraidUnitComplexHomotopyEquiv_hom :
    (zigzagBraidUnitComplexHomotopyEquiv k G).hom =
      (HomologicalComplex.single (GradedModuleCat.{max u w} (zigzagEnvelopingGrading k G).piece)
        c 0).map (zigzagGradedBimoduleUnitIso k G).inv := (rfl)

/-- The `inv` of the unit-complex homotopy equivalence of the zigzag setting is the map of
the single-degree complex induced by the unit isomorphism. This is the characterisation that
lets a consumer compute the `inv` of the unit comparison. -/
@[simp]
theorem zigzagBraidUnitComplexHomotopyEquiv_inv :
    (zigzagBraidUnitComplexHomotopyEquiv k G).inv =
      (HomologicalComplex.single (GradedModuleCat.{max u w} (zigzagEnvelopingGrading k G).piece)
        c 0).map (zigzagGradedBimoduleUnitIso k G).hom := (rfl)

variable (M : GradedModuleCat.{max u w} (zigzagEnvelopingGrading k G).piece)

/-- Tensoring the actual regular zigzag bimodule on the left preserves a graded bimodule. -/
def zigzagBimoduleLeftUnitor :
    GradedModuleCat.bimoduleTensorObj Γ Γ Γ (zigzagGradedBimodule k G) M ≅ M :=
  ((F).flip.obj M).mapIso
      (zigzagGradedBimoduleUnitIso k G).symm ≪≫
    GradedModuleCat.bimoduleTensorLeftUnitor.{w} Γ Γ M

/-- Tensoring the actual regular zigzag bimodule on the right preserves a graded bimodule. -/
def zigzagBimoduleRightUnitor :
    GradedModuleCat.bimoduleTensorObj Γ Γ Γ M (zigzagGradedBimodule k G) ≅ M :=
  ((F).obj M).mapIso (zigzagGradedBimoduleUnitIso k G).symm ≪≫
    GradedModuleCat.bimoduleTensorRightUnitor.{w} Γ Γ M

@[simp]
theorem zigzagBimoduleLeftUnitor_hom_tmul (z : zigzagGradedBimodule k G) (m : M) :
    (zigzagBimoduleLeftUnitor k G M).hom.hom
      (GradedModuleCat.bimoduleTensorTmul Γ Γ Γ (zigzagGradedBimodule k G) M z m) =
      ((Bimodule.of (AlgHom.id k Z)).symm z ⊗ₜ[k] (1 : Zᵐᵒᵖ)) • m := by
  -- Rewrite the composite unit identification and generic left unitor into its two factors.
  simp only [zigzagBimoduleLeftUnitor, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
    GradedModuleCat.hom_comp, LinearMap.comp_apply, Functor.flip_obj_map,
    GradedModuleCat.bimoduleTensor_map_app]
  rw [GradedModuleCat.bimoduleTensorLeftUnitor_hom]
  simp only [GradedModuleCat.bimoduleTensorMap_tmul Γ Γ Γ
      (zigzagGradedBimoduleUnitIso k G).inv (𝟙 M) z m,
    GradedModuleCat.hom_id, LinearMap.id_apply,
    GradedModuleCat.bimoduleTensorLeftUnitorHom_tmul.{w} Γ Γ M,
    GradedModuleCat.bimoduleUnitEquiv_symm_apply.{w} Γ]
  simp only [zigzagGradedBimoduleUnitIso_inv_apply]

@[simp]
theorem zigzagBimoduleRightUnitor_hom_tmul (m : M) (z : zigzagGradedBimodule k G) :
    (zigzagBimoduleRightUnitor k G M).hom.hom
      (GradedModuleCat.bimoduleTensorTmul Γ Γ Γ M (zigzagGradedBimodule k G) m z) =
      ((1 : Z) ⊗ₜ[k] op ((Bimodule.of (AlgHom.id k Z)).symm z)) • m := by
  -- Rewrite the composite unit identification and generic right unitor into its two factors.
  simp only [zigzagBimoduleRightUnitor, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
    GradedModuleCat.hom_comp, LinearMap.comp_apply, GradedModuleCat.bimoduleTensor_obj_map]
  rw [GradedModuleCat.bimoduleTensorRightUnitor_hom]
  simp only [GradedModuleCat.bimoduleTensorMap_tmul Γ Γ Γ
      (𝟙 M) (zigzagGradedBimoduleUnitIso k G).inv m z,
    GradedModuleCat.hom_id, LinearMap.id_apply,
    GradedModuleCat.bimoduleTensorRightUnitorHom_tmul.{w} Γ Γ M,
    GradedModuleCat.bimoduleUnitEquiv_symm_apply.{w} Γ]
  simp only [zigzagGradedBimoduleUnitIso_inv_apply]

@[simp]
theorem zigzagBimoduleLeftUnitor_inv_apply (m : M) :
    (zigzagBimoduleLeftUnitor k G M).inv.hom m =
      GradedModuleCat.bimoduleTensorTmul Γ Γ Γ (zigzagGradedBimodule k G) M
        (Bimodule.of (AlgHom.id k Z) 1) m := by
  -- Rewrite the composite unit identification and generic left unitor into its two factors.
  simp only [zigzagBimoduleLeftUnitor, Iso.trans_inv, Functor.mapIso_inv, Iso.symm_inv,
    GradedModuleCat.hom_comp, LinearMap.comp_apply, Functor.flip_obj_map,
    GradedModuleCat.bimoduleTensor_map_app]
  rw [GradedModuleCat.bimoduleTensorLeftUnitor_inv]
  simp only [GradedModuleCat.bimoduleTensorLeftUnitorInv_apply.{w} Γ Γ M,
    GradedModuleCat.bimoduleTensorMap_tmul Γ Γ Γ
      (zigzagGradedBimoduleUnitIso k G).hom (𝟙 M),
    GradedModuleCat.hom_id, LinearMap.id_apply, zigzagGradedBimoduleUnitIso_hom_apply]
  simp only [GradedModuleCat.bimoduleUnitEquiv_apply.{w} Γ]

@[simp]
theorem zigzagBimoduleRightUnitor_inv_apply (m : M) :
    (zigzagBimoduleRightUnitor k G M).inv.hom m =
      GradedModuleCat.bimoduleTensorTmul Γ Γ Γ M (zigzagGradedBimodule k G) m
        (Bimodule.of (AlgHom.id k Z) 1) := by
  -- Rewrite the composite unit identification and generic right unitor into its two factors.
  simp only [zigzagBimoduleRightUnitor, Iso.trans_inv, Functor.mapIso_inv, Iso.symm_inv,
    GradedModuleCat.hom_comp, LinearMap.comp_apply, GradedModuleCat.bimoduleTensor_obj_map]
  rw [GradedModuleCat.bimoduleTensorRightUnitor_inv]
  simp only [GradedModuleCat.bimoduleTensorRightUnitorInv_apply.{w} Γ Γ M,
    GradedModuleCat.bimoduleTensorMap_tmul Γ Γ Γ
      (𝟙 M) (zigzagGradedBimoduleUnitIso k G).hom,
    GradedModuleCat.hom_id, LinearMap.id_apply, zigzagGradedBimoduleUnitIso_hom_apply]
  simp only [GradedModuleCat.bimoduleUnitEquiv_apply.{w} Γ]

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
  -- The two sides are elements of the carrier of `zigzagGradedBimodule k G`, which is the type
  -- synonym `Bimodule (AlgHom.id k Z)` by construction, but the tensor action in the goal was
  -- elaborated at the carrier instance of that graded module. No rewrite lemma reaches it:
  -- `Bimodule.symm_smul` rewrites `(Bimodule.of f).symm (r • y)` only when `y` is syntactically a
  -- `Bimodule f` and the scalar action is the `Bimodule` one, and no equation can restate the
  -- type of a local hypothesis. The two `change`s below re-elaborate `x`, `y` and the goal at
  -- that type; `Bimodule.symm_smul` applies to the result.
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
