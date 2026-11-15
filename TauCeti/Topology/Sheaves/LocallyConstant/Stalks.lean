/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Stalk
public import TauCeti.Topology.Sheaves.LocallyConstant.Basic

/-!
# Stalks of the locally constant ring sheaf

The native ring stalk of the sheaf of locally constant `R`-valued functions at any point is
canonically `R`. The forward map evaluates a representative at the point; its inverse takes
the germ of a constant function. In particular, two locally constant sections have the same
germ precisely when their values at that point agree. No separation or local connectedness
assumption on the space is needed, and the coefficient ring need not be commutative.

The constant-ring adapter preserves module stalks semilinearly over this ring isomorphism
(`TopCat.Sheaf.toLocallyConstantModuleStalkEquiv`). The equivalence sends each module germ
to the same germ, so the ring-stalk action becomes the original `R`-action.

This identification concerns stalks, not global sections: on a disconnected space the ring
of global locally constant functions need not be `R`.

The construction uses Mathlib's native stalk colimit, `LocallyConstant.evalRingHom`, and
`PresheafOfModules.germ_ringCat_smul` for the module structure on stalks.
-/

public section

noncomputable section

open CategoryTheory Limits Opposite TopologicalSpace

universe u

namespace TopCat

variable {X : TopCat.{u}} {R : Type u} [Ring R]

private def locallyConstantStalkEval (x : X) :
    (locallyConstantRingCatPresheaf X R).stalk x ⟶ RingCat.of R :=
  colimit.desc ((OpenNhds.inclusion x).op ⋙ locallyConstantRingCatPresheaf X R)
    { pt := RingCat.of R
      ι :=
        { app := fun U ↦ RingCat.ofHom (LocallyConstant.evalRingHom ⟨x, U.unop.2⟩)
          naturality := fun _ _ _ ↦ by ext; rfl } }

private theorem locallyConstantStalkEval_germ (x : X) (U : Opens X) (hx : x ∈ U)
    (f : LocallyConstant U R) :
    locallyConstantStalkEval x ((locallyConstantRingCatPresheaf X R).germ U x hx f) =
      f ⟨x, hx⟩ :=
  ConcreteCategory.congr_hom
    (colimit.ι_desc (F := (OpenNhds.inclusion x).op ⋙ locallyConstantRingCatPresheaf X R)
      _ (op ⟨U, hx⟩)) f

/-- The germ of a locally constant function is the germ of the global constant with its value
at the point. -/
theorem germ_locallyConstant_eq_const (x : X) (U : Opens X) (hx : x ∈ U)
    (f : LocallyConstant U R) :
    (locallyConstantRingCatPresheaf X R).germ U x hx f =
      (locallyConstantRingCatPresheaf X R).germ ⊤ x (by trivial)
        (LocallyConstant.const _ (f ⟨x, hx⟩)) := by
  obtain ⟨V, hV, hxV, hf⟩ := f.isLocallyConstant.exists_open ⟨x, hx⟩
  let W : Opens X := ⟨Subtype.val '' V, U.isOpen.isOpenMap_subtype_val _ hV⟩
  have hWU : W ≤ U := by rintro _ ⟨y, _, rfl⟩; exact y.2
  have hxW : x ∈ W := ⟨⟨x, hx⟩, hxV, rfl⟩
  have he : (locallyConstantRingCatPresheaf X R).map (homOfLE hWU).op f =
      (locallyConstantRingCatPresheaf X R).map (homOfLE (le_top : W ≤ ⊤)).op
        (LocallyConstant.const _ (f ⟨x, hx⟩)) := by
    apply LocallyConstant.ext
    rintro ⟨y, hy⟩
    obtain ⟨z, hz, rfl⟩ := hy
    exact hf z hz
  exact (Presheaf.germ_res_apply (locallyConstantRingCatPresheaf X R)
    (homOfLE hWU) x hxW f).symm.trans
    ((congrArg ((locallyConstantRingCatPresheaf X R).germ W x hxW) he).trans
      (Presheaf.germ_res_apply _ (homOfLE (le_top : W ≤ ⊤)) x hxW _))

/-- Evaluation identifies the stalk of the locally constant ring sheaf with its coefficient
ring. Its inverse takes a scalar to the germ of the global constant function. -/
def locallyConstantRingCatStalkIso (x : X) :
    Presheaf.stalk (X := X) (locallyConstantRingCatSheaf X R).obj x ≅ RingCat.of R where
  hom := locallyConstantStalkEval x
  inv := RingCat.ofHom (LocallyConstant.constRingHom : R →+* LocallyConstant (⊤ : Opens X) R) ≫
    (locallyConstantRingCatPresheaf X R).germ ⊤ x (by trivial)
  hom_inv_id := by
    apply Presheaf.stalk_hom_ext
    intro U hx
    ext f
    exact (congrArg (fun r : R ↦ (locallyConstantRingCatPresheaf X R).germ ⊤ x
      (by trivial) (LocallyConstant.const _ r)) (locallyConstantStalkEval_germ x U hx f)).trans
        (germ_locallyConstant_eq_const x U hx f).symm
  inv_hom_id := by
    ext r
    exact locallyConstantStalkEval_germ x ⊤ (by trivial) (LocallyConstant.const _ r)

/-- The stalk isomorphism evaluates any representative at its base point. -/
@[simp]
theorem locallyConstantRingCatStalkIso_hom_germ (x : X) (U : Opens X) (hx : x ∈ U)
    (f : LocallyConstant U R) :
    dsimp% ((locallyConstantRingCatStalkIso (R := R) x).hom
      ((locallyConstantRingCatPresheaf X R).germ U x hx f) = f ⟨x, hx⟩) :=
  locallyConstantStalkEval_germ x U hx f

/-- The inverse stalk isomorphism sends a scalar to the germ of the global constant function. -/
@[simp]
theorem locallyConstantRingCatStalkIso_inv_apply (x : X) (r : R) :
    (locallyConstantRingCatStalkIso (R := R) x).inv r =
      (locallyConstantRingCatPresheaf X R).germ ⊤ x (by trivial) (LocallyConstant.const _ r) :=
  (rfl)

/-- Equality of germs of locally constant sections is detected by evaluation, even when the
sections are defined on different open neighborhoods. -/
@[simp]
theorem germ_locallyConstant_eq_iff (x : X) {U V : Opens X} (hxU : x ∈ U) (hxV : x ∈ V)
    (f : LocallyConstant U R) (g : LocallyConstant V R) :
    (locallyConstantRingCatPresheaf X R).germ U x hxU f =
      (locallyConstantRingCatPresheaf X R).germ V x hxV g ↔ f ⟨x, hxU⟩ = g ⟨x, hxV⟩ := by
  constructor
  · intro h
    exact (locallyConstantRingCatStalkIso_hom_germ x U hxU f).symm.trans
      ((congrArg (locallyConstantRingCatStalkIso (R := R) x).hom h).trans
        (locallyConstantRingCatStalkIso_hom_germ x V hxV g))
  · intro h
    exact (germ_locallyConstant_eq_const x U hxU f).trans
      ((congrArg (fun r : R ↦ (locallyConstantRingCatPresheaf X R).germ ⊤ x
        (by trivial) (LocallyConstant.const _ r)) h).trans
          (germ_locallyConstant_eq_const x V hxV g).symm)

namespace Sheaf

variable (F : X.Sheaf (ModuleCat.{u} R)) (x : X)

private def toLocallyConstantModuleStalkAddEquiv :
    ↑(Presheaf.stalk (X := X) F.toLocallyConstantModule.val.presheaf x) ≃+
      ↑(F.presheaf.stalk x) :=
  (preservesColimitIso (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})
    ((OpenNhds.inclusion x).op ⋙ F.presheaf)).symm.addCommGroupIsoToAddEquiv

private theorem toLocallyConstantModuleStalkAddEquiv_germ
    (U : Opens X) (hx : x ∈ U) (m : F.presheaf.obj (op U)) :
    toLocallyConstantModuleStalkAddEquiv F x
      (Presheaf.germ F.toLocallyConstantModule.val.presheaf U x hx m) =
        F.presheaf.germ U x hx m :=
  ConcreteCategory.congr_hom
    (ι_preservesColimitIso_inv (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})
      ((OpenNhds.inclusion x).op ⋙ F.presheaf) (op ⟨U, hx⟩)) m

private theorem toLocallyConstantModuleStalkAddEquiv_germ_smul
    (U : Opens X) (hx : x ∈ U) (r : LocallyConstant U R) (m : F.presheaf.obj (op U)) :
    toLocallyConstantModuleStalkAddEquiv F x
      (Presheaf.germ (X := X) (locallyConstantRingCatSheaf X R).obj U x hx r •
        Presheaf.germ F.toLocallyConstantModule.val.presheaf U x hx m) =
      r ⟨x, hx⟩ • F.presheaf.germ U x hx m :=
  (congrArg (toLocallyConstantModuleStalkAddEquiv F x)
    (F.toLocallyConstantModule.val.germ_ringCat_smul x U hx r m).symm).trans
      ((toLocallyConstantModuleStalkAddEquiv_germ F x U hx (r • m)).trans
        (germ_smul F r m x hx))

-- Specialize the inverse-pair witnesses locally, without adding global instance rules.
local instance : RingHomInvPair
    (locallyConstantRingCatStalkIso (R := R) x).ringCatIsoToRingEquiv.toRingHom
    (locallyConstantRingCatStalkIso (R := R) x).ringCatIsoToRingEquiv.symm.toRingHom :=
  RingHomInvPair.of_ringEquiv (locallyConstantRingCatStalkIso (R := R) x).ringCatIsoToRingEquiv

local instance : RingHomInvPair
    (locallyConstantRingCatStalkIso (R := R) x).ringCatIsoToRingEquiv.symm.toRingHom
    (locallyConstantRingCatStalkIso (R := R) x).ringCatIsoToRingEquiv.toRingHom :=
  RingHomInvPair.of_ringEquiv_symm
    (locallyConstantRingCatStalkIso (R := R) x).ringCatIsoToRingEquiv

/-- Passing from a sheaf of `R`-modules to a module over the locally constant ring sheaf
preserves stalks, semilinearly along evaluation of the ring stalk. -/
def toLocallyConstantModuleStalkEquiv :
    LinearEquiv (σ' :=
      (locallyConstantRingCatStalkIso (R := R) x).ringCatIsoToRingEquiv.symm.toRingHom)
      (locallyConstantRingCatStalkIso (R := R) x).ringCatIsoToRingEquiv.toRingHom
      ↑(Presheaf.stalk (X := X) F.toLocallyConstantModule.val.presheaf x)
      ↑(F.presheaf.stalk x) := by
  refine { toLocallyConstantModuleStalkAddEquiv F x with map_smul' := ?_ }
  intro r m
  obtain ⟨U, hxU, r, rfl⟩ :=
    Presheaf.exists_germ_eq (X := X) (locallyConstantRingCatSheaf X R).obj r
  obtain ⟨V, hVU, hxV, m, rfl⟩ :=
    Presheaf.exists_le_germ_eq F.toLocallyConstantModule.val.presheaf m hxU
  rw [← Presheaf.germ_res_apply (X := X) (locallyConstantRingCatSheaf X R).obj
    (homOfLE hVU) x hxV r]
  -- The ring and module adapters retain their section carriers only definitionally.
  -- Explicit section arguments let the characteristic lemmas pass through these wrappers.
  exact (toLocallyConstantModuleStalkAddEquiv_germ_smul F x V hxV
    ((locallyConstantRingCatSheaf X R).obj.map (homOfLE hVU).op r) m).trans
      (congrArg₂ (fun a b ↦ a • b)
        (locallyConstantRingCatStalkIso_hom_germ x V hxV _).symm
        (toLocallyConstantModuleStalkAddEquiv_germ F x V hxV m).symm)

/-- The adapter's semilinear stalk equivalence preserves every module germ. -/
@[simp]
theorem toLocallyConstantModuleStalkEquiv_germ
    (U : Opens X) (hx : x ∈ U) (m : F.presheaf.obj (op U)) :
    dsimp% only [PresheafOfModules.presheaf_obj_coe, RingEquiv.toRingHom_eq_coe]
    (F.toLocallyConstantModuleStalkEquiv x
      (Presheaf.germ F.toLocallyConstantModule.val.presheaf U x hx m) =
        F.presheaf.germ U x hx m) :=
  toLocallyConstantModuleStalkAddEquiv_germ F x U hx m

/-- The inverse stalk equivalence also preserves the representative of a germ. -/
@[simp]
theorem toLocallyConstantModuleStalkEquiv_symm_germ
    (U : Opens X) (hx : x ∈ U) (m : F.presheaf.obj (op U)) :
    dsimp% only [PresheafOfModules.presheaf_obj_coe, RingEquiv.toRingHom_eq_coe]
    ((F.toLocallyConstantModuleStalkEquiv x).symm (F.presheaf.germ U x hx m) =
      Presheaf.germ F.toLocallyConstantModule.val.presheaf U x hx m) :=
  (F.toLocallyConstantModuleStalkEquiv x).symm_apply_eq.mpr
    (F.toLocallyConstantModuleStalkEquiv_germ x U hx m).symm

variable {F} {G : X.Sheaf (ModuleCat.{u} R)}

/-- The module-stalk equivalence is natural in the coefficient sheaf. -/
theorem toLocallyConstantModuleStalkEquiv_naturality (α : F ⟶ G)
    (m : ↑(Presheaf.stalk (X := X) F.toLocallyConstantModule.val.presheaf x)) :
    G.toLocallyConstantModuleStalkEquiv x
        ((Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
          (Functor.whiskerRight α.hom (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})) m) =
      (Presheaf.stalkFunctor (ModuleCat.{u} R) x).map α.hom
        (F.toLocallyConstantModuleStalkEquiv x m) := by
  obtain ⟨U, hx, m, rfl⟩ := Presheaf.exists_germ_eq F.toLocallyConstantModule.val.presheaf m
  exact (congrArg (G.toLocallyConstantModuleStalkEquiv x)
    (Presheaf.stalkFunctor_map_germ_apply U x hx
      (Functor.whiskerRight α.hom (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})) m)).trans
        ((G.toLocallyConstantModuleStalkEquiv_germ x U hx (α.hom.app (op U) m)).trans
          ((Presheaf.stalkFunctor_map_germ_apply U x hx α.hom m).symm.trans
            (congrArg ((Presheaf.stalkFunctor (ModuleCat.{u} R) x).map α.hom)
              (F.toLocallyConstantModuleStalkEquiv_germ x U hx m).symm)))

end Sheaf

end TopCat
