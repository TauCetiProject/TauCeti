/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.RepresentationTheory.GaloisLattice.Dual
public import TauCeti.RepresentationTheory.Rep.Dual

/-!
# Contragredient duality of integral Galois lattices

Integral duals preserve finite freeness and continuity of the Galois action. Evaluation
into the double dual exhibits this contravariant functor as an equivalence. This is the
lattice duality relating the character and cocharacter classifications of tori.
-/

public section

open CategoryTheory

namespace TauCeti.GaloisLatticeCat

universe u

variable {k : Type u} [Field k]

/-- The integral dual of a Galois lattice, with its contragredient action. -/
noncomputable abbrev dual (M : GaloisLatticeCat k) : GaloisLatticeCat k :=
  ⟨M.obj.dual, by
    -- Normalize the stored integer module to use the continuity theorem for additive groups.
    rcases M with ⟨@⟨V, hV, hmod, ρ⟩, hM⟩
    have h : hmod = AddCommGroup.toIntModule V := Subsingleton.elim _ _
    subst hmod
    rw [galoisLatticeProperty_iff] at hM
    let _ := hM.1.1
    let _ := hM.1.2
    exact galoisLatticeProperty_dual ρ hM.2⟩

/-- The representation underlying the dual lattice is the contragredient representation. -/
@[simp]
theorem dual_obj (M : GaloisLatticeCat k) : (dual M).obj = M.obj.dual := by
  rfl

/-- Contragredient duality as a functor on integral Galois lattices. -/
@[implicit_reducible]
noncomputable def dualFunctor : (GaloisLatticeCat k)ᵒᵖ ⥤ GaloisLatticeCat k where
  obj M := dual M.unop
  map f := ObjectProperty.homMk (Rep.dualMap f.unop.hom)
  map_id M := by
    apply ObjectProperty.hom_ext
    simp
  map_comp f g := by
    apply ObjectProperty.hom_ext
    simp

/-- The representation underlying the contragredient functor. -/
@[simp]
theorem dualFunctor_obj_obj (M : (GaloisLatticeCat k)ᵒᵖ) :
    ((dualFunctor (k := k)).obj M).obj = M.unop.obj.dual := by rfl

/-- The map part of contragredient duality, in the underlying representation category. -/
@[simp]
theorem dualFunctor_map_hom {M N : (GaloisLatticeCat k)ᵒᵖ} (f : M ⟶ N) :
    ((dualFunctor (k := k)).map f).hom =
      eqToHom (dualFunctor_obj_obj _) ≫ Rep.dualMap f.unop.hom ≫
        eqToHom (dualFunctor_obj_obj _).symm := by
  rfl

/-- Evaluation identifies a Galois lattice with its double dual. -/
noncomputable def doubleDualIso (M : GaloisLatticeCat k) : M ≅
    (dualFunctor (k := k)).obj (Opposite.op ((dualFunctor (k := k)).obj (Opposite.op M))) := by
  dsimp only [dualFunctor]
  exact ObjectProperty.isoMk _ (Rep.doubleDualIso M.obj)

/-- On underlying representations, the double-dual identification is evaluation. -/
@[simp]
theorem doubleDualIso_hom_hom (M : GaloisLatticeCat k) :
    (doubleDualIso M).hom.hom = (Rep.doubleDualIso M.obj).hom ≫
      eqToHom ((dualFunctor_obj_obj _).trans
        (congrArg Rep.dual (dualFunctor_obj_obj (Opposite.op M)))).symm := by
  rfl

/-- Evaluation into the double dual is natural in the lattice. -/
@[reassoc]
theorem doubleDualIso_naturality {M N : GaloisLatticeCat k} (f : M ⟶ N) :
    f ≫ (doubleDualIso N).hom = (doubleDualIso M).hom ≫
      (dualFunctor (k := k)).map ((dualFunctor (k := k)).map f.op).op := by
  apply ObjectProperty.hom_ext
  simpa only [doubleDualIso, dualFunctor, ObjectProperty.FullSubcategory.comp_hom,
    ObjectProperty.isoMk_hom, ObjectProperty.homMk_hom, Quiver.Hom.unop_op, id_eq] using
    Rep.doubleDualIso_naturality f.hom

/-- Contragredient integral duality is an equivalence on Galois lattices. -/
private noncomputable def dualEquivalence : (GaloisLatticeCat k)ᵒᵖ ≌ GaloisLatticeCat k :=
  CategoryTheory.Equivalence.mk dualFunctor dualFunctor.rightOp
    (NatIso.ofComponents (fun M ↦ (doubleDualIso M.unop).symm.op) (fun f ↦ by
      apply Quiver.Hom.unop_inj
      dsimp
      have h := doubleDualIso_naturality f.unop
      apply (Iso.inv_comp_eq _).mpr
      simpa only [Category.assoc, Quiver.Hom.op_unop, Iso.op_inv, Quiver.Hom.unop_op] using
        (Iso.eq_comp_inv _).mpr h))
    (NatIso.ofComponents (fun M ↦ (doubleDualIso M).symm) (fun f ↦ by
      dsimp
      exact (Iso.comp_inv_eq _).mpr ((Iso.eq_inv_comp _).mpr
        (doubleDualIso_naturality f).symm)))

/-- The contragredient functor is an equivalence. -/
noncomputable instance dualFunctor_isEquivalence :
    (dualFunctor (k := k)).IsEquivalence :=
  (dualEquivalence (k := k)).isEquivalence_functor

end TauCeti.GaloisLatticeCat
