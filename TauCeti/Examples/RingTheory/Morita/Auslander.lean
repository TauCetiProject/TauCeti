/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import TauCeti.Algebra.Homology.Ext.DualNumbers
import Mathlib.LinearAlgebra.Basis.Prod
import TauCeti.CategoryTheory.Linear.Biproduct

/-!
# The endomorphism algebra of the dual numbers and their residue module

Let `B = k[ε]` be the dual numbers over a commutative ring `k` and `S = B/(ε)`. An endomorphism of
`B ⊕ S` has four blocks. Evaluation at the two cyclic generators identifies the diagonal blocks
with `B` and `k` and each off-diagonal block with `k`. The block from `S` to `B` takes values in
`ε B`, so its coordinate is the coefficient of `ε`. Over a field this gives dimension five for
the endomorphism algebra in the dual-number example of the Auslander correspondence.

## References

* A. Hochenegger, M. Kalck, D. Ploog, *Spherical subcategories in representation theory*,
  arXiv:1502.06838v4, Section 3.1, for the two-vertex presentation of this Auslander algebra.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits TrivSqZeroExt
open scoped ModuleCat.Algebra

variable (k : Type*) [CommRing k]

local notation "B" => DualNumber k
local notation "P" => dualNumberFree k
local notation "S" => dualNumberResidue k
local notation "s₁" => ModuleCat.Hom.hom (dualNumberProj k) (1 : DualNumber k)

private noncomputable def dualNumberFreeEndEquiv : (P ⟶ P) ≃ₗ[k] B where
  toAddEquiv := ModuleCat.homAddEquiv.trans (LinearMap.ringLmapEquivSelf B B B).toAddEquiv
  map_smul' _ _ := rfl

private theorem fst_homDualNumberResidue_eq_zero (f : S →ₗ[B] B) (x : S) :
    (f x).fst = 0 := by
  have h : DualNumber.eps * f x = 0 := by
    rw [← smul_eq_mul, ← map_smul, eps_smul_dualNumberResidue, map_zero]
  simpa using congrArg TrivSqZeroExt.snd h

/-- The upper right block is read off from the coefficient of `ε` in the image of the
residue class of `1`. -/
private noncomputable def homDualNumberResidueToFreeEquiv : (S ⟶ P) ≃ₗ[k] k :=
  LinearEquiv.ofBijective
    { toFun := fun f ↦ (f.hom s₁ : B).snd
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl } <| by
    constructor
    · intro f g hfg
      apply (cancel_epi (dualNumberProj k)).1
      apply (dualNumberFreeEndEquiv k).injective
      exact TrivSqZeroExt.ext
        ((fst_homDualNumberResidue_eq_zero k f.hom s₁).trans
          (fst_homDualNumberResidue_eq_zero k g.hom s₁).symm) hfg
    · intro c
      let g : S →ₗ[B] B := {
        toFun := fun x ↦ inr (c * dualNumberResidueEquiv k x)
        map_add' := fun x y ↦ by rw [map_add, mul_add, inr_add]
        map_smul' := fun a x ↦ by
          rw [dualNumberResidueEquiv_smul, smul_eq_mul]
          ext <;> simp [TrivSqZeroExt.snd_mul]
          ac_rfl
      }
      refine ⟨ModuleCat.ofHom (X := S) (Y := P) g, ?_⟩
      have hone : dualNumberResidueEquiv k s₁ = 1 :=
        (dualNumberResidueEquiv_apply k s₁).trans <|
          Eq.trans (dualNumberProj_apply k (1 : B)) (fst_one (R := k))
      -- Evaluation followed by `snd` extracts the coefficient used to construct the map.
      change c * dualNumberResidueEquiv k s₁ = c
      rw [hone, mul_one]

/-- The four constituent morphisms of an endomorphism of the regular and residue biproduct. -/
private noncomputable def endDualNumberBiprodBlocks :
    End (P ⊞ S) ≃+ ((P ⟶ P) × (S ⟶ P)) × ((P ⟶ S) × (S ⟶ S)) :=
  -- The biproduct equivalences use the categorical module structure on morphisms.
  letI (X Y : ModuleCat B) : Module k (X ⟶ Y) := Linear.homModule X Y
  End.addEquiv.trans <| (homToBiprodLinearEquiv k (P ⊞ S) P S).toAddEquiv.trans <|
    (homBiprodLinearEquiv k P P S).toAddEquiv.prodCongr (homBiprodLinearEquiv k S P S).toAddEquiv

private theorem endDualNumberBiprodBlocks_apply (f : End (P ⊞ S)) :
    endDualNumberBiprodBlocks k f =
      ((biprod.inl ≫ f.asHom ≫ biprod.fst, biprod.inr ≫ f.asHom ≫ biprod.fst),
        (biprod.inl ≫ f.asHom ≫ biprod.snd, biprod.inr ≫ f.asHom ≫ biprod.snd)) := by
  simp [endDualNumberBiprodBlocks, AddEquiv.prodCongr, Equiv.prodCongr_apply,
    homToBiprodLinearEquiv_apply, homBiprodLinearEquiv_apply]

/-- The four blocks of an endomorphism of `B ⊕ S`, in row order. The diagonal blocks and the
lower left block are evaluated at the corresponding cyclic generators. In the upper right block
we take the coefficient of `ε`. -/
noncomputable def endDualNumberBiprodResidueEquiv :
    End (P ⊞ S) ≃ₗ[k] (B × k) × (k × k) :=
  LinearEquiv.ofBijective
    { toFun := fun f ↦
        (((dualNumberFreeEndEquiv k) (biprod.inl ≫ f.asHom ≫ biprod.fst),
          (homDualNumberResidueToFreeEquiv k) (biprod.inr ≫ f.asHom ≫ biprod.fst)),
        ((homDualNumberFreeEquiv k) (biprod.inl ≫ f.asHom ≫ biprod.snd),
          (homDualNumberResidueEquiv k) (biprod.inr ≫ f.asHom ≫ biprod.snd)))
      map_add' := fun f g ↦ by
        simp [Preadditive.add_comp, Preadditive.comp_add]
        rfl
      map_smul' := fun c f ↦ by
        simp only [End.smul_asHom, Linear.smul_comp, Linear.comp_smul, map_smul,
          homDualNumberFreeEquiv_apply, ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply,
          dualNumberResidueEquiv_apply, homDualNumberResidueEquiv_apply, RingHom.id_apply,
          Prod.smul_mk, smul_eq_mul, Prod.mk.injEq]
        refine ⟨⟨?_, ?_⟩, rfl⟩
        · let z : B := (biprod.inl ≫ f.asHom ≫ biprod.fst : P ⟶ P).hom 1
          -- The categorical scalar action on the regular module is multiplication by
          -- the image of the base scalar.
          change algebraMap k B c * z = c • z
          exact (Algebra.smul_def c z).symm
        · let z : B := (biprod.inr ≫ f.asHom ≫ biprod.fst : S ⟶ P).hom s₁
          -- The same action on the upper right block is read in the `ε` coefficient.
          change (algebraMap k B c * z).snd = c * z.snd
          rw [← Algebra.smul_def]
          rfl } <| by
    let e := ((dualNumberFreeEndEquiv k).toAddEquiv.prodCongr
      (homDualNumberResidueToFreeEquiv k).toAddEquiv).prodCongr
      ((homDualNumberFreeEquiv k).toAddEquiv.prodCongr (homDualNumberResidueEquiv k).toAddEquiv)
    convert e.bijective.comp (endDualNumberBiprodBlocks k).bijective using 1
    funext f
    simp only [LinearMap.coe_mk, AddHom.coe_mk, Function.comp_apply,
      endDualNumberBiprodBlocks_apply]
    rfl

/-- The entries are the values of the four block maps at their cyclic generators. -/
@[simp]
theorem endDualNumberBiprodResidueEquiv_apply (f : End (P ⊞ S)) :
    endDualNumberBiprodResidueEquiv k f =
      ((((biprod.inl ≫ f.asHom ≫ biprod.fst : P ⟶ P).hom 1 : B),
          ((biprod.inr ≫ f.asHom ≫ biprod.fst : S ⟶ P).hom s₁ : B).snd),
        (dualNumberResidueEquiv k ((biprod.inl ≫ f.asHom ≫ biprod.snd : P ⟶ S).hom 1),
          dualNumberResidueEquiv k ((biprod.inr ≫ f.asHom ≫ biprod.snd : S ⟶ S).hom s₁))) := by
  simp only [endDualNumberBiprodResidueEquiv, LinearEquiv.ofBijective_apply,
    LinearMap.coe_mk, AddHom.coe_mk, homDualNumberFreeEquiv_apply, homDualNumberResidueEquiv_apply]
  rfl

/-- The endomorphism algebra of the sum of the dual numbers and their residue module has
rank five over any nontrivial commutative base ring. -/
theorem finrank_end_dualNumber_biprod_residue [Nontrivial k] :
    Module.finrank k (End (P ⊞ S)) = 5 := by
  let b := Module.Basis.singleton Unit k
  rw [(endDualNumberBiprodResidueEquiv k).finrank_eq,
    Module.finrank_eq_card_basis (((dualNumberBasis k).prod b).prod (b.prod b))]
  simp

end TauCeti
