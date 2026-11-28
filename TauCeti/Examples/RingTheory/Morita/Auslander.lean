/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import TauCeti.Algebra.Homology.Ext.DualNumbers
import Mathlib.LinearAlgebra.Basis.Prod
import TauCeti.Algebra.Category.ModuleCat.SpanSingleton
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

/-- The four blocks of an endomorphism of `B ⊕ S`, in row order. The diagonal blocks and the
lower left block are evaluated at the corresponding cyclic generators. In the upper right block
we take the coefficient of `ε`. -/
noncomputable def endDualNumberBiprodResidueEquiv :
    End (P ⊞ S) ≃ₗ[k] (B × k) × (k × k) := by
  let regularEval := (ModuleCat.homSelfLinearEquiv k P).toAddEquiv
  have regularEval_apply (g : P ⟶ P) : regularEval g = g.hom 1 :=
    ModuleCat.homSelfLinearEquiv_apply g
  let residueToFree := (homDualNumberResidueToFreeEquiv k).toAddEquiv
  letI (X Y : ModuleCat B) : Module k (X ⟶ Y) := Linear.homModule X Y
  -- The categorical action on maps into the regular module uses multiplication by the base
  -- scalar, whereas the output coordinates use the componentwise action.
  let topLinear : ((P ⟶ P) × (S ⟶ P)) ≃ₗ[k] (B × k) :=
    { toAddEquiv := regularEval.prodCongr residueToFree
      map_smul' := fun c f ↦ by
        apply Prod.ext
        · change regularEval _ = c • regularEval f.1
          rw [regularEval_apply, regularEval_apply]
          exact (Algebra.smul_def c (f.1.hom 1 : B)).symm
        · change (algebraMap k B c * (f.2.hom s₁ : B)).snd = c * (f.2.hom s₁ : B).snd
          rw [← Algebra.smul_def]
          rfl }
  exact End.linearEquiv ≪≫ₗ homToBiprodLinearEquiv k (P ⊞ S) P S ≪≫ₗ
    (homBiprodLinearEquiv k P P S).prodCongr (homBiprodLinearEquiv k S P S) ≪≫ₗ
    topLinear.prodCongr ((homDualNumberFreeEquiv k).prodCongr (homDualNumberResidueEquiv k))

/-- The entries are the values of the four block maps at their cyclic generators. -/
@[simp]
theorem endDualNumberBiprodResidueEquiv_apply (f : End (P ⊞ S)) :
    endDualNumberBiprodResidueEquiv k f =
      ((((biprod.inl ≫ f.asHom ≫ biprod.fst : P ⟶ P).hom 1 : B),
          ((biprod.inr ≫ f.asHom ≫ biprod.fst : S ⟶ P).hom s₁ : B).snd),
        (dualNumberResidueEquiv k ((biprod.inl ≫ f.asHom ≫ biprod.snd : P ⟶ S).hom 1),
          dualNumberResidueEquiv k ((biprod.inr ≫ f.asHom ≫ biprod.snd : S ⟶ S).hom s₁))) := by
  simp only [endDualNumberBiprodResidueEquiv, LinearEquiv.trans_apply, End.linearEquiv_apply,
    homToBiprodLinearEquiv_apply, homBiprodLinearEquiv_apply, LinearEquiv.prodCongr_apply,
    homDualNumberFreeEquiv_apply, homDualNumberResidueEquiv_apply]
  exact Prod.ext (Prod.ext (ModuleCat.homSelfLinearEquiv_apply _)
    (homDualNumberResidueToFreeEquiv_apply k _)) rfl

/-- The endomorphism algebra of the sum of the dual numbers and their residue module has
rank five over any nontrivial commutative base ring. -/
theorem finrank_end_dualNumber_biprod_residue [Nontrivial k] :
    Module.finrank k (End (P ⊞ S)) = 5 := by
  let b := Module.Basis.singleton Unit k
  rw [(endDualNumberBiprodResidueEquiv k).finrank_eq,
    Module.finrank_eq_card_basis (((dualNumberBasis k).prod b).prod (b.prod b))]
  simp

end TauCeti
