/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.AuslanderReiten.Translate
public import TauCeti.Algebra.Category.ModuleCat.AuslanderReiten.TransposeExt
import TauCeti.RingTheory.MatlisDuality.Semilocal

/-!
# Computing the inverse Auslander–Reiten translate by Ext¹

For a finitely generated left module `M` over a finite-dimensional algebra `A`, if the right
module `D M` has projective dimension at most one, then `τ⁻ M` is `Ext¹_A(D A, M)`. The action
of `a ∈ A` on this Ext group is pullback along the dual of left multiplication by `a` on the
right regular module. Over a right hereditary algebra the projective dimension bound is
automatic.

This is the Ext description used in Grant, *The Nakayama automorphism of a self-injective
preprojective algebra*, https://arxiv.org/abs/1906.11817, Proposition 2.5.
-/

public section

namespace ModuleCat

open CategoryTheory CategoryTheory.Abelian TauCeti
open scoped ModuleCat.Algebra

universe u v

attribute [local instance] moduleOfAlgebra isScalarTower_moduleOfAlgebra

variable (k : Type u) [Field k] {A : Type (max u v)} [Ring A] [Algebra k A]
  [FiniteDimensional k A]

/-- If the right dual of `M` has projective dimension at most one, the inverse Auslander–Reiten
translate is linearly equivalent to `Ext¹_A(D A, M)`, with the left `A`-action carried to
pullback along dualized left multiplications. -/
theorem exists_arInverseTranslateEquivExt (M : ModuleCat.{max u v} A) [Module.Finite A M]
    [HasProjectiveDimensionLE (matlisDualObj k k M) 1] :
    ∃ e : arInverseTranslate k k M ≃ₗ[k] Ext (matlisDualOpObj k k (of Aᵐᵒᵖ A)) M 1,
      ∀ (a : A) (x : arInverseTranslate k k M),
        e (a • x) =
          (Ext.mk₀ (matlisDualOpMap k k (ofHom (LinearMap.mulLeft Aᵐᵒᵖ a)))).comp
            (e x) (zero_add 1) := by
  let N := of Aᵐᵒᵖ (MatlisDual k k M)
  let eN : matlisDualObj k k M ≅ N := (matlisDualObjEquiv k k M).toModuleIso
  have hN : HasProjectiveDimensionLE N 1 := hasProjectiveDimensionLT_of_iso eN 2
  have : Module.Finite k M := Module.Finite.trans A M
  have : Module.Finite Aᵐᵒᵖ (MatlisDual k k M) := Module.Finite.of_restrictScalars_finite k _ _
  have : IsArtinianRing Aᵐᵒᵖ := IsArtinianRing.of_finite k Aᵐᵒᵖ
  have : Module.FinitePresentation Aᵐᵒᵖ N := Module.finitePresentation_of_finite Aᵐᵒᵖ _
  obtain ⟨P, hP⟩ := FiniteProjectivePresentation.exists_isMinimal (M := N)
  have hp := P.injective_p_of_hasProjectiveDimensionLE_one hP hN
  obtain ⟨eP⟩ := nonempty_iso_arInverseTranslate k k M P hP
  let eDD : M ≅ matlisDualOpObj k k N :=
    matlisDualEvalIso (length_quotient_linearMap_self_eq_one k) M
      (isFiniteLength_of_finite k M) ≪≫ (matlisDualOp k k).mapIso eN.symm.op
  let eExt := extLinearEquivOfIso k (Iso.refl (matlisDualOpObj k k (of Aᵐᵒᵖ A))) eDD.symm 1
  refine ⟨(eP.toLinearEquiv.restrictScalars k).trans
    ((P.rightTransposeEquivExtDual.{u, v} k hp).trans eExt), fun a x ↦ ?_⟩
  simp only [LinearEquiv.trans_apply, LinearEquiv.restrictScalars_apply, map_smul, eExt,
    extLinearEquivOfIso_apply, Iso.refl_inv, Ext.mk₀_id_comp]
  rw [P.rightTransposeEquivExtDual_smul.{u, v} k hp, Ext.comp_assoc_of_third_deg_zero]

end ModuleCat
