/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.AuslanderReiten.Translate
public import TauCeti.Algebra.Category.ModuleCat.AuslanderReiten.DualTransposeExt
public import TauCeti.Algebra.Category.ModuleCat.Projective.Presentation.Dimension

/-!
# Computing the inverse Auslander–Reiten translate by Ext¹

For a finitely generated left module `M` over an Artin algebra `A`, if the right
module `D M` has projective dimension at most one, then `τ⁻ M` is `Ext¹_A(D A, M)`. The action
of `a ∈ A` on this Ext group is pullback along the dual of left multiplication by `a` on the
right regular module. Over a right hereditary algebra the projective dimension bound is
automatic.

The computation starts from `ModuleCat.nonempty_iso_arInverseTranslate` and uses the
dual Ext comparison and `ModuleCat.matlisDualEvalIso`.

This is the Ext description used in Grant, *The Nakayama automorphism of a self-injective
preprojective algebra*, https://arxiv.org/abs/1906.11817, Proposition 2.5.
-/

public section

namespace ModuleCat

open CategoryTheory CategoryTheory.Abelian TauCeti
open scoped ModuleCat.Algebra

universe u w

attribute [local instance] moduleOfAlgebra isScalarTower_moduleOfAlgebra

variable (R : Type w) [CommRing R] [IsArtinianRing R] (E : Type w)
  [AddCommGroup E] [Module R E] [Module.Finite R E] [Module.Injective R E]
  {A : Type (max u w)} [Ring A] [Algebra R A] [Module.Finite R A]

/-- If the right dual of `M` has projective dimension at most one, the inverse Auslander–Reiten
translate is `A`-linearly equivalent to `Ext¹_A(D A, M)` with the action by pullback
along dualized left multiplications. -/
theorem exists_arInverseTranslateEquivExt (M : ModuleCat.{max u w} A) [Module.Finite A M]
    [HasProjectiveDimensionLE (matlisDualObj R E M) 1]
    (hE : ∀ 𝔪 : Ideal R, 𝔪.IsMaximal → Module.length R (R ⧸ 𝔪 →ₗ[R] E) = 1) :
    Nonempty (arInverseTranslate R E M ≃ₗ[A] ExtFromMatlisDualRegular.{u, w, w} R E M 1) := by
  let N := of Aᵐᵒᵖ (MatlisDual R E M)
  let eN : matlisDualObj R E M ≅ N := (matlisDualObjEquiv R E M).toModuleIso
  have hN : HasProjectiveDimensionLE N 1 := hasProjectiveDimensionLT_of_iso eN 2
  have : Module.Finite R M := Module.Finite.trans A M
  have : Module.Finite Aᵐᵒᵖ (MatlisDual R E M) := Module.Finite.of_restrictScalars_finite R _ _
  have : IsArtinianRing Aᵐᵒᵖ := IsArtinianRing.of_finite R Aᵐᵒᵖ
  have : Module.FinitePresentation Aᵐᵒᵖ N := Module.finitePresentation_of_finite Aᵐᵒᵖ _
  obtain ⟨P, hP⟩ := FiniteProjectivePresentation.exists_isMinimal (M := N)
  have hp := P.p_injective_of_hasProjectiveDimensionLE_one hP hN
  obtain ⟨eP⟩ := nonempty_iso_arInverseTranslate R E M P hP
  let B : ModuleCat.{max u w} Aᵐᵒᵖ := of Aᵐᵒᵖ A
  have hB : @IsFiniteLength R _ B _ (moduleOfAlgebra R B) := by
    have hscalar : moduleOfAlgebra R B = (inferInstance : Module R A) :=
      Module.ext' _ _ fun c x ↦ (Algebra.commutes c x).symm.trans (Algebra.smul_def c x).symm
    rw [hscalar]
    exact isFiniteLength_of_finite R A
  let eDD : M ≅ matlisDualOpObj R E N :=
    matlisDualEvalIso hE M (isFiniteLength_of_finite_trans R A M) ≪≫
      (matlisDualOp R E).mapIso eN.symm.op
  let e := ExtFromMatlisDualRegular.linearEquivOfIso R E eDD.symm 1
  exact ⟨eP.toLinearEquiv.trans
    ((P.rightTransposeLinearEquivExtDual.{u, w, w} R E hE hB hp).trans e)⟩

end ModuleCat
