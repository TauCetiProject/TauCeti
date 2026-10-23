/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.AuslanderReiten.DoubleTranspose.Minimal
public import TauCeti.Algebra.Module.MinimalProjectivePresentation.Finite
public import TauCeti.Algebra.Category.ModuleCat.ScalarDual
import TauCeti.Algebra.Module.AuslanderReiten.Inverse
import TauCeti.Algebra.Category.ModuleCat.Projective.Stable
import TauCeti.Algebra.Category.ModuleCat.ProjectiveStable.Reflection
import Mathlib.Algebra.Category.ModuleCat.Injective
import Mathlib.RingTheory.HopkinsLevitzki

/-!
# Surjectivity of the Auslander–Reiten translate

Every finite-dimensional non-injective indecomposable module over a finite-dimensional
algebra is the Auslander–Reiten translate of a finite-dimensional non-projective
indecomposable. The preimage is the right transpose of a minimal presentation of the
scalar dual. A minimal presentation of this preimage then computes its translate.

The result concerns actual modules, rather than objects modulo injectives or projectives.
It supplies the surjectivity half of the correspondence on indecomposable isomorphism
classes. The field is arbitrary and the algebra may be noncommutative.

## References

* M. Auslander, I. Reiten, S. O. Smalø, *Representation Theory of Artin Algebras*,
  Cambridge University Press (1995), Section IV.1.
-/

public section

namespace ModuleCat

open CategoryTheory TauCeti

universe u v w

attribute [local instance] moduleOfAlgebraModule isScalarTower_of_algebra_moduleCat

variable {k : Type u} {A : Type v} [Field k] [Ring A] [Algebra k A]
  [FiniteDimensional k A]

/-- Every finite-dimensional non-injective indecomposable is `D Tr` of a finite minimal
presentation of a finite-dimensional non-projective indecomposable. -/
theorem exists_auslanderReitenTranslate (M : ModuleCat.{max u v w} A)
    [Module.Finite k M] (hiM : Indecomposable M) (hinj : ¬ Injective M) :
    ∃ (L : ModuleCat.{max u v w} A) (_ : Module.Finite k L),
      Indecomposable L ∧ ¬ Projective L ∧
      ∃ (P : FiniteProjectivePresentation L), IsMinimalProjectivePresentation P.p P.π ∧
        Nonempty (AuslanderReitenTranslate k P.p ≃ₗ[A] M) := by
  let : IsArtinianRing A := IsArtinianRing.of_finite k A
  let : IsArtinianRing Aᵐᵒᵖ := IsArtinianRing.of_finite k Aᵐᵒᵖ
  let N := rightScalarDual k M
  have : Module.Finite Aᵐᵒᵖ N := Module.Finite.of_restrictScalars_finite k Aᵐᵒᵖ N
  obtain ⟨Q, hQ⟩ := FiniteProjectivePresentation.exists_isMinimal (M := N)
  let e := rightScalarDualEvalEquiv k M
  have he := rightScalarDualEvalEquiv_smul k M
  have hiM' := (indecomposable_iff_isIndecomposableModule M).mp hiM
  have hinj' : ¬ Module.Injective A M := fun h ↦
    hinj ((Module.injective_iff_injective_object A M).mp h)
  have hiL := (Q.isIndecomposableModule_rightTranspose_iff_not_injective hQ e he hiM').mpr
    hinj'
  have hpL : ¬ Module.Projective A Q.rightTranspose := fun h ↦
    hinj' ((Q.projective_rightTranspose_iff_injective hQ e he).mp h)
  -- The bundled transpose uses restriction of scalars, rather than the quotient's
  -- independently inferred scalar action.
  let : SMul k Q.rightTranspose := (moduleOfAlgebraModule (k := k) Q.rightTranspose).toSMul
  let : Module k Q.rightTranspose := moduleOfAlgebraModule (k := k) Q.rightTranspose
  let : IsScalarTower k A Q.rightTranspose :=
    isScalarTower_of_algebra_moduleCat (k := k) Q.rightTranspose
  have hL : Module.Finite k Q.rightTranspose := Module.Finite.trans A _
  obtain ⟨P, hP⟩ := FiniteProjectivePresentation.exists_isMinimal (M := Q.rightTranspose)
  have : Module.Finite k (AuslanderReitenTranspose P.p) := Module.Finite.trans Aᵐᵒᵖ _
  have hN : IsFiniteLength Aᵐᵒᵖ N :=
    isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨inferInstance, inferInstance⟩
  have hTr : IsFiniteLength Aᵐᵒᵖ (AuslanderReitenTranspose P.p) :=
    isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨inferInstance, inferInstance⟩
  have hiN := (indecomposable_iff_isIndecomposableModule N).mpr
    ((e.isIndecomposableModule_iff_of_dual he).mp hiM')
  have hpN : ¬ Projective N := fun h ↦ hinj'
    ((e.moduleInjective_iff_projective_of_dual he).mpr
      ((IsProjective.iff_projective (R := Aᵐᵒᵖ) N).mpr h))
  have hstable := (indecomposable_projectiveStableFunctor_obj_iff N hN hiN).mpr hpN
  exact ⟨Q.rightTranspose, hL,
    (indecomposable_iff_isIndecomposableModule _).mpr hiL,
    fun h ↦ hpL ((IsProjective.iff_projective (R := A) Q.rightTranspose).mpr h),
    P, hP,
    (Q.nonempty_linearEquiv_translate_rightTranspose_iff_isZero_projective_retract.{v, max u w}
      P hP.isSuperfluous_ker hN hTr e he).mpr
        ((indecomposable_iff_isZero_projective_retract N hstable).mp hiN)⟩

end ModuleCat
