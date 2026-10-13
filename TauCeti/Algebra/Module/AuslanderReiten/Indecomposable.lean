/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.AuslanderReiten.Full
public import TauCeti.Algebra.Module.AuslanderReiten.Faithful
public import TauCeti.Algebra.Module.AuslanderReiten.ProjectiveSummand
public import TauCeti.Algebra.Category.ModuleCat.Projective.Stable
public import TauCeti.Algebra.Category.ModuleCat.ProjectiveStable.Reflection

import Mathlib.RingTheory.LocalRing.RingHom.Basic

/-!
# Indecomposability of minimal transposes

The transpose of a finite minimal projective presentation of a finite-length indecomposable
module is indecomposable exactly when the original module is not projective. For arbitrary
finite projective presentations, the corresponding assertion holds in the projective stable
category. Minimality excludes the projective retracts that this category forgets, so the
conclusion then holds for actual modules.

Together with `TauCeti.AuslanderReitenTranslate.isIndecomposableModule_iff`, the transpose
characterization gives the corresponding result for the Auslander–Reiten translate when
the transpose is reflexive over the base. In particular, this applies to finite-dimensional
modules over finite-dimensional algebras over a field, and supplies the preservation of
indecomposability needed to classify modules by their translates.

## References

* M. Auslander, I. Reiten, S. O. Smalø, *Representation Theory of Artin Algebras*,
  Cambridge University Press (1995), Section IV.1.
-/

public section

namespace TauCeti.FiniteProjectivePresentation

open CategoryTheory CategoryTheory.Limits

universe u v

variable {A : Type u} [Ring A] {M : ModuleCat.{v} A} [Small.{v} A]

local notation "S" =>
  ExactStructure.projectiveStableFunctor (ExactStructure.abelian (ModuleCat A))
local notation "T" =>
  ExactStructure.projectiveStableFunctor (ExactStructure.abelian (ModuleCat Aᵐᵒᵖ))

/-- The stable transpose of a finite projective presentation of a finite-length
indecomposable module is indecomposable exactly when the module is not projective.
Minimality is not needed. -/
@[simp]
theorem indecomposable_stableTransposeObj_iff (P : FiniteProjectivePresentation M)
    (hM : IsFiniteLength A M) (hiM : IsIndecomposableModule A M) :
    Indecomposable ((T).obj (ModuleCat.of Aᵐᵒᵖ (AuslanderReitenTranspose P.p))) ↔
      ¬ Module.Projective A M := by
  constructor
  · intro h hproj
    let := hproj
    have hs : IsZero ((S).obj M) :=
      (ExactStructure.isZero_projectiveStableFunctor_obj_iff _ M).mpr
        ((ExactStructure.abelian_isProjective_iff M).mpr inferInstance)
    apply h.1
    apply (IsZero.iff_id_eq_zero _).mpr
    rw [← AuslanderReitenTranspose.stableMap_id P.exact P.surjective,
      (IsZero.iff_id_eq_zero _).mp hs]
    exact (AuslanderReitenTranspose.stableMap P.exact.linearMap_comp_eq_zero
      P.exact P.surjective).map_zero
  · intro hpM
    have hi : Indecomposable M := (indecomposable_iff_isIndecomposableModule M).mpr hiM
    have hs := (ModuleCat.indecomposable_projectiveStableFunctor_obj_iff M hM hi).mpr
      (fun h ↦ by let := h; exact hpM inferInstance)
    have : IsLocalRing (End M) := (indecomposable_iff_isLocalRing_end M hM).mp hi
    have : Nontrivial (End ((S).obj M)) :=
      nontrivial_of_ne (𝟙 ((S).obj M)) 0
        (fun h ↦ hs.1 ((IsZero.iff_id_eq_zero _).mpr h))
    have : IsLocalRing (End ((S).obj M)) := IsLocalRing.of_surjective'
      ({ (S).mapEnd M, (S).mapAddHom with } : End M →+* End ((S).obj M))
      (S).map_surjective
    let X := (T).obj (ModuleCat.of Aᵐᵒᵖ (AuslanderReitenTranspose P.p))
    let f := AuslanderReitenTranspose.stableMap P.exact.linearMap_comp_eq_zero
      P.exact P.surjective
    -- Transposition reverses composition; the opposite ring accounts for that reversal.
    let φ : (End ((S).obj M))ᵐᵒᵖ →+* End X :=
      { toFun := fun a ↦ f a.unop
        map_zero' := f.map_zero
        map_one' := AuslanderReitenTranspose.stableMap_id P.exact P.surjective
        map_add' := fun a b ↦ f.map_add a.unop b.unop
        map_mul' := fun a b ↦ AuslanderReitenTranspose.stableMap_comp
          P.exact.linearMap_comp_eq_zero P.exact P.surjective P.exact P.surjective
          a.unop b.unop }
    let e : (End ((S).obj M))ᵐᵒᵖ ≃+* End X := RingEquiv.ofBijective φ
      ⟨(AuslanderReitenTranspose.stableMap_injective
          P.exact P.surjective P.exact P.surjective).comp MulOpposite.unop_injective,
        (AuslanderReitenTranspose.stableMap_surjective
          P.exact P.surjective P.exact P.surjective).comp MulOpposite.unop_surjective⟩
    have : IsLocalRing (End X) := e.isLocalRing
    exact indecomposable_of_injective_of_isLocalRing (R := End X)
      (fun h ↦ one_ne_zero (α := End X) ((IsZero.iff_id_eq_zero _).mp h)) id
      Function.injective_id rfl rfl (fun _ ↦ rfl)

/-- The transpose of a finite minimal presentation of a finite-length indecomposable module
is indecomposable exactly when the original module is not projective. -/
@[simp]
theorem isIndecomposableModule_auslanderReitenTranspose_iff
    (P : FiniteProjectivePresentation M) (hP : IsMinimalProjectivePresentation P.p P.π)
    (hM : IsFiniteLength A M) (hiM : IsIndecomposableModule A M) :
    IsIndecomposableModule Aᵐᵒᵖ (AuslanderReitenTranspose P.p) ↔
      ¬ Module.Projective A M := by
  constructor
  · intro h hproj
    let := hproj
    let := hP.subsingleton_auslanderReitenTranspose_of_projective
    exact not_nontrivial _
      (isIndecomposableModule_iff_nontrivial_and_forall_isIdempotentElem.mp h).1
  · intro hpM
    apply (indecomposable_iff_isIndecomposableModule
      (ModuleCat.of Aᵐᵒᵖ (AuslanderReitenTranspose P.p))).mp
    apply (ModuleCat.indecomposable_iff_isZero_projective_retract _
      ((P.indecomposable_stableTransposeObj_iff hM hiM).mpr hpM)).mpr
    intro Q r hQ
    let := hQ
    exact hP.isSuperfluous_ker.isZero_of_retract_auslanderReitenTranspose r

end TauCeti.FiniteProjectivePresentation
