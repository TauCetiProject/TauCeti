/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.FGModuleCat.Generator.Basic
public import TauCeti.Algebra.Category.FGModuleCat.KrullSchmidt
public import TauCeti.Algebra.Category.FGModuleCat.MatlisDuality
public import TauCeti.Algebra.Category.FGModuleCat.Projective
public import TauCeti.CategoryTheory.Preadditive.AdditiveClosure.Duality
public import TauCeti.CategoryTheory.Preadditive.KrullSchmidt.AdditiveClosure

import TauCeti.Algebra.Module.Injective.Envelope.Existence
import TauCeti.RingTheory.Artinian.Subalgebra

/-!
# Generator-cogenerators of `mod A` for an Artin algebra

Let `R` be a commutative Artinian ring and `A` an Artin `R`-algebra. A finitely generated module
`M` is a **generator-cogenerator** of `mod A = FGModuleCat A` (`TauCeti.IsGeneratorCogenerator`: a
separator and a coseparator) exactly when both the regular module `A` and its dual `D A` lie in the
additive closure `add M`, and exactly when every indecomposable projective and every
indecomposable injective object of `mod A` is a direct summand of `M`
(`TauCeti.isGeneratorCogenerator_iff_forall_indecomposable`). The base ring `R` may live in any
universe; the statements about `D A` ask that it be small in the universe of `A` and its modules,
which can always be arranged by replacing `R` with the centre of `A`, a commutative Artinian ring
over which `A` is again an Artin algebra.

The generator half holds over any ring (`FGModuleCat.isSeparator_iff_additiveClosure`). The
cogenerator half is its dual: the Matlis duality `(mod A)ᵒᵖ ≌ mod Aᵐᵒᵖ`
(`TauCeti.IsInjectiveEnvelope.fgModuleCatMatlisDuality`) turns coseparators of `mod A` into
separators of `mod Aᵐᵒᵖ`, and the regular right module into `D A`
(`TauCeti.IsInjectiveEnvelope.fgModuleCatMatlisDualRegular`); additive closures correspond under
the duality (`CategoryTheory.Equivalence.additiveClosure_functor_obj_op_iff`). So `M` is a
coseparator exactly when `D A ∈ add M`
(`TauCeti.IsInjectiveEnvelope.isCoseparator_iff_additiveClosure`), with no separate injective
argument. The descriptions through indecomposable objects then follow from the
Krull-Schmidt property of `mod A`, with `FGModuleCat.additiveClosure_regular_of_projective` and
`FGModuleCat.indecomposable_obj_iff`.

The two halves are not symmetric outside the categorical statements. Over every ring the regular
module is a finitely generated projective generator, so separators of `mod R` have the elementwise
description `Module.IsGenerator` (`FGModuleCat.isSeparator_iff_isGenerator`). There is no
cogenerator analogue of this form: a cogenerator of the category of all `R`-modules embeds every
module into a possibly infinite product of copies of itself, and need not be finitely generated,
while `mod R` may have no coseparator at all (`mod ℤ` has none). A finitely generated cogenerator,
`D A`, comes from the duality, which is why the cogenerator results here are stated for Artin
algebras.

The Artin hypothesis is needed for the indecomposable description. Over `ℤ`, the regular module is
not a coseparator of `mod ℤ`, since every morphism `ℤ/2ℤ ⟶ ℤ` is zero
(`FGModuleCat.not_isCoseparator_int`). Yet `mod ℤ` has no nonzero injective object: a nonzero
finitely generated abelian group has a direct summand `ℤ` or `ℤ/pᵏℤ` with `k ≥ 1`, and the
monomorphisms `2 : ℤ ⟶ ℤ` and `ℤ/pᵏℤ ⟶ ℤ/p²ᵏℤ` do not split. So every indecomposable projective
and every indecomposable injective object of `mod ℤ` is a direct summand of `ℤ`, which is not a
generator-cogenerator. (This last part is a remark and is not formalized here.)

## Main definitions

* `TauCeti.IsInjectiveEnvelope.fgModuleCatMatlisDualRegular`: the Matlis dual `D A` of the right
  regular module, a finitely generated left `A`-module.
* `TauCeti.IsInjectiveEnvelope.fgModuleCatMatlisDualRegularEquiv`: the underlying module of `D A`
  is the Matlis dual `Hom_R(A, E)` of the right regular module.
* `TauCeti.IsInjectiveEnvelope.fgModuleCatMatlisDualObjFgModuleCatMatlisDualRegularIso`: the Matlis
  dual of `D A` is the right regular module, by evaluation.

## Main results

* `FGModuleCat.isSeparator_iff_forall_indecomposable`: over a left Artinian ring, `M` is a
  separator of `mod A` exactly when every indecomposable projective is a direct summand of `M`.
* `TauCeti.IsInjectiveEnvelope.isCoseparator_iff_additiveClosure`: `M` is a coseparator of `mod A`
  exactly when `D A ∈ add M`.
* `TauCeti.IsInjectiveEnvelope.isGeneratorCogenerator_iff_additiveClosure`: `M` is a
  generator-cogenerator exactly when `A ∈ add M` and `D A ∈ add M`.
* `FGModuleCat.isCoseparator_iff_forall_indecomposable`: `M` is a coseparator exactly when every
  indecomposable injective is a direct summand of `M`.
* `TauCeti.isGeneratorCogenerator_iff_forall_indecomposable`: `M` is a generator-cogenerator exactly
  when every indecomposable projective and every indecomposable injective is a direct summand of
  `M`.
* `TauCeti.IsInjectiveEnvelope.isGeneratorCogenerator_regular_biprod_fgModuleCatMatlisDualRegular`:
  `A ⊕ D A` is a generator-cogenerator.
* `FGModuleCat.not_isCoseparator_int`: `ℤ` is not a coseparator of `mod ℤ`.

## References

* M. Auslander, I. Reiten, S. O. Smalø, *Representation Theory of Artin Algebras*, Cambridge
  University Press (1995), Sections II.3 and VI.5.
-/

public section

noncomputable section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

attribute [local instance] hasBinaryBiproducts_of_finite_biproducts

/-- **The separators of `mod A` through indecomposables**: over a left Artinian ring, `M` is a
separator of `mod A` exactly when every indecomposable projective object is a direct summand of
`M`. -/
theorem _root_.FGModuleCat.isSeparator_iff_forall_indecomposable {A : Type u} [Ring A]
    [IsArtinianRing A] (M : FGModuleCat.{u} A) :
    IsSeparator M ↔
      ∀ P : FGModuleCat.{u} A, Projective P → Indecomposable P.obj → Nonempty (Retract P M) := by
  have : Projective (FGModuleCat.of A A) := FGModuleCat.projective_of_free A _
  rw [FGModuleCat.isSeparator_iff_additiveClosure]
  refine ⟨fun hM P hP hPi ↦ ?_, fun h ↦ ?_⟩
  · have := FGModuleCat.isLocalRing_end_of_indecomposable hPi
    exact additiveClosure_iff_nonempty_retract.1
      (additiveClosure_le_iff.2 hM _ (FGModuleCat.additiveClosure_regular_of_projective P))
  · refine additiveClosure_iff_forall_indecomposable.2 fun Y hY ⟨r⟩ ↦ ?_
    exact h Y r.projective ((FGModuleCat.indecomposable_obj_iff Y).2 hY)

section Artin

variable {R : Type u} [CommRing R] [IsArtinianRing R] {E : Type v} [AddCommGroup E] [Module R E]
  [Small.{v} R] {f : R ⧸ Ring.jacobson R →ₗ[R] E} {A : Type v} [Ring A] [Algebra R A]
  [Module.Finite R A]

/-- The Matlis dual `D A = Hom_R(A, E)` of the right regular module, as a finitely generated left
`A`-module: the image of the regular right module `Aᵐᵒᵖ` under the Matlis duality
`(mod A)ᵒᵖ ≌ mod Aᵐᵒᵖ`. Defining it through the duality, rather than as the module
`Hom_R(A, E)`, makes the statements about `D A` the duals of the statements about the regular
module. -/
def IsInjectiveEnvelope.fgModuleCatMatlisDualRegular (hf : IsInjectiveEnvelope f) :
    FGModuleCat.{v} A :=
  ((hf.fgModuleCatMatlisDuality (A := A)).inverse.obj (FGModuleCat.of Aᵐᵒᵖ Aᵐᵒᵖ)).unop

theorem IsInjectiveEnvelope.fgModuleCatMatlisDualRegular_def (hf : IsInjectiveEnvelope f) :
    hf.fgModuleCatMatlisDualRegular (A := A) =
      ((hf.fgModuleCatMatlisDuality (A := A)).inverse.obj (FGModuleCat.of Aᵐᵒᵖ Aᵐᵒᵖ)).unop :=
  (rfl)

/-- The underlying module of `D A` is the Matlis dual of the regular right module. -/
@[simp]
theorem IsInjectiveEnvelope.fgModuleCatMatlisDualRegular_obj (hf : IsInjectiveEnvelope f) :
    (hf.fgModuleCatMatlisDualRegular (A := A)).obj =
      ModuleCat.matlisDualOpObj R E (ModuleCat.of Aᵐᵒᵖ Aᵐᵒᵖ) :=
  (rfl)

/-- The underlying module of `D A` is the Matlis dual `Hom_R(A, E)` of the right regular module
`Aᵐᵒᵖ`. The two sides differ only in the `R`-action on `Aᵐᵒᵖ`: through the algebra map in `D A`, and
the usual one in `MatlisDual R E Aᵐᵒᵖ`. -/
def IsInjectiveEnvelope.fgModuleCatMatlisDualRegularEquiv (hf : IsInjectiveEnvelope f) :
    (hf.fgModuleCatMatlisDualRegular (A := A)).obj ≃ₗ[A] MatlisDual R E Aᵐᵒᵖ :=
  (ModuleCat.matlisDualOpObjEquiv R E (ModuleCat.of Aᵐᵒᵖ Aᵐᵒᵖ)).trans
    -- The `R`-action on `ModuleCat.of Aᵐᵒᵖ Aᵐᵒᵖ` is passed explicitly: instance search would find
    -- the usual action on `Aᵐᵒᵖ` instead of the action through the algebra map.
    (@MatlisDual.congrOp R _ E _ _ A _ _ Aᵐᵒᵖ _ _ _ _ (ModuleCat.of Aᵐᵒᵖ Aᵐᵒᵖ) _
      (ModuleCat.moduleOfAlgebra R _) _ (ModuleCat.isScalarTower_moduleOfAlgebra R _)
      (LinearEquiv.refl _ _))

/-- The Matlis dual of `D A` is the regular right module, by evaluation. -/
def IsInjectiveEnvelope.fgModuleCatMatlisDualObjFgModuleCatMatlisDualRegularIso
    (hf : IsInjectiveEnvelope f) :
    hf.fgModuleCatMatlisDual.obj (op (hf.fgModuleCatMatlisDualRegular (A := A))) ≅
      FGModuleCat.of Aᵐᵒᵖ Aᵐᵒᵖ :=
  (hf.fgModuleCatMatlisDuality (A := A)).counitIso.app _

attribute [local instance] ModuleCat.moduleOfAlgebra ModuleCat.isScalarTower_moduleOfAlgebra in
/-- The inverse of `D (D A) ≅ Aᵐᵒᵖ` sends `a` to evaluation at `a`. A pre-simp lemma
(`simp↓`): it applies before `fgModuleCatMatlisDual_obj_obj` rewrites the type of the morphism. -/
@[simp↓]
theorem IsInjectiveEnvelope.fgModuleCatMatlisDualObjFgModuleCatMatlisDualRegularIso_inv_apply
    (hf : IsInjectiveEnvelope f) (a : Aᵐᵒᵖ) (φ : (hf.fgModuleCatMatlisDualRegular (A := A)).obj) :
    MatlisDual.equivLinearMap R E _
      (ModuleCat.matlisDualObjEquiv R E (hf.fgModuleCatMatlisDualRegular (A := A)).obj
        ((hf.fgModuleCatMatlisDualObjFgModuleCatMatlisDualRegularIso (A := A)).inv.hom a)) φ =
      MatlisDual.equivLinearMap R E Aᵐᵒᵖ (hf.fgModuleCatMatlisDualRegularEquiv φ) a := by
  refine (hf.moduleCatEvalIsoOp_hom_apply (A := A) (ModuleCat.of Aᵐᵒᵖ Aᵐᵒᵖ) _ a φ).trans ?_
  exact (@MatlisDual.congrOp_apply R _ E _ _ A _ _ Aᵐᵒᵖ _ _ _ _ (ModuleCat.of Aᵐᵒᵖ Aᵐᵒᵖ) _
    (ModuleCat.moduleOfAlgebra R _) _ (ModuleCat.isScalarTower_moduleOfAlgebra R _)
    (LinearEquiv.refl _ _) (ModuleCat.matlisDualOpObjEquiv R E _ φ) a).symm

/-- `D A` is an injective object of `mod A`, as the dual of the projective right module `Aᵐᵒᵖ`. -/
instance IsInjectiveEnvelope.injective_fgModuleCatMatlisDualRegular (hf : IsInjectiveEnvelope f) :
    Injective (hf.fgModuleCatMatlisDualRegular (A := A)) := by
  have : Projective (FGModuleCat.of Aᵐᵒᵖ Aᵐᵒᵖ) := FGModuleCat.projective_of_free Aᵐᵒᵖ _
  have : Projective ((hf.fgModuleCatMatlisDuality (A := A)).inverse.obj
      (FGModuleCat.of Aᵐᵒᵖ Aᵐᵒᵖ)) :=
    (hf.fgModuleCatMatlisDuality.symm.map_projective_iff _).2 inferInstance
  exact inferInstanceAs (Injective (unop _))

/-- `D A` is a coseparator of `mod A`, as the dual of the separator `Aᵐᵒᵖ` of `mod Aᵐᵒᵖ`. -/
theorem IsInjectiveEnvelope.isCoseparator_fgModuleCatMatlisDualRegular
    (hf : IsInjectiveEnvelope f) : IsCoseparator (hf.fgModuleCatMatlisDualRegular (A := A)) :=
  (isCoseparator_unop_iff _).2
    ((FGModuleCat.isSeparator Aᵐᵒᵖ).of_equivalence hf.fgModuleCatMatlisDuality.symm)

/-- **Finitely generated injective modules are summands of finite sums of `D A`**: an injective
object of `mod A` lies in `add (D A)`. This is the dual of
`FGModuleCat.additiveClosure_regular_of_projective` over `Aᵐᵒᵖ`. -/
theorem IsInjectiveEnvelope.additiveClosure_fgModuleCatMatlisDualRegular_of_injective
    (hf : IsInjectiveEnvelope f) (I : FGModuleCat.{v} A) [Injective I] :
    additiveClosure (hf.fgModuleCatMatlisDualRegular (A := A)) I := by
  let Φ := hf.fgModuleCatMatlisDuality (A := A)
  have : Projective (Φ.functor.obj (op I)) := (Φ.map_projective_iff _).2 inferInstance
  rw [← Φ.additiveClosure_functor_obj_op_iff]
  exact (hf.fgModuleCatMatlisDualObjFgModuleCatMatlisDualRegularIso (A := A)).symm.retract
    |>.additiveClosure_le _
      (FGModuleCat.additiveClosure_regular_of_projective (Φ.functor.obj (op I)))

/-- **The coseparators of `mod A`**: `M` is a coseparator of `mod A` exactly when `D A` lies in
`add M`. Under the Matlis duality this is `FGModuleCat.isSeparator_iff_additiveClosure` for the
right module `D M`. -/
theorem IsInjectiveEnvelope.isCoseparator_iff_additiveClosure (hf : IsInjectiveEnvelope f)
    (M : FGModuleCat.{v} A) :
    IsCoseparator M ↔ additiveClosure M (hf.fgModuleCatMatlisDualRegular (A := A)) := by
  refine ⟨fun hM ↦ ?_, hf.isCoseparator_fgModuleCatMatlisDualRegular.of_additiveClosure⟩
  let Φ := hf.fgModuleCatMatlisDuality (A := A)
  have hN : IsSeparator (Φ.functor.obj (op M)) :=
    ((isSeparator_op_iff M).2 hM).of_equivalence Φ
  rw [← Φ.additiveClosure_functor_obj_op_iff]
  exact (additiveClosure _).prop_of_retract
    (hf.fgModuleCatMatlisDualObjFgModuleCatMatlisDualRegularIso (A := A)).retract
    ((FGModuleCat.isSeparator_iff_additiveClosure _).1 hN)

/-- **The generator-cogenerators of `mod A`**: `M` is a generator-cogenerator exactly when the
regular module `A` and its dual `D A` lie in `add M`. -/
theorem IsInjectiveEnvelope.isGeneratorCogenerator_iff_additiveClosure
    (hf : IsInjectiveEnvelope f) (M : FGModuleCat.{v} A) :
    IsGeneratorCogenerator M ↔ additiveClosure M (FGModuleCat.of A A) ∧
      additiveClosure M (hf.fgModuleCatMatlisDualRegular (A := A)) :=
  isGeneratorCogenerator_iff.trans <| and_congr (FGModuleCat.isSeparator_iff_additiveClosure M)
    (hf.isCoseparator_iff_additiveClosure M)

/-- **`A ⊕ D A` is a generator-cogenerator** of `mod A`. -/
theorem IsInjectiveEnvelope.isGeneratorCogenerator_regular_biprod_fgModuleCatMatlisDualRegular
    (hf : IsInjectiveEnvelope f) :
    IsGeneratorCogenerator (FGModuleCat.of A A ⊞ hf.fgModuleCatMatlisDualRegular (A := A)) :=
  (hf.isGeneratorCogenerator_iff_additiveClosure _).2
    ⟨(additiveClosure _).prop_of_retract ⟨biprod.inl, biprod.fst, by simp⟩ (additiveClosure_self _),
      (additiveClosure _).prop_of_retract ⟨biprod.inr, biprod.snd, by simp⟩
        (additiveClosure_self _)⟩

end Artin

/-- **The coseparators of `mod A` through indecomposables**: over an Artin algebra, `M` is a
coseparator of `mod A` exactly when every indecomposable injective object is a direct summand of
`M`. -/
theorem _root_.FGModuleCat.isCoseparator_iff_forall_indecomposable (R : Type u) [CommRing R]
    [IsArtinianRing R] {A : Type v} [Ring A] [Algebra R A] [Module.Finite R A]
    (M : FGModuleCat.{v} A) :
    IsCoseparator M ↔
      ∀ I : FGModuleCat.{v} A, Injective I → Indecomposable I.obj → Nonempty (Retract I M) := by
  have := IsArtinianRing.of_finite R A
  -- Replace `R` by the centre `C` of `A`, which lies in the universe of `A`, to take `E` there.
  let C := Subalgebra.center R A
  let _ : Algebra C A := inferInstanceAs (Algebra (Subring.center A) A)
  have : IsScalarTower R C A := .of_algebraMap_eq fun _ ↦ rfl
  have : Module.Finite C A := .of_restrictScalars_finite R C A
  obtain ⟨E, _, _, f, hf⟩ := exists_isInjectiveEnvelope C (C ⧸ Ring.jacobson C)
  have := hf.injective_fgModuleCatMatlisDualRegular (A := A)
  rw [hf.isCoseparator_iff_additiveClosure]
  refine ⟨fun hM I hI hIi ↦ ?_, fun h ↦ ?_⟩
  · have := FGModuleCat.isLocalRing_end_of_indecomposable hIi
    exact additiveClosure_iff_nonempty_retract.1 (additiveClosure_le_iff.2 hM _
      (hf.additiveClosure_fgModuleCatMatlisDualRegular_of_injective I))
  · refine additiveClosure_iff_forall_indecomposable.2 fun Y hY ⟨r⟩ ↦ ?_
    exact h Y r.injective ((FGModuleCat.indecomposable_obj_iff Y).2 hY)

/-- **Generator-cogenerators through indecomposables**: over an Artin algebra, `M` is a
generator-cogenerator of `mod A` exactly when every indecomposable projective and every
indecomposable injective object of `mod A` is a direct summand of `M`. -/
theorem isGeneratorCogenerator_iff_forall_indecomposable (R : Type u) [CommRing R]
    [IsArtinianRing R] {A : Type v} [Ring A] [Algebra R A] [Module.Finite R A]
    (M : FGModuleCat.{v} A) :
    IsGeneratorCogenerator M ↔
      (∀ P : FGModuleCat.{v} A, Projective P → Indecomposable P.obj → Nonempty (Retract P M)) ∧
        ∀ I : FGModuleCat.{v} A, Injective I → Indecomposable I.obj → Nonempty (Retract I M) := by
  have := IsArtinianRing.of_finite R A
  exact isGeneratorCogenerator_iff.trans <| and_congr
    (FGModuleCat.isSeparator_iff_forall_indecomposable M)
      (FGModuleCat.isCoseparator_iff_forall_indecomposable R M)

/-- **`ℤ` is not a coseparator of `mod ℤ`**: every morphism `ℤ/2ℤ ⟶ ℤ` is zero, so the identity of
the nonzero module `ℤ/2ℤ` is not detected by morphisms into `ℤ`. -/
theorem _root_.FGModuleCat.not_isCoseparator_int : ¬ IsCoseparator (FGModuleCat.of ℤ ℤ) := by
  intro h
  have hz : ∀ g : FGModuleCat.of ℤ (ZMod 2) ⟶ FGModuleCat.of ℤ ℤ, g = 0 := fun g ↦ by
    refine ObjectProperty.hom_ext _ (ModuleCat.hom_ext (LinearMap.ext fun x ↦ ?_))
    have hx : (2 : ℤ) • x = 0 := by
      simp [zsmul_eq_mul, show (2 : ZMod 2) = 0 from rfl]
    have h2 : (2 : ℤ) • g.hom.hom x = 0 := by rw [← map_zsmul, hx, map_zero]
    simpa using h2
  have h1 := (Preadditive.isCoseparator_iff _).1 h (𝟙 (FGModuleCat.of ℤ (ZMod 2)))
    fun g ↦ by rw [hz g, Limits.comp_zero]
  have := congr(($h1).hom.hom 1)
  simp at this

end TauCeti
