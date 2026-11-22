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

import Mathlib.RingTheory.Finiteness.Small
import TauCeti.Algebra.Category.FGModuleCat.Injective
import TauCeti.Algebra.Subalgebra.Center
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
over which `A` is again an Artin algebra. The descriptions through indecomposable objects hold for
modules in any universe in which `A` is small.

The generator half holds over any ring (`FGModuleCat.isSeparator_iff_additiveClosure`). The
cogenerator half is its dual: the Matlis duality `(mod A)ᵒᵖ ≌ mod Aᵐᵒᵖ`
(`TauCeti.IsInjectiveEnvelope.fgModuleCatMatlisDuality`) turns coseparators of `mod A` into
separators of `mod Aᵐᵒᵖ`, and the regular right module into `D A`
(`TauCeti.IsInjectiveEnvelope.fgModuleCatMatlisDualRegular`, with its API in
`TauCeti/Algebra/Category/FGModuleCat/MatlisDuality.lean`); additive closures correspond under
the duality (`CategoryTheory.Equivalence.additiveClosure_functor_obj_op_iff`). So `M` is a
coseparator exactly when `D A ∈ add M`
(`TauCeti.IsInjectiveEnvelope.isCoseparator_iff_additiveClosure`), with no separate injective
argument. The descriptions through indecomposable objects then follow from the
Krull-Schmidt property of `mod A`, with `FGModuleCat.indecomposable_obj_iff` and
`FGModuleCat.additiveClosure_of_isGenerator_of_projective`: a projective object lies in `add M` for
every separator `M`, and dually an injective object lies in `add M` for every coseparator `M`
(`FGModuleCat.additiveClosure_of_isCoseparator_of_injective`).

Over an Artin algebra, with `A` small in the module universe, a coseparator `M` is injective over
its endomorphism ring (`FGModuleCat.injective_end_of_isCoseparator`), dually to a generator being
projective over it (`TauCeti.Module.IsGenerator.projective_end`): by projectivization and the
Hom-tensor adjunction its dual is projective over the endomorphism ring, and Matlis biduality
returns to `M`. This is the cogenerator half of the Morita-Tachikawa correspondence.

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

## Main results

* `FGModuleCat.isSeparator_iff_forall_indecomposable`: over a left Artinian ring, `M` is a
  separator of `mod A` exactly when every indecomposable projective is a direct summand of `M`.
* `TauCeti.IsInjectiveEnvelope.isCoseparator_iff_additiveClosure`: `M` is a coseparator of `mod A`
  exactly when `D A ∈ add M`.
* `TauCeti.IsInjectiveEnvelope.isGeneratorCogenerator_iff_additiveClosure`: `M` is a
  generator-cogenerator exactly when `A ∈ add M` and `D A ∈ add M`.
* `FGModuleCat.additiveClosure_of_isCoseparator_of_injective`: over an Artin algebra, an injective
  object of `mod A` lies in `add M` for every coseparator `M`.
* `FGModuleCat.isCoseparator_iff_forall_indecomposable`: `M` is a coseparator exactly when every
  indecomposable injective is a direct summand of `M`.
* `TauCeti.isGeneratorCogenerator_iff_forall_indecomposable`: `M` is a generator-cogenerator exactly
  when every indecomposable projective and every indecomposable injective is a direct summand of
  `M`.
* `TauCeti.IsInjectiveEnvelope.isGeneratorCogenerator_regular_biprod_fgModuleCatMatlisDualRegular`:
  `A ⊕ D A` is a generator-cogenerator.
* `FGModuleCat.injective_end_of_isCoseparator`: over an Artin algebra, a coseparator `M` of `mod A`
  is an injective module over its endomorphism ring `Γ`.
* `FGModuleCat.not_isCoseparator_int`: `ℤ` is not a coseparator of `mod ℤ`.

## References

* M. Auslander, I. Reiten, S. O. Smalø, *Representation Theory of Artin Algebras*, Cambridge
  University Press (1995), Sections II.3 and VI.5.
* B. J. Müller, *The classification of algebras by dominant dimension*, Canad. J. Math. 20 (1968),
  398–409, Theorem 2.
-/

public section

noncomputable section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits Opposite

universe u v w

attribute [local instance] hasBinaryBiproducts_of_finite_biproducts

/-- **The separators of `mod A` through indecomposables**: over a left Artinian ring, `M` is a
separator of `mod A` exactly when every indecomposable projective object is a direct summand of
`M`. The modules may live in any universe in which `A` is small. -/
theorem _root_.FGModuleCat.isSeparator_iff_forall_indecomposable {A : Type u} [Ring A]
    [IsArtinianRing A] [Small.{w} A] (M : FGModuleCat.{w} A) :
    IsSeparator M ↔
      ∀ P : FGModuleCat.{w} A, Projective P → Indecomposable P.obj → Nonempty (Retract P M) := by
  -- The regular module, shrunk to the universe `w`, is a projective separator.
  let e := Shrink.linearEquiv.{w} A A
  have : Module.Free A (Shrink.{w} A) := .of_equiv e.symm
  have : Module.IsGenerator A (Shrink.{w} A) := .of_linearEquiv e
  have : Projective (FGModuleCat.of A (Shrink.{w} A)) := FGModuleCat.projective_of_free A _
  refine ⟨fun hM P hP hPi ↦ ?_, fun h ↦ ?_⟩
  · have := FGModuleCat.isLocalRing_end_of_indecomposable hPi
    have := FGModuleCat.isGenerator_of_isSeparator hM
    exact additiveClosure_iff_nonempty_retract.1
      (FGModuleCat.additiveClosure_of_isGenerator_of_projective M P)
  · refine (FGModuleCat.isSeparator_of_isGenerator (FGModuleCat.of A (Shrink.{w} A)))
      |>.of_additiveClosure (additiveClosure_iff_forall_indecomposable.2 fun Y hY ⟨r⟩ ↦ ?_)
    exact h Y r.projective ((FGModuleCat.indecomposable_obj_iff Y).2 hY)

section Artin

variable {R : Type u} [CommRing R] [IsArtinianRing R] {E : Type v} [AddCommGroup E] [Module R E]
  [Small.{v} R] {f : R ⧸ Ring.jacobson R →ₗ[R] E} {A : Type v} [Ring A] [Algebra R A]
  [Module.Finite R A]

/-- `D A` is a coseparator of `mod A`, as the dual of the separator `Aᵐᵒᵖ` of `mod Aᵐᵒᵖ`. -/
theorem IsInjectiveEnvelope.isCoseparator_fgModuleCatMatlisDualRegular
    (hf : IsInjectiveEnvelope f) : IsCoseparator (hf.fgModuleCatMatlisDualRegular (A := A)) := by
  rw [hf.fgModuleCatMatlisDualRegular_def, isCoseparator_unop_iff]
  exact (FGModuleCat.isSeparator Aᵐᵒᵖ).of_equivalence hf.fgModuleCatMatlisDuality.symm

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

/-- **Finitely generated injective modules are summands of finite sums of a coseparator**: over an
Artin algebra, if `M` is a coseparator of `mod A`, then an injective object of `mod A` lies in
`add M`. This is dual to `FGModuleCat.additiveClosure_of_isGenerator_of_projective`. The modules
may live in any universe in which `A` is small. -/
theorem _root_.FGModuleCat.additiveClosure_of_isCoseparator_of_injective (R : Type u) [CommRing R]
    [IsArtinianRing R] {A : Type v} [Ring A] [Algebra R A] [Module.Finite R A] [Small.{w} A]
    {M : FGModuleCat.{w} A} (hM : IsCoseparator M) (I : FGModuleCat.{w} A) [Injective I] :
    additiveClosure M I := by
  -- Replace `R` by the centre `C` of `A`, which is small in the universe `w`, and take an injective
  -- hull `E` of `C ⧸ J(C)` there.
  let C := Subalgebra.center R A
  have : Module.Finite C A := Subalgebra.finite_centerAlgebra_of_finite
  have : Small.{w} C := inferInstanceAs (Small.{w} {a : A // a ∈ C})
  have : Small.{w} (C ⧸ Ring.jacobson C) := small_of_surjective Ideal.Quotient.mk_surjective
  let e := Shrink.linearEquiv.{w} C (C ⧸ Ring.jacobson C)
  obtain ⟨E, _, _, i, hi⟩ := exists_isInjectiveEnvelope C (Shrink.{w} (C ⧸ Ring.jacobson C))
  have hf := hi.comp e.symm.injective (by rw [LinearEquiv.range]; exact isEssential_top)
  -- The Matlis duality turns the coseparator `M` and the injective `I` into a separator and a
  -- projective of `mod Aᵐᵒᵖ`.
  let Φ := hf.fgModuleCatMatlisDuality (A := A)
  have : Small.{w} Aᵐᵒᵖ := small_of_injective MulOpposite.unop_injective
  have := FGModuleCat.isGenerator_of_isSeparator (((isSeparator_op_iff M).2 hM).of_equivalence Φ)
  have : Projective (Φ.functor.obj (op I)) := (Φ.map_projective_iff _).2 inferInstance
  exact Φ.additiveClosure_functor_obj_op_iff.1
    (FGModuleCat.additiveClosure_of_isGenerator_of_projective _ _)

/-- **The coseparators of `mod A` through indecomposables**: over an Artin algebra, `M` is a
coseparator of `mod A` exactly when every indecomposable injective object is a direct summand of
`M`. The modules may live in any universe in which `A` is small. -/
theorem _root_.FGModuleCat.isCoseparator_iff_forall_indecomposable (R : Type u) [CommRing R]
    [IsArtinianRing R] {A : Type v} [Ring A] [Algebra R A] [Module.Finite R A] [Small.{w} A]
    (M : FGModuleCat.{w} A) :
    IsCoseparator M ↔
      ∀ I : FGModuleCat.{w} A, Injective I → Indecomposable I.obj → Nonempty (Retract I M) := by
  have := IsArtinianRing.of_finite R A
  -- Replace `R` by the centre `C` of `A`, which is small in the universe `w`, and take an injective
  -- hull `E` of `C ⧸ J(C)` there.
  let C := Subalgebra.center R A
  have : Module.Finite C A := Subalgebra.finite_centerAlgebra_of_finite
  have : Small.{w} C := inferInstanceAs (Small.{w} {a : A // a ∈ C})
  have : Small.{w} (C ⧸ Ring.jacobson C) := small_of_surjective Ideal.Quotient.mk_surjective
  let e := Shrink.linearEquiv.{w} C (C ⧸ Ring.jacobson C)
  obtain ⟨E, _, _, i, hi⟩ := exists_isInjectiveEnvelope C (Shrink.{w} (C ⧸ Ring.jacobson C))
  have hf := hi.comp e.symm.injective (by rw [LinearEquiv.range]; exact isEssential_top)
  -- The Matlis duality turns coseparators and injectives of `mod A` into separators and
  -- projectives of `mod Aᵐᵒᵖ`, where the shrunk regular module is a projective separator.
  let Φ := hf.fgModuleCatMatlisDuality (A := A)
  have : Small.{w} Aᵐᵒᵖ := small_of_injective MulOpposite.unop_injective
  let e' := Shrink.linearEquiv.{w} Aᵐᵒᵖ Aᵐᵒᵖ
  have : Module.Free Aᵐᵒᵖ (Shrink.{w} Aᵐᵒᵖ) := .of_equiv e'.symm
  have : Module.IsGenerator Aᵐᵒᵖ (Shrink.{w} Aᵐᵒᵖ) := .of_linearEquiv e'
  let G := FGModuleCat.of Aᵐᵒᵖ (Shrink.{w} Aᵐᵒᵖ)
  have : Projective G := FGModuleCat.projective_of_free _ _
  refine ⟨fun hM I hI hIi ↦ ?_, fun h ↦ ?_⟩
  · have := FGModuleCat.isLocalRing_end_of_indecomposable hIi
    exact additiveClosure_iff_nonempty_retract.1
      (FGModuleCat.additiveClosure_of_isCoseparator_of_injective R hM I)
  · -- The dual `D` of `G` is an injective coseparator of `mod A`, and lies in `add M`.
    have : Projective (Φ.inverse.obj G) := (Φ.symm.map_projective_iff _).2 inferInstance
    have : Injective (Φ.inverse.obj G).unop := inferInstanceAs (Injective (unop _))
    have hD : IsCoseparator (Φ.inverse.obj G).unop := (isCoseparator_unop_iff _).2
      ((FGModuleCat.isSeparator_of_isGenerator G).of_equivalence Φ.symm)
    refine hD.of_additiveClosure (additiveClosure_iff_forall_indecomposable.2 fun Y hY ⟨r⟩ ↦ ?_)
    exact h Y r.injective ((FGModuleCat.indecomposable_obj_iff Y).2 hY)

/-- **Generator-cogenerators through indecomposables**: over an Artin algebra, `M` is a
generator-cogenerator of `mod A` exactly when every indecomposable projective and every
indecomposable injective object of `mod A` is a direct summand of `M`. The modules may live in any
universe in which `A` is small. -/
theorem isGeneratorCogenerator_iff_forall_indecomposable (R : Type u) [CommRing R]
    [IsArtinianRing R] {A : Type v} [Ring A] [Algebra R A] [Module.Finite R A] [Small.{w} A]
    (M : FGModuleCat.{w} A) :
    IsGeneratorCogenerator M ↔
      (∀ P : FGModuleCat.{w} A, Projective P → Indecomposable P.obj → Nonempty (Retract P M)) ∧
        ∀ I : FGModuleCat.{w} A, Injective I → Indecomposable I.obj → Nonempty (Retract I M) := by
  have := IsArtinianRing.of_finite R A
  exact isGeneratorCogenerator_iff.trans <| and_congr
    (FGModuleCat.isSeparator_iff_forall_indecomposable M)
      (FGModuleCat.isCoseparator_iff_forall_indecomposable R M)

/-- **A coseparator is injective over its endomorphism ring.** Over an Artin algebra `A`, a
coseparator `M` of `mod A` is an injective module over `Module.End A M`. The modules may live in
any universe in which `A` is small. -/
theorem _root_.FGModuleCat.injective_end_of_isCoseparator (R : Type u) [CommRing R]
    [IsArtinianRing R] {A : Type v} [Ring A] [Algebra R A] [Module.Finite R A] [Small.{w} A]
    {M : FGModuleCat.{w} A} (hM : IsCoseparator M) :
    Module.Injective (Module.End A M.obj) M.obj := by
  have := IsArtinianRing.of_finite R A
  -- Replace `R` by the centre `C` of `A`, which is small in the universe `w`, and take an injective
  -- hull `E` of `C ⧸ J(C)`.
  let C := Subalgebra.center R A
  have : Module.Finite C A := Subalgebra.finite_centerAlgebra_of_finite
  have : Small.{w} C := inferInstanceAs (Small.{w} {a : A // a ∈ C})
  obtain ⟨E, _, _, f, hf, -⟩ := exists_isInjectiveEnvelope_quotient_jacobson C
  have := hf.moduleInjective
  -- The dual `D_C A`, shrunk to the universe `w`, is a finitely generated injective module.
  have : Module.Finite Aᵐᵒᵖ A := .equiv (MulOpposite.opLinearEquiv Aᵐᵒᵖ).symm
  have : Module.Finite A (MatlisDual C E A) := hf.finite_matlisDual_of_finite_op
  have : Small.{w} (MatlisDual C E A) := Module.Finite.small A _
  let e := Shrink.linearEquiv.{w} A (MatlisDual C E A)
  have : Module.Finite A (Shrink.{w} (MatlisDual C E A)) := .equiv e.symm
  have : Module.Injective A (Shrink.{w} (MatlisDual C E A)) :=
    ((Module.Baer.of_injective inferInstance).of_equiv e.symm).injective
  let X := FGModuleCat.of A (Shrink.{w} (MatlisDual C E A))
  have : Injective X := FGModuleCat.injective_of_moduleInjective X
  -- As an injective object, `X` lies in `add M`; so `D_C M` is projective over `End M`.
  have := FGModuleCat.projective_end_op_matlisDual_of_additiveClosure (R := C)
    (FGModuleCat.additiveClosure_of_isCoseparator_of_injective R hM X) e
  exact moduleInjective_of_projective_op_matlisDual hf.length_quotient_linearMap_eq_one
    (isFiniteLength_of_finite_trans C A M.obj)

/-- **`ℤ` is not a coseparator of `mod ℤ`.** -/
theorem _root_.FGModuleCat.not_isCoseparator_int : ¬ IsCoseparator (FGModuleCat.of ℤ ℤ) := by
  -- Every morphism `ℤ/2ℤ ⟶ ℤ` is zero, so the identity of `ℤ/2ℤ` is not detected by them.
  intro h
  have hz : ∀ g : FGModuleCat.of ℤ (ZMod 2) ⟶ FGModuleCat.of ℤ ℤ, g = 0 := fun g ↦ by
    refine ObjectProperty.hom_ext _ (ModuleCat.hom_ext (LinearMap.ext fun x ↦ ?_))
    have hx : (2 : ℤ) • x = 0 := by
      simp [zsmul_eq_mul, CharTwo.two_eq_zero]
    have h2 : (2 : ℤ) • g.hom.hom x = 0 := by rw [← map_zsmul, hx, map_zero]
    simpa using h2
  have h1 := (Preadditive.isCoseparator_iff _).1 h (𝟙 (FGModuleCat.of ℤ (ZMod 2)))
    fun g ↦ by rw [hz g, Limits.comp_zero]
  have := congr(($h1).hom.hom 1)
  simp at this

end TauCeti
