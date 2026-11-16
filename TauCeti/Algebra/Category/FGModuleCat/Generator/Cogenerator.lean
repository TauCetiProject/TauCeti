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
(`TauCeti.IsInjectiveEnvelope.fgModuleCatMatlisDualRegular`, with its API in
`TauCeti/Algebra/Category/FGModuleCat/MatlisDuality.lean`); additive closures correspond under
the duality (`CategoryTheory.Equivalence.additiveClosure_functor_obj_op_iff`). So `M` is a
coseparator exactly when `D A ∈ add M`
(`TauCeti.IsInjectiveEnvelope.isCoseparator_iff_additiveClosure`), with no separate injective
argument. The descriptions through indecomposable objects then follow from the
Krull-Schmidt property of `mod A`, with `FGModuleCat.additiveClosure_regular_of_projective`, its
dual `TauCeti.IsInjectiveEnvelope.additiveClosure_fgModuleCatMatlisDualRegular_of_injective`, and
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
      simp [zsmul_eq_mul, CharTwo.two_eq_zero]
    have h2 : (2 : ℤ) • g.hom.hom x = 0 := by rw [← map_zsmul, hx, map_zero]
    simpa using h2
  have h1 := (Preadditive.isCoseparator_iff _).1 h (𝟙 (FGModuleCat.of ℤ (ZMod 2)))
    fun g ↦ by rw [hz g, Limits.comp_zero]
  have := congr(($h1).hom.hom 1)
  simp at this

end TauCeti
