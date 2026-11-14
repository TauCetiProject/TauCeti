/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.FGModuleCat.Generator
public import TauCeti.Algebra.Category.FGModuleCat.KrullSchmidt
public import TauCeti.Algebra.Category.FGModuleCat.MatlisDuality
public import TauCeti.Algebra.Category.FGModuleCat.Projective
public import TauCeti.CategoryTheory.Preadditive.KrullSchmidt.AdditiveClosure
public import TauCeti.RingTheory.MatlisDuality.Semilocal

import TauCeti.CategoryTheory.Functor.RingEquivEnd

/-!
# Generator-cogenerators of `mod A` for an Artin algebra

Let `R` be a commutative Artinian ring and `A` an Artin `R`-algebra. A finitely generated module
`M` is a **generator-cogenerator** of `mod A = FGModuleCat A` (`TauCeti.IsGeneratorCogenerator`: a
separator and a coseparator) exactly when both the regular module `A` and its dual `D A` lie in the
additive closure `add M`, and exactly when every indecomposable projective and every
indecomposable injective object of `mod A` is a direct summand of `M`
(`TauCeti.isGeneratorCogenerator_iff_forall_indecomposable`).

The generator half holds over any ring (`FGModuleCat.isSeparator_iff_additiveClosure`). The
cogenerator half is its dual: the Matlis duality `(mod A)ᵒᵖ ≌ mod Aᵐᵒᵖ`
(`TauCeti.IsInjectiveEnvelope.fgModuleCatMatlisDuality`) turns coseparators of `mod A` into
separators of `mod Aᵐᵒᵖ`, and the regular right module into `D A`
(`TauCeti.IsInjectiveEnvelope.fgModuleCatDualRegular`); additive closures correspond under the
duality (`TauCeti.additiveClosure_functor_obj_op_iff`). So `M` is a coseparator exactly when
`D A ∈ add M` (`TauCeti.IsInjectiveEnvelope.isCoseparator_iff_additiveClosure`), with no separate
injective argument. The descriptions through indecomposable objects then follow from the
Krull-Schmidt property of `mod A`.

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

* `TauCeti.IsInjectiveEnvelope.fgModuleCatDualRegular`: the dual `D A` of the right regular module,
  a finitely generated left `A`-module.

## Main results

* `FGModuleCat.additiveClosure_regular_of_projective`: a finitely generated projective module lies
  in `add A`, over any ring.
* `TauCeti.IsInjectiveEnvelope.isCoseparator_iff_additiveClosure`: `M` is a coseparator of `mod A`
  exactly when `D A ∈ add M`.
* `TauCeti.IsInjectiveEnvelope.isGeneratorCogenerator_iff_additiveClosure`: `M` is a
  generator-cogenerator exactly when `A ∈ add M` and `D A ∈ add M`.
* `TauCeti.isGeneratorCogenerator_iff_forall_indecomposable`: `M` is a generator-cogenerator exactly
  when every indecomposable projective and every indecomposable injective is a direct summand of
  `M`.
* `TauCeti.IsInjectiveEnvelope.isGeneratorCogenerator_regular_biprod_dualRegular`: `A ⊕ D A` is a
  generator-cogenerator.
* `FGModuleCat.not_isCoseparator_int`: `ℤ` is not a coseparator of `mod ℤ`.

## References

* M. Auslander, I. Reiten, S. O. Smalø, *Representation Theory of Artin Algebras*, Cambridge
  University Press (1995), Sections II.3 and VI.5.
-/

public section

noncomputable section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits Opposite

universe u

attribute [local instance] hasBinaryBiproducts_of_finite_biproducts

section AnyRing

variable {A : Type u} [Ring A]

/-- **Finitely generated projective modules are summands of finite free modules**: a projective
object of `mod A` lies in the additive closure of the regular module. A finite generating family
gives an epimorphism from a finite sum of copies of `A`, which splits. -/
theorem _root_.FGModuleCat.additiveClosure_regular_of_projective (P : FGModuleCat.{u} A)
    [Projective P] : additiveClosure (FGModuleCat.of A A) P := by
  obtain ⟨n, x, hx⟩ := Module.Finite.exists_fin (R := A) (M := P)
  let p : (⨁ fun _ : Fin n ↦ FGModuleCat.of A A) ⟶ P := biproduct.desc fun i ↦
    ObjectProperty.homMk (ModuleCat.ofHom (LinearMap.toSpanSingleton A P (x i)))
  have : Epi p := Preadditive.epi_of_cancel_zero p fun {Z} g hg ↦ by
    have hgi (i : Fin n) : g.hom.hom (x i) = 0 := by
      have h := congr((biproduct.ι _ i ≫ $hg).hom.hom 1)
      simpa [p] using h
    refine ObjectProperty.hom_ext _ (ModuleCat.hom_ext (LinearMap.ext_on_range hx fun i ↦ ?_))
    simpa using hgi i
  exact additiveClosure_iff.2 ⟨n, ⟨⟨Projective.factorThru (𝟙 P) p, p, by simp⟩⟩⟩

variable [IsArtinianRing A]

/-- Over a left Artinian ring, a finitely generated module is indecomposable as a module exactly
when it is an indecomposable object of `mod A`. -/
theorem _root_.FGModuleCat.indecomposable_obj_iff (P : FGModuleCat.{u} A) :
    Indecomposable P.obj ↔ Indecomposable P := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have := FGModuleCat.isLocalRing_end_of_indecomposable h
    exact indecomposable_of_isLocalRing_end
  · have := (IsKrullSchmidt.indecomposable_iff_isLocalRing_end P).1 h
    have : IsLocalRing (End ((ObjectProperty.ι _).obj P)) :=
      ((ObjectProperty.fullyFaithfulι _).ringEquivEnd P).isLocalRing
    exact indecomposable_of_isLocalRing_end (X := (ObjectProperty.ι _).obj P)

/-- **The separators of `mod A` through indecomposables**: over a left Artinian ring, `M` is a
separator of `mod A` exactly when every indecomposable projective object is a direct summand of
`M`. -/
theorem _root_.FGModuleCat.isSeparator_iff_forall_indecomposable (M : FGModuleCat.{u} A) :
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

end AnyRing

section Artin

variable {R : Type u} [CommRing R] [IsArtinianRing R] {E : Type u} [AddCommGroup E] [Module R E]
  {f : R ⧸ Ring.jacobson R →ₗ[R] E} {A : Type u} [Ring A] [Algebra R A] [Module.Finite R A]

/-- The Matlis duality on `mod A` is an additive functor. -/
instance IsInjectiveEnvelope.additive_fgModuleCatMatlisDuality_functor
    (hf : IsInjectiveEnvelope f) : (hf.fgModuleCatMatlisDuality (A := A)).functor.Additive :=
  Functor.additive_of_preserves_binary_products _

/-- The dual `D A = Hom_R(A, E)` of the right regular module, as a finitely generated left
`A`-module: the image of the regular right module `Aᵐᵒᵖ` under the Matlis duality
`(mod A)ᵒᵖ ≌ mod Aᵐᵒᵖ`. Defining it through the duality, rather than as the module
`Hom_R(A, E)`, makes the statements about `D A` the duals of the statements about the regular
module. -/
def IsInjectiveEnvelope.fgModuleCatDualRegular (hf : IsInjectiveEnvelope f) : FGModuleCat.{u} A :=
  ((hf.fgModuleCatMatlisDuality (A := A)).inverse.obj (FGModuleCat.of Aᵐᵒᵖ Aᵐᵒᵖ)).unop

/-- `D A` is an injective object of `mod A`, as the dual of the projective right module `Aᵐᵒᵖ`. -/
theorem IsInjectiveEnvelope.injective_fgModuleCatDualRegular (hf : IsInjectiveEnvelope f) :
    Injective (hf.fgModuleCatDualRegular (A := A)) := by
  have : Projective (FGModuleCat.of Aᵐᵒᵖ Aᵐᵒᵖ) := FGModuleCat.projective_of_free Aᵐᵒᵖ _
  have : Projective ((hf.fgModuleCatMatlisDuality (A := A)).inverse.obj
      (FGModuleCat.of Aᵐᵒᵖ Aᵐᵒᵖ)) :=
    (hf.fgModuleCatMatlisDuality.symm.map_projective_iff _).2 inferInstance
  exact inferInstanceAs (Injective (unop _))

/-- `D A` is a coseparator of `mod A`, as the dual of the separator `Aᵐᵒᵖ` of `mod Aᵐᵒᵖ`. -/
theorem IsInjectiveEnvelope.isCoseparator_fgModuleCatDualRegular (hf : IsInjectiveEnvelope f) :
    IsCoseparator (hf.fgModuleCatDualRegular (A := A)) :=
  (isCoseparator_unop_iff _).2
    ((FGModuleCat.isSeparator Aᵐᵒᵖ).of_equivalence hf.fgModuleCatMatlisDuality.symm)

/-- **Finitely generated injective modules are summands of finite sums of `D A`**: an injective
object of `mod A` lies in `add (D A)`. This is the dual of
`FGModuleCat.additiveClosure_regular_of_projective` over `Aᵐᵒᵖ`. -/
theorem IsInjectiveEnvelope.additiveClosure_fgModuleCatDualRegular_of_injective
    (hf : IsInjectiveEnvelope f) (I : FGModuleCat.{u} A) [Injective I] :
    additiveClosure (hf.fgModuleCatDualRegular (A := A)) I := by
  let Φ := hf.fgModuleCatMatlisDuality (A := A)
  have : Projective (Φ.functor.obj (op I)) := (Φ.map_projective_iff _).2 inferInstance
  rw [← additiveClosure_functor_obj_op_iff Φ]
  exact additiveClosure_le_of_retract (Φ.counitIso.app (FGModuleCat.of Aᵐᵒᵖ Aᵐᵒᵖ)).symm.retract _
    (FGModuleCat.additiveClosure_regular_of_projective (Φ.functor.obj (op I)))

/-- **The coseparators of `mod A`**: `M` is a coseparator of `mod A` exactly when `D A` lies in
`add M`. Under the Matlis duality this is `FGModuleCat.isSeparator_iff_additiveClosure` for the
right module `D M`. -/
theorem IsInjectiveEnvelope.isCoseparator_iff_additiveClosure (hf : IsInjectiveEnvelope f)
    (M : FGModuleCat.{u} A) :
    IsCoseparator M ↔ additiveClosure M (hf.fgModuleCatDualRegular (A := A)) := by
  refine ⟨fun hM ↦ ?_, hf.isCoseparator_fgModuleCatDualRegular.of_additiveClosure⟩
  let Φ := hf.fgModuleCatMatlisDuality (A := A)
  have hN : IsSeparator (Φ.functor.obj (op M)) :=
    ((isSeparator_op_iff M).2 hM).of_equivalence Φ
  rw [← additiveClosure_functor_obj_op_iff Φ]
  exact (additiveClosure _).prop_of_retract (Φ.counitIso.app (FGModuleCat.of Aᵐᵒᵖ Aᵐᵒᵖ)).retract
    ((FGModuleCat.isSeparator_iff_additiveClosure _).1 hN)

/-- **The generator-cogenerators of `mod A`**: `M` is a generator-cogenerator exactly when the
regular module `A` and its dual `D A` lie in `add M`. -/
theorem IsInjectiveEnvelope.isGeneratorCogenerator_iff_additiveClosure
    (hf : IsInjectiveEnvelope f) (M : FGModuleCat.{u} A) :
    IsGeneratorCogenerator M ↔ additiveClosure M (FGModuleCat.of A A) ∧
      additiveClosure M (hf.fgModuleCatDualRegular (A := A)) :=
  isGeneratorCogenerator_iff.trans <| and_congr (FGModuleCat.isSeparator_iff_additiveClosure M)
    (hf.isCoseparator_iff_additiveClosure M)

/-- **`A ⊕ D A` is a generator-cogenerator** of `mod A`. -/
theorem IsInjectiveEnvelope.isGeneratorCogenerator_regular_biprod_dualRegular
    (hf : IsInjectiveEnvelope f) :
    IsGeneratorCogenerator (FGModuleCat.of A A ⊞ hf.fgModuleCatDualRegular (A := A)) :=
  (hf.isGeneratorCogenerator_iff_additiveClosure _).2
    ⟨(additiveClosure _).prop_of_retract ⟨biprod.inl, biprod.fst, by simp⟩ (additiveClosure_self _),
      (additiveClosure _).prop_of_retract ⟨biprod.inr, biprod.snd, by simp⟩
        (additiveClosure_self _)⟩

/-- **The coseparators of `mod A` through indecomposables**: `M` is a coseparator of `mod A`
exactly when every indecomposable injective object is a direct summand of `M`. -/
theorem IsInjectiveEnvelope.isCoseparator_iff_forall_indecomposable (hf : IsInjectiveEnvelope f)
    (M : FGModuleCat.{u} A) :
    IsCoseparator M ↔
      ∀ I : FGModuleCat.{u} A, Injective I → Indecomposable I.obj → Nonempty (Retract I M) := by
  have := IsArtinianRing.of_finite R A
  have := hf.injective_fgModuleCatDualRegular (A := A)
  rw [hf.isCoseparator_iff_additiveClosure]
  refine ⟨fun hM I hI hIi ↦ ?_, fun h ↦ ?_⟩
  · have := FGModuleCat.isLocalRing_end_of_indecomposable hIi
    exact additiveClosure_iff_nonempty_retract.1
      (additiveClosure_le_iff.2 hM _ (hf.additiveClosure_fgModuleCatDualRegular_of_injective I))
  · refine additiveClosure_iff_forall_indecomposable.2 fun Y hY ⟨r⟩ ↦ ?_
    exact h Y r.injective ((FGModuleCat.indecomposable_obj_iff Y).2 hY)

end Artin

/-- **Generator-cogenerators through indecomposables**: over an Artin algebra, `M` is a
generator-cogenerator of `mod A` exactly when every indecomposable projective and every
indecomposable injective object of `mod A` is a direct summand of `M`. -/
theorem isGeneratorCogenerator_iff_forall_indecomposable (R : Type u) [CommRing R]
    [IsArtinianRing R] {A : Type u} [Ring A] [Algebra R A] [Module.Finite R A]
    (M : FGModuleCat.{u} A) :
    IsGeneratorCogenerator M ↔
      (∀ P : FGModuleCat.{u} A, Projective P → Indecomposable P.obj → Nonempty (Retract P M)) ∧
        ∀ I : FGModuleCat.{u} A, Injective I → Indecomposable I.obj → Nonempty (Retract I M) := by
  obtain ⟨E, _, _, f, hf, -⟩ := exists_isInjectiveEnvelope_quotient_jacobson (R := R)
  have := IsArtinianRing.of_finite R A
  exact isGeneratorCogenerator_iff.trans <| and_congr
    (FGModuleCat.isSeparator_iff_forall_indecomposable M)
      (hf.isCoseparator_iff_forall_indecomposable M)

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
