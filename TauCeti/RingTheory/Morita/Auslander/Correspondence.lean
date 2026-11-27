/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.RepresentationFinite
public import TauCeti.Algebra.Category.ModuleCat.Algebra
public import TauCeti.RingTheory.Morita.Auslander.Basic
public import TauCeti.RingTheory.Morita.Setoid

import Mathlib.Data.Quot
import Mathlib.RingTheory.HopkinsLevitzki
import TauCeti.Algebra.Category.FGModuleCat.RepresentationFinite
import TauCeti.RingTheory.Morita.EndomorphismRing

/-!
# The Auslander correspondence on Morita classes

Over a commutative Artinian ring, the Morita classes of representation-finite Artin algebras
correspond to the Morita classes of Auslander algebras that are Artin algebras. The forward map
sends the class of an algebra to the class of the endomorphism algebra of any additive generator
of its finitely generated modules.

The correspondence includes the semisimple classes. Auslander, Reiten and Smalø,
*Representation Theory of Artin Algebras*, Theorem VI.5.7, p. 215, state the nonsemisimple case
using opposite endomorphism rings. Here the correspondence uses `Module.End` and assembles
`isAuslanderAlgebra_end`, `exists_isAdditiveGenerator_algEquiv_end`, and
`isMoritaEquivalent_end_iff`.

## References

* M. Auslander, I. Reiten and S. O. Smalø, *Representation Theory of Artin Algebras*, Chapter VI,
  <https://doi.org/10.1017/CBO9780511623608.007>.
-/

public section

namespace TauCeti

open scoped ModuleCat.Algebra

universe u

variable (R : Type*) [CommRing R]

/-- The Morita classes of representation-finite, module-finite `R`-algebras. -/
abbrev RepresentationFiniteMoritaClass :=
  Quotient (moritaSetoid R fun A : AlgCat.{u} R ↦
    Module.Finite R A ∧ IsRepresentationFinite.{u} A)

/-- The Morita classes of module-finite Auslander algebras over `R`. -/
abbrev AuslanderMoritaClass :=
  Quotient (moritaSetoid R fun Γ : AlgCat.{u} R ↦
    Module.Finite R Γ ∧ IsAuslanderAlgebra Γ)

variable [IsArtinianRing R]

/-- Choose an additive generator for the finitely generated modules over a representative. -/
private noncomputable def chooseAdditiveGenerator
    (A : {A : AlgCat.{u} R // Module.Finite R A ∧ IsRepresentationFinite.{u} A}) :
    {M : FGModuleCat.{u} A.val // IsAdditiveGenerator M} := by
  letI : Module.Finite R A.val := A.property.1
  letI : IsArtinianRing A.val := IsArtinianRing.of_finite R A.val
  exact Classical.indefiniteDescription _ (isRepresentationFinite_iff_exists_isAdditiveGenerator.mp
    A.property.2)

/-- The endomorphism algebra of the chosen additive generator, bundled with its
Auslander-algebra and finiteness properties. -/
private noncomputable def endOfChosenAdditiveGenerator
    (A : {A : AlgCat.{u} R // Module.Finite R A ∧ IsRepresentationFinite.{u} A}) :
    {Γ : AlgCat.{u} R // Module.Finite R Γ ∧ IsAuslanderAlgebra Γ} := by
  letI : Module.Finite R A.val := A.property.1
  let M := chooseAdditiveGenerator R A
  refine ⟨AlgCat.of R (Module.End A.val M.val.obj), ?_, isAuslanderAlgebra_end R M.val M.property⟩
  exact Module.Finite.equiv (ModuleCat.homLinearEquiv (S := R)
    (M := M.val.obj) (N := M.val.obj))

/-- Morita equivalence of the chosen endomorphism algebras is equivalent to Morita equivalence
of their original algebras. -/
private theorem endOfChosenAdditiveGenerator_rel_iff
    (A B : {A : AlgCat.{u} R // Module.Finite R A ∧ IsRepresentationFinite.{u} A}) :
    (moritaSetoid R _).r (endOfChosenAdditiveGenerator R A)
      (endOfChosenAdditiveGenerator R B) ↔ (moritaSetoid R _).r A B := by
  simp only [moritaSetoid_rel_iff]
  have : Module.Finite R A.val := A.property.1
  have : Module.Finite R B.val := B.property.1
  let M := chooseAdditiveGenerator R A
  let N := chooseAdditiveGenerator R B
  exact isMoritaEquivalent_end_iff R M.val N.val M.property N.property

/-- The Auslander correspondence sends the Morita class of a representation-finite Artin algebra
to the Morita class of the endomorphism algebra of an additive generator of its finitely generated
modules. -/
noncomputable def auslanderCorrespondence :
    RepresentationFiniteMoritaClass.{u} R ≃ AuslanderMoritaClass.{u} R := by
  let f : RepresentationFiniteMoritaClass.{u} R → AuslanderMoritaClass.{u} R :=
    Quotient.map (endOfChosenAdditiveGenerator R) fun {A B} h ↦
      (endOfChosenAdditiveGenerator_rel_iff R A B).2 h
  refine Equiv.ofBijective f ⟨?_, ?_⟩
  · intro a b
    refine Quotient.inductionOn₂ a b fun A B h ↦ ?_
    exact Quotient.sound ((endOfChosenAdditiveGenerator_rel_iff R A B).1 (Quotient.exact h))
  · intro q
    refine Quotient.inductionOn q fun Γ ↦ ?_
    have : Module.Finite R Γ.val := Γ.property.1
    obtain ⟨A, _, _, _, M, hM, ⟨e⟩⟩ :=
      exists_isAdditiveGenerator_algEquiv_end R Γ.val Γ.property.2
    have : IsArtinianRing A := IsArtinianRing.of_finite R A
    let a : {A : AlgCat.{u} R // Module.Finite R A ∧ IsRepresentationFinite.{u} A} :=
      ⟨AlgCat.of R A, inferInstance, isRepresentationFinite_iff_exists_isAdditiveGenerator.mpr
        ⟨M, hM⟩⟩
    let N := chooseAdditiveGenerator R a
    have h : IsMoritaEquivalent R (Module.End A N.val.obj) (Module.End A M.obj) :=
      N.property.isMoritaEquivalent_moduleEnd R hM
    refine ⟨Quotient.mk _ a, ?_⟩
    simp only [f, Quotient.map_mk, Quotient.eq, moritaSetoid_rel_iff]
    exact h.trans R (.of_algEquiv R e.symm)

/-- The image of a representative is the class of `Γ` exactly when `Γ` is Morita equivalent
to the endomorphism algebra of any given additive generator of the representative's module
category. -/
theorem auslanderCorrespondence_apply_mk_eq_iff
    (A : {A : AlgCat.{u} R // Module.Finite R A ∧ IsRepresentationFinite.{u} A})
    (Γ : {Γ : AlgCat.{u} R // Module.Finite R Γ ∧ IsAuslanderAlgebra Γ})
    (M : FGModuleCat.{u} A.val) (hM : IsAdditiveGenerator M) :
    auslanderCorrespondence R (Quotient.mk _ A) = Quotient.mk _ Γ ↔
      IsMoritaEquivalent R (Module.End A.val M.obj) Γ.val := by
  let N := chooseAdditiveGenerator R A
  have h : IsMoritaEquivalent R (Module.End A.val N.val.obj) (Module.End A.val M.obj) :=
    N.property.isMoritaEquivalent_moduleEnd R hM
  -- On representatives, the forward function is the quotient map of the chosen endomorphism
  -- algebra.
  have hq : auslanderCorrespondence R (Quotient.mk _ A) =
      Quotient.mk _ (endOfChosenAdditiveGenerator R A) := rfl
  rw [hq, Quotient.eq, moritaSetoid_rel_iff]
  exact ⟨fun he ↦ (h.symm R).trans R he, fun he ↦ h.trans R he⟩

end TauCeti
