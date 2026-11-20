/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Morita.Matrix
public import TauCeti.Algebra.Category.ModuleCat.Generator
public import TauCeti.RingTheory.DominantDimension

/-!
# Morita invariance of the dominant dimension

A **progenerator** `P` of a ring `Γ`, a finitely generated projective generator, has the dominant
dimension of `Γ` (`ModuleCat.dominantDimension_eq_of_isGenerator`). Indeed each of `P` and `Γ` is a
retract of a finite power of the other (`ModuleCat.exists_retract_pi_of_isGenerator_of_projective`),
a finite power has at least the dominant dimension of its factor, with equality for a nonempty
power (`ModuleCat.dominantDimension_pi`), and a retract has at least the dominant dimension of the
ambient object (`CategoryTheory.Retract.dominantDimension_le`).

An equivalence `e : ModuleCat A ≌ ModuleCat B` preserves the dominant dimension of objects
(`CategoryTheory.Functor.dominantDimension_obj`) and carries the regular module `A` to a
progenerator of `B` (`CategoryTheory.Equivalence.isGenerator_functor_obj_self`). So the two rings
have the same dominant dimension (`CategoryTheory.Equivalence.dominantDimension_eq`). No finiteness
of the rings is needed, and the equivalence need not be linear.

## Main results

* `ModuleCat.dominantDimension_eq_of_isGenerator`: a progenerator of `Γ` has the dominant dimension
  of `Γ`.
* `CategoryTheory.Equivalence.dominantDimension_eq`: rings with equivalent module categories have
  the same dominant dimension.
* `RingEquiv.dominantDimension_eq`: isomorphic rings have the same dominant dimension.
* `IsMoritaEquivalent.dominantDimension_eq`: **Morita equivalent algebras have the same dominant
  dimension.**
* `TauCeti.dominantDimension_matrix`: a matrix ring has the dominant dimension of its coefficients.

## References

* M. Auslander, I. Reiten, S. O. Smalø, *Representation Theory of Artin Algebras*, Cambridge
  Studies in Advanced Mathematics 36, CUP (1995), §II.2 and §VI.5.
-/

public section

universe u u'

open CategoryTheory TauCeti

/-- **The dominant dimension of a progenerator.** A finitely generated projective generator `P` of
`Γ` has the dominant dimension of `Γ`: each of `P` and `Γ` is a retract of a finite power of the
other, and a finite power has at least the dominant dimension of its factor. -/
theorem ModuleCat.dominantDimension_eq_of_isGenerator {Γ : Type u} [Ring Γ] (P : ModuleCat.{u} Γ)
    [Module.Finite Γ P] [Module.Projective Γ P] [Module.IsGenerator Γ P] :
    CategoryTheory.dominantDimension P = dominantDimension Γ := by
  have key (X : ModuleCat.{u} Γ) (n : ℕ) : CategoryTheory.dominantDimension X ≤
      CategoryTheory.dominantDimension (ModuleCat.of Γ (Fin n → X)) := by
    rw [ModuleCat.dominantDimension_pi]
    exact le_iInf fun _ ↦ le_rfl
  obtain ⟨m, ⟨r⟩⟩ := ModuleCat.exists_retract_pi_of_projective P
  obtain ⟨n, ⟨r'⟩⟩ :=
    ModuleCat.exists_retract_pi_of_isGenerator_of_projective P (ModuleCat.of Γ Γ)
  rw [dominantDimension_eq_dominantDimension_of]
  exact le_antisymm ((key P n).trans r'.dominantDimension_le)
    ((key (ModuleCat.of Γ Γ) m).trans r.dominantDimension_le)

namespace TauCeti

/-- **Rings with equivalent module categories have the same dominant dimension.** The equivalence
carries the regular module of `A` to a progenerator of `B`, which has the dominant dimension of `B`.
The two module categories may live in different universes. -/
theorem _root_.CategoryTheory.Equivalence.dominantDimension_eq {A : Type u} [Ring A] {B : Type u'}
    [Ring B] (e : ModuleCat.{u} A ≌ ModuleCat.{u'} B) :
    dominantDimension A = dominantDimension B :=
  ((dominantDimension_eq_dominantDimension_of A).trans
    (e.functor.dominantDimension_obj (ModuleCat.of A A)).symm).trans
    (ModuleCat.dominantDimension_eq_of_isGenerator _)

/-- **Isomorphic rings have the same dominant dimension.** -/
theorem _root_.RingEquiv.dominantDimension_eq {A B : Type u} [Ring A] [Ring B] (e : A ≃+* B) :
    dominantDimension A = dominantDimension B :=
  (ModuleCat.restrictScalarsEquivalenceOfRingEquiv e).dominantDimension_eq.symm

/-- **Morita equivalent algebras have the same dominant dimension.** -/
theorem _root_.IsMoritaEquivalent.dominantDimension_eq {R : Type*} [CommSemiring R] {A B : Type u}
    [Ring A] [Ring B] [Algebra R A] [Algebra R B] (h : IsMoritaEquivalent R A B) :
    dominantDimension A = dominantDimension B :=
  h.cond.some.eqv.dominantDimension_eq

/-- **A matrix ring has the dominant dimension of its coefficients.** -/
@[simp]
theorem dominantDimension_matrix {A : Type u} [Ring A] (ι : Type u) [Fintype ι] [DecidableEq ι]
    [Nonempty ι] : dominantDimension (Matrix ι ι A) = dominantDimension A :=
  (IsMoritaEquivalent.matrix A ℤ).dominantDimension_eq.symm

end TauCeti
