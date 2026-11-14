/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Morita.Matrix
public import TauCeti.Algebra.Category.FGModuleCat.Equivalence
public import TauCeti.Algebra.Category.ModuleCat.CartanMap.Morita
public import TauCeti.Algebra.Category.ModuleCat.Equivalence
public import TauCeti.Algebra.Category.ModuleCat.Generator
public import TauCeti.Algebra.Category.ModuleCat.Projective.Basic
public import TauCeti.RingTheory.DominantDimension

/-!
# Morita invariance of the dominant dimension

An equivalence `e : ModuleCat A ≌ ModuleCat B` preserves the dominant dimension of objects
(`CategoryTheory.Equivalence.dominantDimension_functor_obj`), but it carries the regular module `A`
to a progenerator `P` of `B`, not to `B` itself. The dominant dimension of a module only goes up
under retracts and finite powers (`CategoryTheory.Retract.dominantDimension_le`,
`ModuleCat.dominantDimension_le_dominantDimension_pi`). Since `B` is a retract of a finite power of
the generator `P` (`ModuleCat.exists_retract_pi_of_isGenerator`), and `P` is a retract of a finite
power of `B` (`ModuleCat.exists_retract_pi_of_finite_projective`), the two have the same dominant
dimension (`CategoryTheory.Equivalence.dominantDimension_eq`). No finiteness of the rings is needed,
and the equivalence need not be linear.

## Main results

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

universe u

open CategoryTheory TauCeti

namespace TauCeti

/-- **Rings with equivalent module categories have the same dominant dimension.** The equivalence
carries the regular module to a finitely generated projective generator `P`; `B` is a retract of a
finite power of `P` and `P` of a finite power of `B`. -/
theorem _root_.CategoryTheory.Equivalence.dominantDimension_eq {A B : Type u} [Ring A] [Ring B]
    (e : ModuleCat.{u} A ≌ ModuleCat.{u} B) :
    dominantDimension A = dominantDimension B := by
  let P : ModuleCat.{u} B := e.functor.obj (ModuleCat.of A A)
  have hdd : dominantDimension A = CategoryTheory.dominantDimension P := by
    rw [dominantDimension_eq_dominantDimension_of]
    exact (e.dominantDimension_functor_obj _).symm
  have : Module.Finite B P := (e.finite_functor_obj_iff _).2 inferInstance
  have : Module.Projective B P := (e.projective_functor_obj_iff _).2 inferInstance
  have : Module.IsGenerator B P :=
    (congrArg (fun X : ModuleCat.{u} B ↦ Module.IsGenerator B X)
      (e.finiteModulesEquivalence_functor_obj_obj (FGModuleCat.of A A))).mp
      e.finiteModulesEquivalence.isGenerator_functor_obj_regular
  rw [hdd, dominantDimension_eq_dominantDimension_of]
  refine le_antisymm ?_ ?_
  · obtain ⟨n, ⟨r⟩⟩ := ModuleCat.exists_retract_pi_of_isGenerator P
    exact (ModuleCat.dominantDimension_le_dominantDimension_pi P n).trans r.dominantDimension_le
  · obtain ⟨k, ⟨r⟩⟩ := ModuleCat.exists_retract_pi_of_finite_projective P
    exact (ModuleCat.dominantDimension_le_dominantDimension_pi (ModuleCat.of B B) k).trans
      r.dominantDimension_le

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
