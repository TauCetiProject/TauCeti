/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Finiteness.Projective
public import Mathlib.RingTheory.Morita.Matrix
public import TauCeti.Algebra.Category.ModuleCat.Equivalence
public import TauCeti.RingTheory.DominantDimension

/-!
# Morita invariance of the dominant dimension

An equivalence `e : ModuleCat A ≌ ModuleCat B` preserves the dominant dimension of objects
(`CategoryTheory.Functor.dominantDimension_obj`), but it carries the regular module `A` to a
progenerator of `B`, not to `B` itself. The regular module `B` corresponds to a finitely
generated projective `A`-module, a retract of a finite power `Aᵏ`; so `B` is a retract of the
image of `Aᵏ`, whose dominant dimension is that of `Aᵏ`, at least that of `A`
(`ModuleCat.dominantDimension_pi`). By symmetry the two rings have the same dominant dimension
(`CategoryTheory.Equivalence.dominantDimension_eq`). No finiteness of the rings is needed, and the
equivalence need not be linear.

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

universe u u'

open CategoryTheory TauCeti

namespace TauCeti

/-- One inequality of `CategoryTheory.Equivalence.dominantDimension_eq`. -/
private theorem dominantDimension_le_of_equivalence {A : Type u} [Ring A] {B : Type u'} [Ring B]
    (e : ModuleCat.{u} A ≌ ModuleCat.{u'} B) : dominantDimension A ≤ dominantDimension B := by
  -- The `A`-module `Q` corresponding to `B` is a retract of a finite power `Aᵏ`.
  let Q := e.inverse.obj (ModuleCat.of B B)
  have : Module.Finite A Q := (e.symm.finite_functor_obj_iff _).2 inferInstance
  have : Module.Projective A Q := (e.symm.projective_functor_obj_iff _).2 inferInstance
  obtain ⟨k, f, s, -, -, hs⟩ := Module.Finite.exists_comp_eq_id_of_projective A Q
  let r : Retract Q (ModuleCat.of A (Fin k → A)) :=
    ⟨ModuleCat.ofHom s, ModuleCat.ofHom f, by ext x; exact congr($hs x)⟩
  rw [dominantDimension_eq_dominantDimension_of, dominantDimension_eq_dominantDimension_of]
  calc CategoryTheory.dominantDimension (ModuleCat.of A A)
      ≤ CategoryTheory.dominantDimension (ModuleCat.of A (Fin k → ModuleCat.of A A)) := by
        rw [ModuleCat.dominantDimension_pi]
        exact le_iInf fun _ ↦ le_rfl
    _ = CategoryTheory.dominantDimension (e.functor.obj (ModuleCat.of A (Fin k → A))) :=
        (e.functor.dominantDimension_obj _).symm
    _ ≤ CategoryTheory.dominantDimension (e.functor.obj Q) := (r.map e.functor).dominantDimension_le
    _ = CategoryTheory.dominantDimension (ModuleCat.of B B) :=
        dominantDimension_eq_of_iso (e.counitIso.app _)

/-- **Rings with equivalent module categories have the same dominant dimension.** The regular
module of each ring corresponds to a retract of a finite power of the regular module of the
other. The two module categories may live in different universes. -/
theorem _root_.CategoryTheory.Equivalence.dominantDimension_eq {A : Type u} [Ring A] {B : Type u'}
    [Ring B] (e : ModuleCat.{u} A ≌ ModuleCat.{u'} B) :
    dominantDimension A = dominantDimension B :=
  le_antisymm (dominantDimension_le_of_equivalence e) (dominantDimension_le_of_equivalence e.symm)

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
