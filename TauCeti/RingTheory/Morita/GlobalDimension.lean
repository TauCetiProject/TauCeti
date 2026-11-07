/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Morita.Matrix
public import TauCeti.Algebra.Homology.Ext.Equivalence
public import TauCeti.RingTheory.GlobalDimension

/-!
# Morita invariance of the global dimension

The global dimension of a ring is the supremum of the projective dimensions of its modules, and
projective dimension is defined by the vanishing of `Ext`. An equivalence of module categories
identifies the `Ext` groups, so it preserves projective dimension
(`CategoryTheory.Equivalence.projectiveDimension_functor_obj`) and hence the global dimension.
Mathlib's `IsMoritaEquivalent R A B` provides such an equivalence in the universe `max u₁ u₂`,
and the global dimension does not depend on the universe of the modules
(`TauCeti.globalDimension_eq_globalDimension`), so Morita equivalent algebras have the same global
dimension in every universe in which both are small.

## Main results

* `TauCeti.globalDimension_eq_of_equivalence`: rings with equivalent module categories have the
  same global dimension.
* `IsMoritaEquivalent.globalDimension_eq`: Morita equivalent algebras have the same global
  dimension.
* `TauCeti.globalDimension_matrix`: a matrix ring has the global dimension of its coefficients.

## References

* M. Auslander, I. Reiten and S. O. Smalø, *Representation theory of Artin algebras*, Cambridge
  Studies in Advanced Mathematics 36 (1995), Section II.2.
-/

public section

universe v u u' u₁ u₂

open CategoryTheory

namespace TauCeti

/-- **Rings with equivalent module categories have the same global dimension.** No linearity of
the equivalence is needed: an equivalence of module categories is automatically additive. -/
theorem globalDimension_eq_of_equivalence {R : Type u} [Ring R] {S : Type u'} [Ring S]
    (e : ModuleCat.{v} R ≌ ModuleCat.{v} S) : globalDimension.{v} R = globalDimension.{v} S := by
  have := e.functor.additive_of_preserves_binary_products
  refine le_antisymm ((globalDimension_le_iff R _).mpr fun M ↦ ?_)
    ((globalDimension_le_iff S _).mpr fun N ↦ ?_)
  · rw [← e.projectiveDimension_functor_obj M]
    exact ModuleCat.projectiveDimension_le_globalDimension _
  · have hN : projectiveDimension (e.functor.obj (e.inverse.obj N)) = projectiveDimension N :=
      projectiveDimension_eq_of_iso (e.counitIso.app N)
    rw [← hN, e.projectiveDimension_functor_obj]
    exact ModuleCat.projectiveDimension_le_globalDimension _

/-- **Morita equivalent algebras have the same global dimension**, computed with modules in any
universe in which both algebras are small. -/
theorem _root_.IsMoritaEquivalent.globalDimension_eq {R : Type*} [CommSemiring R]
    {A : Type u₁} [Ring A] [Algebra R A] {B : Type u₂} [Ring B] [Algebra R B]
    [Small.{v} A] [Small.{v} B] (h : IsMoritaEquivalent R A B) :
    globalDimension.{v} A = globalDimension.{v} B := by
  obtain ⟨e⟩ := h.cond
  rw [globalDimension_eq_globalDimension.{v, max u₁ u₂} A,
    globalDimension_eq_globalDimension.{v, max u₁ u₂} B]
  exact globalDimension_eq_of_equivalence e.eqv

/-- **A matrix ring has the global dimension of its coefficients.** -/
@[simp]
theorem globalDimension_matrix {A : Type u} [Ring A] (ι : Type u') [Fintype ι] [DecidableEq ι]
    [Nonempty ι] [Small.{v} A] :
    globalDimension.{v} (Matrix ι ι A) = globalDimension.{v} A :=
  have : Small.{v} (Matrix ι ι A) := inferInstanceAs (Small.{v} (ι → ι → A))
  (IsMoritaEquivalent.matrix A ℤ).globalDimension_eq.symm

end TauCeti
