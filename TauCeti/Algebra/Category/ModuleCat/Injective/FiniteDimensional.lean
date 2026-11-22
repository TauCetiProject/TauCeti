/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Injective
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RingTheory.Artinian.Ring
import TauCeti.Algebra.Category.ModuleCat.Algebra
import TauCeti.RingTheory.MatlisDuality.ArtinAlgebra
import Mathlib.RingTheory.Finiteness.Small

/-!
# Finite injective presentations over Artin algebras

Every finitely generated module over an Artin algebra, an algebra finitely generated as a module
over a commutative Artinian ring, embeds into a finitely generated ambient injective module. The
injective term stays in the universe of the original module, provided the algebra is small there;
over a finite-dimensional algebra this smallness is automatic for a nonzero module.

This packages `TauCeti.exists_isInjectiveEnvelope_finite` as Mathlib's `InjectivePresentation`.
Such presentations let finite-dimensional subcategories test injectivity against ambient
injectives without leaving the subcategory.

## Main results

* `ModuleCat.exists_injectivePresentation_finite_of_isArtinianRing`: over an Artin algebra.
* `ModuleCat.exists_injectivePresentation_of_finite`: over a finite-dimensional algebra.

## References

* I. Assem, D. Simson, A. Skowroński, *Elements of the Representation Theory of Associative
  Algebras*, Vol. 1, Section I.5.
* M. Auslander, I. Reiten, S. O. Smalø, *Representation Theory of Artin Algebras*, Cambridge
  University Press (1995), Section II.4.
-/

public section

namespace ModuleCat

open CategoryTheory

universe u v w

section Artin

variable (R : Type u) {A : Type v} [CommRing R] [IsArtinianRing R] [Ring A] [Algebra R A]
  [Module.Finite R A]

include R in
/-- A finitely generated module over an Artin algebra has an ambient injective presentation with
finitely generated target, in the same universe as the source when the algebra is small there. -/
theorem exists_injectivePresentation_finite_of_isArtinianRing [Small.{w} A]
    (M : ModuleCat.{w} A) [Module.Finite A M] :
    ∃ I : InjectivePresentation M, Module.Finite A I.J := by
  let : Module R M := moduleOfAlgebra R M
  have := isScalarTower_moduleOfAlgebra R M
  obtain ⟨Q, _, _, _, i, hi⟩ := TauCeti.exists_isInjectiveEnvelope_finite R (A := A) M
  have : Small.{w} Q := Module.Finite.small A Q
  let e := Shrink.linearEquiv A Q
  have : Module.Finite A (Shrink.{w} Q) := Module.Finite.equiv e.symm
  have : Module.Injective A (Shrink.{w} Q) :=
    ((Module.Baer.of_injective hi.moduleInjective).of_equiv e.symm).injective
  let f : M ⟶ ModuleCat.of A (Shrink.{w} Q) :=
    ModuleCat.ofHom (e.symm.toLinearMap.comp i)
  have : Mono f := (ModuleCat.mono_iff_injective f).mpr
    (e.symm.injective.comp hi.injective)
  exact ⟨{
    J := ModuleCat.of A (Shrink.{w} Q)
    injective := Module.injective_object_of_injective_module A (Shrink.{w} Q)
    f := f }, inferInstance⟩

end Artin

variable (k : Type u) {A : Type v} [Field k] [Ring A] [Algebra k A]
  [FiniteDimensional k A]

include k in
/-- A finitely generated module over a finite-dimensional algebra has an ambient injective
presentation with finitely generated target, in the same universe as the source. -/
theorem exists_injectivePresentation_of_finite (M : ModuleCat.{w} A) [Module.Finite A M] :
    ∃ I : InjectivePresentation M, Module.Finite A I.J := by
  rcases subsingleton_or_nontrivial M with hM | hM
  · exact ⟨{ J := M, injective := (isZero_of_subsingleton M).injective, f := 𝟙 M }, inferInstance⟩
  obtain ⟨m, hm⟩ := exists_ne (0 : M)
  have : Small.{w} A := by
    have : Small.{w} k := by
      let : Module k M := Module.compHom M (algebraMap k A)
      exact small_of_injective (smul_left_injective k hm)
    exact Module.Finite.small k A
  exact exists_injectivePresentation_finite_of_isArtinianRing k M

end ModuleCat
