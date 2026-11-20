/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Injective
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import TauCeti.Algebra.Module.Injective.Envelope.FiniteDimensional
import Mathlib.RingTheory.Finiteness.Small

/-!
# Finite injective presentations over finite-dimensional algebras

Every finitely generated module over a finite-dimensional algebra embeds into a finitely
generated ambient injective module. The injective term stays in the universe of the original
module.

This packages `TauCeti.exists_isInjectiveEnvelope_of_finite` as Mathlib's
`InjectivePresentation`. Such presentations let finite-dimensional subcategories test
injectivity against ambient injectives without leaving the subcategory.

## References

* I. Assem, D. Simson, A. Skowroński, *Elements of the Representation Theory of Associative
  Algebras*, Vol. 1, Section I.5.
-/

public section

namespace ModuleCat

open CategoryTheory

universe u v w

variable (k : Type u) {A : Type v} [Field k] [Ring A] [Algebra k A]
  [FiniteDimensional k A]

include k in
/-- A finitely generated module over a finite-dimensional algebra has an ambient injective
presentation with finitely generated target, in the same universe as the source. -/
theorem exists_injectivePresentation_of_finite (M : ModuleCat.{w} A) [Module.Finite A M] :
    ∃ I : InjectivePresentation M, Module.Finite A I.J := by
  classical
  rcases subsingleton_or_nontrivial M with hM | hM
  · exact ⟨{ J := M, injective := (isZero_of_subsingleton M).injective, f := 𝟙 M }, inferInstance⟩
  obtain ⟨m, hm⟩ := exists_ne (0 : M)
  have : Small.{w} A := by
    have : Small.{w} k := by
      let : Module k M := Module.compHom M (algebraMap k A)
      exact small_of_injective (smul_left_injective k hm)
    exact Module.Finite.small k A
  obtain ⟨Q, _, _, _, _, _, i, hi⟩ :=
    TauCeti.exists_isInjectiveEnvelope_of_finite (k := k) (A := A) M
  have : Module.Finite A Q := Module.Finite.of_restrictScalars_finite k A Q
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

end ModuleCat
