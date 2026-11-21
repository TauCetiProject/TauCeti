/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import TauCeti.Algebra.Module.Injective.Envelope.Basic
import TauCeti.RingTheory.MatlisDuality.ArtinAlgebra

/-!
# Finite-dimensional injective envelopes

Every finite-dimensional module over a finite-dimensional algebra has a finite-dimensional
injective envelope. No algebraic closedness or self-injectivity is required. The result also
applies to finitely generated modules, with their base-field action induced from the algebra.

A finite-dimensional algebra over a field is an Artin algebra, so this is the field case of
`TauCeti.exists_isInjectiveEnvelope_finite`.

## References

* I. Assem, D. Simson, A. Skowroński, *Elements of the Representation Theory of Associative
  Algebras*, Vol. 1, Section I.5.
-/

public section

namespace TauCeti

universe u v w

variable {k : Type u} [Field k] {A : Type v} [Ring A] [Algebra k A]
  [FiniteDimensional k A] (M : Type w) [AddCommGroup M] [Module A M]

/-- Every finite-dimensional module over a finite-dimensional algebra has an injective envelope
which is finite-dimensional over the same field. The envelope can be taken in the universe of
the field and algebra, independently of the universe of the original module. -/
theorem exists_isInjectiveEnvelope_finiteDimensional [Module k M] [IsScalarTower k A M]
    [FiniteDimensional k M] :
    ∃ (Q : Type max u v) (_ : AddCommGroup Q) (_ : Module A Q) (_ : Module k Q)
      (_ : IsScalarTower k A Q) (_ : FiniteDimensional k Q) (i : M →ₗ[A] Q),
      IsInjectiveEnvelope i := by
  have : Module.Finite A M := Module.Finite.of_restrictScalars_finite k A M
  obtain ⟨Q, _, _, _, i, hi⟩ := exists_isInjectiveEnvelope_finite k (A := A) M
  let : Module k Q := Module.compHom Q (algebraMap k A)
  let : IsScalarTower k A Q := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  exact ⟨Q, _, _, _, ‹_›, Module.Finite.trans A Q, i, hi⟩

/-- Every finitely generated module over a finite-dimensional algebra has a finite-dimensional
injective envelope. The field action on the source is induced through the algebra map. -/
theorem exists_isInjectiveEnvelope_of_finite [Module.Finite A M] :
    ∃ (Q : Type max u v) (_ : AddCommGroup Q) (_ : Module A Q) (_ : Module k Q)
      (_ : IsScalarTower k A Q) (_ : FiniteDimensional k Q) (i : M →ₗ[A] Q),
      IsInjectiveEnvelope i := by
  let : Module k M := Module.compHom M (algebraMap k A)
  let : IsScalarTower k A M := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let : FiniteDimensional k M := Module.Finite.trans A M
  exact exists_isInjectiveEnvelope_finiteDimensional M

end TauCeti
