/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import TauCeti.Algebra.Module.Injective.Envelope.FiniteLength
import TauCeti.Algebra.Module.Injective.Dual
public import TauCeti.LinearAlgebra.Dual.Cogenerator
import TauCeti.LinearAlgebra.Dual.RightAction

/-!
# Finite-dimensional injective envelopes

Every finite-dimensional module over a finite-dimensional algebra has a finite-dimensional
injective envelope. No algebraic closedness or self-injectivity is required. The result also
applies to finitely generated modules, with their base-field action induced from the algebra.

Finite powers of the dual of the right regular module provide finite-dimensional injective
ambient modules. Restricting an embedding into one of these yields an envelope, so its
uniqueness follows from the general injective-envelope API.

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
  -- The left action on the dual of the right regular module is precomposition.
  let : Module A (Module.Dual k A) := Module.compHom _ (dualRightAction k A)
  have hsmul (a : A) (φ : Module.Dual k A) (x : A) : (a • φ) x = φ (x * a) :=
    (dualRightAction_apply_apply k A a φ x).trans (by rw [op_smul_eq_mul])
  let : IsScalarTower k A (Module.Dual k A) := IsScalarTower.of_algebraMap_smul fun c φ => by
    ext x
    rw [hsmul, ← Algebra.commutes, ← Algebra.smul_def]
    simp
  let : Module.Injective A (Module.Dual k A) :=
    moduleInjective_of_equiv_dual_regular k (LinearEquiv.refl k _) hsmul
  obtain ⟨n, f, hf⟩ := (LinearEquiv.refl k _).exists_injective_linearMap_pi_of_dual hsmul M
  let : Module.Injective A (Fin n → Module.Dual k A) := Module.Injective.pi A _
  let : IsArtinian A (Fin n → Module.Dual k A) := isArtinian_of_tower k inferInstance
  let : IsNoetherian A (Fin n → Module.Dual k A) := isNoetherian_of_tower k inferInstance
  obtain ⟨P, hP, hp⟩ := exists_isInjectiveEnvelope_submodule A f hf
  let : FiniteDimensional k P :=
    Module.Finite.of_injective (P.subtype.restrictScalars k) P.injective_subtype
  exact ⟨P, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, _, hp⟩

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
