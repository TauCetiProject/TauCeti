/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Derivation.Basic
public import Mathlib.Algebra.Lie.Quotient
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Derivations on quotient algebras

A derivation of an associative algebra descends to a quotient by a two-sided ideal exactly when
it preserves that ideal. This file constructs that descent, out of the Lie subalgebra
`TauCeti.stableDerivations` of derivations preserving the ideal, as a homomorphism of Lie algebras

`Der(A, I) → Der(A ⧸ I)`.

The Lie-algebra packaging records that sums, scalar multiples, and commutators of derivations
preserving `I` still preserve `I`. It lets a Lie algebra acting on `A` by derivations descend its
action to `A ⧸ I` as soon as stability of `I` has been proved. In particular, derivations of a
universal enveloping algebra can act on the finite quotients used to extend Lie representations.

## Main definitions

* `TauCeti.derivationQuotientHom`: descent of stable derivations to the quotient algebra.
* `TauCeti.stableInnerDerivation`: the inner derivations, as a homomorphism of Lie algebras into
  the derivations preserving a two-sided ideal.

## Implementation notes

The stabilizer `TauCeti.stableDerivations` of a submodule only uses the module structure of `A`,
so it belongs to the core derivation API alongside `derivationLieAlgebra`; this file specialises
it to `I.restrictScalars R` for a two-sided ideal `I`. Descent itself is Mathlib's action of a Lie
algebra on the quotient of a Lie module by a stable Lie submodule,
`LieSubmodule.Quotient.actionAsEndoMap`, with its codomain cut down to the derivations of `A ⧸ I`,
in the same way that `innerDerivation` cuts down `LieAlgebra.ad`.
-/

public section

namespace TauCeti

attribute [local instance 100] LieRing.ofAssociativeRing

universe u v

section Quotient

variable (R : Type u) {A : Type v} [CommRing R] [Ring A] [Algebra R A] (I : Ideal A)
  [I.IsTwoSided]

/-- Every inner derivation preserves a two-sided ideal. -/
theorem innerDerivation_mem_stableDerivations (z : A) :
    innerDerivation R z ∈ stableDerivations R (I.restrictScalars R) := by
  rw [mem_stableDerivations]
  intro x hx
  simp only [coe_innerDerivation, LieAlgebra.ad_apply, Ring.lie_def]
  exact I.sub_mem (I.mul_mem_left z hx) (I.mul_mem_right z hx)

/-- **The inner derivations preserve a two-sided ideal**: `innerDerivation` with its codomain cut
down to the derivations preserving `I`, as a homomorphism of Lie algebras. -/
def stableInnerDerivation : A →ₗ⁅R⁆ stableDerivations R (I.restrictScalars R) :=
  { (innerDerivation R).toLinearMap.codRestrict
      (stableDerivations R (I.restrictScalars R)).toSubmodule
      (innerDerivation_mem_stableDerivations R I) with
    map_lie' := fun {z w} => Subtype.ext ((innerDerivation R).map_lie z w) }

/-- The stable inner derivation has the same underlying derivation as the ordinary inner
derivation. -/
@[simp]
theorem coe_stableInnerDerivation (z : A) :
    (stableInnerDerivation R I z : derivationLieAlgebra R A) = innerDerivation R z :=
  (rfl)

/-- The action of a stable derivation on the quotient is a derivation. -/
-- The Leibniz rule on `A ⧸ I` is checked on representatives.
private theorem actionAsEndoMap_mem_derivationLieAlgebra
    (D : stableDerivations R (I.restrictScalars R)) :
    (LieSubmodule.Quotient.actionAsEndoMap
        (stableDerivations.lieSubmodule R (I.restrictScalars R)) D : Module.End R (A ⧸ I)) ∈
      derivationLieAlgebra R (A ⧸ I) := by
  refine mem_derivationLieAlgebra.mpr fun q₁ q₂ => ?_
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective q₁
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective q₂
  -- The quotient action and the quotient-ring multiplication obscure the representative-level
  -- Leibniz rule.
  change Ideal.Quotient.mk I ((D : Module.End R A) (x * y)) =
    Ideal.Quotient.mk I ((D : Module.End R A) x) * Ideal.Quotient.mk I y +
      Ideal.Quotient.mk I x * Ideal.Quotient.mk I ((D : Module.End R A) y)
  rw [derivationLieAlgebra.leibniz, map_add, map_mul, map_mul]

/-- **Stable derivations descend to the quotient.** The assignment sending a derivation of `A`
that preserves the two-sided ideal `I` to its induced derivation of `A ⧸ I`, as a homomorphism of
Lie algebras. -/
-- Mathlib's action of `Der(A, I)` on the quotient of the Lie module `A` by the stable Lie
-- submodule `I`, with its codomain cut down to the derivations.
def derivationQuotientHom :
    stableDerivations R (I.restrictScalars R) →ₗ⁅R⁆ derivationLieAlgebra R (A ⧸ I) :=
  { (LieSubmodule.Quotient.actionAsEndoMap
        (stableDerivations.lieSubmodule R (I.restrictScalars R))).toLinearMap.codRestrict
      (derivationLieAlgebra R (A ⧸ I)).toSubmodule (actionAsEndoMap_mem_derivationLieAlgebra R I)
      with
    map_lie' := fun {D E} => Subtype.ext
      ((LieSubmodule.Quotient.actionAsEndoMap
        (stableDerivations.lieSubmodule R (I.restrictScalars R))).map_lie D E) }

/-- Descent commutes with the quotient map: applying a stable derivation before or after passing
to `A ⧸ I` gives the same result. -/
theorem derivationQuotientHom_comp_mkQ (D : stableDerivations R (I.restrictScalars R)) :
    (derivationQuotientHom R I D : Module.End R (A ⧸ I)).comp
        (I.restrictScalars R).mkQ =
      (I.restrictScalars R).mkQ.comp (D : Module.End R A) := by
  -- Stability of `I` in the form `Submodule.mapQ` asks for; proof irrelevance identifies it with
  -- the membership proof `D.property` that the definition actually carries.
  have hD : I.restrictScalars R ≤ Submodule.comap
      (LieModule.toEnd R (stableDerivations R (I.restrictScalars R)) A D)
      (I.restrictScalars R) := fun x hx => (mem_stableDerivations R _ _).mp D.property x hx
  -- Unfold only the underlying quotient map: Mathlib's `Submodule.mapQ` along the action of `D`.
  change ((I.restrictScalars R).mapQ (I.restrictScalars R)
    (LieModule.toEnd R (stableDerivations R (I.restrictScalars R)) A D) hD).comp
      (I.restrictScalars R).mkQ = _
  exact Submodule.mapQ_mkQ (p := I.restrictScalars R) (q := I.restrictScalars R) _

/-- The descended derivation evaluates on a quotient class by applying the original derivation to
a representative. -/
@[simp]
theorem derivationQuotientHom_apply_mk (D : stableDerivations R (I.restrictScalars R)) (x : A) :
    (derivationQuotientHom R I D : Module.End R (A ⧸ I)) (Ideal.Quotient.mk I x) =
      Ideal.Quotient.mk I ((D : Module.End R A) x) :=
  LinearMap.congr_fun (derivationQuotientHom_comp_mkQ R I D) x

/-- Descending the inner derivation by `z` gives the inner derivation by the image of `z` in the
quotient. -/
@[simp]
theorem derivationQuotientHom_stableInnerDerivation (z : A) :
    derivationQuotientHom R I (stableInnerDerivation R I z) =
      innerDerivation R (Ideal.Quotient.mk I z) := by
  apply derivationLieAlgebra.ext
  intro q
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective q
  rw [derivationQuotientHom_apply_mk]
  simp only [coe_stableInnerDerivation, coe_innerDerivation, LieAlgebra.ad_apply,
    Ring.lie_def]
  rw [map_sub, map_mul, map_mul]

end Quotient

end TauCeti
