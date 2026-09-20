/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Derivation.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Derivations on quotient algebras

A derivation of an associative algebra descends to a quotient by a two-sided ideal exactly when
it preserves that ideal. This file bundles the ideal-preserving derivations as a Lie subalgebra and
constructs the descent as a homomorphism of Lie algebras

`Der(A, I) → Der(A ⧸ I)`.

The Lie-algebra packaging records that sums, scalar multiples, and commutators of derivations
preserving `I` still preserve `I`. It lets a Lie algebra acting on `A` by derivations descend its
action to `A ⧸ I` as soon as stability of `I` has been proved. In particular, derivations of a
universal enveloping algebra can act on the finite quotients used to extend Lie representations.

## Main definitions

* `TauCeti.stableDerivations`: the Lie subalgebra of derivations preserving a fixed ideal.
* `TauCeti.derivationQuotientHom`: descent of stable derivations to the quotient algebra.
* `TauCeti.stableInnerDerivation`: every inner derivation preserves a two-sided ideal.
-/

public section

namespace TauCeti

attribute [local instance 100] LieRing.ofAssociativeRing

universe u v

variable (R : Type u) {A : Type v} [CommRing R] [Ring A] [Algebra R A]

/-- The derivations of `A` that preserve the ideal `I`, as a Lie subalgebra of `Der(A)`.

Closure under the Lie bracket follows because the commutator of two endomorphisms preserving a
submodule again preserves that submodule. -/
def stableDerivations (I : Ideal A) : LieSubalgebra R (derivationLieAlgebra R A) where
  carrier := {D | ∀ x ∈ I, (D : Module.End R A) x ∈ I}
  zero_mem' _ _ := I.zero_mem
  add_mem' hD hE x hx := I.add_mem (hD x hx) (hE x hx)
  smul_mem' r D hD x hx := by
    -- The nested Lie-subalgebra coercions hide the pointwise scalar action on the endomorphism.
    change r • (D : Module.End R A) x ∈ I
    rw [Algebra.smul_def]
    exact I.mul_mem_left _ (hD x hx)
  lie_mem' := by
    intro D E hD hE x hx
    -- The nested Lie-subalgebra coercions hide that this bracket is the commutator of
    -- endomorphisms.
    change (D : Module.End R A) ((E : Module.End R A) x) -
      (E : Module.End R A) ((D : Module.End R A) x) ∈ I
    exact I.sub_mem (hD _ (hE x hx)) (hE _ (hD x hx))

/-- Membership in `stableDerivations R I` means pointwise preservation of `I`. -/
@[simp]
theorem mem_stableDerivations (I : Ideal A) (D : derivationLieAlgebra R A) :
    D ∈ stableDerivations R I ↔ ∀ x ∈ I, (D : Module.End R A) x ∈ I :=
  Iff.rfl

section Quotient

variable (I : Ideal A) [I.IsTwoSided]

/-- Every inner derivation preserves a two-sided ideal. -/
theorem innerDerivation_mem_stableDerivations (z : A) :
    innerDerivation R z ∈ stableDerivations R I := by
  rw [mem_stableDerivations]
  intro x hx
  rw [show (innerDerivation R z : Module.End R A) x = z * x - x * z by
    simp only [coe_innerDerivation, LieAlgebra.ad_apply, Ring.lie_def]]
  exact I.sub_mem (I.mul_mem_left z hx) (I.mul_mem_right z hx)

/-- The inner derivation by `z`, regarded as a derivation preserving the two-sided ideal `I`. -/
def stableInnerDerivation (z : A) : stableDerivations R I :=
  ⟨innerDerivation R z, innerDerivation_mem_stableDerivations R I z⟩

/-- The stable inner derivation has the same underlying derivation as the ordinary inner
derivation. -/
@[simp]
theorem coe_stableInnerDerivation (z : A) :
    ((stableInnerDerivation R I z : derivationLieAlgebra R A) : Module.End R A) =
      (innerDerivation R z : Module.End R A) :=
  (rfl)

/-- A derivation preserving `I`, descended to the quotient algebra `A ⧸ I`.

This implementation helper is private because the public construction is the Lie homomorphism
`TauCeti.derivationQuotientHom`. -/
private noncomputable def quotientDerivation (D : stableDerivations R I) :
    derivationLieAlgebra R (A ⧸ I) := by
  let hD : I.restrictScalars R ≤ (I.restrictScalars R).comap (D : Module.End R A) := by
    intro x hx
    exact D.property x hx
  refine ⟨(I.restrictScalars R).mapQ (I.restrictScalars R) (D : Module.End R A) hD,
    mem_derivationLieAlgebra.mpr ?_⟩
  intro q₁ q₂
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mkₐ_surjective R I q₁
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mkₐ_surjective R I q₂
  -- `mapQ` and the quotient-ring multiplication obscure the representative-level Leibniz rule.
  change Ideal.Quotient.mk I ((D : Module.End R A) (x * y)) =
    Ideal.Quotient.mk I ((D : Module.End R A) x) * Ideal.Quotient.mk I y +
      Ideal.Quotient.mk I x * Ideal.Quotient.mk I ((D : Module.End R A) y)
  rw [derivationLieAlgebra.leibniz, map_add, map_mul, map_mul]

/-- A stable derivation acts on a quotient class by applying the derivation to a representative. -/
@[simp]
private theorem quotientDerivation_mk (D : stableDerivations R I) (x : A) :
    (quotientDerivation R I D : Module.End R (A ⧸ I)) (Ideal.Quotient.mk I x) =
      Ideal.Quotient.mk I ((D : Module.End R A) x) :=
  by
    simp only [quotientDerivation]
    exact Submodule.mapQ_apply (p := I.restrictScalars R) (q := I.restrictScalars R)
      (D : Module.End R A) x

/-- **Stable derivations descend to the quotient.** The assignment sending a derivation of `A`
that preserves the two-sided ideal `I` to its induced derivation of `A ⧸ I` is a homomorphism of
Lie algebras. -/
noncomputable def derivationQuotientHom :
    stableDerivations R I →ₗ⁅R⁆ derivationLieAlgebra R (A ⧸ I) where
  toFun := quotientDerivation R I
  map_add' D E := by
    apply derivationLieAlgebra.ext
    intro q
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective q
    -- Both nested subalgebra coercions reduce this to additivity of the quotient map.
    change Ideal.Quotient.mk I
        ((D : Module.End R A) x + (E : Module.End R A) x) =
      Ideal.Quotient.mk I ((D : Module.End R A) x) +
        Ideal.Quotient.mk I ((E : Module.End R A) x)
    exact map_add (Ideal.Quotient.mk I) _ _
  map_smul' r D := by
    apply derivationLieAlgebra.ext
    intro q
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective q
    -- Both nested subalgebra coercions reduce this to linearity of the quotient map.
    change Ideal.Quotient.mk I (r • (D : Module.End R A) x) =
      r • Ideal.Quotient.mk I ((D : Module.End R A) x)
    exact map_smul (Ideal.Quotient.mkₐ R I) r ((D : Module.End R A) x)
  map_lie' {D E} := by
    apply derivationLieAlgebra.ext
    intro q
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective q
    -- The Lie brackets on both derivation algebras are endomorphism commutators.
    change Ideal.Quotient.mk I
        ((D : Module.End R A) ((E : Module.End R A) x) -
          (E : Module.End R A) ((D : Module.End R A) x)) =
      (quotientDerivation R I D : Module.End R (A ⧸ I))
          (Ideal.Quotient.mk I ((E : Module.End R A) x)) -
        (quotientDerivation R I E : Module.End R (A ⧸ I))
          (Ideal.Quotient.mk I ((D : Module.End R A) x))
    rw [quotientDerivation_mk, quotientDerivation_mk, map_sub]

/-- The descended derivation evaluates on a quotient class by applying the original derivation to
a representative. -/
@[simp]
theorem derivationQuotientHom_apply_mk (D : stableDerivations R I) (x : A) :
    (derivationQuotientHom R I D : Module.End R (A ⧸ I)) (Ideal.Quotient.mk I x) =
      Ideal.Quotient.mk I ((D : Module.End R A) x) :=
  quotientDerivation_mk R I D x

/-- Descent commutes with the quotient map: applying a stable derivation before or after passing
to `A ⧸ I` gives the same result. -/
theorem derivationQuotientHom_comp_mkQ (D : stableDerivations R I) :
    (derivationQuotientHom R I D : Module.End R (A ⧸ I)).comp
        (I.restrictScalars R).mkQ =
      (I.restrictScalars R).mkQ.comp (D : Module.End R A) := by
  ext x
  exact derivationQuotientHom_apply_mk R I D x

/-- Descending the inner derivation by `z` gives the inner derivation by the image of `z` in the
quotient. -/
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
