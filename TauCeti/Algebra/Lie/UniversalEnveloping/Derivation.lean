/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.DualNumber
public import Mathlib.Algebra.Lie.Derivation.Basic
public import TauCeti.Algebra.Lie.Derivation
public import TauCeti.Algebra.Lie.UniversalEnveloping.Basic

/-!
# Lifting a Lie derivation to the enveloping algebra

A derivation `D` of a Lie algebra `L` extends uniquely to a derivation `Dᵁ` of the associative
algebra `U(L)`, characterised by `Dᵁ (ι x) = ι (D x)` on the canonical Lie generators.  This file
constructs that extension and identifies the assignment `D ↦ Dᵁ` as a homomorphism of Lie algebras
into the derivation algebra of `U(L)`.

## The construction

Nothing but the universal property of `U(L)` is used.  Write `A[ε] = A ⊕ Aε` for the dual numbers
over an algebra `A` (Mathlib's `DualNumber`, the square-zero extension of `A` by itself), and send

`x ↦ ι x + ε · ι (D x) : L → U(L)[ε]`.

The Leibniz rule `D ⁅x, y⁆ = ⁅x, D y⁆ + ⁅D x, y⁆` says exactly that this map is a homomorphism of
Lie algebras, because the `ε`-component of a commutator in `A[ε]` is the sum of the two
commutators obtained by differentiating one factor at a time.  So it lifts to an algebra
homomorphism `F : U(L) → U(L)[ε]`; its `1`-component is an algebra endomorphism of `U(L)` fixing
the generators, hence the identity, and multiplicativity of `F` then reads, on `ε`-components, as
the associative Leibniz rule for `a ↦ (F a).snd`.  That map is `Dᵁ`.

The extension is unique because the canonical generators generate `U(L)` as an *algebra*
(`TauCeti.UniversalEnvelopingAlgebra.adjoin_range_ι`) and the elements on which two derivations
agree are closed under products and contain the scalars; this is
`TauCeti.UniversalEnvelopingAlgebra.derivation_ext`, and it is what makes `D ↦ Dᵁ` additive,
`R`-linear and bracket-preserving without any further computation.

## Main definitions

* `TauCeti.UniversalEnvelopingAlgebra.envelopingDerivation`: the derivation `Dᵁ` of `U(L)`
  extending a Lie derivation `D` of `L`, as an element of the derivation Lie algebra
  `TauCeti.derivationLieAlgebra R (U L)`.
* `TauCeti.UniversalEnvelopingAlgebra.envelopingDerivationHom`: the assignment `D ↦ Dᵁ`, as a
  homomorphism of Lie algebras `LieDerivation R L L →ₗ⁅R⁆ Der (U L)`.

## Main results

* `TauCeti.UniversalEnvelopingAlgebra.derivation_ext`: **two derivations of `U(L)` agreeing on the
  canonical Lie generators are equal.**
* `TauCeti.UniversalEnvelopingAlgebra.envelopingDerivation_ι`: **the extension property**
  `Dᵁ (ι x) = ι (D x)`, with
  `TauCeti.UniversalEnvelopingAlgebra.envelopingDerivation_ι'` its `simp`-normal form.
* `TauCeti.UniversalEnvelopingAlgebra.envelopingDerivation_mul`: **the associative Leibniz rule**
  `Dᵁ (a * b) = Dᵁ a * b + a * Dᵁ b`.
* `TauCeti.UniversalEnvelopingAlgebra.envelopingDerivation_inner`: the extension of an inner
  derivation of `L` is the inner derivation of `U(L)` at the corresponding generator, so the
  construction is compatible with the adjoint action.

## Implementation notes

`envelopingDerivation` is valued in the bundled derivation algebra
`TauCeti.derivationLieAlgebra R (U L)` of `TauCeti/Algebra/Lie/Derivation.lean` rather than in the
bare `U L →ₗ[R] U L`: that is the noncommutative derivation API this construction is meant to be
read in (Mathlib's `Derivation` needs a commutative algebra, and `LieDerivation` needs a Lie
bracket, so neither applies to `U(L)`).  The bundling is also what lets `D ↦ Dᵁ` be a `LieHom`,
since the target is a Lie algebra on the nose.

`TauCeti.UniversalEnvelopingAlgebra.envelopingDerivation_mul` is deliberately *not* a `simp` lemma:
the generic `TauCeti.derivationLieAlgebra.leibniz` already is one and already rewrites that
left-hand side, so the `simpNF` linter rejects the tag with "simp can prove this: by simp only [*,
@TauCeti.derivationLieAlgebra.leibniz]".  The lemma is stated all the same, because the Leibniz
rule is the defining property of the extension and a user should not have to reach for the generic
bundled-derivation API to find it.

No lemma with `UniversalEnvelopingAlgebra.ι` on the left-hand side is a `simp` lemma here, for the
reason recorded in `TauCeti/Algebra/Lie/UniversalEnveloping/Basic.lean`: `simp` rewrites `ι` through
Mathlib's `UniversalEnvelopingAlgebra.ι_apply`, so such a left-hand side is not in simp-normal
form.  The primed variants are the simp-normal ones.

## References

* [The Ado--Iwasawa roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/AdoIwasawa/README.md),
  whose derivation-lift targets these are.
* N. Jacobson, *Lie Algebras* (1962), Chapter V, §4.
* J. Dixmier, *Enveloping Algebras*, North-Holland (1977), §2.4.
-/

public section

namespace TauCeti

-- Mathlib does not register the Lie ring of an associative ring as a global instance; the
-- commutator of two elements of an enveloping algebra and of its dual numbers is written with it.
attribute [local instance 100] LieRing.ofAssociativeRing

namespace UniversalEnvelopingAlgebra

universe u v

variable (R : Type u) (L : Type v) [CommRing R] [LieRing L] [LieAlgebra R L]

local notation "U" => _root_.UniversalEnvelopingAlgebra R L

/-! ### Uniqueness of an extension -/

/-- **A derivation of `U(L)` is determined by its values on the canonical Lie generators.** -/
theorem derivation_ext {D E : derivationLieAlgebra R U}
    (h : ∀ x : L, (D : Module.End R U) (_root_.UniversalEnvelopingAlgebra.ι R x)
      = (E : Module.End R U) (_root_.UniversalEnvelopingAlgebra.ι R x)) : D = E := by
  -- The elements on which `D` and `E` agree contain the scalars (a derivation of a unital algebra
  -- kills the unit) and are closed under sums and products (by the Leibniz rule), so they form a
  -- subalgebra; the canonical generators generate `U(L)` as an algebra.
  refine derivationLieAlgebra.ext fun a => ?_
  induction a using induction_ι R L with
  | ι x => exact h x
  | algebraMap r =>
    rw [Algebra.algebraMap_eq_smul_one, map_smul, map_smul,
      derivationLieAlgebra.apply_one_eq_zero, derivationLieAlgebra.apply_one_eq_zero]
  | add a b ha hb => rw [map_add, map_add, ha, hb]
  | mul a b ha hb =>
    rw [derivationLieAlgebra.leibniz, derivationLieAlgebra.leibniz, ha, hb]

/-! ### The extension -/

/-- The `R`-linear map `x ↦ ι x + ε · ι (D x)` from `L` to the dual numbers over `U(L)`. -/
private def dualMap (D : LieDerivation R L L) : L →ₗ[R] DualNumber U where
  toFun x := TrivSqZeroExt.inl (_root_.UniversalEnvelopingAlgebra.ι R x)
    + TrivSqZeroExt.inr (_root_.UniversalEnvelopingAlgebra.ι R (D x))
  map_add' x y := by refine TrivSqZeroExt.ext ?_ ?_ <;> simp
  map_smul' r x := by refine TrivSqZeroExt.ext ?_ ?_ <;> simp

@[simp]
private theorem fst_dualMap (D : LieDerivation R L L) (x : L) :
    (dualMap R L D x).fst = _root_.UniversalEnvelopingAlgebra.ι R x := by
  simp [dualMap]

@[simp]
private theorem snd_dualMap (D : LieDerivation R L L) (x : L) :
    (dualMap R L D x).snd = _root_.UniversalEnvelopingAlgebra.ι R (D x) := by
  simp [dualMap]

/-- The map `x ↦ ι x + ε · ι (D x)` preserves the bracket: on `ε`-components the bracket of two
such elements differentiates one factor at a time, which is the Leibniz rule for `D`. -/
private theorem dualMap_lie (D : LieDerivation R L L) (x y : L) :
    dualMap R L D ⁅x, y⁆ = ⁅dualMap R L D x, dualMap R L D y⁆ := by
  refine TrivSqZeroExt.ext ?_ ?_
  · rw [Ring.lie_def]
    simp only [fst_dualMap, TrivSqZeroExt.fst_sub, TrivSqZeroExt.fst_mul]
    rw [LieHom.map_lie, Ring.lie_def]
  · rw [Ring.lie_def]
    simp only [snd_dualMap, TrivSqZeroExt.snd_sub, DualNumber.snd_mul, fst_dualMap]
    rw [LieDerivation.apply_lie_eq_add, map_add, LieHom.map_lie, LieHom.map_lie, Ring.lie_def,
      Ring.lie_def]
    abel

/-- The map `x ↦ ι x + ε · ι (D x)` as a homomorphism of Lie algebras. -/
private def dualLieHom (D : LieDerivation R L L) : L →ₗ⁅R⁆ DualNumber U :=
  { dualMap R L D with map_lie' := fun {x y} => dualMap_lie R L D x y }

/-- The algebra homomorphism `U(L) → U(L)[ε]` lifting `x ↦ ι x + ε · ι (D x)`. Its first component
is the identity and its second is the derivation extending `D`. -/
private noncomputable def dualAlgHom (D : LieDerivation R L L) : U →ₐ[R] DualNumber U :=
  _root_.UniversalEnvelopingAlgebra.lift R (dualLieHom R L D)

@[simp]
private theorem fst_dualAlgHom (D : LieDerivation R L L) (a : U) :
    (dualAlgHom R L D a).fst = a := by
  induction a using induction_ι R L with
  | ι x =>
    rw [dualAlgHom, _root_.UniversalEnvelopingAlgebra.lift_ι_apply]
    exact fst_dualMap R L D x
  | algebraMap r => rw [AlgHom.commutes]; exact (TrivSqZeroExt.fstHom R U U).commutes r
  | add a b ha hb => rw [map_add, TrivSqZeroExt.fst_add, ha, hb]
  | mul a b ha hb => rw [map_mul, TrivSqZeroExt.fst_mul, ha, hb]

private theorem snd_dualAlgHom_ι (D : LieDerivation R L L) (x : L) :
    (dualAlgHom R L D (_root_.UniversalEnvelopingAlgebra.ι R x)).snd
      = _root_.UniversalEnvelopingAlgebra.ι R (D x) := by
  rw [dualAlgHom, _root_.UniversalEnvelopingAlgebra.lift_ι_apply]
  exact snd_dualMap R L D x

/-- The second component of `dualAlgHom`, as an endomorphism of `U(L)`. -/
private noncomputable def dualEnd (D : LieDerivation R L L) : Module.End R U where
  toFun a := (dualAlgHom R L D a).snd
  map_add' a b := by rw [map_add, TrivSqZeroExt.snd_add]
  map_smul' r a := by rw [RingHom.id_apply, map_smul, TrivSqZeroExt.snd_smul]

private theorem dualEnd_apply (D : LieDerivation R L L) (a : U) :
    dualEnd R L D a = (dualAlgHom R L D a).snd := rfl

-- The extension is the `ε`-component of the algebra homomorphism `U(L) → U(L)[ε]` lifting
-- `x ↦ ι x + ε · ι (D x)`; the associative Leibniz rule is multiplicativity of that homomorphism,
-- given that its `1`-component is the identity.
/-- **The extension of a Lie derivation to the enveloping algebra**: the derivation `Dᵁ` of the
associative algebra `U(L)` with `Dᵁ (ι x) = ι (D x)`, the unique such derivation by
`TauCeti.UniversalEnvelopingAlgebra.derivation_ext`. -/
noncomputable def envelopingDerivation (D : LieDerivation R L L) : derivationLieAlgebra R U :=
  ⟨dualEnd R L D, mem_derivationLieAlgebra.2 fun a b => by
    rw [dualEnd_apply, dualEnd_apply, dualEnd_apply, map_mul, DualNumber.snd_mul,
      fst_dualAlgHom, fst_dualAlgHom, add_comm]⟩

-- Not a `simp` lemma: see the implementation notes.
/-- **The associative Leibniz rule for the extension**: `Dᵁ (a * b) = Dᵁ a * b + a * Dᵁ b`. -/
theorem envelopingDerivation_mul (D : LieDerivation R L L) (a b : U) :
    (envelopingDerivation R L D : Module.End R U) (a * b)
      = (envelopingDerivation R L D : Module.End R U) a * b
        + a * (envelopingDerivation R L D : Module.End R U) b :=
  derivationLieAlgebra.leibniz (envelopingDerivation R L D) a b

/-- **The extension property**: `Dᵁ` agrees with `D` on the canonical Lie generators. This is what
pins down which derivation of `U(L)` the extension is, by
`TauCeti.UniversalEnvelopingAlgebra.derivation_ext`. -/
theorem envelopingDerivation_ι (D : LieDerivation R L L) (x : L) :
    (envelopingDerivation R L D : Module.End R U) (_root_.UniversalEnvelopingAlgebra.ι R x)
      = _root_.UniversalEnvelopingAlgebra.ι R (D x) :=
  snd_dualAlgHom_ι R L D x

/-- The `simp`-normal form of `TauCeti.UniversalEnvelopingAlgebra.envelopingDerivation_ι`, stated
for the canonical generators as `simp` writes them. -/
@[simp]
theorem envelopingDerivation_ι' (D : LieDerivation R L L) (x : L) :
    (envelopingDerivation R L D : Module.End R U)
        (_root_.UniversalEnvelopingAlgebra.mkAlgHom R L (TensorAlgebra.ι R x))
      = _root_.UniversalEnvelopingAlgebra.mkAlgHom R L (TensorAlgebra.ι R (D x)) := by
  simpa only [_root_.UniversalEnvelopingAlgebra.ι_apply] using
    envelopingDerivation_ι R L D x

/-! ### Functoriality in the derivation -/

-- Each of the three identities is an equality of derivations of `U(L)`, so `derivation_ext`
-- reduces it to the corresponding identity of Lie derivations of `L`, read off the extension
-- property.
/-- **Lifting a Lie derivation to the enveloping algebra is a homomorphism of Lie algebras.** -/
noncomputable def envelopingDerivationHom :
    LieDerivation R L L →ₗ⁅R⁆ derivationLieAlgebra R U where
  toFun := envelopingDerivation R L
  map_add' D E := by
    refine derivation_ext R L fun x => ?_
    rw [envelopingDerivation_ι, AddMemClass.coe_add, LinearMap.add_apply,
      envelopingDerivation_ι, envelopingDerivation_ι, LieDerivation.add_apply, map_add]
  map_smul' r D := by
    refine derivation_ext R L fun x => ?_
    rw [RingHom.id_apply, envelopingDerivation_ι, SetLike.val_smul_of_tower,
      LinearMap.smul_apply, envelopingDerivation_ι, LieDerivation.smul_apply, map_smul]
  map_lie' := by
    intro D E
    refine derivation_ext R L fun x => ?_
    rw [envelopingDerivation_ι, LieSubalgebra.coe_bracket, Ring.lie_def,
      LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply,
      envelopingDerivation_ι, envelopingDerivation_ι, envelopingDerivation_ι,
      envelopingDerivation_ι, LieDerivation.lie_apply, map_sub]

@[simp]
theorem envelopingDerivationHom_apply (D : LieDerivation R L L) :
    envelopingDerivationHom R L D = envelopingDerivation R L D :=
  (rfl)

/-! ### Inner derivations -/

/-- **The extension of an inner derivation is inner**: the derivation of `U(L)` extending
`y ↦ ⁅y, x⁆` is `a ↦ ⁅a, ι x⁆`, the commutator with the corresponding canonical generator. So the
adjoint action of `L` on itself is carried to the adjoint action of `U(L)` on itself, and the
extension is not merely some derivation agreeing with `D` on the generators. -/
theorem envelopingDerivation_inner (x : L) (a : U) :
    (envelopingDerivation R L (LieDerivation.inner R L L x) : Module.End R U) a
      = ⁅a, _root_.UniversalEnvelopingAlgebra.ι R x⁆ := by
  have h : envelopingDerivation R L (LieDerivation.inner R L L x)
      = -innerDerivation R (_root_.UniversalEnvelopingAlgebra.ι R x) := by
    refine derivation_ext R L fun y => ?_
    rw [envelopingDerivation_ι, NegMemClass.coe_neg, LinearMap.neg_apply,
      coe_innerDerivation, LieAlgebra.ad_apply, LieDerivation.inner_apply_apply, LieHom.map_lie]
    exact (lie_skew _ _).symm
  rw [h, NegMemClass.coe_neg, LinearMap.neg_apply, coe_innerDerivation, LieAlgebra.ad_apply]
  exact lie_skew a (_root_.UniversalEnvelopingAlgebra.ι R x)

end UniversalEnvelopingAlgebra

end TauCeti
