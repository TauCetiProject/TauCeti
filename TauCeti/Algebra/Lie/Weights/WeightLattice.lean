/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.CharP.Invertible
public import Mathlib.Algebra.Lie.Weights.RootSystem
public import TauCeti.Algebra.Lie.Weights.Integrality

/-!
# The integral weight lattice and the coroot pairings of a weight

Let `L` be a finite-dimensional Lie algebra with non-degenerate Killing form over a field `K` of
characteristic zero and let `H` be a splitting Cartan subalgebra. A linear form
`lam : Module.Dual K H` is *integral* when `lam (α^∨)` is an integer for every root `α`
(`TauCeti.IsIntegralWeight`). This file records the two structures that condition carries: the
**integer** `⟨lam, αᵢ^∨⟩` itself, and the **integral weight lattice** of all integral weights.

The point of naming the integer is that `K` carries no order. Statements such as "`lam` is
dominant" or "`⟨lam + ρ, α^∨⟩` is positive" are not about `K` at all: they are about the integers
that integrality produces, and over an arbitrary characteristic-zero field they can only be made
by naming those integers. `TauCeti.coweightPairing lam i` is that name. Being `ℤ`-valued it is
total in `lam`, and off the integral weights it is junk: the cast equation
`TauCeti.intCast_coweightPairing` saying what the integer *is*, and the algebraic laws that follow
from it, therefore carry the integrality hypothesis that makes them meaningful. What needs no
hypothesis is a weight whose value at one coroot is already displayed as an integer -- exhibiting
that integer *is* integrality at that root -- and that is how the pairing is computed here
(`TauCeti.coweightPairing_eq_of_apply_coroot_eq_intCast`).

The integral weights are closed under the operations of `TauCeti.IsIntegralWeight.add`,
`TauCeti.IsIntegralWeight.neg` and `TauCeti.IsIntegralWeight.zsmul`, so they form a `ℤ`-submodule
`TauCeti.integralWeightLattice` of `Module.Dual K H` -- a lattice and not a `K`-subspace, the
integrality condition being arithmetic rather than linear. The roots lie in it; that the Weyl
vector `ρ` of a base does too is proved with the rest of the dominance theory, in
`TauCeti/Algebra/Lie/HighestWeight/Weight/Lattice.lean`.

## Main definitions

* `TauCeti.coweightPairing lam i`: the integer `⟨lam, αᵢ^∨⟩` pairing a weight with the coroot of
  the root `i`, junk unless `lam` is integral.
* `TauCeti.integralWeightLattice H`: the integral weights, as a `ℤ`-submodule of
  `Module.Dual K H`.

## Main results

* `TauCeti.intCast_coweightPairing`: the defining property, `(⟨lam, αᵢ^∨⟩ : K) = lam (αᵢ^∨)` for
  an integral weight `lam`. Together with `TauCeti.coweightPairing_eq_iff` it pins the pairing
  down, `K` having characteristic zero.
* `TauCeti.coweightPairing_add`, `TauCeti.coweightPairing_neg`, `TauCeti.coweightPairing_sub` and
  `TauCeti.coweightPairing_zsmul`: the pairing is additive in an integral weight.
* `TauCeti.coweightPairing_root_eq_pairingIn`: at a root the pairing is the Cartan integer, in
  Mathlib's crystallographic root-pairing spelling.
* `TauCeti.root_mem_integralWeightLattice`: the roots are integral weights.

## Implementation notes

`TauCeti.coweightPairing` is the inverse image of `lam (αᵢ^∨)` under the integer cast, taken with
`Function.invFun`; the cast is injective in characteristic zero, so on integral weights this is
the unique integer with the right image, and no further choice is made.

`TauCeti.rootCartanWeight` of `TauCeti/Algebra/Lie/Weights/Root/CorootSpan.lean` is the same
integer for a *root* in the first argument, where the root-chain coefficients compute it outright.
Neither subsumes the other: the Cartan integers of `TauCeti.rootCartanWeight` are available with no
hypothesis, while the pairing here accepts the weight of a module, a sum `lam + ρ`, or any other
integral weight, which is what the dominance and dimension statements pair against a coroot. The
lemma identifying the two, `TauCeti.coweightPairing_coe_eq_rootCartanWeight`, is stated beside
`TauCeti.rootCartanWeight`, so that nothing here depends on the root-chain theory.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, GTM 9, §13.2.
* The signature of `TauCeti.coweightPairing`, and its design as a total function that is junk off
  the integral weights, follow the human-authored prototype in
  `TauCetiRoadmap/RepresentationTheory/LieHighestWeight/Suggested.lean`.
-/

public section

namespace TauCeti

open LieAlgebra LieModule Module

universe u v

variable {K : Type u} {L : Type v} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [IsKilling K L] [FiniteDimensional K L]
  {H : LieSubalgebra K L} [H.IsCartanSubalgebra] [IsTriangularizable K H L]

/-! ### The coroot pairings of a weight -/

/-- **The coroot pairing `⟨lam, αᵢ^∨⟩` of a weight, as an integer.** For an integral weight `lam`
this is the unique integer whose image in `K` is `lam (αᵢ^∨)`
(`TauCeti.intCast_coweightPairing`); for any other linear form it is junk.

Making the pairing `ℤ`-valued is what lets dominance and positivity be stated over a field with no
order: see the module docstring. -/
noncomputable def coweightPairing (lam : Dual K H) (i : H.root) : ℤ :=
  Function.invFun (Int.cast : ℤ → K) (lam ((IsKilling.rootSystem H).coroot i))

/- The public lemmas below cannot unfold `TauCeti.coweightPairing` themselves: the module system
only lets an exported theorem unfold exposed definitions. -/
private theorem coweightPairing_def (lam : Dual K H) (i : H.root) :
    coweightPairing lam i =
      Function.invFun (Int.cast : ℤ → K) (lam ((IsKilling.rootSystem H).coroot i)) :=
  rfl

/-- **An integer value of `lam` on a coroot is its coroot pairing.** This is the only way the
pairing is ever computed, and it needs no integrality hypothesis: exhibiting the integer *is*
integrality at that root. -/
theorem coweightPairing_eq_of_apply_coroot_eq_intCast {lam : Dual K H} {i : H.root} {n : ℤ}
    (h : lam ((IsKilling.rootSystem H).coroot i) = (n : K)) : coweightPairing lam i = n := by
  rw [coweightPairing_def, h, Function.leftInverse_invFun Int.cast_injective n]

/-- **The defining property of the coroot pairing**: on an integral weight it casts back to the
value of the weight on the coroot. -/
@[simp]
theorem intCast_coweightPairing {lam : Dual K H} (hlam : IsIntegralWeight lam) (i : H.root) :
    ((coweightPairing lam i : ℤ) : K) = lam ((IsKilling.rootSystem H).coroot i) := by
  obtain ⟨n, hn⟩ : ∃ n : ℤ, lam ((IsKilling.rootSystem H).coroot i) = (n : K) := by
    simpa using hlam.exists_int_apply_coroot (i : Weight K H L)
  rw [coweightPairing_eq_of_apply_coroot_eq_intCast hn, hn]

/-- **The coroot pairing is characterized by its cast.** Characteristic zero makes the integer
unique, so this is the equation to reason with when the value is known in `K`. -/
theorem coweightPairing_eq_iff {lam : Dual K H} (hlam : IsIntegralWeight lam) {i : H.root}
    {n : ℤ} : coweightPairing lam i = n ↔ lam ((IsKilling.rootSystem H).coroot i) = (n : K) :=
  ⟨fun h ↦ by rw [← intCast_coweightPairing hlam i, h],
    coweightPairing_eq_of_apply_coroot_eq_intCast⟩

/-- **The zero weight pairs to zero.** -/
@[simp]
theorem coweightPairing_zero (i : H.root) : coweightPairing (0 : Dual K H) i = 0 :=
  coweightPairing_eq_of_apply_coroot_eq_intCast (by simp)

/-- **The coroot pairing is additive in the weight.** -/
@[simp]
theorem coweightPairing_add {lam mu : Dual K H} (hlam : IsIntegralWeight lam)
    (hmu : IsIntegralWeight mu) (i : H.root) :
    coweightPairing (lam + mu) i = coweightPairing lam i + coweightPairing mu i :=
  coweightPairing_eq_of_apply_coroot_eq_intCast <| by
    rw [LinearMap.add_apply, Int.cast_add, intCast_coweightPairing hlam,
      intCast_coweightPairing hmu]

/-- **The coroot pairing negates with the weight.** -/
@[simp]
theorem coweightPairing_neg {lam : Dual K H} (hlam : IsIntegralWeight lam) (i : H.root) :
    coweightPairing (-lam) i = -coweightPairing lam i :=
  coweightPairing_eq_of_apply_coroot_eq_intCast <| by
    rw [LinearMap.neg_apply, Int.cast_neg, intCast_coweightPairing hlam]

/-- **The coroot pairing subtracts with the weight.** -/
@[simp]
theorem coweightPairing_sub {lam mu : Dual K H} (hlam : IsIntegralWeight lam)
    (hmu : IsIntegralWeight mu) (i : H.root) :
    coweightPairing (lam - mu) i = coweightPairing lam i - coweightPairing mu i := by
  rw [sub_eq_add_neg, coweightPairing_add hlam hmu.neg, coweightPairing_neg hmu, ← sub_eq_add_neg]

/-- **The coroot pairing commutes with integer scaling of the weight.** -/
@[simp]
theorem coweightPairing_zsmul {lam : Dual K H} (hlam : IsIntegralWeight lam) (z : ℤ)
    (i : H.root) : coweightPairing (z • lam) i = z * coweightPairing lam i :=
  coweightPairing_eq_of_apply_coroot_eq_intCast <| by
    rw [LinearMap.smul_apply, Int.cast_mul, intCast_coweightPairing hlam, zsmul_eq_mul]

/-- **At a root the coroot pairing is the Cartan integer**, in the spelling of Mathlib's
crystallographic root-pairing API: the root system of a splitting Cartan subalgebra is valued in
`ℤ`, and `RootPairing.pairingIn` names the same integers this file names for a general weight. -/
-- Not a `simp` lemma: `LieAlgebra.IsKilling.rootSystem_root_apply` is one, so the left-hand side
-- rewrites to `TauCeti.coweightPairing (j : Dual K H) i` and is not in simp-normal form; tagging
-- it fails the `simpNF` linter.
theorem coweightPairing_root_eq_pairingIn (j i : H.root) :
    coweightPairing ((IsKilling.rootSystem H).root j) i =
      (IsKilling.rootSystem H).pairingIn ℤ j i :=
  coweightPairing_eq_of_apply_coroot_eq_intCast <| by
    simpa using (RootPairing.algebraMap_pairingIn (IsKilling.rootSystem H) ℤ j i).symm

/-! ### The integral weight lattice -/

variable (H) in
/-- **The integral weight lattice `X`**: the integral weights, as a `ℤ`-submodule of
`Module.Dual K H`.

It is a lattice and not a `K`-subspace: integrality asks a value to be an *integer*, which is an
arithmetic condition and is destroyed by scaling by a general element of `K`. -/
def integralWeightLattice : Submodule ℤ (Dual K H) where
  carrier := {lam | IsIntegralWeight lam}
  zero_mem' := isIntegralWeight_zero
  add_mem' hlam hmu := hlam.add hmu
  smul_mem' z _ hlam := hlam.zsmul z

omit [CharZero K] [IsTriangularizable K H L] in
/-- **Membership in the integral weight lattice** is integrality. -/
@[simp]
theorem mem_integralWeightLattice_iff {lam : Dual K H} :
    lam ∈ integralWeightLattice H ↔ IsIntegralWeight lam :=
  Iff.rfl

/-- **The roots lie in the integral weight lattice.** A root is a weight of the adjoint module, so
its coroot pairings are the Cartan integers. -/
theorem root_mem_integralWeightLattice (j : H.root) :
    (IsKilling.rootSystem H).root j ∈ integralWeightLattice H := by
  rw [mem_integralWeightLattice_iff, IsKilling.rootSystem_root_apply]
  exact isIntegralWeight_of_weight (j : Weight K H L)

end TauCeti
