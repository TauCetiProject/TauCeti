/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.CharP.Invertible
public import TauCeti.Algebra.Lie.HighestWeight.Basic
public import TauCeti.Algebra.Lie.Weights.Root.CorootSpan
public import TauCeti.LinearAlgebra.RootSystem.Weyl.Vector

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
total in `lam`, and off the integral weights it is junk; every lemma about it therefore carries
the integrality hypothesis that makes it meaningful, in the shape of the cast equation
`TauCeti.intCast_coweightPairing`.

The integral weights are closed under the operations of `TauCeti.IsIntegralWeight.add`,
`TauCeti.IsIntegralWeight.neg` and `TauCeti.IsIntegralWeight.zsmul`, so they form a `ℤ`-submodule
`TauCeti.integralWeightLattice` of `Module.Dual K H` -- a lattice and not a `K`-subspace, the
integrality condition being arithmetic rather than linear. Both objects the highest-weight theory
puts in it are here: the roots, and the Weyl vector `ρ` of a base.

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
* `TauCeti.coweightPairing_root_eq_pairingIn` and
  `TauCeti.coweightPairing_coe_eq_rootCartanWeight`: at a root the pairing is the Cartan integer,
  in Mathlib's root-pairing spelling and in the Lie-theoretic one.
* `TauCeti.root_mem_integralWeightLattice` and `TauCeti.weylVector_mem_integralWeightLattice`: the
  roots and the Weyl vector `ρ` are integral weights.
* `TauCeti.coweightPairing_weylVector`: `⟨ρ, αᵢ^∨⟩ = 1` for a simple root `αᵢ`, as an integer.
* `TauCeti.isDominantIntegral_iff_forall_coweightPairing_nonneg`: an integral weight is dominant
  exactly when its simple coroot pairings are nonnegative integers.
* `TauCeti.IsDominantIntegral.coweightPairing_add_weylVector_pos`: the `ρ`-shift of a dominant
  integral weight has *strictly* positive simple coroot pairings.

## Implementation notes

`TauCeti.coweightPairing` is the inverse image of `lam (αᵢ^∨)` under the integer cast, taken with
`Function.invFun`; the cast is injective in characteristic zero, so on integral weights this is
the unique integer with the right image, and no further choice is made.

`TauCeti.rootCartanWeight` of `TauCeti/Algebra/Lie/Weights/Root/CorootSpan.lean` is the same
integer for a *root* in the first argument, where the root-chain coefficients compute it outright;
`TauCeti.coweightPairing_coe_eq_rootCartanWeight` identifies the two. Neither subsumes the other:
the Cartan integers of `TauCeti.rootCartanWeight` are available with no hypothesis, while the
pairing here accepts the weight of a module, a sum `lam + ρ`, or any other integral weight, which
is what the dominance and dimension statements pair against a coroot.

## References

This file supplies the integral weight lattice milestone of Layer 4 of
`TauCetiRoadmap/RepresentationTheory/LieHighestWeight/README.md`, which asks for the lattice `X` as
a `ℤ`-submodule of `Module.Dual K H`, for the roots and `ρ` as elements of it, and for the coroot
pairings to land in `ℤ`; the target signature `coweightPairing` is pinned in the accompanying
`Suggested.lean`.

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, GTM 9, §13.2.
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
value of the weight on the coroot.

Deliberately not a `simp` lemma: rewriting with it discards the integrality that the pairing
exists to record. -/
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
theorem coweightPairing_add {lam mu : Dual K H} (hlam : IsIntegralWeight lam)
    (hmu : IsIntegralWeight mu) (i : H.root) :
    coweightPairing (lam + mu) i = coweightPairing lam i + coweightPairing mu i :=
  coweightPairing_eq_of_apply_coroot_eq_intCast <| by
    rw [LinearMap.add_apply, Int.cast_add, intCast_coweightPairing hlam,
      intCast_coweightPairing hmu]

/-- **The coroot pairing negates with the weight.** -/
theorem coweightPairing_neg {lam : Dual K H} (hlam : IsIntegralWeight lam) (i : H.root) :
    coweightPairing (-lam) i = -coweightPairing lam i :=
  coweightPairing_eq_of_apply_coroot_eq_intCast <| by
    rw [LinearMap.neg_apply, Int.cast_neg, intCast_coweightPairing hlam]

/-- **The coroot pairing subtracts with the weight.** -/
theorem coweightPairing_sub {lam mu : Dual K H} (hlam : IsIntegralWeight lam)
    (hmu : IsIntegralWeight mu) (i : H.root) :
    coweightPairing (lam - mu) i = coweightPairing lam i - coweightPairing mu i :=
  coweightPairing_eq_of_apply_coroot_eq_intCast <| by
    rw [LinearMap.sub_apply, Int.cast_sub, intCast_coweightPairing hlam,
      intCast_coweightPairing hmu]

/-- **The coroot pairing commutes with integer scaling of the weight.** -/
theorem coweightPairing_zsmul {lam : Dual K H} (hlam : IsIntegralWeight lam) (z : ℤ)
    (i : H.root) : coweightPairing (z • lam) i = z * coweightPairing lam i :=
  coweightPairing_eq_of_apply_coroot_eq_intCast <| by
    rw [LinearMap.smul_apply, Int.cast_mul, intCast_coweightPairing hlam, zsmul_eq_mul]

/-- **At a root the coroot pairing is the Cartan integer**, in the spelling of Mathlib's
crystallographic root-pairing API: the root system of a splitting Cartan subalgebra is valued in
`ℤ`, and `RootPairing.pairingIn` names the same integers this file names for a general weight. -/
theorem coweightPairing_root_eq_pairingIn (j i : H.root) :
    coweightPairing ((IsKilling.rootSystem H).root j) i =
      (IsKilling.rootSystem H).pairingIn ℤ j i :=
  coweightPairing_eq_of_apply_coroot_eq_intCast <| by
    simpa using (RootPairing.algebraMap_pairingIn (IsKilling.rootSystem H) ℤ j i).symm

/-- **At a root the coroot pairing is the Cartan integer**, in the Lie-theoretic spelling: for a
weight `β` of `L` the root-chain description `TauCeti.rootCartanWeight` computes the same
integer. -/
theorem coweightPairing_coe_eq_rootCartanWeight (β : Weight K H L) (i : H.root) :
    coweightPairing (β : Dual K H) i = rootCartanWeight β (i : Weight K H L) :=
  coweightPairing_eq_of_apply_coroot_eq_intCast <| by
    rw [intCast_rootCartanWeight_apply, IsKilling.rootSystem_coroot_apply]
    rfl

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

variable {b : (IsKilling.rootSystem H).Base}

/-- **The Weyl vector is dominant integral**: it pairs to `1` with every simple coroot. -/
theorem isDominantIntegral_weylVector :
    IsDominantIntegral b (weylVector (IsKilling.rootSystem H) b) :=
  isDominantIntegral_iff.mpr fun i hi =>
    ⟨1, by rw [← rootSystem_coroot'_apply, coroot'_weylVector (IsKilling.rootSystem H) b hi,
      Nat.cast_one]⟩

/-- **The Weyl vector lies in the integral weight lattice.** Dominance gives its values on the
simple coroots, and `TauCeti.IsDominantIntegral.isIntegralWeight` propagates integrality to all of
them. -/
theorem weylVector_mem_integralWeightLattice :
    weylVector (IsKilling.rootSystem H) b ∈ integralWeightLattice H :=
  isDominantIntegral_weylVector.isIntegralWeight

/-- **The Weyl vector pairs to one with every simple coroot**, `⟨ρ, αᵢ^∨⟩ = 1`, as an integer. -/
theorem coweightPairing_weylVector {i : H.root} (hi : i ∈ b.support) :
    coweightPairing (weylVector (IsKilling.rootSystem H) b) i = 1 :=
  coweightPairing_eq_of_apply_coroot_eq_intCast <| by
    rw [← rootSystem_coroot'_apply, coroot'_weylVector (IsKilling.rootSystem H) b hi, Int.cast_one]

/-- **The `ρ`-shift raises every simple coroot pairing by one**, as an identity of integers. -/
theorem coweightPairing_add_weylVector {lam : Dual K H} (hlam : IsIntegralWeight lam)
    {i : H.root} (hi : i ∈ b.support) :
    coweightPairing (lam + weylVector (IsKilling.rootSystem H) b) i =
      coweightPairing lam i + 1 := by
  rw [coweightPairing_add hlam weylVector_mem_integralWeightLattice, coweightPairing_weylVector hi]

/-! ### Dominance through the coroot pairings -/

/-- **A dominant integral weight has nonnegative simple coroot pairings.** -/
theorem IsDominantIntegral.coweightPairing_nonneg {lam : Dual K H}
    (hlam : IsDominantIntegral b lam) {i : H.root} (hi : i ∈ b.support) :
    0 ≤ coweightPairing lam i := by
  obtain ⟨n, hn⟩ := isDominantIntegral_iff.mp hlam i hi
  rw [coweightPairing_eq_of_apply_coroot_eq_intCast (n := (n : ℤ)) (by rw [hn, Int.cast_natCast])]
  exact Int.natCast_nonneg n

/-- **Dominance is nonnegativity of the simple coroot pairings.** For an integral weight the
dominance condition of `TauCeti.IsDominantIntegral` is exactly an inequality between integers. -/
theorem isDominantIntegral_iff_forall_coweightPairing_nonneg {lam : Dual K H}
    (hlam : IsIntegralWeight lam) :
    IsDominantIntegral b lam ↔ ∀ i ∈ b.support, 0 ≤ coweightPairing lam i := by
  refine ⟨fun h i hi ↦ h.coweightPairing_nonneg hi, fun h ↦ isDominantIntegral_iff.mpr ?_⟩
  refine fun i hi ↦ ⟨(coweightPairing lam i).toNat, ?_⟩
  rw [← intCast_coweightPairing hlam i]
  exact_mod_cast (Int.toNat_of_nonneg (h i hi)).symm

/-- **A dominant integral weight has nonnegative pairings against every positive coroot**, not
only the simple ones. -/
theorem IsDominantIntegral.coweightPairing_nonneg_of_mem_posRoots {lam : Dual K H}
    (hlam : IsDominantIntegral b lam) {i : H.root}
    (hi : i ∈ posRoots (IsKilling.rootSystem H) b) : 0 ≤ coweightPairing lam i := by
  obtain ⟨n, hn⟩ := hlam.exists_nat_apply_coroot hi
  rw [coweightPairing_eq_of_apply_coroot_eq_intCast (n := (n : ℤ)) (by rw [hn, Int.cast_natCast])]
  exact Int.natCast_nonneg n

/-- **The `ρ`-shift of a dominant integral weight is strictly dominant.** This is the role of `ρ`
in the highest-weight theory, and it is an inequality between integers: over a field with no order
it cannot be stated about the values in `K` at all. -/
theorem IsDominantIntegral.coweightPairing_add_weylVector_pos {lam : Dual K H}
    (hlam : IsDominantIntegral b lam) {i : H.root} (hi : i ∈ b.support) :
    0 < coweightPairing (lam + weylVector (IsKilling.rootSystem H) b) i := by
  rw [coweightPairing_add_weylVector hlam.isIntegralWeight hi]
  exact Int.lt_add_one_iff.mpr (hlam.coweightPairing_nonneg hi)

end TauCeti
