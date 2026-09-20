/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.CharP.Invertible
public import TauCeti.Algebra.Lie.HighestWeight.Basic
public import TauCeti.Algebra.Lie.Weights.WeightLattice
public import TauCeti.LinearAlgebra.RootSystem.Weyl.Vector

/-!
# The Weyl vector and dominance through the coroot pairings

Let `L` be a finite-dimensional Lie algebra with non-degenerate Killing form over a field `K` of
characteristic zero, let `H` be a splitting Cartan subalgebra and let `b` be a base of its root
system. `TauCeti/Algebra/Lie/Weights/WeightLattice.lean` builds the integral weight lattice
`TauCeti.integralWeightLattice H` and the integer coroot pairings
`TauCeti.coweightPairing lam i = ⟨lam, αᵢ^∨⟩`; this file adds what the highest-weight theory needs
of them, namely the Weyl vector `ρ` of `b` and the reading of dominance through those integers.

The Weyl vector pairs to `1` with every simple coroot, so it is a dominant integral weight and in
particular lies in the lattice. Dominance itself becomes an inequality *between integers*:
`TauCeti.IsDominantIntegral b lam` says exactly that `lam` is integral and that every simple coroot
pairing `⟨lam, αᵢ^∨⟩` is nonnegative. That reformulation is what makes the `ρ`-shift usable: the
pairings of `lam + ρ` are those of `lam` raised by one, hence *strictly* positive. Over a field
with no order none of this can be said about the values in `K` at all.

## Main results

* `TauCeti.isDominantIntegral_weylVector` and `TauCeti.weylVector_mem_integralWeightLattice`: the
  Weyl vector `ρ` is a dominant integral weight, and so lies in the integral weight lattice.
* `TauCeti.coweightPairing_weylVector`: `⟨ρ, αᵢ^∨⟩ = 1` for a simple root `αᵢ`, as an integer.
* `TauCeti.coweightPairing_add_weylVector`: the `ρ`-shift raises every simple coroot pairing by
  one.
* `TauCeti.isDominantIntegral_iff_isIntegralWeight_and_forall_coweightPairing_nonneg`: a weight
  is dominant exactly when it is integral and its simple coroot pairings are nonnegative
  integers.
* `TauCeti.IsDominantIntegral.coweightPairing_add_weylVector_pos`: the `ρ`-shift of a dominant
  integral weight has *strictly* positive simple coroot pairings.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, GTM 9, §13.2.
-/

public section

namespace TauCeti

open LieAlgebra LieModule Module

universe u v

variable {K : Type u} {L : Type v} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [IsKilling K L] [FiniteDimensional K L]
  {H : LieSubalgebra K L} [H.IsCartanSubalgebra] [IsTriangularizable K H L]
  {b : (IsKilling.rootSystem H).Base}

/-! ### The Weyl vector -/

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
  mem_integralWeightLattice_iff.mpr isDominantIntegral_weylVector.isIntegralWeight

/-- **The Weyl vector pairs to one with every simple coroot**, `⟨ρ, αᵢ^∨⟩ = 1`, as an integer. -/
@[simp]
theorem coweightPairing_weylVector {i : H.root} (hi : i ∈ b.support) :
    coweightPairing (weylVector (IsKilling.rootSystem H) b) i = 1 :=
  coweightPairing_eq_of_apply_coroot_eq_intCast <| by
    rw [← rootSystem_coroot'_apply, coroot'_weylVector (IsKilling.rootSystem H) b hi, Int.cast_one]

/-- **The `ρ`-shift raises every simple coroot pairing by one**, as an identity of integers. -/
@[simp]
theorem coweightPairing_add_weylVector {lam : Dual K H} (hlam : IsIntegralWeight lam)
    {i : H.root} (hi : i ∈ b.support) :
    coweightPairing (lam + weylVector (IsKilling.rootSystem H) b) i =
      coweightPairing lam i + 1 := by
  rw [coweightPairing_add hlam isDominantIntegral_weylVector.isIntegralWeight,
    coweightPairing_weylVector hi]

/-! ### Dominance through the coroot pairings -/

/-- **A dominant integral weight has nonnegative pairings against every positive coroot**, not
only the simple ones. -/
theorem IsDominantIntegral.coweightPairing_nonneg_of_mem_posRoots {lam : Dual K H}
    (hlam : IsDominantIntegral b lam) {i : H.root}
    (hi : i ∈ posRoots (IsKilling.rootSystem H) b) : 0 ≤ coweightPairing lam i := by
  obtain ⟨n, hn⟩ := hlam.exists_nat_apply_coroot hi
  rw [coweightPairing_eq_of_apply_coroot_eq_intCast (n := (n : ℤ)) (by rw [hn, Int.cast_natCast])]
  exact Int.natCast_nonneg n

/-- **A dominant integral weight has nonnegative simple coroot pairings**, a simple root being
positive. -/
theorem IsDominantIntegral.coweightPairing_nonneg {lam : Dual K H}
    (hlam : IsDominantIntegral b lam) {i : H.root} (hi : i ∈ b.support) :
    0 ≤ coweightPairing lam i :=
  hlam.coweightPairing_nonneg_of_mem_posRoots
    (support_subset_posRoots (IsKilling.rootSystem H) b hi)

/-- **Dominance is integrality together with nonnegativity of the simple coroot pairings.** The
dominance condition of `TauCeti.IsDominantIntegral` is exactly an inequality between integers,
dominance supplying the integrality that makes those integers meaningful. -/
theorem isDominantIntegral_iff_isIntegralWeight_and_forall_coweightPairing_nonneg {lam : Dual K H} :
    IsDominantIntegral b lam ↔
      IsIntegralWeight lam ∧ ∀ i ∈ b.support, 0 ≤ coweightPairing lam i := by
  refine ⟨fun h ↦ ⟨h.isIntegralWeight, fun i hi ↦ h.coweightPairing_nonneg hi⟩, fun h ↦ ?_⟩
  refine isDominantIntegral_iff.mpr fun i hi ↦ ⟨(coweightPairing lam i).toNat, ?_⟩
  rw [← intCast_coweightPairing h.1 i]
  exact_mod_cast (Int.toNat_of_nonneg (h.2 i hi)).symm

/-- **The `ρ`-shift of a dominant integral weight is strictly dominant.** This is the role of `ρ`
in the highest-weight theory, and it is an inequality between integers: over a field with no order
it cannot be stated about the values in `K` at all. -/
theorem IsDominantIntegral.coweightPairing_add_weylVector_pos {lam : Dual K H}
    (hlam : IsDominantIntegral b lam) {i : H.root} (hi : i ∈ b.support) :
    0 < coweightPairing (lam + weylVector (IsKilling.rootSystem H) b) i := by
  rw [coweightPairing_add_weylVector hlam.isIntegralWeight hi]
  exact Int.lt_add_one_iff.mpr (hlam.coweightPairing_nonneg hi)

end TauCeti
