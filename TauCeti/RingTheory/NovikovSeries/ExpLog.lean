/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.NovikovSeries.Derivation
public import TauCeti.RingTheory.NovikovSeries.TopologicalRing
public import TauCeti.Topology.Algebra.IsUniformGroup.Subring
public import TauCeti.Topology.Algebra.TopologicallyNilpotent.ExpLog

/-!
# Exponential and logarithm of Novikov series

Let `K` be a commutative `ℚ`-algebra, `H` an additive commutative monoid and `N : H →+ ℝ` a
period homomorphism. The nonnegative subring of the Novikov ring `Nov(K, H, N)` is a complete,
separated, linearly topologized `ℚ`-algebra, and the series of its positive ideal are
topologically nilpotent. So the general theory of the exponential and logarithm of topologically
nilpotent elements applies (`TauCeti/Topology/Algebra/TopologicallyNilpotent/ExpLog.lean`): for
`a` in the positive ideal, the series of Mathlib's exponential `NormedSpace.exp` and logarithm
`NormedSpace.log`

`exp a = ∑ aⁿ / n!`,    `log (1 + a) = ∑ (-1)ⁿ⁺¹ aⁿ / n`

converge in the period topology, and the exponential is an isomorphism from the additive group of
the positive ideal onto its principal unit group of units `u` with `u - 1` in the positive ideal,
with inverse the logarithm (`TauCeti.NovikovSeries.expMulEquiv`). The dynamical zeta function of a
closed one-form is defined as the exponential of a rational logarithmic series of periodic orbits
lying in the positive ideal; by this isomorphism it is a principal unit.

The degree derivations of `TauCeti/RingTheory/NovikovSeries/Derivation.lean` are continuous, so
they differentiate the logarithm of a principal unit logarithmically: `u * D (log u) = D u`
(`TauCeti.NovikovSeries.mul_degreeDerivation_log`).

## Main definitions

* `TauCeti.NovikovSeries.expMulEquiv`: the exponential, as an isomorphism from the additive group
  of the positive ideal onto its principal unit group, with inverse the logarithm.

## Main results

* `TauCeti.NovikovSeries.coe_exp_nonnegSubring`: the exponential of a series of the nonnegative
  subring does not depend on whether it is computed in the nonnegative subring or in the Novikov
  ring.
* `TauCeti.NovikovSeries.support_log_subset`: the logarithm preserves support in an additive
  submonoid of the exponent monoid.
* `TauCeti.NovikovSeries.mul_degreeDerivation_log`: the logarithmic derivative of the logarithm
  along a degree derivation.

## References

* M. Hutchings and Y.-J. Lee, *Circle-valued Morse theory and Reidemeister torsion*,
  Geom. Topol. 3 (1999), Section 2.
-/

public section

noncomputable section

namespace TauCeti

namespace NovikovSeries

section Ring

variable {H K : Type*} [AddMonoid H] {N : H →+ ℝ} [Ring K] [Algebra ℚ K]

/-- The exponential of a series of the nonnegative subring is the same whether it is computed in
the nonnegative subring or in the Novikov ring. -/
@[simp]
theorem coe_exp_nonnegSubring (a : nonnegSubring K N) :
    ((NormedSpace.exp a : nonnegSubring K N) : NovikovSeries K H N) =
      NormedSpace.exp (a : NovikovSeries K H N) := by
  rw [NormedSpace.exp_eq_tsum_rat (𝔸 := nonnegSubring K N),
    NormedSpace.exp_eq_tsum_rat (𝔸 := NovikovSeries K H N)]
  exact (isClosed_nonnegSubring.isClosedEmbedding_subtypeVal.map_tsum
    (g := (nonnegSubring K N).subtype.toAddMonoidHom) _).trans (by simp)

/-- The logarithm of a series supported in an additive submonoid is supported in that
submonoid. This holds for the totalized logarithm without a positivity assumption. -/
theorem support_log_subset (u : nonnegSubring K N) {S : AddSubmonoid H}
    (hu : (u : NovikovSeries K H N).support ⊆ S) :
    ((NormedSpace.log u : nonnegSubring K N) : NovikovSeries K H N).support ⊆ S := by
  have h_one : (1 : NovikovSeries K H N).support ⊆ S := by
    intro h hh
    rw [← single_zero_one] at hh
    exact (Set.mem_singleton_iff.1 (support_single_subset 0 1 hh)) ▸ S.zero_mem
  have h_sub : ((u : NovikovSeries K H N) - 1).support ⊆ S :=
    (support_sub_subset _ _).trans (Set.union_subset hu h_one)
  have h_pow (n : ℕ) : (((u : NovikovSeries K H N) - 1) ^ n).support ⊆ S := by
    induction n with
    | zero => simpa using h_one
    | succ n hn =>
      rw [pow_succ]
      intro h hh
      obtain ⟨a, ha, b, hb, rfl⟩ := support_mul_subset _ _ hh
      exact S.add_mem (hn ha) (h_sub hb)
  rw [NormedSpace.log_eq_tsum ℚ]
  -- Present the subtype coercion as its bundled additive map so that `map_tsum` applies.
  change ((nonnegSubring K N).subtype.toAddMonoidHom
    (∑' n : ℕ, ((-1) ^ (n + 1) / n : ℚ) • (u - 1) ^ n)).support ⊆ S
  rw [isClosed_nonnegSubring.isClosedEmbedding_subtypeVal.map_tsum
    (g := (nonnegSubring K N).subtype.toAddMonoidHom)]
  intro h hh
  by_contra hs
  apply mem_support.1 hh
  apply coeff_tsum_eq_zero
  intro n
  by_contra hn
  apply hs
  apply h_pow n
  exact support_smul_subset ((-1) ^ (n + 1) / n : ℚ) _ (by simpa using mem_support.2 hn)

end Ring

variable {H K : Type*} [AddCommMonoid H] {N : H →+ ℝ} [CommRing K] [Algebra ℚ K]

variable (K N) in
/-- **Exponential and logarithm** of Novikov series: over a `ℚ`-algebra `K`, the exponential is
an isomorphism from the additive group of the positive ideal onto its principal unit group in the
nonnegative subring, with inverse the logarithm. This is `Ideal.expMulEquiv` for the positive
ideal, whose series are topologically nilpotent. -/
def expMulEquiv : Multiplicative (posIdeal K N) ≃* (posIdeal K N).principalUnitGroup :=
  (posIdeal K N).expMulEquiv fun _ => isTopologicallyNilpotent_of_mem_posIdeal'

/-- `TauCeti.NovikovSeries.expMulEquiv` sends `a` to the unit `exp a`. -/
@[simp]
theorem coe_expMulEquiv_apply (a : posIdeal K N) :
    ((expMulEquiv K N (.ofAdd a) : (nonnegSubring K N)ˣ) : nonnegSubring K N) =
      NormedSpace.exp (a : nonnegSubring K N) :=
  Ideal.coe_expMulEquiv_apply _ _ a

/-- The inverse of `TauCeti.NovikovSeries.expMulEquiv` sends a unit `u` to `log u`. -/
@[simp]
theorem coe_expMulEquiv_symm_apply (u : (posIdeal K N).principalUnitGroup) :
    (((expMulEquiv K N).symm u).toAdd : nonnegSubring K N) =
      NormedSpace.log ((u : (nonnegSubring K N)ˣ) : nonnegSubring K N) :=
  Ideal.coe_expMulEquiv_symm_apply _ _ u

/-- A degree derivation differentiates the logarithm of a principal unit of the nonnegative
subring logarithmically: `u * D (log u) = D u`, read in the Novikov series. -/
theorem mul_degreeDerivation_log (ℓ : H →+ K) {u : nonnegSubring K N}
    (hu : u - 1 ∈ posIdeal K N) :
    (u : NovikovSeries K H N) * degreeDerivation ℓ (NormedSpace.log u : nonnegSubring K N) =
      degreeDerivation ℓ (u : NovikovSeries K H N) := by
  have := congrArg Subtype.val
    ((isTopologicallyNilpotent_of_mem_posIdeal' hu).mul_derivation_log
      (nonnegDegreeDerivation ℓ) (continuous_nonnegDegreeDerivation ℓ))
  simpa only [Subring.coe_mul, coe_nonnegDegreeDerivation] using this

end NovikovSeries

end TauCeti
