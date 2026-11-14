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
* `TauCeti.NovikovSeries.coe_log_nonnegSubring`: the analogous compatibility for the logarithm.
* `TauCeti.NovikovSeries.support_exp_subset`, `TauCeti.NovikovSeries.support_log_subset`: the
  totalized exponential and logarithm preserve support in an additive submonoid or subgroup of
  the exponent monoid, without a positivity assumption.
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

/-- The logarithm of a series of the nonnegative subring is the same whether it is computed in
the nonnegative subring or in the Novikov ring. -/
@[simp]
theorem coe_log_nonnegSubring (a : nonnegSubring K N) :
    ((NormedSpace.log a : nonnegSubring K N) : NovikovSeries K H N) =
      NormedSpace.log (a : NovikovSeries K H N) := by
  rw [NormedSpace.log_eq_tsum ℚ, NormedSpace.log_eq_tsum ℚ]
  exact (isClosed_nonnegSubring.isClosedEmbedding_subtypeVal.map_tsum
    (g := (nonnegSubring K N).subtype.toAddMonoidHom) _).trans (by simp)

private def supportSubalgebra {M : Type*} [SetLike M H] [AddSubmonoidClass M H]
    (S : M) : Subalgebra ℚ (NovikovSeries K H N) where
  carrier := {a | a.support ⊆ S}
  add_mem' ha hb := (support_add_subset _ _).trans (Set.union_subset ha hb)
  mul_mem' ha hb h hh := by
    obtain ⟨a, ha', b, hb', rfl⟩ := support_mul_subset _ _ hh
    exact add_mem (ha ha') (hb hb')
  algebraMap_mem' r h hh := by
    rw [algebraMap_apply] at hh
    exact (Set.mem_singleton_iff.1 (support_single_subset 0 (algebraMap ℚ K r) hh)) ▸
      zero_mem S

private theorem isClosed_supportSubalgebra {M : Type*} [SetLike M H] [AddSubmonoidClass M H]
    (S : M) : IsClosed (supportSubalgebra (K := K) (N := N) S : Set (NovikovSeries K H N)) := by
  have hset : (supportSubalgebra (K := K) (N := N) S : Set (NovikovSeries K H N)) =
      ⋂ h ∈ {h | h ∉ S}, {a | a.coeff h = 0} := by
    ext a
    simp only [supportSubalgebra, Set.mem_ofPred_eq, Set.mem_iInter]
    exact ⟨fun ha h hh => not_not.1 fun hn => hh (ha (mem_support.2 hn)),
      fun ha h hh => not_not.1 fun hn => mem_support.1 hh (ha h hn)⟩
  rw [hset]
  exact isClosed_biInter fun h _ => (isLocallyConstant_coeff h).isClosed_fiber 0

/-- The exponential of a series supported in an additive submonoid or subgroup is supported in
that subobject. This holds for the totalized exponential without a positivity assumption. -/
theorem support_exp_subset (a : NovikovSeries K H N) {M : Type*} [SetLike M H]
    [AddSubmonoidClass M H] {S : M} (ha : a.support ⊆ S) :
    (NormedSpace.exp a).support ⊆ S :=
  NormedSpace.exp_mem (R := ℚ) (s := supportSubalgebra S) (isClosed_supportSubalgebra S) ha

/-- The logarithm of a series supported in an additive submonoid or subgroup is supported in
that subobject. This holds for the totalized logarithm without a positivity assumption. -/
theorem support_log_subset (u : NovikovSeries K H N) {M : Type*} [SetLike M H]
    [AddSubmonoidClass M H] {S : M} (hu : u.support ⊆ S) :
    (NormedSpace.log u).support ⊆ S :=
  NormedSpace.log_mem (R := ℚ) (s := supportSubalgebra S) (isClosed_supportSubalgebra S) hu

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
    (u : NovikovSeries K H N) * degreeDerivation ℓ (NormedSpace.log (u : NovikovSeries K H N)) =
      degreeDerivation ℓ (u : NovikovSeries K H N) := by
  have := congrArg Subtype.val
    ((isTopologicallyNilpotent_of_mem_posIdeal' hu).mul_derivation_log
      (nonnegDegreeDerivation ℓ) (continuous_nonnegDegreeDerivation ℓ))
  simpa only [Subring.coe_mul, coe_nonnegDegreeDerivation, coe_log_nonnegSubring] using this

end NovikovSeries

end TauCeti
