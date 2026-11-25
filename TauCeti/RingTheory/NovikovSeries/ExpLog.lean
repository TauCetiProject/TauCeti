/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.NovikovSeries.Derivation
public import TauCeti.RingTheory.NovikovSeries.Functoriality
public import TauCeti.RingTheory.NovikovSeries.PowerSeries
public import TauCeti.RingTheory.NovikovSeries.TopologicalRing
public import TauCeti.Topology.Algebra.IsUniformGroup.Subring
public import TauCeti.Topology.Algebra.TopologicallyNilpotent.ExpLog
import TauCeti.RingTheory.NovikovSeries.Grading

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

On series in one monomial the exponential is the formal one. For an exponent `γ` of positive
period and a power series `f` without constant term, the series map `f ↦ f(e^γ)`
(`TauCeti.NovikovSeries.ofPowerSeries`) sends the formal exponential `(exp K).subst f` of Mathlib
to `exp (f(e^γ))` (`TauCeti.NovikovSeries.ofPowerSeries_subst_exp`), since both have the
coefficients of `∑ fⁿ / n!`. This is how a zeta function defined in a Novikov ring is compared
with one defined as a formal power series, such as the Lefschetz zeta function of a map.

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
* `TauCeti.NovikovSeries.mapRingHom_exp`: the pushforward along a coefficient map and a
  period-rescaling exponent map commutes with the exponential of a series of the positive ideal.
* `TauCeti.NovikovSeries.toPowerSeries_exp`, `TauCeti.NovikovSeries.ofPowerSeries_subst_exp`: on
  series in one monomial `e^γ` of positive period, the exponential is the formal exponential
  `PowerSeries.exp` of Mathlib, substituted.

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

/-- The exponential of a series supported in an additive submonoid or subgroup is supported in
that subobject. This holds for the totalized exponential without a positivity assumption. -/
theorem support_exp_subset (a : NovikovSeries K H N) {M : Type*} [SetLike M H]
    [AddSubmonoidClass M H] {S : M} (ha : a.support ⊆ S) :
    (NormedSpace.exp a).support ⊆ S := by
  exact (mem_supportedSubalgebra ℚ K N).1
    (NormedSpace.exp_mem (R := ℚ) (s := supportedSubalgebra ℚ K N S)
      (by simpa only [coe_supportedSubalgebra] using
        isClosed_setOf_support_subset (N := N) (S : Set H))
      ((mem_supportedSubalgebra ℚ K N).2 ha))

/-- The logarithm of a series supported in an additive submonoid or subgroup is supported in
that subobject. This holds for the totalized logarithm without a positivity assumption. -/
theorem support_log_subset (u : NovikovSeries K H N) {M : Type*} [SetLike M H]
    [AddSubmonoidClass M H] {S : M} (hu : u.support ⊆ S) :
    (NormedSpace.log u).support ⊆ S := by
  exact (mem_supportedSubalgebra ℚ K N).1
    (NormedSpace.log_mem (R := ℚ) (s := supportedSubalgebra ℚ K N S)
      (by simpa only [coe_supportedSubalgebra] using
        isClosed_setOf_support_subset (N := N) (S : Set H))
      ((mem_supportedSubalgebra ℚ K N).2 hu))

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

section Map

variable {H' K' : Type*} [AddCommMonoid H'] {N' : H' →+ ℝ} [CommRing K'] [Algebra ℚ K']

/-- **Naturality of the exponential.** The pushforward along a ring homomorphism `ρ` of
coefficients and an exponent homomorphism `φ` rescaling periods commutes with the exponential of
a series of the positive ideal: `P_(ρ,φ) (exp a) = exp (P_(ρ,φ) a)`. -/
theorem mapRingHom_exp (ρ : K →+* K') (φ : H →+ H') (hφ : ∃ c > 0, ∀ h, N' (φ h) = c * N h)
    {a : nonnegSubring K N} (ha : a ∈ posIdeal K N) :
    mapRingHom ρ φ hφ (NormedSpace.exp (a : NovikovSeries K H N)) =
      NormedSpace.exp (mapRingHom ρ φ hφ a) := by
  rw [← coe_exp_nonnegSubring, mapRingHom_apply, ← coe_mapNonnegSubring,
    (isTopologicallyNilpotent_of_mem_posIdeal' ha).map_exp _ (continuous_mapNonnegSubring ρ φ hφ),
    coe_exp_nonnegSubring, coe_mapNonnegSubring, mapRingHom_apply]

end Map

section PowerSeries

open scoped PowerSeries

/-- **The exponential of a power series.** For a Novikov series on `ℕ` without constant term,
read as a power series, the exponential `∑ aⁿ / n!` in the period topology is the formal
exponential: `exp a = (exp K).subst a`. -/
theorem toPowerSeries_exp {a : NovikovSeries K ℕ (Nat.castAddMonoidHom ℝ)} (ha : a.coeff 0 = 0) :
    toPowerSeries (NormedSpace.exp a) = (PowerSeries.exp K).subst (toPowerSeries a) := by
  let b : nonnegSubring K (Nat.castAddMonoidHom ℝ) := ⟨a, mem_nonnegSubring_nat a⟩
  have hb : b ∈ posIdeal K (Nat.castAddMonoidHom ℝ) := mem_posIdeal_nat_iff.2 ha
  have hsum : HasSum (fun n : ℕ ↦ (n.factorial : ℚ)⁻¹ • a ^ n) (NormedSpace.exp a) := by
    have := ((isTopologicallyNilpotent_of_mem_posIdeal' hb).hasSum_exp).map
      (nonnegSubring K (Nat.castAddMonoidHom ℝ)).subtype continuous_subtypeVal
    rw [Subring.coe_subtype, coe_exp_nonnegSubring] at this
    exact this.congr_fun fun n ↦ by simp [b]
  -- Both sides have `n`-th coefficient `∑_d (a ^ d)ₙ / d!`.
  ext n
  rw [coeff_toPowerSeries, coeff_eq_finsum_of_hasSum hsum,
    PowerSeries.coeff_subst' (PowerSeries.HasSubst.of_constantCoeff_zero'
      (by rwa [← PowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_toPowerSeries]))]
  refine finsum_congr fun d ↦ ?_
  rw [coeff_smul, PowerSeries.coeff_exp, ← map_pow, coeff_toPowerSeries, algebraMap_smul,
    one_div]

/-- **The series map commutes with the exponential.** For an exponent `γ` of positive period and
a power series `f` without constant term, the image at `e^γ` of the formal exponential
`(exp K).subst f` is the exponential of the image of `f`. -/
theorem ofPowerSeries_subst_exp {γ : H} (hγ : 0 < N γ) {f : K⟦X⟧}
    (hf : PowerSeries.constantCoeff f = 0) :
    ofPowerSeries γ hγ ((PowerSeries.exp K).subst f) =
      NormedSpace.exp (ofPowerSeries γ hγ f) := by
  have hf' : (toPowerSeries.symm f : NovikovSeries K ℕ (Nat.castAddMonoidHom ℝ)).coeff 0 = 0 := by
    rwa [coeff_toPowerSeries_symm, PowerSeries.coeff_zero_eq_constantCoeff_apply]
  have h := toPowerSeries_exp hf'
  rw [RingEquiv.apply_symm_apply] at h
  rw [← h, ofPowerSeries_apply, ofPowerSeries_apply, RingEquiv.symm_apply_apply,
    ← mapRingHom_apply, ← mapRingHom_apply]
  exact mapRingHom_exp (a := ⟨_, mem_nonnegSubring_nat _⟩) _ _ _ (mem_posIdeal_nat_iff.2 hf')

end PowerSeries

end NovikovSeries

end TauCeti
