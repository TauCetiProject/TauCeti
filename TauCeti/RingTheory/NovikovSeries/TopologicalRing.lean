/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.NovikovSeries.Multiplication
public import TauCeti.RingTheory.NovikovSeries.Topology
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.Topology.Algebra.TopologicallyNilpotent
public import TauCeti.Topology.Algebra.Nonarchimedean.GeometricSeries

/-!
# Novikov series form a topological ring, and geometric series

Let `H` be an additive monoid with a period homomorphism `N : H →+ ℝ`. The period filtration
`U_C` of `TauCeti.RingTheory.NovikovSeries.Topology` is compatible with the convolution product:
periods add under multiplication, so `U_C * U_D ⊆ U_(C + D)`
(`TauCeti.NovikovSeries.mul_mem_periodFiltration`). Since every Novikov series lies in some `U_C`,
multiplication is continuous for the period topology and the Novikov series form a
nonarchimedean topological ring. Iterating the estimate, a series supported in periods `≥ C` with
`C > 0` is topologically nilpotent; this is what makes geometric series `∑ aⁿ` of positive-period
series converge in the complete ring of Novikov series, and likewise exponential series when the
coefficients form a `ℚ`-algebra.

The same estimate makes products computable from finite truncations: below the cutoff `C`, the
product of two series with periods bounded below by `A` and `B` only involves their coefficients of
period `< C - B` and `< C - A`
(`TauCeti.NovikovSeries.mul_sub_mul_trunc_mem_periodFiltration`). Multiplying by a monomial
`u e^g` with unit coefficient shifts the filtration by the period `N g` when exponents satisfy
left cancellation
(`TauCeti.NovikovSeries.single_mul_mem_periodFiltration_iff`).

The series supported in nonnegative periods form a subring, whose underlying set is the basic
neighbourhood `U_0`, and the series supported in strictly positive periods form an ideal of it. A
series `a` of the positive ideal lies in `U_C` for some `C > 0`, so it is topologically nilpotent,
and in the complete nonarchimedean Novikov ring the geometric series `∑ aⁿ` converges to a
two-sided inverse of `1 - a` in the nonnegative subring. For a monomial `e^g` with `N g > 0` this
is the expansion `(1 - e^g)⁻¹ = ∑ₖ e^(k • g)`. Such geometric series are the factors in the
product formula for dynamical zeta functions, and they appear in the torsion of circle-valued
Morse complexes.

## Main definitions

* `TauCeti.NovikovSeries.nonnegSubring`: the subring of series supported in periods `≥ 0`.
* `TauCeti.NovikovSeries.posIdeal`: the ideal of the nonnegative subring formed by the series
  supported in periods `> 0`.
* `TauCeti.NovikovSeries.unitsOneSub`: for `a` in the positive ideal, `1 - a` as a unit of the
  nonnegative subring, with inverse the geometric series `∑ aⁿ`.

## Main results

* `TauCeti.NovikovSeries.mul_mem_periodFiltration`: `U_C * U_D ⊆ U_(C + D)`.
* `TauCeti.NovikovSeries.mul_sub_mul_mem_periodFiltration` and
  `TauCeti.NovikovSeries.mul_sub_mul_trunc_mem_periodFiltration`: cutoff compatibility of the
  convolution.
* `TauCeti.NovikovSeries.single_mul_mem_periodFiltration_iff`: multiplication by a monomial with
  unit coefficient shifts the period filtration for left-cancellative exponents.
* The instances `IsTopologicalRing` and `NonarchimedeanRing`: the period topology is a
  nonarchimedean ring topology.
* `TauCeti.NovikovSeries.pow_mem_periodFiltration` and
  `TauCeti.NovikovSeries.isTopologicallyNilpotent_of_mem_periodFiltration`: a series supported in
  periods `≥ C` has its `n`-th power supported in periods `≥ n • C`, so it is topologically
  nilpotent when `C > 0`.
* `TauCeti.NovikovSeries.isTopologicallyNilpotent_of_mem_posIdeal`: a series of the positive ideal
  is topologically nilpotent.
* `TauCeti.NovikovSeries.tsum_pow_mem_nonnegSubring` and
  `TauCeti.NovikovSeries.isUnit_one_sub_of_mem_posIdeal`: for `a` in the positive ideal, the
  geometric series `∑ aⁿ` lies in the nonnegative subring and `1 - a` is a unit there.
* `TauCeti.NovikovSeries.one_sub_single_mul_tsum` and
  `TauCeti.NovikovSeries.tsum_mul_one_sub_single`: the two inverse identities of the monomial
  geometric series `∑ₖ rᵏ e^(k • g)` for `N g > 0`.

## References

* M. Hutchings and Y.-J. Lee, *Circle-valued Morse theory and Reidemeister torsion*,
  Geom. Topol. 3 (1999), Section 2.
* A. Pajitnov, *Circle-valued Morse Theory*, de Gruyter 2006, Chapter 3.
-/

public section

noncomputable section

open Filter Topology

namespace TauCeti

namespace NovikovSeries

variable {R H : Type*}

section NonUnitalNonAssocRing

variable [AddZeroClass H] {N : H →+ ℝ} [NonUnitalNonAssocRing R] {A B C D : ℝ}
  {a a' b b' : NovikovSeries R H N}

/-- Periods add under multiplication: if the coefficients of `a` vanish below the period `C` and
those of `b` below `D`, then those of `a * b` vanish below `C + D`. -/
theorem mul_mem_periodFiltration (ha : a ∈ periodFiltration R N C)
    (hb : b ∈ periodFiltration R N D) : a * b ∈ periodFiltration R N (C + D) := by
  refine mem_periodFiltration.2 fun h hh => ?_
  by_contra hab
  obtain ⟨u, v, rfl, hu, hv⟩ := exists_add_eq_of_coeff_mul_ne_zero hab
  have hu' : C ≤ N u := not_lt.1 fun hu' => hu (mem_periodFiltration.1 ha u hu')
  have hv' : D ≤ N v := not_lt.1 fun hv' => hv (mem_periodFiltration.1 hb v hv')
  rw [map_add] at hh
  linarith

/-- Products are determined modulo `U_C` by approximations of their factors: if `a ∈ U_A` and
`b' ∈ U_B`, and `a'` and `b'` agree with `a` and `b` modulo `U_(C - B)` and `U_(C - A)`, then
`a * b` and `a' * b'` agree modulo `U_C`. -/
theorem mul_sub_mul_mem_periodFiltration (ha : a ∈ periodFiltration R N A)
    (hb' : b' ∈ periodFiltration R N B) (haa' : a - a' ∈ periodFiltration R N (C - B))
    (hbb' : b - b' ∈ periodFiltration R N (C - A)) :
    a * b - a' * b' ∈ periodFiltration R N C := by
  have h₁ := mul_mem_periodFiltration ha hbb'
  have h₂ := mul_mem_periodFiltration haa' hb'
  rw [add_sub_cancel] at h₁
  rw [sub_add_cancel] at h₂
  have hab : a * b - a' * b' = a * (b - b') + (a - a') * b' := by
    rw [mul_sub, sub_mul]
    abel
  rw [hab]
  exact add_mem h₁ h₂

/-- Cutoff compatibility of the convolution: if the coefficients of `a` vanish below `A` and those
of `b` below `B`, then below the cutoff `C` the product `a * b` agrees with the product of the
truncations of `a` below `C - B` and of `b` below `C - A`. -/
theorem mul_sub_mul_trunc_mem_periodFiltration (ha : a ∈ periodFiltration R N A)
    (hb : b ∈ periodFiltration R N B) (C : ℝ) :
    a * b - ofFinsupp (trunc (C - B) a) * ofFinsupp (trunc (C - A) b) ∈
      periodFiltration R N C :=
  mul_sub_mul_mem_periodFiltration ha (ofFinsupp_trunc_mem_periodFiltration _ hb)
    (sub_ofFinsupp_trunc_mem_periodFiltration _ a) (sub_ofFinsupp_trunc_mem_periodFiltration _ b)

/-- Multiplication of Novikov series is continuous for the period topology. -/
instance : IsTopologicalRing (NovikovSeries R H N) := by
  refine .of_addGroup_of_nhds_zero ?_ (fun x => ?_) fun x => ?_
  · refine (hasBasis_nhds_zero.prod_self.tendsto_iff hasBasis_nhds_zero).2 fun C _ =>
      ⟨C / 2, trivial, ?_⟩
    rintro ⟨a, b⟩ ⟨ha, hb⟩
    simpa only [Function.uncurry_apply_pair, SetLike.mem_coe, add_halves] using
      mul_mem_periodFiltration ha hb
  · obtain ⟨D, hx⟩ := exists_mem_periodFiltration x
    exact (hasBasis_nhds_zero.tendsto_iff hasBasis_nhds_zero).2 fun C _ =>
      ⟨C - D, trivial, fun a ha => by
        simpa only [SetLike.mem_coe, add_sub_cancel] using mul_mem_periodFiltration hx ha⟩
  · obtain ⟨D, hx⟩ := exists_mem_periodFiltration x
    exact (hasBasis_nhds_zero.tendsto_iff hasBasis_nhds_zero).2 fun C _ =>
      ⟨C - D, trivial, fun a ha => by
        simpa only [SetLike.mem_coe, sub_add_cancel] using mul_mem_periodFiltration ha hx⟩

end NonUnitalNonAssocRing

section Ring

variable [AddMonoid H] {N : H →+ ℝ} [Ring R] {C : ℝ} {a : NovikovSeries R H N}

/-- The coefficientwise inclusion of the group ring has dense image in its Novikov completion. -/
theorem denseRange_ofAddMonoidAlgebra :
    DenseRange (ofAddMonoidAlgebra : AddMonoidAlgebra R H → NovikovSeries R H N) := by
  apply DenseRange.of_comp (g := AddMonoidAlgebra.ofCoeff)
  have h : (ofAddMonoidAlgebra : AddMonoidAlgebra R H → NovikovSeries R H N) ∘
      AddMonoidAlgebra.ofCoeff = ofFinsupp := by
    funext f
    ext h
    simp only [Function.comp_apply, coeff_ofAddMonoidAlgebra, coeff_ofFinsupp]
  rw [h]
  exact denseRange_ofFinsupp

/-- The period topology is a nonarchimedean ring topology. -/
instance : NonarchimedeanRing (NovikovSeries R H N) where
  is_nonarchimedean := NonarchimedeanAddGroup.is_nonarchimedean

/-- The unit series `1 = e^0` lies in `U_0`. -/
theorem one_mem_periodFiltration_zero : (1 : NovikovSeries R H N) ∈ periodFiltration R N 0 := by
  simpa only [single_zero_one, map_zero] using
    single_mem_periodFiltration (R := R) (N := N) (0 : H) 1

/-- If the coefficients of `a` vanish below the period `C`, then those of `a ^ n` vanish below
`n • C`. -/
theorem pow_mem_periodFiltration (ha : a ∈ periodFiltration R N C) (n : ℕ) :
    a ^ n ∈ periodFiltration R N (n • C) := by
  induction n with
  | zero => simpa using one_mem_periodFiltration_zero
  | succ n ih =>
    rw [pow_succ, succ_nsmul]
    exact mul_mem_periodFiltration ih ha

/-- A Novikov series whose coefficients vanish below some positive period is topologically
nilpotent: its powers tend to `0` in the period topology. -/
theorem isTopologicallyNilpotent_of_mem_periodFiltration (hC : 0 < C)
    (ha : a ∈ periodFiltration R N C) : IsTopologicallyNilpotent a := by
  refine hasBasis_nhds_zero.tendsto_right_iff.2 fun D _ => ?_
  obtain ⟨n, hn⟩ := Archimedean.arch D hC
  filter_upwards [eventually_ge_atTop n] with m hm
  exact antitone_periodFiltration (hn.trans (nsmul_le_nsmul_left hC.le hm))
    (pow_mem_periodFiltration ha m)

/-- A monomial `r e^g` of positive period `N g` is topologically nilpotent. -/
theorem isTopologicallyNilpotent_single {g : H} (hg : 0 < N g) (r : R) :
    IsTopologicallyNilpotent (single g r : NovikovSeries R H N) :=
  isTopologicallyNilpotent_of_mem_periodFiltration hg (single_mem_periodFiltration g r)

/-- **Geometric series of a monomial**, left inverse identity: for `N g > 0`,
`(1 - r e^g) * ∑ₖ rᵏ e^(k • g) = 1`. -/
theorem one_sub_single_mul_tsum {g : H} (hg : 0 < N g) (r : R) :
    (1 - single g r) * ∑' k : ℕ, (single (k • g) (r ^ k) : NovikovSeries R H N) = 1 := by
  simpa using (isTopologicallyNilpotent_single hg r).summable_pow.one_sub_mul_tsum_pow

/-- **Geometric series of a monomial**, right inverse identity: for `N g > 0`,
`(∑ₖ rᵏ e^(k • g)) * (1 - r e^g) = 1`. -/
theorem tsum_mul_one_sub_single {g : H} (hg : 0 < N g) (r : R) :
    (∑' k : ℕ, (single (k • g) (r ^ k) : NovikovSeries R H N)) * (1 - single g r) = 1 := by
  simpa using (isTopologicallyNilpotent_single hg r).summable_pow.tsum_pow_mul_one_sub

variable (R N) in
/-- The subring of Novikov series supported in nonnegative periods. Its underlying additive
subgroup is the basic neighbourhood `U_0` of the period topology. -/
def nonnegSubring : Subring (NovikovSeries R H N) where
  toAddSubgroup := periodFiltration R N 0
  one_mem' := one_mem_periodFiltration_zero
  mul_mem' ha hb := by simpa using mul_mem_periodFiltration ha hb

@[simp]
theorem mem_nonnegSubring {a : NovikovSeries R H N} :
    a ∈ nonnegSubring R N ↔ ∀ h, N h < 0 → a.coeff h = 0 :=
  mem_periodFiltration

variable (R N) in
/-- The underlying additive subgroup of the nonnegative subring is `U_0`. -/
theorem toAddSubgroup_nonnegSubring :
    (nonnegSubring R N).toAddSubgroup = periodFiltration R N 0 :=
  (rfl)

/-- The nonnegative subring is open, hence also closed, in the period topology. -/
theorem isOpen_nonnegSubring : IsOpen (nonnegSubring R N : Set (NovikovSeries R H N)) :=
  isOpen_periodFiltration 0

theorem isClosed_nonnegSubring : IsClosed (nonnegSubring R N : Set (NovikovSeries R H N)) :=
  isClosed_periodFiltration 0

/-- The monomial `r e^g` lies in the nonnegative subring when `N g ≥ 0`. -/
theorem single_mem_nonnegSubring {g : H} (hg : 0 ≤ N g) (r : R) :
    single g r ∈ nonnegSubring R N :=
  antitone_periodFiltration hg (single_mem_periodFiltration g r)

variable (R N) in
/-- The ideal of the nonnegative subring formed by the series supported in strictly positive
periods. Its elements are the series lying in `U_C` for some `C > 0`
(`TauCeti.NovikovSeries.exists_pos_mem_periodFiltration_iff`). -/
def posIdeal : Ideal (nonnegSubring R N) where
  carrier := {a | ∀ h, N h ≤ 0 → (a : NovikovSeries R H N).coeff h = 0}
  add_mem' ha hb h hh := by simp [ha h hh, hb h hh]
  zero_mem' _ _ := rfl
  smul_mem' c a ha := by
    obtain ⟨C, hC, haC⟩ := exists_pos_mem_periodFiltration_iff.2 ha
    exact exists_pos_mem_periodFiltration_iff.1
      ⟨0 + C, by rwa [zero_add], mul_mem_periodFiltration c.2 haC⟩

@[simp]
theorem mem_posIdeal {a : nonnegSubring R N} :
    a ∈ posIdeal R N ↔ ∀ h, N h ≤ 0 → (a : NovikovSeries R H N).coeff h = 0 :=
  Iff.rfl

/-- The positive ideal is two-sided, also for noncommutative coefficients. -/
instance : (posIdeal R N).IsTwoSided where
  mul_mem_of_left b ha := by
    obtain ⟨C, hC, haC⟩ := exists_pos_mem_periodFiltration_iff.2 ha
    exact exists_pos_mem_periodFiltration_iff.1
      ⟨C + 0, by rwa [add_zero], mul_mem_periodFiltration haC b.2⟩

/-- A series of the positive ideal is topologically nilpotent. -/
theorem isTopologicallyNilpotent_of_mem_posIdeal {a : nonnegSubring R N} (ha : a ∈ posIdeal R N) :
    IsTopologicallyNilpotent (a : NovikovSeries R H N) := by
  obtain ⟨C, hC, haC⟩ := exists_pos_mem_periodFiltration_iff.2 ha
  exact isTopologicallyNilpotent_of_mem_periodFiltration hC haC

/-- For `a` in the nonnegative subring, the geometric series `∑ aⁿ` lies in the nonnegative
subring. -/
theorem tsum_pow_mem_nonnegSubring (a : nonnegSubring R N) :
    ∑' n : ℕ, (a : NovikovSeries R H N) ^ n ∈ nonnegSubring R N :=
  tsum_mem isClosed_nonnegSubring fun n => Subring.pow_mem _ a.2 n

/-- For `a` in the positive ideal, `1 - a` as a unit of the nonnegative subring. Its inverse is
the geometric series `∑ aⁿ` (`TauCeti.NovikovSeries.coe_inv_unitsOneSub`). -/
def unitsOneSub {a : nonnegSubring R N} (ha : a ∈ posIdeal R N) : (nonnegSubring R N)ˣ where
  val := 1 - a
  inv := ⟨∑' n : ℕ, (a : NovikovSeries R H N) ^ n, tsum_pow_mem_nonnegSubring a⟩
  val_inv := Subtype.ext <| by
    simpa using (isTopologicallyNilpotent_of_mem_posIdeal ha).summable_pow.one_sub_mul_tsum_pow
  inv_val := Subtype.ext <| by
    simpa using (isTopologicallyNilpotent_of_mem_posIdeal ha).summable_pow.tsum_pow_mul_one_sub

@[simp]
theorem val_unitsOneSub {a : nonnegSubring R N} (ha : a ∈ posIdeal R N) :
    (unitsOneSub ha : nonnegSubring R N) = 1 - a :=
  (rfl)

@[simp]
theorem coe_inv_unitsOneSub {a : nonnegSubring R N} (ha : a ∈ posIdeal R N) :
    ((↑(unitsOneSub ha)⁻¹ : nonnegSubring R N) : NovikovSeries R H N) =
      ∑' n : ℕ, (a : NovikovSeries R H N) ^ n :=
  (rfl)

/-- For `a` in the positive ideal, `1 - a` is a unit of the nonnegative subring. -/
theorem isUnit_one_sub_of_mem_posIdeal {a : nonnegSubring R N} (ha : a ∈ posIdeal R N) :
    IsUnit (1 - a) :=
  (unitsOneSub ha).isUnit

end Ring

section IsLeftCancelAdd

variable [AddZeroClass H] [IsLeftCancelAdd H] {N : H →+ ℝ} [Ring R]

/-- Multiplication by a monomial `u e^g` with unit coefficient shifts the period filtration by
`N g`: when exponents satisfy left cancellation, the coefficients of `single g u * a` vanish
below `N g + C` exactly when those of `a` vanish below `C`. -/
theorem single_mul_mem_periodFiltration_iff (g : H) (u : Rˣ) {C : ℝ}
    {a : NovikovSeries R H N} :
    single g (u : R) * a ∈ periodFiltration R N (N g + C) ↔ a ∈ periodFiltration R N C := by
  refine ⟨fun ha => ?_, mul_mem_periodFiltration (single_mem_periodFiltration g _)⟩
  refine mem_periodFiltration.2 fun h hh => ?_
  have hzero := mem_periodFiltration.1 ha (g + h) (by simpa using add_lt_add_left hh (N g))
  simpa only [coeff_single_mul_add, Units.mul_right_eq_zero] using hzero

end IsLeftCancelAdd

end NovikovSeries

end TauCeti
