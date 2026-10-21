/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.NovikovSeries.Multiplication
public import TauCeti.RingTheory.NovikovSeries.Topology
public import Mathlib.Topology.Algebra.TopologicallyNilpotent

/-!
# Novikov series form a topological ring

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
(`TauCeti.NovikovSeries.mul_sub_mul_trunc_mem_periodFiltration`). Multiplying by a monomial unit
`u e^g` shifts the filtration by the period `N g`
(`TauCeti.NovikovSeries.single_mul_mem_periodFiltration_iff`).

## Main results

* `TauCeti.NovikovSeries.mul_mem_periodFiltration`: `U_C * U_D ⊆ U_(C + D)`.
* `TauCeti.NovikovSeries.mul_sub_mul_mem_periodFiltration` and
  `TauCeti.NovikovSeries.mul_sub_mul_trunc_mem_periodFiltration`: cutoff compatibility of the
  convolution.
* `TauCeti.NovikovSeries.single_mul_mem_periodFiltration_iff`: multiplication by a monomial unit
  shifts the period filtration.
* The instances `IsTopologicalRing` and `NonarchimedeanRing`: the period topology is a
  nonarchimedean ring topology.
* `TauCeti.NovikovSeries.pow_mem_periodFiltration` and
  `TauCeti.NovikovSeries.isTopologicallyNilpotent_of_mem_periodFiltration`: a series supported in
  periods `≥ C` has its `n`-th power supported in periods `≥ n • C`, so it is topologically
  nilpotent when `C > 0`.

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

/-- The period topology is a nonarchimedean ring topology. -/
instance : NonarchimedeanRing (NovikovSeries R H N) where
  is_nonarchimedean := NonarchimedeanAddGroup.is_nonarchimedean

/-- If the coefficients of `a` vanish below the period `C`, then those of `a ^ n` vanish below
`n • C`. -/
theorem pow_mem_periodFiltration (ha : a ∈ periodFiltration R N C) (n : ℕ) :
    a ^ n ∈ periodFiltration R N (n • C) := by
  induction n with
  | zero =>
    have h := single_mem_periodFiltration (R := R) (N := N) (0 : H) 1
    rwa [single_zero_one, map_zero] at h
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

end Ring

section Group

variable [AddGroup H] {N : H →+ ℝ} [Ring R]

/-- Multiplication by a monomial unit `u e^g` shifts the period filtration by `N g`: the
coefficients of `single g u * a` vanish below `N g + C` exactly when those of `a` vanish
below `C`. -/
theorem single_mul_mem_periodFiltration_iff (g : H) (u : Rˣ) {C : ℝ}
    {a : NovikovSeries R H N} :
    single g (u : R) * a ∈ periodFiltration R N (N g + C) ↔ a ∈ periodFiltration R N C := by
  refine ⟨fun ha => ?_, mul_mem_periodFiltration (single_mem_periodFiltration g _)⟩
  have h := mul_mem_periodFiltration (single_mem_periodFiltration (-g) (↑u⁻¹ : R)) ha
  rw [← mul_assoc] at h
  simpa [single_mul_single] using h

end Group

end NovikovSeries

end TauCeti
