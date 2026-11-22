/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Monoid.Submonoid
public import Mathlib.RingTheory.Localization.FractionRing
public import TauCeti.RingTheory.NovikovSeries.Field

/-!
# Novikov series as a localization of the nonnegative subring

Every monomial `e^m` is a unit of the ring of Novikov series, and every Novikov series lies in
the nonnegative subring `Λ₀` after multiplication by a monomial whose period is at least minus
its order. So the full ring of Novikov series is the localization of `Λ₀` at the monomials it
contains, and already at the monomials `e^m` with `m` in any additive submonoid `M` of exponents
whose periods dominate every period of `H`.

The main example is the action-weighted exponent group `G × ℝ` with periods
`(g, r) ↦ E g + r`, where `M` consists of the classes `(0, r)` with `r ≥ 0`. Their monomials
`T^r = e^(0, r)` have degree zero for any grading pulled back from `G`, so inverting them passes
from the energy-filtered ring `Λ₀` to the full coefficient ring without changing degrees. Over
nontrivial coefficients the monomials of positive period are not units of `Λ₀`, since they lie
in the proper ideal `TauCeti.NovikovSeries.posIdeal` (`TauCeti.NovikovSeries.posIdeal_ne_top`), so
this localization genuinely enlarges `Λ₀`: a contraction or an isomorphism over the localized ring
need not come from one over `Λ₀`.

When the coefficients form a field and the period map is injective, the Novikov ring is a field,
and it is then the field of fractions of `Λ₀`; for the real exponent group with the identity
period map this is the field of real-exponent Novikov series.

The statements and their proofs parallel Mathlib's localization of power series at `X`,
`LaurentSeries.of_powerSeries_localization`, and its instance `IsFractionRing K⟦X⟧ K⸨X⸩` in
`Mathlib/RingTheory/LaurentSeries.lean`; the role of the powers of `X` is played here by
monomials of nonnegative, possibly non-integral, period.

## Main definitions

* `TauCeti.NovikovSeries.monomialSubmonoid R N M`: the monomials `e^m`, `m ∈ M`, lying in the
  nonnegative subring, as a submonoid of it.

## Main results

* `TauCeti.NovikovSeries.isLocalization_monomialSubmonoid`: if every period of `H` is at most the
  period of some `m ∈ M`, then the Novikov series are the localization of the nonnegative
  subring at the monomials of `M`.
* `TauCeti.NovikovSeries.isLocalization_monomialSubmonoid_top` (instance): the Novikov series
  are the localization of the nonnegative subring at all monomials it contains.
* `TauCeti.NovikovSeries.isLocalization_monomialSubmonoid_map_inr` (instance): on the exponent
  group `G × ℝ` with periods `(g, r) ↦ E g + r`, the Novikov series are the localization of the
  nonnegative subring at the monomials `T^r = e^(0, r)`, `r ≥ 0`.
* `TauCeti.NovikovSeries.monomialSubmonoid_le_nonZeroDivisors`: monomials are non-zero-divisors
  of the nonnegative subring.
* `TauCeti.NovikovSeries.isFractionRing_nonnegSubring`: over a field, with injective periods,
  the Novikov series form the field of fractions of the nonnegative subring.

## References

* K. Fukaya, Y.-G. Oh, H. Ohta and K. Ono, *Lagrangian intersection Floer theory: anomaly and
  obstruction, Part I*, AMS/IP Studies in Advanced Mathematics 46.1, 2009 (the universal Novikov
  ring `Λ₀` and the ring `Λ` obtained by inverting its monomials).
-/

public section

noncomputable section

namespace TauCeti.NovikovSeries

variable {R H : Type*}

section Ring

variable [Ring R] [AddMonoid H] {N : H →+ ℝ}

variable (R N) in
/-- The monomials `e^m` with exponent `m` in an additive submonoid `M` that lie in the
nonnegative subring, as a submonoid of it. When `M` consists of exponents of nonnegative period,
these are all the monomials `e^m`, `m ∈ M`. -/
def monomialSubmonoid (M : AddSubmonoid H) : Submonoid (nonnegSubring R N) where
  carrier := {a | ∃ m ∈ M, (a : NovikovSeries R H N) = single m 1}
  one_mem' := ⟨0, M.zero_mem, by simp⟩
  mul_mem' := by
    rintro a b ⟨m, hm, ha⟩ ⟨m', hm', hb⟩
    exact ⟨m + m', M.add_mem hm hm', by simp [ha, hb]⟩

@[simp]
theorem mem_monomialSubmonoid {M : AddSubmonoid H} {a : nonnegSubring R N} :
    a ∈ monomialSubmonoid R N M ↔ ∃ m ∈ M, (a : NovikovSeries R H N) = single m 1 :=
  Iff.rfl

/-- A monomial `e^m` with `m ∈ M` of nonnegative period belongs to `monomialSubmonoid R N M`. -/
theorem single_mem_monomialSubmonoid {M : AddSubmonoid H} {m : H} (hm : m ∈ M) (hm₀ : 0 ≤ N m) :
    (⟨single m 1, single_mem_nonnegSubring hm₀ 1⟩ : nonnegSubring R N) ∈
      monomialSubmonoid R N M :=
  ⟨m, hm, rfl⟩

end Ring

section AddGroup

variable [Ring R] [AddGroup H] {N : H →+ ℝ}

/-- Monomials are non-zero-divisors of the nonnegative subring, being units of the full ring of
Novikov series. -/
theorem monomialSubmonoid_le_nonZeroDivisors (M : AddSubmonoid H) :
    monomialSubmonoid R N M ≤ nonZeroDivisors (nonnegSubring R N) := by
  rintro a ⟨m, -, ha⟩
  refine mem_nonZeroDivisors_of_injective (f := (nonnegSubring R N).subtype)
    Subtype.val_injective ?_
  rw [Subring.subtype_apply, ha]
  exact (isUnit_single m isUnit_one).isRegular.mem_nonZeroDivisors

end AddGroup

section CommRing

variable [CommRing R] [AddCommGroup H] {N : H →+ ℝ}

/-- **Novikov series as a localization.** Let `M` be an additive submonoid of exponents whose
periods dominate those of `H`: every `h : H` has some `m ∈ M` with `N h ≤ N m`. Then the ring of
Novikov series is the localization of the nonnegative subring at the monomials `e^m`, `m ∈ M`:
every series lies in the nonnegative subring after multiplication by such a monomial. -/
theorem isLocalization_monomialSubmonoid {M : AddSubmonoid H} (hM : ∀ h, ∃ m ∈ M, N h ≤ N m) :
    IsLocalization (monomialSubmonoid R N M) (NovikovSeries R H N) := by
  refine (isLocalization_iff _ _).2
    ⟨?_, fun z => ?_, fun {x y} hxy => ⟨1, by simpa using Subtype.ext hxy⟩⟩
  · rintro ⟨a, m, -, ha⟩
    rw [Algebra.algebraMap_ofSubsemiring_apply, ha]
    exact isUnit_single m isUnit_one
  by_cases hz : z ∈ nonnegSubring R N
  · exact ⟨(⟨z, hz⟩, 1), by simp [Algebra.algebraMap_ofSubsemiring_apply]⟩
  have hz₀ : z ≠ 0 := by
    rintro rfl
    exact hz (zero_mem _)
  have hzC : z ∈ periodFiltration R N z.order := (mem_periodFiltration_iff_le_order hz₀).2 le_rfl
  have horder : z.order < 0 := lt_of_not_ge fun h =>
    hz (mem_nonnegSubring.2 (mem_periodFiltration.1 (antitone_periodFiltration h hzC)))
  -- Multiply by a monomial `e^m`, `m ∈ M`, whose period dominates that of `-g`, where `g` is a
  -- support exponent of least period `z.order`.
  obtain ⟨g, -, hg⟩ := exists_coeff_ne_zero_and_period_eq_order hz₀
  obtain ⟨m, hmM, hm⟩ := hM (-g)
  rw [map_neg, hg] at hm
  have hmz : single m 1 * z ∈ periodFiltration R N (N m + z.order) := by
    rw [← Units.val_one]
    exact (single_mul_mem_periodFiltration_iff m 1).2 hzC
  replace hmz : single m 1 * z ∈ periodFiltration R N 0 :=
    antitone_periodFiltration (by linarith) hmz
  refine ⟨(⟨single m 1 * z, mem_nonnegSubring.2 (mem_periodFiltration.1 hmz)⟩,
    ⟨_, single_mem_monomialSubmonoid hmM (by linarith)⟩), ?_⟩
  simp [Algebra.algebraMap_ofSubsemiring_apply, mul_comm]

/-- The ring of Novikov series is the localization of the nonnegative subring at all the
monomials it contains. -/
instance isLocalization_monomialSubmonoid_top :
    IsLocalization (monomialSubmonoid R N ⊤) (NovikovSeries R H N) :=
  isLocalization_monomialSubmonoid fun h => ⟨h, AddSubmonoid.mem_top h, le_rfl⟩

/-- **Action-weighted localization.** On the exponent group `G × ℝ` with periods
`(g, r) ↦ E g + r`, the ring of Novikov series is the localization of its nonnegative subring at
the monomials `T^r = e^(0, r)`, `r ≥ 0`. -/
instance isLocalization_monomialSubmonoid_map_inr {G : Type*} [AddCommGroup G] (E : G →+ ℝ) :
    IsLocalization
      (monomialSubmonoid R (E.coprod (AddMonoidHom.id ℝ))
        ((AddSubmonoid.nonneg ℝ).map (AddMonoidHom.inr G ℝ)))
      (NovikovSeries R (G × ℝ) (E.coprod (AddMonoidHom.id ℝ))) :=
  isLocalization_monomialSubmonoid fun h =>
    ⟨(0, max (E h.1 + h.2) 0), ⟨_, le_max_right _ _, rfl⟩, by simp⟩

/-- **The Novikov field as a field of fractions.** Over a field, with an injective period map, the
ring of Novikov series is the field of fractions of its nonnegative subring. The injectivity
cannot be dropped: for `H = ℤ` and `N = 0` the nonnegative subring is the whole Laurent polynomial
ring, in which `1 - e^1` is not invertible. -/
theorem isFractionRing_nonnegSubring {K : Type*} [Field K] (hN : Function.Injective N) :
    IsFractionRing (nonnegSubring K N) (NovikovSeries K H N) :=
  IsLocalization.of_le (monomialSubmonoid K N ⊤) _ (monomialSubmonoid_le_nonZeroDivisors ⊤)
    fun a ha => isUnit_of_injective hN
      (by simpa [Algebra.algebraMap_ofSubsemiring_apply] using nonZeroDivisors.ne_zero ha)

end CommRing

end TauCeti.NovikovSeries
