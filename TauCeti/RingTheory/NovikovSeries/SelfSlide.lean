/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.SelfSlide.CyclicQuotient
public import TauCeti.RingTheory.NovikovSeries.Norm

/-!
# Logarithmic norm elimination for self-slides

A self-slide is a handle slide from a critical point to a translate of itself by a deck
class `h`. On an acyclic component, invariance of the product `τ * ζ` across such an event
reduces to showing that a principal unit is `1`. This unit is the product of the chain-torsion
and zeta change factors, namely the post-to-pre ratio of `τ * ζ`. Cyclic covers detect its
logarithmic coefficients: in the cover associated to `(f.castZMod (d * k)).ker`, where
`f h = d > 0`, lifted slides whose lift-index differences are not divisible by `k` connect
distinct critical points. The elimination theorems take the resulting norm comparisons as
cutoff hypotheses.

For `k > 0`, this kernel retains the multiple `k • h`. For a principal unit `u`, agreement
of the norm with `1` below a cutoff strictly above `N (k • h)` kills the coefficient of
`log u` at `k • h`. When `f` is surjective, the norm's logarithmic coefficient is exactly
`d * k` times the original coefficient; elimination itself does not require surjectivity.

Assume `0 < N h`. Applying this for every `k ≥ 2`, together with vanishing of the
`h`-coefficient, eliminates a positive logarithmic series supported on the integer multiples
of `h`. Such a series starts in filtration `2 * N h`; the same bound holds for `u - 1`
when a principal unit `u` is supported on these multiples and has zero `h`-coefficient.
The norm cutoffs then imply `u = 1`. Each cover may use any cutoff strictly above `N (k • h)`.
The class need not be primitive, the ambient exponent group may have torsion, and the
commutative `ℚ`-algebra of coefficients may have zero divisors.

## Main results

* `TauCeti.NovikovSeries.support_subset_nsmul_ge_two_of_mem_posIdeal`: removing the first
  coefficient of a positive cyclically supported series leaves only indices at least two.
* `TauCeti.NovikovSeries.mem_periodIdeal_two_mul_of_support_subset_zmultiples` and
  `TauCeti.NovikovSeries.sub_one_mem_periodIdeal_two_mul_of_support_subset_zmultiples`:
  the resulting filtration bounds for positive series and principal units.
* `TauCeti.NovikovSeries.coeff_log_algebraNorm_ker_castZMod`: the logarithmic coefficient
  formula for a surjective cyclic coordinate.
* `TauCeti.NovikovSeries.eq_zero_of_forall_algebraNorm_exp_sub_one_mem_periodFiltration`:
  elimination of a positive logarithmic series from its cyclic-cover norm cutoffs.
* `TauCeti.NovikovSeries.eq_one_of_forall_algebraNorm_sub_one_mem_periodFiltration`:
  a principal unit with vanishing `h`-coefficient and these norm cutoffs equals `1`.

## References

* M. Hutchings, *Reidemeister torsion in generalized Morse theory*, Forum Math. 14
  (2002), §§3.4–3.5.
-/

public section

noncomputable section

namespace TauCeti.NovikovSeries

section Ring

variable {R H : Type*} [Ring R] [AddGroup H] {N : H →+ ℝ} {h : H}

/-- A positive series supported on the integer multiples of a positive-period class, with
zero coefficient at that class, is supported on its natural multiples of index at least two. -/
theorem support_subset_nsmul_ge_two_of_mem_posIdeal
    (hpos : 0 < N h) {a : nonnegSubring R N} (ha : a ∈ posIdeal R N)
    (hsupp : (a : NovikovSeries R H N).support ⊆ (AddSubgroup.zmultiples h : Set H))
    (hfirst : (a : NovikovSeries R H N).coeff h = 0) :
    (a : NovikovSeries R H N).support ⊆ {g | ∃ k : ℕ, 2 ≤ k ∧ g = k • h} := by
  intro g hg
  obtain ⟨z, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp (hsupp hg)
  have hgcoeff := mem_support.1 hg
  have hzpos : 0 < z := by
    by_contra hz
    apply hgcoeff
    apply mem_posIdeal.1 ha
    rw [map_zsmul, zsmul_eq_mul]
    exact mul_nonpos_of_nonpos_of_nonneg (by exact_mod_cast (not_lt.1 hz)) hpos.le
  obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hzpos.le
  have hk : 2 ≤ k := by
    have hkpos : 0 < k := by exact_mod_cast hzpos
    have hkne : k ≠ 1 := by
      rintro rfl
      exact hgcoeff (by simpa using hfirst)
    omega
  exact ⟨k, hk, by simp⟩

/-- Removing the first coefficient of a positive series with cyclic support raises its
period-filtration bound to twice the positive generator period. -/
theorem mem_periodIdeal_two_mul_of_support_subset_zmultiples
    (hpos : 0 < N h) {a : nonnegSubring R N} (ha : a ∈ posIdeal R N)
    (hsupp : (a : NovikovSeries R H N).support ⊆ (AddSubgroup.zmultiples h : Set H))
    (hfirst : (a : NovikovSeries R H N).coeff h = 0) :
    a ∈ periodIdeal R N (2 * N h) := by
  apply mem_periodIdeal.2
  refine mem_periodFiltration.2 fun g hg => ?_
  by_contra hcoeff
  obtain ⟨k, hk, rfl⟩ :=
    support_subset_nsmul_ge_two_of_mem_posIdeal hpos ha hsupp hfirst (mem_support.2 hcoeff)
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hperiod : N (k • h) = (k : ℝ) * N h := by simp
  nlinarith

/-- A principal unit with cyclic support and zero first coefficient differs from `1` only
in periods at least twice the positive generator period. -/
theorem sub_one_mem_periodIdeal_two_mul_of_support_subset_zmultiples
    (hpos : 0 < N h) {u : nonnegSubring R N} (hu : u - 1 ∈ posIdeal R N)
    (hsupp : (u : NovikovSeries R H N).support ⊆ (AddSubgroup.zmultiples h : Set H))
    (hfirst : (u : NovikovSeries R H N).coeff h = 0) :
    u - 1 ∈ periodIdeal R N (2 * N h) := by
  have hhne : h ≠ 0 := by rintro rfl; simp at hpos
  apply mem_periodIdeal_two_mul_of_support_subset_zmultiples hpos hu
  · intro g hg
    have hsub := support_sub_subset (u : NovikovSeries R H N) 1 hg
    rcases hsub with hgu | hg1
    · exact hsupp hgu
    · have hgzero : g = 0 := by
        by_contra hne
        exact (mem_support.1 hg1) (by rw [one_def, coeff_single_of_ne hne])
      simpa only [hgzero, SetLike.mem_coe] using (AddSubgroup.zmultiples h).zero_mem
  · rw [AddSubgroupClass.coe_sub, Subring.coe_one, coeff_sub, hfirst,
      one_def, coeff_single_of_ne hhne, sub_zero]

end Ring

variable {R H : Type*} [CommRing R] [Algebra ℚ R] [AddCommGroup H]
  {N : H →+ ℝ} {f : H →+ ℤ} {d : ℕ} [NeZero d] {h : H}

/-- For a principal unit over a commutative `ℚ`-algebra and a surjective integral coordinate,
the norm over its reduction kernel modulo a positive `n` multiplies each logarithmic
coefficient at a kernel exponent by the cover degree `n`. -/
theorem coeff_log_algebraNorm_ker_castZMod {n : ℕ} [NeZero n]
    (hf : Function.Surjective f) {u : nonnegSubring R N}
    (hu : u - 1 ∈ posIdeal R N) (x : (f.castZMod n).ker) :
    (NormedSpace.log (Algebra.norm
      (NovikovSeries R (f.castZMod n).ker (N.comp (f.castZMod n).ker.subtype))
      (u : NovikovSeries R H N))).coeff x =
        n • (NormedSpace.log (u : NovikovSeries R H N)).coeff x := by
  rw [coeff_log_algebraNorm _ hu, f.index_ker_castZMod _ hf]

/-- Over a commutative `ℚ`-algebra, let `f h = d > 0` and `0 < N h`. A positive series
supported on the integer multiples of `h` vanishes if its `h`-coefficient is zero and, for
every `k ≥ 2`, the norm of its exponential in `(f.castZMod (d * k)).ker` agrees with `1`
below some cutoff strictly above `N (k • h)`. -/
theorem eq_zero_of_forall_algebraNorm_exp_sub_one_mem_periodFiltration
    (hh : f h = d) (hpos : 0 < N h) {a : nonnegSubring R N} (ha : a ∈ posIdeal R N)
    (hsupp : (a : NovikovSeries R H N).support ⊆ (AddSubgroup.zmultiples h : Set H))
    (hfirst : (a : NovikovSeries R H N).coeff h = 0)
    (hcut : ∀ k : ℕ, 2 ≤ k → ∃ C > N (k • h),
      Algebra.norm (NovikovSeries R (f.castZMod (d * k)).ker
        (N.comp (f.castZMod (d * k)).ker.subtype))
        (NormedSpace.exp (a : NovikovSeries R H N)) - 1 ∈
          periodFiltration R (N.comp (f.castZMod (d * k)).ker.subtype) C) :
    a = 0 := by
  have hnil := isTopologicallyNilpotent_of_mem_posIdeal' ha
  have hu : NormedSpace.exp a - 1 ∈ posIdeal R N := hnil.exp_sub_one_mem ha
  apply Subtype.ext
  ext g
  rw [Subring.coe_zero, coeff_zero]
  by_contra hg
  obtain ⟨k, hk, rfl⟩ :=
    support_subset_nsmul_ge_two_of_mem_posIdeal hpos ha hsupp hfirst (mem_support.2 hg)
  let : NeZero k := ⟨by omega⟩
  obtain ⟨C, hC, hcutC⟩ := hcut k hk
  have hz := coeff_log_eq_zero_of_algebraNorm_sub_one_mem_periodFiltration
    (f.castZMod (d * k)).ker hu
    ((f.nsmul_mem_ker_castZMod_iff hh (NeZero.ne d) k).2 (dvd_refl _))
    hC (by simpa only [coe_exp_nonnegSubring] using hcutC)
  exact hg (by simpa only [← coe_log_nonnegSubring, hnil.log_exp] using hz)

/-- Over a commutative `ℚ`-algebra, let `f h = d > 0` and `0 < N h`. A principal unit `u`
is `1` if `u` is supported on the integer multiples of `h`, its `h`-coefficient is zero,
and for every `k ≥ 2` its norm over `(f.castZMod (d * k)).ker` agrees with `1` below some
cutoff strictly above `N (k • h)`. -/
theorem eq_one_of_forall_algebraNorm_sub_one_mem_periodFiltration
    (hh : f h = d) (hpos : 0 < N h) {u : nonnegSubring R N}
    (hu : u - 1 ∈ posIdeal R N)
    (hsupp : (u : NovikovSeries R H N).support ⊆ (AddSubgroup.zmultiples h : Set H))
    (hfirst : (u : NovikovSeries R H N).coeff h = 0)
    (hcut : ∀ k : ℕ, 2 ≤ k → ∃ C > N (k • h),
      Algebra.norm (NovikovSeries R (f.castZMod (d * k)).ker
        (N.comp (f.castZMod (d * k)).ker.subtype)) (u : NovikovSeries R H N) - 1 ∈
          periodFiltration R (N.comp (f.castZMod (d * k)).ker.subtype) C) :
    u = 1 := by
  have hnil := isTopologicallyNilpotent_of_mem_posIdeal' hu
  have hcutfirst :=
    sub_one_mem_periodIdeal_two_mul_of_support_subset_zmultiples hpos hu hsupp hfirst
  have hlogfirst : (NormedSpace.log u : nonnegSubring R N).val.coeff h = 0 :=
    mem_periodFiltration.1 (mem_periodIdeal.1 (hnil.log_mem hcutfirst)) h (by linarith)
  have hlog := eq_zero_of_forall_algebraNorm_exp_sub_one_mem_periodFiltration hh hpos
    (hnil.log_mem hu) (by
      simpa only [coe_log_nonnegSubring] using
        support_log_subset (u : NovikovSeries R H N)
          (S := AddSubgroup.zmultiples h) hsupp)
    hlogfirst (by
      intro k hk
      obtain ⟨C, hC, hcutC⟩ := hcut k hk
      exact ⟨C, hC, by
        simpa only [← coe_exp_nonnegSubring, hnil.exp_log] using hcutC⟩)
  rw [← hnil.exp_log, hlog, NormedSpace.exp_zero]

end TauCeti.NovikovSeries
