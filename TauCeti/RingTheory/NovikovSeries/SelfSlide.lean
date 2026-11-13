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

For `k > 0`, reduction of an integral coordinate `f` modulo `d * k`, where `f h = d > 0`,
retains the multiple `k • h`. For a principal unit `u`, congruence of the norm over
this kernel to `1` below a cutoff strictly above `N (k • h)` kills the coefficient
of `log u` at `k • h`. When `f` is surjective, the norm's logarithmic coefficient
is exactly `d * k` times the original coefficient; elimination itself does not
require surjectivity.

Applying this for every `k ≥ 2`, together with vanishing of the `h`-coefficient,
eliminates a positive logarithmic series supported on the integer multiples of
`h`. In particular, a principal unit with such a logarithm is `1`. The cutoffs are
`2 * N (k • h)` when `N h > 0`. This is the algebraic elimination step;
the geometric source of the cover cutoffs and of the `h`-coefficient is separate.
The class need not be primitive, the ambient exponent group may have torsion,
and the commutative `ℚ`-algebra of coefficients may have zero divisors.

## References

* M. Hutchings, *Reidemeister torsion in generalized Morse theory*, Forum Math. 14
  (2002), §§3.4–3.5.
-/

public section

noncomputable section

namespace TauCeti.NovikovSeries

variable {R H : Type*} [CommRing R] [Algebra ℚ R] [AddCommGroup H]
  {N : H →+ ℝ} {f : H →+ ℤ} {d : ℕ} [NeZero d] {h : H}

/-- For a surjective integral coordinate, the norm over its reduction kernel modulo `n`
multiplies each logarithmic coefficient at a kernel exponent by the cover degree `n`. -/
theorem coeff_log_normNonnegSubring_ker_castZMod {n : ℕ} [NeZero n]
    (hf : Function.Surjective f) {u : nonnegSubring R N}
    (hu : u - 1 ∈ posIdeal R N) (x : (f.castZMod n).ker) :
    ((NormedSpace.log (normNonnegSubring (f.castZMod n).ker u) :
      nonnegSubring R (N.comp (f.castZMod n).ker.subtype)) :
      NovikovSeries R (f.castZMod n).ker (N.comp (f.castZMod n).ker.subtype)).coeff x =
        n • (NormedSpace.log u : nonnegSubring R N).val.coeff x := by
  rw [coeff_log_normNonnegSubring _ hu, f.index_ker_castZMod _ hf]

/-- A positive series supported on the integer multiples of a positive-period class `h`
vanishes if its `h`-coefficient is zero and, for every `k ≥ 2`, the norm of its exponential
in `(f.castZMod (d * k)).ker` agrees with `1` below `2 * N (k • h)`. -/
theorem eq_zero_of_forall_algebraNorm_exp_sub_one_mem_periodFiltration
    (hh : f h = d) (hpos : 0 < N h) {a : nonnegSubring R N} (ha : a ∈ posIdeal R N)
    (hsupp : (a : NovikovSeries R H N).support ⊆ (AddSubgroup.zmultiples h : Set H))
    (hfirst : (a : NovikovSeries R H N).coeff h = 0)
    (hcut : ∀ (k : ℕ) [NeZero k], 2 ≤ k →
      Algebra.norm (NovikovSeries R (f.castZMod (d * k)).ker
        (N.comp (f.castZMod (d * k)).ker.subtype))
        (NormedSpace.exp (a : NovikovSeries R H N)) - 1 ∈
          periodFiltration R (N.comp (f.castZMod (d * k)).ker.subtype)
            (2 * N (k • h))) :
    a = 0 := by
  have hnil := isTopologicallyNilpotent_of_mem_posIdeal' ha
  have hu : NormedSpace.exp a - 1 ∈ posIdeal R N := hnil.exp_sub_one_mem ha
  apply Subtype.ext
  ext g
  rw [Subring.coe_zero, coeff_zero]
  by_contra hg
  obtain ⟨z, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp (hsupp (mem_support.2 hg))
  have hzpos : 0 < z := by
    by_contra hz
    apply hg
    apply mem_posIdeal.1 ha
    rw [map_zsmul, zsmul_eq_mul]
    exact mul_nonpos_of_nonpos_of_nonneg (by exact_mod_cast (not_lt.1 hz)) hpos.le
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hzpos.le
  simp only [natCast_zsmul] at hg ⊢
  rcases n with _ | n
  · simp at hzpos
  · rcases n with _ | n
    · exact hg (by simpa using hfirst)
    · let : NeZero (n + 1 + 1) := ⟨by omega⟩
      have hperiod : 0 < N ((n + 1 + 1) • h) := by
        rw [map_nsmul, nsmul_eq_mul]
        exact mul_pos (by positivity) hpos
      have hz := coeff_log_eq_zero_of_algebraNorm_sub_one_mem_periodFiltration
        (f.castZMod (d * (n + 1 + 1))).ker hu
        ((f.nsmul_mem_ker_castZMod_iff hh (NeZero.ne d) (n + 1 + 1)).2 (dvd_refl _))
        (by linarith : N ((n + 1 + 1) • h) < 2 * N ((n + 1 + 1) • h))
        (by simpa only [coe_exp_nonnegSubring] using hcut (n + 1 + 1) (by omega))
      exact hg (by simpa only [hnil.log_exp] using hz)

/-- A principal unit is `1` if its logarithm is supported on the integer multiples of
`h`, has zero `h`-coefficient, and for every `k ≥ 2` its norm over
`(f.castZMod (d * k)).ker` agrees with `1` below `2 * N (k • h)`. -/
theorem eq_one_of_forall_algebraNorm_sub_one_mem_periodFiltration
    (hh : f h = d) (hpos : 0 < N h) {u : nonnegSubring R N}
    (hu : u - 1 ∈ posIdeal R N)
    (hsupp : ((NormedSpace.log u : nonnegSubring R N) : NovikovSeries R H N).support ⊆
      (AddSubgroup.zmultiples h : Set H))
    (hfirst : (NormedSpace.log u : nonnegSubring R N).val.coeff h = 0)
    (hcut : ∀ (k : ℕ) [NeZero k], 2 ≤ k →
      Algebra.norm (NovikovSeries R (f.castZMod (d * k)).ker
        (N.comp (f.castZMod (d * k)).ker.subtype)) (u : NovikovSeries R H N) - 1 ∈
          periodFiltration R (N.comp (f.castZMod (d * k)).ker.subtype)
            (2 * N (k • h))) :
    u = 1 := by
  have hnil := isTopologicallyNilpotent_of_mem_posIdeal' hu
  have hlog := eq_zero_of_forall_algebraNorm_exp_sub_one_mem_periodFiltration hh hpos
    (hnil.log_mem hu) hsupp hfirst (by
      intro k _ hk
      simpa only [← coe_exp_nonnegSubring, hnil.exp_log] using hcut k hk)
  rw [← hnil.exp_log, hlog, NormedSpace.exp_zero]

end TauCeti.NovikovSeries
