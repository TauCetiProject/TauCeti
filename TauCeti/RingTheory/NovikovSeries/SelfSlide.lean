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

For a positive-period slide class `h` and a surjective integral coordinate `f` with
`f h = d > 0`, reduction of `f` modulo `d * k` defines a cover of degree `d * k`.
The logarithm of the norm of a principal unit has coefficient at `k • h` equal to
`(d * k) • (log u).coeff (k • h)`. Thus vanishing below twice the period of `k • h`
eliminates its `k`-th logarithmic coefficient over any commutative `ℚ`-algebra.

Applying this separately for every `k ≥ 2`, together with the vanishing leading
coefficient, eliminates a logarithmic series supported on the positive multiples of
`h`. Its exponential is consequently `1`. This is the algebraic elimination step;
the geometric source of the cover cutoffs and of the leading coefficient is separate.
The factor `d` is retained, so the class need not be primitive, and the ambient
exponent group may have torsion.

## References

* M. Hutchings, *Reidemeister torsion in generalized Morse theory*, Forum Math. 14
  (2002), §§3.4–3.5.
-/

public section

noncomputable section

namespace TauCeti.NovikovSeries

variable {R H : Type*} [CommRing R] [Algebra ℚ R] [AddCommGroup H]
  {N : H →+ ℝ} {f : H →+ ℤ} {d k : ℕ} [NeZero d] [NeZero k]
  {h : H}

/-- The logarithmic norm in the degree `d * k` cyclic cover detects the coefficient
at `k • h` with the full cover degree, including the divisibility `d`. -/
theorem coeff_log_normNonnegSubring_castZMod
    (hf : Function.Surjective f) (hh : f h = d) {u : nonnegSubring R N}
    (hu : u - 1 ∈ posIdeal R N) :
    ((NormedSpace.log (normNonnegSubring (f.castZMod (d * k)).ker u) :
      nonnegSubring R (N.comp (f.castZMod (d * k)).ker.subtype)) :
      NovikovSeries R (f.castZMod (d * k)).ker
        (N.comp (f.castZMod (d * k)).ker.subtype)).coeff
      ⟨k • h, (f.nsmul_mem_ker_castZMod_iff hh (NeZero.ne d) k).2 (dvd_refl k)⟩ =
        (d * k) • (NormedSpace.log u : nonnegSubring R N).val.coeff (k • h) := by
  rw [log_normNonnegSubring _ hu,
    trace_eq_index_smul_comap (exists_period_rescale_subtype _) (by simp),
    coeff_smul, coeff_comap, f.index_ker_castZMod _ hf, AddSubgroup.subtype_apply]

/-- If the norm of a principal unit is `1` below a cutoff strictly above the
period of `k • h`, its `k`-th logarithmic coefficient vanishes. Rational scalars
make multiplication by the cover degree injective even with zero divisors. -/
theorem coeff_log_eq_zero_of_norm_sub_one_mem_periodFiltration
    (hf : Function.Surjective f) (hh : f h = d) {u : nonnegSubring R N}
    (hu : u - 1 ∈ posIdeal R N) {C : ℝ} (hC : N (k • h) < C)
    (hcut : (normNonnegSubring (f.castZMod (d * k)).ker u :
      NovikovSeries R (f.castZMod (d * k)).ker
        (N.comp (f.castZMod (d * k)).ker.subtype)) - 1 ∈
      periodFiltration R (N.comp (f.castZMod (d * k)).ker.subtype) C) :
    (NormedSpace.log u : nonnegSubring R N).val.coeff (k • h) = 0 := by
  let K := (f.castZMod (d * k)).ker
  have hv : normNonnegSubring K u - 1 ∈ posIdeal R (N.comp K.subtype) := by
    simpa using normNonnegSubring_one_add_sub_one_mem_posIdeal K hu
  have hlogcut : (NormedSpace.log (normNonnegSubring K u) :
      nonnegSubring R (N.comp K.subtype)) ∈ periodIdeal R (N.comp K.subtype) C :=
    (isTopologicallyNilpotent_of_mem_posIdeal' hv).log_mem
      (I := periodIdeal R (N.comp K.subtype) C)
        (mem_periodIdeal.2 (by
          rw [sub_eq_add_neg, Subring.coe_add, Subring.coe_neg, Subring.coe_one]
          simpa only [sub_eq_add_neg] using hcut))
  have hz := mem_periodFiltration.1 (mem_periodIdeal.1 hlogcut)
    ⟨k • h, (f.nsmul_mem_ker_castZMod_iff hh (NeZero.ne d) k).2 (dvd_refl k)⟩ hC
  rw [coeff_log_normNonnegSubring_castZMod (f := f) hf hh hu] at hz
  let : HasUniqueDiv R := HasUniqueDiv.of_module_rat R
  exact (nsmul_right_injective (NeZero.ne (d * k))) (by simpa using hz)

omit [NeZero k] in
/-- All-order logarithmic norm elimination. A series supported on the nonnegative
multiples of `h`, in the positive ideal and with zero leading coefficient, has
exponential `1` if every elimination-cover norm is `1` below twice the period of
its first retained multiple. No integral-domain assumption on coefficients or
torsion-freeness assumption on exponents is needed. -/
theorem exp_eq_one_of_forall_norm_exp_sub_one_mem_twice_period
    (hf : Function.Surjective f) (hh : f h = d) (hpos : 0 < N h)
    (a : posIdeal R N)
    (hsupp : (a : NovikovSeries R H N).support ⊆ Set.range (fun n : ℕ => n • h))
    (hfirst : (a : NovikovSeries R H N).coeff h = 0)
    (hcut : ∀ (k : ℕ) [NeZero k], 2 ≤ k →
      (normNonnegSubring (f.castZMod (d * k)).ker
        (NormedSpace.exp (a : nonnegSubring R N)) :
        NovikovSeries R (f.castZMod (d * k)).ker
          (N.comp (f.castZMod (d * k)).ker.subtype)) - 1 ∈
        periodFiltration R (N.comp (f.castZMod (d * k)).ker.subtype)
          (2 * N (k • h))) :
    NormedSpace.exp (a : NovikovSeries R H N) = 1 := by
  have hnil := isTopologicallyNilpotent_of_mem_posIdeal' a.2
  have hu : NormedSpace.exp (a : nonnegSubring R N) - 1 ∈ posIdeal R N :=
    hnil.exp_sub_one_mem a.2
  have ha : (a : NovikovSeries R H N) = 0 := by
    ext g
    rw [coeff_zero]
    by_contra hg
    obtain ⟨n, rfl⟩ := hsupp (mem_support.2 hg)
    rcases n with _ | n
    · exact hg (by simpa using mem_posIdeal.1 a.2 0 (by simp))
    · rcases n with _ | n
      · exact hg (by simpa using hfirst)
      · let : NeZero (n + 1 + 1) := ⟨by omega⟩
        have hperiod : 0 < N ((n + 1 + 1) • h) := by
          rw [map_nsmul, nsmul_eq_mul]
          exact mul_pos (by positivity) hpos
        have hz := coeff_log_eq_zero_of_norm_sub_one_mem_periodFiltration
          (f := f) hf hh hu (by linarith : N ((n + 1 + 1) • h) <
            2 * N ((n + 1 + 1) • h)) (hcut (n + 1 + 1) (by omega))
        exact hg (by simpa only [hnil.log_exp] using hz)
  rw [ha, NormedSpace.exp_zero]

end TauCeti.NovikovSeries
