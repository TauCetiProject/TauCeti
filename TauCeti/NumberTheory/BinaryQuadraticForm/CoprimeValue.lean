/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.BinaryQuadraticForm.Content
import Mathlib.RingTheory.Int.Basic
import TauCeti.RingTheory.UniqueFactorizationDomain.SubsetProduct

/-!
# Values of integral binary quadratic forms coprime to a modulus

A primitive integral form properly represents an integer coprime to any prescribed nonzero
modulus (`IsPrimitive.exists_isCoprime_eval`, Cox Lemma 2.25). For a general integral form,
representing such an integer is equivalent to its content being coprime to the modulus
(`exists_isCoprime_eval_iff`).

## References

* D. A. Cox, *Primes of the Form x² + ny²*, §2, Lemma 2.25.
-/

public section

open UniqueFactorizationMonoid

namespace TauCeti.BinaryQuadraticForm

/-! ### Values prime to a given integer -/

section CoprimeValue

/-- **A primitive form properly represents an integer prime to any given nonzero integer**
(Cox, Lemma 2.25). -/
theorem IsPrimitive.exists_isCoprime_eval {f : BinaryQuadraticForm ℤ} (hf : f.IsPrimitive)
    {M : ℤ} (hM : M ≠ 0) : ∃ x y : ℤ, IsCoprime x y ∧ IsCoprime (f.eval x y) M := by
  classical
  -- `y` collects the primes `p ∣ M` with `p ∤ a`, and `x` those with `p ∣ a` and `p ∤ c`.
  set y := ∏ q ∈ (primeFactors M).filter (fun q ↦ ¬ q ∣ f.a), q
  set x := ∏ q ∈ (primeFactors M).filter (fun q ↦ q ∣ f.a ∧ ¬ q ∣ f.c), q
  have hy {p : ℤ} (hp : Prime p) : p ∣ y ↔ p ∣ M ∧ ¬ p ∣ f.a :=
    prime_dvd_prod_filter_primeFactors_iff hM hp _ fun h ↦ not_congr h.dvd_iff_dvd_left
  have hx {p : ℤ} (hp : Prime p) : p ∣ x ↔ p ∣ M ∧ p ∣ f.a ∧ ¬ p ∣ f.c :=
    prime_dvd_prod_filter_primeFactors_iff hM hp _ fun h ↦
      and_congr h.dvd_iff_dvd_left (not_congr h.dvd_iff_dvd_left)
  have hy0 : y ≠ 0 := Finset.prod_ne_zero_iff.mpr fun q hq ↦
    (prime_of_normalized_factor q (mem_primeFactors.mp (Finset.mem_filter.mp hq).1)).ne_zero
  refine ⟨x, y, isCoprime_of_prime_dvd (fun h ↦ hy0 h.2) fun p hp hpx hpy ↦
    ((hy hp).mp hpy).2 ((hx hp).mp hpx).2.1, isCoprime_of_prime_dvd (fun h ↦ hM h.2)
    fun p hp hpv hpM ↦ ?_⟩
  obtain ⟨u, v, w, huvw⟩ := hf.exists_linearCombination_eq_one
  rw [eval_def] at hpv
  by_cases ha : p ∣ f.a
  · by_cases hc : p ∣ f.c
    · -- `p` divides `a` and `c`, hence not `b`, `x` or `y`; but it divides `bxy`.
      have hpx : ¬ p ∣ x := fun h ↦ ((hx hp).mp h).2.2 hc
      have hpy : ¬ p ∣ y := fun h ↦ ((hy hp).mp h).2 ha
      have hb : p ∣ f.b * x * y :=
        (dvd_add_right (ha.mul_right _)).mp ((dvd_add_left (hc.mul_right _)).mp hpv)
      have hpb : p ∣ f.b := by
        rcases hp.dvd_or_dvd hb with h | h
        · exact (hp.dvd_or_dvd h).resolve_right hpx
        · exact absurd h hpy
      exact hp.not_dvd_one (huvw ▸ dvd_add (dvd_add (ha.mul_left u) (hpb.mul_left v))
        (hc.mul_left w))
    · -- `p` divides `a` and `x` but not `c` or `y`; but it divides `cy²`.
      have hpx : p ∣ x := (hx hp).mpr ⟨hpM, ha, hc⟩
      have hpy : ¬ p ∣ y := fun h ↦ ((hy hp).mp h).2 ha
      have h : p ∣ f.c * y ^ 2 :=
        (dvd_add_right (dvd_add (ha.mul_right _) ((hpx.mul_left f.b).mul_right y))).mp hpv
      rcases hp.dvd_or_dvd h with h | h
      · exact hc h
      · exact hpy (hp.dvd_of_dvd_pow h)
  · -- `p` divides `y` but not `a` or `x`; but it divides `ax²`.
    have hpy : p ∣ y := (hy hp).mpr ⟨hpM, ha⟩
    have hpx : ¬ p ∣ x := fun h ↦ ha ((hx hp).mp h).2.1
    have h : p ∣ f.a * x ^ 2 := (dvd_add_left (hpy.mul_left (f.b * x))).mp
      ((dvd_add_left ((hpy.pow two_ne_zero).mul_left f.c)).mp hpv)
    rcases hp.dvd_or_dvd h with h | h
    · exact ha h
    · exact hpx (hp.dvd_of_dvd_pow h)

/-- An integral form represents a value coprime to a nonzero modulus exactly when
its content is coprime to the modulus. -/
theorem exists_isCoprime_eval_iff (f : BinaryQuadraticForm ℤ) {M : ℤ} (hM : M ≠ 0) :
    (∃ x y : ℤ, IsCoprime (f.eval x y) M) ↔ IsCoprime (f.content : ℤ) M := by
  have heval (x y : ℤ) : f.eval x y = (f.content : ℤ) * f.primPart.eval x y := by
    simpa only [f.content_smul_primPart, nsmul_eq_mul] using f.primPart.eval_nsmul f.content x y
  constructor
  · rintro ⟨x, y, hxy⟩
    rw [heval, IsCoprime.mul_left_iff] at hxy
    exact hxy.1
  · intro h
    by_cases hf : f = 0
    · exact ⟨0, 0, by simpa [hf] using h⟩
    obtain ⟨x, y, -, hxy⟩ := (f.isPrimitive_primPart hf).exists_isCoprime_eval hM
    exact ⟨x, y, heval x y ▸ h.mul_left hxy⟩

end CoprimeValue

end TauCeti.BinaryQuadraticForm
