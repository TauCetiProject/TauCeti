/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.GCDMonoid.Finset
public import Mathlib.Algebra.GCDMonoid.Nat
public import Mathlib.Data.Int.Cast.Basic
public import Mathlib.LinearAlgebra.Span.Defs
-- Proof-only: Bézout's identity for `Finset.gcd` over the Euclidean domain `ℤ`.
import Mathlib.Algebra.EuclideanDomain.Int
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.Tactic.Ring

/-!
# Bézout's identity for a finite family of natural numbers

Natural numbers `f i`, `i ∈ s`, have greatest common divisor `1` in `ℕ` if and only if some
integer combination of them is `1`. Mathlib's `Finset.gcd_eq_sum_mul` gives the forward direction
for the gcd computed in `ℤ`; this file transfers it to the gcd in `ℕ`, where the hypothesis is
usually established, for instance by `Finset.gcd_div_eq_one`.

## Main results

* `Finset.gcd_eq_one_iff_exists_sum_natCast_mul_eq_one`: `s.gcd f = 1` in `ℕ` if and only if
  `∑ i ∈ s, f i * c i = 1` for some `c : ι → ℤ`.
* `TauCeti.forall_nat_mul_eq_iff_mem_span_div_gcd`: cross-product characterization of the
  `ℤ`-span of the primitive vector `i ↦ m i / gcd(m)` for any tuple `m : ι → ℕ` with a nonzero
  coordinate.
-/

public section

namespace Finset

/-- Bézout's identity for natural numbers: `f i`, `i ∈ s`, have greatest common divisor `1` if
and only if some integer combination `∑ i ∈ s, f i * c i` is `1`. -/
theorem gcd_eq_one_iff_exists_sum_natCast_mul_eq_one {ι : Type*} {s : Finset ι} {f : ι → ℕ} :
    s.gcd f = 1 ↔ ∃ c : ι → ℤ, ∑ i ∈ s, (f i : ℤ) * c i = 1 := by
  refine ⟨fun h => ?_, fun ⟨c, hc⟩ => ?_⟩
  · obtain ⟨c, hc⟩ := s.gcd_eq_sum_mul fun i => (f i : ℤ)
    refine ⟨c, hc ▸ Int.eq_one_of_dvd_one Int.finsetGcd_nonneg ?_⟩
    -- The gcd in `ℤ` divides every `f i`, hence also their gcd `1` in `ℕ`.
    rw [← Nat.cast_one, ← h]
    exact Int.dvd_natCast.2 <| Finset.dvd_gcd fun i hi => Int.dvd_natCast.1 (Finset.gcd_dvd hi)
  · -- The gcd in `ℕ` divides every `f i`, hence also the combination `1`.
    refine Nat.dvd_one.1 <| Int.natCast_dvd_natCast.1 ?_
    rw [Nat.cast_one, ← hc]
    exact Finset.dvd_sum fun i hi => (Int.natCast_dvd_natCast.2 (Finset.gcd_dvd hi)).mul_right _

end Finset

namespace TauCeti

/-- For natural numbers `m : ι → ℕ` on a finite index type with at least one nonzero entry, the
cross-product equations `m j * v i = m i * v j` hold for all `i, j` if and only if `v` lies in the
`ℤ`-span of the primitive vector `i ↦ m i / gcd(m)`. -/
theorem forall_nat_mul_eq_iff_mem_span_div_gcd {ι : Type*} [Fintype ι]
    (m : ι → ℕ) (hm : ∃ i, m i ≠ 0) (v : ι → ℤ) :
    (∀ i j, (m j : ℤ) * v i = (m i : ℤ) * v j) ↔
      v ∈ Submodule.span ℤ {fun i ↦ ((m i / Finset.univ.gcd m : ℕ) : ℤ)} := by
  set d : ℕ := Finset.univ.gcd m
  have hd_dvd (i : ι) : d ∣ m i := Finset.gcd_dvd (Finset.mem_univ i)
  have hd_ne : d ≠ 0 := by
    obtain ⟨i₀, hi₀⟩ := hm
    exact ne_zero_of_dvd_ne_zero hi₀ (hd_dvd i₀)
  have hd_ne_int : (d : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr hd_ne
  have hmul_div (i : ι) : (d : ℤ) * ((m i / d : ℕ) : ℤ) = (m i : ℤ) := by
    exact_mod_cast Nat.mul_div_cancel' (hd_dvd i)
  constructor
  · intro hv
    set dℤ : ℤ := Finset.univ.gcd (fun j : ι ↦ (m j : ℤ))
    have hdℤ_dvd : dℤ ∣ (d : ℤ) := Int.natAbs_dvd_natAbs.mp <| by
      rw [Int.natAbs_natCast]
      exact Finset.dvd_gcd fun j _ ↦ by
        simpa only [Int.natAbs_natCast] using
          Int.natAbs_dvd_natAbs.mpr (Finset.gcd_dvd (f := fun k ↦ (m k : ℤ)) (Finset.mem_univ j))
    obtain ⟨q, hq⟩ := hdℤ_dvd
    obtain ⟨g, hg⟩ := Finset.gcd_eq_sum_mul Finset.univ (fun j : ι ↦ (m j : ℤ))
    refine Submodule.mem_span_singleton.mpr ⟨∑ j : ι, v j * (g j * q), funext fun i ↦ ?_⟩
    simp only [Pi.smul_apply, smul_eq_mul]
    apply mul_left_cancel₀ hd_ne_int
    calc
      (d : ℤ) * ((∑ j : ι, v j * (g j * q)) * ((m i / d : ℕ) : ℤ))
          = (m i : ℤ) * ∑ j : ι, v j * (g j * q) := by
            rw [mul_comm (∑ j : ι, _), ← mul_assoc, hmul_div i]
      _ = ∑ j : ι, ((m i : ℤ) * v j) * (g j * q) := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun j _ ↦ by ring
      _ = ∑ j : ι, ((m j : ℤ) * v i) * (g j * q) := by
            exact Finset.sum_congr rfl fun j _ ↦ by rw [hv i j]
      _ = ((∑ j : ι, (m j : ℤ) * g j) * q) * v i := by
            rw [Finset.sum_mul, Finset.sum_mul]
            exact Finset.sum_congr rfl fun j _ ↦ by ring
      _ = (d : ℤ) * v i := by rw [← hg, ← hq]
  · intro hv i j
    rw [Submodule.mem_span_singleton] at hv
    obtain ⟨c, rfl⟩ := hv
    apply mul_left_cancel₀ hd_ne_int
    simp only [Pi.smul_apply, smul_eq_mul]
    calc
      (d : ℤ) * ((m j : ℤ) * (c * ((m i / d : ℕ) : ℤ)))
          = (m j : ℤ) * c * ((d : ℤ) * ((m i / d : ℕ) : ℤ)) := by ring
      _ = (m j : ℤ) * c * (m i : ℤ) := by rw [hmul_div i]
      _ = (m i : ℤ) * c * ((d : ℤ) * ((m j / d : ℕ) : ℤ)) := by
            rw [hmul_div j]; ring
      _ = (d : ℤ) * ((m i : ℤ) * (c * ((m j / d : ℕ) : ℤ))) := by ring

end TauCeti
