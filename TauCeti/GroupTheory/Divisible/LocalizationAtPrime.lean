/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Submodule.Pointwise
public import Mathlib.Algebra.Regular.SMul
public import TauCeti.GroupTheory.Divisible.MaxDivisible

import TauCeti.RingTheory.Regular.IsSMulRegular

/-!
# Divisibility of modules over `ℤ_(p)`

Let `p` be a prime and `R` a `ℤ_(p)`-algebra, that is a ring in which the integers prime to `p`
are units. Every `R`-module on which `p` acts bijectively is uniquely divisible, i.e. a `ℚ`-vector
space (`TauCeti.bijective_nsmul_of_bijective_smul_prime`). If `p` is regular on an `R`-module `M`,
the maximal divisible subgroup `Div(M)` of `M` is `⋂ₙ pⁿ M`
(`TauCeti.AddCommGroup.maxDivisible_eq_toAddSubgroup_iInf_pow_smul_top`), the kernel of the map to
the `(p)`-adic completion (`AdicCompletion.ker_of_span_singleton`).

## Main results

* `TauCeti.bijective_nsmul_of_bijective_smul_prime`: over a `ℤ_(p)`-algebra, a module on which `p`
  acts bijectively is uniquely divisible.
* `TauCeti.AddCommGroup.maxDivisible_eq_toAddSubgroup_iInf_pow_smul_top`: over a `ℤ_(p)`-algebra,
  `Div(M) = ⋂ₙ pⁿ M` for `p`-torsion-free `M`.

## References

* C. Weibel, *The K-book: an introduction to algebraic K-theory*, proof of Proposition VI.7.3 and
  Warning VI.7.5.
* C. Weibel, *Algebraic K-theory of rings of integers in local and global fields*, Handbook of
  K-theory, Corollary 63.
-/

public section

open Function Submodule Pointwise

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M] {p : ℕ}

namespace TauCeti

/-- **Unique divisibility over `ℤ_(p)`.** Let `R` be a ring in which the integers prime to the
prime `p` are units, and `Q` an `R`-module on which multiplication by `p` is bijective. Then
multiplication by every nonzero integer is bijective on `Q`: `Q` is uniquely divisible, i.e. a
`ℚ`-vector space. -/
theorem bijective_nsmul_of_bijective_smul_prime (hp : p.Prime)
    (hR : ∀ n : ℕ, n.Coprime p → IsUnit (n : R)) {Q : Type*} [AddCommGroup Q] [Module R Q]
    (hQ : Bijective fun x : Q ↦ (p : R) • x) {n : ℕ} (hn : n ≠ 0) :
    Bijective fun x : Q ↦ n • x := by
  obtain ⟨a, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn p hp.ne_one
  have hu : IsUnit (m : R) := hR m ((Nat.Prime.coprime_iff_not_dvd hp).mpr hm).symm
  have hpa : Bijective fun x : Q ↦ (p : R) ^ a • x := by
    simpa only [smul_iterate] using hQ.iterate a
  convert hpa.comp hu.smul_bijective using 1
  ext x
  simp [← Nat.cast_smul_eq_nsmul R, mul_smul]

end TauCeti

namespace TauCeti.AddCommGroup

/-- **The maximal divisible subgroup over `ℤ_(p)`.** Let `R` be a ring in which the integers
prime to the prime `p` are units, and `M` an `R`-module on which `p` is regular. Then the maximal
divisible subgroup of `M` is `⋂ₙ pⁿ M`, the kernel of the map to the `(p)`-adic completion. -/
theorem maxDivisible_eq_toAddSubgroup_iInf_pow_smul_top (hp : p.Prime)
    (hR : ∀ n : ℕ, n.Coprime p → IsUnit (n : R)) (hM : IsSMulRegular M (p : R)) :
    maxDivisible M = (⨅ n : ℕ, ((p : R) ^ n • ⊤ : Submodule R M)).toAddSubgroup := by
  set D := ⨅ n : ℕ, ((p : R) ^ n • ⊤ : Submodule R M)
  refine le_antisymm (fun x hx ↦ ?_)
    (AddSubgroup.IsDivisible.le_maxDivisible <| AddSubgroup.isDivisible_def.mpr fun n hn x hx ↦ ?_)
  · -- `x ∈ Div(M)` is a `pⁿ`-fold multiple for every `n`.
    refine (mem_iInf _).mpr fun n ↦ ?_
    obtain ⟨y, -, hy⟩ := exists_mem_maxDivisible_nsmul_eq hx (pow_ne_zero n hp.ne_zero)
    exact (mem_smul_pointwise_iff_exists _ _ _).mpr
      ⟨y, trivial, by rw [← hy, ← Nat.cast_smul_eq_nsmul R, Nat.cast_pow]⟩
  · -- `p` acts bijectively on `D`, so `D` is uniquely divisible.
    have hD : Bijective fun y : D ↦ (p : R) • y := by
      refine ⟨fun y z h ↦ Subtype.ext <| hM <| congrArg Subtype.val h, fun y ↦ ?_⟩
      obtain ⟨z, hz, hzy⟩ := (mem_smul_pointwise_iff_exists _ _ _).mp
        (hM.smul_iInf_pow_smul_top.ge y.property)
      exact ⟨⟨z, hz⟩, Subtype.ext hzy⟩
    obtain ⟨y, hy⟩ := (TauCeti.bijective_nsmul_of_bijective_smul_prime hp hR hD hn).2 ⟨x, hx⟩
    exact ⟨y, y.property, congrArg Subtype.val hy⟩

end TauCeti.AddCommGroup
