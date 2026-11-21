/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.IntegralClosure.Algebra.Defs
public import Mathlib.RingTheory.Valuation.ValuativeRel.Basic
public import Mathlib.RingTheory.Valuation.ValuationSubring
import TauCeti.RingTheory.Henselian.Basic
import TauCeti.RingTheory.Valuation.NontrivialComap
import TauCeti.RingTheory.Valuation.ValuativeRel.Discrete

/-!
# Automatic valuation compatibility for Henselian valued fields

Let `K` be a nontrivial Henselian valued field (`[HenselianRing 𝒪ᵥ[K] 𝓂ᵥ[K]] [IsNontrivial K]`,
where `𝒪ᵥ[K] := Valuation.integer (valuation K)` and `𝓂ᵥ[K] := IsLocalRing.maximalIdeal 𝒪ᵥ[K]`)
and let `R` be a ring carrying a discrete archimedean valuative relation
(`[ValuativeRel.IsDiscrete R] [MulArchimedean (ValueGroupWithZero R)]`, in particular whenever
`ValuativeRel.IsRankLeOne R` holds). Every ring homomorphism `f : K →+* R` sends `𝒪ᵥ[K]` into the
valuation subring of `R`: for any `m ∈ 𝓂ᵥ[K]`, Hensel's lemma
(`TauCeti.HenselianRing.exists_le_pow_eq_one_add`) extracts `k`-th roots of `1 + m` in `𝒪ᵥ[K]`
for arbitrarily large `k : ℕ`, so divisibility rigidity in `R`
(`ValuativeRel.valuation_eq_one_of_forall_exists_le_pow_eq`) forces `valuation R (f (1 + m)) = 1`
and hence `valuation R (f m) ≤ 1` by ultrametricity. Multiplying any `x ∈ 𝒪ᵥ[K]` by a nonzero
element `m ∈ 𝓂ᵥ[K]` gives `x ^ n * m ∈ 𝓂ᵥ[K]` for every `n : ℕ`, so the archimedean property of
`ValueGroupWithZero R` forces `valuation R (f x) ≤ 1`.

When `ValueGroupWithZero K` is also archimedean (`[MulArchimedean (ValueGroupWithZero K)]`), the
pullback `(valuation R).comap f` is either trivial or equivalent to `valuation K`. Consequently,
every integral `K`-algebra `R` carrying a nontrivial discrete archimedean valuative relation is
automatically a `ValuativeExtension` of `K` (`ValuativeExtension.of_isIntegral`). For
nonarchimedean local fields `K` and `R`, `IsNonarchimedeanLocalField` and
`TauCeti.henselianLocalRing_integer` supply these hypotheses automatically.

## Main results

* `RingHom.valuation_map_le_one_of_valuation_le_one`: for a nontrivial Henselian valued field `K`
  and a discrete archimedean valued ring `R`, `f : K →+* R` sends elements of valuation at most `1`
  in `K` to elements of valuation at most `1` in `R`.
* `RingHom.isEquiv_comap_valuation_iff_isNontrivial`: when `ValueGroupWithZero K` is also
  archimedean, `(valuation R).comap f` is equivalent to `valuation K` if and only if it is
  nontrivial.
* `ValuativeExtension.of_isIntegral`: every integral algebra over a nontrivial archimedean
  Henselian valued field `K` carrying a nontrivial discrete archimedean valuative relation is a
  `ValuativeExtension` of `K`.

## Implementation notes

`ValuativeExtension.of_isIntegral` is a `theorem` rather than a global `instance`, matching
`ValuativeExtension.trans`, to avoid firing global backward typeclass search for `Field K`,
`HenselianRing`, `IsDiscrete R`, `MulArchimedean`, and `Algebra.IsIntegral K R` on every
`ValuativeExtension` query.

## References

* F. K. Schmidt, *Mehrfach perfekte Körper*, Math. Ann. 108 (1933), 1–25.
* [A. J. Engler and A. Prestel, *Valued Fields*][engler2005], Corollary 4.1.4.
* J. Neukirch, *Algebraic Number Theory*, Chapter II, §4.
-/

public section
noncomputable section

open ValuativeRel

local notation "𝒪ᵥ[" K "]" => Valuation.integer (valuation K)
local notation "𝓂ᵥ[" K "]" => IsLocalRing.maximalIdeal ↥𝒪ᵥ[K]

section RingHom

variable {K R : Type*} [Field K] [ValuativeRel K] [HenselianRing 𝒪ᵥ[K] 𝓂ᵥ[K]]
  [Ring R] [ValuativeRel R] [IsDiscrete R] [MulArchimedean (ValueGroupWithZero R)]

namespace RingHom

/-- Every homomorphism from a Henselian valued field `K` into a discrete archimedean valued ring
`R` sends elements of valuation strictly less than `1` to elements of valuation at most `1`. -/
private theorem valuation_map_le_one_of_valuation_lt_one (f : K →+* R) {m : K}
    (hm : valuation K m < 1) :
    valuation R (f m) ≤ 1 := by
  have h1m : valuation K (1 + m) = 1 := (valuation K).map_one_add_of_lt hm
  have h1m0 : 1 + m ≠ 0 := by rintro h; simp [h] at h1m
  have hf1m0 : valuation R (f (1 + m)) ≠ 0 :=
    (((IsUnit.mk0 (1 + m) h1m0).map f).map (valuation R)).ne_zero
  have hm' : (⟨m, hm.le⟩ : 𝒪ᵥ[K]) ∈ 𝓂ᵥ[K] :=
    (IsLocalRing.mem_maximalIdeal _).2 (Valuation.Integer.not_isUnit_iff_valuation_lt_one.2 hm)
  have hf1m : valuation R (f (1 + m)) = 1 :=
    valuation_eq_one_of_forall_exists_le_pow_eq hf1m0 fun n ↦ by
      obtain ⟨k, hkn, a, ha⟩ := TauCeti.HenselianRing.exists_le_pow_eq_one_add hm' n
      refine ⟨k, hkn, f (a : K), ?_⟩
      rw [← map_pow, ← SubmonoidClass.coe_pow, ha]
      rfl
  by_contra! hgt
  have hlt : valuation R (1 : R) < valuation R (f m) := by rwa [map_one]
  have hadd : valuation R (1 + f m) = 1 := by simpa only [map_add, map_one] using hf1m
  exact hgt.ne' ((valuation R).map_add_eq_of_lt_right hlt ▸ hadd)

/-- **Integers of a nontrivial Henselian valued field map into the valuation subring of `R`** under
any homomorphism into a discrete archimedean valued ring:
`valuation K x ≤ 1 → valuation R (f x) ≤ 1`. -/
theorem valuation_map_le_one_of_valuation_le_one [IsNontrivial K] (f : K →+* R) {x : K}
    (hx : valuation K x ≤ 1) :
    valuation R (f x) ≤ 1 := by
  by_contra! hgt
  obtain ⟨γ, hγ0, hγ1⟩ := IsNontrivial.exists_lt_one (R := K)
  obtain ⟨m, rfl⟩ := valuation_surjective γ
  have hm0 : m ≠ 0 := by rintro rfl; simp at hγ0
  have hfm0 : valuation R (f m) ≠ 0 := (((IsUnit.mk0 m hm0).map f).map (valuation R)).ne_zero
  obtain ⟨n, hn⟩ := MulArchimedean.arch (valuation R (f m))⁻¹ hgt
  have hlt : valuation K (x ^ (n + 1) * m) < 1 := by
    rw [map_mul, map_pow]
    exact (mul_le_of_le_one_left zero_le (pow_le_one₀ zero_le hx)).trans_lt hγ1
  have hle := f.valuation_map_le_one_of_valuation_lt_one hlt
  rw [map_mul, map_pow, map_mul, map_pow] at hle
  have hgt' : 1 < valuation R (f x) ^ (n + 1) * valuation R (f m) :=
    calc (1 : ValueGroupWithZero R)
        = (valuation R (f m))⁻¹ * valuation R (f m) := (inv_mul_cancel₀ hfm0).symm
      _ < valuation R (f x) ^ (n + 1) * valuation R (f m) :=
          mul_lt_mul_of_pos_right (hn.trans_lt (pow_lt_pow_right₀ hgt n.lt_succ_self))
            (zero_lt_iff.2 hfm0)
  exact hgt'.not_ge hle

/-- **Dichotomy for discrete archimedean valuations pulled back to a nontrivial archimedean
Henselian valued field.** The pullback of `valuation R` along `f : K →+* R` is equivalent to
`valuation K` if and only if it is nontrivial. -/
theorem isEquiv_comap_valuation_iff_isNontrivial [IsNontrivial K]
    [MulArchimedean (ValueGroupWithZero K)] (f : K →+* R) :
    ((valuation R).comap f).IsEquiv (valuation K) ↔ ((valuation R).comap f).IsNontrivial := by
  refine ⟨fun heq ↦ heq.isNontrivial_iff.2 inferInstance, fun hnt ↦ ?_⟩
  refine Valuation.isEquiv_iff_val_le_one.2 fun {x} ↦
    ⟨fun hx ↦ ?_, f.valuation_map_le_one_of_valuation_le_one⟩
  rw [Valuation.comap_apply] at hx
  by_contra! hvx
  have hx0 : x ≠ 0 := by rintro rfl; simp at hvx
  obtain ⟨y, hy⟩ := hnt.exists_one_lt
  obtain ⟨n, hn⟩ := MulArchimedean.arch (valuation K y) hvx
  have hdiv : valuation K (y / x ^ n) ≤ 1 := by
    rw [map_div₀, map_pow, div_le_one₀ (pow_pos (zero_lt_one.trans hvx) n)]
    exact hn
  have hle := f.valuation_map_le_one_of_valuation_le_one hdiv
  have hy_eq : y = y / x ^ n * x ^ n := (div_mul_cancel₀ y (pow_ne_zero n hx0)).symm
  rw [Valuation.comap_apply, hy_eq, map_mul, map_pow, map_mul, map_pow] at hy
  exact hy.not_ge (mul_le_one' hle (pow_le_one' hx n))

end RingHom

end RingHom

/-- **Automatic valuation compatibility along integral extensions of a Henselian rank-one field.**
Every integral algebra `R` over a nontrivial archimedean Henselian valued field `K` carrying a
nontrivial discrete archimedean valuative relation is a `ValuativeExtension` of `K`. Over a field
`K`, `Algebra.IsAlgebraic K R` and `Module.Finite K R` synthesize `Algebra.IsIntegral K R`; when
both `K` and `R` are nonarchimedean local fields, `IsNonarchimedeanLocalField` together with
`TauCeti.henselianLocalRing_integer` discharges the remaining valuation hypotheses. -/
theorem ValuativeExtension.of_isIntegral (K R : Type*) [Field K] [ValuativeRel K]
    [HenselianRing 𝒪ᵥ[K] 𝓂ᵥ[K]] [IsNontrivial K] [MulArchimedean (ValueGroupWithZero K)]
    [Ring R] [ValuativeRel R] [IsDiscrete R] [MulArchimedean (ValueGroupWithZero R)]
    [IsNontrivial R] [Algebra K R] [Algebra.IsIntegral K R] :
    ValuativeExtension K R := by
  have hnt : ((valuation R).comap (algebraMap K R)).IsNontrivial :=
    (valuation R).isNontrivial_comap_algebraMap
  have heq := (algebraMap K R).isEquiv_comap_valuation_iff_isNontrivial.2 hnt
  exact ⟨fun {a b} ↦ (valuation R).vle_iff_le.trans ((heq a b).trans (valuation K).vle_iff_le.symm)⟩
