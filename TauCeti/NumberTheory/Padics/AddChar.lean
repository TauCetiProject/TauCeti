/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Padics.AddChar
public import Mathlib.Topology.Algebra.Monoid.AddChar
public import TauCeti.NumberTheory.Padics.BinomialSeries
public import TauCeti.RingTheory.Huber.Padic.Basic
public import TauCeti.RingTheory.PowerSeries.Evaluation

/-!
# Additive characters of `ℤ_p` in linearly topologised rings

Let `S` be a complete separated commutative ring whose topology is linear (it has a basis of
neighbourhoods of `0` consisting of ideals), with a continuous `ℤ_p`-algebra structure. For a
topologically nilpotent `z ∈ S`, the hypothesis `PowerSeries.HasEval z` of Mathlib's evaluation
`PowerSeries.aeval`, the binomial series `(1 + X) ^ s ∈ ℤ_p⟦X⟧` can be evaluated at `z`, and

`s ↦ (1 + z) ^ s = ∑ₙ (s choose n) zⁿ`   (`PadicInt.binomialAddChar`)

is a continuous additive character `ℤ_p → S` with value `1 + z` at `1`. It is the only one: a
continuous additive character is determined by its value at `1`, since `ℕ` is dense in `ℤ_p`.
Conversely, every continuous additive character `ψ` is of this form: `ψ 1 - 1` is topologically
nilpotent (`AddChar.isTopologicallyNilpotent_eval_one_sub`). Modulo an open ideal `I`, the prime
`p` is nilpotent and `ψ 1 ^ (p ^ n) = ψ (p ^ n)` is `1` for large `n`, so the binomial theorem
`(t + 1) ^ (p ^ n) = t ^ (p ^ n) + 1 + p (⋯)` makes `t = ψ 1 - 1` nilpotent modulo `I`.

This is the adic counterpart of Mathlib's `PadicInt.addChar_of_value_at_one` and
`AddChar.tendsto_eval_one_sub_pow`, which treat complete ultrametric normed `ℤ_p`-algebras through
Mahler series. Neither setting contains the other: `ℚ_p` is complete and normed but not linearly
topologised over itself, while a linear topology need not be metrisable, as for an uncountable
product of copies of `ℤ_p`. When both apply the two characters agree
(`PadicInt.binomialAddChar_eq_addChar_of_value_at_one`).

## Main declarations

* `AddChar.isTopologicallyNilpotent_eval_one_sub`: for a continuous additive character `ψ` of
  `ℤ_p` with values in a linearly topologised `ℤ_p`-algebra, `ψ 1 - 1` is topologically nilpotent.
* `PadicInt.binomialAddChar hz`: the additive character `s ↦ (1 + z) ^ s` of `ℤ_p`, for
  `PowerSeries.HasEval z`.
* `PadicInt.continuous_binomialAddChar`: it is continuous.
* `PadicInt.binomialAddChar_one`, `PadicInt.binomialAddChar_natCast`: its values `1 + z` at `1` and
  `(1 + z) ^ n` at a natural number `n`.
* `PadicInt.eq_binomialAddChar`: a continuous additive character with value `1 + z` at `1` is
  `PadicInt.binomialAddChar hz`.
* `PadicInt.binomialAddChar_eq_addChar_of_value_at_one`: agreement with Mathlib's normed
  construction when both apply.

## References

* P. Colmez, *Fonctions d'une variable p-adique*, Astérisque 330 (2010), §I.3.
* J. Rodrigues Jacinto and C. Williams, *An introduction to p-adic L-functions*, §4.
-/

public section

open Filter Topology PowerSeries.WithPiTopology

/-- **The value at `1` of a continuous additive character of `ℤ_p` is `1` plus a topologically
nilpotent element**, in a linearly topologised commutative ring with a continuous `ℤ_p`-algebra
structure. No completeness or separation is needed. -/
theorem AddChar.isTopologicallyNilpotent_eval_one_sub {p : ℕ} [Fact p.Prime] {S : Type*}
    [CommRing S] [TopologicalSpace S] [IsTopologicalRing S] [IsLinearTopology S S]
    [Algebra ℤ_[p] S] [ContinuousSMul ℤ_[p] S] {ψ : AddChar ℤ_[p] S} (hψ : Continuous ψ) :
    IsTopologicallyNilpotent (ψ 1 - 1) := by
  set t := ψ 1 - 1
  have hp : IsTopologicallyNilpotent (p : ℤ_[p]) :=
    TauCeti.Huber.PadicInt.isTopologicallyNilpotent_iff_dvd.mpr dvd_rfl
  refine IsLinearTopology.hasBasis_ideal.tendsto_right_iff.mpr fun I hI ↦ ?_
  -- Modulo `I`, the prime `p` is nilpotent ...
  obtain ⟨m, hm⟩ := (by simpa using hp.map (continuous_algebraMap ℤ_[p] S) :
    IsTopologicallyNilpotent (p : S)).exists_pow_mem_of_mem_nhds hI
  -- ... and `(t + 1) ^ p ^ n = ψ (p ^ n)` is `1` for some `n`, since `p ^ n → 0` in `ℤ_p`.
  obtain ⟨n, hn⟩ := ((by simpa using ((hψ.tendsto 0).comp hp).sub_const 1 :
    Tendsto (fun n ↦ ψ ((p : ℤ_[p]) ^ n) - 1) atTop (𝓝 0)).eventually_mem hI).exists
  have hψn : ψ ((p : ℤ_[p]) ^ n) = (t + 1) ^ p ^ n := by
    rw [sub_add_cancel, ← AddChar.map_nsmul_eq_pow, nsmul_one, Nat.cast_pow]
  obtain ⟨r, hr⟩ := exists_add_pow_prime_pow_eq (Fact.out : p.Prime) t 1 n
  -- Hence `t ^ p ^ n` is a multiple of `p` modulo `I`, and `t ^ (p ^ n * m)` lies in `I`.
  have ht : Ideal.Quotient.mk I (t ^ p ^ n) =
      Ideal.Quotient.mk I (p : S) * Ideal.Quotient.mk I (-(t * r)) := by
    have h₀ := Ideal.Quotient.eq_zero_iff_mem.mpr hn
    rw [hψn, hr] at h₀
    simp only [map_sub, map_add, map_mul, map_neg, map_one, one_pow, mul_one] at h₀ ⊢
    linear_combination h₀
  have hpm : Ideal.Quotient.mk I (p : S) ^ m = 0 := by
    rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
    exact hm
  refine eventually_atTop.mpr ⟨p ^ n * m, fun k hk ↦ ?_⟩
  rw [SetLike.mem_coe, ← Ideal.Quotient.eq_zero_iff_mem, ← Nat.add_sub_cancel' hk, pow_add,
    pow_mul, map_mul, map_pow, ht]
  rw [mul_pow, hpm, zero_mul, zero_mul]

namespace PadicInt

variable {p : ℕ} [Fact p.Prime] {S : Type*} [CommRing S] [UniformSpace S] [IsUniformAddGroup S]
  [IsTopologicalRing S] [IsLinearTopology S S] [CompleteSpace S] [T2Space S]
  [Algebra ℤ_[p] S] [ContinuousSMul ℤ_[p] S] {z : S}

/-- The additive character `s ↦ (1 + z) ^ s = ∑ₙ (s choose n) zⁿ` of `ℤ_p`, for `z`
topologically nilpotent in a complete linearly topologised `ℤ_p`-algebra: the binomial series
`(1 + X) ^ s` evaluated at `z`. -/
noncomputable def binomialAddChar (hz : PowerSeries.HasEval z) : AddChar ℤ_[p] S where
  toFun s := PowerSeries.aeval hz (PowerSeries.binomialSeries ℤ_[p] s)
  map_zero_eq_one' := by simp [PowerSeries.binomialSeries_zero]
  map_add_eq_mul' a b := by simp [PowerSeries.binomialSeries_add]

theorem binomialAddChar_apply (hz : PowerSeries.HasEval z) (s : ℤ_[p]) :
    binomialAddChar hz s = PowerSeries.aeval hz (PowerSeries.binomialSeries ℤ_[p] s) :=
  (rfl)

@[fun_prop]
theorem continuous_binomialAddChar (hz : PowerSeries.HasEval z) :
    Continuous (binomialAddChar (p := p) hz) :=
  (PowerSeries.continuous_aeval hz).comp continuous_binomialSeries

@[simp]
theorem binomialAddChar_natCast (hz : PowerSeries.HasEval z) (n : ℕ) :
    binomialAddChar (p := p) hz n = (1 + z) ^ n := by
  simp [binomialAddChar_apply, PowerSeries.binomialSeries_nat, PowerSeries.aeval_X]

@[simp]
theorem binomialAddChar_one (hz : PowerSeries.HasEval z) :
    binomialAddChar (p := p) hz 1 = 1 + z := by
  simpa using binomialAddChar_natCast (p := p) hz 1

/-- **Uniqueness of the binomial character.** A continuous additive character `ψ` of `ℤ_p` with
`ψ 1 = 1 + z` is `s ↦ (1 + z) ^ s`. -/
theorem eq_binomialAddChar (hz : PowerSeries.HasEval z) {ψ : AddChar ℤ_[p] S}
    (hψ : Continuous ψ) (h₁ : ψ 1 = 1 + z) : ψ = binomialAddChar hz :=
  denseRange_natCast.addChar_eq_of_eval_one_eq hψ (continuous_binomialAddChar hz) (by simp [h₁])

end PadicInt

namespace PadicInt

variable {p : ℕ} [Fact p.Prime] {S : Type*} [NormedCommRing S] [IsUltrametricDist S]
  [CompleteSpace S] [IsLinearTopology S S] [Algebra ℤ_[p] S] [IsBoundedSMul ℤ_[p] S] {z : S}

/-- **The adic and normed binomial characters agree.** On a complete ultrametric normed
`ℤ_p`-algebra whose topology is also linear, such as `ℤ_p` or the ring of integers of `ℂ_p`, the
binomial character `PadicInt.binomialAddChar` is Mathlib's Mahler-series character
`PadicInt.addChar_of_value_at_one`. Topological nilpotence `PowerSeries.HasEval z` is by
definition the convergence `z ^ n → 0` assumed there. -/
theorem binomialAddChar_eq_addChar_of_value_at_one (hz : PowerSeries.HasEval z) :
    binomialAddChar (p := p) hz = addChar_of_value_at_one z hz :=
  eq_addChar_of_value_at_one hz (continuous_binomialAddChar hz) (binomialAddChar_one hz)

end PadicInt
