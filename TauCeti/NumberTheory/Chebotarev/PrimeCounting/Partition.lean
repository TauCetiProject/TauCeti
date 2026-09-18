/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.ClassEquation
public import TauCeti.NumberTheory.Chebotarev.PrimeCounting.VonMangoldt

/-!
# The Frobenius `ψ` fibres partition Chebyshev's `ψ`

Let `L / K` be a finite Galois extension of number fields with group `G`. A prime power `𝔭 ^ j`
with `𝔭` unramified in `L` lies in the powered Frobenius fibre of exactly one conjugacy class of
`G`, namely `(artinSymbol 𝔭) ^ j`, and a prime power based at a ramified prime lies in none. So the
Frobenius `ψ` functions of all conjugacy classes add up to Chebyshev's `ψ` of `K` with the ramified
primes removed:

```text
∑_C ψ_C(x) + ψ_{ramifiedPrimes K L}(x) = ψ_K(x),
```

and the correction is `O(log x)` because the ramified set is finite.

This is what turns lower bounds for the individual fibres into limits. If
`ψ_D(x) ≥ (#D / #G - ε) x` eventually for every class `D` and every `ε > 0`, and `ψ_K(x) ~ x`, then
the other classes leave no room above `#C / #G` for any single class `C`, because the constants
`#D / #G` add up to `1` by the class equation. Hence `ψ_C(x) / x → #C / #G`.

## Main results

* `NumberField.Chebotarev.sum_frobeniusPrimePowerWeight`: at a single prime power, the Frobenius
  weights of all classes add up to the von Mangoldt weight if the base is unramified, and to `0`
  otherwise.
* `NumberField.Chebotarev.sum_frobeniusPsi_add_primePsi_ramifiedPrimes`: the Frobenius `ψ`
  functions and `ψ` of the ramified primes add up to `ψ_K`.
* `NumberField.Chebotarev.primePsi_univ_sub_sum_frobeniusPsi_isBigO_log`: the Frobenius `ψ`
  functions account for `ψ_K` up to `O(log x)`.
* `NumberField.Chebotarev.tendsto_frobeniusPsi_div_of_eventually_le`: eventual lower bounds
  `#D / #G - ε` for every class, together with `ψ_K(x) ≤ (1 + ε) x`, force
  `ψ_C(x) / x → #C / #G` for every class `C`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §13.
* S. Lang, *Algebraic Number Theory*, Chapter XV.
-/

public section

namespace NumberField.Chebotarev

open Filter TauCeti Topology
open scoped Asymptotics NumberField
open IsDedekindDomain (HeightOneSpectrum)

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L]

open scoped Classical in
variable (K L) in
/-- **The Frobenius weights partition the von Mangoldt weight.** At a prime power `𝔭 ^ j`, the
powered Frobenius weights of all conjugacy classes add up to `log N𝔭` when `𝔭` is unramified in
`L`, the only nonzero term being that of `(artinSymbol 𝔭) ^ j`, and to `0` when `𝔭` ramifies. -/
theorem sum_frobeniusPrimePowerWeight (A : IdealPrimePower K) :
    ∑ C : ConjClasses (L ≃ₐ[K] L), frobeniusPrimePowerWeight K L C A =
      {B : IdealPrimePower K | primePowerBase B ∉ ramifiedPrimes K L}.indicator
        primePowerWeight A := by
  by_cases hA : primePowerBase A ∈ ramifiedPrimes K L
  · rw [Set.indicator_of_notMem (by simpa using hA)]
    refine Finset.sum_eq_zero fun C _ ↦ frobeniusPrimePowerWeight_of_notMem ?_
    intro h
    obtain ⟨hur, -⟩ := mem_frobeniusPrimePowerSet_iff.mp h
    exact (mem_ramifiedPrimes_iff _).mp hA hur
  · rw [Set.indicator_of_mem (by simpa using hA)]
    have hur := not_not.mp ((mem_ramifiedPrimes_iff _).not.mp hA)
    rw [Finset.sum_eq_single (artinSymbol (primePowerBase A).asIdeal hur ^ primePowerExponent A)
      (fun C _ hC ↦ frobeniusPrimePowerWeight_of_notMem
        fun h ↦ hC ((mem_frobeniusPrimePowerSet_iff_artinSymbol_pow_eq hur C).mp h).symm)
      (fun h ↦ absurd (Finset.mem_univ _) h)]
    exact frobeniusPrimePowerWeight_of_artinSymbol_pow_eq hur rfl

open scoped Classical in
variable (K L) in
/-- **The Frobenius `ψ` fibres partition Chebyshev's `ψ`.** Summed over all conjugacy classes of
`Gal(L/K)`, the Frobenius `ψ` functions count every prime power based at a prime unramified in `L`
exactly once; adding `ψ` of the finite set `ramifiedPrimes K L` gives `ψ_K`. -/
theorem sum_frobeniusPsi_add_primePsi_ramifiedPrimes (x : ℝ) :
    ∑ C : ConjClasses (L ≃ₐ[K] L), frobeniusPsi K L C x +
        primePsi K (ramifiedPrimes K L : Set (HeightOneSpectrum (𝓞 K))) x =
      primePsi K Set.univ x := by
  simp only [frobeniusPsi_apply, primePsi_apply]
  rw [Finset.sum_comm, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun A _ ↦ ?_
  rw [sum_frobeniusPrimePowerWeight]
  by_cases hA : primePowerBase A ∈ ramifiedPrimes K L <;>
    simp only [Set.indicator_apply, Set.mem_ofPred_eq, Finset.mem_coe, Set.mem_univ, hA,
      not_true_eq_false, not_false_eq_true, ite_true, ite_false, zero_add, add_zero]

open scoped Classical in
variable (K L) in
/-- **The Frobenius `ψ` fibres account for `ψ_K` up to `O(log x)`.** The only prime powers missed by
all Frobenius fibres are those based at the finitely many primes of `ramifiedPrimes K L`. -/
theorem primePsi_univ_sub_sum_frobeniusPsi_isBigO_log :
    (fun x : ℝ ↦ primePsi K Set.univ x - ∑ C : ConjClasses (L ≃ₐ[K] L), frobeniusPsi K L C x)
      =O[atTop] Real.log := by
  refine (primePsi_isBigO_log_of_finite (ramifiedPrimes K L).finite_toSet).congr_left fun x ↦ ?_
  rw [← sum_frobeniusPsi_add_primePsi_ramifiedPrimes K L x, add_sub_cancel_left]

open scoped Classical in
variable (K L) in
/-- The Frobenius `ψ` functions of all conjugacy classes add up to at most `ψ_K`. -/
theorem sum_frobeniusPsi_le_primePsi_univ (x : ℝ) :
    ∑ C : ConjClasses (L ≃ₐ[K] L), frobeniusPsi K L C x ≤ primePsi K Set.univ x := by
  rw [← sum_frobeniusPsi_add_primePsi_ramifiedPrimes K L x]
  exact le_add_of_nonneg_right (primePsi_nonneg _ x)

/-- **Squeezing the Frobenius `ψ` fibres.** Suppose that for every conjugacy class `D` of
`G = Gal(L/K)` and every `c < #D / #G`, eventually `c * x ≤ ψ_D(x)`, and that for every `c > 1`,
eventually `ψ_K(x) ≤ c * x`, as follows from `ψ_K(x) ~ x`. Then `ψ_C(x) / x → #C / #G` for every
class `C`.

The lower bound for `C` is a hypothesis. The upper bound comes from the others: the classes are
disjoint fibres inside `ψ_K`, and their proportions `#D / #G` add up to `1` by the class equation,
so no class can exceed its share by a fixed proportion of `x`. -/
theorem tendsto_frobeniusPsi_div_of_eventually_le
    (hK : ∀ c : ℝ, 1 < c → ∀ᶠ x in atTop, primePsi K Set.univ x ≤ c * x)
    (hlow : ∀ (D : ConjClasses (L ≃ₐ[K] L)) (c : ℝ),
      c < (Nat.card D.carrier : ℝ) / Nat.card (L ≃ₐ[K] L) →
        ∀ᶠ x in atTop, c * x ≤ frobeniusPsi K L D x)
    (C : ConjClasses (L ≃ₐ[K] L)) :
    Tendsto (fun x ↦ frobeniusPsi K L C x / x) atTop
      (𝓝 ((Nat.card C.carrier : ℝ) / Nat.card (L ≃ₐ[K] L))) := by
  classical
  set δ : ConjClasses (L ≃ₐ[K] L) → ℝ :=
    fun D ↦ (Nat.card D.carrier : ℝ) / Nat.card (L ≃ₐ[K] L)
  -- The class equation: the proportions `#D / #G` add up to `1`.
  have hsum : ∑ D, δ D = 1 := by
    have hG : (Nat.card (L ≃ₐ[K] L) : ℝ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
    have h := Group.sum_card_conj_classes_eq_card (L ≃ₐ[K] L)
    rw [finsum_eq_sum_of_fintype] at h
    simp only [δ, ← Finset.sum_div, div_eq_one_iff_eq hG, Nat.card_coe_set_eq]
    exact_mod_cast h
  refine tendsto_order.2 ⟨fun a ha ↦ ?_, fun b hb ↦ ?_⟩
  · -- Below: the hypothesis for `C` itself, at a constant between `a` and `#C / #G`.
    obtain ⟨c, hac, hcδ⟩ := exists_between ha
    filter_upwards [hlow C c hcδ, eventually_gt_atTop 0] with x hx hx0
    exact hac.trans_le ((le_div_iff₀ hx0).mpr hx)
  · -- Above: every other class takes at least `δ D - ε` of `x`, and `ψ_K` at most `1 + ε`.
    set n : ℕ := Fintype.card (ConjClasses (L ≃ₐ[K] L))
    set ε : ℝ := (b - δ C) / (n + 2) with hε
    have hn : (0 : ℝ) < n + 2 := by positivity
    have hε0 : 0 < ε := div_pos (sub_pos.mpr hb) hn
    have hlowε : ∀ᶠ x in atTop, ∀ D, (δ D - ε) * x ≤ frobeniusPsi K L D x :=
      eventually_all.2 fun D ↦ hlow D _ (sub_lt_self _ hε0)
    filter_upwards [hlowε, hK _ (lt_add_of_pos_right _ hε0), eventually_gt_atTop 0]
      with x hx hxK hx0
    rw [div_lt_iff₀ hx0]
    -- Isolate `ψ_C` in the class sum and bound the remaining classes from below.
    have hsplit := Finset.add_sum_erase Finset.univ (fun D ↦ frobeniusPsi K L D x)
      (Finset.mem_univ C)
    have hrest : ∑ D ∈ Finset.univ.erase C, (δ D - ε) * x ≤
        ∑ D ∈ Finset.univ.erase C, frobeniusPsi K L D x :=
      Finset.sum_le_sum fun D _ ↦ hx D
    have hδrest : ∑ D ∈ Finset.univ.erase C, δ D = 1 - δ C := by
      rw [← hsum, ← Finset.add_sum_erase Finset.univ δ (Finset.mem_univ C), add_sub_cancel_left]
    have hcard : ((Finset.univ.erase C).card : ℝ) ≤ n := by
      exact_mod_cast (Finset.card_erase_le).trans (Finset.card_univ.le)
    rw [← Finset.sum_mul, Finset.sum_sub_distrib, hδrest, Finset.sum_const, nsmul_eq_mul] at hrest
    have hle := sum_frobeniusPsi_le_primePsi_univ K L x
    have hεn : ((Finset.univ.erase C).card : ℝ) * ε * x ≤ n * ε * x := by
      gcongr
    have hb' : b = δ C + (n + 2) * ε := by
      rw [hε, mul_div_cancel₀ _ hn.ne']
      ring
    rw [hb']
    nlinarith

end NumberField.Chebotarev
