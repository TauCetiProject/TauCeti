/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.LaurentSeries
public import TauCeti.RingTheory.HahnSeries.EventualCoeff

/-!
# Convergence of formal Laurent series

This file characterizes convergence in the valuation topology on a Laurent-series field. A family
converges precisely when its supports are eventually bounded below by one common integer and each
coefficient eventually agrees with the corresponding coefficient of the limit. Equivalently, the
order of the difference eventually exceeds every prescribed integer.

The common lower bound is essential. The monomials `X⁻¹, X⁻², ...` have every fixed coefficient
eventually equal to zero, but they do not converge to zero in the valuation topology.

The order formulation is the form used to prove continuity of operations on Laurent series: a
map is continuous once every prescribed order of the output difference is reached from some order of
the input difference. The coefficient formulation instead identifies limits concretely, coefficient
by coefficient, once a common lower bound on the supports is known.

## Main results

* `TauCeti.tendsto_laurentSeries_iff_coeff` characterizes convergence by a common lower support
  bound and eventual equality of every coefficient.
* `TauCeti.tendsto_laurentSeries_iff_orderTop_sub` gives the equivalent order formulation.
* `TauCeti.laurentSeries_eventually_coeff_single_neg_succ_eq_zero` and
  `TauCeti.laurentSeries_not_tendsto_single_neg_succ` exhibit the coefficientwise counterexample.
-/

public section

open Filter Topology WithZero
open scoped LaurentSeries Topology

namespace TauCeti

variable {K : Type*} [Field K]

/-- A family of Laurent series converges exactly when its supports have an eventual common lower
bound and each coefficient eventually agrees with the corresponding coefficient of the limit.

The statement applies to arbitrary filters, not only sequences; for the bottom filter both sides
hold automatically. No topology on the coefficient field is used: coefficient stabilization is
literal eventual equality. -/
theorem tendsto_laurentSeries_iff_coeff {ι : Type*} {l : Filter ι}
    (f : ι → LaurentSeries K) (g : LaurentSeries K) :
    Tendsto f l (nhds g) ↔
      (∃ b : ℤ, ∀ᶠ i in l, ∀ z < b, (f i).coeff z = 0) ∧
        ∀ z : ℤ, ∀ᶠ i in l, (f i).coeff z = g.coeff z := by
  by_cases hl : NeBot l
  · let _ : NeBot l := hl
    constructor
    · intro h
      have hcauchy : Cauchy (l.map f) := h.cauchy_map
      obtain ⟨b, hb⟩ := LaurentSeries.Cauchy.exists_lb_eventual_support hcauchy
      refine ⟨⟨b, ?_⟩, fun z ↦ ?_⟩
      · simpa only [Filter.eventually_map] using hb
      · let _ : UniformSpace K := ⊥
        have hz : Tendsto (fun i ↦ (f i).coeff z) l (nhds (g.coeff z)) :=
          by simpa only [Function.comp_def] using
            (LaurentSeries.uniformContinuous_coeff z).continuous.tendsto g |>.comp h
        exact hz.eventually ((isOpen_discrete {g.coeff z}).mem_nhds (Set.mem_singleton _))
    · rintro ⟨⟨b, hlb⟩, hcoeff⟩
      intro U hU
      obtain ⟨γ, hγ⟩ := Valued.mem_nhds.mp hU
      let D := 1 - log (MonoidWithZeroHom.ValueGroup₀.embedding γ.1)
      have hD : exp (-D) < MonoidWithZeroHom.ValueGroup₀.embedding γ.1 := by
        rw [← lt_log_iff_exp_lt (by simp), neg_sub]
        omega
      rw [Filter.mem_map]
      filter_upwards [hahnSeries_eventually_forall_lt_coeff_eq hlb hcoeff D] with i hi
      apply hγ
      rw [Set.mem_ofPred_eq, Valued.v.restrict_lt_iff_lt_embedding]
      exact lt_of_le_of_lt ((LaurentSeries.valuation_le_iff_coeff_lt_eq_zero K).2
        fun z hz ↦ by rw [HahnSeries.coeff_sub, hi z hz, sub_self]) hD
  · rw [Filter.not_neBot.mp hl]
    simp

/-- Convergence of Laurent series is equivalent to the order of the difference eventually being
at least every prescribed integer. This includes a zero difference, whose order is `⊤`. -/
theorem tendsto_laurentSeries_iff_orderTop_sub {ι : Type*} {l : Filter ι}
    (f : ι → LaurentSeries K) (g : LaurentSeries K) :
    Tendsto f l (nhds g) ↔
      ∀ D : ℤ, ∀ᶠ i in l, (D : WithTop ℤ) ≤ (f i - g).orderTop := by
  rw [tendsto_laurentSeries_iff_coeff]
  constructor
  · rintro ⟨⟨b, hlb⟩, hcoeff⟩ D
    filter_upwards [hahnSeries_eventually_forall_lt_coeff_eq hlb hcoeff D] with i hi
    rw [HahnSeries.le_orderTop_iff_forall]
    intro z hz
    rw [HahnSeries.coeff_sub, hi z (WithTop.coe_lt_coe.mp hz), sub_self]
  · intro h
    refine ⟨⟨g.order, ?_⟩, fun z ↦ ?_⟩
    · filter_upwards [h g.order] with i hi z hz
      have hdiff : (f i - g).coeff z = 0 :=
        (HahnSeries.le_orderTop_iff_forall.mp hi) z (by exact_mod_cast hz)
      rw [HahnSeries.coeff_sub, sub_eq_zero] at hdiff
      rw [hdiff, HahnSeries.coeff_eq_zero_of_lt_order hz]
    · filter_upwards [h (z + 1)] with i hi
      have hdiff : (f i - g).coeff z = 0 :=
        (HahnSeries.le_orderTop_iff_forall.mp hi) z (by exact_mod_cast (lt_add_one z))
      simpa only [HahnSeries.coeff_sub, sub_eq_zero] using hdiff

/-- Every fixed coefficient of the sequence `X⁻¹, X⁻², ...` is eventually zero. -/
theorem laurentSeries_eventually_coeff_single_neg_succ_eq_zero (z : ℤ) :
    ∀ᶠ n : ℕ in atTop,
      (HahnSeries.single (-((n + 1 : ℕ) : ℤ)) (1 : K) : LaurentSeries K).coeff z = 0 := by
  filter_upwards [eventually_ge_atTop (z.natAbs + 1)] with n hn
  rw [HahnSeries.coeff_single]
  split_ifs with h
  · omega
  · rfl

/-- The sequence `X⁻¹, X⁻², ...` does not converge to zero in the Laurent valuation topology,
despite the eventual vanishing of each fixed coefficient. -/
theorem laurentSeries_not_tendsto_single_neg_succ :
    ¬ Tendsto (fun n : ℕ ↦
      (HahnSeries.single (-((n + 1 : ℕ) : ℤ)) (1 : K) : LaurentSeries K)) atTop (nhds 0) := by
  intro h
  obtain ⟨b, hb⟩ := (tendsto_laurentSeries_iff_coeff _ _).1 h |>.1
  obtain ⟨N, hN⟩ := eventually_atTop.1 hb
  let n := N + b.natAbs + 1
  have hn : N ≤ n := by omega
  have hlt : -((n + 1 : ℕ) : ℤ) < b := by
    have hbnd : -b ≤ (b.natAbs : ℤ) := by
      simpa using (Int.le_natAbs (a := -b))
    omega
  have hzero := hN n hn (-((n + 1 : ℕ) : ℤ)) hlt
  simp at hzero

end TauCeti
