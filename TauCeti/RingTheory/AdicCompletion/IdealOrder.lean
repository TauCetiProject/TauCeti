/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import TauCeti.RingTheory.AdicCompletion.Algebra
public import TauCeti.RingTheory.MvPowerSeries.Ideal

/-!
# Ideal order and completion

Maximal-adic completion preserves the local order of every ideal when the maximal ideal is
finitely generated. No regularity, separation or Noetherian hypothesis is required. In particular,
this comparison also retains ideals of infinite order in nonseparated local rings.

Given an identification of the completion with a power-series ring over a field, the order of
an ideal is the infimum of the orders of the expansions of its elements, or of any generating
family. The coefficient field is the field of the chosen identification, not necessarily a
ground field over which the original local ring is an algebra. These results compare algebraic
order with formal-coordinate order without constructing or choosing formal coordinates.

The order convention is that of Bierstone–Milman, *Canonical desingularization in
characteristic zero by blowing up the maximum strata of a local invariant* (1997),
Remark 1.8 and Corollary 3.20.
-/

public section

namespace Ideal

open IsLocalRing

variable {R : Type*} [CommRing R] [IsLocalRing R]

/-- Maximal-adic completion preserves ideal order if the maximal ideal is finitely generated,
even when the original local ring is not separated. -/
theorem localOrder_map_adicCompletion (I : Ideal R) (hfg : (maximalIdeal R).FG) :
    letI := AdicCompletion.isLocalRing_of_fg hfg
    (I.map (algebraMap R (AdicCompletion (maximalIdeal R) R))).localOrder = I.localOrder := by
  let := AdicCompletion.isLocalRing_of_fg hfg
  apply ENat.eq_of_forall_natCast_le_iff
  intro n
  rw [natCast_le_localOrder_iff, natCast_le_localOrder_iff,
    AdicCompletion.maximalIdeal_eq_map_of_fg hfg, ← Ideal.map_pow, map_le_iff_le_comap]
  have hpow : ((maximalIdeal R ^ n).map
      (algebraMap R (AdicCompletion (maximalIdeal R) R))).comap
      (algebraMap R (AdicCompletion (maximalIdeal R) R)) = maximalIdeal R ^ n := by
    ext x
    exact AdicCompletion.algebraMap_mem_map_pow_iff n
  rw [hpow]

variable {σ k : Type*} [Finite σ] [Field k]

/-- In a chosen formal chart of the completion, a principal ideal's local order is the
power-series order of its generator's expansion. -/
theorem localOrder_span_singleton_eq_order_of_completion_equiv (f : R)
    (hfg : (maximalIdeal R).FG)
    (e : AdicCompletion (maximalIdeal R) R ≃+* MvPowerSeries σ k) :
    (span {f}).localOrder =
      (e (algebraMap R (AdicCompletion (maximalIdeal R) R) f)).order := by
  let := AdicCompletion.isLocalRing_of_fg hfg
  rw [← localOrder_map_adicCompletion (span {f}) hfg,
    ← localOrder_map_equiv _ e]
  simp [Ideal.map_span]

/-- In a chosen formal chart of the completion, the local order of a generated ideal is the
infimum of its generators' expansion orders. This includes an empty family, with infimum `∞`.
No finiteness hypothesis on the generating family is needed. -/
theorem localOrder_span_range_eq_iInf_order_of_completion_equiv {ι : Type*} (f : ι → R)
    (hfg : (maximalIdeal R).FG)
    (e : AdicCompletion (maximalIdeal R) R ≃+* MvPowerSeries σ k) :
    (span (Set.range f)).localOrder =
      ⨅ i, (e (algebraMap R (AdicCompletion (maximalIdeal R) R) (f i))).order := by
  rw [localOrder_span_range]
  simp_rw [localOrder_span_singleton_eq_order_of_completion_equiv _ hfg e]

/-- In a chosen formal chart of the completion, an ideal's order is the infimum of the
power-series orders of the expansions of its elements, not their sum. -/
theorem localOrder_eq_iInf_order_of_completion_equiv (I : Ideal R)
    (hfg : (maximalIdeal R).FG)
    (e : AdicCompletion (maximalIdeal R) R ≃+* MvPowerSeries σ k) :
    I.localOrder = ⨅ f : I,
      (e (algebraMap R (AdicCompletion (maximalIdeal R) R) (f : R))).order := by
  simpa only [I.span_eq, localOrder_span_singleton_eq_order_of_completion_equiv _ hfg e,
    iInf_subtype, SetLike.mem_coe] using localOrder_span (I : Set R)

end Ideal
