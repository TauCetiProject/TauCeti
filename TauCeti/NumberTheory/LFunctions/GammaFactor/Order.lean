/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
module

public import TauCeti.NumberTheory.LFunctions.GammaFactor.Basic
public import TauCeti.Analysis.SpecialFunctions.Gamma.Order
public import TauCeti.Analysis.Meromorphic.Multiset
public import Mathlib.Analysis.Meromorphic.Divisor

/-!
# Orders and divisors of shifted archimedean factors

A record's gamma factor is a finite product of shifted `Gammaℝ` and `Gammaℂ` factors. Each
factor has a simple pole on its own shifted lattice and no zeros as a meromorphic germ.
Consequently the record's order is minus the number of factors whose pole lattice contains
the point, counting repeated parameters and overlaps between the two kinds of factor.

The entire reciprocal has exactly that number as its analytic zero multiplicity. The native
divisors on arbitrary domains evaluate to the negative and positive counts respectively.
These statements concern meromorphic germs: the native total gamma value at a pole is zero.

## References

* H. Iwaniec and E. Kowalski, *Analytic Number Theory* (2004), §5.1.
* The simple factor orders come from `TauCeti.Analysis.SpecialFunctions.Gamma.Order`;
  finite-product order additivity extends Mathlib's `meromorphicOrderAt_mul`.
-/

public section

open Complex

namespace TauCeti.LFunctions.AnalyticLFunctionData

variable (d : AnalyticLFunctionData)

private theorem sum_orders_eq_neg_countP {ι : Type*} (m : Multiset ι)
    (p : ι → Prop) [DecidablePred p]
    (f : ι → WithTop ℤ) (hf : ∀ i, f i = if p i then -1 else 0) :
    (m.map f).sum = (-(m.countP p : ℤ) : WithTop ℤ) := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons i m ih =>
    rw [Multiset.map_cons, Multiset.sum_cons, hf, ih, Multiset.countP_cons]
    split_ifs <;> simp [Nat.cast_add, add_comm]

open Classical in
private theorem gammaR_order (z : ℂ) : meromorphicOrderAt Gammaℝ z =
    if (∃ n : ℕ, z = -(2 * (n : ℂ))) then -1 else 0 := by
  split_ifs with hz
  · exact (meromorphicOrderAt_Gammaℝ_eq_neg_one_iff z).mpr hz
  · exact (meromorphicOrderAt_Gammaℝ_eq_zero_iff z).mpr
      (by rwa [Ne, Gammaℝ_eq_zero_iff])

open Classical in
private theorem gammaC_order (z : ℂ) : meromorphicOrderAt Gammaℂ z =
    if (∃ n : ℕ, z = -(n : ℂ)) then -1 else 0 := by
  split_ifs with hz
  · exact (meromorphicOrderAt_Gammaℂ_eq_neg_one_iff z).mpr hz
  · exact (meromorphicOrderAt_Gammaℂ_eq_zero_iff z).mpr
      (by rwa [Ne, Gammaℂ_eq_zero_iff])

/-- The order of a record's gamma factor is the sum of the shifted factor orders. -/
theorem meromorphicOrderAt_gammaFactor (s : ℂ) :
    meromorphicOrderAt d.gammaFactor s =
      (d.gammaR.map fun μ ↦ meromorphicOrderAt Gammaℝ (s + μ)).sum +
        (d.gammaC.map fun ν ↦ meromorphicOrderAt Gammaℂ (s + ν)).sum := by
  have hR (μ : ℂ) : MeromorphicAt (fun z : ℂ ↦ Gammaℝ (z + μ)) s :=
    (TauCeti.meromorphic_Gammaℝ (s + μ)).comp_analyticAt (g := fun z : ℂ ↦ z + μ) (by fun_prop)
  have hC (ν : ℂ) : MeromorphicAt (fun z : ℂ ↦ Gammaℂ (z + ν)) s :=
    (TauCeti.meromorphic_Gammaℂ (s + ν)).comp_analyticAt (g := fun z : ℂ ↦ z + ν) (by fun_prop)
  have heq : d.gammaFactor = (fun z ↦ (d.gammaR.map fun μ ↦ Gammaℝ (z + μ)).prod) *
      (fun z ↦ (d.gammaC.map fun ν ↦ Gammaℂ (z + ν)).prod) := by
    funext z
    exact d.gammaFactor_def z
  rw [heq, meromorphicOrderAt_mul (MeromorphicAt.fun_multisetProd (fun μ _ ↦ hR μ))
    (MeromorphicAt.fun_multisetProd (fun ν _ ↦ hC ν)),
    meromorphicOrderAt_fun_multisetProd (fun μ _ ↦ hR μ),
    meromorphicOrderAt_fun_multisetProd (fun ν _ ↦ hC ν)]
  simp only [meromorphicOrderAt_fun_comp_add_const_eq_meromorphicOrderAt]

open Classical in
/-- The order is the negative number of matching shifted poles, counting repeated parameters. -/
theorem meromorphicOrderAt_gammaFactor_eq_neg_count (s : ℂ) :
    meromorphicOrderAt d.gammaFactor s =
      (-((d.gammaR.countP fun μ ↦ ∃ n : ℕ, s + μ = -(2 * (n : ℂ))) +
        (d.gammaC.countP fun ν ↦ ∃ n : ℕ, s + ν = -(n : ℂ))) : ℤ) := by
  rw [d.meromorphicOrderAt_gammaFactor,
    sum_orders_eq_neg_countP _ _ _ (fun μ ↦ gammaR_order (s + μ)),
    sum_orders_eq_neg_countP _ _ _ (fun ν ↦ gammaC_order (s + ν))]
  simp [add_comm]

/-- Every record gamma factor is in meromorphic normal form on every set. -/
theorem meromorphicNFOn_gammaFactor {U : Set ℂ} : MeromorphicNFOn d.gammaFactor U := by
  apply meromorphicNFOn_inv.mp
  have h : AnalyticOnNhd ℂ d.invGammaFactor U := fun s _ ↦ d.analyticAt_invGammaFactor s
  simpa only [d.invGammaFactor_eq_inv] using h.meromorphicNFOn

/-- A record gamma factor is meromorphic on every set. -/
@[fun_prop]
theorem meromorphicOn_gammaFactor {U : Set ℂ} : MeromorphicOn d.gammaFactor U :=
  d.meromorphic_gammaFactor.meromorphicOn

/-- Gamma factors have no zeros as meromorphic germs. -/
theorem meromorphicOrderAt_gammaFactor_nonpos (s : ℂ) :
    meromorphicOrderAt d.gammaFactor s ≤ 0 := by
  rw [d.meromorphicOrderAt_gammaFactor_eq_neg_count]
  exact WithTop.coe_le_coe.mpr (by omega)

/-- A record gamma factor has finite order at every point. -/
theorem meromorphicOrderAt_gammaFactor_ne_top (s : ℂ) :
    meromorphicOrderAt d.gammaFactor s ≠ ⊤ := by
  rw [d.meromorphicOrderAt_gammaFactor_eq_neg_count]
  exact WithTop.coe_ne_top

/-- The gamma factor has order zero exactly where its native total value is nonzero. -/
theorem meromorphicOrderAt_gammaFactor_eq_zero_iff (s : ℂ) :
    meromorphicOrderAt d.gammaFactor s = 0 ↔ d.gammaFactor s ≠ 0 :=
  (d.meromorphicNFOn_gammaFactor (Set.mem_univ s)).meromorphicOrderAt_eq_zero_iff

/-- Negative meromorphic order identifies the zero total values at gamma poles. -/
theorem meromorphicOrderAt_gammaFactor_neg_iff (s : ℂ) :
    meromorphicOrderAt d.gammaFactor s < 0 ↔ d.gammaFactor s = 0 := by
  rw [lt_iff_le_and_ne, and_iff_right (d.meromorphicOrderAt_gammaFactor_nonpos s)]
  simpa only [not_not] using not_congr (d.meromorphicOrderAt_gammaFactor_eq_zero_iff s)

/-- The poles are exactly the shifted real and complex gamma pole lattices. -/
theorem meromorphicOrderAt_gammaFactor_neg_iff_exists (s : ℂ) :
    meromorphicOrderAt d.gammaFactor s < 0 ↔
      (∃ μ ∈ d.gammaR, ∃ n : ℕ, s + μ = -(2 * (n : ℂ))) ∨
      (∃ ν ∈ d.gammaC, ∃ n : ℕ, s + ν = -(n : ℂ)) := by
  rw [d.meromorphicOrderAt_gammaFactor_neg_iff, d.gammaFactor_eq_zero_iff]

open Classical in
/-- The order of the entire reciprocal counts all matching shifted poles. -/
theorem meromorphicOrderAt_invGammaFactor_eq_count (s : ℂ) :
    meromorphicOrderAt d.invGammaFactor s =
      (((d.gammaR.countP fun μ ↦ ∃ n : ℕ, s + μ = -(2 * (n : ℂ))) +
        (d.gammaC.countP fun ν ↦ ∃ n : ℕ, s + ν = -(n : ℂ))) : ℕ) := by
  rw [d.meromorphicOrderAt_invGammaFactor, d.meromorphicOrderAt_gammaFactor_eq_neg_count]
  simp

open Classical in
/-- The reciprocal zero multiplicity includes repeated and coincident poles. -/
theorem analyticOrderAt_invGammaFactor_eq_count (s : ℂ) :
    analyticOrderAt d.invGammaFactor s =
      (((d.gammaR.countP fun μ ↦ ∃ n : ℕ, s + μ = -(2 * (n : ℂ))) +
        (d.gammaC.countP fun ν ↦ ∃ n : ℕ, s + ν = -(n : ℂ))) : ℕ) := by
  have hm := d.meromorphicOrderAt_invGammaFactor_eq_count s
  rw [(d.analyticAt_invGammaFactor s).meromorphicOrderAt_eq] at hm
  cases ho : analyticOrderAt d.invGammaFactor s with
  | top =>
    simp only [ho, ENat.map_top] at hm
    exact (WithTop.top_ne_coe hm).elim
  | coe n =>
    simp only [ho, ENat.map_natCast] at hm
    have hn : n = (d.gammaR.countP fun μ ↦ ∃ n : ℕ, s + μ = -(2 * (n : ℂ))) +
        (d.gammaC.countP fun ν ↦ ∃ n : ℕ, s + ν = -(n : ℂ)) := by exact_mod_cast hm
    simp [hn]

open Classical in
/-- On its domain the native gamma divisor is the negative shifted-pole count. -/
theorem divisor_gammaFactor_apply {U : Set ℂ} {s : ℂ} (hs : s ∈ U) :
    MeromorphicOn.divisor d.gammaFactor U s =
      (-((d.gammaR.countP fun μ ↦ ∃ n : ℕ, s + μ = -(2 * (n : ℂ))) +
        (d.gammaC.countP fun ν ↦ ∃ n : ℕ, s + ν = -(n : ℂ))) : ℤ) := by
  rw [d.meromorphicOn_gammaFactor.divisor_apply hs,
    d.meromorphicOrderAt_gammaFactor_eq_neg_count]
  simp

open Classical in
/-- The reciprocal's native divisor is the nonnegative shifted-pole count. -/
theorem divisor_invGammaFactor_apply {U : Set ℂ} {s : ℂ} (hs : s ∈ U) :
    MeromorphicOn.divisor d.invGammaFactor U s =
      (((d.gammaR.countP fun μ ↦ ∃ n : ℕ, s + μ = -(2 * (n : ℂ))) +
        (d.gammaC.countP fun ν ↦ ∃ n : ℕ, s + ν = -(n : ℂ))) : ℕ) := by
  have hm : MeromorphicOn d.invGammaFactor U :=
    fun s _ ↦ (d.analyticAt_invGammaFactor s).meromorphicAt
  rw [hm.divisor_apply hs, d.meromorphicOrderAt_invGammaFactor_eq_count]
  simp

end TauCeti.LFunctions.AnalyticLFunctionData
