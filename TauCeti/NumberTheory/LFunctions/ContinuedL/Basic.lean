/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LFunctions.Data.Comparison
public import TauCeti.NumberTheory.LFunctions.GammaFactor.Order
public import TauCeti.NumberTheory.LFunctions.Zeros.Completion.Basic
import Mathlib.NumberTheory.LSeries.Deriv
import Mathlib.NumberTheory.LSeries.Injectivity
import TauCeti.Analysis.Meromorphic.Conj
import TauCeti.Analysis.SpecialFunctions.Pow.Complex

/-!
# The continued uncompleted L-function of an analytic L-function record

Given an `AnalyticLFunctionData` record `d` with completed function `Λ(s)`, conductor `N`, and
entire reciprocal archimedean factor `d.invGammaFactor`, the naive product
`R d s = N^(-s / 2) * Λ(s) * d.invGammaFactor s` recovers the uncompleted L-function off the
support of `d.polarOrder`, including at trivial zeros arising from poles of `γ(s)`. However, at
any point of `d.polarOrder.support` where `(d.polarOrder s : WithTop ℤ) ≤
meromorphicOrderAt d.invGammaFactor s`, the pointwise product multiplies `d.completed s` by `0`:
for the Riemann zeta record at `s = 0`, `completedRiemannZeta 0 * (Gammaℝ 0)⁻¹ = 0`, whereas
`riemannZeta 0 = -1 / 2`. Conversely, at points where `meromorphicOrderAt d.invGammaFactor s <
(d.polarOrder s : WithTop ℤ)` (such as `s = 1` for `riemannZeta`, where `riemannZeta 1 ≠ 0`),
global conversion via `toMeromorphicNFOn` would overwrite the value with `0`.

`AnalyticLFunctionData.continuedL` evaluates `toMeromorphicNFAt (R d) s s` at the finitely many
points `s ∈ d.polarOrder.support` satisfying `(d.polarOrder s : WithTop ℤ) ≤
meromorphicOrderAt d.invGammaFactor s`, while retaining the pointwise product `R d s` everywhere
else. Under `HasMeromorphicContinuation`, this analytically extends `R d` across every cancelled
pole while preserving values at uncancelled poles. Consequently, for `riemannZetaData` and for
every primitive Dirichlet record `dirichletData χ hχ`, `continuedL` agrees with Mathlib's
`riemannZeta` and `χ.LFunction` at every point of `ℂ`.

## Main definitions

* `TauCeti.LFunctions.AnalyticLFunctionData.continuedL`: the continued uncompleted L-function
  attached to `d`.

## Main results

* `continuedL_eventuallyEq`, `completed_eventuallyEq_mul_continuedL`, `completed_eq_mul_continuedL`:
  relations between `d.completed` and `d.continuedL` without continuation hypotheses on `d`, as
  punctured germs everywhere and pointwise where `d.gammaFactor s ≠ 0`.
* `continuedL_dual`, `EqOffZero.continuedL_eq`: compatibility with duality and `EqOffZero`.
* `analyticAt_continuedL`, `meromorphicOrderAt_continuedL`: analyticity wherever `d.completed` is
  analytic, and exact order identity
  `meromorphicOrderAt d.continuedL s = meromorphicOrderAt d.completed s -
  meromorphicOrderAt d.gammaFactor s`.
* `HasMeromorphicContinuation.meromorphicOrderAt_continuedL_nonneg_iff`,
  `HasMeromorphicContinuation.meromorphicOrderAt_continuedL_neg_iff`,
  `HasMeromorphicContinuation.meromorphicOrderAt_continuedL_nonneg_iff_analyticAt`,
  `HasMeromorphicContinuation.continuedL_eq_of_tendsto`: pole-cancellation criteria, canonical
  analyticity at nonnegative order, and punctured-limit evaluation of `d.continuedL`.
* `meromorphicOrderAt_continuedL_pos_iff`, `continuedL_eq_zero_of_gammaFactor_eq_zero`:
  characterization of trivial zeros at poles of `d.gammaFactor`.
* `HasDirichletAgreement.continuedL_eq_LSeries`: agreement with `LSeries d.coeff` on `1 < s.re`,
  extending across any poles of `d.gammaFactor` in that half-plane.
* `HasFunctionalEquation.gammaFactor_mul_continuedL_eq`,
  `HasFunctionalEquation.gammaFactor_mul_continuedL_eventuallyEq`: asymmetric functional equation
  against `d.dual`, pointwise off `d.polarOrder.support` and gamma zeros, and as punctured germs
  everywhere.
* `polarPolynomial_mul_continuedL_eventuallyEq`,
  `HasMeromorphicContinuation.polarPolynomial_mul_continuedL_eq`: germ and pointwise bridges to
  `d.entireCompletion` multiplied by `N^(-s / 2)` and `d.invGammaFactor`.

## References

* H. Iwaniec and E. Kowalski, *Analytic Number Theory*, AMS Colloquium Publications 53 (2004),
  §5.1.
* H. Davenport, *Multiplicative Number Theory*, 3rd ed., §§11–12.
-/

public section

open Complex ComplexConjugate Filter Set Topology

namespace TauCeti.LFunctions.AnalyticLFunctionData

/-- The unextended product `N^(-s / 2) * Λ(s) * γ(s)⁻¹` used to build `continuedL`. -/
private noncomputable def rawContinuedL (d : AnalyticLFunctionData) (s : ℂ) : ℂ :=
  ((d.conductor : ℕ) : ℂ) ^ (-s / 2) * d.completed s * d.invGammaFactor s

private theorem conductor_cast_ne_zero (d : AnalyticLFunctionData) :
    ((d.conductor : ℕ) : ℂ) ≠ 0 := by
  exact_mod_cast d.conductor.ne_zero

private theorem conductor_cpow_ne_zero (d : AnalyticLFunctionData) (w : ℂ) :
    ((d.conductor : ℕ) : ℂ) ^ w ≠ 0 :=
  cpow_ne_zero_iff.mpr (Or.inl d.conductor_cast_ne_zero)

private theorem conductor_cpow_mul_neg_div_two (d : AnalyticLFunctionData) (s : ℂ) :
    ((d.conductor : ℕ) : ℂ) ^ (s / 2) * ((d.conductor : ℕ) : ℂ) ^ (-s / 2) = 1 := by
  rw [← cpow_add _ _ d.conductor_cast_ne_zero]
  have hz : s / 2 + -s / 2 = 0 := by ring
  rw [hz, cpow_zero]

private theorem conductor_cpow_neg_mul_div_two (d : AnalyticLFunctionData) (s : ℂ) :
    ((d.conductor : ℕ) : ℂ) ^ (-s / 2) * ((d.conductor : ℕ) : ℂ) ^ (s / 2) = 1 := by
  rw [mul_comm]
  exact d.conductor_cpow_mul_neg_div_two s

private theorem analyticAt_conductor_cpow_div_two (d : AnalyticLFunctionData) (s : ℂ) :
    AnalyticAt ℂ (fun z : ℂ ↦ ((d.conductor : ℕ) : ℂ) ^ (z / 2)) s :=
  ((differentiable_id.div_const (2 : ℂ)).const_cpow
    (Or.inl d.conductor_cast_ne_zero)).analyticAt s

private theorem analyticAt_conductor_cpow_neg_div_two (d : AnalyticLFunctionData) (s : ℂ) :
    AnalyticAt ℂ (fun z : ℂ ↦ ((d.conductor : ℕ) : ℂ) ^ (-z / 2)) s :=
  ((differentiable_id.neg.div_const (2 : ℂ)).const_cpow
    (Or.inl d.conductor_cast_ne_zero)).analyticAt s

private theorem meromorphicOrderAt_conductor_cpow_neg_div_two (d : AnalyticLFunctionData) (s : ℂ) :
    meromorphicOrderAt (fun z : ℂ ↦ ((d.conductor : ℕ) : ℂ) ^ (-z / 2)) s = 0 :=
  (d.analyticAt_conductor_cpow_neg_div_two s).meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.2
    (d.conductor_cpow_ne_zero _)

private theorem polarOrder_eventually_eq_zero (d : AnalyticLFunctionData) (s : ℂ) :
    ∀ᶠ z in 𝓝[≠] s, d.polarOrder z = 0 := by
  filter_upwards [nhdsNE_of_nhdsNE_sdiff_finite univ_mem
    d.polarOrder.support.finite_toSet.to_subtype] with z hz
  simpa only [Set.mem_sdiff, mem_univ, Finset.mem_coe, Finsupp.mem_support_iff, true_and,
    not_not] using hz

private theorem gammaFactor_eventually_ne_zero (d : AnalyticLFunctionData) (s : ℂ) :
    ∀ᶠ z in 𝓝[≠] s, d.gammaFactor z ≠ 0 :=
  (meromorphicOrderAt_ne_top_iff_eventually_ne_zero (d.meromorphic_gammaFactor s)).1
    (d.meromorphicOrderAt_gammaFactor_ne_top s)

open scoped Classical in
/-- **The continued uncompleted L-function** of an analytic L-function record `d`. At points `s` of
the recorded polar divisor (`d.polarOrder s ≠ 0`) with `(d.polarOrder s : WithTop ℤ) ≤
meromorphicOrderAt d.invGammaFactor s`, this evaluates the local meromorphic normal form
`toMeromorphicNFAt` of `z ↦ N^(-z / 2) * d.completed z * d.invGammaFactor z` (giving the analytic
extension across cancelled poles when `d.HasMeromorphicContinuation` holds); at all other points it
retains the pointwise product. -/
noncomputable def continuedL (d : AnalyticLFunctionData) (s : ℂ) : ℂ :=
  if d.polarOrder s ≠ 0 ∧ (d.polarOrder s : WithTop ℤ) ≤ meromorphicOrderAt d.invGammaFactor s
  then toMeromorphicNFAt
    (fun z ↦ ((d.conductor : ℕ) : ℂ) ^ (-z / 2) * d.completed z * d.invGammaFactor z) s s
  else ((d.conductor : ℕ) : ℂ) ^ (-s / 2) * d.completed s * d.invGammaFactor s

open scoped Classical in
theorem continuedL_def (d : AnalyticLFunctionData) (s : ℂ) :
    d.continuedL s =
      if d.polarOrder s ≠ 0 ∧ (d.polarOrder s : WithTop ℤ) ≤ meromorphicOrderAt d.invGammaFactor s
      then toMeromorphicNFAt
        (fun z ↦ ((d.conductor : ℕ) : ℂ) ^ (-z / 2) * d.completed z * d.invGammaFactor z) s s
      else ((d.conductor : ℕ) : ℂ) ^ (-s / 2) * d.completed s * d.invGammaFactor s := (rfl)

section Basic

variable (d : AnalyticLFunctionData)

/-- Off the support of `d.polarOrder`, `continuedL` is the pointwise product
`N^(-s / 2) * d.completed s * d.invGammaFactor s`. -/
theorem continuedL_eq_of_polarOrder_eq_zero {s : ℂ} (hs : d.polarOrder s = 0) :
    d.continuedL s = ((d.conductor : ℕ) : ℂ) ^ (-s / 2) * d.completed s * d.invGammaFactor s := by
  simp [continuedL_def, hs]

/-- If the meromorphic order of `d.invGammaFactor` at `s` is strictly smaller than `d.polarOrder s`
(an uncancelled pole under `HasMeromorphicContinuation`), `continuedL` retains the pointwise
product. -/
theorem continuedL_eq_of_meromorphicOrderAt_invGammaFactor_lt_polarOrder {s : ℂ}
    (hs : meromorphicOrderAt d.invGammaFactor s < (d.polarOrder s : WithTop ℤ)) :
    d.continuedL s = ((d.conductor : ℕ) : ℂ) ^ (-s / 2) * d.completed s * d.invGammaFactor s := by
  rw [continuedL_def]
  split_ifs with h
  · exact absurd hs (not_lt_of_ge h.2)
  · rfl

/-- At a point in the support of `d.polarOrder` where `(d.polarOrder s : WithTop ℤ) ≤
meromorphicOrderAt d.invGammaFactor s`, `continuedL` evaluates the local meromorphic normal form of
`N^(-z / 2) * d.completed z * d.invGammaFactor z`. -/
theorem continuedL_eq_toMeromorphicNFAt {s : ℂ} (hp : d.polarOrder s ≠ 0)
    (hle : (d.polarOrder s : WithTop ℤ) ≤ meromorphicOrderAt d.invGammaFactor s) :
    d.continuedL s = toMeromorphicNFAt
      (fun z ↦ ((d.conductor : ℕ) : ℂ) ^ (-z / 2) * d.completed z * d.invGammaFactor z) s s := by
  rw [continuedL_def]
  split_ifs with h
  · rfl
  · exact absurd ⟨hp, hle⟩ h

/-- Wherever `d.gammaFactor s ≠ 0`, `continuedL` equals `N^(-s / 2) * d.completed s *
(d.gammaFactor s)⁻¹`, without any continuation hypothesis on `d`. -/
theorem continuedL_eq_of_gammaFactor_ne_zero {s : ℂ} (hs : d.gammaFactor s ≠ 0) :
    d.continuedL s =
      ((d.conductor : ℕ) : ℂ) ^ (-s / 2) * d.completed s * (d.gammaFactor s)⁻¹ := by
  have hinv : d.invGammaFactor s ≠ 0 := by rwa [ne_eq, invGammaFactor_eq_zero_iff]
  have hord : meromorphicOrderAt d.invGammaFactor s = 0 :=
    (d.analyticAt_invGammaFactor s).meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.2 hinv
  rw [continuedL_def, ← invGammaFactor_def]
  split_ifs with h
  · rcases h with ⟨hp, hle⟩
    rw [hord] at hle
    have hle' : (d.polarOrder s : ℤ) ≤ 0 := WithTop.coe_le_coe.mp hle
    exact absurd (by omega) hp
  · rfl

/-- Off the support of `d.polarOrder` (`d.polarOrder s = 0`), if `d.gammaFactor s = 0` then
`d.continuedL s = 0`. Both hypotheses are needed: at `s = 0` for `riemannZetaData`, `Gammaℝ 0 = 0`
while `riemannZetaData.continuedL 0 = -1 / 2`. -/
theorem continuedL_eq_zero_of_gammaFactor_eq_zero {s : ℂ} (hp : d.polarOrder s = 0)
    (hγ : d.gammaFactor s = 0) : d.continuedL s = 0 := by
  rw [d.continuedL_eq_of_polarOrder_eq_zero hp, invGammaFactor_def, hγ, inv_zero, mul_zero]

/-- On a punctured neighbourhood of every `s : ℂ`, `d.continuedL` agrees with
`z ↦ N^(-z / 2) * d.completed z * d.invGammaFactor z`, since `d.polarOrder` has finite support. -/
theorem continuedL_eventuallyEq (s : ℂ) :
    d.continuedL =ᶠ[𝓝[≠] s]
      fun z ↦ ((d.conductor : ℕ) : ℂ) ^ (-z / 2) * d.completed z * d.invGammaFactor z :=
  (d.polarOrder_eventually_eq_zero s).mono fun _ ↦ d.continuedL_eq_of_polarOrder_eq_zero

/-- Wherever `d.gammaFactor s ≠ 0`, the completed function factors pointwise as
`d.completed s = N^(s / 2) * d.gammaFactor s * d.continuedL s`. -/
theorem completed_eq_mul_continuedL {s : ℂ} (hs : d.gammaFactor s ≠ 0) :
    d.completed s = ((d.conductor : ℕ) : ℂ) ^ (s / 2) * d.gammaFactor s * d.continuedL s := by
  rw [d.continuedL_eq_of_gammaFactor_ne_zero hs]
  calc
    d.completed s = (((d.conductor : ℕ) : ℂ) ^ (s / 2) * ((d.conductor : ℕ) : ℂ) ^ (-s / 2)) *
        (d.gammaFactor s * (d.gammaFactor s)⁻¹) * d.completed s := by
      rw [d.conductor_cpow_mul_neg_div_two s, mul_inv_cancel₀ hs, one_mul, one_mul]
    _ = ((d.conductor : ℕ) : ℂ) ^ (s / 2) * d.gammaFactor s *
        (((d.conductor : ℕ) : ℂ) ^ (-s / 2) * d.completed s * (d.gammaFactor s)⁻¹) := by ring

/-- On a punctured neighbourhood of every `s : ℂ`, `d.completed` agrees as a germ with
`z ↦ N^(z / 2) * d.gammaFactor z * d.continuedL z`. -/
theorem completed_eventuallyEq_mul_continuedL (s : ℂ) :
    d.completed =ᶠ[𝓝[≠] s]
      fun z ↦ ((d.conductor : ℕ) : ℂ) ^ (z / 2) * d.gammaFactor z * d.continuedL z :=
  (d.gammaFactor_eventually_ne_zero s).mono fun _ ↦ d.completed_eq_mul_continuedL

/-- If `d.polarOrder = 0`, `continuedL` is everywhere equal to the pointwise product
`N^(-s / 2) * d.completed s * d.invGammaFactor s`. -/
theorem continuedL_eq_of_polarOrder_eq_zero' (hp : d.polarOrder = 0) (s : ℂ) :
    d.continuedL s = ((d.conductor : ℕ) : ℂ) ^ (-s / 2) * d.completed s * d.invGammaFactor s :=
  d.continuedL_eq_of_polarOrder_eq_zero (by simp [hp])

private theorem rawContinuedL_def :
    rawContinuedL d =
      fun z ↦ ((d.conductor : ℕ) : ℂ) ^ (-z / 2) * d.completed z * d.invGammaFactor z := (rfl)

private theorem rawContinuedL_dual (s : ℂ) :
    rawContinuedL d.dual s = conj (rawContinuedL d (conj s)) := by
  have hN := TauCeti.ofReal_cpow_conj (d.conductor : ℕ).cast_nonneg (-conj s / 2)
  rw [Complex.ofReal_natCast, map_div₀, map_neg, Complex.conj_conj, map_ofNat] at hN
  have hinv : d.dual.invGammaFactor s = conj (d.invGammaFactor (conj s)) := by
    simpa only [Complex.star_def] using d.invGammaFactor_dual s
  simp only [rawContinuedL, dual_conductor, dual_completed_apply, hinv, map_mul, hN]

/-- The continued L-function of the dual card is the reflection `s ↦ conj (d.continuedL (conj s))`,
pointwise on all of `ℂ` and without any continuation hypothesis. -/
theorem continuedL_dual_apply (s : ℂ) :
    d.dual.continuedL s = conj (d.continuedL (conj s)) := by
  have hraw : rawContinuedL d.dual = conj ∘ rawContinuedL d ∘ conj := funext d.rawContinuedL_dual
  have hinv_eq : d.dual.invGammaFactor = conj ∘ d.invGammaFactor ∘ conj :=
    funext fun z ↦ by
      simpa only [Complex.star_def, Function.comp_apply] using d.invGammaFactor_dual z
  have hord : meromorphicOrderAt d.dual.invGammaFactor s =
      meromorphicOrderAt d.invGammaFactor (conj s) := by
    rw [hinv_eq, TauCeti.meromorphicOrderAt_conj_conj]
  rw [continuedL_def, continuedL_def, ← d.dual.rawContinuedL_def, ← d.rawContinuedL_def,
    dual_polarOrder_apply, hord]
  split_ifs
  · rw [hraw, TauCeti.toMeromorphicNFAt_conj_conj_apply]
  · exact d.rawContinuedL_dual s

/-- Function-level form of `continuedL_dual_apply`. -/
@[simp]
theorem continuedL_dual : d.dual.continuedL = conj ∘ d.continuedL ∘ conj :=
  funext d.continuedL_dual_apply

end Basic

section Comparison

variable {d e : AnalyticLFunctionData}

/-- Cards related by `EqOffZero` have identical continued L-functions, since `continuedL` does not
read `coeff`. -/
theorem EqOffZero.continuedL_eq (h : d.EqOffZero e) : d.continuedL = e.continuedL := by
  have hinv : d.invGammaFactor = e.invGammaFactor := by
    funext z
    rw [invGammaFactor_def, invGammaFactor_def, h.gammaFactor_eq]
  funext s
  simp only [continuedL_def, h.conductor_eq, h.completed_eq, h.polarOrder_eq, hinv]

end Comparison

section Meromorphic

variable {d : AnalyticLFunctionData}

/-- `d.continuedL` is meromorphic at `s` if and only if `d.completed` is meromorphic at `s`. -/
@[simp]
theorem meromorphicAt_continuedL_iff (s : ℂ) :
    MeromorphicAt d.continuedL s ↔ MeromorphicAt d.completed s := by
  constructor
  · intro hc
    exact ((d.analyticAt_conductor_cpow_div_two s).meromorphicAt.mul
      (d.meromorphic_gammaFactor s) |>.mul hc).congr
        (d.completed_eventuallyEq_mul_continuedL s).symm
  · intro hc
    exact ((d.analyticAt_conductor_cpow_neg_div_two s).meromorphicAt.mul hc |>.mul
      (d.analyticAt_invGammaFactor s).meromorphicAt).congr (d.continuedL_eventuallyEq s).symm

/-- `d.continuedL` is meromorphic on `ℂ` if and only if `d.completed` is meromorphic on `ℂ`. -/
@[simp]
theorem meromorphic_continuedL_iff : Meromorphic d.continuedL ↔ Meromorphic d.completed :=
  forall_congr' meromorphicAt_continuedL_iff

/-- Whenever `d.completed` is analytic at `s`, `d.continuedL` is analytic at `s`. -/
theorem analyticAt_continuedL {s : ℂ} (hc : AnalyticAt ℂ d.completed s) :
    AnalyticAt ℂ d.continuedL s := by
  have han_raw : AnalyticAt ℂ (rawContinuedL d) s :=
    ((d.analyticAt_conductor_cpow_neg_div_two s).mul hc).mul (d.analyticAt_invGammaFactor s)
  have hval : d.continuedL s = rawContinuedL d s := by
    rw [continuedL_def, ← d.rawContinuedL_def]
    split_ifs
    · rw [toMeromorphicNFAt_eq_self.mpr han_raw.meromorphicNFAt]
    · rfl
  exact (analyticAt_congr
    (eventuallyEq_nhds_of_eventuallyEq_nhdsNE (d.continuedL_eventuallyEq s) hval)).2 han_raw

/-- **Order identity for `continuedL`.** Wherever `d.completed` is meromorphic at `s`,
`meromorphicOrderAt d.continuedL s = meromorphicOrderAt d.completed s -
meromorphicOrderAt d.gammaFactor s`. -/
theorem meromorphicOrderAt_continuedL {s : ℂ} (hc : MeromorphicAt d.completed s) :
    meromorphicOrderAt d.continuedL s =
      meromorphicOrderAt d.completed s - meromorphicOrderAt d.gammaFactor s := by
  have hφ : MeromorphicAt (fun z : ℂ ↦ ((d.conductor : ℕ) : ℂ) ^ (-z / 2)) s :=
    (d.analyticAt_conductor_cpow_neg_div_two s).meromorphicAt
  have hinv : MeromorphicAt d.invGammaFactor s := (d.analyticAt_invGammaFactor s).meromorphicAt
  rw [meromorphicOrderAt_congr (d.continuedL_eventuallyEq s),
    fun_meromorphicOrderAt_mul (f := fun z ↦ ((d.conductor : ℕ) : ℂ) ^ (-z / 2) * d.completed z)
      (g := d.invGammaFactor) (hφ.mul hc) hinv,
    fun_meromorphicOrderAt_mul hφ hc, d.meromorphicOrderAt_conductor_cpow_neg_div_two s, zero_add,
    d.meromorphicOrderAt_invGammaFactor, sub_eq_add_neg]

/-- **Characterization of trivial zeros.** At any point `s` where `d.completed` is analytic and
nonzero, `d.continuedL` has positive meromorphic order at `s` if and only if `d.gammaFactor s = 0`
(that is, `s` lies on the shifted pole lattice of the archimedean gamma factor). -/
theorem meromorphicOrderAt_continuedL_pos_iff {s : ℂ} (hc : AnalyticAt ℂ d.completed s)
    (hne : d.completed s ≠ 0) :
    0 < meromorphicOrderAt d.continuedL s ↔ d.gammaFactor s = 0 := by
  have hord_c : meromorphicOrderAt d.completed s = 0 :=
    hc.meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.2 hne
  rw [meromorphicOrderAt_continuedL hc.meromorphicAt, hord_c, zero_sub,
    ← d.meromorphicOrderAt_invGammaFactor, ← d.invGammaFactor_eq_zero_iff_meromorphicOrderAt_pos,
    invGammaFactor_eq_zero_iff]

/-- Under `HasMeromorphicContinuation`, `d.continuedL` is globally meromorphic on `ℂ`. -/
theorem HasMeromorphicContinuation.meromorphic_continuedL (h : d.HasMeromorphicContinuation) :
    Meromorphic d.continuedL :=
  meromorphic_continuedL_iff.2 h.meromorphic

/-- Off the support of `d.polarOrder`, a meromorphically continued card has analytic
`continuedL`. -/
theorem HasMeromorphicContinuation.analyticAt_continuedL_of_polarOrder_eq_zero
    (h : d.HasMeromorphicContinuation) {s : ℂ} (hp : d.polarOrder s = 0) :
    AnalyticAt ℂ d.continuedL s :=
  analyticAt_continuedL (h.analyticAt s hp)

/-- For a meromorphically continued card, `d.continuedL` has nonnegative meromorphic order at `s`
if and only if `d.polarOrder s` does not exceed the vanishing order of `d.invGammaFactor` at `s`. -/
theorem HasMeromorphicContinuation.meromorphicOrderAt_continuedL_nonneg_iff
    (h : d.HasMeromorphicContinuation) (s : ℂ) :
    0 ≤ meromorphicOrderAt d.continuedL s ↔
      (d.polarOrder s : WithTop ℤ) ≤ meromorphicOrderAt d.invGammaFactor s := by
  by_cases hp : d.polarOrder s = 0
  · simp [hp, (h.analyticAt_continuedL_of_polarOrder_eq_zero hp).meromorphicOrderAt_nonneg,
      (d.analyticAt_invGammaFactor s).meromorphicOrderAt_nonneg]
  · rw [meromorphicOrderAt_continuedL (h.meromorphic s), h.meromorphicOrderAt_eq s hp,
      sub_eq_add_neg, ← d.meromorphicOrderAt_invGammaFactor,
      d.meromorphicOrderAt_invGammaFactor_eq_count s]
    norm_cast
    omega

/-- For a meromorphically continued card, `d.continuedL` has a pole at `s`
(`meromorphicOrderAt d.continuedL s < 0`) if and only if the vanishing order of `d.invGammaFactor`
at `s` is strictly smaller than `d.polarOrder s`. -/
theorem HasMeromorphicContinuation.meromorphicOrderAt_continuedL_neg_iff
    (h : d.HasMeromorphicContinuation) (s : ℂ) :
    meromorphicOrderAt d.continuedL s < 0 ↔
      meromorphicOrderAt d.invGammaFactor s < (d.polarOrder s : WithTop ℤ) := by
  simpa only [not_le] using (h.meromorphicOrderAt_continuedL_nonneg_iff s).not

/-- **Canonical analyticity at nonnegative order.** For a meromorphically continued card `d`,
`0 ≤ meromorphicOrderAt d.continuedL s` if and only if `d.continuedL` is analytic at `s`. At
recorded poles cancelled by `d.invGammaFactor`, this relies on the normal-form extension in
`continuedL`. -/
theorem HasMeromorphicContinuation.meromorphicOrderAt_continuedL_nonneg_iff_analyticAt
    (h : d.HasMeromorphicContinuation) (s : ℂ) :
    0 ≤ meromorphicOrderAt d.continuedL s ↔ AnalyticAt ℂ d.continuedL s := by
  refine ⟨fun hord ↦ ?_, AnalyticAt.meromorphicOrderAt_nonneg⟩
  by_cases hp : d.polarOrder s = 0
  · exact h.analyticAt_continuedL_of_polarOrder_eq_zero hp
  · have hm_raw : MeromorphicAt (rawContinuedL d) s :=
      ((d.analyticAt_conductor_cpow_neg_div_two s).meromorphicAt.mul (h.meromorphic s)).mul
        (d.analyticAt_invGammaFactor s).meromorphicAt
    have hle := (h.meromorphicOrderAt_continuedL_nonneg_iff s).1 hord
    have hord_raw : 0 ≤ meromorphicOrderAt (rawContinuedL d) s := by
      rwa [d.rawContinuedL_def, ← meromorphicOrderAt_congr (d.continuedL_eventuallyEq s)]
    have han_nf : AnalyticAt ℂ (toMeromorphicNFAt (rawContinuedL d) s) s :=
      hm_raw.meromorphicOrderAt_nonneg_iff_analyticAt_toMeromorphicNFAt.1 hord_raw
    have hnhds : d.continuedL =ᶠ[𝓝 s] toMeromorphicNFAt (rawContinuedL d) s :=
      eventuallyEq_nhds_of_eventuallyEq_nhdsNE
        ((d.continuedL_eventuallyEq s).trans hm_raw.eq_nhdsNE_toMeromorphicNFAt)
        (d.continuedL_eq_toMeromorphicNFAt hp hle)
    exact (analyticAt_congr hnhds).2 han_nf

/-- If `d` has meromorphic continuation and `d.continuedL` tends to `a` on `𝓝[≠] s`, then
`d.continuedL s = a` (including at poles of `d.completed` cancelled by `d.invGammaFactor`). -/
theorem HasMeromorphicContinuation.continuedL_eq_of_tendsto
    (h : d.HasMeromorphicContinuation) {s a : ℂ}
    (hlim : Tendsto d.continuedL (𝓝[≠] s) (𝓝 a)) : d.continuedL s = a := by
  have hord : 0 ≤ meromorphicOrderAt d.continuedL s :=
    (tendsto_nhds_iff_meromorphicOrderAt_nonneg (h.meromorphic_continuedL s)).1 ⟨a, hlim⟩
  have han : AnalyticAt ℂ d.continuedL s :=
    (h.meromorphicOrderAt_continuedL_nonneg_iff_analyticAt s).1 hord
  exact tendsto_nhds_unique han.continuousAt.continuousWithinAt.tendsto hlim

/-- At every point where `0 ≤ meromorphicOrderAt d.continuedL s`, conversion to meromorphic normal
form on `U` preserves the value of `d.continuedL` at `s`. -/
theorem HasMeromorphicContinuation.toMeromorphicNFOn_continuedL_apply_of_meromorphicOrderAt_nonneg
    (h : d.HasMeromorphicContinuation) {U : Set ℂ} {s : ℂ}
    (hs : 0 ≤ meromorphicOrderAt d.continuedL s) :
    toMeromorphicNFOn d.continuedL U s = d.continuedL s := by
  by_cases hsU : s ∈ U
  · rw [toMeromorphicNFOn_eq_toMeromorphicNFAt h.meromorphic_continuedL.meromorphicOn hsU,
      toMeromorphicNFAt_eq_self.mpr
        ((h.meromorphicOrderAt_continuedL_nonneg_iff_analyticAt s).1 hs).meromorphicNFAt]
  · exact toMeromorphicNFOn_eq_self_on_compl h.meromorphic_continuedL.meromorphicOn hsU

/-- If `d.completed` is in meromorphic normal form at `s`, then `d.continuedL` is also in
meromorphic normal form at `s`. -/
theorem HasMeromorphicContinuation.meromorphicNFAt_continuedL
    (h : d.HasMeromorphicContinuation) {s : ℂ} (hnf : MeromorphicNFAt d.completed s) :
    MeromorphicNFAt d.continuedL s := by
  rcases le_or_gt 0 (meromorphicOrderAt d.continuedL s) with hge | hlt
  · exact ((h.meromorphicOrderAt_continuedL_nonneg_iff_analyticAt s).1 hge).meromorphicNFAt
  · have hlt_pol := (h.meromorphicOrderAt_continuedL_neg_iff s).1 hlt
    have hc0 : d.completed s = 0 := by
      rcases meromorphicNFAt_iff_analyticAt_or.mp hnf with han | ⟨-, -, hc0⟩
      · exact absurd (analyticAt_continuedL han).meromorphicOrderAt_nonneg (not_le_of_gt hlt)
      · exact hc0
    refine meromorphicNFAt_iff_analyticAt_or.mpr (Or.inr ⟨h.meromorphic_continuedL s, hlt, ?_⟩)
    rw [d.continuedL_eq_of_meromorphicOrderAt_invGammaFactor_lt_polarOrder hlt_pol, hc0,
      mul_zero, zero_mul]

/-- If `d.completed` is in meromorphic normal form on `U` (for instance on `univ` for
`AnalyticLFunctionData.ofSeries`), then `d.continuedL` is also in meromorphic normal form on `U`. -/
theorem HasMeromorphicContinuation.meromorphicNFOn_continuedL (h : d.HasMeromorphicContinuation)
    {U : Set ℂ} (hnf : MeromorphicNFOn d.completed U) : MeromorphicNFOn d.continuedL U :=
  fun _ hs ↦ h.meromorphicNFAt_continuedL (hnf hs)

/-- Punctured-germ bridge from `d.polarPolynomial.eval z * d.continuedL z` to
`d.entireCompletion`. Meromorphicity of `d.completed` cannot be dropped, since `d.entireCompletion`
is `0` when `d.completed` is not globally meromorphic. -/
theorem polarPolynomial_mul_continuedL_eventuallyEq (hm : Meromorphic d.completed) (s : ℂ) :
    (fun z ↦ d.polarPolynomial.eval z * d.continuedL z) =ᶠ[𝓝[≠] s]
      fun z ↦ ((d.conductor : ℕ) : ℂ) ^ (-z / 2) * d.entireCompletion z * d.invGammaFactor z := by
  have hm_prod : MeromorphicOn (fun z ↦ d.polarPolynomial.eval z * d.completed z) univ :=
    fun z _ ↦ (AnalyticOnNhd.eval_polynomial d.polarPolynomial z trivial).meromorphicAt.mul (hm z)
  filter_upwards [d.continuedL_eventuallyEq s,
    hm_prod.toMeromorphicNFOn_eq_self_on_nhdsNE (mem_univ s)] with z hz hent
  rw [entireCompletion_def, hent, hz]
  ring

/-- Pointwise bridge from `d.polarPolynomial.eval s * d.continuedL s` to `d.entireCompletion s`,
valid at every point where `0 ≤ meromorphicOrderAt d.continuedL s` (both off poles and at cancelled
poles). At uncancelled poles where `d.gammaFactor s ≠ 0` the equality fails (`0` on the left vs. a
nonzero value on the right for `riemannZetaData` at `s = 1`). -/
theorem HasMeromorphicContinuation.polarPolynomial_mul_continuedL_eq
    (h : d.HasMeromorphicContinuation) {s : ℂ} (hs : 0 ≤ meromorphicOrderAt d.continuedL s) :
    d.polarPolynomial.eval s * d.continuedL s =
      ((d.conductor : ℕ) : ℂ) ^ (-s / 2) * d.entireCompletion s * d.invGammaFactor s := by
  have hanL : AnalyticAt ℂ (fun z ↦ d.polarPolynomial.eval z * d.continuedL z) s :=
    (AnalyticOnNhd.eval_polynomial d.polarPolynomial s trivial).mul
      ((h.meromorphicOrderAt_continuedL_nonneg_iff_analyticAt s).1 hs)
  have hanR : AnalyticAt ℂ
      (fun z ↦ ((d.conductor : ℕ) : ℂ) ^ (-z / 2) * d.entireCompletion z * d.invGammaFactor z) s :=
    ((d.analyticAt_conductor_cpow_neg_div_two s).mul (h.analyticAt_entireCompletion s)).mul
      (d.analyticAt_invGammaFactor s)
  exact ((hanL.continuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE hanR.continuousAt).mp
    (polarPolynomial_mul_continuedL_eventuallyEq h.meromorphic s)).eq_of_nhds

end Meromorphic

section DirichletAgreement

variable {d : AnalyticLFunctionData}

/-- On `1 < s.re` where `d.gammaFactor s ≠ 0`, Dirichlet agreement alone identifies `d.continuedL s`
with `LSeries d.coeff s`. -/
theorem HasDirichletAgreement.continuedL_eq_LSeries_of_gammaFactor_ne_zero
    (hda : d.HasDirichletAgreement) {s : ℂ} (hs : 1 < s.re) (hγ : d.gammaFactor s ≠ 0) :
    d.continuedL s = LSeries d.coeff s := by
  rw [d.continuedL_eq_of_gammaFactor_ne_zero hγ, hda.completed_eq s hs]
  calc
    ((d.conductor : ℕ) : ℂ) ^ (-s / 2) *
        (((d.conductor : ℕ) : ℂ) ^ (s / 2) * d.gammaFactor s * LSeries d.coeff s) *
        (d.gammaFactor s)⁻¹ =
      (((d.conductor : ℕ) : ℂ) ^ (-s / 2) * ((d.conductor : ℕ) : ℂ) ^ (s / 2)) *
        (d.gammaFactor s * (d.gammaFactor s)⁻¹) * LSeries d.coeff s := by ring
    _ = LSeries d.coeff s := by
      rw [d.conductor_cpow_neg_mul_div_two s, mul_inv_cancel₀ hγ, one_mul, one_mul]

/-- At every point `s` with `1 < s.re`, `d.continuedL` agrees with `LSeries d.coeff` on a punctured
neighbourhood of `s`. -/
theorem HasDirichletAgreement.continuedL_eventuallyEq_LSeries
    (hda : d.HasDirichletAgreement) {s : ℂ} (hs : 1 < s.re) :
    d.continuedL =ᶠ[𝓝[≠] s] LSeries d.coeff := by
  have hopen : {z : ℂ | 1 < z.re} ∈ 𝓝[≠] s :=
    nhdsWithin_le_nhds ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs)
  filter_upwards [hopen, d.gammaFactor_eventually_ne_zero s] with z hz hγz
  exact hda.continuedL_eq_LSeries_of_gammaFactor_ne_zero hz hγz

private theorem abscissaOfAbsConv_le_one_or_eq_top
    (hda : d.HasDirichletAgreement) (hmc : d.HasMeromorphicContinuation) :
    LSeries.abscissaOfAbsConv d.coeff ≤ 1 ∨ LSeries.abscissaOfAbsConv d.coeff = ⊤ := by
  rcases le_or_gt (LSeries.abscissaOfAbsConv d.coeff) 1 with habs | habs
  · exact Or.inl habs
  · cases ha : LSeries.abscissaOfAbsConv d.coeff with
    | bot => simp [ha] at habs
    | top => exact Or.inr rfl
    | coe r =>
      exfalso
      rw [ha] at habs
      have hr : 1 < r := by exact_mod_cast habs
      set s₀ : ℂ := (((1 + r) / 2 : ℝ) : ℂ)
      have hs₀_gt : 1 < s₀.re := by simp [s₀]; linarith
      have hs₀_lt : {z : ℂ | z.re < r} ∈ 𝓝[≠] s₀ :=
        nhdsWithin_le_nhds ((isOpen_lt Complex.continuous_re continuous_const).mem_nhds
          (by simp [s₀]; linarith))
      have hzero_s₀ : d.continuedL =ᶠ[𝓝[≠] s₀] 0 := by
        filter_upwards [hda.continuedL_eventuallyEq_LSeries hs₀_gt, hs₀_lt] with z hz hzr
        rw [hz]
        refine LSeries.eq_zero_of_not_LSeriesSummable d.coeff z fun hsum ↦ ?_
        have hle := hsum.abscissaOfAbsConv_le
        rw [ha, EReal.coe_le_coe_iff] at hle
        linarith
      have htop_all : ∀ w : ℂ, meromorphicOrderAt d.continuedL w = ⊤ := fun w ↦
        hmc.meromorphic_continuedL.meromorphicOn.meromorphicOrderAt_eq_top_of_isPreconnected
          isPreconnected_univ (mem_univ s₀) (mem_univ w)
          (meromorphicOrderAt_eq_top_iff.mpr hzero_s₀)
      have hev_real : (fun x : ℝ ↦ LSeries d.coeff x) =ᶠ[atTop] 0 := by
        filter_upwards [eventually_gt_atTop r] with x hx
        have hx1 : 1 < ((x : ℂ)).re := by simp; linarith
        have hcont : ContinuousAt (LSeries d.coeff) (x : ℂ) :=
          (LSeries_analyticOnNhd d.coeff (x : ℂ)
            (by rw [ha]; exact_mod_cast hx)).continuousAt
        have hz0 : d.continuedL =ᶠ[𝓝[≠] (x : ℂ)] 0 :=
          meromorphicOrderAt_eq_top_iff.mp (htop_all x)
        have hlim0 : Tendsto (LSeries d.coeff) (𝓝[≠] (x : ℂ)) (𝓝 0) :=
          tendsto_const_nhds.congr' (hz0.symm.trans (hda.continuedL_eventuallyEq_LSeries hx1))
        exact tendsto_nhds_unique hcont.continuousWithinAt.tendsto hlim0
      rcases LSeries_eventually_eq_zero_iff'.mp hev_real with hcoeff | htop
      · exact one_ne_zero (hda.coeff_one.symm.trans (hcoeff 1 one_ne_zero))
      · rw [ha] at htop
        exact (EReal.coe_ne_top r) htop

private theorem continuousAt_LSeries_of_hasDirichletAgreement
    (hda : d.HasDirichletAgreement) (hmc : d.HasMeromorphicContinuation) {s : ℂ}
    (hs : 1 < s.re) : ContinuousAt (LSeries d.coeff) s := by
  rcases abscissaOfAbsConv_le_one_or_eq_top hda hmc with habs | ha
  · exact (LSeries_analyticOnNhd d.coeff s
      (habs.trans_lt (by exact_mod_cast hs))).continuousAt
  · rw [LSeries_eq_zero_of_abscissaOfAbsConv_eq_top ha]
    exact continuousAt_const

/-- On `1 < s.re`, a card with Dirichlet agreement and meromorphic continuation has analytic
`continuedL` at `s`, even if `d.gammaFactor` has a pole at `s`. -/
theorem HasDirichletAgreement.analyticAt_continuedL (hda : d.HasDirichletAgreement)
    (hmc : d.HasMeromorphicContinuation) {s : ℂ} (hs : 1 < s.re) :
    AnalyticAt ℂ d.continuedL s := by
  have hcont := continuousAt_LSeries_of_hasDirichletAgreement hda hmc hs
  have hlim : Tendsto d.continuedL (𝓝[≠] s) (𝓝 (LSeries d.coeff s)) :=
    hcont.continuousWithinAt.tendsto.congr' (hda.continuedL_eventuallyEq_LSeries hs).symm
  exact (hmc.meromorphicOrderAt_continuedL_nonneg_iff_analyticAt s).1 <|
    (tendsto_nhds_iff_meromorphicOrderAt_nonneg (hmc.meromorphic_continuedL s)).1
      ⟨LSeries d.coeff s, hlim⟩

/-- **Agreement with `LSeries` on `1 < s.re`.** Under Dirichlet agreement and meromorphic
continuation, `d.continuedL s = LSeries d.coeff s` at every point of the half-plane `1 < s.re`,
including any poles of `d.gammaFactor` in that half-plane. -/
theorem HasDirichletAgreement.continuedL_eq_LSeries (hda : d.HasDirichletAgreement)
    (hmc : d.HasMeromorphicContinuation) {s : ℂ} (hs : 1 < s.re) :
    d.continuedL s = LSeries d.coeff s :=
  hmc.continuedL_eq_of_tendsto <|
    (continuousAt_LSeries_of_hasDirichletAgreement hda hmc hs).continuousWithinAt.tendsto.congr'
      (hda.continuedL_eventuallyEq_LSeries hs).symm

/-- Canonical normal-form continuation of `LSeries d.coeff` from `1 < s.re` equals
`toMeromorphicNFOn d.continuedL univ`. -/
theorem HasDirichletAgreement.meromorphicContinuation_LSeries_eq_toMeromorphicNFOn_continuedL
    (hda : d.HasDirichletAgreement) (hmc : d.HasMeromorphicContinuation) :
    meromorphicContinuation 1 (LSeries d.coeff) = toMeromorphicNFOn d.continuedL univ :=
  meromorphicContinuation_eq_toMeromorphicNFOn hmc.meromorphic_continuedL
    (fun _ hs ↦ hda.analyticAt_continuedL hmc hs) (fun _ hs ↦ hda.continuedL_eq_LSeries hmc hs)

end DirichletAgreement

section FunctionalEquation

variable {d : AnalyticLFunctionData}

/-- **Pointwise asymmetric functional equation.** If `d` satisfies `HasFunctionalEquation`,
`d.polarOrder s = 0` (which automatically forces `d.polarOrder (1 - conj s) = 0`),
`d.gammaFactor s ≠ 0`, and `d.dual.gammaFactor (1 - s) ≠ 0`, then
`d.gammaFactor s * d.continuedL s = ε * N^(1 / 2 - s) * d.dual.gammaFactor (1 - s) *
d.dual.continuedL (1 - s)`. -/
theorem HasFunctionalEquation.gammaFactor_mul_continuedL_eq
    (h : d.HasFunctionalEquation) {s : ℂ} (hp : d.polarOrder s = 0)
    (hγ : d.gammaFactor s ≠ 0) (hγ' : d.dual.gammaFactor (1 - s) ≠ 0) :
    d.gammaFactor s * d.continuedL s =
      d.rootNumber * ((d.conductor : ℕ) : ℂ) ^ (1 / 2 - s) *
        d.dual.gammaFactor (1 - s) * d.dual.continuedL (1 - s) := by
  have hp' : d.polarOrder (1 - conj s) = 0 := (h.polarOrder_one_sub_conj s).trans hp
  have hfe := h.completed_eq s hp hp'
  have hc := d.completed_eq_mul_continuedL hγ
  have hc' := d.dual.completed_eq_mul_continuedL hγ'
  rw [dual_conductor] at hc'
  have hpow' : ((d.conductor : ℕ) : ℂ) ^ (-s / 2) * ((d.conductor : ℕ) : ℂ) ^ ((1 - s) / 2) =
      ((d.conductor : ℕ) : ℂ) ^ (1 / 2 - s) := by
    rw [← cpow_add _ _ d.conductor_cast_ne_zero]
    congr 1
    ring
  calc
    d.gammaFactor s * d.continuedL s =
        ((d.conductor : ℕ) : ℂ) ^ (-s / 2) *
          (((d.conductor : ℕ) : ℂ) ^ (s / 2) * d.gammaFactor s * d.continuedL s) := by
      rw [← mul_assoc, ← mul_assoc, d.conductor_cpow_neg_mul_div_two s, one_mul]
    _ = ((d.conductor : ℕ) : ℂ) ^ (-s / 2) * d.completed s := by rw [← hc]
    _ = ((d.conductor : ℕ) : ℂ) ^ (-s / 2) *
          (d.rootNumber *
            (((d.conductor : ℕ) : ℂ) ^ ((1 - s) / 2) *
              d.dual.gammaFactor (1 - s) * d.dual.continuedL (1 - s))) := by rw [hfe, hc']
    _ = d.rootNumber *
          (((d.conductor : ℕ) : ℂ) ^ (-s / 2) * ((d.conductor : ℕ) : ℂ) ^ ((1 - s) / 2)) *
          d.dual.gammaFactor (1 - s) * d.dual.continuedL (1 - s) := by ring
    _ = d.rootNumber * ((d.conductor : ℕ) : ℂ) ^ (1 / 2 - s) *
          d.dual.gammaFactor (1 - s) * d.dual.continuedL (1 - s) := by rw [hpow']

/-- **Asymmetric functional equation as germs.** For any card `d` satisfying
`HasFunctionalEquation` (even without meromorphicity), `γ(z) * continuedL d z` agrees on a punctured
neighbourhood of every `s : ℂ` with `ε * N^(1 / 2 - z) * γ_dual(1 - z) * continuedL d.dual (1 - z)`.
-/
theorem HasFunctionalEquation.gammaFactor_mul_continuedL_eventuallyEq
    (h : d.HasFunctionalEquation) (s : ℂ) :
    (fun z ↦ d.gammaFactor z * d.continuedL z) =ᶠ[𝓝[≠] s]
      fun z ↦ d.rootNumber * ((d.conductor : ℕ) : ℂ) ^ (1 / 2 - z) *
        d.dual.gammaFactor (1 - z) * d.dual.continuedL (1 - z) := by
  have ht : Tendsto (fun z : ℂ ↦ 1 - z) (𝓝[≠] s) (𝓝[≠] (1 - s)) :=
    (continuous_const.sub continuous_id).continuousWithinAt.tendsto_nhdsWithin fun _ hz ↦
      sub_right_injective.ne hz
  filter_upwards [d.polarOrder_eventually_eq_zero s, d.gammaFactor_eventually_ne_zero s,
    ht.eventually (d.dual.gammaFactor_eventually_ne_zero (1 - s))] with z hp hγ hγ'
  exact h.gammaFactor_mul_continuedL_eq hp hγ hγ'

end FunctionalEquation

/-! ### Checks -/

/-- The polar-exclusion hypothesis `d.polarOrder s = 0` in
`HasFunctionalEquation.gammaFactor_mul_continuedL_eq` cannot be omitted, even when both gamma
factors are nonzero: a degree-zero card with `polarOrder` supported at `0` and `1` and completed
values `1` at `1` and `0` elsewhere satisfies `HasFunctionalEquation`, yet the pointwise equation
fails at `s = 1`. -/
example : ∃ d : AnalyticLFunctionData, d.HasFunctionalEquation ∧
    d.gammaFactor 1 ≠ 0 ∧ d.dual.gammaFactor (1 - 1) ≠ 0 ∧
    d.gammaFactor 1 * d.continuedL 1 ≠
      d.rootNumber * ((d.conductor : ℕ) : ℂ) ^ ((1 : ℂ) / 2 - 1) *
        d.dual.gammaFactor (1 - 1) * d.dual.continuedL (1 - 1) := by
  let d : AnalyticLFunctionData :=
    { coeff := 0
      conductor := 1
      gammaR := 0
      gammaC := 0
      rootNumber := 1
      completed := Function.update 0 1 1
      polarOrder := Finsupp.single 0 1 + Finsupp.single 1 1 }
  have hrefl0 (s : ℂ) : (0 : ℂ) = 1 - conj s ↔ s = 1 :=
    ⟨fun h ↦ (starRingEnd ℂ).injective (by rw [map_one]; linear_combination h),
      by rintro rfl; simp⟩
  have hrefl1 (s : ℂ) : (1 : ℂ) = 1 - conj s ↔ s = 0 :=
    ⟨fun h ↦ (starRingEnd ℂ).injective (by rw [map_zero]; linear_combination h),
      by rintro rfl; simp⟩
  have hfe : d.HasFunctionalEquation := by
    refine ⟨by simp [d], fun s ↦ ?_, fun s hs _ ↦ ?_⟩
    · simp only [d, Finsupp.add_apply, Finsupp.single_apply, hrefl0, hrefl1,
        eq_comm (a := (0 : ℂ)), eq_comm (a := (1 : ℂ))]
      exact Nat.add_comm _ _
    · have hs1 : s ≠ 1 := fun h ↦ by subst s; simp [d] at hs
      have hs0 : 1 - conj s ≠ 1 := fun h ↦ by
        have h0 : s = 0 := (hrefl1 s).mp h.symm
        subst s
        simp [d] at hs
      simp [d, dual_completed_apply, Function.update_of_ne hs1, Function.update_of_ne hs0]
  have hγ1 : d.gammaFactor 1 ≠ 0 := by simp [d, gammaFactor_def]
  have hγ0 : d.dual.gammaFactor (1 - 1) ≠ 0 := by simp [d, gammaFactor_def]
  refine ⟨d, hfe, hγ1, hγ0, ?_⟩
  rw [d.continuedL_eq_of_gammaFactor_ne_zero hγ1, d.dual.continuedL_eq_of_gammaFactor_ne_zero hγ0]
  simp [d, gammaFactor_def, dual_completed_apply]

end TauCeti.LFunctions.AnalyticLFunctionData
