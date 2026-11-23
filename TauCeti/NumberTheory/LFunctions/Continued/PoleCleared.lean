/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LFunctions.Continued.Basic
public import TauCeti.NumberTheory.LFunctions.Zeros.Completion.FiniteOrder
import TauCeti.Analysis.Polynomial.Order
import TauCeti.NumberTheory.LFunctions.GammaFactor.Growth

/-!
# Pole-cleared continued functions and their order of growth

For a polynomial `P`, `poleClearedContinuedL d P` is the removable extension of
`s ↦ P(s) · continuedL d s` across the singularities of this product that `P` removes. At a
pole of the continued function that `P` does not clear, the original representative is kept,
as in `AnalyticLFunctionData.continuedL`. The raw product is not a substitute: at the pole of
zeta at `1`, `(1 - 1) · riemannZeta 1 = 0`, while the pole-cleared value is the residue `1`.

The main result is `HasMeromorphicContinuation.orderLE_poleClearedContinuedL`: if `P ≠ 0` clears
every pole of the continued function and the entire completion has order at most `A ≥ 1`, then
the pole-cleared function is entire of order at most `A`. The proof multiplies the entire
completion by the reciprocal gamma factor, which has order at most one, and by the conductor
power `N^(-s/2)`, an exponential of order one. The resulting entire function is
`polarPolynomial · poleClearedContinuedL d P` divided by `P`, and dividing by a nonzero
polynomial does not increase the order. When the record has no poles, the continued function is
itself entire of the same order (`HasMeromorphicContinuation.orderLE_continuedL`).

This is the finite-order input of ZerosOfLFunctions §3.4 for Phragmén–Lindelöf on vertical
strips. It holds on the whole plane, which is stronger than the strip statement used there.

## References

* H. Davenport, *Multiplicative Number Theory*, 3rd ed. (2000), §12.
* H. Iwaniec and E. Kowalski, *Analytic Number Theory* (2004), §5.1.
-/

public section

open Complex Filter Asymptotics Bornology Topology Polynomial

namespace TauCeti.LFunctions.AnalyticLFunctionData

variable (d : AnalyticLFunctionData) (P : ℂ[X])

/-- The pole-cleared continued function: the removable extension of
`s ↦ P(s) · continuedL d s` at every point of nonnegative order. At a remaining pole the
original representative of the product is kept. -/
noncomputable def poleClearedContinuedL : ℂ → ℂ :=
  toMeromorphicNFOn (fun s ↦ P.eval s * d.continuedL s)
    {s | 0 ≤ meromorphicOrderAt (fun z ↦ P.eval z * d.continuedL z) s}

theorem poleClearedContinuedL_def :
    d.poleClearedContinuedL P = toMeromorphicNFOn (fun s ↦ P.eval s * d.continuedL s)
      {s | 0 ≤ meromorphicOrderAt (fun z ↦ P.eval z * d.continuedL z) s} :=
  (rfl)

private theorem meromorphic_eval_mul_continuedL :
    Meromorphic fun s ↦ P.eval s * d.continuedL s :=
  fun s ↦ ((AnalyticOnNhd.eval_polynomial P) s trivial).meromorphicAt.mul
    (d.meromorphic_continuedL s)

variable {d P}

/-- Where the product `P · continuedL d` is analytic, no repair is made. -/
theorem poleClearedContinuedL_eq_of_analyticAt {s : ℂ}
    (ha : AnalyticAt ℂ (fun z ↦ P.eval z * d.continuedL z) s) :
    d.poleClearedContinuedL P s = P.eval s * d.continuedL s := by
  rw [poleClearedContinuedL_def, toMeromorphicNFOn_eq_toMeromorphicNFAt
    (meromorphic_eval_mul_continuedL d P).meromorphicOn ha.meromorphicOrderAt_nonneg,
    toMeromorphicNFAt_eq_self.mpr ha.meromorphicNFAt]

/-- The pole-cleared function has the punctured germs of `P · continuedL d`. -/
theorem poleClearedContinuedL_eventuallyEq (s : ℂ) :
    d.poleClearedContinuedL P =ᶠ[𝓝[≠] s] fun z ↦ P.eval z * d.continuedL z := by
  filter_upwards [(meromorphic_eval_mul_continuedL d P s).eventually_analyticAt] with z hz
  exact poleClearedContinuedL_eq_of_analyticAt hz

/-- Off the roots of `P`, the pole-cleared function is the product `P · continuedL d`, at poles
of the continued function too. -/
theorem poleClearedContinuedL_eq_of_eval_ne_zero {s : ℂ} (hP : P.eval s ≠ 0) :
    d.poleClearedContinuedL P s = P.eval s * d.continuedL s := by
  have hPa : AnalyticAt ℂ (fun z ↦ P.eval z) s := (AnalyticOnNhd.eval_polynomial P) s trivial
  by_cases hs : 0 ≤ meromorphicOrderAt d.continuedL s
  · exact poleClearedContinuedL_eq_of_analyticAt (hPa.mul (d.analyticAt_continuedL hs))
  · apply toMeromorphicNFOn_eq_self_on_compl (meromorphic_eval_mul_continuedL d P).meromorphicOn
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq]
    rwa [fun_meromorphicOrderAt_mul hPa.meromorphicAt (d.meromorphic_continuedL s),
      hPa.meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mpr hP, zero_add]

/-- Clearing by `P ≠ 0` adds the root multiplicity of `P` to the meromorphic order. -/
theorem meromorphicOrderAt_poleClearedContinuedL (hP : P ≠ 0) (s : ℂ) :
    meromorphicOrderAt (d.poleClearedContinuedL P) s =
      meromorphicOrderAt d.continuedL s + (P.rootMultiplicity s : ℕ) := by
  have hPa : AnalyticAt ℂ (fun z ↦ P.eval z) s := (AnalyticOnNhd.eval_polynomial P) s trivial
  rw [meromorphicOrderAt_congr (poleClearedContinuedL_eventuallyEq s),
    fun_meromorphicOrderAt_mul hPa.meromorphicAt (d.meromorphic_continuedL s),
    hPa.meromorphicOrderAt_eq, Polynomial.analyticOrderAt_eval hP, add_comm]
  rfl

/-- The pole-cleared function is analytic at every point of nonnegative order. -/
theorem analyticAt_poleClearedContinuedL {s : ℂ}
    (hs : 0 ≤ meromorphicOrderAt (d.poleClearedContinuedL P) s) :
    AnalyticAt ℂ (d.poleClearedContinuedL P) s := by
  have hr := hs
  rw [meromorphicOrderAt_congr (poleClearedContinuedL_eventuallyEq s)] at hr
  have hnf := meromorphicNFOn_toMeromorphicNFOn (fun z ↦ P.eval z * d.continuedL z)
    {z | 0 ≤ meromorphicOrderAt (fun z ↦ P.eval z * d.continuedL z) z} hr
  rw [← poleClearedContinuedL_def] at hnf
  exact hnf.meromorphicOrderAt_nonneg_iff_analyticAt.mp hs

/-- If `P ≠ 0` clears every pole of the continued function, the pole-cleared function is
entire. -/
theorem differentiable_poleClearedContinuedL (hP : P ≠ 0)
    (hclear : ∀ s, 0 ≤ meromorphicOrderAt d.continuedL s + (P.rootMultiplicity s : ℕ)) :
    Differentiable ℂ (d.poleClearedContinuedL P) := fun s ↦
  (analyticAt_poleClearedContinuedL
    ((meromorphicOrderAt_poleClearedContinuedL hP s).symm ▸ hclear s)).differentiableAt

private theorem orderLE_conductor_cpow :
    OrderLE (fun s : ℂ ↦ ((d.conductor : ℕ) : ℂ) ^ (-s / 2)) 1 := by
  have hN : ((d.conductor : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr d.conductor.ne_zero
  convert orderLE_cexp_mul (-Complex.log ((d.conductor : ℕ) : ℂ) / 2) using 2 with s
  rw [cpow_def_of_ne_zero hN]
  ring_nf

private theorem analyticAt_clearedProduct (h : d.HasMeromorphicContinuation) (s : ℂ) :
    AnalyticAt ℂ (fun z ↦ ((d.conductor : ℕ) : ℂ) ^ (-z / 2) * d.entireCompletion z *
      d.invGammaFactor z) s :=
  ((d.analyticAt_conductor_cpow (g := fun z ↦ -z / 2) (by fun_prop)).mul
    (h.analyticAt_entireCompletion s)).mul (d.analyticAt_invGammaFactor s)

/-- With a meromorphic continuation, the polar polynomial times the continued function is the
entire function `N^(-s/2) · entireCompletion · invGammaFactor`, as punctured germs. -/
private theorem polarPolynomial_mul_continuedL_eventuallyEq (h : d.HasMeromorphicContinuation)
    (s : ℂ) :
    (fun z ↦ d.polarPolynomial.eval z * d.continuedL z) =ᶠ[𝓝[≠] s]
      fun z ↦ ((d.conductor : ℕ) : ℂ) ^ (-z / 2) * d.entireCompletion z *
        d.invGammaFactor z := by
  filter_upwards [continuedL_eventuallyEq h.meromorphic s, h.entireCompletion_eventuallyEq s]
    with z hz hent
  rw [hz, hent, uncompletedProduct_def]
  ring

/-- **Order of the pole-cleared continued function.** If `P ≠ 0` clears every pole of the
continued function and the entire completion has order at most `A ≥ 1`, then the pole-cleared
function is entire of order at most `A`. -/
theorem HasMeromorphicContinuation.orderLE_poleClearedContinuedL
    (h : d.HasMeromorphicContinuation) (hP : P ≠ 0)
    (hclear : ∀ s, 0 ≤ meromorphicOrderAt d.continuedL s + (P.rootMultiplicity s : ℕ))
    {A : ℝ} (hA : OrderLE d.entireCompletion A) (h1 : 1 ≤ A) :
    OrderLE (d.poleClearedContinuedL P) A := by
  have hF := differentiable_poleClearedContinuedL hP hclear
  have hG : OrderLE (fun z ↦ ((d.conductor : ℕ) : ℂ) ^ (-z / 2) * d.entireCompletion z *
      d.invGammaFactor z) A :=
    ((orderLE_conductor_cpow.mono h1).mul hA).mul (d.orderLE_invGammaFactor.mono h1)
  -- The polar polynomial times the cleared function is `P` times an entire function of order `A`.
  have heq : (fun z ↦ d.polarPolynomial.eval z * d.poleClearedContinuedL P z) =
      fun z ↦ P.eval z * (((d.conductor : ℕ) : ℂ) ^ (-z / 2) * d.entireCompletion z *
        d.invGammaFactor z) := by
    funext s
    have hl : AnalyticAt ℂ (fun z ↦ d.polarPolynomial.eval z * d.poleClearedContinuedL P z) s :=
      ((AnalyticOnNhd.eval_polynomial _) s trivial).mul (hF.analyticAt s)
    have hr : AnalyticAt ℂ (fun z ↦ P.eval z * (((d.conductor : ℕ) : ℂ) ^ (-z / 2) *
        d.entireCompletion z * d.invGammaFactor z)) s :=
      ((AnalyticOnNhd.eval_polynomial _) s trivial).mul (analyticAt_clearedProduct h s)
    refine ((hl.continuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE hr.continuousAt).mp ?_)
      |>.eq_of_nhds
    filter_upwards [poleClearedContinuedL_eventuallyEq s,
      polarPolynomial_mul_continuedL_eventuallyEq h s] with z hz hpz
    rw [hz, ← hpz]
    ring
  have hprod : OrderLE (fun z ↦ d.polarPolynomial.eval z * d.poleClearedContinuedL P z) A := by
    rw [heq]
    exact (P.orderLE_eval.mono (by linarith)).mul hG
  refine IsBigO.orderLE ?_ hprod
  have hpoly := Polynomial.isBigO_cobounded_of_degree_le (P := (1 : ℂ[X]))
    (Q := d.polarPolynomial) (by
      simpa using Polynomial.zero_le_degree_iff.mpr d.monic_polarPolynomial.ne_zero)
  simpa using hpoly.mul (isBigO_refl (d.poleClearedContinuedL P) (cobounded ℂ))

/-- **Finite order of the pole-cleared continued function.** For a record of finite order, a
nonzero polynomial clearing every pole of the continued function gives an entire function of
finite order. -/
theorem HasMeromorphicContinuation.isFiniteOrder_poleClearedContinuedL
    (h : d.HasMeromorphicContinuation) (hP : P ≠ 0)
    (hclear : ∀ s, 0 ≤ meromorphicOrderAt d.continuedL s + (P.rootMultiplicity s : ℕ))
    (hfin : d.IsFiniteOrder) :
    TauCeti.IsFiniteOrder (d.poleClearedContinuedL P) := by
  obtain ⟨A, -, hA⟩ := TauCeti.IsFiniteOrder.exists_nonneg hfin
  exact (h.orderLE_poleClearedContinuedL hP hclear (hA.mono (le_max_left A 1))
    (le_max_right A 1)).isFiniteOrder

/-- Clearing by the constant polynomial `1` changes nothing where the continued function is
analytic. -/
theorem poleClearedContinuedL_one_of_analyticAt {s : ℂ} (ha : AnalyticAt ℂ d.continuedL s) :
    d.poleClearedContinuedL 1 s = d.continuedL s := by
  rw [poleClearedContinuedL_eq_of_analyticAt (by simpa using ha), eval_one, one_mul]

/-- **Order of the continued function of a record without poles.** If the record has no poles
and its entire completion has order at most `A ≥ 1`, then the continued function is entire of
order at most `A`. -/
theorem HasMeromorphicContinuation.orderLE_continuedL (h : d.HasMeromorphicContinuation)
    (h0 : d.polarOrder = 0) {A : ℝ} (hA : OrderLE d.entireCompletion A) (h1 : 1 ≤ A) :
    OrderLE d.continuedL A := by
  have ha (s : ℂ) : AnalyticAt ℂ d.continuedL s :=
    h.analyticAt_continuedL_of_polarOrder_eq_zero (by simp [h0])
  have hcl := h.orderLE_poleClearedContinuedL one_ne_zero
    (fun s ↦ by
      rw [rootMultiplicity_eq_zero (by simp), Nat.cast_zero, add_zero]
      exact (ha s).meromorphicOrderAt_nonneg) hA h1
  have heq : d.poleClearedContinuedL 1 = d.continuedL :=
    funext fun s ↦ poleClearedContinuedL_one_of_analyticAt (ha s)
  rwa [heq] at hcl

end TauCeti.LFunctions.AnalyticLFunctionData
