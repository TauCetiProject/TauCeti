/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.CauchyRiemann.RoughCoefficients.Interior
public import TauCeti.Analysis.Sobolev.Local.Multiplication.Higher
import TauCeti.Analysis.Complex.CauchyRiemann.RoughCoefficients.PartialDerivative
import TauCeti.Analysis.Complex.OperatorNorm
import TauCeti.Analysis.Distribution.TestFunction.Inner

/-!
# Interior regularity of every order for real Cauchy–Riemann equations with Sobolev coefficients

Let `Ω ⊆ ℂ` be open, write `z = s + i t`, and let `V` be a finite-dimensional real inner product
space. For coefficients `J ∈ W^{1,p}_loc(Ω; End V)` with `J² = -1` and `S ∈ Lᵖ_loc(Ω; End V)`,
`p > 2`, consider a weak solution `ξ ∈ L^q_loc` of

`∂_s ξ + J ∂_t ξ + S ξ = η`

in the sense of `TauCeti.IsWeakCRSolution`, with `1/p + 1/q < 1` and `q ≤ p`. This file proves
that `ξ` gains one derivative over `η` at every order: if `J, S ∈ W^{k,p}_loc` and
`η ∈ W^{k,q}_loc`, then `ξ ∈ W^{k+1,q}_loc` (`TauCeti.IsWeakCRSolution.memWkpLoc_succ`). This is
the weak regularity statement of McDuff–Salamon, Proposition B.4.9, with a zeroth-order term: for
`J ∈ W^{ℓ,p}_loc` and `S ∈ W^{m,p}_loc` with `m ≤ ℓ` it applies at every order `k ≤ m`. The case
`k = 0` is `TauCeti.IsWeakCRSolution.memWkpLoc_one_of_le`.

The induction runs through the `t`-derivative alone. For `ξ ∈ W^{1,q}_loc` the `t`-derivative of
the equation is again a real Cauchy–Riemann equation,

`∂_s (∂_t ξ) + J ∂_t (∂_t ξ) + (S + ∂_t J) ∂_t ξ = ∂_t η - (∂_t S) ξ`,

which holds weakly (`TauCeti.IsWeakCRSolution.apply_I_of_hasWeakFDerivOn`) with only one weak
derivative of `ξ`, `J` and `S`. It is the case `e = i` of the differentiated equation
`TauCeti.IsSobolevCRCoefficients.isWeakCRSolution_partial`, with the term `(∂_t J) ∂_t ξ` moved
into the zeroth-order coefficient. It is the second row of McDuff–Salamon's differentiated system
`TauCeti.ae_differentiated_cauchyRiemann`; unlike the first row, it does not involve `∂_s ∂_t J`.
The coefficient `S + ∂_t J` is in `W^{k-1,p}_loc` when `J, S ∈ W^{k,p}_loc`, so the induction
hypothesis gives `∂_t ξ ∈ W^{k,q}_loc`. The `s`-derivative is then read off the equation,
`∂_s ξ = η - J ∂_t ξ - S ξ`, whose right side is in `W^{k,q}_loc` by the mixed-exponent products
`TauCeti.MemWkpLoc.clm_apply_succ`.

## Main results

* `TauCeti.IsWeakCRSolution.apply_I_of_hasWeakFDerivOn`: the weak equation for `∂_t ξ`.
* `TauCeti.IsWeakCRSolution.memWkpLoc_succ`: interior `W^{k+1,q}` regularity.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B.4, Proposition B.4.9.
-/

public section

open MeasureTheory TopologicalSpace Complex ContinuousLinearMap
open scoped InnerProductSpace ENNReal NNReal Distributions LineDeriv

namespace TauCeti

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  {Ω : Opens ℂ} {J S : ℂ → V →L[ℝ] V} {DJ : ℂ → ℂ →L[ℝ] V →L[ℝ] V} {ξ η : ℂ → V}

namespace IsWeakCRSolution

/-- **The equation for `∂_t ξ`.** Let `ξ` be a weak solution of `∂_s ξ + J ∂_t ξ + S ξ = η` on
`Ω` with Sobolev coefficients, `1/p + 1/q ≤ 1` and `p, q` finite. Suppose that `ξ` has a weak
derivative `Dξ ∈ L^q_loc`, that `S` has a weak derivative `DS ∈ Lᵖ_loc`, and that `η` has a weak
derivative `Dη`. Then `∂_t ξ = Dξ · I` is a weak solution of

`∂_s (∂_t ξ) + J ∂_t (∂_t ξ) + (S + ∂_t J) ∂_t ξ = ∂_t η - (∂_t S) ξ`. -/
theorem apply_I_of_hasWeakFDerivOn [FiniteDimensional ℝ V] {p q : ℝ≥0∞}
    (h : IsWeakCRSolution q Ω J DJ S ξ η) (hc : IsSobolevCRCoefficients p Ω J DJ S)
    (hpq : p⁻¹ + q⁻¹ ≤ 1) (hp : p ≠ ⊤) (hq : q ≠ ⊤) {DS : ℂ → ℂ →L[ℝ] V →L[ℝ] V}
    (hS : HasWeakFDerivOn volume Ω S DS) (hDS : MemLpLoc p Ω DS) {Dξ Dη : ℂ → ℂ →L[ℝ] V}
    (hξ : HasWeakFDerivOn volume Ω ξ Dξ) (hDξ : MemLpLoc q Ω Dξ)
    (hη : HasWeakFDerivOn volume Ω η Dη) :
    IsWeakCRSolution q Ω J DJ (fun z => S z + DJ z I) (fun z => Dξ z I)
      (fun z => Dη z I - DS z I (ξ z)) := by
  have hloc := Ω.isOpen.isLocallyClosed
  have hDξI : MemLpLoc q Ω (fun z => Dξ z I) := hDξ.clm_comp (apply ℝ V I)
  have heq := (hc.isWeakCRSolution_iff_ae hpq hp hq hξ h.memLpLoc hDξ h.locallyIntegrableOn).1 h
  -- The case `e = i` of the differentiated equation, with `(∂_t J) ∂_t ξ` on the right side.
  have hT := hc.isWeakCRSolution_partial hpq hp hq hξ h.memLpLoc hDξ heq
    (hS.hasWeakLineDerivOn I) (hDS.clm_comp (apply ℝ (V →L[ℝ] V) I)) (hη.hasWeakLineDerivOn I)
  refine isWeakCRSolution_iff.2 ⟨hDξI, (hη.hasWeakLineDerivOn I).locallyIntegrableOn_deriv.sub
    ((hDS.clm_comp (apply ℝ (V →L[ℝ] V) I)).locallyIntegrableOn_clm_apply h.memLpLoc hpq hloc),
    fun φ => ⟨(hc.add_zeroth (hc.memLpLoc_deriv_apply I)).integrable_inner_crFormalAdjoint hpq
      hDξI φ, ?_⟩⟩
  -- Move `(∂_t J) ∂_t ξ` from the right side into the zeroth-order coefficient.
  have hDJ := φ.integrable_inner
    ((hc.memLpLoc_deriv_apply I).locallyIntegrableOn_clm_apply hDξI hpq hloc)
  simp only [inner_crFormalAdjoint_add_zeroth]
  rw [integral_add (hT.integrable_inner_crFormalAdjoint φ) hDJ, hT.integral_inner_crFormalAdjoint φ,
    ← integral_add (φ.integrable_inner hT.locallyIntegrableOn) hDJ]
  refine integral_congr_ae (.of_forall fun z => ?_)
  simp only [inner_sub_right]
  ring

/-- **Interior `W^{k+1,q}` regularity** (McDuff–Salamon, Proposition B.4.9). Let `p > 2`, let
`J ∈ W^{1,p}_loc` with `J² = -1` and `S ∈ Lᵖ_loc`, and let `ξ ∈ L^q_loc` be a weak solution of
`∂_s ξ + J ∂_t ξ + S ξ = η` with `1/p + 1/q < 1` and `q ≤ p`. If moreover `J, S ∈ W^{k,p}_loc` and
`η ∈ W^{k,q}_loc`, then `ξ ∈ W^{k+1,q}_loc`.

For `k = 0` this is `TauCeti.IsWeakCRSolution.memWkpLoc_one_of_le` with `r = q`. -/
theorem memWkpLoc_succ [FiniteDimensional ℝ V] {p q : ℝ≥0} {k : ℕ}
    (h : IsWeakCRSolution q Ω J DJ S ξ η) (hc : IsSobolevCRCoefficients p Ω J DJ S)
    (hp : 2 < p) (hJ2 : ∀ᵐ z ∂volume.restrict Ω, J z * J z = -1)
    (hpq : (p : ℝ≥0∞)⁻¹ + (q : ℝ≥0∞)⁻¹ < 1) (hqp : q ≤ p) (hJ : MemWkpLoc p Ω k J)
    (hS : MemWkpLoc p Ω k S) (hη : MemWkpLoc q Ω k η) : MemWkpLoc q Ω (k + 1) ξ := by
  have hq : 1 < q := by
    have : (1 : ℝ≥0∞) < q := ENNReal.inv_lt_one.1 (lt_of_le_of_lt le_add_self hpq)
    exact_mod_cast this
  induction k generalizing J DJ S ξ η with
  | zero =>
    exact h.memWkpLoc_one_of_le hc (by exact_mod_cast hp) hJ2 hpq (by exact_mod_cast hq)
      ENNReal.coe_ne_top (by exact_mod_cast hqp) (memWkpLoc_zero_iff.1 hη)
  | succ k ih =>
    -- `ξ ∈ W^{k+1,q}_loc` by the induction hypothesis.
    have hξ := ih h hc hJ2 hJ.of_succ hS.of_succ hη.of_succ
    obtain ⟨Dξ, hDξ, hDξk⟩ := hξ.exists_weakFDeriv_of_isOpen
    obtain ⟨DS, hDS, hDSk⟩ := hS.exists_weakFDeriv_of_isOpen
    obtain ⟨Dη, hDη, hDηk⟩ := hη.exists_weakFDeriv_of_isOpen
    have hDJk : MemWkpLoc p Ω k DJ := hJ.memWkpLoc_of_hasWeakFDerivOn hc.hasWeakFDerivOn
    -- `∂_t ξ` solves an equation of the same kind with data one order lower, so
    -- `∂_t ξ ∈ W^{k+1,q}_loc` by the induction hypothesis.
    have hT := h.apply_I_of_hasWeakFDerivOn hc hpq.le ENNReal.coe_ne_top ENNReal.coe_ne_top hDS
      hDSk.memLpLoc hDξ hDξk.memLpLoc hDη
    have hDSξ : MemWkpLoc q Ω k (fun z => DS z I (ξ z)) :=
      (hDSk.clm_comp (apply ℝ (V →L[ℝ] V) I)).bilin_of_memWkpLoc_succ
        (ContinuousLinearMap.id ℝ (V →L[ℝ] V)) hp hq hqp hξ
    have hTk : MemWkpLoc q Ω (k + 1) (fun z => Dξ z I) :=
      ih hT (hc.add_zeroth (hc.memLpLoc_deriv_apply I)) hJ2 hJ.of_succ
        (hS.of_succ.add (hDJk.clm_comp (apply ℝ (V →L[ℝ] V) I)))
        ((hDηk.clm_comp (apply ℝ V I)).sub hDSξ)
    -- `∂_s ξ = η - J ∂_t ξ - S ξ` almost everywhere, which is in `W^{k+1,q}_loc`.
    have heq := (hc.isWeakCRSolution_iff_ae hpq.le ENNReal.coe_ne_top ENNReal.coe_ne_top hDξ
      hξ.memLpLoc hDξk.memLpLoc h.locallyIntegrableOn).1 h
    have h1 : MemWkpLoc q Ω (k + 1) (fun z => Dξ z 1) :=
      ((hη.sub (hJ.clm_apply_succ hp hq hqp hTk)).sub (hS.clm_apply_succ hp hq hqp hξ)).congr_ae
        (heq.mono fun z hz => by simp only [Pi.sub_apply, ← hz]; abel)
    refine memWkpLoc_succ_iff_of_isOpen.2 ⟨hξ.memLpLoc, Dξ, hDξ, ?_⟩
    rw [fun_eq_smulRightL_reCLM_add_smulRightL_imCLM Dξ]
    exact (h1.clm_comp _).add (hTk.clm_comp _)

end IsWeakCRSolution

end TauCeti
