/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.IteratedGradient.Basic
public import TauCeti.Analysis.Sobolev.WeakDeriv.Basic

/-!
# Uniqueness of iterated weak gradient chains

A chain of iterated weak gradients of `u : E → ℝ` on an open set `Ω` is a family of fields
`G i : E → TauCeti.IteratedGradient E i` such that `u` has weak derivative `innerSL ℝ ∘ G 0` and
each `G (i + 1)` is the weak derivative of `G i`. Since weak derivatives are unique almost
everywhere, two such chains of the same function agree almost everywhere, level by level.

## Main declarations

* `TauCeti.ae_eq_of_iteratedGradient_chain`: uniqueness of weak derivative chains.
* `TauCeti.ae_eq_iteratedGradientChain_of_contDiffOn`: for a `C^{n+1}` representative, the chain is
  the classical one.
-/

public section

open MeasureTheory TopologicalSpace

namespace TauCeti

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {mu : Measure E} {Omega : Opens E}

/-- **Uniqueness of weak derivative chains.** Two chains of iterated weak gradients of the same
function on `Ω` agree almost everywhere on `Ω`, level by level. -/
theorem ae_eq_of_iteratedGradient_chain (n : ℕ) {u : E → ℝ}
    {G G' : (i : ℕ) → E → IteratedGradient E i}
    (h0 : HasWeakFDerivOn mu Omega u (fun x => innerSL ℝ (G 0 x)))
    (hG : ∀ i < n, HasWeakFDerivOn mu Omega (G i) (G (i + 1)))
    (h0' : HasWeakFDerivOn mu Omega u (fun x => innerSL ℝ (G' 0 x)))
    (hG' : ∀ i < n, HasWeakFDerivOn mu Omega (G' i) (G' (i + 1))) :
    ∀ i ≤ n, G i =ᵐ[mu.restrict Omega] G' i := by
  intro i hi
  induction i with
  | zero =>
    filter_upwards [h0.ae_eq h0'] with x hx
    exact innerSL_inj.1 hx
  | succ i ih =>
    exact (hG i (by omega)).ae_eq ((hG' i (by omega)).congr_ae (ih (by omega)).symm)


/-- **Weak derivative chains of `C^{n+1}` functions are classical.** If `u` agrees almost
everywhere on `Ω` with a function `f` that is `C^{n+1}` on `Ω`, then every chain of iterated weak
gradients of `u` agrees almost everywhere on `Ω`, through order `n`, with the classical iterated
gradients `TauCeti.iteratedGradientChain f`. -/
theorem ae_eq_iteratedGradientChain_of_contDiffOn [mu.IsAddHaarMeasure] (n : ℕ) {u f : E → ℝ}
    (hf : ContDiffOn ℝ (n + 1) f Omega) (huf : u =ᵐ[mu.restrict Omega] f)
    {G : (i : ℕ) → E → IteratedGradient E i}
    (h0 : HasWeakFDerivOn mu Omega u (fun x => innerSL ℝ (G 0 x)))
    (hG : ∀ i < n, HasWeakFDerivOn mu Omega (G i) (G (i + 1))) :
    ∀ i ≤ n, G i =ᵐ[mu.restrict Omega] iteratedGradientChain f i :=
  ae_eq_of_iteratedGradient_chain n (h0.congr_ae huf) hG
    (by simpa only [iteratedGradientChain_zero] using
      hasWeakFDerivOn_gradient_of_contDiffOn (hf.of_le (by exact_mod_cast (by omega : 1 ≤ n + 1))))
    fun i hi => by
      rw [iteratedGradientChain_succ]
      exact ContDiffOn.hasWeakFDerivOn_fderiv fun x hx =>
        (contDiffAt_iteratedGradientChain (hf.contDiffAt (Omega.isOpen.mem_nhds hx)) i
          (by exact_mod_cast (by omega : 1 + i + 1 ≤ n + 1))).contDiffWithinAt

end TauCeti
