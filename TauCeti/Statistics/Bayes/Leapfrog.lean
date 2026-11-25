/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan Braams, Claude
-/
module

public import Mathlib.MeasureTheory.Group.Prod

/-!
# The leapfrog step of Hamiltonian Monte Carlo

On the phase space `E × E` of positions and momenta of a real vector space `E`, one
**leapfrog step** with identity mass matrix, gradient `g` of the potential (the negative of
the force) and step size `h` is the composition of a half kick `p ↦ p - (h/2) g(x)`, a drift
`x ↦ x + h p` and a second half kick. The **momentum flip** is `(x, p) ↦ (x, -p)`.

The step is reversible: the flip, the step, the flip and the step compose to the identity, so
`momentumFlip ∘ leapfrogStep g h` is an involution and the step is injective. Each kick and the
drift are shears, so the step preserves every product `μ.prod μ` of a right-invariant measure
with itself, in particular Lebesgue measure on `ℝᵈ × ℝᵈ`, for measurable `g`.

## Main definitions

* `TauCeti.leapfrogStep g h`: one leapfrog step.
* `TauCeti.momentumFlip`: the momentum flip `(x, p) ↦ (x, -p)`.

## Main results

* `TauCeti.leapfrogStep_momentumFlip_leapfrogStep`: stepping from the flipped end point returns
  to the flipped starting point.
* `TauCeti.involutive_momentumFlip_comp_leapfrogStep`, `TauCeti.leapfrogStep_injective`.
* `TauCeti.measurePreserving_leapfrogStep`: the step preserves `μ.prod μ`.

The definitions and proofs are adapted from the lean-CKSD project
(<https://github.com/bjbraams/lean-CKSD>), files `CKSD/Bayes/Basic.lean` and
`CKSD/Bayes/Langevin/Hamiltonian/Leapfrog.lean`, and generalized from `ℝᵈ` to a real vector
space with a right-invariant measure.

## References

* B. Leimkuhler and S. Reich, *Simulating Hamiltonian Dynamics*, Cambridge University Press
  (2004), §2.5 and §4.3.1.
-/

public section

noncomputable section

open MeasureTheory

namespace TauCeti

variable {E : Type*}

/-- The **momentum flip** `(x, p) ↦ (x, -p)` on phase space. -/
def momentumFlip [Neg E] (z : E × E) : E × E := (z.1, -z.2)

@[simp]
theorem momentumFlip_apply [Neg E] (z : E × E) : momentumFlip z = (z.1, -z.2) := (rfl)

/-- Flipping the momentum twice gives back the state. -/
theorem momentumFlip_momentumFlip [InvolutiveNeg E] (z : E × E) :
    momentumFlip (momentumFlip z) = z := by
  simp

/-- The momentum flip is an involution. -/
theorem involutive_momentumFlip [InvolutiveNeg E] : Function.Involutive (momentumFlip (E := E)) :=
  momentumFlip_momentumFlip

variable [AddCommGroup E] [Module ℝ E]

/-- One **leapfrog step** with identity mass matrix, gradient `g` of the potential (the
negative of the force) and step size `h`:
`p' = p - (h/2) g(x)`, `x' = x + h p'`, `p'' = p' - (h/2) g(x')`. -/
def leapfrogStep (g : E → E) (h : ℝ) (z : E × E) : E × E :=
  (z.1 + h • (z.2 - (h / 2) • g z.1),
    z.2 - (h / 2) • g z.1 - (h / 2) • g (z.1 + h • (z.2 - (h / 2) • g z.1)))

theorem leapfrogStep_apply (g : E → E) (h : ℝ) (z : E × E) :
    leapfrogStep g h z = (z.1 + h • (z.2 - (h / 2) • g z.1),
      z.2 - (h / 2) • g z.1 - (h / 2) • g (z.1 + h • (z.2 - (h / 2) • g z.1))) := (rfl)

/-- **Reversibility** of the leapfrog step: stepping from the flipped end point returns to the
flipped starting point. -/
theorem leapfrogStep_momentumFlip_leapfrogStep (g : E → E) (h : ℝ) (z : E × E) :
    leapfrogStep g h (momentumFlip (leapfrogStep g h z)) = momentumFlip z := by
  have hx : z.1 + h • (z.2 - (h / 2) • g z.1) + h • (-(z.2 - (h / 2) • g z.1 -
      (h / 2) • g (z.1 + h • (z.2 - (h / 2) • g z.1))) -
      (h / 2) • g (z.1 + h • (z.2 - (h / 2) • g z.1))) = z.1 := by
    rw [neg_sub, sub_sub_cancel_left, smul_neg, add_neg_cancel_right]
  simp only [leapfrogStep_apply, momentumFlip_apply, hx, Prod.mk.injEq, true_and]
  abel

/-- The flip, the step, the flip and the step compose to the identity. -/
theorem involutive_momentumFlip_comp_leapfrogStep (g : E → E) (h : ℝ) :
    Function.Involutive (momentumFlip ∘ leapfrogStep g h) := fun z ↦ by
  simp only [Function.comp_apply, leapfrogStep_momentumFlip_leapfrogStep,
    momentumFlip_momentumFlip]

/-- The leapfrog step is injective. -/
theorem leapfrogStep_injective (g : E → E) (h : ℝ) : Function.Injective (leapfrogStep g h) :=
  (involutive_momentumFlip_comp_leapfrogStep g h).injective.of_comp

/-- The **leapfrog step preserves** `μ.prod μ` for a right-invariant measure `μ` and a
measurable gradient `g` of the potential; in particular it preserves Lebesgue measure on
`ℝᵈ × ℝᵈ`. -/
theorem measurePreserving_leapfrogStep [MeasurableSpace E] [MeasurableAdd₂ E]
    [MeasurableConstSMul ℝ E] {μ : Measure E} [SFinite μ] [μ.IsAddRightInvariant]
    {g : E → E} (hg : Measurable g) (h : ℝ) :
    MeasurePreserving (leapfrogStep g h) (μ.prod μ) (μ.prod μ) := by
  -- A kick `(x, p) ↦ (x, p + f x)` is a translation in each fibre.
  have kick {f : E → E} (hf : Measurable f) :
      MeasurePreserving (fun z : E × E ↦ (z.1, z.2 + f z.1)) (μ.prod μ) (μ.prod μ) :=
    (MeasurePreserving.id μ).skew_product (g := fun x p ↦ p + f x)
      (measurable_snd.add (hf.comp measurable_fst))
      (ae_of_all _ fun x ↦ (measurePreserving_add_right μ (f x)).map_eq)
  have hK := kick (hg.const_smul (-(h / 2)))
  have hD : MeasurePreserving (fun z : E × E ↦ (z.1 + h • z.2, z.2)) (μ.prod μ) (μ.prod μ) :=
    (Measure.measurePreserving_swap.comp
      (kick (measurable_id.const_smul h))).comp
      Measure.measurePreserving_swap
  convert hK.comp (hD.comp hK) using 1
  ext z <;> simp [leapfrogStep_apply, sub_eq_add_neg]

end TauCeti
