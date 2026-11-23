/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.EnergyForm.Sobolev

/-!
# Energy-form lower bounds on slab- or ball-contained domains

For a uniformly elliptic divergence-form operator with bounded drift and nonnegative potential on
a domain `Ω ⊆ ℝ^{n+1}`, the Poincaré inequalities of `TauCeti.Analysis.Sobolev.Poincare.W1p0`
turn the general lower bound
`TauCeti.PDE.UniformlyEllipticOn.mul_norm_sq_le_energyFormH1_self_of_poincare` into explicit
lower bounds on `H¹₀(Ω)`.

## Main results

* `TauCeti.PDE.UniformlyEllipticOn.mul_norm_sq_le_energyFormH1_self_of_subset_slab` and
  `TauCeti.PDE.UniformlyEllipticOn.mul_norm_sq_le_energyFormH1_self_of_subset_ball`: lower bounds on
  `H¹₀(Ω)` for a domain trapped in a slab, or in a ball.

## References

L. C. Evans, *Partial Differential Equations*, Section 6.2; D. Gilbarg and N. Trudinger,
*Elliptic Partial Differential Equations of Second Order*, Chapter 8.
-/

public section

noncomputable section

namespace TauCeti

namespace PDE

open MeasureTheory Set TopologicalSpace

section Euclidean

variable {n : ℕ} {Omega : Opens (EuclideanSpace ℝ (Fin (n + 1)))}
  {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
  {b : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))}
  {c : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} {lam Lam beta gamma : ℝ}

namespace UniformlyEllipticOn

/-- **An energy-form lower bound on `H¹₀(Ω)` for a domain trapped in a slab.** If `Ω ⊆ ℝ^{n+1}` lies
between the hyperplanes `xᵢ = s` and `xᵢ = t`, then every `u ∈ W^{1,2}_0(Ω)` satisfies

`(λ² - β²(t - s)²)/(2λ((t - s)² + 1)) · ‖u‖²_{H¹} ≤ a(u, u)`,

the Poincaré constant of the slab being its width `t - s`. The domain need not be bounded:
boundedness in one direction is enough, and no regularity of `∂Ω` is used, the homogeneous
boundary condition being carried by membership in `W^{1,2}_0(Ω)`. -/
theorem mul_norm_sq_le_energyFormH1_self_of_subset_slab
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))) a lam Lam)
    (ha : AEStronglyMeasurable a (volume.restrict Omega))
    (hb : AEStronglyMeasurable b (volume.restrict Omega))
    (hc : AEStronglyMeasurable c (volume.restrict Omega))
    (hb_bound : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))), ‖b x‖ ≤ beta)
    (hc_bound : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))), ‖c x‖ ≤ gamma)
    (hc_nonneg : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))), 0 ≤ c x)
    {i : Fin (n + 1)} {s t : ℝ}
    (hslab : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))), x i ∈ Icc s t)
    {u : W1p volume Omega 2} (hu : u ∈ w1p0Submodule volume Omega 2) :
    (lam ^ 2 - beta ^ 2 * (t - s) ^ 2) / (2 * lam * ((t - s) ^ 2 + 1)) * ‖u‖ ^ 2
      ≤ energyFormH1 a b c u u :=
  mul_norm_sq_le_energyFormH1_self_of_poincare h ha hb hc hb_bound hc_bound hc_nonneg
    (W1p.norm_value_le_mul_norm_gradient_of_subset_slab hslab hu)

/-- **An energy-form lower bound on `H¹₀(Ω)` for a domain inside a ball.** For
`Ω ⊆ B(z, R) ⊆ ℝ^{n+1}` every `u ∈ W^{1,2}_0(Ω)` satisfies

`(λ² - 4β²R²)/(2λ(4R² + 1)) · ‖u‖²_{H¹} ≤ a(u, u)`.

The Poincaré constant `2R` is the diameter bound, not the sharp one, but it is explicit and
independent of the centre. Together with positivity of the displayed constant, this is the
diagonal estimate used to prove coercivity for a Lax--Milgram application. -/
theorem mul_norm_sq_le_energyFormH1_self_of_subset_ball
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))) a lam Lam)
    (ha : AEStronglyMeasurable a (volume.restrict Omega))
    (hb : AEStronglyMeasurable b (volume.restrict Omega))
    (hc : AEStronglyMeasurable c (volume.restrict Omega))
    (hb_bound : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))), ‖b x‖ ≤ beta)
    (hc_bound : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))), ‖c x‖ ≤ gamma)
    (hc_nonneg : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))), 0 ≤ c x)
    {z : EuclideanSpace ℝ (Fin (n + 1))} {R : ℝ}
    (hball : (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))) ⊆ Metric.ball z R)
    {u : W1p volume Omega 2} (hu : u ∈ w1p0Submodule volume Omega 2) :
    (lam ^ 2 - beta ^ 2 * (2 * R) ^ 2) / (2 * lam * ((2 * R) ^ 2 + 1)) * ‖u‖ ^ 2
      ≤ energyFormH1 a b c u u :=
  mul_norm_sq_le_energyFormH1_self_of_poincare h ha hb hc hb_bound hc_bound hc_nonneg
    (W1p.norm_value_le_mul_norm_gradient_of_subset_ball hball hu)

end UniformlyEllipticOn

end Euclidean

end PDE

end TauCeti
