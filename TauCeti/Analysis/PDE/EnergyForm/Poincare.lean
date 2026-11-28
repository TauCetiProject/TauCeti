/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.EnergyForm.Sobolev
import TauCeti.Analysis.Sobolev.Poincare.WholeSpace
import TauCeti.MeasureTheory.Function.Lp.Norm

/-!
# Energy-form lower bounds on slab- or ball-contained domains

For a uniformly elliptic divergence-form operator with bounded drift and nonnegative potential on
a domain `Ω ⊆ ℝ^{n+1}`, the Poincaré inequalities of `TauCeti.Analysis.Sobolev.Poincare.W1p0`
turn the general lower bound
`TauCeti.PDE.UniformlyEllipticOn.mul_norm_sq_le_energyFormH1_self_of_poincare` into explicit
lower bounds on `H¹₀(Ω)`.

Some such geometric restriction is needed: on the whole space `ℝⁿ` no Poincaré inequality holds,
and the energy form of a bounded principal coefficient without drift and mass is not coercive on
`H¹₀(ℝⁿ)` (`TauCeti.PDE.not_isCoercive_energyFormH1L0_top`).

## Main results

* `TauCeti.PDE.UniformlyEllipticOn.mul_norm_sq_le_energyFormH1_self_of_subset_slab` and
  `TauCeti.PDE.UniformlyEllipticOn.mul_norm_sq_le_energyFormH1_self_of_subset_ball`: lower bounds on
  `H¹₀(Ω)` for a domain trapped in a slab, or in a ball.
* `TauCeti.PDE.not_isCoercive_energyFormH1L0_top`: no coercivity on the whole space.

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

section WholeSpace

open scoped Distributions Matrix

attribute [local instance] W1p0.instNormedAddCommGroup

variable {ι : Type*} [Fintype ι] {mu : Measure (EuclideanSpace ℝ ι)} [mu.IsAddHaarMeasure]
  {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ}

/-- **No coercivity on the whole space.** On `ℝⁿ`, the energy form `∫ ⟨a ∇u, ∇v⟩` of a principal
coefficient with essentially bounded energy density, without drift and mass, is not coercive on
`H¹₀(ℝⁿ)`, however elliptic `a` is. Coercivity `C ‖u‖²_{H¹} ≤ ∫ ⟨a ∇u, ∇u⟩ ≤ Λ ‖∇u‖²_{L²}` would
give the Poincaré inequality `‖u‖_{L²} ≤ √(Λ / C) ‖∇u‖_{L²}` for every test function, and no such
inequality holds on the whole space (`TauCeti.not_exists_eLpNorm_le_const_mul_eLpNorm_fderiv`):
the dilates `φ(x / r)` have `‖∇φ(· / r)‖_{L²} / ‖φ(· / r)‖_{L²} = r⁻¹ ‖∇φ‖_{L²} / ‖φ‖_{L²} → 0`. So
on unbounded domains the lower bound `λ ‖∇u‖²_{L²}` of the ellipticity of `a` does not give
coercivity, and a Poincaré inequality or a positive mass term is needed. -/
theorem not_isCoercive_energyFormH1L0_top
    (hcoeff : MemLp (fun x ↦ energyIntegrand (a x)
      ((0 : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι) x) ((0 : EuclideanSpace ℝ ι → ℝ) x)) ⊤
      (mu.restrict (⊤ : Opens (EuclideanSpace ℝ ι)))) :
    ¬IsCoercive (energyFormH1L0 hcoeff) := by
  rintro ⟨C, hC, hcoer⟩
  -- An essential bound `K` of the energy density bounds the principal coefficient.
  obtain ⟨K, hK0, hab⟩ := exists_ae_abs_dotProduct_mulVec_le_of_memLp_energyIntegrand hcoeff
  -- Coercivity would give a Poincaré inequality with constant `√(K / C)` on the whole space.
  refine not_exists_eLpNorm_le_const_mul_eLpNorm_fderiv (μ := mu) (p := 2) (k := ⊤) two_ne_zero
    ⟨(√(K / C)).toNNReal, fun φ hφ hφc ↦ ?_⟩
  let ψ : 𝓓((⊤ : Opens (EuclideanSpace ℝ ι)), ℝ) := ⟨φ, hφ, hφc, by simp⟩
  let w : W1p0 mu ⊤ 2 := ⟨W1p.ofTestFunctionₗ mu ⊤ 2 ψ, W1p.ofTestFunctionₗ_mem_w1p0Submodule ψ⟩
  have hv := W1p.norm_value_ofTestFunctionₗ_top_sq (mu := mu) ψ
  have hg := W1p.norm_gradient_ofTestFunctionₗ_top_sq (mu := mu) ψ
  have hupper := abs_energyFormH1_zero_zero_le_of_bounds hK0 hab
    (w : W1p mu ⊤ 2) (w : W1p mu ⊤ 2)
  have hlower := hcoer w
  rw [energyFormH1L0_apply] at hlower
  have hnorm : ‖w‖ ^ 2 = ‖W1p.value (w : W1p mu ⊤ 2)‖ ^ 2 + ‖W1p.gradient (w : W1p mu ⊤ 2)‖ ^ 2 :=
    W1p.norm_sq_eq_norm_value_sq_add_norm_gradient_sq _
  set v := ‖W1p.value (w : W1p mu ⊤ 2)‖
  set g := ‖W1p.gradient (w : W1p mu ⊤ 2)‖
  have hvg : v ≤ √(K / C) * g := by
    have key : v ^ 2 ≤ K / C * g ^ 2 := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hC]
      nlinarith [(abs_le.1 hupper).2, sq_nonneg g, sq_nonneg v]
    calc v = √(v ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
      _ ≤ √(K / C * g ^ 2) := Real.sqrt_le_sqrt key
      _ = √(K / C) * g := by
        rw [Real.sqrt_mul (div_nonneg hK0 hC.le), Real.sqrt_sq (norm_nonneg _)]
  -- Both sides of the Poincaré inequality are the `L²` norms of the value and the gradient.
  have hφ2 : MemLp φ 2 mu := (hφ.continuous).memLp_of_hasCompactSupport hφc
  have hDφ2 : MemLp (fderiv ℝ φ) 2 mu :=
    (hφ.continuous_fderiv (by simp)).memLp_of_hasCompactSupport (hφc.fderiv (𝕜 := ℝ))
  rw [hφ2.eLpNorm_two_eq_ofReal_sqrt_integral, hDφ2.eLpNorm_two_eq_ofReal_sqrt_integral,
    ENNReal.ofNNReal_toNNReal, ← ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
  refine ENNReal.ofReal_le_ofReal ?_
  have hv' : √(∫ x, ‖φ x‖ ^ 2 ∂mu) = v := by
    rw [show (∫ x, ‖φ x‖ ^ 2 ∂mu) = v ^ 2 by simp [hv, ψ], Real.sqrt_sq (norm_nonneg _)]
  have hg' : √(∫ x, ‖fderiv ℝ φ x‖ ^ 2 ∂mu) = g := by
    rw [show (∫ x, ‖fderiv ℝ φ x‖ ^ 2 ∂mu) = g ^ 2 by simp [hg, ψ], Real.sqrt_sq (norm_nonneg _)]
  rw [hv', hg']
  exact hvg

end WholeSpace

end PDE

end TauCeti
