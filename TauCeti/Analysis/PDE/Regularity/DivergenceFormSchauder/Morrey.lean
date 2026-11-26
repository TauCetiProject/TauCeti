/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Regularity.DivergenceFormSchauder.Basic
public import TauCeti.MeasureTheory.Function.Morrey
import TauCeti.Analysis.PDE.FundamentalSolution.Divergence
import TauCeti.Analysis.Sobolev.TestFunctionLp.Basic
import TauCeti.Topology.MetricSpace.Holder

/-!
# Schauder estimates for divergence-form equations with data in a Morrey space

Let `u ∈ H¹(Ω)` be a weak solution of the divergence-form equation

`-∂ᵢ(aⁱʲ ∂ⱼu) = f - div G` in an open set `Ω ⊆ ℝ^{n+1}`,

with `a` uniformly elliptic and `a`, `G` `α`-Hölder, `0 < α < 1`, on the `R`-thickening of a set
`S`. The interior Schauder estimate with a datum `f ∈ L^q` gives a `C^{1,β}` gradient only for
`β ≤ 1 - (n + 1) / q`, and needs `q > n + 1`. This file proves the full exponent `β = α` for a
datum in the **Morrey space** `L^{1, n + α}(ℝ^{n+1})`, the functions whose mass on balls of radius
`r` is at most a multiple of `r^(n + α)`: the precise representative of `∇u` is `α`-Hölder on `S`,
with constant

`C (K_G + K_f + R^{-(n+1)/2-α} ‖∇u‖_{L²(Ω)})`,

where `K_G` is the Hölder constant of `G`, `K_f` bounds the Morrey norm of `f`, and `C` depends only
on `n`, `α`, `λ`, `Λ` and a bound `M ≥ R^α K_a`
(`exists_holderOnWith_preciseRepresentative_gradient_of_holderOnWith_of_morreyNormPow_le`, in the
`TauCeti.PDE` namespace).
This is the form of Morrey's `C^{1,α}` estimate in which zero-order terms with coefficients in
Morrey spaces enter, such as the term `d u`, `d ∈ L^{1, n + α}`, in Hopf's boundary point lemma for
weak supersolutions.

## The argument

A measurable, compactly supported `f` in `L^{1, n + α}` is minus the divergence of an `α`-Hölder
field `H`, the gradient of its Newtonian potential, with Hölder constant a multiple of the Morrey
norm of `f` (`TauCeti.exists_holderWith_and_integral_inner_gradient_eq_of_morreyNormPow_le`). So `u`
solves `-∂ᵢ(aⁱʲ ∂ⱼu) = -div (G + H)`, with no scalar datum, and the Schauder estimate for such
equations
(`exists_holderOnWith_preciseRepresentative_gradient_of_holderOnWith_matrixBilinearForm`, in the
`TauCeti.PDE` namespace) applies.

## References

* C. B. Morrey, *Multiple Integrals in the Calculus of Variations*, Springer, 1966, §5.5.
* M. Giaquinta, L. Martinazzi, *An Introduction to the Regularity Theory for Elliptic Systems,
  Harmonic Maps and Minimal Graphs*, 2nd ed., Chapter 5.
* L. Rosales, *Generalizing Hopf's boundary point lemma*, Canad. Math. Bull. (2019),
  arXiv:1806.07003, Lemma 3.1.
-/

public section

noncomputable section

open InnerProductSpace MeasureTheory Metric Module Set TopologicalSpace TauCeti.MeasureTheory
open scoped Distributions ENNReal Gradient InnerProductSpace NNReal

namespace TauCeti

namespace PDE

variable {n : ℕ}

/-- **Interior Schauder estimate with a datum in a Morrey space.** Let `0 < α < 1`. There is a
constant `C`, depending only on `n`, `α`, `λ`, `Λ` and `M`, such that the following holds. Let
`Ω ⊆ ℝ^{n+1}` be open and let `u ∈ H¹(Ω)` be a weak solution of `-∂ᵢ(aⁱʲ ∂ⱼu) = f - div G` in `Ω`,
that is `∫_Ω ⟨a ∇u, ∇φ⟩ = ∫_Ω ⟨G, ∇φ⟩ + ∫_Ω f φ` for every test function `φ`, with `G` locally
integrable on `Ω`. Let `S` be a set whose open `R`-thickening lies in `Ω`, let `a` be uniformly
elliptic with constants `λ`, `Λ` at the points of `S`, and let `a` and `G` be `α`-Hölder on the
`R`-thickening of `S` with constants `K_a` and `K_G`, where `K_a R^α ≤ M`. Let `f` be measurable
and compactly supported, with Morrey norm `‖f‖_{L^{1, n + α}(ℝ^{n+1})} ≤ K_f`, that is
`∫_{B(x, r)} |f| ≤ K_f r^(n + α)` on every closed ball. Then the precise representative of `∇u` is
`α`-Hölder on `S`, with constant `C (K_G + K_f + R^{-(n+1)/2-α} ‖∇u‖_{L²(Ω)})`.

The precise representative agrees with `∇u` almost everywhere on `Ω`
(`TauCeti.MeasureTheory.ae_eq_restrict_preciseRepresentative`). A compactly supported
`f ∈ L^q(ℝ^{n+1})`, `q = (n + 1) / (1 - α)`, satisfies the Morrey hypothesis
(`TauCeti.MeasureTheory.morreyNormPow_le_eLpNorm_rpow_mul`). So, for such `f` and a locally
integrable `G`, this recovers up to constants the case `β = α` of
`exists_holderOnWith_preciseRepresentative_gradient_of_holderOnWith_matrixBilinearForm_of_memLp`,
which needs `f` only in `L^q` of the `R`-thickening of `S` and no integrability of `G`. -/
theorem exists_holderOnWith_preciseRepresentative_gradient_of_holderOnWith_of_morreyNormPow_le
    {α : ℝ≥0} (hα : 0 < α) (hα1 : α < 1) {lam Lam M : ℝ} :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Omega : Opens (EuclideanSpace ℝ (Fin (n + 1)))}
      {u : W1p volume Omega 2}
      {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
      {G : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))}
      {f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} {Ka KG Kf : ℝ≥0}
      {S : Set (EuclideanSpace ℝ (Fin (n + 1)))} {R : ℝ},
      UniformlyEllipticOn S a lam Lam →
      HolderOnWith Ka α (fun x => matrixBilinearForm (a x)) (thickening R S) →
      HolderOnWith KG α G (thickening R S) → (Ka : ℝ) * R ^ (α : ℝ) ≤ M →
      LocallyIntegrableOn G Omega →
      AEStronglyMeasurable f → HasCompactSupport f → morreyNormPow volume univ 1 (n + α) f ≤ Kf →
      (∀ φ : 𝓓(Omega, ℝ), energyFormH1 a 0 0 u (W1p.ofTestFunctionₗ volume Omega 2 φ) =
        (∫ x in Omega, ⟪G x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ) +
          ∫ x in Omega, f x * φ x) →
      0 < R → thickening R S ⊆ Omega →
        HolderOnWith (C * (KG + Kf + R ^ (-(((n : ℝ) + 1) / 2 + α)) * ‖W1p.gradient u‖)).toNNReal
          α (preciseRepresentative volume
            (W1p.gradient u : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))))
          S := by
  obtain ⟨C₀, hC₀⟩ := exists_holderWith_and_integral_inner_gradient_eq_of_morreyNormPow_le
    (volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))) hα hα1
  obtain ⟨C, hC, hS⟩ :=
    exists_holderOnWith_preciseRepresentative_gradient_of_holderOnWith_matrixBilinearForm
      (n := n) hα hα1 (lam := lam) (Lam := Lam) (M := M)
  refine ⟨C * (1 + C₀), by positivity, fun {Omega u a G f Ka KG Kf S R} hell haK hGK hM hGi hfi hfc
    hfM hu hR hRS => ?_⟩
  obtain ⟨H, hH, hHeq⟩ := hC₀ f Kf hfi hfc (by
    rwa [finrank_euclideanSpace_fin, Nat.cast_add, Nat.cast_one, add_sub_cancel_right])
  -- `u` solves the equation with the field `G + H` and no scalar datum.
  have hu' (φ : 𝓓(Omega, ℝ)) : energyFormH1 a 0 0 u (W1p.ofTestFunctionₗ volume Omega 2 φ) =
      ∫ x in Omega, ⟪(G + H) x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ := by
    have hφK : tsupport (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) ⊆ Omega := φ.tsupport_subset
    have hGint : IntegrableOn (fun x => ⟪G x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ)
        Omega := by
      have hGK := hGi.integrableOn_compact_subset hφK φ.hasCompactSupport.isCompact
      refine IntegrableOn.of_forall_sdiff_eq_zero
        (integrable_inner_gradient_testFunction (p := 1) (memLp_one_iff_integrable.2 hGK) φ)
        Omega.isOpen.measurableSet fun x hx => ?_
      rw [gradient_of_notMem_tsupport hx.2, inner_zero_right]
    have hHint : IntegrableOn (fun x => ⟪H x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ)
        Omega :=
      ((hH.continuous hα).inner
        (continuous_gradient_testFunction φ)).integrable_of_hasCompactSupport
        (φ.hasCompactSupport.gradient.mono fun x hx h0 => hx (by
          simp only [h0, inner_zero_right])) |>.integrableOn
    have hf : ∫ x in Omega, f x * φ x =
        ∫ x in Omega, ⟪H x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ := by
      rw [setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => ?_,
        setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => ?_,
        hHeq φ (φ.contDiff.of_le (by simp)) φ.hasCompactSupport]
      · rw [gradient_of_notMem_tsupport fun h => hx (hφK h), inner_zero_right]
      · rw [image_eq_zero_of_notMem_tsupport fun h => hx (hφK h), mul_zero]
    simp only [Pi.add_apply, inner_add_left]
    rw [integral_add hGint hHint, hu φ, hf]
  have h := hS hell haK (hGK.add (hH.holderOnWith _)) hM hu' hR hRS
  refine fun x hx y hy => (h x hx y hy).trans
    (mul_le_mul_left (ENNReal.coe_le_coe.2 (Real.toNNReal_le_toNNReal ?_)) _)
  have hKf : (0 : ℝ) ≤ Kf := Kf.coe_nonneg
  have hKG : (0 : ℝ) ≤ KG := KG.coe_nonneg
  have hgrad : 0 ≤ R ^ (-(((n : ℝ) + 1) / 2 + α)) * ‖W1p.gradient u‖ := by positivity
  push_cast
  nlinarith [mul_nonneg hC (mul_nonneg C₀.coe_nonneg hKG),
    mul_nonneg hC (mul_nonneg C₀.coe_nonneg hgrad)]

end PDE

end TauCeti
