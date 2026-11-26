/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Regularity.DivergenceFormSchauder.BoundedDomain
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

It then proves the same gain up to the boundary for zero boundary values. On a bounded open set
`Ω` with `C^{1,α}` boundary, a weak solution `u ∈ H¹₀(Ω)` of `-∂ᵢ(aⁱʲ ∂ⱼu) = f + h - div G`, with
`f ∈ L^q(Ω)` and `h` in the Morrey space `L^{1, n + α}(Ω)` of `Ω` itself, has a gradient that
agrees almost everywhere with a function `β`-Hölder on `closure Ω` for
`β ≤ min(α, 1 - (n + 1) / q)`, with Hölder constant and supremum at most
`C (K_G + ‖f‖_{L^q(Ω)} + K_h + ‖u‖_{H¹(Ω)})`, where `K_h` bounds the Morrey norm of `h`. Both the
estimate near a single boundary point, which needs a boundary chart there only, and the global
estimate are proved.

These are the forms of Morrey's `C^{1,α}` estimate in which zero-order terms with coefficients in
Morrey spaces enter, such as the term `d u`, `d ∈ L^{1, n + α}`, in Hopf's boundary point lemma for
weak supersolutions: Rosales applies the estimate up to the boundary of an annulus.

## The argument

A measurable, compactly supported `f` in `L^{1, n + α}` is minus the divergence of an `α`-Hölder
field `H`, the gradient of its Newtonian potential, with Hölder constant a multiple of the Morrey
norm of `f` (`TauCeti.exists_holderWith_and_integral_inner_gradient_eq_of_morreyNormPow_le`). So `u`
solves `-∂ᵢ(aⁱʲ ∂ⱼu) = -div (G + H)`, with no scalar datum, and the Schauder estimate for such
equations
(`exists_holderOnWith_preciseRepresentative_gradient_of_holderOnWith_matrixBilinearForm`, in the
`TauCeti.PDE` namespace) applies. On a bounded domain, the extension of `h` by zero is such a datum,
with Morrey norm at most `2^(n + α)` times that of `h` on `Ω`
(`TauCeti.MeasureTheory.morreyNormPow_univ_indicator_le`), and the estimates with an `L^q` datum
(`exists_holderOnWith_gradient_ball_inter_closure_of_graph` and
`exists_holderOnWith_gradient_closure_of_isBounded`) apply to the field `G + H` and the datum `f`.

## Main declarations

All in the `TauCeti.PDE` namespace.

* `exists_holderOnWith_preciseRepresentative_gradient_of_holderOnWith_of_morreyNormPow_le`: the
  interior estimate.
* `exists_holderOnWith_gradient_ball_inter_closure_of_graph_of_morreyNormPow_le`: the estimate near
  a boundary point of a bounded domain, for zero boundary values.
* `exists_holderOnWith_gradient_closure_of_isBounded_of_morreyNormPow_le`: the global estimate on a
  bounded domain with `C^{1,α}` boundary, for zero boundary values.

## References

* C. B. Morrey, *Multiple Integrals in the Calculus of Variations*, Springer, 1966, §5.5.
* M. Giaquinta, L. Martinazzi, *An Introduction to the Regularity Theory for Elliptic Systems,
  Harmonic Maps and Minimal Graphs*, 2nd ed., Chapter 5.
* L. Rosales, *Generalizing Hopf's boundary point lemma*, Canad. Math. Bull. (2019),
  arXiv:1806.07003, Lemma 3.1.
* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Theorem 8.33 (the global `C^{1,α}` estimate).
-/

public section

noncomputable section

open InnerProductSpace MeasureTheory Metric Module Set TopologicalSpace TauCeti.MeasureTheory
open scoped Distributions ENNReal Gradient InnerProductSpace NNReal

namespace TauCeti

namespace PDE

variable {n : ℕ}

/-- A field `H` with `-div H = h` in the whole space, tested against compactly supported `C¹`
functions, turns the scalar datum `h` of the weak form of a divergence-form equation on an open set
`Ω` into the field datum `H`: for every test function `φ` on `Ω`,
`∫_Ω ⟨G + H, ∇φ⟩ = ∫_Ω ⟨G, ∇φ⟩ + ∫_Ω h φ`. -/
private theorem setIntegral_inner_add_gradient_eq {Omega : Opens (EuclideanSpace ℝ (Fin (n + 1)))}
    {G H : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))}
    {h : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} (hG : LocallyIntegrableOn G Omega)
    (hH : Continuous H)
    (hHh : ∀ φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ, ContDiff ℝ 1 φ → HasCompactSupport φ →
      ∫ x, ⟪H x, ∇ φ x⟫_ℝ = ∫ x, h x * φ x) (φ : 𝓓(Omega, ℝ)) :
    ∫ x in Omega, ⟪(G + H) x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ =
      (∫ x in Omega, ⟪G x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ) +
        ∫ x in Omega, h x * φ x := by
  have hφK : tsupport (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) ⊆ Omega := φ.tsupport_subset
  have hGint : IntegrableOn (fun x => ⟪G x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ)
      Omega := by
    have hGK := hG.integrableOn_compact_subset hφK φ.hasCompactSupport.isCompact
    refine IntegrableOn.of_forall_sdiff_eq_zero
      (integrable_inner_gradient_testFunction (p := 1) (memLp_one_iff_integrable.2 hGK) φ)
      Omega.isOpen.measurableSet fun x hx => ?_
    rw [gradient_of_notMem_tsupport hx.2, inner_zero_right]
  have hHint : IntegrableOn (fun x => ⟪H x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ)
      Omega :=
    (hH.inner (continuous_gradient_testFunction φ)).integrable_of_hasCompactSupport
      (φ.hasCompactSupport.gradient.mono fun x hx h0 => hx (by
        simp only [h0, inner_zero_right])) |>.integrableOn
  have hh : ∫ x in Omega, h x * φ x =
      ∫ x in Omega, ⟪H x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => ?_,
      setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => ?_,
      hHh φ (φ.contDiff.of_le (by simp)) φ.hasCompactSupport]
    · rw [gradient_of_notMem_tsupport fun h => hx (hφK h), inner_zero_right]
    · rw [image_eq_zero_of_notMem_tsupport fun h => hx (hφK h), mul_zero]
  simp only [Pi.add_apply, inner_add_left]
  rw [integral_add hGint hHint, hh]

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
    rw [setIntegral_inner_add_gradient_eq hGi (hH.continuous hα) hHeq, hu φ]
  have h := hS hell haK (hGK.add (hH.holderOnWith _)) hM hu' hR hRS
  refine fun x hx y hy => (h x hx y hy).trans
    (mul_le_mul_left (ENNReal.coe_le_coe.2 (Real.toNNReal_le_toNNReal ?_)) _)
  have hKf : (0 : ℝ) ≤ Kf := Kf.coe_nonneg
  have hKG : (0 : ℝ) ≤ KG := KG.coe_nonneg
  have hgrad : 0 ≤ R ^ (-(((n : ℝ) + 1) / 2 + α)) * ‖W1p.gradient u‖ := by positivity
  push_cast
  nlinarith [mul_nonneg hC (mul_nonneg C₀.coe_nonneg hKG),
    mul_nonneg hC (mul_nonneg C₀.coe_nonneg hgrad)]

/-- A scalar datum `h` in the Morrey space `L^{1, n + α}(Ω)` of a bounded open set
`Ω ⊆ ℝ^{n+1}`, `0 < α < 1`, is minus the divergence in `Ω` of an `α`-Hölder field `H` on the whole
space, with Hölder constant `C K_h` for a bound `K_h` on the Morrey norm of `h` and a constant `C`
depending only on `n` and `α`: tested against `φ ∈ 𝓓(Ω)`, `∫_Ω ⟨G + H, ∇φ⟩ = ∫_Ω ⟨G, ∇φ⟩ + ∫_Ω h φ`
for every locally integrable field `G`. The field is that of the extension of `h` by zero. -/
private theorem exists_holderWith_and_setIntegral_inner_add_gradient_eq {α : ℝ≥0} (hα : 0 < α)
    (hα1 : α < 1) :
    ∃ C : ℝ≥0, ∀ {Omega : Opens (EuclideanSpace ℝ (Fin (n + 1)))}
      {h : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} {Kh : ℝ≥0},
      Bornology.IsBounded (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))) →
      AEStronglyMeasurable h (volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin (n + 1))))) →
      morreyNormPow volume Omega 1 (n + α) h ≤ Kh →
      ∃ H : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)),
        HolderWith (C * Kh) α H ∧
        ∀ {G : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))},
          LocallyIntegrableOn G Omega → ∀ φ : 𝓓(Omega, ℝ),
            ∫ x in Omega, ⟪(G + H) x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ =
              (∫ x in Omega, ⟪G x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ) +
                ∫ x in Omega, h x * φ x := by
  obtain ⟨C₀, hC₀⟩ := exists_holderWith_and_integral_inner_gradient_eq_of_morreyNormPow_le
    (volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))) hα hα1
  refine ⟨C₀ * Real.toNNReal (2 ^ ((n : ℝ) + α)), fun {Omega h Kh} hΩ hh hhM => ?_⟩
  have hΩm := Omega.isOpen.measurableSet
  -- The extension of `h` by zero is a compactly supported Morrey function on the whole space.
  obtain ⟨H, hH, hHeq⟩ := hC₀ ((Omega : Set _).indicator h) (Real.toNNReal (2 ^ ((n : ℝ) + α)) * Kh)
    ((aestronglyMeasurable_indicator_iff hΩm).2 hh)
    (HasCompactSupport.intro' hΩ.isCompact_closure isClosed_closure fun x hx =>
      indicator_of_notMem (fun hx' => hx (subset_closure hx')) h)
    (by
      simp only [finrank_euclideanSpace_fin, Nat.cast_add_one, add_sub_cancel_right,
        ENNReal.coe_mul]
      -- `ENNReal.ofReal r` is by definition the coercion of `r.toNNReal`.
      exact (morreyNormPow_univ_indicator_le one_pos).trans (mul_le_mul' le_rfl hhM))
  refine ⟨H, by rwa [mul_assoc], fun {G} hG φ => ?_⟩
  rw [setIntegral_inner_add_gradient_eq hG (hH.continuous hα) hHeq]
  congr 1
  exact setIntegral_congr_fun hΩm fun x hx => by rw [indicator_of_mem hx]

/-- The bookkeeping of the constants: with the field of the Morrey datum added to `G`, a bound
`κ (K_G + C K_h + F + U)` is at most `κ (1 + C) (K_G + F + K_h + U)`. -/
private theorem mul_add_mul_add_add_le {κ C KG Kh F U : ℝ} (hκ : 0 ≤ κ) (hC : 0 ≤ C)
    (hKG : 0 ≤ KG) (hKh : 0 ≤ Kh) (hF : 0 ≤ F) (hU : 0 ≤ U) :
    κ * (KG + C * Kh + F + U) ≤ κ * (1 + C) * (KG + F + Kh + U) := by
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left (by
    nlinarith [mul_nonneg hC hKG, mul_nonneg hC hF, mul_nonneg hC hU]) hκ

/-- **The `C^{1,β}` estimate near a boundary point with a datum in a Morrey space.** Let `x` be a
frontier point of a bounded open set `Ω ⊆ ℝ^{n+1}`, near which `Ω` is, in rigid coordinates
centred at `x`, the region above the graph of a `C¹` function with `α`-Hölder derivative,
`0 < α < 1`. Let `0 < β ≤ α`, `2 ≤ q ≤ ∞` and `β ≤ 1 - (n + 1) / q`. Then there is a ball
`B(x, ρ)` and a constant `κ`, depending on the chart, `n`, `α`, `β`, `q`, `λ`, `Λ` and `M`, with
the following property. Let `a` be uniformly elliptic on `closure Ω` with constants `λ, Λ` and
`α`-Hölder there with constant `K_a ≤ M`, let `G` be `α`-Hölder on `closure Ω` with constant
`K_G`, let `f ∈ L^q(Ω)`, and let `h` be a.e.-strongly measurable on `Ω` with Morrey norm
`‖h‖_{L^{1, n + α}(Ω)} ≤ K_h`. Then for every weak solution `u ∈ H¹₀(Ω)` of
`-∂ᵢ(aⁱʲ ∂ⱼu) = f + h - div G` in `Ω` the gradient `∇u` agrees almost everywhere on
`Ω ∩ B(x, ρ)` with a function that is `β`-Hölder with constant `κ Q` and bounded by `κ Q` on
`B(x, ρ) ∩ closure Ω`, where `Q = K_G + ‖f‖_{L^q(Ω)} + K_h + ‖u‖_{H¹(Ω)}`.

For `h = 0` this is `exists_holderOnWith_gradient_ball_inter_closure_of_graph`. The Morrey datum
reaches the full exponent `β = α`, which an `L^q` datum reaches only for
`q ≥ (n + 1) / (1 - α)`; this is the form in which a zero-order term `d u` with `u` bounded and
`d ∈ L^{1, n + α}(Ω)` enters the estimate. -/
theorem exists_holderOnWith_gradient_ball_inter_closure_of_graph_of_morreyNormPow_le {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {α β : ℝ≥0} (hβ : 0 < β) (hβα : β ≤ α) (hα1 : α < 1) {q : ℝ≥0∞} (hq : 2 ≤ q)
    (hβq : (β : ℝ) ≤ 1 - ((n : ℝ) + 1) / q.toReal) {Ω : Opens (EuclideanSpace ℝ (Fin (n + 1)))}
    (hΩ : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))))
    {x : EuclideanSpace ℝ (Fin (n + 1))}
    {e : EuclideanSpace ℝ (Fin (n + 1)) ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E)}
    {γ : E → ℝ} {h₀ r₀ : ℝ} {Kγ : ℝ≥0} (hex : e x = 0) (hh₀ : 0 < h₀) (hr₀ : 0 < r₀)
    (hγ0 : γ 0 = 0) (hγ : ContDiff ℝ 1 γ) (hγK : HolderWith Kγ α (fderiv ℝ γ))
    (hgraph : ∀ z ∈ normalCylinder h₀ r₀, (e.symm z ∈ Ω ↔ γ z.snd < z.fst)) (lam Lam M : ℝ) :
    ∃ ρ > 0, ∃ κ : ℝ≥0, ∀ {u : W1p0 volume Ω 2}
      {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
      {G : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))}
      {f h : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} {Ka KG Kh : ℝ≥0},
      UniformlyEllipticOn (closure (Ω : Set _)) a lam Lam →
      HolderOnWith Ka α (fun x => matrixBilinearForm (a x)) (closure (Ω : Set _)) →
      (Ka : ℝ) ≤ M → HolderOnWith KG α G (closure (Ω : Set _)) →
      MemLp f q (volume.restrict (Ω : Set _)) →
      AEStronglyMeasurable h (volume.restrict (Ω : Set _)) →
      morreyNormPow volume Ω 1 (n + α) h ≤ Kh →
      (∀ φ : 𝓓(Ω, ℝ), energyFormH1 a 0 0 (u : W1p volume Ω 2)
          (W1p.ofTestFunctionₗ volume Ω 2 φ) =
        (∫ x in Ω, ⟪G x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ) +
          (∫ x in Ω, f x * φ x) + ∫ x in Ω, h x * φ x) →
      ∃ g : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)),
        (W1p.gradient (u : W1p volume Ω 2) : EuclideanSpace ℝ (Fin (n + 1)) →
          EuclideanSpace ℝ (Fin (n + 1))) =ᵐ[volume.restrict ((Ω : Set _) ∩ ball x ρ)] g ∧
        HolderOnWith (κ * (KG + (eLpNorm f q (volume.restrict (Ω : Set _))).toReal + Kh +
          ‖u‖).toNNReal) β g (ball x ρ ∩ closure (Ω : Set _)) ∧
        ∀ y ∈ ball x ρ ∩ closure (Ω : Set _),
          ‖g y‖ ≤ κ * (KG + (eLpNorm f q (volume.restrict (Ω : Set _))).toReal + Kh + ‖u‖) := by
  have hα : 0 < α := hβ.trans_le hβα
  obtain ⟨C, hC⟩ := exists_holderWith_and_setIntegral_inner_add_gradient_eq (n := n) hα hα1
  obtain ⟨ρ, hρ, κ, H⟩ := exists_holderOnWith_gradient_ball_inter_closure_of_graph hβ
    (hβα.trans_lt hα1) hβα hq hβq hΩ hex hh₀ hr₀ hγ0 hγ hγK hgraph lam Lam M
  refine ⟨ρ, hρ, κ * (1 + C), fun {u a G f h Ka KG Kh} hell hKa hKaM hKG hf hh hhM hu => ?_⟩
  obtain ⟨Hf, hHf, hHeq⟩ := hC hΩ hh hhM
  -- `u` solves the equation with the field `G + H_f` and the scalar datum `f` alone.
  obtain ⟨g, hg, hghol, hgb⟩ := H hell hKa hKaM (hKG.add (hHf.holderOnWith _)) hf fun φ => by
    rw [hHeq (((hKG.continuousOn hα).mono subset_closure).locallyIntegrableOn
      Ω.isOpen.measurableSet), hu φ, add_right_comm]
  have hF := ENNReal.toReal_nonneg (a := eLpNorm f q (volume.restrict (Ω : Set _)))
  have hQ := mul_add_mul_add_add_le κ.coe_nonneg C.coe_nonneg KG.coe_nonneg Kh.coe_nonneg hF
    (norm_nonneg u)
  refine ⟨g, hg, hghol.mono_const ?_, fun y hy => (hgb y hy).trans (by push_cast; exact hQ)⟩
  simp (disch := positivity) only [← NNReal.coe_le_coe, NNReal.coe_mul, Real.coe_toNNReal]
  push_cast
  exact hQ

/-- **The global Schauder estimate with a datum in a Morrey space.** Let `Ω ⊆ ℝ^{n+1}` be a
bounded open set with `C^{1,α}` boundary, `0 < α < 1`, as in
`exists_holderOnWith_gradient_closure_of_isBounded`. Let `0 < β ≤ α`, `2 ≤ q ≤ ∞` and
`β ≤ 1 - (n + 1) / q`, and fix `λ`, `Λ` and `M`. There is a constant `C` such that for every
`u ∈ H¹₀(Ω)` solving `-∂ᵢ(aⁱʲ ∂ⱼu) = f + h - div G` weakly in `Ω`, where on `closure Ω` the
coefficient `a` is uniformly elliptic with constants `λ, Λ` and `α`-Hölder with constant
`K_a ≤ M`, the field `G` is `α`-Hölder with constant `K_G`, `f ∈ L^q(Ω)`, and `h` is
a.e.-strongly measurable on `Ω` with Morrey norm `‖h‖_{L^{1, n + α}(Ω)} ≤ K_h`, the gradient `∇u`
agrees almost everywhere on `Ω` with a function that is `β`-Hölder on `closure Ω` with constant
`C Q` and bounded there by `C Q`, where `Q = K_G + ‖f‖_{L^q(Ω)} + K_h + ‖u‖_{H¹(Ω)}`. The constant
depends only on `Ω`, its charts, `n`, `α`, `β`, `q`, `λ`, `Λ` and `M`.

For `h = 0` this is `exists_holderOnWith_gradient_closure_of_isBounded`; the Morrey datum reaches
the full exponent `β = α`. -/
theorem exists_holderOnWith_gradient_closure_of_isBounded_of_morreyNormPow_le {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] {α β : ℝ≥0} (hβ : 0 < β) (hβα : β ≤ α)
    (hα1 : α < 1) {q : ℝ≥0∞} (hq : 2 ≤ q) (hβq : (β : ℝ) ≤ 1 - ((n : ℝ) + 1) / q.toReal)
    {Ω : Opens (EuclideanSpace ℝ (Fin (n + 1)))}
    (hΩ : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))))
    (hchart : ∀ x ∈ frontier (Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))),
      ∃ (e : EuclideanSpace ℝ (Fin (n + 1)) ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E)) (γ : E → ℝ) (h₀ r₀ : ℝ)
        (Kγ : ℝ≥0), e x = 0 ∧ 0 < h₀ ∧ 0 < r₀ ∧ γ 0 = 0 ∧ ContDiff ℝ 1 γ ∧
        HolderWith Kγ α (fderiv ℝ γ) ∧
        ∀ z ∈ normalCylinder h₀ r₀, (e.symm z ∈ Ω ↔ γ z.snd < z.fst))
    (lam Lam M : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {u : W1p0 volume Ω 2}
      {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
      {G : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))}
      {f h : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} {Ka KG Kh : ℝ≥0},
      UniformlyEllipticOn (closure (Ω : Set _)) a lam Lam →
      HolderOnWith Ka α (fun x => matrixBilinearForm (a x)) (closure (Ω : Set _)) →
      (Ka : ℝ) ≤ M → HolderOnWith KG α G (closure (Ω : Set _)) →
      MemLp f q (volume.restrict (Ω : Set _)) →
      AEStronglyMeasurable h (volume.restrict (Ω : Set _)) →
      morreyNormPow volume Ω 1 (n + α) h ≤ Kh →
      (∀ φ : 𝓓(Ω, ℝ), energyFormH1 a 0 0 (u : W1p volume Ω 2)
          (W1p.ofTestFunctionₗ volume Ω 2 φ) =
        (∫ x in Ω, ⟪G x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ) +
          (∫ x in Ω, f x * φ x) + ∫ x in Ω, h x * φ x) →
      ∃ g : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)),
        (W1p.gradient (u : W1p volume Ω 2) : EuclideanSpace ℝ (Fin (n + 1)) →
          EuclideanSpace ℝ (Fin (n + 1))) =ᵐ[volume.restrict (Ω : Set _)] g ∧
        HolderOnWith (C * (KG + (eLpNorm f q (volume.restrict (Ω : Set _))).toReal + Kh +
          ‖u‖)).toNNReal β g (closure (Ω : Set _)) ∧
        ∀ y ∈ closure (Ω : Set _),
          ‖g y‖ ≤ C * (KG + (eLpNorm f q (volume.restrict (Ω : Set _))).toReal + Kh + ‖u‖) := by
  have hα : 0 < α := hβ.trans_le hβα
  obtain ⟨C, hC⟩ := exists_holderWith_and_setIntegral_inner_add_gradient_eq (n := n) hα hα1
  obtain ⟨A, hA, H⟩ := exists_holderOnWith_gradient_closure_of_isBounded hβ (hβα.trans_lt hα1)
    hβα hq hβq hΩ hchart lam Lam M
  refine ⟨A * (1 + C), by positivity,
    fun {u a G f h Ka KG Kh} hell hKa hKaM hKG hf hh hhM hu => ?_⟩
  obtain ⟨Hf, hHf, hHeq⟩ := hC hΩ hh hhM
  -- `u` solves the equation with the field `G + H_f` and the scalar datum `f` alone.
  obtain ⟨g, hg, hghol, hgb⟩ := H hell hKa hKaM (hKG.add (hHf.holderOnWith _)) hf fun φ => by
    rw [hHeq (((hKG.continuousOn hα).mono subset_closure).locallyIntegrableOn
      Ω.isOpen.measurableSet), hu φ, add_right_comm]
  have hQ := mul_add_mul_add_add_le hA C.coe_nonneg KG.coe_nonneg Kh.coe_nonneg
    (ENNReal.toReal_nonneg (a := eLpNorm f q (volume.restrict (Ω : Set _))))
    (norm_nonneg u)
  refine ⟨g, hg, hghol.mono_const (Real.toNNReal_le_toNNReal ?_), fun y hy =>
    (hgb y hy).trans ?_⟩ <;> push_cast <;> exact hQ

end PDE

end TauCeti
