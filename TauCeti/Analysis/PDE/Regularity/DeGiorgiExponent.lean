/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Regularity.Meyers.Example
public import TauCeti.Analysis.Sobolev.W1p.PreciseRepresentative

/-!
# The exponent in De Giorgi's theorem degenerates with the ellipticity ratio

De Giorgi's theorem (`TauCeti.PDE.exists_holderOnWith_preciseRepresentative`) gives an exponent
`α ∈ (0, 1]`, depending only on the dimension and the ellipticity constants `λ ≤ Λ`, such that
every weak solution of `-∂ᵢ(aⁱʲ ∂ⱼu) = 0` with measurable coefficients, uniformly elliptic with
constants `λ, Λ`, is locally `α`-Hölder. This file shows that in dimension `n + 2 ≥ 2` every such
exponent satisfies

`α (α + n) ≤ (n + 1) λ / Λ`.

In particular `α ≤ √((n + 1) λ / Λ)`, and for `n ≥ 1` also `α ≤ (n + 1) λ / (n Λ)`, so in every
dimension `α` tends to `0` as the ellipticity ratio `Λ / λ` tends to infinity. In the plane,
`n = 0`, the bound reads `α ≤ √(λ / Λ)`.

The witness is Meyers' example (`TauCeti.Analysis.PDE.Regularity.Meyers.Example`). For
`0 < μ ≤ 1` the coefficient field `a = TauCeti.PDE.meyersCoefficient μ` on `ℝ^{n+2}`, with
eigenvalue `1` in the radial direction and `κ = μ (μ + n) / (n + 1)` in the tangential directions,
is uniformly elliptic with constants `κ` and `1`, and `u(x) = ‖x‖ ^ (μ - 1) x₀` is a weak solution
of `div(a ∇u) = 0` lying in `H¹` of every bounded open set. It is `μ`-Hölder
(`TauCeti.PDE.holderWith_meyersSolution`) and no better at the origin
(`TauCeti.PDE.not_holderOnWith_meyersSolution`). Taking for `μ` the positive root of
`μ (μ + n) = (n + 1) λ / Λ` and the field `Λ a`, whose constants are `Λ κ = λ` and `Λ`, gives a
solution whose precise representative is not `α`-Hölder near the origin for any `α > μ`.

## Main declarations

* `TauCeti.PDE.mul_add_le_mul_div_of_forall_exists_holderOnWith`: if, on a bounded open set
  `Ω ⊆ ℝ^{n+2}` containing the origin, every weak solution with measurable coefficients, uniformly
  elliptic with constants `λ, Λ`, has a precise representative that is `α`-Hölder on a fixed
  neighbourhood of the origin, then `α (α + n) ≤ (n + 1) λ / Λ`.
* `TauCeti.PDE.mul_add_le_mul_div_of_forall_holderOnWith_preciseRepresentative`: the same bound
  for every exponent with the property stated by De Giorgi's theorem in `ℝ^{n+2}`.

## References

* N. G. Meyers, *An `Lᵖ`-estimate for the gradient of solutions of second order elliptic
  divergence equations*, Ann. Scuola Norm. Sup. Pisa (3) 17 (1963), 189–206, §5 (the coefficient
  field and the solution in the plane).
* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Theorem 8.22 (De Giorgi's theorem).
-/

public section

noncomputable section

open MeasureTheory Metric Set TopologicalSpace TauCeti.MeasureTheory
open scoped NNReal ENNReal Topology

namespace TauCeti

namespace PDE

/-- **The exponent in De Giorgi's theorem degenerates with the ellipticity ratio.** Let
`0 < λ ≤ Λ`, let `Ω ⊆ ℝ^{n+2}` be a bounded open set containing the origin and let `s` be a
neighbourhood of the origin. Suppose that for every measurable coefficient field `a`, uniformly
elliptic on `Ω` with constants `λ, Λ`, every weak solution `u ∈ H¹(Ω)` of `-∂ᵢ(aⁱʲ ∂ⱼu) = 0` on
`Ω` has a precise representative that is `α`-Hölder on `s`, with some constant. Then
`α (α + n) ≤ (n + 1) λ / Λ`; in the plane this is `α ≤ √(λ / Λ)`.

The witness is Meyers' solution for the field `Λ a` with `a = TauCeti.PDE.meyersCoefficient μ`
and `μ (μ + n) = (n + 1) λ / Λ`. It is itself `μ`-Hölder
(`TauCeti.PDE.holderWith_meyersSolution`), so this example yields no smaller bound. -/
theorem mul_add_le_mul_div_of_forall_exists_holderOnWith {n : ℕ} {lam Lam : ℝ} (hlam : 0 < lam)
    (hLam : lam ≤ Lam) {Ω : Opens (EuclideanSpace ℝ (Fin (n + 2)))}
    (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin (n + 2)))))
    (h0 : (0 : EuclideanSpace ℝ (Fin (n + 2))) ∈ Ω) {s : Set (EuclideanSpace ℝ (Fin (n + 2)))}
    (hs : s ∈ 𝓝 0) {α : ℝ≥0}
    (h : ∀ (a : EuclideanSpace ℝ (Fin (n + 2)) → Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ)
      (u : W1p volume Ω 2),
      UniformlyEllipticOn (Ω : Set (EuclideanSpace ℝ (Fin (n + 2)))) a lam Lam →
      AEStronglyMeasurable a (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (n + 2))))) →
      (∀ v : W1p0 volume Ω 2, energyFormH1 a 0 0 u (v : W1p volume Ω 2) = 0) →
      ∃ C, HolderOnWith C α (preciseRepresentative volume (W1p.value u)) s) :
    (α : ℝ) * (α + n) ≤ (n + 1) * (lam / Lam) := by
  have hLam0 : 0 < Lam := hlam.trans_le hLam
  obtain ⟨μ, hμ0, -, hμ⟩ := exists_meyersEigenvalue_eq (n := n) (div_pos hlam hLam0)
    ((div_le_one hLam0).2 hLam)
  -- Meyers' solution for the field `Λ a`, uniformly elliptic with constants `Λ κ = λ` and `Λ`.
  obtain ⟨u, hu⟩ := exists_w1p_value_ae_eq_meyersSolution hμ0 (p := 2) (by norm_num) hb
    (by simp only [ENNReal.toReal_ofNat]; nlinarith)
  obtain ⟨C, hC⟩ := h _ u (uniformlyEllipticOn_smul_meyersCoefficient hμ0 hlam hLam hμ _)
    (stronglyMeasurable_meyersCoefficient.const_smul Lam).aestronglyMeasurable
    (energyFormH1_smul_meyersCoefficient_eq_zero hμ0 Lam u hu)
  -- On `Ω` the precise representative is Meyers' solution itself, which is continuous.
  have heq : EqOn (preciseRepresentative volume (W1p.value u)) (meyersSolution μ) Ω :=
    eqOn_preciseRepresentative_of_continuousOn Ω.isOpen
      (W1p.hasWeakFDerivOn u).locallyIntegrableOn hu (continuous_meyersSolution hμ0).continuousOn
  have hC' : HolderOnWith C α (meyersSolution μ) (s ∩ Ω) := fun x hx y hy => by
    rw [← heq hx.2, ← heq hy.2]
    exact hC x hx.1 y hy.1
  -- So `α ≤ μ`, and `t ↦ t (t + n)` is monotone on `t ≥ 0`.
  have hαμ : (α : ℝ) ≤ μ := by
    by_contra hα
    exact not_holderOnWith_meyersSolution (not_le.1 hα) C
      (Filter.inter_mem hs (Ω.isOpen.mem_nhds h0)) hC'
  rw [← meyersEigenvalue_eq_iff.1 hμ]
  exact mul_le_mul hαμ (by linarith) (by positivity) hμ0.le

/-- **The exponent of De Giorgi's theorem in `ℝ^{n+2}` satisfies `α (α + n) ≤ (n + 1) λ / Λ`.**
Let `0 < λ ≤ Λ`. If `α` and `C` have the property stated by De Giorgi's theorem
(`TauCeti.PDE.exists_holderOnWith_preciseRepresentative`) for Lebesgue measure on `ℝ^{n+2}`,
namely that for every open `Ω`, every measurable `a` uniformly elliptic on `Ω` with constants
`λ, Λ` and every weak solution `u ∈ H¹(Ω)` of `-∂ᵢ(aⁱʲ ∂ⱼu) = 0`, the precise representative of
`u` is `α`-Hölder with constant `C R^(-α - (n + 2) / 2) ‖u‖_{L²(Ω)}` on every `K` whose closed
`R`-thickening lies in `Ω`, then `α (α + n) ≤ (n + 1) λ / Λ`. So `α` tends to `0` as `Λ / λ`
tends to infinity; in the plane the bound is `α ≤ √(λ / Λ)`. -/
theorem mul_add_le_mul_div_of_forall_holderOnWith_preciseRepresentative {n : ℕ} {lam Lam : ℝ}
    (hlam : 0 < lam) (hLam : lam ≤ Lam) {α : ℝ≥0} {C : ℝ}
    (h : ∀ {Omega : Opens (EuclideanSpace ℝ (Fin (n + 2)))}
      {a : EuclideanSpace ℝ (Fin (n + 2)) → Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ}
      {u : W1p volume Omega 2} {K : Set (EuclideanSpace ℝ (Fin (n + 2)))} {R : ℝ},
      UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ (Fin (n + 2)))) a lam Lam →
      AEStronglyMeasurable a (volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin (n + 2))))) →
      (∀ v : W1p0 volume Omega 2, energyFormH1 a 0 0 u (v : W1p volume Omega 2) = 0) →
      0 < R → cthickening R K ⊆ (Omega : Set (EuclideanSpace ℝ (Fin (n + 2)))) →
        HolderOnWith (C * R ^ (-(α : ℝ)) * (R ^ (-(Fintype.card (Fin (n + 2)) : ℝ) / 2) *
          √(∫ y in Omega, W1p.value u y ^ 2))).toNNReal α
          (preciseRepresentative volume (W1p.value u)) K) :
    (α : ℝ) * (α + n) ≤ (n + 1) * (lam / Lam) := by
  -- Apply the local form on `Ω = B(0, 2)` with `K` the closed ball of radius `1 / 2` and `R = 1`.
  let Ω : Opens (EuclideanSpace ℝ (Fin (n + 2))) := ⟨ball 0 2, isOpen_ball⟩
  refine mul_add_le_mul_div_of_forall_exists_holderOnWith hlam hLam (Ω := Ω) isBounded_ball
    (mem_ball_self two_pos) (closedBall_mem_nhds 0 (by norm_num : (0 : ℝ) < 1 / 2))
    fun a u ha ham hu => ⟨_, h ha ham hu one_pos ?_⟩
  rw [cthickening_closedBall zero_le_one (by norm_num)]
  exact closedBall_subset_ball (by norm_num)

end PDE

end TauCeti
