/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Regularity.MeyersExample
public import TauCeti.Analysis.Sobolev.W1p.PreciseRepresentative

/-!
# The exponent in De Giorgi's theorem degenerates with the ellipticity ratio

De Giorgi's theorem (`TauCeti.PDE.exists_holderOnWith_preciseRepresentative`) gives an exponent
`α ∈ (0, 1]`, depending only on the dimension and the ellipticity constants `λ ≤ Λ`, such that
every weak solution of `-∂ᵢ(aⁱʲ ∂ⱼu) = 0` with measurable coefficients, uniformly elliptic with
constants `λ, Λ`, is locally `α`-Hölder. This file shows that in the plane every such exponent
satisfies

`α ≤ √(λ / Λ)`,

so it tends to `0` as the ellipticity ratio `Λ / λ` tends to infinity.

The witness is Meyers' example (`TauCeti.Analysis.PDE.Regularity.MeyersExample`). For
`0 < μ ≤ 1` the coefficient field `a = TauCeti.PDE.meyersCoefficient μ`, which in polar
coordinates is `e_r ⊗ e_r + μ² e_θ ⊗ e_θ`, is uniformly elliptic with constants `μ²` and `1`, and
`u(x) = ‖x‖ ^ (μ - 1) x₀`, which is `r^μ cos θ`, is a weak solution of `div(a ∇u) = 0` lying in
`H¹` of every bounded open set. It is `μ`-Hölder (`TauCeti.PDE.holderWith_meyersSolution`) and no
better at the origin (`TauCeti.PDE.not_holderOnWith_meyersSolution`). Taking `μ = √(λ / Λ)` and
the field `Λ a`, whose constants are `Λ μ² = λ` and `Λ`, gives a solution whose precise
representative is not `α`-Hölder near the origin for any `α > √(λ / Λ)`.

## Main declarations

* `TauCeti.PDE.le_sqrt_div_of_forall_exists_holderOnWith`: if, on a bounded open set `Ω ⊆ ℝ²`
  containing the origin, every weak solution with measurable coefficients, uniformly elliptic
  with constants `λ, Λ`, has a precise representative that is `α`-Hölder on a fixed
  neighbourhood of the origin, then `α ≤ √(λ / Λ)`.
* `TauCeti.PDE.le_sqrt_div_of_forall_holderOnWith_preciseRepresentative`: the same bound for every
  exponent with the property stated by De Giorgi's theorem in the plane.

## References

* N. G. Meyers, *An `Lᵖ`-estimate for the gradient of solutions of second order elliptic
  divergence equations*, Ann. Scuola Norm. Sup. Pisa (3) 17 (1963), 189–206, §5 (the coefficient
  field and the solution).
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
`0 < λ ≤ Λ`, let `Ω ⊆ ℝ²` be a bounded open set containing the origin and let `s` be a
neighbourhood of the origin. Suppose that for every measurable coefficient field `a`, uniformly
elliptic on `Ω` with constants `λ, Λ`, every weak solution `u ∈ H¹(Ω)` of `-∂ᵢ(aⁱʲ ∂ⱼu) = 0` on
`Ω` has a precise representative that is `α`-Hölder on `s`, with some constant. Then
`α ≤ √(λ / Λ)`.

The witness is Meyers' solution for the field `Λ a` with
`a = TauCeti.PDE.meyersCoefficient √(λ / Λ)`. It is itself `√(λ / Λ)`-Hölder
(`TauCeti.PDE.holderWith_meyersSolution`), so this example yields no smaller bound. -/
theorem le_sqrt_div_of_forall_exists_holderOnWith {lam Lam : ℝ} (hlam : 0 < lam)
    (hLam : lam ≤ Lam) {Ω : Opens (EuclideanSpace ℝ (Fin 2))}
    (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin 2))))
    (h0 : (0 : EuclideanSpace ℝ (Fin 2)) ∈ Ω) {s : Set (EuclideanSpace ℝ (Fin 2))}
    (hs : s ∈ 𝓝 0) {α : ℝ≥0}
    (h : ∀ (a : EuclideanSpace ℝ (Fin 2) → Matrix (Fin 2) (Fin 2) ℝ) (u : W1p volume Ω 2),
      UniformlyEllipticOn (Ω : Set (EuclideanSpace ℝ (Fin 2))) a lam Lam →
      AEStronglyMeasurable a (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin 2)))) →
      (∀ v : W1p0 volume Ω 2, energyFormH1 a 0 0 u (v : W1p volume Ω 2) = 0) →
      ∃ C, HolderOnWith C α (preciseRepresentative volume (W1p.value u)) s) :
    (α : ℝ) ≤ √(lam / Lam) := by
  have hLam0 : 0 < Lam := hlam.trans_le hLam
  set μ := √(lam / Lam) with hμ
  have hμ0 : 0 < μ := Real.sqrt_pos.2 (div_pos hlam hLam0)
  have hμ1 : μ ≤ 1 := Real.sqrt_le_one.2 ((div_le_one hLam0).2 hLam)
  -- Meyers' solution for the field `Λ a`, uniformly elliptic with constants `Λ μ² = λ` and `Λ`.
  obtain ⟨u, hu⟩ := exists_w1p_value_ae_eq_meyersSolution hμ0 (p := 2) (by norm_num) hb
    (by simp only [ENNReal.toReal_ofNat]; linarith)
  have hell : UniformlyEllipticOn (Ω : Set (EuclideanSpace ℝ (Fin 2)))
      (Lam • meyersCoefficient μ) lam Lam := by
    have := (uniformlyEllipticOn_meyersCoefficient hμ0 hμ1
      (Ω : Set (EuclideanSpace ℝ (Fin 2)))).const_smul hLam0
    rwa [hμ, Real.sq_sqrt (div_pos hlam hLam0).le, mul_div_cancel₀ _ hLam0.ne', mul_one] at this
  have hsol : ∀ v : W1p0 volume Ω 2,
      energyFormH1 (Lam • meyersCoefficient μ) 0 0 u (v : W1p volume Ω 2) = 0 := fun v => by
    have := energyFormH1_smul_coefficients (meyersCoefficient μ) 0 0 Lam u (v : W1p volume Ω 2)
    rw [smul_zero, smul_zero] at this
    rw [this, energyFormH1_meyersCoefficient_eq_zero hμ0 u hu v, mul_zero]
  obtain ⟨C, hC⟩ := h _ u hell
    (stronglyMeasurable_meyersCoefficient.const_smul Lam).aestronglyMeasurable hsol
  -- On `Ω` the precise representative is Meyers' solution itself, which is continuous.
  have heq : EqOn (preciseRepresentative volume (W1p.value u)) (meyersSolution μ) Ω :=
    eqOn_preciseRepresentative_of_continuousOn Ω.isOpen
      (W1p.hasWeakFDerivOn u).locallyIntegrableOn hu (continuous_meyersSolution hμ0).continuousOn
  have hC' : HolderOnWith C α (meyersSolution μ) (s ∩ Ω) := fun x hx y hy => by
    rw [← heq hx.2, ← heq hy.2]
    exact hC x hx.1 y hy.1
  by_contra hα
  exact not_holderOnWith_meyersSolution (not_le.1 hα) C
    (Filter.inter_mem hs (Ω.isOpen.mem_nhds h0)) hC'

/-- **The exponent of De Giorgi's theorem in the plane is at most `√(λ / Λ)`.** Let `0 < λ ≤ Λ`.
If `α` and `C` have the property stated by De Giorgi's theorem
(`TauCeti.PDE.exists_holderOnWith_preciseRepresentative`) for Lebesgue measure on `ℝ²`, namely
that for every open `Ω`, every measurable `a` uniformly elliptic on `Ω` with constants `λ, Λ` and
every weak solution `u ∈ H¹(Ω)` of `-∂ᵢ(aⁱʲ ∂ⱼu) = 0`, the precise representative of `u` is
`α`-Hölder with constant `C R^(-α - 1) ‖u‖_{L²(Ω)}` on every `K` whose closed `R`-thickening lies
in `Ω`, then `α ≤ √(λ / Λ)`. -/
theorem le_sqrt_div_of_forall_holderOnWith_preciseRepresentative {lam Lam : ℝ} (hlam : 0 < lam)
    (hLam : lam ≤ Lam) {α : ℝ≥0} {C : ℝ}
    (h : ∀ {Omega : Opens (EuclideanSpace ℝ (Fin 2))}
      {a : EuclideanSpace ℝ (Fin 2) → Matrix (Fin 2) (Fin 2) ℝ} {u : W1p volume Omega 2}
      {K : Set (EuclideanSpace ℝ (Fin 2))} {R : ℝ},
      UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ (Fin 2))) a lam Lam →
      AEStronglyMeasurable a (volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin 2)))) →
      (∀ v : W1p0 volume Omega 2, energyFormH1 a 0 0 u (v : W1p volume Omega 2) = 0) →
      0 < R → cthickening R K ⊆ (Omega : Set (EuclideanSpace ℝ (Fin 2))) →
        HolderOnWith (C * R ^ (-(α : ℝ)) * (R ^ (-(Fintype.card (Fin 2) : ℝ) / 2) *
          √(∫ y in Omega, W1p.value u y ^ 2))).toNNReal α
          (preciseRepresentative volume (W1p.value u)) K) :
    (α : ℝ) ≤ √(lam / Lam) := by
  -- Apply the local form on `Ω = B(0, 2)` with `K` the closed ball of radius `1 / 2` and `R = 1`.
  let Ω : Opens (EuclideanSpace ℝ (Fin 2)) := ⟨ball 0 2, isOpen_ball⟩
  refine le_sqrt_div_of_forall_exists_holderOnWith hlam hLam (Ω := Ω) isBounded_ball
    (mem_ball_self two_pos) (closedBall_mem_nhds 0 (by norm_num : (0 : ℝ) < 1 / 2))
    fun a u ha ham hu => ⟨_, h ha ham hu one_pos ?_⟩
  rw [cthickening_closedBall zero_le_one (by norm_num)]
  exact closedBall_subset_ball (by norm_num)

end PDE

end TauCeti
