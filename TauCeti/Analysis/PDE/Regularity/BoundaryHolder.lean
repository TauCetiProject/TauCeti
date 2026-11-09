/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.EnergyForm.HyperplaneReflection
public import TauCeti.Analysis.PDE.Regularity.HolderContinuity

/-!
# De Giorgi's Hölder estimate up to a flat boundary

Let `H = {x | c₀ < ⟪x, ν⟫}` be an open half-space in `ℝⁿ`, `n ≥ 1`, let `ρ` be the reflection in
its boundary hyperplane, and let `U` be an open set with `ρ U ⊆ U`, such as a ball centred on the
hyperplane. Let `a` be measurable and uniformly elliptic with constants `λ, Λ` on the part of `U`
in the closed half-space, and let `u ∈ H¹(U)` vanish on `U ∖ H` and solve

`-∂ᵢ(aⁱʲ ∂ⱼu) = 0` in `U ∩ H`

weakly. So `u` is a weak solution on `U ∩ H` with zero boundary values on the flat part
`U ∩ ∂H` of the boundary. This file proves that `u` is Hölder continuous up to that flat part,
with De Giorgi's exponent `α` and constants depending only on `λ`, `Λ`, the dimension and the
normalization of the Haar measure
(`TauCeti.PDE.exists_holderOnWith_preciseRepresentative_sub_compHyperplaneReflectionL`).

More precisely, the precise representative of the odd reflection `w = u - u ∘ ρ` is `α`-Hölder on
every set `K` whose closed `R`-thickening lies in `U`, with constant
`C R^(-α - n/2) ‖w‖_{L²(U)}`, and `w` agrees with `u` on `U ∩ H`
(`TauCeti.W1p.value_sub_compHyperplaneReflectionL_ae`). The set `K` may meet the hyperplane: this
is a boundary estimate, not an interior one.

## The argument

By the reflection principle for divergence-form equations
(`TauCeti.PDE.energyFormH1_reflectPrincipal_sub_compHyperplaneReflectionL`), `w` is a weak
solution on all of `U` of `-∂ᵢ(a'ⁱʲ ∂ⱼw) = 0` with the reflected coefficient `a'`, which is
measurable and uniformly elliptic with the same constants `λ, Λ`
(`TauCeti.PDE.UniformlyEllipticOn.reflectPrincipal`). De Giorgi's interior theorem
(`TauCeti.PDE.exists_holderOnWith_preciseRepresentative`) applies to `w` on `U`, and the
reflected coefficient is merely measurable, which is all that theorem needs.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Theorem 8.29 (global Hölder estimates for weak solutions).
* E. De Giorgi, *Sulla differenziabilità e l'analiticità delle estremali degli integrali multipli
  regolari*, Mem. Accad. Sci. Torino 3 (1957), 25–43.
-/

public section

noncomputable section

open MeasureTheory Set TopologicalSpace InnerProductSpace TauCeti.MeasureTheory
open scoped NNReal

namespace TauCeti

namespace PDE

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {mu : Measure (EuclideanSpace ℝ ι)}
  [mu.IsAddHaarMeasure] {lam Lam : ℝ}

/-- **De Giorgi's theorem up to a flat boundary.** Let `n ≥ 1` be the dimension. There are
`α ∈ (0, 1]` and `C > 0`, depending only on `λ`, `Λ`, the dimension and the normalization of the
additive Haar measure `mu`, such that the following holds. Let `H = {x | c₀ < ⟪x, ν⟫}` with
`ν ≠ 0`, let `ρ` be the reflection in the hyperplane `∂H` and let `U` be open with `ρ U ⊆ U`. Let
`a` be measurable on `U ∩ H` and uniformly elliptic with constants `λ, Λ` on the part of `U` in
the closed half-space `{x | c₀ ≤ ⟪x, ν⟫}`. Let `u ∈ H¹(U)` vanish on `U ∖ H` and let its
restriction to `U ∩ H` be a weak solution of `-∂ᵢ(aⁱʲ ∂ⱼu) = 0`. If the closed `R`-thickening of
a set `K` lies in `U`, then the precise representative of the odd reflection `w = u - u ∘ ρ`,
which agrees with `u` on `U ∩ H`, is Hölder continuous on `K` with exponent `α` and constant
`C R^(-α - n/2) ‖w‖_{L²(U)}`. -/
theorem exists_holderOnWith_preciseRepresentative_sub_compHyperplaneReflectionL [Nonempty ι] :
    ∃ (α : ℝ≥0) (C : ℝ), 0 < α ∧ α ≤ 1 ∧ 0 < C ∧ ∀ {U H : Opens (EuclideanSpace ℝ ι)}
      {ν : EuclideanSpace ℝ ι} {c₀ : ℝ} {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ}
      {u : W1p mu U 2} {K : Set (EuclideanSpace ℝ ι)} {R : ℝ}, ν ≠ 0 →
      (∀ x, x ∈ H ↔ c₀ < ⟪x, ν⟫_ℝ) → ∀ hU : MapsTo (hyperplaneReflection ν c₀) U U,
      UniformlyEllipticOn {x | x ∈ U ∧ c₀ ≤ ⟪x, ν⟫_ℝ} a lam Lam →
      AEStronglyMeasurable a (mu.restrict (U ⊓ H)) →
      (∀ᵐ x ∂mu.restrict U, x ∉ H → W1p.value u x = 0) →
      (∀ v : W1p0 mu (U ⊓ H) 2,
        energyFormH1 a 0 0 (W1p.restrictL (inf_le_left : U ⊓ H ≤ U) u)
          (v : W1p mu (U ⊓ H) 2) = 0) →
      0 < R → Metric.cthickening R K ⊆ (U : Set (EuclideanSpace ℝ ι)) →
        HolderOnWith (C * R ^ (-(α : ℝ)) * (R ^ (-(Fintype.card ι : ℝ) / 2) *
          √(∫ y in U, W1p.value (u - W1p.compHyperplaneReflectionL ENNReal.ofNat_ne_top ν c₀ hU
            u) y ^ 2 ∂mu))).toNNReal α
          (preciseRepresentative mu
            (W1p.value (u - W1p.compHyperplaneReflectionL ENNReal.ofNat_ne_top ν c₀ hU u))) K := by
  obtain ⟨α, C, hα, hα1, hC, hhol⟩ :=
    exists_holderOnWith_preciseRepresentative (mu := mu) (lam := lam) (Lam := Lam) (ι := ι)
  refine ⟨α, C, hα, hα1, hC, fun {U H ν c₀ a u K R} hν hH hU ha ham hu0 hu hR hRK => ?_⟩
  have ha' : UniformlyEllipticOn (U : Set (EuclideanSpace ℝ ι)) (reflectPrincipal ν c₀ a) lam
      Lam := ha.reflectPrincipal hν hU
  have ham' := aestronglyMeasurable_reflectPrincipal hν hH hU ham
  -- The reflected coefficients are bounded on `U`.
  have hcoeff : MemLp (fun x => energyIntegrand (reflectPrincipal ν c₀ a x)
      (reflectDrift ν c₀ (0 : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι) x)
      (reflectDensity ν c₀ (0 : EuclideanSpace ℝ ι → ℝ) x)) ⊤ (mu.restrict U) := by
    simp only [reflectDrift_zero, reflectDensity_zero]
    exact memLp_energyIntegrand_of_bounds (beta := 0) (gamma := 0)
      ((uniformlyEllipticOn_iff.1 ha').1.le.trans (uniformlyEllipticOn_iff.1 ha').2.1) ham'
      aestronglyMeasurable_const aestronglyMeasurable_const
      (fun x hx => ((uniformlyEllipticOn_iff.1 ha').2.2 hx).2) (fun _ _ => by simp)
      (fun _ _ => by simp)
  refine hhol ha' ham' (fun φ => ?_) hR hRK
  have h := energyFormH1_reflectPrincipal_sub_compHyperplaneReflectionL hν hH hU hcoeff hu0
    (ℓ := 0) (fun v => by rw [zero_apply]; exact hu v) φ
  rwa [reflectDrift_zero, reflectDensity_zero] at h

end PDE

end TauCeti
