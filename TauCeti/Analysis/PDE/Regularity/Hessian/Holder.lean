/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Regularity.GradientHolder
public import TauCeti.Analysis.PDE.Regularity.HigherOrder

/-!
# Hölder continuity of the second derivatives for `-Δu = f`

Let `u ∈ H¹(Ω)` be a weak solution of Poisson's equation `-Δu = f` in an open set
`Ω ⊆ ℝ^{n+1}`, with `f ∈ L²(Ω)`, and let `0 < α < 1`. This file proves that the second derivatives
of `u` are as regular as `f` in the interior: if `f` is `α`-Hölder with constant `K` on the open
`R`-thickening `S_R` of a set `S`, and `S_R` lies in an open `V` whose closure is compact and
contained in `Ω`, then for every direction `e` the weak derivative `∂ₑu ∈ H¹(V)` has a gradient
whose precise representative is `α`-Hölder on `S`, with constant

`C (‖e‖ K + R^{-(n+1)/2-α} ‖∇∂ₑu‖_{L²(V)})`,

where `C` depends only on `n` and `α`, and `‖∇∂ₑu‖_{L²(V)}` is finite by interior `H²`
regularity. Applied along an orthonormal basis, this says that the second derivatives of `u` are
`α`-Hölder on `S`: the interior `C^{2,α}` regularity of Poisson's equation with Hölder data.

## Differentiating the equation

Interior `H²` regularity (`TauCeti.PDE.UniformlyEllipticOn.exists_lowerOrder_eq_restrictL`) puts
`u` in `H²(V)`, so `w = ∂ₑu` lies in `H¹(V)`. The data `f` need not be weakly differentiable, so
`w` is not a weak solution of `-Δw = ∂ₑf`; instead the derivative is kept on the test function.
For a test function `φ` on `V`, moving `∂ₑ` across the energy form
(`TauCeti.PDE.energyFormH1_ofTestFunctionₗ_eq_neg_of_hasWeakLineDerivOn`) and using the equation
for `u` against `∂ₑφ` gives

`∫_V ⟨∇w, ∇φ⟩ = -∫_V ⟨∇u, ∇∂ₑφ⟩ = -∫_V f ∂ₑφ = ∫_V ⟨-f e, ∇φ⟩`,

so `w` solves `-Δw = -div G` in `V` with the field `G = -f e`, which is `α`-Hölder on `S_R` with
constant `‖e‖ K`. The interior Hölder estimate for the gradient
(`TauCeti.PDE.exists_holderOnWith_preciseRepresentative_gradient`) then applies to `w`.

## Main declarations

* `TauCeti.PDE.exists_hasWeakLineDerivOn_and_holderOnWith_preciseRepresentative_gradient`: the
  interior Hölder estimate for the second derivatives of a weak solution of `-Δu = f`.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Theorem 4.6.
* M. Giaquinta, L. Martinazzi, *An Introduction to the Regularity Theory for Elliptic Systems,
  Harmonic Maps and Minimal Graphs*, 2nd ed., Chapter 5.
-/

public section

open InnerProductSpace LineDeriv MeasureTheory Metric Set TopologicalSpace TauCeti.MeasureTheory
open scoped Distributions Gradient InnerProductSpace NNReal

namespace TauCeti

namespace PDE

variable {n : ℕ}

/-- **Interior Hölder continuity of the second derivatives for `-Δu = f`.** Let `0 < α < 1`.
There is a constant `C`, depending only on `n` and `α`, such that the following holds. Let
`Ω ⊆ ℝ^{n+1}` be open, `f ∈ L²(Ω)`, and let `u ∈ H¹(Ω)` be a weak solution of `-Δu = f` in `Ω`,
that is `∫_Ω ⟨∇u, ∇v⟩ = ∫_Ω f v` for every `v ∈ H¹₀(Ω)`. Let `V` be open with compact closure
contained in `Ω`, and suppose that the open `R`-thickening of `S` lies in `V` and that `f` is
`α`-Hölder there with constant `K`. Then for every direction `e`, the weak derivative `∂ₑu` lies
in `H¹(V)`, and the precise representative of its gradient is `α`-Hölder on `S`, with constant
`C (‖e‖ K + R^{-(n+1)/2-α} ‖∇∂ₑu‖_{L²(V)})`.

No boundary condition is imposed on `u` and nothing is assumed about `∂Ω`. The precise
representative agrees with `∇∂ₑu` almost everywhere on `V`
(`TauCeti.MeasureTheory.ae_eq_restrict_preciseRepresentative`). -/
theorem exists_hasWeakLineDerivOn_and_holderOnWith_preciseRepresentative_gradient {α : ℝ≥0}
    (hα : 0 < α) (hα1 : α < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Omega V : Opens (EuclideanSpace ℝ (Fin (n + 1)))}
      {u : W1p volume Omega 2} {f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} {K : ℝ≥0}
      {S : Set (EuclideanSpace ℝ (Fin (n + 1)))} {R : ℝ},
      MemLp f 2 (volume.restrict Omega) →
      (∀ v : W1p0 volume Omega 2, energyFormH1 (fun _ => 1) 0 0 u (v : W1p volume Omega 2) =
        ∫ x in Omega, f x * W1p.value (v : W1p volume Omega 2) x) →
      IsCompact (closure (V : Set (EuclideanSpace ℝ (Fin (n + 1))))) →
      closure (V : Set (EuclideanSpace ℝ (Fin (n + 1)))) ⊆ Omega →
      HolderOnWith K α f (thickening R S) → 0 < R → thickening R S ⊆ V →
      ∀ e : EuclideanSpace ℝ (Fin (n + 1)), ∃ d : W1p volume V 2,
        HasWeakLineDerivOn volume V (W1p.value u) (W1p.value d) e ∧
        HolderOnWith
          (C * (‖e‖ * K + R ^ (-(((n : ℝ) + 1) / 2 + α)) * ‖W1p.gradient d‖)).toNNReal α
          (preciseRepresentative volume
            (W1p.gradient d : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))))
          S := by
  obtain ⟨C, hC, hgrad⟩ := exists_holderOnWith_preciseRepresentative_gradient hα hα1 (n := n)
  refine ⟨C, hC, fun {Omega V u f K S R} hf hu hV hVΩ hfK hR hSV e => ?_⟩
  have hA : ∀ ξ : EuclideanSpace ℝ (Fin (n + 1)),
      1 * ‖ξ‖ ^ 2 ≤ dotProduct ξ (Matrix.mulVec (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) ξ) :=
    fun ξ => by rw [one_mul, ← toQuadraticForm'_one, Matrix.toQuadraticForm'_apply]
  obtain ⟨d, hd, hdeq⟩ :=
    UniformlyEllipticOn.exists_hasWeakLineDerivOn_and_energyFormH1_eq_neg_setIntegral one_pos hA
      hf hu hV hVΩ e
  refine ⟨d, hd, ?_⟩
  -- `d = ∂ₑu` solves `-Δd = -div G` in `V`, with `G = -f e`, which is Hölder on the thickening.
  have hdG : ∀ φ : 𝓓(V, ℝ),
      energyFormH1 (fun _ => 1) 0 0 d (W1p.ofTestFunctionₗ volume V 2 φ) =
        ∫ x in V, ⟪-f x • e, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ := fun φ => by
    rw [hdeq φ, ← integral_neg]
    congr 1 with x
    rw [inner_smul_left, inner_gradient_right,
      ← (φ.contDiff.differentiable (by simp) x).lineDeriv_eq_fderiv]
    simp
  have hG : HolderOnWith (‖e‖₊ * K) α (fun x => -f x • e) (thickening R S) := by
    simpa [Function.comp_def] using
      (ContinuousLinearMap.toSpanSingleton ℝ (-e)).lipschitzWith.holderWith.comp_holderOnWith hfK
  simpa using hgrad hG hdG hR hSV

end PDE

end TauCeti
