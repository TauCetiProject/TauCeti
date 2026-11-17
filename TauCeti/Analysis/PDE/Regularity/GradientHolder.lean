/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Regularity.DivergenceFormSchauder

/-!
# Hölder continuity of the gradient for `-Δu = -div G`

Let `u ∈ H¹(Ω)` be a weak solution of `-Δu = -div G` in an open set `Ω ⊆ ℝ^{n+1}`, that is

`∫_Ω ⟨∇u, ∇φ⟩ = ∫_Ω ⟨G, ∇φ⟩` for every test function `φ` on `Ω`,

and let `0 < α < 1`. This file proves that `∇u` is as regular as `G` in the interior: if the open
`R`-thickening `S_R` of a set `S` lies in `Ω` and `G` is `α`-Hölder on `S_R` with constant `K`,
then the precise representative of `∇u` is `α`-Hölder on `S` with constant
`C (K + R^{-(n+1)/2-α} ‖∇u‖_{L²(Ω)})`, where `C` depends only on `n` and `α`. This is the
interior Schauder estimate for the Laplacian in divergence form,
`[∇u]_{α, S} ≤ C ([G]_{α, S_R} + R^{-(n+1)/2-α} ‖∇u‖_{L²(Ω)})`.

It is the case `a = 1` of the estimate for divergence-form equations with Hölder coefficients,
`TauCeti.PDE.exists_holderOnWith_preciseRepresentative_gradient_of_holderOnWith_matrixBilinearForm`:
the identity matrix is uniformly elliptic with `λ = Λ = 1` and, being constant, is `α`-Hölder with
constant `0`, so the constant there depends only on `n` and `α`.

## Main declarations

* `TauCeti.PDE.exists_holderOnWith_preciseRepresentative_gradient`: the interior Hölder estimate
  for `∇u`, with explicit dependence on `K`, `R` and `‖∇u‖_{L²(Ω)}`.

## References

* S. Campanato, *Equazioni ellittiche del II ordine e spazi `𝓛^{(2,λ)}`*, Ann. Mat. Pura Appl.
  69 (1965), 321–381.
* M. Giaquinta, L. Martinazzi, *An Introduction to the Regularity Theory for Elliptic Systems,
  Harmonic Maps and Minimal Graphs*, 2nd ed., Chapter 5.
* Q. Han, F. Lin, *Elliptic Partial Differential Equations*, Chapter 3.
-/

public section

noncomputable section

open MeasureTheory Metric TopologicalSpace TauCeti.MeasureTheory
open scoped Distributions Gradient InnerProductSpace NNReal

namespace TauCeti

namespace PDE

variable {n : ℕ}

/-- **Interior Hölder continuity of the gradient for `-Δu = -div G`.** Let `0 < α < 1`. There is
a constant `C`, depending only on `n` and `α`, such that the following holds. Let `Ω ⊆ ℝ^{n+1}` be
open and let `u ∈ H¹(Ω)` be a weak solution of `-Δu = -div G` in `Ω`, that is
`∫_Ω ⟨∇u, ∇φ⟩ = ∫_Ω ⟨G, ∇φ⟩` for every test function `φ`, where `G` is `α`-Hölder with constant
`K` on the open `R`-thickening of `S` (the points at distance less than `R` from `S`), which lies
in `Ω`. Then the precise representative of `∇u` is `α`-Hölder on `S`, with constant
`C (K + R^{-(n+1)/2-α} ‖∇u‖_{L²(Ω)})`.

The precise representative agrees with `∇u` almost everywhere on `Ω`
(`TauCeti.MeasureTheory.ae_eq_restrict_preciseRepresentative`). The exponent of `G` passes to
`∇u` without loss; this is false for `α = 1`, which is why `α < 1` is assumed. -/
theorem exists_holderOnWith_preciseRepresentative_gradient {α : ℝ≥0} (hα : 0 < α)
    (hα1 : α < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Omega : Opens (EuclideanSpace ℝ (Fin (n + 1)))}
      {u : W1p volume Omega 2}
      {G : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))} {K : ℝ≥0}
      {S : Set (EuclideanSpace ℝ (Fin (n + 1)))} {R : ℝ},
      HolderOnWith K α G (thickening R S) →
      (∀ φ : 𝓓(Omega, ℝ),
        energyFormH1 (fun _ => 1) 0 0 u (W1p.ofTestFunctionₗ volume Omega 2 φ) =
          ∫ x in Omega, ⟪G x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ) →
      0 < R → thickening R S ⊆ Omega →
        HolderOnWith (C * (K + R ^ (-(((n : ℝ) + 1) / 2 + α)) * ‖W1p.gradient u‖)).toNNReal α
          (preciseRepresentative volume
            (W1p.gradient u : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))))
          S := by
  obtain ⟨C, hC, h⟩ :=
    exists_holderOnWith_preciseRepresentative_gradient_of_holderOnWith_matrixBilinearForm
      (n := n) hα hα1 (lam := 1) (Lam := 1) (M := 0)
  refine ⟨C, hC, fun hG hu hR hRS => ?_⟩
  refine h (uniformlyEllipticOn_const_one_one _)
    ((holderWith_zero_iff.2 fun _ _ => rfl).holderOnWith _) hG (by simp) hu hR hRS

end PDE

end TauCeti
