/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.NovikovModule.Grading

/-!
# Cochain degrees of supported Floer products

For a raw grading `μ` and half-dimension `n`, the cochain degree of a capped generator is
`n - μ`. The corresponding homogeneous completed combinations are exactly those of raw degree
`n - k`. A supported kernel of raw degree `-n` therefore gives a degree-zero product in the
cochain grading. This is a statement about the completed kernel product itself, including its
finite coefficient sums, rather than just about its expected index.

The kernel's grading and support hypotheses remain explicit: establishing them for geometric
counts requires the index and compactness theorems of the chosen Floer problem. No complex,
orientation line, differential or geometric count is constructed here.

The product is `TauCeti.NovikovModule.kernelProduct`, and its homogeneity follows from
`TauCeti.NovikovModule.kernelProduct_mem_gradeBy`.

## References

* S. Piunikhin, D. Salamon and M. Schwarz, *Symplectic Floer–Donaldson theory and quantum
  cohomology*, in *Contact and symplectic geometry*, Publ. Newton Inst. 8 (1996), 171–200.
-/

public section

namespace TauCeti.Floer

open NovikovModule

variable {R S₁ S₂ S₀ : Type*} [CommSemiring R]
  {F₁ : S₁ → ℝ} {F₂ : S₂ → ℝ} {F₀ : S₀ → ℝ}
  {C : ℝ} {κ : S₁ → S₂ → S₀ → R}

/-- A supported product kernel of raw Floer degree `-n` has degree zero on completed
combinations regraded by `k = n - μ`. The degree hypothesis concerns nonzero kernel
coefficients, and the conclusion concerns the actual extended bilinear product. -/
theorem kernelProduct_mem_cochain_gradeBy
    (hκ : ∀ p₁ p₂ p₀, κ p₁ p₂ p₀ ≠ 0 → F₀ p₀ ≤ F₁ p₁ + F₂ p₂ + C)
    (hfin : ∀ p₁ p₂, κ p₁ p₂ ∈ NovikovModule R F₀)
    {μ₁ : S₁ → ℤ} {μ₂ : S₂ → ℤ} {μ₀ : S₀ → ℤ} {n : ℤ}
    (hμ : ∀ p₁ p₂ p₀, κ p₁ p₂ p₀ ≠ 0 → μ₀ p₀ = μ₁ p₁ + μ₂ p₂ - n)
    {i j : ℤ} {a : NovikovModule R F₁} {b : NovikovModule R F₂}
    (ha : a ∈ gradeBy R F₁ (fun p => n - μ₁ p) i)
    (hb : b ∈ gradeBy R F₂ (fun p => n - μ₂ p) j) :
    kernelProduct hκ hfin a b ∈ gradeBy R F₀ (fun p => n - μ₀ p) (i + j) := by
  rw [gradeBy_sub] at ha hb ⊢
  have hm := kernelProduct_mem_gradeBy hκ hfin (ε := -n)
    (fun p₁ p₂ p₀ h => by simpa only [sub_eq_add_neg] using hμ p₁ p₂ p₀ h) ha hb
  have he : (n - i) + (n - j) + -n = n - (i + j) := by omega
  simpa only [he] using hm

end TauCeti.Floer
