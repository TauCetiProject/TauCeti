/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.IteratedFDeriv.DirectionList
public import TauCeti.Analysis.Calculus.BumpFunction.FiniteDimension

/-!
# Symmetry of iterated derivatives

Over `ℝ` or `ℂ`, the `i`-th iterated derivative of a `C^i` map is a symmetric multilinear map:
permuting its arguments does not change its value. Mathlib proves this for second derivatives
(`ContDiffAt.isSymmSndFDerivAt`) and for analytic maps (`ContDiffAt.iteratedFDeriv_comp_perm`);
for `C^i` maps it follows from the independence of iterated directional derivatives of the order
of the directions (`List.Perm.iteratedFDerivAlong_eq`).

## Main results

* `ContDiff.iteratedFDeriv_comp_perm`: over `ℝ` or `ℂ`, the `i`-th iterated derivative of a
  globally `C^i` map is symmetric at every point.
* `ContDiffAt.iteratedFDeriv_comp_perm_of_finiteDimensional`: on a finite-dimensional real
  space, the same holds at a point near which the map is `C^i`.

These are the symmetry statements needed to identify finite jets of maps with finite Taylor
polynomials (`TauCeti.iteratedFDeriv_finiteJetPolynomial_self`).
-/

public section

open scoped ContDiff

namespace TauCeti

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- Over `ℝ` or `ℂ`, the `i`-th iterated derivative of a `C^i` map is symmetric. -/
theorem _root_.ContDiff.iteratedFDeriv_comp_perm [IsRCLikeNormedField 𝕜] {n : ℕ∞ω} {f : E → F}
    (hf : ContDiff 𝕜 n f) {i : ℕ} (hi : i ≤ n) (x : E) (v : Fin i → E)
    (σ : Equiv.Perm (Fin i)) :
    iteratedFDeriv 𝕜 i f x (v ∘ σ) = iteratedFDeriv 𝕜 i f x v := by
  have hfi : ContDiff 𝕜 i f := hf.of_le hi
  rw [← iteratedFDerivAlong_ofFn_eq_iteratedFDeriv hfi,
    ← iteratedFDerivAlong_ofFn_eq_iteratedFDeriv hfi,
    (σ.ofFn_comp_perm v).iteratedFDerivAlong_eq hfi (by simp)]

/-- On a finite-dimensional real space, the `i`-th iterated derivative of a map at a point near
which it is `C^i` is symmetric. -/
theorem _root_.ContDiffAt.iteratedFDeriv_comp_perm_of_finiteDimensional {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} {x : E} {i : ℕ} (hf : ContDiffAt ℝ i f x) (v : Fin i → E)
    (σ : Equiv.Perm (Fin i)) :
    iteratedFDeriv ℝ i f x (v ∘ σ) = iteratedFDeriv ℝ i f x v := by
  obtain ⟨g, hg, -, hgf⟩ := hf.exists_contDiff_eventuallyEq_of_finiteDimensional i
  rw [← (hgf.iteratedFDeriv ℝ i).eq_of_nhds]
  exact hg.iteratedFDeriv_comp_perm le_rfl x v σ

end TauCeti
