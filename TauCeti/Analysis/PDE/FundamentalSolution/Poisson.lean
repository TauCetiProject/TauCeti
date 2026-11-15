/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Laplacian
import TauCeti.Analysis.Calculus.BumpFunction.FiniteDimension
import TauCeti.Analysis.InnerProductSpace.Laplacian.Basic
import TauCeti.Analysis.PDE.FundamentalSolution.Euclidean.Potential
import TauCeti.Analysis.PDE.FundamentalSolution.Planar.Potential

/-!
# Poisson's equation with compactly supported data

Let `E` be a finite-dimensional real inner product space of dimension `d ≥ 2`. This file shows
that Poisson's equation `Δu = g` has a solution `u` of class `C^k` on all of `E` for every `C^k`
function `g` with compact support, `2 ≤ k ≤ ∞`, and deduces that `Δu = f` can be solved near any
compact subset `K` of an open set `Ω` on which `f` is `C^k`.

A solution is obtained as minus the Newtonian potential of `g`. The potentials are constructed on
the model spaces `EuclideanSpace ℝ (Fin d)` (`TauCeti.laplacian_newtonianKernel_convolution`, for
`d ≥ 3`) and `ℂ` (`TauCeti.laplacian_planarNewtonianKernel_convolution`, for `d = 2`), and they
are transported to `E` along a linear isometry, which commutes with the Laplacian
(`TauCeti.laplacian_comp_linearIsometryEquiv_right`). For the local statement, `f` is first
replaced by a compactly supported `C^k` function equal to it near `K`
(`ContDiffOn.exists_contDiff_eventuallyEq_on_isCompact`).

Local solutions of this kind are the building blocks of the solution of `Δv = f` on an arbitrary
open set `Ω` along a compact exhaustion
(`TauCeti.Analysis.InnerProductSpace.Laplacian.Exhaustion`).

## Main declarations

* `TauCeti.exists_contDiff_laplacian_eq_of_hasCompactSupport`: for `g` of class `C^k` with
  compact support there is `u` of class `C^k` with `Δu = g`.
* `TauCeti.exists_contDiff_laplacian_eventuallyEq_nhdsSet`: for `f` of class `C^k` on an open
  set `Ω` and a compact `K ⊆ Ω` there is `u` of class `C^k` with `Δu = f` near `K`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Section 2.2.1, Theorem 1.
-/

public section

namespace TauCeti

open InnerProductSpace Laplacian Filter Set Topology
open scoped Convolution

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

omit [CompleteSpace F] in
/-- Solvability of `Δu = g` for compactly supported `C^k` data transfers along a linear isometry
`E ≃ E'`. -/
private theorem exists_contDiff_laplacian_eq_of_linearIsometryEquiv {E' : Type*}
    [NormedAddCommGroup E'] [InnerProductSpace ℝ E'] [FiniteDimensional ℝ E'] (l : E ≃ₗᵢ[ℝ] E')
    {k : ℕ∞} (h : ∀ g' : E' → F, ContDiff ℝ k g' → HasCompactSupport g' →
      ∃ u' : E' → F, ContDiff ℝ k u' ∧ Δ u' = g')
    {g : E → F} (hg : ContDiff ℝ k g) (hc : HasCompactSupport g) :
    ∃ u : E → F, ContDiff ℝ k u ∧ Δ u = g := by
  obtain ⟨u', hu', hΔ⟩ := h (g ∘ l.symm) (hg.comp l.symm.contDiff)
    (hc.comp_homeomorph l.symm.toHomeomorph)
  refine ⟨u' ∘ l, hu'.comp l.contDiff, ?_⟩
  rw [laplacian_comp_linearIsometryEquiv_right, hΔ]
  ext x
  simp

/-- **Poisson's equation with compactly supported data.** In a finite-dimensional real inner
product space of dimension at least two, every `C^k` function `g` with compact support,
`2 ≤ k ≤ ∞`, is the Laplacian of a `C^k` function on the whole space. -/
theorem exists_contDiff_laplacian_eq_of_hasCompactSupport (hE : 2 ≤ Module.finrank ℝ E)
    {k : ℕ∞} (hk : 2 ≤ k) {g : E → F} (hg : ContDiff ℝ k g) (hc : HasCompactSupport g) :
    ∃ u : E → F, ContDiff ℝ k u ∧ Δ u = g := by
  have hk' : (2 : WithTop ℕ∞) ≤ k := WithTop.coe_le_coe.2 hk
  rcases hE.eq_or_lt with hE2 | hE3
  · -- Dimension two: transport the planar Newtonian potential from `ℂ`.
    refine exists_contDiff_laplacian_eq_of_linearIsometryEquiv
      (((stdOrthonormalBasis ℝ E).reindex (finCongr hE2.symm)).repr.trans
        Complex.orthonormalBasisOneI.repr.symm) (fun g' hg' hc' ↦ ?_) hg hc
    refine ⟨-(planarNewtonianKernel ⋆ g'),
      (contDiff_planarNewtonianKernel_convolution hg' hc').neg, ?_⟩
    rw [laplacian_neg, laplacian_planarNewtonianKernel_convolution (hg'.of_le hk') hc', neg_neg]
  · -- Dimension at least three: transport the Newtonian potential from `ℝᵈ`.
    refine exists_contDiff_laplacian_eq_of_linearIsometryEquiv
      (stdOrthonormalBasis ℝ E).repr (fun g' hg' hc' ↦ ?_) hg hc
    refine ⟨-(newtonianKernel _ ⋆ g'),
      (contDiff_newtonianKernel_convolution hg' hc').neg, ?_⟩
    rw [laplacian_neg, laplacian_newtonianKernel_convolution hE3 (hg'.of_le hk') hc', neg_neg]

/-- **Local solvability of Poisson's equation.** In a finite-dimensional real inner product space
of dimension at least two, let `f` be of class `C^k`, `2 ≤ k ≤ ∞`, on an open set `Ω`, and let
`K ⊆ Ω` be compact. Then some `C^k` function `u` on the whole space satisfies `Δu = f` on a
neighbourhood of `K`. -/
theorem exists_contDiff_laplacian_eventuallyEq_nhdsSet (hE : 2 ≤ Module.finrank ℝ E) {k : ℕ∞}
    (hk : 2 ≤ k) {Ω K : Set E} (hΩ : IsOpen Ω) (hK : IsCompact K) (hKΩ : K ⊆ Ω) {f : E → F}
    (hf : ContDiffOn ℝ k f Ω) :
    ∃ u : E → F, ContDiff ℝ k u ∧ Δ u =ᶠ[𝓝ˢ K] f := by
  obtain ⟨g, hg, hgc, -, -, hgf⟩ := hf.exists_contDiff_eventuallyEq_on_isCompact hK hΩ hKΩ
  obtain ⟨u, hu, hΔ⟩ := exists_contDiff_laplacian_eq_of_hasCompactSupport hE hk hg hgc
  exact ⟨u, hu, hΔ ▸ eventually_nhdsSet_iff_forall.2 hgf⟩

end TauCeti
