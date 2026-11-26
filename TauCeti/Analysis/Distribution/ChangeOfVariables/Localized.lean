/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Topology.OpenPartialHomeomorph.Defs
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import TauCeti.Analysis.Calculus.FDeriv.Equiv
import TauCeti.Geometry.Manifold.Diffeomorph.Germ

/-!
# Localized changes of variables as finite sums of global ones

Let `e` be a smooth open partial homeomorphism of a finite-dimensional real normed space `E` with
smooth inverse, such as a transition map between two charts of a manifold, and let `θ` be a smooth
function with compact support in the source of `e`. This file writes the localized pullback
`u ↦ θ · (u ∘ e)`, extended by `0` off the source, as a finite sum `∑ᵢ φᵢ · (u ∘ Φᵢ)` of
pullbacks along bijections `Φᵢ` of `E` that are smooth with bounded derivatives of every positive
order, multiplied by Schwartz functions `φᵢ` (`TauCeti.exists_sum_smul_comp_eq_smul_comp`).

Pullbacks along such bijections and multiplication by Schwartz functions are bounded on the usual
function spaces of `E` (Lebesgue, Schwartz, Sobolev and Besov spaces), so this reduces the
boundedness of localized changes of variables on those spaces to the global mapping theorems.

## The argument

Near each point of its source, `e` agrees with such a bijection
(`TauCeti.exists_equiv_eventuallyEq_of_det_fderiv_ne_zero`). A finite partition of unity `χᵢ` on
the support of `θ`, subordinate to the open sets where `e` agrees with bijections `Φᵢ`, gives
`θ · (u ∘ e) = ∑ᵢ (θ χᵢ) · (u ∘ Φᵢ)`.

## References

* M. E. Taylor, *Partial Differential Equations I*, 2nd ed., Springer, 2011, Chapter 4, §1
  (invariance of `H^s` under diffeomorphisms, and its localization).
* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, Springer, 1985,
  Appendix B.1.
-/

public section

noncomputable section

namespace TauCeti

open Filter Set
open scoped SchwartzMap ContDiff

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [AddCommGroup F] [Module ℂ F]

/-- **Localized changes of variables as finite sums.** Let `e` be a smooth open partial
homeomorphism of `E` with smooth inverse and `θ` a smooth function with compact support in the
source of `e`. There are finitely many Schwartz functions `φ x` and bijections `Φ x` of `E` that
are smooth with smooth inverses with bounded derivatives of every positive order, such that
`θ · (u ∘ e)` is `∑ x, φ x · (u ∘ Φ x)` for every function `u`. -/
theorem exists_sum_smul_comp_eq_smul_comp {e : OpenPartialHomeomorph E E}
    (he : ContDiffOn ℝ ∞ e e.source) (he' : ContDiffOn ℝ ∞ e.symm e.target) {θ : E → ℝ}
    (hθ : ContDiff ℝ ∞ θ) (hθc : HasCompactSupport θ) (hθe : tsupport θ ⊆ e.source) :
    ∃ (t : Finset e.source) (Φ : e.source → E ≃ E) (φ : e.source → 𝓢(E, ℂ)),
      (∀ x, ContDiff ℝ ∞ (Φ x) ∧ ContDiff ℝ ∞ (Φ x).symm ∧
        (∀ k, 1 ≤ k → ∃ C, ∀ y, ‖iteratedFDeriv ℝ k (Φ x) y‖ ≤ C) ∧
        (∀ k, 1 ≤ k → ∃ C, ∀ y, ‖iteratedFDeriv ℝ k (Φ x).symm y‖ ≤ C)) ∧
      ∀ (u : E → F) y, θ y • u (e y) = ∑ x ∈ t, φ x y • u (Φ x y) := by
  classical
  -- Near each point `x` of the source, `e` agrees with a bijection `Φ x` of `E` whose derivatives
  -- are bounded.
  choose Φ hΦ hΨ hΦb hΨb hΦe using fun x : e.source ↦
    exists_equiv_eventuallyEq_of_det_fderiv_ne_zero
      (eventually_of_mem (e.open_source.mem_nhds x.property) fun y hy ↦
        he.contDiffAt (e.open_source.mem_nhds hy))
      (e.det_fderiv_ne_zero_of_contDiffOn he he' (by simp) x.property)
  -- A finite partition of unity `χ x` on the support of `θ`, with `Φ x = e` on the support of
  -- `χ x`; the pieces `θ χ x` of `θ` are complex Schwartz functions.
  obtain ⟨t, χ, hχ, -, -, hsum⟩ := hθc.isCompact.exists_contDiff_tsupport_subset_finset_sum_eq_one
    (U := fun x : e.source ↦ interior {y | Φ x y = e y}) (fun _ ↦ isOpen_interior)
    fun y hy ↦ mem_iUnion.2 ⟨⟨y, hθe hy⟩, mem_interior_iff_mem_nhds.2 (hΦe ⟨y, hθe hy⟩)⟩
  have hχΦ (x : e.source) (y : E) (hy : χ x y ≠ 0) : Φ x y = e y :=
    interior_subset ((hχ x).2.2 (subset_tsupport _ hy))
  let φ (x : e.source) : 𝓢(E, ℂ) :=
    (hθc.mul_right.comp_left (g := ((↑) : ℝ → ℂ)) Complex.ofReal_zero).toSchwartzMap
      (Complex.ofRealCLM.contDiff.comp (hθ.mul (hχ x).1))
  have hφ (x : e.source) (y : E) : φ x y = ((θ y * χ x y : ℝ) : ℂ) := (rfl)
  refine ⟨t, Φ, φ, fun x ↦ ⟨hΦ x, hΨ x, hΦb x, hΨb x⟩, fun u y ↦ ?_⟩
  simp only [hφ]
  rw [Finset.sum_congr rfl fun x _ ↦ show ((θ y * χ x y : ℝ) : ℂ) • u (Φ x y) =
      ((θ y * χ x y : ℝ) : ℂ) • u (e y) by
    by_cases h : χ x y = 0
    · simp [h]
    · rw [hχΦ x y h], ← Finset.sum_smul, ← Complex.ofReal_sum, ← Finset.mul_sum]
  by_cases hy : y ∈ tsupport θ
  · rw [hsum y hy, mul_one, Complex.coe_smul]
  · simp [image_eq_zero_of_notMem_tsupport hy]

end TauCeti
