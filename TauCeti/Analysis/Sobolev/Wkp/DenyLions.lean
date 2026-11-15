/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Wkp.Basic
public import TauCeti.Analysis.Normed.Operator.Compact.Estimate
import TauCeti.Analysis.Normed.Module.Quotient

/-!
# The Deny–Lions lemma from compactness

Let `Ω` be an open set such that forgetting the highest weak derivative is a compact operator
`W^{m+1,p}(Ω) → W^{m,p}(Ω)`, as the Rellich–Kondrachov theorem provides on bounded Lipschitz
domains. Write `N` for the kernel of the highest weak derivative `D^{m+1}` on `W^{m+1,p}(Ω)`.
This file proves the **Deny–Lions lemma**: on the quotient `W^{m+1,p}(Ω) ⧸ N` the quotient norm is
equivalent to the top seminorm `‖D^{m+1} u‖_{Lᵖ}`, which descends to the quotient. Concretely:

* `N` is finite-dimensional;
* there is a continuous projection `P` of `W^{m+1,p}(Ω)` onto `N` with
  `‖u - P u‖ ≤ C * ‖D^{m+1} u‖` for every `u`;
* `‖D^{m+1} u‖ ≤ ‖[u]‖ ≤ C * ‖D^{m+1} u‖`, where `[u]` is the class of `u` in the quotient.

Classically, on a connected `Ω` the kernel `N` consists of the classes of polynomials of degree at
most `m`, which gives the familiar form of the lemma. The statements here do not use that
identification and need no connectedness.

The argument is Peetre's compact-error estimate in its quotient form,
`ContinuousLinearMap.exists_projection_norm_sub_le_of_compact_estimate`, applied to the estimate
`‖u‖_{m+1,p} ≤ ‖u‖_{m,p} + ‖D^{m+1} u‖_{Lᵖ}` of the graph norm. The first-order case with the
constants as kernel is `TauCeti.W1p.exists_eLpNorm_value_sub_setAverage_le_of_isCompactOperator`.
The corresponding statements on bounded Lipschitz domains are in
`TauCeti.Analysis.Sobolev.LipschitzDomain.Wkp.DenyLions`.

## Main declarations

* `TauCeti.Wkp.finiteDimensional_ker_iteratedGradientL_of_isCompactOperator`: the kernel of the
  highest weak derivative is finite-dimensional.
* `TauCeti.Wkp.exists_projection_norm_sub_le_of_isCompactOperator`: a continuous projection onto
  that kernel whose error is controlled by the highest weak derivative.
* `TauCeti.Wkp.exists_norm_mk_le_of_isCompactOperator`,
  `TauCeti.Wkp.norm_iteratedGradient_le_norm_mk`: the two halves of the equivalence between the
  quotient norm and the top seminorm.

## References

* J. Deny, J.-L. Lions, *Les espaces du type de Beppo Levi*, Ann. Inst. Fourier 5 (1954),
  305–370, Chapitre III, §2, Théorème 2.1.
* P. G. Ciarlet, *The Finite Element Method for Elliptic Problems*, SIAM (2002), Theorem 3.1.1.
-/

public section

noncomputable section

open MeasureTheory TopologicalSpace
open scoped ENNReal

namespace TauCeti

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure]
  {Omega : Opens E} {p : ℝ≥0∞} [Fact (1 ≤ p)]

namespace Wkp

/-- The graph-norm estimate in the compact-error form used by Peetre's lemma: the
`W^{m+1,p}` norm is at most the norm of the highest weak derivative plus the `W^{m,p}` norm. -/
private theorem norm_le_one_mul_norm_iteratedGradientL_add_norm_lowerOrderL (m : ℕ)
    (u : Wkp mu Omega p (m + 1)) :
    ‖u‖ ≤ 1 * ‖iteratedGradientL m u‖ + ‖lowerOrderL m u‖ := by
  rw [one_mul, add_comm ‖_‖, iteratedGradientL_apply, lowerOrderL_apply]
  exact norm_le_norm_lowerOrder_add_norm_iteratedGradient m u

/-- If forgetting the highest weak derivative is a compact operator
`W^{m+1,p}(Ω) → W^{m,p}(Ω)`, then the kernel of the highest weak derivative on `W^{m+1,p}(Ω)` is
finite-dimensional. -/
theorem finiteDimensional_ker_iteratedGradientL_of_isCompactOperator (m : ℕ)
    (hK : IsCompactOperator (lowerOrderL (mu := mu) (Omega := Omega) (p := p) m)) :
    FiniteDimensional ℝ (iteratedGradientL (mu := mu) (Omega := Omega) (p := p) m).ker :=
  (iteratedGradientL m).finiteDimensional_ker_of_compact_estimate hK
    (norm_le_one_mul_norm_iteratedGradientL_add_norm_lowerOrderL m)

/-- **The Deny–Lions lemma, projection form.** If forgetting the highest weak derivative is a
compact operator `W^{m+1,p}(Ω) → W^{m,p}(Ω)`, there are a continuous linear projection `P` of
`W^{m+1,p}(Ω)` onto the kernel of the highest weak derivative `D^{m+1}` and a constant `C` with
`‖u - P u‖ ≤ C * ‖D^{m+1} u‖` for every `u ∈ W^{m+1,p}(Ω)`. -/
theorem exists_projection_norm_sub_le_of_isCompactOperator (m : ℕ)
    (hK : IsCompactOperator (lowerOrderL (mu := mu) (Omega := Omega) (p := p) m)) :
    ∃ (P : Wkp mu Omega p (m + 1) →L[ℝ] Wkp mu Omega p (m + 1)) (C : ℝ), 0 ≤ C ∧
      (∀ u, iteratedGradient m (P u) = 0) ∧ (∀ u, iteratedGradient m u = 0 → P u = u) ∧
      ∀ u, ‖u - P u‖ ≤ C * ‖iteratedGradient m u‖ := by
  obtain ⟨P, C, hC, hP, hrange, hbound⟩ :=
    (iteratedGradientL m).exists_projection_norm_sub_le_of_compact_estimate hK
      (norm_le_one_mul_norm_iteratedGradientL_add_norm_lowerOrderL m)
  refine ⟨P, C, hC, fun u ↦ ?_, fun u hu ↦ ?_, fun u ↦ ?_⟩
  · have h : P u ∈ (P : Wkp mu Omega p (m + 1) →ₗ[ℝ] Wkp mu Omega p (m + 1)).range :=
      LinearMap.mem_range_self _ u
    rwa [hrange, LinearMap.mem_ker, ContinuousLinearMap.coe_coe, iteratedGradientL_apply] at h
  · rw [← iteratedGradientL_apply, ← ContinuousLinearMap.coe_coe, ← LinearMap.mem_ker,
      ← hrange] at hu
    obtain ⟨v, rfl⟩ := hu
    exact congr($hP v)
  · have h := hbound u
    rwa [iteratedGradientL_apply] at h

/-- **The Deny–Lions lemma.** If forgetting the highest weak derivative is a compact operator
`W^{m+1,p}(Ω) → W^{m,p}(Ω)`, the quotient norm of `u ∈ W^{m+1,p}(Ω)` modulo the kernel of the
highest weak derivative `D^{m+1}` is bounded by a constant multiple of `‖D^{m+1} u‖`. With
`TauCeti.Wkp.norm_iteratedGradient_le_norm_mk`, the quotient norm and the descended top seminorm
are equivalent. -/
theorem exists_norm_mk_le_of_isCompactOperator (m : ℕ)
    (hK : IsCompactOperator (lowerOrderL (mu := mu) (Omega := Omega) (p := p) m)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : Wkp mu Omega p (m + 1),
      ‖(Submodule.Quotient.mk u : Wkp mu Omega p (m + 1) ⧸
        (iteratedGradientL (mu := mu) (Omega := Omega) (p := p) m).ker)‖ ≤
        C * ‖iteratedGradient m u‖ := by
  obtain ⟨C, hC, hbound⟩ := (iteratedGradientL m).exists_norm_mk_ker_le_of_compact_estimate hK
    (norm_le_one_mul_norm_iteratedGradientL_add_norm_lowerOrderL m)
  refine ⟨C, hC, fun u ↦ ?_⟩
  have h := hbound u
  rwa [iteratedGradientL_apply] at h

/-- The highest weak derivative descends to the quotient by its kernel without increasing norms:
`‖D^{m+1} u‖` is at most the quotient norm of `u` modulo the kernel of `D^{m+1}`. This is the
easy half of the Deny–Lions equivalence, and needs no compactness. -/
theorem norm_iteratedGradient_le_norm_mk (m : ℕ) (u : Wkp mu Omega p (m + 1)) :
    ‖iteratedGradient m u‖ ≤
      ‖(Submodule.Quotient.mk u : Wkp mu Omega p (m + 1) ⧸
        (iteratedGradientL (mu := mu) (Omega := Omega) (p := p) m).ker)‖ := by
  set N := (iteratedGradientL (mu := mu) (Omega := Omega) (p := p) m).ker
  have hnorm : ‖N.liftQL (iteratedGradientL m) le_rfl‖ ≤ 1 := by
    rw [Submodule.norm_liftQL]
    exact ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v ↦ by
      rw [one_mul, iteratedGradientL_apply]
      exact norm_iteratedGradient_le m v
  calc ‖iteratedGradient m u‖
        = ‖N.liftQL (iteratedGradientL m) le_rfl (Submodule.Quotient.mk u)‖ := by
        rw [Submodule.liftQL_apply, Submodule.liftQ_apply, ContinuousLinearMap.coe_coe,
          iteratedGradientL_apply]
    _ ≤ ‖N.liftQL (iteratedGradientL m) le_rfl‖ * ‖(Submodule.Quotient.mk u : _ ⧸ N)‖ :=
        ContinuousLinearMap.le_opNorm _ _
    _ ≤ ‖(Submodule.Quotient.mk u : _ ⧸ N)‖ := mul_le_of_le_one_left (norm_nonneg _) hnorm

end Wkp

end TauCeti
