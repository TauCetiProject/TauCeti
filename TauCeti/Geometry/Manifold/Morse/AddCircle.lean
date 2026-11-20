/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Morse.OneDimensional
public import TauCeti.Geometry.Manifold.Instances.AddCircle
public import TauCeti.Geometry.Manifold.Morse.CriticalPoints
import TauCeti.Analysis.Calculus.PeriodicDeriv

/-!
# Critical points of functions on the circle

A function `f` on the circle `AddCircle p = ℝ ⧸ pℤ` is read through the quotient map as a
`p`-periodic function `F : ℝ → ℝ` with `f t = F t` for every real `t`. The charts of
`AddCircle p` are local lifts to `ℝ`, so near every chart point the coordinate expression of `f`
is `F` itself (`AddCircle.comp_extChartAt_symm_eventuallyEq_of_forall_coe`). This file reads the
Morse-theoretic notions on the circle off the first two derivatives of `F`:

* `f` is `C^n` exactly when `F` is (`AddCircle.contMDiff_iff_contDiff_of_forall_coe`);
* the class of `t` is a critical point of `f` exactly when `F'(t) = 0`;
* for `C²` functions it is a nondegenerate critical point exactly when moreover `F''(t) ≠ 0`;
* so `f` is a Morse function exactly when `F` is smooth and `F''` does not vanish where `F'`
  does.

## Main results

* `TauCeti.coe_mem_criticalPoints_iff_of_forall_coe`: critical points on the circle.
* `TauCeti.isManifoldNondegenerateCriticalPoint_coe_iff_of_forall_coe`: nondegenerate critical
  points on the circle.
* `TauCeti.isMorse_iff_of_forall_coe`: Morse functions on the circle.
-/

public section

open Filter Function Set
open scoped Manifold Topology ContDiff

namespace TauCeti

variable {p : ℝ} [Fact (0 < p)] {f : AddCircle p → ℝ} {F : ℝ → ℝ}

/-- **Critical points on the circle.** If `f t = F t` for every real `t`, the class of `t` is a
critical point of `f` exactly when `F'(t) = 0`. -/
theorem coe_mem_criticalPoints_iff_of_forall_coe (hf : ∀ t : ℝ, f t = F t) (t : ℝ) :
    (t : AddCircle p) ∈ criticalPoints 𝓘(ℝ) f ↔ deriv F t = 0 := by
  obtain ⟨k, hk⟩ := AddCircle.exists_extChartAt_coe_eq_add_zsmul (p := p) t
  rw [mem_criticalPoints_iff_fderiv_comp_extChartAt_symm_eq_zero,
    (AddCircle.comp_extChartAt_symm_eventuallyEq_of_forall_coe hf _).fderiv_eq,
    ← toSpanSingleton_deriv, hk, ((AddCircle.periodic_of_forall_coe hf).deriv.zsmul k) t]
  exact ⟨fun h ↦ by simpa using congr($h 1), fun h ↦ by simp [h]⟩

/-- **Nondegenerate critical points on the circle.** If `f t = F t` for every real `t` and `F` is
`C²`, the class of `t` is a nondegenerate critical point of `f` exactly when `F'(t) = 0` and
`F''(t) ≠ 0`. -/
theorem isManifoldNondegenerateCriticalPoint_coe_iff_of_forall_coe (hf : ∀ t : ℝ, f t = F t)
    (hF : ContDiff ℝ 2 F) (t : ℝ) :
    IsManifoldNondegenerateCriticalPoint 𝓘(ℝ) f t ↔ deriv F t = 0 ∧ iteratedDeriv 2 F t ≠ 0 := by
  obtain ⟨k, hk⟩ := AddCircle.exists_extChartAt_coe_eq_add_zsmul (p := p) t
  have hper := AddCircle.periodic_of_forall_coe hf
  have heq := AddCircle.comp_extChartAt_symm_eventuallyEq_of_forall_coe hf (t : AddCircle p)
  rw [hk] at heq
  rw [isManifoldNondegenerateCriticalPoint_iff, hk, ← (hper.deriv.zsmul k) t,
    ← ((hper.iteratedDeriv 2).zsmul k) t, ← isNondegenerateCriticalPoint_real_iff hF.contDiffAt]
  exact ⟨fun h ↦ h.congr_of_eventuallyEq heq, fun h ↦ h.congr_of_eventuallyEq heq.symm⟩

/-- **Morse functions on the circle.** If `f t = F t` for every real `t`, then `f` is a Morse
function exactly when `F` is smooth and `F''(t) ≠ 0` wherever `F'(t) = 0`. -/
theorem isMorse_iff_of_forall_coe (hf : ∀ t : ℝ, f t = F t) :
    IsMorse 𝓘(ℝ) f ↔ ContDiff ℝ ∞ F ∧ ∀ t, deriv F t = 0 → iteratedDeriv 2 F t ≠ 0 := by
  rw [isMorse_iff, AddCircle.contMDiff_iff_contDiff_of_forall_coe hf]
  refine and_congr_right fun hF ↦ ?_
  have hF2 : ContDiff ℝ 2 F := hF.of_le (by simp)
  simp_rw [← mem_criticalPoints_iff_fderiv_comp_extChartAt_symm_eq_zero]
  refine ⟨fun h t ht ↦ ?_, fun h x hx ↦ ?_⟩
  · exact ((isManifoldNondegenerateCriticalPoint_coe_iff_of_forall_coe hf hF2 t).1
      (h t ((coe_mem_criticalPoints_iff_of_forall_coe hf t).2 ht))).2
  · induction x using QuotientAddGroup.induction_on with | H t => ?_
    have ht := (coe_mem_criticalPoints_iff_of_forall_coe hf t).1 hx
    exact (isManifoldNondegenerateCriticalPoint_coe_iff_of_forall_coe hf hF2 t).2 ⟨ht, h t ht⟩

end TauCeti
