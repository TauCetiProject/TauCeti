/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Instances.AddCircle
public import TauCeti.Geometry.Manifold.Morse.LocalDiffeomorph
import TauCeti.Algebra.Ring.Periodic
import TauCeti.Analysis.Calculus.Morse.OneDimensional

/-!
# Critical points of functions on a circle

A function on the circle `AddCircle p` is the same as a `p`-periodic function `f : ℝ → ℝ`, through
its lift `Function.Periodic.lift`. The quotient map `ℝ → AddCircle p` is a smooth local
diffeomorphism (`AddCircle.isLocalDiffeomorph_coe`), so, as for smoothness
(`Function.Periodic.contMDiff_lift_iff`), critical points and their nondegeneracy can be read on
`f`:

* the class of `t` is a critical point of the lift exactly when `f' t = 0`
  (`Function.Periodic.coe_mem_criticalPoints_lift_iff`);
* it is a nondegenerate critical point exactly when moreover `f'' t ≠ 0`, for `f` of class `C²`
  near `t` (`Function.Periodic.isManifoldNondegenerateCriticalPoint_lift_coe_iff`);
* so the lift of a smooth `f` is a Morse function exactly when `f'' t ≠ 0` wherever `f' t = 0`
  (`Function.Periodic.isMorse_lift_iff`).

These are the one-variable criteria of `TauCeti.Analysis.Calculus.Morse.OneDimensional`
transported to the circle, which is how explicit functions on the circle are tested for being
Morse.

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  §2.
-/

public section

open Set TauCeti
open scoped Manifold ContDiff

namespace Function.Periodic

variable {p : ℝ} [Fact (0 < p)] {f : ℝ → ℝ}

/-- The class of `t` is a critical point of the lift of a periodic function `f` to the circle
exactly when `f' t = 0`. -/
theorem coe_mem_criticalPoints_lift_iff (hf : Periodic f p) (t : ℝ) :
    (t : AddCircle p) ∈ criticalPoints 𝓘(ℝ) hf.lift ↔ deriv f t = 0 := by
  rw [← ((AddCircle.isLocalDiffeomorph_coe p 1) t).mem_criticalPoints_comp_iff le_rfl,
    hf.lift_comp_coe, mem_criticalPoints_iff_deriv_eq_zero]

/-- The class of `t` is a nondegenerate critical point of the lift of a periodic function `f`,
of class `C²` near `t`, exactly when `f' t = 0` and `f'' t ≠ 0`. -/
theorem isManifoldNondegenerateCriticalPoint_lift_coe_iff (hf : Periodic f p) {t : ℝ}
    (hf₂ : ContDiffAt ℝ 2 f t) :
    IsManifoldNondegenerateCriticalPoint 𝓘(ℝ) hf.lift (t : AddCircle p) ↔
      deriv f t = 0 ∧ iteratedDeriv 2 f t ≠ 0 := by
  rw [← ((AddCircle.isLocalDiffeomorph_coe p 2) t).isManifoldNondegenerateCriticalPoint_comp_iff
    le_rfl, hf.lift_comp_coe, isManifoldNondegenerateCriticalPoint_modelSpace_iff,
    isNondegenerateCriticalPoint_real_iff hf₂]

/-- **Morse functions on the circle.** The lift of a smooth periodic function `f` to the circle is
a Morse function exactly when `f'' t ≠ 0` at every `t` with `f' t = 0`. -/
theorem isMorse_lift_iff (hf : Periodic f p) (h : ContDiff ℝ ∞ f) :
    IsMorse 𝓘(ℝ) hf.lift ↔ ∀ t, deriv f t = 0 → iteratedDeriv 2 f t ≠ 0 := by
  rw [← isMorseOn_univ, isMorseOn_iff_criticalPoints]
  simp only [mem_univ, true_implies, (hf.contMDiff_lift h).contMDiffOn, true_and]
  refine ⟨fun H t ht ↦ ?_, fun H x hx ↦ ?_⟩
  · have hc := (hf.coe_mem_criticalPoints_lift_iff t).2 ht
    exact ((hf.isManifoldNondegenerateCriticalPoint_lift_coe_iff
      (h.contDiffAt.of_le (by simp))).1 (H _ hc)).2
  · obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective x
    have ht := (hf.coe_mem_criticalPoints_lift_iff t).1 hx
    exact (hf.isManifoldNondegenerateCriticalPoint_lift_coe_iff
      (h.contDiffAt.of_le (by simp))).2 ⟨ht, H t ht⟩

end Function.Periodic
