/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.DifferentialForm.Relative.Basic

/-!
# First jets of relative Poincaré primitives

The relative Poincaré operator `fiberwisePoincareHomotopy` integrates contraction with the
normal coordinate on `E × N`. If the input form is continuous and vanishes as a full ambient
tensor at `(q, 0)`, its primitive has zero value and zero Fréchet derivative there. Continuity
at that single point suffices: contraction contributes a factor `‖p‖`, while the input form
tends to zero uniformly along the shrinking normal segment.

For closed forms on an adapted open set this gives a relative primitive of the same
regularity with zero first jet along the zero section. Full ambient vanishing is essential;
vanishing of the tangential pullback alone only guarantees the value of the primitive is zero.
The zero first jet is the input to the relative Moser argument that preserves the ambient
differential along a fixed submanifold.

The construction is the existing `fiberwisePoincareHomotopy`; no new primitive is chosen.
Neither finite dimensionality nor completeness of the base and normal spaces is needed.

## References

* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Springer, 2001, §§6–7
  (relative Poincaré primitives and Moser's argument).
* R. Bott and L. W. Tu, *Differential Forms in Algebraic Topology*, GTM 82, §4
  (integration along the scaling homotopy).
-/

public section

noncomputable section

open Set Filter Metric
open scoped Topology

namespace TauCeti

variable {E N F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup N] [NormedSpace ℝ N]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {k : ℕ}

/-- If a form is continuous within a set stable under scaling the normal coordinate and zero as
a full ambient tensor at a point of the zero section, its relative Poincaré primitive has zero
Fréchet derivative within that set there. Only continuity at this point is required, with no
closedness or differentiability hypothesis on the input. -/
theorem hasFDerivWithinAt_fiberwisePoincareHomotopy_zeroSection
    {ω : E × N → (E × N) [⋀^Fin (k + 1)]→L[ℝ] F} {s : Set (E × N)} {q : E}
    (hω : ContinuousWithinAt ω s (q, 0)) (hzero : ω (q, 0) = 0)
    (hscale : ∀ x ∈ s, ∀ t ∈ Icc (0 : ℝ) 1, (x.1, t • x.2) ∈ s) :
    HasFDerivWithinAt (fiberwisePoincareHomotopy ω)
      (0 : (E × N) →L[ℝ] (E × N) [⋀^Fin k]→L[ℝ] F) s (q, 0) := by
  rw [hasFDerivWithinAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro ε hε
  obtain ⟨δ, hδ, hbound⟩ := Metric.continuousWithinAt_iff.1 hω ε hε
  filter_upwards [inter_mem_nhdsWithin s (ball_mem_nhds (q, (0 : N)) hδ)] with x hx
  simp only [fiberwisePoincareHomotopy_zeroSection, sub_zero,
    zero_apply]
  refine (norm_fiberwisePoincareHomotopy_le (B := ε) fun t ht ↦ ?_).trans ?_
  · have hdist : dist (x.1, t • x.2) (q, (0 : N)) ≤ dist x (q, (0 : N)) := by
      simp only [Prod.dist_eq, dist_zero_right, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg ht.1]
      exact max_le_max le_rfl (mul_le_of_le_one_left (norm_nonneg _) ht.2)
    have := hbound (hscale x hx.1 t ht) (hdist.trans_lt hx.2)
    simpa [hzero, dist_zero_right] using this.le
  · exact mul_le_mul_of_nonneg_left (by
      simpa using (norm_snd_le (x - (q, (0 : N))))) hε.le

/-- If a form is continuous and zero as a full ambient tensor at a point of the zero section,
its relative Poincaré primitive has zero Fréchet derivative there. Only continuity at this
point is required, with no closedness or differentiability hypothesis on the input. -/
theorem hasFDerivAt_fiberwisePoincareHomotopy_zeroSection
    {ω : E × N → (E × N) [⋀^Fin (k + 1)]→L[ℝ] F} {q : E}
    (hω : ContinuousAt ω (q, 0)) (hzero : ω (q, 0) = 0) :
    HasFDerivAt (fiberwisePoincareHomotopy ω)
      (0 : (E × N) →L[ℝ] (E × N) [⋀^Fin k]→L[ℝ] F) (q, 0) :=
  hasFDerivWithinAt_univ.1 <| hasFDerivWithinAt_fiberwisePoincareHomotopy_zeroSection
    hω.continuousWithinAt hzero fun _ _ _ _ ↦ mem_univ _

end TauCeti

open TauCeti

variable {E N F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup N] [NormedSpace ℝ N]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] {k : ℕ}

/-- A closed form of positive degree on an adapted open set, vanishing as a full ambient
tensor on the zero section, has a relative primitive of the same regularity whose value and
Fréchet derivative both vanish along that section. -/
theorem IsOpen.exists_contDiffOn_relative_primitive_fderiv_eq_zero {s : Set (E × N)}
    (hso : IsOpen s) {r : ℕ∞} (hr : 1 ≤ r)
    {ω : E × N → (E × N) [⋀^Fin (k + 1)]→L[ℝ] F}
    (hω : ContDiffOn ℝ r ω s)
    (hscale : ∀ x ∈ s, ∀ t ∈ Icc (0 : ℝ) 1, (x.1, t • x.2) ∈ s)
    (hclosed : ∀ x ∈ s, extDeriv ω x = 0)
    (hzero : ∀ q : E, (q, (0 : N)) ∈ s → ω (q, 0) = 0) :
    ∃ β : E × N → (E × N) [⋀^Fin k]→L[ℝ] F,
      ContDiffOn ℝ r β s ∧ (∀ q : E, β (q, 0) = 0) ∧
      (∀ q : E, (q, (0 : N)) ∈ s → fderiv ℝ β (q, 0) = 0) ∧
      ∀ x ∈ s, extDeriv β x = ω x := by
  refine ⟨fiberwisePoincareHomotopy ω,
    hso.contDiffOn_fiberwisePoincareHomotopy hω hscale,
    fiberwisePoincareHomotopy_zeroSection ω, ?_, ?_⟩
  · intro q hq
    exact (hasFDerivAt_fiberwisePoincareHomotopy_zeroSection
      (hω.continuousOn.continuousAt (hso.mem_nhds hq)) (hzero q hq)).fderiv
  · intro x hx
    exact hso.extDeriv_fiberwisePoincareHomotopy_eq
      (hω.of_le (by exact_mod_cast hr)) hscale hclosed
      (fun q hq ↦ by ext v; simp [hzero q hq]) hx
