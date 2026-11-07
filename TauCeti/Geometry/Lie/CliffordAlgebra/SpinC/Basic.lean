/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.CliffordAlgebra.Spin.Manifold
public import TauCeti.Geometry.Manifold.Algebra.Quotient
public import TauCeti.Topology.Algebra.CliffordAlgebra.Spin.SpinC
public import Mathlib.Geometry.Manifold.Instances.Sphere

/-!
# The smooth compact Spinᶜ quotient

Equip the actual quotient `(Spin(n) × U(1)) / {1, (-1, -1)}` with the smooth quotient charts.
The diagonal kernel is discrete, so the quotient inherits the Lie-group structure and the
quotient map is a local diffeomorphism. The determinant character `[s,z] ↦ z²` is smooth.
These are the native quotient group and topology, not a replacement matrix carrier.

The construction uses the native Spin charts pulled back from the embedded Clifford units
and `Subgroup.instLieGroupDiscreteQuotient` for the central finite quotient.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Appendix D.
* J. W. Morgan, *The Seiberg–Witten equations and applications to the topology of smooth
  four-manifolds* (1996), §3.1.
-/

public section

noncomputable section

open CliffordAlgebra Manifold TauCeti TauCeti.CliffordAlgebra
open scoped Manifold ContDiff

namespace CliffordAlgebra.spinCGroup

variable (n : ℕ) (hQ : realCliffordForm n 0 ≠ 0)

/-- The defining central quotient map is a smooth local diffeomorphism. -/
theorem isLocalDiffeomorph_realMk :
    IsLocalDiffeomorph (𝓘(ℝ, realSpinLieModel n).prod (𝓡 1))
      (𝓘(ℝ, realSpinLieModel n).prod (𝓡 1)) ∞ (mk (realCliffordForm n 0) hQ) := by
  rw [coe_mk]
  exact Subgroup.isLocalDiffeomorph_quotientMk (spinCKernel (realCliffordForm n 0) hQ)

/-- Smoothness on compact Spinᶜ is tested on its defining double cover. -/
theorem contMDiff_iff_contMDiff_comp_mk
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    (f : spinCGroup (realCliffordForm n 0) hQ → M) :
    ContMDiff (𝓘(ℝ, realSpinLieModel n).prod (𝓡 1)) I ∞ f ↔
      ContMDiff (𝓘(ℝ, realSpinLieModel n).prod (𝓡 1)) I ∞
        (f ∘ mk (realCliffordForm n 0) hQ) := by
  rw [coe_mk]
  exact Subgroup.contMDiff_quotient_iff (spinCKernel (realCliffordForm n 0) hQ) le_rfl f

/-- The weight-two determinant character is smooth on the actual Spinᶜ quotient. -/
theorem contMDiff_realDet :
    ContMDiff (𝓘(ℝ, realSpinLieModel n).prod (𝓡 1)) (𝓡 1) ∞
      (det (realCliffordForm n 0) hQ) := by
  apply (contMDiff_iff_contMDiff_comp_mk n hQ _).mpr
  simpa only [Function.comp_def, det_mk] using contMDiff_snd.pow 2

end CliffordAlgebra.spinCGroup
