/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.CliffordAlgebra.Spin.Manifold
public import TauCeti.Geometry.Manifold.Algebra.Quotient
public import TauCeti.Topology.Algebra.CliffordAlgebra.Spin.SpinC.Basic
public import Mathlib.Geometry.Manifold.Instances.Sphere

/-!
# The smooth compact Spinᶜ quotient

Equip the actual quotient `(Spin(n) × U(1)) / {1, (-1, -1)}` with the smooth quotient charts.
The diagonal kernel is discrete, so the quotient inherits the Lie-group structure and the
quotient map is a local diffeomorphism. The determinant character `[s,z] ↦ z²` and charge
conjugation `[s, z] ↦ [s, z⁻¹]` are smooth.
These are the native quotient group and topology, not a replacement matrix carrier.

The construction uses the native Spin charts pulled back from the embedded Clifford units
and `Subgroup.instLieGroupDiscreteQuotient` for the central finite quotient, and packages the
defining cover and canonical Spin inclusion as `ContMDiffMonoidMorphism`s (`realMkSmoothHom`,
`realOfSpinSmoothHom`).

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

/-- Charge conjugation `[s, z] ↦ [s, z⁻¹]` is a smooth automorphism of the actual Spinᶜ
quotient. -/
theorem contMDiff_realChargeConj :
    ContMDiff (𝓘(ℝ, realSpinLieModel n).prod (𝓡 1)) (𝓘(ℝ, realSpinLieModel n).prod (𝓡 1)) ∞
      (chargeConj (realCliffordForm n 0) hQ) := by
  apply (contMDiff_iff_contMDiff_comp_mk n hQ _).mpr
  simpa only [Function.comp_def, MulEquiv.coe_toEquiv, chargeConj_mk] using
    (isLocalDiffeomorph_realMk n hQ).contMDiff.comp (contMDiff_fst.prodMk contMDiff_snd.inv)

/-- The defining central quotient map `Spin(n) × U(1) → Spinᶜ(n)` as a smooth homomorphism. -/
def realMkSmoothHom :
    ContMDiffMonoidMorphism (𝓘(ℝ, realSpinLieModel n).prod (𝓡 1))
      (𝓘(ℝ, realSpinLieModel n).prod (𝓡 1)) ∞
      (spinGroup (realCliffordForm n 0) × Circle) (spinCGroup (realCliffordForm n 0) hQ) where
  toMonoidHom := mk (realCliffordForm n 0) hQ
  contMDiff_toFun := (isLocalDiffeomorph_realMk n hQ).contMDiff

@[simp]
theorem realMkSmoothHom_apply (p : spinGroup (realCliffordForm n 0) × Circle) :
    realMkSmoothHom n hQ p = mk (realCliffordForm n 0) hQ p :=
  (rfl)

/-- The smooth quotient homomorphism `realMkSmoothHom` is a smooth local diffeomorphism. -/
theorem isLocalDiffeomorph_realMkSmoothHom :
    IsLocalDiffeomorph (𝓘(ℝ, realSpinLieModel n).prod (𝓡 1))
      (𝓘(ℝ, realSpinLieModel n).prod (𝓡 1)) ∞ (realMkSmoothHom n hQ) :=
  isLocalDiffeomorph_realMk n hQ

/-- The canonical inclusion `Spin(n) → Spinᶜ(n)` as a smooth homomorphism. -/
def realOfSpinSmoothHom :
    ContMDiffMonoidMorphism 𝓘(ℝ, realSpinLieModel n) (𝓘(ℝ, realSpinLieModel n).prod (𝓡 1)) ∞
      (spinGroup (realCliffordForm n 0)) (spinCGroup (realCliffordForm n 0) hQ) :=
  (realMkSmoothHom n hQ).comp ContMDiffMonoidMorphism.inl

@[simp]
theorem realMkSmoothHom_comp_inl :
    (realMkSmoothHom n hQ).comp ContMDiffMonoidMorphism.inl = realOfSpinSmoothHom n hQ :=
  (rfl)

@[simp]
theorem realOfSpinSmoothHom_apply (s : spinGroup (realCliffordForm n 0)) :
    realOfSpinSmoothHom n hQ s = ofSpin (realCliffordForm n 0) hQ s := by
  simp only [realOfSpinSmoothHom, ContMDiffMonoidMorphism.coe_comp, Function.comp_apply,
    ContMDiffMonoidMorphism.coe_inl, realMkSmoothHom_apply, ofSpin_apply]

end CliffordAlgebra.spinCGroup
