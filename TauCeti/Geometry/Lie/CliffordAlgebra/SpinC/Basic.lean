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

The line `ℂ` with `Spinᶜ(n)` acting smoothly through the determinant character is
`CliffordAlgebra.spinCGroup.DetFiber`, the model fiber of the determinant line of a principal
`Spinᶜ(n)`-bundle.

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

/-! ### The determinant representation -/

/-- The model fiber `ℂ` of the determinant line of a `Spinᶜ(n)`-bundle, on which `Spinᶜ(n)`
acts through its determinant character `[s, z] ↦ z²` (`CliffordAlgebra.spinCGroup.det`). -/
@[expose]
def DetFiber (_n : ℕ) (_hQ : realCliffordForm _n 0 ≠ 0) : Type := ℂ

namespace DetFiber

instance : NormedAddCommGroup (DetFiber n hQ) := inferInstanceAs (NormedAddCommGroup ℂ)

instance : NormedSpace ℂ (DetFiber n hQ) := inferInstanceAs (NormedSpace ℂ ℂ)

/-- The model determinant fiber is the line `ℂ`. -/
def linearEquiv : DetFiber n hQ ≃ₗ[ℂ] ℂ := LinearEquiv.refl ℂ ℂ

/-- The identification of the model determinant fiber with `ℂ` is the identity of `ℂ`. -/
@[simp]
theorem linearEquiv_apply (w : DetFiber n hQ) : linearEquiv n hQ w = w := (rfl)

/-- The inverse identification of `ℂ` with the model determinant fiber is the identity of `ℂ`. -/
@[simp]
theorem linearEquiv_symm_apply (z : ℂ) : (linearEquiv n hQ).symm z = z := (rfl)

/-- The model determinant fiber is a line. -/
@[simp]
theorem finrank_eq : Module.finrank ℂ (DetFiber n hQ) = 1 :=
  (linearEquiv n hQ).finrank_eq.trans (Module.finrank_self ℂ)

instance : FiniteDimensional ℂ (DetFiber n hQ) := inferInstanceAs (FiniteDimensional ℂ ℂ)

/-- `Spinᶜ(n)` acts on the model determinant fiber through its determinant character. -/
instance : DistribMulAction (spinCGroup (realCliffordForm n 0) hQ) (DetFiber n hQ) :=
  DistribMulAction.compHom ℂ (Circle.coeHom.comp (det (realCliffordForm n 0) hQ))

/-- `Spinᶜ(n)` acts on the model determinant fiber by its determinant character. -/
theorem smul_def (x : spinCGroup (realCliffordForm n 0) hQ) (w : DetFiber n hQ) :
    x • w = (det (realCliffordForm n 0) hQ x : ℂ) • w := (rfl)

instance : SMulCommClass (spinCGroup (realCliffordForm n 0) hQ) ℂ (DetFiber n hQ) where
  smul_comm x c w := by simp only [smul_def, smul_comm (det _ hQ x : ℂ) c w]

instance : SMulCommClass (spinCGroup (realCliffordForm n 0) hQ) ℝ (DetFiber n hQ) where
  smul_comm x c w := by simp only [smul_def, smul_comm (det _ hQ x : ℂ) c w]

/-- The determinant action is smooth. -/
instance : ContMDiffSMul (𝓘(ℝ, realSpinLieModel n).prod (𝓡 1)) 𝓘(ℝ, DetFiber n hQ) ∞
    (spinCGroup (realCliffordForm n 0) hQ) (DetFiber n hQ) where
  contMDiff_smul := by
    simp only [smul_def]
    have := finrank_real_complex_fact'
    exact (contDiff_fst.smul contDiff_snd).contMDiff.comp
      (((contMDiff_coe_sphere.comp (contMDiff_realDet n hQ)).comp contMDiff_fst).prodMk_space
        contMDiff_snd)

instance : ContinuousSMul (spinCGroup (realCliffordForm n 0) hQ) (DetFiber n hQ) :=
  ContMDiffSMul.continuousSMul (I := 𝓘(ℝ, realSpinLieModel n).prod (𝓡 1))
    (I' := 𝓘(ℝ, DetFiber n hQ)) ∞

end DetFiber

end CliffordAlgebra.spinCGroup
