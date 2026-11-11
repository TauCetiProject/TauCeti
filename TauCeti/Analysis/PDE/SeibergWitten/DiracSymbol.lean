/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.HalfSpinor
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Comparing the chiral Dirac symbol conventions

For finite-dimensional complex Clifford modules we construct the operator-valued homotopy
`exp(π t i / 2) c(v)`. At `t = 0` this is the differential-symbol convention `c(v)`, and at
`t = 1` it is the Fourier-symbol convention `i c(v)`. For `Q(v) = -‖v‖²`, every intermediate map
is invertible off the zero section, with an explicit inverse between opposite chirality spaces.
This is the pointwise input for showing that the scalar convention does not change the chiral
symbol class, not a construction of a differential operator or its analytic index.

The inverse uses `CliffordAlgebra.halfSpinCliffordMulEquiv`: Clifford multiplication by a
nonisotropic vector has inverse `c(v) / Q(v)`, or `-c(v) / ‖v‖²` for the negative metric
convention. No irreducibility or rank-two assumption is needed.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter II, §5.
* J. W. Morgan, *The Seiberg–Witten equations and applications to the topology of smooth
  four-manifolds* (1996), §3.1.
-/

public section

noncomputable section

namespace CliffordAlgebra

open Module Module.End

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [Fact (finrank ℝ V = 4)] {Q : QuadraticForm ℝ V}
  (o : Orientation ℝ V (Fin 4))

section Topology

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W]
  [FiniteDimensional ℂ W] (ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ W) (ε : ℂ)

/-- The chiral symbol homotopy from `c(v)` to `i c(v)`, in the operator-norm topology. -/
def halfSpinSymbolHomotopy (t : ℝ) (v : V) :
    eigenspace (ρ (chirality Q o)) ε →L[ℂ] eigenspace (ρ (chirality Q o)) (-ε) :=
  Complex.exp (((Real.pi / 2 * t : ℝ) : ℂ) * Complex.I) •
    (halfSpinCliffordMul o ρ ε v).toContinuousLinearMap

/-- Evaluation of the symbol homotopy on a spinor, in the ambient Clifford module. -/
@[simp]
theorem coe_halfSpinSymbolHomotopy_apply (t : ℝ) (v : V)
    (ψ : eigenspace (ρ (chirality Q o)) ε) :
    (halfSpinSymbolHomotopy o ρ ε t v ψ : W) =
      Complex.exp (((Real.pi / 2 * t : ℝ) : ℂ) * Complex.I) • ρ (ι Q v) ψ := by
  simp [halfSpinSymbolHomotopy]

/-- The initial endpoint is Clifford multiplication, the differential-symbol convention. -/
@[simp]
theorem halfSpinSymbolHomotopy_zero (v : V) :
    halfSpinSymbolHomotopy o ρ ε 0 v =
      (halfSpinCliffordMul o ρ ε v).toContinuousLinearMap := by
  simp [halfSpinSymbolHomotopy]

/-- The final endpoint is `i c(v)`, the Fourier-symbol convention. -/
@[simp]
theorem halfSpinSymbolHomotopy_one (v : V) :
    halfSpinSymbolHomotopy o ρ ε 1 v =
      Complex.I • (halfSpinCliffordMul o ρ ε v).toContinuousLinearMap := by
  simp [halfSpinSymbolHomotopy, Complex.exp_pi_div_two_mul_I]

/-- The symbol homotopy is jointly continuous in its parameter and vector. -/
theorem continuous_halfSpinSymbolHomotopy :
    Continuous (fun p : ℝ × V ↦ halfSpinSymbolHomotopy o ρ ε p.1 p.2) := by
  exact (Complex.continuous_exp.comp
    ((Complex.continuous_ofReal.comp (continuous_const.mul continuous_fst)).mul
      continuous_const)).smul
        ((continuous_halfSpinCliffordMul_toContinuousLinearMap o ρ ε).comp continuous_snd)

/-- The symbol homotopy remains zero on the zero section. -/
@[simp]
theorem halfSpinSymbolHomotopy_zero_right (t : ℝ) :
    halfSpinSymbolHomotopy o ρ ε t 0 = 0 := by
  ext ψ
  simp

/-- The symbol homotopy as a continuous linear equivalence off the isotropic cone. -/
def halfSpinSymbolHomotopyEquiv (t : ℝ) {v : V} (hv : Q v ≠ 0) :
    eigenspace (ρ (chirality Q o)) ε ≃L[ℂ] eigenspace (ρ (chirality Q o)) (-ε) :=
  ((halfSpinCliffordMulEquiv o ρ ε hv).trans
    (LinearEquiv.smulOfNeZero ℂ _
      (Complex.exp (((Real.pi / 2 * t : ℝ) : ℂ) * Complex.I))
      (Complex.exp_ne_zero _))).toContinuousLinearEquiv

/-- The equivalence acts by the phase-scaled Clifford multiplication on the ambient module. -/
@[simp]
theorem coe_halfSpinSymbolHomotopyEquiv_apply (t : ℝ) {v : V} (hv : Q v ≠ 0)
    (ψ : eigenspace (ρ (chirality Q o)) ε) :
    (halfSpinSymbolHomotopyEquiv o ρ ε t hv ψ : W) =
      Complex.exp (((Real.pi / 2 * t : ℝ) : ℂ) * Complex.I) • ρ (ι Q v) ψ := by
  simp [halfSpinSymbolHomotopyEquiv]

/-- The equivalence off the isotropic cone has the specified homotopy as its forward map. -/
@[simp]
theorem halfSpinSymbolHomotopyEquiv_toContinuousLinearMap (t : ℝ) {v : V} (hv : Q v ≠ 0) :
    (halfSpinSymbolHomotopyEquiv o ρ ε t hv).toContinuousLinearMap =
      halfSpinSymbolHomotopy o ρ ε t v := by
  ext ψ
  simp

/-- All intermediate symbols are invertible at every nonisotropic vector. -/
theorem halfSpinSymbolHomotopy_bijective (t : ℝ) {v : V} (hv : Q v ≠ 0) :
    Function.Bijective (halfSpinSymbolHomotopy o ρ ε t v) := by
  rw [← halfSpinSymbolHomotopyEquiv_toContinuousLinearMap o ρ ε t hv]
  exact (halfSpinSymbolHomotopyEquiv o ρ ε t hv).bijective

/-- The inverse homotopy symbol is `exp(-π t i / 2) c(v) / Q(v)`, acting from the
`-ε`-chirality space back to the `ε`-chirality space. -/
@[simp]
theorem coe_halfSpinSymbolHomotopyEquiv_symm_apply (t : ℝ) {v : V} (hv : Q v ≠ 0)
    (χ : eigenspace (ρ (chirality Q o)) (-ε)) :
    ((halfSpinSymbolHomotopyEquiv o ρ ε t hv).symm χ : W) =
      (Complex.exp (-(((Real.pi / 2 * t : ℝ) : ℂ) * Complex.I)) * (Q v : ℂ)⁻¹) •
        ρ (ι Q v) χ := by
  simp [halfSpinSymbolHomotopyEquiv, LinearEquiv.trans_symm, Units.smul_def,
    smul_smul, Complex.exp_neg, mul_comm]

end Topology

section Hermitian

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
  [FiniteDimensional ℂ W] {ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ W} (ε : ℂ)

/-- On a Hermitian Clifford module, every map in the homotopy scales norms by `‖v‖`. -/
theorem norm_halfSpinSymbolHomotopy_apply (hQ : ∀ v, Q v = -‖v‖ ^ 2)
    (hρ : ∀ v, LinearMap.adjoint (ρ (ι Q v)) = -ρ (ι Q v)) (t : ℝ) (v : V)
    (ψ : eigenspace (ρ (chirality Q o)) ε) :
    ‖halfSpinSymbolHomotopy o ρ ε t v ψ‖ = ‖v‖ * ‖ψ‖ := by
  simp only [← Submodule.norm_coe, coe_halfSpinSymbolHomotopy_apply, norm_smul,
    Complex.norm_exp_ofReal_mul_I, one_mul, norm_map_ι_apply hQ hρ]

end Hermitian

end CliffordAlgebra
