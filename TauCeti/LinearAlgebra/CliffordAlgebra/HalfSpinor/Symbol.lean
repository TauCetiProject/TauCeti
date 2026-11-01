/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.HalfSpinor.Basic
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Inverting the chiral Clifford symbol

Clifford multiplication by a nonisotropic vector identifies opposite chirality spaces. Its
inverse is `c(v) / Q(v)`, with the opposite source and target. For the geometric convention
`Q(v) = -‖v‖²` this is `-c(v) / ‖v‖²`. No irreducibility or rank-two assumption is needed.

For finite-dimensional complex Clifford modules we also construct the operator-valued homotopy
`exp(π t i / 2) c(v)`. At `t = 0` this is the differential-symbol convention `c(v)`, and at
`t = 1` it is the Fourier-symbol convention `i c(v)`. For `Q(v) = -‖v‖²`, every intermediate map
is invertible off the zero section, with an explicit inverse between opposite chirality spaces.
Thus changing the scalar convention preserves the chiral symbol class. This is pointwise symbol
algebra, not a construction of a differential operator or its analytic index.

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

section Algebra

variable {W : Type*} [AddCommGroup W] [Module ℂ W]
  (ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ W) (ε : ℂ)

/-- Clifford multiplication by a nonisotropic vector, as an equivalence between opposite
chirality spaces. The inverse is Clifford multiplication divided by `Q v`. -/
def halfSpinCliffordMulEquiv {v : V} (hv : Q v ≠ 0) :
    eigenspace (ρ (chirality Q o)) ε ≃ₗ[ℂ] eigenspace (ρ (chirality Q o)) (-ε) where
  toLinearMap := halfSpinCliffordMul o ρ ε v
  invFun χ := ⟨((Q v : ℂ)⁻¹) • ρ (ι Q v) χ, by
    apply Submodule.smul_mem
    simpa only [neg_neg] using map_ι_apply_mem_eigenspace_chirality_neg o χ.property v⟩
  left_inv ψ := by
    apply Subtype.ext
    simp only [LinearMap.toFun_eq_coe, coe_halfSpinCliffordMul_apply_apply,
      map_ι_apply_map_ι_apply, smul_smul]
    rw [inv_mul_cancel₀ (by exact_mod_cast hv), one_smul]
  right_inv χ := by
    apply Subtype.ext
    simp only [LinearMap.toFun_eq_coe, coe_halfSpinCliffordMul_apply_apply,
      map_smul, map_ι_apply_map_ι_apply, smul_smul]
    rw [inv_mul_cancel₀ (by exact_mod_cast hv), one_smul]

/-- The chiral equivalence has the original Clifford multiplication as its forward map. -/
@[simp]
theorem halfSpinCliffordMulEquiv_toLinearMap {v : V} (hv : Q v ≠ 0) :
    (halfSpinCliffordMulEquiv o ρ ε hv).toLinearMap = halfSpinCliffordMul o ρ ε v :=
  (rfl)

/-- The chiral equivalence acts by Clifford multiplication on the ambient module. -/
@[simp]
theorem coe_halfSpinCliffordMulEquiv_apply {v : V} (hv : Q v ≠ 0)
    (ψ : eigenspace (ρ (chirality Q o)) ε) :
    (halfSpinCliffordMulEquiv o ρ ε hv ψ : W) = ρ (ι Q v) ψ :=
  coe_halfSpinCliffordMul_apply_apply o (ρ := ρ) ε v ψ

/-- The inverse chiral symbol has opposite source and target and is `c(v) / Q(v)`. -/
@[simp]
theorem coe_halfSpinCliffordMulEquiv_symm_apply {v : V} (hv : Q v ≠ 0)
    (χ : eigenspace (ρ (chirality Q o)) (-ε)) :
    ((halfSpinCliffordMulEquiv o ρ ε hv).symm χ : W) =
      (Q v : ℂ)⁻¹ • ρ (ι Q v) χ :=
  (rfl)

/-- With the negative metric convention, the inverse chiral symbol is `-c(v) / ‖v‖²`. -/
theorem coe_halfSpinCliffordMulEquiv_symm_apply_of_neg_norm_sq
    (hQ : ∀ v, Q v = -‖v‖ ^ 2) {v : V} (hv : v ≠ 0)
    (χ : eigenspace (ρ (chirality Q o)) (-ε)) :
    ((halfSpinCliffordMulEquiv o ρ ε (v := v) (by simpa [hQ] using hv)).symm χ : W) =
      -((‖v‖ : ℂ) ^ 2)⁻¹ • ρ (ι Q v) χ := by
  simp [hQ]

end Algebra

section Topology

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W]
  [FiniteDimensional ℂ W] (ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ W) (ε : ℂ)

/-- The dimension hypothesis gives the vector space its finite-dimensional topology. -/
local instance : FiniteDimensional ℝ V := .of_fact_finrank_eq_succ 3

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
  have : ContinuousSMul ℝ (eigenspace (ρ (chirality Q o)) ε →L[ℂ]
      eigenspace (ρ (chirality Q o)) (-ε)) := IsScalarTower.continuousSMul ℂ
  let L : V →ₗ[ℝ] (eigenspace (ρ (chirality Q o)) ε →L[ℂ]
      eigenspace (ρ (chirality Q o)) (-ε)) :=
    { toFun := fun v ↦ (halfSpinCliffordMul o ρ ε v).toContinuousLinearMap
      map_add' := fun v w ↦ by ext ψ; simp
      map_smul' := fun r v ↦ by ext ψ; simp }
  exact (Complex.continuous_exp.comp
    ((Complex.continuous_ofReal.comp (continuous_const.mul continuous_fst)).mul
      continuous_const)).smul (L.continuous_of_finiteDimensional.comp continuous_snd)

/-- The symbol homotopy remains zero on the zero section. -/
@[simp]
theorem halfSpinSymbolHomotopy_apply_zero (t : ℝ) :
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

/-- The equivalence off the isotropic cone has the specified homotopy as its forward map. -/
@[simp]
theorem halfSpinSymbolHomotopyEquiv_toContinuousLinearMap (t : ℝ) {v : V} (hv : Q v ≠ 0) :
    (halfSpinSymbolHomotopyEquiv o ρ ε t hv).toContinuousLinearMap =
      halfSpinSymbolHomotopy o ρ ε t v := by
  ext ψ
  rfl

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
  rw [← Submodule.norm_coe, coe_halfSpinSymbolHomotopy_apply, norm_smul,
    Complex.norm_exp_ofReal_mul_I, one_mul, norm_map_ι_apply hQ hρ]
  rfl

end Hermitian

end CliffordAlgebra
