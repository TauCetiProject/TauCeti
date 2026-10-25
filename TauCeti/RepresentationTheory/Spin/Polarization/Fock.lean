/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.LinearAlgebra.CliffordAlgebra.BaseChange
public import TauCeti.RepresentationTheory.Spin.Polarization.ComplexStructure
public import TauCeti.RepresentationTheory.Spin.Polarization.DegreeScaling

/-!
# The normalized Fock action of a complex structure

Let `Q` be a nondegenerate quadratic form on a finite-dimensional real vector space `V` and `J` an
almost complex structure preserving `Q`. The `i`-eigenspace `W` of the complexified complex
structure and the `-i`-eigenspace `W'` polarize `Q.baseChange ℂ`
(`TauCeti.AlmostComplexStructure.spinPolarizationData`), so `TauCeti.spinAction` makes `⋀ W` a
module over the complexified Clifford algebra. On a real vector `v`, with
`1 ⊗ v = v^(1,0) + v^(0,1)`, this native action is exterior multiplication by `v^(1,0)` plus
contraction against the polar form `QuadraticMap.polar (Q.baseChange ℂ) · v^(0,1)`.

In the geometric convention `Q (v) = -g (v, v)` for a metric `g`, the polar form is `-2 g_ℂ`, so
the native action is `ε(v^(1,0)) - 2 ι(v^(0,1))`, where `ι` contracts against `g_ℂ`. Its two
halves carry different factors. Conjugating by the degree scaling `T` of `⋀ W` by `√2`, which acts
on `⋀^p W` by `√2 ^ p = 2 ^ (p / 2)`, gives the `√2`-normalized Fock action
`c(v) = √2 (ε(v^(1,0)) - ι(v^(0,1)))`, in which both halves carry the factor `√2`. This file
defines that action and proves the intertwining equation `T ∘ spinAction a = fockAction a ∘ T`
together with the formula for `c(v)`.

## Main definitions

* `TauCeti.AlmostComplexStructure.fockAction`: the `√2`-normalized Fock action.
* `TauCeti.AlmostComplexStructure.realFockAction`: its restriction to the real Clifford algebra
  `CliffordAlgebra Q`, making `⋀ W` a complex Clifford module of the real space `(V, Q)`.

## Main results

* `TauCeti.AlmostComplexStructure.spinAction_ι_one_tmul`: the native action of a real vector.
* `TauCeti.AlmostComplexStructure.degreeScaling_comp_spinAction_eq_fockAction_comp`: the degree
  scaling by `√2` intertwines the native action with the normalized one.
* `TauCeti.AlmostComplexStructure.fockAction_ι_one_tmul`: the normalized action of a real vector,
  `c(v) = √2 (ε(v^(1,0)) + (1/2) · contraction against polar (Q.baseChange ℂ) · v^(0,1))`.
* `TauCeti.AlmostComplexStructure.fockAction_ι_one_tmul_mul_self`: the Clifford relation
  `c(v) ^ 2 = Q v`, which is `-|v|² Id` in the geometric convention.
* `TauCeti.AlmostComplexStructure.fockAction_ι_coe_W`: a vector of `W` acts by `√2` times
  exterior multiplication.
* `TauCeti.AlmostComplexStructure.realFockAction_ι`: a real generator `ι Q v` acts by `c(v)`.
* `TauCeti.AlmostComplexStructure.realFockAction_ι_mul_ι_apply_apply_one`: on the vacuum,
  `c(u) c(J u) 1 = i Q(u)`.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I §5.
-/

public section

open CliffordAlgebra ExteriorAlgebra
open TauCeti.ExteriorAlgebra
open scoped TensorProduct

namespace TauCeti.AlmostComplexStructure

universe u

variable {V : Type u} [AddCommGroup V] [Module ℝ V] (J : AlmostComplexStructure V)
  {Q : QuadraticForm ℝ V} [FiniteDimensional ℝ V] (hQJ : ∀ v, Q (J v) = Q v)
  (hQ : Q.Nondegenerate)

/-- The rescaled action of a real vector splits into its holomorphic creation part and
antiholomorphic contraction part. -/
theorem scaledSpinAction_ι_one_tmul (r : ℂˣ) (v : V) :
    (J.spinPolarizationData hQJ hQ).scaledSpinAction r
        (ι (Q.baseChange ℂ) ((1 : ℂ) ⊗ₜ v)) =
      (r : ℂ) • (J.spinPolarizationData hQJ hQ).wedge
          ⟨J.holomorphicPart v, J.holomorphicPart_mem_spinPolarizationData_W hQJ hQ v⟩ +
        ((r⁻¹ : ℂˣ) : ℂ) • (J.spinPolarizationData hQJ hQ).contract
          ⟨J.antiholomorphicPart v,
            J.antiholomorphicPart_mem_spinPolarizationData_W' hQJ hQ v⟩ := by
  have hW := (J.spinPolarizationData hQJ hQ).scaledSpinAction_ι_coe_W r
    ⟨J.holomorphicPart v, J.holomorphicPart_mem_spinPolarizationData_W hQJ hQ v⟩
  have hW' := (J.spinPolarizationData hQJ hQ).scaledSpinAction_ι_coe_W' r
    ⟨J.antiholomorphicPart v, J.antiholomorphicPart_mem_spinPolarizationData_W' hQJ hQ v⟩
  -- Reduce the subtype coercions before using the common holomorphic decomposition.
  dsimp only at hW hW'
  rw [← J.holomorphicPart_add_antiholomorphicPart v, map_add, map_add, hW, hW']

private noncomputable def sqrtTwoUnit : ℂˣ :=
  Units.mk0 (Real.sqrt 2 : ℂ) (by norm_num)

private theorem coe_sqrtTwoUnit : (sqrtTwoUnit : ℂ) = Real.sqrt 2 := rfl

/-- **The native action of a real vector** on the spinor module `⋀ W` of the polarization by a
complex structure: exterior multiplication by `v^(1,0)` plus contraction against
`QuadraticMap.polar (Q.baseChange ℂ) · v^(0,1)`. -/
theorem spinAction_ι_one_tmul (v : V) :
    spinAction _ (J.spinPolarizationData hQJ hQ) (ι (Q.baseChange ℂ) ((1 : ℂ) ⊗ₜ v)) =
      (J.spinPolarizationData hQJ hQ).wedge
          ⟨J.holomorphicPart v, J.holomorphicPart_mem_spinPolarizationData_W hQJ hQ v⟩ +
        (J.spinPolarizationData hQJ hQ).contract
          ⟨J.antiholomorphicPart v,
            J.antiholomorphicPart_mem_spinPolarizationData_W' hQJ hQ v⟩ := by
  simpa only [SpinPolarizationData.scaledSpinAction_one, inv_one, Units.val_one, one_smul]
    using J.scaledSpinAction_ι_one_tmul hQJ hQ 1 v

/-- **The `√2`-normalized Fock action** of the complexified Clifford algebra on `⋀ W`: the
conjugate of the native action `TauCeti.spinAction` by the degree scaling of `⋀ W` by `√2`. A real
vector `v` acts by `√2 (ε(v^(1,0)) - ι(v^(0,1)))`, where `ι` contracts against the complex-bilinear
form `g_ℂ = -polar Q_ℂ / 2` (`TauCeti.AlmostComplexStructure.fockAction_ι_one_tmul`). -/
noncomputable def fockAction :
    CliffordAlgebra (Q.baseChange ℂ) →ₐ[ℂ]
      Module.End ℂ (ExteriorAlgebra ℂ (J.spinPolarizationData hQJ hQ).W) :=
  (J.spinPolarizationData hQJ hQ).scaledSpinAction sqrtTwoUnit

/-- The normalized Fock action is the rescaled spinor representation for any unit of value
`√2`. -/
theorem fockAction_eq_scaledSpinAction {r : ℂˣ} (hr : (r : ℂ) = Real.sqrt 2) :
    J.fockAction hQJ hQ = (J.spinPolarizationData hQJ hQ).scaledSpinAction r := by
  rw [fockAction]
  exact congrArg _ (Units.ext (coe_sqrtTwoUnit.trans hr.symm))

/-- **The degree scaling by `√2` intertwines the native and the normalized Fock actions**:
`T ∘ spinAction a = fockAction a ∘ T`, where `T` multiplies `⋀^p W` by `√2 ^ p`
(`TauCeti.ExteriorAlgebra.degreeScaling_of_mem_exteriorPower`). -/
theorem degreeScaling_comp_spinAction_eq_fockAction_comp {r : ℂˣ}
    (hr : (r : ℂ) = Real.sqrt 2) (a : CliffordAlgebra (Q.baseChange ℂ)) :
    (degreeScaling r).toLinearMap ∘ₗ spinAction _ (J.spinPolarizationData hQJ hQ) a =
      J.fockAction hQJ hQ a ∘ₗ (degreeScaling r).toLinearMap := by
  rw [J.fockAction_eq_scaledSpinAction hQJ hQ hr]
  exact (J.spinPolarizationData hQJ hQ).degreeScaling_comp_spinAction r a

/-- **The normalized Fock action of a real vector**: `c(v)` is `√2` times exterior multiplication
by `v^(1,0)` plus `√2 / 2` times contraction against
`QuadraticMap.polar (Q.baseChange ℂ) · v^(0,1)`. In the geometric convention `Q (v) = -g (v, v)`
that contraction is `-2 ι(v^(0,1))` for the contraction `ι` against `g_ℂ`, so this is
`c(v) = √2 (ε(v^(1,0)) - ι(v^(0,1)))`. -/
theorem fockAction_ι_one_tmul (v : V) :
    J.fockAction hQJ hQ (ι (Q.baseChange ℂ) ((1 : ℂ) ⊗ₜ v)) =
      (Real.sqrt 2 : ℂ) • ((J.spinPolarizationData hQJ hQ).wedge
          ⟨J.holomorphicPart v, J.holomorphicPart_mem_spinPolarizationData_W hQJ hQ v⟩ +
        (2 : ℂ)⁻¹ • (J.spinPolarizationData hQJ hQ).contract
          ⟨J.antiholomorphicPart v,
            J.antiholomorphicPart_mem_spinPolarizationData_W' hQJ hQ v⟩) := by
  have hsqrt : (Real.sqrt 2 : ℂ) * Real.sqrt 2 = 2 := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt zero_le_two, Complex.ofReal_ofNat]
  have hinv : (Real.sqrt 2 : ℂ)⁻¹ = Real.sqrt 2 * 2⁻¹ :=
    inv_eq_of_mul_eq_one_right (by rw [← mul_assoc, hsqrt, mul_inv_cancel₀ two_ne_zero])
  rw [J.fockAction_eq_scaledSpinAction hQJ hQ coe_sqrtTwoUnit,
    J.scaledSpinAction_ι_one_tmul hQJ hQ, Units.val_inv_eq_inv_val, coe_sqrtTwoUnit,
    hinv, smul_add, smul_smul]

/-- **The Clifford relation for the normalized Fock action**: `c(v) ^ 2 = Q v`. In the geometric
convention `Q (v) = -g (v, v)` this is `c(v) ^ 2 = -|v|² Id`. -/
theorem fockAction_ι_one_tmul_mul_self (v : V) :
    J.fockAction hQJ hQ (ι (Q.baseChange ℂ) ((1 : ℂ) ⊗ₜ v)) *
        J.fockAction hQJ hQ (ι (Q.baseChange ℂ) ((1 : ℂ) ⊗ₜ v)) =
      algebraMap ℂ _ (Q v : ℂ) := by
  rw [← map_mul, ι_sq_scalar, AlgHom.commutes, QuadraticForm.baseChange_tmul, mul_one,
    Complex.real_smul, mul_one]

/-- In the normalized Fock action a vector of `W` acts by `√2` times exterior multiplication. -/
theorem fockAction_ι_coe_W (x : (J.spinPolarizationData hQJ hQ).W) :
    J.fockAction hQJ hQ (ι (Q.baseChange ℂ) (x : ℂ ⊗[ℝ] V)) =
      (Real.sqrt 2 : ℂ) • (J.spinPolarizationData hQJ hQ).wedge x := by
  rw [J.fockAction_eq_scaledSpinAction hQJ hQ coe_sqrtTwoUnit,
    SpinPolarizationData.scaledSpinAction_ι_coe_W, coe_sqrtTwoUnit]

/-- **The Fock action of the real Clifford algebra**: the normalized Fock action
`TauCeti.AlmostComplexStructure.fockAction` restricted along the canonical map
`CliffordAlgebra.ofBaseChangeAux : CliffordAlgebra Q → CliffordAlgebra (Q.baseChange ℂ)`, which
sends `ι Q v` to `ι (1 ⊗ v)`. It makes `⋀ W` a complex Clifford module of the real quadratic
space `(V, Q)`, on which a real vector `v` acts by `c(v) = √2 (ε(v^(1,0)) - ι(v^(0,1)))`. -/
noncomputable def realFockAction :
    CliffordAlgebra Q →ₐ[ℝ]
      Module.End ℂ (ExteriorAlgebra ℂ (J.spinPolarizationData hQJ hQ).W) :=
  ((J.fockAction hQJ hQ).restrictScalars ℝ).comp (ofBaseChangeAux ℂ Q)

/-- Unfolding lemma for `TauCeti.AlmostComplexStructure.realFockAction`. -/
theorem realFockAction_apply (a : CliffordAlgebra Q) :
    J.realFockAction hQJ hQ a = J.fockAction hQJ hQ (ofBaseChangeAux ℂ Q a) :=
  (rfl)

/-- In the real Fock action a real generator `ι Q v` acts by the normalized Fock operator
`c(v)` of `1 ⊗ v`. -/
@[simp]
theorem realFockAction_ι (v : V) :
    J.realFockAction hQJ hQ (ι Q v) = J.fockAction hQJ hQ (ι (Q.baseChange ℂ) ((1 : ℂ) ⊗ₜ v)) := by
  rw [realFockAction_apply, ofBaseChangeAux_ι]

/-- **The Fock operators of `u` and `J u` on the vacuum**: `c(u) c(J u) 1 = i Q(u)` for the
vacuum `1` of `⋀ W`. -/
theorem realFockAction_ι_mul_ι_apply_apply_one (u : V) :
    J.realFockAction hQJ hQ (ι Q u * ι Q (J u)) 1 = (Complex.I * Q u) • 1 := by
  set P := J.spinPolarizationData hQJ hQ
  have hW : (⟨J.holomorphicPart (J u), J.holomorphicPart_mem_spinPolarizationData_W hQJ hQ _⟩ :
      P.W) = Complex.I • ⟨J.holomorphicPart u,
        J.holomorphicPart_mem_spinPolarizationData_W hQJ hQ u⟩ :=
    Subtype.ext (J.holomorphicPart_apply_apply u)
  have hpolar : QuadraticMap.polar (Q.baseChange ℂ) (J.holomorphicPart u)
      (J.antiholomorphicPart u) = Q u := by
    have h0 : QuadraticMap.polar Q u (J u) = 0 :=
      J.bilinForm_apply_apply_self_eq_zero (g := Q.polarBilin) ⟨QuadraticMap.polar_comm Q⟩
        (J.polar_apply_apply hQJ) u
    rw [J.polar_holomorphicPart_antiholomorphicPart hQJ, h0, QuadraticMap.polar_self]
    push_cast
    ring
  have hsqrt : (Real.sqrt 2 : ℂ) * Real.sqrt 2 = 2 := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt zero_le_two, Complex.ofReal_ofNat]
  simp only [map_mul, Module.End.mul_apply, realFockAction_ι, fockAction_ι_one_tmul,
    LinearMap.smul_apply, LinearMap.add_apply, SpinPolarizationData.wedge_apply,
    SpinPolarizationData.contract_apply, hW, map_smul, mul_one, contractLeft_one, smul_zero,
    add_zero, smul_add, ExteriorAlgebra.ι_sq_zero, contractLeft_ι,
    SpinPolarizationData.pairingEquiv_apply, hpolar, Algebra.algebraMap_eq_smul_one]
  match_scalars
  linear_combination (Complex.I * (Q u : ℂ) / 2) * hsqrt

end TauCeti.AlmostComplexStructure
