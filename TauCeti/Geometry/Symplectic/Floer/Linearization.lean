/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Energy
public import TauCeti.Geometry.Symplectic.Hamiltonian.Variation
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Local-coordinate linearization of the inhomogeneous Floer equation

The nonlinear operator is `∂s u - X_Ks + J(z,u)(∂t u - X_Kt)`. We differentiate it along
jointly `C²` families of maps and Hamiltonians and differentiable families of endomorphisms.
The formula includes the target derivative of `J`, both Hamiltonian linearizations, and the
independent parameter variations of `K` and `J`. Domain dependence of the coefficients is
allowed; the derivative is at a fixed domain point. Along a line `J + q Y` of endomorphism fields
the derivative is `Y(u)(∂t u - X_Kt)` (`hasDerivAt_floerOperator_add_smul`).

`floerLinearization` is the map-direction operator with coefficients fixed. Conjugated by an
exponential weight `e^{δ s}` it becomes `floerLinearization - δ` (`floerLinearization_exp_smul`).
For `C¹` coefficients `J` and `C²` Hamiltonians it is continuous wherever the map and the direction
are `C¹` (`continuousAt_floerLinearization`), so its `L²` norms over compact sets are finite.
It is `∂s ξ + J(z, u z) ∂t ξ` plus a zeroth-order term `floerLinearizationCoeff`
(`floerLinearization_eq_add`), whose coefficient is continuous in `z` where the data are `C¹`
(`continuousAt_floerLinearizationCoeff`, `continuousOn_floerLinearizationCoeff`).
The universal variation theorem identifies its direction field with the actual parameter derivative
of the map, using equality of mixed derivatives rather than assuming it. The endomorphism field need
not square to minus one for differentiation. For an almost complex structure the zero equation
agrees with complex linearity of the existing perturbed derivative. The parameter calculation
extends the unforced formula `TauCeti.fderiv_cauchyRiemannOperator_apply`.

These are local formulas for a constant symplectic form, not an intrinsic connection formula,
a Sobolev operator, or a Fredholm or regularity assertion. See McDuff–Salamon, *J-holomorphic
Curves and Symplectic Topology*, Sections 3.1 and 8.1, for the geometric linearization and
Hamiltonian perturbations.
-/

public section

namespace TauCeti.SymplecticForm

open ContinuousLinearMap

variable {P V : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
variable [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- The local inhomogeneous Floer operator, with convention `ι_X ω = dH`. Its zeros are
`∂s u - X_Ks + J(z,u)(∂t u - X_Kt) = 0`. -/
noncomputable def floerOperator (ω : SymplecticForm V)
    (J : ℝ × ℝ → V → V →L[ℝ] V) (Ks Kt : ℝ × ℝ → V → ℝ)
    (u : ℝ × ℝ → V) (z : ℝ × ℝ) : V :=
  fderiv ℝ u z stdComplexLineReal - ω.hamiltonianVectorField (Ks z) (u z) +
    J z (u z) (fderiv ℝ u z stdComplexLineImag - ω.hamiltonianVectorField (Kt z) (u z))

/-- The coordinate expression of the nonlinear Floer operator. -/
theorem floerOperator_def (ω : SymplecticForm V)
    (J : ℝ × ℝ → V → V →L[ℝ] V) (Ks Kt : ℝ × ℝ → V → ℝ)
    (u : ℝ × ℝ → V) (z : ℝ × ℝ) :
    ω.floerOperator J Ks Kt u z =
      fderiv ℝ u z stdComplexLineReal - ω.hamiltonianVectorField (Ks z) (u z) +
        J z (u z) (fderiv ℝ u z stdComplexLineImag - ω.hamiltonianVectorField (Kt z) (u z)) :=
  (rfl)

/-- For almost complex coefficients, vanishing is complex linearity of `du - X_K`. -/
theorem floerOperator_eq_zero_iff (ω : SymplecticForm V)
    (J : ℝ × ℝ → V → AlmostComplexStructure V) (Ks Kt : ℝ × ℝ → V → ℝ)
    (u : ℝ × ℝ → V) (z : ℝ × ℝ) :
    ω.floerOperator (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) Ks Kt u z = 0 ↔
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z (u z))
        (ω.perturbedFDeriv Ks Kt u z : ℝ × ℝ →ₗ[ℝ] V) := by
  rw [floerOperator_def, ω.isComplexLinearMap_perturbedFDeriv_iff]
  -- The linear and continuous-linear coercions of `J` have the same underlying function.
  rfl

/-- **The `J`-direction derivative of the Floer operator.** Along the line `J + q Y` of
endomorphism fields, the coordinate Floer operator has derivative `Y(u)(∂t u - X_Kt)` at every
parameter `q`. The fields may depend on the domain point. -/
theorem hasDerivAt_floerOperator_add_smul (ω : SymplecticForm V)
    (J Y : ℝ × ℝ → V → V →L[ℝ] V) (Ks Kt : ℝ × ℝ → V → ℝ)
    (u : ℝ × ℝ → V) (z : ℝ × ℝ) (q : ℝ) :
    HasDerivAt (fun q : ℝ ↦ ω.floerOperator (fun w x ↦ J w x + q • Y w x) Ks Kt u z)
      (Y z (u z) (fderiv ℝ u z stdComplexLineImag - ω.hamiltonianVectorField (Kt z) (u z))) q := by
  set ξ := fderiv ℝ u z stdComplexLineImag - ω.hamiltonianVectorField (Kt z) (u z)
  have h (q : ℝ) : ω.floerOperator (fun w x ↦ J w x + q • Y w x) Ks Kt u z =
      ω.floerOperator J Ks Kt u z + q • Y z (u z) ξ := by
    simp only [floerOperator_def, _root_.add_apply, _root_.smul_apply, ξ]
    abel
  simp only [h]
  simpa using
    ((hasDerivAt_id q).smul_const (Y z (u z) ξ)).const_add (ω.floerOperator J Ks Kt u z)

/-- The map-direction linearization with `J` and `K` fixed. Both Hamiltonian derivatives and
the target derivative of `J` are retained, including along constant maps. -/
noncomputable def floerLinearization (ω : SymplecticForm V)
    (J : ℝ × ℝ → V → V →L[ℝ] V) (Ks Kt : ℝ × ℝ → V → ℝ)
    (u ξ : ℝ × ℝ → V) (z : ℝ × ℝ) : V :=
  fderiv ℝ ξ z stdComplexLineReal -
      fderiv ℝ (ω.hamiltonianVectorField (Ks z)) (u z) (ξ z) +
    fderiv ℝ (J z) (u z) (ξ z)
      (fderiv ℝ u z stdComplexLineImag - ω.hamiltonianVectorField (Kt z) (u z)) +
    J z (u z) (fderiv ℝ ξ z stdComplexLineImag -
      fderiv ℝ (ω.hamiltonianVectorField (Kt z)) (u z) (ξ z))

/-- The coordinate expression of the map-direction linearization. -/
theorem floerLinearization_def (ω : SymplecticForm V)
    (J : ℝ × ℝ → V → V →L[ℝ] V) (Ks Kt : ℝ × ℝ → V → ℝ)
    (u ξ : ℝ × ℝ → V) (z : ℝ × ℝ) :
    ω.floerLinearization J Ks Kt u ξ z =
      fderiv ℝ ξ z stdComplexLineReal -
          fderiv ℝ (ω.hamiltonianVectorField (Ks z)) (u z) (ξ z) +
        fderiv ℝ (J z) (u z) (ξ z)
          (fderiv ℝ u z stdComplexLineImag - ω.hamiltonianVectorField (Kt z) (u z)) +
        J z (u z) (fderiv ℝ ξ z stdComplexLineImag -
          fderiv ℝ (ω.hamiltonianVectorField (Kt z)) (u z) (ξ z)) :=
  (rfl)

/-- The linearization is additive on directions differentiable at the domain point. -/
@[simp]
theorem floerLinearization_add (ω : SymplecticForm V)
    (J : ℝ × ℝ → V → V →L[ℝ] V) (Ks Kt : ℝ × ℝ → V → ℝ)
    (u ξ η : ℝ × ℝ → V) (z : ℝ × ℝ) (hξ : DifferentiableAt ℝ ξ z)
    (hη : DifferentiableAt ℝ η z) :
    ω.floerLinearization J Ks Kt u (ξ + η) z =
      ω.floerLinearization J Ks Kt u ξ z + ω.floerLinearization J Ks Kt u η z := by
  simp only [floerLinearization_def, fderiv_add hξ hη, add_apply, Pi.add_apply, map_add,
    map_sub]
  abel

/-- The linearization is subtractive on directions differentiable at the domain point. -/
@[simp]
theorem floerLinearization_sub (ω : SymplecticForm V)
    (J : ℝ × ℝ → V → V →L[ℝ] V) (Ks Kt : ℝ × ℝ → V → ℝ)
    (u ξ η : ℝ × ℝ → V) (z : ℝ × ℝ) (hξ : DifferentiableAt ℝ ξ z)
    (hη : DifferentiableAt ℝ η z) :
    ω.floerLinearization J Ks Kt u (ξ - η) z =
      ω.floerLinearization J Ks Kt u ξ z - ω.floerLinearization J Ks Kt u η z := by
  simp only [floerLinearization_def, fderiv_sub hξ hη, sub_apply, Pi.sub_apply, map_sub]
  abel

/-- The linearization respects real scaling. -/
@[simp]
theorem floerLinearization_smul (ω : SymplecticForm V)
    (J : ℝ × ℝ → V → V →L[ℝ] V) (Ks Kt : ℝ × ℝ → V → ℝ)
    (u ξ : ℝ × ℝ → V) (z : ℝ × ℝ) (c : ℝ) :
    ω.floerLinearization J Ks Kt u (c • ξ) z = c • ω.floerLinearization J Ks Kt u ξ z := by
  simp only [floerLinearization_def, fderiv_const_smul_field c, smul_apply, Pi.smul_apply,
    map_smul, map_sub, smul_sub, smul_add]

/-- The linearization sends the zero direction to zero. -/
@[simp]
theorem floerLinearization_zero (ω : SymplecticForm V)
    (J : ℝ × ℝ → V → V →L[ℝ] V) (Ks Kt : ℝ × ℝ → V → ℝ)
    (u : ℝ × ℝ → V) (z : ℝ × ℝ) :
    ω.floerLinearization J Ks Kt u 0 z = 0 := by
  simp [floerLinearization_def]

/-- **Conjugating the linearization by an exponential weight.** On maps of the form
`e^{-δ s} ξ`, the linearized Floer operator acts as `e^{-δ s} (D - δ) ξ`: the weight only
differentiates in the `s` direction, where the operator has the leading term `∂s`. -/
theorem floerLinearization_exp_smul (ω : SymplecticForm V)
    (J : ℝ × ℝ → V → V →L[ℝ] V) (Ks Kt : ℝ × ℝ → V → ℝ)
    (u ξ : ℝ × ℝ → V) {z : ℝ × ℝ} (δ : ℝ) (hξ : DifferentiableAt ℝ ξ z) :
    ω.floerLinearization J Ks Kt u (fun w ↦ Real.exp (-(δ * w.1)) • ξ w) z =
      Real.exp (-(δ * z.1)) • (ω.floerLinearization J Ks Kt u ξ z - δ • ξ z) := by
  have hc : HasFDerivAt (fun w : ℝ × ℝ ↦ Real.exp (-(δ * w.1)))
      (Real.exp (-(δ * z.1)) • -(δ • ContinuousLinearMap.fst ℝ ℝ ℝ)) z := by
    simpa using ((hasFDerivAt_fst (p := z)).const_smul δ).neg.exp
  have hd : HasFDerivAt (fun w ↦ Real.exp (-(δ * w.1)) • ξ w) _ z := hc.smul hξ.hasFDerivAt
  rw [floerLinearization_def, hd.fderiv, floerLinearization_def]
  simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply, neg_apply,
    ContinuousLinearMap.coe_fst', stdComplexLineReal_fst, stdComplexLineImag_fst, map_smul,
    smul_eq_mul, mul_zero, mul_one, neg_zero, zero_smul, add_zero, map_sub]
  module

/-- The zeroth-order part `ξ ↦ (dJ(u) ξ)(∂t u - X_Kt(u)) - dX_Ks(u) ξ - J(u) dX_Kt(u) ξ` of the
linearized Floer operator at the domain point `z`. -/
noncomputable def floerLinearizationCoeff (ω : SymplecticForm V)
    (J : ℝ × ℝ → V → V →L[ℝ] V) (Ks Kt : ℝ × ℝ → V → ℝ) (u : ℝ × ℝ → V) (z : ℝ × ℝ) :
    V →L[ℝ] V :=
  (fderiv ℝ (J z) (u z)).flip
      (fderiv ℝ u z stdComplexLineImag - ω.hamiltonianVectorField (Kt z) (u z)) -
    fderiv ℝ (ω.hamiltonianVectorField (Ks z)) (u z) -
    (J z (u z)).comp (fderiv ℝ (ω.hamiltonianVectorField (Kt z)) (u z))

/-- The zeroth-order part of the linearized Floer operator, evaluated on a vector. -/
theorem floerLinearizationCoeff_apply (ω : SymplecticForm V)
    (J : ℝ × ℝ → V → V →L[ℝ] V) (Ks Kt : ℝ × ℝ → V → ℝ) (u : ℝ × ℝ → V) (z : ℝ × ℝ) (v : V) :
    ω.floerLinearizationCoeff J Ks Kt u z v =
      fderiv ℝ (J z) (u z) v
          (fderiv ℝ u z stdComplexLineImag - ω.hamiltonianVectorField (Kt z) (u z)) -
        fderiv ℝ (ω.hamiltonianVectorField (Ks z)) (u z) v -
        J z (u z) (fderiv ℝ (ω.hamiltonianVectorField (Kt z)) (u z) v) :=
  (rfl)

/-- The linearized Floer operator is `∂s ξ + J(z, u z) ∂t ξ` plus its zeroth-order part
`floerLinearizationCoeff`. -/
theorem floerLinearization_eq_add (ω : SymplecticForm V)
    (J : ℝ × ℝ → V → V →L[ℝ] V) (Ks Kt : ℝ × ℝ → V → ℝ) (u ξ : ℝ × ℝ → V) (z : ℝ × ℝ) :
    ω.floerLinearization J Ks Kt u ξ z =
      fderiv ℝ ξ z stdComplexLineReal + J z (u z) (fderiv ℝ ξ z stdComplexLineImag) +
        ω.floerLinearizationCoeff J Ks Kt u z (ξ z) := by
  simp only [floerLinearization_def, floerLinearizationCoeff_apply, map_sub]
  abel

/-- The zeroth-order part of the linearized Floer operator is continuous at `z` when the data are
`C¹` (and the Hamiltonians `C²`) at `(z, u z)`, and `u` is `C¹` at `z`. -/
theorem continuousAt_floerLinearizationCoeff (ω : SymplecticForm V)
    {J : ℝ × ℝ → V → V →L[ℝ] V} {Ks Kt : ℝ × ℝ → V → ℝ} {u : ℝ × ℝ → V} {z : ℝ × ℝ}
    (hJ : ContDiffAt ℝ 1 (Function.uncurry J) (z, u z))
    (hKs : ContDiffAt ℝ 2 (Function.uncurry Ks) (z, u z))
    (hKt : ContDiffAt ℝ 2 (Function.uncurry Kt) (z, u z)) (hu : ContDiffAt ℝ 1 u z) :
    ContinuousAt (ω.floerLinearizationCoeff J Ks Kt u) z := by
  have hu₀ : ContDiffAt ℝ 0 u z := hu.of_le (by norm_num)
  have hgraph : ContinuousAt (fun z ↦ (z, u z)) z := continuousAt_id.prodMk hu₀.continuousAt
  have hXs := ω.contDiffAt_hamiltonianVectorField_uncurry (n := 1) hKs
  have hXt := ω.contDiffAt_hamiltonianVectorField_uncurry (n := 1) hKt
  have hdJ : ContinuousAt (fun z ↦ fderiv ℝ (J z) (u z)) z :=
    (hJ.fderiv (f := fun z y ↦ J z y) hu₀ le_rfl).continuousAt
  have hdXs : ContinuousAt (fun z ↦ fderiv ℝ (ω.hamiltonianVectorField (Ks z)) (u z)) z :=
    (hXs.fderiv (f := fun z y ↦ ω.hamiltonianVectorField (Ks z) y) hu₀ le_rfl).continuousAt
  have hdXt : ContinuousAt (fun z ↦ fderiv ℝ (ω.hamiltonianVectorField (Kt z)) (u z)) z :=
    (hXt.fderiv (f := fun z y ↦ ω.hamiltonianVectorField (Kt z) y) hu₀ le_rfl).continuousAt
  have hut : ContinuousAt (fun z ↦ fderiv ℝ u z stdComplexLineImag) z :=
    (hu.fderiv_right (m := 0) le_rfl).continuousAt.clm_apply continuousAt_const
  have hXtu : ContinuousAt (fun z ↦ ω.hamiltonianVectorField (Kt z) (u z)) z :=
    hXt.continuousAt.comp (f := fun z ↦ (z, u z)) hgraph
  have hJu : ContinuousAt (fun z ↦ J z (u z)) z :=
    hJ.continuousAt.comp (f := fun z ↦ (z, u z)) hgraph
  have hflip : ContinuousAt (fun z ↦ (fderiv ℝ (J z) (u z)).flip) z :=
    (flipₗᵢ ℝ V V V).continuous.continuousAt.comp hdJ
  exact ((hflip.clm_apply (hut.sub hXtu)).sub hdXs).sub (hJu.clm_comp hdXt)

/-- The zeroth-order part of the linearized Floer operator is continuous on `K` when the data are
`C¹` (and the Hamiltonians `C²`) at the points `(z, u z)` with `z ∈ K`, and `u` is `C¹` on `K`. -/
theorem continuousOn_floerLinearizationCoeff (ω : SymplecticForm V)
    {J : ℝ × ℝ → V → V →L[ℝ] V} {Ks Kt : ℝ × ℝ → V → ℝ} {u : ℝ × ℝ → V} {K : Set (ℝ × ℝ)}
    (hJ : ∀ z ∈ K, ContDiffAt ℝ 1 (fun p : (ℝ × ℝ) × V ↦ J p.1 p.2) (z, u z))
    (hKs : ∀ z ∈ K, ContDiffAt ℝ 2 (Function.uncurry Ks) (z, u z))
    (hKt : ∀ z ∈ K, ContDiffAt ℝ 2 (Function.uncurry Kt) (z, u z))
    (hu : ∀ z ∈ K, ContDiffAt ℝ 1 u z) :
    ContinuousOn (ω.floerLinearizationCoeff J Ks Kt u) K := fun z hz ↦
  (ω.continuousAt_floerLinearizationCoeff (hJ z hz) (hKs z hz) (hKt z hz)
    (hu z hz)).continuousWithinAt

/-- **Continuity of the linearization.** Let `u` and `ξ` be `C¹` at `z`, and let the
coefficients `J` be `C¹` and the Hamiltonians `K_s`, `K_t` be `C²` at `(z, u z)`, jointly in the
domain and target point. Then the linearized Floer operator along `u` in the direction `ξ` is
continuous at `z`. -/
theorem continuousAt_floerLinearization (ω : SymplecticForm V)
    {J : ℝ × ℝ → V → V →L[ℝ] V} {Ks Kt : ℝ × ℝ → V → ℝ} {u ξ : ℝ × ℝ → V} {z : ℝ × ℝ}
    (hJ : ContDiffAt ℝ 1 (Function.uncurry J) (z, u z))
    (hKs : ContDiffAt ℝ 2 (Function.uncurry Ks) (z, u z))
    (hKt : ContDiffAt ℝ 2 (Function.uncurry Kt) (z, u z)) (hu : ContDiffAt ℝ 1 u z)
    (hξ : ContDiffAt ℝ 1 ξ z) :
    ContinuousAt (ω.floerLinearization J Ks Kt u ξ) z := by
  have hdξ (v : ℝ × ℝ) : ContinuousAt (fun w ↦ fderiv ℝ ξ w v) z :=
    (hξ.continuousAt_fderiv one_ne_zero).clm_apply continuousAt_const
  have hJu : ContinuousAt (fun w ↦ J w (u w)) z :=
    ContinuousAt.comp (f := fun w ↦ (w, u w)) hJ.continuousAt
      (continuousAt_id.prodMk hu.continuousAt)
  rw [show ω.floerLinearization J Ks Kt u ξ = _ from
    funext (ω.floerLinearization_eq_add J Ks Kt u ξ)]
  exact ((hdξ _).add (hJu.clm_apply (hdξ _))).add
    ((ω.continuousAt_floerLinearizationCoeff hJ hKs hKt hu).clm_apply hξ.continuousAt)

section Families

variable (ω : SymplecticForm V)
variable (J : P → ℝ × ℝ → V → V →L[ℝ] V) (Ks Kt : P → ℝ × ℝ → V → ℝ)
variable (u : P → ℝ × ℝ → V) (p : P) (z : ℝ × ℝ)
variable (hu : ContDiffAt ℝ 2 (Function.uncurry u) (p, z))
variable (hJ : DifferentiableAt ℝ (Function.uncurry fun q y ↦ J q z y) (p, u p z))
variable (hKs : ContDiffAt ℝ 2 (Function.uncurry fun q y ↦ Ks q z y) (p, u p z))
variable (hKt : ContDiffAt ℝ 2 (Function.uncurry fun q y ↦ Kt q z y) (p, u p z))

include hu hJ hKs hKt

private theorem hasFDerivAt_floerOperator_aux :
    let A := fderiv ℝ (fun q ↦ fderiv ℝ (u q) z) p
    HasFDerivAt (fun q ↦ ω.floerOperator (J q) (Ks q) (Kt q) (u q) z)
      (A.flip stdComplexLineReal -
          fderiv ℝ (fun q ↦ ω.hamiltonianVectorField (Ks q z) (u q z)) p +
        ((J p z (u p z)).comp (A.flip stdComplexLineImag -
            fderiv ℝ (fun q ↦ ω.hamiltonianVectorField (Kt q z) (u q z)) p) +
          (fderiv ℝ (fun q ↦ J q z (u q z)) p).flip
            (fderiv ℝ (u p) z stdComplexLineImag -
              ω.hamiltonianVectorField (Kt p z) (u p z)))) p := by
  have hdu := (hu.fderiv (m := 1) contDiffAt_const (by norm_num)).differentiableAt one_ne_zero
  have hF : DifferentiableAt ℝ (Function.uncurry u) (p, z) := hu.differentiableAt (by norm_num)
  have huP : DifferentiableAt ℝ (fun q ↦ u q z) p := by
    simpa only [Function.comp_def, Function.uncurry_def] using
      (hF.hasFDerivAt.comp p (hasFDerivAt_prodMk_left (𝕜 := ℝ) p z)).differentiableAt
  have hX (K : P → ℝ × ℝ → V → ℝ)
      (hK : ContDiffAt ℝ 2 (Function.uncurry fun q y ↦ K q z y) (p, u p z)) :=
    ((ω.contDiffAt_hamiltonianVectorField_uncurry (K := fun q ↦ K q z) (n := 1)
      hK).differentiableAt one_ne_zero).comp p (differentiableAt_id.prodMk huP)
  have hJP := hJ.comp p (differentiableAt_id.prodMk huP)
  simpa only [floerOperator_def, Function.comp_def, Function.uncurry_def, id_eq,
    Pi.sub_def, Pi.add_def, comp_zero, zero_add] using
    ((hdu.hasFDerivAt.clm_apply (hasFDerivAt_const (x := p) stdComplexLineReal)).sub
      (hX Ks hKs).hasFDerivAt).add
      (hJP.hasFDerivAt.clm_apply
        ((hdu.hasFDerivAt.clm_apply (hasFDerivAt_const (x := p) stdComplexLineImag)).sub
          (hX Kt hKt).hasFDerivAt))

/-- The actual nonlinear Floer operator is differentiable along the stated coefficient and
map families. No Floer equation or regularity of a solution is assumed. -/
theorem differentiableAt_floerOperator :
    DifferentiableAt ℝ (fun q ↦ ω.floerOperator (J q) (Ks q) (Kt q) (u q) z) p :=
  (hasFDerivAt_floerOperator_aux ω J Ks Kt u p z hu hJ hKs hKt).differentiableAt

/-- **Universal variation of the inhomogeneous Floer operator.** In addition to the map
linearization, there are the terms `-X_(δKs) - J X_(δKt) + δJ(∂t u - X_Kt)`.
The direction field in the linearization is the actual parameter derivative of `u`. -/
theorem fderiv_floerOperator_apply (h : P) :
    fderiv ℝ (fun q ↦ ω.floerOperator (J q) (Ks q) (Kt q) (u q) z) p h =
      ω.floerLinearization (J p) (Ks p) (Kt p) (u p)
          (fun y ↦ fderiv ℝ (fun q ↦ u q y) p h) z -
        ω.hamiltonianVectorField (fun y ↦ fderiv ℝ (fun q ↦ Ks q z y) p h) (u p z) -
        J p z (u p z)
          (ω.hamiltonianVectorField (fun y ↦ fderiv ℝ (fun q ↦ Kt q z y) p h) (u p z)) +
        fderiv ℝ (fun q ↦ J q z (u p z)) p h
          (fderiv ℝ (u p) z stdComplexLineImag - ω.hamiltonianVectorField (Kt p z) (u p z)) := by
  have hA := hasFDerivAt_spatialFDeriv (𝕜 := ℝ) (F := fun w ↦ u w.1 w.2)
    (p := p) (x := z)
    (by simpa only [minSmoothness_of_isRCLikeNormedField, Function.uncurry_def] using hu)
  have hξ := hasFDerivAt_parameterFDeriv_apply (F := fun w ↦ u w.1 w.2) hu h
  have hF : DifferentiableAt ℝ (Function.uncurry u) (p, z) := hu.differentiableAt (by norm_num)
  have huP : DifferentiableAt ℝ (fun q ↦ u q z) p := by
    simpa only [Function.comp_def, Function.uncurry_def] using
      (hF.hasFDerivAt.comp p (hasFDerivAt_prodMk_left (𝕜 := ℝ) p z)).differentiableAt
  rw [(hasFDerivAt_floerOperator_aux ω J Ks Kt u p z hu hJ hKs hKt).fderiv]
  simp only [hA.fderiv, floerLinearization_def, hξ.fderiv, sub_apply, add_apply, comp_apply,
    flip_apply]
  rw [ω.fderiv_hamiltonianVectorField_comp_apply (K := fun q ↦ Ks q z) hKs huP,
    ω.fderiv_hamiltonianVectorField_comp_apply (K := fun q ↦ Kt q z) hKt huP,
    fderiv_comp_graph_apply (f := fun w : P × V ↦ J w.1 z w.2) huP hJ]
  have hJp := congrArg (fun L : P →L[ℝ] (V →L[ℝ] V) ↦ L h) (fderiv_slice_left hJ)
  simp only [comp_apply, inl_apply, Function.uncurry_def] at hJp
  rw [← hJp]
  simp only [add_apply, map_add, map_sub]
  abel

end Families

end TauCeti.SymplecticForm
