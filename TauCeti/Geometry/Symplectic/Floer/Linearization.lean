/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Energy
public import TauCeti.Geometry.Symplectic.Hamiltonian.Variation

/-!
# Local-coordinate linearization of the inhomogeneous Floer equation

The nonlinear operator is `∂s u - X_Ks + J(z,u)(∂t u - X_Kt)`. We differentiate it along
jointly `C²` families of maps and Hamiltonians and differentiable families of endomorphisms.
The formula includes the target derivative of `J`, both Hamiltonian linearizations, and the
independent parameter variations of `K` and `J`. Domain dependence of the coefficients is
allowed; the derivative is at a fixed domain point.

`floerLinearization` is the map-direction operator with coefficients fixed. The universal
variation theorem identifies its direction field with the actual parameter derivative of the
map, using equality of mixed derivatives rather than assuming it. The endomorphism field need
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
  rw [ω.isComplexLinearMap_perturbedFDeriv_iff]
  rfl

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

section Families

variable (ω : SymplecticForm V)
variable (J : P → ℝ × ℝ → V → V →L[ℝ] V) (Ks Kt : P → ℝ × ℝ → V → ℝ)
variable (u : P → ℝ × ℝ → V) (p : P) (z : ℝ × ℝ)
variable (hu : ContDiffAt ℝ 2 (Function.uncurry u) (p, z))
variable (hJ : DifferentiableAt ℝ (Function.uncurry fun q y ↦ J q z y) (p, u p z))
variable (hKs : ContDiffAt ℝ 2 (Function.uncurry fun q y ↦ Ks q z y) (p, u p z))
variable (hKt : ContDiffAt ℝ 2 (Function.uncurry fun q y ↦ Kt q z y) (p, u p z))

include hu hJ hKs hKt

/-- The actual nonlinear Floer operator is differentiable along the stated coefficient and
map families. No Floer equation or regularity of a solution is assumed. -/
theorem differentiableAt_floerOperator :
    DifferentiableAt ℝ (fun q ↦ ω.floerOperator (J q) (Ks q) (Kt q) (u q) z) p := by
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
    Pi.sub_def, Pi.add_def] using
    ((hdu.clm_apply (differentiableAt_const stdComplexLineReal)).sub (hX Ks hKs)).add
      (hJP.clm_apply ((hdu.clm_apply (differentiableAt_const stdComplexLineImag)).sub (hX Kt hKt)))

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
  have hA := hasFDerivAt_spatialFDeriv (𝕜 := ℝ) (F := Function.uncurry u)
    (by simpa using hu)
  have hswap : ContDiffAt ℝ 2 (Function.uncurry fun y q ↦ u q y) (z, p) :=
    hu.comp (z, p) (contDiffAt_snd.prodMk contDiffAt_fst)
  have hParameter :=
    (hswap.fderiv (m := 1) contDiffAt_const (by norm_num)).differentiableAt one_ne_zero
  have hξ := hParameter.hasFDerivAt.clm_apply (hasFDerivAt_const (x := z) h)
  simp only [comp_zero, zero_add] at hξ
  have hF : DifferentiableAt ℝ (Function.uncurry u) (p, z) := hu.differentiableAt (by norm_num)
  have huP : DifferentiableAt ℝ (fun q ↦ u q z) p := by
    simpa only [Function.comp_def, Function.uncurry_def] using
      (hF.hasFDerivAt.comp p (hasFDerivAt_prodMk_left (𝕜 := ℝ) p z)).differentiableAt
  have hX (K : P → ℝ × ℝ → V → ℝ)
      (hK : ContDiffAt ℝ 2 (Function.uncurry fun q y ↦ K q z y) (p, u p z)) :=
    ((ω.contDiffAt_hamiltonianVectorField_uncurry (K := fun q ↦ K q z) (n := 1)
      hK).differentiableAt one_ne_zero).comp p (differentiableAt_id.prodMk huP)
  have hJP := hJ.comp p (differentiableAt_id.prodMk huP)
  have hres := (((hA.clm_apply (hasFDerivAt_const (x := p) stdComplexLineReal)).sub
      (hX Ks hKs).hasFDerivAt).add
    (hJP.hasFDerivAt.clm_apply
      ((hA.clm_apply (hasFDerivAt_const (x := p) stdComplexLineImag)).sub
        (hX Kt hKt).hasFDerivAt))).fderiv
  simp only [Function.uncurry_def, Function.comp_def, id_eq, Pi.sub_def, Pi.add_def] at hres
  simp only [floerOperator_def]
  rw [hres]
  simp only [floerLinearization_def, hξ.fderiv, sub_apply, add_apply, comp_apply,
    flip_apply, zero_apply, map_zero, zero_add]
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
