/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Duality
public import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import TauCeti.Analysis.Calculus.FDeriv.Prod

/-!
# Hamiltonian vector fields on symplectic vector spaces

For a constant symplectic form on a finite-dimensional real normed space, the Hamiltonian
vector field of `H` is obtained by inverting contraction with the symplectic form.
Our sign convention is `ω (X_H x) v = dH(x) v`. For `ω = dq ∧ dp`, this gives the
Hamilton equations `q' = ∂H/∂p`, `p' = -∂H/∂q`.

The characteristic contraction equation determines the field uniquely. Its linearization
is infinitesimally symplectic when `H` is twice continuously differentiable; this is the
identity used to show that Hamiltonian flows preserve the symplectic form.

For an almost complex structure `J` preserving `ω`, the field `J X_H` is the gradient of `H` for
the bilinear form `g = ω(·, J ·)`
(`TauCeti.SymplecticForm.Invariant.associatedBilinForm_hamiltonianVectorField`).

Along a family of Hamiltonians whose derivatives vary continuously, for instance a jointly `C¹`
family evaluated along a continuous map, the Hamiltonian vector fields vary continuously.

The Poisson bracket `{F, G} = ω(X_F, X_G)` of two Hamiltonians is the symplectic pairing of their
Hamiltonian vector fields. With the contraction convention it is `dF(X_G) = -dG(X_F)`; it is
antisymmetric and vanishes when either argument is constant.

See McDuff--Salamon, *Introduction to Symplectic Topology*, the discussion of Hamiltonian
vector fields and their flows. The construction uses `SymplecticForm` contraction duality.
-/

public section

namespace TauCeti.SymplecticForm

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- The Hamiltonian vector field, with convention `ι_X ω = dH`.
The derivative is totalized as usual: at a nondifferentiability point this field is zero. -/
noncomputable def hamiltonianVectorField (ω : SymplecticForm V) (H : V → ℝ) (x : V) : V :=
  ω.toBilinForm.toContinuousBilinearMap.inverse (fderiv ℝ H x)

/-- The Hamiltonian vector field is inverse contraction applied to the derivative. -/
theorem hamiltonianVectorField_def (ω : SymplecticForm V) (H : V → ℝ) (x : V) :
    ω.hamiltonianVectorField H x =
      ω.toBilinForm.toContinuousBilinearMap.inverse (fderiv ℝ H x) :=
  (rfl)

/-- Contraction of the Hamiltonian field is the derivative of the Hamiltonian. -/
@[simp]
theorem apply_hamiltonianVectorField (ω : SymplecticForm V) (H : V → ℝ) (x v : V) :
    ω (ω.hamiltonianVectorField H x) v = fderiv ℝ H x v := by
  exact congrArg (fun L : V →L[ℝ] ℝ ↦ L v)
    (ω.isInvertible_toContinuousBilinearMap.self_apply_inverse (fderiv ℝ H x))

/-- The contraction equation uniquely characterizes the Hamiltonian vector field. -/
theorem eq_hamiltonianVectorField_iff (ω : SymplecticForm V) (H : V → ℝ) (x u : V) :
    u = ω.hamiltonianVectorField H x ↔ ∀ v, ω u v = fderiv ℝ H x v := by
  constructor
  · rintro rfl v
    exact ω.apply_hamiltonianVectorField H x v
  · intro h
    apply ω.isInvertible_toContinuousBilinearMap.injective
    ext v
    exact (h v).trans (ω.apply_hamiltonianVectorField H x v).symm

/-- The Hamiltonian has zero derivative in its own Hamiltonian direction. -/
@[simp]
theorem fderiv_apply_hamiltonianVectorField (ω : SymplecticForm V) (H : V → ℝ) (x : V) :
    fderiv ℝ H x (ω.hamiltonianVectorField H x) = 0 := by
  rw [← ω.apply_hamiltonianVectorField H x, ω.self_eq_zero]

/-- For a `J`-invariant symplectic form, `J X_H(x)` is the gradient of `H` at `x` for the
bilinear form `g = ω(·, J ·)`: `g(J X_H(x), w) = dH(x) w`. -/
theorem Invariant.associatedBilinForm_hamiltonianVectorField {ω : SymplecticForm V}
    {J : AlmostComplexStructure V} (hJ : ω.Invariant J) (H : V → ℝ) (x w : V) :
    ω.associatedBilinForm J (J (ω.hamiltonianVectorField H x)) w = fderiv ℝ H x w := by
  rw [associatedBilinForm_apply, (ω.invariant_iff J).mp hJ, apply_hamiltonianVectorField]

/-- A `C^(n+1)` Hamiltonian has a `C^n` Hamiltonian vector field. -/
theorem contDiff_hamiltonianVectorField (ω : SymplecticForm V) {H : V → ℝ}
    {n : WithTop ℕ∞} (hH : ContDiff ℝ (n + 1) H) :
    ContDiff ℝ n (ω.hamiltonianVectorField H) :=
  ω.toBilinForm.toContinuousBilinearMap.inverse.contDiff.comp
    (hH.fderiv_right le_rfl)

/-- Contracting the linearization of the Hamiltonian vector field gives the Hessian. -/
theorem apply_fderiv_hamiltonianVectorField (ω : SymplecticForm V) {H : V → ℝ}
    {x : V} (hH : DifferentiableAt ℝ (fderiv ℝ H) x) (u v : V) :
    ω (fderiv ℝ (ω.hamiltonianVectorField H) x u) v =
      fderiv ℝ (fderiv ℝ H) x u v := by
  have h := ω.toBilinForm.toContinuousBilinearMap.inverse.hasFDerivAt.comp x hH.hasFDerivAt
  have hX : HasFDerivAt (ω.hamiltonianVectorField H)
      (ω.toBilinForm.toContinuousBilinearMap.inverse.comp (fderiv ℝ (fderiv ℝ H) x)) x := h
  rw [hX.fderiv]
  exact congrArg (fun L : V →L[ℝ] ℝ ↦ L v)
    (ω.isInvertible_toContinuousBilinearMap.self_apply_inverse
      (fderiv ℝ (fderiv ℝ H) x u))

/-- The linearization of a `C²` Hamiltonian vector field is infinitesimally symplectic. -/
theorem apply_fderiv_hamiltonianVectorField_add (ω : SymplecticForm V) {H : V → ℝ}
    {x : V} (hH : ContDiffAt ℝ 2 H x) (u v : V) :
    ω (fderiv ℝ (ω.hamiltonianVectorField H) x u) v +
      ω u (fderiv ℝ (ω.hamiltonianVectorField H) x v) = 0 := by
  have hd := (hH.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  rw [← ω.neg_eq (fderiv ℝ (ω.hamiltonianVectorField H) x v) u,
    ω.apply_fderiv_hamiltonianVectorField hd, ω.apply_fderiv_hamiltonianVectorField hd]
  rw [hH.isSymmSndFDerivAt (by norm_num [minSmoothness_of_isRCLikeNormedField]) u v]
  exact add_neg_cancel _

/-- A constant Hamiltonian has zero Hamiltonian vector field. -/
@[simp]
theorem hamiltonianVectorField_const (ω : SymplecticForm V) (c : ℝ) :
    ω.hamiltonianVectorField (fun _ ↦ c) = 0 := by
  funext x
  rw [Pi.zero_apply, eq_comm, eq_hamiltonianVectorField_iff]
  simp

/-- The Hamiltonian vector field is linear in Hamiltonians differentiable at the point:
`X_{aF + bG} = a X_F + b X_G`. -/
theorem hamiltonianVectorField_const_mul_add_const_mul (ω : SymplecticForm V) {F G : V → ℝ}
    {x : V} (hF : DifferentiableAt ℝ F x) (hG : DifferentiableAt ℝ G x) (a b : ℝ) :
    ω.hamiltonianVectorField (fun y ↦ a * F y + b * G y) x =
      a • ω.hamiltonianVectorField F x + b • ω.hamiltonianVectorField G x := by
  rw [eq_comm, eq_hamiltonianVectorField_iff]
  intro v
  rw [fderiv_fun_add (hF.const_mul a) (hG.const_mul b), fderiv_const_mul hF, fderiv_const_mul hG]
  simp [map_add, map_smul]

section Continuity

variable {X : Type*} [TopologicalSpace X] {K : X → V → ℝ} {u : X → V} {s : Set X}

/-- Along a family of Hamiltonians `K z` and points `u z` whose derivatives `dK_z(u z)` vary
continuously on a set, the Hamiltonian vector fields `X_{K z}(u z)` vary continuously on it. -/
theorem continuousOn_hamiltonianVectorField_comp (ω : SymplecticForm V)
    (h : ContinuousOn (fun z ↦ fderiv ℝ (K z) (u z)) s) :
    ContinuousOn (fun z ↦ ω.hamiltonianVectorField (K z) (u z)) s :=
  ω.toBilinForm.toContinuousBilinearMap.inverse.continuous.comp_continuousOn h

/-- Along a family of Hamiltonians `K z` and points `u z` whose derivatives `dK_z(u z)` vary
continuously, the Hamiltonian vector fields `X_{K z}(u z)` vary continuously. -/
theorem continuous_hamiltonianVectorField_comp (ω : SymplecticForm V)
    (h : Continuous fun z ↦ fderiv ℝ (K z) (u z)) :
    Continuous fun z ↦ ω.hamiltonianVectorField (K z) (u z) :=
  ω.toBilinForm.toContinuousBilinearMap.inverse.continuous.comp h

end Continuity

/-- For a family of Hamiltonians `K z` that is jointly `C¹` over an open set `U` of the parameter
space, the Hamiltonian vector fields `X_{K z}` evaluated along a map continuous on `U` vary
continuously on `U`. -/
theorem continuousOn_hamiltonianVectorField_comp_of_contDiffOn {W : Type*} [NormedAddCommGroup W]
    [NormedSpace ℝ W] (ω : SymplecticForm V) {K : W → V → ℝ} {u : W → V} {U : Set W}
    (hU : IsOpen U) (hu : ContinuousOn u U)
    (hK : ContDiffOn ℝ 1 (Function.uncurry K) (U ×ˢ Set.univ)) :
    ContinuousOn (fun z ↦ ω.hamiltonianVectorField (K z) (u z)) U := by
  have hmem {z : W} (hz : z ∈ U) : (z, u z) ∈ U ×ˢ (Set.univ : Set V) := ⟨hz, Set.mem_univ _⟩
  have hD : ContinuousOn (fun z ↦ fderiv ℝ (Function.uncurry K) (z, u z)) U :=
    (hK.continuousOn_fderiv_of_isOpen (hU.prod isOpen_univ) le_rfl).comp
      (continuousOn_id.prodMk hu) fun _ hz ↦ hmem hz
  -- The target derivative of `K` along `u` is a restriction of its joint derivative.
  exact ω.continuousOn_hamiltonianVectorField_comp <|
    (hD.clm_comp (continuousOn_const (c := ContinuousLinearMap.inr ℝ W V))).congr
      fun _ hz ↦ fderiv_slice_right (f := Function.uncurry K) <|
        (hK.differentiableOn one_ne_zero _ (hmem hz)).differentiableAt
          ((hU.prod isOpen_univ).mem_nhds (hmem hz))

section PoissonBracket

/-- The Poisson bracket `{F, G}(x) = ω(X_F x, X_G x)` of two Hamiltonians. -/
noncomputable def poissonBracket (ω : SymplecticForm V) (F G : V → ℝ) (x : V) : ℝ :=
  ω (ω.hamiltonianVectorField F x) (ω.hamiltonianVectorField G x)

theorem poissonBracket_def (ω : SymplecticForm V) (F G : V → ℝ) (x : V) :
    ω.poissonBracket F G x =
      ω (ω.hamiltonianVectorField F x) (ω.hamiltonianVectorField G x) :=
  (rfl)

/-- The Poisson bracket `{F, G}` is the derivative of `F` along the Hamiltonian field of `G`. -/
theorem poissonBracket_eq_fderiv (ω : SymplecticForm V) (F G : V → ℝ) (x : V) :
    ω.poissonBracket F G x = fderiv ℝ F x (ω.hamiltonianVectorField G x) := by
  rw [poissonBracket_def, apply_hamiltonianVectorField]

/-- The Poisson bracket `{F, G}` is minus the derivative of `G` along the Hamiltonian field of
`F`. -/
theorem poissonBracket_eq_neg_fderiv (ω : SymplecticForm V) (F G : V → ℝ) (x : V) :
    ω.poissonBracket F G x = -fderiv ℝ G x (ω.hamiltonianVectorField F x) := by
  rw [poissonBracket_def, ← ω.neg_eq, apply_hamiltonianVectorField]

/-- The Poisson bracket is antisymmetric. -/
theorem neg_poissonBracket (ω : SymplecticForm V) (F G : V → ℝ) (x : V) :
    -ω.poissonBracket G F x = ω.poissonBracket F G x := by
  rw [poissonBracket_def, poissonBracket_def, ω.neg_eq]

@[simp]
theorem poissonBracket_self (ω : SymplecticForm V) (F : V → ℝ) (x : V) :
    ω.poissonBracket F F x = 0 := by
  rw [poissonBracket_def, self_eq_zero]

@[simp]
theorem poissonBracket_const_left (ω : SymplecticForm V) (c : ℝ) (G : V → ℝ) (x : V) :
    ω.poissonBracket (fun _ ↦ c) G x = 0 := by
  simp [poissonBracket_def]

@[simp]
theorem poissonBracket_const_right (ω : SymplecticForm V) (F : V → ℝ) (c : ℝ) (x : V) :
    ω.poissonBracket F (fun _ ↦ c) x = 0 := by
  simp [poissonBracket_def]

end PoissonBracket

end TauCeti.SymplecticForm
