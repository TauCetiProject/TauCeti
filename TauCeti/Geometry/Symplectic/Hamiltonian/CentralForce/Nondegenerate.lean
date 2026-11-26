/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.CentralForce.Coordinates
public import TauCeti.Geometry.Symplectic.Hamiltonian.SingularPoint
import TauCeti.Analysis.Calculus.Morse.OneDimensional
import TauCeti.Analysis.Calculus.Morse.Prod

/-!
# Circular orbits of planar central forces as singular points

Let `F = (H, L) : V × V → ℝ²` be the energy–momentum map of a particle of mass `m ≠ 0` moving in a
plane `V` in a central potential `U` (`TauCeti.centralForceEnergyMomentum`). Off the collision set
its singular points are the points of the circular orbits: `⟪q, p⟫ = 0` and `U_ℓ'(‖q‖) = 0`, where
`U_ℓ(r) = ℓ² / (2 m r²) + U(r)` is the effective potential of the angular momentum `ℓ = L(q, p)`
(`TauCeti.isRegularPoint_centralForceEnergyMomentum_iff`). For `ℓ = 0` these are the rest points
`p = 0` at the critical points of `U`. This file places these singular points in the local theory
of integrable systems.

* At every such point `F` has rank one
  (`TauCeti.finrank_range_fderiv_centralForceEnergyMomentum_eq_one`).
* It is a nondegenerate point of `F` (`TauCeti.SymplecticForm.IsNondegeneratePoint`) exactly when
  `U_ℓ''(‖q‖) ≠ 0` (`TauCeti.isNondegeneratePoint_centralForceEnergyMomentum_iff`).
* With the angular velocity `Ω = ℓ / (m ‖q‖²)`, the Hessian of `H - Ω L` descends to the
  transversal space `ker dF ⧸ (ker dF ∩ (ker dF)^ω)`
  (`TauCeti.polar_hessianQuadraticForm_centralForceHamiltonian_sub_eq_zero`), and `m` times the
  form it induces there is positive definite exactly when `m U_ℓ''(‖q‖) > 0`
  (`TauCeti.posDef_smul_reducedQuadraticForm_hessianQuadraticForm_centralForceHamiltonian_sub_iff`;
  on vectors of `ker dF` this is
  `TauCeti.forall_pos_mul_hessianQuadraticForm_centralForceHamiltonian_sub_iff`). So at a
  nondegenerate minimum of the effective potential, for a positive mass, the circular orbit is a
  nondegenerate singular point of elliptic type.

The computation takes place in the polar canonical coordinates `((r, p_r), (θ, L))` of
`TauCeti.polarCanonical`, in which `F = (p_r² / (2m) + U_L(r), L)`. At the point
`((r₀, 0), (θ, ℓ))` of a circular orbit the derivative of `F` is `δ ↦ (Ω δL, δL)`. Its kernel is
`δL = 0`, the functionals vanishing on its image are the multiples of `(h, l) ↦ h - Ω l`, and the
symplectic complement of the kernel inside it is the line of `∂_θ`. The transversal space is
therefore the plane of `(δr, δp_r)`, on which the Hessian of `H - Ω L` is
`U_ℓ''(r₀) δr² + δp_r² / m`. On a symplectic plane a single quadratic form is a nondegenerate family
exactly when it is a nondegenerate form
(`TauCeti.SymplecticForm.isNondegenerateQuadraticFamily_const_iff`). The derivative of the polar
parametrization is a linear symplectomorphism (`TauCeti.stdSymplecticForm_fderiv_polarCanonical`),
and nondegeneracy is invariant under such changes of variables
(`TauCeti.SymplecticForm.isNondegeneratePoint_comp_right_iff_of_isSymplectomorphism`).

## Main results

* `TauCeti.finrank_range_fderiv_centralForceEnergyMomentum_eq_one`: circular orbits have rank one.
* `TauCeti.isNondegeneratePoint_centralForceEnergyMomentum_iff`: a circular orbit is a
  nondegenerate point exactly when `U_ℓ''(‖q‖) ≠ 0`.
* `TauCeti.polar_hessianQuadraticForm_centralForceHamiltonian_sub_eq_zero`: the Hessian of
  `H - Ω L` descends to the transversal space.
* `TauCeti.posDef_smul_reducedQuadraticForm_hessianQuadraticForm_centralForceHamiltonian_sub_iff`:
  the transversal Hessian of `H - Ω L`, times `m`, is positive definite exactly when
  `m U_ℓ''(‖q‖) > 0`.

## References

* A. V. Bolsinov and A. T. Fomenko, *Integrable Hamiltonian Systems: Geometry, Topology,
  Classification*, Chapman & Hall/CRC, 2004, Chapter 1 (nondegenerate singular points of rank one).
* V. I. Arnold, *Mathematical Methods of Classical Mechanics*, 2nd ed., Springer, 1989, Section 8
  (motion in a central field).
-/

public section

noncomputable section

open Module Filter Topology
open scoped InnerProductSpace

namespace TauCeti

open SymplecticForm

variable {m ℓ a r₀ : ℝ} {U : ℝ → ℝ}

/-! ### The energy–momentum map in polar canonical coordinates -/


/-- The energy–momentum map `(p_r² / (2m) + U_L(r), L)` of a central force in the polar canonical
coordinates `((r, p_r), (θ, L))`. -/
private def polarEnergyMomentum (m : ℝ) (U : ℝ → ℝ) (y : (ℝ × ℝ) × (ℝ × ℝ)) : Fin 2 → ℝ :=
  ![y.1.2 ^ 2 / (2 * m) + effectivePotential m y.2.2 U y.1.1, y.2.2]

/-- The angular momentum coordinate `L` of `((r, p_r), (θ, L))`. -/
private def polarL : (ℝ × ℝ) × (ℝ × ℝ) →L[ℝ] ℝ :=
  (ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ (ℝ × ℝ) (ℝ × ℝ))

@[simp]
private theorem polarL_apply (y : (ℝ × ℝ) × (ℝ × ℝ)) : polarL y = y.2.2 :=
  (rfl)

/-- The derivative `δ ↦ (Ω δL, δL)` of the polar energy–momentum map along a circular orbit of
angular velocity `Ω`. -/
private def polarDerivative (Ω : ℝ) : (ℝ × ℝ) × (ℝ × ℝ) →L[ℝ] Fin 2 → ℝ :=
  ContinuousLinearMap.pi ![Ω • polarL, polarL]

@[simp]
private theorem polarDerivative_apply (Ω : ℝ) (δ : (ℝ × ℝ) × (ℝ × ℝ)) :
    polarDerivative Ω δ = ![Ω * δ.2.2, δ.2.2] := by
  ext i
  fin_cases i <;> simp [polarDerivative]

/-- The functional `(h, l) ↦ h - Ω l`, which kills the image of `polarDerivative Ω`. -/
private def criticalFunctional (Ω : ℝ) : (Fin 2 → ℝ) →L[ℝ] ℝ :=
  ContinuousLinearMap.proj 0 - Ω • ContinuousLinearMap.proj 1

@[simp]
private theorem criticalFunctional_apply (Ω : ℝ) (v : Fin 2 → ℝ) :
    criticalFunctional Ω v = v 0 - Ω * v 1 :=
  (rfl)

@[simp]
private theorem criticalFunctional_comp_polarDerivative (Ω : ℝ) :
    (criticalFunctional Ω).comp (polarDerivative Ω) = 0 := by
  ext <;> simp

/-- A functional vanishing on the image `ℝ (Ω, 1)` of `polarDerivative Ω` is a multiple of
`(h, l) ↦ h - Ω l`. -/
private theorem eq_smul_criticalFunctional_of_comp_eq_zero {Ω : ℝ} {ℓ' : (Fin 2 → ℝ) →L[ℝ] ℝ}
    (h : ℓ'.comp (polarDerivative Ω) = 0) : ℓ' = ℓ' (Pi.single 0 1) • criticalFunctional Ω := by
  have hsplit (v : Fin 2 → ℝ) : v = v 0 • Pi.single 0 1 + v 1 • Pi.single 1 1 := by
    ext i
    fin_cases i <;> simp
  have h₁ : ℓ' (Pi.single 1 1) = -(Ω * ℓ' (Pi.single 0 1)) := by
    have := congr($h ((0, 0), (0, 1)))
    rw [ContinuousLinearMap.comp_apply, polarDerivative_apply, hsplit ![_, _]] at this
    simp only [mul_one, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, map_add, map_smul, smul_eq_mul, one_mul, zero_apply] at this
    linarith
  refine ContinuousLinearMap.ext fun v ↦ ?_
  have hv : ℓ' v = v 0 * ℓ' (Pi.single 0 1) + v 1 * ℓ' (Pi.single 1 1) := by
    conv_lhs => rw [hsplit v]
    rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  rw [hv, h₁, smul_apply, criticalFunctional_apply, smul_eq_mul]
  ring

/-- The kernel of `polarDerivative Ω` is `δL = 0`. -/
private theorem mem_ker_polarDerivative_iff (Ω : ℝ) (v : (ℝ × ℝ) × (ℝ × ℝ)) :
    v ∈ (polarDerivative Ω).ker ↔ v.2.2 = 0 := by
  simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, polarDerivative_apply, funext_iff,
    Fin.forall_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    Pi.zero_apply, mul_eq_zero]
  tauto

/-- Within the kernel `δL = 0` of `polarDerivative Ω`, the symplectic complement of the kernel is
the line `δr = δp_r = δL = 0` of `∂_θ`. -/
private theorem mem_orthogonal_ker_polarDerivative_iff (Ω : ℝ) {v : (ℝ × ℝ) × (ℝ × ℝ)}
    (hv : v.2.2 = 0) :
    v ∈ ((stdSymplecticForm (V := ℝ)).prod (stdSymplecticForm (V := ℝ))).orthogonal
      (polarDerivative Ω).ker ↔ v.1 = 0 := by
  rw [SymplecticForm.mem_orthogonal_iff]
  constructor
  · intro hw
    have h₁ := hw ((1, 0), (0, 0)) ((mem_ker_polarDerivative_iff Ω _).2 rfl)
    have h₂ := hw ((0, 1), (0, 0)) ((mem_ker_polarDerivative_iff Ω _).2 rfl)
    simp only [SymplecticForm.prod_apply, stdSymplecticForm_apply, RCLike.inner_apply,
      conj_trivial, mul_one, mul_zero, sub_zero, sub_self, add_zero, zero_sub, neg_eq_zero]
      at h₁ h₂
    exact Prod.ext h₂ h₁
  · intro h y hy
    simp [(mem_ker_polarDerivative_iff Ω y).1 hy, h, hv]

/-! ### The transversal plane -/

/-- The map `z ↦ [(z, 0)]` from the plane `(δr, δp_r)` to the transversal space
`ker T ⧸ (ker T)^ω` of `T = polarDerivative Ω`. -/
private def transversalPlaneMap (Ω : ℝ) :
    (ℝ × ℝ) →ₗ[ℝ] ((stdSymplecticForm (V := ℝ)).prod (stdSymplecticForm (V := ℝ))).ReducedSpace
      (polarDerivative Ω).ker :=
  (Submodule.mkQ _).comp (LinearMap.codRestrict _ (LinearMap.inl ℝ (ℝ × ℝ) (ℝ × ℝ))
    fun _ ↦ (mem_ker_polarDerivative_iff Ω _).2 rfl)

private theorem transversalPlaneMap_apply (Ω : ℝ) (z : ℝ × ℝ) :
    transversalPlaneMap Ω z =
      Submodule.Quotient.mk ⟨(z, 0), (mem_ker_polarDerivative_iff Ω _).2 rfl⟩ :=
  (rfl)

private theorem reduction_transversalPlaneMap (Ω : ℝ) (z z' : ℝ × ℝ) :
    ((stdSymplecticForm (V := ℝ)).prod (stdSymplecticForm (V := ℝ))).reduction
        (polarDerivative Ω).ker (transversalPlaneMap Ω z) (transversalPlaneMap Ω z') =
      stdSymplecticForm z z' := by
  rw [transversalPlaneMap_apply, transversalPlaneMap_apply, SymplecticForm.reduction_mk]
  simp

/-- The plane `(δr, δp_r)` maps bijectively onto the transversal space: the map is symplectic, hence
injective, and every class `[u]` with `δL = 0` is `[(u.1, 0)]`, since `u - (u.1, 0)` lies on the
line of `∂_θ`. -/
private theorem bijective_transversalPlaneMap (Ω : ℝ) :
    Function.Bijective (transversalPlaneMap Ω) := by
  refine ⟨?_, fun x ↦ ?_⟩
  · rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro z hz
    refine (stdSymplecticForm (V := ℝ)).nondegenerate.1 z fun z' ↦ ?_
    have := reduction_transversalPlaneMap Ω z z'
    rw [LinearMap.mem_ker.1 hz] at this
    simpa using this.symm
  · induction x using Submodule.Quotient.induction_on with
    | H u =>
      refine ⟨(u : (ℝ × ℝ) × (ℝ × ℝ)).1, ?_⟩
      rw [transversalPlaneMap_apply, SymplecticForm.ReducedSpace.mk_eq_mk_iff]
      exact (mem_orthogonal_ker_polarDerivative_iff Ω
        (by simp [(mem_ker_polarDerivative_iff Ω u).1 u.property])).2 (by simp)

/-- The plane `(δr, δp_r)`, with its standard symplectic form, is the transversal space of the
polar energy–momentum map along a circular orbit. -/
private def transversalPlaneEquiv (Ω : ℝ) :
    (ℝ × ℝ) ≃ₗ[ℝ] ((stdSymplecticForm (V := ℝ)).prod (stdSymplecticForm (V := ℝ))).ReducedSpace
      (polarDerivative Ω).ker :=
  LinearEquiv.ofBijective _ (bijective_transversalPlaneMap Ω)

private theorem transversalPlaneEquiv_apply (Ω : ℝ) (z : ℝ × ℝ) :
    transversalPlaneEquiv Ω z = transversalPlaneMap Ω z :=
  (rfl)

private theorem isSymplectomorphism_transversalPlaneEquiv (Ω : ℝ) :
    IsSymplectomorphism stdSymplecticForm
      (((stdSymplecticForm (V := ℝ)).prod (stdSymplecticForm (V := ℝ))).reduction
        (polarDerivative Ω).ker) (transversalPlaneEquiv Ω) :=
  isSymplectomorphism_iff.2 (reduction_transversalPlaneMap Ω)

/-- The quadratic form `(δr, δp_r) ↦ a δr² + δp_r² / m` on the transversal plane. -/
private def transversalForm (a m : ℝ) : QuadraticForm ℝ (ℝ × ℝ) :=
  (a • QuadraticMap.sq).prod (m⁻¹ • QuadraticMap.sq)

private theorem transversalForm_apply (a m : ℝ) (z : ℝ × ℝ) :
    transversalForm a m z = a * z.1 ^ 2 + z.2 ^ 2 / m := by
  simp [transversalForm]
  ring

private theorem nondegenerate_transversalForm_iff (hm : m ≠ 0) :
    (transversalForm a m).Nondegenerate ↔ a ≠ 0 := by
  have hsq : (QuadraticMap.sq : QuadraticForm ℝ ℝ).Nondegenerate :=
    QuadraticMap.Anisotropic.nondegenerate fun x hx ↦ by simpa using hx
  rw [transversalForm, QuadraticMap.nondegenerate_prod_iff,
    QuadraticMap.nondegenerate_smul_iff (isUnit_iff_ne_zero.2 (inv_ne_zero hm)), and_iff_left hsq]
  refine ⟨fun h ha ↦ ?_, fun ha ↦
    (QuadraticMap.nondegenerate_smul_iff (isUnit_iff_ne_zero.2 ha) _).2 hsq⟩
  -- For `a = 0` the first factor is the zero form, whose radical is everything.
  have h₁ : (1 : ℝ) ∈ (a • QuadraticMap.sq : QuadraticForm ℝ ℝ).radical := by
    simp [QuadraticMap.mem_radical_iff', ha]
  simp [h.radical_eq_bot] at h₁

/-! ### Derivatives along a circular orbit -/

private theorem differentiableAt_polarEnergyMomentum (hr₀ : r₀ ≠ 0) (hm : m ≠ 0)
    (hU : DifferentiableAt ℝ U r₀) (p : ℝ) (z : ℝ × ℝ) :
    DifferentiableAt ℝ (polarEnergyMomentum m U) ((r₀, p), z) := by
  have _hU' : DifferentiableAt ℝ (fun y : (ℝ × ℝ) × (ℝ × ℝ) ↦ U y.1.1) ((r₀, p), z) :=
    hU.comp _ (by fun_prop)
  refine differentiableAt_pi.2 fun i ↦ ?_
  fin_cases i
  · simp only [polarEnergyMomentum, effectivePotential_apply, Fin.zero_eta, Fin.isValue,
      Matrix.cons_val_zero]
    have : (2 * m * r₀ ^ 2) ≠ 0 := by positivity
    fun_prop (disch := assumption)
  · simp only [polarEnergyMomentum, Fin.mk_one, Fin.isValue, Matrix.cons_val_one,
      Matrix.cons_val_fin_one]
    fun_prop

private theorem contDiffAt_polarEnergyMomentum (hr₀ : r₀ ≠ 0) (hm : m ≠ 0)
    (hU : ContDiffAt ℝ 2 U r₀) (p : ℝ) (z : ℝ × ℝ) :
    ContDiffAt ℝ 2 (polarEnergyMomentum m U) ((r₀, p), z) := by
  have _hU' : ContDiffAt ℝ 2 (fun y : (ℝ × ℝ) × (ℝ × ℝ) ↦ U y.1.1) ((r₀, p), z) :=
    hU.comp _ (by fun_prop)
  refine contDiffAt_pi' fun i ↦ ?_
  fin_cases i
  · simp only [polarEnergyMomentum, effectivePotential_apply, Fin.zero_eta, Fin.isValue,
      Matrix.cons_val_zero]
    have : (2 * m * r₀ ^ 2) ≠ 0 := by positivity
    fun_prop (disch := assumption)
  · simp only [polarEnergyMomentum, Fin.mk_one, Fin.isValue, Matrix.cons_val_one,
      Matrix.cons_val_fin_one]
    fun_prop

/-- Along a circular orbit, where `p_r = 0` and `U_ℓ'(r₀) = 0`, the polar energy–momentum map has
derivative `δ ↦ (Ω δL, δL)` with the angular velocity `Ω = ℓ / (m r₀²)`. -/
private theorem hasFDerivAt_polarEnergyMomentum (hr₀ : r₀ ≠ 0) (hm : m ≠ 0)
    (hU : DifferentiableAt ℝ U r₀) (hcrit : HasDerivAt (effectivePotential m ℓ U) 0 r₀) (θ : ℝ) :
    HasFDerivAt (polarEnergyMomentum m U) (polarDerivative (ℓ / (m * r₀ ^ 2)))
      ((r₀, 0), (θ, ℓ)) := by
  set y₀ : (ℝ × ℝ) × (ℝ × ℝ) := ((r₀, 0), (θ, ℓ))
  have hdiff : DifferentiableAt ℝ (polarEnergyMomentum m U) y₀ :=
    differentiableAt_polarEnergyMomentum hr₀ hm hU 0 (θ, ℓ)
  obtain ⟨U', hU'⟩ : ∃ U', HasDerivAt U U' r₀ := ⟨_, hU.hasDerivAt⟩
  have hU'eq := (hasDerivAt_effectivePotential_zero_iff (m := m) (ℓ := ℓ) hU' hr₀).1 hcrit
  refine hdiff.hasFDerivAt.congr_fderiv (ContinuousLinearMap.ext fun δ ↦ ?_)
  -- Compare the derivative along the line `t ↦ y₀ + t δ` with the derivative computed one
  -- coordinate at a time.
  have hline : HasDerivAt (fun t : ℝ ↦ y₀ + t • δ) δ 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const δ).const_add y₀
  have h₁ := hdiff.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hline (by simp)
  have hcoord (c d : ℝ) : HasDerivAt (fun t : ℝ ↦ c + t * d) d 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const d).const_add c
  have hr := hcoord r₀ δ.1.1
  have hUc : HasDerivAt (fun t : ℝ ↦ U (r₀ + t * δ.1.1)) (U' * δ.1.1) 0 :=
    hU'.comp_of_eq (0 : ℝ) hr (by simp)
  have h₂ : HasDerivAt (fun t : ℝ ↦ polarEnergyMomentum m U (y₀ + t • δ))
      (polarDerivative (ℓ / (m * r₀ ^ 2)) δ) 0 := by
    rw [polarDerivative_apply]
    refine hasDerivAt_pi.2 fun i ↦ ?_
    fin_cases i
    · have := (((hcoord 0 δ.1.2).pow 2).div_const (2 * m)).add
        ((((hcoord ℓ δ.2.2).pow 2).div (((hr.pow 2).const_mul (2 * m))) (by simp [hm, hr₀])).add
          hUc)
      refine (this.congr_of_eventuallyEq (.of_forall fun t ↦ ?_)).congr_deriv ?_
      · simp [polarEnergyMomentum, y₀, effectivePotential_apply]
      · simp only [Pi.pow_apply, zero_mul, add_zero, Fin.zero_eta, Fin.isValue,
          Matrix.cons_val_zero, hU'eq]
        field_simp
        ring
    · simpa [polarEnergyMomentum, y₀] using hcoord ℓ δ.2.2
  exact h₁.unique h₂

/-- At `(r₀, 0)`, the function `(r, p_r) ↦ U_ℓ(r) + p_r² / (2m) + c` has the Hessian
`(δr, δp_r) ↦ U_ℓ''(r₀) δr² + δp_r² / m`. -/
private theorem hessianQuadraticForm_effectivePotential_add (hr₀ : r₀ ≠ 0) (hm : m ≠ 0)
    (hU : ContDiffAt ℝ 2 U r₀) (ha : HasDerivAt (deriv (effectivePotential m ℓ U)) a r₀) (c : ℝ)
    (w : ℝ × ℝ) :
    hessianQuadraticForm (fun z : ℝ × ℝ ↦ (effectivePotential m ℓ U ∘ Prod.fst +
      (fun p : ℝ ↦ p ^ 2 / (2 * m)) ∘ Prod.snd : ℝ × ℝ → ℝ) z + c) (r₀, 0) w =
      a * w.1 ^ 2 + w.2 ^ 2 / m := by
  have hS : ContDiffAt ℝ 2 (fun p : ℝ ↦ p ^ 2 / (2 * m)) 0 := by fun_prop
  have hE₂ : iteratedDeriv 2 (effectivePotential m ℓ U) r₀ = a := by
    rw [iteratedDeriv_succ, iteratedDeriv_one, ha.deriv]
  have hS₂ : iteratedDeriv 2 (fun p : ℝ ↦ p ^ 2 / (2 * m)) 0 = 1 / m := by
    have hd : deriv (fun p : ℝ ↦ p ^ 2 / (2 * m)) = fun p ↦ p / m := funext fun p ↦ by
      rw [((hasDerivAt_pow 2 p).div_const (2 * m)).deriv]
      field_simp
      ring
    rw [iteratedDeriv_succ, iteratedDeriv_one, hd,
      ((hasDerivAt_id' (x := (0 : ℝ))).div_const m).deriv]
  rw [hessianQuadraticForm_add_const, hessianQuadraticForm_comp_fst_add_comp_snd
    (contDiffAt_effectivePotential hU hr₀) hS, QuadraticMap.prod_apply,
    hessianQuadraticForm_real_apply, hessianQuadraticForm_real_apply, hE₂, hS₂]
  ring

/-- Along a circular orbit, on the kernel `δL = 0` of the derivative, the Hessian of the critical
combination `H - Ω L` of the polar energy–momentum map is `U_ℓ''(r₀) δr² + δp_r² / m`. -/
private theorem hessianQuadraticForm_criticalFunctional_comp_polarEnergyMomentum (hr₀ : r₀ ≠ 0)
    (hm : m ≠ 0) (hU : ContDiffAt ℝ 2 U r₀) (hcrit : HasDerivAt (effectivePotential m ℓ U) 0 r₀)
    (ha : HasDerivAt (deriv (effectivePotential m ℓ U)) a r₀) (θ : ℝ)
    {v : (ℝ × ℝ) × (ℝ × ℝ)} (hv : v.2.2 = 0) :
    hessianQuadraticForm (criticalFunctional (ℓ / (m * r₀ ^ 2)) ∘ polarEnergyMomentum m U)
      ((r₀, 0), (θ, ℓ)) v = a * v.1.1 ^ 2 + v.1.2 ^ 2 / m := by
  set Ω := ℓ / (m * r₀ ^ 2)
  set f := criticalFunctional Ω ∘ polarEnergyMomentum m U
  have hG := contDiffAt_polarEnergyMomentum hr₀ hm hU 0 (θ, ℓ)
  have hfc : fderiv ℝ f ((r₀, 0), (θ, ℓ)) = 0 := by
    rw [fderiv_comp _ (criticalFunctional Ω).differentiableAt (hG.differentiableAt two_ne_zero),
      (hasFDerivAt_polarEnergyMomentum hr₀ hm (hU.differentiableAt two_ne_zero) hcrit θ).fderiv,
      ContinuousLinearMap.fderiv, criticalFunctional_comp_polarDerivative]
  -- Restrict to the slice `L = ℓ` through the point, parametrized by `((r, p_r), θ)`.
  let ψ : (ℝ × ℝ) × ℝ → (ℝ × ℝ) × (ℝ × ℝ) := fun z ↦ (z.1, (z.2, ℓ))
  have hψ : HasFDerivAt ψ ((ContinuousLinearMap.fst ℝ (ℝ × ℝ) ℝ).prod
      ((ContinuousLinearMap.snd ℝ (ℝ × ℝ) ℝ).prod 0)) ((r₀, 0), θ) :=
    hasFDerivAt_fst.prodMk (hasFDerivAt_snd.prodMk (hasFDerivAt_const ℓ _))
  have key := hessianQuadraticForm_comp (φ := ψ) (b := ((r₀, 0), θ))
    ((criticalFunctional Ω).contDiff.contDiffAt.comp _ hG) (by fun_prop) hfc
  -- On the slice, `H - Ω L` is a separated sum of `U_ℓ(r)` and `p_r² / (2m)`, up to a constant.
  set h : ℝ × ℝ → ℝ := fun z ↦ (effectivePotential m ℓ U ∘ Prod.fst +
    (fun p : ℝ ↦ p ^ 2 / (2 * m)) ∘ Prod.snd : ℝ × ℝ → ℝ) z + -(Ω * ℓ)
  have hfψ : f ∘ ψ = h ∘ (ContinuousLinearMap.fst ℝ (ℝ × ℝ) ℝ) := by
    funext z
    simp [f, ψ, h, polarEnergyMomentum]
    ring
  have hh : ContDiffAt ℝ 2 h (r₀, 0) := by
    have hS : ContDiffAt ℝ 2 (fun p : ℝ ↦ p ^ 2 / (2 * m)) 0 := by fun_prop
    have h₁ := (contDiffAt_effectivePotential (m := m) (ℓ := ℓ) hU hr₀).comp ((r₀, 0) : ℝ × ℝ)
      contDiffAt_fst
    exact (h₁.add (hS.comp ((r₀, 0) : ℝ × ℝ) contDiffAt_snd)).add contDiffAt_const
  calc hessianQuadraticForm f ((r₀, 0), (θ, ℓ)) v
      = (hessianQuadraticForm f (ψ ((r₀, 0), θ))).comp (fderiv ℝ ψ ((r₀, 0), θ)).toLinearMap
          (v.1, v.2.1) := by
        rw [QuadraticMap.comp_apply, hψ.fderiv]
        congr 1
        ext <;> simp [hv]
    _ = hessianQuadraticForm h (r₀, 0) v.1 := by
        rw [← key, hfψ, ContinuousLinearMap.hessianQuadraticForm_comp _ hh,
          QuadraticMap.comp_apply, ContinuousLinearMap.coe_coe, ContinuousLinearMap.coe_fst']
    _ = a * v.1.1 ^ 2 + v.1.2 ^ 2 / m :=
        hessianQuadraticForm_effectivePotential_add hr₀ hm hU ha _ _

/-- Along a circular orbit, on the kernel `δL = 0`, the Hessian of `ℓ' ∘ F` for a functional `ℓ'`
vanishing on the image of the derivative is `ℓ'(1, 0) (U_ℓ''(r₀) δr² + δp_r² / m)`. -/
private theorem hessianQuadraticForm_comp_polarEnergyMomentum (hr₀ : r₀ ≠ 0) (hm : m ≠ 0)
    (hU : ContDiffAt ℝ 2 U r₀) (hcrit : HasDerivAt (effectivePotential m ℓ U) 0 r₀)
    (ha : HasDerivAt (deriv (effectivePotential m ℓ U)) a r₀) (θ : ℝ)
    {ℓ' : (Fin 2 → ℝ) →L[ℝ] ℝ} (h : ℓ'.comp (polarDerivative (ℓ / (m * r₀ ^ 2))) = 0)
    {v : (ℝ × ℝ) × (ℝ × ℝ)} (hv : v.2.2 = 0) :
    hessianQuadraticForm (ℓ' ∘ polarEnergyMomentum m U) ((r₀, 0), (θ, ℓ)) v =
      ℓ' (Pi.single 0 1) * (a * v.1.1 ^ 2 + v.1.2 ^ 2 / m) := by
  have hfun : ℓ' ∘ polarEnergyMomentum m U = ℓ' (Pi.single 0 1) •
      (criticalFunctional (ℓ / (m * r₀ ^ 2)) ∘ polarEnergyMomentum m U) := by
    conv_lhs => rw [eq_smul_criticalFunctional_of_comp_eq_zero h]
    ext y
    simp
  rw [hfun, hessianQuadraticForm_smul, smul_apply, smul_eq_mul,
    hessianQuadraticForm_criticalFunctional_comp_polarEnergyMomentum hr₀ hm hU hcrit ha θ hv]

/-- Along a circular orbit, the Hessians of the critical functions `ℓ' ∘ F` vanish on
`(ker T ∩ (ker T)^ω) × ker T`, so they descend to the transversal space. -/
private theorem polar_hessianQuadraticForm_comp_polarEnergyMomentum_eq_zero (hr₀ : r₀ ≠ 0)
    (hm : m ≠ 0) (hU : ContDiffAt ℝ 2 U r₀) (hcrit : HasDerivAt (effectivePotential m ℓ U) 0 r₀)
    (ha : HasDerivAt (deriv (effectivePotential m ℓ U)) a r₀) (θ : ℝ)
    {ℓ' : (Fin 2 → ℝ) →L[ℝ] ℝ} (h : ℓ'.comp (polarDerivative (ℓ / (m * r₀ ^ 2))) = 0) :
    ∀ w ∈ (polarDerivative (ℓ / (m * r₀ ^ 2))).ker ⊓
        ((stdSymplecticForm (V := ℝ)).prod (stdSymplecticForm (V := ℝ))).orthogonal
          (polarDerivative (ℓ / (m * r₀ ^ 2))).ker,
      ∀ u ∈ (polarDerivative (ℓ / (m * r₀ ^ 2))).ker, QuadraticMap.polar
        (hessianQuadraticForm (ℓ' ∘ polarEnergyMomentum m U) ((r₀, 0), (θ, ℓ))) w u = 0 := by
  intro w hw u hu
  have hK := mem_ker_polarDerivative_iff (ℓ / (m * r₀ ^ 2))
  have hw₂ := (hK w).1 hw.1
  have hu₂ := (hK u).1 hu
  have hw₁ := (mem_orthogonal_ker_polarDerivative_iff _ hw₂).1 hw.2
  have hH {v : (ℝ × ℝ) × (ℝ × ℝ)} (hv : v.2.2 = 0) :=
    hessianQuadraticForm_comp_polarEnergyMomentum hr₀ hm hU hcrit ha θ h hv
  rw [QuadraticMap.polar, hH (by simp [hw₂, hu₂]), hH hw₂, hH hu₂, Prod.fst_add, hw₁]
  simp

/-- **Circular orbits in polar coordinates.** At a point `((r₀, 0), (θ, ℓ))` of a circular orbit,
where `U_ℓ'(r₀) = 0`, the polar energy–momentum map has a nondegenerate point exactly when
`U_ℓ''(r₀) ≠ 0`. -/
private theorem isNondegeneratePoint_polarEnergyMomentum_iff (hr₀ : r₀ ≠ 0) (hm : m ≠ 0)
    (hU : ContDiffAt ℝ 2 U r₀) (hcrit : HasDerivAt (effectivePotential m ℓ U) 0 r₀)
    (ha : HasDerivAt (deriv (effectivePotential m ℓ U)) a r₀) (θ : ℝ) :
    ((stdSymplecticForm (V := ℝ)).prod (stdSymplecticForm (V := ℝ))).IsNondegeneratePoint
      (polarEnergyMomentum m U) ((r₀, 0), (θ, ℓ)) ↔ a ≠ 0 := by
  set ω := (stdSymplecticForm (V := ℝ)).prod (stdSymplecticForm (V := ℝ))
  set T := polarDerivative (ℓ / (m * r₀ ^ 2))
  set G := polarEnergyMomentum m U
  have hdesc (ℓ' : {ℓ' : (Fin 2 → ℝ) →L[ℝ] ℝ // ℓ'.comp T = 0}) :=
    polar_hessianQuadraticForm_comp_polarEnergyMomentum_eq_zero hr₀ hm hU hcrit ha θ ℓ'.property
  -- The transversal Hessians, read on the plane `(δr, δp_r)`, are the multiples of
  -- `a δr² + δp_r² / m`.
  have hQ (ℓ' : {ℓ' : (Fin 2 → ℝ) →L[ℝ] ℝ // ℓ'.comp T = 0}) :
      (ω.reducedQuadraticForm T.ker (hessianQuadraticForm (ℓ'.val ∘ G) ((r₀, 0), (θ, ℓ)))
          (hdesc ℓ')).comp
          (transversalPlaneEquiv (ℓ / (m * r₀ ^ 2)) : (ℝ × ℝ) →ₗ[ℝ] ω.ReducedSpace T.ker) =
        ℓ'.val (Pi.single 0 1) • transversalForm a m := by
    ext z
    rw [QuadraticMap.comp_apply, LinearEquiv.coe_coe, transversalPlaneEquiv_apply,
      transversalPlaneMap_apply, SymplecticForm.reducedQuadraticForm_mk, smul_apply,
      transversalForm_apply, smul_eq_mul]
    exact hessianQuadraticForm_comp_polarEnergyMomentum hr₀ hm hU hcrit ha θ ℓ'.property rfl
  have hspan : Submodule.span ℝ (Set.range fun ℓ' : {ℓ' : (Fin 2 → ℝ) →L[ℝ] ℝ // ℓ'.comp T = 0} ↦
      ℓ'.val (Pi.single 0 1) • transversalForm a m) =
      Submodule.span ℝ (Set.range fun _ : Unit ↦ transversalForm a m) := by
    rw [Set.range_const]
    refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)
    · rintro _ ⟨ℓ', rfl⟩
      exact Submodule.smul_mem _ _ (Submodule.subset_span rfl)
    · rintro _ rfl
      exact Submodule.subset_span ⟨⟨_, criticalFunctional_comp_polarDerivative _⟩, by simp⟩
  have hfam : (ω.reduction T.ker).IsNondegenerateQuadraticFamily
      (fun ℓ' : {ℓ' : (Fin 2 → ℝ) →L[ℝ] ℝ // ℓ'.comp T = 0} ↦
        ω.reducedQuadraticForm T.ker (hessianQuadraticForm (ℓ'.val ∘ G) ((r₀, 0), (θ, ℓ)))
          (hdesc ℓ')) ↔ a ≠ 0 := by
    rw [← isNondegenerateQuadraticFamily_comp_iff (isSymplectomorphism_transversalPlaneEquiv _),
      funext hQ, isNondegenerateQuadraticFamily_iff_of_span_eq hspan,
      isNondegenerateQuadraticFamily_const_iff (by simp), nondegenerate_transversalForm_iff hm]
  rw [isNondegeneratePoint_iff_of_fderiv_eq
    (hasFDerivAt_polarEnergyMomentum hr₀ hm (hU.differentiableAt two_ne_zero) hcrit θ).fderiv]
  exact ⟨fun h ↦ hfam.1 h.2.isNondegenerateQuadraticFamily, fun h ↦
    ⟨contDiffAt_polarEnergyMomentum hr₀ hm hU 0 (θ, ℓ), fun ℓ' hℓ' ↦ hdesc ⟨ℓ', hℓ'⟩, hfam.2 h⟩⟩

/-! ### Circular orbits in the plane -/

section Plane

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  (b : OrthonormalBasis (Fin 2) ℝ V)

/-- Near a point with `r > 0`, the energy–momentum map read in polar canonical coordinates is the
polar energy–momentum map. -/
private theorem centralForceEnergyMomentum_comp_polarCanonical_eventuallyEq
    {y : (ℝ × ℝ) × (ℝ × ℝ)} (hy : 0 < y.1.1) :
    centralForceEnergyMomentum b m U ∘ polarCanonical (b 0) (b 1) =ᶠ[𝓝 y]
      polarEnergyMomentum m U := by
  have hu := b.norm_eq_one 0
  have hw := b.norm_eq_one 1
  have huw := b.inner_eq_zero (i := 0) (j := 1) (by decide)
  filter_upwards [((continuous_fst.comp continuous_fst).tendsto y).eventually
    (eventually_gt_nhds hy)] with z hz
  ext i
  fin_cases i
  · simp [polarEnergyMomentum, centralForceHamiltonian_polarCanonical hu hw huw m U hz]
  · simp [polarEnergyMomentum, angularMomentum_polarCanonical hu hw huw hz.ne']

/-- The polar canonical coordinates `((‖q‖, 0), (θ, L))` of a point `(q, p)` with `⟪q, p⟫ = 0`,
for the lift `θ ∈ (-π, π]` of its polar angle. -/
private def polarPoint (q p : V) : (ℝ × ℝ) × (ℝ × ℝ) :=
  ((‖q‖, 0), ((polarAngle (b 0) (b 1) q).toReal, angularMomentum (b 0) (b 1) (q, p)))

private theorem polarCanonical_polarPoint {q : V} (p : V) (hq : q ≠ 0) (hqp : ⟪q, p⟫_ℝ = 0) :
    polarCanonical (b 0) (b 1) (polarPoint b q p) = (q, p) := by
  have := polarCanonical_polarAngle b p hq (Real.Angle.coe_toReal _)
  rwa [radialMomentum_def, hqp, zero_div] at this

/-- The derivative of the polar canonical parametrization at `polarPoint b q p`, as a linear
equivalence. -/
private def fderivPolarCanonicalEquiv {q : V} (p : V) (hq : q ≠ 0) :
    ((ℝ × ℝ) × (ℝ × ℝ)) ≃ₗ[ℝ] V × V :=
  LinearEquiv.ofBijective (fderiv ℝ (polarCanonical (b 0) (b 1)) (polarPoint b q p)).toLinearMap
    (bijective_fderiv_polarCanonical b (x := polarPoint b q p) (norm_ne_zero_iff.2 hq))

private theorem fderivPolarCanonicalEquiv_apply {q : V} (p : V) (hq : q ≠ 0)
    (u : (ℝ × ℝ) × (ℝ × ℝ)) :
    fderivPolarCanonicalEquiv b p hq u =
      fderiv ℝ (polarCanonical (b 0) (b 1)) (polarPoint b q p) u :=
  (rfl)

/-- The derivative of the polar canonical parametrization is a linear symplectomorphism from
`dr ∧ dp_r + dθ ∧ dL` to the standard form. -/
private theorem isSymplectomorphism_fderivPolarCanonicalEquiv {q : V} (p : V) (hq : q ≠ 0) :
    IsSymplectomorphism ((stdSymplecticForm (V := ℝ)).prod (stdSymplecticForm (V := ℝ)))
      stdSymplecticForm (fderivPolarCanonicalEquiv b p hq) :=
  isSymplectomorphism_iff.2 fun v w ↦ stdSymplecticForm_fderiv_polarCanonical (b.norm_eq_one 0)
    (b.norm_eq_one 1) (b.inner_eq_zero (by decide)) (x := polarPoint b q p)
    (norm_ne_zero_iff.2 hq) v w

/-- At a point of a circular orbit, the derivative of the energy–momentum map, read through the
polar parametrization, is `δ ↦ (Ω δL, δL)` with the angular velocity `Ω = ℓ / (m ‖q‖²)`. -/
private theorem fderiv_centralForceEnergyMomentum_fderivPolarCanonicalEquiv (hm : m ≠ 0)
    {q p : V} (hq : q ≠ 0) (hqp : ⟪q, p⟫_ℝ = 0) (hU : DifferentiableAt ℝ U ‖q‖)
    (hcrit : HasDerivAt (effectivePotential m (angularMomentum (b 0) (b 1) (q, p)) U) 0 ‖q‖)
    (u : (ℝ × ℝ) × (ℝ × ℝ)) :
    fderiv ℝ (centralForceEnergyMomentum b m U) (q, p) (fderivPolarCanonicalEquiv b p hq u) =
      polarDerivative (angularMomentum (b 0) (b 1) (q, p) / (m * ‖q‖ ^ 2)) u := by
  have hr : 0 < ‖q‖ := norm_pos_iff.2 hq
  have hy₀ := polarCanonical_polarPoint b p hq hqp
  have hF : DifferentiableAt ℝ (centralForceEnergyMomentum b m U)
      (polarCanonical (b 0) (b 1) (polarPoint b q p)) := by
    rw [hy₀]
    exact (hasFDerivAt_centralForceEnergyMomentum b hU.hasDerivAt hq).differentiableAt
  have hcomp : fderiv ℝ (centralForceEnergyMomentum b m U ∘ polarCanonical (b 0) (b 1))
      (polarPoint b q p) =
        polarDerivative (angularMomentum (b 0) (b 1) (q, p) / (m * ‖q‖ ^ 2)) := by
    rw [(centralForceEnergyMomentum_comp_polarCanonical_eventuallyEq b (y := polarPoint b q p)
      hr).fderiv_eq]
    exact (hasFDerivAt_polarEnergyMomentum hr.ne' hm hU hcrit _).fderiv
  rw [← hcomp, fderiv_comp _ hF ((contDiffAt_polarCanonical (b 0) (b 1) (n := 1)
    hr.ne').differentiableAt one_ne_zero), hy₀, ContinuousLinearMap.comp_apply,
    fderivPolarCanonicalEquiv_apply]

/-- At a point of a circular orbit, the Hessian of `H - Ω L` is that of its polar version, read
through the derivative of the polar parametrization. -/
private theorem hessianQuadraticForm_criticalFunctional_comp_fderivPolarCanonicalEquiv
    (hm : m ≠ 0) {q p : V} (hq : q ≠ 0) (hqp : ⟪q, p⟫_ℝ = 0) (hU : ContDiffAt ℝ 2 U ‖q‖)
    (hcrit : HasDerivAt (effectivePotential m (angularMomentum (b 0) (b 1) (q, p)) U) 0 ‖q‖)
    (u : (ℝ × ℝ) × (ℝ × ℝ)) :
    hessianQuadraticForm (criticalFunctional (angularMomentum (b 0) (b 1) (q, p) / (m * ‖q‖ ^ 2)) ∘
        centralForceEnergyMomentum b m U) (q, p) (fderivPolarCanonicalEquiv b p hq u) =
      hessianQuadraticForm (criticalFunctional (angularMomentum (b 0) (b 1) (q, p) /
        (m * ‖q‖ ^ 2)) ∘ polarEnergyMomentum m U) (polarPoint b q p) u := by
  set Ω := angularMomentum (b 0) (b 1) (q, p) / (m * ‖q‖ ^ 2)
  set F := centralForceEnergyMomentum b m U
  have hr : 0 < ‖q‖ := norm_pos_iff.2 hq
  have hy₀ := polarCanonical_polarPoint b p hq hqp
  have hFc : ContDiffAt ℝ 2 F (polarCanonical (b 0) (b 1) (polarPoint b q p)) := by
    rw [hy₀]
    exact contDiffAt_centralForceEnergyMomentum b hU hq
  -- `H - Ω L` is critical at `(q, p)`, since `(h, l) ↦ h - Ω l` kills the image of `dF`.
  have hfc : fderiv ℝ (criticalFunctional Ω ∘ F) (polarCanonical (b 0) (b 1) (polarPoint b q p)) =
      0 := by
    rw [fderiv_comp _ (criticalFunctional Ω).differentiableAt (hFc.differentiableAt two_ne_zero),
      ContinuousLinearMap.fderiv, hy₀]
    refine ContinuousLinearMap.ext fun v ↦ ?_
    obtain ⟨u, rfl⟩ := (fderivPolarCanonicalEquiv b p hq).surjective v
    simp [F, fderiv_centralForceEnergyMomentum_fderivPolarCanonicalEquiv b hm hq hqp
      (hU.differentiableAt two_ne_zero) hcrit, Ω]
  have key := hessianQuadraticForm_comp ((criticalFunctional Ω).contDiff.contDiffAt.comp _ hFc)
    (contDiffAt_polarCanonical (b 0) (b 1) hr.ne') hfc
  have hev : (criticalFunctional Ω ∘ F) ∘ polarCanonical (b 0) (b 1) =ᶠ[𝓝 (polarPoint b q p)]
      criticalFunctional Ω ∘ polarEnergyMomentum m U :=
    (centralForceEnergyMomentum_comp_polarCanonical_eventuallyEq b (y := polarPoint b q p)
      hr).fun_comp (criticalFunctional Ω)
  rw [← hessianQuadraticForm_congr_of_eventuallyEq hev, key, QuadraticMap.comp_apply, hy₀,
    ContinuousLinearMap.coe_coe, fderivPolarCanonicalEquiv_apply]

/-- The derivative of the polar parametrization carries the kernel `δL = 0` of the polar
derivative onto the kernel of `dF`. -/
private theorem fderivPolarCanonicalEquiv_mem_ker_iff (hm : m ≠ 0) {q p : V} (hq : q ≠ 0)
    (hqp : ⟪q, p⟫_ℝ = 0) (hU : DifferentiableAt ℝ U ‖q‖)
    (hcrit : HasDerivAt (effectivePotential m (angularMomentum (b 0) (b 1) (q, p)) U) 0 ‖q‖)
    (u : (ℝ × ℝ) × (ℝ × ℝ)) :
    fderivPolarCanonicalEquiv b p hq u ∈ (fderiv ℝ (centralForceEnergyMomentum b m U) (q, p)).ker ↔
      u.2.2 = 0 := by
  rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe,
    fderiv_centralForceEnergyMomentum_fderivPolarCanonicalEquiv b hm hq hqp hU hcrit,
    ← mem_ker_polarDerivative_iff (angularMomentum (b 0) (b 1) (q, p) / (m * ‖q‖ ^ 2)),
    LinearMap.mem_ker, ContinuousLinearMap.coe_coe]

/-- The derivative of the polar parametrization carries the line of `∂_θ` onto
`ker dF ∩ (ker dF)^ω`. -/
private theorem fderivPolarCanonicalEquiv_mem_orthogonal_iff (hm : m ≠ 0) {q p : V} (hq : q ≠ 0)
    (hqp : ⟪q, p⟫_ℝ = 0) (hU : DifferentiableAt ℝ U ‖q‖)
    (hcrit : HasDerivAt (effectivePotential m (angularMomentum (b 0) (b 1) (q, p)) U) 0 ‖q‖)
    {u : (ℝ × ℝ) × (ℝ × ℝ)} (hu : u.2.2 = 0) :
    fderivPolarCanonicalEquiv b p hq u ∈
      stdSymplecticForm.orthogonal (fderiv ℝ (centralForceEnergyMomentum b m U) (q, p)).ker ↔
        u.1 = 0 := by
  set Ω := angularMomentum (b 0) (b 1) (q, p) / (m * ‖q‖ ^ 2)
  have hker := fderivPolarCanonicalEquiv_mem_ker_iff b hm hq hqp hU hcrit
  rw [← mem_orthogonal_ker_polarDerivative_iff Ω hu]
  simp only [SymplecticForm.mem_orthogonal_iff]
  have he := isSymplectomorphism_fderivPolarCanonicalEquiv b p hq
  refine ⟨fun h z hz ↦ (he.apply z u).symm.trans
    (h _ ((hker z).2 ((mem_ker_polarDerivative_iff Ω z).1 hz))), fun h y hy ↦ ?_⟩
  obtain ⟨z, rfl⟩ := (fderivPolarCanonicalEquiv b p hq).surjective y
  exact (he.apply z u).trans (h z ((mem_ker_polarDerivative_iff Ω z).2 ((hker z).1 hy)))

/-- **Circular orbits have rank one.** At a point `(q, p)` of a circular orbit of a planar central
force, `q ≠ 0`, `⟪q, p⟫ = 0` and `U_ℓ'(‖q‖) = 0` for the angular momentum `ℓ` of `(q, p)`, the
energy–momentum map `(H, L)` has rank one. This includes the rest points `p = 0` at the critical
points of `U`. -/
theorem finrank_range_fderiv_centralForceEnergyMomentum_eq_one (hm : m ≠ 0) {q p : V} (hq : q ≠ 0)
    (hqp : ⟪q, p⟫_ℝ = 0) (hU : DifferentiableAt ℝ U ‖q‖)
    (hcrit : HasDerivAt (effectivePotential m (angularMomentum (b 0) (b 1) (q, p)) U) 0 ‖q‖) :
    finrank ℝ (fderiv ℝ (centralForceEnergyMomentum b m U) (q, p)).range = 1 := by
  set Ω := angularMomentum (b 0) (b 1) (q, p) / (m * ‖q‖ ^ 2)
  have hrange : (fderiv ℝ (centralForceEnergyMomentum b m U) (q, p)).range =
      Submodule.span ℝ {![Ω, 1]} := by
    ext w
    simp only [LinearMap.mem_range, ContinuousLinearMap.coe_coe, Submodule.mem_span_singleton]
    constructor
    · rintro ⟨v, rfl⟩
      obtain ⟨u, rfl⟩ := (fderivPolarCanonicalEquiv b p hq).surjective v
      rw [fderiv_centralForceEnergyMomentum_fderivPolarCanonicalEquiv b hm hq hqp hU hcrit]
      exact ⟨u.2.2, by ext i; fin_cases i <;> simp [Ω, mul_comm]⟩
    · rintro ⟨c, rfl⟩
      refine ⟨fderivPolarCanonicalEquiv b p hq ((0, 0), (0, c)), ?_⟩
      rw [fderiv_centralForceEnergyMomentum_fderivPolarCanonicalEquiv b hm hq hqp hU hcrit]
      ext i
      fin_cases i <;> simp [Ω, mul_comm]
  rw [hrange, finrank_span_singleton]
  intro h
  simpa using congr_fun h 1

/-- **Circular orbits are nondegenerate singular points.** Let `(q, p)` be a point of a circular
orbit of a planar central force with mass `m ≠ 0` and potential `U`, `C²` near `‖q‖`: `q ≠ 0`,
`⟪q, p⟫ = 0`, and `U_ℓ'(‖q‖) = 0` for the effective potential `U_ℓ` of the angular momentum `ℓ`
of `(q, p)`. Then `(q, p)` is a nondegenerate point of the energy–momentum map `(H, L)` exactly when
`U_ℓ''(‖q‖) ≠ 0`. -/
theorem isNondegeneratePoint_centralForceEnergyMomentum_iff [FiniteDimensional ℝ V] (hm : m ≠ 0)
    {q p : V} (hq : q ≠ 0) (hqp : ⟪q, p⟫_ℝ = 0) (hU : ContDiffAt ℝ 2 U ‖q‖)
    (hcrit : HasDerivAt (effectivePotential m (angularMomentum (b 0) (b 1) (q, p)) U) 0 ‖q‖)
    (ha : HasDerivAt (deriv (effectivePotential m (angularMomentum (b 0) (b 1) (q, p)) U)) a ‖q‖) :
    stdSymplecticForm.IsNondegeneratePoint (centralForceEnergyMomentum b m U) (q, p) ↔ a ≠ 0 := by
  have hr : 0 < ‖q‖ := norm_pos_iff.2 hq
  have key := isNondegeneratePoint_comp_right_iff_of_isSymplectomorphism
    (F := centralForceEnergyMomentum b m U) (y := polarPoint b q p)
    (isSymplectomorphism_fderivPolarCanonicalEquiv b p hq)
    (contDiffAt_polarCanonical (b 0) (b 1) hr.ne') fun u ↦
      (fderivPolarCanonicalEquiv_apply b p hq u).symm
  rw [polarCanonical_polarPoint b p hq hqp] at key
  have hev := centralForceEnergyMomentum_comp_polarCanonical_eventuallyEq b (m := m) (U := U)
    (y := polarPoint b q p) hr
  rw [← key, ← isNondegeneratePoint_polarEnergyMomentum_iff hr.ne' hm hU hcrit ha
    (polarAngle (b 0) (b 1) q).toReal]
  exact ⟨fun h ↦ h.congr_of_eventuallyEq hev, fun h ↦ h.congr_of_eventuallyEq hev.symm⟩

/-- **The transversal Hessian along a circular orbit.** At a point `(q, p)` of a circular orbit as
in `TauCeti.isNondegeneratePoint_centralForceEnergyMomentum_iff`, with angular momentum `ℓ` and
angular velocity `Ω = ℓ / (m ‖q‖²)`, the polar form of the Hessian of `H - Ω L` vanishes on
`(ker dF ∩ (ker dF)^ω) × ker dF`. So this Hessian descends to the transversal space
`ker dF ⧸ (ker dF ∩ (ker dF)^ω)` (`TauCeti.SymplecticForm.reducedQuadraticForm`). -/
theorem polar_hessianQuadraticForm_centralForceHamiltonian_sub_eq_zero (hm : m ≠ 0) {q p : V}
    (hq : q ≠ 0) (hqp : ⟪q, p⟫_ℝ = 0) (hU : ContDiffAt ℝ 2 U ‖q‖)
    (hcrit : HasDerivAt (effectivePotential m (angularMomentum (b 0) (b 1) (q, p)) U) 0 ‖q‖) :
    ∀ w ∈ (fderiv ℝ (centralForceEnergyMomentum b m U) (q, p)).ker ⊓
        stdSymplecticForm.orthogonal (fderiv ℝ (centralForceEnergyMomentum b m U) (q, p)).ker,
      ∀ u ∈ (fderiv ℝ (centralForceEnergyMomentum b m U) (q, p)).ker,
        QuadraticMap.polar (hessianQuadraticForm (fun x ↦ centralForceHamiltonian m U x -
          angularMomentum (b 0) (b 1) (q, p) / (m * ‖q‖ ^ 2) * angularMomentum (b 0) (b 1) x)
          (q, p)) w u = 0 := by
  set Ω := angularMomentum (b 0) (b 1) (q, p) / (m * ‖q‖ ^ 2)
  set e := fderivPolarCanonicalEquiv b p hq
  have hd := hU.differentiableAt two_ne_zero
  have hker := fderivPolarCanonicalEquiv_mem_ker_iff b hm hq hqp hd hcrit
  obtain ⟨a, ha⟩ : ∃ a, HasDerivAt
      (deriv (effectivePotential m (angularMomentum (b 0) (b 1) (q, p)) U)) a ‖q‖ :=
    ⟨_, ((((contDiffAt_effectivePotential hU (norm_ne_zero_iff.2 hq)).fderiv_right (m := 1)
      (by norm_num)).differentiableAt one_ne_zero).clm_apply (differentiableAt_const 1)).hasDerivAt⟩
  have hfun : (fun x ↦ centralForceHamiltonian m U x - Ω * angularMomentum (b 0) (b 1) x) =
      criticalFunctional Ω ∘ centralForceEnergyMomentum b m U := funext fun x ↦ by simp
  rw [hfun]
  intro w hw u hu
  obtain ⟨w, rfl⟩ := e.surjective w
  obtain ⟨u, rfl⟩ := e.surjective u
  have hw₂ := (hker w).1 hw.1
  have hQ := hessianQuadraticForm_criticalFunctional_comp_fderivPolarCanonicalEquiv b hm hq hqp hU
    hcrit
  rw [QuadraticMap.polar, ← map_add e w u, hQ, hQ, hQ, ← QuadraticMap.polar, polarPoint]
  exact polar_hessianQuadraticForm_comp_polarEnergyMomentum_eq_zero (norm_ne_zero_iff.2 hq) hm hU
    hcrit ha _ (criticalFunctional_comp_polarDerivative Ω) w
    ⟨(mem_ker_polarDerivative_iff Ω w).2 hw₂, (mem_orthogonal_ker_polarDerivative_iff Ω hw₂).2
      ((fderivPolarCanonicalEquiv_mem_orthogonal_iff b hm hq hqp hd hcrit hw₂).1 hw.2)⟩
    u ((mem_ker_polarDerivative_iff Ω u).2 ((hker u).1 hu))

/-- At a point `x = (q, p)` of a circular orbit as in
`TauCeti.isNondegeneratePoint_centralForceEnergyMomentum_iff`, with angular momentum `ℓ` and angular
velocity `Ω = ℓ / (m ‖q‖²)`, `m` times the Hessian of `H - Ω L` at `x` is positive on every vector
of `ker dF_x` outside `(ker dF_x)^ω` exactly when `m U_ℓ''(‖q‖) > 0`. On the transversal space this
is `TauCeti.posDef_smul_reducedQuadraticForm_hessianQuadraticForm_centralForceHamiltonian_sub_iff`.
-/
theorem forall_pos_mul_hessianQuadraticForm_centralForceHamiltonian_sub_iff (hm : m ≠ 0)
    {q p : V} (hq : q ≠ 0) (hqp : ⟪q, p⟫_ℝ = 0) (hU : ContDiffAt ℝ 2 U ‖q‖)
    (hcrit : HasDerivAt (effectivePotential m (angularMomentum (b 0) (b 1) (q, p)) U) 0 ‖q‖)
    (ha : HasDerivAt (deriv (effectivePotential m (angularMomentum (b 0) (b 1) (q, p)) U)) a ‖q‖) :
    (∀ v ∈ (fderiv ℝ (centralForceEnergyMomentum b m U) (q, p)).ker,
      v ∉ stdSymplecticForm.orthogonal (fderiv ℝ (centralForceEnergyMomentum b m U) (q, p)).ker →
        0 < m * hessianQuadraticForm (fun x ↦ centralForceHamiltonian m U x -
          angularMomentum (b 0) (b 1) (q, p) / (m * ‖q‖ ^ 2) * angularMomentum (b 0) (b 1) x)
          (q, p) v) ↔ 0 < m * a := by
  set Ω := angularMomentum (b 0) (b 1) (q, p) / (m * ‖q‖ ^ 2)
  set F := centralForceEnergyMomentum b m U
  set e := fderivPolarCanonicalEquiv b p hq
  have hd := hU.differentiableAt two_ne_zero
  have hfun : (fun x ↦ centralForceHamiltonian m U x - Ω * angularMomentum (b 0) (b 1) x) =
      criticalFunctional Ω ∘ F := funext fun x ↦ by simp [F]
  rw [hfun]
  -- `e` carries the kernel `δL = 0` and its symplectic complement to those of `dF`.
  have hker (u : (ℝ × ℝ) × (ℝ × ℝ)) : e u ∈ (fderiv ℝ F (q, p)).ker ↔ u.2.2 = 0 :=
    fderivPolarCanonicalEquiv_mem_ker_iff b hm hq hqp hd hcrit u
  have horth {u : (ℝ × ℝ) × (ℝ × ℝ)} (hu : u.2.2 = 0) :
      e u ∈ stdSymplecticForm.orthogonal (fderiv ℝ F (q, p)).ker ↔ u.1 = 0 :=
    fderivPolarCanonicalEquiv_mem_orthogonal_iff b hm hq hqp hd hcrit hu
  have hval {u : (ℝ × ℝ) × (ℝ × ℝ)} (hu : u.2.2 = 0) :
      m * hessianQuadraticForm (criticalFunctional Ω ∘ F) (q, p) (e u) =
        m * a * u.1.1 ^ 2 + u.1.2 ^ 2 := by
    rw [hessianQuadraticForm_criticalFunctional_comp_fderivPolarCanonicalEquiv b hm hq hqp hU
      hcrit, polarPoint, hessianQuadraticForm_criticalFunctional_comp_polarEnergyMomentum
        (norm_ne_zero_iff.2 hq) hm hU hcrit ha _ hu]
    field_simp
  constructor
  · intro h
    have := h (e ((1, 0), (0, 0))) ((hker _).2 rfl) (by simp [horth])
    rwa [hval rfl, one_pow, mul_one, zero_pow two_ne_zero, add_zero] at this
  · intro hma v hv hvo
    obtain ⟨u, rfl⟩ := e.surjective v
    have hu₂ := (hker u).1 hv
    have hu₁ : u.1 ≠ 0 := fun h ↦ hvo ((horth hu₂).2 h)
    rw [hval hu₂]
    -- `m a δr² + δp_r²` is positive as soon as `(δr, δp_r) ≠ 0`.
    obtain h | h : u.1.1 ≠ 0 ∨ u.1.2 ≠ 0 := by
      by_contra! h
      exact hu₁ (Prod.ext h.1 h.2)
    all_goals positivity

/-- **Circular orbits at a minimum are elliptic.** At a point `x = (q, p)` of a circular orbit as in
`TauCeti.isNondegeneratePoint_centralForceEnergyMomentum_iff`, with angular momentum `ℓ` and angular
velocity `Ω = ℓ / (m ‖q‖²)`, `m` times the transversal Hessian of `H - Ω L`, the form it induces on
the transversal space `ker dF_x ⧸ (ker dF_x ∩ (ker dF_x)^ω)`, is positive definite exactly when
`m U_ℓ''(‖q‖) > 0`. This is the case at a nondegenerate minimum of the effective potential for a
positive mass: there the circular orbit is a singular point of elliptic type. -/
theorem posDef_smul_reducedQuadraticForm_hessianQuadraticForm_centralForceHamiltonian_sub_iff
    (hm : m ≠ 0) {q p : V} (hq : q ≠ 0) (hqp : ⟪q, p⟫_ℝ = 0) (hU : ContDiffAt ℝ 2 U ‖q‖)
    (hcrit : HasDerivAt (effectivePotential m (angularMomentum (b 0) (b 1) (q, p)) U) 0 ‖q‖)
    (ha : HasDerivAt (deriv (effectivePotential m (angularMomentum (b 0) (b 1) (q, p)) U)) a ‖q‖) :
    (m • stdSymplecticForm.reducedQuadraticForm
      (fderiv ℝ (centralForceEnergyMomentum b m U) (q, p)).ker
      (hessianQuadraticForm (fun x ↦ centralForceHamiltonian m U x -
        angularMomentum (b 0) (b 1) (q, p) / (m * ‖q‖ ^ 2) * angularMomentum (b 0) (b 1) x) (q, p))
      (polar_hessianQuadraticForm_centralForceHamiltonian_sub_eq_zero b hm hq hqp hU hcrit)).PosDef
      ↔ 0 < m * a := by
  rw [← forall_pos_mul_hessianQuadraticForm_centralForceHamiltonian_sub_iff b hm hq hqp hU hcrit ha]
  constructor
  · intro h v hv hvo
    simpa using h (Submodule.Quotient.mk ⟨v, hv⟩)
      (by rwa [Ne, SymplecticForm.ReducedSpace.mk_eq_zero_iff])
  · intro h x hx
    induction x using Submodule.Quotient.induction_on with
    | H u =>
      rw [Ne, SymplecticForm.ReducedSpace.mk_eq_zero_iff] at hx
      simpa using h u u.property hx

end Plane

end TauCeti
