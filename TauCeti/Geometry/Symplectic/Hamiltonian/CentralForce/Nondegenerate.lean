/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.CentralForce.Integrable
public import TauCeti.Geometry.Symplectic.Hamiltonian.CentralForce.Radial
public import TauCeti.Geometry.Symplectic.Hamiltonian.Elliptic
public import TauCeti.Geometry.Symplectic.Hamiltonian.SingularPoint
import TauCeti.Analysis.Calculus.Bilinear
import TauCeti.Analysis.Calculus.Morse.NormSq
import TauCeti.Analysis.Calculus.Morse.OneDimensional
import TauCeti.Analysis.Calculus.Morse.Prod
import TauCeti.Geometry.Symplectic.Hamiltonian.Williamson

/-!
# Circular orbits of planar central forces are nondegenerate rank-one points

A particle of mass `m` in a plane `V`, with orthonormal basis `b`, moving in a central potential
`U`, has the energy–momentum map `F = (H, L) : V × V → ℝ²`
(`TauCeti.centralForceEnergyMomentum`), with `H(q, p) = ‖p‖² / (2m) + U(‖q‖)` and
`L = q₁p₂ - q₂p₁`. Off the collision set its critical points are the points `x = (q, p)` of the
circular orbits, and for `L = 0` the rest points at critical points of `U`: those with
`⟪q, p⟫ = 0` and `U'(‖q‖) = L² / (m ‖q‖³)`, that is, with `r = ‖q‖` a critical point of the
effective potential `U_ℓ(r) = ℓ² / (2 m r²) + U(r)` for `ℓ = L(x)`
(`TauCeti.isRegularPoint_centralForceEnergyMomentum_iff`). There `dF_x` has rank one, with
`dH = Ω dL` for the angular velocity `Ω = ℓ / (m r²)`
(`TauCeti.finrank_range_fderiv_centralForceEnergyMomentum`). This file computes the transversal
type of these singular points in the sense of `TauCeti.SymplecticForm.IsNondegeneratePoint`.

The critical functions at `x`, the functions `μ ∘ F` for the functionals `μ` on `ℝ²` with
`μ ∘ dF_x = 0`, are the multiples of `H - Ω L`
(`TauCeti.comp_centralForceEnergyMomentum_eq_smul_of_comp_fderiv_eq_zero`). The transversal space
`U / (U ∩ U^ω)` of `U = ker dF_x` is a plane, spanned by the classes of the radial displacement
`(q, -p)` and of the radial momentum `(0, q)`. These pair to `ω₀ = ‖q‖²`, and the Hessian of
`H - Ω L` is diagonal on them, with the values

`Hess(H - Ω L)(q, -p) = r² U_ℓ''(r)`,  `Hess(H - Ω L)(0, q) = r² / m`,

computed from the Hessians of the angular momentum, `2 L`
(`TauCeti.hessianQuadraticForm_angularMomentum`), and of the energy
(`TauCeti.hessianQuadraticForm_centralForceHamiltonian_apply`). Hence:

* for `m ≠ 0`, the point `x` is a nondegenerate point of `F` exactly when `U_ℓ''(r) ≠ 0`
  (`TauCeti.isNondegeneratePoint_centralForceEnergyMomentum_iff`);
* at a nondegenerate minimum of the effective potential, `U_ℓ''(r) > 0`, and for `m > 0`, the
  transversal Hessian is positive definite, so it is `ν` times the elliptic block
  `(x² + y²) / 2` of a Darboux basis of the transversal plane, for some `ν > 0`: one elliptic
  block. This is
  `TauCeti.exists_isDarbouxBasis_hessianQuadraticForm_centralForceHamiltonian_sub_eq_smul_elliptic`.

The same statements cover the rest points with `L = 0`, where `p = 0`, `Ω = 0` and `U_0 = U`.

## Main results

* `TauCeti.hessianQuadraticForm_angularMomentum`: the angular momentum is quadratic, with Hessian
  `2 L`.
* `TauCeti.hessianQuadraticForm_centralForceHamiltonian_apply`: the Hessian of the energy is the
  Hessian of `q ↦ U(‖q‖)` plus `‖δp‖² / m`.
* `TauCeti.comp_centralForceEnergyMomentum_eq_smul_of_comp_fderiv_eq_zero`: the critical functions
  at a circular orbit are the multiples of `H - Ω L`.
* `TauCeti.isNondegeneratePoint_centralForceEnergyMomentum_iff`: for `m ≠ 0`, a circular orbit
  is a nondegenerate rank-one point exactly when `U_ℓ''(r) ≠ 0`.
* `TauCeti.exists_isDarbouxBasis_hessianQuadraticForm_centralForceHamiltonian_sub_eq_smul_elliptic`:
  at a nondegenerate minimum of the effective potential its transversal type is one elliptic block.

## References

* A. V. Bolsinov and A. T. Fomenko, *Integrable Hamiltonian Systems: Geometry, Topology,
  Classification*, Chapman & Hall/CRC, 2004, Chapter 1 (nondegenerate singular points of rank
  one).
* V. I. Arnold, *Mathematical Methods of Classical Mechanics*, 2nd ed., Graduate Texts in
  Mathematics 60, Springer, 1989, Section 8 (the effective potential and circular orbits).
-/

public section

noncomputable section

open Module
open scoped InnerProductSpace

namespace TauCeti

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-! ### The Hessians of the angular momentum and of the energy -/

/-- **The angular momentum is quadratic.** Its Hessian at every point is twice the angular
momentum: `Hess L (δq, δp) = 2 L(δq, δp)`. -/
theorem hessianQuadraticForm_angularMomentum (u w : V) (x v : V × V) :
    hessianQuadraticForm (angularMomentum u w) x v = 2 * angularMomentum u w v := by
  -- `L` is the quadratic form `z ↦ B z z` of the bilinear form
  -- `B z z' = ⟪z.1, u⟫⟪z'.2, w⟫ - ⟪z.1, w⟫⟪z'.2, u⟫`.
  let ℓ₁ (a : V) : V × V →L[ℝ] ℝ := (innerSL ℝ a).comp (ContinuousLinearMap.fst ℝ V V)
  let ℓ₂ (a : V) : V × V →L[ℝ] ℝ := (innerSL ℝ a).comp (ContinuousLinearMap.snd ℝ V V)
  let B : V × V →L[ℝ] V × V →L[ℝ] ℝ := (ℓ₁ u).smulRight (ℓ₂ w) - (ℓ₁ w).smulRight (ℓ₂ u)
  have h : angularMomentum u w = fun z ↦ B z z := by
    funext ⟨z₁, z₂⟩
    simp [B, ℓ₁, ℓ₂, real_inner_comm]
  obtain ⟨v₁, v₂⟩ := v
  rw [h, hessianQuadraticForm_apply, B.fderiv_fderiv_apply_self]
  simp [B, ℓ₁, ℓ₂]
  ring

/-- **The Hessian of a central-force Hamiltonian.** Off the collision set, at a point where `U` is
`C²`, the Hessian of `H(q, p) = ‖p‖² / (2m) + U(‖q‖)` on `(δq, δp)` is the Hessian of
`q ↦ U(‖q‖)` on `δq` plus `‖δp‖² / m`. -/
theorem hessianQuadraticForm_centralForceHamiltonian_apply {m : ℝ} {U : ℝ → ℝ} {x : V × V}
    (hU : ContDiffAt ℝ 2 U ‖x.1‖) (hq : x.1 ≠ 0) (v : V × V) :
    hessianQuadraticForm (centralForceHamiltonian m U) x v =
      hessianQuadraticForm (fun z ↦ U ‖z‖) x.1 v.1 + ‖v.2‖ ^ 2 / m := by
  obtain ⟨q, p⟩ := x
  have h : centralForceHamiltonian m U = (fun z : V ↦ U ‖z‖) ∘ Prod.fst +
      ((2 * m)⁻¹ • fun z : V ↦ ‖z‖ ^ 2) ∘ Prod.snd := by
    funext ⟨y₁, y₂⟩
    simp [div_eq_inv_mul, add_comm]
  have hφ : ContDiffAt ℝ 2 (fun z : V ↦ U ‖z‖) q := hU.comp q (contDiffAt_norm ℝ hq)
  have hψ : ContDiffAt ℝ 2 ((2 * m)⁻¹ • fun z : V ↦ ‖z‖ ^ 2) p :=
    (contDiff_const.smul (contDiff_norm_sq ℝ)).contDiffAt
  rw [h, hessianQuadraticForm_comp_fst_add_comp_snd hφ hψ, QuadraticMap.prod_apply,
    hessianQuadraticForm_smul, smul_apply, hessianQuadraticForm_norm_sq, smul_eq_mul]
  ring

/-- The Hessian of `H - Ω L`, for any constant `Ω`, on `v = (δq, δp)`. -/
private theorem hessianQuadraticForm_sub_mul_angularMomentum_apply
    (b : OrthonormalBasis (Fin 2) ℝ V) {m : ℝ} {U : ℝ → ℝ} {x : V × V}
    (hU : ContDiffAt ℝ 2 U ‖x.1‖) (hq : x.1 ≠ 0) (Ω : ℝ) (v : V × V) :
    hessianQuadraticForm (fun y ↦ centralForceHamiltonian m U y -
        Ω * angularMomentum (b 0) (b 1) y) x v =
      hessianQuadraticForm (fun z ↦ U ‖z‖) x.1 v.1 + ‖v.2‖ ^ 2 / m -
        Ω * (2 * angularMomentum (b 0) (b 1) v) := by
  have hL : ContDiffAt ℝ 2 (angularMomentum (b 0) (b 1) : V × V → ℝ) x := by
    have h : angularMomentum (b 0) (b 1) = fun y ↦ centralForceEnergyMomentum b m U y 1 := by
      simp
    rw [h]
    exact contDiffAt_pi.1 (contDiffAt_centralForceEnergyMomentum b hU hq) 1
  have hΩL : ContDiffAt ℝ 2 ((-Ω) • angularMomentum (b 0) (b 1)) x := hL.const_smul (-Ω)
  have h : (fun y ↦ centralForceHamiltonian m U y - Ω * angularMomentum (b 0) (b 1) y) =
      centralForceHamiltonian m U + (-Ω) • angularMomentum (b 0) (b 1) := by
    funext y
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [h, hessianQuadraticForm_add (contDiffAt_centralForceHamiltonian hU hq) hΩL,
    add_apply, hessianQuadraticForm_smul, smul_apply, smul_eq_mul,
    hessianQuadraticForm_centralForceHamiltonian_apply hU hq, hessianQuadraticForm_angularMomentum]
  ring

/-! ### The critical functions at a circular orbit -/

section Circular

variable [FiniteDimensional ℝ V] (b : OrthonormalBasis (Fin 2) ℝ V) {m : ℝ} {U : ℝ → ℝ}
  {x : V × V}

/-- **The critical functions at a circular orbit.** At a point `(q, p)` with `⟪q, p⟫ = 0` and
`U'(‖q‖) = L² / (m ‖q‖³)`, every function `ℓ ∘ F` that is critical there, `ℓ ∘ dF = 0`, is the
multiple `ℓ(1, 0) (H - Ω L)` of `H - Ω L`, for the angular velocity `Ω = L / (m ‖q‖²)`. -/
theorem comp_centralForceEnergyMomentum_eq_smul_of_comp_fderiv_eq_zero {U' : ℝ}
    (hU : HasDerivAt U U' ‖x.1‖) (hq : x.1 ≠ 0) (h0 : ⟪x.1, x.2⟫_ℝ = 0)
    (hU' : U' = angularMomentum (b 0) (b 1) x ^ 2 / (m * ‖x.1‖ ^ 3))
    {ℓ : (Fin 2 → ℝ) →L[ℝ] ℝ}
    (hℓ : ℓ.comp (fderiv ℝ (centralForceEnergyMomentum b m U) x) = 0) :
    ℓ ∘ centralForceEnergyMomentum b m U = ℓ (Pi.single 0 1) • fun y ↦
      centralForceHamiltonian m U y -
        angularMomentum (b 0) (b 1) x / (m * ‖x.1‖ ^ 2) * angularMomentum (b 0) (b 1) y := by
  set Ω := angularMomentum (b 0) (b 1) x / (m * ‖x.1‖ ^ 2)
  -- `ℓ` vanishes on the image of `dF`, which contains `(Ω, 1)`.
  have hw : ℓ ![Ω, 1] = 0 := by
    have hmem : ![Ω, 1] ∈ (fderiv ℝ (centralForceEnergyMomentum b m U) x).range := by
      rw [range_fderiv_centralForceEnergyMomentum b hU hq h0 hU']
      exact Submodule.mem_span_singleton_self _
    obtain ⟨v, hv⟩ := hmem
    rw [← hv, ContinuousLinearMap.coe_coe, ← ContinuousLinearMap.comp_apply, hℓ, zero_apply]
  have hpair : (![Ω, 1] : Fin 2 → ℝ) = Ω • Pi.single 0 1 + Pi.single 1 1 := by
    ext i
    fin_cases i <;> simp
  rw [hpair, map_add, map_smul, smul_eq_mul] at hw
  funext y
  rw [comp_centralForceEnergyMomentum, eq_neg_of_add_eq_zero_right hw]
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

/-- The functional `(a, c) ↦ a - Ω c` kills the image of the differential at a point of a
circular orbit, and composed with `F` it is `H - Ω L`. -/
private theorem exists_comp_fderiv_eq_zero_and_comp_eq {U' : ℝ}
    (hU : HasDerivAt U U' ‖x.1‖) (hq : x.1 ≠ 0) (h0 : ⟪x.1, x.2⟫_ℝ = 0)
    (hU' : U' = angularMomentum (b 0) (b 1) x ^ 2 / (m * ‖x.1‖ ^ 3)) :
    ∃ ℓ₀ : (Fin 2 → ℝ) →L[ℝ] ℝ, ℓ₀.comp (fderiv ℝ (centralForceEnergyMomentum b m U) x) = 0 ∧
      ℓ₀ ∘ centralForceEnergyMomentum b m U = fun y ↦ centralForceHamiltonian m U y -
        angularMomentum (b 0) (b 1) x / (m * ‖x.1‖ ^ 2) * angularMomentum (b 0) (b 1) y := by
  refine ⟨ContinuousLinearMap.proj 0 - (angularMomentum (b 0) (b 1) x / (m * ‖x.1‖ ^ 2)) •
    ContinuousLinearMap.proj 1, ContinuousLinearMap.ext fun v ↦ ?_, ?_⟩
  · rw [ContinuousLinearMap.comp_apply,
      fderiv_centralForceEnergyMomentum_apply_eq_smul b hU hq h0 hU']
    simp [mul_comm]
  · rw [comp_centralForceEnergyMomentum]
    simp [sub_eq_add_neg]

/-! ### The transversal plane -/

/-- The transversal space at a point of a circular orbit has dimension two. -/
private theorem finrank_reducedSpace_ker_fderiv_centralForceEnergyMomentum {U' : ℝ}
    (hU : HasDerivAt U U' ‖x.1‖) (hq : x.1 ≠ 0) (h0 : ⟪x.1, x.2⟫_ℝ = 0)
    (hU' : U' = angularMomentum (b 0) (b 1) x ^ 2 / (m * ‖x.1‖ ^ 3)) :
    finrank ℝ ((stdSymplecticForm (V := V)).ReducedSpace
      (fderiv ℝ (centralForceEnergyMomentum b m U) x).ker) = 2 := by
  have h := (stdSymplecticForm (V := V)).finrank_reducedSpace_ker_fderiv
    (hasFDerivAt_centralForceEnergyMomentum b (m := m) hU hq).differentiableAt
    fun ℓ ℓ' ↦ stdSymplecticForm_poissonBracket_comp_centralForceEnergyMomentum b m U ℓ ℓ' x
  rw [finrank_range_fderiv_centralForceEnergyMomentum b hU hq h0 hU', Module.finrank_prod,
    finrank_eq_card_basis b.toBasis, Fintype.card_fin] at h
  omega

/-- The classes of the radial displacement `(q, -p)` and of the radial momentum `(0, q)` form a
basis of the transversal space at a point of a circular orbit. -/
private theorem exists_basis_reducedSpace_ker_fderiv_centralForceEnergyMomentum {U' : ℝ}
    (hU : HasDerivAt U U' ‖x.1‖) (hq : x.1 ≠ 0) (h0 : ⟪x.1, x.2⟫_ℝ = 0)
    (hU' : U' = angularMomentum (b 0) (b 1) x ^ 2 / (m * ‖x.1‖ ^ 3)) :
    ∃ (e : Basis (Fin 2) ℝ ((stdSymplecticForm (V := V)).ReducedSpace
        (fderiv ℝ (centralForceEnergyMomentum b m U) x).ker))
      (u₀ u₁ : (fderiv ℝ (centralForceEnergyMomentum b m U) x).ker),
      (u₀ : V × V) = (x.1, -x.2) ∧ (u₁ : V × V) = (0, x.1) ∧
        e 0 = Submodule.Quotient.mk u₀ ∧ e 1 = Submodule.Quotient.mk u₁ := by
  have hT := fderiv_centralForceEnergyMomentum_apply_eq_smul b hU hq h0 hU'
  -- Both vectors are tangent to the level set of `L`, so to that of `F`.
  have h₀ : (x.1, -x.2) ∈ (fderiv ℝ (centralForceEnergyMomentum b m U) x).ker := by
    obtain ⟨q, p⟩ := x
    rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, hT, fderiv_angularMomentum_apply]
    simp
  have h₁ : ((0 : V), x.1) ∈ (fderiv ℝ (centralForceEnergyMomentum b m U) x).ker := by
    rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, hT, fderiv_angularMomentum_apply]
    obtain ⟨q, p⟩ := x
    simp [mul_comm]
  set ω := (stdSymplecticForm (V := V)).reduction
    (fderiv ℝ (centralForceEnergyMomentum b m U) x).ker
  set e₀ := (Submodule.Quotient.mk ⟨_, h₀⟩ : (stdSymplecticForm (V := V)).ReducedSpace _)
  set e₁ := (Submodule.Quotient.mk ⟨_, h₁⟩ : (stdSymplecticForm (V := V)).ReducedSpace _)
  -- The two classes pair to `‖q‖² ≠ 0` under the reduced symplectic form.
  have hω : ω e₀ e₁ = ‖x.1‖ ^ 2 := by
    simp [ω, e₀, e₁]
  have hr : ‖x.1‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.2 hq)
  have hli : LinearIndependent ℝ ![e₀, e₁] := by
    refine LinearIndependent.pair_iff.2 fun s t hst ↦ ⟨?_, ?_⟩
    · have h := ω.apply_smul_add_smul e₀ e₁ s t 0 1
      rw [hst, zero_smul, zero_add, one_smul, hω] at h
      simpa [hr] using h.symm
    · have h := ω.apply_smul_add_smul e₀ e₁ 1 0 s t
      rw [hst, zero_smul, add_zero, one_smul, hω] at h
      simpa [hr] using h.symm
  refine ⟨basisOfLinearIndependentOfCardEqFinrank hli ?_, ⟨_, h₀⟩, ⟨_, h₁⟩, rfl, rfl, ?_, ?_⟩
  · rw [Fintype.card_fin, finrank_reducedSpace_ker_fderiv_centralForceEnergyMomentum b hU hq h0 hU']
  · simp [e₀]
  · simp [e₁]

/-- At a point of a circular orbit, the Hessian of `H - Ω L` descends to the transversal
space. -/
private theorem exists_reducedQuadraticForm_eq_hessianQuadraticForm {U' : ℝ}
    (hU : ContDiffAt ℝ 2 U ‖x.1‖) (hUd : HasDerivAt U U' ‖x.1‖) (hq : x.1 ≠ 0)
    (h0 : ⟪x.1, x.2⟫_ℝ = 0) (hU' : U' = angularMomentum (b 0) (b 1) x ^ 2 / (m * ‖x.1‖ ^ 3)) :
    ∃ Q : QuadraticForm ℝ ((stdSymplecticForm (V := V)).ReducedSpace
        (fderiv ℝ (centralForceEnergyMomentum b m U) x).ker),
      ∀ u, Q (Submodule.Quotient.mk u) = hessianQuadraticForm (fun y ↦
        centralForceHamiltonian m U y -
          angularMomentum (b 0) (b 1) x / (m * ‖x.1‖ ^ 2) * angularMomentum (b 0) (b 1) y) x u := by
  obtain ⟨ℓ₀, hℓ₀, hcomp⟩ := exists_comp_fderiv_eq_zero_and_comp_eq b hUd hq h0 hU'
  rw [← hcomp]
  exact ⟨_, (stdSymplecticForm (V := V)).reducedQuadraticForm_mk _ _ fun _ hw u _ ↦
    (stdSymplecticForm (V := V)).polar_hessianQuadraticForm_eq_zero_of_mem_orthogonal
      (contDiffAt_centralForceEnergyMomentum b hU hq) hℓ₀
      (fun ℓ' ↦ .of_forall fun y ↦
        stdSymplecticForm_poissonBracket_comp_centralForceEnergyMomentum b m U ℓ' ℓ₀ y)
      hw.2 u⟩

/-- At a point of a circular orbit, the transversal Hessians of all the critical functions
`ℓ ∘ F` span the line of the transversal Hessian of `H - Ω L`. -/
private theorem span_range_eq_span_range_const {U' : ℝ}
    (hU : HasDerivAt U U' ‖x.1‖) (hq : x.1 ≠ 0) (h0 : ⟪x.1, x.2⟫_ℝ = 0)
    (hU' : U' = angularMomentum (b 0) (b 1) x ^ 2 / (m * ‖x.1‖ ^ 3))
    {Q : QuadraticForm ℝ ((stdSymplecticForm (V := V)).ReducedSpace
      (fderiv ℝ (centralForceEnergyMomentum b m U) x).ker)}
    (hQ : ∀ u, Q (Submodule.Quotient.mk u) = hessianQuadraticForm (fun y ↦
      centralForceHamiltonian m U y -
        angularMomentum (b 0) (b 1) x / (m * ‖x.1‖ ^ 2) * angularMomentum (b 0) (b 1) y) x u)
    {Q' : {ℓ : (Fin 2 → ℝ) →L[ℝ] ℝ // ℓ.comp (fderiv ℝ (centralForceEnergyMomentum b m U) x) = 0} →
      QuadraticForm ℝ ((stdSymplecticForm (V := V)).ReducedSpace
        (fderiv ℝ (centralForceEnergyMomentum b m U) x).ker)}
    (hQ' : ∀ ℓ u, Q' ℓ (Submodule.Quotient.mk u) =
      hessianQuadraticForm (ℓ.val ∘ centralForceEnergyMomentum b m U) x u) :
    Submodule.span ℝ (Set.range Q') = Submodule.span ℝ (Set.range fun _ : Unit ↦ Q) := by
  obtain ⟨ℓ₀, hℓ₀, hcomp⟩ := exists_comp_fderiv_eq_zero_and_comp_eq b hU hq h0 hU'
  refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)
  · rintro _ ⟨ℓ, rfl⟩
    have h : Q' ℓ = ℓ.val (Pi.single 0 1) • Q := by
      ext v
      induction v using Submodule.Quotient.induction_on with
      | H u =>
        rw [hQ', smul_apply, hQ, comp_centralForceEnergyMomentum_eq_smul_of_comp_fderiv_eq_zero b
          hU hq h0 hU' ℓ.property, hessianQuadraticForm_smul, smul_apply]
    rw [h]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨(), rfl⟩)
  · rintro _ ⟨-, rfl⟩
    refine Submodule.subset_span ⟨⟨ℓ₀, hℓ₀⟩, ?_⟩
    ext v
    induction v using Submodule.Quotient.induction_on with
    | H u => rw [hQ', hQ, hcomp]

/-- On the basis of the classes of `(q, -p)` and `(0, q)`, the transversal Hessian of `H - Ω L`
takes the values `‖q‖² U_ℓ''(‖q‖)` and `‖q‖² / m`, and the two basis vectors are orthogonal for
it. -/
private theorem exists_basis_apply_eq {U' : ℝ} (hm : m ≠ 0) (hU : ContDiffAt ℝ 2 U ‖x.1‖)
    (hUd : HasDerivAt U U' ‖x.1‖) (hq : x.1 ≠ 0) (h0 : ⟪x.1, x.2⟫_ℝ = 0)
    (hU' : U' = angularMomentum (b 0) (b 1) x ^ 2 / (m * ‖x.1‖ ^ 3))
    {Q : QuadraticForm ℝ ((stdSymplecticForm (V := V)).ReducedSpace
      (fderiv ℝ (centralForceEnergyMomentum b m U) x).ker)}
    (hQ : ∀ u, Q (Submodule.Quotient.mk u) = hessianQuadraticForm (fun y ↦
      centralForceHamiltonian m U y -
        angularMomentum (b 0) (b 1) x / (m * ‖x.1‖ ^ 2) * angularMomentum (b 0) (b 1) y) x u) :
    ∃ e : Basis (Fin 2) ℝ ((stdSymplecticForm (V := V)).ReducedSpace
        (fderiv ℝ (centralForceEnergyMomentum b m U) x).ker),
      Q (e 0) = ‖x.1‖ ^ 2 *
          iteratedDeriv 2 (effectivePotential m (angularMomentum (b 0) (b 1) x) U) ‖x.1‖ ∧
        Q (e 1) = ‖x.1‖ ^ 2 / m ∧ QuadraticMap.polar Q (e 0) (e 1) = 0 := by
  obtain ⟨e, u₀, u₁, hu₀, hu₁, he₀, he₁⟩ :=
    exists_basis_reducedSpace_ker_fderiv_centralForceEnergyMomentum b hUd hq h0 hU'
  have hr : ‖x.1‖ ≠ 0 := norm_ne_zero_iff.2 hq
  have hH := hessianQuadraticForm_sub_mul_angularMomentum_apply b (m := m) hU hq
    (angularMomentum (b 0) (b 1) x / (m * ‖x.1‖ ^ 2))
  -- In the plane, `p ⊥ q` gives `‖p‖² ‖q‖² = L²`.
  have hp : ‖x.2‖ ^ 2 * ‖x.1‖ ^ 2 = angularMomentum (b 0) (b 1) x ^ 2 := by
    rw [sq_angularMomentum b x, h0]
    ring
  have hrad := hessianQuadraticForm_comp_norm_apply_self hU hq
  rw [hessianQuadraticForm_real_apply] at hrad
  have hneg : angularMomentum (b 0) (b 1) (x.1, -x.2) = -angularMomentum (b 0) (b 1) x := by
    obtain ⟨q, p⟩ := x
    simp
    ring
  have hzero : angularMomentum (b 0) (b 1) ((0 : V), x.1) = 0 := by
    simp
  refine ⟨e, ?_, ?_, ?_⟩
  · rw [he₀, hQ, hu₀, hH, iteratedDeriv_two_effectivePotential hU hr, hneg, norm_neg, hrad]
    field_simp
    linear_combination hp
  · rw [he₁, hQ, hu₁, hH, hzero, QuadraticMap.map_zero]
    ring
  · have hsum : angularMomentum (b 0) (b 1) (x.1, -x.2 + x.1) =
        -angularMomentum (b 0) (b 1) x := by
      obtain ⟨q, p⟩ := x
      simp [inner_add_left]
      ring
    have hnorm : ‖-x.2 + x.1‖ ^ 2 = ‖x.2‖ ^ 2 + ‖x.1‖ ^ 2 := by
      rw [norm_add_sq_real, norm_neg, inner_neg_left, real_inner_comm, h0]
      ring
    simp only [QuadraticMap.polar, he₀, he₁, ← Submodule.Quotient.mk_add, hQ]
    simp [hu₀, hu₁, hH, hsum, hneg, hzero, hnorm]
    ring

/-! ### Nondegeneracy and the elliptic type -/

/-- **Circular orbits of a planar central force are nondegenerate rank-one points exactly at
nondegenerate critical points of the effective potential.** Let `x = (q, p)` lie off the collision
set with `⟪q, p⟫ = 0` and `U'(‖q‖) = ℓ² / (m ‖q‖³)` for `ℓ = L(x)`, a point of a circular orbit
or, for `ℓ = 0`, a rest point, where `U` is `C²` at `‖q‖`, and let `m ≠ 0`. Then `x` is a
nondegenerate point of the energy–momentum map `F = (H, L)` exactly when `U_ℓ''(‖q‖) ≠ 0` for the
effective potential `U_ℓ(r) = ℓ² / (2 m r²) + U(r)`. -/
theorem isNondegeneratePoint_centralForceEnergyMomentum_iff (hm : m ≠ 0)
    (hU : ContDiffAt ℝ 2 U ‖x.1‖) (hq : x.1 ≠ 0) (h0 : ⟪x.1, x.2⟫_ℝ = 0)
    (hU' : deriv U ‖x.1‖ = angularMomentum (b 0) (b 1) x ^ 2 / (m * ‖x.1‖ ^ 3)) :
    (stdSymplecticForm (V := V)).IsNondegeneratePoint (centralForceEnergyMomentum b m U) x ↔
      iteratedDeriv 2 (effectivePotential m (angularMomentum (b 0) (b 1) x) U) ‖x.1‖ ≠ 0 := by
  have hUd : HasDerivAt U (deriv U ‖x.1‖) ‖x.1‖ := (hU.differentiableAt two_ne_zero).hasDerivAt
  obtain ⟨Q, hQ⟩ := exists_reducedQuadraticForm_eq_hessianQuadraticForm b hU hUd hq h0 hU'
  obtain ⟨e, he₀, he₁, he₀₁⟩ := exists_basis_apply_eq b hm hU hUd hq h0 hU' hQ
  have hr : ‖x.1‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.2 hq)
  -- All the critical functions are multiples of `H - Ω L`, and the transversal space is a plane,
  -- so nondegeneracy is that of the single transversal Hessian `Q`, which is diagonal in `e`.
  rw [SymplecticForm.isNondegeneratePoint_iff_of_poissonBracket
      (contDiffAt_centralForceEnergyMomentum b hU hq)
      fun ℓ ℓ' ↦ .of_forall fun y ↦
        stdSymplecticForm_poissonBracket_comp_centralForceEnergyMomentum b m U ℓ' ℓ y,
    SymplecticForm.isNondegenerateQuadraticFamily_iff_of_span_eq
      (span_range_eq_span_range_const b hUd hq h0 hU' hQ fun ℓ u ↦
        SymplecticForm.reducedQuadraticForm_mk _ _ _ _ u),
    SymplecticForm.isNondegenerateQuadraticFamily_const_iff
      (finrank_reducedSpace_ker_fderiv_centralForceEnergyMomentum b hUd hq h0 hU'),
    ← QuadraticMap.nondegenerate_polar_iff]
  refine (LinearMap.BilinForm.iIsOrtho.nondegenerate_iff_not_isOrtho_basis_self
    (QuadraticMap.polarBilin Q) e
    (LinearMap.BilinForm.iIsOrtho_def.2 fun i j hij ↦ ?_)).trans ?_
  · fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · simp [he₀₁]
    · simp [QuadraticMap.polar_comm Q (e 1), he₀₁]
    · exact absurd rfl hij
  · simp [Fin.forall_fin_two, QuadraticMap.polar_self, he₀, he₁, hm, hr]

/-- **At a nondegenerate minimum of the effective potential, a circular orbit is of elliptic
type.** Let `x = (q, p)` be a point of a circular orbit, or a rest point, as in
`TauCeti.isNondegeneratePoint_centralForceEnergyMomentum_iff`, with `m > 0` and
`U_ℓ''(‖q‖) > 0`. The critical functions at `x` are the multiples of `H - Ω L`, for
`Ω = ℓ / (m ‖q‖²)`, and the Hessian of `H - Ω L` on the transversal plane is `ν` times the elliptic
block `(x² + y²) / 2` of a Darboux basis of that plane, for some `ν > 0`: the transversal Williamson
type is one elliptic block. -/
theorem exists_isDarbouxBasis_hessianQuadraticForm_centralForceHamiltonian_sub_eq_smul_elliptic
    (hm : 0 < m) (hU : ContDiffAt ℝ 2 U ‖x.1‖) (hq : x.1 ≠ 0) (h0 : ⟪x.1, x.2⟫_ℝ = 0)
    (hU' : deriv U ‖x.1‖ = angularMomentum (b 0) (b 1) x ^ 2 / (m * ‖x.1‖ ^ 3))
    (hmin : 0 < iteratedDeriv 2 (effectivePotential m (angularMomentum (b 0) (b 1) x) U) ‖x.1‖) :
    ∃ (e : Basis (Fin 1 × Fin 2) ℝ ((stdSymplecticForm (V := V)).ReducedSpace
        (fderiv ℝ (centralForceEnergyMomentum b m U) x).ker)) (ν : ℝ),
      ((stdSymplecticForm (V := V)).reduction _).IsDarbouxBasis e ∧ 0 < ν ∧
        ∀ u : (fderiv ℝ (centralForceEnergyMomentum b m U) x).ker,
          hessianQuadraticForm (fun y ↦ centralForceHamiltonian m U y -
            angularMomentum (b 0) (b 1) x / (m * ‖x.1‖ ^ 2) * angularMomentum (b 0) (b 1) y) x u =
              ν * SymplecticForm.elliptic e 0 (Submodule.Quotient.mk u) := by
  have hUd : HasDerivAt U (deriv U ‖x.1‖) ‖x.1‖ := (hU.differentiableAt two_ne_zero).hasDerivAt
  obtain ⟨Q, hQ⟩ := exists_reducedQuadraticForm_eq_hessianQuadraticForm b hU hUd hq h0 hU'
  obtain ⟨e, he₀, he₁, he₀₁⟩ := exists_basis_apply_eq b hm.ne' hU hUd hq h0 hU' hQ
  -- In the orthogonal basis `e`, the form `Q` is the diagonal form with the positive entries
  -- `‖q‖² U_ℓ''(‖q‖)` and `‖q‖² / m`.
  have hpos : Q.PosDef := by
    have horth : (QuadraticMap.associated (R := ℝ) Q).IsOrthoᵢ e := by
      refine LinearMap.isOrthoᵢ_def.2 fun i j hij ↦ ?_
      rw [QuadraticMap.associated_isOrtho, ← QuadraticMap.isOrtho_polarBilin,
        QuadraticMap.polarBilin_apply_apply]
      fin_cases i <;> fin_cases j
      · exact absurd rfl hij
      · exact he₀₁
      · rwa [QuadraticMap.polar_comm]
      · exact absurd rfl hij
    have h := (QuadraticMap.posDef_weightedSumSquares_iff fun i ↦ Q (e i)).2
      (Fin.forall_fin_two.2 ⟨he₀ ▸ by positivity, he₁ ▸ by positivity⟩)
    rw [← Q.basisRepr_eq_of_iIsOrtho e horth] at h
    convert h.comp e.equivFun.toLinearMap e.equivFun.injective
    ext v
    simp [QuadraticMap.basisRepr]
  obtain ⟨n, d, ν, hd, hν, hQd⟩ :=
    ((stdSymplecticForm (V := V)).reduction _).exists_isDarbouxBasis_eq_sum_smul_elliptic_of_posDef
      hpos
  -- The transversal plane carries exactly one block.
  obtain rfl : n = 1 := by
    have h := finrank_eq_card_basis d
    rw [finrank_reducedSpace_ker_fderiv_centralForceEnergyMomentum b hUd hq h0 hU',
      Fintype.card_prod, Fintype.card_fin, Fintype.card_fin] at h
    omega
  refine ⟨d, ν 0, hd, hν 0, fun u ↦ ?_⟩
  rw [← hQ, hQd, Fin.sum_univ_one, smul_apply, smul_eq_mul]

end Circular

end TauCeti
