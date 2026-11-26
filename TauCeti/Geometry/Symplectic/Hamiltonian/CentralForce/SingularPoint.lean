/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.CentralForce.Polar
public import TauCeti.Geometry.Symplectic.Hamiltonian.SingularPoint
import TauCeti.Analysis.Calculus.Morse.OneDimensional
import TauCeti.Analysis.Calculus.Morse.Prod

/-!
# Circular orbits of planar central forces as singular points

A particle of mass `m` in the plane `V`, moving in a central potential `U`, has the
energy–momentum map `F = (H, L) : V × V → ℝ²` (`TauCeti.centralForceEnergyMomentum`), a completely
integrable system off the collision set `q = 0`. Its singular points there are the points of the
circular orbits: the radial momentum vanishes, `⟪q, p⟫ = 0`, and `‖q‖` is a critical point of the
effective potential `U_L(r) = L² / (2 m r²) + U(r)` of the angular momentum `L` of the point
(`TauCeti.isRegularPoint_centralForceEnergyMomentum_iff`). For `L = 0` they are the rest points
`p = 0` at the critical points of `U`. This file computes the local type of these singular points
in the sense of Eliasson's nondegeneracy (`TauCeti.SymplecticForm.IsNondegeneratePoint`).

At such a point `F` has rank one
(`TauCeti.finrank_range_fderiv_centralForceEnergyMomentum`): `dH = κ dL` for the angular velocity
`κ = L / (m ‖q‖²)`, and `dL ≠ 0`. The critical function is `H - κ L`. In the polar canonical
coordinates `((r, p_r), (θ, L))` of `TauCeti.polarCanonical`, in which
`F = (p_r² / (2m) + U_L(r), L)` and the standard form is `dr ∧ dp_r + dθ ∧ dL`, the kernel of
`dF` is `{δL = 0}`, its symplectic complement is the line of `∂_θ`, the generator of the rotations,
and the transversal space is the plane of the radial pair `(r, p_r)`. On it the transversal
Hessian of `H - κ L` is

`U_L''(‖q‖) δr² + δp_r² / m`

(`TauCeti.hessianQuadraticForm_centralForceHamiltonian_sub_mul_angularMomentum`), where `δr` and
`δp_r` are read off with the differential of the radial projection `(q, p) ↦ (‖q‖, p_r)`. Hence:

* the point is a nondegenerate point of `F` exactly when `U_L''(‖q‖) ≠ 0`
  (`TauCeti.isNondegeneratePoint_centralForceEnergyMomentum_iff`);
* the Hessian of `H - κ L` descends to the transversal plane
  (`TauCeti.polar_hessianQuadraticForm_centralForceHamiltonian_sub_mul_angularMomentum_eq_zero`);
* at a nondegenerate minimum of the effective potential, for a positive mass, the transversal
  Hessian is positive outside `(ker dF)^ω`
  (`TauCeti.hessianQuadraticForm_centralForceHamiltonian_sub_mul_angularMomentum_pos`), so its
  reduction to the transversal plane is positive definite
  (`TauCeti.posDef_reducedQuadraticForm_centralForceHamiltonian_sub_mul_angularMomentum`): the
  transversal reduction gives one elliptic block, the linearization of the stable circular orbit.
  By the same formula, at a nondegenerate maximum the transversal Hessian is indefinite, a
  hyperbolic block.

The computation is done in polar canonical coordinates, where the transversal Hessians are all
multiples of one quadratic form on a symplectic plane, and transported to `V × V` along the
polar canonical parametrization, whose differential is a linear symplectomorphism
(`TauCeti.SymplecticForm.isNondegeneratePoint_comp_right_iff_of_isSymplectomorphism`).

## Main results

* `TauCeti.finrank_range_fderiv_centralForceEnergyMomentum`: circular orbits have rank one.
* `TauCeti.isNondegeneratePoint_centralForceEnergyMomentum_iff`: a circular orbit is a
  nondegenerate point exactly when `U_L''(‖q‖) ≠ 0`.
* `TauCeti.hessianQuadraticForm_centralForceHamiltonian_sub_mul_angularMomentum`: the transversal
  Hessian `U_L''(‖q‖) δr² + δp_r² / m`.
* `TauCeti.hessianQuadraticForm_centralForceHamiltonian_sub_mul_angularMomentum_pos`,
  `TauCeti.posDef_reducedQuadraticForm_centralForceHamiltonian_sub_mul_angularMomentum`: stable
  circular orbits are elliptic.

## References

* L. H. Eliasson, *Normal forms for Hamiltonian systems with Poisson commuting integrals —
  elliptic case*, Commentarii Mathematici Helvetici 65 (1990), 4–35.
* A. V. Bolsinov and A. T. Fomenko, *Integrable Hamiltonian Systems: Geometry, Topology,
  Classification*, Chapman & Hall/CRC, 2004, Chapter 1.
* V. I. Arnold, *Mathematical Methods of Classical Mechanics*, 2nd ed., Graduate Texts in
  Mathematics 60, Springer, 1989, Section 8 (motion in a central field).
-/

public section

noncomputable section

open Module
open scoped InnerProductSpace ContDiff Topology

namespace TauCeti

/-! ### The energy–momentum map in polar canonical coordinates -/

section Polar

/-- The symplectic form `dr ∧ dp_r + dθ ∧ dL` of the polar canonical coordinates
`((r, p_r), (θ, L))`. -/
private abbrev polarForm : SymplecticForm ((ℝ × ℝ) × (ℝ × ℝ)) :=
  (stdSymplecticForm (V := ℝ)).prod (stdSymplecticForm (V := ℝ))

variable {m ℓ r₀ θ₀ : ℝ} {U : ℝ → ℝ}

/-- The energy–momentum map `(p_r² / (2m) + U_L(r), L)` of a planar central force in the polar
canonical coordinates `((r, p_r), (θ, L))`. -/
private def polarEnergyMomentum (m : ℝ) (U : ℝ → ℝ) (y : (ℝ × ℝ) × (ℝ × ℝ)) : Fin 2 → ℝ :=
  ![y.1.2 ^ 2 / (2 * m) + effectivePotential m y.2.2 U y.1.1, y.2.2]

/-- The angular momentum coordinate `((r, p_r), (θ, L)) ↦ L`. -/
private def polarL : (ℝ × ℝ) × (ℝ × ℝ) →L[ℝ] ℝ :=
  (ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ (ℝ × ℝ) (ℝ × ℝ))

@[simp]
private theorem polarL_apply (δ : (ℝ × ℝ) × (ℝ × ℝ)) : polarL δ = δ.2.2 := rfl

/-- The differential `δ ↦ (κ δL, δL)` of the polar energy–momentum map at a point of a circular
orbit, with angular velocity `κ`. -/
private def polarDiff (κ : ℝ) : (ℝ × ℝ) × (ℝ × ℝ) →L[ℝ] Fin 2 → ℝ :=
  ContinuousLinearMap.pi ![κ • polarL, polarL]

@[simp]
private theorem polarDiff_apply (κ : ℝ) (δ : (ℝ × ℝ) × (ℝ × ℝ)) :
    polarDiff κ δ = ![κ * δ.2.2, δ.2.2] := by
  ext i
  fin_cases i <;> simp [polarDiff]

/-- At a point `((r₀, 0), (θ₀, ℓ))` where `U'(r₀) = ℓ² / (m r₀³)`, the differential of the polar
energy–momentum map is `δ ↦ (κ δL, δL)` with `κ = ℓ / (m r₀²)`. -/
private theorem hasFDerivAt_polarEnergyMomentum {U' : ℝ} (hr₀ : r₀ ≠ 0)
    (hU : HasDerivAt U U' r₀) (hc : U' = ℓ ^ 2 / (m * r₀ ^ 3)) :
    HasFDerivAt (polarEnergyMomentum m U) (polarDiff (ℓ / (m * r₀ ^ 2))) ((r₀, 0), (θ₀, ℓ)) := by
  set x₀ : (ℝ × ℝ) × (ℝ × ℝ) := ((r₀, 0), (θ₀, ℓ))
  have hr : HasFDerivAt (fun y : (ℝ × ℝ) × (ℝ × ℝ) ↦ y.1.1) _ x₀ :=
    (hasFDerivAt_fst (𝕜 := ℝ) (p := x₀)).fst
  have hp : HasFDerivAt (fun y : (ℝ × ℝ) × (ℝ × ℝ) ↦ y.1.2) _ x₀ :=
    (hasFDerivAt_fst (𝕜 := ℝ) (p := x₀)).snd
  have hL : HasFDerivAt (fun y : (ℝ × ℝ) × (ℝ × ℝ) ↦ y.2.2) polarL x₀ :=
    (hasFDerivAt_snd (𝕜 := ℝ) (p := x₀)).snd
  have hψ := ((hasDerivAt_pow 2 r₀).inv (pow_ne_zero 2 hr₀)).const_mul (2 * m)⁻¹
  have hH := HasFDerivAt.add (HasFDerivAt.mul_const (hp.pow 2) (2 * m)⁻¹)
    (HasFDerivAt.add (HasFDerivAt.mul (hL.pow 2) (hψ.comp_hasFDerivAt x₀ hr))
      (hU.comp_hasFDerivAt x₀ hr))
  have hH' : HasFDerivAt (fun y : (ℝ × ℝ) × (ℝ × ℝ) ↦
      y.1.2 ^ 2 / (2 * m) + effectivePotential m y.2.2 U y.1.1)
      ((ℓ / (m * r₀ ^ 2)) • polarL) x₀ := by
    refine (hH.congr_of_eventuallyEq (.of_forall fun y ↦ ?_)).congr_fderiv ?_
    · simp only [effectivePotential_apply, Pi.add_apply, Pi.mul_apply, Function.comp_apply,
        Pi.inv_apply]
      ring
    · refine ContinuousLinearMap.ext fun δ ↦ ?_
      simp only [add_apply, smul_apply, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.coe_fst', Function.comp_apply, Pi.inv_apply, polarL_apply, smul_eq_mul,
        nsmul_eq_mul, hc, x₀]
      field_simp
      ring
  rw [hasFDerivAt_pi']
  intro i
  fin_cases i
  · simpa [polarEnergyMomentum, polarDiff] using hH'
  · simpa [polarEnergyMomentum, polarDiff] using hL

/-- The polar energy–momentum map is `C²` off `r = 0` where the potential is. -/
private theorem contDiffAt_polarEnergyMomentum (hm : m ≠ 0) {y : (ℝ × ℝ) × (ℝ × ℝ)}
    (hr : y.1.1 ≠ 0) (hU : ContDiffAt ℝ 2 U y.1.1) :
    ContDiffAt ℝ 2 (polarEnergyMomentum m U) y := by
  rw [contDiffAt_pi]
  intro i
  fin_cases i
  · simp only [polarEnergyMomentum, Fin.zero_eta, Matrix.cons_val_zero, effectivePotential_apply]
    fun_prop (disch := simp [hm, hr])
  · simp only [polarEnergyMomentum, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    fun_prop

/-- On the hyperplane `L = ℓ`, the polar energy–momentum map only depends on `(r, p_r)`: the
Hessian of `y ↦ c (U_ℓ(r) + p_r² / (2m)) + C` at `((r₀, 0), z)` is
`c (U_ℓ''(r₀) δr² + δp_r² / m)`. -/
private theorem hessianQuadraticForm_radial (hm : m ≠ 0) (hr₀ : r₀ ≠ 0)
    (hU : ContDiffAt ℝ 2 U r₀) (c C : ℝ) (z : ℝ × ℝ) (δ : (ℝ × ℝ) × (ℝ × ℝ)) :
    hessianQuadraticForm (fun y : (ℝ × ℝ) × (ℝ × ℝ) ↦
        c * (effectivePotential m ℓ U y.1.1 + y.1.2 ^ 2 / (2 * m)) + C) ((r₀, 0), z) δ =
      c * (iteratedDeriv 2 (effectivePotential m ℓ U) r₀ * δ.1.1 ^ 2 + δ.1.2 ^ 2 / m) := by
  set ψ : ℝ × ℝ → ℝ := (fun r ↦ effectivePotential m ℓ U r) ∘ Prod.fst +
    (fun p ↦ p ^ 2 / (2 * m)) ∘ Prod.snd
  have hVℓ : ContDiffAt ℝ 2 (effectivePotential m ℓ U) r₀ := by
    have h : effectivePotential m ℓ U = fun r ↦ ℓ ^ 2 / (2 * m * r ^ 2) + U r :=
      funext (effectivePotential_apply m ℓ U)
    rw [h]
    fun_prop (disch := simp [hm, hr₀])
  have hψ : ContDiffAt ℝ 2 ψ (r₀, 0) := (hVℓ.comp _ contDiffAt_fst).add (by fun_prop)
  have hquad : iteratedDeriv 2 (fun p : ℝ ↦ p ^ 2 / (2 * m)) 0 = 1 / m := by
    norm_num [iteratedDeriv_div_const, iteratedDeriv_pow, Nat.descFactorial, div_mul_cancel_left₀]
  have hf : (fun y : (ℝ × ℝ) × (ℝ × ℝ) ↦
      c * (effectivePotential m ℓ U y.1.1 + y.1.2 ^ 2 / (2 * m)) + C) =
      fun y ↦ (c • (ψ ∘ ContinuousLinearMap.fst ℝ (ℝ × ℝ) (ℝ × ℝ))) y + C := by
    funext y
    simp [ψ]
  rw [hf, hessianQuadraticForm_add_const, hessianQuadraticForm_smul, smul_apply,
    ContinuousLinearMap.hessianQuadraticForm_comp _ (by simpa using hψ)]
  simp only [QuadraticMap.comp_apply, ContinuousLinearMap.coe_coe,
    ContinuousLinearMap.coe_fst', ψ]
  rw [hessianQuadraticForm_comp_fst_add_comp_snd hVℓ (by fun_prop), QuadraticMap.prod_apply,
    hessianQuadraticForm_real_apply, hessianQuadraticForm_real_apply, hquad, smul_eq_mul]
  ring

/-- **The transversal Hessian in polar coordinates.** At a point `((r₀, 0), (θ₀, ℓ))` with
`r₀ ≠ 0`, along a vector `δ` with `δL = 0` the Hessian of `l ∘ (H, L)` is
`l(1, 0) (U_ℓ''(r₀) δr² + δp_r² / m)`. -/
private theorem hessianQuadraticForm_polarEnergyMomentum (hm : m ≠ 0) (hr₀ : r₀ ≠ 0)
    (hU : ContDiffAt ℝ 2 U r₀) (l : (Fin 2 → ℝ) →L[ℝ] ℝ) {δ : (ℝ × ℝ) × (ℝ × ℝ)}
    (hδ : δ.2.2 = 0) :
    hessianQuadraticForm (l ∘ polarEnergyMomentum m U) ((r₀, 0), (θ₀, ℓ)) δ =
      l (Pi.single 0 1) *
        (iteratedDeriv 2 (effectivePotential m ℓ U) r₀ * δ.1.1 ^ 2 + δ.1.2 ^ 2 / m) := by
  set x₀ : (ℝ × ℝ) × (ℝ × ℝ) := ((r₀, 0), (θ₀, ℓ))
  set g := l ∘ polarEnergyMomentum m U
  -- The projection `P` onto the hyperplane `L = 0`, and the translation by `a` back to `L = ℓ`.
  set P : (ℝ × ℝ) × (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) × (ℝ × ℝ) :=
    (ContinuousLinearMap.fst ℝ (ℝ × ℝ) (ℝ × ℝ)).prod
      (((ContinuousLinearMap.inl ℝ ℝ ℝ).comp (ContinuousLinearMap.fst ℝ ℝ ℝ)).comp
        (ContinuousLinearMap.snd ℝ (ℝ × ℝ) (ℝ × ℝ)))
  set a : (ℝ × ℝ) × (ℝ × ℝ) := ((0, 0), (0, ℓ))
  have hPx : P x₀ + a = x₀ := by simp [P, a, x₀]
  have hPδ : P δ = δ := by
    ext <;> simp [P, hδ]
  have hg : ContDiffAt ℝ 2 g x₀ :=
    l.contDiff.contDiffAt.comp _ (contDiffAt_polarEnergyMomentum hm hr₀ hU)
  have hga : ContDiffAt ℝ 2 (fun y ↦ g (y + a)) (P x₀) := by
    refine ContDiffAt.comp (g := g) (P x₀) ?_ (contDiffAt_id.add contDiffAt_const)
    simpa [hPx] using hg
  -- Translating the base point does not change the Hessian.
  have htr : hessianQuadraticForm g x₀ = hessianQuadraticForm (fun y ↦ g (y + a)) (P x₀) := by
    ext v
    rw [hessianQuadraticForm_apply, hessianQuadraticForm_apply, fderiv_fderiv_comp_add_right, hPx]
  -- On the hyperplane `L = ℓ`, `g` is a function of `(r, p_r)` alone.
  have hgP : (fun y ↦ g (y + a)) ∘ P = fun y ↦ l (Pi.single 0 1) *
      (effectivePotential m ℓ U y.1.1 + y.1.2 ^ 2 / (2 * m)) + ℓ * l (Pi.single 1 1) := by
    funext y
    have hv (v : Fin 2 → ℝ) : v = v 0 • Pi.single 0 1 + v 1 • Pi.single 1 1 := by
      ext i
      fin_cases i <;> simp
    simp only [Function.comp_apply, g]
    rw [hv (polarEnergyMomentum m U _), map_add, map_smul, map_smul]
    simp [polarEnergyMomentum, P, a, mul_comm, add_comm, add_left_comm]
  have hcomp := congrArg (· δ) (ContinuousLinearMap.hessianQuadraticForm_comp P hga)
  simp only [QuadraticMap.comp_apply, ContinuousLinearMap.coe_coe, hPδ] at hcomp
  rw [htr, ← hcomp, hgP, hessianQuadraticForm_radial hm hr₀ hU]


private theorem mem_ker_polarDiff {κ : ℝ} {δ : (ℝ × ℝ) × (ℝ × ℝ)} :
    δ ∈ (polarDiff κ).ker ↔ δ.2.2 = 0 := by
  rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, polarDiff_apply]
  constructor
  · intro h
    simpa using congrFun h 1
  · intro h
    ext i
    fin_cases i <;> simp [h]

/-- The vectors of `ker dF` that are also in its symplectic complement are the multiples of
`∂_θ`. -/
private theorem eq_of_mem_ker_inf_orthogonal {κ : ℝ} {w : (ℝ × ℝ) × (ℝ × ℝ)}
    (hw : w ∈ (polarDiff κ).ker ⊓ polarForm.orthogonal (polarDiff κ).ker) :
    w.1 = 0 ∧ w.2.2 = 0 := by
  obtain ⟨hwk, hwo⟩ := Submodule.mem_inf.1 hw
  rw [mem_ker_polarDiff] at hwk
  have h₁ := (SymplecticForm.mem_orthogonal_iff'.1 hwo) ((1, 0), (0, 0)) (by simp)
  have h₂ := (SymplecticForm.mem_orthogonal_iff'.1 hwo) ((0, 1), (0, 0)) (by simp)
  simp only [SymplecticForm.prod_apply, stdSymplecticForm_apply, RCLike.inner_apply,
    conj_trivial, zero_mul, one_mul, zero_sub, sub_self, add_zero, neg_eq_zero, sub_zero] at h₁ h₂
  exact ⟨Prod.ext h₂ h₁, hwk⟩

/-- The transversal space of the polar energy–momentum map at a circular orbit is a plane. -/
private theorem finrank_reducedSpace_ker_polarDiff (κ : ℝ) :
    finrank ℝ (polarForm.ReducedSpace (polarDiff κ).ker) = 2 := by
  have hcoiso : polarForm.IsCoisotropic (polarDiff κ).ker := by
    refine SymplecticForm.isCoisotropic_iff_le.2 fun w hw ↦ ?_
    rw [mem_ker_polarDiff]
    simpa using (SymplecticForm.mem_orthogonal_iff'.1 hw) ((0, 0), (1, 0)) (by simp)
  have hker : (polarDiff κ).ker = LinearMap.ker (polarL : (ℝ × ℝ) × (ℝ × ℝ) →ₗ[ℝ] ℝ) := by
    ext δ
    rw [mem_ker_polarDiff, LinearMap.mem_ker, ContinuousLinearMap.coe_coe, polarL_apply]
  have hrange : LinearMap.range (polarL : (ℝ × ℝ) × (ℝ × ℝ) →ₗ[ℝ] ℝ) = ⊤ :=
    LinearMap.range_eq_top.2 fun t ↦ ⟨((0, 0), (0, t)), by simp⟩
  have h₁ := LinearMap.finrank_range_add_finrank_ker (polarL : (ℝ × ℝ) × (ℝ × ℝ) →ₗ[ℝ] ℝ)
  rw [hrange, finrank_top] at h₁
  have h₂ := hcoiso.finrank_reducedSpace_add_finrank
  rw [hker] at h₂
  simp only [finrank_prod, finrank_self] at h₁ h₂
  rw [hker]
  omega

/-- On the transversal plane of a circular orbit, a quadratic form with
`Q [δ] = c δr² + δp_r² / m` is nondegenerate exactly when `c ≠ 0`. -/
private theorem nondegenerate_iff_of_reducedSpace (hm : m ≠ 0) {κ c : ℝ}
    {Q : QuadraticForm ℝ (polarForm.ReducedSpace (polarDiff κ).ker)}
    (hQ : ∀ u : (polarDiff κ).ker, Q (Submodule.Quotient.mk u) =
      c * (u : (ℝ × ℝ) × (ℝ × ℝ)).1.1 ^ 2 + (u : (ℝ × ℝ) × (ℝ × ℝ)).1.2 ^ 2 / m) :
    Q.Nondegenerate ↔ c ≠ 0 := by
  -- The polar form of `Q` is `2 (c δr δr' + δp_r δp_r' / m)`.
  have hpolar (u u' : (polarDiff κ).ker) : QuadraticMap.polar Q (Submodule.Quotient.mk u)
      (Submodule.Quotient.mk u') = 2 * (c * (u : (ℝ × ℝ) × (ℝ × ℝ)).1.1 *
        (u' : (ℝ × ℝ) × (ℝ × ℝ)).1.1 +
          (u : (ℝ × ℝ) × (ℝ × ℝ)).1.2 * (u' : (ℝ × ℝ) × (ℝ × ℝ)).1.2 / m) := by
    rw [QuadraticMap.polar, ← Submodule.Quotient.mk_add, hQ, hQ, hQ]
    simp only [Submodule.coe_add, Prod.fst_add, Prod.snd_add]
    ring
  have hr : (((1, 0), (0, 0)) : (ℝ × ℝ) × (ℝ × ℝ)) ∈ (polarDiff κ).ker := by simp
  have hp : (((0, 1), (0, 0)) : (ℝ × ℝ) × (ℝ × ℝ)) ∈ (polarDiff κ).ker := by simp
  rw [QuadraticMap.nondegenerate_iff_radical_eq_bot, QuadraticMap.radical_eq_ker_polarBilin,
    Submodule.eq_bot_iff]
  constructor
  · -- If `c = 0`, the class of `∂_r` is a nonzero vector of the radical.
    intro h hc0
    have hzero := h (Submodule.Quotient.mk ⟨_, hr⟩) <| by
      refine LinearMap.mem_ker.2 (LinearMap.ext fun v ↦ ?_)
      induction v using Submodule.Quotient.induction_on with
      | H u => simp [hpolar, hc0]
    rw [SymplecticForm.ReducedSpace.mk_eq_zero_iff, SymplecticForm.mem_orthogonal_iff'] at hzero
    simpa using hzero _ hp
  · -- If `c ≠ 0`, a vector of the radical has `δr = δp_r = 0`, so it lies in `K^ω`.
    intro hc0 v hv
    induction v using Submodule.Quotient.induction_on with
    | H u =>
    have hv' := LinearMap.mem_ker.1 hv
    have h₁ := congrArg (· (Submodule.Quotient.mk ⟨_, hr⟩)) hv'
    have h₂ := congrArg (· (Submodule.Quotient.mk ⟨_, hp⟩)) hv'
    simp only [QuadraticMap.polarBilin_apply_apply, hpolar, LinearMap.zero_apply] at h₁ h₂
    have hu₁ : (u : (ℝ × ℝ) × (ℝ × ℝ)).1.1 = 0 := by simpa [hc0] using h₁
    have hu₂ : (u : (ℝ × ℝ) × (ℝ × ℝ)).1.2 = 0 := by simpa [hm] using h₂
    have hu₃ : (u : (ℝ × ℝ) × (ℝ × ℝ)).2.2 = 0 := mem_ker_polarDiff.1 u.property
    rw [SymplecticForm.ReducedSpace.mk_eq_zero_iff]
    intro y hy
    have hy₃ : y.2.2 = 0 := mem_ker_polarDiff.1 hy
    simp [hu₁, hu₂, hu₃, hy₃]

/-- The Hessians of the functions `l ∘ (H, L)` at a circular orbit vanish on `(K ∩ K^ω) × K` for
`K = ker d(H, L)`, since `K ∩ K^ω` is the line of `∂_θ`. -/
private theorem polar_hessianQuadraticForm_polarEnergyMomentum_eq_zero (hm : m ≠ 0)
    (hr₀ : r₀ ≠ 0) (hU : ContDiffAt ℝ 2 U r₀) (κ : ℝ) (l : (Fin 2 → ℝ) →L[ℝ] ℝ) :
    ∀ w ∈ (polarDiff κ).ker ⊓ polarForm.orthogonal (polarDiff κ).ker, ∀ u ∈ (polarDiff κ).ker,
      QuadraticMap.polar (hessianQuadraticForm (l ∘ polarEnergyMomentum m U)
        ((r₀, 0), (θ₀, ℓ))) w u = 0 := by
  intro w hw u hu
  obtain ⟨hw₁, -⟩ := eq_of_mem_ker_inf_orthogonal hw
  have hwK := mem_ker_polarDiff.1 (Submodule.mem_inf.1 hw).1
  have huK := mem_ker_polarDiff.1 hu
  rw [QuadraticMap.polar, hessianQuadraticForm_polarEnergyMomentum hm hr₀ hU l (by simp [hwK, huK]),
    hessianQuadraticForm_polarEnergyMomentum hm hr₀ hU l hwK,
    hessianQuadraticForm_polarEnergyMomentum hm hr₀ hU l huK]
  simp [hw₁]

/-- **Circular orbits in polar coordinates.** At a point `((r₀, 0), (θ₀, ℓ))` with `r₀ ≠ 0` a
critical point of the effective potential `U_ℓ`, the polar energy–momentum map has a nondegenerate
point exactly when `U_ℓ''(r₀) ≠ 0`. -/
private theorem isNondegeneratePoint_polarEnergyMomentum_iff (hm : m ≠ 0) (hr₀ : r₀ ≠ 0)
    (hU : ContDiffAt ℝ 2 U r₀) (hc : deriv (effectivePotential m ℓ U) r₀ = 0) :
    polarForm.IsNondegeneratePoint (polarEnergyMomentum m U) ((r₀, 0), (θ₀, ℓ)) ↔
      iteratedDeriv 2 (effectivePotential m ℓ U) r₀ ≠ 0 := by
  set x₀ : (ℝ × ℝ) × (ℝ × ℝ) := ((r₀, 0), (θ₀, ℓ))
  set κ := ℓ / (m * r₀ ^ 2)
  set K := (polarDiff κ).ker
  have hdesc :=
    polar_hessianQuadraticForm_polarEnergyMomentum_eq_zero (θ₀ := θ₀) (ℓ := ℓ) hm hr₀ hU κ
  have hUd := hU.differentiableAt two_ne_zero
  rw [SymplecticForm.isNondegeneratePoint_iff_of_fderiv_eq
    (hasFDerivAt_polarEnergyMomentum (θ₀ := θ₀) hr₀ hUd.hasDerivAt
      ((deriv_effectivePotential_eq_zero_iff hUd hr₀).1 hc)).fderiv,
    and_iff_right (contDiffAt_polarEnergyMomentum (y := x₀) hm hr₀ hU)]
  -- All transversal Hessians are multiples of the one of `H - κ L`.
  set l₀ : (Fin 2 → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj 0 - κ • ContinuousLinearMap.proj 1
  have hl₀ : l₀.comp (polarDiff κ) = 0 := by
    refine ContinuousLinearMap.ext fun δ ↦ ?_
    simp [l₀]
  set Q := polarForm.reducedQuadraticForm K
    (hessianQuadraticForm (l₀ ∘ polarEnergyMomentum m U) x₀) (hdesc l₀)
  have hQmk (u : K) : Q (Submodule.Quotient.mk u) =
      iteratedDeriv 2 (effectivePotential m ℓ U) r₀ * (u : (ℝ × ℝ) × (ℝ × ℝ)).1.1 ^ 2 +
        (u : (ℝ × ℝ) × (ℝ × ℝ)).1.2 ^ 2 / m := by
    rw [SymplecticForm.reducedQuadraticForm_mk,
      hessianQuadraticForm_polarEnergyMomentum hm hr₀ hU l₀ (mem_ker_polarDiff.1 u.property)]
    simp [l₀]
  have hmem (l : {l : (Fin 2 → ℝ) →L[ℝ] ℝ // l.comp (polarDiff κ) = 0}) :
      polarForm.reducedQuadraticForm K
        (hessianQuadraticForm (l.val ∘ polarEnergyMomentum m U) x₀) (hdesc l.val) =
        l.val (Pi.single 0 1) • Q := by
    ext v
    induction v using Submodule.Quotient.induction_on with
    | H u => rw [smul_apply, hQmk, SymplecticForm.reducedQuadraticForm_mk,
        hessianQuadraticForm_polarEnergyMomentum hm hr₀ hU _ (mem_ker_polarDiff.1 u.property),
        smul_eq_mul]
  have hspan : Submodule.span ℝ (Set.range fun l : {l : (Fin 2 → ℝ) →L[ℝ] ℝ //
        l.comp (polarDiff κ) = 0} ↦ polarForm.reducedQuadraticForm K
          (hessianQuadraticForm (l.val ∘ polarEnergyMomentum m U) x₀) (hdesc l.val)) =
      Submodule.span ℝ (Set.range fun _ : Unit ↦ Q) := by
    refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)
    · rintro _ ⟨l, rfl⟩
      dsimp only
      rw [hmem]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨(), rfl⟩)
    · rintro _ ⟨-, rfl⟩
      exact Submodule.subset_span ⟨⟨l₀, hl₀⟩, rfl⟩
  have hfam : (polarForm.reduction K).IsNondegenerateQuadraticFamily _ ↔
      (polarForm.reduction K).IsNondegenerateQuadraticFamily fun _ : Unit ↦ Q :=
    SymplecticForm.isNondegenerateQuadraticFamily_iff_of_span_eq hspan
  rw [SymplecticForm.isNondegenerateQuadraticFamily_const_iff
    (finrank_reducedSpace_ker_polarDiff κ), nondegenerate_iff_of_reducedSpace hm hQmk] at hfam
  exact ⟨fun h ↦ hfam.1 h.isNondegenerateQuadraticFamily,
    fun h ↦ ⟨fun l _ ↦ hdesc l, hfam.2 h⟩⟩

end Polar

/-! ### Circular orbits in the phase space of the plane -/

section Plane

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  (b : OrthonormalBasis (Fin 2) ℝ V) {m : ℝ} {U : ℝ → ℝ} {x : V × V}

/-- Near a point of a circular orbit, polar canonical coordinates `((r, p_r), (θ, L))` identify
the energy–momentum map `(H, L)` with `(p_r² / (2m) + U_L(r), L)` through a map whose differential
`e` at the point is a linear symplectomorphism; the differential of the radial projection sends
`e δ` to the radial part `δ.1 = (δr, δp_r)`. -/
private theorem exists_polarCanonical (hq : x.1 ≠ 0) (h0 : ⟪x.1, x.2⟫_ℝ = 0) :
    ∃ θ : ℝ, ∃ e : ((ℝ × ℝ) × (ℝ × ℝ)) ≃ₗ[ℝ] V × V,
      polarCanonical (b 0) (b 1) ((‖x.1‖, 0), (θ, angularMomentum (b 0) (b 1) x)) = x ∧
      SymplecticForm.IsSymplectomorphism polarForm stdSymplecticForm e ∧
      (∀ v, fderiv ℝ (polarCanonical (b 0) (b 1))
        ((‖x.1‖, 0), (θ, angularMomentum (b 0) (b 1) x)) v = e v) ∧
      centralForceEnergyMomentum b m U ∘ polarCanonical (b 0) (b 1) =ᶠ[𝓝
        ((‖x.1‖, 0), (θ, angularMomentum (b 0) (b 1) x))] polarEnergyMomentum m U ∧
      ∀ δ, fderiv ℝ radialProjection x (e δ) = δ.1 := by
  have hu : ‖b 0‖ = 1 := b.orthonormal.norm_eq_one 0
  have hw : ‖b 1‖ = 1 := b.orthonormal.norm_eq_one 1
  have huw : ⟪b 0, b 1⟫_ℝ = 0 := b.orthonormal.2 (by decide)
  set θ := (polarAngle (b 0) (b 1) x.1).toReal
  set y₀ : (ℝ × ℝ) × (ℝ × ℝ) := ((‖x.1‖, 0), (θ, angularMomentum (b 0) (b 1) x))
  have hr₀ : 0 < y₀.1.1 := norm_pos_iff.2 hq
  have hx : polarCanonical (b 0) (b 1) y₀ = x := by
    have h := polarCanonical_polarAngle b x.2 hq (Real.Angle.coe_toReal _)
    rwa [radialMomentum_apply, h0, zero_div] at h
  -- The differential of the parametrization is a linear symplectomorphism.
  set D := fderiv ℝ (polarCanonical (b 0) (b 1)) y₀
  have hD (δ δ' : (ℝ × ℝ) × (ℝ × ℝ)) : stdSymplecticForm (D δ) (D δ') = polarForm δ δ' :=
    stdSymplecticForm_fderiv_polarCanonical hu hw huw hr₀.ne' δ δ'
  set e := LinearEquiv.ofBijective (D : (ℝ × ℝ) × (ℝ × ℝ) →ₗ[ℝ] V × V)
    (bijective_fderiv_polarCanonical b hr₀.ne')
  have hpos : ∀ᶠ y in 𝓝 y₀, 0 < y.1.1 :=
    (continuous_fst.comp continuous_fst).continuousAt.eventually (lt_mem_nhds hr₀)
  refine ⟨θ, e, hx, SymplecticForm.isSymplectomorphism_iff.2 hD,
    fun δ ↦ (LinearEquiv.ofBijective_apply _ δ).symm, ?_, fun δ ↦ ?_⟩
  · -- Off `r = 0`, the energy and angular momentum read `p_r² / (2m) + U_L(r)` and `L`.
    filter_upwards [hpos] with y hy
    ext i
    fin_cases i
    · simp [polarEnergyMomentum, centralForceHamiltonian_polarCanonical hu hw huw m U hy]
    · simp [polarEnergyMomentum, angularMomentum_polarCanonical hu hw huw hy.ne']
  · -- Off `r = 0`, the radial projection reads `(r, p_r)`, so its differential reads `δ.1`.
    have hrad : radialProjection ∘ polarCanonical (b 0) (b 1) =ᶠ[𝓝 y₀] Prod.fst := by
      filter_upwards [hpos] with y hy
      refine Prod.ext ?_ ?_
      · simp [norm_fst_polarCanonical hu hw huw, abs_of_pos hy]
      · simp [radialMomentum_polarCanonical hu hw huw hy]
    have h := fderiv_comp y₀ (hx ▸ (hasFDerivAt_radialProjection hq).differentiableAt)
      ((contDiffAt_polarCanonical (n := 1) _ _ hr₀.ne').differentiableAt one_ne_zero)
    rw [hrad.fderiv_eq, hx, fderiv_fst] at h
    rw [LinearEquiv.ofBijective_apply, ContinuousLinearMap.coe_coe,
      ← ContinuousLinearMap.comp_apply, ← h, ContinuousLinearMap.coe_fst']

/-- At a point of a circular orbit, the differential of the energy–momentum map, read in polar
canonical coordinates, is `δ ↦ (κ δL, δL)` for the angular velocity `κ = L / (m ‖q‖²)`. -/
private theorem fderiv_apply_eq_polarDiff (hq : x.1 ≠ 0)
    (hU : DifferentiableAt ℝ U ‖x.1‖)
    (hc : deriv (effectivePotential m (angularMomentum (b 0) (b 1) x) U) ‖x.1‖ = 0) {θ : ℝ}
    {e : ((ℝ × ℝ) × (ℝ × ℝ)) ≃ₗ[ℝ] V × V}
    (hx : polarCanonical (b 0) (b 1) ((‖x.1‖, 0), (θ, angularMomentum (b 0) (b 1) x)) = x)
    (hφe : ∀ v, fderiv ℝ (polarCanonical (b 0) (b 1))
      ((‖x.1‖, 0), (θ, angularMomentum (b 0) (b 1) x)) v = e v)
    (hev : centralForceEnergyMomentum b m U ∘ polarCanonical (b 0) (b 1) =ᶠ[𝓝
        ((‖x.1‖, 0), (θ, angularMomentum (b 0) (b 1) x))] polarEnergyMomentum m U)
    (δ : (ℝ × ℝ) × (ℝ × ℝ)) :
    fderiv ℝ (centralForceEnergyMomentum b m U) x (e δ) =
      polarDiff (angularMomentum (b 0) (b 1) x / (m * ‖x.1‖ ^ 2)) δ := by
  set ℓ := angularMomentum (b 0) (b 1) x
  set y₀ : (ℝ × ℝ) × (ℝ × ℝ) := ((‖x.1‖, 0), (θ, ℓ))
  have hr₀ : ‖x.1‖ ≠ 0 := norm_ne_zero_iff.2 hq
  have hUd := hU.hasDerivAt
  have hcirc := (deriv_effectivePotential_eq_zero_iff hU hr₀).1 hc
  have hF : DifferentiableAt ℝ (centralForceEnergyMomentum b m U) (polarCanonical (b 0) (b 1) y₀) :=
    hx ▸ (hasFDerivAt_centralForceEnergyMomentum b hUd hq).differentiableAt
  have hφ : DifferentiableAt ℝ (polarCanonical (b 0) (b 1)) y₀ :=
    (contDiffAt_polarCanonical (n := 1) _ _ hr₀).differentiableAt one_ne_zero
  have h := fderiv_comp y₀ hF hφ
  rw [hev.fderiv_eq, (hasFDerivAt_polarEnergyMomentum hr₀ hUd hcirc).fderiv, hx] at h
  rw [← hφe, ← ContinuousLinearMap.comp_apply, ← h]

/-- If a linear map `f` reads `δ ↦ (κ δL, δL)` through `e`, then `e δ` lies in its kernel exactly
when `δL = 0`. -/
private theorem apply_mem_ker_iff_of_apply_eq_polarDiff {f : V × V →L[ℝ] Fin 2 → ℝ} {κ : ℝ}
    {e : ((ℝ × ℝ) × (ℝ × ℝ)) ≃ₗ[ℝ] V × V} (hd : ∀ δ, f (e δ) = polarDiff κ δ)
    {δ : (ℝ × ℝ) × (ℝ × ℝ)} :
    e δ ∈ (f : V × V →ₗ[ℝ] Fin 2 → ℝ).ker ↔ δ.2.2 = 0 := by
  rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, hd, ← mem_ker_polarDiff (κ := κ),
    LinearMap.mem_ker, ContinuousLinearMap.coe_coe]

/-- **Circular orbits have rank one.** At a point `(q, p)` with `q ≠ 0` on a circular orbit, where
`⟪q, p⟫ = 0` and `‖q‖` is a critical point of the effective potential `U_L` of its angular
momentum `L`, the differential of the energy–momentum map `(H, L)` has rank one. This includes the
rest points `p = 0` at critical points of `U`. -/
theorem finrank_range_fderiv_centralForceEnergyMomentum (hq : x.1 ≠ 0)
    (hU : DifferentiableAt ℝ U ‖x.1‖) (h0 : ⟪x.1, x.2⟫_ℝ = 0)
    (hc : deriv (effectivePotential m (angularMomentum (b 0) (b 1) x) U) ‖x.1‖ = 0) :
    finrank ℝ (fderiv ℝ (centralForceEnergyMomentum b m U) x).range = 1 := by
  obtain ⟨θ, e, hx, -, hφe, hev, -⟩ := exists_polarCanonical b (m := m) (U := U) hq h0
  set ℓ := angularMomentum (b 0) (b 1) x
  -- The differential of `(H, L)` at `x`, read through the bijection `e`, is `δ ↦ (κ δL, δL)`.
  have hcomp : (fderiv ℝ (centralForceEnergyMomentum b m U) x : V × V →ₗ[ℝ] Fin 2 → ℝ).comp
      (e : (ℝ × ℝ) × (ℝ × ℝ) →ₗ[ℝ] V × V) =
        ((polarDiff (ℓ / (m * ‖x.1‖ ^ 2)) : (ℝ × ℝ) × (ℝ × ℝ) →L[ℝ] Fin 2 → ℝ) :
          (ℝ × ℝ) × (ℝ × ℝ) →ₗ[ℝ] Fin 2 → ℝ) :=
    LinearMap.ext (fderiv_apply_eq_polarDiff b hq hU hc hx hφe hev)
  have hrange := LinearMap.range_comp_of_range_eq_top
    (fderiv ℝ (centralForceEnergyMomentum b m U) x : V × V →ₗ[ℝ] Fin 2 → ℝ)
    (LinearEquiv.range e)
  rw [hcomp] at hrange
  rw [← hrange]
  -- The image of `δ ↦ (κ δL, δL)` is the line spanned by `(κ, 1)`.
  have hspan : LinearMap.range ((polarDiff (ℓ / (m * ‖x.1‖ ^ 2)) :
        (ℝ × ℝ) × (ℝ × ℝ) →L[ℝ] Fin 2 → ℝ) : (ℝ × ℝ) × (ℝ × ℝ) →ₗ[ℝ] Fin 2 → ℝ) =
      ℝ ∙ ![ℓ / (m * ‖x.1‖ ^ 2), 1] := by
    ext w
    rw [LinearMap.mem_range, Submodule.mem_span_singleton]
    constructor
    · rintro ⟨δ, rfl⟩
      refine ⟨δ.2.2, funext fun i ↦ ?_⟩
      fin_cases i <;> simp [mul_comm]
    · rintro ⟨a, rfl⟩
      refine ⟨((0, 0), (0, a)), funext fun i ↦ ?_⟩
      fin_cases i <;> simp [mul_comm]
  rw [hspan, finrank_span_singleton]
  intro h
  simpa using congrFun h 1

/-- **Circular orbits are nondegenerate exactly when the effective potential is.** Let
`(q, p)`, `q ≠ 0`, lie on a circular orbit of the planar central force with mass `m ≠ 0` and
potential `U`, twice continuously differentiable at `‖q‖`: the radial momentum vanishes,
`⟪q, p⟫ = 0`, and `‖q‖` is a critical point of the effective potential `U_L` of the angular
momentum `L` of `(q, p)`. Then `(q, p)` is a nondegenerate point of rank one of the
energy–momentum map `(H, L)` exactly when `U_L''(‖q‖) ≠ 0`.

The transversal space at `(q, p)` is the plane of the radial pair `(r, p_r)`, on which the
transversal Hessian of `H - κ L`, with `κ = L / (m ‖q‖²)` the angular velocity, is
`U_L''(‖q‖) δr² + δp_r² / m`. -/
theorem isNondegeneratePoint_centralForceEnergyMomentum_iff [FiniteDimensional ℝ V] (hm : m ≠ 0)
    (hq : x.1 ≠ 0) (hU : ContDiffAt ℝ 2 U ‖x.1‖) (h0 : ⟪x.1, x.2⟫_ℝ = 0)
    (hc : deriv (effectivePotential m (angularMomentum (b 0) (b 1) x) U) ‖x.1‖ = 0) :
    stdSymplecticForm.IsNondegeneratePoint (centralForceEnergyMomentum b m U) x ↔
      iteratedDeriv 2 (effectivePotential m (angularMomentum (b 0) (b 1) x) U) ‖x.1‖ ≠ 0 := by
  obtain ⟨θ, e, hx, he, hφe, hev, -⟩ := exists_polarCanonical b (m := m) (U := U) hq h0
  have hφ : ContDiffAt ℝ 2 (polarCanonical (b 0) (b 1))
      ((‖x.1‖, 0), (θ, angularMomentum (b 0) (b 1) x)) :=
    contDiffAt_polarCanonical _ _ (norm_ne_zero_iff.2 hq)
  rw [← isNondegeneratePoint_polarEnergyMomentum_iff (θ₀ := θ) hm (norm_ne_zero_iff.2 hq) hU hc]
  conv_lhs => rw [← hx]
  rw [← SymplecticForm.isNondegeneratePoint_comp_right_iff_of_isSymplectomorphism he hφ hφe]
  exact ⟨fun h ↦ h.congr_of_eventuallyEq hev, fun h ↦ h.congr_of_eventuallyEq hev.symm⟩

/-- At a point of a circular orbit, `H - κ L` is critical for the angular velocity
`κ = L / (m ‖q‖²)`: the functional `(a, c) ↦ a - κ c` kills the image of `d(H, L)`. -/
private theorem comp_fderiv_centralForceEnergyMomentum_eq_zero (hq : x.1 ≠ 0)
    (hU : DifferentiableAt ℝ U ‖x.1‖) (h0 : ⟪x.1, x.2⟫_ℝ = 0)
    (hc : deriv (effectivePotential m (angularMomentum (b 0) (b 1) x) U) ‖x.1‖ = 0) :
    (ContinuousLinearMap.proj 0 - (angularMomentum (b 0) (b 1) x / (m * ‖x.1‖ ^ 2)) •
        ContinuousLinearMap.proj 1 : (Fin 2 → ℝ) →L[ℝ] ℝ).comp
      (fderiv ℝ (centralForceEnergyMomentum b m U) x) = 0 := by
  obtain ⟨θ, e, hx, -, hφe, hev, -⟩ := exists_polarCanonical b (m := m) (U := U) hq h0
  refine ContinuousLinearMap.ext fun w ↦ ?_
  obtain ⟨δ, rfl⟩ := e.surjective w
  simp [fderiv_apply_eq_polarDiff b hq hU hc hx hφe hev]

/-- **The transversal Hessian of a circular orbit.** Let `(q, p)`, `q ≠ 0`, lie on a circular
orbit of the planar central force with mass `m ≠ 0` and potential `U`, twice continuously
differentiable at `‖q‖`, and let `κ = L / (m ‖q‖²)` be its angular velocity, so that
`d(H - κ L) = 0` at `(q, p)`. On a vector `v` of `ker d(H, L)`, the Hessian of `H - κ L` is

`U_L''(‖q‖) δr² + δp_r² / m`,

where `(δr, δp_r)` is the image of `v` under the differential of the radial projection
`(q, p) ↦ (‖q‖, p_r)`. -/
theorem hessianQuadraticForm_centralForceHamiltonian_sub_mul_angularMomentum (hm : m ≠ 0)
    (hq : x.1 ≠ 0) (hU : ContDiffAt ℝ 2 U ‖x.1‖) (h0 : ⟪x.1, x.2⟫_ℝ = 0)
    (hc : deriv (effectivePotential m (angularMomentum (b 0) (b 1) x) U) ‖x.1‖ = 0) {v : V × V}
    (hv : fderiv ℝ (centralForceEnergyMomentum b m U) x v = 0) :
    hessianQuadraticForm (fun y ↦ centralForceHamiltonian m U y -
        angularMomentum (b 0) (b 1) x / (m * ‖x.1‖ ^ 2) * angularMomentum (b 0) (b 1) y) x v =
      iteratedDeriv 2 (effectivePotential m (angularMomentum (b 0) (b 1) x) U) ‖x.1‖ *
          (fderiv ℝ radialProjection x v).1 ^ 2 + (fderiv ℝ radialProjection x v).2 ^ 2 / m := by
  obtain ⟨θ, e, hx, -, hφe, hev, hdrad⟩ := exists_polarCanonical b (m := m) (U := U) hq h0
  set ℓ := angularMomentum (b 0) (b 1) x
  set κ := ℓ / (m * ‖x.1‖ ^ 2)
  set y₀ : (ℝ × ℝ) × (ℝ × ℝ) := ((‖x.1‖, 0), (θ, ℓ))
  have hr₀ : ‖x.1‖ ≠ 0 := norm_ne_zero_iff.2 hq
  have hd := fderiv_apply_eq_polarDiff b hq (hU.differentiableAt two_ne_zero) hc hx hφe hev
  have hφ : ContDiffAt ℝ 2 (polarCanonical (b 0) (b 1)) y₀ := contDiffAt_polarCanonical _ _ hr₀
  -- `H - κ L` is `l₀ ∘ (H, L)` for the functional `l₀` killing the image of `d(H, L)`.
  set l₀ : (Fin 2 → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj 0 - κ • ContinuousLinearMap.proj 1
  have hf : (fun y ↦ centralForceHamiltonian m U y - κ * angularMomentum (b 0) (b 1) y) =
      l₀ ∘ centralForceEnergyMomentum b m U := by
    funext y
    simp [l₀]
  have hFC : ContDiffAt ℝ 2 (centralForceEnergyMomentum b m U) x :=
    contDiffAt_centralForceEnergyMomentum b hU hq
  have hcrit : fderiv ℝ (l₀ ∘ centralForceEnergyMomentum b m U) x = 0 := by
    rw [fderiv_comp x l₀.differentiableAt (hFC.differentiableAt two_ne_zero), l₀.fderiv]
    exact comp_fderiv_centralForceEnergyMomentum_eq_zero b hq (hU.differentiableAt two_ne_zero)
      h0 hc
  obtain ⟨δ, rfl⟩ := e.surjective v
  have hδ : δ.2.2 = 0 := (apply_mem_ker_iff_of_apply_eq_polarDiff hd).1 hv
  -- Pull the Hessian back to polar canonical coordinates, where it was computed.
  have hcomp := hessianQuadraticForm_comp (f := l₀ ∘ centralForceEnergyMomentum b m U)
    (hx ▸ l₀.contDiff.contDiffAt.comp x hFC) hφ (hx ▸ hcrit)
  rw [hx] at hcomp
  have hpull := congrArg (· δ) hcomp
  simp only [QuadraticMap.comp_apply, ContinuousLinearMap.coe_coe, hφe] at hpull
  rw [hf, ← hpull, Function.comp_assoc,
    hessianQuadraticForm_congr_of_eventuallyEq (hev.fun_comp l₀),
    hessianQuadraticForm_polarEnergyMomentum hm hr₀ hU l₀ hδ, hdrad δ]
  simp [l₀]

/-- At a circular orbit, a vector of `ker d(H, L)` whose radial components `(δr, δp_r)` vanish
lies in the symplectic complement of `ker d(H, L)`. -/
private theorem mem_orthogonal_ker_of_fderiv_radialProjection_eq_zero (hq : x.1 ≠ 0)
    (hU : DifferentiableAt ℝ U ‖x.1‖) (h0 : ⟪x.1, x.2⟫_ℝ = 0)
    (hc : deriv (effectivePotential m (angularMomentum (b 0) (b 1) x) U) ‖x.1‖ = 0) {v : V × V}
    (hv : fderiv ℝ (centralForceEnergyMomentum b m U) x v = 0)
    (hr : fderiv ℝ radialProjection x v = 0) :
    v ∈ stdSymplecticForm.orthogonal (fderiv ℝ (centralForceEnergyMomentum b m U) x).ker := by
  obtain ⟨θ, e, hx, he, hφe, hev, hdrad⟩ := exists_polarCanonical b (m := m) (U := U) hq h0
  have hd := fderiv_apply_eq_polarDiff b hq hU hc hx hφe hev
  obtain ⟨δ, rfl⟩ := e.surjective v
  have hδ : δ.2.2 = 0 := (apply_mem_ker_iff_of_apply_eq_polarDiff hd).1 hv
  have hδ₁ : δ.1 = 0 := (hdrad δ).symm.trans hr
  rw [SymplecticForm.mem_orthogonal_iff]
  intro w hw
  obtain ⟨δ', rfl⟩ := e.surjective w
  have hδ' : δ'.2.2 = 0 := (apply_mem_ker_iff_of_apply_eq_polarDiff hd).1 hw
  rw [he.apply]
  simp [hδ, hδ₁, hδ']

/-- **Stable circular orbits are elliptic.** At a point of a circular orbit, as in
`TauCeti.isNondegeneratePoint_centralForceEnergyMomentum_iff`, at which `‖q‖` is a nondegenerate
minimum of the effective potential, `U_L''(‖q‖) > 0`, and for a positive mass, the transversal
Hessian of `H - κ L` is positive definite: it is positive on every vector of `ker d(H, L)` outside
the symplectic complement of `ker d(H, L)`. The induced form on the transversal plane is
`TauCeti.posDef_reducedQuadraticForm_centralForceHamiltonian_sub_mul_angularMomentum`. -/
theorem hessianQuadraticForm_centralForceHamiltonian_sub_mul_angularMomentum_pos (hm : 0 < m)
    (hq : x.1 ≠ 0) (hU : ContDiffAt ℝ 2 U ‖x.1‖) (h0 : ⟪x.1, x.2⟫_ℝ = 0)
    (hc : deriv (effectivePotential m (angularMomentum (b 0) (b 1) x) U) ‖x.1‖ = 0)
    (hpos : 0 < iteratedDeriv 2 (effectivePotential m (angularMomentum (b 0) (b 1) x) U) ‖x.1‖)
    {v : V × V} (hv : fderiv ℝ (centralForceEnergyMomentum b m U) x v = 0)
    (hv' : v ∉ stdSymplecticForm.orthogonal (fderiv ℝ (centralForceEnergyMomentum b m U) x).ker) :
    0 < hessianQuadraticForm (fun y ↦ centralForceHamiltonian m U y -
        angularMomentum (b 0) (b 1) x / (m * ‖x.1‖ ^ 2) * angularMomentum (b 0) (b 1) y) x v := by
  rw [hessianQuadraticForm_centralForceHamiltonian_sub_mul_angularMomentum b hm.ne' hq hU h0 hc hv]
  have hne : fderiv ℝ radialProjection x v ≠ 0 := fun hr ↦ hv'
    (mem_orthogonal_ker_of_fderiv_radialProjection_eq_zero b hq
      (hU.differentiableAt two_ne_zero) h0 hc hv hr)
  rcases eq_or_ne (fderiv ℝ radialProjection x v).1 0 with h₁ | h₁
  · have h₂ : (fderiv ℝ radialProjection x v).2 ≠ 0 := fun h₂ ↦ hne (Prod.ext h₁ h₂)
    rw [h₁]
    positivity
  · positivity

/-- **The transversal Hessian of a circular orbit descends to the transversal plane.** At a point
of a circular orbit, as in `TauCeti.isNondegeneratePoint_centralForceEnergyMomentum_iff`, the
polar form of the Hessian of `H - κ L` vanishes on `(K ∩ K^ω) × K` for `K = ker d(H, L)`, so it
induces a quadratic form on the transversal plane `K / (K ∩ K^ω)`. -/
theorem polar_hessianQuadraticForm_centralForceHamiltonian_sub_mul_angularMomentum_eq_zero
    (hq : x.1 ≠ 0) (hU : ContDiffAt ℝ 2 U ‖x.1‖) (h0 : ⟪x.1, x.2⟫_ℝ = 0)
    (hc : deriv (effectivePotential m (angularMomentum (b 0) (b 1) x) U) ‖x.1‖ = 0) :
    ∀ w ∈ (fderiv ℝ (centralForceEnergyMomentum b m U) x).ker ⊓
        stdSymplecticForm.orthogonal (fderiv ℝ (centralForceEnergyMomentum b m U) x).ker,
      ∀ u ∈ (fderiv ℝ (centralForceEnergyMomentum b m U) x).ker,
        QuadraticMap.polar (hessianQuadraticForm (fun y ↦ centralForceHamiltonian m U y -
          angularMomentum (b 0) (b 1) x / (m * ‖x.1‖ ^ 2) * angularMomentum (b 0) (b 1) y) x)
          w u = 0 := by
  intro w hw u _
  have : FiniteDimensional ℝ V := b.toBasis.finiteDimensional_of_finite
  set κ := angularMomentum (b 0) (b 1) x / (m * ‖x.1‖ ^ 2)
  set l₀ : (Fin 2 → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj 0 - κ • ContinuousLinearMap.proj 1
  have hf : (fun y ↦ centralForceHamiltonian m U y - κ * angularMomentum (b 0) (b 1) y) =
      l₀ ∘ centralForceEnergyMomentum b m U := by
    funext y
    simp [l₀]
  have hFC : ContDiffAt ℝ 2 (centralForceEnergyMomentum b m U) x :=
    contDiffAt_centralForceEnergyMomentum b hU hq
  rw [hf]
  refine stdSymplecticForm.polar_hessianQuadraticForm_eq_zero_of_mem_orthogonal hFC
    (comp_fderiv_centralForceEnergyMomentum_eq_zero b hq (hU.differentiableAt two_ne_zero) h0 hc)
    (fun ℓ' ↦ ?_) hw.2 u
  -- The components `H` and `L` Poisson-commute everywhere, so all `ℓ ∘ (H, L)` do near `x`.
  refine stdSymplecticForm.poissonBracket_comp_eventuallyEq_zero
    (hFC.eventually (by simp) |>.mono fun _ hy ↦ hy.differentiableAt two_ne_zero)
    (fun i j ↦ Filter.Eventually.of_forall fun y ↦ ?_) ℓ' l₀
  fin_cases i <;> fin_cases j <;>
    simp [stdSymplecticForm_poissonBracket_centralForceHamiltonian_angularMomentum,
      stdSymplecticForm_poissonBracket_angularMomentum_centralForceHamiltonian]

/-- **Stable circular orbits are elliptic, on the transversal plane.** At a point of a circular
orbit, as in `TauCeti.isNondegeneratePoint_centralForceEnergyMomentum_iff`, at which `‖q‖` is a
nondegenerate minimum of the effective potential, `U_L''(‖q‖) > 0`, and for a positive mass, the
transversal reduction of the Hessian of `H - κ L` to `K / (K ∩ K^ω)`, `K = ker d(H, L)`, is
positive definite. The transversal plane is a symplectic plane, and a definite quadratic form on a
symplectic plane is an elliptic block. -/
theorem posDef_reducedQuadraticForm_centralForceHamiltonian_sub_mul_angularMomentum (hm : 0 < m)
    (hq : x.1 ≠ 0) (hU : ContDiffAt ℝ 2 U ‖x.1‖) (h0 : ⟪x.1, x.2⟫_ℝ = 0)
    (hc : deriv (effectivePotential m (angularMomentum (b 0) (b 1) x) U) ‖x.1‖ = 0)
    (hpos : 0 < iteratedDeriv 2 (effectivePotential m (angularMomentum (b 0) (b 1) x) U) ‖x.1‖) :
    (stdSymplecticForm.reducedQuadraticForm (fderiv ℝ (centralForceEnergyMomentum b m U) x).ker
      (hessianQuadraticForm (fun y ↦ centralForceHamiltonian m U y -
        angularMomentum (b 0) (b 1) x / (m * ‖x.1‖ ^ 2) * angularMomentum (b 0) (b 1) y) x)
      (polar_hessianQuadraticForm_centralForceHamiltonian_sub_mul_angularMomentum_eq_zero b
        hq hU h0 hc)).PosDef := by
  intro v hv
  induction v using Submodule.Quotient.induction_on with
  | H u =>
  rw [SymplecticForm.reducedQuadraticForm_mk]
  exact hessianQuadraticForm_centralForceHamiltonian_sub_mul_angularMomentum_pos b hm hq hU h0 hc
    hpos (LinearMap.mem_ker.1 u.property)
    fun hu ↦ hv (SymplecticForm.ReducedSpace.mk_eq_zero_iff.2 hu)

end Plane

end TauCeti
