/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.CentralForce.Polar
public import TauCeti.Geometry.Symplectic.Hamiltonian.SingularPoint
import TauCeti.Analysis.Calculus.FDeriv.Prod
import TauCeti.Analysis.Calculus.Morse.OneDimensional
import TauCeti.Analysis.Calculus.Morse.Prod

/-!
# Circular orbits of planar central forces as nondegenerate points of rank one

Let `F = (H, L)` be the energy–momentum map of a planar central force
(`TauCeti.centralForceEnergyMomentum`), with `H = ‖p‖² / (2m) + U(‖q‖)` and `L` the angular
momentum. Off the collision set, its critical points are the points of the circular orbits and
the rest points: `⟪q, p⟫ = 0` and `r = ‖q‖` is a critical point of the effective potential
`U_L(r) = L² / (2 m r²) + U(r)` (`TauCeti.isRegularPoint_centralForceEnergyMomentum_iff`). There
`dH = Ω dL` with the angular velocity `Ω = L / (m r²)`, so `F` has rank one, and the critical
function is `H - Ω L`.

This file computes the transversal data of such a point in the sense of Eliasson and
Bolsinov–Fomenko (`TauCeti.SymplecticForm.IsNondegeneratePoint`). The polar canonical coordinates
`(r, p_r, θ, L)` of `TauCeti.polarCanonical` give a symplectic slice of the transversal space
`ker dF ⧸ (ker dF)^ω`: the directions `(δr, δp_r)`, on which `ω₀` restricts to `dr ∧ dp_r`. In
these coordinates the transversal Hessians are the multiples of

`U_L''(r) δr² + δp_r² / m`

(`TauCeti.hessianQuadraticForm_comp_centralForceEnergyMomentum_apply_fderiv_polarCanonical`), the
Hessian of the reduced Hamiltonian `p_r² / (2m) + U_L(r)` of the radial motion. Hence a point of a
circular orbit is a nondegenerate point of `F` exactly when `r` is a nondegenerate critical point
of the effective potential, `U_L''(r) ≠ 0`
(`TauCeti.isNondegeneratePoint_centralForceEnergyMomentum_iff`). For `m > 0` the transversal
Hessian of the critical function `H - Ω L` on the radial directions is positive definite exactly
when `U_L''(r) > 0`, that is, at a nondegenerate minimum of the effective potential
(`posDef_hessianQuadraticForm_comp_centralForceEnergyMomentum_comp_fderiv_polarCanonical_inl_iff`).
By Williamson's theorem
(`TauCeti.SymplecticForm.exists_isDarbouxBasis_eq_sum_smul_elliptic_of_posDef`), a positive
definite form on the two-dimensional slice is a multiple of one elliptic block; that normal form
is not restated here.

The components of `F` Poisson-commute everywhere
(`TauCeti.stdSymplecticForm_poissonBracket_comp_centralForceEnergyMomentum`), which makes the
transversal Hessians well defined.

## Main results

* `TauCeti.comp_fderiv_centralForceEnergyMomentum_eq_zero`: on a circular orbit, the critical
  functional `h - Ω l` kills the image of `dF`.
* `TauCeti.finrank_range_fderiv_centralForceEnergyMomentum`,
  `TauCeti.finrank_range_fderiv_centralForceEnergyMomentum_polarCanonical`: `F` has rank one at a
  point of a circular orbit.
* `TauCeti.hessianQuadraticForm_comp_centralForceEnergyMomentum_apply_fderiv_polarCanonical`: the
  transversal Hessians in the slice coordinates `(δr, δp_r)`.
* `TauCeti.isNondegeneratePoint_centralForceEnergyMomentum_iff`,
  `TauCeti.isNondegeneratePoint_centralForceEnergyMomentum_polarCanonical_iff`: a point of a
  circular orbit is nondegenerate exactly when `U_L''(r) ≠ 0`.
* `posDef_hessianQuadraticForm_comp_centralForceEnergyMomentum_comp_fderiv_polarCanonical_inl_iff`:
  for `m > 0` the transversal Hessian of `H - Ω L` on the radial directions is positive definite
  exactly when `U_L''(r) > 0`.

## References

* A. V. Bolsinov and A. T. Fomenko, *Integrable Hamiltonian Systems: Geometry, Topology,
  Classification*, Chapman & Hall/CRC, 2004, Chapter 1.
* V. I. Arnold, *Mathematical Methods of Classical Mechanics*, 2nd ed., Graduate Texts in
  Mathematics 60, Springer, 1989, Section 8.
-/

public section

open Filter Module Topology
open scoped InnerProductSpace

namespace TauCeti

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  (b : OrthonormalBasis (Fin 2) ℝ V)

/-! ### The transversal model -/

/-- The reduced radial Hamiltonian `(δr, δp_r) ↦ U_L(r + δr) + δp_r² / (2m)` near `(r, 0)`. -/
private noncomputable def transversalModel (m L : ℝ) (U : ℝ → ℝ) (r : ℝ) : ℝ × ℝ → ℝ :=
  (fun s ↦ effectivePotential m L U (r + s)) ∘ Prod.fst + (fun t ↦ t ^ 2 / (2 * m)) ∘ Prod.snd

variable {m L r : ℝ} {U : ℝ → ℝ}

private theorem contDiffAt_shift_effectivePotential (hU : ContDiffAt ℝ 2 U r) (hr : r ≠ 0) :
    ContDiffAt ℝ 2 (fun s ↦ effectivePotential m L U (r + s)) 0 := by
  refine ContDiffAt.comp (g := effectivePotential m L U) 0 ?_ (by fun_prop)
  simpa using contDiffAt_effectivePotential (m := m) (ℓ := L) hU hr

private theorem deriv_sq_div : deriv (fun t : ℝ ↦ t ^ 2 / (2 * m)) = fun t ↦ t / m := by
  funext t
  rw [((hasDerivAt_pow 2 t).div_const (2 * m)).deriv]
  ring

private theorem iteratedDeriv_two_sq_div : iteratedDeriv 2 (fun t : ℝ ↦ t ^ 2 / (2 * m)) 0 =
    1 / m := by
  rw [iteratedDeriv_succ, iteratedDeriv_one, deriv_sq_div, ((hasDerivAt_id' 0).div_const m).deriv]

private theorem contDiffAt_transversalModel (hU : ContDiffAt ℝ 2 U r) (hr : r ≠ 0) :
    ContDiffAt ℝ 2 (transversalModel m L U r) 0 :=
  ((contDiffAt_shift_effectivePotential hU hr).comp (0 : ℝ × ℝ) contDiffAt_fst).add
    ((by fun_prop : ContDiffAt ℝ 2 (fun t : ℝ ↦ t ^ 2 / (2 * m)) 0).comp (0 : ℝ × ℝ)
      contDiffAt_snd)

private theorem fderiv_transversalModel (hU : ContDiffAt ℝ 2 U r) (hr : r ≠ 0)
    (hc : deriv (effectivePotential m L U) r = 0) :
    fderiv ℝ (transversalModel m L U r) 0 = 0 := by
  rw [transversalModel, ← Prod.mk_zero_zero, fderiv_comp_fst_add_comp_snd_eq_zero_iff
    ((contDiffAt_shift_effectivePotential hU hr).differentiableAt two_ne_zero)
    (by fun_prop), ← toSpanSingleton_deriv, ← toSpanSingleton_deriv, deriv_comp_const_add,
    add_zero, hc, deriv_sq_div]
  simp

/-- The Hessian of the transversal model is `U_L''(r) δr² + δp_r² / m`. -/
private theorem hessianQuadraticForm_transversalModel (hU : ContDiffAt ℝ 2 U r) (hr : r ≠ 0)
    (a : ℝ × ℝ) :
    hessianQuadraticForm (transversalModel m L U r) 0 a =
      iteratedDeriv 2 (effectivePotential m L U) r * a.1 ^ 2 + a.2 ^ 2 / m := by
  rw [transversalModel, ← Prod.mk_zero_zero, hessianQuadraticForm_comp_fst_add_comp_snd
    (contDiffAt_shift_effectivePotential hU hr) (by fun_prop), QuadraticMap.prod_apply,
    hessianQuadraticForm_real_apply, hessianQuadraticForm_real_apply,
    iteratedDeriv_comp_const_add, iteratedDeriv_two_sq_div]
  simp only [add_zero]
  ring

/-- The Hessian of the transversal model is nondegenerate exactly when `U_L''(r) ≠ 0`. -/
private theorem nondegenerate_hessianQuadraticForm_transversalModel_iff (hm : m ≠ 0)
    (hU : ContDiffAt ℝ 2 U r) (hr : r ≠ 0) (hc : deriv (effectivePotential m L U) r = 0) :
    (hessianQuadraticForm (transversalModel m L U r) 0).Nondegenerate ↔
      iteratedDeriv 2 (effectivePotential m L U) r ≠ 0 := by
  -- At a `C²` critical point, nondegeneracy of the Hessian is Morse nondegeneracy, which splits
  -- over the two separated variables.
  have key : (hessianQuadraticForm (transversalModel m L U r) 0).Nondegenerate ↔
      IsNondegenerateCriticalPoint (transversalModel m L U r) 0 := by
    rw [isNondegenerateCriticalPoint_iff_hessianQuadraticForm_nondegenerate]
    exact ⟨fun h ↦ ⟨contDiffAt_transversalModel hU hr,
      fderiv_transversalModel hU hr hc, h⟩, fun h ↦ h.2.2⟩
  rw [key, transversalModel, ← Prod.mk_zero_zero,
    isNondegenerateCriticalPoint_comp_fst_add_comp_snd_iff,
    isNondegenerateCriticalPoint_real_iff (contDiffAt_shift_effectivePotential hU hr),
    isNondegenerateCriticalPoint_real_iff (by fun_prop), deriv_comp_const_add,
    iteratedDeriv_comp_const_add, deriv_sq_div, iteratedDeriv_two_sq_div]
  simp [hc, hm]

/-! ### The slice of radial directions in polar coordinates -/

variable {θ : ℝ}

/-- Near `0`, the energy–momentum map along the radial directions `(δr, δp_r)` of the polar
canonical coordinates at `(r, 0, θ, L)` is `(U_L(r + δr) + δp_r² / (2m), L)`. -/
private theorem eventuallyEq_centralForceEnergyMomentum_polarCanonical (hr : 0 < r) :
    (fun a : ℝ × ℝ ↦ centralForceEnergyMomentum b m U (polarCanonical (b 0) (b 1)
        (((r, 0), (θ, L)) + ContinuousLinearMap.inl ℝ (ℝ × ℝ) (ℝ × ℝ) a))) =ᶠ[𝓝 0]
      fun a ↦ ![transversalModel m L U r a, L] := by
  have hu := b.norm_eq_one 0
  have hw := b.norm_eq_one 1
  have huw : ⟪b 0, b 1⟫_ℝ = 0 := b.inner_eq_zero (by decide)
  have hev : ∀ᶠ a : ℝ × ℝ in 𝓝 0, 0 < r + a.1 :=
    (continuous_const.add continuous_fst).continuousAt.eventually
      (lt_mem_nhds (by simpa using hr))
  filter_upwards [hev] with a ha
  have hpt : ((r, 0), (θ, L)) + ContinuousLinearMap.inl ℝ (ℝ × ℝ) (ℝ × ℝ) a =
      ((r + a.1, a.2), (θ, L)) := by
    ext <;> simp
  rw [hpt]
  ext i
  fin_cases i
  · rw [Fin.zero_eta, centralForceEnergyMomentum_zero,
      centralForceHamiltonian_polarCanonical hu hw huw m U ha]
    simp [transversalModel, add_comm]
  · rw [Fin.mk_one, centralForceEnergyMomentum_one, angularMomentum_polarCanonical hu hw huw ha.ne']
    simp

/-- The position of the point with polar coordinates `(r, 0, θ, L)`, `r > 0`, has length `r`. -/
private theorem norm_fst_polarCanonical_of_pos (hr : 0 < r) :
    ‖(polarCanonical (b 0) (b 1) ((r, 0), (θ, L))).1‖ = r := by
  rw [norm_fst_polarCanonical (b.norm_eq_one 0) (b.norm_eq_one 1) (b.inner_eq_zero (by decide)),
    abs_of_pos hr]

/-- The point with polar coordinates `(r, 0, θ, L)`, `r > 0`, is off the collision set. -/
private theorem fst_polarCanonical_ne_zero_of_pos (hr : 0 < r) :
    (polarCanonical (b 0) (b 1) ((r, 0), (θ, L))).1 ≠ 0 := by
  rw [← norm_ne_zero_iff, norm_fst_polarCanonical_of_pos b hr]
  exact hr.ne'

/-- A potential `C²` at `r > 0` is differentiable at the distance to the origin of the point with
polar coordinates `(r, 0, θ, L)`. -/
private theorem hasDerivAt_norm_fst_polarCanonical_of_pos (hU : ContDiffAt ℝ 2 U r)
    (hr : 0 < r) : HasDerivAt U (deriv U r) ‖(polarCanonical (b 0) (b 1) ((r, 0), (θ, L))).1‖ := by
  rw [norm_fst_polarCanonical_of_pos b hr]
  exact (hU.differentiableAt two_ne_zero).hasDerivAt

/-- For a potential `C²` at `r > 0`, the energy–momentum map is `C²` at the point with polar
coordinates `(r, 0, θ, L)`. -/
private theorem contDiffAt_centralForceEnergyMomentum_polarCanonical (hU : ContDiffAt ℝ 2 U r)
    (hr : 0 < r) : ContDiffAt ℝ 2 (centralForceEnergyMomentum b m U)
      (polarCanonical (b 0) (b 1) ((r, 0), (θ, L))) :=
  contDiffAt_centralForceEnergyMomentum b (by rwa [norm_fst_polarCanonical_of_pos b hr])
    (fst_polarCanonical_ne_zero_of_pos b hr)

/-- The chain rule for the energy–momentum map in polar coordinates at `(r, 0, θ, L)`, `r > 0`. -/
private theorem hasFDerivAt_centralForceEnergyMomentum_comp_polarCanonical
    (hU : ContDiffAt ℝ 2 U r) (hr : 0 < r) :
    HasFDerivAt (centralForceEnergyMomentum b m U ∘ polarCanonical (b 0) (b 1))
      ((fderiv ℝ (centralForceEnergyMomentum b m U)
        (polarCanonical (b 0) (b 1) ((r, 0), (θ, L)))).comp
        (fderiv ℝ (polarCanonical (b 0) (b 1)) ((r, 0), (θ, L)))) ((r, 0), (θ, L)) :=
  (((contDiffAt_centralForceEnergyMomentum_polarCanonical b hU hr).differentiableAt
    two_ne_zero).hasFDerivAt).comp _ ((contDiffAt_polarCanonical (b 0) (b 1) (n := 1)
      hr.ne').differentiableAt one_ne_zero).hasFDerivAt

/-- At the point with polar coordinates `(r, 0, θ, L)`, `r > 0`, the momentum is orthogonal to the
position. -/
private theorem inner_polarCanonical_of_pos (hr : 0 < r) :
    ⟪(polarCanonical (b 0) (b 1) ((r, 0), (θ, L))).1,
      (polarCanonical (b 0) (b 1) ((r, 0), (θ, L))).2⟫_ℝ = 0 := by
  have h := radialMomentum_polarCanonical (b.norm_eq_one 0) (b.norm_eq_one 1)
    (b.inner_eq_zero (by decide)) (x := ((r, 0), (θ, L))) hr
  rw [radialMomentum_def, norm_fst_polarCanonical_of_pos b hr, div_eq_zero_iff] at h
  exact h.resolve_right hr.ne'

/-- The pair `(U_L(r + δr) + δp_r² / (2m), L)` is critical at `0`. -/
private theorem hasFDerivAt_transversalModel_pair (hU : ContDiffAt ℝ 2 U r) (hr : r ≠ 0)
    (hc : deriv (effectivePotential m L U) r = 0) :
    HasFDerivAt (fun a : ℝ × ℝ ↦ ![transversalModel m L U r a, L])
      (0 : ℝ × ℝ →L[ℝ] Fin 2 → ℝ) 0 := by
  refine hasFDerivAt_pi'.2 fun i ↦ ?_
  fin_cases i
  · have h := ((contDiffAt_transversalModel (m := m) (L := L) hU hr).differentiableAt
      two_ne_zero).hasFDerivAt
    simpa [fderiv_transversalModel hU hr hc] using h
  · simpa using hasFDerivAt_const L (0 : ℝ × ℝ)

/-- **The radial directions lie in the kernel.** At a point `(r, 0, θ, L)` of a circular orbit,
the derivative of the energy–momentum map kills the image `(δr, δp_r, 0, 0)` of the radial
directions under the derivative of the polar canonical coordinates. -/
private theorem fderiv_centralForceEnergyMomentum_fderiv_polarCanonical_inl
    (hU : ContDiffAt ℝ 2 U r) (hr : 0 < r) (hc : deriv (effectivePotential m L U) r = 0)
    (a : ℝ × ℝ) :
    fderiv ℝ (centralForceEnergyMomentum b m U) (polarCanonical (b 0) (b 1) ((r, 0), (θ, L)))
      (fderiv ℝ (polarCanonical (b 0) (b 1)) ((r, 0), (θ, L)) (a, 0)) = 0 := by
  set y : (ℝ × ℝ) × (ℝ × ℝ) := ((r, 0), (θ, L))
  have hg : HasFDerivAt (centralForceEnergyMomentum b m U ∘ polarCanonical (b 0) (b 1))
      ((fderiv ℝ (centralForceEnergyMomentum b m U) (polarCanonical (b 0) (b 1) y)).comp
        (fderiv ℝ (polarCanonical (b 0) (b 1)) y))
      (y + ContinuousLinearMap.inl ℝ (ℝ × ℝ) (ℝ × ℝ) 0) := by
    rw [ContinuousLinearMap.inl_apply, Prod.mk_zero_zero, add_zero]
    exact hasFDerivAt_centralForceEnergyMomentum_comp_polarCanonical b hU hr
  have h := ((hg.comp (0 : ℝ × ℝ)
    ((ContinuousLinearMap.inl ℝ (ℝ × ℝ) (ℝ × ℝ)).hasFDerivAt.const_add y)).congr_of_eventuallyEq
    (eventuallyEq_centralForceEnergyMomentum_polarCanonical b hr).symm).unique
    (hasFDerivAt_transversalModel_pair hU hr.ne' hc)
  simpa using DFunLike.congr_fun h a

/-- **The transversal Hessians of a circular orbit.** Let `(r, 0, θ, L)`, `r > 0`, be polar
canonical coordinates with vanishing radial momentum. For every linear functional
`ℓ` on `ℝ²` vanishing on the image of the derivative of the energy–momentum map `F` there, the
Hessian of `ℓ ∘ F` on the radial direction `(δr, δp_r)` is

`ℓ(e₀) (U_L''(r) δr² + δp_r² / m)`,

the Hessian of the reduced radial Hamiltonian `p_r² / (2m) + U_L(r)` scaled by the coefficient of
the energy in `ℓ`. Such functionals other than `0` exist exactly on the circular orbits, where
`U_L'(r) = 0`. -/
theorem hessianQuadraticForm_comp_centralForceEnergyMomentum_apply_fderiv_polarCanonical
    (hU : ContDiffAt ℝ 2 U r) (hr : 0 < r) {ℓ : (Fin 2 → ℝ) →L[ℝ] ℝ}
    (hℓ : ℓ.comp (fderiv ℝ (centralForceEnergyMomentum b m U)
      (polarCanonical (b 0) (b 1) ((r, 0), (θ, L)))) = 0) (a : ℝ × ℝ) :
    hessianQuadraticForm (ℓ ∘ centralForceEnergyMomentum b m U)
        (polarCanonical (b 0) (b 1) ((r, 0), (θ, L)))
        (fderiv ℝ (polarCanonical (b 0) (b 1)) ((r, 0), (θ, L)) (a, 0)) =
      ℓ (Pi.single 0 1) *
        (iteratedDeriv 2 (effectivePotential m L U) r * a.1 ^ 2 + a.2 ^ 2 / m) := by
  set y : (ℝ × ℝ) × (ℝ × ℝ) := ((r, 0), (θ, L))
  set F := centralForceEnergyMomentum b m U
  set φ := polarCanonical (b 0) (b 1)
  set ψ := fun a : ℝ × ℝ ↦ y + ContinuousLinearMap.inl ℝ (ℝ × ℝ) (ℝ × ℝ) a
  have hFC : ContDiffAt ℝ 2 F (φ y) := contDiffAt_centralForceEnergyMomentum_polarCanonical b hU hr
  have hφ : ContDiffAt ℝ 2 φ y := contDiffAt_polarCanonical (b 0) (b 1) hr.ne'
  have hℓF : ContDiffAt ℝ 2 (ℓ ∘ F) (φ y) := ℓ.contDiff.contDiffAt.comp _ hFC
  have hd₁ : fderiv ℝ (ℓ ∘ F) (φ y) = 0 := by
    rw [fderiv_comp _ ℓ.differentiableAt (hFC.differentiableAt two_ne_zero), ℓ.fderiv, hℓ]
  -- Pull the Hessian back first along the polar coordinates, then along the affine slice `ψ`;
  -- both are legitimate since the functions are critical at the respective points.
  have hy : ψ 0 = y := by simp [ψ]
  have hψ : ContDiffAt ℝ 2 ψ 0 :=
    (contDiff_const.add (ContinuousLinearMap.inl ℝ (ℝ × ℝ) (ℝ × ℝ)).contDiff).contDiffAt
  have hℓFφ : ContDiffAt ℝ 2 ((ℓ ∘ F) ∘ φ) (ψ 0) := by
    rw [hy]
    exact hℓF.comp y hφ
  have hd₂ : fderiv ℝ ((ℓ ∘ F) ∘ φ) (ψ 0) = 0 := by
    rw [hy, fderiv_comp y (hℓF.differentiableAt two_ne_zero) (hφ.differentiableAt two_ne_zero),
      hd₁, ContinuousLinearMap.zero_comp]
  have h := hessianQuadraticForm_comp hℓFφ hψ hd₂
  rw [hy, hessianQuadraticForm_comp hℓF hφ hd₁,
    ((ContinuousLinearMap.inl ℝ (ℝ × ℝ) (ℝ × ℝ)).hasFDerivAt.const_add y).fderiv] at h
  -- Along the slice, `ℓ ∘ F` is `ℓ(e₀)` times the transversal model plus a constant.
  have hslice : hessianQuadraticForm (((ℓ ∘ F) ∘ φ) ∘ ψ) 0 = hessianQuadraticForm
      (fun a ↦ (ℓ (Pi.single 0 1) • transversalModel m L U r) a + ℓ (Pi.single 1 1) * L) 0 := by
    refine hessianQuadraticForm_congr_of_eventuallyEq ?_
    filter_upwards [eventuallyEq_centralForceEnergyMomentum_polarCanonical b (m := m) (U := U)
      (θ := θ) (L := L) hr] with a ha
    have h₀ : centralForceHamiltonian m U (φ (ψ a)) = transversalModel m L U r a := by
      simpa [φ, ψ, y] using congrFun ha 0
    have h₁ : angularMomentum (b 0) (b 1) (φ (ψ a)) = L := by
      simpa [φ, ψ, y] using congrFun ha 1
    simp [F, comp_centralForceEnergyMomentum, h₀, h₁]
  have ha := congrArg (fun Q ↦ Q a) h
  rw [hslice, hessianQuadraticForm_add_const, hessianQuadraticForm_smul] at ha
  simp only [QuadraticMap.comp_apply, smul_apply, ContinuousLinearMap.coe_coe,
    ContinuousLinearMap.inl_apply, smul_eq_mul] at ha
  rw [← ha, hessianQuadraticForm_transversalModel hU hr.ne']

/-- The transversal Hessian of `ℓ ∘ F` pulled back to the radial directions is `ℓ(e₀)` times the
Hessian of the transversal model. -/
private theorem hessianQuadraticForm_comp_centralForceEnergyMomentum_comp_fderiv_polarCanonical_inl
    (hU : ContDiffAt ℝ 2 U r) (hr : 0 < r) {ℓ : (Fin 2 → ℝ) →L[ℝ] ℝ}
    (hℓ : ℓ.comp (fderiv ℝ (centralForceEnergyMomentum b m U)
      (polarCanonical (b 0) (b 1) ((r, 0), (θ, L)))) = 0) :
    (hessianQuadraticForm (ℓ ∘ centralForceEnergyMomentum b m U)
        (polarCanonical (b 0) (b 1) ((r, 0), (θ, L)))).comp
        ((fderiv ℝ (polarCanonical (b 0) (b 1)) ((r, 0), (θ, L)) :
          (ℝ × ℝ) × (ℝ × ℝ) →ₗ[ℝ] V × V) ∘ₗ LinearMap.inl ℝ (ℝ × ℝ) (ℝ × ℝ)) =
      ℓ (Pi.single 0 1) • hessianQuadraticForm (transversalModel m L U r) 0 := by
  ext a
  rw [QuadraticMap.comp_apply, LinearMap.comp_apply, LinearMap.inl_apply,
    ContinuousLinearMap.coe_coe,
    hessianQuadraticForm_comp_centralForceEnergyMomentum_apply_fderiv_polarCanonical b hU hr hℓ,
    smul_apply, smul_eq_mul, hessianQuadraticForm_transversalModel hU hr.ne']

/-- **Positive definiteness of the transversal Hessian on the radial directions.** For a positive
mass, at the point with polar coordinates `(r, 0, θ, L)`, `r > 0`, let `ℓ` be a functional with
`ℓ ∘ dF = 0` and `ℓ(e₀) = 1`, such as the critical functional `h - Ω l` of a circular orbit
(`TauCeti.comp_fderiv_centralForceEnergyMomentum_eq_zero`). The Hessian of `ℓ ∘ F`, pulled back
along the derivative of the polar coordinates to the radial directions `(δr, δp_r)`, is positive
definite exactly when `U_L''(r) > 0`.

Williamson's theorem
(`TauCeti.SymplecticForm.exists_isDarbouxBasis_eq_sum_smul_elliptic_of_posDef`) turns this positive
definite form on the two-dimensional slice into one elliptic block; that step is not restated
here. -/
theorem
    posDef_hessianQuadraticForm_comp_centralForceEnergyMomentum_comp_fderiv_polarCanonical_inl_iff
    (hm : 0 < m)
    (hU : ContDiffAt ℝ 2 U r) (hr : 0 < r) {ℓ : (Fin 2 → ℝ) →L[ℝ] ℝ}
    (hℓ : ℓ.comp (fderiv ℝ (centralForceEnergyMomentum b m U)
      (polarCanonical (b 0) (b 1) ((r, 0), (θ, L)))) = 0) (hℓ₀ : ℓ (Pi.single 0 1) = 1) :
    ((hessianQuadraticForm (ℓ ∘ centralForceEnergyMomentum b m U)
        (polarCanonical (b 0) (b 1) ((r, 0), (θ, L)))).comp
        ((fderiv ℝ (polarCanonical (b 0) (b 1)) ((r, 0), (θ, L)) :
          (ℝ × ℝ) × (ℝ × ℝ) →ₗ[ℝ] V × V) ∘ₗ LinearMap.inl ℝ (ℝ × ℝ) (ℝ × ℝ))).PosDef ↔
      0 < iteratedDeriv 2 (effectivePotential m L U) r := by
  have hQ (a : ℝ × ℝ) : ((hessianQuadraticForm (ℓ ∘ centralForceEnergyMomentum b m U)
      (polarCanonical (b 0) (b 1) ((r, 0), (θ, L)))).comp
      ((fderiv ℝ (polarCanonical (b 0) (b 1)) ((r, 0), (θ, L)) :
        (ℝ × ℝ) × (ℝ × ℝ) →ₗ[ℝ] V × V) ∘ₗ LinearMap.inl ℝ (ℝ × ℝ) (ℝ × ℝ))) a =
      iteratedDeriv 2 (effectivePotential m L U) r * a.1 ^ 2 + a.2 ^ 2 / m := by
    rw [hessianQuadraticForm_comp_centralForceEnergyMomentum_comp_fderiv_polarCanonical_inl b hU hr
      hℓ, hℓ₀, one_smul, hessianQuadraticForm_transversalModel hU hr.ne']
  refine ⟨fun h ↦ ?_, fun h a ha ↦ ?_⟩
  · have h₁ := h (1, 0) (by simp)
    rw [hQ] at h₁
    simpa using h₁
  rw [hQ]
  rcases eq_or_ne a.1 0 with h₁ | h₁
  · have h₂ : a.2 ≠ 0 := fun h₂ ↦ ha (Prod.ext h₁ h₂)
    rw [h₁]
    positivity
  · positivity

/-- On a circular orbit the potential has derivative `U'(r) = L² / (m r³)`, read at the point with
polar coordinates `(r, 0, θ, L)`. -/
private theorem deriv_eq_of_deriv_effectivePotential_eq_zero (hU : ContDiffAt ℝ 2 U r)
    (hr : 0 < r) (hc : deriv (effectivePotential m L U) r = 0) :
    deriv U r = angularMomentum (b 0) (b 1) (polarCanonical (b 0) (b 1) ((r, 0), (θ, L))) ^ 2 /
      (m * ‖(polarCanonical (b 0) (b 1) ((r, 0), (θ, L))).1‖ ^ 3) := by
  rw [angularMomentum_polarCanonical (b.norm_eq_one 0) (b.norm_eq_one 1)
    (b.inner_eq_zero (by decide)) hr.ne', norm_fst_polarCanonical_of_pos b hr]
  have h := ((hasDerivAt_effectivePotential (m := m) (ℓ := L)
    (hU.differentiableAt two_ne_zero).hasDerivAt hr.ne').deriv).symm.trans hc
  linarith

/-- In polar coordinates the angular-momentum component of the derivative is `δL`: the derivative
of the energy–momentum map sends the image of `(0, 0, 0, 1)` to a vector with second component
`1`. -/
private theorem fderiv_centralForceEnergyMomentum_fderiv_polarCanonical_one
    (hU : ContDiffAt ℝ 2 U r) (hr : 0 < r) :
    fderiv ℝ (centralForceEnergyMomentum b m U) (polarCanonical (b 0) (b 1) ((r, 0), (θ, L)))
      (fderiv ℝ (polarCanonical (b 0) (b 1)) ((r, 0), (θ, L)) ((0, 0), (0, 1))) 1 = 1 := by
  -- Off `r = 0`, the angular momentum of the point with polar coordinates `z` is `z.2.2`.
  have hev : (fun z ↦ centralForceEnergyMomentum b m U (polarCanonical (b 0) (b 1) z) 1)
      =ᶠ[𝓝 ((r, 0), (θ, L))] fun z ↦ z.2.2 := by
    filter_upwards [(continuous_fst.comp continuous_fst).continuousAt.eventually_ne hr.ne']
      with z hz
    rw [centralForceEnergyMomentum_one]
    exact angularMomentum_polarCanonical (b.norm_eq_one 0) (b.norm_eq_one 1)
      (b.inner_eq_zero (by decide)) hz
  have h := (((ContinuousLinearMap.proj 1).hasFDerivAt.comp _
    (hasFDerivAt_centralForceEnergyMomentum_comp_polarCanonical b hU hr)).congr_of_eventuallyEq
    hev.symm).unique ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp
      (ContinuousLinearMap.snd ℝ (ℝ × ℝ) (ℝ × ℝ))).hasFDerivAt
  simpa using DFunLike.congr_fun h ((0, 0), (0, 1))

/-- A point `(q, p)` with `q ≠ 0` and `⟪q, p⟫ = 0` has polar coordinates `(‖q‖, 0, θ, L(q, p))`
for some angle `θ`. -/
private theorem exists_polarCanonical_eq {x : V × V} (hq : x.1 ≠ 0) (h0 : ⟪x.1, x.2⟫_ℝ = 0) :
    ∃ θ : ℝ, polarCanonical (b 0) (b 1) ((‖x.1‖, 0), (θ, angularMomentum (b 0) (b 1) x)) = x := by
  obtain ⟨θ, hθ⟩ : ∃ θ : ℝ, (θ : Real.Angle) = polarAngle (b 0) (b 1) x.1 :=
    (polarAngle (b 0) (b 1) x.1).induction_on fun θ ↦ ⟨θ, rfl⟩
  have hx := polarCanonical_polarAngle b x.2 hq hθ
  rw [radialMomentum_apply, h0, zero_div, Prod.mk.eta] at hx
  exact ⟨θ, hx⟩

section FiniteDimensional

variable [FiniteDimensional ℝ V]

/-- **The critical functional of a circular orbit.** At the point with polar coordinates
`(r, 0, θ, L)` of a circular orbit, `dH = Ω dL` with the angular velocity `Ω = L / (m r²)`: the
functional `(h, l) ↦ h - Ω l` kills the image of the derivative of the energy–momentum map. -/
theorem comp_fderiv_centralForceEnergyMomentum_eq_zero (hU : ContDiffAt ℝ 2 U r)
    (hr : 0 < r) (hc : deriv (effectivePotential m L U) r = 0) :
    (ContinuousLinearMap.proj 0 - (L / (m * r ^ 2)) • ContinuousLinearMap.proj 1 :
        (Fin 2 → ℝ) →L[ℝ] ℝ).comp (fderiv ℝ (centralForceEnergyMomentum b m U)
          (polarCanonical (b 0) (b 1) ((r, 0), (θ, L)))) = 0 := by
  set P := polarCanonical (b 0) (b 1) ((r, 0), (θ, L))
  have hq : P.1 ≠ 0 := fst_polarCanonical_ne_zero_of_pos b hr
  have hU' : HasDerivAt U (deriv U r) ‖P.1‖ := hasDerivAt_norm_fst_polarCanonical_of_pos b hU hr
  have hX := stdSymplecticForm_hamiltonianVectorField_centralForceHamiltonian_eq_smul b hU' hq
    (inner_polarCanonical_of_pos b hr) (deriv_eq_of_deriv_effectivePotential_eq_zero b hU hr hc)
  rw [angularMomentum_polarCanonical (b.norm_eq_one 0) (b.norm_eq_one 1)
    (b.inner_eq_zero (by decide)) hr.ne', norm_fst_polarCanonical_of_pos b hr] at hX
  have key (v : V × V) : fderiv ℝ (centralForceHamiltonian m U) P v =
      L / (m * r ^ 2) * fderiv ℝ (angularMomentum (b 0) (b 1)) P v := by
    rw [← stdSymplecticForm.apply_hamiltonianVectorField,
      ← stdSymplecticForm.apply_hamiltonianVectorField, hX]
    simp
  refine ContinuousLinearMap.ext fun v ↦ ?_
  rw [(hasFDerivAt_centralForceEnergyMomentum b hU' hq).fderiv,
    ← (hasFDerivAt_centralForceHamiltonian hU' hq).fderiv,
    ← (hasFDerivAt_angularMomentum (b 0) (b 1) P).fderiv]
  simp [key]

/-- **Circular orbits have rank one, in polar coordinates.** At the point with polar coordinates
`(r, 0, θ, L)`, `r > 0`, of a circular orbit, the derivative of the energy–momentum map has rank
one. -/
theorem finrank_range_fderiv_centralForceEnergyMomentum_polarCanonical (hm : m ≠ 0)
    (hU : ContDiffAt ℝ 2 U r) (hr : 0 < r) (hc : deriv (effectivePotential m L U) r = 0) :
    finrank ℝ (fderiv ℝ (centralForceEnergyMomentum b m U)
      (polarCanonical (b 0) (b 1) ((r, 0), (θ, L)))).range = 1 := by
  set P := polarCanonical (b 0) (b 1) ((r, 0), (θ, L))
  have hq : P.1 ≠ 0 := fst_polarCanonical_ne_zero_of_pos b hr
  have hU' : HasDerivAt U (deriv U r) ‖P.1‖ := hasDerivAt_norm_fst_polarCanonical_of_pos b hU hr
  -- The point is critical, so the derivative is not onto `ℝ²`.
  have hns : ¬Function.Surjective (fderiv ℝ (centralForceEnergyMomentum b m U) P) := by
    rw [← isRegularPoint_iff_surjective_fderiv, isRegularPoint_centralForceEnergyMomentum_iff b hm
      hU' hq, not_not]
    exact ⟨inner_polarCanonical_of_pos b hr,
      deriv_eq_of_deriv_effectivePotential_eq_zero b hU hr hc⟩
  have hlt := Submodule.finrank_lt (s := (fderiv ℝ (centralForceEnergyMomentum b m U) P).range)
    fun h ↦ hns (LinearMap.range_eq_top.1 h)
  rw [Module.finrank_fin_fun] at hlt
  -- It is not zero, since its angular-momentum component is `δL`.
  have hpos : finrank ℝ (fderiv ℝ (centralForceEnergyMomentum b m U) P).range ≠ 0 := by
    intro h0
    set w := fderiv ℝ (polarCanonical (b 0) (b 1)) ((r, 0), (θ, L)) ((0, 0), (0, 1))
    have hv : fderiv ℝ (centralForceEnergyMomentum b m U) P w 1 = 1 :=
      fderiv_centralForceEnergyMomentum_fderiv_polarCanonical_one b hU hr
    have hmem : fderiv ℝ (centralForceEnergyMomentum b m U) P w ∈
        (fderiv ℝ (centralForceEnergyMomentum b m U) P).range :=
      LinearMap.mem_range_self _ w
    rw [Submodule.finrank_eq_zero.1 h0, Submodule.mem_bot] at hmem
    rw [hmem] at hv
    exact zero_ne_one hv
  omega

/-- **The transversal space of a circular orbit is a plane.** At the point with polar
coordinates `(r, 0, θ, L)` of a circular orbit, the reduced space `ker dF ⧸ (ker dF)^ω` has
dimension `4 - 2 · 1 = 2`. -/
private theorem finrank_reducedSpace_ker_fderiv_centralForceEnergyMomentum (hm : m ≠ 0)
    (hU : ContDiffAt ℝ 2 U r) (hr : 0 < r) (hc : deriv (effectivePotential m L U) r = 0) :
    finrank ℝ ((stdSymplecticForm (V := V)).ReducedSpace (fderiv ℝ
      (centralForceEnergyMomentum b m U) (polarCanonical (b 0) (b 1) ((r, 0), (θ, L)))).ker) =
      2 := by
  have h := (stdSymplecticForm (V := V)).finrank_reducedSpace_ker_fderiv
    ((contDiffAt_centralForceEnergyMomentum_polarCanonical b (m := m) (θ := θ) (L := L) hU
      hr).differentiableAt two_ne_zero)
    fun ℓ ℓ' ↦ stdSymplecticForm_poissonBracket_comp_centralForceEnergyMomentum b m U ℓ ℓ' _
  rw [finrank_range_fderiv_centralForceEnergyMomentum_polarCanonical b hm hU hr hc,
    Module.finrank_prod, Module.finrank_eq_card_basis b.toBasis, Fintype.card_fin] at h
  omega

/-! ### Nondegeneracy -/

/-- **Nondegeneracy of circular orbits, in polar coordinates.** Let `(r, 0, θ, L)`, `r > 0`, be the
polar canonical coordinates of a point of a circular orbit of a planar central force, that is,
`r` is a critical point of the effective potential `U_L`, and let the potential be `C²` at `r`.
The point is a nondegenerate point of the energy–momentum map exactly when `r` is a nondegenerate
critical point of `U_L`, `U_L''(r) ≠ 0`. -/
theorem isNondegeneratePoint_centralForceEnergyMomentum_polarCanonical_iff (hm : m ≠ 0)
    (hU : ContDiffAt ℝ 2 U r) (hr : 0 < r) (hc : deriv (effectivePotential m L U) r = 0) :
    (stdSymplecticForm (V := V)).IsNondegeneratePoint (centralForceEnergyMomentum b m U)
        (polarCanonical (b 0) (b 1) ((r, 0), (θ, L))) ↔
      iteratedDeriv 2 (effectivePotential m L U) r ≠ 0 := by
  set y : (ℝ × ℝ) × (ℝ × ℝ) := ((r, 0), (θ, L))
  set F := centralForceEnergyMomentum b m U
  set T := fderiv ℝ F (polarCanonical (b 0) (b 1) y)
  -- The radial directions `(δr, δp_r)` form a symplectic slice of the transversal space.
  set j : ℝ × ℝ →ₗ[ℝ] V × V := (fderiv ℝ (polarCanonical (b 0) (b 1)) y :
    (ℝ × ℝ) × (ℝ × ℝ) →ₗ[ℝ] V × V) ∘ₗ LinearMap.inl ℝ (ℝ × ℝ) (ℝ × ℝ)
  have hFC : ContDiffAt ℝ 2 F (polarCanonical (b 0) (b 1) y) :=
    contDiffAt_centralForceEnergyMomentum_polarCanonical b hU hr
  have hjU (a : ℝ × ℝ) : j a ∈ T.ker :=
    fderiv_centralForceEnergyMomentum_fderiv_polarCanonical_inl b hU hr hc a
  have hjω (a c : ℝ × ℝ) : stdSymplecticForm (j a) (j c) = stdSymplecticForm a c := by
    have h := stdSymplecticForm_fderiv_polarCanonical (b.norm_eq_one 0) (b.norm_eq_one 1)
      (b.inner_eq_zero (by decide)) (x := y) hr.ne' (a, 0) (c, 0)
    simpa [j, SymplecticForm.prod_apply] using h
  have hd : finrank ℝ (ℝ × ℝ) = finrank ℝ ((stdSymplecticForm (V := V)).ReducedSpace T.ker) := by
    rw [finrank_reducedSpace_ker_fderiv_centralForceEnergyMomentum b hm hU hr hc,
      Module.finrank_prod, Module.finrank_self]
  rw [SymplecticForm.isNondegeneratePoint_iff_of_poissonBracket hFC fun ℓ ℓ' ↦ .of_forall fun z ↦
      stdSymplecticForm_poissonBracket_comp_centralForceEnergyMomentum b m U ℓ' ℓ z,
    SymplecticForm.isNondegenerateQuadraticFamily_reduction_iff_of_slice hjU hjω hd]
  -- In the slice the transversal Hessians are the multiples `ℓ(e₀) Q` of the Hessian `Q` of the
  -- transversal model, and the critical functional `h - Ω l` has `ℓ(e₀) = 1`.
  have hfam : (fun ℓ : {ℓ : (Fin 2 → ℝ) →L[ℝ] ℝ // ℓ.comp T = 0} ↦
      (hessianQuadraticForm (ℓ.val ∘ F) (polarCanonical (b 0) (b 1) y)).comp j) =
      fun ℓ ↦ ℓ.val (Pi.single 0 1) • hessianQuadraticForm (transversalModel m L U r) 0 := by
    funext ℓ
    exact hessianQuadraticForm_comp_centralForceEnergyMomentum_comp_fderiv_polarCanonical_inl b hU
      hr ℓ.property
  rw [hfam, SymplecticForm.isNondegenerateQuadraticFamily_smul_iff
      (i := ⟨_, comp_fderiv_centralForceEnergyMomentum_eq_zero b hU hr hc⟩) (by simp),
    SymplecticForm.isNondegenerateQuadraticFamily_const_iff (by simp),
    nondegenerate_hessianQuadraticForm_transversalModel_iff hm hU hr.ne' hc]

/-- **Circular orbits have rank one.** Let `(q, p)` be a point of a circular orbit of a planar
central force with angular momentum `L`: `q ≠ 0`, `⟪q, p⟫ = 0`, and `‖q‖` is a critical point of
the effective potential `U_L`, at which the potential is `C²`. Then the derivative of the
energy–momentum map `(H, L)` has rank one at `(q, p)`. -/
theorem finrank_range_fderiv_centralForceEnergyMomentum (hm : m ≠ 0) {x : V × V}
    (hq : x.1 ≠ 0) (hU : ContDiffAt ℝ 2 U ‖x.1‖) (h0 : ⟪x.1, x.2⟫_ℝ = 0)
    (hc : deriv (effectivePotential m (angularMomentum (b 0) (b 1) x) U) ‖x.1‖ = 0) :
    finrank ℝ (fderiv ℝ (centralForceEnergyMomentum b m U) x).range = 1 := by
  obtain ⟨θ, hx⟩ := exists_polarCanonical_eq b hq h0
  have h := finrank_range_fderiv_centralForceEnergyMomentum_polarCanonical b (θ := θ) hm hU
    (norm_pos_iff.2 hq) hc
  rwa [hx] at h

/-- **Nondegeneracy of circular orbits.** Let `(q, p)` be a point of a circular orbit of a planar
central force with angular momentum `L`: `q ≠ 0`, `⟪q, p⟫ = 0`, and `‖q‖` is a critical point of
the effective potential `U_L`, at which the potential is `C²`. Then `(q, p)` is a nondegenerate
point of the energy–momentum map `(H, L)` exactly when `‖q‖` is a nondegenerate critical point of
`U_L`, `U_L''(‖q‖) ≠ 0`. The energy–momentum map has rank one there
(`TauCeti.finrank_range_fderiv_centralForceEnergyMomentum`). -/
theorem isNondegeneratePoint_centralForceEnergyMomentum_iff (hm : m ≠ 0) {x : V × V}
    (hq : x.1 ≠ 0) (hU : ContDiffAt ℝ 2 U ‖x.1‖) (h0 : ⟪x.1, x.2⟫_ℝ = 0)
    (hc : deriv (effectivePotential m (angularMomentum (b 0) (b 1) x) U) ‖x.1‖ = 0) :
    (stdSymplecticForm (V := V)).IsNondegeneratePoint (centralForceEnergyMomentum b m U) x ↔
      iteratedDeriv 2 (effectivePotential m (angularMomentum (b 0) (b 1) x) U) ‖x.1‖ ≠ 0 := by
  obtain ⟨θ, hx⟩ := exists_polarCanonical_eq b hq h0
  have h := isNondegeneratePoint_centralForceEnergyMomentum_polarCanonical_iff b (θ := θ) hm hU
    (norm_pos_iff.2 hq) hc
  rwa [hx] at h

end FiniteDimensional

end TauCeti
