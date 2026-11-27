/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.CentralForce.Polar
public import TauCeti.Geometry.Symplectic.Hamiltonian.Elliptic
public import TauCeti.Geometry.Symplectic.Hamiltonian.SingularPoint
import TauCeti.Analysis.Calculus.Bilinear
import TauCeti.Analysis.Calculus.FDeriv.Prod
import TauCeti.Analysis.Calculus.Morse.NormSq
import TauCeti.Analysis.Calculus.Morse.OneDimensional
import TauCeti.Analysis.Calculus.Morse.Prod
import TauCeti.Geometry.Symplectic.Hamiltonian.Williamson

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
(`TauCeti.isNondegeneratePoint_centralForceEnergyMomentum_polarCanonical_iff`; at a point of
`V × V` this is `TauCeti.isNondegeneratePoint_centralForceEnergyMomentum_iff`, in the module
`TauCeti.Geometry.Symplectic.Hamiltonian.CentralForce.SingularPoint`). For `m > 0` the transversal
Hessian of the critical function `H - Ω L` on the radial directions is positive definite exactly
when `U_L''(r) > 0`, that is, at a nondegenerate minimum of the effective potential
(`posDef_hessianQuadraticForm_comp_centralForceEnergyMomentum_comp_fderiv_polarCanonical_inl_iff`).
By Williamson's theorem
(`TauCeti.SymplecticForm.exists_isDarbouxBasis_eq_sum_smul_elliptic_of_posDef`), a positive
definite form on the two-dimensional transversal plane is a multiple of one elliptic block.

Directly in `V × V`, the critical functions at such a point `x` are the multiples of `H - Ω L`
(`TauCeti.comp_centralForceEnergyMomentum_eq_smul_of_comp_fderiv_eq_zero`). The transversal plane
is spanned by the classes of the radial displacement `(q, -p)` and of the radial momentum
`(0, q)`, which pair to `ω₀ = ‖q‖²`, and the Hessian of `H - Ω L` is diagonal on them, with the
values `r² U_L''(r)` and `r² / m`, computed from the Hessians of the angular momentum, `2 L`
(`TauCeti.hessianQuadraticForm_angularMomentum`), and of the energy
(`TauCeti.hessianQuadraticForm_centralForceHamiltonian_apply`). Hence at a nondegenerate minimum
of the effective potential, for `m > 0`, the transversal Hessian of `H - Ω L` is `ν > 0` times the
elliptic block `(x² + y²) / 2` of a Darboux basis of the transversal plane
(`TauCeti.exists_isDarbouxBasis_hessianQuadraticForm_centralForceHamiltonian_sub_eq_smul_elliptic`).

The components of `F` Poisson-commute everywhere
(`TauCeti.stdSymplecticForm_poissonBracket_comp_centralForceEnergyMomentum`), which makes the
transversal Hessians well defined.

## Main results

* `TauCeti.comp_fderiv_centralForceEnergyMomentum_eq_zero`: on a circular orbit, the critical
  functional `h - Ω l` kills the image of `dF`.
* `TauCeti.finrank_range_fderiv_centralForceEnergyMomentum_polarCanonical`: `F` has rank one at a
  point of a circular orbit.
* `TauCeti.hessianQuadraticForm_comp_centralForceEnergyMomentum_apply_fderiv_polarCanonical`: the
  transversal Hessians in the slice coordinates `(δr, δp_r)`.
* `TauCeti.isNondegeneratePoint_centralForceEnergyMomentum_polarCanonical_iff`: a point of a
  circular orbit is nondegenerate exactly when `U_L''(r) ≠ 0`.
* `posDef_hessianQuadraticForm_comp_centralForceEnergyMomentum_comp_fderiv_polarCanonical_inl_iff`:
  for `m > 0` the transversal Hessian of `H - Ω L` on the radial directions is positive definite
  exactly when `U_L''(r) > 0`.
* `TauCeti.hessianQuadraticForm_angularMomentum`: the angular momentum is quadratic, with Hessian
  `2 L`.
* `TauCeti.hessianQuadraticForm_centralForceHamiltonian_apply`: the Hessian of the energy is the
  Hessian of `q ↦ U(‖q‖)` plus `‖δp‖² / m`.
* `TauCeti.comp_centralForceEnergyMomentum_eq_smul_of_comp_fderiv_eq_zero`: the critical functions
  at a circular orbit are the multiples of `H - Ω L`.
* `TauCeti.exists_isDarbouxBasis_hessianQuadraticForm_centralForceHamiltonian_sub_eq_smul_elliptic`:
  at a nondegenerate minimum of the effective potential the transversal type is one elliptic block.

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

/-- A potential differentiable at `r > 0` is differentiable at the distance to the origin of the
point with polar coordinates `(r, 0, θ, L)`. -/
private theorem hasDerivAt_norm_fst_polarCanonical_of_pos (hU : DifferentiableAt ℝ U r)
    (hr : 0 < r) : HasDerivAt U (deriv U r) ‖(polarCanonical (b 0) (b 1) ((r, 0), (θ, L))).1‖ := by
  rw [norm_fst_polarCanonical_of_pos b hr]
  exact hU.hasDerivAt

/-- For a potential `C²` at `r > 0`, the energy–momentum map is `C²` at the point with polar
coordinates `(r, 0, θ, L)`. -/
private theorem contDiffAt_centralForceEnergyMomentum_polarCanonical (hU : ContDiffAt ℝ 2 U r)
    (hr : 0 < r) : ContDiffAt ℝ 2 (centralForceEnergyMomentum b m U)
      (polarCanonical (b 0) (b 1) ((r, 0), (θ, L))) :=
  contDiffAt_centralForceEnergyMomentum b (by rwa [norm_fst_polarCanonical_of_pos b hr])
    (fst_polarCanonical_ne_zero_of_pos b hr)

/-- The chain rule for the energy–momentum map in polar coordinates at `(r, 0, θ, L)`, `r > 0`. -/
private theorem hasFDerivAt_centralForceEnergyMomentum_comp_polarCanonical
    (hU : DifferentiableAt ℝ U r) (hr : 0 < r) :
    HasFDerivAt (centralForceEnergyMomentum b m U ∘ polarCanonical (b 0) (b 1))
      ((fderiv ℝ (centralForceEnergyMomentum b m U)
        (polarCanonical (b 0) (b 1) ((r, 0), (θ, L)))).comp
        (fderiv ℝ (polarCanonical (b 0) (b 1)) ((r, 0), (θ, L)))) ((r, 0), (θ, L)) :=
  (hasFDerivAt_centralForceEnergyMomentum b (hasDerivAt_norm_fst_polarCanonical_of_pos b hU hr)
    (fst_polarCanonical_ne_zero_of_pos b hr)).differentiableAt.hasFDerivAt.comp _
    ((contDiffAt_polarCanonical (b 0) (b 1) (n := 1) hr.ne').differentiableAt
      one_ne_zero).hasFDerivAt

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
    exact hasFDerivAt_centralForceEnergyMomentum_comp_polarCanonical b
      (hU.differentiableAt two_ne_zero) hr
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
private theorem deriv_eq_of_deriv_effectivePotential_eq_zero (hU : DifferentiableAt ℝ U r)
    (hr : 0 < r) (hc : deriv (effectivePotential m L U) r = 0) :
    deriv U r = angularMomentum (b 0) (b 1) (polarCanonical (b 0) (b 1) ((r, 0), (θ, L))) ^ 2 /
      (m * ‖(polarCanonical (b 0) (b 1) ((r, 0), (θ, L))).1‖ ^ 3) := by
  rw [angularMomentum_polarCanonical (b.norm_eq_one 0) (b.norm_eq_one 1)
    (b.inner_eq_zero (by decide)) hr.ne', norm_fst_polarCanonical_of_pos b hr]
  have h := ((hasDerivAt_effectivePotential (m := m) (ℓ := L) hU.hasDerivAt
    hr.ne').deriv).symm.trans hc
  linarith

/-- In polar coordinates the angular-momentum component of the derivative is `δL`: the derivative
of the energy–momentum map sends the image of `(0, 0, 0, 1)` to a vector with second component
`1`. -/
private theorem fderiv_centralForceEnergyMomentum_fderiv_polarCanonical_one
    (hU : DifferentiableAt ℝ U r) (hr : 0 < r) :
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

section FiniteDimensional

variable [FiniteDimensional ℝ V]

/-- **The critical functional of a circular orbit.** At the point with polar coordinates
`(r, 0, θ, L)` of a circular orbit, `dH = Ω dL` with the angular velocity `Ω = L / (m r²)`: the
functional `(h, l) ↦ h - Ω l` kills the image of the derivative of the energy–momentum map. -/
theorem comp_fderiv_centralForceEnergyMomentum_eq_zero (hU : DifferentiableAt ℝ U r)
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
    (hU : DifferentiableAt ℝ U r) (hr : 0 < r) (hc : deriv (effectivePotential m L U) r = 0) :
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
  rw [finrank_range_fderiv_centralForceEnergyMomentum_polarCanonical b hm
      (hU.differentiableAt two_ne_zero) hr hc,
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
      (i := ⟨_, comp_fderiv_centralForceEnergyMomentum_eq_zero b (hU.differentiableAt two_ne_zero)
        hr hc⟩) (by simp),
    SymplecticForm.isNondegenerateQuadraticFamily_const_iff (by simp),
    nondegenerate_hessianQuadraticForm_transversalModel_iff hm hU hr.ne' hc]

end FiniteDimensional

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
theorem hessianQuadraticForm_centralForceHamiltonian_apply {x : V × V} (hU : ContDiffAt ℝ 2 U ‖x.1‖)
    (hq : x.1 ≠ 0) (v : V × V) :
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
private theorem hessianQuadraticForm_sub_mul_angularMomentum_apply {x : V × V}
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

variable [FiniteDimensional ℝ V] {x : V × V}

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

/-- At a point of a circular orbit there is a critical functional `ℓ₀`, the functional
`(a, c) ↦ a - Ω c` with `Ω = L / (m ‖q‖²)`: it kills the image of the differential, and composed
with `F` it is `H - Ω L`. -/
theorem exists_comp_fderiv_centralForceEnergyMomentum_eq_zero_and_comp_eq {U' : ℝ}
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
private theorem finrank_reducedSpace_ker_fderiv_centralForceEnergyMomentum_of_hasDerivAt
    {U' : ℝ}
    (hU : HasDerivAt U U' ‖x.1‖) (hq : x.1 ≠ 0) (h0 : ⟪x.1, x.2⟫_ℝ = 0)
    (hU' : U' = angularMomentum (b 0) (b 1) x ^ 2 / (m * ‖x.1‖ ^ 3)) :
    finrank ℝ ((stdSymplecticForm (V := V)).ReducedSpace
      (fderiv ℝ (centralForceEnergyMomentum b m U) x).ker) = 2 := by
  have h := (stdSymplecticForm (V := V)).finrank_reducedSpace_ker_fderiv
    (hasFDerivAt_centralForceEnergyMomentum b (m := m) hU hq).differentiableAt
    fun ℓ ℓ' ↦ stdSymplecticForm_poissonBracket_comp_centralForceEnergyMomentum b m U ℓ ℓ' x
  rw [range_fderiv_centralForceEnergyMomentum b hU hq h0 hU',
    finrank_span_singleton fun h ↦ by simpa using congrFun h 1, Module.finrank_prod,
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
  · rw [Fintype.card_fin,
      finrank_reducedSpace_ker_fderiv_centralForceEnergyMomentum_of_hasDerivAt b hU hq h0 hU']
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
  obtain ⟨ℓ₀, hℓ₀, hcomp⟩ :=
    exists_comp_fderiv_centralForceEnergyMomentum_eq_zero_and_comp_eq b hUd hq h0 hU'
  rw [← hcomp]
  exact ⟨_, (stdSymplecticForm (V := V)).reducedQuadraticForm_mk _ _ fun _ hw u _ ↦
    (stdSymplecticForm (V := V)).polar_hessianQuadraticForm_eq_zero_of_mem_orthogonal
      (contDiffAt_centralForceEnergyMomentum b hU hq) hℓ₀
      (fun ℓ' ↦ .of_forall fun y ↦
        stdSymplecticForm_poissonBracket_comp_centralForceEnergyMomentum b m U ℓ' ℓ₀ y)
      hw.2 u⟩

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

/-! ### The elliptic type -/

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
    rw [finrank_reducedSpace_ker_fderiv_centralForceEnergyMomentum_of_hasDerivAt b hUd hq h0 hU',
      Fintype.card_prod, Fintype.card_fin, Fintype.card_fin] at h
    omega
  refine ⟨d, ν 0, hd, hν 0, fun u ↦ ?_⟩
  rw [← hQ, hQd, Fin.sum_univ_one, smul_apply, smul_eq_mul]

end Circular

end TauCeti
