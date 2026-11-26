/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.CentralForce.Nondegenerate
public import TauCeti.Geometry.Symplectic.Hamiltonian.SingularPoint.Williamson
import TauCeti.Geometry.Symplectic.Hamiltonian.CentralForce.SingularPoint

/-!
# The Williamson type of a stable circular orbit of a planar central force

Let `F = (H, L)` be the energy–momentum map of a planar central force
(`TauCeti.centralForceEnergyMomentum`), with mass `m > 0`, `H = ‖p‖² / (2m) + U(‖q‖)` and `L` the
angular momentum. A point `x = (q, p)` of a circular orbit, `⟪q, p⟫ = 0` with `r = ‖q‖` a critical
point of the effective potential `U_L(r) = L² / (2 m r²) + U(r)`, is a point of rank one of `F`,
and it is a nondegenerate point exactly when `U_L''(r) ≠ 0`
(`TauCeti.isNondegeneratePoint_centralForceEnergyMomentum_iff`).

This file computes its Williamson type at a nondegenerate minimum of the effective potential,
`U_L''(r) > 0`: the type is one elliptic block, `(k_e, k_h, k_f) = (1, 0, 0)`
(`TauCeti.hasWilliamsonTypeAt_centralForceEnergyMomentum_one_zero_zero`). The critical functions
at `x` are the multiples of `H - Ω L`, `Ω = L / (m r²)`
(`TauCeti.comp_centralForceEnergyMomentum_eq_smul_of_comp_fderiv_eq_zero`), and on the
transversal plane the Hessian of `H - Ω L` is a positive multiple of the elliptic block
`(x² + y²) / 2` of a Darboux basis
(`TauCeti.exists_isDarbouxBasis_hessianQuadraticForm_centralForceHamiltonian_sub_eq_smul_elliptic`).
So the transversal Hessians span the line of that elliptic block. This matches the dimension
count `k_e + k_h + 2 k_f = n - r = 2 - 1`.
-/

public section

noncomputable section

open scoped InnerProductSpace

namespace TauCeti

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  (b : OrthonormalBasis (Fin 2) ℝ V) {m : ℝ} {U : ℝ → ℝ} {x : V × V}

/-- **A stable circular orbit has Williamson type `(1, 0, 0)`.** At a point `x = (q, p)` of a
circular orbit of a planar central force with `m > 0`, `⟪q, p⟫ = 0` and
`U'(‖q‖) = L² / (m ‖q‖³)`, at which `‖q‖` is a nondegenerate minimum of the effective potential,
`U_L''(‖q‖) > 0`, the energy–momentum map has a nondegenerate point of Williamson type
`(1, 0, 0)`: its transversal Hessians span the line of one elliptic block. -/
theorem hasWilliamsonTypeAt_centralForceEnergyMomentum_one_zero_zero (hm : 0 < m)
    (hU : ContDiffAt ℝ 2 U ‖x.1‖) (hq : x.1 ≠ 0) (h0 : ⟪x.1, x.2⟫_ℝ = 0)
    (hU' : deriv U ‖x.1‖ = angularMomentum (b 0) (b 1) x ^ 2 / (m * ‖x.1‖ ^ 3))
    (hmin : 0 < iteratedDeriv 2 (effectivePotential m (angularMomentum (b 0) (b 1) x) U) ‖x.1‖) :
    stdSymplecticForm.HasWilliamsonTypeAt (centralForceEnergyMomentum b m U) x 1 0 0 := by
  have hUd : HasDerivAt U (deriv U ‖x.1‖) ‖x.1‖ := (hU.differentiableAt two_ne_zero).hasDerivAt
  have hc : deriv (effectivePotential m (angularMomentum (b 0) (b 1) x) U) ‖x.1‖ = 0 :=
    (deriv_effectivePotential_eq_zero_iff (hU.differentiableAt two_ne_zero)
      (norm_ne_zero_iff.2 hq)).2 hU'
  have hnd := (isNondegeneratePoint_centralForceEnergyMomentum_iff b hm.ne' hq hU h0 hc).2 hmin.ne'
  set T := fderiv ℝ (centralForceEnergyMomentum b m U) x
  obtain ⟨e, ν, he, hν, hH⟩ :=
    exists_isDarbouxBasis_hessianQuadraticForm_centralForceHamiltonian_sub_eq_smul_elliptic b hm
      hU hq h0 hU' hmin
  set P := SymplecticForm.elliptic e 0
  -- Each transversal Hessian is the multiple `ℓ(1, 0) ν` of the elliptic block `P`.
  have hfam (ℓ : {ℓ : (Fin 2 → ℝ) →L[ℝ] ℝ // ℓ.comp T = 0}) (hQ) :
      stdSymplecticForm.reducedQuadraticForm T.ker
        (hessianQuadraticForm (ℓ.val ∘ centralForceEnergyMomentum b m U) x) hQ =
          (ℓ.val (Pi.single 0 1) * ν) • P := by
    ext y
    induction y using Submodule.Quotient.induction_on with
    | H u =>
      rw [SymplecticForm.reducedQuadraticForm_mk,
        comp_centralForceEnergyMomentum_eq_smul_of_comp_fderiv_eq_zero b hUd hq h0 hU' ℓ.property,
        hessianQuadraticForm_smul, smul_apply, hH u]
      simp [mul_assoc]
  -- The critical functional `ℓ₀` with `ℓ₀ ∘ F = H - Ω L` has transversal Hessian `ν • P`.
  obtain ⟨ℓ₀, hℓ₀, hcomp⟩ :=
    exists_comp_fderiv_centralForceEnergyMomentum_eq_zero_and_comp_eq b hUd hq h0 hU'
  refine SymplecticForm.hasWilliamsonTypeAt_iff.2
    ⟨hnd, (SymplecticForm.hasWilliamsonType_iff_of_span_eq ?_).2 he.hasWilliamsonType_elliptic⟩
  rw [Set.range_unique (f := SymplecticForm.elliptic e), Fin.default_eq_zero]
  refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)
  · rintro _ ⟨ℓ, rfl⟩
    dsimp only
    rw [hfam]
    exact Submodule.smul_mem _ _ (Submodule.subset_span rfl)
  · rintro _ rfl
    refine (Submodule.smul_mem_iff _ hν.ne').1 (Submodule.subset_span ⟨⟨ℓ₀, hℓ₀⟩, ?_⟩)
    ext y
    induction y using Submodule.Quotient.induction_on with
    | H u =>
      simp only [SymplecticForm.reducedQuadraticForm_mk, hcomp, smul_apply, smul_eq_mul]
      exact hH u

end TauCeti
