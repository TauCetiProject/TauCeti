/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Curvature
import TauCeti.Geometry.Manifold.ContMDiff.Prod
import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Normalization.MovingEnds

/-!
# Normalizing the end Hamiltonians of the pair of pants

A Hamiltonian is determined by its Hamiltonian vector field only up to a function of time:
`H_q(t, x)` and `H_q(t, x) + c_q(t)` generate the same flow, have the same one-periodic orbits,
and give the same Floer equation. Their actions differ by the time average of `c_q`
(`TauCeti.SymplecticForm.hamiltonianAction_add_const`, and `TauCeti.cappedLoopAction_add_const`
for capped loops in a manifold). This file shows how the energy identity of the pair of pants

`E(u) = ∫_S u^*ω + ∑ q, ±∫₀¹ H_q(t, x_q(t)) dt - ∫_S R_K(u)`

absorbs such a change of normalization on its three ends, for a manifold target `M` with a
two-form `ω`, such as a closed symplectic manifold, and for a symplectic vector space target.

The pair-of-pants perturbation (`TauCeti.Floer.pairOfPantsPerturbation`) is additive in the end
Hamiltonians, so normalizing by `c` adds to it the perturbation `k` of the target-independent
Hamiltonians `c_q`, which has no Hamiltonian vector field
(`TauCeti.Floer.pairOfPantsPerturbation_add_const`). Consequently:

* the perturbed derivative `du - X_K`, hence the Floer equation, and the Floer energy density
  are unchanged
  (`TauCeti.SmoothTwoForm.perturbedMFDeriv_pairOfPantsPerturbation_add_const`,
  `TauCeti.SmoothTwoForm.floerEnergyDensity_pairOfPantsPerturbation_add_const`);
* the curvature changes by the curvature of `k`, which does not depend on the target point
  (`TauCeti.SmoothTwoForm.hamiltonianCurvature_pairOfPantsPerturbation_add_const`);
* the integral of the curvature of `k` over the pair of pants is exactly the sum
  `∑ q, ±∫₀¹ c_q`, with the sign `+` on the input ends `0`, `1` and `-` on the output end `∞`
  (`TauCeti.SmoothTwoForm.setIntegral_hamiltonianCurvature_pairOfPantsPerturbation_const`).

So along every map whose curvature for `H_q` is integrable on `S`, the integrated curvature
changes by `∑ q, ±∫₀¹ c_q`
(`TauCeti.SmoothTwoForm.setIntegral_hamiltonianCurvature_pairOfPantsPerturbation_add_const`),
which is exactly the change `∑ q, ±∫₀¹ c_q` of the Hamiltonian terms at the asymptotic orbits.
The two changes cancel in the energy identity
`TauCeti.SmoothTwoForm.IsNondegenerate.integral_floerEnergyDensity_pairOfPantsPerturbation`, as
they must, since the energy itself is unchanged.

The curvature of `k` is the exterior derivative `∂_s k_t - ∂_t k_s` of a one-form on the domain,
the same for every target. The pair-of-pants perturbation is the datum of the sphere with two
moving input ends, at `0` and `1` with scales `1` and `-1`
(`TauCeti.Floer.puncturedSpherePerturbation_eq_pairOfPantsPerturbation`), and these ends satisfy
the separation hypotheses of that datum's energy identity. So the integrated curvature statements
for a manifold target are the two-input-end case of those for spheres with moving input ends
(`TauCeti.SmoothTwoForm.setIntegral_hamiltonianCurvature_puncturedSpherePerturbation_const`,
`TauCeti.SmoothTwoForm.setIntegral_hamiltonianCurvature_puncturedSpherePerturbation_add_const`),
and the vector-space curvature statements are the specializations of the manifold ones to the
constant form `TauCeti.SymplecticForm.constSmooth`.

## References

* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, Section 8.1, on the
  curvature of Hamiltonian perturbations and the energy identity.
-/

public section

open Set Function MeasureTheory TauCeti.ThricePuncturedSphere TauCeti.ThricePuncturedSphere.Puncture
open scoped Manifold

namespace TauCeti

namespace Floer

variable {M : Type*} {c : Puncture → ℝ → ℝ}

/-- The components of the perturbation of target-independent Hamiltonians, as functions of the
domain point alone: their values at any target point `y`. -/
private theorem pairOfPantsPerturbation_const_target_fun (c : Puncture → ℝ → ℝ) (y : M) (v : ℂ) :
    (fun z (x : M) ↦ pairOfPantsPerturbation (fun q t (_ : M) ↦ c q t)
        (Complex.equivRealProdCLM.symm z) x v) =
      fun z _ ↦ pairOfPantsPerturbation (fun q t (_ : M) ↦ c q t)
        (Complex.equivRealProdCLM.symm z) y v := by
  funext z x
  rw [pairOfPantsPerturbation_const_target c _ x y]

/-- The components of the normalized perturbation are the components of the original one plus
those of the perturbation of the normalizing functions, evaluated at any target point `y`. -/
private theorem pairOfPantsPerturbation_add_const_fun (H : Puncture → ℝ → M → ℝ)
    (c : Puncture → ℝ → ℝ) (y : M) (v : ℂ) :
    (fun z x ↦ pairOfPantsPerturbation (fun q t y ↦ H q t y + c q t)
        (Complex.equivRealProdCLM.symm z) x v) =
      fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x v +
        pairOfPantsPerturbation (fun q t (_ : M) ↦ c q t)
          (Complex.equivRealProdCLM.symm z) y v := by
  funext z x
  rw [pairOfPantsPerturbation_add_const, add_apply,
    pairOfPantsPerturbation_const_target c _ x y]

/-- The perturbation of target-independent Hamiltonians on the pair of pants is the datum of the
sphere with two moving input ends, at `0` and `1` with scales `1` and `-1`. -/
private theorem puncturedSpherePerturbation_const_eq_pairOfPantsPerturbation
    (c : Puncture → ℝ → ℝ) :
    puncturedSpherePerturbation ![0, 1] ![1, -1] (fun i t (_ : M) ↦ ![c zero, c one] i t)
        (fun t _ ↦ c inf t) = pairOfPantsPerturbation fun q t (_ : M) ↦ c q t := by
  rw [← puncturedSpherePerturbation_eq_pairOfPantsPerturbation]
  congr 1
  funext i
  fin_cases i <;> rfl

/-- The pair-of-pants perturbation of normalized end Hamiltonians is the datum of the sphere with
two moving input ends, at `0` and `1` with scales `1` and `-1`, of the normalized Hamiltonians. -/
private theorem puncturedSpherePerturbation_add_const_eq_pairOfPantsPerturbation
    (H : Puncture → ℝ → M → ℝ) (c : Puncture → ℝ → ℝ) :
    puncturedSpherePerturbation ![0, 1] ![1, -1]
        (fun i t y ↦ ![H zero, H one] i t y + ![c zero, c one] i t)
        (fun t y ↦ H inf t y + c inf t) = pairOfPantsPerturbation fun q t y ↦ H q t y + c q t := by
  rw [← puncturedSpherePerturbation_eq_pairOfPantsPerturbation]
  congr 1
  funext i
  fin_cases i <;> rfl

/-- The pair of pants is the sphere minus the centers `0` and `1` of its two input ends. -/
private theorem thricePuncturedSphereReal_eq_setOf_forall_ne :
    thricePuncturedSphereReal =
      {z | ∀ i, Complex.equivRealProdCLM.symm z ≠ (![0, 1] : Fin 2 → ℂ) i} := by
  ext z
  simp [Fin.forall_fin_two]

/-- The input ends of the pair of pants have nonzero scales. -/
private theorem pairOfPants_scale_ne_zero : ∀ i, (![1, -1] : Fin 2 → ℂ) i ≠ 0 := by
  simp [Fin.forall_fin_two]

/-- The discs `‖w - c i‖ < ‖a i‖ / 2` of the two input ends of the pair of pants are disjoint. -/
private theorem pairOfPants_sep :
    Pairwise fun i j ↦ ‖(![1, -1] : Fin 2 → ℂ) i‖ / 2 + ‖(![1, -1] : Fin 2 → ℂ) j‖ / 2 ≤
      ‖(![0, 1] : Fin 2 → ℂ) i - ![0, 1] j‖ := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all <;> norm_num

/-- The discs of the two input ends of the pair of pants lie in the disc `‖w‖ ≤ 2 exp (2π)`. -/
private theorem pairOfPants_out :
    ∀ i, ‖(![0, 1] : Fin 2 → ℂ) i‖ + ‖(![1, -1] : Fin 2 → ℂ) i‖ / 2 ≤
      2 * Real.exp (2 * Real.pi) := by
  have := Real.add_one_le_exp (2 * Real.pi)
  have := Real.pi_pos
  simp only [Fin.forall_fin_two]
  constructor <;> simp <;> linarith

end Floer

/-! ### Symplectic vector spaces: the Floer equation and the curvature of a normalization -/

namespace SymplecticForm

open Floer

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {H : Puncture → ℝ → V → ℝ}
  {c : Puncture → ℝ → ℝ}

variable [FiniteDimensional ℝ V]

/-- **Normalizing the end Hamiltonians does not change the Floer equation.** The perturbed
derivative `du - X_K` of any map is the same for the end Hamiltonians `H_q` and
`H_q + c_q`. -/
@[simp]
theorem perturbedFDeriv_pairOfPantsPerturbation_add_const (ω : SymplecticForm V)
    (H : Puncture → ℝ → V → ℝ) (c : Puncture → ℝ → ℝ) (u : ℝ × ℝ → V) :
    ω.perturbedFDeriv
        (fun z x ↦ pairOfPantsPerturbation (fun q t y ↦ H q t y + c q t)
          (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation (fun q t y ↦ H q t y + c q t)
          (Complex.equivRealProdCLM.symm z) x Complex.I) u =
      ω.perturbedFDeriv
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u := by
  rw [pairOfPantsPerturbation_add_const_fun H c 0, pairOfPantsPerturbation_add_const_fun H c 0,
    perturbedFDeriv_add_const]

/-- **Normalizing the end Hamiltonians does not change the energy density.** -/
@[simp]
theorem floerEnergyDensity_pairOfPantsPerturbation_add_const (ω : SymplecticForm V)
    (H : Puncture → ℝ → V → ℝ) (c : Puncture → ℝ → ℝ) (u : ℝ × ℝ → V) :
    ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsPerturbation (fun q t y ↦ H q t y + c q t)
          (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation (fun q t y ↦ H q t y + c q t)
          (Complex.equivRealProdCLM.symm z) x Complex.I) u =
      ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u := by
  rw [pairOfPantsPerturbation_add_const_fun H c 0, pairOfPantsPerturbation_add_const_fun H c 0,
    floerEnergyDensity_add_const]

/-- The curvature of the perturbation of target-independent Hamiltonians does not depend on the
target point. -/
theorem hamiltonianCurvature_pairOfPantsPerturbation_const_target (ω : SymplecticForm V)
    (c : Puncture → ℝ → ℝ) (z : ℝ × ℝ) (x y : V) :
    ω.hamiltonianCurvature
        (fun z x ↦ pairOfPantsPerturbation (fun q t (_ : V) ↦ c q t)
          (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation (fun q t (_ : V) ↦ c q t)
          (Complex.equivRealProdCLM.symm z) x Complex.I) z x =
      ω.hamiltonianCurvature
        (fun z x ↦ pairOfPantsPerturbation (fun q t (_ : V) ↦ c q t)
          (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation (fun q t (_ : V) ↦ c q t)
          (Complex.equivRealProdCLM.symm z) x Complex.I) z y := by
  rw [pairOfPantsPerturbation_const_target_fun c 0, pairOfPantsPerturbation_const_target_fun c 0,
    hamiltonianCurvature_const, hamiltonianCurvature_const]

end SymplecticForm

/-! ### Manifold targets -/

namespace SmoothTwoForm

open Floer

variable {E G M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E G} [TopologicalSpace M] [ChartedSpace G M] [IsManifold I ⊤ M]
  {H : Puncture → ℝ → M → ℝ} {c : Puncture → ℝ → ℝ}

/-- **Normalizing the end Hamiltonians does not change the Floer equation, for a manifold
target.** The perturbed derivative `du - X_K` of any map into `M` is the same for the end
Hamiltonians `H_q` and `H_q + c_q`. -/
@[simp]
theorem perturbedMFDeriv_pairOfPantsPerturbation_add_const (ω : SmoothTwoForm I M)
    (H : Puncture → ℝ → M → ℝ) (c : Puncture → ℝ → ℝ) (u : ℝ × ℝ → M) :
    ω.perturbedMFDeriv
        (fun z x ↦ pairOfPantsPerturbation (fun q t y ↦ H q t y + c q t)
          (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation (fun q t y ↦ H q t y + c q t)
          (Complex.equivRealProdCLM.symm z) x Complex.I) u =
      ω.perturbedMFDeriv
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u := by
  rw [pairOfPantsPerturbation_add_const_fun H c (u 0),
    pairOfPantsPerturbation_add_const_fun H c (u 0), perturbedMFDeriv_add_const]

/-- **Normalizing the end Hamiltonians does not change the energy density, for a manifold
target.** -/
@[simp]
theorem floerEnergyDensity_pairOfPantsPerturbation_add_const (ω : SmoothTwoForm I M)
    (H : Puncture → ℝ → M → ℝ) (c : Puncture → ℝ → ℝ) (u : ℝ × ℝ → M) :
    ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsPerturbation (fun q t y ↦ H q t y + c q t)
          (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation (fun q t y ↦ H q t y + c q t)
          (Complex.equivRealProdCLM.symm z) x Complex.I) u =
      ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u := by
  rw [pairOfPantsPerturbation_add_const_fun H c (u 0),
    pairOfPantsPerturbation_add_const_fun H c (u 0), floerEnergyDensity_add_const]

/-- The curvature of the perturbation of target-independent Hamiltonians does not depend on the
target point, for a manifold target. -/
theorem hamiltonianCurvature_pairOfPantsPerturbation_const_target (ω : SmoothTwoForm I M)
    (c : Puncture → ℝ → ℝ) (z : ℝ × ℝ) (x y : M) :
    ω.hamiltonianCurvature
        (fun z x ↦ pairOfPantsPerturbation (fun q t (_ : M) ↦ c q t)
          (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation (fun q t (_ : M) ↦ c q t)
          (Complex.equivRealProdCLM.symm z) x Complex.I) z x =
      ω.hamiltonianCurvature
        (fun z x ↦ pairOfPantsPerturbation (fun q t (_ : M) ↦ c q t)
          (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation (fun q t (_ : M) ↦ c q t)
          (Complex.equivRealProdCLM.symm z) x Complex.I) z y := by
  rw [pairOfPantsPerturbation_const_target_fun c x, pairOfPantsPerturbation_const_target_fun c x,
    hamiltonianCurvature_const, hamiltonianCurvature_const]

/-- **The curvature of the normalized perturbation, for a manifold target.** At every point of the
pair of pants, the curvature of the perturbation of the end Hamiltonians `H_q + c_q` is the
curvature for `H_q` plus the curvature of the perturbation of the target-independent Hamiltonians
`c_q`. -/
theorem hamiltonianCurvature_pairOfPantsPerturbation_add_const (ω : SmoothTwoForm I M)
    (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q)))
    (hc : ∀ q, Periodic (c q) 1) (hcs : ∀ q, ContDiff ℝ 1 (c q)) {z : ℝ × ℝ}
    (hz : z ∈ thricePuncturedSphereReal) (x : M) :
    ω.hamiltonianCurvature
        (fun z x ↦ pairOfPantsPerturbation (fun q t y ↦ H q t y + c q t)
          (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation (fun q t y ↦ H q t y + c q t)
          (Complex.equivRealProdCLM.symm z) x Complex.I) z x =
      ω.hamiltonianCurvature
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          z x +
        ω.hamiltonianCurvature
          (fun z x ↦ pairOfPantsPerturbation (fun q t (_ : M) ↦ c q t)
            (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation (fun q t (_ : M) ↦ c q t)
            (Complex.equivRealProdCLM.symm z) x Complex.I) z x := by
  have hc' q : Periodic (fun t (_ : M) ↦ c q t) 1 := (hc q).comp (Function.const M)
  have hcs' q : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry fun t (_ : M) ↦ c q t) :=
    (hcs q).contMDiff.comp contMDiff_fst
  rw [pairOfPantsPerturbation_add_const_fun H c x, pairOfPantsPerturbation_add_const_fun H c x,
    hamiltonianCurvature_add_const ω (differentiableAt_pairOfPantsPerturbation_domain hH hHs hz x 1)
      (differentiableAt_pairOfPantsPerturbation_domain hH hHs hz x Complex.I)
      (differentiableAt_pairOfPantsPerturbation_domain hc' hcs' hz x 1)
      (differentiableAt_pairOfPantsPerturbation_domain hc' hcs' hz x Complex.I),
    pairOfPantsPerturbation_const_target_fun c x, pairOfPantsPerturbation_const_target_fun c x]

/-- **The integrated curvature of a normalization, for a manifold target.** For period-one `C¹`
functions `c_q` of time, the curvature of the pair-of-pants perturbation of the target-independent
Hamiltonians `c_q` on `M` integrates over the pair of pants to `∑ q, ±∫₀¹ c_q`, with the sign `+`
on the input ends and `-` on the output end, along any map `u`. This is the case of two input ends
at `0` and `1` of
`SmoothTwoForm.setIntegral_hamiltonianCurvature_puncturedSpherePerturbation_const`. -/
theorem setIntegral_hamiltonianCurvature_pairOfPantsPerturbation_const (ω : SmoothTwoForm I M)
    (hc : ∀ q, Periodic (c q) 1) (hcs : ∀ q, ContDiff ℝ 1 (c q)) (u : ℝ × ℝ → M) :
    ∫ z in thricePuncturedSphereReal, ω.hamiltonianCurvature
        (fun z x ↦ pairOfPantsPerturbation (fun q t (_ : M) ↦ c q t)
          (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation (fun q t (_ : M) ↦ c q t)
          (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z) =
      ∑ q, q.endSign * ∫ t in (0 : ℝ)..1, c q t := by
  have h := ω.setIntegral_hamiltonianCurvature_puncturedSpherePerturbation_const
    (k := ![c zero, c one]) (Fin.forall_fin_two.2 ⟨hc zero, hc one⟩)
    (Fin.forall_fin_two.2 ⟨hcs zero, hcs one⟩) (hc inf) (hcs inf) pairOfPants_scale_ne_zero
    pairOfPants_sep pairOfPants_out u
  rw [puncturedSpherePerturbation_const_eq_pairOfPantsPerturbation,
    ← thricePuncturedSphereReal_eq_setOf_forall_ne] at h
  simp [h, Fin.sum_univ_two, Puncture.sum_univ, sub_eq_add_neg]

/-- **Normalizing the end Hamiltonians shifts the integrated curvature, for a manifold target.**
Along a map whose curvature for `H_q` is integrable on the pair of pants, the integrated curvature
of the perturbation of the end Hamiltonians `H_q + c_q` is the integrated curvature for `H_q` plus
`∑ q, ±∫₀¹ c_q`, with the sign `+` on the input ends and `-` on the output end. This is also the
change of the Hamiltonian terms `∑ q, ±∫₀¹ H_q(t, x_q(t)) dt` of the energy identity
`SmoothTwoForm.IsNondegenerate.integral_floerEnergyDensity_pairOfPantsPerturbation`, so the two
changes cancel and the energy identity for `H_q + c_q` is the one for `H_q`. This is the case of
two input ends at `0` and `1` of
`SmoothTwoForm.setIntegral_hamiltonianCurvature_puncturedSpherePerturbation_add_const`. -/
theorem setIntegral_hamiltonianCurvature_pairOfPantsPerturbation_add_const (ω : SmoothTwoForm I M)
    (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q)))
    (hc : ∀ q, Periodic (c q) 1) (hcs : ∀ q, ContDiff ℝ 1 (c q)) {u : ℝ × ℝ → M}
    (hu : IntegrableOn (fun z ↦ ω.hamiltonianCurvature
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        z (u z)) thricePuncturedSphereReal) :
    ∫ z in thricePuncturedSphereReal, ω.hamiltonianCurvature
        (fun z x ↦ pairOfPantsPerturbation (fun q t y ↦ H q t y + c q t)
          (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation (fun q t y ↦ H q t y + c q t)
          (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z) =
      (∫ z in thricePuncturedSphereReal, ω.hamiltonianCurvature
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          z (u z)) +
        ∑ q, q.endSign * ∫ t in (0 : ℝ)..1, c q t := by
  rw [← puncturedSpherePerturbation_eq_pairOfPantsPerturbation,
    thricePuncturedSphereReal_eq_setOf_forall_ne] at hu
  have h := ω.setIntegral_hamiltonianCurvature_puncturedSpherePerturbation_add_const
    (Fin.forall_fin_two.2 ⟨hH zero, hH one⟩) (Fin.forall_fin_two.2 ⟨hHs zero, hHs one⟩)
    (hH inf) (hHs inf) (k := ![c zero, c one]) (Fin.forall_fin_two.2 ⟨hc zero, hc one⟩)
    (Fin.forall_fin_two.2 ⟨hcs zero, hcs one⟩) (hc inf) (hcs inf) pairOfPants_scale_ne_zero
    pairOfPants_sep pairOfPants_out hu
  rw [puncturedSpherePerturbation_add_const_eq_pairOfPantsPerturbation,
    puncturedSpherePerturbation_eq_pairOfPantsPerturbation,
    ← thricePuncturedSphereReal_eq_setOf_forall_ne] at h
  simp [h, Fin.sum_univ_two, Puncture.sum_univ, sub_eq_add_neg]

end SmoothTwoForm

/-! ### Symplectic vector spaces: the curvature of the normalized perturbation -/

namespace SymplecticForm

open Floer

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {H : Puncture → ℝ → V → ℝ} {c : Puncture → ℝ → ℝ}

/-- **The curvature of the normalized perturbation.** At every point of the pair of pants, the
curvature of the perturbation of the end Hamiltonians `H_q + c_q` is the curvature for `H_q` plus
the curvature of the perturbation of the target-independent Hamiltonians `c_q`. This is the
vector-space case of `SmoothTwoForm.hamiltonianCurvature_pairOfPantsPerturbation_add_const`. -/
theorem hamiltonianCurvature_pairOfPantsPerturbation_add_const (ω : SymplecticForm V)
    (hH : ∀ q, Periodic (H q) 1) (hHs : ∀ q, ContDiff ℝ 1 (uncurry (H q)))
    (hc : ∀ q, Periodic (c q) 1) (hcs : ∀ q, ContDiff ℝ 1 (c q)) {z : ℝ × ℝ}
    (hz : z ∈ thricePuncturedSphereReal) (x : V) :
    ω.hamiltonianCurvature
        (fun z x ↦ pairOfPantsPerturbation (fun q t y ↦ H q t y + c q t)
          (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation (fun q t y ↦ H q t y + c q t)
          (Complex.equivRealProdCLM.symm z) x Complex.I) z x =
      ω.hamiltonianCurvature
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          z x +
        ω.hamiltonianCurvature
          (fun z x ↦ pairOfPantsPerturbation (fun q t (_ : V) ↦ c q t)
            (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation (fun q t (_ : V) ↦ c q t)
            (Complex.equivRealProdCLM.symm z) x Complex.I) z x := by
  have h := ω.constSmooth.hamiltonianCurvature_pairOfPantsPerturbation_add_const hH
    (fun q ↦ contMDiff_prod_modelWithCornersSelf_iff.2 (hHs q).contMDiff) hc hcs hz x
  simp only [hamiltonianCurvature_constSmooth] at h
  exact h

/-- **The integrated curvature of a normalization.** For period-one `C¹` functions `c_q` of time,
the curvature of the pair-of-pants perturbation of the target-independent Hamiltonians `c_q`
integrates over the pair of pants to `∑ q, ±∫₀¹ c_q`, with the sign `+` on the input ends and `-`
on the output end, along any map `u`. This is the vector-space case of
`SmoothTwoForm.setIntegral_hamiltonianCurvature_pairOfPantsPerturbation_const`. -/
theorem setIntegral_hamiltonianCurvature_pairOfPantsPerturbation_const (ω : SymplecticForm V)
    (hc : ∀ q, Periodic (c q) 1) (hcs : ∀ q, ContDiff ℝ 1 (c q)) (u : ℝ × ℝ → V) :
    ∫ z in {z : ℝ × ℝ | Complex.equivRealProdCLM.symm z ≠ 0 ∧
        Complex.equivRealProdCLM.symm z ≠ 1}, ω.hamiltonianCurvature
        (fun z x ↦ pairOfPantsPerturbation (fun q t (_ : V) ↦ c q t)
          (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation (fun q t (_ : V) ↦ c q t)
          (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z) =
      ∑ q, q.endSign * ∫ t in (0 : ℝ)..1, c q t := by
  rw [← thricePuncturedSphereReal_def]
  have h := ω.constSmooth.setIntegral_hamiltonianCurvature_pairOfPantsPerturbation_const hc hcs u
  simp only [hamiltonianCurvature_constSmooth] at h
  exact h

/-- **Normalizing the end Hamiltonians shifts the integrated curvature.** Along a map whose
curvature for `H_q` is integrable on the pair of pants, the integrated curvature of the
perturbation of the end Hamiltonians `H_q + c_q` is the integrated curvature for `H_q` plus
`∑ q, ±∫₀¹ c_q`, with the sign `+` on the input ends and `-` on the output end. This is also the
change of the Hamiltonian terms `∑ q, ±∫₀¹ H_q(t, x_q(t)) dt` of the energy identity
`SymplecticForm.integral_floerEnergyDensity_pairOfPantsPerturbation`, so the two changes cancel
and the energy identity for `H_q + c_q` is the one for `H_q`. This is the vector-space case of
`SmoothTwoForm.setIntegral_hamiltonianCurvature_pairOfPantsPerturbation_add_const`. -/
theorem setIntegral_hamiltonianCurvature_pairOfPantsPerturbation_add_const (ω : SymplecticForm V)
    (hH : ∀ q, Periodic (H q) 1) (hHs : ∀ q, ContDiff ℝ 1 (uncurry (H q)))
    (hc : ∀ q, Periodic (c q) 1) (hcs : ∀ q, ContDiff ℝ 1 (c q)) {u : ℝ × ℝ → V}
    (hu : IntegrableOn (fun z ↦ ω.hamiltonianCurvature
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        z (u z))
      {z : ℝ × ℝ | Complex.equivRealProdCLM.symm z ≠ 0 ∧
        Complex.equivRealProdCLM.symm z ≠ 1}) :
    ∫ z in {z : ℝ × ℝ | Complex.equivRealProdCLM.symm z ≠ 0 ∧
        Complex.equivRealProdCLM.symm z ≠ 1}, ω.hamiltonianCurvature
        (fun z x ↦ pairOfPantsPerturbation (fun q t y ↦ H q t y + c q t)
          (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation (fun q t y ↦ H q t y + c q t)
          (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z) =
      (∫ z in {z : ℝ × ℝ | Complex.equivRealProdCLM.symm z ≠ 0 ∧
          Complex.equivRealProdCLM.symm z ≠ 1}, ω.hamiltonianCurvature
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          z (u z)) +
        ∑ q, q.endSign * ∫ t in (0 : ℝ)..1, c q t := by
  rw [← thricePuncturedSphereReal_def] at hu ⊢
  have h := ω.constSmooth.setIntegral_hamiltonianCurvature_pairOfPantsPerturbation_add_const hH
    (fun q ↦ contMDiff_prod_modelWithCornersSelf_iff.2 (hHs q).contMDiff) hc hcs
    (by simpa only [hamiltonianCurvature_constSmooth] using hu)
  simp only [hamiltonianCurvature_constSmooth] at h
  exact h

end SymplecticForm

end TauCeti
