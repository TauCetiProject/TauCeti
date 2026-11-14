/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Curvature
import TauCeti.Geometry.Manifold.ContMDiff.Prod
import TauCeti.Geometry.Symplectic.Complex.Line
import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Energy.Asymptotic

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
the same for every target. Its integral is computed once, for a symplectic vector space, by the
vector-space energy identity along a constant map
(`TauCeti.SymplecticForm.setIntegral_hamiltonianCurvature_pairOfPantsPerturbation_const`). The
vector-space curvature statements are the specializations of the manifold ones to the constant
form `TauCeti.SymplecticForm.constSmooth`.

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

/-- Periodic normalizations `c_q` give period-one target-independent Hamiltonians. -/
private theorem periodic_const_target (hc : ∀ q, Periodic (c q) 1) (q : Puncture) :
    Periodic (fun t (_ : M) ↦ c q t) 1 :=
  fun t ↦ funext fun _ ↦ hc q t

/-- Continuous periodic normalizations `c_q` are bounded. -/
private theorem exists_forall_abs_le (hc : ∀ q, Periodic (c q) 1)
    (hcs : ∀ q, ContDiff ℝ 1 (c q)) : ∃ B : Puncture → ℝ, ∀ q t, |c q t| ≤ B q := by
  have hb : ∀ q, ∃ B, ∀ t, |c q t| ≤ B := fun q ↦ by
    obtain ⟨B, hB⟩ := isBounded_iff_forall_norm_le.1
      ((hc q).isBounded_of_continuous one_ne_zero (hcs q).continuous)
    exact ⟨B, fun t ↦ hB _ (mem_range_self t)⟩
  choose B hB using hb
  exact ⟨B, hB⟩

end Floer

/-! ### Symplectic vector spaces: the Floer equation and the curvature of a normalization -/

namespace SymplecticForm

open Floer

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {H : Puncture → ℝ → V → ℝ}
  {c : Puncture → ℝ → ℝ}

/-- `C¹` normalizations `c_q` give `C¹` target-independent Hamiltonians. -/
private theorem contDiff_uncurry_const_target (hcs : ∀ q, ContDiff ℝ 1 (c q)) (q : Puncture) :
    ContDiff ℝ 1 (uncurry fun t (_ : V) ↦ c q t) :=
  (hcs q).comp contDiff_fst

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

/-- **The integrated curvature of a normalization.** For period-one `C¹` functions `c_q` of time,
the curvature of the pair-of-pants perturbation of the target-independent Hamiltonians `c_q`
integrates over the pair of pants to `∑ q, ±∫₀¹ c_q`, with the sign `+` on the input ends and `-`
on the output end, along any map `u`. -/
theorem setIntegral_hamiltonianCurvature_pairOfPantsPerturbation_const (ω : SymplecticForm V)
    (hc : ∀ q, Periodic (c q) 1) (hcs : ∀ q, ContDiff ℝ 1 (c q)) (u : ℝ × ℝ → V) :
    ∫ z in {z : ℝ × ℝ | Complex.equivRealProdCLM.symm z ≠ 0 ∧
        Complex.equivRealProdCLM.symm z ≠ 1}, ω.hamiltonianCurvature
        (fun z x ↦ pairOfPantsPerturbation (fun q t (_ : V) ↦ c q t)
          (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation (fun q t (_ : V) ↦ c q t)
          (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z) =
      ∑ q, q.endSign * ∫ t in (0 : ℝ)..1, c q t := by
  obtain ⟨B, hB⟩ := exists_forall_abs_le hc hcs
  -- Along the constant map `0`, the energy density and the area density vanish.
  have hE : ω.floerEnergyDensity
      (fun z x ↦ pairOfPantsPerturbation (fun q t (_ : V) ↦ c q t)
        (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ pairOfPantsPerturbation (fun q t (_ : V) ↦ c q t)
        (Complex.equivRealProdCLM.symm z) x Complex.I) (fun _ ↦ (0 : V)) = 0 := by
    funext z
    rw [pairOfPantsPerturbation_const_target_fun c 0, pairOfPantsPerturbation_const_target_fun c 0,
      floerEnergyDensity_def, perturbedFDeriv_const]
    simp
  have hA : (fun z : ℝ × ℝ ↦ ω (fderiv ℝ (fun _ ↦ (0 : V)) z stdComplexLineReal)
      (fderiv ℝ (fun _ ↦ (0 : V)) z stdComplexLineImag)) = 0 := by
    funext z
    simp
  -- The energy identity for the constant map `0` leaves only the curvature and the end terms.
  have h := ω.integral_floerEnergyDensity_pairOfPantsPerturbation (periodic_const_target hc)
    (contDiff_uncurry_const_target hcs) (B := B) (fun q t _ ↦ hB q t) (u := fun _ ↦ (0 : V))
    contDiffOn_const (x := fun _ _ ↦ 0) (fun _ _ ↦ tendsto_const_nhds)
    (by rw [hE]; exact integrableOn_zero) (by rw [hA]; exact integrableOn_zero)
  rw [hE, hA] at h
  simp only [integral_zero', zero_add] at h
  -- The curvature does not depend on the target point, so it is the same along `u` and `0`.
  have hu : (fun z ↦ ω.hamiltonianCurvature
      (fun z x ↦ pairOfPantsPerturbation (fun q t (_ : V) ↦ c q t)
        (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ pairOfPantsPerturbation (fun q t (_ : V) ↦ c q t)
        (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z)) =
      fun z ↦ ω.hamiltonianCurvature
        (fun z x ↦ pairOfPantsPerturbation (fun q t (_ : V) ↦ c q t)
          (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation (fun q t (_ : V) ↦ c q t)
          (Complex.equivRealProdCLM.symm z) x Complex.I) z 0 :=
    funext fun z ↦ ω.hamiltonianCurvature_pairOfPantsPerturbation_const_target c z (u z) 0
  rw [hu]
  linarith

end SymplecticForm

/-! ### Manifold targets -/

namespace SmoothTwoForm

open Floer

variable {E G M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E G} [TopologicalSpace M] [ChartedSpace G M] [IsManifold I ⊤ M]
  {H : Puncture → ℝ → M → ℝ} {c : Puncture → ℝ → ℝ}

omit [IsManifold I ⊤ M] in
/-- `C¹` normalizations `c_q` give `C¹` target-independent Hamiltonians on `M`. -/
private theorem contMDiff_uncurry_const_target (hcs : ∀ q, ContDiff ℝ 1 (c q)) (q : Puncture) :
    ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry fun t (_ : M) ↦ c q t) :=
  (hcs q).contMDiff.comp contMDiff_fst

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
  have hc' := periodic_const_target (M := M) hc
  have hcs' := contMDiff_uncurry_const_target (I := I) (M := M) hcs
  rw [pairOfPantsPerturbation_add_const_fun H c x, pairOfPantsPerturbation_add_const_fun H c x,
    hamiltonianCurvature_add_const ω (differentiableAt_pairOfPantsPerturbation_domain hH hHs hz x 1)
      (differentiableAt_pairOfPantsPerturbation_domain hH hHs hz x Complex.I)
      (differentiableAt_pairOfPantsPerturbation_domain hc' hcs' hz x 1)
      (differentiableAt_pairOfPantsPerturbation_domain hc' hcs' hz x Complex.I),
    pairOfPantsPerturbation_const_target_fun c x, pairOfPantsPerturbation_const_target_fun c x]

/-- **The integrated curvature of a normalization, for a manifold target.** For period-one `C¹`
functions `c_q` of time, the curvature of the pair-of-pants perturbation of the target-independent
Hamiltonians `c_q` on `M` integrates over the pair of pants to `∑ q, ±∫₀¹ c_q`, with the sign `+`
on the input ends and `-` on the output end, along any map `u`. -/
theorem setIntegral_hamiltonianCurvature_pairOfPantsPerturbation_const (ω : SmoothTwoForm I M)
    (hc : ∀ q, Periodic (c q) 1) (hcs : ∀ q, ContDiff ℝ 1 (c q)) (u : ℝ × ℝ → M) :
    ∫ z in thricePuncturedSphereReal, ω.hamiltonianCurvature
        (fun z x ↦ pairOfPantsPerturbation (fun q t (_ : M) ↦ c q t)
          (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation (fun q t (_ : M) ↦ c q t)
          (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z) =
      ∑ q, q.endSign * ∫ t in (0 : ℝ)..1, c q t := by
  -- The curvature of a target-independent datum is the exterior derivative of a one-form on the
  -- domain, whatever the target; on `ℂ` with its standard symplectic form it was computed above.
  have h (z : ℝ × ℝ) : ω.hamiltonianCurvature
      (fun z x ↦ pairOfPantsPerturbation (fun q t (_ : M) ↦ c q t)
        (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ pairOfPantsPerturbation (fun q t (_ : M) ↦ c q t)
        (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z) =
      stdComplexSymplecticForm.hamiltonianCurvature
        (fun z x ↦ pairOfPantsPerturbation (fun q t (_ : ℂ) ↦ c q t)
          (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation (fun q t (_ : ℂ) ↦ c q t)
          (Complex.equivRealProdCLM.symm z) x Complex.I) z 0 := by
    rw [pairOfPantsPerturbation_const_target_fun c (u z),
      pairOfPantsPerturbation_const_target_fun c (u z), hamiltonianCurvature_const,
      pairOfPantsPerturbation_const_target_fun c (0 : ℂ),
      pairOfPantsPerturbation_const_target_fun c (0 : ℂ),
      SymplecticForm.hamiltonianCurvature_const]
    -- Both sides are the same exterior derivative of a one-form on the domain.
    simp only [pairOfPantsPerturbation_def]
  rw [integral_congr_ae (Filter.Eventually.of_forall h), thricePuncturedSphereReal_def]
  exact stdComplexSymplecticForm.setIntegral_hamiltonianCurvature_pairOfPantsPerturbation_const
    hc hcs fun _ ↦ 0

/-- **Normalizing the end Hamiltonians shifts the integrated curvature, for a manifold target.**
Along a map whose curvature for `H_q` is integrable on the pair of pants, the integrated curvature
of the perturbation of the end Hamiltonians `H_q + c_q` is the integrated curvature for `H_q` plus
`∑ q, ±∫₀¹ c_q`, with the sign `+` on the input ends and `-` on the output end. This is also the
change of the Hamiltonian terms `∑ q, ±∫₀¹ H_q(t, x_q(t)) dt` of the energy identity
`SmoothTwoForm.IsNondegenerate.integral_floerEnergyDensity_pairOfPantsPerturbation`, so the two
changes cancel and the energy identity for `H_q + c_q` is the one for `H_q`. -/
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
  -- The curvature of the normalization does not depend on the target point, so it is integrable
  -- along `u` because it is along a constant map.
  have hk := (ω.integrableOn_hamiltonianCurvature_pairOfPantsPerturbation
    (periodic_const_target hc) (contMDiff_uncurry_const_target hcs)
    (u := fun _ ↦ u 0) continuousOn_const).congr_fun
    (fun z _ ↦ ω.hamiltonianCurvature_pairOfPantsPerturbation_const_target c z (u 0) (u z))
    isOpen_thricePuncturedSphereReal.measurableSet
  rw [← ω.setIntegral_hamiltonianCurvature_pairOfPantsPerturbation_const hc hcs u,
    ← integral_add hu hk]
  exact setIntegral_congr_fun isOpen_thricePuncturedSphereReal.measurableSet fun z hz ↦
    ω.hamiltonianCurvature_pairOfPantsPerturbation_add_const hH hHs hc hcs hz (u z)

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
