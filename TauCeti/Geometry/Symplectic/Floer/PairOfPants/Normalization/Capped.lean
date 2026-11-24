/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Energy.Capped
import TauCeti.Geometry.Manifold.ContMDiff.Prod
import TauCeti.Geometry.Symplectic.Complex.Line

/-!
# Normalizing the end Hamiltonians of the capped comparison family

The comparison between the pair-of-pants product and the quantum product caps the three ends of
the pair of pants `S = ℂ ∖ {0, 1}` with Piunikhin–Salamon–Schwarz planes, and carries the
perturbation `K = TauCeti.Floer.cappedPerturbation a L H` built from end Hamiltonians `H_q`, and
the comparison family `K_R = TauCeti.Floer.cappedComparisonPerturbation H R`. A Hamiltonian is
determined by its Hamiltonian vector field only up to a function of time: `H_q(t, x)` and
`H_q(t, x) + c_q(t)` generate the same flow. This file shows how the energy identity of the capped
three-pole sphere,

`E(u) = ∫ u^* ω - ∫ R_K(u)`

(`TauCeti.SmoothTwoForm.IsNondegenerate.integral_floerEnergyDensity_cappedPerturbation`), behaves
under such a change of normalization, for a manifold target with a two-form and for a symplectic
vector space target.

The capped perturbation is additive in the end Hamiltonians, so normalizing by `c` adds to it the
capped perturbation `k` of the target-independent Hamiltonians `c_q`
(`TauCeti.Floer.cappedPerturbation_add_const`), which has no Hamiltonian vector field.
Consequently:

* the perturbed derivative `du - X_K`, hence the Floer equation, and the Floer energy density are
  unchanged (`TauCeti.SmoothTwoForm.perturbedMFDeriv_cappedPerturbation_add_const`,
  `TauCeti.SmoothTwoForm.floerEnergyDensity_cappedPerturbation_add_const`);
* the curvature changes pointwise by the curvature of `k`, which does not depend on the target
  point (`TauCeti.SmoothTwoForm.hamiltonianCurvature_cappedPerturbation_add_const`);
* the curvature of `k` integrates to zero over the plane
  (`TauCeti.SmoothTwoForm.integral_hamiltonianCurvature_cappedPerturbation_const`).

So, unlike on the pair of pants, the integrated curvature itself does not change
(`TauCeti.SmoothTwoForm.integral_hamiltonianCurvature_cappedPerturbation_add_const`, and
`TauCeti.SmoothTwoForm.integral_hamiltonianCurvature_cappedComparisonPerturbation_add_const` along
the comparison family). On the pair of pants a normalization shifts the integrated curvature by
`∑ q, ±∫₀¹ c_q`, which the end actions absorb
(`TauCeti.SmoothTwoForm.setIntegral_hamiltonianCurvature_pairOfPantsPerturbation_add_const`). Here
the three ends are capped, the domain is a closed sphere and there are no end actions: the
curvature of `k` is the exterior derivative `∂_s k_t - ∂_t k_s` of a one-form on the plane with
compact support, and its integral vanishes. It is computed once, for a symplectic vector space,
by the energy identity along a constant map.

Since both sides of the energy identity are unchanged, the uniform energy bound of the comparison
family holds with any normalization of the end Hamiltonians: if `|H_q(t, x) - c_q(t)| ≤ B_q` for
period-one `C¹` functions `c_q`, the energy of a `C¹` map for every member `K_R`, `R ≥ 0`, of the
family differs from its symplectic area by at most `2 (B₀ + B₁ + B_∞)`
(in the namespace `TauCeti.SmoothTwoForm`,
`IsNondegenerate.abs_integral_floerEnergyDensity_cappedComparisonPerturbation_sub_le_of_abs_sub_le`,
and for a vector space target, in the namespace `TauCeti.SymplecticForm`,
`abs_integral_floerEnergyDensity_cappedComparisonPerturbation_sub_le_of_abs_sub_le`).
For instance `c_q(t) = H_q(t, x₀)` for a point `x₀` bounds the energy defect by the oscillations
`sup_x H_q(t, x) - inf_x H_q(t, x)` of the end Hamiltonians, which do not depend on their
normalization, rather than by their sizes `sup |H_q|`, which do.

## References

* S. Piunikhin, D. Salamon and M. Schwarz, *Symplectic Floer–Donaldson theory and quantum
  cohomology*, in *Contact and symplectic geometry*, Publ. Newton Inst. 8 (1996), 171–200, on
  the comparison of the pair-of-pants product with the quantum product.
* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, Section 8.1, on the
  curvature of Hamiltonian perturbations and the energy identity.
-/

public section

open Set Function MeasureTheory TauCeti.ThricePuncturedSphere
open scoped Manifold

namespace TauCeti

namespace Floer

variable {M : Type*} {a L : ℝ}

/-- The components of the capped perturbation of target-independent Hamiltonians, as functions of
the domain point alone: their values at any target point `y`, of any target type. -/
private theorem cappedPerturbation_const_target_fun {N : Type*} (c : Puncture → ℝ → ℝ) (y : N)
    (v : ℂ) :
    (fun z (x : M) ↦ cappedPerturbation a L (fun q t (_ : M) ↦ c q t)
        (Complex.equivRealProdCLM.symm z) x v) =
      fun z _ ↦ cappedPerturbation a L (fun q t (_ : N) ↦ c q t)
        (Complex.equivRealProdCLM.symm z) y v := by
  funext z x
  rw [cappedPerturbation_const_target a L c _ x y]

/-- The components of the normalized capped perturbation are the components of the original one
plus those of the capped perturbation of the normalizing functions, evaluated at any target
point `y`. -/
private theorem cappedPerturbation_add_const_fun (H : Puncture → ℝ → M → ℝ)
    (c : Puncture → ℝ → ℝ) (y : M) (v : ℂ) :
    (fun z x ↦ cappedPerturbation a L (fun q t y ↦ H q t y + c q t)
        (Complex.equivRealProdCLM.symm z) x v) =
      fun z x ↦ cappedPerturbation a L H (Complex.equivRealProdCLM.symm z) x v +
        cappedPerturbation a L (fun q t (_ : M) ↦ c q t)
          (Complex.equivRealProdCLM.symm z) y v := by
  funext z x
  rw [cappedPerturbation_add_const, add_apply,
    cappedPerturbation_const_target a L c _ x y]

/-- Normalizing period-one end Hamiltonians by period-one functions of time leaves them of period
one. -/
private theorem periodic_sub_const {H : Puncture → ℝ → M → ℝ} {c : Puncture → ℝ → ℝ}
    (hH : ∀ q, Periodic (H q) 1) (hc : ∀ q, Periodic (c q) 1) (q : Puncture) :
    Periodic (fun t x ↦ H q t x - c q t) 1 := fun t ↦ funext fun x ↦
  congrArg₂ (· - ·) (congrFun (hH q t) x) (hc q t)

/-- Periodic normalizations `c_q` give period-one target-independent Hamiltonians. -/
private theorem periodic_const_target {c : Puncture → ℝ → ℝ} (hc : ∀ q, Periodic (c q) 1)
    (q : Puncture) : Periodic (fun t (_ : M) ↦ c q t) 1 :=
  fun t ↦ funext fun _ ↦ hc q t

/-- End Hamiltonians are their normalization by `c` plus `c`. -/
private theorem sub_const_add_const (H : Puncture → ℝ → M → ℝ) (c : Puncture → ℝ → ℝ) :
    (fun q t x ↦ H q t x - c q t + c q t) = H :=
  funext fun _ ↦ funext fun _ ↦ funext fun _ ↦ sub_add_cancel _ _

end Floer

/-! ### Symplectic vector spaces -/

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
derivative `du - X_K` of any map is the same for the capped perturbations of the end Hamiltonians
`H_q` and `H_q + c_q`. -/
@[simp]
theorem perturbedFDeriv_cappedPerturbation_add_const (ω : SymplecticForm V) (a L : ℝ)
    (H : Puncture → ℝ → V → ℝ) (c : Puncture → ℝ → ℝ) (u : ℝ × ℝ → V) :
    ω.perturbedFDeriv
        (fun z x ↦ cappedPerturbation a L (fun q t y ↦ H q t y + c q t)
          (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ cappedPerturbation a L (fun q t y ↦ H q t y + c q t)
          (Complex.equivRealProdCLM.symm z) x Complex.I) u =
      ω.perturbedFDeriv
        (fun z x ↦ cappedPerturbation a L H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ cappedPerturbation a L H (Complex.equivRealProdCLM.symm z) x Complex.I) u := by
  rw [cappedPerturbation_add_const_fun H c 0, cappedPerturbation_add_const_fun H c 0,
    perturbedFDeriv_add_const]

/-- **Normalizing the end Hamiltonians does not change the energy density** of the capped
perturbation. -/
@[simp]
theorem floerEnergyDensity_cappedPerturbation_add_const (ω : SymplecticForm V) (a L : ℝ)
    (H : Puncture → ℝ → V → ℝ) (c : Puncture → ℝ → ℝ) (u : ℝ × ℝ → V) :
    ω.floerEnergyDensity
        (fun z x ↦ cappedPerturbation a L (fun q t y ↦ H q t y + c q t)
          (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ cappedPerturbation a L (fun q t y ↦ H q t y + c q t)
          (Complex.equivRealProdCLM.symm z) x Complex.I) u =
      ω.floerEnergyDensity
        (fun z x ↦ cappedPerturbation a L H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ cappedPerturbation a L H (Complex.equivRealProdCLM.symm z) x Complex.I) u := by
  rw [cappedPerturbation_add_const_fun H c 0, cappedPerturbation_add_const_fun H c 0,
    floerEnergyDensity_add_const]

/-- Normalizing the end Hamiltonians does not change the energy density of the comparison
family. -/
private theorem floerEnergyDensity_cappedComparisonPerturbation_add_const (ω : SymplecticForm V)
    (H : Puncture → ℝ → V → ℝ) (c : Puncture → ℝ → ℝ) (R : ℝ) (u : ℝ × ℝ → V) :
    ω.floerEnergyDensity
        (fun z x ↦ cappedComparisonPerturbation (fun q t y ↦ H q t y + c q t) R
          (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ cappedComparisonPerturbation (fun q t y ↦ H q t y + c q t) R
          (Complex.equivRealProdCLM.symm z) x Complex.I) u =
      ω.floerEnergyDensity
        (fun z x ↦ cappedComparisonPerturbation H R (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ cappedComparisonPerturbation H R (Complex.equivRealProdCLM.symm z) x Complex.I)
        u := by
  simp only [cappedComparisonPerturbation_def, floerEnergyDensity_cappedPerturbation_add_const]

/-- The curvature of the capped perturbation of target-independent Hamiltonians does not depend on
the target point. -/
theorem hamiltonianCurvature_cappedPerturbation_const_target (ω : SymplecticForm V) (a L : ℝ)
    (c : Puncture → ℝ → ℝ) (z : ℝ × ℝ) (x y : V) :
    ω.hamiltonianCurvature
        (fun z x ↦ cappedPerturbation a L (fun q t (_ : V) ↦ c q t)
          (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ cappedPerturbation a L (fun q t (_ : V) ↦ c q t)
          (Complex.equivRealProdCLM.symm z) x Complex.I) z x =
      ω.hamiltonianCurvature
        (fun z x ↦ cappedPerturbation a L (fun q t (_ : V) ↦ c q t)
          (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ cappedPerturbation a L (fun q t (_ : V) ↦ c q t)
          (Complex.equivRealProdCLM.symm z) x Complex.I) z y := by
  rw [cappedPerturbation_const_target_fun c (0 : V), cappedPerturbation_const_target_fun c (0 : V),
    hamiltonianCurvature_const, hamiltonianCurvature_const]

/-- For `C¹` functions `c_q` of time, the curvature of the capped perturbation of the
target-independent Hamiltonians `c_q` is integrable along any map `u`: it is continuous, with
compact support. -/
theorem integrable_hamiltonianCurvature_cappedPerturbation_const (ω : SymplecticForm V)
    (hc : ∀ q, Periodic (c q) 1) (hcs : ∀ q, ContDiff ℝ 1 (c q)) (a L : ℝ) (u : ℝ × ℝ → V) :
    Integrable fun z ↦ ω.hamiltonianCurvature
        (fun z x ↦ cappedPerturbation a L (fun q t (_ : V) ↦ c q t)
          (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ cappedPerturbation a L (fun q t (_ : V) ↦ c q t)
          (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z) := by
  -- The components of the datum at the target point `0`, as functions of the domain point.
  have hk (v : ℂ) : ContDiff ℝ 1 fun z ↦ cappedPerturbation a L (fun q t (_ : V) ↦ c q t)
      (Complex.equivRealProdCLM.symm z) 0 v :=
    (contDiff_cappedPerturbation_apply (periodic_const_target hc)
      (contDiff_uncurry_const_target hcs) a L v).comp (contDiff_id.prodMk contDiff_const)
  have hks (v : ℂ) (w : ℝ × ℝ) : HasCompactSupport fun z ↦ fderiv ℝ (fun z ↦ cappedPerturbation a L
      (fun q t (_ : V) ↦ c q t) (Complex.equivRealProdCLM.symm z) 0 v) z w :=
    (hasCompactSupport_cappedPerturbation_apply a L (fun _ ↦ (0 : V)) v).fderiv_apply ℝ w
  have hkc (v : ℂ) (w : ℝ × ℝ) : Continuous fun z ↦ fderiv ℝ (fun z ↦ cappedPerturbation a L
      (fun q t (_ : V) ↦ c q t) (Complex.equivRealProdCLM.symm z) 0 v) z w :=
    ((hk v).continuous_fderiv one_ne_zero).clm_apply continuous_const
  rw [cappedPerturbation_const_target_fun c (0 : V), cappedPerturbation_const_target_fun c (0 : V)]
  simp only [hamiltonianCurvature_const]
  exact ((hkc _ _).sub (hkc _ _)).integrable_of_hasCompactSupport ((hks _ _).sub (hks _ _))

/-- **The curvature of a normalization integrates to zero.** For period-one `C¹` functions `c_q`
of time, the curvature of the capped perturbation of the target-independent Hamiltonians `c_q`
integrates to zero over the plane, along any map `u`: it is the exterior derivative of a one-form
with compact support. -/
theorem integral_hamiltonianCurvature_cappedPerturbation_const (ω : SymplecticForm V)
    (hc : ∀ q, Periodic (c q) 1) (hcs : ∀ q, ContDiff ℝ 1 (c q))
    (a L : ℝ) (u : ℝ × ℝ → V) :
    ∫ z, ω.hamiltonianCurvature
        (fun z x ↦ cappedPerturbation a L (fun q t (_ : V) ↦ c q t)
          (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ cappedPerturbation a L (fun q t (_ : V) ↦ c q t)
          (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z) = 0 := by
  -- Along the constant map `0`, the energy density and the area density vanish.
  have hE : ω.floerEnergyDensity
      (fun z x ↦ cappedPerturbation a L (fun q t (_ : V) ↦ c q t)
        (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ cappedPerturbation a L (fun q t (_ : V) ↦ c q t)
        (Complex.equivRealProdCLM.symm z) x Complex.I) (fun _ ↦ (0 : V)) = 0 := by
    funext z
    rw [cappedPerturbation_const_target_fun c (0 : V),
      cappedPerturbation_const_target_fun c (0 : V), floerEnergyDensity_def, perturbedFDeriv_const]
    simp
  -- The energy identity for the constant map `0` leaves only the curvature.
  have h := ω.setIntegral_floerEnergyDensity_cappedPerturbation
    (periodic_const_target hc) (contDiff_uncurry_const_target hcs) a L isOpen_univ
    (subset_univ _) contDiffOn_const MeasurableSet.univ (subset_univ _)
    (by rw [hE]; exact integrableOn_zero)
  rw [hE] at h
  simp only [Measure.restrict_univ, Pi.zero_apply, integral_zero, fderiv_fun_const, zero_apply,
    map_zero, zero_sub, zero_eq_neg] at h
  -- The curvature does not depend on the target point, so it is the same along `u` and `0`.
  have hu : (fun z ↦ ω.hamiltonianCurvature
      (fun z x ↦ cappedPerturbation a L (fun q t (_ : V) ↦ c q t)
        (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ cappedPerturbation a L (fun q t (_ : V) ↦ c q t)
        (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z)) =
      fun z ↦ ω.hamiltonianCurvature
        (fun z x ↦ cappedPerturbation a L (fun q t (_ : V) ↦ c q t)
          (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ cappedPerturbation a L (fun q t (_ : V) ↦ c q t)
          (Complex.equivRealProdCLM.symm z) x Complex.I) z 0 :=
    funext fun z ↦ ω.hamiltonianCurvature_cappedPerturbation_const_target a L c z (u z) 0
  rw [hu]
  exact h

end SymplecticForm

/-! ### Manifold targets -/

namespace SmoothTwoForm

open Floer

variable {E G M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E G} [TopologicalSpace M] [ChartedSpace G M] [IsManifold I ⊤ M]
  {ω : SmoothTwoForm I M} {H : Puncture → ℝ → M → ℝ} {c : Puncture → ℝ → ℝ}

omit [IsManifold I ⊤ M] in
/-- `C¹` normalizations `c_q` give `C¹` target-independent Hamiltonians on `M`. -/
private theorem contMDiff_uncurry_const_target (hcs : ∀ q, ContDiff ℝ 1 (c q)) (q : Puncture) :
    ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry fun t (_ : M) ↦ c q t) :=
  (hcs q).contMDiff.comp contMDiff_fst

omit [IsManifold I ⊤ M] in
/-- A component of the capped perturbation is differentiable in the point of the plane chart. -/
private theorem differentiableAt_cappedPerturbation_domain (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q))) (a L : ℝ) (z : ℝ × ℝ)
    (x : M) (v : ℂ) :
    DifferentiableAt ℝ (fun w ↦ cappedPerturbation a L H (Complex.equivRealProdCLM.symm w) x v)
      z :=
  (differentiable_cappedPerturbation_domain hH hHs a L x v).differentiableAt.comp z
    Complex.equivRealProdCLM.symm.differentiableAt

/-- **Normalizing the end Hamiltonians does not change the Floer equation, for a manifold
target.** The perturbed derivative `du - X_K` of any map into `M` is the same for the capped
perturbations of the end Hamiltonians `H_q` and `H_q + c_q`. -/
@[simp]
theorem perturbedMFDeriv_cappedPerturbation_add_const (ω : SmoothTwoForm I M) (a L : ℝ)
    (H : Puncture → ℝ → M → ℝ) (c : Puncture → ℝ → ℝ) (u : ℝ × ℝ → M) :
    ω.perturbedMFDeriv
        (fun z x ↦ cappedPerturbation a L (fun q t y ↦ H q t y + c q t)
          (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ cappedPerturbation a L (fun q t y ↦ H q t y + c q t)
          (Complex.equivRealProdCLM.symm z) x Complex.I) u =
      ω.perturbedMFDeriv
        (fun z x ↦ cappedPerturbation a L H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ cappedPerturbation a L H (Complex.equivRealProdCLM.symm z) x Complex.I) u := by
  rw [cappedPerturbation_add_const_fun H c (u 0), cappedPerturbation_add_const_fun H c (u 0),
    perturbedMFDeriv_add_const]

/-- **Normalizing the end Hamiltonians does not change the energy density** of the capped
perturbation, for a manifold target. -/
@[simp]
theorem floerEnergyDensity_cappedPerturbation_add_const (ω : SmoothTwoForm I M) (a L : ℝ)
    (H : Puncture → ℝ → M → ℝ) (c : Puncture → ℝ → ℝ) (u : ℝ × ℝ → M) :
    ω.floerEnergyDensity
        (fun z x ↦ cappedPerturbation a L (fun q t y ↦ H q t y + c q t)
          (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ cappedPerturbation a L (fun q t y ↦ H q t y + c q t)
          (Complex.equivRealProdCLM.symm z) x Complex.I) u =
      ω.floerEnergyDensity
        (fun z x ↦ cappedPerturbation a L H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ cappedPerturbation a L H (Complex.equivRealProdCLM.symm z) x Complex.I) u := by
  rw [cappedPerturbation_add_const_fun H c (u 0), cappedPerturbation_add_const_fun H c (u 0),
    floerEnergyDensity_add_const]

/-- Normalizing the end Hamiltonians does not change the energy density of the comparison family,
for a manifold target. -/
private theorem floerEnergyDensity_cappedComparisonPerturbation_add_const (ω : SmoothTwoForm I M)
    (H : Puncture → ℝ → M → ℝ) (c : Puncture → ℝ → ℝ) (R : ℝ) (u : ℝ × ℝ → M) :
    ω.floerEnergyDensity
        (fun z x ↦ cappedComparisonPerturbation (fun q t y ↦ H q t y + c q t) R
          (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ cappedComparisonPerturbation (fun q t y ↦ H q t y + c q t) R
          (Complex.equivRealProdCLM.symm z) x Complex.I) u =
      ω.floerEnergyDensity
        (fun z x ↦ cappedComparisonPerturbation H R (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ cappedComparisonPerturbation H R (Complex.equivRealProdCLM.symm z) x Complex.I)
        u := by
  simp only [cappedComparisonPerturbation_def, floerEnergyDensity_cappedPerturbation_add_const]

/-- The curvature of the capped perturbation of target-independent Hamiltonians does not depend on
the target point, for a manifold target. -/
theorem hamiltonianCurvature_cappedPerturbation_const_target (ω : SmoothTwoForm I M) (a L : ℝ)
    (c : Puncture → ℝ → ℝ) (z : ℝ × ℝ) (x y : M) :
    ω.hamiltonianCurvature
        (fun z x ↦ cappedPerturbation a L (fun q t (_ : M) ↦ c q t)
          (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ cappedPerturbation a L (fun q t (_ : M) ↦ c q t)
          (Complex.equivRealProdCLM.symm z) x Complex.I) z x =
      ω.hamiltonianCurvature
        (fun z x ↦ cappedPerturbation a L (fun q t (_ : M) ↦ c q t)
          (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ cappedPerturbation a L (fun q t (_ : M) ↦ c q t)
          (Complex.equivRealProdCLM.symm z) x Complex.I) z y := by
  rw [cappedPerturbation_const_target_fun c x, cappedPerturbation_const_target_fun c x,
    hamiltonianCurvature_const, hamiltonianCurvature_const]

/-- **The curvature of the normalized capped perturbation, for a manifold target.** At every point
of the plane, the curvature of the capped perturbation of the end Hamiltonians `H_q + c_q` is the
curvature for `H_q` plus the curvature of the capped perturbation of the target-independent
Hamiltonians `c_q`. -/
theorem hamiltonianCurvature_cappedPerturbation_add_const (ω : SmoothTwoForm I M)
    (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q)))
    (hc : ∀ q, Periodic (c q) 1) (hcs : ∀ q, ContDiff ℝ 1 (c q)) (a L : ℝ) (z : ℝ × ℝ) (x : M) :
    ω.hamiltonianCurvature
        (fun z x ↦ cappedPerturbation a L (fun q t y ↦ H q t y + c q t)
          (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ cappedPerturbation a L (fun q t y ↦ H q t y + c q t)
          (Complex.equivRealProdCLM.symm z) x Complex.I) z x =
      ω.hamiltonianCurvature
          (fun z x ↦ cappedPerturbation a L H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ cappedPerturbation a L H (Complex.equivRealProdCLM.symm z) x Complex.I)
          z x +
        ω.hamiltonianCurvature
          (fun z x ↦ cappedPerturbation a L (fun q t (_ : M) ↦ c q t)
            (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ cappedPerturbation a L (fun q t (_ : M) ↦ c q t)
            (Complex.equivRealProdCLM.symm z) x Complex.I) z x := by
  have hc' := periodic_const_target (M := M) hc
  have hcs' := contMDiff_uncurry_const_target (I := I) (M := M) hcs
  rw [cappedPerturbation_add_const_fun H c x, cappedPerturbation_add_const_fun H c x,
    hamiltonianCurvature_add_const ω (differentiableAt_cappedPerturbation_domain hH hHs a L z x 1)
      (differentiableAt_cappedPerturbation_domain hH hHs a L z x Complex.I)
      (differentiableAt_cappedPerturbation_domain hc' hcs' a L z x 1)
      (differentiableAt_cappedPerturbation_domain hc' hcs' a L z x Complex.I),
    cappedPerturbation_const_target_fun c x, cappedPerturbation_const_target_fun c x]

/-- The curvature of the capped perturbation of target-independent Hamiltonians on `M` is the one on
`ℂ` with its standard symplectic form: whatever the target, it is the exterior derivative of the
same one-form on the domain. -/
private theorem hamiltonianCurvature_cappedPerturbation_const_eq_stdComplexSymplecticForm
    (ω : SmoothTwoForm I M) (a L : ℝ) (c : Puncture → ℝ → ℝ) (z : ℝ × ℝ) (x : M) :
    ω.hamiltonianCurvature
        (fun z x ↦ cappedPerturbation a L (fun q t (_ : M) ↦ c q t)
          (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ cappedPerturbation a L (fun q t (_ : M) ↦ c q t)
          (Complex.equivRealProdCLM.symm z) x Complex.I) z x =
      stdComplexSymplecticForm.hamiltonianCurvature
        (fun z x ↦ cappedPerturbation a L (fun q t (_ : ℂ) ↦ c q t)
          (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ cappedPerturbation a L (fun q t (_ : ℂ) ↦ c q t)
          (Complex.equivRealProdCLM.symm z) x Complex.I) z 0 := by
  rw [cappedPerturbation_const_target_fun (M := M) c (0 : ℂ),
    cappedPerturbation_const_target_fun (M := M) c (0 : ℂ), hamiltonianCurvature_const,
    cappedPerturbation_const_target_fun (M := ℂ) c (0 : ℂ),
    cappedPerturbation_const_target_fun (M := ℂ) c (0 : ℂ),
    SymplecticForm.hamiltonianCurvature_const]

/-- **The curvature of a normalization integrates to zero, for a manifold target.** For
period-one `C¹` functions `c_q` of time, the curvature of the capped perturbation of the
target-independent Hamiltonians `c_q` on `M` integrates to zero over the plane, along any map
`u`. -/
theorem integral_hamiltonianCurvature_cappedPerturbation_const (ω : SmoothTwoForm I M)
    (hc : ∀ q, Periodic (c q) 1) (hcs : ∀ q, ContDiff ℝ 1 (c q)) (a L : ℝ) (u : ℝ × ℝ → M) :
    ∫ z, ω.hamiltonianCurvature
        (fun z x ↦ cappedPerturbation a L (fun q t (_ : M) ↦ c q t)
          (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ cappedPerturbation a L (fun q t (_ : M) ↦ c q t)
          (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z) = 0 := by
  rw [integral_congr_ae (Filter.Eventually.of_forall fun z ↦
    ω.hamiltonianCurvature_cappedPerturbation_const_eq_stdComplexSymplecticForm a L c z (u z))]
  exact stdComplexSymplecticForm.integral_hamiltonianCurvature_cappedPerturbation_const hc hcs a L
    fun _ ↦ 0

/-- For `C¹` functions `c_q` of time, the curvature of the capped perturbation of the
target-independent Hamiltonians `c_q` on `M` is integrable along any map `u`. -/
theorem integrable_hamiltonianCurvature_cappedPerturbation_const (ω : SmoothTwoForm I M)
    (hc : ∀ q, Periodic (c q) 1) (hcs : ∀ q, ContDiff ℝ 1 (c q)) (a L : ℝ) (u : ℝ × ℝ → M) :
    Integrable fun z ↦ ω.hamiltonianCurvature
        (fun z x ↦ cappedPerturbation a L (fun q t (_ : M) ↦ c q t)
          (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ cappedPerturbation a L (fun q t (_ : M) ↦ c q t)
          (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z) := by
  exact (stdComplexSymplecticForm.integrable_hamiltonianCurvature_cappedPerturbation_const hc hcs
    a L fun _ ↦ 0).congr (Filter.Eventually.of_forall fun z ↦
      (ω.hamiltonianCurvature_cappedPerturbation_const_eq_stdComplexSymplecticForm a L c z
        (u z)).symm)

/-- Normalizing the end Hamiltonians does not change the integrability of the curvature of the
capped perturbation along a map. -/
theorem integrable_hamiltonianCurvature_cappedPerturbation_add_const_iff (ω : SmoothTwoForm I M)
    (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q)))
    (hc : ∀ q, Periodic (c q) 1) (hcs : ∀ q, ContDiff ℝ 1 (c q)) (a L : ℝ) (u : ℝ × ℝ → M) :
    (Integrable fun z ↦ ω.hamiltonianCurvature
        (fun z x ↦ cappedPerturbation a L (fun q t y ↦ H q t y + c q t)
          (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ cappedPerturbation a L (fun q t y ↦ H q t y + c q t)
          (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z)) ↔
      Integrable fun z ↦ ω.hamiltonianCurvature
        (fun z x ↦ cappedPerturbation a L H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ cappedPerturbation a L H (Complex.equivRealProdCLM.symm z) x Complex.I)
        z (u z) := by
  simp only [ω.hamiltonianCurvature_cappedPerturbation_add_const hH hHs hc hcs a L]
  exact integrable_add_iff_integrable_left'
    (ω.integrable_hamiltonianCurvature_cappedPerturbation_const hc hcs a L u)

/-- **Normalizing the end Hamiltonians does not change the integrated curvature, for a manifold
target.** Along a map whose curvature for `H_q` is integrable over the plane, the integrated
curvature of the capped perturbation of the end Hamiltonians `H_q + c_q` is the integrated
curvature for `H_q`. Both sides of the energy identity
`SmoothTwoForm.IsNondegenerate.integral_floerEnergyDensity_cappedPerturbation` are therefore
unchanged by the normalization. -/
theorem integral_hamiltonianCurvature_cappedPerturbation_add_const (ω : SmoothTwoForm I M)
    (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q)))
    (hc : ∀ q, Periodic (c q) 1) (hcs : ∀ q, ContDiff ℝ 1 (c q)) (a L : ℝ) {u : ℝ × ℝ → M}
    (hu : Integrable fun z ↦ ω.hamiltonianCurvature
        (fun z x ↦ cappedPerturbation a L H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ cappedPerturbation a L H (Complex.equivRealProdCLM.symm z) x Complex.I)
        z (u z)) :
    ∫ z, ω.hamiltonianCurvature
        (fun z x ↦ cappedPerturbation a L (fun q t y ↦ H q t y + c q t)
          (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ cappedPerturbation a L (fun q t y ↦ H q t y + c q t)
          (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z) =
      ∫ z, ω.hamiltonianCurvature
        (fun z x ↦ cappedPerturbation a L H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ cappedPerturbation a L H (Complex.equivRealProdCLM.symm z) x Complex.I)
        z (u z) := by
  simp only [ω.hamiltonianCurvature_cappedPerturbation_add_const hH hHs hc hcs a L]
  rw [integral_add hu (ω.integrable_hamiltonianCurvature_cappedPerturbation_const hc hcs a L u),
    ω.integral_hamiltonianCurvature_cappedPerturbation_const hc hcs a L u, add_zero]

/-- **Normalizing the end Hamiltonians does not change the integrated curvature of the comparison
family, for a manifold target.** For every `R`, along a map whose curvature for `K_R` built from
`H_q` is integrable, the integrated curvature of `K_R` built from `H_q + c_q` is the same. -/
theorem integral_hamiltonianCurvature_cappedComparisonPerturbation_add_const
    (ω : SmoothTwoForm I M) (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q)))
    (hc : ∀ q, Periodic (c q) 1) (hcs : ∀ q, ContDiff ℝ 1 (c q)) (R : ℝ) {u : ℝ × ℝ → M}
    (hu : Integrable fun z ↦ ω.hamiltonianCurvature
        (fun z x ↦ cappedComparisonPerturbation H R (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ cappedComparisonPerturbation H R (Complex.equivRealProdCLM.symm z) x
          Complex.I) z (u z)) :
    ∫ z, ω.hamiltonianCurvature
        (fun z x ↦ cappedComparisonPerturbation (fun q t y ↦ H q t y + c q t) R
          (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ cappedComparisonPerturbation (fun q t y ↦ H q t y + c q t) R
          (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z) =
      ∫ z, ω.hamiltonianCurvature
        (fun z x ↦ cappedComparisonPerturbation H R (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ cappedComparisonPerturbation H R (Complex.equivRealProdCLM.symm z) x
          Complex.I) z (u z) := by
  simp only [cappedComparisonPerturbation_def] at hu ⊢
  exact ω.integral_hamiltonianCurvature_cappedPerturbation_add_const hH hHs hc hcs _ _ hu

/-- Normalizing the end Hamiltonians does not change the integrability of the curvature of the
comparison family along a map. -/
private theorem integrable_hamiltonianCurvature_cappedComparisonPerturbation_add_const_iff
    (ω : SmoothTwoForm I M) (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q)))
    (hc : ∀ q, Periodic (c q) 1) (hcs : ∀ q, ContDiff ℝ 1 (c q)) (R : ℝ) (u : ℝ × ℝ → M) :
    (Integrable fun z ↦ ω.hamiltonianCurvature
        (fun z x ↦ cappedComparisonPerturbation (fun q t y ↦ H q t y + c q t) R
          (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ cappedComparisonPerturbation (fun q t y ↦ H q t y + c q t) R
          (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z)) ↔
      Integrable fun z ↦ ω.hamiltonianCurvature
        (fun z x ↦ cappedComparisonPerturbation H R (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ cappedComparisonPerturbation H R (Complex.equivRealProdCLM.symm z) x
          Complex.I) z (u z) := by
  simp only [cappedComparisonPerturbation_def]
  exact ω.integrable_hamiltonianCurvature_cappedPerturbation_add_const_iff hH hHs hc hcs _ _ u

namespace IsNondegenerate

/-- **The energy bound of the comparison family for any normalization, for a manifold target.**
If the end Hamiltonians differ from period-one `C¹` functions `c_q` of time by at most `B_q`,
`|H_q(t, x) - c_q(t)| ≤ B_q`, then for every `R ≥ 0` the energy of a `C¹` map for `K_R`, with
integrable energy and curvature, differs from its symplectic area by at most `2 (B₀ + B₁ + B_∞)`.
With `c_q(t) = H_q(t, x₀)` for a point `x₀`, the bound `B_q` can be taken to be the largest
oscillation `sup_x H_q(t, x) - inf_x H_q(t, x)` of the end Hamiltonian over a time `t`. -/
theorem abs_integral_floerEnergyDensity_cappedComparisonPerturbation_sub_le_of_abs_sub_le
    [FiniteDimensional ℝ E] (hω : ω.IsNondegenerate) (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q)))
    (hc : ∀ q, Periodic (c q) 1) (hcs : ∀ q, ContDiff ℝ 1 (c q))
    {B : Puncture → ℝ} (hB : ∀ q t x, |H q t x - c q t| ≤ B q) {R : ℝ} (hR₀ : 0 ≤ R)
    {u : ℝ × ℝ → M} (hu : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 1 u)
    (hE : Integrable (ω.floerEnergyDensity
      (fun z x ↦ cappedComparisonPerturbation H R (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ cappedComparisonPerturbation H R (Complex.equivRealProdCLM.symm z) x Complex.I)
      u))
    (hR : Integrable fun z ↦ ω.hamiltonianCurvature
      (fun z x ↦ cappedComparisonPerturbation H R (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ cappedComparisonPerturbation H R (Complex.equivRealProdCLM.symm z) x Complex.I)
      z (u z)) :
    |(∫ z, ω.floerEnergyDensity
        (fun z x ↦ cappedComparisonPerturbation H R (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ cappedComparisonPerturbation H R (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z) -
      ∫ z, (SmoothBundleForm.eval₂ ω (u z)
        (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
        (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)| ≤ 2 * ∑ q, B q := by
  -- Write `H_q = (H_q - c_q) + c_q`; the datum built from `H_q - c_q` has the same energy density.
  have hGp := periodic_sub_const hH hc
  have hGs (q : Puncture) :
      ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry fun t x ↦ H q t x - c q t) :=
    (hHs q).sub (contMDiff_uncurry_const_target hcs q)
  rw [← sub_const_add_const H c] at hE hR ⊢
  rw [floerEnergyDensity_cappedComparisonPerturbation_add_const] at hE ⊢
  rw [ω.integrable_hamiltonianCurvature_cappedComparisonPerturbation_add_const_iff hGp hGs hc hcs]
    at hR
  exact hω.abs_integral_floerEnergyDensity_cappedComparisonPerturbation_sub_le hGp hGs hB hR₀ hu
    hE hR

end IsNondegenerate

end SmoothTwoForm

/-! ### Symplectic vector spaces: the curvature of the normalized perturbation -/

namespace SymplecticForm

open Floer

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {H : Puncture → ℝ → V → ℝ} {c : Puncture → ℝ → ℝ}

/-- **The curvature of the normalized capped perturbation.** At every point of the plane, the
curvature of the capped perturbation of the end Hamiltonians `H_q + c_q` is the curvature for `H_q`
plus the curvature of the capped perturbation of the target-independent Hamiltonians `c_q`. This
is the vector-space case of `SmoothTwoForm.hamiltonianCurvature_cappedPerturbation_add_const`. -/
theorem hamiltonianCurvature_cappedPerturbation_add_const (ω : SymplecticForm V)
    (hH : ∀ q, Periodic (H q) 1) (hHs : ∀ q, ContDiff ℝ 1 (uncurry (H q)))
    (hc : ∀ q, Periodic (c q) 1) (hcs : ∀ q, ContDiff ℝ 1 (c q)) (a L : ℝ) (z : ℝ × ℝ) (x : V) :
    ω.hamiltonianCurvature
        (fun z x ↦ cappedPerturbation a L (fun q t y ↦ H q t y + c q t)
          (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ cappedPerturbation a L (fun q t y ↦ H q t y + c q t)
          (Complex.equivRealProdCLM.symm z) x Complex.I) z x =
      ω.hamiltonianCurvature
          (fun z x ↦ cappedPerturbation a L H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ cappedPerturbation a L H (Complex.equivRealProdCLM.symm z) x Complex.I)
          z x +
        ω.hamiltonianCurvature
          (fun z x ↦ cappedPerturbation a L (fun q t (_ : V) ↦ c q t)
            (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ cappedPerturbation a L (fun q t (_ : V) ↦ c q t)
            (Complex.equivRealProdCLM.symm z) x Complex.I) z x := by
  have h := ω.constSmooth.hamiltonianCurvature_cappedPerturbation_add_const hH
    (fun q ↦ contMDiff_prod_modelWithCornersSelf_iff.2 (hHs q).contMDiff) hc hcs a L z x
  simp only [hamiltonianCurvature_constSmooth] at h
  exact h

/-- **Normalizing the end Hamiltonians does not change the integrated curvature.** Along a map
whose curvature for `H_q` is integrable over the plane, the integrated curvature of the capped
perturbation of the end Hamiltonians `H_q + c_q` is the integrated curvature for `H_q`. This is the
vector-space case of `SmoothTwoForm.integral_hamiltonianCurvature_cappedPerturbation_add_const`. -/
theorem integral_hamiltonianCurvature_cappedPerturbation_add_const (ω : SymplecticForm V)
    (hH : ∀ q, Periodic (H q) 1) (hHs : ∀ q, ContDiff ℝ 1 (uncurry (H q)))
    (hc : ∀ q, Periodic (c q) 1) (hcs : ∀ q, ContDiff ℝ 1 (c q)) (a L : ℝ) {u : ℝ × ℝ → V}
    (hu : Integrable fun z ↦ ω.hamiltonianCurvature
        (fun z x ↦ cappedPerturbation a L H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ cappedPerturbation a L H (Complex.equivRealProdCLM.symm z) x Complex.I)
        z (u z)) :
    ∫ z, ω.hamiltonianCurvature
        (fun z x ↦ cappedPerturbation a L (fun q t y ↦ H q t y + c q t)
          (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ cappedPerturbation a L (fun q t y ↦ H q t y + c q t)
          (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z) =
      ∫ z, ω.hamiltonianCurvature
        (fun z x ↦ cappedPerturbation a L H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ cappedPerturbation a L H (Complex.equivRealProdCLM.symm z) x Complex.I)
        z (u z) := by
  have h := ω.constSmooth.integral_hamiltonianCurvature_cappedPerturbation_add_const hH
    (fun q ↦ contMDiff_prod_modelWithCornersSelf_iff.2 (hHs q).contMDiff) hc hcs a L
    (by simpa only [hamiltonianCurvature_constSmooth] using hu)
  simp only [hamiltonianCurvature_constSmooth] at h
  exact h

/-- **The energy bound of the comparison family for any normalization.** For a symplectic vector
space target, if the end Hamiltonians differ from period-one `C¹` functions `c_q` of time by at
most `B_q`, `|H_q(t, x) - c_q(t)| ≤ B_q`, then for every `R ≥ 0` the energy of a `C¹` map `u` for
`K_R`, if it is integrable, differs from the symplectic area of `u` by at most
`2 (B₀ + B₁ + B_∞)`. -/
theorem abs_integral_floerEnergyDensity_cappedComparisonPerturbation_sub_le_of_abs_sub_le
    (ω : SymplecticForm V) (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContDiff ℝ 1 (uncurry (H q))) (hc : ∀ q, Periodic (c q) 1)
    (hcs : ∀ q, ContDiff ℝ 1 (c q)) {B : Puncture → ℝ} (hB : ∀ q t x, |H q t x - c q t| ≤ B q)
    {R : ℝ} (hR₀ : 0 ≤ R) {u : ℝ × ℝ → V} (hu : ContDiff ℝ 1 u)
    (hE : Integrable (ω.floerEnergyDensity
      (fun z x ↦ cappedComparisonPerturbation H R (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ cappedComparisonPerturbation H R (Complex.equivRealProdCLM.symm z) x Complex.I)
      u)) :
    |(∫ z, ω.floerEnergyDensity
        (fun z x ↦ cappedComparisonPerturbation H R (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ cappedComparisonPerturbation H R (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z) -
      ∫ z, ω (fderiv ℝ u z stdComplexLineReal) (fderiv ℝ u z stdComplexLineImag)| ≤
        2 * ∑ q, B q := by
  -- Write `H_q = (H_q - c_q) + c_q`; the datum built from `H_q - c_q` has the same energy density.
  have hGs (q : Puncture) : ContDiff ℝ 1 (uncurry fun t x ↦ H q t x - c q t) :=
    (hHs q).sub (contDiff_uncurry_const_target hcs q)
  rw [← sub_const_add_const H c, floerEnergyDensity_cappedComparisonPerturbation_add_const] at hE ⊢
  exact ω.abs_integral_floerEnergyDensity_cappedComparisonPerturbation_sub_le
    (periodic_sub_const hH hc) hGs hB hR₀ hu hE

end SymplecticForm

end TauCeti
