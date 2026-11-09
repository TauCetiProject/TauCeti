/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Curvature

/-!
# Changes of normalization on the pair of pants

Let `K` be the pair-of-pants perturbation (`TauCeti.Floer.pairOfPantsPerturbation`) of period-one
Hamiltonians `H_q` on the three ends of `S = ℂ ∖ {0, 1}`, and let `c_q` be period-one functions of
time alone. Replacing `H_q` by `H_q + c_q` is a change of normalization: it does not change the
Hamiltonian vector fields, so the Floer equation and the energy of every map stay the same, while
the actions of the end loops shift by `∫₀¹ c_q`. This file proves that the curvature term of the
energy identity

`E(u) = A₀ + A₁ - A_∞ - ∫_S R_K(u)`

absorbs exactly these shifts, for a symplectic vector space target.

The pointwise facts behind this hold for any perturbation and any target. Adding functions
`κ_s(z)`, `κ_t(z)` of the domain point alone to the components of `K` changes neither the
perturbed derivative `du - X_K(u)` nor the energy density
(`SymplecticForm.perturbedFDeriv_add_const`, `SymplecticForm.floerEnergyDensity_add_const`, and
`SmoothTwoForm.perturbedMFDeriv_add_const`, `SmoothTwoForm.floerEnergyDensity_add_const` for a
manifold target), and it shifts the curvature by the curl `∂_s κ_t - ∂_t κ_s`
(`SymplecticForm.hamiltonianCurvature_add_const`, `SmoothTwoForm.hamiltonianCurvature_add_const`).

The perturbation is additive in the Hamiltonians (`TauCeti.Floer.pairOfPantsPerturbation_add`),
and for Hamiltonians of time alone it does not depend on the target point
(`TauCeti.Floer.pairOfPantsPerturbation_eq_of_forall_eq`). The datum `K_c` of the `c_q` is
therefore a one-form on `S`, whose curvature is its curl
(`SymplecticForm.hamiltonianCurvature_const`). Its total curl is the signed sum of the means of
the `c_q`,

`∫_S R_{K_c} = ∫₀¹ c₀ + ∫₀¹ c₁ - ∫₀¹ c_∞`

(`SymplecticForm.setIntegral_hamiltonianCurvature_pairOfPantsPerturbation_eq_sum`). Consequently,
along every map `u` continuous on `S`,

`∫_S R_{K_{H+c}}(u) = ∫_S R_{K_H}(u) + ∫₀¹ c₀ + ∫₀¹ c₁ - ∫₀¹ c_∞`

(`SymplecticForm.setIntegral_hamiltonianCurvature_pairOfPantsPerturbation_add`), while the energy
density is unchanged (`SymplecticForm.floerEnergyDensity_pairOfPantsPerturbation_add`). Since the
action of every loop shifts by `∫₀¹ c_q` (`SymplecticForm.hamiltonianAction_add_const`), the
shifts of `A₀ + A₁ - A_∞` and of `∫_S R_K(u)` cancel in the energy identity. Energy and action
bounds derived from the identity with a curvature term, such as the one-sided bound
`SymplecticForm.sum_mul_integral_le_setIntegral_hamiltonianCurvature_pairOfPantsPerturbation`,
can therefore be computed in any normalization of the end Hamiltonians.

## References

* M. Schwarz, *Cohomology operations from S¹-cobordisms in Floer homology*, PhD thesis,
  ETH Zürich (1995), on the energy estimate for the pair-of-pants product.
* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, Section 8.1, on
  Hamiltonian perturbations and their curvature.
-/

public section

open Set Function MeasureTheory TauCeti.ThricePuncturedSphere
  TauCeti.ThricePuncturedSphere.Puncture

namespace TauCeti

namespace SymplecticForm

open Floer

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {H : Puncture → ℝ → V → ℝ} {c : Puncture → ℝ → ℝ}

omit [NormedSpace ℝ V] [FiniteDimensional ℝ V] in
/-- The components of the pair-of-pants perturbation of Hamiltonians `c_q` of time alone, in real
coordinates, as functions on the domain. -/
private theorem pairOfPantsPerturbation_fun_const_eq (c : Puncture → ℝ → ℝ) (v : ℂ) :
    (fun (z : ℝ × ℝ) (x : V) ↦
        pairOfPantsPerturbation (fun q t (_ : V) ↦ c q t) (Complex.equivRealProdCLM.symm z) x v) =
      fun z _ ↦ pairOfPantsPerturbation (fun q t (_ : V) ↦ c q t)
        (Complex.equivRealProdCLM.symm z) 0 v := by
  funext z x
  rw [pairOfPantsPerturbation_eq_of_forall_eq (x := x) (y := 0) (fun _ _ ↦ rfl)]

omit [FiniteDimensional ℝ V] in
/-- Hamiltonians of time alone which are `C¹` are jointly `C¹` on `ℝ × V`. -/
private theorem contDiff_uncurry_const (hcs : ∀ q, ContDiff ℝ 1 (c q)) (q : Puncture) :
    ContDiff ℝ 1 (uncurry fun t (_ : V) ↦ c q t) :=
  (hcs q).comp contDiff_fst

omit [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] in
/-- Hamiltonians of time alone which have period one have period one on `ℝ × V`. -/
private theorem periodic_const (hc : ∀ q, Periodic (c q) 1) (q : Puncture) :
    Periodic (fun t (_ : V) ↦ c q t) 1 :=
  (hc q).comp fun a _ ↦ a

omit [NormedSpace ℝ V] [FiniteDimensional ℝ V] in
/-- The components of the pair-of-pants perturbation of `H_q + c_q`, for `c_q` of time alone, are
those of `H_q` plus functions on the domain. -/
private theorem pairOfPantsPerturbation_add_fun_eq (H : Puncture → ℝ → V → ℝ)
    (c : Puncture → ℝ → ℝ) (v : ℂ) :
    (fun (z : ℝ × ℝ) (x : V) ↦ pairOfPantsPerturbation (fun q t y ↦ H q t y + c q t)
        (Complex.equivRealProdCLM.symm z) x v) =
      fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x v +
        pairOfPantsPerturbation (fun q t (_ : V) ↦ c q t)
          (Complex.equivRealProdCLM.symm z) 0 v := by
  funext z x
  rw [pairOfPantsPerturbation_add H (fun q t (_ : V) ↦ c q t), add_apply,
    pairOfPantsPerturbation_eq_of_forall_eq (H := fun q t (_ : V) ↦ c q t) (x := x) (y := 0)
      (fun _ _ ↦ rfl)]

/-- The curvature of the pair-of-pants perturbation of Hamiltonians `c_q` of time alone, negated,
is the curvature of the perturbation of the negated Hamiltonians `-c_q`. -/
private theorem hamiltonianCurvature_pairOfPantsPerturbation_neg (ω : SymplecticForm V)
    (c : Puncture → ℝ → ℝ) (z : ℝ × ℝ) (x : V) :
    ω.hamiltonianCurvature
        (fun z x ↦ pairOfPantsPerturbation (fun q t (_ : V) ↦ -c q t)
          (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation (fun q t (_ : V) ↦ -c q t)
          (Complex.equivRealProdCLM.symm z) x Complex.I) z x =
      -ω.hamiltonianCurvature
        (fun z x ↦ pairOfPantsPerturbation (fun q t (_ : V) ↦ c q t)
          (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation (fun q t (_ : V) ↦ c q t)
          (Complex.equivRealProdCLM.symm z) x Complex.I) z x := by
  have hneg (v : ℂ) := pairOfPantsPerturbation_fun_const_eq (V := V) (fun q t ↦ -c q t) v
  simp only at hneg
  have hf (v : ℂ) : (fun z : ℝ × ℝ ↦ pairOfPantsPerturbation (fun q t (_ : V) ↦ -c q t)
      (Complex.equivRealProdCLM.symm z) 0 v) = fun z ↦ -pairOfPantsPerturbation
        (fun q t (_ : V) ↦ c q t) (Complex.equivRealProdCLM.symm z) 0 v := by
    funext z
    rw [pairOfPantsPerturbation_neg, neg_apply]
  rw [hneg, hneg, pairOfPantsPerturbation_fun_const_eq, pairOfPantsPerturbation_fun_const_eq,
    hamiltonianCurvature_const, hamiltonianCurvature_const, hf, hf, fderiv_fun_neg, fderiv_fun_neg,
    neg_apply, neg_apply]
  ring

/-- **The total curl of a time-dependent normalization.** Let `c_q` be period-one `C¹` functions
of time alone. Along every map `u`, the curvature of their pair-of-pants perturbation integrates
over `S = ℂ ∖ {0, 1}` to

`∫_S R_{K_c}(u) = ∫₀¹ c₀ + ∫₀¹ c₁ - ∫₀¹ c_∞`,

the signed sum of the means of `c_q`, with the sign `+` on the input ends `0` and `1` and `-` on
the output end `∞`. -/
theorem setIntegral_hamiltonianCurvature_pairOfPantsPerturbation_eq_sum (ω : SymplecticForm V)
    (hc : ∀ q, Periodic (c q) 1) (hcs : ∀ q, ContDiff ℝ 1 (c q)) (u : ℝ × ℝ → V) :
    ∫ z in {z : ℝ × ℝ | Complex.equivRealProdCLM.symm z ≠ 0 ∧
        Complex.equivRealProdCLM.symm z ≠ 1}, ω.hamiltonianCurvature
          (fun z x ↦ pairOfPantsPerturbation (fun q t (_ : V) ↦ c q t)
            (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation (fun q t (_ : V) ↦ c q t)
            (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z) =
      ∑ q, q.endSign * ∫ t in (0 : ℝ)..1, c q t := by
  -- The curvature does not depend on the target point, so `u` may be replaced by `0`.
  have hu : ∀ (c : Puncture → ℝ → ℝ) (z : ℝ × ℝ), ω.hamiltonianCurvature
      (fun z x ↦ pairOfPantsPerturbation (fun q t (_ : V) ↦ c q t)
        (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ pairOfPantsPerturbation (fun q t (_ : V) ↦ c q t)
        (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z) =
      ω.hamiltonianCurvature
        (fun z x ↦ pairOfPantsPerturbation (fun q t (_ : V) ↦ c q t)
          (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation (fun q t (_ : V) ↦ c q t)
          (Complex.equivRealProdCLM.symm z) x Complex.I) z 0 := fun c z ↦ by
    rw [pairOfPantsPerturbation_fun_const_eq, pairOfPantsPerturbation_fun_const_eq,
      hamiltonianCurvature_const, hamiltonianCurvature_const]
  simp only [hu c]
  have hci (q : Puncture) : IntervalIntegrable (c q) volume 0 1 :=
    (hcs q).continuous.intervalIntegrable 0 1
  -- The one-sided curvature bound, for `c` and for `-c`, gives both inequalities.
  have hge := sum_mul_integral_le_setIntegral_hamiltonianCurvature_pairOfPantsPerturbation ω
    (H := fun q t (_ : V) ↦ c q t) (periodic_const hc)
    (contDiff_uncurry_const hcs) hci (fun _ _ _ ↦ le_rfl) (u := fun _ ↦ (0 : V))
    continuousOn_const
  have hle := sum_mul_integral_le_setIntegral_hamiltonianCurvature_pairOfPantsPerturbation ω
    (H := fun q t (_ : V) ↦ -c q t) (fun q t ↦ funext fun _ ↦ congrArg Neg.neg (hc q t))
    (contDiff_uncurry_const fun q ↦ (hcs q).neg) (h := fun q t ↦ -c q t)
    (fun q ↦ (hci q).neg) (fun _ _ _ ↦ le_rfl) (u := fun _ ↦ (0 : V)) continuousOn_const
  simp only [hamiltonianCurvature_pairOfPantsPerturbation_neg, integral_neg,
    intervalIntegral.integral_neg, mul_neg, Finset.sum_neg_distrib, neg_le_neg_iff] at hle
  exact le_antisymm hle hge

/-- **The energy density does not see the normalization of the pair of pants.** Adding functions
`c_q` of time alone to the end Hamiltonians leaves the Floer energy density of every map
unchanged. -/
@[simp]
theorem floerEnergyDensity_pairOfPantsPerturbation_add (ω : SymplecticForm V)
    (H : Puncture → ℝ → V → ℝ) (c : Puncture → ℝ → ℝ) :
    ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsPerturbation (fun q t y ↦ H q t y + c q t)
          (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation (fun q t y ↦ H q t y + c q t)
          (Complex.equivRealProdCLM.symm z) x Complex.I) =
      ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) := by
  rw [pairOfPantsPerturbation_add_fun_eq, pairOfPantsPerturbation_add_fun_eq,
    floerEnergyDensity_add_const]

/-- **The curvature absorbs a change of normalization of the pair of pants.** Let `H_q` be
period-one `C¹` Hamiltonians and `c_q` period-one `C¹` functions of time alone. Along every map `u`
continuous on `S = ℂ ∖ {0, 1}`, replacing `H_q` by `H_q + c_q` changes the integrated curvature of
the pair-of-pants perturbation by the signed sum of the means of `c_q`:

`∫_S R_{K_{H+c}}(u) = ∫_S R_{K_H}(u) + ∫₀¹ c₀ + ∫₀¹ c₁ - ∫₀¹ c_∞`.

This is the same amount by which the signed sum `A₀ + A₁ - A_∞` of the actions of the end loops
changes (`SymplecticForm.hamiltonianAction_add_const`). -/
theorem setIntegral_hamiltonianCurvature_pairOfPantsPerturbation_add (ω : SymplecticForm V)
    (hH : ∀ q, Periodic (H q) 1) (hHs : ∀ q, ContDiff ℝ 1 (uncurry (H q)))
    (hc : ∀ q, Periodic (c q) 1) (hcs : ∀ q, ContDiff ℝ 1 (c q)) {u : ℝ × ℝ → V}
    (hu : ContinuousOn u {z : ℝ × ℝ | Complex.equivRealProdCLM.symm z ≠ 0 ∧
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
            z (u z)) + ∑ q, q.endSign * ∫ t in (0 : ℝ)..1, c q t := by
  have hS : IsOpen {z : ℝ × ℝ | Complex.equivRealProdCLM.symm z ≠ 0 ∧
      Complex.equivRealProdCLM.symm z ≠ 1} := isOpen_thricePuncturedSphereReal
  have hcH := contDiff_uncurry_const (V := V) hcs
  have hcP := periodic_const (V := V) hc
  -- Pointwise on `S`, the curvature of `H + c` is that of `H` plus the curl of the datum of `c`.
  have hpt : EqOn
      (fun z ↦ ω.hamiltonianCurvature
        (fun z x ↦ pairOfPantsPerturbation (fun q t y ↦ H q t y + c q t)
          (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation (fun q t y ↦ H q t y + c q t)
          (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z))
      (fun z ↦ ω.hamiltonianCurvature
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          z (u z) +
        ω.hamiltonianCurvature
          (fun z x ↦ pairOfPantsPerturbation (fun q t (_ : V) ↦ c q t)
            (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation (fun q t (_ : V) ↦ c q t)
            (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z))
      {z : ℝ × ℝ | Complex.equivRealProdCLM.symm z ≠ 0 ∧ Complex.equivRealProdCLM.symm z ≠ 1} :=
    fun z hz ↦ by
      simp only [pairOfPantsPerturbation_add_fun_eq, pairOfPantsPerturbation_fun_const_eq c]
      rw [hamiltonianCurvature_add_const ω
          (differentiableAt_pairOfPantsPerturbation_domain hH hHs hz _ _)
          (differentiableAt_pairOfPantsPerturbation_domain hH hHs hz _ _)
          (differentiableAt_pairOfPantsPerturbation_domain hcP hcH hz _ _)
          (differentiableAt_pairOfPantsPerturbation_domain hcP hcH hz _ _),
        hamiltonianCurvature_const]
  rw [setIntegral_congr_fun hS.measurableSet hpt,
    integral_add (integrableOn_hamiltonianCurvature_pairOfPantsPerturbation ω hH hHs hu)
      (integrableOn_hamiltonianCurvature_pairOfPantsPerturbation ω hcP hcH hu),
    setIntegral_hamiltonianCurvature_pairOfPantsPerturbation_eq_sum ω hc hcs]

end SymplecticForm

end TauCeti
