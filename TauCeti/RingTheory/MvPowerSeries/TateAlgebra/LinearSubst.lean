/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.AnalyticSubst
public import Mathlib.Data.Matrix.Mul

/-!
# Linear substitutions of restricted power series

A matrix whose entries satisfy the bounds `‖Aᵢⱼ‖ sⱼ ≤ rᵢ` pulls restricted series on the
polydisc of radii `r` back to the polydisc of radii `s`. An invertible matrix gives an
injective pullback. The proof uses the formal inverse and requires a radius bound
only on the forward matrix.
-/

public section

namespace TauCeti.MvPowerSeries

open _root_.MvPowerSeries Matrix

variable {R : Type*} [NormedCommRing R] [IsUltrametricDist R] {k m : ℕ}
  {r : Fin k → ℝ} {s : Fin m → ℝ}

variable [∀ j, Fact (0 < s j)]

private theorem norm_polynomialToRestricted_sum_C_mul_X_le {a : Fin m → R} {ρ : ℝ}
    (hρ : 0 ≤ ρ) (ha : ∀ j, ‖a j‖ * s j ≤ ρ) :
    ‖polynomialToRestricted s (∑ j, MvPolynomial.C (a j) * MvPolynomial.X j)‖ ≤ ρ := by
  rw [map_sum]
  apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hρ
  intro j _
  simpa [MvPolynomial.C_mul_X_eq_monomial, polynomialToRestricted_apply, MvPolynomial.coe_monomial,
    norm_monomial, Finsupp.prod_single_index] using ha j

variable [CompleteSpace R] [∀ i, Fact (0 < r i)]

/-- Pullback along the linear map `z ↦ A *ᵥ z` between closed polydiscs. -/
noncomputable def restrictedLinearSubst (A : Matrix (Fin k) (Fin m) R)
    (hA : ∀ i j, ‖A i j‖ * s j ≤ r i) :
    IsRestricted.subring (R := R) r →ₐ[R] IsRestricted.subring (R := R) s :=
  restrictedAnalyticSubst
    (fun i ↦ polynomialToRestricted s (∑ j, MvPolynomial.C (A i j) * MvPolynomial.X j))
    (fun i ↦ norm_polynomialToRestricted_sum_C_mul_X_le (Fact.out : 0 < r i).le (hA i))

/-- Linear pullback sends each variable to the linear form in the corresponding matrix row. -/
@[simp]
theorem restrictedLinearSubst_X (A : Matrix (Fin k) (Fin m) R)
    (hA : ∀ i j, ‖A i j‖ * s j ≤ r i) (i : Fin k) :
    restrictedLinearSubst A hA ⟨X i, isRestricted_monomial r (Finsupp.single i 1) 1⟩ =
      polynomialToRestricted s (∑ j, MvPolynomial.C (A i j) * MvPolynomial.X j) :=
  restrictedAnalyticSubst_X _ _ i

/-- Pullback along a bounded linear map does not increase Gauss norms. -/
theorem norm_restrictedLinearSubst_le (A : Matrix (Fin k) (Fin m) R)
    (hA : ∀ i j, ‖A i j‖ * s j ≤ r i) (f : IsRestricted.subring (R := R) r) :
    ‖restrictedLinearSubst A hA f‖ ≤ ‖f‖ :=
  norm_restrictedAnalyticSubst_le _ _ f

/-- Linear pullback agrees with formal substitution of the linear forms given by the rows. -/
@[simp]
theorem coe_restrictedLinearSubst (A : Matrix (Fin k) (Fin m) R)
    (hA : ∀ i j, ‖A i j‖ * s j ≤ r i) (f : IsRestricted.subring (R := R) r) :
    (restrictedLinearSubst A hA f : MvPowerSeries (Fin m) R) =
      subst (fun i ↦ ∑ j, C (A i j) * X j) (f : MvPowerSeries (Fin k) R) := by
  rw [restrictedLinearSubst, coe_restrictedAnalyticSubst_eq_subst _ _
    (hasSubst_of_constantCoeff_zero (fun i ↦ by simp))]
  simp

/-- Evaluating a linear pullback at `x` is evaluating the original series at `A *ᵥ x`. -/
theorem restrictedEval₂_restrictedLinearSubst (A : Matrix (Fin k) (Fin m) R)
    (hA : ∀ i j, ‖A i j‖ * s j ≤ r i) (x : Fin m → R) (hx : ∀ j, ‖x j‖ ≤ s j)
    (f : IsRestricted.subring (R := R) r)
    (hAx : ∀ i, ‖(A *ᵥ x) i‖ ≤ r i) :
    restrictedEval₂ (RingHom.id R) x (fun _ ↦ le_rfl) hx (restrictedLinearSubst A hA f) =
      restrictedEval₂ (RingHom.id R) (A *ᵥ x) (fun _ ↦ le_rfl) hAx f := by
  have h : (fun i ↦ restrictedEval₂ (RingHom.id R) x (fun _ ↦ le_rfl) hx
      (polynomialToRestricted s (∑ j, MvPolynomial.C (A i j) * MvPolynomial.X j))) = A *ᵥ x := by
    funext i
    rw [polynomialToRestricted_apply, restrictedEval₂_polynomial]
    simp [mulVec, dotProduct]
  simp only [restrictedLinearSubst, restrictedEval₂_restrictedAnalyticSubst]
  congr

/-- An invertible linear change of variables gives an injective pullback. Only the forward
matrix needs to satisfy the radius bounds. -/
theorem restrictedLinearSubst_injective {s : Fin k → ℝ} [∀ i, Fact (0 < s i)]
    (A : Matrix (Fin k) (Fin k) R) (hA : ∀ i j, ‖A i j‖ * s j ≤ r i) (h : IsUnit A) :
    Function.Injective (restrictedLinearSubst A hA) := by
  obtain ⟨u, rfl⟩ := h
  let a : Fin k → MvPowerSeries (Fin k) R := fun i ↦ ∑ j, C ((u : Matrix _ _ R) i j) * X j
  let b : Fin k → MvPowerSeries (Fin k) R := fun i ↦
    ∑ j, C ((↑(u⁻¹) : Matrix (Fin k) (Fin k) R) i j) * X j
  have ha : HasSubst a := hasSubst_of_constantCoeff_zero fun i ↦ by simp [a]
  have hb : HasSubst b := hasSubst_of_constantCoeff_zero fun i ↦ by simp [b]
  have hcomp : (fun i ↦ subst b (a i)) = X := by
    funext i
    have hrow : ∀ l, (∑ j, (u : Matrix _ _ R) i j * (↑(u⁻¹) : Matrix (Fin k) (Fin k) R) j l) =
        (1 : Matrix (Fin k) (Fin k) R) i l := by
      intro l
      simpa only [Matrix.mul_apply] using
        congrArg (fun M : Matrix (Fin k) (Fin k) R ↦ M i l) u.mul_inv
    have hc (c : R) : substAlgHom hb (C c) = C c := by rw [coe_substAlgHom, subst_C]
    simp only [a, ← coe_substAlgHom hb, map_sum, map_mul, hc, substAlgHom_X, b,
      Finset.mul_sum]
    rw [Finset.sum_comm]
    simp only [← mul_assoc, ← map_mul (C (σ := Fin k)), ← Finset.sum_mul,
      ← map_sum (C (σ := Fin k)), hrow]
    simp [Matrix.one_apply]
  intro f g hfg
  apply Subtype.ext
  have e := congrArg (fun f : IsRestricted.subring (R := R) s ↦
    subst b (f : MvPowerSeries (Fin k) R)) hfg
  have h' : subst b (subst a (f : MvPowerSeries (Fin k) R)) =
      subst b (subst a (g : MvPowerSeries (Fin k) R)) := by
    simpa only [coe_restrictedLinearSubst, a] using e
  simpa only [subst_comp_subst_apply ha hb, hcomp, subst_self, id_eq] using h'

end TauCeti.MvPowerSeries
