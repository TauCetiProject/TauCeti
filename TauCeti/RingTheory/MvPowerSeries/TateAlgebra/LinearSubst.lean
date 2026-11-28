/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.Ultra
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.AnalyticSubst
public import TauCeti.RingTheory.MvPowerSeries.Substitution

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

variable [CompleteSpace R] [∀ i, Fact (0 ≤ r i)]

/-- Pullback along the linear map `z ↦ A *ᵥ z` between closed polydiscs. -/
noncomputable def restrictedLinearSubst (A : Matrix (Fin k) (Fin m) R)
    (hA : ∀ i j, ‖A i j‖ * s j ≤ r i) :
    IsRestricted.subring (R := R) r →ₐ[R] IsRestricted.subring (R := R) s :=
  restrictedAnalyticSubst
    (fun i ↦ polynomialToRestricted s (∑ j, MvPolynomial.C (A i j) * MvPolynomial.X j))
    (fun i ↦ norm_polynomialToRestricted_sum_C_mul_X_le (Fact.out : 0 ≤ r i) (hA i))

/-- Linear pullback sends each variable to the linear form in the corresponding matrix row. -/
@[simp]
theorem restrictedLinearSubst_X (A : Matrix (Fin k) (Fin m) R)
    (hA : ∀ i j, ‖A i j‖ * s j ≤ r i) (i : Fin k) :
    restrictedLinearSubst A hA ⟨X i, isRestricted_monomial r (Finsupp.single i 1) 1⟩ =
      polynomialToRestricted s (∑ j, MvPolynomial.C (A i j) * MvPolynomial.X j) :=
  restrictedAnalyticSubst_X _ _ i

omit [∀ i, Fact (0 ≤ r i)] in
/-- Pullback along a bounded linear map does not increase Gauss norms. -/
theorem norm_restrictedLinearSubst_le [∀ i, Fact (0 < r i)] (A : Matrix (Fin k) (Fin m) R)
    (hA : ∀ i j, ‖A i j‖ * s j ≤ r i) (f : IsRestricted.subring (R := R) r) :
    letI : ∀ i, Fact (0 ≤ r i) := fun i ↦ ⟨(Fact.out : 0 < r i).le⟩
    ‖restrictedLinearSubst A hA f‖ ≤ ‖f‖ := by
  let : ∀ i, Fact (0 ≤ r i) := fun i ↦ ⟨(Fact.out : 0 < r i).le⟩
  exact norm_restrictedAnalyticSubst_le _ _ f

/-- Linear pullback agrees with formal substitution of the linear forms given by the rows. -/
@[simp]
theorem coe_restrictedLinearSubst (A : Matrix (Fin k) (Fin m) R)
    (hA : ∀ i j, ‖A i j‖ * s j ≤ r i) (f : IsRestricted.subring (R := R) r) :
    (restrictedLinearSubst A hA f : MvPowerSeries (Fin m) R) =
      subst (fun i ↦ ∑ j, C (A i j) * X j) (f : MvPowerSeries (Fin k) R) := by
  rw [restrictedLinearSubst, coe_restrictedAnalyticSubst_eq_subst _ _
    (hasSubst_of_constantCoeff_zero (fun i ↦ by simp))]
  simp

/-- Evaluating a linear pullback in a complete ultrametric ring is evaluating the original
series at the image under the coefficient-mapped matrix. -/
theorem restrictedEval₂_restrictedLinearSubst {S : Type*} [NormedCommRing S]
    [IsUltrametricDist S] [CompleteSpace S] (φ : R →+* S)
    (A : Matrix (Fin k) (Fin m) R) (hA : ∀ i j, ‖A i j‖ * s j ≤ r i) (x : Fin m → S)
    (hφ : ∀ a, ‖φ a‖ ≤ ‖a‖) (hx : ∀ j, ‖x j‖ ≤ s j)
    (f : IsRestricted.subring (R := R) r) :
    restrictedEval₂ φ x hφ hx (restrictedLinearSubst A hA f) =
      restrictedEval₂ φ (A.map φ *ᵥ x) hφ (A.norm_map_mulVec_le φ hA x hφ hx) f := by
  let g : Fin k → IsRestricted.subring (R := R) s := fun i ↦
    polynomialToRestricted s (∑ j, MvPolynomial.C (A i j) * MvPolynomial.X j)
  have hg : ∀ i, ‖g i‖ ≤ r i := fun i ↦
    norm_polynomialToRestricted_sum_C_mul_X_le (Fact.out : 0 ≤ r i) (hA i)
  have h : (fun i ↦ restrictedEval₂ φ x hφ hx (g i)) = A.map φ *ᵥ x := by
    funext i
    dsimp only [g]
    rw [polynomialToRestricted_apply, restrictedEval₂_polynomial]
    have hp : (∑ j, MvPolynomial.C (A i j) * MvPolynomial.X j) =
        ((A.map MvPolynomial.C *ᵥ MvPolynomial.X) i) := by
      rw [mulVec_apply_eq_sum]
      rfl
    rw [hp]
    rw [← MvPolynomial.coe_eval₂Hom, RingHom.map_mulVec]
    simp [Function.comp_def]
  have hs := (hasSum_restrictedAnalyticSubst g hg f).map (restrictedEval₂ φ x hφ hx)
    (continuous_restrictedEval₂ φ x hφ hx)
  have ht := hasSum_restrictedEval₂ φ (A.map φ *ᵥ x) hφ
    (A.norm_map_mulVec_le φ hA x hφ hx) f
  apply HasSum.unique hs
  convert ht using 1
  funext t
  rw [TauCeti.Huber.weightedEvalTerm_def]
  simp only [Function.comp_apply, map_mul, map_prod, map_pow, restrictedEval₂_algebraMap,
    congrFun h]

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
    have ha' : a = (u : Matrix (Fin k) (Fin k) R).map C *ᵥ X := by
      funext j
      simp only [a, mulVec_apply_eq_sum, Matrix.map_apply]
    have hb' : b = (↑(u⁻¹) : Matrix (Fin k) (Fin k) R).map C *ᵥ X := by
      funext j
      simp only [b, mulVec_apply_eq_sum, Matrix.map_apply]
    rw [ha', hb', subst_matrix_mulVec, u.mul_inv]
    simp
  intro f g hfg
  apply Subtype.ext
  have e := congrArg (fun f : IsRestricted.subring (R := R) s ↦
    subst b (f : MvPowerSeries (Fin k) R)) hfg
  have h' : subst b (subst a (f : MvPowerSeries (Fin k) R)) =
      subst b (subst a (g : MvPowerSeries (Fin k) R)) := by
    simpa only [coe_restrictedLinearSubst, a] using e
  simpa only [subst_comp_subst_apply ha hb, hcomp, subst_self, id_eq] using h'

end TauCeti.MvPowerSeries
