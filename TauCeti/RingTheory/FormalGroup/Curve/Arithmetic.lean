/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.FormalGroup.Curve.Basic
import TauCeti.RingTheory.MvPowerSeries.Equiv
import TauCeti.RingTheory.PowerSeries.Expand
import TauCeti.RingTheory.PowerSeries.Substitution

/-!
# Arithmetic of curves

For the additive formal group, forgetting a curve preserves addition of power series.
For any commutative formal group, multiplication by an invertible natural number is an
additive automorphism of curves. Its inverse supplies division by that number even when the
formal group law does not give a scalar action of the coefficient ring. These arithmetic maps
support normalized Cartier operators on curves. Verschiebung `Vₙ` (the substitution of `X^n`
for the curve parameter `X`) is injective for every nonzero index `n`, without commutativity of
the formal group law or a unit assumption on the index.

Curve operations also respect degree-by-degree truncation: the degree-`k` coefficients of
`V_n γ`, `f_n γ`, and `f_* γ` depend only on the coefficients of `γ` up to degrees `k / n`,
`k * n`, and `k`, respectively.
-/

public section

namespace FormalGroup

variable {R S : Type*} [CommRing R] [CommRing S]

namespace Curve

/-- Forgetting a curve on the additive formal group preserves addition of power series. -/
noncomputable def additiveToPowerSeriesHom : (𝔾ₐ (R := R)).Curve →+ PowerSeries R where
  toFun := toPowerSeries
  map_zero' := toPowerSeries_zero
  map_add' := toPowerSeries_add_𝔾ₐ

@[simp]
theorem additiveToPowerSeriesHom_apply (γ : (𝔾ₐ (R := R)).Curve) :
    additiveToPowerSeriesHom γ = γ.toPowerSeries := (rfl)

end Curve

/-! ### Division by invertible natural numbers -/

section CurveDivision

variable (F : FormalGroup R) [F.IsComm]

/-- Multiplication by an invertible natural number is an automorphism of the group of curves
on a commutative formal group law. -/
noncomputable def nsmulCurveEquiv (n : ℕ) (hunit : IsUnit (n : R)) : F.Curve ≃+ F.Curve :=
  ((F.nsmulHom n).toIso (by simpa using hunit)).curveEquiv

@[simp]
theorem nsmulCurveEquiv_apply (n : ℕ) (hunit : IsUnit (n : R)) (γ : F.Curve) :
    F.nsmulCurveEquiv n hunit γ = n • γ := by
  simp [nsmulCurveEquiv]

@[simp]
theorem nsmulCurveEquiv_one (hunit : IsUnit ((1 : ℕ) : R)) :
    F.nsmulCurveEquiv 1 hunit = AddEquiv.refl F.Curve := by
  ext γ
  simp

@[simp]
theorem nsmul_nsmulCurveEquiv_symm (n : ℕ) (hunit : IsUnit (n : R)) (γ : F.Curve) :
    n • (F.nsmulCurveEquiv n hunit).symm γ = γ := by
  simpa only [nsmulCurveEquiv_apply] using (F.nsmulCurveEquiv n hunit).apply_symm_apply γ

@[simp]
theorem nsmulCurveEquiv_symm_nsmul (n : ℕ) (hunit : IsUnit (n : R)) (γ : F.Curve) :
    (F.nsmulCurveEquiv n hunit).symm (n • γ) = γ := by
  simpa only [nsmulCurveEquiv_apply] using (F.nsmulCurveEquiv n hunit).symm_apply_apply γ

/-- An additive map between groups of curves on commutative formal group laws commutes with
division by an invertible natural number. The source and target coefficient rings may differ. -/
theorem map_nsmulCurveEquiv_symm {G : FormalGroup S} [G.IsComm]
    (f : F.Curve →+ G.Curve) (n : ℕ) (hR : IsUnit (n : R)) (hS : IsUnit (n : S))
    (γ : F.Curve) :
    f ((F.nsmulCurveEquiv n hR).symm γ) =
      (G.nsmulCurveEquiv n hS).symm (f γ) := by
  apply (G.nsmulCurveEquiv n hS).injective
  rw [nsmulCurveEquiv_apply, nsmulCurveEquiv_apply, ← map_nsmul,
    nsmul_nsmulCurveEquiv_symm, nsmul_nsmulCurveEquiv_symm]

end CurveDivision

/-- Verschiebung of any nonzero index is injective on curves. -/
theorem verschiebungCurve_injective (F : FormalGroup R) (n : ℕ) (hn : n ≠ 0) :
    Function.Injective (F.verschiebungCurve n hn) := by
  intro γ δ h
  apply Curve.ext
  apply PowerSeries.expand_injective n hn
  simpa only [toPowerSeries_verschiebungCurve] using congrArg Curve.toPowerSeries h

/-! ### Degree-by-degree truncation of curve operators -/

/-- The degree-`≤ M` coefficients of the symmetric formal-group sum `∑ i : σ, γ(Tᵢ)` depend only
on the coefficients of `γ` up to degree `M`. -/
theorem Curve.coeff_symmSum_congr (F : FormalGroup R) [F.IsComm] (σ : Type*) [Fintype σ]
    {γ₁ γ₂ : F.Curve} {M : ℕ}
    (h : ∀ i ≤ M, PowerSeries.coeff i γ₁.toPowerSeries = PowerSeries.coeff i γ₂.toPowerSeries)
    {d : σ →₀ ℕ} (hd : d.degree ≤ M) :
    MvPowerSeries.coeff d (Curve.symmSum F σ γ₁ : MvPowerSeries σ R) =
      MvPowerSeries.coeff d (Curve.symmSum F σ γ₂ : MvPowerSeries σ R) := by
  classical
  have hzero_single (γ : F.Curve) (a : σ) :
      MvPowerSeries.constantCoeff (Curve.coordPointHom F a γ).val = 0 := by
    rw [Curve.val_coordPointHom, PowerSeries.toMvPowerSeries_apply,
      MvPowerSeries.constantCoeff_rename]
    exact γ.constantCoeff_toPowerSeries
  have hzero (γ : F.Curve) (s : Finset σ) :
      MvPowerSeries.constantCoeff (∑ a ∈ s, Curve.coordPointHom F a γ).val = 0 :=
    Finset.sum_induction _ (fun x : F.Point σ ↦ MvPowerSeries.constantCoeff x.val = 0)
      (fun x y hx hy ↦ MvPowerSeries.constantCoeff_subst_eq_zero
        (MvPowerSeries.hasSubst_of_constantCoeff_zero (Fin.forall_fin_two.mpr ⟨hx, hy⟩))
        (Fin.forall_fin_two.mpr ⟨hx, hy⟩) F.zero_constantCoeff)
      (by simp [zero_apply]) (fun a _ ↦ hzero_single γ a)
  have hcoord (a : σ) : ((M + 1 : ℕ) : ℕ∞) ≤
      ((Curve.coordPointHom F a γ₁).val - (Curve.coordPointHom F a γ₂).val).order :=
    MvPowerSeries.nat_le_order fun e he ↦ by
      rw [map_sub, Curve.val_coordPointHom, Curve.val_coordPointHom,
        PowerSeries.coeff_toMvPowerSeries, PowerSeries.coeff_toMvPowerSeries]
      split_ifs with hea
      · exact sub_eq_zero.mpr (h (e a) ((Finsupp.le_degree a e).trans (Nat.lt_succ_iff.mp he)))
      · exact sub_self 0
  have hsum (s : Finset σ) : ((M + 1 : ℕ) : ℕ∞) ≤
      ((∑ a ∈ s, Curve.coordPointHom F a γ₁).val -
        (∑ a ∈ s, Curve.coordPointHom F a γ₂).val).order := by
    induction s using Finset.induction_on with
    | empty => simp [zero_apply]
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, add_apply, add_apply]
      refine MvPowerSeries.nat_le_order fun e he ↦ ?_
      rw [F.coeff_subst_sub_subst_of_degree_le (hzero_single γ₁ a) (hzero_single γ₂ a)
        (hzero γ₁ s) (hzero γ₂ s) (hcoord a) ih he.le,
        MvPowerSeries.coeff_of_lt_order ((Nat.cast_lt.mpr he).trans_le (hcoord a)),
        MvPowerSeries.coeff_of_lt_order ((Nat.cast_lt.mpr he).trans_le ih), _root_.add_zero]
  have hlt : (d.degree : ℕ∞) < ((M + 1 : ℕ) : ℕ∞) := Nat.cast_lt.mpr (Nat.lt_succ_of_le hd)
  rw [Curve.coe_symmSum, Curve.coe_symmSum]
  exact sub_eq_zero.mp <| by
    rw [← map_sub]
    exact MvPowerSeries.coeff_of_lt_order (hlt.trans_le (hsum Finset.univ))

/-- The degree-`k` coefficient of `V_n γ` depends only on the coefficients of `γ` up to degree
`k / n`. -/
theorem coeff_verschiebungCurve_congr (F : FormalGroup R) (n : ℕ) (hn : n ≠ 0)
    {γ₁ γ₂ : F.Curve} {k : ℕ}
    (h : ∀ i ≤ k / n, PowerSeries.coeff i γ₁.toPowerSeries = PowerSeries.coeff i γ₂.toPowerSeries) :
    PowerSeries.coeff k (F.verschiebungCurve n hn γ₁).toPowerSeries =
      PowerSeries.coeff k (F.verschiebungCurve n hn γ₂).toPowerSeries := by
  simp only [toPowerSeries_verschiebungCurve, PowerSeries.coeff_expand]
  split_ifs with hdvd
  · exact h (k / n) le_rfl
  · rfl

/-- The degree-`k` coefficient of `f_n γ` depends only on the coefficients of `γ` up to degree
`k * n`. -/
theorem coeff_frobeniusCurve_congr (F : FormalGroup R) [F.IsComm] (n : ℕ) (hn : n ≠ 0)
    {γ₁ γ₂ : F.Curve} {k : ℕ}
    (h : ∀ i ≤ k * n, PowerSeries.coeff i γ₁.toPowerSeries = PowerSeries.coeff i γ₂.toPowerSeries) :
    PowerSeries.coeff k (F.frobeniusCurve n hn γ₁).toPowerSeries =
      PowerSeries.coeff k (F.frobeniusCurve n hn γ₂).toPowerSeries := by
  rw [toPowerSeries_frobeniusCurve, toPowerSeries_frobeniusCurve,
    MvPowerSeries.symmetricSubalgebra.coeff_evalTopEsymm,
    MvPowerSeries.symmetricSubalgebra.coeff_evalTopEsymm, Fintype.card_fin]
  refine congrArg (fun P ↦ (MvPolynomial.symmetricSubalgebra.evalTopEsymm (Fin n) R P).coeff k)
    (Subtype.ext <| MvPolynomial.coe_inj.mp <| MvPowerSeries.ext fun d ↦ ?_)
  rw [MvPowerSeries.coe_homogeneousComponentPolynomial,
    MvPowerSeries.coe_homogeneousComponentPolynomial,
    MvPowerSeries.coeff_homogeneousComponent, MvPowerSeries.coeff_homogeneousComponent]
  split_ifs with hd
  · exact Curve.coeff_symmSum_congr F (Fin n) h hd.le
  · rfl

/-- The degree-`k` coefficient of `f.mapCurve γ` depends only on the coefficients of `γ` up to
degree `k`. -/
theorem _root_.TauCeti.FormalGroupHom.coeff_mapCurve_congr {F G : FormalGroup R}
    (f : TauCeti.FormalGroupHom F G) {γ₁ γ₂ : F.Curve} {k : ℕ}
    (h : ∀ i ≤ k, PowerSeries.coeff i γ₁.toPowerSeries = PowerSeries.coeff i γ₂.toPowerSeries) :
    PowerSeries.coeff k (f.mapCurve γ₁).toPowerSeries =
      PowerSeries.coeff k (f.mapCurve γ₂).toPowerSeries := by
  rw [TauCeti.FormalGroupHom.toPowerSeries_mapCurve,
    TauCeti.FormalGroupHom.toPowerSeries_mapCurve,
    ← PowerSeries.coeff_trunc_comp_trunc f.toPowerSeries γ₁.constantCoeff_toPowerSeries
      (Nat.lt_succ_self k) (Nat.lt_succ_self k),
    ← PowerSeries.coeff_trunc_comp_trunc f.toPowerSeries γ₂.constantCoeff_toPowerSeries
      (Nat.lt_succ_self k) (Nat.lt_succ_self k)]
  have htrunc : PowerSeries.trunc (k + 1) γ₁.toPowerSeries =
      PowerSeries.trunc (k + 1) γ₂.toPowerSeries := by
    ext i
    rw [PowerSeries.coeff_trunc, PowerSeries.coeff_trunc]
    split_ifs with hi
    · exact h i (Nat.lt_succ_iff.mp hi)
    · rfl
  rw [htrunc]

end FormalGroup
