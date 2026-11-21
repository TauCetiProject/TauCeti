/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.FormalGroup.Curve.Basic
import TauCeti.RingTheory.FormalGroup.Basic
import TauCeti.RingTheory.FormalGroup.Point.Order
import TauCeti.RingTheory.MvPowerSeries.Equiv
import TauCeti.RingTheory.PowerSeries.Expand

/-!
# Arithmetic of curves

For the additive formal group, forgetting a curve preserves addition of power series.
Finite-order agreement of formal group laws and curves is preserved by curve addition and finite
curve sums (`FormalGroup.Curve.le_order_add_sub`, `FormalGroup.Curve.le_order_sum_sub`).
Monomial curves `c Tⁿ` (`n ≠ 0`, `FormalGroup.monomialCurve`) provide the elementary summands in
curve expansions such as Ravenel's modulo-`p` `[p]`-series formula, and commute with base change
(`FormalGroup.map_monomialCurve`, `FormalGroup.map_toPowerSeries_sum_monomialCurve`) and
Verschiebung. For any commutative formal group, multiplication by an invertible natural number
is an additive automorphism of curves. Its inverse supplies division by that number even when the
formal group law does not give a scalar action of the coefficient ring. These arithmetic maps
support normalized Cartier operators on curves. Verschiebung `Vₙ` (the substitution of `X^n`
for the curve parameter `X`) is injective for every nonzero index `n`, without commutativity of
the formal group law or a unit assumption on the index.

Curve operations also respect degree-by-degree truncation: the degree-`≤ M` coefficients of a
symmetric formal-group sum `∑ i : σ, γ(Tᵢ)` depend only on the coefficients of `γ` up to degree
`M` (`FormalGroup.Curve.coeff_symmSum_congr`), and the degree-`k` coefficient of `V_n γ` depends
only on those up to degree `k / n` (`FormalGroup.coeff_verschiebungCurve_congr`).
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

/-- If formal group laws `F` and `G` agree below degree `M`, and curves `γ₁, γ₂` on `F` agree
below degree `M` with curves `δ₁, δ₂` on `G`, then `γ₁ + γ₂` and `δ₁ + δ₂` agree below degree
`M`. -/
theorem le_order_add_sub {F G : FormalGroup R} {M : ℕ}
    (hFG : (M : ℕ∞) ≤ (F.toPowerSeries - G.toPowerSeries).order)
    {γ₁ γ₂ : F.Curve} {δ₁ δ₂ : G.Curve}
    (h₁ : (M : ℕ∞) ≤ (γ₁.toPowerSeries - δ₁.toPowerSeries).order)
    (h₂ : (M : ℕ∞) ≤ (γ₂.toPowerSeries - δ₂.toPowerSeries).order) :
    (M : ℕ∞) ≤ ((γ₁ + γ₂).toPowerSeries - (δ₁ + δ₂).toPowerSeries).order := by
  rw [toPowerSeries_add, toPowerSeries_add, PowerSeries.order_eq_order]
  exact le_order_subst_pair_sub hFG
    (by rw [← PowerSeries.constantCoeff_eq]; exact γ₁.constantCoeff_toPowerSeries)
    (by rw [← PowerSeries.constantCoeff_eq]; exact γ₂.constantCoeff_toPowerSeries)
    (by rw [← PowerSeries.constantCoeff_eq]; exact δ₁.constantCoeff_toPowerSeries)
    (by rw [← PowerSeries.constantCoeff_eq]; exact δ₂.constantCoeff_toPowerSeries)
    (by rwa [← PowerSeries.order_eq_order]) (by rwa [← PowerSeries.order_eq_order])

/-- If commutative formal group laws `F` and `G` agree below degree `M`, and finite families of
curves `γ` on `F` and `δ` on `G` agree below degree `M` at every index in `I`, then their
formal-group sums agree below degree `M`. -/
theorem le_order_sum_sub {ι : Type*} {F G : FormalGroup R} [F.IsComm] [G.IsComm] {M : ℕ}
    (hFG : (M : ℕ∞) ≤ (F.toPowerSeries - G.toPowerSeries).order)
    (I : Finset ι) (γ : ι → F.Curve) (δ : ι → G.Curve)
    (hγδ : ∀ i ∈ I, (M : ℕ∞) ≤ ((γ i).toPowerSeries - (δ i).toPowerSeries).order) :
    (M : ℕ∞) ≤ ((∑ i ∈ I, γ i).toPowerSeries - (∑ i ∈ I, δ i).toPowerSeries).order := by
  classical
  induction I using Finset.induction_on with
  | empty => simp
  | @insert a J haJ ih =>
    rw [Finset.sum_insert haJ, Finset.sum_insert haJ]
    exact le_order_add_sub hFG (hγδ a (Finset.mem_insert_self a J))
      (ih fun i hi ↦ hγδ i (Finset.mem_insert_of_mem hi))

end Curve

/-! ### Monomial curves -/

/-- The monomial curve `c Tⁿ` (`n ≠ 0`) on a formal group law `F`. -/
noncomputable def monomialCurve (F : FormalGroup R) (n : ℕ) (hn : n ≠ 0) (c : R) : F.Curve :=
  ⟨c • PowerSeries.X ^ n, by simp [zero_pow hn]⟩

/-- The underlying power series of `F.monomialCurve n hn c` is `c • X ^ n`. -/
@[simp]
theorem toPowerSeries_monomialCurve (F : FormalGroup R) (n : ℕ) (hn : n ≠ 0) (c : R) :
    (F.monomialCurve n hn c).toPowerSeries = c • PowerSeries.X ^ n := (rfl)

/-- A monomial curve with zero coefficient is the zero curve. -/
@[simp]
theorem monomialCurve_zero (F : FormalGroup R) (n : ℕ) (hn : n ≠ 0) :
    F.monomialCurve n hn 0 = 0 :=
  Curve.ext (zero_smul R _)

/-- The degree-`1` monomial curve with coefficient `1` is the tautological curve `X`. -/
@[simp]
theorem monomialCurve_one (F : FormalGroup R) :
    F.monomialCurve 1 one_ne_zero 1 = F.tautologicalCurve :=
  Curve.ext (by simp)

/-- Base change sends a monomial curve `c Tⁿ` to `(φ c) Tⁿ`. -/
@[simp]
theorem map_monomialCurve (F : FormalGroup R) (φ : R →+* S) (n : ℕ) (hn : n ≠ 0) (c : R) :
    Curve.map φ (F.monomialCurve n hn c) = (F.map φ).monomialCurve n hn (φ c) := by
  ext k
  simp [apply_ite φ]

/-- Base change along `φ : R →+* S` identifying `F.map φ = G` sends the power series of a finite
sum of monomial curves `∑ j ∈ s, (u j) T^(e j)` on `F` to `∑ j ∈ s, (v j) T^(e j)` on `G`. -/
theorem map_toPowerSeries_sum_monomialCurve {ι : Type*} {F : FormalGroup R} {G : FormalGroup S}
    [F.IsComm] [G.IsComm] (φ : R →+* S) (hFG : F.map φ = G) (s : Finset ι)
    (e : ι → ℕ) (he : ∀ j, e j ≠ 0) (u : ι → R) (v : ι → S) (huv : ∀ j ∈ s, φ (u j) = v j) :
    PowerSeries.map φ (∑ j ∈ s, F.monomialCurve (e j) (he j) (u j)).toPowerSeries =
      (∑ j ∈ s, G.monomialCurve (e j) (he j) (v j)).toPowerSeries := by
  subst hFG
  rw [← Curve.toPowerSeries_map, map_sum]
  congr 1
  exact Finset.sum_congr rfl fun j hj ↦ by rw [map_monomialCurve, huv j hj]

/-- Verschiebung `Vₘ` sends a monomial curve `c Tⁿ` to `c T^(n m)`. -/
@[simp]
theorem verschiebungCurve_monomialCurve (F : FormalGroup R) {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0)
    (c : R) :
    F.verschiebungCurve m hm (F.monomialCurve n hn c) =
      F.monomialCurve (n * m) (mul_ne_zero hn hm) c :=
  Curve.ext (by simp [← pow_mul, mul_comm])

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

/-- The degree-`k` coefficient of `(F.nsmulCurveEquiv n hunit).symm γ` depends only on the
coefficients of `γ` in degrees `≤ k`. -/
theorem coeff_nsmulCurveEquiv_symm_congr {n k : ℕ} (hunit : IsUnit (n : R))
    {γ₁ γ₂ : F.Curve}
    (h : ∀ i ≤ k, PowerSeries.coeff i γ₁.toPowerSeries = PowerSeries.coeff i γ₂.toPowerSeries) :
    PowerSeries.coeff k ((F.nsmulCurveEquiv n hunit).symm γ₁).toPowerSeries =
      PowerSeries.coeff k ((F.nsmulCurveEquiv n hunit).symm γ₂).toPowerSeries := by
  rw [nsmulCurveEquiv, TauCeti.FormalGroupIso.curveEquiv_symm_apply,
    TauCeti.FormalGroupIso.curveEquiv_symm_apply]
  exact TauCeti.FormalGroupHom.coeff_mapCurve_congr _ h

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
  have hcoord (a : σ) : ((M + 1 : ℕ) : ℕ∞) ≤
      (Curve.coordPointHom F a γ₁ - Curve.coordPointHom F a γ₂).val.order :=
    F.le_order_val_sub_of_le_order_sub (hzero_single γ₁ a) (hzero_single γ₂ a) <|
      MvPowerSeries.nat_le_order fun e he ↦ by
        rw [map_sub, Curve.val_coordPointHom, Curve.val_coordPointHom,
          PowerSeries.coeff_toMvPowerSeries, PowerSeries.coeff_toMvPowerSeries]
        split_ifs with hea
        · exact sub_eq_zero.mpr (h (e a) ((Finsupp.le_degree a e).trans (Nat.lt_succ_iff.mp he)))
        · exact sub_self 0
  have hpt : ((M + 1 : ℕ) : ℕ∞) ≤
      ((∑ a : σ, Curve.coordPointHom F a γ₁) -
        (∑ a : σ, Curve.coordPointHom F a γ₂)).val.order := by
    rw [← Finset.sum_sub_distrib]
    exact F.le_order_val_sum Finset.univ _ fun a _ ↦ hcoord a
  have hdiff := (Nat.cast_le.mpr (Nat.le_succ (M + 1))).trans
    (F.le_order_val_sub_val_sub (Nat.succ_ne_zero M)
      (Curve.constantCoeff_val_sum_coordPointHom Finset.univ γ₂) hpt)
  have hsum : ((M + 1 : ℕ) : ℕ∞) ≤
      ((∑ a : σ, Curve.coordPointHom F a γ₁).val -
        (∑ a : σ, Curve.coordPointHom F a γ₂).val).order := by
    simpa only [sub_add_cancel] using MvPowerSeries.le_order_add hdiff hpt
  have hlt : (d.degree : ℕ∞) < ((M + 1 : ℕ) : ℕ∞) := Nat.cast_lt.mpr (Nat.lt_succ_of_le hd)
  rw [Curve.coe_symmSum, Curve.coe_symmSum]
  exact sub_eq_zero.mp <| by
    rw [← map_sub]
    exact MvPowerSeries.coeff_of_lt_order (hlt.trans_le hsum)

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

end FormalGroup
