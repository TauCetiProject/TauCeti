/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Nat.Log
public import TauCeti.RingTheory.MvPowerSeries.Order
public import Mathlib.RingTheory.MvPowerSeries.PiTopology
public import Mathlib.RingTheory.MvPowerSeries.Substitution
public import TauCeti.RingTheory.PowerSeries.Exp.Padic.Subst

import Mathlib.Analysis.Normed.Algebra.Ultra
import TauCeti.Data.Nat.Pow
import TauCeti.RingTheory.MvPowerSeries.NormCoeff
import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Subst

/-!
# Couplings and normal form of `p`-adic multivariate power series

For an integer `p > 1`, finite index types `Φ` and `c`, and a partner rule `pr : ℕ → Φ → Φ`, the
`e`-th coupling is `Γ_e = ∑ x : Φ × c, X x ^ p ^ e * X (pr e x.1, x.2)`, homogeneous of degree
`p ^ e + 1`. Given `S : Set ℕ` and coefficients `l : ℕ → ℕ → R` in a topological commutative ring,
the formal sum `Ξ = ∑_{e ∈ S} ∑_j l e j • Γ_e ^ p ^ j` converges coefficientwise.

For a prime `p` and a normed field `K` extending `ℚ_[p]`, a series `F : MvPowerSeries (Φ × c) K`
has **normal form** `HasNormalForm p S pr ϖ l F` if
`F(ϖ z) = W * exp ((ϖ ^ (p + 1) / p) • Ξ)` for an integral series `W` (`∀ d, ‖coeff d W‖ ≤ 1`).

## Main definitions and results

* `MvPowerSeries.coupling`, `MvPowerSeries.couplingSum`, `MvPowerSeries.HasNormalForm`.
* `MvPowerSeries.HasNormalForm.exists_subst_eq_mul_exp`, `MvPowerSeries.HasNormalForm.rescale`,
  `MvPowerSeries.HasNormalForm.exists_of_norm_eq`: substitution, rescaling, and dependence on `‖ϖ‖`.
* `MvPowerSeries.HasNormalForm.norm_coeff_subst_le_one`: if `F` has normal form with integral `l`,
  `0 ≤ r ≤ 1`, `‖ϖ ^ (p + 1) / p‖ * r ≤ p ^ (-(p - 1)⁻¹)`, and `Z` is an integral substitution
  without constant term whose couplings `Γ_e(Z)` have norm at most `r` up to degree `B` for `e ∈ S`
  with `e ≤ p.log B`, then `F(ϖ Z)` is integral in degrees at most `B`.

## References

* L. Alpöge, `New.coupling`, `New.couplingSum`, and `New.HasNormalForm` in
  `src/New/Derivatives/Divisibility/NormalForm.lean`,
  <https://github.com/leanprover-community/riemann-hypothesis/tree/dba5aded4bf7>.
-/

public section

open MvPowerSeries WithPiTopology

namespace MvPowerSeries

section Coupling

variable {R : Type*} [CommRing R] {Φ c : Type*} [Fintype Φ] [Fintype c]

/-- The coupling `Γ_e = ∑ x : Φ × c, X x ^ p ^ e * X (pr e x.1, x.2)`. -/
noncomputable def coupling (p : ℕ) (pr : ℕ → Φ → Φ) (e : ℕ) : MvPowerSeries (Φ × c) R :=
  ∑ x : Φ × c, X x ^ p ^ e * X (pr e x.1, x.2)

/-- Definitional unfolding of `MvPowerSeries.coupling`. -/
theorem coupling_def (p : ℕ) (pr : ℕ → Φ → Φ) (e : ℕ) :
    (coupling p pr e : MvPowerSeries (Φ × c) R) =
      ∑ x : Φ × c, X x ^ p ^ e * X (pr e x.1, x.2) := by rfl

/-- The formal sum `Ξ = ∑_{e ∈ S} ∑_j l e j • Γ_e ^ p ^ j` in the coefficientwise topology. -/
noncomputable def couplingSum [TopologicalSpace R] (p : ℕ) (S : Set ℕ) (pr : ℕ → Φ → Φ)
    (l : ℕ → ℕ → R) : MvPowerSeries (Φ × c) R :=
  ∑' x : S × ℕ, l x.1 x.2 • coupling p pr x.1 ^ p ^ x.2

/-- Definitional unfolding of `MvPowerSeries.couplingSum`. -/
theorem couplingSum_def [TopologicalSpace R] (p : ℕ) (S : Set ℕ) (pr : ℕ → Φ → Φ)
    (l : ℕ → ℕ → R) :
    (couplingSum p S pr l : MvPowerSeries (Φ × c) R) =
      ∑' x : S × ℕ, l x.1 x.2 • coupling p pr x.1 ^ p ^ x.2 := by rfl

/-- Substituting `Z` into `coupling p pr e`. -/
theorem subst_coupling {p : ℕ} {pr : ℕ → Φ → Φ} {τ : Type*} {Z : Φ × c → MvPowerSeries τ R}
    (hZ : HasSubst Z) (e : ℕ) :
    (coupling p pr e : MvPowerSeries (Φ × c) R).subst Z =
      ∑ x : Φ × c, Z x ^ p ^ e * Z (pr e x.1, x.2) := by
  simp only [coupling_def, ← coe_substAlgHom hZ, map_sum, map_mul, map_pow, substAlgHom_X]

/-- The coupling `Γ_e` is homogeneous of degree `p ^ e + 1`. -/
theorem rescale_coupling {p : ℕ} {pr : ℕ → Φ → Φ} (α : R) (e : ℕ) :
    rescale (fun _ : Φ × c ↦ α) (coupling p pr e : MvPowerSeries (Φ × c) R) =
      α ^ (p ^ e + 1) • coupling p pr e := by
  rw [rescale_eq_subst, subst_coupling (HasSubst.smul_X _), coupling_def, Finset.smul_sum]
  simp only [Pi.smul_apply', smul_pow, smul_mul_smul_comm, pow_succ]

/-- The constant coefficient of `coupling p pr e` is `0`. -/
@[simp]
theorem constantCoeff_coupling {p : ℕ} {pr : ℕ → Φ → Φ} (e : ℕ) :
    constantCoeff (coupling p pr e : MvPowerSeries (Φ × c) R) = 0 := by
  simp [coupling_def]

/-- The coupling `Γ_e` has order at least `p ^ e + 1`. -/
theorem le_order_coupling {p : ℕ} {pr : ℕ → Φ → Φ} (e : ℕ) :
    ((p ^ e + 1 : ℕ) : ℕ∞) ≤ (coupling p pr e : MvPowerSeries (Φ × c) R).order := by
  refine le_order fun d hd ↦ ?_
  rw [coupling_def, map_sum]
  refine Finset.sum_eq_zero fun x _ ↦ coeff_of_lt_order (hd.trans_le ?_)
  have h2 : (1 : ℕ∞) ≤ (X (pr e x.1, x.2) : MvPowerSeries (Φ × c) R).order :=
    one_le_order_iff_constCoeff_eq_zero.2 (constantCoeff_X _)
  have hpow : ((p ^ e : ℕ) : ℕ∞) ≤ (X x ^ p ^ e : MvPowerSeries (Φ × c) R).order :=
    le_order_pow_of_constantCoeff_eq_zero (p ^ e) (constantCoeff_X (R := R) x)
  have hsum : ((p ^ e + 1 : ℕ) : ℕ∞) ≤
      (X x ^ p ^ e : MvPowerSeries (Φ × c) R).order +
        (X (pr e x.1, x.2) : MvPowerSeries (Φ × c) R).order := by
    simpa [Nat.cast_add] using add_le_add hpow h2
  exact hsum.trans le_order_mul

/-- Substituting series without constant term into `Γ_e ^ p ^ j` has order at least
`(p ^ e + 1) * p ^ j`. -/
theorem le_order_subst_coupling_pow {p : ℕ} {pr : ℕ → Φ → Φ} {τ : Type*}
    {Z : Φ × c → MvPowerSeries τ R} (hZ : ∀ x, constantCoeff (Z x) = 0) (e j : ℕ) :
    (((p ^ e + 1) * p ^ j : ℕ) : ℕ∞) ≤
      ((coupling p pr e : MvPowerSeries (Φ × c) R).subst Z ^ p ^ j).order :=
  calc (((p ^ e + 1) * p ^ j : ℕ) : ℕ∞)
      = p ^ j • ((p ^ e + 1 : ℕ) : ℕ∞) := by rw [nsmul_eq_mul, Nat.cast_mul, mul_comm]
    _ ≤ p ^ j • ((coupling p pr e : MvPowerSeries (Φ × c) R).subst Z).order :=
        nsmul_le_nsmul_right
          ((le_order_coupling e).trans
            (order_le_order_subst (hasSubst_of_constantCoeff_zero hZ) hZ _)) _
    _ ≤ _ := le_order_pow (p ^ j)

/-- `Γ_e ^ p ^ j` has order at least `(p ^ e + 1) * p ^ j`. -/
theorem le_order_coupling_pow {p : ℕ} {pr : ℕ → Φ → Φ} (e j : ℕ) :
    (((p ^ e + 1) * p ^ j : ℕ) : ℕ∞) ≤
      ((coupling p pr e : MvPowerSeries (Φ × c) R) ^ p ^ j).order := by
  simpa [subst_self] using le_order_subst_coupling_pow (Z := X) (fun x ↦ constantCoeff_X x) e j

private lemma coeff_smul_coupling_pow_eq_zero {p : ℕ} (hp : 1 < p) {S : Set ℕ}
    {pr : ℕ → Φ → Φ} {l : ℕ → ℕ → R} {D : ℕ} {m : Φ × c →₀ ℕ} (hm : m.degree ≤ D)
    {x : S × ℕ} (hx : x ∉
      letI := Classical.decPred (· ∈ S)
      ((Finset.range (D + 1)).subtype (· ∈ S)) ×ˢ Finset.range (D + 1)) :
    coeff m (l x.1 x.2 • (coupling p pr x.1 : MvPowerSeries (Φ × c) R) ^ p ^ x.2) = 0 := by
  classical
  rcases x with ⟨⟨e, _⟩, j⟩
  simp only [Finset.mem_product, Finset.mem_subtype, Finset.mem_range, not_and_or, not_lt] at hx
  have hlt : m.degree < (p ^ e + 1) * p ^ j :=
    hm.trans_lt (Nat.lt_add_one_mul_pow_of_lt hp (hx.imp Nat.lt_of_succ_le Nat.lt_of_succ_le))
  rw [coeff_smul, coeff_of_lt_order ((Nat.cast_lt.2 hlt).trans_le (le_order_coupling_pow e j)),
    mul_zero]

/-- For every multi-index `d`, only finitely many terms of `couplingSum` have nonzero `d`-th
coefficient, so the sum converges coefficientwise in any topology on `R`. -/
theorem hasSum_couplingSum [TopologicalSpace R] {p : ℕ} (hp : 1 < p) {S : Set ℕ}
    {pr : ℕ → Φ → Φ} {l : ℕ → ℕ → R} :
    HasSum (fun x : S × ℕ ↦ l x.1 x.2 • (coupling p pr x.1 : MvPowerSeries (Φ × c) R) ^ p ^ x.2)
      (couplingSum p S pr l) := by
  classical
  rw [couplingSum_def]
  refine Summable.hasSum (WithPiTopology.summable_iff_summable_coeff.2 fun d ↦ ?_)
  exact summable_of_ne_finset_zero (s :=
    ((Finset.range (d.degree + 1)).subtype (· ∈ S)) ×ˢ Finset.range (d.degree + 1))
    fun _ hx ↦ coeff_smul_coupling_pow_eq_zero hp le_rfl hx

/-- `couplingSum p S pr l` has zero constant coefficient. -/
@[simp]
theorem constantCoeff_couplingSum [TopologicalSpace R] [T2Space R] {p : ℕ} (hp : 1 < p)
    {S : Set ℕ} {pr : ℕ → Φ → Φ} {l : ℕ → ℕ → R} :
    constantCoeff (couplingSum p S pr l : MvPowerSeries (Φ × c) R) = 0 := by
  have hp0 : p ≠ 0 := by omega
  have h0 : HasSum (fun x : S × ℕ ↦
      constantCoeff (l x.1 x.2 • (coupling p pr x.1 : MvPowerSeries (Φ × c) R) ^ p ^ x.2)) 0 := by
    convert hasSum_zero with x; simp [constantCoeff_coupling, hp0]
  exact (hasSum_iff_hasSum_coeff.1
    (hasSum_couplingSum hp (S := S) (pr := pr) (l := l)) 0).unique h0

/-- The `d`-th coefficient of `couplingSum p S pr l` equals the finite sum of the `d`-th
coefficients of the terms with `e, j ≤ d.degree`. -/
theorem coeff_couplingSum [TopologicalSpace R] [T2Space R] {p : ℕ} (hp : 1 < p) {S : Set ℕ}
    {pr : ℕ → Φ → Φ} {l : ℕ → ℕ → R} (d : Φ × c →₀ ℕ) :
    letI := Classical.decPred (· ∈ S)
    coeff d (couplingSum p S pr l : MvPowerSeries (Φ × c) R) =
      ∑ x ∈ ((Finset.range (d.degree + 1)).subtype (· ∈ S)) ×ˢ Finset.range (d.degree + 1),
        coeff d (l x.1 x.2 • (coupling p pr x.1 : MvPowerSeries (Φ × c) R) ^ p ^ x.2) := by
  classical
  exact (hasSum_iff_hasSum_coeff.1 (hasSum_couplingSum hp (S := S) (pr := pr) (l := l)) d).unique
    (hasSum_sum_of_ne_finset_zero fun _ hx ↦ coeff_smul_coupling_pow_eq_zero hp le_rfl hx)

/-- The `d`-th coefficient of `(couplingSum p S pr l).subst Z` equals the finite sum of the
`d`-th coefficients of the terms with `e, j ≤ d.degree`. -/
theorem coeff_subst_couplingSum_eq_sum [TopologicalSpace R] [T2Space R] {p : ℕ} (hp : 1 < p)
    {S : Set ℕ} {pr : ℕ → Φ → Φ} {l : ℕ → ℕ → R} {τ : Type*}
    {Z : Φ × c → MvPowerSeries τ R} (hZ : ∀ x, constantCoeff (Z x) = 0) (d : τ →₀ ℕ) :
    letI := Classical.decPred (· ∈ S)
    coeff d ((couplingSum p S pr l).subst Z) =
      ∑ x ∈ ((Finset.range (d.degree + 1)).subtype (· ∈ S)) ×ˢ Finset.range (d.degree + 1),
        coeff d (l x.1 x.2 • (coupling p pr x.1 : MvPowerSeries (Φ × c) R).subst Z ^ p ^ x.2) := by
  classical
  have hsub : HasSubst Z := hasSubst_of_constantCoeff_zero hZ
  set s := ((Finset.range (d.degree + 1)).subtype (· ∈ S)) ×ˢ Finset.range (d.degree + 1)
  have hrem : ∀ m : Φ × c →₀ ℕ, m.degree ≤ d.degree →
      coeff m (couplingSum p S pr l - ∑ x ∈ s, l x.1 x.2 • coupling p pr x.1 ^ p ^ x.2) = 0 := by
    intro m hm
    rw [map_sub, map_sum, sub_eq_zero]
    exact (hasSum_iff_hasSum_coeff.1 (hasSum_couplingSum hp (S := S) (pr := pr) (l := l)) m).unique
      (hasSum_sum_of_ne_finset_zero fun _ hx ↦ coeff_smul_coupling_pow_eq_zero hp hm hx)
  have hord0 : ((d.degree + 1 : ℕ) : ℕ∞) ≤
      (couplingSum p S pr l - ∑ x ∈ s, l x.1 x.2 • coupling p pr x.1 ^ p ^ x.2).order :=
    le_order fun m hm ↦ hrem m (Nat.lt_succ_iff.mp (Nat.cast_lt.mp hm))
  have hzero : coeff d
      ((couplingSum p S pr l - ∑ x ∈ s, l x.1 x.2 • coupling p pr x.1 ^ p ^ x.2).subst Z) = 0 :=
    coeff_of_lt_order ((Nat.cast_lt.2 (Nat.lt_succ_self d.degree)).trans_le
      (hord0.trans (order_le_order_subst hsub hZ _)))
  rw [← coe_substAlgHom hsub, map_sub, map_sum, map_sub, map_sum, sub_eq_zero] at hzero
  simpa only [coe_substAlgHom, subst_smul hsub, subst_pow hsub] using hzero

/-- Multiplying all coefficients `l e j` by a constant `a` scales `couplingSum p S pr l` by `a`. -/
theorem couplingSum_const_mul [TopologicalSpace R] [T2Space R] {p : ℕ}
    (hp : 1 < p) {S : Set ℕ} {pr : ℕ → Φ → Φ} {l : ℕ → ℕ → R} (a : R) :
    (couplingSum p S pr fun e j ↦ a * l e j : MvPowerSeries (Φ × c) R) =
      a • couplingSum p S pr l := by
  classical
  ext d
  simp only [coeff_couplingSum hp, coeff_smul, Finset.mul_sum, mul_assoc]

/-- Rescaling `couplingSum p S pr l` by `α` multiplies `l e j` by `α ^ ((p ^ e + 1) * p ^ j)`. -/
theorem rescale_couplingSum [TopologicalSpace R] [T2Space R] {p : ℕ} (hp : 1 < p)
    {S : Set ℕ} {pr : ℕ → Φ → Φ} {l : ℕ → ℕ → R} (α : R) :
    rescale (fun _ : Φ × c ↦ α) (couplingSum p S pr l : MvPowerSeries (Φ × c) R) =
      couplingSum p S pr fun e j : ℕ ↦ α ^ ((p ^ e + 1) * p ^ j) * l e j := by
  classical
  ext d
  let Z : Φ × c → MvPowerSeries (Φ × c) R :=
    (fun _ : Φ × c ↦ α) • (X : Φ × c → MvPowerSeries (Φ × c) R)
  have hterm (x : S × ℕ) :
      l x.1 x.2 • (coupling p pr x.1 : MvPowerSeries (Φ × c) R).subst Z ^ p ^ x.2 =
        (α ^ ((p ^ (x.1 : ℕ) + 1) * p ^ x.2) * l x.1 x.2) • coupling p pr x.1 ^ p ^ x.2 := by
    have hZeq : Z = (fun _ : Φ × c ↦ α) • X := rfl
    rw [hZeq, ← rescale_eq_subst, rescale_coupling, smul_pow, smul_smul, ← pow_mul,
      mul_comm (l _ _)]
  rw [rescale_eq_subst, coeff_subst_couplingSum_eq_sum hp (fun x ↦ by simp), coeff_couplingSum hp]
  simp only [Z, hterm]

end Coupling

section CouplingBound

variable {R : Type*} [NormedCommRing R] {Φ c : Type*} [Fintype Φ] [Fintype c]
  {p : ℕ} {S : Set ℕ} {pr : ℕ → Φ → Φ} {l : ℕ → ℕ → R}

/-- If `0 ≤ r ≤ 1`, `‖l e j‖ ≤ 1`, `Z` has zero constant term, and
`‖coeff d ((coupling p pr e).subst Z)‖ ≤ r` for all `e ∈ S` with `e ≤ p.log B` and `d.degree ≤ B`,
then `‖coeff d ((couplingSum p S pr l).subst Z)‖ ≤ r` for all `d.degree ≤ B`. -/
theorem norm_coeff_subst_couplingSum_le [IsUltrametricDist R] (hp : 1 < p) {τ : Type*} {r : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (hl : ∀ e j, ‖l e j‖ ≤ 1) {Z : Φ × c → MvPowerSeries τ R}
    (hZ : ∀ x, constantCoeff (Z x) = 0) {B : ℕ}
    (hΓ : ∀ e ∈ S, e ≤ p.log B → ∀ d : τ →₀ ℕ, d.degree ≤ B →
      ‖coeff d ((coupling p pr e : MvPowerSeries (Φ × c) R).subst Z)‖ ≤ r)
    {d : τ →₀ ℕ} (hd : d.degree ≤ B) :
    ‖coeff d ((couplingSum p S pr l).subst Z)‖ ≤ r := by
  classical
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  rw [coeff_subst_couplingSum_eq_sum hp hZ]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hr0 fun ⟨⟨e, he⟩, j⟩ _ ↦ ?_
  rw [coeff_smul]
  calc ‖l e j * coeff d ((coupling p pr e : MvPowerSeries (Φ × c) R).subst Z ^ p ^ j)‖
      ≤ ‖l e j‖ * ‖coeff d ((coupling p pr e : MvPowerSeries (Φ × c) R).subst Z ^ p ^ j)‖ :=
        norm_mul_le _ _
    _ ≤ 1 * ‖coeff d ((coupling p pr e : MvPowerSeries (Φ × c) R).subst Z ^ p ^ j)‖ :=
        mul_le_mul_of_nonneg_right (hl e j) (norm_nonneg _)
    _ = ‖coeff d ((coupling p pr e : MvPowerSeries (Φ × c) R).subst Z ^ p ^ j)‖ := one_mul _
    _ ≤ r := ?_
  obtain h_le | h_lt := le_or_gt e (p.log B)
  · exact MvPowerSeries.norm_coeff_pow_le_of_degree_le hr1 (hΓ e he h_le)
      (pow_ne_zero j hp0.ne') hd
  · have hdeg : d.degree < (p ^ e + 1) * p ^ j :=
      lt_of_lt_of_le
        ((hd.trans_lt (Nat.lt_pow_of_log_lt hp h_lt)).trans (Nat.lt_succ_self _))
        (Nat.le_mul_of_pos_right _ (pow_pos hp0 j))
    rw [coeff_of_lt_order ((Nat.cast_lt.2 hdeg).trans_le (le_order_subst_coupling_pow hZ e j)),
      norm_zero]
    exact hr0

end CouplingBound

section NormalForm

variable {p : ℕ} [Fact p.Prime] {K : Type*} [NormedField K] [Algebra ℚ K] [NormedAlgebra ℚ_[p] K]
  {Φ c : Type*} [Fintype Φ] [Fintype c]

/-- `F` has the normal form `F(ϖ z) = W * exp ((ϖ ^ (p + 1) / p) • Ξ)` with `W` integral. -/
def HasNormalForm (p : ℕ) (S : Set ℕ) (pr : ℕ → Φ → Φ) (ϖ : K) (l : ℕ → ℕ → K)
    (F : MvPowerSeries (Φ × c) K) : Prop :=
  ∃ W : MvPowerSeries (Φ × c) K, (∀ d, ‖coeff d W‖ ≤ 1) ∧
    F.rescale (fun _ : Φ × c ↦ ϖ) =
      W * (PowerSeries.exp K).subst ((ϖ ^ (p + 1) / p) • couplingSum p S pr l)

omit [Fact p.Prime] [NormedAlgebra ℚ_[p] K] in
/-- Definitional unfolding of `MvPowerSeries.HasNormalForm`. -/
theorem hasNormalForm_iff {S : Set ℕ} {pr : ℕ → Φ → Φ} {ϖ : K} {l : ℕ → ℕ → K}
    {F : MvPowerSeries (Φ × c) K} :
    HasNormalForm p S pr ϖ l F ↔
      ∃ W : MvPowerSeries (Φ × c) K, (∀ d, ‖coeff d W‖ ≤ 1) ∧
        F.rescale (fun _ : Φ × c ↦ ϖ) =
          W * (PowerSeries.exp K).subst ((ϖ ^ (p + 1) / p) • couplingSum p S pr l) :=
  Iff.rfl

variable {S : Set ℕ} {pr : ℕ → Φ → Φ} {ϖ : K} {l : ℕ → ℕ → K} {F : MvPowerSeries (Φ × c) K}

omit [Fact p.Prime] [NormedAlgebra ℚ_[p] K] in
/-- Substituting integral `Z` without constant term into `F(ϖ z)` preserves the normal form
factorization. -/
theorem HasNormalForm.exists_subst_eq_mul_exp [IsUltrametricDist K] (hp : 1 < p)
    (hF : HasNormalForm p S pr ϖ l F) {τ : Type*} {Z : Φ × c → MvPowerSeries τ K}
    (hZ_int : ∀ x d, ‖coeff d (Z x)‖ ≤ 1) (hZ : ∀ x, constantCoeff (Z x) = 0) :
    ∃ W : MvPowerSeries τ K, (∀ d, ‖coeff d W‖ ≤ 1) ∧
      F.subst (fun x : Φ × c ↦ ϖ • Z x) =
        W * (PowerSeries.exp K).subst ((ϖ ^ (p + 1) / p) • (couplingSum p S pr l).subst Z) := by
  classical
  obtain ⟨W, hW_int, hW⟩ := hF
  have hsub : HasSubst Z := hasSubst_of_constantCoeff_zero hZ
  have h_rescale : F.subst (fun x : Φ × c ↦ ϖ • Z x) = (F.rescale fun _ ↦ ϖ).subst Z := by
    rw [rescale_eq_subst, subst_comp_subst_apply (HasSubst.smul_X _) hsub]
    simp only [Pi.smul_apply', subst_smul hsub, subst_X hsub]
  refine ⟨W.subst Z, fun d ↦ ?_, ?_⟩
  · refine MvPowerSeries.norm_coeff_subst_le hsub W d zero_le_one fun m ↦ ?_
    rw [norm_mul]
    have hprod : ‖coeff d (m.prod fun x k ↦ Z x ^ k)‖ ≤ 1 := by
      have h1 := MvPowerSeries.norm_coeff_prod_le_prod_pow (s := fun _ : τ ↦ (1 : ℝ))
        (fun _ ↦ zero_le_one) (S := m.support) (f := fun x ↦ Z x ^ m x) (fun x _ t ↦ by
          simpa [Finsupp.prod] using MvPowerSeries.norm_coeff_pow_le_prod_pow
            (s := fun _ : τ ↦ (1 : ℝ)) (fun _ ↦ zero_le_one)
            (fun u ↦ by simpa [Finsupp.prod] using hZ_int x u) (m x) t) d
      simpa [Finsupp.prod] using h1
    exact (mul_le_mul (hW_int m) hprod (norm_nonneg _) zero_le_one).trans_eq (mul_one 1)
  · rw [h_rescale, hW, subst_mul hsub]
    congr 1
    have h0 : constantCoeff ((ϖ ^ (p + 1) / p) •
        (couplingSum p S pr l : MvPowerSeries (Φ × c) K)) = 0 := by
      rw [← coeff_zero_eq_constantCoeff, coeff_smul, coeff_zero_eq_constantCoeff,
        constantCoeff_couplingSum hp, mul_zero]
    have hcomp := subst_comp_subst_apply
      (PowerSeries.HasSubst.of_constantCoeff_zero h0).const hsub (PowerSeries.exp K)
    simpa only [PowerSeries.subst, Function.const_apply, subst_smul hsub] using hcomp

omit [Fact p.Prime] [NormedAlgebra ℚ_[p] K] in
/-- Rescaling `F` by an integral scalar `α` (`‖α‖ ≤ 1`) preserves the normal form. -/
theorem HasNormalForm.rescale [IsUltrametricDist K] (hp : 1 < p)
    (hF : HasNormalForm p S pr ϖ l F) {α : K} (hα : ‖α‖ ≤ 1) :
    HasNormalForm p S pr ϖ (fun e j : ℕ ↦ α ^ ((p ^ e + 1) * p ^ j) * l e j)
      (F.rescale fun _ : Φ × c ↦ α) := by
  classical
  let Z : Φ × c → MvPowerSeries (Φ × c) K := fun x ↦ α • X x
  have h_subst : (F.rescale fun _ ↦ α).rescale (fun _ ↦ ϖ) = F.subst fun x ↦ ϖ • Z x := by
    rw [rescale_rescale, rescale_eq_subst]
    congr! with x; simp [Z, smul_smul, mul_comm]
  rw [hasNormalForm_iff, h_subst, ← rescale_couplingSum hp,
    rescale_eq_subst _ (couplingSum p S pr l)]
  refine hF.exists_subst_eq_mul_exp hp (fun x d ↦ ?_) (fun x ↦ by simp [Z])
  simp only [Z, coeff_smul, coeff_X]
  split_ifs <;> simp [hα]

omit [Fact p.Prime] [NormedAlgebra ℚ_[p] K] in
/-- Existence of a normal form depends only on `‖ϖ‖`. -/
theorem HasNormalForm.exists_of_norm_eq [IsUltrametricDist K] (hp : 1 < p)
    (hF : HasNormalForm p S pr ϖ l F) {ϖ' : K} (h_norm : ‖ϖ'‖ = ‖ϖ‖) :
    ∃ l' : ℕ → ℕ → K, HasNormalForm p S pr ϖ' l' F := by
  rcases eq_or_ne ϖ 0 with rfl | hϖ
  · have hϖ' : ϖ' = 0 := norm_eq_zero.1 (h_norm.trans norm_zero)
    exact ⟨l, hϖ' ▸ hF⟩
  have hϖ' : ϖ' ≠ 0 := by rwa [← norm_ne_zero_iff, h_norm, norm_ne_zero_iff]
  let α : K := ϖ' / ϖ; let β : K := ϖ / ϖ'
  have hα : ‖α‖ ≤ 1 := by simp [α, h_norm, hϖ]
  let l₁ (e j : ℕ) : K := α ^ ((p ^ e + 1) * p ^ j) * l e j
  have h_scale : (fun _ : Φ × c ↦ ϖ') = (fun _ ↦ α) * fun _ ↦ ϖ :=
    funext fun _ ↦ (div_mul_cancel₀ ϖ' hϖ).symm
  have h_const : ϖ' ^ (p + 1) / p * β ^ (p + 1) = ϖ ^ (p + 1) / p := by
    simp [β, div_mul_eq_mul_div, ← mul_pow, mul_div_cancel₀ ϖ hϖ']
  obtain ⟨W, hW_int, hW⟩ := hF.rescale hp hα
  refine ⟨fun e j ↦ β ^ (p + 1) * l₁ e j, W, hW_int, ?_⟩
  rw [couplingSum_const_mul hp, smul_smul, h_const, ← hW, rescale_rescale, h_scale]

/-- If `F` has normal form with integral `l`, `0 ≤ r ≤ 1`,
`‖ϖ ^ (p + 1) / p‖ * r ≤ p ^ (-(p - 1)⁻¹)`, and `Z` is an integral substitution without constant
term whose couplings `Γ_e(Z)` have norm at most `r` up to degree `B` for `e ∈ S` with
`e ≤ p.log B`, then `F(ϖ Z)` is integral in degrees at most `B`. -/
theorem HasNormalForm.norm_coeff_subst_le_one (hF : HasNormalForm p S pr ϖ l F)
    (hl : ∀ e j, ‖l e j‖ ≤ 1) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hr : ‖ϖ ^ (p + 1) / p‖ * r ≤ (p : ℝ) ^ (-(p - 1 : ℝ)⁻¹)) {τ : Type*}
    {Z : Φ × c → MvPowerSeries τ K} (hZ_int : ∀ x d, ‖coeff d (Z x)‖ ≤ 1)
    (hZ : ∀ x, constantCoeff (Z x) = 0) {B : ℕ}
    (hΓ : ∀ e ∈ S, e ≤ p.log B → ∀ d : τ →₀ ℕ, d.degree ≤ B →
      ‖coeff d ((coupling p pr e : MvPowerSeries (Φ × c) K).subst Z)‖ ≤ r)
    {m : τ →₀ ℕ} (hm : m.degree ≤ B) :
    ‖coeff m (F.subst fun x : Φ × c ↦ ϖ • Z x)‖ ≤ 1 := by
  have : IsUltrametricDist K := .of_normedAlgebra ℚ_[p]
  have hp : 1 < p := (Fact.out : p.Prime).one_lt
  set Ξ : MvPowerSeries τ K := (couplingSum p S pr l).subst Z
  have hΞ0 : constantCoeff Ξ = 0 :=
    constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero hZ) hZ
      (constantCoeff_couplingSum hp)
  obtain ⟨W, hW_int, hW⟩ := hF.exists_subst_eq_mul_exp hp hZ_int hZ
  rw [hW]
  have h1 := MvPowerSeries.norm_coeff_mul_mul_prod_le (c := fun _ : τ ↦ (1 : ℝ))
    (fun _ ↦ zero_le_one) (f := W) (g := (PowerSeries.exp K).subst ((ϖ ^ (p + 1) / p) • Ξ))
    (n := m) (r := 1) (s := 1)
    (fun d _ ↦ by simpa [Finsupp.prod] using hW_int d)
    (fun d hd ↦ by
      simpa [Finsupp.prod] using PowerSeries.norm_coeff_subst_exp_smul_le_one hr hΞ0
        (fun u hu ↦ norm_coeff_subst_couplingSum_le hp hr0 hr1 hl hZ hΓ hu)
        ((Finsupp.degree_mono hd).trans hm))
  simpa [Finsupp.prod] using h1

end NormalForm

end MvPowerSeries
