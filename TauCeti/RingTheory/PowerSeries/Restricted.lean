/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
public import Mathlib.Algebra.Polynomial.Monic
public import Mathlib.RingTheory.PowerSeries.Order
public import Mathlib.RingTheory.PowerSeries.Restricted
public import Mathlib.RingTheory.PowerSeries.Trunc
public import TauCeti.Analysis.Asymptotics.Lemmas

/-!
# Restricted power series and their coefficient algebra

Mathlib's `PowerSeries.IsRestricted` asks the weighted coefficient norms of a power series to
tend to zero. A series whose coefficients vanish in every degree past some bound — a polynomial —
satisfies that condition at every radius, and a series restricted at one radius is restricted at
every smaller one. Without any ultrametric hypothesis, products of series restricted at one
radius are restricted at every strictly smaller radius. Over an ultrametric
normed ring, constant series make the restricted subring an `S`-algebra whenever the coefficient
ring is an `S`-algebra. Scalar actions are coefficientwise, and scalar towers of the coefficients
extend to the restricted series. Over a commutative coefficient ring the polynomial inclusion is
an algebra homomorphism; it gives the comparisons used in Weierstrass division and its quotients.

## Main results

* `TauCeti.PowerSeries.isRestricted_of_forall_coeff_eq_zero`: a series with a vanishing tail is
  restricted at every radius.
* `TauCeti.PowerSeries.isRestricted_of_abs_le`: restrictedness passes to smaller radii, and
  `TauCeti.PowerSeries.isRestrictedSubring_le_of_abs_le` is the resulting containment of subrings.
* `TauCeti.PowerSeries.isRestricted_polynomial`: every polynomial is restricted, in particular
  `X - a` (`TauCeti.PowerSeries.isRestricted_X_sub_C`).
* `PowerSeries.IsRestricted.summable_norm_coeff_mul_pow`: weighted coefficient norms are
  summable strictly inside the radius of restrictedness.
* `PowerSeries.IsRestricted.mul_of_abs_lt`: over any normed ring, a product of series restricted
  at `c'` is restricted at every `c` with `|c| < |c'|`.
* `TauCeti.PowerSeries.not_isRestricted_mk_pow`: for `a ≠ 0` and a multiplicative norm, `∑ aⁿ Xⁿ`
  is not restricted at the radius `‖a‖⁻¹`, and `TauCeti.PowerSeries.not_isRestricted_mk_one`:
  over a nontrivial normed ring, `∑ Xⁿ` is not restricted at the radius `1`.
* `PowerSeries.IsRestricted.rescale`: if `f(X)` is restricted at `‖a‖ * c`, then `f(aX)`
  is restricted at `c`.
* `TauCeti.PowerSeries.coe_algebraMap_isRestrictedSubring` and
  `TauCeti.PowerSeries.coe_smul_isRestrictedSubring`: scalar maps and scalar multiplication agree
  with those on the ambient formal series.
* `TauCeti.PowerSeries.polynomialToRestricted`: the polynomial inclusion as an algebra map.
* `TauCeti.PowerSeries.exists_isUnit_isMonicOfDegree_mul_eq_of_isUnit_leadingCoeff`: move a unit
  leading coefficient from a polynomial factor to its restricted-unit cofactor.
* `PowerSeries.order_eq_of_isUnit_X_pow_mul_finprod_eq`: in `f = u * (X ^ a * ∏ᶠ m, g m)` with a
  restricted unit `u` and constant-one polynomials `g m`, `f.order = a`.
-/

public section

namespace TauCeti.PowerSeries

variable {R : Type*} [NormedRing R] {c : ℝ} {f : PowerSeries R}

/-- A power series whose coefficients vanish in every degree `≥ n` is restricted at every radius:
its weighted coefficient norms are eventually zero. Such a series is a polynomial of degree less
than `n`. -/
theorem isRestricted_of_forall_coeff_eq_zero {n : ℕ}
    (hf : ∀ m, n ≤ m → f.coeff m = 0) : f.IsRestricted c := by
  rw [PowerSeries.isRestricted_iff']
  have h : ∀ᶠ m in Filter.atTop, (0 : ℝ) = ‖f.coeff m‖ * c ^ m := by
    filter_upwards [Filter.eventually_ge_atTop n] with m hm
    simp [hf m hm]
  exact Filter.Tendsto.congr' h tendsto_const_nhds

/-- **Restrictedness passes to smaller radii.** If the weighted coefficient norms of `f` tend to
zero at the radius `c'`, they do so at every radius `c` with `|c| ≤ |c'|`, being dominated by the
former. -/
theorem isRestricted_of_abs_le {c' : ℝ} (hf : f.IsRestricted c') (h : |c| ≤ |c'|) :
    f.IsRestricted c := by
  rw [← PowerSeries.isRestricted_abs_iff, PowerSeries.isRestricted_iff'] at hf ⊢
  refine squeeze_zero (fun n ↦ by positivity) (fun n ↦ ?_) hf
  gcongr

/-- Over an ultrametric ring, the subring of series restricted at `c'` lies in the subring of
series restricted at any `c` with `|c| ≤ |c'|`. -/
theorem isRestrictedSubring_le_of_abs_le [IsUltrametricDist R] {c' : ℝ} (h : |c| ≤ |c'|) :
    PowerSeries.IsRestricted.subring (R := R) c' ≤ PowerSeries.IsRestricted.subring c :=
  fun _ hf ↦ isRestricted_of_abs_le hf h

/-- Every polynomial is restricted at every radius. -/
theorem isRestricted_polynomial (p : Polynomial R) : (p : PowerSeries R).IsRestricted c :=
  isRestricted_of_forall_coeff_eq_zero (n := p.natDegree + 1) fun m hm ↦ by
    rw [Polynomial.coeff_coe]
    exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)

/-- The linear polynomial `X - a` is restricted at every radius. -/
theorem isRestricted_X_sub_C (a : R) :
    (PowerSeries.X - PowerSeries.C a : PowerSeries R).IsRestricted c := by
  have h := (isRestricted_polynomial (c := c) (Polynomial.X : Polynomial R)).sub
    (PowerSeries.isRestricted_C c a)
  rwa [Polynomial.coe_X] at h

/-- **Rescaling changes the radius.** If `f(X)` is restricted at the radius `‖a‖ * c`, then
`f(aX)` is restricted at the radius `c`. No multiplicativity of the norm is needed: the weighted
coefficient norms of `f(aX)` are eventually dominated by those of `f`. -/
theorem _root_.PowerSeries.IsRestricted.rescale {R : Type*} [NormedCommRing R] {c : ℝ}
    {f : PowerSeries R} {a : R}
    (hf : f.IsRestricted (‖a‖ * c)) : (PowerSeries.rescale a f).IsRestricted c := by
  rw [← PowerSeries.isRestricted_abs_iff, PowerSeries.isRestricted_iff'] at hf ⊢
  refine squeeze_zero' (.of_forall fun n ↦ by positivity) ?_ hf
  filter_upwards [eventually_norm_pow_le a] with n hn
  rw [PowerSeries.coeff_rescale, abs_mul, abs_norm, mul_pow, ← mul_assoc, mul_comm _ (‖a‖ ^ n)]
  gcongr
  exact (norm_mul_le _ _).trans (by gcongr)

/-- For `a ≠ 0` over a ring with multiplicative norm, the geometric series `∑ aⁿ Xⁿ` is not
restricted at the radius `‖a‖⁻¹`: all its weighted coefficient norms there equal `1`. -/
theorem not_isRestricted_mk_pow [NormMulClass R] {a : R} (ha : a ≠ 0) :
    ¬(PowerSeries.mk fun n ↦ a ^ n).IsRestricted ‖a‖⁻¹ := by
  intro hf
  have : Nontrivial R := ⟨⟨a, 0, ha⟩⟩
  have : NormOneClass R := NormMulClass.toNormOneClass
  have h := (PowerSeries.isRestricted_iff' _ _).mp hf
  simp only [PowerSeries.coeff_mk, norm_pow, ← mul_pow, mul_inv_cancel₀ (norm_ne_zero_iff.mpr ha),
    one_pow] at h
  exact one_ne_zero (tendsto_nhds_unique tendsto_const_nhds h)

/-- Over a nontrivial normed ring, the series `∑ Xⁿ` is not restricted at the radius `1`: all its
weighted coefficient norms there equal `‖1‖ ≠ 0`. -/
theorem not_isRestricted_mk_one [Nontrivial R] :
    ¬(PowerSeries.mk 1 : PowerSeries R).IsRestricted 1 := by
  intro hf
  have h := (PowerSeries.isRestricted_iff' _ _).mp hf
  simp only [PowerSeries.coeff_mk, Pi.one_apply, one_pow, mul_one] at h
  exact norm_ne_zero_iff.mpr one_ne_zero (tendsto_nhds_unique tendsto_const_nhds h)

/-- A series restricted at `c` has weighted coefficient norms at `|c|` bounded by some `A ≥ 0`. -/
theorem _root_.PowerSeries.IsRestricted.exists_nonneg_norm_coeff_mul_pow_le
    (hf : f.IsRestricted c) :
    ∃ A, 0 ≤ A ∧ ∀ n, ‖f.coeff n‖ * |c| ^ n ≤ A := by
  rw [← PowerSeries.isRestricted_abs_iff, PowerSeries.isRestricted_iff'] at hf
  obtain ⟨A, hA⟩ := hf.bddAbove_range
  exact ⟨A, (by positivity : 0 ≤ ‖f.coeff 0‖ * |c| ^ 0).trans (hA ⟨0, rfl⟩), fun n ↦ hA ⟨n, rfl⟩⟩

section Algebra

variable {R : Type*} [NormedRing R] [IsUltrametricDist R] {c : ℝ}

/-- An algebra structure on the coefficients induces one on restricted power series through
constant series. Scalars act as on the ambient formal series, and the coefficient ring need not
be commutative. -/
noncomputable instance instAlgebraIsRestrictedSubring {S : Type*} [CommSemiring S] [Algebra S R] :
    Algebra S (PowerSeries.IsRestricted.subring (R := R) c) where
  smul s f := ⟨s • (f : PowerSeries R), by
    rw [Algebra.smul_def, PowerSeries.algebraMap_apply]
    exact (PowerSeries.isRestricted_C c (algebraMap S R s)).mul f.2⟩
  algebraMap := (algebraMap S (PowerSeries R)).codRestrict _ fun s ↦ by
    rw [PowerSeries.algebraMap_apply]
    exact PowerSeries.isRestricted_C c _
  commutes' s f := Subtype.ext <| by
    simpa only [Subring.coe_mul, RingHom.codRestrict_apply] using
      Algebra.commutes s (f : PowerSeries R)
  smul_def' s f := Subtype.ext <| by
    rw [Subring.coe_mul, RingHom.codRestrict_apply]
    convert Algebra.smul_def s (f : PowerSeries R) using 1

/-- A scalar maps to the constant restricted series of its image in the coefficient ring. -/
@[simp]
theorem coe_algebraMap_isRestrictedSubring {S : Type*} [CommSemiring S] [Algebra S R] (s : S) :
    (algebraMap S (PowerSeries.IsRestricted.subring (R := R) c) s : PowerSeries R) =
      PowerSeries.C (algebraMap S R s) := by
  calc
    _ = algebraMap S (PowerSeries R) s := (rfl)
    _ = _ := PowerSeries.algebraMap_apply

/-- Scalars act on restricted series as on their underlying formal power series. -/
@[simp]
theorem coe_smul_isRestrictedSubring {S : Type*} [CommSemiring S] [Algebra S R] (s : S)
    (f : PowerSeries.IsRestricted.subring (R := R) c) :
    ((s • f : PowerSeries.IsRestricted.subring (R := R) c) : PowerSeries R) =
      s • (f : PowerSeries R) := (rfl)

/-- Scalar towers on the coefficients induce scalar towers on restricted power series. -/
instance {S T : Type*} [CommSemiring S] [CommSemiring T] [Algebra S R] [Algebra T R]
    [SMul S T] [IsScalarTower S T R] :
    IsScalarTower S T (PowerSeries.IsRestricted.subring (R := R) c) where
  smul_assoc s t f := Subtype.ext <| by
    simp only [coe_smul_isRestrictedSubring]
    exact smul_assoc s t (f : PowerSeries R)

end Algebra

section CommAlgebra

variable {R : Type*} [NormedCommRing R] [IsUltrametricDist R] {c : ℝ}

/-- The inclusion of polynomials into the algebra of restricted power series. -/
noncomputable def polynomialToRestricted (c : ℝ) :
    Polynomial R →ₐ[R] PowerSeries.IsRestricted.subring (R := R) c where
  __ := Polynomial.coeToPowerSeries.ringHom.codRestrict _ isRestricted_polynomial
  commutes' a := Subtype.ext (Polynomial.coe_C a)

/-- The polynomial inclusion has the usual underlying power series. -/
@[simp]
theorem coe_polynomialToRestricted (p : Polynomial R) :
    (polynomialToRestricted c p : PowerSeries R) = p := (rfl)

/-- The inclusion of polynomials into restricted power series is injective at every radius. -/
theorem polynomialToRestricted_injective (c : ℝ) :
    Function.Injective (polynomialToRestricted (R := R) c) := by
  intro p q h
  apply Polynomial.coe_injective R
  simpa only [coe_polynomialToRestricted] using
    congrArg (fun f : PowerSeries.IsRestricted.subring (R := R) c ↦ (f : PowerSeries R)) h

/-- A restricted series whose coefficients vanish from degree `s` onward is the polynomial
inclusion of its `s`-truncation. -/
theorem polynomialToRestricted_trunc_eq_of_coeff_eq_zero {s : ℕ}
    (r : PowerSeries.IsRestricted.subring (R := R) c)
    (hr : ∀ n, s ≤ n → (r : PowerSeries R).coeff n = 0) :
    polynomialToRestricted c (PowerSeries.trunc s (r : PowerSeries R)) = r := by
  apply Subtype.ext
  ext n
  simp only [coe_polynomialToRestricted, Polynomial.coeff_coe, PowerSeries.coeff_trunc]
  split_ifs with hn
  · rfl
  · exact (hr n (by omega)).symm

/-- Move an invertible leading coefficient from a polynomial to its restricted-unit factor. -/
theorem exists_isUnit_isMonicOfDegree_mul_eq_of_isUnit_leadingCoeff
    {d : ℕ} {f : PowerSeries R} {P : Polynomial R}
    {U : PowerSeries.IsRestricted.subring (R := R) c} (ha : IsUnit P.leadingCoeff)
    (hd : P.natDegree = d) (hU : IsUnit U)
    (hf : f = (P : PowerSeries R) * (U : PowerSeries R)) :
    ∃ e : PowerSeries.IsRestricted.subring (R := R) c, IsUnit e ∧
      (ha.unit⁻¹ • P).IsMonicOfDegree d ∧
      (e : PowerSeries R) = P.leadingCoeff • (U : PowerSeries R) ∧
      (e : PowerSeries R) * ((ha.unit⁻¹ • P : Polynomial R) : PowerSeries R) = f := by
  set u := ha.unit
  have hu : (u : R) = P.leadingCoeff := ha.unit_spec
  refine ⟨algebraMap R _ u * U, (u.isUnit.map (algebraMap R _)).mul hU,
    ⟨by rw [Polynomial.natDegree_smul_of_smul_regular P (IsSMulRegular.all _), hd],
      Polynomial.monic_of_isUnit_leadingCoeff_inv_smul ha⟩, ?_, ?_⟩
  · rw [Subring.coe_mul, coe_algebraMap_isRestrictedSubring, Algebra.algebraMap_self_apply,
      hu, PowerSeries.smul_eq_C_mul]
  · rw [Subring.coe_mul, coe_algebraMap_isRestrictedSubring, Algebra.algebraMap_self_apply,
      ← PowerSeries.smul_eq_C_mul, Units.smul_def, Polynomial.coe_smul,
      smul_mul_smul_comm, u.mul_inv, one_smul, mul_comm]
    exact hf.symm

end CommAlgebra

end TauCeti.PowerSeries

namespace PowerSeries

open Filter
open scoped Topology

variable {R : Type*} [NormedRing R] {c c' : ℝ} {f g : PowerSeries R}

/-- The weighted coefficient norms of a restricted series are summable at every strictly
smaller radius. No completeness or ultrametric hypothesis is needed. -/
theorem IsRestricted.summable_norm_coeff_mul_pow (hf : f.IsRestricted c') {t : ℝ}
    (ht : |t| < |c'|) : Summable fun n ↦ ‖coeff n f‖ * t ^ n := by
  have hs : 0 < |c'| := (abs_nonneg t).trans_lt ht
  obtain ⟨B, _, hB⟩ := hf.exists_nonneg_norm_coeff_mul_pow_le
  have hq : |t| / |c'| < 1 := (div_lt_one hs).mpr ht
  refine Summable.of_norm_bounded
    ((summable_geometric_of_lt_one (by positivity) hq).mul_left B) fun n ↦ ?_
  calc ‖‖coeff n f‖ * t ^ n‖ = ‖coeff n f‖ * |c'| ^ n * (|t| / |c'|) ^ n := by
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (norm_nonneg _), abs_pow, div_pow]
        field_simp
    _ ≤ B * (|t| / |c'|) ^ n :=
      mul_le_mul_of_nonneg_right (hB n) (by positivity)

/-- **Products of restricted series at a smaller radius.** Over any normed ring, if `f` and `g`
are restricted at the radius `c'`, then `f * g` is restricted at every radius `c` with
`|c| < |c'|`: the weighted coefficient norms of `f * g` at `c'` grow at most linearly, and the
geometric factor `(|c| / |c'|)ⁿ` absorbs this growth. Over an ultrametric ring no radius is lost
(`MvPowerSeries.IsRestricted.mul`). -/
theorem IsRestricted.mul_of_abs_lt (hf : f.IsRestricted c') (hg : g.IsRestricted c')
    (h : |c| < |c'|) : (f * g).IsRestricted c := by
  obtain ⟨A, hA0, hA⟩ := hf.exists_nonneg_norm_coeff_mul_pow_le
  obtain ⟨B, hB0, hB⟩ := hg.exists_nonneg_norm_coeff_mul_pow_le
  have hq : 0 < |c'| := (abs_nonneg c).trans_lt h
  set ρ := |c| / |c'|
  have hupper : Tendsto (fun n : ℕ ↦ (n + 1 : ℝ) * ρ ^ n * (A * B)) atTop (𝓝 0) := by
    simpa using (TauCeti.tendsto_add_pow_mul_pow_of_lt_one 1 (by positivity)
      ((div_lt_one hq).mpr h)).mul_const (A * B)
  rw [← isRestricted_abs_iff, isRestricted_iff']
  refine squeeze_zero (fun n ↦ by positivity) (fun n ↦ ?_) hupper
  rw [coeff_mul]
  calc
    ‖∑ p ∈ Finset.antidiagonal n, coeff p.1 f * coeff p.2 g‖ * |c| ^ n
        ≤ (∑ p ∈ Finset.antidiagonal n, ‖coeff p.1 f * coeff p.2 g‖) * |c| ^ n :=
      mul_le_mul_of_nonneg_right (norm_sum_le _ _) (by positivity)
    _ = ∑ p ∈ Finset.antidiagonal n, ‖coeff p.1 f * coeff p.2 g‖ * |c| ^ n := by
      rw [Finset.sum_mul]
    _ ≤ ∑ _p ∈ Finset.antidiagonal n, A * B * ρ ^ n := by
      refine Finset.sum_le_sum fun p hp ↦ ?_
      have hp' := Finset.mem_antidiagonal.mp hp
      calc
        ‖coeff p.1 f * coeff p.2 g‖ * |c| ^ n
            ≤ (‖coeff p.1 f‖ * ‖coeff p.2 g‖) * |c| ^ n := by gcongr; exact norm_mul_le _ _
        _ = (‖coeff p.1 f‖ * |c| ^ p.1) * (‖coeff p.2 g‖ * |c| ^ p.2) := by
          rw [← hp', pow_add]
          ring
        _ ≤ (A * ρ ^ p.1) * (B * ρ ^ p.2) :=
          mul_le_mul (TauCeti.mul_abs_pow_le_of_forall_mul_pow_le hq hA p.1)
            (TauCeti.mul_abs_pow_le_of_forall_mul_pow_le hq hB p.2)
            (by positivity) (by positivity)
        _ = A * B * ρ ^ n := by rw [← hp', pow_add]; ring
    _ = (n + 1 : ℝ) * ρ ^ n * (A * B) := by
      rw [Finset.sum_const, Finset.Nat.card_antidiagonal]
      ring

/-- In a factorisation `f = u * (X ^ a * ∏ᶠ m, g m)` on a closed disc of radius `r`, where `u` is a
restricted unit and every factor `g m` has constant coefficient `1`, the exponent `a` is the order
of vanishing `f.order` at zero. -/
theorem order_eq_of_isUnit_X_pow_mul_finprod_eq {R ι : Type*} [NormedCommRing R]
    [IsUltrametricDist R] [Nontrivial R] {f : PowerSeries R} {r : ℝ}
    {u : IsRestricted.subring (R := R) r} (hu : IsUnit u) {a : ℕ} {g : ι → Polynomial R}
    (hc0 : ∀ m, (g m).coeff 0 = 1)
    (hmul : (u : PowerSeries R) * (((Polynomial.X ^ a * ∏ᶠ m, g m : Polynomial R) :
      PowerSeries R)) = f) :
    f.order = a := by
  set Q : PowerSeries R := ((∏ᶠ m, g m : Polynomial R) : PowerSeries R)
  have hmul' : (X : PowerSeries R) ^ a * ((u : PowerSeries R) * Q) = f := by
    rw [← hmul, Polynomial.coe_mul, Polynomial.coe_pow, Polynomial.coe_X]
    ring
  have hQ0 : constantCoeff Q = 1 := by
    by_cases hfin : (Function.mulSupport g).Finite
    · rw [Polynomial.constantCoeff_coe, ← Polynomial.constantCoeff_apply,
        map_finprod Polynomial.constantCoeff hfin,
        finprod_eq_one_of_forall_eq_one fun m => by simpa using hc0 m]
    · simp [Q, finprod_of_infinite_mulSupport hfin]
  have hfa : f.coeff a ≠ 0 := by
    have ha : ((X : PowerSeries R) ^ a * ((u : PowerSeries R) * Q)).coeff (0 + a) = f.coeff a := by
      rw [zero_add, hmul']
    rw [← ha, coeff_X_pow_mul, coeff_zero_eq_constantCoeff_apply, map_mul, hQ0, mul_one]
    exact ((hu.map (IsRestricted.subring r).subtype).map constantCoeff).ne_zero
  refine le_antisymm (f.order_le a hfa) ?_
  calc (a : ℕ∞) = ((X : PowerSeries R) ^ a).order := (order_X_pow a).symm
    _ ≤ ((X : PowerSeries R) ^ a).order + ((u : PowerSeries R) * Q).order := self_le_add_right _ _
    _ ≤ f.order := hmul' ▸ le_order_mul _ _

end PowerSeries
