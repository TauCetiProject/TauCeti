/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.PowerSeries.EvalAt
public import TauCeti.RingTheory.PowerSeries.GaussNorm.Radius
public import TauCeti.RingTheory.PowerSeries.Weierstrass.Quotient
import Mathlib.Analysis.Normed.Algebra.Ultra

/-!
# Normalised Weierstrass preparation on a closed disc

Let `K` be a complete nonarchimedean field and `f` a power series over `K` with `f(0) = 1`,
restricted at a radius `r > 0`, and distinguished of degree `d` there: `d` is the last index at
which the weighted coefficient norm `‖aₙ‖ rⁿ` attains the Gauss norm `‖f‖_r`. Weierstrass
preparation writes `f = e * ω` with `ω` monic of degree `d` and `e` a unit of the ring of series
restricted at `r`. Since `f(0) = 1`, the constant coefficient of `ω` is nonzero, and rescaling
both factors gives the *normalised disc preparation*

```text
f = P * U,    P(0) = U(0) = 1,    deg P = d,    U restricted at r,    ‖U - 1‖_r < 1.
```

The zeros of `f` in the closed disc of radius `r`, in any complete normed field extension of
`K`, are the roots of `P` there, and `f` and `P` have the same order of vanishing at `0`.

For a restricted series `U` with `U(0) = 1`, the bound `‖U - 1‖_r < 1` says exactly that `U` is
distinguished of degree `0` at `r` (`TauCeti.PowerSeries.gaussNorm_sub_one_lt_one_iff`), that is,
over a complete field, that `U` is a unit of the ring of series restricted at `r`
(`TauCeti.PowerSeries.isUnit_iff_gaussNorm_sub_one_lt_one`). Then `‖U‖_r = 1`,
so `‖f‖_r = ‖P‖_r`, and since the Gauss norm is multiplicative, `f - P = P * (U - 1)` is strictly
smaller than `f`.

If `r ≤ s` and `f = Q * V` is the normalised preparation at `s`, then `V` is also a unit at `r`,
so `Q` is `P` times a unit of the ring of series restricted at `r`. Since division of polynomials
by `P` agrees with Weierstrass division at `r`, it follows that `P` divides `Q` as a polynomial.
Taking `r = s` gives uniqueness of the normalised preparation.

## Main definitions

* `TauCeti.PowerSeries.IsDiscPreparation`: `f = P * U` is the normalised preparation of `f` on
  the closed disc of radius `r`, in the distinguished degree `d` of `f`.

## Main results

* `TauCeti.PowerSeries.IsDistinguished.exists_isDiscPreparation` and
  `TauCeti.PowerSeries.IsDistinguished.existsUnique_isDiscPreparation`: existence and uniqueness of
  the normalised disc preparation.
* `TauCeti.PowerSeries.exists_isDiscPreparation_iff`: a series has a normalised disc preparation
  at `r` in degree `d` exactly when it is restricted and distinguished of degree `d` at `r` and has
  constant coefficient `1`.
* `TauCeti.PowerSeries.IsDiscPreparation.dvd_of_le`: the polynomial factor at a radius `r` divides
  the polynomial factor at every radius `s ≥ r`.
* `TauCeti.PowerSeries.IsDiscPreparation.gaussNorm_sub_lt`: `‖f - P‖_r < ‖f‖_r`.
* `TauCeti.PowerSeries.IsDiscPreparation.gaussNorm_sub_one_le_div` and
  `TauCeti.PowerSeries.IsDiscPreparation.gaussNorm_sub_le_mul_div`: on a smaller positive
  disc, `‖U - 1‖_s ≤ s / r` and `‖f - P‖_s ≤ ‖f‖_s * (s / r)`.
* `TauCeti.PowerSeries.tendsto_gaussNorm_sub_of_isDiscPreparation`: disc polynomials at
  radii tending to infinity converge to the series in each fixed positive-radius Gauss norm.
* `TauCeti.PowerSeries.IsDiscPreparation.order_eq` and
  `TauCeti.PowerSeries.IsDiscPreparation.evalAt_eq_zero_iff`: `f` and `P` have the same order of
  vanishing at `0` and the same zeros in the closed disc of radius `r`, in every complete normed
  field extension.

## References

* Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*, §5.2.2, Theorem 1, for Weierstrass
  preparation.
* M. Lazard, *Les zéros d'une fonction analytique d'une variable sur un corps valué complet*,
  Publications Mathématiques de l'IHÉS 14 (1962), §§3–4, for the polynomials attached to closed
  discs, their divisibility as the radius grows, and their approximation estimates.
-/

public section

open Filter
open scoped Topology

namespace TauCeti.PowerSeries

open _root_.PowerSeries

variable {K : Type*} [NormedField K] [IsUltrametricDist K] {r s : ℝ} {d e : ℕ}
  {f : PowerSeries K} {P Q : Polynomial K} {U V : PowerSeries K}

/-! ### The normalised disc preparation -/

variable (r d f P U) in
/-- `f = P * U` is the **normalised preparation** of `f` on the closed disc of radius `r`: `f` is
distinguished of degree `d` at `r`, `P` is a polynomial of degree `d` with constant coefficient `1`,
and `U` is a series restricted at `r` with constant coefficient `1` and `‖U - 1‖_r < 1`.

Over a complete nonarchimedean field, a series with constant coefficient `1` which is restricted at
`r > 0` has exactly one such factorization in its distinguished degree
(`TauCeti.PowerSeries.IsDistinguished.existsUnique_isDiscPreparation`). The polynomial `P` carries
the zeros of `f` in the closed disc of radius `r`
(`TauCeti.PowerSeries.IsDiscPreparation.evalAt_eq_zero_iff`). -/
structure IsDiscPreparation : Prop where
  /-- The series `f` is distinguished of degree `d` at `r`. -/
  isDistinguished : IsDistinguished r d f
  /-- The polynomial factor has degree `d`. -/
  natDegree_eq : P.natDegree = d
  /-- The polynomial factor has constant coefficient `1`. -/
  coeff_zero_eq_one : P.coeff 0 = 1
  /-- The series factor is restricted at `r`. -/
  isRestricted : U.IsRestricted r
  /-- The series factor has constant coefficient `1`. -/
  constantCoeff_eq_one : constantCoeff U = 1
  /-- The series factor is close to `1` at `r`. -/
  gaussNorm_sub_one_lt : (U - 1).gaussNorm norm r < 1
  /-- `f` is the product of the two factors. -/
  eq_mul : f = P * U

namespace IsDiscPreparation

omit [IsUltrametricDist K] in
/-- The polynomial factor of a normalised disc preparation is nonzero. -/
theorem ne_zero (h : IsDiscPreparation r d f P U) : P ≠ 0 := by
  rintro rfl
  simpa using h.coeff_zero_eq_one

/-- The series factor of a normalised disc preparation has Gauss norm `1`. -/
theorem gaussNorm_eq_one (h : IsDiscPreparation r d f P U) : U.gaussNorm norm r = 1 :=
  gaussNorm_eq_one_of_gaussNorm_sub_one_lt h.isRestricted h.gaussNorm_sub_one_lt

/-- The series factor of a normalised disc preparation is distinguished of degree `0`. -/
theorem isDistinguished_zero (h : IsDiscPreparation r d f P U) (hr : 0 < r) :
    IsDistinguished r 0 U :=
  (gaussNorm_sub_one_lt_one_iff hr h.isRestricted h.constantCoeff_eq_one).mp h.gaussNorm_sub_one_lt

/-- The series factor of a normalised disc preparation is a unit of the ring of series restricted
at `r`. -/
theorem isUnit [CompleteSpace K] (h : IsDiscPreparation r d f P U) (hr : 0 < r) :
    IsUnit (⟨U, h.isRestricted⟩ : PowerSeries.IsRestricted.subring (R := K) r) :=
  (isUnit_iff_gaussNorm_sub_one_lt_one hr _ h.constantCoeff_eq_one).mpr h.gaussNorm_sub_one_lt

/-- The polynomial factor is distinguished of degree `d` at `r`, like `f`. -/
theorem isDistinguished_coe (h : IsDiscPreparation r d f P U) (hr : 0 < r) :
    IsDistinguished r d (P : PowerSeries K) := by
  obtain ⟨k, hk⟩ := exists_isDistinguished hr (isRestricted_polynomial (c := r) P)
    (by exact_mod_cast h.ne_zero)
  have hPU := hk.mul (h.isDistinguished_zero hr) hr (norm_mul _ _)
  rw [add_zero, ← h.eq_mul] at hPU
  rwa [hPU.unique h.isDistinguished] at hk

/-- **The Gauss norm of the disc polynomial.** The series `f` and the polynomial factor of its
normalised disc preparation have the same Gauss norm at `r`. -/
theorem gaussNorm_coe (h : IsDiscPreparation r d f P U) (hr : 0 < r) :
    (P : PowerSeries K).gaussNorm norm r = f.gaussNorm norm r := by
  rw [h.eq_mul, gaussNorm_mul_of_isRestricted hr (isRestricted_polynomial P) h.isRestricted,
    h.gaussNorm_eq_one, mul_one]

/-- **The disc polynomial approximates `f`.** The polynomial factor `P` of the normalised disc
preparation of `f` at `r` satisfies `‖f - P‖_r < ‖f‖_r`. -/
theorem gaussNorm_sub_lt (h : IsDiscPreparation r d f P U) (hr : 0 < r) :
    (f - P).gaussNorm norm r < f.gaussNorm norm r := by
  have hfP : f - P = (P : PowerSeries K) * (U - 1) := by
    rw [h.eq_mul, mul_sub, mul_one]
  have hP : 0 < (P : PowerSeries K).gaussNorm norm r :=
    gaussNorm_pos hr (hasGaussNorm_of_isRestricted (isRestricted_polynomial P))
      (by exact_mod_cast h.ne_zero)
  rw [hfP, gaussNorm_mul_of_isRestricted hr (isRestricted_polynomial P)
    (h.isRestricted.sub (PowerSeries.isRestricted_one r)), ← h.gaussNorm_coe hr]
  exact mul_lt_of_lt_one_right hP h.gaussNorm_sub_one_lt

omit [IsUltrametricDist K] in
/-- The normalised cofactor is uniformly close to one on a smaller disc, with
an explicit bound depending only on the ratio of radii. -/
theorem gaussNorm_sub_one_le_div (h : IsDiscPreparation r d f P U)
    (hr : 0 < r) (hs : 0 ≤ s) (hsr : s ≤ r) :
    (U - 1).gaussNorm norm s ≤ s / r := by
  have hbound := PowerSeries.gaussNorm_sub_one_le_mul_div (f := U) hr hs hsr
    (hasGaussNorm_of_isRestricted (h.isRestricted.sub (isRestricted_one r)))
    h.constantCoeff_eq_one
  exact hbound.trans (mul_le_of_le_one_left (by positivity) h.gaussNorm_sub_one_lt.le)

/-- The disc polynomial has the same Gauss norm as the series on every positive
smaller disc, not only on the preparation disc. -/
theorem gaussNorm_coe_of_le (h : IsDiscPreparation r d f P U)
    (hs : 0 < s) (hsr : s ≤ r) :
    (P : PowerSeries K).gaussNorm norm s = f.gaussNorm norm s := by
  have hUs := isRestricted_of_abs_le h.isRestricted (abs_le_abs_of_nonneg hs.le hsr)
  have hclose : (U - 1).gaussNorm norm s < 1 :=
    (gaussNorm_le_gaussNorm_of_le norm_nonneg hs.le hsr
      (hasGaussNorm_of_isRestricted (h.isRestricted.sub (isRestricted_one r)))).trans_lt
        h.gaussNorm_sub_one_lt
  rw [h.eq_mul, gaussNorm_mul_of_isRestricted hs (isRestricted_polynomial P) hUs,
    gaussNorm_eq_one_of_gaussNorm_sub_one_lt hUs hclose, mul_one]

/-- The normalised disc polynomial approximates the series on every smaller
positive disc, with error at most `‖f‖_s * (s / r)`. -/
theorem gaussNorm_sub_le_mul_div (h : IsDiscPreparation r d f P U)
    (hs : 0 < s) (hsr : s ≤ r) :
    (f - P).gaussNorm norm s ≤ f.gaussNorm norm s * (s / r) := by
  have hUs := isRestricted_of_abs_le h.isRestricted (abs_le_abs_of_nonneg hs.le hsr)
  have heq : f - P = (P : PowerSeries K) * (U - 1) := by
    rw [h.eq_mul, mul_sub, mul_one]
  rw [heq, gaussNorm_mul_of_isRestricted hs (isRestricted_polynomial P)
    (hUs.sub (isRestricted_one s)), h.gaussNorm_coe_of_le hs hsr]
  exact mul_le_mul_of_nonneg_left (h.gaussNorm_sub_one_le_div (hs.trans_le hsr) hs.le hsr)
    (PowerSeries.gaussNorm_nonneg _ _ _ norm_nonneg)

omit [IsUltrametricDist K] in
/-- **The order of vanishing at `0`.** The series `f` and the polynomial factor of its normalised
disc preparation have the same order of vanishing at `0`. -/
theorem order_eq (h : IsDiscPreparation r d f P U) : f.order = (P : PowerSeries K).order := by
  have hU : U.order = 0 := by
    by_contra hne
    simpa [h.constantCoeff_eq_one] using order_ne_zero_iff_constCoeff_eq_zero.mp hne
  rw [h.eq_mul, order_mul, hU, add_zero]

/-- **The zeros in the closed disc.** In a complete normed field extension `L` of a
nonarchimedean field `K`, a point `x` with `‖x‖ ≤ r` is a zero of `f` exactly when it is a root of
the polynomial factor of the normalised disc preparation of `f` at `r`. -/
theorem evalAt_eq_zero_iff {L : Type*} [NormedField L] [NormedAlgebra K L]
    [CompleteSpace L] (h : IsDiscPreparation r d f P U) {x : L} (hx : ‖x‖ ≤ r) :
    f.evalAt x = 0 ↔ Polynomial.aeval x P = 0 := by
  have : IsUltrametricDist L := .of_normedAlgebra K
  have hU1 := h.isRestricted.sub (PowerSeries.isRestricted_one r)
  -- `U(x) = (U - 1)(x) + 1` with `‖(U - 1)(x)‖ ≤ ‖U - 1‖_r < 1`, so `U(x) ≠ 0`.
  have hu : U.evalAt x ≠ 0 := by
    intro hx0
    have hlt := (_root_.PowerSeries.norm_evalAt_le_gaussNorm
      (hasGaussNorm_of_isRestricted hU1) hx).trans_lt h.gaussNorm_sub_one_lt
    rw [← sub_add_cancel U 1, _root_.PowerSeries.IsRestricted.evalAt_add hU1
      (PowerSeries.isRestricted_one r) hx, _root_.PowerSeries.evalAt_one,
      add_eq_zero_iff_eq_neg] at hx0
    simp [hx0] at hlt
  rw [h.eq_mul, _root_.PowerSeries.IsRestricted.evalAt_mul (isRestricted_polynomial P)
    h.isRestricted hx, _root_.PowerSeries.evalAt_coe, mul_eq_zero, or_iff_left hu]

/-- **Nested disc polynomials.** If `f = P * U` and `f = Q * V` are the normalised disc
preparations of `f` at radii `0 < r ≤ s`, then `P` divides `Q`. -/
theorem dvd_of_le [CompleteSpace K] (h : IsDiscPreparation r d f P U)
    (h' : IsDiscPreparation s e f Q V) (hr : 0 < r) (hrs : r ≤ s) : P ∣ Q := by
  have hrs' : |r| ≤ |s| := by rwa [abs_of_pos hr, abs_of_pos (hr.trans_le hrs)]
  -- `V` is close to `1` at `r` as well, so it is a unit at `r`.
  have hVr : V.IsRestricted r := isRestricted_of_abs_le h'.isRestricted hrs'
  have hVs : (V - 1).HasGaussNorm norm s :=
    hasGaussNorm_of_isRestricted (h'.isRestricted.sub (PowerSeries.isRestricted_one s))
  have hVr1 : (V - 1).gaussNorm norm r < 1 :=
    (gaussNorm_le_gaussNorm_of_le (fun _ ↦ norm_nonneg _) hr.le hrs hVs).trans_lt
      h'.gaussNorm_sub_one_lt
  obtain ⟨W, hW⟩ := ((isUnit_iff_gaussNorm_sub_one_lt_one hr ⟨V, hVr⟩
    h'.constantCoeff_eq_one).mpr hVr1).exists_right_inv
  have hVW : V * (W : PowerSeries K) = 1 := congrArg Subtype.val hW
  -- Normalise `P` to the monic polynomial `ω = a⁻¹ • P`, distinguished of degree `d` at `r`.
  set a := P.leadingCoeff with ha_def
  have ha : a ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr h.ne_zero
  set ω : Polynomial K := Polynomial.C a⁻¹ * P with hω_def
  have hω : ω.IsMonicOfDegree d :=
    ⟨by rw [hω_def, Polynomial.natDegree_C_mul (inv_ne_zero ha), h.natDegree_eq],
      Polynomial.monic_C_mul_of_mul_leadingCoeff_eq_one (inv_mul_cancel₀ ha)⟩
  have hPω : (P : PowerSeries K) = C a * ω := by
    rw [hω_def, Polynomial.coe_mul, Polynomial.coe_C, ← mul_assoc, ← map_mul,
      mul_inv_cancel₀ ha, map_one, one_mul]
  have hωd : IsDistinguished r d (ω : PowerSeries K) := by
    have hd := h.isDistinguished_coe hr
    rw [hPω] at hd
    exact hd.of_isUnit_mul hr ((isUnit_iff_ne_zero.mpr ha).map
      (algebraMap K (PowerSeries.IsRestricted.subring (R := K) r)))
  -- At `r`, `Q = f * W = ω * (a • U * W)`, so `ω` divides `Q` among restricted series.
  have hdvd : polynomialToRestricted r ω ∣ polynomialToRestricted r Q := by
    refine ⟨algebraMap K _ a * ⟨U, h.isRestricted⟩ * W, Subtype.ext ?_⟩
    have hQ : (Q : PowerSeries K) = f * W := by
      rw [h'.eq_mul, mul_assoc, hVW, mul_one]
    simp only [coe_polynomialToRestricted, Subring.coe_mul, coe_algebraMap_isRestrictedSubring,
      Algebra.algebraMap_self_apply]
    rw [hQ, h.eq_mul, hPω]
    ring
  exact (dvd_mul_left P _).trans ((hωd.polynomialToRestricted_dvd_iff hr hω Q).mp hdvd)

/-- **Uniqueness of the normalised disc preparation.** Over a complete nonarchimedean field, a
series has at most one normalised preparation on the closed disc of a positive radius `r`. -/
theorem unique [CompleteSpace K] (h : IsDiscPreparation r d f P U)
    (h' : IsDiscPreparation r e f Q V) (hr : 0 < r) : P = Q ∧ U = V := by
  -- `P` and `Q` divide each other, and a unit polynomial with constant coefficient `1` is `1`.
  obtain ⟨u, hu⟩ := h.dvd_of_le h' hr le_rfl
  obtain ⟨u', hu'⟩ := h'.dvd_of_le h hr le_rfl
  have huu : u * u' = 1 :=
    (mul_left_cancel₀ h.ne_zero (by rw [mul_one, ← mul_assoc, ← hu, ← hu'])).symm
  obtain ⟨c, -, rfl⟩ := Polynomial.isUnit_iff.mp (IsUnit.of_mul_eq_one _ huu)
  have hc : c = 1 := by
    simpa [h.coeff_zero_eq_one, h'.coeff_zero_eq_one, eq_comm] using
      congrArg (AddMonoidAlgebra.coeff · 0) hu
  have hPQ : P = Q := by rw [hu, hc, Polynomial.C_1, mul_one]
  refine ⟨hPQ, mul_left_cancel₀ (by exact_mod_cast h.ne_zero : (P : PowerSeries K) ≠ 0) ?_⟩
  rw [← h.eq_mul, hPQ, ← h'.eq_mul]

end IsDiscPreparation

/-- **Normalised preparation on a closed disc.** Over a complete nonarchimedean field, a series
`f` with `f(0) = 1`, restricted and distinguished of degree `d` at a radius `r > 0`, is `P * U`
with `P` a polynomial of degree `d`, `U` restricted at `r`, `P(0) = U(0) = 1` and
`‖U - 1‖_r < 1`. -/
theorem IsDistinguished.exists_isDiscPreparation [CompleteSpace K] (hf : IsDistinguished r d f)
    (hr : 0 < r) (hfr : f.IsRestricted r) (hf0 : constantCoeff f = 1) :
    ∃ (P : Polynomial K) (U : PowerSeries K), IsDiscPreparation r d f P U := by
  obtain ⟨e, ω, he, hω, heω⟩ :=
    hf.exists_isUnit_isMonicOfDegree_mul_eq (isUnit_iff_ne_zero.mpr hf.coeff_ne_zero) hr hfr
  -- `f(0) = e(0) * ω(0) = 1`, so `b = ω(0)` is nonzero. Put `P = b⁻¹ • ω` and `U = b • e`.
  set b := ω.coeff 0 with hb_def
  have h0 : b * constantCoeff (e : PowerSeries K) = 1 := by
    rw [← hf0, ← heω, map_mul, Polynomial.constantCoeff_coe, mul_comm]
  have hb : b ≠ 0 := left_ne_zero_of_mul_eq_one h0
  set U' : PowerSeries.IsRestricted.subring (R := K) r := algebraMap K _ b * e with hU'_def
  have hU' : (U' : PowerSeries K) = C b * e := by
    rw [hU'_def, Subring.coe_mul, coe_algebraMap_isRestrictedSubring, Algebra.algebraMap_self_apply]
  have hU0 : constantCoeff (U' : PowerSeries K) = 1 := by
    rw [hU', map_mul, constantCoeff_C, h0]
  have hb1 : C b⁻¹ * C b = (1 : PowerSeries K) := by
    rw [← map_mul, inv_mul_cancel₀ hb, map_one]
  refine ⟨Polynomial.C b⁻¹ * ω, U',
    { isDistinguished := hf
      natDegree_eq := by rw [Polynomial.natDegree_C_mul (inv_ne_zero hb), hω.natDegree_eq]
      coeff_zero_eq_one := by rw [Polynomial.coeff_C_mul, inv_mul_cancel₀ hb]
      isRestricted := U'.2
      constantCoeff_eq_one := hU0
      gaussNorm_sub_one_lt := (isUnit_iff_gaussNorm_sub_one_lt_one hr U' hU0).mp
        (((isUnit_iff_ne_zero.mpr hb).map _).mul he)
      eq_mul := ?_ }⟩
  rw [hU', Polynomial.coe_mul, Polynomial.coe_C, ← heω]
  linear_combination (-((e : PowerSeries K) * ω)) * hb1

/-- **Normalised preparation on a closed disc**, in its unique-existence form: over a complete
nonarchimedean field, a series with constant coefficient `1`, restricted and distinguished of
degree `d` at a radius `r > 0`, has exactly one normalised preparation on the closed disc of
radius `r`. -/
theorem IsDistinguished.existsUnique_isDiscPreparation [CompleteSpace K]
    (hf : IsDistinguished r d f) (hr : 0 < r) (hfr : f.IsRestricted r)
    (hf0 : constantCoeff f = 1) :
    ∃! PU : Polynomial K × PowerSeries K, IsDiscPreparation r d f PU.1 PU.2 := by
  obtain ⟨P, U, h⟩ := hf.exists_isDiscPreparation hr hfr hf0
  refine ⟨(P, U), h, fun PU h' ↦ ?_⟩
  obtain ⟨h1, h2⟩ := h'.unique h hr
  exact Prod.ext h1 h2

/-- **Characterisation of the normalised disc preparation.** Over a complete nonarchimedean field
and at a radius `r > 0`, a series has a normalised preparation on the closed disc of radius `r` in
degree `d` exactly when it is restricted and distinguished of degree `d` at `r` and has constant
coefficient `1`. -/
theorem exists_isDiscPreparation_iff [CompleteSpace K] (hr : 0 < r) :
    (∃ (P : Polynomial K) (U : PowerSeries K), IsDiscPreparation r d f P U) ↔
      IsDistinguished r d f ∧ f.IsRestricted r ∧ constantCoeff f = 1 := by
  refine ⟨fun ⟨P, U, h⟩ ↦ ⟨h.isDistinguished, ?_, ?_⟩, fun ⟨hf, hfr, hf0⟩ ↦
    hf.exists_isDiscPreparation hr hfr hf0⟩
  · rw [h.eq_mul]
    exact (isRestricted_polynomial P).mul h.isRestricted
  · rw [h.eq_mul, map_mul, Polynomial.constantCoeff_coe, h.coeff_zero_eq_one,
      h.constantCoeff_eq_one, one_mul]

variable {ι : Type*} {l : Filter ι} {ρ : ι → ℝ} {D : ι → ℕ}
  {p : ι → Polynomial K} {u : ι → PowerSeries K}

omit [IsUltrametricDist K] in
/-- At radii tending to infinity, any family of normalised disc cofactors tends
to one in each fixed positive-radius Gauss norm. Only eventual preparation is needed. -/
theorem tendsto_gaussNorm_sub_one_of_isDiscPreparation
    (hρ : Tendsto ρ l atTop)
    (h : ∀ᶠ i in l, IsDiscPreparation (ρ i) (D i) f (p i) (u i)) (hs : 0 < s) :
    Tendsto (fun i ↦ (u i - 1).gaussNorm norm s) l (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall fun _ ↦
    PowerSeries.gaussNorm_nonneg _ _ _ norm_nonneg) ?_
    ((tendsto_const_nhds (x := s)).div_atTop hρ)
  filter_upwards [h, hρ.eventually_ge_atTop s] with i hi hsi
  exact hi.gaussNorm_sub_one_le_div (hs.trans_le hsi) hs.le hsi

/-- At radii tending to infinity, the normalised disc polynomials converge to
the series in every fixed positive-radius Gauss norm. -/
theorem tendsto_gaussNorm_sub_of_isDiscPreparation
    (hρ : Tendsto ρ l atTop)
    (h : ∀ᶠ i in l, IsDiscPreparation (ρ i) (D i) f (p i) (u i)) (hs : 0 < s) :
    Tendsto (fun i ↦ (f - p i).gaussNorm norm s) l (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall fun _ ↦
    PowerSeries.gaussNorm_nonneg _ _ _ norm_nonneg) ?_
    (by simpa using
      ((tendsto_const_nhds (x := s)).div_atTop hρ).const_mul (f.gaussNorm norm s))
  filter_upwards [h, hρ.eventually_ge_atTop s] with i hi hsi
  exact hi.gaussNorm_sub_le_mul_div hs hsi

end TauCeti.PowerSeries
