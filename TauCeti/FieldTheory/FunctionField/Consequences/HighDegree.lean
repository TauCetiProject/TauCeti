/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Differential.CanonicalDivisor

/-!
# Riemann--Roch in high degree

For a divisor `D` of a function field of genus `g`, the Riemann--Roch theorem simplifies to

`ℓ(D) = deg D + 1 - g`

as soon as `deg D > 2g - 2`.  Indeed, if `W` is a canonical divisor, then `W - D` has negative
degree, so its Riemann--Roch space vanishes.  This is Stichtenoth, *Algebraic Function Fields and
Codes*, 2nd ed., Theorem 1.5.17.

The genus-one specialization gives the section-dimension ladder `ℓ(nP) = n * deg P` at every
place `P` and every positive integer `n`; at a rational place it reads `ℓ(nP) = n`, the dimension
input for the construction of Weierstrass coordinates.

## Main results

* `TauCeti.Divisor.dim_eq_degree_add_one_sub_genus_of_two_mul_genus_sub_one_le_degree`: the
  high-degree form of Riemann--Roch.
* `TauCeti.Divisor.indexOfSpecialty_eq_zero_of_two_mul_genus_sub_one_le_degree`: divisors above
  the canonical degree are nonspecial.
* `TauCeti.Divisor.dim_eq_degree_of_genus_eq_one`: in genus one, every positive-degree divisor
  has dimension equal to its degree.
* `TauCeti.Divisor.dim_natCast_zsmul_ofPoint_of_genus_eq_one`: `ℓ(nP) = n * deg P` at a place of
  a genus-one function field, for `n >= 1`.
* `TauCeti.Divisor.dim_single_of_genus_eq_one`: `ℓ(nP) = n` at a rational place of a genus-one
  function field, for `n >= 1`.
* `Place.exists_poles_eq_natCast_zsmul_ofPoint_of_two_mul_genus_sub_one_le_sub_one_mul_degree`: a
  function with pole divisor exactly `nP` exists as soon as `2g - 1 <= (n - 1) * deg P`.
* `TauCeti.Place.exists_ord_eq_neg_and_forall_ne_ord_nonneg`: for every `n >= 2g`, a nonzero
  function has order `-n` at a prescribed place and is regular elsewhere.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Theorem 1.5.17.
-/

public section

namespace TauCeti

open AlgebraicGeometry

variable {k F : Type*} [Field k] [Field F] [Algebra k F]

namespace Divisor

/-- **Riemann--Roch in high degree** (Stichtenoth, Theorem 1.5.17): if
`deg D >= 2g - 1`, then

`ℓ(D) = deg D + 1 - g`.

The statement uses integers throughout, matching both divisor degree and the Riemann--Roch
identity and avoiding a truncated natural-number subtraction. -/
theorem dim_eq_degree_add_one_sub_genus_of_two_mul_genus_sub_one_le_degree
    (hF : IsFunctionField k F) (hex : IsIntegrallyClosedIn k F) {D : Divisor k F}
    (hD : 2 * (genus k F : ℤ) - 1 ≤ degree D) :
    (dim D : ℤ) = degree D + 1 - genus k F := by
  obtain ⟨W, hW⟩ := exists_isRiemannRochDivisor hF hex
  have hdegW : degree W = 2 * (genus k F : ℤ) - 2 := hW.degree_eq hF hex
  have hneg : degree (W - D) < 0 := by
    rw [degree_sub, hdegW]
    omega
  have hzero : dim (W - D) = 0 := dim_eq_zero_of_degree_neg hF hneg
  simpa [hzero] using Divisor.isRiemannRochDivisor_iff.mp hW D

/-- The weak-inequality spelling of nonspeciality in high degree:
`deg D >= 2g - 1` implies `i(D) = 0`. -/
theorem indexOfSpecialty_eq_zero_of_two_mul_genus_sub_one_le_degree
    (hF : IsFunctionField k F) (hex : IsIntegrallyClosedIn k F) {D : Divisor k F}
    (hD : 2 * (genus k F : ℤ) - 1 ≤ degree D) :
    indexOfSpecialty D = 0 := by
  rw [indexOfSpecialty_def,
    dim_eq_degree_add_one_sub_genus_of_two_mul_genus_sub_one_le_degree hF hex hD]
  omega

/-! ### Genus one -/

/-- On a genus-one function field, every divisor of positive degree has Riemann--Roch dimension
equal to its degree. -/
theorem dim_eq_degree_of_genus_eq_one (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) (hg : genus k F = 1) {D : Divisor k F}
    (hD : 0 < degree D) : (dim D : ℤ) = degree D := by
  have hhigh : 2 * (genus k F : ℤ) - 1 ≤ degree D := by
    rw [hg]
    norm_num
    exact hD
  have h :=
    dim_eq_degree_add_one_sub_genus_of_two_mul_genus_sub_one_le_degree hF hex hhigh
  rw [hg] at h
  omega

/-- On a genus-one function field, the Riemann--Roch space of `nP` has dimension `n * deg P` for
every place `P` and every positive natural number `n`.

This is the genus-one section-dimension ladder; at a rational place it reads `ℓ(nP) = n`, the
dimension input used to construct Weierstrass coordinates. -/
theorem dim_natCast_zsmul_ofPoint_of_genus_eq_one (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) (hg : genus k F = 1) {P : Place k F}
    {n : ℕ} (hn : 1 ≤ n) :
    dim ((n : ℤ) • WeilDivisor.ofPoint P) = n * P.degree := by
  have hdeg : degree ((n : ℤ) • WeilDivisor.ofPoint P : Divisor k F) = (n * P.degree : ℕ) := by
    rw [degree_zsmul, degree_ofPoint]
    push_cast
    ring
  have hdegpos : 0 < degree ((n : ℤ) • WeilDivisor.ofPoint P : Divisor k F) := by
    rw [hdeg]
    exact_mod_cast Nat.mul_pos hn (P.one_le_degree_of_isFunctionField hF)
  have hdim := dim_eq_degree_of_genus_eq_one hF hex hg hdegpos
  rw [hdeg] at hdim
  exact_mod_cast hdim

/-- On a genus-one function field, the Riemann--Roch space of `nP` at a rational place has
dimension `n` for every positive natural number `n`. -/
theorem dim_single_of_genus_eq_one (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) (hg : genus k F = 1) {P : Place k F}
    (hP : P.degree = 1) {n : ℕ} (hn : 1 ≤ n) :
    dim (Finsupp.single P (n : ℤ) : Divisor k F) = n := by
  rw [WeilDivisor.single_eq_zsmul_ofPoint,
    dim_natCast_zsmul_ofPoint_of_genus_eq_one hF hex hg hn, hP, Nat.mul_one]

end Divisor

/-! ### Functions with one prescribed pole -/

namespace Place

/-- The uniform bound `2g <= n` implies the sharper hypothesis `2g - 1 <= (n - 1) * deg P` used
by the prescribed-pole construction, because every place has degree at least one. -/
private theorem two_mul_genus_sub_one_le_sub_one_mul_degree (hF : IsFunctionField k F)
    {P : Place k F} {n : ℕ} (hn : 2 * genus k F ≤ n) (hnpos : 0 < n) :
    2 * (genus k F : ℤ) - 1 ≤ ((n : ℤ) - 1) * P.degree := by
  have hPdeg : (1 : ℤ) ≤ P.degree := by
    exact_mod_cast P.one_le_degree_of_isFunctionField hF
  have hncast : 2 * (genus k F : ℤ) ≤ n := by
    exact_mod_cast hn
  have hnsub_le_mul : (n : ℤ) - 1 ≤ ((n : ℤ) - 1) * P.degree :=
    le_mul_of_one_le_right (by omega) hPdeg
  omega

/-- If the Riemann--Roch dimensions of `(n - 1)P` and `nP` differ, there is a nonzero function
with order exactly `-n` at `P` that is regular at every other place. -/
theorem exists_ord_eq_neg_and_forall_ne_ord_nonneg_of_dim_lt
    (hF : IsFunctionField k F) (P : Place k F) {n : ℕ} (hnpos : 0 < n)
    (hdimlt : Divisor.dim (((n - 1 : ℕ) : ℤ) • WeilDivisor.ofPoint P) <
      Divisor.dim ((n : ℤ) • WeilDivisor.ofPoint P)) :
    ∃ x : F, x ≠ 0 ∧ P.ord x = -(n : ℤ) ∧ ∀ Q : Place k F, Q ≠ P → 0 ≤ Q.ord x := by
  let D : Divisor k F := (n : ℤ) • WeilDivisor.ofPoint P
  let E : Divisor k F := ((n - 1 : ℕ) : ℤ) • WeilDivisor.ofPoint P
  have hnsub : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := by
    omega
  have hED : E ≤ D := by
    refine WeilDivisor.le_iff.mpr fun Q ↦ ?_
    rcases eq_or_ne Q P with rfl | hQP
    · simp only [E, D, WeilDivisor.coeff_zsmul, WeilDivisor.coeff_ofPoint_self, mul_one,
        hnsub]
      omega
    · simp [E, D, WeilDivisor.coeff_ofPoint_of_ne hQP]
  let _ := finiteDimensional_riemannRochSpace hF D
  have hfinranklt : Module.finrank k (riemannRochSpace E) <
      Module.finrank k (riemannRochSpace D) := by
    simpa only [← Divisor.dim_def, E, D] using hdimlt
  have hlt : riemannRochSpace E < riemannRochSpace D :=
    Submodule.lt_of_le_of_finrank_lt_finrank (riemannRochSpace_mono hED) hfinranklt
  obtain ⟨x, hxD, hxE⟩ := SetLike.exists_of_lt hlt
  have hx0 : x ≠ 0 := fun hx ↦ hxE (hx ▸ Submodule.zero_mem _)
  have hxDord := (mem_riemannRochSpace_iff_neg_le_ord hx0).mp hxD
  have hxnotE : ¬∀ Q : Place k F, -E.coeff Q ≤ Q.ord x := by
    simpa [mem_riemannRochSpace_iff_neg_le_ord hx0] using hxE
  push Not at hxnotE
  obtain ⟨Q, hQ⟩ := hxnotE
  have hQP : Q = P := by
    by_contra hne
    have hxQ := hxDord Q
    simp only [E, D, WeilDivisor.coeff_zsmul,
      WeilDivisor.coeff_ofPoint_of_ne hne] at hxQ hQ
    omega
  subst Q
  refine ⟨x, hx0, ?_, fun Q hQP ↦ ?_⟩
  · have hxP := hxDord P
    simp only [D, WeilDivisor.coeff_zsmul, WeilDivisor.coeff_ofPoint_self, mul_one] at hxP
    simp only [E, WeilDivisor.coeff_zsmul, WeilDivisor.coeff_ofPoint_self, mul_one,
      hnsub] at hQ
    omega
  · have hxQ := hxDord Q
    simp only [D, WeilDivisor.coeff_zsmul, WeilDivisor.coeff_ofPoint_of_ne hQP,
      mul_zero] at hxQ
    omega

/-- For every place `P` and every positive `n` with `2g - 1 <= (n - 1) * deg P`, there is a
nonzero function with a pole of order exactly `n` at `P` and no other poles (Stichtenoth,
Proposition 1.6.6).

The hypothesis is exactly what makes `(n - 1)P` a high-degree divisor, so the consecutive
Riemann--Roch spaces differ in dimension. -/
theorem exists_ord_eq_neg_and_forall_ne_ord_nonneg_of_two_mul_genus_sub_one_le_sub_one_mul_degree
    (hF : IsFunctionField k F) (hex : IsIntegrallyClosedIn k F) (P : Place k F) {n : ℕ}
    (hnpos : 0 < n) (hn : 2 * (genus k F : ℤ) - 1 ≤ ((n : ℤ) - 1) * P.degree) :
    ∃ x : F, x ≠ 0 ∧ P.ord x = -(n : ℤ) ∧ ∀ Q : Place k F, Q ≠ P → 0 ≤ Q.ord x := by
  let D : Divisor k F := (n : ℤ) • WeilDivisor.ofPoint P
  let E : Divisor k F := ((n - 1 : ℕ) : ℤ) • WeilDivisor.ofPoint P
  have hnsub : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := by
    omega
  have hhighE : 2 * (genus k F : ℤ) - 1 ≤ Divisor.degree E := by
    simp only [E, Divisor.degree_zsmul, Divisor.degree_ofPoint, hnsub]
    exact hn
  have hED : E ≤ D := by
    refine WeilDivisor.le_iff.mpr fun Q ↦ ?_
    rcases eq_or_ne Q P with rfl | hQP
    · simp only [E, D, WeilDivisor.coeff_zsmul, WeilDivisor.coeff_ofPoint_self, mul_one,
        hnsub]
      omega
    · simp [E, D, WeilDivisor.coeff_ofPoint_of_ne hQP]
  have hhighD : 2 * (genus k F : ℤ) - 1 ≤ Divisor.degree D :=
    hhighE.trans (Divisor.degree_le_of_le hED)
  have hdimE :=
    Divisor.dim_eq_degree_add_one_sub_genus_of_two_mul_genus_sub_one_le_degree
      hF hex hhighE
  have hdimD :=
    Divisor.dim_eq_degree_add_one_sub_genus_of_two_mul_genus_sub_one_le_degree
      hF hex hhighD
  have hPdeg : (1 : ℤ) ≤ P.degree := by
    exact_mod_cast P.one_le_degree_of_isFunctionField hF
  have hdimlt : Divisor.dim E < Divisor.dim D := by
    have hdeg : Divisor.degree D = Divisor.degree E + P.degree := by
      simp only [D, E, Divisor.degree_zsmul, Divisor.degree_ofPoint, hnsub]
      ring
    omega
  exact P.exists_ord_eq_neg_and_forall_ne_ord_nonneg_of_dim_lt hF hnpos (by
    simpa only [E, D] using hdimlt)

/-- For every place `P` and natural number `n >= 2g`, there is a nonzero function with order `-n`
at `P` that is regular at every other place (Stichtenoth, Proposition 1.6.6). -/
theorem exists_ord_eq_neg_and_forall_ne_ord_nonneg (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) (P : Place k F) {n : ℕ} (hn : 2 * genus k F ≤ n) :
    ∃ x : F, x ≠ 0 ∧ P.ord x = -(n : ℤ) ∧ ∀ Q : Place k F, Q ≠ P → 0 ≤ Q.ord x := by
  rcases n.eq_zero_or_pos with rfl | hnpos
  · refine ⟨1, one_ne_zero, ?_, fun Q _ ↦ ?_⟩
    · simp
    · simp
  · exact
      P.exists_ord_eq_neg_and_forall_ne_ord_nonneg_of_two_mul_genus_sub_one_le_sub_one_mul_degree
        hF hex hnpos (two_mul_genus_sub_one_le_sub_one_mul_degree hF hn hnpos)

/-- For every place `P` and every positive `n` with `2g - 1 <= (n - 1) * deg P`, some function
has pole divisor exactly `nP` (Stichtenoth, Proposition 1.6.6). -/
theorem exists_poles_eq_natCast_zsmul_ofPoint_of_two_mul_genus_sub_one_le_sub_one_mul_degree
    (hF : IsFunctionField k F) (hex : IsIntegrallyClosedIn k F) (P : Place k F) {n : ℕ}
    (hnpos : 0 < n) (hn : 2 * (genus k F : ℤ) - 1 ≤ ((n : ℤ) - 1) * P.degree) :
    ∃ z : Fˣ, Divisor.poles hF z = (n : ℤ) • WeilDivisor.ofPoint P := by
  obtain ⟨x, hx0, hxP, hxQ⟩ :=
    P.exists_ord_eq_neg_and_forall_ne_ord_nonneg_of_two_mul_genus_sub_one_le_sub_one_mul_degree
      hF hex hnpos hn
  refine ⟨Units.mk0 x hx0, WeilDivisor.ext fun Q ↦ ?_⟩
  rcases eq_or_ne Q P with rfl | hQP
  · rw [Divisor.coeff_poles, Units.val_mk0, hxP, WeilDivisor.coeff_zsmul,
      WeilDivisor.coeff_ofPoint_self, mul_one]
    omega
  · rw [Divisor.coeff_poles, Units.val_mk0, WeilDivisor.coeff_zsmul,
      WeilDivisor.coeff_ofPoint_of_ne hQP, mul_zero]
    have := hxQ Q hQP
    omega

/-- For every place `P` and `n >= 2g`, some function has pole divisor exactly `nP`
(Stichtenoth, Proposition 1.6.6). -/
theorem exists_poles_eq_natCast_zsmul_ofPoint (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) (P : Place k F) {n : ℕ} (hn : 2 * genus k F ≤ n) :
    ∃ z : Fˣ, Divisor.poles hF z = (n : ℤ) • WeilDivisor.ofPoint P := by
  rcases n.eq_zero_or_pos with rfl | hnpos
  · exact ⟨1, WeilDivisor.ext fun Q ↦ by simp⟩
  · exact
      P.exists_poles_eq_natCast_zsmul_ofPoint_of_two_mul_genus_sub_one_le_sub_one_mul_degree
        hF hex hnpos (two_mul_genus_sub_one_le_sub_one_mul_degree hF hn hnpos)

end Place

end TauCeti
