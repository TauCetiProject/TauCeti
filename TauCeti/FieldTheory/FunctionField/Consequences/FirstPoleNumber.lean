/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Consequences.WeierstrassGaps
public import TauCeti.FieldTheory.FunctionField.Place.Expansion.Laurent.Equiv
import TauCeti.FieldTheory.FunctionField.RiemannRoch.Equiv

/-!
# Functions whose pole order is the first pole number

Let `P` be a rational place of a function field `F / k` with exact constant field `k`, and let
`m` be the least positive pole number at `P`: the smallest pole order of a function regular away
from `P`. Such an `m` exists, since every integer at least `2g` is a pole number.

Every function whose only pole is at `P`, of order at most `m`, is a constant plus a multiple of
any fixed function `z` with a pole of order exactly `m` at `P`:

`L(m P) = k ⊕ k z`.

Indeed, the gaps in `1, …, m` are `1, …, m - 1`, so by the gap count `ℓ(m P) = 2`.

The affine freedom `z ↦ a z + b` is removed by a normalization of the Laurent expansion in a
uniformizer `t` at `P`: there is exactly one `z ∈ L(m P)` whose coefficient of `t ^ (-m)` is `1`
and whose constant coefficient is `0`. The normalized function depends only on `P` and `t`.
This rigidification is what makes the function canonical in Köck's proof that a Belyi pair over
`ℂ` descends to a number field: a field automorphism carrying the constants along an automorphism
`σ` of `k` and fixing `P` and `t` acts on Laurent coefficients by `σ`, which fixes `0` and `1`, so
it fixes the normalized function.

## Main results

* `TauCeti.Place.exists_pos_isPoleNumber_and_isGap_of_lt`: the least positive pole number at a
  place exists.
* `TauCeti.Place.riemannRochSpace_zsmul_ofPoint_eq_span_pair`: for the least positive pole
  number `m` at a rational place and any `z` with a pole of order exactly `m` there and no other
  pole, `L(m P)` is spanned by `1` and `z`.
* `TauCeti.Place.existsUnique_laurentCoeff_eq_one_and_laurentCoeff_zero_eq_zero`: there is a
  unique function in `L(m P)` whose Laurent expansion in `t` has coefficient `1` at `t ^ (-m)`
  and constant coefficient `0`.
* `TauCeti.Place.apply_eq_self_of_laurentCoeff_eq_one_of_laurentCoeff_zero_eq_zero`: a semilinear
  field automorphism fixing `P` and `t` fixes that function.

## References

* B. Köck, *Belyi's theorem revisited*, Beiträge zur Algebra und Geometrie 45 (2004), 253–265,
  proof of (2.2) Theorem.
* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Theorem 1.6.8.
-/

public section

namespace TauCeti

open AlgebraicGeometry

variable {k F : Type*} [Field k] [Field F] [Algebra k F]

namespace Place

/-- **The least positive pole number exists.** At every place of a function field with exact
constant field there is a positive pole number `m` below which every positive integer is a gap. -/
theorem exists_pos_isPoleNumber_and_isGap_of_lt (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) (P : Place k F) :
    ∃ m : ℕ, 0 < m ∧ P.IsPoleNumber m ∧ ∀ n, 0 < n → n < m → P.IsGap n := by
  classical
  have h : ∃ m : ℕ, 0 < m ∧ P.IsPoleNumber m :=
    ⟨2 * genus k F + 1, by omega,
      by simpa using P.not_isGap_of_two_mul_genus_le hF hex le_self_add⟩
  exact ⟨Nat.find h, (Nat.find_spec h).1, (Nat.find_spec h).2,
    fun n hn hlt ↦ (P.isGap_iff_not_isPoleNumber n).mpr fun hpole ↦
      Nat.find_min h hlt ⟨hn, hpole⟩⟩

/-- **`L(m P) = k ⊕ k z` for the first pole number `m`.** Let `P` be a rational place of a
function field with exact constant field, and let `m > 0` be such that every positive integer
below `m` is a gap at `P`. If `z` has a pole of order exactly `m` at `P` and no other pole, then
the functions with poles bounded by `m P` are exactly the combinations `a z + b` with
`a, b ∈ k`. -/
theorem riemannRochSpace_zsmul_ofPoint_eq_span_pair (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) {P : Place k F} (hP : P.degree = 1) {m : ℕ} (hm : 0 < m)
    (hgap : ∀ n, 0 < n → n < m → P.IsGap n) {z : F} (hzP : P.ord z = -m)
    (hz : ∀ Q : Place k F, Q ≠ P → 0 ≤ Q.ord z) :
    riemannRochSpace ((m : ℤ) • WeilDivisor.ofPoint P) = Submodule.span k {1, z} := by
  have hz0 : z ≠ 0 := by
    rintro rfl
    simp at hzP
    omega
  -- The gaps in `1, …, m` are exactly `1, …, m - 1`, so the gap count gives `ℓ(m P) = 2`.
  have hgaps : P.gapNumbersUpTo m = Finset.Icc 1 (m - 1) := by
    ext n
    simp only [mem_gapNumbersUpTo_iff, Finset.mem_Icc]
    refine ⟨fun ⟨h1, hn, hng⟩ ↦ ⟨h1, ?_⟩, fun ⟨h1, hn⟩ ↦ ⟨h1, by omega, hgap n h1 (by omega)⟩⟩
    rcases hn.lt_or_eq with hn | rfl
    · omega
    · exact absurd ((P.isPoleNumber_iff n).mpr ⟨z, hz0, hzP, hz⟩)
        ((P.isGap_iff_not_isPoleNumber n).mp hng)
  have hdim := P.card_gapNumbersUpTo_add_dim hF hex hP m
  rw [hgaps, Nat.card_Icc] at hdim
  -- A nonconstant `z` is linearly independent from `1`, so `span {1, z}` also has dimension 2.
  have hli : LinearIndependent k ![(1 : F), z] := by
    refine (LinearIndependent.pair_iff' one_ne_zero).mpr fun a ha ↦ ?_
    rw [Algebra.smul_def, mul_one] at ha
    have := P.ord_eq_zero_of_isAlgebraic (ha ▸ isAlgebraic_algebraMap a)
    omega
  have hspan : Module.finrank k (Submodule.span k {(1 : F), z}) = 2 := by
    rw [← Matrix.range_cons_cons_empty (1 : F) z ![], finrank_span_eq_card hli, Fintype.card_fin]
  have := finiteDimensional_riemannRochSpace hF ((m : ℤ) • WeilDivisor.ofPoint P)
  refine (Submodule.eq_of_le_of_finrank_eq ?_ ?_).symm
  · rw [Submodule.span_le, Set.insert_subset_iff, Set.singleton_subset_iff]
    refine ⟨one_mem_riemannRochSpace_iff.mpr ?_,
      (mem_riemannRochSpace_zsmul_ofPoint_iff hz0).mpr ⟨by omega, hz⟩⟩
    exact zsmul_nonneg (WeilDivisor.ofPoint_nonneg P)
      (by omega)
  · rw [hspan, ← Divisor.dim_def]
    omega

/-- **The normalized function with a pole of the first pole order.** Let `P` be a rational place
of a function field with exact constant field, `t` a uniformizer at `P`, and `m` the least
positive pole number at `P`. Then exactly one function `z` with poles bounded by `m P` has
Laurent expansion in `t` with coefficient `1` at `t ^ (-m)` and constant coefficient `0`. -/
theorem existsUnique_laurentCoeff_eq_one_and_laurentCoeff_zero_eq_zero
    (hF : IsFunctionField k F) (hex : IsIntegrallyClosedIn k F) {P : Place k F}
    (hP : P.degree = 1) {t : F} (ht : P.ord t = 1) {m : ℕ} (hm : 0 < m)
    (hpole : P.IsPoleNumber m) (hgap : ∀ n, 0 < n → n < m → P.IsGap n) :
    ∃! z, z ∈ riemannRochSpace ((m : ℤ) • WeilDivisor.ofPoint P) ∧
      P.laurentCoeff hP ht (-m) z = 1 ∧ P.laurentCoeff hP ht 0 z = 0 := by
  obtain ⟨z₀, hz₀, hz₀P, hz₀Q⟩ := (P.isPoleNumber_iff m).mp hpole
  rw [riemannRochSpace_zsmul_ofPoint_eq_span_pair hF hex hP hm hgap hz₀P hz₀Q]
  -- Write the leading and constant coefficients of `z₀` as `c ≠ 0` and `d`.
  set c := P.laurentCoeff hP ht (-m) z₀ with hc
  set d := P.laurentCoeff hP ht 0 z₀ with hd
  have hc0 : c ≠ 0 := by simpa only [hz₀P] using P.laurentCoeff_ord_ne_zero hP ht hz₀
  have hm0 : (-m : ℤ) ≠ 0 := by omega
  -- On `a • 1 + b • z₀` the two coefficients are `b c` and `a + b d`.
  have hcoeff (a b : k) : P.laurentCoeff hP ht (-m) (a • 1 + b • z₀) = b * c ∧
      P.laurentCoeff hP ht 0 (a • 1 + b • z₀) = a + b * d := by
    rw [← Algebra.algebraMap_eq_smul_one, map_add, map_add, map_smul, map_smul,
      laurentCoeff_algebraMap, laurentCoeff_algebraMap, ← hc, ← hd]
    simp [hm0]
  refine ⟨-(c⁻¹ * d) • 1 + c⁻¹ • z₀, ⟨Submodule.mem_span_pair.mpr ⟨_, _, rfl⟩, ?_⟩, ?_⟩
  · rw [(hcoeff _ _).1, (hcoeff _ _).2, inv_mul_cancel₀ hc0]
    exact ⟨rfl, by ring⟩
  · rintro z ⟨hz, h1, h0⟩
    obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hz
    rw [(hcoeff a b).1] at h1
    rw [(hcoeff a b).2] at h0
    have hb : b = c⁻¹ := eq_inv_of_mul_eq_one_left h1
    have ha : a = -(c⁻¹ * d) := by rw [← hb]; linear_combination h0
    rw [ha, hb]

/-- **Semilinear automorphisms fixing `P` and `t` fix the normalized function.** Let `P` be a
rational place of a function field with exact constant field, `t` a uniformizer at `P`, `m` the
least positive pole number at `P`, and `z` the function of
`TauCeti.Place.existsUnique_laurentCoeff_eq_one_and_laurentCoeff_zero_eq_zero`. Every field
automorphism `τ` of `F` that carries the constants along an automorphism `σ` of `k`, maps `P` to
itself, and fixes `t`, fixes `z`. -/
theorem apply_eq_self_of_laurentCoeff_eq_one_of_laurentCoeff_zero_eq_zero
    (hF : IsFunctionField k F) (hex : IsIntegrallyClosedIn k F) {P : Place k F}
    (hP : P.degree = 1) {t : F} (ht : P.ord t = 1) {m : ℕ} (hm : 0 < m)
    (hpole : P.IsPoleNumber m) (hgap : ∀ n, 0 < n → n < m → P.IsGap n) (σ : k ≃+* k)
    (τ : F ≃+* F) (h : ∀ c, τ (algebraMap k F c) = algebraMap k F (σ c))
    (hτP : equivOfRingEquiv σ τ h P = P) (hτt : τ t = t) {z : F}
    (hz : z ∈ riemannRochSpace ((m : ℤ) • WeilDivisor.ofPoint P))
    (h₁ : P.laurentCoeff hP ht (-m) z = 1) (h₀ : P.laurentCoeff hP ht 0 z = 0) : τ z = z := by
  have hcoeff (n : ℤ) : P.laurentCoeff hP ht n (τ z) = σ (P.laurentCoeff hP ht n z) :=
    laurentCoeff_equivOfRingEquiv σ τ h hP ht hτP hP hτt ht n z
  refine (existsUnique_laurentCoeff_eq_one_and_laurentCoeff_zero_eq_zero hF hex hP ht hm hpole
    hgap).unique ⟨?_, ?_, ?_⟩ ⟨hz, h₁, h₀⟩
  · -- `τ` maps `L(m P)` onto `L(m τ(P)) = L(m P)`.
    have hD : Finsupp.domCongr (equivOfRingEquiv σ τ h) ((m : ℤ) • WeilDivisor.ofPoint P) =
        (m : ℤ) • WeilDivisor.ofPoint P := by
      rw [map_zsmul, WeilDivisor.domCongr_ofPoint, hτP]
    rwa [← hD, mem_riemannRochSpace_domCongr_equivOfRingEquiv_iff]
  · rw [hcoeff, h₁, map_one]
  · rw [hcoeff, h₀, map_zero]

end Place

end TauCeti
