/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Consequences.WeierstrassGaps
public import TauCeti.FieldTheory.FunctionField.Hyperelliptic.RationalSubfield
public import TauCeti.FieldTheory.FunctionField.RiemannRoch.Conorm
-- Proof-only: `k(x)` has genus zero; degrees of places in an extension.
import TauCeti.FieldTheory.FunctionField.Consequences.GenusZero
import TauCeti.FieldTheory.FunctionField.Place.Extension.Degree

/-!
# Weierstrass gaps at the rational places of a double cover of the line

Let `F / k` be a function field with exact constant field `k` and genus `g`, and let `x ∈ F` be
transcendental with `[F : k(x)] = 2`; for `g ≥ 2` this is a hyperelliptic function field. The
Weierstrass gaps at a rational place `P` of `F` are decided by whether `P` ramifies over `k(x)`:

* if `P` is ramified, its gaps are the odd numbers `1, 3, …, 2g - 1`;
* if `P` is unramified, its gaps are `1, 2, …, g`.

For `g ≥ 2` the two gap sequences differ, so a rational place has `2` as a pole number exactly when
it ramifies over `k(x)`: the rational places whose gap sequence is not `1, …, g` are exactly the
ramified ones. In terms of Weierstrass weights, the ramified rational places have the maximal
weight `g (g - 1) / 2` and the unramified ones have weight `0`. Conversely, away from
characteristic two or over a perfect field, a function field of genus `g ≥ 2` with a rational
place at which `2` is a pole number, that is, a rational place of maximal weight, is
hyperelliptic.

## Main results

* `TauCeti.Place.ramificationIdx_mul_relativeDegree_eq_two_of_isPoleNumber`: a positive pole
  number `m` at `P` with `m · deg P ≤ g` makes `P` the only place over its restriction to `k(x)`.
* `TauCeti.Place.isPoleNumber_two_of_one_lt_ramificationIdx`: `2` is a pole number at a ramified
  rational place.
* `TauCeti.Place.weierstrassGaps_eq_image_range_of_one_lt_ramificationIdx`: the gaps at a ramified
  rational place are `1, 3, …, 2g - 1`.
* `TauCeti.Place.weierstrassGaps_eq_Icc_of_ramificationIdx_eq_one`: the gaps at an unramified
  rational place are `1, …, g`.
* `TauCeti.Place.isPoleNumber_two_iff_one_lt_ramificationIdx`: for `g ≥ 2`, `2` is a pole number
  at a rational place exactly when the place ramifies over `k(x)`.
* `TauCeti.Place.weierstrassWeight_eq_genus_choose_two_iff_one_lt_ramificationIdx` and
  `TauCeti.Place.weierstrassWeight_eq_zero_of_ramificationIdx_eq_one`: ramified rational places
  have weight `g (g - 1) / 2`, unramified ones weight `0`.
* `TauCeti.isHyperellipticFunctionField_of_isPoleNumber_two` and
  `TauCeti.isHyperellipticFunctionField_of_isPoleNumber_two_of_perfectField`: a rational place at
  which `2` is a pole number makes a function field of genus at least two hyperelliptic, away from
  characteristic two or over a perfect field.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Theorem 1.6.8 and Proposition 6.2.4.
* H. M. Farkas and I. Kra, *Riemann Surfaces*, 2nd ed., GTM 71, Springer, 1992, Section III.7,
  for the gap sequences of a hyperelliptic Riemann surface.
-/

public section

open scoped IntermediateField

namespace TauCeti

open AlgebraicGeometry

variable {k F : Type*} [Field k] [Field F] [Algebra k F]

namespace Place

variable (hF : IsFunctionField k F) (hex : IsIntegrallyClosedIn k F) {x : F}
  (hx : Transcendental k x) (hdeg : Module.finrank k⟮x⟯ F = 2) [FiniteDimensional k⟮x⟯ F]
include hF hex hx hdeg

omit hF hex in
/-- If the conorm of an effective divisor `D₀` of `k(x)` is a positive multiple `m P` of a single
place, then `e(P ∣ P₀) f(P ∣ P₀) = 2` for the restriction `P₀` of `P`. -/
private theorem ramificationIdx_mul_relativeDegree_eq_two_of_conorm_eq {P : Place k F} {m : ℕ}
    (hm : 0 < m) {D₀ : Divisor k k⟮x⟯} (hD₀ : 0 ≤ D₀)
    (hcon : Divisor.conorm k F D₀ = (m : ℤ) • WeilDivisor.ofPoint P) :
    ramificationIdx k⟮x⟯ P * relativeDegree k k⟮x⟯ P = 2 := by
  have hK : IsFunctionField k k⟮x⟯ := hx.isFunctionField_adjoin
  set P₀ := P.restrict k k⟮x⟯
  -- Degrees: `m deg P = 2 deg D₀`.
  have hdegcon : (m : ℤ) * P.degree = 2 * Divisor.degree D₀ := by
    have h := Divisor.degree_conorm_of_finrank_eq_one k F hK (Module.finrank_self k) D₀
    rw [hcon, hdeg] at h
    simpa using h
  -- The coefficient at `P`: `m = e(P ∣ P₀) D₀(P₀)`.
  have hcoeff : (m : ℤ) = ramificationIdx k⟮x⟯ P * D₀.coeff P₀ := by
    have h := congrArg (fun D : Divisor k F ↦ D.coeff P) hcon
    simp only [Divisor.coeff_conorm, WeilDivisor.coeff_zsmul,
      WeilDivisor.coeff_ofPoint_self, mul_one] at h
    exact h.symm
  -- `D₀` is effective, so `D₀(P₀) deg P₀ ≤ deg D₀`.
  have hsingle : D₀.coeff P₀ • WeilDivisor.ofPoint P₀ ≤ D₀ := by
    refine WeilDivisor.le_iff.mpr fun Q ↦ ?_
    rw [WeilDivisor.coeff_zsmul]
    rcases eq_or_ne Q P₀ with rfl | hQ
    · rw [WeilDivisor.coeff_ofPoint_self, mul_one]
    · rw [WeilDivisor.coeff_ofPoint_of_ne hQ, mul_zero]
      exact WeilDivisor.coeff_le_coeff hD₀ Q
  have hcdeg : D₀.coeff P₀ * P₀.degree ≤ Divisor.degree D₀ := by
    simpa using Divisor.degree_le_of_le hsingle
  -- With `deg P = deg P₀ · f`: `c deg P₀ · (e f) = m deg P = 2 deg D₀ ≥ 2 c deg P₀`, where
  -- `c = D₀(P₀)`, and `c deg P₀ > 0`, so `e f ≥ 2`; the fundamental inequality gives `e f ≤ 2`.
  have hPdeg := degree_eq_degree_restrict_mul_relativeDegree k k⟮x⟯ P
  have hle := ramificationIdx_mul_relativeDegree_le_finrank k k⟮x⟯ P
  rw [hdeg] at hle
  have hP₀ : 1 ≤ P₀.degree := P₀.one_le_degree_of_isFunctionField hK
  set e := ramificationIdx k⟮x⟯ P
  set f := relativeDegree k k⟮x⟯ P
  set c := D₀.coeff P₀
  have hc : 0 < c := by
    rcases (Int.natCast_nonneg e).lt_or_eq with he | he
    · nlinarith
    · rw [← he] at hcoeff
      omega
  have hkey : c * P₀.degree * 2 ≤ c * P₀.degree * (e * f : ℕ) := by
    rw [hPdeg] at hdegcon
    push_cast at hdegcon ⊢
    rw [hcoeff] at hdegcon
    nlinarith
  have hpos : 0 < c * P₀.degree := mul_pos hc (by exact_mod_cast hP₀)
  have h2 : (2 : ℤ) ≤ (e * f : ℕ) := le_of_mul_le_mul_left hkey hpos
  omega

/-- **A positive pole number `m` with `m · deg P ≤ g` forces `e f = 2` over `k(x)`.** If
`[F : k(x)] = 2`, then `e(P ∣ P₀) f(P ∣ P₀) = 2` for the restriction `P₀` of `P` to `k(x)`.
This uses Stichtenoth, Proposition 6.2.4(a). -/
theorem ramificationIdx_mul_relativeDegree_eq_two_of_isPoleNumber {P : Place k F} {m : ℕ}
    (hP : P.IsPoleNumber m) (hm : 0 < m) (hmg : m * P.degree ≤ genus k F) :
    ramificationIdx k⟮x⟯ P * relativeDegree k k⟮x⟯ P = 2 := by
  obtain ⟨z, hz0, hzP, hzQ⟩ := (P.isPoleNumber_iff m).mp hP
  obtain ⟨u, rfl⟩ : ∃ u : Fˣ, (u : F) = z := ⟨Units.mk0 z hz0, rfl⟩
  have hK : IsFunctionField k k⟮x⟯ := hx.isFunctionField_adjoin
  -- The pole divisor of `u` is `m P`, of degree `[F : k(u)] = m deg P ≤ g`, so `u ∈ k(x)` by
  -- Stichtenoth, Proposition 6.2.4(a) (`mem_adjoin_of_finrank_adjoin_le_genus`).
  have hpoles : Divisor.poles hF u = (m : ℤ) • WeilDivisor.ofPoint P := by
    refine WeilDivisor.ext fun Q ↦ ?_
    rw [Divisor.coeff_poles, WeilDivisor.coeff_zsmul]
    rcases eq_or_ne Q P with rfl | hQP
    · rw [hzP, WeilDivisor.coeff_ofPoint_self]
      omega
    · rw [WeilDivisor.coeff_ofPoint_of_ne hQP]
      have := hzQ Q hQP
      omega
  have hzalg : ¬IsAlgebraic k (u : F) := fun h ↦ by
    have := P.ord_eq_zero_of_isAlgebraic h
    omega
  have hfinrank : (Module.finrank k⟮(u : F)⟯ F : ℤ) = m * P.degree := by
    simpa [hpoles] using (Divisor.degree_poles hF u hzalg).symm
  have hzx : (u : F) ∈ k⟮x⟯ := mem_adjoin_of_finrank_adjoin_le_genus hF hex hx hdeg (by omega)
  -- Its pole divisor is then the conorm of its pole divisor in `k(x)`.
  set z₀ : k⟮x⟯ := ⟨u, hzx⟩
  have hz₀ : z₀ ≠ 0 := fun h ↦ hz0 (congrArg Subtype.val h)
  refine ramificationIdx_mul_relativeDegree_eq_two_of_conorm_eq hx hdeg hm
    (Divisor.isEffective_poles hK (Units.mk0 z₀ hz₀)).zero_le ?_
  rw [Divisor.conorm_poles k F hK hF, ← hpoles]
  congr 1
  exact Units.ext (by simp [z₀])

omit hex in
/-- At a rational place ramified over `k(x)`, the restriction `P₀` is rational and `P` is the only
place above it: `Con(P₀) = 2 P`. -/
private theorem conorm_ofPoint_restrict_of_one_lt_ramificationIdx {P : Place k F}
    (hP : P.degree = 1) (hram : 1 < ramificationIdx k⟮x⟯ P) :
    (P.restrict k k⟮x⟯).degree = 1 ∧
      Divisor.conorm k F (WeilDivisor.ofPoint (P.restrict k k⟮x⟯)) =
        (2 : ℤ) • WeilDivisor.ofPoint P := by
  have hK : IsFunctionField k k⟮x⟯ := hx.isFunctionField_adjoin
  set P₀ := P.restrict k k⟮x⟯
  have hP₀ : P₀.degree = 1 :=
    le_antisymm (hP ▸ degree_restrict_le k k⟮x⟯ P) (P₀.one_le_degree_of_isFunctionField hK)
  have he : ramificationIdx k⟮x⟯ P = 2 :=
    le_antisymm (hdeg ▸ ramificationIdx_le_finrank k⟮x⟯ P) hram
  refine ⟨hP₀, ?_⟩
  -- `Con(P₀) - 2P` is effective of degree `2 deg P₀ - 2 deg P = 0`, hence zero.
  set E := Divisor.conorm k F (WeilDivisor.ofPoint P₀) - (2 : ℤ) • WeilDivisor.ofPoint P
  have hE : 0 ≤ E := by
    refine WeilDivisor.le_iff.mpr fun Q ↦ ?_
    simp only [E, WeilDivisor.coeff_sub, WeilDivisor.coeff_zsmul, Divisor.coeff_conorm,
      WeilDivisor.coeff_zero]
    rcases eq_or_ne Q P with rfl | hQP
    · simp [he, P₀]
    · rw [WeilDivisor.coeff_ofPoint_of_ne hQP, mul_zero, sub_zero]
      exact mul_nonneg (Int.natCast_nonneg _)
        (WeilDivisor.coeff_le_coeff (WeilDivisor.isEffective_ofPoint P₀).zero_le _)
  have hEdeg : Divisor.degree E = 0 := by
    simp only [E, map_sub, Divisor.degree_conorm_of_finrank_eq_one k F hK (Module.finrank_self k),
      hdeg, Divisor.degree_ofPoint, hP₀, Divisor.degree_zsmul, hP]
    norm_num
  exact sub_eq_zero.mp ((Divisor.degree_eq_zero_iff hF hE).mp hEdeg)

/-- **`2` is a pole number at a rational place ramified over `k(x)`.** -/
theorem isPoleNumber_two_of_one_lt_ramificationIdx {P : Place k F} (hP : P.degree = 1)
    (hram : 1 < ramificationIdx k⟮x⟯ P) : P.IsPoleNumber 2 := by
  have hK : IsFunctionField k k⟮x⟯ := hx.isFunctionField_adjoin
  obtain ⟨hP₀, hcon⟩ :=
    conorm_ofPoint_restrict_of_one_lt_ramificationIdx hF hx hdeg hP hram
  set P₀ := P.restrict k k⟮x⟯
  -- The restriction `P₀` is rational with `Con(P₀) = 2P`, so `L(P₀)` lies in `L(2P)`, and
  -- `ℓ(P₀) ≥ 2` by Riemann's theorem on `k(x)`, of genus zero.
  have hdim₀ : 2 ≤ Divisor.dim (WeilDivisor.ofPoint P₀) := by
    have h := Divisor.degree_add_one_sub_genus_le_dim hK (WeilDivisor.ofPoint P₀)
    rw [Divisor.degree_ofPoint, hP₀, genus_adjoin_simple_eq_zero hx] at h
    omega
  -- `L(P₀)` embeds into `L(2P)`.
  have hmap : ∀ u ∈ riemannRochSpace (WeilDivisor.ofPoint P₀),
      (IsScalarTower.toAlgHom k k⟮x⟯ F).toLinearMap u ∈
        riemannRochSpace ((2 : ℤ) • WeilDivisor.ofPoint P) := fun u hu ↦ by
    rw [← hcon]
    exact (mem_riemannRochSpace_conorm_iff hF _ u).mpr hu
  have := finiteDimensional_riemannRochSpace hF ((2 : ℤ) • WeilDivisor.ofPoint P)
  have hdim : 2 ≤ Divisor.dim ((2 : ℤ) • WeilDivisor.ofPoint P) := by
    refine hdim₀.trans ?_
    rw [Divisor.dim_def, Divisor.dim_def]
    refine LinearMap.finrank_le_finrank_of_injective
      (f := (IsScalarTower.toAlgHom k k⟮x⟯ F).toLinearMap.restrict hmap) fun u v huv ↦ ?_
    exact Subtype.ext ((algebraMap k⟮x⟯ F).injective (by simpa using Subtype.ext_iff.mp huv))
  -- Either `ℓ(P) < ℓ(2P)`, or `ℓ(P) ≥ 2 > ℓ(0)` makes `1`, hence `2 = 1 + 1`, a pole number.
  by_cases hlt : Divisor.dim ((1 : ℤ) • WeilDivisor.ofPoint P) <
      Divisor.dim ((2 : ℤ) • WeilDivisor.ofPoint P)
  · exact (P.isPoleNumber_iff_dim_lt hF (by norm_num : 0 < 2)).mpr (by simpa using hlt)
  · have h1 : P.IsPoleNumber 1 := (P.isPoleNumber_iff_dim_lt hF (by norm_num : 0 < 1)).mpr (by
      simp only [Nat.sub_self, Nat.cast_zero, zero_smul, Nat.cast_one,
        Divisor.dim_zero_of_isIntegrallyClosedIn hF hex]
      omega)
    exact h1.add h1

/-- **The Weierstrass gaps at a ramified rational place are `1, 3, …, 2g - 1`.** -/
theorem weierstrassGaps_eq_image_range_of_one_lt_ramificationIdx {P : Place k F}
    (hP : P.degree = 1) (hram : 1 < ramificationIdx k⟮x⟯ P) :
    P.weierstrassGaps = (Finset.range (genus k F)).image fun i ↦ 2 * i + 1 :=
  weierstrassGaps_eq_image_range_of_isPoleNumber_two hF hex hP
    (isPoleNumber_two_of_one_lt_ramificationIdx hF hex hx hdeg hP hram)

/-- **No number up to the genus is a pole number at an unramified rational place.** -/
theorem isGap_of_ramificationIdx_eq_one {P : Place k F} (hP : P.degree = 1)
    (hram : ramificationIdx k⟮x⟯ P = 1) {m : ℕ} (hm : 0 < m) (hmg : m ≤ genus k F) :
    P.IsGap m := by
  -- A pole number `m` with `1 ≤ m ≤ g` would force `e(P ∣ P₀) f(P ∣ P₀) = 2`, while an
  -- unramified rational place has `e = f = 1`.
  rw [isGap_iff_not_isPoleNumber]
  intro hpole
  have h := ramificationIdx_mul_relativeDegree_eq_two_of_isPoleNumber hF hex hx hdeg hpole hm
    (by rwa [hP, mul_one])
  have hPdeg := degree_eq_degree_restrict_mul_relativeDegree k k⟮x⟯ P
  have hP₀ := (P.restrict k k⟮x⟯).one_le_degree_of_isFunctionField hx.isFunctionField_adjoin
  rw [hram, one_mul] at h
  rw [h, hP] at hPdeg
  omega

/-- **The Weierstrass gaps at an unramified rational place are `1, …, g`.** -/
theorem weierstrassGaps_eq_Icc_of_ramificationIdx_eq_one {P : Place k F} (hP : P.degree = 1)
    (hram : ramificationIdx k⟮x⟯ P = 1) : P.weierstrassGaps = Finset.Icc 1 (genus k F) := by
  refine (Finset.eq_of_subset_of_card_le (fun m hm ↦ ?_) ?_).symm
  · obtain ⟨hm1, hmg⟩ := Finset.mem_Icc.mp hm
    exact (P.mem_weierstrassGaps_iff_isGap hF hex m).mpr
      (isGap_of_ramificationIdx_eq_one hF hex hx hdeg hP hram hm1 hmg)
  · rw [card_weierstrassGaps hF hex hP, Nat.card_Icc, Nat.add_sub_cancel]

/-- **For `g ≥ 2`, `2` is a pole number at a rational place exactly when the place ramifies over
`k(x)`.** In particular the rational places whose gap sequence is not `1, …, g` are exactly the
ramified ones. -/
theorem isPoleNumber_two_iff_one_lt_ramificationIdx (hg : 2 ≤ genus k F) {P : Place k F}
    (hP : P.degree = 1) : P.IsPoleNumber 2 ↔ 1 < ramificationIdx k⟮x⟯ P := by
  refine ⟨fun h2 ↦ ?_, isPoleNumber_two_of_one_lt_ramificationIdx hF hex hx hdeg hP⟩
  by_contra hram
  have he : ramificationIdx k⟮x⟯ P = 1 := by
    have := ramificationIdx_pos k⟮x⟯ P
    omega
  exact absurd h2 ((P.isGap_iff_not_isPoleNumber 2).mp
    (isGap_of_ramificationIdx_eq_one hF hex hx hdeg hP he (by norm_num) hg))

/-- **A rational place has the maximal Weierstrass weight `g (g - 1) / 2` exactly when it ramifies
over `k(x)`**, for `g ≥ 2`: the branch places of the double cover are its places of maximal
weight. -/
theorem weierstrassWeight_eq_genus_choose_two_iff_one_lt_ramificationIdx (hg : 2 ≤ genus k F)
    {P : Place k F} (hP : P.degree = 1) :
    P.weierstrassWeight = (genus k F).choose 2 ↔ 1 < ramificationIdx k⟮x⟯ P :=
  (weierstrassWeight_eq_genus_choose_two_iff hF hex hP).trans
    (isPoleNumber_two_iff_one_lt_ramificationIdx hF hex hx hdeg hg hP)

/-- **A rational place unramified over `k(x)` has Weierstrass weight zero.** -/
theorem weierstrassWeight_eq_zero_of_ramificationIdx_eq_one {P : Place k F} (hP : P.degree = 1)
    (hram : ramificationIdx k⟮x⟯ P = 1) : P.weierstrassWeight = 0 :=
  (weierstrassWeight_eq_zero_iff hF hex hP).mpr
    (weierstrassGaps_eq_Icc_of_ramificationIdx_eq_one hF hex hx hdeg hP hram)

end Place

/-- If `2` is a pole number at `P`, then `ℓ(2P) ≥ 2`: `ℓ(P) < ℓ(2P)` and `ℓ(P) ≥ ℓ(0) = 1`. -/
private theorem two_le_dim_two_zsmul_ofPoint_of_isPoleNumber_two (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) {P : Place k F} (hpole : P.IsPoleNumber 2) :
    2 ≤ Divisor.dim ((2 : ℤ) • WeilDivisor.ofPoint P) := by
  have hlt := (P.isPoleNumber_iff_dim_lt hF (by norm_num : 0 < 2)).mp hpole
  have hle : Divisor.dim (0 : Divisor k F) ≤ Divisor.dim ((1 : ℤ) • WeilDivisor.ofPoint P) :=
    Divisor.dim_mono hF (by simpa using
      WeilDivisor.isEffective_iff_zero_le.mp (WeilDivisor.isEffective_ofPoint P))
  rw [Divisor.dim_zero_of_isIntegrallyClosedIn hF hex] at hle
  simp only [Nat.add_one_sub_one, Nat.cast_one, Nat.cast_ofNat] at hlt
  omega

/-- **A rational place at which `2` is a pole number makes a function field of genus `g ≥ 2`
hyperelliptic**, away from characteristic two: the divisor `2P` has degree two and `ℓ(2P) ≥ 2`.
By `TauCeti.Place.weierstrassWeight_eq_genus_choose_two_iff`, these are the rational places of
maximal Weierstrass weight `g (g - 1) / 2`, so a function field that is not hyperelliptic has
none. Over a perfect field the characteristic hypothesis can be dropped, see
`TauCeti.isHyperellipticFunctionField_of_isPoleNumber_two_of_perfectField`. -/
theorem isHyperellipticFunctionField_of_isPoleNumber_two (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) (h2 : (2 : k) ≠ 0) (hg : 2 ≤ genus k F) {P : Place k F}
    (hP : P.degree = 1) (hpole : P.IsPoleNumber 2) : IsHyperellipticFunctionField k F :=
  (isHyperellipticFunctionField_iff_two_le_genus_and_exists_degree_eq_two_and_two_le_dim
    hF hex h2).mpr ⟨hg, (2 : ℤ) • WeilDivisor.ofPoint P, by simp [hP],
      two_le_dim_two_zsmul_ofPoint_of_isPoleNumber_two hF hex hpole⟩

/-- **Over a perfect field, a rational place at which `2` is a pole number makes a function field
of genus `g ≥ 2` hyperelliptic**, in every characteristic: the divisor `2P` of degree two with
`ℓ(2P) ≥ 2` gives a rational subfield of index two. Over a perfect field the positive genus rules
out a purely inseparable index-two extension, so `F` is separable over this subfield, see
`TauCeti.isHyperellipticFunctionField_iff_two_le_genus_and_exists_finrank_adjoin_eq_two`. -/
theorem isHyperellipticFunctionField_of_isPoleNumber_two_of_perfectField [PerfectField k]
    (hF : IsFunctionField k F) (hex : IsIntegrallyClosedIn k F) (hg : 2 ≤ genus k F)
    {P : Place k F} (hP : P.degree = 1) (hpole : P.IsPoleNumber 2) :
    IsHyperellipticFunctionField k F :=
  isHyperellipticFunctionField_iff_two_le_genus_and_exists_finrank_adjoin_eq_two.mpr
    ⟨hg, exists_transcendental_finrank_adjoin_eq_two_of_degree_eq_two hF hex (by omega)
      (by simp [hP]) (two_le_dim_two_zsmul_ofPoint_of_isPoleNumber_two hF hex hpole)⟩

end TauCeti
