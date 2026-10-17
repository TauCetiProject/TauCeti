/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Fuchsian.Arithmetic
public import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
public import Mathlib.Data.ZMod.Units
import Mathlib.Data.Nat.Totient
import TauCeti.Data.ZMod.Divisibility
import TauCeti.Data.ZMod.Units

/-!
# The cusps of `Γ₁(N)`

Unless `N ∣ 4`, the number of cusps of `Γ₁(N)` is `ε∞ = ½ ∑_{d ∣ N} φ(d) φ(N / d)`, the cusp
count in the dimension formulas for `Γ₁(N)`. Cusps are counted as the cusp orbits of the
effective image of `Γ₁(N)` in `PSL(2, ℝ)`, the boundary orbits adjoined to its analytic quotient.

Every cusp is `γ • ∞` for some `γ ∈ SL(2, ℤ)`. For `γ` and `γ'` with bottom rows `(c, d)` and
`(c', d')`, the cusps `γ • ∞` and `γ' • ∞` are `Γ₁(N)`-equivalent exactly when
`(c', d') ≡ ±(c, d + j c) (mod N)` for some integer `j`. Without the sign, this congruence is
detected by the *label* of `γ`: the residue of `c` modulo `N`, together with the residue of `d`
modulo `gcd(c, N)`, which is a unit. Every pair of a residue `c` modulo `N` and a unit modulo
`gcd(c, N)` is a label, so there are `∑_{d ∣ N} φ(d) φ(N / d)` labels. The sign identifies the
labels of `γ` and `-γ`, which differ unless `N ∣ 4`, so each cusp has exactly two labels.

For `N ∣ 4` some cusps have a single label, and these levels are not treated here: `Γ₁(1)` and
`Γ₁(2)` contain `-1`, and `γ` and `-γ` have the same label for the irregular cusp `1/2` of
`Γ₁(4)`. For an odd prime `p`, the count is `p - 1`.

## Main definitions

* `TauCeti.gamma1CuspLabel`: the label `(c mod N, d mod gcd(c, N))` of `γ ∈ SL(2, ℤ)`.

## Main results

* `TauCeti.gamma1CuspLabel_eq_iff`: two matrices have the same label exactly when their bottom
  rows satisfy `(c', d') ≡ (c, d + j c) (mod N)` for some integer `j`.
* `TauCeti.gamma1CuspLabel_surjective`: every residue `c` modulo `N` and every unit modulo
  `gcd(c, N)` form a label.
* `TauCeti.cuspOrbitOfSL2Z_Gamma1_eq_iff_gamma1CuspLabel`: `γ • ∞` and `γ' • ∞` are
  `Γ₁(N)`-equivalent exactly when `γ'` has the label of `γ` or of `-γ`.
* `TauCeti.cuspOrbitOfSL2Z_Gamma1_eq_iff`: the same criterion as a congruence on bottom rows.
* `TauCeti.gamma1CuspLabel_neg_ne_self`: unless `N ∣ 4`, the labels of `-γ` and `γ` differ.
* `TauCeti.two_mul_card_cuspOrbit_Gamma1`: unless `N ∣ 4`, twice the number of cusps of `Γ₁(N)`
  is `∑_{d ∣ N} φ(d) φ(N / d)`.
* `TauCeti.card_cuspOrbit_Gamma1_of_prime`: `Γ₁(p)` has `p - 1` cusps for an odd prime `p`.

## References

* F. Diamond and J. Shurman, *A First Course in Modular Forms*, §§3.8–3.9. The criterion for
  equivalence of cusps is stated there for the first column `(a, c)` of `γ`; the bottom-row form
  used here is the one in which the labels of `Γ₀(N)` in
  `TauCeti.NumberTheory.ModularForms.CongruenceSubgroups.Cusp.Count` are stated.
-/

public section

open Matrix Matrix.SpecialLinearGroup CongruenceSubgroup ModularGroup
open scoped MatrixGroups

namespace TauCeti

variable {N : ℕ} [NeZero N]

/-! ### Labels of cusps -/

/-- The lower-right entry of `γ` is prime to `gcd(c, N)`, for `c` the lower-left entry. -/
private theorem isCoprime_gcd_val (γ : SL(2, ℤ)) :
    IsCoprime (γ 1 1) ((γ 1 0 : ZMod N).val.gcd N : ℤ) := by
  rw [ZMod.gcd_val_intCast]
  exact (bottom_row_coprime γ).symm.of_isCoprime_of_dvd_right (Int.gcd_dvd_left ..)

omit [NeZero N] in
/-- A unit of `ZMod (gcd(c, N))` given by an integer, compared with a unit of
`ZMod (gcd(c', N))` for `c = c'`: the moduli agree only propositionally, so the units are
compared as `HEq`. -/
private theorem heq_unitOfIsCoprime_iff {c c' : ZMod N} (hc : c = c') {d : ℤ}
    (hd : IsCoprime d (c.val.gcd N : ℤ)) (u : (ZMod (c'.val.gcd N))ˣ) :
    HEq (ZMod.unitOfIsCoprime d hd) u ↔ (d : ZMod (c'.val.gcd N)) = u := by
  subst hc
  rw [heq_iff_eq, Units.ext_iff, ZMod.coe_unitOfIsCoprime]

variable (N) in
/-- **The label of the cusp `γ • ∞` of `Γ₁(N)`.** For `γ ∈ SL(2, ℤ)` with bottom row `(c, d)`,
it is the residue of `c` modulo `N` together with the unit `d` modulo `gcd(c, N)`. Matrices
representing the same cusp have the same label up to replacing `γ` by `-γ`
(`cuspOrbitOfSL2Z_Gamma1_eq_iff_gamma1CuspLabel`). -/
noncomputable def gamma1CuspLabel (γ : SL(2, ℤ)) : Σ c : ZMod N, (ZMod (c.val.gcd N))ˣ :=
  ⟨γ 1 0, ZMod.unitOfIsCoprime (γ 1 1) (isCoprime_gcd_val γ)⟩

/-- The residue in the label of `γ` is the lower-left entry of `γ` modulo `N`. -/
@[simp]
theorem gamma1CuspLabel_fst (γ : SL(2, ℤ)) : (gamma1CuspLabel N γ).1 = γ 1 0 :=
  (rfl)

/-- The unit in the label of `γ` is the lower-right entry of `γ`. -/
@[simp]
theorem coe_gamma1CuspLabel_snd (γ : SL(2, ℤ)) :
    ((gamma1CuspLabel N γ).2 : ZMod ((gamma1CuspLabel N γ).1.val.gcd N)) = γ 1 1 :=
  (rfl)

/-- Two matrices have the same label exactly when their bottom rows `(c, d)` and `(c', d')`
satisfy `(c', d') ≡ (c, d + j c) (mod N)` for some integer `j`. -/
theorem gamma1CuspLabel_eq_iff (γ γ' : SL(2, ℤ)) :
    gamma1CuspLabel N γ = gamma1CuspLabel N γ' ↔
      ∃ j : ℤ, (γ' 1 0 : ZMod N) = γ 1 0 ∧ (γ' 1 1 : ZMod N) = γ 1 1 + j * γ 1 0 := by
  rw [gamma1CuspLabel, gamma1CuspLabel, Sigma.mk.inj_iff]
  constructor
  · rintro ⟨hc, hd⟩
    rw [heq_unitOfIsCoprime_iff hc, ZMod.coe_unitOfIsCoprime,
      ZMod.intCast_eq_intCast_iff_dvd_sub, ZMod.gcd_val_intCast,
      ZMod.gcd_dvd_iff_exists_intCast_eq_mul] at hd
    obtain ⟨j, hj⟩ := hd
    refine ⟨j, hc.symm, ?_⟩
    push_cast at hj
    linear_combination hj - j * hc
  · rintro ⟨j, hc, hd⟩
    refine ⟨hc.symm, (heq_unitOfIsCoprime_iff hc.symm _ _).mpr ?_⟩
    rw [ZMod.coe_unitOfIsCoprime, ZMod.intCast_eq_intCast_iff_dvd_sub, ZMod.gcd_val_intCast,
      ZMod.gcd_dvd_iff_exists_intCast_eq_mul]
    exact ⟨j, by push_cast; linear_combination hd - j * hc⟩

/-- Every residue `c` modulo `N` and every unit modulo `gcd(c, N)` form a label: that of a matrix
whose bottom row lifts `c` and a lift of the unit to a residue modulo `N`. -/
theorem gamma1CuspLabel_surjective : Function.Surjective (gamma1CuspLabel N) := by
  rintro ⟨c, u⟩
  obtain ⟨c₀, rfl⟩ := ZMod.intCast_surjective c
  have hg : (c₀ : ZMod N).val.gcd N ∣ N := Nat.gcd_dvd_right ..
  obtain ⟨d₁, hd₁⟩ := ZMod.intCast_surjective (u : ZMod ((c₀ : ZMod N).val.gcd N))
  obtain ⟨e, he⟩ := ZMod.intCast_surjective ((u⁻¹ : (ZMod _)ˣ) : ZMod ((c₀ : ZMod N).val.gcd N))
  -- `d₁` is invertible modulo `gcd(c₀, N)`, so `c₀` and `d₁` are coprime modulo `N`.
  have hde : (Int.gcd c₀ N : ℤ) ∣ d₁ * e - 1 := by
    rw [← ZMod.gcd_val_intCast, ← ZMod.intCast_eq_intCast_iff_dvd_sub]
    push_cast
    rw [hd₁, he, Units.mul_inv]
  obtain ⟨j, hj⟩ := (ZMod.gcd_dvd_iff_exists_intCast_eq_mul c₀ _).mp hde
  have hcop : IsCoprime (c₀ : ZMod N) (d₁ : ZMod N) :=
    ⟨-j, e, by push_cast at hj; linear_combination hj⟩
  obtain ⟨c₂, d₂, hc₂, hd₂, h₂⟩ := hcop.exists_int_lifts
  obtain ⟨γ, -, hγ⟩ := bottom_row_surj
    (show ![c₂, d₂] ∈ {cd : Fin 2 → ℤ | IsCoprime (cd 0) (cd 1)} from h₂)
  have hc₃ : γ 1 0 = c₂ := congrFun hγ 0
  have hd₃ : γ 1 1 = d₂ := congrFun hγ 1
  have hc : (γ 1 0 : ZMod N) = c₀ := by rw [hc₃, hc₂]
  refine ⟨γ, ?_⟩
  rw [gamma1CuspLabel]
  refine Sigma.ext hc ((heq_unitOfIsCoprime_iff hc (isCoprime_gcd_val γ) u).mpr ?_)
  rw [← hd₁, ZMod.intCast_eq_intCast_iff_dvd_sub, hd₃]
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at hd₂
  exact (Int.natCast_dvd_natCast.mpr hg).trans hd₂

/-! ### Equivalence of cusps -/

/-- Matrices with the same label represent the same cusp of `Γ₁(N)`. -/
private theorem cuspOrbitOfSL2Z_Gamma1_eq_of_gamma1CuspLabel_eq {γ γ' : SL(2, ℤ)}
    (h : gamma1CuspLabel N γ = gamma1CuspLabel N γ') :
    (Gamma1 N).cuspOrbitOfSL2Z γ = (Gamma1 N).cuspOrbitOfSL2Z γ' := by
  obtain ⟨j, hc, hd⟩ := (gamma1CuspLabel_eq_iff γ γ').mp h
  have hdet := γ.det_coe
  have hdet' := γ'.det_coe
  rw [det_fin_two] at hdet hdet'
  have hdet₁ := congrArg (Int.cast : ℤ → ZMod N) hdet
  have hdet₁' := congrArg (Int.cast : ℤ → ZMod N) hdet'
  push_cast at hdet₁ hdet₁'
  rw [Subgroup.cuspOrbitOfSL2Z_eq_iff]
  refine ⟨γ * T ^ j * γ'⁻¹, ?_, ?_⟩
  · rw [Gamma1_mem]
    simp only [coe_mul, coe_inv, adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two, of_apply,
      cons_val', cons_val_zero, cons_val_one, empty_val', cons_val_fin_one, coe_T_zpow]
    push_cast
    refine ⟨?_, ?_, ?_⟩
    · linear_combination γ 0 0 * hd - (γ 0 0 * j + γ 0 1) * hc + hdet₁
    · linear_combination γ' 0 1 * hc - γ' 0 0 * hd + hdet₁'
    · linear_combination γ 1 0 * hd - (γ 1 0 * j + γ 1 1) * hc
  · have hT : γ⁻¹ * (γ * T ^ j * γ'⁻¹) * γ' = T ^ j := by group
    rw [hT, coe_T_zpow]
    rfl

/-- **The criterion for equivalence of cusps of `Γ₁(N)`, through labels.** The cusps `γ • ∞` and
`γ' • ∞` are `Γ₁(N)`-equivalent exactly when `γ'` has the label of `γ` or of `-γ`. -/
theorem cuspOrbitOfSL2Z_Gamma1_eq_iff_gamma1CuspLabel (γ γ' : SL(2, ℤ)) :
    (Gamma1 N).cuspOrbitOfSL2Z γ = (Gamma1 N).cuspOrbitOfSL2Z γ' ↔
      gamma1CuspLabel N γ = gamma1CuspLabel N γ' ∨
        gamma1CuspLabel N (-γ) = gamma1CuspLabel N γ' := by
  constructor
  · rw [Subgroup.cuspOrbitOfSL2Z_eq_iff]
    rintro ⟨h, hh, hM⟩
    obtain ⟨M, hMdef⟩ : ∃ M, γ⁻¹ * h * γ' = M := ⟨_, rfl⟩
    have hg : h * γ' = γ * M := by rw [← hMdef]; group
    rw [hMdef] at hM
    have hdet := M.det_coe
    rw [det_fin_two, hM, mul_zero, sub_zero] at hdet
    obtain ⟨-, h11, h10⟩ := (Gamma1_mem N h).mp hh
    have e10 := congrArg (fun A : SL(2, ℤ) ↦ ((A 1 0 : ℤ) : ZMod N)) hg
    have e11 := congrArg (fun A : SL(2, ℤ) ↦ ((A 1 1 : ℤ) : ZMod N)) hg
    simp only [coe_mul, Matrix.mul_apply, Fin.sum_univ_two, hM] at e10 e11
    push_cast [h10, h11] at e10 e11
    rcases Int.eq_one_or_neg_one_of_mul_eq_one' hdet with ⟨h0, h1⟩ | ⟨h0, h1⟩
    · rw [h0] at e10
      rw [h1] at e11
      push_cast at e10 e11
      refine .inl ((gamma1CuspLabel_eq_iff _ _).mpr ⟨M 0 1, ?_, ?_⟩)
      · linear_combination e10
      · linear_combination e11
    · rw [h0] at e10
      rw [h1] at e11
      push_cast at e10 e11
      refine .inr ((gamma1CuspLabel_eq_iff _ _).mpr ⟨-M 0 1, ?_, ?_⟩)
      · simp only [coe_neg, Matrix.neg_apply, Int.cast_neg]
        linear_combination e10
      · simp only [coe_neg, Matrix.neg_apply, Int.cast_neg]
        linear_combination e11
  · rintro (h | h)
    · exact cuspOrbitOfSL2Z_Gamma1_eq_of_gamma1CuspLabel_eq h
    · rw [← Subgroup.cuspOrbitOfSL2Z_neg _ γ]
      exact cuspOrbitOfSL2Z_Gamma1_eq_of_gamma1CuspLabel_eq h

/-- **The criterion for equivalence of cusps of `Γ₁(N)`.** For `γ` and `γ'` with bottom rows
`(c, d)` and `(c', d')`, the cusps `γ • ∞` and `γ' • ∞` are `Γ₁(N)`-equivalent exactly when
`(c', d') ≡ ±(c, d + j c) (mod N)` for some integer `j`. -/
theorem cuspOrbitOfSL2Z_Gamma1_eq_iff (γ γ' : SL(2, ℤ)) :
    (Gamma1 N).cuspOrbitOfSL2Z γ = (Gamma1 N).cuspOrbitOfSL2Z γ' ↔
      ∃ j : ℤ, ((γ' 1 0 : ZMod N) = γ 1 0 ∧ (γ' 1 1 : ZMod N) = γ 1 1 + j * γ 1 0) ∨
        ((γ' 1 0 : ZMod N) = -γ 1 0 ∧ (γ' 1 1 : ZMod N) = -(γ 1 1 + j * γ 1 0)) := by
  rw [cuspOrbitOfSL2Z_Gamma1_eq_iff_gamma1CuspLabel, gamma1CuspLabel_eq_iff,
    gamma1CuspLabel_eq_iff, ← exists_or]
  simp only [coe_neg, Matrix.neg_apply, Int.cast_neg, mul_neg, neg_add]

/-- Unless `N ∣ 4`, the labels of `-γ` and `γ` differ: the cusp `γ • ∞` of `Γ₁(N)` has exactly the
two labels of `γ` and `-γ`. -/
theorem gamma1CuspLabel_neg_ne_self (hN : ¬N ∣ 4) (γ : SL(2, ℤ)) :
    gamma1CuspLabel N (-γ) ≠ gamma1CuspLabel N γ := by
  intro h
  obtain ⟨j, hc, hd⟩ := (gamma1CuspLabel_eq_iff _ _).mp h
  simp only [coe_neg, neg_apply, Int.cast_neg] at hc hd
  obtain ⟨x, y, hxy⟩ := bottom_row_coprime γ
  have hxy₁ := congrArg (Int.cast : ℤ → ZMod N) hxy
  push_cast at hxy₁
  refine hN ((ZMod.natCast_eq_zero_iff 4 N).mp ?_)
  push_cast
  linear_combination -4 * hxy₁ + (2 * x - j * y) * hc + 2 * y * hd

/-! ### The number of cusps -/

/-- There are `∑_{d ∣ N} φ(d) φ(N / d)` labels: the residues `c` modulo `N` with
`gcd(c, N) = d` are `φ(N / d)` in number, and each carries `φ(d)` units modulo `d`. -/
private theorem card_gamma1CuspLabel :
    Nat.card (Σ c : ZMod N, (ZMod (c.val.gcd N))ˣ) =
      ∑ d ∈ N.divisors, Nat.totient d * Nat.totient (N / d) := by
  have (c : ZMod N) : NeZero (c.val.gcd N) := ⟨Nat.gcd_ne_zero_right (NeZero.ne N)⟩
  rw [Nat.card_sigma]
  simp_rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
  rw [Finset.sum_nbij' ZMod.val (fun k ↦ (k : ZMod N)) (g := fun k ↦ Nat.totient (k.gcd N))
      (by simp [ZMod.val_lt]) (by simp) (by simp)
      (fun k hk ↦ ZMod.val_cast_of_lt (Finset.mem_range.mp hk)) (by simp),
    ← Finset.sum_fiberwise_of_maps_to (g := fun k ↦ N.gcd k) (t := N.divisors)
      (fun k _ ↦ Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_left N k, NeZero.ne N⟩)]
  refine Finset.sum_congr rfl fun d hd ↦ ?_
  rw [Nat.totient_div_of_dvd (Nat.dvd_of_mem_divisors hd), Finset.card_eq_sum_ones,
    Finset.mul_sum, mul_comm]
  refine Finset.sum_congr rfl fun k hk ↦ ?_
  rw [Nat.gcd_comm, (Finset.mem_filter.mp hk).2, one_mul]

/-- **The cusp count `ε∞` of `Γ₁(N)`.** Unless `N ∣ 4`, twice the number of cusps of `Γ₁(N)` is
`∑_{d ∣ N} φ(d) φ(N / d)`. -/
theorem two_mul_card_cuspOrbit_Gamma1 (hN : ¬N ∣ 4) :
    2 * Nat.card ((Gamma1 N).map sl2zToPSL2R).CuspOrbit =
      ∑ d ∈ N.divisors, Nat.totient d * Nat.totient (N / d) := by
  have hs := (Gamma1 N).cuspOrbitOfSL2Z_surjective
  -- Each cusp, with a chosen representative `γ`, has the two labels of `γ` and of `-γ`.
  let f (x : ((Gamma1 N).map sl2zToPSL2R).CuspOrbit × Bool) :
      Σ c : ZMod N, (ZMod (c.val.gcd N))ˣ :=
    gamma1CuspLabel N (if x.2 then -Function.surjInv hs x.1 else Function.surjInv hs x.1)
  have hf : Function.Bijective f := by
    refine ⟨?_, fun x ↦ ?_⟩
    · rintro ⟨C, b⟩ ⟨C', b'⟩ h
      have hC := cuspOrbitOfSL2Z_Gamma1_eq_of_gamma1CuspLabel_eq h
      simp only [apply_ite, Subgroup.cuspOrbitOfSL2Z_neg, ite_self, Function.surjInv_eq hs] at hC
      subst hC
      cases b <;> cases b' <;> simp only [f, ite_true, Bool.false_eq_true, ite_false] at h ⊢
      · exact (gamma1CuspLabel_neg_ne_self hN _ h.symm).elim
      · exact (gamma1CuspLabel_neg_ne_self hN _ h).elim
    · obtain ⟨γ, rfl⟩ := gamma1CuspLabel_surjective x
      rcases (cuspOrbitOfSL2Z_Gamma1_eq_iff_gamma1CuspLabel _ γ).mp
        (Function.surjInv_eq hs ((Gamma1 N).cuspOrbitOfSL2Z γ)) with h | h
      · exact ⟨((Gamma1 N).cuspOrbitOfSL2Z γ, false), h⟩
      · exact ⟨((Gamma1 N).cuspOrbitOfSL2Z γ, true), h⟩
  rw [← card_gamma1CuspLabel, ← Nat.card_congr (Equiv.ofBijective f hf), Nat.card_prod,
    Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool, mul_comm]

/-- `Γ₁(p)` has `p - 1` cusps for an odd prime `p`. -/
theorem card_cuspOrbit_Gamma1_of_prime {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) :
    Nat.card ((Gamma1 p).map sl2zToPSL2R).CuspOrbit = p - 1 := by
  have hp' := (Fact.out : p.Prime)
  have h4 : ¬p ∣ 4 := fun h ↦ hp <| (Nat.prime_dvd_prime_iff_eq hp' Nat.prime_two).mp <|
    hp'.dvd_of_dvd_pow (show p ∣ 2 ^ 2 from h)
  have h := two_mul_card_cuspOrbit_Gamma1 h4
  rw [hp'.divisors, Finset.sum_pair hp'.one_lt.ne, Nat.div_self hp'.pos, Nat.div_one,
    Nat.totient_one, Nat.totient_prime hp'] at h
  omega

end TauCeti
