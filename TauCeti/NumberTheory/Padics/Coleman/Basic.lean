/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.PowerSeries.Expand
public import Mathlib.RingTheory.PowerSeries.Substitution

import Mathlib.Data.Nat.Choose.Dvd
import TauCeti.RingTheory.PowerSeries.Cartier
import TauCeti.RingTheory.PowerSeries.Substitution

/-!
# Coleman's Frobenius substitution and power-series basis

Let `p` be a prime and `O` a `(p)`-adically complete commutative ring. The Frobenius substitution
`Φ : O⟦X⟧ →ₐ[O] O⟦X⟧` sending `f(X)` to `f((1 + X) ^ p - 1)` reduces modulo `p` to
`PowerSeries.expand p`. Combining the Cartier decomposition
(`TauCeti.RingTheory.PowerSeries.Cartier`) with the unitriangular change of basis from `{X ^ i}`
to `{(1 + X) ^ i}` gives a basis for `expand p` over any commutative ring `O`; inverting the
`(p)`-adically contractive perturbation `Φ - expand p` by a Neumann series shows that every
`f ∈ O⟦X⟧` expands uniquely as `f = ∑ i < p, Φ(cᵢ) * (1 + X) ^ i`, with no domain, regularity, or
compactness assumption on `O`.

## Main definitions

* `TauCeti.Coleman.frobeniusHom`: the `O`-algebra endomorphism `f ↦ f((1 + X) ^ p - 1)`.
* `TauCeti.Coleman.coordEquiv`, `TauCeti.Coleman.coord`: the `O`-linear equivalence sending
  `f ∈ O⟦X⟧` to its Coleman coordinates `cᵢ(f)` in `f = ∑ i < p, Φ(cᵢ(f)) * (1 + X) ^ i`.

## Main results

* `TauCeti.Coleman.frobeniusHom_eq_expand`: when `(p : O) = 0`, `Φ` coincides with `expand p`.
* `TauCeti.Coleman.sum_frobeniusHom_coord`, `TauCeti.Coleman.coord_unique`: unique expansion
  `f = ∑ i < p, Φ(cᵢ) * (1 + X) ^ i`.
* `TauCeti.Coleman.coord_one_add_X_pow`, `TauCeti.Coleman.map_coord`: coordinates of `(1 + X) ^ n`
  and functoriality along coefficient ring homomorphisms.
* `TauCeti.Coleman.coeff_coord_mem_pow_of_coeff_mem_pow`: explicit `(p)`-adic modulus of
  continuity for the Coleman coordinates.

## References

* R. F. Coleman, *Division Values in Local Fields*, Invent. Math. 53 (1979), §II.
* J. Coates and R. Sujatha, *Cyclotomic Fields and Zeta Values*, Springer (2006), §3.3.
* J. Rodrigues Jacinto and C. Williams, *An introduction to p-adic L-functions* (2025), §3.5.
-/

public noncomputable section

open PowerSeries

namespace TauCeti.Coleman

section Frobenius

variable (p : ℕ) (O : Type*) [CommRing O]

/-- The series `(1 + X) ^ p - 1` has zero constant coefficient and can therefore be substituted
into any power series over `O`. -/
theorem hasSubst_one_add_X_pow_sub_one : HasSubst ((1 + X : O⟦X⟧) ^ p - 1) :=
  HasSubst.of_constantCoeff_zero' (by simp)

/-- The Frobenius substitution `Φ : O⟦X⟧ →ₐ[O] O⟦X⟧` sending `f(X)` to `f((1 + X) ^ p - 1)`. -/
def frobeniusHom : O⟦X⟧ →ₐ[O] O⟦X⟧ :=
  substAlgHom (hasSubst_one_add_X_pow_sub_one p O)

variable {p O}

/-- Applying `frobeniusHom` substitutes `(1 + X) ^ p - 1`. -/
theorem frobeniusHom_apply (f : O⟦X⟧) :
    frobeniusHom p O f = f.subst ((1 + X : O⟦X⟧) ^ p - 1) :=
  congrFun (coe_substAlgHom (hasSubst_one_add_X_pow_sub_one p O)) f

/-- `frobeniusHom` sends `X` to `(1 + X) ^ p - 1`. -/
@[simp]
theorem frobeniusHom_X : frobeniusHom p O X = (1 + X : O⟦X⟧) ^ p - 1 := by
  rw [frobeniusHom_apply, subst_X (hasSubst_one_add_X_pow_sub_one p O)]

/-- `frobeniusHom` fixes constant power series. -/
@[simp]
theorem frobeniusHom_C (c : O) : frobeniusHom p O (C c) = C c :=
  (frobeniusHom p O).commutes c

/-- `frobeniusHom` raises `1 + X` to the `p`-th power. -/
@[simp]
theorem frobeniusHom_one_add_X : frobeniusHom p O (1 + X) = (1 + X : O⟦X⟧) ^ p := by
  simp [map_add]

/-- `frobeniusHom` sends `(1 + X) ^ n` to `(1 + X) ^ (p * n)`. -/
@[simp]
theorem frobeniusHom_one_add_X_pow (n : ℕ) :
    frobeniusHom p O ((1 + X) ^ n) = (1 + X : O⟦X⟧) ^ (p * n) := by
  rw [map_pow, frobeniusHom_one_add_X, ← pow_mul]

/-- Coefficientwise change of base ring commutes with `frobeniusHom`. -/
theorem map_frobeniusHom {O' : Type*} [CommRing O'] (φ : O →+* O') (f : O⟦X⟧) :
    PowerSeries.map φ (frobeniusHom p O f) = frobeniusHom p O' (PowerSeries.map φ f) := by
  rw [frobeniusHom_apply, frobeniusHom_apply]
  have h := PowerSeries.map_subst (hasSubst_one_add_X_pow_sub_one p O) (h := φ) f
  have hX : MvPowerSeries.map φ (X : O⟦X⟧) = (X : O'⟦X⟧) := PowerSeries.map_X φ
  simpa only [PowerSeries.map, map_sub, map_pow, map_add, map_one, hX] using h

private theorem C_p_dvd_one_add_X_pow_sub_one_sub_X_pow [Fact p.Prime] :
    C (p : O) ∣ ((1 + X : O⟦X⟧) ^ p - 1) - X ^ p := by
  have hp_eq : p = (p - 1) + 1 := (Nat.sub_add_cancel (Fact.out : p.Prime).pos).symm
  have hpow : (1 + X : O⟦X⟧) ^ p - 1 - X ^ p =
      ∑ m ∈ Finset.range (p - 1), X ^ (m + 1) * (p.choose (m + 1) : O⟦X⟧) := by
    rw [add_comm 1 X, add_pow]
    conv_lhs => rw [Finset.sum_range_succ, hp_eq, Finset.sum_range_succ']
    simp only [one_pow, mul_one, pow_zero, Nat.choose_zero_right, Nat.cast_one, Nat.choose_self,
      ← hp_eq]
    ring
  rw [hpow]
  refine Finset.dvd_sum fun m hm ↦ ?_
  obtain ⟨q, hq⟩ := (Fact.out : p.Prime).dvd_choose_self (Nat.succ_ne_zero m)
    (by have := Finset.mem_range.mp hm; omega)
  exact ⟨X ^ (m + 1) * (q : O⟦X⟧), by rw [hq, Nat.cast_mul, map_natCast]; ring⟩

/-- When `(p : O) = 0`, `frobeniusHom` coincides with `PowerSeries.expand p`. -/
theorem frobeniusHom_eq_expand [Fact p.Prime] (hp : (p : O) = 0) (f : O⟦X⟧) :
    frobeniusHom p O f = expand p (Fact.out : p.Prime).ne_zero f := by
  obtain ⟨q, hq⟩ := C_p_dvd_one_add_X_pow_sub_one_sub_X_pow (p := p) (O := O)
  rw [hp, map_zero, zero_mul, sub_eq_zero] at hq
  rw [frobeniusHom_apply, expand_apply, hq]

end Frobenius

section BasisConstruction

variable {p : ℕ} [Fact p.Prime] {O : Type*} [CommRing O]

private def expandOneAddXLinearMap (p : ℕ) [Fact p.Prime] (O : Type*) [CommRing O] :
    (Fin p → O⟦X⟧) →ₗ[O] O⟦X⟧ where
  toFun a := ∑ i : Fin p, expand p (Fact.out : p.Prime).ne_zero (a i) * (1 + X) ^ (i : ℕ)
  map_add' _ _ := by simp only [Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]
  map_smul' _ _ := by
    simp only [Pi.smul_apply, map_smul, smul_mul_assoc, Finset.smul_sum, RingHom.id_apply]

private def expandOneAddXInv (p : ℕ) (O : Type*) [CommRing O] : O⟦X⟧ →ₗ[O] (Fin p → O⟦X⟧) where
  toFun f j := ∑ k : Fin p,
    if (j : ℕ) ≤ k then ((-1 : O) ^ ((k : ℕ) - j) * ((k : ℕ).choose j : O)) • cartier O p k f
    else 0
  map_add' f g := funext fun j ↦ by
    simp only [map_add, Pi.add_apply, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ ↦ by split_ifs <;> simp
  map_smul' c f := funext fun j ↦ by
    simp only [map_smul, Pi.smul_apply, RingHom.id_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    split_ifs
    · rw [smul_comm]
    · rw [smul_zero]

omit [Fact p.Prime] in
private theorem sum_neg_one_pow_choose_mul_one_add_X_pow (k : Fin p) :
    (∑ j : Fin p, if (j : ℕ) ≤ k then
        C ((-1 : O) ^ ((k : ℕ) - j) * ((k : ℕ).choose j : O)) * (1 + X) ^ (j : ℕ)
      else 0) = X ^ (k : ℕ) := by
  have hfilt : (Finset.range p).filter (· ≤ (k : ℕ)) = Finset.range ((k : ℕ) + 1) := by
    ext j; simp only [Finset.mem_filter, Finset.mem_range]; omega
  calc (∑ j : Fin p, if (j : ℕ) ≤ k then
          C ((-1 : O) ^ ((k : ℕ) - j) * ((k : ℕ).choose j : O)) * (1 + X) ^ (j : ℕ) else 0)
      = ∑ j ∈ Finset.range ((k : ℕ) + 1),
          (1 + X : O⟦X⟧) ^ j * (-1 : O⟦X⟧) ^ ((k : ℕ) - j) * ((k : ℕ).choose j : O⟦X⟧) := by
        rw [Fin.sum_univ_eq_sum_range (fun j ↦ if j ≤ (k : ℕ) then
          C ((-1 : O) ^ ((k : ℕ) - j) * ((k : ℕ).choose j : O)) * (1 + X) ^ j else 0),
          ← Finset.sum_filter, hfilt]
        exact Finset.sum_congr rfl fun j _ ↦ by
          simp only [map_mul, map_pow, map_neg, map_one, map_natCast]; ring
    _ = ((1 + X : O⟦X⟧) + (-1 : O⟦X⟧)) ^ (k : ℕ) := (add_pow _ _ _).symm
    _ = X ^ (k : ℕ) := by simp

private theorem expandOneAddX_rightInverse (f : O⟦X⟧) :
    expandOneAddXLinearMap p O (expandOneAddXInv p O f) = f := by
  have hp : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  simp only [expandOneAddXLinearMap, expandOneAddXInv, LinearMap.coe_mk, AddHom.coe_mk]
  calc ∑ j : Fin p, expand p hp (∑ k : Fin p, if (j : ℕ) ≤ k then
          ((-1 : O) ^ ((k : ℕ) - j) * ((k : ℕ).choose j : O)) • cartier O p k f else 0) *
          (1 + X) ^ (j : ℕ)
      = ∑ k : Fin p, expand p hp (cartier O p k f) * (∑ j : Fin p, if (j : ℕ) ≤ k then
          C ((-1 : O) ^ ((k : ℕ) - j) * ((k : ℕ).choose j : O)) * (1 + X) ^ (j : ℕ) else 0) := by
        simp_rw [map_sum, Finset.sum_mul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun k _ ↦ ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ ↦ by
          split_ifs
          · rw [map_smul, PowerSeries.smul_eq_C_mul]; ring
          · simp
    _ = f := by
        simp_rw [sum_neg_one_pow_choose_mul_one_add_X_pow, mul_comm (expand p hp _)]
        rw [Fin.sum_univ_eq_sum_range (fun k ↦ X ^ k * expand p hp (cartier O p k f))]
        exact (sum_X_pow_mul_expand_cartier p hp f).symm

omit [Fact p.Prime] in
private theorem cartier_one_add_X_pow (k j : Fin p) :
    cartier O p k ((1 + X : O⟦X⟧) ^ (j : ℕ)) =
      if (k : ℕ) ≤ j then C (((j : ℕ).choose k : O)) else 0 := by
  rw [add_comm 1 X, add_pow]
  simp only [one_pow, mul_one, map_sum]
  have hterm (m : ℕ) (hm : m ∈ Finset.range ((j : ℕ) + 1)) :
      cartier O p k (X ^ m * ((j : ℕ).choose m : O⟦X⟧)) =
        if m = (k : ℕ) then C (((j : ℕ).choose m : O)) else 0 := by
    have hm_lt : m < p := lt_of_lt_of_le (Finset.mem_range.mp hm) j.isLt
    have hmon : X ^ m * ((j : ℕ).choose m : O⟦X⟧) = monomial m (((j : ℕ).choose m : O)) := by
      rw [monomial_eq_C_mul_X_pow, map_natCast, mul_comm]
    rw [hmon, cartier_monomial p k m k.isLt, Nat.mod_eq_of_lt hm_lt, Nat.div_eq_of_lt hm_lt]
    split_ifs <;> simp [monomial_zero_eq_C_apply]
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq']
  simp only [Finset.mem_range, Nat.lt_succ_iff]

private theorem expandOneAddX_injective : Function.Injective (expandOneAddXLinearMap p O) := by
  have hp : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  rw [injective_iff_map_eq_zero]
  intro a ha
  have hsys (k : Fin p) :
      (∑ j : Fin p, if (k : ℕ) ≤ j then C (((j : ℕ).choose k : O)) * a j else 0) = 0 := by
    have hc := congrArg (cartier O p k) ha
    simp only [expandOneAddXLinearMap, LinearMap.coe_mk, AddHom.coe_mk, map_sum, map_zero] at hc
    conv_rhs => rw [← hc]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [cartier_expand_mul p k hp k.isLt, cartier_one_add_X_pow]
    split_ifs <;> simp [mul_comm]
  suffices ∀ d : ℕ, ∀ k : Fin p, p - 1 - (k : ℕ) = d → a k = 0 from
    funext fun k ↦ this (p - 1 - (k : ℕ)) k rfl
  intro d
  induction d using Nat.strongRecOn with
  | ind d ih =>
    intro k hk
    have hsplit := hsys k
    rw [Finset.sum_eq_single k] at hsplit
    · simpa using hsplit
    · intro j _ hjk
      split_ifs with hle
      · have hlt : (k : ℕ) < j := lt_of_le_of_ne hle (fun h ↦ hjk (Fin.ext h.symm))
        rw [ih _ (by omega) j rfl, mul_zero]
      · rfl
    · simp

private def expandOneAddXEquiv (p : ℕ) [Fact p.Prime] (O : Type*) [CommRing O] :
    (Fin p → O⟦X⟧) ≃ₗ[O] O⟦X⟧ :=
  LinearEquiv.ofLinearMap (expandOneAddXLinearMap p O) (expandOneAddXInv p O)
    (LinearMap.ext expandOneAddX_rightInverse)
    (LinearMap.ext fun _ ↦ expandOneAddX_injective (expandOneAddX_rightInverse _))

private theorem expandOneAddXEquiv_apply (a : Fin p → O⟦X⟧) :
    expandOneAddXEquiv p O a = expandOneAddXLinearMap p O a := rfl

private theorem expandOneAddXEquiv_symm_apply (f : O⟦X⟧) :
    (expandOneAddXEquiv p O).symm f = expandOneAddXInv p O f := rfl

private theorem coeff_frobeniusHom_sub_expand_mem (J : Ideal O) {g : O⟦X⟧} {n : ℕ}
    (hg : ∀ m ≤ n, coeff m g ∈ J) :
    coeff n (frobeniusHom p O g - expand p (Fact.out : p.Prime).ne_zero g) ∈
      Ideal.span {(p : O)} * J := by
  have hp : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  have h1 : constantCoeff ((1 + X : O⟦X⟧) ^ p - 1) = 0 := by simp
  have h2 : constantCoeff (X ^ p : O⟦X⟧) = 0 := by rw [map_pow, constantCoeff_X, zero_pow hp]
  rw [map_sub, frobeniusHom_apply, expand_apply, coeff_subst_eq_sum_range g h1,
    coeff_subst_eq_sum_range g h2, ← Finset.sum_sub_distrib]
  refine Ideal.sum_mem _ fun k hk ↦ ?_
  rw [Finset.mem_range, Nat.lt_succ_iff] at hk
  rw [smul_eq_mul, smul_eq_mul, ← mul_sub, ← map_sub]
  refine Ideal.mul_mem_mul_rev ?_ (hg k hk)
  obtain ⟨r, hr⟩ :=
    (C_p_dvd_one_add_X_pow_sub_one_sub_X_pow (p := p) (O := O)).trans (sub_dvd_pow_sub_pow _ _ k)
  rw [hr, coeff_C_mul]
  exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)

private def assemblyDiff (p : ℕ) [Fact p.Prime] (O : Type*) [CommRing O] :
    (Fin p → O⟦X⟧) →ₗ[O] O⟦X⟧ where
  toFun a := ∑ i : Fin p,
    (frobeniusHom p O (a i) - expand p (Fact.out : p.Prime).ne_zero (a i)) * (1 + X) ^ (i : ℕ)
  map_add' _ _ := by
    simp only [Pi.add_apply, map_add, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun _ _ ↦ by ring
  map_smul' _ _ := by
    simp only [Pi.smul_apply, map_smul, Finset.smul_sum, RingHom.id_apply]
    exact Finset.sum_congr rfl fun _ _ ↦ by rw [← smul_sub, smul_mul_assoc]

private def neumannStep (p : ℕ) [Fact p.Prime] (O : Type*) [CommRing O] :
    Module.End O (Fin p → O⟦X⟧) :=
  (expandOneAddXEquiv p O).symm.toLinearMap.comp (assemblyDiff p O)

private theorem coeff_expandOneAddXEquiv_symm_mem (J : Ideal O) {f : O⟦X⟧} {n : ℕ}
    (hf : ∀ s < p * (n + 1), coeff s f ∈ J) (j : Fin p) :
    coeff n ((expandOneAddXEquiv p O).symm f j) ∈ J := by
  rw [expandOneAddXEquiv_symm_apply]
  simp only [expandOneAddXInv, LinearMap.coe_mk, AddHom.coe_mk, map_sum]
  refine Ideal.sum_mem _ fun k _ ↦ ?_
  split_ifs
  · rw [map_smul, coeff_cartier]
    exact J.smul_mem _ (hf _ (by have := k.isLt; nlinarith))
  · simp

private theorem coeff_neumannStep_mem (J : Ideal O) {a : Fin p → O⟦X⟧} {n : ℕ}
    (ha : ∀ i : Fin p, ∀ m < p * (n + 1), coeff m (a i) ∈ J) (j : Fin p) :
    coeff n (neumannStep p O a j) ∈ Ideal.span {(p : O)} * J := by
  rw [neumannStep, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap]
  refine coeff_expandOneAddXEquiv_symm_mem (Ideal.span {(p : O)} * J) (fun s hs ↦ ?_) j
  simp only [assemblyDiff, LinearMap.coe_mk, AddHom.coe_mk, map_sum]
  refine Ideal.sum_mem _ fun i _ ↦ ?_
  rw [coeff_mul]
  refine Ideal.sum_mem _ fun xy hxy ↦ ?_
  rw [Finset.mem_antidiagonal] at hxy
  exact Ideal.mul_mem_right _ _ (coeff_frobeniusHom_sub_expand_mem J fun m hm ↦ ha i m (by omega))

private theorem coeff_neumannStep_pow_mem (a : Fin p → O⟦X⟧) (m : ℕ) (i : Fin p) (n : ℕ) :
    coeff n ((neumannStep p O ^ m) a i) ∈ Ideal.span {(p : O)} ^ m := by
  induction m generalizing n i with
  | zero => simp
  | succ m ih =>
    rw [pow_succ' (neumannStep p O), mul_apply_eq_comp, pow_succ']
    exact coeff_neumannStep_mem (Ideal.span {(p : O)} ^ m) (fun j r _ ↦ ih j r) i

private def assembly (p : ℕ) (O : Type*) [CommRing O] : (Fin p → O⟦X⟧) →ₗ[O] O⟦X⟧ where
  toFun a := ∑ i : Fin p, frobeniusHom p O (a i) * (1 + X) ^ (i : ℕ)
  map_add' _ _ := by simp only [Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]
  map_smul' _ _ := by
    simp only [Pi.smul_apply, map_smul, smul_mul_assoc, Finset.smul_sum, RingHom.id_apply]

private theorem assembly_eq_expandOneAddXEquiv_add_neumannStep (a : Fin p → O⟦X⟧) :
    assembly p O a = expandOneAddXEquiv p O (a + neumannStep p O a) := by
  rw [map_add, neumannStep, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
    (expandOneAddXEquiv p O).apply_symm_apply, expandOneAddXEquiv_apply]
  simp only [assembly, expandOneAddXLinearMap, assemblyDiff, LinearMap.coe_mk, AddHom.coe_mk,
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun _ _ ↦ by ring

private theorem id_add_neumannStep_injective [IsAdicComplete (Ideal.span {(p : O)}) O] :
    Function.Injective ((LinearMap.id : Module.End O (Fin p → O⟦X⟧)) + neumannStep p O) := by
  set I : Ideal O := Ideal.span {(p : O)}
  set T : Module.End O (Fin p → O⟦X⟧) := neumannStep p O
  rw [injective_iff_map_eq_zero]
  intro a ha
  have hTa : T a = -a := eq_neg_of_add_eq_zero_right ha
  have hpow (m : ℕ) : (T ^ m) a = (-1 : O) ^ m • a := by
    induction m with
    | zero => simp
    | succ m ih =>
      rw [pow_succ', mul_apply_eq_comp, ih, map_smul, hTa, pow_succ', neg_one_mul, smul_neg,
        neg_smul]
  funext i; ext n
  refine IsHausdorff.haus (I := I) inferInstance (coeff n (a i)) fun m ↦ ?_
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]
  have hmem : coeff n ((T ^ m) a i) ∈ I ^ m := coeff_neumannStep_pow_mem a m i n
  rw [hpow m, Pi.smul_apply, map_smul, smul_eq_mul] at hmem
  have hmul := Ideal.mul_mem_left (I ^ m) ((-1 : O) ^ m) hmem
  rwa [← mul_assoc, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_mul] at hmul

private def neumannPartialSum (b : Fin p → O⟦X⟧) (N : ℕ) : Fin p → O⟦X⟧ :=
  ∑ m ∈ Finset.range N, (-1 : O) ^ m • (neumannStep p O ^ m) b

private theorem neumannPartialSum_telescoping (b : Fin p → O⟦X⟧) (M : ℕ) :
    neumannPartialSum b M + neumannStep p O (neumannPartialSum b M) =
      b - (-1 : O) ^ M • (neumannStep p O ^ M) b := by
  induction M with
  | zero => simp [neumannPartialSum]
  | succ M ih =>
    have hsucc : neumannPartialSum b (M + 1) =
        neumannPartialSum b M + (-1 : O) ^ M • (neumannStep p O ^ M) b :=
      Finset.sum_range_succ _ M
    have hstep : neumannStep p O ((neumannStep p O ^ M) b) = (neumannStep p O ^ (M + 1)) b := by
      rw [pow_succ', mul_apply_eq_comp]
    rw [hsucc, map_add, map_smul, hstep, add_add_add_comm, ih, pow_succ' (-1 : O), neg_one_mul,
      neg_smul]
    abel

private theorem coeff_neumannPartialSum_sub_mem (b : Fin p → O⟦X⟧) {M N : ℕ} (hMN : M ≤ N)
    (i : Fin p) (n : ℕ) :
    coeff n (neumannPartialSum b M i) - coeff n (neumannPartialSum b N i) ∈
      Ideal.span {(p : O)} ^ M := by
  have hsub : neumannPartialSum b N - neumannPartialSum b M =
      ∑ m ∈ Finset.Ico M N, (-1 : O) ^ m • (neumannStep p O ^ m) b := by
    simp only [neumannPartialSum]
    rw [← Finset.sum_range_add_sum_Ico _ hMN, add_sub_cancel_left]
  rw [← neg_mem_iff, neg_sub, ← map_sub, ← Pi.sub_apply, hsub, Finset.sum_apply, map_sum]
  refine Ideal.sum_mem _ fun m hm ↦ ?_
  rw [Pi.smul_apply, map_smul]
  exact Ideal.pow_le_pow_right (Finset.mem_Ico.mp hm).1
    ((Ideal.span {(p : O)} ^ m).smul_mem _ (coeff_neumannStep_pow_mem b m i n))

private theorem id_add_neumannStep_surjective [IsAdicComplete (Ideal.span {(p : O)}) O] :
    Function.Surjective ((LinearMap.id : Module.End O (Fin p → O⟦X⟧)) + neumannStep p O) := by
  set I : Ideal O := Ideal.span {(p : O)}
  set T : Module.End O (Fin p → O⟦X⟧) := neumannStep p O
  intro b
  have hex (i : Fin p) (n : ℕ) :
      ∃ c : O, ∀ M : ℕ, coeff n (neumannPartialSum b M i) - c ∈ I ^ M := by
    obtain ⟨c, hc⟩ := IsPrecomplete.prec (I := I) (M := O) inferInstance
      (f := fun N ↦ coeff n (neumannPartialSum b N i)) (fun {M N} hMN ↦ by
        rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
        exact coeff_neumannPartialSum_sub_mem b hMN i n)
    exact ⟨c, fun M ↦ by simpa [SModEq.sub_mem] using hc M⟩
  choose c hc using hex
  let a : Fin p → O⟦X⟧ := fun i ↦ mk (c i)
  refine ⟨a, funext fun i ↦ PowerSeries.ext fun n ↦ ?_⟩
  rw [← sub_eq_zero, ← map_sub]
  refine IsHausdorff.haus (I := I) inferInstance (coeff n ((a + T a) i - b i)) fun M ↦ ?_
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]
  have htel : neumannPartialSum b M + T (neumannPartialSum b M) =
      b - (-1 : O) ^ M • (T ^ M) b := neumannPartialSum_telescoping b M
  have hdecomp : (a + T a) - b =
      (a - neumannPartialSum b M) + T (a - neumannPartialSum b M) -
        (-1 : O) ^ M • (T ^ M) b := by
    calc (a + T a) - b
        = (a + T a) - (neumannPartialSum b M + T (neumannPartialSum b M) +
            (-1 : O) ^ M • (T ^ M) b) := by rw [htel, sub_add_cancel]
      _ = (a - neumannPartialSum b M) + T (a - neumannPartialSum b M) -
            (-1 : O) ^ M • (T ^ M) b := by rw [map_sub]; abel
  rw [← Pi.sub_apply, hdecomp]
  simp only [Pi.sub_apply, Pi.add_apply, map_sub, map_add]
  have haS (j : Fin p) (r : ℕ) : coeff r ((a - neumannPartialSum b M) j) ∈ I ^ M := by
    rw [Pi.sub_apply, map_sub, coeff_mk, ← neg_mem_iff, neg_sub]; exact hc j r M
  have hTaS : coeff n (T a i) - coeff n (T (neumannPartialSum b M) i) ∈ I ^ M := by
    rw [← map_sub, ← Pi.sub_apply, ← map_sub]
    exact Ideal.mul_le_right (coeff_neumannStep_mem (I ^ M) (fun j r _ ↦ haS j r) i)
  have hTM : coeff n (((-1 : O) ^ M • (T ^ M) b) i) ∈ I ^ M := by
    rw [Pi.smul_apply, map_smul]
    exact (I ^ M).smul_mem _ (coeff_neumannStep_pow_mem b M i n)
  exact sub_mem (add_mem (haS i n) hTaS) hTM

private theorem assembly_bijective [IsAdicComplete (Ideal.span {(p : O)}) O] :
    Function.Bijective (assembly p O) := by
  let idAddT : Module.End O (Fin p → O⟦X⟧) := LinearMap.id + neumannStep p O
  have hcomp : (assembly p O : (Fin p → O⟦X⟧) → O⟦X⟧) = (expandOneAddXEquiv p O) ∘ idAddT :=
    funext assembly_eq_expandOneAddXEquiv_add_neumannStep
  rw [hcomp]
  exact (expandOneAddXEquiv p O).bijective.comp
    ⟨id_add_neumannStep_injective, id_add_neumannStep_surjective⟩

end BasisConstruction

section Coordinates

variable (p : ℕ) [Fact p.Prime] (O : Type*) [CommRing O] [IsAdicComplete (Ideal.span {(p : O)}) O]

/-- The `O`-linear equivalence sending a power series `f ∈ O⟦X⟧` to its unique tuple of Coleman
coordinates `c : Fin p → O⟦X⟧` satisfying `∑ i < p, Φ(c i) * (1 + X) ^ i = f`. -/
def coordEquiv : O⟦X⟧ ≃ₗ[O] (Fin p → O⟦X⟧) :=
  (LinearEquiv.ofBijective (assembly p O) assembly_bijective).symm

/-- The `i`-th Coleman coordinate `cᵢ : O⟦X⟧ →ₗ[O] O⟦X⟧` in the unique expansion
`f = ∑ i < p, Φ(cᵢ(f)) * (1 + X) ^ i`. -/
def coord (i : Fin p) : O⟦X⟧ →ₗ[O] O⟦X⟧ :=
  (LinearMap.proj i).comp (coordEquiv p O).toLinearMap

variable {p O}

/-- Evaluating `coordEquiv p O f` at `i` gives `coord p O i f`. -/
@[simp]
theorem coordEquiv_apply (f : O⟦X⟧) (i : Fin p) : coordEquiv p O f i = coord p O i f := by rfl

/-- The inverse of `coordEquiv p O` assembles the Coleman expansion
`∑ i < p, Φ(a i) * (1 + X) ^ i`. -/
@[simp]
theorem coordEquiv_symm_apply (a : Fin p → O⟦X⟧) :
    (coordEquiv p O).symm a = ∑ i : Fin p, frobeniusHom p O (a i) * (1 + X) ^ (i : ℕ) := by rfl

/-- Every power series `f ∈ O⟦X⟧` expands in the Coleman basis as
`∑ i < p, Φ(coord p O i f) * (1 + X) ^ i`. -/
theorem sum_frobeniusHom_coord (f : O⟦X⟧) :
    ∑ i : Fin p, frobeniusHom p O (coord p O i f) * (1 + X) ^ (i : ℕ) = f :=
  (LinearEquiv.ofBijective (assembly p O) assembly_bijective).apply_symm_apply f

/-- Uniqueness of coordinates in the Coleman expansion. -/
theorem coord_unique {a : Fin p → O⟦X⟧} {f : O⟦X⟧}
    (ha : ∑ i : Fin p, frobeniusHom p O (a i) * (1 + X) ^ (i : ℕ) = f) (i : Fin p) :
    coord p O i f = a i :=
  congrFun ((LinearEquiv.ofBijective (assembly p O) assembly_bijective).symm_apply_eq.mpr ha.symm) i

/-- Multiplying by `Φ(a)` scales every Coleman coordinate by `a`. -/
@[simp]
theorem coord_frobeniusHom_mul (a f : O⟦X⟧) (i : Fin p) :
    coord p O i (frobeniusHom p O a * f) = a * coord p O i f := by
  refine coord_unique (a := fun j ↦ a * coord p O j f) ?_ i
  simp only [map_mul, mul_assoc, ← Finset.mul_sum, sum_frobeniusHom_coord]

/-- The Coleman coordinates of `(1 + X) ^ n` pick out the residue `n % p` with coefficient
`(1 + X) ^ (n / p)`. -/
theorem coord_one_add_X_pow (n : ℕ) (j : Fin p) :
    coord p O j ((1 + X : O⟦X⟧) ^ n) =
      if (j : ℕ) = n % p then (1 + X) ^ (n / p) else 0 := by
  refine coord_unique (a := fun k : Fin p ↦
    if (k : ℕ) = n % p then (1 + X) ^ (n / p) else 0) ?_ j
  let r : Fin p := ⟨n % p, Nat.mod_lt n (Fact.out : p.Prime).pos⟩
  rw [Finset.sum_eq_single r]
  · simp [r, frobeniusHom_one_add_X_pow, ← pow_add, Nat.div_add_mod]
  · intro k _ hkr
    have hk : (k : ℕ) ≠ n % p := fun h ↦ hkr (Fin.ext h)
    simp [hk]
  · simp

/-- The Coleman coordinates of `1` are `1` at `i = 0` and `0` elsewhere. -/
@[simp]
theorem coord_one (i : Fin p) : coord p O i 1 = if (i : ℕ) = 0 then 1 else 0 := by
  simpa using coord_one_add_X_pow (p := p) (O := O) 0 i

/-- The Coleman coordinates of `Φ(a)` are `a` at `i = 0` and `0` elsewhere. -/
@[simp]
theorem coord_frobeniusHom (a : O⟦X⟧) (i : Fin p) :
    coord p O i (frobeniusHom p O a) = if (i : ℕ) = 0 then a else 0 := by
  simpa using coord_frobeniusHom_mul (p := p) a 1 i

/-- Multiplying by a constant `C c` scales every Coleman coordinate by `C c`. -/
@[simp]
theorem coord_C_mul (c : O) (f : O⟦X⟧) (i : Fin p) :
    coord p O i (C c * f) = C c * coord p O i f := by
  conv_lhs => rw [← frobeniusHom_C (p := p) c]
  exact coord_frobeniusHom_mul (C c) f i

/-- The Coleman coordinates of a constant series `C c` are `C c` at `i = 0` and `0` elsewhere. -/
@[simp]
theorem coord_C (c : O) (i : Fin p) : coord p O i (C c) = if (i : ℕ) = 0 then C c else 0 := by
  conv_lhs => rw [← frobeniusHom_C (p := p) c]
  exact coord_frobeniusHom (C c) i

/-- Coefficientwise change of base ring commutes with Coleman coordinates. -/
theorem map_coord {O' : Type*} [CommRing O'] [IsAdicComplete (Ideal.span {(p : O')}) O']
    (φ : O →+* O') (f : O⟦X⟧) (i : Fin p) :
    PowerSeries.map φ (coord p O i f) = coord p O' i (PowerSeries.map φ f) := by
  symm
  refine coord_unique (a := fun j ↦ PowerSeries.map φ (coord p O j f)) ?_ i
  have h := congrArg (PowerSeries.map φ) (sum_frobeniusHom_coord (p := p) f)
  simpa only [map_sum, map_mul, map_pow, map_add, map_one, map_X, map_frobeniusHom] using h

/-- **Explicit `(p)`-adic modulus of continuity for Coleman coordinates.** If the first
`p ^ k * (n + 1)` coefficients of `f` lie in `(p) ^ k`, then the `n`-th coefficient of every
Coleman coordinate of `f` lies in `(p) ^ k`. -/
theorem coeff_coord_mem_pow_of_coeff_mem_pow :
    ∀ k : ℕ, ∀ {f : O⟦X⟧} {n : ℕ},
      (∀ s < p ^ k * (n + 1), coeff s f ∈ Ideal.span {(p : O)} ^ k) →
      ∀ i : Fin p, coeff n (coord p O i f) ∈ Ideal.span {(p : O)} ^ k
  | 0, _, _, _, _ => by simp
  | k + 1, f, n, hf, i => by
    let a : Fin p → O⟦X⟧ := fun j ↦ coord p O j f
    have ha_eq : a = (expandOneAddXEquiv p O).symm f - neumannStep p O a := by
      have h1 : expandOneAddXEquiv p O (a + neumannStep p O a) = f := by
        rw [← assembly_eq_expandOneAddXEquiv_add_neumannStep]; exact sum_frobeniusHom_coord f
      have h2 := congrArg (expandOneAddXEquiv p O).symm h1
      rw [LinearEquiv.symm_apply_apply] at h2
      exact eq_sub_of_add_eq h2
    have hcoeff : coeff n (coord p O i f) =
        coeff n ((expandOneAddXEquiv p O).symm f i) - coeff n (neumannStep p O a i) := by
      rw [← map_sub, ← Pi.sub_apply, ← ha_eq]
    rw [hcoeff]
    refine sub_mem ?_ ?_
    · refine coeff_expandOneAddXEquiv_symm_mem (Ideal.span {(p : O)} ^ (k + 1)) (fun s hs ↦ ?_) i
      have hpk : 1 ≤ p ^ k := Nat.one_le_pow k p (Fact.out : p.Prime).pos
      exact hf s (lt_of_lt_of_le hs (by rw [pow_succ']; nlinarith))
    · rw [pow_succ']
      refine coeff_neumannStep_mem (Ideal.span {(p : O)} ^ k) (fun j m hm ↦ ?_) i
      refine coeff_coord_mem_pow_of_coeff_mem_pow k (fun s hs ↦ ?_) j
      refine Ideal.pow_le_pow_right (Nat.le_succ k) (hf s (lt_of_lt_of_le hs ?_))
      rw [pow_succ, mul_assoc]
      exact Nat.mul_le_mul_left _ hm

end Coordinates

end TauCeti.Coleman
