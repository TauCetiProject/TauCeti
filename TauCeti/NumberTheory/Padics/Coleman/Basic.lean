/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.PowerSeries.Expand
public import Mathlib.RingTheory.PowerSeries.Substitution

import Mathlib.Algebra.Ring.GeomSum
import TauCeti.RingTheory.AdicCompletion.Pi
import TauCeti.RingTheory.PowerSeries.Cartier
import TauCeti.RingTheory.PowerSeries.OneAddXPow
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
* `TauCeti.Coleman.frobeniusHom_injective`, `TauCeti.Coleman.frobeniusHom_mem_span_p_pow_iff`:
  injectivity of `Φ` and reflection of `(p) ^ k`-congruences.
* `TauCeti.Coleman.coord_one_add_X_pow`, `TauCeti.Coleman.map_coord`: coordinates of `(1 + X) ^ n`
  and functoriality along coefficient ring homomorphisms.
* `TauCeti.Coleman.coeff_coord_mem_span_pow_of_coeff_mem_span_pow`: explicit `(p)`-adic modulus of
  continuity for the Coleman coordinates.

## References

* R. F. Coleman, *Division Values in Local Fields*, Invent. Math. 53 (1979), §§II, IV (Lemma 6,
  Theorem 11).
* J. Coates and R. Sujatha, *Cyclotomic Fields and Zeta Values*, Springer (2006), §2.2
  (Proposition 2.2.3).
* R. Sharifi, *Iwasawa Theory*, §5.4 (Proposition 5.4.3).
* J. Rodrigues Jacinto and C. Williams, *An introduction to p-adic L-functions* (2025), Chapter 10
  (Lemma 10.8).
-/

public noncomputable section

open PowerSeries

namespace TauCeti.Coleman

section Frobenius

variable (p : ℕ) (O : Type*) [CommRing O]

/-- The series `(1 + X) ^ p - 1` satisfies `HasSubst` over any commutative ring `O`. -/
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
  -- `PowerSeries.map` is `MvPowerSeries.map` over `Unit`, the form in which Mathlib states
  -- `PowerSeries.map_subst`.
  change PowerSeries.map φ _ =
    (PowerSeries.map φ f).subst (PowerSeries.map φ ((1 + X : O⟦X⟧) ^ p - 1)) at h
  rw [h, map_sub, map_pow, map_add, map_one, PowerSeries.map_X]

/-- When `(p : O) = 0`, `frobeniusHom` coincides with `PowerSeries.expand p`. -/
theorem frobeniusHom_eq_expand [Fact p.Prime] (hp : (p : O) = 0) (f : O⟦X⟧) :
    frobeniusHom p O f = expand p (Fact.out : p.Prime).ne_zero f := by
  obtain ⟨q, hq⟩ := C_dvd_one_add_X_pow_sub_one_sub_X_pow (O := O) (Fact.out : p.Prime)
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
    _ = ∑ k : Fin p, X ^ (k : ℕ) * expand p hp (cartier O p k f) := by
        refine Finset.sum_congr rfl fun k _ ↦ ?_
        have hfilt : (Finset.range p).filter (· ≤ (k : ℕ)) = Finset.range ((k : ℕ) + 1) := by
          ext j; simp only [Finset.mem_filter, Finset.mem_range]; omega
        have hbinom : (∑ j : Fin p, if (j : ℕ) ≤ k then
            C ((-1 : O) ^ ((k : ℕ) - j) * ((k : ℕ).choose j : O)) * (1 + X) ^ (j : ℕ) else 0) =
            X ^ (k : ℕ) := by
          rw [Fin.sum_univ_eq_sum_range (fun j ↦ if j ≤ (k : ℕ) then
            C ((-1 : O) ^ ((k : ℕ) - j) * ((k : ℕ).choose j : O)) * (1 + X) ^ j else 0),
            ← Finset.sum_filter, hfilt]
          calc ∑ j ∈ Finset.range ((k : ℕ) + 1),
                C ((-1 : O) ^ ((k : ℕ) - j) * ((k : ℕ).choose j : O)) * (1 + X) ^ j
              = ∑ j ∈ Finset.range ((k : ℕ) + 1),
                  (1 + X : O⟦X⟧) ^ j * (-1 : O⟦X⟧) ^ ((k : ℕ) - j) *
                    ((k : ℕ).choose j : O⟦X⟧) :=
                Finset.sum_congr rfl fun j _ ↦ by
                  simp only [map_mul, map_pow, map_neg, map_one, map_natCast]; ring
            _ = ((1 + X : O⟦X⟧) + (-1 : O⟦X⟧)) ^ (k : ℕ) := (add_pow _ _ _).symm
            _ = X ^ (k : ℕ) := by simp
        rw [hbinom, mul_comm]
    _ = f := by
        rw [Fin.sum_univ_eq_sum_range (fun k ↦ X ^ k * expand p hp (cartier O p k f))]
        exact (sum_X_pow_mul_expand_cartier p hp f).symm

private theorem expandOneAddX_injective : Function.Injective (expandOneAddXLinearMap p O) := by
  have hp : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  rw [injective_iff_map_eq_zero]
  intro a ha
  have hsys (k : Fin p) : (∑ j : Fin p, C (((j : ℕ).choose k : O)) * a j) = 0 := by
    have hc := congrArg (cartier O p k) ha
    simp only [expandOneAddXLinearMap, LinearMap.coe_mk, AddHom.coe_mk, map_sum, map_zero] at hc
    conv_rhs => rw [← hc]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [cartier_expand_mul p k hp k.isLt, PowerSeries.cartier_one_add_X_pow p k j.isLt, mul_comm]
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
      rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hjk) with hlt | hgt
      · rw [Nat.choose_eq_zero_of_lt hlt, Nat.cast_zero, map_zero, zero_mul]
      · rw [ih _ (by omega) j rfl, mul_zero]
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
    (C_dvd_one_add_X_pow_sub_one_sub_X_pow (O := O) (Fact.out : p.Prime)).trans
      (sub_dvd_pow_sub_pow _ _ k)
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

omit [Fact p.Prime] in
private theorem assembly_apply (a : Fin p → O⟦X⟧) :
    assembly p O a = ∑ i : Fin p, frobeniusHom p O (a i) * (1 + X) ^ (i : ℕ) := rfl

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
  have hzero : (fun x : Fin p × ℕ ↦ coeff x.2 (a x.1)) = 0 :=
    TauCeti.eq_zero_of_forall_pow_dvd (p : O) fun m ⟨i, n⟩ ↦ by
      rw [← Ideal.mem_span_singleton, ← Ideal.span_singleton_pow]
      have hmem : coeff n ((T ^ m) a i) ∈ I ^ m := coeff_neumannStep_pow_mem a m i n
      rw [hpow m, Pi.smul_apply, map_smul, smul_eq_mul] at hmem
      have hmul := Ideal.mul_mem_left (I ^ m) ((-1 : O) ^ m) hmem
      rwa [← mul_assoc, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_mul] at hmul
  funext i; ext n
  exact congrFun hzero (i, n)

private def neumannPartialSum (b : Fin p → O⟦X⟧) (N : ℕ) : Fin p → O⟦X⟧ :=
  ∑ m ∈ Finset.range N, (-1 : O) ^ m • (neumannStep p O ^ m) b

private theorem neumannPartialSum_telescoping (b : Fin p → O⟦X⟧) (M : ℕ) :
    neumannPartialSum b M + neumannStep p O (neumannPartialSum b M) =
      b - (-1 : O) ^ M • (neumannStep p O ^ M) b := by
  set T : Module.End O (Fin p → O⟦X⟧) := neumannStep p O
  have hneg (m : ℕ) : (-T) ^ m = (-1 : O) ^ m • T ^ m := by
    rw [← neg_one_smul O T, smul_pow]
  have hgeom := congrArg (fun L : Module.End O (Fin p → O⟦X⟧) ↦ L b) (mul_neg_geom_sum (-T) M)
  simp only [sub_neg_eq_add, mul_apply_eq_comp, LinearMap.add_apply, LinearMap.sub_apply,
    one_apply_eq_self, LinearMap.sum_apply, hneg, LinearMap.smul_apply] at hgeom
  exact hgeom

private theorem id_add_neumannStep_surjective [IsAdicComplete (Ideal.span {(p : O)}) O] :
    Function.Surjective ((LinearMap.id : Module.End O (Fin p → O⟦X⟧)) + neumannStep p O) := by
  set I : Ideal O := Ideal.span {(p : O)}
  set T : Module.End O (Fin p → O⟦X⟧) := neumannStep p O
  intro b
  obtain ⟨c, hc⟩ := TauCeti.exists_forall_pow_dvd_sub (p : O)
    (fun m (x : Fin p × ℕ) ↦ coeff x.2 (neumannPartialSum b m x.1)) fun m ⟨i, n⟩ ↦ by
      rw [← Ideal.mem_span_singleton, ← Ideal.span_singleton_pow, ← map_sub, ← Pi.sub_apply,
        neumannPartialSum, neumannPartialSum, Finset.sum_range_succ, add_sub_cancel_left,
        Pi.smul_apply, map_smul]
      exact (I ^ m).smul_mem _ (coeff_neumannStep_pow_mem b m i n)
  let a : Fin p → O⟦X⟧ := fun i ↦ mk fun n ↦ c (i, n)
  have hzero : (fun x : Fin p × ℕ ↦ coeff x.2 ((a + T a) x.1 - b x.1)) = 0 :=
    TauCeti.eq_zero_of_forall_pow_dvd (p : O) fun M ⟨i, n⟩ ↦ by
      rw [← Ideal.mem_span_singleton, ← Ideal.span_singleton_pow]
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
        rw [Pi.sub_apply, map_sub, coeff_mk, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
        exact hc M (j, r)
      have hTaS : coeff n (T a i) - coeff n (T (neumannPartialSum b M) i) ∈ I ^ M := by
        rw [← map_sub, ← Pi.sub_apply, ← map_sub]
        exact Ideal.mul_le_right (coeff_neumannStep_mem (I ^ M) (fun j r _ ↦ haS j r) i)
      have hTM : coeff n (((-1 : O) ^ M • (T ^ M) b) i) ∈ I ^ M := by
        rw [Pi.smul_apply, map_smul]
        exact (I ^ M).smul_mem _ (coeff_neumannStep_pow_mem b M i n)
      exact sub_mem (add_mem (haS i n) hTaS) hTM
  refine ⟨a, funext fun i ↦ PowerSeries.ext fun n ↦ ?_⟩
  rw [← sub_eq_zero, ← map_sub]
  exact congrFun hzero (i, n)

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
coordinates `c : Fin p → O⟦X⟧` satisfying `∑ i < p, Φ(c i) * (1 + X) ^ i = f` (Coleman,
Theorem 11; Sharifi, Proposition 5.4.3; Rodrigues Jacinto–Williams, Lemma 10.8). -/
def coordEquiv : O⟦X⟧ ≃ₗ[O] (Fin p → O⟦X⟧) :=
  (LinearEquiv.ofBijective (assembly p O) assembly_bijective).symm

/-- The `i`-th Coleman coordinate `cᵢ : O⟦X⟧ →ₗ[O] O⟦X⟧` in the unique expansion
`f = ∑ i < p, Φ(cᵢ(f)) * (1 + X) ^ i`. -/
def coord (i : Fin p) : O⟦X⟧ →ₗ[O] O⟦X⟧ :=
  (LinearMap.proj i).comp (coordEquiv p O).toLinearMap

variable {p O}

/-- Evaluating `coordEquiv p O f` at `i` gives `coord p O i f`. -/
@[simp]
theorem coordEquiv_apply (f : O⟦X⟧) (i : Fin p) : coordEquiv p O f i = coord p O i f := by
  rw [coord, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, LinearMap.proj_apply]

/-- The inverse of `coordEquiv p O` assembles the Coleman expansion
`∑ i < p, Φ(a i) * (1 + X) ^ i`. -/
@[simp]
theorem coordEquiv_symm_apply (a : Fin p → O⟦X⟧) :
    (coordEquiv p O).symm a = ∑ i : Fin p, frobeniusHom p O (a i) * (1 + X) ^ (i : ℕ) := by
  rw [coordEquiv, LinearEquiv.symm_symm, LinearEquiv.ofBijective_apply, assembly_apply]

/-- **Coleman's basis expansion.** Every power series `f ∈ O⟦X⟧` expands uniquely as
`∑ i < p, Φ(coord p O i f) * (1 + X) ^ i` (Coleman, Theorem 11; Sharifi, Proposition 5.4.3;
Rodrigues Jacinto–Williams, Lemma 10.8). -/
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
@[simp]
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

/-- The Coleman coordinates of `1 + X` are `1` at `i = 1` and `0` elsewhere. -/
@[simp]
theorem coord_one_add_X (i : Fin p) :
    coord p O i (1 + X) = if (i : ℕ) = 1 then 1 else 0 := by
  simpa [Nat.mod_eq_of_lt (Fact.out : p.Prime).one_lt,
    Nat.div_eq_of_lt (Fact.out : p.Prime).one_lt] using coord_one_add_X_pow (p := p) (O := O) 1 i

/-- The Coleman coordinates of `1` are `1` at `i = 0` and `0` elsewhere. -/
@[simp]
theorem coord_one (i : Fin p) : coord p O i 1 = if (i : ℕ) = 0 then 1 else 0 := by
  simpa using coord_one_add_X_pow (p := p) (O := O) 0 i

/-- The Coleman coordinates of `Φ(a)` are `a` at `i = 0` and `0` elsewhere. -/
@[simp]
theorem coord_frobeniusHom (a : O⟦X⟧) (i : Fin p) :
    coord p O i (frobeniusHom p O a) = if (i : ℕ) = 0 then a else 0 := by
  simpa using coord_frobeniusHom_mul (p := p) a 1 i

/-- Over a `(p)`-adically complete ring `O`, Frobenius substitution `frobeniusHom p O` is
injective. -/
theorem frobeniusHom_injective : Function.Injective (frobeniusHom p O) := fun f g h ↦ by
  simpa using congrArg (coord p O ⟨0, (Fact.out : p.Prime).pos⟩) h

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

/-- Frobenius substitution preserves and reflects membership in `(p) ^ k`. -/
theorem frobeniusHom_mem_span_p_pow_iff (k : ℕ) {f : O⟦X⟧} :
    frobeniusHom p O f ∈ Ideal.span {(p : O⟦X⟧)} ^ k ↔ f ∈ Ideal.span {(p : O⟦X⟧)} ^ k := by
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton, Ideal.mem_span_singleton]
  refine ⟨fun ⟨g, hg⟩ ↦ ⟨coord p O ⟨0, (Fact.out : p.Prime).pos⟩ g, ?_⟩,
    fun ⟨g, hg⟩ ↦ ⟨frobeniusHom p O g, by rw [hg, map_mul, map_pow, map_natCast]⟩⟩
  have h := congrArg (coord p O ⟨0, (Fact.out : p.Prime).pos⟩) hg
  simp only [coord_frobeniusHom, ↓reduceIte] at h
  rwa [← map_natCast C, ← map_pow, coord_C_mul, map_pow, map_natCast] at h

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
theorem coeff_coord_mem_span_pow_of_coeff_mem_span_pow :
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
      refine coeff_coord_mem_span_pow_of_coeff_mem_span_pow k (fun s hs ↦ ?_) j
      refine Ideal.pow_le_pow_right (Nat.le_succ k) (hf s (lt_of_lt_of_le hs ?_))
      rw [pow_succ, mul_assoc]
      exact Nat.mul_le_mul_left _ hm

end Coordinates

end TauCeti.Coleman
