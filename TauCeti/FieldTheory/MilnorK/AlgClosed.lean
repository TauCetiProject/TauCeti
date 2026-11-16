/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Splits
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import TauCeti.FieldTheory.MilnorK.Grading
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Monic
import TauCeti.Algebra.Module.Submodule.Quotient
import TauCeti.LinearAlgebra.TensorProduct.Torsion
import TauCeti.LinearAlgebra.TensorSquare

/-!
# Unique divisibility of Milnor K-groups over algebraically closed fields

This file proves Bass–Tate's root-factorization divisibility theorem for Milnor K-theory: for a
field `F` and a positive integer `m`, if every polynomial `X ^ m - C (a : F)` with `a : Fˣ` splits
over `F`, then every homogeneous Steinberg relation submodule `MilnorK.relationSubmodule F n` is
`m`-divisible, and multiplication by `m` is bijective on `MilnorK.degree F n` for every `n ≥ 2`.
In particular, for an algebraically closed field `F`, `MilnorK.degree F n` is uniquely divisible
in every degree `n ≥ 2`.

## Main results

* `TauCeti.MilnorK.surjective_nsmul_relationSubmodule_of_splits`: `relationSubmodule F n` is
  `m`-divisible whenever every `X ^ m - C (a : F)` splits over `F`.
* `TauCeti.MilnorK.bijective_nsmul_quotient_of_splits`: multiplication by `m` is bijective on
  `((⨂[ℤ]^n) (Additive Fˣ)) ⧸ relationSubmodule F n` for `n ≥ 2` under the splitting hypothesis.
* `TauCeti.MilnorK.bijective_nsmul_degree_of_splits`: multiplication by `m` is bijective on
  `MilnorK.degree F n` for `n ≥ 2` under the splitting hypothesis.
* `TauCeti.MilnorK.uniqueDivisible_of_isAlgClosed`: for an algebraically closed field `F`,
  `MilnorK.degree F n` is uniquely divisible for all `n ≥ 2`.

## References

* C. A. Weibel, *The K-book: An Introduction to Algebraic K-Theory*, Proposition III.6.4.1,
  Example III.7.2(b), and Exercise III.7.3.
-/

public section

namespace TauCeti

open scoped Polynomial TensorProduct

universe u

namespace MilnorK

section SplitsDivisibility

variable {F : Type u} [Field F]

private theorem surjective_zsmul_additive_units_of_splits {m : ℕ} (hm : 0 < m)
    (hsplit : ∀ a : Fˣ, (Polynomial.X ^ m - Polynomial.C (a : F)).Splits) :
    Function.Surjective (fun u : Additive Fˣ ↦ (m : ℤ) • u) := by
  intro u
  let a : Fˣ := Additive.toMul u
  let f : F[X] := Polynomial.X ^ m - Polynomial.C (a : F)
  have hf_monic : f.Monic := Polynomial.monic_X_pow_sub_C (a : F) hm.ne'
  have hf_deg : f.degree ≠ 0 := by
    rw [Polynomial.degree_eq_natDegree hf_monic.ne_zero, Polynomial.natDegree_X_pow_sub_C]
    exact_mod_cast hm.ne'
  obtain ⟨r, hr⟩ := (hsplit a).exists_eval_eq_zero hf_deg
  have hr_pow : r ^ m = (a : F) := by
    simpa [f, sub_eq_zero] using hr
  have hr_ne : r ≠ 0 := by
    intro h0
    rw [h0, zero_pow hm.ne'] at hr_pow
    exact a.ne_zero hr_pow.symm
  let r_u : Fˣ := Units.mk0 r hr_ne
  refine ⟨Additive.ofMul r_u, ?_⟩
  dsimp only
  rw [natCast_zsmul, ← ofMul_pow]
  have hpow : r_u ^ m = a := Units.ext (by simpa [r_u] using hr_pow)
  rw [hpow, ofMul_toMul]

private theorem bijective_zsmul_of_linearEquiv {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    (e : M ≃ₗ[ℤ] N) (k : ℤ) (h : Function.Bijective (fun x : M ↦ k • x)) :
    Function.Bijective (fun y : N ↦ k • y) := by
  have heq : (fun y : N ↦ k • y) = e ∘ (fun x : M ↦ k • x) ∘ e.symm := by
    funext y
    simp only [Function.comp_apply, ← map_smul, LinearEquiv.apply_symm_apply]
  rw [heq]
  exact e.bijective.comp (h.comp e.symm.bijective)

private theorem bijective_zsmul_tensorPower_of_splits {m : ℕ} (hm : 0 < m)
    (hsplit : ∀ a : Fˣ, (Polynomial.X ^ m - Polynomial.C (a : F)).Splits) :
    ∀ {n : ℕ}, 2 ≤ n → Function.Bijective (fun t : (⨂[ℤ]^n) (Additive Fˣ) ↦ (m : ℤ) • t) := by
  have h1 : Function.Surjective (fun u : Additive Fˣ ↦ (m : ℤ) • u) :=
    surjective_zsmul_additive_units_of_splits hm hsplit
  intro n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  clear hn
  induction k with
  | zero =>
    have h2 : Function.Bijective
        (fun t : Additive Fˣ ⊗[ℤ] Additive Fˣ ↦ (m : ℤ) • t) :=
      bijective_smul_tensorProduct (m : ℤ) h1 h1
    exact bijective_zsmul_of_linearEquiv
      (tensorProductEquivTensorSquare ℤ (Additive Fˣ)) (m : ℤ) h2
  | succ k ih =>
    have hpow1 : Function.Surjective (fun u : (⨂[ℤ]^1) (Additive Fˣ) ↦ (m : ℤ) • u) := by
      intro u
      obtain ⟨v, hv⟩ := h1 (PiTensorProduct.subsingletonEquiv (0 : Fin 1) u)
      refine ⟨(PiTensorProduct.subsingletonEquiv (0 : Fin 1)).symm v, ?_⟩
      dsimp only at hv ⊢
      rw [← map_smul, hv, LinearEquiv.symm_apply_apply]
    have hprod : Function.Bijective
        (fun t : (⨂[ℤ]^(2 + k)) (Additive Fˣ) ⊗[ℤ] (⨂[ℤ]^1) (Additive Fˣ) ↦ (m : ℤ) • t) :=
      bijective_smul_tensorProduct (m : ℤ) ih.surjective hpow1
    exact bijective_zsmul_of_linearEquiv
      (TensorPower.mulEquiv (R := ℤ) (M := Additive Fˣ) (n := 2 + k) (m := 1)) (m : ℤ) hprod

private theorem exists_zsmul_tprod_update_of_multiset {n m : ℕ} (hm : 0 < m)
    (x : Fin n → Additive Fˣ) {i : ℕ} (hi : i + 1 < n)
    (s : Multiset F)
    (hs_root : ∀ r ∈ s, r ^ m = ((Additive.toMul (x ⟨i, by omega⟩) : Fˣ) : F))
    (hs_one_sub : ∀ r ∈ s, 1 - r ≠ 0) :
    ∀ (P : Fˣ), (P : F) = (s.map (fun r ↦ 1 - r)).prod →
      ∃ w ∈ relationSubmodule F n,
        (m : ℤ) • w =
          PiTensorProduct.tprod ℤ (Function.update x ⟨i + 1, hi⟩ (Additive.ofMul P)) := by
  let i₀ : Fin n := ⟨i, by omega⟩
  let i₁ : Fin n := ⟨i + 1, hi⟩
  have hi01 : i₀ ≠ i₁ := by
    intro h
    have : i = i + 1 := congrArg Fin.val h
    omega
  induction s using Multiset.induction_on with
  | empty =>
    intro P hP
    have hP1 : P = 1 := Units.ext (by simpa using hP)
    refine ⟨0, Submodule.zero_mem _, ?_⟩
    rw [smul_zero, hP1, ofMul_one]
    exact ((PiTensorProduct.tprod ℤ).map_coord_zero i₁ (Function.update_self i₁ 0 x)).symm
  | cons r t ih =>
    intro P hP
    have hr_root : r ^ m = ((Additive.toMul (x i₀) : Fˣ) : F) :=
      hs_root r (Multiset.mem_cons_self r t)
    have hr_ne : r ≠ 0 := by
      intro h0
      rw [h0, zero_pow hm.ne'] at hr_root
      exact (Additive.toMul (x i₀)).ne_zero hr_root.symm
    have hr_1sub : 1 - r ≠ 0 := hs_one_sub r (Multiset.mem_cons_self r t)
    have ht_root : ∀ q ∈ t, q ^ m = ((Additive.toMul (x i₀) : Fˣ) : F) :=
      fun q hq ↦ hs_root q (Multiset.mem_cons_of_mem hq)
    have ht_1sub : ∀ q ∈ t, 1 - q ≠ 0 :=
      fun q hq ↦ hs_one_sub q (Multiset.mem_cons_of_mem hq)
    have ht_prod_ne : (t.map (fun q ↦ 1 - q)).prod ≠ 0 := by
      intro h0
      have hmem0 : (0 : F) ∈ t.map (fun q ↦ 1 - q) := Multiset.prod_eq_zero_iff.mp h0
      obtain ⟨q, hq, hq0⟩ := Multiset.mem_map.mp hmem0
      exact ht_1sub q hq hq0
    let u : Fˣ := Units.mk0 r hr_ne
    let v : Fˣ := Units.mk0 (1 - r) hr_1sub
    let Pt : Fˣ := Units.mk0 (t.map (fun q ↦ 1 - q)).prod ht_prod_ne
    have hP_eq : P = v * Pt := Units.ext (by
      simpa [v, Pt, Multiset.map_cons, Multiset.prod_cons] using hP)
    obtain ⟨w₂, hw₂_mem, hw₂_eq⟩ := ih ht_root ht_1sub Pt rfl
    let y : Fin n → Additive Fˣ :=
      Function.update (Function.update x i₁ (Additive.ofMul v)) i₀ (Additive.ofMul u)
    have hw₁_mem : PiTensorProduct.tprod ℤ y ∈ relationSubmodule F n := by
      refine tprod_mem_relationSubmodule y (i := i) hi ?_
      have hy0 : y i₀ = Additive.ofMul u := by simp [y]
      have hy1 : y i₁ = Additive.ofMul v := by simp [y, hi01.symm]
      change ((Additive.toMul (y i₀) : Fˣ) : F) + ((Additive.toMul (y i₁) : Fˣ) : F) = 1
      rw [hy0, hy1, toMul_ofMul, toMul_ofMul]
      simp [u, v]
    have hu_pow : (m : ℤ) • Additive.ofMul u = x i₀ := by
      rw [natCast_zsmul, ← ofMul_pow]
      have hpow : u ^ m = Additive.toMul (x i₀) := Units.ext (by simpa [u] using hr_root)
      rw [hpow, ofMul_toMul]
    have hw₁_eq : (m : ℤ) • PiTensorProduct.tprod ℤ y =
        PiTensorProduct.tprod ℤ (Function.update x i₁ (Additive.ofMul v)) := by
      have hsmul := (PiTensorProduct.tprod ℤ).map_update_smul
        (Function.update x i₁ (Additive.ofMul v)) i₀ (m : ℤ) (Additive.ofMul u)
      dsimp only [RingHom.id_apply] at hsmul
      dsimp only [y]
      rw [← hsmul]
      congr 1
      ext j
      by_cases hj : j = i₀
      · subst hj
        rw [Function.update_self, Function.update_of_ne hi01, hu_pow]
      · rw [Function.update_of_ne hj]
    refine ⟨PiTensorProduct.tprod ℤ y + w₂, Submodule.add_mem _ hw₁_mem hw₂_mem, ?_⟩
    rw [smul_add, hw₁_eq, hw₂_eq, hP_eq, ofMul_mul,
      (PiTensorProduct.tprod ℤ).map_update_add x i₁ (Additive.ofMul v) (Additive.ofMul Pt)]

/-- If every polynomial `X ^ m - C (a : F)` with `a : Fˣ` splits over `F`, then the degree-`n`
Steinberg relation submodule `relationSubmodule F n` is `m`-divisible. -/
theorem surjective_nsmul_relationSubmodule_of_splits {m : ℕ} (hm : 0 < m)
    (hsplit : ∀ a : Fˣ, (Polynomial.X ^ m - Polynomial.C (a : F)).Splits) (n : ℕ) :
    Function.Surjective (fun x : relationSubmodule F n ↦ m • x) := by
  intro ⟨t, ht⟩
  suffices ∃ w ∈ relationSubmodule F n, (m : ℤ) • w = t by
    obtain ⟨w, hw, rfl⟩ := this
    exact ⟨⟨w, hw⟩, Subtype.ext (by simp [natCast_zsmul])⟩
  rw [relationSubmodule_def] at ht
  refine Submodule.span_induction ?_ ?_ ?_ ?_ ht
  · rintro _ ⟨x, i, hi, hab, rfl⟩
    let a : Fˣ := Additive.toMul (x ⟨i, by omega⟩)
    let b : Fˣ := Additive.toMul (x ⟨i + 1, hi⟩)
    let f : F[X] := Polynomial.X ^ m - Polynomial.C (a : F)
    have hf_monic : f.Monic := Polynomial.monic_X_pow_sub_C (a : F) hm.ne'
    have hfs : f.Splits := hsplit a
    obtain ⟨s, hs⟩ := Polynomial.splits_iff_exists_multiset.mp hfs
    have hf_prod : f = (s.map (fun r ↦ Polynomial.X - Polynomial.C r)).prod := by
      rw [hs, hf_monic.leadingCoeff, map_one, one_mul]
    have hs_root : ∀ r ∈ s, r ^ m = (a : F) := by
      intro r hr
      have hev : Polynomial.eval r f = 0 := by
        rw [hf_prod, Polynomial.eval_multiset_prod]
        refine Multiset.prod_eq_zero ?_
        rw [Multiset.mem_map]
        refine ⟨Polynomial.X - Polynomial.C r, Multiset.mem_map.mpr ⟨r, hr, rfl⟩, ?_⟩
        simp
      simpa [f, sub_eq_zero] using hev
    have hs_prod : (b : F) = (s.map (fun r ↦ 1 - r)).prod := by
      have hb_eq : (b : F) = 1 - (a : F) := eq_sub_of_add_eq' hab
      calc
        (b : F) = Polynomial.eval 1 f := by simp [f, hb_eq]
        _ = (s.map (fun r ↦ 1 - r)).prod := by
              rw [hf_prod, Polynomial.eval_multiset_prod, Multiset.map_map]
              congr 1
              refine Multiset.map_congr rfl fun r _ ↦ ?_
              simp
    have hs_one_sub : ∀ r ∈ s, 1 - r ≠ 0 := by
      intro r hr h0
      have hprod0 : (s.map (fun q ↦ 1 - q)).prod = 0 :=
        Multiset.prod_eq_zero (Multiset.mem_map.mpr ⟨r, hr, h0⟩)
      rw [hprod0] at hs_prod
      exact b.ne_zero hs_prod
    obtain ⟨w, hw_mem, hw_eq⟩ :=
      exists_zsmul_tprod_update_of_multiset hm x hi s hs_root hs_one_sub b hs_prod
    have hupd : Function.update x ⟨i + 1, hi⟩ (Additive.ofMul b) = x := by
      apply Function.update_eq_self_iff.mpr
      exact ofMul_toMul _
    rw [hupd] at hw_eq
    exact ⟨w, hw_mem, hw_eq⟩
  · exact ⟨0, Submodule.zero_mem _, smul_zero (m : ℤ)⟩
  · rintro _ _ _ _ ⟨w₁, hw₁, rfl⟩ ⟨w₂, hw₂, rfl⟩
    exact ⟨w₁ + w₂, Submodule.add_mem _ hw₁ hw₂, smul_add (m : ℤ) w₁ w₂⟩
  · rintro k _ _ ⟨w, hw, rfl⟩
    exact ⟨k • w, Submodule.smul_mem _ k hw, smul_comm (m : ℤ) k w⟩

/-- If every polynomial `X ^ m - C (a : F)` with `a : Fˣ` splits over `F`, then multiplication by
`m` is bijective on the degree-`n` tensor-power quotient
`((⨂[ℤ]^n) (Additive Fˣ)) ⧸ relationSubmodule F n` for every `n ≥ 2`. -/
theorem bijective_nsmul_quotient_of_splits {m : ℕ} (hm : 0 < m)
    (hsplit : ∀ a : Fˣ, (Polynomial.X ^ m - Polynomial.C (a : F)).Splits)
    {n : ℕ} (hn : 2 ≤ n) :
    Function.Bijective
      (fun q : ((⨂[ℤ]^n) (Additive Fˣ)) ⧸ relationSubmodule F n ↦ m • q) := by
  have hT : Function.Bijective (fun t : (⨂[ℤ]^n) (Additive Fˣ) ↦ (m : ℤ) • t) :=
    bijective_zsmul_tensorPower_of_splits hm hsplit hn
  have hR : Function.Surjective (fun s : relationSubmodule F n ↦ (m : ℤ) • s) := by
    simpa [natCast_zsmul] using surjective_nsmul_relationSubmodule_of_splits hm hsplit n
  simpa [natCast_zsmul] using
    Submodule.bijective_smul_quotient (relationSubmodule F n) (m : ℤ) hT hR

/-- If every polynomial `X ^ m - C (a : F)` with `a : Fˣ` splits over `F`, then multiplication by
`m` is bijective on `MilnorK.degree F n` for every `n ≥ 2`. -/
theorem bijective_nsmul_degree_of_splits {m : ℕ} (hm : 0 < m)
    (hsplit : ∀ a : Fˣ, (Polynomial.X ^ m - Polynomial.C (a : F)).Splits)
    {n : ℕ} (hn : 2 ≤ n) :
    Function.Bijective (fun x : degree F n ↦ m • x) := by
  have hQ : Function.Bijective
      (fun q : ((⨂[ℤ]^n) (Additive Fˣ)) ⧸ relationSubmodule F n ↦ (m : ℤ) • q) := by
    simpa [natCast_zsmul] using bijective_nsmul_quotient_of_splits hm hsplit hn
  have hD := bijective_zsmul_of_linearEquiv (degreeEquivQuotient F n).symm (m : ℤ) hQ
  simpa [natCast_zsmul] using hD

end SplitsDivisibility

/-- Milnor K-groups of algebraically closed fields are uniquely divisible in degrees at least
two. -/
theorem uniqueDivisible_of_isAlgClosed (F : Type u) [Field F] [IsAlgClosed F]
    (n : ℕ) (hn : 2 ≤ n) (m : ℕ) (hm : 0 < m) :
    Function.Bijective (fun x : degree F n ↦ m • x) :=
  bijective_nsmul_degree_of_splits hm (fun _ ↦ IsAlgClosed.splits _) hn

end MilnorK

end TauCeti
