/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.ZMod.Basic
public import TauCeti.NumberTheory.NumberField.Index.Basic
import Mathlib.RingTheory.Conductor
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import TauCeti.Algebra.Polynomial.MapZMod
import TauCeti.NumberTheory.NumberField.Index.Exponent

/-!
# Dedekind's criterion

Let `θ` be an integral primitive element of a number field `K`, with minimal polynomial
`f = minpoly ℤ θ`, and let `p` be a prime. Factor the reduction of `f` modulo `p` as

`f mod p = ∏ i, φ i ^ e i`,

with the `φ i` distinct monic irreducible polynomials over `ZMod p` and every `e i > 0`. Choose
lifts `Φ i : ℤ[X]` of the `φ i`. Then `f - ∏ i, Φ i ^ e i` reduces to zero modulo `p`, so it is
`p H` for an integer polynomial `H` (`exists_C_mul_eq_minpoly_sub_prod`). **Dedekind's
criterion** (`not_dvd_index_iff`) states that

`p ∤ [𝓞 K : ℤ[θ]]  ↔  ∀ i, e i = 1 ∨ ¬ φ i ∣ (H mod p)`.

The criterion decides, from `f`, `p`, the factorisation of `f mod p` and any choice of lifts,
whether `p` divides the index of the order `ℤ[θ]` in `𝓞 K`, that is, whether `ℤ[θ]` is
`p`-maximal; in particular it makes the hypothesis of the Kummer–Dedekind theorem at `p`
checkable. Its truth value does not depend on which lifts `Φ i`, and hence which `H`, are chosen
(`forall_eq_one_or_not_dvd_map_iff`).

## Main results

* `TauCeti.NumberField.IntegralPrimitiveElement.not_dvd_index_iff`: Dedekind's criterion.
* `TauCeti.NumberField.IntegralPrimitiveElement.not_dvd_index_of_forall_eq_one_or_not_dvd_map`,
  `TauCeti.NumberField.IntegralPrimitiveElement.dvd_index_of_ne_one_of_dvd_map`: its sufficient
  and its necessary direction.
* `TauCeti.NumberField.IntegralPrimitiveElement.forall_eq_one_or_not_dvd_map_iff`: the criterion
  does not depend on the lifts.
* `TauCeti.NumberField.IntegralPrimitiveElement.exists_notMem_mul_mem_adjoin`: the element of
  `ℤ[θ]` outside a prime above `p` that carries the sufficient direction.
* `TauCeti.NumberField.IntegralPrimitiveElement.exists_aeval_eq_of_mem_adjoin_of_mem`: an
  element of `ℤ[θ]` lying in a prime above `p` containing `Φ(θ)` is `Φ(θ) Q(θ) + p D(θ)`.

## References

* H. Cohen, *A Course in Computational Algebraic Number Theory*, Theorem 6.1.4.
-/

public section

open scoped NumberField
open Polynomial

namespace TauCeti.NumberField.IntegralPrimitiveElement

variable {K : Type*} [Field K] [NumberField K] {p : ℕ}

variable (θ : IntegralPrimitiveElement K)

/-- **The minimal polynomial differs from the product of the lifts by a multiple of `p`.** If
`minpoly ℤ θ` reduces to `∏ i, φ i ^ e i` modulo `p` and each `Φ i` lifts `φ i`, then
`minpoly ℤ θ - ∏ i, Φ i ^ e i` is `p` times an integer polynomial `H`. -/
theorem exists_C_mul_eq_minpoly_sub_prod {ι : Type*} [Fintype ι] {φ : ι → (ZMod p)[X]}
    {e : ι → ℕ} {Φ : ι → ℤ[X]}
    (hfact : (minpoly ℤ θ.1).map (Int.castRingHom (ZMod p)) = ∏ i, φ i ^ e i)
    (hΦ : ∀ i, (Φ i).map (Int.castRingHom (ZMod p)) = φ i) :
    ∃ H : ℤ[X], C (p : ℤ) * H = minpoly ℤ θ.1 - ∏ i, Φ i ^ e i :=
  Polynomial.exists_C_mul_eq_sub_of_map_zmod_eq (by
    rw [hfact, Polynomial.map_prod]
    simp only [Polynomial.map_pow, hΦ])

/-- Conversely, `p H = minpoly ℤ θ - ∏ i, Φ i ^ e i` recovers the factorisation of
`minpoly ℤ θ` modulo `p` from the lifts. -/
theorem map_minpoly_eq_prod_of_C_mul_eq {ι : Type*} [Fintype ι] {φ : ι → (ZMod p)[X]}
    {e : ι → ℕ} {Φ : ι → ℤ[X]} {H : ℤ[X]}
    (hΦ : ∀ i, (Φ i).map (Int.castRingHom (ZMod p)) = φ i)
    (hH : C (p : ℤ) * H = minpoly ℤ θ.1 - ∏ i, Φ i ^ e i) :
    (minpoly ℤ θ.1).map (Int.castRingHom (ZMod p)) = ∏ i, φ i ^ e i := by
  have h0 : (C (p : ℤ) * H).map (Int.castRingHom (ZMod p)) = 0 :=
    (Polynomial.map_intCastRingHom_zmod_eq_zero_iff _).mpr (by
      rw [← C_eq_natCast]; exact dvd_mul_right _ _)
  rw [hH, Polynomial.map_sub, Polynomial.map_prod] at h0
  simp only [Polynomial.map_pow, hΦ] at h0
  exact sub_eq_zero.mp h0

/-- Evaluating `C p * H = minpoly ℤ θ - ∏ i, Φ i ^ e i` at `θ`. -/
theorem natCast_mul_aeval_eq_neg_prod {ι : Type*} [Fintype ι] {e : ι → ℕ} {Φ : ι → ℤ[X]}
    {H : ℤ[X]} (hH : C (p : ℤ) * H = minpoly ℤ θ.1 - ∏ i, Φ i ^ e i) :
    (p : 𝓞 K) * aeval θ.1 H = -∏ i, aeval θ.1 (Φ i) ^ e i := by
  have := congrArg (aeval θ.1) hH
  simp only [map_mul, map_sub, minpoly.aeval, map_prod, map_pow, zero_sub, map_natCast] at this
  exact this

section Prime

variable [Fact p.Prime]

/-- An element of `ℤ[θ]` lying in a proper ideal `P` of `𝓞 K` that contains `p` and `Φ(θ)`,
where `Φ` reduces modulo `p` to an irreducible polynomial, is `Φ(θ) Q(θ) + p D(θ)` for integer
polynomials `Q`, `D`. -/
theorem exists_aeval_eq_of_mem_adjoin_of_mem {Φ : ℤ[X]}
    (hirr : Irreducible (Φ.map (Int.castRingHom (ZMod p)))) {P : Ideal (𝓞 K)} (hP : P ≠ ⊤)
    (hp : (p : 𝓞 K) ∈ P) (hΦ : aeval θ.1 Φ ∈ P) {g : 𝓞 K} (hgA : g ∈ θ.adjoin) (hgP : g ∈ P) :
    ∃ Q D : ℤ[X], g = aeval θ.1 Φ * aeval θ.1 Q + (p : 𝓞 K) * aeval θ.1 D := by
  obtain ⟨G, rfl⟩ := (θ.mem_adjoin_iff g).mp hgA
  obtain ⟨Q, D, hQD⟩ := Polynomial.exists_eq_mul_add_C_mul_of_map_zmod_dvd
    (Polynomial.map_zmod_dvd_map_of_aeval_mem θ.1 hP hp hirr hΦ hgP)
  refine ⟨Q, D, ?_⟩
  have h := congrArg (aeval θ.1) hQD
  simp only [map_add, map_mul, map_natCast] at h
  exact h

/-- Let `P` be a proper ideal of `𝓞 K` containing `p` and `a = Φ(θ)`, where `Φ` reduces modulo
`p` to an irreducible polynomial and `a ≠ 0`, and let `t, h ∈ ℤ[θ]` satisfy
`p h = -(a ^ (k + 1) t)`. If `a ^ m t w ∈ ℤ[θ]`, then `t h ^ m w ∈ ℤ[θ]`. -/
private theorem mul_pow_mul_mem_adjoin_of_pow_mul_mul_mem {Φ : ℤ[X]}
    (hirr : Irreducible (Φ.map (Int.castRingHom (ZMod p)))) {P : Ideal (𝓞 K)} (hP : P ≠ ⊤)
    (hp : (p : 𝓞 K) ∈ P) (hi : aeval θ.1 Φ ∈ P) (ha0 : aeval θ.1 Φ ≠ 0) {t h : 𝓞 K}
    (htA : t ∈ θ.adjoin) (hhA : h ∈ θ.adjoin) {k : ℕ}
    (hph : (p : 𝓞 K) * h = -(aeval θ.1 Φ ^ (k + 1) * t)) (m : ℕ) (w : 𝓞 K)
    (hw : aeval θ.1 Φ ^ m * t * w ∈ θ.adjoin) : t * h ^ m * w ∈ θ.adjoin := by
  induction m generalizing w with
  | zero => simpa using hw
  | succ m ih =>
    have hwP : aeval θ.1 Φ ^ (m + 1) * t * w ∈ P :=
      P.mul_mem_right _ (P.mul_mem_right _ (P.pow_mem_of_mem hi _ m.succ_pos))
    obtain ⟨Q, D, hQD⟩ := θ.exists_aeval_eq_of_mem_adjoin_of_mem hirr hP hp hi hw hwP
    have key : aeval θ.1 Φ * (aeval θ.1 Φ ^ m * t * (h * w)) =
        aeval θ.1 Φ * (h * aeval θ.1 Q - aeval θ.1 Φ ^ k * t * aeval θ.1 D) := by
      linear_combination h * hQD + aeval θ.1 D * hph
    have hw' := ih (h * w) (by
      rw [mul_left_cancel₀ ha0 key]
      exact θ.adjoin.sub_mem (θ.adjoin.mul_mem hhA (θ.aeval_mem_adjoin _))
        (θ.adjoin.mul_mem (θ.adjoin.mul_mem (θ.adjoin.pow_mem (θ.aeval_mem_adjoin _) _) htA)
          (θ.aeval_mem_adjoin _)))
    convert hw' using 1
    ring

omit [Fact p.Prime] in
/-- Let `p ≠ 0`, let `g, q, d ∈ ℤ[θ]` and `a, h ∈ 𝓞 K`, and let `β ∈ K` satisfy `p β = a g` and
`a β = -h`, where `h = a q + p d`. Then `β` is an algebraic integer. -/
private theorem isIntegral_of_natCast_mul_eq_of_mul_eq_neg (hp : p ≠ 0) {a g h q d : 𝓞 K}
    (hg : g ∈ θ.adjoin) (hq : q ∈ θ.adjoin) (hd : d ∈ θ.adjoin) {β : K}
    (hβp : (p : K) * β = algebraMap (𝓞 K) K a * algebraMap (𝓞 K) K g)
    (hβa : algebraMap (𝓞 K) K a * β = -algebraMap (𝓞 K) K h)
    (hh : h = a * q + (p : 𝓞 K) * d) : IsIntegral ℤ β := by
  have hp0 : (p : K) ≠ 0 := Nat.cast_ne_zero.mpr hp
  have hh' := congrArg (algebraMap (𝓞 K) K) hh
  simp only [map_mul, map_add, map_natCast] at hh'
  let N₀ : Submodule ℤ (𝓞 K) := θ.adjoin.toSubmodule.map (LinearMap.mulLeft ℤ (p : 𝓞 K)) ⊔
    θ.adjoin.toSubmodule.map (LinearMap.mulLeft ℤ a)
  let ι' : 𝓞 K →ₗ[ℤ] K := (Algebra.linearMap (𝓞 K) K).restrictScalars ℤ
  refine isIntegral_of_smul_mem_submodule (N₀.map ι') ?_
    ((IsNoetherian.noetherian N₀).map ι') β ?_
  · intro hbot
    have hmem : ι' (LinearMap.mulLeft ℤ (p : 𝓞 K) 1) ∈ N₀.map ι' :=
      Submodule.mem_map_of_mem (Submodule.mem_sup_left (Submodule.mem_map_of_mem
        ((Subalgebra.mem_toSubmodule _).mpr θ.adjoin.one_mem)))
    rw [hbot, Submodule.mem_bot] at hmem
    simp only [ι', LinearMap.restrictScalars_apply, Algebra.linearMap_apply,
      LinearMap.mulLeft_apply, mul_one, map_natCast] at hmem
    exact hp0 hmem
  · rintro n ⟨y, hy, rfl⟩
    obtain ⟨y₁, hy₁, y₂, hy₂, rfl⟩ := Submodule.mem_sup.mp hy
    obtain ⟨a', ha', rfl⟩ := hy₁
    obtain ⟨b, hb, rfl⟩ := hy₂
    have ha' : a' ∈ θ.adjoin := (Subalgebra.mem_toSubmodule _).mp ha'
    have hb : b ∈ θ.adjoin := (Subalgebra.mem_toSubmodule _).mp hb
    refine ⟨a * (g * a' - q * b) + (p : 𝓞 K) * (-(d * b)), ?_, ?_⟩
    · refine Submodule.mem_sup.mpr ⟨(p : 𝓞 K) * (-(d * b)), ?_, a * (g * a' - q * b), ?_,
        add_comm _ _⟩
      · exact Submodule.mem_map_of_mem ((Subalgebra.mem_toSubmodule _).mpr
          (θ.adjoin.neg_mem (θ.adjoin.mul_mem hd hb)))
      · exact Submodule.mem_map_of_mem ((Subalgebra.mem_toSubmodule _).mpr
          (θ.adjoin.sub_mem (θ.adjoin.mul_mem hg ha') (θ.adjoin.mul_mem hq hb)))
    · simp only [ι', LinearMap.restrictScalars_apply, Algebra.linearMap_apply,
        LinearMap.mulLeft_apply, smul_eq_mul, map_add, map_mul, map_sub, map_neg, map_natCast]
      linear_combination -(algebraMap (𝓞 K) K a') * hβp - (algebraMap (𝓞 K) K b) * hβa +
        (algebraMap (𝓞 K) K b) * hh'

/-- Let `Φ` reduce modulo `p` to an irreducible polynomial `φ`, and let `minpoly ℤ θ` reduce to
`φ * (φ * ψ)` with `ψ` the reduction of `G₁`. Then no `β ∈ 𝓞 K` with `p β = Φ(θ) G₁(θ)` lies in
`ℤ[θ]`. -/
private theorem notMem_adjoin_of_natCast_mul_eq {Φ G₁ : ℤ[X]}
    (hirr : Irreducible (Φ.map (Int.castRingHom (ZMod p))))
    (hf : (minpoly ℤ θ.1).map (Int.castRingHom (ZMod p)) =
      Φ.map (Int.castRingHom (ZMod p)) *
        (Φ.map (Int.castRingHom (ZMod p)) * G₁.map (Int.castRingHom (ZMod p))))
    {β : 𝓞 K} (hβ : (p : 𝓞 K) * β = aeval θ.1 Φ * aeval θ.1 G₁) : β ∉ θ.adjoin := by
  intro hmem
  obtain ⟨B, hB⟩ := (θ.mem_adjoin_iff β).mp hmem
  have hGB : aeval θ.1 (Φ * G₁ - C (p : ℤ) * B) = 0 := by
    simp only [map_sub, map_mul, map_natCast, hB, hβ, sub_self]
  have hdvd := Polynomial.map_dvd (Int.castRingHom (ZMod p))
    (minpoly.isIntegrallyClosed_dvd θ.1.isIntegral hGB)
  have hzero : (C (p : ℤ) * B).map (Int.castRingHom (ZMod p)) = 0 := by
    rw [Polynomial.map_intCastRingHom_zmod_eq_zero_iff, ← C_eq_natCast]
    exact dvd_mul_right _ _
  rw [Polynomial.map_sub, hzero, sub_zero, Polynomial.map_mul] at hdvd
  have hf0 : (minpoly ℤ θ.1).map (Int.castRingHom (ZMod p)) ≠ 0 :=
    ((minpoly.monic θ.1.isIntegral).map _).ne_zero
  have hG0 : Φ.map (Int.castRingHom (ZMod p)) * G₁.map (Int.castRingHom (ZMod p)) ≠ 0 :=
    right_ne_zero_of_mul (hf ▸ hf0)
  have hdeg := Polynomial.natDegree_le_of_dvd hdvd hG0
  rw [hf, Polynomial.natDegree_mul hirr.ne_zero hG0] at hdeg
  have hpos : 0 < (Φ.map (Int.castRingHom (ZMod p))).natDegree :=
    Polynomial.natDegree_pos_iff_degree_pos.mpr (degree_pos_of_irreducible hirr)
  omega

section Criterion

variable {ι : Type*} [Fintype ι] {φ : ι → (ZMod p)[X]} {e : ι → ℕ} {Φ : ι → ℤ[X]} {H : ℤ[X]}

/- The proof of the criterion, in outline. Write `A = ℤ[θ]` and `𝔣` for its conductor.

* Suppose `p` divides the index. Then `𝔣 + p 𝓞 K` is a proper ideal
  (`not_dvd_index_of_conductor_sup_span_eq_top`); let `P` be a maximal ideal containing it. `P`
  contains `Φ i (θ)` for some `i`, and the right-hand side at `i` produces `σ ∈ A` outside `P`
  with `σ z ∈ A` whenever `p z ∈ A` (`exists_notMem_mul_mem_adjoin`): for `e i = 1` take
  `σ = ∏_{j ≠ i} Φ j (θ) ^ e j`, and for `φ i ∤ (H mod p)` take
  `σ = H(θ) ^ e i ∏_{j ≠ i} Φ j (θ) ^ e j`, descending along the powers of `Φ i (θ)` with the
  identity `p H(θ) = -∏ j, Φ j (θ) ^ e j` (`mul_pow_mul_mem_adjoin_of_pow_mul_mul_mem`).
  Iterating, a power of `σ` times the `p`-free part of the index lies in `𝔣 ⊆ P`, a
  contradiction (`not_dvd_index_of_forall_eq_one_or_not_dvd_map`).
* If `e i ≥ 2` and `φ i ∣ (H mod p)`, then `β = Φ i (θ) ^ (e i - 1) ∏_{j ≠ i} Φ j (θ) ^ e j / p`
  is an algebraic integer (`isIntegral_of_natCast_mul_eq_of_mul_eq_neg`) that is not in `A`
  (`notMem_adjoin_of_natCast_mul_eq`). So `β` has order `p` in `𝓞 K / A`, and `p` divides the
  index (`dvd_index_of_ne_one_of_dvd_map`). -/

/-- **The key step of Dedekind's criterion.** Let `P` be a prime of `𝓞 K` containing `p` and
`Φ i (θ)`. If `e i = 1`, or if `φ i` does not divide the reduction of `H`, then there is
`σ ∈ ℤ[θ]` outside `P` such that `σ z ∈ ℤ[θ]` whenever `p z ∈ ℤ[θ]`. -/
theorem exists_notMem_mul_mem_adjoin (hφ : ∀ i, Irreducible (φ i)) (hφm : ∀ i, (φ i).Monic)
    (hinj : Function.Injective φ) (hΦ : ∀ i, (Φ i).map (Int.castRingHom (ZMod p)) = φ i)
    (hH : C (p : ℤ) * H = minpoly ℤ θ.1 - ∏ i, Φ i ^ e i)
    {P : Ideal (𝓞 K)} [P.IsPrime] (hp : (p : 𝓞 K) ∈ P) {i : ι} (he : 0 < e i)
    (hi : aeval θ.1 (Φ i) ∈ P) (hcrit : e i = 1 ∨ ¬ φ i ∣ H.map (Int.castRingHom (ZMod p))) :
    ∃ σ ∈ θ.adjoin, σ ∉ P ∧ ∀ z : 𝓞 K, (p : 𝓞 K) * z ∈ θ.adjoin → σ * z ∈ θ.adjoin := by
  classical
  have hPtop : P ≠ ⊤ := Ideal.IsPrime.ne_top inferInstance
  have hp0 : (p : 𝓞 K) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  have hirr : Irreducible ((Φ i).map (Int.castRingHom (ZMod p))) := hΦ i ▸ hφ i
  have hprod := θ.natCast_mul_aeval_eq_neg_prod hH
  set ai := aeval θ.1 (Φ i) with hai
  set Hθ := aeval θ.1 H with hHθ
  set t := ∏ j ∈ Finset.univ.erase i, aeval θ.1 (Φ j) ^ e j with ht
  have hsplit : ∏ j, aeval θ.1 (Φ j) ^ e j = ai ^ e i * t :=
    (Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)).symm
  have htA : t ∈ θ.adjoin :=
    Subalgebra.prod_mem _ fun j _ => Subalgebra.pow_mem _ (θ.aeval_mem_adjoin _) _
  have htP : t ∉ P := by
    intro htP
    obtain ⟨j, hj, hjP⟩ := Ideal.IsPrime.prod_mem_iff.mp htP
    have hjP' : aeval θ.1 (Φ j) ∈ P := Ideal.IsPrime.mem_of_pow_mem inferInstance _ hjP
    have hdvd := Polynomial.map_zmod_dvd_map_of_aeval_mem θ.1 hPtop hp hirr hi hjP'
    rw [hΦ i, hΦ j] at hdvd
    exact (Finset.mem_erase.mp hj).1 (hinj (eq_of_monic_of_associated (hφm i) (hφm j)
      ((hφ i).associated_of_dvd (hφ j) hdvd))).symm
  rcases hcrit with h1 | hnd
  · -- `e i = 1`: multiply by `t`.
    refine ⟨t, htA, htP, fun z hz => ?_⟩
    obtain ⟨Q, D, hQD⟩ :=
      θ.exists_aeval_eq_of_mem_adjoin_of_mem hirr hPtop hp hi hz (P.mul_mem_right z hp)
    have key : (p : 𝓞 K) * (t * z) =
        (p : 𝓞 K) * (-(Hθ * aeval θ.1 Q) + t * aeval θ.1 D) := by
      rw [h1, pow_one] at hsplit
      linear_combination t * hQD + aeval θ.1 Q * hprod - aeval θ.1 Q * hsplit
    rw [mul_left_cancel₀ hp0 key]
    exact θ.adjoin.add_mem (θ.adjoin.neg_mem (θ.adjoin.mul_mem (θ.aeval_mem_adjoin _)
      (θ.aeval_mem_adjoin _))) (θ.adjoin.mul_mem htA (θ.aeval_mem_adjoin _))
  · -- `φ i ∤ (H mod p)`: `H(θ)` is a unit modulo `P`, and `p H(θ) = -Φ i (θ) ^ e i * t`.
    have hHP : Hθ ∉ P := fun h =>
      hnd (hΦ i ▸ Polynomial.map_zmod_dvd_map_of_aeval_mem θ.1 hPtop hp hirr hi h)
    have hpH : (p : 𝓞 K) * Hθ = -(ai ^ e i * t) := by rw [hprod, hsplit]
    obtain ⟨k, hk⟩ : ∃ k, e i = k + 1 := ⟨e i - 1, by omega⟩
    have hai0 : ai ≠ 0 := by
      intro h0
      rw [h0, hk, zero_pow k.succ_ne_zero, zero_mul, neg_zero] at hpH
      exact hHP ((mul_eq_zero.mp hpH).resolve_left hp0 ▸ P.zero_mem)
    refine ⟨t * Hθ ^ e i, θ.adjoin.mul_mem htA (θ.adjoin.pow_mem (θ.aeval_mem_adjoin _) _),
      fun h => ?_, fun z hz => ?_⟩
    · rcases Ideal.IsPrime.mem_or_mem inferInstance h with h | h
      · exact htP h
      · exact hHP (Ideal.IsPrime.mem_of_pow_mem inferInstance _ h)
    · rw [hk] at hpH
      apply θ.mul_pow_mul_mem_adjoin_of_pow_mul_mul_mem hirr hPtop hp hi hai0 htA
        (θ.aeval_mem_adjoin H) hpH (e i) z
      have : ai ^ e i * t * z = -(Hθ * ((p : 𝓞 K) * z)) := by
        rw [hk]
        linear_combination z * hpH
      rw [this]
      exact θ.adjoin.neg_mem (θ.adjoin.mul_mem (θ.aeval_mem_adjoin _) hz)

/-- **Dedekind's criterion, the sufficient direction.** If for every `i` either `e i = 1` or
`φ i` does not divide the reduction of `H`, then `p` does not divide the index `[𝓞 K : ℤ[θ]]`. -/
theorem not_dvd_index_of_forall_eq_one_or_not_dvd_map (hφ : ∀ i, Irreducible (φ i))
    (hφm : ∀ i, (φ i).Monic) (hinj : Function.Injective φ) (he : ∀ i, 0 < e i)
    (hΦ : ∀ i, (Φ i).map (Int.castRingHom (ZMod p)) = φ i)
    (hH : C (p : ℤ) * H = minpoly ℤ θ.1 - ∏ i, Φ i ^ e i)
    (hcrit : ∀ i, e i = 1 ∨ ¬ φ i ∣ H.map (Int.castRingHom (ZMod p))) : ¬ p ∣ θ.index := by
  classical
  have hprod := θ.natCast_mul_aeval_eq_neg_prod hH
  intro hdvd
  have hne : conductor ℤ θ.1 ⊔ Ideal.span {(p : 𝓞 K)} ≠ ⊤ := fun h =>
    θ.not_dvd_index_of_conductor_sup_span_eq_top (Fact.out : p.Prime).ne_one h hdvd
  obtain ⟨P, hPmax, hle⟩ := Ideal.exists_le_maximal _ hne
  have : P.IsPrime := hPmax.isPrime
  have hp : (p : 𝓞 K) ∈ P := hle (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
  have hcond : conductor ℤ θ.1 ≤ P := le_sup_left.trans hle
  have hprodmem : ∏ j, aeval θ.1 (Φ j) ^ e j ∈ P := by
    rw [← neg_mem_iff, ← hprod]
    exact P.mul_mem_right _ hp
  obtain ⟨i, -, hi⟩ := Ideal.IsPrime.prod_mem_iff.mp hprodmem
  have hi : aeval θ.1 (Φ i) ∈ P := Ideal.IsPrime.mem_of_pow_mem inferInstance _ hi
  obtain ⟨σ, hσA, hσP, hσ⟩ :=
    θ.exists_notMem_mul_mem_adjoin hφ hφm hinj hΦ hH hp (he i) hi (hcrit i)
  have hiter : ∀ k (z : 𝓞 K), (p : 𝓞 K) ^ k * z ∈ θ.adjoin → σ ^ k * z ∈ θ.adjoin := by
    intro k
    induction k with
    | zero => intro z hz; simpa using hz
    | succ k ih =>
      intro z hz
      have h1 : (p : 𝓞 K) * ((p : 𝓞 K) ^ k * z) ∈ θ.adjoin := by
        rw [← mul_assoc, ← pow_succ']
        exact hz
      have h2 : (p : 𝓞 K) ^ k * (σ * z) ∈ θ.adjoin := by
        rw [mul_left_comm]
        exact hσ _ h1
      rw [pow_succ, mul_assoc]
      exact ih _ h2
  obtain ⟨k, N, hN, hkN⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd θ.index_pos.ne' p (Fact.out : p.Prime).ne_one
  have hindex : ∀ x : 𝓞 K, (θ.index : 𝓞 K) * x ∈ θ.adjoin := fun x => by
    rw [adjoin_def]
    exact mem_conductor_iff.mp ((RingOfIntegers.exponent_dvd_iff θ.1).mp θ.exponent_dvd_index) x
  have hσN : σ ^ k * (N : 𝓞 K) ∈ conductor ℤ θ.1 := by
    rw [mem_conductor_iff]
    intro x
    rw [← adjoin_def, mul_assoc]
    apply hiter k
    have := hindex x
    rw [hkN, Nat.cast_mul, Nat.cast_pow, mul_assoc] at this
    exact this
  rcases Ideal.IsPrime.mem_or_mem inferInstance (hcond hσN) with h | h
  · exact hσP (Ideal.IsPrime.mem_of_pow_mem inferInstance _ h)
  · obtain ⟨a, b, hab⟩ :=
      Nat.isCoprime_iff_coprime.mpr ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hN)
    apply hPmax.ne_top
    rw [Ideal.eq_top_iff_one]
    have h1 : (1 : 𝓞 K) = a * (p : 𝓞 K) + b * (N : 𝓞 K) := by
      have := congrArg (Int.cast : ℤ → 𝓞 K) hab
      push_cast at this
      exact this.symm
    rw [h1]
    exact P.add_mem (P.mul_mem_left _ hp) (P.mul_mem_left _ h)

/-- **Dedekind's criterion, the necessary direction.** If `e i ≥ 2` and `φ i` divides the
reduction of `H` for some `i`, then `p` divides the index `[𝓞 K : ℤ[θ]]`. -/
theorem dvd_index_of_ne_one_of_dvd_map (i : ι) (hφi : Irreducible (φ i))
    (hΦ : ∀ i, (Φ i).map (Int.castRingHom (ZMod p)) = φ i)
    (hH : C (p : ℤ) * H = minpoly ℤ θ.1 - ∏ i, Φ i ^ e i) (h1 : e i ≠ 1)
    (he : 0 < e i) (hdvd : φ i ∣ H.map (Int.castRingHom (ZMod p))) : p ∣ θ.index := by
  classical
  have hp0 : (p : K) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  have hprod := θ.natCast_mul_aeval_eq_neg_prod hH
  obtain ⟨m, hm⟩ : ∃ m, e i = m + 2 := ⟨e i - 2, by omega⟩
  set G₁ : ℤ[X] := Φ i ^ m * ∏ j ∈ Finset.univ.erase i, Φ j ^ e j with hG₁
  have hΦG : Φ i * (Φ i * G₁) = ∏ j, Φ j ^ e j := by
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i), hm, hG₁]
    ring
  have hφG : (minpoly ℤ θ.1).map (Int.castRingHom (ZMod p)) =
      (Φ i).map (Int.castRingHom (ZMod p)) *
        ((Φ i).map (Int.castRingHom (ZMod p)) * G₁.map (Int.castRingHom (ZMod p))) := by
    rw [← Polynomial.map_mul, ← Polynomial.map_mul, hΦG, θ.map_minpoly_eq_prod_of_C_mul_eq hΦ hH,
      Polynomial.map_prod]
    simp only [Polynomial.map_pow, hΦ]
  set ai := aeval θ.1 (Φ i) with hai
  set g₁ := aeval θ.1 G₁ with hg₁
  set Hθ := aeval θ.1 H with hHθ
  have hag : ai * (ai * g₁) = -((p : 𝓞 K) * Hθ) := by
    rw [hprod, hai, hg₁, ← map_mul, ← map_mul, hΦG, map_prod]
    simp only [map_pow, neg_neg]
  obtain ⟨Q, D, hHQ⟩ := Polynomial.exists_eq_mul_add_C_mul_of_map_zmod_dvd (Φ := Φ i) (G := H)
    (by rw [hΦ i]; exact hdvd)
  have hHQ' : Hθ = ai * aeval θ.1 Q + (p : 𝓞 K) * aeval θ.1 D := by
    have h := congrArg (aeval θ.1) hHQ
    simp only [map_add, map_mul, map_natCast] at h
    exact h
  -- The candidate `β = Φ i (θ) g₁ / p`, an algebraic integer that is not in `ℤ[θ]`.
  obtain ⟨β, hβ⟩ : ∃ β : K, β = algebraMap (𝓞 K) K (ai * g₁) / (p : K) := ⟨_, rfl⟩
  have hβp : (p : K) * β = algebraMap (𝓞 K) K ai * algebraMap (𝓞 K) K g₁ := by
    rw [hβ, map_mul]
    field_simp
  have hag' := congrArg (algebraMap (𝓞 K) K) hag
  simp only [map_mul, map_neg, map_natCast] at hag'
  have hβai : algebraMap (𝓞 K) K ai * β = -algebraMap (𝓞 K) K Hθ := by
    apply mul_left_cancel₀ hp0
    rw [mul_left_comm, hβp]
    linear_combination hag'
  have hβint : IsIntegral ℤ β := θ.isIntegral_of_natCast_mul_eq_of_mul_eq_neg
    (Fact.out : p.Prime).ne_zero (θ.aeval_mem_adjoin G₁) (θ.aeval_mem_adjoin Q)
    (θ.aeval_mem_adjoin D) hβp hβai hHQ'
  set βₒ : 𝓞 K := ⟨β, hβint⟩ with hβₒ
  have hpβ : (p : 𝓞 K) * βₒ = ai * g₁ := by
    apply NumberField.RingOfIntegers.ext
    simp only [map_mul, map_natCast]
    exact hβp
  have hβA : βₒ ∉ θ.adjoin := θ.notMem_adjoin_of_natCast_mul_eq (hΦ i ▸ hφi) hφG hpβ
  have hq0 : θ.adjoin.toSubmodule.mkQ βₒ ≠ 0 := by
    rw [Ne, mkQ_eq_zero_iff]
    exact hβA
  have hpq : p • θ.adjoin.toSubmodule.mkQ βₒ = 0 := by
    rw [nsmul_mkQ_eq_zero_iff, hpβ]
    exact θ.adjoin.mul_mem (θ.aeval_mem_adjoin _) (θ.aeval_mem_adjoin _)
  rw [index_def, ← addOrderOf_eq_prime hpq hq0]
  exact addOrderOf_dvd_natCard _

/-- **Dedekind's criterion.** Let `θ` be an integral primitive element of `K` with minimal
polynomial `f = minpoly ℤ θ`, let `p` be a prime, and factor `f mod p = ∏ i, φ i ^ e i` into
distinct monic irreducible polynomials `φ i` over `ZMod p`, each with multiplicity `e i > 0`.
Choose lifts `Φ i : ℤ[X]` of the `φ i` and let `H : ℤ[X]` satisfy `p H = f - ∏ i, Φ i ^ e i`
(which records the factorisation, by `map_minpoly_eq_prod_of_C_mul_eq`). Then `p` does not
divide the index `[𝓞 K : ℤ[θ]]` if and only if, for every `i`, either `e i = 1` or `φ i` does
not divide `H mod p`. -/
theorem not_dvd_index_iff (hφ : ∀ i, Irreducible (φ i)) (hφm : ∀ i, (φ i).Monic)
    (hinj : Function.Injective φ) (he : ∀ i, 0 < e i)
    (hΦ : ∀ i, (Φ i).map (Int.castRingHom (ZMod p)) = φ i)
    (hH : C (p : ℤ) * H = minpoly ℤ θ.1 - ∏ i, Φ i ^ e i) :
    ¬ p ∣ θ.index ↔ ∀ i, e i = 1 ∨ ¬ φ i ∣ H.map (Int.castRingHom (ZMod p)) := by
  refine ⟨fun h i => ?_, θ.not_dvd_index_of_forall_eq_one_or_not_dvd_map hφ hφm hinj he hΦ hH⟩
  by_contra hcon
  rw [not_or, not_not] at hcon
  exact h (θ.dvd_index_of_ne_one_of_dvd_map i (hφ i) hΦ hH hcon.1 (he i) hcon.2)

/-- The right-hand side of Dedekind's criterion does not depend on the choice of the lifts
`Φ i` of the `φ i`, nor on the resulting `H`. -/
theorem forall_eq_one_or_not_dvd_map_iff (hφ : ∀ i, Irreducible (φ i))
    (hφm : ∀ i, (φ i).Monic) (hinj : Function.Injective φ) (he : ∀ i, 0 < e i)
    {Φ' : ι → ℤ[X]} {H' : ℤ[X]}
    (hΦ : ∀ i, (Φ i).map (Int.castRingHom (ZMod p)) = φ i)
    (hH : C (p : ℤ) * H = minpoly ℤ θ.1 - ∏ i, Φ i ^ e i)
    (hΦ' : ∀ i, (Φ' i).map (Int.castRingHom (ZMod p)) = φ i)
    (hH' : C (p : ℤ) * H' = minpoly ℤ θ.1 - ∏ i, Φ' i ^ e i) :
    (∀ i, e i = 1 ∨ ¬ φ i ∣ H.map (Int.castRingHom (ZMod p))) ↔
      ∀ i, e i = 1 ∨ ¬ φ i ∣ H'.map (Int.castRingHom (ZMod p)) := by
  rw [← θ.not_dvd_index_iff hφ hφm hinj he hΦ hH, ← θ.not_dvd_index_iff hφ hφm hinj he hΦ' hH']

end Criterion

end Prime

end TauCeti.NumberField.IntegralPrimitiveElement
