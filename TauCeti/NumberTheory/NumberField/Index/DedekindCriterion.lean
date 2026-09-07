/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.RingTheory.Conductor
public import TauCeti.NumberTheory.NumberField.Index.Basic
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.PrincipalIdealDomain
import TauCeti.Algebra.Polynomial.MapZMod

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

The proof is elementary and takes place inside `𝓞 K`. Write `A = ℤ[θ]` and `𝔣` for its
conductor.

* Suppose `p` divides the index. Then `𝔣 + p 𝓞 K` is a proper ideal, since otherwise
  multiplication by `p` would be bijective on the finite group `𝓞 K / A`; let `P` be a maximal
  ideal containing it. `P` contains `Φ i (θ)` for some `i`, and the right-hand side at `i`
  produces `σ ∈ A` outside `P` with `σ z ∈ A` whenever `p z ∈ A`
  (`exists_notMem_mul_mem_adjoin`): for `e i = 1` take `σ = ∏_{j ≠ i} Φ j (θ) ^ e j`, and for
  `φ i ∤ H̄` take `σ = H(θ) ^ e i ∏_{j ≠ i} Φ j (θ) ^ e j`, descending along the powers of
  `Φ i (θ)` with the identity `p H(θ) = -∏ j, Φ j (θ) ^ e j`. Iterating, a power of `σ` times the
  `p`-free part of the index lies in `𝔣 ⊆ P`, a contradiction (`not_dvd_index_of_forall`).
* If `e i ≥ 2` and `φ i ∣ H̄`, then `β = Φ i (θ) ^ (e i - 1) ∏_{j ≠ i} Φ j (θ) ^ e j / p` is an
  algebraic integer, because it preserves the finitely generated `ℤ`-submodule
  `p A + Φ i (θ) A` of `K`. It is not in `A`, since otherwise `f mod p` would divide a nonzero
  polynomial of smaller degree. So `β` has order `p` in `𝓞 K / A`, and `p` divides the index
  (`dvd_index_of_ne_one_of_dvd`).

In particular the right-hand side of the criterion does not depend on the choice of the lifts
(`forall_eq_one_or_not_dvd_map_iff`).

## Main results

* `TauCeti.NumberField.IntegralPrimitiveElement.exists_C_mul_eq_minpoly_sub_prod`: the
  polynomial `H` exists.
* `TauCeti.NumberField.IntegralPrimitiveElement.not_dvd_index_iff`: Dedekind's criterion.
* `TauCeti.NumberField.IntegralPrimitiveElement.forall_eq_one_or_not_dvd_map_iff`: the
  criterion does not depend on the lifts.

## References

* H. Cohen, *A Course in Computational Algebraic Number Theory*, Theorem 6.1.4.
-/

public section

open scoped NumberField
open Polynomial

namespace TauCeti.NumberField.IntegralPrimitiveElement

variable {K : Type*} [Field K] [NumberField K] {p : ℕ}

variable (θ : IntegralPrimitiveElement K)

/-- **The reductions of the lifts multiply to the reduction of the minimal polynomial.** If
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

/-- Evaluating `C p * H = minpoly ℤ θ - ∏ i, Φ i ^ e i` at `θ`. -/
theorem natCast_mul_aeval_eq_neg_prod {ι : Type*} [Fintype ι] {e : ι → ℕ} {Φ : ι → ℤ[X]}
    {H : ℤ[X]} (hH : C (p : ℤ) * H = minpoly ℤ θ.1 - ∏ i, Φ i ^ e i) :
    (p : 𝓞 K) * aeval θ.1 H = -∏ i, aeval θ.1 (Φ i) ^ e i := by
  have := congrArg (aeval θ.1) hH
  simp only [map_mul, map_sub, minpoly.aeval, map_prod, map_pow, zero_sub, map_natCast] at this
  exact this

section Prime

variable [Fact p.Prime]

/-- If `G(θ)` lies in a proper ideal `P` of `𝓞 K` containing `p` and `Φ(θ)`, where `Φ` reduces
modulo `p` to an irreducible polynomial, then that irreducible polynomial divides the reduction
of `G`. -/
theorem map_dvd_map_of_aeval_mem {P : Ideal (𝓞 K)} (hP : P ≠ ⊤) (hp : (p : 𝓞 K) ∈ P)
    {Φ G : ℤ[X]} (hirr : Irreducible (Φ.map (Int.castRingHom (ZMod p))))
    (hΦ : aeval θ.1 Φ ∈ P) (hG : aeval θ.1 G ∈ P) :
    Φ.map (Int.castRingHom (ZMod p)) ∣ G.map (Int.castRingHom (ZMod p)) := by
  by_contra hndvd
  obtain ⟨a, b, hab⟩ := hirr.coprime_iff_not_dvd.mpr hndvd
  obtain ⟨A, rfl⟩ := Polynomial.map_surjective (Int.castRingHom (ZMod p)) ZMod.intCast_surjective a
  obtain ⟨B, rfl⟩ := Polynomial.map_surjective (Int.castRingHom (ZMod p)) ZMod.intCast_surjective b
  obtain ⟨D, hD⟩ := Polynomial.exists_C_mul_eq_sub_of_map_zmod_eq (n := p) (G := A * Φ + B * G)
    (G' := 1) (by
    rw [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_mul, Polynomial.map_one, hab])
  apply hP
  rw [Ideal.eq_top_iff_one]
  have h1 := congrArg (aeval θ.1) hD
  simp only [map_mul, map_add, map_sub, map_one, map_natCast] at h1
  have : (1 : 𝓞 K) = aeval θ.1 A * aeval θ.1 Φ + aeval θ.1 B * aeval θ.1 G -
      (p : 𝓞 K) * aeval θ.1 D := by rw [h1]; ring
  rw [this]
  exact P.sub_mem (P.add_mem (P.mul_mem_left _ hΦ) (P.mul_mem_left _ hG)) (P.mul_mem_right _ hp)

/-- Conversely, if the reduction of `Φ` divides the reduction of `G`, then `G(θ)` lies in the
`ℤ[θ]`-ideal generated by `p` and `Φ(θ)`: `G(θ) = Φ(θ) Q(θ) + p C(θ)` for integer polynomials
`Q`, `C`. -/
theorem exists_aeval_eq_of_map_dvd_map {Φ G : ℤ[X]}
    (h : Φ.map (Int.castRingHom (ZMod p)) ∣ G.map (Int.castRingHom (ZMod p))) :
    ∃ Q D : ℤ[X], aeval θ.1 G = aeval θ.1 Φ * aeval θ.1 Q + (p : 𝓞 K) * aeval θ.1 D := by
  obtain ⟨q, hq⟩ := h
  obtain ⟨Q, rfl⟩ := Polynomial.map_surjective (Int.castRingHom (ZMod p)) ZMod.intCast_surjective q
  obtain ⟨D, hD⟩ := Polynomial.exists_C_mul_eq_sub_of_map_zmod_eq (n := p) (G := G)
    (G' := Φ * Q) (by
    rw [Polynomial.map_mul, hq])
  refine ⟨Q, D, ?_⟩
  have h1 := congrArg (aeval θ.1) hD
  simp only [map_mul, map_sub, map_natCast] at h1
  rw [← sub_eq_iff_eq_add'.mp h1.symm]

/-- If the conductor of `ℤ[θ]` in `𝓞 K` is coprime to `p`, then `p` does not divide the index:
multiplication by `p` is then surjective, hence bijective, on the finite group `𝓞 K / ℤ[θ]`,
which therefore has no element of order `p`. -/
theorem not_dvd_index_of_conductor_sup_span_eq_top
    (h : conductor ℤ θ.1 ⊔ Ideal.span {(p : 𝓞 K)} = ⊤) : ¬ p ∣ θ.index := by
  classical
  have : Fintype θ.Quotient := Fintype.ofFinite _
  intro hp
  rw [index_def, Nat.card_eq_fintype_card] at hp
  obtain ⟨x, hx⟩ := exists_prime_addOrderOf_dvd_card p hp
  have hsurj : Function.Surjective (fun y : θ.Quotient => p • y) := by
    have h1 : (1 : 𝓞 K) ∈ conductor ℤ θ.1 ⊔ Ideal.span {(p : 𝓞 K)} := h ▸ Submodule.mem_top
    obtain ⟨c, hc, m, hm, hcm⟩ := Submodule.mem_sup.mp h1
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hm
    intro y
    obtain ⟨b, rfl⟩ := Submodule.mkQ_surjective _ y
    refine ⟨θ.adjoin.toSubmodule.mkQ (a * b), ?_⟩
    change p • θ.adjoin.toSubmodule.mkQ (a * b) = θ.adjoin.toSubmodule.mkQ b
    have hb : b = c * b + (p : 𝓞 K) * (a * b) := by
      calc b = (c + a * (p : 𝓞 K)) * b := by rw [hcm, one_mul]
        _ = c * b + (p : 𝓞 K) * (a * b) := by ring
    have hcb : θ.adjoin.toSubmodule.mkQ (c * b) = 0 := by
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Subalgebra.mem_toSubmodule,
        adjoin_def]
      exact mem_conductor_iff.mp hc b
    conv_rhs => rw [hb]
    rw [map_add, hcb, zero_add, ← map_nsmul, nsmul_eq_mul]
  have hinj := Finite.injective_iff_surjective.mpr hsurj
  have hx0 : x = 0 := hinj (by
    change p • x = p • (0 : θ.Quotient)
    rw [smul_zero, ← hx, addOrderOf_nsmul_eq_zero])
  rw [hx0, addOrderOf_zero] at hx
  exact (Fact.out : p.Prime).one_lt.ne hx

/-- Every polynomial expression in `θ` lies in `ℤ[θ]`. -/
theorem aeval_mem_adjoin (G : ℤ[X]) : aeval θ.1 G ∈ θ.adjoin := by
  rw [adjoin_def]
  exact Polynomial.aeval_mem_adjoin_singleton ℤ θ.1

section Criterion

variable {ι : Type*} [Fintype ι] {φ : ι → (ZMod p)[X]} {e : ι → ℕ} {Φ : ι → ℤ[X]} {H : ℤ[X]}

/-- **The key step of Dedekind's criterion.** Let `P` be a prime of `𝓞 K` containing `p` and
`Φ i (θ)`. If `e i = 1`, or if `φ i` does not divide the reduction of `H`, then there is
`σ ∈ ℤ[θ]` outside `P` such that `σ z ∈ ℤ[θ]` whenever `p z ∈ ℤ[θ]`. -/
theorem exists_notMem_mul_mem_adjoin (hφ : ∀ i, Irreducible (φ i)) (hφm : ∀ i, (φ i).Monic)
    (hinj : Function.Injective φ) (he : ∀ i, 0 < e i)
    (hΦ : ∀ i, (Φ i).map (Int.castRingHom (ZMod p)) = φ i)
    (hH : C (p : ℤ) * H = minpoly ℤ θ.1 - ∏ i, Φ i ^ e i)
    {P : Ideal (𝓞 K)} [P.IsPrime] (hp : (p : 𝓞 K) ∈ P) {i : ι} (hi : aeval θ.1 (Φ i) ∈ P)
    (hcrit : e i = 1 ∨ ¬ φ i ∣ H.map (Int.castRingHom (ZMod p))) :
    ∃ σ ∈ θ.adjoin, σ ∉ P ∧ ∀ z : 𝓞 K, (p : 𝓞 K) * z ∈ θ.adjoin → σ * z ∈ θ.adjoin := by
  classical
  have hPtop : P ≠ ⊤ := Ideal.IsPrime.ne_top inferInstance
  have hp0 : (p : 𝓞 K) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
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
    have hdvd := θ.map_dvd_map_of_aeval_mem hPtop hp (hΦ i ▸ hφ i) hi hjP'
    rw [hΦ i, hΦ j] at hdvd
    exact (Finset.mem_erase.mp hj).1 (hinj (eq_of_monic_of_associated (hφm i) (hφm j)
      ((hφ i).associated_of_dvd (hφ j) hdvd))).symm
  -- an element of `ℤ[θ] ∩ P` is `Φ i (θ) Q(θ) + p D(θ)`
  have hmem : ∀ g ∈ θ.adjoin, g ∈ P →
      ∃ Q D : ℤ[X], g = ai * aeval θ.1 Q + (p : 𝓞 K) * aeval θ.1 D := by
    intro g hgA hgP
    rw [adjoin_def, Algebra.adjoin_singleton_eq_range_aeval] at hgA
    obtain ⟨G, rfl⟩ := hgA
    have hdvd := θ.map_dvd_map_of_aeval_mem hPtop hp (hΦ i ▸ hφ i) hi hgP
    exact θ.exists_aeval_eq_of_map_dvd_map hdvd
  rcases hcrit with h1 | hnd
  · -- `e i = 1`: multiply by `t`.
    refine ⟨t, htA, htP, fun z hz => ?_⟩
    obtain ⟨Q, D, hQD⟩ := hmem _ hz (P.mul_mem_right z hp)
    have key : (p : 𝓞 K) * (t * z) =
        (p : 𝓞 K) * (-(Hθ * aeval θ.1 Q) + t * aeval θ.1 D) := by
      rw [h1, pow_one] at hsplit
      linear_combination t * hQD + aeval θ.1 Q * hprod - aeval θ.1 Q * hsplit
    rw [mul_left_cancel₀ hp0 key]
    exact θ.adjoin.add_mem (θ.adjoin.neg_mem (θ.adjoin.mul_mem (θ.aeval_mem_adjoin _)
      (θ.aeval_mem_adjoin _))) (θ.adjoin.mul_mem htA (θ.aeval_mem_adjoin _))
  · -- `φ i ∤ H̄`: `H(θ)` is a unit modulo `P`, and `p H(θ) = -Φ i (θ) ^ e i * t`.
    have hHP : Hθ ∉ P := fun h =>
      hnd (hΦ i ▸ θ.map_dvd_map_of_aeval_mem hPtop hp (hΦ i ▸ hφ i) hi h)
    have hpH : (p : 𝓞 K) * Hθ = -(ai ^ e i * t) := by rw [hprod, hsplit]
    obtain ⟨k, hk⟩ : ∃ k, e i = k + 1 := ⟨e i - 1, by have := he i; omega⟩
    have hai0 : ai ≠ 0 := by
      intro h0
      rw [h0, hk, zero_pow k.succ_ne_zero, zero_mul, neg_zero] at hpH
      exact hHP ((mul_eq_zero.mp hpH).resolve_left hp0 ▸ P.zero_mem)
    -- descent on the power of `Φ i (θ)`
    have hdesc : ∀ m (w : 𝓞 K), ai ^ m * t * w ∈ θ.adjoin → t * Hθ ^ m * w ∈ θ.adjoin := by
      intro m
      induction m with
      | zero => intro w hw; simpa using hw
      | succ m ih =>
        intro w hw
        have hwP : ai ^ (m + 1) * t * w ∈ P :=
          P.mul_mem_right _ (P.mul_mem_right _ (P.pow_mem_of_mem hi _ m.succ_pos))
        obtain ⟨Q, D, hQD⟩ := hmem _ hw hwP
        have key : ai * (ai ^ m * t * (Hθ * w)) =
            ai * (Hθ * aeval θ.1 Q - ai ^ k * t * aeval θ.1 D) := by
          rw [hk] at hpH
          linear_combination Hθ * hQD + aeval θ.1 D * hpH
        have hw' := ih (Hθ * w) (by
          rw [mul_left_cancel₀ hai0 key]
          exact θ.adjoin.sub_mem (θ.adjoin.mul_mem (θ.aeval_mem_adjoin _) (θ.aeval_mem_adjoin _))
            (θ.adjoin.mul_mem (θ.adjoin.mul_mem (θ.adjoin.pow_mem (θ.aeval_mem_adjoin _) _) htA)
              (θ.aeval_mem_adjoin _)))
        rw [show t * Hθ ^ (m + 1) * w = t * Hθ ^ m * (Hθ * w) by ring]
        exact hw'
    refine ⟨t * Hθ ^ e i, θ.adjoin.mul_mem htA (θ.adjoin.pow_mem (θ.aeval_mem_adjoin _) _),
      fun h => ?_, fun z hz => ?_⟩
    · rcases Ideal.IsPrime.mem_or_mem inferInstance h with h | h
      · exact htP h
      · exact hHP (Ideal.IsPrime.mem_of_pow_mem inferInstance _ h)
    · apply hdesc (e i) z
      have : ai ^ e i * t * z = -(Hθ * ((p : 𝓞 K) * z)) := by linear_combination z * hpH
      rw [this]
      exact θ.adjoin.neg_mem (θ.adjoin.mul_mem (θ.aeval_mem_adjoin _) hz)

/-- **Dedekind's criterion, the sufficient direction.** If for every `i` either `e i = 1` or
`φ i` does not divide the reduction of `H`, then `p` does not divide the index `[𝓞 K : ℤ[θ]]`. -/
theorem not_dvd_index_of_forall (hφ : ∀ i, Irreducible (φ i)) (hφm : ∀ i, (φ i).Monic)
    (hinj : Function.Injective φ) (he : ∀ i, 0 < e i)
    (hΦ : ∀ i, (Φ i).map (Int.castRingHom (ZMod p)) = φ i)
    (hH : C (p : ℤ) * H = minpoly ℤ θ.1 - ∏ i, Φ i ^ e i)
    (hcrit : ∀ i, e i = 1 ∨ ¬ φ i ∣ H.map (Int.castRingHom (ZMod p))) : ¬ p ∣ θ.index := by
  classical
  have hprod := θ.natCast_mul_aeval_eq_neg_prod hH
  intro hdvd
  have hne : conductor ℤ θ.1 ⊔ Ideal.span {(p : 𝓞 K)} ≠ ⊤ := fun h =>
    θ.not_dvd_index_of_conductor_sup_span_eq_top h hdvd
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
    θ.exists_notMem_mul_mem_adjoin hφ hφm hinj he hΦ hH hp hi (hcrit i)
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
        rw [show (p : 𝓞 K) ^ k * (σ * z) = σ * ((p : 𝓞 K) ^ k * z) by ring]
        exact hσ _ h1
      rw [show σ ^ (k + 1) * z = σ ^ k * (σ * z) by ring]
      exact ih _ h2
  obtain ⟨k, N, hN, hkN⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd θ.index_pos.ne' p (Fact.out : p.Prime).ne_one
  have hindex : ∀ x : 𝓞 K, (θ.index : 𝓞 K) * x ∈ θ.adjoin := fun x => by
    rw [← nsmul_mkQ_eq_zero_iff, index_def]
    exact card_nsmul_eq_zero'
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
reduction of `H` for some `i`, then `p` divides the index `[𝓞 K : ℤ[θ]]`: the element
`Φ i (θ) ^ (e i - 1) · ∏_{j ≠ i} Φ j (θ) ^ e j / p` of `K` is an algebraic integer that does not
lie in `ℤ[θ]`, although `p` times it does. -/
theorem dvd_index_of_ne_one_of_dvd (hφ : ∀ i, Irreducible (φ i))
    (hfact : (minpoly ℤ θ.1).map (Int.castRingHom (ZMod p)) = ∏ i, φ i ^ e i)
    (hΦ : ∀ i, (Φ i).map (Int.castRingHom (ZMod p)) = φ i)
    (hH : C (p : ℤ) * H = minpoly ℤ θ.1 - ∏ i, Φ i ^ e i) {i : ι} (h1 : e i ≠ 1)
    (he : 0 < e i) (hdvd : φ i ∣ H.map (Int.castRingHom (ZMod p))) : p ∣ θ.index := by
  classical
  have hp0 : (p : K) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  have hprod := θ.natCast_mul_aeval_eq_neg_prod hH
  obtain ⟨m, hm⟩ : ∃ m, e i = m + 2 := ⟨e i - 2, by omega⟩
  set G₁ : ℤ[X] := Φ i ^ m * ∏ j ∈ Finset.univ.erase i, Φ j ^ e j with hG₁
  have hΦG : Φ i * (Φ i * G₁) = ∏ j, Φ j ^ e j := by
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i), hm, hG₁]
    ring
  have hφG : ∏ j, φ j ^ e j = φ i * (φ i * G₁.map (Int.castRingHom (ZMod p))) := by
    rw [← hΦ i, ← Polynomial.map_mul, ← Polynomial.map_mul, hΦG, Polynomial.map_prod]
    simp only [Polynomial.map_pow, hΦ]
  set ai := aeval θ.1 (Φ i) with hai
  set g₁ := aeval θ.1 G₁ with hg₁
  set Hθ := aeval θ.1 H with hHθ
  have hag : ai * (ai * g₁) = -((p : 𝓞 K) * Hθ) := by
    rw [hprod, hai, hg₁, ← map_mul, ← map_mul, hΦG, map_prod]
    simp only [map_pow, neg_neg]
  obtain ⟨Q, D, hHQ⟩ := θ.exists_aeval_eq_of_map_dvd_map (Φ := Φ i) (G := H) (by
    rw [hΦ i]; exact hdvd)
  rw [← hai, ← hHθ] at hHQ
  -- The candidate `β = Φ i (θ) g₁ / p`, an algebraic integer.
  obtain ⟨β, hβ⟩ : ∃ β : K, β = algebraMap (𝓞 K) K (ai * g₁) / (p : K) := ⟨_, rfl⟩
  have hβp : (p : K) * β = algebraMap (𝓞 K) K ai * algebraMap (𝓞 K) K g₁ := by
    rw [hβ, map_mul]
    field_simp
  have hag' := congrArg (algebraMap (𝓞 K) K) hag
  have hHQ' := congrArg (algebraMap (𝓞 K) K) hHQ
  simp only [map_mul, map_neg, map_add, map_natCast] at hag' hHQ'
  have hβai : algebraMap (𝓞 K) K ai * β = -algebraMap (𝓞 K) K Hθ := by
    apply mul_left_cancel₀ hp0
    rw [mul_left_comm, hβp]
    linear_combination hag'
  have hβint : IsIntegral ℤ β := by
    let N₀ : Submodule ℤ (𝓞 K) := θ.adjoin.toSubmodule.map (LinearMap.mulLeft ℤ (p : 𝓞 K)) ⊔
      θ.adjoin.toSubmodule.map (LinearMap.mulLeft ℤ ai)
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
      obtain ⟨a, ha, rfl⟩ := hy₁
      obtain ⟨b, hb, rfl⟩ := hy₂
      have ha : a ∈ θ.adjoin := ha
      have hb : b ∈ θ.adjoin := hb
      refine ⟨ai * (g₁ * a - aeval θ.1 Q * b) + (p : 𝓞 K) * (-(aeval θ.1 D * b)), ?_, ?_⟩
      · refine Submodule.mem_sup.mpr ⟨(p : 𝓞 K) * (-(aeval θ.1 D * b)), ?_,
          ai * (g₁ * a - aeval θ.1 Q * b), ?_, add_comm _ _⟩
        · exact Submodule.mem_map_of_mem ((Subalgebra.mem_toSubmodule _).mpr
            (θ.adjoin.neg_mem (θ.adjoin.mul_mem (θ.aeval_mem_adjoin _) hb)))
        · exact Submodule.mem_map_of_mem ((Subalgebra.mem_toSubmodule _).mpr
            (θ.adjoin.sub_mem (θ.adjoin.mul_mem (θ.aeval_mem_adjoin _) ha)
              (θ.adjoin.mul_mem (θ.aeval_mem_adjoin _) hb)))
      · simp only [ι', LinearMap.restrictScalars_apply, Algebra.linearMap_apply,
          LinearMap.mulLeft_apply, smul_eq_mul, map_add, map_mul, map_sub, map_neg, map_natCast]
        linear_combination -(algebraMap (𝓞 K) K a) * hβp - (algebraMap (𝓞 K) K b) * hβai +
          (algebraMap (𝓞 K) K b) * hHQ'
  set βₒ : 𝓞 K := ⟨β, hβint⟩ with hβₒ
  have hpβ : (p : 𝓞 K) * βₒ = ai * g₁ := by
    apply NumberField.RingOfIntegers.ext
    simp only [map_mul, map_natCast]
    exact hβp
  -- `βₒ` is not in `ℤ[θ]`: otherwise `minpoly ℤ θ` would divide a polynomial of smaller degree
  -- modulo `p`.
  have hβA : βₒ ∉ θ.adjoin := by
    intro hmem
    rw [adjoin_def, Algebra.adjoin_singleton_eq_range_aeval] at hmem
    obtain ⟨B, hB⟩ := hmem
    have hB' : aeval θ.1 B = βₒ := hB
    have hGB : aeval θ.1 (Φ i * G₁ - C (p : ℤ) * B) = 0 := by
      simp only [map_sub, map_mul, map_natCast, hB', hpβ, ← hai, ← hg₁, sub_self]
    have hf := Polynomial.map_dvd (Int.castRingHom (ZMod p))
      (minpoly.isIntegrallyClosed_dvd θ.1.isIntegral hGB)
    have hzero : (C (p : ℤ) * B).map (Int.castRingHom (ZMod p)) = 0 := by
      rw [Polynomial.map_mul, Polynomial.map_C, eq_intCast, Int.cast_natCast, ZMod.natCast_self,
        C_0, zero_mul]
    rw [Polynomial.map_sub, hzero, sub_zero, Polynomial.map_mul, hΦ i] at hf
    have hfbar : (minpoly ℤ θ.1).map (Int.castRingHom (ZMod p)) =
        φ i * (φ i * G₁.map (Int.castRingHom (ZMod p))) := by rw [hfact, hφG]
    have hf0 : (minpoly ℤ θ.1).map (Int.castRingHom (ZMod p)) ≠ 0 :=
      ((minpoly.monic θ.1.isIntegral).map _).ne_zero
    have hG0 : φ i * G₁.map (Int.castRingHom (ZMod p)) ≠ 0 :=
      right_ne_zero_of_mul (hfbar ▸ hf0)
    have hdeg := Polynomial.natDegree_le_of_dvd hf hG0
    rw [hfbar, Polynomial.natDegree_mul (hφ i).ne_zero hG0] at hdeg
    have hpos : 0 < (φ i).natDegree :=
      Polynomial.natDegree_pos_iff_degree_pos.mpr (degree_pos_of_irreducible (hφ i))
    omega
  have hq0 : θ.adjoin.toSubmodule.mkQ βₒ ≠ 0 := by
    rw [Ne, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Subalgebra.mem_toSubmodule]
    exact hβA
  have hpq : p • θ.adjoin.toSubmodule.mkQ βₒ = 0 := by
    rw [nsmul_mkQ_eq_zero_iff, hpβ]
    exact θ.adjoin.mul_mem (θ.aeval_mem_adjoin _) (θ.aeval_mem_adjoin _)
  rw [index_def, ← addOrderOf_eq_prime hpq hq0]
  exact addOrderOf_dvd_natCard _

-- The statement follows the human-authored specification
-- `TauCetiRoadmap/NumberFieldArithmetic/Suggested.lean`, Layer 3.7.
/-- **Dedekind's criterion.** Let `θ` be an integral primitive element of `K` with minimal
polynomial `f = minpoly ℤ θ`, let `p` be a prime, and factor `f mod p = ∏ i, φ i ^ e i` into
distinct monic irreducible polynomials `φ i` over `ZMod p`, each with multiplicity `e i > 0`.
Choose lifts `Φ i : ℤ[X]` of the `φ i` and let `H : ℤ[X]` satisfy `p H = f - ∏ i, Φ i ^ e i`.
Then `p` does not divide the index `[𝓞 K : ℤ[θ]]` if and only if, for every `i`, either
`e i = 1` or `φ i` does not divide `H mod p`. -/
theorem not_dvd_index_iff (hφ : ∀ i, Irreducible (φ i)) (hφm : ∀ i, (φ i).Monic)
    (hinj : Function.Injective φ) (he : ∀ i, 0 < e i)
    (hfact : (minpoly ℤ θ.1).map (Int.castRingHom (ZMod p)) = ∏ i, φ i ^ e i)
    (hΦ : ∀ i, (Φ i).map (Int.castRingHom (ZMod p)) = φ i)
    (hH : C (p : ℤ) * H = minpoly ℤ θ.1 - ∏ i, Φ i ^ e i) :
    ¬ p ∣ θ.index ↔ ∀ i, e i = 1 ∨ ¬ φ i ∣ H.map (Int.castRingHom (ZMod p)) := by
  refine ⟨fun h i => ?_, θ.not_dvd_index_of_forall hφ hφm hinj he hΦ hH⟩
  by_contra hcon
  rw [not_or, not_not] at hcon
  exact h (θ.dvd_index_of_ne_one_of_dvd hφ hfact hΦ hH hcon.1 (he i) hcon.2)

/-- The right-hand side of Dedekind's criterion does not depend on the choice of the lifts
`Φ i` of the `φ i`, nor on the resulting `H`. -/
theorem forall_eq_one_or_not_dvd_map_iff (hφ : ∀ i, Irreducible (φ i))
    (hφm : ∀ i, (φ i).Monic) (hinj : Function.Injective φ) (he : ∀ i, 0 < e i)
    (hfact : (minpoly ℤ θ.1).map (Int.castRingHom (ZMod p)) = ∏ i, φ i ^ e i)
    {Φ' : ι → ℤ[X]} {H' : ℤ[X]}
    (hΦ : ∀ i, (Φ i).map (Int.castRingHom (ZMod p)) = φ i)
    (hH : C (p : ℤ) * H = minpoly ℤ θ.1 - ∏ i, Φ i ^ e i)
    (hΦ' : ∀ i, (Φ' i).map (Int.castRingHom (ZMod p)) = φ i)
    (hH' : C (p : ℤ) * H' = minpoly ℤ θ.1 - ∏ i, Φ' i ^ e i) :
    (∀ i, e i = 1 ∨ ¬ φ i ∣ H.map (Int.castRingHom (ZMod p))) ↔
      ∀ i, e i = 1 ∨ ¬ φ i ∣ H'.map (Int.castRingHom (ZMod p)) := by
  rw [← θ.not_dvd_index_iff hφ hφm hinj he hfact hΦ hH,
    ← θ.not_dvd_index_iff hφ hφm hinj he hfact hΦ' hH']

end Criterion

end Prime

end TauCeti.NumberField.IntegralPrimitiveElement
