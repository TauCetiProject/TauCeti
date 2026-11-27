/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Cyclotomic.Basic

import Mathlib.Tactic.LinearCombination
import TauCeti.FieldTheory.Kummer.Character
import TauCeti.FieldTheory.Kummer.Cyclic
import TauCeti.FieldTheory.PowerDescent
import TauCeti.NumberTheory.Cyclotomic.Irreducible
import TauCeti.NumberTheory.Multiplicity
import TauCeti.RingTheory.RootsOfUnity.PPower

/-!
# Descending prime-power roots from a cyclotomic extension

Let `p` be a prime, `M` a field and `L = M(μ_{p ^ e})` a `p ^ e`-th cyclotomic extension of `M`.
If `p` is odd, or if `M` contains a square root `i` of `-1`, then for every `E ≥ e` an element of
`M` that is a `p ^ E`-th power in `L` is already a `p ^ E`-th power in `M`
(`TauCeti.exists_pow_eq_of_isCyclotomicExtension`). The hypothesis cannot be dropped:
`16 = (1 + i) ^ 8` is an `8`-th power in `ℚ(μ_8)`, but not in `ℚ`.

The proof climbs down the tower `M ⊆ M(μ_p) ⊆ M(μ_{p ^ 2}) ⊆ ⋯ ⊆ M(μ_{p ^ e})` one step at a time.

* The bottom step `M ⊆ M(μ_p)` has degree at most `p - 1`, prime to `p`, and a norm argument
  descends the root (`TauCeti.exists_pow_eq_of_coprime_finrank`). When `p = 2` and `i ∈ M`, the
  steps up to `M(μ_4) = M` are trivial.
* Every other step `K ⊆ K(ω)` adjoins a root of unity `ω` with `ω ^ p ∈ K`, where `K` contains a
  primitive `p ^ h`-th root of unity with `p ^ h > 2`. Such an extension is trivial or cyclic of
  degree `p`, with a generator `g` acting by `g ω = ξ ω` for a primitive `p`-th root of unity
  `ξ ∈ K` (`TauCeti.exists_forall_mem_zpowers_apply_eq`). For `x = y ^ (p ^ E) ∈ K` the ratio
  `η = g y / y` is a `p`-power root of unity whose `p` conjugates multiply to `1`. The generator
  raises `η` to a power `a ≡ 1 (mod p ^ h)`, so the product of the conjugates is
  `η ^ (1 + a + ⋯ + a ^ (p - 1))`, and `p` divides this exponent exactly once
  (`Nat.not_sq_dvd_geom_sum`). Hence `η ^ p = 1`, so `η = ξ ^ k` for some `k`, and `y / ω ^ k` is
  a `p ^ E`-th root of `x` fixed by `g`, that is, an element of `K`
  (`TauCeti.exists_pow_eq_of_adjoin_eq_top`).

This is the cyclotomic descent in Chevalley's proof that a congruence condition detects the `n`-th
powers in a finitely generated subgroup of the multiplicative group of a number field: a root found
in `M(μ_{p ^ e})` is returned to `M`. When `p = 2` and `i ∉ M`, the root is first returned to
`M(i)` by this file and then to `M` by `TauCeti.exists_pow_eq_of_forall_not_isPrimitiveRoot`.

## Main results

* `TauCeti.exists_pow_eq_of_adjoin_eq_top`: a `p ^ E`-th root descends along a step `K ⊆ K(ω)`
  of the `p`-power cyclotomic tower above `K ∋ μ_{p ^ h}`, `p ^ h > 2`.
* `TauCeti.exists_pow_eq_of_isCyclotomicExtension`: a `p ^ E`-th root, `E ≥ e`, descends from
  `M(μ_{p ^ e})` to `M` when `p` is odd or `i ∈ M`.

## References

* C. Chevalley, *Deux théorèmes d'arithmétique*, J. Math. Soc. Japan 3 (1951), 36–44, §§1–5.
-/

public section

open Module IntermediateField Finset

namespace TauCeti

variable {K L : Type*} [Field K] [Field L] [Algebra K L] {p h E : ℕ} [hp : Fact p.Prime]
  {ζ : K}

/-- Let `K` contain a primitive `p ^ h`-th root of unity, `p ^ h > 2`, and let `g` be a
`K`-automorphism of `L`. A `p`-power root of unity `η ∈ L` whose conjugates `η, g η, …,
g ^ (p - 1) η` multiply to `1` is a `p`-th root of unity. -/
private theorem pow_prime_eq_one_of_prod_eq_one (hζ : IsPrimitiveRoot ζ (p ^ h)) (h2 : 2 < p ^ h)
    (g : L ≃ₐ[K] L) {η : L} (hηE : η ^ p ^ E = 1) (hprod : ∏ i ∈ range p, (g ^ i) η = 1) :
    η ^ p = 1 := by
  have hζL := hζ.map_of_injective (algebraMap K L).injective
  -- the `p ^ h`-th roots of unity of `L` lie in `K`, so the automorphisms fix them
  have hfix (θ : L) (hθ : θ ^ p ^ h = 1) (i : ℕ) : (g ^ i) θ = θ := by
    obtain ⟨j, -, rfl⟩ := hζL.eq_pow_of_pow_eq_one hθ
    rw [← map_pow, AlgEquiv.commutes]
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp.out).1 (orderOf_dvd_of_pow_eq_one hηE)
  rcases le_or_gt j h with hjh | hhj
  · have hηh : η ^ p ^ h = 1 := by
      rw [← orderOf_dvd_iff_pow_eq_one, hj]
      exact pow_dvd_pow p hjh
    simpa [hfix η hηh] using hprod
  exfalso
  have hh : h ≠ 0 := by
    rintro rfl
    simp at h2
  -- `g` raises `η` to a power `a`, and `a ≡ 1 [MOD p ^ h]` since `g` fixes `η ^ p ^ (j - h)`
  have hη : IsPrimitiveRoot η (p ^ j) := hj ▸ IsPrimitiveRoot.orderOf η
  obtain ⟨a, -, ha⟩ := hη.eq_pow_of_pow_eq_one (ξ := g η)
    (by rw [← map_pow, hη.pow_eq_one, map_one])
  have hgi (i : ℕ) : (g ^ i) η = η ^ a ^ i := by
    induction i with
    | zero => simp
    | succ i ih => simp [pow_succ', ih, ← ha, ← pow_mul]
  have hpj : p ^ j = p ^ (j - h) * p ^ h := by rw [← pow_add, Nat.sub_add_cancel hhj.le]
  have hmod : a * p ^ (j - h) ≡ p ^ (j - h) [MOD p ^ j] := by
    have hfixη : η ^ (a * p ^ (j - h)) = η ^ p ^ (j - h) := by
      simpa [pow_mul, ha] using hfix (η ^ p ^ (j - h)) (by rw [← pow_mul, ← hpj, hη.pow_eq_one]) 1
    rwa [(hη.isOfFinOrder (pow_ne_zero _ hp.out.ne_zero)).pow_eq_pow_iff_modEq,
      ← hη.eq_orderOf] at hfixη
  have ha1 : a ≡ 1 [MOD p ^ h] := by
    refine Nat.ModEq.mul_left_cancel' (c := p ^ (j - h)) (pow_ne_zero _ hp.out.ne_zero) ?_
    rwa [mul_one, mul_comm _ a, ← hpj]
  -- the product of the conjugates of `η` is `η ^ (1 + a + ⋯ + a ^ (p - 1))`
  have hS : p ^ 2 ∣ ∑ i ∈ range p, a ^ i := by
    refine (pow_dvd_pow p (by omega : 2 ≤ j)).trans (hη.dvd_of_pow_eq_one _ ?_)
    rw [← prod_pow_eq_pow_sum, ← hprod]
    exact prod_congr rfl fun i _ ↦ (hgi i).symm
  refine Nat.not_sq_dvd_geom_sum (ha1.of_dvd (dvd_pow_self p (by omega))) (fun hp2 ↦ ?_) hS
  subst hp2
  have hh2 : 2 ≤ h := by
    by_contra! hh2
    obtain rfl : h = 1 := by omega
    simp at h2
  exact ha1.of_dvd (pow_dvd_pow 2 hh2)

/-- **Descent along one step of the cyclotomic tower.** Let `K` contain a primitive `p ^ h`-th root
of unity, with `p ^ h > 2`, and let `L = K(ω)` for a `p ^ E`-th root of unity `ω` with `ω ^ p ∈ K`.
Then an element of `K` that is a `p ^ E`-th power in `L` is a `p ^ E`-th power in `K`. -/
theorem exists_pow_eq_of_adjoin_eq_top (hζ : IsPrimitiveRoot ζ (p ^ h)) (h2 : 2 < p ^ h)
    {ω : L} (hωE : ω ^ p ^ E = 1) {b : K} (hωp : ω ^ p = algebraMap K L b) (hgen : K⟮ω⟯ = ⊤)
    {x : K} {y : L} (hy : y ^ p ^ E = algebraMap K L x) : ∃ z : K, z ^ p ^ E = x := by
  have hh : h ≠ 0 := by
    rintro rfl
    simp at h2
  have hξ : IsPrimitiveRoot (ζ ^ p ^ (h - 1)) p := by
    simpa using hζ.pow_pow_sub hp.out.ne_zero (Nat.one_le_iff_ne_zero.2 hh)
  have : NeZero p := ⟨hp.out.ne_zero⟩
  obtain ⟨g, hg, hd, hgω⟩ := exists_forall_mem_zpowers_apply_eq hξ hωp hgen
  rcases (Nat.dvd_prime hp.out).1 hd with h1 | hpd
  · -- `L = K`
    obtain ⟨z, rfl⟩ : y ∈ Set.range (algebraMap K L) := by
      rw [← IntermediateField.mem_bot, IntermediateField.bot_eq_top_iff_finrank_eq_one.2 h1]
      trivial
    exact ⟨z, (algebraMap K L).injective (by rw [map_pow, hy])⟩
  rw [hpd, Nat.div_self hp.out.pos, pow_one] at hgω
  have : FiniteDimensional K L := Module.finite_of_finrank_pos (hpd ▸ hp.out.pos)
  have : IsGalois K L := isGalois_of_pow_eq_of_adjoin_eq_top hξ hωp hgen
  have hgp : g ^ p = 1 := by
    rw [← hpd, ← IsGalois.card_aut_eq_finrank]
    exact pow_card_eq_one'
  rcases eq_or_ne x 0 with rfl | hx0
  · exact ⟨0, zero_pow (pow_ne_zero _ hp.out.ne_zero)⟩
  have hy0 : y ≠ 0 := by
    rintro rfl
    rw [zero_pow (pow_ne_zero _ hp.out.ne_zero), eq_comm, map_eq_zero] at hy
    exact hx0 hy
  -- `η = g y / y` is a `p ^ E`-th root of unity whose conjugates multiply to `g ^ p y / y = 1`
  set η := g y / y with hη
  have hηE : η ^ p ^ E = 1 := apply_div_pow_eq_one hy0 (by rw [hy, AlgEquiv.commutes])
  have hprod (n : ℕ) : ∏ i ∈ range n, (g ^ i) η = (g ^ n) y / y := by
    induction n with
    | zero => simp [div_self hy0]
    | succ n ih =>
      have hgy : (g ^ n) y ≠ 0 := (map_ne_zero (g ^ n)).2 hy0
      rw [prod_range_succ, ih, pow_succ, AlgEquiv.mul_apply, hη, map_div₀]
      field_simp
  have hηp := pow_prime_eq_one_of_prod_eq_one hζ h2 g hηE (by rw [hprod, hgp]; simp [div_self hy0])
  -- so `η` is a power of `ξ = g ω / ω`, and `y / ω ^ k` is fixed by `g`
  obtain ⟨k, -, hk⟩ := (hξ.map_of_injective (algebraMap K L).injective).eq_pow_of_pow_eq_one hηp
  obtain ⟨z, hz⟩ : y / ω ^ k ∈ Set.range (algebraMap K L) := by
    have hfix : g ∈ MulAction.stabilizer (L ≃ₐ[K] L) (y / ω ^ k) := by
      have hgy : g y ≠ 0 := (map_ne_zero g).2 hy0
      rw [MulAction.mem_stabilizer_iff, AlgEquiv.smul_def, map_div₀, map_pow, hgω, mul_pow, hk, hη]
      field_simp
    exact (IsGalois.mem_range_algebraMap_iff_fixed _).2 fun σ ↦ Subgroup.zpowers_le.2 hfix (hg σ)
  have hωk : (ω ^ k) ^ p ^ E = 1 := by rw [pow_right_comm, hωE, one_pow]
  exact ⟨z, (algebraMap K L).injective (by simp [hz, div_pow, hωk, hy])⟩

/-- The bottom of the tower: if `p ^ e ≤ 2 p`, and `p` is odd or `i ∈ M`, then `[M(μ_{p ^ e}) : M]`
is prime to `p`. -/
private theorem coprime_finrank_of_pow_le {M L : Type*} [Field M] [Field L] [Algebra M L] {e : ℕ}
    [IsCyclotomicExtension {p ^ e} M L] (hM : p ≠ 2 ∨ ∃ i : M, i ^ 2 = -1) (he : p ^ e ≤ 2 * p) :
    p.Coprime (finrank M L) := by
  have : NeZero (p ^ e) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  have : FiniteDimensional M L := IsCyclotomicExtension.finiteDimensional {p ^ e} M L
  rcases ne_or_eq p 2 with hp2 | rfl
  · -- for odd `p` the exponent is at most one, and `[L : M] ≤ φ (p ^ e) < p`
    have he1 : e ≤ 1 := by
      by_contra! he1
      have h3 : 3 ≤ p := lt_of_le_of_ne hp.out.two_le (Ne.symm hp2)
      have : p ^ 2 ≤ p ^ e := Nat.pow_le_pow_right hp.out.pos he1
      nlinarith
    have hlt : finrank M L < p := by
      refine (IsCyclotomicExtension.finrank_le_totient (n := p ^ e) M L).trans_lt ?_
      interval_cases e
      · simpa using hp.out.one_lt
      · simpa [Nat.totient_prime hp.out] using hp.out.pos
    exact Nat.coprime_of_lt_prime finrank_pos.ne' hlt hp.out
  -- for `p = 2` the exponent is at most two, and the fourth roots of unity `±1, ±i` lie in `M`
  obtain ⟨i, hi⟩ := hM.resolve_left (by simp)
  have he2 : e ≤ 2 := by
    by_contra! he2
    have : 2 ^ 3 ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) he2
    omega
  set ζ := IsCyclotomicExtension.zeta (2 ^ e) M L
  have hζ := IsCyclotomicExtension.zeta_spec (2 ^ e) M L
  have h4 : ζ ^ 4 = 1 := (hζ.pow_eq_one_iff_dvd 4).2 (by interval_cases e <;> norm_num)
  have hi' : algebraMap M L i ^ 2 = -1 := by rw [← map_pow, hi, map_neg, map_one]
  have hζM : ζ ∈ Set.range (algebraMap M L) := by
    have : (ζ - 1) * (ζ + 1) * ((ζ - algebraMap M L i) * (ζ + algebraMap M L i)) = 0 := by
      linear_combination h4 + (1 - ζ ^ 2) * hi'
    rcases mul_eq_zero.1 this with h | h <;> rcases mul_eq_zero.1 h with h | h
    · exact ⟨1, by rw [map_one, ← sub_eq_zero.1 h]⟩
    · exact ⟨-1, by rw [map_neg, map_one, eq_neg_of_add_eq_zero_left h]⟩
    · exact ⟨i, (sub_eq_zero.1 h).symm⟩
    · exact ⟨-i, by rw [map_neg, eq_neg_of_add_eq_zero_left h]⟩
  have hbot : (⊥ : Subalgebra M L) = ⊤ := by
    rw [← IsCyclotomicExtension.adjoin_primitive_root_eq_top hζ]
    exact le_antisymm bot_le (Algebra.adjoin_le (Set.singleton_subset_iff.2 hζM))
  rw [Subalgebra.bot_eq_top_iff_finrank_eq_one.1 hbot]
  exact Nat.coprime_one_right 2

/-- **Cyclotomic descent of prime-power roots.** Let `p` be a prime, `L` a `p ^ e`-th
cyclotomic extension of `M` and `e ≤ E`. If `p` is odd, or if `-1` is a square in `M`, then an
element of `M` that is a `p ^ E`-th power in `L` is a `p ^ E`-th power in `M`. -/
theorem exists_pow_eq_of_isCyclotomicExtension {M L : Type*} [Field M] [Field L] [Algebra M L]
    {e : ℕ} [IsCyclotomicExtension {p ^ e} M L] (he : e ≤ E) (hM : p ≠ 2 ∨ ∃ i : M, i ^ 2 = -1)
    {x : M} {y : L} (hy : y ^ p ^ E = algebraMap M L x) : ∃ z : M, z ^ p ^ E = x := by
  induction e generalizing L x y with
  | zero =>
    have h1 : p ^ 0 ≤ 2 * p := by
      have := hp.out.pos
      rw [pow_zero]
      omega
    exact exists_pow_eq_of_coprime_finrank ((coprime_finrank_of_pow_le hM h1).pow_left E) hy
  | succ e ih =>
    by_cases h2 : 2 < p ^ e
    swap
    · exact exists_pow_eq_of_coprime_finrank
        ((coprime_finrank_of_pow_le (e := e + 1) hM (by rw [pow_succ]; nlinarith)).pow_left E) hy
    -- descend from `L = M(ζ)` to `K = M(ζ ^ p)`, then apply the induction hypothesis to `K`
    have : NeZero (p ^ (e + 1)) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
    set ζ := IsCyclotomicExtension.zeta (p ^ (e + 1)) M L
    have hζ := IsCyclotomicExtension.zeta_spec (p ^ (e + 1)) M L
    have hζp : IsPrimitiveRoot (ζ ^ p) (p ^ e) := hζ.pow (NeZero.pos _) (pow_succ' p e)
    have : NeZero (p ^ e) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
    let K := M⟮ζ ^ p⟯
    have : IsCyclotomicExtension {p ^ e} M K := hζp.intermediateField_adjoin_isCyclotomicExtension M
    have hζK : IsPrimitiveRoot (AdjoinSimple.gen M (ζ ^ p)) (p ^ e) :=
      hζp.of_map_of_injective (f := algebraMap K L) (algebraMap K L).injective
    have hgen : K⟮ζ⟯ = ⊤ := by
      refine IntermediateField.adjoin_eq_top_of_adjoin_eq_top M (eq_top_iff.2 fun w _ ↦ ?_)
      refine IntermediateField.algebra_adjoin_le_adjoin M {ζ} ?_
      rw [IsCyclotomicExtension.adjoin_primitive_root_eq_top hζ]
      trivial
    obtain ⟨z, hz⟩ := exists_pow_eq_of_adjoin_eq_top hζK h2
      ((hζ.pow_eq_one_iff_dvd _).2 (pow_dvd_pow p he)) (AdjoinSimple.algebraMap_gen M (ζ ^ p)).symm
      hgen (x := algebraMap M K x) (by rw [hy, IsScalarTower.algebraMap_apply M K L])
    exact ih (by omega) hz

end TauCeti
