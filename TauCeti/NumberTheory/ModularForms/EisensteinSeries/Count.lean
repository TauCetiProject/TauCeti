/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.EisensteinSeries.Subspace
public import TauCeti.NumberTheory.ModularForms.CongruenceSubgroups.Cusp.Gamma1
import TauCeti.NumberTheory.DirichletCharacter.Basic
import TauCeti.NumberTheory.DirichletCharacter.Even

/-!
# Counting the Eisenstein series with character

The normalized raised Eisenstein series `E_k^(ψ, φ, t)` of weight `k` and level `N` are indexed
by `TauCeti.EisensteinSeries.CharIndex N k`: primitive characters `ψ` modulo `u` and `φ` modulo
`v` with `ψ(-1) φ(-1) = (-1)^k`, and a raising parameter `t` with `t u v ∣ N`. This file counts
these indices. Away from the levels `1`, `2` and `4` there are exactly as many as there are
cusps of `Γ₁(N)`:

`2 · #CharIndex N k = ∑_{g ∣ N} totient(g) totient(N / g) = 2 ε∞(Γ₁(N))`,

where `totient` is Euler's function `Nat.totient`.

The series are linearly independent, so in weight `k ≥ 3` the Eisenstein subspaces
`TauCeti.eisensteinSubspace` of the spaces `M_k(N, χ)` have dimensions summing to this number
(`TauCeti.finrank_eisensteinSubspace`). Comparing it with the number of cusps, which bounds the
dimension of the Eisenstein part of `M_k(Γ₁(N))` through the constant terms, is how
Diamond–Shurman show that the series span that part (Theorem 4.5.2); this file supplies the
count of the series.

The count goes through a bijection. Raising `ψ` and `φ` to the levels `g = t u` and `N / g`
sends an index to a divisor `g ∣ N` and a pair of characters modulo `g` and `N / g` of
product parity `(-1)^k`; conversely, `u` and `v` are the conductors of such a pair, `ψ` and `φ`
their primitive characters, and `t = g / u`. This gives the count `card_eq_sum` at every
level. When `g` or `N / g` exceeds `2`, an odd character at that level exchanges the two
parities, so exactly half of the `totient(g) totient(N / g)` pairs have parity `(-1)^k`
(`DirichletCharacter.two_mul_card_apply_neg_one_mul_apply_neg_one_eq`). Every divisor `g` of
`N ∉ {1, 2, 4}` has this property.

At the levels `1`, `2` and `4` the count is direct. Modulo `1` and `2` the only character is
trivial and even, so a pair of such characters has parity `(-1)^k` exactly when `k` is even. There
are `1`, `2` and `3` indices in even weight, and `0`, `0` and `2` in odd weight. In odd weight the
level-`4` count is one less than the three cusps of `Γ₁(4)`, matching its irregular cusp.

## Main results

* `TauCeti.EisensteinSeries.CharIndex.card_eq_sum`: the number of indices as a sum over the
  divisors `g` of `N` of the number of character pairs modulo `g` and `N / g` with product
  parity `(-1)^k`.
* `TauCeti.EisensteinSeries.CharIndex.two_mul_card`:
  `2 · #CharIndex N k = ∑_{g ∣ N} totient(g) totient(N / g)` for `N ∉ {1, 2, 4}`.
* `TauCeti.EisensteinSeries.CharIndex.card_eq_card_cuspOrbit_Gamma1`: for `N ∉ {1, 2, 4}`, the
  indices are as many as the cusps of `Γ₁(N)`.
* `TauCeti.EisensteinSeries.CharIndex.card_one`, `TauCeti.EisensteinSeries.CharIndex.card_two`,
  `TauCeti.EisensteinSeries.CharIndex.card_four`: the counts at the levels `1`, `2` and `4`.

## References

* [F. Diamond and J. Shurman, *A first course in modular forms*][diamondshurman2005],
  Section 4.5, Theorem 4.5.2, and Section 3.8 for the cusps of `Γ₁(N)`.
-/

public section

open CongruenceSubgroup DirichletCharacter

namespace TauCeti.EisensteinSeries.CharIndex

variable {N k : ℕ}

section NeZero

variable [NeZero N]

/-- The level data of an index `(ψ, φ, t)`: the divisor `g = t u` of `N`, and the characters `ψ`
and `φ` raised to level `N`, which factor through `g` and `N / g` respectively. -/
private noncomputable def toLevel (a : CharIndex N k) :
    Σ g : N.divisors, {p : DirichletCharacter ℂ N × DirichletCharacter ℂ N //
      p.1.FactorsThrough g ∧ p.2.FactorsThrough (N / g) ∧
        p.1 (-1) * p.2 (-1) = (-1) ^ (k : ℤ)} :=
  have hg : a.t * a.u ∣ N := (Dvd.intro _ (mul_assoc _ _ _)).trans a.level_dvd
  ⟨⟨a.t * a.u, Nat.mem_divisors.mpr ⟨hg, NeZero.ne N⟩⟩,
    ⟨(a.psi.changeLevel a.u_dvd, a.phi.changeLevel a.v_dvd),
      ⟨hg, a.psi.changeLevel (dvd_mul_left a.u a.t), changeLevel_trans _ _ _⟩,
      ⟨Nat.div_dvd_of_dvd hg,
        a.phi.changeLevel (Nat.dvd_div_of_mul_dvd (by rw [mul_assoc]; exact a.level_dvd)),
        changeLevel_trans _ _ _⟩,
      by rw [changeLevel_apply_neg_one, changeLevel_apply_neg_one]; exact a.parity⟩⟩

private theorem toLevel_injective : Function.Injective (toLevel (N := N) (k := k)) := by
  intro a b h
  have hg : a.t * a.u = b.t * b.u := congrArg (fun x ↦ (x.1 : ℕ)) h
  have hpsi : a.psi.changeLevel a.u_dvd = b.psi.changeLevel b.u_dvd :=
    congrArg (fun x ↦ x.2.1.1) h
  have hu := u_eq_of_changeLevel_eq hpsi
  have hu₀ : 0 < b.u := Nat.pos_of_dvd_of_pos b.u_dvd (NeZero.pos N)
  exact eq_of_changeLevel_eq (Nat.eq_of_mul_eq_mul_right hu₀ (hu ▸ hg)) hpsi
    (congrArg (fun x ↦ x.2.1.2) h)

private theorem toLevel_surjective : Function.Surjective (toLevel (N := N) (k := k)) := by
  rintro ⟨⟨g, hg⟩, ⟨⟨χ₁, χ₂⟩, h₁, h₂, hpar⟩⟩
  have hgN : g ∣ N := Nat.dvd_of_mem_divisors hg
  have hu : χ₁.conductor ∣ g := χ₁.conductor_dvd_of_mem_conductorSet h₁
  have hv : χ₂.conductor ∣ N / g := χ₂.conductor_dvd_of_mem_conductorSet h₂
  refine ⟨⟨χ₁.conductor, χ₂.conductor, g / χ₁.conductor, χ₁.primitiveCharacter,
    χ₂.primitiveCharacter, χ₁.primitiveCharacter_isPrimitive, χ₂.primitiveCharacter_isPrimitive,
    ?_, ?_⟩, ?_⟩
  · rwa [← changeLevel_apply_neg_one χ₁.conductor_dvd_level,
      ← changeLevel_apply_neg_one χ₂.conductor_dvd_level, changeLevel_primitiveCharacter,
      changeLevel_primitiveCharacter]
  · rw [← mul_assoc, Nat.div_mul_cancel hu]
    exact (mul_dvd_mul_left g hv).trans (dvd_of_eq (Nat.mul_div_cancel' hgN))
  · exact Sigma.subtype_ext (Subtype.ext (Nat.div_mul_cancel hu))
      (Prod.ext (changeLevel_primitiveCharacter χ₁) (changeLevel_primitiveCharacter χ₂))

/-- The pairs of characters at level `N` factoring through `g` and `N / g` are the raises of the
pairs of characters modulo `g` and `N / g` (`DirichletCharacter.factorsThroughEquiv`), with the
same parity. -/
private theorem card_factorsThrough {g : ℕ} (hg : g ∣ N) :
    Nat.card {p : DirichletCharacter ℂ N × DirichletCharacter ℂ N //
      p.1.FactorsThrough g ∧ p.2.FactorsThrough (N / g) ∧
        p.1 (-1) * p.2 (-1) = (-1) ^ (k : ℤ)} =
    Nat.card {q : DirichletCharacter ℂ g × DirichletCharacter ℂ (N / g) //
      q.1 (-1) * q.2 (-1) = (-1) ^ (k : ℤ)} := by
  have : NeZero (N / g) := ⟨fun h ↦ NeZero.ne N (Nat.eq_zero_of_dvd_of_div_eq_zero hg h)⟩
  refine Nat.card_congr (((Equiv.subtypeEquivRight fun _ ↦ and_assoc.symm).trans
    (Equiv.subtypeSubtypeEquivSubtypeInter _ _).symm).trans
    ((Equiv.subtypeProdEquivProd.trans ((factorsThroughEquiv hg).prodCongr
      (factorsThroughEquiv (Nat.div_dvd_of_dvd hg)))).subtypeEquiv fun p ↦ ?_))
  obtain ⟨⟨χ₁, χ₂⟩, h₁, h₂⟩ := p
  dsimp only at h₁ h₂
  simp only [Equiv.trans_apply, Equiv.subtypeProdEquivProd, Equiv.coe_fn_mk,
    Equiv.prodCongr_apply, Prod.map, factorsThroughEquiv_apply]
  rw [← changeLevel_apply_neg_one h₁.dvd, ← changeLevel_apply_neg_one h₂.dvd,
    ← h₁.eq_changeLevel, ← h₂.eq_changeLevel]

/-- At a nonzero level there are finitely many Eisenstein indices. -/
instance : Finite (CharIndex N k) :=
  Finite.of_injective _ toLevel_injective

/-- **The number of Eisenstein indices** at level `N`: indices `(ψ, φ, t)` correspond to the
divisors `g = t u` of `N` together with a pair of characters modulo `g` and `N / g` whose product
parity is `(-1)^k`. -/
theorem card_eq_sum :
    Nat.card (CharIndex N k) = ∑ g ∈ N.divisors,
      Nat.card {q : DirichletCharacter ℂ g × DirichletCharacter ℂ (N / g) //
        q.1 (-1) * q.2 (-1) = (-1) ^ (k : ℤ)} := by
  rw [Nat.card_eq_of_bijective _ ⟨toLevel_injective, toLevel_surjective⟩, Nat.card_sigma,
    ← Finset.sum_coe_sort N.divisors]
  exact Finset.sum_congr rfl fun g _ ↦ card_factorsThrough (Nat.dvd_of_mem_divisors g.2)

end NeZero

/-- **Twice the number of Eisenstein indices** is `∑_{g ∣ N} totient(g) totient(N / g)` away from
the levels `1`, `2` and `4`. -/
theorem two_mul_card (hN : 2 < N) (hN4 : N ≠ 4) :
    2 * Nat.card (CharIndex N k) = ∑ g ∈ N.divisors, g.totient * (N / g).totient := by
  have : NeZero N := ⟨by omega⟩
  rw [card_eq_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun g hg ↦ ?_
  have hgN := Nat.dvd_of_mem_divisors hg
  have hNg : g * (N / g) = N := Nat.mul_div_cancel' hgN
  have : NeZero g := ⟨fun h ↦ by simp [h] at hNg; omega⟩
  have : NeZero (N / g) := ⟨fun h ↦ by simp [h] at hNg; omega⟩
  refine two_mul_card_apply_neg_one_mul_apply_neg_one_eq ?_
    (by rw [zpow_natCast]; exact neg_one_pow_eq_or ℂ k)
  by_contra! h
  have hg₀ : 0 < g := NeZero.pos g
  have hm₀ : 0 < N / g := NeZero.pos (N / g)
  generalize N / g = m at h hNg hm₀
  obtain ⟨h₁, h₂⟩ := h
  interval_cases g <;> interval_cases m <;> omega

/-- **The Eisenstein indices are as many as the cusps of `Γ₁(N)`** away from the levels `1`,
`2` and `4`. -/
theorem card_eq_card_cuspOrbit_Gamma1 (hN : 2 < N) (hN4 : N ≠ 4) :
    Nat.card (CharIndex N k) = Nat.card ((Gamma1 N).map sl2zToPSL2R).CuspOrbit := by
  have : NeZero N := ⟨by omega⟩
  have h₁ := two_mul_card (k := k) hN hN4
  have h₂ := card_cuspOrbit_Gamma1 N hN hN4
  omega

/-! ### The levels `1`, `2` and `4` -/

/-- Modulo `a ≤ 2` and `b ≤ 2` the only characters are trivial and even, so there is one pair of
parity `(-1)^k` when `k` is even and none when `k` is odd. -/
private theorem card_parity_of_le_two {a b : ℕ} [NeZero a] [NeZero b] (ha : a ≤ 2) (hb : b ≤ 2) :
    Nat.card {q : DirichletCharacter ℂ a × DirichletCharacter ℂ b //
      q.1 (-1) * q.2 (-1) = (-1) ^ (k : ℤ)} = if Even k then 1 else 0 := by
  have hneg {n : ℕ} [NeZero n] (hn : n ≤ 2) (χ : DirichletCharacter ℂ n) : χ (-1) = 1 := by
    obtain rfl | rfl : n = 1 ∨ n = 2 := by have := NeZero.ne n; omega
    all_goals rw [show (-1 : ZMod _) = 1 by decide, map_one]
  have hcard {n : ℕ} [NeZero n] (hn : n ≤ 2) : Nat.card (DirichletCharacter ℂ n) = 1 := by
    rw [card_eq_totient_of_hasEnoughRootsOfUnity ℂ n]
    obtain rfl | rfl : n = 1 ∨ n = 2 := by have := NeZero.ne n; omega
    all_goals rfl
  simp only [hneg ha, hneg hb, one_mul, zpow_natCast]
  split_ifs with hk
  · rw [hk.neg_one_pow, Nat.card_congr (Equiv.subtypeUnivEquiv fun _ ↦ rfl), Nat.card_prod,
      hcard ha, hcard hb]
  · rw [(Nat.not_even_iff_odd.mp hk).neg_one_pow]
    have : IsEmpty {q : DirichletCharacter ℂ a × DirichletCharacter ℂ b // (1 : ℂ) = -1} :=
      ⟨fun ⟨_, h⟩ ↦ by norm_num at h⟩
    exact Nat.card_of_isEmpty

/-- Of the two pairs of characters modulo `a` and `b`, with `{a, b} = {1, 4}`, exactly one has
parity `(-1)^k`. -/
private theorem card_parity_of_mul_eq_four {a b : ℕ} [NeZero a] [NeZero b]
    (hab : a = 1 ∧ b = 4 ∨ a = 4 ∧ b = 1) :
    Nat.card {q : DirichletCharacter ℂ a × DirichletCharacter ℂ b //
      q.1 (-1) * q.2 (-1) = (-1) ^ (k : ℤ)} = 1 := by
  have h := two_mul_card_apply_neg_one_mul_apply_neg_one_eq (R := ℂ) (a := a) (b := b)
    (ε := (-1) ^ (k : ℤ)) (by omega) (by rw [zpow_natCast]; exact neg_one_pow_eq_or ℂ k)
  obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := hab <;>
  · rw [Nat.totient_one, show Nat.totient 4 = 2 by decide] at h
    omega

/-- There is one Eisenstein index at level `1` in even weight, and none in odd weight. -/
theorem card_one : Nat.card (CharIndex 1 k) = if Even k then 1 else 0 := by
  rw [card_eq_sum, Nat.divisors_one, Finset.sum_singleton]
  exact card_parity_of_le_two (by norm_num) (by norm_num)

/-- There are two Eisenstein indices at level `2` in even weight, and none in odd weight. -/
theorem card_two : Nat.card (CharIndex 2 k) = if Even k then 2 else 0 := by
  rw [card_eq_sum, Nat.prime_two.divisors, Finset.sum_pair (by norm_num),
    card_parity_of_le_two (by norm_num) (by norm_num),
    card_parity_of_le_two (by norm_num) (by norm_num)]
  split_ifs <;> rfl

/-- There are three Eisenstein indices at level `4` in even weight, and two in odd weight. -/
theorem card_four : Nat.card (CharIndex 4 k) = if Even k then 3 else 2 := by
  rw [card_eq_sum, show Nat.divisors 4 = {1, 2, 4} by decide, Finset.sum_insert (by decide),
    Finset.sum_pair (by norm_num)]
  simp only [Nat.reduceDiv]
  rw [card_parity_of_mul_eq_four (.inl ⟨rfl, rfl⟩), card_parity_of_mul_eq_four (.inr ⟨rfl, rfl⟩),
    card_parity_of_le_two (a := 2) (b := 2) (by norm_num) (by norm_num)]
  split_ifs <;> rfl

end TauCeti.EisensteinSeries.CharIndex
