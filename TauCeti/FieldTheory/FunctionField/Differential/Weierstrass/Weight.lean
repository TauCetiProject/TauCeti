/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Consequences.WeierstrassGaps
public import TauCeti.FieldTheory.FunctionField.Differential.Wronskian

/-!
# The Weierstrass weight as the order of a Wronskian

Let `W` be a canonical divisor of a function field `F / k` with exact constants and genus `g`,
in the form of a divisor satisfying the Riemann--Roch identity
(`TauCeti.Divisor.IsRiemannRochDivisor`), so that `ℓ(W) = g`. Let `P` be a rational place with a
separating prime element `t`. This file proves that the Wronskian, with respect to `t`, of any
`k`-basis of `L(W)` has order

`ord_P W(f₁, …, f_g) = w(P) - g · W(P)`

at `P`, where `w(P) = ∑ⱼ (lⱼ - j)` is the Weierstrass weight of the gaps `l₁ < ⋯ < l_g` at `P`
(`TauCeti.Place.weierstrassWeight`). The hypothesis is that the gaps at `P` stay pairwise
distinct in `k`; this always holds in characteristic zero (use `Nat.cast_injective.injOn`), and in
characteristic `p` whenever `p ≥ 2g - 1`, because every gap lies in `1, …, 2g - 1`.

For `W` the divisor of a Weil differential `ω`, the sections `f ∈ L(W)` are the coefficients of
the regular differentials `f ω`, and the correction `g · W(P)` is the order of `ω^g` at `P`: the
Wronskian of the regular differentials vanishes at `P` to order exactly the Weierstrass weight.
This local identity is the input to the Wronskian count of Weierstrass points.

The proof chooses, for each gap `l`, a section of `L(W)` of order `l - 1 - W(P)` at `P`
(`TauCeti.Place.isGap_iff_exists_mem_riemannRochSpace_ord_eq`). These `g` sections have pairwise
distinct orders, so the order of their Wronskian is computed by
`TauCeti.Place.ord_wronskian_derivativeOfSeparating`. Any basis of `L(W)` is related to this
family by a matrix over `k`, which multiplies the Wronskian by a nonzero constant
(`Derivation.wronskian_sum_smul`).

## Main results

* `TauCeti.Place.wronskian_derivativeOfSeparating_basis_ne_zero`: the Wronskian of a basis of
  `L(W)` is nonzero when the gaps at `P` are distinct in `k`.
* `TauCeti.Place.ord_wronskian_derivativeOfSeparating_basis_eq_weierstrassWeight_sub`: its order
  at `P` is `w(P) - g · W(P)`.

## References

* D. M. Goldschmidt, *Algebraic Functions and Projective Curves*, GTM 215, Springer, 2003,
  the Wronskian treatment of Weierstrass points.
* H. M. Farkas and I. Kra, *Riemann Surfaces*, 2nd ed., GTM 71, Springer, 1992, Section III.5,
  for the Weierstrass weight as the order of the Wronskian of the regular differentials.
-/

public section

open scoped IntermediateField

namespace TauCeti

namespace Place

variable {k F : Type*} [Field k] [Field F] [Algebra k F] (P : Place k F) {t : F}
  (hP : P.degree = 1) (ht : P.ord t = 1) (htr : Transcendental k t) [Algebra.IsSeparable k⟮t⟯ F]
  {W : Divisor k F} {g₀ : ℕ}

include hP ht in
/-- The Wronskian of a basis of `L(W)` is a nonzero constant multiple of the Wronskian of a family
of sections of `L(W)` adapted to the gaps at `P`, whose order is `w(P) - g · W(P)`. -/
private theorem exists_wronskian_eq_wronskian_basis_mul (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) (hW : W.IsRiemannRochDivisor g₀)
    (hgaps : Set.InjOn (Nat.cast : ℕ → k) P.weierstrassGaps) {n : ℕ}
    (b : Module.Basis (Fin n) k (riemannRochSpace W)) :
    ∃ f : Fin n → F, (derivativeOfSeparating htr).wronskian f ≠ 0 ∧
      P.ord ((derivativeOfSeparating htr).wronskian f) =
        P.weierstrassWeight - (genus k F : ℤ) * W.coeff P ∧
      ∃ c : k, (derivativeOfSeparating htr).wronskian f =
        (derivativeOfSeparating htr).wronskian (fun i ↦ (b i : F)) * algebraMap k F c := by
  have hn : n = genus k F := by
    have h := Module.finrank_eq_card_basis b
    rw [Fintype.card_fin, ← Divisor.dim_def, hW.dim_eq hF hex, hW.genus_eq hF hex] at h
    exact h.symm
  have hcard : P.weierstrassGaps.card = n := (P.card_weierstrassGaps hF hex hP).trans hn.symm
  -- Enumerate the gaps as `e 0, …, e (n - 1)`.
  set e : Fin n → ℕ := fun j ↦ ((P.weierstrassGaps.equivFinOfCardEq hcard).symm j : ℕ)
  have he_mem : ∀ j, e j ∈ P.weierstrassGaps := fun j ↦
    ((P.weierstrassGaps.equivFinOfCardEq hcard).symm j).2
  have he_inj : Function.Injective e := Subtype.val_injective.comp (Equiv.injective _)
  have he_sum : ∑ j, (e j : ℤ) = ∑ m ∈ P.weierstrassGaps, (m : ℤ) := by
    rw [← Finset.sum_coe_sort P.weierstrassGaps]
    exact Equiv.sum_comp (P.weierstrassGaps.equivFinOfCardEq hcard).symm fun m ↦ ((m : ℕ) : ℤ)
  -- A section of `L(W)` of order `e j - 1 - W(P)` at `P` for each gap `e j`.
  choose f hfW hf0 hford using fun j ↦
    (P.isGap_iff_exists_mem_riemannRochSpace_ord_eq hF hW hP
      ((P.mem_weierstrassGaps_iff _).mp (he_mem j)).1).mp
      ((P.mem_weierstrassGaps_iff_isGap hF hex _).mp (he_mem j))
  have hinj : Function.Injective fun j ↦ (P.ord (f j) : k) := fun i j hij ↦ by
    simp only [hford] at hij
    push_cast at hij
    exact he_inj (hgaps (he_mem i) (he_mem j) (by linear_combination hij))
  refine ⟨f, P.wronskian_derivativeOfSeparating_ne_zero hP ht htr hf0 hinj, ?_, ?_⟩
  · -- `∑ⱼ (e j - 1 - W(P)) - n (n - 1) / 2 = ∑ gaps - (n + 1).choose 2 - n W(P)`.
    have hw := P.weierstrassWeight_add_card_add_one_choose_two
    rw [hcard] at hw
    have hch : (n + 1).choose 2 = n + n * (n - 1) / 2 := by
      rw [Nat.choose_succ_succ', Nat.choose_one_right, Nat.choose_two_right]
    have hwZ : (P.weierstrassWeight : ℤ) + (n + (n * (n - 1) / 2 : ℕ)) =
        ∑ m ∈ P.weierstrassGaps, (m : ℤ) := by
      rw [← Nat.cast_sum, ← hw, hch]
      push_cast
      ring
    rw [P.ord_wronskian_derivativeOfSeparating hP ht htr hf0 hinj]
    simp only [hford, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one, he_sum, ← hn]
    linarith
  · -- Expand each `f j` in the basis `b`.
    refine ⟨(Matrix.of fun i j ↦ b.repr ⟨f j, hfW j⟩ i).det, ?_⟩
    rw [← Derivation.wronskian_sum_smul]
    congr 1
    funext j
    have h := congrArg Subtype.val (b.sum_repr ⟨f j, hfW j⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at h
    simpa only [Matrix.of_apply] using h.symm

include hP ht in
/-- **The Wronskian of a canonical basis is a nonzero function.** If `W`
satisfies the Riemann--Roch identity, `P` is a rational place with a separating prime element `t`,
and the gaps at `P` are pairwise distinct in `k`, then the Wronskian with respect to `t` of any
`k`-basis of `L(W)` is nonzero. -/
theorem wronskian_derivativeOfSeparating_basis_ne_zero (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) (hW : W.IsRiemannRochDivisor g₀)
    (hgaps : Set.InjOn (Nat.cast : ℕ → k) P.weierstrassGaps) {n : ℕ}
    (b : Module.Basis (Fin n) k (riemannRochSpace W)) :
    (derivativeOfSeparating htr).wronskian (fun i ↦ (b i : F)) ≠ 0 := by
  obtain ⟨f, hf0, -, c, hc⟩ := P.exists_wronskian_eq_wronskian_basis_mul hP ht htr hF hex hW hgaps b
  exact left_ne_zero_of_mul (hc ▸ hf0)

include hP ht in
/-- **The Weierstrass weight is the order of the Wronskian of a canonical basis.** If `W`
satisfies the Riemann--Roch identity for a function field with exact constants and genus `g`, `P`
is a rational place with a separating prime element `t`, and the gaps at `P` are pairwise distinct
in `k`, then the Wronskian with respect to `t` of any `k`-basis of `L(W)` has order
`w(P) - g · W(P)` at `P`, where `w(P)` is the Weierstrass weight. -/
theorem ord_wronskian_derivativeOfSeparating_basis_eq_weierstrassWeight_sub
    (hF : IsFunctionField k F) (hex : IsIntegrallyClosedIn k F) (hW : W.IsRiemannRochDivisor g₀)
    (hgaps : Set.InjOn (Nat.cast : ℕ → k) P.weierstrassGaps) {n : ℕ}
    (b : Module.Basis (Fin n) k (riemannRochSpace W)) :
    P.ord ((derivativeOfSeparating htr).wronskian (fun i ↦ (b i : F))) =
      P.weierstrassWeight - (genus k F : ℤ) * W.coeff P := by
  obtain ⟨f, hf0, hord, c, hc⟩ :=
    P.exists_wronskian_eq_wronskian_basis_mul hP ht htr hF hex hW hgaps b
  rw [hc] at hf0 hord
  rwa [P.ord_mul (left_ne_zero_of_mul hf0) (right_ne_zero_of_mul hf0), ord_algebraMap,
    add_zero] at hord

end Place

end TauCeti
