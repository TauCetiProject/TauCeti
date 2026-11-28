/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Transcendental.Waldschmidt.Interpolation.Residual
import TauCeti.LinearAlgebra.FreeModule.BoxPoints

/-!
# The subgroup obstruction of Waldschmidt's rank argument

In the rank argument of Waldschmidt's lower bound for linear forms in logarithms (W00 §9.2.3), a
zero estimate on the algebraic group `G = W × 𝔾ₘ` is applied, where `W = V · y + K e₀` is spanned
by the grid points of a residual subspace `V` of dimension `d` (`TauCeti.IsWaldschmidtResidual`)
and by the direction `e₀` of the derivatives, so that `dim W = d`. The points are
`γ(s) = (s · y, α₁^(s₁) ⋯ αₘ^(sₘ))` for the indices `s` in `Σ₀ = (S - S) ∩ V`, and the
derivatives are taken along `(e₀, 1)`. If the interpolation matrix does not have full rank,
Philippon's zero estimate (W00, Chapter 5) produces a connected algebraic subgroup `G* ≠ G` with

`binom(S₀ + ℓ*, ℓ*) · #((Σ₀ + G*) / G*) · H(G*; T₀, 2T₁) ≤ H(G; T₀, 2T₁)`,

where `ℓ*` is `0` if `(e₀, 1)` is tangent to `G*` and `1` otherwise, and `H` is the degree of the
closure in `ℙ^d × ℙ¹` for the bidegree `(T₀, 2T₁)` of the auxiliary polynomials:
`H(G; T₀, 2T₁) = (d + 1) T₀^d (2T₁)`. The connected algebraic subgroups of `W × 𝔾ₘ` are the
products `U × 𝔾ₘ` and `U × {1}` with `U ≤ W` a subspace, of degrees `(dim U + 1) T₀^(dim U) (2T₁)`
and `T₀^(dim U)`. This file shows that, under the hypotheses of the rank argument, no proper one
satisfies this inequality:

* for `U × 𝔾ₘ` with `e₀ ∈ U ≠ W` (so `ℓ* = 0`) it follows from the count
  `TauCeti.mul_pow_lt_mul_ncard_image_mkQ_waldschmidtPoint` on the residual subspace;
* for `U × 𝔾ₘ` with `e₀ ∉ U` (so `ℓ* = 1`) it follows from that count applied to `U + K e₀`,
  together with `S₀ + 1 ≥ 2 T₀`;
* for `U × {1}` (so `ℓ* = 1`) it follows from `(S₀ + 1) #S > (m + 1) T₀^m (2T₁)`, which the
  residual inequality transfers to `(S₀ + 1) #Σ₀ > (d + 1) T₀^d (2T₁)`. Two points of `Σ₀` in the
  same coset of `U × {1}` differ by an exponent vector `v` with `α^v = 1`; when the `α_j` have
  multiplicative rank at least `m - 1` these lie on a line, and since `‖s‖∞ < T₀ / 4` on `S` a
  coset meets `Σ₀` in at most `T₀` points. For `U = 0` the cosets are single points, because the
  grid point map is injective on `Σ₀` when `β₀ ≠ 0` or `(S - S)[2]` meets the line through the
  coefficient vector `c = (β₁, …, β_{m-1}, -1)` only in `0` (`TauCeti.injOn_waldschmidtPoint`).

The zero estimate itself is not proved here.

## Main results

* `TauCeti.mul_pow_lt_add_one_mul_mul_pow_mul_ncard_image_mkQ_waldschmidtPoint`: for every
  subspace `U`, `(d + 1) T₀^d < (S₀ + 1) (dim U + 1) T₀^(dim U) #π_U(Σ₀ · y)`; for `U ≤ W` with
  `e₀ ∉ U` this says that `U × 𝔾ₘ` violates Philippon's inequality.
* `TauCeti.mul_pow_mul_lt_add_one_mul_ncard_image_mul_pow`: for every subspace `U`,
  `(d + 1) T₀^d (2T₁) < (S₀ + 1) #((Σ₀ + U × {1}) / (U × {1})) T₀^(dim U)`, that is, `U × {1}`
  violates Philippon's inequality.

## References

* M. Waldschmidt, *Diophantine Approximation on Linear Algebraic Groups*, Springer (2000),
  Chapter 5 (by D. Roy) and §9.2.3, Proposition 9.16.
* P. Philippon, *Lemmes de zéros dans les groupes algébriques commutatifs*, Bull. Soc. Math.
  France 114 (1986), 355–383.
-/

public section

open Module Set
open scoped Pointwise

namespace TauCeti

variable {n : ℕ} {K : Type*} [Field K]

/-- The inequality `(d + 1) #π_V(S) ≤ (m + 1) T₀^(m-d)` of a residual subspace `V` of dimension `d`
turns `(m + 1) T₀^m x < y #S` into `(d + 1) T₀^d x < y #((S - S) ∩ V)`, because each class of `S`
modulo `V` is a translate of a subset of `(S - S) ∩ V`. -/
private theorem mul_pow_mul_lt_mul_ncard_sub_inter {S : Set (Fin (n + 1) → ℤ)} {T₀ x y : ℕ}
    {V : Submodule K (Fin (n + 1) → K)}
    (hV : (finrank K V + 1) * ((fun s ↦ V.mkQ fun i ↦ (s i : K)) '' S).ncard ≤
      (n + 2) * T₀ ^ (n + 1 - finrank K V))
    (hcard : (n + 2) * T₀ ^ (n + 1) * x < y * S.ncard) :
    (finrank K V + 1) * T₀ ^ finrank K V * x <
      y * ((S - S) ∩ {s | (fun i ↦ (s i : K)) ∈ V}).ncard := by
  set d := finrank K V
  have hS : S.Finite := finite_of_ncard_pos (Nat.pos_of_ne_zero fun h ↦ by simp [h] at hcard)
  have hcount := ncard_image_le_ncard_image_mkQ_mul_ncard_image_sub_inter (AddMonoidHom.id _) hS V
  rw [AddMonoidHom.coe_id, image_id, image_id] at hcount
  have hd : d ≤ n + 1 := (Submodule.finrank_le V).trans_eq (by simp)
  have hpow : T₀ ^ (n + 1) = T₀ ^ (n + 1 - d) * T₀ ^ d := by
    rw [← pow_add]
    congr 1
    lia
  refine Nat.lt_of_mul_lt_mul_left (a := (n + 2) * T₀ ^ (n + 1 - d)) ?_
  calc (n + 2) * T₀ ^ (n + 1 - d) * ((d + 1) * T₀ ^ d * x)
      = (d + 1) * ((n + 2) * T₀ ^ (n + 1) * x) := by rw [hpow]; ring
    _ < (d + 1) * (y * S.ncard) := Nat.mul_lt_mul_of_pos_left hcard d.succ_pos
    _ ≤ y * ((d + 1) * ((fun s ↦ V.mkQ fun i ↦ (s i : K)) '' S).ncard *
          ((S - S) ∩ {s | (fun i ↦ (s i : K)) ∈ V}).ncard) := by
        rw [mul_left_comm, mul_assoc]
        exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hcount)
    _ ≤ (n + 2) * T₀ ^ (n + 1 - d) * (y * ((S - S) ∩ {s | (fun i ↦ (s i : K)) ∈ V}).ncard) := by
        rw [mul_left_comm]
        exact Nat.mul_le_mul_right _ hV

/-- If `S` is nonempty and finite, the set `(S - S) ∩ V` is finite and contains `0`. -/
private theorem finite_and_nonempty_sub_inter {S : Set (Fin (n + 1) → ℤ)} (hS : 0 < S.ncard)
    (V : Submodule K (Fin (n + 1) → K)) :
    ((S - S) ∩ {s | (fun i ↦ (s i : K)) ∈ V}).Finite ∧
      ((S - S) ∩ {s | (fun i ↦ (s i : K)) ∈ V}).Nonempty := by
  have hfin : S.Finite := finite_of_ncard_pos hS
  obtain ⟨s, hs⟩ := (ncard_pos hfin).mp hS
  exact ⟨(hfin.sub hfin).inter_of_left _, 0, ⟨s, hs, s, hs, sub_self s⟩, by
    simp only [Set.mem_ofPred_eq, Pi.zero_apply, Int.cast_zero]
    exact V.zero_mem⟩

/-- The residual count in the form `(d + 1) T₀^d ≤ (d' + 1) T₀^(d') #π_{W'}(Σ₀ · y)`, for every
subspace `W'` of `W = V · y + K e₀` containing `e₀`, of dimension `d'`; for `W' = W` both sides
are `(d + 1) T₀^d`. -/
private theorem mul_pow_le_mul_pow_mul_ncard_image_mkQ_waldschmidtPoint (b : Fin (n + 1) → K)
    {S : Set (Fin (n + 1) → ℤ)} (hS : 0 < S.ncard) {T₀ : ℕ}
    {V : Submodule K (Fin (n + 1) → K)}
    (hV : IsWaldschmidtResidual (Fin.snoc (fun k : Fin n ↦ b k.succ) (-1)) S T₀ V)
    {W' : Submodule K (Fin (n + 1) → K)} (he₀ : Pi.single 0 1 ∈ W')
    (hW' : W' ≤ V.map (waldschmidtPointMap b) ⊔ K ∙ Pi.single 0 1) :
    (finrank K V + 1) * T₀ ^ finrank K V ≤
      (finrank K W' + 1) * T₀ ^ finrank K W' * ((fun s ↦ W'.mkQ (waldschmidtPoint b s)) ''
        ((S - S) ∩ {s | (fun i ↦ (s i : K)) ∈ V})).ncard := by
  obtain ⟨hAfin, hAne⟩ := finite_and_nonempty_sub_inter hS V
  have hdW' : finrank K W' ≤ finrank K V :=
    finrank_map_waldschmidtPointMap_sup b hV.mem ▸ Submodule.finrank_mono hW'
  rcases hW'.lt_or_eq with hlt | rfl
  · have h := mul_pow_lt_mul_ncard_image_mkQ_waldschmidtPoint b (finite_of_ncard_pos hS) hV he₀
      hlt one_ne_zero
    rw [one_nsmul] at h
    calc (finrank K V + 1) * T₀ ^ finrank K V
        = (finrank K V + 1) * T₀ ^ (finrank K V - finrank K W') * T₀ ^ finrank K W' := by
          rw [mul_assoc, ← pow_add, Nat.sub_add_cancel hdW']
      _ ≤ (finrank K W' + 1) * ((fun s ↦ W'.mkQ (waldschmidtPoint b s)) ''
            ((S - S) ∩ {s | (fun i ↦ (s i : K)) ∈ V})).ncard * T₀ ^ finrank K W' :=
          Nat.mul_le_mul_right _ h.le
      _ = _ := by ring
  · rw [finrank_map_waldschmidtPointMap_sup b hV.mem]
    exact Nat.le_mul_of_pos_right _ ((hAne.image _).ncard_pos (hAfin.image _))

/-- The case `U ≤ W = V · y + K e₀` of
`TauCeti.mul_pow_lt_add_one_mul_mul_pow_mul_ncard_image_mkQ_waldschmidtPoint`. -/
private theorem mul_pow_lt_add_one_mul_mul_pow_mul_ncard_image_mkQ_waldschmidtPoint_of_le
    [CharZero K] (b : Fin (n + 1) → K) {S : Set (Fin (n + 1) → ℤ)} {T₀ T₁ S₀ : ℕ}
    (hT₀ : 0 < T₀) (hT₁ : 0 < T₁) (hS₀ : 2 * T₀ ≤ S₀ + 1)
    (hcard : (n + 2) * T₀ ^ (n + 1) * (2 * T₁) < (S₀ + 1) * S.ncard)
    (hb : b 0 ≠ 0 ∨ ∀ v ∈ 2 • (S - S),
      (fun i ↦ (v i : K)) ∈ K ∙ Fin.snoc (fun k : Fin n ↦ b k.succ) (-1) → v = 0)
    {V : Submodule K (Fin (n + 1) → K)}
    (hV : IsWaldschmidtResidual (Fin.snoc (fun k : Fin n ↦ b k.succ) (-1)) S T₀ V)
    {U : Submodule K (Fin (n + 1) → K)}
    (hU : U ≤ V.map (waldschmidtPointMap b) ⊔ K ∙ Pi.single 0 1) :
    (finrank K V + 1) * T₀ ^ finrank K V <
      (S₀ + 1) * ((finrank K U + 1) * T₀ ^ finrank K U *
        ((fun s ↦ U.mkQ (waldschmidtPoint b s)) ''
          ((S - S) ∩ {s | (fun i ↦ (s i : K)) ∈ V})).ncard) := by
  set A := (S - S) ∩ {s | (fun i ↦ (s i : K)) ∈ V}
  have hpos : 0 < S.ncard := Nat.pos_of_ne_zero fun h ↦ by simp [h] at hcard
  obtain ⟨hAfin, hAne⟩ := finite_and_nonempty_sub_inter hpos V
  have hNU : 0 < ((fun s ↦ U.mkQ (waldschmidtPoint b s)) '' A).ncard :=
    (hAne.image _).ncard_pos (hAfin.image _)
  by_cases he : Pi.single 0 1 ∈ U
  · -- `e₀ ∈ U`: the residual count on `U`, and `S₀ + 1 ≥ 2`.
    have h := mul_pow_le_mul_pow_mul_ncard_image_mkQ_waldschmidtPoint b hpos hV he hU
    have hX : 0 < (finrank K U + 1) * T₀ ^ finrank K U *
        ((fun s ↦ U.mkQ (waldschmidtPoint b s)) '' A).ncard :=
      Nat.mul_pos (Nat.mul_pos (finrank K U).succ_pos (pow_pos hT₀ _)) hNU
    exact h.trans_lt (lt_mul_of_one_lt_left hX (by omega))
  rcases (finrank K U).eq_zero_or_pos with h0 | h0
  · -- `U = 0`: the classes are single points, and `(S₀ + 1) #A > (d + 1) T₀^d (2T₁)`.
    have hinj : InjOn (fun s ↦ U.mkQ (waldschmidtPoint b s)) A := fun s hs t ht hst ↦
      injOn_waldschmidtPoint (A := S - S)
        (by rwa [sub_eq_add_neg (S - S), neg_sub, ← two_nsmul]) hs.1 ht.1
        (by simpa [Submodule.finrank_eq_zero.mp h0, Submodule.Quotient.eq, sub_eq_zero] using hst)
    rw [hinj.ncard_image, h0, pow_zero, mul_one, zero_add, one_mul]
    exact (Nat.le_mul_of_pos_right _ (by omega)).trans_lt
      (mul_pow_mul_lt_mul_ncard_sub_inter hV.mul_ncard_image_mkQ_le hcard)
  · -- `e₀ ∉ U ≠ 0`: the residual count on `U + K e₀`, `dim U + 2 < 2 (dim U + 1)` and
    -- `S₀ + 1 ≥ 2 T₀`; modulo `U + K e₀` there are at most as many classes as modulo `U`.
    have h := mul_pow_le_mul_pow_mul_ncard_image_mkQ_waldschmidtPoint b hpos hV
      (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _))
      (sup_le hU ((Submodule.span_singleton_le_iff_mem _ _).2
        (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _))))
    rw [Submodule.finrank_sup_span_singleton he] at h
    have hle : ((fun s ↦ (U ⊔ K ∙ Pi.single 0 1).mkQ (waldschmidtPoint b s)) '' A).ncard ≤
        ((fun s ↦ U.mkQ (waldschmidtPoint b s)) '' A).ncard := by
      have : (fun s ↦ (U ⊔ K ∙ Pi.single 0 1).mkQ (waldschmidtPoint b s)) '' A =
          Submodule.factor le_sup_left '' ((fun s ↦ U.mkQ (waldschmidtPoint b s)) '' A) := by
        rw [image_image]
        simp only [Submodule.factor_mk]
      rw [this]
      exact ncard_image_le (hAfin.image _)
    refine h.trans_lt ?_
    calc (finrank K U + 1 + 1) * T₀ ^ (finrank K U + 1) *
          ((fun s ↦ (U ⊔ K ∙ Pi.single 0 1).mkQ (waldschmidtPoint b s)) '' A).ncard
        ≤ (finrank K U + 1 + 1) * T₀ ^ (finrank K U + 1) *
          ((fun s ↦ U.mkQ (waldschmidtPoint b s)) '' A).ncard := Nat.mul_le_mul_left _ hle
      _ < (2 * (finrank K U + 1)) * T₀ ^ (finrank K U + 1) *
          ((fun s ↦ U.mkQ (waldschmidtPoint b s)) '' A).ncard :=
        Nat.mul_lt_mul_of_pos_right (Nat.mul_lt_mul_of_pos_right (by omega) (pow_pos hT₀ _)) hNU
      _ = 2 * T₀ * ((finrank K U + 1) * T₀ ^ finrank K U *
          ((fun s ↦ U.mkQ (waldschmidtPoint b s)) '' A).ncard) := by ring
      _ ≤ _ := Nat.mul_le_mul_right _ hS₀

/-- **The subgroups `U × 𝔾ₘ` are no obstruction.** Let `V` be a residual subspace of dimension
`d` for `c = (β₁, …, β_{m-1}, -1)` (`TauCeti.IsWaldschmidtResidual`), set `Σ₀ = (S - S) ∩ V`,
and suppose that `T₀, T₁ ≥ 1`, `S₀ + 1 ≥ 2 T₀`, `(S₀ + 1) #S > (m + 1) T₀^m (2T₁)`, and that
`β₀ ≠ 0` or `(S - S)[2]` meets the line `K c` only in `0`. Then for every subspace `U`, the grid
points of `Σ₀` modulo `U` satisfy

`(d + 1) T₀^d < (S₀ + 1) (dim U + 1) T₀^(dim U) #π_U(Σ₀ · y)`.

For `U ≤ W = V · y + K e₀` with `e₀ ∉ U`, after multiplying by `2T₁`, this says that the subgroup
`U × 𝔾ₘ` of `W × 𝔾ₘ`, to which the derivation `(e₀, 1)` is not tangent, violates Philippon's
inequality. (When `e₀ ∈ U ≠ W` the stronger bound without the factor `S₀ + 1` follows from
`TauCeti.mul_pow_lt_mul_ncard_image_mkQ_waldschmidtPoint`.) -/
theorem mul_pow_lt_add_one_mul_mul_pow_mul_ncard_image_mkQ_waldschmidtPoint [CharZero K]
    (b : Fin (n + 1) → K) {S : Set (Fin (n + 1) → ℤ)} {T₀ T₁ S₀ : ℕ}
    (hT₀ : 0 < T₀) (hT₁ : 0 < T₁) (hS₀ : 2 * T₀ ≤ S₀ + 1)
    (hcard : (n + 2) * T₀ ^ (n + 1) * (2 * T₁) < (S₀ + 1) * S.ncard)
    (hb : b 0 ≠ 0 ∨ ∀ v ∈ 2 • (S - S),
      (fun i ↦ (v i : K)) ∈ K ∙ Fin.snoc (fun k : Fin n ↦ b k.succ) (-1) → v = 0)
    {V : Submodule K (Fin (n + 1) → K)}
    (hV : IsWaldschmidtResidual (Fin.snoc (fun k : Fin n ↦ b k.succ) (-1)) S T₀ V)
    (U : Submodule K (Fin (n + 1) → K)) :
    (finrank K V + 1) * T₀ ^ finrank K V <
      (S₀ + 1) * ((finrank K U + 1) * T₀ ^ finrank K U *
        ((fun s ↦ U.mkQ (waldschmidtPoint b s)) ''
          ((S - S) ∩ {s | (fun i ↦ (s i : K)) ∈ V})).ncard) := by
  set W := V.map (waldschmidtPointMap b) ⊔ K ∙ Pi.single 0 1
  set A := (S - S) ∩ {s | (fun i ↦ (s i : K)) ∈ V}
  have hle := mul_pow_lt_add_one_mul_mul_pow_mul_ncard_image_mkQ_waldschmidtPoint_of_le b hT₀ hT₁
    hS₀ hcard hb hV (U := U ⊓ W) inf_le_right
  -- On the grid points, which lie in `W`, the classes modulo `U` and `U ⊓ W` agree.
  have hW (s : Fin (n + 1) → ℤ) (hs : s ∈ A) : waldschmidtPoint b s ∈ W := by
    rw [← waldschmidtPointMap_intCast]
    exact Submodule.mem_sup_left (Submodule.mem_map_of_mem hs.2)
  have hN : ((fun s ↦ U.mkQ (waldschmidtPoint b s)) '' A).ncard =
      ((fun s ↦ (U ⊓ W).mkQ (waldschmidtPoint b s)) '' A).ncard := by
    have : (fun s ↦ U.mkQ (waldschmidtPoint b s)) '' A =
        Submodule.factor inf_le_left '' ((fun s ↦ (U ⊓ W).mkQ (waldschmidtPoint b s)) '' A) := by
      rw [image_image]
      simp only [Submodule.factor_mk]
    rw [this, InjOn.ncard_image]
    rintro _ ⟨s, hs, rfl⟩ _ ⟨t, ht, rfl⟩ hst
    beta_reduce at hst ⊢
    rw [Submodule.factor_mk, Submodule.factor_mk, Submodule.mkQ_apply, Submodule.mkQ_apply,
      Submodule.Quotient.eq] at hst
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
    exact Submodule.mem_inf.2 ⟨hst, W.sub_mem (hW s hs) (hW t ht)⟩
  rw [hN]
  refine hle.trans_le (Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ ?_))
  have hdim : finrank K ↥(U ⊓ W) ≤ finrank K U := Submodule.finrank_mono inf_le_left
  exact Nat.mul_le_mul (by omega) (Nat.pow_le_pow_right hT₀ hdim)

/-- **The subgroups `U × {1}` are no obstruction.** Let `V` satisfy the residual inequality
`(d + 1) #π_V(S) ≤ (m + 1) T₀^(m-d)`, where `d = dim V`, and set `Σ₀ = (S - S) ∩ V`. Suppose
that `α₁, …, αₘ` generate a subgroup of `Kˣ` of rank at least `m - 1`, that `‖s‖∞ < T₀ / 4` on `S`,
that `(S₀ + 1) #S > (m + 1) T₀^m (2T₁)`, and that `β₀ ≠ 0` or `(S - S)[2]` meets the line through
`c = (β₁, …, β_{m-1}, -1)` only in `0`. Then for every subspace `U`, the classes of the points
`(s · y, α^s)`, `s ∈ Σ₀`, modulo `U × {1}` satisfy

`(d + 1) T₀^d (2T₁) < (S₀ + 1) · #{(π_U(s · y), α^s) : s ∈ Σ₀} · T₀^(dim U)`.

For `U ≤ W = V · y + K e₀` this says that the subgroup `U × {1}` of `W × 𝔾ₘ`, to which the
derivation `(e₀, 1)` is not tangent, violates Philippon's inequality. -/
theorem mul_pow_mul_lt_add_one_mul_ncard_image_mul_pow [CharZero K] (b : Fin (n + 1) → K)
    (α : Fin (n + 1) → Kˣ)
    (hα : n + 1 ≤ finrank ℤ (Submodule.span ℤ (range fun j ↦ Additive.ofMul (α j))) + 1)
    {S : Set (Fin (n + 1) → ℤ)} {T₀ T₁ S₀ : ℕ} (hS : ∀ s ∈ S, ∀ i, 4 * |s i| < T₀)
    (hcard : (n + 2) * T₀ ^ (n + 1) * (2 * T₁) < (S₀ + 1) * S.ncard)
    (hb : b 0 ≠ 0 ∨ ∀ v ∈ 2 • (S - S),
      (fun i ↦ (v i : K)) ∈ K ∙ Fin.snoc (fun k : Fin n ↦ b k.succ) (-1) → v = 0)
    {V : Submodule K (Fin (n + 1) → K)}
    (hV : (finrank K V + 1) * ((fun s ↦ V.mkQ fun i ↦ (s i : K)) '' S).ncard ≤
      (n + 2) * T₀ ^ (n + 1 - finrank K V))
    (U : Submodule K (Fin (n + 1) → K)) :
    (finrank K V + 1) * T₀ ^ finrank K V * (2 * T₁) <
      (S₀ + 1) * ((fun s ↦ (U.mkQ (waldschmidtPoint b s), ∏ j, α j ^ s j)) ''
        ((S - S) ∩ {s | (fun i ↦ (s i : K)) ∈ V})).ncard * T₀ ^ finrank K U := by
  set A := (S - S) ∩ {s | (fun i ↦ (s i : K)) ∈ V}
  set g := fun s ↦ (U.mkQ (waldschmidtPoint b s), ∏ j, α j ^ s j)
  have hpos : 0 < S.ncard := Nat.pos_of_ne_zero fun h ↦ by simp [h] at hcard
  have hA := mul_pow_mul_lt_mul_ncard_sub_inter hV hcard
  obtain ⟨s₀, hs₀⟩ := (ncard_pos (finite_of_ncard_pos hpos)).mp hpos
  have hT₀ : 0 < T₀ := by
    have := hS s₀ hs₀ 0
    have := abs_nonneg (s₀ 0)
    omega
  rcases (finrank K U).eq_zero_or_pos with hU | hU
  · -- For `U = 0` the classes are single points, as the grid point map is injective on `A`.
    have hU' : U = ⊥ := Submodule.finrank_eq_zero.mp hU
    have hinj : InjOn g A := fun s hs t ht hst ↦
      injOn_waldschmidtPoint (A := S - S)
        (by rwa [sub_eq_add_neg (S - S), neg_sub, ← two_nsmul]) hs.1 ht.1
        (by simpa [g, hU', Submodule.Quotient.eq, sub_eq_zero] using congrArg Prod.fst hst)
    rwa [hinj.ncard_image, hU, pow_zero, mul_one]
  · -- Otherwise each class meets `A` in at most `T₀` points.
    have hR : ∀ s ∈ A, ∀ t ∈ A, ∀ i, |s i - t i| ≤ ((T₀ - 1 : ℕ) : ℤ) := by
      have hbox (s : Fin (n + 1) → ℤ) (hs : s ∈ S) (i : Fin (n + 1)) :
          -(T₀ : ℤ) < 4 * s i ∧ 4 * s i < T₀ := by
        have := hS s hs i
        rcases abs_cases (s i) with h | h <;> omega
      rintro _ ⟨⟨s₁, hs₁, s₂, hs₂, rfl⟩, -⟩ _ ⟨⟨s₃, hs₃, s₄, hs₄, rfl⟩, -⟩ i
      have := hbox s₁ hs₁ i
      have := hbox s₂ hs₂ i
      have := hbox s₃ hs₃ i
      have := hbox s₄ hs₄ i
      simp only [Pi.sub_apply]
      rw [abs_le]
      omega
    have hfib := ncard_le_ncard_image_mul_add_one α hα g (fun s _ t _ h ↦ congrArg Prod.snd h) hR
    rw [Nat.sub_add_cancel hT₀] at hfib
    calc _ < (S₀ + 1) * A.ncard := hA
      _ ≤ (S₀ + 1) * ((g '' A).ncard * T₀) := Nat.mul_le_mul_left _ hfib
      _ ≤ (S₀ + 1) * (g '' A).ncard * T₀ ^ finrank K U := by
        rw [← mul_assoc]
        exact Nat.mul_le_mul_left _ (Nat.le_self_pow hU.ne' _)

end TauCeti
