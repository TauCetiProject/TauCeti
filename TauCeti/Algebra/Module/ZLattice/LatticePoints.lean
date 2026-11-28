/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.ZLattice.SuccessiveMinima
import Mathlib.Data.ZMod.Defs
import TauCeti.Analysis.Convex.Gauge.Basic

/-!
# Lattice points in a convex body, by the successive minima

Let `L` be a discrete spanning lattice in a real normed space `E` of dimension `d`, and let `K` be
a convex body symmetric about `0` with `0` in its interior, with successive minima
`λ₀ ≤ ⋯ ≤ λ_{d-1}` (`ZLattice.successiveMin`, indexed from zero). Henk's bounds on the number of
points of `L` in `K` (boundary points and the origin included) are

```text
|L ∩ K| ≤ (⌊2 / λ₀⌋ + 1) ^ d,        |L ∩ K| < 2 ^ (d - 1) ∏_{i < d} (⌊2 / λᵢ⌋ + 1)   (d ≥ 2).
```

Both rest on a pigeonhole count. If a map `f` to a finite set `H` identifies two points `x, y` of a
subset `S` of an additive group only when `x - y` lies in a set `T`, then `|S| ≤ |H| · |T|`.
Taking for `f` the quotient map by a subgroup `N` of finite index gives the *index count*
`|S| ≤ [G : N] · |T|`; taking the coordinates modulo `q` in a `ℤ`-basis of `n` elements gives the
*congruence-free count* `|S| ≤ q ^ n` when no two points of `S` differ by an element of `q • G`.
Two points of `L ∩ K` differ by a point of `2 • K`, since `K` is symmetric and convex.

* For the first minimum, `q = ⌊2 / λ₀⌋ + 1` satisfies `2 / q < λ₀`, so `q • L` meets `2 • K` only
  in `0`, and the congruence-free count applies.
* For all the minima, take a `ℤ`-basis `b` of `L` whose real flags contain the lattice vectors
  below each minimum (`ZLattice.exists_basis_mem_flag_of_gauge_lt_successiveMin`), put
  `qᵢ = ⌊2 / λᵢ⌋ + 1`, and round the `qᵢ` up to a divisor chain `nᵢ` with `qᵢ ≤ nᵢ < 2 qᵢ`,
  `n_{d-1} = q_{d-1}` and `nⱼ ∣ nᵢ` for `i ≤ j` (powers of two times `q_{d-1}`). If two points of
  `L ∩ K` have coordinates congruent modulo every `nᵢ`, their difference `v ∈ 2 • K` is `0`:
  otherwise, at the largest index `j` with a nonzero coordinate, `v = nⱼ • w` with `w` outside the
  `j`-th flag, so `gauge K w ≥ λⱼ` and `gauge K v ≥ nⱼ λⱼ ≥ qⱼ λⱼ > 2`. Hence
  `|L ∩ K| ≤ ∏ nᵢ < 2 ^ (d - 1) ∏ qᵢ`.

## Main results

* `Set.encard_le_natCard_mul_encard_of_sub_mem`: the pigeonhole count through a map.
* `AddSubgroup.encard_le_index_mul_encard`: the index count.
* `Module.Basis.encard_le_pow_of_sub_eq_nsmul`: the congruence-free count.
* `AddSubgroup.encard_inter_le_relIndex_mul_encard_inter_two_smul`: the sublattice count
  `|L ∩ K| ≤ [L : M] · |M ∩ 2 • K|` for a finite relative index `[L : M]`.
* `ZLattice.natCard_inter_le_pow`: Henk's bound by the first minimum.
* `Nat.exists_dvd_chain_of_antitone` and `Finset.prod_lt_two_pow_mul_prod`: the divisor chain
  rounding and its product bound.
* `ZLattice.natCard_inter_lt_two_pow_mul_prod`: Henk's bound by all the successive minima.

## References

* M. Henk, *Successive minima and lattice points*, Rend. Circ. Mat. Palermo (2) Suppl. 70 (2002),
  377–384, Theorem 1.5, inequality (1.3), Lemma 2.1 and (2.1)–(2.5); arXiv:math/0204158.
-/

public section

open Module Set
open scoped Pointwise

/-! ### Counting through a map to a finite set -/

/-- **Counting through a map to a finite set.** If `f` identifies two points `x, y` of `S` only
when `x - y ∈ T`, then `|S| ≤ |H| · |T|`: in each fibre of `f`, the points of `S` are determined
by their differences from one of them. No finiteness of `S` or `T` is assumed. -/
theorem Set.encard_le_natCard_mul_encard_of_sub_mem {G H : Type*} [AddGroup G] [Finite H]
    (f : G → H) (T : Set G) {S : Set G} (hS : ∀ x ∈ S, ∀ y ∈ S, f x = f y → x - y ∈ T) :
    S.encard ≤ Nat.card H * T.encard := by
  -- `r` picks a point of `S` in every fibre of `f` that meets `S`.
  set r := Function.invFunOn f S
  have hr (x : G) (hx : x ∈ S) : r (f x) ∈ S ∧ f (r (f x)) = f x :=
    ⟨Function.invFunOn_mem ⟨x, hx, rfl⟩, Function.invFunOn_eq ⟨x, hx, rfl⟩⟩
  calc S.encard ≤ ((univ : Set H) ×ˢ T).encard := by
        refine encard_le_encard_of_injOn (f := fun x ↦ (f x, x - r (f x)))
          (fun x hx ↦ ⟨mem_univ _, hS x hx _ (hr x hx).1 (hr x hx).2.symm⟩) ?_
        intro x _ y _ hxy
        simp only [Prod.mk.injEq] at hxy
        rw [hxy.1, sub_left_inj] at hxy
        exact hxy.2
    _ = Nat.card H * T.encard := by rw [encard_prod, encard_univ, ENat.card_eq_coe_natCard]

/-- **The index count.** For a subgroup `N` of finite index and sets `S, T` such that `x - y ∈ N`
implies `x - y ∈ T` for `x, y ∈ S`, `|S| ≤ [G : N] · |T|`. The group need not be commutative: the
classes of `x - y ∈ N` are the right cosets, which number `[G : N]` like the left ones. -/
theorem AddSubgroup.encard_le_index_mul_encard {G : Type*} [AddGroup G] (N : AddSubgroup G)
    [N.FiniteIndex] (T : Set G) {S : Set G} (hS : ∀ x ∈ S, ∀ y ∈ S, x - y ∈ N → x - y ∈ T) :
    S.encard ≤ N.index * T.encard :=
  encard_le_natCard_mul_encard_of_sub_mem (fun x ↦ ((-x : G) : G ⧸ N)) T
    fun x hx y hy hxy ↦ hS x hx y hy <| by
      rwa [QuotientAddGroup.eq, neg_neg, ← sub_eq_add_neg] at hxy

/-- **The congruence-free count.** If `G` has a `ℤ`-basis indexed by `ι`, `q ≠ 0`, and no two
distinct points of `S` differ by an element of `q • G`, then `|S| ≤ q ^ |ι|`. -/
theorem Module.Basis.encard_le_pow_of_sub_eq_nsmul {G ι : Type*} [AddCommGroup G] [Fintype ι]
    (b : Basis ι ℤ G) {q : ℕ} (hq : q ≠ 0) {S : Set G}
    (hS : ∀ x ∈ S, ∀ y ∈ S, ∀ z : G, x - y = q • z → x = y) :
    S.encard ≤ q ^ Fintype.card ι := by
  have : NeZero q := ⟨hq⟩
  have h := encard_le_natCard_mul_encard_of_sub_mem (fun x : G ↦ fun i ↦ (b.repr x i : ZMod q))
    {0} (S := S) fun x hx y hy hxy ↦ ?_
  · rwa [encard_singleton, mul_one, Nat.card_pi, Finset.prod_congr rfl fun i _ ↦ Nat.card_zmod q,
      Finset.prod_const, Finset.card_univ, Nat.cast_pow] at h
  -- Every coordinate of `x - y` is divisible by `q`, so `x - y = q • z`.
  have hdvd (i : ι) : (q : ℤ) ∣ b.repr (x - y) i := by
    have := congrFun hxy i
    rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at this
    rw [map_sub, Finsupp.sub_apply, ← dvd_neg, neg_sub]
    exact this
  refine mem_singleton_iff.2 (sub_eq_zero.2 (hS x hx y hy
    (b.equivFun.symm fun i ↦ b.repr (x - y) i / q) (b.equivFun.injective ?_)))
  ext i
  rw [← natCast_zsmul, map_zsmul, LinearEquiv.apply_symm_apply, Pi.smul_apply, smul_eq_mul,
    Basis.equivFun_apply, Int.mul_ediv_cancel' (hdvd i)]

/-- Two points of a convex set symmetric about `0` differ by a point of its double. -/
private theorem sub_mem_two_smul {E : Type*} [AddCommGroup E] [Module ℝ E] {K : Set E}
    (hKc : Convex ℝ K) (hKs : ∀ x ∈ K, -x ∈ K) {x y : E} (hx : x ∈ K) (hy : y ∈ K) :
    x - y ∈ (2 : ℝ) • K := by
  refine ⟨(1 / 2 : ℝ) • x + (1 / 2 : ℝ) • (-y),
    hKc hx (hKs y hy) (by norm_num) (by norm_num) (by norm_num), ?_⟩
  simp only [smul_add, smul_smul, smul_neg]
  norm_num [sub_eq_add_neg]

/-- The points of a subgroup `p` in a set `K`, counted in `E` or in `p`. -/
private theorem encard_inter_eq_encard_setOf {E S : Type*} [SetLike S E] (p : S) (K : Set E) :
    ((p : Set E) ∩ K).encard = {x : p | (x : E) ∈ K}.encard := by
  rw [← Subtype.val_injective.encard_image]
  congr 1
  ext x
  exact ⟨fun ⟨hxp, hxK⟩ ↦ ⟨⟨x, hxp⟩, hxK, rfl⟩, fun ⟨y, hy, hyx⟩ ↦ hyx ▸ ⟨y.property, hy⟩⟩

/-- **The sublattice count.** Let `K` be a convex set symmetric about `0`, and `L, M` additive
subgroups with `M ∩ L` of finite index `[L : M]` in `L`. Then `|L ∩ K| ≤ [L : M] · |M ∩ 2 • K|`: two
points of `L ∩ K` in one coset of `M ∩ L` differ by a point of `M ∩ 2 • K`. -/
theorem AddSubgroup.encard_inter_le_relIndex_mul_encard_inter_two_smul {E : Type*}
    [AddCommGroup E] [Module ℝ E] {L M : AddSubgroup E} (hindex : M.relIndex L ≠ 0)
    {K : Set E} (hKc : Convex ℝ K) (hKs : ∀ x ∈ K, -x ∈ K) :
    ((L : Set E) ∩ K).encard ≤ M.relIndex L * ((M : Set E) ∩ (2 : ℝ) • K).encard := by
  have : (M.addSubgroupOf L).FiniteIndex := ⟨hindex⟩
  have h := (M.addSubgroupOf L).encard_le_index_mul_encard
    {x | (x : E) ∈ (M : Set E) ∩ (2 : ℝ) • K} (S := {x | (x : E) ∈ K})
    fun x hx y hy hxy ↦ ⟨AddSubgroup.mem_addSubgroupOf.1 hxy, sub_mem_two_smul hKc hKs hx hy⟩
  rw [← encard_inter_eq_encard_setOf, ← encard_inter_eq_encard_setOf] at h
  exact h.trans (mul_le_mul_right (encard_le_encard inter_subset_right) _)

namespace ZLattice

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {K : ConvexBody E}

/-- **Henk's bound by the first minimum.** Let `L` be a discrete spanning lattice in a space of
dimension `d ≥ 1` and `K` a convex body symmetric about `0` with `0` in its interior. Then
`|L ∩ K| ≤ (⌊2 / λ₀⌋ + 1) ^ d`: for `q = ⌊2 / λ₀⌋ + 1`, two distinct points of `L ∩ K` cannot
differ by a point of `q • L`, which would lie in `2 • K` and have gauge at most `2 / q < λ₀`. -/
theorem natCard_inter_le_pow (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (hKs : ∀ x ∈ K, -x ∈ K) (hK : 0 ∈ interior (K : Set E)) (hd : 0 < finrank ℝ E) :
    Nat.card ↥((L : Set E) ∩ K) ≤ (⌊2 / successiveMin L K ⟨0, hd⟩⌋₊ + 1) ^ finrank ℝ E := by
  have := ConvexBody.finiteDimensional_of_zero_mem_interior hK
  have := ZLattice.module_free ℝ L
  set m₀ := successiveMin L K ⟨0, hd⟩
  set q := ⌊2 / m₀⌋₊ + 1
  have hm₀ : 0 < m₀ := successiveMin_pos L hK _
  have hq : 2 < q * m₀ := by
    have := Nat.lt_floor_add_one (2 / m₀)
    rw [div_lt_iff₀ hm₀] at this
    exact_mod_cast this
  have h := (Free.chooseBasis ℤ L).encard_le_pow_of_sub_eq_nsmul (q := q) (Nat.add_one_ne_zero _)
    (S := {x : L | (x : E) ∈ (K : Set E)}) fun x hx y hy z hz ↦ ?_
  · rw [← finrank_eq_card_chooseBasisIndex, ZLattice.rank ℝ L, ← encard_inter_eq_encard_setOf,
      ← Nat.cast_pow] at h
    rw [Nat.card_coe_set_eq, ncard_def]
    exact ENat.toNat_le_of_le_natCast h
  -- Otherwise `z ≠ 0` has gauge at most `2 / q < λ₀`.
  by_contra hxy
  have hz0 : (z : E) ≠ 0 := by
    rintro hz0
    rw [Submodule.coe_eq_zero.1 hz0, smul_zero, sub_eq_zero] at hz
    exact hxy hz
  have hv : gauge (K : Set E) (x - y : L) ≤ 2 :=
    gauge_le_of_mem zero_le_two (sub_mem_two_smul K.convex hKs hx hy)
  rw [hz, Submodule.coe_smul_of_tower, ← Nat.cast_smul_eq_nsmul ℝ,
    gauge_smul_of_nonneg (Nat.cast_nonneg _), smul_eq_mul] at hv
  have hgz : 0 < gauge (K : Set E) z := (ConvexBody.gauge_pos_iff hK).2 hz0
  have hle : m₀ ≤ gauge (K : Set E) z := (successiveMin_zero_le_iff L hK hd hgz.le).2
    ⟨z, z.property, hz0, (ConvexBody.gauge_le_iff_mem_smul hK hgz).1 le_rfl⟩
  nlinarith [mul_le_mul_of_nonneg_left hle (Nat.cast_nonneg (α := ℝ) q)]

end ZLattice

/-! ### Rounding to a divisor chain -/

/-- **Rounding to a divisor chain.** Let `q` be a positive antitone function on a preorder, and
`l` an index where `q` is least. Rounding each `q i` up to `q l` times a power of `2` gives `n` with
`q i ≤ n i < 2 q i`, `n l = q l`, and `n j ∣ n i` whenever `i ≤ j`. -/
theorem Nat.exists_dvd_chain_of_antitone {ι : Type*} [Preorder ι] (q : ι → ℕ)
    (hq : ∀ i, 0 < q i) (hanti : Antitone q) (l : ι) (hl : ∀ i, q l ≤ q i) :
    ∃ n : ι → ℕ, (∀ i, q i ≤ n i) ∧ (∀ i, n i < 2 * q i) ∧ n l = q l ∧
      ∀ i j, i ≤ j → n j ∣ n i := by
  classical
  have hex (i : ι) : ∃ k, q i ≤ q l * 2 ^ k :=
    ⟨q i, Nat.lt_two_pow_self.le.trans (Nat.le_mul_of_pos_left _ (hq l))⟩
  refine ⟨fun i ↦ q l * 2 ^ Nat.find (hex i), fun i ↦ Nat.find_spec (hex i), fun i ↦ ?_,
    ?_, fun i j hij ↦ ?_⟩
  · change q l * 2 ^ Nat.find (hex i) < 2 * q i
    rcases h : Nat.find (hex i) with _ | k
    · have := hl i
      have := hq i
      rw [pow_zero, mul_one]
      omega
    · have hk := Nat.find_min (hex i) (m := k) (by omega)
      rw [not_le] at hk
      rw [pow_succ, ← mul_assoc]
      linarith
  · change q l * 2 ^ Nat.find (hex l) = q l
    rw [(Nat.find_eq_zero (hex l)).2 (by simp), pow_zero, mul_one]
  · exact Nat.mul_dvd_mul_left _ (Nat.pow_dvd_pow 2
      (Nat.find_min' (hex j) ((hanti hij).trans (Nat.find_spec (hex i)))))

/-- The product bound for a rounding to a divisor chain: if `n i < 2 q i` for every `i` and
`n l = q l` at one index, then `∏ n i < 2 ^ (|ι| - 1) ∏ q i` as soon as `|ι| ≥ 2`. -/
theorem Finset.prod_lt_two_pow_mul_prod {ι : Type*} [Fintype ι] {n q : ι → ℕ}
    (hn : ∀ i, n i < 2 * q i) {l : ι} (hl : n l = q l) (hcard : 2 ≤ Fintype.card ι) :
    ∏ i, n i < 2 ^ (Fintype.card ι - 1) * ∏ i, q i := by
  classical
  have hq (i : ι) : 0 < q i := by have := hn i; omega
  by_cases hn₀ : ∀ i, 0 < n i
  swap
  · push Not at hn₀
    obtain ⟨i, hi⟩ := hn₀
    rw [Finset.prod_eq_zero (mem_univ i) (Nat.le_zero.1 hi)]
    exact Nat.mul_pos (by positivity) (Finset.prod_pos fun i _ ↦ hq i)
  have hne : (univ.erase l).Nonempty := by
    rw [← Finset.card_pos, Finset.card_erase_of_mem (mem_univ l), Finset.card_univ]
    omega
  rw [← Finset.mul_prod_erase _ _ (mem_univ l), ← Finset.mul_prod_erase _ q (mem_univ l), hl,
    mul_left_comm]
  refine Nat.mul_lt_mul_of_pos_left ?_ (hq l)
  calc ∏ i ∈ univ.erase l, n i < ∏ i ∈ univ.erase l, 2 * q i :=
        Finset.prod_lt_prod_of_nonempty₀ (fun i _ ↦ hn₀ i) (fun i _ ↦ hn i) hne
    _ = 2 ^ (Fintype.card ι - 1) * ∏ i ∈ univ.erase l, q i := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_erase_of_mem (mem_univ l),
          Finset.card_univ]

/-! ### Henk's bound by all the successive minima -/

namespace ZLattice

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {K : ConvexBody E}

/-- The key step of Henk's bound. Let `b` be a `ℤ`-basis of `L` whose real flags contain the
lattice vectors below each minimum, and `n` a divisor chain (`n j ∣ n i` for `i ≤ j`) with
`2 < n i * λ i`. A vector of `L` in `2 • K` whose `i`-th coordinate is divisible by `n i` for every
`i` is `0`: at the largest index `j` with a nonzero coordinate it is `n j • w` with `w` outside the
`j`-th flag, so that its gauge is at least `n j * λ j > 2`. -/
private theorem eq_zero_of_dvd_repr [FiniteDimensional ℝ E] {L : Submodule ℤ E}
    [DiscreteTopology L] [IsZLattice ℝ L] {b : Basis (Fin (finrank ℝ E)) ℤ L}
    (hb : ∀ i, ∀ x ∈ L, gauge (K : Set E) x < successiveMin L K i →
      x ∈ (b.ofZLatticeBasis ℝ L).flag i.castSucc)
    {n : Fin (finrank ℝ E) → ℕ} (hdvd : ∀ i j, i ≤ j → n j ∣ n i)
    (hn : ∀ i, 2 < n i * successiveMin L K i) {v : L} (hv : (v : E) ∈ (2 : ℝ) • (K : Set E))
    (hvn : ∀ i, (n i : ℤ) ∣ b.repr v i) : v = 0 := by
  by_contra hv0
  have hne : (b.repr v).support.Nonempty :=
    Finsupp.support_nonempty_iff.2 (b.repr.map_ne_zero_iff.2 hv0)
  set j := (b.repr v).support.max' hne
  have hj : b.repr v j ≠ 0 := Finsupp.mem_support_iff.1 ((b.repr v).support.max'_mem hne)
  -- Every coordinate of `v` is divisible by `n j`.
  have hdvd' (i : Fin (finrank ℝ E)) : (n j : ℤ) ∣ b.repr v i := by
    rcases le_or_gt i j with hij | hij
    · exact (Int.natCast_dvd_natCast.2 (hdvd i j hij)).trans (hvn i)
    · rw [Finsupp.notMem_support_iff.1 fun h ↦ hij.not_ge ((b.repr v).support.le_max' i h)]
      exact dvd_zero _
  set w : L := b.equivFun.symm fun i ↦ b.repr v i / n j
  have hw (i : Fin (finrank ℝ E)) : b.repr w i = b.repr v i / n j := by
    rw [← Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
  have hvw : v = (n j : ℤ) • w := b.equivFun.injective <| funext fun i ↦ by
    rw [map_zsmul, Pi.smul_apply, smul_eq_mul, Basis.equivFun_apply, Basis.equivFun_apply, hw,
      Int.mul_ediv_cancel' (hdvd' i)]
  -- `w` lies outside the `j`-th flag, so its gauge is at least `λ j`.
  have hwflag : (w : E) ∉ (b.ofZLatticeBasis ℝ L).flag j.castSucc := by
    rw [Basis.mem_flag_iff_repr_eq_zero, not_forall]
    refine ⟨j, fun h ↦ ?_⟩
    rw [Basis.ofZLatticeBasis_repr_apply, hw, Int.cast_eq_zero] at h
    have := h le_rfl
    exact hj (by rw [← Int.mul_ediv_cancel' (hdvd' j), this, mul_zero])
  have hgw : successiveMin L K j ≤ gauge (K : Set E) w :=
    not_lt.1 fun h ↦ hwflag (hb j w w.property h)
  have hgv : gauge (K : Set E) v ≤ 2 := gauge_le_of_mem zero_le_two hv
  rw [hvw, Submodule.coe_smul, ← Int.cast_smul_eq_zsmul ℝ, Int.cast_natCast,
    gauge_smul_of_nonneg (Nat.cast_nonneg _), smul_eq_mul] at hgv
  nlinarith [mul_le_mul_of_nonneg_left hgw (Nat.cast_nonneg (α := ℝ) (n j)), hn j]

/-- **Henk's bound by the successive minima.** Let `L` be a discrete spanning lattice in a space of
dimension `d ≥ 2` and `K` a convex body symmetric about `0` with `0` in its interior, with
successive minima `λ i`. Then `|L ∩ K| < 2 ^ (d - 1) ∏ i, (⌊2 / λ i⌋ + 1)`; the count includes the
boundary points and the origin. -/
theorem natCard_inter_lt_two_pow_mul_prod (L : Submodule ℤ E) [DiscreteTopology L]
    [IsZLattice ℝ L] (hKs : ∀ x ∈ K, -x ∈ K) (hK : 0 ∈ interior (K : Set E))
    (hd : 2 ≤ finrank ℝ E) :
    Nat.card ↥((L : Set E) ∩ K) <
      2 ^ (finrank ℝ E - 1) * ∏ i, (⌊2 / successiveMin L K i⌋₊ + 1) := by
  have := ConvexBody.finiteDimensional_of_zero_mem_interior hK
  set q : Fin (finrank ℝ E) → ℕ := fun i ↦ ⌊2 / successiveMin L K i⌋₊ + 1
  have hanti : Antitone q := fun i j hij ↦ Nat.add_le_add_right (Nat.floor_le_floor
    (div_le_div_of_nonneg_left zero_le_two (successiveMin_pos L hK i)
      (monotone_successiveMin L hK hij))) 1
  set l : Fin (finrank ℝ E) := ⟨finrank ℝ E - 1, by omega⟩
  obtain ⟨n, hqn, hn2, hnl, hdvd⟩ := Nat.exists_dvd_chain_of_antitone q (fun _ ↦ Nat.succ_pos _)
    hanti l fun i ↦ hanti (Fin.le_def.2 (by simp only [l]; omega))
  have : ∀ i, NeZero (n i) := fun i ↦ ⟨(Nat.succ_pos _ |>.trans_le (hqn i)).ne'⟩
  have hn (i : Fin (finrank ℝ E)) : 2 < n i * successiveMin L K i := by
    have h := Nat.lt_floor_add_one (2 / successiveMin L K i)
    rw [div_lt_iff₀ (successiveMin_pos L hK i)] at h
    have : ((⌊2 / successiveMin L K i⌋₊ + 1 : ℕ) : ℝ) ≤ n i := by exact_mod_cast hqn i
    push_cast at this
    nlinarith [successiveMin_pos L hK i]
  obtain ⟨b, hb⟩ := exists_basis_mem_flag_of_gauge_lt_successiveMin L hK
  -- Points of `L ∩ K` with coordinates congruent modulo every `n i` coincide.
  have h := encard_le_natCard_mul_encard_of_sub_mem
    (fun x : L ↦ fun i ↦ (b.repr x i : ZMod (n i))) {0} (S := {x : L | (x : E) ∈ (K : Set E)})
    fun x hx y hy hxy ↦ mem_singleton_iff.2 <| eq_zero_of_dvd_repr hb hdvd hn
      (sub_mem_two_smul K.convex hKs hx hy) fun i ↦ by
        have := congrFun hxy i
        rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at this
        rw [map_sub, Finsupp.sub_apply, ← dvd_neg, neg_sub]
        exact this
  rw [encard_singleton, mul_one, Nat.card_pi, Finset.prod_congr rfl fun i _ ↦ Nat.card_zmod (n i),
    ← encard_inter_eq_encard_setOf] at h
  rw [Nat.card_coe_set_eq, ncard_def]
  refine (ENat.toNat_le_of_le_natCast h).trans_lt ?_
  simpa only [Fintype.card_fin] using
    Finset.prod_lt_two_pow_mul_prod hn2 hnl (by rwa [Fintype.card_fin])

end ZLattice
