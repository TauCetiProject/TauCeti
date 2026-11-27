/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.SetTheory.Cardinal.Partition.Basic
import Mathlib.Order.Interval.Set.InitialSeg
import Mathlib.SetTheory.Cardinal.Arithmetic
import TauCeti.Order.Fin.Tuple
import TauCeti.Order.Hom.Basic

/-!
# End-homogeneous sets

Let `lam` be an infinite cardinal and `c` a colouring of the increasing `(n + 2)`-tuples of a
well-order `J` by at most `lam` colours. If `J` has cardinality at least `(2 ^ lam)⁺`, then some
subset of `J` of cardinality `lam⁺` is end-homogeneous for `c`: on it, the colour of an increasing
tuple does not depend on its last entry. This is the step of the Erdős–Rado theorem
`ℶₙ(κ)⁺ → (κ⁺)ⁿ⁺¹_κ` that raises the exponent by one.

The end-homogeneity is with respect to the order of `J`, not to an order of construction.

## Main results

* `TauCeti.exists_isEndHomogeneousOn`: from `(2 ^ lam)⁺ ≤ #J`, an end-homogeneous set of
  cardinality at least `lam⁺`.
* `TauCeti.exists_forall_eq_of_apply_zero_eq`: the pair form, a set of cardinality at least
  `lam⁺` on which the colour of an increasing pair depends only on its smaller point.

## Implementation notes

The proof is the Erdős–Rado tree argument. For a point `x`, the set of its *tree predecessors* is
defined by well-founded recursion: `y < x` is a tree predecessor of `x` when every increasing tuple
with last entry `y` and earlier entries among the tree predecessors of `x` gets the same colour as
the tuple obtained by replacing `y` with `x`. The tree predecessors of a tree predecessor `y` of
`x` are those of `x` below `y`, so the tree predecessors of any point form an end-homogeneous set.
A point is determined by its tree predecessors together with its colours against them. Enumerating
each branch by an initial segment of `(lam⁺).ord.ToType`, a branch with at most `lam` points
carries at most `lam ^ lam = 2 ^ lam` colour patterns. So if every point had at most `lam` tree
predecessors, `J` would have at most `lam⁺ * 2 ^ lam = 2 ^ lam` points.

## References

* P. Erdős and R. Rado, *A partition calculus in set theory*, Bull. Amer. Math. Soc. 62 (1956).
* D. Marker, *Lectures on Infinitary Model Theory*, Lecture Notes in Logic 46 (2016), proof of
  Theorem 5.5.
-/

public section

universe u

open Cardinal Set
open scoped Ordinal

namespace TauCeti

section Tuples

variable {J : Type*} [LinearOrder J] {n : ℕ}

/-- Replace the last entry of an increasing tuple by a point above its other entries. -/
private def withLast (s : Fin (n + 2) ↪o J) (x : J) (hx : s (Fin.last n).castSucc < x) :
    Fin (n + 2) ↪o J :=
  OrderEmbedding.snoc (Fin.castSuccOrderEmb.trans s) x fun k ↦ by
    simpa using (s.strictMono.monotone (Fin.castSucc_le_castSucc_iff.2 (Fin.le_last k))).trans_lt hx

@[simp]
private theorem withLast_castSucc (s : Fin (n + 2) ↪o J) (x : J)
    (hx : s (Fin.last n).castSucc < x) (k : Fin (n + 1)) :
    withLast s x hx k.castSucc = s k.castSucc := by
  simp [withLast]

@[simp]
private theorem withLast_last (s : Fin (n + 2) ↪o J) (x : J) (hx : s (Fin.last n).castSucc < x) :
    withLast s x hx (Fin.last _) = x := by
  simp [withLast]

end Tuples

section Tree

variable {J D : Type*} [LinearOrder J] [WellFoundedLT J] {n : ℕ}

/-- The *tree predecessors* of `x` for a colouring `c` of increasing `(n + 2)`-tuples: by
well-founded recursion, `y < x` is a tree predecessor of `x` when any two increasing tuples that
agree on their first `n + 1` entries, those entries being tree predecessors of `x`, and end in `y`
and `x` respectively, get the same colour. -/
private def treePred (c : (Fin (n + 2) ↪o J) → D) (x : J) : Set J :=
  {y | wellFounded_lt.fix (C := fun _ ↦ Prop) (fun y IH ↦ y < x ∧
    ∀ s t : Fin (n + 2) ↪o J, (hs : s (Fin.last _) = y) → t (Fin.last _) = x →
      (∀ k : Fin (n + 1), s k.castSucc = t k.castSucc) →
      (∀ k : Fin (n + 1), IH (s k.castSucc) (hs ▸ s.strictMono (Fin.castSucc_lt_last k))) →
      c s = c t) y}

variable {c : (Fin (n + 2) ↪o J) → D} {x y z : J}

private theorem mem_treePred_iff :
    y ∈ treePred c x ↔ y < x ∧
      ∀ s t : Fin (n + 2) ↪o J, s (Fin.last _) = y → t (Fin.last _) = x →
        (∀ k : Fin (n + 1), s k.castSucc = t k.castSucc) →
        (∀ k : Fin (n + 1), s k.castSucc ∈ treePred c x) → c s = c t := by
  rw [treePred, mem_ofPred_eq, WellFounded.fix_eq]
  -- After one unfolding of the recursion, the recursive call `IH (s k.castSucc) _` is the term
  -- `wellFounded_lt.fix _ (s k.castSucc)`, which is membership in `treePred c x` by definition.
  exact Iff.rfl

private theorem lt_of_mem_treePred (hy : y ∈ treePred c x) : y < x :=
  (mem_treePred_iff.1 hy).1

/-- **The tree is a tree.** The tree predecessors of a tree predecessor `y` of `x` are the tree
predecessors of `x` below `y`. -/
private theorem treePred_eq_of_mem (hy : y ∈ treePred c x) :
    treePred c y = treePred c x ∩ Iio y := by
  ext z
  induction z using WellFoundedLT.induction with | _ z IH => ?_
  rw [mem_treePred_iff, mem_inter_iff, mem_treePred_iff, mem_Iio]
  by_cases hzy : z < y
  swap
  · tauto
  have hyx := lt_of_mem_treePred hy
  -- For a tuple ending in `z`, its earlier entries are tree predecessors of `y` exactly when they
  -- are tree predecessors of `x`.
  have hmem {s : Fin (n + 2) ↪o J} (hs : s (Fin.last _) = z) (k : Fin (n + 1)) :
      s k.castSucc ∈ treePred c y ↔ s k.castSucc ∈ treePred c x := by
    have hk : s k.castSucc < z := hs ▸ s.strictMono (Fin.castSucc_lt_last k)
    rw [IH _ hk, mem_inter_iff, mem_Iio, and_iff_left (hk.trans hzy)]
  have hsy {s : Fin (n + 2) ↪o J} (hs : s (Fin.last _) = z) : s (Fin.last n).castSucc < y :=
    (s.strictMono (Fin.castSucc_lt_last _)).trans (hs ▸ hzy)
  -- Moving the last entry from `y` to `x` does not change the colour, since `y` is a tree
  -- predecessor of `x`.
  have hyx' {s : Fin (n + 2) ↪o J} (hs : s (Fin.last _) = z)
      (hsx : ∀ k : Fin (n + 1), s k.castSucc ∈ treePred c x) (t : Fin (n + 2) ↪o J)
      (ht : t (Fin.last _) = x) (hst : ∀ k : Fin (n + 1), s k.castSucc = t k.castSucc) :
      c (withLast s y (hsy hs)) = c t :=
    (mem_treePred_iff.1 hy).2 _ t (by simp) ht (by simpa using hst) (by simpa using hsx)
  refine ⟨fun ⟨_, h⟩ ↦ ⟨⟨hzy.trans hyx, fun s t hs ht hst hsx ↦ ?_⟩, hzy⟩,
    fun ⟨⟨_, h⟩, _⟩ ↦ ⟨hzy, fun s t hs ht hst hsy' ↦ ?_⟩⟩
  · rw [h s (withLast s y (hsy hs)) hs (by simp) (by simp) fun k ↦ (hmem hs k).2 (hsx k)]
    exact hyx' hs hsx t ht hst
  · have hsx k := (hmem hs k).1 (hsy' k)
    have hx : s (Fin.last n).castSucc < x := (hsy hs).trans hyx
    rw [h s (withLast s x hx) hs (by simp) (by simp) hsx, ← hyx' hs hsx _ (by simp) (by simp)]
    congr 1
    exact RelEmbedding.ext <| Fin.lastCases (by simp [ht]) (by simp [hst])

/-- The tree predecessors of `x` form an end-homogeneous set. -/
private theorem isEndHomogeneousOn_treePred (c : (Fin (n + 2) ↪o J) → D) (x : J) :
    IsEndHomogeneousOn c (treePred c x) := by
  -- If `u < v` are tree predecessors of `x`, then `u` is a tree predecessor of `v`.
  have key (s t : Fin (n + 2) ↪o J) (hs : ∀ k, s k ∈ treePred c x) (ht : ∀ k, t k ∈ treePred c x)
      (hst : ∀ k : Fin (n + 1), s k.castSucc = t k.castSucc)
      (hlt : s (Fin.last _) < t (Fin.last _)) : c s = c t := by
    have hP := treePred_eq_of_mem (ht (Fin.last _))
    refine (mem_treePred_iff.1 ?_).2 s t rfl rfl hst fun k ↦ ?_
    · rw [hP]
      exact ⟨hs _, hlt⟩
    · rw [hP]
      exact ⟨hs _, (s.strictMono (Fin.castSucc_lt_last k)).trans hlt⟩
  refine isEndHomogeneousOn_def.2 fun s t hs ht hst ↦ ?_
  rcases lt_trichotomy (s (Fin.last _)) (t (Fin.last _)) with hlt | heq | hgt
  · exact key s t hs ht hst hlt
  · rw [RelEmbedding.ext (Fin.lastCases heq hst)]
  · exact (key t s ht hs (fun k ↦ (hst k).symm) hgt).symm

/-- A point is determined by its tree predecessors together with its colours against them. -/
private theorem eq_of_treePred_eq (hxy : treePred c x = treePred c y)
    (hc : ∀ s t : Fin (n + 2) ↪o J, s (Fin.last _) = x → t (Fin.last _) = y →
      (∀ k : Fin (n + 1), s k.castSucc = t k.castSucc) →
      (∀ k : Fin (n + 1), s k.castSucc ∈ treePred c x) → c s = c t) :
    x = y := by
  rcases lt_trichotomy x y with hlt | heq | hgt
  · refine absurd (lt_of_mem_treePred (hxy ▸ (mem_treePred_iff.2 ⟨hlt, ?_⟩))) (lt_irrefl x)
    exact fun s t hs ht hst hsP ↦ hc s t hs ht hst (hxy ▸ hsP)
  · exact heq
  · refine absurd (lt_of_mem_treePred (hxy ▸ (mem_treePred_iff.2 ⟨hgt, ?_⟩))) (lt_irrefl y)
    exact fun s t hs ht hst hsP ↦ (hc t s ht hs (fun k ↦ (hst k).symm)
      fun k ↦ hst k ▸ hsP k).symm

/-- **Rigidity of branches.** Two enumerations `e`, `e'` of branches of the tree by the same
well-order, along which the tree predecessors of each point are the earlier points, and which
give every increasing tuple the same colour, are equal. -/
private theorem eq_of_comp_eq {T : Type*} [LinearOrder T] [WellFoundedLT T] {e e' : T ↪o J}
    (he : ∀ v, treePred c (e v) = e '' Iio v) (he' : ∀ v, treePred c (e' v) = e' '' Iio v)
    (hc : ∀ σ : Fin (n + 2) ↪o T, c (σ.trans e) = c (σ.trans e')) : e = e' := by
  refine RelEmbedding.ext fun v ↦ ?_
  induction v using WellFoundedLT.induction with | _ v IH => ?_
  have himage : e '' Iio v = e' '' Iio v := image_congr fun u hu ↦ IH u hu
  refine eq_of_treePred_eq (by rw [he, he', himage]) fun s t hs ht hst hsP ↦ ?_
  -- Pull `s` back along `e`: its entries are `e v` and points of `e '' Iio v`.
  have hmem (k : Fin (n + 2)) : s k ∈ e '' Iic v := by
    induction k using Fin.lastCases with
    | last => exact ⟨v, self_mem_Iic, hs.symm⟩
    | cast k =>
      obtain ⟨w, hw, hwk⟩ := he v ▸ hsP k
      exact ⟨w, Iio_subset_Iic_self hw, hwk⟩
  obtain ⟨σ, -, rfl⟩ := e.exists_trans_eq_of_forall_mem_image s hmem
  have hl : σ (Fin.last _) = v := e.injective hs
  have hσt : σ.trans e' = t := by
    refine RelEmbedding.ext <| Fin.lastCases ?_ fun k ↦ ?_
    · simp [hl, ht]
    · have hk : σ k.castSucc < v := hl ▸ σ.strictMono (Fin.castSucc_lt_last k)
      simpa [← IH _ hk] using hst k
  rw [← hσt, hc]

/-- Each point of the branch `insert x (treePred c x)` has as tree predecessors the points of
the branch below it. -/
private theorem treePred_eq_of_mem_insert (hy : y ∈ insert x (treePred c x)) :
    treePred c y = insert x (treePred c x) ∩ Iio y := by
  rcases hy with rfl | hy
  · rw [insert_inter_of_notMem (lt_irrefl _), inter_eq_left.2 fun z hz ↦ lt_of_mem_treePred hz]
  · rw [treePred_eq_of_mem hy, insert_inter_of_notMem (lt_asymm (lt_of_mem_treePred hy))]

/-- Two branches enumerated by initial segments `Iio w` and `Iio w'` of a well-order, with `w = w'`
and the same colour pattern, are equal. The colour patterns are compared heterogeneously, as they
arise as components of equal elements of a sigma type. -/
private theorem range_eq_of_heq {W : Type*} [LinearOrder W] [WellFoundedLT W] {w w' : W}
    (h : w = w') {e : Iio w ↪o J} {e' : Iio w' ↪o J} (he : ∀ v, treePred c (e v) = e '' Iio v)
    (he' : ∀ v, treePred c (e' v) = e' '' Iio v)
    (hc : HEq (fun σ : Fin (n + 2) ↪o Iio w ↦ c (σ.trans e))
      (fun σ : Fin (n + 2) ↪o Iio w' ↦ c (σ.trans e'))) :
    range e = range e' := by
  subst h
  rw [eq_of_comp_eq he he' fun σ ↦ congrFun (eq_of_heq hc) σ]

end Tree

section Counting

variable {J D : Type u} [LinearOrder J] [WellFoundedLT J] {n : ℕ} {lam : Cardinal.{u}}

/-- A branch `insert x (treePred c x)` with at most `lam` points is enumerated by an initial
segment of the well-order `(lam⁺).ord.ToType`. -/
private theorem exists_orderEmbedding_Iio (c : (Fin (n + 2) ↪o J) → D) (hlam : ℵ₀ ≤ lam)
    (x : J) (hx : #(treePred c x) ≤ lam) :
    ∃ (w : (Order.succ lam).ord.ToType) (e : Iio w ↪o J), range e = insert x (treePred c x) := by
  set Q := insert x (treePred c x)
  have hQ : typeLT Q < typeLT (Order.succ lam).ord.ToType := by
    simpa [lt_ord, Order.lt_succ_iff] using
      mk_insert_le.trans ((add_le_add hx le_rfl).trans (add_one_eq hlam).le)
  obtain ⟨f⟩ := Ordinal.type_lt_iff.1 hQ
  let iso : Q ≃o Iio f.top := f.orderIsoIio
  refine ⟨f.top, iso.symm.toOrderEmbedding.trans (OrderEmbedding.subtype (· ∈ Q)), ?_⟩
  ext z
  refine ⟨?_, fun hz ↦ ⟨iso ⟨z, hz⟩, by simp⟩⟩
  rintro ⟨w, rfl⟩
  exact (iso.symm w).property

/-- **The counting step of the Erdős–Rado tree argument.** If `J` has more than `2 ^ lam` points,
some point has more than `lam` tree predecessors. -/
private theorem exists_lt_mk_treePred (hlam : ℵ₀ ≤ lam) (hJ : Order.succ (2 ^ lam) ≤ #J)
    (hD : #D ≤ lam) (c : (Fin (n + 2) ↪o J) → D) : ∃ x, lam < #(treePred c x) := by
  by_contra! h
  choose w e he using fun x ↦ exists_orderEmbedding_Iio c hlam x (h x)
  -- Along each enumeration, the tree predecessors of a point are the earlier points.
  have hpred (x : J) (v : Iio (w x)) : treePred c (e x v) = e x '' Iio v := by
    rw [← (e x).preimage_Iio, image_preimage_eq_range_inter, he,
      treePred_eq_of_mem_insert (he x ▸ mem_range_self v)]
  -- A point is determined by the length of its branch and the colours along the branch.
  let code (x : J) : Σ w : (Order.succ lam).ord.ToType, (Fin (n + 2) ↪o Iio w) → D :=
    ⟨w x, fun σ ↦ c (σ.trans (e x))⟩
  have hcode : Function.Injective code := fun x y hxy ↦ by
    obtain ⟨hw, hc⟩ := Sigma.mk.inj_iff.1 hxy
    have hxy := range_eq_of_heq hw (hpred x) (hpred y) hc
    rw [he, he] at hxy
    have hx : x ∈ insert y (treePred c y) := hxy ▸ mem_insert x _
    have hy : y ∈ insert x (treePred c x) := hxy ▸ mem_insert y _
    rcases hx with rfl | hx
    · rfl
    rcases hy with rfl | hy
    · rfl
    exact absurd (lt_of_mem_treePred hx) (lt_of_mem_treePred hy).not_gt
  -- Each initial segment has at most `lam` points, so carries at most `lam ^ lam` colourings.
  have hfib (v : (Order.succ lam).ord.ToType) : #((Fin (n + 2) ↪o Iio v) → D) ≤ 2 ^ lam := by
    have hv : #(Iio v) ≤ lam := Order.lt_succ_iff.1 <| by
      simpa using mk_Iio_lt v (by simp)
    have htup : #(Fin (n + 2) ↪o Iio v) ≤ lam := by
      refine (mk_le_of_injective DFunLike.coe_injective).trans ?_
      simpa using (power_le_power_right hv).trans (power_nat_le hlam (n := n + 2))
    rw [← power_def, ← power_self_eq hlam]
    exact (power_le_power_right hD).trans (power_le_power_left (aleph0_pos.trans_le hlam).ne' htup)
  have h2 : ℵ₀ ≤ 2 ^ lam := hlam.trans (cantor lam).le
  refine (Order.lt_succ (2 ^ lam)).not_ge (hJ.trans ((mk_le_of_injective hcode).trans ?_))
  rw [mk_sigma]
  refine (sum_le_sum _ _ hfib).trans ?_
  rw [sum_const', mk_ord_toType]
  calc Order.succ lam * 2 ^ lam ≤ 2 ^ lam * 2 ^ lam := by
        gcongr
        exact Order.succ_le_of_lt (cantor lam)
    _ = 2 ^ lam := mul_eq_self h2

end Counting

/-- **End-homogeneous sets.** Let `lam` be infinite and `J` a well-order of cardinality at least
`(2 ^ lam)⁺`. Every colouring of the increasing `(n + 2)`-tuples of `J` by at most `lam` colours has
an end-homogeneous set of cardinality at least `lam⁺`: on it, the colour of an increasing tuple
does not depend on its last entry. -/
theorem exists_isEndHomogeneousOn {lam : Cardinal.{u}} (hlam : ℵ₀ ≤ lam) {J : Type u}
    [LinearOrder J] [WellFoundedLT J] (hJ : Order.succ (2 ^ lam) ≤ #J) {D : Type u}
    (hD : #D ≤ lam) {n : ℕ} (c : (Fin (n + 2) ↪o J) → D) :
    ∃ H : Set J, Order.succ lam ≤ #H ∧ IsEndHomogeneousOn c H := by
  obtain ⟨x, hx⟩ := exists_lt_mk_treePred hlam hJ hD c
  exact ⟨treePred c x, Order.succ_le_of_lt hx, isEndHomogeneousOn_treePred c x⟩

/-- **End-homogeneous sets for pairs**, the case `n = 0` of `exists_isEndHomogeneousOn`. Let `lam`
be infinite and `J` a well-order of cardinality at least `(2 ^ lam)⁺`. Every colouring of the
increasing pairs of `J` by at most `lam` colours has a set `H` of cardinality at least `lam⁺` on
which the colour of a pair depends only on its smaller point. -/
theorem exists_forall_eq_of_apply_zero_eq {lam : Cardinal.{u}} (hlam : ℵ₀ ≤ lam) {J : Type u}
    [LinearOrder J] [WellFoundedLT J] (hJ : Order.succ (2 ^ lam) ≤ #J) {D : Type u}
    (hD : #D ≤ lam) (c : (Fin 2 ↪o J) → D) :
    ∃ H : Set J, Order.succ lam ≤ #H ∧
      ∀ s t : Fin 2 ↪o J, (∀ k, s k ∈ H) → (∀ k, t k ∈ H) → s 0 = t 0 → c s = c t := by
  obtain ⟨H, hH, hc⟩ := exists_isEndHomogeneousOn hlam hJ hD (n := 0) c
  exact ⟨H, hH, fun s t hs ht h0 ↦
    isEndHomogeneousOn_def.1 hc s t hs ht (Fin.forall_fin_one.2 h0)⟩

end TauCeti
