/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.PushoutI.Basic
public import TauCeti.GroupTheory.PushoutI.Reduced
public import TauCeti.GroupTheory.TrivialIntersection
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Subgroup
import TauCeti.Data.Int.DivMod
import TauCeti.Data.Int.UnitStep

/-!
# Centralizers in an amalgamated product

This file computes centralizers of two kinds of elements of an amalgamated product: elements of a
factor not conjugate into the amalgamated subgroup, and elements conjugate into no factor.

## Elements of a factor

Let `φ i : H →* G i` be a family of injective group homomorphisms, with amalgamated product
`Monoid.PushoutI φ`. If an element `g` of a factor `G i` is not conjugate in `G i` into the
amalgamated subgroup `φ i H`, then every element of the amalgamated product commuting with `g`
lies in `G i`: the centralizer of `g` in the amalgamated product is its centralizer in `G i`.
In the action of the amalgamated product on its Bass–Serre tree, such a `g` fixes the vertex
`G i` and no edge at it, so it fixes no other vertex, and an element commuting with `g`
preserves its fixed point set.

The proof uses normal forms rather than the Bass–Serre tree: write an element `x` commuting with
`g` as `a * w` with `a ∈ G i` and `w` a reduced word not starting in `G i`
(`Monoid.PushoutI.exists_eq_of_mul_list_prod`). If `w` is nonempty, then
`x⁻¹ * g * x = w⁻¹ * (a⁻¹ * g * a) * w` lies in no factor
(`Monoid.PushoutI.list_prod_inv_mul_of_mul_list_prod_notMem_range_of`), but it equals `g`.

## Hyperbolic elements

Let `E = A ∗_C B` be an amalgamated product of two groups, Mathlib's `Monoid.PushoutI` over `Bool`
with injective maps of `C` into the factors, and suppose that `C` is malnormal in one factor. The
centralizer of an element of `E` conjugate into neither factor is cyclic.

In the Bass–Serre tree of the amalgam such an element `x` is hyperbolic: it translates a line, its
axis, and an element commuting with `x` preserves the axis and translates it in the direction of
`x`. At a vertex of the malnormal factor, the stabilizer of the two edges of the axis is
`C ∩ a C a⁻¹ = 1` for a letter `a ∉ C`, so the centralizer of `x` acts faithfully on the axis by
translations and embeds in `ℤ`.

The proof follows this picture with normal forms in place of the tree. A conjugate of `x` is
cyclically reduced, `a₁ ⋯ aᵣ` with `r ≥ 2` letters alternately from `A ∖ C` and `B ∖ C`, the first
and the last from different factors. The cosets `P m C` of the partial products `P m` of the
periodic word `⋯ a₁ ⋯ aᵣ a₁ ⋯ aᵣ ⋯` play the role of the edges of the axis, and the number of
letters of a normal form, an invariant of the element, plays the role of the distance. An element
`g` for which `g⁻¹ x g` has at most `r` letters lies in one of the cosets `P m C`; so an element
commuting with `x` permutes these cosets, by a translation of the index since it commutes with
`x`.

## Main results

* `Monoid.PushoutI.centralizer_of_eq_map`: the centralizer of an element of a factor that is not
  conjugate in that factor into the amalgamated subgroup.
* `Monoid.PushoutI.isCyclic_centralizer`: in `A ∗_C B` with `C` malnormal in one factor, the
  centralizer of an element conjugate into neither factor is cyclic.

## Implementation notes

Inside the proofs for hyperbolic elements a letter is a pair `(i, e)` of a factor `i` and an
element `e` of the amalgam in the image of that factor and not in the image of `C`, so that letters
of one factor can be multiplied without casts between the factors; the normal form lemmas of
`TauCeti.GroupTheory.PushoutI.Reduced` are translated to such lists once.

## References

* W. Magnus, A. Karrass, D. Solitar, *Combinatorial group theory*, Theorem 4.5 (commuting
  elements of an amalgamated product), as used in G. Baumslag, A. Myasnikov, V. Remeslennikov,
  *Algebraic geometry over groups I: Algebraic sets and ideal theory*, J. Algebra 219 (1999),
  proof of Theorem A2.
* J.-P. Serre, *Trees*, Chapter I, §1.2, Theorem 1 (the normal form theorem), §4 (the tree of an
  amalgam) and §6 (hyperbolic automorphisms and their axes).
* R. C. Lyndon, P. E. Schupp, *Combinatorial group theory*, Chapter IV, §2 (normal forms in free
  products with amalgamation).
* O. Kharlampovich, A. Myasnikov, V. Remeslennikov, D. Serbin, *Subgroups of fully residually free
  groups: algorithmic problems*, Contemp. Math. 360 (2004), §5, Lemma 19.
-/

public section

open Function

namespace Monoid.PushoutI

section General

variable {ι : Type*} {G : ι → Type*} {H : Type*} [∀ i, Group (G i)] [Group H]
  {φ : ∀ i, H →* G i}

/-! ### Centralizers of elements of a factor -/

open Subgroup in
/-- **Centralizers of factor elements away from the amalgamated subgroup.** If an element `g` of
a factor `G i` of an amalgamated product of groups is not conjugate in `G i` into the amalgamated
subgroup, then its centralizer in the amalgamated product is its centralizer in `G i`. -/
theorem centralizer_of_eq_map (hφ : ∀ i, Injective (φ i)) {i : ι} {g : G i}
    (hg : ∀ k : G i, k * g * k⁻¹ ∉ (φ i).range) :
    centralizer {of (φ := φ) i g} = (centralizer {g}).map (of i) := by
  refine le_antisymm (fun x hx => ?_) (map_le_iff_le_comap.2 fun k hk => ?_)
  · obtain ⟨a, L, hc, hred, hhead, rfl⟩ := exists_eq_of_mul_list_prod i x
    have hx' : (of (φ := φ) i a * (L.map fun l => of l.1 l.2).prod)⁻¹ * of i g *
        (of i a * (L.map fun l => of l.1 l.2).prod) = of i g := by
      rw [mul_assoc, ← mem_centralizer_singleton_iff.1 hx, inv_mul_cancel_left]
    rcases eq_or_ne L [] with rfl | hL
    · refine ⟨a, mem_centralizer_singleton_iff.2 (of_injective hφ i ?_), by simp⟩
      simpa using (mem_centralizer_singleton_iff.1 hx).eq
    · -- Otherwise `x⁻¹ * g * x` is a reduced word of length at least three.
      refine (list_prod_inv_mul_of_mul_list_prod_notMem_range_of hφ hL hc hred (hg a⁻¹) hhead
        ⟨g, ?_⟩).elim
      rw [← hx']
      simp [mul_assoc]
  · rw [mem_comap, mem_centralizer_singleton_iff, commute_iff_eq, ← map_mul, ← map_mul,
      (mem_centralizer_singleton_iff.1 hk).eq]

/-! ### Letters as elements of the amalgamated product -/

/-- A letter of the amalgamated product from the factor `l.1`: an element `l.2` of the image of
`G l.1` that is not in the image of the amalgamated subgroup. -/
private def IsLetter (l : ι × PushoutI φ) : Prop :=
  l.2 ∈ (of (φ := φ) l.1).range ∧ l.2 ∉ (base φ).range

/-- A reduced list of letters: consecutive letters come from different factors. -/
private def IsRed (L : List (ι × PushoutI φ)) : Prop :=
  L.IsChain (fun l l' => l.1 ≠ l'.1) ∧ ∀ l ∈ L, IsLetter l

/-- The product of a list of letters. -/
private def lprod (L : List (ι × PushoutI φ)) : PushoutI φ := (L.map Prod.snd).prod

@[simp] private theorem lprod_nil : lprod ([] : List (ι × PushoutI φ)) = 1 := (rfl)

@[simp] private theorem lprod_cons (l : ι × PushoutI φ) (L : List (ι × PushoutI φ)) :
    lprod (l :: L) = l.2 * lprod L := by
  simp [lprod]

@[simp] private theorem lprod_append (L L' : List (ι × PushoutI φ)) :
    lprod (L ++ L') = lprod L * lprod L' := by
  simp [lprod]

private theorem IsLetter.inv {l : ι × PushoutI φ} (h : IsLetter l) : IsLetter (l.1, l.2⁻¹) :=
  ⟨inv_mem h.1, fun h' => h.2 (by simpa using inv_mem h')⟩

private theorem IsLetter.base_mul {l : ι × PushoutI φ} (h : IsLetter l) (c : H) :
    IsLetter (l.1, base φ c * l.2) := by
  have hc : base φ c ∈ (base φ).range := ⟨c, rfl⟩
  exact ⟨mul_mem (base_range_le_of_range _ hc) h.1,
    fun h' => h.2 (by simpa using mul_mem (inv_mem hc) h')⟩

private theorem IsLetter.mul_base {l : ι × PushoutI φ} (h : IsLetter l) (c : H) :
    IsLetter (l.1, l.2 * base φ c) := by
  have hc : base φ c ∈ (base φ).range := ⟨c, rfl⟩
  exact ⟨mul_mem h.1 (base_range_le_of_range _ hc),
    fun h' => h.2 (by simpa using mul_mem h' (inv_mem hc))⟩

@[simp] private theorem isRed_nil : IsRed ([] : List (ι × PushoutI φ)) := by
  simp [IsRed]

private theorem isRed_cons {l : ι × PushoutI φ} {L : List (ι × PushoutI φ)} :
    IsRed (l :: L) ↔ IsLetter l ∧ (∀ l' ∈ L.head?, l.1 ≠ l'.1) ∧ IsRed L := by
  simp only [IsRed, List.isChain_cons, List.forall_mem_cons]
  tauto

private theorem isRed_append {L L' : List (ι × PushoutI φ)} :
    IsRed (L ++ L') ↔
      IsRed L ∧ IsRed L' ∧ ∀ a ∈ L.getLast?, ∀ a' ∈ L'.head?, a.1 ≠ a'.1 := by
  simp only [IsRed, List.isChain_append, List.forall_mem_append]
  tauto

private theorem isRed_singleton {l : ι × PushoutI φ} : IsRed [l] ↔ IsLetter l := by
  simp [IsRed]

/-- A reduced list of letters, read backwards with inverted letters. -/
private def revInv (L : List (ι × PushoutI φ)) : List (ι × PushoutI φ) :=
  (L.map fun l => (l.1, l.2⁻¹)).reverse

@[simp] private theorem length_revInv (L : List (ι × PushoutI φ)) :
    (revInv L).length = L.length := by
  simp [revInv]

private theorem lprod_revInv (L : List (ι × PushoutI φ)) : lprod (revInv L) = (lprod L)⁻¹ := by
  simp [lprod, revInv, List.prod_inv_reverse, Function.comp_def]

private theorem isRed_revInv {L : List (ι × PushoutI φ)} (hL : IsRed L) : IsRed (revInv L) := by
  refine ⟨?_, fun l' hl' => ?_⟩
  · rw [revInv, List.isChain_reverse, List.isChain_map]
    exact hL.1.imp fun _ _ h => h.symm
  · obtain ⟨l, hl, rfl⟩ := List.mem_map.1 (List.mem_reverse.1 hl')
    exact (hL.2 l hl).inv

private theorem getLast?_revInv (L : List (ι × PushoutI φ)) :
    (revInv L).getLast? = L.head?.map fun l => (l.1, l.2⁻¹) := by
  simp [revInv]

/-- The conjugate of a reduced list `Z` by a reduced list `K` whose first letter is in a factor
different from those of the first and the last letters of `Z` is reduced. -/
private theorem IsRed.conj {Z K : List (ι × PushoutI φ)} (hZ : IsRed Z) (hK : IsRed K)
    (hfirst : ∀ z ∈ Z.head?, ∀ k ∈ K.head?, z.1 ≠ k.1)
    (hlast : ∀ z ∈ Z.getLast?, ∀ k ∈ K.head?, z.1 ≠ k.1) (hZne : Z ≠ []) :
    IsRed (revInv K ++ (Z ++ K)) := by
  refine isRed_append.2 ⟨isRed_revInv hK, isRed_append.2 ⟨hZ, hK, hlast⟩, fun a ha a' ha' => ?_⟩
  rw [getLast?_revInv] at ha
  obtain ⟨k, hk, rfl⟩ := Option.mem_map.1 ha
  rw [List.head?_append_of_ne_nil _ hZne] at ha'
  exact (hfirst a' ha' k hk).symm

private theorem lprod_conj (Z K : List (ι × PushoutI φ)) :
    lprod (revInv K ++ (Z ++ K)) = (lprod K)⁻¹ * lprod Z * lprod K := by
  simp [lprod_revInv, mul_assoc]

/-- A reduced list of letters gives a reduced list of letters of the factors with the same
product. -/
private theorem IsRed.exists_sigma {L : List (ι × PushoutI φ)} (hL : IsRed L) :
    ∃ K : List (Σ i, G i), (K.IsChain fun k k' => k.1 ≠ k'.1) ∧ (∀ k ∈ K, k.2 ∉ (φ k.1).range) ∧
      K.length = L.length ∧ (K.map fun k => of k.1 k.2).prod = lprod L := by
  have hpre (l : ι × PushoutI φ) : ∃ a : G l.1, IsLetter l → of l.1 a = l.2 := by
    by_cases h : IsLetter l
    · obtain ⟨a, ha⟩ := h.1
      exact ⟨a, fun _ => ha⟩
    · exact ⟨1, fun h' => absurd h' h⟩
  choose pre hpre using hpre
  refine ⟨L.map fun l => ⟨l.1, pre l⟩, ?_, ?_, by simp, ?_⟩
  · rw [List.isChain_map]
    exact hL.1
  · simp only [List.mem_map]
    rintro _ ⟨l, hl, rfl⟩ ⟨c, hc⟩
    refine (hL.2 l hl).2 ⟨c, ?_⟩
    rw [← hpre l (hL.2 l hl), ← of_apply_eq_base φ l.1 c]
    exact congrArg _ hc
  · simp only [List.map_map, lprod]
    exact congrArg List.prod (List.map_congr_left fun l hl => hpre l (hL.2 l hl))

variable (hφ : ∀ i, Injective (φ i))
include hφ

/-- The number of letters of a reduced list is determined by its product up to the amalgamated
subgroup. -/
private theorem IsRed.length_eq {L L' : List (ι × PushoutI φ)} (hL : IsRed L) (hL' : IsRed L')
    {h h' : H} (heq : base φ h * lprod L = base φ h' * lprod L') : L.length = L'.length := by
  obtain ⟨K, hc, hred, hlen, hprod⟩ := hL.exists_sigma
  obtain ⟨K', hc', hred', hlen', hprod'⟩ := hL'.exists_sigma
  rw [← hlen, ← hlen']
  simpa using congrArg List.length
    (map_fst_eq_of_base_mul_list_prod_eq hφ hc hred hc' hred' (by rw [hprod, hprod', heq]))

/-- Normal forms with letters in the amalgamated product. -/
private theorem exists_eq_base_mul_lprod (x : PushoutI φ) :
    ∃ (c : H) (L : List (ι × PushoutI φ)), IsRed L ∧ x = base φ c * lprod L := by
  obtain ⟨c, ⟨K, _, hc⟩, hred, rfl⟩ := exists_eq_base_mul_ofCoprodI_prod x
  refine ⟨c, K.map fun k => (k.1, of k.1 k.2), ⟨?_, ?_⟩, ?_⟩
  · rw [List.isChain_map]
    exact hc
  · simp only [List.mem_map]
    rintro _ ⟨k, hk, rfl⟩
    refine ⟨⟨k.2, rfl⟩, fun ⟨c', hc'⟩ => hred k hk ⟨c', of_injective hφ k.1 ?_⟩⟩
    rw [of_apply_eq_base, hc']
  · simp [lprod, CoprodI.Word.prod, map_list_prod, Function.comp_def]

end General

section Bool

variable {H : Type*} [Group H] {G : Bool → Type*} [∀ b, Group (G b)] {φ : ∀ b, H →* G b}

/-! ### The axis of a cyclically reduced element -/

/-- A periodic bi-infinite reduced word in `A ∗_C B`: letters `ℓ m` for `m : ℤ`, consecutive ones
from different factors, of period `r > 0`, with partial products `P (m + 1) = P m * ℓ m`. Then
`P r` is a cyclically reduced element and the cosets `P m C` form its axis in the Bass–Serre
tree. -/
private structure Axis (φ : ∀ b, H →* G b) where
  /-- The letters. -/
  ℓ : ℤ → Bool × PushoutI φ
  /-- The partial products. -/
  P : ℤ → PushoutI φ
  /-- The period. -/
  r : ℕ
  r_pos : 0 < r
  isLetter : ∀ m, IsLetter (ℓ m)
  ne : ∀ m, (ℓ (m + 1)).1 ≠ (ℓ m).1
  periodic : ∀ m, ℓ (m + r) = ℓ m
  P_zero : P 0 = 1
  P_succ : ∀ m, P (m + 1) = P m * (ℓ m).2

namespace Axis

/-- The axis read from the letter `ℓ k` on. -/
private def shift (A : Axis φ) (k : ℤ) : Axis φ where
  ℓ m := A.ℓ (m + k)
  P m := (A.P k)⁻¹ * A.P (m + k)
  r := A.r
  r_pos := A.r_pos
  isLetter m := A.isLetter _
  ne m := by simpa only [add_right_comm] using A.ne (m + k)
  periodic m := by simpa only [add_right_comm] using A.periodic (m + k)
  P_zero := by simp
  P_succ m := by rw [add_right_comm, A.P_succ, mul_assoc]

/-- The axis read backwards, with inverted letters: the axis of `(P r)⁻¹`. -/
private def reverse (A : Axis φ) : Axis φ where
  ℓ m := ((A.ℓ (-1 - m)).1, (A.ℓ (-1 - m)).2⁻¹)
  P m := A.P (-m)
  r := A.r
  r_pos := A.r_pos
  isLetter m := (A.isLetter _).inv
  ne m := by
    have hm : -1 - (m + 1) + 1 = -1 - m := by ring
    have := A.ne (-1 - (m + 1))
    rw [hm] at this
    exact this.symm
  periodic m := by
    have hm : -1 - (m + A.r) + A.r = -1 - m := by ring
    have := A.periodic (-1 - (m + A.r))
    rw [hm] at this
    simp [this]
  P_zero := by simp [A.P_zero]
  P_succ m := by
    have hm : -1 - m + 1 = -m := by ring
    have hm' : -(m + 1) = -1 - m := by ring
    have := A.P_succ (-1 - m)
    rw [hm] at this
    rw [this, hm', mul_inv_cancel_right]

/-- The letters `ℓ a, …, ℓ (a + k - 1)`. -/
private def seg (A : Axis φ) (a : ℤ) : ℕ → List (Bool × PushoutI φ)
  | 0 => []
  | k + 1 => A.ℓ a :: A.seg (a + 1) k

@[simp] private theorem seg_zero (A : Axis φ) (a : ℤ) : A.seg a 0 = [] := (rfl)

@[simp] private theorem seg_succ (A : Axis φ) (a : ℤ) (k : ℕ) :
    A.seg a (k + 1) = A.ℓ a :: A.seg (a + 1) k :=
  (rfl)

@[simp] private theorem length_seg (A : Axis φ) (a : ℤ) (k : ℕ) : (A.seg a k).length = k := by
  induction k generalizing a with
  | zero => rfl
  | succ k ih => simp [ih]

private theorem seg_succ_right (A : Axis φ) (a : ℤ) (k : ℕ) :
    A.seg a (k + 1) = A.seg a k ++ [A.ℓ (a + k)] := by
  induction k generalizing a with
  | zero => simp
  | succ k ih =>
    rw [seg_succ, ih, seg_succ, List.cons_append]
    push_cast
    ring_nf

private theorem isRed_seg (A : Axis φ) (a : ℤ) (k : ℕ) : IsRed (A.seg a k) := by
  induction k generalizing a with
  | zero => exact isRed_nil
  | succ k ih =>
    refine isRed_cons.2 ⟨A.isLetter a, fun l hl => ?_, ih _⟩
    cases k with
    | zero => simp at hl
    | succ k =>
      obtain rfl : l = A.ℓ (a + 1) := by simpa using hl.symm
      exact (A.ne a).symm

private theorem P_add (A : Axis φ) (a : ℤ) (k : ℕ) : A.P (a + k) = A.P a * lprod (A.seg a k) := by
  induction k generalizing a with
  | zero => simp
  | succ k ih =>
    rw [seg_succ, lprod_cons, ← mul_assoc, ← A.P_succ, ← ih]
    push_cast
    ring_nf

/-- Left multiplication by `P r` translates the axis by its period. -/
private theorem P_add_r (A : Axis φ) (m : ℤ) : A.P (m + A.r) = A.P A.r * A.P m := by
  induction m using Int.induction_on with
  | zero => simp [A.P_zero]
  | succ m ih =>
    rw [add_right_comm, A.P_succ, ih, A.P_succ, A.periodic, mul_assoc]
  | pred m ih =>
    have hm : -(m : ℤ) - 1 + A.r + 1 = -m + A.r := by ring
    have hm' : -(m : ℤ) - 1 + 1 = -m := by ring
    have h1 := A.P_succ (-(m : ℤ) - 1 + A.r)
    have h2 := A.P_succ (-(m : ℤ) - 1)
    rw [hm, A.periodic] at h1
    rw [hm'] at h2
    rw [ih, h2, ← mul_assoc] at h1
    exact (mul_right_cancel h1).symm

/-- The period of an axis is at least two: consecutive letters alternate between the factors. -/
private theorem two_le_r (A : Axis φ) : 2 ≤ A.r := by
  by_contra h
  have h1 : A.r = 1 := by have := A.r_pos; omega
  have := A.periodic 0
  rw [h1, Nat.cast_one, zero_add] at this
  exact A.ne 0 (by rw [zero_add, this])

private theorem P_neg_r (A : Axis φ) : A.P (-A.r) = (A.P A.r)⁻¹ := by
  have := A.P_add_r (-A.r)
  rw [neg_add_cancel, A.P_zero] at this
  exact eq_inv_of_mul_eq_one_right this.symm

private theorem P_one (A : Axis φ) : A.P 1 = (A.ℓ 0).2 := by
  simpa [A.P_zero] using A.P_succ 0

private theorem lprod_seg_r (A : Axis φ) : lprod (A.seg 0 A.r) = A.P A.r := by
  simpa [A.P_zero] using (A.P_add 0 A.r).symm

/-- For a letter `e` of the factor of `ℓ 0` with `ℓ 0⁻¹ * e ∉ C`, the word
`(e⁻¹ * ℓ 0) (ℓ 1) ⋯ (ℓ (r - 1)) e`, whose product is `e⁻¹ * P r * e`, is reduced. -/
private theorem isRed_conj_seg (A : Axis φ) {j : Bool} {e : PushoutI φ} (he : IsLetter (j, e))
    (hj : j = (A.ℓ 0).1) (hd : (A.ℓ 0).2⁻¹ * e ∉ (base φ).range) {r' : ℕ} (hr' : A.r = r' + 2) :
    IsRed ((j, e⁻¹ * (A.ℓ 0).2) :: (A.seg 1 (r' + 1) ++ [(j, e)])) := by
  have hlast : (A.ℓ (1 + r')).1 ≠ j := by
    have h1 := A.ne (1 + r')
    have h2 := A.periodic 0
    have hr : (1 : ℤ) + r' + 1 = ((r' + 2 : ℕ) : ℤ) := by push_cast; ring
    rw [zero_add, hr'] at h2
    rw [hr, h2] at h1
    exact hj ▸ h1.symm
  refine isRed_cons.2 ⟨⟨mul_mem (inv_mem he.1) (hj ▸ (A.isLetter 0).1), fun h => hd ?_⟩, ?_, ?_⟩
  · simpa using inv_mem h
  · intro l hl
    obtain rfl : l = A.ℓ 1 := by simpa using hl.symm
    simpa [hj] using (A.ne 0).symm
  · refine isRed_append.2 ⟨A.isRed_seg 1 _, isRed_singleton.2 he, fun a ha a' ha' => ?_⟩
    rw [A.seg_succ_right, List.getLast?_append, List.getLast?_singleton] at ha
    simp only [Option.some_or, Option.mem_def, Option.some.injEq] at ha
    simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at ha'
    subst ha ha'
    exact hlast

/-- If the first letter `e` of `e * k` lies in the factor of `ℓ 0` and `ℓ 0⁻¹ * e ∉ C`, then
`(e * k)⁻¹ * P r * (e * k)` is a reduced word with `r + 1 + 2 * |k|` letters. -/
private theorem exists_conj_eq_lprod_of_notMem (A : Axis φ) {j : Bool} {e : PushoutI φ}
    {K : List (Bool × PushoutI φ)} (hK : IsRed ((j, e) :: K)) (hj : j = (A.ℓ 0).1)
    (hd : (A.ℓ 0).2⁻¹ * e ∉ (base φ).range) :
    ∃ L, IsRed L ∧ L.length = A.r + 1 + 2 * K.length ∧
      (e * lprod K)⁻¹ * A.P A.r * (e * lprod K) = lprod L := by
  obtain ⟨he, hhead, hKred⟩ := isRed_cons.1 hK
  obtain ⟨r', hr'⟩ : ∃ r', A.r = r' + 2 := ⟨A.r - 2, by have := A.two_le_r; omega⟩
  -- `e⁻¹ * P r * e` is the reduced word `Z = (e⁻¹ * ℓ 0) (ℓ 1) ⋯ (ℓ (r - 1)) e`, whose first and
  -- last letters lie in the factor `j`, different from that of the first letter of `k`.
  set Z : List (Bool × PushoutI φ) := (j, e⁻¹ * (A.ℓ 0).2) :: (A.seg 1 (r' + 1) ++ [(j, e)])
  have hZ : IsRed Z := A.isRed_conj_seg he hj hd hr'
  have hZlast : Z.getLast? = some (j, e) := by
    simp only [Z]
    rw [← List.cons_append, List.getLast?_concat]
  refine ⟨revInv K ++ (Z ++ K), IsRed.conj hZ hKred (fun z hz k hk => ?_) (fun z hz k hk => ?_)
    (List.cons_ne_nil _ _), by simp [Z, hr']; omega, ?_⟩
  · simp only [Z, List.head?_cons, Option.mem_def, Option.some.injEq] at hz
    exact hz ▸ hhead k hk
  · rw [hZlast, Option.mem_def, Option.some.injEq] at hz
    exact hz ▸ hhead k hk
  · rw [lprod_conj, ← A.lprod_seg_r, hr', seg_succ]
    simp [Z, mul_assoc]

/-- One step of `exists_P_inv_mul_mem`: if the first letter `e` of `g = e * k` lies in the factor
of `ℓ 0` and the claim holds for `k` and every axis, it holds for `g`. Either `ℓ 0⁻¹ * e` lies in
the amalgamated subgroup, and `g` lies on the axis shifted by one, or `g⁻¹ * P r * g` has more than
`r` letters. -/
private theorem exists_P_inv_mul_mem_step (hφ : ∀ b, Injective (φ b)) (A : Axis φ) {j : Bool}
    {e : PushoutI φ} {K : List (Bool × PushoutI φ)} (hK : IsRed ((j, e) :: K)) (hj : j = (A.ℓ 0).1)
    (ih : ∀ (A' : Axis φ) (c : H) (L : List (Bool × PushoutI φ)), IsRed L → L.length ≤ A'.r →
      (base φ c * lprod K)⁻¹ * A'.P A'.r * (base φ c * lprod K) = lprod L →
      ∃ m, (A'.P m)⁻¹ * (base φ c * lprod K) ∈ (base φ).range)
    {L : List (Bool × PushoutI φ)} (hL : IsRed L) (hLr : L.length ≤ A.r)
    (hconj : (e * lprod K)⁻¹ * A.P A.r * (e * lprod K) = lprod L) :
    ∃ m, (A.P m)⁻¹ * (e * lprod K) ∈ (base φ).range := by
  by_cases hd : (A.ℓ 0).2⁻¹ * e ∈ (base φ).range
  · obtain ⟨c, hc⟩ := hd
    have hg : e * lprod K = A.P 1 * (base φ c * lprod K) := by
      rw [A.P_one, hc]
      group
    obtain ⟨m, hm⟩ := ih (A.shift 1) c L hL hLr (by
      simp only [shift]
      rw [add_comm, A.P_add_r 1]
      rw [hg] at hconj
      simpa [mul_assoc] using hconj)
    refine ⟨m + 1, ?_⟩
    rw [hg]
    simpa [shift, mul_assoc] using hm
  · obtain ⟨L', hL', hlen, heq⟩ := A.exists_conj_eq_lprod_of_notMem hK hj hd
    have := hL'.length_eq hφ hL (h := 1) (h' := 1) (by rw [← heq, hconj])
    omega

/-- **The elements with a short conjugate of `P r` lie on the axis.** If `g⁻¹ * P r * g` is the
product of a reduced word with at most `r` letters, then `g ∈ P m C` for some `m`. -/
private theorem exists_P_inv_mul_mem (hφ : ∀ b, Injective (φ b)) :
    ∀ (K : List (Bool × PushoutI φ)), IsRed K → ∀ (A : Axis φ) (c : H)
      (L : List (Bool × PushoutI φ)), IsRed L → L.length ≤ A.r →
      (base φ c * lprod K)⁻¹ * A.P A.r * (base φ c * lprod K) = lprod L →
      ∃ m, (A.P m)⁻¹ * (base φ c * lprod K) ∈ (base φ).range
  | [], _, A, c, _, _, _, _ => ⟨0, by simp [A.P_zero]⟩
  | (j, e) :: K, hK, A, c, L, hL, hLr, hconj => by
    have hK' : IsRed ((j, base φ c * e) :: K) := by
      obtain ⟨he, hhead, hKred⟩ := isRed_cons.1 hK
      exact isRed_cons.2 ⟨he.base_mul c, hhead, hKred⟩
    have ih := exists_P_inv_mul_mem hφ K (isRed_cons.1 hK).2.2
    have hg : base φ c * lprod ((j, e) :: K) = base φ c * e * lprod K := by
      rw [lprod_cons, mul_assoc]
    rw [hg] at hconj ⊢
    by_cases hj : j = (A.ℓ 0).1
    · exact A.exists_P_inv_mul_mem_step hφ hK' hj ih hL hLr hconj
    · -- The first letter is in the factor of `ℓ (-1)`: read the axis backwards.
      have hj' : j = (A.reverse.ℓ 0).1 := by
        have h := A.ne (-1)
        rw [neg_add_cancel] at h
        simp only [reverse, sub_zero]
        revert hj h
        cases j <;> cases (A.ℓ 0).1 <;> cases (A.ℓ (-1)).1 <;> simp
      obtain ⟨m, hm⟩ := A.reverse.exists_P_inv_mul_mem_step hφ hK' hj' ih (isRed_revInv hL)
        (by simpa [reverse] using hLr) (by
          simp only [reverse]
          rw [A.P_neg_r, lprod_revInv, ← hconj]
          group)
      exact ⟨-m, by simpa [reverse] using hm⟩

/-- `P a⁻¹ * P b` is a reduced word with `|b - a|` letters. -/
private theorem exists_P_inv_mul_P (A : Axis φ) (a b : ℤ) :
    ∃ L, IsRed L ∧ L.length = (b - a).natAbs ∧ (A.P a)⁻¹ * A.P b = lprod L := by
  rcases le_total a b with h | h
  · obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le (sub_nonneg.2 h)
    obtain rfl : b = a + k := by omega
    refine ⟨A.seg a k, A.isRed_seg a k, by simp, ?_⟩
    rw [A.P_add, inv_mul_cancel_left]
  · obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le (sub_nonneg.2 h)
    obtain rfl : a = b + k := by omega
    refine ⟨revInv (A.seg b k), isRed_revInv (A.isRed_seg b k), by simp, ?_⟩
    rw [lprod_revInv, A.P_add, mul_inv_rev, inv_mul_cancel_right]

/-- The cosets `P m C` of the axis are distinct. -/
private theorem eq_of_P_inv_mul_P_mem (hφ : ∀ b, Injective (φ b)) (A : Axis φ) {a b : ℤ}
    (h : (A.P a)⁻¹ * A.P b ∈ (base φ).range) : a = b := by
  obtain ⟨L, hL, hlen, heq⟩ := A.exists_P_inv_mul_P a b
  obtain ⟨c, hc⟩ := h
  have := hL.length_eq hφ isRed_nil (h := 1) (h' := c) (by simp [← heq, hc])
  rw [this, List.length_nil, eq_comm, Int.natAbs_eq_zero, sub_eq_zero] at hlen
  exact hlen.symm

/-- An element maps a coset `P m C` of the axis into at most one coset `P k C`. -/
private theorem eq_of_mem_of_mem (hφ : ∀ b, Injective (φ b)) (A : Axis φ) {y : PushoutI φ}
    {m k k' : ℤ} (hk : (A.P k)⁻¹ * (y * A.P m) ∈ (base φ).range)
    (hk' : (A.P k')⁻¹ * (y * A.P m) ∈ (base φ).range) : k = k' :=
  A.eq_of_P_inv_mul_P_mem hφ (by simpa [mul_assoc] using mul_mem hk (inv_mem hk'))

/-- Consecutive cosets of the axis differ by one letter. -/
private theorem eq_add_one_or_eq_sub_one (hφ : ∀ b, Injective (φ b)) (A : Axis φ) {a b : ℤ}
    {c c' : H} {l : Bool × PushoutI φ} (hl : IsLetter l)
    (h : (A.P a)⁻¹ * A.P b = base φ c * l.2 * base φ c') : b = a + 1 ∨ b = a - 1 := by
  obtain ⟨L, hL, hlen, heq⟩ := A.exists_P_inv_mul_P a b
  have := hL.length_eq hφ (isRed_singleton.2 (hl.mul_base c')) (h := 1) (h' := c)
    (by simp [← heq, h, mul_assoc])
  rw [this, List.length_singleton, eq_comm, Int.natAbs_eq_iff] at hlen
  omega

/-- An element commuting with `P r` maps each coset `P m C` of the axis to a coset of the
axis. -/
private theorem exists_P_inv_mul_mul_P_mem (hφ : ∀ b, Injective (φ b)) (A : Axis φ) {y : PushoutI φ}
    (hy : Commute y (A.P A.r)) (m : ℤ) :
    ∃ k, (A.P k)⁻¹ * (y * A.P m) ∈ (base φ).range := by
  obtain ⟨c, K, hK, hg⟩ := exists_eq_base_mul_lprod hφ (y * A.P m)
  rw [hg]
  refine A.exists_P_inv_mul_mem hφ K hK c (A.seg m A.r) (A.isRed_seg m _) (by simp) ?_
  have hseg : lprod (A.seg m A.r) = (A.P m)⁻¹ * (A.P A.r * A.P m) := by
    rw [← A.P_add_r, A.P_add, inv_mul_cancel_left]
  have hconj : y⁻¹ * A.P A.r * y = A.P A.r := by rw [mul_assoc, ← hy.eq, inv_mul_cancel_left]
  rw [← hg, hseg]
  nth_rw 2 [← hconj]
  group

/-- **An element commuting with `P r` translates the axis**: there is `τ` with
`y * P m ∈ P (m + τ) C` for all `m`. -/
private theorem exists_translation (hφ : ∀ b, Injective (φ b)) (A : Axis φ) {y : PushoutI φ}
    (hy : Commute y (A.P A.r)) :
    ∃ τ : ℤ, ∀ m, (A.P (m + τ))⁻¹ * (y * A.P m) ∈ (base φ).range := by
  choose σ hσ using A.exists_P_inv_mul_mul_P_mem hφ hy
  have hinj : Injective σ := fun m m' h => A.eq_of_P_inv_mul_P_mem hφ (by
    have := mul_mem (inv_mem (hσ m)) (hσ m')
    rw [h] at this
    simpa [mul_assoc] using this)
  have hstep (m : ℤ) : σ (m + 1) = σ m + 1 ∨ σ (m + 1) = σ m - 1 := by
    obtain ⟨c, hc⟩ := hσ m
    obtain ⟨c', hc'⟩ := hσ (m + 1)
    refine A.eq_add_one_or_eq_sub_one hφ (A.isLetter m) (c := c) (c' := c'⁻¹) ?_
    rw [map_inv, hc, hc', A.P_succ]
    group
  have hper (m : ℤ) : σ (m + A.r) = σ m + A.r := by
    refine (A.eq_of_mem_of_mem hφ ?_ (hσ (m + A.r))).symm
    have h : (A.P (σ m + A.r))⁻¹ * (y * A.P (m + A.r)) = (A.P (σ m))⁻¹ * (y * A.P m) := by
      rw [A.P_add_r, A.P_add_r, ← mul_assoc y, hy.eq]
      group
    exact h ▸ hσ m
  -- The period excludes a reflection of the axis.
  have htr : ∀ m, σ m = σ 0 + m :=
    (Int.forall_eq_add_or_forall_eq_sub_of_injective_of_step hinj hstep).resolve_right fun h => by
      have h0 := hper 0
      rw [h (0 + A.r)] at h0
      have := A.r_pos
      omega
  refine ⟨σ 0, fun m => ?_⟩
  rw [add_comm, ← htr m]
  exact hσ m

/-- **The pointwise stabilizer of the axis is trivial** when the amalgamated subgroup is
malnormal in one factor: the axis passes through a vertex of that factor, where the stabilizer of
the two adjacent edges is `C ∩ a⁻¹ C a = 1` for a letter `a ∉ C`. -/
private theorem eq_one_of_forall_mem (hφ : ∀ b, Injective (φ b)) (A : Axis φ) {b : Bool}
    (hT : TauCeti.IsTISubgroup (φ b).range) {y : PushoutI φ}
    (hy : ∀ m, (A.P m)⁻¹ * (y * A.P m) ∈ (base φ).range) : y = 1 := by
  obtain ⟨m, hm⟩ : ∃ m, (A.ℓ m).1 = b := by
    by_cases h : (A.ℓ 0).1 = b
    · exact ⟨0, h⟩
    · refine ⟨1, ?_⟩
      have := A.ne 0
      rw [zero_add] at this
      revert h this
      cases b <;> cases (A.ℓ 0).1 <;> cases (A.ℓ 1).1 <;> simp
  obtain ⟨c₀, hc₀⟩ := hy m
  obtain ⟨c₁, hc₁⟩ := hy (m + 1)
  obtain ⟨a, ha⟩ : (A.ℓ m).2 ∈ (of (φ := φ) b).range := hm ▸ (A.isLetter m).1
  have ha' : a⁻¹ ∉ (φ b).range := fun h => (A.isLetter m).2 (by
    obtain ⟨c, hc⟩ := inv_mem_iff.1 h
    exact MonoidHom.mem_range.2 ⟨c, by rw [← ha, ← hc, of_apply_eq_base]⟩)
  have key : of (φ := φ) b (φ b c₁) = of b (a⁻¹ * φ b c₀ * a) := by
    rw [map_mul, map_mul, map_inv, of_apply_eq_base, of_apply_eq_base, ha, hc₀, hc₁, A.P_succ]
    group
  have h1 : φ b c₀ = 1 := hT.eq_one ha' (MonoidHom.mem_range.2 ⟨c₀, rfl⟩)
    (by rw [inv_inv, ← of_injective hφ b key]; exact MonoidHom.mem_range.2 ⟨c₁, rfl⟩)
  have h2 : (A.P m)⁻¹ * (y * A.P m) = 1 := by
    rw [← hc₀, ← of_apply_eq_base φ b, h1, map_one]
  simpa [mul_assoc] using congrArg (fun z => A.P m * z * (A.P m)⁻¹) h2

/-- **The centralizer of the cyclically reduced element `P r` is cyclic**, when the amalgamated
subgroup is malnormal in one factor: it acts on the axis by translations, faithfully. -/
private theorem isCyclic_centralizer (hφ : ∀ b, Injective (φ b)) (A : Axis φ) {b : Bool}
    (hT : TauCeti.IsTISubgroup (φ b).range) : IsCyclic (Subgroup.centralizer {A.P A.r}) := by
  choose τ hτ using fun y : Subgroup.centralizer {A.P A.r} =>
    A.exists_translation hφ (Subgroup.mem_centralizer_singleton_iff.1 y.property)
  have hmul (y z : Subgroup.centralizer {A.P A.r}) : τ (y * z) = τ y + τ z := by
    have h : (A.P (0 + (τ z + τ y)))⁻¹ * ((y * z : Subgroup.centralizer _) * A.P 0) ∈
        (base φ).range := by
      simpa [mul_assoc] using mul_mem (hτ y (τ z)) (hτ z 0)
    simpa [add_comm] using A.eq_of_mem_of_mem hφ (hτ (y * z) 0) h
  refine isCyclic_of_injective (MonoidHom.mk' (fun y => Multiplicative.ofAdd (τ y)) fun y z => by
    rw [hmul, ofAdd_add]) ((injective_iff_map_eq_one _).2 fun y hy => Subtype.ext ?_)
  have hy0 : τ y = 0 := by simpa using hy
  exact A.eq_one_of_forall_mem hφ hT fun m => by simpa [hy0] using hτ y m

end Axis

private theorem lprod_take_add_one (Z : List (Bool × PushoutI φ)) (j : ℕ) (hj : j < Z.length) :
    lprod (Z.take (j + 1)) = lprod (Z.take j) * Z[j].2 := by
  rw [List.take_add_one, List.getElem?_eq_getElem hj, Option.toList_some, lprod_append,
    lprod_cons, lprod_nil, mul_one]

namespace Axis

/-- The axis of a cyclically reduced word `Z`: the letters of `Z` repeated periodically, with
`P m = Z ^ q * (the first j letters of Z)` for `m = q * |Z| + j`. -/
private def ofList (Z : List (Bool × PushoutI φ)) (hZ : IsRed Z) (hne : Z ≠ [])
    (hcyc : (Z.head hne).1 ≠ (Z.getLast hne).1) : Axis φ where
  ℓ m := Z.getD (m % Z.length).toNat (false, 1)
  P m := lprod Z ^ (m / Z.length) * lprod (Z.take (m % Z.length).toNat)
  r := Z.length
  r_pos := List.length_pos_of_ne_nil hne
  isLetter m := by
    have hlt : (m % Z.length).toNat < Z.length := Int.natMod_lt (List.length_pos_of_ne_nil hne).ne'
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]
    exact hZ.2 _ (List.getElem_mem _)
  ne m := by
    have hn := List.length_pos_of_ne_nil hne
    have hlt : (m % Z.length).toNat < Z.length := Int.natMod_lt hn.ne'
    have h0 := Int.emod_nonneg m (b := Z.length) (by omega)
    have h1 := Int.emod_lt_of_pos m (b := Z.length) (by omega)
    simp only [List.getD_eq_getElem?_getD]
    obtain h | h : m % Z.length + 1 < Z.length ∨ m % Z.length + 1 = Z.length := by omega
    · have hj : (m % Z.length).toNat + 1 < Z.length := by omega
      have hk : (m % Z.length + 1).toNat = (m % Z.length).toNat + 1 := by omega
      rw [Int.add_one_emod_of_emod_add_one_lt h, hk, List.getElem?_eq_getElem hj,
        List.getElem?_eq_getElem hlt]
      exact (hZ.1.getElem _ hj).symm
    · rw [Int.add_one_emod_of_emod_add_one_eq h, Int.toNat_zero, List.getElem?_eq_getElem hn,
        List.getElem?_eq_getElem hlt]
      have hidx : (m % (Z.length : ℤ)).toNat = Z.length - 1 := by omega
      rw [List.head_eq_getElem, List.getLast_eq_getElem] at hcyc
      simpa [hidx] using hcyc
  periodic m := by rw [Int.add_emod_right]
  P_zero := by simp
  P_succ m := by
    have hn := List.length_pos_of_ne_nil hne
    have hlt : (m % Z.length).toNat < Z.length := Int.natMod_lt hn.ne'
    have h0 := Int.emod_nonneg m (b := Z.length) (by omega)
    have h1 := Int.emod_lt_of_pos m (b := Z.length) (by omega)
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt, Option.getD_some]
    obtain h | h : m % Z.length + 1 < Z.length ∨ m % Z.length + 1 = Z.length := by omega
    · have hk : (m % Z.length + 1).toNat = (m % Z.length).toNat + 1 := by omega
      rw [Int.add_one_ediv_of_emod_add_one_lt h, Int.add_one_emod_of_emod_add_one_lt h, hk,
        lprod_take_add_one _ _ hlt, mul_assoc]
    · have hZ : lprod Z = lprod (Z.take ((m % Z.length).toNat + 1)) := by
        rw [List.take_of_length_le (by omega)]
      rw [Int.add_one_ediv_of_emod_add_one_eq (by omega) h, Int.add_one_emod_of_emod_add_one_eq h,
        Int.toNat_zero, List.take_zero, lprod_nil, mul_one, zpow_add_one, mul_assoc]
      nth_rw 2 [hZ]
      rw [lprod_take_add_one _ _ hlt]

private theorem ofList_P_r (Z : List (Bool × PushoutI φ)) (hZ : IsRed Z) (hne : Z ≠ [])
    (hcyc : (Z.head hne).1 ≠ (Z.getLast hne).1) :
    (ofList Z hZ hne hcyc).P (ofList Z hZ hne hcyc).r = lprod Z := by
  have hn : (Z.length : ℤ) ≠ 0 := by exact_mod_cast (List.length_pos_of_ne_nil hne).ne'
  simp [ofList, Int.ediv_self hn]

end Axis

/-- One step of cyclic reduction: a reduced word of length `≥ 2` whose first and last letters lie
in the same factor is conjugate to `c * w` for a shorter reduced word `w`. -/
private theorem exists_conj_shorter {j : Bool} {e : PushoutI φ} {M : List (Bool × PushoutI φ)}
    {l : Bool × PushoutI φ} (hZ : IsRed ((j, e) :: (M ++ [l]))) (hl : l.1 = j) :
    ∃ (w : PushoutI φ) (c : H) (M' : List (Bool × PushoutI φ)), IsRed M' ∧
      M'.length < M.length + 2 ∧ w * lprod ((j, e) :: (M ++ [l])) * w⁻¹ = base φ c * lprod M' := by
  obtain ⟨he, -, hMl⟩ := isRed_cons.1 hZ
  obtain ⟨hM, hl', hlast⟩ := isRed_append.1 hMl
  have hconj : e⁻¹ * lprod ((j, e) :: (M ++ [l])) * e = lprod M * (l.2 * e) := by
    simp [mul_assoc]
  by_cases hm : l.2 * e ∈ (base φ).range
  · obtain ⟨c, hc⟩ := hm
    refine ⟨base φ c * e⁻¹, c, M, hM, by omega, ?_⟩
    calc _ = base φ c * (e⁻¹ * lprod ((j, e) :: (M ++ [l])) * e) * (base φ c)⁻¹ := by group
      _ = _ := by rw [hconj, ← hc]; group
  · refine ⟨e⁻¹, 1, M ++ [(j, l.2 * e)], ?_, by simp, ?_⟩
    · refine isRed_append.2 ⟨hM, isRed_singleton.2 ⟨mul_mem ?_ he.1, hm⟩, ?_⟩
      · exact hl ▸ (isRed_singleton.1 hl').1
      · simpa [hl] using hlast
    · rw [inv_inv, hconj]
      simp

/-- **Cyclic reduction.** Every element of the amalgam is conjugate into a factor or to the
cyclically reduced element `P r` of an axis. -/
private theorem exists_conj_eq_P_r (n : ℕ) :
    ∀ (K : List (Bool × PushoutI φ)), K.length = n → IsRed K → ∀ c : H,
      (∃ (i : Bool) (y : PushoutI φ), y * (base φ c * lprod K) * y⁻¹ ∈ (of (φ := φ) i).range) ∨
      ∃ (y : PushoutI φ) (A : Axis φ), y * (base φ c * lprod K) * y⁻¹ = A.P A.r := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro K hKn hK c
  rcases K with _ | ⟨⟨j, e⟩, K⟩
  · exact Or.inl ⟨false, 1, by simpa using base_range_le_of_range false ⟨c, rfl⟩⟩
  have hZ : IsRed ((j, base φ c * e) :: K) := by
    obtain ⟨he, hh, hK'⟩ := isRed_cons.1 hK
    exact isRed_cons.2 ⟨he.base_mul c, hh, hK'⟩
  have hx : base φ c * lprod ((j, e) :: K) = lprod ((j, base φ c * e) :: K) := by
    simp [mul_assoc]
  rw [hx]
  by_cases hcyc : (((j, base φ c * e) :: K).head (List.cons_ne_nil _ _)).1 ≠
      (((j, base φ c * e) :: K).getLast (List.cons_ne_nil _ _)).1
  · exact Or.inr ⟨1, Axis.ofList _ hZ _ hcyc, by simp [Axis.ofList_P_r]⟩
  rcases eq_or_ne K [] with rfl | hK'
  · exact Or.inl ⟨j, 1, by simpa using (isRed_cons.1 hZ).1.1⟩
  obtain ⟨M, l, rfl⟩ : ∃ M l, K = M ++ [l] :=
    ⟨K.dropLast, K.getLast hK', (List.dropLast_append_getLast hK').symm⟩
  have hl : l.1 = j := by
    rw [ne_eq, not_not] at hcyc
    simpa using hcyc.symm
  obtain ⟨w, c', M', hM', hlen, hw⟩ := exists_conj_shorter hZ hl
  rcases ih M'.length (by simp at hKn; omega) M' rfl hM' c' with ⟨i, y, hy⟩ | ⟨y, A, hy⟩
  · exact Or.inl ⟨i, y * w, by rw [← hw] at hy; simpa [mul_assoc] using hy⟩
  · exact Or.inr ⟨y * w, A, by rw [← hy, ← hw]; group⟩

/-- In an amalgamated product `A ∗_C B` in which `C` is malnormal in one of the factors, the
centralizer of an element conjugate into neither factor is cyclic. -/
theorem isCyclic_centralizer (hφ : ∀ b, Injective (φ b)) {b : Bool}
    (hT : TauCeti.IsTISubgroup (φ b).range) {x : PushoutI φ}
    (hx : ∀ (i : Bool) (y : PushoutI φ), y * x * y⁻¹ ∉ (of i).range) :
    IsCyclic (Subgroup.centralizer {x}) := by
  obtain ⟨c, K, hK, rfl⟩ := exists_eq_base_mul_lprod hφ x
  rcases exists_conj_eq_P_r K.length K rfl hK c with ⟨i, y, hy⟩ | ⟨y, A, hy⟩
  · exact absurd hy (hx i y)
  set x := base φ c * lprod K
  have : IsCyclic (Subgroup.centralizer {y * x * y⁻¹}) := by
    rw [hy]
    exact A.isCyclic_centralizer hφ hT
  refine isCyclic_of_injective (G' := Subgroup.centralizer {y * x * y⁻¹})
    (((MulAut.conj y).toMonoidHom.comp (Subgroup.centralizer {x}).subtype).codRestrict
      (Subgroup.centralizer {y * x * y⁻¹}) fun z => ?_) fun z₁ z₂ h => ?_
  · exact Subgroup.mem_centralizer_singleton_iff.2
      ((Commute.conj_iff y).2 (Subgroup.mem_centralizer_singleton_iff.1 z.property))
  · exact Subtype.ext (by simpa using congrArg Subtype.val h)

end Bool

end Monoid.PushoutI
