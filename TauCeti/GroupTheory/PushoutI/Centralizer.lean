/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.PushoutI.Reduced
public import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# Centralizers of elements of a factor of an amalgamated product

Let `φ i : H →* G i` be a family of injective group homomorphisms, with amalgamated product
`Monoid.PushoutI φ`, and let `g` be an element of a factor `G i`. In each of the following two
situations every element of the amalgamated product commuting with `g` lies in `G i`, so the
centralizer of `g` in the amalgamated product is its centralizer in `G i`.

* `g` is not conjugate in `G i` into the amalgamated subgroup `φ i H`. In the action of the
  amalgamated product on its Bass–Serre tree, such a `g` fixes the vertex `G i` and no edge at it,
  so it fixes no other vertex, and an element commuting with `g` preserves its fixed point set.
* `g` is nontrivial and the image `φ j H` is malnormal in `G j` for every other index `j`. Beyond
  `g ≠ 1`, no condition on `g` or on `φ i H` inside `G i` is needed, so `g` may lie in the
  amalgamated subgroup. In the Bass–Serre tree, the vertex of `G i` is the only vertex of type `i`
  fixed by `g`: `g` would also fix the path to another one, which passes through a vertex of a
  factor `G j` with `j ≠ i`, entering and leaving it along two different edges, while by
  malnormality of `φ j H` in `G j` a nontrivial element fixes at most one edge there. An element
  commuting with `g` preserves the set of vertices fixed by `g`, and the action preserves the
  types of vertices, so it fixes the vertex of `G i`.

Malnormality cannot be dropped in the second statement: in `⟨a, b | a² = b²⟩ = ℤ ∗_{2ℤ} ℤ` the
element `a²` commutes with `b`, which does not lie in the factor `⟨a⟩`. On the other hand its
hypotheses hold in the double `G ∗_C G` of a group along a malnormal subgroup `C`, for instance
along the centralizer of a nontrivial element of a CSA group.

## Main results

* `Monoid.PushoutI.centralizer_of_eq_map`: the centralizer of an element of a factor that is not
  conjugate in that factor into the amalgamated subgroup.
* `Monoid.PushoutI.centralizer_of_eq_map_of_isTISubgroup`: the centralizer of a nontrivial factor
  element in an amalgam whose edge groups are malnormal in the other factors.

## Implementation notes

The proofs use normal forms rather than the Bass–Serre tree. Write an element `x` commuting with
`g` as `a * w` with `a ∈ G i` and `w` the product of a reduced word not starting in `G i`
(`Monoid.PushoutI.exists_eq_of_mul_list_prod`). If `w` is nontrivial, then `g` is the conjugate
`w⁻¹ * g' * w` of `g' = a⁻¹ * g * a`. When `g'` is outside the amalgamated subgroup, as it always
is in the first situation, this conjugate is a reduced word of length at least three, which lies
in no factor (`Monoid.PushoutI.list_prod_inv_mul_of_mul_list_prod_notMem_range_of`). When `g'`
lies in the amalgamated subgroup, malnormality turns the first letter `k ∈ G j` of `w` into the
letter `k⁻¹ * g' * k` outside the amalgamated subgroup, and the conjugate is a reduced word that is
either of length at least three or a single letter of `G j`. Neither lies in `G i`, since `G i`
meets `G j` only in the amalgamated subgroup
(`Monoid.PushoutI.list_prod_inv_mul_base_mul_list_prod_notMem_range`). The two theorems share the
reduction to these conjugates and differ only in how they rule them out.

## References

* W. Magnus, A. Karrass, D. Solitar, *Combinatorial group theory*, Theorem 4.5 (commuting
  elements of an amalgamated product), as used in G. Baumslag, A. Myasnikov, V. Remeslennikov,
  *Algebraic geometry over groups I: Algebraic sets and ideal theory*, J. Algebra 219 (1999),
  proof of Theorem A2.
* J.-P. Serre, *Trees*, Springer (1980), Chapter I, §1.2, Theorem 1 (the normal form theorem for
  amalgamated products) and §4 (the tree of an amalgam).
* R. C. Lyndon, P. E. Schupp, *Combinatorial Group Theory*, Springer (1977), Chapter IV, §2
  (free products with amalgamation).
-/

public section

namespace Monoid.PushoutI

open Function Subgroup

variable {ι : Type*} {G : ι → Type*} {H : Type*} [∀ i, Group (G i)] [Group H]
  {φ : ∀ i, H →* G i}

/-- Let `g` be an element of a factor `G i` of an amalgamated product of groups. Suppose that for
every `a ∈ G i` and every product `w` of a nonempty list of letters, consecutive ones from different
factors, none of them in the amalgamated subgroup and the first not in `G i`, the conjugate
`w⁻¹ * (a⁻¹ * g * a) * w` is not in `G i`. Then the centralizer of `g` in the amalgamated product
is its centralizer in `G i`. -/
private theorem centralizer_of_eq_map_of_forall (hφ : ∀ i, Injective (φ i)) {i : ι} {g : G i}
    (hg : ∀ (a : G i) (L : List (Σ i, G i)), L ≠ [] → L.IsChain (fun l l' => l.1 ≠ l'.1) →
      (∀ l ∈ L, l.2 ∉ (φ l.1).range) → (∀ l ∈ L.head?, l.1 ≠ i) →
      (L.map fun l => of l.1 l.2).prod⁻¹ * of i (a⁻¹ * g * a) * (L.map fun l => of l.1 l.2).prod ∉
        (of (φ := φ) i).range) :
    centralizer {of (φ := φ) i g} = (centralizer {g}).map (of i) := by
  refine le_antisymm (fun x hx => ?_) ?_
  · -- Write `x = a * w`, with `a ∈ G i` and `w` a reduced word not starting in `G i`; then `w`
    -- conjugates `a⁻¹ * g * a` to `g`, which forces `w = 1`.
    obtain ⟨a, L, hc, hred, hhead, rfl⟩ := exists_eq_of_mul_list_prod i x
    rcases eq_or_ne L [] with rfl | hL
    · refine ⟨a, mem_centralizer_singleton_iff.2 (of_injective hφ i ?_), by simp⟩
      simpa using (mem_centralizer_singleton_iff.1 hx).eq
    refine (hg a L hL hc hred hhead ⟨g, ?_⟩).elim
    have hx' : (of (φ := φ) i a * (L.map fun l => of l.1 l.2).prod)⁻¹ * of i g *
        (of i a * (L.map fun l => of l.1 l.2).prod) = of i g := by
      rw [mul_assoc, ← mem_centralizer_singleton_iff.1 hx, inv_mul_cancel_left]
    simpa [mul_assoc] using hx'.symm
  · simpa using map_centralizer_le_centralizer_image {g} (of (φ := φ) i)

/-- **Centralizers of factor elements away from the amalgamated subgroup.** If an element `g` of
a factor `G i` of an amalgamated product of groups is not conjugate in `G i` into the amalgamated
subgroup, then its centralizer in the amalgamated product is its centralizer in `G i`. -/
theorem centralizer_of_eq_map (hφ : ∀ i, Injective (φ i)) {i : ι} {g : G i}
    (hg : ∀ k : G i, k * g * k⁻¹ ∉ (φ i).range) :
    centralizer {of (φ := φ) i g} = (centralizer {g}).map (of i) :=
  -- Each conjugate `w⁻¹ * (a⁻¹ * g * a) * w` is a reduced word of length at least three.
  centralizer_of_eq_map_of_forall hφ fun a _ hL hc hred hhead =>
    list_prod_inv_mul_of_mul_list_prod_notMem_range_of hφ hL hc hred (by simpa using hg a⁻¹) hhead

/-- **Centralizers in an amalgam with malnormal edge group.** If the structure maps are injective
and their images are malnormal in the factors other than `G i`, the centralizer in the amalgam of a
nontrivial element `g` of `G i` is the image of its centralizer in `G i`. -/
theorem centralizer_of_eq_map_of_isTISubgroup (hφ : ∀ j, Injective (φ j)) {i : ι}
    (hH : ∀ j, j ≠ i → TauCeti.IsTISubgroup (φ j).range) {g : G i} (hg : g ≠ 1) :
    centralizer {(of i g : PushoutI φ)} = (centralizer {g}).map (of i) := by
  refine centralizer_of_eq_map_of_forall hφ fun a L hL hc hred hhead => ?_
  by_cases hgr : a⁻¹ * g * a ∈ (φ i).range
  · obtain ⟨h, hh⟩ := hgr
    have hg' : a⁻¹ * g * a ≠ 1 := by simpa [mul_assoc, inv_mul_eq_one] using hg
    rw [← hh, of_apply_eq_base]
    exact list_prod_inv_mul_base_mul_list_prod_notMem_range hφ hH hL hc hred hhead
      fun h1 => hg' (by rw [← hh, h1, map_one])
  · exact list_prod_inv_mul_of_mul_list_prod_notMem_range_of hφ hL hc hred hgr hhead

/-! ### Examples -/

/-- In the double `K ∗_C K` of a group along a malnormal subgroup `C`, for instance the centralizer
of a nontrivial element of a CSA group, the centralizer of a nontrivial element of the first copy
of `K` is its centralizer in `K`. -/
example {K : Type*} [Group K] {C : Subgroup K} (hC : TauCeti.IsTISubgroup C) {g : K}
    (hg : g ≠ 1) :
    centralizer {(of false g : PushoutI fun _ : Bool => C.subtype)} =
      (centralizer {g}).map (of (φ := fun _ : Bool => C.subtype) false) :=
  centralizer_of_eq_map_of_isTISubgroup (fun _ => Subtype.val_injective)
    (fun _ _ => by simpa using hC) hg

/-- Malnormality cannot be dropped: in `ℤ ∗_{2ℤ} ℤ = ⟨a, b | a² = b²⟩`, whose edge group `2ℤ` is
not malnormal in `ℤ`, the generator `b` of the second factor commutes with the element `a²` of
the first factor without lying in the first factor. -/
example : ∃ y ∈ centralizer {(of false (.ofAdd 2) :
      PushoutI fun _ : Bool => (powMonoidHom 2 : Multiplicative ℤ →* Multiplicative ℤ))},
    y ∉ (of false).range := by
  set φ₂ : Bool → Multiplicative ℤ →* Multiplicative ℤ := fun _ => powMonoidHom 2
  have hφ : ∀ b, Injective (φ₂ b) := fun _ m n h => by
    simpa [φ₂] using congrArg (fun z : Multiplicative ℤ => z.toAdd) h
  have hp (b : Bool) : φ₂ b (.ofAdd 1) = .ofAdd 2 :=
    Multiplicative.toAdd.injective (by simp [φ₂])
  have h2 (b : Bool) : of (φ := φ₂) b (.ofAdd 2) = base φ₂ (.ofAdd 1) := by
    rw [← of_apply_eq_base φ₂ b, hp b]
  refine ⟨of true (.ofAdd 1), mem_centralizer_singleton_iff.2 ?_, ?_⟩
  · rw [h2 false, ← h2 true]
    exact (Commute.all _ _).map (of true)
  · -- `ofAdd 1` is not in the image `2ℤ` of the edge group.
    rw [of_mem_range_of_iff hφ (by simp : true ≠ false)]
    rintro ⟨m, hm⟩
    have := congrArg Multiplicative.toAdd hm
    simp [φ₂] at this
    omega

end Monoid.PushoutI
