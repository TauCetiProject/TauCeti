/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.CSA
public import TauCeti.GroupTheory.PushoutI.Reduced

/-!
# Centralizers of elements of a factor of an amalgamated product

Let `φ i : H →* G i` be a family of injective group homomorphisms, with amalgamated product
`Monoid.PushoutI φ`, and let `g` be an element of a factor `G i`. In each of the following two
situations every element of the amalgamated product commuting with `g` lies in `G i`, so the
centralizer of `g` in the amalgamated product is its centralizer in `G i`.

* `g` is not conjugate in `G i` into the amalgamated subgroup `φ i H`. In the action of the
  amalgamated product on its Bass–Serre tree, such a `g` fixes the vertex `G i` and no edge at it,
  so it fixes no other vertex, and an element commuting with `g` preserves its fixed point set.
* `g` is nontrivial and the image `φ j H` is malnormal in `G j` for every other index `j`. No
  condition on `g` or on `φ i H` inside `G i` is needed, so `g` may lie in the amalgamated subgroup.
  In the Bass–Serre tree, the subtree fixed by `g` stops at the vertices of the other factors, by
  malnormality there; so it is bounded, its centre is the vertex of `G i` or the vertex of the
  amalgamated subgroup next to it, and every element commuting with `g` fixes that centre.

Malnormality cannot be dropped in the second statement: in `⟨a, b | a² = b²⟩ = ℤ ∗_{2ℤ} ℤ` the
element `a²` commutes with `b`, which does not lie in the factor `⟨a⟩`. On the other hand its
hypotheses hold in the double `G ∗_{C_G(u)} G` of a CSA group along the centralizer of an element.

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
meets `G j` only in the amalgamated subgroup.

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

/-- **Centralizers of factor elements away from the amalgamated subgroup.** If an element `g` of
a factor `G i` of an amalgamated product of groups is not conjugate in `G i` into the amalgamated
subgroup, then its centralizer in the amalgamated product is its centralizer in `G i`. -/
theorem centralizer_of_eq_map (hφ : ∀ i, Injective (φ i)) {i : ι} {g : G i}
    (hg : ∀ k : G i, k * g * k⁻¹ ∉ (φ i).range) :
    centralizer {of (φ := φ) i g} = (centralizer {g}).map (of i) := by
  refine le_antisymm (fun x hx => ?_) ?_
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
  · simpa using map_centralizer_le_centralizer_image {g} (of (φ := φ) i)

/-- In an amalgamated product of groups, let `w` be the product of a nonempty list of letters,
consecutive ones from different factors and none of them in the amalgamated subgroup, whose first
letter is not in `G i`, and suppose that the amalgamated subgroup is malnormal in every factor other
than `G i`. Then `w` conjugates no nontrivial element of the amalgamated subgroup into `G i`. -/
private theorem list_prod_inv_mul_base_mul_list_prod_notMem_range (hφ : ∀ i, Injective (φ i))
    {i : ι} (hH : ∀ j, j ≠ i → TauCeti.IsTISubgroup (φ j).range) {L : List (Σ i, G i)} (hL : L ≠ [])
    (hc : L.IsChain fun l l' => l.1 ≠ l'.1) (hred : ∀ l ∈ L, l.2 ∉ (φ l.1).range)
    (hi : ∀ l ∈ L.head?, l.1 ≠ i) {h : H} (h1 : h ≠ 1) :
    (L.map fun l => of l.1 l.2).prod⁻¹ * base φ h * (L.map fun l => of l.1 l.2).prod ∉
      (of (φ := φ) i).range := by
  -- The first letter `k` of `w` lies in a factor `G j` with `j ≠ i`, where `k⁻¹ * h * k` is
  -- outside the amalgamated subgroup by malnormality.
  obtain ⟨⟨j, k⟩, L₁, rfl⟩ := List.exists_cons_of_ne_nil hL
  have hji : j ≠ i := hi _ rfl
  have hm : k⁻¹ * φ j h * k ∉ (φ j).range := by
    simpa using (hH j hji).conj_notMem (g := k⁻¹) (by simpa using hred _ List.mem_cons_self)
      ⟨h, rfl⟩ ((map_ne_one_iff _ (hφ j)).2 h1)
  have hconj : ((⟨j, k⟩ :: L₁).map fun l => of (φ := φ) l.1 l.2).prod⁻¹ * base φ h *
      ((⟨j, k⟩ :: L₁).map fun l => of l.1 l.2).prod = (L₁.map fun l => of (φ := φ) l.1 l.2).prod⁻¹ *
        of j (k⁻¹ * φ j h * k) * (L₁.map fun l => of l.1 l.2).prod := by
    rw [← of_apply_eq_base φ j]
    simp [mul_assoc]
  rw [hconj]
  rcases eq_or_ne L₁ [] with rfl | hL₁
  · -- A letter of `G j` outside the amalgamated subgroup is not in `G i`.
    intro hmem
    obtain ⟨h', hh'⟩ : of j (k⁻¹ * φ j h * k) ∈ (base φ).range := by
      rw [← inf_of_range_eq_base_range hφ hji]
      exact ⟨⟨_, rfl⟩, by simpa using hmem⟩
    exact hm ⟨h', of_injective hφ j (by rw [of_apply_eq_base, hh'])⟩
  · exact list_prod_inv_mul_of_mul_list_prod_notMem_range_of hφ hL₁ (List.isChain_cons.1 hc).2
      (fun l hl => hred l (List.mem_cons_of_mem _ hl)) hm
      (fun l hl => ((List.isChain_cons.1 hc).1 l hl).symm)

/-- **Centralizers in an amalgam with malnormal edge group.** If the structure maps are injective
and their images are malnormal in the factors other than `G i`, the centralizer in the amalgam of a
nontrivial element `g` of `G i` is the image of its centralizer in `G i`. -/
theorem centralizer_of_eq_map_of_isTISubgroup (hφ : ∀ j, Injective (φ j)) {i : ι}
    (hH : ∀ j, j ≠ i → TauCeti.IsTISubgroup (φ j).range) {g : G i} (hg : g ≠ 1) :
    centralizer {(of i g : PushoutI φ)} = (centralizer {g}).map (of i) := by
  refine le_antisymm (fun x hx => ?_) ?_
  · -- Write `x = a * w`, with `a ∈ G i` and `w` a reduced word not starting in `G i`; then `w`
    -- conjugates `a⁻¹ * g * a` to `g`, which forces `w = 1`.
    obtain ⟨a, L, hc, hred, hhead, rfl⟩ := exists_eq_of_mul_list_prod i x
    have hconj : (L.map fun l => of (φ := φ) l.1 l.2).prod⁻¹ * of i (a⁻¹ * g * a) *
        (L.map fun l => of l.1 l.2).prod = of i g := by
      have hx' : (of (φ := φ) i a * (L.map fun l => of l.1 l.2).prod)⁻¹ * of i g *
          (of i a * (L.map fun l => of l.1 l.2).prod) = of i g := by
        rw [mul_assoc, ← mem_centralizer_singleton_iff.1 hx, inv_mul_cancel_left]
      simpa [mul_assoc] using hx'
    rcases eq_or_ne L [] with rfl | hL
    · refine ⟨a, mem_centralizer_singleton_iff.2 (of_injective hφ i ?_), by simp⟩
      simpa using (mem_centralizer_singleton_iff.1 hx).eq
    exfalso
    by_cases hgr : a⁻¹ * g * a ∈ (φ i).range
    · obtain ⟨h, hh⟩ := hgr
      have hg' : a⁻¹ * g * a ≠ 1 := by simpa [mul_assoc, inv_mul_eq_one] using hg
      refine list_prod_inv_mul_base_mul_list_prod_notMem_range hφ hH hL hc hred hhead (h := h)
        (fun h1 => hg' (by rw [← hh, h1, map_one])) ⟨g, ?_⟩
      rw [← of_apply_eq_base φ i, hh, hconj]
    · exact list_prod_inv_mul_of_mul_list_prod_notMem_range_of hφ hL hc hred hgr hhead
        ⟨g, hconj.symm⟩
  · simpa using map_centralizer_le_centralizer_image {g} (of (φ := φ) i)

/-! ### Examples -/

/-- In the double `G ∗_{C_G(u)} G` of a CSA group along the centralizer of `u`, the centralizer of
a nontrivial element of the first copy of `G` is its centralizer in `G`. -/
example {K : Type*} [Group K] (hK : Group.IsCSA K) (u : K) {g : K} (hg : g ≠ 1) :
    centralizer {(of false g : PushoutI fun _ : Bool => (centralizer {u}).subtype)} =
      (centralizer {g}).map (of (φ := fun _ : Bool => (centralizer {u}).subtype) false) :=
  centralizer_of_eq_map_of_isTISubgroup (fun _ => Subtype.val_injective)
    (fun _ _ => by simpa using hK.centralizer_isTISubgroup u) hg

/-- Malnormality cannot be dropped: in `ℤ ∗_{2ℤ} ℤ = ⟨a, b | a² = b²⟩`, whose edge group `2ℤ` is
not malnormal in `ℤ`, the generator `b` of the second factor commutes with the element `a²` of
the first factor without lying in the first factor. -/
example : ∃ y ∈ centralizer {(of false (.ofAdd 2) :
      PushoutI fun _ : Bool => (powMonoidHom 2 : Multiplicative ℤ →* Multiplicative ℤ))},
    y ∉ (of false).range := by
  set φ₂ : Bool → Multiplicative ℤ →* Multiplicative ℤ := fun _ => powMonoidHom 2
  have hφ : ∀ b, Injective (φ₂ b) := fun _ m n h => by
    simpa [φ₂] using congrArg (fun z : Multiplicative ℤ => z.toAdd) h
  have h2 (b : Bool) : of (φ := φ₂) b (.ofAdd 2) = base φ₂ (.ofAdd 1) := by
    rw [← of_apply_eq_base φ₂ b]
    rfl
  refine ⟨of true (.ofAdd 1), mem_centralizer_singleton_iff.2 ?_, fun hy => ?_⟩
  · rw [h2 false, ← h2 true]
    exact (Commute.all _ _).map (of true)
  · obtain ⟨h, hh⟩ : of (φ := φ₂) true (.ofAdd 1) ∈ (base φ₂).range := by
      rw [← inf_of_range_eq_base_range hφ (by simp : true ≠ false)]
      exact ⟨⟨_, rfl⟩, hy⟩
    rw [← of_apply_eq_base φ₂ true] at hh
    have := congrArg (fun z : Multiplicative ℤ => z.toAdd) (of_injective hφ true hh)
    simp [φ₂] at this
    omega

end Monoid.PushoutI
