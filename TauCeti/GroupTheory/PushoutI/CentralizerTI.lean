/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.CSA
public import TauCeti.GroupTheory.PushoutI.Reduced

/-!
# Centralizers of factor elements in an amalgam with malnormal edge groups

Let `Monoid.PushoutI φ` be the amalgamated product of groups `G i` over a group `H`, with
injective structure maps `φ i : H →* G i`, and let `x` be a nontrivial element of a factor `G i`.
Suppose that the image `φ j H` is malnormal in `G j` for every other index `j`. Then `x` commutes,
in the amalgam, only with elements of `G i`: its centralizer is the image of the centralizer of `x`
in `G i` (`Monoid.PushoutI.centralizer_of_eq_map_of_isTISubgroup`). No condition on `x` or on
`φ i H` inside `G i` is needed, so `x` may lie in the amalgamated subgroup.

In the Bass–Serre tree, the subtree fixed by `x` stops at the vertices of the other factors, by
malnormality there; so it is bounded, its centre is the vertex of `G i` or the vertex of the
amalgamated subgroup next to it, and every element commuting with `x` fixes that centre.

Malnormality cannot be dropped: in `⟨a, b | a² = b²⟩ = ℤ ∗_{2ℤ} ℤ` the element `a²` commutes with
`b`, which does not lie in the factor `⟨a⟩`. On the other hand the hypotheses hold in the double
`G ∗_{C_G(u)} G` of a CSA group along the centralizer of an element.

## Main results

* `Monoid.PushoutI.centralizer_of_eq_map_of_isTISubgroup`: the centralizer of a nontrivial factor
  element in an amalgam whose edge groups are malnormal in the other factors.

## Implementation notes

The proof uses normal forms rather than the Bass–Serre tree. Write an element `y` commuting with
`x` as `y⁻¹ = a * w` with `a ∈ G i` and `w` the product of a reduced word not starting in `G i`
(`Monoid.PushoutI.exists_eq_of_mul_list_prod`). If `w` is nontrivial, then `x` is the conjugate
`w⁻¹ * x' * w` of `x' = a⁻¹ * x * a`. When `x'` is outside the amalgamated subgroup this conjugate
is a reduced word of length at least three; when `x'` lies in it, malnormality turns the first
letter `k ∈ G j` of `w` into the letter `k⁻¹ * x' * k` outside the amalgamated subgroup, and the
conjugate is a reduced word that is either of length at least three or a single letter of `G j`.
By the normal form theorem neither lies in `G i`: a conjugate of length at least three lies in no
factor (`Monoid.PushoutI.list_prod_inv_mul_of_mul_list_prod_notMem_range_of`), and `G i` meets
`G j` only in the amalgamated subgroup.

## References

* J.-P. Serre, *Trees*, Springer (1980), Chapter I, §1.2, Theorem 1 (the normal form theorem for
  amalgamated products) and §4 (the tree of an amalgam).
* R. C. Lyndon, P. E. Schupp, *Combinatorial Group Theory*, Springer (1977), Chapter IV, §2
  (free products with amalgamation).
-/

public section

namespace Monoid.PushoutI

open Function Subgroup

variable {ι : Type*} {G : ι → Type*} [∀ i, Group (G i)] {H : Type*} [Group H]
  {φ : ∀ i, H →* G i}

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
nontrivial element `x` of `G i` is the image of its centralizer in `G i`. -/
theorem centralizer_of_eq_map_of_isTISubgroup (hφ : ∀ j, Injective (φ j)) {i : ι}
    (hH : ∀ j, j ≠ i → TauCeti.IsTISubgroup (φ j).range) {x : G i} (hx : x ≠ 1) :
    centralizer {(of i x : PushoutI φ)} = (centralizer {x}).map (of i) := by
  refine le_antisymm (fun y hy => ?_) ?_
  · -- Write `y⁻¹ = a * w`, with `a ∈ G i` and `w` a reduced word not starting in `G i`; then `w`
    -- conjugates `a⁻¹ * x * a` to `x`, which forces `w = 1`.
    obtain ⟨a, L, hc, hred, hhead, hya⟩ := exists_eq_of_mul_list_prod i y⁻¹
    have hconj : (L.map fun l => of (φ := φ) l.1 l.2).prod⁻¹ * of i (a⁻¹ * x * a) *
        (L.map fun l => of l.1 l.2).prod = of i x := by
      have h := mem_centralizer_singleton_iff.1 (inv_mem hy)
      rw [hya] at h
      simp only [map_mul, map_inv, mul_assoc] at h ⊢
      rw [← h]
      group
    have hx' : a⁻¹ * x * a ≠ 1 := by simpa [mul_assoc, inv_mul_eq_one] using hx
    rcases eq_or_ne L [] with rfl | hL
    · simp only [List.map_nil, List.prod_nil, inv_one, one_mul, mul_one] at hconj
      refine ⟨a⁻¹, mem_centralizer_singleton_iff.2 ?_, ?_⟩
      · rw [Commute, SemiconjBy]
        conv_rhs => rw [← of_injective hφ i hconj]
        group
      · rw [map_inv, ← inv_inv y, hya]
        simp
    exfalso
    by_cases hxr : a⁻¹ * x * a ∈ (φ i).range
    · obtain ⟨h, hh⟩ := hxr
      refine list_prod_inv_mul_base_mul_list_prod_notMem_range hφ hH hL hc hred hhead (h := h)
        (fun h1 => hx' (by rw [← hh, h1, map_one])) ⟨x, ?_⟩
      rw [← of_apply_eq_base φ i, hh, hconj]
    · exact list_prod_inv_mul_of_mul_list_prod_notMem_range_of hφ hL hc hred hxr hhead
        ⟨x, hconj.symm⟩
  · simpa using map_centralizer_le_centralizer_image {x} (of (φ := φ) i)

/-! ### Examples -/

/-- In the double `G ∗_{C_G(u)} G` of a CSA group along the centralizer of `u`, the centralizer of
a nontrivial element of the first copy of `G` is its centralizer in `G`. -/
example {K : Type*} [Group K] (hK : Group.IsCSA K) (u : K) {x : K} (hx : x ≠ 1) :
    centralizer {(of false x : PushoutI fun _ : Bool => (centralizer {u}).subtype)} =
      (centralizer {x}).map (of (φ := fun _ : Bool => (centralizer {u}).subtype) false) :=
  centralizer_of_eq_map_of_isTISubgroup (fun _ => Subtype.val_injective)
    (fun _ _ => by simpa using hK.centralizer_isTISubgroup u) hx

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
    exact ((Commute.all _ _).map (of true)).eq
  · obtain ⟨h, hh⟩ : of (φ := φ₂) true (.ofAdd 1) ∈ (base φ₂).range := by
      rw [← inf_of_range_eq_base_range hφ (by simp : true ≠ false)]
      exact ⟨⟨_, rfl⟩, hy⟩
    rw [← of_apply_eq_base φ₂ true] at hh
    have := congrArg (fun z : Multiplicative ℤ => z.toAdd) (of_injective hφ true hh)
    simp [φ₂] at this
    omega

end Monoid.PushoutI
