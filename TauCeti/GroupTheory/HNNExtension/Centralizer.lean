/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.HNNExtension.NormalForm

/-!
# Centralizers of base elements in an HNN extension

Let `HNNExtension B A A' φ` be the HNN extension of a group `B` along an isomorphism
`φ : A ≃* A'` of subgroups, with stable letter `t`, so that `t * a * t⁻¹ = φ a` for `a ∈ A`.
Suppose that `A` and `A'` are malnormal in `B` and that no nontrivial element of `A'` is conjugate
in `B` into `A`. Then a nontrivial element `x` of `B` commutes, in the HNN extension, only with
elements of `B`: its centralizer is the image of its centralizer in `B`
(`HNNExtension.centralizer_of_eq_map`).

In the Bass–Serre tree, `x` fixes the vertex of `B`, and by the two conditions it fixes at most
one edge there: two fixed edges at a vertex would conjugate a nontrivial element of `A'` into `A`,
or a nontrivial element of `A` or of `A'` back into the same subgroup by an element outside it. At
the other end of a fixed edge `x` acts as a nontrivial element of `A` or of `A'`, which for the
same reason fixes no further edge. So the fixed subtree of `x` is either the vertex of `B` or a
single edge at it. An element commuting with `x` preserves this subtree, and since the HNN
extension acts on its tree without inversions, it fixes the vertex of `B`.

Both conditions are needed. For `A = A' = B` and `φ` the identity, both malnormal, the stable
letter commutes with every element of `B`. For `A = ⟨a⟩` and `A' = ⟨b a b⁻¹⟩` in the free group
`B = F(a, b)`, with `φ` the conjugation by `b`, the element `b⁻¹ * t` commutes with `a`. For
`B = ⟨a, r | [a, r] = 1⟩ ∗ ⟨e⟩`, `A = ⟨a⟩` (not malnormal), `A' = ⟨e⟩` and `φ a = e`, the element
`t * r * t⁻¹` commutes with `e`.

## Main results

* `HNNExtension.centralizer_of_eq_map`: the centralizer of a nontrivial base element, when the
  associated subgroups are malnormal and no nontrivial element of one is conjugate into the
  other.

## Implementation notes

The proof uses Britton's lemma in the form of `HNNExtension.head_inv_mul_mul_head_mem_toSubgroup`
(from Mathlib's `HNNExtension.ReducedWord.map_fst_eq_and_of_prod_eq`): if `w = h * t ^ u * ⋯` is
the product of a reduced word and `w⁻¹ * c * w ∈ B` for some `c ∈ B`, then `h⁻¹ * c * h` lies in
the associated subgroup of `t ^ (-u)`. Write an element commuting with `x` as such a product `w`,
so that `w⁻¹ * x * w = x`, and `w = h * t ^ u * z` with `z` the product of the rest of the word.
Then `h⁻¹ * x * h` lies in the associated subgroup of `t ^ (-u)`, and
`x₁ = t ^ (-u) * (h⁻¹ * x * h) * t ^ u` is a nontrivial element of the associated subgroup of
`t ^ u` (`HNNExtension.t_zpow_mul_of_mul_inv_t_zpow`) with `z⁻¹ * x₁ * z = x`. If `z = b` is a
single letter of `B`, then `x` is conjugate in `B` both to `h⁻¹ * x * h` and to `x₁`, which
contradicts the hypothesis on conjugates. Otherwise `z = b * t ^ u' * ⋯` with `t ^ u * z` reduced,
and `HNNExtension.prod_inv_mul_mul_prod_notMem_range` shows that `z⁻¹ * x₁ * z` is not in `B`.

## References

* R. C. Lyndon, P. E. Schupp, *Combinatorial Group Theory*, Springer (1977), Chapter IV, §2
  (Britton's lemma).
* J.-P. Serre, *Trees*, Springer (1980), Chapter I, §1.4 (HNN extensions) and §4 (their trees).
-/

public section

open Subgroup

namespace HNNExtension

open NormalWord

variable {B : Type*} [Group B] {A A' : Subgroup B} {φ : A ≃* A'}

/-- If `A` and `A'` are malnormal and no nontrivial element of `A'` is conjugate into `A`, a
reduced word whose product commutes with a nontrivial element `x` of the base group has no
letters. -/
private theorem toList_eq_nil_of_prod_inv_mul_mul_prod_eq (hA : TauCeti.IsTISubgroup A)
    (hA' : TauCeti.IsTISubgroup A') (hAA' : ∀ g : B, ∀ a ∈ A', g * a * g⁻¹ ∈ A → a = 1) {x : B}
    (hx : x ≠ 1) {w : ReducedWord B A A'} (hw : (w.prod φ)⁻¹ * of x * w.prod φ = of x) :
    w.toList = [] := by
  rcases hL : w.toList with _ | ⟨⟨u, b⟩, L⟩
  · rfl
  exfalso
  -- With `w = h * t ^ u * z`, `h⁻¹ * x * h` lies in the associated subgroup of `t ^ (-u)`, and
  -- `x₁ = t ^ (-u) * (h⁻¹ * x * h) * t ^ u` in that of `t ^ u`, with `z⁻¹ * x₁ * z = x`.
  have hx₀ := head_inv_mul_mul_head_mem_toSubgroup hL ⟨x, hw.symm⟩
  set x₁ : B := (toSubgroupEquiv φ (-u) ⟨_, hx₀⟩ : B)
  have hx₁ : x₁ ∈ toSubgroup A A' u := by simpa using (toSubgroupEquiv φ (-u) ⟨_, hx₀⟩).property
  have hchain := w.chain
  rw [hL, List.isChain_cons] at hchain
  let z : ReducedWord B A A' := ⟨b, L, hchain.2⟩
  have hz : (z.prod φ)⁻¹ * of x₁ * z.prod φ = of x := by
    have hwz : w.prod φ = of w.head * t ^ (u : ℤ) * z.prod φ := by
      simp [ReducedWord.prod, z, hL, mul_assoc]
    rw [hwz] at hw
    rw [← hw, ← t_zpow_mul_of_mul_inv_t_zpow]
    simp only [map_mul, map_inv, Units.val_neg]
    group
  have hx₁1 : x₁ ≠ 1 := fun h1 =>
    hx (by simpa [h1, map_eq_one_iff _ (of_injective (φ := φ))] using hz.symm)
  rcases hL' : L with _ | ⟨⟨u', b'⟩, L'⟩
  · -- `x` is conjugate in `B` both to `h⁻¹ * x * h` and to `x₁`, which is impossible.
    have hzb : z.prod φ = of b := by simp [ReducedWord.prod, z, hL']
    rw [hzb, ← map_inv, ← map_mul, ← map_mul] at hz
    refine hx₁1 (eq_one_of_mul_mul_inv_mem_toSubgroup_neg hAA' (g := w.head⁻¹ * b⁻¹) hx₁ ?_)
    rw [← of_injective φ hz] at hx₀
    simpa [mul_assoc] using hx₀
  · exact prod_inv_mul_mul_prod_notMem_range hA hA' hAA' hx₁ hx₁1 (w := z) hL'
      (fun hb => hchain.1 (u', b') (by simp [hL']) hb) ⟨x, hz.symm⟩

variable (φ) in
/-- **Centralizers in an HNN extension with malnormal, non-conjugate associated subgroups.** If
`A` and `A'` are malnormal and no nontrivial element of `A'` is conjugate into `A`, the
centralizer in `HNNExtension B A A' φ` of a nontrivial element `x` of `B` is the image of its
centralizer in `B`. -/
theorem centralizer_of_eq_map (hA : TauCeti.IsTISubgroup A) (hA' : TauCeti.IsTISubgroup A')
    (hAA' : ∀ g : B, ∀ a ∈ A', g * a * g⁻¹ ∈ A → a = 1) {x : B} (hx : x ≠ 1) :
    centralizer {(of x : HNNExtension B A A' φ)} = (centralizer {x}).map of := by
  refine le_antisymm (fun y hy => ?_) ?_
  · -- Write `y` as a reduced word; it has no letters, so it is an element of `B`.
    obtain ⟨w, rfl⟩ : ∃ w : ReducedWord B A A', w.prod φ = y := by
      obtain ⟨d⟩ := TransversalPair.nonempty B A A'
      -- The inverse of `NormalWord.equiv φ d` is, by definition, the product of a normal word.
      exact ⟨(NormalWord.equiv φ d y).toReducedWord, (NormalWord.equiv φ d).symm_apply_apply y⟩
    have hw : w.prod φ = of w.head := by
      simp [ReducedWord.prod, toList_eq_nil_of_prod_inv_mul_mul_prod_eq hA hA' hAA' hx (w := w)
        (by rw [mul_assoc, ← mem_centralizer_singleton_iff.1 hy, inv_mul_cancel_left])]
    refine ⟨w.head, mem_centralizer_singleton_iff.2 (of_injective φ ?_), hw.symm⟩
    simpa [hw] using (mem_centralizer_singleton_iff.1 hy).eq
  · simpa using map_centralizer_le_centralizer_image {x} (of : B →* HNNExtension B A A' φ)

/-! ### Examples -/

/-- With trivial associated subgroups the HNN extension is the free product `B ∗ ⟨t⟩`, and a
nontrivial element of `B` has the same centralizer there as in `B`. -/
example {x : B} (hx : x ≠ 1) :
    centralizer {(of x : HNNExtension B ⊥ ⊥ (.refl _))} = (centralizer {x}).map of :=
  centralizer_of_eq_map _ .bot .bot (fun _ _ ha _ => by simpa using ha) hx

/-- The hypothesis on conjugates cannot be dropped: for `A = A' = B` and the identity of `B`, both
malnormal, the stable letter commutes with every element of `B` but does not lie in `B`. -/
example (x : B) : ∃ y ∈ centralizer {(of x : HNNExtension B ⊤ ⊤ (.refl _))},
    y ∉ (of : B →* HNNExtension B ⊤ ⊤ (.refl _)).range := by
  refine ⟨t, mem_centralizer_singleton_iff.2 ?_, fun ⟨g, hg⟩ => ?_⟩
  · simpa [commute_iff_eq] using t_mul_of (φ := .refl (⊤ : Subgroup B)) ⟨x, mem_top x⟩
  · simpa using congrArg (lift (1 : B →* Multiplicative ℤ) (.ofAdd 1) fun _ => by simp) hg.symm

end HNNExtension
