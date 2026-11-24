/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.HNNExtension.Basic

/-!
# Centralizers of base elements in an HNN extension

Let `HNNExtension B A A' φ` be the HNN extension of a group `B` along an isomorphism
`φ : A ≃* A'` of subgroups, with stable letter `t`, so that `t * a * t⁻¹ = φ a` for `a ∈ A`.
Suppose that `A` and `A'` are malnormal in `B` and that no nontrivial element of `A'` is conjugate
in `B` into `A`. Then a nontrivial element `x` of `B` commutes, in the HNN extension, only with
elements of `B`: its centralizer is the image of its centralizer in `B`
(`HNNExtension.centralizer_of_eq_map`).

In the Bass–Serre tree, `x` fixes the vertex of `B` and at most some edges at that vertex: after
crossing an edge, `x` acts as an element of `A` or of `A'`, which by the two conditions fixes no
further edge. So the fixed subtree of `x` is a star around the vertex of `B`, and every element
commuting with `x` fixes that vertex.

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
(from Mathlib's `HNNExtension.ReducedWord.map_fst_eq_and_of_prod_eq`): a reduced word starting with
`t ^ u` conjugates an element of `B` back into `B` only if its head conjugates it into the
associated subgroup of `t ^ (-u)`. Write an element commuting with `x` as a reduced word
`h * t ^ u * b * ⋯`. Then `h⁻¹ * x * h` lies in the associated subgroup of `t ^ (-u)`, so `t ^ u`
carries it to a nontrivial element `x₁` of the associated subgroup of `t ^ u`
(`HNNExtension.exists_t_zpow_conj_eq_of`). If there is no further letter, `x` is conjugate in `B`
both to `h⁻¹ * x * h` and to `x₁`, which contradicts the hypothesis on conjugates; if the next
letter is `t ^ u'`, the same lemma puts `b⁻¹ * x₁ * b` into the associated subgroup of `t ^ (-u')`,
which contradicts malnormality when `u' = -u` (as the word is reduced, `b` is then outside the
associated subgroup of `t ^ u`) and the hypothesis on conjugates when `u' = u`.

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

/-- If no nontrivial element of `A'` is conjugate into `A`, no nontrivial element of the associated
subgroup of `t ^ u` is conjugate into that of `t ^ (-u)`. -/
private theorem eq_one_of_mul_mul_inv_mem_toSubgroup_neg
    (hAA' : ∀ g : B, ∀ a ∈ A', g * a * g⁻¹ ∈ A → a = 1) {u : ℤˣ} {a g : B}
    (ha : a ∈ toSubgroup A A' u) (hga : g * a * g⁻¹ ∈ toSubgroup A A' (-u)) : a = 1 := by
  rcases Int.units_eq_one_or u with rfl | rfl
  · exact conj_eq_one_iff.1 (hAA' g⁻¹ _ (by simpa using hga) (by simpa [mul_assoc] using ha))
  · exact hAA' g a (by simpa using ha) (by simpa using hga)

/-- If `A` and `A'` are malnormal, so is the associated subgroup of every `t ^ u`. -/
private theorem isTISubgroup_toSubgroup (hA : TauCeti.IsTISubgroup A)
    (hA' : TauCeti.IsTISubgroup A') (u : ℤˣ) : TauCeti.IsTISubgroup (toSubgroup A A' u) := by
  rcases Int.units_eq_one_or u with rfl | rfl
  exacts [hA, hA']

/-- Let `x₁` be a nontrivial element of the associated subgroup of `t ^ u`, and `z` a reduced word
starting with a letter `t ^ u'` such that `t ^ u * z` is still reduced. If `A` and `A'` are
malnormal and no nontrivial element of `A'` is conjugate into `A`, then the product of `z` does not
conjugate `x₁` into the base group. -/
private theorem prod_inv_mul_mul_prod_notMem_range (hA : TauCeti.IsTISubgroup A)
    (hA' : TauCeti.IsTISubgroup A') (hAA' : ∀ g : B, ∀ a ∈ A', g * a * g⁻¹ ∈ A → a = 1) {u : ℤˣ}
    {x₁ : B} (hx₁ : x₁ ∈ toSubgroup A A' u) (hx₁1 : x₁ ≠ 1) {z : ReducedWord B A A'} {u' : ℤˣ}
    {b : B} {L : List (ℤˣ × B)} (hz : z.toList = (u', b) :: L)
    (hred : z.head ∈ toSubgroup A A' u → u = u') :
    (z.prod φ)⁻¹ * of x₁ * z.prod φ ∉ (of : B →* HNNExtension B A A' φ).range := by
  -- The head of `z` conjugates `x₁` into the associated subgroup of `t ^ (-u')`. This contradicts
  -- the hypothesis on conjugates if `u' = u`, and malnormality if `u' = -u`, since then the head
  -- is outside the associated subgroup of `t ^ u`.
  intro hmem
  have hx₂ := head_inv_mul_mul_head_mem_toSubgroup hz hmem
  by_cases hu : u' = u
  · subst hu
    exact hx₁1 (eq_one_of_mul_mul_inv_mem_toSubgroup_neg hAA' (g := z.head⁻¹) hx₁
      (by simpa using hx₂))
  · refine hx₁1 ((isTISubgroup_toSubgroup hA hA' u).eq_one (g := z.head⁻¹)
      (by simpa using fun hb => hu (hred hb).symm) hx₁ ?_)
    rw [Int.units_ne_iff_eq_neg.1 hu, neg_neg] at hx₂
    simpa using hx₂

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
  -- The head `h` conjugates `x` into the associated subgroup of `t ^ (-u)`, and `t ^ u` carries
  -- `h⁻¹ * x * h` to an element `x₁` of the associated subgroup of `t ^ u`, which the rest `z` of
  -- the word conjugates to `x`; so `x₁` is nontrivial.
  have hx₀ := head_inv_mul_mul_head_mem_toSubgroup hL ⟨x, hw.symm⟩
  obtain ⟨x₁, hx₁, hx₁t⟩ := exists_t_zpow_conj_eq_of (φ := φ) u hx₀
  have hchain := w.chain
  rw [hL, List.isChain_cons] at hchain
  let z : ReducedWord B A A' := ⟨b, L, hchain.2⟩
  have hz : (z.prod φ)⁻¹ * of x₁ * z.prod φ = of x := by
    have hwz : w.prod φ = of w.head * t ^ (u : ℤ) * z.prod φ := by
      simp [ReducedWord.prod, z, hL, mul_assoc]
    rw [hwz] at hw
    rw [← hw, ← hx₁t]
    simp only [map_mul, map_inv]
    group
  have hx₁1 : x₁ ≠ 1 := by
    rintro rfl
    exact hx (by simpa [map_eq_one_iff _ (of_injective (φ := φ))] using hz.symm)
  rcases hL' : L with _ | ⟨⟨u', b'⟩, L'⟩
  · -- `x` is conjugate in `B` both to `h⁻¹ * x * h` and to `x₁`, which is impossible.
    have hzb : z.prod φ = of b := by simp [ReducedWord.prod, z, hL']
    rw [hzb, ← map_inv, ← map_mul, ← map_mul] at hz
    refine hx₁1 (eq_one_of_mul_mul_inv_mem_toSubgroup_neg hAA' (g := w.head⁻¹ * b⁻¹) hx₁ ?_)
    rw [← of_injective φ hz] at hx₀
    simpa [mul_assoc] using hx₀
  · exact prod_inv_mul_mul_prod_notMem_range hA hA' hAA' hx₁ hx₁1 (z := z) hL'
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
      exact ⟨(y • (NormalWord.empty : NormalWord d)).toReducedWord, by simp⟩
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
  · rw [Commute, SemiconjBy]
    simpa using t_mul_of (φ := .refl (⊤ : Subgroup B)) ⟨x, mem_top x⟩
  · simpa using congrArg (lift (1 : B →* Multiplicative ℤ) (.ofAdd 1) fun _ => by simp) hg.symm

end HNNExtension
