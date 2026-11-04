/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.HNNExtension
public import TauCeti.GroupTheory.CSA

/-!
# Conjugating the base group by the stable letter of an HNN extension

Let `HNNExtension G A B φ` be the HNN extension of `G` along an isomorphism `φ : A ≃* B` of
subgroups, with stable letter `t`, so that `t * a * t⁻¹ = φ a` for `a ∈ A`. Britton's lemma
(`HNNExtension.ReducedWord.toList_eq_nil_of_mem_of_range`) shows that these are the only elements
of `G` that `t` conjugates back into `G`: `t * g * t⁻¹` lies in `G` exactly when `g ∈ A`, and
`t⁻¹ * g * t` lies in `G` exactly when `g ∈ B`. Consequently `g ∈ G` commutes with `t` exactly when
`g ∈ A` and `φ g = g`; for the HNN extension along the identity of `A`, exactly when `g ∈ A`.

This controls commutation transitivity in an HNN extension along the identity of `A`. If `c ∈ A`
is nontrivial then `t` commutes with `c`, so if commutation is transitive through `c` then every
element of `G` commuting with `c` commutes with `t` and therefore lies in `A`. Extensions of
centralizers `⟨G, t | [c, t] = 1, c ∈ C_G(u)⟩` therefore have to use the full centralizer
`C_G(u)`: for `u ≠ 1`, replacing it by a smaller subgroup `A ∋ u` with `C_G(u) ⊄ A` produces a
group that is not commutative transitive, hence not CSA.

## Main results

* `HNNExtension.t_mul_of_mul_inv_t_mem_range_iff`: `t * g * t⁻¹ ∈ G ↔ g ∈ A`.
* `HNNExtension.inv_t_mul_of_mul_t_mem_range_iff`: `t⁻¹ * g * t ∈ G ↔ g ∈ B`.
* `HNNExtension.commute_of_t_iff`: `g` commutes with `t` iff `g ∈ A` and `φ g = g`.
* `HNNExtension.commute_of_t_iff_mem`: along the identity of `A`, `g` commutes with `t` iff
  `g ∈ A`.
* `HNNExtension.centralizer_le_of_isCommTransitive`: if the HNN extension along the identity of
  `A` is commutative transitive, then `A` contains the centralizer in `G` of each of its
  nontrivial elements.

## References

* R. C. Lyndon, P. E. Schupp, *Combinatorial Group Theory*, Springer (1977), Chapter IV, §2
  (Britton's lemma).
* O. Kharlampovich, A. Myasnikov, *Irreducible affine varieties over a free group. I*,
  J. Algebra 200 (1998), §1, Definition 5 (free extensions of centralizers).
-/

public section

open Subgroup

namespace HNNExtension

variable {G : Type*} [Group G] {A B : Subgroup G} {φ : A ≃* B}

/-- The stable letter conjugates `g` into the base group exactly when `g ∈ A`. -/
theorem t_mul_of_mul_inv_t_mem_range_iff {g : G} :
    t * of g * t⁻¹ ∈ (of : G →* HNNExtension G A B φ).range ↔ g ∈ A := by
  refine ⟨fun h => ?_, fun hg => ⟨φ ⟨g, hg⟩, ?_⟩⟩
  · by_contra hg
    -- The word `t * g * t⁻¹` is reduced, so Britton's lemma rules out its lying in `G`.
    let w : NormalWord.ReducedWord G A B :=
      { head := 1
        toList := [(1, g), (-1, 1)]
        chain := by simp [hg] }
    have hw : w.prod φ = t * of g * t⁻¹ := by
      simp [w, NormalWord.ReducedWord.prod, mul_assoc]
    have := ReducedWord.toList_eq_nil_of_mem_of_range φ w (hw ▸ h)
    simp [w] at this
  · exact equiv_eq_conj (φ := φ) ⟨g, hg⟩

/-- The inverse of the stable letter conjugates `g` into the base group exactly when `g ∈ B`. -/
theorem inv_t_mul_of_mul_t_mem_range_iff {g : G} :
    t⁻¹ * of g * t ∈ (of : G →* HNNExtension G A B φ).range ↔ g ∈ B := by
  refine ⟨fun h => ?_, fun hg => ⟨φ.symm ⟨g, hg⟩, ?_⟩⟩
  · by_contra hg
    -- The word `t⁻¹ * g * t` is reduced, so Britton's lemma rules out its lying in `G`.
    let w : NormalWord.ReducedWord G A B :=
      { head := 1
        toList := [(-1, g), (1, 1)]
        chain := by simp [hg] }
    have hw : w.prod φ = t⁻¹ * of g * t := by
      simp [w, NormalWord.ReducedWord.prod, mul_assoc]
    have := ReducedWord.toList_eq_nil_of_mem_of_range φ w (hw ▸ h)
    simp [w] at this
  · exact equiv_symm_eq_conj (φ := φ) ⟨g, hg⟩

/-- An element of the base group commutes with the stable letter exactly when it lies in `A`
and is fixed by `φ`. -/
theorem commute_of_t_iff {g : G} :
    Commute (of g : HNNExtension G A B φ) t ↔ ∃ hg : g ∈ A, (φ ⟨g, hg⟩ : G) = g := by
  have key : Commute (of g : HNNExtension G A B φ) t ↔
      (t * of g * t⁻¹ : HNNExtension G A B φ) = of g := by
    rw [mul_inv_eq_iff_eq_mul, commute_iff_eq, eq_comm]
  rw [key]
  constructor
  · intro h
    have hg : g ∈ A := t_mul_of_mul_inv_t_mem_range_iff.1 ⟨g, h.symm⟩
    refine ⟨hg, of_injective (φ := φ) ?_⟩
    rw [equiv_eq_conj (φ := φ) ⟨g, hg⟩, h]
  · rintro ⟨hg, hφ⟩
    rw [← equiv_eq_conj (φ := φ) ⟨g, hg⟩, hφ]

/-- In the HNN extension along the identity of `A`, an element of the base group commutes with
the stable letter exactly when it lies in `A`. -/
@[simp]
theorem commute_of_t_iff_mem {g : G} :
    Commute (of g : HNNExtension G A A (MulEquiv.refl A)) t ↔ g ∈ A := by
  simp [commute_of_t_iff]

/-- If the HNN extension along the identity of `A` is commutative transitive, then `A` contains
the centralizer in `G` of each of its nontrivial elements. -/
theorem centralizer_le_of_isCommTransitive
    (h : Group.IsCommTransitive (HNNExtension G A A (MulEquiv.refl A))) {c : G} (hcA : c ∈ A)
    (hc : c ≠ 1) : centralizer {c} ≤ A := by
  intro x hx
  rw [← commute_of_t_iff_mem]
  -- `of x` commutes with `of c ≠ 1`, which commutes with `t`.
  refine (Group.isCommTransitive_iff _).1 h _ (of c) _ ?_ ?_ (commute_of_t_iff_mem.2 hcA)
  · rwa [Ne, map_eq_one_iff _ (of_injective (φ := MulEquiv.refl A))]
  · exact ((commute_iff_eq x c).2 (mem_centralizer_singleton_iff.1 hx)).map of

end HNNExtension
