/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Coxeter.Bruhat

/-!
# The longest element reverses the Bruhat order

Let `cs : CoxeterSystem M W` be a Coxeter system. An element `w₀` is a **longest element**
(`CoxeterSystem.IsLongest`) when `ℓ (u * w₀) + ℓ u = ℓ w₀` for every `u : W`. This is the length
identity of the longest element of a finite Coxeter group, such as the longest element of a finite
Weyl group. It forces `w₀` to be an involution of maximal length with every simple reflection as a
left and right descent, and it determines `w₀`. Conversely, an element of maximal length is a
longest element (`CoxeterSystem.isLongest_iff_forall_length_le`). The same holds inside a standard
parabolic subgroup `W_J`: lengths complement in an element `w₀J` of maximal length of `W_J`
(`CoxeterSystem.length_mul_add_length_of_forall_length_le`).

The main point is that multiplication by `w₀` **reverses the Bruhat order**: an edge `u → t * u` of
the Bruhat graph becomes the edge `t * u * w₀ → u * w₀`, since lengths are complemented in `ℓ w₀`.
So `v * w₀ ≤ u * w₀` exactly when `u ≤ v`, and likewise on the left. In particular `w₀` is the
greatest element.

The same holds on parabolic quotients. Let `J` and `K` be sets of simple indices whose standard
parabolic subgroups are exchanged by conjugation with `w₀`, that is `w₀ W_J w₀ = W_K`. Then the
map `u W_J ↦ u w₀ W_K` is a bijection from `W / W_J` to `W / W_K`, its own inverse up to
exchanging `J` and `K`. On minimal coset representatives it sends `u` to
`CoxeterSystem.minimalCosetRep K (u * w₀)`, and it reverses the Bruhat orders of the two quotients.
Hence it carries covers to covers in the opposite direction, and a saturated chain
`x₀ ⋗ x₁ ⋗ ⋯ ⋗ x_l` of `W / W_J` to the saturated chain `x_l w₀ ⋗ ⋯ ⋗ x₀ w₀` of `W / W_K`
(`CoxeterSystem.MinimalCosetRepChain.reverseMul`).

For a dominant weight `λ` of a finite root datum, `w₀` conjugates the stabilizer of `λ` to the
stabilizer of the dominant weight `-w₀ λ`. This reversal of saturated chains of `W / W_λ` is then
the order-theoretic part of Littelmann's duality `π ↦ π^*` on Lakshmibai–Seshadri paths, which
reverses a path and sends paths of shape `λ` to paths of shape `-w₀ λ`.

Left multiplication by `w₀` also acts on `W / W_J`, now with no condition on `J`. If `w₀J` has
maximal length in `W_J` and `u` is a minimal coset representative of `W / W_J`, the minimal coset
representative of `w₀ u W_J` is `w₀ * u * w₀J`, of length `ℓ w₀ - ℓ u - ℓ w₀J`
(`CoxeterSystem.IsLongest.minimalCosetRep_mul_left`). Read on the right cosets
`W_J w` by inversion, this is the **Kostant involution** `w ↦ w₀J * w * w₀` of the minimal
representatives of the cosets in `W_J \ W` (`CoxeterSystem.IsLongest.kostantInvolution`). For the
Weyl group `W` of a split reductive group `G` and the Weyl group `W_J` of the Levi subgroup of a
standard parabolic subgroup `P`, these minimal representatives are Kostant's representatives, and
`ℓ w₀ - ℓ w₀J` is the number of positive roots outside the Levi subgroup, the dimension of `G / P`.

## Main definitions

* `CoxeterSystem.IsLongest`: the length identity `ℓ (u * w₀) + ℓ u = ℓ w₀` of a longest element.
* `CoxeterSystem.MinimalCosetRepChain.reverseMul`: the reversal of a saturated chain of `W / W_J`
  by right multiplication with a longest element, a saturated chain of `W / W_K`.
* `CoxeterSystem.IsLongest.kostantInvolution`: the involution `w ↦ w₀J * w * w₀` of the minimal
  representatives of the right cosets `W_J w`.

## Main results

* `CoxeterSystem.IsLongest.mul_self`, `CoxeterSystem.IsLongest.length_le` and
  `CoxeterSystem.IsLongest.unique`: a longest element is an involution of maximal length, and there
  is at most one.
* `CoxeterSystem.isLongest_iff_forall_length_le`: **the longest element is the element of maximal
  length**.
* `CoxeterSystem.length_mul_add_length_of_forall_length_le` and
  `CoxeterSystem.length_mul_left_add_length_of_forall_length_le`: lengths complement in an element
  of maximal length of a standard parabolic subgroup.
* `CoxeterSystem.IsLongest.bruhatLE_mul_iff` and `CoxeterSystem.IsLongest.bruhatLE_mul_left_iff`:
  **multiplication by `w₀` reverses the Bruhat order**.
* `CoxeterSystem.IsLongest.bruhatLE`: every element lies below `w₀`.
* `CoxeterSystem.IsLongest.minimalCosetRep_mul_minimalCosetRep_mul`: `u W_J ↦ u w₀ W_K` is an
  involution on minimal coset representatives, up to exchanging `J` and `K`.
* `CoxeterSystem.IsLongest.bruhatLE_minimalCosetRep_mul_iff`: **it reverses the Bruhat orders of
  the parabolic quotients**.
* `CoxeterSystem.IsLongest.minimalCosetRepCovBy_minimalCosetRep_mul_iff`: it reverses covers.
* `CoxeterSystem.MinimalCosetRepChain.head_reverseMul`,
  `CoxeterSystem.MinimalCosetRepChain.last_reverseMul` and
  `CoxeterSystem.MinimalCosetRepChain.reverseMul_reverseMul`: the reversed chain runs between the
  images of the ends of the chain, and reversing twice returns the chain.
* `CoxeterSystem.IsLongest.minimalCosetRep_mul_left`: for a minimal coset representative `u` of
  `W / W_J`, the minimal coset representative of `w₀ * u` is `w₀ * u * w₀J`.
* `CoxeterSystem.IsLongest.kostantInvolution_involutive` and
  `CoxeterSystem.IsLongest.length_kostantInvolution`: **the Kostant involution is an involution and
  complements lengths**, `ℓ (w₀J * w * w₀) + ℓ w + ℓ w₀J = ℓ w₀`.

## References

* A. Björner and F. Brenti, *Combinatorics of Coxeter Groups*, Springer GTM 231 (2005),
  Sections 2.3 (properties of the longest element) and 2.5.
* P. Littelmann, *Paths and root operators in representation theory*, Ann. of Math. 142 (1995),
  499--525 (the dual path `π^*`).
* G. Boxer and V. Pilloni, *Higher Hida theory for Siegel modular forms*, §1.4 (the involution
  `w ↦ w₀,M w w₀,G` of Kostant representatives).
-/

public section

namespace CoxeterSystem

variable {B W : Type*} [Group W] {M : CoxeterMatrix B} (cs : CoxeterSystem M W) {u v w₀ : W}

local prefix:100 "ℓ " => cs.length
local prefix:100 "s " => cs.simple
local prefix:100 "π " => cs.wordProd

/-- `w₀` is a **longest element** of the Coxeter system when `ℓ (u * w₀) + ℓ u = ℓ w₀` for every
`u : W`: right multiplication by `w₀` complements lengths in `ℓ w₀`. The longest element of a
finite Coxeter group has this property; it implies that `w₀` has maximal length
(`CoxeterSystem.IsLongest.length_le`) and determines `w₀` (`CoxeterSystem.IsLongest.unique`). -/
def IsLongest (w₀ : W) : Prop := ∀ u, ℓ (u * w₀) + ℓ u = ℓ w₀

/-- The defining length identity of a longest element. -/
theorem isLongest_iff : cs.IsLongest w₀ ↔ ∀ u, ℓ (u * w₀) + ℓ u = ℓ w₀ :=
  Iff.rfl

/-! ### Elements of maximal length -/

section MaximalLength

variable {J : Set B}

/-- Let `w₀` have maximal length in `cs.parabolic J`, and let `u ∈ cs.parabolic J` be a prefix of
`w₀`, in the sense that `ℓ (u⁻¹ * w₀) + ℓ u = ℓ w₀`. If `j ∈ J` is not a right descent of `u`, then
it is a left descent of `u⁻¹ * w₀`. -/
private theorem isLeftDescent_inv_mul_of_forall_length_le (hw₀ : w₀ ∈ cs.parabolic J)
    (h : ∀ v ∈ cs.parabolic J, ℓ v ≤ ℓ w₀) (hu : u ∈ cs.parabolic J)
    (hadd : ℓ (u⁻¹ * w₀) + ℓ u = ℓ w₀) {j : B} (hj : j ∈ J) (hnd : ¬ cs.IsRightDescent u j) :
    cs.IsLeftDescent (u⁻¹ * w₀) j := by
  -- The reflection `t = u * s j * u⁻¹` lies in `cs.parabolic J`, so it shortens `w₀`.
  have ht : cs.IsReflection (u * s j * u⁻¹) := (cs.isReflection_simple j).conj u
  have htw : u * s j * u⁻¹ * w₀ ∈ cs.parabolic J :=
    mul_mem (mul_mem (mul_mem hu (cs.simple_mem_parabolic hj)) (inv_mem hu)) hw₀
  obtain ⟨α, hα, rfl⟩ := cs.exists_isReduced u
  obtain ⟨ξ, hξ, hξx⟩ := cs.exists_isReduced ((π α)⁻¹ * w₀)
  have hw : w₀ = π (α ++ ξ) := by rw [cs.wordProd_append, ← hξx, mul_inv_cancel_left]
  have hinv : cs.IsLeftInversion (π (α ++ ξ)) (π α * s j * (π α)⁻¹) := by
    rw [← hw]
    exact ⟨ht, lt_of_le_of_ne (h _ htw) (ht.length_mul_right_ne w₀)⟩
  -- By the strong exchange condition, `t * w₀` deletes one letter of `α ++ ξ`.
  obtain ⟨k, hk, hke⟩ := cs.strongExchange hinv
  rw [List.length_append] at hk
  rcases Nat.lt_or_ge k α.length with hkα | hkα
  · -- A letter of `α`: then `π α * s j = t * π α` is shorter than `π α`, against `hnd`.
    rw [List.eraseIdx_append_of_lt_length hkα, cs.wordProd_append, cs.wordProd_append,
      ← mul_assoc] at hke
    have hαj : π α * s j = π (α.eraseIdx k) := by
      simpa only [inv_mul_cancel_right] using mul_right_cancel hke
    refine absurd ?_ hnd
    rw [IsRightDescent, hαj, hα.eq]
    have := cs.length_wordProd_le (α.eraseIdx k)
    have := List.length_eraseIdx_add_one hkα
    omega
  · -- A letter of `ξ`: then `s j * π ξ` is shorter than `π ξ = u⁻¹ * w₀`.
    rw [List.eraseIdx_append_of_length_le hkα, cs.wordProd_append, cs.wordProd_append] at hke
    have hjξ : s j * π ξ = π (ξ.eraseIdx (k - α.length)) := by
      refine mul_left_cancel (a := π α) ?_
      rw [← hke]
      simp only [mul_assoc, inv_mul_cancel_left]
    rw [hξx, IsLeftDescent, hjξ, hξ.eq]
    have := cs.length_wordProd_le (ξ.eraseIdx (k - α.length))
    have := List.length_eraseIdx_add_one (show k - α.length < ξ.length by omega)
    omega

/-- Every element of `cs.parabolic J` is a prefix of an element `w₀` of maximal length in
`cs.parabolic J`. The proof is by induction on length, through the strong exchange condition: a
reflection of `W_J` cannot lengthen `w₀`. -/
private theorem length_inv_mul_add_length_of_forall_length_le (hw₀ : w₀ ∈ cs.parabolic J)
    (h : ∀ v ∈ cs.parabolic J, ℓ v ≤ ℓ w₀) (n : ℕ) :
    ∀ u ∈ cs.parabolic J, ℓ u = n → ℓ (u⁻¹ * w₀) + ℓ u = ℓ w₀ := by
  induction n with
  | zero =>
    intro u _ hn
    simp [cs.length_eq_zero_iff.mp hn]
  | succ n ih =>
    intro u hu hn
    -- Peel off a right descent `j ∈ J` of `u`; then `j` is a left descent of `(u * s j)⁻¹ * w₀`.
    obtain ⟨j, hj, hdesc⟩ := cs.exists_rightDescent_mem_of_mem_parabolic_of_ne_one hu fun h₁ ↦ by
      simp [h₁] at hn
    have hlen := cs.isRightDescent_iff.mp hdesc
    have hu' : u * s j ∈ cs.parabolic J := mul_mem hu (cs.simple_mem_parabolic hj)
    have hIH := ih _ hu' (by omega)
    have hd := cs.isLeftDescent_iff.mp <| cs.isLeftDescent_inv_mul_of_forall_length_le hw₀ h hu'
      hIH hj (cs.isRightDescent_iff_not_isRightDescent_mul.mp hdesc)
    have hss : s j * ((u * s j)⁻¹ * w₀) = u⁻¹ * w₀ := by
      rw [mul_inv_rev, cs.inv_simple, mul_assoc, cs.simple_mul_simple_cancel_left]
    rw [hss] at hd
    omega

/-- **Lengths complement in an element of maximal length of a standard parabolic subgroup.** If
`w₀` has maximal length in `cs.parabolic J`, then `ℓ (u * w₀) + ℓ u = ℓ w₀` for every `u` in
`cs.parabolic J`. -/
theorem length_mul_add_length_of_forall_length_le (hw₀ : w₀ ∈ cs.parabolic J)
    (h : ∀ v ∈ cs.parabolic J, ℓ v ≤ ℓ w₀) (hu : u ∈ cs.parabolic J) :
    ℓ (u * w₀) + ℓ u = ℓ w₀ := by
  simpa only [inv_inv, cs.length_inv] using
    cs.length_inv_mul_add_length_of_forall_length_le hw₀ h _ u⁻¹ (inv_mem hu) rfl

/-- An element of maximal length of a standard parabolic subgroup is an involution. -/
theorem mul_self_of_forall_length_le (hw₀ : w₀ ∈ cs.parabolic J)
    (h : ∀ v ∈ cs.parabolic J, ℓ v ≤ ℓ w₀) : w₀ * w₀ = 1 :=
  cs.length_eq_zero_iff.mp <| by
    have := cs.length_mul_add_length_of_forall_length_le hw₀ h hw₀
    omega

/-- An element of maximal length of a standard parabolic subgroup is its own inverse. -/
theorem inv_eq_of_forall_length_le (hw₀ : w₀ ∈ cs.parabolic J)
    (h : ∀ v ∈ cs.parabolic J, ℓ v ≤ ℓ w₀) : w₀⁻¹ = w₀ :=
  (eq_inv_of_mul_eq_one_left (cs.mul_self_of_forall_length_le hw₀ h)).symm

theorem mul_mul_cancel_left_of_forall_length_le (hw₀ : w₀ ∈ cs.parabolic J)
    (h : ∀ v ∈ cs.parabolic J, ℓ v ≤ ℓ w₀) (u : W) : w₀ * (w₀ * u) = u := by
  rw [← mul_assoc, cs.mul_self_of_forall_length_le hw₀ h, one_mul]

/-- **Lengths complement in an element of maximal length of a standard parabolic subgroup**, for
multiplication on the left: `ℓ (w₀ * u) + ℓ u = ℓ w₀` for every `u` in `cs.parabolic J`. -/
theorem length_mul_left_add_length_of_forall_length_le (hw₀ : w₀ ∈ cs.parabolic J)
    (h : ∀ v ∈ cs.parabolic J, ℓ v ≤ ℓ w₀) (hu : u ∈ cs.parabolic J) :
    ℓ (w₀ * u) + ℓ u = ℓ w₀ := by
  rw [← cs.length_inv (w₀ * u), mul_inv_rev, cs.inv_eq_of_forall_length_le hw₀ h,
    ← cs.length_inv u]
  exact cs.length_mul_add_length_of_forall_length_le hw₀ h (inv_mem hu)

end MaximalLength

namespace IsLongest

variable {cs}

/-- Right multiplication by a longest element complements lengths. -/
theorem length_mul_add_length (h : cs.IsLongest w₀) (u : W) : ℓ (u * w₀) + ℓ u = ℓ w₀ :=
  h u

/-- **A longest element has maximal length.** -/
theorem length_le (h : cs.IsLongest w₀) (u : W) : ℓ u ≤ ℓ w₀ := by
  have := h u
  omega

/-- A longest element is an involution. -/
theorem mul_self (h : cs.IsLongest w₀) : w₀ * w₀ = 1 :=
  cs.mul_self_of_forall_length_le (J := Set.univ) (by simp [parabolic_univ])
    fun v _ ↦ h.length_le v

/-- A longest element is its own inverse. -/
theorem inv_eq (h : cs.IsLongest w₀) : w₀⁻¹ = w₀ :=
  cs.inv_eq_of_forall_length_le (J := Set.univ) (by simp [parabolic_univ])
    fun v _ ↦ h.length_le v

theorem mul_mul_cancel_left (h : cs.IsLongest w₀) (u : W) : w₀ * (w₀ * u) = u :=
  cs.mul_mul_cancel_left_of_forall_length_le (J := Set.univ) (by simp [parabolic_univ])
    (fun v _ ↦ h.length_le v) u

theorem mul_mul_cancel_right (h : cs.IsLongest w₀) (u : W) : u * w₀ * w₀ = u := by
  rw [mul_assoc, h.mul_self, mul_one]

/-- Left multiplication by a longest element also complements lengths. -/
theorem length_mul_left_add_length (h : cs.IsLongest w₀) (u : W) : ℓ (w₀ * u) + ℓ u = ℓ w₀ :=
  cs.length_mul_left_add_length_of_forall_length_le (J := Set.univ) (by simp [parabolic_univ])
    (fun v _ ↦ h.length_le v) (by simp [parabolic_univ])

/-- **There is at most one longest element.** -/
theorem unique {w₀' : W} (h : cs.IsLongest w₀) (h' : cs.IsLongest w₀') : w₀ = w₀' := by
  have h₁ := h' w₀
  have h₂ := h w₀'
  have h₃ : w₀ * w₀' = 1 := cs.length_eq_zero_iff.mp (by omega)
  rw [eq_inv_of_mul_eq_one_left h₃, h'.inv_eq]

/-- Every simple reflection is a right descent of a longest element. -/
theorem isRightDescent (h : cs.IsLongest w₀) (i : B) : cs.IsRightDescent w₀ i := by
  have := h.length_mul_left_add_length (s i)
  rw [cs.length_simple] at this
  exact cs.isRightDescent_iff.mpr this

/-- Every simple reflection is a left descent of a longest element. -/
theorem isLeftDescent (h : cs.IsLongest w₀) (i : B) : cs.IsLeftDescent w₀ i := by
  have := h (s i)
  rw [cs.length_simple] at this
  exact cs.isLeftDescent_iff.mpr this

/-! ### Reversal of the Bruhat order -/

/-- Right multiplication by a longest element reverses the edges of the Bruhat graph. -/
theorem bruhatStep_mul (h : cs.IsLongest w₀) (huv : cs.BruhatStep u v) :
    cs.BruhatStep (v * w₀) (u * w₀) := by
  obtain ⟨t, ht, rfl, hlt⟩ := cs.bruhatStep_iff.mp huv
  refine cs.bruhatStep_iff.mpr ⟨t, ht, by rw [← mul_assoc, ← mul_assoc, ht.mul_self, one_mul], ?_⟩
  have h₁ := h u
  have h₂ := h (t * u)
  omega

/-- Right multiplication by a longest element reverses the Bruhat order. -/
theorem bruhatLE_mul (h : cs.IsLongest w₀) (huv : cs.BruhatLE u v) :
    cs.BruhatLE (v * w₀) (u * w₀) := by
  rw [bruhatLE_iff_reflTransGen] at huv ⊢
  induction huv with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hs ih => exact Relation.ReflTransGen.head (h.bruhatStep_mul hs) ih

/-- **Right multiplication by a longest element reverses the Bruhat order**: `v w₀ ≤ u w₀` exactly
when `u ≤ v`. -/
theorem bruhatLE_mul_iff (h : cs.IsLongest w₀) :
    cs.BruhatLE (v * w₀) (u * w₀) ↔ cs.BruhatLE u v :=
  ⟨fun huv ↦ by simpa [h.mul_mul_cancel_right] using h.bruhatLE_mul huv, h.bruhatLE_mul⟩

/-- **Left multiplication by a longest element reverses the Bruhat order**: `w₀ v ≤ w₀ u` exactly
when `u ≤ v`. -/
theorem bruhatLE_mul_left_iff (h : cs.IsLongest w₀) :
    cs.BruhatLE (w₀ * v) (w₀ * u) ↔ cs.BruhatLE u v := by
  rw [← bruhatLE_inv_iff, mul_inv_rev, mul_inv_rev, h.inv_eq, h.bruhatLE_mul_iff,
    bruhatLE_inv_iff]

/-- **A longest element is the greatest element of the Bruhat order.** -/
theorem bruhatLE (h : cs.IsLongest w₀) (u : W) : cs.BruhatLE u w₀ := by
  rw [← h.bruhatLE_mul_iff, h.mul_self]
  exact cs.one_bruhatLE _

/-! ### Reversal of parabolic quotients -/

variable {J K : Set B}

/-- If conjugation by an involution `w₀` carries `W_J` onto `W_K`, it carries `W_K` onto `W_J`. -/
theorem conj_mem_parabolic_iff_symm (h : cs.IsLongest w₀)
    (hJK : ∀ p, w₀ * p * w₀ ∈ cs.parabolic K ↔ p ∈ cs.parabolic J) (q : W) :
    w₀ * q * w₀ ∈ cs.parabolic J ↔ q ∈ cs.parabolic K := by
  rw [← hJK, mul_assoc w₀ q w₀, h.mul_mul_cancel_left, mul_assoc, h.mul_self, mul_one]

/-- **`u W_J ↦ u w₀ W_K` is an involution**, up to exchanging `J` and `K`: on a minimal coset
representative `u` of `W / W_J`, applying it twice returns `u`. -/
theorem minimalCosetRep_mul_minimalCosetRep_mul (h : cs.IsLongest w₀)
    (hJK : ∀ p, w₀ * p * w₀ ∈ cs.parabolic K ↔ p ∈ cs.parabolic J)
    (hu : cs.IsMinimalCosetRep J u) :
    cs.minimalCosetRep J (cs.minimalCosetRep K (u * w₀) * w₀) = u := by
  refine ((cs.eq_minimalCosetRep_iff).mpr ⟨hu, ?_⟩).symm
  -- With `p = (u w₀)⁻¹ m ∈ W_K` for the representative `m`, the element is `w₀ p⁻¹ w₀ ∈ W_J`.
  have hp := (h.conj_mem_parabolic_iff_symm hJK _).mpr
    (inv_mem (cs.inv_mul_minimalCosetRep_mem K (u * w₀)))
  simpa [mul_assoc, h.inv_eq, h.mul_self] using hp

/-- **`u W_J ↦ u w₀ W_K` reverses the Bruhat orders of the parabolic quotients**: for minimal coset
representatives `u` and `v` of `W / W_J`, the representative of `v w₀ W_K` lies below that of
`u w₀ W_K` exactly when `u ≤ v`. -/
theorem bruhatLE_minimalCosetRep_mul_iff (h : cs.IsLongest w₀)
    (hJK : ∀ p, w₀ * p * w₀ ∈ cs.parabolic K ↔ p ∈ cs.parabolic J)
    (hu : cs.IsMinimalCosetRep J u) (hv : cs.IsMinimalCosetRep J v) :
    cs.BruhatLE (cs.minimalCosetRep K (v * w₀)) (cs.minimalCosetRep K (u * w₀)) ↔
      cs.BruhatLE u v := by
  refine ⟨fun huv ↦ ?_, fun huv ↦ (h.bruhatLE_mul huv).minimalCosetRep K⟩
  have := (h.bruhatLE_mul huv).minimalCosetRep J
  rwa [h.minimalCosetRep_mul_minimalCosetRep_mul hJK hu,
    h.minimalCosetRep_mul_minimalCosetRep_mul hJK hv] at this

/-- `u W_J ↦ u w₀ W_K` carries a cover `y ⋖ x` of `W / W_J` to a cover `x w₀ ⋖ y w₀` of
`W / W_K`. -/
theorem minimalCosetRepCovBy_minimalCosetRep_mul (h : cs.IsLongest w₀)
    (hJK : ∀ p, w₀ * p * w₀ ∈ cs.parabolic K ↔ p ∈ cs.parabolic J) {x y : W}
    (hyx : cs.MinimalCosetRepCovBy J y x) :
    cs.MinimalCosetRepCovBy K (cs.minimalCosetRep K (x * w₀)) (cs.minimalCosetRep K (y * w₀)) where
  isMinimalCosetRep_left := cs.isMinimalCosetRep_minimalCosetRep K _
  isMinimalCosetRep_right := cs.isMinimalCosetRep_minimalCosetRep K _
  bruhatLE := (h.bruhatLE_mul hyx.bruhatLE).minimalCosetRep K
  ne hxy := hyx.ne <| by
    rw [← h.minimalCosetRep_mul_minimalCosetRep_mul hJK hyx.isMinimalCosetRep_left,
      ← h.minimalCosetRep_mul_minimalCosetRep_mul hJK hyx.isMinimalCosetRep_right, hxy]
  eq_or_eq z hz hxz hzy := by
    -- Carry `z` back to `W / W_J`, where it lies between `y` and `x`.
    have hKJ := h.conj_mem_parabolic_iff_symm hJK
    have hz' := h.minimalCosetRep_mul_minimalCosetRep_mul hKJ hz
    have hyz := (h.bruhatLE_mul hzy).minimalCosetRep J
    have hzx := (h.bruhatLE_mul hxz).minimalCosetRep J
    rw [h.minimalCosetRep_mul_minimalCosetRep_mul hJK hyx.isMinimalCosetRep_left] at hyz
    rw [h.minimalCosetRep_mul_minimalCosetRep_mul hJK hyx.isMinimalCosetRep_right] at hzx
    rcases hyx.eq_or_eq _ (cs.isMinimalCosetRep_minimalCosetRep J _) hyz hzx with hzy' | hzx'
    · exact Or.inr (hz'.symm.trans (by rw [hzy']))
    · exact Or.inl (hz'.symm.trans (by rw [hzx']))

/-- **`u W_J ↦ u w₀ W_K` reverses covers**: for minimal coset representatives `x` and `y` of
`W / W_J`, the representative of `x w₀ W_K` is covered by that of `y w₀ W_K` exactly when `y` is
covered by `x`. -/
theorem minimalCosetRepCovBy_minimalCosetRep_mul_iff (h : cs.IsLongest w₀)
    (hJK : ∀ p, w₀ * p * w₀ ∈ cs.parabolic K ↔ p ∈ cs.parabolic J) {x y : W}
    (hx : cs.IsMinimalCosetRep J x) (hy : cs.IsMinimalCosetRep J y) :
    cs.MinimalCosetRepCovBy K (cs.minimalCosetRep K (x * w₀)) (cs.minimalCosetRep K (y * w₀)) ↔
      cs.MinimalCosetRepCovBy J y x := by
  refine ⟨fun hxy ↦ ?_, h.minimalCosetRepCovBy_minimalCosetRep_mul hJK⟩
  have := h.minimalCosetRepCovBy_minimalCosetRep_mul (h.conj_mem_parabolic_iff_symm hJK) hxy
  rwa [h.minimalCosetRep_mul_minimalCosetRep_mul hJK hx,
    h.minimalCosetRep_mul_minimalCosetRep_mul hJK hy] at this

end IsLongest

/-- **An element of maximal length is a longest element**: if no element of `W` is longer than
`w₀`, then `ℓ (u * w₀) + ℓ u = ℓ w₀` for every `u : W`. -/
theorem isLongest_of_forall_length_le (h : ∀ v, ℓ v ≤ ℓ w₀) : cs.IsLongest w₀ := fun _ ↦
  cs.length_mul_add_length_of_forall_length_le (J := Set.univ) (by simp [parabolic_univ])
    (fun v _ ↦ h v) (by simp [parabolic_univ])

/-- **The longest element is the element of maximal length.** -/
theorem isLongest_iff_forall_length_le : cs.IsLongest w₀ ↔ ∀ v, ℓ v ≤ ℓ w₀ :=
  ⟨IsLongest.length_le, cs.isLongest_of_forall_length_le⟩

/-! ### The Kostant involution -/

namespace IsLongest

variable {cs} {J : Set B} {w₀J : W}

/-- Let `w₀` be the longest element. For a minimal coset representative `u` of `W / W_J` and any
`x ∈ cs.parabolic J`, the length of `w₀ * u * x` is the complement `ℓ w₀ - ℓ u - ℓ x`. -/
theorem length_mul_mul_add_length_add_length (h : cs.IsLongest w₀) {x : W}
    (hx : x ∈ cs.parabolic J) (hu : cs.IsMinimalCosetRep J u) :
    ℓ (w₀ * u * x) + ℓ u + ℓ x = ℓ w₀ := by
  have h₁ := h.length_mul_left_add_length (u * x)
  have h₂ := cs.length_mul_of_isMinimalCosetRep hu hx
  rw [mul_assoc]
  omega

/-- Let `w₀` be the longest element and `w₀J` an element of maximal length of `cs.parabolic J`.
If `u` is a minimal coset representative of `W / W_J`, so is `w₀ * u * w₀J`. -/
theorem isMinimalCosetRep_mul_mul (h : cs.IsLongest w₀) (hJ : w₀J ∈ cs.parabolic J)
    (h₀J : ∀ v ∈ cs.parabolic J, ℓ v ≤ ℓ w₀J) (hu : cs.IsMinimalCosetRep J u) :
    cs.IsMinimalCosetRep J (w₀ * u * w₀J) := by
  refine cs.isMinimalCosetRep_iff.mpr fun i hi ↦ cs.not_isRightDescent_iff.mpr ?_
  -- Both lengths are complements in `ℓ w₀`, and `ℓ (w₀J * s i) + 1 = ℓ w₀J`.
  have hv := cs.simple_mem_parabolic hi
  have h₁ := h.length_mul_mul_add_length_add_length hJ hu
  have h₂ := h.length_mul_mul_add_length_add_length (mul_mem hJ hv) hu
  have h₅ := cs.length_mul_left_add_length_of_forall_length_le hJ h₀J hv
  rw [cs.length_simple] at h₅
  rw [← mul_assoc] at h₂
  omega

/-- **Left multiplication by the longest element on `W / W_J`.** Let `w₀` be the longest element
and `w₀J` an element of maximal length of `cs.parabolic J`. For a minimal coset representative `u`
of `W / W_J`, the minimal coset representative of `w₀ * u` is `w₀ * u * w₀J`: the longest element
of `u W_J` is `u * w₀J`, so the shortest element of `w₀ u W_J` is `w₀ * u * w₀J`. -/
theorem minimalCosetRep_mul_left (h : cs.IsLongest w₀) (hJ : w₀J ∈ cs.parabolic J)
    (h₀J : ∀ v ∈ cs.parabolic J, ℓ v ≤ ℓ w₀J) (hu : cs.IsMinimalCosetRep J u) :
    cs.minimalCosetRep J (w₀ * u) = w₀ * u * w₀J := by
  refine ((cs.eq_minimalCosetRep_iff).mpr ⟨h.isMinimalCosetRep_mul_mul hJ h₀J hu, ?_⟩).symm
  rwa [inv_mul_cancel_left]

/-- `w₀J * w * w₀` is a minimal representative of a right coset `W_J w` whenever `w` is. Minimal
representatives `w` of right cosets are spelled `cs.IsMinimalCosetRep J w⁻¹`. -/
theorem isMinimalCosetRep_inv_mul_mul (h : cs.IsLongest w₀) (hJ : w₀J ∈ cs.parabolic J)
    (h₀J : ∀ v ∈ cs.parabolic J, ℓ v ≤ ℓ w₀J) {w : W} (hw : cs.IsMinimalCosetRep J w⁻¹) :
    cs.IsMinimalCosetRep J (w₀J * w * w₀)⁻¹ := by
  rw [mul_inv_rev, mul_inv_rev, h.inv_eq, cs.inv_eq_of_forall_length_le hJ h₀J, ← mul_assoc]
  exact h.isMinimalCosetRep_mul_mul hJ h₀J hw

/-- Let `w₀` be the longest element. For a minimal representative `w` of a right coset `W_J w`
and any `x ∈ cs.parabolic J`, the length of `x * w * w₀` is the complement `ℓ w₀ - ℓ w - ℓ x`. -/
theorem length_mul_mul_add_length_add_length_of_isMinimalCosetRep_inv (h : cs.IsLongest w₀)
    {x : W} (hx : x ∈ cs.parabolic J) {w : W} (hw : cs.IsMinimalCosetRep J w⁻¹) :
    ℓ (x * w * w₀) + ℓ w + ℓ x = ℓ w₀ := by
  have hinv : (x * w * w₀)⁻¹ = w₀ * w⁻¹ * x⁻¹ := by
    rw [mul_inv_rev, mul_inv_rev, h.inv_eq, mul_assoc]
  rw [← cs.length_inv (x * w * w₀), hinv, ← cs.length_inv w, ← cs.length_inv x]
  exact h.length_mul_mul_add_length_add_length (inv_mem hx) hw

/-- The **Kostant involution** `w ↦ w₀J * w * w₀` of the minimal representatives of the right
cosets `W_J w`, for the longest element `w₀` and an element `w₀J` of maximal length of the standard
parabolic subgroup `cs.parabolic J`. Minimal representatives `w` of right cosets are spelled
`cs.IsMinimalCosetRep J w⁻¹`. It sends `ℓ w` to `ℓ w₀ - ℓ w₀J - ℓ w`
(`CoxeterSystem.IsLongest.length_kostantInvolution`). When `W` is the Weyl group of a split
reductive group `G` and `W_J` that of the Levi subgroup of a standard parabolic subgroup `P`,
`ℓ w₀ - ℓ w₀J` is the number of positive roots outside the Levi subgroup, the dimension of
`G / P`. -/
def kostantInvolution (h : cs.IsLongest w₀) (hJ : w₀J ∈ cs.parabolic J)
    (h₀J : ∀ v ∈ cs.parabolic J, ℓ v ≤ ℓ w₀J) :
    Equiv.Perm {w : W // cs.IsMinimalCosetRep J w⁻¹} :=
  Function.Involutive.toPerm
    (fun w ↦ ⟨w₀J * w.val * w₀, h.isMinimalCosetRep_inv_mul_mul hJ h₀J w.property⟩)
    fun w ↦ Subtype.ext <| by
      dsimp only
      rw [mul_assoc w₀J w.val, cs.mul_mul_cancel_left_of_forall_length_le hJ h₀J,
        h.mul_mul_cancel_right]

variable (h : cs.IsLongest w₀) (hJ : w₀J ∈ cs.parabolic J)
  (h₀J : ∀ v ∈ cs.parabolic J, ℓ v ≤ ℓ w₀J)

@[simp]
theorem coe_kostantInvolution (w : {w : W // cs.IsMinimalCosetRep J w⁻¹}) :
    (h.kostantInvolution hJ h₀J w).val = w₀J * w.val * w₀ :=
  (rfl)

/-- **The Kostant involution is an involution.** -/
theorem kostantInvolution_involutive : Function.Involutive (h.kostantInvolution hJ h₀J) :=
  Function.Involutive.toPerm_involutive _

@[simp]
theorem kostantInvolution_kostantInvolution (w : {w : W // cs.IsMinimalCosetRep J w⁻¹}) :
    h.kostantInvolution hJ h₀J (h.kostantInvolution hJ h₀J w) = w :=
  h.kostantInvolution_involutive hJ h₀J w

@[simp]
theorem kostantInvolution_symm : (h.kostantInvolution hJ h₀J).symm = h.kostantInvolution hJ h₀J :=
  Function.Involutive.toPerm_symm _

/-- **The Kostant involution complements lengths**: `ℓ (w₀J * w * w₀) + ℓ w + ℓ w₀J = ℓ w₀`. -/
theorem length_kostantInvolution (w : {w : W // cs.IsMinimalCosetRep J w⁻¹}) :
    ℓ (h.kostantInvolution hJ h₀J w).val + ℓ w.val + ℓ w₀J = ℓ w₀ :=
  h.length_mul_mul_add_length_add_length_of_isMinimalCosetRep_inv hJ w.property

end IsLongest

/-! ### Reversal of saturated chains -/

namespace MinimalCosetRepChain

variable {cs} {J K : Set B}

/-- The **reversal of a saturated chain by a longest element**. Let conjugation by a longest element
`w₀` carry `W_J` onto `W_K`. A saturated chain `x₀ ⋗ x₁ ⋗ ⋯ ⋗ x_l` of `W / W_J` is carried to the
saturated chain `x_l w₀ ⋗ ⋯ ⋗ x₁ w₀ ⋗ x₀ w₀` of `W / W_K`, each coset `x w₀ W_K` represented by its
minimal coset representative (`CoxeterSystem.IsLongest.minimalCosetRepCovBy_minimalCosetRep_mul`).
-/
noncomputable def reverseMul (h : cs.IsLongest w₀)
    (hJK : ∀ p, w₀ * p * w₀ ∈ cs.parabolic K ↔ p ∈ cs.parabolic J)
    (C : cs.MinimalCosetRepChain J) : cs.MinimalCosetRepChain K :=
  C.reverse.map
    { toFun x := ⟨cs.minimalCosetRep K (x.val * w₀), cs.isMinimalCosetRep_minimalCosetRep K _⟩
      map_rel' hxy := h.minimalCosetRepCovBy_minimalCosetRep_mul hJK (SetRel.mem_inv.mp hxy) }

variable (h : cs.IsLongest w₀) (hJK : ∀ p, w₀ * p * w₀ ∈ cs.parabolic K ↔ p ∈ cs.parabolic J)
  (C : cs.MinimalCosetRepChain J)

@[simp]
theorem length_reverseMul : (C.reverseMul h hJK).length = C.length :=
  (rfl)

@[simp]
theorem reverseMul_apply (k : Fin ((C.reverseMul h hJK).length + 1)) :
    ((C.reverseMul h hJK) k).val =
      cs.minimalCosetRep K ((C (Fin.rev ⟨k, by simpa using k.isLt⟩)).val * w₀) :=
  (rfl)

/-- The reversed chain starts at the coset of the last element of the chain, times `w₀`. -/
@[simp]
theorem head_reverseMul : (C.reverseMul h hJK).head.val = cs.minimalCosetRep K (C.last.val * w₀)
    := by
  simp [reverseMul]

/-- The reversed chain ends at the coset of the first element of the chain, times `w₀`. -/
@[simp]
theorem last_reverseMul : (C.reverseMul h hJK).last.val = cs.minimalCosetRep K (C.head.val * w₀)
    := by
  simp [reverseMul]

/-- **Reversing a saturated chain twice by a longest element returns it.** -/
@[simp]
theorem reverseMul_reverseMul :
    (C.reverseMul h hJK).reverseMul h (h.conj_mem_parabolic_iff_symm hJK) = C := by
  refine RelSeries.ext rfl (funext fun k ↦ Subtype.ext ?_)
  rw [Function.comp_apply, reverseMul_apply, reverseMul_apply]
  convert h.minimalCosetRep_mul_minimalCosetRep_mul hJK (C k).property using 6
  · exact congrArg C (Fin.ext (by simp [Fin.val_rev]; omega))
  · exact congrArg C (Fin.ext rfl)

end MinimalCosetRepChain

end CoxeterSystem
