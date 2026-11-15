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
left and right descent, and it determines `w₀`.

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

## Main definitions

* `CoxeterSystem.IsLongest`: the length identity `ℓ (u * w₀) + ℓ u = ℓ w₀` of a longest element.
* `CoxeterSystem.MinimalCosetRepChain.reverseMul`: the reversal of a saturated chain of `W / W_J`
  by right multiplication with a longest element, a saturated chain of `W / W_K`.

## Main results

* `CoxeterSystem.IsLongest.mul_self`, `CoxeterSystem.IsLongest.length_le` and
  `CoxeterSystem.IsLongest.unique`: a longest element is an involution of maximal length, and there
  is at most one.
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

## References

* A. Björner and F. Brenti, *Combinatorics of Coxeter Groups*, Springer GTM 231 (2005),
  Sections 2.3 (properties of the longest element) and 2.5.
* P. Littelmann, *Paths and root operators in representation theory*, Ann. of Math. 142 (1995),
  499--525 (the dual path `π^*`).
-/

public section

namespace CoxeterSystem

variable {B W : Type*} [Group W] {M : CoxeterMatrix B} (cs : CoxeterSystem M W) {u v w₀ : W}

local prefix:100 "ℓ " => cs.length
local prefix:100 "s " => cs.simple

/-- `w₀` is a **longest element** of the Coxeter system when `ℓ (u * w₀) + ℓ u = ℓ w₀` for every
`u : W`: right multiplication by `w₀` complements lengths in `ℓ w₀`. The longest element of a
finite Coxeter group has this property; it implies that `w₀` has maximal length
(`CoxeterSystem.IsLongest.length_le`) and determines `w₀` (`CoxeterSystem.IsLongest.unique`). -/
def IsLongest (w₀ : W) : Prop := ∀ u, ℓ (u * w₀) + ℓ u = ℓ w₀

/-- The defining length identity of a longest element. -/
theorem isLongest_iff : cs.IsLongest w₀ ↔ ∀ u, ℓ (u * w₀) + ℓ u = ℓ w₀ :=
  Iff.rfl

namespace IsLongest

variable {cs}

/-- Right multiplication by a longest element complements lengths. -/
theorem length_mul_add_length (h : cs.IsLongest w₀) (u : W) : ℓ (u * w₀) + ℓ u = ℓ w₀ :=
  h u

/-- A longest element is an involution. -/
theorem mul_self (h : cs.IsLongest w₀) : w₀ * w₀ = 1 :=
  cs.length_eq_zero_iff.mp (by have := h w₀; omega)

/-- A longest element is its own inverse. -/
theorem inv_eq (h : cs.IsLongest w₀) : w₀⁻¹ = w₀ :=
  (eq_inv_of_mul_eq_one_left h.mul_self).symm

theorem mul_mul_cancel_left (h : cs.IsLongest w₀) (u : W) : w₀ * (w₀ * u) = u := by
  rw [← mul_assoc, h.mul_self, one_mul]

theorem mul_mul_cancel_right (h : cs.IsLongest w₀) (u : W) : u * w₀ * w₀ = u := by
  rw [mul_assoc, h.mul_self, mul_one]

/-- Left multiplication by a longest element also complements lengths. -/
theorem length_mul_left_add_length (h : cs.IsLongest w₀) (u : W) : ℓ (w₀ * u) + ℓ u = ℓ w₀ := by
  rw [← cs.length_inv (w₀ * u), mul_inv_rev, h.inv_eq, ← cs.length_inv u]
  exact h u⁻¹

/-- **A longest element has maximal length.** -/
theorem length_le (h : cs.IsLongest w₀) (u : W) : ℓ u ≤ ℓ w₀ := by
  have := h u
  omega

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
    { toFun x := ⟨cs.minimalCosetRep K (x.1 * w₀), cs.isMinimalCosetRep_minimalCosetRep K _⟩
      map_rel' hxy := h.minimalCosetRepCovBy_minimalCosetRep_mul hJK (SetRel.mem_inv.mp hxy) }

variable (h : cs.IsLongest w₀) (hJK : ∀ p, w₀ * p * w₀ ∈ cs.parabolic K ↔ p ∈ cs.parabolic J)
  (C : cs.MinimalCosetRepChain J)

@[simp]
theorem length_reverseMul : (C.reverseMul h hJK).length = C.length :=
  (rfl)

@[simp]
theorem reverseMul_apply (k : Fin ((C.reverseMul h hJK).length + 1)) :
    ((C.reverseMul h hJK) k).1 =
      cs.minimalCosetRep K ((C (Fin.rev ⟨k, by simpa using k.2⟩)).1 * w₀) :=
  (rfl)

/-- The reversed chain starts at the coset of the last element of the chain, times `w₀`. -/
@[simp]
theorem head_reverseMul : (C.reverseMul h hJK).head.1 = cs.minimalCosetRep K (C.last.1 * w₀) := by
  simp [reverseMul]

/-- The reversed chain ends at the coset of the first element of the chain, times `w₀`. -/
@[simp]
theorem last_reverseMul : (C.reverseMul h hJK).last.1 = cs.minimalCosetRep K (C.head.1 * w₀) := by
  simp [reverseMul]

/-- **Reversing a saturated chain twice by a longest element returns it.** -/
@[simp]
theorem reverseMul_reverseMul :
    (C.reverseMul h hJK).reverseMul h (h.conj_mem_parabolic_iff_symm hJK) = C := by
  refine RelSeries.ext rfl (funext fun k ↦ Subtype.ext ?_)
  rw [Function.comp_apply, reverseMul_apply, reverseMul_apply]
  convert h.minimalCosetRep_mul_minimalCosetRep_mul hJK (C k).2 using 6
  · exact congrArg C (Fin.ext (by simp [Fin.val_rev]; omega))
  · exact congrArg C (Fin.ext rfl)

end MinimalCosetRepChain

end CoxeterSystem
