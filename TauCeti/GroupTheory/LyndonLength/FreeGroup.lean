/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.FreeGroup.CyclicallyReduced
public import TauCeti.GroupTheory.FreeGroup.Reduce
public import TauCeti.GroupTheory.LyndonLength.Basic

/-!
# Word length on a free group is a free regular Lyndon length function

The word length `FreeGroup.norm`, the length of the reduced word, is an integer-valued Lyndon
length function on `FreeGroup α`. It is the based length function of the action of `FreeGroup α`
on its Cayley tree, at the vertex `1`.

Its Gromov product `c(g, f)` is the length of the longest common prefix of the reduced words of
`g` and `f` (`TauCeti.LyndonLength.gromovProduct_freeGroupNorm`): the reduced word of `g⁻¹ * f` is
obtained by cancelling this common prefix. The axioms follow from this description. Common prefix
lengths are ultrametric, which gives (L3); they are integers, which gives (L4); the length of the
square of a nontrivial element exceeds its own length because its cyclically reduced core is
nonempty, which gives (L5); and the common prefix itself is a common initial segment of the
required length, which gives (L6).

## Main definitions

* `TauCeti.LyndonLength.freeGroupNorm α`: word length on `FreeGroup α` as a Lyndon length function.

## Main results

* `TauCeti.LyndonLength.gromovProduct_freeGroupNorm`: the Gromov product of word length is the
  common prefix length of reduced words.
* `TauCeti.LyndonLength.isFree_freeGroupNorm`, `TauCeti.LyndonLength.isRegular_freeGroupNorm`:
  word length is a free regular Lyndon length function.

## References

* R. C. Lyndon, *Length functions in groups*, Math. Scand. 12 (1963), 209–234.
* O. Kharlampovich, A. Myasnikov, V. Remeslennikov, D. Serbin, *Groups with free regular length
  functions in `ℤⁿ`*, Trans. Amer. Math. Soc. 364 (2012), 2847–2882, §2.2, Example 1.
-/

public section

namespace TauCeti.LyndonLength

open FreeGroup

variable (α : Type*) [DecidableEq α]

/-- Word length on the free group `FreeGroup α`, Mathlib's `FreeGroup.norm`, as an integer-valued
Lyndon length function. -/
def freeGroupNorm : LyndonLength (FreeGroup α) ℤ where
  toFun g := g.norm
  map_one' := by simp
  map_inv' g := by simp [norm_inv_eq]
  eq_of_lt' g f h := by
    -- Twice the Gromov products are twice the common prefix lengths, which are ultrametric.
    have hgf := norm_inv_mul_add_two_mul_commonPrefixLength g f
    have hgh := norm_inv_mul_add_two_mul_commonPrefixLength g h
    have hfh := norm_inv_mul_add_two_mul_commonPrefixLength f h
    have h₁ := List.min_commonPrefixLength_le f.toWord g.toWord h.toWord
    have h₂ := List.min_commonPrefixLength_le g.toWord f.toWord h.toWord
    have hcomm := List.commonPrefixLength_comm f.toWord g.toWord
    omega

variable {α}

@[simp]
theorem freeGroupNorm_apply (g : FreeGroup α) : freeGroupNorm α g = g.norm :=
  (rfl)

/-- The Gromov product of word length on a free group is the length of the longest common prefix
of the reduced words. -/
@[simp]
theorem gromovProduct_freeGroupNorm (g f : FreeGroup α) :
    (freeGroupNorm α).gromovProduct g f =
      DivisibleHull.coe (List.commonPrefixLength g.toWord f.toWord : ℤ) := by
  rw [eq_comm, coe_eq_gromovProduct_iff]
  have := norm_inv_mul_add_two_mul_commonPrefixLength g f
  simp only [freeGroupNorm_apply, nsmul_eq_mul]
  push_cast
  omega

/-- Word length on a free group is a free Lyndon length function. -/
theorem isFree_freeGroupNorm : (freeGroupNorm α).IsFree where
  exists_coe_eq_gromovProduct g f := ⟨_, (gromovProduct_freeGroupNorm g f).symm⟩
  lt_map_sq g hg := by
    have h₁ := norm_pow_eq g (n := 1) one_pos
    have h₂ := norm_pow_eq g (n := 2) two_pos
    have hpos := length_reduceCyclically_toWord_pos_iff.2 hg
    rw [pow_one] at h₁
    simp only [freeGroupNorm_apply]
    omega

/-- Word length on a free group is a regular Lyndon length function: the longest common prefix
of the reduced words of `g` and `f` is a common initial segment of length `c(g, f)`. -/
theorem isRegular_freeGroupNorm : (freeGroupNorm α).IsRegular := by
  refine (isRegular_iff _).2 fun g f => ?_
  set k := List.commonPrefixLength g.toWord f.toWord with hk
  have hnorm {w : List (α × Bool)} (hw : w <:+: g.toWord ∨ w <:+: f.toWord) :
      norm (FreeGroup.mk w) = w.length := by
    rw [norm, toWord_mk, (hw.elim isReduced_toWord.infix isReduced_toWord.infix).reduce_eq]
  have hgk : k ≤ g.toWord.length := List.commonPrefixLength_le_length_left _ _
  have hfk : k ≤ f.toWord.length := List.commonPrefixLength_le_length_right _ _
  have htake : g.toWord.take k = f.toWord.take k := List.take_commonPrefixLength_eq _ _
  refine ⟨FreeGroup.mk (g.toWord.take k), FreeGroup.mk (g.toWord.drop k),
    FreeGroup.mk (f.toWord.drop k), ?_, ?_, ?_, ?_, ?_⟩
  · rw [mul_mk, List.take_append_drop, mk_toWord]
  · rw [htake, mul_mk, List.take_append_drop, mk_toWord]
  · simp only [freeGroupNorm_apply]
    rw [hnorm (.inl (List.take_prefix _ _).isInfix), hnorm (.inl (List.drop_suffix _ _).isInfix),
      List.length_take, List.length_drop, norm]
    omega
  · simp only [freeGroupNorm_apply]
    rw [htake, hnorm (.inr (List.take_prefix _ _).isInfix),
      hnorm (.inr (List.drop_suffix _ _).isInfix), List.length_take, List.length_drop, norm]
    omega
  · rw [gromovProduct_freeGroupNorm, freeGroupNorm_apply,
      hnorm (.inl (List.take_prefix _ _).isInfix), List.length_take, ← hk, min_eq_left hgk]

end TauCeti.LyndonLength
