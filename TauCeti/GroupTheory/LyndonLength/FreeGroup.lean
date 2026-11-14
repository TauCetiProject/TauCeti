/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.FreeGroup.CyclicallyReduced
public import TauCeti.GroupTheory.FreeGroup.Reduce
public import TauCeti.GroupTheory.LyndonLength.Separated
import TauCeti.GroupTheory.FreeGroup.BigPowers

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

The restriction of word length to a subgroup `H` is again a free Lyndon length function
(`TauCeti.LyndonLength.IsFree.comap`), but it need not be regular: for finitely generated `H` it
is regular exactly when `H` has a basis `U` such that any two distinct elements of `U ∪ U⁻¹` have
different initial letters (this criterion is not proved here). For letters `b ≠ c` the subgroup
`⟨ab, ac⟩` is a counterexample, since the Gromov product of `ab` and `ac` is `1`
(`TauCeti.LyndonLength.gromovProduct_freeGroupNorm_of_mul_of_of_mul_of`) and every element of the
subgroup has even length. Together with the zero length function, which is regular and
not free on a nontrivial group, this shows that freeness and regularity are independent.

Two elements `u`, `v` of a free group that do not commute are separated for word length: the
cancellation in `uᵐ vⁿ` is the same for all large `m` and `n`. Indeed, the reduced words of `u⁻ᵐ`
and `vⁿ` begin with long prefixes of the attracting rays of `u⁻¹` and `v`, and these rays differ
within their first `‖u‖ ‖v‖` letters, `‖·‖` being word length, unless `u` and `v` commute.

## Main definitions

* `TauCeti.LyndonLength.freeGroupNorm α`: word length on `FreeGroup α` as a Lyndon length function.

## Main results

* `TauCeti.LyndonLength.gromovProduct_freeGroupNorm`: the Gromov product of word length is the
  common prefix length of reduced words.
* `TauCeti.LyndonLength.isFree_freeGroupNorm`, `TauCeti.LyndonLength.isRegular_freeGroupNorm`:
  word length is a free regular Lyndon length function.
* `TauCeti.LyndonLength.not_isRegular_comap_freeGroupNorm_subtype_closure`: the restriction of
  word length to `⟨ab, ac⟩` is not regular.
* `TauCeti.LyndonLength.isSeparated_freeGroupNorm_of_not_commute`: non-commuting elements of a free
  group are separated for word length.

## References

* R. C. Lyndon, *Length functions in groups*, Math. Scand. 12 (1963), 209–234.
* O. Kharlampovich, A. Myasnikov, V. Remeslennikov, D. Serbin, *Groups with free regular length
  functions in `ℤⁿ`*, Trans. Amer. Math. Soc. 364 (2012), 2847–2882, §2.2, Examples 1 and 2.
* A. Myasnikov, V. Remeslennikov, D. Serbin, *Regular free length functions on Lyndon's free
  `ℤ[t]`-group `F^{ℤ[t]}`*, Contemp. Math. 378 (2005), 37–77, Lemma 6.5.
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

/-! ### Restriction to a subgroup -/

/-- For letters `b ≠ c`, the Gromov product of `ab` and `ac` for word length is `1`: their reduced
words have exactly the initial letter `a` in common. -/
theorem gromovProduct_freeGroupNorm_of_mul_of_of_mul_of {a b c : α} (hbc : b ≠ c) :
    (freeGroupNorm α).gromovProduct (of a * of b) (of a * of c) = DivisibleHull.coe (1 : ℤ) := by
  simp [hbc]

/-- Regularity is not inherited by subgroups: for letters `b ≠ c`, the restriction of word length
to the subgroup `⟨ab, ac⟩` of a free group is not regular, although it is free
(`isFree_freeGroupNorm.comap (Subgroup.subtype_injective _)`). The Gromov product of `ab` and
`ac` is `1` (`gromovProduct_freeGroupNorm_of_mul_of_of_mul_of`), while every element of the
subgroup has even length. -/
theorem not_isRegular_comap_freeGroupNorm_subtype_closure {a b c : α} (hbc : b ≠ c) :
    ¬((freeGroupNorm α).comap (Subgroup.closure {of a * of b, of a * of c}).subtype).IsRegular := by
  intro h
  obtain ⟨u, -, -, -, -, -, -, hu⟩ := (isRegular_iff _).1 h
    ⟨of a * of b, Subgroup.subset_closure (by simp)⟩
    ⟨of a * of c, Subgroup.subset_closure (by simp)⟩
  have heven : Even (norm (u : FreeGroup α)) :=
    even_norm_of_mem_closure (by rintro _ (rfl | rfl) <;> simp [even_norm_mul_iff]) u.2
  rw [gromovProduct_comap, Subgroup.coe_subtype,
    gromovProduct_freeGroupNorm_of_mul_of_of_mul_of hbc] at hu
  have hu' : norm (u : FreeGroup α) = 1 := by simpa using hu
  simp [hu'] at heven

/-! ### Separated elements -/

/-- Two elements of a free group that do not commute are separated for the word length. -/
theorem isSeparated_freeGroupNorm_of_not_commute {u v : FreeGroup α} (h : ¬Commute u v) :
    (freeGroupNorm α).IsSeparated u v := by
  -- The reduced words of `u⁻ᵐ` and `vⁿ` begin with prefixes of the rays of `u⁻¹` and `v`, and
  -- these rays differ in their first `L` letters.
  set L := u.norm * v.norm
  have hL : (u⁻¹ ^ L).toWord.take L ≠ (v ^ L).toWord.take L := fun heq =>
    h (Commute.inv_left_iff.1 (commute_of_take_toWord_pow_eq (by rw [norm_inv_eq]) heq))
  have key (m n : ℕ) (hm : L ≤ m) (hn : L ≤ n) :
      List.commonPrefixLength (u⁻¹ ^ m).toWord (v ^ n).toWord =
        List.commonPrefixLength ((u⁻¹ ^ L).toWord.take L) ((v ^ L).toWord.take L) := by
    rw [← take_toWord_pow_of_le u⁻¹ hm, ← take_toWord_pow_of_le v hn] at hL ⊢
    rw [List.commonPrefixLength_take_left, List.commonPrefixLength_take_right, ← min_assoc,
      min_self, min_eq_right]
    by_contra! hlt
    exact hL (List.le_commonPrefixLength_iff.1 hlt.le).2.2
  refine isSeparated_iff.2 ⟨L, fun m n hm hn => ?_⟩
  rw [← inv_pow, ← inv_pow, gromovProduct_freeGroupNorm, gromovProduct_freeGroupNorm, key m n hm hn,
    key L L le_rfl le_rfl]

end TauCeti.LyndonLength
