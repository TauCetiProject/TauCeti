/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.Profinite.Demushkin.Character.Basic
public import TauCeti.Topology.Algebra.Group.Profinite.Demushkin.NormalForm.Existence
public import TauCeti.Topology.Algebra.Group.Profinite.Demushkin.NormalForm.QInvariant

/-!
# The canonical character of a Demushkin group in normal form

Let `G` be a Demushkin group and let `e : G ≃ₜ* ⟨x₁, …, xₙ ∣ r⟩` be a topological isomorphism onto
the pro-`p` group presented by one of Labute's normal-form words `r`. The canonical character
`TauCeti.demushkinCharacter` of `G`, pulled back along `e⁻¹`, is a continuous character of the
presented group with the prescription property, so it is the character with the tabulated values
of `TauCeti.Topology.Algebra.Group.Profinite.Demushkin.NormalForm.Prescription`, and its image is
the closed subgroup of `ℤ_pˣ` computed in
`TauCeti.Topology.Algebra.Group.Profinite.Demushkin.NormalForm.Existence`. This file reads both
tables on the canonical character of `G` through `e`: the *marking* of the generators, in the form
the marked classification of Demushkin groups states it, and the image invariant.

The values are tabulated as equations in `ℤ_p`, `χ(x₂)(1 - q) = 1` rather than `χ(x₂) = (1 - q)⁻¹`,
on the generators `TauCeti.presentedProPGen`, which are `1` out of range. Because of that
convention a marking clause on a generator beyond the rank is not vacuous but false:
`TauCeti.not_marked_of_demushkinRank_le` records that no isomorphism onto any presented group
satisfies a clause `χ(x_i)(1 - 2^f) = 1` at an index `i` at or beyond the rank. In particular the
fourth-generator clause of the even dyadic family fails at rank `2`, and the third-generator clause
of the odd family fails at rank `1`, so any marked form of those families must assume rank at
least `4`, respectively `3`.

Finally, the images separate Demushkin groups that the pair `(n, q)` does not: at `q = 2` and any
rank `n ≥ 3` there are two Demushkin groups of rank `n` with `q = 2` that are not topologically
isomorphic, because their canonical characters have the images `{±1} × U^(2)` and `{±1}`
(`TauCeti.exists_isDemushkin_demushkinQ_eq_two_isEmpty_continuousMulEquiv`). For `q ≠ 2` the pair
`(n, q)` is a complete invariant; that is the classification theorem and is not proved here.

## Main results

* `TauCeti.demushkinCharacter_apply_equiv_symm_of_equiv_demushkinWordNeTwo`,
  `TauCeti.demushkinCharacter_apply_equiv_symm_of_equiv_demushkinWordTwoOdd`,
  `TauCeti.demushkinCharacter_apply_equiv_symm_of_equiv_demushkinWordTwoOddTop`,
  `TauCeti.demushkinCharacter_apply_equiv_symm_of_equiv_demushkinWordTwoEven`,
  `TauCeti.demushkinCharacter_apply_equiv_symm_of_equiv_demushkinWordTwoRankTwo`: **the character
  table on the canonical character**: along an isomorphism onto a normal form, the canonical
  character takes the tabulated values on the marked generators.
* `TauCeti.range_demushkinCharacter_eq_unitsPrincipal_of_equiv_demushkinWordNeTwo`,
  `TauCeti.range_demushkinCharacter_eq_bot_of_equiv_demushkinWordNeTwo`,
  `TauCeti.range_demushkinCharacter_eq_zpowers_neg_one_of_equiv_demushkinWordNeTwo`,
  `TauCeti.range_demushkinCharacter_eq_unitsPlusMinus_of_equiv_demushkinWordTwoOdd`,
  `TauCeti.range_demushkinCharacter_eq_zpowers_neg_one_of_equiv_demushkinWordTwoOdd_one`,
  `TauCeti.range_demushkinCharacter_eq_zpowers_neg_one_of_equiv_demushkinWordTwoOddTop`,
  `TauCeti.range_demushkinCharacter_eq_unitsPlusMinus_of_equiv_demushkinWordTwoEven`,
  `TauCeti.range_demushkinCharacter_eq_of_equiv_demushkinWordTwoEven_two_pow`,
  `TauCeti.range_demushkinCharacter_eq_of_equiv_demushkinWordTwoRankTwo_two_pow`: **the image
  table on the canonical character**: a Demushkin group isomorphic to a normal form has the
  tabulated closed subgroup of `ℤ_pˣ` as the image of its canonical character.
* `TauCeti.not_marked_of_demushkinRank_le`: a marking clause on a generator at or beyond the rank
  is unsatisfiable.
* `TauCeti.exists_isDemushkin_demushkinQ_eq_two_isEmpty_continuousMulEquiv`: **`(n, q)` is not a
  complete invariant at `q = 2`**.

## References

* J. P. Labute, *Classification of Demushkin groups*, Canad. J. Math. 19 (1967), 106–132, §3,
  Theorem 4 and its corollary, and Remark 2.
* J.-P. Serre, *Structure de certains pro-p-groupes*, Séminaire Bourbaki 252 (1962/63).
* J. Neukirch, A. Schmidt and K. Wingberg, *Cohomology of Number Fields*, 2nd ed., Chapter III, §9.
-/

public section

namespace TauCeti

open Subgroup

universe u

variable {n : ℕ} {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TotallyDisconnectedSpace G]

/-! ### The `q ≠ 2` normal form `x₁^q (x₁, x₂)(x₃, x₄) ⋯ (x_{n-1}, x_n)` -/

section NeTwo

variable {p : ℕ} [Fact p.Prime] {q : ℕ} (hG : IsDemushkin p G)
include hG

/-- **The character table on the canonical character, `q ≠ 2`.** Along an isomorphism
`e : G ≃ₜ* ⟨x₁, …, xₙ ∣ x₁^q (x₁, x₂)(x₃, x₄) ⋯ (x_{n-1}, x_n)⟩`, for `p ∣ q` and `n ≥ 2` even, the
canonical character of `G` satisfies `χ(x₂)(1 - q) = 1` and `χ(x_i) = 1` for every `i ≠ 2`, the
generators being read back in `G` through `e⁻¹`. -/
theorem demushkinCharacter_apply_equiv_symm_of_equiv_demushkinWordNeTwo (hq : p ∣ q) (hn : Even n)
    (hn₁ : 1 < n) (e : G ≃ₜ* presentedProP p (Fin n) {demushkinWordNeTwo q n (freeProPGen p n)}) :
    (demushkinCharacter hG (e.symm (presentedProPGen p n _ 1)) : ℤ_[p]) * (1 - q) = 1 ∧
      ∀ i, i ≠ 1 → demushkinCharacter hG (e.symm (presentedProPGen p n _ i)) = 1 :=
  (hasPrescriptionProperty_presentedProP_demushkinWordNeTwo_iff q n _ hq hn hn₁).1
    (hasPrescriptionProperty_demushkinCharacter hG).comp_equiv

/-- **A Demushkin group isomorphic to the `q ≠ 2` normal form with `q = p^f` has orientation image
`U^(f) = 1 + p^f ℤ_p`**, for `f ≥ 1`, and `f ≥ 2` when `p = 2`, and `n ≥ 2` even. -/
theorem range_demushkinCharacter_eq_unitsPrincipal_of_equiv_demushkinWordNeTwo (hn : Even n)
    (hn₁ : 1 < n) {f : ℕ} (hq : q = p ^ f) (hf : 0 < f) (hf₂ : p = 2 → 2 ≤ f)
    (e : G ≃ₜ* presentedProP p (Fin n) {demushkinWordNeTwo q n (freeProPGen p n)}) :
    (demushkinCharacter hG).toMonoidHom.range = unitsPrincipal p f :=
  range_demushkinCharacter_eq_of_equiv hG e fun _ ↦
    range_eq_unitsPrincipal_of_hasPrescriptionProperty_demushkinWordNeTwo hn hn₁ hq hf hf₂

/-- **A Demushkin group isomorphic to the `q = 0` normal form has trivial orientation image**, for
`n ≥ 2` even. -/
theorem range_demushkinCharacter_eq_bot_of_equiv_demushkinWordNeTwo (hn : Even n) (hn₁ : 1 < n)
    (hq : q = 0)
    (e : G ≃ₜ* presentedProP p (Fin n) {demushkinWordNeTwo q n (freeProPGen p n)}) :
    (demushkinCharacter hG).toMonoidHom.range = ⊥ :=
  range_demushkinCharacter_eq_of_equiv hG e fun _ ↦
    range_eq_bot_of_hasPrescriptionProperty_demushkinWordNeTwo hn hn₁ hq

end NeTwo

section Dyadic

variable (hG : IsDemushkin 2 G)
include hG

/-- **A Demushkin group isomorphic to the even-rank form `x₁² (x₁, x₂)(x₃, x₄) ⋯` has orientation
image `{±1}`**, for `n ≥ 2` even: this is the `q ≠ 2` word at `q = 2`, the even dyadic form with
`α = 0` at level `f = ∞`. -/
theorem range_demushkinCharacter_eq_zpowers_neg_one_of_equiv_demushkinWordNeTwo (hn : Even n)
    (hn₁ : 1 < n)
    (e : G ≃ₜ* presentedProP 2 (Fin n) {demushkinWordNeTwo 2 n (freeProPGen 2 n)}) :
    (demushkinCharacter hG).toMonoidHom.range = zpowers (-1 : ℤ_[2]ˣ) :=
  range_demushkinCharacter_eq_of_equiv hG e fun _ ↦
    range_eq_zpowers_neg_one_of_hasPrescriptionProperty_demushkinWordNeTwo hn hn₁

/-! ### The `q = 2`, `n` odd normal form `x₁² x₂^{2^f} (x₂, x₃) ⋯ (x_{n-1}, x_n)` -/

section TwoOdd

variable {f : ℕ}

/-- **The character table on the canonical character, `q = 2` and `n` odd.** Along an isomorphism
`e : G ≃ₜ* ⟨x₁, …, xₙ ∣ x₁² x₂^{2^f} (x₂, x₃) ⋯ (x_{n-1}, x_n)⟩`, for `f ≥ 1` and `n ≥ 3` odd, the
canonical character of `G` satisfies `χ(x₁) = -1`, `χ(x₃)(1 - 2^f) = 1` and `χ(x_i) = 1`
otherwise. -/
theorem demushkinCharacter_apply_equiv_symm_of_equiv_demushkinWordTwoOdd (hf : 0 < f) (hn : Odd n)
    (hn₂ : 2 < n)
    (e : G ≃ₜ* presentedProP 2 (Fin n) {demushkinWordTwoOdd f n (freeProPGen 2 n)}) :
    demushkinCharacter hG (e.symm (presentedProPGen 2 n _ 0)) = -1 ∧
      (demushkinCharacter hG (e.symm (presentedProPGen 2 n _ 2)) : ℤ_[2]) * (1 - 2 ^ f) = 1 ∧
      ∀ i, i ≠ 0 → i ≠ 2 → demushkinCharacter hG (e.symm (presentedProPGen 2 n _ i)) = 1 :=
  (hasPrescriptionProperty_presentedProP_demushkinWordTwoOdd_iff f n _ hf hn hn₂).1
    (hasPrescriptionProperty_demushkinCharacter hG).comp_equiv

/-- **A Demushkin group isomorphic to the odd-rank dyadic normal form at level `f` has orientation
image `{±1} × U^(f)`**, for `f ≥ 2` and `n ≥ 3` odd. -/
theorem range_demushkinCharacter_eq_unitsPlusMinus_of_equiv_demushkinWordTwoOdd (hf : 2 ≤ f)
    (hn : Odd n) (hn₂ : 2 < n)
    (e : G ≃ₜ* presentedProP 2 (Fin n) {demushkinWordTwoOdd f n (freeProPGen 2 n)}) :
    (demushkinCharacter hG).toMonoidHom.range = unitsPlusMinus f :=
  range_demushkinCharacter_eq_of_equiv hG e fun _ ↦
    range_eq_unitsPlusMinus_of_hasPrescriptionProperty_demushkinWordTwoOdd hf hn hn₂

/-- **A Demushkin group isomorphic to `ℤ/2 = ⟨x₁ ∣ x₁²⟩` has orientation image `{±1}`**: the odd
word at rank one reads `x₁²` for every level `f`. -/
theorem range_demushkinCharacter_eq_zpowers_neg_one_of_equiv_demushkinWordTwoOdd_one
    (e : G ≃ₜ* presentedProP 2 (Fin 1) {demushkinWordTwoOdd f 1 (freeProPGen 2 1)}) :
    (demushkinCharacter hG).toMonoidHom.range = zpowers (-1 : ℤ_[2]ˣ) :=
  range_demushkinCharacter_eq_of_equiv hG e fun _ ↦
    range_eq_zpowers_neg_one_of_hasPrescriptionProperty_demushkinWordTwoOdd_one

end TwoOdd

/-! ### The `q = 2`, `n` odd normal form at level `f = ∞`, `x₁² (x₂, x₃) ⋯ (x_{n-1}, x_n)` -/

section TwoOddTop

/-- **The character table on the canonical character, `q = 2`, `n` odd, level `f = ∞`.** Along an
isomorphism `e : G ≃ₜ* ⟨x₁, …, xₙ ∣ x₁² (x₂, x₃) ⋯ (x_{n-1}, x_n)⟩`, for `n` odd, the canonical
character of `G` satisfies `χ(x₁) = -1` and `χ(x_i) = 1` for every `i ≠ 1`. -/
theorem demushkinCharacter_apply_equiv_symm_of_equiv_demushkinWordTwoOddTop (hn : Odd n)
    (e : G ≃ₜ* presentedProP 2 (Fin n) {demushkinWordTwoOddTop n (freeProPGen 2 n)}) :
    demushkinCharacter hG (e.symm (presentedProPGen 2 n _ 0)) = -1 ∧
      ∀ i, i ≠ 0 → demushkinCharacter hG (e.symm (presentedProPGen 2 n _ i)) = 1 :=
  (hasPrescriptionProperty_presentedProP_demushkinWordTwoOddTop_iff n _ hn).1
    (hasPrescriptionProperty_demushkinCharacter hG).comp_equiv

/-- **A Demushkin group isomorphic to the odd-rank dyadic normal form at level `f = ∞` has
orientation image `{±1}`**, for `n` odd. -/
theorem range_demushkinCharacter_eq_zpowers_neg_one_of_equiv_demushkinWordTwoOddTop (hn : Odd n)
    (e : G ≃ₜ* presentedProP 2 (Fin n) {demushkinWordTwoOddTop n (freeProPGen 2 n)}) :
    (demushkinCharacter hG).toMonoidHom.range = zpowers (-1 : ℤ_[2]ˣ) :=
  range_demushkinCharacter_eq_of_equiv hG e fun _ ↦
    range_eq_zpowers_neg_one_of_hasPrescriptionProperty_demushkinWordTwoOddTop hn

end TwoOddTop

/-! ### The `q = 2`, `n` even normal form `x₁^{2+a} (x₁, x₂) x₃^{2^f} (x₃, x₄) ⋯ (x_{n-1}, x_n)` -/

section TwoEven

variable {a f : ℕ}

/-- **The character table on the canonical character, `q = 2` and `n` even.** Along an isomorphism
`e : G ≃ₜ* ⟨x₁, …, xₙ ∣ x₁^{2+a} (x₁, x₂) x₃^{2^f} (x₃, x₄) ⋯ (x_{n-1}, x_n)⟩`, for `a` even,
`f ≥ 1` and `n ≥ 4` even, the canonical character of `G` satisfies `χ(x₂)(1 + a) = -1`,
`χ(x₄)(1 - 2^f) = 1` and `χ(x_i) = 1` otherwise. -/
theorem demushkinCharacter_apply_equiv_symm_of_equiv_demushkinWordTwoEven (ha : 2 ∣ a) (hf : 0 < f)
    (hn : Even n) (hn₃ : 3 < n)
    (e : G ≃ₜ* presentedProP 2 (Fin n) {demushkinWordTwoEven a f n (freeProPGen 2 n)}) :
    (demushkinCharacter hG (e.symm (presentedProPGen 2 n _ 1)) : ℤ_[2]) * (1 + a) = -1 ∧
      (demushkinCharacter hG (e.symm (presentedProPGen 2 n _ 3)) : ℤ_[2]) * (1 - 2 ^ f) = 1 ∧
      ∀ i, i ≠ 1 → i ≠ 3 → demushkinCharacter hG (e.symm (presentedProPGen 2 n _ i)) = 1 :=
  (hasPrescriptionProperty_presentedProP_demushkinWordTwoEven_iff a f n _ ha hf hn hn₃).1
    (hasPrescriptionProperty_demushkinCharacter hG).comp_equiv

/-- **A Demushkin group isomorphic to the even-rank dyadic normal form with `2^f ∣ α` has
orientation image `{±1} × U^(f)`**, for `f ≥ 2` and `n ≥ 4` even. This includes `α = 0`. -/
theorem range_demushkinCharacter_eq_unitsPlusMinus_of_equiv_demushkinWordTwoEven (hf : 2 ≤ f)
    (hn : Even n) (hn₃ : 3 < n) (ha' : (2 : ℤ_[2]) ^ f ∣ (a : ℤ_[2]))
    (e : G ≃ₜ* presentedProP 2 (Fin n) {demushkinWordTwoEven a f n (freeProPGen 2 n)}) :
    (demushkinCharacter hG).toMonoidHom.range = unitsPlusMinus f :=
  range_demushkinCharacter_eq_of_equiv hG e fun _ ↦
    range_eq_unitsPlusMinus_of_hasPrescriptionProperty_demushkinWordTwoEven hf hn hn₃ ha'

/-- **A Demushkin group isomorphic to the even-rank dyadic normal form with `α = 2^g` and level
`f > g` has orientation image `U^[g]`**, the closed subgroup generated by `-1 + 2^g`, for `g ≥ 2`
and `n ≥ 4` even. -/
theorem range_demushkinCharacter_eq_of_equiv_demushkinWordTwoEven_two_pow {g : ℕ} (hg : 2 ≤ g)
    (hgf : g < f) (hn : Even n) (hn₃ : 3 < n) {w : ℤ_[2]ˣ}
    (hw : (w : ℤ_[2]) = -1 + (2 : ℤ_[2]) ^ g)
    (e : G ≃ₜ* presentedProP 2 (Fin n) {demushkinWordTwoEven (2 ^ g) f n (freeProPGen 2 n)}) :
    (demushkinCharacter hG).toMonoidHom.range = (zpowers w).topologicalClosure :=
  range_demushkinCharacter_eq_of_equiv hG e fun _ ↦
    range_eq_of_hasPrescriptionProperty_demushkinWordTwoEven_two_pow hg hgf hn hn₃ hw

end TwoEven

/-! ### The `q = 2`, `n = 2` normal form `x₁^{2+a} (x₁, x₂)` -/

section TwoRankTwo

variable {a : ℕ}

/-- **The character table on the canonical character, `q = 2` and `n = 2`.** Along an isomorphism
`e : G ≃ₜ* ⟨x₁, x₂ ∣ x₁^{2+a} (x₁, x₂)⟩`, for `a` even, the canonical character of `G` satisfies
`χ(x₁) = 1` and `χ(x₂)(1 + a) = -1`. -/
theorem demushkinCharacter_apply_equiv_symm_of_equiv_demushkinWordTwoRankTwo (ha : 2 ∣ a)
    (e : G ≃ₜ* presentedProP 2 (Fin 2) {demushkinWordTwoRankTwo a (freeProPGen 2 2)}) :
    demushkinCharacter hG (e.symm (presentedProPGen 2 2 _ 0)) = 1 ∧
      (demushkinCharacter hG (e.symm (presentedProPGen 2 2 _ 1)) : ℤ_[2]) * (1 + a) = -1 :=
  (hasPrescriptionProperty_presentedProP_demushkinWordTwoRankTwo_iff a _ ha).1
    (hasPrescriptionProperty_demushkinCharacter hG).comp_equiv

/-- **A Demushkin group isomorphic to the rank-two dyadic normal form with `α = 2^g` has
orientation image `U^[g]`**, the closed subgroup generated by `-1 + 2^g`, for `g ≥ 2`. -/
theorem range_demushkinCharacter_eq_of_equiv_demushkinWordTwoRankTwo_two_pow {g : ℕ} (hg : 2 ≤ g)
    {w : ℤ_[2]ˣ} (hw : (w : ℤ_[2]) = -1 + (2 : ℤ_[2]) ^ g)
    (e : G ≃ₜ* presentedProP 2 (Fin 2) {demushkinWordTwoRankTwo (2 ^ g) (freeProPGen 2 2)}) :
    (demushkinCharacter hG).toMonoidHom.range = (zpowers w).topologicalClosure :=
  range_demushkinCharacter_eq_of_equiv hG e fun _ ↦
    range_eq_of_hasPrescriptionProperty_demushkinWordTwoRankTwo_two_pow hg hw

end TwoRankTwo

/-! ### Marking clauses beyond the rank -/

/-- **A marking clause `χ(x_i)(1 - 2^f) = 1` on a generator beyond the rank is unsatisfiable.**
For `i ≥ demushkinRank hG` the generator `presentedProPGen 2 _ _ i` of any presented group on
`Fin (demushkinRank hG)` is `1`, and every isomorphism and every character sends `1` to `1`, so
the clause reads `1 - 2^f = 1`, which is false in `ℤ₂`, for every `f`, every relator set and every
isomorphism `e`. At rank `2` and `i = 3` this is the fourth-generator clause `χ(x₄)(1 - 2^f) = 1`
of the even-rank dyadic family, whose other hypotheses are met at rank two by
`⟨x₁, x₂ ∣ x₁⁶ (x₁, x₂)⟩` with `α = 4`, `f = 3` and image `U^[2]`; at rank `1` and `i = 2` it is
the third-generator clause of the odd-rank family. This is why any marked statement of those
families must assume rank at least `4`, respectively `3`. -/
theorem not_marked_of_demushkinRank_le {i : ℕ} (hi : demushkinRank hG ≤ i) (f : ℕ)
    (rels : Set (freeProP 2 (Fin (demushkinRank hG))))
    (e : G ≃ₜ* presentedProP 2 (Fin (demushkinRank hG)) rels) :
    ¬ ((demushkinCharacter hG (e.symm (presentedProPGen 2 (demushkinRank hG) rels i)) : ℤ_[2]) *
        (1 - 2 ^ f) = 1) := by
  rw [presentedProPGen_eq_one_of_le _ _ _ hi, map_one, map_one, Units.val_one, one_mul,
    sub_eq_self]
  exact pow_ne_zero _ two_ne_zero

end Dyadic

/-! ### `(n, q)` is not a complete invariant at `q = 2` -/

/-- **At `q = 2` the pair `(n, q)` is not a complete invariant of Demushkin groups.** For every
`n ≥ 3` there are two Demushkin groups of rank `n` with `q = 2`, each presented on `n` generators
by one relator, which are not topologically isomorphic: the images of their canonical characters
are `{±1} × U^(2)` and `{±1}`. For `n` odd they are `⟨x₁, …, xₙ ∣ x₁² x₂⁴ (x₂, x₃) ⋯⟩` and
`⟨x₁, …, xₙ ∣ x₁² (x₂, x₃) ⋯⟩`; for `n` even they are
`⟨x₁, …, xₙ ∣ x₁² (x₁, x₂) x₃⁴ (x₃, x₄) ⋯⟩` and `⟨x₁, …, xₙ ∣ x₁² (x₁, x₂)(x₃, x₄) ⋯⟩`. At `n = 2`
every Demushkin group with `q = 2` has image
`U^[v₂(α)]` or `{±1}`, and at `n = 1` the only Demushkin group is `ℤ/2`. -/
theorem exists_isDemushkin_demushkinQ_eq_two_isEmpty_continuousMulEquiv (hn : 3 ≤ n) :
    ∃ r₁ r₂ : freeProP 2 (Fin n), ∃ h₁ : IsDemushkin 2 (presentedProP 2 (Fin n) {r₁}),
      ∃ h₂ : IsDemushkin 2 (presentedProP 2 (Fin n) {r₂}),
      demushkinRank h₁ = n ∧ demushkinRank h₂ = n ∧ demushkinQ h₁ = 2 ∧ demushkinQ h₂ = 2 ∧
        IsEmpty (presentedProP 2 (Fin n) {r₁} ≃ₜ* presentedProP 2 (Fin n) {r₂}) := by
  rcases Nat.even_or_odd n with hev | hodd
  · -- Even rank `n ≥ 4`: `x₁² (x₁, x₂) x₃⁴ (x₃, x₄) ⋯` against `x₁² (x₁, x₂)(x₃, x₄) ⋯`.
    have hn₃ : 3 < n := by obtain ⟨k, hk⟩ := hev; omega
    have h₁ := isDemushkin_presentedProP_demushkinWordTwoEven hev (by omega) (dvd_zero 2) two_pos
    have h₂ := isDemushkin_presentedProP_demushkinWordNeTwo (p := 2) hev (by omega) dvd_rfl
    refine ⟨_, _, h₁, h₂, demushkinRank_presentedProP_demushkinWordTwoEven (dvd_zero 2) two_pos h₁,
      demushkinRank_presentedProP_demushkinWordNeTwo dvd_rfl h₂,
      demushkinQ_presentedProP_demushkinWordTwoEven (dvd_zero 4) two_pos h₁, ?_, ⟨fun e ↦ ?_⟩⟩
    · rw [demushkinQ_presentedProP_demushkinWordNeTwo dvd_rfl two_ne_zero h₂, padicValNat_self,
        pow_one]
    · refine unitsPlusMinus_ne_zpowers_neg_one 2 ?_
      rw [← range_demushkinCharacter_eq_unitsPlusMinus_of_equiv_demushkinWordTwoEven h₂ le_rfl hev
        hn₃ (by rw [Nat.cast_zero]; exact dvd_zero _) e.symm]
      exact range_demushkinCharacter_eq_zpowers_neg_one_of_equiv_demushkinWordNeTwo h₂ hev
        (by omega) (ContinuousMulEquiv.refl _)
  · -- Odd rank `n ≥ 3`: `x₁² x₂⁴ (x₂, x₃) ⋯` against `x₁² (x₂, x₃) ⋯`.
    have h₁ := isDemushkin_presentedProP_demushkinWordTwoOdd hodd (f := 2) two_pos
    have h₂ := isDemushkin_presentedProP_demushkinWordTwoOddTop hodd
    refine ⟨_, _, h₁, h₂, demushkinRank_presentedProP_demushkinWordTwoOdd two_pos h₁,
      demushkinRank_presentedProP_demushkinWordTwoOddTop h₂,
      demushkinQ_presentedProP_demushkinWordTwoOdd two_pos h₁,
      demushkinQ_presentedProP_demushkinWordTwoOddTop h₂, ⟨fun e ↦ ?_⟩⟩
    refine unitsPlusMinus_ne_zpowers_neg_one 2 ?_
    rw [← range_demushkinCharacter_eq_unitsPlusMinus_of_equiv_demushkinWordTwoOdd h₂ le_rfl hodd
      (by omega) e.symm]
    exact range_demushkinCharacter_eq_zpowers_neg_one_of_equiv_demushkinWordTwoOddTop h₂ hodd
      (ContinuousMulEquiv.refl _)

end TauCeti
