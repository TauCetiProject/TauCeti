/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.InfWord.Mul
public import TauCeti.GroupTheory.LyndonLength.Basic

/-!
# Cyclic decompositions, subgroups of infinite words, and free Lyndon length functions

Let `Λ` be a discretely ordered abelian group and `X` a set. When `Λ` is non-Archimedean and `X`
is nonempty, the partial multiplication `∗` of reduced `Λ`-words is genuinely partial and not
every reduced word admits a cyclic decomposition (see `TauCeti.GroupTheory.InfWord.Examples`).

Nonetheless, many subsets of the reduced `Λ`-words are closed under `∗` and inversion and contain
the empty word; equipped with `∗`, any such subset `H` (`TauCeti.InfWord.ReducedSubgroup Λ X`) is a
group. Because the Gromov product `(|u| + |v| - |u⁻¹ ∗ v|) / 2` in such a group is the length of the
longest common initial segment of `u` and `v`, word length `w ↦ |w|` is always a Lyndon length
function on `H` satisfying (L4).

To obtain axiom (L5), `|w| < |w ^ 2|` for `w ≠ ε`, one restricts to `CDR(Λ, X)`
(`TauCeti.InfWord.CDR`), the set of reduced words admitting a *cyclic decomposition*
`w = c⁻¹ ++ v ++ c` with `v` cyclically reduced (`TauCeti.InfWord.IsCyclicallyReduced`). Every word
`w ∈ CDR(Λ, X)` has a unique cyclic decomposition (`TauCeti.InfWord.IsCyclicDecomposition.unique`),
its square `w ∗ w` is defined and equals `c⁻¹ ++ (v ++ v) ++ c`, and for `w ≠ ε` the cyclically
reduced core `v` is nonempty so `|w| < |w| + |v| = |w ∗ w|`. Consequently, on every subgroup of
`CDR(Λ, X)`, word length is a free Lyndon length function
(`TauCeti.InfWord.ReducedSubgroup.isFree_lyndonLength`).

## Main definitions

* `TauCeti.InfWord.IsCyclicallyReduced`: reduced `Λ`-words whose first and last letters do not
  cancel (`w ++ w` is reduced).
* `TauCeti.InfWord.IsCyclicDecomposition`: `w = c⁻¹ ++ v ++ c` is reduced with `v` cyclically
  reduced.
* `TauCeti.InfWord.CDR`: the set `CDR(Λ, X)` of words admitting a cyclic decomposition.
* `TauCeti.InfWord.lyndonLengthOfIsMul`, `TauCeti.InfWord.ReducedSubgroup.lyndonLength`: word length
  as a `Λ`-valued Lyndon length function.

## Main results

* `TauCeti.InfWord.IsCyclicallyReduced.npow`, `TauCeti.InfWord.IsCyclicallyReduced.isMul_npow`:
  the powers `uⁿ` (`TauCeti.InfWord.npow`) of a cyclically reduced word `u` are cyclically
  reduced, and `uᵐ ∗ uⁿ = uᵐ⁺ⁿ`.
* `TauCeti.InfWord.IsCyclicDecomposition.unique`: uniqueness of the cyclic decomposition `(c, v)`.
* `TauCeti.InfWord.IsCyclicDecomposition.mul_self`: for `w = c⁻¹ ++ v ++ c` in `CDR(Λ, X)`,
  `w ∗ w = c⁻¹ ++ (v ++ v) ++ c`.
* `TauCeti.InfWord.mem_CDR_of_isMul_conj`: `CDR(Λ, X)` is closed under conjugation: if
  `u ∈ CDR(Λ, X)` and `c⁻¹ ∗ u ∗ c` is defined, then it lies in `CDR(Λ, X)`.
* `TauCeti.InfWord.gromovProduct_lyndonLengthOfIsMul_eq_of_isGreatest`,
  `TauCeti.InfWord.ReducedSubgroup.gromovProduct_lyndonLength_eq_of_isGreatest`: the Gromov product
  of word length is the length of the longest common initial segment.
* `TauCeti.InfWord.isFree_lyndonLengthOfIsMul`,
  `TauCeti.InfWord.ReducedSubgroup.isFree_lyndonLength`: on any subgroup of `CDR(Λ, X)`, `w ↦ |w|`
  is a free Lyndon length function.

## References

* A. Myasnikov, V. Remeslennikov, D. Serbin, *Regular free length functions on Lyndon's free
  `ℤ[t]`-group `F^{ℤ[t]}`*, Contemp. Math. 378 (2005), 37–77, §3.3 (standard exponentiation and
  Lemma 3.8 (1)) and §4 (Theorem 4.1 and Corollary 4.2).
* O. Kharlampovich, A. Myasnikov, V. Remeslennikov, D. Serbin, *Groups with free regular length
  functions in `ℤⁿ`*, Trans. Amer. Math. Soc. 364 (2012), 2847–2882, §2.3, Theorem 2.
-/

public section

namespace TauCeti

namespace InfWord

variable {Λ X : Type*}

/-! ### Cyclically reduced infinite words -/

section Preorder

variable [Zero Λ] [Preorder Λ] [SuccOrder Λ] {w : InfWord Λ X}

/-- A `Λ`-word `w` is *cyclically reduced* if it is reduced and, when nonempty, its first letter is
not the inverse of its last letter. The empty word is cyclically reduced. -/
def IsCyclicallyReduced (w : InfWord Λ X) : Prop :=
  w.IsReduced ∧
    (0 < w.length → w.letter (Order.succ 0) ≠ (w.letter w.length).map (Prod.map id not))

theorem isCyclicallyReduced_iff :
    w.IsCyclicallyReduced ↔ w.IsReduced ∧
      (0 < w.length → w.letter (Order.succ 0) ≠ (w.letter w.length).map (Prod.map id not)) :=
  Iff.rfl

@[grind →]
theorem IsCyclicallyReduced.isReduced (h : w.IsCyclicallyReduced) : w.IsReduced :=
  h.1

/-- In a nonempty cyclically reduced word, the first letter is not the inverse of the last
letter. -/
theorem IsCyclicallyReduced.letter_succ_zero_ne (h : w.IsCyclicallyReduced) (hw : 0 < w.length) :
    w.letter (Order.succ 0) ≠ (w.letter w.length).map (Prod.map id not) :=
  h.2 hw

@[simp]
theorem isCyclicallyReduced_empty : (empty Λ X).IsCyclicallyReduced :=
  ⟨isReduced_empty, by simp⟩

end Preorder

section LinearOrder

variable [Zero Λ] [LinearOrder Λ] [SuccOrder Λ]

/-- Every constant word `x^α` is cyclically reduced. -/
@[simp]
theorem isCyclicallyReduced_ofFun_const (α : Λ) (x : X × Bool) :
    (ofFun α fun _ => x).IsCyclicallyReduced := by
  refine ⟨isReduced_ofFun_const α x, fun h => ?_⟩
  have hα : 0 < α := by simpa using h
  have h01 : 0 < Order.succ (0 : Λ) := Order.lt_succ_self_of_lt hα
  rw [length_ofFun, max_eq_left hα.le,
    letter_ofFun_of_pos_of_le _ h01 (Order.succ_le_of_lt hα),
    letter_ofFun_of_pos_of_le _ hα le_rfl]
  simp [Prod.ext_iff]

end LinearOrder

section Discrete

variable [AddCommGroup Λ] [LinearOrder Λ] [IsOrderedAddMonoid Λ] [SuccOrder Λ]
  {u v w c c₁ c₂ v₁ v₂ : InfWord Λ X}

/-- A word `w` is cyclically reduced if and only if `w ++ w` is reduced. -/
theorem isCyclicallyReduced_iff_isReduced_append_self :
    w.IsCyclicallyReduced ↔ (w ++ w).IsReduced := by
  rw [isCyclicallyReduced_iff, isReduced_append_iff]
  exact ⟨fun ⟨h₁, h₂⟩ => ⟨h₁, h₁, fun h _ => h₂ h⟩, fun ⟨h₁, _, h₂⟩ => ⟨h₁, fun h => h₂ h h⟩⟩

theorem IsCyclicallyReduced.isReduced_append_self (h : w.IsCyclicallyReduced) :
    (w ++ w).IsReduced :=
  isCyclicallyReduced_iff_isReduced_append_self.1 h

@[simp, grind =]
theorem isCyclicallyReduced_inv : w⁻¹.IsCyclicallyReduced ↔ w.IsCyclicallyReduced := by
  rw [isCyclicallyReduced_iff_isReduced_append_self, ← inv_append, isReduced_inv,
    ← isCyclicallyReduced_iff_isReduced_append_self]

theorem IsCyclicallyReduced.inv (h : w.IsCyclicallyReduced) : w⁻¹.IsCyclicallyReduced :=
  isCyclicallyReduced_inv.2 h

/-- If `w` is cyclically reduced, then `w ++ w` is again cyclically reduced. -/
theorem IsCyclicallyReduced.append_self (h : w.IsCyclicallyReduced) :
    (w ++ w).IsCyclicallyReduced := by
  refine ⟨h.isReduced_append_self, fun hlen => ?_⟩
  have hw : 0 < w.length := length_pos_iff.2 (by rintro rfl; simp at hlen)
  rw [letter_append_of_le _ (Order.succ_le_of_lt hw), length_append,
    letter_append_length_add _ _ hw]
  exact h.2 hw

theorem IsCyclicallyReduced.isMul_self (h : w.IsCyclicallyReduced) : IsMul w w (w ++ w) :=
  isMul_append h.isReduced_append_self

theorem IsCyclicallyReduced.mul_self (h : w.IsCyclicallyReduced) :
    w.mul w = Part.some (w ++ w) :=
  mul_eq_some_append h.isReduced_append_self

/-- A cyclically reduced word `u` cannot cancel on both sides against a reduced word `c`: either
`u ++ c` or `c⁻¹ ++ u` is reduced. -/
theorem IsCyclicallyReduced.isReduced_append_or_isReduced_inv_append (hu : u.IsCyclicallyReduced)
    (hc : c.IsReduced) : (u ++ c).IsReduced ∨ (c⁻¹ ++ u).IsReduced := by
  rw [isReduced_append_iff, isReduced_inv_append_iff]
  by_cases h : 0 < u.length ∧ 0 < c.length ∧
      c.letter (Order.succ 0) = (u.letter u.length).map (Prod.map id not)
  · exact .inr ⟨hc, hu.isReduced, fun _ _ h' => hu.letter_succ_zero_ne h.1 (h'.trans h.2.2)⟩
  · exact .inl ⟨hu.isReduced, hc, fun h₁ h₂ h₃ => h ⟨h₁, h₂, h₃⟩⟩

private theorem IsCyclicallyReduced.isReduced_npow (hu : u.IsCyclicallyReduced) (n : ℕ) :
    (u.npow n).IsReduced := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [npow_succ]
    refine isReduced_append_iff.2 ⟨ih, hu.isReduced, fun hn hu0 => ?_⟩
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 :=
      Nat.exists_eq_succ_of_ne_zero (by rintro rfl; simp at hn)
    rw [npow_succ, length_append, letter_append_length_add _ _ hu0]
    exact hu.letter_succ_zero_ne hu0

/-- The powers of a cyclically reduced word are cyclically reduced. -/
theorem IsCyclicallyReduced.npow (hu : u.IsCyclicallyReduced) (n : ℕ) :
    (u.npow n).IsCyclicallyReduced := by
  rw [isCyclicallyReduced_iff_isReduced_append_self, ← npow_add]
  exact hu.isReduced_npow _

/-- For a cyclically reduced word `u`, `uᵐ ∗ uⁿ = uᵐ⁺ⁿ`. -/
theorem IsCyclicallyReduced.isMul_npow (hu : u.IsCyclicallyReduced) (m n : ℕ) :
    IsMul (u.npow m) (u.npow n) (u.npow (m + n)) := by
  rw [npow_add]
  exact isMul_append (npow_add u m n ▸ hu.isReduced_npow (m + n))

/-! ### Cyclic decompositions and `CDR(Λ, X)` -/

/-- `IsCyclicDecomposition w c v` means that `w` is the reduced concatenation `c⁻¹ ++ v ++ c` with
`v` cyclically reduced. When `v` is empty, reducedness of `c⁻¹ ++ c` forces `c` and `w` to be empty
as well. -/
def IsCyclicDecomposition (w c v : InfWord Λ X) : Prop :=
  v.IsCyclicallyReduced ∧ w.IsReduced ∧ w = c⁻¹ ++ v ++ c

theorem isCyclicDecomposition_iff :
    IsCyclicDecomposition w c v ↔ v.IsCyclicallyReduced ∧ w.IsReduced ∧ w = c⁻¹ ++ v ++ c :=
  Iff.rfl

@[grind →]
theorem IsCyclicDecomposition.isCyclicallyReduced (h : IsCyclicDecomposition w c v) :
    v.IsCyclicallyReduced := h.1

@[grind →]
theorem IsCyclicDecomposition.isReduced (h : IsCyclicDecomposition w c v) : w.IsReduced := h.2.1

theorem IsCyclicDecomposition.eq (h : IsCyclicDecomposition w c v) : w = c⁻¹ ++ v ++ c := h.2.2

/-- In a cyclic decomposition `w = c⁻¹ ++ v ++ c`, `w` is empty if and only if its cyclically
reduced core `v` is empty. -/
theorem IsCyclicDecomposition.eq_empty_iff (h : IsCyclicDecomposition w c v) :
    w = empty Λ X ↔ v = empty Λ X := by
  refine ⟨fun hw => ?_, fun hv => ?_⟩
  · exact (append_eq_empty_iff.1 (append_eq_empty_iff.1 (h.eq.symm.trans hw)).1).2
  · have hred : (c⁻¹ ++ c).IsReduced := by simpa [h.eq, hv] using h.isReduced
    have hc : c = empty Λ X := isReduced_inv_append_self_iff.1 hred
    simp [h.eq, hv, hc]

@[simp]
theorem isCyclicDecomposition_empty_iff :
    IsCyclicDecomposition (empty Λ X) c v ↔ c = empty Λ X ∧ v = empty Λ X := by
  refine ⟨fun h => ?_, ?_⟩
  · have h1 := append_eq_empty_iff.1 h.eq.symm
    exact ⟨h1.2, (append_eq_empty_iff.1 h1.1).2⟩
  · rintro ⟨rfl, rfl⟩
    exact ⟨isCyclicallyReduced_empty, isReduced_empty, by simp⟩

theorem IsCyclicDecomposition.inv (h : IsCyclicDecomposition w c v) :
    IsCyclicDecomposition w⁻¹ c v⁻¹ :=
  ⟨h.isCyclicallyReduced.inv, h.isReduced.inv, by rw [h.eq, inv_append, inv_append, inv_inv,
    append_assoc]⟩

@[simp, grind =]
theorem isCyclicDecomposition_inv_iff :
    IsCyclicDecomposition w⁻¹ c v⁻¹ ↔ IsCyclicDecomposition w c v :=
  ⟨fun h => by simpa using h.inv, IsCyclicDecomposition.inv⟩

/-- The cyclic decomposition `w = c⁻¹ ++ v ++ c` of a word is unique. -/
theorem IsCyclicDecomposition.unique (h₁ : IsCyclicDecomposition w c₁ v₁)
    (h₂ : IsCyclicDecomposition w c₂ v₂) : c₁ = c₂ ∧ v₁ = v₂ := by
  have key {c₁ v₁ c₂ v₂ d : InfWord Λ X} (h₁ : IsCyclicDecomposition w c₁ v₁)
      (hc : c₂⁻¹ = c₁⁻¹ ++ d) (hv : v₁ ++ c₁ = d ++ (v₂ ++ c₂)) : c₁ = c₂ ∧ v₁ = v₂ := by
    have hc₂ : c₂ = d⁻¹ ++ c₁ := by simpa using congrArg Inv.inv hc
    have hv₁ : v₁ = d ++ v₂ ++ d⁻¹ :=
      (append_left_inj c₁).1 (by simpa [hc₂, append_assoc] using hv)
    rcases eq_or_ne d (empty Λ X) with rfl | hd
    · exact ⟨by simpa using hc₂.symm, by simpa using hv₁⟩
    exfalso
    have hd0 : 0 < d.length := length_pos_iff.2 hd
    have hv₁0 : 0 < v₁.length := length_pos_iff.2 (by rw [hv₁]; simp [hd])
    have hfirst : v₁.letter (Order.succ 0) = d.letter (Order.succ 0) := by
      rw [hv₁, append_assoc, letter_append_of_le _ (Order.succ_le_of_lt hd0)]
    have hlast : v₁.letter v₁.length = (d.letter (Order.succ 0)).map (Prod.map id not) := by
      rw [hv₁, length_append, letter_append_length_add _ _ (by simpa using hd0), length_inv,
        letter_inv_length]
    refine h₁.isCyclicallyReduced.letter_succ_zero_ne hv₁0 ?_
    rw [hfirst, hlast, Option.map_map]
    simp [Function.comp_def, Prod.map]
  have heq : c₁⁻¹ ++ (v₁ ++ c₁) = c₂⁻¹ ++ (v₂ ++ c₂) := by
    simpa only [append_assoc] using h₁.eq.symm.trans h₂.eq
  rcases append_eq_append_iff.1 heq with ⟨d, hc, hv⟩ | ⟨d, hc, hv⟩
  · exact key h₁ hc hv
  · exact (key h₂ hc hv).imp Eq.symm Eq.symm

/-- Squaring a cyclic decomposition `w = c⁻¹ ++ v ++ c` doubles its cyclically reduced core,
yielding the cyclic decomposition `c⁻¹ ++ (v ++ v) ++ c`. -/
theorem IsCyclicDecomposition.sq (h : IsCyclicDecomposition w c v) :
    IsCyclicDecomposition (c⁻¹ ++ (v ++ v) ++ c) c (v ++ v) := by
  rcases eq_or_ne v (empty Λ X) with rfl | hv
  · obtain rfl := h.eq_empty_iff.2 rfl
    obtain ⟨rfl, -⟩ := isCyclicDecomposition_empty_iff.1 h
    simp
  have hv0 : 0 < v.length := length_pos_iff.2 hv
  have hcv : (c⁻¹ ++ v).IsReduced := (h.eq ▸ h.isReduced).left_of_append
  have hcvv : (c⁻¹ ++ v ++ v).IsReduced := by
    refine isReduced_append_iff.2 ⟨hcv, h.isCyclicallyReduced.isReduced, fun _ _ => ?_⟩
    rw [length_append, letter_append_length_add _ _ hv0]
    exact h.isCyclicallyReduced.letter_succ_zero_ne hv0
  refine ⟨h.isCyclicallyReduced.append_self, ?_, by simp [append_assoc]⟩
  rw [← append_assoc]
  refine isReduced_append_iff.2 ⟨hcvv, (h.eq ▸ h.isReduced).right_of_append, fun _ hc0 => ?_⟩
  have hjoin := (isReduced_append_iff.1 (h.eq ▸ h.isReduced)).2.2
    (length_pos_iff.2 (by simp [hv])) hc0
  rw [length_append, letter_append_length_add _ _ hv0] at hjoin
  rwa [length_append, letter_append_length_add (c⁻¹ ++ v) v hv0]

/-- For `w = c⁻¹ ++ v ++ c` in cyclic decomposition, `w ∗ w` is defined and equals
`c⁻¹ ++ (v ++ v) ++ c`. -/
theorem IsCyclicDecomposition.isMul_self (h : IsCyclicDecomposition w c v) :
    IsMul w w (c⁻¹ ++ (v ++ v) ++ c) := by
  rw [← mul_eq_some_iff, h.eq]
  have hred := h.eq ▸ h.isReduced
  have hred' : (c⁻¹ ++ (v ++ c)).IsReduced := by simpa [append_assoc] using hred
  have hsq : ((c⁻¹ ++ v) ++ (v ++ c)).IsReduced := by
    simpa [append_assoc] using h.sq.isReduced
  nth_rw 2 [append_assoc]
  rw [append_mul_inv_append_cancel hred hred', mul_eq_some_append hsq]
  simp [append_assoc]

/-- For `w = c⁻¹ ++ v ++ c` in cyclic decomposition,
`w.mul w = Part.some (c⁻¹ ++ (v ++ v) ++ c)`. -/
theorem IsCyclicDecomposition.mul_self (h : IsCyclicDecomposition w c v) :
    w.mul w = Part.some (c⁻¹ ++ (v ++ v) ++ c) :=
  mul_eq_some_iff.2 h.isMul_self

variable (Λ X) in
/-- `CDR(Λ, X)`, the set of reduced `Λ`-words admitting a cyclic decomposition `c⁻¹ ++ v ++ c`
with `v` cyclically reduced. -/
def CDR : Set (InfWord Λ X) :=
  {w | ∃ c v, IsCyclicDecomposition w c v}

theorem mem_CDR_iff : w ∈ CDR Λ X ↔ ∃ c v, IsCyclicDecomposition w c v :=
  Iff.rfl

@[grind →]
theorem IsCyclicDecomposition.mem_CDR (h : IsCyclicDecomposition w c v) : w ∈ CDR Λ X :=
  ⟨c, v, h⟩

@[grind →]
theorem isReduced_of_mem_CDR (h : w ∈ CDR Λ X) : w.IsReduced :=
  let ⟨_, _, hd⟩ := h; hd.isReduced

@[simp]
theorem empty_mem_CDR : empty Λ X ∈ CDR Λ X :=
  ⟨empty Λ X, empty Λ X, isCyclicDecomposition_empty_iff.2 ⟨rfl, rfl⟩⟩

@[grind →]
theorem IsCyclicallyReduced.mem_CDR (h : w.IsCyclicallyReduced) : w ∈ CDR Λ X :=
  ⟨empty Λ X, w, h, h.isReduced, by simp⟩

@[simp]
theorem ofFun_const_mem_CDR (α : Λ) (x : X × Bool) : ofFun α (fun _ => x) ∈ CDR Λ X :=
  (isCyclicallyReduced_ofFun_const α x).mem_CDR

@[simp, grind =]
theorem inv_mem_CDR : w⁻¹ ∈ CDR Λ X ↔ w ∈ CDR Λ X :=
  ⟨fun ⟨c, v, h⟩ => by simpa using h.inv.mem_CDR, fun ⟨c, v, h⟩ => h.inv.mem_CDR⟩

/-- Every word in `CDR(Λ, X)` has a defined square `w ∗ w` under the partial multiplication. -/
theorem mul_self_dom_of_mem_CDR (h : w ∈ CDR Λ X) : (w.mul w).Dom := by
  obtain ⟨c, v, hd⟩ := h
  exact mul_dom_iff.2 ⟨_, hd.isMul_self⟩

/-- Squaring strictly increases the length of every nonempty word in `CDR(Λ, X)`. -/
theorem length_lt_length_of_mem_CDR_of_isMul_self (hw : w ∈ CDR Λ X) (hne : w ≠ empty Λ X)
    (hm : IsMul w w u) : w.length < u.length := by
  obtain ⟨c, v, hd⟩ := hw
  obtain rfl := hd.isMul_self.unique hm
  have hv0 : 0 < v.length := length_pos_iff.2 (mt hd.eq_empty_iff.2 hne)
  rw [hd.eq]
  simp only [length_append, length_inv]
  grind

/-- If `u ++ r = r ++ m` for a cyclically reduced `u` and a reduced `r ++ m`, then `m` is
cyclically reduced. -/
private theorem IsCyclicallyReduced.of_append_eq_append {r m : InfWord Λ X}
    (hu : u.IsCyclicallyReduced) (hred : (r ++ m).IsReduced) (h : u ++ r = r ++ m) :
    m.IsCyclicallyReduced := by
  have hmu : m.length = u.length := by
    have := congrArg length h
    grind
  refine ⟨hred.right_of_append, fun hm0 => ?_⟩
  rcases eq_or_ne r (empty Λ X) with rfl | hr
  · simp only [append_empty, empty_append] at h
    exact (h ▸ hu).letter_succ_zero_ne hm0
  have hr0 : 0 < r.length := length_pos_iff.2 hr
  have hlast : m.letter m.length = r.letter r.length := by
    have := congrArg (letter · (r.length + u.length)) h
    rw [add_comm, letter_append_length_add _ _ hr0, add_comm, ← hmu,
      letter_append_length_add _ _ hm0] at this
    exact this.symm
  rw [hlast]
  exact hred.letter_succ_zero_ne_of_append hr0 hm0

/-- The conjugate `c⁻¹ ∗ (u ∘ c)` of a cyclically reduced word `u`, when it is defined, lies in
`CDR(Λ, X)`. -/
private theorem mem_CDR_of_isMul_inv_append (hu : u.IsCyclicallyReduced)
    (h : IsMul c⁻¹ (u ++ c) v) : v ∈ CDR Λ X := by
  obtain ⟨-, hred, a, b, r, hca, hw, rfl, hv⟩ := isMul_iff.1 h
  obtain rfl : c = r ++ a⁻¹ := by rw [← inv_inv c, hca, inv_append, inv_inv]
  have hdrop : b.drop u.length = a⁻¹ := by
    have := congrArg (drop · (r.length + u.length)) hw
    rwa [drop_append_length_add _ _ u.length_nonneg, ← append_assoc, add_comm, ← length_append,
      drop_append_length, eq_comm] at this
  obtain ⟨m, hm⟩ : ∃ m, b.take u.length = m := ⟨_, rfl⟩
  obtain rfl : b = m ++ a⁻¹ := by rw [← hdrop, ← hm, take_append_drop]
  rw [hw, ← append_assoc] at hred
  rw [← append_assoc, ← append_assoc, append_left_inj] at hw
  exact ⟨a⁻¹, m, hu.of_append_eq_append hred.left_of_append hw, hv, by simp [append_assoc]⟩

/-- A conjugate of a word of `CDR(Λ, X)` lies in `CDR(Λ, X)`: if `u ∈ CDR(Λ, X)` and the products
`c⁻¹ ∗ u = x` and `x ∗ c = v` are defined, then `v ∈ CDR(Λ, X)`. The product `u ∗ c` need not be
defined. -/
theorem mem_CDR_of_isMul_conj {x : InfWord Λ X} (hu : u ∈ CDR Λ X) (h₁ : IsMul c⁻¹ u x)
    (h₂ : IsMul x c v) : v ∈ CDR Λ X := by
  obtain ⟨e, w, hd⟩ := hu
  have hu' := hd.isReduced
  rw [hd.eq, append_assoc] at hu' h₁
  -- `c⁻¹ ∗ e⁻¹ = d⁻¹`, that is `e ∗ c = d`, is defined
  obtain ⟨d, hcd⟩ : ∃ d, IsMul c⁻¹ e⁻¹ d⁻¹ := by
    obtain ⟨d', hd'⟩ := h₁.exists_isMul_take e⁻¹.length
    rw [take_append_length] at hd'
    exact ⟨d'⁻¹, by rwa [inv_inv]⟩
  have hec : IsMul e c d := by simpa using hcd.inv
  have hwe : IsMul w e (w ++ e) := isMul_append hu'.right_of_append
  have hx : IsMul d⁻¹ (w ++ e) x := hcd.assoc_right (isMul_append hu') h₁
  rcases hd.isCyclicallyReduced.isReduced_append_or_isReduced_inv_append hec.isReduced with h | h
  · have h₃ : IsMul (w ++ e) c (w ++ d) := (hwe.assoc_iff hec).2 (isMul_append h)
    exact mem_CDR_of_isMul_inv_append hd.isCyclicallyReduced ((hx.assoc_iff h₃).1 h₂)
  · have h₃ : IsMul (d⁻¹ ++ w) e x := ((isMul_append h).assoc_iff hwe).2 hx
    rw [← inv_mem_CDR]
    refine mem_CDR_of_isMul_inv_append (c := d) hd.isCyclicallyReduced.inv ?_
    simpa using ((h₃.assoc_iff hec).1 h₂).inv

/-! ### Word length as a free Lyndon length function -/

section LyndonLength

variable {G : Type*} [Group G]

/-- If `f : G → InfWord Λ X` turns multiplication in `G` into the partial product `∗` of reduced
`Λ`-words, then `g ↦ |f g|` is a `Λ`-valued Lyndon length function on `G`. -/
def lyndonLengthOfIsMul (f : G → InfWord Λ X)
    (hf : ∀ g k, IsMul (f g) (f k) (f (g * k))) : LyndonLength G Λ where
  toFun g := (f g).length
  map_one' := by simp [map_one_of_forall_isMul hf]
  map_inv' g := by simp [map_inv_of_forall_isMul hf g]
  eq_of_lt' g k h := by
    have key (a b : G) :
        ∃ δ, IsGreatest {β | 0 ≤ β ∧ β ≤ (f a).length ∧ β ≤ (f b).length ∧
          (f a).take β = (f b).take β} δ ∧
          (f (a⁻¹ * b)).length + 2 • δ = (f a).length + (f b).length := by
      have hmul : IsMul (f a)⁻¹ (f b) (f (a⁻¹ * b)) := by
        simpa [map_inv_of_forall_isMul hf a] using hf a⁻¹ b
      obtain ⟨δ, hδ⟩ := exists_isGreatest_of_isMul_inv_left hmul
      exact ⟨δ, hδ, length_add_two_nsmul_eq_of_isMul_inv_left hmul hδ⟩
    obtain ⟨δ_gk, hgk, egk⟩ := key g k
    obtain ⟨δ_gh, hgh, egh⟩ := key g h
    obtain ⟨δ_kh, hkh, ekh⟩ := key k h
    have hgk_symm : IsGreatest {β | 0 ≤ β ∧ β ≤ (f k).length ∧ β ≤ (f g).length ∧
        (f k).take β = (f g).take β} δ_gk :=
      ⟨⟨hgk.1.1, hgk.1.2.2.1, hgk.1.2.1, hgk.1.2.2.2.symm⟩,
        fun β ⟨h0, h1, h2, h3⟩ => hgk.2 ⟨h0, h2, h1, h3.symm⟩⟩
    have u1 := min_le_of_isGreatest_common_prefix hgk_symm hgh hkh
    have u2 := min_le_of_isGreatest_common_prefix hgk hkh hgh
    intro hlt
    have hδlt : δ_gh < δ_gk := by grind [two_nsmul]
    have hδeq : δ_gh = δ_kh := le_antisymm (by grind) (by grind)
    grind [two_nsmul]

@[simp]
theorem lyndonLengthOfIsMul_apply (f : G → InfWord Λ X)
    (hf : ∀ g k, IsMul (f g) (f k) (f (g * k))) (g : G) :
    lyndonLengthOfIsMul f hf g = (f g).length := (rfl)

/-- If `δ` is the length of the longest common initial segment of `f g` and `f k`, then the Gromov
product of `g` and `k` for `lyndonLengthOfIsMul f hf` is `δ`. -/
theorem gromovProduct_lyndonLengthOfIsMul_eq_of_isGreatest {f : G → InfWord Λ X}
    (hf : ∀ g k, IsMul (f g) (f k) (f (g * k))) {g k : G} {δ : Λ}
    (hδ : IsGreatest {β | 0 ≤ β ∧ β ≤ (f g).length ∧ β ≤ (f k).length ∧
      (f g).take β = (f k).take β} δ) :
    (lyndonLengthOfIsMul f hf).gromovProduct g k = (δ : DivisibleHull Λ) := by
  have hmul : IsMul (f g)⁻¹ (f k) (f (g⁻¹ * k)) := by
    simpa [map_inv_of_forall_isMul hf g] using hf g⁻¹ k
  have hlen := length_add_two_nsmul_eq_of_isMul_inv_left hmul hδ
  exact ((LyndonLength.coe_eq_gromovProduct_iff _).2
    (by simp only [lyndonLengthOfIsMul_apply]; grind)).symm

/-- For any `f : G → InfWord Λ X` turning multiplication into `∗`, the common initial segments of
`f g` and `f k` have a longest element of length `δ`, and `δ` is their Gromov product for
`lyndonLengthOfIsMul f hf`. -/
theorem exists_isGreatest_and_coe_eq_gromovProduct_lyndonLengthOfIsMul (f : G → InfWord Λ X)
    (hf : ∀ g k, IsMul (f g) (f k) (f (g * k))) (g k : G) :
    ∃ δ : Λ, IsGreatest {β | 0 ≤ β ∧ β ≤ (f g).length ∧ β ≤ (f k).length ∧
      (f g).take β = (f k).take β} δ ∧
      (δ : DivisibleHull Λ) = (lyndonLengthOfIsMul f hf).gromovProduct g k := by
  have hmul : IsMul (f g)⁻¹ (f k) (f (g⁻¹ * k)) := by
    simpa [map_inv_of_forall_isMul hf g] using hf g⁻¹ k
  obtain ⟨δ, hδ⟩ := exists_isGreatest_of_isMul_inv_left hmul
  exact ⟨δ, hδ, (gromovProduct_lyndonLengthOfIsMul_eq_of_isGreatest hf hδ).symm⟩

/-- Every Gromov product of `lyndonLengthOfIsMul f hf` lies in `Λ`. -/
theorem exists_coe_eq_gromovProduct_lyndonLengthOfIsMul (f : G → InfWord Λ X)
    (hf : ∀ g k, IsMul (f g) (f k) (f (g * k))) (g k : G) :
    ∃ c : Λ, (c : DivisibleHull Λ) = (lyndonLengthOfIsMul f hf).gromovProduct g k :=
  let ⟨δ, _, hδ⟩ := exists_isGreatest_and_coe_eq_gromovProduct_lyndonLengthOfIsMul f hf g k
  ⟨δ, hδ⟩

/-- If an injective map `f : G → InfWord Λ X` turns multiplication into `∗` and lands in
`CDR(Λ, X)`, then `g ↦ |f g|` is a free Lyndon length function on `G`. -/
theorem isFree_lyndonLengthOfIsMul {f : G → InfWord Λ X}
    (hf : ∀ g k, IsMul (f g) (f k) (f (g * k))) (hinj : Function.Injective f)
    (hCDR : ∀ g, f g ∈ CDR Λ X) : (lyndonLengthOfIsMul f hf).IsFree where
  exists_coe_eq_gromovProduct := exists_coe_eq_gromovProduct_lyndonLengthOfIsMul f hf
  lt_map_sq g hg := by
    have hne : f g ≠ empty Λ X := by
      rw [← map_one_of_forall_isMul hf]
      exact hinj.ne hg
    have hsq : IsMul (f g) (f g) (f (g ^ 2)) := by simpa [sq] using hf g g
    simpa only [lyndonLengthOfIsMul_apply] using
      length_lt_length_of_mem_CDR_of_isMul_self (hCDR g) hne hsq

/-- Word length `w ↦ |w|` on a subgroup `H` of reduced `Λ`-words as a `Λ`-valued Lyndon length
function. -/
noncomputable def ReducedSubgroup.lyndonLength (H : ReducedSubgroup Λ X) : LyndonLength H Λ :=
  lyndonLengthOfIsMul Subtype.val H.isMul_coe_mul

@[simp]
theorem ReducedSubgroup.lyndonLength_apply (H : ReducedSubgroup Λ X) (u : H) :
    H.lyndonLength u = (u : InfWord Λ X).length := (rfl)

/-- Restricting word length along the inclusion `H ≤ K` of subgroups of reduced words yields word
length on `H`. -/
@[simp]
theorem ReducedSubgroup.comap_lyndonLength_inclusion {H K : ReducedSubgroup Λ X} (h : H ≤ K) :
    K.lyndonLength.comap (inclusion h) = H.lyndonLength := by
  ext u
  simp

/-- In a subgroup `H` of reduced words, if `δ` is the length of the longest common initial segment
of `u` and `v`, then their Gromov product for `H.lyndonLength` is `δ`. -/
theorem ReducedSubgroup.gromovProduct_lyndonLength_eq_of_isGreatest
    {H : ReducedSubgroup Λ X} {u v : H} {δ : Λ}
    (hδ : IsGreatest {β | 0 ≤ β ∧ β ≤ (u : InfWord Λ X).length ∧
      β ≤ (v : InfWord Λ X).length ∧
      (u : InfWord Λ X).take β = (v : InfWord Λ X).take β} δ) :
    H.lyndonLength.gromovProduct u v = (δ : DivisibleHull Λ) :=
  gromovProduct_lyndonLengthOfIsMul_eq_of_isGreatest H.isMul_coe_mul hδ

/-- For any `u, v` in a subgroup `H` of reduced words, their common initial segments have a longest
element of length `δ`, and `δ` is their Gromov product for `H.lyndonLength`. -/
theorem ReducedSubgroup.exists_isGreatest_and_coe_eq_gromovProduct_lyndonLength
    (H : ReducedSubgroup Λ X) (u v : H) :
    ∃ δ : Λ, IsGreatest {β | 0 ≤ β ∧ β ≤ (u : InfWord Λ X).length ∧
      β ≤ (v : InfWord Λ X).length ∧
      (u : InfWord Λ X).take β = (v : InfWord Λ X).take β} δ ∧
      (δ : DivisibleHull Λ) = H.lyndonLength.gromovProduct u v :=
  exists_isGreatest_and_coe_eq_gromovProduct_lyndonLengthOfIsMul Subtype.val H.isMul_coe_mul u v

/-- On any subgroup of `CDR(Λ, X)`, word length `w ↦ |w|` is a free Lyndon length function. -/
theorem ReducedSubgroup.isFree_lyndonLength {H : ReducedSubgroup Λ X}
    (hH : (H : Set (InfWord Λ X)) ⊆ CDR Λ X) : H.lyndonLength.IsFree :=
  isFree_lyndonLengthOfIsMul H.isMul_coe_mul Subtype.val_injective fun u => hH u.property

end LyndonLength

end Discrete

end InfWord

end TauCeti
