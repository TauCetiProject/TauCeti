/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.GroupAction.OrbitRelQuotient
public import TauCeti.GroupTheory.BranchTuple.Basic
public import TauCeti.GroupTheory.SpecificGroups.Braid.Basic
import Mathlib.Tactic.Group
import TauCeti.Data.List.ProdOfFn

/-!
# The Hurwitz action of the braid group on branch tuples

Moving two adjacent branch points of a cover of the line around each other changes its branch
tuple by a *Hurwitz move*. The `i`-th positive move replaces the adjacent entries
`(a, b) = (t i, t (i + 1))` by `(a * b * a⁻¹, a)` and leaves the other entries alone; its inverse
replaces `(a, b)` by `(b, b⁻¹ * a * b)`. The moves satisfy the relations of the Artin braid group,
so they define the Hurwitz action `TauCeti.BraidGroup r →* Equiv.Perm (BranchTuple r G)`, in which
the elementary braid `σ i` acts by the `i`-th move.

The Hurwitz action preserves the ordered product exactly (not merely up to conjugacy), the
generated subgroup exactly, and the multiset of conjugacy classes of the entries. More precisely,
a braid `b` moves the class of the entry at position `j` to position `permHom r b j`, so the
ordered list of classes is preserved by pure braids but permuted by the elementary braids. The
moves commute with homomorphisms applied entrywise, so the action descends to Nielsen classes
relative to any group of automorphisms.

## Main definitions

* `TauCeti.BranchTuple.hurwitzMove i`: the `i`-th positive Hurwitz move, as a permutation of
  branch tuples.
* `TauCeti.BranchTuple.hurwitzAction`: the Hurwitz action of the braid group on branch tuples.
* `TauCeti.NielsenClass.hurwitzAction`: the induced action on Nielsen classes.

## Main results

* `TauCeti.BranchTuple.hurwitzMove_mul_hurwitzMove_comm` and
  `TauCeti.BranchTuple.hurwitzMove_braid`: the moves satisfy the braid relations.
* `TauCeti.BranchTuple.hurwitzAction_sigma`: `σ i` acts by the `i`-th move.
* `TauCeti.BranchTuple.apply_hurwitzAction_of_apply_hurwitzMove` and
  `TauCeti.BranchTuple.apply_hurwitzAction_eq_of_invariant`: to show that a map out of branch
  tuples is equivariant for, or invariant under, the Hurwitz action, it suffices to check single
  Hurwitz moves.
* `TauCeti.BranchTuple.product_hurwitzAction`, `TauCeti.BranchTuple.generated_hurwitzAction` and
  `TauCeti.BranchTuple.classMultiset_hurwitzAction`: the invariants of the action.
* `TauCeti.BranchTuple.isConj_hurwitzAction_apply`: the entry of `b • t` at position `k` is
  conjugate to the entry of `t` at position `(permHom r b)⁻¹ k`; in particular pure braids
  preserve ordered class conditions
  (`TauCeti.BranchTuple.isConj_hurwitzAction_apply_of_mem_pureSubgroup`).
* `TauCeti.BranchTuple.hurwitzAction_comp`: the action commutes with homomorphisms applied
  entrywise.

## References

* M. M. Wood, *An algebraic lifting invariant of Ellenberg, Venkatesh, and Westerland*, Res.
  Math. Sci. 8 (2021), §3.
* J. S. Ellenberg, A. Venkatesh, C. Westerland, *Homological stability for Hurwitz spaces and the
  Cohen-Lenstra conjecture over function fields*, Ann. of Math. 183 (2016), §§2.1–2.2.
* H. Völklein, *Groups as Galois groups*, Cambridge Stud. Adv. Math. 53 (1996), Chapter 9.
-/

public section

namespace TauCeti

namespace BranchTuple

open BraidGroup Function

variable {G H : Type*} [Group G] [Group H] {r : ℕ}

/-! ### Hurwitz moves -/

/-- The `i`-th positive Hurwitz move: the adjacent entries `(a, b)` at positions `i` and `i + 1`
are replaced by `(a * b * a⁻¹, a)`, the other entries are unchanged. The inverse replaces `(a, b)`
by `(b, b⁻¹ * a * b)`. -/
def hurwitzMove (i : Fin (r - 1)) : Equiv.Perm (BranchTuple r G) where
  toFun t := update (update t (strand i) (t (strand i) * t (strandSucc i) * (t (strand i))⁻¹))
    (strandSucc i) (t (strand i))
  invFun t := update (update t (strand i) (t (strandSucc i))) (strandSucc i)
    ((t (strandSucc i))⁻¹ * t (strand i) * t (strandSucc i))
  left_inv t := by
    have hne := strand_ne_strandSucc i
    funext k
    simp only [update_apply, hne, ↓reduceIte]
    split_ifs with h₁ h₂ <;> subst_vars <;> group
  right_inv t := by
    have hne := strand_ne_strandSucc i
    funext k
    simp only [update_apply, hne, ↓reduceIte]
    split_ifs with h₁ h₂ <;> subst_vars <;> group

/-- The value of a Hurwitz move at every position. -/
theorem hurwitzMove_apply (i : Fin (r - 1)) (t : BranchTuple r G) (k : Fin r) :
    hurwitzMove i t k =
      if k = strandSucc i then t (strand i)
      else if k = strand i then t (strand i) * t (strandSucc i) * (t (strand i))⁻¹ else t k := by
  simp only [hurwitzMove, Equiv.coe_fn_mk, update_apply]

/-- The value of an inverse Hurwitz move at every position. -/
theorem hurwitzMove_symm_apply (i : Fin (r - 1)) (t : BranchTuple r G) (k : Fin r) :
    (hurwitzMove i).symm t k =
      if k = strandSucc i then (t (strandSucc i))⁻¹ * t (strand i) * t (strandSucc i)
      else if k = strand i then t (strandSucc i) else t k := by
  simp only [hurwitzMove, Equiv.coe_fn_symm_mk, update_apply]

@[simp]
theorem hurwitzMove_apply_strand (i : Fin (r - 1)) (t : BranchTuple r G) :
    hurwitzMove i t (strand i) = t (strand i) * t (strandSucc i) * (t (strand i))⁻¹ := by
  simp [hurwitzMove_apply, strand_ne_strandSucc]

@[simp]
theorem hurwitzMove_apply_strandSucc (i : Fin (r - 1)) (t : BranchTuple r G) :
    hurwitzMove i t (strandSucc i) = t (strand i) := by
  simp [hurwitzMove_apply]

theorem hurwitzMove_apply_of_ne (i : Fin (r - 1)) (t : BranchTuple r G) {k : Fin r}
    (h₀ : k ≠ strand i) (h₁ : k ≠ strandSucc i) : hurwitzMove i t k = t k := by
  simp [hurwitzMove_apply, h₀, h₁]

@[simp]
theorem hurwitzMove_symm_apply_strand (i : Fin (r - 1)) (t : BranchTuple r G) :
    (hurwitzMove i).symm t (strand i) = t (strandSucc i) := by
  simp [hurwitzMove_symm_apply, strand_ne_strandSucc]

@[simp]
theorem hurwitzMove_symm_apply_strandSucc (i : Fin (r - 1)) (t : BranchTuple r G) :
    (hurwitzMove i).symm t (strandSucc i) =
      (t (strandSucc i))⁻¹ * t (strand i) * t (strandSucc i) := by
  simp [hurwitzMove_symm_apply]

theorem hurwitzMove_symm_apply_of_ne (i : Fin (r - 1)) (t : BranchTuple r G) {k : Fin r}
    (h₀ : k ≠ strand i) (h₁ : k ≠ strandSucc i) : (hurwitzMove i).symm t k = t k := by
  simp [hurwitzMove_symm_apply, h₀, h₁]

/-- Hurwitz moves at disjoint pairs of positions commute. -/
theorem hurwitzMove_mul_hurwitzMove_comm {i j : Fin (r - 1)}
    (h : (i : ℕ) + 2 ≤ j ∨ (j : ℕ) + 2 ≤ i) :
    hurwitzMove (G := G) i * hurwitzMove j = hurwitzMove j * hurwitzMove i := by
  -- Each inequality between the four strands follows from their distinctness: identifying two
  -- of them makes the list `[strand i, strandSucc i, strand j, strandSucc j]` repeat an entry.
  have hnd := nodup_strand_strandSucc_strand_strandSucc h
  have h₂ : strand i ≠ strand j := fun e ↦ by simp [e] at hnd
  have h₃ : strand i ≠ strandSucc j := fun e ↦ by simp [e] at hnd
  have h₄ : strandSucc i ≠ strand j := fun e ↦ by simp [e] at hnd
  have h₅ : strandSucc i ≠ strandSucc j := fun e ↦ by simp [e] at hnd
  have ia : ∀ u : BranchTuple r G, hurwitzMove i u (strand j) = u (strand j) :=
    fun u ↦ hurwitzMove_apply_of_ne i u (Ne.symm h₂) (Ne.symm h₄)
  have ib : ∀ u : BranchTuple r G, hurwitzMove i u (strandSucc j) = u (strandSucc j) :=
    fun u ↦ hurwitzMove_apply_of_ne i u (Ne.symm h₃) (Ne.symm h₅)
  have ja : ∀ u : BranchTuple r G, hurwitzMove j u (strand i) = u (strand i) :=
    fun u ↦ hurwitzMove_apply_of_ne j u h₂ h₃
  have jb : ∀ u : BranchTuple r G, hurwitzMove j u (strandSucc i) = u (strandSucc i) :=
    fun u ↦ hurwitzMove_apply_of_ne j u h₄ h₅
  refine Equiv.ext fun t ↦ funext fun k ↦ ?_
  simp only [Equiv.Perm.mul_apply]
  by_cases hk₁ : k = strand i
  · subst hk₁
    simp only [hurwitzMove_apply_strand, ja, jb]
  by_cases hk₂ : k = strandSucc i
  · subst hk₂
    simp only [hurwitzMove_apply_strandSucc, ja, jb]
  by_cases hk₃ : k = strand j
  · subst hk₃
    simp only [hurwitzMove_apply_strand, ia, ib]
  by_cases hk₄ : k = strandSucc j
  · subst hk₄
    simp only [hurwitzMove_apply_strandSucc, ia, ib]
  have hi : ∀ u : BranchTuple r G, hurwitzMove i u k = u k :=
    fun u ↦ hurwitzMove_apply_of_ne i u hk₁ hk₂
  have hj : ∀ u : BranchTuple r G, hurwitzMove j u k = u k :=
    fun u ↦ hurwitzMove_apply_of_ne j u hk₃ hk₄
  simp only [hi, hj]

/-- Hurwitz moves at overlapping pairs of positions satisfy the braid relation. -/
theorem hurwitzMove_braid {i j : Fin (r - 1)} (h : (i : ℕ) + 1 = j ∨ (j : ℕ) + 1 = i) :
    hurwitzMove (G := G) i * hurwitzMove j * hurwitzMove i =
      hurwitzMove j * hurwitzMove i * hurwitzMove j := by
  suffices hforward : ∀ {i j : Fin (r - 1)}, (i : ℕ) + 1 = j →
      hurwitzMove (G := G) i * hurwitzMove j * hurwitzMove i =
        hurwitzMove j * hurwitzMove i * hurwitzMove j by
    rcases h with h | h
    · exact hforward h
    · exact (hforward h).symm
  intro i j h
  -- The three positions involved are `strand i`, `strandSucc i = strand j` and `strandSucc j`.
  have hji := strand_eq_strandSucc_of_succ h
  have hab := strand_ne_strandSucc i
  have hac := strand_ne_strandSucc_of_succ h
  have hbc : strandSucc i ≠ strandSucc j := hji ▸ strand_ne_strandSucc j
  have ja : ∀ u : BranchTuple r G, hurwitzMove j u (strand i) = u (strand i) :=
    fun u ↦ hurwitzMove_apply_of_ne j u (hji ▸ hab) hac
  have jb : ∀ u : BranchTuple r G, hurwitzMove j u (strandSucc i) =
      u (strandSucc i) * u (strandSucc j) * (u (strandSucc i))⁻¹ := fun u ↦ by
    rw [← hji]
    exact hurwitzMove_apply_strand j u
  have jc : ∀ u : BranchTuple r G, hurwitzMove j u (strandSucc j) = u (strandSucc i) :=
    fun u ↦ by
      rw [← hji]
      exact hurwitzMove_apply_strandSucc j u
  have ic : ∀ u : BranchTuple r G, hurwitzMove i u (strandSucc j) = u (strandSucc j) :=
    fun u ↦ hurwitzMove_apply_of_ne i u (Ne.symm hac) (Ne.symm hbc)
  refine Equiv.ext fun t ↦ funext fun k ↦ ?_
  simp only [Equiv.Perm.mul_apply]
  by_cases hka : k = strand i
  · subst hka
    simp only [hurwitzMove_apply_strand, hurwitzMove_apply_strandSucc, ja, jb, ic]
    simp [mul_assoc]
  by_cases hkb : k = strandSucc i
  · subst hkb
    simp only [hurwitzMove_apply_strand, hurwitzMove_apply_strandSucc, ja, jb, ic]
    simp [mul_assoc, hji]
  by_cases hkc : k = strandSucc j
  · subst hkc
    simp only [hurwitzMove_apply_strandSucc, ja, jc, ic]
  have hkb' : k ≠ strand j := hji ▸ hkb
  have hi : ∀ u : BranchTuple r G, hurwitzMove i u k = u k :=
    fun u ↦ hurwitzMove_apply_of_ne i u hka hkb
  have hj : ∀ u : BranchTuple r G, hurwitzMove j u k = u k :=
    fun u ↦ hurwitzMove_apply_of_ne j u hkb' hkc
  simp only [hi, hj]

/-! ### The Hurwitz action -/

/-- The Hurwitz action of the braid group on branch tuples of length `r`, a left action in which
the elementary braid `σ i` acts by the `i`-th positive Hurwitz move. -/
def hurwitzAction : BraidGroup r →* Equiv.Perm (BranchTuple r G) :=
  BraidGroup.lift hurwitzMove hurwitzMove_mul_hurwitzMove_comm hurwitzMove_braid

/-- The elementary braid `σ i` acts by the `i`-th positive Hurwitz move. -/
@[simp]
theorem hurwitzAction_sigma (i : Fin (r - 1)) :
    hurwitzAction (sigma i) = hurwitzMove (G := G) i := by
  rw [hurwitzAction, lift_sigma]

/-- A map out of branch tuples intertwining each Hurwitz move with the action of the corresponding
elementary braid through `ρ` intertwines the whole Hurwitz action with `ρ`. -/
theorem apply_hurwitzAction_of_apply_hurwitzMove {X : Type*} (ρ : BraidGroup r →* Equiv.Perm X)
    {F : BranchTuple r G → X} (h : ∀ i t, F (hurwitzMove i t) = ρ (sigma i) (F t))
    (b : BraidGroup r) (t : BranchTuple r G) : F (hurwitzAction b t) = ρ b (F t) := by
  induction b using sigma_induction_on generalizing t with
  | sigma i => rw [hurwitzAction_sigma, h]
  | one => simp
  | mul b b' hb hb' => simp only [map_mul, Equiv.Perm.mul_apply, hb, hb']
  | inv b hb =>
    rw [map_inv, map_inv, Equiv.Perm.inv_def, Equiv.Perm.inv_def, Equiv.eq_symm_apply, ← hb,
      Equiv.apply_symm_apply]

/-- A function of branch tuples invariant under every Hurwitz move is invariant under the Hurwitz
action. -/
theorem apply_hurwitzAction_eq_of_invariant {X : Type*} {F : BranchTuple r G → X}
    (h : ∀ i t, F (hurwitzMove i t) = F t) (b : BraidGroup r) (t : BranchTuple r G) :
    F (hurwitzAction b t) = F t := by
  simpa using apply_hurwitzAction_of_apply_hurwitzMove 1 (by simpa using h) b t

/-! ### Invariants of the Hurwitz action -/

private theorem take_ofFn_hurwitzMove (i : Fin (r - 1)) (t : BranchTuple r G) :
    (List.ofFn (hurwitzMove i t)).take (strand i) = (List.ofFn t).take (strand i) := by
  refine List.ext_getElem (by simp) fun n h₁ _ ↦ ?_
  simp only [List.getElem_take, List.getElem_ofFn]
  simp only [List.length_take, List.length_ofFn, val_strand, lt_min_iff] at h₁
  exact hurwitzMove_apply_of_ne i t (by simp [Fin.ext_iff]; omega) (by simp [Fin.ext_iff]; omega)

private theorem drop_ofFn_hurwitzMove (i : Fin (r - 1)) (t : BranchTuple r G) :
    (List.ofFn (hurwitzMove i t)).drop (strandSucc i + 1) =
      (List.ofFn t).drop (strandSucc i + 1) := by
  refine List.ext_getElem (by simp) fun n _ _ ↦ ?_
  simp only [List.getElem_drop, List.getElem_ofFn]
  exact hurwitzMove_apply_of_ne i t (by simp [Fin.ext_iff]; omega) (by simp [Fin.ext_iff]; omega)

/-- A Hurwitz move preserves the ordered product. -/
@[simp]
theorem product_hurwitzMove (i : Fin (r - 1)) (t : BranchTuple r G) :
    product (hurwitzMove i t) = product t := by
  have hi : (strand i : ℕ) + 1 = strandSucc i := by simp
  rw [product_def, product_def, List.prod_ofFn_eq_take_mul_mul_drop _ hi,
    List.prod_ofFn_eq_take_mul_mul_drop t hi, take_ofFn_hurwitzMove, drop_ofFn_hurwitzMove,
    hurwitzMove_apply_strand, hurwitzMove_apply_strandSucc]
  group

/-- A Hurwitz move preserves the generated subgroup. -/
@[simp]
theorem generated_hurwitzMove (i : Fin (r - 1)) (t : BranchTuple r G) :
    generated (hurwitzMove i t) = generated t := by
  refine le_antisymm (generated_le_iff.mpr fun k ↦ ?_) (generated_le_iff.mpr fun k ↦ ?_)
  · rw [hurwitzMove_apply]
    split_ifs
    · exact apply_mem_generated t _
    · exact mul_mem (mul_mem (apply_mem_generated t _) (apply_mem_generated t _))
        (inv_mem (apply_mem_generated t _))
    · exact apply_mem_generated t _
  · set u := hurwitzMove i t
    rw [show t = (hurwitzMove i).symm u by simp [u], hurwitzMove_symm_apply]
    split_ifs
    · exact mul_mem (mul_mem (inv_mem (apply_mem_generated u _)) (apply_mem_generated u _))
        (apply_mem_generated u _)
    · exact apply_mem_generated u _
    · exact apply_mem_generated u _

/-- The entry of a Hurwitz move at position `k` is conjugate to the entry of the original tuple at
the position exchanged with `k` by the underlying transposition. -/
theorem isConj_hurwitzMove_apply (i : Fin (r - 1)) (t : BranchTuple r G) (k : Fin r) :
    IsConj (t (transposition i k)) (hurwitzMove i t k) := by
  by_cases h₁ : k = strandSucc i
  · subst h₁
    rw [transposition_apply_strandSucc, hurwitzMove_apply_strandSucc]
  by_cases h₀ : k = strand i
  · subst h₀
    rw [transposition_apply_strand, hurwitzMove_apply_strand]
    exact isConj_iff.mpr ⟨t (strand i), rfl⟩
  rw [hurwitzMove_apply_of_ne i t h₀ h₁, transposition_eq_swap,
    Equiv.swap_apply_of_ne_of_ne h₀ h₁]

/-- The Hurwitz action preserves the ordered product exactly. -/
@[simp]
theorem product_hurwitzAction (b : BraidGroup r) (t : BranchTuple r G) :
    product (hurwitzAction b t) = product t :=
  apply_hurwitzAction_eq_of_invariant product_hurwitzMove b t

/-- The Hurwitz action preserves the generated subgroup exactly. -/
@[simp]
theorem generated_hurwitzAction (b : BraidGroup r) (t : BranchTuple r G) :
    generated (hurwitzAction b t) = generated t :=
  apply_hurwitzAction_eq_of_invariant generated_hurwitzMove b t

/-- Under the Hurwitz action of a braid `b`, the entry at position `k` is conjugate to the entry of
the original tuple at position `(permHom r b)⁻¹ k`: the conjugacy classes of the entries travel
with the strands of `b`. -/
theorem isConj_hurwitzAction_apply (b : BraidGroup r) (t : BranchTuple r G) (k : Fin r) :
    IsConj (t ((permHom r b)⁻¹ k)) (hurwitzAction b t k) := by
  induction b using sigma_induction_on generalizing t k with
  | sigma i =>
    rw [hurwitzAction_sigma, permHom_sigma, transposition_eq_swap, Equiv.swap_inv,
      ← transposition_eq_swap]
    exact isConj_hurwitzMove_apply i t k
  | one =>
    simp only [map_one, inv_one, Equiv.Perm.one_apply]
    exact IsConj.refl _
  | mul b b' hb hb' =>
    rw [map_mul, map_mul, mul_inv_rev, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]
    exact (hb' t _).trans (hb _ k)
  | inv b hb =>
    have h := hb ((hurwitzAction b)⁻¹ t) (permHom r b k)
    simp only [Equiv.Perm.inv_def, Equiv.symm_apply_apply, Equiv.apply_symm_apply] at h
    rw [map_inv, map_inv, inv_inv, Equiv.Perm.inv_def]
    exact h.symm

/-- A pure braid preserves the conjugacy class of each entry, so it preserves ordered class
conditions; the elementary braids, which are not pure, exchange the classes of two entries. -/
theorem isConj_hurwitzAction_apply_of_mem_pureSubgroup {b : BraidGroup r}
    (hb : b ∈ pureSubgroup r) (t : BranchTuple r G) (k : Fin r) :
    IsConj (t k) (hurwitzAction b t k) := by
  simpa [mem_pureSubgroup.mp hb] using isConj_hurwitzAction_apply b t k

/-- The Hurwitz action preserves the multiset of conjugacy classes of the entries. -/
@[simp]
theorem classMultiset_hurwitzAction (b : BraidGroup r) (t : BranchTuple r G) :
    classMultiset (hurwitzAction b t) = classMultiset t :=
  classMultiset_eq_of_isConj (permHom r b)⁻¹ (isConj_hurwitzAction_apply b t)

/-! ### Equivariance -/

/-- Hurwitz moves commute with homomorphisms applied entrywise. -/
theorem hurwitzMove_comp (f : G →* H) (i : Fin (r - 1)) (t : BranchTuple r G) :
    hurwitzMove i (f ∘ t) = f ∘ hurwitzMove i t := by
  funext k
  simp only [hurwitzMove_apply, comp_apply]
  split_ifs <;> simp

/-- The Hurwitz action commutes with homomorphisms applied entrywise. -/
theorem hurwitzAction_comp (f : G →* H) (b : BraidGroup r) (t : BranchTuple r G) :
    hurwitzAction b (f ∘ t) = f ∘ hurwitzAction b t :=
  (apply_hurwitzAction_of_apply_hurwitzMove hurwitzAction (F := fun t ↦ ⇑f ∘ t)
    (fun i t ↦ by rw [hurwitzAction_sigma, hurwitzMove_comp]) b t).symm

/-- The Hurwitz action commutes with automorphisms applied entrywise. -/
theorem hurwitzAction_smul (φ : MulAut G) (b : BraidGroup r) (t : BranchTuple r G) :
    hurwitzAction b (φ • t) = φ • hurwitzAction b t := by
  rw [smul_eq_comp, smul_eq_comp, hurwitzAction_comp]

end BranchTuple

namespace NielsenClass

variable {G : Type*} [Group G] {A : Subgroup (MulAut G)} {r : ℕ}

/-- The Hurwitz action of the braid group on Nielsen classes relative to a group `A` of
automorphisms, induced by the action on branch tuples. -/
def hurwitzAction : BraidGroup r →* Equiv.Perm (NielsenClass A r) where
  toFun b := MulAction.orbitRelQuotientCongr (MulEquiv.refl A) (BranchTuple.hurwitzAction b)
    fun φ t ↦ by
      rw [MulEquiv.refl_apply, Subgroup.smul_def, Subgroup.smul_def,
        BranchTuple.hurwitzAction_smul]
  map_one' := by
    ext q
    induction q using Quotient.inductionOn'
    simp
  map_mul' b b' := by
    ext q
    induction q using Quotient.inductionOn'
    simp

/-- The Hurwitz action on Nielsen classes is computed on representatives. -/
@[simp]
theorem hurwitzAction_mk (b : BraidGroup r) (t : BranchTuple r G) :
    hurwitzAction b (Quotient.mk'' t : NielsenClass A r) =
      Quotient.mk'' (BranchTuple.hurwitzAction b t) :=
  MulAction.orbitRelQuotientCongr_mk _ _ _ t

end NielsenClass

end TauCeti
