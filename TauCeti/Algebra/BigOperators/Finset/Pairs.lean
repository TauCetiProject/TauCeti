/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Order.Interval.Finset.Defs

/-!
# Sums and products over pairs

A sum of `F : l × l → M` over all ordered pairs, for `l` a finite linear order, can be folded onto
the increasing pairs by adding each term to its transpose. When `F` vanishes on the diagonal the
diagonal contributes nothing and the fold is exact, which is
`TauCeti.sum_univ_prod_eq_sum_lt_add_swap`.

This is the shape a sum indexed by unordered pairs takes once the linear order is used to name each
pair by its increasing representative. It is what lets an antisymmetric summand, for which the two
terms of a transposed pair combine, be summed over pairs rather than over ordered pairs.

For a symmetric summand the increasing representative carries no information beyond the unordered
pair, so a product `∏_{i<j} f i j` over the increasing pairs is unchanged when the indices are
permuted, which is `TauCeti.prod_prod_Ioi_comp_perm`. This is the symmetric counterpart of
Mathlib's `Equiv.Perm.prod_Ioi_comp_eq_sign_mul_prod`, where an antisymmetric summand picks up the
sign of the permutation.

## Main results

* `TauCeti.sum_univ_prod_eq_sum_lt_add_swap`: a sum over all ordered pairs of a function vanishing
  on the diagonal, as a sum over the increasing pairs of the term plus its transpose.
* `TauCeti.prod_prod_Ioi_comp_perm`: a product of a symmetric function over the increasing pairs is
  invariant under permuting the indices.
* `TauCeti.prod_prod_Ioi_eq_of_two`: separates the first pair and its cross terms from a product
  over the increasing pairs of a finite ordinal.
* `TauCeti.prod_prod_Ioi_snoc`: splits the pair product of a tuple with a final entry.
* `TauCeti.prod_prod_Ioi_append`: the pair product of appended tuples splits into the pair
  products of each tuple and their cross terms.
-/

public section

namespace TauCeti

open Finset

/-- Peel the first two indices off a product over the increasing pairs of `Fin (m + 2)`. -/
theorem prod_prod_Ioi_eq_of_two {M : Type*} [CommMonoid M] {m : ℕ}
    (f : Fin (m + 2) → Fin (m + 2) → M) :
    ∏ i, ∏ j ∈ Ioi i, f i j =
      f 0 1 * ((∏ k : Fin m, f 0 k.succ.succ) * ∏ k : Fin m, f 1 k.succ.succ) *
        ∏ i : Fin m, ∏ j ∈ Ioi i, f i.succ.succ j.succ.succ := by
  simp only [Fin.prod_univ_succ, Fin.prod_Ioi_zero, Fin.prod_Ioi_succ, Fin.succ_zero_eq_one]
  ac_rfl

/-- A pair product on a tuple extended by a final entry splits into the old pairs and the
pairings with that entry. -/
theorem prod_prod_Ioi_snoc {A M : Type*} [CommMonoid M] {n : ℕ}
    (f : A → A → M) (w : Fin n → A) (a : A) :
    (∏ i : Fin (n + 1), ∏ j ∈ (Ioi i : Finset (Fin (n + 1))),
      f (Fin.snoc (α := fun _ => A) w a i) (Fin.snoc (α := fun _ => A) w a j)) =
      (∏ i : Fin n, ∏ j ∈ Ioi i, f (w i) (w j)) *
        (∏ i : Fin n, f (w i) a) := by
  have hIoi (i : Fin n) :
      (Ioi i.castSucc : Finset (Fin (n + 1))) =
        insert (Fin.last n) ((Ioi i).map Fin.castSuccEmb) := by
    ext j
    rcases j.eq_castSucc_or_eq_last with ⟨k, rfl⟩ | rfl
    · simp [Fin.le_last]
    · simp
  rw [Fin.prod_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last]
  simp_rw [hIoi]
  have hlast (i : Fin n) : Fin.last n ∉ (Ioi i).map Fin.castSuccEmb := by simp
  simp_rw [Finset.prod_insert (hlast _), Finset.prod_map]
  simp [Fin.snoc_castSucc, Fin.top_eq_last, Fin.snoc_last,
    Finset.prod_mul_distrib, mul_comm]

/-- The pair product of concatenated tuples is the product over pairs in each tuple and over
all pairs with one entry in each tuple. -/
theorem prod_prod_Ioi_append {A M : Type*} [CommMonoid M] {n m : ℕ}
    (f : A → A → M) (w : Fin n → A) (v : Fin m → A) :
    (∏ i : Fin (n + m), ∏ j ∈ Ioi i, f (Fin.append w v i) (Fin.append w v j)) =
      (∏ i : Fin n, ∏ j ∈ Ioi i, f (w i) (w j)) *
      (∏ i : Fin m, ∏ j ∈ Ioi i, f (v i) (v j)) *
      (∏ i : Fin n, ∏ j : Fin m, f (w i) (v j)) := by
  induction m with
  | zero =>
    have hv : v = Fin.elim0 := Subsingleton.elim _ _
    subst v
    simp
  | succ m ih =>
    let v₀ := Fin.init v
    let b := v (Fin.last m)
    have hv : v = Fin.snoc v₀ b := (Fin.snoc_init_self v).symm
    rw [hv, Fin.append_snoc]
    -- `Nat.add_succ` makes `n + (m + 1)` and `(n + m) + 1` definitionally equal here.
    -- The remaining `change` exposes the `Fin.snoc` expression used by the snoc lemma.
    change (∏ i : Fin ((n + m) + 1), ∏ j ∈ Ioi i,
      f (Fin.snoc (α := fun _ => A) (Fin.append w v₀) b i)
        (Fin.snoc (α := fun _ => A) (Fin.append w v₀) b j)) = _
    rw [prod_prod_Ioi_snoc f (Fin.append w v₀) b]
    rw [prod_prod_Ioi_snoc f v₀ b, ih v₀]
    simp only [Fin.prod_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last]
    have hcross : (∏ i : Fin (n + m), f (Fin.append w v₀ i) b) =
        (∏ i : Fin n, f (w i) b) * ∏ i : Fin m, f (v₀ i) b := by
      rw [Fin.prod_univ_add]
      simp
    rw [hcross]
    simp only [Finset.prod_mul_distrib]
    ac_rfl

/-- **A sum over all ordered pairs, folded onto the increasing ones.** A function vanishing on the
diagonal sums over `l × l` to the sum over the increasing pairs of its value together with its
value at the transposed pair. -/
theorem sum_univ_prod_eq_sum_lt_add_swap {l : Type*} [Fintype l] [LinearOrder l] {M : Type*}
    [AddCommMonoid M] (F : l × l → M) (hdiag : ∀ a, F (a, a) = 0) :
    ∑ ij : l × l, F ij =
      ∑ ij ∈ {ij : l × l | ij.1 < ij.2}, (F ij + F ij.swap) := by
  classical
  have hswap : ∑ ij ∈ {ij : l × l | ij.2 < ij.1}, F ij =
      ∑ ij ∈ {ij : l × l | ij.1 < ij.2}, F ij.swap :=
    Finset.sum_nbij' (i := Prod.swap) (j := Prod.swap) (by simp) (by simp) (by simp) (by simp)
      (by simp)
  have hnot : ∑ ij ∈ {ij : l × l | ij.2 < ij.1}, F ij =
      ∑ ij ∈ {ij : l × l | ¬ ij.1 < ij.2}, F ij := by
    refine Finset.sum_subset ?_ ?_
    · intro ij hij
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hij ⊢
      exact hij.le
    · rintro ⟨a, b⟩ hmem hnotmem
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hmem hnotmem
      exact hdiag a ▸ congrArg (fun c => F (a, c)) (le_antisymm hnotmem hmem).symm
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun ij : l × l => ij.1 < ij.2) F,
    ← hnot, hswap, Finset.sum_add_distrib]

/-- **A product over the increasing pairs of a symmetric function is permutation invariant:**
for symmetric `f`, `∏_{i<j} f (σ i) (σ j) = ∏_{i<j} f i j` for every permutation `σ`. -/
@[to_additive /-- **A sum over the increasing pairs of a symmetric function is permutation
invariant:** for symmetric `f`, `∑_{i<j} f (σ i) (σ j) = ∑_{i<j} f i j` for every permutation
`σ`. -/]
theorem prod_prod_Ioi_comp_perm {ι M : Type*} [LinearOrder ι] [Fintype ι]
    [LocallyFiniteOrderTop ι] [CommMonoid M] (f : ι → ι → M) (σ : Equiv.Perm ι)
    (hf : ∀ i j, f i j = f j i) :
    ∏ i, ∏ j ∈ Ioi i, f (σ i) (σ j) = ∏ i, ∏ j ∈ Ioi i, f i j := by
  rw [prod_sigma', prod_sigma']
  refine prod_nbij' (fun x ↦ ⟨min (σ x.1) (σ x.2), max (σ x.1) (σ x.2)⟩)
    (fun y ↦ ⟨min (σ.symm y.1) (σ.symm y.2), max (σ.symm y.1) (σ.symm y.2)⟩) ?_ ?_ ?_ ?_ ?_
  all_goals
    rintro ⟨a, b⟩ h
    simp only [mem_sigma, mem_univ, mem_Ioi, true_and] at h ⊢
  · rcases lt_or_gt_of_ne (σ.injective.ne h.ne) with hab | hab
    · simpa [hab.le] using hab
    · simpa [hab.le] using hab
  · rcases lt_or_gt_of_ne (σ.symm.injective.ne h.ne) with hab | hab
    · simpa [hab.le] using hab
    · simpa [hab.le] using hab
  · rcases le_total (σ a) (σ b) with hab | hab <;> simp [hab, h.le]
  · rcases le_total (σ.symm a) (σ.symm b) with hab | hab <;> simp [hab, h.le]
  · rcases le_total (σ a) (σ b) with hab | hab
    · simp [hab]
    · simp [hab, hf]

end TauCeti
