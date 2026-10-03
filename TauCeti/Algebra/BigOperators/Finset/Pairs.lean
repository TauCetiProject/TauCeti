/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.Order.BigOperators.Group.LocallyFinite
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
* `TauCeti.prod_prod_Ici_eq_prod_prod_Ioi_mul_prod_diag`: a product over weakly increasing
  pairs separates into the strictly increasing pairs and the diagonal.
* `TauCeti.prod_prod_Ioi_eq_of_two`: separates the first pair and its cross terms from a product
  over the increasing pairs of a finite ordinal.
* `TauCeti.prod_prod_Ioi_three` and `TauCeti.prod_prod_Ioi_four`: the products over the increasing
  pairs of `Fin 3` and of `Fin 4`, written out.
* `TauCeti.prod_prod_Ioi_snoc`: splits the pair product of a tuple with a final entry.
* `TauCeti.prod_prod_Ioi_append`: the pair product of appended tuples splits into the pair
  products of each tuple and their cross terms.
* `TauCeti.prod_prod_Ioi_append_of_mul`: the cross term for a bimultiplicative pairing
  is the pairing of the products.
* `TauCeti.sum_sum_Ioi_append_of_mul`: the same for a pairing turning products into sums.
* `TauCeti.prod_prod_Ioi_scale`: scaling all entries of a pair product for a symmetric
  bimultiplicative pairing.
-/

public section

namespace TauCeti

open Finset

/-- A product over weakly increasing pairs splits into the strictly increasing pairs and the
diagonal. -/
theorem prod_prod_Ici_eq_prod_prod_Ioi_mul_prod_diag
    {ι M : Type*} [PartialOrder ι] [Fintype ι]
    [LocallyFiniteOrderTop ι] [CommMonoid M] (f : ι → ι → M) :
    (∏ i, ∏ j ∈ Ici i, f i j) = (∏ i, ∏ j ∈ Ioi i, f i j) * ∏ i, f i i := by
  calc
    (∏ i, ∏ j ∈ Ici i, f i j) = ∏ i, (f i i * ∏ j ∈ Ioi i, f i j) := by
      apply Finset.prod_congr rfl
      intro i _
      exact (mul_prod_Ioi_eq_prod_Ici (f := f i) i).symm
    _ = _ := by rw [prod_mul_distrib, mul_comm]

/-- Peel the first two indices off a product over the increasing pairs of `Fin (m + 2)`. -/
theorem prod_prod_Ioi_eq_of_two {M : Type*} [CommMonoid M] {m : ℕ}
    (f : Fin (m + 2) → Fin (m + 2) → M) :
    ∏ i, ∏ j ∈ Ioi i, f i j =
      f 0 1 * ((∏ k : Fin m, f 0 k.succ.succ) * ∏ k : Fin m, f 1 k.succ.succ) *
        ∏ i : Fin m, ∏ j ∈ Ioi i, f i.succ.succ j.succ.succ := by
  simp only [Fin.prod_univ_succ, Fin.prod_Ioi_zero, Fin.prod_Ioi_succ, Fin.succ_zero_eq_one]
  ac_rfl

/-- The product over the three increasing pairs of `Fin 3`. -/
theorem prod_prod_Ioi_three {M : Type*} [CommMonoid M] (f : Fin 3 → Fin 3 → M) :
    ∏ i, ∏ j ∈ Ioi i, f i j = f 0 1 * f 0 2 * f 1 2 := by
  simp [Fin.prod_univ_succ, Fin.prod_Ioi_succ, mul_assoc]

/-- The product over the six increasing pairs of `Fin 4`. -/
theorem prod_prod_Ioi_four {M : Type*} [CommMonoid M] (f : Fin 4 → Fin 4 → M) :
    ∏ i, ∏ j ∈ Ioi i, f i j = f 0 1 * f 0 2 * f 0 3 * f 1 2 * f 1 3 * f 2 3 := by
  simp [Fin.prod_univ_succ, Fin.prod_Ioi_succ, mul_assoc]

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

/-- The pairwise product of a concatenation for a bimultiplicative pairing. -/
theorem prod_prod_Ioi_append_of_mul {A M : Type*} [CommMonoid A] [CommMonoid M] (F : A → A → M)
    (hone_left : ∀ b, F 1 b = 1) (hone_right : ∀ a, F a 1 = 1)
    (hmul_left : ∀ a b c, F (a * b) c = F a c * F b c)
    (hmul_right : ∀ a b c, F a (b * c) = F a b * F a c)
    {m n : ℕ} (p : Fin m → A) (q : Fin n → A) :
    (∏ i, ∏ j ∈ Ioi i, F (Fin.append p q i) (Fin.append p q j)) =
      (∏ i, ∏ j ∈ Ioi i, F (p i) (p j)) *
        (∏ i, ∏ j ∈ Ioi i, F (q i) (q j)) *
        F (∏ i, p i) (∏ j, q j) := by
  let h₁ (a : A) : A →* M := {
    toFun := F a
    map_one' := hone_right a
    map_mul' := hmul_right a }
  let h₂ (b : A) : A →* M := {
    toFun := fun a => F a b
    map_one' := hone_left b
    map_mul' := fun a c => hmul_left a c b }
  rw [prod_prod_Ioi_append]
  congr 1
  calc
    (∏ i, ∏ j, F (p i) (q j)) = ∏ i, F (p i) (∏ j, q j) := by
      apply Finset.prod_congr rfl
      intro i _
      exact (map_prod (h₁ (p i)) q Finset.univ).symm
    _ = F (∏ i, p i) (∏ j, q j) :=
      (map_prod (h₂ (∏ j, q j)) p Finset.univ).symm

/-- The pairwise sum of a concatenation for a pairing that turns products in either argument into
sums. -/
theorem sum_sum_Ioi_append_of_mul {A M : Type*} [CommMonoid A] [AddCommMonoid M] (F : A → A → M)
    (hone_left : ∀ b, F 1 b = 0) (hone_right : ∀ a, F a 1 = 0)
    (hmul_left : ∀ a b c, F (a * b) c = F a c + F b c)
    (hmul_right : ∀ a b c, F a (b * c) = F a b + F a c)
    {m n : ℕ} (p : Fin m → A) (q : Fin n → A) :
    (∑ i, ∑ j ∈ Ioi i, F (Fin.append p q i) (Fin.append p q j)) =
      (∑ i, ∑ j ∈ Ioi i, F (p i) (p j)) +
        (∑ i, ∑ j ∈ Ioi i, F (q i) (q j)) +
        F (∏ i, p i) (∏ j, q j) := by
  apply Multiplicative.ofAdd.injective
  simpa only [ofAdd_add, ofAdd_sum] using prod_prod_Ioi_append_of_mul
    (fun a b => Multiplicative.ofAdd (F a b))
    (fun b => by rw [hone_left, ofAdd_zero]) (fun a => by rw [hone_right, ofAdd_zero])
    (fun a b c => by rw [hmul_left, ofAdd_add]) (fun a b c => by rw [hmul_right, ofAdd_add]) p q

/-- Scaling every coefficient in a pairwise product for a symmetric bimultiplicative
pairing. The self-pairing law supplies the correction for each coefficient pair. -/
theorem prod_prod_Ioi_scale {A M : Type*} [CommMonoid A] [CommMonoid M] (F : A → A → M)
    {s : A}
    (hmul_right : ∀ a b c, F a (b * c) = F a b * F a c)
    (hcomm : ∀ a b, F a b = F b a) (a : A) (hself : F a a = F a s)
    {n : ℕ} (w : Fin n → A) :
    (∏ i, ∏ j ∈ Ioi i, F (a * w i) (a * w j)) =
      (∏ i, ∏ j ∈ Ioi i, F (w i) (w j)) *
        F a s ^ n.choose 2 * F a (∏ i, w i) ^ (n - 1) := by
  have hmul_left (x y z : A) : F (x * y) z = F x z * F y z := by
    rw [hcomm (x * y) z, hmul_right, hcomm z x, hcomm z y]
  have hmulmul (b c : A) :
      F (a * b) (a * c) = F b c * F a s * F a b * F a c := by
    rw [hmul_left, hmul_right, hmul_right, hself, hcomm b a]
    ac_rfl
  have hprod_nonempty {k : ℕ} (v : Fin (k + 1) → A) :
      (∏ i, F a (v i)) = F a (∏ i, v i) := by
    induction k with
    | zero => simp
    | succ k ih =>
      calc
        (∏ i, F a (v i)) = F a (v 0) * ∏ i : Fin (k + 1), F a (v i.succ) :=
          Fin.prod_univ_succ _
        _ = F a (v 0) * F a (∏ i : Fin (k + 1), v i.succ) :=
          congrArg (F a (v 0) * ·) (ih (fun i => v i.succ))
        _ = F a (∏ i, v i) := by rw [Fin.prod_univ_succ v, hmul_right]
  induction n with
  | zero => simp
  | succ n ih =>
    cases n with
    | zero => simp
    | succ n =>
      let w₀ := Fin.init w
      let b := w (Fin.last (n + 1))
      have hw : w = Fin.snoc w₀ b := (Fin.snoc_init_self w).symm
      rw [hw]
      have hs (i : Fin ((n + 1) + 1)) :
          a * Fin.snoc (α := fun _ => A) w₀ b i =
            Fin.snoc (α := fun _ => A) (fun j => a * w₀ j) (a * b) i := by
        rcases i.eq_castSucc_or_eq_last with ⟨j, rfl⟩ | rfl <;> simp
      simp_rw [hs]
      have hprod : (∏ i, F a (w₀ i)) = F a (∏ i, w₀ i) :=
        hprod_nonempty w₀
      have hchoose : ((n + 1) + 1).choose 2 = (n + 1).choose 2 + (n + 1) := by
        rw [Nat.choose_succ_succ', Nat.choose_one_right, add_comm]
      rw [prod_prod_Ioi_snoc F (fun j => a * w₀ j) (a * b),
        prod_prod_Ioi_snoc F w₀ b, ih w₀, Fin.prod_snoc, Nat.add_sub_cancel]
      simp_rw [hmulmul]
      simp only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
        hprod, hmul_right, mul_pow, hchoose, pow_add]
      rw [Nat.add_sub_cancel, pow_succ (F a (∏ i, w₀ i)) n,
        pow_succ (F a b) n]
      simp only [pow_one]
      ac_nf

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
