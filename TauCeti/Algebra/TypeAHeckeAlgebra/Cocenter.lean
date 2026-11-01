/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.TypeAHeckeAlgebra.CycleWord
public import TauCeti.Combinatorics.Enumerative.Partition.Basic

/-!
# Cycle-block words span the cocenter of a Hecke stage

Write `gᵢ = q • T i` and `ζₘ = g_(m-2) * ⋯ * g_0` for the cycle word on `m` strands
(`TauCeti.InfiniteTypeAHeckeAlgebra.cycleWord`). For a list `l = [m₁, m₂, …]` of block sizes, the
cycle-block word `ζ_l = ζ_(m₁) * shift m₁ (ζ_(m₂) * shift m₂ (⋯))`
(`TauCeti.InfiniteTypeAHeckeAlgebra.cycleBlockWord`) places the cycle words on the consecutive
disjoint blocks of `m₁, m₂, …` strands. For a partition `μ` of `n`, `ζ_μ`
(`TauCeti.InfiniteTypeAHeckeAlgebra.cycleWordPart`) is the cycle-block word of the parts of `μ` in
nonincreasing order; it lies in the stage `Hₙ` of the first `n` strands.

The cocenter of `Hₙ` is its quotient by the linear span of the commutators `x * y - y * x`, and the
trace functionals on `Hₙ` are the linear maps out of it. The main result
`TauCeti.InfiniteTypeAHeckeAlgebra.trace_eq_of_cycleBlock_values` says that the classes of the
words `ζ_μ`, for the partitions `μ` of `n`, span the cocenter: two trace functionals on `Hₙ` that
agree on every `ζ_μ` are equal. In contrast with
`TauCeti.InfiniteTypeAHeckeAlgebra.towerTrace_eq_of_cycleChain_values`, the functionals live on a
single stage and need not be multiplicative on disjoint blocks of strands. The result holds over
every commutative ring and for every unit `q`. The linear independence of these classes, which
makes them a basis of the cocenter in the split semisimple case, is not proved here.

Two facts reduce every element of `Hₙ` to the words `ζ_μ` modulo commutators. Along the
decomposition `Hₖ₊₂ = Hₖ₊₁ + Hₖ₊₁ Tₖ Hₖ₊₁`
(`TauCeti.InfiniteTypeAHeckeAlgebra.toSubmodule_stage_add_two`), rotating under the trace reduces
every element to cycle-block words of compositions of `n`, one strand at a time, as for
block-multiplicative traces. And two adjacent blocks of `c` and `d` strands are exchanged by
conjugation with an invertible element of the stage `c + d`, the product of descending words
`T (d - 1) * ⋯ * T 0` shifted along the first block, so the order of the blocks does not matter.

## Main definitions

* `TauCeti.InfiniteTypeAHeckeAlgebra.cycleBlockWord`: the cycle-block word `ζ_l` of a list of
  block sizes.
* `TauCeti.InfiniteTypeAHeckeAlgebra.cycleWordPart`: the cycle-block word `ζ_μ` of a partition.

## Main results

* `TauCeti.InfiniteTypeAHeckeAlgebra.cycleBlockWord_append`: the cycle-block word of a
  concatenation is the product of the first word with the shift of the second.
* `TauCeti.InfiniteTypeAHeckeAlgebra.trace_eq_of_cycleBlock_values`: two trace functionals on the
  stage `Hₙ` agreeing on every `ζ_μ`, for `μ` a partition of `n`, are equal.

## References

* M. Geck and G. Pfeiffer, *Characters of Finite Coxeter Groups and Iwahori-Hecke Algebras*,
  OUP (2000), Section 8.2, where a trace on a Hecke algebra is shown to be determined by
  its values on the elements `T_w` for `w` of minimal length in its conjugacy class; in type A
  these are the cycle-block words of partitions.
* A. Ram, *A Frobenius formula for the characters of the Hecke algebras*, Invent. Math. 106
  (1991), 461–488, for the cycle-block words `g_(m-1) ⋯ g_1` on consecutive blocks.
-/

public section

namespace TauCeti

namespace InfiniteTypeAHeckeAlgebra

variable {R : Type*} [CommRing R] {q : Rˣ}

section CycleBlockWord

variable (q) in
/-- The cycle-block word `ζ_l` of a list `l = [m₁, m₂, …]` of block sizes: the product
`ζ_(m₁) * shift m₁ (ζ_(m₂) * shift m₂ (⋯))` of the cycle words `ζₘ` placed on the consecutive
disjoint blocks of `m₁, m₂, …` strands. -/
def cycleBlockWord : List ℕ → InfiniteTypeAHeckeAlgebra R q
  | [] => 1
  | m :: l => cycleWord q m * shift R q m (cycleBlockWord l)

/-- The cycle-block word of the empty list is `1`. -/
@[simp]
theorem cycleBlockWord_nil : cycleBlockWord q [] = (1 : InfiniteTypeAHeckeAlgebra R q) := by
  rw [cycleBlockWord]

/-- The cycle-block word of `m :: l` is the cycle word on the first `m` strands times the shift by
`m` of the cycle-block word of `l`. -/
@[simp]
theorem cycleBlockWord_cons (m : ℕ) (l : List ℕ) :
    cycleBlockWord q (m :: l) = cycleWord q m * shift R q m (cycleBlockWord q l) := by
  rw [cycleBlockWord]

/-- The cycle-block word of a single block is the cycle word. -/
theorem cycleBlockWord_singleton (m : ℕ) :
    cycleBlockWord q [m] = (cycleWord q m : InfiniteTypeAHeckeAlgebra R q) := by
  simp

/-- The cycle-block word of a concatenation `l ++ l'` is the cycle-block word of `l` times the
shift of that of `l'` past the `l.sum` strands of `l`. -/
theorem cycleBlockWord_append (l l' : List ℕ) :
    cycleBlockWord q (l ++ l') =
      (cycleBlockWord q l : InfiniteTypeAHeckeAlgebra R q) *
        shift R q l.sum (cycleBlockWord q l') := by
  induction l with
  | nil => simp
  | cons m l ih =>
    rw [List.cons_append, cycleBlockWord_cons, cycleBlockWord_cons, ih, map_mul, shift_shift,
      List.sum_cons, mul_assoc]

/-- Adding a block of one strand at the end does not change the cycle-block word: the words are
compatible with the tower inclusions. -/
@[simp]
theorem cycleBlockWord_append_singleton_one (l : List ℕ) :
    cycleBlockWord q (l ++ [1]) = (cycleBlockWord q l : InfiniteTypeAHeckeAlgebra R q) := by
  simp [cycleBlockWord_append]

/-- The cycle-block word of `l` lies in the stage of the first `l.sum` strands. -/
theorem cycleBlockWord_mem_stage (l : List ℕ) :
    (cycleBlockWord q l : InfiniteTypeAHeckeAlgebra R q) ∈ stage R q l.sum := by
  induction l with
  | nil =>
    rw [cycleBlockWord_nil]
    exact one_mem _
  | cons m l ih =>
    rw [cycleBlockWord_cons, List.sum_cons]
    refine mul_mem (stage_mono (Nat.le_add_right m l.sum) (cycleWord_mem_stage m)) ?_
    rw [Nat.add_comm]
    exact shift_mem_stage m ih

/-- A cycle-block word whose first block has `j + 1` strands is `q ^ j` times the descending
product `T (j - 1) * ⋯ * T 0` followed by the shift of the remaining blocks. -/
private theorem cycleBlockWord_succ_cons (j : ℕ) (l : List ℕ) :
    cycleBlockWord q ((j + 1) :: l) =
      (q : R) ^ j • (cosetRep q j 0 * shift R q (j + 1) (cycleBlockWord q l)) := by
  rw [cycleBlockWord_cons, cycleWord_def, Nat.add_sub_cancel, smul_mul_assoc]

variable (q) in
/-- The cycle-block word `ζ_μ` of a partition `μ`: the cycle words `ζ_(μ₁), ζ_(μ₂), …` of its
parts, in nonincreasing order, placed on consecutive disjoint blocks of strands. -/
def cycleWordPart {n : ℕ} (μ : n.Partition) : InfiniteTypeAHeckeAlgebra R q :=
  cycleBlockWord q (μ.parts.sort (· ≥ ·))

/-- The cycle-block word of a partition is that of its parts in nonincreasing order. -/
theorem cycleWordPart_def {n : ℕ} (μ : n.Partition) :
    cycleWordPart q μ = cycleBlockWord q (μ.parts.sort (· ≥ ·)) := (rfl)

/-- The cycle-block word of a partition of `n` lies in the stage of the first `n` strands. -/
theorem cycleWordPart_mem_stage {n : ℕ} (μ : n.Partition) :
    (cycleWordPart q μ : InfiniteTypeAHeckeAlgebra R q) ∈ stage R q n := by
  simpa only [cycleWordPart_def, Nat.Partition.sum_sort_parts] using
    cycleBlockWord_mem_stage (q := q) (μ.parts.sort (· ≥ ·))

end CycleBlockWord

section BlockSwap

/-! ### Exchanging two adjacent blocks of strands -/

/-- An element of the stage `n` with a two-sided inverse in the stage `n`. -/
private def IsStageUnit (n : ℕ) (u : InfiniteTypeAHeckeAlgebra R q) : Prop :=
  u ∈ stage R q n ∧ ∃ v ∈ stage R q n, u * v = 1 ∧ v * u = 1

private theorem isStageUnit_one (n : ℕ) : IsStageUnit n (1 : InfiniteTypeAHeckeAlgebra R q) :=
  ⟨one_mem _, 1, one_mem _, mul_one 1, mul_one 1⟩

private theorem IsStageUnit.mono {m n : ℕ} (h : m ≤ n) {u : InfiniteTypeAHeckeAlgebra R q}
    (hu : IsStageUnit m u) : IsStageUnit n u := by
  obtain ⟨hu, v, hv, huv, hvu⟩ := hu
  exact ⟨stage_mono h hu, v, stage_mono h hv, huv, hvu⟩

private theorem IsStageUnit.mul {n : ℕ} {u u' : InfiniteTypeAHeckeAlgebra R q}
    (hu : IsStageUnit n u) (hu' : IsStageUnit n u') : IsStageUnit n (u * u') := by
  obtain ⟨hu, v, hv, huv, hvu⟩ := hu
  obtain ⟨hu', v', hv', huv', hvu'⟩ := hu'
  refine ⟨mul_mem hu hu', v' * v, mul_mem hv' hv, ?_, ?_⟩
  · rw [mul_assoc, ← mul_assoc u' v', huv', one_mul, huv]
  · rw [mul_assoc, ← mul_assoc v u, hvu, one_mul, hvu']

private theorem IsStageUnit.shift {n : ℕ} (k : ℕ) {u : InfiniteTypeAHeckeAlgebra R q}
    (hu : IsStageUnit n u) : IsStageUnit (n + k) (InfiniteTypeAHeckeAlgebra.shift R q k u) := by
  obtain ⟨hu, v, hv, huv, hvu⟩ := hu
  exact ⟨shift_mem_stage k hu, InfiniteTypeAHeckeAlgebra.shift R q k v, shift_mem_stage k hv,
    by rw [← map_mul, huv, map_one], by rw [← map_mul, hvu, map_one]⟩

private theorem isStageUnit_cosetRep (n : ℕ) :
    IsStageUnit (n + 1) (cosetRep q n 0 : InfiniteTypeAHeckeAlgebra R q) := by
  induction n with
  | zero =>
    rw [cosetRep_self]
    exact isStageUnit_one 1
  | succ n ih =>
    rw [cosetRep_succ (Nat.zero_le n)]
    have hT : T q n ∈ stage R q (n + 2) := T_mem_stage (by omega)
    refine IsStageUnit.mul ⟨hT, ↑(unitT q n)⁻¹, ?_, by simpa only [val_unitT] using
      (unitT q n).mul_inv, by simpa only [val_unitT] using (unitT q n).inv_mul⟩ (ih.mono (by omega))
    rw [val_inv_unitT]
    exact sub_mem hT (Subalgebra.algebraMap_mem _ _)

variable (q) in
/-- The block swap moving a block of `c` strands past the next block of `d` strands: the product
of the descending words `T (d + k - 1) * ⋯ * T k` for `k = 0, …, c - 1`, each moving one strand of
the first block past the second block. -/
private def blockSwap (d : ℕ) : ℕ → InfiniteTypeAHeckeAlgebra R q
  | 0 => 1
  | c + 1 => cosetRep q d 0 * shift R q 1 (blockSwap d c)

private theorem isStageUnit_blockSwap (d c : ℕ) : IsStageUnit (c + d) (blockSwap q d c) := by
  induction c with
  | zero =>
    rw [blockSwap]
    exact isStageUnit_one _
  | succ c ih =>
    rw [blockSwap]
    exact ((isStageUnit_cosetRep d).mono (by omega)).mul ((ih.shift 1).mono (by omega))

/-- The block swap moves the second block of `d` strands to the first `d` strands. -/
private theorem blockSwap_mul_shift (d c : ℕ) {y : InfiniteTypeAHeckeAlgebra R q}
    (hy : y ∈ stage R q d) : blockSwap q d c * shift R q c y = y * blockSwap q d c := by
  induction c with
  | zero => simp [blockSwap]
  | succ c ih =>
    have hs : shift R q (c + 1) y = shift R q 1 (shift R q c y) := by
      rw [shift_shift, Nat.add_comm]
    rw [blockSwap, hs, mul_assoc, ← map_mul, ih, map_mul, ← mul_assoc,
      cosetRep_zero_mul_shift_one hy, mul_assoc]

/-- Moving two consecutive strands past a block of `d` strands, one after the other, carries the
crossing `T 0` of these strands to `T d`. -/
private theorem cosetRep_mul_shift_cosetRep_mul_T_zero (d : ℕ) :
    cosetRep q d 0 * shift R q 1 (cosetRep q d 0) * T q 0 =
      T q d * cosetRep q d 0 * shift R q 1 (cosetRep q d 0) := by
  have h : shift R q 1 (cosetRep q d 0) * T q 0 = cosetRep q (d + 1) 0 := by
    rw [shift_cosetRep, cosetRep_succ_mul_T (Nat.succ_pos d)]
  rw [mul_assoc, h, ← cosetRep_succ (Nat.zero_le d),
    cosetRep_zero_mul_shift_one (cosetRep_mem_stage d 0)]

/-- The block swap moves the first block of `c` strands up by `d` strands, on generators. -/
private theorem blockSwap_mul_T (d : ℕ) :
    ∀ c i, i + 1 < c → blockSwap q d c * T q i = T q (i + d) * blockSwap q d c
  | 0, i, hi => absurd hi (by omega)
  | c + 1, 0, hi => by
    obtain ⟨c, rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
    have hc : Commute (T q 0) (shift R q 2 (blockSwap q d c)) :=
      commute_shift_of_mem_stage (T_mem_stage (by omega)) _
    simp only [blockSwap, map_mul, shift_shift, Nat.zero_add]
    rw [← mul_assoc, mul_assoc _ _ (T q 0), ← hc.eq, ← mul_assoc,
      cosetRep_mul_shift_cosetRep_mul_T_zero, mul_assoc (T q d), mul_assoc (T q d)]
  | c + 1, i + 1, hi => by
    have hc : Commute (T q (i + d + 1)) (cosetRep q d 0) :=
      commute_T_of_mem_stage (by omega) (cosetRep_mem_stage d 0)
    rw [blockSwap, mul_assoc, ← shift_T 1 i, ← map_mul, blockSwap_mul_T d c i (by omega), map_mul,
      shift_T, ← mul_assoc, ← hc.eq, mul_assoc, Nat.add_right_comm]

/-- The block swap moves the first block of `c` strands up by `d` strands. -/
private theorem blockSwap_mul (d c : ℕ) {x : InfiniteTypeAHeckeAlgebra R q}
    (hx : x ∈ stage R q c) : blockSwap q d c * x = shift R q d x * blockSwap q d c :=
  mul_map_eq_map_mul_of_mem_stage (f := AlgHom.id R _) (fun i hi ↦ by
    rw [AlgHom.id_apply, shift_T]
    exact blockSwap_mul_T d c i hi) hx

/-- The block swap conjugates `a * shift c b` to `b * shift d a`, for `a` on the first `c` strands
and `b` on the next `d` strands. -/
private theorem blockSwap_mul_mul_shift {c d : ℕ} {a b : InfiniteTypeAHeckeAlgebra R q}
    (ha : a ∈ stage R q c) (hb : b ∈ stage R q d) :
    blockSwap q d c * (a * shift R q c b) = b * shift R q d a * blockSwap q d c := by
  rw [← mul_assoc, blockSwap_mul d c ha, mul_assoc, blockSwap_mul_shift d c hb, ← mul_assoc,
    (commute_shift_of_mem_stage hb a).eq]

end BlockSwap

section Trace

variable {M : Type*} [AddCommGroup M] [Module R M] {σ : InfiniteTypeAHeckeAlgebra R q →ₗ[R] M}
  {N : ℕ}

/-- A functional that is tracial on the stage `N` takes the same value on two elements of the
stage `N` conjugate by an invertible element of the stage `N`. -/
private theorem map_eq_of_mul_eq_mul
    (hσ : ∀ x ∈ stage R q N, ∀ y ∈ stage R q N, σ (x * y) = σ (y * x))
    {u x y : InfiniteTypeAHeckeAlgebra R q} (hu : IsStageUnit N u) (hx : x ∈ stage R q N)
    (h : u * x = y * u) : σ x = σ y := by
  obtain ⟨hu, v, hv, huv, hvu⟩ := hu
  have hy : y ∈ stage R q N := by
    have hy : y = u * x * v := by rw [h, mul_assoc, huv, mul_one]
    exact hy ▸ mul_mem (mul_mem hu hx) hv
  have hx' : x = v * y * u := by rw [mul_assoc, ← h, ← mul_assoc, hvu, one_mul]
  rw [hx', hσ _ (mul_mem hv hy) _ hu, ← mul_assoc, huv, one_mul]

/-- A functional that is tracial on the stage `N` takes the same value on the cycle-block words of
two lists differing by the order of their blocks, preceded by any element on the strands before
them. -/
private theorem map_mul_shift_cycleBlockWord_eq_of_perm
    (hσ : ∀ x ∈ stage R q N, ∀ y ∈ stage R q N, σ (x * y) = σ (y * x)) {l l' : List ℕ}
    (hl : l.Perm l') :
    ∀ {k : ℕ} {x : InfiniteTypeAHeckeAlgebra R q}, x ∈ stage R q k → k + l.sum = N →
      σ (x * shift R q k (cycleBlockWord q l)) = σ (x * shift R q k (cycleBlockWord q l')) := by
  induction hl with
  | nil => exact fun _ _ ↦ rfl
  | cons m _ ih =>
    intro k x hx hk
    rw [List.sum_cons] at hk
    have hx' : x * shift R q k (cycleWord q m) ∈ stage R q (k + m) := mul_mem
      (stage_mono (Nat.le_add_right k m) hx) (Nat.add_comm m k ▸ shift_mem_stage k
        (cycleWord_mem_stage m))
    simpa only [cycleBlockWord_cons, map_mul, shift_shift, mul_assoc] using
      ih hx' (by omega)
  | swap m m' l =>
    intro k x hx hk
    simp only [List.sum_cons] at hk
    -- Both sides are `x * shift k (a * shift c b) * t` with the tail `t` on the last strands.
    have e : ∀ a b : ℕ, x * shift R q k (cycleBlockWord q (a :: b :: l)) =
        x * shift R q k (cycleWord q a * shift R q a (cycleWord q b)) *
          shift R q (k + (a + b)) (cycleBlockWord q l) := fun a b ↦ by
      simp only [cycleBlockWord_cons, map_mul, shift_shift, mul_assoc]
    rw [e, e, Nat.add_comm m' m]
    set t := shift R q (k + (m + m')) (cycleBlockWord q l)
    have ht : t ∈ stage R q N := by
      have := shift_mem_stage (k + (m + m')) (cycleBlockWord_mem_stage (q := q) l)
      rwa [show l.sum + (k + (m + m')) = N by omega] at this
    -- Conjugate by the block swap on the strands `k, …, k + m + m' - 1`.
    have hW : blockSwap q m m' ∈ stage R q (m + m') :=
      Nat.add_comm m' m ▸ (isStageUnit_blockSwap m m').1
    have hux : shift R q k (blockSwap q m m') * x = x * shift R q k (blockSwap q m m') :=
      (commute_shift_of_mem_stage hx _).eq.symm
    have hut : shift R q k (blockSwap q m m') * t = t * shift R q k (blockSwap q m m') := by
      simp only [t, ← shift_shift k (m + m'), ← map_mul,
        (commute_shift_of_mem_stage hW (cycleBlockWord q l)).eq]
    have hP : shift R q k (blockSwap q m m') *
        shift R q k (cycleWord q m' * shift R q m' (cycleWord q m)) =
          shift R q k (cycleWord q m * shift R q m (cycleWord q m')) *
            shift R q k (blockSwap q m m') := by
      rw [← map_mul, blockSwap_mul_mul_shift (cycleWord_mem_stage m') (cycleWord_mem_stage m),
        map_mul]
    refine map_eq_of_mul_eq_mul hσ (((isStageUnit_blockSwap m m').shift k).mono (by omega))
      (mul_mem (mul_mem (stage_mono (by omega) hx) ?_) ht) ?_
    · have := shift_mem_stage k (mul_mem (stage_mono (Nat.le_add_right m' m)
        (cycleWord_mem_stage (q := q) m')) (Nat.add_comm m m' ▸ shift_mem_stage m'
          (cycleWord_mem_stage (q := q) m)))
      exact stage_mono (by omega) this
    · calc _ = shift R q k (blockSwap q m m') * x *
            shift R q k (cycleWord q m' * shift R q m' (cycleWord q m)) * t := by
            simp only [mul_assoc]
        _ = x * shift R q k (cycleWord q m * shift R q m (cycleWord q m')) *
            (shift R q k (blockSwap q m m') * t) := by
            rw [hux, mul_assoc x, hP]
            simp only [mul_assoc]
        _ = _ := by
            rw [hut]
            simp only [mul_assoc]
  | trans h₁ _ ih₁ ih₂ =>
    intro k x hx hk
    rw [ih₁ hx hk, ih₂ hx (by rwa [← h₁.sum_eq])]

/-- A functional that is tracial on the stage `N` and vanishes on the cycle-block words of the
partitions of `N` vanishes on those of all compositions of `N`. -/
private theorem map_cycleBlockWord_eq_zero
    (hσ : ∀ x ∈ stage R q N, ∀ y ∈ stage R q N, σ (x * y) = σ (y * x))
    (h : ∀ μ : N.Partition, σ (cycleWordPart q μ) = 0) {l : List ℕ} (hl : ∀ m ∈ l, 0 < m)
    (hsum : l.sum = N) : σ (cycleBlockWord q l) = 0 := by
  let μ : N.Partition := ⟨l, fun hi ↦ hl _ (Multiset.mem_coe.1 hi), by rw [Multiset.sum_coe, hsum]⟩
  have hperm : (μ.parts.sort (· ≥ ·)).Perm l :=
    Multiset.coe_eq_coe.1 (Multiset.sort_eq μ.parts (· ≥ ·))
  have := map_mul_shift_cycleBlockWord_eq_of_perm hσ hperm (one_mem (stage R q 0))
    (by rw [Nat.zero_add, hperm.sum_eq, hsum])
  simp only [shift_zero, AlgHom.id_apply, one_mul] at this
  rw [← this, ← cycleWordPart_def, h μ]

/-- The rotation step: for a functional tracial on the stage `N`, elements `b`, `e` of the stage
`a + 1` with `a < k`, and `t` commuting with the stage `k + 1`, the value at
`b * T a * e * (cosetRep q k (a + 1) * t)` is the value at `e * b * (cosetRep q k a * t)`. -/
private theorem map_mul_T_mul_mul_cosetRep_mul
    (hσ : ∀ x ∈ stage R q N, ∀ y ∈ stage R q N, σ (x * y) = σ (y * x)) {a k : ℕ} (hak : a < k)
    (hkN : k + 1 ≤ N) {b e t : InfiniteTypeAHeckeAlgebra R q} (hb : b ∈ stage R q (a + 1))
    (he : e ∈ stage R q (a + 1)) (ht : t ∈ stage R q N)
    (htk : ∀ z ∈ stage R q (k + 1), Commute z t) :
    σ (b * T q a * e * (cosetRep q k (a + 1) * t)) = σ (e * b * (cosetRep q k a * t)) := by
  -- `cosetRep q k (a + 1)` lives on the strands from `a + 1` on, so it commutes with `b`.
  have hcb : Commute b (cosetRep q k (a + 1)) := by
    have hc : cosetRep q k (a + 1) = shift R q (a + 1) (cosetRep q (k - (a + 1)) 0) := by
      rw [shift_cosetRep, Nat.sub_add_cancel hak, Nat.zero_add]
    rw [hc]
    exact commute_shift_of_mem_stage hb _
  have h1 := (htk b (stage_mono (by omega) hb)).eq
  have h2 := (htk (T q a) (T_mem_stage (by omega))).eq
  have h3 : t * (b * T q a) = b * (T q a * t) := by
    rw [← mul_assoc, ← h1, mul_assoc, ← h2]
  have h4 : cosetRep q k (a + 1) * (b * (T q a * t)) =
      b * (cosetRep q k (a + 1) * (T q a * t)) := by
    rw [← mul_assoc, ← hcb.eq, mul_assoc]
  have hrot : e * (cosetRep q k (a + 1) * t) * (b * T q a) = e * b * (cosetRep q k a * t) := by
    calc e * (cosetRep q k (a + 1) * t) * (b * T q a)
        = e * (cosetRep q k (a + 1) * (t * (b * T q a))) := by simp only [mul_assoc]
      _ = e * b * (cosetRep q k (a + 1) * T q a * t) := by
          rw [h3, h4]
          simp only [mul_assoc]
      _ = e * b * (cosetRep q k a * t) := by rw [cosetRep_succ_mul_T hak]
  rw [← hrot, ← hσ _ (mul_mem (stage_mono (by omega) hb) (T_mem_stage (by omega))) _
    (mul_mem (stage_mono (by omega) he) (mul_mem (stage_mono (by omega)
      (cosetRep_mem_stage k (a + 1))) ht))]
  simp only [mul_assoc]

/-- A functional that is tracial on the stage `N` and vanishes on the cycle-block words of the
partitions of `N` vanishes on the stage `N`. -/
private theorem map_eq_zero_of_mem_stage
    (hσ : ∀ x ∈ stage R q N, ∀ y ∈ stage R q N, σ (x * y) = σ (y * x))
    (h : ∀ μ : N.Partition, σ (cycleWordPart q μ) = 0) {x : InfiniteTypeAHeckeAlgebra R q}
    (hx : x ∈ stage R q N) : σ x = 0 := by
  -- Strong induction on the number `k` of strands carrying an arbitrary element, followed by
  -- cycle-block words of a composition on the remaining strands.
  have key : ∀ k, ∀ x ∈ stage R q k, ∀ l : List ℕ, (∀ m ∈ l, 0 < m) → k + l.sum = N →
      σ (x * shift R q k (cycleBlockWord q l)) = 0 := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ihk =>
      intro x hx l hl hkl
      rcases k with _ | k
      · rw [stage_eq_bot_of_le_one (Nat.zero_le 1), Algebra.mem_bot] at hx
        obtain ⟨r, rfl⟩ := hx
        rw [shift_zero, AlgHom.id_apply, ← Algebra.smul_def, map_smul,
          map_cycleBlockWord_eq_zero hσ h hl (by omega), smul_zero]
      set t := shift R q (k + 1) (cycleBlockWord q l)
      have ht : t ∈ stage R q N := by
        have := shift_mem_stage (k + 1) (cycleBlockWord_mem_stage (q := q) l)
        rwa [show l.sum + (k + 1) = N by omega] at this
      -- For `b` in the stage `a`, the descending word from `T (k - 1)` to `T a` is the cycle word
      -- on the strands `a, …, k`, so `b * (cosetRep q k a * t)` falls under the induction.
      have hB : ∀ a ≤ k, ∀ b ∈ stage R q a, σ (b * (cosetRep q k a * t)) = 0 := by
        intro a ha b hb
        obtain ⟨j, rfl⟩ : ∃ j, k = j + a := ⟨k - a, by omega⟩
        have hc : cosetRep q (j + a) a * t =
            shift R q a (cosetRep q j 0 * shift R q (j + 1) (cycleBlockWord q l)) := by
          rw [map_mul, shift_cosetRep, Nat.zero_add, shift_shift,
            show a + (j + 1) = j + a + 1 by omega]
        have h0 := ihk a (by omega) b hb ((j + 1) :: l) (List.forall_mem_cons.2 ⟨j.succ_pos, hl⟩)
          (by rw [List.sum_cons]; omega)
        rwa [cycleBlockWord_succ_cons, map_smul, mul_smul_comm, map_smul,
          (q.isUnit.pow j).smul_eq_zero, ← hc] at h0
      -- For `y` in the stage `a + 1`, split `y` along `Hₐ₊₁ = Hₐ + Hₐ Tₐ₋₁ Hₐ` and rotate.
      have hI : ∀ a ≤ k, ∀ y ∈ stage R q (a + 1), σ (y * (cosetRep q k a * t)) = 0 := by
        intro a
        induction a with
        | zero =>
          intro ha y hy
          rw [stage_eq_bot_of_le_one le_rfl, ← stage_eq_bot_of_le_one (Nat.zero_le 1)] at hy
          exact hB 0 ha y hy
        | succ a iha =>
          intro ha y hy
          let P : Submodule R (InfiniteTypeAHeckeAlgebra R q) :=
            (LinearMap.ker σ).comap (LinearMap.mulRight R (cosetRep q k (a + 1) * t))
          have hP : ∀ y, y ∈ P ↔ σ (y * (cosetRep q k (a + 1) * t)) = 0 := fun _ ↦ Iff.rfl
          refine (hP y).1 <| (toSubmodule_stage_add_two_le_iff.2 ⟨fun b hb ↦ (hP b).2 ?_,
            fun b hb e he ↦ (hP _).2 ?_⟩) hy
          · exact hB (a + 1) ha b hb
          · rw [map_mul_T_mul_mul_cosetRep_mul hσ ha (by omega) hb he ht
              fun z hz ↦ commute_shift_of_mem_stage hz _]
            exact iha (by omega) _ (mul_mem he hb)
      simpa only [cosetRep_self, one_mul] using hI k le_rfl x hx
  simpa only [cycleBlockWord_nil, map_one, mul_one] using key N x hx [] (by simp) (by simp)

/-- **Cycle-block words span the cocenter.** Two trace functionals on the stage of the first `n`
strands are equal as soon as they agree on the cycle-block word `ζ_μ` of every partition `μ` of
`n`. -/
theorem trace_eq_of_cycleBlock_values {n : ℕ} {τ τ' : stage R q n →ₗ[R] M}
    (hτ : ∀ x y, τ (x * y) = τ (y * x)) (hτ' : ∀ x y, τ' (x * y) = τ' (y * x))
    (h : ∀ μ : n.Partition, τ ⟨cycleWordPart q μ, cycleWordPart_mem_stage μ⟩ =
      τ' ⟨cycleWordPart q μ, cycleWordPart_mem_stage μ⟩) :
    τ = τ' := by
  -- The commutators of the stage and the words `ζ_μ` span a submodule containing the stage.
  set C : Submodule R (InfiniteTypeAHeckeAlgebra R q) :=
    Submodule.span R {z | ∃ x ∈ stage R q n, ∃ y ∈ stage R q n, x * y - y * x = z} ⊔
      Submodule.span R (Set.range (cycleWordPart q : n.Partition → _))
  have hC : ∀ x ∈ stage R q n, x ∈ C := fun x hx ↦ by
    rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply]
    refine map_eq_zero_of_mem_stage (fun x hx y hy ↦ ?_) (fun μ ↦ ?_) hx
    · rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
      exact Submodule.mem_sup_left (Submodule.subset_span ⟨x, hx, y, hy, rfl⟩)
    · rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact Submodule.mem_sup_right (Submodule.subset_span ⟨μ, rfl⟩)
  -- That submodule lies in the image of the locus where the two functionals agree.
  have hCK : C ≤ (LinearMap.eqLocus τ τ').map (stage R q n).val.toLinearMap := by
    refine sup_le (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)
    · rintro _ ⟨x, hx, y, hy, rfl⟩
      refine ⟨⟨x, hx⟩ * ⟨y, hy⟩ - ⟨y, hy⟩ * ⟨x, hx⟩, LinearMap.mem_eqLocus.2 ?_, rfl⟩
      rw [map_sub, map_sub, hτ, hτ', sub_self, sub_self]
    · rintro _ ⟨μ, rfl⟩
      exact ⟨⟨cycleWordPart q μ, cycleWordPart_mem_stage μ⟩, h μ, rfl⟩
  ext x
  obtain ⟨y, hy, hyx⟩ := hCK (hC x x.2)
  rw [← Subtype.ext hyx]
  exact hy

end Trace

end InfiniteTypeAHeckeAlgebra

end TauCeti
