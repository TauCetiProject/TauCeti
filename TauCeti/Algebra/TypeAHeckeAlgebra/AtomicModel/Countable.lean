/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.Tannery
public import Mathlib.Analysis.Normed.Ring.InfiniteSum
public import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
public import TauCeti.Algebra.TypeAHeckeAlgebra.AtomicModel.CycleWord
public import TauCeti.Algebra.TypeAHeckeAlgebra.AtomicModel.Positivity
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Topology.Order.Basic

/-!
# Countable atomic models, infinite cycle-trace products, and the dust passage

For a linearly ordered alphabet `ι` and an absolutely summable weight family `p : ι → R` in a
complete normed commutative ring `R`, the matrix entries of `signedChecked pos q x` are uniformly
bounded (`exists_norm_signedChecked_single_apply_le`), so the diagonal series converges absolutely
and defines `countableAtomicTrace` (bundled over `ℂ` as `countableAtomicPositiveFunctional`).

Strict monotone inclusions intertwine `signedChecked` (`signedChecked_strictMono_single_apply`),
giving exhaustion by finite `atomicTrace`s (`tendsto_atomicTrace_finset`). Traciality, scaling on
`1` / `strandIncl` / `tailIncl`, block multiplicativity, `⋆`-positivity
(`countableAtomicTrace_star_mul_self_nonneg`), and the left- and right-slice Ocneanu
identifications (`countableAtomicTrace_eq_ocneanuTrace_of_leftSlice`,
`countableAtomicTrace_eq_ocneanuTrace_of_rightSlice`) pass to countable alphabets.

We also lift the cycle-word generating identity to infinite alphabets over a complete normed field
`K` (`countableAtomicTrace_cycleWord_hasProd`), evaluate the `Q = 1` signed power sums
(`countableAtomicTrace_cycleWord_of_sq_eq_one`), and prove the continuous-dust limit
`exp ((Q - 1) * γ * x)` (`tendsto_atomicTrace_dust_generating_function`).

## References

* Yu. A. Neretin, *Some remarks on traces on the infinite-dimensional Iwahori–Hecke algebra*,
  arXiv:2101.02133, §§1.6–1.7 and §3.1.
* H. Wenzl, *Hecke algebras of type A_n and subfactors*, Invent. Math. 92 (1988), 349–383, §3.
-/

public section

open Filter Function Finsupp
open scoped Topology ComplexOrder

namespace TauCeti

section StrictMonoAlphabet

variable {R : Type*} [CommRing R] {ι ι' : Type*} [LinearOrder ι] [LinearOrder ι']
  (pos : ι → Prop) [DecidablePred pos] (pos' : ι' → Prop) [DecidablePred pos'] {n : ℕ}

/-- A strictly monotone sign-preserving map intertwines `signedCheckedR` via `lmapDomain`. -/
theorem signedCheckedR_comp_lmapDomain_strictMono (s : R) {g : ι' → ι} (hg : StrictMono g)
    (hpos : ∀ a, pos (g a) ↔ pos' a) (j k : Fin n) :
    (signedCheckedR pos s j k).comp (lmapDomain R R (fun w : Fin n → ι' ↦ g ∘ w)) =
      (lmapDomain R R (fun w : Fin n → ι' ↦ g ∘ w)).comp (signedCheckedR pos' s j k) := by
  ext w : 2
  simp only [LinearMap.coe_comp, comp_apply, lsingle_apply]
  conv_lhs => rw [lmapDomain_apply, mapDomain_single]
  rw [signedCheckedR_single_one, signedCheckedR_single_one]
  simp only [comp_apply]
  by_cases hjk : w j = w k
  · simp only [hjk, ↓reduceIte, hpos (w k)]
    split_ifs <;> simp only [map_smul, lmapDomain_apply, mapDomain_single]
  · simp only [hjk, hg.injective.ne hjk, ↓reduceIte, hg.lt_iff_lt]
    split_ifs <;> simp only [map_sub, map_neg, map_smul, lmapDomain_apply, mapDomain_single,
      Function.comp_assoc]

end StrictMonoAlphabet

namespace TypeAHeckeAlgebra

section StrictMonoAndCycleDiag

variable {R : Type*} [CommRing R] {ι : Type*} [LinearOrder ι] (pos : ι → Prop) [DecidablePred pos]
  (q : Rˣ) {n : ℕ}

/-- **Alphabet embedding invariance of `signedChecked`** under strictly monotone sign-preserving
maps `g : ι' → ι`. -/
theorem signedChecked_strictMono_single_apply {ι' : Type*} [LinearOrder ι']
    (pos' : ι' → Prop) [DecidablePred pos'] {g : ι' → ι} (hg : StrictMono g)
    (hpos : ∀ a, pos (g a) ↔ pos' a) (x : TypeAHeckeAlgebra R q n) (w u : Fin n → ι') :
    signedChecked pos q x (single (g ∘ w) 1) (g ∘ u) =
      signedChecked pos' q x (single w 1) u := by
  set L := lmapDomain R R (fun v : Fin n → ι' ↦ g ∘ v)
  have hcomp : (signedChecked pos q x).comp L = L.comp (signedChecked pos' q x) := by
    have hx : x ∈ Algebra.adjoin R (Set.range (T (n := n) q)) := by rw [adjoin_range_T]; trivial
    induction hx using Algebra.adjoin_induction with
    | mem _ hy =>
      obtain ⟨i, rfl⟩ := hy
      rw [signedChecked_T, signedChecked_T, LinearMap.smul_comp, LinearMap.comp_smul,
        signedCheckedR_comp_lmapDomain_strictMono pos pos' (q : R) hg hpos]
    | algebraMap r =>
      ext v : 2; simp [L, AlgHom.commutes, Module.algebraMap_end_apply]
    | add _ _ _ _ hx hy => rw [map_add, map_add, LinearMap.add_comp, LinearMap.comp_add, hx, hy]
    | mul _ _ _ _ hx hy =>
      rw [map_mul, map_mul, Module.End.mul_eq_comp, Module.End.mul_eq_comp, LinearMap.comp_assoc,
        hy, ← LinearMap.comp_assoc, hx, LinearMap.comp_assoc]
  have hw := LinearMap.congr_fun hcomp (single w 1)
  simp only [LinearMap.coe_comp, comp_apply, L, lmapDomain_apply, mapDomain_single] at hw
  rw [hw, mapDomain_apply_of_injective hg.injective.comp_left]

/-- **Cycle-word diagonal recursion across a prepended first strand.** -/
theorem signedChecked_cycleWord_succ_cons_apply {m : ℕ} (a : ι) (w : Fin (m + 1) → ι) :
    signedChecked pos q (cycleWord q (m + 2)) (single (Fin.cons a w) 1) (Fin.cons a w) =
      signedChecked pos q (cycleWord q (m + 1)) (single w 1) w *
        (if a = w 0 then (if pos (w 0) then (q : R) ^ 2 else -1)
          else if a < w 0 then (q : R) ^ 2 - 1 else 0) := by
  rw [← tailIncl_cycleWord_mul_smul_T_zero m, mul_smul_comm, map_smul, LinearMap.smul_apply,
    Finsupp.smul_apply, smul_eq_mul, signedChecked_tailIncl_mul_T_zero_single_cons_apply]
  linear_combination (signedChecked pos q (cycleWord q (m + 1)) (single w 1) w *
    (if a = w 0 then (if pos (w 0) then (q : R) ^ 2 else -1)
      else if a < w 0 then (q : R) ^ 2 - 1 else 0)) * Units.mul_inv q

/-- At `(q : R) ^ 2 = 1`, the diagonal entry of `cycleWord (m + 1)` vanishes off constant words. -/
theorem signedChecked_cycleWord_single_apply_of_sq_eq_one (hq : (q : R) ^ 2 = 1) :
    ∀ {m : ℕ} (w : Fin (m + 1) → ι),
      signedChecked pos q (cycleWord q (m + 1)) (single w 1) w =
        if ∀ i, w i = w 0 then (if pos (w 0) then (1 : R) else -1) ^ m else 0
  | 0, w => by simp [Fin.forall_fin_one]
  | m + 1, w => by
    conv_lhs => rw [← Fin.cons_self_tail w]
    rw [signedChecked_cycleWord_succ_cons_apply,
      signedChecked_cycleWord_single_apply_of_sq_eq_one hq (Fin.tail w), hq, sub_self, ite_self]
    by_cases hall : ∀ i : Fin (m + 2), w i = w 0
    · have h0 : w 0 = Fin.tail w 0 := (hall (0 : Fin (m + 1)).succ).symm
      have hj : ∀ j : Fin (m + 1), Fin.tail w j = Fin.tail w 0 := fun j ↦ (hall j.succ).trans h0
      rw [ite_eq_left hj, ite_eq_left h0, ite_eq_left hall, ← h0, pow_succ]
    · rw [ite_eq_right hall]
      by_cases h0 : w 0 = Fin.tail w 0
      · rw [ite_eq_right (fun hj ↦ hall (Fin.forall_fin_succ.mpr ⟨rfl,
          fun j ↦ (hj j).trans h0.symm⟩)), zero_mul]
      · rw [ite_eq_right h0, mul_zero]

/-- **Cycle-word atomic trace at `Q = 1`** equals the signed `(m + 1)`-th power sum. -/
theorem atomicTrace_cycleWord_of_sq_eq_one [Fintype ι] (hq : (q : R) ^ 2 = 1) (p : ι → R)
    (m : ℕ) :
    atomicTrace pos q p (m + 1) (cycleWord q (m + 1)) =
      ∑ a, (if pos a then (1 : R) else -1) ^ m * p a ^ (m + 1) := by
  classical
  rw [atomicTrace_eq_sum]
  simp_rw [signedChecked_cycleWord_single_apply_of_sq_eq_one pos q hq, ite_mul, zero_mul,
    ← Finset.sum_filter]
  refine Finset.sum_bij' (fun w _ ↦ w 0) (fun a _ _ ↦ a) (fun _ _ ↦ Finset.mem_univ _)
    (fun _ _ ↦ Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun _ ↦ rfl⟩)
    (fun w hw ↦ funext fun i ↦ ((Finset.mem_filter.mp hw).2 i).symm) (fun _ _ ↦ rfl) fun w hw ↦ ?_
  simp [fun i ↦ congrArg p ((Finset.mem_filter.mp hw).2 i)]

end StrictMonoAndCycleDiag

section NormBounds

variable {R : Type*} [NormedCommRing R] {ι : Type*} [LinearOrder ι] (pos : ι → Prop)
  [DecidablePred pos] (q : Rˣ) {n : ℕ}

private noncomputable def wordL1 {α : Type*} (v : α →₀ R) : ℝ := v.sum fun _ r ↦ ‖r‖

private theorem wordL1_add_le {α : Type*} (v₁ v₂ : α →₀ R) :
    wordL1 (v₁ + v₂) ≤ wordL1 v₁ + wordL1 v₂ := by
  classical
  dsimp only [wordL1]
  rw [Finsupp.sum_of_support_subset _ v₁.support_add _ (fun _ _ ↦ norm_zero),
    Finsupp.sum_of_support_subset v₁ Finset.subset_union_left _ (fun _ _ ↦ norm_zero),
    Finsupp.sum_of_support_subset v₂ Finset.subset_union_right _ (fun _ _ ↦ norm_zero),
    ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun u _ ↦ norm_add_le (v₁ u) (v₂ u)

private theorem wordL1_smul_le {α : Type*} (r : R) (v : α →₀ R) :
    wordL1 (r • v) ≤ ‖r‖ * wordL1 v := by
  dsimp only [wordL1]
  rw [Finsupp.sum_of_support_subset _ Finsupp.support_smul _ (fun _ _ ↦ norm_zero),
    Finsupp.sum, Finset.mul_sum]
  exact Finset.sum_le_sum fun u _ ↦ norm_mul_le r (v u)

private theorem wordL1_linearMap_le {α : Type*} (f : (α →₀ R) →ₗ[R] (α →₀ R)) {C : ℝ}
    (hC : ∀ w, wordL1 (f (single w 1)) ≤ C) (v : α →₀ R) : wordL1 (f v) ≤ C * wordL1 v := by
  classical
  have hsum : ∀ (s : Finset α) (g : α → α →₀ R), wordL1 (∑ b ∈ s, g b) ≤ ∑ b ∈ s, wordL1 (g b) :=
    fun s g ↦ Finset.induction (by simp [wordL1]) (fun b s hbs ih ↦ by
      rw [Finset.sum_insert hbs, Finset.sum_insert hbs]
      exact (wordL1_add_le _ _).trans (add_le_add_right ih _)) s
  conv_lhs => rw [← Finsupp.sum_single v, Finsupp.sum, map_sum]
  calc wordL1 (∑ u ∈ v.support, f (single u (v u)))
      ≤ ∑ u ∈ v.support, wordL1 (f (single u (v u))) := hsum _ _
    _ ≤ ∑ u ∈ v.support, ‖v u‖ * C := Finset.sum_le_sum fun u _ ↦ by
        rw [← smul_single_one, map_smul]
        exact (wordL1_smul_le _ _).trans (mul_le_mul_of_nonneg_left (hC u) (norm_nonneg _))
    _ = C * wordL1 v := by rw [← Finset.sum_mul, mul_comm]; rfl

/-- **Uniform matrix-entry bound for `signedChecked`** across all words `w, u : Fin n → ι`. -/
theorem exists_norm_signedChecked_single_apply_le (x : TypeAHeckeAlgebra R q n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w u : Fin n → ι, ‖signedChecked pos q x (single w 1) u‖ ≤ C := by
  classical
  suffices h : ∃ B : ℝ, 0 ≤ B ∧ ∀ w : Fin n → ι, wordL1 (signedChecked pos q x (single w 1)) ≤ B by
    obtain ⟨B, hB0, hB⟩ := h
    refine ⟨B, hB0, fun w u ↦ le_trans ?_ (hB w)⟩
    by_cases hu : u ∈ (signedChecked pos q x (single w 1)).support
    · exact Finset.single_le_sum (fun _ _ ↦ norm_nonneg _) hu
    · rw [Finsupp.notMem_support_iff.mp hu, norm_zero]
      exact Finset.sum_nonneg fun _ _ ↦ norm_nonneg _
  have h1 (u : Fin n → ι) : wordL1 (single u (1 : R)) ≤ ‖(1 : R)‖ := by
    simp [wordL1, Finsupp.sum_single_index]
  have hs (r : R) (u : Fin n → ι) : wordL1 (r • single u (1 : R)) ≤ ‖r‖ * ‖(1 : R)‖ :=
    (wordL1_smul_le _ _).trans (mul_le_mul_of_nonneg_left (h1 u) (norm_nonneg _))
  have hneg (v : (Fin n → ι) →₀ R) : wordL1 (-v) = wordL1 v := by
    simp [wordL1, Finsupp.sum_neg_index]
  have hx : x ∈ Algebra.adjoin R (Set.range (T (n := n) q)) := by rw [adjoin_range_T]; trivial
  induction hx using Algebra.adjoin_induction with
  | mem _ hy =>
    obtain ⟨i, rfl⟩ := hy
    refine ⟨‖((q⁻¹ : Rˣ) : R)‖ * ((‖(q : R) ^ 2‖ + 1 + ‖(q : R) ^ 2 - 1‖ + ‖(q : R)‖) *
        ‖(1 : R)‖), by positivity, fun w ↦ ?_⟩
    rw [signedChecked_T, LinearMap.smul_apply]
    refine (wordL1_smul_le _ _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
    rw [signedCheckedR_single_one]
    have hnn := norm_nonneg (1 : R)
    split_ifs
    · exact (hs _ w).trans (by nlinarith [norm_nonneg ((q : R) ^ 2 - 1), norm_nonneg (q : R)])
    · rw [neg_smul, one_smul, hneg]
      exact (h1 w).trans (by
        nlinarith [norm_nonneg ((q : R) ^ 2), norm_nonneg ((q : R) ^ 2 - 1), norm_nonneg (q : R)])
    · rw [sub_eq_add_neg]
      refine (wordL1_add_le _ _).trans ?_
      rw [hneg]
      exact (add_le_add (hs _ _) (hs _ _)).trans (by nlinarith [norm_nonneg ((q : R) ^ 2)])
    · rw [hneg]
      exact (hs _ _).trans (by nlinarith [norm_nonneg ((q : R) ^ 2), norm_nonneg ((q : R) ^ 2 - 1)])
  | algebraMap r =>
    exact ⟨‖r‖ * ‖(1 : R)‖, by positivity, fun w ↦ by
      rw [AlgHom.commutes, Module.algebraMap_end_apply]; exact hs r w⟩
  | add _ _ _ _ hx hy =>
    obtain ⟨Bx, hBx0, hBx⟩ := hx; obtain ⟨By, hBy0, hBy⟩ := hy
    exact ⟨Bx + By, add_nonneg hBx0 hBy0, fun w ↦ by
      rw [map_add, LinearMap.add_apply]
      exact (wordL1_add_le _ _).trans (add_le_add (hBx w) (hBy w))⟩
  | mul _ _ _ _ hx hy =>
    obtain ⟨Bx, hBx0, hBx⟩ := hx; obtain ⟨By, hBy0, hBy⟩ := hy
    exact ⟨Bx * By, mul_nonneg hBx0 hBy0, fun w ↦ by
      rw [map_mul, mul_apply_eq_comp]
      exact (wordL1_linearMap_le _ hBx _).trans (mul_le_mul_of_nonneg_left (hBy w) hBx0)⟩

/-- **Sharp diagonal norm bound on cycle words.** -/
theorem norm_signedChecked_cycleWord_single_apply_le :
    ∀ {m : ℕ} (w : Fin (m + 1) → ι),
      ‖signedChecked pos q (cycleWord q (m + 1)) (single w 1) w‖ ≤
        ‖(1 : R)‖ * max 1 (max ‖(q : R) ^ 2‖ ‖(q : R) ^ 2 - 1‖) ^ m
  | 0, w => by rw [cycleWord_one, map_one, one_apply_eq_self, single_eq_same, pow_zero, mul_one]
  | m + 1, w => by
    set M : ℝ := max 1 (max ‖(q : R) ^ 2‖ ‖(q : R) ^ 2 - 1‖)
    conv_lhs => rw [← Fin.cons_self_tail w]
    rw [signedChecked_cycleWord_succ_cons_apply, pow_succ M m, ← mul_assoc]
    have ih := norm_signedChecked_cycleWord_single_apply_le (Fin.tail w)
    set z := signedChecked pos q (cycleWord q (m + 1)) (single (Fin.tail w) 1) (Fin.tail w)
    refine le_trans ?_ (mul_le_mul_of_nonneg_right ih (by positivity))
    split_ifs
    · exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left
        ((le_max_left _ _).trans (le_max_right _ _)) (norm_nonneg z))
    · rw [mul_neg, mul_one, norm_neg]; exact le_mul_of_one_le_right (norm_nonneg z) (le_max_left ..)
    · exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left
        ((le_max_right _ _).trans (le_max_right _ _)) (norm_nonneg z))
    · rw [mul_zero, norm_zero]; positivity

end NormBounds

section CountableTrace

variable {R : Type*} [NormedCommRing R] [CompleteSpace R] {ι : Type*} [LinearOrder ι]
  (pos : ι → Prop) [DecidablePred pos] (q : Rˣ)

omit [CompleteSpace R] [LinearOrder ι] in
/-- If `‖p a‖` is summable, then `∏ i : Fin n, ‖p (w i)‖` is summable over `w : Fin n → ι`. -/
theorem summable_norm_prod_apply {p : ι → R} (hp : Summable fun a ↦ ‖p a‖) :
    ∀ n : ℕ, Summable fun w : Fin n → ι ↦ ∏ i, ‖p (w i)‖
  | 0 => (hasSum_fintype _).summable
  | n + 1 => by
    rw [← (Fin.consEquiv (fun _ : Fin (n + 1) ↦ ι)).summable_iff]
    exact (hp.mul_of_nonneg (summable_norm_prod_apply hp n) (fun _ ↦ norm_nonneg _)
      (fun _ ↦ Finset.prod_nonneg fun _ _ ↦ norm_nonneg _)).congr fun _ ↦ by
      simp [Fin.prod_univ_succ]

omit [CompleteSpace R] [LinearOrder ι] in
/-- The `ℓ¹` sum of word weights `∏ i, ‖p (w i)‖` over `Fin n → ι` is `(∑' a, ‖p a‖) ^ n`. -/
theorem tsum_norm_prod_apply {p : ι → R} (hp : Summable fun a ↦ ‖p a‖) :
    ∀ n : ℕ, (∑' w : Fin n → ι, ∏ i, ‖p (w i)‖) = (∑' a, ‖p a‖) ^ n
  | 0 => by simp
  | n + 1 => by
    rw [← (Fin.consEquiv (fun _ : Fin (n + 1) ↦ ι)).tsum_eq]
    have heq : (fun aw : ι × (Fin n → ι) ↦
        ∏ i : Fin (n + 1), ‖p (Fin.consEquiv (fun _ : Fin (n + 1) ↦ ι) aw i)‖) =
        fun aw ↦ ‖p aw.1‖ * ∏ i : Fin n, ‖p (aw.2 i)‖ := by ext ⟨a, w⟩; simp [Fin.prod_univ_succ]
    rw [heq, ← tsum_mul_tsum_of_summable_norm (hp.congr fun a ↦ (norm_norm (p a)).symm)
      ((summable_norm_prod_apply hp n).congr fun w ↦
        (Real.norm_of_nonneg (Finset.prod_nonneg fun _ _ ↦ norm_nonneg _)).symm),
      tsum_norm_prod_apply hp n, pow_succ']

omit [CompleteSpace R] in
/-- Absolute summability of the weighted diagonal coefficients of `signedChecked pos q x`. -/
theorem summable_norm_signedChecked_mul_prod {p : ι → R} (hp : Summable fun a ↦ ‖p a‖) (n : ℕ)
    (x : TypeAHeckeAlgebra R q n) :
    Summable fun w : Fin n → ι ↦ ‖signedChecked pos q x (single w 1) w * ∏ i, p (w i)‖ := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_signedChecked_single_apply_le pos q x
  refine ((summable_norm_prod_apply hp n).mul_left C).of_nonneg_of_le (fun _ ↦ norm_nonneg _)
    fun w ↦ ?_
  rcases eq_or_ne n 0 with rfl | hn
  · simpa using hC w w
  · exact (norm_mul_le _ _).trans (mul_le_mul (hC w w)
      (Finset.norm_prod_le' _ ⟨⟨0, Nat.pos_of_ne_zero hn⟩, Finset.mem_univ _⟩ _)
      (norm_nonneg _) hC0)

/-- **The countable atomic trace** on `TypeAHeckeAlgebra R q n` for an absolutely summable weight
family `p : ι → R`. -/
noncomputable def countableAtomicTrace (p : ι → R) (hp : Summable fun a ↦ ‖p a‖) (n : ℕ) :
    TypeAHeckeAlgebra R q n →ₗ[R] R where
  toFun x := ∑' w : Fin n → ι, signedChecked pos q x (single w 1) w * ∏ i, p (w i)
  map_add' x y := by
    simp only [map_add, LinearMap.add_apply, Finsupp.add_apply, add_mul]
    exact (summable_norm_signedChecked_mul_prod pos q hp n x).of_norm.tsum_add
      (summable_norm_signedChecked_mul_prod pos q hp n y).of_norm
  map_smul' r x := by
    simp only [map_smul, LinearMap.smul_apply, Finsupp.smul_apply, smul_eq_mul, mul_assoc,
      RingHom.id_apply]
    exact (summable_norm_signedChecked_mul_prod pos q hp n x).of_norm.tsum_mul_left r

theorem countableAtomicTrace_apply (p : ι → R) (hp : Summable fun a ↦ ‖p a‖) (n : ℕ)
    (x : TypeAHeckeAlgebra R q n) :
    countableAtomicTrace pos q p hp n x =
      ∑' w : Fin n → ι, signedChecked pos q x (single w 1) w * ∏ i, p (w i) :=
  (rfl)

/-- On a finite alphabet, `countableAtomicTrace` agrees with `atomicTrace`. -/
theorem countableAtomicTrace_eq_atomicTrace [Finite ι] (p : ι → R)
    (hp : Summable fun a ↦ ‖p a‖) (n : ℕ) (x : TypeAHeckeAlgebra R q n) :
    countableAtomicTrace pos q p hp n x = atomicTrace pos q p n x := by
  cases nonempty_fintype ι
  rw [countableAtomicTrace_apply, tsum_fintype, atomicTrace_eq_sum]

/-- **Exhaustion of `countableAtomicTrace` by finite sub-alphabets** along `atTop`. -/
theorem tendsto_atomicTrace_finset (p : ι → R) (hp : Summable fun a ↦ ‖p a‖) (n : ℕ)
    (x : TypeAHeckeAlgebra R q n) :
    Tendsto (fun s : Finset ι ↦ atomicTrace (fun a : s ↦ pos a) q (fun a : s ↦ p a) n x)
      atTop (𝓝 (countableAtomicTrace pos q p hp n x)) := by
  classical
  have hpi : Tendsto (fun s : Finset ι ↦ Fintype.piFinset fun _ : Fin n ↦ s) atTop atTop :=
    tendsto_atTop_atTop.mpr fun T ↦ ⟨T.biUnion fun w ↦ Finset.univ.image w,
      fun s hs w hw ↦ Fintype.mem_piFinset.mpr fun i ↦
        hs (Finset.mem_biUnion.mpr ⟨w, hw, Finset.mem_image_of_mem w (Finset.mem_univ i)⟩)⟩
  refine ((summable_norm_signedChecked_mul_prod pos q hp n x).of_norm.hasSum.comp hpi).congr
    fun s ↦ ?_
  rw [comp_apply, atomicTrace_eq_sum]; symm
  refine Finset.sum_bij (fun (w : Fin n → s) _ ↦ Subtype.val ∘ w)
    (fun w _ ↦ Fintype.mem_piFinset.mpr fun i ↦ (w i).2)
    (fun _ _ _ _ h ↦ funext fun i ↦ Subtype.ext (congrFun h i))
    (fun w hw ↦ ⟨fun i ↦ ⟨w i, Fintype.mem_piFinset.mp hw i⟩, Finset.mem_univ _, rfl⟩) fun w _ ↦ ?_
  rw [signedChecked_strictMono_single_apply pos q (fun a : s ↦ pos a)
    (fun _ _ h ↦ h) (fun _ ↦ Iff.rfl)]; rfl

/-- The countable atomic trace is tracial. -/
theorem countableAtomicTrace_mul_comm (p : ι → R) (hp : Summable fun a ↦ ‖p a‖) {n : ℕ}
    (x y : TypeAHeckeAlgebra R q n) :
    countableAtomicTrace pos q p hp n (x * y) = countableAtomicTrace pos q p hp n (y * x) :=
  tendsto_nhds_unique (tendsto_atomicTrace_finset pos q p hp n (x * y)) <|
    (tendsto_atomicTrace_finset pos q p hp n (y * x)).congr fun s ↦
      (atomicTrace_mul_comm (fun a : s ↦ pos a) q (fun a : s ↦ p a) x y).symm

/-- The countable atomic trace of `1` on `n` strands is `(∑' a, p a) ^ n`. -/
@[simp]
theorem countableAtomicTrace_one (p : ι → R) (hp : Summable fun a ↦ ‖p a‖) (n : ℕ) :
    countableAtomicTrace pos q p hp n 1 = (∑' a, p a) ^ n :=
  tendsto_nhds_unique (tendsto_atomicTrace_finset pos q p hp n 1) <|
    (hp.of_norm.hasSum.pow n).congr fun s ↦ by
      rw [atomicTrace_one, Finset.univ_eq_attach, s.sum_attach p]

/-- Adding an uncrossed last strand multiplies `countableAtomicTrace` by `∑' a, p a`. -/
@[simp]
theorem countableAtomicTrace_strandIncl (p : ι → R) (hp : Summable fun a ↦ ‖p a‖) {n : ℕ}
    (x : TypeAHeckeAlgebra R q n) :
    countableAtomicTrace pos q p hp (n + 1) (strandIncl R q n x) =
      countableAtomicTrace pos q p hp n x * ∑' a, p a :=
  tendsto_nhds_unique (tendsto_atomicTrace_finset pos q p hp (n + 1) (strandIncl R q n x)) <|
    ((tendsto_atomicTrace_finset pos q p hp n x).mul hp.of_norm.hasSum).congr fun s ↦ by
      rw [← Finset.sum_attach s p, ← Finset.univ_eq_attach, ← atomicTrace_strandIncl]

/-- Adding an uncrossed first strand multiplies `countableAtomicTrace` by `∑' a, p a`. -/
@[simp]
theorem countableAtomicTrace_tailIncl (p : ι → R) (hp : Summable fun a ↦ ‖p a‖) {n : ℕ}
    (x : TypeAHeckeAlgebra R q n) :
    countableAtomicTrace pos q p hp (n + 1) (tailIncl q n x) =
      countableAtomicTrace pos q p hp n x * ∑' a, p a :=
  tendsto_nhds_unique (tendsto_atomicTrace_finset pos q p hp (n + 1) (tailIncl q n x)) <|
    ((tendsto_atomicTrace_finset pos q p hp n x).mul hp.of_norm.hasSum).congr fun s ↦ by
      rw [← Finset.sum_attach s p, ← Finset.univ_eq_attach, ← atomicTrace_tailIncl]

/-- **Block multiplicativity of `countableAtomicTrace`** on disjoint consecutive strand blocks. -/
theorem countableAtomicTrace_castAdd_mul_natAdd (p : ι → R) (hp : Summable fun a ↦ ‖p a‖)
    {m n : ℕ} (x : TypeAHeckeAlgebra R q m) (y : TypeAHeckeAlgebra R q n) :
    countableAtomicTrace pos q p hp (m + n) (castAdd R q m n x * natAdd R q m n y) =
      countableAtomicTrace pos q p hp m x * countableAtomicTrace pos q p hp n y :=
  tendsto_nhds_unique
    (tendsto_atomicTrace_finset pos q p hp (m + n) (castAdd R q m n x * natAdd R q m n y)) <|
    ((tendsto_atomicTrace_finset pos q p hp m x).mul
      (tendsto_atomicTrace_finset pos q p hp n y)).congr fun s ↦
        (atomicTrace_castAdd_mul_natAdd (fun a : s ↦ pos a) q (fun a : s ↦ p a) x y).symm

/-- **Positivity of countable atomic traces** for nonnegative weights over a complete normed
`StarOrderedRing` with `OrderClosedTopology`. -/
theorem countableAtomicTrace_star_mul_self_nonneg [PartialOrder R] [StarRing R] [StarOrderedRing R]
    [OrderClosedTopology R] [Fact (IsSelfAdjoint (q : R))] {p : ι → R}
    (hp : Summable fun a ↦ ‖p a‖) (hp0 : ∀ a, 0 ≤ p a) {n : ℕ} (x : TypeAHeckeAlgebra R q n) :
    0 ≤ countableAtomicTrace pos q p hp n (star x * x) :=
  ge_of_tendsto (tendsto_atomicTrace_finset pos q p hp n (star x * x)) <|
    Eventually.of_forall fun s ↦
      atomicTrace_star_mul_self_nonneg (fun a : s ↦ pos a) q (fun a : s ↦ hp0 a) x

/-- The complex countable atomic trace on `n` strands bundled as a `StarPositiveFunctional`. -/
noncomputable def countableAtomicPositiveFunctional (q : ℂˣ) [Fact (IsSelfAdjoint (q : ℂ))]
    {p : ι → ℂ} (hp : Summable fun a ↦ ‖p a‖) (hp0 : ∀ a, 0 ≤ p a) (n : ℕ) :
    StarPositiveFunctional (TypeAHeckeAlgebra ℂ q n) where
  toLinearMap := countableAtomicTrace pos q p hp n
  square_nonneg := countableAtomicTrace_star_mul_self_nonneg pos q hp hp0

@[simp]
theorem countableAtomicPositiveFunctional_apply (q : ℂˣ) [Fact (IsSelfAdjoint (q : ℂ))]
    {p : ι → ℂ} (hp : Summable fun a ↦ ‖p a‖) (hp0 : ∀ a, 0 ≤ p a) (n : ℕ)
    (x : TypeAHeckeAlgebra ℂ q n) :
    countableAtomicPositiveFunctional pos q hp hp0 n x =
      countableAtomicTrace pos q p hp n x :=
  (rfl)

/-- **Cycle-word countable atomic trace at `Q = 1`** equals the signed `(m + 1)`-th power sum. -/
theorem countableAtomicTrace_cycleWord_of_sq_eq_one (hq : (q : R) ^ 2 = 1) (p : ι → R)
    (hp : Summable fun a ↦ ‖p a‖) (m : ℕ) :
    countableAtomicTrace pos q p hp (m + 1) (cycleWord q (m + 1)) =
      ∑' a, (if pos a then (1 : R) else -1) ^ m * p a ^ (m + 1) := by
  have hpow : Summable fun a ↦ ‖(if pos a then (1 : R) else -1) ^ m * p a ^ (m + 1)‖ := by
    refine (hp.mul_left (‖(1 : R)‖ * (∑' b, ‖p b‖) ^ m)).of_nonneg_of_le
      (fun _ ↦ norm_nonneg _) fun a ↦ ?_
    have h1 : ‖(if pos a then (1 : R) else -1) ^ m‖ = ‖(1 : R)‖ := by split_ifs <;> simp
    have h2 : ‖p a ^ (m + 1)‖ ≤ (∑' b, ‖p b‖) ^ m * ‖p a‖ :=
      (norm_pow_le' (p a) (Nat.succ_pos m)).trans <| by
        rw [pow_succ]; gcongr; exact hp.le_tsum a fun _ _ ↦ norm_nonneg _
    exact (norm_mul_le _ _).trans <| by
      rw [h1, mul_assoc]; exact mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
  refine tendsto_nhds_unique
    (tendsto_atomicTrace_finset pos q p hp (m + 1) (cycleWord q (m + 1))) <|
    hpow.of_norm.hasSum.congr fun s ↦ ?_
  rw [← Finset.sum_attach s (fun a ↦ (if pos a then (1 : R) else -1) ^ m * p a ^ (m + 1)),
    ← Finset.univ_eq_attach, ← atomicTrace_cycleWord_of_sq_eq_one (fun a : s ↦ pos a) q hq]

private theorem tsum_slice_eq {p : ι → R} (hp : Summable fun a ↦ ‖p a‖) (b : ι)
    (P : ι → Prop) [DecidablePred P] (hPb : ¬ P b) :
    (Summable fun a ↦ (if a = b then (if pos b then (q : R) ^ 2 else -1)
        else if P a then (q : R) ^ 2 - 1 else 0) * p a) ∧
      (∑' a, (if a = b then (if pos b then (q : R) ^ 2 else -1)
        else if P a then (q : R) ^ 2 - 1 else 0) * p a) =
        (if pos b then (q : R) ^ 2 else -1) * p b +
          ((q : R) ^ 2 - 1) * ∑' a, if P a then p a else 0 := by
  classical
  have h₁ : Summable fun a ↦ if a = b then (if pos b then (q : R) ^ 2 else -1) * p b else 0 :=
    summable_of_ne_finset_zero (s := {b}) fun _ ha ↦ by simp [Finset.notMem_singleton.mp ha]
  have h_ite : Summable fun a ↦ ‖if P a then p a else 0‖ :=
    hp.of_nonneg_of_le (fun _ ↦ norm_nonneg _) fun _ ↦ by split_ifs <;> simp
  have h₂ : Summable fun a ↦ ((q : R) ^ 2 - 1) * if P a then p a else 0 := h_ite.of_norm.mul_left _
  have hpt : (fun a ↦ (if a = b then (if pos b then (q : R) ^ 2 else -1)
        else if P a then (q : R) ^ 2 - 1 else 0) * p a) =
      fun a ↦ (if a = b then (if pos b then (q : R) ^ 2 else -1) * p b else 0) +
        ((q : R) ^ 2 - 1) * (if P a then p a else 0) := by
    ext a; by_cases hab : a = b
    · subst hab; simp [hPb]
    · by_cases hPa : P a <;> simp [hab, hPa]
  rw [hpt]
  exact ⟨h₁.add h₂, by rw [h₁.tsum_add h₂, tsum_ite_eq, h_ite.of_norm.tsum_mul_left]⟩

omit [LinearOrder ι] in
private theorem tsum_fin_equiv {n : ℕ} (e : (Fin n → ι) × ι ≃ (Fin (n + 1) → ι))
    {f : (Fin (n + 1) → ι) → R} (hf : Summable f) :
    (∑' u, f u) = ∑' w : Fin n → ι, ∑' a : ι, f (e (w, a)) :=
  (e.tsum_eq f).symm.trans (Summable.tsum_prod (e.summable_iff.mpr hf))

/-- **Countable first-site (left-slice) Markov rule** for `countableAtomicTrace`. -/
theorem countableAtomicTrace_T_zero_mul_tailIncl (p : ι → R) (hp : Summable fun a ↦ ‖p a‖)
    {z : R}
    (hz : ∀ b, (if pos b then (q : R) ^ 2 else -1) * p b +
      ((q : R) ^ 2 - 1) * (∑' a, if a < b then p a else 0) = q * z)
    {n : ℕ} (x : TypeAHeckeAlgebra R q (n + 1)) :
    countableAtomicTrace pos q p hp (n + 2) (T q (0 : Fin (n + 1)) * tailIncl q (n + 1) x) =
      z * countableAtomicTrace pos q p hp (n + 1) x := by
  rw [countableAtomicTrace_mul_comm, countableAtomicTrace_apply,
    tsum_fin_equiv ((Equiv.prodComm ..).trans (Fin.consEquiv fun _ : Fin (n + 2) ↦ ι))
      (summable_norm_signedChecked_mul_prod pos q hp (n + 2) _).of_norm,
    countableAtomicTrace_apply,
    ← (summable_norm_signedChecked_mul_prod pos q hp (n + 1) x).of_norm.tsum_mul_left]
  congr 1 with w
  have hsl := tsum_slice_eq pos q hp (w 0) (· < w 0) (lt_irrefl _)
  simp only [Equiv.trans_apply, Equiv.prodComm_apply, Prod.swap_prod_mk, Fin.consEquiv_apply,
    signedChecked_tailIncl_mul_T_zero_single_cons_apply, Fin.prod_univ_succ (n := n + 1),
    Fin.cons_zero, Fin.cons_succ]
  rw [show (fun a ↦ _) = fun a ↦ (((q⁻¹ : Rˣ) : R) * signedChecked pos q x (single w 1) w *
      ∏ i, p (w i)) * ((if a = w 0 then (if pos (w 0) then (q : R) ^ 2 else -1)
        else if a < w 0 then (q : R) ^ 2 - 1 else 0) * p a) from funext fun _ ↦ by ring,
    hsl.1.tsum_mul_left, hsl.2, hz (w 0)]
  linear_combination (z * signedChecked pos q x (single w 1) w * ∏ i, p (w i)) * Units.inv_mul q

/-- **Countable atomic trace with scalar left slice is the Ocneanu trace.** -/
theorem countableAtomicTrace_eq_ocneanuTrace_of_leftSlice (p : ι → R)
    (hp : Summable fun a ↦ ‖p a‖) {z : R} (hp1 : ∑' a, p a = 1)
    (hz : ∀ b, (if pos b then (q : R) ^ 2 else -1) * p b +
      ((q : R) ^ 2 - 1) * (∑' a, if a < b then p a else 0) = q * z)
    {n : ℕ} (x : TypeAHeckeAlgebra R q n) :
    countableAtomicTrace pos q p hp n x =
      InfiniteTypeAHeckeAlgebra.ocneanuTrace R q z (toInfinite R q n x) :=
  eq_ocneanuTrace_toInfinite_of_T_zero_mul_tailIncl (countableAtomicTrace pos q p hp)
    (by simp) (by simp [hp1]) (fun _ ↦ countableAtomicTrace_mul_comm pos q p hp)
    (fun _ _ ↦ countableAtomicTrace_castAdd_mul_natAdd pos q p hp)
    (fun _ ↦ countableAtomicTrace_T_zero_mul_tailIncl pos q p hp hz) n x

/-- **Countable last-site (right-slice) Markov rule** for `countableAtomicTrace`. -/
theorem countableAtomicTrace_strandIncl_mul_T_last (p : ι → R) (hp : Summable fun a ↦ ‖p a‖)
    {z : R}
    (hz : ∀ b, (if pos b then (q : R) ^ 2 else -1) * p b +
      ((q : R) ^ 2 - 1) * (∑' c, if b < c then p c else 0) = q * z)
    {n : ℕ} (x : TypeAHeckeAlgebra R q (n + 1)) :
    countableAtomicTrace pos q p hp (n + 2)
        (strandIncl R q (n + 1) x * T q (Fin.last n)) =
      z * countableAtomicTrace pos q p hp (n + 1) x := by
  have hj : BraidGroup.strand (Fin.last n : Fin (n + 2 - 1)) = (Fin.last n).castSucc :=
    Fin.ext (by simp)
  have hk : BraidGroup.strandSucc (Fin.last n : Fin (n + 2 - 1)) = Fin.last (n + 1) :=
    Fin.ext (by simp)
  have hdiag (w : Fin (n + 1) → ι) (c : ι) :
      signedChecked pos q (strandIncl R q (n + 1) x * T q (Fin.last n))
          (single (Fin.snoc w c) 1) (Fin.snoc w c) =
        ((q⁻¹ : Rˣ) : R) * signedChecked pos q x (single w 1) w *
          (if c = w (Fin.last n) then (if pos (w (Fin.last n)) then (q : R) ^ 2 else -1)
            else if w (Fin.last n) < c then (q : R) ^ 2 - 1 else 0) := by
    have hswap : Fin.snoc w c ∘ Equiv.swap (Fin.last n).castSucc (Fin.last (n + 1)) =
        Fin.snoc (update w (Fin.last n) c) (w (Fin.last n)) := by
      rw [Equiv.comp_swap_eq_update]; simp [← Fin.snoc_update, Fin.update_snoc_last]
    simp only [map_mul, mul_apply_eq_comp, signedChecked_T, hj, hk, LinearMap.smul_apply,
      signedCheckedR_single_one, Fin.snoc_castSucc, Fin.snoc_last, hswap]
    rcases lt_trichotomy (w (Fin.last n)) c with h | rfl | h
    · simp only [h.ne, h.ne', h, ↓reduceIte, map_sub, map_smul, Finsupp.smul_apply,
        Finsupp.sub_apply, smul_eq_mul, signedChecked_strandIncl_single_snoc_apply_snoc]; ring
    · simp only [↓reduceIte, map_smul, Finsupp.smul_apply, smul_eq_mul,
        signedChecked_strandIncl_single_snoc_apply_snoc]; ring
    · simp only [h.ne, h.ne', h.not_gt, ↓reduceIte, map_neg, map_smul, Finsupp.smul_apply,
        Finsupp.neg_apply, smul_eq_mul, signedChecked_strandIncl_single_snoc_apply_snoc]; ring
  rw [countableAtomicTrace_apply,
    tsum_fin_equiv ((Equiv.prodComm ..).trans (Fin.snocEquiv fun _ : Fin (n + 2) ↦ ι))
      (summable_norm_signedChecked_mul_prod pos q hp (n + 2) _).of_norm,
    countableAtomicTrace_apply,
    ← (summable_norm_signedChecked_mul_prod pos q hp (n + 1) x).of_norm.tsum_mul_left]
  congr 1 with w
  have hsr := tsum_slice_eq pos q hp (w (Fin.last n)) (w (Fin.last n) < ·) (lt_irrefl _)
  simp only [Equiv.trans_apply, Equiv.prodComm_apply, Prod.swap_prod_mk, Fin.snocEquiv_apply,
    hdiag, Fin.prod_univ_castSucc (n := n + 1), Fin.snoc_castSucc, Fin.snoc_last]
  rw [show (fun c ↦ _) = fun c ↦ (((q⁻¹ : Rˣ) : R) * signedChecked pos q x (single w 1) w *
      ∏ i, p (w i)) * ((if c = w (Fin.last n) then (if pos (w (Fin.last n)) then (q : R) ^ 2
        else -1) else if w (Fin.last n) < c then (q : R) ^ 2 - 1 else 0) * p c) from
      funext fun _ ↦ by ring, hsr.1.tsum_mul_left, hsr.2, hz (w (Fin.last n))]
  linear_combination (z * signedChecked pos q x (single w 1) w * ∏ i, p (w i)) * Units.inv_mul q

/-- **Countable atomic trace with scalar right slice is the Ocneanu trace.** -/
theorem countableAtomicTrace_eq_ocneanuTrace_of_rightSlice (p : ι → R)
    (hp : Summable fun a ↦ ‖p a‖) {z : R} (hp1 : ∑' a, p a = 1)
    (hz : ∀ b, (if pos b then (q : R) ^ 2 else -1) * p b +
      ((q : R) ^ 2 - 1) * (∑' c, if b < c then p c else 0) = q * z)
    {n : ℕ} (x : TypeAHeckeAlgebra R q n) :
    countableAtomicTrace pos q p hp n x =
      InfiniteTypeAHeckeAlgebra.ocneanuTrace R q z (toInfinite R q n x) :=
  eq_ocneanuTrace_toInfinite (countableAtomicTrace pos q p hp) (by simp)
    (fun _ _ ↦ by rw [countableAtomicTrace_strandIncl, hp1, mul_one])
    (fun _ ↦ countableAtomicTrace_mul_comm pos q p hp)
    (fun _ ↦ countableAtomicTrace_strandIncl_mul_T_last pos q p hp hz) n x

end CountableTrace

section GeneratingProductAndDust

private theorem tsum_coeff_mul_pow_mul_eval {R : Type*} [NormedCommRing R] [CompleteSpace R]
    (F : PowerSeries R) (P Q : Polynomial R) (x : R)
    (hF : Summable fun m : ℕ ↦ ‖PowerSeries.coeff m F * x ^ m‖)
    (hFP : F * (P : PowerSeries R) = (Q : PowerSeries R)) :
    (∑' m : ℕ, PowerSeries.coeff m F * x ^ m) * P.eval x = Q.eval x := by
  have hpoly (S : Polynomial R) :
      (Summable fun k : ℕ ↦ ‖S.coeff k * x ^ k‖) ∧ (∑' k : ℕ, S.coeff k * x ^ k) = S.eval x :=
    ⟨summable_of_ne_finset_zero (s := Finset.range (S.natDegree + 1)) fun k hk ↦ by
      rw [S.coeff_eq_zero_of_natDegree_lt (by simpa using hk), zero_mul, norm_zero],
    by rw [tsum_eq_sum (s := Finset.range (S.natDegree + 1)) fun k hk ↦ by
      rw [S.coeff_eq_zero_of_natDegree_lt (by simpa using hk), zero_mul], S.eval_eq_sum_range]⟩
  rw [← (hpoly P).2, ← (hpoly Q).2,
    tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hF (hpoly P).1]
  congr 1 with n
  rw [← Polynomial.coeff_coe, ← hFP, PowerSeries.coeff_mul, Finset.sum_mul]
  exact Finset.sum_congr rfl fun kl hkl ↦ by
    rw [Polynomial.coeff_coe, ← Finset.mem_antidiagonal.mp hkl, pow_add]; ring

/-- Norm bound on the countable atomic trace of a cycle word `cycleWord (m + 1)`. -/
theorem norm_countableAtomicTrace_cycleWord_le {R : Type*} [NormedCommRing R] [CompleteSpace R]
    {ι : Type*} [LinearOrder ι] (pos : ι → Prop) [DecidablePred pos] (q : Rˣ) (p : ι → R)
    (hp : Summable fun a ↦ ‖p a‖) (m : ℕ) :
    ‖countableAtomicTrace pos q p hp (m + 1) (cycleWord q (m + 1))‖ ≤
      ‖(1 : R)‖ * max 1 (max ‖(q : R) ^ 2‖ ‖(q : R) ^ 2 - 1‖) ^ m *
        (∑' a, ‖p a‖) ^ (m + 1) := by
  rw [countableAtomicTrace_apply]
  refine (norm_tsum_le_tsum_norm
    (summable_norm_signedChecked_mul_prod pos q hp (m + 1) (cycleWord q (m + 1)))).trans ?_
  refine ((summable_norm_signedChecked_mul_prod pos q hp (m + 1) _).tsum_le_tsum (fun w ↦
    (norm_mul_le _ _).trans (mul_le_mul (norm_signedChecked_cycleWord_single_apply_le pos q w)
      (Finset.norm_prod_le' _ Finset.univ_nonempty _) (norm_nonneg _) (by positivity)))
    ((summable_norm_prod_apply hp (m + 1)).mul_left _)).trans_eq ?_
  rw [(summable_norm_prod_apply hp (m + 1)).tsum_mul_left, tsum_norm_prod_apply hp (m + 1)]

private theorem norm_countableAtomicTrace_cycleWord_mul_pow_le {K : Type*}
    [NontriviallyNormedField K] [CompleteSpace K] {ι : Type*} [LinearOrder ι] (pos : ι → Prop)
    [DecidablePred pos] (q : Kˣ) (p : ι → K) (hp : Summable fun a ↦ ‖p a‖) (x : K) (m : ℕ) :
    ‖countableAtomicTrace pos q p hp (m + 1) (cycleWord q (m + 1)) * x ^ (m + 1)‖ ≤
      ((∑' a, ‖p a‖) * ‖x‖) *
        (max 1 (max ‖(q : K) ^ 2‖ ‖(q : K) ^ 2 - 1‖) * (∑' a, ‖p a‖) * ‖x‖) ^ m := by
  rw [norm_mul, norm_pow]
  refine (mul_le_mul_of_nonneg_right (norm_countableAtomicTrace_cycleWord_le pos q p hp m)
    (pow_nonneg (norm_nonneg x) _)).trans ?_
  rw [norm_one, one_mul]; exact le_of_eq (by ring)

private theorem eval_denom_ne_zero {K : Type*} [NontriviallyNormedField K] {ι : Type*} [Fintype ι]
    (pos : ι → Prop) [DecidablePred pos] (q : Kˣ) (p : ι → K) {x : K}
    (hx : max 1 (max ‖(q : K) ^ 2‖ ‖(q : K) ^ 2 - 1‖) * (∑ a, ‖p a‖) * ‖x‖ < 1) (a : ι) :
    (if pos a then 1 - (q : K) ^ 2 * p a * x else 1 + p a * x) ≠ 0 := by
  set M : ℝ := max 1 (max ‖(q : K) ^ 2‖ ‖(q : K) ^ 2 - 1‖)
  have hpa : ‖p a‖ ≤ ∑ b, ‖p b‖ :=
    Finset.single_le_sum (fun _ _ ↦ norm_nonneg _) (Finset.mem_univ a)
  split_ifs <;> intro h0
  · have : (1 : ℝ) = ‖(q : K) ^ 2 * p a * x‖ := by
      simpa [sub_eq_zero.mp h0] using (norm_one (α := K)).symm
    have hMQ : ‖(q : K) ^ 2‖ ≤ M := (le_max_left _ _).trans (le_max_right _ _)
    have : ‖(q : K) ^ 2 * p a * x‖ ≤ M * (∑ b, ‖p b‖) * ‖x‖ := by simp only [norm_mul]; gcongr
    linarith
  · have : (1 : ℝ) = ‖p a * x‖ := by rw [eq_neg_of_add_eq_zero_right h0, norm_neg, norm_one]
    have : ‖p a * x‖ ≤ M * (∑ b, ‖p b‖) * ‖x‖ := by
      rw [norm_mul, ← one_mul ‖p a‖]; have : 1 ≤ M := le_max_left _ _; gcongr
    linarith

/-- **Analytic evaluation of the cycle-trace generating function on a finite alphabet** on the disk
`max 1 (max ‖Q‖ ‖Q - 1‖) * (∑ a, ‖p a‖) * ‖x‖ < 1` (`Q = q ^ 2`). -/
theorem atomicTrace_cycleWord_generating_eval {K : Type*} [NontriviallyNormedField K]
    [CompleteSpace K] {ι : Type*} [LinearOrder ι] [Fintype ι] (pos : ι → Prop) [DecidablePred pos]
    (q : Kˣ) (p : ι → K) {x : K}
    (hx : max 1 (max ‖(q : K) ^ 2‖ ‖(q : K) ^ 2 - 1‖) * (∑ a, ‖p a‖) * ‖x‖ < 1) :
    (Summable fun m : ℕ ↦ ‖atomicTrace pos q p (m + 1) (cycleWord q (m + 1)) * x ^ (m + 1)‖) ∧
      1 + ((q : K) ^ 2 - 1) *
          (∑' m : ℕ, atomicTrace pos q p (m + 1) (cycleWord q (m + 1)) * x ^ (m + 1)) =
        ∏ a, (if pos a then (1 - p a * x) / (1 - (q : K) ^ 2 * p a * x)
          else (1 + (q : K) ^ 2 * p a * x) / (1 + p a * x)) := by
  have hp : Summable fun a ↦ ‖p a‖ := (hasSum_fintype _).summable
  have hsum : Summable fun m : ℕ ↦
      ‖atomicTrace pos q p (m + 1) (cycleWord q (m + 1)) * x ^ (m + 1)‖ :=
    ((summable_geometric_of_lt_one (by positivity) hx).mul_left _).of_nonneg_of_le
      (fun _ ↦ norm_nonneg _) fun m ↦ by
        rw [← countableAtomicTrace_eq_atomicTrace pos q p hp]
        simpa only [tsum_fintype] using
          norm_countableAtomicTrace_cycleWord_mul_pow_le pos q p hp x m
  refine ⟨hsum, ?_⟩
  let F : PowerSeries K := PowerSeries.mk fun m ↦
    if m = 0 then 1 else ((q : K) ^ 2 - 1) * atomicTrace pos q p m (cycleWord q m)
  let P : Polynomial K := ∏ a, if pos a then 1 - Polynomial.C ((q : K) ^ 2 * p a) * Polynomial.X
    else 1 + Polynomial.C (p a) * Polynomial.X
  let Qp : Polynomial K := ∏ a, if pos a then 1 - Polynomial.C (p a) * Polynomial.X
    else 1 + Polynomial.C ((q : K) ^ 2 * p a) * Polynomial.X
  have hF_sum : Summable fun m : ℕ ↦ ‖PowerSeries.coeff m F * x ^ m‖ := by
    rw [← summable_nat_add_iff 1]
    exact (hsum.mul_left ‖(q : K) ^ 2 - 1‖).of_nonneg_of_le (fun _ ↦ norm_nonneg _) fun m ↦ by
      simp only [F, PowerSeries.coeff_mk, Nat.succ_ne_zero, ↓reduceIte, mul_assoc]
      exact norm_mul_le _ _
  have hFP : F * (P : PowerSeries K) = (Qp : PowerSeries K) := by
    rw [← Polynomial.coeToPowerSeries.ringHom_apply (φ := P),
      ← Polynomial.coeToPowerSeries.ringHom_apply (φ := Qp)]
    dsimp only [P, Qp]; rw [map_prod, map_prod]
    simpa only [F, Polynomial.coeToPowerSeries.ringHom_apply,
      apply_ite ((↑) : Polynomial K → PowerSeries K), Polynomial.coe_sub, Polynomial.coe_add,
      Polynomial.coe_one, Polynomial.coe_mul, Polynomial.coe_C, Polynomial.coe_X] using
      atomicTrace_cycleWord_generating_function pos q p
  have heval := tsum_coeff_mul_pow_mul_eval F P Qp x hF_sum hFP
  rw [hF_sum.of_norm.tsum_eq_zero_add] at heval
  simp only [F, P, Qp, PowerSeries.coeff_mk, ↓reduceIte, pow_zero, mul_one, Nat.succ_ne_zero,
    mul_assoc, hsum.of_norm.tsum_mul_left, Polynomial.eval_prod,
    apply_ite (Polynomial.eval x), Polynomial.eval_sub, Polynomial.eval_add,
    Polynomial.eval_one, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X] at heval
  rw [show (∏ a, (if pos a then (1 - p a * x) / (1 - (q : K) ^ 2 * p a * x)
        else (1 + (q : K) ^ 2 * p a * x) / (1 + p a * x))) =
      (∏ a, (if pos a then 1 - p a * x else 1 + (q : K) ^ 2 * p a * x)) /
        ∏ a, (if pos a then 1 - (q : K) ^ 2 * p a * x else 1 + p a * x) by
    rw [← Finset.prod_div_distrib]; exact Finset.prod_congr rfl fun _ _ ↦ by split_ifs <;> rfl,
    eq_div_iff (Finset.prod_ne_zero_iff.mpr fun a _ ↦ eval_denom_ne_zero pos q p hx a)]
  simpa only [mul_assoc] using heval

/-- **Countable cycle-trace generating product** over any complete normed field `K` on the disk
`max 1 (max ‖Q‖ ‖Q - 1‖) * (∑' a, ‖p a‖) * ‖x‖ < 1` (`Q = q ^ 2`). -/
theorem countableAtomicTrace_cycleWord_hasProd {K : Type*} [NontriviallyNormedField K]
    [CompleteSpace K] {ι : Type*} [LinearOrder ι] (pos : ι → Prop) [DecidablePred pos]
    (q : Kˣ) (p : ι → K) (hp : Summable fun a ↦ ‖p a‖) {x : K}
    (hx : max 1 (max ‖(q : K) ^ 2‖ ‖(q : K) ^ 2 - 1‖) * (∑' a, ‖p a‖) * ‖x‖ < 1) :
    (Summable fun m : ℕ ↦
        ‖countableAtomicTrace pos q p hp (m + 1) (cycleWord q (m + 1)) * x ^ (m + 1)‖) ∧
      HasProd (fun a : ι ↦
          if pos a then (1 - p a * x) / (1 - (q : K) ^ 2 * p a * x)
          else (1 + (q : K) ^ 2 * p a * x) / (1 + p a * x))
        (1 + ((q : K) ^ 2 - 1) * ∑' m : ℕ,
          countableAtomicTrace pos q p hp (m + 1) (cycleWord q (m + 1)) * x ^ (m + 1)) := by
  set M : ℝ := max 1 (max ‖(q : K) ^ 2‖ ‖(q : K) ^ 2 - 1‖)
  set S : ℝ := ∑' a, ‖p a‖
  have : 0 ≤ S := tsum_nonneg fun _ ↦ norm_nonneg _
  have hmaj : Summable fun m : ℕ ↦ (S * ‖x‖) * (M * S * ‖x‖) ^ m :=
    (summable_geometric_of_lt_one (by positivity) hx).mul_left _
  refine ⟨hmaj.of_nonneg_of_le (fun _ ↦ norm_nonneg _)
    (norm_countableAtomicTrace_cycleWord_mul_pow_le pos q p hp x), ?_⟩
  have hs_le (s : Finset ι) : ∑ a : s, ‖p a‖ ≤ S := by
    rw [Finset.univ_eq_attach, s.sum_attach fun a ↦ ‖p a‖]
    exact hp.sum_le_tsum s fun _ _ ↦ norm_nonneg _
  have hdom : Tendsto (fun s : Finset ι ↦ ∑' m : ℕ,
      atomicTrace (fun a : s ↦ pos a) q (fun a : s ↦ p a) (m + 1) (cycleWord q (m + 1)) *
        x ^ (m + 1)) atTop
      (𝓝 (∑' m : ℕ, countableAtomicTrace pos q p hp (m + 1) (cycleWord q (m + 1)) *
        x ^ (m + 1))) := by
    refine tendsto_tsum_of_dominated_convergence hmaj
      (fun m ↦ (tendsto_atomicTrace_finset pos q p hp (m + 1) (cycleWord q (m + 1))).mul_const _)
      (Eventually.of_forall fun s m ↦ ?_)
    have hps : Summable fun a : s ↦ ‖p a‖ := (hasSum_fintype _).summable
    rw [← countableAtomicTrace_eq_atomicTrace (fun a : s ↦ pos a) q (fun a : s ↦ p a) hps]
    refine (norm_countableAtomicTrace_cycleWord_mul_pow_le _ q _ hps x m).trans ?_
    rw [tsum_fintype]; have := hs_le s; gcongr
  refine (tendsto_const_nhds.add (hdom.const_mul _)).congr fun s ↦ ?_
  have hxs : M * (∑ a : s, ‖p a‖) * ‖x‖ < 1 :=
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hs_le s) (by positivity))
      (norm_nonneg x)).trans_lt hx
  rw [(atomicTrace_cycleWord_generating_eval (fun a : s ↦ pos a) q (fun a : s ↦ p a) hxs).2,
    Finset.univ_eq_attach,
    s.prod_attach (fun a ↦ if pos a then (1 - p a * x) / (1 - (q : K) ^ 2 * p a * x)
      else (1 + (q : K) ^ 2 * p a * x) / (1 + p a * x))]

/-- **The continuous-dust passage (`exp ((Q - 1) * γ * x)`):** splitting weight `γ` across `N`
positive (`b = true`) or negative (`b = false`) letters of weight `γ / N` converges as `N → ∞` to
`Complex.exp (((q : ℂ) ^ 2 - 1) * γ * x)`. -/
theorem tendsto_atomicTrace_dust_generating_function (b : Bool) (q : ℂˣ) (γ x : ℂ)
    (hx : max 1 (max ‖(q : ℂ) ^ 2‖ ‖(q : ℂ) ^ 2 - 1‖) * ‖γ‖ * ‖x‖ < 1) :
    Tendsto (fun N : ℕ ↦ 1 + ((q : ℂ) ^ 2 - 1) * ∑' m : ℕ,
        atomicTrace (fun _ : Fin N ↦ b = true) q (fun _ ↦ γ / N) (m + 1) (cycleWord q (m + 1)) *
          x ^ (m + 1))
      atTop (𝓝 (Complex.exp (((q : ℂ) ^ 2 - 1) * γ * x))) := by
  have hprod : (fun N : ℕ ↦
      (if b then (1 - γ * x / N) / (1 - (q : ℂ) ^ 2 * γ * x / N)
        else (1 + (q : ℂ) ^ 2 * γ * x / N) / (1 + γ * x / N)) ^ N) =ᶠ[atTop]
      fun N : ℕ ↦ 1 + ((q : ℂ) ^ 2 - 1) * ∑' m : ℕ,
        atomicTrace (fun _ : Fin N ↦ b = true) q (fun _ ↦ γ / N) (m + 1) (cycleWord q (m + 1)) *
          x ^ (m + 1) := by
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hsum_norm : ∑ _a : Fin N, ‖γ / (N : ℂ)‖ = ‖γ‖ := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, norm_div,
        Complex.norm_natCast, mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr (by omega))]
    rw [(atomicTrace_cycleWord_generating_eval (fun _ : Fin N ↦ b = true) q
      (fun _ ↦ γ / N) (by rwa [hsum_norm])).2, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin]
    cases b <;> · simp only [Bool.false_eq_true, ↓reduceIte]; congr 1; congr 1 <;> ring
  refine Tendsto.congr' hprod ?_
  have hlim (u v : ℂ) : Tendsto (fun N : ℕ ↦ (1 + u / N) ^ N / (1 + v / N) ^ N) atTop
      (𝓝 (Complex.exp (u - v))) := by
    rw [Complex.exp_sub]
    exact (Complex.tendsto_one_add_div_pow_exp u).div
      (Complex.tendsto_one_add_div_pow_exp v) (Complex.exp_ne_zero _)
  cases b
  · convert hlim ((q : ℂ) ^ 2 * γ * x) (γ * x) using 1
    · ext N; simp [div_pow]
    · congr 2; ring
  · convert hlim (-(γ * x)) (-((q : ℂ) ^ 2 * γ * x)) using 1
    · ext N; simp [div_pow, sub_eq_add_neg, neg_div]
    · congr 2; ring

end GeneratingProductAndDust

end TypeAHeckeAlgebra

end TauCeti
