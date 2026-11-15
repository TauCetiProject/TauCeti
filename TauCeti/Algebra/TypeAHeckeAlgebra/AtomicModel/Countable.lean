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

Let `ι` be an arbitrary (for instance countably infinite) linearly ordered alphabet of positive and
negative letters, and let `p : ι → R` be an absolutely summable weight family
(`Summable fun a ↦ ‖p a‖`) in a complete normed commutative ring `R`. Because each element
`x : TypeAHeckeAlgebra R q n` is a finite linear combination of words in the Hecke generators and
each signed checked R-matrix has at most two nonzero entries per column, the matrix entries of
`signedChecked pos q x` in the standard word basis are uniformly bounded in norm across the entire
alphabet (`TauCeti.TypeAHeckeAlgebra.exists_norm_signedChecked_single_apply_le`). Consequently the
diagonal series

`∑' (w : Fin n → ι), signedChecked pos q x (single w 1) w * ∏ i, p (w i)`

converges absolutely and defines the *countable atomic trace*
`TauCeti.TypeAHeckeAlgebra.countableAtomicTrace`.

Restricting the alphabet to finite subsets `s : Finset ι` intertwines `signedChecked` via the
strictly monotone inclusion `Subtype.val : s → ι`
(`TauCeti.TypeAHeckeAlgebra.signedChecked_strictMono_single_apply`), so `countableAtomicTrace` is
the limit along `atTop : Filter (Finset ι)` of the finite-alphabet atomic traces
(`TauCeti.TypeAHeckeAlgebra.tendsto_atomicTrace_finset`). Traciality, normalization on `1`,
strand-inclusion and tail-inclusion scaling, separated-block multiplicativity, and `⋆`-positivity
for nonnegative weights therefore pass directly from finite alphabets to countable ones. Moreover,
when `∑' a, p a = 1` and either every right slice or every left slice equals `q * z`, the countable
atomic trace restricts `ocneanuTrace R q z`
(`TauCeti.TypeAHeckeAlgebra.countableAtomicTrace_eq_ocneanuTrace_of_rightSlice`,
`TauCeti.TypeAHeckeAlgebra.countableAtomicTrace_eq_ocneanuTrace_of_leftSlice`).

Finally, we pass the cycle-word generating identity of
`TauCeti.Algebra.TypeAHeckeAlgebra.AtomicModel.CycleWord` to infinite alphabets and to continuous
dust:
* Over a complete normed field `K` (`ℂ`, `ℝ`, …), on the open disk
  `max 1 (max ‖Q‖ ‖Q - 1‖) * (∑' a, ‖p a‖) * ‖x‖ < 1` with `Q = q ^ 2`, the infinite product of
  `(1 - p a * x) / (1 - Q * p a * x)` over positive letters and
  `(1 + Q * p a * x) / (1 + p a * x)` over negative letters converges (`HasProd`) to
  `1 + (Q - 1) * ∑' m, tr (ζ_(m + 1)) * x ^ (m + 1)`
  (`TauCeti.TypeAHeckeAlgebra.countableAtomicTrace_cycleWord_hasProd`).
* At `Q = 1` (`q ^ 2 = 1`), only constant words survive on the diagonal of `ζ_(m + 1)` and
  `tr (ζ_(m + 1)) = ∑' a, (if pos a then 1 else -1) ^ m * p a ^ (m + 1)`
  (`TauCeti.TypeAHeckeAlgebra.countableAtomicTrace_cycleWord_of_sq_eq_one`).
* Splitting a weight `γ : ℂ` equally across `N` positive (or `N` negative) letters gives the finite
  generating function `((1 - γ * x / N) / (1 - Q * γ * x / N)) ^ N` (or
  `((1 + Q * γ * x / N) / (1 + γ * x / N)) ^ N`), and both converge as `N → ∞` to the dust factor
  `exp ((Q - 1) * γ * x)`
  (`TauCeti.TypeAHeckeAlgebra.tendsto_atomicTrace_dust_generating_function`).

## Main definitions

* `TauCeti.TypeAHeckeAlgebra.countableAtomicTrace`: the atomic trace on `n` strands for an
  absolutely summable weight family on an arbitrary linearly ordered alphabet.
* `TauCeti.TypeAHeckeAlgebra.countableAtomicPositiveFunctional`: the complex countable atomic trace
  bundled as a `StarPositiveFunctional` when `0 ≤ p a`.

## Main results

* `TauCeti.TypeAHeckeAlgebra.signedChecked_strictMono_single_apply`: strictly monotone
  sign-preserving alphabet maps preserve matrix entries of `signedChecked`.
* `TauCeti.TypeAHeckeAlgebra.tendsto_atomicTrace_finset`: `countableAtomicTrace` is the `Finset`
  exhaustion limit of finite `atomicTrace`s.
* `TauCeti.TypeAHeckeAlgebra.countableAtomicTrace_star_mul_self_nonneg`: positivity of countable
  atomic traces on `star x * x`.
* `TauCeti.TypeAHeckeAlgebra.countableAtomicTrace_eq_ocneanuTrace_of_rightSlice` and
  `TauCeti.TypeAHeckeAlgebra.countableAtomicTrace_eq_ocneanuTrace_of_leftSlice`: countable right-
  and left-slice realizations of `ocneanuTrace`.
* `TauCeti.TypeAHeckeAlgebra.countableAtomicTrace_cycleWord_hasProd`,
  `TauCeti.TypeAHeckeAlgebra.countableAtomicTrace_cycleWord_of_sq_eq_one`, and
  `TauCeti.TypeAHeckeAlgebra.tendsto_atomicTrace_dust_generating_function`: the countable
  cycle-trace generating product, `Q = 1` power sums, and `exp ((Q - 1) * γ * x)` dust limit.

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

/-- A strictly monotone sign-preserving map of alphabets intertwines `signedCheckedR` via
`Finsupp.lmapDomain`. -/
theorem signedCheckedR_comp_lmapDomain_strictMono (s : R) {g : ι' → ι} (hg : StrictMono g)
    (hpos : ∀ a, pos (g a) ↔ pos' a) (j k : Fin n) :
    (signedCheckedR pos s j k).comp (lmapDomain R R (fun w : Fin n → ι' ↦ g ∘ w)) =
      (lmapDomain R R (fun w : Fin n → ι' ↦ g ∘ w)).comp (signedCheckedR pos' s j k) := by
  ext w : 2
  simp only [LinearMap.coe_comp, comp_apply, lsingle_apply, signedCheckedR_single_one]
  rw [lmapDomain_apply, mapDomain_single, signedCheckedR_single_one]
  by_cases hjk : w j = w k
  · simp only [comp_apply, hjk, ↓reduceIte, hpos (w k)]
    split_ifs <;> rw [map_smul, lmapDomain_apply, mapDomain_single]
  · have hjk' : g (w j) ≠ g (w k) := hg.injective.ne hjk
    simp only [comp_apply, hjk, hjk', ↓reduceIte, hg.lt_iff_lt]
    split_ifs
    · rw [map_sub, map_smul, map_smul, lmapDomain_apply, lmapDomain_apply, mapDomain_single,
        mapDomain_single, Function.comp_assoc]
    · rw [map_neg, map_smul, lmapDomain_apply, mapDomain_single, Function.comp_assoc]

end StrictMonoAlphabet

namespace TypeAHeckeAlgebra

section StrictMonoAndCycleDiag

variable {R : Type*} [CommRing R] {ι : Type*} [LinearOrder ι] (pos : ι → Prop) [DecidablePred pos]
  (q : Rˣ) {n : ℕ}

/-- **Alphabet restriction / embedding invariance of `signedChecked`.** Any strictly monotone
sign-preserving map `g : ι' → ι` preserves all word-basis matrix entries of `signedChecked`. -/
theorem signedChecked_strictMono_single_apply {ι' : Type*} [LinearOrder ι']
    (pos' : ι' → Prop) [DecidablePred pos'] {g : ι' → ι} (hg : StrictMono g)
    (hpos : ∀ a, pos (g a) ↔ pos' a) (x : TypeAHeckeAlgebra R q n) (w u : Fin n → ι') :
    signedChecked pos q x (single (g ∘ w) 1) (g ∘ u) =
      signedChecked pos' q x (single w 1) u := by
  set L := lmapDomain R R (fun v : Fin n → ι' ↦ g ∘ v)
  have hcomp : (signedChecked pos q x).comp L = L.comp (signedChecked pos' q x) := by
    have hx : x ∈ Algebra.adjoin R (Set.range (T (n := n) q)) := by
      rw [adjoin_range_T]
      trivial
    induction hx using Algebra.adjoin_induction with
    | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      rw [signedChecked_T, signedChecked_T, LinearMap.smul_comp, LinearMap.comp_smul,
        signedCheckedR_comp_lmapDomain_strictMono pos pos' (q : R) hg hpos]
    | algebraMap r =>
      ext v : 2
      simp [L, AlgHom.commutes, Module.algebraMap_end_apply]
    | add x y _ _ hx hy =>
      rw [map_add, map_add, LinearMap.add_comp, LinearMap.comp_add, hx, hy]
    | mul x y _ _ hx hy =>
      rw [map_mul, map_mul, Module.End.mul_eq_comp, Module.End.mul_eq_comp, LinearMap.comp_assoc,
        hy, ← LinearMap.comp_assoc, hx, LinearMap.comp_assoc]
  have hw := LinearMap.congr_fun hcomp (single w 1)
  simp only [LinearMap.coe_comp, comp_apply, L, lmapDomain_apply, mapDomain_single] at hw
  rw [hw, mapDomain_apply_of_injective hg.injective.comp_left]

/-- **Cycle-word diagonal recursion across a prepended first strand.** The `q` and `q⁻¹` factors in
`g_0 = q • T 0` cancel algebraically, expressing the diagonal entry of `cycleWord (m + 2)` at
`Fin.cons a w` directly as that of `cycleWord (m + 1)` at `w` times `{q ^ 2, -1, q ^ 2 - 1, 0}`. -/
theorem signedChecked_cycleWord_succ_cons_apply {m : ℕ} (a : ι) (w : Fin (m + 1) → ι) :
    signedChecked pos q (cycleWord q (m + 2)) (single (Fin.cons a w) 1) (Fin.cons a w) =
      signedChecked pos q (cycleWord q (m + 1)) (single w 1) w *
        (if a = w 0 then (if pos (w 0) then (q : R) ^ 2 else -1)
          else if a < w 0 then (q : R) ^ 2 - 1 else 0) := by
  have hq : (q : R) * ↑q⁻¹ = 1 := Units.mul_inv q
  rw [← tailIncl_cycleWord_mul_smul_T_zero m, mul_smul_comm, map_smul, LinearMap.smul_apply,
    Finsupp.smul_apply, smul_eq_mul, signedChecked_tailIncl_mul_T_zero_single_cons_apply]
  linear_combination (signedChecked pos q (cycleWord q (m + 1)) (single w 1) w *
    (if a = w 0 then (if pos (w 0) then (q : R) ^ 2 else -1)
      else if a < w 0 then (q : R) ^ 2 - 1 else 0)) * hq

/-- At `(q : R) ^ 2 = 1`, the diagonal entry of `cycleWord (m + 1)` at a word `w` vanishes unless
`w` is constant, where it equals `(if pos (w 0) then 1 else -1) ^ m`. -/
theorem signedChecked_cycleWord_single_apply_of_sq_eq_one (hq : (q : R) ^ 2 = 1) :
    ∀ {m : ℕ} (w : Fin (m + 1) → ι),
      signedChecked pos q (cycleWord q (m + 1)) (single w 1) w =
        if ∀ i, w i = w 0 then (if pos (w 0) then (1 : R) else -1) ^ m else 0
  | 0, w => by
    have hall : ∀ i : Fin 1, w i = w 0 := fun i ↦ by rw [Fin.eq_zero i]
    simp [hall]
  | m + 1, w => by
    conv_lhs => rw [← Fin.cons_self_tail w]
    rw [signedChecked_cycleWord_succ_cons_apply,
      signedChecked_cycleWord_single_apply_of_sq_eq_one hq (Fin.tail w), hq, sub_self, ite_self]
    have ht0 : Fin.tail w 0 = w 1 := rfl
    rw [ht0]
    by_cases hall : ∀ i : Fin (m + 2), w i = w 0
    · have h0 : w 0 = w 1 := (hall 1).symm
      have hj : ∀ j : Fin (m + 1), Fin.tail w j = w 1 := fun j ↦ (hall j.succ).trans h0
      rw [ite_eq_left hj, ite_eq_left h0, ite_eq_left hall, h0, pow_succ]
    · rw [ite_eq_right hall]
      by_cases h0 : w 0 = w 1
      · have hj : ¬∀ j : Fin (m + 1), Fin.tail w j = w 1 := fun hj ↦
          hall (Fin.forall_fin_succ.mpr ⟨rfl, fun j ↦ (hj j).trans h0.symm⟩)
        rw [ite_eq_right hj, zero_mul]
      · rw [ite_eq_right h0, mul_zero]

/-- **Cycle-word atomic trace at `Q = 1`.** When `(q : R) ^ 2 = 1`, the atomic trace of
`cycleWord (m + 1)` on a finite alphabet is the signed `(m + 1)`-th power sum of the weights. -/
theorem atomicTrace_cycleWord_of_sq_eq_one [Fintype ι] (hq : (q : R) ^ 2 = 1) (p : ι → R)
    (m : ℕ) :
    atomicTrace pos q p (m + 1) (cycleWord q (m + 1)) =
      ∑ a, (if pos a then (1 : R) else -1) ^ m * p a ^ (m + 1) := by
  classical
  rw [atomicTrace_eq_sum]
  simp_rw [signedChecked_cycleWord_single_apply_of_sq_eq_one pos q hq, ite_mul, zero_mul,
    ← Finset.sum_filter]
  refine Finset.sum_bij' (fun w _ ↦ w 0) (fun a _ ↦ fun _ ↦ a) (fun _ _ ↦ Finset.mem_univ _)
    (fun a _ ↦ Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun _ ↦ rfl⟩)
    (fun w hw ↦ funext fun i ↦ ((Finset.mem_filter.mp hw).2 i).symm)
    (fun _ _ ↦ rfl) fun w hw ↦ ?_
  have hconst := (Finset.mem_filter.mp hw).2
  congr 1
  calc ∏ i : Fin (m + 1), p (w i) = ∏ _i : Fin (m + 1), p (w 0) :=
        Finset.prod_congr rfl fun i _ ↦ by rw [hconst i]
    _ = p (w 0) ^ (m + 1) := by simp

end StrictMonoAndCycleDiag

section NormBounds

variable {R : Type*} [NormedCommRing R] {ι : Type*} [LinearOrder ι] (pos : ι → Prop)
  [DecidablePred pos] (q : Rˣ) {n : ℕ}

private noncomputable def wordL1 {α : Type*} (v : α →₀ R) : ℝ :=
  v.sum fun _ r ↦ ‖r‖

private theorem wordL1_nonneg {α : Type*} (v : α →₀ R) : 0 ≤ wordL1 v :=
  Finset.sum_nonneg fun _ _ ↦ norm_nonneg _

private theorem norm_apply_le_wordL1 {α : Type*} (v : α →₀ R) (u : α) :
    ‖v u‖ ≤ wordL1 v := by
  classical
  by_cases hu : u ∈ v.support
  · exact Finset.single_le_sum (fun _ _ ↦ norm_nonneg _) hu
  · rw [Finsupp.notMem_support_iff.mp hu, norm_zero]
    exact wordL1_nonneg v

private theorem wordL1_zero {α : Type*} : wordL1 (0 : α →₀ R) = 0 := by
  simp [wordL1]

private theorem wordL1_neg {α : Type*} (v : α →₀ R) : wordL1 (-v) = wordL1 v := by
  simp [wordL1, Finsupp.sum_neg_index]

private theorem wordL1_add_le {α : Type*} (v₁ v₂ : α →₀ R) :
    wordL1 (v₁ + v₂) ≤ wordL1 v₁ + wordL1 v₂ := by
  classical
  dsimp only [wordL1]
  rw [Finsupp.sum_of_support_subset _ v₁.support_add _ (fun _ _ ↦ norm_zero),
    Finsupp.sum_of_support_subset v₁ Finset.subset_union_left _ (fun _ _ ↦ norm_zero),
    Finsupp.sum_of_support_subset v₂ Finset.subset_union_right _ (fun _ _ ↦ norm_zero),
    ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun u _ ↦ norm_add_le (v₁ u) (v₂ u)

private theorem wordL1_sub_le {α : Type*} (v₁ v₂ : α →₀ R) :
    wordL1 (v₁ - v₂) ≤ wordL1 v₁ + wordL1 v₂ := by
  rw [sub_eq_add_neg, ← wordL1_neg v₂]
  exact wordL1_add_le v₁ (-v₂)

private theorem wordL1_smul_le {α : Type*} (r : R) (v : α →₀ R) :
    wordL1 (r • v) ≤ ‖r‖ * wordL1 v := by
  dsimp only [wordL1]
  rw [Finsupp.sum_of_support_subset _ Finsupp.support_smul _ (fun _ _ ↦ norm_zero),
    Finsupp.sum, Finset.mul_sum]
  exact Finset.sum_le_sum fun u _ ↦ norm_mul_le r (v u)

private theorem wordL1_single_le {α : Type*} (u : α) (r : R) :
    wordL1 (single u r) ≤ ‖r‖ := by
  simp [wordL1, Finsupp.sum_single_index]

private theorem wordL1_finset_sum_le {α β : Type*} (s : Finset β) (g : β → α →₀ R) :
    wordL1 (∑ b ∈ s, g b) ≤ ∑ b ∈ s, wordL1 (g b) := by
  classical
  induction s using Finset.induction with
  | empty => simp [wordL1_zero]
  | insert b s hbs ih =>
    rw [Finset.sum_insert hbs, Finset.sum_insert hbs]
    exact (wordL1_add_le _ _).trans (add_le_add_right ih _)

private theorem wordL1_linearMap_le {α : Type*} (f : (α →₀ R) →ₗ[R] (α →₀ R)) {C : ℝ}
    (hC : ∀ w, wordL1 (f (single w 1)) ≤ C) (v : α →₀ R) :
    wordL1 (f v) ≤ C * wordL1 v := by
  have hsingle (u : α) : single u (v u) = v u • single u 1 := by
    rw [Finsupp.smul_single', mul_one]
  conv_lhs => rw [← Finsupp.sum_single v, Finsupp.sum]
  simp_rw [hsingle]
  rw [map_sum]
  calc wordL1 (∑ u ∈ v.support, f (v u • single u 1))
      ≤ ∑ u ∈ v.support, wordL1 (v u • f (single u 1)) := by
        simp_rw [map_smul]
        exact wordL1_finset_sum_le _ _
    _ ≤ ∑ u ∈ v.support, ‖v u‖ * C :=
        Finset.sum_le_sum fun u _ ↦ (wordL1_smul_le _ _).trans
          (mul_le_mul_of_nonneg_left (hC u) (norm_nonneg _))
    _ = C * wordL1 v := by
        rw [← Finset.sum_mul, mul_comm]
        rfl

/-- **Uniform matrix-entry bound for `signedChecked`.** For every `x : TypeAHeckeAlgebra R q n`, the
norms of the word-basis matrix entries `signedChecked pos q x (single w 1) u` are uniformly bounded
across all words `w, u : Fin n → ι`. -/
theorem exists_norm_signedChecked_single_apply_le (x : TypeAHeckeAlgebra R q n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w u : Fin n → ι, ‖signedChecked pos q x (single w 1) u‖ ≤ C := by
  suffices h : ∃ B : ℝ, 0 ≤ B ∧ ∀ w : Fin n → ι, wordL1 (signedChecked pos q x (single w 1)) ≤
      B * wordL1 (single (w : Fin n → ι) (1 : R)) by
    obtain ⟨B, hB0, hB⟩ := h
    refine ⟨B * ‖(1 : R)‖, mul_nonneg hB0 (norm_nonneg _), fun w u ↦ ?_⟩
    exact (norm_apply_le_wordL1 _ u).trans ((hB w).trans
      (mul_le_mul_of_nonneg_left (wordL1_single_le w 1) hB0))
  have hx : x ∈ Algebra.adjoin R (Set.range (T (n := n) q)) := by
    rw [adjoin_range_T]
    trivial
  induction hx using Algebra.adjoin_induction with
  | mem y hy =>
    obtain ⟨i, rfl⟩ := hy
    set K : ℝ := ‖((q⁻¹ : Rˣ) : R)‖ * (‖(q : R) ^ 2‖ + 1 + ‖(q : R) ^ 2 - 1‖ + ‖(q : R)‖)
    refine ⟨K, by positivity, fun w ↦ ?_⟩
    rw [signedChecked_T, LinearMap.smul_apply]
    refine (wordL1_smul_le _ _).trans ?_
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    have hsw : wordL1 (single (w ∘ Equiv.swap (BraidGroup.strand i) (BraidGroup.strandSucc i))
        (1 : R)) = wordL1 (single w (1 : R)) := by
      simp [wordL1, Finsupp.sum_single_index]
    have hw0 : 0 ≤ wordL1 (single w (1 : R)) := wordL1_nonneg _
    rw [signedCheckedR_single_one]
    split_ifs
    · have h1 := wordL1_smul_le ((q : R) ^ 2) (single w (1 : R))
      nlinarith [norm_nonneg ((q : R) ^ 2 - 1), norm_nonneg (q : R)]
    · rw [neg_smul, one_smul, wordL1_neg]
      nlinarith [norm_nonneg ((q : R) ^ 2), norm_nonneg ((q : R) ^ 2 - 1), norm_nonneg (q : R)]
    · have h0 := wordL1_sub_le (((q : R) ^ 2 - 1) • single w (1 : R))
        ((q : R) • single (w ∘ Equiv.swap (BraidGroup.strand i) (BraidGroup.strandSucc i)) (1 : R))
      have h1 := wordL1_smul_le ((q : R) ^ 2 - 1) (single w (1 : R))
      have h2 := wordL1_smul_le (q : R)
        (single (w ∘ Equiv.swap (BraidGroup.strand i) (BraidGroup.strandSucc i)) (1 : R))
      rw [hsw] at h2
      nlinarith [norm_nonneg ((q : R) ^ 2)]
    · rw [wordL1_neg]
      have h2 := wordL1_smul_le (q : R)
        (single (w ∘ Equiv.swap (BraidGroup.strand i) (BraidGroup.strandSucc i)) (1 : R))
      rw [hsw] at h2
      nlinarith [norm_nonneg ((q : R) ^ 2), norm_nonneg ((q : R) ^ 2 - 1)]
  | algebraMap r =>
    refine ⟨‖r‖, norm_nonneg r, fun w ↦ ?_⟩
    rw [AlgHom.commutes, Module.algebraMap_end_apply]
    exact wordL1_smul_le r (single w 1)
  | add x y _ _ hx hy =>
    obtain ⟨Bx, hBx0, hBx⟩ := hx
    obtain ⟨By, hBy0, hBy⟩ := hy
    refine ⟨Bx + By, add_nonneg hBx0 hBy0, fun w ↦ ?_⟩
    rw [map_add, LinearMap.add_apply, add_mul]
    exact (wordL1_add_le _ _).trans (add_le_add (hBx w) (hBy w))
  | mul x y _ _ hx hy =>
    obtain ⟨Bx, hBx0, hBx⟩ := hx
    obtain ⟨By, hBy0, hBy⟩ := hy
    refine ⟨Bx * ‖(1 : R)‖ * By, by positivity, fun w ↦ ?_⟩
    rw [map_mul, mul_apply_eq_comp, mul_assoc]
    refine (wordL1_linearMap_le (signedChecked pos q x) (fun u ↦ ?_) _).trans
      (mul_le_mul_of_nonneg_left (hBy w) (by positivity))
    exact (hBx u).trans (mul_le_mul_of_nonneg_left (wordL1_single_le u 1) hBx0)

/-- **Sharp diagonal norm bound on cycle words.** For every word `w : Fin (m + 1) → ι`,
`‖signedChecked pos q (cycleWord q (m + 1)) (single w 1) w‖ ≤
  ‖(1 : R)‖ * max 1 (max ‖(q : R) ^ 2‖ ‖(q : R) ^ 2 - 1‖) ^ m`. -/
theorem norm_signedChecked_cycleWord_single_apply_le :
    ∀ {m : ℕ} (w : Fin (m + 1) → ι),
      ‖signedChecked pos q (cycleWord q (m + 1)) (single w 1) w‖ ≤
        ‖(1 : R)‖ * max 1 (max ‖(q : R) ^ 2‖ ‖(q : R) ^ 2 - 1‖) ^ m
  | 0, w => by
    rw [cycleWord_one, map_one, one_apply_eq_self, single_eq_same, pow_zero, mul_one]
  | m + 1, w => by
    set M : ℝ := max 1 (max ‖(q : R) ^ 2‖ ‖(q : R) ^ 2 - 1‖)
    have hM1 : (1 : ℝ) ≤ M := le_max_left _ _
    have hMQ : ‖(q : R) ^ 2‖ ≤ M := (le_max_left _ _).trans (le_max_right _ _)
    have hMQ1 : ‖(q : R) ^ 2 - 1‖ ≤ M := (le_max_right _ _).trans (le_max_right _ _)
    have hcons : Fin.cons (w 0) (Fin.tail w) = w := Fin.cons_self_tail w
    rw [← hcons, signedChecked_cycleWord_succ_cons_apply, pow_succ M m, ← mul_assoc]
    have ih := norm_signedChecked_cycleWord_single_apply_le (Fin.tail w)
    set z := signedChecked pos q (cycleWord q (m + 1)) (single (Fin.tail w) 1) (Fin.tail w)
    have hstep : ‖z * (if w 0 = Fin.tail w 0 then (if pos (Fin.tail w 0) then (q : R) ^ 2 else -1)
        else if w 0 < Fin.tail w 0 then (q : R) ^ 2 - 1 else 0)‖ ≤ ‖z‖ * M := by
      split_ifs
      · exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left hMQ (norm_nonneg z))
      · rw [mul_neg, mul_one, norm_neg]
        exact le_mul_of_one_le_right (norm_nonneg z) hM1
      · exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left hMQ1 (norm_nonneg z))
      · rw [mul_zero, norm_zero]
        positivity
    exact hstep.trans (mul_le_mul_of_nonneg_right ih (by positivity))

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
    have h := hp.mul_of_nonneg (summable_norm_prod_apply hp n) (fun _ ↦ norm_nonneg _)
      (fun _ ↦ Finset.prod_nonneg fun _ _ ↦ norm_nonneg _)
    refine h.congr fun aw ↦ ?_
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
        fun aw ↦ ‖p aw.1‖ * ∏ i : Fin n, ‖p (aw.2 i)‖ := by
      ext ⟨a, w⟩
      simp [Fin.prod_univ_succ]
    have hp' : Summable fun a ↦ ‖‖p a‖‖ := hp.congr fun a ↦ (norm_norm (p a)).symm
    have hprod' : Summable fun w : Fin n → ι ↦ ‖∏ i, ‖p (w i)‖‖ :=
      (summable_norm_prod_apply hp n).congr fun w ↦
        (Real.norm_of_nonneg (Finset.prod_nonneg fun _ _ ↦ norm_nonneg _)).symm
    rw [heq, ← tsum_mul_tsum_of_summable_norm hp' hprod', tsum_norm_prod_apply hp n, pow_succ']

omit [CompleteSpace R] in
private theorem norm_nonempty_prod_le {α : Type*} {s : Finset α} (hs : s.Nonempty) (f : α → R) :
    ‖∏ i ∈ s, f i‖ ≤ ∏ i ∈ s, ‖f i‖ := by
  classical
  induction hs using Finset.Nonempty.cons_induction with
  | singleton a => simp
  | cons a s has _ ih =>
    rw [Finset.prod_cons, Finset.prod_cons]
    exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left ih (norm_nonneg _))

omit [CompleteSpace R] in
/-- Absolute summability of the weighted diagonal coefficients of `signedChecked pos q x`. -/
theorem summable_norm_signedChecked_mul_prod {p : ι → R} (hp : Summable fun a ↦ ‖p a‖) (n : ℕ)
    (x : TypeAHeckeAlgebra R q n) :
    Summable fun w : Fin n → ι ↦ ‖signedChecked pos q x (single w 1) w * ∏ i, p (w i)‖ := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_signedChecked_single_apply_le pos q x
  refine ((summable_norm_prod_apply hp n).mul_left C).of_nonneg_of_le (fun _ ↦ norm_nonneg _)
    fun w ↦ ?_
  rcases eq_or_ne n 0 with rfl | hn
  · have : ∏ i : Fin 0, p (w i) = 1 := rfl
    rw [this, mul_one]
    simpa using hC w w
  · have hne : (Finset.univ : Finset (Fin n)).Nonempty :=
      ⟨⟨0, Nat.pos_of_ne_zero hn⟩, Finset.mem_univ _⟩
    exact (norm_mul_le _ _).trans
      (mul_le_mul (hC w w) (norm_nonempty_prod_le hne fun i ↦ p (w i)) (norm_nonneg _) hC0)

/-- **The countable atomic trace** on `TypeAHeckeAlgebra R q n` associated with a signed linearly
ordered alphabet `ι` and an absolutely summable weight family `p : ι → R`. -/
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

/-- **Exhaustion of a countable atomic trace by finite sub-alphabets.** Along the directed system
`atTop : Filter (Finset ι)` of finite subsets of `ι`, the finite `atomicTrace`s converge to
`countableAtomicTrace`. -/
theorem tendsto_atomicTrace_finset (p : ι → R) (hp : Summable fun a ↦ ‖p a‖) (n : ℕ)
    (x : TypeAHeckeAlgebra R q n) :
    Tendsto (fun s : Finset ι ↦ atomicTrace (fun a : s ↦ pos a) q (fun a : s ↦ p a) n x)
      atTop (𝓝 (countableAtomicTrace pos q p hp n x)) := by
  classical
  have hpi : Tendsto (fun s : Finset ι ↦ Fintype.piFinset fun _ : Fin n ↦ s) atTop atTop := by
    rw [tendsto_atTop_atTop]
    intro T
    refine ⟨T.biUnion fun w ↦ Finset.univ.image w,
      fun s hs w hw ↦ Fintype.mem_piFinset.mpr fun i ↦
        hs (Finset.mem_biUnion.mpr ⟨w, hw, Finset.mem_image_of_mem w (Finset.mem_univ i)⟩)⟩
  have hsum := ((summable_norm_signedChecked_mul_prod pos q hp n x).of_norm.hasSum).comp hpi
  refine hsum.congr fun s ↦ ?_
  rw [comp_apply, atomicTrace_eq_sum]
  symm
  refine Finset.sum_bij (fun (w : Fin n → s) _ ↦ Subtype.val ∘ w)
    (fun w _ ↦ Fintype.mem_piFinset.mpr fun i ↦ (w i).2)
    (fun w₁ _ w₂ _ h ↦ funext fun i ↦ Subtype.ext (congrFun h i))
    (fun w hw ↦ ⟨fun i ↦ ⟨w i, Fintype.mem_piFinset.mp hw i⟩, Finset.mem_univ _, rfl⟩)
    fun w _ ↦ ?_
  rw [signedChecked_strictMono_single_apply pos q (fun a : s ↦ pos a)
    (fun _ _ h ↦ h) (fun _ ↦ Iff.rfl)]
  rfl

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
    countableAtomicTrace pos q p hp n 1 = (∑' a, p a) ^ n := by
  refine tendsto_nhds_unique (tendsto_atomicTrace_finset pos q p hp n 1) ?_
  have h : Tendsto (fun s : Finset ι ↦ (∑ a ∈ s, p a) ^ n) atTop (𝓝 ((∑' a, p a) ^ n)) :=
    hp.of_norm.hasSum.pow n
  refine h.congr fun s ↦ ?_
  rw [atomicTrace_one, Finset.univ_eq_attach, s.sum_attach p]

/-- Adding an uncrossed last strand multiplies `countableAtomicTrace` by `∑' a, p a`. -/
@[simp]
theorem countableAtomicTrace_strandIncl (p : ι → R) (hp : Summable fun a ↦ ‖p a‖) {n : ℕ}
    (x : TypeAHeckeAlgebra R q n) :
    countableAtomicTrace pos q p hp (n + 1) (strandIncl R q n x) =
      countableAtomicTrace pos q p hp n x * ∑' a, p a := by
  refine tendsto_nhds_unique (tendsto_atomicTrace_finset pos q p hp (n + 1) (strandIncl R q n x)) ?_
  refine ((tendsto_atomicTrace_finset pos q p hp n x).mul hp.of_norm.hasSum).congr fun s ↦ ?_
  rw [← Finset.sum_attach s p, ← Finset.univ_eq_attach, ← atomicTrace_strandIncl]

/-- Adding an uncrossed first strand multiplies `countableAtomicTrace` by `∑' a, p a`. -/
@[simp]
theorem countableAtomicTrace_tailIncl (p : ι → R) (hp : Summable fun a ↦ ‖p a‖) {n : ℕ}
    (x : TypeAHeckeAlgebra R q n) :
    countableAtomicTrace pos q p hp (n + 1) (tailIncl q n x) =
      countableAtomicTrace pos q p hp n x * ∑' a, p a := by
  refine tendsto_nhds_unique (tendsto_atomicTrace_finset pos q p hp (n + 1) (tailIncl q n x)) ?_
  refine ((tendsto_atomicTrace_finset pos q p hp n x).mul hp.of_norm.hasSum).congr fun s ↦ ?_
  rw [← Finset.sum_attach s p, ← Finset.univ_eq_attach, ← atomicTrace_tailIncl]

/-- **Block multiplicativity of `countableAtomicTrace`.** Elements on disjoint consecutive blocks of
strands factor under `countableAtomicTrace`. -/
theorem countableAtomicTrace_castAdd_mul_natAdd (p : ι → R) (hp : Summable fun a ↦ ‖p a‖)
    {m n : ℕ} (x : TypeAHeckeAlgebra R q m) (y : TypeAHeckeAlgebra R q n) :
    countableAtomicTrace pos q p hp (m + n) (castAdd R q m n x * natAdd R q m n y) =
      countableAtomicTrace pos q p hp m x * countableAtomicTrace pos q p hp n y := by
  refine tendsto_nhds_unique
    (tendsto_atomicTrace_finset pos q p hp (m + n) (castAdd R q m n x * natAdd R q m n y)) ?_
  exact ((tendsto_atomicTrace_finset pos q p hp m x).mul
    (tendsto_atomicTrace_finset pos q p hp n y)).congr fun s ↦
      (atomicTrace_castAdd_mul_natAdd (fun a : s ↦ pos a) q (fun a : s ↦ p a) x y).symm

/-- **Positivity of countable atomic traces.** Over a complete normed commutative `StarOrderedRing`
with closed order (`ℝ`, `ℂ`, …), a star-fixed parameter `q`, and nonnegative summable weights
`0 ≤ p a`, the countable atomic trace is nonnegative on every square `star x * x`. -/
theorem countableAtomicTrace_star_mul_self_nonneg [PartialOrder R] [StarRing R] [StarOrderedRing R]
    [OrderClosedTopology R] [Fact (IsSelfAdjoint (q : R))] {p : ι → R}
    (hp : Summable fun a ↦ ‖p a‖) (hp0 : ∀ a, 0 ≤ p a) {n : ℕ} (x : TypeAHeckeAlgebra R q n) :
    0 ≤ countableAtomicTrace pos q p hp n (star x * x) :=
  ge_of_tendsto (tendsto_atomicTrace_finset pos q p hp n (star x * x)) <|
    Eventually.of_forall fun s ↦
      atomicTrace_star_mul_self_nonneg (fun a : s ↦ pos a) q (fun a : s ↦ hp0 a) x

/-- The complex countable atomic trace on `n` strands bundled as a `StarPositiveFunctional`, for a
star-fixed parameter `q : ℂˣ` and nonnegative absolutely summable weights `0 ≤ p a`. -/
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

/-- **Cycle-word countable atomic trace at `Q = 1`.** When `(q : R) ^ 2 = 1`, the countable atomic
trace of `cycleWord (m + 1)` is the convergent signed `(m + 1)`-th power sum of the weights. -/
theorem countableAtomicTrace_cycleWord_of_sq_eq_one (hq : (q : R) ^ 2 = 1) (p : ι → R)
    (hp : Summable fun a ↦ ‖p a‖) (m : ℕ) :
    countableAtomicTrace pos q p hp (m + 1) (cycleWord q (m + 1)) =
      ∑' a, (if pos a then (1 : R) else -1) ^ m * p a ^ (m + 1) := by
  have hpow : Summable fun a ↦ ‖(if pos a then (1 : R) else -1) ^ m * p a ^ (m + 1)‖ := by
    have hc : ∀ a, ‖(if pos a then (1 : R) else -1) ^ m‖ ≤ ‖(1 : R)‖ * max 1 ‖(1 : R)‖ ^ m := by
      intro a
      induction m with
      | zero => simp
      | succ k ih =>
        rw [pow_succ _ k, pow_succ _ k]
        refine (norm_mul_le _ _).trans ?_
        have h1 : ‖if pos a then (1 : R) else -1‖ ≤ max 1 ‖(1 : R)‖ := by
          split_ifs <;> simp
        exact (mul_le_mul ih h1 (norm_nonneg _) (by positivity)).trans_eq (mul_assoc _ _ _)
    have hle_sum (a : ι) : ‖p a‖ ≤ ∑' b, ‖p b‖ := hp.le_tsum a fun _ _ ↦ norm_nonneg _
    have hp_pow (a : ι) : ‖p a ^ (m + 1)‖ ≤ (∑' b, ‖p b‖) ^ m * ‖p a‖ := by
      clear hc
      induction m with
      | zero => simp
      | succ k ih =>
        rw [pow_succ (p a) (k + 1), pow_succ (∑' b, ‖p b‖) k]
        refine (norm_mul_le _ _).trans ((mul_le_mul_of_nonneg_right ih (norm_nonneg _)).trans ?_)
        rw [mul_assoc, mul_assoc]
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right (hle_sum a) (norm_nonneg _)) (by positivity)
    refine (hp.mul_left (‖(1 : R)‖ * max 1 ‖(1 : R)‖ ^ m * (∑' b, ‖p b‖) ^ m)).of_nonneg_of_le
      (fun _ ↦ norm_nonneg _) fun a ↦ ?_
    refine (norm_mul_le _ _).trans ?_
    rw [mul_assoc]
    exact mul_le_mul (hc a) (hp_pow a) (norm_nonneg _) (by positivity)
  refine tendsto_nhds_unique
    (tendsto_atomicTrace_finset pos q p hp (m + 1) (cycleWord q (m + 1))) ?_
  refine hpow.of_norm.hasSum.congr fun s ↦ ?_
  rw [← Finset.sum_attach s (fun a ↦ (if pos a then (1 : R) else -1) ^ m * p a ^ (m + 1)),
    ← Finset.univ_eq_attach, ← atomicTrace_cycleWord_of_sq_eq_one (fun a : s ↦ pos a) q hq]

private theorem tsum_leftSlice_split {p : ι → R} (hp : Summable fun a ↦ ‖p a‖) (b : ι) :
    (∑' a, (if a = b then (if pos b then (q : R) ^ 2 else -1)
      else if a < b then (q : R) ^ 2 - 1 else 0) * p a) =
      (if pos b then (q : R) ^ 2 else -1) * p b +
        ((q : R) ^ 2 - 1) * ∑' a, if a < b then p a else 0 := by
  classical
  have h₁ : Summable fun a : ι ↦ if a = b then (if pos b then (q : R) ^ 2 else -1) * p b else 0 :=
    summable_of_ne_finset_zero (s := {b}) fun a ha ↦ by
      simp [Finset.notMem_singleton.mp ha]
  have h_ite : Summable fun a : ι ↦ ‖if a < b then p a else 0‖ :=
    hp.of_nonneg_of_le (fun _ ↦ norm_nonneg _) fun a ↦ by split_ifs <;> simp
  have h₂ : Summable fun a : ι ↦ ((q : R) ^ 2 - 1) * if a < b then p a else 0 :=
    h_ite.of_norm.mul_left _
  have hpt (a : ι) : (if a = b then (if pos b then (q : R) ^ 2 else -1)
      else if a < b then (q : R) ^ 2 - 1 else 0) * p a =
      (if a = b then (if pos b then (q : R) ^ 2 else -1) * p b else 0) +
        ((q : R) ^ 2 - 1) * (if a < b then p a else 0) := by
    rcases lt_trichotomy a b with hab | rfl | hab
    · simp [hab.ne, hab]
    · simp
    · simp [hab.ne', hab.not_gt]
  simp_rw [hpt]
  rw [h₁.tsum_add h₂, tsum_ite_eq, h_ite.of_norm.tsum_mul_left]

omit [LinearOrder ι] in
private theorem tsum_fin_cons {n : ℕ} {f : (Fin (n + 1) → ι) → R} (hf : Summable f) :
    (∑' u : Fin (n + 1) → ι, f u) = ∑' w : Fin n → ι, ∑' a : ι, f (Fin.cons a w) := by
  let e := (Equiv.prodComm (Fin n → ι) ι).trans (Fin.consEquiv fun _ : Fin (n + 1) ↦ ι)
  exact (e.tsum_eq f).symm.trans (Summable.tsum_prod (e.summable_iff.mpr hf))

omit [LinearOrder ι] in
private theorem tsum_fin_snoc {n : ℕ} {f : (Fin (n + 1) → ι) → R} (hf : Summable f) :
    (∑' u : Fin (n + 1) → ι, f u) = ∑' w : Fin n → ι, ∑' c : ι, f (Fin.snoc w c) := by
  let e := (Equiv.prodComm (Fin n → ι) ι).trans (Fin.snocEquiv fun _ : Fin (n + 1) ↦ ι)
  exact (e.tsum_eq f).symm.trans (Summable.tsum_prod (e.summable_iff.mpr hf))

/-- **Countable first-site (left-slice) Markov rule.** If every countable left slice
`(if pos b then q ^ 2 else -1) * p b + (q ^ 2 - 1) * ∑' a, (if a < b then p a else 0)` equals
`q * z`, then multiplying a shifted-tail element by `T 0` multiplies `countableAtomicTrace` by
`z`. -/
theorem countableAtomicTrace_T_zero_mul_tailIncl (p : ι → R) (hp : Summable fun a ↦ ‖p a‖)
    {z : R}
    (hz : ∀ b, (if pos b then (q : R) ^ 2 else -1) * p b +
      ((q : R) ^ 2 - 1) * (∑' a, if a < b then p a else 0) = q * z)
    {n : ℕ} (x : TypeAHeckeAlgebra R q (n + 1)) :
    countableAtomicTrace pos q p hp (n + 2) (T q (0 : Fin (n + 1)) * tailIncl q (n + 1) x) =
      z * countableAtomicTrace pos q p hp (n + 1) x := by
  rw [countableAtomicTrace_mul_comm, countableAtomicTrace_apply,
    tsum_fin_cons (summable_norm_signedChecked_mul_prod pos q hp (n + 2) _).of_norm,
    countableAtomicTrace_apply,
    ← (summable_norm_signedChecked_mul_prod pos q hp (n + 1) x).of_norm.tsum_mul_left]
  congr 1 with w
  simp_rw [signedChecked_tailIncl_mul_T_zero_single_cons_apply,
    Fin.prod_univ_succ (n := n + 1), Fin.cons_zero, Fin.cons_succ]
  have hsl_sum : Summable fun a : ι ↦
      (if a = w 0 then (if pos (w 0) then (q : R) ^ 2 else -1)
        else if a < w 0 then (q : R) ^ 2 - 1 else 0) * p a := by
    refine ((hp.mul_left (max ‖(q : R) ^ 2‖ (max ‖(1 : R)‖ ‖(q : R) ^ 2 - 1‖))).of_nonneg_of_le
      (fun _ ↦ norm_nonneg _) fun a ↦ ?_).of_norm
    refine (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
    split_ifs
    · exact le_max_left _ _
    · rw [norm_neg]
      exact (le_max_left _ _).trans (le_max_right _ _)
    · exact (le_max_right _ _).trans (le_max_right _ _)
    · rw [norm_zero]
      positivity
  have heq : (fun a : ι ↦ ((q⁻¹ : Rˣ) : R) * signedChecked pos q x (single w 1) w *
      (if a = w 0 then (if pos (w 0) then (q : R) ^ 2 else -1)
        else if a < w 0 then (q : R) ^ 2 - 1 else 0) * (p a * ∏ i, p (w i))) =
      fun a : ι ↦ (((q⁻¹ : Rˣ) : R) * signedChecked pos q x (single w 1) w * ∏ i, p (w i)) *
        ((if a = w 0 then (if pos (w 0) then (q : R) ^ 2 else -1)
          else if a < w 0 then (q : R) ^ 2 - 1 else 0) * p a) := by
    ext a
    ring
  have hq : ((q⁻¹ : Rˣ) : R) * q = 1 := Units.inv_mul q
  rw [heq, hsl_sum.tsum_mul_left, tsum_leftSlice_split pos q hp (w 0), hz (w 0)]
  linear_combination (z * signedChecked pos q x (single w 1) w * ∏ i, p (w i)) * hq

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

private theorem tsum_rightSlice_split {p : ι → R} (hp : Summable fun a ↦ ‖p a‖) (b : ι) :
    (∑' c, (if b = c then (if pos c then (q : R) ^ 2 else -1)
      else if b < c then (q : R) ^ 2 - 1 else 0) * p c) =
      (if pos b then (q : R) ^ 2 else -1) * p b +
        ((q : R) ^ 2 - 1) * ∑' c, if b < c then p c else 0 := by
  classical
  have h₁ : Summable fun c : ι ↦ if c = b then (if pos b then (q : R) ^ 2 else -1) * p b else 0 :=
    summable_of_ne_finset_zero (s := {b}) fun c hc ↦ by
      simp [Finset.notMem_singleton.mp hc]
  have h_ite : Summable fun c : ι ↦ ‖if b < c then p c else 0‖ :=
    hp.of_nonneg_of_le (fun _ ↦ norm_nonneg _) fun c ↦ by split_ifs <;> simp
  have h₂ : Summable fun c : ι ↦ ((q : R) ^ 2 - 1) * if b < c then p c else 0 :=
    h_ite.of_norm.mul_left _
  have hpt (c : ι) : (if b = c then (if pos c then (q : R) ^ 2 else -1)
      else if b < c then (q : R) ^ 2 - 1 else 0) * p c =
      (if c = b then (if pos b then (q : R) ^ 2 else -1) * p b else 0) +
        ((q : R) ^ 2 - 1) * (if b < c then p c else 0) := by
    rcases lt_trichotomy b c with hbc | rfl | hbc
    · simp [hbc.ne, hbc.ne', hbc]
    · simp
    · simp [hbc.ne, hbc.ne', hbc.not_gt]
  simp_rw [hpt]
  rw [h₁.tsum_add h₂, tsum_ite_eq, h_ite.of_norm.tsum_mul_left]

/-- **Countable last-site (right-slice) Markov rule.** If every countable right slice
`(if pos b then q ^ 2 else -1) * p b + (q ^ 2 - 1) * ∑' c, (if b < c then p c else 0)` equals
`q * z`, then multiplying a strand-included element by `T n` multiplies `countableAtomicTrace` by
`z`. -/
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
          (if w (Fin.last n) = c then (if pos c then (q : R) ^ 2 else -1)
            else if w (Fin.last n) < c then (q : R) ^ 2 - 1 else 0) := by
    have hswap : Fin.snoc w c ∘ Equiv.swap (Fin.last n).castSucc (Fin.last (n + 1)) =
        Fin.snoc (update w (Fin.last n) c) (w (Fin.last n)) := by
      rw [Equiv.comp_swap_eq_update]
      simp [← Fin.snoc_update, Fin.update_snoc_last]
    simp only [map_mul, mul_apply_eq_comp, signedChecked_T, hj, hk, LinearMap.smul_apply,
      signedCheckedR_single_one, Fin.snoc_castSucc, Fin.snoc_last, hswap]
    rcases lt_trichotomy (w (Fin.last n)) c with h | h | h
    · simp only [h.ne, h, ↓reduceIte, map_sub, map_smul, Finsupp.smul_apply,
        Finsupp.sub_apply, smul_eq_mul, signedChecked_strandIncl_single_snoc_apply_snoc]
      ring
    · subst h
      simp only [↓reduceIte, map_smul, Finsupp.smul_apply, smul_eq_mul,
        signedChecked_strandIncl_single_snoc_apply_snoc]
      ring
    · simp only [h.ne', h.not_gt, ↓reduceIte, map_neg, map_smul, Finsupp.smul_apply,
        Finsupp.neg_apply, smul_eq_mul, signedChecked_strandIncl_single_snoc_apply_snoc]
      ring
  rw [countableAtomicTrace_apply,
    tsum_fin_snoc (summable_norm_signedChecked_mul_prod pos q hp (n + 2) _).of_norm,
    countableAtomicTrace_apply,
    ← (summable_norm_signedChecked_mul_prod pos q hp (n + 1) x).of_norm.tsum_mul_left]
  congr 1 with w
  simp_rw [hdiag, Fin.prod_univ_castSucc (n := n + 1), Fin.snoc_castSucc, Fin.snoc_last]
  have hsr_sum : Summable fun c : ι ↦
      (if w (Fin.last n) = c then (if pos c then (q : R) ^ 2 else -1)
        else if w (Fin.last n) < c then (q : R) ^ 2 - 1 else 0) * p c := by
    refine ((hp.mul_left (max ‖(q : R) ^ 2‖ (max ‖(1 : R)‖ ‖(q : R) ^ 2 - 1‖))).of_nonneg_of_le
      (fun _ ↦ norm_nonneg _) fun c ↦ ?_).of_norm
    refine (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
    split_ifs
    · exact le_max_left _ _
    · rw [norm_neg]
      exact (le_max_left _ _).trans (le_max_right _ _)
    · exact (le_max_right _ _).trans (le_max_right _ _)
    · rw [norm_zero]
      positivity
  have heq : (fun c : ι ↦ ((q⁻¹ : Rˣ) : R) * signedChecked pos q x (single w 1) w *
      (if w (Fin.last n) = c then (if pos c then (q : R) ^ 2 else -1)
        else if w (Fin.last n) < c then (q : R) ^ 2 - 1 else 0) * ((∏ i, p (w i)) * p c)) =
      fun c : ι ↦ (((q⁻¹ : Rˣ) : R) * signedChecked pos q x (single w 1) w * ∏ i, p (w i)) *
        ((if w (Fin.last n) = c then (if pos c then (q : R) ^ 2 else -1)
          else if w (Fin.last n) < c then (q : R) ^ 2 - 1 else 0) * p c) := by
    ext c
    ring
  have hq : ((q⁻¹ : Rˣ) : R) * q = 1 := Units.inv_mul q
  rw [heq, hsr_sum.tsum_mul_left, tsum_rightSlice_split pos q hp (w (Fin.last n)),
    hz (w (Fin.last n))]
  linear_combination (z * signedChecked pos q x (single w 1) w * ∏ i, p (w i)) * hq

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
      (Summable fun k : ℕ ↦ ‖S.coeff k * x ^ k‖) ∧
        (∑' k : ℕ, S.coeff k * x ^ k) = S.eval x := by
    refine ⟨summable_of_ne_finset_zero (s := Finset.range (S.natDegree + 1)) fun k hk ↦ ?_, ?_⟩
    · simp only [Finset.mem_range] at hk
      rw [S.coeff_eq_zero_of_natDegree_lt (by omega), zero_mul, norm_zero]
    · rw [tsum_eq_sum (s := Finset.range (S.natDegree + 1)) fun k hk ↦ by
        simp only [Finset.mem_range] at hk
        rw [S.coeff_eq_zero_of_natDegree_lt (by omega), zero_mul], S.eval_eq_sum_range]
  rw [← (hpoly P).2, ← (hpoly Q).2,
    tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hF (hpoly P).1]
  congr 1 with n
  rw [← Polynomial.coeff_coe, ← hFP, PowerSeries.coeff_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun kl hkl ↦ ?_
  rw [Polynomial.coeff_coe, ← Finset.mem_antidiagonal.mp hkl, pow_add]
  ring

/-- Norm bound on the countable atomic trace of a cycle word `cycleWord (m + 1)`. -/
theorem norm_countableAtomicTrace_cycleWord_le {R : Type*} [NormedCommRing R] [CompleteSpace R]
    {ι : Type*} [LinearOrder ι] (pos : ι → Prop) [DecidablePred pos] (q : Rˣ) (p : ι → R)
    (hp : Summable fun a ↦ ‖p a‖) (m : ℕ) :
    ‖countableAtomicTrace pos q p hp (m + 1) (cycleWord q (m + 1))‖ ≤
      ‖(1 : R)‖ * max 1 (max ‖(q : R) ^ 2‖ ‖(q : R) ^ 2 - 1‖) ^ m *
        (∑' a, ‖p a‖) ^ (m + 1) := by
  set M : ℝ := max 1 (max ‖(q : R) ^ 2‖ ‖(q : R) ^ 2 - 1‖)
  rw [countableAtomicTrace_apply]
  refine (norm_tsum_le_tsum_norm
    (summable_norm_signedChecked_mul_prod pos q hp (m + 1) (cycleWord q (m + 1)))).trans ?_
  calc (∑' w : Fin (m + 1) → ι,
        ‖signedChecked pos q (cycleWord q (m + 1)) (single w 1) w * ∏ i, p (w i)‖)
      ≤ ∑' w : Fin (m + 1) → ι, (‖(1 : R)‖ * M ^ m) * ∏ i, ‖p (w i)‖ := by
        refine (summable_norm_signedChecked_mul_prod pos q hp (m + 1) _).tsum_le_tsum (fun w ↦ ?_)
          ((summable_norm_prod_apply hp (m + 1)).mul_left _)
        have hne : (Finset.univ : Finset (Fin (m + 1))).Nonempty := Finset.univ_nonempty
        exact (norm_mul_le _ _).trans
          (mul_le_mul (norm_signedChecked_cycleWord_single_apply_le pos q w)
            (norm_nonempty_prod_le hne fun i ↦ p (w i)) (norm_nonneg _) (by positivity))
    _ = ‖(1 : R)‖ * M ^ m * (∑' a, ‖p a‖) ^ (m + 1) := by
        rw [(summable_norm_prod_apply hp (m + 1)).tsum_mul_left, tsum_norm_prod_apply hp (m + 1)]

private theorem eval_denom_ne_zero {K : Type*} [NontriviallyNormedField K] {ι : Type*} [Fintype ι]
    (pos : ι → Prop) [DecidablePred pos] (q : Kˣ) (p : ι → K) {x : K}
    (hx : max 1 (max ‖(q : K) ^ 2‖ ‖(q : K) ^ 2 - 1‖) * (∑ a, ‖p a‖) * ‖x‖ < 1) (a : ι) :
    (if pos a then 1 - (q : K) ^ 2 * p a * x else 1 + p a * x) ≠ 0 := by
  set M : ℝ := max 1 (max ‖(q : K) ^ 2‖ ‖(q : K) ^ 2 - 1‖)
  set S : ℝ := ∑ b, ‖p b‖
  have hM0 : 0 ≤ M := by positivity
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun _ _ ↦ norm_nonneg _
  have hpa : ‖p a‖ ≤ S := Finset.single_le_sum (fun _ _ ↦ norm_nonneg _) (Finset.mem_univ a)
  split_ifs
  · intro h0
    have h1 : (1 : ℝ) = ‖(q : K) ^ 2 * p a * x‖ := by
      simpa [sub_eq_zero.mp h0] using (norm_one (α := K)).symm
    have hMQ : ‖(q : K) ^ 2‖ ≤ M := (le_max_left _ _).trans (le_max_right _ _)
    have hle : ‖(q : K) ^ 2 * p a * x‖ ≤ M * S * ‖x‖ := by
      calc ‖(q : K) ^ 2 * p a * x‖ ≤ ‖(q : K) ^ 2‖ * ‖p a‖ * ‖x‖ := by
            refine (norm_mul_le _ _).trans
              (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg x))
        _ ≤ M * S * ‖x‖ := mul_le_mul_of_nonneg_right
            (mul_le_mul hMQ hpa (norm_nonneg _) hM0) (norm_nonneg x)
    linarith
  · intro h0
    have h1 : (1 : ℝ) = ‖p a * x‖ := by
      have : p a * x = -1 := eq_neg_of_add_eq_zero_right h0
      rw [this, norm_neg, norm_one]
    have hM1 : (1 : ℝ) ≤ M := le_max_left _ _
    have hle : ‖p a * x‖ ≤ M * S * ‖x‖ := by
      calc ‖p a * x‖ ≤ 1 * S * ‖x‖ := by
            rw [one_mul]
            exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right hpa (norm_nonneg x))
        _ ≤ M * S * ‖x‖ := mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hM1 hS0) (norm_nonneg x)
    linarith

/-- **Analytic evaluation of the cycle-trace generating function on a finite alphabet.** Over any
complete normed field `K`, on the disk `max 1 (max ‖Q‖ ‖Q - 1‖) * (∑ a, ‖p a‖) * ‖x‖ < 1` with
`Q = q ^ 2`, the cycle-trace generating series converges absolutely and equals the rational product
over the alphabet. -/
theorem atomicTrace_cycleWord_generating_eval {K : Type*} [NontriviallyNormedField K]
    [CompleteSpace K] {ι : Type*} [LinearOrder ι] [Fintype ι] (pos : ι → Prop) [DecidablePred pos]
    (q : Kˣ) (p : ι → K) {x : K}
    (hx : max 1 (max ‖(q : K) ^ 2‖ ‖(q : K) ^ 2 - 1‖) * (∑ a, ‖p a‖) * ‖x‖ < 1) :
    (Summable fun m : ℕ ↦ ‖atomicTrace pos q p (m + 1) (cycleWord q (m + 1)) * x ^ (m + 1)‖) ∧
      1 + ((q : K) ^ 2 - 1) *
          (∑' m : ℕ, atomicTrace pos q p (m + 1) (cycleWord q (m + 1)) * x ^ (m + 1)) =
        ∏ a, (if pos a then (1 - p a * x) / (1 - (q : K) ^ 2 * p a * x)
          else (1 + (q : K) ^ 2 * p a * x) / (1 + p a * x)) := by
  set M : ℝ := max 1 (max ‖(q : K) ^ 2‖ ‖(q : K) ^ 2 - 1‖)
  set S : ℝ := ∑ a, ‖p a‖
  have hp : Summable fun a ↦ ‖p a‖ := (hasSum_fintype _).summable
  have hS : ∑' a, ‖p a‖ = S := tsum_fintype _
  have hr0 : 0 ≤ M * S * ‖x‖ := by positivity
  have hmaj : Summable fun m : ℕ ↦ (S * ‖x‖) * (M * S * ‖x‖) ^ m :=
    (summable_geometric_of_lt_one hr0 hx).mul_left _
  have hterm_le (m : ℕ) :
      ‖atomicTrace pos q p (m + 1) (cycleWord q (m + 1)) * x ^ (m + 1)‖ ≤
        (S * ‖x‖) * (M * S * ‖x‖) ^ m := by
    rw [← countableAtomicTrace_eq_atomicTrace pos q p hp, norm_mul, norm_pow]
    refine (mul_le_mul_of_nonneg_right
      (norm_countableAtomicTrace_cycleWord_le pos q p hp m)
      (pow_nonneg (norm_nonneg x) _)).trans ?_
    rw [norm_one, one_mul, hS]
    exact le_of_eq (by ring)
  have hsum : Summable fun m : ℕ ↦
      ‖atomicTrace pos q p (m + 1) (cycleWord q (m + 1)) * x ^ (m + 1)‖ :=
    hmaj.of_nonneg_of_le (fun _ ↦ norm_nonneg _) hterm_le
  refine ⟨hsum, ?_⟩
  let F : PowerSeries K := PowerSeries.mk fun m ↦
    if m = 0 then 1 else ((q : K) ^ 2 - 1) * atomicTrace pos q p m (cycleWord q m)
  let P : Polynomial K := ∏ a,
    if pos a then 1 - Polynomial.C ((q : K) ^ 2 * p a) * Polynomial.X
    else 1 + Polynomial.C (p a) * Polynomial.X
  let Qp : Polynomial K := ∏ a,
    if pos a then 1 - Polynomial.C (p a) * Polynomial.X
    else 1 + Polynomial.C ((q : K) ^ 2 * p a) * Polynomial.X
  have hF_sum : Summable fun m : ℕ ↦ ‖PowerSeries.coeff m F * x ^ m‖ := by
    rw [← summable_nat_add_iff 1]
    refine (hsum.mul_left ‖(q : K) ^ 2 - 1‖).of_nonneg_of_le (fun _ ↦ norm_nonneg _) fun m ↦ ?_
    simp only [F, PowerSeries.coeff_mk, Nat.succ_ne_zero, ↓reduceIte, mul_assoc]
    exact norm_mul_le _ _
  have hFP : F * (P : PowerSeries K) = (Qp : PowerSeries K) := by
    have hgen := atomicTrace_cycleWord_generating_function pos q p
    rw [← Polynomial.coeToPowerSeries.ringHom_apply (φ := P),
      ← Polynomial.coeToPowerSeries.ringHom_apply (φ := Qp)]
    dsimp only [P, Qp]
    rw [map_prod, map_prod]
    simpa only [F, Polynomial.coeToPowerSeries.ringHom_apply,
      apply_ite ((↑) : Polynomial K → PowerSeries K),
      Polynomial.coe_sub, Polynomial.coe_add, Polynomial.coe_one, Polynomial.coe_mul,
      Polynomial.coe_C, Polynomial.coe_X] using hgen
  have heval := tsum_coeff_mul_pow_mul_eval F P Qp x hF_sum hFP
  have hF_tsum : (∑' m : ℕ, PowerSeries.coeff m F * x ^ m) =
      1 + ((q : K) ^ 2 - 1) *
        ∑' m : ℕ, atomicTrace pos q p (m + 1) (cycleWord q (m + 1)) * x ^ (m + 1) := by
    rw [hF_sum.of_norm.tsum_eq_zero_add]
    simp only [F, PowerSeries.coeff_mk, ↓reduceIte, pow_zero, mul_one, Nat.succ_ne_zero, mul_assoc]
    rw [hsum.of_norm.tsum_mul_left]
  have hP_eval : P.eval x =
      ∏ a, (if pos a then 1 - (q : K) ^ 2 * p a * x else 1 + p a * x) := by
    simp only [P, Polynomial.eval_prod]
    exact Finset.prod_congr rfl fun a _ ↦ by split_ifs <;> simp [mul_assoc]
  have hQ_eval : Qp.eval x =
      ∏ a, (if pos a then 1 - p a * x else 1 + (q : K) ^ 2 * p a * x) := by
    simp only [Qp, Polynomial.eval_prod]
    exact Finset.prod_congr rfl fun a _ ↦ by split_ifs <;> simp [mul_assoc]
  rw [hF_tsum, hP_eval, hQ_eval] at heval
  have hprod_div :
      (∏ a, (if pos a then (1 - p a * x) / (1 - (q : K) ^ 2 * p a * x)
        else (1 + (q : K) ^ 2 * p a * x) / (1 + p a * x))) =
        (∏ a, (if pos a then 1 - p a * x else 1 + (q : K) ^ 2 * p a * x)) /
          ∏ a, (if pos a then 1 - (q : K) ^ 2 * p a * x else 1 + p a * x) := by
    rw [← Finset.prod_div_distrib]
    exact Finset.prod_congr rfl fun a _ ↦ by split_ifs <;> rfl
  rw [hprod_div,
    eq_div_iff (Finset.prod_ne_zero_iff.mpr fun a _ ↦ eval_denom_ne_zero pos q p hx a)]
  exact heval

/-- **Countable cycle-trace generating product.** Over any complete normed field `K` (`ℂ`, `ℝ`, …),
for an absolutely summable weight family `p : ι → K` and any `x : K` with
`max 1 (max ‖Q‖ ‖Q - 1‖) * (∑' a, ‖p a‖) * ‖x‖ < 1`, `Q = q ^ 2`, the infinite product of
`(1 - p a * x) / (1 - Q * p a * x)` over positive letters and
`(1 + Q * p a * x) / (1 + p a * x)` over negative letters converges (`HasProd`) to
`1 + (Q - 1) * ∑' m, countableAtomicTrace (m + 1) (cycleWord (m + 1)) * x ^ (m + 1)`. -/
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
  have hM0 : 0 ≤ M := by positivity
  have hr0 : 0 ≤ M * S * ‖x‖ := by
    have : 0 ≤ S := tsum_nonneg fun _ ↦ norm_nonneg _
    positivity
  have hmaj : Summable fun m : ℕ ↦ (S * ‖x‖) * (M * S * ‖x‖) ^ m :=
    (summable_geometric_of_lt_one hr0 hx).mul_left _
  have hbound_lim (m : ℕ) :
      ‖countableAtomicTrace pos q p hp (m + 1) (cycleWord q (m + 1)) * x ^ (m + 1)‖ ≤
        (S * ‖x‖) * (M * S * ‖x‖) ^ m := by
    rw [norm_mul, norm_pow]
    refine (mul_le_mul_of_nonneg_right
      (norm_countableAtomicTrace_cycleWord_le pos q p hp m)
      (pow_nonneg (norm_nonneg x) _)).trans ?_
    rw [norm_one, one_mul]
    exact le_of_eq (by ring)
  refine ⟨hmaj.of_nonneg_of_le (fun _ ↦ norm_nonneg _) hbound_lim, ?_⟩
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
    rw [← countableAtomicTrace_eq_atomicTrace (fun a : s ↦ pos a) q (fun a : s ↦ p a) hps,
      norm_mul, norm_pow]
    refine (mul_le_mul_of_nonneg_right
      (norm_countableAtomicTrace_cycleWord_le (fun a : s ↦ pos a) q (fun a : s ↦ p a) hps m)
      (pow_nonneg (norm_nonneg x) _)).trans ?_
    rw [norm_one, one_mul, tsum_fintype]
    calc M ^ m * (∑ a : s, ‖p a‖) ^ (m + 1) * ‖x‖ ^ (m + 1)
        ≤ M ^ m * S ^ (m + 1) * ‖x‖ ^ (m + 1) := by
          have := hs_le s
          gcongr
      _ = (S * ‖x‖) * (M * S * ‖x‖) ^ m := by ring
  have hrhs : Tendsto (fun s : Finset ι ↦ 1 + ((q : K) ^ 2 - 1) * ∑' m : ℕ,
      atomicTrace (fun a : s ↦ pos a) q (fun a : s ↦ p a) (m + 1) (cycleWord q (m + 1)) *
        x ^ (m + 1)) atTop
      (𝓝 (1 + ((q : K) ^ 2 - 1) * ∑' m : ℕ,
        countableAtomicTrace pos q p hp (m + 1) (cycleWord q (m + 1)) * x ^ (m + 1))) :=
    tendsto_const_nhds.add (hdom.const_mul _)
  refine hrhs.congr fun s ↦ ?_
  have hxs : M * (∑ a : s, ‖p a‖) * ‖x‖ < 1 :=
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hs_le s) hM0)
      (norm_nonneg x)).trans_lt hx
  rw [(atomicTrace_cycleWord_generating_eval (fun a : s ↦ pos a) q (fun a : s ↦ p a) hxs).2,
    Finset.univ_eq_attach,
    s.prod_attach (fun a ↦ if pos a then (1 - p a * x) / (1 - (q : K) ^ 2 * p a * x)
      else (1 + (q : K) ^ 2 * p a * x) / (1 + p a * x))]

/-- **The continuous-dust passage (`exp ((Q - 1) * γ * x)`).** Splitting a complex weight `γ`
equally across `N` positive letters (`b = true`) or `N` negative letters (`b = false`) of weight
`γ / N` produces on the disk `max 1 (max ‖Q‖ ‖Q - 1‖) * ‖γ‖ * ‖x‖ < 1` the finite cycle-trace
generating function `((1 - γ * x / N) / (1 - Q * γ * x / N)) ^ N` or
`((1 + Q * γ * x / N) / (1 + γ * x / N)) ^ N`, and as `N → ∞` both converge to
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
    have hxN : max 1 (max ‖(q : ℂ) ^ 2‖ ‖(q : ℂ) ^ 2 - 1‖) *
        (∑ _a : Fin N, ‖γ / (N : ℂ)‖) * ‖x‖ < 1 := by rwa [hsum_norm]
    rw [(atomicTrace_cycleWord_generating_eval (fun _ : Fin N ↦ b = true) q
      (fun _ ↦ γ / N) hxN).2, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    cases b <;>
    · simp only [Bool.false_eq_true, ↓reduceIte]
      congr 1
      congr 1 <;> ring
  refine Tendsto.congr' hprod ?_
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte, div_pow]
    have hnum := Complex.tendsto_one_add_div_pow_exp ((q : ℂ) ^ 2 * γ * x)
    have hden := Complex.tendsto_one_add_div_pow_exp (γ * x)
    have hexp : Complex.exp ((q : ℂ) ^ 2 * γ * x) / Complex.exp (γ * x) =
        Complex.exp (((q : ℂ) ^ 2 - 1) * γ * x) := by
      rw [← Complex.exp_sub]
      congr 1
      ring
    rw [← hexp]
    exact hnum.div hden (Complex.exp_ne_zero _)
  · simp only [↓reduceIte, div_pow]
    have hnum : Tendsto (fun N : ℕ ↦ (1 - γ * x / N) ^ N) atTop
        (𝓝 (Complex.exp (-(γ * x)))) := by
      simpa [sub_eq_add_neg, neg_div] using Complex.tendsto_one_add_div_pow_exp (-(γ * x))
    have hden : Tendsto (fun N : ℕ ↦ (1 - (q : ℂ) ^ 2 * γ * x / N) ^ N) atTop
        (𝓝 (Complex.exp (-((q : ℂ) ^ 2 * γ * x)))) := by
      simpa [sub_eq_add_neg, neg_div] using
        Complex.tendsto_one_add_div_pow_exp (-((q : ℂ) ^ 2 * γ * x))
    have hexp : Complex.exp (-(γ * x)) / Complex.exp (-((q : ℂ) ^ 2 * γ * x)) =
        Complex.exp (((q : ℂ) ^ 2 - 1) * γ * x) := by
      rw [← Complex.exp_sub]
      congr 1
      ring
    rw [← hexp]
    exact hnum.div hden (Complex.exp_ne_zero _)

end GeneratingProductAndDust

end TypeAHeckeAlgebra

end TauCeti
