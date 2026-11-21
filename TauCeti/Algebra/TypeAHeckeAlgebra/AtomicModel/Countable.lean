/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Ring.InfiniteSum
public import TauCeti.Algebra.TypeAHeckeAlgebra.AtomicModel.CycleWord
public import TauCeti.Algebra.TypeAHeckeAlgebra.AtomicModel.LeftSlice
public import TauCeti.Algebra.TypeAHeckeAlgebra.AtomicModel.Positivity
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Topology.Order.Basic
import TauCeti.Algebra.Order.Star.Basic
import TauCeti.Analysis.Normed.Module.Finsupp
import TauCeti.Analysis.Normed.Ring.InfiniteSum
import TauCeti.RingTheory.PowerSeries.EvalAt

/-!
# Countable atomic models, infinite cycle-trace products, and the dust passage

For a linearly ordered alphabet `ι` and an absolutely summable weight family `p : ι → R` in a
complete normed commutative ring `R`, the matrix entries of `signedChecked pos q x` are uniformly
bounded (`exists_norm_signedChecked_single_apply_le`), so the diagonal series converges absolutely
and defines `countableAtomicTrace` (bundled over `ℂ` as `countableAtomicPositiveFunctional`).

Exhaustion by finite `atomicTrace`s (`tendsto_atomicTrace_finset`) passes traciality, scaling on
`1` / `strandIncl` / `tailIncl`, block multiplicativity, star compatibility
(`star_countableAtomicTrace`, `countableAtomicTrace_star`), `⋆`-positivity
(`countableAtomicTrace_star_mul_self_nonneg`), null space and trace radical for strictly positive
weights (`countableAtomicTrace_star_mul_self_eq_zero_iff`,
`traceRadical_countableAtomicTrace_eq_ker_signedChecked`), and the left- and right-slice Ocneanu
identifications (`countableAtomicTrace_eq_ocneanuTrace_of_leftSlice`,
`countableAtomicTrace_eq_ocneanuTrace_of_rightSlice`) to countable alphabets.

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

namespace TauCeti.TypeAHeckeAlgebra

section NormBounds

variable {R : Type*} [NormedCommRing R] {ι : Type*} [LinearOrder ι] (pos : ι → Prop)
  [DecidablePred pos] (q : Rˣ) {n : ℕ}

/-- **Uniform matrix-entry bound for `signedChecked`** across all words `w, u : Fin n → ι`. -/
theorem exists_norm_signedChecked_single_apply_le (x : TypeAHeckeAlgebra R q n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w u : Fin n → ι, ‖signedChecked pos q x (single w 1) u‖ ≤ C := by
  suffices h : ∃ B : ℝ, 0 ≤ B ∧
      ∀ w : Fin n → ι, (signedChecked pos q x (single w 1)).sum (fun _ r ↦ ‖r‖) ≤ B by
    obtain ⟨B, hB0, hB⟩ := h
    exact ⟨B, hB0, fun w u ↦ (Finsupp.norm_apply_le_sum_norm _ u).trans (hB w)⟩
  have h1 (u : Fin n → ι) : (single u (1 : R)).sum (fun _ r ↦ ‖r‖) ≤ ‖(1 : R)‖ := by
    simp [Finsupp.sum_single_index]
  have hs (r : R) (u : Fin n → ι) : (r • single u (1 : R)).sum (fun _ c ↦ ‖c‖) ≤ ‖r‖ * ‖(1 : R)‖ :=
    (Finsupp.sum_norm_smul_le r _).trans (mul_le_mul_of_nonneg_left (h1 u) (norm_nonneg _))
  have hx : x ∈ Algebra.adjoin R (Set.range (T (n := n) q)) := by rw [adjoin_range_T]; trivial
  induction hx using Algebra.adjoin_induction with
  | mem _ hy =>
    obtain ⟨i, rfl⟩ := hy
    set B₀ := ‖(q : R) ^ 2‖ + 1 + ‖(q : R) ^ 2 - 1‖ + ‖(q : R)‖
    refine ⟨‖((q⁻¹ : Rˣ) : R)‖ * (B₀ * ‖(1 : R)‖), by positivity, fun w ↦ ?_⟩
    rw [signedChecked_T, LinearMap.smul_apply]
    refine (Finsupp.sum_norm_smul_le _ _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
    rw [signedCheckedR_single_one]
    have := norm_nonneg (1 : R); have := norm_nonneg ((q : R) ^ 2)
    have := norm_nonneg ((q : R) ^ 2 - 1); have := norm_nonneg (q : R)
    split_ifs
    · exact (hs _ w).trans (by nlinarith)
    · rw [neg_smul, one_smul, Finsupp.sum_norm_neg]; exact (h1 w).trans (by nlinarith)
    · rw [sub_eq_add_neg]
      refine (Finsupp.sum_norm_add_le _ _).trans ?_
      rw [Finsupp.sum_norm_neg]; exact (add_le_add (hs _ _) (hs _ _)).trans (by nlinarith)
    · rw [Finsupp.sum_norm_neg]; exact (hs _ _).trans (by nlinarith)
  | algebraMap r =>
    exact ⟨‖r‖ * ‖(1 : R)‖, by positivity, fun w ↦ by
      rw [AlgHom.commutes, Module.algebraMap_end_apply]; exact hs r w⟩
  | add _ _ _ _ hx hy =>
    obtain ⟨Bx, hBx0, hBx⟩ := hx; obtain ⟨By, hBy0, hBy⟩ := hy
    exact ⟨Bx + By, add_nonneg hBx0 hBy0, fun w ↦ by
      rw [map_add, LinearMap.add_apply]
      exact (Finsupp.sum_norm_add_le _ _).trans (add_le_add (hBx w) (hBy w))⟩
  | mul _ _ _ _ hx hy =>
    obtain ⟨Bx, hBx0, hBx⟩ := hx; obtain ⟨By, hBy0, hBy⟩ := hy
    exact ⟨Bx * By, mul_nonneg hBx0 hBy0, fun w ↦ by
      rw [map_mul, mul_apply_eq_comp]
      exact (LinearMap.sum_norm_apply_le _ hBx _).trans (mul_le_mul_of_nonneg_left (hBy w) hBx0)⟩

/-- **Sharp diagonal norm bound on cycle words.** -/
theorem norm_signedChecked_cycleWord_single_apply_le :
    ∀ {m : ℕ} (w : Fin (m + 1) → ι),
      ‖signedChecked pos q (cycleWord q (m + 1)) (single w 1) w‖ ≤
        ‖(1 : R)‖ * max 1 (max ‖(q : R) ^ 2‖ ‖(q : R) ^ 2 - 1‖) ^ m
  | 0, w => by rw [cycleWord_one, map_one, one_apply_eq_self, single_eq_same, pow_zero, mul_one]
  | m + 1, w => by
    set M : ℝ := max 1 (max ‖(q : R) ^ 2‖ ‖(q : R) ^ 2 - 1‖)
    conv_lhs => rw [← Fin.snoc_init_self w]
    rw [signedChecked_cycleWord_succ_snoc_apply, pow_succ M m, ← mul_assoc]
    have ih := norm_signedChecked_cycleWord_single_apply_le (Fin.init w)
    set z := signedChecked pos q (cycleWord q (m + 1)) (single (Fin.init w) 1) (Fin.init w)
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

omit [CompleteSpace R] in
/-- Absolute summability of the weighted diagonal coefficients of `signedChecked pos q x`. -/
theorem summable_norm_signedChecked_mul_prod {p : ι → R} (hp : Summable fun a ↦ ‖p a‖) (n : ℕ)
    (x : TypeAHeckeAlgebra R q n) :
    Summable fun w : Fin n → ι ↦ ‖signedChecked pos q x (single w 1) w * ∏ i, p (w i)‖ := by
  obtain ⟨C, _, hC⟩ := exists_norm_signedChecked_single_apply_le pos q x
  refine ((summable_norm_prod_of_summable_norm (f := fun _ : Fin n ↦ p) fun _ ↦ hp).mul_left
    C).of_nonneg_of_le (fun _ ↦ norm_nonneg _) fun w ↦
    (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (hC w w) (norm_nonneg _))

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
      ∑' w : Fin n → ι, signedChecked pos q x (single w 1) w * ∏ i, p (w i) := (rfl)

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
    (fun w _ ↦ Fintype.mem_piFinset.mpr fun i ↦ (w i).property)
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

/-- Conjugating `countableAtomicTrace` conjugates both the weights and the argument. -/
theorem star_countableAtomicTrace [StarRing R] [NormedStarGroup R]
    [Fact (IsSelfAdjoint (q : R))] (p : ι → R) (hp : Summable fun a ↦ ‖p a‖) {n : ℕ}
    (x : TypeAHeckeAlgebra R q n) :
    star (countableAtomicTrace pos q p hp n x) =
      countableAtomicTrace pos q (star ∘ p) (hp.congr fun _ ↦ (norm_star _).symm) n (star x) :=
  tendsto_nhds_unique
    ((continuous_star.tendsto _).comp (tendsto_atomicTrace_finset pos q p hp n x)) <|
    (tendsto_atomicTrace_finset pos q (star ∘ p) (hp.congr fun _ ↦ (norm_star _).symm) n
      (star x)).congr fun s ↦ (star_atomicTrace (fun a : s ↦ pos a) q (fun a : s ↦ p a) x).symm

/-- For self-adjoint weights, `countableAtomicTrace` commutes with `star`. -/
@[simp]
theorem countableAtomicTrace_star [StarRing R] [ContinuousStar R]
    [Fact (IsSelfAdjoint (q : R))] {p : ι → R} (hp_sum : Summable fun a ↦ ‖p a‖)
    (hp : ∀ a, IsSelfAdjoint (p a)) {n : ℕ} (x : TypeAHeckeAlgebra R q n) :
    countableAtomicTrace pos q p hp_sum n (star x) =
      star (countableAtomicTrace pos q p hp_sum n x) :=
  tendsto_nhds_unique (tendsto_atomicTrace_finset pos q p hp_sum n (star x)) <|
    ((continuous_star.tendsto _).comp (tendsto_atomicTrace_finset pos q p hp_sum n x)).congr
      fun s ↦ (atomicTrace_star (fun a : s ↦ pos a) q (fun a : s ↦ hp a) x).symm

/-- **Null space of a strictly positive countable atomic trace** over a complete normed
`StarOrderedRing` with `OrderClosedTopology` and no zero divisors:
`countableAtomicTrace (star x * x) = 0 ↔ signedChecked pos q x = 0`. -/
theorem countableAtomicTrace_star_mul_self_eq_zero_iff [PartialOrder R] [StarRing R]
    [StarOrderedRing R] [OrderClosedTopology R] [NoZeroDivisors R]
    [Fact (IsSelfAdjoint (q : R))] {p : ι → R} (hp : Summable fun a ↦ ‖p a‖)
    (hp0 : ∀ a, 0 < p a) {n : ℕ} (x : TypeAHeckeAlgebra R q n) :
    countableAtomicTrace pos q p hp n (star x * x) = 0 ↔ signedChecked pos q x = 0 := by
  refine ⟨fun hx ↦ ?_, fun hx ↦ by
    rw [countableAtomicTrace_apply, map_mul (signedChecked pos q), hx]; simp⟩
  rcases subsingleton_or_nontrivial R with _ | _
  · exact Subsingleton.elim _ _
  rw [countableAtomicTrace_apply] at hx
  have hsum : Summable fun w : Fin n → ι ↦
      signedChecked pos q (star x * x) (single w 1) w * ∏ i, p (w i) :=
    (summable_norm_signedChecked_mul_prod pos q hp n (star x * x)).of_norm
  have hnonneg (w : Fin n → ι) :
      0 ≤ signedChecked pos q (star x * x) (single w 1) w * ∏ i, p (w i) :=
    StarOrderedRing.mul_nonneg (signedChecked_star_mul_self_single_apply_nonneg pos q x w)
      (Finset.prod_nonneg_of_starOrderedRing fun i _ ↦ (hp0 (w i)).le)
  ext w u
  simp only [LinearMap.coe_comp, comp_apply, lsingle_apply, LinearMap.zero_apply,
    Finsupp.coe_zero, Pi.zero_apply]
  have hw : signedChecked pos q (star x * x) (single w 1) w * ∏ i, p (w i) = 0 :=
    le_antisymm ((hsum.le_tsum w fun _ _ ↦ hnonneg _).trans_eq hx) (hnonneg w)
  have hdiag : signedChecked pos q (star x * x) (single w 1) w = 0 :=
    (mul_eq_zero.mp hw).resolve_right (Finset.prod_ne_zero_iff.mpr fun i _ ↦ (hp0 (w i)).ne')
  rw [signedChecked_star_mul_self_single_apply] at hdiag
  have hcol := (Finset.sum_eq_zero_iff_of_nonneg fun _ _ ↦ star_mul_self_nonneg _).mp hdiag
  by_contra hne
  exact hne ((mul_eq_zero.mp (hcol u (Finsupp.mem_support_iff.mpr hne))).elim star_eq_zero.mp id)

/-- **Trace radical of a strictly positive countable atomic model** equals
`RingHom.ker (signedChecked)`. -/
theorem traceRadical_countableAtomicTrace_eq_ker_signedChecked [PartialOrder R] [StarRing R]
    [StarOrderedRing R] [OrderClosedTopology R] [NoZeroDivisors R]
    [Fact (IsSelfAdjoint (q : R))] {p : ι → R} (hp : Summable fun a ↦ ‖p a‖)
    (hp0 : ∀ a, 0 < p a) (n : ℕ) :
    (countableAtomicTrace pos q p hp n).traceRadical
        (countableAtomicTrace_mul_comm pos q p hp) =
      RingHom.ker (signedChecked pos q) := by
  ext x
  simp only [LinearMap.mem_traceRadical, RingHom.mem_ker]
  refine ⟨fun hx ↦ (countableAtomicTrace_star_mul_self_eq_zero_iff pos q hp hp0 x).mp
    (by rw [countableAtomicTrace_mul_comm]; exact hx (star x)), fun hx y ↦ ?_⟩
  rw [countableAtomicTrace_apply, map_mul (signedChecked pos q), hx]
  simp

/-- The complex countable atomic trace on `n` strands bundled as a `StarPositiveFunctional`. -/
noncomputable def countableAtomicPositiveFunctional (q : ℂˣ) [Fact (IsSelfAdjoint (q : ℂ))]
    {p : ι → ℂ} (hp : Summable fun a ↦ ‖p a‖) (hp0 : ∀ a, 0 ≤ p a) (n : ℕ) :
    StarPositiveFunctional (TypeAHeckeAlgebra ℂ q n) where
  toLinearMap := countableAtomicTrace pos q p hp n
  square_nonneg := countableAtomicTrace_star_mul_self_nonneg pos q hp hp0

/-- Forgetting positivity recovers the underlying countable atomic trace. -/
@[simp]
theorem toLinearMap_countableAtomicPositiveFunctional (q : ℂˣ) [Fact (IsSelfAdjoint (q : ℂ))]
    {p : ι → ℂ} (hp : Summable fun a ↦ ‖p a‖) (hp0 : ∀ a, 0 ≤ p a) (n : ℕ) :
    (countableAtomicPositiveFunctional pos q hp hp0 n).toLinearMap =
      countableAtomicTrace pos q p hp n := (rfl)

/-- Evaluating `countableAtomicPositiveFunctional` at an element recovers `countableAtomicTrace`. -/
@[simp]
theorem countableAtomicPositiveFunctional_apply (q : ℂˣ) [Fact (IsSelfAdjoint (q : ℂ))]
    {p : ι → ℂ} (hp : Summable fun a ↦ ‖p a‖) (hp0 : ∀ a, 0 ≤ p a) (n : ℕ)
    (x : TypeAHeckeAlgebra ℂ q n) :
    countableAtomicPositiveFunctional pos q hp hp0 n x =
      countableAtomicTrace pos q p hp n x := (rfl)

/-- **Cycle-word countable atomic trace at `Q = 1`** equals the signed `(m + 1)`-th power sum. -/
theorem countableAtomicTrace_cycleWord_of_sq_eq_one (hq : (q : R) ^ 2 = 1) (p : ι → R)
    (hp : Summable fun a ↦ ‖p a‖) (m : ℕ) :
    countableAtomicTrace pos q p hp (m + 1) (cycleWord q (m + 1)) =
      ∑' a, (if pos a then (1 : R) else -1) ^ m * p a ^ (m + 1) := by
  have hsign (a : ι) : ‖(if pos a then (1 : R) else -1) ^ m‖ = ‖(1 : R)‖ := by
    split_ifs <;> simp
  have hpow : Summable fun a ↦ ‖(if pos a then (1 : R) else -1) ^ m * p a ^ (m + 1)‖ :=
    (hp.mul_left (‖(1 : R)‖ * (∑' b, ‖p b‖) ^ m)).of_nonneg_of_le
      (fun _ ↦ norm_nonneg _) fun a ↦ (norm_mul_le _ _).trans <| by
        rw [hsign a, mul_assoc]
        refine mul_le_mul_of_nonneg_left ((norm_pow_le' (p a) (Nat.succ_pos m)).trans ?_)
          (norm_nonneg _)
        rw [pow_succ]; gcongr; exact hp.le_tsum a fun _ _ ↦ norm_nonneg _
  refine tendsto_nhds_unique
    (tendsto_atomicTrace_finset pos q p hp (m + 1) (cycleWord q (m + 1))) <|
    hpow.of_norm.hasSum.congr fun s ↦ ?_
  rw [← Finset.sum_attach s (fun a ↦ (if pos a then (1 : R) else -1) ^ m * p a ^ (m + 1)),
    ← Finset.univ_eq_attach, ← atomicTrace_cycleWord_of_sq_eq_one (fun a : s ↦ pos a) q hq]

private theorem countableAtomicTrace_eq_mul_of_slice (p : ι → R) (hp : Summable fun a ↦ ‖p a‖)
    {z : R} {n : ℕ} {x : TypeAHeckeAlgebra R q (n + 1)} {y : TypeAHeckeAlgebra R q (n + 2)}
    (e : (Fin (n + 1) → ι) × ι ≃ (Fin (n + 2) → ι)) (b : (Fin (n + 1) → ι) → ι)
    (P : ι → ι → Prop) [∀ u, DecidablePred (P u)] (hP : ∀ u, ¬ P u u)
    (hprod : ∀ w a, ∏ i, p (e (w, a) i) = p a * ∏ i, p (w i))
    (hdiag : ∀ w a, signedChecked pos q y (single (e (w, a)) 1) (e (w, a)) =
      ((q⁻¹ : Rˣ) : R) * signedChecked pos q x (single w 1) w *
        (if a = b w then (if pos (b w) then (q : R) ^ 2 else -1)
          else if P (b w) a then (q : R) ^ 2 - 1 else 0))
    (hz : ∀ u, (if pos u then (q : R) ^ 2 else -1) * p u +
      ((q : R) ^ 2 - 1) * (∑' a, if P u a then p a else 0) = q * z) :
    countableAtomicTrace pos q p hp (n + 2) y = z * countableAtomicTrace pos q p hp (n + 1) x := by
  classical
  rw [countableAtomicTrace_apply,
    (e.tsum_eq _).symm.trans (Summable.tsum_prod (e.summable_iff.mpr
      (summable_norm_signedChecked_mul_prod pos q hp (n + 2) y).of_norm)),
    countableAtomicTrace_apply,
    ← (summable_norm_signedChecked_mul_prod pos q hp (n + 1) x).of_norm.tsum_mul_left]
  congr 1 with w
  set u := b w
  have h₁ : Summable fun a ↦ if a = u then (if pos u then (q : R) ^ 2 else -1) * p u else 0 :=
    summable_of_ne_finset_zero (s := {u}) fun _ ha ↦ by simp [Finset.notMem_singleton.mp ha]
  have h_ite : Summable fun a ↦ ‖if P u a then p a else 0‖ :=
    hp.of_nonneg_of_le (fun _ ↦ norm_nonneg _) fun _ ↦ by split_ifs <;> simp
  have h₂ := h_ite.of_norm.mul_left ((q : R) ^ 2 - 1)
  have hdecomp (a : ι) :
      signedChecked pos q y (single (e (w, a)) 1) (e (w, a)) * ∏ i, p (e (w, a) i) =
        (((q⁻¹ : Rˣ) : R) * signedChecked pos q x (single w 1) w * ∏ i, p (w i)) *
          ((if a = u then (if pos u then (q : R) ^ 2 else -1) * p u else 0) +
            ((q : R) ^ 2 - 1) * (if P u a then p a else 0)) := by
    rw [hdiag w a, hprod w a]
    split_ifs <;> simp_all [u] <;> ring
  rw [funext hdecomp, (h₁.add h₂).tsum_mul_left, h₁.tsum_add h₂, tsum_ite_eq,
    h_ite.of_norm.tsum_mul_left, hz u]
  linear_combination (z * signedChecked pos q x (single w 1) w * ∏ i, p (w i)) * Units.inv_mul q

/-- **Countable first-site (left-slice) Markov rule** for `countableAtomicTrace`. -/
theorem countableAtomicTrace_T_zero_mul_tailIncl (p : ι → R) (hp : Summable fun a ↦ ‖p a‖)
    {z : R}
    (hz : ∀ b, (if pos b then (q : R) ^ 2 else -1) * p b +
      ((q : R) ^ 2 - 1) * (∑' a, if a < b then p a else 0) = q * z)
    {n : ℕ} (x : TypeAHeckeAlgebra R q (n + 1)) :
    countableAtomicTrace pos q p hp (n + 2) (T q (0 : Fin (n + 1)) * tailIncl q (n + 1) x) =
      z * countableAtomicTrace pos q p hp (n + 1) x := by
  rw [countableAtomicTrace_mul_comm]
  exact countableAtomicTrace_eq_mul_of_slice pos q p hp
    ((Equiv.prodComm (Fin (n + 1) → ι) ι).trans (Fin.consEquiv fun _ : Fin (n + 2) ↦ ι))
    (· 0) (fun u a ↦ a < u) lt_irrefl
    (fun w a ↦ by simp [Fin.prod_univ_succ (n := n + 1)])
    (fun w a ↦ signedChecked_tailIncl_mul_T_zero_single_cons_apply pos q x a w) hz

/-- **Countable atomic trace with scalar left slice is the Ocneanu trace.** -/
theorem countableAtomicTrace_eq_ocneanuTrace_of_leftSlice (p : ι → R)
    (hp : Summable fun a ↦ ‖p a‖) {z : R} (hp1 : ∑' a, p a = 1)
    (hz : ∀ b, (if pos b then (q : R) ^ 2 else -1) * p b +
      ((q : R) ^ 2 - 1) * (∑' a, if a < b then p a else 0) = q * z)
    {n : ℕ} (x : TypeAHeckeAlgebra R q n) :
    countableAtomicTrace pos q p hp n x =
      InfiniteTypeAHeckeAlgebra.ocneanuTrace R q z (toInfinite R q n x) :=
  (InfiniteTypeAHeckeAlgebra.isMarkovTrace_ocneanuTrace z).eq_toInfinite_of_T_zero_mul_tailIncl
    (countableAtomicTrace pos q p hp) (by simp) (by simp [hp1])
    (fun _ ↦ countableAtomicTrace_mul_comm pos q p hp)
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
  refine countableAtomicTrace_eq_mul_of_slice pos q p hp
    ((Equiv.prodComm (Fin (n + 1) → ι) ι).trans (Fin.snocEquiv fun _ : Fin (n + 2) ↦ ι))
    (· (Fin.last n)) (· < ·) lt_irrefl
    (fun w c ↦ by simp [Fin.prod_univ_castSucc (n := n + 1), mul_comm]) (fun w c ↦ ?_) hz
  simp only [Equiv.trans_apply, Equiv.prodComm_apply, Prod.swap_prod_mk, Fin.snocEquiv_apply,
    signedChecked_strandIncl_mul_T_last_single_snoc_apply]
  congr 1
  by_cases h : c = w (Fin.last n) <;> simp [h, eq_comm]

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

/-- Norm bound on the countable atomic trace of a cycle word `cycleWord (m + 1)`. -/
theorem norm_countableAtomicTrace_cycleWord_le {R : Type*} [NormedCommRing R] [CompleteSpace R]
    {ι : Type*} [LinearOrder ι] (pos : ι → Prop) [DecidablePred pos] (q : Rˣ) (p : ι → R)
    (hp : Summable fun a ↦ ‖p a‖) (m : ℕ) :
    ‖countableAtomicTrace pos q p hp (m + 1) (cycleWord q (m + 1))‖ ≤
      ‖(1 : R)‖ * max 1 (max ‖(q : R) ^ 2‖ ‖(q : R) ^ 2 - 1‖) ^ m *
        (∑' a, ‖p a‖) ^ (m + 1) := by
  have hp_norm : ∀ _ : Fin (m + 1), Summable fun a ↦ ‖‖p a‖‖ := fun _ ↦ by simpa using hp
  have hprod : Summable fun w : Fin (m + 1) → ι ↦ ∏ i, ‖p (w i)‖ := by
    simpa only [Real.norm_of_nonneg (Finset.prod_nonneg fun _ _ ↦ norm_nonneg _)] using
      summable_norm_prod_of_summable_norm hp_norm
  rw [countableAtomicTrace_apply]
  refine (norm_tsum_le_tsum_norm
    (summable_norm_signedChecked_mul_prod pos q hp (m + 1) (cycleWord q (m + 1)))).trans ?_
  refine ((summable_norm_signedChecked_mul_prod pos q hp (m + 1) _).tsum_le_tsum (fun w ↦
    (norm_mul_le _ _).trans (mul_le_mul (norm_signedChecked_cycleWord_single_apply_le pos q w)
      (Finset.norm_prod_le' _ Finset.univ_nonempty _) (norm_nonneg _) (by positivity)))
    (hprod.mul_left _)).trans_eq ?_
  rw [hprod.tsum_mul_left, ← prod_tsum_of_summable_norm hp_norm, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin]

private theorem norm_countableAtomicTrace_cycleWord_mul_pow_le {K : Type*}
    [NormedField K] [CompleteSpace K] {ι : Type*} [LinearOrder ι] (pos : ι → Prop)
    [DecidablePred pos] (q : Kˣ) (p : ι → K) (hp : Summable fun a ↦ ‖p a‖) (x : K) (m : ℕ) :
    ‖countableAtomicTrace pos q p hp (m + 1) (cycleWord q (m + 1)) * x ^ (m + 1)‖ ≤
      ((∑' a, ‖p a‖) * ‖x‖) *
        (max 1 (max ‖(q : K) ^ 2‖ ‖(q : K) ^ 2 - 1‖) * (∑' a, ‖p a‖) * ‖x‖) ^ m := by
  rw [norm_mul, norm_pow]
  refine (mul_le_mul_of_nonneg_right (norm_countableAtomicTrace_cycleWord_le pos q p hp m)
    (pow_nonneg (norm_nonneg x) _)).trans ?_
  rw [norm_one, one_mul]; exact le_of_eq (by ring)

private theorem eval_denom_ne_zero {K : Type*} [NormedField K] {ι : Type*} [Fintype ι]
    (pos : ι → Prop) [DecidablePred pos] (q : Kˣ) (p : ι → K) {x : K}
    (hx : max 1 (max ‖(q : K) ^ 2‖ ‖(q : K) ^ 2 - 1‖) * (∑ a, ‖p a‖) * ‖x‖ < 1) (a : ι) :
    (if pos a then 1 - (q : K) ^ 2 * p a * x else 1 + p a * x) ≠ 0 := by
  set M : ℝ := max 1 (max ‖(q : K) ^ 2‖ ‖(q : K) ^ 2 - 1‖)
  have hpa : ‖p a‖ ≤ ∑ b, ‖p b‖ :=
    Finset.single_le_sum (fun _ _ ↦ norm_nonneg _) (Finset.mem_univ a)
  have h1M : 1 ≤ M := le_max_left _ _
  have hQM : ‖(q : K) ^ 2‖ ≤ M := (le_max_left _ _).trans (le_max_right _ _)
  split_ifs <;> intro h0
  · have : ‖(q : K) ^ 2 * p a * x‖ = 1 := by simpa [sub_eq_zero.mp h0] using norm_one (α := K)
    have : ‖(q : K) ^ 2 * p a * x‖ ≤ M * (∑ b, ‖p b‖) * ‖x‖ := by simp only [norm_mul]; gcongr
    linarith
  · have : ‖p a * x‖ = 1 := by rw [eq_neg_of_add_eq_zero_right h0, norm_neg, norm_one]
    have : ‖p a * x‖ ≤ M * (∑ b, ‖p b‖) * ‖x‖ := by rw [norm_mul, ← one_mul ‖p a‖]; gcongr
    linarith

private theorem tsum_coeff_mul_pow_mul_eval_eq {K : Type*} [NormedField K] [CompleteSpace K]
    (F : PowerSeries K) (P Qp : Polynomial K) {x : K}
    (hF : Summable fun m : ℕ ↦ ‖PowerSeries.coeff m F * x ^ m‖)
    (hFP : F * (P : PowerSeries K) = (Qp : PowerSeries K)) :
    (∑' m : ℕ, PowerSeries.coeff m F * x ^ m) * P.eval x = Qp.eval x := by
  have hP : Summable fun m : ℕ ↦ ‖PowerSeries.coeff m (P : PowerSeries K) • x ^ m‖ :=
    summable_of_ne_finset_zero (s := Finset.range (P.natDegree + 1)) fun k hk ↦ by
      simp [P.coeff_eq_zero_of_natDegree_lt (by simpa using hk)]
  have heval := PowerSeries.evalAt_mul_of_summable_norm (b := x)
    (by simpa only [smul_eq_mul] using hF) hP
  rw [hFP, PowerSeries.evalAt_coe, PowerSeries.evalAt_coe, Polynomial.coe_aeval_eq_eval,
    PowerSeries.evalAt_def] at heval
  simpa only [smul_eq_mul] using heval.symm

/-- **Analytic evaluation of the cycle-trace generating function on a finite alphabet** on the disk
`max 1 (max ‖Q‖ ‖Q - 1‖) * (∑ a, ‖p a‖) * ‖x‖ < 1` (`Q = q ^ 2`). -/
theorem atomicTrace_cycleWord_generating_eval {K : Type*} [NormedField K]
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
        simpa [tsum_fintype] using norm_countableAtomicTrace_cycleWord_mul_pow_le pos q p hp x m
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
    simpa only [F, P, Qp, map_prod, Polynomial.coeToPowerSeries.ringHom_apply,
      apply_ite ((↑) : Polynomial K → PowerSeries K), Polynomial.coe_sub, Polynomial.coe_add,
      Polynomial.coe_one, Polynomial.coe_mul, Polynomial.coe_C, Polynomial.coe_X] using
      atomicTrace_cycleWord_generating_function pos q p
  have heval := tsum_coeff_mul_pow_mul_eval_eq F P Qp hF_sum hFP
  rw [hF_sum.of_norm.tsum_eq_zero_add] at heval
  simp only [F, P, Qp, PowerSeries.coeff_mk, ↓reduceIte, pow_zero, mul_one, Nat.succ_ne_zero,
    mul_assoc, hsum.of_norm.tsum_mul_left, Polynomial.eval_prod, apply_ite (Polynomial.eval x),
    Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_one, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X] at heval
  rw [show (∏ a, (if pos a then (1 - p a * x) / (1 - (q : K) ^ 2 * p a * x)
        else (1 + (q : K) ^ 2 * p a * x) / (1 + p a * x))) =
      (∏ a, (if pos a then 1 - p a * x else 1 + (q : K) ^ 2 * p a * x)) /
        ∏ a, (if pos a then 1 - (q : K) ^ 2 * p a * x else 1 + p a * x) by
    rw [← Finset.prod_div_distrib]; exact Finset.prod_congr rfl fun _ _ ↦ by split_ifs <;> rfl,
    eq_div_iff (Finset.prod_ne_zero_iff.mpr fun a _ ↦ eval_denom_ne_zero pos q p hx a)]
  simpa only [mul_assoc] using heval

/-- **Countable cycle-trace generating product** over any complete normed field `K` on the disk
`max 1 (max ‖Q‖ ‖Q - 1‖) * (∑' a, ‖p a‖) * ‖x‖ < 1` (`Q = q ^ 2`). -/
theorem countableAtomicTrace_cycleWord_hasProd {K : Type*} [NormedField K]
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
  have hmaj := (summable_geometric_of_lt_one (by positivity) hx).mul_left (S * ‖x‖)
  refine ⟨hmaj.of_nonneg_of_le (fun _ ↦ norm_nonneg _)
    (norm_countableAtomicTrace_cycleWord_mul_pow_le pos q p hp x), ?_⟩
  have hs_le (s : Finset ι) : ∑ a : s, ‖p a‖ ≤ S := by
    rw [Finset.univ_eq_attach, s.sum_attach fun a ↦ ‖p a‖]
    exact hp.sum_le_tsum s fun _ _ ↦ norm_nonneg _
  have hdom : Tendsto (fun s : Finset ι ↦ ∑' m : ℕ,
      atomicTrace (fun a : s ↦ pos a) q (fun a : s ↦ p a) (m + 1) (cycleWord q (m + 1)) *
        x ^ (m + 1)) atTop
      (𝓝 (∑' m : ℕ, countableAtomicTrace pos q p hp (m + 1) (cycleWord q (m + 1)) *
        x ^ (m + 1))) :=
    tendsto_tsum_of_dominated_convergence hmaj
      (fun m ↦ (tendsto_atomicTrace_finset pos q p hp (m + 1) (cycleWord q (m + 1))).mul_const _)
      (Eventually.of_forall fun s m ↦ by
        have hps : Summable fun a : s ↦ ‖p a‖ := (hasSum_fintype _).summable
        rw [← countableAtomicTrace_eq_atomicTrace (fun a : s ↦ pos a) q (fun a : s ↦ p a) hps]
        refine (norm_countableAtomicTrace_cycleWord_mul_pow_le _ q _ hps x m).trans ?_
        rw [tsum_fintype]; have := hs_le s; gcongr)
  refine (tendsto_const_nhds.add (hdom.const_mul _)).congr fun s ↦ ?_
  have hxs : M * (∑ a : s, ‖p a‖) * ‖x‖ < 1 :=
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hs_le s) (by positivity))
      (norm_nonneg x)).trans_lt hx
  rw [(atomicTrace_cycleWord_generating_eval (fun a : s ↦ pos a) q (fun a : s ↦ p a) hxs).2,
    Finset.univ_eq_attach, s.prod_attach (fun a ↦
      if pos a then (1 - p a * x) / (1 - (q : K) ^ 2 * p a * x)
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
  refine Tendsto.congr' (f₁ := fun N : ℕ ↦
      (if b then (1 - γ * x / N) / (1 - (q : ℂ) ^ 2 * γ * x / N)
        else (1 + (q : ℂ) ^ 2 * γ * x / N) / (1 + γ * x / N)) ^ N) ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with N hN
    have hsum_norm : ∑ _a : Fin N, ‖γ / (N : ℂ)‖ = ‖γ‖ := by
      simp [mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr (by omega) : (N : ℝ) ≠ 0)]
    rw [(atomicTrace_cycleWord_generating_eval (fun _ : Fin N ↦ b = true) q
      (fun _ ↦ γ / N) (by rwa [hsum_norm])).2, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin]
    cases b <;> · simp only [Bool.false_eq_true, ↓reduceIte]; congr 1; congr 1 <;> ring
  · have hlim (u v : ℂ) : Tendsto (fun N : ℕ ↦ (1 + u / N) ^ N / (1 + v / N) ^ N) atTop
        (𝓝 (Complex.exp (u - v))) := Complex.exp_sub u v ▸
      (Complex.tendsto_one_add_div_pow_exp u).div
        (Complex.tendsto_one_add_div_pow_exp v) (Complex.exp_ne_zero _)
    cases b
    · convert hlim ((q : ℂ) ^ 2 * γ * x) (γ * x) using 1
      · ext N; simp [div_pow]
      · congr 2; ring
    · convert hlim (-(γ * x)) (-((q : ℂ) ^ 2 * γ * x)) using 1
      · ext N; simp [div_pow, sub_eq_add_neg, neg_div]
      · congr 2; ring

end GeneratingProductAndDust

end TauCeti.TypeAHeckeAlgebra
