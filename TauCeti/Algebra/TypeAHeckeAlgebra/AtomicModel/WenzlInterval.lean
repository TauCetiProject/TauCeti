/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.Sum.Order
public import TauCeti.Algebra.TypeAHeckeAlgebra.AtomicModel.Countable
public import TauCeti.Algebra.TypeAHeckeAlgebra.Regular.Form
public import TauCeti.RingTheory.TraceFunctional.Radical
import Mathlib.Analysis.Complex.Order
import Mathlib.Topology.Algebra.InfiniteSum.Constructions
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-!
# Countable geometric models and positivity of positive-real Markov traces

For a real nonzero parameter `q : ℂˣ` (`IsSelfAdjoint (q : ℂ)`) with `Q = q ^ 2 > 0`, write the
Ocneanu trace parameter in projection coordinates as `z = q * η - q⁻¹ * (1 - η)`, so that
`q * z = (1 + Q) * η - 1`. In Wenzl's classification of positive Markov traces on the infinite
type-A Hecke algebra at positive real `Q`, the projection parameters `η` giving `⋆`-positive
states form the set `TauCeti.wenzlPositiveSet Q`, consisting of the closed continuous interval
`[min (1 / (1 + Q)) (Q / (1 + Q)), max (1 / (1 + Q)) (Q / (1 + Q))]` together with Wenzl's
discrete series `a_d(Q)` (`TauCeti.wenzlParam d Q`) for `d : ℤ`, `d ≠ 0`.

This file proves sufficiency — every parameter in `wenzlPositiveSet Q` yields a `⋆`-positive
Ocneanu trace (`TauCeti.InfiniteTypeAHeckeAlgebra.ocneanuTrace_star_mul_self_nonneg`, bundled as
`TauCeti.InfiniteTypeAHeckeAlgebra.ocneanuPositiveFunctional`) — by constructing concrete positive
models for each regime:

1. **The canonical symmetrizing trace (`z = 0`, covering the continuous interval `{1 / 2}` at
   `Q = 1`).** Over any commutative ring `R`, the canonical trace `canonicalTrace cs` on `n`
   strands agrees with `ocneanuTrace R q 0 ∘ toInfinite R q n`
   (`TauCeti.TypeAHeckeAlgebra.canonicalTrace_eq_ocneanuTrace_zero`). Consequently, for real
   nonzero `q`, `ocneanuTrace` at `z = 0` is both `⋆`-positive and faithful (`traceRadical = ⊥`)
   on `InfiniteTypeAHeckeAlgebra`
   (`TauCeti.InfiniteTypeAHeckeAlgebra.traceRadical_ocneanuTrace_zero`).
2. **Two-sided countable geometric progressions on `ℕ ⊕ₗ ℕᵒᵈ` (covering the continuous interval
   for `Q > 1` and `0 < Q < 1`).**
   * For `1 < Q`, placing positive letters along `ℕ` with weights `s / Q ^ (k + 1)`
     (`s = (1 + Q) * η - 1`) followed by negative letters along `ℕᵒᵈ` with weights
     `c / Q ^ (k + 1)` (`c = Q - (1 + Q) * η`) gives total weight `1`, constant left slice `s`,
     cycle-trace infinite product `(1 + c * x) / (1 - s * x)`, and nonnegative weights whenever
     `η ∈ [1 / (1 + Q), Q / (1 + Q)]`
     (`TauCeti.TypeAHeckeAlgebra.countableAtomicTrace_wenzlGtOneWeight_eq_ocneanuTrace`,
     `TauCeti.TypeAHeckeAlgebra.wenzlGtOneWeight_cycleWord_hasProd`).
   * For `0 < Q < 1`, placing negative letters along `ℕ` with weights `(1 - (1 + Q) * η) * Q ^ k`
     followed by positive letters along `ℕᵒᵈ` with weights `((1 + Q) * η - Q) * Q ^ k` gives total
     weight `1`, constant left slice `(1 + Q) * η - 1`, and nonnegative weights whenever
     `η ∈ [Q / (1 + Q), 1 / (1 + Q)]`
     (`TauCeti.TypeAHeckeAlgebra.countableAtomicTrace_wenzlLtOneWeight_eq_ocneanuTrace`).
3. **Finite positive and negative geometric atomic models (covering `d > 0` and `d < 0` for all
   `Q > 0`, including the uniform alphabet `p_i = 1 / r` at `Q = 1`).** These are realized by
   `atomicTrace_geometric_eq` and `atomicTrace_negGeometric_eq` together with
   `atomicTrace_star_mul_self_nonneg`.

Note on conventions: `wenzlPositiveSet Q` is invariant under `η ↦ 1 - η`
(`TauCeti.one_sub_mem_wenzlPositiveSet_iff`) and `Q ↦ Q⁻¹` (`TauCeti.wenzlPositiveSet_inv`), so
it coincides under both the `(T + q⁻¹) / (q + q⁻¹)` and `(q - T) / (q + q⁻¹)` eigenprojection
conventions. Only sufficiency (positivity on `wenzlPositiveSet Q`) is proved here; necessity is
not asserted.

## Main definitions

* `TauCeti.TypeAHeckeAlgebra.wenzlGtOnePos`, `TauCeti.TypeAHeckeAlgebra.wenzlGtOneWeight`:
  the signed alphabet `ℕ ⊕ₗ ℕᵒᵈ` and geometric weights for `1 < Q`.
* `TauCeti.TypeAHeckeAlgebra.wenzlLtOnePos`, `TauCeti.TypeAHeckeAlgebra.wenzlLtOneWeight`:
  the signed alphabet `ℕ ⊕ₗ ℕᵒᵈ` and geometric weights for `0 < Q < 1`.
* `TauCeti.wenzlPositiveSet`: Wenzl's positive-real projection parameter set.
* `TauCeti.InfiniteTypeAHeckeAlgebra.ocneanuPositiveFunctional`: `ocneanuTrace ℂ q z` bundled as a
  `StarPositiveFunctional` across `wenzlPositiveSet Q`.

## Main results

* `TauCeti.TypeAHeckeAlgebra.canonicalTrace_eq_ocneanuTrace_zero`: the canonical trace on `n`
  strands is `ocneanuTrace R q 0 ∘ toInfinite R q n`.
* `TauCeti.InfiniteTypeAHeckeAlgebra.star_ocneanuTrace`,
  `TauCeti.InfiniteTypeAHeckeAlgebra.ocneanuTrace_zero_star_mul_self_nonneg`, and
  `TauCeti.InfiniteTypeAHeckeAlgebra.traceRadical_ocneanuTrace_zero`: conjugation compatibility of
  `ocneanuTrace`, and positivity and faithfulness at `z = 0`.
* `TauCeti.TypeAHeckeAlgebra.countableAtomicTrace_wenzlGtOneWeight_eq_ocneanuTrace`,
  `TauCeti.TypeAHeckeAlgebra.wenzlGtOneWeight_cycleWord_hasProd`, and
  `TauCeti.TypeAHeckeAlgebra.countableAtomicTrace_wenzlLtOneWeight_eq_ocneanuTrace`: countable
  atomic realizations and telescoping generating product for Wenzl's continuous interval.
* `TauCeti.InfiniteTypeAHeckeAlgebra.ocneanuTrace_star_mul_self_nonneg`: positivity of the Ocneanu
  trace across `wenzlPositiveSet Q`.

## References

* H. Wenzl, *Hecke algebras of type A_n and subfactors*, Invent. Math. 92 (1988), 349–383, §3.
* Yu. A. Neretin, *Some remarks on traces on the infinite-dimensional Iwahori–Hecke algebra*,
  arXiv:2101.02133, §§1.6–1.7 and §3.1.
-/

public section

open Filter Function Finsupp OrderDual
open scoped Topology ComplexOrder

namespace TauCeti

section CanonicalOcneanu

namespace TypeAHeckeAlgebra

variable {R : Type*} [CommRing R] {q : Rˣ} {n : ℕ}

/-- Evaluation of the `A_∞` regular representation at `(single 1 1) 1` recovers the canonical
symmetrizing trace on every finite stage. -/
theorem canonicalTrace_eq_regularRep_toInfinite {W W' : Type*} [Group W] [Group W']
    (cs : CoxeterSystem (CoxeterMatrix.A (n - 1)) W)
    (cs' : CoxeterSystem coxeterMatrixAInfty W') (x : TypeAHeckeAlgebra R q n) :
    canonicalTrace cs x =
      InfiniteTypeAHeckeAlgebra.regularRep q cs' (toInfinite R q n x) (single 1 1) 1 := by
  classical
  have h : canonicalTrace (R := R) (q := q) cs =
      (Finsupp.lapply (1 : W')).comp ((LinearMap.applyₗ (single (1 : W') (1 : R))).comp
        ((InfiniteTypeAHeckeAlgebra.regularRep q cs').toLinearMap.comp
          (toInfinite R q n).toLinearMap)) := by
    refine (basisTw q cs).ext fun w ↦ ?_
    simp only [LinearMap.coe_comp, comp_apply, AlgHom.toLinearMap_apply,
      LinearMap.applyₗ_apply_apply, Finsupp.lapply_apply, coe_basisTw, canonicalTrace_Tw,
      regularRep_toInfinite_Tw_apply_single_one, single_apply]
    have hinj := cs.parabolicHom_injective (cs' := cs') coxeterMatrixA_eq_coxeterMatrixAInfty
    rw [eq_comm, map_eq_one_iff _ hinj]
  exact LinearMap.congr_fun h x

/-- **The canonical trace is the `z = 0` Ocneanu trace.** Over every commutative ring `R` and unit
`q : Rˣ`, the PBW identity-coefficient functional `canonicalTrace cs` agrees with
`ocneanuTrace R q 0` along `toInfinite`. -/
theorem canonicalTrace_eq_ocneanuTrace_zero {W : Type*} [Group W]
    (cs : CoxeterSystem (CoxeterMatrix.A (n - 1)) W) (x : TypeAHeckeAlgebra R q n) :
    canonicalTrace cs x = InfiniteTypeAHeckeAlgebra.ocneanuTrace R q 0 (toInfinite R q n x) := by
  classical
  let cs₀ (m : ℕ) := (CoxeterMatrix.A (m - 1)).toCoxeterSystem
  let cs' := coxeterMatrixAInfty.toCoxeterSystem
  rw [canonicalTrace_eq_regularRep_toInfinite cs cs',
    ← canonicalTrace_eq_regularRep_toInfinite (cs₀ n) cs']
  refine eq_ocneanuTrace_toInfinite (fun m ↦ canonicalTrace (cs₀ m))
    (canonicalTrace_one (cs₀ 0))
    (fun m y ↦ by
      rw [canonicalTrace_eq_regularRep_toInfinite (cs₀ (m + 1)) cs',
        canonicalTrace_eq_regularRep_toInfinite (cs₀ m) cs', toInfinite_strandIncl])
    (fun m ↦ canonicalTrace_mul_comm (cs₀ m))
    (fun m y ↦ ?_) n x
  rw [zero_mul, canonicalTrace_mul_comm]
  have hzero : (canonicalTrace (R := R) (q := q) (cs₀ (m + 2))).comp
      ((LinearMap.mulLeft R (T q (Fin.last m))).comp (strandIncl R q (m + 1)).toLinearMap) = 0 := by
    refine (basisTw q (cs₀ (m + 1))).ext fun w ↦ ?_
    simp only [LinearMap.coe_comp, comp_apply, AlgHom.toLinearMap_apply, LinearMap.mulLeft_apply,
      LinearMap.zero_apply, coe_basisTw,
      canonicalTrace_eq_regularRep_toInfinite (cs₀ (m + 2)) cs', map_mul, toInfinite_T,
      Fin.val_last, toInfinite_strandIncl, mul_apply_eq_comp,
      InfiniteTypeAHeckeAlgebra.regularRep_T, regularRep_toInfinite_Tw_apply_single_one]
    set u := (cs₀ (m + 1)).parabolicHom cs' coxeterMatrixA_eq_coxeterMatrixAInfty w
    have hsu : cs'.simple m * u ≠ 1 := by
      intro hmul
      have hmem : cs'.simple m ∈
          ((cs₀ (m + 1)).parabolicHom cs' coxeterMatrixA_eq_coxeterMatrixAInfty).range := by
        refine ⟨w⁻¹, ?_⟩
        rw [map_inv]
        exact (eq_inv_of_mul_eq_one_left hmul).symm
      rw [cs₀ (m + 1) |>.range_parabolicHom coxeterMatrixA_eq_coxeterMatrixAInfty,
        cs'.simple_mem_parabolic_iff] at hmem
      obtain ⟨j, hj⟩ := hmem
      exact absurd hj j.isLt.ne
    by_cases hd : cs'.IsLeftDescent u m
    · have hu1 : u ≠ 1 := fun h1 ↦ cs'.not_isLeftDescent_one m (h1 ▸ hd)
      rw [cs'.heckeLeftMul_single_of_isLeftDescent hd]
      simp [hu1.symm, hsu.symm]
    · rw [cs'.heckeLeftMul_single_of_not_isLeftDescent hd]
      simp [hsu.symm]
  exact LinearMap.congr_fun hzero y

end TypeAHeckeAlgebra

namespace InfiniteTypeAHeckeAlgebra

/-- Conjugating `ocneanuTrace R q z x` conjugates both the Markov parameter `z` and the element `x`
under the real-parameter involution. -/
theorem star_ocneanuTrace {R : Type*} [CommRing R] [StarRing R] {q : Rˣ}
    [Fact (IsSelfAdjoint (q : R))] (z : R) (x : InfiniteTypeAHeckeAlgebra R q) :
    star (ocneanuTrace R q z x) = ocneanuTrace R q (star z) (star x) := by
  let φ : InfiniteTypeAHeckeAlgebra R q →ₗ[R] R :=
    { toFun y := star (ocneanuTrace R q z (star y))
      map_add' a b := by simp
      map_smul' r a := by simp [star_smul] }
  have hφ : IsMarkovTrace (star z) φ :=
    { map_one := by simp [φ]
      map_mul_comm a b := by simp [φ, star_mul, (isMarkovTrace_ocneanuTrace z).map_mul_comm]
      map_mul_T {n a} ha := by
        have hcomm := (isMarkovTrace_ocneanuTrace (q := q) z).map_mul_comm (T q n) (star a)
        have ha' : star a ∈ stage R q (n + 1) := star_mem_stage_iff.mpr ha
        simp only [φ, LinearMap.coe_mk, AddHom.coe_mk, star_mul, star_T]
        rw [hcomm, (isMarkovTrace_ocneanuTrace z).map_mul_T ha', star_mul, mul_comm] }
  have heq := LinearMap.congr_fun hφ.eq_ocneanuTrace (star x)
  simpa [φ] using heq

/-- For a self-adjoint Markov parameter `z`, `ocneanuTrace R q z` commutes with `star`. -/
@[simp]
theorem ocneanuTrace_star {R : Type*} [CommRing R] [StarRing R] {q : Rˣ}
    [Fact (IsSelfAdjoint (q : R))] {z : R} (hz : IsSelfAdjoint z)
    (x : InfiniteTypeAHeckeAlgebra R q) :
    ocneanuTrace R q z (star x) = star (ocneanuTrace R q z x) := by
  rw [star_ocneanuTrace, hz.star_eq]

/-- **Positivity of the `z = 0` Ocneanu trace.** Over any commutative `StarOrderedRing` with a
star-fixed unit parameter `q`, `ocneanuTrace R q 0` is nonnegative on every square `star x * x`. -/
theorem ocneanuTrace_zero_star_mul_self_nonneg {R : Type*} [CommRing R] [PartialOrder R]
    [StarRing R] [StarOrderedRing R] {q : Rˣ} [Fact (IsSelfAdjoint (q : R))]
    (x : InfiniteTypeAHeckeAlgebra R q) :
    0 ≤ ocneanuTrace R q 0 (star x * x) := by
  obtain ⟨n, hx⟩ := exists_mem_stage x
  rw [← TypeAHeckeAlgebra.range_toInfinite, AlgHom.mem_range] at hx
  obtain ⟨y, rfl⟩ := hx
  rw [← TypeAHeckeAlgebra.toInfinite_star, ← map_mul,
    ← TypeAHeckeAlgebra.canonicalTrace_eq_ocneanuTrace_zero (permCoxeterSystem n),
    TypeAHeckeAlgebra.canonicalTrace_star_mul]
  exact Finset.sum_nonneg fun _ _ ↦ star_mul_self_nonneg _

/-- Over `ℝ` or `ℂ` (`RCLike 𝕜`), the `z = 0` Ocneanu trace form is anisotropic:
`ocneanuTrace 𝕜 q 0 (star x * x) = 0 ↔ x = 0`, including at `q = ±1`. -/
@[simp]
theorem ocneanuTrace_zero_star_mul_self_eq_zero_iff {𝕜 : Type*} [RCLike 𝕜] {q : 𝕜ˣ}
    [Fact (IsSelfAdjoint (q : 𝕜))] (x : InfiniteTypeAHeckeAlgebra 𝕜 q) :
    ocneanuTrace 𝕜 q 0 (star x * x) = 0 ↔ x = 0 := by
  obtain ⟨n, hx⟩ := exists_mem_stage x
  rw [← TypeAHeckeAlgebra.range_toInfinite, AlgHom.mem_range] at hx
  obtain ⟨y, rfl⟩ := hx
  rw [← TypeAHeckeAlgebra.toInfinite_star, ← map_mul,
    ← TypeAHeckeAlgebra.canonicalTrace_eq_ocneanuTrace_zero (permCoxeterSystem n),
    TypeAHeckeAlgebra.canonicalTrace_star_mul_self_eq_zero_iff,
    map_eq_zero_iff _ (TypeAHeckeAlgebra.toInfinite_injective 𝕜 q n)]

/-- **Faithfulness of the `z = 0` Ocneanu trace.** Over `ℝ` or `ℂ` with real nonzero parameter `q`,
the trace radical of `ocneanuTrace 𝕜 q 0` is trivial. -/
theorem traceRadical_ocneanuTrace_zero {𝕜 : Type*} [RCLike 𝕜] {q : 𝕜ˣ}
    [Fact (IsSelfAdjoint (q : 𝕜))] :
    (ocneanuTrace 𝕜 q 0).traceRadical (isMarkovTrace_ocneanuTrace 0).map_mul_comm = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  simp only [LinearMap.mem_traceRadical] at hx
  have h0 : ocneanuTrace 𝕜 q 0 (star x * x) = 0 := by
    rw [(isMarkovTrace_ocneanuTrace 0).map_mul_comm]
    exact hx (star x)
  exact (ocneanuTrace_zero_star_mul_self_eq_zero_iff x).mp h0

end InfiniteTypeAHeckeAlgebra

end CanonicalOcneanu

namespace TypeAHeckeAlgebra

section CountableGeometricModels

private def natSumDualEquiv : (ℕ ⊕ ℕ) ≃ (ℕ ⊕ₗ ℕᵒᵈ) :=
  (Equiv.sumCongr (Equiv.refl ℕ) toDual).trans toLex

private theorem summable_natSumDual {α : Type*} [AddCommMonoid α] [TopologicalSpace α]
    [ContinuousAdd α] {f : (ℕ ⊕ₗ ℕᵒᵈ) → α}
    (h₁ : Summable fun k : ℕ ↦ f (Sum.inlₗ k))
    (h₂ : Summable fun k : ℕ ↦ f (Sum.inrₗ (toDual k))) :
    Summable f :=
  natSumDualEquiv.summable_iff.mp (Summable.sum (f ∘ natSumDualEquiv) h₁ h₂)

private theorem tsum_natSumDual {α : Type*} [AddCommMonoid α] [TopologicalSpace α]
    [ContinuousAdd α] [T2Space α] {f : (ℕ ⊕ₗ ℕᵒᵈ) → α}
    (h₁ : Summable fun k : ℕ ↦ f (Sum.inlₗ k))
    (h₂ : Summable fun k : ℕ ↦ f (Sum.inrₗ (toDual k))) :
    (∑' a : ℕ ⊕ₗ ℕᵒᵈ, f a) =
      (∑' k : ℕ, f (Sum.inlₗ k)) + ∑' k : ℕ, f (Sum.inrₗ (toDual k)) := by
  rw [← natSumDualEquiv.tsum_eq]
  exact Summable.tsum_sum (f := f ∘ natSumDualEquiv) h₁ h₂

private theorem tsum_gt_eq_sub_sum_range {f : ℕ → ℝ} (hf : Summable f) (m : ℕ) :
    (Summable fun k : ℕ ↦ if m < k then f k else 0) ∧
      (∑' k : ℕ, if m < k then f k else 0) =
        (∑' k : ℕ, f k) - ∑ k ∈ Finset.range (m + 1), f k := by
  have hgt : Summable fun k : ℕ ↦ if m < k then f k else 0 :=
    hf.norm.of_norm_bounded fun k ↦ by
      split_ifs
      · exact le_rfl
      · rw [norm_zero]
        exact norm_nonneg _
  have hle : Summable fun k : ℕ ↦ if k < m + 1 then f k else 0 :=
    summable_of_ne_finset_zero (s := Finset.range (m + 1)) fun k hk ↦ by
      simp only [Finset.mem_range] at hk
      exact ite_eq_right hk
  have hadd : (∑ k ∈ Finset.range (m + 1), f k) + (∑' k : ℕ, if m < k then f k else 0) =
      ∑' k : ℕ, f k := by
    have hsum_le : (∑' k : ℕ, if k < m + 1 then f k else 0) = ∑ k ∈ Finset.range (m + 1), f k := by
      rw [tsum_eq_sum (s := Finset.range (m + 1)) fun k hk ↦ by
        simp only [Finset.mem_range] at hk
        exact ite_eq_right hk]
      exact Finset.sum_congr rfl fun k hk ↦ ite_eq_left (Finset.mem_range.mp hk)
    rw [← hsum_le, ← hle.tsum_add hgt]
    congr 1 with k
    by_cases hk : k < m + 1
    · have hnot : ¬m < k := by omega
      simp [hk, hnot]
    · have hlt : m < k := by omega
      simp [hk, hlt]
  exact ⟨hgt, eq_sub_of_add_eq' hadd⟩

private theorem tsum_lt_inl_natSumDual (f : (ℕ ⊕ₗ ℕᵒᵈ) → ℝ) (m : ℕ) :
    (∑' a : ℕ ⊕ₗ ℕᵒᵈ, if a < Sum.inlₗ m then f a else 0) =
      ∑ k ∈ Finset.range m, f (Sum.inlₗ k) := by
  have h1 : Summable fun k : ℕ ↦
      if (Sum.inlₗ k : ℕ ⊕ₗ ℕᵒᵈ) < Sum.inlₗ m then f (Sum.inlₗ k) else 0 :=
    summable_of_ne_finset_zero (s := Finset.range m) fun k hk ↦ by
      simp only [Sum.Lex.inl_lt_inl_iff]
      exact ite_eq_right (Finset.mem_range.not.mp hk)
  have h2 : Summable fun k : ℕ ↦
      if (Sum.inrₗ (toDual k) : ℕ ⊕ₗ ℕᵒᵈ) < Sum.inlₗ m then f (Sum.inrₗ (toDual k)) else 0 := by
    simp only [Sum.Lex.not_inr_lt_inl, ↓reduceIte]
    exact summable_zero
  have hsplit := tsum_natSumDual
    (f := fun a : ℕ ⊕ₗ ℕᵒᵈ ↦ if a < Sum.inlₗ m then f a else 0) h1 h2
  rw [hsplit]
  have hsum1 : (∑' k : ℕ, if (Sum.inlₗ k : ℕ ⊕ₗ ℕᵒᵈ) < Sum.inlₗ m then f (Sum.inlₗ k) else 0) =
      ∑ k ∈ Finset.range m, f (Sum.inlₗ k) := by
    simp only [Sum.Lex.inl_lt_inl_iff]
    rw [tsum_eq_sum (s := Finset.range m) fun k hk ↦ ite_eq_right (Finset.mem_range.not.mp hk)]
    exact Finset.sum_congr rfl fun k hk ↦ ite_eq_left (Finset.mem_range.mp hk)
  have hsum2 : (∑' k : ℕ, if (Sum.inrₗ (toDual k) : ℕ ⊕ₗ ℕᵒᵈ) < Sum.inlₗ m then
      f (Sum.inrₗ (toDual k)) else 0) = 0 := by
    simp only [Sum.Lex.not_inr_lt_inl, ↓reduceIte, tsum_zero]
  rw [hsum1, hsum2, add_zero]

private theorem tsum_lt_inr_natSumDual {f : (ℕ ⊕ₗ ℕᵒᵈ) → ℝ}
    (h₁ : Summable fun k : ℕ ↦ f (Sum.inlₗ k))
    (h₂ : Summable fun k : ℕ ↦ f (Sum.inrₗ (toDual k))) (m : ℕ) :
    (∑' a : ℕ ⊕ₗ ℕᵒᵈ, if a < Sum.inrₗ (toDual m) then f a else 0) =
      (∑' k : ℕ, f (Sum.inlₗ k)) + (∑' k : ℕ, f (Sum.inrₗ (toDual k))) -
        ∑ k ∈ Finset.range (m + 1), f (Sum.inrₗ (toDual k)) := by
  have h1 : Summable fun k : ℕ ↦
      if (Sum.inlₗ k : ℕ ⊕ₗ ℕᵒᵈ) < Sum.inrₗ (toDual m) then f (Sum.inlₗ k) else 0 := by
    simpa only [Sum.Lex.inl_lt_inr, ↓reduceIte] using h₁
  have hgt := tsum_gt_eq_sub_sum_range h₂ m
  have h2 : Summable fun k : ℕ ↦
      if (Sum.inrₗ (toDual k) : ℕ ⊕ₗ ℕᵒᵈ) < Sum.inrₗ (toDual m) then
        f (Sum.inrₗ (toDual k)) else 0 := by
    simpa only [Sum.Lex.inr_lt_inr_iff, toDual_lt_toDual] using hgt.1
  have hsplit := tsum_natSumDual
    (f := fun a : ℕ ⊕ₗ ℕᵒᵈ ↦ if a < Sum.inrₗ (toDual m) then f a else 0) h1 h2
  rw [hsplit]
  simp only [Sum.Lex.inl_lt_inr, Sum.Lex.inr_lt_inr_iff, toDual_lt_toDual, ↓reduceIte, hgt.2]
  ring

/-! ### The `1 < Q` countable model on `ℕ ⊕ₗ ℕᵒᵈ` -/

/-- Sign predicate on `ℕ ⊕ₗ ℕᵒᵈ` for Wenzl's continuous interval when `1 < Q`: positive letters on
the left (`ℕ`) followed by negative letters on the right (`ℕᵒᵈ`). -/
def wenzlGtOnePos (a : ℕ ⊕ₗ ℕᵒᵈ) : Prop :=
  (ofLex a).isLeft = true

instance : DecidablePred wenzlGtOnePos :=
  fun a ↦ inferInstanceAs (Decidable ((ofLex a).isLeft = true))

/-- Real geometric weights on `ℕ ⊕ₗ ℕᵒᵈ` for `1 < Q` and projection parameter `η`:
`((1 + Q) * η - 1) / Q ^ (k + 1)` on positive letters `Sum.inlₗ k` and
`(Q - (1 + Q) * η) / Q ^ (k + 1)` on negative letters `Sum.inrₗ (toDual k)`. -/
noncomputable def wenzlGtOneWeight (Q η : ℝ) (a : ℕ ⊕ₗ ℕᵒᵈ) : ℝ :=
  match ofLex a with
  | Sum.inl k => ((1 + Q) * η - 1) * Q⁻¹ * (Q⁻¹) ^ k
  | Sum.inr k => (Q - (1 + Q) * η) * Q⁻¹ * (Q⁻¹) ^ ofDual k

/-- For `1 < Q` and `η ∈ [1 / (1 + Q), Q / (1 + Q)]`, `wenzlGtOneWeight Q η` is nonnegative. -/
theorem wenzlGtOneWeight_nonneg {Q : ℝ} (hQ : 1 < Q) {η : ℝ}
    (hη : η ∈ Set.Icc (1 / (1 + Q)) (Q / (1 + Q))) (a : ℕ ⊕ₗ ℕᵒᵈ) :
    0 ≤ wenzlGtOneWeight Q η a := by
  have hr0 : 0 ≤ Q⁻¹ := inv_nonneg.mpr (zero_lt_one.trans hQ).le
  have h1Q : 0 < 1 + Q := by linarith
  have hs : 0 ≤ (1 + Q) * η - 1 := by
    have := (div_le_iff₀ h1Q).mp hη.1
    linarith
  have hc : 0 ≤ Q - (1 + Q) * η := by
    have := (le_div_iff₀ h1Q).mp hη.2
    linarith
  cases ha : ofLex a with
  | inl k =>
    simp only [wenzlGtOneWeight, ha]
    exact mul_nonneg (mul_nonneg hs hr0) (pow_nonneg hr0 k)
  | inr k =>
    simp only [wenzlGtOneWeight, ha]
    exact mul_nonneg (mul_nonneg hc hr0) (pow_nonneg hr0 (ofDual k))

/-- For `1 < Q` and any `η : ℝ`, `wenzlGtOneWeight Q η` is absolutely summable. -/
theorem summable_norm_wenzlGtOneWeight {Q : ℝ} (hQ : 1 < Q) (η : ℝ) :
    Summable fun a ↦ ‖wenzlGtOneWeight Q η a‖ := by
  have hr0 : 0 ≤ Q⁻¹ := inv_nonneg.mpr (zero_lt_one.trans hQ).le
  have hr1 : Q⁻¹ < 1 := inv_lt_one_of_one_lt₀ hQ
  have hgeom := summable_geometric_of_lt_one hr0 hr1
  refine summable_natSumDual ?_ ?_
  · refine (hgeom.mul_left ‖((1 + Q) * η - 1) * Q⁻¹‖).congr fun k ↦ ?_
    dsimp only [wenzlGtOneWeight, ofLex_toLex]
    simp only [norm_mul, norm_pow, Real.norm_of_nonneg hr0]
  · refine (hgeom.mul_left ‖(Q - (1 + Q) * η) * Q⁻¹‖).congr fun k ↦ ?_
    dsimp only [wenzlGtOneWeight, ofLex_toLex, ofDual_toDual]
    simp only [norm_mul, norm_pow, Real.norm_of_nonneg hr0]

/-- For `1 < Q` and any `η : ℝ`, the total weight of `wenzlGtOneWeight Q η` is `1`. -/
theorem tsum_wenzlGtOneWeight {Q : ℝ} (hQ : 1 < Q) (η : ℝ) :
    (∑' a, wenzlGtOneWeight Q η a) = 1 := by
  have hQ0 : Q ≠ 0 := (zero_lt_one.trans hQ).ne'
  have hQ1 : Q - 1 ≠ 0 := sub_ne_zero.mpr hQ.ne'
  have hr0 : 0 ≤ Q⁻¹ := inv_nonneg.mpr (zero_lt_one.trans hQ).le
  have hr1 : Q⁻¹ < 1 := inv_lt_one_of_one_lt₀ hQ
  have hgeom := summable_geometric_of_lt_one hr0 hr1
  rw [tsum_natSumDual (hgeom.mul_left _) (hgeom.mul_left _)]
  simp only [wenzlGtOneWeight, ofLex_toLex, ofDual_toDual]
  rw [hgeom.tsum_mul_left, hgeom.tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1]
  field_simp
  ring

/-- Every left slice of `wenzlGtOneWeight Q η` equals `(1 + Q) * η - 1`. -/
theorem wenzlGtOneWeight_leftSlice {Q : ℝ} (hQ : 1 < Q) (η : ℝ) (b : ℕ ⊕ₗ ℕᵒᵈ) :
    (if wenzlGtOnePos b then Q else -1) * wenzlGtOneWeight Q η b +
      (Q - 1) * (∑' a, if a < b then wenzlGtOneWeight Q η a else 0) = (1 + Q) * η - 1 := by
  set s := (1 + Q) * η - 1
  set c := Q - (1 + Q) * η
  have hQ0 : Q ≠ 0 := (zero_lt_one.trans hQ).ne'
  have hQ1 : Q - 1 ≠ 0 := sub_ne_zero.mpr hQ.ne'
  have hr0 : 0 ≤ Q⁻¹ := inv_nonneg.mpr (zero_lt_one.trans hQ).le
  have hr1 : Q⁻¹ < 1 := inv_lt_one_of_one_lt₀ hQ
  have hgeom := summable_geometric_of_lt_one hr0 hr1
  have htel (r : ℝ) (m : ℕ) :
      (Q - 1) * ∑ k ∈ Finset.range m, r * Q⁻¹ * (Q⁻¹) ^ k = r * (1 - (Q⁻¹) ^ m) := by
    calc (Q - 1) * ∑ k ∈ Finset.range m, r * Q⁻¹ * (Q⁻¹) ^ k
        = r * ((1 - Q⁻¹) * ∑ k ∈ Finset.range m, (Q⁻¹) ^ k) := by
          rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun k _ ↦ ?_
          field_simp
      _ = r * (1 - (Q⁻¹) ^ m) := by rw [mul_neg_geom_sum]
  cases hb : ofLex b with
  | inl m =>
    have hbrw : b = Sum.inlₗ m := (toLex_ofLex b).symm.trans (congrArg toLex hb)
    subst hbrw
    rw [tsum_lt_inl_natSumDual (wenzlGtOneWeight Q η) m]
    simp only [wenzlGtOnePos, wenzlGtOneWeight, ofLex_toLex, Sum.isLeft_inl, ↓reduceIte, htel]
    simp only [inv_pow]
    dsimp only [s]
    field_simp
    ring
  | inr m' =>
    obtain ⟨m, rfl⟩ : ∃ m : ℕ, toDual m = m' := ⟨ofDual m', rfl⟩
    have hbrw : b = Sum.inrₗ (toDual m) := (toLex_ofLex b).symm.trans (congrArg toLex hb)
    subst hbrw
    rw [tsum_lt_inr_natSumDual (f := wenzlGtOneWeight Q η)
      (hgeom.mul_left (s * Q⁻¹)) (hgeom.mul_left (c * Q⁻¹)) m]
    simp only [wenzlGtOnePos, wenzlGtOneWeight, ofLex_toLex, ofDual_toDual, Sum.isLeft_inr,
      Bool.false_eq_true, ↓reduceIte]
    rw [hgeom.tsum_mul_left, hgeom.tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1,
      mul_sub, mul_add, htel]
    simp only [inv_pow]
    dsimp only [s]
    field_simp
    ring

/-- **Countable geometric realization of the Ocneanu trace for `1 < Q`.** When `(q : ℂ) ^ 2 = Q`
with `1 < Q`, the countable atomic trace of `wenzlGtOneWeight Q η` on `ℕ ⊕ₗ ℕᵒᵈ` equals
`ocneanuTrace ℂ q ((q : ℂ) * η - (↑q⁻¹ : ℂ) * (1 - η))` along `toInfinite`. -/
theorem countableAtomicTrace_wenzlGtOneWeight_eq_ocneanuTrace {q : ℂˣ} {Q : ℝ} (hQ : 1 < Q)
    (hqQ : (q : ℂ) ^ 2 = Q) (η : ℝ) {n : ℕ} (x : TypeAHeckeAlgebra ℂ q n) :
    countableAtomicTrace wenzlGtOnePos q (fun a ↦ (wenzlGtOneWeight Q η a : ℂ))
        ((summable_norm_wenzlGtOneWeight hQ η).congr fun a ↦ (Complex.norm_real _).symm) n x =
      InfiniteTypeAHeckeAlgebra.ocneanuTrace ℂ q
        ((q : ℂ) * η - (↑q⁻¹ : ℂ) * (1 - η)) (toInfinite ℂ q n x) := by
  refine countableAtomicTrace_eq_ocneanuTrace_of_leftSlice wenzlGtOnePos q _ _ ?_ (fun b ↦ ?_) x
  · rw [← Complex.ofReal_tsum, tsum_wenzlGtOneWeight hQ η, Complex.ofReal_one]
  · have hsl := congrArg ((↑) : ℝ → ℂ) (wenzlGtOneWeight_leftSlice hQ η b)
    push_cast [Complex.ofReal_tsum, apply_ite ((↑) : ℝ → ℂ)] at hsl
    rw [← hqQ] at hsl
    have _ : (q : ℂ) ≠ 0 := q.ne_zero
    rw [hsl, Units.val_inv_eq_inv_val]
    field_simp
    ring

/-- **Telescoping infinite product for Wenzl's `1 < Q` countable model.** For `1 < Q`,
`η ∈ [1 / (1 + Q), Q / (1 + Q)]`, and `Q * ‖x‖ < 1`, the cycle-trace infinite product over
`ℕ ⊕ₗ ℕᵒᵈ` converges (`HasProd`) to `(1 + c * x) / (1 - s * x)` with `s = (1 + Q) * η - 1` and
`c = Q - (1 + Q) * η`. -/
theorem wenzlGtOneWeight_cycleWord_hasProd {q : ℂˣ} {Q : ℝ} (hQ : 1 < Q) (hqQ : (q : ℂ) ^ 2 = Q)
    {η : ℝ} (hη : η ∈ Set.Icc (1 / (1 + Q)) (Q / (1 + Q))) {x : ℂ} (hx : Q * ‖x‖ < 1) :
    HasProd (fun a : ℕ ⊕ₗ ℕᵒᵈ ↦
        if wenzlGtOnePos a then
          (1 - (wenzlGtOneWeight Q η a : ℂ) * x) /
            (1 - (q : ℂ) ^ 2 * (wenzlGtOneWeight Q η a : ℂ) * x)
        else
          (1 + (q : ℂ) ^ 2 * (wenzlGtOneWeight Q η a : ℂ) * x) /
            (1 + (wenzlGtOneWeight Q η a : ℂ) * x))
      ((1 + ((Q - (1 + Q) * η : ℝ) : ℂ) * x) /
        (1 - (((1 + Q) * η - 1 : ℝ) : ℂ) * x)) := by
  have hp : Summable fun a ↦ ‖(wenzlGtOneWeight Q η a : ℂ)‖ :=
    (summable_norm_wenzlGtOneWeight hQ η).congr fun a ↦ (Complex.norm_real _).symm
  have hnorm_sum : (∑' a, ‖(wenzlGtOneWeight Q η a : ℂ)‖) = 1 := by
    have heq : (fun a ↦ ‖(wenzlGtOneWeight Q η a : ℂ)‖) = wenzlGtOneWeight Q η := by
      ext a
      rw [Complex.norm_real, Real.norm_of_nonneg (wenzlGtOneWeight_nonneg hQ hη a)]
    rw [heq, tsum_wenzlGtOneWeight hQ η]
  have hmax : max 1 (max ‖(q : ℂ) ^ 2‖ ‖(q : ℂ) ^ 2 - 1‖) = Q := by
    have h1 : ‖(q : ℂ) ^ 2‖ = Q := by
      rw [hqQ, Complex.norm_real, Real.norm_of_nonneg (zero_lt_one.trans hQ).le]
    have h2 : ‖(q : ℂ) ^ 2 - 1‖ = Q - 1 := by
      rw [hqQ, ← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
        Real.norm_of_nonneg (sub_nonneg.mpr hQ.le)]
    rw [h1, h2, max_eq_left (a := Q) (b := Q - 1) (by linarith), max_eq_right hQ.le]
  have hdisk : max 1 (max ‖(q : ℂ) ^ 2‖ ‖(q : ℂ) ^ 2 - 1‖) *
      (∑' a, ‖(wenzlGtOneWeight Q η a : ℂ)‖) * ‖x‖ < 1 := by
    rwa [hmax, hnorm_sum, mul_one]
  have hprod := (countableAtomicTrace_cycleWord_hasProd wenzlGtOnePos q _ hp hdisk).2
  set s : ℝ := (1 + Q) * η - 1
  have hs0 : 0 ≤ s := by
    have := (div_le_iff₀ (by linarith : 0 < 1 + Q)).mp hη.1
    linarith
  have hsQ : s ≤ Q := by
    have := (le_div_iff₀ (by linarith : 0 < 1 + Q)).mp hη.2
    linarith
  have hsx : ‖(s : ℂ) * x‖ < 1 := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hs0]
    exact (mul_le_mul_of_nonneg_right hsQ (norm_nonneg x)).trans_lt hx
  have hval : 1 + ((q : ℂ) ^ 2 - 1) * (∑' m : ℕ, countableAtomicTrace wenzlGtOnePos q
      (fun a ↦ (wenzlGtOneWeight Q η a : ℂ)) hp (m + 1) (cycleWord q (m + 1)) * x ^ (m + 1)) =
      (1 + ((Q - (1 + Q) * η : ℝ) : ℂ) * x) / (1 - (s : ℂ) * x) := by
    have htr (m : ℕ) : countableAtomicTrace wenzlGtOnePos q
        (fun a ↦ (wenzlGtOneWeight Q η a : ℂ)) hp (m + 1) (cycleWord q (m + 1)) * x ^ (m + 1) =
        x * ((s : ℂ) * x) ^ m := by
      rw [countableAtomicTrace_wenzlGtOneWeight_eq_ocneanuTrace hQ hqQ η, toInfinite_cycleWord,
        (InfiniteTypeAHeckeAlgebra.isMarkovTrace_ocneanuTrace _).map_cycleWord, Nat.add_sub_cancel]
      have hqz : (q : ℂ) * ((q : ℂ) * η - (↑q⁻¹ : ℂ) * (1 - η)) = (s : ℂ) := by
        have _ : (q : ℂ) ≠ 0 := q.ne_zero
        dsimp only [s]
        push_cast
        rw [← hqQ]
        field_simp
        ring
      rw [hqz]
      ring
    simp_rw [htr]
    have hgeom : Summable fun m : ℕ ↦ ((s : ℂ) * x) ^ m := summable_geometric_of_norm_lt_one hsx
    have hne : 1 - (s : ℂ) * x ≠ 0 := fun h0 ↦ by
      have : (1 : ℝ) = ‖(s : ℂ) * x‖ := by simpa [sub_eq_zero.mp h0] using (norm_one (α := ℂ)).symm
      linarith
    have hmul : (1 - (s : ℂ) * x)⁻¹ * (1 - (s : ℂ) * x) = 1 := inv_mul_cancel₀ hne
    rw [hgeom.tsum_mul_left, tsum_geometric_of_norm_lt_one hsx, hqQ, eq_div_iff hne]
    dsimp only [s] at hmul ⊢
    push_cast at hmul ⊢
    linear_combination ((Q : ℂ) - 1) * x * hmul
  rwa [hval] at hprod

/-! ### The `0 < Q < 1` countable model on `ℕ ⊕ₗ ℕᵒᵈ` -/

/-- Sign predicate on `ℕ ⊕ₗ ℕᵒᵈ` for Wenzl's continuous interval when `0 < Q < 1`: negative letters
on the left (`ℕ`) followed by positive letters on the right (`ℕᵒᵈ`). -/
def wenzlLtOnePos (a : ℕ ⊕ₗ ℕᵒᵈ) : Prop :=
  (ofLex a).isRight = true

instance : DecidablePred wenzlLtOnePos :=
  fun a ↦ inferInstanceAs (Decidable ((ofLex a).isRight = true))

/-- Real geometric weights on `ℕ ⊕ₗ ℕᵒᵈ` for `0 < Q < 1` and projection parameter `η`:
`(1 - (1 + Q) * η) * Q ^ k` on negative letters `Sum.inlₗ k` and
`((1 + Q) * η - Q) * Q ^ k` on positive letters `Sum.inrₗ (toDual k)`. -/
noncomputable def wenzlLtOneWeight (Q η : ℝ) (a : ℕ ⊕ₗ ℕᵒᵈ) : ℝ :=
  match ofLex a with
  | Sum.inl k => (1 - (1 + Q) * η) * Q ^ k
  | Sum.inr k => ((1 + Q) * η - Q) * Q ^ ofDual k

/-- For `0 < Q < 1` and `η ∈ [Q / (1 + Q), 1 / (1 + Q)]`, `wenzlLtOneWeight Q η` is nonnegative. -/
theorem wenzlLtOneWeight_nonneg {Q : ℝ} (hQ0 : 0 < Q) {η : ℝ}
    (hη : η ∈ Set.Icc (Q / (1 + Q)) (1 / (1 + Q))) (a : ℕ ⊕ₗ ℕᵒᵈ) :
    0 ≤ wenzlLtOneWeight Q η a := by
  have h1Q : 0 < 1 + Q := by linarith
  have hu : 0 ≤ 1 - (1 + Q) * η := by
    have := (le_div_iff₀ h1Q).mp hη.2
    linarith
  have hv : 0 ≤ (1 + Q) * η - Q := by
    have := (div_le_iff₀ h1Q).mp hη.1
    linarith
  cases ha : ofLex a with
  | inl k =>
    simp only [wenzlLtOneWeight, ha]
    exact mul_nonneg hu (pow_nonneg hQ0.le k)
  | inr k =>
    simp only [wenzlLtOneWeight, ha]
    exact mul_nonneg hv (pow_nonneg hQ0.le (ofDual k))

/-- For `0 < Q < 1` and any `η : ℝ`, `wenzlLtOneWeight Q η` is absolutely summable. -/
theorem summable_norm_wenzlLtOneWeight {Q : ℝ} (hQ0 : 0 < Q) (hQ1 : Q < 1) (η : ℝ) :
    Summable fun a ↦ ‖wenzlLtOneWeight Q η a‖ := by
  have hgeom := summable_geometric_of_lt_one hQ0.le hQ1
  refine summable_natSumDual ?_ ?_
  · refine (hgeom.mul_left ‖1 - (1 + Q) * η‖).congr fun k ↦ ?_
    dsimp only [wenzlLtOneWeight, ofLex_toLex]
    simp only [norm_mul, norm_pow, Real.norm_of_nonneg hQ0.le]
  · refine (hgeom.mul_left ‖(1 + Q) * η - Q‖).congr fun k ↦ ?_
    dsimp only [wenzlLtOneWeight, ofLex_toLex, ofDual_toDual]
    simp only [norm_mul, norm_pow, Real.norm_of_nonneg hQ0.le]

/-- For `0 < Q < 1` and any `η : ℝ`, the total weight of `wenzlLtOneWeight Q η` is `1`. -/
theorem tsum_wenzlLtOneWeight {Q : ℝ} (hQ0 : 0 < Q) (hQ1 : Q < 1) (η : ℝ) :
    (∑' a, wenzlLtOneWeight Q η a) = 1 := by
  have h1Q : 1 - Q ≠ 0 := sub_ne_zero.mpr hQ1.ne'
  have hgeom := summable_geometric_of_lt_one hQ0.le hQ1
  rw [tsum_natSumDual (hgeom.mul_left _) (hgeom.mul_left _)]
  simp only [wenzlLtOneWeight, ofLex_toLex, ofDual_toDual]
  rw [hgeom.tsum_mul_left, hgeom.tsum_mul_left, tsum_geometric_of_lt_one hQ0.le hQ1]
  field_simp
  ring

/-- Every left slice of `wenzlLtOneWeight Q η` equals `(1 + Q) * η - 1`. -/
theorem wenzlLtOneWeight_leftSlice {Q : ℝ} (hQ0 : 0 < Q) (hQ1 : Q < 1) (η : ℝ)
    (b : ℕ ⊕ₗ ℕᵒᵈ) :
    (if wenzlLtOnePos b then Q else -1) * wenzlLtOneWeight Q η b +
      (Q - 1) * (∑' a, if a < b then wenzlLtOneWeight Q η a else 0) = (1 + Q) * η - 1 := by
  set u := 1 - (1 + Q) * η
  set v := (1 + Q) * η - Q
  have h1Q : 1 - Q ≠ 0 := sub_ne_zero.mpr hQ1.ne'
  have hgeom := summable_geometric_of_lt_one hQ0.le hQ1
  have htel (r : ℝ) (m : ℕ) : (Q - 1) * ∑ k ∈ Finset.range m, r * Q ^ k = -r * (1 - Q ^ m) := by
    calc (Q - 1) * ∑ k ∈ Finset.range m, r * Q ^ k
        = -r * ((1 - Q) * ∑ k ∈ Finset.range m, Q ^ k) := by
          rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
          exact Finset.sum_congr rfl fun k _ ↦ by ring
      _ = -r * (1 - Q ^ m) := by rw [mul_neg_geom_sum]
  cases hb : ofLex b with
  | inl m =>
    have hbrw : b = Sum.inlₗ m := (toLex_ofLex b).symm.trans (congrArg toLex hb)
    subst hbrw
    rw [tsum_lt_inl_natSumDual (wenzlLtOneWeight Q η) m]
    simp only [wenzlLtOnePos, wenzlLtOneWeight, ofLex_toLex, Sum.isRight_inl, Bool.false_eq_true,
      ↓reduceIte, htel]
    ring
  | inr m' =>
    obtain ⟨m, rfl⟩ : ∃ m : ℕ, toDual m = m' := ⟨ofDual m', rfl⟩
    have hbrw : b = Sum.inrₗ (toDual m) := (toLex_ofLex b).symm.trans (congrArg toLex hb)
    subst hbrw
    rw [tsum_lt_inr_natSumDual (f := wenzlLtOneWeight Q η)
      (hgeom.mul_left u) (hgeom.mul_left v) m]
    simp only [wenzlLtOnePos, wenzlLtOneWeight, ofLex_toLex, ofDual_toDual, Sum.isRight_inr,
      ↓reduceIte]
    rw [hgeom.tsum_mul_left, hgeom.tsum_mul_left, tsum_geometric_of_lt_one hQ0.le hQ1,
      mul_sub, mul_add, htel]
    field_simp
    ring

/-- **Countable geometric realization of the Ocneanu trace for `0 < Q < 1`.** When
`(q : ℂ) ^ 2 = Q` with `0 < Q < 1`, the countable atomic trace of `wenzlLtOneWeight Q η` on
`ℕ ⊕ₗ ℕᵒᵈ` equals `ocneanuTrace ℂ q ((q : ℂ) * η - (↑q⁻¹ : ℂ) * (1 - η))` along `toInfinite`. -/
theorem countableAtomicTrace_wenzlLtOneWeight_eq_ocneanuTrace {q : ℂˣ} {Q : ℝ} (hQ0 : 0 < Q)
    (hQ1 : Q < 1) (hqQ : (q : ℂ) ^ 2 = Q) (η : ℝ) {n : ℕ} (x : TypeAHeckeAlgebra ℂ q n) :
    countableAtomicTrace wenzlLtOnePos q (fun a ↦ (wenzlLtOneWeight Q η a : ℂ))
        ((summable_norm_wenzlLtOneWeight hQ0 hQ1 η).congr fun a ↦ (Complex.norm_real _).symm) n x =
      InfiniteTypeAHeckeAlgebra.ocneanuTrace ℂ q
        ((q : ℂ) * η - (↑q⁻¹ : ℂ) * (1 - η)) (toInfinite ℂ q n x) := by
  refine countableAtomicTrace_eq_ocneanuTrace_of_leftSlice wenzlLtOnePos q _ _ ?_ (fun b ↦ ?_) x
  · rw [← Complex.ofReal_tsum, tsum_wenzlLtOneWeight hQ0 hQ1 η, Complex.ofReal_one]
  · have hsl := congrArg ((↑) : ℝ → ℂ) (wenzlLtOneWeight_leftSlice hQ0 hQ1 η b)
    push_cast [Complex.ofReal_tsum, apply_ite ((↑) : ℝ → ℂ)] at hsl
    rw [← hqQ] at hsl
    have _ : (q : ℂ) ≠ 0 := q.ne_zero
    rw [hsl, Units.val_inv_eq_inv_val]
    field_simp
    ring

end CountableGeometricModels

end TypeAHeckeAlgebra

/-! ### Wenzl's positive-real parameter set and positivity of `ocneanuTrace` -/

/-- **Wenzl's positive-real projection parameter set** for `Q > 0`: the closed continuous interval
between `1 / (1 + Q)` and `Q / (1 + Q)` together with the discrete series `wenzlParam d Q` for
nonzero integers `d : ℤ`. -/
noncomputable def wenzlPositiveSet (Q : ℝ) : Set ℝ :=
  Set.Icc (min (1 / (1 + Q)) (Q / (1 + Q))) (max (1 / (1 + Q)) (Q / (1 + Q))) ∪
    {η | ∃ d : ℤ, d ≠ 0 ∧ η = wenzlParam d Q}

/-- Every nonzero integer parameter `wenzlParam d Q` lies in `wenzlPositiveSet Q`. -/
theorem wenzlParam_mem_wenzlPositiveSet {d : ℤ} (hd : d ≠ 0) (Q : ℝ) :
    wenzlParam d Q ∈ wenzlPositiveSet Q :=
  Or.inr ⟨d, hd, rfl⟩

/-- When `1 ≤ Q`, the interval `[1 / (1 + Q), Q / (1 + Q)]` is contained in `wenzlPositiveSet Q`. -/
theorem mem_wenzlPositiveSet_of_mem_Icc_of_one_le {Q : ℝ} (hQ : 1 ≤ Q) {η : ℝ}
    (hη : η ∈ Set.Icc (1 / (1 + Q)) (Q / (1 + Q))) :
    η ∈ wenzlPositiveSet Q := by
  have hle : 1 / (1 + Q) ≤ Q / (1 + Q) :=
    div_le_div_of_nonneg_right hQ (by linarith)
  exact Or.inl ⟨(min_eq_left hle).symm ▸ hη.1, (max_eq_right hle).symm ▸ hη.2⟩

/-- When `0 ≤ Q ≤ 1`, the interval `[Q / (1 + Q), 1 / (1 + Q)]` is contained in
`wenzlPositiveSet Q`. -/
theorem mem_wenzlPositiveSet_of_mem_Icc_of_le_one {Q : ℝ} (hQ0 : 0 ≤ Q) (hQ1 : Q ≤ 1) {η : ℝ}
    (hη : η ∈ Set.Icc (Q / (1 + Q)) (1 / (1 + Q))) :
    η ∈ wenzlPositiveSet Q := by
  have hle : Q / (1 + Q) ≤ 1 / (1 + Q) :=
    div_le_div_of_nonneg_right hQ1 (by linarith)
  exact Or.inl ⟨(min_eq_right hle).symm ▸ hη.1, (max_eq_left hle).symm ▸ hη.2⟩

/-- Inversion symmetry `wenzlPositiveSet Q⁻¹ = wenzlPositiveSet Q` for `0 < Q`. -/
theorem wenzlPositiveSet_inv {Q : ℝ} (hQ : 0 < Q) :
    wenzlPositiveSet Q⁻¹ = wenzlPositiveSet Q := by
  have h1 : 1 / (1 + Q⁻¹) = Q / (1 + Q) := by field_simp; ring
  have h2 : Q⁻¹ / (1 + Q⁻¹) = 1 / (1 + Q) := by field_simp; ring
  ext η
  simp only [wenzlPositiveSet, Set.mem_union, Set.mem_Icc, Set.mem_ofPred_eq, h1, h2,
    min_comm (Q / (1 + Q)), max_comm (Q / (1 + Q)), wenzlParam_inv]

/-- Complement symmetry `1 - η ∈ wenzlPositiveSet Q ↔ η ∈ wenzlPositiveSet Q` for `0 < Q`,
matching the two eigenprojection conventions `(T + q⁻¹) / (q + q⁻¹)` and `(q - T) / (q + q⁻¹)`. -/
theorem one_sub_mem_wenzlPositiveSet_iff {Q : ℝ} (hQ : 0 < Q) {η : ℝ} :
    1 - η ∈ wenzlPositiveSet Q ↔ η ∈ wenzlPositiveSet Q := by
  suffices h : ∀ x, x ∈ wenzlPositiveSet Q → 1 - x ∈ wenzlPositiveSet Q from
    ⟨fun hx ↦ by simpa using h (1 - η) hx, h η⟩
  rintro x (hx | ⟨d, hd, rfl⟩)
  · left
    have h1Q : 1 + Q ≠ 0 := by linarith
    have hc1 : 1 - 1 / (1 + Q) = Q / (1 + Q) := by field_simp; ring
    have hc2 : 1 - Q / (1 + Q) = 1 / (1 + Q) := by field_simp; ring
    rcases le_total (1 / (1 + Q)) (Q / (1 + Q)) with hle | hle
    · rw [min_eq_left hle, max_eq_right hle] at hx ⊢
      exact ⟨by linarith [hx.2], by linarith [hx.1]⟩
    · rw [min_eq_right hle, max_eq_left hle] at hx ⊢
      exact ⟨by linarith [hx.2], by linarith [hx.1]⟩
  · right
    refine ⟨-d, neg_ne_zero.mpr hd, ?_⟩
    have hZ : 0 < ∑ i ∈ Finset.range d.natAbs, Q ^ i :=
      Finset.sum_pos (fun i _ ↦ pow_pos hQ i)
        (Finset.nonempty_range_iff.mpr (Int.natAbs_ne_zero.mpr hd))
    have hden : (1 + Q) * ∑ i ∈ Finset.range d.natAbs, Q ^ i ≠ 0 :=
      mul_ne_zero (by linarith) hZ.ne'
    linarith [wenzlParam_add_wenzlParam_neg hden]

namespace InfiniteTypeAHeckeAlgebra

private theorem pos_of_ofReal_eq_sq {q : ℂˣ} [Fact (IsSelfAdjoint (q : ℂ))] {Q : ℝ}
    (hQ : (Q : ℂ) = (q : ℂ) ^ 2) : 0 < Q := by
  have him : (q : ℂ).im = 0 :=
    Complex.conj_eq_iff_im.mp (Fact.out : IsSelfAdjoint (q : ℂ)).star_eq
  have hre : (q : ℂ) = ((q : ℂ).re : ℂ) := Complex.ext (by simp) (by simp [him])
  have hQre : Q = (q : ℂ).re ^ 2 :=
    Complex.ofReal_injective (hQ.trans ((congrArg (· ^ 2) hre).trans (Complex.ofReal_pow _ 2).symm))
  have hne : (q : ℂ).re ≠ 0 := fun h0 ↦ q.ne_zero (by rw [hre, h0, Complex.ofReal_zero])
  rw [hQre]
  exact sq_pos_of_ne_zero hne

private theorem ofReal_wenzlParam (d : ℤ) (Q : ℝ) :
    ((wenzlParam d Q : ℝ) : ℂ) = wenzlParam d (Q : ℂ) := by
  obtain ⟨r, rfl | rfl⟩ := Int.eq_nat_or_neg d
  · simp [wenzlParam_natCast]
  · simp [wenzlParam_neg_natCast]

private theorem ocneanuTrace_wenzlParam_natSucc_nonneg {q : ℂˣ} [Fact (IsSelfAdjoint (q : ℂ))]
    {Q : ℝ} (hQ0 : 0 < Q) (hQ : (Q : ℂ) = (q : ℂ) ^ 2) (r : ℕ) {n : ℕ}
    (y : TypeAHeckeAlgebra ℂ q n) :
    0 ≤ ocneanuTrace ℂ q ((q : ℂ) * ((wenzlParam ((r + 1 : ℕ) : ℤ) Q : ℝ) : ℂ) -
        (↑q⁻¹ : ℂ) * (1 - ((wenzlParam ((r + 1 : ℕ) : ℤ) Q : ℝ) : ℂ)))
      (TypeAHeckeAlgebra.toInfinite ℂ q n (star y * y)) := by
  set Z : ℝ := ∑ a ∈ Finset.range (r + 1), Q ^ a
  have hZ0 : 0 < Z :=
    Finset.sum_pos (fun a _ ↦ pow_pos hQ0 a) (Finset.nonempty_range_iff.mpr (Nat.succ_ne_zero r))
  set c : ℝ := Z⁻¹
  have hcZ : (c : ℂ) * ∑ a ∈ Finset.range (r + 1), ((q : ℂ) ^ 2) ^ a = 1 := by
    have hr : c * Z = 1 := inv_mul_cancel₀ hZ0.ne'
    have hcast := congrArg ((↑) : ℝ → ℂ) hr
    push_cast [Z, hQ] at hcast
    exact hcast
  have hz : (q : ℂ) * ((wenzlParam ((r + 1 : ℕ) : ℤ) Q : ℝ) : ℂ) -
      (↑q⁻¹ : ℂ) * (1 - ((wenzlParam ((r + 1 : ℕ) : ℤ) Q : ℝ) : ℂ)) =
      (c : ℂ) * (q : ℂ) ^ (2 * r + 1) := by
    have h1Q : 1 + (q : ℂ) ^ 2 ≠ 0 := by
      rw [← hQ, ← Complex.ofReal_one, ← Complex.ofReal_add]
      exact Complex.ofReal_ne_zero.mpr (by linarith)
    have hZc : ∑ a ∈ Finset.range (r + 1), ((q : ℂ) ^ 2) ^ a ≠ 0 :=
      right_ne_zero_of_mul_eq_one hcZ
    have hq0 : (q : ℂ) ≠ 0 := q.ne_zero
    rw [ofReal_wenzlParam, hQ, wenzlParam_natCast, Units.val_inv_eq_inv_val,
      geom_sum_succ' (n := r + 1)]
    field_simp
    linear_combination -((1 + (q : ℂ) ^ 2) * (q : ℂ) ^ (2 * r + 2)) * hcZ
  rw [hz, ← TypeAHeckeAlgebra.atomicTrace_geometric_eq q hcZ (star y * y)]
  refine TypeAHeckeAlgebra.atomicTrace_star_mul_self_nonneg _ q (fun a ↦ ?_) y
  have ha : 0 ≤ c * Q ^ (a : ℕ) := by positivity
  simpa [hQ] using Complex.zero_le_real.mpr ha

private theorem ocneanuTrace_wenzlParam_negNatSucc_nonneg {q : ℂˣ} [Fact (IsSelfAdjoint (q : ℂ))]
    {Q : ℝ} (hQ0 : 0 < Q) (hQ : (Q : ℂ) = (q : ℂ) ^ 2) (r : ℕ) {n : ℕ}
    (y : TypeAHeckeAlgebra ℂ q n) :
    0 ≤ ocneanuTrace ℂ q ((q : ℂ) * ((wenzlParam (-((r + 1 : ℕ) : ℤ)) Q : ℝ) : ℂ) -
        (↑q⁻¹ : ℂ) * (1 - ((wenzlParam (-((r + 1 : ℕ) : ℤ)) Q : ℝ) : ℂ)))
      (TypeAHeckeAlgebra.toInfinite ℂ q n (star y * y)) := by
  set Z : ℝ := ∑ a ∈ Finset.range (r + 1), Q ^ a
  have hZ0 : 0 < Z :=
    Finset.sum_pos (fun a _ ↦ pow_pos hQ0 a) (Finset.nonempty_range_iff.mpr (Nat.succ_ne_zero r))
  set c : ℝ := Z⁻¹
  have hcZ : (c : ℂ) * ∑ a ∈ Finset.range (r + 1), ((q : ℂ) ^ 2) ^ a = 1 := by
    have hr : c * Z = 1 := inv_mul_cancel₀ hZ0.ne'
    have hcast := congrArg ((↑) : ℝ → ℂ) hr
    push_cast [Z, hQ] at hcast
    exact hcast
  have hz : (q : ℂ) * ((wenzlParam (-((r + 1 : ℕ) : ℤ)) Q : ℝ) : ℂ) -
      (↑q⁻¹ : ℂ) * (1 - ((wenzlParam (-((r + 1 : ℕ) : ℤ)) Q : ℝ) : ℂ)) =
      -((c : ℂ) * ↑q⁻¹) := by
    have h1Q : 1 + (q : ℂ) ^ 2 ≠ 0 := by
      rw [← hQ, ← Complex.ofReal_one, ← Complex.ofReal_add]
      exact Complex.ofReal_ne_zero.mpr (by linarith)
    have hZc : ∑ a ∈ Finset.range (r + 1), ((q : ℂ) ^ 2) ^ a ≠ 0 :=
      right_ne_zero_of_mul_eq_one hcZ
    have hq0 : (q : ℂ) ≠ 0 := q.ne_zero
    have hg : ∑ a ∈ Finset.range (r + 1), ((q : ℂ) ^ 2) ^ a =
        (q : ℂ) ^ 2 * ∑ a ∈ Finset.range r, ((q : ℂ) ^ 2) ^ a + 1 := by
      rw [Finset.sum_range_succ', Finset.mul_sum, pow_zero]
      congr 1
      exact Finset.sum_congr rfl fun a _ ↦ by ring
    rw [ofReal_wenzlParam, hQ, wenzlParam_neg_natCast, Nat.add_sub_cancel,
      Units.val_inv_eq_inv_val]
    field_simp
    linear_combination -((1 + (q : ℂ) ^ 2) * hg) + (1 + (q : ℂ) ^ 2) * hcZ
  rw [hz, ← TypeAHeckeAlgebra.atomicTrace_negGeometric_eq q hcZ (star y * y)]
  refine TypeAHeckeAlgebra.atomicTrace_star_mul_self_nonneg _ q (fun a ↦ ?_) y
  have ha : 0 ≤ c * Q ^ (a : ℕ) := by positivity
  simpa [hQ] using Complex.zero_le_real.mpr ha

/-- **Positivity of the Ocneanu trace across Wenzl's positive-real parameter set.** For every real
nonzero parameter `q : ℂˣ` (`IsSelfAdjoint (q : ℂ)`) with `(Q : ℂ) = (q : ℂ) ^ 2` and every
projection parameter `η ∈ wenzlPositiveSet Q`, the Ocneanu trace with parameter
`z = q * η - q⁻¹ * (1 - η)` is nonnegative on every square `star x * x` in
`InfiniteTypeAHeckeAlgebra ℂ q`. -/
theorem ocneanuTrace_star_mul_self_nonneg {q : ℂˣ} [Fact (IsSelfAdjoint (q : ℂ))] {Q : ℝ}
    (hQ : (Q : ℂ) = (q : ℂ) ^ 2) {η : ℝ} (hη : η ∈ wenzlPositiveSet Q)
    (x : InfiniteTypeAHeckeAlgebra ℂ q) :
    0 ≤ ocneanuTrace ℂ q ((q : ℂ) * η - (↑q⁻¹ : ℂ) * (1 - η)) (star x * x) := by
  have hQ0 : 0 < Q := pos_of_ofReal_eq_sq hQ
  obtain ⟨n, hx⟩ := exists_mem_stage x
  rw [← TypeAHeckeAlgebra.range_toInfinite, AlgHom.mem_range] at hx
  obtain ⟨y, rfl⟩ := hx
  rcases hη with hIcc | ⟨d, hd, rfl⟩
  · rcases lt_trichotomy Q 1 with hQ1 | rfl | hQ1
    · have hle : Q / (1 + Q) ≤ 1 / (1 + Q) := div_le_div_of_nonneg_right hQ1.le (by linarith)
      rw [min_eq_right hle, max_eq_left hle] at hIcc
      rw [← TypeAHeckeAlgebra.toInfinite_star, ← map_mul,
        ← TypeAHeckeAlgebra.countableAtomicTrace_wenzlLtOneWeight_eq_ocneanuTrace hQ0 hQ1 hQ.symm]
      exact TypeAHeckeAlgebra.countableAtomicTrace_star_mul_self_nonneg _ q _
        (fun a ↦ Complex.zero_le_real.mpr (TypeAHeckeAlgebra.wenzlLtOneWeight_nonneg hQ0 hIcc a)) y
    · have hη_half : η = 1 / 2 := by
        rw [show (1 : ℝ) / (1 + 1) = 1 / 2 by norm_num, min_self, max_self,
          Set.Icc_self, Set.mem_singleton_iff] at hIcc
        exact hIcc
      subst hη_half
      have hz0 : (q : ℂ) * ((1 / 2 : ℝ) : ℂ) - (↑q⁻¹ : ℂ) * (1 - ((1 / 2 : ℝ) : ℂ)) = 0 := by
        have _ : (q : ℂ) ≠ 0 := q.ne_zero
        have hq2 : (q : ℂ) ^ 2 = 1 := by simpa using hQ.symm
        rw [Units.val_inv_eq_inv_val]
        push_cast
        field_simp
        linear_combination hq2
      rw [hz0]
      exact ocneanuTrace_zero_star_mul_self_nonneg _
    · have hle : 1 / (1 + Q) ≤ Q / (1 + Q) := div_le_div_of_nonneg_right hQ1.le (by linarith)
      rw [min_eq_left hle, max_eq_right hle] at hIcc
      rw [← TypeAHeckeAlgebra.toInfinite_star, ← map_mul,
        ← TypeAHeckeAlgebra.countableAtomicTrace_wenzlGtOneWeight_eq_ocneanuTrace hQ1 hQ.symm]
      exact TypeAHeckeAlgebra.countableAtomicTrace_star_mul_self_nonneg _ q _
        (fun a ↦ Complex.zero_le_real.mpr (TypeAHeckeAlgebra.wenzlGtOneWeight_nonneg hQ1 hIcc a)) y
  · rw [← TypeAHeckeAlgebra.toInfinite_star, ← map_mul]
    obtain ⟨r, rfl | rfl⟩ := Int.eq_nat_or_neg d
    · rcases r with _ | r
      · exact absurd rfl hd
      · exact ocneanuTrace_wenzlParam_natSucc_nonneg hQ0 hQ r y
    · rcases r with _ | r
      · simp at hd
      · exact ocneanuTrace_wenzlParam_negNatSucc_nonneg hQ0 hQ r y

/-- The complex Ocneanu trace on `InfiniteTypeAHeckeAlgebra ℂ q` bundled as a
`StarPositiveFunctional` for every real nonzero `q : ℂˣ` and every projection parameter
`η ∈ wenzlPositiveSet Q` (`(Q : ℂ) = (q : ℂ) ^ 2`). -/
noncomputable def ocneanuPositiveFunctional (q : ℂˣ) [Fact (IsSelfAdjoint (q : ℂ))] {Q : ℝ}
    (hQ : (Q : ℂ) = (q : ℂ) ^ 2) {η : ℝ} (hη : η ∈ wenzlPositiveSet Q) :
    StarPositiveFunctional (InfiniteTypeAHeckeAlgebra ℂ q) where
  toLinearMap := ocneanuTrace ℂ q ((q : ℂ) * η - (↑q⁻¹ : ℂ) * (1 - η))
  square_nonneg := ocneanuTrace_star_mul_self_nonneg hQ hη

@[simp]
theorem ocneanuPositiveFunctional_apply (q : ℂˣ) [Fact (IsSelfAdjoint (q : ℂ))] {Q : ℝ}
    (hQ : (Q : ℂ) = (q : ℂ) ^ 2) {η : ℝ} (hη : η ∈ wenzlPositiveSet Q)
    (x : InfiniteTypeAHeckeAlgebra ℂ q) :
    ocneanuPositiveFunctional q hQ hη x =
      ocneanuTrace ℂ q ((q : ℂ) * η - (↑q⁻¹ : ℂ) * (1 - η)) x :=
  (rfl)

end InfiniteTypeAHeckeAlgebra

end TauCeti
