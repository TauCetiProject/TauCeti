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

For real nonzero `q : ℂˣ` (`IsSelfAdjoint (q : ℂ)`) with `Q = q ^ 2 > 0`, writing
`z = q * η - q⁻¹ * (1 - η)` gives `q * z = (1 + Q) * η - 1`. We define Wenzl's positive-real set
`TauCeti.wenzlPositiveSet Q` (the closed interval between `1 / (1 + Q)` and `Q / (1 + Q)` union
`TauCeti.wenzlParam d Q` for `d ≠ 0`), verify its `η ↦ 1 - η` and `Q ↦ Q⁻¹` symmetries, and prove
sufficiency (`TauCeti.InfiniteTypeAHeckeAlgebra.ocneanuTrace_star_mul_self_nonneg`, bundled as
`TauCeti.InfiniteTypeAHeckeAlgebra.ocneanuPositiveFunctional`) via three explicit models:
1. **Canonical symmetrizing trace (`z = 0`, `η = 1 / 2` at `Q = 1`)**: agrees with `canonicalTrace`
   on every finite stage (`canonicalTrace_eq_ocneanuTrace_zero`) and is positive and faithful
   (`traceRadical_ocneanuTrace_zero`).
2. **Two-sided geometric models on `ℕ ⊕ₗ ℕᵒᵈ` (`1 < Q` and `0 < Q < 1`)**: `wenzlGtOneWeight` and
   `wenzlLtOneWeight` realize the continuous interval, with telescoping cycle-trace product
   `(1 + c * x) / (1 - s * x)` for `1 < Q` (`wenzlGtOneWeight_cycleWord_hasProd`).
3. **Finite positive/negative geometric atomic models (`d ≠ 0`, `Q > 0`)**.

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

/-- Evaluating the `A_∞` regular representation at `(single 1 1) 1` recovers `canonicalTrace`. -/
theorem canonicalTrace_eq_regularRep_toInfinite {W W' : Type*} [Group W] [Group W']
    (cs : CoxeterSystem (CoxeterMatrix.A (n - 1)) W)
    (cs' : CoxeterSystem coxeterMatrixAInfty W') (x : TypeAHeckeAlgebra R q n) :
    canonicalTrace cs x =
      InfiniteTypeAHeckeAlgebra.regularRep q cs' (toInfinite R q n x) (single 1 1) 1 := by
  classical
  refine LinearMap.congr_fun ((basisTw q cs).ext (f₁ := canonicalTrace (R := R) (q := q) cs)
    (f₂ := (Finsupp.lapply (1 : W')).comp ((LinearMap.applyₗ (single (1 : W') (1 : R))).comp
      ((InfiniteTypeAHeckeAlgebra.regularRep q cs').toLinearMap.comp
        (toInfinite R q n).toLinearMap))) fun w ↦ ?_) x
  simp only [LinearMap.coe_comp, comp_apply, AlgHom.toLinearMap_apply,
    LinearMap.applyₗ_apply_apply, Finsupp.lapply_apply, coe_basisTw, canonicalTrace_Tw,
    regularRep_toInfinite_Tw_apply_single_one, single_apply]
  rw [eq_comm, map_eq_one_iff _
    (cs.parabolicHom_injective (cs' := cs') coxeterMatrixA_eq_coxeterMatrixAInfty)]

/-- **The canonical trace is the `z = 0` Ocneanu trace** along `toInfinite`. -/
theorem canonicalTrace_eq_ocneanuTrace_zero {W : Type*} [Group W]
    (cs : CoxeterSystem (CoxeterMatrix.A (n - 1)) W) (x : TypeAHeckeAlgebra R q n) :
    canonicalTrace cs x = InfiniteTypeAHeckeAlgebra.ocneanuTrace R q 0 (toInfinite R q n x) := by
  classical
  let cs₀ (m : ℕ) := (CoxeterMatrix.A (m - 1)).toCoxeterSystem
  let cs' := coxeterMatrixAInfty.toCoxeterSystem
  rw [canonicalTrace_eq_regularRep_toInfinite cs cs',
    ← canonicalTrace_eq_regularRep_toInfinite (cs₀ n) cs']
  refine eq_ocneanuTrace_toInfinite (fun m ↦ canonicalTrace (cs₀ m))
    (canonicalTrace_one (cs₀ 0)) (fun m y ↦ by
      rw [canonicalTrace_eq_regularRep_toInfinite (cs₀ (m + 1)) cs',
        canonicalTrace_eq_regularRep_toInfinite (cs₀ m) cs', toInfinite_strandIncl])
    (fun m ↦ canonicalTrace_mul_comm (cs₀ m)) (fun m y ↦ ?_) n x
  rw [zero_mul, canonicalTrace_mul_comm]
  refine LinearMap.congr_fun ((basisTw q (cs₀ (m + 1))).ext
    (f₁ := (canonicalTrace (R := R) (q := q) (cs₀ (m + 2))).comp
      ((LinearMap.mulLeft R (T q (Fin.last m))).comp (strandIncl R q (m + 1)).toLinearMap))
    (f₂ := 0) fun w ↦ ?_) y
  simp only [LinearMap.coe_comp, comp_apply, AlgHom.toLinearMap_apply, LinearMap.mulLeft_apply,
    LinearMap.zero_apply, coe_basisTw,
    canonicalTrace_eq_regularRep_toInfinite (cs₀ (m + 2)) cs', map_mul, toInfinite_T,
    Fin.val_last, toInfinite_strandIncl, mul_apply_eq_comp,
    InfiniteTypeAHeckeAlgebra.regularRep_T, regularRep_toInfinite_Tw_apply_single_one]
  set u := (cs₀ (m + 1)).parabolicHom cs' coxeterMatrixA_eq_coxeterMatrixAInfty w
  have hsu : cs'.simple m * u ≠ 1 := fun hmul ↦ by
    have hmem : cs'.simple m ∈
        ((cs₀ (m + 1)).parabolicHom cs' coxeterMatrixA_eq_coxeterMatrixAInfty).range :=
      ⟨w⁻¹, by rw [map_inv]; exact (eq_inv_of_mul_eq_one_left hmul).symm⟩
    rw [(cs₀ (m + 1)).range_parabolicHom coxeterMatrixA_eq_coxeterMatrixAInfty,
      cs'.simple_mem_parabolic_iff] at hmem
    obtain ⟨j, hj⟩ := hmem; exact j.isLt.ne hj
  by_cases hd : cs'.IsLeftDescent u m
  · have hu1 : u ≠ 1 := fun h1 ↦ cs'.not_isLeftDescent_one m (h1 ▸ hd)
    rw [cs'.heckeLeftMul_single_of_isLeftDescent hd]; simp [hu1.symm, hsu.symm]
  · rw [cs'.heckeLeftMul_single_of_not_isLeftDescent hd]; simp [hsu.symm]

end TypeAHeckeAlgebra

namespace InfiniteTypeAHeckeAlgebra

/-- Conjugating `ocneanuTrace R q z x` conjugates both `z` and `x`. -/
theorem star_ocneanuTrace {R : Type*} [CommRing R] [StarRing R] {q : Rˣ}
    [Fact (IsSelfAdjoint (q : R))] (z : R) (x : InfiniteTypeAHeckeAlgebra R q) :
    star (ocneanuTrace R q z x) = ocneanuTrace R q (star z) (star x) := by
  let φ : InfiniteTypeAHeckeAlgebra R q →ₗ[R] R :=
    { toFun y := star (ocneanuTrace R q z (star y))
      map_add' _ _ := by simp
      map_smul' _ _ := by simp [star_smul] }
  have hφ : IsMarkovTrace (star z) φ :=
    { map_one := by simp [φ]
      map_mul_comm _ _ := by simp [φ, star_mul, (isMarkovTrace_ocneanuTrace z).map_mul_comm]
      map_mul_T {n a} ha := by
        simp only [φ, LinearMap.coe_mk, AddHom.coe_mk, star_mul, star_T]
        rw [(isMarkovTrace_ocneanuTrace (q := q) z).map_mul_comm (T q n) (star a),
          (isMarkovTrace_ocneanuTrace z).map_mul_T (star_mem_stage_iff.mpr ha),
          star_mul, mul_comm] }
  simpa [φ] using LinearMap.congr_fun hφ.eq_ocneanuTrace (star x)

/-- For a self-adjoint Markov parameter `z`, `ocneanuTrace R q z` commutes with `star`. -/
@[simp]
theorem ocneanuTrace_star {R : Type*} [CommRing R] [StarRing R] {q : Rˣ}
    [Fact (IsSelfAdjoint (q : R))] {z : R} (hz : IsSelfAdjoint z)
    (x : InfiniteTypeAHeckeAlgebra R q) :
    ocneanuTrace R q z (star x) = star (ocneanuTrace R q z x) := by
  rw [star_ocneanuTrace, hz.star_eq]

/-- **Positivity of the `z = 0` Ocneanu trace** over any commutative `StarOrderedRing`. -/
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

/-- Over `ℝ` or `ℂ` (`RCLike 𝕜`), the `z = 0` Ocneanu trace form is anisotropic. -/
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

/-- **Faithfulness of the `z = 0` Ocneanu trace** over `ℝ` or `ℂ`. -/
theorem traceRadical_ocneanuTrace_zero {𝕜 : Type*} [RCLike 𝕜] {q : 𝕜ˣ}
    [Fact (IsSelfAdjoint (q : 𝕜))] :
    (ocneanuTrace 𝕜 q 0).traceRadical (isMarkovTrace_ocneanuTrace 0).map_mul_comm = ⊥ := by
  refine eq_bot_iff.mpr fun x hx ↦ (ocneanuTrace_zero_star_mul_self_eq_zero_iff x).mp ?_
  rw [LinearMap.mem_traceRadical] at hx
  rw [(isMarkovTrace_ocneanuTrace 0).map_mul_comm]
  exact hx (star x)

end InfiniteTypeAHeckeAlgebra

end CanonicalOcneanu

namespace TypeAHeckeAlgebra

section CountableGeometricModels

private def natSumDualEquiv : (ℕ ⊕ ℕ) ≃ (ℕ ⊕ₗ ℕᵒᵈ) :=
  (Equiv.sumCongr (Equiv.refl ℕ) toDual).trans toLex

private theorem summable_natSumDual {α : Type*} [AddCommMonoid α] [TopologicalSpace α]
    [ContinuousAdd α] {f : (ℕ ⊕ₗ ℕᵒᵈ) → α}
    (h₁ : Summable fun k : ℕ ↦ f (Sum.inlₗ k))
    (h₂ : Summable fun k : ℕ ↦ f (Sum.inrₗ (toDual k))) : Summable f :=
  natSumDualEquiv.summable_iff.mp (Summable.sum (f ∘ natSumDualEquiv) h₁ h₂)

private theorem tsum_natSumDual {α : Type*} [AddCommMonoid α] [TopologicalSpace α]
    [ContinuousAdd α] [T2Space α] {f : (ℕ ⊕ₗ ℕᵒᵈ) → α}
    (h₁ : Summable fun k : ℕ ↦ f (Sum.inlₗ k))
    (h₂ : Summable fun k : ℕ ↦ f (Sum.inrₗ (toDual k))) :
    (∑' a : ℕ ⊕ₗ ℕᵒᵈ, f a) =
      (∑' k : ℕ, f (Sum.inlₗ k)) + ∑' k : ℕ, f (Sum.inrₗ (toDual k)) := by
  rw [← natSumDualEquiv.tsum_eq]
  exact Summable.tsum_sum (f := f ∘ natSumDualEquiv) h₁ h₂

private theorem natSumDual_cases (b : ℕ ⊕ₗ ℕᵒᵈ) :
    (∃ m, b = Sum.inlₗ m) ∨ (∃ m, b = Sum.inrₗ (toDual m)) := by
  cases hb : ofLex b with
  | inl m => exact Or.inl ⟨m, (toLex_ofLex b).symm.trans (congrArg toLex hb)⟩
  | inr m => exact Or.inr ⟨ofDual m, (toLex_ofLex b).symm.trans (congrArg toLex hb)⟩

private theorem tsum_ite_lt_eq_sum_range (f : ℕ → ℝ) (m : ℕ) :
    (Summable fun k : ℕ ↦ if k < m then f k else 0) ∧
      (∑' k : ℕ, if k < m then f k else 0) = ∑ k ∈ Finset.range m, f k :=
  ⟨summable_of_ne_finset_zero (s := Finset.range m) fun _ hk ↦
      ite_eq_right (Finset.mem_range.not.mp hk),
    (tsum_eq_sum (s := Finset.range m) fun _ hk ↦
      ite_eq_right (Finset.mem_range.not.mp hk)).trans <|
      Finset.sum_congr rfl fun _ hk ↦ ite_eq_left (Finset.mem_range.mp hk)⟩

private theorem tsum_gt_eq_sub_sum_range {f : ℕ → ℝ} (hf : Summable f) (m : ℕ) :
    (Summable fun k : ℕ ↦ if m < k then f k else 0) ∧
      (∑' k : ℕ, if m < k then f k else 0) =
        (∑' k : ℕ, f k) - ∑ k ∈ Finset.range (m + 1), f k := by
  have hgt : Summable fun k : ℕ ↦ if m < k then f k else 0 :=
    hf.norm.of_norm_bounded fun k ↦ by split_ifs <;> simp
  have hle := tsum_ite_lt_eq_sum_range f (m + 1)
  refine ⟨hgt, eq_sub_of_add_eq' ?_⟩
  rw [← hle.2, ← hle.1.tsum_add hgt]
  congr 1 with k; by_cases hk : k < m + 1 <;> simp [hk, show (m < k ↔ ¬k < m + 1) by omega]

private theorem tsum_lt_inl_natSumDual (f : (ℕ ⊕ₗ ℕᵒᵈ) → ℝ) (m : ℕ) :
    (∑' a : ℕ ⊕ₗ ℕᵒᵈ, if a < Sum.inlₗ m then f a else 0) =
      ∑ k ∈ Finset.range m, f (Sum.inlₗ k) := by
  have h1 := tsum_ite_lt_eq_sum_range (fun k ↦ f (Sum.inlₗ k)) m
  rw [tsum_natSumDual (f := fun a : ℕ ⊕ₗ ℕᵒᵈ ↦ if a < Sum.inlₗ m then f a else 0)
    (by simpa only [Sum.Lex.inl_lt_inl_iff] using h1.1)
    (by simpa only [Sum.Lex.not_inr_lt_inl, ↓reduceIte] using summable_zero)]
  simpa only [Sum.Lex.inl_lt_inl_iff, Sum.Lex.not_inr_lt_inl, ↓reduceIte, tsum_zero, add_zero]
    using h1.2

private theorem tsum_lt_inr_natSumDual {f : (ℕ ⊕ₗ ℕᵒᵈ) → ℝ}
    (h₁ : Summable fun k : ℕ ↦ f (Sum.inlₗ k))
    (h₂ : Summable fun k : ℕ ↦ f (Sum.inrₗ (toDual k))) (m : ℕ) :
    (∑' a : ℕ ⊕ₗ ℕᵒᵈ, if a < Sum.inrₗ (toDual m) then f a else 0) =
      (∑' k : ℕ, f (Sum.inlₗ k)) + (∑' k : ℕ, f (Sum.inrₗ (toDual k))) -
        ∑ k ∈ Finset.range (m + 1), f (Sum.inrₗ (toDual k)) := by
  have hgt := tsum_gt_eq_sub_sum_range h₂ m
  rw [tsum_natSumDual (f := fun a : ℕ ⊕ₗ ℕᵒᵈ ↦ if a < Sum.inrₗ (toDual m) then f a else 0)
    (by simpa only [Sum.Lex.inl_lt_inr, ↓reduceIte] using h₁)
    (by simpa only [Sum.Lex.inr_lt_inr_iff, toDual_lt_toDual] using hgt.1)]
  simp only [Sum.Lex.inl_lt_inr, Sum.Lex.inr_lt_inr_iff, toDual_lt_toDual, ↓reduceIte, hgt.2]
  ring

private noncomputable def twoSidedGeom (a₁ a₂ r : ℝ) (a : ℕ ⊕ₗ ℕᵒᵈ) : ℝ :=
  match ofLex a with
  | Sum.inl k => a₁ * r ^ k
  | Sum.inr k => a₂ * r ^ ofDual k

private theorem twoSidedGeom_nonneg {a₁ a₂ r : ℝ} (h₁ : 0 ≤ a₁) (h₂ : 0 ≤ a₂) (hr : 0 ≤ r)
    (a : ℕ ⊕ₗ ℕᵒᵈ) : 0 ≤ twoSidedGeom a₁ a₂ r a := by
  cases ha : ofLex a <;> simp only [twoSidedGeom, ha] <;> positivity

private theorem summable_norm_twoSidedGeom (a₁ a₂ : ℝ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Summable fun a ↦ ‖twoSidedGeom a₁ a₂ r a‖ := by
  have hgeom := summable_geometric_of_lt_one hr0 hr1
  refine summable_natSumDual
    ((hgeom.mul_left ‖a₁‖).congr fun k ↦ by
      simp [twoSidedGeom, norm_mul, norm_pow, Real.norm_of_nonneg hr0])
    ((hgeom.mul_left ‖a₂‖).congr fun k ↦ by
      simp [twoSidedGeom, norm_mul, norm_pow, Real.norm_of_nonneg hr0])

private theorem tsum_twoSidedGeom (a₁ a₂ : ℝ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    (∑' a, twoSidedGeom a₁ a₂ r a) = (a₁ + a₂) / (1 - r) := by
  have hgeom := summable_geometric_of_lt_one hr0 hr1
  rw [tsum_natSumDual (hgeom.mul_left a₁) (hgeom.mul_left a₂)]
  simp only [twoSidedGeom, ofLex_toLex, ofDual_toDual, hgeom.tsum_mul_left,
    tsum_geometric_of_lt_one hr0 hr1]
  ring

private theorem mul_tsum_lt_twoSidedGeom_inl (a₁ a₂ r : ℝ) (m : ℕ) :
    (1 - r) * (∑' a : ℕ ⊕ₗ ℕᵒᵈ, if a < Sum.inlₗ m then twoSidedGeom a₁ a₂ r a else 0) =
      a₁ * (1 - r ^ m) := by
  rw [tsum_lt_inl_natSumDual]
  simp only [twoSidedGeom, ofLex_toLex, ← Finset.mul_sum]
  rw [mul_left_comm, mul_neg_geom_sum]

private theorem mul_tsum_lt_twoSidedGeom_inr (a₁ a₂ : ℝ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (m : ℕ) :
    (1 - r) * (∑' a : ℕ ⊕ₗ ℕᵒᵈ, if a < Sum.inrₗ (toDual m) then twoSidedGeom a₁ a₂ r a else 0) =
      a₁ + a₂ * r ^ (m + 1) := by
  have hgeom := summable_geometric_of_lt_one hr0 hr1
  rw [tsum_lt_inr_natSumDual (hgeom.mul_left a₁) (hgeom.mul_left a₂)]
  simp only [twoSidedGeom, ofLex_toLex, ofDual_toDual, hgeom.tsum_mul_left,
    tsum_geometric_of_lt_one hr0 hr1, ← Finset.mul_sum]
  rw [mul_sub, mul_left_comm (1 - r) a₂, mul_neg_geom_sum]
  have h1r : 1 - r ≠ 0 := sub_ne_zero.mpr hr1.ne'
  field_simp; ring

private theorem countableAtomicTrace_ofReal_eq_ocneanuTrace_of_leftSlice {ι : Type*}
    [LinearOrder ι] (pos : ι → Prop) [DecidablePred pos] {q : ℂˣ} {Q : ℝ}
    (hqQ : (q : ℂ) ^ 2 = Q) {w : ι → ℝ} (hw : Summable fun a ↦ ‖w a‖) (η : ℝ)
    (hsum : (∑' a, w a) = 1)
    (hslice : ∀ b, (if pos b then Q else -1) * w b +
      (Q - 1) * (∑' a, if a < b then w a else 0) = (1 + Q) * η - 1)
    {n : ℕ} (x : TypeAHeckeAlgebra ℂ q n) :
    countableAtomicTrace pos q (fun a ↦ (w a : ℂ))
        (hw.congr fun a ↦ (Complex.norm_real _).symm) n x =
      InfiniteTypeAHeckeAlgebra.ocneanuTrace ℂ q
        ((q : ℂ) * η - (↑q⁻¹ : ℂ) * (1 - η)) (toInfinite ℂ q n x) := by
  refine countableAtomicTrace_eq_ocneanuTrace_of_leftSlice pos q _ _
    (by rw [← Complex.ofReal_tsum, hsum, Complex.ofReal_one]) (fun b ↦ ?_) x
  have hsl := congrArg ((↑) : ℝ → ℂ) (hslice b)
  push_cast [Complex.ofReal_tsum, apply_ite ((↑) : ℝ → ℂ)] at hsl
  rw [← hqQ] at hsl
  have _ : (q : ℂ) ≠ 0 := q.ne_zero
  rw [hsl, Units.val_inv_eq_inv_val]
  field_simp; ring

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
  have hs : 0 ≤ (1 + Q) * η - 1 := by linarith [(div_le_iff₀ h1Q).mp hη.1]
  have hc : 0 ≤ Q - (1 + Q) * η := by linarith [(le_div_iff₀ h1Q).mp hη.2]
  exact twoSidedGeom_nonneg (mul_nonneg hs hr0) (mul_nonneg hc hr0) hr0 a

/-- For `1 < Q` and any `η : ℝ`, `wenzlGtOneWeight Q η` is absolutely summable. -/
theorem summable_norm_wenzlGtOneWeight {Q : ℝ} (hQ : 1 < Q) (η : ℝ) :
    Summable fun a ↦ ‖wenzlGtOneWeight Q η a‖ :=
  summable_norm_twoSidedGeom _ _ (inv_nonneg.mpr (zero_lt_one.trans hQ).le)
    (inv_lt_one_of_one_lt₀ hQ)

/-- For `1 < Q` and any `η : ℝ`, the total weight of `wenzlGtOneWeight Q η` is `1`. -/
theorem tsum_wenzlGtOneWeight {Q : ℝ} (hQ : 1 < Q) (η : ℝ) :
    (∑' a, wenzlGtOneWeight Q η a) = 1 := by
  have hQ0 : Q ≠ 0 := (zero_lt_one.trans hQ).ne'
  have hQ1 : Q - 1 ≠ 0 := sub_ne_zero.mpr hQ.ne'
  change (∑' a, twoSidedGeom (((1 + Q) * η - 1) * Q⁻¹) ((Q - (1 + Q) * η) * Q⁻¹) Q⁻¹ a) = 1
  rw [tsum_twoSidedGeom _ _ (inv_nonneg.mpr (zero_lt_one.trans hQ).le) (inv_lt_one_of_one_lt₀ hQ)]
  field_simp; ring

/-- Every left slice of `wenzlGtOneWeight Q η` equals `(1 + Q) * η - 1`. -/
theorem wenzlGtOneWeight_leftSlice {Q : ℝ} (hQ : 1 < Q) (η : ℝ) (b : ℕ ⊕ₗ ℕᵒᵈ) :
    (if wenzlGtOnePos b then Q else -1) * wenzlGtOneWeight Q η b +
      (Q - 1) * (∑' a, if a < b then wenzlGtOneWeight Q η a else 0) = (1 + Q) * η - 1 := by
  have hQ0 : Q ≠ 0 := (zero_lt_one.trans hQ).ne'
  have hQsub : Q - 1 = Q * (1 - Q⁻¹) := by field_simp
  rcases natSumDual_cases b with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · have h := mul_tsum_lt_twoSidedGeom_inl (((1 + Q) * η - 1) * Q⁻¹) ((Q - (1 + Q) * η) * Q⁻¹)
      Q⁻¹ m
    change (1 - Q⁻¹) * (∑' a, if a < Sum.inlₗ m then wenzlGtOneWeight Q η a else 0) = _ at h
    rw [hQsub, mul_assoc, h]
    simp only [wenzlGtOnePos, wenzlGtOneWeight, ofLex_toLex, Sum.isLeft_inl, ↓reduceIte]
    field_simp; ring
  · have h := mul_tsum_lt_twoSidedGeom_inr (((1 + Q) * η - 1) * Q⁻¹) ((Q - (1 + Q) * η) * Q⁻¹)
      (inv_nonneg.mpr (zero_lt_one.trans hQ).le) (inv_lt_one_of_one_lt₀ hQ) m
    change (1 - Q⁻¹) *
      (∑' a, if a < Sum.inrₗ (toDual m) then wenzlGtOneWeight Q η a else 0) = _ at h
    rw [hQsub, mul_assoc, h, pow_succ']
    simp only [wenzlGtOnePos, wenzlGtOneWeight, ofLex_toLex, ofDual_toDual, Sum.isLeft_inr,
      Bool.false_eq_true, ↓reduceIte]
    field_simp; ring

/-- **Countable geometric realization of the Ocneanu trace for `1 < Q`.** -/
theorem countableAtomicTrace_wenzlGtOneWeight_eq_ocneanuTrace {q : ℂˣ} {Q : ℝ} (hQ : 1 < Q)
    (hqQ : (q : ℂ) ^ 2 = Q) (η : ℝ) {n : ℕ} (x : TypeAHeckeAlgebra ℂ q n) :
    countableAtomicTrace wenzlGtOnePos q (fun a ↦ (wenzlGtOneWeight Q η a : ℂ))
        ((summable_norm_wenzlGtOneWeight hQ η).congr fun _ ↦ (Complex.norm_real _).symm) n x =
      InfiniteTypeAHeckeAlgebra.ocneanuTrace ℂ q
        ((q : ℂ) * η - (↑q⁻¹ : ℂ) * (1 - η)) (toInfinite ℂ q n x) :=
  countableAtomicTrace_ofReal_eq_ocneanuTrace_of_leftSlice wenzlGtOnePos hqQ
    (summable_norm_wenzlGtOneWeight hQ η) η (tsum_wenzlGtOneWeight hQ η)
    (wenzlGtOneWeight_leftSlice hQ η) x

/-- **Telescoping infinite product for Wenzl's `1 < Q` countable model.** For `1 < Q`,
`η ∈ [1 / (1 + Q), Q / (1 + Q)]`, and `Q * ‖x‖ < 1`, the cycle-trace product converges to
`(1 + (Q - (1 + Q) * η) * x) / (1 - ((1 + Q) * η - 1) * x)`. -/
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
    (summable_norm_wenzlGtOneWeight hQ η).congr fun _ ↦ (Complex.norm_real _).symm
  have hnorm_sum : (∑' a, ‖(wenzlGtOneWeight Q η a : ℂ)‖) = 1 := by
    simpa only [Complex.norm_real, Real.norm_of_nonneg (wenzlGtOneWeight_nonneg hQ hη _)] using
      tsum_wenzlGtOneWeight hQ η
  have hmax : max 1 (max ‖(q : ℂ) ^ 2‖ ‖(q : ℂ) ^ 2 - 1‖) = Q := by
    rw [hqQ, ← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Complex.norm_real,
      Real.norm_of_nonneg (zero_lt_one.trans hQ).le, Real.norm_of_nonneg (sub_nonneg.mpr hQ.le),
      max_eq_left (a := Q) (b := Q - 1) (by linarith), max_eq_right hQ.le]
  have hprod := (countableAtomicTrace_cycleWord_hasProd wenzlGtOnePos q _ hp
    (by rwa [hmax, hnorm_sum, mul_one])).2
  set s : ℝ := (1 + Q) * η - 1
  have hs0 : 0 ≤ s := by linarith [(div_le_iff₀ (by linarith : 0 < 1 + Q)).mp hη.1]
  have hsx : ‖(s : ℂ) * x‖ < 1 := by
    have hsQ : s ≤ Q := by linarith [(le_div_iff₀ (by linarith : 0 < 1 + Q)).mp hη.2]
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hs0]
    exact (mul_le_mul_of_nonneg_right hsQ (norm_nonneg x)).trans_lt hx
  have htr (m : ℕ) : countableAtomicTrace wenzlGtOnePos q (fun a ↦ (wenzlGtOneWeight Q η a : ℂ))
      hp (m + 1) (cycleWord q (m + 1)) * x ^ (m + 1) = x * ((s : ℂ) * x) ^ m := by
    rw [countableAtomicTrace_wenzlGtOneWeight_eq_ocneanuTrace hQ hqQ η, toInfinite_cycleWord,
      (InfiniteTypeAHeckeAlgebra.isMarkovTrace_ocneanuTrace _).map_cycleWord, Nat.add_sub_cancel]
    have hqz : (q : ℂ) * ((q : ℂ) * η - (↑q⁻¹ : ℂ) * (1 - η)) = (s : ℂ) := by
      have _ : (q : ℂ) ≠ 0 := q.ne_zero
      dsimp only [s]; push_cast; rw [← hqQ]; field_simp; ring
    rw [hqz]; ring
  have hne : 1 - (s : ℂ) * x ≠ 0 := fun h0 ↦ by
    have : (1 : ℝ) = ‖(s : ℂ) * x‖ := by simpa [sub_eq_zero.mp h0] using (norm_one (α := ℂ)).symm
    linarith
  convert hprod using 1
  simp_rw [htr]
  rw [(summable_geometric_of_norm_lt_one hsx).tsum_mul_left,
    tsum_geometric_of_norm_lt_one hsx, hqQ, eq_comm, eq_div_iff hne]
  have hmul : (1 - (s : ℂ) * x)⁻¹ * (1 - (s : ℂ) * x) = 1 := inv_mul_cancel₀ hne
  dsimp only [s] at hmul ⊢; push_cast at hmul ⊢
  linear_combination ((Q : ℂ) - 1) * x * hmul

/-! ### The `0 < Q < 1` countable model on `ℕ ⊕ₗ ℕᵒᵈ` -/

/-- Sign predicate on `ℕ ⊕ₗ ℕᵒᵈ` for `0 < Q < 1`: negative on `ℕ`, positive on `ℕᵒᵈ`. -/
def wenzlLtOnePos (a : ℕ ⊕ₗ ℕᵒᵈ) : Prop :=
  (ofLex a).isRight = true

instance : DecidablePred wenzlLtOnePos :=
  fun a ↦ inferInstanceAs (Decidable ((ofLex a).isRight = true))

/-- Real geometric weights on `ℕ ⊕ₗ ℕᵒᵈ` for `0 < Q < 1` and projection parameter `η`. -/
noncomputable def wenzlLtOneWeight (Q η : ℝ) (a : ℕ ⊕ₗ ℕᵒᵈ) : ℝ :=
  match ofLex a with
  | Sum.inl k => (1 - (1 + Q) * η) * Q ^ k
  | Sum.inr k => ((1 + Q) * η - Q) * Q ^ ofDual k

/-- For `0 < Q < 1` and `η ∈ [Q / (1 + Q), 1 / (1 + Q)]`, `wenzlLtOneWeight Q η` is nonnegative. -/
theorem wenzlLtOneWeight_nonneg {Q : ℝ} (hQ0 : 0 < Q) {η : ℝ}
    (hη : η ∈ Set.Icc (Q / (1 + Q)) (1 / (1 + Q))) (a : ℕ ⊕ₗ ℕᵒᵈ) :
    0 ≤ wenzlLtOneWeight Q η a := by
  have h1Q : 0 < 1 + Q := by linarith
  exact twoSidedGeom_nonneg (by linarith [(le_div_iff₀ h1Q).mp hη.2])
    (by linarith [(div_le_iff₀ h1Q).mp hη.1]) hQ0.le a

/-- For `0 < Q < 1` and any `η : ℝ`, `wenzlLtOneWeight Q η` is absolutely summable. -/
theorem summable_norm_wenzlLtOneWeight {Q : ℝ} (hQ0 : 0 < Q) (hQ1 : Q < 1) (η : ℝ) :
    Summable fun a ↦ ‖wenzlLtOneWeight Q η a‖ :=
  summable_norm_twoSidedGeom _ _ hQ0.le hQ1

/-- For `0 < Q < 1` and any `η : ℝ`, the total weight of `wenzlLtOneWeight Q η` is `1`. -/
theorem tsum_wenzlLtOneWeight {Q : ℝ} (hQ0 : 0 < Q) (hQ1 : Q < 1) (η : ℝ) :
    (∑' a, wenzlLtOneWeight Q η a) = 1 := by
  have h1Q : 1 - Q ≠ 0 := sub_ne_zero.mpr hQ1.ne'
  change (∑' a, twoSidedGeom (1 - (1 + Q) * η) ((1 + Q) * η - Q) Q a) = 1
  rw [tsum_twoSidedGeom _ _ hQ0.le hQ1]; field_simp; ring

/-- Every left slice of `wenzlLtOneWeight Q η` equals `(1 + Q) * η - 1`. -/
theorem wenzlLtOneWeight_leftSlice {Q : ℝ} (hQ0 : 0 < Q) (hQ1 : Q < 1) (η : ℝ)
    (b : ℕ ⊕ₗ ℕᵒᵈ) :
    (if wenzlLtOnePos b then Q else -1) * wenzlLtOneWeight Q η b +
      (Q - 1) * (∑' a, if a < b then wenzlLtOneWeight Q η a else 0) = (1 + Q) * η - 1 := by
  rcases natSumDual_cases b with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · have h := mul_tsum_lt_twoSidedGeom_inl (1 - (1 + Q) * η) ((1 + Q) * η - Q) Q m
    change (1 - Q) * (∑' a, if a < Sum.inlₗ m then wenzlLtOneWeight Q η a else 0) = _ at h
    rw [show Q - 1 = -(1 - Q) by ring, neg_mul, h]
    simp only [wenzlLtOnePos, wenzlLtOneWeight, ofLex_toLex, Sum.isRight_inl, Bool.false_eq_true,
      ↓reduceIte]
    ring
  · have h := mul_tsum_lt_twoSidedGeom_inr (1 - (1 + Q) * η) ((1 + Q) * η - Q) hQ0.le hQ1 m
    change (1 - Q) *
      (∑' a, if a < Sum.inrₗ (toDual m) then wenzlLtOneWeight Q η a else 0) = _ at h
    rw [show Q - 1 = -(1 - Q) by ring, neg_mul, h, pow_succ']
    simp only [wenzlLtOnePos, wenzlLtOneWeight, ofLex_toLex, ofDual_toDual, Sum.isRight_inr,
      ↓reduceIte]
    ring

/-- **Countable geometric realization of the Ocneanu trace for `0 < Q < 1`.** -/
theorem countableAtomicTrace_wenzlLtOneWeight_eq_ocneanuTrace {q : ℂˣ} {Q : ℝ} (hQ0 : 0 < Q)
    (hQ1 : Q < 1) (hqQ : (q : ℂ) ^ 2 = Q) (η : ℝ) {n : ℕ} (x : TypeAHeckeAlgebra ℂ q n) :
    countableAtomicTrace wenzlLtOnePos q (fun a ↦ (wenzlLtOneWeight Q η a : ℂ))
        ((summable_norm_wenzlLtOneWeight hQ0 hQ1 η).congr fun _ ↦ (Complex.norm_real _).symm) n x =
      InfiniteTypeAHeckeAlgebra.ocneanuTrace ℂ q
        ((q : ℂ) * η - (↑q⁻¹ : ℂ) * (1 - η)) (toInfinite ℂ q n x) :=
  countableAtomicTrace_ofReal_eq_ocneanuTrace_of_leftSlice wenzlLtOnePos hqQ
    (summable_norm_wenzlLtOneWeight hQ0 hQ1 η) η (tsum_wenzlLtOneWeight hQ0 hQ1 η)
    (wenzlLtOneWeight_leftSlice hQ0 hQ1 η) x

end CountableGeometricModels

end TypeAHeckeAlgebra

/-! ### Wenzl's positive-real parameter set and positivity of `ocneanuTrace` -/

/-- **Wenzl's positive-real projection parameter set** for `Q > 0`: the closed interval between
`1 / (1 + Q)` and `Q / (1 + Q)` union `{wenzlParam d Q | d ≠ 0}`. -/
noncomputable def wenzlPositiveSet (Q : ℝ) : Set ℝ :=
  Set.Icc (min (1 / (1 + Q)) (Q / (1 + Q))) (max (1 / (1 + Q)) (Q / (1 + Q))) ∪
    {η | ∃ d : ℤ, d ≠ 0 ∧ η = wenzlParam d Q}

/-- Every nonzero integer parameter `wenzlParam d Q` lies in `wenzlPositiveSet Q`. -/
theorem wenzlParam_mem_wenzlPositiveSet {d : ℤ} (hd : d ≠ 0) (Q : ℝ) :
    wenzlParam d Q ∈ wenzlPositiveSet Q :=
  Or.inr ⟨d, hd, rfl⟩

/-- When `1 ≤ Q`, `[1 / (1 + Q), Q / (1 + Q)] ⊆ wenzlPositiveSet Q`. -/
theorem mem_wenzlPositiveSet_of_mem_Icc_of_one_le {Q : ℝ} (hQ : 1 ≤ Q) {η : ℝ}
    (hη : η ∈ Set.Icc (1 / (1 + Q)) (Q / (1 + Q))) : η ∈ wenzlPositiveSet Q := by
  have hle : 1 / (1 + Q) ≤ Q / (1 + Q) := div_le_div_of_nonneg_right hQ (by linarith)
  exact Or.inl ⟨(min_eq_left hle).symm ▸ hη.1, (max_eq_right hle).symm ▸ hη.2⟩

/-- When `0 ≤ Q ≤ 1`, `[Q / (1 + Q), 1 / (1 + Q)] ⊆ wenzlPositiveSet Q`. -/
theorem mem_wenzlPositiveSet_of_mem_Icc_of_le_one {Q : ℝ} (hQ0 : 0 ≤ Q) (hQ1 : Q ≤ 1) {η : ℝ}
    (hη : η ∈ Set.Icc (Q / (1 + Q)) (1 / (1 + Q))) : η ∈ wenzlPositiveSet Q := by
  have hle : Q / (1 + Q) ≤ 1 / (1 + Q) := div_le_div_of_nonneg_right hQ1 (by linarith)
  exact Or.inl ⟨(min_eq_right hle).symm ▸ hη.1, (max_eq_left hle).symm ▸ hη.2⟩

/-- Inversion symmetry `wenzlPositiveSet Q⁻¹ = wenzlPositiveSet Q` for `0 < Q`. -/
theorem wenzlPositiveSet_inv {Q : ℝ} (hQ : 0 < Q) : wenzlPositiveSet Q⁻¹ = wenzlPositiveSet Q := by
  have h1 : 1 / (1 + Q⁻¹) = Q / (1 + Q) := by field_simp; ring
  have h2 : Q⁻¹ / (1 + Q⁻¹) = 1 / (1 + Q) := by field_simp; ring
  ext η
  simp only [wenzlPositiveSet, Set.mem_union, Set.mem_Icc, Set.mem_ofPred_eq, h1, h2,
    min_comm (Q / (1 + Q)), max_comm (Q / (1 + Q)), wenzlParam_inv]

/-- Complement symmetry `1 - η ∈ wenzlPositiveSet Q ↔ η ∈ wenzlPositiveSet Q` for `0 < Q`. -/
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
    · rw [min_eq_left hle, max_eq_right hle] at hx ⊢; exact ⟨by linarith [hx.2], by linarith [hx.1]⟩
    · rw [min_eq_right hle, max_eq_left hle] at hx ⊢; exact ⟨by linarith [hx.2], by linarith [hx.1]⟩
  · refine Or.inr ⟨-d, neg_ne_zero.mpr hd, ?_⟩
    have hZ : 0 < ∑ i ∈ Finset.range d.natAbs, Q ^ i :=
      Finset.sum_pos (fun i _ ↦ pow_pos hQ i)
        (Finset.nonempty_range_iff.mpr (Int.natAbs_ne_zero.mpr hd))
    linarith [wenzlParam_add_wenzlParam_neg (mul_ne_zero (by linarith : 1 + Q ≠ 0) hZ.ne')]

namespace InfiniteTypeAHeckeAlgebra

private theorem pos_of_ofReal_eq_sq {q : ℂˣ} [Fact (IsSelfAdjoint (q : ℂ))] {Q : ℝ}
    (hQ : (Q : ℂ) = (q : ℂ) ^ 2) : 0 < Q := by
  have him : (q : ℂ).im = 0 :=
    Complex.conj_eq_iff_im.mp (Fact.out : IsSelfAdjoint (q : ℂ)).star_eq
  have hre : (q : ℂ) = ((q : ℂ).re : ℂ) := Complex.ext rfl (by simp [him])
  rw [Complex.ofReal_injective
    (hQ.trans ((congrArg (· ^ 2) hre).trans (Complex.ofReal_pow _ 2).symm))]
  exact sq_pos_of_ne_zero fun h0 ↦ q.ne_zero (by rw [hre, h0, Complex.ofReal_zero])

private theorem ofReal_wenzlParam (d : ℤ) (Q : ℝ) :
    ((wenzlParam d Q : ℝ) : ℂ) = wenzlParam d (Q : ℂ) := by
  obtain ⟨r, rfl | rfl⟩ := Int.eq_nat_or_neg d <;> simp [wenzlParam_natCast, wenzlParam_neg_natCast]

private theorem ocneanuTrace_wenzlParam_nonneg {q : ℂˣ} [Fact (IsSelfAdjoint (q : ℂ))]
    {Q : ℝ} (hQ0 : 0 < Q) (hQ : (Q : ℂ) = (q : ℂ) ^ 2) (b : Bool) (r : ℕ) {n : ℕ}
    (y : TypeAHeckeAlgebra ℂ q n) :
    let d : ℤ := if b then ((r + 1 : ℕ) : ℤ) else -((r + 1 : ℕ) : ℤ)
    0 ≤ ocneanuTrace ℂ q ((q : ℂ) * ((wenzlParam d Q : ℝ) : ℂ) -
        (↑q⁻¹ : ℂ) * (1 - ((wenzlParam d Q : ℝ) : ℂ)))
      (TypeAHeckeAlgebra.toInfinite ℂ q n (star y * y)) := by
  set Z : ℝ := ∑ a ∈ Finset.range (r + 1), Q ^ a
  have hZ0 : 0 < Z :=
    Finset.sum_pos (fun a _ ↦ pow_pos hQ0 a) (Finset.nonempty_range_iff.mpr (Nat.succ_ne_zero r))
  set c : ℝ := Z⁻¹
  have hcZ : (c : ℂ) * ∑ a ∈ Finset.range (r + 1), ((q : ℂ) ^ 2) ^ a = 1 := by
    have hr : c * Z = 1 := inv_mul_cancel₀ hZ0.ne'
    have hcast := congrArg ((↑) : ℝ → ℂ) hr
    push_cast [Z, hQ] at hcast; exact hcast
  have h1Q : 1 + (q : ℂ) ^ 2 ≠ 0 := by
    rw [← hQ, ← Complex.ofReal_one, ← Complex.ofReal_add]
    exact Complex.ofReal_ne_zero.mpr (by linarith)
  have hZc : ∑ a ∈ Finset.range (r + 1), ((q : ℂ) ^ 2) ^ a ≠ 0 := right_ne_zero_of_mul_eq_one hcZ
  have hq0 : (q : ℂ) ≠ 0 := q.ne_zero
  have hw (a : Fin (r + 1)) : (0 : ℂ) ≤ (c : ℂ) * ((q : ℂ) ^ 2) ^ (a : ℕ) := by
    simpa [hQ] using Complex.zero_le_real.mpr (show 0 ≤ c * Q ^ (a : ℕ) by positivity)
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte]
    have hg : ∑ a ∈ Finset.range (r + 1), ((q : ℂ) ^ 2) ^ a =
        (q : ℂ) ^ 2 * ∑ a ∈ Finset.range r, ((q : ℂ) ^ 2) ^ a + 1 := by
      simp [Finset.sum_range_succ', pow_succ', ← Finset.mul_sum]
    have hz : (q : ℂ) * ((wenzlParam (-((r + 1 : ℕ) : ℤ)) Q : ℝ) : ℂ) -
        (↑q⁻¹ : ℂ) * (1 - ((wenzlParam (-((r + 1 : ℕ) : ℤ)) Q : ℝ) : ℂ)) = -((c : ℂ) * ↑q⁻¹) := by
      rw [ofReal_wenzlParam, hQ, wenzlParam_neg_natCast, Nat.add_sub_cancel,
        Units.val_inv_eq_inv_val]
      field_simp; linear_combination -((1 + (q : ℂ) ^ 2) * hg) + (1 + (q : ℂ) ^ 2) * hcZ
    rw [hz, ← TypeAHeckeAlgebra.atomicTrace_negGeometric_eq q hcZ (star y * y)]
    exact TypeAHeckeAlgebra.atomicTrace_star_mul_self_nonneg _ q hw y
  · simp only [↓reduceIte]
    have hz : (q : ℂ) * ((wenzlParam ((r + 1 : ℕ) : ℤ) Q : ℝ) : ℂ) -
        (↑q⁻¹ : ℂ) * (1 - ((wenzlParam ((r + 1 : ℕ) : ℤ) Q : ℝ) : ℂ)) =
        (c : ℂ) * (q : ℂ) ^ (2 * r + 1) := by
      rw [ofReal_wenzlParam, hQ, wenzlParam_natCast, Units.val_inv_eq_inv_val,
        geom_sum_succ' (n := r + 1)]
      field_simp; linear_combination -((1 + (q : ℂ) ^ 2) * (q : ℂ) ^ (2 * r + 2)) * hcZ
    rw [hz, ← TypeAHeckeAlgebra.atomicTrace_geometric_eq q hcZ (star y * y)]
    exact TypeAHeckeAlgebra.atomicTrace_star_mul_self_nonneg _ q hw y

/-- **Positivity of the Ocneanu trace across Wenzl's positive-real parameter set.** For real nonzero
`q : ℂˣ` with `(Q : ℂ) = (q : ℂ) ^ 2` and `η ∈ wenzlPositiveSet Q`, the Ocneanu trace at
`z = q * η - q⁻¹ * (1 - η)` is nonnegative on every `star x * x`. -/
theorem ocneanuTrace_star_mul_self_nonneg {q : ℂˣ} [Fact (IsSelfAdjoint (q : ℂ))] {Q : ℝ}
    (hQ : (Q : ℂ) = (q : ℂ) ^ 2) {η : ℝ} (hη : η ∈ wenzlPositiveSet Q)
    (x : InfiniteTypeAHeckeAlgebra ℂ q) :
    0 ≤ ocneanuTrace ℂ q ((q : ℂ) * η - (↑q⁻¹ : ℂ) * (1 - η)) (star x * x) := by
  have hQ0 : 0 < Q := pos_of_ofReal_eq_sq hQ
  obtain ⟨n, hx⟩ := exists_mem_stage x
  rw [← TypeAHeckeAlgebra.range_toInfinite, AlgHom.mem_range] at hx
  obtain ⟨y, rfl⟩ := hx
  rw [← TypeAHeckeAlgebra.toInfinite_star, ← map_mul]
  rcases hη with hIcc | ⟨d, hd, rfl⟩
  · rcases lt_trichotomy Q 1 with hQ1 | rfl | hQ1
    · have hle : Q / (1 + Q) ≤ 1 / (1 + Q) := div_le_div_of_nonneg_right hQ1.le (by linarith)
      rw [min_eq_right hle, max_eq_left hle] at hIcc
      rw [← TypeAHeckeAlgebra.countableAtomicTrace_wenzlLtOneWeight_eq_ocneanuTrace hQ0 hQ1 hQ.symm]
      exact TypeAHeckeAlgebra.countableAtomicTrace_star_mul_self_nonneg _ q _
        (fun a ↦ Complex.zero_le_real.mpr (TypeAHeckeAlgebra.wenzlLtOneWeight_nonneg hQ0 hIcc a)) y
    · rw [show (1 : ℝ) / (1 + 1) = 1 / 2 by norm_num, min_self, max_self,
        Set.Icc_self, Set.mem_singleton_iff] at hIcc
      subst hIcc
      have hz0 : (q : ℂ) * ((1 / 2 : ℝ) : ℂ) - (↑q⁻¹ : ℂ) * (1 - ((1 / 2 : ℝ) : ℂ)) = 0 := by
        have _ : (q : ℂ) ≠ 0 := q.ne_zero
        have hq2 : (q : ℂ) ^ 2 = 1 := by simpa using hQ.symm
        rw [Units.val_inv_eq_inv_val]; push_cast; field_simp; linear_combination hq2
      rw [hz0, map_mul, TypeAHeckeAlgebra.toInfinite_star]
      exact ocneanuTrace_zero_star_mul_self_nonneg _
    · have hle : 1 / (1 + Q) ≤ Q / (1 + Q) := div_le_div_of_nonneg_right hQ1.le (by linarith)
      rw [min_eq_left hle, max_eq_right hle] at hIcc
      rw [← TypeAHeckeAlgebra.countableAtomicTrace_wenzlGtOneWeight_eq_ocneanuTrace hQ1 hQ.symm]
      exact TypeAHeckeAlgebra.countableAtomicTrace_star_mul_self_nonneg _ q _
        (fun a ↦ Complex.zero_le_real.mpr (TypeAHeckeAlgebra.wenzlGtOneWeight_nonneg hQ1 hIcc a)) y
  · obtain ⟨_ | r, rfl | rfl⟩ := Int.eq_nat_or_neg d
    · exact absurd rfl hd
    · simp at hd
    · exact ocneanuTrace_wenzlParam_nonneg hQ0 hQ true r y
    · exact ocneanuTrace_wenzlParam_nonneg hQ0 hQ false r y

/-- The complex Ocneanu trace on `InfiniteTypeAHeckeAlgebra ℂ q` bundled as a
`StarPositiveFunctional` for real nonzero `q : ℂˣ` and `η ∈ wenzlPositiveSet Q`. -/
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
