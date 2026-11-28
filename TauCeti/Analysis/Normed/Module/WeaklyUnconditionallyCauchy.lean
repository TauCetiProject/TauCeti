/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.InfiniteSum
public import Mathlib.Analysis.RCLike.Basic
public import TauCeti.Topology.ContinuousMap.ZeroAtInfty.Discrete
import TauCeti.Analysis.Normed.Module.Bases.WeaklyNull
import TauCeti.Analysis.Normed.Module.BoundedCoefficients

/-!
# Series with bounded partial sums and copies of `c₀`

A series `∑ xₙ` in a real or complex normed space is *weakly unconditionally Cauchy* when its
finite subsums `∑ n ∈ s, x n` are uniformly bounded; equivalently, its finite signed sums
`∑ n ∈ s, ± x n` are, since each signed sum is a difference of two subsums. Every unconditionally
convergent series has this property, and the unit vectors of `c₀` show that the converse fails.
This file proves that `c₀` is the only obstruction (Bessaga–Pełczyński):

* `TauCeti.summable_of_forall_not_antilipschitzWith`: if a Banach space `X` contains no copy of
  `c₀`, that is no bounded-below continuous linear map `C₀(ℕ, 𝕜) →L[𝕜] X`, then every series in
  `X` with bounded finite subsums converges unconditionally;
* `TauCeti.forall_summable_iff_forall_not_antilipschitzWith`: this property characterizes the
  Banach spaces containing no copy of `c₀`.

The supporting results are the following. A family with bounded finite subsums is absolutely
summable against every continuous linear functional
(`TauCeti.summable_norm_apply_of_forall_norm_sum_le`), and its sums against null coefficient
families define a bounded operator `ZeroAtInftyContinuousMap.linearCombinationOfBddSums` out of
`C₀(I, 𝕜)`. A non-summable family in a Banach space has pairwise disjoint finite blocks with sums of
norm bounded below (`TauCeti.exists_pairwise_disjoint_le_norm_sum_of_not_summable`). These block
sums again have bounded subsums, so they are weakly null but not norm null, and a basic
subsequence of them (`TauCeti.exists_strictMono_norm_sum_range_le_two_mul`) spans a copy of `c₀`.

## References

* C. Bessaga and A. Pełczyński, *On bases and unconditional convergence of series in Banach
  spaces*, Studia Math. 17 (1958), 151–164.
* F. Albiac and N. J. Kalton, *Topics in Banach Space Theory*, Theorem 2.4.11.
* J. Diestel, *Sequences and Series in Banach Spaces*, Chapter V, Theorem 8.
-/

public section

open Filter Finset Function Topology
open scoped NNReal ZeroAtInfty

variable {𝕜 X : Type*} [RCLike 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]

namespace TauCeti

/-- If every finite subsum of a family `x` has norm at most `C`, then the values of a continuous
linear functional `f` along `x` have absolute sums at most `4 * C * ‖f‖`. -/
theorem sum_norm_apply_le_of_forall_norm_sum_le {ι : Type*} {x : ι → X} {C : ℝ}
    (hx : ∀ s : Finset ι, ‖∑ i ∈ s, x i‖ ≤ C) (f : StrongDual 𝕜 X) (s : Finset ι) :
    ∑ i ∈ s, ‖f (x i)‖ ≤ 4 * C * ‖f‖ := by
  -- Rotate each value `f (x i)` onto the nonnegative real axis.
  choose c hc hfc using fun i ↦ RCLike.exists_norm_eq_mul_self (f (x i))
  calc ∑ i ∈ s, ‖f (x i)‖ = RCLike.re (f (∑ i ∈ s, c i • x i)) := by
        simp only [map_sum, map_smul, smul_eq_mul, ← hfc, RCLike.ofReal_re]
    _ ≤ ‖f (∑ i ∈ s, c i • x i)‖ := RCLike.re_le_norm _
    _ ≤ ‖f‖ * ‖∑ i ∈ s, c i • x i‖ := f.le_opNorm _
    _ ≤ ‖f‖ * (4 * 1 * C) := by
        gcongr
        exact norm_sum_smul_le_four_mul (fun u _ ↦ hx u) zero_le_one fun i _ ↦ (hc i).le
    _ = 4 * C * ‖f‖ := by ring

/-- A family with uniformly bounded finite subsums is absolutely summable against every continuous
linear functional. -/
theorem summable_norm_apply_of_forall_norm_sum_le {ι : Type*} {x : ι → X} {C : ℝ}
    (hx : ∀ s : Finset ι, ‖∑ i ∈ s, x i‖ ≤ C) (f : StrongDual 𝕜 X) :
    Summable fun i ↦ ‖f (x i)‖ :=
  summable_of_sum_le (fun _ ↦ norm_nonneg _) (sum_norm_apply_le_of_forall_norm_sum_le hx f)

/-- A family which is not summable in a complete space has pairwise disjoint finite blocks whose
sums all have norm at least some fixed `ε > 0`. -/
theorem exists_pairwise_disjoint_le_norm_sum_of_not_summable [CompleteSpace X] {ι : Type*}
    {x : ι → X} (hx : ¬Summable x) :
    ∃ ε > 0, ∃ t : ℕ → Finset ι, Pairwise (Disjoint on t) ∧ ∀ k, ε ≤ ‖∑ i ∈ t k, x i‖ := by
  classical
  rw [summable_iff_vanishing_norm] at hx
  push Not at hx
  obtain ⟨ε, hε, hT⟩ := hx
  choose T hTdisj hTnorm using hT
  -- `S k` is the union of the first `k` blocks, and the next block avoids it.
  let S : ℕ → Finset ι := Nat.rec ∅ fun _ S ↦ S ∪ T S
  have hS (k : ℕ) : S (k + 1) = S k ∪ T (S k) := rfl
  have hmono : Monotone S := monotone_nat_of_le_succ fun k ↦ by rw [hS]; exact subset_union_left
  have hsub {i j : ℕ} (hij : i < j) : T (S i) ⊆ S j :=
    (subset_union_right.trans (hS i).symm.subset).trans (hmono hij)
  refine ⟨ε, hε, fun k ↦ T (S k), fun i j hij ↦ ?_, fun k ↦ hTnorm _⟩
  rcases hij.lt_or_gt with h | h
  · exact (hTdisj (S j)).symm.mono_left (hsub h)
  · exact (hTdisj (S i)).mono_right (hsub h)

end TauCeti

namespace ZeroAtInftyContinuousMap

variable {I : Type*} [TopologicalSpace I] [DiscreteTopology I]

/-- If the finite subsums of `v` are bounded, then the series `∑ i, a i • v i` with coefficients
vanishing at infinity converges unconditionally in a Banach space. -/
theorem summable_smul_of_forall_norm_sum_le [CompleteSpace X] {v : I → X} {C : ℝ}
    (hv : ∀ s : Finset I, ‖∑ i ∈ s, v i‖ ≤ C) (a : C₀(I, 𝕜)) :
    Summable fun i ↦ a i • v i := by
  classical
  have hC : 0 ≤ C := by simpa using hv ∅
  refine summable_iff_vanishing_norm.2 fun δ hδ ↦ ?_
  -- Only finitely many coefficients exceed `η`; the remaining terms have small sums.
  set η := δ / (4 * C + 1) with hη
  have hη0 : 0 < η := by positivity
  have hfin : {i | ¬‖a i‖ ≤ η}.Finite := eventually_cofinite.1 <|
    (tendsto_zero_iff_norm_tendsto_zero.1 a.tendsto_cofinite).eventually (eventually_le_nhds hη0)
  refine ⟨hfin.toFinset, fun t ht ↦ ?_⟩
  have hat (i : I) (hi : i ∈ t) : ‖a i‖ ≤ η :=
    not_not.1 fun h ↦ disjoint_left.1 ht hi (hfin.mem_toFinset.2 h)
  calc ‖∑ i ∈ t, a i • v i‖ ≤ 4 * η * C :=
        TauCeti.norm_sum_smul_le_four_mul (fun u _ ↦ hv u) hη0.le hat
    _ = δ * (4 * C / (4 * C + 1)) := by rw [hη]; field_simp
    _ < δ * 1 := by gcongr; exact (div_lt_one (by positivity)).2 (lt_add_one _)
    _ = δ := mul_one δ

/-- The norm of `∑' i, a i • v i` is at most `4 * C * ‖a‖` when the finite subsums of `v` have
norm at most `C`. -/
theorem norm_tsum_smul_le_of_forall_norm_sum_le [CompleteSpace X] {v : I → X} {C : ℝ}
    (hv : ∀ s : Finset I, ‖∑ i ∈ s, v i‖ ≤ C) (a : C₀(I, 𝕜)) :
    ‖∑' i, a i • v i‖ ≤ 4 * C * ‖a‖ :=
  le_of_tendsto' (summable_smul_of_forall_norm_sum_le hv a).hasSum.norm fun s ↦
    (TauCeti.norm_sum_smul_le_four_mul (fun u _ ↦ hv u) (norm_nonneg a)
      fun i _ ↦ norm_coe_le_norm a i).trans_eq (by ring)

variable (𝕜) in
/-- The **linear combination map** of a family `v` with bounded finite subsums in a Banach space:
the bounded operator `C₀(I, 𝕜) →L[𝕜] X` sending `a` to `∑' i, a i • v i`. -/
noncomputable def linearCombinationOfBddSums [CompleteSpace X] (v : I → X)
    (hv : ∃ C, ∀ s : Finset I, ‖∑ i ∈ s, v i‖ ≤ C) : C₀(I, 𝕜) →L[𝕜] X :=
  LinearMap.mkContinuousOfExistsBound
    { toFun a := ∑' i, a i • v i
      map_add' a b := by
        obtain ⟨C, hC⟩ := hv
        simp only [FunLike.coe_add, Pi.add_apply, add_smul]
        exact (summable_smul_of_forall_norm_sum_le hC a).tsum_add
          (summable_smul_of_forall_norm_sum_le hC b)
      map_smul' c a := by
        obtain ⟨C, hC⟩ := hv
        simp only [FunLike.coe_smul, Pi.smul_apply, smul_eq_mul, mul_smul, RingHom.id_apply]
        exact (summable_smul_of_forall_norm_sum_le hC a).tsum_const_smul c }
    (let ⟨C, hC⟩ := hv; ⟨4 * C, fun a ↦ norm_tsum_smul_le_of_forall_norm_sum_le hC a⟩)

variable [CompleteSpace X] {v : I → X} (hv : ∃ C, ∀ s : Finset I, ‖∑ i ∈ s, v i‖ ≤ C)

/-- The linear combination map at `a` is the sum `∑' i, a i • v i`. -/
theorem linearCombinationOfBddSums_apply (a : C₀(I, 𝕜)) :
    linearCombinationOfBddSums 𝕜 v hv a = ∑' i, a i • v i :=
  (rfl)

/-- The series `∑ i, a i • v i` converges unconditionally to the linear combination map at `a`. -/
theorem hasSum_linearCombinationOfBddSums (a : C₀(I, 𝕜)) :
    HasSum (fun i ↦ a i • v i) (linearCombinationOfBddSums 𝕜 v hv a) :=
  (summable_smul_of_forall_norm_sum_le hv.choose_spec a).hasSum

/-- The linear combination map sends the coordinate vector at `i` to `v i`. -/
@[simp]
theorem linearCombinationOfBddSums_single [DecidableEq I] (i : I) :
    linearCombinationOfBddSums 𝕜 v hv (single i 1) = v i := by
  rw [linearCombinationOfBddSums_apply, tsum_eq_single i fun j hj ↦ by simp [hj]]
  simp

/-- The linear combination map has norm at most `4 * C` when the finite subsums of `v` have norm at
most `C`. -/
theorem norm_linearCombinationOfBddSums_le {C : ℝ} (hC : ∀ s : Finset I, ‖∑ i ∈ s, v i‖ ≤ C) :
    ‖linearCombinationOfBddSums 𝕜 v hv‖ ≤ 4 * C := by
  have hC0 : 0 ≤ C := by simpa using hC ∅
  exact ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun a ↦
    norm_tsum_smul_le_of_forall_norm_sum_le hC a

end ZeroAtInftyContinuousMap

namespace TauCeti

/-- On a basic sequence with constant `2` whose terms have norm at least `ε > 0`, the linear
combination map is bounded below: it is antilipschitz with constant `4 / ε`. -/
private theorem exists_antilipschitzWith_linearCombinationOfBddSums [CompleteSpace X]
    {v : ℕ → X} (hv : ∃ C, ∀ s : Finset ℕ, ‖∑ i ∈ s, v i‖ ≤ C) {ε : ℝ} (hε : 0 < ε)
    (hvε : ∀ j, ε ≤ ‖v j‖) (hbasic : ∀ (a : ℕ → 𝕜) {m n : ℕ}, m ≤ n →
      ‖∑ i ∈ range m, a i • v i‖ ≤ 2 * ‖∑ i ∈ range n, a i • v i‖) :
    ∃ K, AntilipschitzWith K (ZeroAtInftyContinuousMap.linearCombinationOfBddSums 𝕜 v hv) := by
  set T := ZeroAtInftyContinuousMap.linearCombinationOfBddSums 𝕜 v hv
  -- Each coefficient is controlled by the partial sums, and these converge to `T a`.
  have hcoef (a : C₀(ℕ, 𝕜)) (m : ℕ) : ‖a m‖ * ε ≤ 4 * ‖T a‖ := by
    have hlim :=
      (ZeroAtInftyContinuousMap.hasSum_linearCombinationOfBddSums hv a).tendsto_sum_nat.norm
    refine ge_of_tendsto (hlim.const_mul 4) (eventually_atTop.2 ⟨m + 1, fun n hn ↦ ?_⟩)
    calc ‖a m‖ * ε ≤ ‖a m • v m‖ := by rw [norm_smul]; gcongr; exact hvε m
      _ = ‖∑ i ∈ range (m + 1), a i • v i - ∑ i ∈ range m, a i • v i‖ := by
          rw [sum_range_succ_sub_sum]
      _ ≤ ‖∑ i ∈ range (m + 1), a i • v i‖ + ‖∑ i ∈ range m, a i • v i‖ := norm_sub_le _ _
      _ ≤ 2 * ‖∑ i ∈ range n, a i • v i‖ + 2 * ‖∑ i ∈ range n, a i • v i‖ :=
          add_le_add (hbasic a hn) (hbasic a (by omega))
      _ = 4 * ‖∑ i ∈ range n, a i • v i‖ := by ring
  refine ⟨(4 / ε).toNNReal, T.antilipschitz_of_bound fun a ↦ ?_⟩
  rw [Real.coe_toNNReal _ (by positivity)]
  refine (ZeroAtInftyContinuousMap.norm_le (by positivity)).2 fun m ↦ ?_
  rw [div_mul_eq_mul_div, le_div_iff₀ hε]
  linarith [hcoef a m]

/-- **Bessaga–Pełczyński.** In a real or complex Banach space containing no copy of `c₀`, that is
admitting no bounded-below continuous linear map from `C₀(ℕ, 𝕜)`, every series with uniformly
bounded finite subsums converges unconditionally. -/
theorem summable_of_forall_not_antilipschitzWith [CompleteSpace X]
    (hX : ∀ (T : C₀(ℕ, 𝕜) →L[𝕜] X) (K : ℝ≥0), ¬AntilipschitzWith K T) {x : ℕ → X}
    (hx : ∃ C, ∀ s : Finset ℕ, ‖∑ n ∈ s, x n‖ ≤ C) : Summable x := by
  classical
  by_contra hns
  obtain ⟨C, hC⟩ := hx
  obtain ⟨ε, hε, t, ht, htε⟩ := exists_pairwise_disjoint_le_norm_sum_of_not_summable hns
  -- The block sums `u k` have bounded subsums, so they are weakly null but not norm null.
  set u : ℕ → X := fun k ↦ ∑ n ∈ t k, x n
  have hu (s : Finset ℕ) : ‖∑ k ∈ s, u k‖ ≤ C := by
    rw [← sum_biUnion (ht.set_pairwise _)]
    exact hC _
  have hweak (f : StrongDual 𝕜 X) : Tendsto (fun k ↦ f (u k)) atTop (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.2
      (summable_norm_apply_of_forall_norm_sum_le hu f).tendsto_atTop_zero
  -- A basic subsequence of the block sums spans a copy of `c₀`.
  obtain ⟨φ, hφ, hφε, hbasic⟩ :=
    exists_strictMono_norm_sum_range_le_two_mul hweak hε (Frequently.of_forall htε)
  have hv (s : Finset ℕ) : ‖∑ j ∈ s, u (φ j)‖ ≤ C := by
    rw [← sum_image hφ.injective.injOn]
    exact hu _
  obtain ⟨K, hK⟩ := exists_antilipschitzWith_linearCombinationOfBddSums ⟨C, hv⟩ hε hφε hbasic
  exact hX _ K hK

/-- **The `c₀` criterion for unconditional convergence.** A real or complex Banach space contains no
copy of `c₀`, that is admits no bounded-below continuous linear map from `C₀(ℕ, 𝕜)`, exactly when
every series in it with uniformly bounded finite subsums converges unconditionally. -/
theorem forall_summable_iff_forall_not_antilipschitzWith [CompleteSpace X] :
    (∀ x : ℕ → X, (∃ C, ∀ s : Finset ℕ, ‖∑ n ∈ s, x n‖ ≤ C) → Summable x) ↔
      ∀ (T : C₀(ℕ, 𝕜) →L[𝕜] X) (K : ℝ≥0), ¬AntilipschitzWith K T := by
  classical
  refine ⟨fun h T K hK ↦ ?_, fun hX x hx ↦ summable_of_forall_not_antilipschitzWith hX hx⟩
  -- The images of the coordinate vectors have bounded subsums but are not norm null.
  have hbound (s : Finset ℕ) :
      ‖∑ n ∈ s, ZeroAtInftyContinuousMap.single n (1 : 𝕜)‖ ≤ 1 :=
    (ZeroAtInftyContinuousMap.norm_le zero_le_one).2 fun j ↦ by
      rw [ZeroAtInftyContinuousMap.sum_single_apply]
      split_ifs <;> simp
  have hsum := h (fun n ↦ T (ZeroAtInftyContinuousMap.single n 1)) ⟨‖T‖, fun s ↦ by
    rw [← map_sum]
    exact T.le_of_opNorm_le_of_le le_rfl (hbound s) |>.trans_eq (mul_one _)⟩
  have h0 := (tendsto_zero_iff_norm_tendsto_zero.1 hsum.tendsto_atTop_zero).const_mul (K : ℝ)
  rw [mul_zero] at h0
  obtain ⟨n, hn⟩ := (h0.eventually (gt_mem_nhds zero_lt_one)).exists
  have := hK.le_mul_norm (map_zero T) (ZeroAtInftyContinuousMap.single n (1 : 𝕜))
  rw [ZeroAtInftyContinuousMap.norm_single, norm_one] at this
  linarith

end TauCeti
