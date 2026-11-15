/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Real.Cardinality

/-!
# Countable support and separability of `ℓᵖ` spaces

Every sequence in `ℓᵖ` at a finite exponent `p < ∞` vanishes outside a countable set of indices
(`Memℓp.countable_dsupport`, `lp.countable_dsupport`): for `p = 0` its support is finite by
definition, and for `0 < p < ∞` the `p`-th powers of the coordinate norms form a summable
nonnegative family, whose support is countable.

Conversely, uncountably many nontrivial fibers obstruct separability of `lp E p` at every normed
exponent `1 ≤ p ≤ ∞`: choosing a nonzero element in each nontrivial fiber produces single-coordinate
vectors whose pairwise distances on each norm-threshold slice `{i | (n + 1)⁻¹ ≤ ‖x i‖}` are bounded
away from zero, so a separable `lp E p` can only accommodate countably many nontrivial fibers
(`lp.countable_nontrivial_of_separableSpace`). Together with the isometric coordinate inclusions
`E i ↪ lp E p`, this characterizes separability at finite exponents `1 ≤ p < ∞`
(`lp.separableSpace_iff`, `lp.separableSpace_iff_countable`): `lp E p` is separable if and only if
every fiber `E i` is separable and `{i | Nontrivial (E i)}` is countable.

In particular, for distinct indices `i ≠ j` in `ℓ²`, the unit coordinate vectors sit at distance
`√2` (`lp.dist_single_one_two_of_ne`), and `ℓᵖ([0, 1], G)` is nonseparable for every nontrivial
normed group `G` and `1 ≤ p ≤ ∞` (`lp.not_separableSpace_Icc`).

## References

* J. B. Conway, *A Course in Functional Analysis*, 2nd ed., §I.4.
* F. Albiac and N. J. Kalton, *Topics in Banach Space Theory*, Chapter 1.
-/

public section

open scoped ENNReal Topology lp

section Support

variable {ι G : Type*} {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)] [NormedAddCommGroup G]
  {p : ℝ≥0∞}

/-- Every sequence in `ℓᵖ` for `p ≠ ∞` has countable support. -/
theorem Memℓp.countable_dsupport {f : ∀ i, E i} (hf : Memℓp f p) (hp : p ≠ ∞) :
    {i | f i ≠ 0}.Countable := by
  rcases eq_or_ne p 0 with rfl | hp₀
  · exact hf.finite_dsupport.countable
  · have hpr : 0 < p.toReal := ENNReal.toReal_pos hp₀ hp
    refine (hf.summable hpr).countable_support.mono fun i hi ↦ ?_
    exact (Real.rpow_pos_of_pos (norm_pos_iff.2 hi) p.toReal).ne'

/-- Non-dependent form of `Memℓp.countable_dsupport` phrased with `Function.support`. -/
theorem Memℓp.countable_support {f : ι → G} (hf : Memℓp f p) (hp : p ≠ ∞) :
    (Function.support f).Countable :=
  hf.countable_dsupport hp

/-- Every element of `lp E p` for `p ≠ ∞` has countable support. -/
theorem lp.countable_dsupport (f : lp E p) (hp : p ≠ ∞) :
    {i | f i ≠ 0}.Countable :=
  (lp.memℓp f).countable_dsupport hp

/-- Every element of `ℓ^p(ι, G)` for `p ≠ ∞` has countable `Function.support`. -/
theorem lp.countable_support (f : ℓ^p(ι, G)) (hp : p ≠ ∞) :
    (Function.support f).Countable :=
  (lp.memℓp f).countable_support hp

end Support

namespace lp

section SingleDist

variable {ι G : Type*} {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)] [NormedAddCommGroup G]
  {p : ℝ≥0∞}

/-- For `0 < p < ∞` and distinct indices `i ≠ j`, the `ℓᵖ` norm of the difference of two
single-coordinate vectors is `(‖x‖ ^ p + ‖y‖ ^ p) ^ (1 / p)`. -/
theorem norm_single_sub_single_of_ne [DecidableEq ι] (hp : 0 < p.toReal) {i j : ι} (hij : i ≠ j)
    (x : E i) (y : E j) :
    ‖lp.single p i x - lp.single p j y‖ = (‖x‖ ^ p.toReal + ‖y‖ ^ p.toReal) ^ (1 / p.toReal) := by
  let f : ∀ k, E k := fun k ↦ if hki : k = i then hki ▸ x else if hkj : k = j then hkj ▸ (-y) else 0
  have hsum : ∑ k ∈ ({i, j} : Finset ι), lp.single p k (f k) =
      lp.single p i x - lp.single p j y := by
    rw [Finset.sum_pair hij, sub_eq_add_neg, ← lp.single_neg]
    simp [f, hij.symm]
  have hrpow := lp.norm_sum_single (E := E) hp f {i, j}
  rw [hsum, Finset.sum_pair hij] at hrpow
  have hfi : ‖f i‖ = ‖x‖ := by simp [f]
  have hfj : ‖f j‖ = ‖y‖ := by simp [f, hij.symm]
  rw [hfi, hfj] at hrpow
  have hexp := congrArg (· ^ (1 / p.toReal)) hrpow
  simpa [← Real.rpow_mul (norm_nonneg' _), hp.ne'] using hexp

/-- For `1 ≤ p < ∞` and distinct indices `i ≠ j`, the distance between `lp.single p i x` and
`lp.single p j y` is `(‖x‖ ^ p + ‖y‖ ^ p) ^ (1 / p)`. -/
theorem dist_single_single_of_ne [DecidableEq ι] [Fact (1 ≤ p)] (hp : p ≠ ∞) {i j : ι}
    (hij : i ≠ j) (x : E i) (y : E j) :
    dist (lp.single p i x) (lp.single p j y) =
      (‖x‖ ^ p.toReal + ‖y‖ ^ p.toReal) ^ (1 / p.toReal) := by
  have hp₀ : 0 < p.toReal := ENNReal.toReal_pos (zero_lt_one.trans_le Fact.out).ne' hp
  rw [dist_eq_norm, norm_single_sub_single_of_ne hp₀ hij]

/-- Distinct unit coordinate vectors in `ℓ²(ι, G)` sit at pairwise distance `√2`. -/
theorem dist_single_one_two_of_ne [DecidableEq ι] [One G] [NormOneClass G] {i j : ι}
    (hij : i ≠ j) :
    dist (lp.single (E := fun _ : ι ↦ G) 2 i 1) (lp.single 2 j 1) = √2 := by
  rw [dist_single_single_of_ne (by simp) hij, Real.sqrt_eq_rpow]
  norm_num

end SingleDist

section Separability

variable {ι G : Type*} {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)] [NormedAddCommGroup G]
  {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Each coordinate fiber of a separable `lp E p` space is separable, as it embeds isometrically via
`lp.single p i`. -/
theorem separableSpace_apply_of_separableSpace [TopologicalSpace.SeparableSpace (lp E p)]
    (i : ι) : TopologicalSpace.SeparableSpace (E i) := by
  classical
  have := UniformSpace.secondCountable_of_separable (lp E p)
  have := (lp.isometry_single (E := E) (p := p) i).isEmbedding.secondCountableTopology
  infer_instance

/-- If `lp E p` is separable (`1 ≤ p ≤ ∞`), at most countably many fibers `E i` are nontrivial. -/
theorem countable_nontrivial_of_separableSpace [TopologicalSpace.SeparableSpace (lp E p)] :
    {i | Nontrivial (E i)}.Countable := by
  classical
  have hp₀ : p ≠ 0 := (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne'
  -- Pick a nonzero vector `x i` in each nontrivial fiber and stratify by `(n + 1)⁻¹ ≤ ‖x i‖`.
  let x : ∀ i, E i := fun i ↦
    if h : ∃ v : E i, v ≠ 0 then Classical.choose h else 0
  have hx_pos {i : ι} (hi : Nontrivial (E i)) : 0 < ‖x i‖ := by
    obtain ⟨v, hv⟩ := exists_ne (0 : E i)
    have hex : ∃ w : E i, w ≠ 0 := ⟨v, hv⟩
    simpa only [x, dite_eq_left hex, norm_pos_iff] using Classical.choose_spec hex
  have hcover : {i | Nontrivial (E i)} ⊆ ⋃ n : ℕ, {i | ((n : ℝ) + 1)⁻¹ ≤ ‖x i‖} := by
    intro i hi
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (hx_pos hi)
    exact Set.mem_iUnion.2 ⟨n, by simpa only [one_div, Set.mem_ofPred_eq] using hn.le⟩
  refine (Set.countable_iUnion fun n : ℕ ↦ ?_).mono hcover
  set r : ℝ := ((n : ℝ) + 1)⁻¹
  have hr : 0 < r := by positivity
  let B : ι → Set (lp E p) := fun i ↦ Metric.ball (lp.single p i (x i)) (r / 2)
  have hdisj : {i | r ≤ ‖x i‖}.PairwiseDisjoint B := by
    intro i hi j _ hij
    refine Metric.ball_disjoint_ball ?_
    have hcoord : r ≤ ‖(lp.single p i (x i) - lp.single p j (x j)) i‖ := by
      simpa [lp.single_apply, Pi.single_eq_same, Pi.single_eq_of_ne hij] using hi
    calc r / 2 + r / 2 = r := add_halves r
      _ ≤ ‖(lp.single p i (x i) - lp.single p j (x j)) i‖ := hcoord
      _ ≤ ‖lp.single p i (x i) - lp.single p j (x j)‖ := lp.norm_apply_le_norm hp₀ _ i
      _ = dist (lp.single p i (x i)) (lp.single p j (x j)) := (dist_eq_norm _ _).symm
  exact hdisj.countable_of_isOpen (fun _ _ ↦ Metric.isOpen_ball)
    fun i _ ↦ ⟨lp.single p i (x i), Metric.mem_ball_self (half_pos hr)⟩

/-- For a finite exponent `1 ≤ p < ∞`, `lp E p` is separable when every fiber is separable and only
countably many fibers are nontrivial. -/
theorem separableSpace_of_countable_nontrivial [∀ i, TopologicalSpace.SeparableSpace (E i)]
    (hc : {i | Nontrivial (E i)}.Countable) (hp : p ≠ ∞) :
    TopologicalSpace.SeparableSpace (lp E p) := by
  classical
  have := hc.to_subtype
  set S : Set (lp E p) := ⋃ i : {i // Nontrivial (E i)}, Set.range (lp.single p i.1)
  have hS : TopologicalSpace.IsSeparable S :=
    .iUnion fun i ↦ TopologicalSpace.isSeparable_range (lp.isometry_single i.1).continuous
  rw [← TopologicalSpace.isSeparable_univ_iff]
  refine (hS.span (R := ℕ)).closure.mono fun f _ ↦
    mem_closure_of_tendsto (lp.hasSum_single hp f) (Filter.Eventually.of_forall fun s ↦ ?_)
  refine Submodule.sum_mem _ fun i _ ↦ ?_
  by_cases hfi : f i = 0
  · simp [hfi]
  · have hnt : Nontrivial (E i) := ⟨⟨f i, 0, hfi⟩⟩
    exact Submodule.subset_span (Set.mem_iUnion.2 ⟨⟨i, hnt⟩, f i, rfl⟩)

/-- **Separability of `lp E p` (`1 ≤ p < ∞`).** For a finite exponent `1 ≤ p < ∞`, `lp E p` is
separable if and only if every coordinate fiber `E i` is separable and `{i | Nontrivial (E i)}` is
countable. -/
theorem separableSpace_iff (hp : p ≠ ∞) :
    TopologicalSpace.SeparableSpace (lp E p) ↔
      (∀ i, TopologicalSpace.SeparableSpace (E i)) ∧ {i | Nontrivial (E i)}.Countable :=
  ⟨fun _ ↦ ⟨separableSpace_apply_of_separableSpace (p := p),
      countable_nontrivial_of_separableSpace (p := p)⟩,
    fun ⟨_, hc⟩ ↦ separableSpace_of_countable_nontrivial hc hp⟩

/-- For a nontrivial separable fiber `G` and `1 ≤ p < ∞`, `ℓ^p(ι, G)` is separable if and only if
the index type `ι` is countable. -/
theorem separableSpace_iff_countable [Nontrivial G] [TopologicalSpace.SeparableSpace G]
    (hp : p ≠ ∞) :
    TopologicalSpace.SeparableSpace ℓ^p(ι, G) ↔ Countable ι := by
  rw [separableSpace_iff hp]
  simp [‹Nontrivial G›, ‹TopologicalSpace.SeparableSpace G›, Set.countable_univ_iff]

/-- Over an uncountable index type and a nontrivial fiber `G`, `ℓ^p(ι, G)` (`1 ≤ p ≤ ∞`) is not
separable. -/
theorem not_separableSpace_of_not_countable [Nontrivial G] (hι : ¬ Countable ι) :
    ¬ TopologicalSpace.SeparableSpace ℓ^p(ι, G) := by
  intro _
  have hc := countable_nontrivial_of_separableSpace (E := fun _ : ι ↦ G) (p := p)
  simp only [‹Nontrivial G›, Set.ofPred_true, Set.countable_univ_iff] at hc
  exact hι hc

/-- For any nontrivial normed group `G` and `1 ≤ p ≤ ∞` (in particular `ℓ²([0, 1], ℝ)` and
`ℓ²([0, 1], ℂ)`), the sequence space `ℓ^p([0, 1], G)` indexed by `[0, 1]` is not separable. -/
theorem not_separableSpace_Icc [Nontrivial G] :
    ¬ TopologicalSpace.SeparableSpace ℓ^p(Set.Icc (0 : ℝ) 1, G) := by
  refine not_separableSpace_of_not_countable fun hc ↦ ?_
  have hle := Cardinal.Real.Icc_countable_iff.mp (Set.countable_coe_iff.mp hc)
  linarith

end Separability

end lp
