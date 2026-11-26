/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.Eigenvalues.Basic
public import Mathlib.Analysis.Matrix.MeasurableSpace
public import Mathlib.Analysis.Calculus.FDeriv.Basic

/-!
# Continuity of ordered Hermitian eigenvalues

The decreasing eigenvalue list of a Hermitian matrix is `1`-Lipschitz from the Euclidean
operator norm to the sup norm on the list. In particular it is continuous, including at
repeated eigenvalues, and measurable for the entrywise Borel structure on matrices.
These results allow eigenvalues of a measurable random Hermitian matrix to be treated as
random variables, without choosing measurable eigenvectors.

We use the subtype of Hermitian matrices, with its inherited topology and measurable
structure. For a family of Hermitian matrices, continuity of the entries at a point gives
continuity of the ordered eigenvalues there (`Matrix.continuousAt_eigenvalues₀`), so a spectral
gap of `M x₀` persists near `x₀` (`Matrix.eventually_eigenvalues₀_lt`), and differentiability of
the entries at a point makes the ordered eigenvalues move by `O(‖x - x₀‖)`
(`Matrix.isBigO_eigenvalues₀_sub`). On the real vector space of Hermitian matrices the ordered
eigenvalues are continuous (`Matrix.continuous_eigenvalues₀_selfAdjoint`), so the Hermitian
matrices whose ordered eigenvalues lie in an open set form an open set
(`Matrix.isOpen_setOf_eigenvalues₀_mem`). Along any filter, if
`‖A i - B i‖ → 0` in the Euclidean operator norm for Hermitian `A i` and `B i`, then selected
ordered eigenvalues of `A i` converge to the limit of the corresponding eigenvalues of `B i`
(`Filter.Tendsto.eigenvalues₀_of_tendsto_l2_opNorm_sub_zero`); the sizes may vary. Continuity
uses the usual entrywise topology: Mathlib's Euclidean operator norm induces this same topology.
Empty index types are allowed.

## References

* R. Bhatia, *Matrix Analysis*, Springer (1997), Chapter III, for Weyl's perturbation bound
  and continuity of ordered eigenvalues.
-/

public section

noncomputable section

namespace Matrix

variable {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [RCLike 𝕜]

open scoped Matrix.Norms.L2Operator

/-- The decreasing eigenvalue list is `1`-Lipschitz for the Euclidean operator norm on
Hermitian matrices and the sup norm on the eigenvalue list. -/
theorem lipschitzWith_eigenvalues₀ :
    LipschitzWith 1 (fun A : {A : Matrix n n 𝕜 // A.IsHermitian} => A.property.eigenvalues₀) := by
  refine LipschitzWith.of_dist_le_mul fun A B => ?_
  simp only [NNReal.coe_one, one_mul, Subtype.dist_eq, dist_eq_norm]
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_
  simpa only [Pi.sub_apply, Real.norm_eq_abs] using
    A.property.abs_eigenvalues₀_sub_le_norm B.property i

/-- Ordered Hermitian eigenvalues depend continuously on the matrix, even at repeated
eigenvalues. -/
@[fun_prop]
theorem continuous_eigenvalues₀ :
    Continuous (fun A : {A : Matrix n n 𝕜 // A.IsHermitian} => A.property.eigenvalues₀) :=
  lipschitzWith_eigenvalues₀.continuous

/-- Mathlib's matrix-indexed eigenvalue list is continuous on Hermitian matrices. -/
@[fun_prop]
theorem continuous_eigenvalues :
    Continuous (fun A : {A : Matrix n n 𝕜 // A.IsHermitian} => A.property.eigenvalues) := by
  apply continuous_pi
  intro i
  -- The matrix-indexed list is the sorted list reindexed by a fixed finite equivalence.
  simpa only [IsHermitian.eigenvalues, Function.comp_def] using
    (continuous_apply _).comp (continuous_eigenvalues₀ (n := n) (𝕜 := 𝕜))

/-- The ordered eigenvalues of a family of Hermitian matrices are continuous at every point at
which its entries are, including at repeated eigenvalues. -/
theorem continuousAt_eigenvalues₀ {X : Type*} [TopologicalSpace X] {M : X → Matrix n n 𝕜}
    (hM : ∀ x, (M x).IsHermitian) {x₀ : X} (h : ∀ a b, ContinuousAt (fun x ↦ M x a b) x₀)
    (i : Fin (Fintype.card n)) : ContinuousAt (fun x ↦ (hM x).eigenvalues₀ i) x₀ :=
  ((continuous_apply i).comp continuous_eigenvalues₀).continuousAt.comp
    (f := fun x ↦ (⟨M x, hM x⟩ : {A : Matrix n n 𝕜 // A.IsHermitian}))
    (tendsto_subtype_rng.2 (continuousAt_pi.2 fun a ↦ continuousAt_pi.2 fun b ↦ h a b))

/-- The ordered eigenvalues are continuous on the real vector space of Hermitian matrices. -/
@[fun_prop]
theorem continuous_eigenvalues₀_selfAdjoint :
    Continuous (fun A : selfAdjoint.submodule ℝ (Matrix n n 𝕜) ↦
      A.property.isHermitian.eigenvalues₀) :=
  continuous_eigenvalues₀.comp (continuous_subtypeVal.subtype_mk fun A ↦ A.property.isHermitian)

/-- The Hermitian matrices whose ordered eigenvalue vector lies in an open set `Ω` form an open
set. -/
theorem isOpen_setOf_eigenvalues₀_mem {Ω : Set (Fin (Fintype.card n) → ℝ)} (hΩ : IsOpen Ω) :
    IsOpen {A : selfAdjoint.submodule ℝ (Matrix n n 𝕜) |
      A.property.isHermitian.eigenvalues₀ ∈ Ω} :=
  hΩ.preimage continuous_eigenvalues₀_selfAdjoint

open Filter Topology in
/-- **Spectral gaps persist.** For a family of Hermitian matrices whose entries are continuous at
`x₀`, if the `k` largest eigenvalues of `M x₀` are separated from the others, `λⱼ < λᵢ` for
`i < k ≤ j`, then the same holds for `M x` for every `x` near `x₀`. -/
theorem eventually_eigenvalues₀_lt {X : Type*} [TopologicalSpace X] {M : X → Matrix n n 𝕜}
    (hM : ∀ x, (M x).IsHermitian) {x₀ : X} (h : ∀ a b, ContinuousAt (fun x ↦ M x a b) x₀)
    {k : ℕ} (hgap : ∀ i j : Fin (Fintype.card n), i.val < k → k ≤ j.val →
      (hM x₀).eigenvalues₀ j < (hM x₀).eigenvalues₀ i) :
    ∀ᶠ x in 𝓝 x₀, ∀ i j : Fin (Fintype.card n), i.val < k → k ≤ j.val →
      (hM x).eigenvalues₀ j < (hM x).eigenvalues₀ i := by
  refine eventually_all.2 fun i ↦ eventually_all.2 fun j ↦ ?_
  by_cases hij : i.val < k ∧ k ≤ j.val
  · filter_upwards [(continuousAt_eigenvalues₀ hM h j).eventually_lt
      (continuousAt_eigenvalues₀ hM h i) (hgap i j hij.1 hij.2)] with x hx
    exact fun _ _ ↦ hx
  · exact Eventually.of_forall fun _ hi hj ↦ absurd ⟨hi, hj⟩ hij

open Asymptotics Filter Finset Topology in
/-- The sorted eigenvalues of a family of Hermitian matrices whose entries are differentiable at
`x₀` move by `O(‖x - x₀‖)`. -/
theorem isBigO_eigenvalues₀_sub {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {M : E → Matrix n n 𝕜} {x₀ : E} (hM : ∀ x, (M x).IsHermitian)
    (hMd : ∀ a b, DifferentiableAt ℝ (fun x ↦ M x a b) x₀) :
    (fun x ↦ (hM x).eigenvalues₀ - (hM x₀).eigenvalues₀) =O[𝓝 x₀] fun x ↦ x - x₀ := by
  set ε : E → ℝ := fun x ↦ ∑ a, ∑ b, ‖M x a b - M x₀ a b‖
  have hεO : ε =O[𝓝 x₀] fun x ↦ ‖x - x₀‖ :=
    IsBigO.fun_sum fun a _ ↦ IsBigO.fun_sum fun b _ ↦
      (hMd a b).hasFDerivAt.isBigO_sub.norm_left.norm_right
  refine IsBigO.of_norm_right (IsBigO.trans ?_ hεO)
  refine IsBigO.of_bound (Fintype.card n) (Eventually.of_forall fun x ↦ ?_)
  have hε : 0 ≤ ε x := sum_nonneg fun _ _ ↦ sum_nonneg fun _ _ ↦ norm_nonneg _
  rw [Real.norm_of_nonneg hε]
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i ↦ ?_
  rw [Pi.sub_apply, Real.norm_eq_abs]
  -- Each entry of `M x - M x₀` is bounded by the sum `ε x` of all of them.
  refine (hM x).abs_eigenvalues₀_sub_le_of_entry_le (hM x₀) (fun a b ↦ ?_) i
  exact (single_le_sum (f := fun b ↦ ‖M x a b - M x₀ a b‖) (fun _ _ ↦ norm_nonneg _)
    (mem_univ b)).trans (single_le_sum (f := fun a ↦ ∑ b, ‖M x a b - M x₀ a b‖)
      (fun _ _ ↦ sum_nonneg fun _ _ ↦ norm_nonneg _) (mem_univ a))

open Filter in
open scoped Topology in
/-- If the selected ordered eigenvalues of `B` converge and `‖A - B‖` tends to zero in
operator norm, the corresponding eigenvalues of `A` converge to the same limit.
The index type may vary. -/
theorem _root_.Filter.Tendsto.eigenvalues₀_of_tendsto_l2_opNorm_sub_zero
    {ι : Type*} {m : ι → Type*} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)]
    {A B : (i : ι) → Matrix (m i) (m i) 𝕜} {hB : ∀ i, (B i).IsHermitian}
    {j : (i : ι) → Fin (Fintype.card (m i))} {l : Filter ι} {c : ℝ}
    (h : Tendsto (fun i ↦ (hB i).eigenvalues₀ (j i)) l (𝓝 c))
    (hA : ∀ i, (A i).IsHermitian) (hd : Tendsto (fun i ↦ ‖A i - B i‖) l (𝓝 0)) :
    Tendsto (fun i ↦ (hA i).eigenvalues₀ (j i)) l (𝓝 c) := by
  apply h.congr_dist
  refine squeeze_zero (fun _ ↦ dist_nonneg) (fun i ↦ ?_) hd
  rw [dist_comm, Real.dist_eq]
  exact (hA i).abs_eigenvalues₀_sub_le_norm (hB i) (j i)

variable [MeasurableSpace 𝕜] [BorelSpace 𝕜]

/-- The ordered eigenvalue list of a Hermitian matrix is measurable for the entrywise
Borel structure. -/
@[fun_prop]
theorem measurable_eigenvalues₀ :
    Measurable (fun A : {A : Matrix n n 𝕜 // A.IsHermitian} => A.property.eigenvalues₀) :=
  continuous_eigenvalues₀.measurable

/-- Mathlib's matrix-indexed eigenvalue list is measurable on Hermitian matrices. -/
@[fun_prop]
theorem measurable_eigenvalues :
    Measurable (fun A : {A : Matrix n n 𝕜 // A.IsHermitian} => A.property.eigenvalues) :=
  continuous_eigenvalues.measurable

end Matrix
