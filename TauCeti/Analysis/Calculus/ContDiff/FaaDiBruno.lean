/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.FaaDiBruno
public import Mathlib.Analysis.Calculus.ContDiff.Comp

/-!
# Continuity of the Faà di Bruno composition

The `m`-th coefficient of `q.taylorComp p` is a finite sum, over the ordered partitions of `m`,
of continuous multilinear expressions in the coefficients of `q` and `p` of order at most `m`.
So it depends continuously on these finitely many coefficients. Combined with Mathlib's Faà di
Bruno formula `iteratedFDerivWithin_comp`, this says that the `m`-th derivative of a composite
`g ∘ f` depends continuously on the derivatives of `g` and of `f` of order at most `m`, which is
how continuity of composition in `C^n` topologies is proved.

The same expansion bounds the norm of the `m`-th coefficient
(`FormalMultilinearSeries.norm_taylorComp_le`): if the coefficients of `p` of orders `1` through
`m` have norm at most `B`, it is at most `max 1 B ^ m` times the sum, over the ordered partitions
`c` of `m`, of `‖q c.length‖`. For a composite `g ∘ f` this bounds the `m`-th derivative by the
derivatives of `g` of order at most `m` (`ContDiffAt.norm_iteratedFDeriv_comp_le_sum`), keeping
track of each order separately, as needed for changes of variables in Sobolev spaces.
-/

public section

open Filter Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]

/-- The `m`-th coefficient of the Taylor composition `q.taylorComp p` is continuous in the
coefficients of `q` of order at most `m` and of `p` of orders `1` through `m` (the constant
coefficient of `p` does not enter). -/
theorem Filter.Tendsto.taylorComp {α : Type*} {l : Filter α}
    {q : α → FormalMultilinearSeries 𝕜 F G} {p : α → FormalMultilinearSeries 𝕜 E F}
    {q₀ : FormalMultilinearSeries 𝕜 F G} {p₀ : FormalMultilinearSeries 𝕜 E F} {m : ℕ}
    (hq : ∀ k ≤ m, Tendsto (fun a ↦ q a k) l (𝓝 (q₀ k)))
    (hp : ∀ k, 1 ≤ k → k ≤ m → Tendsto (fun a ↦ p a k) l (𝓝 (p₀ k))) :
    Tendsto (fun a ↦ (q a).taylorComp (p a) m) l (𝓝 (q₀.taylorComp p₀ m)) := by
  refine tendsto_finsetSum _ fun c _ ↦ ?_
  have hB := ((c.compAlongOrderedFinpartitionL 𝕜 E F G).continuous.tendsto _).comp
    (hq c.length c.length_le)
  have hP : Tendsto (fun a i ↦ p a (c.partSize i)) l (𝓝 fun i ↦ p₀ (c.partSize i)) :=
    tendsto_pi_nhds.2 fun i ↦ hp _ (c.partSize_pos i) (c.partSize_le i)
  exact (continuous_eval.tendsto _).comp (hB.prodMk_nhds hP)

/-- **A norm bound for the Faà di Bruno composition.** If the coefficients of `p` of orders `1`
through `m` have norm at most `B`, then the `m`-th coefficient of `q.taylorComp p` has norm at
most `max 1 B ^ m` times the sum, over the ordered partitions `c` of `m`, of `‖q c.length‖`. -/
theorem FormalMultilinearSeries.norm_taylorComp_le (q : FormalMultilinearSeries 𝕜 F G)
    (p : FormalMultilinearSeries 𝕜 E F) {m : ℕ} {B : ℝ}
    (hp : ∀ k, 1 ≤ k → k ≤ m → ‖p k‖ ≤ B) :
    ‖q.taylorComp p m‖ ≤ max 1 B ^ m * ∑ c : OrderedFinpartition m, ‖q c.length‖ := by
  rw [Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun c _ ↦ ?_)
  refine (c.norm_compAlongOrderedFinpartition_le _ _).trans ?_
  rw [mul_comm (max 1 B ^ m)]
  gcongr
  calc ∏ i, ‖p (c.partSize i)‖ ≤ ∏ _i : Fin c.length, max 1 B := by
        gcongr with i
        exact (hp _ (c.partSize_pos i) (c.partSize_le i)).trans (le_max_right _ _)
    _ = max 1 B ^ c.length := by simp
    _ ≤ max 1 B ^ m := pow_le_pow_right₀ (le_max_left _ _) c.length_le

/-- **A norm bound for the derivatives of a composite.** If `g` is `Cᵐ` at `f x`, `f` is `Cᵐ` at
`x`, and the derivatives of `f` at `x` of orders `1` through `m` have norm at most `B`, then the
`m`-th derivative of `g ∘ f` at `x` has norm at most `max 1 B ^ m` times the sum, over the ordered
partitions `c` of `m`, of the norms of the derivatives of `g` at `f x` of order `c.length ≤ m`. -/
theorem ContDiffAt.norm_iteratedFDeriv_comp_le_sum {g : F → G} {f : E → F} {x : E} {m : ℕ}
    (hg : ContDiffAt 𝕜 m g (f x)) (hf : ContDiffAt 𝕜 m f x) {B : ℝ}
    (hB : ∀ k, 1 ≤ k → k ≤ m → ‖iteratedFDeriv 𝕜 k f x‖ ≤ B) :
    ‖iteratedFDeriv 𝕜 m (g ∘ f) x‖ ≤
      max 1 B ^ m * ∑ c : OrderedFinpartition m, ‖iteratedFDeriv 𝕜 c.length g (f x)‖ := by
  rw [iteratedFDeriv_comp hg hf le_rfl]
  exact FormalMultilinearSeries.norm_taylorComp_le _ _ hB
