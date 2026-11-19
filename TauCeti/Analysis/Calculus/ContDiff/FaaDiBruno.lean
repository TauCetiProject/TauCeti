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

The same expansion shows that the `m`-th derivative of `g ∘ f` at `x` depends only on the
derivatives of `g` at `f x` and of `f` at `x` of order at most `m`
(`ContDiffAt.iteratedFDeriv_comp_congr`). Consequently the derivatives of `y ↦ g (y, s (h y))` up
to order `r` depend only on those of `s` up to order `r`
(`ContDiffAt.iteratedFDeriv_graph_comp_congr`), which makes jets of sections independent of
bundle coordinates.
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

/-- The `m`-th coefficient of the Taylor composition `q.taylorComp p` depends only on the
coefficients of `q` of order at most `m` and of `p` of orders `1` through `m`. -/
theorem FormalMultilinearSeries.taylorComp_congr {q₁ q₂ : FormalMultilinearSeries 𝕜 F G}
    {p₁ p₂ : FormalMultilinearSeries 𝕜 E F} {m : ℕ} (hq : ∀ k ≤ m, q₁ k = q₂ k)
    (hp : ∀ k, 1 ≤ k → k ≤ m → p₁ k = p₂ k) :
    q₁.taylorComp p₁ m = q₂.taylorComp p₂ m := by
  refine Finset.sum_congr rfl fun c _ ↦ ?_
  simp only [FormalMultilinearSeries.compAlongOrderedFinpartition, hq c.length c.length_le,
    fun i ↦ hp _ (c.partSize_pos i) (c.partSize_le i)]

/-- **Locality of the derivatives of a composite.** The `m`-th derivative of `g ∘ f` at `x` depends
only on the derivatives of `g` at `f x` of order at most `m` and on those of `f` at `x` of orders
`1` through `m`. -/
theorem ContDiffAt.iteratedFDeriv_comp_congr {g₁ g₂ : F → G} {f₁ f₂ : E → F} {x₁ x₂ : E}
    {m : ℕ}
    (hg₁ : ContDiffAt 𝕜 m g₁ (f₁ x₁)) (hf₁ : ContDiffAt 𝕜 m f₁ x₁)
    (hg₂ : ContDiffAt 𝕜 m g₂ (f₂ x₂)) (hf₂ : ContDiffAt 𝕜 m f₂ x₂)
    (hg : ∀ k ≤ m, iteratedFDeriv 𝕜 k g₁ (f₁ x₁) = iteratedFDeriv 𝕜 k g₂ (f₂ x₂))
    (hf : ∀ k, 1 ≤ k → k ≤ m → iteratedFDeriv 𝕜 k f₁ x₁ = iteratedFDeriv 𝕜 k f₂ x₂) :
    iteratedFDeriv 𝕜 m (g₁ ∘ f₁) x₁ = iteratedFDeriv 𝕜 m (g₂ ∘ f₂) x₂ := by
  rw [iteratedFDeriv_comp hg₁ hf₁ le_rfl, iteratedFDeriv_comp hg₂ hf₂ le_rfl]
  exact FormalMultilinearSeries.taylorComp_congr hg hf

/-- The iterated derivatives of `y ↦ g (y, s (h y))` at `x` up to order `r` depend only on those
of `s` at `h x`: transforming a section `s` by a base change `h` and a base-dependent fibre map
`g` is well defined on jets of sections. -/
theorem ContDiffAt.iteratedFDeriv_graph_comp_congr {H : Type*} [NormedAddCommGroup H]
    [NormedSpace 𝕜 H] {r : ℕ} {x : E} {h : E → F} {g : E × H → G} {s t : F → H}
    (hh : ContDiffAt 𝕜 r h x) (hg : ContDiffAt 𝕜 r g (x, s (h x)))
    (hs : ContDiffAt 𝕜 r s (h x)) (ht : ContDiffAt 𝕜 r t (h x))
    (hst : ∀ k ≤ r, iteratedFDeriv 𝕜 k s (h x) = iteratedFDeriv 𝕜 k t (h x)) {k : ℕ}
    (hk : k ≤ r) :
    iteratedFDeriv 𝕜 k (fun y ↦ g (y, s (h y))) x =
      iteratedFDeriv 𝕜 k (fun y ↦ g (y, t (h y))) x := by
  have hv : s (h x) = t (h x) := by
    simpa using congrArg (fun m ↦ m Fin.elim0) (hst 0 (Nat.zero_le r))
  have hcast {i : ℕ} (hi : i ≤ r) : (i : WithTop ℕ∞) ≤ r := by exact_mod_cast hi
  -- First the jets of `s ∘ h` and `t ∘ h` agree, then those of the graphs `y ↦ (y, s (h y))`.
  have hcomp (i : ℕ) (hi : i ≤ r) :
      iteratedFDeriv 𝕜 i (s ∘ h) x = iteratedFDeriv 𝕜 i (t ∘ h) x :=
    ContDiffAt.iteratedFDeriv_comp_congr ((hs.of_le (hcast hi))) (hh.of_le (hcast hi))
      (ht.of_le (hcast hi)) (hh.of_le (hcast hi)) (fun l hl ↦ hst l (hl.trans hi))
      (fun _ _ _ ↦ rfl)
  have hgraph (i : ℕ) (hi : i ≤ r) :
      iteratedFDeriv 𝕜 i (fun y ↦ (y, (s ∘ h) y)) x =
        iteratedFDeriv 𝕜 i (fun y ↦ (y, (t ∘ h) y)) x := by
    rw [iteratedFDeriv_prodMk (f := fun y ↦ y) contDiffAt_id (hs.comp x hh) (hcast hi),
      iteratedFDeriv_prodMk (f := fun y ↦ y) contDiffAt_id (ht.comp x hh) (hcast hi), hcomp i hi]
  have hg' : ContDiffAt 𝕜 r g (x, t (h x)) := hv ▸ hg
  exact ContDiffAt.iteratedFDeriv_comp_congr (f₁ := fun y ↦ (y, (s ∘ h) y))
    (f₂ := fun y ↦ (y, (t ∘ h) y)) (hg.of_le (hcast hk))
    ((contDiffAt_id.prodMk (hs.comp x hh)).of_le (hcast hk)) (hg'.of_le (hcast hk))
    ((contDiffAt_id.prodMk (ht.comp x hh)).of_le (hcast hk))
    (fun l _ ↦ by simp only [Function.comp_apply, hv]) fun l _ hl ↦ hgraph l (hl.trans hk)
