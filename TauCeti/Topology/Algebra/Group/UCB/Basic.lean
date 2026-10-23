/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Monoid.Submonoid
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Order.Lattice
public import Mathlib.Topology.Algebra.IsUniformGroup.Defs
public import Mathlib.Topology.ContinuousMap.Bounded.Normed

/-!
# Bounded functions uniformly continuous under small left multiplication

For a topological group `G`, `TauCeti.ucb G` is the subalgebra of real bounded continuous
functions `f` such that `f (u * x)` is uniformly close to `f x` for all `u` near `1`:

```text
∀ ε > 0,  ∀ᶠ u in 𝓝 1,  ∀ x,  |f (u * x) - f x| < ε.
```

`TauCeti.UCB G` is the corresponding type. It inherits the supremum norm, the unital algebra
structure and the pointwise order of `G →ᵇ ℝ`, and it is a lattice for the pointwise maximum and
minimum. This is the function space on which invariant means of a topological group are defined.

No separation, local compactness or countability hypothesis on `G` is used. Bekka, de la Harpe and
Valette call this condition *left* uniform continuity, while it is uniform continuity for Mathlib's
*right* uniformity `IsTopologicalGroup.rightUniformSpace`, whose entourages compare `(x, y)` through
`y * x⁻¹`; the formula, not the label, is authoritative. The left and right uniformities of a
general group can differ, so no `IsUniformGroup` structure is used.

## Main definitions

* `TauCeti.ucbSubalgebra 𝕜 G`: the subalgebra of `G →ᵇ 𝕜` defined by the same condition with
  `‖·‖` in place of `|·|`, for a normed field `𝕜`.
* `TauCeti.ucb G`: the subalgebra of `G →ᵇ ℝ` defined by the condition above, the case `𝕜 = ℝ`.
* `TauCeti.UCB G`: its carrier type, a real Banach algebra and lattice.

## Main results

* `TauCeti.mem_ucb_iff_tendsto`: the condition says that the left-multiplication orbit
  `u ↦ f (u * ·)` tends to `f` in supremum norm as `u → 1`.
* `TauCeti.mem_ucb_iff_uniformContinuous`: the condition is uniform continuity for the right
  uniformity of `G`.
* `TauCeti.isClosed_ucb`: `ucb G` is closed under uniform limits, so `UCB G` is complete.
* `TauCeti.sup_mem_ucb`, `TauCeti.inf_mem_ucb`, `TauCeti.abs_mem_ucb`: closure under the lattice
  operations.

## References

* B. Bekka, P. de la Harpe, A. Valette, *Kazhdan's Property (T)*, Appendix A.3 and
  Definition G.1.4.
-/

public section

noncomputable section

open Filter Topology
open scoped BoundedContinuousFunction

namespace BoundedContinuousFunction

variable {M β : Type*} [MulOneClass M] [TopologicalSpace M] [SeparatelyContinuousMul M]
  [PseudoMetricSpace β]

/-- The left-multiplication orbit `u ↦ f (u * ·)` of a bounded continuous function tends to `f`
in supremum distance as `u → 1` exactly when `f (u * x)` is uniformly close to `f x` for all `u`
near `1`. -/
@[to_additive /-- The left-addition orbit `u ↦ f (u + ·)` of a bounded continuous function tends
to `f` in supremum distance as `u → 0` exactly when `f (u + x)` is uniformly close to `f x` for all
`u` near `0`. -/]
theorem tendsto_compContinuous_mulLeft_iff (f : M →ᵇ β) :
    Tendsto (fun u => f.compContinuous (ContinuousMap.mulLeft u)) (𝓝 1) (𝓝 f) ↔
      ∀ ε > 0, ∀ᶠ u in 𝓝 (1 : M), ∀ x, dist (f (u * x)) (f x) < ε := by
  rw [Metric.tendsto_nhds]
  refine ⟨fun h ε hε => ?_, fun h ε hε => ?_⟩
  · filter_upwards [h ε hε] with u hu x
    exact (dist_coe_le_dist x).trans_lt hu
  · filter_upwards [h (ε / 2) (half_pos hε)] with u hu
    exact ((dist_le (half_pos hε).le).2 fun x => (hu x).le).trans_lt (half_lt_self hε)

end BoundedContinuousFunction

namespace TauCeti

variable {𝕜 G : Type*} [NormedField 𝕜] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

section UniformContinuous

variable {β : Type*} [PseudoMetricSpace β]

/-- A function on a topological group is uniformly continuous for the right uniformity exactly
when `f (u * x)` is uniformly close to `f x` for all `u` near `1`. -/
theorem uniformContinuous_rightUniformSpace_iff (f : G → β) :
    (letI : UniformSpace G := IsTopologicalGroup.rightUniformSpace G
     UniformContinuous f) ↔
      ∀ ε > 0, ∀ᶠ u in 𝓝 (1 : G), ∀ x, dist (f (u * x)) (f x) < ε := by
  let : UniformSpace G := IsTopologicalGroup.rightUniformSpace G
  rw [UniformContinuous, uniformity_eq_comap_nhds_one',
    ((𝓝 (1 : G)).basis_sets.comap _).tendsto_iff Metric.uniformity_basis_dist]
  refine forall₂_congr fun ε _ => ⟨fun ⟨U, hU, h⟩ => ?_, fun h => ?_⟩
  · filter_upwards [hU] with u hu x
    rw [dist_comm]
    exact h (x, u * x) (by simpa using hu)
  · refine ⟨_, h, fun p hp => ?_⟩
    simpa [dist_comm] using hp p.1

/-- A function on a topological group whose values `f (u * x)` are uniformly close to `f x` for
all `u` near `1` is continuous. -/
theorem continuous_of_forall_eventually_dist_mul_lt {f : G → β}
    (h : ∀ ε > 0, ∀ᶠ u in 𝓝 (1 : G), ∀ x, dist (f (u * x)) (f x) < ε) : Continuous f :=
  letI : UniformSpace G := IsTopologicalGroup.rightUniformSpace G
  ((uniformContinuous_rightUniformSpace_iff f).2 h).continuous

end UniformContinuous

section UCB

variable (𝕜 G) in
/-- The bounded continuous functions `f : G →ᵇ 𝕜` such that `f (u * x)` is uniformly close to
`f x` for all `u` near `1`, as a subalgebra of `G →ᵇ 𝕜`. The real space `ucb G` is the case
`𝕜 = ℝ`. -/
def ucbSubalgebra : Subalgebra 𝕜 (G →ᵇ 𝕜) where
  carrier := {f | ∀ ε > 0, ∀ᶠ u in 𝓝 (1 : G), ∀ x, ‖f (u * x) - f x‖ < ε}
  mul_mem' {f g} hf hg := by
    simp only [Set.mem_ofPred_eq, ← dist_eq_norm,
      ← BoundedContinuousFunction.tendsto_compContinuous_mulLeft_iff] at hf hg ⊢
    exact hf.mul hg
  add_mem' {f g} hf hg := by
    simp only [Set.mem_ofPred_eq, ← dist_eq_norm,
      ← BoundedContinuousFunction.tendsto_compContinuous_mulLeft_iff] at hf hg ⊢
    exact hf.add hg
  algebraMap_mem' c := by
    simp only [Set.mem_ofPred_eq, ← dist_eq_norm,
      ← BoundedContinuousFunction.tendsto_compContinuous_mulLeft_iff]
    exact tendsto_const_nhds

/-- The defining condition of `ucbSubalgebra 𝕜 G`. -/
theorem mem_ucbSubalgebra_iff {f : G →ᵇ 𝕜} :
    f ∈ ucbSubalgebra 𝕜 G ↔ ∀ ε > 0, ∀ᶠ u in 𝓝 (1 : G), ∀ x, ‖f (u * x) - f x‖ < ε :=
  Iff.rfl

/-- Membership in `ucbSubalgebra 𝕜 G` says that `u ↦ f (u * ·)` tends to `f` in supremum norm as
`u → 1`. -/
theorem mem_ucbSubalgebra_iff_tendsto {f : G →ᵇ 𝕜} :
    f ∈ ucbSubalgebra 𝕜 G ↔
      Tendsto (fun u => f.compContinuous (ContinuousMap.mulLeft u)) (𝓝 1) (𝓝 f) := by
  simp only [mem_ucbSubalgebra_iff, ← dist_eq_norm,
    BoundedContinuousFunction.tendsto_compContinuous_mulLeft_iff]

variable (G) in
/-- The real bounded continuous functions `f` on `G` such that `f (u * x)` is uniformly close to
`f x` for all `u` near `1`, as a subalgebra of `G →ᵇ ℝ`. -/
def ucb : Subalgebra ℝ (G →ᵇ ℝ) :=
  ucbSubalgebra ℝ G

variable (G) in
/-- The real Banach algebra of bounded functions on `G` that are uniformly continuous under small
left multiplication, with the supremum norm, algebra operations and order of `G →ᵇ ℝ`. -/
abbrev UCB : Type _ := ucb G

/-- The defining condition of `ucb G`. -/
theorem mem_ucb_iff {f : G →ᵇ ℝ} :
    f ∈ ucb G ↔ ∀ ε > 0, ∀ᶠ u in 𝓝 (1 : G), ∀ x, |f (u * x) - f x| < ε := by
  simp only [ucb, mem_ucbSubalgebra_iff, Real.norm_eq_abs]

/-- Membership in `ucb G` says that `u ↦ f (u * ·)` tends to `f` in supremum norm as `u → 1`. -/
theorem mem_ucb_iff_tendsto {f : G →ᵇ ℝ} :
    f ∈ ucb G ↔ Tendsto (fun u => f.compContinuous (ContinuousMap.mulLeft u)) (𝓝 1) (𝓝 f) :=
  mem_ucbSubalgebra_iff_tendsto

/-- Membership in `ucb G` is uniform continuity for the right uniformity of `G`. -/
theorem mem_ucb_iff_uniformContinuous {f : G →ᵇ ℝ} :
    f ∈ ucb G ↔
      (letI : UniformSpace G := IsTopologicalGroup.rightUniformSpace G
       UniformContinuous f) := by
  simp only [mem_ucb_iff, ← Real.dist_eq, uniformContinuous_rightUniformSpace_iff]

/-- `ucb G` is closed in `G →ᵇ ℝ`: a uniform limit of functions in `ucb G` lies in `ucb G`. -/
theorem isClosed_ucb : IsClosed (ucb G : Set (G →ᵇ ℝ)) := by
  refine isClosed_of_closure_subset fun f hf ε hε => ?_
  obtain ⟨g, hg, hfg⟩ := Metric.mem_closure_iff.1 hf (ε / 3) (by positivity)
  filter_upwards [hg (ε / 3) (by positivity)] with u hu x
  simp only [← dist_eq_norm] at hu ⊢
  calc dist (f (u * x)) (f x)
      ≤ dist (f (u * x)) (g (u * x)) + dist (g (u * x)) (g x) + dist (g x) (f x) :=
        dist_triangle4 _ _ _ _
    _ < ε / 3 + ε / 3 + ε / 3 := by
        gcongr
        · exact (BoundedContinuousFunction.dist_coe_le_dist _).trans_lt hfg
        · exact hu x
        · exact (BoundedContinuousFunction.dist_coe_le_dist _).trans_lt (by rwa [dist_comm])
    _ = ε := by ring

/-- `UCB G` is a real normed group for the supremum norm of `G →ᵇ ℝ`. This inherited instance is
restated so that typeclass search finds it directly when `UCB G` occurs inside another type, such
as the continuous dual `UCB G →L[ℝ] ℝ`; the search through `Subalgebra` and `G →ᵇ ℝ` fails
there. -/
instance : NormedAddCommGroup (UCB G) :=
  inferInstance

/-- `UCB G` is a real Banach space. -/
instance : CompleteSpace (UCB G) :=
  isClosed_ucb.completeSpace_coe

/-- Constant functions belong to `ucb G`. -/
@[simp]
theorem const_mem_ucb (c : ℝ) : BoundedContinuousFunction.const G c ∈ ucb G :=
  fun ε hε => .of_forall fun _ _ => by simpa using hε

/-- `ucb G` is closed under the pointwise maximum. -/
theorem sup_mem_ucb {f g : G →ᵇ ℝ} (hf : f ∈ ucb G) (hg : g ∈ ucb G) : f ⊔ g ∈ ucb G := by
  rw [mem_ucb_iff_tendsto] at hf hg ⊢
  exact hf.sup_nhds hg

/-- `ucb G` is closed under the pointwise minimum. -/
theorem inf_mem_ucb {f g : G →ᵇ ℝ} (hf : f ∈ ucb G) (hg : g ∈ ucb G) : f ⊓ g ∈ ucb G := by
  rw [mem_ucb_iff_tendsto] at hf hg ⊢
  exact hf.inf_nhds hg

/-- `ucb G` is closed under the pointwise absolute value. -/
theorem abs_mem_ucb {f : G →ᵇ ℝ} (hf : f ∈ ucb G) : |f| ∈ ucb G :=
  sup_mem_ucb hf (neg_mem hf)

/-- `UCB G` is a lattice for the pointwise maximum and minimum. -/
instance : Lattice (UCB G) :=
  Subtype.lattice (fun _ _ => sup_mem_ucb) (fun _ _ => inf_mem_ucb)

/-- The supremum norm of `UCB G` is solid for its pointwise order, as in `G →ᵇ ℝ`. -/
instance : HasSolidNorm (UCB G) where
  solid _ _ h := HasSolidNorm.solid (α := G →ᵇ ℝ) h

namespace UCB

@[simp, norm_cast]
theorem coe_sup (f g : UCB G) : ((f ⊔ g : UCB G) : G →ᵇ ℝ) = (f : G →ᵇ ℝ) ⊔ (g : G →ᵇ ℝ) :=
  rfl

@[simp, norm_cast]
theorem coe_inf (f g : UCB G) : ((f ⊓ g : UCB G) : G →ᵇ ℝ) = (f : G →ᵇ ℝ) ⊓ (g : G →ᵇ ℝ) :=
  rfl

@[simp, norm_cast]
theorem coe_abs (f : UCB G) : ((|f| : UCB G) : G →ᵇ ℝ) = |(f : G →ᵇ ℝ)| :=
  rfl

/-- Two elements of `UCB G` are equal when they agree at every point. -/
@[ext]
theorem ext {f g : UCB G} (h : ∀ x, (f : G →ᵇ ℝ) x = (g : G →ᵇ ℝ) x) : f = g :=
  Subtype.ext (BoundedContinuousFunction.ext h)

/-- The order on `UCB G` is the pointwise order. -/
theorem le_def {f g : UCB G} : f ≤ g ↔ ∀ x, (f : G →ᵇ ℝ) x ≤ (g : G →ᵇ ℝ) x :=
  Iff.rfl

/-- Each value of an element of `UCB G` is bounded by its supremum norm. -/
theorem abs_apply_le_norm (f : UCB G) (x : G) : |(f : G →ᵇ ℝ) x| ≤ ‖f‖ :=
  (f : G →ᵇ ℝ).norm_coe_le_norm x

/-- Every element of `UCB G` lies below the constant function with value its supremum norm. -/
theorem le_norm_smul_one (f : UCB G) : f ≤ ‖f‖ • 1 :=
  le_def.2 fun x => by simpa using (f : G →ᵇ ℝ).apply_le_norm x

end UCB

end UCB

end TauCeti
