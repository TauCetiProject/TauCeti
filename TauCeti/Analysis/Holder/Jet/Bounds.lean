/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.MetricSpace.Holder
public import TauCeti.Analysis.Calculus.IteratedFDeriv.Basic
public import TauCeti.Analysis.Calculus.IteratedFDeriv.CompContinuousLinearEquiv
public import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
public import Mathlib.Analysis.Calculus.ContDiff.Defs
import TauCeti.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-!
# Hölder bounds for local derivative fields

On an open convex set, a bound on the next derivative makes a derivative field Lipschitz
(`ContDiffOn.lipschitzOnWith_iteratedFDeriv`), so bounds for a derivative field and its next
derivative give a Hölder bound for every exponent at most one. Thus local `C^{k,α}` data need a
separate Hölder hypothesis only at their top derivative
(`ContDiffOn.holderOnWith_iteratedFDeriv_of_le`); on a convex set of small diameter `r` the
Hölder constant of a lower derivative field is `O(r^(1-α))`
(`ContDiffOn.holderOnWith_iteratedFDeriv_of_lt_of_dist_le`). On the whole space, a uniform bound
on the next derivative makes a derivative field Lipschitz
(`ContDiff.lipschitzWith_iteratedFDeriv`).
Currying preserves these bounds exactly. On an open set that need not be convex, a `C^1` map is
locally Lipschitz, hence Hölder on every compact subset, so one more derivative makes the top
derivative Hölder there.

`ContDiffOn.exists_ball_bounds_and_holderOnWith_iteratedFDeriv` gives common bounds and Hölder
constants for every derivative field of local `C^{n,α}` data on a positive ball, without an extra
derivative or finite-dimensional parameter assumption. Constant maps have zero Hölder constant at
every derivative order (`TauCeti.holderWith_iteratedFDeriv_const`), and adding a constant keeps
the Hölder constant (`TauCeti.holderOnWith_iteratedFDeriv_add_const`).
-/

public section

open Set Metric Filter
open scoped NNReal Topology

variable {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]

variable [NormedSpace ℝ E] [NormedSpace ℝ F]

namespace TauCeti

/-- Currying preserves the Hölder bound of the top derivative exactly. -/
theorem holderOnWith_iteratedFDeriv_succ_iff {f : E → F} {s : Set E} {j : ℕ}
    {H α : ℝ≥0} :
    HolderOnWith H α (iteratedFDeriv ℝ (j + 1) f) s ↔
      HolderOnWith H α (iteratedFDeriv ℝ j (fderiv ℝ f)) s := by
  simp only [holderOnWith_iff_dist_le, iteratedFDeriv_succ_eq_comp_right,
    Function.comp_apply, LinearIsometryEquiv.dist_map]

/-- The order-zero derivative field has the same Hölder constant as the original function. -/
theorem holderOnWith_iteratedFDeriv_zero_iff {f : E → F} {s : Set E} {H α : ℝ≥0} :
    HolderOnWith H α (iteratedFDeriv ℝ 0 f) s ↔ HolderOnWith H α f s := by
  simp only [holderOnWith_iff_dist_le, iteratedFDeriv_zero_eq_comp,
    Function.comp_apply, LinearIsometryEquiv.dist_map]

/-- The first derivative field has the same Hölder constant as the derivative. -/
theorem holderOnWith_iteratedFDeriv_one_iff {f : E → F} {s : Set E} {H α : ℝ≥0} :
    HolderOnWith H α (iteratedFDeriv ℝ 1 f) s ↔ HolderOnWith H α (fderiv ℝ f) s :=
  holderOnWith_iteratedFDeriv_succ_iff.trans holderOnWith_iteratedFDeriv_zero_iff

/-- On a convex open set, a derivative field below the top order whose next derivative is
bounded by `L` is `L`-Lipschitz. -/
theorem _root_.ContDiffOn.lipschitzOnWith_iteratedFDeriv {k j : ℕ} {s : Set E} {f : E → F}
    {L : ℝ≥0} (hf : ContDiffOn ℝ k f s) (hs : IsOpen s) (hconv : Convex ℝ s) (hj : j < k)
    (hnext : ∀ x ∈ s, ‖iteratedFDeriv ℝ (j + 1) f x‖ ≤ L) :
    LipschitzOnWith L (iteratedFDeriv ℝ j f) s := by
  have hdiff : ∀ x ∈ s, DifferentiableAt ℝ (iteratedFDeriv ℝ j f) x := fun x hx =>
    (hf.contDiffAt (hs.mem_nhds hx)).differentiableAt_iteratedFDeriv (by exact_mod_cast hj)
  have hder : ∀ x ∈ s, ‖fderiv ℝ (iteratedFDeriv ℝ j f) x‖₊ ≤ L := fun x hx ↦ by
    exact_mod_cast (norm_fderiv_iteratedFDeriv (𝕜 := ℝ) (f := f) (n := j) (x := x)) ▸ hnext x hx
  exact hconv.lipschitzOnWith_of_nnNorm_fderiv_le hdiff hder

/-- Every derivative field below the top order is Hölder, controlled by the uniform bound on
that field and its next derivative. No Hölder assumption on lower derivatives is needed. -/
theorem _root_.ContDiffOn.holderOnWith_iteratedFDeriv_of_lt {k j : ℕ} {s : Set E}
    {f : E → F} {M L α : ℝ≥0} (hf : ContDiffOn ℝ k f s) (hs : IsOpen s)
    (hconv : Convex ℝ s) (hj : j < k) (hα : α ≤ 1)
    (hb : ∀ x ∈ s, ‖iteratedFDeriv ℝ j f x‖ ≤ M)
    (hnext : ∀ x ∈ s, ‖iteratedFDeriv ℝ (j + 1) f x‖ ≤ L) :
    HolderOnWith (L + 2 * M) α (iteratedFDeriv ℝ j f) s :=
  (hf.lipschitzOnWith_iteratedFDeriv hs hconv hj hnext).holderOnWith_of_norm_le hb hα

/-- On a convex open set `s` whose points are at distance at most `r` from each other, a
derivative field below the top order whose next derivative is bounded by `L` is `α`-Hölder with
constant `L r ^ (1 - α)`, for `α ≤ 1`. For `α < 1` this constant tends to zero with `r`. -/
theorem _root_.ContDiffOn.holderOnWith_iteratedFDeriv_of_lt_of_dist_le {k j : ℕ} {s : Set E}
    {f : E → F} {L α r : ℝ≥0} (hf : ContDiffOn ℝ k f s) (hs : IsOpen s)
    (hconv : Convex ℝ s) (hj : j < k) (hα : α ≤ 1) (hr : ∀ x ∈ s, ∀ y ∈ s, dist x y ≤ r)
    (hnext : ∀ x ∈ s, ‖iteratedFDeriv ℝ (j + 1) f x‖ ≤ L) :
    HolderOnWith (L * r ^ (1 - (α : ℝ))) α (iteratedFDeriv ℝ j f) s := by
  simpa using (hf.lipschitzOnWith_iteratedFDeriv hs hconv hj hnext).holderOnWith.of_le
    (fun x hx y hy ↦ edist_le_coe.2 (hr x hx y hy)) hα

/-- On a convex open set, every derivative field through order `k` of a `C^k` map with
derivatives bounded by `M` and `k`-th derivative `α`-Hölder with constant `H` is `α`-Hölder with
constant `H + 3 M`. -/
theorem _root_.ContDiffOn.holderOnWith_iteratedFDeriv_of_le {k j : ℕ} {s : Set E}
    {f : E → F} {M H α : ℝ≥0} (hf : ContDiffOn ℝ k f s) (hs : IsOpen s)
    (hconv : Convex ℝ s) (hj : j ≤ k) (hα : α ≤ 1)
    (hb : ∀ i ≤ k, ∀ x ∈ s, ‖iteratedFDeriv ℝ i f x‖ ≤ M)
    (hH : HolderOnWith H α (iteratedFDeriv ℝ k f) s) :
    HolderOnWith (H + 3 * M) α (iteratedFDeriv ℝ j f) s := by
  rcases hj.eq_or_lt with rfl | hj
  · exact hH.mono_const le_self_add
  · have hlow := hf.holderOnWith_iteratedFDeriv_of_lt hs hconv hj hα
      (hb j hj.le) (hb (j + 1) (by omega))
    have hconstant : M + 2 * M = 3 * M := by ring
    rw [hconstant] at hlow
    exact hlow.mono_const le_add_self

/-- Every derivative field through order `k` of a `C^{k+1}` map whose derivatives through order
`k + 1` are bounded by `N` everywhere is `α`-Hölder with constant `3 N`. -/
theorem _root_.ContDiff.holderWith_iteratedFDeriv_of_le {k j : ℕ} {f : E → F} {N α : ℝ≥0}
    (hf : ContDiff ℝ (k + 1) f) (hj : j ≤ k) (hα : α ≤ 1)
    (hb : ∀ i ≤ k + 1, ∀ x, ‖iteratedFDeriv ℝ i f x‖ ≤ N) :
    HolderWith (3 * N) α (iteratedFDeriv ℝ j f) := by
  have hlow := hf.contDiffOn.holderOnWith_iteratedFDeriv_of_lt (k := k + 1)
    isOpen_univ convex_univ (by omega : j < k + 1) hα
    (fun x _ => hb j (by omega) x) (fun x _ => hb (j + 1) (by omega) x)
  convert holderOnWith_univ.mp hlow using 1
  ring

/-- A derivative field below the top order whose next derivative is bounded by `L` everywhere is
`L`-Lipschitz. -/
theorem _root_.ContDiff.lipschitzWith_iteratedFDeriv {k j : ℕ} {f : E → F} {L : ℝ≥0}
    (hf : ContDiff ℝ k f) (hj : j < k) (hnext : ∀ x, ‖iteratedFDeriv ℝ (j + 1) f x‖ ≤ L) :
    LipschitzWith L (iteratedFDeriv ℝ j f) :=
  lipschitzWith_of_nnNorm_fderiv_le (hf.differentiable_iteratedFDeriv (by exact_mod_cast hj))
    fun x ↦ by
      have h := hnext x
      rw [← norm_fderiv_iteratedFDeriv] at h
      exact_mod_cast h

/-- A map of class `C^1` on an open set `s` is locally Lipschitz on `s`. Compare Mathlib's
`ContDiffOn.locallyLipschitzOn`, which assumes `s` convex instead of open. -/
theorem _root_.ContDiffOn.locallyLipschitzOn_of_isOpen {𝕂 E' F' : Type*} [RCLike 𝕂]
    [NormedAddCommGroup E'] [NormedSpace 𝕂 E'] [NormedAddCommGroup F'] [NormedSpace 𝕂 F']
    {s : Set E'} {g : E' → F'} (hg : ContDiffOn 𝕂 1 g s) (hs : IsOpen s) :
    LocallyLipschitzOn s g := by
  intro x hx
  obtain ⟨L, t, ht, hLt⟩ := (hg.contDiffAt (hs.mem_nhds hx)).exists_lipschitzOnWith
  exact ⟨L, t, mem_nhdsWithin_of_mem_nhds ht, hLt⟩

/-- A map of class `C^1` on an open set `s` is `α`-Hölder on each compact subset of `s`, for every
`α ≤ 1`. Compare `ContDiffOn.exists_holderOnWith`, for a compact convex set. -/
theorem _root_.ContDiffOn.exists_holderOnWith_of_isOpen {𝕂 E' F' : Type*} [RCLike 𝕂]
    [NormedAddCommGroup E'] [NormedSpace 𝕂 E'] [NormedAddCommGroup F'] [NormedSpace 𝕂 F']
    {s K : Set E'} {g : E' → F'} {α : ℝ≥0} (hg : ContDiffOn 𝕂 1 g s) (hs : IsOpen s)
    (hα : α ≤ 1) (hK : IsCompact K) (hKs : K ⊆ s) : ∃ C, HolderOnWith C α g K :=
  (hg.locallyLipschitzOn_of_isOpen hs).exists_holderOnWith_of_isCompact hα hK hKs

/-- For a map of class `C^{k+1}` on an open set `s`, the `k`-th derivative is `α`-Hölder on each
compact subset of `s`, for every `α ≤ 1`. -/
theorem _root_.ContDiffOn.exists_holderOnWith_iteratedFDeriv {𝕂 E' F' : Type*} [RCLike 𝕂]
    [NormedAddCommGroup E'] [NormedSpace 𝕂 E'] [NormedAddCommGroup F'] [NormedSpace 𝕂 F']
    {k : ℕ} {s K : Set E'} {f : E' → F'} {α : ℝ≥0} (hf : ContDiffOn 𝕂 (k + 1) f s)
    (hs : IsOpen s) (hα : α ≤ 1) (hK : IsCompact K) (hKs : K ⊆ s) :
    ∃ C, HolderOnWith C α (iteratedFDeriv 𝕂 k f) K :=
  ContDiffOn.exists_holderOnWith_of_isOpen (fun _ hx ↦
    ((hf.contDiffAt (hs.mem_nhds hx)).iteratedFDeriv_right (add_comm _ _).le).contDiffWithinAt)
    hs hα hK hKs

/-- Every derivative field of a constant map is Hölder with constant zero, at every order
and exponent. -/
theorem holderWith_iteratedFDeriv_const {𝕜 : Type u𝕜} {E' : Type uE} {F' : Type uF}
    [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] [NormedAddCommGroup F'] [NormedSpace 𝕜 F']
    (n : ℕ) (α : ℝ≥0) (v : F') :
    HolderWith 0 α (iteratedFDeriv 𝕜 n (fun _ : E' ↦ v)) := by
  cases n with
  | zero =>
    simp only [iteratedFDeriv_zero_eq_comp, Function.comp_def]
    exact HolderWith.const
  | succ n =>
    rw [iteratedFDeriv_succ_const]
    exact HolderWith.zero

/-- Local `C^{n,α}` data have common bounded and Hölder derivative fields through order `n`
on a positive ball. No compactness of the parameter space or extra derivative is required. -/
theorem _root_.ContDiffOn.exists_ball_bounds_and_holderOnWith_iteratedFDeriv
    {P : Type uP} {V : Type uV} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup V] [NormedSpace ℝ V] {f : P → V} {s : Set P} {a : P}
    {n : ℕ} {α C : ℝ≥0} (hf : ContDiffOn ℝ n f s) (hs : s ∈ 𝓝 a)
    (hα : α ≤ 1) (hH : HolderOnWith C α (iteratedFDeriv ℝ n f) s) :
    ∃ r > 0, ball a r ⊆ s ∧ ∃ M H : ℝ≥0,
      (∀ j ≤ n, ∀ x ∈ ball a r, ‖iteratedFDeriv ℝ j f x‖ ≤ M) ∧
      ∀ j ≤ n, HolderOnWith H α (iteratedFDeriv ℝ j f) (ball a r) := by
  obtain ⟨r, hr, A, hA⟩ := (hf.contDiffAt hs).exists_ball_bound_iteratedFDeriv
  obtain ⟨ρ, hρ, hρs⟩ := Metric.eventually_nhds_iff_ball.mp
    (Filter.Eventually.and (ball_mem_nhds a hr) hs)
  have hrs : ball a ρ ⊆ s := fun x hx ↦ (hρs x hx).2
  have hbound : ∀ j ≤ n, ∀ x ∈ ball a ρ, ‖iteratedFDeriv ℝ j f x‖ ≤ A.toNNReal := by
    intro j hj x hx
    exact (hA j hj x (hρs x hx).1).trans (Real.le_coe_toNNReal A)
  refine ⟨ρ, hρ, hrs, A.toNNReal, max C (3 * A.toNNReal), hbound, fun j hj ↦ ?_⟩
  rcases hj.lt_or_eq with hj | rfl
  · have h := (hf.mono hrs).holderOnWith_iteratedFDeriv_of_lt isOpen_ball (convex_ball a ρ)
      hj hα (hbound j hj.le) (hbound (j + 1) hj)
    apply h.mono_const
    calc A.toNNReal + 2 * A.toNNReal = 3 * A.toNNReal := by ring
         _ ≤ max C (3 * A.toNNReal) := le_max_right _ _
  · exact (hH.mono hrs).mono_const (le_max_left _ _)

/-- Adding a constant keeps a Hölder bound on a derivative field: at order zero the distances are
unchanged, and at positive order the derivative field itself is unchanged. -/
theorem holderOnWith_iteratedFDeriv_add_const {f : E → F} {s : Set E} {n : ℕ} {C α : ℝ≥0}
    (y : F) (h : HolderOnWith C α (iteratedFDeriv ℝ n f) s) :
    HolderOnWith C α (iteratedFDeriv ℝ n fun x ↦ f x + y) s := by
  rcases n with _ | n
  · rw [holderOnWith_iteratedFDeriv_zero_iff] at h ⊢
    intro a ha b hb
    simpa only [edist_add_right] using h a ha b hb
  · rwa [iteratedFDeriv_succ_add_const]

end TauCeti
