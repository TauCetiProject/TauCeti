/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Complex.Pseudoconvex.Strong
public import TauCeti.Geometry.Manifold.Complex.SquaredDistance
public import TauCeti.Geometry.Manifold.Morse.CriticalPoints
public import TauCeti.Geometry.Manifold.Morse.Generic.Strong
import TauCeti.Algebra.Order.Group.Bounds
import TauCeti.Topology.Maps.Proper.Basic
import TauCeti.Topology.Maps.Proper.Metric

/-!
# Morse approximation of pseudoconvex functions and exhaustions

On a complex manifold `M` of complex dimension `n`, strong `q`-pseudoconvexity everywhere is open
in the strong Whitney topology on `C²` jets
(`TauCeti.exists_strongCkControl_isManifoldStronglyPseudoconvexAt`), while Morse functions are
dense in the strong Whitney topology (`ContMDiffMap.exists_isMorse_mem_ball_sub_compl`). Combining
the order-two positivity control with any prescribed strong `C^k` control via
`ContMDiffMap.StrongCkControl.sup` produces smooth Morse approximations that simultaneously stay in
the prescribed strong `C^k` ball, satisfy a prescribed continuous positive `C⁰` error bound, agree
with the original function near any closed set on a neighbourhood of which it is already Morse, and
remain globally strongly `q`-pseudoconvex so that every critical point has real Morse index at most
`n + q`.

For a proper function `f`, relative proper Morse approximation
(`ContMDiffMap.exists_isMorse_isProperMap_mem_ball_sub_compl`) preserves properness within uniform
`C⁰` distance `1` in every strong `C^k` ball, with no separate sigma-compactness hypothesis on `M`
needed because a proper map into `ℝ` already makes `M` sigma-compact
(`IsProperMap.sigmaCompactSpace`). When `f` is moreover bounded below — a smooth strongly
`q`-pseudoconvex exhaustion — the perturbed function `g` is again proper, bounded below, globally
strongly `q`-pseudoconvex, and Morse with all critical indices at most `n + q`, and satisfies
`|g - f| < 1` everywhere (agreeing with `f` near `C` in the relative form).

Specializing to `q = 0` yields the corresponding statements for strictly plurisubharmonic functions
and exhaustions, with real Morse indices bounded by `n`. In particular, along any smooth proper
holomorphic immersion `i : M → F` into a proper complex inner product space and for any fixed
centre `a : F`, the squared distance `x ↦ ‖i x - a‖²` is perturbed within `C⁰` error `1` into a
proper bounded-below strictly plurisubharmonic Morse exhaustion of `M` without varying the centre
`a` or avoiding a focal set.

This file also records the `C²` critical-point counting consequences of strong `q`-pseudoconvexity:
`TauCeti.criticalCount` vanishes in degrees above `n + q`, and the counts in degrees
`0, …, n + q` sum to `TauCeti.totalCriticalCount`.

## Main results

* `TauCeti.criticalCount_eq_zero_of_isManifoldStronglyPseudoconvexAt` and
  `TauCeti.sum_criticalCount_eq_totalCriticalCount_of_isManifoldStronglyPseudoconvexAt`: a real
  `C²` function strongly `q`-pseudoconvex at its critical points has no critical points of index
  above `dim_ℂ E + q`, and its critical counts up to `dim_ℂ E + q` sum to the total critical count.
* `ContMDiffMap.exists_isMorse_isManifoldStronglyPseudoconvexAt_mem_ball_sub_compl` and
  `ContMDiffMap.exists_isMorse_isManifoldStronglyPseudoconvexAt_mem_ball`: relative and global
  strong-Whitney Morse approximation of smooth strongly `q`-pseudoconvex functions.
* `ContMDiffMap.exists_isMorse_isProperMap_isManifoldStronglyPseudoconvexAt_mem_ball_sub_compl` and
  `ContMDiffMap.exists_isMorse_isProperMap_isManifoldStronglyPseudoconvexAt_mem_ball`: proper
  strong-Whitney Morse approximation within `C⁰` distance `1`, without assuming sigma-compactness
  separately.
* `TauCeti.exists_isMorse_isProperMap_bddBelow_isManifoldStronglyPseudoconvexAt_sub_compl` and
  `TauCeti.exists_isMorse_isProperMap_bddBelow_isManifoldStronglyPseudoconvexAt`: relative and
  global Morse perturbation of a smooth proper bounded-below strongly `q`-pseudoconvex exhaustion.
* `ContMDiffMap.exists_isMorse_isManifoldStrictlyPlurisubharmonicAt_mem_ball_sub_compl`,
  `ContMDiffMap.exists_isMorse_isProperMap_isManifoldStrictlyPlurisubharmonicAt_mem_ball_sub_compl`,
  and `TauCeti.exists_isMorse_isProperMap_bddBelow_isManifoldStrictlyPlurisubharmonicAt_sub_compl`:
  the strictly plurisubharmonic (`q = 0`) counterparts, together with their global specializations.
* `TauCeti.exists_isMorse_isProperMap_isManifoldStrictlyPlurisubharmonicAt_norm_sq_sub_comp`:
  proper bounded-below strictly plurisubharmonic Morse perturbation of squared distance along any
  smooth proper holomorphic immersion at a fixed centre.

## References

* R. Hain, *Notes on the Morse theory of complex manifolds*, Section 2.
* M. Hirsch, *Differential Topology*, Graduate Texts in Mathematics 33, Springer, 1976, Chapter 2,
  §1, and Chapter 6, §1.
* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  §§6–7.
-/

public section

open Function Module Set Topology
open scoped ContDiff Manifold TauCeti.ManifoldStrongWhitney

universe u

namespace TauCeti

section CriticalCount

variable {E : Type*} {M : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [FiniteDimensional ℂ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) 2 M]
  {f : M → ℝ}

/-- A real `C²` function on a complex manifold of complex dimension `n` which is strongly
`q`-pseudoconvex at each of its critical points has no critical points of real Morse index larger
than `n + q`. -/
theorem criticalCount_eq_zero_of_isManifoldStronglyPseudoconvexAt {q j : ℕ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) 2 f)
    (hq : ∀ x ∈ criticalPoints 𝓘(ℝ, E) f, IsManifoldStronglyPseudoconvexAt E q f x)
    (hj : finrank ℂ E + q < j) :
    criticalCount 𝓘(ℝ, E) f j = 0 := by
  rw [criticalCount_def, encard_eq_zero, eq_empty_iff_forall_notMem]
  rintro x ⟨hx, rfl⟩
  exact (((hq x hx).manifoldMorseIndex_le (hf x) (mem_criticalPoints.mp hx)).trans_lt hj).false

/-- For a real `C²` function on a complex manifold of complex dimension `n` which is strongly
`q`-pseudoconvex at each of its critical points, the critical counts in indices `0, …, n + q` add
up to the total number of critical points. -/
theorem sum_criticalCount_eq_totalCriticalCount_of_isManifoldStronglyPseudoconvexAt {q : ℕ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) 2 f)
    (hq : ∀ x ∈ criticalPoints 𝓘(ℝ, E) f, IsManifoldStronglyPseudoconvexAt E q f x) :
    ∑ j ∈ Finset.range (finrank ℂ E + q + 1), criticalCount 𝓘(ℝ, E) f j =
      totalCriticalCount 𝓘(ℝ, E) f := by
  have : FiniteDimensional ℝ E := .trans ℝ ℂ E
  rcases le_total (finrank ℂ E + q + 1) (finrank ℝ E + 1) with h | h
  · refine (Finset.sum_subset (Finset.range_mono h) fun j _ hj ↦ ?_).trans
      sum_criticalCount_eq_totalCriticalCount
    rw [Finset.mem_range, not_lt] at hj
    exact criticalCount_eq_zero_of_isManifoldStronglyPseudoconvexAt hf hq (by omega)
  · refine (Finset.sum_subset (Finset.range_mono h) fun j _ hj ↦ ?_).symm.trans
      sum_criticalCount_eq_totalCriticalCount
    rw [Finset.mem_range, not_lt] at hj
    exact criticalCount_eq_zero_of_finrank_lt (by omega)

/-- A real `C²` function on a complex manifold of complex dimension `n` which is strictly
plurisubharmonic at each of its critical points has no critical points of real Morse index larger
than `n`. -/
theorem criticalCount_eq_zero_of_isManifoldStrictlyPlurisubharmonicAt {j : ℕ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) 2 f)
    (hpos : ∀ x ∈ criticalPoints 𝓘(ℝ, E) f, IsManifoldStrictlyPlurisubharmonicAt E f x)
    (hj : finrank ℂ E < j) :
    criticalCount 𝓘(ℝ, E) f j = 0 :=
  criticalCount_eq_zero_of_isManifoldStronglyPseudoconvexAt (q := 0) hf
    (fun x hx ↦ (hpos x hx).isManifoldStronglyPseudoconvexAt 0) (by simpa using hj)

/-- For a real `C²` function on a complex manifold of complex dimension `n` which is strictly
plurisubharmonic at each of its critical points, the critical counts in indices `0, …, n` add up to
the total number of critical points. -/
theorem sum_criticalCount_eq_totalCriticalCount_of_isManifoldStrictlyPlurisubharmonicAt
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) 2 f)
    (hpos : ∀ x ∈ criticalPoints 𝓘(ℝ, E) f, IsManifoldStrictlyPlurisubharmonicAt E f x) :
    ∑ j ∈ Finset.range (finrank ℂ E + 1), criticalCount 𝓘(ℝ, E) f j =
      totalCriticalCount 𝓘(ℝ, E) f :=
  sum_criticalCount_eq_totalCriticalCount_of_isManifoldStronglyPseudoconvexAt (q := 0) hf
    fun x hx ↦ (hpos x hx).isManifoldStronglyPseudoconvexAt 0

end CriticalCount

end TauCeti

namespace ContMDiffMap

open TauCeti

variable {E : Type*} {M : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [FiniteDimensional ℂ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℂ, E) ∞ M] [T2Space M]

local instance : IsManifold 𝓘(ℝ, E) ∞ M :=
  IsManifold.restrictScalars ℝ (inferInstance : IsManifold 𝓘(ℂ, E) ∞ M)

section SigmaCompact

variable [SigmaCompactSpace M]

/-- Every strong `C^∞` ball around a smooth globally strongly `q`-pseudoconvex function `f` contains
a strong `C^∞` ball around `f` consisting of globally strongly `q`-pseudoconvex functions whose
critical points all have real Morse index at most `dim_ℂ E + q`. -/
private theorem exists_strongCkControl_ball_subset_isManifoldStronglyPseudoconvexAt {q : ℕ}
    (f : C^∞⟮𝓘(ℝ, E), M; 𝓘(ℝ), ℝ⟯) (c : StrongCkControl 𝓘(ℝ, E) M ∞)
    (hf : ∀ x, IsManifoldStronglyPseudoconvexAt E q f x) :
    ∃ c' : StrongCkControl 𝓘(ℝ, E) M ∞, c'.ball f ⊆ c.ball f ∧
      ∀ g ∈ c'.ball f, (∀ x, IsManifoldStronglyPseudoconvexAt E q g x) ∧
        ∀ x ∈ criticalPoints 𝓘(ℝ, E) g, manifoldMorseIndex 𝓘(ℝ, E) g x ≤ finrank ℂ E + q := by
  have : IsManifold 𝓘(ℂ, E) 2 M := IsManifold.of_le (by simp : (2 : ℕ∞ω) ≤ ∞)
  obtain ⟨c₀, -, hc₀⟩ :=
    exists_strongCkControl_isManifoldStronglyPseudoconvexAt (by simp : (2 : ℕ∞ω) ≤ ∞) q f hf
  refine ⟨c.sup c₀, StrongCkControl.ball_sup_subset_left c c₀ f, fun g hg ↦ ?_⟩
  have hg_pos : ∀ x, IsManifoldStronglyPseudoconvexAt E q g x :=
    hc₀ g (StrongCkControl.ball_sup_subset_right c c₀ f hg)
  exact ⟨hg_pos, fun x hx ↦
    (hg_pos x).manifoldMorseIndex_le (g.contMDiff.of_le (by simp : (2 : ℕ∞ω) ≤ ∞)).contMDiffAt
      (mem_criticalPoints.mp hx)⟩

/-- **Relative Morse approximation of strongly `q`-pseudoconvex functions.** Every strong `C^k`
neighbourhood `c.ball f` of a smooth globally strongly `q`-pseudoconvex function `f` on a
sigma-compact Hausdorff complex manifold contains a smooth globally strongly `q`-pseudoconvex Morse
function `g` within a prescribed continuous positive tolerance `ε` of `f`, whose critical points all
have real Morse index at most `dim_ℂ E + q`. If `f` is already Morse on an open neighbourhood `V`
of a closed set `C`, then `g` can be chosen equal to `f` near `C`. -/
theorem exists_isMorse_isManifoldStronglyPseudoconvexAt_mem_ball_sub_compl {q : ℕ}
    (f : C^∞⟮𝓘(ℝ, E), M; 𝓘(ℝ), ℝ⟯) (c : StrongCkControl 𝓘(ℝ, E) M ∞)
    (hf : ∀ x, IsManifoldStronglyPseudoconvexAt E q f x)
    {ε : M → ℝ} (hε : Continuous ε) (hε₀ : ∀ x, 0 < ε x)
    {C V : Set M} (hC : IsClosed C) (hV : IsOpen V) (hCV : C ⊆ V)
    (hfV : IsMorseOn 𝓘(ℝ, E) f V) :
    ∃ g ∈ c.ball f, IsMorse 𝓘(ℝ, E) g ∧
      (∀ x, IsManifoldStronglyPseudoconvexAt E q g x) ∧
      (∀ x ∈ criticalPoints 𝓘(ℝ, E) g, manifoldMorseIndex 𝓘(ℝ, E) g x ≤ finrank ℂ E + q) ∧
      (∀ x, |g x - f x| < ε x) ∧
      tsupport (fun x ↦ g x - f x) ⊆ Cᶜ := by
  have : FiniteDimensional ℝ E := .trans ℝ ℂ E
  obtain ⟨c', hsub, hc'⟩ :=
    f.exists_strongCkControl_ball_subset_isManifoldStronglyPseudoconvexAt c hf
  obtain ⟨g, hg, hgm, hgf, hgs⟩ := f.exists_isMorse_mem_ball_sub_compl c' hε hε₀ hC hV hCV hfV
  obtain ⟨hg_pos, hg_idx⟩ := hc' g hg
  exact ⟨g, hsub hg, hgm, hg_pos, hg_idx, hgf, hgs⟩

/-- **Morse approximation of strongly `q`-pseudoconvex functions** in a strong `C^k` ball and
within a continuous positive `C⁰` tolerance. -/
theorem exists_isMorse_isManifoldStronglyPseudoconvexAt_mem_ball {q : ℕ}
    (f : C^∞⟮𝓘(ℝ, E), M; 𝓘(ℝ), ℝ⟯) (c : StrongCkControl 𝓘(ℝ, E) M ∞)
    (hf : ∀ x, IsManifoldStronglyPseudoconvexAt E q f x)
    {ε : M → ℝ} (hε : Continuous ε) (hε₀ : ∀ x, 0 < ε x) :
    ∃ g ∈ c.ball f, IsMorse 𝓘(ℝ, E) g ∧
      (∀ x, IsManifoldStronglyPseudoconvexAt E q g x) ∧
      (∀ x ∈ criticalPoints 𝓘(ℝ, E) g, manifoldMorseIndex 𝓘(ℝ, E) g x ≤ finrank ℂ E + q) ∧
      ∀ x, |g x - f x| < ε x := by
  obtain ⟨g, hg, hgm, hg_pos, hg_idx, hgf, -⟩ :=
    f.exists_isMorse_isManifoldStronglyPseudoconvexAt_mem_ball_sub_compl c hf hε hε₀
      isClosed_empty isOpen_empty (subset_refl _) isMorseOn_empty
  exact ⟨g, hg, hgm, hg_pos, hg_idx, hgf⟩

/-- **Relative Morse approximation of strictly plurisubharmonic functions.** Every strong `C^k`
neighbourhood `c.ball f` of a smooth globally strictly plurisubharmonic function `f` contains a
smooth globally strictly plurisubharmonic Morse function `g` within `ε` of `f`, agreeing with `f`
near `C` and having real Morse index at most `dim_ℂ E` at every critical point. -/
theorem exists_isMorse_isManifoldStrictlyPlurisubharmonicAt_mem_ball_sub_compl
    (f : C^∞⟮𝓘(ℝ, E), M; 𝓘(ℝ), ℝ⟯) (c : StrongCkControl 𝓘(ℝ, E) M ∞)
    (hf : ∀ x, IsManifoldStrictlyPlurisubharmonicAt E f x)
    {ε : M → ℝ} (hε : Continuous ε) (hε₀ : ∀ x, 0 < ε x)
    {C V : Set M} (hC : IsClosed C) (hV : IsOpen V) (hCV : C ⊆ V)
    (hfV : IsMorseOn 𝓘(ℝ, E) f V) :
    ∃ g ∈ c.ball f, IsMorse 𝓘(ℝ, E) g ∧
      (∀ x, IsManifoldStrictlyPlurisubharmonicAt E g x) ∧
      (∀ x ∈ criticalPoints 𝓘(ℝ, E) g, manifoldMorseIndex 𝓘(ℝ, E) g x ≤ finrank ℂ E) ∧
      (∀ x, |g x - f x| < ε x) ∧
      tsupport (fun x ↦ g x - f x) ⊆ Cᶜ := by
  simpa only [isManifoldStronglyPseudoconvexAt_zero_iff, add_zero] using
    f.exists_isMorse_isManifoldStronglyPseudoconvexAt_mem_ball_sub_compl (q := 0) c
      (fun x ↦ (hf x).isManifoldStronglyPseudoconvexAt 0) hε hε₀ hC hV hCV hfV

/-- **Morse approximation of strictly plurisubharmonic functions** in a strong `C^k` ball and
within a continuous positive `C⁰` tolerance. -/
theorem exists_isMorse_isManifoldStrictlyPlurisubharmonicAt_mem_ball
    (f : C^∞⟮𝓘(ℝ, E), M; 𝓘(ℝ), ℝ⟯) (c : StrongCkControl 𝓘(ℝ, E) M ∞)
    (hf : ∀ x, IsManifoldStrictlyPlurisubharmonicAt E f x)
    {ε : M → ℝ} (hε : Continuous ε) (hε₀ : ∀ x, 0 < ε x) :
    ∃ g ∈ c.ball f, IsMorse 𝓘(ℝ, E) g ∧
      (∀ x, IsManifoldStrictlyPlurisubharmonicAt E g x) ∧
      (∀ x ∈ criticalPoints 𝓘(ℝ, E) g, manifoldMorseIndex 𝓘(ℝ, E) g x ≤ finrank ℂ E) ∧
      ∀ x, |g x - f x| < ε x := by
  obtain ⟨g, hg, hgm, hg_pos, hg_idx, hgf, -⟩ :=
    f.exists_isMorse_isManifoldStrictlyPlurisubharmonicAt_mem_ball_sub_compl c hf hε hε₀
      isClosed_empty isOpen_empty (subset_refl _) isMorseOn_empty
  exact ⟨g, hg, hgm, hg_pos, hg_idx, hgf⟩

end SigmaCompact

/-- **Relative proper Morse approximation of strongly `q`-pseudoconvex functions.** A proper smooth
globally strongly `q`-pseudoconvex function `f` is approximated, in every strong `C^k`
neighbourhood `c.ball f`, by proper smooth globally strongly `q`-pseudoconvex Morse functions `g`
within `C⁰` distance `1` of `f` whose critical points have real Morse index at most `dim_ℂ E + q`,
agreeing with `f` near any closed set `C` on an open neighbourhood `V` of which `f` is already
Morse. No separate sigma-compactness hypothesis on `M` is needed. -/
theorem exists_isMorse_isProperMap_isManifoldStronglyPseudoconvexAt_mem_ball_sub_compl {q : ℕ}
    (f : C^∞⟮𝓘(ℝ, E), M; 𝓘(ℝ), ℝ⟯) (c : StrongCkControl 𝓘(ℝ, E) M ∞)
    (hf_prop : IsProperMap f) (hf_pos : ∀ x, IsManifoldStronglyPseudoconvexAt E q f x)
    {C V : Set M} (hC : IsClosed C) (hV : IsOpen V) (hCV : C ⊆ V)
    (hfV : IsMorseOn 𝓘(ℝ, E) f V) :
    ∃ g ∈ c.ball f, IsMorse 𝓘(ℝ, E) g ∧ IsProperMap g ∧
      (∀ x, IsManifoldStronglyPseudoconvexAt E q g x) ∧
      (∀ x ∈ criticalPoints 𝓘(ℝ, E) g, manifoldMorseIndex 𝓘(ℝ, E) g x ≤ finrank ℂ E + q) ∧
      (∀ x, |g x - f x| < 1) ∧
      tsupport (fun x ↦ g x - f x) ⊆ Cᶜ := by
  have := hf_prop.sigmaCompactSpace
  have : FiniteDimensional ℝ E := .trans ℝ ℂ E
  obtain ⟨c', hsub, hc'⟩ :=
    f.exists_strongCkControl_ball_subset_isManifoldStronglyPseudoconvexAt c hf_pos
  obtain ⟨g, hg, hgm, hgp, hgf, hgs⟩ :=
    f.exists_isMorse_isProperMap_mem_ball_sub_compl c' hf_prop hC hV hCV hfV
  obtain ⟨hg_pos, hg_idx⟩ := hc' g hg
  exact ⟨g, hsub hg, hgm, hgp, hg_pos, hg_idx, hgf, hgs⟩

/-- **Proper Morse approximation of strongly `q`-pseudoconvex functions** in a strong `C^k` ball
within `C⁰` distance `1`. -/
theorem exists_isMorse_isProperMap_isManifoldStronglyPseudoconvexAt_mem_ball {q : ℕ}
    (f : C^∞⟮𝓘(ℝ, E), M; 𝓘(ℝ), ℝ⟯) (c : StrongCkControl 𝓘(ℝ, E) M ∞)
    (hf_prop : IsProperMap f) (hf_pos : ∀ x, IsManifoldStronglyPseudoconvexAt E q f x) :
    ∃ g ∈ c.ball f, IsMorse 𝓘(ℝ, E) g ∧ IsProperMap g ∧
      (∀ x, IsManifoldStronglyPseudoconvexAt E q g x) ∧
      (∀ x ∈ criticalPoints 𝓘(ℝ, E) g, manifoldMorseIndex 𝓘(ℝ, E) g x ≤ finrank ℂ E + q) ∧
      ∀ x, |g x - f x| < 1 := by
  obtain ⟨g, hg, hgm, hgp, hg_pos, hg_idx, hgf, -⟩ :=
    f.exists_isMorse_isProperMap_isManifoldStronglyPseudoconvexAt_mem_ball_sub_compl c hf_prop
      hf_pos isClosed_empty isOpen_empty (subset_refl _) isMorseOn_empty
  exact ⟨g, hg, hgm, hgp, hg_pos, hg_idx, hgf⟩

/-- **Relative proper Morse approximation of strictly plurisubharmonic functions.** -/
theorem exists_isMorse_isProperMap_isManifoldStrictlyPlurisubharmonicAt_mem_ball_sub_compl
    (f : C^∞⟮𝓘(ℝ, E), M; 𝓘(ℝ), ℝ⟯) (c : StrongCkControl 𝓘(ℝ, E) M ∞)
    (hf_prop : IsProperMap f) (hf_pos : ∀ x, IsManifoldStrictlyPlurisubharmonicAt E f x)
    {C V : Set M} (hC : IsClosed C) (hV : IsOpen V) (hCV : C ⊆ V)
    (hfV : IsMorseOn 𝓘(ℝ, E) f V) :
    ∃ g ∈ c.ball f, IsMorse 𝓘(ℝ, E) g ∧ IsProperMap g ∧
      (∀ x, IsManifoldStrictlyPlurisubharmonicAt E g x) ∧
      (∀ x ∈ criticalPoints 𝓘(ℝ, E) g, manifoldMorseIndex 𝓘(ℝ, E) g x ≤ finrank ℂ E) ∧
      (∀ x, |g x - f x| < 1) ∧
      tsupport (fun x ↦ g x - f x) ⊆ Cᶜ := by
  simpa only [isManifoldStronglyPseudoconvexAt_zero_iff, add_zero] using
    f.exists_isMorse_isProperMap_isManifoldStronglyPseudoconvexAt_mem_ball_sub_compl (q := 0) c
      hf_prop (fun x ↦ (hf_pos x).isManifoldStronglyPseudoconvexAt 0) hC hV hCV hfV

/-- **Proper Morse approximation of strictly plurisubharmonic functions** in a strong `C^k` ball
within `C⁰` distance `1`. -/
theorem exists_isMorse_isProperMap_isManifoldStrictlyPlurisubharmonicAt_mem_ball
    (f : C^∞⟮𝓘(ℝ, E), M; 𝓘(ℝ), ℝ⟯) (c : StrongCkControl 𝓘(ℝ, E) M ∞)
    (hf_prop : IsProperMap f) (hf_pos : ∀ x, IsManifoldStrictlyPlurisubharmonicAt E f x) :
    ∃ g ∈ c.ball f, IsMorse 𝓘(ℝ, E) g ∧ IsProperMap g ∧
      (∀ x, IsManifoldStrictlyPlurisubharmonicAt E g x) ∧
      (∀ x ∈ criticalPoints 𝓘(ℝ, E) g, manifoldMorseIndex 𝓘(ℝ, E) g x ≤ finrank ℂ E) ∧
      ∀ x, |g x - f x| < 1 := by
  obtain ⟨g, hg, hgm, hgp, hg_pos, hg_idx, hgf, -⟩ :=
    f.exists_isMorse_isProperMap_isManifoldStrictlyPlurisubharmonicAt_mem_ball_sub_compl c hf_prop
      hf_pos isClosed_empty isOpen_empty (subset_refl _) isMorseOn_empty
  exact ⟨g, hg, hgm, hgp, hg_pos, hg_idx, hgf⟩

end ContMDiffMap

namespace TauCeti

variable {E : Type*} {M : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [FiniteDimensional ℂ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℂ, E) ∞ M] [T2Space M]

local instance : IsManifold 𝓘(ℝ, E) ∞ M :=
  IsManifold.restrictScalars ℝ (inferInstance : IsManifold 𝓘(ℂ, E) ∞ M)

/-- **Relative Morse perturbation of a strongly `q`-pseudoconvex exhaustion.** Given a smooth
proper bounded-below globally strongly `q`-pseudoconvex function `f : M → ℝ` on a Hausdorff complex
manifold which is already Morse on an open neighbourhood `V` of a closed set `C`, there is a smooth
proper bounded-below globally strongly `q`-pseudoconvex Morse function `g` within `C⁰` distance `1`
of `f` that agrees with `f` near `C` and has real Morse index at most `dim_ℂ E + q` at every
critical point. -/
theorem exists_isMorse_isProperMap_bddBelow_isManifoldStronglyPseudoconvexAt_sub_compl {q : ℕ}
    {f : M → ℝ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ f) (hf_prop : IsProperMap f)
    (hf_bdd : BddBelow (range f)) (hf_pos : ∀ x, IsManifoldStronglyPseudoconvexAt E q f x)
    {C V : Set M} (hC : IsClosed C) (hV : IsOpen V) (hCV : C ⊆ V)
    (hfV : IsMorseOn 𝓘(ℝ, E) f V) :
    ∃ g : C^∞⟮𝓘(ℝ, E), M; 𝓘(ℝ), ℝ⟯,
      IsMorse 𝓘(ℝ, E) g ∧ IsProperMap g ∧ BddBelow (range g) ∧
      (∀ x, IsManifoldStronglyPseudoconvexAt E q g x) ∧
      (∀ x ∈ criticalPoints 𝓘(ℝ, E) g, manifoldMorseIndex 𝓘(ℝ, E) g x ≤ finrank ℂ E + q) ∧
      (∀ x, |g x - f x| < 1) ∧
      tsupport (fun x ↦ g x - f x) ⊆ Cᶜ := by
  obtain ⟨g, -, hgm, hgp, hg_pos, hg_idx, hgf, hgs⟩ :=
    ContMDiffMap.exists_isMorse_isProperMap_isManifoldStronglyPseudoconvexAt_mem_ball_sub_compl
      ⟨f, hf⟩ .empty hf_prop hf_pos hC hV hCV hfV
  simp only [ContMDiffMap.coeFn_mk] at hgf hgs
  exact ⟨g, hgm, hgp, hf_bdd.range_of_abs_sub_le fun x ↦ (hgf x).le, hg_pos, hg_idx, hgf, hgs⟩

/-- **Morse perturbation of a strongly `q`-pseudoconvex exhaustion.** A smooth proper bounded-below
globally strongly `q`-pseudoconvex function `f : M → ℝ` on a Hausdorff complex manifold is
approximated within `C⁰` distance `1` by a smooth proper bounded-below globally strongly
`q`-pseudoconvex Morse exhaustion whose critical points all have real Morse index at most
`dim_ℂ E + q`. -/
theorem exists_isMorse_isProperMap_bddBelow_isManifoldStronglyPseudoconvexAt {q : ℕ} {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ f) (hf_prop : IsProperMap f) (hf_bdd : BddBelow (range f))
    (hf_pos : ∀ x, IsManifoldStronglyPseudoconvexAt E q f x) :
    ∃ g : C^∞⟮𝓘(ℝ, E), M; 𝓘(ℝ), ℝ⟯,
      IsMorse 𝓘(ℝ, E) g ∧ IsProperMap g ∧ BddBelow (range g) ∧
      (∀ x, IsManifoldStronglyPseudoconvexAt E q g x) ∧
      (∀ x ∈ criticalPoints 𝓘(ℝ, E) g, manifoldMorseIndex 𝓘(ℝ, E) g x ≤ finrank ℂ E + q) ∧
      ∀ x, |g x - f x| < 1 := by
  obtain ⟨g, hgm, hgp, hg_bdd, hg_pos, hg_idx, hgf, -⟩ :=
    exists_isMorse_isProperMap_bddBelow_isManifoldStronglyPseudoconvexAt_sub_compl hf hf_prop
      hf_bdd hf_pos isClosed_empty isOpen_empty (subset_refl _) isMorseOn_empty
  exact ⟨g, hgm, hgp, hg_bdd, hg_pos, hg_idx, hgf⟩

/-- **Relative Morse perturbation of a strictly plurisubharmonic exhaustion.** -/
theorem exists_isMorse_isProperMap_bddBelow_isManifoldStrictlyPlurisubharmonicAt_sub_compl
    {f : M → ℝ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ f) (hf_prop : IsProperMap f)
    (hf_bdd : BddBelow (range f)) (hf_pos : ∀ x, IsManifoldStrictlyPlurisubharmonicAt E f x)
    {C V : Set M} (hC : IsClosed C) (hV : IsOpen V) (hCV : C ⊆ V)
    (hfV : IsMorseOn 𝓘(ℝ, E) f V) :
    ∃ g : C^∞⟮𝓘(ℝ, E), M; 𝓘(ℝ), ℝ⟯,
      IsMorse 𝓘(ℝ, E) g ∧ IsProperMap g ∧ BddBelow (range g) ∧
      (∀ x, IsManifoldStrictlyPlurisubharmonicAt E g x) ∧
      (∀ x ∈ criticalPoints 𝓘(ℝ, E) g, manifoldMorseIndex 𝓘(ℝ, E) g x ≤ finrank ℂ E) ∧
      (∀ x, |g x - f x| < 1) ∧
      tsupport (fun x ↦ g x - f x) ⊆ Cᶜ := by
  simpa only [isManifoldStronglyPseudoconvexAt_zero_iff, add_zero] using
    exists_isMorse_isProperMap_bddBelow_isManifoldStronglyPseudoconvexAt_sub_compl (q := 0) hf
      hf_prop hf_bdd (fun x ↦ (hf_pos x).isManifoldStronglyPseudoconvexAt 0) hC hV hCV hfV

/-- **Morse perturbation of a strictly plurisubharmonic exhaustion.** A smooth proper bounded-below
globally strictly plurisubharmonic function `f : M → ℝ` on a Hausdorff complex manifold is
approximated within `C⁰` distance `1` by a smooth proper bounded-below globally strictly
plurisubharmonic Morse exhaustion whose critical points all have real Morse index at most
`dim_ℂ E`. -/
theorem exists_isMorse_isProperMap_bddBelow_isManifoldStrictlyPlurisubharmonicAt {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ f) (hf_prop : IsProperMap f) (hf_bdd : BddBelow (range f))
    (hf_pos : ∀ x, IsManifoldStrictlyPlurisubharmonicAt E f x) :
    ∃ g : C^∞⟮𝓘(ℝ, E), M; 𝓘(ℝ), ℝ⟯,
      IsMorse 𝓘(ℝ, E) g ∧ IsProperMap g ∧ BddBelow (range g) ∧
      (∀ x, IsManifoldStrictlyPlurisubharmonicAt E g x) ∧
      (∀ x ∈ criticalPoints 𝓘(ℝ, E) g, manifoldMorseIndex 𝓘(ℝ, E) g x ≤ finrank ℂ E) ∧
      ∀ x, |g x - f x| < 1 := by
  obtain ⟨g, hgm, hgp, hg_bdd, hg_pos, hg_idx, hgf, -⟩ :=
    exists_isMorse_isProperMap_bddBelow_isManifoldStrictlyPlurisubharmonicAt_sub_compl hf hf_prop
      hf_bdd hf_pos isClosed_empty isOpen_empty (subset_refl _) isMorseOn_empty
  exact ⟨g, hgm, hgp, hg_bdd, hg_pos, hg_idx, hgf⟩

/-- **Morse perturbation of squared distance along a proper holomorphic immersion.** For any smooth
proper holomorphic immersion `i : M → F` into a proper complex inner product space and any fixed
centre `a : F`, `x ↦ ‖i x - a‖²` is approximated within `C⁰` distance `1` by a smooth proper
bounded-below globally strictly plurisubharmonic Morse exhaustion whose critical points all have
real Morse index at most `dim_ℂ E`. Unlike Milnor's focal-set argument, `a` is arbitrary and is not
varied. -/
theorem exists_isMorse_isProperMap_isManifoldStrictlyPlurisubharmonicAt_norm_sq_sub_comp
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [ProperSpace F]
    {i : M → F} (hi : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, F) ∞ i) (hip : IsProperMap i)
    (hinj : ∀ x, Injective (mvfderiv 𝓘(ℂ, E) i x)) (a : F) :
    ∃ g : C^∞⟮𝓘(ℝ, E), M; 𝓘(ℝ), ℝ⟯,
      IsMorse 𝓘(ℝ, E) g ∧ IsProperMap g ∧ BddBelow (range g) ∧
      (∀ x, IsManifoldStrictlyPlurisubharmonicAt E g x) ∧
      (∀ x ∈ criticalPoints 𝓘(ℝ, E) g, manifoldMorseIndex 𝓘(ℝ, E) g x ≤ finrank ℂ E) ∧
      ∀ x, |g x - ‖i x - a‖ ^ 2| < 1 := by
  have hiR : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ i := by
    simpa using hi.restrictScalars ℝ
  have hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ (fun x ↦ ‖i x - a‖ ^ 2) :=
    (contDiff_norm_sq ℂ).contMDiff.comp (hiR.sub contMDiff_const)
  have hf_prop : IsProperMap (fun x ↦ ‖i x - a‖ ^ 2) :=
    (isProperMap_norm_sq_sub_comp_iff hi.continuous a).2 hip
  have hf_bdd : BddBelow (range fun x ↦ ‖i x - a‖ ^ 2) :=
    ⟨0, by rintro _ ⟨x, rfl⟩; positivity⟩
  have hf_pos : ∀ x, IsManifoldStrictlyPlurisubharmonicAt E (fun y ↦ ‖i y - a‖ ^ 2) x :=
    fun x ↦ (isManifoldStrictlyPlurisubharmonicAt_norm_sq_sub_comp_iff
      ((hi.of_le (by simp : (2 : ℕ∞ω) ≤ ∞)) x)).2 (hinj x)
  exact exists_isMorse_isProperMap_bddBelow_isManifoldStrictlyPlurisubharmonicAt hf hf_prop hf_bdd
    hf_pos

end TauCeti
