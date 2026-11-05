/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Complex.Pseudoconvex.Strong
public import TauCeti.Geometry.Manifold.Morse.Cell.Band
public import TauCeti.Geometry.Manifold.Morse.Generic.Strong

import TauCeti.Geometry.Manifold.ContMDiff.RestrictScalars
import TauCeti.Topology.Maps.Proper.Basic

/-!
# Morse approximation and homology vanishing on pseudoconvex complex manifolds

On a complex manifold `M` of complex dimension `n`, everywhere strong `q`-pseudoconvexity is open
in the strong `C²` Whitney topology
(`TauCeti.exists_strongCkControl_isManifoldStronglyPseudoconvexAt`), while Morse functions are
dense in the strong `C^∞` Whitney topology with prescribed `C⁰` error and relative to an open
neighbourhood of any closed set where the function is already Morse
(`ContMDiffMap.exists_isMorse_mem_ball_sub_compl`,
`ContMDiffMap.exists_isMorse_isProperMap_mem_ball`). Combining both shows that any smooth proper
bounded-below strongly `q`-pseudoconvex exhaustion can be perturbed within `C⁰` distance `1` (and
away from an already-Morse closed set) to a proper bounded-below strongly `q`-pseudoconvex Morse
exhaustion whose critical points all have real Morse index at most `n + q`
(`ContMDiffMap.exists_isMorse_isProperMap_bddBelow_isManifoldStronglyPseudoconvexAt`).

Combining this Morse approximation with
`TauCeti.IsMorse.isZero_singularHomology_of_manifoldMorseIndex_le` yields global singular homology
vanishing `Hₖ(M; R) = 0` for `k > n + q` on any complex manifold carrying an arbitrary smooth
proper bounded-below everywhere strongly `q`-pseudoconvex exhaustion, without assuming the
exhaustion is Morse
(`TauCeti.isZero_singularHomology_of_isProperMap_of_isManifoldStronglyPseudoconvexAt`, and for
strictly plurisubharmonic exhaustions
`TauCeti.isZero_singularHomology_of_isProperMap_of_isManifoldStrictlyPlurisubharmonicAt`), with
coefficients in any abelian category with coproducts and exact sequential colimits (in particular
any module over a ring, such as `ℤ`).

## Main results

* `ContMDiffMap.exists_isMorse_mem_ball_sub_compl_isManifoldStronglyPseudoconvexAt`,
  `ContMDiffMap.exists_isMorse_isProperMap_bddBelow_isManifoldStronglyPseudoconvexAt`: relative and
  proper Morse approximation preserving strong `q`-pseudoconvexity and the index bound `n + q`.
* `TauCeti.isZero_singularHomology_of_isProperMap_of_isManifoldStronglyPseudoconvexAt`,
  `TauCeti.isZero_singularHomology_of_isProperMap_of_isManifoldStrictlyPlurisubharmonicAt`:
  vanishing of `Hₖ(M; R)` above degree `n + q` (and above `n` in the strictly plurisubharmonic
  case) for smooth non-Morse exhaustions.

## References

* A. Andreotti and T. Frankel, *The Lefschetz theorem on hyperplane sections*, Ann. of Math. (2)
  69 (1959), 713–717.
* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  Section 7.
* R. Hain, *Notes on the Morse theory of complex manifolds*, Section 2.
-/

public section

noncomputable section

open AlgebraicTopology CategoryTheory ContMDiffMap Limits Module Set Topology
open scoped ContDiff Manifold

universe u v w

namespace TauCeti

variable {E : Type*} {M : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ∞ M] [T2Space M]

/-- **Relative Morse approximation preserving strong `q`-pseudoconvexity.** Let `f` be a smooth
everywhere strongly `q`-pseudoconvex function on a Hausdorff sigma-compact complex manifold `M` of
complex dimension `n`, already Morse on an open neighbourhood `V` of a closed set `C`. For every
continuous positive tolerance `ε`, there is a smooth Morse function `g` with `|g - f| < ε`
everywhere, agreeing with `f` near `C`, which remains everywhere strongly `q`-pseudoconvex and has
Morse index at most `n + q` at every critical point. -/
theorem _root_.ContMDiffMap.exists_isMorse_mem_ball_sub_compl_isManifoldStronglyPseudoconvexAt
    [SigmaCompactSpace M] (f : C^∞⟮𝓘(ℝ, E), M; 𝓘(ℝ), ℝ⟯) (q : ℕ)
    (hf : ∀ x, IsManifoldStronglyPseudoconvexAt E q f x)
    {ε : M → ℝ} (hε : Continuous ε) (hε₀ : ∀ x, 0 < ε x)
    {C V : Set M} (hC : IsClosed C) (hV : IsOpen V) (hCV : C ⊆ V)
    (hfV : IsMorseOn 𝓘(ℝ, E) f V) :
    ∃ g : C^∞⟮𝓘(ℝ, E), M; 𝓘(ℝ), ℝ⟯, IsMorse 𝓘(ℝ, E) g ∧ (∀ x, |g x - f x| < ε x) ∧
      tsupport (fun x ↦ g x - f x) ⊆ Cᶜ ∧
      (∀ x, IsManifoldStronglyPseudoconvexAt E q g x) ∧
      ∀ x ∈ criticalPoints 𝓘(ℝ, E) g, manifoldMorseIndex 𝓘(ℝ, E) g x ≤ finrank ℂ E + q := by
  have : FiniteDimensional ℝ E := Module.Finite.trans ℂ E
  have : IsManifold 𝓘(ℝ, E) ∞ M :=
    IsManifold.restrictScalars ℝ (inferInstance : IsManifold 𝓘(ℂ, E) ∞ M)
  obtain ⟨c, -, hc⟩ :=
    exists_strongCkControl_isManifoldStronglyPseudoconvexAt (by norm_cast) q f hf
  obtain ⟨g, hg, hgm, hgε, hgs⟩ := f.exists_isMorse_mem_ball_sub_compl c hε hε₀ hC hV hCV hfV
  refine ⟨g, hgm, hgε, hgs, fun x ↦ hc g hg x, fun x hx ↦ ?_⟩
  exact (hc g hg x).manifoldMorseIndex_le (g.contMDiff x |>.of_le (by norm_cast))
    (mem_criticalPoints.1 hx)

/-- **Proper Morse exhaustion approximation preserving strong `q`-pseudoconvexity.** Every smooth
proper bounded-below everywhere strongly `q`-pseudoconvex function `f` on `M`, already Morse on an
open neighbourhood `V` of a closed set `C`, admits a smooth proper bounded-below Morse
approximation `g` within `C⁰` distance `1`, agreeing with `f` near `C`, everywhere strongly
`q`-pseudoconvex, and with Morse index at most `finrank ℂ E + q` at every critical point. -/
theorem _root_.ContMDiffMap.exists_isMorse_isProperMap_bddBelow_isManifoldStronglyPseudoconvexAt
    (f : C^∞⟮𝓘(ℝ, E), M; 𝓘(ℝ), ℝ⟯) (q : ℕ)
    (hf : ∀ x, IsManifoldStronglyPseudoconvexAt E q f x)
    (hp : IsProperMap f) (hbdd : BddBelow (range f))
    {C V : Set M} (hC : IsClosed C) (hV : IsOpen V) (hCV : C ⊆ V)
    (hfV : IsMorseOn 𝓘(ℝ, E) f V) :
    ∃ g : C^∞⟮𝓘(ℝ, E), M; 𝓘(ℝ), ℝ⟯, IsMorse 𝓘(ℝ, E) g ∧ IsProperMap g ∧ BddBelow (range g) ∧
      (∀ x, |g x - f x| < 1) ∧ tsupport (fun x ↦ g x - f x) ⊆ Cᶜ ∧
      (∀ x, IsManifoldStronglyPseudoconvexAt E q g x) ∧
      ∀ x ∈ criticalPoints 𝓘(ℝ, E) g, manifoldMorseIndex 𝓘(ℝ, E) g x ≤ finrank ℂ E + q := by
  have : SigmaCompactSpace M := hp.sigmaCompactSpace
  have : FiniteDimensional ℝ E := Module.Finite.trans ℂ E
  have : IsManifold 𝓘(ℝ, E) ∞ M :=
    IsManifold.restrictScalars ℝ (inferInstance : IsManifold 𝓘(ℂ, E) ∞ M)
  obtain ⟨c, -, hc⟩ :=
    exists_strongCkControl_isManifoldStronglyPseudoconvexAt (by norm_cast) q f hf
  obtain ⟨g, hg, hgm, hgp, hgf, hgs⟩ := f.exists_isMorse_isProperMap_mem_ball c hp hC hV hCV hfV
  obtain ⟨b, hb⟩ := hbdd
  refine ⟨g, hgm, hgp, ⟨b - 1, forall_mem_range.2 fun x ↦ by
    linarith [(abs_lt.1 (hgf x)).1, hb (mem_range_self x)]⟩, hgf, hgs, fun x ↦ hc g hg x,
    fun x hx ↦ (hc g hg x).manifoldMorseIndex_le (g.contMDiff x |>.of_le (by norm_cast))
      (mem_criticalPoints.1 hx)⟩

/-- **Homology vanishing on manifolds with a smooth strongly `q`-pseudoconvex exhaustion.** If `M`
carries a smooth proper bounded-below everywhere strongly `q`-pseudoconvex function `f : M → ℝ`
(not assumed to be Morse), then `Hₙ(M; R) = 0` for `n > finrank ℂ E + q`. -/
theorem isZero_singularHomology_of_isProperMap_of_isManifoldStronglyPseudoconvexAt
    {f : M → ℝ} {q : ℕ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ f) (hp : IsProperMap f)
    (hbdd : BddBelow (range f)) (hq : ∀ x, IsManifoldStronglyPseudoconvexAt E q f x)
    {𝒜 : Type v} [Category.{w} 𝒜] [Abelian 𝒜] [HasCoproducts.{u} 𝒜]
    [HasColimitsOfShape ℕ 𝒜] [HasExactColimitsOfShape ℕ 𝒜] (R : 𝒜) {n : ℕ}
    (hn : finrank ℂ E + q < n) :
    IsZero (((singularHomologyFunctor 𝒜 n).obj R).obj (TopCat.of M)) := by
  have : FiniteDimensional ℝ E := Module.Finite.trans ℂ E
  have : IsManifold 𝓘(ℝ, E) ∞ M :=
    IsManifold.restrictScalars ℝ (inferInstance : IsManifold 𝓘(ℂ, E) ∞ M)
  let F : C^∞⟮𝓘(ℝ, E), M; 𝓘(ℝ), ℝ⟯ := ⟨f, hf⟩
  obtain ⟨g, hgm, hgp, hgbdd, -, -, -, hgidx⟩ :=
    F.exists_isMorse_isProperMap_bddBelow_isManifoldStronglyPseudoconvexAt q hq hp hbdd
      isClosed_empty isOpen_empty (subset_refl _) isMorseOn_empty
  exact hgm.isZero_singularHomology_of_manifoldMorseIndex_le hgp hgbdd hgidx R hn

/-- **Homology vanishing on manifolds with a smooth strictly plurisubharmonic exhaustion.** If `M`
carries a smooth proper bounded-below everywhere strictly plurisubharmonic function, `Hₙ(M; R) = 0`
for `n > finrank ℂ E`. -/
theorem isZero_singularHomology_of_isProperMap_of_isManifoldStrictlyPlurisubharmonicAt
    {f : M → ℝ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ f) (hp : IsProperMap f)
    (hbdd : BddBelow (range f)) (hpsh : ∀ x, IsManifoldStrictlyPlurisubharmonicAt E f x)
    {𝒜 : Type v} [Category.{w} 𝒜] [Abelian 𝒜] [HasCoproducts.{u} 𝒜]
    [HasColimitsOfShape ℕ 𝒜] [HasExactColimitsOfShape ℕ 𝒜] (R : 𝒜) {n : ℕ}
    (hn : finrank ℂ E < n) :
    IsZero (((singularHomologyFunctor 𝒜 n).obj R).obj (TopCat.of M)) :=
  isZero_singularHomology_of_isProperMap_of_isManifoldStronglyPseudoconvexAt (q := 0) hf hp hbdd
    (fun x ↦ (hpsh x).isManifoldStronglyPseudoconvexAt 0) R (by omega)

end TauCeti
