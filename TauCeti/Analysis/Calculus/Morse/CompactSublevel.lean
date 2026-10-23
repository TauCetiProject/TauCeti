/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Morse.Breaking
import TauCeti.Analysis.Calculus.Morse.Stable

/-!
# Broken Morse chains and finite index-one trajectory spaces from compact sublevels

Suppose every sublevel of a finite-dimensional Morse function is compact. Every forward
negative-gradient orbit stays in the sublevel of its initial point, so it converges to a critical
point. A point in the closure of an unstable manifold also has a backward orbit in the sublevel
of its originating critical point; this orbit converges to a critical point as well.

Under Morse--Smale transversality, these convergence facts also produce finite chains of
nonconstant connecting orbits forced by stable- or unstable-set closure incidence, with the number
of components bounded by the Morse-index drop. They do not assert convergence of a sequence of
trajectories to a broken chain.

These two convergence facts discharge the global endpoint hypotheses in the compactness theorem
for index-one trajectory slices. The slice at an intermediate value is a closed subset of
a compact level, and Morse--Smale transversality makes it discrete. It therefore contains only
finitely many unparametrized trajectories, the finiteness needed for the Morse differential.

The compact-sublevel hypothesis is the usual properness condition for a bounded-below Morse
function on Euclidean space. On a compact manifold, compactness comes from the ambient space
instead.

## Reference

M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
Chapter 3 (compactness of spaces of trajectories).
-/

public section

open Filter Set Topology
open scoped Gradient NNReal

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {f : E → ℝ} {K : ℝ≥0}

/-- Every forward orbit of a globally Morse function converges to a nondegenerate critical
point when the sublevel at its initial value is compact. -/
theorem exists_stableSet_of_isCompact_sublevel (hfs : ContDiff ℝ 2 f)
    (hf : LipschitzWith K (∇ f)) (hM : HasNondegenerateCriticalPointsOn f univ)
    (y : E) (hcompact : IsCompact {z | f z ≤ f y}) :
    ∃ q, IsNondegenerateCriticalPoint f q ∧
      y ∈ Flow.stableSet (negativeGradientFlow f hf) q := by
  let φ := negativeGradientFlow f hf
  have hanti := negativeGradientFlow_orbit_antitone f hf y
    (fun _ ↦ hfs.differentiable (by norm_num) _)
  have hmaps : MapsTo (fun t ↦ φ t y) (Ici 0) {z | f z ≤ f y} := by
    intro t ht
    simpa only [Set.mem_ofPred_eq, φ, _root_.Flow.map_zero_apply] using hanti ht
  have hγ : IsIntegralCurveOn (fun t ↦ φ t y) (fun _ x ↦ -∇ f x) (Ici 0) :=
    ((isNegativeGradient_negativeGradientFlow f hf).isIntegralCurve y).isIntegralCurveOn _
  obtain ⟨q, -, hq, hlim⟩ :=
    IsIntegralCurveOn.exists_tendsto_atTop_of_hasNondegenerateCriticalPointsOn
      hγ hcompact hmaps
      (fun _ _ ↦ hfs.differentiable (by norm_num) _)
      (hfs.continuous_fderiv (by norm_num)).continuousOn
      (hM.mono (subset_univ _))
  have hq' : fderiv ℝ f q = 0 := by
    rw [← toDual_gradient (𝕜 := ℝ) (f := f) (x := q), hq, map_zero]
  exact ⟨q, (hasNondegenerateCriticalPointsOn_iff.mp hM) (mem_univ q) hq',
    Flow.mem_stableSet.mpr hlim⟩

/-- Every backward orbit starting in the closure of an unstable manifold converges to some
nondegenerate critical point when the sublevel at the originating point is compact. -/
theorem exists_unstableSet_of_mem_closure_unstableSet_of_isCompact_sublevel
    (hfs : ContDiff ℝ 2 f) (hf : LipschitzWith K (∇ f))
    (hM : HasNondegenerateCriticalPointsOn f univ)
    {p y : E} (hcompact : IsCompact {z | f z ≤ f p})
    (hy : y ∈ closure (Flow.unstableSet (negativeGradientFlow f hf) p)) :
    ∃ a, IsNondegenerateCriticalPoint f a ∧
      y ∈ Flow.unstableSet (negativeGradientFlow f hf) a := by
  let φ := negativeGradientFlow f hf
  have hbound : ∀ z ∈ closure (Flow.unstableSet φ p), f z ≤ f p := by
    intro z hz
    exact (isClosed_le hfs.continuous continuous_const).closure_subset
      (closure_mono (fun w hw ↦
        (isNegativeGradient_negativeGradientFlow f hf).value_ge_of_mem_unstableSet hw
          (fun _ ↦ hfs.differentiable (by norm_num) _) hfs.continuous.continuousAt) hz)
  have hmaps : MapsTo (fun t ↦ φ t y) (Iic 0) {z | f z ≤ f p} := by
    intro t _
    apply hbound
    exact map_mem_closure (φ.continuous_toFun t) hy
      (Flow.isInvariant_unstableSet φ p t)
  have hγ : IsIntegralCurveOn (fun t ↦ φ t y) (fun _ x ↦ -∇ f x) (Iic 0) :=
    ((isNegativeGradient_negativeGradientFlow f hf).isIntegralCurve y).isIntegralCurveOn _
  obtain ⟨a, -, ha, hlim⟩ :=
    IsIntegralCurveOn.exists_tendsto_atBot_of_hasNondegenerateCriticalPointsOn
      hγ hcompact hmaps
      (fun _ _ ↦ hfs.differentiable (by norm_num) _)
      (hfs.continuous_fderiv (by norm_num)).continuousOn
      (hM.mono (subset_univ _))
  have ha' : fderiv ℝ f a = 0 := by
    rw [← toDual_gradient (𝕜 := ℝ) (f := f) (x := a), ha, map_zero]
  exact ⟨a, (hasNondegenerateCriticalPointsOn_iff.mp hM) (mem_univ a) ha',
    Flow.mem_unstableSet.mpr hlim⟩

namespace IsNondegenerateCriticalPoint

variable {x p q : E}

/-- For a globally Morse function with compact sublevels and Morse--Smale transversality,
a stable-set closure incidence produces a finite chain `x :: l` from `x` to `q` of nonconstant
connecting orbits between nondegenerate critical points. Compactness supplies forward convergence,
and `l.length` is at most `morseIndex f x - morseIndex f q`. -/
theorem exists_isChain_of_mem_closure_stableSet_inter_stableSet_of_isCompact_sublevel
    (hx : IsNondegenerateCriticalPoint f x) (hfs : ContDiff ℝ 2 f)
    (hf : LipschitzWith K (∇ f)) (hM : HasNondegenerateCriticalPointsOn f univ)
    (hcompact : ∀ c : ℝ, IsCompact {z | f z ≤ c}) (hqx : q ≠ x)
    (hy : (closure (Flow.stableSet (negativeGradientFlow f hf) q) ∩
      Flow.stableSet (negativeGradientFlow f hf) x).Nonempty)
    (htr : IsMorseSmale f hf) :
    ∃ l : List E,
      (x :: l).IsChain (fun a b ↦ a ≠ b ∧
        (Flow.unstableSet (negativeGradientFlow f hf) a ∩
          Flow.stableSet (negativeGradientFlow f hf) b).Nonempty) ∧
      (x :: l).getLast (List.cons_ne_nil _ _) = q ∧
      (∀ a ∈ x :: l, IsNondegenerateCriticalPoint f a) ∧
      l.length + morseIndex f q ≤ morseIndex f x :=
  hx.exists_isChain_of_mem_closure_stableSet_inter_stableSet hfs hf hqx hy
    (fun {_} _ ↦ exists_stableSet_of_isCompact_sublevel hfs hf hM _ (hcompact _)) htr

/-- For a globally Morse function with Morse--Smale transversality and compact sublevel at
`f p`, an unstable-set closure incidence produces a finite chain `p :: l` from `p` to `x` of
nonconstant connecting orbits between nondegenerate critical points. Compactness supplies backward
convergence, and `l.length` is at most `morseIndex f p - morseIndex f x`. -/
theorem exists_isChain_of_mem_closure_unstableSet_inter_unstableSet_of_isCompact_sublevel
    (hx : IsNondegenerateCriticalPoint f x) (hfs : ContDiff ℝ 2 f)
    (hf : LipschitzWith K (∇ f)) (hM : HasNondegenerateCriticalPointsOn f univ)
    (hcompact : IsCompact {z | f z ≤ f p}) (hpx : p ≠ x)
    (hy : (closure (Flow.unstableSet (negativeGradientFlow f hf) p) ∩
      Flow.unstableSet (negativeGradientFlow f hf) x).Nonempty)
    (htr : IsMorseSmale f hf) :
    ∃ l : List E,
      (p :: l).IsChain (fun a b ↦ a ≠ b ∧
        (Flow.unstableSet (negativeGradientFlow f hf) a ∩
          Flow.stableSet (negativeGradientFlow f hf) b).Nonempty) ∧
      (p :: l).getLast (List.cons_ne_nil _ _) = x ∧
      (∀ a ∈ p :: l, IsNondegenerateCriticalPoint f a) ∧
      l.length + morseIndex f x ≤ morseIndex f p :=
  hx.exists_isChain_of_mem_closure_unstableSet_inter_unstableSet hfs hf hpx hy
    (fun {_} hz ↦ exists_unstableSet_of_mem_closure_unstableSet_of_isCompact_sublevel
      hfs hf hM hcompact hz) htr

end IsNondegenerateCriticalPoint

/-- An index-one Morse--Smale trajectory space has finitely many trajectories when the Morse
function has compact sublevels. A trajectory is represented by its unique point at the level
`f = c`, where `f q < c < f p`. -/
theorem finite_unstableSet_inter_stableSet_inter_level_of_isCompact_sublevel
    (hfs : ContDiff ℝ 2 f) (hf : LipschitzWith K (∇ f))
    (hM : HasNondegenerateCriticalPointsOn f univ)
    (hcompact : ∀ c : ℝ, IsCompact {z | f z ≤ c}) {p q : E}
    (hp : IsNondegenerateCriticalPoint f p) (hq : IsNondegenerateCriticalPoint f q)
    (hind : morseIndex f p = morseIndex f q + 1) {c : ℝ} (hc : f q < c ∧ c < f p)
    (htr : IsMorseSmale f hf) :
    (Flow.unstableSet (negativeGradientFlow f hf) p ∩
      Flow.stableSet (negativeGradientFlow f hf) q ∩ {z | f z = c}).Finite := by
  apply hp.finite_unstableSet_inter_stableSet_inter_level hq hfs hf hind hc
    (fun {_} _ ↦ exists_stableSet_of_isCompact_sublevel hfs hf hM _ (hcompact _))
    (fun {_} hy ↦ exists_unstableSet_of_mem_closure_unstableSet_of_isCompact_sublevel
      hfs hf hM (hcompact _) hy) htr (hcompact c)
  intro z hz
  exact hz.2.le

end TauCeti
