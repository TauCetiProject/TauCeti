/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Morse.Breaking
import TauCeti.Analysis.Calculus.Gradient
import TauCeti.Analysis.Calculus.Morse.LevelSlice
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

The same convergence facts control the levels of an unstable set. A limit of points of `W^u(p)`
lies in the unstable set of `p` itself or of a critical point of strictly smaller value, so the
level `W^u(p) ∩ {f = c}` is compact when no critical value lies in `[c, f p)`. When no critical
value lies in `[c₁, c)`, the forward orbits of a compact set of noncritical points of value at
most `c` all descend below `c₁` after a common time. These are the dynamical inputs of the
Morse--Smale genericity argument, which perturbs `f` on a band below each critical value.

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
  have hmaps : MapsTo (fun t ↦ φ t y) (Ici 0) {z | f z ≤ f y} := by
    intro t ht
    simpa only [Set.mem_ofPred_eq, φ, _root_.Flow.map_zero_apply] using hanti ht
  have hγ : IsIntegralCurveOn (fun t ↦ φ t y) (fun _ x ↦ -∇ f x) (Ici 0) :=
    ((isNegativeGradient_negativeGradientFlow f hf).isIntegralCurve y).isIntegralCurveOn _
  obtain ⟨q, -, hq, hlim⟩ :=
    hγ.exists_tendsto_atTop_of_hasNondegenerateCriticalPointsOn hcompact hmaps
      (hfs.continuous_fderiv (by norm_num)).continuousOn
      (hM.mono (subset_univ _))
  have hq' : fderiv ℝ f q = 0 := by
    rw [← gradient_eq_zero_iff, hq]
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
  have hmaps : MapsTo (fun t ↦ φ t y) (Iic 0) {z | f z ≤ f p} := fun t _ ↦
    (isNegativeGradient_negativeGradientFlow f hf).value_ge_of_mem_closure_unstableSet
      (hfs.differentiable (by norm_num))
      (map_mem_closure (φ.continuous_toFun t) hy (Flow.isInvariant_unstableSet φ p t))
  have hγ : IsIntegralCurveOn (fun t ↦ φ t y) (fun _ x ↦ -∇ f x) (Iic 0) :=
    ((isNegativeGradient_negativeGradientFlow f hf).isIntegralCurve y).isIntegralCurveOn _
  obtain ⟨a, -, ha, hlim⟩ :=
    hγ.exists_tendsto_atBot_of_hasNondegenerateCriticalPointsOn hcompact hmaps
      (hfs.continuous_fderiv (by norm_num)).continuousOn
      (hM.mono (subset_univ _))
  have ha' : fderiv ℝ f a = 0 := by
    rw [← gradient_eq_zero_iff, ha]
  exact ⟨a, (hasNondegenerateCriticalPointsOn_iff.mp hM) (mem_univ a) ha',
    Flow.mem_unstableSet.mpr hlim⟩

/-- For a globally Morse function with compact sublevels and Morse--Smale transversality,
a stable-set closure incidence produces a finite chain `x :: l` from `x` to `q` of nonconstant
connecting orbits between nondegenerate critical points. Compactness supplies forward convergence,
and `l.length` is at most `morseIndex f x - morseIndex f q`. -/
theorem exists_isChain_of_mem_closure_stableSet_inter_stableSet_of_isCompact_sublevel
    {q x : E} (hfs : ContDiff ℝ 2 f)
    (hf : LipschitzWith K (∇ f)) (hM : HasNondegenerateCriticalPointsOn f univ)
    (hcompact : ∀ c : ℝ, IsCompact {z | f z ≤ c})
    (hy : (closure (Flow.stableSet (negativeGradientFlow f hf) q) ∩
      Flow.stableSet (negativeGradientFlow f hf) x).Nonempty)
    (htr : IsMorseSmale f hf) :
    ∃ l : List E,
      (x :: l).IsChain (fun a b ↦ a ≠ b ∧
        (Flow.unstableSet (negativeGradientFlow f hf) a ∩
          Flow.stableSet (negativeGradientFlow f hf) b).Nonempty) ∧
      (x :: l).getLast (List.cons_ne_nil _ _) = q ∧
      (∀ a ∈ x :: l, IsNondegenerateCriticalPoint f a) ∧
      l.length + morseIndex f q ≤ morseIndex f x := by
  have ⟨y, _, hy₂⟩ := hy
  obtain ⟨a, ha, hya⟩ := exists_stableSet_of_isCompact_sublevel hfs hf hM y (hcompact _)
  have hx : IsNondegenerateCriticalPoint f x :=
    tendsto_nhds_unique (Flow.mem_stableSet.1 hya) (Flow.mem_stableSet.1 hy₂) ▸ ha
  by_cases hqx : q = x
  · subst hqx
    exact ⟨[], by simp, by simp, by simpa using hx, by simp⟩
  · exact hx.exists_isChain_of_mem_closure_stableSet_inter_stableSet hfs hf hqx hy
      (fun {_} _ ↦ exists_stableSet_of_isCompact_sublevel hfs hf hM _ (hcompact _)) htr

/-- For a globally Morse function with Morse--Smale transversality and compact sublevel at
`f p`, an unstable-set closure incidence produces a finite chain `p :: l` from `p` to `x` of
nonconstant connecting orbits between nondegenerate critical points. Compactness supplies backward
convergence, and `l.length` is at most `morseIndex f p - morseIndex f x`. -/
theorem exists_isChain_of_mem_closure_unstableSet_inter_unstableSet_of_isCompact_sublevel
    {p x : E} (hfs : ContDiff ℝ 2 f)
    (hf : LipschitzWith K (∇ f)) (hM : HasNondegenerateCriticalPointsOn f univ)
    (hcompact : IsCompact {z | f z ≤ f p})
    (hy : (closure (Flow.unstableSet (negativeGradientFlow f hf) p) ∩
      Flow.unstableSet (negativeGradientFlow f hf) x).Nonempty)
    (htr : IsMorseSmale f hf) :
    ∃ l : List E,
      (p :: l).IsChain (fun a b ↦ a ≠ b ∧
        (Flow.unstableSet (negativeGradientFlow f hf) a ∩
          Flow.stableSet (negativeGradientFlow f hf) b).Nonempty) ∧
      (p :: l).getLast (List.cons_ne_nil _ _) = x ∧
      (∀ a ∈ p :: l, IsNondegenerateCriticalPoint f a) ∧
      l.length + morseIndex f x ≤ morseIndex f p := by
  have ⟨y, hy₁, hy₂⟩ := hy
  obtain ⟨a, ha, hya⟩ :=
    exists_unstableSet_of_mem_closure_unstableSet_of_isCompact_sublevel hfs hf hM hcompact hy₁
  have hx : IsNondegenerateCriticalPoint f x :=
    tendsto_nhds_unique (Flow.mem_unstableSet.1 hya) (Flow.mem_unstableSet.1 hy₂) ▸ ha
  by_cases hpx : p = x
  · subst hpx
    exact ⟨[], by simp, by simp, by simpa using hx, by simp⟩
  · exact hx.exists_isChain_of_mem_closure_unstableSet_inter_unstableSet hfs hf hpx hy
      (fun {_} hz ↦ exists_unstableSet_of_mem_closure_unstableSet_of_isCompact_sublevel
        hfs hf hM hcompact hz) htr

/-- An index-one Morse--Smale trajectory space has finitely many trajectories when the Morse
function has compact sublevels. A trajectory is represented by its unique point at the level
`f = c`, where `f q < c < f p`. -/
theorem finite_unstableSet_inter_stableSet_inter_level_of_isCompact_sublevel
    (hfs : ContDiff ℝ 2 f) (hf : LipschitzWith K (∇ f))
    (hM : HasNondegenerateCriticalPointsOn f univ)
    (hcompact : ∀ c : ℝ, IsCompact {z | f z ≤ c}) {p q : E}
    (hind : morseIndex f p = morseIndex f q + 1) {c : ℝ} (hc : f q < c ∧ c < f p)
    (htr : IsMorseSmale f hf) :
    (Flow.unstableSet (negativeGradientFlow f hf) p ∩
      Flow.stableSet (negativeGradientFlow f hf) q ∩ {z | f z = c}).Finite := by
  rcases eq_empty_or_nonempty (Flow.unstableSet (negativeGradientFlow f hf) p ∩
    Flow.stableSet (negativeGradientFlow f hf) q ∩ {z | f z = c}) with hS | ⟨z, hz⟩
  · exact hS ▸ finite_empty
  -- The endpoints of a connecting orbit are rest points, hence critical, hence nondegenerate.
  have hcrit {x : E} (hx : ∀ t, negativeGradientFlow f hf t x = x) :
      IsNondegenerateCriticalPoint f x :=
    hasNondegenerateCriticalPointsOn_iff.1 hM (mem_univ x)
      (gradient_eq_zero_iff.1 ((forall_negativeGradientFlow_eq_self_iff f hf x).1 hx))
  have hp := hcrit (Flow.fixed_of_mem_unstableSet hz.1.1)
  have hq := hcrit (Flow.fixed_of_mem_stableSet hz.1.2)
  apply hp.finite_unstableSet_inter_stableSet_inter_level hq hfs hf hind hc
    (fun {_} _ ↦ exists_stableSet_of_isCompact_sublevel hfs hf hM _ (hcompact _))
    (fun {_} hy ↦ exists_unstableSet_of_mem_closure_unstableSet_of_isCompact_sublevel
      hfs hf hM (hcompact _) hy) htr (hcompact c)
  intro z hz
  exact hz.2.le

/-! ### Levels of unstable sets -/

/-- **Broken limits lower the value.** Let `f` be a globally Morse function whose sublevel at `p`
is compact. If a point of the unstable set of a nondegenerate critical point `a ≠ p` is a limit of
points of the unstable set of `p`, then `f a < f p`. -/
theorem value_lt_of_mem_closure_unstableSet_inter_unstableSet_of_isCompact_sublevel
    (hfs : ContDiff ℝ 2 f) (hf : LipschitzWith K (∇ f))
    (hM : HasNondegenerateCriticalPointsOn f univ) {p a y : E}
    (hcompact : IsCompact {z | f z ≤ f p}) (ha : IsNondegenerateCriticalPoint f a) (hpa : p ≠ a)
    (hy : y ∈ closure (Flow.unstableSet (negativeGradientFlow f hf) p) ∩
      Flow.unstableSet (negativeGradientFlow f hf) a) :
    f a < f p := by
  let φ := negativeGradientFlow f hf
  have hφ := isNegativeGradient_negativeGradientFlow f hf
  have hd : Differentiable ℝ f := hfs.differentiable (by norm_num)
  obtain ⟨b, z, -, hba, hz, hzb⟩ :=
    exists_prevCriticalPoint_of_mem_closure_unstableSet_inter_unstableSet ha hfs hf hpa hy
      fun hz ↦ exists_unstableSet_of_mem_closure_unstableSet_of_isCompact_sublevel hfs hf hM
        hcompact hz
  have hbp : f b ≤ f p :=
    le_of_tendsto (hd.continuous.continuousAt.tendsto.comp (Flow.mem_unstableSet.1 hzb))
      (Eventually.of_forall fun t ↦ hφ.value_ge_of_mem_closure_unstableSet hd
        (map_mem_closure (φ.continuous_toFun t) hz.1 (Flow.isInvariant_unstableSet φ p t)))
  exact (hφ.value_lt_of_mem_unstableSet_inter_stableSet (fun _ ↦ hd _)
    hd.continuous.continuousAt hd.continuous.continuousAt hba ⟨hzb, hz.2⟩).trans_le hbp

/-- **The levels of an unstable set are compact.** Let `f` be a globally Morse function whose
sublevel at `p` is compact. If no critical value lies in `[c, f p)`, then the points of the
unstable set of `p` at the level `c` form a compact set. -/
theorem isCompact_unstableSet_inter_level_of_isCompact_sublevel
    (hfs : ContDiff ℝ 2 f) (hf : LipschitzWith K (∇ f))
    (hM : HasNondegenerateCriticalPointsOn f univ) {p : E}
    (hcompact : IsCompact {z | f z ≤ f p}) {c : ℝ}
    (hc : ∀ a, IsNondegenerateCriticalPoint f a → f a < f p → f a < c) :
    IsCompact (Flow.unstableSet (negativeGradientFlow f hf) p ∩ {z | f z = c}) := by
  have hφ := isNegativeGradient_negativeGradientFlow f hf
  have hd : Differentiable ℝ f := hfs.differentiable (by norm_num)
  refine hcompact.of_isClosed_subset (isClosed_of_closure_subset fun y hy ↦ ?_)
    fun z hz ↦ hφ.value_ge_of_mem_closure_unstableSet hd (subset_closure hz.1)
  have hyc : f y = c := (isClosed_eq hfs.continuous continuous_const).closure_subset
    (closure_mono inter_subset_right hy)
  have hyu := closure_mono inter_subset_left hy
  obtain ⟨a, ha, hya⟩ :=
    exists_unstableSet_of_mem_closure_unstableSet_of_isCompact_sublevel hfs hf hM hcompact hyu
  refine ⟨?_, hyc⟩
  obtain rfl | hpa := eq_or_ne p a
  · exact hya
  have hle : f y ≤ f a :=
    hφ.value_ge_of_mem_unstableSet hya (fun _ ↦ hd _) hd.continuous.continuousAt
  exact absurd (hc a ha (value_lt_of_mem_closure_unstableSet_inter_unstableSet_of_isCompact_sublevel
    hfs hf hM hcompact ha hpa ⟨hyu, hya⟩)) (hyc ▸ hle).not_gt

/-- **Uniform descent below a regular band.** Let `f` be a globally Morse function whose sublevel
at `c` is compact, with no critical value in `[c₁, c)`. The forward orbits of a compact set of
noncritical points of value at most `c` all lie below `c₁` after a common time. -/
theorem exists_forall_value_negativeGradientFlow_lt_of_isCompact_sublevel
    (hfs : ContDiff ℝ 2 f) (hf : LipschitzWith K (∇ f))
    (hM : HasNondegenerateCriticalPointsOn f univ) {c₁ c : ℝ}
    (hcompact : IsCompact {z | f z ≤ c})
    (hc : ∀ a, IsNondegenerateCriticalPoint f a → f a < c → f a < c₁)
    {C : Set E} (hC : IsCompact C) (hCc : ∀ x ∈ C, f x ≤ c) (hCcrit : ∀ x ∈ C, ∇ f x ≠ 0) :
    ∃ T, ∀ x ∈ C, ∀ t, T ≤ t → f (negativeGradientFlow f hf t x) < c₁ := by
  let φ := negativeGradientFlow f hf
  have hφ := isNegativeGradient_negativeGradientFlow f hf
  have hd : ∀ x t, DifferentiableAt ℝ f (φ t x) := fun _ _ ↦ hfs.differentiable (by norm_num) _
  have hexit : ∀ x ∈ C, ∃ t > 0, φ t x ∈ {z | f z < c₁} := by
    intro x hx
    obtain ⟨q, hq, hxq⟩ := exists_stableSet_of_isCompact_sublevel hfs hf hM x
      (hcompact.of_isClosed_subset (isClosed_le hfs.continuous continuous_const)
        fun _ hz ↦ le_trans hz (hCc x hx))
    have hmove : ∃ t, φ t x ≠ x := by
      by_contra! hfix
      exact hCcrit x hx ((forall_negativeGradientFlow_eq_self_iff f hf x).1 hfix)
    have hqx : f q < c := calc
      f q ≤ f (φ 1 x) := hφ.value_le_of_mem_stableSet (Flow.isInvariant_stableSet φ q 1 hxq)
        (fun t ↦ hd _ t) hfs.continuous.continuousAt
      _ < f (φ 0 x) := hφ.orbit_strictAnti_of_nonconstant (hd x) hmove zero_lt_one
      _ ≤ c := by simpa using hCc x hx
    exact (((hfs.continuous.continuousAt.tendsto.comp (Flow.mem_stableSet.1 hxq)).eventually
      (gt_mem_nhds (hc q hq hqx))).and (eventually_gt_atTop 0)).exists.imp fun _ h ↦ ⟨h.2, h.1⟩
  obtain ⟨T, hT⟩ := φ.exists_forall_exists_mem_Ioo_apply_mem hC
    (isOpen_lt hfs.continuous continuous_const) hexit
  refine ⟨T, fun x hx t ht ↦ ?_⟩
  obtain ⟨σ, hσ, hσc⟩ := hT x hx
  exact (negativeGradientFlow_orbit_antitone f hf x (hσ.2.le.trans ht)).trans_lt hσc

end TauCeti
