/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Gluing.Broken
import TauCeti.Analysis.Calculus.Morse.Gluing.Centre
import TauCeti.Analysis.Normed.Lp.ProdLp
import TauCeti.Topology.Algebra.Order.Field
import TauCeti.Dynamics.Flow.Lyapunov
import TauCeti.Data.Set.Function

/-!
# Half-open gluing charts into a transverse set

Let `f` be a Morse function on a compact boundaryless manifold `M` of dimension `n`, `X` a
pseudo-gradient adapted to `f` satisfying the Morse–Smale condition, `a₁` a point of a trajectory
from a critical point `p` to a critical point `q` with `ind p = ind q + 1`, and `y` a point of the
unstable manifold `W^u(q)`, possibly `q` itself. Let `Z` be a set of dimension `n - ind q` through
`y`, flattened
near `y` by a chart of the maximal atlas and transverse to `W^u(q)` at `y`. Then `W^u(p) ∩ Z` is
expected to be one-dimensional, and its points whose orbits follow the trajectory through `a₁`
accumulate at `y` (`IsMorseSmale.exists_mem_unstableSet_inter_flow_mem_of_isSliceChart`). This
file shows that they form a half-open arc ending at `y`.

Record a point `x` of `W^u(p) ∩ Z` by the pair `(w, x)`, where `w` is the point of the orbit of
`x` on the level of `a₁`, and the broken configuration by `(a₁, y)`. The main theorem
(`IsMorseSmale.exists_homeomorph_Ico_of_isSliceChart`) shows that `(a₁, y)` has a neighbourhood
among these pairs homeomorphic to a half-open interval `[0, δ)`. Two cases are the boundary charts
of compactified one-dimensional moduli spaces:

* **Broken trajectories.** For `Z` the level cut `W^s(r) ∩ {f = f a₂}` through a point `a₂` of a
  trajectory from `q` to `r`, with `ind q = ind r + 1`, the pairs are the trajectories from `p` to
  `r` recorded on two levels, and the chart is the boundary chart of the compactified space of
  index-two trajectories at a broken trajectory
  (`IsMorseSmale.exists_homeomorph_Ico_of_mem_unstableSet_inter_stableSet`), whose boundary points
  therefore come in pairs (`TauCeti.even_ncard_of_forall_exists_homeomorph_Ico`).
* **Morse–Smale pairs.** For `Z` the stable manifold of a critical point of a second
  pseudo-gradient, the chart is the boundary chart at a configuration breaking at the source of the
  one-dimensional intersections of a Morse–Smale pair, the moduli spaces of continuation maps
  (`IsMorseSmalePair.exists_homeomorph_Ico_of_source` and, by reversing both fields,
  `IsMorseSmalePair.exists_homeomorph_Ico_of_target` in
  `TauCeti.Geometry.Manifold.Morse.Gluing.Pair`). Here `y = q` occurs, for instance for the
  identity continuation, where `Z` is the stable manifold of `q` itself.

For `y ≠ q` the proof glues in a Morse box at `q`
(`TauCeti.IsAdaptedPseudoGradient.exists_morseBox_of_broken_of_isSliceChart`) with entrance
point `y₁` on the trajectory through `a₁` and exit point `y₂` on the orbit of `y`. The level cut
of `W^u(p)` through `y₁` and the set `Z' = flow (-T) ⁻¹' Z` through `y₂` are transverse discs
(`IsMorseSmale.exists_unstableSet_level_param` and
`TauCeti.exists_param_of_span_mtangentConeAt_sup_eq_top`), and the model gluing
(`TauCeti.exists_homeomorph_closure_splitGluingPairs_of_hasStrictFDerivAt`) joins them by a
half-open arc of entrance and exit points. Unlike a stable manifold, `Z'` is not invariant under the
flow, so the point of `Z'` on an orbit must be recovered from its exit point. Since `Z'` is
transverse to `W^u(q)` and of complementary dimension, the velocity `X y₂` is not tangent to it
(`TauCeti.IsAdaptedPseudoGradient.notMem_span_mtangentConeAt_of_isSliceChart`), so near a regular
point an orbit meets `Z'` at most once
(`TauCeti.IsAdaptedPseudoGradient.eventually_eq_zero_of_flow_eq_of_isSliceChart`; both are in
`TauCeti.Geometry.Manifold.Morse.Stable.Transversality`).
Hence the flow embeds `[-1, 1] × K` for a compact piece `K` of `Z'`, and the point of `Z'` depends
continuously on the exit point.

For `y = q` the orbits of the glued points never leave the box. There `Z` is a graph
`u ↦ (u, k u)` through the centre, and the trace of `W^u(p)` on the entrance face a graph
`v ↦ (g v, v)`. The orbit through `(g v, v)` meets the graph of `k` at time `T` exactly when `v`
solves the gluing equation `l • k (l • g v) = v` at the rate `l = e^{-T}`
(`TauCeti.splitQuadraticFlow_snd_eq_iff_smul_comp_smul_eq`). For small `l` this equation is a
contraction, whose solution `v l` depends continuously on `l`, with `v 0 = 0`
(`TauCeti.eventually_exists_continuousOn_smul_comp_smul_eq_iff`). The arc is
`l ↦ ((g (v l), v l), (l • g (v l), k (l • g (v l))))` read on `M`; the rate is read off the point
of `Z` as `‖u‖ / ε`. Conversely, a point of `W^u(p) ∩ Z` near `q` and the entrance point of its
orbit near the trajectory through `a₁` lie on one orbit crossing the entrance face once
(`TauCeti.IsAdaptedPseudoGradient.eq_of_flow_eq_of_norm_fst_eq`), so they are a point of the arc.

## Main results

In the namespace `TauCeti.IsAdaptedPseudoGradient`:

* `IsMorseSmale.exists_homeomorph_Ico_of_isSliceChart`: the half-open gluing chart into a
  transverse set.
* `IsMorseSmale.exists_homeomorph_Ico_of_mem_unstableSet_inter_stableSet`: for consecutive
  indices, a broken trajectory has a neighbourhood homeomorphic to `[0, δ)` among the unbroken
  trajectories recorded on two levels.

## References

* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapter 3 (gluing of broken trajectories, using a pseudo-gradient that is linear near the
  critical points).
* M. Hutchings, *Lecture notes on Morse homology (with an eye towards Floer theory and
  pseudoholomorphic curves)*, 2002, §4.1 (the continuation map is a chain map, by counting the
  ends of the one-dimensional moduli spaces of continuation trajectories).
-/

public section

open Filter Function Metric Set Topology
open scoped ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [T2Space M] {f : M → ℝ} {X : (x : M) → TangentSpace 𝓘(ℝ, E) x}

/-- A gluing parameter `r₁ ≤ min r₀ 1` small enough that `n u² < ε²` for every `u ∈ [0, r₁ ε]`. -/
private theorem exists_pos_forall_mul_sq_lt_sq {n ε r₀ : ℝ} (hn : 0 ≤ n) (hε : 0 < ε)
    (hr₀ : 0 < r₀) :
    ∃ r₁, 0 < r₁ ∧ r₁ ≤ r₀ ∧ r₁ ≤ 1 ∧ ∀ u, 0 ≤ u → u ≤ r₁ * ε → n * u ^ 2 < ε ^ 2 := by
  set r₁ := min r₀ (1 / (n + 1))
  have hr₁ : 0 < r₁ := lt_min hr₀ (by positivity)
  have hr₁n : n * (r₁ * ε) ^ 2 < ε ^ 2 := by
    have h₁ : r₁ * (n + 1) ≤ 1 := (le_div_iff₀ (by positivity)).1 (min_le_right _ _)
    have h₂ : 0 < r₁ * ε := mul_pos hr₁ hε
    have h₃ : r₁ * ε * (n + 1) ≤ ε := by nlinarith
    have h₄ : (r₁ * ε * (n + 1)) ^ 2 ≤ ε ^ 2 := pow_le_pow_left₀ (by positivity) h₃ 2
    nlinarith [mul_pos h₂ h₂]
  exact ⟨r₁, hr₁, min_le_left _ _, (min_le_right _ _).trans
    ((div_le_one (by positivity)).2 (by linarith)), fun u hu hu' ↦
    lt_of_le_of_lt (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hu hu' 2) hn) hr₁n⟩

namespace IsAdaptedPseudoGradient

/-- **The point of a transverse set on an orbit depends continuously on the orbit.** Let `Z` be a
set flattened near a point `y ≠ q` of `W^u(q)` by a chart of the maximal atlas, of dimension
`n - ind q` and transverse to `W^u(q)` at `y`, so that `X y` is not tangent to `Z`. Then inside any
neighbourhood `V` of `y` there is a neighbourhood `C` of `y` such that the flow for times in
`[-1, 1]` is injective on `C ∩ Z`, with an inverse `π`, continuous on the image, which recovers
the point of `C ∩ Z`. -/
private theorem exists_continuousOn_flow_inv (hX : IsAdaptedPseudoGradient f X)
    (hf : IsMorse 𝓘(ℝ, E) f) {q y : M} {Z : Set M} {L : Submodule ℝ E}
    {φZ : OpenPartialHomeomorph M E} (hφZ : φZ ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M)
    (hZ : IsSliceChart φZ (L : Set E) Z) (hyφZ : y ∈ φZ.source) (hyZ : y ∈ Z)
    (hy : y ∈ hX.flow.unstableSet q) (hyc : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f y ≠ 0)
    (hdim : Module.finrank ℝ L + manifoldMorseIndex 𝓘(ℝ, E) f q = Module.finrank ℝ E)
    (htr : Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) Z y) ⊔
      Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX.flow.unstableSet q) y) = ⊤)
    {V : Set M} (hV : V ∈ 𝓝 y) :
    ∃ C ∈ 𝓝 y, C ⊆ V ∧ ∃ π : M → M,
      ContinuousOn π ((fun x : ℝ × M ↦ hX.flow x.1 x.2) '' (Icc (-1 : ℝ) 1 ×ˢ (C ∩ Z))) ∧
      ∀ t ∈ Icc (-1 : ℝ) 1, ∀ w ∈ C ∩ Z, π (hX.flow t w) = w := by
  have hL : IsClosed (L : Set E) := Submodule.isClosed_of_finiteDimensional _
  have hXZ := hX.notMem_span_mtangentConeAt_of_isSliceChart hf hφZ hZ hyφZ hyZ hy hyc hdim htr
  obtain ⟨u₀, hu₀, v₀, hv₀, huv⟩ :=
    mem_nhds_prod_iff.1 (hX.eventually_eq_zero_of_flow_eq_of_isSliceChart hφZ hZ hyφZ hyZ hXZ)
  -- A closed neighbourhood `C` of `y` in the source of `φZ`; then `C ∩ Z` is compact.
  obtain ⟨C, hC, hCc, hCsub⟩ :=
    exists_mem_nhds_isClosed_subset (inter_mem (inter_mem (inter_mem hu₀ hv₀)
      (φZ.open_source.mem_nhds hyφZ)) hV)
  have hK : IsClosed (C ∩ Z) := by
    have hK' : C ∩ Z = C ∩ φZ ⁻¹' L :=
      ext fun w ↦ and_congr_right fun hwC ↦ hZ.mem_iff (hCsub hwC).1.2
    rw [hK']
    exact ContinuousOn.preimage_isClosed_of_isClosed
      (φZ.continuousOn.mono fun w hw ↦ (hCsub hw).1.2) hCc hL
  -- The flow on `[-1, 1] × (C ∩ Z)` is a continuous injection of a compact space, hence an
  -- embedding.
  set K : Set (ℝ × M) := Icc (-1 : ℝ) 1 ×ˢ (C ∩ Z)
  have : CompactSpace K := isCompact_iff_compactSpace.1 (isCompact_Icc.prod hK.isCompact)
  set Θ : K → M := fun x ↦ hX.flow x.val.1 x.val.2
  have hΘc : Continuous Θ := hX.flow.cont'.comp continuous_subtypeVal
  have hΘi : Injective Θ := by
    rintro ⟨⟨t, w⟩, ht, hwC, hwZ⟩ ⟨⟨t', w'⟩, ht', hw'C, hw'Z⟩ hΘ
    simp only [Θ] at hΘ
    have hww' : hX.flow (t - t') w = w' := by
      rw [sub_eq_add_neg, add_comm, Flow.map_add, hΘ, ← Flow.map_add, neg_add_cancel,
        Flow.map_zero_apply]
    have h0 := huv (mk_mem_prod (hCsub hwC).1.1.1 (hCsub hw'C).1.1.2) hwZ hw'Z _ hww'
    have htt : t = t' := by linarith
    subst htt
    rw [sub_self, Flow.map_zero_apply] at hww'
    subst hww'
    rfl
  set hom := (hΘc.isClosedEmbedding hΘi).isEmbedding.toHomeomorph
  have hrange : range Θ = (fun x : ℝ × M ↦ hX.flow x.1 x.2) '' K := by
    ext x
    exact ⟨fun ⟨k, hk⟩ ↦ ⟨k.val, k.property, hk⟩, fun ⟨k, hk, hkx⟩ ↦ ⟨⟨k, hk⟩, hkx⟩⟩
  classical
  refine ⟨C, hC, fun w hw ↦ (hCsub hw).2, fun x ↦ if h : x ∈ range Θ then
    (hom.symm ⟨x, h⟩).val.2 else x, ?_, fun t ht w hw ↦ ?_⟩
  · rw [← hrange, continuousOn_iff_continuous_domRestrict]
    refine (continuous_snd.comp (continuous_subtypeVal.comp hom.symm.continuous)).congr
      fun x ↦ ?_
    simp only [domRestrict_apply, x.property, ↓reduceDIte]
    rfl
  · have hk : hX.flow t w ∈ range Θ := ⟨⟨(t, w), ht, hw⟩, rfl⟩
    have : hom.symm ⟨_, hk⟩ = ⟨(t, w), ht, hw⟩ := hom.symm_apply_eq.2 (Subtype.ext rfl)
    simp only [hk, ↓reduceDIte, this]

/-- **A transverse set as a disc in split coordinates.** Let `φ` be a Morse chart at `q` in which,
near a point `y` of `W^u(q)`, the unstable set of `q` lies in the plane where the first split
coordinate `u` vanishes, and let `Z` be a set through `y` of dimension `n - ind q`, flattened near
`y` by a chart of the maximal atlas and transverse to `W^u(q)` at `y`. Then `Z` near `y` is a disc
`ι : L → M` with `ι 0 = y`, reaching every point of `Z` near `y` from small parameters, whose split
coordinates are strictly differentiable at `0` with invertible `u`-component. -/
private theorem exists_param_splitCoord_of_isSliceChart (hX : IsAdaptedPseudoGradient f X)
    {q y : M} (φ : MorseChart E f q) (hyφ : y ∈ φ.toChart.source)
    (hyu : y ∈ hX.flow.unstableSet q)
    (hloc : ∀ᶠ w in 𝓝 y, w ∈ hX.flow.unstableSet q →
      (φ.splitCoord (φ.coord (φ.toChart w))).fst = 0)
    {Z : Set M} {L : Submodule ℝ E} {φZ : OpenPartialHomeomorph M E}
    (hφZ : φZ ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M) (hZ : IsSliceChart φZ (L : Set E) Z)
    (hyφZ : y ∈ φZ.source) (hyZ : y ∈ Z)
    (hdim : Module.finrank ℝ L + manifoldMorseIndex 𝓘(ℝ, E) f q = Module.finrank ℝ E)
    (htr : Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) Z y) ⊔
      Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX.flow.unstableSet q) y) = ⊤) :
    ∃ (ι : L → M)
      (χ' : L →L[ℝ] WithLp 2 (({i // φ.weight i = 1} → ℝ) × ({i // ¬φ.weight i = 1} → ℝ))),
      ι 0 = y ∧ ContinuousAt ι 0 ∧ (∀ᶠ z in 𝓝 0, ι z ∈ Z) ∧
      HasStrictFDerivAt (fun z ↦ φ.splitCoord (φ.coord (φ.toChart (ι z)))) χ' 0 ∧
      (WithLp.fstL 2 ℝ ({i // φ.weight i = 1} → ℝ) ({i // ¬φ.weight i = 1} → ℝ) ∘L
        χ').IsInvertible ∧
      ∀ V ∈ 𝓝 (0 : L), ∀ᶠ w in 𝓝 y, w ∈ Z → ∃ z ∈ V, ι z = w := by
  set P := WithLp.fstL 2 ℝ ({i // φ.weight i = 1} → ℝ) ({i // ¬φ.weight i = 1} → ℝ) ∘L
    φ.splitCoordL.toContinuousLinearMap
  have hPs : Function.Surjective P := fun b ↦ by
    obtain ⟨u, hu⟩ := φ.splitCoordL.surjective (WithLp.toLp 2 (b, 0))
    exact ⟨u, by simp [P, hu]⟩
  have hL : IsClosed (L : Set E) := Submodule.isClosed_of_finiteDimensional _
  have hdimZ : Module.finrank ℝ (Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) Z y)) =
      Module.finrank ℝ L := hZ.finrank_span_mtangentConeAt (by simp) hφZ hL hyφZ hyZ
  obtain ⟨ι, ι', hι0, hι, hιs, hd, hinv, hexh⟩ :=
    exists_param_of_span_mtangentConeAt_sup_eq_top (by simp) hφZ hZ hyφZ hyZ hyu htr
      (by have := φ.finrank_fst_splitCoord_add_manifoldMorseIndex; rw [hdimZ]; omega)
      φ.mem_maximalAtlas hyφ hPs (by simpa [P] using hloc)
  exact ⟨ι, (φ.splitCoordL : E →L[ℝ] _) ∘L ι', hι0, hι, hιs,
    by simpa using φ.splitCoordL.hasStrictFDerivAt.comp 0 hd,
    by rwa [← ContinuousLinearMap.comp_assoc], hexh⟩

/-- **The model gluing arc into a transverse set, on the manifold.** For a trajectory from `p`
through `a₁` to `q`, with `ind p = ind q + 1`, and a set `Z` of dimension `n - ind q` flattened
near a point `y ≠ q` of `W^u(q)` and transverse to `W^u(q)` there, there are points `flow T₁ a₁`
and `flow T₂ y` and a continuous arc `B` in `M × M` starting at this pair, along which, for
`s ≠ 0`, `(B s).1` lies in `W^u(p)` and flows to the point `(B s).2` of `flow (-T₂) ⁻¹' Z`,
different `s` giving different orbits. Every pair of such points near the start, the first on the
level of `flow T₁ a₁`, is reached by the arc below its end. -/
private theorem IsMorseSmale.exists_transverseGluingArc {hX : IsAdaptedPseudoGradient f X}
    (h : hX.IsMorseSmale) (hf : IsMorse 𝓘(ℝ, E) f) {p q a₁ y : M} {Z : Set M}
    (hpq : manifoldMorseIndex 𝓘(ℝ, E) f p = manifoldMorseIndex 𝓘(ℝ, E) f q + 1)
    (ha₁ : a₁ ∈ hX.flow.unstableSet p ∩ hX.flow.stableSet q) (hy : y ∈ hX.flow.unstableSet q)
    (hyq : y ≠ q) {L : Submodule ℝ E} {φZ : OpenPartialHomeomorph M E}
    (hφZ : φZ ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M) (hZ : IsSliceChart φZ (L : Set E) Z)
    (hyφZ : y ∈ φZ.source) (hyZ : y ∈ Z)
    (hdim : Module.finrank ℝ L + manifoldMorseIndex 𝓘(ℝ, E) f q = Module.finrank ℝ E)
    (htr : Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) Z y) ⊔
      Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX.flow.unstableSet q) y) = ⊤) :
    ∃ (T₁ T₂ δ : ℝ) (hδ : 0 < δ) (B : Icc (0 : ℝ) δ → M × M), Continuous B ∧
      B ⟨0, left_mem_Icc.2 hδ.le⟩ = (hX.flow T₁ a₁, hX.flow T₂ y) ∧
      (∀ s : Icc (0 : ℝ) δ, (s : ℝ) ≠ 0 → (B s).1 ∈ hX.flow.unstableSet p ∧
        hX.flow (-T₂) (B s).2 ∈ Z ∧ ∃ t, hX.flow t (B s).1 = (B s).2) ∧
      (∀ s, f (B s).2 < f q) ∧
      (∀ s s' : Icc (0 : ℝ) δ, (s : ℝ) ≠ 0 → (s' : ℝ) ≠ 0 → ∀ t,
        hX.flow t (B s).1 = (B s').1 → s = s') ∧
      ∀ᶠ w : M × M in 𝓝 (hX.flow T₁ a₁, hX.flow T₂ y),
        w.1 ∈ hX.flow.unstableSet p → f w.1 = f (hX.flow T₁ a₁) → hX.flow (-T₂) w.2 ∈ Z →
        (∃ t, hX.flow t w.1 = w.2) →
        ∃ s : Icc (0 : ℝ) δ, (s : ℝ) < δ ∧ (∃ t, hX.flow t w.1 = (B s).1) ∧ w.2 = (B s).2 := by
  -- Plan: choose a Morse box at `q` with entrance point `y₁` on the trajectory through `a₁` and
  -- exit point `y₂` on the orbit of `y`. Glue the level disc of `W^u(p)` through `y₁` to the disc
  -- of `Z' = flow (-T₂) ⁻¹' Z` through `y₂`. The second point of the arc is the point of `Z'` on
  -- the orbit of the exit point, which depends continuously on it: an orbit meets `Z'` at most
  -- once near `y₂`, so following the flow for bounded times embeds a compact piece of `Z'`.
  have hpq' : p ≠ q := by rintro rfl; omega
  obtain ⟨r, φ, ε, ρ, T₁, T₂, y₁, y₂, φ', hqr, hφ, hε, hερ, hε₂, hloc, hT₁, hT₂, hy₁φ, hy₂φ, hy₁s,
    hy₁ε, hy₂u, hy₂ε, hy₁, hy₂, hφ', hZ', hy₂φ', hy₂Z, htr'⟩ :=
    hX.exists_morseBox_of_broken_of_isSliceChart hf hpq' ha₁ hy hyq hφZ hZ hyφZ hyZ htr
  set Φ : M → WithLp 2 (({i // φ.weight i = 1} → ℝ) × ({i // ¬φ.weight i = 1} → ℝ)) :=
    fun w ↦ φ.splitCoord (φ.coord (φ.toChart w)) with hΦdef
  set Ψ : WithLp 2 (({i // φ.weight i = 1} → ℝ) × ({i // ¬φ.weight i = 1} → ℝ)) → M :=
    fun z ↦ φ.toChart.symm (φ.coord.symm (φ.splitCoord.symm z)) with hΨdef
  have hΨΦ : ∀ w ∈ φ.toChart.source, Ψ (Φ w) = w := fun w hw ↦ by
    simp only [hΨdef, hΦdef, LinearEquiv.symm_apply_apply, φ.toChart.left_inv hw]
  have hε₁ : ∀ z, ‖z‖ ≤ ε → φ.coord.symm z ∈ φ.toChart.target := fun z hz ↦
    hε₂ z (by linarith)
  have hfa₁ := hX.mem_Ioo_of_mem_unstableSet_inter_stableSet hpq' ha₁
  have hfy₂ := hX.mem_Ioo_of_mem_unstableSet_inter_stableSet hqr hy₂
  obtain ⟨hA₁, hA₂, hy₁κ, hy₂κ⟩ :=
    hX.eventually_of_morseBox φ hε hερ hloc hy₁φ hy₂φ hy₁s hy₁ε hy₂u hy₂ε
  have hloc₁ : ∀ᶠ w in 𝓝 y₁, w ∈ hX.flow.stableSet q → (Φ w).snd = 0 :=
    hA₁.mono fun w hw ↦ hw.2.2.2.2.1
  have hloc₂ : ∀ᶠ w in 𝓝 y₂, w ∈ hX.flow.unstableSet q → (Φ w).fst = 0 :=
    hA₂.mono fun w hw ↦ hw.2.2.2.2.1
  set U := {w | w ∈ φ.toChart.source ∧ ‖(Φ w).fst‖ < 2 * ε ∧ ‖(Φ w).snd‖ < ε}
  set V := {w | w ∈ φ.toChart.source ∧ ‖(Φ w).fst‖ < ε ∧ ‖(Φ w).snd‖ < 2 * ε}
  have hU : U ∈ 𝓝 y₁ := hA₁.mono fun w ⟨h₁, _, h₂, h₃, _⟩ ↦ ⟨h₁, h₂, h₃⟩
  have hV : V ∈ 𝓝 y₂ := hA₂.mono fun w ⟨h₁, _, h₂, h₃, _⟩ ↦ ⟨h₁, h₃, h₂⟩
  -- The transverse set carried by the flow to the exit point.
  set Z' := hX.flow (-T₂) ⁻¹' Z
  -- Near `y₂`, the point of `Z'` on an orbit depends continuously on the orbit.
  have hy₂c : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f y₂ ≠ 0 :=
    hX.mfderiv_ne_zero_of_mem_unstableSet_inter_stableSet hqr hy₂
  have hΦc : ContinuousAt Φ y₂ := φ.continuousAt_splitCoord_coord_toChart hy₂φ
  have hexit : ContinuousAt (fun w ↦ splitExitTime ε (Φ w)) y₂ := by
    simp only [splitExitTime_def]
    refine (Real.continuousAt_log ?_).comp (continuousAt_const.div
      ((WithLp.continuous_snd 2 _ _).norm.continuousAt.comp hΦc) ?_)
    · rw [hy₂ε, div_self hε.ne']; exact one_ne_zero
    · rw [hy₂ε]; exact hε.ne'
  have hexit₀ : splitExitTime ε (Φ y₂) = 0 := by
    rw [splitExitTime_def, hy₂ε, div_self hε.ne', Real.log_one]
  obtain ⟨C, hC, hCV, π, hπ, hπeq⟩ := hX.exists_continuousOn_flow_inv hf hφ' hZ' hy₂φ' hy₂Z hy₂.1
    hy₂c hdim htr' (inter_mem (inter_mem hV
      (hX.mdifferentiable.continuous.continuousAt.eventually (gt_mem_nhds hfy₂.2)))
      (hexit.eventually (Ioo_mem_nhds (show (-1 : ℝ) < splitExitTime ε (Φ y₂) by simp [hexit₀])
        (show splitExitTime ε (Φ y₂) < 1 by simp [hexit₀]))))
  have hCm : ∀ w ∈ C, w ∈ V ∧ f w < f q ∧ splitExitTime ε (Φ w) ∈ Ioo (-1 : ℝ) 1 :=
    fun w hw ↦ ⟨(hCV hw).1.1, (hCV hw).1.2, (hCV hw).2⟩
  set R := (fun x : ℝ × M ↦ hX.flow x.1 x.2) '' (Icc (-1 : ℝ) 1 ×ˢ (C ∩ Z'))
  have hπR : ∀ x ∈ R, π x ∈ C ∩ Z' ∧ ∃ t, hX.flow t (π x) = x := by
    rintro _ ⟨⟨t, w⟩, ⟨ht, hw⟩, rfl⟩
    rw [hπeq t ht w hw]
    exact ⟨hw, t, rfl⟩
  -- A disc in the level cut of `W^u(p)` through `y₁` and a disc in `Z'` through `y₂`.
  obtain ⟨F₁, ι₁, ψ', hι₁0, hι₁, hι₁s, hψ, hψ', hexh₁⟩ :=
    h.exists_unstableSet_level_param hf hpq φ hy₁ hy₁φ hloc₁
  obtain ⟨ι₂, χ', hι₂0, hι₂, hι₂s, hχ, hχ', hexh₂⟩ :=
    hX.exists_param_splitCoord_of_isSliceChart φ hy₂φ hy₂.1 hloc₂ hφ' hZ' hy₂φ' hy₂Z hdim htr'
  have hψ₀ : Φ (ι₁ 0) = WithLp.toLp 2 ((Φ y₁).fst, 0) := by
    rw [hι₁0, ← hloc₁.self_of_nhds hy₁.2]
    rfl
  have hχ₀ : Φ (ι₂ 0) = WithLp.toLp 2 (0, (Φ y₂).snd) := by
    rw [hι₂0, ← hloc₂.self_of_nhds hy₂.1]
    rfl
  have hΦy₁ : WithLp.toLp 2 ((Φ y₁).fst, 0) = Φ y₁ :=
    WithLp.ofLp_injective 2 (Prod.ext (by simp) (by simpa using hy₁s.symm))
  have hΦy₂ : WithLp.toLp 2 (0, (Φ y₂).snd) = Φ y₂ :=
    WithLp.ofLp_injective 2 (Prod.ext (by simpa using hy₂u.symm) (by simp))
  -- Parameters near `0` whose points lie in the box and in the prescribed sets.
  set U' : Set F₁ := {z | ι₁ z ∈ U ∧ ι₁ z ∈ hX.flow.unstableSet p ∧ f (ι₁ z) = f y₁}
  set V' : Set L := {z | ι₂ z ∈ C ∧ ι₂ z ∈ Z'}
  have hU' : U' ∈ 𝓝 0 :=
    (Filter.Eventually.and (hι₁.preimage_mem_nhds (by rwa [hι₁0])) hι₁s).mono
      fun z ⟨h₁, h₂⟩ ↦ ⟨h₁, h₂⟩
  have hV' : V' ∈ 𝓝 0 :=
    (Filter.Eventually.and (hι₂.preimage_mem_nhds (by rwa [hι₂0])) hι₂s).mono
      fun z ⟨h₁, h₂⟩ ↦ ⟨h₁, h₂⟩
  obtain ⟨r₀, hr₀, g, k, ⟨e, he, he₀⟩, hcl, hpairs, hexh⟩ :=
    exists_homeomorph_closure_splitGluingPairs_of_hasStrictFDerivAt hψ hψ' hψ₀ hy₁ε hχ hχ' hχ₀
      hy₂ε hε hU' hV'
  rw [hΦy₁, hΦy₂] at he₀ hcl
  -- Restrict to gluing parameters small enough for the passage to be unique.
  obtain ⟨r₁, hr₁, hr₁r₀, hr₁1, hsmall⟩ :=
    exists_pos_forall_mul_sq_lt_sq (n := (Module.finrank ℝ E : ℝ)) (Nat.cast_nonneg _) hε hr₀
  have hr₁ε : r₁ * ε ≤ ε := mul_le_of_le_one_left hε.le hr₁1
  have hz₀ : (Φ y₁, Φ y₂) ∈ closure (splitGluingPairs ε r₀ g k) := hcl ▸ mem_insert _ _
  have he₀' : e ⟨0, left_mem_Icc.2 hr₀.le⟩ = ⟨_, hz₀⟩ := Subtype.ext he₀
  have hepair : ∀ s : Icc (0 : ℝ) r₀, (s : ℝ) ≠ 0 →
      (e s).val ∈ splitGluingPairs ε r₀ g k ∧ ‖(e s).val.1.snd‖ = s * ε := by
    intro s hs
    refine ⟨e.injective.val_mem_of_subset_insert hcl.subset he₀ fun h ↦
      hs (congrArg Subtype.val h), ?_⟩
    have := he (e s)
    rw [e.symm_apply_apply] at this
    rw [this, div_mul_cancel₀ _ hε.ne']
  -- Points of the gluing pairs read on `M`: the entrance points lie in `W^u(p)`, and the exit
  -- points are reached from points of `C ∩ Z'` in times in `[-1, 1]`; each entrance point flows
  -- to its exit point.
  have hglue : ∀ z ∈ splitGluingPairs ε r₀ g k, Ψ z.1 ∈ hX.flow.unstableSet p ∧ Ψ z.2 ∈ R ∧
      hX.flow (splitExitTime ε z.1) (Ψ z.1) = Ψ z.2 := by
    intro z hz
    obtain ⟨⟨z₁, ⟨⟨hw, hwf, hws⟩, hwu, -⟩, hwz⟩, ⟨z₂, ⟨hz₂C, hz₂Z⟩, hz₂⟩⟩ := hpairs z hz
    obtain ⟨⟨hw', hw'f, hw's⟩, -, hτ⟩ := hCm _ hz₂C
    obtain ⟨h₁, h₃, h₂⟩ :=
      hX.flow_eq_of_mem_splitGluingPairs φ hφ hε hε₂ hz hw hwf hws hwz hw' hw'f hw's hz₂
    refine ⟨?_, ⟨(_, ι₂ z₂), ⟨Ioo_subset_Icc_self hτ, hz₂C, hz₂Z⟩, h₂⟩, h₃⟩
    simp only [hΨdef]
    rw [← h₁]
    exact (Flow.apply_mem_unstableSet_iff _ _).2 hwu
  have hexitR : ∀ z ∈ splitGluingPairs ε r₀ g k, Ψ z.2 ∈ R := fun z hz ↦ (hglue z hz).2.1
  have hmemR : ∀ s : Icc (0 : ℝ) r₁,
      Ψ (e (inclusion (Icc_subset_Icc_right hr₁r₀) s)).val.2 ∈ R := by
    intro s
    by_cases hs : (s : ℝ) = 0
    · have hs0 : inclusion (Icc_subset_Icc_right hr₁r₀) s = ⟨0, left_mem_Icc.2 hr₀.le⟩ :=
        Subtype.ext hs
      rw [hs0, he₀]
      refine ⟨(0, y₂), ⟨by norm_num, mem_of_mem_nhds hC, hy₂Z⟩, ?_⟩
      simp only [Flow.map_zero_apply]
      exact (hΨΦ y₂ hy₂φ).symm
    · exact hexitR _ (hepair (inclusion (Icc_subset_Icc_right hr₁r₀) s) hs).1
  -- The arc: the entrance point of the gluing pair, and the point of `Z'` on the orbit of its exit
  -- point.
  set c : Icc (0 : ℝ) r₁ → M × M := fun s ↦
    (Ψ (e (inclusion (Icc_subset_Icc_right hr₁r₀) s)).val.1,
      Ψ (e (inclusion (Icc_subset_Icc_right hr₁r₀) s)).val.2) with hcdef
  have hcc : Continuous c := by
    refine continuous_iff_continuousAt.2 fun s ↦ ?_
    have hc : Continuous fun s : Icc (0 : ℝ) r₁ ↦
        (e (inclusion (Icc_subset_Icc_right hr₁r₀) s)).val :=
      continuous_subtypeVal.comp (e.continuous.comp (continuous_inclusion _))
    exact (continuousAt_toChart_symm_of_mem_insert_splitGluingPairs φ hε₁ hy₁φ hy₂φ
      (by rw [← hcl]; exact (e (inclusion (Icc_subset_Icc_right hr₁r₀) s)).property)).comp
      hc.continuousAt
  set B : Icc (0 : ℝ) r₁ → M × M := fun s ↦ ((c s).1, π (c s).2) with hBdef
  have hBc : Continuous B :=
    (continuous_fst.comp hcc).prodMk (hπ.comp_continuous (continuous_snd.comp hcc) hmemR)
  have hc0 : c ⟨0, left_mem_Icc.2 hr₁.le⟩ = (y₁, y₂) := by
    simp only [hcdef]
    rw [inclusion_mk, he₀', hΨΦ y₁ hy₁φ, hΨΦ y₂ hy₂φ]
  have hBq : ∀ s, f (B s).2 < f q := fun s ↦ (hCm _ (hπR _ (hmemR s)).1.1).2.1
  -- For `s ≠ 0`, the first point lies in `W^u(p)` and flows to the second point, in `Z'`.
  have hBs : ∀ s : Icc (0 : ℝ) r₁, (s : ℝ) ≠ 0 → (B s).1 ∈ hX.flow.unstableSet p ∧
      hX.flow (-T₂) (B s).2 ∈ Z ∧ ∃ t, hX.flow t (B s).1 = (B s).2 := by
    intro s hs
    obtain ⟨hz, -⟩ := hepair (inclusion (Icc_subset_Icc_right hr₁r₀) s) hs
    set z := (e (inclusion (Icc_subset_Icc_right hr₁r₀) s)).val with hzdef
    obtain ⟨hentry, -, hflow⟩ := hglue z hz
    obtain ⟨hK, τ, hτ⟩ := hπR _ (hmemR s)
    refine ⟨hentry, hK.2, -τ + splitExitTime ε z.1, ?_⟩
    simp only [hBdef, hcdef, ← hzdef]
    rw [Flow.map_add, hflow]
    have := congrArg (hX.flow (-τ)) hτ
    rw [Flow.map_neg_apply_map] at this
    exact this.symm
  refine ⟨T₁, T₂, r₁, hr₁, B, hBc, ?_, hBs, hBq, fun s s' hs hs' t hss' ↦ ?_, ?_⟩
  · -- The arc starts at the broken pair.
    have := hπeq 0 (by norm_num) y₂ ⟨mem_of_mem_nhds hC, hy₂Z⟩
    rw [Flow.map_zero_apply] at this
    simp only [hBdef]
    rw [hc0, this, hT₁, hT₂]
  · -- Two unbroken pairs whose entrance points lie on one orbit are equal.
    set z := (e (inclusion (Icc_subset_Icc_right hr₁r₀) s)).val
    set z' := (e (inclusion (Icc_subset_Icc_right hr₁r₀) s')).val
    obtain ⟨hz, hzn⟩ := hepair (inclusion (Icc_subset_Icc_right hr₁r₀) s) hs
    obtain ⟨hz', hzn'⟩ := hepair (inclusion (Icc_subset_Icc_right hr₁r₀) s') hs'
    have hle : ∀ u : Icc (0 : ℝ) r₁, (u : ℝ) * ε ≤ r₁ * ε := fun u ↦
      mul_le_mul_of_nonneg_right u.property.2 hε.le
    obtain ⟨hBu, -, t₀, ht₀⟩ := hBs s hs
    obtain ⟨b, hpb, hb, -⟩ := exists_mem_unstableSet_inter_stableSet_of_apply_flow_lt hX hf hBu
      (t := t₀) (by rw [ht₀]; exact hBq s) (by linarith [hfa₁.1, hfa₁.2])
    have hsrc := mem_splitPassage_source.1 (mem_splitGluingPairs.1 hz).1
    have hsrc' := mem_splitPassage_source.1 (mem_splitGluingPairs.1 hz').1
    have h1 := hX.eq_of_flow_eq_of_norm_fst_eq φ hφ hε hε₁ hsrc.1 hsrc.2.2 hsrc'.1 hsrc'.2.2
      (hsmall _ (norm_nonneg _) (hzn ▸ hle s)) (hsmall _ (norm_nonneg _) (hzn' ▸ hle s'))
      (hX.strictAnti_flow_of_mem_unstableSet_inter_stableSet hpb hb) hss'
    have hzz : z = z' := Prod.ext h1 (by
      rw [(mem_splitGluingPairs.1 hz).2.2.2.1, (mem_splitGluingPairs.1 hz').2.2.2.1, h1])
    exact inclusion_injective _ (e.injective (Subtype.ext hzz))
  · -- A trajectory near the broken one crosses the box once; its entrance and exit points form a
    -- gluing pair of small parameter.
    have hκ : ∀ x, Tendsto (fun w ↦ ‖(Φ w).fst‖ * ‖(Φ w).snd‖) (𝓝 x) (𝓝 0) →
        ∀ᶠ w in 𝓝 x, ‖(Φ w).fst‖ * ‖(Φ w).snd‖ / ε < r₁ * ε := fun x hx ↦ by
      have h := hx.div_const ε
      rw [zero_div] at h
      exact h.eventually (gt_mem_nhds (mul_pos hr₁ hε))
    have hκ₁ := hκ y₁ hy₁κ
    have hκ₂ := hκ y₂ hy₂κ
    obtain ⟨A₁, hA₁', A₂, hA₂', hA⟩ := mem_nhds_prod_iff.1 hexh
    have hC' : ∀ᶠ w in 𝓝 y₂, w ∈ C := hC
    rw [hT₁, hT₂]
    filter_upwards [((hA₁.and hκ₁).and (hexh₁ A₁ hA₁')).prod_nhds
      (((hA₂.and hκ₂).and (hexh₂ A₂ hA₂')).and hC')] with w hw hw1 hw1f hw2Z hwt
    obtain ⟨⟨⟨⟨hw₁src, hw₁f0, hw₁f, hw₁s, hw₁q⟩, hκw₁⟩, hex₁⟩,
      ⟨⟨⟨hw₂src, hw₂s0, hw₂s, hw₂f, hw₂q⟩, hκw₂⟩, hex₂⟩, hw₂C⟩ := hw
    obtain ⟨t, ht⟩ := hwt
    have hw2u : w.2 ∈ hX.flow.unstableSet p := ht ▸ (Flow.apply_mem_unstableSet_iff _ _).2 hw1
    have hw2fq : f w.2 < f q := (hCm _ hw₂C).2.1
    obtain ⟨b, hpb, hb, -⟩ := exists_mem_unstableSet_inter_stableSet_of_apply_flow_lt hX hf hw1
      (t := t) (by rw [ht]; exact hw2fq) (by linarith [hfa₁.1, hfa₁.2])
    -- Off the broken trajectory, the coordinate that vanishes on it does not vanish.
    have hsnd₁ : (Φ w.1).snd ≠ 0 := fun h0 ↦ by
      have hq2 : w.2 ∈ hX.flow.stableSet q :=
        ht ▸ (Flow.apply_mem_stableSet_iff _ _).2 (hw₁q.2 h0)
      have := Flow.le_of_mem_stableSet_of_antitone hq2
        hX.mdifferentiable.continuous.continuousAt (hX.antitone_flow _)
      linarith
    have hfst₂ : (Φ w.2).fst ≠ 0 := fun h0 ↦
      (Flow.disjoint_unstableSet hpq').ne_of_mem hw2u (hw₂q.2 h0) rfl
    obtain ⟨hE, hEQ'⟩ := hX.splitPassage_splitEntryTime_eq_splitExitTime φ hφ hε hε₂ hw₁src
      (norm_pos_iff.1 hw₁f0) hw₁f hsnd₁ hw₁s hw₂src (norm_pos_iff.1 hw₂s0) hw₂s hfst₂ hw₂f
      (by linarith) (hsmall _ (by positivity) hκw₁.le) (by linarith)
      (hsmall _ (by positivity) hκw₂.le)
      (hX.strictAnti_flow_of_mem_unstableSet_inter_stableSet hpb hb) ht
    obtain ⟨z₁, hz₁, hz₁w⟩ := hex₁ hw1 hw1f
    obtain ⟨z₂, hz₂, hz₂w⟩ := hex₂ hw2Z
    have hq := hA (mk_mem_prod hz₁ hz₂)
    simp only [mem_ofPred_eq, hz₁w, hz₂w] at hq
    have hEQ := hq (mem_splitPassage_source.1 hE).2.1 hEQ'
    -- The pair is a point of the arc of small parameter.
    set s₀ := e.symm ⟨_, subset_closure hEQ⟩ with hs₀def
    have hs₀r₁ : (s₀ : ℝ) < r₁ := by
      rw [hs₀def, he, div_lt_iff₀ hε, norm_snd_splitQuadraticFlow_splitEntryTime hε
        (norm_pos_iff.1 hw₁f0)]
      exact hκw₁
    have hes : e (inclusion (Icc_subset_Icc_right hr₁r₀) ⟨(s₀ : ℝ), s₀.property.1, hs₀r₁.le⟩) =
        ⟨_, subset_closure hEQ⟩ := by
      rw [← e.apply_symm_apply ⟨_, subset_closure hEQ⟩, ← hs₀def]
    refine ⟨⟨s₀, s₀.property.1, hs₀r₁.le⟩, hs₀r₁, ⟨splitEntryTime ε (Φ w.1), ?_⟩, ?_⟩
    · simp only [hBdef, hcdef, hes]
      exact hX.flow_splitEntryTime_of_norm_lt φ hφ hε hε₂ hw₁src hw₁f hw₁s
    · have h₂ := hX.flow_splitExitTime_of_norm_lt φ hφ hε hε₂ hw₂src hw₂f hw₂s
      simp only [hBdef, hcdef, hes]
      have h₂' : Ψ (splitQuadraticFlow (splitExitTime ε (Φ w.2)) (Φ w.2)) =
          hX.flow (splitExitTime ε (Φ w.2)) w.2 := h₂.symm
      rw [h₂', hπeq _ (Ioo_subset_Icc_self (hCm _ hw₂C).2.2) _ ⟨hw₂C, hw2Z⟩]

/-- **The glued orbit at a solved rate.** Let `φ` be a Morse chart at `q` in which `X` is linear
and whose coordinate cube of radius `ε` lies in the chart, and let `(g y, y)` be a point with
`‖g y‖ ≤ ε` solving the gluing equation `l • k (l • g y) = y` at a rate `0 < l ≤ 1`, with
`‖k (l • g y)‖ ≤ ε`. Then in time `-log l` its orbit stays in the box and reaches the point
`(l • g y, k (l • g y))` of the graph of `k`. -/
private theorem flow_neg_log_eq_of_smul_comp_smul_eq (hX : IsAdaptedPseudoGradient f X) {q : M}
    (φ : MorseChart E f q)
    (hφ : ∀ y ∈ φ.toChart.source, φ.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ.toChart y (X y)) =
      fun i ↦ -(φ.weight i * φ.coord (φ.toChart y) i))
    {ε : ℝ} (hε₁ : ∀ z, ‖z‖ ≤ ε → φ.coord.symm z ∈ φ.toChart.target)
    {g : ({i // ¬φ.weight i = 1} → ℝ) → {i // φ.weight i = 1} → ℝ}
    {k : ({i // φ.weight i = 1} → ℝ) → {i // ¬φ.weight i = 1} → ℝ}
    {y : {i // ¬φ.weight i = 1} → ℝ} {l : ℝ} (hl : 0 < l) (hl₁ : l ≤ 1) (hgy : ‖g y‖ ≤ ε)
    (hfix : l • k (l • g y) = y) (hk : ‖k (l • g y)‖ ≤ ε) :
    hX.flow (-Real.log l) (φ.toChart.symm (φ.coord.symm (φ.splitCoord.symm
      (WithLp.toLp 2 (g y, y))))) =
      φ.toChart.symm (φ.coord.symm (φ.splitCoord.symm (WithLp.toLp 2 (l • g y, k (l • g y))))) := by
  obtain ⟨hpt, hbox⟩ := splitQuadraticFlow_eq_and_norm_le_of_smul_comp_smul_eq hl hgy hfix hk
  rw [← uIcc_of_le (neg_nonneg.2 (Real.log_nonpos hl.le hl₁))] at hbox
  rw [hX.flow_toChart_symm_splitCoord_symm φ hφ hε₁ hbox, hpt]

/-- **Orbits from the entrance graph to the graph through the centre.** Let `φ` be a Morse chart at
`q` in which `X` is linear and whose coordinate cube of radius `2 ε` lies in the chart, and let
`v l` be the solutions of the gluing equation `l • k (l • g y) = y` for the graphs
`y ↦ (g y, y)` in the entrance face and `x ↦ (x, k x)` through the centre, for rates
`l ∈ [0, l₀]` with `l₀ ≤ 1`. Let `w₁` be a point near the entrance face whose entrance point lies
on the graph of `g`, with small expanding coordinate, and `w₂ ≠ q` a point of its orbit near the
centre on the graph of `k`, along which `f` strictly decreases. Then, at the rate
`l = ‖u‖ / ε` read from the contracting coordinate `u` of `w₂`, the orbit of `w₁` enters the box
at `(g (v l), v l)`, and `w₂` is the point `(l • g (v l), k (l • g (v l)))`. -/
private theorem flow_splitEntryTime_eq_and_eq_of_centre (hX : IsAdaptedPseudoGradient f X)
    {q : M} (φ : MorseChart E f q)
    (hφ : ∀ y ∈ φ.toChart.source, φ.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ.toChart y (X y)) =
      fun i ↦ -(φ.weight i * φ.coord (φ.toChart y) i))
    {ε : ℝ} (hε : 0 < ε) (hε₂ : ∀ z, ‖z‖ ≤ 2 * ε → φ.coord.symm z ∈ φ.toChart.target)
    {g : ({i // ¬φ.weight i = 1} → ℝ) → {i // φ.weight i = 1} → ℝ}
    {k : ({i // φ.weight i = 1} → ℝ) → {i // ¬φ.weight i = 1} → ℝ}
    {δ l₀ : ℝ} (hδε : δ ≤ ε) (hδ : Module.finrank ℝ E * δ ^ 2 < ε ^ 2) (hl₀ : l₀ ≤ 1)
    {v : ℝ → {i // ¬φ.weight i = 1} → ℝ}
    (hv : ∀ l ∈ Icc 0 l₀, ∀ y ∈ closedBall 0 δ, l • k (l • g y) = y → y = v l)
    {w₁ w₂ : M} (hw₁ : w₁ ∈ φ.toChart.source)
    (hw₁f₀ : (φ.splitCoord (φ.coord (φ.toChart w₁))).fst ≠ 0)
    (hw₁f : ‖(φ.splitCoord (φ.coord (φ.toChart w₁))).fst‖ < 2 * ε)
    (hw₁s : ‖(φ.splitCoord (φ.coord (φ.toChart w₁))).snd‖ < ε)
    (hw₁δ : ‖(φ.splitCoord (φ.coord (φ.toChart w₁))).fst‖ *
      ‖(φ.splitCoord (φ.coord (φ.toChart w₁))).snd‖ / ε ≤ δ)
    (hw₁g : (splitQuadraticFlow (splitEntryTime ε (φ.splitCoord (φ.coord (φ.toChart w₁))))
        (φ.splitCoord (φ.coord (φ.toChart w₁)))).fst =
      g (splitQuadraticFlow (splitEntryTime ε (φ.splitCoord (φ.coord (φ.toChart w₁))))
        (φ.splitCoord (φ.coord (φ.toChart w₁)))).snd)
    (hw₂ : w₂ ∈ φ.toChart.source) (hw₂f₀ : (φ.splitCoord (φ.coord (φ.toChart w₂))).fst ≠ 0)
    (hw₂f : ‖(φ.splitCoord (φ.coord (φ.toChart w₂))).fst‖ ≤ l₀ * ε)
    (hw₂s : ‖(φ.splitCoord (φ.coord (φ.toChart w₂))).snd‖ < ε)
    (hw₂δ : ‖(φ.splitCoord (φ.coord (φ.toChart w₂))).fst‖ *
      ‖(φ.splitCoord (φ.coord (φ.toChart w₂))).snd‖ / ε ≤ δ)
    (hw₂k : (φ.splitCoord (φ.coord (φ.toChart w₂))).snd =
      k (φ.splitCoord (φ.coord (φ.toChart w₂))).fst)
    (hanti : StrictAnti fun t ↦ f (hX.flow t w₁)) {t : ℝ} (ht : hX.flow t w₁ = w₂) :
    hX.flow (splitEntryTime ε (φ.splitCoord (φ.coord (φ.toChart w₁)))) w₁ =
        φ.toChart.symm (φ.coord.symm (φ.splitCoord.symm (WithLp.toLp 2
          (g (v (‖(φ.splitCoord (φ.coord (φ.toChart w₂))).fst‖ / ε)),
            v (‖(φ.splitCoord (φ.coord (φ.toChart w₂))).fst‖ / ε))))) ∧
      w₂ = φ.toChart.symm (φ.coord.symm (φ.splitCoord.symm (WithLp.toLp 2
        ((‖(φ.splitCoord (φ.coord (φ.toChart w₂))).fst‖ / ε) •
          g (v (‖(φ.splitCoord (φ.coord (φ.toChart w₂))).fst‖ / ε)),
         k ((‖(φ.splitCoord (φ.coord (φ.toChart w₂))).fst‖ / ε) •
          g (v (‖(φ.splitCoord (φ.coord (φ.toChart w₂))).fst‖ / ε))))))) := by
  set z₁ := φ.splitCoord (φ.coord (φ.toChart w₁)) with hz₁def
  set z₂ := φ.splitCoord (φ.coord (φ.toChart w₂)) with hz₂def
  have hε₁ : ∀ z, ‖z‖ ≤ ε → φ.coord.symm z ∈ φ.toChart.target := fun z hz ↦ hε₂ z (by linarith)
  -- The entrance points of the orbits of `w₁` and of `w₂`, the latter read backwards.
  set E₁ := splitQuadraticFlow (splitEntryTime ε z₁) z₁ with hE₁def
  set E₂ := splitQuadraticFlow (splitEntryTime ε z₂) z₂ with hE₂def
  have hΨE₁ := hX.flow_splitEntryTime_of_norm_lt φ hφ hε hε₂ hw₁ hw₁f hw₁s
  have hΨE₂ := hX.flow_splitEntryTime_of_norm_lt φ hφ hε hε₂ hw₂
    (by nlinarith [norm_nonneg z₂.fst]) hw₂s
  rw [← hz₁def, ← hE₁def] at hΨE₁
  rw [← hz₂def, ← hE₂def] at hΨE₂
  have hE₁s : ‖E₁.snd‖ ≤ δ := by
    rw [norm_snd_splitQuadraticFlow_splitEntryTime hε hw₁f₀]; exact hw₁δ
  have hE₂s : ‖E₂.snd‖ ≤ δ := by
    rw [norm_snd_splitQuadraticFlow_splitEntryTime hε hw₂f₀]; exact hw₂δ
  have hn (z : WithLp 2 (({i // φ.weight i = 1} → ℝ) × ({i // ¬φ.weight i = 1} → ℝ)))
      (hz : ‖z.snd‖ ≤ δ) : Module.finrank ℝ E * ‖z.snd‖ ^ 2 < ε ^ 2 :=
    lt_of_le_of_lt (by gcongr) hδ
  -- Both lie on the orbit of `w₁`, so they are equal.
  have hantiE : StrictAnti fun σ ↦ f (hX.flow σ
      (φ.toChart.symm (φ.coord.symm (φ.splitCoord.symm E₁)))) := fun a b hab ↦ by
    have h := hanti (by linarith : a + splitEntryTime ε z₁ < b + splitEntryTime ε z₁)
    simp only [Flow.map_add] at h
    rwa [hΨE₁] at h
  have hE : E₁ = E₂ := hX.eq_of_flow_eq_of_norm_fst_eq φ hφ hε hε₁
    (norm_fst_splitQuadraticFlow_splitEntryTime hε hw₁f₀) (hE₁s.trans hδε)
    (norm_fst_splitQuadraticFlow_splitEntryTime hε hw₂f₀) (hE₂s.trans hδε) (hn _ hE₁s) (hn _ hE₂s)
    hantiE (t := splitEntryTime ε z₂ + t - splitEntryTime ε z₁) (by
      rw [← hΨE₁, ← hΨE₂, ← ht, ← Flow.map_add, ← Flow.map_add]
      congr 1
      ring)
  -- So `E₂ = (g y, y)` solves the gluing equation at the rate `l`.
  set l := ‖z₂.fst‖ / ε with hldef
  have hl : l ∈ Icc 0 l₀ := ⟨by positivity, by rw [hldef, div_le_iff₀ hε]; exact hw₂f⟩
  have hexpl : Real.exp (-(-splitEntryTime ε z₂)) = l := by
    rw [neg_neg, splitEntryTime_def, Real.exp_log (div_pos (norm_pos_iff.2 hw₂f₀) hε)]
  have hE₂g : E₂ = WithLp.toLp 2 (g E₂.snd, E₂.snd) :=
    WithLp.ofLp_injective 2 (Prod.ext (by simpa [← hE] using hw₁g) (by simp))
  have hback : splitQuadraticFlow (-splitEntryTime ε z₂) E₂ = z₂ := by
    rw [hE₂def, Flow.map_neg_apply_map]
  have hfix : l • k (l • g E₂.snd) = E₂.snd := by
    have h := (splitQuadraticFlow_snd_eq_iff_smul_comp_smul_eq (k := k) _ (g E₂.snd) E₂.snd).1
      (by rw [← hE₂g, hback]; exact hw₂k)
    rwa [hexpl] at h
  have hyv : E₂.snd = v l := hv l hl _ (mem_closedBall_zero_iff.2 hE₂s) hfix
  have hfst : z₂.fst = l • g E₂.snd := by
    rw [← hback, hE₂g, splitQuadraticFlow_apply, hexpl]
    simp
  refine ⟨by rw [hΨE₁, hE, hE₂g, hyv], ?_⟩
  have hz₂ : z₂ = WithLp.toLp 2 (l • g E₂.snd, k (l • g E₂.snd)) :=
    WithLp.ofLp_injective 2 (Prod.ext (by simpa using hfst) (by simpa [hfst] using hw₂k))
  rw [← hyv, ← hz₂, hz₂def, LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply,
    φ.toChart.left_inv hw₂]

/-- **A set transverse to the unstable manifold at the critical point is a graph through the
centre.** Let `φ` be a Morse chart at `q` on whose cube of radius `ρ` the unstable set of `q` is the
plane where the contracting split coordinate `u` vanishes, and let `Z` be a set through `q` of
dimension `n - ind q`, flattened near `q` by a chart of the maximal atlas and transverse to `W^u(q)`
at `q`. Near the centre, `Z` is a Lipschitz graph `u ↦ (u, k u)` over a closed ball of the
contracting factor, with `k 0 = 0`: the points of the graph lie in `Z`, and the points of `Z` near
`q` lie on the graph. -/
private theorem exists_lipschitzOnWith_graph_of_isSliceChart (hX : IsAdaptedPseudoGradient f X)
    {q : M} (φ : MorseChart E f q) {ρ : ℝ} (hρ : 0 < ρ)
    (hloc : ∀ w ∈ φ.toChart.source, ‖φ.coord (φ.toChart w)‖ < ρ →
      (w ∈ hX.flow.unstableSet q ↔ (φ.splitCoord (φ.coord (φ.toChart w))).fst = 0))
    (hq : q ∈ hX.flow.unstableSet q) {Z : Set M} {L : Submodule ℝ E}
    {φZ : OpenPartialHomeomorph M E} (hφZ : φZ ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M)
    (hZ : IsSliceChart φZ (L : Set E) Z) (hqφZ : q ∈ φZ.source) (hqZ : q ∈ Z)
    (hdim : Module.finrank ℝ L + manifoldMorseIndex 𝓘(ℝ, E) f q = Module.finrank ℝ E)
    (htr : Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) Z q) ⊔
      Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX.flow.unstableSet q) q) = ⊤) :
    ∃ η > 0, ∃ (K : NNReal) (k : ({i // φ.weight i = 1} → ℝ) → {i // ¬φ.weight i = 1} → ℝ),
      LipschitzOnWith K k (closedBall 0 η) ∧ k 0 = 0 ∧ (∀ u ∈ closedBall 0 η,
        φ.toChart.symm (φ.coord.symm (φ.splitCoord.symm (WithLp.toLp 2 (u, k u)))) ∈ Z) ∧
      ∀ᶠ w in 𝓝 q, w ∈ Z → (φ.splitCoord (φ.coord (φ.toChart w))).fst ∈ closedBall 0 η ∧
        (φ.splitCoord (φ.coord (φ.toChart w))).snd =
          k (φ.splitCoord (φ.coord (φ.toChart w))).fst := by
  -- A disc of `Z` through `q` whose points near `0` exhaust `Z` near `q`: its tangent space is
  -- transverse to `W^u(q)`, the plane `u = 0`, and of the dimension of the contracting factor.
  have hlocq : ∀ᶠ w in 𝓝 q, w ∈ hX.flow.unstableSet q →
      (φ.splitCoord (φ.coord (φ.toChart w))).fst = 0 := by
    filter_upwards [φ.eventually_mem_source_norm_coord_lt hρ] with w ⟨hw, hwρ⟩
    exact (hloc w hw hwρ).1
  obtain ⟨ι₂, χ', hι₂0, hι₂, hι₂s, hχ, hχ', hexh₂⟩ :=
    hX.exists_param_splitCoord_of_isSliceChart φ φ.mem_source hq hlocq hφZ hZ hqφZ hqZ hdim htr
  have hχ₀ : φ.splitCoord (φ.coord (φ.toChart (ι₂ 0))) = 0 := by simp [hι₂0, φ.apply_self]
  set V' : Set L := {z | ι₂ z ∈ φ.toChart.source ∧ ι₂ z ∈ Z}
  have hV' : V' ∈ 𝓝 0 :=
    (Filter.Eventually.and (hι₂.preimage_mem_nhds
      (by rw [hι₂0]; exact φ.toChart.open_source.mem_nhds φ.mem_source)) hι₂s).mono
      fun z ⟨h₁, h₂⟩ ↦ ⟨h₁, h₂⟩
  obtain ⟨η, hη, Kk, k, hk, hk₀, hkpts, hkexh⟩ :=
    exists_lipschitzOnWith_graph_of_hasStrictFDerivAt hχ hχ' hχ₀ hV'
  -- The graph of `k` lies in `Z`, and the points of `Z` near `q` are points of the disc, hence of
  -- the graph.
  refine ⟨η, hη, Kk, k, hk, hk₀, fun u hu ↦ ?_, ?_⟩
  · obtain ⟨z, ⟨hzs, hzZ⟩, hz⟩ := hkpts u hu
    rw [← hz, LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply, φ.toChart.left_inv hzs]
    exact hzZ
  · filter_upwards [hexh₂ _ hkexh] with w hw hwZ
    obtain ⟨z, hz, rfl⟩ := hw hwZ
    exact hz

omit [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M] [T2Space M] in
/-- Reading a continuous family of split coordinates in the cube of radius `2 ε` back on `M`
through a Morse chart containing that cube is continuous. -/
private theorem continuous_toChart_symm_coord_symm_splitCoord_symm_comp {q : M}
    (φ : MorseChart E f q) {ε : ℝ} (hε₂ : ∀ z, ‖z‖ ≤ 2 * ε → φ.coord.symm z ∈ φ.toChart.target)
    {α : Type*} [TopologicalSpace α]
    {c : α → WithLp 2 (({i // φ.weight i = 1} → ℝ) × ({i // ¬φ.weight i = 1} → ℝ))}
    (hc : Continuous c) (hcε : ∀ a, ‖(c a).fst‖ ≤ 2 * ε ∧ ‖(c a).snd‖ ≤ 2 * ε) :
    Continuous fun a ↦ φ.toChart.symm (φ.coord.symm (φ.splitCoord.symm (c a))) :=
  continuous_iff_continuousAt.2 fun a ↦
    (φ.continuousAt_toChart_symm_coord_symm_splitCoord_symm
      (MorseChart.coord_symm_splitCoord_symm_mem_target_of_norm_le hε₂ (hcε a).1
        (hcε a).2)).comp hc.continuousAt

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M] [T2Space M] in
/-- Two points with split coordinates `z` and `z'` in the cube of radius `2 ε` contained in a
Morse chart, whose first coordinates have norms `l ε` and `l' ε`, are equal only if `l = l'`. -/
private theorem eq_of_toChart_symm_eq_of_norm_fst_eq {q : M} (φ : MorseChart E f q) {ε : ℝ}
    (hε : 0 < ε) (hε₂ : ∀ z, ‖z‖ ≤ 2 * ε → φ.coord.symm z ∈ φ.toChart.target)
    {z z' : WithLp 2 (({i // φ.weight i = 1} → ℝ) × ({i // ¬φ.weight i = 1} → ℝ))}
    (hz : ‖z.fst‖ ≤ 2 * ε ∧ ‖z.snd‖ ≤ 2 * ε) (hz' : ‖z'.fst‖ ≤ 2 * ε ∧ ‖z'.snd‖ ≤ 2 * ε)
    {l l' : ℝ} (hzl : ‖z.fst‖ = l * ε) (hzl' : ‖z'.fst‖ = l' * ε)
    (h : φ.toChart.symm (φ.coord.symm (φ.splitCoord.symm z)) =
      φ.toChart.symm (φ.coord.symm (φ.splitCoord.symm z'))) :
    l = l' := by
  have hzz' := φ.injOn_toChart_symm_coord_symm_splitCoord_symm
    (MorseChart.coord_symm_splitCoord_symm_mem_target_of_norm_le hε₂ hz.1 hz.2)
    (MorseChart.coord_symm_splitCoord_symm_mem_target_of_norm_le hε₂ hz'.1 hz'.2) h
  rw [← hzz', hzl] at hzl'
  exact mul_right_cancel₀ hε.ne' hzl'

/-- **The glued arc through the centre.** Let `φ` be a Morse chart at `q` in which `X` is linear
and whose coordinate cube of radius `2 ε` lies in the chart, let `g` and `k` be continuous on sets
`s₁` and `s₂`, and let `v` be continuous on `[0, l₀]`, with `l₀ ≤ 1`, where each `v l` is a solution
in `s₁` of the gluing equation `l • k (l • g y) = y` with `l • g (v l) ∈ s₂`, `‖g (v l)‖ = ε`,
`‖v l‖ ≤ ε` and `‖k (l • g (v l))‖ ≤ ε`. Send `l` to the entrance point `(g (v l), v l)` and the
point `(l • g (v l), k (l • g (v l)))` of the graph of `k`, read on `M`. This arc is continuous,
for `l ≠ 0` its entrance point flows in time `-log l` to its point on the graph of `k`, and
distinct rates give distinct points on the graph of `k`. -/
private theorem continuous_and_flow_neg_log_eq_of_smul_comp_smul_eq
    (hX : IsAdaptedPseudoGradient f X) {q : M} (φ : MorseChart E f q)
    (hφ : ∀ y ∈ φ.toChart.source, φ.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ.toChart y (X y)) =
      fun i ↦ -(φ.weight i * φ.coord (φ.toChart y) i))
    {ε : ℝ} (hε : 0 < ε) (hε₂ : ∀ z, ‖z‖ ≤ 2 * ε → φ.coord.symm z ∈ φ.toChart.target)
    {g : ({i // ¬φ.weight i = 1} → ℝ) → {i // φ.weight i = 1} → ℝ}
    {k : ({i // φ.weight i = 1} → ℝ) → {i // ¬φ.weight i = 1} → ℝ}
    {s₁ : Set ({i // ¬φ.weight i = 1} → ℝ)} {s₂ : Set ({i // φ.weight i = 1} → ℝ)}
    (hg : ContinuousOn g s₁) (hk : ContinuousOn k s₂) {l₀ : ℝ} (hl₀ : l₀ ≤ 1)
    {v : ℝ → {i // ¬φ.weight i = 1} → ℝ} (hvc : ContinuousOn v (Icc 0 l₀))
    (hvs₁ : ∀ l ∈ Icc 0 l₀, v l ∈ s₁) (hvs₂ : ∀ l ∈ Icc 0 l₀, l • g (v l) ∈ s₂)
    (hgε : ∀ l ∈ Icc 0 l₀, ‖g (v l)‖ = ε) (hvε : ∀ l ∈ Icc 0 l₀, ‖v l‖ ≤ ε)
    (hkε : ∀ l ∈ Icc 0 l₀, ‖k (l • g (v l))‖ ≤ ε)
    (hfix : ∀ l ∈ Icc 0 l₀, l • k (l • g (v l)) = v l) :
    (Continuous fun s : Icc (0 : ℝ) l₀ ↦
      (φ.toChart.symm (φ.coord.symm (φ.splitCoord.symm (WithLp.toLp 2 (g (v s), v s)))),
        φ.toChart.symm (φ.coord.symm (φ.splitCoord.symm
          (WithLp.toLp 2 ((s : ℝ) • g (v s), k ((s : ℝ) • g (v s)))))))) ∧
      (∀ s : Icc (0 : ℝ) l₀, (s : ℝ) ≠ 0 → hX.flow (-Real.log s)
        (φ.toChart.symm (φ.coord.symm (φ.splitCoord.symm (WithLp.toLp 2 (g (v s), v s))))) =
          φ.toChart.symm (φ.coord.symm (φ.splitCoord.symm
            (WithLp.toLp 2 ((s : ℝ) • g (v s), k ((s : ℝ) • g (v s))))))) ∧
      ∀ s s' : Icc (0 : ℝ) l₀,
        φ.toChart.symm (φ.coord.symm (φ.splitCoord.symm
            (WithLp.toLp 2 ((s : ℝ) • g (v s), k ((s : ℝ) • g (v s)))))) =
          φ.toChart.symm (φ.coord.symm (φ.splitCoord.symm
            (WithLp.toLp 2 ((s' : ℝ) • g (v s'), k ((s' : ℝ) • g (v s')))))) → s = s' := by
  have hnorm_g {l : ℝ} (hl : l ∈ Icc 0 l₀) : ‖l • g (v l)‖ = l * ε := by
    rw [norm_smul, Real.norm_of_nonneg hl.1, hgε l hl]
  -- Both points lie in the cube of radius `2 ε`.
  have hB₁ε (s : Icc (0 : ℝ) l₀) : ‖(WithLp.toLp 2 (g (v s), v s)).fst‖ ≤ 2 * ε ∧
      ‖(WithLp.toLp 2 (g (v s), v s)).snd‖ ≤ 2 * ε := by
    rw [WithLp.toLp_fst, WithLp.toLp_snd, hgε s s.property]
    exact ⟨by linarith, by linarith [hvε s s.property]⟩
  have hB₂ε (s : Icc (0 : ℝ) l₀) :
      ‖(WithLp.toLp 2 ((s : ℝ) • g (v s), k ((s : ℝ) • g (v s)))).fst‖ ≤ 2 * ε ∧
        ‖(WithLp.toLp 2 ((s : ℝ) • g (v s), k ((s : ℝ) • g (v s)))).snd‖ ≤ 2 * ε := by
    rw [WithLp.toLp_fst, WithLp.toLp_snd, hnorm_g s.property]
    exact ⟨by nlinarith [s.property.1, s.property.2], by linarith [hkε s s.property]⟩
  have hvc' : Continuous fun s : Icc (0 : ℝ) l₀ ↦ v s :=
    hvc.comp_continuous continuous_subtypeVal fun s ↦ s.property
  have hgc : Continuous fun s : Icc (0 : ℝ) l₀ ↦ g (v s) :=
    hg.comp_continuous hvc' fun s ↦ hvs₁ s s.property
  have hsgc : Continuous fun s : Icc (0 : ℝ) l₀ ↦ (s : ℝ) • g (v s) :=
    continuous_subtypeVal.smul hgc
  have hkc : Continuous fun s : Icc (0 : ℝ) l₀ ↦ k ((s : ℝ) • g (v s)) :=
    hk.comp_continuous hsgc fun s ↦ hvs₂ s s.property
  -- The point on the graph of `k` determines the rate, through the norm `l ε` of its first
  -- coordinate.
  refine ⟨(continuous_toChart_symm_coord_symm_splitCoord_symm_comp φ hε₂
      ((WithLp.prod_continuous_toLp 2 _ _).comp (hgc.prodMk hvc')) hB₁ε).prodMk
      (continuous_toChart_symm_coord_symm_splitCoord_symm_comp φ hε₂
        ((WithLp.prod_continuous_toLp 2 _ _).comp (hsgc.prodMk hkc)) hB₂ε), fun s hs ↦ ?_,
    fun s s' h ↦ Subtype.ext (eq_of_toChart_symm_eq_of_norm_fst_eq φ hε hε₂ (hB₂ε s) (hB₂ε s')
      (hnorm_g s.property) (hnorm_g s'.property) h)⟩
  -- For `l > 0`, the entrance point flows in time `-log l` to the point of the graph of `k`.
  exact hX.flow_neg_log_eq_of_smul_comp_smul_eq φ hφ (fun z hz ↦ hε₂ z (by linarith))
    (lt_of_le_of_ne s.property.1 (Ne.symm hs)) (s.property.2.trans hl₀)
    (hgε s s.property).le (hfix s s.property) (hkε s s.property)

/-- **The pairs recorded near a configuration broken at the centre lie on the glued family.** Let
`φ` be a Morse chart at `q` in which `X` is linear and whose coordinate cube of radius `2 ε` lies
in the chart, and let `v l` be the solutions in the closed ball of radius `δ` of the gluing
equation `l • k (l • g y) = y`, for rates `l ∈ [0, l₀]` with `l₀ ≤ 1` and `k 0 = 0`. Let `y₁` be a
point near which the points lie in the box near its entrance face and the orbits of the points of
`W^u(p)` on the level of `y₁` enter the box on the graph of `g`, with `‖u‖ ‖v‖ → 0` at `y₁`, and
let `Z` be the graph of `k` near `q`, for a critical point `p ≠ q` with `f q < f p`. Then every
pair `(w₁, w₂)` near `(y₁, q)`, with `w₁ ∈ W^u(p)` on the level of `y₁` and `w₂ ∈ Z` on its orbit,
is reached at a rate `l ∈ [0, l₀)`: the orbit of `w₁` enters the box at `(g (v l), v l)`, and `w₂`
is the point `(l • g (v l), k (l • g (v l)))`. -/
private theorem eventually_exists_flow_splitEntryTime_eq_and_eq_of_centre
    (hX : IsAdaptedPseudoGradient f X) (hf : IsMorse 𝓘(ℝ, E) f) {p q y₁ : M} (hpq : p ≠ q)
    (hq : q ∈ hX.flow.unstableSet q) (hqp : f q < f p) (φ : MorseChart E f q)
    (hφ : ∀ y ∈ φ.toChart.source, φ.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ.toChart y (X y)) =
      fun i ↦ -(φ.weight i * φ.coord (φ.toChart y) i))
    {ε : ℝ} (hε : 0 < ε) (hε₂ : ∀ z, ‖z‖ ≤ 2 * ε → φ.coord.symm z ∈ φ.toChart.target)
    {g : ({i // ¬φ.weight i = 1} → ℝ) → {i // φ.weight i = 1} → ℝ}
    {k : ({i // φ.weight i = 1} → ℝ) → {i // ¬φ.weight i = 1} → ℝ}
    {δ l₀ : ℝ} (hδ : 0 < δ) (hl₀ : 0 < l₀) (hl₀₁ : l₀ ≤ 1)
    {v : ℝ → {i // ¬φ.weight i = 1} → ℝ}
    (hv : ∀ l ∈ Icc 0 l₀, ∀ y ∈ closedBall 0 δ, l • k (l • g y) = y → y = v l) (hk₀ : k 0 = 0)
    (hA₁ : ∀ᶠ w in 𝓝 y₁, w ∈ φ.toChart.source ∧
      0 < ‖(φ.splitCoord (φ.coord (φ.toChart w))).fst‖ ∧
      ‖(φ.splitCoord (φ.coord (φ.toChart w))).fst‖ < 2 * ε ∧
      ‖(φ.splitCoord (φ.coord (φ.toChart w))).snd‖ < ε)
    (hy₁κ : Tendsto (fun w ↦ ‖(φ.splitCoord (φ.coord (φ.toChart w))).fst‖ *
      ‖(φ.splitCoord (φ.coord (φ.toChart w))).snd‖) (𝓝 y₁) (𝓝 0))
    (hg₁ : ∀ᶠ w in 𝓝 y₁, w ∈ hX.flow.unstableSet p → f w = f y₁ →
      (splitQuadraticFlow (splitEntryTime ε (φ.splitCoord (φ.coord (φ.toChart w))))
          (φ.splitCoord (φ.coord (φ.toChart w)))).fst =
        g (splitQuadraticFlow (splitEntryTime ε (φ.splitCoord (φ.coord (φ.toChart w))))
          (φ.splitCoord (φ.coord (φ.toChart w)))).snd)
    {Z : Set M} (hkZ : ∀ᶠ w in 𝓝 q, w ∈ Z → (φ.splitCoord (φ.coord (φ.toChart w))).snd =
      k (φ.splitCoord (φ.coord (φ.toChart w))).fst) :
    ∀ᶠ w : M × M in 𝓝 (y₁, q), w.1 ∈ hX.flow.unstableSet p → f w.1 = f y₁ → w.2 ∈ Z →
      (∃ t, hX.flow t w.1 = w.2) → ∃ l ∈ Ico 0 l₀,
        hX.flow (splitEntryTime ε (φ.splitCoord (φ.coord (φ.toChart w.1)))) w.1 =
          φ.toChart.symm (φ.coord.symm (φ.splitCoord.symm (WithLp.toLp 2 (g (v l), v l)))) ∧
        w.2 = φ.toChart.symm (φ.coord.symm (φ.splitCoord.symm
          (WithLp.toLp 2 (l • g (v l), k (l • g (v l)))))) := by
  -- A bound `r₁ ε ≤ δ` on the entrance points, small enough for the entrance-face uniqueness.
  obtain ⟨r₁, hr₁, hr₁δ, hr₁₁, hsmall₁⟩ :=
    exists_pos_forall_mul_sq_lt_sq (n := (Module.finrank ℝ E : ℝ)) (Nat.cast_nonneg _) hε
      (div_pos hδ hε)
  have hcδ : r₁ * ε ≤ δ := by rwa [le_div_iff₀ hε] at hr₁δ
  have hcn := hsmall₁ (r₁ * ε) (by positivity) le_rfl
  have hκ : ∀ x : M, Tendsto (fun w ↦ ‖(φ.splitCoord (φ.coord (φ.toChart w))).fst‖ *
      ‖(φ.splitCoord (φ.coord (φ.toChart w))).snd‖) (𝓝 x) (𝓝 0) →
      ∀ᶠ w in 𝓝 x, ‖(φ.splitCoord (φ.coord (φ.toChart w))).fst‖ *
        ‖(φ.splitCoord (φ.coord (φ.toChart w))).snd‖ / ε < r₁ * ε := fun x hx ↦ by
    have h := hx.div_const ε
    rw [zero_div] at h
    exact h.eventually (gt_mem_nhds (mul_pos hr₁ hε))
  -- Near `q` both split coordinates are small and `f < f p`.
  have hΦq : φ.splitCoord (φ.coord (φ.toChart q)) = 0 := by simp [φ.apply_self]
  have hfstq := φ.tendsto_norm_fst_splitCoord_coord_toChart φ.mem_source
  have hsndq := φ.tendsto_norm_snd_splitCoord_coord_toChart φ.mem_source
  rw [hΦq, WithLp.zero_fst, norm_zero] at hfstq
  rw [hΦq, WithLp.zero_snd, norm_zero] at hsndq
  have hN₂ := ((Filter.Eventually.and (φ.toChart.open_source.mem_nhds φ.mem_source)
    (hfstq.eventually (gt_mem_nhds (mul_pos hl₀ hε)))).and
    ((hsndq.eventually (gt_mem_nhds hε)).and
      ((hκ q (by simpa only [mul_zero] using hfstq.mul hsndq)).and (hkZ.and
        (hX.mdifferentiable.continuous.continuousAt.eventually (gt_mem_nhds hqp))))))
  filter_upwards [((hA₁.and (hκ y₁ hy₁κ)).and hg₁).prod_nhds hN₂] with w
    ⟨⟨⟨⟨hw₁src, hw₁f0, hw₁f, hw₁s⟩, hκw₁⟩, hg₁w⟩, ⟨hw₂src, hw₂f⟩, hw₂s, hκw₂, hk₂, hw₂p⟩
    hw1u hw1f hw2Z ⟨t, ht⟩
  -- `w.2` lies in `W^u(p)`, so it is not the centre, the only point of the graph of `k` with
  -- `u = 0`.
  have hw₂u : w.2 ∈ hX.flow.unstableSet p := ht ▸ (Flow.apply_mem_unstableSet_iff _ _).2 hw1u
  have hu : (φ.splitCoord (φ.coord (φ.toChart w.2))).fst ≠ 0 := by
    intro h0
    have hz₂ : φ.splitCoord (φ.coord (φ.toChart w.2)) = 0 := WithLp.ofLp_injective 2
      (Prod.ext (by simpa using h0) (by simpa [h0, hk₀] using hk₂ hw2Z))
    refine (Flow.disjoint_unstableSet hpq).ne_of_mem hw₂u hq ?_
    simpa [φ.toChart.left_inv hw₂src, φ.toChart_symm_zero] using
      congrArg (fun z ↦ φ.toChart.symm (φ.coord.symm (φ.splitCoord.symm z))) hz₂
  -- Along the orbit of `w.1` from `p`, `f` strictly decreases.
  obtain ⟨b, hpb, hb, -⟩ := exists_mem_unstableSet_inter_stableSet_of_apply_flow_lt hX hf hw1u
    (t := t) (by rw [ht]; exact hw₂p) le_rfl
  obtain ⟨h₁, h₂⟩ := flow_splitEntryTime_eq_and_eq_of_centre hX φ hφ hε hε₂
    (mul_le_of_le_one_left hε.le hr₁₁) hcn hl₀₁
    (fun l hl y hy hfix ↦ hv l hl y (closedBall_subset_closedBall hcδ hy) hfix) hw₁src
    (norm_pos_iff.1 hw₁f0) hw₁f hw₁s hκw₁.le (hg₁w hw1u hw1f) hw₂src hu hw₂f.le hw₂s hκw₂.le
    (hk₂ hw2Z) (hX.strictAnti_flow_of_mem_unstableSet_inter_stableSet hpb hb) ht
  exact ⟨_, ⟨by positivity, by rw [div_lt_iff₀ hε]; exact hw₂f⟩, h₁, h₂⟩

/-- **The model gluing arc through the critical point, on the manifold.** For a trajectory from `p`
through `a₁` to `q`, with `ind p = ind q + 1`, and a set `Z` of dimension `n - ind q` flattened near
`q` and transverse to `W^u(q)` there, there are a point `flow T₁ a₁` and a continuous arc `B` in
`M × M` starting at `(flow T₁ a₁, q)`, along which, for `s ≠ 0`, `(B s).1` lies in `W^u(p)` and
flows to the point `(B s).2` of `Z`, distinct parameters giving distinct points of `Z`, all below
the level of `a₁`. Every pair of such points near the start, the first on the level of
`flow T₁ a₁`, is reached by the arc below its end. -/
private theorem IsMorseSmale.exists_centreGluingArc {hX : IsAdaptedPseudoGradient f X}
    (h : hX.IsMorseSmale) (hf : IsMorse 𝓘(ℝ, E) f) {p q a₁ : M} {Z : Set M}
    (hpq : manifoldMorseIndex 𝓘(ℝ, E) f p = manifoldMorseIndex 𝓘(ℝ, E) f q + 1)
    (ha₁ : a₁ ∈ hX.flow.unstableSet p ∩ hX.flow.stableSet q) {L : Submodule ℝ E}
    {φZ : OpenPartialHomeomorph M E} (hφZ : φZ ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M)
    (hZ : IsSliceChart φZ (L : Set E) Z) (hqφZ : q ∈ φZ.source) (hqZ : q ∈ Z)
    (hdim : Module.finrank ℝ L + manifoldMorseIndex 𝓘(ℝ, E) f q = Module.finrank ℝ E)
    (htr : Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) Z q) ⊔
      Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX.flow.unstableSet q) q) = ⊤) :
    ∃ (T₁ δ : ℝ) (hδ : 0 < δ) (B : Icc (0 : ℝ) δ → M × M), Continuous B ∧
      B ⟨0, left_mem_Icc.2 hδ.le⟩ = (hX.flow T₁ a₁, q) ∧
      (∀ s : Icc (0 : ℝ) δ, (s : ℝ) ≠ 0 → (B s).1 ∈ hX.flow.unstableSet p ∧
        (B s).2 ∈ Z ∧ ∃ t, hX.flow t (B s).1 = (B s).2) ∧
      (∀ s, f (B s).2 < f a₁) ∧
      (∀ s s' : Icc (0 : ℝ) δ, (B s).2 = (B s').2 → s = s') ∧
      ∀ᶠ w : M × M in 𝓝 (hX.flow T₁ a₁, q),
        w.1 ∈ hX.flow.unstableSet p → f w.1 = f (hX.flow T₁ a₁) → w.2 ∈ Z →
        (∃ t, hX.flow t w.1 = w.2) →
        ∃ s : Icc (0 : ℝ) δ, (s : ℝ) < δ ∧ (∃ t, hX.flow t w.1 = (B s).1) ∧ w.2 = (B s).2 := by
  -- Plan: in a Morse box at `q`, the trace of `W^u(p)` on the entrance face is a graph
  -- `v ↦ (g v, v)` and `Z` near the centre is a graph `u ↦ (u, k u)`. The orbit through `(g v, v)`
  -- meets the graph of `k` at time `T` exactly when `v` solves the gluing equation at the rate
  -- `l = e^{-T}`, whose solution `v l` depends continuously on `l`; the arc is
  -- `l ↦ ((g (v l), v l), (l • g (v l), k (l • g (v l))))`, read on `M`.
  have hpq' : p ≠ q := by rintro rfl; omega
  have hq := hX.mfderiv_eq_zero_of_mem_stableSet ha₁.2
  have hqq := hX.mem_unstableSet_inter_stableSet_self hq
  obtain ⟨φ, ρ, hφ, hρ, hT, hloc⟩ := hX.exists_morseChart_box hf hq
  have hsmall : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε ∧ 2 * ε < ρ := by
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (gt_mem_nhds (half_pos hρ))]
      with ε hε hερ
    exact ⟨hε, by linarith⟩
  obtain ⟨ε, ⟨T₁, hy₁φ, hy₁s, hy₁f⟩, hε, hερ⟩ :=
    ((hX.eventually_exists_flow_mem_entranceFace φ hφ hρ (fun w hw hwρ ↦ (hloc w hw hwρ).1) hpq'
      ha₁).and hsmall).exists
  set y₁ := hX.flow T₁ a₁
  have hy₁ : y₁ ∈ hX.flow.unstableSet p ∩ hX.flow.stableSet q :=
    hX.flow.isInvariant_unstableSet_inter_stableSet p q T₁ ha₁
  have hfa₁ := hX.mem_Ioo_of_mem_unstableSet_inter_stableSet hpq' ha₁
  have hε₂ : ∀ z, ‖z‖ ≤ 2 * ε → φ.coord.symm z ∈ φ.toChart.target := fun z hz ↦
    hT z (by linarith)
  have hε₁ : ∀ z, ‖z‖ ≤ ε → φ.coord.symm z ∈ φ.toChart.target := fun z hz ↦ hε₂ z (by linarith)
  set Φ : M → WithLp 2 (({i // φ.weight i = 1} → ℝ) × ({i // ¬φ.weight i = 1} → ℝ)) :=
    fun w ↦ φ.splitCoord (φ.coord (φ.toChart w)) with hΦdef
  set Ψ : WithLp 2 (({i // φ.weight i = 1} → ℝ) × ({i // ¬φ.weight i = 1} → ℝ)) → M :=
    fun z ↦ φ.toChart.symm (φ.coord.symm (φ.splitCoord.symm z)) with hΨdef
  have hΨΦ : ∀ w ∈ φ.toChart.source, Ψ (Φ w) = w := fun w hw ↦ by
    simp only [hΨdef, hΦdef, LinearEquiv.symm_apply_apply, φ.toChart.left_inv hw]
  have hΨ0 : Ψ 0 = q := by simp [hΨdef, φ.toChart_symm_zero]
  -- Near `y₁`: the point lies in the box near the entrance face.
  replace hy₁s : (Φ y₁).snd = 0 := hy₁s
  replace hy₁f : ‖(Φ y₁).fst‖ = ε := hy₁f
  have hy₁Φ : Φ y₁ = WithLp.toLp 2 ((Φ y₁).fst, 0) :=
    WithLp.ofLp_injective 2 (Prod.ext (by simp) (by simpa using hy₁s))
  obtain ⟨hA₁, hy₁κ⟩ := hX.eventually_of_entranceFace φ hε hερ hloc hy₁φ hy₁s hy₁f
  have hloc₁ : ∀ᶠ w in 𝓝 y₁, w ∈ hX.flow.stableSet q → (Φ w).snd = 0 :=
    hA₁.mono fun w hw ↦ hw.2.2.2.2.1
  -- The trace of `W^u(p)` on the entrance face is a graph `v ↦ (g v, v)`.
  obtain ⟨F₁, ι₁, ψ', hι₁0, hι₁, hι₁s, hψ, hψ', hexh₁⟩ :=
    h.exists_unstableSet_level_param hf hpq φ hy₁ hy₁φ hloc₁
  have hψs : ∀ᶠ z in 𝓝 (0 : F₁), φ.coord.symm (φ.splitCoord.symm (Φ (ι₁ z))) ∈
      φ.toChart.target ∧ Ψ (Φ (ι₁ z)) ∈ hX.flow.unstableSet p := by
    filter_upwards [hι₁.preimage_mem_nhds
      (by rw [hι₁0]; exact φ.toChart.open_source.mem_nhds hy₁φ), hι₁s] with z hzs hzu
    exact ⟨by simpa [hΦdef] using φ.toChart.map_source hzs, by rw [hΨΦ _ hzs]; exact hzu.1⟩
  obtain ⟨δ, hδ, Kg, g, hg, hg0, hgpts, hgexh⟩ :=
    hX.exists_lipschitzOnWith_entranceFace_graph φ hφ hε hε₂ hy₁φ hy₁s hy₁f hψ hψ'
      (by simp only [hι₁0]) hψs univ_mem
  have hgε : ∀ v ∈ closedBall (0 : {i // ¬φ.weight i = 1} → ℝ) δ, ‖g v‖ = ε := fun v hv ↦
    (hgpts v hv).1
  -- The points of the graph of `g` lie in `W^u(p)`.
  have hgu : ∀ v ∈ closedBall (0 : {i // ¬φ.weight i = 1} → ℝ) δ,
      Ψ (WithLp.toLp 2 (g v, v)) ∈ hX.flow.unstableSet p := by
    intro v hv
    obtain ⟨-, u, ⟨hu, -⟩, τ, hτ⟩ := hgpts v hv
    have h := (Flow.apply_mem_unstableSet_iff hX.flow τ).2 hu
    rwa [hτ] at h
  -- `Z` near the centre is a graph `u ↦ (u, k u)` through the centre.
  obtain ⟨η, hη, Kk, k, hk, hk₀, hkZ, hkexh⟩ := hX.exists_lipschitzOnWith_graph_of_isSliceChart φ
    hρ (fun w hw hwρ ↦ (hloc w hw hwρ).2) hqq.1 hφZ hZ hqφZ hqZ hdim htr
  -- A cube around the centre on which `f < f a₁`.
  have hΨc0 : ContinuousAt Ψ 0 := φ.continuousAt_toChart_symm_coord_symm_splitCoord_symm
    (by simpa using hε₁ 0 (by simp [hε.le]))
  have hfq : ∀ᶠ w in 𝓝 q, f w < f a₁ :=
    hX.mdifferentiable.continuous.continuousAt.eventually (gt_mem_nhds hfa₁.1)
  have hW : ∀ᶠ z in 𝓝 (0 : WithLp 2 (({i // φ.weight i = 1} → ℝ) ×
      ({i // ¬φ.weight i = 1} → ℝ))), f (Ψ z) < f a₁ :=
    hΨc0.tendsto.eventually (p := fun w ↦ f w < f a₁) (by rw [hΨ0]; exact hfq)
  obtain ⟨r, hr, hW'⟩ := WithLp.exists_pos_forall_toLp_mem_of_mem_nhds_zero hW
  -- The gluing rates `l ∈ [0, l₀]`, with the solution `v l` of the gluing equation.
  have hsmall₀ : ∀ᶠ l₀ in 𝓝[>] (0 : ℝ), 0 < l₀ ∧ l₀ * ε < ε ∧ l₀ * ε < r ∧
      l₀ * (Kk * ε) < r ∧ l₀ * (Kk * ε) < ε :=
    Filter.Eventually.and self_mem_nhdsWithin
      (((tendsto_mul_const_nhdsGT_zero ε).eventually (gt_mem_nhds hε)).and
        (((tendsto_mul_const_nhdsGT_zero ε).eventually (gt_mem_nhds hr)).and
          (((tendsto_mul_const_nhdsGT_zero (Kk * ε)).eventually (gt_mem_nhds hr)).and
            ((tendsto_mul_const_nhdsGT_zero (Kk * ε)).eventually (gt_mem_nhds hε)))))
  obtain ⟨l₀, ⟨v, hvc, hv₀, hv⟩, hl₀, hl₀₁, hl₀r, hl₀k, hl₀kε⟩ :=
    ((eventually_exists_continuousOn_smul_comp_smul_eq_iff hδ hη hg hgε hk hk₀).and
      hsmall₀).exists
  rw [mul_left_comm] at hl₀k hl₀kε
  have hl₀₁' : l₀ < 1 := by nlinarith
  -- Bounds along the family.
  have hfixed {l : ℝ} (hl : l ∈ Icc 0 l₀) : l • k (l • g (v l)) = v l :=
    ((hv l hl).2.2.2 _ (hv l hl).1).2 rfl
  have hnorm_g {l : ℝ} (hl : l ∈ Icc 0 l₀) : ‖l • g (v l)‖ = l * ε := by
    rw [norm_smul, Real.norm_of_nonneg hl.1, hgε _ (hv l hl).1]
  have hnorm_k {l : ℝ} (hl : l ∈ Icc 0 l₀) : ‖k (l • g (v l))‖ ≤ Kk * (l₀ * ε) :=
    (hv l hl).2.2.1.trans (by gcongr; exact hl.2)
  have hnorm_v {l : ℝ} (hl : l ∈ Icc 0 l₀) : ‖v l‖ ≤ ε := by
    rw [← hfixed hl, norm_smul, Real.norm_of_nonneg hl.1]
    exact (mul_le_of_le_one_left (norm_nonneg _) (by linarith [hl.2])).trans
      ((hnorm_k hl).trans hl₀kε.le)
  -- The arc: the entrance point `(g (v l), v l)` and the point `(l • g (v l), k (l • g (v l)))`
  -- of the graph of `k` on its orbit, read on `M`; both lie in the cube of radius `2 ε`.
  set B : Icc (0 : ℝ) l₀ → M × M := fun s ↦ (Ψ (WithLp.toLp 2 (g (v s), v s)),
    Ψ (WithLp.toLp 2 ((s : ℝ) • g (v s), k ((s : ℝ) • g (v s))))) with hBdef
  obtain ⟨hBc, hflowB, hBinj⟩ := hX.continuous_and_flow_neg_log_eq_of_smul_comp_smul_eq φ hφ hε
    hε₂ hg.continuousOn hk.continuousOn hl₀₁'.le hvc (fun l hl ↦ (hv l hl).1)
    (fun l hl ↦ (hv l hl).2.1) (fun l hl ↦ hgε _ (hv l hl).1) (fun _ ↦ hnorm_v)
    (fun _ hl ↦ (hnorm_k hl).trans hl₀kε.le) fun _ ↦ hfixed
  have hB₀ : B ⟨0, left_mem_Icc.2 hl₀.le⟩ = (y₁, q) := by
    simp only [hBdef, hv₀, hg0, zero_smul, hk₀]
    rw [← hy₁Φ, hΨΦ y₁ hy₁φ, Prod.mk_zero_zero, WithLp.toLp_zero, hΨ0]
  have hBS : ∀ s : Icc (0 : ℝ) l₀, (s : ℝ) ≠ 0 → (B s).1 ∈ hX.flow.unstableSet p ∧
      (B s).2 ∈ Z ∧ ∃ t, hX.flow t (B s).1 = (B s).2 :=
    fun s hs ↦ ⟨hgu _ (hv s s.property).1, hkZ _ (hv s s.property).2.1, _, hflowB s hs⟩
  have hBq : ∀ s : Icc (0 : ℝ) l₀, f (B s).2 < f a₁ := fun s ↦
    hW' _ _ (by rw [hnorm_g s.property]; nlinarith [s.property.1, s.property.2])
      ((hnorm_k s.property).trans_lt hl₀k)
  -- Every recorded pair near `(y₁, q)` is a point of the arc.
  have hfwd : ∀ᶠ w : M × M in 𝓝 (y₁, q),
      w.1 ∈ hX.flow.unstableSet p → f w.1 = f y₁ → w.2 ∈ Z → (∃ t, hX.flow t w.1 = w.2) →
      ∃ s : Icc (0 : ℝ) l₀, (s : ℝ) < l₀ ∧ (∃ t, hX.flow t w.1 = (B s).1) ∧ w.2 = (B s).2 := by
    filter_upwards [eventually_exists_flow_splitEntryTime_eq_and_eq_of_centre hX hf hpq' hqq.1
      (hfa₁.1.trans hfa₁.2) φ hφ hε hε₂ hδ hl₀ hl₀₁'.le
      (fun l hl y hy hfix ↦ ((hv l hl).2.2.2 y hy).1 hfix) hk₀
      (hA₁.mono fun w hw ↦ ⟨hw.1, hw.2.1, hw.2.2.1, hw.2.2.2.1⟩) hy₁κ
      ((hexh₁ _ (Filter.eventually_iff.1 hgexh)).mono fun w hw hwu hwf ↦ by
        obtain ⟨z, hz, rfl⟩ := hw hwu hwf
        exact hz)
      (hkexh.mono fun w hw hwZ ↦ (hw hwZ).2)] with w hw hw1u hw1f hw2Z hw12
    obtain ⟨l, hl, h₁, h₂⟩ := hw hw1u hw1f hw2Z hw12
    exact ⟨⟨l, Ico_subset_Icc_self hl⟩, hl.2, ⟨_, h₁⟩, h₂⟩
  exact ⟨T₁, l₀, hl₀, B, hBc, hB₀, hBS, hBq, hBinj, hfwd⟩

/-- **Gluing a broken trajectory into a transverse set.** Let `X` be a Morse–Smale adapted
pseudo-gradient for a Morse function `f` on a compact manifold of dimension `n`, `a₁` a point of a
trajectory from `p` to a critical point `q` with `ind p = ind q + 1`, and `y` a point of the
unstable manifold `W^u(q)`, possibly `q` itself. Let `Z` be a set through `y` of dimension
`n - ind q`, flattened near
`y` by a chart of the maximal atlas and transverse to `W^u(q)` at `y`, so that `W^u(p) ∩ Z` is
expected to be one-dimensional. Record a point `x` of `W^u(p) ∩ Z` by the pair `(w, x)` of the
point `w` of its orbit on the level of `a₁` and `x` itself, and the broken configuration by
`(a₁, y)`. Then `(a₁, y)` has a neighbourhood `N` among these pairs homeomorphic to a half-open
interval `[0, δ)`, with `(a₁, y)` corresponding to `0`.

So the broken configuration is an endpoint of the compactified space of the points of
`W^u(p) ∩ Z` whose orbits follow the trajectory through `a₁`. -/
theorem IsMorseSmale.exists_homeomorph_Ico_of_isSliceChart {hX : IsAdaptedPseudoGradient f X}
    (h : hX.IsMorseSmale) (hf : IsMorse 𝓘(ℝ, E) f) {p q a₁ y : M} {Z : Set M}
    (hpq : manifoldMorseIndex 𝓘(ℝ, E) f p = manifoldMorseIndex 𝓘(ℝ, E) f q + 1)
    (ha₁ : a₁ ∈ hX.flow.unstableSet p ∩ hX.flow.stableSet q) (hy : y ∈ hX.flow.unstableSet q)
    {L : Submodule ℝ E} {φZ : OpenPartialHomeomorph M E}
    (hφZ : φZ ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M) (hZ : IsSliceChart φZ (L : Set E) Z)
    (hyφZ : y ∈ φZ.source) (hyZ : y ∈ Z)
    (hdim : Module.finrank ℝ L + manifoldMorseIndex 𝓘(ℝ, E) f q = Module.finrank ℝ E)
    (htr : Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) Z y) ⊔
      Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX.flow.unstableSet q) y) = ⊤) :
    ∃ (N : Set (M × M)) (δ : ℝ) (hδ : 0 < δ) (e : Ico (0 : ℝ) δ ≃ₜ N),
      (e ⟨0, left_mem_Ico.2 hδ⟩ : M × M) = (a₁, y) ∧
      N ⊆ insert (a₁, y) {w | w.2 ∈ hX.flow.unstableSet p ∩ Z ∧ f w.1 = f a₁ ∧
        ∃ t, hX.flow t w.1 = w.2} ∧
      N ∈ 𝓝[insert (a₁, y) {w | w.2 ∈ hX.flow.unstableSet p ∩ Z ∧ f w.1 = f a₁ ∧
        ∃ t, hX.flow t w.1 = w.2}] (a₁, y) := by
  -- Plan: follow the arc `B` of `exists_transverseGluingArc` (for `y ≠ q`) or of
  -- `exists_centreGluingArc` (for `y = q`), its first points to the level of `a₁` and its second
  -- points back by the flow to `Z`. The resulting map `F` is continuous and injective on a closed
  -- interval, hence an embedding, and every pair near `(a₁, y)` is a value of `F` at a parameter
  -- below the end of the interval.
  have hpq' : p ≠ q := by rintro rfl; omega
  have hfa₁ := hX.mem_Ioo_of_mem_unstableSet_inter_stableSet hpq' ha₁
  obtain ⟨T₁, T₂, δ, hδ, B, hBc, hB₀, hBS, hBq, hBinj, hBfwd⟩ : ∃ (T₁ T₂ δ : ℝ) (hδ : 0 < δ)
      (B : Icc (0 : ℝ) δ → M × M), Continuous B ∧
      B ⟨0, left_mem_Icc.2 hδ.le⟩ = (hX.flow T₁ a₁, hX.flow T₂ y) ∧
      (∀ s : Icc (0 : ℝ) δ, (s : ℝ) ≠ 0 → (B s).1 ∈ hX.flow.unstableSet p ∧
        hX.flow (-T₂) (B s).2 ∈ Z ∧ ∃ t, hX.flow t (B s).1 = (B s).2) ∧
      (∀ s, f (B s).2 < f a₁) ∧
      (∀ s s' : Icc (0 : ℝ) δ, (s : ℝ) ≠ 0 → (s' : ℝ) ≠ 0 →
        (∃ t, hX.flow t (B s).1 = (B s').1) → (B s).2 = (B s').2 → s = s') ∧
      ∀ᶠ w : M × M in 𝓝 (hX.flow T₁ a₁, hX.flow T₂ y),
        w.1 ∈ hX.flow.unstableSet p → f w.1 = f (hX.flow T₁ a₁) → hX.flow (-T₂) w.2 ∈ Z →
        (∃ t, hX.flow t w.1 = w.2) →
        ∃ s : Icc (0 : ℝ) δ, (s : ℝ) < δ ∧ (∃ t, hX.flow t w.1 = (B s).1) ∧ w.2 = (B s).2 := by
    rcases eq_or_ne y q with rfl | hyq
    · obtain ⟨T₁, δ, hδ, B, hBc, hB₀, hBS, hBq, hBinj, hBfwd⟩ :=
        h.exists_centreGluingArc hf hpq ha₁ hφZ hZ hyφZ hyZ hdim htr
      refine ⟨T₁, 0, δ, hδ, B, hBc, by rw [hB₀, Flow.map_zero_apply], fun s hs ↦ ?_, hBq,
        fun s s' _ _ _ h ↦ hBinj s s' h, ?_⟩
      · rw [neg_zero, Flow.map_zero_apply]
        exact hBS s hs
      · simpa only [Flow.map_zero_apply, neg_zero] using hBfwd
    · obtain ⟨T₁, T₂, δ, hδ, B, hBc, hB₀, hBS, hBq, hBinj, hBfwd⟩ :=
        h.exists_transverseGluingArc hf hpq ha₁ hy hyq hφZ hZ hyφZ hyZ hdim htr
      exact ⟨T₁, T₂, δ, hδ, B, hBc, hB₀, hBS, fun s ↦ (hBq s).trans hfa₁.1,
        fun s s' hs hs' ⟨t, ht⟩ _ ↦ hBinj s s' hs hs' t ht, hBfwd⟩
  set S := {w : M × M | w.2 ∈ hX.flow.unstableSet p ∩ Z ∧ f w.1 = f a₁ ∧
    ∃ t, hX.flow t w.1 = w.2} with hSdef
  have hy₁ : hX.flow T₁ a₁ ∈ hX.flow.unstableSet p ∩ hX.flow.stableSet q :=
    hX.flow.isInvariant_unstableSet_inter_stableSet p q T₁ ha₁
  -- Along the arc, the first points run from `p` to a critical point below `f a₁`.
  have hB : ∀ s, ∃ b, p ≠ b ∧ (B s).1 ∈ hX.flow.unstableSet p ∩ hX.flow.stableSet b ∧
      f b < f a₁ := by
    intro s
    by_cases hs : (s : ℝ) = 0
    · obtain rfl : s = ⟨0, left_mem_Icc.2 hδ.le⟩ := Subtype.ext hs
      rw [hB₀]
      exact ⟨q, hpq', hy₁, hfa₁.1⟩
    · obtain ⟨hs₁, -, t, ht⟩ := hBS s hs
      exact exists_mem_unstableSet_inter_stableSet_of_apply_flow_lt hX hf hs₁ (t := t)
        (by rw [ht]; exact hBq s) hfa₁.2.le
  -- The level points along the arc, and the points of `Z`.
  set F : Icc (0 : ℝ) δ → M × M := fun s ↦
    (hX.flow (Flow.levelCrossingTime hX.flow f (f a₁) (B s).1) (B s).1,
      hX.flow (-T₂) (B s).2) with hFdef
  have hFc : Continuous F := by
    refine continuous_iff_continuousAt.2 fun s ↦ ?_
    obtain ⟨b, hpb, hb, hfb⟩ := hB s
    obtain ⟨σ₁, hσ₁, -⟩ :=
      hX.existsUnique_flow_eq_of_mem_unstableSet_inter_stableSet hpb hb hfb hfa₁.2
    have h₁ := hX.tendsto_flow_levelCrossingTime hpb hb hσ₁
      ((continuous_fst.comp hBc).tendsto s) (.of_forall fun s' ↦ by
        obtain ⟨b', hpb', hb', -⟩ := hB s'
        exact hX.strictAnti_flow_of_mem_unstableSet_inter_stableSet hpb' hb')
    have e₁ := Flow.flow_levelCrossingTime_flow
      (hX.strictAnti_flow_of_mem_unstableSet_inter_stableSet hpb hb) hσ₁ 0
    rw [Flow.map_zero_apply] at e₁
    rw [← e₁] at h₁
    exact h₁.prodMk_nhds (((hX.flow.continuous_toFun (-T₂)).comp
      (continuous_snd.comp hBc)).tendsto s)
  have hF₀ : F ⟨0, left_mem_Icc.2 hδ.le⟩ = (a₁, y) := by
    have e₁ := Flow.flow_levelCrossingTime_flow
      (hX.strictAnti_flow_of_mem_unstableSet_inter_stableSet hpq' ha₁)
      (by rw [Flow.map_zero_apply] : f (hX.flow 0 a₁) = f a₁) T₁
    rw [Flow.map_zero_apply] at e₁
    simp only [hFdef, hB₀, e₁, Flow.map_neg_apply_map]
  -- Away from `0`, the pairs are recorded points of `W^u(p) ∩ Z`.
  have hFS : ∀ s : Icc (0 : ℝ) δ, (s : ℝ) ≠ 0 → F s ∈ S := by
    intro s hs
    obtain ⟨hs₁, hsZ, t, ht⟩ := hBS s hs
    obtain ⟨b, hpb, hb, hfb⟩ := hB s
    obtain ⟨σ₁, hσ₁, -⟩ :=
      hX.existsUnique_flow_eq_of_mem_unstableSet_inter_stableSet hpb hb hfb hfa₁.2
    have e₁ := Flow.flow_levelCrossingTime_flow
      (hX.strictAnti_flow_of_mem_unstableSet_inter_stableSet hpb hb) hσ₁ 0
    rw [Flow.map_zero_apply] at e₁
    simp only [hFdef, hSdef, mem_ofPred_eq, e₁]
    refine ⟨⟨?_, hsZ⟩, hσ₁, -T₂ + t - σ₁, ?_⟩
    · rw [← ht, ← Flow.map_add]
      exact (Flow.apply_mem_unstableSet_iff _ _).2 hs₁
    · rw [← Flow.map_add, sub_add_cancel, Flow.map_add, ht]
  have hFinj : Injective F := by
    -- Off `0`, the second point lies in `W^u(p)`, which does not contain `y ∈ W^u(q)`.
    have hne : ∀ s : Icc (0 : ℝ) δ, (s : ℝ) ≠ 0 → F s ≠ (a₁, y) := fun s hs hF ↦ by
      have hu : (F s).2 ∈ hX.flow.unstableSet p := (hFS s hs).1.1
      rw [hF] at hu
      exact (Flow.disjoint_unstableSet hpq').ne_of_mem hu hy rfl
    intro s s' hss'
    by_cases hs : (s : ℝ) = 0
    · by_cases hs' : (s' : ℝ) = 0
      · exact Subtype.ext (hs.trans hs'.symm)
      · obtain rfl : s = ⟨0, left_mem_Icc.2 hδ.le⟩ := Subtype.ext hs
        rw [hF₀] at hss'
        exact absurd hss'.symm (hne s' hs')
    by_cases hs' : (s' : ℝ) = 0
    · obtain rfl : s' = ⟨0, left_mem_Icc.2 hδ.le⟩ := Subtype.ext hs'
      rw [hF₀] at hss'
      exact absurd hss' (hne s hs)
    -- Equal first level points put the first points of `B s` and `B s'` on one orbit, and the
    -- flow by `-T₂` is injective.
    refine hBinj s s' hs hs' ⟨Flow.levelCrossingTime hX.flow f (f a₁) (B s).1 -
      Flow.levelCrossingTime hX.flow f (f a₁) (B s').1, ?_⟩ ?_
    · have h₁ := congrArg Prod.fst hss'
      simp only [hFdef] at h₁
      rw [sub_eq_add_neg, add_comm, Flow.map_add, h₁, ← Flow.map_add, neg_add_cancel,
        Flow.map_zero_apply]
    · have h₂ := congrArg (fun w : M × M ↦ hX.flow T₂ w.2) hss'
      simpa only [hFdef, ← Flow.map_add, add_neg_cancel, Flow.map_zero_apply] using h₂
  -- Every recorded point near the broken configuration is a value of the arc.
  have hfwd : ∀ᶠ w in 𝓝[S] (a₁, y),
      ∃ s : Ico (0 : ℝ) δ, F (inclusion Ico_subset_Icc_self s) = w := by
    have hSmem : ∀ᶠ w in 𝓝[S] (a₁, y), w ∈ S := self_mem_nhdsWithin
    have hfy₁ := hX.mem_Ioo_of_mem_unstableSet_inter_stableSet hpq' hy₁
    -- `f y ≤ f q`, which is below the level of the entrance point `flow T₁ a₁`.
    have hfyq : f y < f (hX.flow T₁ a₁) :=
      (Flow.le_of_mem_unstableSet_of_antitone hy hX.mdifferentiable.continuous.continuousAt
        (hX.antitone_flow _)).trans_lt hfy₁.1
    have hlow : ∀ᶠ w in 𝓝[S] (a₁, y), f w.2 < f (hX.flow T₁ a₁) :=
      ((hX.mdifferentiable.continuous.comp continuous_snd).continuousAt.eventually
        (gt_mem_nhds hfyq)).filter_mono nhdsWithin_le_nhds
    -- The first points of recorded points lie on trajectories from `p` below that level.
    have hrec : ∀ w ∈ S, f w.2 < f (hX.flow T₁ a₁) → ∃ b, p ≠ b ∧
        w.1 ∈ hX.flow.unstableSet p ∩ hX.flow.stableSet b ∧ f b < f (hX.flow T₁ a₁) := by
      rintro w ⟨⟨hw2u, -⟩, -, t, ht⟩ hw2
      have hw1u : w.1 ∈ hX.flow.unstableSet p := by
        rw [← ht] at hw2u
        exact (Flow.apply_mem_unstableSet_iff _ _).1 hw2u
      exact exists_mem_unstableSet_inter_stableSet_of_apply_flow_lt hX hf hw1u (t := t)
        (by rw [ht]; exact hw2) hfy₁.2.le
    have hm₁ := hX.tendsto_flow_levelCrossingTime hpq' ha₁ (σ₀ := T₁) rfl
      ((continuous_fst.tendsto _).mono_left nhdsWithin_le_nhds)
      ((hSmem.and hlow).mono fun w ⟨hw, hw2⟩ ↦ by
        obtain ⟨b, hpb, hb, -⟩ := hrec w hw hw2
        exact hX.strictAnti_flow_of_mem_unstableSet_inter_stableSet hpb hb)
    have hm₂ : Tendsto (fun w : M × M ↦ hX.flow T₂ w.2) (𝓝[S] (a₁, y)) (𝓝 (hX.flow T₂ y)) :=
      (((hX.flow.continuous_toFun T₂).comp continuous_snd).tendsto _).mono_left
        nhdsWithin_le_nhds
    filter_upwards [hSmem, hlow, (hm₁.prodMk_nhds hm₂).eventually hBfwd] with w hw hw2 hfw
    obtain ⟨b, hpb, hb, hfb⟩ := hrec w hw hw2
    obtain ⟨⟨-, hw2Z⟩, hw1f, t, ht⟩ := hw
    have hanti₁ := hX.strictAnti_flow_of_mem_unstableSet_inter_stableSet hpb hb
    obtain ⟨σ₁, hσ₁, -⟩ := hX.existsUnique_flow_eq_of_mem_unstableSet_inter_stableSet hpb hb
      hfb hfy₁.2
    set τ₁ := Flow.levelCrossingTime hX.flow f (f (hX.flow T₁ a₁)) w.1
    obtain ⟨s, hs, ⟨t₁, ht₁⟩, ht₂⟩ := hfw
      ((Flow.apply_mem_unstableSet_iff _ _).2 hb.1) (Flow.apply_flow_levelCrossingTime ⟨σ₁, hσ₁⟩)
      (by rw [Flow.map_neg_apply_map]; exact hw2Z)
      ⟨T₂ + t - τ₁, by rw [← Flow.map_add, sub_add_cancel, Flow.map_add, ht]⟩
    refine ⟨⟨s, s.property.1, hs⟩, ?_⟩
    have e₁ := Flow.flow_levelCrossingTime_flow hanti₁
      (by rw [Flow.map_zero_apply]; exact hw1f : f (hX.flow 0 w.1) = f a₁) (t₁ + τ₁)
    rw [Flow.map_zero_apply, Flow.map_add] at e₁
    rw [ht₁] at e₁
    refine Prod.ext e₁ ?_
    simp only [hFdef]
    rw [← ht₂, Flow.map_neg_apply_map]
  have hemb : IsEmbedding (F ∘ inclusion (Ico_subset_Icc_self : Ico (0 : ℝ) δ ⊆ Icc 0 δ)) :=
    (hFc.isClosedEmbedding hFinj).isEmbedding.comp (IsEmbedding.inclusion Ico_subset_Icc_self)
  refine ⟨range (F ∘ inclusion Ico_subset_Icc_self), δ, hδ, hemb.toHomeomorph, hF₀, ?_, ?_⟩
  · rintro _ ⟨s, rfl⟩
    by_cases hs : (s : ℝ) = 0
    · left
      rw [← hF₀]
      exact congrArg F (Subtype.ext hs)
    · exact Or.inr (hFS _ hs)
  · rw [mem_nhdsWithin_insert]
    refine ⟨⟨⟨0, left_mem_Ico.2 hδ⟩, hF₀⟩, ?_⟩
    filter_upwards [hfwd] with w ⟨s, hs⟩ using ⟨s, hs⟩

/-- **The level cut of a stable manifold at a broken trajectory.** For a point `a₂` of a
trajectory from `q` to `r`, with `ind q = ind r + 1`, the level cut `W^s(r) ∩ {f = f a₂}` is
flattened near `a₂` by a chart of the maximal atlas onto a subspace of dimension `n - ind q`, and
is transverse to `W^u(q)` at `a₂`. -/
private theorem IsMorseSmale.exists_isSliceChart_stableSet_inter_level
    {hX : IsAdaptedPseudoGradient f X} (h : hX.IsMorseSmale) (hf : IsMorse 𝓘(ℝ, E) f)
    {q r a₂ : M}
    (hqr : manifoldMorseIndex 𝓘(ℝ, E) f q = manifoldMorseIndex 𝓘(ℝ, E) f r + 1)
    (ha₂ : a₂ ∈ hX.flow.unstableSet q ∩ hX.flow.stableSet r) :
    ∃ (L : Submodule ℝ E) (φZ : OpenPartialHomeomorph M E),
      φZ ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M ∧
      IsSliceChart φZ (L : Set E) (hX.flow.stableSet r ∩ f ⁻¹' {f a₂}) ∧ a₂ ∈ φZ.source ∧
      Module.finrank ℝ L + manifoldMorseIndex 𝓘(ℝ, E) f q = Module.finrank ℝ E ∧
      Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX.flow.stableSet r ∩ f ⁻¹' {f a₂}) a₂) ⊔
        Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX.flow.unstableSet q) a₂) = ⊤ := by
  have hqr' : q ≠ r := by rintro rfl; omega
  -- The level cut is flattened near `a₂`, since `df (X a₂) ≠ 0` and `X`
  -- is tangent to `W^s(r)`.
  obtain ⟨L, φr, hLr, ha₂φr, hφr, hSr⟩ :=
    hX.exists_isSliceChart_stableSet (hX.mfderiv_eq_zero_of_mem_stableSet ha₂.2) ha₂.2
  set T := Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX.flow.stableSet r) a₂) with hTdef
  set U := Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX.flow.unstableSet q) a₂)
  -- The differential of `f` at `a₂`, read on the model space. `mvfderiv` is a map on
  -- `TangentSpace 𝓘(ℝ, E) a₂`, which is `E` only by definition, so `rw` cannot pass between
  -- `mvfderiv` and `df`; the `change` steps below restate goals across this identification.
  set df : E →ₗ[ℝ] ℝ := (mvfderiv 𝓘(ℝ, E) f a₂).toLinearMap
  set v₀ : E := X a₂
  have hXT : v₀ ∈ T := Submodule.subset_span
    (hX.mem_mtangentConeAt_of_isInvariant (hX.flow.isInvariant_stableSet r) ha₂.2)
  have hXU : v₀ ∈ U := Submodule.subset_span
    (hX.mem_mtangentConeAt_of_isInvariant (hX.flow.isInvariant_unstableSet q) ha₂.1)
  have hdf : df v₀ ≠ 0 := (hX.mvfderiv_apply_lt_zero a₂
    (hX.mfderiv_ne_zero_of_mem_unstableSet_inter_stableSet hqr' ha₂)).ne
  have hrange : (mvfderiv 𝓘(ℝ, E) f a₂).range = ⊤ :=
    LinearMap.range_eq_top_of_surjective _ fun c ↦ ⟨(c / df v₀) • v₀, by
      -- Read the differential on `E` (see `df`).
      change df ((c / df v₀) • v₀) = c
      rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hdf]⟩
  set K : Submodule ℝ E := LinearMap.ker df with hKdef
  have htrK : T ⊔ K = ⊤ := top_unique <|
    (LinearMap.span_singleton_sup_ker_eq_top df hdf).ge.trans
      (sup_le_sup_right ((Submodule.span_singleton_le_iff_mem _ _).2 hXT) _)
  have hcc (P : Submodule ℝ E) : P.ClosedComplemented :=
    .of_finiteDimensional_quotient (Submodule.isClosed_of_finiteDimensional _)
  obtain ⟨φZ, ha₂φZ, hφZ, hZ⟩ :=
    exists_isSliceChart_inter_preimage_of_span_mtangentConeAt_sup_ker_eq_top (by simp) hφr hSr
      ha₂φr isOpen_univ (mem_univ _) hf.contMDiff.contMDiffOn rfl hrange htrK (hcc _) (hcc _)
      (hcc _)
  have hspan := span_mtangentConeAt_inter_preimage_of_span_mtangentConeAt_sup_ker_eq_top
    (by simp) hφr hSr ha₂φr isOpen_univ (mem_univ _) hf.contMDiff.contMDiffOn rfl hrange
    htrK (hcc _) (hcc _) (hcc _)
  -- Read the kernel of the differential on `E` (see `df`).
  rw [← hTdef] at hspan
  change _ = T ⊓ K at hspan
  -- It has dimension `n - ind q`: cutting `W^s(r)` by the transverse hyperplane `ker df`.
  have hdim : Module.finrank ℝ ↥(T ⊓ K) + manifoldMorseIndex 𝓘(ℝ, E) f q =
      Module.finrank ℝ E := by
    have hT := hX.finrank_span_mtangentConeAt_stableSet_add_manifoldMorseIndex ha₂.2
    have hsum := Submodule.finrank_sup_add_finrank_inf_eq T K
    have hker := LinearMap.finrank_range_add_finrank_ker df
    rw [htrK, finrank_top] at hsum
    -- Read the range of the differential on `E` (see `df`).
    rw [show LinearMap.range df = ⊤ from hrange, finrank_top, Module.finrank_self, ← hKdef]
      at hker
    rw [← hTdef] at hT
    omega
  -- It is transverse to `W^u(q)`: a tangent vector of `W^s(r)` is a vector of the cut plus a
  -- multiple of `X a₂`, which is tangent to `W^u(q)`.
  have htr : Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E)
      (hX.flow.stableSet r ∩ f ⁻¹' {f a₂}) a₂) ⊔ U = ⊤ := by
    rw [hspan]
    refine top_unique ((h.span_mtangentConeAt_sup_eq_top ha₂).symm.le.trans
      (sup_le (le_sup_right) fun v hv ↦ ?_))
    have hv' : v - (df v / df v₀) • v₀ ∈ T ⊓ K := by
      refine Submodule.mem_inf.2 ⟨T.sub_mem hv (T.smul_mem _ hXT), ?_⟩
      rw [hKdef, LinearMap.mem_ker, map_sub, map_smul, smul_eq_mul, div_mul_cancel₀ _ hdf,
        sub_self]
    exact Submodule.mem_sup.2 ⟨_, hv', _, U.smul_mem _ hXU, sub_add_cancel _ _⟩
  exact ⟨_, φZ, hφZ, hZ, ha₂φZ, hdim, htr⟩

/-- **Gluing at a broken trajectory.** Let `X` be a Morse–Smale adapted pseudo-gradient for a
Morse function `f` on a compact manifold, and `p`, `q`, `r` critical points of consecutive indices
`ind p = ind q + 1 = ind r + 2`. Record trajectories from `p` to `r` by their points on two levels:
take a point `a₁` of a trajectory from `p` to `q` and a point `a₂` of a trajectory from `q` to `r`,
and let `S` be the set of pairs `(w₁, w₂)` of points of one trajectory from `p` to `r` with
`f w₁ = f a₁` and `f w₂ = f a₂`. Then the broken trajectory `(a₁, a₂)` has a neighbourhood `N` in
`S ∪ {(a₁, a₂)}` homeomorphic to a half-open interval `[0, δ)`, with `(a₁, a₂)` corresponding to
`0`.

So the broken trajectories are endpoints of the compactified space of index-two trajectories
recorded on two levels, and every broken trajectory is a limit of unbroken ones. This is the case
of `IsMorseSmale.exists_homeomorph_Ico_of_isSliceChart` in which the transverse set is the level
cut `W^s(r) ∩ {f = f a₂}`. -/
theorem IsMorseSmale.exists_homeomorph_Ico_of_mem_unstableSet_inter_stableSet
    {hX : IsAdaptedPseudoGradient f X} (h : hX.IsMorseSmale) (hf : IsMorse 𝓘(ℝ, E) f)
    {p q r a₁ a₂ : M}
    (hpq : manifoldMorseIndex 𝓘(ℝ, E) f p = manifoldMorseIndex 𝓘(ℝ, E) f q + 1)
    (hqr : manifoldMorseIndex 𝓘(ℝ, E) f q = manifoldMorseIndex 𝓘(ℝ, E) f r + 1)
    (ha₁ : a₁ ∈ hX.flow.unstableSet p ∩ hX.flow.stableSet q)
    (ha₂ : a₂ ∈ hX.flow.unstableSet q ∩ hX.flow.stableSet r) :
    ∃ (N : Set (M × M)) (δ : ℝ) (hδ : 0 < δ) (e : Ico (0 : ℝ) δ ≃ₜ N),
      (e ⟨0, left_mem_Ico.2 hδ⟩ : M × M) = (a₁, a₂) ∧
      N ⊆ insert (a₁, a₂) {w | w.1 ∈ hX.flow.unstableSet p ∩ hX.flow.stableSet r ∧
        f w.1 = f a₁ ∧ f w.2 = f a₂ ∧ ∃ t, hX.flow t w.1 = w.2} ∧
      N ∈ 𝓝[insert (a₁, a₂) {w | w.1 ∈ hX.flow.unstableSet p ∩ hX.flow.stableSet r ∧
        f w.1 = f a₁ ∧ f w.2 = f a₂ ∧ ∃ t, hX.flow t w.1 = w.2}] (a₁, a₂) := by
  -- The transverse set is the level cut `W^s(r) ∩ {f = f a₂}`.
  obtain ⟨L, φZ, hφZ, hZ, ha₂φZ, hdim, htr⟩ :=
    h.exists_isSliceChart_stableSet_inter_level hf hqr ha₂
  obtain ⟨N, δ, hδ, e, he₀, hN, hNw⟩ :=
    h.exists_homeomorph_Ico_of_isSliceChart hf hpq ha₁ ha₂.1 hφZ hZ ha₂φZ ⟨ha₂.2, rfl⟩
      hdim htr
  -- The recorded points of `W^u(p) ∩ Z` are the pairs of points of trajectories from `p` to `r`.
  have hS : {w : M × M | w.2 ∈ hX.flow.unstableSet p ∩ (hX.flow.stableSet r ∩ f ⁻¹' {f a₂}) ∧
      f w.1 = f a₁ ∧ ∃ t, hX.flow t w.1 = w.2} =
      {w | w.1 ∈ hX.flow.unstableSet p ∩ hX.flow.stableSet r ∧
        f w.1 = f a₁ ∧ f w.2 = f a₂ ∧ ∃ t, hX.flow t w.1 = w.2} := by
    ext w
    simp only [mem_ofPred_eq, mem_inter_iff, mem_preimage, mem_singleton_iff]
    constructor
    · rintro ⟨⟨hu, hs, hw2⟩, hw1, t, ht⟩
      rw [← ht] at hu hs
      exact ⟨⟨(Flow.apply_mem_unstableSet_iff _ _).1 hu, (Flow.apply_mem_stableSet_iff _ _).1 hs⟩,
        hw1, hw2, t, ht⟩
    · rintro ⟨⟨hu, hs⟩, hw1, hw2, t, ht⟩
      refine ⟨⟨?_, ?_, hw2⟩, hw1, t, ht⟩
      · rw [← ht]; exact (Flow.apply_mem_unstableSet_iff _ _).2 hu
      · rw [← ht]; exact (Flow.apply_mem_stableSet_iff _ _).2 hs
  rw [hS] at hN hNw
  exact ⟨N, δ, hδ, e, he₀, hN, hNw⟩

end IsAdaptedPseudoGradient

end TauCeti
