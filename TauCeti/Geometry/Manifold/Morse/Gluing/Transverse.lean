/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Gluing.Broken
import TauCeti.Analysis.Calculus.Morse.Gluing.Centre
import TauCeti.Analysis.Normed.Lp.ProdLp
import TauCeti.Dynamics.Flow.Lyapunov
import TauCeti.Data.Set.Function

/-!
# Half-open gluing charts into a transverse set

Let `f` be a Morse function on a compact boundaryless manifold `M` of dimension `n`, `X` a
pseudo-gradient adapted to `f` satisfying the Morse–Smale condition, `a₁` a point of a trajectory
from a critical point `p` to a critical point `q` with `ind p = ind q + 1`, and `y` a point of the
unstable manifold `W^u(q)`, possibly `q` itself. Let `Z` be a set of dimension `n - ind q` through
`y`, flattened near `y` by a chart of the maximal atlas and transverse to `W^u(q)` at `y`. Then
`W^u(p) ∩ Z` is expected to be one-dimensional, and its points whose orbits follow the trajectory
through `a₁` accumulate at `y`
(`IsMorseSmale.exists_mem_unstableSet_inter_flow_mem_of_isSliceChart`). This file shows that they
form a half-open arc ending at `y`.

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
  `TauCeti.Geometry.Manifold.Morse.Gluing.Pair`). There `y` may be the critical point at which
  the configuration breaks, as for the identity continuation `X₀ = X₁`, where every broken
  configuration is of this kind.

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

For `y = q` the set `Z` passes through the centre of the box, where it is the graph `u ↦ (u, k u)`
of a Lipschitz map with `k 0 = 0`, and the model gluing at the centre
(`TauCeti.exists_homeomorph_closure_splitCenterBallGluingPairs`) joins the trace of `W^u(p)` on the
entrance face to it. The orbit of a point near `q` crosses the entrance face once near the
trajectory through `a₁`, also when it lies on the stable set of `q`
(`TauCeti.IsAdaptedPseudoGradient.eq_of_flow_eq_of_norm_fst_eq`), so every point of `W^u(p) ∩ Z`
near `q` whose orbit passes near `a₁` lies on the arc. In both cases the arc is read on the level
of `a₁` in the same way.

## Main results

In the namespace `TauCeti.IsAdaptedPseudoGradient`:

* `IsMorseSmale.exists_homeomorph_Ico_of_isSliceChart`: the half-open gluing chart into a
  transverse set, also through the critical point `q`.
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

open Filter Function Set Topology
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

omit [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M] [T2Space M] in
/-- **The box near the centre lies below a level.** Let `φ` be a Morse chart at `q`, where `f` is
continuous, and `c > f q`. For some `ρc > 0`, the points of the chart with split coordinates
`(u, v)`, `‖u‖ < ρc` and `‖v‖ < ρc`, lie below the level `c`. -/
private theorem MorseChart.exists_pos_forall_norm_lt_apply_lt {q : M} (φ : MorseChart E f q)
    (hf : ContinuousAt f q) {c : ℝ} (hqc : f q < c) :
    ∃ ρc > 0, ∀ z : WithLp 2 (({i // φ.weight i = 1} → ℝ) × ({i // ¬φ.weight i = 1} → ℝ)),
      ‖z.fst‖ < ρc → ‖z.snd‖ < ρc →
        f (φ.toChart.symm (φ.coord.symm (φ.splitCoord.symm z))) < c := by
  have h0 : φ.coord.symm (φ.splitCoord.symm 0) ∈ φ.toChart.target := by
    simpa using φ.toChart.map_source φ.mem_source
  have hW : (fun z ↦ φ.toChart.symm (φ.coord.symm (φ.splitCoord.symm z))) ⁻¹' {w | f w < c} ∈
      𝓝 0 := by
    refine (φ.continuousAt_toChart_symm_coord_symm_splitCoord_symm h0).preimage_mem_nhds ?_
    simpa using hf.preimage_mem_nhds (gt_mem_nhds hqc)
  obtain ⟨ρc, hρc, hρcW⟩ := WithLp.exists_pos_forall_toLp_mem_of_mem_nhds_zero hW
  exact ⟨ρc, hρc, fun z hu hv ↦ hρcW z.fst z.snd hu hv⟩

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
  have hL : IsClosed (L : Set E) := Submodule.isClosed_of_finiteDimensional _
  have hdimZ' : Module.finrank ℝ (Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) Z' y₂)) =
      Module.finrank ℝ L := hZ'.finrank_span_mtangentConeAt (by simp) hφ' hL hy₂φ' hy₂Z
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
  set P := WithLp.fstL 2 ℝ ({i // φ.weight i = 1} → ℝ) ({i // ¬φ.weight i = 1} → ℝ) ∘L
    φ.splitCoordL.toContinuousLinearMap
  have hPs : Function.Surjective P := fun b ↦ by
    obtain ⟨u, hu⟩ := φ.splitCoordL.surjective (WithLp.toLp 2 (b, 0))
    exact ⟨u, by simp [P, hu]⟩
  obtain ⟨ι₂, ι₂', hι₂0, hι₂, hι₂s, hd₂, hinv₂, hexh₂⟩ :=
    exists_param_of_span_mtangentConeAt_sup_eq_top (by simp) hφ' hZ' hy₂φ' hy₂Z hy₂.1 htr'
      (by have := φ.finrank_fst_splitCoord_add_manifoldMorseIndex; rw [hdimZ']; omega)
      φ.mem_maximalAtlas hy₂φ hPs (by simpa [P] using hloc₂)
  have hχ : HasStrictFDerivAt (fun z ↦ Φ (ι₂ z)) ((φ.splitCoordL : E →L[ℝ] _) ∘L ι₂') 0 := by
    simpa using φ.splitCoordL.hasStrictFDerivAt.comp 0 hd₂
  have hχ' : (WithLp.fstL 2 ℝ ({i // φ.weight i = 1} → ℝ) ({i // ¬φ.weight i = 1} → ℝ) ∘L
      ((φ.splitCoordL : E →L[ℝ] _) ∘L ι₂')).IsInvertible := by
    rwa [← ContinuousLinearMap.comp_assoc]
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
    have h1 := hX.eq_of_flow_eq_of_norm_fst_eq φ hφ hε₁ hsrc.1 hsrc.2.2 hsrc'.1 hsrc'.2.2
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

/-- **From a gluing arc to a half-open chart.** Let `a₁` be a point of a trajectory from `p` to
`q ≠ p`, `y` a point, `Z` a set, and `B` a continuous arc in `M × M` starting at
`(flow T₁ a₁, flow T₂ y)`, along which, for `s ≠ 0`, `(B s).1` lies in `W^u(p)` and flows to the
point `(B s).2` of `flow (-T₂) ⁻¹' Z`, below a level `c` under `f a₁` and `f (flow T₁ a₁)`. If the
second points of the arc are distinct and every such pair near the start, the first point on the
level of `flow T₁ a₁`, is reached by the arc below its end, then the broken configuration
`(a₁, y)` has a neighbourhood among the recorded points of `W^u(p) ∩ Z` homeomorphic to a
half-open interval, as in `IsMorseSmale.exists_homeomorph_Ico_of_isSliceChart`. -/
private theorem exists_homeomorph_Ico_of_gluingArc {hX : IsAdaptedPseudoGradient f X}
    (hf : IsMorse 𝓘(ℝ, E) f) {p q a₁ y : M} {Z : Set M} (hpq' : p ≠ q)
    (ha₁ : a₁ ∈ hX.flow.unstableSet p ∩ hX.flow.stableSet q) {c T₁ T₂ δ : ℝ} (hδ : 0 < δ)
    (hca₁ : c < f a₁) (hcT₁ : c < f (hX.flow T₁ a₁)) (hfy : f y < c)
    {B : Icc (0 : ℝ) δ → M × M} (hBc : Continuous B)
    (hB₀ : B ⟨0, left_mem_Icc.2 hδ.le⟩ = (hX.flow T₁ a₁, hX.flow T₂ y))
    (hBS : ∀ s : Icc (0 : ℝ) δ, (s : ℝ) ≠ 0 → (B s).1 ∈ hX.flow.unstableSet p ∧
      hX.flow (-T₂) (B s).2 ∈ Z ∧ ∃ t, hX.flow t (B s).1 = (B s).2)
    (hBc' : ∀ s, f (B s).2 < c) (hBinj : Injective fun s ↦ (B s).2)
    (hBfwd : ∀ᶠ w : M × M in 𝓝 (hX.flow T₁ a₁, hX.flow T₂ y),
      w.1 ∈ hX.flow.unstableSet p → f w.1 = f (hX.flow T₁ a₁) → hX.flow (-T₂) w.2 ∈ Z →
      (∃ t, hX.flow t w.1 = w.2) →
      ∃ s : Icc (0 : ℝ) δ, (s : ℝ) < δ ∧ (∃ t, hX.flow t w.1 = (B s).1) ∧ w.2 = (B s).2) :
    ∃ (N : Set (M × M)) (δ : ℝ) (hδ : 0 < δ) (e : Ico (0 : ℝ) δ ≃ₜ N),
      (e ⟨0, left_mem_Ico.2 hδ⟩ : M × M) = (a₁, y) ∧
      N ⊆ insert (a₁, y) {w | w.2 ∈ hX.flow.unstableSet p ∩ Z ∧ f w.1 = f a₁ ∧
        ∃ t, hX.flow t w.1 = w.2} ∧
      N ∈ 𝓝[insert (a₁, y) {w | w.2 ∈ hX.flow.unstableSet p ∩ Z ∧ f w.1 = f a₁ ∧
        ∃ t, hX.flow t w.1 = w.2}] (a₁, y) := by
  -- Plan: follow the arc `B`, its first points to the level of `a₁` and its second points back
  -- by the flow to `Z`. The resulting map `F` is continuous and injective on a closed interval,
  -- hence an embedding, and every pair near `(a₁, y)` is a value of `F` at a parameter below the
  -- end of the interval.
  set S := {w : M × M | w.2 ∈ hX.flow.unstableSet p ∩ Z ∧ f w.1 = f a₁ ∧
    ∃ t, hX.flow t w.1 = w.2} with hSdef
  have hfa₁ := hX.mem_Ioo_of_mem_unstableSet_inter_stableSet hpq' ha₁
  have hy₁ : hX.flow T₁ a₁ ∈ hX.flow.unstableSet p ∩ hX.flow.stableSet q :=
    hX.flow.isInvariant_unstableSet_inter_stableSet p q T₁ ha₁
  -- Along the arc, the first points run from `p` to a critical point below `c`, except at `0`,
  -- where the trajectory runs to `q`.
  have hBb : ∀ s : Icc (0 : ℝ) δ, (s : ℝ) ≠ 0 → ∃ b, p ≠ b ∧
      (B s).1 ∈ hX.flow.unstableSet p ∩ hX.flow.stableSet b ∧ f b < c := by
    intro s hs
    obtain ⟨hs₁, -, t, ht⟩ := hBS s hs
    exact exists_mem_unstableSet_inter_stableSet_of_apply_flow_lt hX hf hs₁ (t := t)
      (by rw [ht]; exact hBc' s) (by linarith [hfa₁.1, hfa₁.2])
  have hB : ∀ s, ∃ b, p ≠ b ∧ (B s).1 ∈ hX.flow.unstableSet p ∩ hX.flow.stableSet b ∧
      f b < f a₁ := by
    intro s
    by_cases hs : (s : ℝ) = 0
    · obtain rfl : s = ⟨0, left_mem_Icc.2 hδ.le⟩ := Subtype.ext hs
      rw [hB₀]
      exact ⟨q, hpq', hy₁, hfa₁.1⟩
    · obtain ⟨b, hpb, hb, hfb⟩ := hBb s hs
      exact ⟨b, hpb, hb, hfb.trans hca₁⟩
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
  -- Distinct parameters give distinct second points.
  have hFinj : Injective F := fun s s' hss' ↦ hBinj (by
    have h₂ := congrArg (fun w ↦ hX.flow T₂ w.2) hss'
    simpa only [hFdef, Flow.map_apply_map_neg] using h₂)
  -- Every recorded point near the broken configuration is a value of the arc.
  have hfwd : ∀ᶠ w in 𝓝[S] (a₁, y),
      ∃ s : Ico (0 : ℝ) δ, F (inclusion Ico_subset_Icc_self s) = w := by
    have hSmem : ∀ᶠ w in 𝓝[S] (a₁, y), w ∈ S := self_mem_nhdsWithin
    have hlow : ∀ᶠ w in 𝓝[S] (a₁, y), f w.2 < c :=
      ((hX.mdifferentiable.continuous.comp continuous_snd).continuousAt.eventually
        (gt_mem_nhds hfy)).filter_mono nhdsWithin_le_nhds
    -- The first points of recorded points lie on trajectories from `p` below `c`.
    have hrec : ∀ w ∈ S, f w.2 < c → ∃ b, p ≠ b ∧
        w.1 ∈ hX.flow.unstableSet p ∩ hX.flow.stableSet b ∧ f b < c := by
      rintro w ⟨⟨hw2u, -⟩, -, t, ht⟩ hw2
      have hw1u : w.1 ∈ hX.flow.unstableSet p := by
        rw [← ht] at hw2u
        exact (Flow.apply_mem_unstableSet_iff _ _).1 hw2u
      exact exists_mem_unstableSet_inter_stableSet_of_apply_flow_lt hX hf hw1u (t := t)
        (by rw [ht]; exact hw2) (by linarith [hfa₁.1, hfa₁.2])
    have hm₁ := hX.tendsto_flow_levelCrossingTime hpq' ha₁ (σ₀ := T₁) rfl
      ((continuous_fst.tendsto _).mono_left nhdsWithin_le_nhds)
      ((hSmem.and hlow).mono fun w ⟨hw, hw2⟩ ↦ by
        obtain ⟨b, hpb, hb, -⟩ := hrec w hw hw2
        exact hX.strictAnti_flow_of_mem_unstableSet_inter_stableSet hpb hb)
    have hm₂ : Tendsto (fun w : M × M ↦ hX.flow T₂ w.2) (𝓝[S] (a₁, y)) (𝓝 (hX.flow T₂ y)) :=
      (((hX.flow.continuous_toFun T₂).comp continuous_snd).tendsto _).mono_left
        nhdsWithin_le_nhds
    have hfy₁ := hX.mem_Ioo_of_mem_unstableSet_inter_stableSet hpq' hy₁
    filter_upwards [hSmem, hlow, (hm₁.prodMk_nhds hm₂).eventually hBfwd] with w hw hw2 hfw
    obtain ⟨b, hpb, hb, hfb⟩ := hrec w hw hw2
    obtain ⟨⟨-, hw2Z⟩, hw1f, t, ht⟩ := hw
    have hanti₁ := hX.strictAnti_flow_of_mem_unstableSet_inter_stableSet hpb hb
    obtain ⟨σ₁, hσ₁, -⟩ := hX.existsUnique_flow_eq_of_mem_unstableSet_inter_stableSet hpb hb
      (by linarith) hfy₁.2
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

/-- **A transverse set through the critical point is a graph near the centre.** Let `φ` be a Morse
chart at the critical point `q`, on whose cube of radius `ρ` the unstable set of `q` is the plane
where the contracting split coordinate `u` vanishes, and let `Z` be a set through `q` of dimension
`n - ind q`, flattened near `q` by a chart of the maximal atlas and transverse to `W^u(q)` at `q`.
Near the centre, `Z` is the graph of a Lipschitz map `u ↦ k u` with `k 0 = 0`: the points of the
chart with split coordinates `(u, k u)` lie in `Z`, and near `q` the split coordinates of every
point of `Z` lie on the graph of `k`. -/
private theorem exists_lipschitzOnWith_graph_of_isSliceChart (hX : IsAdaptedPseudoGradient f X)
    {q : M} (hq : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f q = 0) (φ : MorseChart E f q) {ρ : ℝ} (hρ : 0 < ρ)
    (hloc : ∀ w ∈ φ.toChart.source, ‖φ.coord (φ.toChart w)‖ < ρ →
      (w ∈ hX.flow.unstableSet q ↔ (φ.splitCoord (φ.coord (φ.toChart w))).fst = 0))
    {Z : Set M} {L : Submodule ℝ E} {φZ : OpenPartialHomeomorph M E}
    (hφZ : φZ ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M) (hZ : IsSliceChart φZ (L : Set E) Z)
    (hqφZ : q ∈ φZ.source) (hqZ : q ∈ Z)
    (hdim : Module.finrank ℝ L + manifoldMorseIndex 𝓘(ℝ, E) f q = Module.finrank ℝ E)
    (htr : Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) Z q) ⊔
      Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX.flow.unstableSet q) q) = ⊤) :
    ∃ η > 0, ∃ (K : NNReal) (k : ({i // φ.weight i = 1} → ℝ) → {i // ¬φ.weight i = 1} → ℝ),
      LipschitzOnWith K k (Metric.closedBall 0 η) ∧ k 0 = 0 ∧
      (∀ u ∈ Metric.closedBall 0 η,
        φ.coord.symm (φ.splitCoord.symm (WithLp.toLp 2 (u, k u))) ∈ φ.toChart.target ∧
        φ.toChart.symm (φ.coord.symm (φ.splitCoord.symm (WithLp.toLp 2 (u, k u)))) ∈ Z) ∧
      ∀ᶠ w in 𝓝 q, w ∈ Z → (φ.splitCoord (φ.coord (φ.toChart w))).snd =
        k (φ.splitCoord (φ.coord (φ.toChart w))).fst := by
  set Φ : M → WithLp 2 (({i // φ.weight i = 1} → ℝ) × ({i // ¬φ.weight i = 1} → ℝ)) :=
    fun w ↦ φ.splitCoord (φ.coord (φ.toChart w)) with hΦdef
  -- Near `q` the unstable set of `q` is the kernel of the contracting coordinate `u`, and `Z`,
  -- of the complementary dimension, is parametrized transversally to it.
  set P := WithLp.fstL 2 ℝ ({i // φ.weight i = 1} → ℝ) ({i // ¬φ.weight i = 1} → ℝ) ∘L
    φ.splitCoordL.toContinuousLinearMap
  have hPs : Function.Surjective P := fun b ↦ by
    obtain ⟨u, hu⟩ := φ.splitCoordL.surjective (WithLp.toLp 2 (b, 0))
    exact ⟨u, by simp [P, hu]⟩
  have hsP : ∀ᶠ w in 𝓝 q, w ∈ hX.flow.unstableSet q → P (φ.toChart w) = 0 := by
    filter_upwards [φ.eventually_mem_source_norm_coord_lt hρ] with w ⟨hw, hwρ⟩ hwu
    simpa [P] using (hloc w hw hwρ).1 hwu
  have hdimZ : Module.finrank ℝ (Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) Z q)) =
      Module.finrank ℝ L :=
    hZ.finrank_span_mtangentConeAt (by simp) hφZ (Submodule.isClosed_of_finiteDimensional _)
      hqφZ hqZ
  obtain ⟨ι, ι', hι0, hι, hιs, hd, hinv, hexh⟩ :=
    exists_param_of_span_mtangentConeAt_sup_eq_top (by simp) hφZ hZ hqφZ hqZ
      (hX.mem_unstableSet_inter_stableSet_self hq).1 htr
      (by have := φ.finrank_fst_splitCoord_add_manifoldMorseIndex; rw [hdimZ]; omega)
      φ.mem_maximalAtlas φ.mem_source hPs hsP
  have hχ : HasStrictFDerivAt (fun z ↦ Φ (ι z)) ((φ.splitCoordL : E →L[ℝ] _) ∘L ι') 0 := by
    simpa using φ.splitCoordL.hasStrictFDerivAt.comp 0 hd
  have hχ' : (WithLp.fstL 2 ℝ ({i // φ.weight i = 1} → ℝ) ({i // ¬φ.weight i = 1} → ℝ) ∘L
      ((φ.splitCoordL : E →L[ℝ] _) ∘L ι')).IsInvertible := by
    rwa [← ContinuousLinearMap.comp_assoc]
  have hV : {z | ι z ∈ Z ∧ ι z ∈ φ.toChart.source} ∈ 𝓝 0 :=
    hιs.and (hι.preimage_mem_nhds (by rw [hι0]; exact φ.toChart.open_source.mem_nhds φ.mem_source))
  obtain ⟨η, hη, K, k, hk, hk₀, hkpts, hkexh⟩ :=
    exists_lipschitzOnWith_graph_of_hasStrictFDerivAt hχ hχ' (by simp [hΦdef, hι0, φ.apply_self])
      hV
  refine ⟨η, hη, K, k, hk, hk₀, fun u hu ↦ ?_, ?_⟩
  · -- The point over `u` is the point of `Z` with split coordinates `(u, k u)`.
    obtain ⟨z, ⟨hzZ, hzs⟩, hz⟩ := hkpts u hu
    rw [← hz]
    simpa [hΦdef, φ.toChart.left_inv hzs] using ⟨φ.toChart.map_source hzs, hzZ⟩
  · filter_upwards [hexh _ hkexh] with w hw hwZ
    obtain ⟨z, hz, rfl⟩ := hw hwZ
    exact hz.2

/-- **A gluing pair at the centre, read on the manifold.** Let `φ` be a Morse chart at `q` in which
`X` is linear and which contains the cube of radius `ε`, let `g` take values on the sphere of
radius `ε` and `k` be `Kk`-Lipschitz with `k 0 = 0`, over closed balls of radius `r₀ ε ≤ ε`, with
`Kk r₀ ε ≤ ε`. The two points of a gluing pair at the centre are the split coordinates of points of
the chart, the first of which flows to the second, and the expanding coordinate of the second has
norm at most `Kk r₀ ε`. -/
private theorem exists_flow_eq_of_mem_splitCenterBallGluingPairs (hX : IsAdaptedPseudoGradient f X)
    {q : M} (φ : MorseChart E f q)
    (hφ : ∀ y ∈ φ.toChart.source, φ.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ.toChart y (X y)) =
      fun i ↦ -(φ.weight i * φ.coord (φ.toChart y) i))
    {ε r₀ : ℝ} {Kk : NNReal} (hε₁ : ∀ z, ‖z‖ ≤ ε → φ.coord.symm z ∈ φ.toChart.target)
    {g : ({i // ¬φ.weight i = 1} → ℝ) → {i // φ.weight i = 1} → ℝ}
    {k : ({i // φ.weight i = 1} → ℝ) → {i // ¬φ.weight i = 1} → ℝ}
    (hgε : ∀ v ∈ Metric.closedBall 0 (r₀ * ε), ‖g v‖ = ε)
    (hk : LipschitzOnWith Kk k (Metric.closedBall 0 (r₀ * ε))) (hk₀ : k 0 = 0)
    (hr₀ε : r₀ * ε ≤ ε) (hKkε : Kk * (r₀ * ε) ≤ ε)
    {z : WithLp 2 (({i // φ.weight i = 1} → ℝ) × ({i // ¬φ.weight i = 1} → ℝ)) ×
      WithLp 2 (({i // φ.weight i = 1} → ℝ) × ({i // ¬φ.weight i = 1} → ℝ))}
    (hz : z ∈ splitCenterBallGluingPairs ε r₀ g k) :
    φ.coord.symm (φ.splitCoord.symm z.1) ∈ φ.toChart.target ∧
      φ.coord.symm (φ.splitCoord.symm z.2) ∈ φ.toChart.target ∧
      (∃ t, hX.flow t (φ.toChart.symm (φ.coord.symm (φ.splitCoord.symm z.1))) =
        φ.toChart.symm (φ.coord.symm (φ.splitCoord.symm z.2))) ∧
      ‖z.2.snd‖ ≤ Kk * (r₀ * ε) := by
  obtain ⟨hz₁, hzg, ⟨T, hT0, hzT⟩, hz₂, hzk⟩ := mem_splitCenterBallGluingPairs.1 hz
  have hgz : ‖z.1.fst‖ = ε := by rw [hzg]; exact hgε _ (mem_closedBall_zero_iff.2 hz₁)
  have hz₂s : ‖z.2.snd‖ ≤ Kk * (r₀ * ε) := by
    have h := hk.norm_sub_le (mem_closedBall_zero_iff.2 hz₂)
      (Metric.mem_closedBall_self ((norm_nonneg _).trans hz₂))
    rw [hk₀, sub_zero, sub_zero, ← hzk] at h
    exact h.trans (by gcongr)
  -- The model orbit from `z.1` to `z.2` stays in the box, so the flow reads it.
  have h := hX.flow_toChart_symm_splitCoord_symm φ hφ hε₁ (t := T) fun s hs ↦
    norm_fst_le_and_norm_snd_le_splitQuadraticFlow hgz.le (by rw [← hzT]; exact hz₂s.trans hKkε)
      (by rwa [uIcc_of_le hT0] at hs)
  rw [← hzT] at h
  exact ⟨MorseChart.coord_symm_splitCoord_symm_mem_target_of_norm_le hε₁ hgz.le (hz₁.trans hr₀ε),
    MorseChart.coord_symm_splitCoord_symm_mem_target_of_norm_le hε₁ (hz₂.trans hr₀ε)
      (hz₂s.trans hKkε), ⟨T, h⟩, hz₂s⟩

/-- **A trajectory near a broken one at the centre gives a gluing pair.** Let `φ` be a Morse chart
at `q` in which `X` is linear, which contains the cube of radius `2 ε`, and on whose cube of
radius `ρ` the plane `u = 0` lies in `W^u(q)`. Let `w₁ ∈ W^u(p)`, with `p ≠ q`, lie near the
entrance face with `‖u‖ ‖v‖ / ε < r₀ ε` and its model entrance point on the graph of `g`, and let
`w₂ = φ_t w₁`, below the level of `p`, lie in the box with `‖u‖ < r₀ ε`, on the graph of `k`. If
`r₀ ≤ 1` and `r₀ ^ 2 n < 1`, the model entrance point of `w₂` and the split coordinates of `w₂`
form a gluing pair at the centre, and `w₁` flows to the point with the coordinates of that entrance
point. -/
private theorem exists_flow_eq_and_mem_splitCenterBallGluingPairs (hX : IsAdaptedPseudoGradient f X)
    (hf : IsMorse 𝓘(ℝ, E) f) {p q : M} (hpq : p ≠ q) (φ : MorseChart E f q)
    (hφ : ∀ y ∈ φ.toChart.source, φ.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ.toChart y (X y)) =
      fun i ↦ -(φ.weight i * φ.coord (φ.toChart y) i))
    {ε ρ r₀ : ℝ} (hε : 0 < ε) (hε₂ : ∀ z, ‖z‖ ≤ 2 * ε → φ.coord.symm z ∈ φ.toChart.target)
    (hloc : ∀ w ∈ φ.toChart.source, ‖φ.coord (φ.toChart w)‖ < ρ →
      (φ.splitCoord (φ.coord (φ.toChart w))).fst = 0 → w ∈ hX.flow.unstableSet q)
    (hr₀ : r₀ ≤ 1) (hn : r₀ ^ 2 * Module.finrank ℝ E < 1)
    {g : ({i // ¬φ.weight i = 1} → ℝ) → {i // φ.weight i = 1} → ℝ}
    {k : ({i // φ.weight i = 1} → ℝ) → {i // ¬φ.weight i = 1} → ℝ}
    {w₁ w₂ : M} (hw₁u : w₁ ∈ hX.flow.unstableSet p) (hw₁s : w₁ ∈ φ.toChart.source)
    (hw₁f0 : 0 < ‖(φ.splitCoord (φ.coord (φ.toChart w₁))).fst‖)
    (hw₁f : ‖(φ.splitCoord (φ.coord (φ.toChart w₁))).fst‖ < 2 * ε)
    (hw₁n : ‖(φ.splitCoord (φ.coord (φ.toChart w₁))).snd‖ < ε)
    (hw₁κ : ‖(φ.splitCoord (φ.coord (φ.toChart w₁))).fst‖ *
      ‖(φ.splitCoord (φ.coord (φ.toChart w₁))).snd‖ / ε < r₀ * ε)
    (hw₁g : (splitQuadraticFlow (splitEntryTime ε (φ.splitCoord (φ.coord (φ.toChart w₁))))
        (φ.splitCoord (φ.coord (φ.toChart w₁)))).fst =
      g (splitQuadraticFlow (splitEntryTime ε (φ.splitCoord (φ.coord (φ.toChart w₁))))
        (φ.splitCoord (φ.coord (φ.toChart w₁)))).snd)
    (hw₂s : w₂ ∈ φ.toChart.source) (hw₂ρ : ‖φ.coord (φ.toChart w₂)‖ < ρ)
    (hw₂f : ‖(φ.splitCoord (φ.coord (φ.toChart w₂))).fst‖ < r₀ * ε)
    (hw₂n : ‖(φ.splitCoord (φ.coord (φ.toChart w₂))).snd‖ < ε)
    (hw₂k : (φ.splitCoord (φ.coord (φ.toChart w₂))).snd =
      k (φ.splitCoord (φ.coord (φ.toChart w₂))).fst)
    (hw₂p : f w₂ < f p) {t : ℝ} (ht : hX.flow t w₁ = w₂) :
    (splitQuadraticFlow (splitEntryTime ε (φ.splitCoord (φ.coord (φ.toChart w₂))))
        (φ.splitCoord (φ.coord (φ.toChart w₂))), φ.splitCoord (φ.coord (φ.toChart w₂))) ∈
      splitCenterBallGluingPairs ε r₀ g k ∧
    hX.flow (splitEntryTime ε (φ.splitCoord (φ.coord (φ.toChart w₂))) + t) w₁ =
      φ.toChart.symm (φ.coord.symm (φ.splitCoord.symm
        (splitQuadraticFlow (splitEntryTime ε (φ.splitCoord (φ.coord (φ.toChart w₂))))
          (φ.splitCoord (φ.coord (φ.toChart w₂)))))) := by
  set Φ : M → WithLp 2 (({i // φ.weight i = 1} → ℝ) × ({i // ¬φ.weight i = 1} → ℝ)) :=
    fun w ↦ φ.splitCoord (φ.coord (φ.toChart w))
  set Ψ : WithLp 2 (({i // φ.weight i = 1} → ℝ) × ({i // ¬φ.weight i = 1} → ℝ)) → M :=
    fun z ↦ φ.toChart.symm (φ.coord.symm (φ.splitCoord.symm z))
  have hε₁ : ∀ z, ‖z‖ ≤ ε → φ.coord.symm z ∈ φ.toChart.target := fun z hz ↦ hε₂ z (by linarith)
  have hr₀ε : r₀ * ε ≤ ε := mul_le_of_le_one_left hε.le hr₀
  have hw2u : w₂ ∈ hX.flow.unstableSet p := ht ▸ (Flow.apply_mem_unstableSet_iff _ _).2 hw₁u
  obtain ⟨b, hpb, hb, -⟩ := exists_mem_unstableSet_inter_stableSet_of_apply_flow_lt hX hf hw₁u
    (t := t) (by rw [ht]; exact hw₂p) le_rfl
  have hanti := hX.strictAnti_flow_of_mem_unstableSet_inter_stableSet hpb hb
  -- Off `W^u(q)`, the point `w₂` has a nonzero contracting coordinate.
  have hξ : (Φ w₂).fst ≠ 0 := fun h0 ↦
    (Flow.disjoint_unstableSet hpq).ne_of_mem hw2u (hloc w₂ hw₂s hw₂ρ h0) rfl
  have hz₁ : (Φ w₁).fst ≠ 0 := norm_pos_iff.1 hw₁f0
  set E₁ := splitQuadraticFlow (splitEntryTime ε (Φ w₁)) (Φ w₁) with hE₁def
  set E₂ := splitQuadraticFlow (splitEntryTime ε (Φ w₂)) (Φ w₂) with hE₂def
  have hE₁ : Ψ E₁ = hX.flow (splitEntryTime ε (Φ w₁)) w₁ :=
    (hX.flow_splitEntryTime_of_norm_lt φ hφ hε hε₂ hw₁s hw₁f hw₁n).symm
  have hE₂ : Ψ E₂ = hX.flow (splitEntryTime ε (Φ w₂)) w₂ :=
    (hX.flow_splitEntryTime_of_norm_lt φ hφ hε hε₂ hw₂s (by linarith) hw₂n).symm
  have hE₁f : ‖E₁.fst‖ = ε := norm_fst_splitQuadraticFlow_splitEntryTime hε hz₁
  have hE₂f : ‖E₂.fst‖ = ε := norm_fst_splitQuadraticFlow_splitEntryTime hε hξ
  have hE₁r : ‖E₁.snd‖ < r₀ * ε := by
    rw [hE₁def, norm_snd_splitQuadraticFlow_splitEntryTime hε hz₁]
    exact hw₁κ
  have hE₂r : ‖E₂.snd‖ < r₀ * ε := by
    rw [hE₂def, norm_snd_splitQuadraticFlow_splitEntryTime hε hξ, div_lt_iff₀ hε]
    calc ‖(Φ w₂).fst‖ * ‖(Φ w₂).snd‖ ≤ ‖(Φ w₂).fst‖ * ε := by gcongr
      _ < r₀ * ε * ε := by gcongr
  have hn' : ∀ v : {i // ¬φ.weight i = 1} → ℝ, ‖v‖ < r₀ * ε →
      Module.finrank ℝ E * ‖v‖ ^ 2 < ε ^ 2 := fun v hv ↦ by
    have hv2 : ‖v‖ ^ 2 ≤ (r₀ * ε) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hv.le 2
    calc (Module.finrank ℝ E : ℝ) * ‖v‖ ^ 2 ≤ Module.finrank ℝ E * (r₀ * ε) ^ 2 := by gcongr
      _ = r₀ ^ 2 * Module.finrank ℝ E * ε ^ 2 := by ring
      _ < 1 * ε ^ 2 := by gcongr
      _ = ε ^ 2 := one_mul _
  -- The two entrance points lie on one orbit, so they are equal.
  have hantiE : StrictAnti fun s ↦ f (hX.flow s (Ψ E₁)) := fun a b hab ↦ by
    simpa only [hE₁, ← Flow.map_add] using
      hanti (by linarith : a + splitEntryTime ε (Φ w₁) < b + splitEntryTime ε (Φ w₁))
  have horb : hX.flow (splitEntryTime ε (Φ w₂) + t - splitEntryTime ε (Φ w₁)) (Ψ E₁) = Ψ E₂ := by
    rw [hE₁, hE₂, ← ht, ← Flow.map_add, ← Flow.map_add]
    congr 1
    ring
  have hEE : E₁ = E₂ := hX.eq_of_flow_eq_of_norm_fst_eq φ hφ hε₁ hE₁f (by linarith) hE₂f
    (by linarith) (hn' _ hE₁r) (hn' _ hE₂r) hantiE horb
  refine ⟨mem_splitCenterBallGluingPairs.2 ⟨hE₂r.le, by rw [← hEE]; exact hw₁g,
    ⟨-splitEntryTime ε (Φ w₂), neg_nonneg.2 (splitEntryTime_nonpos (by linarith)),
      (Flow.map_neg_apply_map _ _ _).symm⟩, hw₂f.le, hw₂k⟩, ?_⟩
  rw [Flow.map_add, ht]
  exact hE₂.symm

/-- **A gluing pair at the centre, between two sets.** Under the hypotheses of
`exists_flow_eq_of_mem_splitCenterBallGluingPairs`, let the points of the chart with split
coordinates `(g v, v)` lie in `A` and those with split coordinates `(u, k u)` lie in `B`, for
`‖u‖, ‖v‖ ≤ r₀ ε`.
The first point of a gluing pair at the centre, read on the manifold, lies in `A` and flows to the
second, which lies in `B`, and the two split coordinates of the second have norms at most `r₀ ε`
and `Kk r₀ ε`. -/
private theorem mem_and_exists_flow_eq_of_mem_splitCenterBallGluingPairs
    (hX : IsAdaptedPseudoGradient f X) {q : M} (φ : MorseChart E f q)
    (hφ : ∀ y ∈ φ.toChart.source, φ.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ.toChart y (X y)) =
      fun i ↦ -(φ.weight i * φ.coord (φ.toChart y) i))
    {ε r₀ : ℝ} {Kk : NNReal} (hε₁ : ∀ z, ‖z‖ ≤ ε → φ.coord.symm z ∈ φ.toChart.target)
    {g : ({i // ¬φ.weight i = 1} → ℝ) → {i // φ.weight i = 1} → ℝ}
    {k : ({i // φ.weight i = 1} → ℝ) → {i // ¬φ.weight i = 1} → ℝ}
    (hgε : ∀ v ∈ Metric.closedBall 0 (r₀ * ε), ‖g v‖ = ε)
    (hk : LipschitzOnWith Kk k (Metric.closedBall 0 (r₀ * ε))) (hk₀ : k 0 = 0)
    (hr₀ε : r₀ * ε ≤ ε) (hKkε : Kk * (r₀ * ε) ≤ ε) {A B : Set M}
    (hgA : ∀ v ∈ Metric.closedBall 0 (r₀ * ε),
      φ.toChart.symm (φ.coord.symm (φ.splitCoord.symm (WithLp.toLp 2 (g v, v)))) ∈ A)
    (hkB : ∀ u ∈ Metric.closedBall 0 (r₀ * ε),
      φ.toChart.symm (φ.coord.symm (φ.splitCoord.symm (WithLp.toLp 2 (u, k u)))) ∈ B)
    {z : WithLp 2 (({i // φ.weight i = 1} → ℝ) × ({i // ¬φ.weight i = 1} → ℝ)) ×
      WithLp 2 (({i // φ.weight i = 1} → ℝ) × ({i // ¬φ.weight i = 1} → ℝ))}
    (hz : z ∈ splitCenterBallGluingPairs ε r₀ g k) :
    φ.coord.symm (φ.splitCoord.symm z.1) ∈ φ.toChart.target ∧
      φ.coord.symm (φ.splitCoord.symm z.2) ∈ φ.toChart.target ∧
      φ.toChart.symm (φ.coord.symm (φ.splitCoord.symm z.1)) ∈ A ∧
      φ.toChart.symm (φ.coord.symm (φ.splitCoord.symm z.2)) ∈ B ∧
      (∃ t, hX.flow t (φ.toChart.symm (φ.coord.symm (φ.splitCoord.symm z.1))) =
        φ.toChart.symm (φ.coord.symm (φ.splitCoord.symm z.2))) ∧
      ‖z.2.fst‖ ≤ r₀ * ε ∧ ‖z.2.snd‖ ≤ Kk * (r₀ * ε) := by
  obtain ⟨hz₁, hzg, -, hz₂, hzk⟩ := mem_splitCenterBallGluingPairs.1 hz
  obtain ⟨hz₁t, hz₂t, ht, hz₂s⟩ :=
    hX.exists_flow_eq_of_mem_splitCenterBallGluingPairs φ hφ hε₁ hgε hk hk₀ hr₀ε hKkε hz
  -- The two points lie on the graphs of `g` and of `k`.
  have hz1 : z.1 = WithLp.toLp 2 (g z.1.snd, z.1.snd) :=
    WithLp.ofLp_injective 2 (Prod.ext (by simpa using hzg) (by simp))
  have hz2 : z.2 = WithLp.toLp 2 (z.2.fst, k z.2.fst) :=
    WithLp.ofLp_injective 2 (Prod.ext (by simp) (by simpa using hzk))
  refine ⟨hz₁t, hz₂t, ?_, ?_, ht, hz₂, hz₂s⟩
  · rw [hz1]
    exact hgA _ (mem_closedBall_zero_iff.2 hz₁)
  · rw [hz2]
    exact hkB _ (mem_closedBall_zero_iff.2 hz₂)

/-- **Trajectories near a broken one at the centre give gluing pairs.** Let `φ` be a Morse chart
at `q` in which `X` is linear, which contains the cube of radius `2 ε`, and on whose cube of
radius `ρ` the plane `u = 0` lies in `W^u(q)`, and let `p ≠ q` with `f q < f p`. Suppose that near
`y₁` the points of the chart satisfy `0 < ‖u‖ < 2 ε` and `‖v‖ < ε`, that `‖u‖ ‖v‖` tends to `0`
at `y₁`, that the model entrance points of the points of `W^u(p)` on the level of `y₁` near `y₁`
lie on the graph of `g`, and that near `q` the points of `Z` lie on the graph of `k`. If
`0 < r₀ ≤ 1` and `r₀ ^ 2 n < 1`, then for every pair `(w₁, w₂)` near `(y₁, q)` of a point
`w₁ ∈ W^u(p)` on the level of `y₁` and a point `w₂ ∈ Z` of its orbit, the model entrance point of
`w₂` and the split coordinates of `w₂` form a gluing pair at the centre with `‖u‖ < r₀ ε`, and
`w₁` flows to the point with the coordinates of that entrance point. -/
private theorem eventually_mem_splitCenterBallGluingPairs (hX : IsAdaptedPseudoGradient f X)
    (hf : IsMorse 𝓘(ℝ, E) f) {p q y₁ : M} (hpq : p ≠ q) (hqp : f q < f p) (φ : MorseChart E f q)
    (hφ : ∀ y ∈ φ.toChart.source, φ.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ.toChart y (X y)) =
      fun i ↦ -(φ.weight i * φ.coord (φ.toChart y) i))
    {ε ρ r₀ : ℝ} (hε : 0 < ε) (hε₂ : ∀ z, ‖z‖ ≤ 2 * ε → φ.coord.symm z ∈ φ.toChart.target)
    (hρ : 0 < ρ) (hloc : ∀ w ∈ φ.toChart.source, ‖φ.coord (φ.toChart w)‖ < ρ →
      (φ.splitCoord (φ.coord (φ.toChart w))).fst = 0 → w ∈ hX.flow.unstableSet q)
    (hr₀ : 0 < r₀) (hr₀₁ : r₀ ≤ 1) (hn : r₀ ^ 2 * Module.finrank ℝ E < 1)
    {g : ({i // ¬φ.weight i = 1} → ℝ) → {i // φ.weight i = 1} → ℝ}
    {k : ({i // φ.weight i = 1} → ℝ) → {i // ¬φ.weight i = 1} → ℝ} {Z : Set M}
    (hnear₁ : ∀ᶠ w in 𝓝 y₁, w ∈ φ.toChart.source ∧
      0 < ‖(φ.splitCoord (φ.coord (φ.toChart w))).fst‖ ∧
      ‖(φ.splitCoord (φ.coord (φ.toChart w))).fst‖ < 2 * ε ∧
      ‖(φ.splitCoord (φ.coord (φ.toChart w))).snd‖ < ε)
    (hκ₁ : Tendsto (fun w ↦ ‖(φ.splitCoord (φ.coord (φ.toChart w))).fst‖ *
      ‖(φ.splitCoord (φ.coord (φ.toChart w))).snd‖) (𝓝 y₁) (𝓝 0))
    (hgraph : ∀ᶠ w in 𝓝 y₁, w ∈ hX.flow.unstableSet p → f w = f y₁ →
      (splitQuadraticFlow (splitEntryTime ε (φ.splitCoord (φ.coord (φ.toChart w))))
        (φ.splitCoord (φ.coord (φ.toChart w)))).fst =
      g (splitQuadraticFlow (splitEntryTime ε (φ.splitCoord (φ.coord (φ.toChart w))))
        (φ.splitCoord (φ.coord (φ.toChart w)))).snd)
    (hkexh : ∀ᶠ w in 𝓝 q, w ∈ Z → (φ.splitCoord (φ.coord (φ.toChart w))).snd =
      k (φ.splitCoord (φ.coord (φ.toChart w))).fst) :
    ∀ᶠ w : M × M in 𝓝 (y₁, q), w.1 ∈ hX.flow.unstableSet p → f w.1 = f y₁ → w.2 ∈ Z →
      (∃ t, hX.flow t w.1 = w.2) →
      (splitQuadraticFlow (splitEntryTime ε (φ.splitCoord (φ.coord (φ.toChart w.2))))
          (φ.splitCoord (φ.coord (φ.toChart w.2))), φ.splitCoord (φ.coord (φ.toChart w.2))) ∈
        splitCenterBallGluingPairs ε r₀ g k ∧
      ‖(φ.splitCoord (φ.coord (φ.toChart w.2))).fst‖ < r₀ * ε ∧
      (∃ τ, hX.flow τ w.1 = φ.toChart.symm (φ.coord.symm (φ.splitCoord.symm
        (splitQuadraticFlow (splitEntryTime ε (φ.splitCoord (φ.coord (φ.toChart w.2))))
          (φ.splitCoord (φ.coord (φ.toChart w.2))))))) ∧
      φ.toChart.symm (φ.coord.symm (φ.splitCoord.symm
        (φ.splitCoord (φ.coord (φ.toChart w.2))))) = w.2 := by
  set Φ : M → WithLp 2 (({i // φ.weight i = 1} → ℝ) × ({i // ¬φ.weight i = 1} → ℝ)) :=
    fun w ↦ φ.splitCoord (φ.coord (φ.toChart w))
  -- Near `q` the points of the chart lie in the small box around the centre, below `f p`.
  have hΦ₂ : Tendsto Φ (𝓝 q) (𝓝 0) := by
    have h := (φ.continuousAt_splitCoord_coord_toChart φ.mem_source).tendsto
    rwa [show φ.splitCoord (φ.coord (φ.toChart q)) = 0 by simp [φ.apply_self]] at h
  have hfst₂ : Tendsto (fun w ↦ ‖(Φ w).fst‖) (𝓝 q) (𝓝 0) := by
    simpa [Function.comp_def] using ((WithLp.continuous_fst 2 _ _).tendsto 0).norm.comp hΦ₂
  have hsnd₂ : Tendsto (fun w ↦ ‖(Φ w).snd‖) (𝓝 q) (𝓝 0) := by
    simpa [Function.comp_def] using ((WithLp.continuous_snd 2 _ _).tendsto 0).norm.comp hΦ₂
  have hnear₂ : ∀ᶠ w in 𝓝 q, (w ∈ φ.toChart.source ∧ ‖φ.coord (φ.toChart w)‖ < ρ) ∧
      ‖(Φ w).fst‖ < r₀ * ε ∧ ‖(Φ w).snd‖ < ε ∧ f w < f p :=
    (φ.eventually_mem_source_norm_coord_lt hρ).and
      ((hfst₂.eventually (gt_mem_nhds (mul_pos hr₀ hε))).and
        ((hsnd₂.eventually (gt_mem_nhds hε)).and
          (hX.mdifferentiable.continuous.continuousAt.eventually (gt_mem_nhds hqp))))
  filter_upwards [((hnear₁.and ((hκ₁.div_const ε).eventually
    (gt_mem_nhds (by simpa using mul_pos hr₀ hε)))).and hgraph).prod_nhds (hnear₂.and hkexh)]
    with w hw hw1u hw1f hw2Z hwt
  obtain ⟨⟨⟨⟨hw₁s, hw₁f0, hw₁f, hw₁n⟩, hκw⟩, hw₁g⟩, ⟨⟨hw₂s, hw₂ρ⟩, hw₂f, hw₂n, hw₂p⟩, hw₂k⟩ := hw
  obtain ⟨t, ht⟩ := hwt
  obtain ⟨hP, hflow⟩ := hX.exists_flow_eq_and_mem_splitCenterBallGluingPairs hf hpq φ hφ hε hε₂ hloc
    hr₀₁ hn hw1u hw₁s hw₁f0 hw₁f hw₁n hκw (hw₁g hw1u hw1f) hw₂s hw₂ρ hw₂f hw₂n (hw₂k hw2Z) hw₂p ht
  exact ⟨hP, hw₂f, ⟨_, hflow⟩, by simp [φ.toChart.left_inv hw₂s]⟩

/-- **The model gluing arc into a transverse set through the critical point, on the manifold.**
For a trajectory from `p` through `a₁` to `q`, with `ind p = ind q + 1`, and a set `Z` through `q`
of dimension `n - ind q`, flattened near `q` and transverse to `W^u(q)` at `q`, there are a point
`flow T₁ a₁`, a level `c` above `f q` and below `f a₁` and `f (flow T₁ a₁)`, and a continuous arc
`B` in `M × M` starting at `(flow T₁ a₁, q)`, along which, for `s ≠ 0`, `(B s).1` lies in `W^u(p)`
and flows to the point `(B s).2` of `Z`, below the level `c`, different `s` giving different
second points. Every pair of such points near the start, the first on the level of
`flow T₁ a₁`, is reached by the arc below its end. -/
private theorem IsMorseSmale.exists_centerGluingArc {hX : IsAdaptedPseudoGradient f X}
    (h : hX.IsMorseSmale) (hf : IsMorse 𝓘(ℝ, E) f) {p q a₁ : M} {Z : Set M}
    (hpq : manifoldMorseIndex 𝓘(ℝ, E) f p = manifoldMorseIndex 𝓘(ℝ, E) f q + 1)
    (ha₁ : a₁ ∈ hX.flow.unstableSet p ∩ hX.flow.stableSet q) {L : Submodule ℝ E}
    {φZ : OpenPartialHomeomorph M E} (hφZ : φZ ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M)
    (hZ : IsSliceChart φZ (L : Set E) Z) (hqφZ : q ∈ φZ.source) (hqZ : q ∈ Z)
    (hdim : Module.finrank ℝ L + manifoldMorseIndex 𝓘(ℝ, E) f q = Module.finrank ℝ E)
    (htr : Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) Z q) ⊔
      Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX.flow.unstableSet q) q) = ⊤) :
    ∃ (c T₁ δ : ℝ) (hδ : 0 < δ) (B : Icc (0 : ℝ) δ → M × M),
      c < f a₁ ∧ c < f (hX.flow T₁ a₁) ∧ f q < c ∧ Continuous B ∧
      B ⟨0, left_mem_Icc.2 hδ.le⟩ = (hX.flow T₁ a₁, q) ∧
      (∀ s : Icc (0 : ℝ) δ, (s : ℝ) ≠ 0 → (B s).1 ∈ hX.flow.unstableSet p ∧
        (B s).2 ∈ Z ∧ ∃ t, hX.flow t (B s).1 = (B s).2) ∧
      (∀ s, f (B s).2 < c) ∧ Injective (fun s ↦ (B s).2) ∧
      ∀ᶠ w : M × M in 𝓝 (hX.flow T₁ a₁, q),
        w.1 ∈ hX.flow.unstableSet p → f w.1 = f (hX.flow T₁ a₁) → w.2 ∈ Z →
        (∃ t, hX.flow t w.1 = w.2) →
        ∃ s : Icc (0 : ℝ) δ, (s : ℝ) < δ ∧ (∃ t, hX.flow t w.1 = (B s).1) ∧ w.2 = (B s).2 := by
  -- Plan: choose a Morse box at `q` with entrance point `y₁` on the trajectory through `a₁`. Glue
  -- the trace of `W^u(p)` on the entrance face to the graph of `Z` through the centre with the
  -- model `TauCeti.exists_homeomorph_closure_splitCenterBallGluingPairs`, and read the arc on `M`.
  have hpq' : p ≠ q := by rintro rfl; omega
  have hq := hX.mfderiv_eq_zero_of_mem_stableSet ha₁.2
  have hfa₁ := hX.mem_Ioo_of_mem_unstableSet_inter_stableSet hpq' ha₁
  obtain ⟨φ, ρ, hφ, hρ, hT, hloc⟩ := hX.exists_morseChart_box hf hq
  set Φ : M → WithLp 2 (({i // φ.weight i = 1} → ℝ) × ({i // ¬φ.weight i = 1} → ℝ)) :=
    fun w ↦ φ.splitCoord (φ.coord (φ.toChart w)) with hΦdef
  set Ψ : WithLp 2 (({i // φ.weight i = 1} → ℝ) × ({i // ¬φ.weight i = 1} → ℝ)) → M :=
    fun z ↦ φ.toChart.symm (φ.coord.symm (φ.splitCoord.symm z)) with hΨdef
  have hΨΦ : ∀ w ∈ φ.toChart.source, Ψ (Φ w) = w := fun w hw ↦ by
    simp only [hΨdef, hΦdef, LinearEquiv.symm_apply_apply, φ.toChart.left_inv hw]
  have hΦq : Φ q = 0 := by simp [hΦdef, φ.apply_self]
  -- `Z` near the centre, as a graph.
  obtain ⟨η, hη, Kk, k, hk, hk₀, hkZ, hkexh⟩ := hX.exists_lipschitzOnWith_graph_of_isSliceChart hq
    φ hρ (fun w hw hwρ ↦ (hloc w hw hwρ).2) hφZ hZ hqφZ hqZ hdim htr
  -- A box whose entrance face meets the trajectory through `a₁` at `y₁`.
  have hsmall : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε ∧ 2 * ε < ρ := by
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (gt_mem_nhds (half_pos hρ))]
      with ε hε hερ
    exact ⟨hε, by linarith⟩
  obtain ⟨ε, ⟨T₁, hy₁φ, hy₁s, hy₁f⟩, hε, hερ⟩ :=
    ((hX.eventually_exists_flow_mem_entranceFace φ hφ hρ (fun w hw hwρ ↦ (hloc w hw hwρ).1) hpq'
      ha₁).and hsmall).exists
  set y₁ := hX.flow T₁ a₁
  have hε₂ : ∀ z, ‖z‖ ≤ 2 * ε → φ.coord.symm z ∈ φ.toChart.target := fun z hz ↦ hT z (by linarith)
  have hε₁ : ∀ z, ‖z‖ ≤ ε → φ.coord.symm z ∈ φ.toChart.target := fun z hz ↦ hε₂ z (by linarith)
  have hy₁ : y₁ ∈ hX.flow.unstableSet p ∩ hX.flow.stableSet q :=
    hX.flow.isInvariant_unstableSet_inter_stableSet p q T₁ ha₁
  have hfy₁ := hX.mem_Ioo_of_mem_unstableSet_inter_stableSet hpq' hy₁
  -- The level `c` between `f q` and both `f a₁` and `f y₁`.
  set c := (f q + min (f a₁) (f y₁)) / 2 with hcdef
  have hmin := lt_min hfa₁.1 hfy₁.1
  have hca₁ : c < f a₁ := by have := min_le_left (f a₁) (f y₁); linarith
  have hcy₁ : c < f y₁ := by have := min_le_right (f a₁) (f y₁); linarith
  have hqc : f q < c := by linarith
  -- Near `y₁` the box coordinates are those of the entrance face.
  obtain ⟨hnear₁, hκ₁⟩ := hX.eventually_of_morseBox_entranceFace φ hε hερ
    (fun w hw hwρ ↦ (hloc w hw hwρ).1) hy₁φ hy₁s hy₁f
  -- The trace of `W^u(p)` on the entrance face, near `y₁`.
  obtain ⟨F₁, ι₁, ψ', hι₁0, hι₁, hι₁s, hψ, hψ', hexh₁⟩ :=
    h.exists_unstableSet_level_param hf hpq φ hy₁ hy₁φ (hnear₁.mono fun w hw ↦ hw.2.2.2.2.1)
  have hψ₀ : Φ (ι₁ 0) = WithLp.toLp 2 ((Φ y₁).fst, 0) := by
    rw [hι₁0]
    exact WithLp.ofLp_injective 2 (Prod.ext (by simp) (by simpa using hy₁s))
  set U₁ : Set F₁ := {z | (ι₁ z ∈ φ.toChart.source ∧ 0 < ‖(Φ (ι₁ z)).fst‖ ∧
    ‖(Φ (ι₁ z)).fst‖ < 2 * ε ∧ ‖(Φ (ι₁ z)).snd‖ < ε ∧
    (ι₁ z ∈ hX.flow.stableSet q ↔ (Φ (ι₁ z)).snd = 0)) ∧ ι₁ z ∈ hX.flow.unstableSet p}
  have hU₁ : U₁ ∈ 𝓝 0 := by
    have h₁ := hι₁.tendsto.eventually (p := fun w ↦ w ∈ φ.toChart.source ∧
      0 < ‖(Φ w).fst‖ ∧ ‖(Φ w).fst‖ < 2 * ε ∧ ‖(Φ w).snd‖ < ε ∧
      (w ∈ hX.flow.stableSet q ↔ (Φ w).snd = 0)) (by rw [hι₁0]; exact hnear₁)
    filter_upwards [h₁, hι₁s] with z hz hz' using ⟨hz, hz'.1⟩
  obtain ⟨δg, hδg, Kg, g, hg, hg₀, hgpts, hgexh⟩ :=
    exists_splitQuadraticFlow_splitEntryTime_eq_graph hψ hψ' hψ₀ hy₁f hε hU₁
  -- Points of the graph of `g` lie in `W^u(p)`.
  have hgu : ∀ v ∈ Metric.closedBall 0 δg,
      Ψ (WithLp.toLp 2 (g v, v)) ∈ hX.flow.unstableSet p := by
    intro v hv
    obtain ⟨-, z, ⟨⟨hzs, -, hzf, hzn, -⟩, hzu⟩, hz⟩ := hgpts v hv
    have h : Ψ (WithLp.toLp 2 (g v, v)) =
        hX.flow (splitEntryTime ε (Φ (ι₁ z))) (ι₁ z) := by
      rw [← hz]
      exact (hX.flow_splitEntryTime_of_norm_lt φ hφ hε hε₂ hzs hzf hzn).symm
    rw [h]
    exact (Flow.apply_mem_unstableSet_iff _ _).2 hzu
  -- Near the centre, the points of the box lie below the level `c`.
  obtain ⟨ρc, hρc, hlowc⟩ :=
    φ.exists_pos_forall_norm_lt_apply_lt hX.mdifferentiable.continuous.continuousAt hqc
  -- Choose the gluing radius `r₀`.
  have hev (a b : ℝ) (hb : 0 < b) : ∀ᶠ r in 𝓝 (0 : ℝ), r * a < b :=
    ((continuous_id.mul continuous_const).tendsto' 0 0 (by simp)).eventually (gt_mem_nhds hb)
  have hev₂ (a : ℝ) : ∀ᶠ r in 𝓝 (0 : ℝ), r ^ 2 * a < 1 :=
    (((continuous_pow 2).mul continuous_const).tendsto' 0 0 (by simp)).eventually
      (gt_mem_nhds one_pos)
  have hall : ∀ᶠ r in 𝓝[>] (0 : ℝ), 0 < r ∧ r * 1 < 1 ∧ r * ε < δg ∧ r * ε < η ∧ r * Kk < 1 ∧
      r ^ 2 * (Kk * Kg) < 1 ∧ r ^ 2 * Module.finrank ℝ E < 1 ∧ r * ε < ρc ∧
      r * (Kk * ε) < ρc :=
    (show ∀ᶠ r in 𝓝[>] (0 : ℝ), 0 < r from self_mem_nhdsWithin).and
      (nhdsWithin_le_nhds ((hev 1 1 one_pos).and ((hev ε δg hδg).and ((hev ε η hη).and
        ((hev Kk 1 one_pos).and ((hev₂ (Kk * Kg)).and ((hev₂ (Module.finrank ℝ E)).and
          ((hev ε ρc hρc).and (hev (Kk * ε) ρc hρc)))))))))
  obtain ⟨r₀, hr₀, hr₀₁, hr₀g, hr₀k, hKk, hK, hn, hρ₁, hρ₂⟩ := hall.exists
  rw [mul_one] at hr₀₁
  have hr₀ε : r₀ * ε ≤ ε := mul_le_of_le_one_left hε.le hr₀₁.le
  have hKkε : Kk * (r₀ * ε) ≤ ε := by nlinarith [Kk.coe_nonneg]
  have hg' : LipschitzOnWith Kg g (Metric.closedBall 0 (r₀ * ε)) :=
    hg.mono (Metric.closedBall_subset_closedBall hr₀g.le)
  have hgε' : ∀ v ∈ Metric.closedBall (0 : {i // ¬φ.weight i = 1} → ℝ) (r₀ * ε), ‖g v‖ = ε :=
    fun v hv ↦ (hgpts v (Metric.closedBall_subset_closedBall hr₀g.le hv)).1
  have hk' : LipschitzOnWith Kk k (Metric.closedBall 0 (r₀ * ε)) :=
    hk.mono (Metric.closedBall_subset_closedBall hr₀k.le)
  obtain ⟨e, he, he₀⟩ := exists_homeomorph_closure_splitCenterBallGluingPairs hg' hgε' hk' hk₀ hε
    hr₀ hr₀₁.le (by rw [mul_comm]; exact hKk.le) (by rw [mul_comm]; exact hK)
  have hcl := closure_splitCenterBallGluingPairs hg' hgε' hk' hk₀ hε hr₀ hr₀₁.le
    (by rw [mul_comm]; exact hKk.le) (by rw [mul_comm]; exact hK)
  have hbr : ((WithLp.toLp 2 (g 0, 0), 0) : WithLp 2 (({i // φ.weight i = 1} → ℝ) ×
      ({i // ¬φ.weight i = 1} → ℝ)) × _) = (Φ y₁, Φ q) := by
    rw [hg₀, hΦq, ← hψ₀, hι₁0]
  rw [hbr] at he₀ hcl
  -- The pairs, read on `M`.
  have hpair (z) (hz : z ∈ splitCenterBallGluingPairs ε r₀ g k) :=
    hX.mem_and_exists_flow_eq_of_mem_splitCenterBallGluingPairs φ hφ hε₁ hgε' hk' hk₀ hr₀ε hKkε
      (A := hX.flow.unstableSet p) (B := Z)
      (fun v hv ↦ hgu v (Metric.closedBall_subset_closedBall hr₀g.le hv))
      (fun u hu ↦ (hkZ u (Metric.closedBall_subset_closedBall hr₀k.le hu)).2) hz
  -- The arc: the two points of the gluing pair at each gluing parameter, read on `M`.
  have hmem : ∀ s : Icc (0 : ℝ) r₀, (s : ℝ) ≠ 0 → (e s).val ∈ splitCenterBallGluingPairs ε r₀ g k :=
    fun s hs ↦ e.injective.val_mem_of_subset_insert hcl.subset he₀ fun h ↦
      hs (congrArg Subtype.val h)
  have htgt : ∀ s : Icc (0 : ℝ) r₀,
      φ.coord.symm (φ.splitCoord.symm (e s).val.1) ∈ φ.toChart.target ∧
      φ.coord.symm (φ.splitCoord.symm (e s).val.2) ∈ φ.toChart.target := by
    intro s
    by_cases hs : (s : ℝ) = 0
    · obtain rfl : s = ⟨0, left_mem_Icc.2 hr₀.le⟩ := Subtype.ext hs
      rw [he₀]
      exact ⟨by simpa [hΦdef] using φ.toChart.map_source hy₁φ,
        by simpa [hΦdef] using φ.toChart.map_source φ.mem_source⟩
    · exact ⟨(hpair _ (hmem s hs)).1, (hpair _ (hmem s hs)).2.1⟩
  set B : Icc (0 : ℝ) r₀ → M × M := fun s ↦ (Ψ (e s).val.1, Ψ (e s).val.2) with hBdef
  have hBc : Continuous B := by
    refine continuous_iff_continuousAt.2 fun s ↦ ?_
    have hc : Continuous fun s ↦ (e s).val := continuous_subtypeVal.comp e.continuous
    exact (ContinuousAt.comp (f := fun s ↦ (e s).val.1)
      (φ.continuousAt_toChart_symm_coord_symm_splitCoord_symm (htgt s).1)
      (continuous_fst.comp hc).continuousAt).prodMk
      (ContinuousAt.comp (f := fun s ↦ (e s).val.2)
        (φ.continuousAt_toChart_symm_coord_symm_splitCoord_symm (htgt s).2)
        (continuous_snd.comp hc).continuousAt)
  have hB₀ : B ⟨0, left_mem_Icc.2 hr₀.le⟩ = (y₁, q) := by
    simp only [hBdef, he₀, hΨΦ y₁ hy₁φ, hΨΦ q φ.mem_source]
  have hcoord : ∀ s : Icc (0 : ℝ) r₀, (s : ℝ) = ‖(e s).val.2.fst‖ / ε := fun s ↦ by
    have := he (e s)
    rwa [e.symm_apply_apply] at this
  refine ⟨c, T₁, r₀, hr₀, B, hca₁, hcy₁, hqc, hBc, hB₀, fun s hs ↦ ?_, fun s ↦ ?_,
    fun s s' hss' ↦ ?_, ?_⟩
  · obtain ⟨-, -, hu, hZ', ht, -⟩ := hpair _ (hmem s hs)
    exact ⟨hu, hZ', ht⟩
  · by_cases hs : (s : ℝ) = 0
    · obtain rfl : s = ⟨0, left_mem_Icc.2 hr₀.le⟩ := Subtype.ext hs
      rw [hB₀]
      exact hqc
    · obtain ⟨-, -, -, -, -, hfst, hsnd⟩ := hpair _ (hmem s hs)
      exact hlowc _ (hfst.trans_lt hρ₁) (hsnd.trans_lt (by rw [mul_left_comm]; exact hρ₂))
  · -- Distinct parameters give distinct second points, since the parameter is `‖u‖ / ε`.
    have h2 : (e s).val.2 = (e s').val.2 :=
      φ.injOn_toChart_symm_coord_symm_splitCoord_symm (htgt s).2 (htgt s').2 hss'
    exact Subtype.ext (by rw [hcoord s, hcoord s', h2])
  · -- A trajectory from `p` near the broken one enters the box once, through the graph of `g`, and
    -- meets `Z` near `q` on the graph of `k`: its entrance point and that point form a gluing
    -- pair at the centre, of small parameter.
    have hgraph : ∀ᶠ w in 𝓝 y₁, w ∈ hX.flow.unstableSet p → f w = f y₁ →
        (splitQuadraticFlow (splitEntryTime ε (Φ w)) (Φ w)).fst =
          g (splitQuadraticFlow (splitEntryTime ε (Φ w)) (Φ w)).snd := by
      filter_upwards [hexh₁ _ hgexh] with w hw hwu hwf
      obtain ⟨z, hzg, rfl⟩ := hw hwu hwf
      exact hzg
    filter_upwards [hX.eventually_mem_splitCenterBallGluingPairs hf hpq' (by linarith [hfa₁.2]) φ hφ
      hε hε₂ hρ (fun w hw hwρ ↦ (hloc w hw hwρ).2.2) hr₀ hr₀₁.le hn
      (hnear₁.mono fun w hw ↦ ⟨hw.1, hw.2.1, hw.2.2.1, hw.2.2.2.1⟩) hκ₁ hgraph hkexh]
      with w hw hw1u hw1f hw2Z hwt
    obtain ⟨hP, hw₂f, ⟨τ, hτ⟩, hw₂⟩ := hw hw1u hw1f hw2Z hwt
    set s₀ := e.symm ⟨(_, Φ w.2), subset_closure hP⟩ with hs₀def
    have hBs₀ : B s₀ = (Ψ (splitQuadraticFlow (splitEntryTime ε (Φ w.2)) (Φ w.2)), Ψ (Φ w.2)) := by
      simp only [hBdef, hs₀def, e.apply_symm_apply, hΦdef]
    have hs₀ : (s₀ : ℝ) < r₀ := by
      rw [hs₀def, he, div_lt_iff₀ hε]
      exact hw₂f
    refine ⟨s₀, hs₀, ⟨τ, ?_⟩, ?_⟩
    · rw [hBs₀]
      exact hτ
    · rw [hBs₀]
      exact hw₂.symm

/-- **Gluing a broken trajectory into a transverse set.** Let `X` be a Morse–Smale adapted
pseudo-gradient for a Morse function `f` on a compact manifold of dimension `n`, `a₁` a point of a
trajectory from `p` to a critical point `q` with `ind p = ind q + 1`, and `y` a point of the
unstable manifold `W^u(q)`, possibly `q` itself. Let `Z` be a set through `y` of dimension
`n - ind q`, flattened near `y` by a chart of the maximal atlas and transverse to `W^u(q)` at `y`,
so that `W^u(p) ∩ Z` is expected to be one-dimensional. Record a point `x` of `W^u(p) ∩ Z` by the
pair `(w, x)` of the point `w` of its orbit on the level of `a₁` and `x` itself, and the broken
configuration by `(a₁, y)`. Then `(a₁, y)` has a neighbourhood `N` among these pairs homeomorphic
to a half-open interval `[0, δ)`, with `(a₁, y)` corresponding to `0`.

So the broken configuration is an endpoint of the compactified space of the points of
`W^u(p) ∩ Z` whose orbits follow the trajectory through `a₁`. For `y = q` the points of the arc
are points of `W^u(p) ∩ Z` converging to the critical point `q` itself. -/
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
  have hpq' : p ≠ q := by rintro rfl; omega
  have hfa₁ := hX.mem_Ioo_of_mem_unstableSet_inter_stableSet hpq' ha₁
  rcases eq_or_ne y q with rfl | hyq
  · -- At the critical point itself, glue into `Z` through the centre of a Morse box.
    obtain ⟨c, T₁, δ, hδ, B, hca₁, hcT₁, hqc, hBc, hB₀, hBS, hBc', hBinj, hBfwd⟩ :=
      h.exists_centerGluingArc hf hpq ha₁ hφZ hZ hyφZ hyZ hdim htr
    exact exists_homeomorph_Ico_of_gluingArc hf hpq' ha₁ (T₂ := 0) hδ hca₁ hcT₁ hqc hBc
      (by rw [hB₀, Flow.map_zero_apply])
      (by simpa only [neg_zero, Flow.map_zero_apply] using hBS) hBc' hBinj
      (by simpa only [neg_zero, Flow.map_zero_apply] using hBfwd)
  -- Off the critical point, glue through the exit face, below the level `f q`.
  obtain ⟨T₁, T₂, δ, hδ, B, hBc, hB₀, hBS, hBq, hBinj, hBfwd⟩ :=
    h.exists_transverseGluingArc hf hpq ha₁ hy hyq hφZ hZ hyφZ hyZ hdim htr
  have hfy₁ := hX.mem_Ioo_of_mem_unstableSet_inter_stableSet hpq'
    (hX.flow.isInvariant_unstableSet_inter_stableSet p q T₁ ha₁)
  have hfyq : f y < f q := by
    obtain ⟨r, -, hyr⟩ := hX.exists_tendsto_atTop hf y
    have hqr : q ≠ r := by
      rintro rfl
      exact hyq (hX.eq_of_mem_unstableSet_inter_stableSet ⟨hy, Flow.mem_stableSet.2 hyr⟩)
    exact (hX.mem_Ioo_of_mem_unstableSet_inter_stableSet hqr ⟨hy, Flow.mem_stableSet.2 hyr⟩).2
  -- The second points of the arc are distinct: away from `0` they lie in `W^u(p)` on distinct
  -- orbits, and at `0` in `W^u(q)`.
  have hB2 : ∀ s : Icc (0 : ℝ) δ, (s : ℝ) ≠ 0 → (B s).2 ∈ hX.flow.unstableSet p := fun s hs ↦ by
    obtain ⟨hs₁, -, t, ht⟩ := hBS s hs
    rw [← ht]
    exact (Flow.apply_mem_unstableSet_iff _ _).2 hs₁
  have hB02 : (B ⟨0, left_mem_Icc.2 hδ.le⟩).2 ∈ hX.flow.unstableSet q := by
    rw [hB₀]
    exact (Flow.apply_mem_unstableSet_iff _ _).2 hy
  have hBinj' : Injective fun s ↦ (B s).2 := by
    intro s s' hss'
    simp only at hss'
    by_cases hs : (s : ℝ) = 0 <;> by_cases hs' : (s' : ℝ) = 0
    · exact Subtype.ext (hs.trans hs'.symm)
    · obtain rfl : s = ⟨0, left_mem_Icc.2 hδ.le⟩ := Subtype.ext hs
      exact absurd hss'.symm ((Flow.disjoint_unstableSet hpq').ne_of_mem (hB2 s' hs') hB02)
    · obtain rfl : s' = ⟨0, left_mem_Icc.2 hδ.le⟩ := Subtype.ext hs'
      exact absurd hss' ((Flow.disjoint_unstableSet hpq').ne_of_mem (hB2 s hs) hB02)
    · obtain ⟨-, -, t, ht⟩ := hBS s hs
      obtain ⟨-, -, t', ht'⟩ := hBS s' hs'
      exact hBinj s s' hs hs' (-t' + t) (by
        rw [Flow.map_add, ht, hss', ← ht', Flow.map_neg_apply_map])
  exact exists_homeomorph_Ico_of_gluingArc hf hpq' ha₁ hδ hfa₁.1 hfy₁.1 hfyq hBc hB₀ hBS
    hBq hBinj' hBfwd

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
    h.exists_homeomorph_Ico_of_isSliceChart hf hpq ha₁ ha₂.1 hφZ hZ ha₂φZ ⟨ha₂.2, rfl⟩ hdim
      htr
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
