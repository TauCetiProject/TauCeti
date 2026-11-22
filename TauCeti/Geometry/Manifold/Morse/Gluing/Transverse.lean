/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Gluing.Broken
import TauCeti.Dynamics.Flow.Lyapunov
import TauCeti.Geometry.Manifold.Flow.HittingTime

/-!
# Half-open gluing charts into a transverse set

Let `f` be a Morse function on a compact boundaryless manifold `M` of dimension `n`, `X` a
pseudo-gradient adapted to `f` satisfying the Morse–Smale condition, `a₁` a point of a trajectory
from a critical point `p` to a critical point `q` with `ind p = ind q + 1`, and `y ≠ q` a point of
the unstable manifold `W^u(q)`. Let `Z` be a set of dimension `n - ind q` through `y`, flattened
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
  `TauCeti.Geometry.Manifold.Morse.Gluing.Pair`).

The proof glues in a Morse box at `q` (`TauCeti.IsAdaptedPseudoGradient.exists_morseBox_of_broken`)
with entrance point `y₁` on the trajectory through `a₁` and exit point `y₂` on the orbit of `y`.
The level cut of `W^u(p)` through `y₁` and the set `Z' = flow (-T) ⁻¹' Z` through `y₂` are
transverse discs (`IsMorseSmale.exists_unstableSet_level_param` and
`TauCeti.exists_param_of_span_mtangentConeAt_sup_eq_top`), and the model gluing
(`TauCeti.exists_homeomorph_closure_splitGluingPairs_of_hasStrictFDerivAt`) joins them by a
half-open arc of entrance and exit points. Unlike a stable manifold, `Z'` is not invariant under the
flow, so the point of `Z'` on an orbit must be recovered from its exit point. Since `Z'` is
transverse to `W^u(q)` and of complementary dimension, the velocity `X y₂` is not tangent to it,
so near a regular point an orbit meets `Z'` at most once
(`TauCeti.IsAdaptedPseudoGradient.eventually_eq_zero_of_flow_eq_of_isSliceChart`, from the local
uniqueness of hitting times of a transverse section `TauCeti.eventually_eq_flowHittingTime_iff`).
Hence the flow embeds `[-1, 1] × K` for a compact piece `K` of `Z'`, and the point of `Z'` depends
continuously on the exit point.

## Main results

In the namespace `TauCeti.IsAdaptedPseudoGradient`:

* `eventually_eq_zero_of_flow_eq_of_isSliceChart`: near a regular point, an orbit meets a
  flattened set transverse to the flow at most once.
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

/-- A homeomorphism from `[0, r₀]` onto `closure S = insert z₀ S`, taking `0` to `z₀`, takes every
nonzero parameter into `S`. -/
private theorem val_homeomorph_mem_of_ne_zero {X : Type*} [TopologicalSpace X] {S : Set X}
    {z₀ : X} {r₀ : ℝ} (hr₀ : 0 ≤ r₀) (e : Icc (0 : ℝ) r₀ ≃ₜ closure S)
    (hcl : closure S = insert z₀ S) (he₀ : (e ⟨0, left_mem_Icc.2 hr₀⟩).val = z₀)
    (s : Icc (0 : ℝ) r₀) (hs : (s : ℝ) ≠ 0) : (e s).val ∈ S := by
  have hmem : (e s).val ∈ insert z₀ S := hcl ▸ (e s).property
  refine hmem.resolve_left fun h0 ↦ hs ?_
  have : e s = e ⟨0, left_mem_Icc.2 hr₀⟩ := Subtype.ext (h0.trans he₀.symm)
  exact congrArg Subtype.val (e.injective this)

namespace IsAdaptedPseudoGradient

/-- **An orbit meets a set transverse to the flow at most once near a regular point.** Let `Z` be
a set flattened near a point `y` by a chart of the maximal atlas, with `X y` not tangent to `Z` at
`y`, so that `X y ≠ 0` and `y` is not a critical point. Then two points of `Z` near `y` on a common
orbit are equal, and the time from one to the other is `0`. -/
theorem eventually_eq_zero_of_flow_eq_of_isSliceChart (hX : IsAdaptedPseudoGradient f X)
    {Z : Set M} {y : M} {L : Submodule ℝ E} {φZ : OpenPartialHomeomorph M E}
    (hφZ : φZ ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M) (hZ : IsSliceChart φZ (L : Set E) Z)
    (hyφZ : y ∈ φZ.source) (hyZ : y ∈ Z)
    (hXZ : X y ∉ Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) Z y)) :
    ∀ᶠ w : M × M in 𝓝 (y, y), w.1 ∈ Z → w.2 ∈ Z → ∀ t, hX.flow t w.1 = w.2 → t = 0 := by
  have hL : IsClosed (L : Set E) := Submodule.isClosed_of_finiteDimensional _
  -- `y` is not a critical point, since `X y` is not tangent to `Z`, so in particular nonzero.
  have hy : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f y ≠ 0 := mt hX.eq_zero_iff.2 fun h0 ↦ hXZ (by
    rw [h0]
    exact zero_mem _)
  -- A linear form `ℓ` vanishing on `L` but not on the image of `X y` in the chart: the level of
  -- `g = ℓ ∘ φZ` through `y` contains `Z` near `y` and is transverse to the flow.
  have hXL : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φZ y (X y) ∉ L := fun h ↦ hXZ <| by
    rw [hZ.span_mtangentConeAt_eq_comap (by simp) hφZ hL hyφZ hyZ]
    exact h
  obtain ⟨ℓ, hℓ, hLℓ⟩ := Submodule.exists_le_ker_of_notMem hXL
  set ℓc : E →L[ℝ] ℝ := LinearMap.toContinuousLinearMap ℓ
  set g : M → ℝ := ℓc ∘ φZ with hg
  have hφZy : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ φZ y := contMDiffAt_of_mem_maximalAtlas hφZ hyφZ
  have hgd : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ) ∞ g y := ℓc.contMDiff.contMDiffAt.comp y hφZy
  have hgv : mvfderiv 𝓘(ℝ, E) g y (X y) ≠ 0 := by
    have h := mvfderiv_comp_apply (g := ℓc) (f := φZ) y
      ((ℓc.contMDiff (n := ∞)).mdifferentiable (by simp) _) (hφZy.mdifferentiableAt (by simp)) (X y)
    rw [← hg] at h
    rw [h, mvfderiv_eq_fderiv_apply, ℓc.fderiv]
    exact hℓ
  -- Near `(0, y)` the orbit of a point meets the level of `g` through `y` at a unique time.
  have hv : CMDiff 1 (fun z ↦ (⟨z, X z⟩ : TangentBundle 𝓘(ℝ, E) M)) := hX.contMDiff.of_le (by simp)
  have hT := mem_flowDomain_zero hv y
  have hhit := eventually_eq_flowHittingTime_iff hv hT
    (by rw [flowOf_zero]; exact hgd.of_le (by simp)) (by rw [flowOf_zero]; exact hgv)
  rw [flowOf_zero] at hhit
  have hflow : ∀ t z, flowOf X t z = hX.flow t z := fun t z ↦ by
    rw [flowOf_apply, hX.flow_apply]
  obtain ⟨A, hA, B, hB, hAB⟩ := mem_nhds_prod_iff.1 hhit
  obtain ⟨δ, hδ, hδA⟩ := Metric.mem_nhds_iff.1 hA
  -- Far from time `0`, `f` has dropped or risen along the orbit by a definite amount.
  have hanti := hX.strictAnti_comp (hX.isMIntegralCurve_flow y) (hX.mfderiv_flow_ne_zero hy)
  have h₁ : f (hX.flow (δ / 2) y) < f y := by
    simpa using hanti (half_pos hδ)
  have h₂ : f y < f (hX.flow (-(δ / 2)) y) := by
    simpa using hanti (neg_lt_zero.2 (half_pos hδ))
  have hc₁ : Continuous fun w ↦ f (hX.flow (δ / 2) w) :=
    hX.mdifferentiable.continuous.comp (hX.contMDiff_flow_apply _).continuous
  have hc₂ : Continuous fun w ↦ f (hX.flow (-(δ / 2)) w) :=
    hX.mdifferentiable.continuous.comp (hX.contMDiff_flow_apply _).continuous
  obtain ⟨m₁, hm₁, hm₁'⟩ := exists_between h₁
  obtain ⟨m₂, hm₂, hm₂'⟩ := exists_between h₂
  have hfy := hX.mdifferentiable.continuous.continuousAt (x := y)
  have hB' : ∀ᶠ w in 𝓝 y, w ∈ B := hB
  have hN₁ : ∀ᶠ w in 𝓝 y, f (hX.flow (δ / 2) w) < m₁ ∧ m₂ < f (hX.flow (-(δ / 2)) w) ∧
      w ∈ B ∧ w ∈ φZ.source :=
    (hc₁.continuousAt.eventually (gt_mem_nhds hm₁)).and
      ((hc₂.continuousAt.eventually (lt_mem_nhds hm₂')).and
        (hB'.and (φZ.open_source.mem_nhds hyφZ)))
  have hN₂ : ∀ᶠ w in 𝓝 y, m₁ < f w ∧ f w < m₂ ∧ w ∈ φZ.source :=
    (hfy.eventually (lt_mem_nhds hm₁')).and
      ((hfy.eventually (gt_mem_nhds hm₂)).and (φZ.open_source.mem_nhds hyφZ))
  have hgZ : ∀ w ∈ φZ.source, w ∈ Z → g w = 0 := fun w hw hwZ ↦
    LinearMap.mem_ker.1 (hLℓ ((hZ.mem_iff hw).1 hwZ))
  filter_upwards [hN₁.prodMk_nhds hN₂] with w ⟨⟨hw₁, hw₂, hwB, hwφ⟩, hw'₁, hw'₂, hw'φ⟩ hwZ hw'Z t ht
  have hw1 := hX.antitone_flow w.1
  rcases lt_or_ge t (δ / 2) with htδ | htδ
  · rcases lt_or_ge (-(δ / 2)) t with htδ' | htδ'
    · -- For small times, both `0` and `t` are the hitting time of the level of `g` through `y`.
      have htA : t ∈ A := hδA (by
        rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt]; constructor <;> linarith)
      have h0A : (0 : ℝ) ∈ A := hδA (by simpa using hδ)
      have hgy : g y = 0 := hgZ y hyφZ hyZ
      have e₁ := (hAB (mk_mem_prod htA hwB)).1 (by
        simp only [hflow, ht, hgy]
        exact hgZ _ hw'φ hw'Z)
      have e₀ := (hAB (mk_mem_prod h0A hwB)).1 (by
        simp only [hflow, Flow.map_zero_apply, hgy]
        exact hgZ _ hwφ hwZ)
      exact e₁.trans e₀.symm
    · -- For times at most `-δ / 2`, `f` has risen.
      have := hw1 htδ'
      simp only [ht] at this
      linarith
  · -- For times at least `δ / 2`, `f` has dropped.
    have := hw1 htδ
    simp only [ht] at this
    linarith

/-- A point of `W^u(p)` whose orbit passes below a level `c ≤ f p` lies on a trajectory from `p`
to a critical point `b ≠ p` below `c`. -/
private theorem exists_mem_unstableSet_inter_stableSet_of_apply_flow_lt
    (hX : IsAdaptedPseudoGradient f X) (hf : IsMorse 𝓘(ℝ, E) f) {p w : M}
    (hw : w ∈ hX.flow.unstableSet p) {t c : ℝ} (ht : f (hX.flow t w) < c) (hcp : c ≤ f p) :
    ∃ b, p ≠ b ∧ w ∈ hX.flow.unstableSet p ∩ hX.flow.stableSet b ∧ f b < c := by
  obtain ⟨b, -, hb⟩ := hX.exists_tendsto_atTop hf w
  have hb : w ∈ hX.flow.stableSet b := Flow.mem_stableSet.2 hb
  have hfb : f b ≤ f (hX.flow t w) :=
    Flow.le_of_mem_stableSet_of_antitone ((Flow.apply_mem_stableSet_iff _ t).2 hb)
      hX.mdifferentiable.continuous.continuousAt (hX.antitone_flow _)
  exact ⟨b, by rintro rfl; linarith, ⟨hw, hb⟩, hfb.trans_lt ht⟩

/-- **A set transverse to an unstable manifold, of complementary dimension, is transverse to the
flow.** Let `Z` be flattened near a regular point `y` of `W^u(q)`, of dimension `n - ind q` and
transverse to `W^u(q)` at `y`. Then the tangent spaces of `Z` and `W^u(q)` at `y` meet in `0`, so
`X y`, which is tangent to `W^u(q)` and nonzero, is not tangent to `Z`. -/
private theorem notMem_span_mtangentConeAt_of_isSliceChart (hX : IsAdaptedPseudoGradient f X)
    (hf : IsMorse 𝓘(ℝ, E) f) {q y : M} {Z : Set M} {L : Submodule ℝ E}
    {φZ : OpenPartialHomeomorph M E} (hφZ : φZ ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M)
    (hZ : IsSliceChart φZ (L : Set E) Z) (hyφZ : y ∈ φZ.source) (hyZ : y ∈ Z)
    (hy : y ∈ hX.flow.unstableSet q) (hyc : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f y ≠ 0)
    (hdim : Module.finrank ℝ L + manifoldMorseIndex 𝓘(ℝ, E) f q = Module.finrank ℝ E)
    (htr : Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) Z y) ⊔
      Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX.flow.unstableSet q) y) = ⊤) :
    X y ∉ Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) Z y) := by
  have hL : IsClosed (L : Set E) := Submodule.isClosed_of_finiteDimensional _
  intro hXy
  have hXu : X y ∈ Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX.flow.unstableSet q) y) :=
    Submodule.subset_span (hX.mem_mtangentConeAt_of_isInvariant
      (hX.flow.isInvariant_unstableSet q) hy)
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq
    (Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) Z y))
    (Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX.flow.unstableSet q) y))
  rw [htr, finrank_top, hZ.finrank_span_mtangentConeAt (by simp) hφZ hL hyφZ hyZ,
    hX.finrank_span_mtangentConeAt_unstableSet hf hy] at hsum
  have hinf := Submodule.finrank_eq_zero.1 (by omega : Module.finrank ℝ ↥(
    Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) Z y) ⊓
      Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX.flow.unstableSet q) y)) = 0)
  have hmem : X y ∈ Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) Z y) ⊓
      Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX.flow.unstableSet q) y) := ⟨hXy, hXu⟩
  have h0 : X y = 0 := by
    rw [hinf] at hmem
    exact (Submodule.mem_bot ℝ).1 hmem
  have := hX.mvfderiv_apply_lt_zero y hyc
  rw [h0, map_zero] at this
  exact lt_irrefl _ this

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
  obtain ⟨r, -, hyr⟩ := hX.exists_tendsto_atTop hf y
  have hyr : y ∈ hX.flow.stableSet r := Flow.mem_stableSet.2 hyr
  have hqr : q ≠ r := by
    rintro rfl
    exact hyq (hX.eq_of_mem_unstableSet_inter_stableSet ⟨hy, hyr⟩)
  obtain ⟨φ, ε, ρ, T₁, T₂, y₁, y₂, hφ, hε, hερ, hε₂, hloc, hT₁, hT₂, hy₁φ, hy₂φ, hy₁s, hy₁ε,
    hy₂u, hy₂ε⟩ := hX.exists_morseBox_of_broken hf hpq' hqr ha₁ ⟨hy, hyr⟩
  set Φ : M → WithLp 2 (({i // φ.weight i = 1} → ℝ) × ({i // ¬φ.weight i = 1} → ℝ)) :=
    fun w ↦ φ.splitCoord (φ.coord (φ.toChart w)) with hΦdef
  set Ψ : WithLp 2 (({i // φ.weight i = 1} → ℝ) × ({i // ¬φ.weight i = 1} → ℝ)) → M :=
    fun z ↦ φ.toChart.symm (φ.coord.symm (φ.splitCoord.symm z)) with hΨdef
  have hΨΦ : ∀ w ∈ φ.toChart.source, Ψ (Φ w) = w := fun w hw ↦ by
    simp only [hΨdef, hΦdef, LinearEquiv.symm_apply_apply, φ.toChart.left_inv hw]
  have hε₁ : ∀ z, ‖z‖ ≤ ε → φ.coord.symm z ∈ φ.toChart.target := fun z hz ↦
    hε₂ z (by linarith)
  have hy₁ : y₁ ∈ hX.flow.unstableSet p ∩ hX.flow.stableSet q :=
    hT₁ ▸ hX.flow.isInvariant_unstableSet_inter_stableSet p q T₁ ha₁
  have hy₂ : y₂ ∈ hX.flow.unstableSet q ∩ hX.flow.stableSet r :=
    hT₂ ▸ hX.flow.isInvariant_unstableSet_inter_stableSet q r T₂ ⟨hy, hyr⟩
  have hy₂y : hX.flow (-T₂) y₂ = y := by rw [← hT₂, Flow.map_neg_apply_map]
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
  set Z' := hX.flow (-T₂) ⁻¹' Z with hZ'def
  obtain ⟨φ', hφ', hZ', hy₂φ', htr'⟩ := hX.exists_isSliceChart_preimage_flow hφZ hZ hyφZ htr T₂
  rw [hT₂] at hy₂φ' htr'
  have hy₂Z : y₂ ∈ Z' := by rw [hZ'def, mem_preimage, hy₂y]; exact hyZ
  have hL : IsClosed (L : Set E) := Submodule.isClosed_of_finiteDimensional _
  have hdimZ' : Module.finrank ℝ (Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) Z' y₂)) =
      Module.finrank ℝ L := hZ'.finrank_span_mtangentConeAt (by simp) hφ' hL hy₂φ' hy₂Z
  -- Near `y₂`, the point of `Z'` on an orbit depends continuously on the orbit.
  have hy₂c : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f y₂ ≠ 0 :=
    hX.mfderiv_ne_zero_of_mem_unstableSet_inter_stableSet hqr hy₂
  have hΦc : ContinuousAt Φ y₂ :=
    (φ.splitCoordL.continuous.continuousAt.comp (φ.toChart.continuousAt hy₂φ)).congr
      (.of_forall fun _ ↦ φ.splitCoordL_apply _)
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
    refine ⟨val_homeomorph_mem_of_ne_zero hr₀.le e hcl he₀ s hs, ?_⟩
    have := he (e s)
    rw [e.symm_apply_apply] at this
    rw [this, div_mul_cancel₀ _ hε.ne']
  -- Points of the gluing pairs read on `M`: the entrance points lie in `W^u(p)`, and the exit
  -- points are reached from points of `C ∩ Z'` in times in `[-1, 1]`.
  have hentry : ∀ z ∈ splitGluingPairs ε r₀ g k, Ψ z.1 ∈ hX.flow.unstableSet p := by
    intro z hz
    obtain ⟨⟨z₁, ⟨⟨hw, hwf, hws⟩, hwu, -⟩, hwz⟩, -⟩ := hpairs z hz
    have h₁ := hX.flow_splitEntryTime_of_norm_lt φ hφ hε hε₂ hw hwf hws
    rw [hwz] at h₁
    simp only [hΨdef]
    rw [← h₁]
    exact (Flow.apply_mem_unstableSet_iff _ _).2 hwu
  have hexitR : ∀ z ∈ splitGluingPairs ε r₀ g k, Ψ z.2 ∈ R := by
    intro z hz
    obtain ⟨-, ⟨z₂, ⟨hz₂C, hz₂Z⟩, hz₂⟩⟩ := hpairs z hz
    obtain ⟨⟨hw, hwf, hws⟩, -, hτ⟩ := hCm _ hz₂C
    have h₂ := hX.flow_splitExitTime_of_norm_lt φ hφ hε hε₂ hw hwf hws
    rw [hz₂] at h₂
    exact ⟨(_, ι₂ z₂), ⟨Ioo_subset_Icc_self hτ, hz₂C, hz₂Z⟩, h₂⟩
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
    obtain ⟨hsrc, -, -, hpass, -⟩ := mem_splitGluingPairs.1 hz
    have hflow : hX.flow (splitExitTime ε z.1) (Ψ z.1) = Ψ z.2 := by
      rw [hpass]; exact hX.flow_splitExitTime φ hφ (fun z hz ↦ hε₂ z (by linarith)) hsrc
    obtain ⟨hK, τ, hτ⟩ := hπR _ (hmemR s)
    refine ⟨hentry z hz, hK.2, -τ + splitExitTime ε z.1, ?_⟩
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
    have h1 := hX.eq_of_flow_eq_of_mem_splitPassage_source φ hφ hε₁ (mem_splitGluingPairs.1 hz).1
      (mem_splitGluingPairs.1 hz').1
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

/-- **Gluing a broken trajectory into a transverse set.** Let `X` be a Morse–Smale adapted
pseudo-gradient for a Morse function `f` on a compact manifold of dimension `n`, `a₁` a point of a
trajectory from `p` to a critical point `q` with `ind p = ind q + 1`, and `y ≠ q` a point of the
unstable manifold `W^u(q)`. Let `Z` be a set through `y` of dimension `n - ind q`, flattened near
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
    (hyq : y ≠ q) {L : Submodule ℝ E} {φZ : OpenPartialHomeomorph M E}
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
  -- Plan: follow the arc `B` of `exists_transverseGluingArc`, its first points to the level of
  -- `a₁` and its second points back by the flow to `Z`. The resulting map `F` is continuous and
  -- injective on a closed interval, hence an embedding, and every pair near `(a₁, y)` is a value
  -- of `F` at a parameter below the end of the interval.
  have hpq' : p ≠ q := by rintro rfl; omega
  obtain ⟨T₁, T₂, δ, hδ, B, hBc, hB₀, hBS, hBq, hBinj, hBfwd⟩ :=
    h.exists_transverseGluingArc hf hpq ha₁ hy hyq hφZ hZ hyφZ hyZ hdim htr
  set S := {w : M × M | w.2 ∈ hX.flow.unstableSet p ∩ Z ∧ f w.1 = f a₁ ∧
    ∃ t, hX.flow t w.1 = w.2} with hSdef
  have hfa₁ := hX.mem_Ioo_of_mem_unstableSet_inter_stableSet hpq' ha₁
  have hy₁ : hX.flow T₁ a₁ ∈ hX.flow.unstableSet p ∩ hX.flow.stableSet q :=
    hX.flow.isInvariant_unstableSet_inter_stableSet p q T₁ ha₁
  -- Along the arc, the first points run from `p` to a critical point below `f q`, except at `0`,
  -- where the trajectory runs to `q`.
  have hBb : ∀ s : Icc (0 : ℝ) δ, (s : ℝ) ≠ 0 → ∃ b, p ≠ b ∧
      (B s).1 ∈ hX.flow.unstableSet p ∩ hX.flow.stableSet b ∧ f b < f q := by
    intro s hs
    obtain ⟨hs₁, -, t, ht⟩ := hBS s hs
    exact exists_mem_unstableSet_inter_stableSet_of_apply_flow_lt hX hf hs₁ (t := t)
      (by rw [ht]; exact hBq s) (by linarith [hfa₁.1, hfa₁.2])
  have hB : ∀ s, ∃ b, p ≠ b ∧ (B s).1 ∈ hX.flow.unstableSet p ∩ hX.flow.stableSet b ∧
      f b < f a₁ := by
    intro s
    by_cases hs : (s : ℝ) = 0
    · obtain rfl : s = ⟨0, left_mem_Icc.2 hδ.le⟩ := Subtype.ext hs
      rw [hB₀]
      exact ⟨q, hpq', hy₁, hfa₁.1⟩
    · obtain ⟨b, hpb, hb, hfb⟩ := hBb s hs
      exact ⟨b, hpb, hb, hfb.trans hfa₁.1⟩
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
    have hne : ∀ s : Icc (0 : ℝ) δ, (s : ℝ) ≠ 0 → F s ≠ (a₁, y) := fun s hs hF ↦ by
      obtain ⟨b, -, hb, hfb⟩ := hBb s hs
      have hb' : (F s).1 ∈ hX.flow.stableSet b := (Flow.apply_mem_stableSet_iff _ _).2 hb.2
      rw [hF] at hb'
      have hbq : b ≠ q := by rintro rfl; exact lt_irrefl _ hfb
      exact (Flow.disjoint_stableSet hbq).ne_of_mem hb' ha₁.2 rfl
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
    -- Equal first level points put the first points of `B s` and `B s'` on one orbit.
    refine hBinj s s' hs hs' (Flow.levelCrossingTime hX.flow f (f a₁) (B s).1 -
      Flow.levelCrossingTime hX.flow f (f a₁) (B s').1) ?_
    have h₁ := congrArg Prod.fst hss'
    simp only [hFdef] at h₁
    rw [sub_eq_add_neg, add_comm, Flow.map_add, h₁, ← Flow.map_add, neg_add_cancel,
      Flow.map_zero_apply]
  -- Every recorded point near the broken configuration is a value of the arc.
  have hfwd : ∀ᶠ w in 𝓝[S] (a₁, y),
      ∃ s : Ico (0 : ℝ) δ, F (inclusion Ico_subset_Icc_self s) = w := by
    have hSmem : ∀ᶠ w in 𝓝[S] (a₁, y), w ∈ S := self_mem_nhdsWithin
    have hfyq : f y < f q := by
      obtain ⟨r, -, hyr⟩ := hX.exists_tendsto_atTop hf y
      have hqr : q ≠ r := by
        rintro rfl
        exact hyq (hX.eq_of_mem_unstableSet_inter_stableSet ⟨hy, Flow.mem_stableSet.2 hyr⟩)
      exact (hX.mem_Ioo_of_mem_unstableSet_inter_stableSet hqr
        ⟨hy, Flow.mem_stableSet.2 hyr⟩).2
    have hlow : ∀ᶠ w in 𝓝[S] (a₁, y), f w.2 < f q :=
      ((hX.mdifferentiable.continuous.comp continuous_snd).continuousAt.eventually
        (gt_mem_nhds hfyq)).filter_mono nhdsWithin_le_nhds
    -- The first points of recorded points lie on trajectories from `p` below `f q`.
    have hrec : ∀ w ∈ S, f w.2 < f q → ∃ b, p ≠ b ∧
        w.1 ∈ hX.flow.unstableSet p ∩ hX.flow.stableSet b ∧ f b < f q := by
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
      (by linarith [hfy₁.1]) hfy₁.2
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
  have hqr' : q ≠ r := by rintro rfl; omega
  have ha₂q : a₂ ≠ q := by
    rintro rfl
    exact (hX.mem_Ioo_of_mem_unstableSet_inter_stableSet hqr' ha₂).2.false
  -- The transverse set is the level cut `W^s(r) ∩ {f = f a₂}`.
  obtain ⟨L, φZ, hφZ, hZ, ha₂φZ, hdim, htr⟩ :=
    h.exists_isSliceChart_stableSet_inter_level hf hqr ha₂
  obtain ⟨N, δ, hδ, e, he₀, hN, hNw⟩ :=
    h.exists_homeomorph_Ico_of_isSliceChart hf hpq ha₁ ha₂.1 ha₂q hφZ hZ ha₂φZ ⟨ha₂.2, rfl⟩
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
