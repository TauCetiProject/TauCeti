/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.RiemannSurface.LocalNormalForm
public import TauCeti.Analysis.Complex.RiemannSurface.Degree
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Discs above a branch value

For a holomorphic map from a compact Riemann surface which is constant near no point, a
sufficiently small coordinate disc in the target has its entire preimage in disjoint power
coordinates around the points of the central fibre. The preimages of both the open and the
closed target disc are exactly the unions of the corresponding source discs. The source radii
satisfy `rₓ ^ mₓ = δ`, where `mₓ` is the local multiplicity and `δ` the common target radius.
The closed discs lie inside the coordinate domains, so they are compact embedded discs.

These neighbourhoods permit excision of discs around branch values while retaining the full
preimage, as needed for the topological branched-cover Euler-characteristic formula. Source
coordinates can be chosen inside independently prescribed neighbourhoods, and the target
coordinate is arbitrary. Neither connectedness of the target nor surjectivity is required.

The construction combines `exists_chart_eq_pow_localMultiplicity` with compactness of the
complement of the finitely many source charts. This is also the separation argument used in
`RiemannSurface.FiberMultiset` to assemble local fibre multisets.

## References

* Otto Forster, *Lectures on Riemann Surfaces*, §§4 and 17.
* Rick Miranda, *Algebraic Curves and Riemann Surfaces*, Chapter II, §4.
-/

public noncomputable section

open Filter Function IsManifold Metric Set Topology
open scoped Manifold

namespace TauCeti.RiemannSurface

section Helpers

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y}

/-- Compactness rules out further sheets outside a neighbourhood of the fibre: if an open set `U`
contains `f ⁻¹' {y}`, then in a chart `e'` at `y` a small open coordinate disc has its
preimage inside `U`. -/
theorem exists_ball_preimage_subset [CompactSpace X] [T2Space Y] (hf : Continuous f) {y : Y}
    {e' : OpenPartialHomeomorph Y ℂ} (hy : y ∈ e'.source) {U : Set X} (hU : IsOpen U)
    (hfib : f ⁻¹' {y} ⊆ U) :
    ∃ ε > 0, ball (e' y) ε ⊆ e'.target ∧
      ∀ z, f z ∈ e'.source → e' (f z) ∈ ball (e' y) ε → z ∈ U := by
  have hV : IsOpen (f '' Uᶜ)ᶜ :=
    (hU.isClosed_compl.isCompact.image hf).isClosed.isOpen_compl
  have hyV : y ∈ (f '' Uᶜ)ᶜ := by
    rintro ⟨z, hz, hzy⟩
    exact hz (hfib hzy)
  have hcoord : e'.target ∩ e'.symm ⁻¹' (f '' Uᶜ)ᶜ ∈ 𝓝 (e' y) :=
    inter_mem (e'.open_target.mem_nhds (e'.map_source hy))
      ((e'.tendsto_symm hy).eventually (hV.mem_nhds hyV))
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp hcoord
  refine ⟨ε, hε, fun w hw ↦ (hεsub hw).1, fun z hz hzb ↦ ?_⟩
  by_contra hzU
  have := (hεsub hzb).2
  simp only [mem_preimage, e'.left_inv hz] at this
  exact this ⟨z, hzU, rfl⟩

/-- The preimage of an open coordinate disc is the union of the source discs, when each source
chart `e x` carries the target chart to the `m x`-th power with radii `r x ^ m x = δ`, and every
point over the disc lies in a source chart. -/
private theorem preimage_ball_eq_iUnion {ι : Type*} {e' : OpenPartialHomeomorph Y ℂ} {y : Y}
    {δ : ℝ} {e : ι → OpenPartialHomeomorph X ℂ} {r : ι → ℝ} {m : ι → ℕ}
    (hm : ∀ x, m x ≠ 0) (hr : ∀ x, 0 < r x) (hrpow : ∀ x, r x ^ m x = δ)
    (hrsub : ∀ x, closedBall (0 : ℂ) (r x) ⊆ (e x).target)
    (hpow : ∀ x, ∀ z ∈ (e x).source, f z ∈ e'.source ∧ e' (f z) - e' y = e x z ^ m x)
    (hfull : ∀ z, f z ∈ e'.source ∧ e' (f z) ∈ ball (e' y) δ → z ∈ ⋃ x, (e x).source) :
    f ⁻¹' (e'.source ∩ e' ⁻¹' ball (e' y) δ) = ⋃ x, (e x).symm '' ball 0 (r x) := by
  ext z
  constructor
  · intro hz
    obtain ⟨x, hx⟩ := mem_iUnion.mp (hfull z hz)
    refine mem_iUnion.mpr ⟨x, e x z, ?_, (e x).left_inv hx⟩
    rw [mem_ball_zero_iff, ← pow_lt_pow_iff_left₀ (norm_nonneg _) (hr x).le (hm x), hrpow x,
      ← norm_pow, ← (hpow x z hx).2]
    exact mem_ball_iff_norm.mp hz.2
  · intro hz
    obtain ⟨x, w, hw, rfl⟩ := mem_iUnion.mp hz
    have hwt := hrsub x (ball_subset_closedBall hw)
    have h := hpow x ((e x).symm w) ((e x).map_target hwt)
    refine ⟨h.1, ?_⟩
    rw [mem_preimage, mem_ball_iff_norm, h.2, (e x).right_inv hwt, norm_pow, ← hrpow x]
    exact (pow_lt_pow_iff_left₀ (norm_nonneg _) (hr x).le (hm x)).2 (mem_ball_zero_iff.mp hw)

/-- The preimage of a closed coordinate disc is the union of the closed source discs, under the
hypotheses of `preimage_ball_eq_iUnion`. -/
private theorem preimage_closedBall_eq_iUnion {ι : Type*} {e' : OpenPartialHomeomorph Y ℂ}
    {y : Y} {δ : ℝ} {e : ι → OpenPartialHomeomorph X ℂ} {r : ι → ℝ} {m : ι → ℕ}
    (hm : ∀ x, m x ≠ 0) (hr : ∀ x, 0 < r x) (hrpow : ∀ x, r x ^ m x = δ)
    (hrsub : ∀ x, closedBall (0 : ℂ) (r x) ⊆ (e x).target)
    (hpow : ∀ x, ∀ z ∈ (e x).source, f z ∈ e'.source ∧ e' (f z) - e' y = e x z ^ m x)
    (hfull : ∀ z, f z ∈ e'.source ∧ e' (f z) ∈ closedBall (e' y) δ → z ∈ ⋃ x, (e x).source) :
    f ⁻¹' (e'.source ∩ e' ⁻¹' closedBall (e' y) δ) = ⋃ x, (e x).symm '' closedBall 0 (r x) := by
  ext z
  constructor
  · intro hz
    obtain ⟨x, hx⟩ := mem_iUnion.mp (hfull z hz)
    refine mem_iUnion.mpr ⟨x, e x z, ?_, (e x).left_inv hx⟩
    rw [mem_closedBall_zero_iff, ← pow_le_pow_iff_left₀ (norm_nonneg _) (hr x).le (hm x),
      hrpow x, ← norm_pow, ← (hpow x z hx).2]
    exact mem_closedBall_iff_norm.mp hz.2
  · intro hz
    obtain ⟨x, w, hw, rfl⟩ := mem_iUnion.mp hz
    have hwt := hrsub x hw
    have h := hpow x ((e x).symm w) ((e x).map_target hwt)
    refine ⟨h.1, ?_⟩
    rw [mem_preimage, mem_closedBall_iff_norm, h.2, (e x).right_inv hwt, norm_pow, ← hrpow x]
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (hr x).le (hm x)).2 (mem_closedBall_zero_iff.mp hw)

end Helpers

variable {X Y : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [TopologicalSpace Y] [ChartedSpace ℂ Y]
  [IsManifold 𝓘(ℂ) 1 X] [IsManifold 𝓘(ℂ) 1 Y]
  [CompactSpace X] [T2Space X] [T2Space Y] {f : X → Y}

/-- **Disjoint power coordinates over a whole disc.** In any target chart at `y`, a sufficiently
small disc and its closure lift to disjoint coordinate discs around the points of `f ⁻¹' {y}`.
The map on each disc is the power of exponent `localMultiplicity f x`; the radii satisfy
`rₓ ^ localMultiplicity f x = δ`. The closed discs are contained in the chart domains, and
both preimage equalities account for every point upstairs. Each source chart can be chosen
inside its prescribed neighbourhood `W x`. -/
theorem exists_disjoint_power_charts
    (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) (hne : ∀ x, ¬ EventuallyConst f (𝓝 x))
    {y : Y} {e' : OpenPartialHomeomorph Y ℂ}
    (he' : e' ∈ maximalAtlas 𝓘(ℂ) 1 Y) (hy : y ∈ e'.source)
    (W : (f ⁻¹' {y}) → Set X) (hW : ∀ x : f ⁻¹' {y}, W x ∈ 𝓝 (x : X)) :
    ∃ (δ : ℝ) (e : (f ⁻¹' {y}) → OpenPartialHomeomorph X ℂ)
        (r : (f ⁻¹' {y}) → ℝ),
      0 < δ ∧ closedBall (e' y) δ ⊆ e'.target ∧
      (∀ x, e x ∈ maximalAtlas 𝓘(ℂ) 1 X ∧ (x : X) ∈ (e x).source ∧ e x x = 0 ∧
        (e x).source ⊆ W x ∧ 0 < r x ∧
        r x ^ localMultiplicity f x = δ ∧ closedBall 0 (r x) ⊆ (e x).target ∧
        ∀ z ∈ (e x).source,
          f z ∈ e'.source ∧ e' (f z) - e' y = e x z ^ localMultiplicity f x) ∧
      Pairwise (fun x x' ↦ Disjoint (e x).source (e x').source) ∧
      f ⁻¹' (e'.source ∩ e' ⁻¹' ball (e' y) δ) =
        ⋃ x, (e x).symm '' ball 0 (r x) ∧
      f ⁻¹' (e'.source ∩ e' ⁻¹' closedBall (e' y) δ) =
        ⋃ x, (e x).symm '' closedBall 0 (r x) := by
  classical
  have hm (x : X) : localMultiplicity f x ≠ 0 :=
    ((localMultiplicity_pos_iff (.of_forall hf)).2 (hne x)).ne'
  have hS : (f ⁻¹' {y}).Finite := finite_preimage_singleton hf hne y
  let : Fintype (f ⁻¹' {y}) := hS.fintype
  -- Separate the central fibre before choosing the local normal forms.
  obtain ⟨O, hO, hdisj⟩ := hS.t2_separation
  have hloc (x : f ⁻¹' {y}) : ∃ e : OpenPartialHomeomorph X ℂ,
      e ∈ maximalAtlas 𝓘(ℂ) 1 X ∧ (x : X) ∈ e.source ∧ e x = 0 ∧
      e.source ⊆ O x ∩ W x ∧ ∀ z ∈ e.source,
        f z ∈ e'.source ∧ e' (f z) - e' y = e z ^ localMultiplicity f x := by
    have hx : f x = y := x.2
    simpa only [hx] using exists_chart_eq_pow_localMultiplicity (.of_forall hf) (hne x)
      he' (by rwa [hx]) (inter_mem ((hO x).2.mem_nhds (hO x).1) (hW x))
  choose e he hxe hex hsub hpow using hloc
  have hedisj : Pairwise (fun x x' : f ⁻¹' {y} ↦ Disjoint (e x).source (e x').source) := by
    intro x x' hxx'
    exact (hdisj x.2 x'.2 (fun h ↦ hxx' (Subtype.ext h))).mono
      ((hsub x).trans inter_subset_left) ((hsub x').trans inter_subset_left)
  obtain ⟨ε, hε, hεt, hεU⟩ := exists_ball_preimage_subset hf.continuous hy
    (isOpen_iUnion fun x ↦ (e x).open_source)
    fun z hz ↦ mem_iUnion.mpr ⟨⟨z, hz⟩, hxe ⟨z, hz⟩⟩
  have hrad (x : f ⁻¹' {y}) : ∃ R > 0, ball (0 : ℂ) R ⊆ (e x).target :=
    Metric.mem_nhds_iff.mp ((e x).open_target.mem_nhds (hex x ▸ (e x).map_source (hxe x)))
  choose R hR hRsub using hrad
  -- A common target radius fits inside every powered source radius and the omitted-sheet gap.
  obtain ⟨η, hη, hηsub⟩ := Metric.mem_nhds_iff.mp (show ∀ᶠ δ : ℝ in 𝓝 0,
      δ < ε ∧ ∀ x : f ⁻¹' {y}, δ < R x ^ localMultiplicity f x from
    (eventually_lt_nhds hε).and (eventually_all.mpr fun x ↦
      eventually_lt_nhds (pow_pos (hR x) _)))
  obtain ⟨δ, hδ, hδsmall⟩ : ∃ δ : ℝ, 0 < δ ∧
      δ < ε ∧ ∀ x : f ⁻¹' {y}, δ < R x ^ localMultiplicity f x :=
    ⟨η / 2, half_pos hη, hηsub (by
      rw [mem_ball_zero_iff, Real.norm_eq_abs, abs_of_pos (half_pos hη)]
      exact half_lt_self hη)⟩
  let r (x : f ⁻¹' {y}) := δ ^ (localMultiplicity f x : ℝ)⁻¹
  have hr (x : f ⁻¹' {y}) : 0 < r x := Real.rpow_pos_of_pos hδ _
  have hrpow (x : f ⁻¹' {y}) : r x ^ localMultiplicity f x = δ :=
    Real.rpow_inv_natCast_pow hδ.le (hm x)
  have hrsub (x : f ⁻¹' {y}) : closedBall (0 : ℂ) (r x) ⊆ (e x).target :=
    (closedBall_subset_ball (lt_of_pow_lt_pow_left₀ (localMultiplicity f x) (hR x).le
      (by rw [hrpow]; exact hδsmall.2 x))).trans (hRsub x)
  have hfull {z : X} (hz : f z ∈ e'.source ∧ e' (f z) ∈ closedBall (e' y) δ) :
      z ∈ ⋃ x, (e x).source :=
    hεU z hz.1 (closedBall_subset_ball hδsmall.1 hz.2)
  exact ⟨δ, e, r, hδ, (closedBall_subset_ball hδsmall.1).trans hεt,
    fun x ↦ ⟨he x, hxe x, hex x, (hsub x).trans inter_subset_right, hr x, hrpow x, hrsub x,
      hpow x⟩, hedisj,
    preimage_ball_eq_iUnion (fun x ↦ hm x) hr hrpow hrsub hpow fun z hz ↦
      hfull ⟨hz.1, ball_subset_closedBall hz.2⟩,
    preimage_closedBall_eq_iUnion (fun x ↦ hm x) hr hrpow hrsub hpow fun z hz ↦ hfull hz⟩

end TauCeti.RiemannSurface
