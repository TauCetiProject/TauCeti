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
  let S := f ⁻¹' {y}
  have hS : S.Finite := finite_preimage_singleton hf hne y
  let : Fintype S := hS.fintype
  -- Separate the central fibre before choosing the local normal forms.
  obtain ⟨O, hO, hdisj⟩ := hS.t2_separation
  have hloc (x : S) : ∃ e : OpenPartialHomeomorph X ℂ,
      e ∈ maximalAtlas 𝓘(ℂ) 1 X ∧ (x : X) ∈ e.source ∧ e x = 0 ∧
      e.source ⊆ O x ∩ W x ∧ ∀ z ∈ e.source,
        f z ∈ e'.source ∧ e' (f z) - e' y = e z ^ localMultiplicity f x := by
    have hx : f x = y := x.2
    simpa only [hx] using exists_chart_eq_pow_localMultiplicity (.of_forall hf) (hne x)
      he' (hx ▸ hy) (inter_mem ((hO x).2.mem_nhds (hO x).1) (hW x))
  choose e he hxe hex hsub hpow using hloc
  have hedisj : Pairwise (fun x x' : S ↦ Disjoint (e x).source (e x').source) := by
    intro x x' hxx'
    exact (hdisj x.2 x'.2 (fun h ↦ hxx' (Subtype.ext h))).mono
      ((hsub x).trans inter_subset_left) ((hsub x').trans inter_subset_left)
  -- Compactness rules out further sheets outside these chart domains.
  let U := ⋃ x : S, (e x).source
  have hU : IsOpen U := isOpen_iUnion fun x ↦ (e x).open_source
  let V := (f '' Uᶜ)ᶜ
  have hyV : y ∈ V := by
    rintro ⟨z, hz, hzy⟩
    exact hz (mem_iUnion.mpr ⟨⟨z, hzy⟩, hxe ⟨z, hzy⟩⟩)
  have hV : IsOpen V := (hU.isClosed_compl.isCompact.image hf.continuous).isClosed.isOpen_compl
  have hpre : f ⁻¹' V ⊆ U := by
    intro z hz
    by_contra hzU
    exact hz ⟨z, hzU, rfl⟩
  have hcoord : e'.target ∩ e'.symm ⁻¹' V ∈ 𝓝 (e' y) := by
    refine inter_mem (e'.open_target.mem_nhds (e'.map_source hy)) ?_
    exact (e'.tendsto_symm hy).eventually (hV.mem_nhds hyV)
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp hcoord
  have hrad (x : S) : ∃ R > 0, ball (0 : ℂ) R ⊆ (e x).target :=
    Metric.mem_nhds_iff.mp ((e x).open_target.mem_nhds (hex x ▸ (e x).map_source (hxe x)))
  choose R hR hRsub using hrad
  -- A common target radius fits inside every powered source radius and the omitted-sheet gap.
  have hsmall : ∀ᶠ δ : ℝ in 𝓝 0, δ < ε ∧ ∀ x : S, δ < R x ^ localMultiplicity f x := by
    exact (eventually_lt_nhds hε).and (eventually_all.mpr fun x ↦
      eventually_lt_nhds (pow_pos (hR x) _))
  obtain ⟨η, hη, hηsub⟩ := Metric.mem_nhds_iff.mp hsmall
  let δ := η / 2
  have hδ : 0 < δ := half_pos hη
  have hδsmall : δ < ε ∧ ∀ x : S, δ < R x ^ localMultiplicity f x :=
    hηsub (by simpa only [mem_ball, Real.dist_eq, sub_zero, abs_of_pos hδ] using
      (half_lt_self hη))
  let r (x : S) := δ ^ (localMultiplicity f x : ℝ)⁻¹
  have hr (x : S) : 0 < r x := Real.rpow_pos_of_pos hδ _
  have hrpow (x : S) : r x ^ localMultiplicity f x = δ :=
    Real.rpow_inv_natCast_pow hδ.le (hm x)
  have hrsub (x : S) : closedBall (0 : ℂ) (r x) ⊆ (e x).target := by
    apply Subset.trans (closedBall_subset_ball ?_) (hRsub x)
    apply lt_of_pow_lt_pow_left₀ (localMultiplicity f x) (hR x).le
    rw [hrpow]
    exact hδsmall.2 x
  have htgt : closedBall (e' y) δ ⊆ e'.target ∩ e'.symm ⁻¹' V :=
    (closedBall_subset_ball hδsmall.1).trans hεsub
  have hfull {z : X} (hz : f z ∈ e'.source ∩ e' ⁻¹' closedBall (e' y) δ) : z ∈ U := by
    apply hpre
    have h := (htgt hz.2).2
    simpa only [mem_preimage, e'.left_inv hz.1] using h
  refine ⟨δ, e, r, hδ, htgt.trans inter_subset_left, fun x ↦
    ⟨he x, hxe x, hex x, (hsub x).trans inter_subset_right, hr x, hrpow x, hrsub x, hpow x⟩,
    hedisj, ?_, ?_⟩
  · ext z
    constructor
    · intro hz
      obtain ⟨x, hx⟩ := mem_iUnion.mp (hfull ⟨hz.1, ball_subset_closedBall hz.2⟩)
      refine mem_iUnion.mpr ⟨x, e x z, ?_, (e x).left_inv hx⟩
      rw [mem_ball_zero_iff, ← pow_lt_pow_iff_left₀ (norm_nonneg _) (hr x).le
        (hm x), hrpow x, ← norm_pow,
        ← (hpow x z hx).2]
      exact mem_ball_iff_norm.mp hz.2
    · intro hz
      obtain ⟨x, w, hw, rfl⟩ := mem_iUnion.mp hz
      have hwt := hrsub x (ball_subset_closedBall hw)
      have h := hpow x ((e x).symm w) ((e x).map_target hwt)
      refine ⟨h.1, ?_⟩
      rw [mem_preimage, mem_ball_iff_norm, h.2, (e x).right_inv hwt, norm_pow, ← hrpow x]
      exact (pow_lt_pow_iff_left₀ (norm_nonneg _) (hr x).le
        (hm x)).2 (mem_ball_zero_iff.mp hw)
  · ext z
    constructor
    · intro hz
      obtain ⟨x, hx⟩ := mem_iUnion.mp (hfull hz)
      refine mem_iUnion.mpr ⟨x, e x z, ?_, (e x).left_inv hx⟩
      rw [mem_closedBall_zero_iff, ← pow_le_pow_iff_left₀ (norm_nonneg _) (hr x).le
        (hm x), hrpow x, ← norm_pow,
        ← (hpow x z hx).2]
      exact mem_closedBall_iff_norm.mp hz.2
    · intro hz
      obtain ⟨x, w, hw, rfl⟩ := mem_iUnion.mp hz
      have hwt := hrsub x hw
      have h := hpow x ((e x).symm w) ((e x).map_target hwt)
      refine ⟨h.1, ?_⟩
      rw [mem_preimage, mem_closedBall_iff_norm, h.2, (e x).right_inv hwt, norm_pow, ← hrpow x]
      exact (pow_le_pow_iff_left₀ (norm_nonneg _) (hr x).le
        (hm x)).2
        (mem_closedBall_zero_iff.mp hw)

end TauCeti.RiemannSurface
