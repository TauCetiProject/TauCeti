/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.LipschitzDomain.Basic
import Mathlib.Topology.Order.IntermediateValue

/-!
# Admissible boundary parts of Lipschitz domains

Mixed boundary value problems impose a Dirichlet condition on a part `Γ` of the frontier of a
Lipschitz domain `Ω` and a Neumann condition on the rest. For the Sobolev functions vanishing on
`Γ` to be characterized by their trace, `Γ` has to sit in the boundary as regularly as the
boundary sits in the ambient space: near each frontier point, in a Lipschitz boundary chart of
`Ω`, the part `Γ` is the part of the boundary graph lying over all of the base, over none of it,
or over the region on one side of a Lipschitz interface in the base. These are the strong
Lipschitz pairs `(Ω, Γ)` of Bauer, Pauly and Schomburg.

Charts are those of `Set.IsLipschitzChart`: an affine isometry `e : F ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E)`
in which `Ω` is, inside the cylinder `normalCylinder h r`, the region strictly above the graph of
a Lipschitz `γ : E → ℝ`. The base regions are the subsets of `E` that are all of `E`, empty, or,
after a linear isometry `E ≃ₗᵢ[ℝ] WithLp 2 (ℝ × E')`, the region strictly above the graph of a
Lipschitz function on `E'` (`Set.IsAdmissibleBaseRegion`). Taking the region strictly below
instead gives nothing new, since the normal coordinate of `ℝ × E'` can be reflected. For
`E = ℝⁿ` the interface model is `E' = ℝⁿ⁻¹`; when `E` is zero-dimensional only the first two
shapes occur.

Relative openness of `Γ` in `frontier Ω` is not part of the definition: each chart presents `Γ`
near its centre as the graph over an open base region, so an admissible boundary part is
automatically relatively open (`Set.IsAdmissibleBoundaryPart.exists_isOpen_frontier_inter_eq`).
Admissibility is not a property of `closure Γ`: when `E` is nontrivial, removing one point from
an admissible `Γ` keeps its closure but destroys the chart description at the removed point.

## Main declarations

* `Set.IsAdmissibleBaseRegion`: the three shapes of base region.
* `Set.IsBoundaryPartChart`: a Lipschitz chart of `Ω` in which `Γ` is the part of the graph over
  a given base region, with restriction to smaller cylinders (`Set.IsBoundaryPartChart.mono`),
  recentring (`Set.IsBoundaryPartChart.trans_constVAdd`), transport by affine isometries
  (`Set.IsBoundaryPartChart.image`) and positive dilation (`Set.IsBoundaryPartChart.smul`), and
  its defining condition in the two set forms consumed by chart localization
  (`Set.IsBoundaryPartChart.inter_preimage_normalCylinder_subset`,
  `Set.IsBoundaryPartChart.setOf_inter_normalCylinder_subset`).
* `Set.IsLipschitzChart.isBoundaryPartChart_univ_of_subset`,
  `Set.IsLipschitzChart.isBoundaryPartChart_empty_of_disjoint`: a Lipschitz chart whose cylinder
  sees only points of `Γ` on the frontier, or no point of `Γ`, is a boundary-part chart over the
  whole base, or over the empty base region.
* `Set.IsBoundaryPartChart.ordConnected_inter_preimage`: with a one-dimensional base and an
  interval as base region, a frontier arc inside the cylinder meets `Γ` along an interval of
  parameters.
* `Set.IsAdmissibleBoundaryPart`: `Γ ⊆ frontier Ω` and every frontier point is the centre of a
  boundary-part chart with an admissible base region.
* `Set.IsLipschitzDomain.isAdmissibleBoundaryPart_of_frontier_inter_eq`: a relatively open `Γ` is
  admissible once the points of `closure Γ \ Γ` have boundary-part charts with admissible base.
* `Set.isAdmissibleBoundaryPart_iff_exists_mem_normalCylinder`: the charts need not be centred.
* `Set.IsLipschitzChart.exists_isBoundaryPartChart_empty`,
  `Set.IsLipschitzChart.exists_isBoundaryPartChart_univ`: a centred Lipschitz chart, shrunk, is a
  boundary-part chart over the empty base or the whole base when `Γ` misses, or contains, the
  frontier near the centre.
* `Set.IsAdmissibleBaseRegion.ordConnected`,
  `Set.IsAdmissibleBoundaryPart.exists_mem_nhds_forall_mem_of_mapsTo`: for a one-dimensional base,
  the base regions are order-connected, so along a frontier path near a point an admissible
  boundary part is met in an interval of parameters.
* `Set.isAdmissibleBaseRegion_Ioi`, `Set.isAdmissibleBaseRegion_Iio`: conversely, open half-lines
  are admissible base regions, with interfaces modelled on a zero space.
* `Set.IsAdmissibleBoundaryPart.isLipschitzDomain`: `Ω` is then a Lipschitz domain.
* `Set.IsAdmissibleBoundaryPart.exists_isOpen_frontier_inter_eq`: `Γ` is relatively open in the
  frontier.
* `Set.IsLipschitzDomain.isAdmissibleBoundaryPart_empty`,
  `Set.IsLipschitzDomain.isAdmissibleBoundaryPart_frontier`: `∅` and `frontier Ω` are admissible
  boundary parts of every Lipschitz domain, and `Set.isAdmissibleBoundaryPart_empty_iff`,
  `Set.isAdmissibleBoundaryPart_frontier_iff` show that they are so only for Lipschitz domains.
* `Set.isAdmissibleBoundaryPart_image_iff`, `Set.isAdmissibleBoundaryPart_smul_iff`: invariance
  under affine isometries and positive dilations of the pair `(Ω, Γ)`.
* `Set.isAdmissibleBoundaryPart_setOf_lt_fst`: the part of a Lipschitz graph over an admissible
  base region is an admissible boundary part of the region above the graph, and
  `Set.isAdmissibleBoundaryPart_normalHalfSpace` is its model case, a half-hyperplane in the
  boundary of a half-space.

## References

* S. Bauer, D. Pauly and M. Schomburg, *The Maxwell compactness property in bounded weak
  Lipschitz domains with mixed boundary conditions*, SIAM J. Math. Anal. 48 (2016), §2.1
  (strong Lipschitz pairs).
* P. Grisvard, *Elliptic Problems in Nonsmooth Domains*, Definition 1.2.1.1.
-/

public section

namespace Set

open Metric TauCeti Filter
open scoped Topology
open scoped NNReal Pointwise

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]

/-! ### Admissible base regions -/

/-- A set `B` in the base `E` of a boundary chart is an **admissible base region**, with
interfaces modelled on `E'`, if it is all of `E`, empty, or, after a linear isometry
`f : E ≃ₗᵢ[ℝ] WithLp 2 (ℝ × E')`, the region strictly above the graph of a Lipschitz function
`β : E' → ℝ`. -/
def IsAdmissibleBaseRegion (B : Set E) (E' : Type*) [NormedAddCommGroup E'] [NormedSpace ℝ E'] :
    Prop :=
  B = univ ∨ B = ∅ ∨ ∃ (f : E ≃ₗᵢ[ℝ] WithLp 2 (ℝ × E')) (β : E' → ℝ) (K : ℝ≥0),
    LipschitzWith K β ∧ B = f ⁻¹' {z | β z.snd < z.fst}

/-- An admissible base region written out as its three shapes. -/
theorem isAdmissibleBaseRegion_iff {B : Set E} :
    B.IsAdmissibleBaseRegion E' ↔ B = univ ∨ B = ∅ ∨
      ∃ (f : E ≃ₗᵢ[ℝ] WithLp 2 (ℝ × E')) (β : E' → ℝ) (K : ℝ≥0),
        LipschitzWith K β ∧ B = f ⁻¹' {z | β z.snd < z.fst} :=
  Iff.rfl

/-- The whole base is an admissible base region. -/
theorem isAdmissibleBaseRegion_univ : (univ : Set E).IsAdmissibleBaseRegion E' :=
  Or.inl rfl

/-- The empty base region is admissible. -/
theorem isAdmissibleBaseRegion_empty : (∅ : Set E).IsAdmissibleBaseRegion E' :=
  Or.inr (Or.inl rfl)

/-- The region above the graph of a Lipschitz function, after a linear isometry of the base, is
an admissible base region. -/
theorem isAdmissibleBaseRegion_preimage_setOf_lt_fst (f : E ≃ₗᵢ[ℝ] WithLp 2 (ℝ × E'))
    {β : E' → ℝ} {K : ℝ≥0} (hβ : LipschitzWith K β) :
    (f ⁻¹' {z | β z.snd < z.fst}).IsAdmissibleBaseRegion E' :=
  Or.inr (Or.inr ⟨f, β, K, hβ, rfl⟩)

namespace IsAdmissibleBaseRegion

variable {B : Set E}

/-- An admissible base region is open. -/
theorem isOpen (hB : B.IsAdmissibleBaseRegion E') : IsOpen B := by
  obtain rfl | rfl | ⟨f, β, K, hβ, rfl⟩ := hB
  · exact isOpen_univ
  · exact isOpen_empty
  · exact (isOpen_lt (hβ.continuous.comp (WithLp.sndL 2 ℝ ℝ E').continuous)
      (WithLp.fstL 2 ℝ ℝ E').continuous).preimage f.continuous

/-- Translating an admissible base region gives an admissible base region. -/
theorem preimage_add_const (hB : B.IsAdmissibleBaseRegion E') (q : E) :
    ((· + q) ⁻¹' B).IsAdmissibleBaseRegion E' := by
  obtain rfl | rfl | ⟨f, β, K, hβ, rfl⟩ := hB
  · exact isAdmissibleBaseRegion_univ
  · exact isAdmissibleBaseRegion_empty
  · -- The translated region lies above the translated graph, which is again `K`-Lipschitz.
    have hβ' : LipschitzWith K fun y => β (y + (f q).snd) - (f q).fst :=
      LipschitzWith.of_dist_le_mul fun y y' => by
        simpa using hβ.dist_le_mul (y + (f q).snd) (y' + (f q).snd)
    convert isAdmissibleBaseRegion_preimage_setOf_lt_fst f hβ' using 1
    ext y
    simp only [mem_preimage, mem_ofPred_eq, map_add, WithLp.add_fst, WithLp.add_snd]
    constructor <;> intro h <;> linarith

/-- Dilating an admissible base region by a positive factor gives an admissible base region. -/
theorem smul (hB : B.IsAdmissibleBaseRegion E') {c : ℝ} (hc : 0 < c) :
    (c • B).IsAdmissibleBaseRegion E' := by
  obtain rfl | rfl | ⟨f, β, K, hβ, rfl⟩ := hB
  · rw [smul_set_univ₀ hc.ne']
    exact isAdmissibleBaseRegion_univ
  · rw [smul_set_empty]
    exact isAdmissibleBaseRegion_empty
  · -- The dilated region lies above the dilated graph `y ↦ c * β (c⁻¹ • y)`, whose Lipschitz
    -- constant is `‖c‖₊ * K * ‖c⁻¹‖₊ = K`.
    have hK : ‖c‖₊ * K * ‖c⁻¹‖₊ = K := by
      rw [mul_comm, ← mul_assoc, ← nnNorm_mul, inv_mul_cancel₀ hc.ne', nnNorm_one, one_mul]
    have hβ' : LipschitzWith K fun y => c * β (c⁻¹ • y) := by
      simpa only [hK, Function.comp_def, smul_eq_mul] using
        ((lipschitzWith_smul c).comp hβ).comp (lipschitzWith_smul c⁻¹)
    convert isAdmissibleBaseRegion_preimage_setOf_lt_fst f hβ' using 1
    ext y
    simp only [mem_smul_set_iff_inv_smul_mem₀ hc.ne', mem_preimage, mem_ofPred_eq, map_smul,
      WithLp.smul_fst, WithLp.smul_snd, smul_eq_mul, lt_inv_mul_iff₀ hc]

end IsAdmissibleBaseRegion

/-! ### Boundary-part charts -/

/-- A **boundary-part chart** of the pair `(Ω, Γ)`: a Lipschitz boundary chart of `Ω`, with
coordinates `e`, graph `γ` and cylinder `normalCylinder h r`, in which the part of `Γ` inside the
cylinder is the part of the graph of `γ` lying over the base region `B ⊆ E`. -/
structure IsBoundaryPartChart (Ω Γ : Set F) (e : F ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E)) (γ : E → ℝ)
    (K : ℝ≥0) (h r : ℝ) (B : Set E) : Prop where
  /-- The chart is a Lipschitz boundary chart of `Ω`. -/
  isLipschitzChart : IsLipschitzChart Ω e γ K h r
  /-- Inside the cylinder, `Γ` is the part of the graph lying over `B`. -/
  image_inter_normalCylinder :
    e '' Γ ∩ normalCylinder h r = {z | z.fst = γ z.snd ∧ z.snd ∈ B} ∩ normalCylinder h r

/-- A Lipschitz chart of `Ω` is a boundary-part chart of `(Ω, Γ)` over `B` as soon as the points
of the cylinder corresponding to points of `Γ` are those of the graph over `B`. -/
theorem IsLipschitzChart.isBoundaryPartChart_of_forall_mem_iff {Ω Γ : Set F}
    {e : F ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E)} {γ : E → ℝ} {K : ℝ≥0} {h r : ℝ} {B : Set E}
    (hc : IsLipschitzChart Ω e γ K h r)
    (hmem : ∀ z ∈ normalCylinder h r, e.symm z ∈ Γ ↔ z.fst = γ z.snd ∧ z.snd ∈ B) :
    IsBoundaryPartChart Ω Γ e γ K h r B where
  isLipschitzChart := hc
  image_inter_normalCylinder := by
    ext z
    simp only [mem_inter_iff, mem_ofPred_eq]
    refine and_congr_left fun hz => ?_
    rw [← hmem z hz]
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa using hx
    · exact fun hx => ⟨_, hx, e.apply_symm_apply z⟩

/-- Every Lipschitz chart of `Ω` is a boundary-part chart of `(Ω, frontier Ω)` over the whole
base. -/
theorem IsLipschitzChart.isBoundaryPartChart_frontier {Ω : Set F}
    {e : F ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E)} {γ : E → ℝ} {K : ℝ≥0} {h r : ℝ}
    (hc : IsLipschitzChart Ω e γ K h r) :
    IsBoundaryPartChart Ω (frontier Ω) e γ K h r univ where
  isLipschitzChart := hc
  image_inter_normalCylinder := by simpa using hc.image_frontier_inter_normalCylinder

/-- Every Lipschitz chart of `Ω` is a boundary-part chart of `(Ω, ∅)` over the empty base
region. -/
theorem IsLipschitzChart.isBoundaryPartChart_empty {Ω : Set F}
    {e : F ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E)} {γ : E → ℝ} {K : ℝ≥0} {h r : ℝ}
    (hc : IsLipschitzChart Ω e γ K h r) :
    IsBoundaryPartChart Ω ∅ e γ K h r ∅ where
  isLipschitzChart := hc
  image_inter_normalCylinder := by simp

/-- A Lipschitz chart of `Ω` whose cylinder corresponds to no point of `Γ` is a boundary-part
chart of `(Ω, Γ)` over the empty base region. -/
theorem IsLipschitzChart.isBoundaryPartChart_empty_of_disjoint {Ω Γ : Set F}
    {e : F ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E)} {γ : E → ℝ} {K : ℝ≥0} {h r : ℝ}
    (hc : IsLipschitzChart Ω e γ K h r) (hΓ : Disjoint Γ (e ⁻¹' normalCylinder h r)) :
    IsBoundaryPartChart Ω Γ e γ K h r ∅ where
  isLipschitzChart := hc
  image_inter_normalCylinder := by
    have hΓC : e '' Γ ∩ normalCylinder h r = ∅ :=
      eq_empty_of_forall_notMem fun _ ⟨⟨_, hy, hyz⟩, hz⟩ =>
        disjoint_left.1 hΓ hy (by rwa [mem_preimage, hyz])
    rw [hΓC, ← hc.isBoundaryPartChart_empty.image_inter_normalCylinder, image_empty, empty_inter]

/-- A Lipschitz chart of `Ω` whose cylinder corresponds only to points of `Γ ⊆ frontier Ω` on the
frontier is a boundary-part chart of `(Ω, Γ)` over the whole base. -/
theorem IsLipschitzChart.isBoundaryPartChart_univ_of_subset {Ω Γ : Set F}
    {e : F ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E)} {γ : E → ℝ} {K : ℝ≥0} {h r : ℝ}
    (hc : IsLipschitzChart Ω e γ K h r) (hΓ : Γ ⊆ frontier Ω)
    (hsub : frontier Ω ∩ e ⁻¹' normalCylinder h r ⊆ Γ) :
    IsBoundaryPartChart Ω Γ e γ K h r univ where
  isLipschitzChart := hc
  image_inter_normalCylinder := by
    have hΓC : e '' Γ ∩ normalCylinder h r = e '' frontier Ω ∩ normalCylinder h r :=
      Subset.antisymm (inter_subset_inter_left _ (image_mono hΓ))
        fun _ ⟨⟨y, hy, hyz⟩, hz⟩ => ⟨⟨y, hsub ⟨hy, by rwa [mem_preimage, hyz]⟩, hyz⟩, hz⟩
    rw [hΓC, hc.isBoundaryPartChart_frontier.image_inter_normalCylinder]

namespace IsBoundaryPartChart

variable {Ω Γ : Set F} {e : F ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E)} {γ : E → ℝ} {K : ℝ≥0} {h r : ℝ}
  {B : Set E}

/-- A point whose image lies in the cylinder of a boundary-part chart belongs to `Γ` exactly when
its image lies on the graph over the base region. -/
theorem mem_iff (hc : IsBoundaryPartChart Ω Γ e γ K h r B) {x : F}
    (hxC : e x ∈ normalCylinder h r) : x ∈ Γ ↔ (e x).fst = γ (e x).snd ∧ (e x).snd ∈ B := by
  rw [← e.injective.mem_set_image]
  exact ⟨fun hx => (hc.image_inter_normalCylinder.subset ⟨hx, hxC⟩).1,
    fun hx => (hc.image_inter_normalCylinder.superset ⟨hx, hxC⟩).1⟩

/-- A frontier point of `Ω` whose image lies in the cylinder of a boundary-part chart belongs to
`Γ` exactly when the base coordinate of its image lies in the base region. -/
theorem mem_iff_of_mem_frontier (hc : IsBoundaryPartChart Ω Γ e γ K h r B) {x : F}
    (hx : x ∈ frontier Ω) (hxC : e x ∈ normalCylinder h r) : x ∈ Γ ↔ (e x).snd ∈ B := by
  rw [hc.mem_iff hxC, and_iff_right (hc.isLipschitzChart.fst_apply_eq_of_mem_frontier hx hxC)]

/-- Inside the cylinder of a boundary-part chart, the points of `Γ` have their images on the graph
over the base region. -/
theorem inter_preimage_normalCylinder_subset (hc : IsBoundaryPartChart Ω Γ e γ K h r B) :
    Γ ∩ e ⁻¹' normalCylinder h r ⊆ e ⁻¹' {z | z.fst = γ z.snd ∧ z.snd ∈ B} :=
  fun _ hx => (hc.mem_iff hx.2).1 hx.1

/-- Inside the cylinder of a boundary-part chart, the points of the graph over the base region are
images of points of `Γ`. -/
theorem setOf_inter_normalCylinder_subset (hc : IsBoundaryPartChart Ω Γ e γ K h r B) :
    {z | z.fst = γ z.snd ∧ z.snd ∈ B} ∩ normalCylinder h r ⊆ e.symm ⁻¹' Γ :=
  fun z hz => (hc.mem_iff (x := e.symm z) (by simpa using hz.2)).2 (by simpa using hz.1)

/-- A boundary-part chart restricts to every smaller cylinder. -/
theorem mono (hc : IsBoundaryPartChart Ω Γ e γ K h r B) {h' r' : ℝ} (hh' : 0 < h')
    (hr' : 0 < r') (hh : h' ≤ h) (hr : r' ≤ r) : IsBoundaryPartChart Ω Γ e γ K h' r' B where
  isLipschitzChart := hc.isLipschitzChart.mono hh' hr' hh hr
  image_inter_normalCylinder := by
    have hsub := normalCylinder_mono (E := E) hh hr
    rw [← inter_eq_right.2 hsub, ← inter_assoc, hc.image_inter_normalCylinder, inter_assoc]

/-- A boundary-part chart with Lipschitz constant `K` is one with every constant `K' ≥ K`. -/
theorem weaken (hc : IsBoundaryPartChart Ω Γ e γ K h r B) {K' : ℝ≥0} (hK : K ≤ K') :
    IsBoundaryPartChart Ω Γ e γ K' h r B :=
  { hc with isLipschitzChart := hc.isLipschitzChart.weaken hK }

/-- Recentring a boundary-part chart at the point `p` of the model, as in
`Set.IsLipschitzChart.trans_constVAdd`: the base region is translated along with the graph. -/
theorem trans_constVAdd (hc : IsBoundaryPartChart Ω Γ e γ K h r B) (p : WithLp 2 (ℝ × E))
    {h' r' : ℝ} (hh' : 0 < h') (hr' : 0 < r') (hh : |p.fst| + h' ≤ h) (hr : ‖p.snd‖ + r' ≤ r) :
    IsBoundaryPartChart Ω Γ (e.trans (AffineIsometryEquiv.constVAdd ℝ _ (-p)))
      (fun y => γ (y + p.snd) - p.fst) K h' r' ((· + p.snd) ⁻¹' B) := by
  refine (hc.isLipschitzChart.trans_constVAdd p hh' hr' hh hr).isBoundaryPartChart_of_forall_mem_iff
    fun w hw => ?_
  have hC := add_mem_normalCylinder hh hr hw
  have hsymm : (e.trans (AffineIsometryEquiv.constVAdd ℝ _ (-p))).symm w = e.symm (p + w) := by
    rw [AffineIsometryEquiv.symm_apply_eq]
    simp
  rw [hsymm, hc.mem_iff (by rwa [e.apply_symm_apply]), e.apply_symm_apply, mem_preimage]
  simp only [WithLp.add_fst, WithLp.add_snd, add_comm p.snd w.snd]
  constructor <;> rintro ⟨h₁, h₂⟩ <;> exact ⟨by linarith, h₂⟩

/-- A boundary-part chart can be recentred at any point of its cylinder, keeping its Lipschitz
constant; the base region is translated accordingly. -/
theorem exists_isBoundaryPartChart_eq_zero (hc : IsBoundaryPartChart Ω Γ e γ K h r B) {x : F}
    (hx : e x ∈ normalCylinder h r) :
    ∃ (e' : F ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E)) (γ' : E → ℝ) (h' r' : ℝ),
      IsBoundaryPartChart Ω Γ e' γ' K h' r' ((· + (e x).snd) ⁻¹' B) ∧ e' x = 0 := by
  have hx' : |(e x).fst| < h ∧ ‖(e x).snd‖ < r := by
    simpa only [mem_normalCylinder, abs_lt, and_assoc] using hx
  exact ⟨_, _, _, _, hc.trans_constVAdd (e x) (sub_pos.2 hx'.1) (sub_pos.2 hx'.2)
    (by linarith) (by linarith), by simp⟩

/-- Transporting a boundary-part chart along an affine isometry `g : F ≃ᵃⁱ[ℝ] G`. -/
theorem image (hc : IsBoundaryPartChart Ω Γ e γ K h r B) (g : F ≃ᵃⁱ[ℝ] G) :
    IsBoundaryPartChart (g '' Ω) (g '' Γ) (g.symm.trans e) γ K h r B where
  isLipschitzChart := hc.isLipschitzChart.image g
  image_inter_normalCylinder := by
    simpa only [image_image, AffineIsometryEquiv.coe_trans, Function.comp_apply,
      AffineIsometryEquiv.symm_apply_apply] using hc.image_inter_normalCylinder

/-- Dilating a boundary-part chart by a factor `c > 0`, as in `Set.IsLipschitzChart.smul`: the
base region is dilated along with the graph and the cylinder. -/
theorem smul (hc : IsBoundaryPartChart Ω Γ e γ K h r B) {c : ℝ} (hc0 : 0 < c) :
    IsBoundaryPartChart (c • Ω) (c • Γ) (dilateConj c e) (fun y => c * γ (c⁻¹ • y)) K (c * h)
      (c * r) (c • B) where
  isLipschitzChart := hc.isLipschitzChart.smul hc0
  image_inter_normalCylinder := by
    have himage : dilateConj c e '' (c • Γ) = c • (e '' Γ) := by
      rw [← image_smul, ← image_smul, image_image, image_image]
      simp_rw [dilateConj_smul]
    have hgraph : {z : WithLp 2 (ℝ × E) | z.fst = c * γ (c⁻¹ • z.snd) ∧ z.snd ∈ c • B} =
        c • {z : WithLp 2 (ℝ × E) | z.fst = γ z.snd ∧ z.snd ∈ B} := by
      ext z
      simp only [mem_smul_set_iff_inv_smul_mem₀ hc0.ne', mem_ofPred_eq, WithLp.smul_fst,
        WithLp.smul_snd, smul_eq_mul, inv_mul_eq_iff_eq_mul₀ hc0.ne']
    rw [himage, hgraph, ← smul_normalCylinder hc0, ← smul_set_inter₀ hc0.ne',
      ← smul_set_inter₀ hc0.ne', hc.image_inter_normalCylinder]

/-- A boundary-part chart of `(Ω, Γ')` is one of `(Ω, Γ)` whenever `Γ` and `Γ'` agree inside the
cylinder. -/
theorem of_inter_preimage_eq {Γ' : Set F} (hc : IsBoundaryPartChart Ω Γ' e γ K h r B)
    (hΓ : Γ ∩ e ⁻¹' normalCylinder h r = Γ' ∩ e ⁻¹' normalCylinder h r) :
    IsBoundaryPartChart Ω Γ e γ K h r B where
  isLipschitzChart := hc.isLipschitzChart
  image_inter_normalCylinder := by
    rw [← image_inter_preimage, hΓ, image_inter_preimage, hc.image_inter_normalCylinder]

/-- **Boundary parts along a frontier arc of a planar domain.** In a boundary-part chart with a
one-dimensional base and an interval as base region, let `c` be a continuous injective arc,
parametrized by an interval `I`, running in the frontier of `Ω` inside the cylinder. Then the
parameters at which `c` lies in `Γ` form an interval. Indeed the base coordinate of `c` is
continuous and injective on `I`, as two frontier points of the cylinder with the same base
coordinate coincide, hence strictly monotone, and `c t ∈ Γ` exactly when that coordinate lies in
the base region. -/
theorem ordConnected_inter_preimage {e : F ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × ℝ)} {γ : ℝ → ℝ} {K : ℝ≥0}
    {h r : ℝ} {B : Set ℝ} (hc : IsBoundaryPartChart Ω Γ e γ K h r B) (hB : B.OrdConnected)
    {I : Set ℝ} (hI : I.OrdConnected) {c : ℝ → F} (hcont : ContinuousOn c I) (hinj : InjOn c I)
    (hfr : MapsTo c I (frontier Ω)) (hC : MapsTo c I (e ⁻¹' normalCylinder h r)) :
    (I ∩ c ⁻¹' Γ).OrdConnected := by
  set g : ℝ → ℝ := fun t => (e (c t)).snd
  have hmem (t : ℝ) (ht : t ∈ I) : c t ∈ Γ ↔ g t ∈ B :=
    hc.mem_iff_of_mem_frontier (hfr ht) (hC ht)
  have hginj : InjOn g I := by
    intro s hs t ht hst
    have hs' := hc.isLipschitzChart.fst_apply_eq_of_mem_frontier (hfr hs) (hC hs)
    have ht' := hc.isLipschitzChart.fst_apply_eq_of_mem_frontier (hfr ht) (hC ht)
    refine hinj hs ht (e.injective ((WithLp.ext_iff 2).2 (Prod.ext ?_ ?_)))
    · simp only [WithLp.ofLp_fst]
      rw [hs', ht']
      exact congrArg γ hst
    · simpa only [WithLp.ofLp_snd] using hst
  have hgcont : ContinuousOn g I :=
    (WithLp.continuous_snd 2 ℝ ℝ).comp_continuousOn (e.continuous.comp_continuousOn hcont)
  refine ⟨fun s hs t ht u hu => ⟨hI.out hs.1 ht.1 hu, ?_⟩⟩
  have hIcc : Icc s t ⊆ I := hI.out hs.1 ht.1
  have hst : s ≤ t := hu.1.trans hu.2
  -- On `[s, t]` the base coordinate is strictly monotone or strictly antitone.
  have hgu : g u ∈ uIcc (g s) (g t) := by
    rcases (hgcont.mono hIcc).strictMonoOn_of_injOn_Icc' hst (hginj.mono hIcc) with hm | hm
    · exact Icc_subset_uIcc ⟨hm.monotoneOn (left_mem_Icc.2 hst) hu hu.1,
        hm.monotoneOn hu (right_mem_Icc.2 hst) hu.2⟩
    · exact Icc_subset_uIcc' ⟨hm.antitoneOn hu (right_mem_Icc.2 hst) hu.2,
        hm.antitoneOn (left_mem_Icc.2 hst) hu hu.1⟩
  exact (hmem u (hIcc hu)).2
    (hB.uIcc_subset ((hmem s hs.1).1 hs.2) ((hmem t ht.1).1 ht.2) hgu)

end IsBoundaryPartChart

/-- A Lipschitz chart centred at `x` gives a boundary-part chart of `(Ω, Γ)` over the empty base
region as soon as `Γ` misses a neighbourhood of `x`. -/
theorem IsLipschitzChart.exists_isBoundaryPartChart_empty {Ω Γ : Set F}
    {e : F ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E)} {γ : E → ℝ} {K : ℝ≥0} {h r : ℝ}
    (hc : IsLipschitzChart Ω e γ K h r) {x : F} (hex : e x = 0) {V : Set F} (hV : V ∈ 𝓝 x)
    (hΓV : Disjoint Γ V) : ∃ ρ : ℝ, IsBoundaryPartChart Ω Γ e γ K ρ ρ ∅ := by
  obtain ⟨ρ, hcρ, hsub⟩ := hc.exists_preimage_normalCylinder_subset hex hV
  refine ⟨ρ, hcρ.isBoundaryPartChart_empty.of_inter_preimage_eq ?_⟩
  rw [empty_inter]
  exact hΓV.mono_right hsub |>.inter_eq

/-- A Lipschitz chart centred at `x` gives a boundary-part chart of `(Ω, Γ)` over the whole base
as soon as `Γ ⊆ frontier Ω` contains the frontier near `x`. -/
theorem IsLipschitzChart.exists_isBoundaryPartChart_univ {Ω Γ : Set F}
    {e : F ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E)} {γ : E → ℝ} {K : ℝ≥0} {h r : ℝ}
    (hc : IsLipschitzChart Ω e γ K h r) {x : F} (hex : e x = 0) {V : Set F} (hV : V ∈ 𝓝 x)
    (hΓ : Γ ⊆ frontier Ω) (hΓV : frontier Ω ∩ V ⊆ Γ) :
    ∃ ρ : ℝ, IsBoundaryPartChart Ω Γ e γ K ρ ρ univ := by
  obtain ⟨ρ, hcρ, hsub⟩ := hc.exists_preimage_normalCylinder_subset hex hV
  refine ⟨ρ, hcρ.isBoundaryPartChart_frontier.of_inter_preimage_eq ?_⟩
  exact Subset.antisymm (inter_subset_inter_left _ hΓ)
    fun y hy => ⟨hΓV ⟨hy.1, hsub hy.2⟩, hy.2⟩

/-! ### Admissible boundary parts -/

/-- A set `Γ` is an **admissible boundary part** of `Ω ⊆ F`, with boundary charts modelled on
`ℝ × E` and interfaces in the base modelled on `ℝ × E'`, if it lies in the frontier of `Ω` and
every frontier point of `Ω` is the centre of a Lipschitz boundary chart of `Ω` in which `Γ` is
the part of the boundary graph lying over all of the base, over none of it, or over the region on
one side of a Lipschitz graph in the base (`Set.IsAdmissibleBaseRegion`). -/
structure IsAdmissibleBoundaryPart (Ω Γ : Set F) (E E' : Type*) [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup E'] [NormedSpace ℝ E'] : Prop where
  /-- An admissible boundary part lies in the frontier. -/
  subset_frontier : Γ ⊆ frontier Ω
  /-- Every frontier point is the centre of a boundary-part chart with admissible base. -/
  exists_isBoundaryPartChart : ∀ x ∈ frontier Ω, ∃ (e : F ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E))
    (γ : E → ℝ) (K : ℝ≥0) (h r : ℝ) (B : Set E),
    IsBoundaryPartChart Ω Γ e γ K h r B ∧ B.IsAdmissibleBaseRegion E' ∧ e x = 0

/-- A set is an admissible boundary part if and only if it lies in the frontier and every
frontier point lies in the cylinder of some boundary-part chart with admissible base, not
necessarily centred at it. -/
theorem isAdmissibleBoundaryPart_iff_exists_mem_normalCylinder {Ω Γ : Set F} :
    Ω.IsAdmissibleBoundaryPart Γ E E' ↔ Γ ⊆ frontier Ω ∧ ∀ x ∈ frontier Ω,
      ∃ (e : F ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E)) (γ : E → ℝ) (K : ℝ≥0) (h r : ℝ) (B : Set E),
        IsBoundaryPartChart Ω Γ e γ K h r B ∧ B.IsAdmissibleBaseRegion E' ∧
          e x ∈ normalCylinder h r := by
  refine ⟨fun hΓ => ⟨hΓ.subset_frontier, fun x hx => ?_⟩, fun hΓ => ⟨hΓ.1, fun x hx => ?_⟩⟩
  · obtain ⟨e, γ, K, h, r, B, hc, hB, hex⟩ := hΓ.exists_isBoundaryPartChart x hx
    exact ⟨e, γ, K, h, r, B, hc, hB, hex ▸ zero_mem_normalCylinder hc.isLipschitzChart.height_pos
      hc.isLipschitzChart.radius_pos⟩
  · obtain ⟨e, γ, K, h, r, B, hc, hB, hxC⟩ := hΓ.2 x hx
    obtain ⟨e', γ', h', r', hc', hex⟩ := hc.exists_isBoundaryPartChart_eq_zero hxC
    exact ⟨e', γ', K, h', r', _, hc', hB.preimage_add_const _, hex⟩

namespace IsAdmissibleBoundaryPart

variable {Ω Γ : Set F}

/-- A set with an admissible boundary part is a Lipschitz domain. -/
theorem isLipschitzDomain (hΓ : Ω.IsAdmissibleBoundaryPart Γ E E') : Ω.IsLipschitzDomain E := by
  refine isLipschitzDomain_iff_exists_mem_normalCylinder.2 fun x hx => ?_
  obtain ⟨e, γ, K, h, r, _, hc, _, hxC⟩ :=
    (isAdmissibleBoundaryPart_iff_exists_mem_normalCylinder.1 hΓ).2 x hx
  exact ⟨e, γ, K, h, r, hc.isLipschitzChart, hxC⟩

/-- **An admissible boundary part is relatively open in the frontier.** -/
theorem exists_isOpen_frontier_inter_eq (hΓ : Ω.IsAdmissibleBoundaryPart Γ E E') :
    ∃ U : Set F, IsOpen U ∧ frontier Ω ∩ U = Γ := by
  choose e γ K h r B hc hB hex using
    fun x : Γ => hΓ.exists_isBoundaryPartChart x (hΓ.subset_frontier x.property)
  refine ⟨⋃ x : Γ, e x ⁻¹' (normalCylinder (h x) (r x) ∩ WithLp.snd ⁻¹' B x),
    isOpen_iUnion fun x => ((isOpen_normalCylinder _ _).inter ((hB x).isOpen.preimage
      (WithLp.sndL 2 ℝ ℝ E).continuous)).preimage (e x).continuous, ?_⟩
  ext y
  simp only [mem_inter_iff, mem_iUnion, mem_preimage]
  constructor
  · rintro ⟨hy, x, hyC, hyB⟩
    exact ((hc x).mem_iff_of_mem_frontier hy hyC).2 hyB
  · intro hy
    have hyC : e ⟨y, hy⟩ y ∈ normalCylinder (h ⟨y, hy⟩) (r ⟨y, hy⟩) := hex ⟨y, hy⟩ ▸
      zero_mem_normalCylinder (hc ⟨y, hy⟩).isLipschitzChart.height_pos
        (hc ⟨y, hy⟩).isLipschitzChart.radius_pos
    exact ⟨hΓ.subset_frontier hy, ⟨y, hy⟩, hyC,
      ((hc ⟨y, hy⟩).mem_iff_of_mem_frontier (hΓ.subset_frontier hy) hyC).1 hy⟩

/-- The image of an admissible boundary part under an affine isometry is an admissible boundary
part of the image. -/
theorem image (hΓ : Ω.IsAdmissibleBoundaryPart Γ E E') (g : F ≃ᵃⁱ[ℝ] G) :
    (g '' Ω).IsAdmissibleBoundaryPart (g '' Γ) E E' where
  subset_frontier := by
    rw [← g.image_frontier]
    exact image_mono hΓ.subset_frontier
  exists_isBoundaryPartChart y hy := by
    rw [← g.image_frontier] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    obtain ⟨e, γ, K, h, r, B, hc, hB, hex⟩ := hΓ.exists_isBoundaryPartChart x hx
    exact ⟨g.symm.trans e, γ, K, h, r, B, hc.image g, hB, by simpa using hex⟩

/-- The dilation of an admissible boundary part by a factor `c > 0` is an admissible boundary
part of the dilated set. -/
theorem smul (hΓ : Ω.IsAdmissibleBoundaryPart Γ E E') {c : ℝ} (hc : 0 < c) :
    (c • Ω).IsAdmissibleBoundaryPart (c • Γ) E E' where
  subset_frontier := by
    rw [frontier_smul₀ hc.ne']
    exact smul_set_mono hΓ.subset_frontier
  exists_isBoundaryPartChart y hy := by
    rw [frontier_smul₀ hc.ne', ← image_smul] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    obtain ⟨e, γ, K, h, r, B, hce, hB, hex⟩ := hΓ.exists_isBoundaryPartChart x hx
    exact ⟨dilateConj c e, _, K, _, _, _, hce.smul hc, hB.smul hc, by simp [hex]⟩

end IsAdmissibleBoundaryPart

/-- Being an admissible boundary part is invariant under affine isometries of the pair. -/
@[simp]
theorem isAdmissibleBoundaryPart_image_iff {Ω Γ : Set F} (g : F ≃ᵃⁱ[ℝ] G) :
    (g '' Ω).IsAdmissibleBoundaryPart (g '' Γ) E E' ↔ Ω.IsAdmissibleBoundaryPart Γ E E' :=
  ⟨fun hΓ => by simpa [image_image] using hΓ.image g.symm, fun hΓ => hΓ.image g⟩

/-- Being an admissible boundary part is invariant under positive dilations of the pair. -/
@[simp]
theorem isAdmissibleBoundaryPart_smul_iff {Ω Γ : Set F} {c : ℝ} (hc : 0 < c) :
    (c • Ω).IsAdmissibleBoundaryPart (c • Γ) E E' ↔ Ω.IsAdmissibleBoundaryPart Γ E E' :=
  ⟨fun hΓ => by simpa [smul_smul, hc.ne'] using hΓ.smul (inv_pos.2 hc), fun hΓ => hΓ.smul hc⟩

namespace IsLipschitzDomain

variable {Ω : Set F}

/-- The empty set is an admissible boundary part of every Lipschitz domain. -/
theorem isAdmissibleBoundaryPart_empty (hΩ : Ω.IsLipschitzDomain E) :
    Ω.IsAdmissibleBoundaryPart ∅ E E' := by
  refine isAdmissibleBoundaryPart_iff_exists_mem_normalCylinder.2 ⟨empty_subset _, fun x hx => ?_⟩
  obtain ⟨e, γ, K, h, r, hc, hxC⟩ := isLipschitzDomain_iff_exists_mem_normalCylinder.1 hΩ x hx
  exact ⟨e, γ, K, h, r, ∅, hc.isBoundaryPartChart_empty, isAdmissibleBaseRegion_empty, hxC⟩

/-- **Admissibility needs checking only on the relative boundary of `Γ`.** Let `Γ` be relatively
open in the frontier of a Lipschitz domain `Ω`. A chart centred at a point of `Γ` can be shrunk to
meet the frontier only in `Γ`, and one centred at a point outside `closure Γ` to miss `Γ`, so `Γ`
is an admissible boundary part as soon as every point of `closure Γ \ Γ` is the centre of a
boundary-part chart with admissible base. -/
theorem isAdmissibleBoundaryPart_of_frontier_inter_eq (hΩ : Ω.IsLipschitzDomain E) {Γ U : Set F}
    (hU : IsOpen U) (hΓ : frontier Ω ∩ U = Γ)
    (hcl : ∀ x ∈ closure Γ \ Γ, ∃ (e : F ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E)) (γ : E → ℝ) (K : ℝ≥0)
      (h r : ℝ) (B : Set E), IsBoundaryPartChart Ω Γ e γ K h r B ∧
        B.IsAdmissibleBaseRegion E' ∧ e x = 0) :
    Ω.IsAdmissibleBoundaryPart Γ E E' := by
  have hsub : Γ ⊆ frontier Ω := hΓ ▸ inter_subset_left
  refine ⟨hsub, fun x hx => ?_⟩
  obtain ⟨e₀, γ, K, h₀, r₀, hc₀, hxC⟩ := isLipschitzDomain_iff_exists_mem_normalCylinder.1 hΩ x hx
  obtain ⟨e, γ, h, r, hc, hex⟩ := hc₀.exists_isLipschitzChart_eq_zero hxC
  by_cases hxΓ : x ∈ Γ
  · rw [← hΓ] at hxΓ
    obtain ⟨ρ, hc', hU'⟩ := hc.exists_preimage_normalCylinder_subset hex (hU.mem_nhds hxΓ.2)
    refine ⟨e, γ, K, ρ, ρ, univ, hc'.isBoundaryPartChart_univ_of_subset hsub fun y hy => ?_,
      isAdmissibleBaseRegion_univ, hex⟩
    exact hΓ ▸ ⟨hy.1, hU' hy.2⟩
  by_cases hxc : x ∈ closure Γ
  · exact hcl x ⟨hxc, hxΓ⟩
  obtain ⟨ρ, hc', hU'⟩ := hc.exists_preimage_normalCylinder_subset hex
    (isClosed_closure.isOpen_compl.mem_nhds hxc)
  exact ⟨e, γ, K, ρ, ρ, ∅, hc'.isBoundaryPartChart_empty_of_disjoint
    (disjoint_left.2 fun _ hy hyC => hU' hyC (subset_closure hy)), isAdmissibleBaseRegion_empty,
    hex⟩

/-- The whole frontier is an admissible boundary part of every Lipschitz domain. -/
theorem isAdmissibleBoundaryPart_frontier (hΩ : Ω.IsLipschitzDomain E) :
    Ω.IsAdmissibleBoundaryPart (frontier Ω) E E' := by
  refine isAdmissibleBoundaryPart_iff_exists_mem_normalCylinder.2 ⟨subset_rfl, fun x hx => ?_⟩
  obtain ⟨e, γ, K, h, r, hc, hxC⟩ := isLipschitzDomain_iff_exists_mem_normalCylinder.1 hΩ x hx
  exact ⟨e, γ, K, h, r, univ, hc.isBoundaryPartChart_frontier, isAdmissibleBaseRegion_univ, hxC⟩

end IsLipschitzDomain

/-- The empty set is an admissible boundary part of `Ω` exactly when `Ω` is a Lipschitz
domain. -/
@[simp]
theorem isAdmissibleBoundaryPart_empty_iff {Ω : Set F} :
    Ω.IsAdmissibleBoundaryPart ∅ E E' ↔ Ω.IsLipschitzDomain E :=
  ⟨IsAdmissibleBoundaryPart.isLipschitzDomain, IsLipschitzDomain.isAdmissibleBoundaryPart_empty⟩

/-- The whole frontier is an admissible boundary part of `Ω` exactly when `Ω` is a Lipschitz
domain. -/
@[simp]
theorem isAdmissibleBoundaryPart_frontier_iff {Ω : Set F} :
    Ω.IsAdmissibleBoundaryPart (frontier Ω) E E' ↔ Ω.IsLipschitzDomain E :=
  ⟨IsAdmissibleBoundaryPart.isLipschitzDomain,
    IsLipschitzDomain.isAdmissibleBoundaryPart_frontier⟩

/-! ### The region above a Lipschitz graph -/

/-- **Boundary parts of the region above a Lipschitz graph.** The part of the graph of a
Lipschitz `γ : E → ℝ` lying over an admissible base region `B` is an admissible boundary part of
the region strictly above the graph. For `γ = 0` and `B` a half-space of `E` this is the model
half-hyperplane of the mixed problem on a half-space. -/
theorem isAdmissibleBoundaryPart_setOf_lt_fst {γ : E → ℝ} {K : ℝ≥0} (hγ : LipschitzWith K γ)
    {B : Set E} (hB : B.IsAdmissibleBaseRegion E') :
    {x : WithLp 2 (ℝ × E) | γ x.snd < x.fst}.IsAdmissibleBoundaryPart
      {x | x.fst = γ x.snd ∧ x.snd ∈ B} E E' := by
  rw [isAdmissibleBoundaryPart_iff_exists_mem_normalCylinder,
    frontier_setOf_lt_fst hγ.continuous]
  refine ⟨fun x hx => hx.1, fun x _ => ⟨_, γ, K, |x.fst| + 1, ‖x.snd‖ + 1, B,
    (isLipschitzChart_refl_setOf_lt_fst hγ (by positivity)
      (by positivity)).isBoundaryPartChart_of_forall_mem_iff
      -- The inverse of the affine identity reduces definitionally to the identity, so both sides
      -- of the membership condition agree.
      fun z _ => Iff.rfl, hB,
    by simpa only [AffineIsometryEquiv.coe_refl, id_eq] using mem_normalCylinder_abs_add_one x⟩⟩

/-- **The model half-hyperplane.** In the half-space `{0 < t}` of `ℝ × (ℝ × E')`, the half of the
boundary hyperplane where the next coordinate is positive is an admissible boundary part. -/
theorem isAdmissibleBoundaryPart_normalHalfSpace :
    IsAdmissibleBoundaryPart (normalHalfSpace (E := WithLp 2 (ℝ × E')) 0 : Set _)
      {x : WithLp 2 (ℝ × WithLp 2 (ℝ × E')) | x.fst = 0 ∧ 0 < x.snd.fst}
      (WithLp 2 (ℝ × E')) E' := by
  convert isAdmissibleBoundaryPart_setOf_lt_fst (LipschitzWith.const (0 : ℝ))
    (isAdmissibleBaseRegion_preimage_setOf_lt_fst (LinearIsometryEquiv.refl ℝ (WithLp 2 (ℝ × E')))
      (LipschitzWith.const (0 : ℝ))) using 1 <;> ext <;> simp

/-! ### One-dimensional bases -/

/-- **Admissible base regions on a line are order-connected.** For a one-dimensional base `ℝ`,
every admissible base region is order-connected. -/
theorem IsAdmissibleBaseRegion.ordConnected {B : Set ℝ} (hB : B.IsAdmissibleBaseRegion E') :
    B.OrdConnected := by
  obtain rfl | rfl | ⟨f, β, K, -, rfl⟩ := hB
  · exact ordConnected_univ
  · exact ordConnected_empty
  have hf (s : ℝ) : f s = s • f 1 := by rw [← map_smul, smul_eq_mul, mul_one]
  have hfst (s : ℝ) : (f s).fst = s * (f 1).fst := by rw [hf, WithLp.smul_fst, smul_eq_mul]
  -- A linear isometry `ℝ ≃ₗᵢ[ℝ] WithLp 2 (ℝ × E')` forces `E'` to be zero, so the region above a
  -- graph over `E'` is the set where a nonzero multiple of the coordinate exceeds a constant.
  -- The first coordinate of `f 1` is nonzero, since `f` reaches `(1, 0)`.
  have ha : (f 1).fst ≠ 0 := fun ha => by
    obtain ⟨s, hs⟩ := f.surjective (WithLp.toLp 2 (1, 0))
    have := congrArg WithLp.fst hs
    rw [hfst, ha, mul_zero] at this
    simp at this
  -- The second coordinate of every `f s` vanishes, since `f` reaches `(0, (f s).snd)`.
  have hsnd (s : ℝ) : (f s).snd = 0 := by
    obtain ⟨u, hu⟩ := f.surjective (WithLp.toLp 2 (0, (f 1).snd))
    have h1 : u * (f 1).fst = 0 := by
      rw [← hfst, hu, WithLp.toLp_fst]
    have h2 : u • (f 1).snd = (f 1).snd := by
      rw [← WithLp.smul_snd, ← hf, hu, WithLp.toLp_snd]
    rw [(mul_eq_zero.1 h1).resolve_right ha, zero_smul] at h2
    rw [hf, WithLp.smul_snd, ← h2, smul_zero]
  refine ⟨fun x hx y hy t ht => ?_⟩
  rw [mem_preimage, mem_ofPred_eq, hfst, hsnd] at hx hy ⊢
  rcases ha.lt_or_gt with ha | ha <;> nlinarith [ht.1, ht.2]

/-- Conversely, the open half-line `(c, ∞)` is an admissible base region, with interfaces modelled
on a zero space: it is the region above the constant `c` after `s ↦ (s, 0)`. -/
theorem isAdmissibleBaseRegion_Ioi [Subsingleton E'] (c : ℝ) :
    (Ioi c).IsAdmissibleBaseRegion E' := by
  have : Unique E' := uniqueOfSubsingleton 0
  convert isAdmissibleBaseRegion_preimage_setOf_lt_fst
    (LinearIsometryEquiv.withLpProdUnique 2 ℝ ℝ E').symm (LipschitzWith.const (α := E') c) using 1
  ext s
  simp

/-- The open half-line `(-∞, c)` is an admissible base region, with interfaces modelled on a zero
space: it is the region above the constant `-c` after `s ↦ (-s, 0)`. -/
theorem isAdmissibleBaseRegion_Iio [Subsingleton E'] (c : ℝ) :
    (Iio c).IsAdmissibleBaseRegion E' := by
  have : Unique E' := uniqueOfSubsingleton 0
  convert isAdmissibleBaseRegion_preimage_setOf_lt_fst
    ((LinearIsometryEquiv.neg ℝ).trans (LinearIsometryEquiv.withLpProdUnique 2 ℝ ℝ E').symm)
    (LipschitzWith.const (α := E') (-c)) using 1
  ext s
  simp

/-- **Along a frontier path, an admissible boundary part of a planar chart is order-connected.**
If the boundary charts have a one-dimensional base, then every frontier point `x` has a
neighbourhood `U` such that for every continuous injective path `c` on `[a, b]` running through
`frontier Ω ∩ U`, the parameters `t` with `c t ∈ Γ` form an order-connected set: if both ends
lie in `Γ`, so does every point between. -/
theorem IsAdmissibleBoundaryPart.exists_mem_nhds_forall_mem_of_mapsTo {Ω Γ : Set F}
    (hΓ : Ω.IsAdmissibleBoundaryPart Γ ℝ E') {x : F} (hx : x ∈ frontier Ω) :
    ∃ U ∈ 𝓝 x, ∀ (c : ℝ → F) {a b : ℝ}, a ≤ b → ContinuousOn c (Icc a b) →
      InjOn c (Icc a b) → MapsTo c (Icc a b) (frontier Ω ∩ U) → c a ∈ Γ → c b ∈ Γ →
        ∀ t ∈ Icc a b, c t ∈ Γ := by
  obtain ⟨e, γ, K, h, r, B, hc, hB, hex⟩ := hΓ.exists_isBoundaryPartChart x hx
  have hC := hc.isLipschitzChart
  refine ⟨e ⁻¹' normalCylinder h r, ((isOpen_normalCylinder h r).preimage e.continuous).mem_nhds
    (by rw [mem_preimage, hex]; exact zero_mem_normalCylinder hC.height_pos hC.radius_pos),
    fun c a b hab hcc hci hcm hca hcb t ht => ?_⟩
  -- In the chart, the base coordinate along `c` is continuous and injective, hence monotone, and
  -- the base region is order-connected.
  set φ : ℝ → ℝ := fun t => (e (c t)).snd
  have hφc : ContinuousOn φ (Icc a b) :=
    (WithLp.sndL 2 ℝ ℝ ℝ).continuous.comp_continuousOn (e.continuous.comp_continuousOn hcc)
  -- Two frontier points of the cylinder with the same base coordinate are equal.
  have hφi : InjOn φ (Icc a b) := fun s hs u hu hsu => by
    refine hci hs hu (e.injective (WithLp.ofLp_injective 2 (Prod.ext ?_ hsu)))
    rw [WithLp.ofLp_fst, WithLp.ofLp_fst, hC.fst_apply_eq_of_mem_frontier (hcm hs).1 (hcm hs).2,
      hC.fst_apply_eq_of_mem_frontier (hcm hu).1 (hcm hu).2]
    exact congrArg γ hsu
  have hmem (u : ℝ) (hu : u ∈ Icc a b) : c u ∈ Γ ↔ φ u ∈ B :=
    hc.mem_iff_of_mem_frontier (hcm hu).1 (hcm hu).2
  have ha := left_mem_Icc.2 hab
  have hb := right_mem_Icc.2 hab
  rw [hmem t ht]
  rcases hφc.strictMonoOn_of_injOn_Icc' hab hφi with hm | hm
  · exact hB.ordConnected.out ((hmem a ha).1 hca) ((hmem b hb).1 hcb)
      ⟨hm.monotoneOn ha ht ht.1, hm.monotoneOn ht hb ht.2⟩
  · exact hB.ordConnected.out ((hmem b hb).1 hcb) ((hmem a ha).1 hca)
      ⟨hm.antitoneOn ht hb ht.2, hm.antitoneOn ha ht ht.1⟩

end Set
