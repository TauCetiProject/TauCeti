/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.LipschitzDomain.Basic

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
  (`Set.IsBoundaryPartChart.image`) and positive dilation (`Set.IsBoundaryPartChart.smul`).
* `Set.IsAdmissibleBoundaryPart`: `Γ ⊆ frontier Ω` and every frontier point is the centre of a
  boundary-part chart with an admissible base region.
* `Set.isAdmissibleBoundaryPart_iff_exists_mem_normalCylinder`: the charts need not be centred.
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

open Metric TauCeti
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

end IsBoundaryPartChart

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
      fun z _ => Iff.rfl, hB, mem_normalCylinder_abs_add_one x⟩⟩

/-- **The model half-hyperplane.** In the half-space `{0 < t}` of `ℝ × (ℝ × E')`, the half of the
boundary hyperplane where the next coordinate is positive is an admissible boundary part. -/
theorem isAdmissibleBoundaryPart_normalHalfSpace :
    IsAdmissibleBoundaryPart (normalHalfSpace (E := WithLp 2 (ℝ × E')) 0 : Set _)
      {x : WithLp 2 (ℝ × WithLp 2 (ℝ × E')) | x.fst = 0 ∧ 0 < x.snd.fst}
      (WithLp 2 (ℝ × E')) E' := by
  convert isAdmissibleBoundaryPart_setOf_lt_fst (LipschitzWith.const (0 : ℝ))
    (isAdmissibleBaseRegion_preimage_setOf_lt_fst (LinearIsometryEquiv.refl ℝ (WithLp 2 (ℝ × E')))
      (LipschitzWith.const (0 : ℝ))) using 1 <;> ext <;> simp

end Set
