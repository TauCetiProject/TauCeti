/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Affine.Isometry
public import Mathlib.Analysis.Normed.Lp.ProdLp
public import Mathlib.Topology.MetricSpace.Lipschitz
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Domains with Lipschitz boundary

This file defines the local graph condition for a Lipschitz domain in a Euclidean product
`WithLp 2 (ℝ × E)`. A Lipschitz boundary chart is a rigid change of coordinates identifying the
domain inside a product cylinder with the region above the graph of a Lipschitz function. The
graph passes through the centre of the chart, so the normal and tangential radii can be reduced
without changing the coordinates or the graph.

The global predicate `Set.IsLipschitzDomainWith` requires a chart centred at every frontier point,
with a single Lipschitz bound for all local graphs. It is invariant under affine isometries and
positive dilations, and on a compact part of the frontier finitely many charts suffice. These are
the geometric hypotheses used to transport Sobolev trace and extension operators from a flat
half-space through boundary charts and to patch them with a partition of unity.

## Main declarations

* `TauCeti.normalCylinder`: the product cylinder used by boundary charts.
* `Set.IsLipschitzChartWith`: a Lipschitz boundary chart with given coordinates, graph and radii.
* `Set.IsLipschitzDomainAtWith`: the existence of a Lipschitz boundary chart centred at one point.
* `Set.IsLipschitzDomainWith`: an open set with the local graph condition at every frontier point.
* `Set.IsLipschitzChartWith.mono_radii`: restriction of a chart to a smaller cylinder.
* `Set.IsLipschitzDomainWith.smul`: positive dilations preserve Lipschitz domains and constants.
* `Set.IsLipschitzDomainWith.exists_finset_isLipschitzChartWith_cover`: the frontier of a bounded
  Lipschitz domain is covered by finitely many chart cylinders with a common Lipschitz constant.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., §5.5.
* W. McLean, *Strongly Elliptic Systems and Boundary Integral Equations*, §3.1.
-/

public section

noncomputable section

namespace TauCeti

open Metric Set
open scoped NNReal Pointwise

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The open product cylinder of normal radius `a` and tangential radius `b`, centred at the
origin of `WithLp 2 (ℝ × E)`. -/
def normalCylinder (a b : ℝ) : Set (WithLp 2 (ℝ × E)) :=
  {x | x.fst ∈ Ioo (-a) a ∧ x.snd ∈ ball 0 b}

omit [NormedSpace ℝ E] in
/-- Membership in the normal product cylinder, in terms of its two coordinates. -/
@[simp]
theorem mem_normalCylinder {a b : ℝ} {x : WithLp 2 (ℝ × E)} :
    x ∈ normalCylinder a b ↔ -a < x.fst ∧ x.fst < a ∧ ‖x.snd‖ < b := by
  simp [normalCylinder, and_assoc]

omit [NormedSpace ℝ E] in
/-- A normal product cylinder is open. -/
theorem isOpen_normalCylinder (a b : ℝ) : IsOpen (normalCylinder (E := E) a b) := by
  exact (isOpen_Ioo.preimage (WithLp.prod_continuous_ofLp 2 ℝ E).fst).inter
    (isOpen_ball.preimage (WithLp.prod_continuous_ofLp 2 ℝ E).snd)

omit [NormedSpace ℝ E] in
/-- Shrinking either radius shrinks the normal product cylinder. -/
theorem normalCylinder_mono {a b a' b' : ℝ} (ha : a' ≤ a) (hb : b' ≤ b) :
    normalCylinder (E := E) a' b' ⊆ normalCylinder a b := by
  intro x hx
  simp only [mem_normalCylinder] at hx ⊢
  exact ⟨lt_of_le_of_lt (neg_le_neg ha) hx.1, hx.2.1.trans_le ha, hx.2.2.trans_le hb⟩

omit [NormedSpace ℝ E] in
/-- A normal product cylinder with positive radii contains its centre. -/
theorem zero_mem_normalCylinder {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (0 : WithLp 2 (ℝ × E)) ∈ normalCylinder a b := by
  simp [ha, hb]

/-- Dilating a normal product cylinder by `c > 0` multiplies both radii by `c`. -/
theorem smul_normalCylinder {c : ℝ} (hc : 0 < c) (a b : ℝ) :
    c • normalCylinder (E := E) a b = normalCylinder (c * a) (c * b) := by
  ext z
  rw [mem_smul_set_iff_inv_smul_mem₀ hc.ne']
  simp only [mem_normalCylinder, WithLp.smul_fst, WithLp.smul_snd, smul_eq_mul, norm_smul,
    norm_inv, Real.norm_eq_abs, abs_of_pos hc, inv_mul_lt_iff₀ hc, lt_inv_mul_iff₀ hc, mul_neg]

end TauCeti

namespace Set

open Metric Filter TauCeti Topology
open scoped NNReal Pointwise

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- `Omega.IsLipschitzChartWith L e φ a b` says that the rigid coordinates `e` identify `Omega`
inside the open product cylinder `normalCylinder a b` with the strict epigraph of `φ`, where `φ`
satisfies `LipschitzWith L φ` and `φ 0 = 0`. The centre `e.symm 0` of the chart therefore lies on
the graph.

The two independently positive cylinder radii retain the product geometry needed for boundary
charts and permit either the normal or tangential direction to be shrunk later. -/
def IsLipschitzChartWith (Omega : Set (WithLp 2 (ℝ × E))) (L : ℝ≥0)
    (e : WithLp 2 (ℝ × E) ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E)) (φ : E → ℝ) (a b : ℝ) : Prop :=
  0 < a ∧ 0 < b ∧ φ 0 = 0 ∧ LipschitzWith L φ ∧
    ∀ z ∈ normalCylinder a b, (e.symm z ∈ Omega ↔ φ z.snd < z.fst)

/-- A Lipschitz boundary chart written out as a rigid-coordinate graph condition. -/
theorem isLipschitzChartWith_iff (Omega : Set (WithLp 2 (ℝ × E))) (L : ℝ≥0)
    (e : WithLp 2 (ℝ × E) ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E)) (φ : E → ℝ) (a b : ℝ) :
    Omega.IsLipschitzChartWith L e φ a b ↔
      0 < a ∧ 0 < b ∧ φ 0 = 0 ∧ LipschitzWith L φ ∧
        ∀ z ∈ normalCylinder a b, (e.symm z ∈ Omega ↔ φ z.snd < z.fst) :=
  Iff.rfl

/-- A set is a Lipschitz domain at `x`, with graph constant at most `L`, if it has a Lipschitz
boundary chart whose rigid coordinates take `x` to the origin. -/
def IsLipschitzDomainAtWith (Omega : Set (WithLp 2 (ℝ × E))) (L : ℝ≥0)
    (x : WithLp 2 (ℝ × E)) : Prop :=
  ∃ (e : WithLp 2 (ℝ × E) ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E)) (φ : E → ℝ) (a b : ℝ),
    e x = 0 ∧ Omega.IsLipschitzChartWith L e φ a b

/-- The local Lipschitz-domain predicate is the existence of a chart centred at the point. -/
theorem isLipschitzDomainAtWith_iff (Omega : Set (WithLp 2 (ℝ × E))) (L : ℝ≥0)
    (x : WithLp 2 (ℝ × E)) :
    Omega.IsLipschitzDomainAtWith L x ↔
      ∃ (e : WithLp 2 (ℝ × E) ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E)) (φ : E → ℝ) (a b : ℝ),
        e x = 0 ∧ Omega.IsLipschitzChartWith L e φ a b :=
  Iff.rfl

/-- An open set is a Lipschitz domain with constant `L` if it has a Lipschitz graph chart with
that bound at every point of its frontier. -/
def IsLipschitzDomainWith (Omega : Set (WithLp 2 (ℝ × E))) (L : ℝ≥0) : Prop :=
  IsOpen Omega ∧ ∀ x ∈ frontier Omega, Omega.IsLipschitzDomainAtWith L x

/-- A set is a Lipschitz domain with constant `L` exactly when it is open and has a local
`L`-Lipschitz graph chart at every frontier point. -/
theorem isLipschitzDomainWith_iff (Omega : Set (WithLp 2 (ℝ × E))) (L : ℝ≥0) :
    Omega.IsLipschitzDomainWith L ↔
      IsOpen Omega ∧ ∀ x ∈ frontier Omega, Omega.IsLipschitzDomainAtWith L x :=
  Iff.rfl

section Chart

variable {Omega : Set (WithLp 2 (ℝ × E))} {L : ℝ≥0}
  {e : WithLp 2 (ℝ × E) ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E)} {φ : E → ℝ} {a b : ℝ}

/-- A Lipschitz boundary chart remains valid after increasing the allowed Lipschitz constant. -/
theorem IsLipschitzChartWith.weaken (h : Omega.IsLipschitzChartWith L e φ a b) {L' : ℝ≥0}
    (hLL' : L ≤ L') : Omega.IsLipschitzChartWith L' e φ a b :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1.weaken hLL', h.2.2.2.2⟩

/-- **Restriction of a chart.** A Lipschitz boundary chart remains valid on every smaller
cylinder with positive radii, with the same coordinates and graph. -/
theorem IsLipschitzChartWith.mono_radii (h : Omega.IsLipschitzChartWith L e φ a b)
    {a' b' : ℝ} (ha' : 0 < a') (hb' : 0 < b') (haa' : a' ≤ a) (hbb' : b' ≤ b) :
    Omega.IsLipschitzChartWith L e φ a' b' :=
  ⟨ha', hb', h.2.2.1, h.2.2.2.1, fun z hz ↦ h.2.2.2.2 z (normalCylinder_mono haa' hbb' hz)⟩

/-- The preimage of the chart cylinder is a neighbourhood of the centre of the chart. -/
theorem IsLipschitzChartWith.preimage_normalCylinder_mem_nhds
    (h : Omega.IsLipschitzChartWith L e φ a b) {x : WithLp 2 (ℝ × E)} (hx : e x = 0) :
    e ⁻¹' normalCylinder a b ∈ 𝓝 x :=
  ((isOpen_normalCylinder a b).preimage e.continuous).mem_nhds
    (by simpa [hx] using zero_mem_normalCylinder (E := E) h.1 h.2.1)

/-- **Rigid-coordinate transport of a chart.** Composing the coordinates of a chart with the
inverse of an affine isometry `g` gives a chart for the image of the set under `g`. -/
theorem IsLipschitzChartWith.image_affineIsometryEquiv
    (h : Omega.IsLipschitzChartWith L e φ a b) (g : WithLp 2 (ℝ × E) ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E)) :
    (g '' Omega).IsLipschitzChartWith L (g.symm.trans e) φ a b := by
  refine ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, fun z hz ↦ ?_⟩
  have hchart : (g.symm.trans e).symm z = g (e.symm z) := by
    simpa only [Function.comp_apply, AffineIsometryEquiv.symm_symm] using
      congrFun (AffineIsometryEquiv.coe_symm_trans g.symm e) z
  rw [hchart, g.injective.mem_set_image]
  exact h.2.2.2.2 z hz

end Chart

/-- A local Lipschitz-domain chart remains valid after increasing the allowed Lipschitz
constant. -/
theorem IsLipschitzDomainAtWith.mono {Omega : Set (WithLp 2 (ℝ × E))} {L L' : ℝ≥0}
    {x : WithLp 2 (ℝ × E)} (h : Omega.IsLipschitzDomainAtWith L x) (hLL' : L ≤ L') :
    Omega.IsLipschitzDomainAtWith L' x := by
  obtain ⟨e, φ, a, b, hex, hchart⟩ := h
  exact ⟨e, φ, a, b, hex, hchart.weaken hLL'⟩

/-- A Lipschitz domain remains one after increasing the allowed Lipschitz constant. -/
theorem IsLipschitzDomainWith.mono {Omega : Set (WithLp 2 (ℝ × E))} {L L' : ℝ≥0}
    (h : Omega.IsLipschitzDomainWith L) (hLL' : L ≤ L') :
    Omega.IsLipschitzDomainWith L' :=
  ⟨h.1, fun x hx ↦ (h.2 x hx).mono hLL'⟩

/-- Transport a local Lipschitz-domain chart by an affine isometry. -/
theorem IsLipschitzDomainAtWith.image_affineIsometryEquiv
    {Omega : Set (WithLp 2 (ℝ × E))} {L : ℝ≥0} {x : WithLp 2 (ℝ × E)}
    (h : Omega.IsLipschitzDomainAtWith L x)
    (g : WithLp 2 (ℝ × E) ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E)) :
    (g '' Omega).IsLipschitzDomainAtWith L (g x) := by
  obtain ⟨e, φ, a, b, hex, hchart⟩ := h
  exact ⟨g.symm.trans e, φ, a, b, by simp [hex], hchart.image_affineIsometryEquiv g⟩

/-- The local Lipschitz-domain condition is invariant under an affine isometry. -/
theorem isLipschitzDomainAtWith_image_affineIsometryEquiv_iff
    {Omega : Set (WithLp 2 (ℝ × E))} {L : ℝ≥0} {x : WithLp 2 (ℝ × E)}
    (g : WithLp 2 (ℝ × E) ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E)) :
    (g '' Omega).IsLipschitzDomainAtWith L (g x) ↔ Omega.IsLipschitzDomainAtWith L x := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.image_affineIsometryEquiv g⟩
  have himage : g.symm '' g '' Omega = Omega :=
    g.toContinuousAffineEquiv.symm_image_image Omega
  simpa only [himage, AffineIsometryEquiv.symm_apply_apply] using
    h.image_affineIsometryEquiv g.symm

/-- Affine isometries preserve Lipschitz domains and their Lipschitz constant. -/
theorem IsLipschitzDomainWith.image_affineIsometryEquiv
    {Omega : Set (WithLp 2 (ℝ × E))} {L : ℝ≥0} (h : Omega.IsLipschitzDomainWith L)
    (g : WithLp 2 (ℝ × E) ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E)) :
    (g '' Omega).IsLipschitzDomainWith L := by
  refine ⟨g.toHomeomorph.isOpenMap _ h.1, fun y hy ↦ ?_⟩
  have hfrontier : g '' frontier Omega = frontier (g '' Omega) := by
    exact g.toHomeomorph.image_frontier Omega
  rw [← hfrontier] at hy
  obtain ⟨x, hx, rfl⟩ := hy
  exact (h.2 x hx).image_affineIsometryEquiv g

/-- Being a Lipschitz domain with a fixed constant is invariant under affine isometries. -/
theorem isLipschitzDomainWith_image_affineIsometryEquiv_iff
    {Omega : Set (WithLp 2 (ℝ × E))} {L : ℝ≥0}
    (g : WithLp 2 (ℝ × E) ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E)) :
    (g '' Omega).IsLipschitzDomainWith L ↔ Omega.IsLipschitzDomainWith L := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.image_affineIsometryEquiv g⟩
  have himage : g.symm '' g '' Omega = Omega :=
    g.toContinuousAffineEquiv.symm_image_image Omega
  simpa only [himage] using h.image_affineIsometryEquiv g.symm

section Dilation

/-- **Positive dilation of a chart.** If `Omega` is a Lipschitz domain at `x`, then `c • Omega`
is a Lipschitz domain at `c • x` for every `c > 0`, with the same Lipschitz constant: the graph
`φ` becomes `y ↦ c * φ (c⁻¹ • y)` and both cylinder radii are multiplied by `c`. -/
theorem IsLipschitzDomainAtWith.smul {Omega : Set (WithLp 2 (ℝ × E))} {L : ℝ≥0}
    {x : WithLp 2 (ℝ × E)} (h : Omega.IsLipschitzDomainAtWith L x) {c : ℝ} (hc : 0 < c) :
    (c • Omega).IsLipschitzDomainAtWith L (c • x) := by
  obtain ⟨e, φ, a, b, hex, ha, hb, hφ0, hφ, hOmega⟩ := h
  -- The conjugate `y ↦ c • e (c⁻¹ • y)` of `e` is again an affine isometry: it has the linear
  -- part of `e` and translation part `c • e 0`.
  let e' : WithLp 2 (ℝ × E) ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E) :=
    e.linearIsometryEquiv.toAffineIsometryEquiv.trans
      (AffineIsometryEquiv.constVAdd ℝ _ (c • e 0))
  have he' (y : WithLp 2 (ℝ × E)) : e' (c • y) = c • e y := by
    have he : e y = e.linearIsometryEquiv y + e 0 := by simpa using e.map_vadd 0 y
    simp [e', he, smul_add, add_comm]
  have hsymm (z : WithLp 2 (ℝ × E)) : e'.symm z = c • e.symm (c⁻¹ • z) := by
    rw [AffineIsometryEquiv.symm_apply_eq, he', AffineIsometryEquiv.apply_symm_apply,
      smul_inv_smul₀ hc.ne']
  refine ⟨e', fun y ↦ c * φ (c⁻¹ • y), c * a, c * b, by rw [he', hex, smul_zero],
    mul_pos hc ha, mul_pos hc hb, by simp [hφ0], ?_, fun z hz ↦ ?_⟩
  · refine LipschitzWith.of_dist_le_mul fun y z ↦ ?_
    have hyz := hφ.dist_le_mul (c⁻¹ • y) (c⁻¹ • z)
    rw [dist_smul₀, Real.norm_eq_abs, abs_inv, abs_of_pos hc] at hyz
    rw [Real.dist_eq, ← mul_sub, abs_mul, abs_of_pos hc, ← Real.dist_eq]
    calc c * dist (φ (c⁻¹ • y)) (φ (c⁻¹ • z)) ≤ c * (L * (c⁻¹ * dist y z)) :=
          mul_le_mul_of_nonneg_left hyz hc.le
      _ = L * dist y z := by field_simp
  · rw [← smul_normalCylinder hc, mem_smul_set_iff_inv_smul_mem₀ hc.ne'] at hz
    rw [hsymm, smul_mem_smul_set_iff₀ hc.ne', hOmega _ hz]
    simp only [WithLp.smul_fst, WithLp.smul_snd, smul_eq_mul]
    rw [← mul_lt_mul_iff_of_pos_left hc, mul_inv_cancel_left₀ hc.ne']

/-- **Positive dilation of a Lipschitz domain.** For `c > 0`, the dilation `c • Omega` of a
Lipschitz domain with constant `L` is a Lipschitz domain with the same constant. -/
theorem IsLipschitzDomainWith.smul {Omega : Set (WithLp 2 (ℝ × E))} {L : ℝ≥0}
    (h : Omega.IsLipschitzDomainWith L) {c : ℝ} (hc : 0 < c) :
    (c • Omega).IsLipschitzDomainWith L := by
  refine ⟨h.1.smul₀ hc.ne', fun y hy ↦ ?_⟩
  have hfrontier : c • frontier Omega = frontier (c • Omega) := by
    rw [frontier, frontier, closure_smul₀' hc.ne', interior_smul₀ hc.ne', smul_set_sdiff₀ hc.ne']
  rw [← hfrontier] at hy
  obtain ⟨x, hx, rfl⟩ := hy
  exact (h.2 x hx).smul hc

end Dilation

section Cover

variable {Omega : Set (WithLp 2 (ℝ × E))} {L : ℝ≥0}

/-- **Finite chart covers of compact boundary pieces.** If `Omega` is a Lipschitz domain with
constant `L` at every point of a compact set `K`, then finitely many points of `K` carry
Lipschitz boundary charts with the common constant `L` whose cylinders cover `K`. -/
theorem _root_.IsCompact.exists_finset_isLipschitzChartWith_cover {K : Set (WithLp 2 (ℝ × E))}
    (hK : IsCompact K) (h : ∀ x ∈ K, Omega.IsLipschitzDomainAtWith L x) :
    ∃ (t : Finset (WithLp 2 (ℝ × E))) (e : WithLp 2 (ℝ × E) → WithLp 2 (ℝ × E) ≃ᵃⁱ[ℝ]
        WithLp 2 (ℝ × E)) (φ : WithLp 2 (ℝ × E) → E → ℝ) (a b : WithLp 2 (ℝ × E) → ℝ),
      (∀ x ∈ t, x ∈ K ∧ e x x = 0 ∧ Omega.IsLipschitzChartWith L (e x) (φ x) (a x) (b x)) ∧
        K ⊆ ⋃ x ∈ t, e x ⁻¹' normalCylinder (a x) (b x) := by
  choose! e φ a b hex hchart using h
  obtain ⟨t, htK, hcover⟩ := hK.elim_nhds_subcover _
    fun x hx ↦ (hchart x hx).preimage_normalCylinder_mem_nhds (hex x hx)
  exact ⟨t, e, φ, a, b, fun x hx ↦ ⟨htK x hx, hex x (htK x hx), hchart x (htK x hx)⟩, hcover⟩

/-- **Finite chart covers of bounded Lipschitz domains.** The frontier of a bounded Lipschitz
domain with constant `L` is covered by the cylinders of finitely many Lipschitz boundary charts,
centred at frontier points, all with the common Lipschitz constant `L`. -/
theorem IsLipschitzDomainWith.exists_finset_isLipschitzChartWith_cover [FiniteDimensional ℝ E]
    (h : Omega.IsLipschitzDomainWith L) (hb : Bornology.IsBounded Omega) :
    ∃ (t : Finset (WithLp 2 (ℝ × E))) (e : WithLp 2 (ℝ × E) → WithLp 2 (ℝ × E) ≃ᵃⁱ[ℝ]
        WithLp 2 (ℝ × E)) (φ : WithLp 2 (ℝ × E) → E → ℝ) (a b : WithLp 2 (ℝ × E) → ℝ),
      (∀ x ∈ t, x ∈ frontier Omega ∧ e x x = 0 ∧
        Omega.IsLipschitzChartWith L (e x) (φ x) (a x) (b x)) ∧
        frontier Omega ⊆ ⋃ x ∈ t, e x ⁻¹' normalCylinder (a x) (b x) :=
  (isCompact_of_isClosed_isBounded isClosed_frontier
    (hb.closure.subset frontier_subset_closure)).exists_finset_isLipschitzChartWith_cover h.2

end Cover

end Set

end
