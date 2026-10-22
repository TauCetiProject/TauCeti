/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Affine.Isometry
public import TauCeti.Analysis.Normed.Lp.GraphDomain
public import Mathlib.Topology.MetricSpace.Lipschitz
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Domains with Lipschitz boundary

`Set.IsLipschitzChart` is the shared uncentred geometric chart in an arbitrary real normed
ambient space. `Set.IsLipschitzChartWith` adds normalization of its graph at zero, as required
by the Sobolev consumers. `Set.IsLipschitzDomain` allows the bound to vary along the frontier;
`Set.IsLipschitzDomainWith` retains its distinct uniform quantitative bound. The theorem
`Set.isLipschitzDomain_iff_forall_exists_isLipschitzDomainAtWith` relates these conditions.

Charts can be recentred and transported by affine isometries or positive dilation. Domains
with compact frontier have finite chart covers with a common bound; epigraphs of globally
Lipschitz functions are examples.

A shared chart identifies a set in a real normed ambient space with an epigraph inside
a cylinder in the real normed model space `WithLp 2 (ℝ × E)`. The centered predicate
`Set.IsLipschitzChartWith` additionally requires that the graph pass through the chart centre.
For centered charts the normal and tangential radii can be reduced without changing the
coordinates or the graph. Shared charts have no normalization requirement on the graph.

The global predicate `Set.IsLipschitzDomainWith` requires a chart centred at every frontier point,
with a single Lipschitz bound for all local graphs. It is invariant under affine isometries and
positive dilations, and on a compact part of the frontier finitely many charts suffice. These are
the geometric hypotheses used to transport Sobolev trace and extension operators from a flat
half-space through boundary charts and to patch them with a partition of unity.

Locally Lipschitz boundary graphs extend to global graphs with the same constant and radii,
using Mathlib's `LipschitzOnWith.extend_real`. The open set `TauCeti.chartEpigraph` and its
support-containment lemmas provide the shared geometry for chart trace and extension operators.

## Main declarations

* `TauCeti.normalCylinder`: the product cylinder used by boundary charts.
* `Set.IsLipschitzChartWith`: a Lipschitz boundary chart with given coordinates, graph and radii.
* `Set.IsLipschitzDomainAtWith`: the existence of a Lipschitz boundary chart centred at one point.
* `Set.IsLipschitzDomainWith`: an open set with the local graph condition at every frontier point.
* `Set.IsLipschitzChartWith.lipschitzWith`, `Set.IsLipschitzChartWith.apply_zero`: the graph of a
  chart is `L`-Lipschitz and passes through the centre.
* `TauCeti.exists_isLipschitzChartWith_of_lipschitzOnWith`: extension of a local Lipschitz graph
  to a global graph defining the same boundary chart.
* `Set.IsLipschitzChartWith.mono_radii`: restriction of a chart to a smaller cylinder.
* `Set.IsLipschitzChartWith.exists_mono_radii_two_mul_lt`: restriction to a cylinder whose
  normal radius exceeds twice the graph's tangential rise.
* `Set.IsLipschitzChartWith.smul`: positive dilation of a chart, with explicit coordinates
  `TauCeti.dilateConj`, graph and radii.
* `Set.IsLipschitzDomainWith.smul`: positive dilations preserve Lipschitz domains and constants.
* `Set.IsLipschitzDomainWith.exists_finset_isLipschitzChartWith_cover`: the frontier of a bounded
  Lipschitz domain is covered by finitely many chart cylinders with a common Lipschitz constant.
* `Set.IsLipschitzDomainWith.exists_finset_isLipschitzChartWith_two_mul_lt_cover`: the frontier of
  a bounded Lipschitz domain is covered by finitely many shortened chart cylinders.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., §5.5.
* W. McLean, *Strongly Elliptic Systems and Boundary Integral Equations*, §3.1.
* P. Grisvard, *Elliptic Problems in Nonsmooth Domains*, Definition 1.2.1.1.
* L. C. Evans and R. F. Gariepy, *Measure Theory and Fine Properties of Functions*, §4.3.
-/

public section

noncomputable section

namespace TauCeti

open Metric Set Filter Topology
open scoped NNReal Pointwise

variable {E : Type*} [SeminormedAddCommGroup E]

/-- The open product cylinder of normal radius `a` and tangential radius `b`, centred at the
origin of `WithLp 2 (ℝ × E)`. -/
def normalCylinder (a b : ℝ) : Set (WithLp 2 (ℝ × E)) :=
  {x | x.fst ∈ Ioo (-a) a ∧ x.snd ∈ ball 0 b}

/-- Membership in the normal product cylinder, in terms of its two coordinates. -/
@[simp]
theorem mem_normalCylinder {a b : ℝ} {x : WithLp 2 (ℝ × E)} :
    x ∈ normalCylinder a b ↔ -a < x.fst ∧ x.fst < a ∧ ‖x.snd‖ < b := by
  simp [normalCylinder, and_assoc]

/-- A normal product cylinder is open. -/
theorem isOpen_normalCylinder (a b : ℝ) : IsOpen (normalCylinder (E := E) a b) := by
  exact (isOpen_Ioo.preimage (WithLp.prod_continuous_ofLp 2 ℝ E).fst).inter
    (isOpen_ball.preimage (WithLp.prod_continuous_ofLp 2 ℝ E).snd)

/-- A normal product cylinder is bounded. -/
theorem isBounded_normalCylinder (a b : ℝ) :
    Bornology.IsBounded (normalCylinder (E := E) a b) :=
  (WithLp.prod_antilipschitzWith_ofLp 2 ℝ E).isBounded_preimage
    ((isBounded_Ioo (-a) a).prod isBounded_ball)

/-- Shrinking either radius shrinks the normal product cylinder. -/
theorem normalCylinder_mono {a b a' b' : ℝ} (ha : a' ≤ a) (hb : b' ≤ b) :
    normalCylinder (E := E) a' b' ⊆ normalCylinder a b := by
  intro x hx
  simp only [mem_normalCylinder] at hx ⊢
  exact ⟨lt_of_le_of_lt (neg_le_neg ha) hx.1, hx.2.1.trans_le ha, hx.2.2.trans_le hb⟩

/-- A normal product cylinder with positive radii contains its centre. -/
theorem zero_mem_normalCylinder {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (0 : WithLp 2 (ℝ × E)) ∈ normalCylinder a b := by
  simp [ha, hb]

/-- Dilating a normal product cylinder by `c > 0` multiplies both radii by `c`. -/
theorem smul_normalCylinder [MulAction ℝ E] [NormSMulClass ℝ E] {c : ℝ} (hc : 0 < c)
    (a b : ℝ) :
    c • normalCylinder (E := E) a b = normalCylinder (c * a) (c * b) := by
  ext z
  rw [mem_smul_set_iff_inv_smul_mem₀ hc.ne']
  simp only [mem_normalCylinder, ← WithLp.ofLp_fst, ← WithLp.ofLp_snd, WithLp.ofLp_smul,
    Prod.smul_fst, Prod.smul_snd, smul_eq_mul, norm_smul,
    norm_inv, Real.norm_eq_abs, abs_of_pos hc, inv_mul_lt_iff₀ hc, lt_inv_mul_iff₀ hc, mul_neg]


end TauCeti

namespace Set

open Metric Filter TauCeti Topology
open scoped NNReal Pointwise

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]

/-! ### Lipschitz boundary charts -/

/-- A **Lipschitz boundary chart** of `Ω ⊆ F`. In the coordinates given by the affine isometry
`e : F ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E)`, the part of `Ω` inside the open cylinder
`normalCylinder h r` is the part of that cylinder strictly above the graph `x.fst = γ x.snd` of
the `K`-Lipschitz function `γ : E → ℝ`. -/
structure IsLipschitzChart (Ω : Set F) (e : F ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E)) (γ : E → ℝ) (K : ℝ≥0)
    (h r : ℝ) : Prop where
  /-- The cylinder has positive half-height. -/
  height_pos : 0 < h
  /-- The cylinder has positive radius. -/
  radius_pos : 0 < r
  /-- The graph function is `K`-Lipschitz. -/
  lipschitzWith : LipschitzWith K γ
  /-- Inside the cylinder, `Ω` is the region above the graph. -/
  image_inter_normalCylinder :
    e '' Ω ∩ normalCylinder h r = {x | γ x.snd < x.fst} ∩ normalCylinder h r

namespace IsLipschitzChart

variable {Ω : Set F} {e : F ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E)} {γ : E → ℝ} {K : ℝ≥0} {h r : ℝ}

/-- Inside the cylinder of a Lipschitz chart, the frontier of `Ω` is the graph. -/
theorem image_frontier_inter_normalCylinder (hc : IsLipschitzChart Ω e γ K h r) :
    e '' frontier Ω ∩ normalCylinder h r = {x | x.fst = γ x.snd} ∩ normalCylinder h r := by
  have hC := isOpen_normalCylinder (E := E) h r
  rw [← e.coe_toHomeomorph, e.toHomeomorph.image_frontier, e.coe_toHomeomorph,
    ← frontier_inter_open_inter hC, hc.image_inter_normalCylinder, frontier_inter_open_inter hC,
    frontier_setOf_lt_fst hc.lipschitzWith.continuous]

/-- Inside the cylinder of a Lipschitz chart, the closure of `Ω` is the region on or above the
graph. -/
theorem image_closure_inter_normalCylinder (hc : IsLipschitzChart Ω e γ K h r) :
    e '' closure Ω ∩ normalCylinder h r = {x | γ x.snd ≤ x.fst} ∩ normalCylinder h r := by
  rw [closure_eq_self_union_frontier, image_union, union_inter_distrib_right,
    hc.image_inter_normalCylinder, hc.image_frontier_inter_normalCylinder,
    ← union_inter_distrib_right]
  congr 1
  ext x
  simp [le_iff_lt_or_eq, eq_comm]

/-- A point whose image lies in the cylinder of a Lipschitz chart belongs to `Ω` exactly when
its image lies above the graph. -/
theorem mem_iff (hc : IsLipschitzChart Ω e γ K h r) {x : F} (hxC : e x ∈ normalCylinder h r) :
    x ∈ Ω ↔ γ (e x).snd < (e x).fst := by
  rw [← e.injective.mem_set_image]
  exact ⟨fun hx => (hc.image_inter_normalCylinder.subset ⟨hx, hxC⟩).1,
    fun hx => (hc.image_inter_normalCylinder.superset ⟨hx, hxC⟩).1⟩

/-- A frontier point of `Ω` inside the cylinder of a Lipschitz chart lies on the graph. -/
theorem fst_apply_eq_of_mem_frontier (hc : IsLipschitzChart Ω e γ K h r) {x : F}
    (hx : x ∈ frontier Ω) (hxC : e x ∈ normalCylinder h r) : (e x).fst = γ (e x).snd :=
  (hc.image_frontier_inter_normalCylinder.subset ⟨mem_image_of_mem e hx, hxC⟩).1

/-- A Lipschitz chart restricts to every smaller cylinder. -/
theorem mono (hc : IsLipschitzChart Ω e γ K h r) {h' r' : ℝ} (hh' : 0 < h') (hr' : 0 < r')
    (hh : h' ≤ h) (hr : r' ≤ r) : IsLipschitzChart Ω e γ K h' r' where
  height_pos := hh'
  radius_pos := hr'
  lipschitzWith := hc.lipschitzWith
  image_inter_normalCylinder := by
    have hsub := normalCylinder_mono (E := E) hh hr
    rw [← inter_eq_right.2 hsub, ← inter_assoc, hc.image_inter_normalCylinder, inter_assoc]

/-- A `K`-Lipschitz chart is a `K'`-Lipschitz chart for every `K' ≥ K`. -/
theorem weaken (hc : IsLipschitzChart Ω e γ K h r) {K' : ℝ≥0} (hK : K ≤ K') :
    IsLipschitzChart Ω e γ K' h r :=
  { hc with lipschitzWith := hc.lipschitzWith.weaken hK }

/-- Recentring a Lipschitz chart at the point `p` of the model: after translating by `-p`, the
graph function becomes `y ↦ γ (y + p.snd) - p.fst`, and any cylinder whose translate by `p`
lies in the original cylinder is again a chart. -/
theorem trans_constVAdd (hc : IsLipschitzChart Ω e γ K h r) (p : WithLp 2 (ℝ × E)) {h' r' : ℝ}
    (hh' : 0 < h') (hr' : 0 < r') (hh : |p.fst| + h' ≤ h) (hr : ‖p.snd‖ + r' ≤ r) :
    IsLipschitzChart Ω (e.trans (AffineIsometryEquiv.constVAdd ℝ _ (-p)))
      (fun y => γ (y + p.snd) - p.fst) K h' r' where
  height_pos := hh'
  radius_pos := hr'
  lipschitzWith := LipschitzWith.of_dist_le_mul fun y y' => by
    simpa using hc.lipschitzWith.dist_le_mul (y + p.snd) (y' + p.snd)
  image_inter_normalCylinder := by
    ext w
    -- The translate `p + w` of a point `w` of the new cylinder lies in the old cylinder.
    have hC : w ∈ normalCylinder h' r' → p + w ∈ normalCylinder h r := by
      intro hw
      rw [mem_normalCylinder] at hw ⊢
      simp only [WithLp.add_fst, WithLp.add_snd]
      exact ⟨by linarith [neg_abs_le p.fst], by linarith [le_abs_self p.fst],
        by linarith [norm_add_le p.snd w.snd]⟩
    have key : p + w ∈ e '' Ω ∩ normalCylinder h r ↔
        p + w ∈ {x | γ x.snd < x.fst} ∩ normalCylinder h r := by
      rw [hc.image_inter_normalCylinder]
    simp only [AffineIsometryEquiv.coe_trans, image_comp, AffineIsometryEquiv.coe_constVAdd,
      vadd_eq_add, image_add_left, neg_neg, mem_inter_iff, mem_preimage, mem_ofPred_eq] at key ⊢
    constructor
    · rintro ⟨hw, hwC⟩
      have := (key.1 ⟨hw, hC hwC⟩).1
      simp only [WithLp.add_fst, WithLp.add_snd] at this
      exact ⟨by rw [add_comm w.snd]; linarith, hwC⟩
    · rintro ⟨hw, hwC⟩
      refine ⟨(key.2 ⟨?_, hC hwC⟩).1, hwC⟩
      simp only [WithLp.add_fst, WithLp.add_snd]
      rw [add_comm p.snd]
      linarith

/-- A Lipschitz chart can be recentred at any point of its cylinder, keeping its Lipschitz
constant. -/
theorem exists_isLipschitzChart_eq_zero (hc : IsLipschitzChart Ω e γ K h r) {x : F}
    (hx : e x ∈ normalCylinder h r) :
    ∃ (e' : F ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E)) (γ' : E → ℝ) (h' r' : ℝ),
      IsLipschitzChart Ω e' γ' K h' r' ∧ e' x = 0 := by
  have hx' : |(e x).fst| < h ∧ ‖(e x).snd‖ < r := by
    simpa only [mem_normalCylinder, abs_lt, and_assoc] using hx
  exact ⟨_, _, _, _, hc.trans_constVAdd (e x) (sub_pos.2 hx'.1) (sub_pos.2 hx'.2)
    (by linarith) (by linarith), by simp⟩

/-- Transporting a Lipschitz chart along an affine isometry `g : F ≃ᵃⁱ[ℝ] G`. -/
theorem image (hc : IsLipschitzChart Ω e γ K h r) (g : F ≃ᵃⁱ[ℝ] G) :
    IsLipschitzChart (g '' Ω) (g.symm.trans e) γ K h r :=
  { hc with
    image_inter_normalCylinder := by
      simpa only [image_image, AffineIsometryEquiv.coe_trans, Function.comp_apply,
        AffineIsometryEquiv.symm_apply_apply] using hc.image_inter_normalCylinder }

/-- Dilating a Lipschitz chart by a factor `c > 0`: the dilated set `c • Ω` has a chart with
graph function `y ↦ c * γ (c⁻¹ • y)`, the same Lipschitz constant, and the dilated cylinder. -/
theorem smul (hc : IsLipschitzChart Ω e γ K h r) {c : ℝ} (hc0 : 0 < c) :
    IsLipschitzChart (c • Ω) (dilateConj c e) (fun y => c * γ (c⁻¹ • y)) K (c * h) (c * r) := by
  refine ⟨mul_pos hc0 hc.height_pos, mul_pos hc0 hc.radius_pos, ?_, ?_⟩
  · have hK : ‖c‖₊ * K * ‖c⁻¹‖₊ = K := by
      rw [mul_comm, ← mul_assoc, ← nnnorm_mul, inv_mul_cancel₀ hc0.ne', nnnorm_one, one_mul]
    simpa only [hK, Function.comp_def, smul_eq_mul] using
      ((lipschitzWith_smul c).comp hc.lipschitzWith).comp (lipschitzWith_smul c⁻¹)
  · have himage : dilateConj c e '' (c • Ω) = c • (e '' Ω) := by
      rw [← image_smul, ← image_smul, image_image, image_image]
      simp_rw [dilateConj_smul]
    have hepi : {x : WithLp 2 (ℝ × E) | c * γ (c⁻¹ • x.snd) < x.fst} =
        c • {x : WithLp 2 (ℝ × E) | γ x.snd < x.fst} := by
      ext x
      simp only [mem_smul_set_iff_inv_smul_mem₀ hc0.ne', mem_ofPred_eq, WithLp.smul_fst,
        WithLp.smul_snd, smul_eq_mul, lt_inv_mul_iff₀ hc0]
    rw [himage, hepi, ← smul_normalCylinder hc0, ← smul_set_inter₀ hc0.ne',
      ← smul_set_inter₀ hc0.ne', hc.image_inter_normalCylinder]

end IsLipschitzChart

/-! ### Lipschitz domains -/

/-- A set `Ω ⊆ F` is a **Lipschitz domain** modelled on `ℝ × E` if every point of its frontier
is the centre of a Lipschitz boundary chart: after an affine isometry
`e : F ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E)` sending the point to the origin, `Ω` is, inside an open cylinder
around the origin, the region above the graph of a Lipschitz function on `E`. -/
def IsLipschitzDomain (Ω : Set F) (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] : Prop :=
  ∀ x ∈ frontier Ω, ∃ (e : F ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E)) (γ : E → ℝ) (K : ℝ≥0) (h r : ℝ),
    IsLipschitzChart Ω e γ K h r ∧ e x = 0

/-- A set is a Lipschitz domain if and only if every frontier point lies in the cylinder of
some Lipschitz chart, not necessarily centred at it. -/
theorem isLipschitzDomain_iff_exists_mem_normalCylinder {Ω : Set F} :
    Ω.IsLipschitzDomain E ↔ ∀ x ∈ frontier Ω, ∃ (e : F ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E)) (γ : E → ℝ)
      (K : ℝ≥0) (h r : ℝ), IsLipschitzChart Ω e γ K h r ∧ e x ∈ normalCylinder h r := by
  refine ⟨fun hΩ x hx => ?_, fun hΩ x hx => ?_⟩
  · obtain ⟨e, γ, K, h, r, hc, hex⟩ := hΩ x hx
    exact ⟨e, γ, K, h, r, hc, hex ▸ zero_mem_normalCylinder hc.height_pos hc.radius_pos⟩
  · obtain ⟨e, γ, K, h, r, hc, hxC⟩ := hΩ x hx
    obtain ⟨e', γ', h', r', hc', hex⟩ := hc.exists_isLipschitzChart_eq_zero hxC
    exact ⟨e', γ', K, h', r', hc', hex⟩

namespace IsLipschitzDomain

variable {Ω : Set F}

/-- A Lipschitz domain is open: none of its frontier points belong to it, since in a chart
centred at such a point the origin lies on the graph rather than above it. -/
theorem isOpen (hΩ : Ω.IsLipschitzDomain E) : IsOpen Ω := by
  refine subset_interior_iff_isOpen.1 fun x hxΩ => ?_
  rcases (closure_eq_interior_union_frontier Ω ▸ subset_closure hxΩ :
    x ∈ interior Ω ∪ frontier Ω) with hx | hx
  · exact hx
  obtain ⟨e, γ, K, h, r, hc, hex⟩ := hΩ x hx
  have hxC : e x ∈ normalCylinder h r := hex ▸ zero_mem_normalCylinder hc.height_pos hc.radius_pos
  exact absurd (hc.fst_apply_eq_of_mem_frontier hx hxC) ((hc.mem_iff hxC).1 hxΩ).ne'

/-- The image of a Lipschitz domain under an affine isometry is a Lipschitz domain. -/
theorem image (hΩ : Ω.IsLipschitzDomain E) (g : F ≃ᵃⁱ[ℝ] G) : (g '' Ω).IsLipschitzDomain E := by
  intro y hy
  rw [← g.coe_toHomeomorph, ← g.toHomeomorph.image_frontier, g.coe_toHomeomorph] at hy
  obtain ⟨x, hx, rfl⟩ := hy
  obtain ⟨e, γ, K, h, r, hc, hex⟩ := hΩ x hx
  exact ⟨g.symm.trans e, γ, K, h, r, hc.image g, by simpa using hex⟩

/-- The dilation of a Lipschitz domain by a factor `c > 0` is a Lipschitz domain. -/
theorem smul (hΩ : Ω.IsLipschitzDomain E) {c : ℝ} (hc : 0 < c) :
    (c • Ω).IsLipschitzDomain E := by
  intro y hy
  rw [← image_smul, ← (isHomeomorph_smul₀ hc.ne').image_frontier] at hy
  obtain ⟨x, hx, rfl⟩ := hy
  obtain ⟨e, γ, K, h, r, hce, hex⟩ := hΩ x hx
  exact ⟨dilateConj c e, _, K, _, _, hce.smul hc, by simp [hex]⟩

/-- A Lipschitz domain with compact frontier has a finite cover of its frontier by the
cylinders of Lipschitz charts sharing a common Lipschitz constant. -/
theorem exists_finite_cover (hΩ : Ω.IsLipschitzDomain E) (hcompact : IsCompact (frontier Ω)) :
    ∃ (K : ℝ≥0) (m : ℕ) (e : Fin m → F ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E)) (γ : Fin m → E → ℝ)
      (h r : Fin m → ℝ), (∀ i, IsLipschitzChart Ω (e i) (γ i) K (h i) (r i)) ∧
        frontier Ω ⊆ ⋃ i, e i ⁻¹' normalCylinder (h i) (r i) := by
  choose e γ K h r hc hex using fun x : frontier Ω => hΩ x x.2
  obtain ⟨t, ht⟩ := hcompact.elim_finite_subcover
    (fun x : frontier Ω => e x ⁻¹' normalCylinder (h x) (r x))
    (fun x => (isOpen_normalCylinder _ _).preimage (e x).continuous)
    fun x hx => mem_iUnion.2 ⟨⟨x, hx⟩, by
      simpa [mem_preimage, hex] using
        zero_mem_normalCylinder (E := E) (hc ⟨x, hx⟩).height_pos (hc ⟨x, hx⟩).radius_pos⟩
  let f : Fin t.card → frontier Ω := fun i => t.equivFin.symm i
  refine ⟨t.sup K, t.card, fun i => e (f i), fun i => γ (f i), fun i => h (f i),
    fun i => r (f i), fun i => (hc (f i)).weaken (t.le_sup (t.equivFin.symm i).2), ?_⟩
  intro x hx
  obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.1 (ht hx)
  exact mem_iUnion.2 ⟨t.equivFin ⟨y, hy⟩, by simpa [f] using hxy⟩

/-- A bounded Lipschitz domain in a proper space has a finite cover of its frontier by the
cylinders of Lipschitz charts sharing a common Lipschitz constant. -/
theorem exists_finite_cover_of_isBounded [ProperSpace F] (hΩ : Ω.IsLipschitzDomain E)
    (hb : Bornology.IsBounded Ω) :
    ∃ (K : ℝ≥0) (m : ℕ) (e : Fin m → F ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E)) (γ : Fin m → E → ℝ)
      (h r : Fin m → ℝ), (∀ i, IsLipschitzChart Ω (e i) (γ i) K (h i) (r i)) ∧
        frontier Ω ⊆ ⋃ i, e i ⁻¹' normalCylinder (h i) (r i) :=
  hΩ.exists_finite_cover <| Metric.isCompact_of_isClosed_isBounded isClosed_frontier
    (hb.closure.subset frontier_subset_closure)

end IsLipschitzDomain

/-- Being a Lipschitz domain is invariant under affine isometries. -/
@[simp]
theorem isLipschitzDomain_image_iff {Ω : Set F} (g : F ≃ᵃⁱ[ℝ] G) :
    (g '' Ω).IsLipschitzDomain E ↔ Ω.IsLipschitzDomain E :=
  ⟨fun hΩ => by simpa [image_image] using hΩ.image g.symm, fun hΩ => hΩ.image g⟩

/-- Being a Lipschitz domain is invariant under positive dilations. -/
@[simp]
theorem isLipschitzDomain_smul_iff {Ω : Set F} {c : ℝ} (hc : 0 < c) :
    (c • Ω).IsLipschitzDomain E ↔ Ω.IsLipschitzDomain E :=
  ⟨fun hΩ => by simpa [smul_smul, hc.ne'] using hΩ.smul (inv_pos.2 hc), fun hΩ => hΩ.smul hc⟩

/-! ### The region above a Lipschitz graph -/

/-- The identity is a Lipschitz chart, with any cylinder, of the region above the graph of a
Lipschitz function. -/
theorem isLipschitzChart_refl_setOf_lt_fst {γ : E → ℝ} {K : ℝ≥0} (hγ : LipschitzWith K γ)
    {h r : ℝ} (hh : 0 < h) (hr : 0 < r) :
    IsLipschitzChart {x : WithLp 2 (ℝ × E) | γ x.snd < x.fst}
      (AffineIsometryEquiv.refl ℝ _) γ K h r where
  height_pos := hh
  radius_pos := hr
  lipschitzWith := hγ
  image_inter_normalCylinder := by simp

/-- The region strictly above the graph of a Lipschitz function `γ : E → ℝ` is a Lipschitz
domain modelled on `ℝ × E`. -/
theorem isLipschitzDomain_setOf_lt_fst {γ : E → ℝ} {K : ℝ≥0} (hγ : LipschitzWith K γ) :
    {x : WithLp 2 (ℝ × E) | γ x.snd < x.fst}.IsLipschitzDomain E :=
  isLipschitzDomain_iff_exists_mem_normalCylinder.2 fun x _ =>
    ⟨_, γ, K, |x.fst| + 1, ‖x.snd‖ + 1,
      isLipschitzChart_refl_setOf_lt_fst hγ (by positivity) (by positivity), by
        rw [mem_normalCylinder]
        -- The affine identity and its coordinate projections reduce definitionally.
        change -(|x.fst| + 1) < x.fst ∧ x.fst < |x.fst| + 1 ∧ ‖x.snd‖ < ‖x.snd‖ + 1
        exact ⟨by linarith [neg_abs_le x.fst], by linarith [le_abs_self x.fst], by linarith⟩⟩


end Set

namespace Set

open Metric Filter TauCeti Topology
open scoped NNReal Pointwise

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- `Omega.IsLipschitzChartWith L e φ a b` says that the rigid coordinates `e` identify `Omega`
inside the open product cylinder `normalCylinder a b` with the strict epigraph of `φ`, where `φ`
satisfies `LipschitzWith L φ` and `φ 0 = 0`. The centre `e.symm 0` of the chart therefore lies on
the graph.

The two independently positive cylinder radii retain the product geometry needed for boundary
charts and permit either the normal or tangential direction to be shrunk later. -/
def IsLipschitzChartWith (Omega : Set F) (L : ℝ≥0)
    (e : F ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E)) (φ : E → ℝ) (a b : ℝ) : Prop :=
  φ 0 = 0 ∧ Omega.IsLipschitzChart e φ L a b

/-- A centered chart is the shared geometric chart with its graph normalized at the origin. -/
theorem IsLipschitzChartWith.toIsLipschitzChart {Omega : Set F} {L : ℝ≥0}
    {e : F ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E)} {φ : E → ℝ} {a b : ℝ}
    (h : Omega.IsLipschitzChartWith L e φ a b) : Omega.IsLipschitzChart e φ L a b :=
  h.2

/-- A geometric chart whose graph vanishes at the origin is a centered chart. -/
theorem IsLipschitzChart.isLipschitzChartWith {Omega : Set F} {L : ℝ≥0}
    {e : F ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E)} {φ : E → ℝ} {a b : ℝ}
    (h : Omega.IsLipschitzChart e φ L a b) (hφ : φ 0 = 0) :
    Omega.IsLipschitzChartWith L e φ a b :=
  ⟨hφ, h⟩

/-- A centered Lipschitz boundary chart written out as a rigid-coordinate graph condition. -/
theorem isLipschitzChartWith_iff (Omega : Set F) (L : ℝ≥0)
    (e : F ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E)) (φ : E → ℝ) (a b : ℝ) :
    Omega.IsLipschitzChartWith L e φ a b ↔
      0 < a ∧ 0 < b ∧ φ 0 = 0 ∧ LipschitzWith L φ ∧
        ∀ z ∈ normalCylinder a b, (e.symm z ∈ Omega ↔ φ z.snd < z.fst) := by
  constructor
  · rintro ⟨hφ, h⟩
    exact ⟨h.height_pos, h.radius_pos, hφ, h.lipschitzWith,
      fun z hz ↦ by simpa using h.mem_iff (x := e.symm z) (by simpa using hz)⟩
  · rintro ⟨ha, hb, hφ, hLip, hmem⟩
    refine ⟨hφ, ha, hb, hLip, ?_⟩
    ext z
    simp only [mem_inter_iff, mem_ofPred_eq]
    apply and_congr_left
    intro hz
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (hmem (e x) hz).1 (by simpa using hx)
    · intro hφz
      exact ⟨e.symm z, (hmem z hz).2 hφz, e.apply_symm_apply z⟩

/-- A set is a Lipschitz domain at `x`, with graph constant at most `L`, if it has a Lipschitz
boundary chart whose rigid coordinates take `x` to the origin. -/
def IsLipschitzDomainAtWith (Omega : Set F) (L : ℝ≥0)
    (x : F) : Prop :=
  ∃ (e : F ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E)) (φ : E → ℝ) (a b : ℝ),
    e x = 0 ∧ Omega.IsLipschitzChartWith L e φ a b

/-- The local Lipschitz-domain predicate is the existence of a chart centred at the point. -/
theorem isLipschitzDomainAtWith_iff (Omega : Set F) (L : ℝ≥0)
    (x : F) :
    Omega.IsLipschitzDomainAtWith (E := E) L x ↔
      ∃ (e : F ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E)) (φ : E → ℝ) (a b : ℝ),
        e x = 0 ∧ Omega.IsLipschitzChartWith L e φ a b :=
  Iff.rfl

/-- An open set is a Lipschitz domain with constant `L` if it has a Lipschitz graph chart with
that bound at every point of its frontier. -/
def IsLipschitzDomainWith (Omega : Set (WithLp 2 (ℝ × E))) (L : ℝ≥0) : Prop :=
  IsOpen Omega ∧ ∀ x ∈ frontier Omega, Omega.IsLipschitzDomainAtWith (E := E) L x

/-- A set is a Lipschitz domain with constant `L` exactly when it is open and has a local
`L`-Lipschitz graph chart at every frontier point. -/
theorem isLipschitzDomainWith_iff (Omega : Set (WithLp 2 (ℝ × E))) (L : ℝ≥0) :
    Omega.IsLipschitzDomainWith L ↔
      IsOpen Omega ∧ ∀ x ∈ frontier Omega, Omega.IsLipschitzDomainAtWith (E := E) L x :=
  Iff.rfl

section Chart

variable {Omega : Set F} {L : ℝ≥0}
  {e : F ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E)} {φ : E → ℝ} {a b : ℝ}

/-- The graph function of a Lipschitz boundary chart is `L`-Lipschitz. -/
theorem IsLipschitzChartWith.lipschitzWith (h : Omega.IsLipschitzChartWith L e φ a b) :
    LipschitzWith L φ :=
  h.toIsLipschitzChart.lipschitzWith

/-- The graph of a Lipschitz boundary chart passes through the centre of the chart. -/
theorem IsLipschitzChartWith.apply_zero (h : Omega.IsLipschitzChartWith L e φ a b) : φ 0 = 0 :=
  h.1

/-- **Membership in chart coordinates.** A point `z` of the chart cylinder corresponds to a point
of `Omega` exactly when it lies strictly above the graph of `φ`. -/
theorem IsLipschitzChartWith.symm_mem_iff (h : Omega.IsLipschitzChartWith L e φ a b)
    {z : WithLp 2 (ℝ × E)} (hz : z ∈ normalCylinder a b) :
    e.symm z ∈ Omega ↔ φ z.snd < z.fst :=
  by simpa using h.toIsLipschitzChart.mem_iff (x := e.symm z) (by simpa using hz)

/-- **Membership through a chart.** A point `x` whose coordinates `e x` lie in the chart cylinder
belongs to `Omega` exactly when `e x` lies strictly above the graph of `φ`. -/
theorem IsLipschitzChartWith.mem_iff (h : Omega.IsLipschitzChartWith L e φ a b)
    {x : F} (hx : e x ∈ normalCylinder a b) :
    x ∈ Omega ↔ φ (e x).snd < (e x).fst := by
  simpa using h.symm_mem_iff hx

/-- A Lipschitz boundary chart remains valid after increasing the allowed Lipschitz constant. -/
theorem IsLipschitzChartWith.weaken (h : Omega.IsLipschitzChartWith L e φ a b) {L' : ℝ≥0}
    (hLL' : L ≤ L') : Omega.IsLipschitzChartWith L' e φ a b :=
  ⟨h.1, h.toIsLipschitzChart.weaken hLL'⟩

/-- **Restriction of a chart.** A Lipschitz boundary chart remains valid on every smaller
cylinder with positive radii, with the same coordinates and graph. -/
theorem IsLipschitzChartWith.mono_radii (h : Omega.IsLipschitzChartWith L e φ a b)
    {a' b' : ℝ} (ha' : 0 < a') (hb' : 0 < b') (haa' : a' ≤ a) (hbb' : b' ≤ b) :
    Omega.IsLipschitzChartWith L e φ a' b' :=
  ⟨h.1, h.toIsLipschitzChart.mono ha' hb' haa' hbb'⟩

/-- **Room for reflection across the graph.** Shrinking the tangential radius of a chart gives a
chart with the same coordinates, graph and normal radius whose radii satisfy `2 * L * b' < a`.
The shortened cylinder `normalCylinder (a - 2 * L * b') b'` then still contains the centre, and
the reflection `t ↦ 2 * φ y - t` across the graph keeps it inside `normalCylinder a b'`. -/
theorem IsLipschitzChartWith.exists_mono_radii_two_mul_lt
    (h : Omega.IsLipschitzChartWith L e φ a b) :
    ∃ b' ≤ b, Omega.IsLipschitzChartWith L e φ a b' ∧ 2 * L * b' < a := by
  have hL : (0 : ℝ) < 2 * L + 1 := by positivity
  refine ⟨min b (a / (2 * L + 1)), min_le_left _ _,
    h.mono_radii h.toIsLipschitzChart.height_pos
      (lt_min h.toIsLipschitzChart.radius_pos
        (div_pos h.toIsLipschitzChart.height_pos hL)) le_rfl (min_le_left _ _), ?_⟩
  calc 2 * L * min b (a / (2 * L + 1)) ≤ 2 * L * (a / (2 * L + 1)) := by
        gcongr; exact min_le_right _ _
    _ < a := by
        rw [mul_div_assoc', div_lt_iff₀ hL]
        nlinarith [h.toIsLipschitzChart.height_pos]

/-- The preimage of the chart cylinder is a neighbourhood of the centre of the chart. -/
theorem IsLipschitzChartWith.preimage_normalCylinder_mem_nhds
    (h : Omega.IsLipschitzChartWith L e φ a b) {x : F} (hx : e x = 0) :
    e ⁻¹' normalCylinder a b ∈ 𝓝 x :=
  ((isOpen_normalCylinder a b).preimage e.continuous).mem_nhds
    (by simpa [hx] using
      (zero_mem_normalCylinder (E := E) h.toIsLipschitzChart.height_pos
        h.toIsLipschitzChart.radius_pos))

/-- **Rigid-coordinate transport of a chart.** Composing the coordinates of a chart with the
inverse of an affine isometry `g` gives a chart for the image of the set under `g`. -/
theorem IsLipschitzChartWith.image_affineIsometryEquiv
    (h : Omega.IsLipschitzChartWith L e φ a b) (g : F ≃ᵃⁱ[ℝ] G) :
    (g '' Omega).IsLipschitzChartWith L (g.symm.trans e) φ a b :=
  ⟨h.1, h.toIsLipschitzChart.image g⟩

end Chart

/-- A local Lipschitz-domain chart remains valid after increasing the allowed Lipschitz
constant. -/
theorem IsLipschitzDomainAtWith.mono {Omega : Set F} {L L' : ℝ≥0}
    {x : F} (h : Omega.IsLipschitzDomainAtWith (E := E) L x) (hLL' : L ≤ L') :
    Omega.IsLipschitzDomainAtWith (E := E) L' x := by
  obtain ⟨e, φ, a, b, hex, hchart⟩ := h
  exact ⟨e, φ, a, b, hex, hchart.weaken hLL'⟩

/-- A Lipschitz domain remains one after increasing the allowed Lipschitz constant. -/
theorem IsLipschitzDomainWith.mono {Omega : Set (WithLp 2 (ℝ × E))} {L L' : ℝ≥0}
    (h : Omega.IsLipschitzDomainWith L) (hLL' : L ≤ L') :
    Omega.IsLipschitzDomainWith L' :=
  ⟨h.1, fun x hx ↦ (h.2 x hx).mono hLL'⟩

/-- Transport a local Lipschitz-domain chart by an affine isometry. -/
theorem IsLipschitzDomainAtWith.image_affineIsometryEquiv
    {Omega : Set F} {L : ℝ≥0} {x : F}
    (h : Omega.IsLipschitzDomainAtWith (E := E) L x)
    (g : F ≃ᵃⁱ[ℝ] G) :
    (g '' Omega).IsLipschitzDomainAtWith (E := E) L (g x) := by
  obtain ⟨e, φ, a, b, hex, hchart⟩ := h
  exact ⟨g.symm.trans e, φ, a, b, by simp [hex], hchart.image_affineIsometryEquiv g⟩

/-- The local Lipschitz-domain condition is invariant under an affine isometry. -/
theorem isLipschitzDomainAtWith_image_affineIsometryEquiv_iff
    {Omega : Set F} {L : ℝ≥0} {x : F}
    (g : F ≃ᵃⁱ[ℝ] G) :
    (g '' Omega).IsLipschitzDomainAtWith (E := E) L (g x) ↔
      Omega.IsLipschitzDomainAtWith (E := E) L x := by
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

/-- **Positive dilation of a chart.** For `c > 0`, a Lipschitz boundary chart for `Omega` with
coordinates `e`, graph `φ` and radii `a`, `b` gives a chart for `c • Omega` with the same Lipschitz
constant, the conjugated coordinates `dilateConj c e`, the graph `y ↦ c * φ (c⁻¹ • y)` and the
radii `c * a`, `c * b`. -/
theorem IsLipschitzChartWith.smul {Omega : Set F} {L : ℝ≥0}
    {e : F ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E)} {φ : E → ℝ} {a b : ℝ}
    (h : Omega.IsLipschitzChartWith L e φ a b) {c : ℝ} (hc : 0 < c) :
    (c • Omega).IsLipschitzChartWith L (dilateConj c e) (fun y ↦ c * φ (c⁻¹ • y))
      (c * a) (c * b) :=
  ⟨by simp [h.apply_zero], h.toIsLipschitzChart.smul hc⟩

/-- **Positive dilation of a local chart.** If `Omega` is a Lipschitz domain at `x`, then
`c • Omega` is a Lipschitz domain at `c • x` for every `c > 0`, with the same Lipschitz constant.
See `Set.IsLipschitzChartWith.smul` for the explicit dilated chart. -/
theorem IsLipschitzDomainAtWith.smul {Omega : Set F} {L : ℝ≥0}
    {x : F} (h : Omega.IsLipschitzDomainAtWith (E := E) L x) {c : ℝ} (hc : 0 < c) :
    (c • Omega).IsLipschitzDomainAtWith (E := E) L (c • x) := by
  obtain ⟨e, φ, a, b, hex, hchart⟩ := h
  exact ⟨dilateConj c e, _, _, _, by rw [dilateConj_smul, hex, smul_zero], hchart.smul hc⟩

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
    (hK : IsCompact K) (h : ∀ x ∈ K, Omega.IsLipschitzDomainAtWith (E := E) L x) :
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

/-- **Finite covers of compact boundary pieces by shortened chart cylinders.** If `Omega` is a
Lipschitz domain with constant `L` at every point of a compact set `K`, then finitely many points
of `K` carry Lipschitz boundary charts with the common constant `L` and radii satisfying
`2 * L * b x < a x`, whose shortened cylinders `normalCylinder (a x - 2 * L * b x) (b x)`
cover `K`. -/
theorem _root_.IsCompact.exists_finset_isLipschitzChartWith_two_mul_lt_cover
    {K : Set (WithLp 2 (ℝ × E))} (hK : IsCompact K)
    (h : ∀ x ∈ K, Omega.IsLipschitzDomainAtWith (E := E) L x) :
    ∃ (t : Finset (WithLp 2 (ℝ × E))) (e : WithLp 2 (ℝ × E) → WithLp 2 (ℝ × E) ≃ᵃⁱ[ℝ]
        WithLp 2 (ℝ × E)) (φ : WithLp 2 (ℝ × E) → E → ℝ) (a b : WithLp 2 (ℝ × E) → ℝ),
      (∀ x ∈ t, x ∈ K ∧ e x x = 0 ∧
        Omega.IsLipschitzChartWith L (e x) (φ x) (a x) (b x) ∧ 2 * L * b x < a x) ∧
        K ⊆ ⋃ x ∈ t, e x ⁻¹' normalCylinder (a x - 2 * L * b x) (b x) := by
  have hshort : ∀ x ∈ K, ∃ (e : WithLp 2 (ℝ × E) ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E))
      (φ : E → ℝ) (a b : ℝ), e x = 0 ∧ Omega.IsLipschitzChartWith L e φ a b ∧ 2 * L * b < a := by
    intro x hx
    obtain ⟨e, φ, a, b, hex, hchart⟩ := (isLipschitzDomainAtWith_iff ..).1 (h x hx)
    obtain ⟨b', -, hchart', hlt⟩ := hchart.exists_mono_radii_two_mul_lt
    exact ⟨e, φ, a, b', hex, hchart', hlt⟩
  choose! e φ a b hex hchart hlt using hshort
  have hnhds : ∀ x ∈ K, e x ⁻¹' normalCylinder (a x - 2 * L * b x) (b x) ∈ 𝓝 x := by
    intro x hx
    have hb0 := ((isLipschitzChartWith_iff ..).1 (hchart x hx)).2.1
    exact ((hchart x hx).mono_radii (sub_pos.2 (hlt x hx)) hb0 (sub_le_self _ (by positivity))
      le_rfl).preimage_normalCylinder_mem_nhds (hex x hx)
  obtain ⟨t, htK, hcover⟩ := hK.elim_nhds_subcover _ hnhds
  exact ⟨t, e, φ, a, b, fun x hx ↦ ⟨htK x hx, hex x (htK x hx), hchart x (htK x hx),
    hlt x (htK x hx)⟩, hcover⟩

/-- **Finite covers of bounded Lipschitz domains by shortened chart cylinders.** The frontier of
a bounded Lipschitz domain with constant `L` is covered by finitely many shortened cylinders
`normalCylinder (a x - 2 * L * b x) (b x)` of Lipschitz boundary charts, centred at frontier points,
with the common constant `L` and radii satisfying `2 * L * b x < a x`. -/
theorem IsLipschitzDomainWith.exists_finset_isLipschitzChartWith_two_mul_lt_cover
    [FiniteDimensional ℝ E] (h : Omega.IsLipschitzDomainWith L) (hb : Bornology.IsBounded Omega) :
    ∃ (t : Finset (WithLp 2 (ℝ × E))) (e : WithLp 2 (ℝ × E) → WithLp 2 (ℝ × E) ≃ᵃⁱ[ℝ]
        WithLp 2 (ℝ × E)) (φ : WithLp 2 (ℝ × E) → E → ℝ) (a b : WithLp 2 (ℝ × E) → ℝ),
      (∀ x ∈ t, x ∈ frontier Omega ∧ e x x = 0 ∧
        Omega.IsLipschitzChartWith L (e x) (φ x) (a x) (b x) ∧ 2 * L * b x < a x) ∧
        frontier Omega ⊆ ⋃ x ∈ t, e x ⁻¹' normalCylinder (a x - 2 * L * b x) (b x) :=
  (isCompact_of_isClosed_isBounded isClosed_frontier
    (hb.closure.subset frontier_subset_closure)).exists_finset_isLipschitzChartWith_two_mul_lt_cover
    h.2

end Cover

/-- A uniform Lipschitz bound gives the pointwise Lipschitz-domain condition. -/
theorem IsLipschitzDomainWith.isLipschitzDomain
    {Omega : Set (WithLp 2 (ℝ × E))} {L : ℝ≥0} (h : Omega.IsLipschitzDomainWith L) :
    Omega.IsLipschitzDomain E := by
  intro x hx
  obtain ⟨e, φ, a, b, hex, hchart⟩ := h.2 x hx
  exact ⟨e, φ, L, a, b, hchart.toIsLipschitzChart, hex⟩

/-- Pointwise Lipschitz domains allow the graph bound to vary with the frontier point. -/
theorem isLipschitzDomain_iff_forall_exists_isLipschitzDomainAtWith
    {Omega : Set F} :
    Omega.IsLipschitzDomain E ↔
      ∀ x ∈ frontier Omega, ∃ L, Omega.IsLipschitzDomainAtWith (E := E) L x := by
  constructor
  · intro h x hx
    obtain ⟨e, φ, L, a, b, hchart, hex⟩ := h x hx
    refine ⟨L, e, φ, a, b, hex, hchart.isLipschitzChartWith ?_⟩
    have heq := hchart.fst_apply_eq_of_mem_frontier hx
      (hex ▸ zero_mem_normalCylinder hchart.height_pos hchart.radius_pos)
    simpa [hex] using heq.symm
  · intro h x hx
    obtain ⟨L, e, φ, a, b, hex, hchart⟩ := h x hx
    exact ⟨e, φ, L, a, b, hchart.toIsLipschitzChart, hex⟩

end Set

namespace TauCeti

open Metric Set
open scoped NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {Omega : Set F} {L : ℝ≥0}
  {e : F ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E)} {φ : E → ℝ} {a b : ℝ}

/-- The points whose chart coordinates lie strictly above the graph of `φ`. -/
def chartEpigraph (e : F ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E))
    (hφ : Continuous φ) : TopologicalSpace.Opens F :=
  TopologicalSpace.Opens.comap ⟨e, e.continuous⟩ (normalEpigraph ⟨φ, hφ⟩)

/-- Membership in the chart epigraph is the graph inequality in chart coordinates. -/
@[simp]
theorem mem_chartEpigraph {hφ : Continuous φ} {x : F} :
    x ∈ chartEpigraph e hφ ↔ φ (e x).snd < (e x).fst :=
  mem_normalEpigraph _ _

/-- The epigraph in chart coordinates is the inverse-chart preimage of the chart epigraph. -/
theorem coe_normalEpigraph_eq_preimage (e : F ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E))
    (hφ : Continuous φ) :
    (normalEpigraph ⟨φ, hφ⟩ : Set (WithLp 2 (ℝ × E))) =
      e.symm ⁻¹' chartEpigraph e hφ := by
  ext x
  simp [chartEpigraph]

/-- On a cutoff supported in the chart cylinder, the chart epigraph lies in the domain. -/
theorem chartEpigraph_inter_tsupport_subset
    (h : Omega.IsLipschitzChartWith L e φ a b) {ψ : F → ℝ}
    (hs : tsupport ψ ⊆ e ⁻¹' normalCylinder a b) :
    (chartEpigraph e h.lipschitzWith.continuous : Set _) ∩ tsupport ψ ⊆ Omega :=
  fun _ hx => (h.mem_iff (hs hx.2)).2 (mem_chartEpigraph.1 hx.1)

/-- On a cutoff supported in the chart cylinder, the domain lies in the chart epigraph. -/
theorem inter_tsupport_subset_chartEpigraph
    (h : Omega.IsLipschitzChartWith L e φ a b) {ψ : F → ℝ}
    (hs : tsupport ψ ⊆ e ⁻¹' normalCylinder a b) :
    Omega ∩ tsupport ψ ⊆ chartEpigraph e h.lipschitzWith.continuous :=
  fun _ hx => mem_chartEpigraph.2 ((h.mem_iff (hs hx.2)).1 hx.1)

/-- A graph that is Lipschitz only on the tangential ball of a boundary chart can be extended
to a global Lipschitz graph defining the same chart, with the same constant and radii. -/
theorem exists_isLipschitzChartWith_of_lipschitzOnWith (ha : 0 < a) (hb : 0 < b)
    (hφ0 : φ 0 = 0) (hφ : LipschitzOnWith L φ (ball 0 b))
    (hgraph : ∀ z ∈ normalCylinder a b, (e.symm z ∈ Omega ↔ φ z.snd < z.fst)) :
    ∃ ψ : E → ℝ, EqOn φ ψ (ball 0 b) ∧ Omega.IsLipschitzChartWith L e ψ a b := by
  obtain ⟨ψ, hψ, heq⟩ := hφ.extend_real
  refine ⟨ψ, heq, (isLipschitzChartWith_iff ..).mpr ⟨ha, hb, ?_, hψ, ?_⟩⟩
  · rw [← heq (mem_ball_self hb), hφ0]
  · intro z hz
    rw [← heq (by simpa only [mem_ball, dist_zero_right] using
      (mem_normalCylinder.mp hz).2.2)]
    exact hgraph z hz

end TauCeti

end
