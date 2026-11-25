/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.LipschitzDomain.Basic

/-!
# Admissible boundary parts of Lipschitz domains

A mixed boundary value problem on a Lipschitz domain `Ω` prescribes a Dirichlet condition on a
part `Γ` of the frontier and a Neumann condition on the rest. For the Sobolev theory of such
problems, for instance the characterization of the functions vanishing on `Γ` by their trace,
the interface between `Γ` and the rest of the frontier must itself be Lipschitz. This file
defines the boundary parts for which this holds, the strong Lipschitz pairs of
Bauer–Pauly–Schomburg.

In a Lipschitz boundary chart `e : F ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E)` of `Ω`, the frontier inside the
chart cylinder is the graph of a Lipschitz function `γ : E → ℝ` over the base `E`. A boundary
part `Γ` is admissible when every frontier point has such a chart in which `Γ` is the part of
the graph lying over an *admissible base* `U ⊆ E`: all of `E`, nothing, or the region strictly
above the graph of a Lipschitz function `β : E' → ℝ` after an affine isometry
`E ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E')`. The model type `E'` of the interface is a parameter, as the model
type `E` of the frontier is for `Set.IsLipschitzDomain`; for `F = ℝⁿ⁺¹` the intended choices
are `E = ℝⁿ` and `E' = ℝⁿ⁻¹`. When `E` is zero-dimensional there is no affine isometry onto
`ℝ × E'`, so only the first two kinds of base occur, as they should for intervals.

The translation by a constant in the graph direction and the side of the interface graph are
absorbed by the affine isometry, so the interface "strictly on one side of a Lipschitz graph of
`n − 1` coordinates, after a linear isometry of the base" is exactly the third kind of base.

Admissibility forces `Γ` to be relatively open in the frontier
(`Set.IsAdmissibleBoundaryPart.exists_isOpen_inter_frontier_eq`). The empty set and the whole
frontier are admissible exactly when `Ω` is a Lipschitz domain. Charts can be shrunk and
recentred, and admissibility is invariant under affine isometries and positive dilations of the
pair `(Ω, Γ)`, as for the domain predicate.

## Main declarations

* `Set.IsAdmissibleBase`: the admissible bases of a boundary chart.
* `Set.IsAdmissibleChart`: a Lipschitz boundary chart of `Ω` in which `Γ` is the part of the
  graph over a given admissible base.
* `Set.IsAdmissibleBoundaryPart`: a part of the frontier with an admissible chart centred at
  every frontier point.
* `Set.isAdmissibleBoundaryPart_iff_exists_mem_normalCylinder`: charts need not be centred.
* `Set.IsAdmissibleBoundaryPart.exists_isOpen_inter_frontier_eq`: admissible boundary parts are
  relatively open in the frontier.
* `Set.isAdmissibleBoundaryPart_empty_iff`, `Set.isAdmissibleBoundaryPart_frontier_iff`: the
  empty part and the whole frontier.
* `Set.isAdmissibleBoundaryPart_image_iff`, `Set.isAdmissibleBoundaryPart_smul_iff`: invariance
  under affine isometries and positive dilations.
* `Set.IsAdmissibleBase.isAdmissibleBoundaryPart_setOf_lt_fst`: the model case, the part of a
  Lipschitz graph over an admissible base, as a boundary part of the region above the graph.

## References

* S. Bauer, D. Pauly, M. Schomburg, *The Maxwell compactness property in bounded weak Lipschitz
  domains with mixed boundary conditions*, SIAM J. Math. Anal. 48 (2016), §2.1.
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

/-! ### Admissible bases -/

/-- A set `U` of the base `E` of a boundary chart is an **admissible base**, with interfaces
modelled on `E'`, if it is all of `E`, empty, or the region strictly above the graph of a
Lipschitz function `β : E' → ℝ` after an affine isometry `ψ : E ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E')`. -/
def IsAdmissibleBase (U : Set E) (E' : Type*) [NormedAddCommGroup E'] [NormedSpace ℝ E'] :
    Prop :=
  U = univ ∨ U = ∅ ∨ ∃ (ψ : E ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E')) (β : E' → ℝ) (K : ℝ≥0),
    LipschitzWith K β ∧ U = ψ ⁻¹' {w | β w.snd < w.fst}

/-- An admissible base written out: all of `E`, empty, or the region above a Lipschitz graph after
an affine isometry. -/
theorem isAdmissibleBase_iff {U : Set E} :
    U.IsAdmissibleBase E' ↔ U = univ ∨ U = ∅ ∨ ∃ (ψ : E ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E')) (β : E' → ℝ)
      (K : ℝ≥0), LipschitzWith K β ∧ U = ψ ⁻¹' {w | β w.snd < w.fst} :=
  Iff.rfl

/-- The whole base is admissible. -/
@[simp]
theorem isAdmissibleBase_univ : (univ : Set E).IsAdmissibleBase E' :=
  Or.inl rfl

/-- The empty base is admissible. -/
@[simp]
theorem isAdmissibleBase_empty : (∅ : Set E).IsAdmissibleBase E' :=
  Or.inr (Or.inl rfl)

/-- The region above a Lipschitz graph, after an affine isometry, is an admissible base. -/
theorem isAdmissibleBase_preimage_setOf_lt_fst (ψ : E ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E')) {β : E' → ℝ}
    {K : ℝ≥0} (hβ : LipschitzWith K β) :
    (ψ ⁻¹' {w | β w.snd < w.fst}).IsAdmissibleBase E' :=
  Or.inr (Or.inr ⟨ψ, β, K, hβ, rfl⟩)

namespace IsAdmissibleBase

variable {U : Set E}

/-- Admissible bases are open. -/
theorem isOpen (hU : U.IsAdmissibleBase E') : IsOpen U := by
  rcases hU with rfl | rfl | ⟨ψ, β, K, hβ, rfl⟩
  · exact isOpen_univ
  · exact isOpen_empty
  · have hβc := hβ.continuous
    exact (isOpen_lt (by fun_prop) (by fun_prop)).preimage ψ.continuous

/-- Translates of admissible bases are admissible. -/
theorem preimage_add_right (hU : U.IsAdmissibleBase E') (p : E) :
    ((· + p) ⁻¹' U).IsAdmissibleBase E' := by
  rcases hU with rfl | rfl | ⟨ψ, β, K, hβ, rfl⟩
  · exact isAdmissibleBase_univ
  · exact isAdmissibleBase_empty
  · convert isAdmissibleBase_preimage_setOf_lt_fst
      ((AffineIsometryEquiv.constVAdd ℝ E p).trans ψ) hβ using 1
    ext y
    simp [add_comm]

/-- Positive dilates of admissible bases are admissible: the dilate of the region above the
graph of `β` is the region above the graph of `y ↦ c * β (c⁻¹ • y)`. -/
theorem smul (hU : U.IsAdmissibleBase E') {c : ℝ} (hc : 0 < c) :
    (c • U).IsAdmissibleBase E' := by
  rcases hU with rfl | rfl | ⟨ψ, β, K, hβ, rfl⟩
  · rw [smul_set_univ₀ hc.ne']
    exact isAdmissibleBase_univ
  · rw [smul_set_empty]
    exact isAdmissibleBase_empty
  · -- The dilated graph is `K`-Lipschitz, as for the dilate of the chart of its epigraph.
    have hβ' : LipschitzWith K fun y => c * β (c⁻¹ • y) :=
      ((isLipschitzChart_refl_setOf_lt_fst hβ one_pos one_pos).smul hc).lipschitzWith
    convert isAdmissibleBase_preimage_setOf_lt_fst (dilateConj c ψ) hβ' using 1
    ext y
    have hy : dilateConj c ψ y = c • ψ (c⁻¹ • y) := by
      rw [← dilateConj_smul, smul_inv_smul₀ hc.ne']
    simp only [mem_smul_set_iff_inv_smul_mem₀ hc.ne', mem_preimage, mem_ofPred_eq, hy,
      WithLp.smul_fst, WithLp.smul_snd, smul_eq_mul, inv_smul_smul₀ hc.ne',
      mul_lt_mul_iff_right₀ hc]

end IsAdmissibleBase

/-! ### Admissible charts -/

/-- An **admissible chart** of a boundary part `Γ` of `Ω`: a Lipschitz boundary chart of `Ω`,
with coordinates `e`, graph `γ` and cylinder `normalCylinder h r`, in which `Γ` inside the
cylinder is the part of the graph lying over the admissible base `U`. -/
structure IsAdmissibleChart (Γ Ω : Set F) (E' : Type*) [NormedAddCommGroup E'] [NormedSpace ℝ E']
    (e : F ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E)) (γ : E → ℝ) (K : ℝ≥0) (h r : ℝ) (U : Set E) : Prop
    extends IsLipschitzChart Ω e γ K h r where
  /-- The base over which `Γ` lies is admissible. -/
  isAdmissibleBase : U.IsAdmissibleBase E'
  /-- Inside the cylinder, `Γ` is the part of the graph over `U`. -/
  image_part_inter_normalCylinder :
    e '' Γ ∩ normalCylinder h r = {z | z.fst = γ z.snd ∧ z.snd ∈ U} ∩ normalCylinder h r

/-- A Lipschitz chart of `Ω` is an admissible chart of a part `Γ` of the frontier if a frontier
point in the cylinder lies in `Γ` exactly when its base coordinate lies in the admissible base
`U`. -/
theorem isAdmissibleChart_of_forall_mem_iff {Γ Ω : Set F} {e : F ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E)}
    {γ : E → ℝ} {K : ℝ≥0} {h r : ℝ} {U : Set E} (hc : IsLipschitzChart Ω e γ K h r)
    (hU : U.IsAdmissibleBase E') (hΓ : Γ ⊆ frontier Ω)
    (hmem : ∀ x ∈ frontier Ω, e x ∈ normalCylinder h r → (x ∈ Γ ↔ (e x).snd ∈ U)) :
    Γ.IsAdmissibleChart Ω E' e γ K h r U where
  toIsLipschitzChart := hc
  isAdmissibleBase := hU
  image_part_inter_normalCylinder := by
    ext z
    constructor
    · rintro ⟨⟨x, hx, rfl⟩, hzC⟩
      exact ⟨⟨hc.fst_apply_eq_of_mem_frontier (hΓ hx) hzC, (hmem x (hΓ hx) hzC).1 hx⟩, hzC⟩
    · rintro ⟨⟨hzγ, hzU⟩, hzC⟩
      obtain ⟨⟨x, hx, rfl⟩, -⟩ :=
        hc.image_frontier_inter_normalCylinder.superset ⟨hzγ, hzC⟩
      exact ⟨⟨x, (hmem x hx hzC).2 hzU, rfl⟩, hzC⟩

namespace IsAdmissibleChart

variable {Γ Ω : Set F} {e : F ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E)} {γ : E → ℝ} {K : ℝ≥0} {h r : ℝ}
  {U : Set E}

/-- A frontier point in the cylinder of an admissible chart lies in `Γ` exactly when its base
coordinate lies in the base `U`. -/
theorem mem_iff_snd_mem (hc : Γ.IsAdmissibleChart Ω E' e γ K h r U) {x : F} (hx : x ∈ frontier Ω)
    (hxC : e x ∈ normalCylinder h r) : x ∈ Γ ↔ (e x).snd ∈ U := by
  rw [← e.injective.mem_set_image]
  constructor
  · exact fun hxΓ => (hc.image_part_inter_normalCylinder.subset ⟨hxΓ, hxC⟩).1.2
  · exact fun hxU => (hc.image_part_inter_normalCylinder.superset
      ⟨⟨hc.fst_apply_eq_of_mem_frontier hx hxC, hxU⟩, hxC⟩).1

/-- An admissible chart restricts to every smaller cylinder. -/
theorem mono (hc : Γ.IsAdmissibleChart Ω E' e γ K h r U) {h' r' : ℝ} (hh' : 0 < h')
    (hr' : 0 < r') (hh : h' ≤ h) (hr : r' ≤ r) : Γ.IsAdmissibleChart Ω E' e γ K h' r' U where
  toIsLipschitzChart := hc.toIsLipschitzChart.mono hh' hr' hh hr
  isAdmissibleBase := hc.isAdmissibleBase
  image_part_inter_normalCylinder := by
    have hsub := normalCylinder_mono (E := E) hh hr
    rw [← inter_eq_right.2 hsub, ← inter_assoc, hc.image_part_inter_normalCylinder, inter_assoc]

/-- A `K`-Lipschitz admissible chart is a `K'`-Lipschitz admissible chart for every `K' ≥ K`. -/
theorem weaken (hc : Γ.IsAdmissibleChart Ω E' e γ K h r U) {K' : ℝ≥0} (hK : K ≤ K') :
    Γ.IsAdmissibleChart Ω E' e γ K' h r U :=
  { hc with toIsLipschitzChart := hc.toIsLipschitzChart.weaken hK }

/-- Recentring an admissible chart at the point `p` of the model: after translating by `-p`,
the graph becomes `y ↦ γ (y + p.snd) - p.fst` and the base becomes the translate
`(· + p.snd) ⁻¹' U`. -/
theorem trans_constVAdd (hc : Γ.IsAdmissibleChart Ω E' e γ K h r U) (p : WithLp 2 (ℝ × E))
    {h' r' : ℝ} (hh' : 0 < h') (hr' : 0 < r') (hh : |p.fst| + h' ≤ h) (hr : ‖p.snd‖ + r' ≤ r) :
    Γ.IsAdmissibleChart Ω E' (e.trans (AffineIsometryEquiv.constVAdd ℝ _ (-p)))
      (fun y => γ (y + p.snd) - p.fst) K h' r' ((· + p.snd) ⁻¹' U) where
  toIsLipschitzChart := hc.toIsLipschitzChart.trans_constVAdd p hh' hr' hh hr
  isAdmissibleBase := hc.isAdmissibleBase.preimage_add_right p.snd
  image_part_inter_normalCylinder := by
    ext w
    have hC := add_mem_normalCylinder (w := w) hh hr
    have key : p + w ∈ e '' Γ ∩ normalCylinder h r ↔
        p + w ∈ {z | z.fst = γ z.snd ∧ z.snd ∈ U} ∩ normalCylinder h r := by
      rw [hc.image_part_inter_normalCylinder]
    simp only [AffineIsometryEquiv.coe_trans, image_comp, AffineIsometryEquiv.coe_constVAdd,
      vadd_eq_add, image_add_left, neg_neg, mem_inter_iff, mem_preimage, mem_ofPred_eq,
      WithLp.add_fst, WithLp.add_snd] at key ⊢
    constructor
    · rintro ⟨hw, hwC⟩
      obtain ⟨hγ, hU⟩ := (key.1 ⟨hw, hC hwC⟩).1
      exact ⟨⟨by rw [add_comm w.snd]; linarith, by rwa [add_comm w.snd]⟩, hwC⟩
    · rintro ⟨⟨hγ, hU⟩, hwC⟩
      refine ⟨(key.2 ⟨⟨?_, by rwa [add_comm p.snd]⟩, hC hwC⟩).1, hwC⟩
      rw [add_comm p.snd]
      linarith

/-- An admissible chart can be recentred at any point of its cylinder, keeping its Lipschitz
constant. -/
theorem exists_isAdmissibleChart_eq_zero (hc : Γ.IsAdmissibleChart Ω E' e γ K h r U) {x : F}
    (hx : e x ∈ normalCylinder h r) :
    ∃ (e' : F ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E)) (γ' : E → ℝ) (h' r' : ℝ) (U' : Set E),
      Γ.IsAdmissibleChart Ω E' e' γ' K h' r' U' ∧ e' x = 0 := by
  have hx' : |(e x).fst| < h ∧ ‖(e x).snd‖ < r := by
    simpa only [mem_normalCylinder, abs_lt, and_assoc] using hx
  exact ⟨_, _, _, _, _, hc.trans_constVAdd (e x) (sub_pos.2 hx'.1) (sub_pos.2 hx'.2)
    (by linarith) (by linarith), by simp⟩

/-- Transporting an admissible chart along an affine isometry `g : F ≃ᵃⁱ[ℝ] G`. -/
theorem image (hc : Γ.IsAdmissibleChart Ω E' e γ K h r U) (g : F ≃ᵃⁱ[ℝ] G) :
    (g '' Γ).IsAdmissibleChart (g '' Ω) E' (g.symm.trans e) γ K h r U where
  toIsLipschitzChart := hc.toIsLipschitzChart.image g
  isAdmissibleBase := hc.isAdmissibleBase
  image_part_inter_normalCylinder := by
    simpa only [image_image, AffineIsometryEquiv.coe_trans, Function.comp_apply,
      AffineIsometryEquiv.symm_apply_apply] using hc.image_part_inter_normalCylinder

/-- Dilating an admissible chart by a factor `c > 0`: the graph becomes
`y ↦ c * γ (c⁻¹ • y)`, the cylinder and the base are dilated, and the Lipschitz constant is
unchanged. -/
theorem smul (hc : Γ.IsAdmissibleChart Ω E' e γ K h r U) {c : ℝ} (hc0 : 0 < c) :
    (c • Γ).IsAdmissibleChart (c • Ω) E' (dilateConj c e) (fun y => c * γ (c⁻¹ • y)) K (c * h)
      (c * r) (c • U) where
  toIsLipschitzChart := hc.toIsLipschitzChart.smul hc0
  isAdmissibleBase := hc.isAdmissibleBase.smul hc0
  image_part_inter_normalCylinder := by
    have himage : dilateConj c e '' (c • Γ) = c • (e '' Γ) := by
      rw [← image_smul, ← image_smul, image_image, image_image]
      simp_rw [dilateConj_smul]
    have hgraph : {z : WithLp 2 (ℝ × E) | z.fst = c * γ (c⁻¹ • z.snd) ∧ z.snd ∈ c • U} =
        c • {z : WithLp 2 (ℝ × E) | z.fst = γ z.snd ∧ z.snd ∈ U} := by
      ext z
      simp only [mem_smul_set_iff_inv_smul_mem₀ hc0.ne', mem_ofPred_eq, WithLp.smul_fst,
        WithLp.smul_snd, smul_eq_mul, inv_mul_eq_iff_eq_mul₀ hc0.ne']
    rw [himage, hgraph, ← smul_normalCylinder hc0, ← smul_set_inter₀ hc0.ne',
      ← smul_set_inter₀ hc0.ne', hc.image_part_inter_normalCylinder]

end IsAdmissibleChart

/-! ### Admissible boundary parts -/

/-- A set `Γ ⊆ F` is an **admissible boundary part** of `Ω`, with frontier modelled on `ℝ × E`
and interfaces modelled on `ℝ × E'`, if it lies in the frontier of `Ω` and every frontier point
of `Ω` is the centre of an admissible chart of `Γ`: a Lipschitz boundary chart of `Ω` in which
`Γ` is the part of the graph over all of the base, over none of it, or over the region strictly
above a Lipschitz graph in the base. These are the strong Lipschitz pairs of
Bauer–Pauly–Schomburg. -/
def IsAdmissibleBoundaryPart (Γ Ω : Set F) (E E' : Type*) [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup E'] [NormedSpace ℝ E'] : Prop :=
  Γ ⊆ frontier Ω ∧ ∀ x ∈ frontier Ω, ∃ (e : F ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E)) (γ : E → ℝ) (K : ℝ≥0)
    (h r : ℝ) (U : Set E), Γ.IsAdmissibleChart Ω E' e γ K h r U ∧ e x = 0

/-- An admissible boundary part written out: a part of the frontier with an admissible chart
centred at every frontier point. -/
theorem isAdmissibleBoundaryPart_iff {Γ Ω : Set F} :
    Γ.IsAdmissibleBoundaryPart Ω E E' ↔ Γ ⊆ frontier Ω ∧ ∀ x ∈ frontier Ω,
      ∃ (e : F ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E)) (γ : E → ℝ) (K : ℝ≥0) (h r : ℝ) (U : Set E),
        Γ.IsAdmissibleChart Ω E' e γ K h r U ∧ e x = 0 :=
  Iff.rfl

/-- A part of the frontier is admissible if and only if every frontier point lies in the
cylinder of some admissible chart, not necessarily centred at it. -/
theorem isAdmissibleBoundaryPart_iff_exists_mem_normalCylinder {Γ Ω : Set F} :
    Γ.IsAdmissibleBoundaryPart Ω E E' ↔ Γ ⊆ frontier Ω ∧ ∀ x ∈ frontier Ω,
      ∃ (e : F ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E)) (γ : E → ℝ) (K : ℝ≥0) (h r : ℝ) (U : Set E),
        Γ.IsAdmissibleChart Ω E' e γ K h r U ∧ e x ∈ normalCylinder h r := by
  refine and_congr_right fun _ => ⟨fun hΓ x hx => ?_, fun hΓ x hx => ?_⟩
  · obtain ⟨e, γ, K, h, r, U, hc, hex⟩ := hΓ x hx
    exact ⟨e, γ, K, h, r, U, hc, hex ▸ zero_mem_normalCylinder hc.height_pos hc.radius_pos⟩
  · obtain ⟨e, γ, K, h, r, U, hc, hxC⟩ := hΓ x hx
    obtain ⟨e', γ', h', r', U', hc', hex⟩ := hc.exists_isAdmissibleChart_eq_zero hxC
    exact ⟨e', γ', K, h', r', U', hc', hex⟩

namespace IsAdmissibleBoundaryPart

variable {Γ Ω : Set F}

/-- An admissible boundary part lies in the frontier. -/
theorem subset_frontier (hΓ : Γ.IsAdmissibleBoundaryPart Ω E E') : Γ ⊆ frontier Ω :=
  hΓ.1

/-- A set with an admissible boundary part is a Lipschitz domain. -/
theorem isLipschitzDomain (hΓ : Γ.IsAdmissibleBoundaryPart Ω E E') : Ω.IsLipschitzDomain E := by
  refine isLipschitzDomain_iff_exists_mem_normalCylinder.2 fun x hx => ?_
  obtain ⟨e, γ, K, h, r, U, hc, hxC⟩ :=
    (isAdmissibleBoundaryPart_iff_exists_mem_normalCylinder.1 hΓ).2 x hx
  exact ⟨e, γ, K, h, r, hc.toIsLipschitzChart, hxC⟩

/-- **Admissible boundary parts are relatively open** in the frontier: in a chart centred at a
point of `Γ`, the frontier points over the open base `U` all belong to `Γ`. -/
theorem exists_isOpen_inter_frontier_eq (hΓ : Γ.IsAdmissibleBoundaryPart Ω E E') :
    ∃ V : Set F, IsOpen V ∧ V ∩ frontier Ω = Γ := by
  have key : ∀ x ∈ Γ, ∃ W : Set F, IsOpen W ∧ x ∈ W ∧ W ∩ frontier Ω ⊆ Γ := by
    intro x hx
    obtain ⟨e, γ, K, h, r, U, hc, hex⟩ := hΓ.2 x (hΓ.1 hx)
    have hxC : e x ∈ normalCylinder h r :=
      hex ▸ zero_mem_normalCylinder hc.height_pos hc.radius_pos
    refine ⟨e ⁻¹' (normalCylinder h r ∩ {z | z.snd ∈ U}),
      ((isOpen_normalCylinder h r).inter
        (hc.isAdmissibleBase.isOpen.preimage (by fun_prop))).preimage e.continuous,
      ⟨hxC, (hc.mem_iff_snd_mem (hΓ.1 hx) hxC).1 hx⟩, ?_⟩
    rintro y ⟨⟨hyC, hyU⟩, hyF⟩
    exact (hc.mem_iff_snd_mem hyF hyC).2 hyU
  choose! W hWo hxW hWΓ using key
  refine ⟨⋃ x ∈ Γ, W x, isOpen_biUnion hWo, Subset.antisymm ?_
    fun x hx => ⟨mem_biUnion hx (hxW x hx), hΓ.1 hx⟩⟩
  rintro y ⟨hy, hyF⟩
  obtain ⟨x, hx, hyx⟩ := mem_iUnion₂.1 hy
  exact hWΓ x hx ⟨hyx, hyF⟩

/-- The image of an admissible boundary part under an affine isometry is admissible. -/
theorem image (hΓ : Γ.IsAdmissibleBoundaryPart Ω E E') (g : F ≃ᵃⁱ[ℝ] G) :
    (g '' Γ).IsAdmissibleBoundaryPart (g '' Ω) E E' := by
  have hfr : frontier (g '' Ω) = g '' frontier Ω := (g.image_frontier Ω).symm
  refine ⟨hfr ▸ image_mono hΓ.1, fun y hy => ?_⟩
  rw [hfr] at hy
  obtain ⟨x, hx, rfl⟩ := hy
  obtain ⟨e, γ, K, h, r, U, hc, hex⟩ := hΓ.2 x hx
  exact ⟨g.symm.trans e, γ, K, h, r, U, hc.image g, by simpa using hex⟩

/-- The dilate of an admissible boundary part by a factor `c > 0` is admissible. -/
theorem smul (hΓ : Γ.IsAdmissibleBoundaryPart Ω E E') {c : ℝ} (hc : 0 < c) :
    (c • Γ).IsAdmissibleBoundaryPart (c • Ω) E E' := by
  have hfr := frontier_smul₀ hc.ne' Ω
  refine ⟨hfr ▸ smul_set_mono hΓ.1, fun y hy => ?_⟩
  rw [hfr, ← image_smul] at hy
  obtain ⟨x, hx, rfl⟩ := hy
  obtain ⟨e, γ, K, h, r, U, hce, hex⟩ := hΓ.2 x hx
  exact ⟨dilateConj c e, _, K, _, _, _, hce.smul hc, by simp [hex]⟩

end IsAdmissibleBoundaryPart

/-- Admissibility of a boundary part is invariant under affine isometries of the pair. -/
@[simp]
theorem isAdmissibleBoundaryPart_image_iff {Γ Ω : Set F} (g : F ≃ᵃⁱ[ℝ] G) :
    (g '' Γ).IsAdmissibleBoundaryPart (g '' Ω) E E' ↔ Γ.IsAdmissibleBoundaryPart Ω E E' :=
  ⟨fun hΓ => by simpa [image_image] using hΓ.image g.symm, fun hΓ => hΓ.image g⟩

/-- Admissibility of a boundary part is invariant under positive dilations of the pair. -/
@[simp]
theorem isAdmissibleBoundaryPart_smul_iff {Γ Ω : Set F} {c : ℝ} (hc : 0 < c) :
    (c • Γ).IsAdmissibleBoundaryPart (c • Ω) E E' ↔ Γ.IsAdmissibleBoundaryPart Ω E E' :=
  ⟨fun hΓ => by simpa [smul_smul, hc.ne'] using hΓ.smul (inv_pos.2 hc), fun hΓ => hΓ.smul hc⟩

/-- **The empty boundary part** is admissible exactly for Lipschitz domains. -/
@[simp]
theorem isAdmissibleBoundaryPart_empty_iff {Ω : Set F} :
    (∅ : Set F).IsAdmissibleBoundaryPart Ω E E' ↔ Ω.IsLipschitzDomain E := by
  refine ⟨IsAdmissibleBoundaryPart.isLipschitzDomain, fun hΩ =>
    isAdmissibleBoundaryPart_iff_exists_mem_normalCylinder.2 ⟨empty_subset _, fun x hx => ?_⟩⟩
  obtain ⟨e, γ, K, h, r, hc, hxC⟩ := isLipschitzDomain_iff_exists_mem_normalCylinder.1 hΩ x hx
  exact ⟨e, γ, K, h, r, ∅, isAdmissibleChart_of_forall_mem_iff hc isAdmissibleBase_empty
    (empty_subset _) fun _ _ _ => by simp, hxC⟩

/-- **The whole frontier** is an admissible boundary part exactly for Lipschitz domains. -/
@[simp]
theorem isAdmissibleBoundaryPart_frontier_iff {Ω : Set F} :
    (frontier Ω).IsAdmissibleBoundaryPart Ω E E' ↔ Ω.IsLipschitzDomain E := by
  refine ⟨IsAdmissibleBoundaryPart.isLipschitzDomain, fun hΩ =>
    isAdmissibleBoundaryPart_iff_exists_mem_normalCylinder.2 ⟨subset_rfl, fun x hx => ?_⟩⟩
  obtain ⟨e, γ, K, h, r, hc, hxC⟩ := isLipschitzDomain_iff_exists_mem_normalCylinder.1 hΩ x hx
  exact ⟨e, γ, K, h, r, univ, isAdmissibleChart_of_forall_mem_iff hc isAdmissibleBase_univ
    subset_rfl fun y hy _ => by simp [hy], hxC⟩

/-- The empty set is an admissible boundary part of every Lipschitz domain. -/
theorem IsLipschitzDomain.isAdmissibleBoundaryPart_empty {Ω : Set F}
    (hΩ : Ω.IsLipschitzDomain E) : (∅ : Set F).IsAdmissibleBoundaryPart Ω E E' :=
  isAdmissibleBoundaryPart_empty_iff.2 hΩ

/-- The frontier of a Lipschitz domain is an admissible boundary part. -/
theorem IsLipschitzDomain.isAdmissibleBoundaryPart_frontier {Ω : Set F}
    (hΩ : Ω.IsLipschitzDomain E) : (frontier Ω).IsAdmissibleBoundaryPart Ω E E' :=
  isAdmissibleBoundaryPart_frontier_iff.2 hΩ

/-- **The model case.** For a Lipschitz function `γ : E → ℝ` and an admissible base `U ⊆ E`, the
part of the graph of `γ` over `U` is an admissible boundary part of the region strictly above
the graph. For `U` the region above a Lipschitz graph in the base, this is the configuration to
which boundary charts reduce a mixed boundary condition near the interface. -/
theorem IsAdmissibleBase.isAdmissibleBoundaryPart_setOf_lt_fst {U : Set E}
    (hU : U.IsAdmissibleBase E') {γ : E → ℝ} {K : ℝ≥0} (hγ : LipschitzWith K γ) :
    {z : WithLp 2 (ℝ × E) | z.fst = γ z.snd ∧ z.snd ∈ U}.IsAdmissibleBoundaryPart
      {z | γ z.snd < z.fst} E E' := by
  have hfr := frontier_setOf_lt_fst hγ.continuous
  refine isAdmissibleBoundaryPart_iff_exists_mem_normalCylinder.2
    ⟨hfr ▸ fun z hz => hz.1, fun x _ => ⟨_, γ, K, |x.fst| + 1, ‖x.snd‖ + 1, U,
      isAdmissibleChart_of_forall_mem_iff
        (isLipschitzChart_refl_setOf_lt_fst hγ (by positivity) (by positivity)) hU
        (hfr ▸ fun z hz => hz.1) fun z hz _ => ?_, ?_⟩⟩
  · rw [hfr] at hz
    simp only [AffineIsometryEquiv.coe_refl, id, mem_ofPred_eq] at hz ⊢
    exact and_iff_right hz
  · exact mem_normalCylinder_abs_add_one x

end Set
