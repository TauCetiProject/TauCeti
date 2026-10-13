/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Affine.Isometry
public import Mathlib.Analysis.Normed.Lp.ProdLp
public import Mathlib.Topology.EMetricSpace.Lipschitz
public import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.Algebra.ConstMulAction

/-!
# Lipschitz domains

A set `Ω` in a real normed space `F` is a *Lipschitz domain* if near each of its boundary
points it is, after a rigid change of coordinates, the region above the graph of a Lipschitz
function. This is the boundary regularity under which the trace and extension theorems for
Sobolev spaces hold, and over which bounded variation functions have traces.

The local model is the Euclidean product `WithLp 2 (ℝ × E)`, whose first coordinate is the
normal direction and whose second ranges over the hyperplane `E`. For `F = ℝⁿ⁺¹` one takes
`E = ℝⁿ`; when no affine isometry `F ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E)` exists, only sets with empty
frontier are Lipschitz domains modelled on `E`.

* `TauCeti.normalCylinder h r` is the open cylinder `{x | |x.fst| < h ∧ ‖x.snd‖ < r}`.
* `TauCeti.IsLipschitzChart Ω e γ K h r` says that the affine isometry
  `e : F ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E)` carries the part of `Ω` inside the cylinder
  `e ⁻¹' normalCylinder h r` onto the part of the cylinder strictly above the graph
  `x.fst = γ x.snd` of the `K`-Lipschitz function `γ : E → ℝ`. The boundary of `Ω` inside the
  cylinder is then the graph (`TauCeti.IsLipschitzChart.image_frontier_inter_normalCylinder`).
* `TauCeti.IsLipschitzDomain E Ω` says that every frontier point of `Ω` is the centre of such a
  chart. Such a set is open (`TauCeti.IsLipschitzDomain.isOpen`).

The graph function is defined and Lipschitz on all of `E`, not only over the base of the
cylinder; by McShane's extension (`LipschitzOnWith.extend_real`) this is no restriction, and it
lets a chart be followed by the global graph-flattening shear `(t, y) ↦ (t - γ y, y)`.

Charts restrict to smaller cylinders (`TauCeti.IsLipschitzChart.mono`) and can be recentred at
any point of their cylinder (`TauCeti.IsLipschitzChart.exists_isLipschitzChart_eq_zero`), so a
chart around one boundary point serves every nearby one. Lipschitz domains are preserved by
affine isometries (`TauCeti.IsLipschitzDomain.image`) and by positive dilations
(`TauCeti.IsLipschitzDomain.smul`), with the Lipschitz constant unchanged. A bounded Lipschitz
domain in a proper space has a finite cover of its frontier by charts with a common Lipschitz
constant (`TauCeti.IsLipschitzDomain.exists_finite_cover`). The region above the graph of any
Lipschitz function is a Lipschitz domain (`TauCeti.isLipschitzDomain_setOf_lt_fst`).

## References

* P. Grisvard, *Elliptic Problems in Nonsmooth Domains*, Definition 1.2.1.1, which uses a box
  in place of the round cylinder.
* L. C. Evans, R. F. Gariepy, *Measure Theory and Fine Properties of Functions*, 2nd ed.,
  §4.3 (Lipschitz domains as the setting for the trace theorem).
-/

public section

namespace TauCeti

open Set Filter Topology
open scoped NNReal Pointwise

variable {E : Type*} [NormedAddCommGroup E]

/-! ### Cylinders and regions above graphs in `ℝ × E` -/

section Cylinder

/-- The open cylinder `{x | |x.fst| < h ∧ ‖x.snd‖ < r}` in the Euclidean product `ℝ × E`,
centred at the origin, of half-height `h` in the normal coordinate and radius `r` in the
hyperplane `E`. -/
def normalCylinder (h r : ℝ) : Set (WithLp 2 (ℝ × E)) :=
  {x | |x.fst| < h ∧ ‖x.snd‖ < r}

@[simp]
theorem mem_normalCylinder {h r : ℝ} {x : WithLp 2 (ℝ × E)} :
    x ∈ normalCylinder h r ↔ |x.fst| < h ∧ ‖x.snd‖ < r :=
  Iff.rfl

/-- The cylinder is open. -/
theorem isOpen_normalCylinder (h r : ℝ) : IsOpen (normalCylinder (E := E) h r) :=
  (isOpen_lt (by fun_prop) continuous_const).and (isOpen_lt (by fun_prop) continuous_const)

/-- A cylinder of positive height and radius contains the origin. -/
theorem zero_mem_normalCylinder {h r : ℝ} (hh : 0 < h) (hr : 0 < r) :
    (0 : WithLp 2 (ℝ × E)) ∈ normalCylinder h r := by
  simp [hh, hr]

/-- The cylinder grows with its height and radius. -/
theorem normalCylinder_mono {h h' r r' : ℝ} (hh : h ≤ h') (hr : r ≤ r') :
    normalCylinder (E := E) h r ⊆ normalCylinder h' r' :=
  fun _ hx => ⟨hx.1.trans_le hh, hx.2.trans_le hr⟩

/-- The frontier of the region strictly above the graph of a continuous function is the
graph. -/
theorem frontier_setOf_lt_fst {γ : E → ℝ} (hγ : Continuous γ) :
    frontier {x : WithLp 2 (ℝ × E) | γ x.snd < x.fst} = {x | x.fst = γ x.snd} := by
  have hopen : IsOpen {x : WithLp 2 (ℝ × E) | γ x.snd < x.fst} :=
    isOpen_lt (by fun_prop) (by fun_prop)
  refine Subset.antisymm
    (fun x hx => (frontier_lt_subset_eq (by fun_prop) (by fun_prop) hx).symm) fun x hx => ?_
  rw [mem_ofPred_eq] at hx
  rw [hopen.frontier_eq, Set.mem_sdiff, mem_ofPred_eq]
  refine ⟨?_, fun h => h.ne' hx⟩
  -- A graph point is the limit of the points `x + (t, 0)` above it, as `t → 0⁺`.
  have hlim : Tendsto (fun t : ℝ => x + WithLp.toLp 2 (t, (0 : E))) (𝓝[>] 0) (𝓝 x) := by
    have hcont : Continuous fun t : ℝ => x + WithLp.toLp 2 (t, (0 : E)) := by fun_prop
    have h0 := (hcont.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi 0))
    rwa [Prod.mk_zero_zero, WithLp.toLp_zero, add_zero] at h0
  refine mem_closure_of_tendsto hlim ?_
  filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
  simp only [WithLp.add_fst, WithLp.add_snd, WithLp.toLp_fst, WithLp.toLp_snd, add_zero, ← hx]
  linarith

variable [NormedSpace ℝ E]

/-- Dilating a cylinder by `c > 0` multiplies its height and radius by `c`. -/
theorem smul_normalCylinder {c : ℝ} (hc : 0 < c) (h r : ℝ) :
    c • normalCylinder (E := E) h r = normalCylinder (c * h) (c * r) := by
  ext x
  simp only [mem_smul_set_iff_inv_smul_mem₀ hc.ne', mem_normalCylinder, WithLp.smul_fst,
    WithLp.smul_snd, smul_eq_mul, abs_mul, norm_smul, Real.norm_eq_abs, abs_inv,
    abs_of_pos hc, inv_mul_lt_iff₀ hc]

end Cylinder

variable [NormedSpace ℝ E] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
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
    have hC : w ∈ normalCylinder h' r' → p + w ∈ normalCylinder h r := fun hw =>
      ⟨by rw [WithLp.add_fst]; linarith [abs_add_le p.fst w.fst, hw.1],
        by rw [WithLp.add_snd]; linarith [norm_add_le p.snd w.snd, hw.2]⟩
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
      IsLipschitzChart Ω e' γ' K h' r' ∧ e' x = 0 :=
  ⟨_, _, _, _, hc.trans_constVAdd (e x) (sub_pos.2 hx.1) (sub_pos.2 hx.2) (by linarith)
    (by linarith), by simp⟩

/-- Transporting a Lipschitz chart along an affine isometry `g : F ≃ᵃⁱ[ℝ] G`. -/
theorem image (hc : IsLipschitzChart Ω e γ K h r) (g : F ≃ᵃⁱ[ℝ] G) :
    IsLipschitzChart (g '' Ω) (g.symm.trans e) γ K h r :=
  { hc with
    image_inter_normalCylinder := by
      simpa only [image_image, AffineIsometryEquiv.coe_trans, Function.comp_apply,
        AffineIsometryEquiv.symm_apply_apply] using hc.image_inter_normalCylinder }

/-- Dilating a Lipschitz chart by a factor `c > 0`: the dilated set `c • Ω` has a chart with
graph function `y ↦ c * γ (c⁻¹ • y)`, the same Lipschitz constant, and the dilated cylinder. -/
theorem exists_isLipschitzChart_smul (hc : IsLipschitzChart Ω e γ K h r) {c : ℝ} (hc0 : 0 < c) :
    ∃ e' : F ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E), (∀ x, e' (c • x) = c • e x) ∧
      IsLipschitzChart (c • Ω) e' (fun y => c * γ (c⁻¹ • y)) K (c * h) (c * r) := by
  -- The dilation `x ↦ c • e (c⁻¹ • x)` is again an affine isometry: it has the linear part of
  -- `e` and the translation part `c • e 0`.
  set e' : F ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E) := e.linearIsometryEquiv.toAffineIsometryEquiv.trans
    (AffineIsometryEquiv.constVAdd ℝ _ (c • e 0)) with he'
  have hlin : ∀ x, e.linearIsometryEquiv x = e x - e 0 := fun x => by
    simpa using e.map_vsub x 0
  have he'_apply : ∀ x, e' (c • x) = c • e x := fun x => by
    simp only [he', AffineIsometryEquiv.coe_trans, Function.comp_apply,
      LinearIsometryEquiv.coe_toAffineIsometryEquiv, AffineIsometryEquiv.coe_constVAdd,
      vadd_eq_add]
    rw [map_smul, hlin, smul_sub]
    abel
  refine ⟨e', he'_apply, mul_pos hc0 hc.height_pos, mul_pos hc0 hc.radius_pos, ?_, ?_⟩
  · refine LipschitzWith.of_dist_le_mul fun y y' => ?_
    calc dist (c * γ (c⁻¹ • y)) (c * γ (c⁻¹ • y'))
        = c * dist (γ (c⁻¹ • y)) (γ (c⁻¹ • y')) := by
          rw [Real.dist_eq, Real.dist_eq, ← mul_sub, abs_mul, abs_of_pos hc0]
      _ ≤ c * (K * dist (c⁻¹ • y) (c⁻¹ • y')) :=
          mul_le_mul_of_nonneg_left (hc.lipschitzWith.dist_le_mul _ _) hc0.le
      _ = K * dist y y' := by
          rw [dist_smul₀, Real.norm_of_nonneg (inv_nonneg.2 hc0.le)]
          field_simp
  · have himage : e' '' (c • Ω) = c • (e '' Ω) := by
      rw [← image_smul, ← image_smul, image_image, image_image]
      simp_rw [he'_apply]
    have hepi : {x : WithLp 2 (ℝ × E) | c * γ (c⁻¹ • x.snd) < x.fst} =
        c • {x : WithLp 2 (ℝ × E) | γ x.snd < x.fst} := by
      ext x
      simp only [mem_smul_set_iff_inv_smul_mem₀ hc0.ne', mem_ofPred_eq, WithLp.smul_fst,
        WithLp.smul_snd, smul_eq_mul, lt_inv_mul_iff₀ hc0]
    rw [himage, hepi, ← smul_normalCylinder hc0, ← smul_set_inter₀ hc0.ne',
      ← smul_set_inter₀ hc0.ne', hc.image_inter_normalCylinder]

end IsLipschitzChart

/-! ### Lipschitz domains -/

variable (E) in
/-- A set `Ω ⊆ F` is a **Lipschitz domain** modelled on `ℝ × E` if every point of its frontier
is the centre of a Lipschitz boundary chart: after an affine isometry
`e : F ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E)` sending the point to the origin, `Ω` is, inside an open cylinder
around the origin, the region above the graph of a Lipschitz function on `E`. -/
def IsLipschitzDomain (Ω : Set F) : Prop :=
  ∀ x ∈ frontier Ω, ∃ (e : F ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E)) (γ : E → ℝ) (K : ℝ≥0) (h r : ℝ),
    IsLipschitzChart Ω e γ K h r ∧ e x = 0

/-- Unfolding `TauCeti.IsLipschitzDomain`. -/
theorem isLipschitzDomain_iff {Ω : Set F} :
    IsLipschitzDomain E Ω ↔ ∀ x ∈ frontier Ω, ∃ (e : F ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E)) (γ : E → ℝ)
      (K : ℝ≥0) (h r : ℝ), IsLipschitzChart Ω e γ K h r ∧ e x = 0 :=
  Iff.rfl

/-- A set is a Lipschitz domain if and only if every frontier point lies in the cylinder of
some Lipschitz chart, not necessarily centred at it. -/
theorem isLipschitzDomain_iff_exists_mem_normalCylinder {Ω : Set F} :
    IsLipschitzDomain E Ω ↔ ∀ x ∈ frontier Ω, ∃ (e : F ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E)) (γ : E → ℝ)
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
theorem isOpen (hΩ : IsLipschitzDomain E Ω) : IsOpen Ω := by
  refine subset_interior_iff_isOpen.1 fun x hxΩ => ?_
  rcases (closure_eq_interior_union_frontier Ω ▸ subset_closure hxΩ :
    x ∈ interior Ω ∪ frontier Ω) with hx | hx
  · exact hx
  obtain ⟨e, γ, K, h, r, hc, hex⟩ := hΩ x hx
  have hxC : e x ∈ normalCylinder h r := hex ▸ zero_mem_normalCylinder hc.height_pos hc.radius_pos
  have habove : γ (e x).snd < (e x).fst :=
    (hc.image_inter_normalCylinder.subset ⟨mem_image_of_mem e hxΩ, hxC⟩).1
  exact absurd (hc.fst_apply_eq_of_mem_frontier hx hxC) habove.ne'

/-- The image of a Lipschitz domain under an affine isometry is a Lipschitz domain. -/
theorem image (hΩ : IsLipschitzDomain E Ω) (g : F ≃ᵃⁱ[ℝ] G) : IsLipschitzDomain E (g '' Ω) := by
  intro y hy
  rw [← g.coe_toHomeomorph, ← g.toHomeomorph.image_frontier, g.coe_toHomeomorph] at hy
  obtain ⟨x, hx, rfl⟩ := hy
  obtain ⟨e, γ, K, h, r, hc, hex⟩ := hΩ x hx
  exact ⟨g.symm.trans e, γ, K, h, r, hc.image g, by simpa using hex⟩

/-- The dilation of a Lipschitz domain by a factor `c > 0` is a Lipschitz domain. -/
theorem smul (hΩ : IsLipschitzDomain E Ω) {c : ℝ} (hc : 0 < c) :
    IsLipschitzDomain E (c • Ω) := by
  intro y hy
  rw [← image_smul, ← (isHomeomorph_smul₀ hc.ne').image_frontier] at hy
  obtain ⟨x, hx, rfl⟩ := hy
  obtain ⟨e, γ, K, h, r, hce, hex⟩ := hΩ x hx
  obtain ⟨e', he', hc'⟩ := hce.exists_isLipschitzChart_smul hc
  exact ⟨e', _, K, _, _, hc', by simp [he', hex]⟩

/-- A bounded Lipschitz domain in a proper space has a finite cover of its frontier by the
cylinders of Lipschitz charts sharing a common Lipschitz constant. -/
theorem exists_finite_cover [ProperSpace F] (hΩ : IsLipschitzDomain E Ω)
    (hb : Bornology.IsBounded Ω) :
    ∃ (K : ℝ≥0) (m : ℕ) (e : Fin m → F ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E)) (γ : Fin m → E → ℝ)
      (h r : Fin m → ℝ), (∀ i, IsLipschitzChart Ω (e i) (γ i) K (h i) (r i)) ∧
        frontier Ω ⊆ ⋃ i, e i ⁻¹' normalCylinder (h i) (r i) := by
  choose e γ K h r hc hex using fun x : frontier Ω => hΩ x x.2
  have hcompact : IsCompact (frontier Ω) :=
    Metric.isCompact_of_isClosed_isBounded isClosed_frontier
      (hb.closure.subset frontier_subset_closure)
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

end IsLipschitzDomain

/-- Being a Lipschitz domain is invariant under affine isometries. -/
@[simp]
theorem isLipschitzDomain_image_iff {Ω : Set F} (g : F ≃ᵃⁱ[ℝ] G) :
    IsLipschitzDomain E (g '' Ω) ↔ IsLipschitzDomain E Ω :=
  ⟨fun hΩ => by simpa [image_image] using hΩ.image g.symm, fun hΩ => hΩ.image g⟩

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
    IsLipschitzDomain E {x : WithLp 2 (ℝ × E) | γ x.snd < x.fst} :=
  isLipschitzDomain_iff_exists_mem_normalCylinder.2 fun x _ =>
    ⟨_, γ, K, |x.fst| + 1, ‖x.snd‖ + 1,
      isLipschitzChart_refl_setOf_lt_fst hγ (by positivity) (by positivity), by simp⟩

end TauCeti
