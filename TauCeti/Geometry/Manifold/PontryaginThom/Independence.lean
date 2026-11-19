/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.PontryaginThom.Basic
import Mathlib.Analysis.Calculus.MeanValue
import TauCeti.Topology.Compactness.Normed
import TauCeti.Topology.OpenPartialHomeomorph.Basic

/-!
# Independence of the Pontryagin–Thom collapse from the tube

The Pontryagin–Thom collapse `M → OnePoint V` of a framed submanifold is built from a chosen
framed tube `τ : S × V → M` around it (`TauCeti.pontryaginThomCollapse`). This file shows that, up
to homotopy, it depends on the tube only through the framing it induces along the core.

Let `τ₀` and `τ₁` be framed tubes around the same map `f : S → M`, with `S` compact, `M`
Hausdorff and `V` a real normed space. Suppose that near the core `τ₁` reads in `τ₀` as
`τ₁ (x, v) = τ₀ (x', A x v + o(‖v‖))`, uniformly in `x`, for a continuous family `A` of linear
automorphisms of `V` (`TauCeti.HasTransitionFDeriv`). For tubes whose transition is `C¹` in the
fibre direction, `A x` is the fibre derivative of the normal coordinate of `τ₀⁻¹ ∘ τ₁` at `(x, 0)`
(`TauCeti.HasTransitionFDeriv.of_hasFDerivAt`). Then:

* the collapse of `τ₁` is homotopic to the collapse of `τ₀` reframed by `A`, the tube
  `(x, v) ↦ τ₀ (x, A x v)`
  (`TauCeti.IsFramedTube.pontryaginThomCollapseMap_homotopic_comp_prodUnitsHomeomorph`);
* if `A` is homotopic to the identity through linear automorphisms, the collapses of `τ₁` and `τ₀`
  are homotopic (`TauCeti.IsFramedTube.pontryaginThomCollapseMap_homotopic`), and so are their
  collapses onto the sphere `Sᵏ` for `V = ℝᵏ`
  (`TauCeti.IsFramedTube.pontryaginThomSphereMap_homotopic`).

Together with the invariance under homotopies of the framing
(`TauCeti.pontryaginThomCollapseMap_comp_prodUnitsHomeomorph_homotopic`), the homotopy class of
the collapse depends only on the homotopy class of the framing of the core read to first order.
Some condition on `A` is needed: reframing a tube with fibre `ℝᵏ`, `k ≥ 1`, by a reflection of
`ℝᵏ` in a hyperplane composes its collapse with a reflection of `Sᵏ`, which has degree `-1`.

The proof has two steps.

* **Shrinking.** The radial compressions `v ↦ (1 + s ‖v‖ / r)⁻¹ • v`, `s ∈ [0, 1]`, form an
  isotopy of tubes from `τ₁` to its reparametrized restriction to `S × B(0, r)`, so the collapse
  does not change up to homotopy. For small `r` the shrunk tube lies in the image of `τ₀`, and it
  is `τ₀ ∘ g` for an open embedding `g` of `S × V` fixing the zero section.
* **The Alexander trick.** The rescalings `g_t (x, v) = ((g (x, t v)).1, t⁻¹ (g (x, t v)).2)`,
  `t ∈ (0, 1]`, extended at `t = 0` by the linearization `(x, v) ↦ (x, A x v)`, form an isotopy
  of open embeddings of `S × V`. Continuity at `t = 0` is the uniform first-order estimate for
  `g`, and for its inverse, which follows from it by compactness of `S`. So `τ₀ ∘ g` is isotopic
  to the reframed tube, and their collapses are homotopic
  (`TauCeti.pontryaginThomCollapseMap_homotopic`).

Only the topology of the tubes and the first-order estimate along the core are used; no smooth
structure on `S` or `M` is needed.

## Main definitions and results

* `TauCeti.HasTransitionFDeriv τ₀ τ₁ A`: the transition from `τ₁` to `τ₀` has fibre derivative
  `A` along the core.
* `TauCeti.HasTransitionFDeriv.of_hasFDerivAt`: a transition that is `C¹` in the fibre direction
  has a fibre derivative along the core.
* `TauCeti.IsFramedTube.pontryaginThomCollapseMap_homotopic_comp_prodUnitsHomeomorph`: the collapse
  of `τ₁` is that of `τ₀` reframed by `A`, up to homotopy.
* `TauCeti.IsFramedTube.pontryaginThomCollapseMap_homotopic`,
  `TauCeti.IsFramedTube.pontryaginThomSphereMap_homotopic`: tubes whose transition derivative is
  homotopic to the identity have homotopic collapses.

## References

* J. W. Milnor, *Topology from the Differentiable Viewpoint*, University Press of Virginia,
  1965, §7.
* M. W. Hirsch, *Differential Topology*, Graduate Texts in Mathematics 33, Springer, 1976,
  Chapter 4, §5 (uniqueness of tubular neighbourhoods, through the rescaling of an embedding to
  its derivative along the zero section).
-/

public section

open Function Set Topology Filter Metric OnePoint

namespace TauCeti

variable {S M V : Type*} [TopologicalSpace S] [TopologicalSpace M] [NormedAddCommGroup V]
  [NormedSpace ℝ V]

/-! ### Shrinking a tube into a ball -/

/-- The radial compression `v ↦ (1 + s ‖v‖ / r)⁻¹ • v`. For `0 ≤ s` and `0 < r` it is a
homeomorphism of `V` onto the open set `{u | s ‖u‖ < r}`, the ball of radius `r / s` when `s > 0`,
with inverse `TauCeti.radialExpand r s`. -/
private noncomputable def radialShrink (r s : ℝ) (v : V) : V :=
  (1 + s * ‖v‖ / r)⁻¹ • v

/-- The inverse `u ↦ (1 - s ‖u‖ / r)⁻¹ • u` of the radial compression on `{u | s ‖u‖ < r}`. -/
private noncomputable def radialExpand (r s : ℝ) (u : V) : V :=
  (1 - s * ‖u‖ / r)⁻¹ • u

variable {r s : ℝ}

omit [NormedSpace ℝ V] in
private theorem radialShrink_factor_pos (hr : 0 < r) (hs : 0 ≤ s) (v : V) :
    0 < 1 + s * ‖v‖ / r := by
  positivity

private theorem norm_radialShrink (hr : 0 < r) (hs : 0 ≤ s) (v : V) :
    ‖radialShrink r s v‖ = ‖v‖ / (1 + s * ‖v‖ / r) := by
  rw [radialShrink, norm_smul, norm_inv, Real.norm_of_nonneg (radialShrink_factor_pos hr hs v).le,
    inv_mul_eq_div]

private theorem mul_norm_radialShrink_lt (hr : 0 < r) (hs : 0 ≤ s) (v : V) :
    s * ‖radialShrink r s v‖ < r := by
  have h := radialShrink_factor_pos hr hs v
  rw [norm_radialShrink hr hs, ← mul_div_assoc, div_lt_iff₀ h, mul_add, mul_one,
    mul_div_cancel₀ _ hr.ne']
  linarith

private theorem radialExpand_radialShrink (hr : 0 < r) (hs : 0 ≤ s) (v : V) :
    radialExpand r s (radialShrink r s v) = v := by
  have h := radialShrink_factor_pos hr hs v
  have key : 1 - s * ‖radialShrink r s v‖ / r = (1 + s * ‖v‖ / r)⁻¹ := by
    rw [norm_radialShrink hr hs]
    field_simp
    ring
  rw [radialExpand, key, inv_inv, radialShrink, smul_smul, mul_inv_cancel₀ h.ne', one_smul]

private theorem radialShrink_radialExpand (hr : 0 < r) {u : V} (hu : s * ‖u‖ < r) :
    radialShrink r s (radialExpand r s u) = u := by
  have h : 0 < 1 - s * ‖u‖ / r := by
    rw [sub_pos, div_lt_one hr]
    exact hu
  have key : 1 + s * ‖radialExpand r s u‖ / r = (1 - s * ‖u‖ / r)⁻¹ := by
    rw [radialExpand, norm_smul, norm_inv, Real.norm_of_nonneg h.le]
    field_simp
    ring
  rw [radialShrink, key, inv_inv, radialExpand, smul_smul, mul_inv_cancel₀ h.ne', one_smul]

/-- The compression moves `v` by at most `‖v‖² / r`; it is tangent to the identity at `0`. -/
private theorem norm_radialShrink_one_sub_le (hr : 0 < r) (v : V) :
    ‖radialShrink r 1 v - v‖ ≤ ‖v‖ ^ 2 / r := by
  set a := 1 + 1 * ‖v‖ / r with ha
  have ha1 : 1 ≤ a := le_add_of_nonneg_right (by positivity)
  have ha0 : 0 < a := zero_lt_one.trans_le ha1
  have h1 : 1 - a⁻¹ = (a - 1) / a := by field_simp
  have hb : 1 - a⁻¹ ≤ ‖v‖ / r := by
    rw [h1]
    calc (a - 1) / a ≤ a - 1 := div_le_self (by linarith) ha1
      _ = ‖v‖ / r := by rw [ha]; ring
  have hv : radialShrink r 1 v - v = (a⁻¹ - 1) • v := by rw [radialShrink, ← ha, sub_smul, one_smul]
  rw [hv, norm_smul, Real.norm_eq_abs, abs_sub_comm,
    abs_of_nonneg (by rw [h1]; exact div_nonneg (by linarith) ha0.le)]
  calc (1 - a⁻¹) * ‖v‖ ≤ ‖v‖ / r * ‖v‖ := mul_le_mul_of_nonneg_right hb (norm_nonneg v)
    _ = ‖v‖ ^ 2 / r := by ring

private theorem norm_radialShrink_le (hr : 0 < r) (hs : 0 ≤ s) (v : V) :
    ‖radialShrink r s v‖ ≤ ‖v‖ := by
  rw [norm_radialShrink hr hs]
  exact div_le_self (norm_nonneg v) (le_add_of_nonneg_right (by positivity))

private theorem continuous_radialShrink (hr : 0 < r) {X : Type*} [TopologicalSpace X]
    {s : X → ℝ} {v : X → V} (hs : Continuous s) (hs₀ : ∀ x, 0 ≤ s x) (hv : Continuous v) :
    Continuous fun x ↦ radialShrink r (s x) (v x) :=
  ((continuous_const.add ((hs.mul hv.norm).div_const r)).inv₀
    fun x ↦ (radialShrink_factor_pos hr (hs₀ x) (v x)).ne').smul hv

private theorem continuousOn_radialExpand (hr : 0 < r) {X : Type*} [TopologicalSpace X]
    {s : X → ℝ} {u : X → V} (hs : Continuous s) (hu : Continuous u) :
    ContinuousOn (fun x ↦ radialExpand r (s x) (u x)) {x | s x * ‖u x‖ < r} := by
  refine (ContinuousOn.inv₀ (f := fun x ↦ 1 - s x * ‖u x‖ / r) (by fun_prop)
    fun x hx ↦ ?_).smul hu.continuousOn
  have : s x * ‖u x‖ / r < 1 := (div_lt_one hr).2 hx
  exact (sub_pos.2 this).ne'

/-- For `0 ≤ s`, the fibrewise compression `(x, v) ↦ (x, (1 + s ‖v‖ / r)⁻¹ • v)` is an open
embedding of `S × V`. -/
private theorem isOpenEmbedding_prodMap_radialShrink (hr : 0 < r) (hs : 0 ≤ s) :
    IsOpenEmbedding (Prod.map id (radialShrink r s) : S × V → S × V) :=
  IsOpenEmbedding.id.prodMap <| IsOpenEmbedding.of_continuousOn_inverse (W := {u | s * ‖u‖ < r})
    (continuous_radialShrink hr continuous_const (fun _ ↦ hs) continuous_id)
    (isOpen_lt (by fun_prop) continuous_const)
    (continuousOn_radialExpand hr continuous_const continuous_id)
    (mul_norm_radialShrink_lt hr hs) (radialExpand_radialShrink hr hs)
    fun _ hu ↦ radialShrink_radialExpand hr hu

/-- The compressions for `s ∈ [0, 1]` form an isotopy of open embeddings: the total map
`(s, x, v) ↦ (s, x, (1 + s ‖v‖ / r)⁻¹ • v)` is an open embedding of `[0, 1] × (S × V)`. -/
private theorem isOpenEmbedding_radialShrink_family (hr : 0 < r) :
    IsOpenEmbedding fun q : unitInterval × (S × V) ↦ (q.1, (q.2.1, radialShrink r q.1 q.2.2)) := by
  refine IsOpenEmbedding.of_continuousOn_inverse (W := {q | (q.1 : ℝ) * ‖q.2.2‖ < r})
    (g := fun q ↦ (q.1, (q.2.1, radialExpand r q.1 q.2.2)))
    (continuous_fst.prodMk (continuous_snd.fst.prodMk (continuous_radialShrink hr
      (continuous_subtype_val.comp continuous_fst) (fun q ↦ q.1.2.1) continuous_snd.snd)))
    (isOpen_lt (by fun_prop) continuous_const)
    (continuous_fst.continuousOn.prodMk (continuous_snd.fst.continuousOn.prodMk
      (continuousOn_radialExpand hr (continuous_subtype_val.comp continuous_fst)
        continuous_snd.snd)))
    (fun q ↦ mul_norm_radialShrink_lt hr q.1.2.1 q.2.2) (fun q ↦ ?_) fun q hq ↦ ?_
  · rw [radialExpand_radialShrink hr q.1.2.1]
  · rw [radialShrink_radialExpand hr hq]

/-- **Shrinking a tube into a ball does not change its collapse up to homotopy.** The tube
`(x, v) ↦ τ (x, (1 + ‖v‖ / r)⁻¹ • v)`, the restriction of `τ` to `S × B(0, r)` reparametrized by a
radial homeomorphism `V ≃ B(0, r)`, has a collapse homotopic to that of `τ`. -/
private theorem pontryaginThomCollapseMap_homotopic_comp_radialShrink [CompactSpace S]
    [T2Space M] {τ : S × V → M} (hτ : IsOpenEmbedding τ) (hr : 0 < r) :
    (pontryaginThomCollapseMap hτ).Homotopic
      (pontryaginThomCollapseMap (hτ.comp (isOpenEmbedding_prodMap_radialShrink (S := S) hr
        zero_le_one))) := by
  refine pontryaginThomCollapseMap_homotopic _ _
    (τ := fun q ↦ τ (q.2.1, radialShrink r q.1 q.2.2))
    ((IsOpenEmbedding.id.prodMap hτ).comp (isOpenEmbedding_radialShrink_family hr))
    (fun p ↦ by simp [radialShrink]) fun p ↦ by rw [comp_apply, Prod.map_apply']; rfl

/-! ### Rescaling a map of `S × V` along the zero section -/

omit [TopologicalSpace S] [TopologicalSpace M] in
/-- A first-order estimate at `t • v` rescales to one at `v`. -/
private theorem norm_inv_smul_sub_le {t : ℝ} (ht : 0 < t) {w v : V} {L : V →L[ℝ] V} {c : ℝ}
    (h : ‖w - L (t • v)‖ ≤ c * ‖t • v‖) : ‖t⁻¹ • w - L v‖ ≤ c * ‖v‖ := by
  have : t⁻¹ • w - L v = t⁻¹ • (w - L (t • v)) := by
    rw [map_smul, smul_sub, inv_smul_smul₀ ht.ne']
  rw [this, norm_smul, norm_inv, Real.norm_of_nonneg ht.le]
  rw [norm_smul, Real.norm_of_nonneg ht.le] at h
  calc t⁻¹ * ‖w - L (t • v)‖ ≤ t⁻¹ * (c * (t * ‖v‖)) := by gcongr
    _ = c * ‖v‖ := by field_simp

/-- The rescaling of a map `h : S × V → S × V` along the zero section, with limit `L` at `t = 0`:
at `(t, x, w)` it is `(h (x, t w)).1, t⁻¹ (h (x, t w)).2` for `t ≠ 0`, and `(x, L x w)` for
`t = 0`. For `t = 1` it is `h`. If `h` fixes the zero section and has fibre derivative `L` along
it, this is continuous: it is the deformation of `h` into its linearization along the zero
section (the Alexander trick). -/
private noncomputable def rescale (h : S × V → S × V) (L : S → V →L[ℝ] V)
    (q : unitInterval × (S × V)) : S × V :=
  if (q.1 : ℝ) = 0 then (q.2.1, L q.2.1 q.2.2)
  else ((h (q.2.1, (q.1 : ℝ) • q.2.2)).1, (q.1 : ℝ)⁻¹ • (h (q.2.1, (q.1 : ℝ) • q.2.2)).2)

omit [TopologicalSpace S] [TopologicalSpace M] in
private theorem rescale_of_eq_zero {h : S × V → S × V} {L : S → V →L[ℝ] V}
    {q : unitInterval × (S × V)} (hq : (q.1 : ℝ) = 0) : rescale h L q = (q.2.1, L q.2.1 q.2.2) := by
  simp [rescale, hq]

omit [TopologicalSpace S] [TopologicalSpace M] in
private theorem rescale_of_ne_zero {h : S × V → S × V} {L : S → V →L[ℝ] V}
    {q : unitInterval × (S × V)} (hq : (q.1 : ℝ) ≠ 0) :
    rescale h L q = ((h (q.2.1, (q.1 : ℝ) • q.2.2)).1,
      (q.1 : ℝ)⁻¹ • (h (q.2.1, (q.1 : ℝ) • q.2.2)).2) := by
  simp [rescale, hq]

omit [TopologicalSpace S] [TopologicalSpace M] in
/-- Away from `t = 0`, rescaling back by `t` recovers the value of `h`. -/
private theorem rescale_smul_eq {h : S × V → S × V} (L : S → V →L[ℝ] V)
    {q : unitInterval × (S × V)} (hq : (q.1 : ℝ) ≠ 0) :
    ((rescale h L q).1, (q.1 : ℝ) • (rescale h L q).2) = h (q.2.1, (q.1 : ℝ) • q.2.2) := by
  rw [rescale_of_ne_zero hq, smul_inv_smul₀ hq]

omit [TopologicalSpace S] [TopologicalSpace M] in
private theorem fst_rescale {h : S × V → S × V} (L : S → V →L[ℝ] V)
    (h0 : ∀ x, h (x, 0) = (x, 0)) (q : unitInterval × (S × V)) :
    (rescale h L q).1 = (h (q.2.1, (q.1 : ℝ) • q.2.2)).1 := by
  by_cases hq : (q.1 : ℝ) = 0
  · rw [rescale_of_eq_zero hq, hq, zero_smul, h0]
  · rw [rescale_of_ne_zero hq]

/-- **The rescaling is continuous.** Let `h` be continuous on an open set `U ⊇ S × {0}`, fixing
the zero section, with fibre derivative `L` along it uniformly in `x`. Then the rescaling of `h`
is continuous on the open set of `(t, x, w)` with `(x, t w) ∈ U`. -/
private theorem continuousOn_rescale {h : S × V → S × V}
    {L : S → V →L[ℝ] V} (hL : Continuous L) {U : Set (S × V)} (hU : IsOpen U)
    (hh : ContinuousOn h U) (h0 : ∀ x, h (x, 0) = (x, 0))
    (hest : ∀ ε > 0, ∃ δ > 0, ∀ x v, (x, v) ∈ U → ‖v‖ < δ → ‖(h (x, v)).2 - L x v‖ ≤ ε * ‖v‖) :
    ContinuousOn (rescale h L) {q | (q.2.1, (q.1 : ℝ) • q.2.2) ∈ U} := by
  have hcU : Continuous fun q : unitInterval × (S × V) ↦ (q.2.1, (q.1 : ℝ) • q.2.2) := by fun_prop
  have hW : IsOpen {q : unitInterval × (S × V) | (q.2.1, (q.1 : ℝ) • q.2.2) ∈ U} :=
    hU.preimage hcU
  have hhc : ContinuousOn (fun q : unitInterval × (S × V) ↦ h (q.2.1, (q.1 : ℝ) • q.2.2))
    {q | (q.2.1, (q.1 : ℝ) • q.2.2) ∈ U} := hh.comp hcU.continuousOn fun _ hq ↦ hq
  refine hW.continuousOn_iff.2 fun q hq ↦ ?_
  -- The first component is the first component of `h (x, t w)`, also at `t = 0`.
  have h₁ : ContinuousAt (fun p ↦ (rescale h L p).1) q := by
    simp_rw [fst_rescale L h0]
    exact (continuous_fst.comp_continuousOn hhc).continuousAt (hW.mem_nhds hq)
  suffices h₂ : ContinuousAt (fun p ↦ (rescale h L p).2) q from h₁.prodMk h₂
  by_cases ht : (q.1 : ℝ) = 0
  · -- At `t = 0` the second component converges to `L x w` by the uniform estimate.
    rw [ContinuousAt, rescale_of_eq_zero ht]
    have hL' : ContinuousAt (fun p : unitInterval × (S × V) ↦ L p.2.1 p.2.2) q := by fun_prop
    suffices h₀ : Tendsto (fun p ↦ (rescale h L p).2 - L p.2.1 p.2.2) (𝓝 q) (𝓝 0) by
      simpa using h₀.add hL'
    refine Metric.tendsto_nhds.2 fun ε hε ↦ ?_
    obtain ⟨δ, hδ, hδε⟩ := hest (ε / 2 / (‖q.2.2‖ + 1)) (by positivity)
    have hδ' : (q.1 : ℝ) * ‖q.2.2‖ < δ := by simpa [ht] using hδ
    filter_upwards [hW.mem_nhds hq, (isOpen_lt (f := fun p : unitInterval × (S × V) ↦
        (p.1 : ℝ) * ‖p.2.2‖) (by fun_prop) continuous_const).mem_nhds hδ',
      (isOpen_lt (f := fun p : unitInterval × (S × V) ↦ ‖p.2.2‖) (by fun_prop)
        continuous_const).mem_nhds (lt_add_one ‖q.2.2‖)] with p hpU hpδ hpv
    rw [dist_zero_right]
    by_cases hp : (p.1 : ℝ) = 0
    · rwa [rescale_of_eq_zero hp, sub_self, norm_zero]
    have hp0 : 0 < (p.1 : ℝ) := lt_of_le_of_ne p.1.2.1 (Ne.symm hp)
    rw [rescale_of_ne_zero hp]
    have := hδε p.2.1 _ hpU (by rwa [norm_smul, Real.norm_of_nonneg hp0.le])
    calc ‖(p.1 : ℝ)⁻¹ • (h (p.2.1, (p.1 : ℝ) • p.2.2)).2 - L p.2.1 p.2.2‖
        ≤ ε / 2 / (‖q.2.2‖ + 1) * ‖p.2.2‖ := norm_inv_smul_sub_le hp0 this
      _ ≤ ε / 2 / (‖q.2.2‖ + 1) * (‖q.2.2‖ + 1) := by gcongr
      _ = ε / 2 := div_mul_cancel₀ _ (by positivity)
      _ < ε := half_lt_self hε
  · -- Away from `t = 0` the second component is given by its formula near `q`.
    have hev : (fun p ↦ (rescale h L p).2) =ᶠ[𝓝 q]
        fun p ↦ (p.1 : ℝ)⁻¹ • (h (p.2.1, (p.1 : ℝ) • p.2.2)).2 := by
      filter_upwards [(isOpen_ne_fun (f := fun p : unitInterval × (S × V) ↦ (p.1 : ℝ))
        (by fun_prop) continuous_const).mem_nhds ht] with p hp
      rw [rescale_of_ne_zero hp]
    refine ContinuousAt.congr ?_ hev.symm
    exact ((continuous_subtype_val.comp continuous_fst).continuousAt.inv₀ ht).smul
      ((continuous_snd.comp_continuousOn hhc).continuousAt (hW.mem_nhds hq))

omit [TopologicalSpace S] [TopologicalSpace M] in
/-- Let `B` invert `T` on `v`, with `‖B‖ ≤ K`, let `u` be within `ε' ‖v‖` of `T v` with
`K ε' ≤ 1 / 2`, and let `B'` be within `η` of `B`. Then `v` is within `(2 K² ε' + η) ‖u‖` of
`B' u`. -/
private theorem norm_sub_apply_le_of_apply_eq {T B B' : V →L[ℝ] V} {u v : V} {K ε' η : ℝ}
    (hBT : B (T v) = v) (hB : ‖B‖ ≤ K) (hKε : K * ε' ≤ 1 / 2) (hε' : 0 ≤ ε')
    (hu : ‖u - T v‖ ≤ ε' * ‖v‖) (hη : ‖B' - B‖ ≤ η) :
    ‖v - B' u‖ ≤ (2 * K ^ 2 * ε' + η) * ‖u‖ := by
  have hK : 0 ≤ K := (norm_nonneg _).trans hB
  have hTv : ‖T v‖ ≤ ‖u‖ + ε' * ‖v‖ :=
    (norm_le_insert' (T v) u).trans (by rw [norm_sub_rev]; gcongr)
  -- First, `‖v‖ ≤ 2 K ‖u‖`.
  have hv : ‖v‖ ≤ 2 * K * ‖u‖ := by
    have : ‖v‖ ≤ K * (‖u‖ + ε' * ‖v‖) :=
      calc ‖v‖ = ‖B (T v)‖ := by rw [hBT]
        _ ≤ ‖B‖ * ‖T v‖ := B.le_opNorm _
        _ ≤ K * (‖u‖ + ε' * ‖v‖) := mul_le_mul hB hTv (norm_nonneg _) hK
    nlinarith [norm_nonneg v, norm_nonneg u]
  have key : v - B' u = B (T v - u) + (B - B') u := by
    rw [map_sub, hBT, sub_apply]
    abel
  calc ‖v - B' u‖ ≤ ‖B‖ * ‖T v - u‖ + ‖B - B'‖ * ‖u‖ := by
        rw [key]
        exact norm_add_le_of_le (B.le_opNorm _) ((B - B').le_opNorm _)
    _ ≤ K * (ε' * (2 * K * ‖u‖)) + η * ‖u‖ := by
        rw [norm_sub_rev, norm_sub_rev B]
        gcongr
        exact hu.trans (by gcongr)
    _ = (2 * K ^ 2 * ε' + η) * ‖u‖ := by ring

/-- **The inverse has the inverse fibre derivative.** Let `g` be an open embedding of `S × V`
fixing the zero section, with fibre derivative `A x` along it uniformly in `x`, and let `g'` be an
inverse of `g` on its range. Then `g'` has fibre derivative `(A x)⁻¹` along the zero section,
uniformly in `x`. -/
private theorem exists_norm_inverse_sub_le [CompactSpace S] {g g' : S × V → S × V}
    (hg : IsOpenEmbedding g) (hg' : ContinuousOn g' (range g)) (hg'g : ∀ p, g' (g p) = p)
    (hgg' : ∀ q ∈ range g, g (g' q) = q) (h0 : ∀ x, g (x, 0) = (x, 0))
    {A : S → (V →L[ℝ] V)ˣ} (hA : Continuous A)
    (hest : ∀ ε > 0, ∃ δ > 0, ∀ x v, ‖v‖ < δ → ‖(g (x, v)).2 - (A x : V →L[ℝ] V) v‖ ≤ ε * ‖v‖)
    (ε : ℝ) (hε : 0 < ε) : ∃ δ > 0, ∀ x u, (x, u) ∈ range g → ‖u‖ < δ →
      ‖(g' (x, u)).2 - (↑(A x)⁻¹ : V →L[ℝ] V) u‖ ≤ ε * ‖u‖ := by
  have hAi : Continuous fun x ↦ (↑(A x)⁻¹ : V →L[ℝ] V) := Units.continuous_coe_inv.comp hA
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hAi.continuousOn
  set K := max C 1
  have hK : 0 < K := lt_max_of_lt_right one_pos
  have hAK (x : S) : ‖(↑(A x)⁻¹ : V →L[ℝ] V)‖ ≤ K := (hC x (mem_univ x)).trans (le_max_left _ _)
  set ε' := min (1 / (2 * K)) (ε / (4 * K ^ 2))
  obtain ⟨δ₁, hδ₁, hδ₁ε⟩ := hest ε' (lt_min (by positivity) (by positivity))
  -- Near the zero section, `(A x)⁻¹` changes little between a point and its image under `g`.
  have hO₃ : IsOpen {p : S × V | ‖(↑(A (g p).1)⁻¹ : V →L[ℝ] V) - ↑(A p.1)⁻¹‖ < ε / 2} :=
    isOpen_lt ((hAi.comp (continuous_fst.comp hg.continuous)).sub
      (hAi.comp continuous_fst)).norm continuous_const
  obtain ⟨δ₃, hδ₃, hδ₃A⟩ := isCompact_univ.exists_pos_forall_norm_lt
    (Q := fun (v : V) (x : S) ↦ ‖(↑(A (g (x, v)).1)⁻¹ : V →L[ℝ] V) - ↑(A x)⁻¹‖ < ε / 2)
    fun x _ ↦ (hO₃.preimage continuous_swap).mem_nhds (by simp [h0, hε])
  -- Near the zero section of the range, the inverse `g'` stays near the zero section.
  have hO₂ : IsOpen (range g ∩ g' ⁻¹' {p | ‖p.2‖ < min δ₁ δ₃}) :=
    hg'.isOpen_inter_preimage hg.isOpen_range (isOpen_lt continuous_snd.norm continuous_const)
  obtain ⟨δ₂, hδ₂, hδ₂g⟩ := isCompact_univ.exists_pos_forall_norm_lt
    (Q := fun (u : V) (x : S) ↦ (x, u) ∈ range g ∩ g' ⁻¹' {p | ‖p.2‖ < min δ₁ δ₃})
    fun x _ ↦ (hO₂.preimage continuous_swap).mem_nhds
      ⟨⟨(x, 0), h0 x⟩, by rw [mem_preimage, Prod.swap_prod_mk, ← h0 x, hg'g]; simp [hδ₁, hδ₃]⟩
  refine ⟨δ₂, hδ₂, fun x u hxu hu ↦ ?_⟩
  rcases hp : g' (x, u) with ⟨y, v⟩
  have hgp : g (y, v) = (x, u) := hp ▸ hgg' _ hxu
  have hv : ‖v‖ < min δ₁ δ₃ := by simpa [hp] using (hδ₂g hu x (mem_univ x)).2
  have h₁ := hδ₁ε y v (hv.trans_le (min_le_left _ _))
  have h₃ := hδ₃A (hv.trans_le (min_le_right _ _)) y (mem_univ y)
  simp only [hgp] at h₁
  simp only [hgp] at h₃
  have hBv : (↑(A y)⁻¹ : V →L[ℝ] V) ((A y : V →L[ℝ] V) v) = v := by
    simp [← mul_apply_eq_comp]
  have hKε : K * ε' ≤ 1 / 2 := by
    calc K * ε' ≤ K * (1 / (2 * K)) := by gcongr; exact min_le_left _ _
      _ = 1 / 2 := by field_simp
  have hε'K : 2 * K ^ 2 * ε' ≤ ε / 2 := by
    calc 2 * K ^ 2 * ε' ≤ 2 * K ^ 2 * (ε / (4 * K ^ 2)) := by gcongr; exact min_le_right _ _
      _ = ε / 2 := by field_simp; ring
  calc ‖v - (↑(A x)⁻¹ : V →L[ℝ] V) u‖ ≤ (2 * K ^ 2 * ε' + ε / 2) * ‖u‖ :=
        norm_sub_apply_le_of_apply_eq hBv (hAK y) hKε (by positivity) h₁ h₃.le
    _ ≤ ε * ‖u‖ := by nlinarith [norm_nonneg u]

/-- **The Alexander isotopy.** Let `g` be an open embedding of `S × V` fixing the zero section,
with fibre derivative `A x` along it uniformly in `x`. Then the rescalings of `g`, joined at
`t = 0` to its linearization `(x, v) ↦ (x, A x v)`, form an isotopy of open embeddings: the
total map `(t, x, v) ↦ (t, rescale g A (t, x, v))` is an open embedding. -/
private theorem isOpenEmbedding_rescale [CompactSpace S] [Nonempty S] {g : S × V → S × V}
    (hg : IsOpenEmbedding g) (h0 : ∀ x, g (x, 0) = (x, 0)) {A : S → (V →L[ℝ] V)ˣ}
    (hA : Continuous A)
    (hest : ∀ ε > 0, ∃ δ > 0, ∀ x v, ‖v‖ < δ → ‖(g (x, v)).2 - (A x : V →L[ℝ] V) v‖ ≤ ε * ‖v‖) :
    IsOpenEmbedding fun q : unitInterval × (S × V) ↦
      (q.1, rescale g (fun x ↦ (A x : V →L[ℝ] V)) q) := by
  set g' := (hg.toOpenPartialHomeomorph g).symm
  have hg'g (p : S × V) : g' (g p) = p :=
    IsOpenEmbedding.toOpenPartialHomeomorph_left_inv g hg
  have hgg' (q : S × V) (hq : q ∈ range g) : g (g' q) = q :=
    IsOpenEmbedding.toOpenPartialHomeomorph_right_inv g hg hq
  have hg' : ContinuousOn g' (range g) := by
    simpa using (hg.toOpenPartialHomeomorph g).continuousOn_symm
  have hg'0 (x : S) : g' (x, 0) = (x, 0) := by simpa [h0] using hg'g (x, 0)
  have hcont := continuousOn_rescale (Units.continuous_val.comp hA) isOpen_univ
    hg.continuous.continuousOn h0 fun ε hε ↦ (hest ε hε).imp fun _ ⟨hδ, h⟩ ↦
      ⟨hδ, fun x v _ ↦ h x v⟩
  simp only [mem_univ, ofPred_true, continuousOn_univ] at hcont
  refine IsOpenEmbedding.of_continuousOn_inverse
    (W := {q | (q.2.1, (q.1 : ℝ) • q.2.2) ∈ range g})
    (g := fun q ↦ (q.1, rescale g' (fun x ↦ (↑(A x)⁻¹ : V →L[ℝ] V)) q))
    (continuous_fst.prodMk hcont) (hg.isOpen_range.preimage (by fun_prop))
    (continuous_fst.continuousOn.prodMk (continuousOn_rescale (Units.continuous_coe_inv.comp hA)
      hg.isOpen_range hg' hg'0 fun ε hε ↦
        exists_norm_inverse_sub_le hg hg' hg'g hgg' h0 hA hest ε hε)) (fun q ↦ ?_) (fun q ↦ ?_)
    fun q hq ↦ ?_
  · -- The family stays in the domain of the inverse.
    by_cases ht : (q.1 : ℝ) = 0
    · simp only [mem_ofPred_eq, rescale_of_eq_zero ht, ht, zero_smul]
      exact ⟨(q.2.1, 0), h0 _⟩
    · exact ⟨_, (rescale_smul_eq _ ht).symm⟩
  · -- The inverse family undoes the family.
    refine Prod.ext rfl ?_
    dsimp only
    by_cases ht : (q.1 : ℝ) = 0
    · simp [rescale, ht, ← mul_apply_eq_comp]
    · simp [rescale, ht, hg'g]
  · -- The family undoes the inverse family on its domain.
    refine Prod.ext rfl ?_
    dsimp only
    by_cases ht : (q.1 : ℝ) = 0
    · simp [rescale, ht, ← mul_apply_eq_comp]
    · have hq' : (q.2.1, (q.1 : ℝ) • q.2.2) ∈ range g := hq
      simp [rescale, ht, hgg' _ hq']

/-! ### The derivative of the transition between two tubes -/

/-- The transition from a tube `τ₁` to a tube `τ₀` has **fibre derivative `A` along the core**:
near the core, `τ₁ (x, v) = τ₀ (x', A x v + o(‖v‖))`, uniformly in `x`. Explicitly, for every
`ε > 0` there is `δ > 0` such that for `‖v‖ < δ` the point `τ₁ (x, v)` is `τ₀ p` for some `p` with
`‖p.2 - A x v‖ ≤ ε ‖v‖`. When the transition `τ₀⁻¹ ∘ τ₁` is `C¹` in the fibre direction near the
core and `S` is compact, this holds with `A x` the fibre derivative of its normal coordinate at
`(x, 0)` (`TauCeti.HasTransitionFDeriv.of_hasFDerivAt`). -/
def HasTransitionFDeriv (τ₀ τ₁ : S × V → M) (A : S → V →L[ℝ] V) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x (v : V), ‖v‖ < δ →
    ∃ p : S × V, τ₁ (x, v) = τ₀ p ∧ ‖p.2 - A x v‖ ≤ ε * ‖v‖

omit [TopologicalSpace S] [TopologicalSpace M] in
/-- Unfolding `TauCeti.HasTransitionFDeriv`. -/
theorem hasTransitionFDeriv_iff {τ₀ τ₁ : S × V → M} {A : S → V →L[ℝ] V} :
    HasTransitionFDeriv τ₀ τ₁ A ↔ ∀ ε > 0, ∃ δ > 0, ∀ x (v : V), ‖v‖ < δ →
      ∃ p : S × V, τ₁ (x, v) = τ₀ p ∧ ‖p.2 - A x v‖ ≤ ε * ‖v‖ :=
  Iff.rfl

omit [TopologicalSpace M] in
/-- **A transition that is `C¹` in the fibre direction has a fibre derivative along the core.**
Suppose that `τ₁ (x, v) = τ₀ (φ (x, v))` for `‖v‖ < r`, where `φ` fixes the normal coordinate
`0` and its normal coordinate `w ↦ (φ (x, w)).2` has derivative `D (x, w)` at every `w` of the
ball `B(0, r)`, with `D` continuous on `S × B(0, r)`. If `S` is compact, the transition from `τ₁`
to `τ₀` has fibre derivative `x ↦ D (x, 0)` along the core. -/
theorem HasTransitionFDeriv.of_hasFDerivAt [CompactSpace S] {τ₀ τ₁ : S × V → M}
    {φ : S × V → S × V} {D : S × V → V →L[ℝ] V} (hr : 0 < r)
    (hφ : ∀ x (v : V), ‖v‖ < r → τ₁ (x, v) = τ₀ (φ (x, v))) (hφ0 : ∀ x, (φ (x, 0)).2 = 0)
    (hD : ∀ x (v : V), ‖v‖ < r → HasFDerivAt (fun w ↦ (φ (x, w)).2) (D (x, v)) v)
    (hDc : ContinuousOn D (univ ×ˢ ball 0 r)) :
    HasTransitionFDeriv τ₀ τ₁ fun x ↦ D (x, 0) := by
  intro ε hε
  have h0 (x : S) : (x, (0 : V)) ∈ univ ×ˢ ball (0 : V) r := ⟨trivial, mem_ball_self hr⟩
  -- Near the core, `D` stays within `ε` of its value on the core.
  have hO : IsOpen (univ ×ˢ ball (0 : V) r ∩ (fun p ↦ D p - D (p.1, 0)) ⁻¹' ball 0 ε) :=
    (hDc.sub (hDc.comp (continuous_fst.prodMk continuous_const).continuousOn
      fun p _ ↦ h0 p.1)).isOpen_inter_preimage (isOpen_univ.prod isOpen_ball) isOpen_ball
  obtain ⟨δ, hδ, hδO⟩ := isCompact_univ.exists_pos_forall_norm_lt
    (Q := fun (v : V) (x : S) ↦
      (x, v) ∈ univ ×ˢ ball (0 : V) r ∩ (fun p ↦ D p - D (p.1, 0)) ⁻¹' ball 0 ε)
    fun x _ ↦ (hO.preimage continuous_swap).mem_nhds ⟨h0 x, by simpa using hε⟩
  refine ⟨δ, hδ, fun x v hv ↦ ⟨φ (x, v), hφ x v (mem_ball_zero_iff.1 (hδO hv x trivial).1.2), ?_⟩⟩
  have hball (w : V) (hw : w ∈ ball (0 : V) δ) := hδO (mem_ball_zero_iff.1 hw) x (mem_univ x)
  -- The mean value inequality on the ball `B(0, δ)` bounds the deviation from `D (x, 0)`.
  have := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le'
    (f := fun w ↦ (φ (x, w)).2) (φ := D (x, 0))
    (fun w hw ↦ (hD x w (mem_ball_zero_iff.1 (hball w hw).1.2)).hasFDerivWithinAt)
    (fun w hw ↦ (mem_ball_zero_iff.1 (hball w hw).2).le) (convex_ball (0 : V) δ)
    (mem_ball_self hδ) (mem_ball_zero_iff.2 hv)
  simpa [hφ0] using this

/-! ### Independence of the tube -/

omit [TopologicalSpace M] in
/-- After shrinking `τ₁` into a ball, its transition `g` into `τ₀` keeps the fibre derivative
`A` of the transition of `τ₁` along the core. -/
private theorem exists_norm_transition_sub_le [CompactSpace S] {τ₀ τ₁ : S × V → M}
    (hτ₀ : Injective τ₀) {g : S × V → S × V} (hr : 0 < r)
    (hg : ∀ p, τ₀ (g p) = τ₁ (p.1, radialShrink r 1 p.2)) {A : S → (V →L[ℝ] V)ˣ}
    (hA : Continuous A)
    (hτ : HasTransitionFDeriv τ₀ τ₁ fun x ↦ (A x : V →L[ℝ] V))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ δ > 0, ∀ x v, ‖v‖ < δ → ‖(g (x, v)).2 - (A x : V →L[ℝ] V) v‖ ≤ ε * ‖v‖ := by
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn
    (Units.continuous_val.comp hA).continuousOn
  set K := max C 1
  have hK : 0 < K := lt_max_of_lt_right one_pos
  have hAK (x : S) : ‖(A x : V →L[ℝ] V)‖ ≤ K := (hC x (mem_univ x)).trans (le_max_left _ _)
  obtain ⟨δ₁, hδ₁, h₁⟩ := hτ (ε / 2) (half_pos hε)
  refine ⟨min δ₁ (ε * r / (2 * K)), by positivity, fun x v hv ↦ ?_⟩
  have hvδ₁ : ‖v‖ < δ₁ := hv.trans_le (min_le_left _ _)
  have hvK : ‖v‖ ≤ ε * r / (2 * K) := hv.le.trans (min_le_right _ _)
  obtain ⟨p, hp, hpe⟩ := h₁ x (radialShrink r 1 v)
    ((norm_radialShrink_le hr zero_le_one v).trans_lt hvδ₁)
  rw [show g (x, v) = p from hτ₀ ((hg _).trans hp)]
  have hlin : ‖(A x : V →L[ℝ] V) (radialShrink r 1 v) - (A x : V →L[ℝ] V) v‖ ≤
      ε / 2 * ‖v‖ := by
    rw [← map_sub]
    calc _ ≤ K * (‖v‖ ^ 2 / r) := ((A x : V →L[ℝ] V).le_opNorm _).trans
          (mul_le_mul (hAK x) (norm_radialShrink_one_sub_le hr v) (norm_nonneg _) hK.le)
      _ = K / r * ‖v‖ * ‖v‖ := by ring
      _ ≤ K / r * (ε * r / (2 * K)) * ‖v‖ := by gcongr
      _ = ε / 2 * ‖v‖ := by field_simp
  calc ‖p.2 - (A x : V →L[ℝ] V) v‖
      ≤ ‖p.2 - (A x : V →L[ℝ] V) (radialShrink r 1 v)‖ +
        ‖(A x : V →L[ℝ] V) (radialShrink r 1 v) - (A x : V →L[ℝ] V) v‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ ε / 2 * ‖v‖ + ε / 2 * ‖v‖ :=
        add_le_add (hpe.trans (by gcongr; exact norm_radialShrink_le hr zero_le_one v)) hlin
    _ = ε * ‖v‖ := by ring

/-- **The collapse of a framed tube is the collapse of another one, reframed by the derivative of
the transition.** Let `τ₀` and `τ₁` be framed tubes around the same map `f : S → M`, with compact
`S` and Hausdorff `M`. Suppose that near the core `τ₁` reads in `τ₀` as
`τ₁ (x, v) = τ₀ (x', A x v + o(‖v‖))`, uniformly in `x`, for a continuous family `A` of linear
automorphisms of `V`: the transition from `τ₁` to `τ₀` has fibre derivative `A` along the core.
Then the collapse of `τ₁` is homotopic to that of the tube `(x, v) ↦ τ₀ (x, A x v)`. -/
theorem IsFramedTube.pontryaginThomCollapseMap_homotopic_comp_prodUnitsHomeomorph
    [CompactSpace S] [T2Space M] {f : S → M} {τ₀ τ₁ : S × V → M} (h₁ : IsFramedTube f τ₁)
    (h₀ : IsFramedTube f τ₀) {A : S → (V →L[ℝ] V)ˣ} (hA : Continuous A)
    (hτ : HasTransitionFDeriv τ₀ τ₁ fun x ↦ (A x : V →L[ℝ] V)) :
    (pontryaginThomCollapseMap h₁.isOpenEmbedding).Homotopic
      (pontryaginThomCollapseMap
        (h₀.isOpenEmbedding.comp (prodUnitsHomeomorph A hA).isOpenEmbedding)) := by
  rcases isEmpty_or_nonempty S with hS | hS
  · -- Over an empty core both tubes are empty, and both collapses are constant at `∞`.
    have h (τ : S × V → M) (m : M) : pontryaginThomCollapse τ m = (∞ : OnePoint V) :=
      pontryaginThomCollapse_of_notMem_range (by simp)
    have heq : pontryaginThomCollapseMap h₁.isOpenEmbedding = pontryaginThomCollapseMap
        (h₀.isOpenEmbedding.comp (prodUnitsHomeomorph A hA).isOpenEmbedding) :=
      ContinuousMap.ext fun m ↦ by simp only [coe_pontryaginThomCollapseMap, h]
    exact heq ▸ .refl _
  -- First shrink `τ₁` into the domain of `τ₀`, along a radial compression `ρ` onto `B(0, r)`.
  obtain ⟨r, hr, hτr⟩ := hτ 1 one_pos
  have hρ := isOpenEmbedding_prodMap_radialShrink (S := S) (V := V) hr zero_le_one
  refine (pontryaginThomCollapseMap_homotopic_comp_radialShrink h₁.isOpenEmbedding hr).trans ?_
  have hmem (p : S × V) : τ₁ (p.1, radialShrink r 1 p.2) ∈ range τ₀ := by
    obtain ⟨q, hq, -⟩ := hτr p.1 _ (by simpa using mul_norm_radialShrink_lt hr zero_le_one p.2)
    exact ⟨q, hq.symm⟩
  -- Then `τ₁ ∘ ρ = τ₀ ∘ g` for the transition `g`, an open embedding of `S × V`.
  set g : S × V → S × V := fun p ↦
    (h₀.isOpenEmbedding.toOpenPartialHomeomorph τ₀).symm (τ₁ (p.1, radialShrink r 1 p.2))
  have hτ₀g (p : S × V) : τ₀ (g p) = τ₁ (p.1, radialShrink r 1 p.2) :=
    IsOpenEmbedding.toOpenPartialHomeomorph_right_inv τ₀ h₀.isOpenEmbedding (hmem p)
  have hg : IsOpenEmbedding g := (IsOpenEmbedding.of_comp_iff g h₀.isOpenEmbedding).1 <| by
    convert h₁.isOpenEmbedding.comp hρ using 1
    exact funext hτ₀g
  have hg0 (x : S) : g (x, 0) = (x, 0) :=
    h₀.isOpenEmbedding.injective (by simp [hτ₀g, radialShrink, h₀.apply_zero, h₁.apply_zero])
  -- The Alexander isotopy deforms `τ₀ ∘ g` into the reframed tube `τ₀ ∘ (id × A)`.
  refine (pontryaginThomCollapseMap_homotopic _ _
    (τ := fun q ↦ τ₀ (rescale g (fun x ↦ (A x : V →L[ℝ] V)) q))
    ((IsOpenEmbedding.id.prodMap h₀.isOpenEmbedding).comp (isOpenEmbedding_rescale hg hg0 hA
      (exists_norm_transition_sub_le h₀.isOpenEmbedding.injective hr hτ₀g hA hτ)))
    (fun p ↦ ?_) fun p ↦ ?_).symm
  · simp [rescale]
  · simp [rescale, hτ₀g, Prod.map_apply']

/-- **Independence of the Pontryagin–Thom collapse from the tube.** Let `τ₀` and `τ₁` be framed
tubes around the same map `f : S → M`, with compact `S` and Hausdorff `M`, such that near the core
`τ₁ (x, v) = τ₀ (x', A x v + o(‖v‖))` uniformly in `x`, for a continuous family `A` of linear
automorphisms of `V`. If `A` is homotopic to the identity through linear automorphisms, the
framings of the two tubes agree up to homotopy, and their Pontryagin–Thom collapses are
homotopic. -/
theorem IsFramedTube.pontryaginThomCollapseMap_homotopic [CompactSpace S] [T2Space M]
    {f : S → M} {τ₀ τ₁ : S × V → M} (h₁ : IsFramedTube f τ₁) (h₀ : IsFramedTube f τ₀)
    {A : S → (V →L[ℝ] V)ˣ} (hA : Continuous A)
    (hτ : HasTransitionFDeriv τ₀ τ₁ fun x ↦ (A x : V →L[ℝ] V))
    {B : unitInterval × S → (V →L[ℝ] V)ˣ} (hB : Continuous B) (hB₀ : ∀ x, B (0, x) = A x)
    (hB₁ : ∀ x, B (1, x) = 1) :
    (pontryaginThomCollapseMap h₁.isOpenEmbedding).Homotopic
      (pontryaginThomCollapseMap h₀.isOpenEmbedding) := by
  have e₀ : pontryaginThomCollapseMap
      (h₀.isOpenEmbedding.comp (prodUnitsHomeomorph A hA).isOpenEmbedding) =
      pontryaginThomCollapseMap (h₀.isOpenEmbedding.comp (prodUnitsHomeomorph (fun x ↦ B (0, x))
        (hB.comp (Continuous.prodMk_right 0))).isOpenEmbedding) := by
    ext m
    simp [hB₀]
  have e₁ : pontryaginThomCollapseMap (h₀.isOpenEmbedding.comp (prodUnitsHomeomorph
      (fun x ↦ B (1, x)) (hB.comp (Continuous.prodMk_right 1))).isOpenEmbedding) =
      pontryaginThomCollapseMap h₀.isOpenEmbedding := by
    ext m
    simp only [hB₁, coe_pontryaginThomCollapseMap]
    congr 1
    funext p
    simp
  have h := h₁.pontryaginThomCollapseMap_homotopic_comp_prodUnitsHomeomorph h₀ hA hτ
  rw [e₀] at h
  rw [← e₁]
  exact h.trans
    (pontryaginThomCollapseMap_comp_prodUnitsHomeomorph_homotopic h₀.isOpenEmbedding hB)

/-- **Independence of the collapse onto the sphere from the tube.** For `V = ℝᵏ`, two framed tubes
around the same map whose transition has a fibre derivative `A` along the core that is homotopic
to the identity through linear automorphisms have homotopic collapses onto `Sᵏ`. -/
theorem IsFramedTube.pontryaginThomSphereMap_homotopic {k : ℕ} [CompactSpace S] [T2Space M]
    {f : S → M} {τ₀ τ₁ : S × (Fin k → ℝ) → M} (h₁ : IsFramedTube f τ₁) (h₀ : IsFramedTube f τ₀)
    {A : S → ((Fin k → ℝ) →L[ℝ] (Fin k → ℝ))ˣ} (hA : Continuous A)
    (hτ : HasTransitionFDeriv τ₀ τ₁ fun x ↦ (A x : (Fin k → ℝ) →L[ℝ] (Fin k → ℝ)))
    {B : unitInterval × S → ((Fin k → ℝ) →L[ℝ] (Fin k → ℝ))ˣ} (hB : Continuous B)
    (hB₀ : ∀ x, B (0, x) = A x) (hB₁ : ∀ x, B (1, x) = 1)
    (s₀ : Metric.sphere (0 : EuclideanSpace ℝ (Fin (k + 1))) 1) :
    (pontryaginThomSphereMap h₁.isOpenEmbedding s₀).Homotopic
      (pontryaginThomSphereMap h₀.isOpenEmbedding s₀) := by
  have e {τ : S × (Fin k → ℝ) → M} (hτ : IsOpenEmbedding τ) : pontryaginThomSphereMap hτ s₀ =
      (onePointHomeomorphSphere k s₀ : C(OnePoint (Fin k → ℝ), _)).comp
        (pontryaginThomCollapseMap hτ) :=
    ContinuousMap.ext fun m ↦ by simp [coe_pontryaginThomSphereMap]
  rw [e, e]
  exact (ContinuousMap.Homotopic.refl _).comp
    (h₁.pontryaginThomCollapseMap_homotopic h₀ hA hτ hB hB₀ hB₁)

end TauCeti
