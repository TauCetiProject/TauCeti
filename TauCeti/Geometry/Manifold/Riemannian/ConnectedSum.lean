/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Euclidean.Inversion
public import TauCeti.Geometry.Manifold.ConnectedSum.Smooth
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.OpenSubset
public import TauCeti.Geometry.Manifold.MFDeriv.Opens
public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Restriction
public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Sum
public import TauCeti.Geometry.Manifold.Riemannian.Pullback.Descent

import TauCeti.Analysis.Normed.Group.BallSphere
import TauCeti.Geometry.Manifold.MFDeriv.Sum

/-!
# Gluing Riemannian metrics along the neck of a connected sum

The connected sum `TauCeti.ConnectedSum e₁ e₂` of `M` and `N` removes the centres of the balls
`e₁ : E → M` and `e₂ : E → N` and glues `e₁ v` to `e₂ (inversion 0 1 v)` for `v ≠ 0`. Let `g₁` and
`g₂` be smooth metrics on `M` and `N`, and let `0 ≤ a < b`. Suppose that on the *neck*
`a < ‖v‖ < b` the gluing map `e₂ ∘ inversion 0 1 ∘ e₁⁻¹` carries `g₁` to `g₂`, in the sense that
for all `ξ` and `ζ`

`g₁ (De₁ ξ, De₁ ζ) = g₂ (D(e₂ ∘ inversion 0 1) ξ, D(e₂ ∘ inversion 0 1) ζ)`

at `v`. Then `M # N` carries the metric `Bundle.ContMDiffRiemannianMetric.connectedSum` which is
`g₁` on `M` outside the closed ball `e₁ (closedBall 0 a)` and `g₂` on `N` outside the closed ball
`e₂ (closedBall 0 b⁻¹)`. These two regions cover the connected sum and meet exactly along the neck,
where the two metrics agree. Its scalar curvature at each point is that of `g₁` or of `g₂`; the
consequence for positive scalar curvature is
`Bundle.ContMDiffRiemannianMetric.HasPositiveScalarCurvature.connectedSum`.

The metric is descended (`Bundle.ContMDiffRiemannianMetric.descend`) from the disjoint union of
the restrictions of `g₁` and `g₂` to the two regions, along the map from that disjoint union onto
`M # N`, which is a surjective local diffeomorphism.

The basic example of the neck hypothesis is a cylindrical neck. The metric `⟪ξ, ζ⟫ / ‖v‖ ^ 2` on
`E ∖ {0}` is the product metric `g_S + dt²` of the cylinder `S × ℝ` in the logarithmic polar
coordinates `v = e^t u`, and it is invariant under the inversion
(`EuclideanGeometry.inner_fderiv_inversion_div_dist_sq`). So if `g₁` read through `e₁` is this
cylinder metric for `a < ‖v‖ < b`, and `g₂` read through `e₂` is the cylinder metric for
`b⁻¹ < ‖w‖ < a⁻¹`, the neck hypothesis holds
(`Bundle.ContMDiffRiemannianMetric.inner_mfderiv_inversion_eq_of_cylinder`). In the construction
of Gromov and Lawson a metric of positive scalar curvature is first deformed near a point, keeping
its scalar curvature positive, into a torpedo whose cylindrical end is such a neck; two such
metrics are then joined along their necks as here. That deformation is not carried out here.

## Main definitions

* `Bundle.ContMDiffRiemannianMetric.connectedSum`: the metric on `M # N` glued from `g₁` and `g₂`
  along the neck.

## Main results

* `Bundle.ContMDiffRiemannianMetric.connectedSum_inner_mfderiv_inl` and
  `Bundle.ContMDiffRiemannianMetric.connectedSum_inner_mfderiv_inr`: the glued metric is `g₁` on
  `M` outside `e₁ (closedBall 0 a)` and `g₂` on `N` outside `e₂ (closedBall 0 b⁻¹)`.
* `Bundle.ContMDiffRiemannianMetric.scalarCurvature_connectedSum_inl` and
  `Bundle.ContMDiffRiemannianMetric.scalarCurvature_connectedSum_inr`: its scalar curvature there
  is that of `g₁`, respectively `g₂`.
* `Bundle.ContMDiffRiemannianMetric.range_scalarCurvature_connectedSum_subset`: every value of its
  scalar curvature is a value of the scalar curvature of `g₁` or of `g₂`.
* `Bundle.ContMDiffRiemannianMetric.inner_mfderiv_inversion_eq_of_cylinder`: two cylindrical
  necks satisfy the neck hypothesis.

## References

* M. Gromov, H. B. Lawson, *The classification of simply connected manifolds of positive
  scalar curvature*, Ann. of Math. 111 (1980), 423–434, Theorem A, for the neck construction.
* A. Kosinski, *Differential Manifolds*, Academic Press (1993), Chapter VI, Section 1, for the
  connected sum glued by the inversion.
-/

public section

noncomputable section

open Bundle Set Function Filter Topology TopologicalSpace EuclideanGeometry Metric
open TauCeti TauCeti.ConnectedSum
open scoped ContDiff Manifold

namespace Bundle.ContMDiffRiemannianMetric

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
  {N : Type*} [TopologicalSpace N] [T2Space N] [ChartedSpace H N] [IsManifold I ∞ N]
  {e₁ : E → M} {e₂ : E → N} {a b : ℝ}

/-! ### The two regions and the neck -/

/-- The points of the punctured summands outside the closed balls `e₁ (closedBall 0 a)` and
`e₂ (closedBall 0 b⁻¹)`. -/
private def outer (e₁ : E → M) (e₂ : E → N) (a b : ℝ) : Set (puncture e₁ ⊕ puncture e₂) :=
  {z | Sum.elim (fun x : puncture e₁ ↦ (x : M) ∉ e₁ '' closedBall 0 a)
    (fun y : puncture e₂ ↦ (y : N) ∉ e₂ '' closedBall 0 b⁻¹) z}

private theorem isOpen_outer (h₁ : Continuous e₁) (h₂ : Continuous e₂) :
    IsOpen (outer e₁ e₂ a b) :=
  isOpen_sum_iff.2
    ⟨((isCompact_closedBall 0 a).image h₁).isClosed.isOpen_compl.preimage continuous_subtype_val,
      ((isCompact_closedBall 0 b⁻¹).image h₂).isClosed.isOpen_compl.preimage
        continuous_subtype_val⟩

/-- The two regions, as an open subset of the disjoint union of the punctured summands. -/
private def outerOpens (h₁ : Continuous e₁) (h₂ : Continuous e₂) :
    Opens (puncture e₁ ⊕ puncture e₂) :=
  ⟨outer e₁ e₂ a b, isOpen_outer h₁ h₂⟩

private theorem inl_mem_outerOpens {h₁ : Continuous e₁} {h₂ : Continuous e₂} {x : puncture e₁} :
    .inl x ∈ outerOpens (a := a) (b := b) h₁ h₂ ↔ (x : M) ∉ e₁ '' closedBall 0 a :=
  Iff.rfl

private theorem inr_mem_outerOpens {h₁ : Continuous e₁} {h₂ : Continuous e₂} {y : puncture e₂} :
    .inr y ∈ outerOpens (a := a) (b := b) h₁ h₂ ↔ (y : N) ∉ e₂ '' closedBall 0 b⁻¹ :=
  Iff.rfl

variable (E) in
/-- The neck `a < ‖v‖ < b`. -/
private def neck (a b : ℝ) : Opens E :=
  ⟨{v | a < ‖v‖ ∧ ‖v‖ < b},
    (isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const)⟩

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
private theorem mem_neck {v : E} : v ∈ neck E a b ↔ a < ‖v‖ ∧ ‖v‖ < b :=
  Iff.rfl

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
private theorem ne_zero_of_mem_neck (ha : 0 ≤ a) (w : neck E a b) : w.1 ≠ 0 :=
  norm_pos_iff.1 (ha.trans_lt (mem_neck.1 w.2).1)

section Gluing

variable (g₁ : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
  (g₂ : ContMDiffRiemannianMetric I ∞ E (fun y : N ↦ TangentSpace I y))
  (h₁ : IsOpenEmbedding e₁) (h₂ : IsOpenEmbedding e₂)
  (d₁ : IsLocalDiffeomorph 𝓘(ℝ, E) I ∞ e₁) (d₂ : IsLocalDiffeomorph 𝓘(ℝ, E) I ∞ e₂)

/-- The map onto the connected sum from the two regions. -/
private def outerMap : outerOpens (a := a) (b := b) h₁.continuous h₂.continuous →
    ConnectedSum e₁ e₂ :=
  ConnectedSum.mk e₁ e₂ ∘ Subtype.val

private theorem outerMap_apply (z : outerOpens (a := a) (b := b) h₁.continuous h₂.continuous) :
    outerMap h₁ h₂ z = ConnectedSum.mk e₁ e₂ z.1 :=
  rfl

include d₁ d₂ in
private theorem isLocalDiffeomorph_outerMap :
    letI := ConnectedSum.chartedSpace (H := H) h₁ h₂
    IsLocalDiffeomorph I I (∞ + 1) (outerMap (a := a) (b := b) h₁ h₂) :=
  letI := ConnectedSum.chartedSpace (H := H) h₁ h₂
  fun z ↦ (TauCeti.isLocalDiffeomorph_subtype_val z).comp
    (hg := isLocalDiffeomorph_mk (n := ⊤) h₁ h₂ d₁ d₂ z.1)

/-- The two regions cover the connected sum. -/
private theorem outerMap_surjective (ha : 0 ≤ a) (hab : a < b) :
    Surjective (outerMap (a := a) (b := b) h₁ h₂) := by
  intro p
  obtain ⟨z, rfl⟩ := mk_surjective e₁ e₂ p
  rcases z with ⟨x, hx⟩ | ⟨y, hy⟩
  · by_cases hxa : x ∈ e₁ '' closedBall 0 a
    · -- `x = e₁ v` with `0 < ‖v‖ ≤ a` is glued to `e₂ (inversion 0 1 v)`, which lies outside
      -- `e₂ (closedBall 0 b⁻¹)` as `‖inversion 0 1 v‖ = ‖v‖⁻¹ ≥ a⁻¹ > b⁻¹`.
      obtain ⟨v, hv, rfl⟩ := hxa
      have hv0 : v ≠ 0 := fun h ↦ mem_puncture.1 hx (by rw [h])
      have hy : e₂ (inversion 0 1 v) ∈ puncture e₂ := apply_inversion_mem_puncture h₂.injective hv0
      refine ⟨⟨.inr ⟨_, hy⟩, inr_mem_outerOpens.2 ?_⟩, ?_⟩
      · rw [h₂.injective.apply_notMem_image_closedBall_zero_iff,
          inv_lt_norm_inversion_iff (ha.trans_lt hab) hv0]
        exact (mem_closedBall_zero_iff.1 hv).trans_lt hab
      · rw [outerMap_apply, mk_inl, mk_inr]
        exact (inl_eq_inr v hv0 hx hy).symm
    · exact ⟨⟨.inl ⟨x, hx⟩, hxa⟩, outerMap_apply h₁ h₂ _⟩
  · by_cases hyb : y ∈ e₂ '' closedBall 0 b⁻¹
    · -- `y = e₂ w` with `0 < ‖w‖ ≤ b⁻¹` is glued to `e₁ (inversion 0 1 w)`, which lies outside
      -- `e₁ (closedBall 0 a)` as `‖inversion 0 1 w‖ = ‖w‖⁻¹ ≥ b > a`.
      obtain ⟨w, hw, rfl⟩ := hyb
      have hw0 : w ≠ 0 := fun h ↦ mem_puncture.1 hy (by rw [h])
      have hpos : 0 < ‖w‖ := norm_pos_iff.2 hw0
      have hx : e₁ (inversion 0 1 w) ∈ puncture e₁ := apply_inversion_mem_puncture h₁.injective hw0
      refine ⟨⟨.inl ⟨_, hx⟩, inl_mem_outerOpens.2 ?_⟩, ?_⟩
      · rw [h₁.injective.apply_notMem_image_closedBall_zero_iff, norm_inversion_zero_one]
        have hb : b ≤ ‖w‖⁻¹ := by
          rw [le_inv_comm₀ (ha.trans_lt hab) hpos]
          exact mem_closedBall_zero_iff.1 hw
        exact hab.trans_le hb
      · rw [outerMap_apply, mk_inl, mk_inr]
        exact inl_inversion_eq_inr hw0 hx hy
    · exact ⟨⟨.inr ⟨y, hy⟩, hyb⟩, outerMap_apply h₁ h₂ _⟩

/-- The neck, mapped into the first punctured summand by `e₁`. -/
private def neckPunctureInl (ha : 0 ≤ a) (w : neck E a b) : puncture e₁ :=
  ⟨e₁ w.1, mem_puncture.2 (h₁.injective.ne (ne_zero_of_mem_neck ha w))⟩

/-- The neck, mapped into the second punctured summand by `e₂ ∘ inversion 0 1`. -/
private def neckPunctureInr (ha : 0 ≤ a) (w : neck E a b) : puncture e₂ :=
  ⟨e₂ (inversion 0 1 w.1), apply_inversion_mem_puncture h₂.injective (ne_zero_of_mem_neck ha w)⟩

/-- The neck, mapped into the first region by `e₁`. -/
private def neckInl (ha : 0 ≤ a) (w : neck E a b) :
    outerOpens (a := a) (b := b) h₁.continuous h₂.continuous :=
  ⟨.inl (neckPunctureInl h₁ ha w),
    h₁.injective.apply_notMem_image_closedBall_zero_iff.2 (mem_neck.1 w.2).1⟩

/-- The neck, mapped into the second region by `e₂ ∘ inversion 0 1`. -/
private def neckInr (ha : 0 ≤ a) (w : neck E a b) :
    outerOpens (a := a) (b := b) h₁.continuous h₂.continuous :=
  ⟨.inr (neckPunctureInr h₂ ha w), h₂.injective.apply_notMem_image_closedBall_zero_iff.2 <|
    (inv_lt_norm_inversion_iff (ha.trans_lt ((mem_neck.1 w.2).1.trans (mem_neck.1 w.2).2))
      (ne_zero_of_mem_neck ha w)).2 (mem_neck.1 w.2).2⟩

private theorem coe_neckInl (ha : 0 ≤ a) (w : neck E a b) :
    (neckInl h₁ h₂ ha w).1 = .inl (neckPunctureInl h₁ ha w) :=
  rfl

private theorem coe_neckInr (ha : 0 ≤ a) (w : neck E a b) :
    (neckInr h₁ h₂ ha w).1 = .inr (neckPunctureInr h₂ ha w) :=
  rfl

/-- The two maps of the neck into the regions agree in the connected sum. -/
private theorem outerMap_comp_neckInl (ha : 0 ≤ a) :
    outerMap h₁ h₂ ∘ neckInl h₁ h₂ ha = outerMap (a := a) (b := b) h₁ h₂ ∘ neckInr h₁ h₂ ha :=
  funext fun w ↦ by
    rw [comp_apply, comp_apply, outerMap_apply, outerMap_apply, coe_neckInl, coe_neckInr, mk_inl,
      mk_inr]
    exact inl_eq_inr w.1 (ne_zero_of_mem_neck ha w) _ _

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
include d₁ in
private theorem contMDiff_neckPunctureInl (ha : 0 ≤ a) :
    ContMDiff 𝓘(ℝ, E) I ∞ (neckPunctureInl (b := b) h₁ ha) := fun w ↦
  (ContMDiffAt.subtypeVal_comp_iff (puncture e₁) _ w).mp
    ((d₁.contMDiff.comp contMDiff_subtype_val) w)

omit [FiniteDimensional ℝ E] [IsManifold I ∞ N] in
include d₂ in
private theorem contMDiff_neckPunctureInr (ha : 0 ≤ a) :
    ContMDiff 𝓘(ℝ, E) I ∞ (neckPunctureInr (b := b) h₂ ha) := fun w ↦
  (ContMDiffAt.subtypeVal_comp_iff (puncture e₂) _ w).mp
    (d₂.contMDiff.contMDiffAt.comp w
      ((contDiffAt_inversion (ne_zero_of_mem_neck ha w)).contMDiffAt.comp w
        contMDiff_subtype_val.contMDiffAt))

omit [IsManifold I ∞ M] [IsManifold I ∞ N] in
include d₁ in
private theorem contMDiff_neckInl (ha : 0 ≤ a) :
    ContMDiff 𝓘(ℝ, E) I ∞ (neckInl (b := b) h₁ h₂ ha) := fun w ↦
  (ContMDiffAt.subtypeVal_comp_iff _ _ w).mp
    (ContMDiff.inl.contMDiffAt.comp w (contMDiff_neckPunctureInl h₁ d₁ ha w))

omit [IsManifold I ∞ M] [IsManifold I ∞ N] in
include d₂ in
private theorem contMDiff_neckInr (ha : 0 ≤ a) :
    ContMDiff 𝓘(ℝ, E) I ∞ (neckInr (b := b) h₁ h₂ ha) := fun w ↦
  (ContMDiffAt.subtypeVal_comp_iff _ _ w).mp
    (ContMDiff.inr.contMDiffAt.comp w (contMDiff_neckPunctureInr h₂ d₂ ha w))

omit [IsManifold I ∞ M] [IsManifold I ∞ N] in
include d₁ in
/-- Along the neck, the map into the first region has the differential of `e₁`. -/
private theorem mfderiv_neckInl_apply (ha : 0 ≤ a) (w : neck E a b)
    (ξ : TangentSpace 𝓘(ℝ, E) w) :
    mfderiv 𝓘(ℝ, E) I (neckInl h₁ h₂ ha) w ξ = mfderiv 𝓘(ℝ, E) I e₁ w.1 ξ := by
  have hP := (contMDiff_neckPunctureInl h₁ d₁ ha w).mdifferentiableAt (by simp)
  have hval : Subtype.val ∘ neckInl h₁ h₂ ha = Sum.inl ∘ neckPunctureInl (b := b) h₁ ha := rfl
  have hval' : Subtype.val ∘ neckPunctureInl (b := b) h₁ ha = e₁ ∘ Subtype.val := rfl
  refine (TauCeti.Manifold.mfderiv_subtype_val_comp_apply
    ((contMDiff_neckInl h₁ h₂ d₁ ha w).mdifferentiableAt (by simp)) ξ).symm.trans ?_
  rw [hval, TauCeti.mfderiv_sumInl_comp_apply hP,
    ← TauCeti.Manifold.mfderiv_subtype_val_comp_apply hP ξ, hval']
  exact TauCeti.Manifold.mfderiv_comp_subtype_val_apply ((d₁ w.1).mdifferentiableAt (by simp)) ξ

omit [IsManifold I ∞ M] [IsManifold I ∞ N] in
include d₂ in
/-- Along the neck, the map into the second region has the differential of
`e₂ ∘ inversion 0 1`. -/
private theorem mfderiv_neckInr_apply (ha : 0 ≤ a) (w : neck E a b)
    (ξ : TangentSpace 𝓘(ℝ, E) w) :
    mfderiv 𝓘(ℝ, E) I (neckInr h₁ h₂ ha) w ξ =
      mfderiv 𝓘(ℝ, E) I e₂ (inversion 0 1 w.1) (fderiv ℝ (inversion (0 : E) 1) w.1 ξ) := by
  have hP := (contMDiff_neckPunctureInr h₂ d₂ ha w).mdifferentiableAt (by simp)
  have hinv : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E) (inversion (0 : E) 1) w.1 :=
    (contDiffAt_inversion (n := 1) (ne_zero_of_mem_neck ha w)).contMDiffAt.mdifferentiableAt
      one_ne_zero
  have he₂ : MDifferentiableAt 𝓘(ℝ, E) I e₂ (inversion 0 1 w.1) :=
    (d₂ _).mdifferentiableAt (by simp)
  have hval : Subtype.val ∘ neckInr h₁ h₂ ha = Sum.inr ∘ neckPunctureInr (b := b) h₂ ha := rfl
  have hval' : Subtype.val ∘ neckPunctureInr (b := b) h₂ ha =
      (e₂ ∘ inversion 0 1) ∘ Subtype.val := rfl
  refine (TauCeti.Manifold.mfderiv_subtype_val_comp_apply
    ((contMDiff_neckInr h₁ h₂ d₂ ha w).mdifferentiableAt (by simp)) ξ).symm.trans ?_
  rw [hval, TauCeti.mfderiv_sumInr_comp_apply hP,
    ← TauCeti.Manifold.mfderiv_subtype_val_comp_apply hP ξ, hval']
  refine (TauCeti.Manifold.mfderiv_comp_subtype_val_apply (he₂.comp _ hinv) ξ).trans ?_
  rw [mfderiv_comp _ he₂ hinv, mfderiv_eq_fderiv]
  exact ContinuousLinearMap.comp_apply _ _ _

/-- The disjoint union of `g₁` and `g₂`, restricted to the two regions. -/
private def outerMetric :
    ContMDiffRiemannianMetric I ∞ E (fun z : outerOpens (a := a) (b := b) h₁.continuous
      h₂.continuous ↦ TangentSpace I z) :=
  ((g₁.restrictOpenTangentSpace (puncture e₁)).sumTangentSpace
    (g₂.restrictOpenTangentSpace (puncture e₂))).restrictOpenTangentSpace _

private theorem outerMetric_inner_inl (x : puncture e₁)
    (hx : (.inl x : puncture e₁ ⊕ puncture e₂) ∈ outerOpens (a := a) (b := b) h₁.continuous
      h₂.continuous) (u u' : TangentSpace I (⟨Sum.inl x, hx⟩ : outerOpens h₁.continuous
        h₂.continuous)) :
    (outerMetric g₁ g₂ h₁ h₂).inner ⟨Sum.inl x, hx⟩ u u' = g₁.inner x.1 u u' := by
  refine (restrictOpenTangentSpace_inner _ _ ⟨Sum.inl x, hx⟩ u u').trans ?_
  rw [TauCeti.Manifold.tangentSpaceOpenEquiv_apply, TauCeti.Manifold.tangentSpaceOpenEquiv_apply]
  refine (sumTangentSpace_inner_inl _ _ x u u').trans ?_
  refine (restrictOpenTangentSpace_inner _ _ x u u').trans ?_
  exact congrArg₂ (fun s t ↦ g₁.inner x.1 s t) (TauCeti.Manifold.tangentSpaceOpenEquiv_apply x u)
    (TauCeti.Manifold.tangentSpaceOpenEquiv_apply x u')

private theorem outerMetric_inner_inr (y : puncture e₂)
    (hy : (.inr y : puncture e₁ ⊕ puncture e₂) ∈ outerOpens (a := a) (b := b) h₁.continuous
      h₂.continuous) (u u' : TangentSpace I (⟨Sum.inr y, hy⟩ : outerOpens h₁.continuous
        h₂.continuous)) :
    (outerMetric g₁ g₂ h₁ h₂).inner ⟨Sum.inr y, hy⟩ u u' = g₂.inner y.1 u u' := by
  refine (restrictOpenTangentSpace_inner _ _ ⟨Sum.inr y, hy⟩ u u').trans ?_
  rw [TauCeti.Manifold.tangentSpaceOpenEquiv_apply, TauCeti.Manifold.tangentSpaceOpenEquiv_apply]
  refine (sumTangentSpace_inner_inr _ _ y u u').trans ?_
  refine (restrictOpenTangentSpace_inner _ _ y u u').trans ?_
  exact congrArg₂ (fun s t ↦ g₂.inner y.1 s t) (TauCeti.Manifold.tangentSpaceOpenEquiv_apply y u)
    (TauCeti.Manifold.tangentSpaceOpenEquiv_apply y u')

variable {g₁ g₂} (hg : ∀ v : E, a < ‖v‖ → ‖v‖ < b → ∀ ξ ζ : E,
  g₁.inner (e₁ v) (mfderiv 𝓘(ℝ, E) I e₁ v ξ) (mfderiv 𝓘(ℝ, E) I e₁ v ζ) =
    g₂.inner (e₂ (inversion 0 1 v))
      (mfderiv 𝓘(ℝ, E) I e₂ (inversion 0 1 v) (fderiv ℝ (inversion (0 : E) 1) v ξ))
      (mfderiv 𝓘(ℝ, E) I e₂ (inversion 0 1 v) (fderiv ℝ (inversion (0 : E) 1) v ζ)))

include d₁ d₂ hg in
/-- At glued points of the neck, tangent vectors with the same images in the connected sum have
the same inner products for the two metrics. -/
private theorem outerMetric_inner_neckInl_eq (ha : 0 ≤ a) (w : neck E a b)
    {u u' : TangentSpace I (neckInl h₁ h₂ ha w)} {v v' : TangentSpace I (neckInr h₁ h₂ ha w)} :
    letI := ConnectedSum.chartedSpace (H := H) h₁ h₂
    mfderiv I I (outerMap h₁ h₂) (neckInl h₁ h₂ ha w) u =
        mfderiv I I (outerMap h₁ h₂) (neckInr h₁ h₂ ha w) v →
      mfderiv I I (outerMap h₁ h₂) (neckInl h₁ h₂ ha w) u' =
        mfderiv I I (outerMap h₁ h₂) (neckInr h₁ h₂ ha w) v' →
      (outerMetric g₁ g₂ h₁ h₂).inner (neckInl h₁ h₂ ha w) u u' =
        (outerMetric g₁ g₂ h₁ h₂).inner (neckInr h₁ h₂ ha w) v v' := by
  let := ConnectedSum.chartedSpace (H := H) h₁ h₂
  have := ConnectedSum.isManifold (n := ⊤) h₁ h₂ d₁ d₂
  intro hu hu'
  have hf := isLocalDiffeomorph_outerMap (a := a) (b := b) h₁ h₂ d₁ d₂
  have hρ₁ := (contMDiff_neckInl h₁ h₂ d₁ ha w).mdifferentiableAt (by simp)
  have hρ₂ := (contMDiff_neckInr h₁ h₂ d₂ ha w).mdifferentiableAt (by simp)
  -- The differentials of the two maps of the neck agree after the map to the connected sum.
  have hcomp (ξ : TangentSpace 𝓘(ℝ, E) w) : mfderiv I I (outerMap h₁ h₂) (neckInl h₁ h₂ ha w)
      (mfderiv 𝓘(ℝ, E) I (neckInl h₁ h₂ ha) w ξ) = mfderiv I I (outerMap h₁ h₂)
        (neckInr h₁ h₂ ha w) (mfderiv 𝓘(ℝ, E) I (neckInr h₁ h₂ ha) w ξ) := by
    have h₁' := mfderiv_comp w ((hf _).mdifferentiableAt (by simp)) hρ₁
    have h₂' := mfderiv_comp w ((hf _).mdifferentiableAt (by simp)) hρ₂
    rw [outerMap_comp_neckInl h₁ h₂ ha, h₂'] at h₁'
    exact (DFunLike.congr_fun h₁' ξ).symm
  -- Every tangent vector at `e₁ w` is the image of a vector of `E` under the differential of `e₁`.
  obtain ⟨L, hL⟩ := d₁.isInvertible_mfderiv (by simp) w.1
  have hL' (t : TangentSpace I (e₁ w.1)) : mfderiv 𝓘(ℝ, E) I e₁ w.1 (L.symm t) = t := by
    rw [← hL]
    exact L.apply_symm_apply t
  have hpre (t : TangentSpace I (e₁ w.1)) :
      mfderiv 𝓘(ℝ, E) I (neckInl h₁ h₂ ha) w (L.symm t) = t :=
    (mfderiv_neckInl_apply h₁ h₂ d₁ ha w _).trans (hL' t)
  have hinj := ((hf.isInvertible_mfderiv (by simp)) (neckInr h₁ h₂ ha w)).injective
  have hv : v = mfderiv 𝓘(ℝ, E) I (neckInr h₁ h₂ ha) w (L.symm u) :=
    hinj ((hu.symm.trans (congrArg _ (hpre u).symm)).trans (hcomp _))
  have hv' : v' = mfderiv 𝓘(ℝ, E) I (neckInr h₁ h₂ ha) w (L.symm u') :=
    hinj ((hu'.symm.trans (congrArg _ (hpre u').symm)).trans (hcomp _))
  subst hv hv'
  have hw := mem_neck.1 w.2
  calc (outerMetric g₁ g₂ h₁ h₂).inner (neckInl h₁ h₂ ha w) u u'
      = g₁.inner (e₁ w.1) u u' := outerMetric_inner_inl g₁ g₂ h₁ h₂ _ _ u u'
    _ = g₁.inner (e₁ w.1) (mfderiv 𝓘(ℝ, E) I e₁ w.1 (L.symm u))
          (mfderiv 𝓘(ℝ, E) I e₁ w.1 (L.symm u')) :=
        (congrArg₂ (fun s t ↦ g₁.inner (e₁ w.1) s t) (hL' u) (hL' u')).symm
    _ = _ := hg w.1 hw.1 hw.2 _ _
    _ = _ := ((outerMetric_inner_inr g₁ g₂ h₁ h₂ _ _ _ _).trans
        (congrArg₂ (fun s t ↦ g₂.inner (e₂ (inversion 0 1 w.1)) s t)
          (mfderiv_neckInr_apply h₁ h₂ d₂ ha w _) (mfderiv_neckInr_apply h₁ h₂ d₂ ha w _))).symm

include d₁ d₂ hg in
/-- Tangent vectors at points of the two regions with the same images in the connected sum have
the same inner products. -/
private theorem outerMetric_inner_eq (ha : 0 ≤ a) (hab : a < b) :
    letI := ConnectedSum.chartedSpace (H := H) h₁ h₂
    ∀ (z z' : outerOpens (a := a) (b := b) h₁.continuous h₂.continuous)
      (u u' : TangentSpace I z) (v v' : TangentSpace I z'), outerMap h₁ h₂ z = outerMap h₁ h₂ z' →
      mfderiv I I (outerMap h₁ h₂) z u = mfderiv I I (outerMap h₁ h₂) z' v →
      mfderiv I I (outerMap h₁ h₂) z u' = mfderiv I I (outerMap h₁ h₂) z' v' →
      (outerMetric g₁ g₂ h₁ h₂).inner z u u' = (outerMetric g₁ g₂ h₁ h₂).inner z' v v' := by
  let := ConnectedSum.chartedSpace (H := H) h₁ h₂
  have := ConnectedSum.isManifold (n := ⊤) h₁ h₂ d₁ d₂
  have hf := isLocalDiffeomorph_outerMap (a := a) (b := b) h₁ h₂ d₁ d₂
  have hb : 0 < b := ha.trans_lt hab
  intro z z' u u' v v' hzz' hu hu'
  rw [outerMap_apply, outerMap_apply, mk_eq_mk_iff h₁.injective h₂.injective] at hzz'
  rcases hzz' with h | h | h
  · -- The same point: the differential of `outerMap` there is injective.
    obtain rfl : z = z' := Subtype.ext h
    have hinj := (hf.isInvertible_mfderiv (by simp) z).injective
    rw [hinj hu, hinj hu']
  · -- `z = e₁ v₀` and `z' = e₂ (inversion 0 1 v₀)`, with `v₀` on the neck.
    rcases z with ⟨⟨x, hx⟩ | x, hz⟩ <;> rcases z' with ⟨y | ⟨y, hy⟩, hz'⟩ <;>
      simp only [rel_inl_inr, not_rel_inl_inl, not_rel_inr_inl, not_rel_inr_inr] at h
    obtain ⟨v₀, hv₀, rfl, rfl⟩ := h
    have hlt : ‖v₀‖ < b :=
      (inv_lt_norm_inversion_iff hb hv₀).1
        (h₂.injective.apply_notMem_image_closedBall_zero_iff.1 hz')
    exact outerMetric_inner_neckInl_eq h₁ h₂ d₁ d₂ hg ha
      ⟨v₀, mem_neck.2 ⟨h₁.injective.apply_notMem_image_closedBall_zero_iff.1 hz, hlt⟩⟩ hu hu'
  · -- `z' = e₁ v₀` and `z = e₂ (inversion 0 1 v₀)`, with `v₀` on the neck.
    rcases z with ⟨x | ⟨x, hx⟩, hz⟩ <;> rcases z' with ⟨⟨y, hy⟩ | y, hz'⟩ <;>
      simp only [rel_inl_inr, not_rel_inl_inl, not_rel_inr_inl, not_rel_inr_inr] at h
    obtain ⟨v₀, hv₀, rfl, rfl⟩ := h
    have hlt : ‖v₀‖ < b :=
      (inv_lt_norm_inversion_iff hb hv₀).1
        (h₂.injective.apply_notMem_image_closedBall_zero_iff.1 hz)
    exact (outerMetric_inner_neckInl_eq h₁ h₂ d₁ d₂ hg ha
      ⟨v₀, mem_neck.2 ⟨h₁.injective.apply_notMem_image_closedBall_zero_iff.1 hz', hlt⟩⟩
        hu.symm hu'.symm).symm

variable (g₁ g₂) in
/-- **The metric of a connected sum glued along a neck.** Let `0 ≤ a < b`, and suppose that on the
neck `a < ‖v‖ < b` the gluing map `e₂ ∘ inversion 0 1 ∘ e₁⁻¹` of the connected sum carries `g₁`
to `g₂` (the hypothesis `hg`). This is the metric on `M # N` which is `g₁` on `M` outside
`e₁ (closedBall 0 a)` and `g₂` on `N` outside `e₂ (closedBall 0 b⁻¹)`
(`Bundle.ContMDiffRiemannianMetric.connectedSum_inner_mfderiv_inl`,
`Bundle.ContMDiffRiemannianMetric.connectedSum_inner_mfderiv_inr`). -/
def connectedSum (ha : 0 ≤ a) (hab : a < b) :
    letI := ConnectedSum.chartedSpace (H := H) h₁ h₂
    haveI := ConnectedSum.isManifold (n := ⊤) h₁ h₂ d₁ d₂
    ContMDiffRiemannianMetric I ∞ E (fun p : ConnectedSum e₁ e₂ ↦ TangentSpace I p) :=
  letI := ConnectedSum.chartedSpace (H := H) h₁ h₂
  haveI := ConnectedSum.isManifold (n := ⊤) h₁ h₂ d₁ d₂
  (outerMetric g₁ g₂ h₁ h₂).descend (isLocalDiffeomorph_outerMap h₁ h₂ d₁ d₂)
    (outerMap_surjective h₁ h₂ ha hab) (outerMetric_inner_eq h₁ h₂ d₁ d₂ hg ha hab)

include d₁ d₂ in
/-- The differential of the map from the two regions is that of the quotient map. -/
private theorem mfderiv_outerMap_apply
    (z : outerOpens (a := a) (b := b) h₁.continuous h₂.continuous) (u : TangentSpace I z) :
    letI := ConnectedSum.chartedSpace (H := H) h₁ h₂
    mfderiv I I (outerMap h₁ h₂) z u = mfderiv I I (ConnectedSum.mk e₁ e₂) z.1 u :=
  letI := ConnectedSum.chartedSpace (H := H) h₁ h₂
  haveI := ConnectedSum.isManifold (n := ⊤) h₁ h₂ d₁ d₂
  TauCeti.Manifold.mfderiv_comp_subtype_val_apply
    ((isLocalDiffeomorph_mk (n := ⊤) h₁ h₂ d₁ d₂ z.1).mdifferentiableAt (by simp)) u

/-- On `M` outside `e₁ (closedBall 0 a)`, the glued metric is `g₁`. -/
theorem connectedSum_inner_mfderiv_inl (ha : 0 ≤ a) (hab : a < b) (x : puncture e₁)
    (hx : (x : M) ∉ e₁ '' closedBall 0 a) (u u' : TangentSpace I x) :
    letI := ConnectedSum.chartedSpace (H := H) h₁ h₂
    haveI := ConnectedSum.isManifold (n := ⊤) h₁ h₂ d₁ d₂
    (g₁.connectedSum g₂ h₁ h₂ d₁ d₂ hg ha hab).inner (inl e₁ e₂ x)
      (mfderiv I I (inl e₁ e₂) x u) (mfderiv I I (inl e₁ e₂) x u') = g₁.inner x u u' := by
  let := ConnectedSum.chartedSpace (H := H) h₁ h₂
  have := ConnectedSum.isManifold (n := ⊤) h₁ h₂ d₁ d₂
  let z : outerOpens (a := a) (b := b) h₁.continuous h₂.continuous := ⟨Sum.inl x, hx⟩
  have hD (t : TangentSpace I x) :
      mfderiv I I (outerMap h₁ h₂) z t = mfderiv I I (inl e₁ e₂) x t :=
    (mfderiv_outerMap_apply h₁ h₂ d₁ d₂ z t).trans
      (mfderiv_inl_apply (n := ⊤) h₁ h₂ d₁ d₂ (by simp) x t).symm
  have h := descend_inner_mfderiv_of_eq (outerMetric g₁ g₂ h₁ h₂)
    (isLocalDiffeomorph_outerMap h₁ h₂ d₁ d₂) (outerMap_surjective h₁ h₂ ha hab)
    (outerMetric_inner_eq h₁ h₂ d₁ d₂ hg ha hab) (x := z) (y := inl e₁ e₂ x)
    (by rw [outerMap_apply, mk_inl]) u u'
  exact (congrArg₂ (fun s t ↦ (g₁.connectedSum g₂ h₁ h₂ d₁ d₂ hg ha hab).inner (inl e₁ e₂ x) s t)
    (hD u).symm (hD u').symm).trans (h.trans (outerMetric_inner_inl g₁ g₂ h₁ h₂ x hx u u'))

/-- On `N` outside `e₂ (closedBall 0 b⁻¹)`, the glued metric is `g₂`. -/
theorem connectedSum_inner_mfderiv_inr (ha : 0 ≤ a) (hab : a < b) (y : puncture e₂)
    (hy : (y : N) ∉ e₂ '' closedBall 0 b⁻¹) (u u' : TangentSpace I y) :
    letI := ConnectedSum.chartedSpace (H := H) h₁ h₂
    haveI := ConnectedSum.isManifold (n := ⊤) h₁ h₂ d₁ d₂
    (g₁.connectedSum g₂ h₁ h₂ d₁ d₂ hg ha hab).inner (inr e₁ e₂ y)
      (mfderiv I I (inr e₁ e₂) y u) (mfderiv I I (inr e₁ e₂) y u') = g₂.inner y u u' := by
  let := ConnectedSum.chartedSpace (H := H) h₁ h₂
  have := ConnectedSum.isManifold (n := ⊤) h₁ h₂ d₁ d₂
  let z : outerOpens (a := a) (b := b) h₁.continuous h₂.continuous := ⟨Sum.inr y, hy⟩
  have hD (t : TangentSpace I y) :
      mfderiv I I (outerMap h₁ h₂) z t = mfderiv I I (inr e₁ e₂) y t :=
    (mfderiv_outerMap_apply h₁ h₂ d₁ d₂ z t).trans
      (mfderiv_inr_apply (n := ⊤) h₁ h₂ d₁ d₂ (by simp) y t).symm
  have h := descend_inner_mfderiv_of_eq (outerMetric g₁ g₂ h₁ h₂)
    (isLocalDiffeomorph_outerMap h₁ h₂ d₁ d₂) (outerMap_surjective h₁ h₂ ha hab)
    (outerMetric_inner_eq h₁ h₂ d₁ d₂ hg ha hab) (x := z) (y := inr e₁ e₂ y)
    (by rw [outerMap_apply, mk_inr]) u u'
  exact (congrArg₂ (fun s t ↦ (g₁.connectedSum g₂ h₁ h₂ d₁ d₂ hg ha hab).inner (inr e₁ e₂ y) s t)
    (hD u).symm (hD u').symm).trans (h.trans (outerMetric_inner_inr g₁ g₂ h₁ h₂ y hy u u'))

private theorem scalarCurvature_outerMetric_inl (x : puncture e₁)
    (hx : (.inl x : puncture e₁ ⊕ puncture e₂) ∈ outerOpens (a := a) (b := b) h₁.continuous
      h₂.continuous) :
    (outerMetric g₁ g₂ h₁ h₂).scalarCurvature ⟨Sum.inl x, hx⟩ = g₁.scalarCurvature x := by
  rw [outerMetric, scalarCurvature_restrictOpenTangentSpace, scalarCurvature_sumTangentSpace_inl,
    scalarCurvature_restrictOpenTangentSpace]

private theorem scalarCurvature_outerMetric_inr (y : puncture e₂)
    (hy : (.inr y : puncture e₁ ⊕ puncture e₂) ∈ outerOpens (a := a) (b := b) h₁.continuous
      h₂.continuous) :
    (outerMetric g₁ g₂ h₁ h₂).scalarCurvature ⟨Sum.inr y, hy⟩ = g₂.scalarCurvature y := by
  rw [outerMetric, scalarCurvature_restrictOpenTangentSpace, scalarCurvature_sumTangentSpace_inr,
    scalarCurvature_restrictOpenTangentSpace]

/-- On `M` outside `e₁ (closedBall 0 a)`, the glued metric has the scalar curvature of `g₁`. -/
theorem scalarCurvature_connectedSum_inl (ha : 0 ≤ a) (hab : a < b) (x : puncture e₁)
    (hx : (x : M) ∉ e₁ '' closedBall 0 a) :
    letI := ConnectedSum.chartedSpace (H := H) h₁ h₂
    haveI := ConnectedSum.isManifold (n := ⊤) h₁ h₂ d₁ d₂
    haveI := ConnectedSum.t2Space h₁ h₂
    (g₁.connectedSum g₂ h₁ h₂ d₁ d₂ hg ha hab).scalarCurvature (inl e₁ e₂ x) =
      g₁.scalarCurvature x := by
  let := ConnectedSum.chartedSpace (H := H) h₁ h₂
  have := ConnectedSum.isManifold (n := ⊤) h₁ h₂ d₁ d₂
  have := ConnectedSum.t2Space h₁ h₂
  rw [← mk_inl, ← outerMap_apply (a := a) (b := b) h₁ h₂ ⟨Sum.inl x, hx⟩, connectedSum,
    scalarCurvature_descend]
  exact scalarCurvature_outerMetric_inl (g₁ := g₁) (g₂ := g₂) h₁ h₂ x hx

/-- On `N` outside `e₂ (closedBall 0 b⁻¹)`, the glued metric has the scalar curvature of `g₂`. -/
theorem scalarCurvature_connectedSum_inr (ha : 0 ≤ a) (hab : a < b) (y : puncture e₂)
    (hy : (y : N) ∉ e₂ '' closedBall 0 b⁻¹) :
    letI := ConnectedSum.chartedSpace (H := H) h₁ h₂
    haveI := ConnectedSum.isManifold (n := ⊤) h₁ h₂ d₁ d₂
    haveI := ConnectedSum.t2Space h₁ h₂
    (g₁.connectedSum g₂ h₁ h₂ d₁ d₂ hg ha hab).scalarCurvature (inr e₁ e₂ y) =
      g₂.scalarCurvature y := by
  let := ConnectedSum.chartedSpace (H := H) h₁ h₂
  have := ConnectedSum.isManifold (n := ⊤) h₁ h₂ d₁ d₂
  have := ConnectedSum.t2Space h₁ h₂
  rw [← mk_inr, ← outerMap_apply (a := a) (b := b) h₁ h₂ ⟨Sum.inr y, hy⟩, connectedSum,
    scalarCurvature_descend]
  exact scalarCurvature_outerMetric_inr (g₁ := g₁) (g₂ := g₂) h₁ h₂ y hy

/-- Every value of the scalar curvature of the glued metric is a value of the scalar curvature of
`g₁` or of `g₂`: the two regions cover the connected sum, and on each the glued metric has the
scalar curvature of `g₁`, respectively `g₂`. -/
theorem range_scalarCurvature_connectedSum_subset (ha : 0 ≤ a) (hab : a < b) :
    letI := ConnectedSum.chartedSpace (H := H) h₁ h₂
    haveI := ConnectedSum.isManifold (n := ⊤) h₁ h₂ d₁ d₂
    haveI := ConnectedSum.t2Space h₁ h₂
    range (g₁.connectedSum g₂ h₁ h₂ d₁ d₂ hg ha hab).scalarCurvature ⊆
      range g₁.scalarCurvature ∪ range g₂.scalarCurvature := by
  let := ConnectedSum.chartedSpace (H := H) h₁ h₂
  have := ConnectedSum.isManifold (n := ⊤) h₁ h₂ d₁ d₂
  have := ConnectedSum.t2Space h₁ h₂
  rintro _ ⟨p, rfl⟩
  obtain ⟨⟨x | y, hz⟩, rfl⟩ := outerMap_surjective h₁ h₂ ha hab p
  · rw [outerMap_apply, mk_inl, scalarCurvature_connectedSum_inl h₁ h₂ d₁ d₂ hg ha hab x hz]
    exact .inl ⟨x, rfl⟩
  · rw [outerMap_apply, mk_inr, scalarCurvature_connectedSum_inr h₁ h₂ d₁ d₂ hg ha hab y hz]
    exact .inr ⟨y, rfl⟩

end Gluing

variable {g₁ : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)}
  {g₂ : ContMDiffRiemannianMetric I ∞ E (fun y : N ↦ TangentSpace I y)}

omit [FiniteDimensional ℝ E] [T2Space M] [T2Space N] in
/-- **Cylindrical necks agree.** Suppose that `g₁` read through `e₁` is the cylinder metric
`⟪ξ, ζ⟫ / ‖v‖ ^ 2` for `a < ‖v‖ < b`, and that `g₂` read through `e₂` is the cylinder metric for
`b⁻¹ < ‖w‖ < a⁻¹`. Since the inversion preserves the cylinder metric, the gluing map of the
connected sum carries `g₁` to `g₂` on the neck `a < ‖v‖ < b`: this is the hypothesis of
`Bundle.ContMDiffRiemannianMetric.connectedSum`. -/
theorem inner_mfderiv_inversion_eq_of_cylinder (ha : 0 < a)
    (hcyl₁ : ∀ v : E, a < ‖v‖ → ‖v‖ < b → ∀ ξ ζ : E,
      g₁.inner (e₁ v) (mfderiv 𝓘(ℝ, E) I e₁ v ξ) (mfderiv 𝓘(ℝ, E) I e₁ v ζ) =
        Inner.inner ℝ ξ ζ / ‖v‖ ^ 2)
    (hcyl₂ : ∀ w : E, b⁻¹ < ‖w‖ → ‖w‖ < a⁻¹ → ∀ ξ ζ : E,
      g₂.inner (e₂ w) (mfderiv 𝓘(ℝ, E) I e₂ w ξ) (mfderiv 𝓘(ℝ, E) I e₂ w ζ) =
        Inner.inner ℝ ξ ζ / ‖w‖ ^ 2) :
    ∀ v : E, a < ‖v‖ → ‖v‖ < b → ∀ ξ ζ : E,
      g₁.inner (e₁ v) (mfderiv 𝓘(ℝ, E) I e₁ v ξ) (mfderiv 𝓘(ℝ, E) I e₁ v ζ) =
        g₂.inner (e₂ (inversion 0 1 v))
          (mfderiv 𝓘(ℝ, E) I e₂ (inversion 0 1 v) (fderiv ℝ (inversion (0 : E) 1) v ξ))
          (mfderiv 𝓘(ℝ, E) I e₂ (inversion 0 1 v) (fderiv ℝ (inversion (0 : E) 1) v ζ)) := by
  intro v hav hvb ξ ζ
  have hv : v ≠ 0 := norm_pos_iff.1 (ha.trans hav)
  rw [hcyl₁ v hav hvb, hcyl₂ _ ((inv_lt_norm_inversion_iff (ha.trans (hav.trans hvb)) hv).2 hvb)
    ((norm_inversion_lt_inv_iff ha hv).2 hav)]
  simpa only [dist_zero_right] using
    (inner_fderiv_inversion_div_dist_sq (0 : E) v one_ne_zero ξ ζ).symm

end Bundle.ContMDiffRiemannianMetric
