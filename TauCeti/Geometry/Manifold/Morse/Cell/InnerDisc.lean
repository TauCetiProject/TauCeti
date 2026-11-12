/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Cell.Annulus
import TauCeti.AlgebraicTopology.Disk.Annulus

/-!
# Extending a homotopy of small Morse discs to the characteristic maps

Let `ψ₀` and `ψ₁` be two normal-form charts of the same index `k` at a critical level `c`, in which
`f = c - Σ_{j < k} yⱼ² + Σ_{j ≥ k} yⱼ²`, with characteristic maps
`χ₀, χ₁ : (D^k, ∂D^k) → (M_{c+ε}, M_{c-ε})`, `χ(w) = ψ⁻¹(√ε • (w, 0))`, and let `g` be a linear
isometry of `ℝᵏ`. Milnor's comparison of the cells attached by the two charts first compares
only small discs: for a radius `0 < d ≤ 1` one constructs a homotopy `G` from `χ₁` to `χ₀ ∘ g` on
the disc `‖w‖ ≤ d` which stays in `M_{c+ε}` and keeps the small boundary sphere `‖w‖ = d` in
`M_{c-εd²}`. This file shows that such a homotopy of small discs extends to a homotopy of maps of
pairs `K : χ₁ ≃ χ₀ ∘ g` on the whole disc, keeping the boundary sphere in the lower sublevel
`M_{c-ε}` (`TauCeti.exists_homotopy_morseCharacteristicMap_of_innerDisc`), provided the band
`f⁻¹[c - ε, c - εd²]` is compact and free of critical points. This is the homotopy of pairs that
the change-of-chart comparison `TauCeti.morseChartChange` and the reattachment map
`TauCeti.morseCellReattachment` take as input.

The extension works for families of discs over any parameter space `X`, which is what the
comparison of continuous families of Morse charts over a compact parameter space needs. Only the
values of `f` on the discs matter: if `m₀, m₁ : X × D^k → M` satisfy `f (mⱼ (x, w)) ≤ c - ε‖w‖²`,
as the characteristic maps of Morse charts do with equality, then a homotopy of the families of
small discs `‖w‖ ≤ d` with the same bounds as `G` extends to a homotopy from `m₁` to `m₀` which
stays in `M_{c+ε}` and keeps `X × ∂D^k` in `M_{c-ε}`
(`TauCeti.exists_parametric_homotopy_of_innerDisc`). The critical-free band deformation is the same
for every parameter, since `f` does not depend on it. The comparison of two charts is the case of a
one-point parameter space.

The construction follows Milnor. Let `R` deform `M_{c-εd²}` onto `M_{c-ε}` across the band
(`TauCeti.exists_sublevelDeformation`). Write a point of the annulus `d ≤ ‖w‖ ≤ 1` of the disc
as `(d + (1 - d) s) • θ` with `s ∈ [0, 1]` and `θ` on the unit sphere. The homotopy has three
stages; on the small disc the first and last are constant in time, and the second is `G`:

* on the annulus, deform the annulus of `m₁` to the retraction track
  `(s, x, θ) ↦ R (s, m₁ (x, d θ))` of its inner circle (`ContinuousMap.HomotopyRel.annulusToTrack`),
  keeping `m₁` on the small disc;
* move the small disc by `G`, together with the retraction track of its boundary circle
  (`ContinuousMap.Homotopy.retractionTrackHomotopy`);
* undo the first stage for the annulus of `m₀`.

On the seam `‖w‖ = d` the pieces agree because `R` starts at the identity, and on the outer
sphere every stage stays in `M_{c-ε}`: the annulus deformation does by construction, and the
track has reached the end of `R` there. No overlap of the whole characteristic discs of the two
charts is used.

## Main results

* `TauCeti.exists_parametric_homotopy_of_innerDisc_of_homotopyRel`: a homotopy of the families of
  small discs of two families of maps `X × D^k → M` with `f ≤ c - ε‖w‖²`, keeping their boundary
  spheres in `M_{c-εd²}`, extends to a homotopy of the families, keeping `X × ∂D^k` in `M_{c-ε}`,
  given a deformation of `M_{c-εd²}` into `M_{c-ε}` fixing `M_{c-ε}`.
* `TauCeti.exists_parametric_homotopy_of_innerDisc`: the same when `M` is a manifold and the band
  `f⁻¹[c - ε, c - εd²]` is compact and free of critical points, which supplies the deformation.
* `TauCeti.exists_homotopy_morseCharacteristicMap_of_innerDisc_of_homotopyRel` and
  `TauCeti.exists_homotopy_morseCharacteristicMap_of_innerDisc`: the case of the characteristic
  maps of two Morse charts, as a homotopy of maps of pairs.

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  §3, Remark 3.3.
-/

public section

noncomputable section

universe u v

open Set Metric Topology unitInterval CategoryTheory
open scoped ContDiff Manifold

namespace TauCeti

section Stages

variable {X : Type*} [TopologicalSpace X] {M : Type*} [TopologicalSpace M] {f : M → ℝ}
  {c ε : ℝ} {k : ℕ} {d : I}

/-- The bounds kept by every stage: the discs go into `M_{c+ε}` and their boundaries into
`M_{c-ε}`. -/
private def StageBound (f : M → ℝ) (c ε : ℝ) (m : C(X × TopCat.disk.{u} k, M)) : Prop :=
  (∀ q, f (m q) ≤ c + ε) ∧ ∀ x s, f (m (x, TopCat.diskBoundaryInclusion k s)) ≤ c - ε

/-- The annulus of a family of discs on which `f ≤ c - ε‖w‖²` lies in `M_{c-εd²}`. -/
private theorem apply_annulusPoint_le (hε : 0 ≤ ε) (m : C(X × TopCat.disk.{u} k, M))
    (hm : ∀ x w, f (m (x, w)) ≤ c - ε * ‖w.down.1‖ ^ 2) (p : I × (X × TopCat.diskBoundary.{u} k)) :
    f (m (p.2.1, TopCat.annulusPoint d.2.1 d.2.2 (p.1, p.2.2))) ≤ c - ε * (d : ℝ) ^ 2 := by
  refine (hm _ _).trans (sub_le_sub_left (mul_le_mul_of_nonneg_left ?_ hε) c)
  rw [TopCat.norm_annulusPoint]
  exact pow_le_pow_left₀ d.2.1 (TopCat.le_add_one_sub_mul d.2.2 p.1) 2

/-- The annulus `d ≤ ‖w‖ ≤ 1` of a family of discs on which `f ≤ c - ε‖w‖²`, as a map into
`M_{c-εd²}`. -/
private def familyAnnulus (hε : 0 ≤ ε) (m : C(X × TopCat.disk.{u} k, M))
    (hm : ∀ x w, f (m (x, w)) ≤ c - ε * ‖w.down.1‖ ^ 2) :
    C(I × (X × TopCat.diskBoundary.{u} k), {x : M | f x ≤ c - ε * (d : ℝ) ^ 2}) where
  toFun p :=
    ⟨m (p.2.1, TopCat.annulusPoint d.2.1 d.2.2 (p.1, p.2.2)), apply_annulusPoint_le hε m hm p⟩
  continuous_toFun :=
    (m.continuous.comp (by fun_prop)).subtype_mk fun p ↦ apply_annulusPoint_le hε m hm p

private theorem coe_familyAnnulus_apply (hε : 0 ≤ ε) (m : C(X × TopCat.disk.{u} k, M))
    (hm : ∀ x w, f (m (x, w)) ≤ c - ε * ‖w.down.1‖ ^ 2) (p : I × (X × TopCat.diskBoundary.{u} k)) :
    (familyAnnulus (d := d) hε m hm p : M) =
      m (p.2.1, TopCat.annulusPoint d.2.1 d.2.2 (p.1, p.2.2)) :=
  (rfl)

/-- The outer circle of the annulus lies in the lower sublevel `M_{c-ε}`. -/
private theorem familyAnnulus_one_mem (hε : 0 ≤ ε) (m : C(X × TopCat.disk.{u} k, M))
    (hm : ∀ x w, f (m (x, w)) ≤ c - ε * ‖w.down.1‖ ^ 2) (q : X × TopCat.diskBoundary.{u} k) :
    familyAnnulus (d := d) hε m hm (1, q) ∈ {x | f x.val ≤ c - ε} := by
  have h := hm q.1 (TopCat.annulusPoint d.2.1 d.2.2 (1, q.2))
  rw [TopCat.annulusPoint_one, TopCat.norm_diskBoundaryInclusion, one_pow, mul_one] at h
  rw [Set.mem_ofPred_eq, coe_familyAnnulus_apply, TopCat.annulusPoint_one]
  exact h

/-- Glue a map on the small discs and a map on the annuli, both depending on a time and a
parameter, along the seam `‖w‖ = d`. -/
private def stageGlue (hd : 0 < d)
    (A : C((I × X) × closedBall (0 : EuclideanSpace ℝ (Fin k)) d, M))
    (B : C((I × X) × (I × TopCat.diskBoundary.{u} k), M))
    (hAB : ∀ p θ, B (p, 0, θ) =
      A (p, ⟨(d : ℝ) • θ.down.1, TopCat.smul_diskBoundary_mem_closedBall d.2.1 θ⟩)) :
    C(I × (X × TopCat.disk.{u} k), M) where
  toFun p := TopCat.discGlue (unitInterval.coe_pos.2 hd) A B hAB ((p.1, p.2.1), p.2.2)
  continuous_toFun := (TopCat.discGlue _ A B hAB).continuous.comp (by fun_prop)

private theorem stageGlue_of_norm_le (hd : 0 < d)
    (A : C((I × X) × closedBall (0 : EuclideanSpace ℝ (Fin k)) d, M))
    (B : C((I × X) × (I × TopCat.diskBoundary.{u} k), M))
    (hAB : ∀ p θ, B (p, 0, θ) =
      A (p, ⟨(d : ℝ) • θ.down.1, TopCat.smul_diskBoundary_mem_closedBall d.2.1 θ⟩))
    (t : I) (x : X) {w : TopCat.disk.{u} k} (hw : ‖w.down.1‖ ≤ d) :
    stageGlue hd A B hAB (t, x, w) = A ((t, x), ⟨w.down.1, mem_closedBall_zero_iff.2 hw⟩) :=
  TopCat.discGlue_apply_of_norm_le _ _ _ _ _ hw

private theorem stageGlue_of_le_norm (hd : 0 < d)
    (A : C((I × X) × closedBall (0 : EuclideanSpace ℝ (Fin k)) d, M))
    (B : C((I × X) × (I × TopCat.diskBoundary.{u} k), M))
    (hAB : ∀ p θ, B (p, 0, θ) =
      A (p, ⟨(d : ℝ) • θ.down.1, TopCat.smul_diskBoundary_mem_closedBall d.2.1 θ⟩))
    (t : I) (x : X) {w : TopCat.disk.{u} k} (hw : d ≤ ‖w.down.1‖) :
    stageGlue hd A B hAB (t, x, w) =
      B ((t, x), TopCat.annulusParam d w, TopCat.annulusDir (unitInterval.coe_pos.2 hd) ⟨w, hw⟩) :=
  TopCat.discGlue_apply_of_le_norm _ _ _ _ _ hw

private theorem stageGlue_le (hd : 0 < d)
    (A : C((I × X) × closedBall (0 : EuclideanSpace ℝ (Fin k)) d, M))
    (B : C((I × X) × (I × TopCat.diskBoundary.{u} k), M))
    (hAB : ∀ p θ, B (p, 0, θ) =
      A (p, ⟨(d : ℝ) • θ.down.1, TopCat.smul_diskBoundary_mem_closedBall d.2.1 θ⟩))
    {a : ℝ} (hA : ∀ q, f (A q) ≤ a) (hB : ∀ q, f (B q) ≤ a)
    (q : I × (X × TopCat.disk.{u} k)) : f (stageGlue hd A B hAB q) ≤ a :=
  TopCat.discGlue_mem (S := {x | f x ≤ a}) _ _ _ _ hA hB _

private theorem stageGlue_boundary_le (hd : 0 < d)
    (A : C((I × X) × closedBall (0 : EuclideanSpace ℝ (Fin k)) d, M))
    (B : C((I × X) × (I × TopCat.diskBoundary.{u} k), M))
    (hAB : ∀ p θ, B (p, 0, θ) =
      A (p, ⟨(d : ℝ) • θ.down.1, TopCat.smul_diskBoundary_mem_closedBall d.2.1 θ⟩))
    {a : ℝ} (hA : ∀ p (v : closedBall (0 : EuclideanSpace ℝ (Fin k)) d),
      ‖(v : EuclideanSpace ℝ (Fin k))‖ = 1 → f (A (p, v)) ≤ a)
    (hB : ∀ p θ, f (B (p, 1, θ)) ≤ a) (t : I) (x : X) (s : TopCat.diskBoundary.{u} k) :
    f (stageGlue hd A B hAB (t, x, TopCat.diskBoundaryInclusion k s)) ≤ a :=
  TopCat.discGlue_mem_of_norm_eq_one (S := {x | f x ≤ a}) _ _ _ _ hA hB _
    (TopCat.norm_diskBoundaryInclusion s)

/-- `c - εa² ≤ c + ε`, so the sublevel `M_{c-εa²}` lies in `M_{c+ε}`. -/
private theorem sub_mul_sq_le_add (hε : 0 ≤ ε) (a : ℝ) : c - ε * a ^ 2 ≤ c + ε :=
  (sub_le_self _ (by positivity)).trans (le_add_of_nonneg_right hε)

variable {r : C({x : M | f x ≤ c - ε * (d : ℝ) ^ 2}, {x : M | f x ≤ c - ε * (d : ℝ) ^ 2})}
  (R : (ContinuousMap.id _).HomotopyRel r {x | f x.val ≤ c - ε}) (hr : ∀ x, f (r x).val ≤ c - ε)
  (hε : 0 ≤ ε) (hd : 0 < d)

/-- The deformation of the annulus of a family of discs to the retraction track of its inner
circle. -/
private def annulusDeformation (m : C(X × TopCat.disk.{u} k, M))
    (hm : ∀ x w, f (m (x, w)) ≤ c - ε * ‖w.down.1‖ ^ 2) :=
  R.annulusToTrack hr (familyAnnulus hε m hm) (familyAnnulus_one_mem hε m hm) (ContinuousMap.id I)
    rfl rfl

/-- The first stage for a family `m`: on the small discs it is `m`, and on the annuli it deforms
the annulus of `m` to the retraction track of its inner circle. -/
private def annulusStage (m : C(X × TopCat.disk.{u} k, M))
    (hm : ∀ x w, f (m (x, w)) ≤ c - ε * ‖w.down.1‖ ^ 2) : C(I × (X × TopCat.disk.{u} k), M) :=
  stageGlue hd ⟨fun p ↦ m (p.1.2, TopCat.smallDiskIncl d.2.2 p.2), by fun_prop⟩
    ⟨fun p ↦ (annulusDeformation R hr hε m hm (p.1.1, p.2.1, p.1.2, p.2.2) : M), by fun_prop⟩
    fun p θ ↦ by
      have h := ((annulusDeformation R hr hε m hm).prop p.1).1 (p.2, θ)
      simp only [ContinuousMap.HomotopyWith.coe_toHomotopy,
        ContinuousMap.Homotopy.curry_apply] at h
      simp [h, coe_familyAnnulus_apply, TopCat.annulusPoint_zero]

variable (m : C(X × TopCat.disk.{u} k, M)) (hm : ∀ x w, f (m (x, w)) ≤ c - ε * ‖w.down.1‖ ^ 2)

/-- On the small discs the first stage is `m` at all times. -/
private theorem annulusStage_of_norm_le (t : I) (x : X) {w : TopCat.disk.{u} k}
    (hw : ‖w.down.1‖ ≤ d) : annulusStage R hr hε hd m hm (t, x, w) = m (x, w) :=
  (stageGlue_of_norm_le hd _ _ _ t x hw).trans
    (congrArg (fun w ↦ m (x, w)) (TopCat.smallDiskIncl_mk d.2.2 _))

/-- On the annuli the first stage is the deformation of the annulus to the retraction track, read
in annulus coordinates. -/
private theorem annulusStage_of_le_norm (t : I) (x : X) {w : TopCat.disk.{u} k}
    (hw : d ≤ ‖w.down.1‖) :
    annulusStage R hr hε hd m hm (t, x, w) =
      (annulusDeformation R hr hε m hm
        (t, TopCat.annulusParam d w, x, TopCat.annulusDir (unitInterval.coe_pos.2 hd) ⟨w, hw⟩) :
        M) :=
  stageGlue_of_le_norm hd _ _ _ t x hw

/-- The first stage as a homotopy keeping the bounds `TauCeti.StageBound`. -/
private def annulusStageHomotopy :
    ContinuousMap.HomotopyWith m ((annulusStage R hr hε hd m hm).curry 1) (StageBound f c ε) where
  toFun := annulusStage R hr hε hd m hm
  continuous_toFun := (annulusStage R hr hε hd m hm).continuous
  map_zero_left q := by
    rcases le_total ‖q.2.down.1‖ d with hw | hw
    · exact annulusStage_of_norm_le R hr hε hd m hm 0 q.1 hw
    · rw [annulusStage_of_le_norm R hr hε hd m hm 0 q.1 hw, ContinuousMap.HomotopyWith.apply_zero,
        coe_familyAnnulus_apply, TopCat.annulusPoint_annulusParam_annulusDir _ d.2.2 ⟨q.2, hw⟩]
  map_one_left _ := rfl
  prop' t := by
    refine ⟨fun q ↦ stageGlue_le hd _ _ _ (fun q ↦ ?_) (fun q ↦ ?_) (t, q),
      fun x s ↦ stageGlue_boundary_le hd _ _ _ (fun p v hv ↦ ?_) (fun p θ ↦ ?_) t x s⟩
    · exact (hm _ _).trans (sub_mul_sq_le_add hε _)
    · exact (annulusDeformation R hr hε m hm _).2.trans (sub_mul_sq_le_add hε _)
    · exact (hm p.2 (TopCat.smallDiskIncl d.2.2 v)).trans_eq
        (by rw [TopCat.smallDiskIncl_apply, hv, one_pow, mul_one])
    · exact ((annulusDeformation R hr hε m hm).prop p.1).2 (p.2, θ)

end Stages

section Middle

variable {X : Type*} [TopologicalSpace X] {M : Type*} [TopologicalSpace M] {f : M → ℝ}
  {c ε : ℝ} {k : ℕ} {d : I}
  {r : C({x : M | f x ≤ c - ε * (d : ℝ) ^ 2}, {x : M | f x ≤ c - ε * (d : ℝ) ^ 2})}
  (R : (ContinuousMap.id _).HomotopyRel r {x | f x.val ≤ c - ε}) (hr : ∀ x, f (r x).val ≤ c - ε)
  (hε : 0 ≤ ε) (hd : 0 < d) {m₀ m₁ : C(X × TopCat.disk.{u} k, M)}
  (hm₀ : ∀ x w, f (m₀ (x, w)) ≤ c - ε * ‖w.down.1‖ ^ 2)
  (hm₁ : ∀ x w, f (m₁ (x, w)) ≤ c - ε * ‖w.down.1‖ ^ 2)
  (G : C(I × (X × closedBall (0 : EuclideanSpace ℝ (Fin k)) d), M))
  (hG₀ : ∀ x w, G (0, x, w) = m₁ (x, ⟨⟨w, closedBall_subset_closedBall d.2.2 w.2⟩⟩))
  (hG₁ : ∀ x w, G (1, x, w) = m₀ (x, ⟨⟨w, closedBall_subset_closedBall d.2.2 w.2⟩⟩))
  (hGf : ∀ p, f (G p) ≤ c + ε)
  (hGd : ∀ t x (w : closedBall (0 : EuclideanSpace ℝ (Fin k)) d),
    ‖(w : EuclideanSpace ℝ (Fin k))‖ = d → f (G (t, x, w)) ≤ c - ε * (d : ℝ) ^ 2)

/-- The homotopy `G` restricted to the inner circles, as a homotopy in `M_{c-εd²}` between the
inner circles of the annuli of `m₁` and `m₀`. -/
private def circleHomotopy :
    ContinuousMap.Homotopy
      ⟨fun q ↦ familyAnnulus (d := d) hε m₁ hm₁ (0, q), by fun_prop⟩
      ⟨fun q ↦ familyAnnulus (d := d) hε m₀ hm₀ (0, q), by fun_prop⟩ where
  toFun p := ⟨G (p.1, p.2.1,
      ⟨(d : ℝ) • p.2.2.down.1, TopCat.smul_diskBoundary_mem_closedBall d.2.1 p.2.2⟩),
    hGd _ _ _ (by rw [norm_smul, mem_sphere_zero_iff_norm.1 p.2.2.down.2,
      Real.norm_of_nonneg d.2.1, mul_one])⟩
  continuous_toFun := by fun_prop
  map_zero_left q := Subtype.ext (by
    simp only [ContinuousMap.coe_mk, hG₀, coe_familyAnnulus_apply, TopCat.annulusPoint_zero,
      TopCat.smallDiskIncl_apply])
  map_one_left q := Subtype.ext (by
    simp only [ContinuousMap.coe_mk, hG₁, coe_familyAnnulus_apply, TopCat.annulusPoint_zero,
      TopCat.smallDiskIncl_apply])

private theorem coe_circleHomotopy_apply (p : I × (X × TopCat.diskBoundary.{u} k)) :
    (circleHomotopy hε hm₀ hm₁ G hG₀ hG₁ hGd p : M) =
      G (p.1, p.2.1,
        ⟨(d : ℝ) • p.2.2.down.1, TopCat.smul_diskBoundary_mem_closedBall d.2.1 p.2.2⟩) :=
  (rfl)

/-- The second stage: move the small discs by `G`, together with the retraction tracks of their
boundary circles. -/
private def middleStage : C(I × (X × TopCat.disk.{u} k), M) :=
  stageGlue hd ⟨fun p ↦ G (p.1.1, p.1.2, p.2), by fun_prop⟩
    ⟨fun p ↦ (R.toHomotopy.retractionTrackHomotopy (ContinuousMap.id I)
      (circleHomotopy hε hm₀ hm₁ G hG₀ hG₁ hGd) (p.1.1, p.2.1, p.1.2, p.2.2) : M), by fun_prop⟩
    fun p θ ↦ by
      simp only [ContinuousMap.coe_mk, ContinuousMap.Homotopy.retractionTrackHomotopy_apply,
        ContinuousMap.id_apply, ContinuousMap.Homotopy.apply_zero, coe_circleHomotopy_apply]

/-- On the small discs the second stage is `G`. -/
private theorem middleStage_of_norm_le (t : I) (x : X) {w : TopCat.disk.{u} k}
    (hw : ‖w.down.1‖ ≤ d) :
    middleStage R hε hd hm₀ hm₁ G hG₀ hG₁ hGd (t, x, w) =
      G (t, x, ⟨w.down.1, mem_closedBall_zero_iff.2 hw⟩) :=
  stageGlue_of_norm_le hd _ _ _ t x hw

/-- On the annuli the second stage is the retraction track of `G` on the inner circles, read in
annulus coordinates. -/
private theorem middleStage_of_le_norm (t : I) (x : X) {w : TopCat.disk.{u} k}
    (hw : d ≤ ‖w.down.1‖) :
    middleStage R hε hd hm₀ hm₁ G hG₀ hG₁ hGd (t, x, w) =
      (R.toHomotopy.retractionTrackHomotopy (ContinuousMap.id I)
        (circleHomotopy hε hm₀ hm₁ G hG₀ hG₁ hGd)
        (t, TopCat.annulusParam d w, x, TopCat.annulusDir (unitInterval.coe_pos.2 hd) ⟨w, hw⟩) :
        M) :=
  stageGlue_of_le_norm hd _ _ _ t x hw

/-- The second stage as a homotopy keeping the bounds `TauCeti.StageBound`, from the end of the
first stage for `m₁` to the end of the first stage for `m₀`. -/
private def middleStageHomotopy :
    ContinuousMap.HomotopyWith ((annulusStage R hr hε hd m₁ hm₁).curry 1)
      ((annulusStage R hr hε hd m₀ hm₀).curry 1) (StageBound f c ε) where
  toFun := middleStage R hε hd hm₀ hm₁ G hG₀ hG₁ hGd
  continuous_toFun := (middleStage R hε hd hm₀ hm₁ G hG₀ hG₁ hGd).continuous
  map_zero_left q := by
    rw [ContinuousMap.curry_apply]
    rcases le_total ‖q.2.down.1‖ d with hw | hw
    · -- Both sides evaluate `m` at the point `q.2` of the disc, up to structure eta.
      rw [middleStage_of_norm_le (hw := hw), annulusStage_of_norm_le (hw := hw), hG₀]
      rfl
    · rw [middleStage_of_le_norm (hw := hw), annulusStage_of_le_norm (hw := hw)]
      simp [annulusDeformation]
  map_one_left q := by
    rw [ContinuousMap.curry_apply]
    rcases le_total ‖q.2.down.1‖ d with hw | hw
    · -- Both sides evaluate `m` at the point `q.2` of the disc, up to structure eta.
      rw [middleStage_of_norm_le (hw := hw), annulusStage_of_norm_le (hw := hw), hG₁]
      rfl
    · rw [middleStage_of_le_norm (hw := hw), annulusStage_of_le_norm (hw := hw)]
      simp [annulusDeformation]
  prop' t := by
    refine ⟨fun q ↦ stageGlue_le hd _ _ _ (fun q ↦ hGf _) (fun q ↦ ?_) (t, q),
      fun x s ↦ stageGlue_boundary_le hd _ _ _ (fun p v hv ↦ ?_) (fun p θ ↦ ?_) t x s⟩
    · exact (R.toHomotopy.retractionTrackHomotopy (ContinuousMap.id I)
        (circleHomotopy hε hm₀ hm₁ G hG₀ hG₁ hGd) _).2.trans (sub_mul_sq_le_add hε _)
    · -- A unit vector of the small disc forces `d = 1`.
      have hd₁ : (d : ℝ) = 1 := le_antisymm d.2.2 (hv ▸ mem_closedBall_zero_iff.1 v.2)
      simpa [hd₁] using hGd _ _ v (hv.trans hd₁.symm)
    · exact R.toHomotopy.retractionTrackHomotopy_one_mem (B := {x | f x.val ≤ c - ε}) hr rfl _ _
        (p.2, θ)

end Middle

section Topological

variable {X : Type*} [TopologicalSpace X] {M : Type*} [TopologicalSpace M] {f : M → ℝ}
  {c ε : ℝ} {k : ℕ}

/-- **A homotopy of families of small discs extends to the whole discs, given a deformation of the
band.** Let `m₀, m₁ : X × D^k → M` be families of discs parametrized by `X` with
`f (mⱼ (x, w)) ≤ c - ε‖w‖²`, as for the characteristic maps of Morse charts. Let `0 < d ≤ 1`, and
let `R` be a homotopy from the identity of `M_{c-εd²}` to a self-map `r` with values in `M_{c-ε}`,
fixing `M_{c-ε}`. Suppose that `G` is a homotopy, on the discs `‖w‖ ≤ d`, from `m₁` to `m₀`, with
values in `M_{c+ε}`, which keeps the spheres `‖w‖ = d` in `M_{c-εd²}`. Then `m₁` is homotopic to
`m₀` by a homotopy with values in `M_{c+ε}` which keeps `X × ∂D^k` in `M_{c-ε}`. -/
theorem exists_parametric_homotopy_of_innerDisc_of_homotopyRel (hε : 0 ≤ ε) {d : I} (hd : 0 < d)
    {r : C({x : M | f x ≤ c - ε * (d : ℝ) ^ 2}, {x : M | f x ≤ c - ε * (d : ℝ) ^ 2})}
    (R : (ContinuousMap.id _).HomotopyRel r {x | f x.val ≤ c - ε})
    (hr : ∀ x, f (r x).val ≤ c - ε) {m₀ m₁ : C(X × TopCat.disk.{u} k, M)}
    (hm₀ : ∀ x w, f (m₀ (x, w)) ≤ c - ε * ‖w.down.1‖ ^ 2)
    (hm₁ : ∀ x w, f (m₁ (x, w)) ≤ c - ε * ‖w.down.1‖ ^ 2)
    (G : C(I × (X × closedBall (0 : EuclideanSpace ℝ (Fin k)) d), M))
    (hG₀ : ∀ x w, G (0, x, w) = m₁ (x, ⟨⟨w, closedBall_subset_closedBall d.2.2 w.2⟩⟩))
    (hG₁ : ∀ x w, G (1, x, w) = m₀ (x, ⟨⟨w, closedBall_subset_closedBall d.2.2 w.2⟩⟩))
    (hGf : ∀ p, f (G p) ≤ c + ε)
    (hGd : ∀ t x (w : closedBall (0 : EuclideanSpace ℝ (Fin k)) d),
      ‖(w : EuclideanSpace ℝ (Fin k))‖ = d → f (G (t, x, w)) ≤ c - ε * (d : ℝ) ^ 2) :
    ∃ K : m₁.Homotopy m₀, (∀ p, f (K p) ≤ c + ε) ∧
      ∀ t x (s : TopCat.diskBoundary.{u} k),
        f (K (t, x, TopCat.diskBoundaryInclusion k s)) ≤ c - ε := by
  -- Deform the annuli of `m₁`, move the small discs with their tracks, and undo the annulus
  -- deformation for `m₀`.
  let K := (annulusStageHomotopy R hr hε hd m₁ hm₁).trans
    ((middleStageHomotopy R hr hε hd hm₀ hm₁ G hG₀ hG₁ hGf hGd).trans
      (annulusStageHomotopy R hr hε hd m₀ hm₀).symm)
  exact ⟨K.toHomotopy, fun p ↦ (K.prop p.1).1 p.2, fun t x s ↦ (K.prop t).2 x s⟩

/-- **A homotopy of small Morse discs extends to the characteristic maps, given a deformation of
the band.** Let `ψ₀` and `ψ₁` be charts with values in `ℝⁿ` in which
`f = c - Σ_{j < k} yⱼ² + Σ_{j ≥ k} yⱼ²`, whose targets contain the closed ball of radius `√ε`, with
characteristic maps `χ₀` and `χ₁`, and let `g` be a linear isometry of `ℝᵏ`. Let `0 < d ≤ 1`, and
let `R` be a homotopy from the identity of `M_{c-εd²}` to a self-map `r` with values in `M_{c-ε}`,
fixing `M_{c-ε}`. Suppose that `G` is a homotopy, on the disc `‖w‖ ≤ d`, from `w ↦ χ₁ w` to
`w ↦ χ₀ (g w)`, with values in `M_{c+ε}`, which keeps the sphere `‖w‖ = d` in `M_{c-εd²}`. Then
`χ₁` is homotopic to `χ₀ ∘ g` as a map of pairs `(D^k, ∂D^k) → (M_{c+ε}, M_{c-ε})`: the homotopy
keeps the boundary sphere in `M_{c-ε}`. -/
theorem exists_homotopy_morseCharacteristicMap_of_innerDisc_of_homotopyRel
    {M : Type u} [TopologicalSpace M] {f : M → ℝ} {n : ℕ}
    {ψ₀ ψ₁ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))} (hk : k ≤ n) (hε : 0 ≤ ε)
    (hball₀ : closedBall 0 √ε ⊆ ψ₀.target) (hball₁ : closedBall 0 √ε ⊆ ψ₁.target)
    (hf₀ : ∀ y ∈ ψ₀.source, f y = c + ∑ j, (if j.val < k then -1 else 1) * ψ₀ y j ^ 2)
    (hf₁ : ∀ y ∈ ψ₁.source, f y = c + ∑ j, (if j.val < k then -1 else 1) * ψ₁ y j ^ 2)
    (g : EuclideanSpace ℝ (Fin k) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin k)) {d : I} (hd : 0 < d)
    {r : C({x : M | f x ≤ c - ε * (d : ℝ) ^ 2}, {x : M | f x ≤ c - ε * (d : ℝ) ^ 2})}
    (R : (ContinuousMap.id _).HomotopyRel r {x | f x.val ≤ c - ε})
    (hr : ∀ x, f (r x).val ≤ c - ε)
    (G : C(I × closedBall (0 : EuclideanSpace ℝ (Fin k)) d, M))
    (hG₀ : ∀ w, G (0, w) = ψ₁.morseCellMap hk ε w)
    (hG₁ : ∀ w, G (1, w) = ψ₀.morseCellMap hk ε (g w))
    (hGf : ∀ t w, f (G (t, w)) ≤ c + ε)
    (hGd : ∀ t (w : closedBall (0 : EuclideanSpace ℝ (Fin k)) d),
      ‖(w : EuclideanSpace ℝ (Fin k))‖ = d → f (G (t, w)) ≤ c - ε * (d : ℝ) ^ 2) :
    ∃ K : (ψ₁.morseCharacteristicMap hk hε hball₁ hf₁).hom.Homotopy
        (g.diskMap ≫ ψ₀.morseCharacteristicMap hk hε hball₀ hf₀).hom,
      ∀ t (s : TopCat.diskBoundary.{u} k), f (K (t, TopCat.diskBoundaryInclusion k s)) ≤ c - ε := by
  -- Apply the parametric statement over a one-point parameter space.
  let m₀ : C(Unit × TopCat.disk.{u} k, M) :=
    ⟨fun q ↦ ψ₀.morseCellMap hk ε (g q.2.down.1),
      (ψ₀.continuousOn_morseCellMap hball₀ hk).comp_continuous (by fun_prop) fun q ↦ by
        rw [mem_closedBall_zero_iff, g.norm_map]
        exact mem_closedBall_zero_iff.1 q.2.down.2⟩
  let m₁ : C(Unit × TopCat.disk.{u} k, M) :=
    ⟨fun q ↦ ψ₁.morseCellMap hk ε q.2.down.1,
      (ψ₁.continuousOn_morseCellMap hball₁ hk).comp_continuous (by fun_prop) fun q ↦ q.2.down.2⟩
  have hm₀ : ∀ x w, f (m₀ (x, w)) ≤ c - ε * ‖w.down.1‖ ^ 2 := fun _ w ↦ by
    have hw := mem_closedBall_zero_iff.1 w.down.2
    rw [← g.norm_map] at hw ⊢
    exact (OpenPartialHomeomorph.apply_morseCellMap_eq_sub_mul_norm_sq hball₀ hf₀ hk hε hw).le
  have hm₁ : ∀ x w, f (m₁ (x, w)) ≤ c - ε * ‖w.down.1‖ ^ 2 := fun _ w ↦
    (OpenPartialHomeomorph.apply_morseCellMap_eq_sub_mul_norm_sq hball₁ hf₁ hk hε
      (mem_closedBall_zero_iff.1 w.down.2)).le
  obtain ⟨K, hKf, hKd⟩ := exists_parametric_homotopy_of_innerDisc_of_homotopyRel hε hd R hr hm₀
    hm₁ ⟨fun p : I × (Unit × _) ↦ G (p.1, p.2.2), by fun_prop⟩ (fun _ w ↦ hG₀ w)
    (fun _ w ↦ hG₁ w) (fun p ↦ hGf _ _) (fun t _ w hw ↦ hGd t w hw)
  exact ⟨{ toFun p := ⟨K (p.1, (), p.2), hKf _⟩
           continuous_toFun := (K.continuous.comp (by fun_prop)).subtype_mk _
           -- The endpoints of `K` are `m₁` and `m₀`, which unfold to the characteristic maps.
           map_zero_left w := Subtype.ext ((K.apply_zero ((), w)).trans
             (OpenPartialHomeomorph.coe_morseCharacteristicMap_apply hball₁ hf₁ hk hε w).symm)
           map_one_left w := Subtype.ext ((K.apply_one ((), w)).trans (by
             rw [TopCat.hom_comp, ContinuousMap.comp_apply,
               OpenPartialHomeomorph.coe_morseCharacteristicMap_apply,
               LinearIsometryEquiv.coe_diskMap_apply_down]
             rfl)) },
    fun t s ↦ hKd t () s⟩

end Topological

section Main

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {Iₘ : ModelWithCorners ℝ E H} [Iₘ.Boundaryless]
  {M : Type v} [TopologicalSpace M] [ChartedSpace H M] [IsManifold Iₘ ∞ M] [T2Space M]
  {f : M → ℝ} {c ε : ℝ} {n k : ℕ}

/-- A compact band `f⁻¹[c - ε, c - εd²]` without critical points supplies a deformation of
`M_{c-εd²}` into `M_{c-ε}` fixing `M_{c-ε}`. -/
private theorem exists_homotopyRel_sublevel (hf : ContMDiff Iₘ 𝓘(ℝ) ∞ f) {d : I}
    (hcompact : IsCompact (f ⁻¹' Icc (c - ε) (c - ε * (d : ℝ) ^ 2)))
    (hreg : ∀ x, c - ε ≤ f x → f x ≤ c - ε * (d : ℝ) ^ 2 → mfderiv Iₘ 𝓘(ℝ) f x ≠ 0)
    (hε : 0 ≤ ε) :
    ∃ r : C({x : M | f x ≤ c - ε * (d : ℝ) ^ 2}, {x : M | f x ≤ c - ε * (d : ℝ) ^ 2}),
      (∀ x, f (r x).val ≤ c - ε) ∧
        Nonempty ((ContinuousMap.id _).HomotopyRel r {x | f x.val ≤ c - ε}) := by
  have hab : c - ε ≤ c - ε * (d : ℝ) ^ 2 := by
    have := pow_le_one₀ d.2.1 d.2.2 (n := 2)
    nlinarith
  obtain ⟨r, -, ⟨R⟩⟩ := exists_sublevelDeformation hf hab hcompact hreg
  refine ⟨_, fun x ↦ ?_, ⟨R.symm⟩⟩
  rw [ContinuousMap.comp_apply, coe_sublevelInclusion_apply]
  exact (r x).2

/-- **A homotopy of families of small discs extends to the whole discs.** Let `m₀, m₁ : X × D^k → M`
be families of discs parametrized by `X` with `f (mⱼ (x, w)) ≤ c - ε‖w‖²`, as for the
characteristic maps of Morse charts. Let `0 < d ≤ 1` be such that the band `f⁻¹[c - ε, c - εd²]` is
compact and free of critical points. Suppose that `G` is a homotopy, on the discs `‖w‖ ≤ d`, from
`m₁` to `m₀`, with values in `M_{c+ε}`, which keeps the spheres `‖w‖ = d` in `M_{c-εd²}`. Then `m₁`
is homotopic to `m₀` by a homotopy with values in `M_{c+ε}` which keeps `X × ∂D^k` in
`M_{c-ε}`. -/
theorem exists_parametric_homotopy_of_innerDisc {X : Type*} [TopologicalSpace X]
    (hf : ContMDiff Iₘ 𝓘(ℝ) ∞ f) (hε : 0 ≤ ε) {d : I} (hd : 0 < d)
    (hcompact : IsCompact (f ⁻¹' Icc (c - ε) (c - ε * (d : ℝ) ^ 2)))
    (hreg : ∀ x, c - ε ≤ f x → f x ≤ c - ε * (d : ℝ) ^ 2 → mfderiv Iₘ 𝓘(ℝ) f x ≠ 0)
    {m₀ m₁ : C(X × TopCat.disk.{u} k, M)}
    (hm₀ : ∀ x w, f (m₀ (x, w)) ≤ c - ε * ‖w.down.1‖ ^ 2)
    (hm₁ : ∀ x w, f (m₁ (x, w)) ≤ c - ε * ‖w.down.1‖ ^ 2)
    (G : C(I × (X × closedBall (0 : EuclideanSpace ℝ (Fin k)) d), M))
    (hG₀ : ∀ x w, G (0, x, w) = m₁ (x, ⟨⟨w, closedBall_subset_closedBall d.2.2 w.2⟩⟩))
    (hG₁ : ∀ x w, G (1, x, w) = m₀ (x, ⟨⟨w, closedBall_subset_closedBall d.2.2 w.2⟩⟩))
    (hGf : ∀ p, f (G p) ≤ c + ε)
    (hGd : ∀ t x (w : closedBall (0 : EuclideanSpace ℝ (Fin k)) d),
      ‖(w : EuclideanSpace ℝ (Fin k))‖ = d → f (G (t, x, w)) ≤ c - ε * (d : ℝ) ^ 2) :
    ∃ K : m₁.Homotopy m₀, (∀ p, f (K p) ≤ c + ε) ∧
      ∀ t x (s : TopCat.diskBoundary.{u} k),
        f (K (t, x, TopCat.diskBoundaryInclusion k s)) ≤ c - ε := by
  obtain ⟨r, hr, ⟨R⟩⟩ := exists_homotopyRel_sublevel hf hcompact hreg hε
  exact exists_parametric_homotopy_of_innerDisc_of_homotopyRel hε hd R hr hm₀ hm₁ G hG₀ hG₁ hGf hGd

/-- **A homotopy of small Morse discs extends to the characteristic maps.** Let `ψ₀` and `ψ₁` be
charts with values in `ℝⁿ` in which `f = c - Σ_{j < k} yⱼ² + Σ_{j ≥ k} yⱼ²`, whose targets contain
the closed ball of radius `√ε`, with characteristic maps `χ₀` and `χ₁`, and let `g` be a linear
isometry of `ℝᵏ`. Let `0 < d ≤ 1` be such that the band `f⁻¹[c - ε, c - εd²]` is compact and free
of critical points. Suppose that `G` is a homotopy, on the disc `‖w‖ ≤ d`, from `w ↦ χ₁ w` to
`w ↦ χ₀ (g w)`, with values in `M_{c+ε}`, which keeps the sphere `‖w‖ = d` in `M_{c-εd²}`. Then
`χ₁` is homotopic to `χ₀ ∘ g` as a map of pairs `(D^k, ∂D^k) → (M_{c+ε}, M_{c-ε})`: the homotopy
keeps the boundary sphere in `M_{c-ε}`. -/
theorem exists_homotopy_morseCharacteristicMap_of_innerDisc (hf : ContMDiff Iₘ 𝓘(ℝ) ∞ f)
    {ψ₀ ψ₁ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))} (hk : k ≤ n) (hε : 0 ≤ ε)
    (hball₀ : closedBall 0 √ε ⊆ ψ₀.target) (hball₁ : closedBall 0 √ε ⊆ ψ₁.target)
    (hf₀ : ∀ y ∈ ψ₀.source, f y = c + ∑ j, (if j.val < k then -1 else 1) * ψ₀ y j ^ 2)
    (hf₁ : ∀ y ∈ ψ₁.source, f y = c + ∑ j, (if j.val < k then -1 else 1) * ψ₁ y j ^ 2)
    (g : EuclideanSpace ℝ (Fin k) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin k)) {d : I} (hd : 0 < d)
    (hcompact : IsCompact (f ⁻¹' Icc (c - ε) (c - ε * (d : ℝ) ^ 2)))
    (hreg : ∀ x, c - ε ≤ f x → f x ≤ c - ε * (d : ℝ) ^ 2 → mfderiv Iₘ 𝓘(ℝ) f x ≠ 0)
    (G : C(I × closedBall (0 : EuclideanSpace ℝ (Fin k)) d, M))
    (hG₀ : ∀ w, G (0, w) = ψ₁.morseCellMap hk ε w)
    (hG₁ : ∀ w, G (1, w) = ψ₀.morseCellMap hk ε (g w))
    (hGf : ∀ t w, f (G (t, w)) ≤ c + ε)
    (hGd : ∀ t (w : closedBall (0 : EuclideanSpace ℝ (Fin k)) d),
      ‖(w : EuclideanSpace ℝ (Fin k))‖ = d → f (G (t, w)) ≤ c - ε * (d : ℝ) ^ 2) :
    ∃ K : (ψ₁.morseCharacteristicMap hk hε hball₁ hf₁).hom.Homotopy
        (g.diskMap ≫ ψ₀.morseCharacteristicMap hk hε hball₀ hf₀).hom,
      ∀ t (s : TopCat.diskBoundary.{v} k), f (K (t, TopCat.diskBoundaryInclusion k s)) ≤ c - ε := by
  obtain ⟨r, hr, ⟨R⟩⟩ := exists_homotopyRel_sublevel hf hcompact hreg hε
  exact exists_homotopy_morseCharacteristicMap_of_innerDisc_of_homotopyRel hk hε hball₀ hball₁ hf₀
    hf₁ g hd R hr G hG₀ hG₁ hGf hGd

end Main

end TauCeti
