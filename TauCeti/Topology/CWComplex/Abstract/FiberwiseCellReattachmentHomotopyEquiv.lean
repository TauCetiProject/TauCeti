/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.CWComplex.Abstract.FiberwiseCellAttachment
import TauCeti.Topology.Homotopy.Homotopic.Rel

/-!
# Fiberwise cell reattachment maps are homotopy equivalences

For two families `χ₀` and `χ₁` of characteristic maps over a parameter space `P`, self-maps `h i`
of `P × D^{k i}` over `P` preserving `P × ∂D^{k i}` and homotopies `K i : χ₁ i ≃ χ₀ i ∘ (p, h i)`
keeping `P × ∂D^{k i}` in `A`, the fiberwise reattachment map
`E : (P × A) ∪_{α₁} ⨆ᵢ (P × D^{k i}) → (P × A) ∪_{α₀} ⨆ᵢ (P × D^{k i})`
is `TauCeti.fiberwiseCellReattachment`.

When the maps `h i (p, ·)` are invertible, with inverses continuous in `p` and preserving the
boundary spheres, `E` is a homotopy equivalence over `P` relative to `P × A`
(`TauCeti.exists_homotopyRel_fiberwiseCellReattachment_comp`), with no hypothesis on the
comparison maps. Indeed `E` factors as the reattachment along `K` which does not move the discs,
followed by the homeomorphism reparametrizing the discs by `h`
(`TauCeti.fiberwiseCellAttachmentIso`), and a reattachment which does not move the discs is
inverted by the reattachment along the reverse homotopy: on a cell their composite runs along `K`
on the boundary sphere and back again, and contracting this excursion gives a homotopy to the
identity over `P`, relative to `P × A`.

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  Lemma 3.6 and Remark 3.3.
-/

public section

noncomputable section

open CategoryTheory Limits Set Metric unitInterval

universe u

namespace TauCeti

variable {P Y : Type u} [TopologicalSpace P] [TopologicalSpace Y] {A : Set Y} {ι : Type u}
  {k : ι → ℕ}

section Inverse

/-! ### Reattaching along a homotopy and back

When the self-maps of the discs are the identity, reattaching along a homotopy `K` of families of
characteristic maps and then along the reverse homotopy gives a map of the fiberwise adjunction
space which is homotopic to the identity, over `P` and relative to `P × A`. On a cell it is
`x ↦ 4x` on the disc of radius `1/4`, and on the annulus `1/4 ≤ ‖x‖` it runs along `K` on the
boundary sphere forward and then back, at the times `4‖x‖ - 1` and `2 - 2‖x‖`. Capping these
times by `1 - u` contracts the excursion along `K`, and the radial push of the disc of radius `1/4`
then undoes the rescaling `x ↦ 4x`.
-/

variable (α₀ α₁ : ∀ i, C(P × TopCat.diskBoundary.{u} (k i), A))
  (χ₀ χ₁ : ∀ i, C(P × TopCat.disk.{u} (k i), Y))
  (hχ₀ : ∀ i p s, χ₀ i (p, TopCat.diskBoundaryInclusion (k i) s) = α₀ i (p, s))
  (hχ₁ : ∀ i p s, χ₁ i (p, TopCat.diskBoundaryInclusion (k i) s) = α₁ i (p, s))
  (K : ∀ i, (χ₁ i).Homotopy ((χ₀ i).comp (ContinuousMap.fst.prodMk ContinuousMap.snd)))
  (hK : ∀ i t p s, K i (t, (p, TopCat.diskBoundaryInclusion (k i) s)) ∈ A)

variable (k) in
/-- The second projection `P × D^{k i} → D^{k i}` preserves the boundary spheres. -/
private theorem mapsTo_snd (i : ι) (p : P) :
    MapsTo
      (fun w ↦ (ContinuousMap.snd : C(P × TopCat.disk.{u} (k i), TopCat.disk.{u} (k i))) (p, w))
      (range (TopCat.diskBoundaryInclusion (k i))) (range (TopCat.diskBoundaryInclusion (k i))) :=
  fun _ hw ↦ hw

/-- The time `min (3s, (3 - 3s)/2, 1 - u)` along the homotopy at which the point of radial
parameter `s` of the annulus `1/4 ≤ ‖x‖` is read, at stage `u` of the contraction. -/
private def undoTime (u s : I) : I :=
  projIcc 0 1 zero_le_one (min (min (3 * (s : ℝ)) ((3 - 3 * s) / 2)) (1 - u))

@[fun_prop]
private theorem continuous_undoTime {X : Type*} [TopologicalSpace X] {f g : X → I}
    (hf : Continuous f) (hg : Continuous g) : Continuous fun x ↦ undoTime (f x) (g x) :=
  continuous_projIcc.comp (by fun_prop)

private theorem coe_undoTime (u s : I) :
    (undoTime u s : ℝ) = min (min (3 * (s : ℝ)) ((3 - 3 * s) / 2)) (1 - u) := by
  have h₀ : 0 ≤ min (min (3 * (s : ℝ)) ((3 - 3 * s) / 2)) (1 - u) :=
    le_min (le_min (by linarith [s.2.1]) (by linarith [s.2.2])) (by linarith [u.2.2])
  have h₁ : min (min (3 * (s : ℝ)) ((3 - 3 * s) / 2)) (1 - u) ≤ 1 :=
    (min_le_right _ _).trans (by linarith [u.2.1])
  rw [undoTime, coe_projIcc, min_eq_right h₁, max_eq_right h₀]

private theorem undoTime_zero_right (u : I) : undoTime u 0 = 0 :=
  Subtype.ext ((coe_undoTime u 0).trans (by
    rw [Icc.coe_zero, mul_zero, sub_zero, min_eq_left (by norm_num : (0 : ℝ) ≤ 3 / 2)]
    exact min_eq_left (by linarith [u.2.2])))

/-- On the disc of radius `1/4`, the factor `4` keeps a point in the unit disc. -/
private theorem four_smul_mem_closedBall {n : ℕ}
    (v : closedBall (0 : EuclideanSpace ℝ (Fin n)) (1 / 4)) :
    (4 : ℝ) • (v : EuclideanSpace ℝ (Fin n)) ∈ closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 := by
  rw [mem_closedBall_zero_iff, norm_smul, Real.norm_of_nonneg (by norm_num)]
  linarith [mem_closedBall_zero_iff.1 v.2]

include hχ₁ in
/-- On the `i`-th family of discs, stage `u` of the contraction: `x ↦ 4x` into the `i`-th cell on
the disc of radius `1/4`, and on the annulus the homotopy `K i` on the boundary sphere read at the
time `TauCeti.undoTime`. -/
private def undoCell (i : ι) : C((I × P) × TopCat.disk.{u} (k i), fiberwiseCellAttachment α₁) :=
  TopCat.discGlue (by norm_num : (0 : ℝ) < 1 / 4)
    ⟨fun q ↦ fiberwiseCellAttachmentCell α₁ i
        (q.1.2, ULift.up ⟨(4 : ℝ) • (q.2 : EuclideanSpace ℝ (Fin (k i))),
          four_smul_mem_closedBall q.2⟩),
      (fiberwiseCellAttachmentCell α₁ i).hom.continuous.comp (by fun_prop)⟩
    ⟨fun q ↦ fiberwiseCellAttachmentIncl α₁
        (q.1.2, ⟨K i (undoTime q.1.1 q.2.1, (q.1.2, TopCat.diskBoundaryInclusion (k i) q.2.2)),
          hK i _ _ _⟩),
      (fiberwiseCellAttachmentIncl α₁).hom.continuous.comp (by fun_prop)⟩
    fun q θ ↦ by
      -- On the seam the time vanishes, and `K i` starts at `χ₁ i`, which is `α₁ i` on the sphere.
      have hθ : (ULift.up ⟨(4 : ℝ) • (1 / 4 : ℝ) • θ.down.1, four_smul_mem_closedBall
          ⟨(1 / 4 : ℝ) • θ.down.1, TopCat.smul_diskBoundary_mem_closedBall (by norm_num) θ⟩⟩ :
            TopCat.disk.{u} (k i)) = TopCat.diskBoundaryInclusion (k i) θ :=
        ULift.ext (Subtype.ext (by
          simp only [smul_smul, TopCat.coe_diskBoundaryInclusion_apply_down]
          norm_num))
      simp only [ContinuousMap.coe_mk, undoTime_zero_right, ContinuousMap.Homotopy.apply_zero,
        hχ₁]
      rw [hθ, fiberwiseCellAttachmentCell_diskBoundaryInclusion]

private theorem undoCell_of_norm_le (i : ι) (u : I) (p : P) {w v : TopCat.disk.{u} (k i)}
    (hw : ‖w.down.1‖ ≤ 1 / 4) (hv : v.down.1 = (4 : ℝ) • w.down.1) :
    undoCell α₁ χ₀ χ₁ hχ₁ K hK i ((u, p), w) = fiberwiseCellAttachmentCell α₁ i (p, v) := by
  rw [undoCell, TopCat.discGlue_apply_of_norm_le _ _ _ _ _ hw]
  exact congrArg (fun v ↦ fiberwiseCellAttachmentCell α₁ i (p, v))
    (ULift.ext (Subtype.ext hv.symm))

private theorem undoCell_of_le_norm (i : ι) (u : I) (p : P) {w : TopCat.disk.{u} (k i)}
    (hw : 1 / 4 ≤ ‖w.down.1‖) {t : I}
    (ht : (t : ℝ) = min (min (4 * ‖w.down.1‖ - 1) (2 - 2 * ‖w.down.1‖)) (1 - u))
    {s : TopCat.diskBoundary.{u} (k i)} (hs : s.down.1 = ‖w.down.1‖⁻¹ • w.down.1) :
    undoCell α₁ χ₀ χ₁ hχ₁ K hK i ((u, p), w) =
      fiberwiseCellAttachmentIncl α₁
        (p, ⟨K i (t, (p, TopCat.diskBoundaryInclusion (k i) s)), hK i t p s⟩) := by
  have ha := TopCat.add_one_sub_mul_annulusParam (by norm_num : (1 / 4 : ℝ) ≤ 1) hw
  have ht' : undoTime u (TopCat.annulusParam (1 / 4) w) = t := by
    refine Subtype.ext ((coe_undoTime _ _).trans (ht ▸ ?_))
    have h₁ : (3 - 3 * (TopCat.annulusParam (1 / 4) w : ℝ)) / 2 = 2 - 2 * ‖w.down.1‖ := by
      linarith
    have h₂ : 3 * (TopCat.annulusParam (1 / 4) w : ℝ) = 4 * ‖w.down.1‖ - 1 := by linarith
    rw [h₁, h₂]
  have hs' : TopCat.annulusDir (by norm_num) ⟨w, hw⟩ = s :=
    ULift.ext (Subtype.ext ((TopCat.coe_annulusDir _ _).trans hs.symm))
  rw [undoCell, TopCat.discGlue_apply_of_le_norm _ _ _ _ _ hw]
  simp only [ContinuousMap.coe_mk, ht', hs']


include hχ₁ in
/-- At every stage of the contraction, the boundary sphere of the `i`-th family of discs goes to
its attaching map. -/
private theorem undoCell_diskBoundaryInclusion (i : ι) (u : I) (p : P)
    (s : TopCat.diskBoundary.{u} (k i)) :
    undoCell α₁ χ₀ χ₁ hχ₁ K hK i ((u, p), TopCat.diskBoundaryInclusion (k i) s) =
      fiberwiseCellAttachmentIncl α₁ (p, α₁ i (p, s)) := by
  rw [undoCell_of_le_norm α₁ χ₀ χ₁ hχ₁ K hK i u p (t := 0) (s := s)
    (by rw [TopCat.norm_diskBoundaryInclusion]; norm_num)
    (by rw [TopCat.norm_diskBoundaryInclusion, Icc.coe_zero]; norm_num [u.2.2])
    (by rw [TopCat.norm_diskBoundaryInclusion, inv_one, one_smul,
      TopCat.coe_diskBoundaryInclusion_apply_down])]
  exact congrArg (fun a ↦ fiberwiseCellAttachmentIncl α₁ (p, a))
    (Subtype.ext ((K i).apply_zero _ |>.trans (hχ₁ i p s)))

/-- Every stage of the contraction lies over `P`. -/
private theorem fiberwiseCellAttachmentProj_undoCell (i : ι) (u : I) (p : P)
    (w : TopCat.disk.{u} (k i)) :
    fiberwiseCellAttachmentProj α₁ (undoCell α₁ χ₀ χ₁ hχ₁ K hK i ((u, p), w)) = p := by
  rcases le_total ‖w.down.1‖ (1 / 4) with hw | hw
  · rw [undoCell, TopCat.discGlue_apply_of_norm_le _ _ _ _ _ hw]
    exact fiberwiseCellAttachmentProj_fiberwiseCellAttachmentCell α₁ i _
  · rw [undoCell, TopCat.discGlue_apply_of_le_norm _ _ _ _ _ hw]
    exact fiberwiseCellAttachmentProj_fiberwiseCellAttachmentIncl α₁ _

include hχ₁ in
/-- The contraction `I × ((P × A) ∪_{α₁} ⨆ᵢ (P × D^{k i})) → (P × A) ∪_{α₁} ⨆ᵢ (P × D^{k i})`: the
identity on `P × A`, and `TauCeti.undoCell` on the cylinders over the cells. -/
private def undoHomotopyFun : C(I × fiberwiseCellAttachment α₁, fiberwiseCellAttachment α₁) :=
  fiberwiseCellAttachmentCylinderDesc α₁
    ((fiberwiseCellAttachmentIncl α₁).hom.comp ContinuousMap.snd)
    (fun i ↦ (undoCell α₁ χ₀ χ₁ hχ₁ K hK i).comp ⟨fun q ↦ ((q.1, q.2.1), q.2.2), by fun_prop⟩)
    fun i t p s ↦ undoCell_diskBoundaryInclusion α₁ χ₀ χ₁ hχ₁ K hK i t p s

private theorem undoHomotopyFun_fiberwiseCellAttachmentIncl (t : I) (x : P × A) :
    undoHomotopyFun α₁ χ₀ χ₁ hχ₁ K hK (t, fiberwiseCellAttachmentIncl α₁ x) =
      fiberwiseCellAttachmentIncl α₁ x :=
  fiberwiseCellAttachmentCylinderDesc_fiberwiseCellAttachmentIncl α₁ _ _ _ t x

private theorem undoHomotopyFun_fiberwiseCellAttachmentCell (t : I) (i : ι)
    (x : P × TopCat.disk.{u} (k i)) :
    undoHomotopyFun α₁ χ₀ χ₁ hχ₁ K hK (t, fiberwiseCellAttachmentCell α₁ i x) =
      undoCell α₁ χ₀ χ₁ hχ₁ K hK i ((t, x.1), x.2) :=
  fiberwiseCellAttachmentCylinderDesc_fiberwiseCellAttachmentCell α₁ _ _ _ t i x

/-- The radial push of every cell at the end of its homotopy: `x ↦ 4x` on the disc of radius
`1/4`, with the annulus `1/4 ≤ ‖x‖` pushed onto the boundary sphere. -/
private def radialPushMap : fiberwiseCellAttachment α₁ ⟶ fiberwiseCellAttachment α₁ :=
  fiberwiseCellAttachmentDesc α₁ (fiberwiseCellAttachmentIncl α₁)
    (fun i ↦ TopCat.ofHom ⟨fun x ↦ fiberwiseCellAttachmentCell α₁ i
        (x.1, TopCat.diskRadialPush (k i) (by norm_num : (0 : ℝ) ≤ 1 / 4) (1, x.2)),
      (fiberwiseCellAttachmentCell α₁ i).hom.continuous.comp (continuous_fst.prodMk
        ((TopCat.diskRadialPush (k i) _).continuous.comp
          (continuous_const.prodMk continuous_snd)))⟩)
    fun i p s ↦ (congrArg (fun w ↦ fiberwiseCellAttachmentCell α₁ i (p, w))
      (TopCat.diskRadialPush_diskBoundaryInclusion (by norm_num) (by norm_num) 1 s)).trans
      (fiberwiseCellAttachmentCell_diskBoundaryInclusion α₁ i p s)

private theorem radialPushMap_fiberwiseCellAttachmentCell (i : ι) (p : P)
    (w : TopCat.disk.{u} (k i)) :
    radialPushMap α₁ (fiberwiseCellAttachmentCell α₁ i (p, w)) =
      fiberwiseCellAttachmentCell α₁ i
        (p, TopCat.diskRadialPush (k i) (by norm_num : (0 : ℝ) ≤ 1 / 4) (1, w)) :=
  fiberwiseCellAttachmentDesc_fiberwiseCellAttachmentCell α₁ _ _ _ i (p, w)

/-- The radial push of the cells, undone along the radial push homotopy of the discs. -/
private def pushHomotopyFun : C(I × fiberwiseCellAttachment α₁, fiberwiseCellAttachment α₁) :=
  fiberwiseCellAttachmentCylinderDesc α₁
    ((fiberwiseCellAttachmentIncl α₁).hom.comp ContinuousMap.snd)
    (fun i ↦ ⟨fun q ↦ fiberwiseCellAttachmentCell α₁ i
        (q.2.1, TopCat.diskRadialPush (k i) (by norm_num : (0 : ℝ) ≤ 1 / 4) (σ q.1, q.2.2)),
      (fiberwiseCellAttachmentCell α₁ i).hom.continuous.comp ((continuous_fst.comp continuous_snd)
        |>.prodMk ((TopCat.diskRadialPush (k i) _).continuous.comp
          ((continuous_symm.comp continuous_fst).prodMk (continuous_snd.comp continuous_snd))))⟩)
    fun i t p s ↦ by
      rw [ContinuousMap.coe_mk,
        TopCat.diskRadialPush_diskBoundaryInclusion (by norm_num) (by norm_num),
        fiberwiseCellAttachmentCell_diskBoundaryInclusion, ContinuousMap.comp_apply,
        ContinuousMap.snd_apply]

private theorem pushHomotopyFun_fiberwiseCellAttachmentIncl (t : I) (x : P × A) :
    pushHomotopyFun α₁ (t, fiberwiseCellAttachmentIncl α₁ x) = fiberwiseCellAttachmentIncl α₁ x :=
  fiberwiseCellAttachmentCylinderDesc_fiberwiseCellAttachmentIncl α₁ _ _ _ t x

private theorem pushHomotopyFun_fiberwiseCellAttachmentCell (t : I) (i : ι)
    (x : P × TopCat.disk.{u} (k i)) :
    pushHomotopyFun α₁ (t, fiberwiseCellAttachmentCell α₁ i x) =
      fiberwiseCellAttachmentCell α₁ i
        (x.1, TopCat.diskRadialPush (k i) (by norm_num : (0 : ℝ) ≤ 1 / 4) (σ t, x.2)) :=
  fiberwiseCellAttachmentCylinderDesc_fiberwiseCellAttachmentCell α₁ _ _ _ t i x

/-- The radial push of the cells is homotopic to the identity, relative to `P × A`. -/
private def pushHomotopy :
    (radialPushMap α₁).hom.HomotopyRel (ContinuousMap.id _)
      (range (fiberwiseCellAttachmentIncl α₁)) where
  toFun := pushHomotopyFun α₁
  continuous_toFun := (pushHomotopyFun α₁).continuous
  map_zero_left y := by
    refine fiberwiseCellAttachment_induction α₁ (fun x ↦ ?_) (fun i x ↦ ?_) y
    · rw [pushHomotopyFun_fiberwiseCellAttachmentIncl]
      exact (fiberwiseCellAttachmentDesc_fiberwiseCellAttachmentIncl α₁ _ _ _ x).symm
    · rw [pushHomotopyFun_fiberwiseCellAttachmentCell, symm_zero]
      exact (radialPushMap_fiberwiseCellAttachmentCell α₁ i x.1 x.2).symm
  map_one_left y := by
    refine fiberwiseCellAttachment_induction α₁ (fun x ↦ ?_) (fun i x ↦ ?_) y
    · exact pushHomotopyFun_fiberwiseCellAttachmentIncl α₁ 1 x
    · rw [pushHomotopyFun_fiberwiseCellAttachmentCell, symm_one, TopCat.diskRadialPush_zero,
        Prod.mk.eta, ContinuousMap.id_apply]
  prop' t y hy := by
    obtain ⟨x, rfl⟩ := hy
    exact (pushHomotopyFun_fiberwiseCellAttachmentIncl α₁ t x).trans
      (fiberwiseCellAttachmentDesc_fiberwiseCellAttachmentIncl α₁ _ _ _ x).symm

private theorem fiberwiseCellAttachmentProj_pushHomotopy (t : I)
    (y : fiberwiseCellAttachment α₁) :
    fiberwiseCellAttachmentProj α₁ (pushHomotopy α₁ (t, y)) = fiberwiseCellAttachmentProj α₁ y :=
  fiberwiseCellAttachmentProj_fiberwiseCellAttachmentCylinderDesc α₁ _ _ _
    (fun _ x ↦ fiberwiseCellAttachmentProj_fiberwiseCellAttachmentIncl α₁ x)
    (fun i _ _ ↦ fiberwiseCellAttachmentProj_fiberwiseCellAttachmentCell α₁ i _) t y


variable (K' : ∀ i, (χ₀ i).Homotopy ((χ₁ i).comp (ContinuousMap.fst.prodMk ContinuousMap.snd)))
  (hK' : ∀ i t p s, K' i (t, (p, TopCat.diskBoundaryInclusion (k i) s)) ∈ A)
  (hKK' : ∀ i t p s, K' i (t, (p, TopCat.diskBoundaryInclusion (k i) s)) =
    K i (σ t, (p, TopCat.diskBoundaryInclusion (k i) s)))

include hKK' in
/-- At the start of the contraction, `TauCeti.undoCell` is the reattachment map along `K` followed
by the reattachment map along the reverse homotopy `K'`, on the `i`-th cell. -/
private theorem undoCell_zero (i : ι) (p : P) (w : TopCat.disk.{u} (k i)) :
    undoCell α₁ χ₀ χ₁ hχ₁ K hK i ((0, p), w) =
      fiberwiseCellReattachment α₁ α₀ χ₁ χ₀ hχ₁ hχ₀ (fun _ ↦ ContinuousMap.snd)
        (mapsTo_snd k) K' hK'
        (fiberwiseCellReattachment α₀ α₁ χ₀ χ₁ hχ₀ hχ₁ (fun _ ↦ ContinuousMap.snd)
          (mapsTo_snd k) K hK (fiberwiseCellAttachmentCell α₁ i (p, w))) := by
  set v := TopCat.reattachmentRadial w
  rcases le_total ‖w.down.1‖ (1 / 2) with hw | hw
  · -- The first reattachment map sends `w` to the point `v = 2w` of the `i`-th cell.
    have hv : v.down.1 = (2 : ℝ) • w.down.1 := TopCat.coe_reattachmentRadial_of_norm_le hw
    have hvn : ‖v.down.1‖ = 2 * ‖w.down.1‖ := by
      rw [hv, norm_smul, Real.norm_of_nonneg zero_le_two]
    rw [fiberwiseCellReattachment_fiberwiseCellAttachmentCell_of_norm_le (hw := hw) (hv := hv)]
    simp only [ContinuousMap.snd_apply]
    rcases le_total ‖w.down.1‖ (1 / 4) with hw' | hw'
    · -- On the disc of radius `1/4` both maps are `w ↦ 4w`.
      have hv' : (TopCat.reattachmentRadial v).down.1 = (2 : ℝ) • v.down.1 :=
        TopCat.coe_reattachmentRadial_of_norm_le (by rw [hvn]; linarith)
      rw [fiberwiseCellReattachment_fiberwiseCellAttachmentCell_of_norm_le (w := v)
        (hw := by rw [hvn]; linarith) (hv := hv'),
        undoCell_of_norm_le α₁ χ₀ χ₁ hχ₁ K hK i 0 p hw' (by rw [hv', hv, smul_smul]; norm_num)]
      simp only [ContinuousMap.snd_apply]
    · -- On the annulus `1/4 ≤ ‖w‖ ≤ 1/2` the reverse homotopy is read at time `2 - 4‖w‖`.
      have hvn' : 1 / 2 ≤ ‖v.down.1‖ := by rw [hvn]; linarith
      obtain ⟨t, ht⟩ : ∃ t : I, (t : ℝ) = 2 - 2 * ‖v.down.1‖ :=
        ⟨TopCat.reattachmentTime v, TopCat.coe_reattachmentTime_of_le_norm hvn'⟩
      obtain ⟨s, hs⟩ : ∃ s : TopCat.diskBoundary.{u} (k i), s.down.1 = ‖v.down.1‖⁻¹ • v.down.1 :=
        ⟨TopCat.annulusDir (by norm_num) ⟨v, hvn'⟩, TopCat.coe_annulusDir _ _⟩
      rw [fiberwiseCellReattachment_fiberwiseCellAttachmentCell_of_le_norm (w := v) (hw := hvn')
        (ht := ht) (hs := hs), undoCell_of_le_norm α₁ χ₀ χ₁ hχ₁ K hK i 0 p hw' (t := σ t) (s := s)
        (by
          rw [coe_symm_eq, ht, hvn, Icc.coe_zero, sub_zero,
            min_eq_left (show 4 * ‖w.down.1‖ - 1 ≤ 2 - 2 * ‖w.down.1‖ by linarith),
            min_eq_left (show 4 * ‖w.down.1‖ - 1 ≤ 1 by linarith)]
          ring)
        (by rw [hs, hvn, hv, smul_smul, mul_inv_rev, mul_assoc, inv_mul_cancel₀ two_ne_zero,
          mul_one])]
      exact congrArg (fun a ↦ fiberwiseCellAttachmentIncl α₁ (p, a))
        (Subtype.ext (hKK' i t p s).symm)
  · -- On the annulus `1/2 ≤ ‖w‖` the homotopy is read at time `2 - 2‖w‖`, and the second
    -- reattachment map fixes `P × A`.
    obtain ⟨t, ht⟩ : ∃ t : I, (t : ℝ) = 2 - 2 * ‖w.down.1‖ :=
      ⟨TopCat.reattachmentTime w, TopCat.coe_reattachmentTime_of_le_norm hw⟩
    obtain ⟨s, hs⟩ : ∃ s : TopCat.diskBoundary.{u} (k i), s.down.1 = ‖w.down.1‖⁻¹ • w.down.1 :=
      ⟨TopCat.annulusDir (by norm_num) ⟨w, hw⟩, TopCat.coe_annulusDir _ _⟩
    rw [fiberwiseCellReattachment_fiberwiseCellAttachmentCell_of_le_norm (hw := hw) (ht := ht)
      (hs := hs), fiberwiseCellReattachment_fiberwiseCellAttachmentIncl,
      undoCell_of_le_norm α₁ χ₀ χ₁ hχ₁ K hK i 0 p (by linarith) (t := t) (s := s)
        (by
          rw [ht, Icc.coe_zero, sub_zero,
            min_eq_right (show 2 - 2 * ‖w.down.1‖ ≤ 4 * ‖w.down.1‖ - 1 by linarith),
            min_eq_left (show 2 - 2 * ‖w.down.1‖ ≤ 1 by linarith)]) hs]

/-- At the end of the contraction, `TauCeti.undoCell` is the radial push of the `i`-th cell. -/
private theorem undoCell_one (i : ι) (p : P) (w : TopCat.disk.{u} (k i)) :
    undoCell α₁ χ₀ χ₁ hχ₁ K hK i ((1, p), w) =
      radialPushMap α₁ (fiberwiseCellAttachmentCell α₁ i (p, w)) := by
  have hw₁ : ‖w.down.1‖ ≤ 1 := mem_closedBall_zero_iff.1 w.down.2
  rw [radialPushMap_fiberwiseCellAttachmentCell]
  rcases le_total ‖w.down.1‖ (1 / 4) with hw | hw
  · exact undoCell_of_norm_le α₁ χ₀ χ₁ hχ₁ K hK i 1 p hw (by
      rw [TopCat.coe_diskRadialPush_one_of_norm_le _ hw]; norm_num)
  · have hpush : TopCat.diskRadialPush (k i) (by norm_num : (0 : ℝ) ≤ 1 / 4) (1, w) =
        TopCat.diskBoundaryInclusion (k i) (TopCat.annulusDir (by norm_num) ⟨w, hw⟩) :=
      (TopCat.diskBoundaryInclusion_annulusDir _ ⟨w, hw⟩).symm
    rw [undoCell_of_le_norm α₁ χ₀ χ₁ hχ₁ K hK i 1 p hw (t := 0)
      (s := TopCat.annulusDir (by norm_num) ⟨w, hw⟩)
      (by rw [Icc.coe_one, sub_self, Icc.coe_zero, min_eq_right (le_min (by linarith)
        (by linarith))]) (TopCat.coe_annulusDir _ _),
      hpush, fiberwiseCellAttachmentCell_diskBoundaryInclusion]
    exact congrArg (fun a ↦ fiberwiseCellAttachmentIncl α₁ (p, a))
      (Subtype.ext ((K i).apply_zero _ |>.trans (hχ₁ i p _)))

include hKK' in
/-- The contraction of the excursion along `K`, from the reattachment map along `K` followed by
the reattachment map along its reverse to the radial push of the cells, relative to `P × A`. -/
private def undoHomotopy :
    (fiberwiseCellReattachment α₀ α₁ χ₀ χ₁ hχ₀ hχ₁ (fun _ ↦ ContinuousMap.snd)
        (mapsTo_snd k) K hK ≫
      fiberwiseCellReattachment α₁ α₀ χ₁ χ₀ hχ₁ hχ₀ (fun _ ↦ ContinuousMap.snd)
        (mapsTo_snd k) K' hK').hom.HomotopyRel (radialPushMap α₁).hom
      (range (fiberwiseCellAttachmentIncl α₁)) where
  toFun := undoHomotopyFun α₁ χ₀ χ₁ hχ₁ K hK
  continuous_toFun := (undoHomotopyFun α₁ χ₀ χ₁ hχ₁ K hK).continuous
  map_zero_left y := by
    refine fiberwiseCellAttachment_induction α₁ (fun x ↦ ?_) (fun i x ↦ ?_) y
    · rw [undoHomotopyFun_fiberwiseCellAttachmentIncl, TopCat.hom_comp, ContinuousMap.comp_apply,
        fiberwiseCellReattachment_fiberwiseCellAttachmentIncl,
        fiberwiseCellReattachment_fiberwiseCellAttachmentIncl]
    · rw [undoHomotopyFun_fiberwiseCellAttachmentCell,
        undoCell_zero α₀ α₁ χ₀ χ₁ hχ₀ hχ₁ K hK K' hK' hKK', Prod.mk.eta, TopCat.hom_comp,
        ContinuousMap.comp_apply]
  map_one_left y := by
    refine fiberwiseCellAttachment_induction α₁ (fun x ↦ ?_) (fun i x ↦ ?_) y
    · rw [undoHomotopyFun_fiberwiseCellAttachmentIncl]
      exact (fiberwiseCellAttachmentDesc_fiberwiseCellAttachmentIncl α₁ _ _ _ x).symm
    · rw [undoHomotopyFun_fiberwiseCellAttachmentCell, undoCell_one]
  prop' t y hy := by
    obtain ⟨x, rfl⟩ := hy
    rw [ContinuousMap.coe_mk, undoHomotopyFun_fiberwiseCellAttachmentIncl, TopCat.hom_comp,
      ContinuousMap.comp_apply, fiberwiseCellReattachment_fiberwiseCellAttachmentIncl,
      fiberwiseCellReattachment_fiberwiseCellAttachmentIncl]

include hKK' in
/-- **Reattaching along a homotopy and back is homotopic to the identity, over `P`.** Let
`K i : χ₁ i ≃ χ₀ i` be homotopies of families of characteristic maps keeping the boundary spheres
in `A`, and let `K' i : χ₀ i ≃ χ₁ i` agree on the boundary spheres with the reverse of `K i`. The
fiberwise reattachment map along `K` (with the identity of the discs), followed by the fiberwise
reattachment map along `K'`, is homotopic to the identity of
`(P × A) ∪_{α₁} ⨆ᵢ (P × D^{k i})`, relative to `P × A`, through maps over `P`. -/
private theorem exists_homotopyRel_reattachment_comp_symm :
    ∃ F : (fiberwiseCellReattachment α₀ α₁ χ₀ χ₁ hχ₀ hχ₁ (fun _ ↦ ContinuousMap.snd)
          (mapsTo_snd k) K hK ≫
        fiberwiseCellReattachment α₁ α₀ χ₁ χ₀ hχ₁ hχ₀ (fun _ ↦ ContinuousMap.snd)
          (mapsTo_snd k) K' hK').hom.HomotopyRel (ContinuousMap.id _)
        (range (fiberwiseCellAttachmentIncl α₁)),
      ∀ t y, fiberwiseCellAttachmentProj α₁ (F (t, y)) = fiberwiseCellAttachmentProj α₁ y := by
  refine ⟨(undoHomotopy α₀ α₁ χ₀ χ₁ hχ₀ hχ₁ K hK K' hK' hKK').trans (pushHomotopy α₁),
    fun t y ↦ ?_⟩
  rw [ContinuousMap.HomotopyRel.trans_apply]
  split_ifs
  · exact fiberwiseCellAttachmentProj_fiberwiseCellAttachmentCylinderDesc α₁ _ _ _
      (fun _ x ↦ fiberwiseCellAttachmentProj_fiberwiseCellAttachmentIncl α₁ x)
      (fun i _ x ↦ fiberwiseCellAttachmentProj_undoCell α₁ χ₀ χ₁ hχ₁ K hK i _ x.1 x.2) _ y
  · exact fiberwiseCellAttachmentProj_pushHomotopy α₁ _ y

end Inverse

section HomotopyEquiv

variable (α₀ α₁ : ∀ i, C(P × TopCat.diskBoundary.{u} (k i), A))
  (χ₀ χ₁ : ∀ i, C(P × TopCat.disk.{u} (k i), Y))
  (hχ₀ : ∀ i p s, χ₀ i (p, TopCat.diskBoundaryInclusion (k i) s) = α₀ i (p, s))
  (hχ₁ : ∀ i p s, χ₁ i (p, TopCat.diskBoundaryInclusion (k i) s) = α₁ i (p, s))
  (h : ∀ i, C(P × TopCat.disk.{u} (k i), TopCat.disk.{u} (k i)))
  (hh : ∀ i p, MapsTo (fun w ↦ h i (p, w)) (range (TopCat.diskBoundaryInclusion (k i)))
    (range (TopCat.diskBoundaryInclusion (k i))))
  (K : ∀ i, (χ₁ i).Homotopy ((χ₀ i).comp (ContinuousMap.fst.prodMk (h i))))
  (hK : ∀ i t p s, K i (t, (p, TopCat.diskBoundaryInclusion (k i) s)) ∈ A)

/-- The end `(p, s) ↦ K i (1, (p, s))` of the homotopies on the boundary spheres: the attaching
maps `α₀ i (p, h i (p, s))` of the characteristic families `χ₀ i ∘ (p, h i)`. -/
private def endAttachingMap (i : ι) : C(P × TopCat.diskBoundary.{u} (k i), A) :=
  ⟨fun x ↦ ⟨K i (1, (x.1, TopCat.diskBoundaryInclusion (k i) x.2)), hK i 1 x.1 x.2⟩,
    ((K i).continuous.comp (continuous_const.prodMk (continuous_fst.prodMk
      ((TopCat.diskBoundaryInclusion (k i)).hom.continuous.comp continuous_snd)))).subtype_mk _⟩

private theorem comp_diskBoundaryInclusion_eq_endAttachingMap (i : ι) (p : P)
    (s : TopCat.diskBoundary.{u} (k i)) :
    ((χ₀ i).comp (ContinuousMap.fst.prodMk (h i))) (p, TopCat.diskBoundaryInclusion (k i) s) =
      endAttachingMap χ₀ χ₁ h K hK i (p, s) :=
  ((K i).apply_one _).symm

/-- `K i`, read as a homotopy from `χ₁ i` to `χ₀ i ∘ (p, h i)` composed with the identity of the
discs. -/
private def castHomotopy (i : ι) :
    (χ₁ i).Homotopy (((χ₀ i).comp (ContinuousMap.fst.prodMk (h i))).comp
      (ContinuousMap.fst.prodMk ContinuousMap.snd)) :=
  (K i).cast rfl (ContinuousMap.ext fun _ ↦ by simp)

/-- The reverse of `K i`, read as a homotopy from `χ₀ i ∘ (p, h i)` to `χ₁ i` composed with the
identity of the discs. -/
private def symmHomotopy (i : ι) :
    ((χ₀ i).comp (ContinuousMap.fst.prodMk (h i))).Homotopy
      ((χ₁ i).comp (ContinuousMap.fst.prodMk ContinuousMap.snd)) :=
  (K i).symm.cast rfl (ContinuousMap.ext fun _ ↦ by simp)

include hK in
private theorem castHomotopy_mem (i : ι) (t : I) (p : P) (s : TopCat.diskBoundary.{u} (k i)) :
    castHomotopy χ₀ χ₁ h K i (t, (p, TopCat.diskBoundaryInclusion (k i) s)) ∈ A :=
  hK i t p s

include hK in
private theorem symmHomotopy_mem (i : ι) (t : I) (p : P) (s : TopCat.diskBoundary.{u} (k i)) :
    symmHomotopy χ₀ χ₁ h K i (t, (p, TopCat.diskBoundaryInclusion (k i) s)) ∈ A :=
  hK i (σ t) p s

include hχ₀ in
private theorem endAttachingMap_eq (i : ι) (p : P) (s s' : TopCat.diskBoundary.{u} (k i))
    (hs : h i (p, TopCat.diskBoundaryInclusion (k i) s) = TopCat.diskBoundaryInclusion (k i) s') :
    endAttachingMap χ₀ χ₁ h K hK i (p, s) = α₀ i (p, s') :=
  Subtype.ext (((K i).apply_one _).trans (by
    rw [ContinuousMap.comp_apply, ContinuousMap.prod_eval, ContinuousMap.fst_apply, hs, hχ₀]))

/-- The reattachment map along `K` and `h` is the reattachment map along `K` with the identity of
the discs, into the attachment along the end of `K`, followed by the reparametrization of the
discs by `h`. -/
private theorem fiberwiseCellReattachment_eq_comp_fiberwiseCellAttachmentIso
    (h' : ∀ i, C(P × TopCat.disk.{u} (k i), TopCat.disk.{u} (k i)))
    (hh' : ∀ i p, MapsTo (fun w ↦ h' i (p, w)) (range (TopCat.diskBoundaryInclusion (k i)))
      (range (TopCat.diskBoundaryInclusion (k i))))
    (hh'h : ∀ i p w, h' i (p, h i (p, w)) = w) (hhh' : ∀ i p w, h i (p, h' i (p, w)) = w) :
    fiberwiseCellReattachment α₀ α₁ χ₀ χ₁ hχ₀ hχ₁ h hh K hK =
      fiberwiseCellReattachment (endAttachingMap χ₀ χ₁ h K hK) α₁
          (fun i ↦ (χ₀ i).comp (ContinuousMap.fst.prodMk (h i))) χ₁
          (comp_diskBoundaryInclusion_eq_endAttachingMap χ₀ χ₁ h K hK) hχ₁
          (fun _ ↦ ContinuousMap.snd) (mapsTo_snd k) (castHomotopy χ₀ χ₁ h K)
          (castHomotopy_mem χ₀ χ₁ h K hK) ≫
        (fiberwiseCellAttachmentIso α₀ (endAttachingMap χ₀ χ₁ h K hK) h h' hh hh' hh'h hhh'
          (endAttachingMap_eq α₀ χ₀ χ₁ hχ₀ h K hK)).hom := by
  refine fiberwiseCellAttachment_hom_ext α₁ (fun x ↦ ?_) fun i x ↦ ?_
  · rw [ConcreteCategory.comp_apply, fiberwiseCellReattachment_fiberwiseCellAttachmentIncl,
      fiberwiseCellReattachment_fiberwiseCellAttachmentIncl,
      fiberwiseCellAttachmentIso_hom_fiberwiseCellAttachmentIncl]
  obtain ⟨p, w⟩ := x
  rw [ConcreteCategory.comp_apply]
  rcases le_total ‖w.down.1‖ (1 / 2) with hw | hw
  · have hv := TopCat.coe_reattachmentRadial_of_norm_le hw
    rw [fiberwiseCellReattachment_fiberwiseCellAttachmentCell_of_norm_le (hw := hw) (hv := hv),
      fiberwiseCellReattachment_fiberwiseCellAttachmentCell_of_norm_le (hw := hw) (hv := hv),
      fiberwiseCellAttachmentIso_hom_fiberwiseCellAttachmentCell]
    simp only [ContinuousMap.snd_apply]
  · obtain ⟨s, hs⟩ : ∃ s : TopCat.diskBoundary.{u} (k i), s.down.1 = ‖w.down.1‖⁻¹ • w.down.1 :=
      ⟨TopCat.annulusDir (by norm_num) ⟨w, hw⟩, TopCat.coe_annulusDir _ _⟩
    obtain ⟨t, ht⟩ : ∃ t : I, (t : ℝ) = 2 - 2 * ‖w.down.1‖ :=
      ⟨TopCat.reattachmentTime w, TopCat.coe_reattachmentTime_of_le_norm hw⟩
    rw [fiberwiseCellReattachment_fiberwiseCellAttachmentCell_of_le_norm (hw := hw) (ht := ht)
        (hs := hs),
      fiberwiseCellReattachment_fiberwiseCellAttachmentCell_of_le_norm (hw := hw) (ht := ht)
        (hs := hs),
      fiberwiseCellAttachmentIso_hom_fiberwiseCellAttachmentIncl]
    simp only [castHomotopy, ContinuousMap.Homotopy.cast_apply]

/-- **The fiberwise reattachment map is a homotopy equivalence over `P`, relative to `P × A`.**
Let `E : (P × A) ∪_{α₁} ⨆ᵢ (P × D^{k i}) → (P × A) ∪_{α₀} ⨆ᵢ (P × D^{k i})` be the fiberwise
reattachment map of a family of homotopies `K i : χ₁ i ≃ χ₀ i ∘ (p, h i)` keeping the boundary
spheres in `A`, where the self-maps `h i (p, ·)` of the disc pairs are invertible, with inverses
`h' i (p, ·)` continuous in `p` and preserving the boundary spheres. Then `E` has a homotopy
inverse `E'` over `P` which is the identity on `P × A`, and both composites are homotopic to the
identities relative to `P × A`, through maps over `P`. The inverse is the reparametrization of the
discs by `h'` followed by the reattachment map along the reverse of `K`. -/
theorem exists_homotopyRel_fiberwiseCellReattachment_comp
    (h' : ∀ i, C(P × TopCat.disk.{u} (k i), TopCat.disk.{u} (k i)))
    (hh' : ∀ i p, MapsTo (fun w ↦ h' i (p, w)) (range (TopCat.diskBoundaryInclusion (k i)))
      (range (TopCat.diskBoundaryInclusion (k i))))
    (hh'h : ∀ i p w, h' i (p, h i (p, w)) = w) (hhh' : ∀ i p w, h i (p, h' i (p, w)) = w) :
    ∃ E' : fiberwiseCellAttachment α₀ ⟶ fiberwiseCellAttachment α₁,
      fiberwiseCellAttachmentIncl α₀ ≫ E' = fiberwiseCellAttachmentIncl α₁ ∧
      (∀ y, fiberwiseCellAttachmentProj α₁ (E' y) = fiberwiseCellAttachmentProj α₀ y) ∧
      (∃ F : (fiberwiseCellReattachment α₀ α₁ χ₀ χ₁ hχ₀ hχ₁ h hh K hK ≫ E').hom.HomotopyRel
          (ContinuousMap.id _) (range (fiberwiseCellAttachmentIncl α₁)),
        ∀ t y, fiberwiseCellAttachmentProj α₁ (F (t, y)) = fiberwiseCellAttachmentProj α₁ y) ∧
      (∃ F : (E' ≫ fiberwiseCellReattachment α₀ α₁ χ₀ χ₁ hχ₀ hχ₁ h hh K hK).hom.HomotopyRel
          (ContinuousMap.id _) (range (fiberwiseCellAttachmentIncl α₀)),
        ∀ t y, fiberwiseCellAttachmentProj α₀ (F (t, y)) = fiberwiseCellAttachmentProj α₀ y) := by
  -- Write `E = E₀ ≫ J`, where `E₀` reattaches along `K` without moving the discs, into the
  -- attachment along the end `α` of `K`, and `J` reparametrizes the discs by `h`.
  set α := endAttachingMap χ₀ χ₁ h K hK
  set χ := fun i ↦ (χ₀ i).comp (ContinuousMap.fst.prodMk (h i))
  have hχ := comp_diskBoundaryInclusion_eq_endAttachingMap χ₀ χ₁ h K hK
  have hKc := castHomotopy_mem χ₀ χ₁ h K hK
  have hKs := symmHomotopy_mem χ₀ χ₁ h K hK
  set J := fiberwiseCellAttachmentIso α₀ α h h' hh hh' hh'h hhh'
    (endAttachingMap_eq α₀ χ₀ χ₁ hχ₀ h K hK)
  set E₀ := fiberwiseCellReattachment α α₁ χ χ₁ hχ hχ₁ (fun _ ↦ ContinuousMap.snd) (mapsTo_snd k)
    (castHomotopy χ₀ χ₁ h K) hKc
  set E₁ := fiberwiseCellReattachment α₁ α χ₁ χ hχ₁ hχ (fun _ ↦ ContinuousMap.snd) (mapsTo_snd k)
    (symmHomotopy χ₀ χ₁ h K) hKs
  have hE : fiberwiseCellReattachment α₀ α₁ χ₀ χ₁ hχ₀ hχ₁ h hh K hK = E₀ ≫ J.hom :=
    fiberwiseCellReattachment_eq_comp_fiberwiseCellAttachmentIso α₀ α₁ χ₀ χ₁ hχ₀ hχ₁ h hh K hK h'
      hh' hh'h hhh'
  obtain ⟨F₁, hF₁⟩ := exists_homotopyRel_reattachment_comp_symm
    α α₁ χ χ₁ hχ hχ₁ (castHomotopy χ₀ χ₁ h K) hKc (symmHomotopy χ₀ χ₁ h K) hKs
    fun i t p s ↦ by
      simp only [castHomotopy, symmHomotopy, ContinuousMap.Homotopy.cast_apply,
        ContinuousMap.Homotopy.symm_apply]
  obtain ⟨F₀, hF₀⟩ := exists_homotopyRel_reattachment_comp_symm
    α₁ α χ₁ χ hχ₁ hχ (symmHomotopy χ₀ χ₁ h K) hKs (castHomotopy χ₀ χ₁ h K) hKc
    fun i t p s ↦ by
      simp only [castHomotopy, symmHomotopy, ContinuousMap.Homotopy.cast_apply,
        ContinuousMap.Homotopy.symm_apply, symm_symm]
  refine ⟨J.inv ≫ E₁, ?_, fun y ↦ ?_, ⟨F₁.cast ?_ rfl, fun t y ↦ hF₁ t y⟩, ?_⟩
  · ext x
    rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply,
      fiberwiseCellAttachmentIso_inv_fiberwiseCellAttachmentIncl,
      fiberwiseCellReattachment_fiberwiseCellAttachmentIncl]
  · rw [ConcreteCategory.comp_apply, fiberwiseCellAttachmentProj_fiberwiseCellReattachment,
      fiberwiseCellAttachmentProj_fiberwiseCellAttachmentIso_inv]
  · -- `E ≫ E' = E₀ ≫ J ≫ J⁻¹ ≫ E₁ = E₀ ≫ E₁`.
    rw [hE, Category.assoc, Iso.hom_inv_id_assoc]
  -- `E' ≫ E = J⁻¹ ≫ (E₁ ≫ E₀) ≫ J`, and `E₁ ≫ E₀` is homotopic to the identity.
  have hS : range (fiberwiseCellAttachmentIncl α₀) ⊆
      J.inv.hom ⁻¹' range (fiberwiseCellAttachmentIncl α) := by
    rintro _ ⟨x, rfl⟩
    exact ⟨x, (fiberwiseCellAttachmentIso_inv_fiberwiseCellAttachmentIncl ..).symm⟩
  refine ⟨(((F₀.precomp J.inv.hom).mono hS).compContinuousMap J.hom.hom).cast
    (by rw [hE]; ext y; simp only [ContinuousMap.comp_apply, TopCat.hom_comp, E₀, E₁])
    (by ext y; simp),
    fun t y ↦ ?_⟩
  rw [ContinuousMap.HomotopyRel.cast_apply, ContinuousMap.HomotopyRel.compContinuousMap_apply,
    ContinuousMap.HomotopyRel.mono_apply, ContinuousMap.HomotopyRel.precomp_apply]
  exact ((fiberwiseCellAttachmentProj_fiberwiseCellAttachmentIso_hom ..).trans (hF₀ t _)).trans
    (fiberwiseCellAttachmentProj_fiberwiseCellAttachmentIso_inv ..)

end HomotopyEquiv

end TauCeti
