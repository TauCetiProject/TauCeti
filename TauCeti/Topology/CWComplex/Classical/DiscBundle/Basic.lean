/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import TauCeti.Topology.CWComplex.Classical.Finite
public import TauCeti.Topology.CWComplex.Classical.OpenCells
public import TauCeti.Topology.VectorBundle.Contractible
import Mathlib.Analysis.Convex.Contractible
import TauCeti.Analysis.Normed.Module.Ball.Homeomorph
import TauCeti.Topology.FiberBundle.Separation
import TauCeti.Topology.MetricSpace.Isometry.Basic
import TauCeti.Topology.Separation.InvFunOn

/-!
# The disc bundle of a vector bundle over a CW complex

Let `E → B` be a real vector bundle of rank `r` over a Hausdorff space, with finite-dimensional
model fibre and fibre inner products whose norm is continuous on the total space, and let `C` be a
CW complex relative to `D` in `B`. Write `D(E)` and `S(E)` for the unit disc and sphere bundles
(`TauCeti.discBundle`, `TauCeti.sphereBundle`). This file shows that the part `D(E)|_C` of the disc
bundle over `C` is a CW complex relative to `S(E)|_C ∪ D(E)|_D`, with one `(m + r)`-cell for each
`m`-cell of `C` (`TauCeti.relCWComplexDiscBundle`, `TauCeti.cellDiscBundleEquiv`). No orientation
of `E` is needed. The closed cell over a closed cell `e` of `C` is the part `D(E)|_e` of the disc
bundle over `e` (`TauCeti.closedCell_relCWComplexDiscBundle`), its open cell consists of the
vectors of norm less than one over the open cell of `e`
(`TauCeti.openCell_relCWComplexDiscBundle`), and its boundary is `S(E)|_e ∪ D(E)|_∂e`
(`TauCeti.cellFrontier_relCWComplexDiscBundle`).

Over the whole of a CW complex `B`, this gives a relative CW structure on `D(E)` relative to
`S(E)` (`TauCeti.relCWComplexDiscBundleSphereBundle`), and over a relative CW pair `(B, A)`, `D(E)`
carries a relative CW structure relative to `S(E) ∪ D(E)|_A` (`TauCeti.relCWComplexDiscBundleRel`).
Finiteness properties (`FiniteDimensional`, `FiniteType`, `Finite`) are preserved in all cases. The
corresponding subtype structures on `univ : Set (discBundle F E)` are in
`TauCeti.Topology.CWComplex.Classical.DiscBundle.Subtype`.

The characteristic map of the cell over an `m`-cell `j` of `C` is built from a continuous
orthonormal frame `φ` of `E` along the characteristic map `χ` of `j`
(`TauCeti.discBundleCellFrame`): splitting the coordinates of `Fin (m + r) → ℝ` into base
coordinates `y : Fin m → ℝ` and fibre coordinates `z : Fin r → ℝ`, it sends `(y, z)` to the vector
`φ_y (σ z)` over `χ y` (`TauCeti.map_relCWComplexDiscBundle_apply`), where `σ`
(`TauCeti.discBundleFibreCoord`) carries the unit ball of the sup norm on `Fin r → ℝ` radially onto
the unit ball of the Euclidean space of dimension `r` (`ContinuousLinearEquiv.unitBallHomeomorph`).
The unit sphere of the sup norm on `Fin (m + r) → ℝ` is `(Sᵐ⁻¹ × Dʳ) ∪ (Dᵐ × Sʳ⁻¹)`, so the
boundary of the cell lies in `D(E)|_∂j ∪ S(E)`.

The inverse of the characteristic map is continuous on the open cell because the closed unit ball
is compact and its boundary sphere is mapped outside the open cell. The weak topology comes from
that of `C`, because the projection of the disc bundle onto the base is proper
(`TauCeti.isProperMap_discBundle_proj`). Let `v` be a point outside a set `A` which meets every
closed cell and the base in closed sets. The points of `A` over `π v` form a compact set, which
has a neighbourhood `W` missing a neighbourhood of `v`; the projection of the rest of `A`, outside
`W`, is closed in the weak topology of `C` and misses `π v`.

## Main definitions

* `TauCeti.discBundleFibreCoord`, `TauCeti.discBundleCellFrame`: the radial fibre coordinate
  homeomorphism and chosen continuous orthonormal frame along a base cell.
* `TauCeti.relCWComplexDiscBundle`: the relative CW structure on `D(E)|_C`, relative to
  `S(E)|_C ∪ D(E)|_D`.
* `TauCeti.cellDiscBundleEquiv`: its `n`-cells are the `m`-cells of `C` with `m + r = n`.
* `TauCeti.relCWComplexDiscBundleSphereBundle` and `TauCeti.relCWComplexDiscBundleRel`: the
  relative CW structures on `D(E)` in `TotalSpace F E` relative to `S(E)` and to `S(E) ∪ D(E)|_A`.

## Main results

* `TauCeti.isEmpty_cell_relCWComplexDiscBundle_of_lt`: there are no cells below the rank.
* `TauCeti.map_relCWComplexDiscBundle_apply` and `TauCeti.proj_map_relCWComplexDiscBundle`: the
  explicit evaluation and projection formulas for the characteristic maps.
* `TauCeti.closedCell_relCWComplexDiscBundle`, `TauCeti.openCell_relCWComplexDiscBundle` and
  `TauCeti.cellFrontier_relCWComplexDiscBundle`: the closed cells, open cells and cell boundaries.
* `TauCeti.finite_relCWComplexDiscBundle`, `TauCeti.finite_relCWComplexDiscBundleSphereBundle`,
  and `TauCeti.finite_relCWComplexDiscBundleRel`: finiteness preservation for disc bundles.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton University Press, 1974, §18 (the cell structure of the Thom space of a bundle over a
  CW complex).
* A. Hatcher, *Vector Bundles and K-Theory*, §4.D (disc bundles and Thom spaces).
-/

public section

noncomputable section

open Bundle Metric Set Topology Topology.RelCWComplex

universe u

namespace TauCeti

variable {B : Type u} [TopologicalSpace B] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type u} [∀ b, NormedAddCommGroup (E b)]
  [∀ b, InnerProductSpace ℝ (E b)] [TopologicalSpace (TotalSpace F E)] [FiberBundle F E]
  [VectorBundle ℝ F E] [ContinuousFiberNorm F E] {C D : Set B} [RelCWComplex C D]

section Cells

variable (F C) in
/-- The `n`-cells of the disc bundle over `C`: the `m`-cells of `C` with `m + r = n`, where `r` is
the rank of the bundle. -/
private abbrev DiscCell (n : ℕ) : Type u :=
  Σ m : {m : ℕ // m + Module.finrank ℝ F = n}, cell C m

variable (F) in
/-- The radial identification of the sup-norm coordinates `Fin r → ℝ` of the fibre directions of a
cell with the Euclidean space of dimension `r`. It matches the open unit balls, the closed unit
balls and the unit spheres. -/
def discBundleFibreCoord :
    (Fin (Module.finrank ℝ F) → ℝ) ≃ₜ EuclideanSpace ℝ (Fin (Module.finrank ℝ F)) :=
  (EuclideanSpace.equiv (Fin (Module.finrank ℝ F)) ℝ).symm.unitBallHomeomorph

/-- Forward evaluation formula for `TauCeti.discBundleFibreCoord`: it rescales the Euclidean vector
`WithLp.toLp 2 z` so that its Euclidean norm equals the sup norm `‖z‖`. -/
theorem discBundleFibreCoord_apply (z : Fin (Module.finrank ℝ F) → ℝ) :
    discBundleFibreCoord F z =
      (‖z‖ / ‖(WithLp.toLp 2 z : EuclideanSpace ℝ (Fin (Module.finrank ℝ F)))‖) •
        WithLp.toLp 2 z := by
  let L : (Fin (Module.finrank ℝ F) → ℝ) ≃L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ F)) :=
    (EuclideanSpace.equiv (Fin (Module.finrank ℝ F)) ℝ).symm
  have hgauge : gauge (L '' closedBall 0 1) (L z) = ‖z‖ := by
    rw [← div_one ‖z‖, ← gauge_closedBall zero_le_one z, gauge_def', gauge_def']
    congr 2
    ext r
    exact and_congr_right fun _ ↦ by rw [← map_smul, L.injective.mem_set_image]
  rw [discBundleFibreCoord, ContinuousLinearEquiv.unitBallHomeomorph_apply, gaugeRescale_def,
    hgauge, gauge_closedBall zero_le_one, div_one]
  rfl

/-- `TauCeti.discBundleFibreCoord` sends zero to zero. -/
@[simp]
theorem discBundleFibreCoord_zero : discBundleFibreCoord F 0 = 0 := by
  simp [discBundleFibreCoord_apply]

/-- Inverse evaluation formula for `TauCeti.discBundleFibreCoord`: it rescales `w.ofLp` so that its
sup norm equals the Euclidean norm `‖w‖`. -/
theorem discBundleFibreCoord_symm_apply (w : EuclideanSpace ℝ (Fin (Module.finrank ℝ F))) :
    (discBundleFibreCoord F).symm w = (‖w‖ / ‖w.ofLp‖) • w.ofLp := by
  rw [(discBundleFibreCoord F).symm_apply_eq, discBundleFibreCoord_apply]
  by_cases hw : w = 0
  · simp [hw]
  · have hwn : ‖w‖ ≠ 0 := norm_ne_zero_iff.2 hw
    have hofn : ‖w.ofLp‖ ≠ 0 := norm_ne_zero_iff.2 (fun h ↦ hw (by ext i; exact congrFun h i))
    have hc : 0 < ‖w‖ / ‖w.ofLp‖ := div_pos (norm_pos_iff.2 hw) (norm_pos_iff.2
      (fun h ↦ hw (by ext i; exact congrFun h i)))
    have hsmul :
        (WithLp.toLp 2 ((‖w‖ / ‖w.ofLp‖) • w.ofLp) :
            EuclideanSpace ℝ (Fin (Module.finrank ℝ F))) =
          (‖w‖ / ‖w.ofLp‖) • w := by
      ext i
      simp
    rw [hsmul, norm_smul, norm_smul, Real.norm_of_nonneg hc.le, smul_smul]
    have hcoeff :
        ((‖w‖ / ‖w.ofLp‖) * ‖w.ofLp‖ / ((‖w‖ / ‖w.ofLp‖) * ‖w‖)) * (‖w‖ / ‖w.ofLp‖) = 1 := by
      field_simp [hwn, hofn]
    simp [hcoeff]

/-- The inverse of `TauCeti.discBundleFibreCoord` sends zero to zero. -/
@[simp]
theorem discBundleFibreCoord_symm_zero : (discBundleFibreCoord F).symm 0 = 0 := by
  simp [discBundleFibreCoord_symm_apply]

/-- `TauCeti.discBundleFibreCoord` carries the closed unit ball of the sup norm onto the closed
Euclidean unit ball. -/
@[simp]
theorem image_discBundleFibreCoord_closedBall :
    discBundleFibreCoord F '' closedBall 0 1 = closedBall 0 1 :=
  ContinuousLinearEquiv.image_unitBallHomeomorph_closedBall _

/-- `TauCeti.discBundleFibreCoord` carries the open unit ball of the sup norm onto the open
Euclidean unit ball. -/
@[simp]
theorem image_discBundleFibreCoord_ball :
    discBundleFibreCoord F '' ball 0 1 = ball 0 1 :=
  ContinuousLinearEquiv.image_unitBallHomeomorph_ball _

/-- `TauCeti.discBundleFibreCoord` carries the unit sphere of the sup norm onto the Euclidean unit
sphere. -/
@[simp]
theorem image_discBundleFibreCoord_sphere :
    discBundleFibreCoord F '' sphere 0 1 = sphere 0 1 :=
  ContinuousLinearEquiv.image_unitBallHomeomorph_sphere _

/-- Preimage of the closed Euclidean unit ball under `TauCeti.discBundleFibreCoord`. -/
@[simp]
theorem preimage_discBundleFibreCoord_closedBall :
    discBundleFibreCoord F ⁻¹' closedBall 0 1 = closedBall 0 1 := by
  rw [← image_discBundleFibreCoord_closedBall, Homeomorph.preimage_image]

/-- Preimage of the open Euclidean unit ball under `TauCeti.discBundleFibreCoord`. -/
@[simp]
theorem preimage_discBundleFibreCoord_ball :
    discBundleFibreCoord F ⁻¹' ball 0 1 = ball 0 1 := by
  rw [← image_discBundleFibreCoord_ball, Homeomorph.preimage_image]

/-- Preimage of the Euclidean unit sphere under `TauCeti.discBundleFibreCoord`. -/
@[simp]
theorem preimage_discBundleFibreCoord_sphere :
    discBundleFibreCoord F ⁻¹' sphere 0 1 = sphere 0 1 := by
  rw [← image_discBundleFibreCoord_sphere, Homeomorph.preimage_image]

/-- `TauCeti.discBundleFibreCoord` preserves the closed unit ball (`‖z‖ ≤ 1`). -/
@[simp]
theorem norm_discBundleFibreCoord_le_one_iff {z : Fin (Module.finrank ℝ F) → ℝ} :
    ‖discBundleFibreCoord F z‖ ≤ 1 ↔ ‖z‖ ≤ 1 :=
  ContinuousLinearEquiv.norm_unitBallHomeomorph_le_one_iff _

/-- `TauCeti.discBundleFibreCoord` preserves the open unit ball (`‖z‖ < 1`). -/
@[simp]
theorem norm_discBundleFibreCoord_lt_one_iff {z : Fin (Module.finrank ℝ F) → ℝ} :
    ‖discBundleFibreCoord F z‖ < 1 ↔ ‖z‖ < 1 :=
  ContinuousLinearEquiv.norm_unitBallHomeomorph_lt_one_iff _

/-- `TauCeti.discBundleFibreCoord` preserves the unit sphere (`‖z‖ = 1`). -/
@[simp]
theorem norm_discBundleFibreCoord_eq_one_iff {z : Fin (Module.finrank ℝ F) → ℝ} :
    ‖discBundleFibreCoord F z‖ = 1 ↔ ‖z‖ = 1 :=
  ContinuousLinearEquiv.norm_unitBallHomeomorph_eq_one_iff _

/-- The inverse of `TauCeti.discBundleFibreCoord` preserves the closed unit ball (`‖w‖ ≤ 1`). -/
@[simp]
theorem norm_discBundleFibreCoord_symm_le_one_iff
    {w : EuclideanSpace ℝ (Fin (Module.finrank ℝ F))} :
    ‖(discBundleFibreCoord F).symm w‖ ≤ 1 ↔ ‖w‖ ≤ 1 :=
  ContinuousLinearEquiv.norm_unitBallHomeomorph_symm_le_one_iff _

/-- The inverse of `TauCeti.discBundleFibreCoord` preserves the open unit ball (`‖w‖ < 1`). -/
@[simp]
theorem norm_discBundleFibreCoord_symm_lt_one_iff
    {w : EuclideanSpace ℝ (Fin (Module.finrank ℝ F))} :
    ‖(discBundleFibreCoord F).symm w‖ < 1 ↔ ‖w‖ < 1 :=
  ContinuousLinearEquiv.norm_unitBallHomeomorph_symm_lt_one_iff _

/-- The inverse of `TauCeti.discBundleFibreCoord` preserves the unit sphere (`‖w‖ = 1`). -/
@[simp]
theorem norm_discBundleFibreCoord_symm_eq_one_iff
    {w : EuclideanSpace ℝ (Fin (Module.finrank ℝ F))} :
    ‖(discBundleFibreCoord F).symm w‖ = 1 ↔ ‖w‖ = 1 :=
  ContinuousLinearEquiv.norm_unitBallHomeomorph_symm_eq_one_iff _

/-- The splitting of the coordinates of an `n`-cell of the disc bundle into the coordinates of the
cell of `C` and the fibre coordinates. -/
private abbrev cellSplit {n : ℕ} (c : DiscCell F C n) :
    (Fin n → ℝ) ≃ᵢ (Fin c.1.val → ℝ) × (Fin (Module.finrank ℝ F) → ℝ) :=
  (Fin.appendIsometryOfEq c.1.property).symm

variable [FiniteDimensional ℝ F]

variable (F E) in
/-- A continuous orthonormal frame of `E` along the retracted characteristic map
`cellRetractMap m j` of a base `m`-cell `j`. -/
def discBundleCellFrame {m : ℕ} (j : cell C m) :
    C(Fin m → ℝ, OrthonormalFrameBundle ℝ F E (EuclideanSpace ℝ (Fin (Module.finrank ℝ F)))) :=
  (exists_orthonormalFrameBundle_lift_of_contractibleSpace F E finrank_euclideanSpace_fin
    (cellRetractMap m j)).choose

/-- The chosen orthonormal frame `TauCeti.discBundleCellFrame` over `y` sits in the fibre over
`cellRetractMap m j y`. -/
theorem proj_discBundleCellFrame {m : ℕ} (j : cell C m) (y : Fin m → ℝ) :
    (discBundleCellFrame F E j y).proj = cellRetractMap m j y :=
  (exists_orthonormalFrameBundle_lift_of_contractibleSpace F E finrank_euclideanSpace_fin
    (cellRetractMap m j)).choose_spec y

/-- The characteristic map of the cell of the disc bundle over the cell `c.2` of `C`: the base
coordinates are read through the characteristic map of `c.2`, and the fibre coordinates through
the frame `discBundleCellFrame` over the base point. -/
private def discCellFun {n : ℕ} (c : DiscCell F C n) (x : Fin n → ℝ) : TotalSpace F E :=
  ⟨(discBundleCellFrame F E c.2 (cellSplit c x).1).proj,
    (discBundleCellFrame F E c.2 (cellSplit c x).1).frame
      (discBundleFibreCoord F (cellSplit c x).2)⟩

private theorem continuous_discCellFun {n : ℕ} (c : DiscCell F C n) :
    Continuous (discCellFun (E := E) c) :=
  OrthonormalFrameBundle.continuous_totalSpaceMk_frame_apply.comp
    (((discBundleCellFrame F E c.2).continuous.comp
        (continuous_fst.comp (cellSplit c).continuous)).prodMk
      ((discBundleFibreCoord F).continuous.comp (continuous_snd.comp (cellSplit c).continuous)))

private theorem proj_discCellFun {n : ℕ} (c : DiscCell F C n) {x : Fin n → ℝ}
    (hx : x ∈ closedBall 0 1) :
    (discCellFun (E := E) c x).proj = map c.1.val c.2 (cellSplit c x).1 :=
  (proj_discBundleCellFrame c.2 _).trans
    (cellRetractMap_of_mem c.1.val c.2
      ((Fin.mem_closedBall_iff_appendIsometryOfEq_symm c.1.property).1 hx).1)

private theorem norm_discCellFun {n : ℕ} (c : DiscCell F C n) (x : Fin n → ℝ) :
    ‖(discCellFun (E := E) c x).snd‖ = ‖discBundleFibreCoord F (cellSplit c x).2‖ :=
  (discBundleCellFrame F E c.2 (cellSplit c x).1).frame.norm_map _

/-- A vector over the image of a point `y` of the closed unit ball under the characteristic map of
`c.2` is the value of `discCellFun c` at a point with base coordinates `y`. -/
private theorem exists_discCellFun_eq {n : ℕ} (c : DiscCell F C n) {y : Fin c.1.val → ℝ}
    (hy : y ∈ closedBall 0 1) {v : TotalSpace F E} (hv : v.proj = map c.1.val c.2 y) :
    ∃ z, ‖discBundleFibreCoord F z‖ = ‖v.snd‖ ∧ discCellFun c ((cellSplit c).symm (y, z)) = v := by
  have hp : v.proj = (discBundleCellFrame F E c.2 y).proj := by
    rw [proj_discBundleCellFrame, cellRetractMap_of_mem c.1.val c.2 hy, hv]
  -- Read `v` in the frame over `y`.
  obtain ⟨w, hw, hwv⟩ : ∃ w, ‖w‖ = ‖v.snd‖ ∧
      (⟨(discBundleCellFrame F E c.2 y).proj,
        (discBundleCellFrame F E c.2 y).frame w⟩ : TotalSpace F E) = v := by
    generalize discBundleCellFrame F E c.2 y = p at hp
    obtain ⟨b', φ⟩ := p
    obtain ⟨b, u⟩ := v
    obtain rfl : b = b' := hp
    exact ⟨φ.symm u, by simp, by simp⟩
  refine ⟨(discBundleFibreCoord F).symm w, by rwa [Homeomorph.apply_symm_apply], ?_⟩
  have hsplit : cellSplit c ((cellSplit c).symm (y, (discBundleFibreCoord F).symm w)) =
      (y, (discBundleFibreCoord F).symm w) :=
    (cellSplit c).apply_symm_apply _
  unfold discCellFun
  rw [hsplit, Homeomorph.apply_symm_apply]
  exact hwv

private theorem image_closedBall_discCellFun {n : ℕ} (c : DiscCell F C n) :
    discCellFun (E := E) c '' closedBall 0 1 =
      discBundle F E ∩ TotalSpace.proj ⁻¹' closedCell c.1.val c.2 := by
  ext v
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨h₁, h₂⟩ := (Fin.mem_closedBall_iff_appendIsometryOfEq_symm c.1.property).1 hx
    refine ⟨?_, ?_⟩
    · rw [mem_discBundle, norm_discCellFun, norm_discBundleFibreCoord_le_one_iff]
      exact mem_closedBall_zero_iff.1 h₂
    · rw [mem_preimage, proj_discCellFun c hx]
      exact mem_image_of_mem _ h₁
  · rintro ⟨hv, y, hy, hyv⟩
    obtain ⟨z, hz, hzv⟩ := exists_discCellFun_eq c hy hyv.symm
    refine ⟨(cellSplit c).symm (y, z),
      (Fin.mem_closedBall_iff_appendIsometryOfEq_symm c.1.property).2 ?_, hzv⟩
    rw [IsometryEquiv.apply_symm_apply]
    exact ⟨hy, mem_closedBall_zero_iff.2
      (norm_discBundleFibreCoord_le_one_iff.1 (hz ▸ mem_discBundle.1 hv))⟩

private theorem image_ball_discCellFun {n : ℕ} (c : DiscCell F C n) :
    discCellFun (E := E) c '' ball 0 1 =
      {v : TotalSpace F E | ‖v.snd‖ < 1} ∩ TotalSpace.proj ⁻¹' openCell c.1.val c.2 := by
  ext v
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨h₁, h₂⟩ := (Fin.mem_ball_iff_appendIsometryOfEq_symm c.1.property).1 hx
    refine ⟨(norm_discCellFun c x).trans_lt
      (norm_discBundleFibreCoord_lt_one_iff.2 (mem_ball_zero_iff.1 h₂)), ?_⟩
    rw [mem_preimage, proj_discCellFun c (ball_subset_closedBall hx)]
    exact mem_image_of_mem _ h₁
  · rintro ⟨hv, y, hy, hyv⟩
    obtain ⟨z, hz, hzv⟩ := exists_discCellFun_eq c (ball_subset_closedBall hy) hyv.symm
    refine ⟨(cellSplit c).symm (y, z), (Fin.mem_ball_iff_appendIsometryOfEq_symm c.1.property).2 ?_,
        hzv⟩
    rw [IsometryEquiv.apply_symm_apply]
    exact ⟨hy, mem_ball_zero_iff.2 (norm_discBundleFibreCoord_lt_one_iff.1 (hz ▸ hv))⟩

private theorem image_sphere_discCellFun {n : ℕ} (c : DiscCell F C n) :
    discCellFun (E := E) c '' sphere 0 1 =
      sphereBundle F E ∩ TotalSpace.proj ⁻¹' closedCell c.1.val c.2 ∪
        discBundle F E ∩ TotalSpace.proj ⁻¹' cellFrontier c.1.val c.2 := by
  ext v
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hx' := sphere_subset_closedBall hx
    have hv : discCellFun c x ∈ discBundle F E ∩ TotalSpace.proj ⁻¹' closedCell c.1.val c.2 := by
      rw [← image_closedBall_discCellFun (E := E) c]
      exact mem_image_of_mem _ hx'
    rcases (Fin.mem_sphere_iff_appendIsometryOfEq_symm c.1.property).1 hx with ⟨h₁, -⟩ | ⟨-, h₂⟩
    · refine Or.inr ⟨hv.1, ?_⟩
      rw [mem_preimage, proj_discCellFun c hx']
      exact mem_image_of_mem _ h₁
    · refine Or.inl ⟨?_, hv.2⟩
      rw [mem_sphereBundle, norm_discCellFun, norm_discBundleFibreCoord_eq_one_iff]
      exact mem_sphere_zero_iff_norm.1 h₂
  · rintro (⟨hv, y, hy, hyv⟩ | ⟨hv, y, hy, hyv⟩)
    · obtain ⟨z, hz, hzv⟩ := exists_discCellFun_eq c hy hyv.symm
      refine ⟨(cellSplit c).symm (y, z),
        (Fin.mem_sphere_iff_appendIsometryOfEq_symm c.1.property).2 (Or.inr ?_), hzv⟩
      rw [IsometryEquiv.apply_symm_apply]
      exact ⟨hy, mem_sphere_zero_iff_norm.2
        (norm_discBundleFibreCoord_eq_one_iff.1 (hz ▸ mem_sphereBundle.1 hv))⟩
    · obtain ⟨z, hz, hzv⟩ := exists_discCellFun_eq c (sphere_subset_closedBall hy) hyv.symm
      refine ⟨(cellSplit c).symm (y, z),
        (Fin.mem_sphere_iff_appendIsometryOfEq_symm c.1.property).2 (Or.inl ?_), hzv⟩
      rw [IsometryEquiv.apply_symm_apply]
      exact ⟨hy, mem_closedBall_zero_iff.2
        (norm_discBundleFibreCoord_le_one_iff.1 (hz ▸ mem_discBundle.1 hv))⟩

/-- The characteristic map of a cell of the disc bundle is injective on the open unit ball: the
base coordinates are determined by the base point, since the characteristic map of `c.2` is
injective there, and then the fibre coordinates by the frame over it. -/
private theorem injOn_discCellFun {n : ℕ} (c : DiscCell F C n) :
    InjOn (discCellFun (E := E) c) (ball 0 1) := by
  intro x hx x' hx' h
  have h₁ : (cellSplit c x).1 = (cellSplit c x').1 := by
    have hproj := congrArg TotalSpace.proj h
    rw [proj_discCellFun c (ball_subset_closedBall hx),
      proj_discCellFun c (ball_subset_closedBall hx')] at hproj
    exact (map c.1.val c.2).injOn
      (by rw [source_eq]; exact ((Fin.mem_ball_iff_appendIsometryOfEq_symm c.1.property).1 hx).1)
      (by rw [source_eq]; exact ((Fin.mem_ball_iff_appendIsometryOfEq_symm c.1.property).1 hx').1)
          hproj
  have h₂ : (cellSplit c x).2 = (cellSplit c x').2 := by
    unfold discCellFun at h
    rw [h₁] at h
    exact (discBundleFibreCoord F).injective
      ((discBundleCellFrame F E c.2 _).frame.injective (TotalSpace.mk_inj.1 h))
  exact (cellSplit c).injective (Prod.ext h₁ h₂)

/-- The characteristic map of a cell of the disc bundle, as a partial equivalence with source the
open unit ball. -/
private def discCellMap {n : ℕ} (c : DiscCell F C n) : PartialEquiv (Fin n → ℝ) (TotalSpace F E) :=
  (injOn_discCellFun c).toPartialEquiv _ _

private theorem coe_discCellMap {n : ℕ} (c : DiscCell F C n) :
    ⇑(discCellMap (E := E) c) = discCellFun c := by
  rw [discCellMap, InjOn.toPartialEquiv, BijOn.toPartialEquiv_apply]

/-- Distinct cells of the disc bundle have disjoint open cells, since they lie over distinct open
cells of `C`. -/
private theorem pairwiseDisjoint_discCellMap :
    (univ : Set (Σ n, DiscCell F C n)).PairwiseDisjoint
      (fun c ↦ discCellMap (E := E) c.2 '' ball 0 1) := by
  rintro ⟨n, ⟨m, hm⟩, j⟩ - ⟨n', ⟨m', hm'⟩, j'⟩ - hne
  simp only [Function.onFun, coe_discCellMap, image_ball_discCellFun]
  refine Disjoint.mono inter_subset_right inter_subset_right
    ((disjoint_openCell_of_ne fun h ↦ hne ?_).preimage _)
  obtain ⟨rfl, hj⟩ := Sigma.mk.inj_iff.1 h
  obtain rfl := eq_of_heq hj
  subst hm hm'
  rfl

/-- An open cell of the disc bundle misses the base: its vectors have norm less than one, and it
lies over an open cell of `C`, which misses `D`. -/
private theorem disjoint_discCellMap_base {n : ℕ} (c : DiscCell F C n) :
    Disjoint (discCellMap (E := E) c '' ball 0 1)
      (sphereBundle F E ∩ TotalSpace.proj ⁻¹' C ∪ discBundle F E ∩ TotalSpace.proj ⁻¹' D) := by
  rw [coe_discCellMap, image_ball_discCellFun]
  refine disjoint_union_right.2 ⟨Disjoint.mono inter_subset_left inter_subset_left ?_,
    Disjoint.mono inter_subset_right inter_subset_right ((disjointBase _ _).preimage _)⟩
  exact disjoint_norm_lt_one_sphereBundle

/-- The boundary of a cell of the disc bundle lies in the base together with finitely many cells
of smaller dimension: its part over the boundary of the cell of `C` lies over `D` or over finitely
many closed cells of `C` of smaller dimension, and the rest lies in the sphere bundle. -/
private theorem mapsTo_discCellMap {n : ℕ} (c : DiscCell F C n) :
    ∃ I : Π k, Finset (DiscCell F C k), MapsTo (discCellMap (E := E) c) (sphere 0 1)
      (sphereBundle F E ∩ TotalSpace.proj ⁻¹' C ∪ discBundle F E ∩ TotalSpace.proj ⁻¹' D ∪
        ⋃ (k < n) (c' ∈ I k), discCellMap c' '' closedBall 0 1) := by
  obtain ⟨I, hI⟩ := cellFrontier_subset_base_union_finite_closedCell c.1.val c.2
  refine ⟨fun k ↦ ((Finset.range (k + 1)).subtype (· + Module.finrank ℝ F = k)).sigma
    fun m ↦ I m.val, ?_⟩
  rw [mapsTo_iff_image_subset, coe_discCellMap, image_sphere_discCellFun]
  rintro v (⟨hv, hvC⟩ | ⟨hv, hvC⟩)
  · exact Or.inl (Or.inl ⟨hv, closedCell_subset_complex (C := C) c.1.val c.2 hvC⟩)
  rcases hI hvC with hvD | hvC
  · exact Or.inl (Or.inr ⟨hv, hvD⟩)
  obtain ⟨m, hm, j, hj, hvj⟩ : ∃ m < c.1.val, ∃ j ∈ I m, v.proj ∈ closedCell m j := by
    simpa using hvC
  have hn := c.1.property
  refine Or.inr (mem_iUnion₂.2 ⟨m + Module.finrank ℝ F, by omega, mem_iUnion₂.2
    ⟨⟨⟨m, rfl⟩, j⟩, Finset.mem_sigma.2 ⟨Finset.mem_subtype.2
      (Finset.mem_range.2 (Nat.lt_succ_of_le (Nat.le_add_right _ _))), hj⟩, ?_⟩⟩)
  rw [coe_discCellMap, image_closedBall_discCellFun]
  exact ⟨hv, hvj⟩

/-- The base and the closed cells of the disc bundle cover the disc bundle over `C`. -/
private theorem union_discCellMap :
    sphereBundle F E ∩ TotalSpace.proj ⁻¹' C ∪ discBundle F E ∩ TotalSpace.proj ⁻¹' D ∪
        ⋃ (n : ℕ) (c : DiscCell F C n), discCellMap (E := E) c '' closedBall 0 1 =
      discBundle F E ∩ TotalSpace.proj ⁻¹' C := by
  simp only [coe_discCellMap, image_closedBall_discCellFun]
  refine subset_antisymm (union_subset (union_subset ?_ ?_) (iUnion₂_subset fun n c ↦ ?_)) ?_
  · exact fun v hv ↦ ⟨mem_discBundle.2 (mem_sphereBundle.1 hv.1).le, hv.2⟩
  · exact inter_subset_inter_right _ (preimage_mono base_subset_complex)
  · exact inter_subset_inter_right _ (preimage_mono (closedCell_subset_complex _ _))
  · rintro v ⟨hv, hvC⟩
    rw [mem_preimage, ← RelCWComplex.union (C := C), mem_union, mem_iUnion₂] at hvC
    rcases hvC with hvD | ⟨m, j, hvj⟩
    · exact Or.inl (Or.inr ⟨hv, hvD⟩)
    · exact Or.inr (mem_iUnion₂.2 ⟨m + Module.finrank ℝ F, ⟨⟨m, rfl⟩, j⟩, hv, hvj⟩)

end Cells

section Structure

variable [FiniteDimensional ℝ F] [T2Space B]

/-- The boundary image of `discCellFun c` is disjoint from its open cell image. -/
private theorem disjoint_image_sphere_ball_discCellFun {n : ℕ} (c : DiscCell F C n) :
    Disjoint (discCellFun (E := E) c '' sphere 0 1) (discCellFun (E := E) c '' ball 0 1) := by
  rw [image_sphere_discCellFun, image_ball_discCellFun]
  refine disjoint_union_left.2 ⟨Disjoint.mono inter_subset_left inter_subset_left ?_,
    Disjoint.mono inter_subset_right inter_subset_right
      (((disjoint_skeletonLT_openCell le_rfl).mono_left
        (cellFrontier_subset_skeletonLT c.1.val c.2)).preimage _)⟩
  exact disjoint_norm_lt_one_sphereBundle.symm

/-- The inverse of the characteristic map of a cell is continuous on the open cell: the closed unit
ball is compact, and its boundary sphere is mapped outside the open cell. -/
private theorem continuousOn_symm_discCellMap {n : ℕ} (c : DiscCell F C n) :
    ContinuousOn (discCellMap (E := E) c).symm (discCellMap c).target := by
  refine (continuous_discCellFun c).continuousOn.continuousOn_invFunOn_image_of_isCompact
    (isCompact_closedBall 0 1) ball_subset_closedBall (injOn_discCellFun c) ?_
  rw [closedBall_sdiff_ball]
  exact disjoint_image_sphere_ball_discCellFun c

/-- **The disc bundle over `C` has the weak topology.** A set `A` in the disc bundle over `C`
which meets the part of the disc bundle over every closed cell of `C` and over `D` in a closed set
is closed. -/
private theorem isClosed_of_isClosed_inter_proj_preimage {A : Set (TotalSpace F E)}
    (hA : A ⊆ discBundle F E ∩ TotalSpace.proj ⁻¹' C)
    (hcell : ∀ m (j : cell C m), IsClosed (A ∩ TotalSpace.proj ⁻¹' closedCell m j))
    (hD : IsClosed (A ∩ TotalSpace.proj ⁻¹' D)) : IsClosed A := by
  have hproj := FiberBundle.continuous_proj F E
  rw [← closure_subset_iff_isClosed]
  intro v hv
  by_contra hvA
  -- The point `v` lies over the base or over a closed cell of `C`, over which `A` is closed.
  have hvC : v.proj ∈ C := (closure_minimal hA
    ((isClosed_discBundle F E).inter (RelCWComplex.isClosed.preimage hproj)) hv).2
  obtain ⟨K, hK, hvK⟩ : ∃ K : Set B, IsClosed (A ∩ TotalSpace.proj ⁻¹' K) ∧ v.proj ∈ K := by
    rw [← RelCWComplex.union (C := C), mem_union, mem_iUnion₂] at hvC
    rcases hvC with hvD | ⟨m, j, hvj⟩
    exacts [⟨D, hD, hvD⟩, ⟨_, hcell m j, hvj⟩]
  -- So the points of `A` over `v.proj` form a compact set; separate it from `v`.
  have hS : IsCompact (A ∩ TotalSpace.proj ⁻¹' {v.proj}) := by
    refine (isCompact_discBundle_inter_proj_preimage_singleton ℝ F E v.proj).of_isClosed_subset ?_
      fun a ha ↦ ⟨(hA ha.1).1, ha.2⟩
    have hset : A ∩ TotalSpace.proj ⁻¹' K ∩ TotalSpace.proj ⁻¹' {v.proj} =
        A ∩ TotalSpace.proj ⁻¹' {v.proj} := by
      rw [inter_assoc, ← preimage_inter, inter_eq_right.2 (singleton_subset_iff.2 hvK)]
    exact hset ▸ hK.inter (isClosed_singleton.preimage hproj)
  obtain ⟨U, W, hU, hW, hvU, hSW, hUW⟩ := SeparatedNhds.of_isCompact_isCompact isCompact_singleton
    hS (disjoint_singleton_left.2 fun h ↦ hvA h.1)
  -- The projection of the part of `A` outside `W` is closed and misses `v.proj`.
  have hT : IsClosed (TotalSpace.proj '' (A \ W)) := by
    have hpiece {K : Set B} (hK : IsClosed (A ∩ TotalSpace.proj ⁻¹' K)) :
        IsClosed (TotalSpace.proj '' (A \ W) ∩ K) := by
      rw [← image_inter_preimage, ← inter_sdiff_right_comm]
      exact isClosed_image_proj_of_subset_discBundle ℝ (hK.sdiff hW) fun a ha ↦ (hA ha.1.1).1
    refine (RelCWComplex.closed C _ ?_).2 ⟨fun m j ↦ hpiece (hcell m j), hpiece hD⟩
    rintro _ ⟨a, ha, rfl⟩
    exact (hA ha.1).2
  have hvT : v.proj ∉ TotalSpace.proj '' (A \ W) := by
    rintro ⟨a, ⟨haA, haW⟩, hav⟩
    exact haW (hSW ⟨haA, hav⟩)
  -- A neighbourhood of `v` misses `A`.
  obtain ⟨a, ⟨haU, haT⟩, haA⟩ := mem_closure_iff.1 hv _
    (hU.inter (hT.isOpen_compl.preimage hproj)) ⟨hvU rfl, hvT⟩
  by_cases haW : a ∈ W
  · exact Set.disjoint_left.1 hUW haU haW
  · exact haT ⟨a, ⟨haA, haW⟩, rfl⟩

variable (F E C) in
/-- **The disc bundle over a CW complex.** Let `E` be a real vector bundle of rank `r` over a
Hausdorff space, with finite-dimensional model fibre and fibre inner products whose norm is
continuous on the total space, and let `C` be a CW complex relative to `D`. Then the part
`D(E)|_C` of the unit disc bundle over `C` is a CW complex relative to `S(E)|_C ∪ D(E)|_D`. Its
`n`-cells are the `m`-cells of `C` with `m + r = n` (`TauCeti.cellDiscBundleEquiv`), the closed
cell over a closed cell `e` of `C` being `D(E)|_e`. -/
@[instance_reducible]
def relCWComplexDiscBundle :
    RelCWComplex (discBundle F E ∩ TotalSpace.proj ⁻¹' C)
      (sphereBundle F E ∩ TotalSpace.proj ⁻¹' C ∪ discBundle F E ∩ TotalSpace.proj ⁻¹' D) where
  cell := DiscCell F C
  map _ c := discCellMap c
  source_eq _ _ := rfl
  continuousOn _ c := by
    rw [coe_discCellMap]
    exact (continuous_discCellFun c).continuousOn
  continuousOn_symm _ c := continuousOn_symm_discCellMap c
  pairwiseDisjoint' := pairwiseDisjoint_discCellMap
  disjointBase' _ c := disjoint_discCellMap_base c
  mapsTo _ c := mapsTo_discCellMap c
  closed' A hA h := by
    refine isClosed_of_isClosed_inter_proj_preimage hA (fun m j ↦ ?_) ?_
    · have hcell := h.1 (m + Module.finrank ℝ F) ⟨⟨m, rfl⟩, j⟩
      rwa [coe_discCellMap, image_closedBall_discCellFun, ← inter_assoc,
        inter_eq_left.2 fun a ha ↦ (hA ha).1] at hcell
    · convert h.2.inter ((isClosedBase C).preimage (FiberBundle.continuous_proj F E)) using 1
      ext a
      simp only [mem_inter_iff, mem_union, mem_preimage]
      exact ⟨fun ⟨haA, haD⟩ ↦ ⟨⟨haA, Or.inr ⟨(hA haA).1, haD⟩⟩, haD⟩,
        fun ⟨⟨haA, _⟩, haD⟩ ↦ ⟨haA, haD⟩⟩
  isClosedBase := by
    have hproj := FiberBundle.continuous_proj F E
    exact ((isClosed_sphereBundle F E).inter (RelCWComplex.isClosed.preimage hproj)).union
      ((isClosed_discBundle F E).inter ((isClosedBase C).preimage hproj))
  union' := union_discCellMap

variable (F E C) in
/-- The `n`-cells of the disc bundle over `C` are the `m`-cells of `C` with `m + r = n`, where `r`
is the rank of the bundle. -/
def cellDiscBundleEquiv (n : ℕ) :
    letI := relCWComplexDiscBundle F E C
    cell (discBundle F E ∩ TotalSpace.proj ⁻¹' C) n ≃
      Σ m : {m : ℕ // m + Module.finrank ℝ F = n}, cell C m :=
  Equiv.refl _

/-- The disc bundle has no cells of dimension below the rank of the bundle. -/
theorem isEmpty_cell_relCWComplexDiscBundle_of_lt {n : ℕ} (hn : n < Module.finrank ℝ F) :
    letI := relCWComplexDiscBundle F E C
    IsEmpty (cell (discBundle F E ∩ TotalSpace.proj ⁻¹' C) n) := by
  let := relCWComplexDiscBundle F E C
  exact ⟨fun c ↦ by have := ((cellDiscBundleEquiv F E C n) c).1.property; omega⟩

variable {n : ℕ} (c : Σ m : {m : ℕ // m + Module.finrank ℝ F = n}, cell C m)

/-- The characteristic map of the cell of the disc bundle over a cell of `C` is `discCellFun`. This
unfolds the `map` field of `relCWComplexDiscBundle` and `cellDiscBundleEquiv`, which is
`Equiv.refl`. -/
private theorem coe_map_relCWComplexDiscBundle :
    letI := relCWComplexDiscBundle F E C
    ⇑(map n ((cellDiscBundleEquiv F E C n).symm c)) = discCellFun c :=
  coe_discCellMap c

/-- Explicit evaluation of the characteristic map of a cell of `relCWComplexDiscBundle` in terms of
the chosen orthonormal frame `TauCeti.discBundleCellFrame` and radial fibre coordinate
`TauCeti.discBundleFibreCoord`. -/
theorem map_relCWComplexDiscBundle_apply (x : Fin n → ℝ) :
    letI := relCWComplexDiscBundle F E C
    map n ((cellDiscBundleEquiv F E C n).symm c) x =
      ⟨(discBundleCellFrame F E c.2 ((Fin.appendIsometryOfEq c.1.property).symm x).1).proj,
        (discBundleCellFrame F E c.2 ((Fin.appendIsometryOfEq c.1.property).symm x).1).frame
          (discBundleFibreCoord F ((Fin.appendIsometryOfEq c.1.property).symm x).2)⟩ := by
  rw [coe_map_relCWComplexDiscBundle]
  rfl

/-- The characteristic maps of the disc bundle cover those of `C`: on the closed unit ball, the
characteristic map of the cell over an `m`-cell `j` of `C` lies over the characteristic map of `j`
applied to the first `m` coordinates. -/
theorem proj_map_relCWComplexDiscBundle {x : Fin n → ℝ} (hx : x ∈ closedBall 0 1) :
    letI := relCWComplexDiscBundle F E C
    (map n ((cellDiscBundleEquiv F E C n).symm c) x).proj =
      map c.1.val c.2 ((Fin.appendIsometryOfEq c.1.property).symm x).1 := by
  rw [coe_map_relCWComplexDiscBundle]
  exact proj_discCellFun c hx

/-- The closed cell of the disc bundle over an `m`-cell `j` of `C` is the part of the disc bundle
over the closed cell of `j`. -/
@[simp]
theorem closedCell_relCWComplexDiscBundle :
    letI := relCWComplexDiscBundle F E C
    closedCell n ((cellDiscBundleEquiv F E C n).symm c) =
      discBundle F E ∩ TotalSpace.proj ⁻¹' closedCell c.1.val c.2 := by
  let := relCWComplexDiscBundle F E C
  rw [closedCell, coe_map_relCWComplexDiscBundle]
  exact image_closedBall_discCellFun c

/-- The open cell of the disc bundle over an `m`-cell `j` of `C` consists of the vectors of norm
less than one over the open cell of `j`. -/
@[simp]
theorem openCell_relCWComplexDiscBundle :
    letI := relCWComplexDiscBundle F E C
    openCell n ((cellDiscBundleEquiv F E C n).symm c) =
      {v : TotalSpace F E | ‖v.snd‖ < 1} ∩ TotalSpace.proj ⁻¹' openCell c.1.val c.2 := by
  let := relCWComplexDiscBundle F E C
  rw [openCell, coe_map_relCWComplexDiscBundle]
  exact image_ball_discCellFun c

/-- The boundary of the cell of the disc bundle over an `m`-cell `j` of `C` is the part of the
sphere bundle over the closed cell of `j` together with the part of the disc bundle over the
boundary of `j`. -/
@[simp]
theorem cellFrontier_relCWComplexDiscBundle :
    letI := relCWComplexDiscBundle F E C
    cellFrontier n ((cellDiscBundleEquiv F E C n).symm c) =
      sphereBundle F E ∩ TotalSpace.proj ⁻¹' closedCell c.1.val c.2 ∪
        discBundle F E ∩ TotalSpace.proj ⁻¹' cellFrontier c.1.val c.2 := by
  let := relCWComplexDiscBundle F E C
  rw [cellFrontier, coe_map_relCWComplexDiscBundle]
  exact image_sphere_discCellFun c

variable (F E C) in
/-- **Weak topology of a unit disc bundle over a relative CW complex.** A subset `S` of the unit
disc bundle over `C` is closed in `D(E)` if and only if its intersections with the preimages of
every closed cell of `C` and of `D` are closed. -/
theorem closed_discBundleProj_preimage (S : Set (discBundle F E))
    (hS : S ⊆ discBundleProj F E ⁻¹' C) :
    IsClosed S ↔
      (∀ n (j : cell C n), IsClosed (S ∩ discBundleProj F E ⁻¹' closedCell n j)) ∧
      IsClosed (S ∩ discBundleProj F E ⁻¹' D) := by
  refine ⟨fun h ↦ ⟨fun n j ↦ h.inter (isClosed_closedCell.preimage (discBundleProj F E).continuous),
      h.inter ((isClosedBase C).preimage (discBundleProj F E).continuous)⟩, fun ⟨hcell, hD⟩ ↦ ?_⟩
  have hemb : IsClosedEmbedding (Subtype.val : discBundle F E → TotalSpace F E) :=
    IsClosedEmbedding.subtypeVal (isClosed_discBundle F E)
  have himg (K : Set B) : (Subtype.val '' S) ∩ TotalSpace.proj ⁻¹' K =
      Subtype.val '' (S ∩ discBundleProj F E ⁻¹' K) := by
    ext v
    simp only [mem_inter_iff, mem_image, mem_preimage, discBundleProj_apply]
    exact ⟨fun ⟨⟨w, hwS, hwv⟩, hvK⟩ ↦ ⟨w, ⟨hwS, hwv ▸ hvK⟩, hwv⟩,
      fun ⟨w, ⟨hwS, hwK⟩, hwv⟩ ↦ ⟨⟨w, hwS, hwv⟩, hwv ▸ hwK⟩⟩
  refine hemb.isClosed_iff_image_isClosed.2 (isClosed_of_isClosed_inter_proj_preimage (C := C)
    ?_ (fun m j ↦ ?_) ?_)
  · rintro _ ⟨v, hv, rfl⟩
    exact ⟨v.property, by simpa only [mem_preimage, discBundleProj_apply] using hS hv⟩
  · rw [himg]
    exact hemb.isClosedMap _ (hcell m j)
  · rw [himg]
    exact hemb.isClosedMap _ hD

/-- The disc bundle over a finite-dimensional CW complex is finite-dimensional. -/
theorem finiteDimensional_relCWComplexDiscBundle [RelCWComplex.FiniteDimensional C] :
    letI := relCWComplexDiscBundle F E C
    RelCWComplex.FiniteDimensional (discBundle F E ∩ TotalSpace.proj ⁻¹' C) := by
  let := relCWComplexDiscBundle F E C
  refine ⟨?_⟩
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1
    (FiniteDimensional.eventually_isEmpty_cell (C := C) (D := D))
  refine Filter.eventually_atTop.2 ⟨N + Module.finrank ℝ F, fun k hk ↦ ⟨fun c ↦ ?_⟩⟩
  obtain ⟨⟨m, hm⟩, j⟩ := (cellDiscBundleEquiv F E C k) c
  exact (hN m (by omega)).false j

/-- The disc bundle over a CW complex of finite type has finite type. -/
theorem finiteType_relCWComplexDiscBundle [RelCWComplex.FiniteType C] :
    letI := relCWComplexDiscBundle F E C
    RelCWComplex.FiniteType (discBundle F E ∩ TotalSpace.proj ⁻¹' C) :=
  let := relCWComplexDiscBundle F E C
  have (m : ℕ) : _root_.Finite (cell C m) := FiniteType.finite_cell m
  have (k : ℕ) : Subsingleton {m : ℕ // m + Module.finrank ℝ F = k} :=
    ⟨fun a b ↦ Subtype.ext (by have := a.property; have := b.property; omega)⟩
  ⟨fun k ↦ Finite.of_equiv _ (cellDiscBundleEquiv F E C k).symm⟩

/-- The disc bundle over a finite CW complex is a finite relative CW complex. -/
theorem finite_relCWComplexDiscBundle [RelCWComplex.Finite C] :
    letI := relCWComplexDiscBundle F E C
    RelCWComplex.Finite (discBundle F E ∩ TotalSpace.proj ⁻¹' C) :=
  letI := relCWComplexDiscBundle F E C
  have := finiteDimensional_relCWComplexDiscBundle (F := F) (E := E) (C := C)
  have := finiteType_relCWComplexDiscBundle (F := F) (E := E) (C := C)
  finite_of_finiteDimensional_finiteType _

end Structure

end TauCeti

namespace TauCeti

section Sets

variable {B : Type u} (F : Type*) (E : B → Type u) [∀ b, NormedAddCommGroup (E b)]

/-- The part of the disc bundle over all of `B` is the disc bundle. -/
private theorem discBundle_inter_preimage_univ :
    discBundle F E ∩ TotalSpace.proj ⁻¹' (univ : Set B) = discBundle F E := by
  simp

/-- The base of the relative CW structure of the disc bundle over all of `B` is the sphere
bundle. -/
private theorem sphereBundle_union_empty :
    sphereBundle F E ∩ TotalSpace.proj ⁻¹' (univ : Set B) ∪
      discBundle F E ∩ TotalSpace.proj ⁻¹' (∅ : Set B) = sphereBundle F E := by
  simp

/-- The base of the relative CW structure of the disc bundle over `(univ, A)` is
`S(E) ∪ D(E)|_A`. -/
private theorem sphereBundle_union_rel (A : Set B) :
    sphereBundle F E ∩ TotalSpace.proj ⁻¹' (univ : Set B) ∪
      discBundle F E ∩ TotalSpace.proj ⁻¹' A =
      sphereBundle F E ∪ discBundle F E ∩ TotalSpace.proj ⁻¹' A := by
  simp

end Sets

variable {B : Type u} [TopologicalSpace B] [T2Space B] (F : Type*) [NormedAddCommGroup F]
  [NormedSpace ℝ F] [FiniteDimensional ℝ F] (E : B → Type u) [∀ b, NormedAddCommGroup (E b)]
  [∀ b, InnerProductSpace ℝ (E b)] [TopologicalSpace (TotalSpace F E)] [FiberBundle F E]
  [VectorBundle ℝ F E] [ContinuousFiberNorm F E]

section DiscBundle

variable [CWComplex (univ : Set B)]

/-- **The disc bundle over a CW complex, relative to the sphere bundle.** If `B` is a CW complex,
the unit disc bundle `D(E)` is a CW complex relative to the unit sphere bundle `S(E)`, with one
`(m + r)`-cell for each `m`-cell of `B`, `r` the rank
(`TauCeti.relCWComplexDiscBundleSphereBundleCellEquiv`). It is `TauCeti.relCWComplexDiscBundle`
for the whole of `B`. -/
@[instance_reducible]
def relCWComplexDiscBundleSphereBundle : RelCWComplex (discBundle F E) (sphereBundle F E) :=
  (relCWComplexDiscBundle F E (univ : Set B)).copy (discBundle F E) (sphereBundle F E)
    (discBundle_inter_preimage_univ F E) (sphereBundle_union_empty F E)

/-- The `n`-cells of the disc bundle relative to the sphere bundle are the `m`-cells of `B` with
`m + r = n`, where `r` is the rank of the bundle. -/
def relCWComplexDiscBundleSphereBundleCellEquiv (n : ℕ) :
    letI := relCWComplexDiscBundleSphereBundle F E
    cell (discBundle F E) n ≃
      Σ m : {m : ℕ // m + Module.finrank ℝ F = n}, cell (univ : Set B) m :=
  letI := relCWComplexDiscBundle F E (univ : Set B)
  ((relCWComplexDiscBundle F E (univ : Set B)).copyCellEquiv (discBundle F E) (sphereBundle F E)
    (discBundle_inter_preimage_univ F E) (sphereBundle_union_empty F E) n).trans
    (cellDiscBundleEquiv F E univ n)

variable {F E}

/-- The disc bundle relative to the sphere bundle has no cells below the rank of the bundle. -/
theorem isEmpty_cell_relCWComplexDiscBundleSphereBundle_of_lt {n : ℕ}
    (hn : n < Module.finrank ℝ F) :
    letI := relCWComplexDiscBundleSphereBundle F E
    IsEmpty (cell (discBundle F E) n) :=
  letI := relCWComplexDiscBundleSphereBundle F E
  letI := relCWComplexDiscBundle F E (univ : Set B)
  have := isEmpty_cell_relCWComplexDiscBundle_of_lt (F := F) (E := E) (C := (univ : Set B)) hn
  ((relCWComplexDiscBundle F E (univ : Set B)).copyCellEquiv (discBundle F E) (sphereBundle F E)
    (discBundle_inter_preimage_univ F E) (sphereBundle_union_empty F E) n).isEmpty_congr.2
    inferInstance

variable {n : ℕ} (c : Σ m : {m : ℕ // m + Module.finrank ℝ F = n}, cell (univ : Set B) m)

/-- The characteristic maps of `TauCeti.relCWComplexDiscBundleSphereBundle` are those of
`TauCeti.relCWComplexDiscBundle` for the whole of `B`. -/
theorem coe_map_relCWComplexDiscBundleSphereBundle :
    letI := relCWComplexDiscBundleSphereBundle F E
    letI := relCWComplexDiscBundle F E (univ : Set B)
    ⇑(map n ((relCWComplexDiscBundleSphereBundleCellEquiv F E n).symm c)) =
      ⇑(map n ((cellDiscBundleEquiv F E univ n).symm c)) := by
  let I := relCWComplexDiscBundle F E (univ : Set B)
  have hcopy := I.map_copy (discBundle F E) (sphereBundle F E) (discBundle_inter_preimage_univ F E)
    (sphereBundle_union_empty F E) n ((relCWComplexDiscBundleSphereBundleCellEquiv F E n).symm c)
  refine (congrArg (fun f : PartialEquiv _ _ ↦ (f : (Fin n → ℝ) → TotalSpace F E))
    hcopy).trans ?_
  rw [relCWComplexDiscBundleSphereBundleCellEquiv, Equiv.symm_trans_apply,
    Equiv.apply_symm_apply]

/-- Explicit evaluation of a characteristic map of `relCWComplexDiscBundleSphereBundle` in terms
of `TauCeti.discBundleCellFrame` and `TauCeti.discBundleFibreCoord`. -/
theorem map_relCWComplexDiscBundleSphereBundle_apply (x : Fin n → ℝ) :
    letI := relCWComplexDiscBundleSphereBundle F E
    map n ((relCWComplexDiscBundleSphereBundleCellEquiv F E n).symm c) x =
      ⟨(discBundleCellFrame F E c.2 ((Fin.appendIsometryOfEq c.1.property).symm x).1).proj,
        (discBundleCellFrame F E c.2 ((Fin.appendIsometryOfEq c.1.property).symm x).1).frame
          (discBundleFibreCoord F ((Fin.appendIsometryOfEq c.1.property).symm x).2)⟩ := by
  let := relCWComplexDiscBundle F E (univ : Set B)
  rw [coe_map_relCWComplexDiscBundleSphereBundle]
  exact map_relCWComplexDiscBundle_apply c x

/-- The characteristic map of the cell of the disc bundle over an `m`-cell of `B` lies over the
characteristic map of that cell, applied to the first `m` coordinates. -/
theorem proj_map_relCWComplexDiscBundleSphereBundle {x : Fin n → ℝ} (hx : x ∈ closedBall 0 1) :
    letI := relCWComplexDiscBundleSphereBundle F E
    (map n ((relCWComplexDiscBundleSphereBundleCellEquiv F E n).symm c) x).proj =
      map c.1.val c.2 ((Fin.appendIsometryOfEq c.1.property).symm x).1 := by
  let := relCWComplexDiscBundle F E (univ : Set B)
  rw [coe_map_relCWComplexDiscBundleSphereBundle]
  exact proj_map_relCWComplexDiscBundle c hx

/-- The closed cell of the disc bundle over an `m`-cell `j` of `B` is the part of the disc bundle
over the closed cell of `j`. -/
@[simp]
theorem closedCell_relCWComplexDiscBundleSphereBundle :
    letI := relCWComplexDiscBundleSphereBundle F E
    closedCell n ((relCWComplexDiscBundleSphereBundleCellEquiv F E n).symm c) =
      discBundle F E ∩ TotalSpace.proj ⁻¹' closedCell c.1.val c.2 := by
  let I := relCWComplexDiscBundle F E (univ : Set B)
  rw [relCWComplexDiscBundleSphereBundleCellEquiv, Equiv.symm_trans_apply]
  refine (I.closedCell_copy (discBundle F E) (sphereBundle F E)
    (discBundle_inter_preimage_univ F E) (sphereBundle_union_empty F E) n _).trans ?_
  rw [Equiv.apply_symm_apply]
  exact closedCell_relCWComplexDiscBundle (E := E) c

/-- The open cell of the disc bundle over an `m`-cell `j` of `B` consists of the vectors of norm
less than one over the open cell of `j`. -/
@[simp]
theorem openCell_relCWComplexDiscBundleSphereBundle :
    letI := relCWComplexDiscBundleSphereBundle F E
    openCell n ((relCWComplexDiscBundleSphereBundleCellEquiv F E n).symm c) =
      {v : TotalSpace F E | ‖v.snd‖ < 1} ∩ TotalSpace.proj ⁻¹' openCell c.1.val c.2 := by
  let I := relCWComplexDiscBundle F E (univ : Set B)
  rw [relCWComplexDiscBundleSphereBundleCellEquiv, Equiv.symm_trans_apply]
  refine (I.openCell_copy (discBundle F E) (sphereBundle F E)
    (discBundle_inter_preimage_univ F E) (sphereBundle_union_empty F E) n _).trans ?_
  rw [Equiv.apply_symm_apply]
  exact openCell_relCWComplexDiscBundle (E := E) c

/-- The boundary of the cell of the disc bundle over an `m`-cell `j` of `B` is the part of the
sphere bundle over the closed cell of `j` together with the part of the disc bundle over the
boundary of `j`. -/
@[simp]
theorem cellFrontier_relCWComplexDiscBundleSphereBundle :
    letI := relCWComplexDiscBundleSphereBundle F E
    cellFrontier n ((relCWComplexDiscBundleSphereBundleCellEquiv F E n).symm c) =
      sphereBundle F E ∩ TotalSpace.proj ⁻¹' closedCell c.1.val c.2 ∪
        discBundle F E ∩ TotalSpace.proj ⁻¹' cellFrontier c.1.val c.2 := by
  let I := relCWComplexDiscBundle F E (univ : Set B)
  rw [relCWComplexDiscBundleSphereBundleCellEquiv, Equiv.symm_trans_apply]
  refine (I.cellFrontier_copy (discBundle F E) (sphereBundle F E)
    (discBundle_inter_preimage_univ F E) (sphereBundle_union_empty F E) n _).trans ?_
  rw [Equiv.apply_symm_apply]
  exact cellFrontier_relCWComplexDiscBundle (E := E) c

variable (F E) in
/-- The disc bundle over a finite-dimensional CW complex is finite-dimensional relative to the
sphere bundle. -/
theorem finiteDimensional_relCWComplexDiscBundleSphereBundle
    [RelCWComplex.FiniteDimensional (univ : Set B)] :
    letI := relCWComplexDiscBundleSphereBundle F E
    RelCWComplex.FiniteDimensional (discBundle F E) :=
  letI := relCWComplexDiscBundle F E (univ : Set B)
  haveI := finiteDimensional_relCWComplexDiscBundle (F := F) (E := E) (C := (univ : Set B))
  (relCWComplexDiscBundle F E (univ : Set B)).finiteDimensional_copy (discBundle F E)
    (sphereBundle F E) (discBundle_inter_preimage_univ F E) (sphereBundle_union_empty F E)

variable (F E) in
/-- The disc bundle over a CW complex of finite type has finite type relative to the sphere
bundle. -/
theorem finiteType_relCWComplexDiscBundleSphereBundle [RelCWComplex.FiniteType (univ : Set B)] :
    letI := relCWComplexDiscBundleSphereBundle F E
    RelCWComplex.FiniteType (discBundle F E) :=
  letI := relCWComplexDiscBundle F E (univ : Set B)
  haveI := finiteType_relCWComplexDiscBundle (F := F) (E := E) (C := (univ : Set B))
  (relCWComplexDiscBundle F E (univ : Set B)).finiteType_copy (discBundle F E)
    (sphereBundle F E) (discBundle_inter_preimage_univ F E) (sphereBundle_union_empty F E)

variable (F E) in
/-- The disc bundle over a finite CW complex is a finite CW complex relative to the sphere
bundle. -/
theorem finite_relCWComplexDiscBundleSphereBundle [RelCWComplex.Finite (univ : Set B)] :
    letI := relCWComplexDiscBundleSphereBundle F E
    RelCWComplex.Finite (discBundle F E) :=
  letI := relCWComplexDiscBundle F E (univ : Set B)
  haveI := finite_relCWComplexDiscBundle (F := F) (E := E) (C := (univ : Set B))
  (relCWComplexDiscBundle F E (univ : Set B)).finite_copy (discBundle F E)
    (sphereBundle F E) (discBundle_inter_preimage_univ F E) (sphereBundle_union_empty F E)

end DiscBundle

section DiscBundleRel

variable (A : Set B) [RelCWComplex (univ : Set B) A]

/-- **The disc bundle over a relative CW pair `(B, A)`, relative to `S(E) ∪ D(E)|_A`.** If
`(univ : Set B)` is a CW complex relative to `A`, the unit disc bundle `D(E)` is a CW complex
relative to `S(E) ∪ D(E)|_A`, with one `(m + r)`-cell for each relative `m`-cell of `(B, A)`
(`TauCeti.relCWComplexDiscBundleRelCellEquiv`). It is `TauCeti.relCWComplexDiscBundle` specialized
to `C = univ` and `D = A`. -/
@[instance_reducible]
def relCWComplexDiscBundleRel :
    RelCWComplex (discBundle F E) (sphereBundle F E ∪ discBundle F E ∩ TotalSpace.proj ⁻¹' A) :=
  (relCWComplexDiscBundle F E (univ : Set B)).copy (discBundle F E)
    (sphereBundle F E ∪ discBundle F E ∩ TotalSpace.proj ⁻¹' A)
    (discBundle_inter_preimage_univ F E) (sphereBundle_union_rel F E A)

/-- The `n`-cells of `D(E)` relative to `S(E) ∪ D(E)|_A` are the relative `m`-cells of `(B, A)`
with `m + r = n`, where `r` is the rank of the bundle. -/
def relCWComplexDiscBundleRelCellEquiv (n : ℕ) :
    letI := relCWComplexDiscBundleRel F E A
    cell (discBundle F E) n ≃
      Σ m : {m : ℕ // m + Module.finrank ℝ F = n}, cell (univ : Set B) m :=
  letI := relCWComplexDiscBundle F E (univ : Set B)
  ((relCWComplexDiscBundle F E (univ : Set B)).copyCellEquiv (discBundle F E)
    (sphereBundle F E ∪ discBundle F E ∩ TotalSpace.proj ⁻¹' A)
    (discBundle_inter_preimage_univ F E) (sphereBundle_union_rel F E A) n).trans
    (cellDiscBundleEquiv F E univ n)

variable {F E A}

/-- Below the rank of the bundle, `relCWComplexDiscBundleRel` has no cells. -/
theorem isEmpty_cell_relCWComplexDiscBundleRel_of_lt {n : ℕ} (hn : n < Module.finrank ℝ F) :
    letI := relCWComplexDiscBundleRel F E A
    IsEmpty (cell (discBundle F E) n) :=
  let := relCWComplexDiscBundleRel F E A
  letI := relCWComplexDiscBundle F E (univ : Set B)
  have := isEmpty_cell_relCWComplexDiscBundle_of_lt (F := F) (E := E) (C := (univ : Set B)) hn
  ((relCWComplexDiscBundle F E (univ : Set B)).copyCellEquiv (discBundle F E)
    (sphereBundle F E ∪ discBundle F E ∩ TotalSpace.proj ⁻¹' A)
    (discBundle_inter_preimage_univ F E) (sphereBundle_union_rel F E A) n).isEmpty_congr.2
    inferInstance

variable {n : ℕ} (c : Σ m : {m : ℕ // m + Module.finrank ℝ F = n}, cell (univ : Set B) m)

/-- The characteristic maps of `TauCeti.relCWComplexDiscBundleRel` are those of
`TauCeti.relCWComplexDiscBundle` specialized to `C = univ`. -/
theorem coe_map_relCWComplexDiscBundleRel :
    letI := relCWComplexDiscBundleRel F E A
    letI := relCWComplexDiscBundle F E (univ : Set B)
    ⇑(map n ((relCWComplexDiscBundleRelCellEquiv F E A n).symm c)) =
      ⇑(map n ((cellDiscBundleEquiv F E univ n).symm c)) := by
  let I := relCWComplexDiscBundle F E (univ : Set B)
  have hcopy := I.map_copy (discBundle F E)
    (sphereBundle F E ∪ discBundle F E ∩ TotalSpace.proj ⁻¹' A)
    (discBundle_inter_preimage_univ F E) (sphereBundle_union_rel F E A) n
    ((relCWComplexDiscBundleRelCellEquiv F E A n).symm c)
  refine (congrArg (fun f : PartialEquiv _ _ ↦ (f : (Fin n → ℝ) → TotalSpace F E))
    hcopy).trans ?_
  rw [relCWComplexDiscBundleRelCellEquiv, Equiv.symm_trans_apply, Equiv.apply_symm_apply]

/-- Explicit evaluation of a characteristic map of `relCWComplexDiscBundleRel` in terms of
`TauCeti.discBundleCellFrame` and `TauCeti.discBundleFibreCoord`. -/
theorem map_relCWComplexDiscBundleRel_apply (x : Fin n → ℝ) :
    letI := relCWComplexDiscBundleRel F E A
    map n ((relCWComplexDiscBundleRelCellEquiv F E A n).symm c) x =
      ⟨(discBundleCellFrame F E c.2 ((Fin.appendIsometryOfEq c.1.property).symm x).1).proj,
        (discBundleCellFrame F E c.2 ((Fin.appendIsometryOfEq c.1.property).symm x).1).frame
          (discBundleFibreCoord F ((Fin.appendIsometryOfEq c.1.property).symm x).2)⟩ := by
  let := relCWComplexDiscBundle F E (univ : Set B)
  rw [coe_map_relCWComplexDiscBundleRel]
  exact map_relCWComplexDiscBundle_apply c x

/-- The characteristic map of the cell of `D(E)` over a relative `m`-cell of `(B, A)` lies over
the characteristic map of that cell, applied to the first `m` coordinates. -/
theorem proj_map_relCWComplexDiscBundleRel {x : Fin n → ℝ} (hx : x ∈ closedBall 0 1) :
    letI := relCWComplexDiscBundleRel F E A
    (map n ((relCWComplexDiscBundleRelCellEquiv F E A n).symm c) x).proj =
      map c.1.val c.2 ((Fin.appendIsometryOfEq c.1.property).symm x).1 := by
  let := relCWComplexDiscBundle F E (univ : Set B)
  rw [coe_map_relCWComplexDiscBundleRel]
  exact proj_map_relCWComplexDiscBundle c hx

/-- The closed cell of `relCWComplexDiscBundleRel` over a relative `m`-cell `j` of `(B, A)` is the
part of the disc bundle over the closed cell of `j`. -/
@[simp]
theorem closedCell_relCWComplexDiscBundleRel :
    letI := relCWComplexDiscBundleRel F E A
    closedCell n ((relCWComplexDiscBundleRelCellEquiv F E A n).symm c) =
      discBundle F E ∩ TotalSpace.proj ⁻¹' closedCell c.1.val c.2 := by
  let I := relCWComplexDiscBundle F E (univ : Set B)
  rw [relCWComplexDiscBundleRelCellEquiv, Equiv.symm_trans_apply]
  refine (I.closedCell_copy (discBundle F E)
    (sphereBundle F E ∪ discBundle F E ∩ TotalSpace.proj ⁻¹' A)
    (discBundle_inter_preimage_univ F E) (sphereBundle_union_rel F E A) n _).trans ?_
  rw [Equiv.apply_symm_apply]
  exact closedCell_relCWComplexDiscBundle (E := E) c

/-- The open cell of `relCWComplexDiscBundleRel` over a relative `m`-cell `j` of `(B, A)` consists
of the vectors of norm less than one over the open cell of `j`. -/
@[simp]
theorem openCell_relCWComplexDiscBundleRel :
    letI := relCWComplexDiscBundleRel F E A
    openCell n ((relCWComplexDiscBundleRelCellEquiv F E A n).symm c) =
      {v : TotalSpace F E | ‖v.snd‖ < 1} ∩ TotalSpace.proj ⁻¹' openCell c.1.val c.2 := by
  let I := relCWComplexDiscBundle F E (univ : Set B)
  rw [relCWComplexDiscBundleRelCellEquiv, Equiv.symm_trans_apply]
  refine (I.openCell_copy (discBundle F E)
    (sphereBundle F E ∪ discBundle F E ∩ TotalSpace.proj ⁻¹' A)
    (discBundle_inter_preimage_univ F E) (sphereBundle_union_rel F E A) n _).trans ?_
  rw [Equiv.apply_symm_apply]
  exact openCell_relCWComplexDiscBundle (E := E) c

/-- The boundary of the cell of `relCWComplexDiscBundleRel` over a relative `m`-cell `j` of
`(B, A)` is the part of the sphere bundle over the closed cell of `j` together with the part of the
disc bundle over the boundary of `j`. -/
@[simp]
theorem cellFrontier_relCWComplexDiscBundleRel :
    letI := relCWComplexDiscBundleRel F E A
    cellFrontier n ((relCWComplexDiscBundleRelCellEquiv F E A n).symm c) =
      sphereBundle F E ∩ TotalSpace.proj ⁻¹' closedCell c.1.val c.2 ∪
        discBundle F E ∩ TotalSpace.proj ⁻¹' cellFrontier c.1.val c.2 := by
  let I := relCWComplexDiscBundle F E (univ : Set B)
  rw [relCWComplexDiscBundleRelCellEquiv, Equiv.symm_trans_apply]
  refine (I.cellFrontier_copy (discBundle F E)
    (sphereBundle F E ∪ discBundle F E ∩ TotalSpace.proj ⁻¹' A)
    (discBundle_inter_preimage_univ F E) (sphereBundle_union_rel F E A) n _).trans ?_
  rw [Equiv.apply_symm_apply]
  exact cellFrontier_relCWComplexDiscBundle (E := E) c

variable (F E A)

/-- `relCWComplexDiscBundleRel` is finite-dimensional when `(B, A)` is finite-dimensional. -/
theorem finiteDimensional_relCWComplexDiscBundleRel
    [RelCWComplex.FiniteDimensional (univ : Set B)] :
    letI := relCWComplexDiscBundleRel F E A
    RelCWComplex.FiniteDimensional (discBundle F E) :=
  letI := relCWComplexDiscBundle F E (univ : Set B)
  haveI := finiteDimensional_relCWComplexDiscBundle (F := F) (E := E) (C := (univ : Set B))
  (relCWComplexDiscBundle F E (univ : Set B)).finiteDimensional_copy (discBundle F E)
    (sphereBundle F E ∪ discBundle F E ∩ TotalSpace.proj ⁻¹' A)
    (discBundle_inter_preimage_univ F E) (sphereBundle_union_rel F E A)

/-- `relCWComplexDiscBundleRel` has finite type when `(B, A)` has finite type. -/
theorem finiteType_relCWComplexDiscBundleRel [RelCWComplex.FiniteType (univ : Set B)] :
    letI := relCWComplexDiscBundleRel F E A
    RelCWComplex.FiniteType (discBundle F E) :=
  letI := relCWComplexDiscBundle F E (univ : Set B)
  haveI := finiteType_relCWComplexDiscBundle (F := F) (E := E) (C := (univ : Set B))
  (relCWComplexDiscBundle F E (univ : Set B)).finiteType_copy (discBundle F E)
    (sphereBundle F E ∪ discBundle F E ∩ TotalSpace.proj ⁻¹' A)
    (discBundle_inter_preimage_univ F E) (sphereBundle_union_rel F E A)

/-- `relCWComplexDiscBundleRel` is finite when `(B, A)` is finite. -/
theorem finite_relCWComplexDiscBundleRel [RelCWComplex.Finite (univ : Set B)] :
    letI := relCWComplexDiscBundleRel F E A
    RelCWComplex.Finite (discBundle F E) :=
  letI := relCWComplexDiscBundle F E (univ : Set B)
  haveI := finite_relCWComplexDiscBundle (F := F) (E := E) (C := (univ : Set B))
  (relCWComplexDiscBundle F E (univ : Set B)).finite_copy (discBundle F E)
    (sphereBundle F E ∪ discBundle F E ∩ TotalSpace.proj ⁻¹' A)
    (discBundle_inter_preimage_univ F E) (sphereBundle_union_rel F E A)

end DiscBundleRel

end TauCeti
