/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.UpperHalfPlane.Cayley
public import TauCeti.Geometry.Manifold.Complex.BorderedHolomorphic.Interior
public import TauCeti.Topology.Constructions.DoubleAlong.Disc

/-!
# The closed unit disc as a Riemann surface with boundary

The closed unit disc is a Riemann surface with boundary, modelled on the closed upper half-plane.
For a point `ζ` of the unit circle, the Cayley chart `TauCeti.ClosedUnitDisc.cayleyChart ζ` is
`z ↦ I (ζ - z) / (ζ + z)`. It is defined on the closed disc minus `-ζ`, its image is the whole
closed upper half-plane, and its inverse is `w ↦ ζ (I - w) / (I + w)`: the imaginary part of
`I (ζ - z) / (ζ + z)` is `(1 - ‖z‖²) / ‖ζ + z‖²`, so `‖z‖ ≤ 1` exactly when the image has
nonnegative imaginary part, and the image is real exactly when `‖z‖ = 1`. The atlas consists of
the Cayley charts for all `ζ`; the chart at `z` uses `ζ = 1` when `0 ≤ re z` and `ζ = -1`
otherwise. The transition maps are Möbius maps preserving the closed upper half-plane, with their
pole on the real axis, so they are holomorphic on their domains, up to the boundary, and lie in
the bordered holomorphic groupoid.

The manifold interior is the open unit disc, and the manifold boundary is the unit circle
`TauCeti.DoubleAlong.discBoundary`, the boundary along which `TauCeti.DoubleAlong` doubles the
disc to the Riemann sphere. The induced complex structure on the interior is the standard one:
the inclusion of the interior into `ℂ` is analytic.

The carrier `TauCeti.ClosedUnitDisc` is a type synonym for `closedBall (0 : ℂ) 1`, the carrier of
`TauCeti.DoubleAlong.discBoundary`. It is a synonym, not the subtype itself, because the subtype
already carries the half-space atlas `TauCeti.instChartedSpaceClosedBallComplex` modelled on
`EuclideanHalfSpace 2`, and the model of a charted space is an `outParam`: a second
`ChartedSpace` instance on the same type would make chart lookups ambiguous.

## Main declarations

* `TauCeti.ClosedUnitDisc`: the closed unit disc, as a type synonym of `closedBall (0 : ℂ) 1`.
* `TauCeti.ClosedUnitDisc.cayleyChart`: the Cayley chart attached to a point of the unit circle.
* `TauCeti.ClosedUnitDisc.instChartedSpace`: the atlas of Cayley charts.
* `TauCeti.ClosedUnitDisc.instHasGroupoid`: the Cayley charts have bordered holomorphic
  transition maps, so the closed disc is a Riemann surface with boundary.
* `TauCeti.ClosedUnitDisc.mem_borderedInterior_iff` and
  `TauCeti.ClosedUnitDisc.compl_borderedInterior`: the interior is the open disc and its
  complement is the boundary circle `TauCeti.DoubleAlong.discBoundary`.
* `TauCeti.ClosedUnitDisc.contMDiff_coe_borderedInterior`: the inclusion of the interior into
  `ℂ` is analytic, so the interior carries the standard complex structure.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS
  Colloquium Publications **52**, 2012, Section 2.4, for Riemann surfaces with boundary.
-/

@[expose] public section

noncomputable section

open Set Complex Metric Filter
open scoped Manifold ContDiff Topology

namespace TauCeti

/-- The closed unit disc in `ℂ`, as a type synonym of `closedBall (0 : ℂ) 1`. It carries the
atlas of Cayley charts modelled on the closed upper half-plane. The synonym keeps this atlas
apart from the half-space atlas `TauCeti.instChartedSpaceClosedBallComplex` of the subtype. -/
def ClosedUnitDisc : Type := closedBall (0 : ℂ) 1

namespace ClosedUnitDisc

/-- The closed unit disc carries the subspace topology of `ℂ`. -/
instance instTopologicalSpace : TopologicalSpace ClosedUnitDisc :=
  inferInstanceAs (TopologicalSpace (closedBall (0 : ℂ) 1))

/-- A point of the closed unit disc is a complex number. -/
instance instCoeOut : CoeOut ClosedUnitDisc ℂ :=
  ⟨fun z : closedBall (0 : ℂ) 1 ↦ (z : ℂ)⟩

/-- The inclusion of the closed unit disc into `ℂ` is continuous. -/
theorem continuous_coe : Continuous ((↑) : ClosedUnitDisc → ℂ) :=
  continuous_subtype_val

/-- A point of the closed unit disc is determined by its value in `ℂ`. -/
theorem coe_injective : Function.Injective ((↑) : ClosedUnitDisc → ℂ) :=
  Subtype.val_injective

/-- The closed unit disc carries the topology induced from `ℂ`. -/
theorem isInducing_coe : Topology.IsInducing ((↑) : ClosedUnitDisc → ℂ) :=
  Topology.IsInducing.subtypeVal

/-- A point of the closed unit disc has norm at most one. -/
theorem norm_coe_le_one (z : ClosedUnitDisc) : ‖(z : ℂ)‖ ≤ 1 :=
  mem_closedBall_zero_iff.1 (z : closedBall (0 : ℂ) 1).2

/-- The identity, from the closed unit disc to the subtype `closedBall (0 : ℂ) 1` it is a synonym
of. -/
def homeomorphClosedBall : ClosedUnitDisc ≃ₜ closedBall (0 : ℂ) 1 :=
  Homeomorph.refl _

@[simp]
theorem coe_homeomorphClosedBall (z : ClosedUnitDisc) : (homeomorphClosedBall z : ℂ) = z :=
  rfl

@[simp]
theorem coe_homeomorphClosedBall_symm (z : closedBall (0 : ℂ) 1) :
    (homeomorphClosedBall.symm z : ℂ) = z :=
  rfl

/-- A complex number of norm at most one, as a point of the closed unit disc. -/
def mk (z : ℂ) (hz : ‖z‖ ≤ 1) : ClosedUnitDisc :=
  (⟨z, mem_closedBall_zero_iff.2 hz⟩ : closedBall (0 : ℂ) 1)

@[simp]
theorem coe_mk (z : ℂ) (hz : ‖z‖ ≤ 1) : (mk z hz : ℂ) = z :=
  rfl

/-! ### Algebra of the Cayley transform -/

private theorem normSq_of_norm_eq_one {ζ : ℂ} (hζ : ‖ζ‖ = 1) : normSq ζ = 1 := by
  rw [normSq_eq_norm_sq, hζ, one_pow]

private theorem ne_zero_of_norm_eq_one {ζ : ℂ} (hζ : ‖ζ‖ = 1) : ζ ≠ 0 := by
  rintro rfl
  simp at hζ

/-- The imaginary part of the Cayley transform is `(1 - ‖z‖²) / ‖ζ + z‖²`. -/
theorem im_cayley {ζ : ℂ} (hζ : ‖ζ‖ = 1) (z : ℂ) :
    (I * (ζ - z) / (ζ + z)).im = (1 - normSq z) / normSq (ζ + z) := by
  have h1 := normSq_of_norm_eq_one hζ
  rw [normSq_apply] at h1
  rw [div_im, ← sub_div, normSq_apply, normSq_apply]
  congr 1
  simp only [mul_re, mul_im, I_re, I_im, sub_re, sub_im, add_re, add_im]
  linear_combination h1

private theorem norm_cayleyInv {ζ : ℂ} (hζ : ‖ζ‖ = 1) (w : ℂ) :
    ‖ζ * (I - w) / (I + w)‖ = ‖I - w‖ / ‖I + w‖ := by
  rw [norm_div, norm_mul, hζ, one_mul]

/-- The inverse Cayley transform of a point of the closed upper half-plane lies in the closed unit
disc. -/
theorem norm_cayleyInv_le_one {ζ : ℂ} (hζ : ‖ζ‖ = 1) {w : ℂ} (hw : 0 ≤ w.im) :
    ‖ζ * (I - w) / (I + w)‖ ≤ 1 := by
  rw [norm_cayleyInv hζ, norm_sub_rev, add_comm]
  exact (norm_sub_I_div_norm_add_I_le_one_iff (add_I_ne_zero_of_im_nonneg hw)).2 hw

/-- The inverse Cayley transform with center `ζ` never takes the value `-ζ`. -/
theorem cayleyInv_ne_neg {ζ : ℂ} (hζ : ‖ζ‖ = 1) {w : ℂ} (hw : 0 ≤ w.im) :
    ζ * (I - w) / (I + w) ≠ -ζ := by
  intro h
  have hζ0 := ne_zero_of_norm_eq_one hζ
  have hw0 := add_comm I w ▸ add_I_ne_zero_of_im_nonneg hw
  rw [div_eq_iff hw0] at h
  have : ζ * (2 * I) = 0 := by linear_combination h
  simp [hζ0, I_ne_zero] at this

/-- The inverse Cayley transform undoes the Cayley transform away from `-ζ`. -/
theorem cayleyInv_cayley {ζ z : ℂ} (hζ : ‖ζ‖ = 1) (hz : z ≠ -ζ) :
    ζ * (I - I * (ζ - z) / (ζ + z)) / (I + I * (ζ - z) / (ζ + z)) = z := by
  have hζ0 := ne_zero_of_norm_eq_one hζ
  have hz0 : ζ + z ≠ 0 := fun h ↦ hz (by linear_combination h)
  have h2 : I + I * (ζ - z) / (ζ + z) = 2 * I * ζ / (ζ + z) := by
    field_simp
    ring
  rw [h2, div_eq_iff (by simp [hζ0, hz0, I_ne_zero])]
  field_simp
  ring

/-- The Cayley transform undoes the inverse Cayley transform on the closed upper half-plane. -/
theorem cayley_cayleyInv {ζ w : ℂ} (hζ : ‖ζ‖ = 1) (hw : 0 ≤ w.im) :
    I * (ζ - ζ * (I - w) / (I + w)) / (ζ + ζ * (I - w) / (I + w)) = w := by
  have hζ0 := ne_zero_of_norm_eq_one hζ
  have hw0 := add_comm I w ▸ add_I_ne_zero_of_im_nonneg hw
  have h2 : ζ + ζ * (I - w) / (I + w) = 2 * I * ζ / (I + w) := by
    field_simp
    ring
  rw [h2, div_eq_iff (by simp [hζ0, hw0, I_ne_zero])]
  field_simp
  ring_nf

/-! ### Cayley charts -/

/-- The Cayley transform of a point of the closed unit disc has nonnegative imaginary part. -/
theorem im_cayley_nonneg {ζ : ℂ} (hζ : ‖ζ‖ = 1) (z : ClosedUnitDisc) :
    0 ≤ (I * (ζ - z) / (ζ + z)).im := by
  rw [im_cayley hζ]
  refine div_nonneg ?_ (normSq_nonneg _)
  rw [sub_nonneg, normSq_eq_norm_sq]
  exact pow_le_one₀ (norm_nonneg _) (norm_coe_le_one z)

/-- The Cayley chart attached to a point `ζ` of the unit circle: the map
`z ↦ I (ζ - z) / (ζ + z)` from the closed unit disc minus `-ζ` onto the closed upper half-plane,
with inverse `w ↦ ζ (I - w) / (I + w)`. It sends `ζ` to `0` and `0` to `I`. -/
def cayleyChart (ζ : ℂ) (hζ : ‖ζ‖ = 1) :
    OpenPartialHomeomorph ClosedUnitDisc ClosedUpperHalfPlane where
  toFun z := ⟨I * (ζ - z) / (ζ + z), im_cayley_nonneg hζ z⟩
  invFun w := mk (ζ * (I - w) / (I + w)) (norm_cayleyInv_le_one hζ w.2)
  source := {z : ClosedUnitDisc | (z : ℂ) ≠ -ζ}
  target := univ
  map_source' _ _ := mem_univ _
  map_target' w _ := cayleyInv_ne_neg hζ w.2
  left_inv' z hz := coe_injective (cayleyInv_cayley hζ hz)
  right_inv' w _ := Subtype.ext (cayley_cayleyInv hζ w.2)
  open_source := isOpen_ne_fun continuous_coe continuous_const
  open_target := isOpen_univ
  continuousOn_toFun := by
    refine ((Topology.IsEmbedding.subtypeVal
      (p := fun w : ℂ ↦ 0 ≤ w.im)).isInducing.continuousOn_iff).2 fun z hz ↦ ?_
    have hz' : ζ + (z : ℂ) ≠ 0 := fun h ↦ hz (by linear_combination h)
    exact ((continuousAt_const.mul (continuousAt_const.sub continuous_coe.continuousAt)).div
      (continuousAt_const.add continuous_coe.continuousAt) hz').continuousWithinAt
  continuousOn_invFun := by
    refine (isInducing_coe.continuousOn_iff).2 ?_
    refine Continuous.continuousOn (continuous_iff_continuousAt.2 fun w ↦ ?_)
    exact (continuousAt_const.mul (continuousAt_const.sub continuous_subtype_val.continuousAt)).div
      (continuousAt_const.add continuous_subtype_val.continuousAt)
      (add_comm I (w : ℂ) ▸ add_I_ne_zero_of_im_nonneg w.2)

variable {ζ : ℂ} {hζ : ‖ζ‖ = 1}

/-- A Cayley chart is `z ↦ I (ζ - z) / (ζ + z)`. -/
@[simp]
theorem coe_cayleyChart_apply (z : ClosedUnitDisc) :
    (cayleyChart ζ hζ z : ℂ) = I * (ζ - z) / (ζ + z) :=
  rfl

/-- The inverse of a Cayley chart is `w ↦ ζ (I - w) / (I + w)`. -/
@[simp]
theorem coe_cayleyChart_symm_apply (w : ClosedUpperHalfPlane) :
    ((cayleyChart ζ hζ).symm w : ℂ) = ζ * (I - w) / (I + w) :=
  rfl

/-- A Cayley chart is defined on the closed unit disc minus `-ζ`. -/
@[simp]
theorem cayleyChart_source :
    (cayleyChart ζ hζ).source = {z : ClosedUnitDisc | (z : ℂ) ≠ -ζ} :=
  rfl

/-- A Cayley chart takes values in the whole closed upper half-plane. -/
@[simp]
theorem cayleyChart_target : (cayleyChart ζ hζ).target = univ :=
  rfl

/-- The imaginary part of a Cayley chart is `(1 - ‖z‖²) / ‖ζ + z‖²`. -/
theorem im_cayleyChart_apply (z : ClosedUnitDisc) :
    (cayleyChart ζ hζ z : ℂ).im = (1 - ‖(z : ℂ)‖ ^ 2) / ‖ζ + z‖ ^ 2 := by
  rw [coe_cayleyChart_apply, im_cayley hζ, Complex.sq_norm, Complex.sq_norm]

/-- A point of the source of a Cayley chart has image of positive imaginary part exactly when it
lies in the open unit disc. -/
theorem im_cayleyChart_pos_iff {z : ClosedUnitDisc} (hz : z ∈ (cayleyChart ζ hζ).source) :
    0 < (cayleyChart ζ hζ z : ℂ).im ↔ ‖(z : ℂ)‖ < 1 := by
  have hz0 : ‖ζ + z‖ ≠ 0 := norm_ne_zero_iff.2 fun h ↦ hz (by linear_combination h)
  rw [im_cayleyChart_apply, div_pos_iff_of_pos_right (by positivity), sub_pos,
    sq_lt_one_iff₀ (norm_nonneg _)]

/-! ### The atlas -/

/-- The center of the preferred chart at `z`: `1` if `0 ≤ re z`, and `-1` otherwise. -/
def chartCenter (z : ClosedUnitDisc) : ℂ :=
  if 0 ≤ (z : ℂ).re then 1 else -1

/-- The center of the preferred chart lies on the unit circle. -/
theorem norm_chartCenter (z : ClosedUnitDisc) : ‖chartCenter z‖ = 1 := by
  unfold chartCenter
  split_ifs <;> simp

/-- A point lies in the source of its preferred chart. -/
theorem coe_ne_neg_chartCenter (z : ClosedUnitDisc) : (z : ℂ) ≠ -chartCenter z := by
  unfold chartCenter
  split_ifs with h
  · intro hz
    rw [hz] at h
    norm_num at h
  · intro hz
    rw [hz] at h
    norm_num at h

/-- The closed unit disc is a charted space modelled on the closed upper half-plane: the atlas
consists of the Cayley charts, and the chart at `z` has center `1` if `0 ≤ re z` and `-1`
otherwise. -/
instance instChartedSpace : ChartedSpace ClosedUpperHalfPlane ClosedUnitDisc where
  atlas := {e | ∃ (ζ : ℂ) (hζ : ‖ζ‖ = 1), e = cayleyChart ζ hζ}
  chartAt z := cayleyChart (chartCenter z) (norm_chartCenter z)
  mem_chart_source z := coe_ne_neg_chartCenter z
  chart_mem_atlas _ := ⟨_, _, rfl⟩

/-- The chart at `z` is the Cayley chart centered at `chartCenter z`. -/
theorem chartAt_eq (z : ClosedUnitDisc) :
    chartAt ClosedUpperHalfPlane z = cayleyChart (chartCenter z) (norm_chartCenter z) :=
  rfl

/-- The charts of the atlas are the Cayley charts. -/
theorem mem_atlas_iff {e : OpenPartialHomeomorph ClosedUnitDisc ClosedUpperHalfPlane} :
    e ∈ atlas ClosedUpperHalfPlane ClosedUnitDisc ↔
      ∃ (ζ : ℂ) (hζ : ‖ζ‖ = 1), e = cayleyChart ζ hζ :=
  Iff.rfl

/-! ### Transition maps -/

/-- A map of the closed upper half-plane that agrees, on an open set, with a function that is
complex analytic at each of its points in the ambient coordinate, is smooth up to the boundary
there and complex differentiable at the interior points. -/
private theorem contDiffOn_and_differentiableOn_of_contDiffAt
    {f : ClosedUpperHalfPlane → ClosedUpperHalfPlane} {s : Set ClosedUpperHalfPlane} {F : ℂ → ℂ}
    (hF : ∀ x ∈ s, ContDiffAt ℂ ∞ F x ∧ (f x : ℂ) = F x) :
    ContDiffOn ℝ ∞ (closedUpperHalfPlaneModel ∘ f ∘ closedUpperHalfPlaneModel.symm)
        (closedUpperHalfPlaneModel.symm ⁻¹' s ∩ range closedUpperHalfPlaneModel) ∧
      DifferentiableOn ℂ (closedUpperHalfPlaneModel ∘ f ∘ closedUpperHalfPlaneModel.symm)
        (closedUpperHalfPlaneModel.symm ⁻¹' s ∩ {z | 0 < z.im}) := by
  have hcoe : ∀ {z : ℂ}, 0 ≤ z.im → ((closedUpperHalfPlaneModel.symm z : ClosedUpperHalfPlane) : ℂ)
      = z := fun hz ↦ coe_closedUpperHalfPlaneModel_symm_of_im_nonneg hz
  have heq : ∀ {z : ℂ}, 0 ≤ z.im → closedUpperHalfPlaneModel.symm z ∈ s →
      (closedUpperHalfPlaneModel ∘ f ∘ closedUpperHalfPlaneModel.symm) z = F z := by
    intro z hz hs
    simpa [hcoe hz] using (hF _ hs).2
  have hat : ∀ {z : ℂ}, 0 ≤ z.im → closedUpperHalfPlaneModel.symm z ∈ s → ContDiffAt ℂ ∞ F z := by
    intro z hz hs
    simpa [hcoe hz] using (hF _ hs).1
  refine ⟨fun z hz ↦ ?_, fun z hz ↦ ?_⟩
  · have him : 0 ≤ z.im := by simpa using hz.2
    refine ((hat him hz.1).restrict_scalars ℝ).contDiffWithinAt.congr (fun y hy ↦ ?_) ?_
    · exact heq (by simpa using hy.2) hy.1
    · exact heq him hz.1
  · have him : 0 ≤ z.im := le_of_lt hz.2
    refine ((hat him hz.1).differentiableAt (by simp)).differentiableWithinAt.congr
      (fun y hy ↦ ?_) ?_
    · exact heq (le_of_lt hy.2) hy.1
    · exact heq him hz.1

/-- The transition map between two Cayley charts is the Möbius map
`w ↦ I (ζ' - u) / (ζ' + u)` with `u = ζ (I - w) / (I + w)`, which is analytic on the domain of
the transition. -/
private theorem transition_property (ζ ζ' : ℂ) (hζ : ‖ζ‖ = 1) (hζ' : ‖ζ'‖ = 1) :
    ContDiffOn ℝ ∞ (closedUpperHalfPlaneModel ∘ ((cayleyChart ζ hζ).symm ≫ₕ cayleyChart ζ' hζ') ∘
          closedUpperHalfPlaneModel.symm)
        (closedUpperHalfPlaneModel.symm ⁻¹' ((cayleyChart ζ hζ).symm ≫ₕ cayleyChart ζ' hζ').source ∩
          range closedUpperHalfPlaneModel) ∧
      DifferentiableOn ℂ (closedUpperHalfPlaneModel ∘
          ((cayleyChart ζ hζ).symm ≫ₕ cayleyChart ζ' hζ') ∘ closedUpperHalfPlaneModel.symm)
        (closedUpperHalfPlaneModel.symm ⁻¹' ((cayleyChart ζ hζ).symm ≫ₕ cayleyChart ζ' hζ').source ∩
          {z | 0 < z.im}) := by
  refine contDiffOn_and_differentiableOn_of_contDiffAt
    (F := fun w ↦ I * (ζ' - ζ * (I - w) / (I + w)) / (ζ' + ζ * (I - w) / (I + w))) ?_
  intro w hw
  simp only [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
    cayleyChart_target, univ_inter, mem_preimage, cayleyChart_source, mem_ofPred_eq,
    coe_cayleyChart_symm_apply] at hw
  refine ⟨?_, rfl⟩
  have hw0 := add_comm I (w : ℂ) ▸ add_I_ne_zero_of_im_nonneg w.2
  have hu : ContDiffAt ℂ ∞ (fun w : ℂ ↦ ζ * (I - w) / (I + w)) w :=
    (contDiffAt_const.mul (contDiffAt_const.sub contDiffAt_id)).div
      (contDiffAt_const.add contDiffAt_id) hw0
  exact (contDiffAt_const.mul (contDiffAt_const.sub hu)).div (contDiffAt_const.add hu)
    fun h ↦ hw (by linear_combination h)

/-- The transition map between two Cayley charts lies in the bordered holomorphic groupoid. -/
theorem cayleyChart_symm_trans_mem_borderedHolomorphicGroupoid (ζ ζ' : ℂ) (hζ : ‖ζ‖ = 1)
    (hζ' : ‖ζ'‖ = 1) :
    (cayleyChart ζ hζ).symm ≫ₕ cayleyChart ζ' hζ' ∈ borderedHolomorphicGroupoid := by
  have h₁ := transition_property ζ ζ' hζ hζ'
  have h₂ := transition_property ζ' ζ hζ' hζ
  have hsymm : ((cayleyChart ζ hζ).symm ≫ₕ cayleyChart ζ' hζ').symm =
      (cayleyChart ζ' hζ').symm ≫ₕ cayleyChart ζ hζ := by
    rw [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm, OpenPartialHomeomorph.symm_symm]
  refine mem_borderedHolomorphicGroupoid_iff.2 ⟨⟨h₁.1, ?_⟩, h₁.2, ?_⟩
  · rw [hsymm, ← OpenPartialHomeomorph.symm_source, hsymm]
    exact h₂.1
  · rw [hsymm, ← OpenPartialHomeomorph.symm_source, hsymm]
    exact h₂.2

/-- The closed unit disc, with its Cayley charts, is a Riemann surface with boundary. -/
instance instHasGroupoid : HasGroupoid ClosedUnitDisc borderedHolomorphicGroupoid where
  compatible := by
    rintro _ _ ⟨ζ, hζ, rfl⟩ ⟨ζ', hζ', rfl⟩
    exact cayleyChart_symm_trans_mem_borderedHolomorphicGroupoid ζ ζ' hζ hζ'

/-! ### Interior and boundary -/

/-- The interior of the closed unit disc is the open unit disc. -/
theorem mem_borderedInterior_iff {z : ClosedUnitDisc} :
    z ∈ borderedInterior ClosedUnitDisc ↔ ‖(z : ℂ)‖ < 1 := by
  rw [mem_borderedInterior_iff_im_chartAt_pos, chartAt_eq,
    im_cayleyChart_pos_iff (coe_ne_neg_chartCenter z)]

/-- The interior of the closed unit disc is the open unit disc. -/
theorem coe_borderedInterior :
    (borderedInterior ClosedUnitDisc : Set ClosedUnitDisc) = {z : ClosedUnitDisc | ‖(z : ℂ)‖ < 1} :=
  Set.ext fun _ ↦ mem_borderedInterior_iff

/-- The complement of the interior of the closed unit disc is its boundary circle, the boundary
along which `TauCeti.DoubleAlong` doubles the disc to the Riemann sphere. -/
theorem compl_borderedInterior :
    (borderedInterior ClosedUnitDisc : Set ClosedUnitDisc)ᶜ = DoubleAlong.discBoundary := by
  ext z
  refine Iff.trans ?_ (DoubleAlong.mem_discBoundary (z := z)).symm
  rw [mem_compl_iff, SetLike.mem_coe, mem_borderedInterior_iff, not_lt]
  exact ⟨fun h ↦ le_antisymm (norm_coe_le_one z) h, fun h ↦ h.ge⟩

/-- The inclusion of the interior of the closed unit disc into `ℂ` is analytic for the complex
structure induced by the Cayley charts. So the induced complex structure on the open disc is the
standard one. -/
theorem contMDiff_coe_borderedInterior :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω
      (fun z : borderedInterior ClosedUnitDisc ↦ ((z : ClosedUnitDisc) : ℂ)) := by
  intro x
  refine contMDiffAt_iff.2 ⟨(continuous_coe.comp continuous_subtype_val).continuousAt, ?_⟩
  simp only [mfld_simps]
  refine ContDiffAt.contDiffWithinAt ?_
  set w := chartAt ℂ x x
  have hw : w ∈ (chartAt ℂ x).target := mem_chart_target ℂ x
  have himw : 0 < w.im := by
    rw [chartAt_borderedInterior_target] at hw
    exact hw.2
  have hev : (fun v ↦ (((chartAt ℂ x).symm v : ClosedUnitDisc) : ℂ)) =ᶠ[𝓝 w]
      fun v ↦ chartCenter (x : ClosedUnitDisc) * (I - v) / (I + v) := by
    filter_upwards [(chartAt ℂ x).open_target.mem_nhds hw] with v hv
    rw [chartAt_borderedInterior_symm_apply x hv, chartAt_eq, coe_cayleyChart_symm_apply]
    have hvim : 0 ≤ v.im := by
      rw [chartAt_borderedInterior_target] at hv
      exact hv.2.le
    rw [coe_closedUpperHalfPlaneModel_symm_of_im_nonneg hvim]
  refine ContDiffAt.congr_of_eventuallyEq ?_ hev
  exact (contDiffAt_const.mul (contDiffAt_const.sub contDiffAt_id)).div
    (contDiffAt_const.add contDiffAt_id) (add_comm I w ▸ add_I_ne_zero_of_im_nonneg himw.le)

end ClosedUnitDisc

end TauCeti
