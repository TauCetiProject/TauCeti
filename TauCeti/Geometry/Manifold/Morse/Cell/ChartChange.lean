/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Disk.Annulus
public import TauCeti.Geometry.Manifold.Morse.Cell.Comparison
public import TauCeti.Topology.Homotopy.Homotopic.Rel

/-!
# Changing the charts of a cell attachment

Passing a critical level `c` of a Morse function attaches one cell to the lower sublevel
`M_{c-ε} = {f ≤ c - ε}` at each critical point, but the attaching maps depend on the chosen
normal-form charts. Let `φ₀ i` and `φ₁ i` be two families of charts with values in `ℝⁿ`, in which
`f = c - Σ_{j < k i} yⱼ² + Σ_{j ≥ k i} yⱼ²` and whose targets contain the closed ball of radius
`√ε`. They have characteristic maps `χ₀ i, χ₁ i : (D^{k i}, ∂D^{k i}) → (M_{c+ε}, M_{c-ε})` and
attachment spaces `M_{c-ε} ∪_{α₀} ⨆ᵢ D^{k i}` and `M_{c-ε} ∪_{α₁} ⨆ᵢ D^{k i}`
(`TauCeti.morseCellAttachment`). Suppose given maps of discs `h i : D^{k i} → D^{k i}` (for
instance orthogonal maps) and homotopies of pairs `K i : χ₁ i ≃ χ₀ i ∘ h i`, that is, homotopies
which keep the boundary sphere in `M_{c-ε}` at all times; we write `K i (t, w)` for its value at
time `t` and point `w` of the disc. On the boundary sphere it is a homotopy from the attaching map
`α₁ i` to `α₀ i ∘ h i`.

Following Milnor, the comparison `E_H : M_{c-ε} ∪_{α₁} ⨆ᵢ D^{k i} → M_{c-ε} ∪_{α₀} ⨆ᵢ D^{k i}`
(`TauCeti.morseChartChange`) is the identity on the lower sublevel, sends a point `x` of the
`i`-th disc with `‖x‖ ≤ 1/2` to the point `h i (2x)` of the `i`-th disc of the target, and sends a
point `x` with `1/2 ≤ ‖x‖` to the point `K i (2 - 2‖x‖, x / ‖x‖)` of the lower sublevel. The two
formulas agree on the seam `‖x‖ = 1/2` because `K i` ends at `χ₀ i ∘ h i`, and on the boundary
sphere the formula is the attaching map `α₁ i`, because `K i` starts at `χ₁ i`.

Composed with the handle-to-cell comparison `Φ₀` of the charts `φ₀` (`TauCeti.morseCellComparison`),
`E_H` reads on the `i`-th disc as `K i` restricted to the cup `D × {1} ∪ ∂D × [0, 1]` of the
cylinder `D × [0, 1]`, flattened onto the disc. The straight-line homotopy in the convex cylinder
between this flattening and the bottom disc `D × {0}` fixes the boundary sphere, so
`Φ₀ ∘ E_H` is homotopic to `Φ₁` relative to the lower sublevel
(`TauCeti.homotopicRel_morseChartChange_comp_morseCellComparison`). Hence `E_H ≃ g₀ ∘ Φ₁` relative
to the lower sublevel for every left inverse `g₀` of `Φ₀`. If `g₀` and `g₁` are left inverses of
`Φ₀` and `Φ₁` which are homotopy inverses relative to the images of `Φ₀` and `Φ₁`, then `E_H` is a
homotopy equivalence relative to the lower sublevel with homotopy inverse `g₁ ∘ Φ₀`
(`TauCeti.relHomotopyInverse_morseChartChange_of_leftInverse`). Milnor's cell attachment theorem
provides such `g₀` and `g₁` when `f` is smooth, both families consist of finitely many smooth charts
with pairwise disjoint sources whose targets contain the closed ball of radius `√(2ε)`, the band
`f⁻¹[c - ε, c + ε]` is compact and its critical points lie in the charts of each family
(`TauCeti.exists_relHomotopyInverse_morseChartChange`).

The charts may have any indices; for a `0`-cell the disc is a point of norm `0`, on which `E_H` is
`h i`, the identity of the point.

## Main definitions

* `TauCeti.morseChartChange`: Milnor's comparison `E_H` between the attachment spaces of two
  families of normal-form charts, built from homotopies of pairs between their characteristic maps.

## Main results

* `TauCeti.morseCellAttachmentIncl_comp_morseChartChange`: `E_H` is the identity on the lower
  sublevel.
* `TauCeti.morseChartChange_morseCellAttachmentCell_of_norm_le`,
  `TauCeti.morseChartChange_morseCellAttachmentCell_of_le_norm`: the formulas for `E_H` on the
  inner half-disc and on the outer annulus.
* `TauCeti.homotopicRel_morseChartChange_comp_morseCellComparison`: `Φ₀ ∘ E_H ≃ Φ₁` relative to
  the lower sublevel.
* `TauCeti.homotopicRel_morseChartChange_of_leftInverse`: `E_H ≃ g₀ ∘ Φ₁` relative to the lower
  sublevel for every left inverse `g₀` of `Φ₀`.
* `TauCeti.relHomotopyInverse_morseChartChange_of_leftInverse`: `E_H` is a homotopy equivalence
  relative to the lower sublevel, with homotopy inverse `g₁ ∘ Φ₀`, given relative homotopy inverses
  `g₀`, `g₁` of `Φ₀`, `Φ₁`.
* `TauCeti.exists_relHomotopyInverse_morseChartChange`: for smooth charts covering the critical
  points of a compact band, `E_H` is a homotopy equivalence relative to the lower sublevel.

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  Lemma 3.6 and Remark 3.3.
-/

public section

noncomputable section

open Function Set Metric Topology CategoryTheory Limits
open scoped ContDiff Manifold

universe u

namespace TauCeti

section Cup

open unitInterval

variable {E : Type*} [NormedAddCommGroup E]

/-- The time coordinate of the flattening of the cup `D × {1} ∪ ∂D × [0, 1]` onto the disc:
`1` on the inner half-disc and `2 - 2‖x‖` on the outer annulus. -/
private def cupTime (x : E) : ℝ :=
  2 - 2 * max ‖x‖ 2⁻¹

private theorem continuous_cupTime : Continuous (cupTime : E → ℝ) := by
  unfold cupTime
  fun_prop

private theorem cupTime_of_le_norm {x : E} (hx : 2⁻¹ ≤ ‖x‖) : cupTime x = 2 - 2 * ‖x‖ := by
  rw [cupTime, max_eq_left hx]

private theorem cupTime_of_norm_le {x : E} (hx : ‖x‖ ≤ 2⁻¹) : cupTime x = 1 := by
  rw [cupTime, max_eq_right hx]
  norm_num

private theorem cupTime_of_norm_eq_one {x : E} (hx : ‖x‖ = 1) : cupTime x = 0 := by
  rw [cupTime_of_le_norm (by rw [hx]; norm_num), hx]
  norm_num

private theorem cupTime_mem {x : E} (hx : ‖x‖ ≤ 1) : cupTime x ∈ I := by
  rw [cupTime]
  constructor
  · linarith [max_le hx (by norm_num : (2⁻¹ : ℝ) ≤ 1)]
  · linarith [le_max_right ‖x‖ 2⁻¹]

variable [NormedSpace ℝ E]

/-- The point coordinate of the flattening of the cup `D × {1} ∪ ∂D × [0, 1]` onto the disc:
`x ↦ 2x` on the inner half-disc and `x ↦ x / ‖x‖` on the outer annulus, that is, twice the radial
retraction onto the ball of radius `1/2`. -/
private def cupPoint (x : E) : E :=
  (2 : ℝ) • radialRetraction 2⁻¹ x

private theorem norm_cupPoint (x : E) : ‖cupPoint x‖ = 2 * min ‖x‖ 2⁻¹ := by
  rw [cupPoint, norm_smul, norm_radialRetraction (by norm_num), Real.norm_two]

private theorem cupPoint_of_le_norm {x : E} (hx : 2⁻¹ ≤ ‖x‖) : cupPoint x = ‖x‖⁻¹ • x := by
  rw [cupPoint, radialRetraction_of_le_norm hx, smul_smul, mul_div_assoc',
    mul_inv_cancel₀ two_ne_zero, one_div]

private theorem norm_cupPoint_of_le_norm {x : E} (hx : 2⁻¹ ≤ ‖x‖) : ‖cupPoint x‖ = 1 := by
  rw [norm_cupPoint, min_eq_right hx, mul_inv_cancel₀ two_ne_zero]

private theorem cupPoint_inv_two_smul {x : E} (hx : ‖x‖ ≤ 1) : cupPoint ((2⁻¹ : ℝ) • x) = x := by
  have h : ‖(2⁻¹ : ℝ) • x‖ ≤ 2⁻¹ := by
    rw [norm_smul, Real.norm_of_nonneg (by norm_num)]
    linarith
  rw [cupPoint, radialRetraction_of_norm_le h, smul_smul, mul_inv_cancel₀ two_ne_zero, one_smul]

private theorem cupPoint_of_norm_eq_one {x : E} (hx : ‖x‖ = 1) : cupPoint x = x := by
  rw [cupPoint_of_le_norm (by rw [hx]; norm_num), hx, inv_one, one_smul]

variable {k : ℕ}

/-- The flattening of the cup onto the disc `D^k`, point coordinate. -/
private def diskCup (w : TopCat.disk.{u} k) : TopCat.disk.{u} k :=
  ULift.up ⟨cupPoint (w.down : EuclideanSpace ℝ (Fin k)), mem_closedBall_zero_iff.2 <| by
    rw [norm_cupPoint]
    linarith [min_le_right ‖(w.down : EuclideanSpace ℝ (Fin k))‖ 2⁻¹]⟩

/-- The flattening of the cup onto the disc `D^k`, time coordinate. -/
private def diskCupTime (w : TopCat.disk.{u} k) : I :=
  ⟨cupTime (w.down : EuclideanSpace ℝ (Fin k)), cupTime_mem (mem_closedBall_zero_iff.1 w.down.2)⟩

private theorem continuous_diskCup : Continuous (diskCup.{u} (k := k)) :=
  continuous_uliftUp.comp ((((continuous_const.radialRetraction (fun _ ↦ by norm_num)
    continuous_subtype_val).const_smul (2 : ℝ)).comp continuous_uliftDown).subtype_mk _)

private theorem coe_diskCup (w : TopCat.disk.{u} k) :
    ((diskCup w).down : EuclideanSpace ℝ (Fin k)) = cupPoint (w.down : EuclideanSpace ℝ (Fin k)) :=
  (rfl)

private theorem diskCupTime_of_norm_le {w : TopCat.disk.{u} k}
    (hw : ‖(w.down : EuclideanSpace ℝ (Fin k))‖ ≤ 2⁻¹) : diskCupTime w = 1 :=
  Subtype.ext (cupTime_of_norm_le hw)

/-- The straight-line homotopy in the cylinder `D^k × [0, 1]` from the flattened cup to the bottom
disc, point coordinate: `(1 - s) • cupPoint w + s • w`. -/
private def diskCupHomotopy (w : TopCat.disk.{u} k) (s : I) : TopCat.disk.{u} k :=
  ULift.up ⟨(1 - (s : ℝ)) • cupPoint (w.down : EuclideanSpace ℝ (Fin k)) +
      (s : ℝ) • (w.down : EuclideanSpace ℝ (Fin k)),
    convex_closedBall (0 : EuclideanSpace ℝ (Fin k)) 1
      (diskCup w).down.2 w.down.2 (sub_nonneg.2 s.2.2) s.2.1
      (sub_add_cancel 1 _)⟩

/-- The straight-line homotopy in the cylinder `D^k × [0, 1]` from the flattened cup to the bottom
disc, time coordinate: `(1 - s) * cupTime w`. -/
private def diskCupHomotopyTime (w : TopCat.disk.{u} k) (s : I) : I :=
  ⟨(1 - (s : ℝ)) * cupTime (w.down : EuclideanSpace ℝ (Fin k)),
    unitInterval.mul_mem ⟨sub_nonneg.2 s.2.2, sub_le_self _ s.2.1⟩ (diskCupTime w).2⟩

private theorem continuous_diskCupHomotopy :
    Continuous fun p : TopCat.disk.{u} k × I ↦ diskCupHomotopy p.1 p.2 := by
  have hw : Continuous fun p : TopCat.disk.{u} k × I ↦
      ((p.1.down : EuclideanSpace ℝ (Fin k))) :=
    (continuous_subtype_val.comp continuous_uliftDown).comp continuous_fst
  have hs : Continuous fun p : TopCat.disk.{u} k × I ↦ ((p.2 : ℝ)) :=
    continuous_subtype_val.comp continuous_snd
  have hcup : Continuous fun p : TopCat.disk.{u} k × I ↦
      cupPoint (p.1.down : EuclideanSpace ℝ (Fin k)) :=
    (continuous_subtype_val.comp (continuous_uliftDown.comp continuous_diskCup)).comp continuous_fst
  exact continuous_uliftUp.comp ((((continuous_const.sub hs).smul hcup).add
    (hs.smul hw)).subtype_mk _)

private theorem continuous_diskCupHomotopyTime :
    Continuous fun p : TopCat.disk.{u} k × I ↦ diskCupHomotopyTime p.1 p.2 := by
  have hw : Continuous fun p : TopCat.disk.{u} k × I ↦
      ((p.1.down : EuclideanSpace ℝ (Fin k))) :=
    (continuous_subtype_val.comp continuous_uliftDown).comp continuous_fst
  have hs : Continuous fun p : TopCat.disk.{u} k × I ↦ ((p.2 : ℝ)) :=
    continuous_subtype_val.comp continuous_snd
  exact ((continuous_const.sub hs).mul (continuous_cupTime.comp hw)).subtype_mk _

private theorem diskCupHomotopy_zero (w : TopCat.disk.{u} k) : diskCupHomotopy w 0 = diskCup w :=
  ULift.ext (Subtype.ext (by simp [diskCupHomotopy, coe_diskCup]))

private theorem diskCupHomotopyTime_zero (w : TopCat.disk.{u} k) :
    diskCupHomotopyTime w 0 = diskCupTime w :=
  Subtype.ext (by simp [diskCupHomotopyTime, diskCupTime])

private theorem diskCupHomotopy_one (w : TopCat.disk.{u} k) : diskCupHomotopy w 1 = w :=
  ULift.ext (Subtype.ext (by simp [diskCupHomotopy]))

private theorem diskCupHomotopyTime_one (w : TopCat.disk.{u} k) : diskCupHomotopyTime w 1 = 0 :=
  Subtype.ext (by simp [diskCupHomotopyTime])

private theorem diskCupHomotopy_of_norm_eq_one {w : TopCat.disk.{u} k}
    (hw : ‖(w.down : EuclideanSpace ℝ (Fin k))‖ = 1) (s : I) : diskCupHomotopy w s = w :=
  ULift.ext (Subtype.ext (by
    simp only [diskCupHomotopy, cupPoint_of_norm_eq_one hw, ← add_smul, sub_add_cancel,
      one_smul]))

private theorem diskCupHomotopyTime_of_norm_eq_one {w : TopCat.disk.{u} k}
    (hw : ‖(w.down : EuclideanSpace ℝ (Fin k))‖ = 1) (s : I) : diskCupHomotopyTime w s = 0 :=
  Subtype.ext (by simp [diskCupHomotopyTime, cupTime_of_norm_eq_one hw])

end Cup

section ChartChange

open unitInterval

variable {M : Type u} [TopologicalSpace M] {n : ℕ} {ι : Type u} {f : M → ℝ} {c ε : ℝ}
  (φ₀ φ₁ : ι → OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))) (k : ι → ℕ)
  (hk : ∀ i, k i ≤ n) (hε : 0 < ε)
  (hball₀ : ∀ i, closedBall 0 √ε ⊆ (φ₀ i).target)
  (hball₁ : ∀ i, closedBall 0 √ε ⊆ (φ₁ i).target)
  (hf₀ : ∀ i, ∀ y ∈ (φ₀ i).source, f y = c + ∑ j, (if j.val < k i then -1 else 1) * φ₀ i y j ^ 2)
  (hf₁ : ∀ i, ∀ y ∈ (φ₁ i).source, f y = c + ∑ j, (if j.val < k i then -1 else 1) * φ₁ i y j ^ 2)
  (h : ∀ i, TopCat.disk.{u} (k i) ⟶ TopCat.disk.{u} (k i))
  (K : ∀ i, ((φ₁ i).morseCharacteristicMap (hk i) hε.le (hball₁ i) (hf₁ i)).hom.Homotopy
    (((φ₀ i).morseCharacteristicMap (hk i) hε.le (hball₀ i) (hf₀ i)).hom.comp (h i).hom))
  (hK : ∀ i t (w : TopCat.disk.{u} (k i)), ‖(w.down : EuclideanSpace ℝ (Fin (k i)))‖ = 1 →
    f (K i (t, w)) ≤ c - ε)

include hK in
/-- On the seam, where `K i` ends at `χ₀ i ∘ h i` on the boundary sphere, the cell of `φ₀ i` meets
the lower sublevel. -/
private theorem morseCellAttachmentCell_eq_morseCellAttachmentIncl (i : ι)
    (v : TopCat.disk.{u} (k i)) (hv : ‖(v.down : EuclideanSpace ℝ (Fin (k i)))‖ = 1)
    (z : {x | f x ≤ c - ε}) (hz : (z : M) = K i (1, v)) :
    morseCellAttachmentCell φ₀ k hk hε.le hball₀ hf₀ i (h i v) =
      morseCellAttachmentIncl φ₀ k hk hε.le hball₀ hf₀ z := by
  have hKv : (K i (1, v) : M) =
      (φ₀ i).morseCharacteristicMap (hk i) hε.le (hball₀ i) (hf₀ i) (h i v) := by
    rw [(K i).apply_one, ContinuousMap.comp_apply]
  have hmem : h i v ∈ (φ₀ i).morseCharacteristicMap (hk i) hε.le (hball₀ i) (hf₀ i) ⁻¹'
      {x | f x ≤ c - ε} := by
    rw [mem_preimage, mem_ofPred_eq, ← hKv]
    exact hK i 1 v hv
  rw [OpenPartialHomeomorph.preimage_morseCharacteristicMap_sublevel (hball₀ i) (hf₀ i) (hk i) hε]
    at hmem
  obtain ⟨s, hs⟩ := hmem
  rw [← hs, ← ConcreteCategory.comp_apply,
    ← morseAttachingMap_comp_morseCellAttachmentIncl φ₀ k hk hball₀ hf₀ hε.le,
    ConcreteCategory.comp_apply]
  refine congrArg _ (Subtype.ext ?_)
  rw [hz, hKv, ← hs]
  have hsq := ConcreteCategory.congr_hom
    ((φ₀ i).morseAttachingMap_comp_sublevelInclusion (hball₀ i) (hf₀ i) (hk i) hε.le) s
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, TopCat.ofHom_apply] at hsq
  rw [← hsq, coe_sublevelInclusion_apply]

/-- The disc part of `TauCeti.morseChartChange`: the map `x ↦ h i (2x)` into the cell of `φ₀ i` on
the disc of radius `1/2`, glued to `K i` read in the annulus coordinates of the annulus
`1/2 ≤ ‖x‖`. The pieces agree on the seam `‖x‖ = 1/2` because `K i` ends at `χ₀ i ∘ h i`. -/
private def morseChartChangeCellFun (i : ι) :
    C(TopCat.disk.{u} (k i), morseCellAttachment φ₀ k hk hε.le hball₀ hf₀) :=
  (TopCat.diskGlue (P := Unit) (by norm_num : (0 : ℝ) < 2⁻¹)
    ⟨fun p ↦ morseCellAttachmentCell φ₀ k hk hε.le hball₀ hf₀ i
        (h i (diskCup (ULift.up ⟨p.2.1, closedBall_subset_closedBall (by norm_num) p.2.2⟩))),
      (morseCellAttachmentCell φ₀ k hk hε.le hball₀ hf₀ i).hom.continuous.comp
        ((h i).hom.continuous.comp (continuous_diskCup.comp (continuous_uliftUp.comp
          ((continuous_subtype_val.comp continuous_snd).subtype_mk _))))⟩
    ⟨fun p ↦ morseCellAttachmentIncl φ₀ k hk hε.le hball₀ hf₀
        ⟨K i (σ p.2.1, TopCat.diskBoundaryInclusion (k i) p.2.2),
          hK i _ _ (TopCat.norm_diskBoundaryInclusion _)⟩,
      (morseCellAttachmentIncl φ₀ k hk hε.le hball₀ hf₀).hom.continuous.comp
        ((continuous_subtype_val.comp ((K i).continuous.comp
          ((continuous_symm.comp (continuous_fst.comp continuous_snd)).prodMk
            ((TopCat.diskBoundaryInclusion (k i)).hom.continuous.comp
              (continuous_snd.comp continuous_snd))))).subtype_mk _)⟩
    fun _ θ ↦ by
      -- The flattened cup sends the point `θ / 2` of the seam to `θ`.
      have hθ : diskCup (ULift.up ⟨(2⁻¹ : ℝ) • θ.down.1, closedBall_subset_closedBall
          (by norm_num) (TopCat.smul_diskBoundary_mem_closedBall (by norm_num) θ)⟩) =
          TopCat.diskBoundaryInclusion (k i) θ := by
        refine ULift.ext (Subtype.ext ((coe_diskCup _).trans ((cupPoint_inv_two_smul
          (mem_sphere_zero_iff_norm.1 θ.down.2).le).trans
            (TopCat.coe_diskBoundaryInclusion_apply_down _ _).symm)))
      simp only [ContinuousMap.coe_mk, symm_zero, hθ]
      exact (morseCellAttachmentCell_eq_morseCellAttachmentIncl φ₀ φ₁ k hk hε hball₀ hball₁ hf₀
        hf₁ h K hK i _ (TopCat.norm_diskBoundaryInclusion θ) _ rfl).symm).curry ()

private theorem morseChartChangeCellFun_of_norm_le (i : ι) {w : TopCat.disk.{u} (k i)}
    (hw : ‖(w.down : EuclideanSpace ℝ (Fin (k i)))‖ ≤ 2⁻¹) :
    morseChartChangeCellFun φ₀ φ₁ k hk hε hball₀ hball₁ hf₀ hf₁ h K hK i w =
      morseCellAttachmentCell φ₀ k hk hε.le hball₀ hf₀ i (h i (diskCup w)) := by
  rw [morseChartChangeCellFun, ContinuousMap.curry_apply,
    TopCat.diskGlue_apply_of_norm_le _ _ _ _ _ hw]
  rfl

private theorem morseChartChangeCellFun_of_le_norm (i : ι) {w : TopCat.disk.{u} (k i)}
    (hw : 2⁻¹ ≤ ‖(w.down : EuclideanSpace ℝ (Fin (k i)))‖) :
    morseChartChangeCellFun φ₀ φ₁ k hk hε hball₀ hball₁ hf₀ hf₁ h K hK i w =
      morseCellAttachmentIncl φ₀ k hk hε.le hball₀ hf₀
        ⟨K i (σ (TopCat.annulusParam 2⁻¹ w), TopCat.diskBoundaryInclusion (k i)
          (TopCat.annulusDir (by norm_num) ⟨w, hw⟩)),
          hK i _ _ (TopCat.norm_diskBoundaryInclusion _)⟩ := by
  rw [morseChartChangeCellFun, ContinuousMap.curry_apply,
    TopCat.diskGlue_apply_of_le_norm _ _ _ _ _ hw]
  rfl

/-- The disc part of `TauCeti.morseChartChange`. -/
private def morseChartChangeCell (i : ι) :
    TopCat.disk.{u} (k i) ⟶ morseCellAttachment φ₀ k hk hε.le hball₀ hf₀ :=
  TopCat.ofHom (morseChartChangeCellFun φ₀ φ₁ k hk hε hball₀ hball₁ hf₀ hf₁ h K hK i)

private theorem morseChartChangeCell_apply (i : ι) (w : TopCat.disk.{u} (k i)) :
    morseChartChangeCell φ₀ φ₁ k hk hε hball₀ hball₁ hf₀ hf₁ h K hK i w =
      morseChartChangeCellFun φ₀ φ₁ k hk hε hball₀ hball₁ hf₀ hf₁ h K hK i w :=
  (rfl)

/-- On the boundary sphere, where `K i` starts at `χ₁ i`, the disc part of
`TauCeti.morseChartChange` is the attaching map of `φ₁ i`. -/
private theorem morseAttachingMap_comp_morseCellAttachmentIncl_eq (i : ι) :
    (φ₁ i).morseAttachingMap (hk i) hε.le (hball₁ i) (hf₁ i) ≫
        morseCellAttachmentIncl φ₀ k hk hε.le hball₀ hf₀ =
      TopCat.diskBoundaryInclusion (k i) ≫
        morseChartChangeCell φ₀ φ₁ k hk hε hball₀ hball₁ hf₀ hf₁ h K hK i := by
  ext s
  have hw :
      2⁻¹ ≤ ‖((TopCat.diskBoundaryInclusion (k i) s).down : EuclideanSpace ℝ (Fin (k i)))‖ := by
    rw [TopCat.norm_diskBoundaryInclusion]
    norm_num
  rw [ConcreteCategory.comp_apply (TopCat.diskBoundaryInclusion (k i)), morseChartChangeCell_apply,
    morseChartChangeCellFun_of_le_norm (hw := hw), ConcreteCategory.comp_apply]
  refine congrArg _ (Subtype.ext ?_)
  simp only [TopCat.annulusParam_of_norm_eq_one (by norm_num : (2⁻¹ : ℝ) < 1)
    (TopCat.norm_diskBoundaryInclusion s), symm_one, TopCat.annulusDir_diskBoundaryInclusion,
    (K i).apply_zero]
  have hsq := ConcreteCategory.congr_hom
    ((φ₁ i).morseAttachingMap_comp_sublevelInclusion (hball₁ i) (hf₁ i) (hk i) hε.le) s
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, TopCat.ofHom_apply] at hsq
  rw [← hsq, coe_sublevelInclusion_apply]

/-- **Milnor's change-of-chart comparison.** Let `φ₀ i` and `φ₁ i` be two families of charts with
values in `ℝⁿ`, in which `f = c - Σ_{j < k i} yⱼ² + Σ_{j ≥ k i} yⱼ²` and whose targets contain the
closed ball of radius `√ε`, let `h i : D^{k i} → D^{k i}` be maps of discs, and let
`K i : χ₁ i ≃ χ₀ i ∘ h i` be homotopies from the characteristic map of `φ₁ i` to that of `φ₀ i`
after `h i`, keeping the boundary sphere in the lower sublevel `M_{c-ε}`. The comparison
`E_H : M_{c-ε} ∪_{α₁} ⨆ᵢ D^{k i} → M_{c-ε} ∪_{α₀} ⨆ᵢ D^{k i}` is the identity on `M_{c-ε}`, sends
`x` in the `i`-th disc with `‖x‖ ≤ 1/2` to the point `h i (2x)` of the `i`-th disc, and sends `x`
with `1/2 ≤ ‖x‖` to the point `K i (2 - 2‖x‖, x / ‖x‖)` of `M_{c-ε}`. -/
def morseChartChange :
    morseCellAttachment φ₁ k hk hε.le hball₁ hf₁ ⟶ morseCellAttachment φ₀ k hk hε.le hball₀ hf₀ :=
  morseCellAttachmentDesc φ₁ k hk hε.le hball₁ hf₁
    (morseCellAttachmentIncl φ₀ k hk hε.le hball₀ hf₀)
    (morseChartChangeCell φ₀ φ₁ k hk hε hball₀ hball₁ hf₀ hf₁ h K hK)
    (morseAttachingMap_comp_morseCellAttachmentIncl_eq φ₀ φ₁ k hk hε hball₀ hball₁ hf₀ hf₁ h K hK)

/-- The change-of-chart comparison is the identity on the lower sublevel. -/
@[reassoc (attr := simp)]
theorem morseCellAttachmentIncl_comp_morseChartChange :
    morseCellAttachmentIncl φ₁ k hk hε.le hball₁ hf₁ ≫
        morseChartChange φ₀ φ₁ k hk hε hball₀ hball₁ hf₀ hf₁ h K hK =
      morseCellAttachmentIncl φ₀ k hk hε.le hball₀ hf₀ :=
  morseCellAttachmentIncl_desc _ _ _ _ _ _ _ _ _

/-- The change-of-chart comparison sends a point of the lower sublevel to itself. -/
@[simp]
theorem morseChartChange_morseCellAttachmentIncl (x : {x | f x ≤ c - ε}) :
    morseChartChange φ₀ φ₁ k hk hε hball₀ hball₁ hf₀ hf₁ h K hK
        (morseCellAttachmentIncl φ₁ k hk hε.le hball₁ hf₁ x) =
      morseCellAttachmentIncl φ₀ k hk hε.le hball₀ hf₀ x := by
  rw [← ConcreteCategory.comp_apply, morseCellAttachmentIncl_comp_morseChartChange]

private theorem coe_morseCellComparison_morseChartChange_incl (x : {x | f x ≤ c - ε}) :
    (morseCellComparison φ₀ k hk hε.le hball₀ hf₀
        (morseChartChange φ₀ φ₁ k hk hε hball₀ hball₁ hf₀ hf₁ h K hK
          (morseCellAttachmentIncl φ₁ k hk hε.le hball₁ hf₁ x)) : M) = x := by
  rw [morseChartChange_morseCellAttachmentIncl, coe_morseCellComparison_morseCellAttachmentIncl]

private theorem morseChartChange_morseCellAttachmentCell (i : ι) (w : TopCat.disk.{u} (k i)) :
    morseChartChange φ₀ φ₁ k hk hε hball₀ hball₁ hf₀ hf₁ h K hK
        (morseCellAttachmentCell φ₁ k hk hε.le hball₁ hf₁ i w) =
      morseChartChangeCellFun φ₀ φ₁ k hk hε hball₀ hball₁ hf₀ hf₁ h K hK i w := by
  rw [← ConcreteCategory.comp_apply, morseChartChange, morseCellAttachmentCell_desc,
    morseChartChangeCell_apply]

/-- On the inner half-disc `‖w‖ ≤ 1/2` of the `i`-th cell, the change-of-chart comparison is
`w ↦ h i (2w)`, followed by the `i`-th cell of the target. -/
theorem morseChartChange_morseCellAttachmentCell_of_norm_le (i : ι) {w v : TopCat.disk.{u} (k i)}
    (hw : ‖(w.down : EuclideanSpace ℝ (Fin (k i)))‖ ≤ 2⁻¹)
    (hv : (v.down : EuclideanSpace ℝ (Fin (k i))) = (2 : ℝ) • (w.down : EuclideanSpace ℝ _)) :
    morseChartChange φ₀ φ₁ k hk hε hball₀ hball₁ hf₀ hf₁ h K hK
        (morseCellAttachmentCell φ₁ k hk hε.le hball₁ hf₁ i w) =
      morseCellAttachmentCell φ₀ k hk hε.le hball₀ hf₀ i (h i v) := by
  rw [morseChartChange_morseCellAttachmentCell, morseChartChangeCellFun_of_norm_le (hw := hw)]
  congr 2
  exact ULift.ext (Subtype.ext
    ((congrArg ((2 : ℝ) • ·) (radialRetraction_of_norm_le hw)).trans hv.symm))

/-- On the outer annulus `1/2 ≤ ‖w‖` of the `i`-th cell, the change-of-chart comparison is
`w ↦ K i (2 - 2‖w‖, w / ‖w‖)`, a point of the lower sublevel. -/
theorem morseChartChange_morseCellAttachmentCell_of_le_norm (i : ι) {w v : TopCat.disk.{u} (k i)}
    {t : I} (hw : 2⁻¹ ≤ ‖(w.down : EuclideanSpace ℝ (Fin (k i)))‖)
    (ht : (t : ℝ) = 2 - 2 * ‖(w.down : EuclideanSpace ℝ (Fin (k i)))‖)
    (hv : (v.down : EuclideanSpace ℝ (Fin (k i))) =
      ‖(w.down : EuclideanSpace ℝ (Fin (k i)))‖⁻¹ • (w.down : EuclideanSpace ℝ _))
    (z : {x | f x ≤ c - ε}) (hz : (z : M) = K i (t, v)) :
    morseChartChange φ₀ φ₁ k hk hε hball₀ hball₁ hf₀ hf₁ h K hK
        (morseCellAttachmentCell φ₁ k hk hε.le hball₁ hf₁ i w) =
      morseCellAttachmentIncl φ₀ k hk hε.le hball₀ hf₀ z := by
  have htime : σ (TopCat.annulusParam 2⁻¹ w) = t := by
    have h := TopCat.add_one_sub_mul_annulusParam (by norm_num : (2⁻¹ : ℝ) ≤ 1) hw
    refine Subtype.ext ?_
    rw [coe_symm_eq, ht]
    linarith
  have hdir : TopCat.diskBoundaryInclusion (k i) (TopCat.annulusDir (by norm_num) ⟨w, hw⟩) = v :=
    ULift.ext (Subtype.ext ((TopCat.coe_diskBoundaryInclusion_apply_down _ _).trans
      ((TopCat.coe_annulusDir _ _).trans hv.symm)))
  rw [morseChartChange_morseCellAttachmentCell, morseChartChangeCellFun_of_le_norm (hw := hw)]
  refine congrArg _ (Subtype.ext ?_)
  rw [hz]
  exact congrArg (fun p ↦ (K i p : M)) (Prod.ext htime hdir)

/-- After the handle-to-cell comparison of `φ₀`, the change-of-chart comparison reads on the
`i`-th disc as `K i` along the flattened cup. -/
private theorem morseCellComparison_morseChartChange_morseCellAttachmentCell (i : ι)
    (w : TopCat.disk.{u} (k i)) :
    (morseCellComparison φ₀ k hk hε.le hball₀ hf₀
        (morseChartChange φ₀ φ₁ k hk hε hball₀ hball₁ hf₀ hf₁ h K hK
          (morseCellAttachmentCell φ₁ k hk hε.le hball₁ hf₁ i w))) =
      K i (diskCupTime w, diskCup w) := by
  by_cases hw : 2⁻¹ ≤ ‖(w.down : EuclideanSpace ℝ (Fin (k i)))‖
  · rw [morseChartChange_morseCellAttachmentCell_of_le_norm φ₀ φ₁ k hk hε hball₀ hball₁ hf₀ hf₁ h
      K hK i hw (cupTime_of_le_norm hw) (cupPoint_of_le_norm hw)
      ⟨K i (diskCupTime w, diskCup w), hK i _ _ (norm_cupPoint_of_le_norm hw)⟩ rfl]
    exact Subtype.ext (coe_morseCellComparison_morseCellAttachmentIncl φ₀ k hk hball₀ hf₀ hε.le _)
  · rw [morseChartChange_morseCellAttachmentCell, morseChartChangeCellFun_of_norm_le
      (hw := (not_le.1 hw).le), ← ConcreteCategory.comp_apply,
      morseCellAttachmentCell_comp_morseCellComparison, diskCupTime_of_norm_le (not_le.1 hw).le,
      (K i).apply_one, ContinuousMap.comp_apply]

/-- The disc part of the homotopy from `Φ₀ ∘ E_H` to `Φ₁`: `K i` along the straight-line homotopy
from the flattened cup to the bottom disc of the cylinder. -/
private def morseChartChangeHomotopyCell (i : ι) :
    TopCat.disk.{u} (k i) ⟶ TopCat.of C(I, {x | f x ≤ c + ε}) :=
  TopCat.ofHom (ContinuousMap.curry
    ⟨fun p ↦ K i (diskCupHomotopyTime p.1 p.2, diskCupHomotopy p.1 p.2),
      (K i).continuous.comp (continuous_diskCupHomotopyTime.prodMk continuous_diskCupHomotopy)⟩)

/-- The lower-sublevel part of the homotopy from `Φ₀ ∘ E_H` to `Φ₁`: constant paths. -/
private def morseChartChangeHomotopyIncl :
    TopCat.of {x | f x ≤ c - ε} ⟶ TopCat.of C(I, {x | f x ≤ c + ε}) :=
  TopCat.ofHom (ContinuousMap.const'.comp (sublevelInclusion f (c - ε) (c + ε) (by linarith)))

private theorem morseChartChangeHomotopyIncl_apply (x : {x | f x ≤ c - ε}) (t : I) :
    (morseChartChangeHomotopyIncl hε x t : M) = x :=
  coe_sublevelInclusion_apply f _ x

private theorem morseChartChangeHomotopyCell_apply (i : ι) (w : TopCat.disk.{u} (k i)) (t : I) :
    morseChartChangeHomotopyCell φ₀ φ₁ k hk hε hball₀ hball₁ hf₀ hf₁ h K i w t =
      K i (diskCupHomotopyTime w t, diskCupHomotopy w t) :=
  (rfl)

private theorem morseAttachingMap_comp_morseChartChangeHomotopyIncl (i : ι) :
    (φ₁ i).morseAttachingMap (hk i) hε.le (hball₁ i) (hf₁ i) ≫
        morseChartChangeHomotopyIncl (f := f) (c := c) hε =
      TopCat.diskBoundaryInclusion (k i) ≫
        morseChartChangeHomotopyCell φ₀ φ₁ k hk hε hball₀ hball₁ hf₀ hf₁ h K i := by
  ext s t
  set w := TopCat.diskBoundaryInclusion (k i) s
  have hw : ‖(w.down : EuclideanSpace ℝ (Fin (k i)))‖ = 1 := TopCat.norm_diskBoundaryInclusion s
  refine (morseChartChangeHomotopyIncl_apply hε _ t).trans (Eq.trans ?_ (congrArg Subtype.val
    (morseChartChangeHomotopyCell_apply φ₀ φ₁ k hk hε hball₀ hball₁ hf₀ hf₁ h K i w t)).symm)
  rw [diskCupHomotopyTime_of_norm_eq_one hw, diskCupHomotopy_of_norm_eq_one hw, (K i).apply_zero]
  have hsq := ConcreteCategory.congr_hom
    ((φ₁ i).morseAttachingMap_comp_sublevelInclusion (hball₁ i) (hf₁ i) (hk i) hε.le) s
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, TopCat.ofHom_apply] at hsq
  exact (coe_sublevelInclusion_apply f _ _).symm.trans (congrArg Subtype.val hsq)

/-- The homotopy from `Φ₀ ∘ E_H` to `Φ₁`, as a map into the paths in `M_{c+ε}`. -/
private def morseChartChangeHomotopyMap :
    morseCellAttachment φ₁ k hk hε.le hball₁ hf₁ ⟶ TopCat.of C(I, {x | f x ≤ c + ε}) :=
  morseCellAttachmentDesc φ₁ k hk hε.le hball₁ hf₁ (morseChartChangeHomotopyIncl hε)
    (morseChartChangeHomotopyCell φ₀ φ₁ k hk hε hball₀ hball₁ hf₀ hf₁ h K)
    (morseAttachingMap_comp_morseChartChangeHomotopyIncl φ₀ φ₁ k hk hε hball₀ hball₁ hf₀ hf₁ h K)

private theorem morseChartChangeHomotopyMap_incl (x : {x | f x ≤ c - ε}) (t : I) :
    (morseChartChangeHomotopyMap φ₀ φ₁ k hk hε hball₀ hball₁ hf₀ hf₁ h K
        (morseCellAttachmentIncl φ₁ k hk hε.le hball₁ hf₁ x) t : M) = x := by
  rw [← ConcreteCategory.comp_apply, morseChartChangeHomotopyMap, morseCellAttachmentIncl_desc]
  exact morseChartChangeHomotopyIncl_apply hε x t

private theorem morseChartChangeHomotopyMap_cell (i : ι) (w : TopCat.disk.{u} (k i)) (t : I) :
    morseChartChangeHomotopyMap φ₀ φ₁ k hk hε hball₀ hball₁ hf₀ hf₁ h K
        (morseCellAttachmentCell φ₁ k hk hε.le hball₁ hf₁ i w) t =
      K i (diskCupHomotopyTime w t, diskCupHomotopy w t) := by
  rw [← ConcreteCategory.comp_apply, morseChartChangeHomotopyMap, morseCellAttachmentCell_desc]
  exact morseChartChangeHomotopyCell_apply φ₀ φ₁ k hk hε hball₀ hball₁ hf₀ hf₁ h K i w t

/-- The homotopy from `Φ₀ ∘ E_H` to `Φ₁` relative to the lower sublevel. -/
private def morseChartChangeHomotopy :
    ((morseChartChange φ₀ φ₁ k hk hε hball₀ hball₁ hf₀ hf₁ h K hK ≫
        morseCellComparison φ₀ k hk hε.le hball₀ hf₀).hom).HomotopyRel
      (morseCellComparison φ₁ k hk hε.le hball₁ hf₁).hom
      (range (morseCellAttachmentIncl φ₁ k hk hε.le hball₁ hf₁)) where
  toFun p := morseChartChangeHomotopyMap φ₀ φ₁ k hk hε hball₀ hball₁ hf₀ hf₁ h K p.2 p.1
  continuous_toFun := continuous_eval.comp
    (((morseChartChangeHomotopyMap φ₀ φ₁ k hk hε hball₀ hball₁ hf₀ hf₁ h K).hom.continuous.comp
      continuous_snd).prodMk continuous_fst)
  map_zero_left y := by
    obtain ⟨x, rfl⟩ | hy :=
      (range_morseCellAttachmentIncl_union_iUnion_range_morseCellAttachmentCell φ₁ k hk hball₁ hf₁
        hε.le).symm ▸ mem_univ y
    · exact Subtype.ext ((morseChartChangeHomotopyMap_incl φ₀ φ₁ k hk hε hball₀ hball₁ hf₀ hf₁ h K
        x 0).trans (coe_morseCellComparison_morseChartChange_incl φ₀ φ₁ k hk hε hball₀ hball₁ hf₀
          hf₁ h K hK x).symm)
    · obtain ⟨i, w, rfl⟩ := mem_iUnion.1 hy
      rw [morseChartChangeHomotopyMap_cell, diskCupHomotopyTime_zero, diskCupHomotopy_zero,
        TopCat.hom_comp, ContinuousMap.comp_apply]
      exact (morseCellComparison_morseChartChange_morseCellAttachmentCell φ₀ φ₁ k hk hε hball₀
        hball₁ hf₀ hf₁ h K hK i w).symm
  map_one_left y := by
    obtain ⟨x, rfl⟩ | hy :=
      (range_morseCellAttachmentIncl_union_iUnion_range_morseCellAttachmentCell φ₁ k hk hball₁ hf₁
        hε.le).symm ▸ mem_univ y
    · exact Subtype.ext ((morseChartChangeHomotopyMap_incl φ₀ φ₁ k hk hε hball₀ hball₁ hf₀ hf₁ h K
        x 1).trans
          (coe_morseCellComparison_morseCellAttachmentIncl φ₁ k hk hball₁ hf₁ hε.le x).symm)
    · obtain ⟨i, w, rfl⟩ := mem_iUnion.1 hy
      rw [morseChartChangeHomotopyMap_cell, diskCupHomotopyTime_one, diskCupHomotopy_one,
        (K i).apply_zero, ← ConcreteCategory.comp_apply,
        morseCellAttachmentCell_comp_morseCellComparison]
  prop' t y hy := by
    obtain ⟨x, rfl⟩ := hy
    exact Subtype.ext ((morseChartChangeHomotopyMap_incl φ₀ φ₁ k hk hε hball₀ hball₁ hf₀ hf₁ h K
      x t).trans (coe_morseCellComparison_morseChartChange_incl φ₀ φ₁ k hk hε hball₀ hball₁ hf₀
        hf₁ h K hK x).symm)

/-- **The change-of-chart comparison is compatible with the handle-to-cell comparisons.** The
composite `Φ₀ ∘ E_H` of the change-of-chart comparison with the handle-to-cell comparison
`Φ₀ : M_{c-ε} ∪_{α₀} ⨆ᵢ D^{k i} → M_{c+ε}` of the charts `φ₀` is homotopic to the handle-to-cell
comparison `Φ₁` of the charts `φ₁`, relative to the lower sublevel `M_{c-ε}`. -/
theorem homotopicRel_morseChartChange_comp_morseCellComparison :
    ((morseChartChange φ₀ φ₁ k hk hε hball₀ hball₁ hf₀ hf₁ h K hK ≫
        morseCellComparison φ₀ k hk hε.le hball₀ hf₀).hom).HomotopicRel
      (morseCellComparison φ₁ k hk hε.le hball₁ hf₁).hom
      (range (morseCellAttachmentIncl φ₁ k hk hε.le hball₁ hf₁)) :=
  ⟨morseChartChangeHomotopy φ₀ φ₁ k hk hε hball₀ hball₁ hf₀ hf₁ h K hK⟩

/-- If `g₀` is a left inverse of the handle-to-cell comparison `Φ₀` of the charts `φ₀`, then the
change-of-chart comparison `E_H` is homotopic to `g₀ ∘ Φ₁` relative to the lower sublevel. -/
theorem homotopicRel_morseChartChange_of_leftInverse
    {g₀ : C({x | f x ≤ c + ε}, morseCellAttachment φ₀ k hk hε.le hball₀ hf₀)}
    (hg₀ : LeftInverse g₀ (morseCellComparison φ₀ k hk hε.le hball₀ hf₀)) :
    (morseChartChange φ₀ φ₁ k hk hε hball₀ hball₁ hf₀ hf₁ h K hK).hom.HomotopicRel
      (g₀.comp (morseCellComparison φ₁ k hk hε.le hball₁ hf₁).hom)
      (range (morseCellAttachmentIncl φ₁ k hk hε.le hball₁ hf₁)) := by
  have := (homotopicRel_morseChartChange_comp_morseCellComparison φ₀ φ₁ k hk hε hball₀ hball₁ hf₀
    hf₁ h K hK).comp_continuousMap g₀
  convert this using 1
  ext y
  exact (hg₀ _).symm

/-- **The change-of-chart comparison is a homotopy equivalence relative to the lower sublevel.**
Let `g₀` and `g₁` be left inverses of the handle-to-cell comparisons `Φ₀` and `Φ₁` of the charts
`φ₀` and `φ₁` such that `Φ₀ ∘ g₀` and `Φ₁ ∘ g₁` are homotopic to the identity relative to the
images of `Φ₀` and `Φ₁`. Then `g₁ ∘ Φ₀` is a homotopy inverse of the change-of-chart comparison
`E_H : M_{c-ε} ∪_{α₁} ⨆ᵢ D^{k i} → M_{c-ε} ∪_{α₀} ⨆ᵢ D^{k i}`: it is the identity on the lower
sublevel `M_{c-ε}`, and both homotopies are relative to `M_{c-ε}`. -/
theorem relHomotopyInverse_morseChartChange_of_leftInverse
    {g₀ : C({x | f x ≤ c + ε}, morseCellAttachment φ₀ k hk hε.le hball₀ hf₀)}
    (hg₀ : LeftInverse g₀ (morseCellComparison φ₀ k hk hε.le hball₀ hf₀))
    (hd₀ : (ContinuousMap.id _).HomotopicRel
      ((morseCellComparison φ₀ k hk hε.le hball₀ hf₀).hom.comp g₀)
      (range (morseCellComparison φ₀ k hk hε.le hball₀ hf₀)))
    {g₁ : C({x | f x ≤ c + ε}, morseCellAttachment φ₁ k hk hε.le hball₁ hf₁)}
    (hg₁ : LeftInverse g₁ (morseCellComparison φ₁ k hk hε.le hball₁ hf₁))
    (hd₁ : (ContinuousMap.id _).HomotopicRel
      ((morseCellComparison φ₁ k hk hε.le hball₁ hf₁).hom.comp g₁)
      (range (morseCellComparison φ₁ k hk hε.le hball₁ hf₁))) :
    morseCellAttachmentIncl φ₀ k hk hε.le hball₀ hf₀ ≫
        TopCat.ofHom (g₁.comp (morseCellComparison φ₀ k hk hε.le hball₀ hf₀).hom) =
      morseCellAttachmentIncl φ₁ k hk hε.le hball₁ hf₁ ∧
    (TopCat.ofHom (g₁.comp (morseCellComparison φ₀ k hk hε.le hball₀ hf₀).hom) ≫
        morseChartChange φ₀ φ₁ k hk hε hball₀ hball₁ hf₀ hf₁ h K hK).hom.HomotopicRel
      (ContinuousMap.id _) (range (morseCellAttachmentIncl φ₀ k hk hε.le hball₀ hf₀)) ∧
    (morseChartChange φ₀ φ₁ k hk hε hball₀ hball₁ hf₀ hf₁ h K hK ≫
        TopCat.ofHom (g₁.comp (morseCellComparison φ₀ k hk hε.le hball₀ hf₀).hom)).hom.HomotopicRel
      (ContinuousMap.id _) (range (morseCellAttachmentIncl φ₁ k hk hε.le hball₁ hf₁)) := by
  set Φ₀ := morseCellComparison φ₀ k hk hε.le hball₀ hf₀
  set Φ₁ := morseCellComparison φ₁ k hk hε.le hball₁ hf₁
  set ι₀ := morseCellAttachmentIncl φ₀ k hk hε.le hball₀ hf₀
  set ι₁ := morseCellAttachmentIncl φ₁ k hk hε.le hball₁ hf₁
  have hE := homotopicRel_morseChartChange_of_leftInverse φ₀ φ₁ k hk hε hball₀ hball₁ hf₀ hf₁ h
    K hK hg₀
  -- Both comparisons are the inclusion on the lower sublevel.
  have hΦ (x : {x | f x ≤ c - ε}) : Φ₀ (ι₀ x) = Φ₁ (ι₁ x) :=
    Subtype.ext ((coe_morseCellComparison_morseCellAttachmentIncl φ₀ k hk hball₀ hf₀ hε.le x).trans
      (coe_morseCellComparison_morseCellAttachmentIncl φ₁ k hk hball₁ hf₁ hε.le x).symm)
  have hg₁ι (x : {x | f x ≤ c - ε}) : g₁ (Φ₀ (ι₀ x)) = ι₁ x := by
    rw [hΦ, hg₁]
  refine ⟨?_, ?_, ?_⟩
  · ext x
    exact hg₁ι x
  · -- `E_H ∘ g₁ ∘ Φ₀ ≃ g₀ ∘ Φ₁ ∘ g₁ ∘ Φ₀ ≃ g₀ ∘ Φ₀ = id`.
    have h₁ := (hE.precomp (g₁.comp Φ₀.hom)).mono (T := range ι₀) (by
      rintro _ ⟨x, rfl⟩
      exact ⟨x, (hg₁ι x).symm⟩)
    have h₂ := ((hd₁.symm.precomp Φ₀.hom).mono (T := range ι₀) (by
      rintro _ ⟨x, rfl⟩
      exact ⟨ι₁ x, (hΦ x).symm⟩)).comp_continuousMap g₀
    have e : g₀.comp ((ContinuousMap.id _).comp Φ₀.hom) = ContinuousMap.id _ :=
      ContinuousMap.ext hg₀
    rw [e] at h₂
    exact h₁.trans h₂
  · -- `g₁ ∘ Φ₀ ∘ E_H ≃ g₁ ∘ Φ₀ ∘ g₀ ∘ Φ₁ ≃ g₁ ∘ Φ₁ = id`.
    have h₁ := hE.comp_continuousMap (g₁.comp Φ₀.hom)
    have h₂ := ((hd₀.symm.precomp Φ₁.hom).mono (T := range ι₁) (by
      rintro _ ⟨x, rfl⟩
      exact ⟨ι₀ x, hΦ x⟩)).comp_continuousMap g₁
    have e : g₁.comp ((ContinuousMap.id _).comp Φ₁.hom) = ContinuousMap.id _ :=
      ContinuousMap.ext hg₁
    rw [e] at h₂
    exact h₁.trans h₂

end ChartChange

section Deformation

variable {E H : Type*} {M : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [FiniteDimensional ℝ E]
  [I.Boundaryless] [IsManifold I ∞ M] [T2Space M] {n : ℕ} {ι : Type u} {f : M → ℝ} {c ε : ℝ}

/-- **The change-of-chart comparison is a homotopy equivalence relative to the lower sublevel.**
Let `f` be smooth and let `ψ₀ i`, `ψ₁ i` be two finite families of smooth charts with pairwise
disjoint sources, whose targets contain the closed ball of radius `√(2ε)`, in which
`f = c - Σ_{j < k i} yⱼ² + Σ_{j ≥ k i} yⱼ²`. Suppose that the band `f⁻¹[c - ε, c + ε]` is compact
and that its critical points lie in the charts of each family. Then for any homotopies of pairs
`K i : χ₁ i ≃ χ₀ i ∘ h i` between the characteristic maps, the change-of-chart comparison
`E_H : M_{c-ε} ∪_{α₁} ⨆ᵢ D^{k i} → M_{c-ε} ∪_{α₀} ⨆ᵢ D^{k i}` has a homotopy inverse `E'` which is
the identity on the lower sublevel `M_{c-ε}`, with both homotopies relative to `M_{c-ε}`. -/
theorem exists_relHomotopyInverse_morseChartChange [Finite ι] (hfs : ContMDiff I 𝓘(ℝ) ∞ f)
    (ψ₀ ψ₁ : ι → PartialDiffeomorph I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M
      (EuclideanSpace ℝ (Fin n)) ∞)
    (hψ₀ : Pairwise (Disjoint on fun i ↦ (ψ₀ i).source))
    (hψ₁ : Pairwise (Disjoint on fun i ↦ (ψ₁ i).source)) (k : ι → ℕ) (hk : ∀ i, k i ≤ n)
    (hε : 0 < ε) (hball₀ : ∀ i, closedBall 0 √(2 * ε) ⊆ (ψ₀ i).target)
    (hball₁ : ∀ i, closedBall 0 √(2 * ε) ⊆ (ψ₁ i).target)
    (hf₀ : ∀ i, ∀ y ∈ (ψ₀ i).source, f y = c + ∑ j, (if j.val < k i then -1 else 1) * ψ₀ i y j ^ 2)
    (hf₁ : ∀ i, ∀ y ∈ (ψ₁ i).source, f y = c + ∑ j, (if j.val < k i then -1 else 1) * ψ₁ i y j ^ 2)
    (hcompact : IsCompact (f ⁻¹' Icc (c - ε) (c + ε)))
    (hcrit₀ : criticalPoints I f ∩ f ⁻¹' Icc (c - ε) (c + ε) ⊆ ⋃ i, (ψ₀ i).source)
    (hcrit₁ : criticalPoints I f ∩ f ⁻¹' Icc (c - ε) (c + ε) ⊆ ⋃ i, (ψ₁ i).source)
    (h : ∀ i, TopCat.disk.{u} (k i) ⟶ TopCat.disk.{u} (k i))
    (K : ∀ i, ((ψ₁ i).toOpenPartialHomeomorph.morseCharacteristicMap (hk i) hε.le
        ((hball₁ i).trans' (closedBall_subset_closedBall (Real.sqrt_le_sqrt_two_mul ε)))
        (hf₁ i)).hom.Homotopy
      (((ψ₀ i).toOpenPartialHomeomorph.morseCharacteristicMap (hk i) hε.le
        ((hball₀ i).trans' (closedBall_subset_closedBall (Real.sqrt_le_sqrt_two_mul ε)))
        (hf₀ i)).hom.comp (h i).hom))
    (hK : ∀ i t (w : TopCat.disk.{u} (k i)), ‖(w.down : EuclideanSpace ℝ (Fin (k i)))‖ = 1 →
      f (K i (t, w)) ≤ c - ε) :
    ∃ E' : morseCellAttachment (fun i ↦ (ψ₀ i).toOpenPartialHomeomorph) k hk hε.le
        (fun i ↦ (hball₀ i).trans' (closedBall_subset_closedBall (Real.sqrt_le_sqrt_two_mul ε)))
        hf₀ ⟶
      morseCellAttachment (fun i ↦ (ψ₁ i).toOpenPartialHomeomorph) k hk hε.le
        (fun i ↦ (hball₁ i).trans' (closedBall_subset_closedBall (Real.sqrt_le_sqrt_two_mul ε)))
        hf₁,
      morseCellAttachmentIncl _ k hk hε.le _ hf₀ ≫ E' = morseCellAttachmentIncl _ k hk hε.le _ hf₁ ∧
      (E' ≫ morseChartChange _ _ k hk hε _ _ hf₀ hf₁ h K hK).hom.HomotopicRel
        (ContinuousMap.id _) (range (morseCellAttachmentIncl _ k hk hε.le _ hf₀)) ∧
      (morseChartChange _ _ k hk hε _ _ hf₀ hf₁ h K hK ≫ E').hom.HomotopicRel
        (ContinuousMap.id _) (range (morseCellAttachmentIncl _ k hk hε.le _ hf₁)) := by
  obtain ⟨g₀, hg₀, hd₀⟩ := exists_morseCellAttachment_deformation hfs ψ₀ hψ₀ k hk hε hball₀ hf₀
    hcompact hcrit₀
  obtain ⟨g₁, hg₁, hd₁⟩ := exists_morseCellAttachment_deformation hfs ψ₁ hψ₁ k hk hε hball₁ hf₁
    hcompact hcrit₁
  exact ⟨_, relHomotopyInverse_morseChartChange_of_leftInverse _ _ k hk hε _ _ hf₀ hf₁ h K hK hg₀
    hd₀ hg₁ hd₁⟩

end Deformation

end TauCeti
