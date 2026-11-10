/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.OpenPartialHomeomorph.Basic
public import TauCeti.AlgebraicTopology.Disk
public import TauCeti.AlgebraicTopology.Disk.LinearIsometry
public import TauCeti.Analysis.InnerProductSpace.PiL2
public import TauCeti.Analysis.Normed.Lp.PiLp
public import TauCeti.Topology.Order.Sublevel

/-!
# Characteristic and attaching maps of Morse cells

Let `ψ` be a chart of `M` with values in `ℝⁿ` in which a function `f` has the normal form

`f = c - Σ_{j < k} yⱼ² + Σ_{j ≥ k} yⱼ²`,

and suppose the target of `ψ` contains the closed ball of radius `√ε` about `0`, for some
`0 < ε`. When the centre of `ψ` is the only critical point of `f` in the compact region
`f⁻¹[c - ε, c + ε]` and `ε` is small, Milnor's *Morse Theory*, Theorem 3.2, shows that passing
the level `c` attaches, up to homotopy, the cell `{‖y‖² ≤ ε, yⱼ = 0 for j ≥ k}` of the negative
coordinates, read in `M` through `ψ`. The constructions here use only the chart hypotheses. This
file parametrizes that cell by the unit disc `D^k ⊆ ℝᵏ`:

`χ(w) = ψ⁻¹(√ε • (w, 0))`,

where `(w, 0) ∈ ℝⁿ` extends `w` by zero onto the first `k` coordinates. Then
`f (χ w) = c - ε ‖w‖²`, so `χ` maps the disc into the sublevel `M_c = {f ≤ c}` and its boundary
sphere into the level `f⁻¹(c - ε)`; a point of the disc is sent into the lower sublevel
`M_{c-ε} = {f ≤ c - ε}` exactly when it lies on the boundary sphere. The map `χ` is injective on
the disc, its image there is the cell, and it is a closed embedding of the disc into a Hausdorff
`M`.

Bundled as morphisms of topological spaces, `χ` is the characteristic map
`(D^k, ∂D^k) → (M_{c+ε}, M_{c-ε})` of the cell and its restriction to the boundary sphere is the
attaching map `∂D^k → M_{c-ε}`. These are the maps out of which the comparison between
`M_{c-ε}` with cells attached along the attaching maps and the sublevel `M_{c+ε}` is built, as
the map induced on the pushout by the inclusion of `M_{c-ε}` and the characteristic maps.

Two normal-form charts of the same index may parametrize the cell differently. Suppose the
characteristic map `χ₁` of one is homotopic as a map of pairs to `χ₀ ∘ g` for the characteristic
map `χ₀` of the other and an orthogonal map `g` (in Milnor's comparison of two charts, the polar
factor of the negative block of the transition). Then the attaching map `α₁` is homotopic to
`α₀ ∘ g`. If `det g = 1`, then `g` can be removed: it is joined to the identity in the special
orthogonal group, so `χ₁` is homotopic to `χ₀` as a map of pairs, and the two attaching maps are
homotopic. If the cell has index `1` and `det g = -1`, then `g = -1`, and `α₁` is homotopic to
`α₀` composed with the swap of the two points of `∂D¹ = {-1, 1}`. In every index, `det g = -1`
changes the sign of the attaching map in reduced homology
(`TauCeti.reducedSingularHomologyFunctor_map_morseAttachingMap_of_det_eq_neg_one`).

## Main definitions

* `OpenPartialHomeomorph.morseCellMap`: the parametrization `w ↦ ψ⁻¹(√ε • (w, 0))` of the cell
  of a normal-form chart.
* `OpenPartialHomeomorph.morseCharacteristicMap`: the characteristic map `D^k ⟶ M_{c+ε}` of the
  cell.
* `OpenPartialHomeomorph.morseAttachingMap`: the attaching map `∂D^k ⟶ M_{c-ε}` of the cell.

## Main results

* `OpenPartialHomeomorph.morseCellMap_image_closedBall`: the image of the unit disc is the cell
  `{‖ψ x‖² ≤ ε, (ψ x)ⱼ = 0 for j ≥ k}`.
* `OpenPartialHomeomorph.closedBall_inter_preimage_morseCellMap_sublevel`: a point of the disc
  lands in `M_{c-ε}` exactly when it lies on the boundary sphere.
* `OpenPartialHomeomorph.preimage_morseCharacteristicMap_sublevel`: the characteristic map is a
  map of pairs `(D^k, ∂D^k) → (M_{c+ε}, M_{c-ε})`.
* `OpenPartialHomeomorph.isClosedEmbedding_morseCharacteristicMap`: the characteristic map is a
  closed embedding.
* `OpenPartialHomeomorph.morseAttachingMap_comp_sublevelInclusion`: the attaching map is the
  restriction of the characteristic map to the boundary sphere.
* `TauCeti.mapsTo_range_diskBoundaryInclusion_of_morseCharacteristicMap_le`,
  `TauCeti.mapsTo_range_diskBoundaryInclusion_of_homotopy_morseCharacteristicMap`: for `0 < ε`, a
  self-map `h` of the disc such that `χ ∘ h` sends the boundary sphere into the lower sublevel, for
  instance the end of a homotopy of maps of pairs, preserves the boundary sphere.
* `TauCeti.homotopic_morseAttachingMap_diskBoundaryMap_comp`: a homotopy of pairs from `χ₁` to
  `χ₀ ∘ g` gives a homotopy from `α₁` to `α₀ ∘ g`.
* `TauCeti.exists_homotopy_morseCharacteristicMap_of_det_eq_one`,
  `TauCeti.homotopic_morseAttachingMap_of_det_eq_one`: an orthogonal change of parametrization of
  determinant `1` is removed from a homotopy of characteristic maps, and the attaching maps are
  then homotopic.
* `TauCeti.homotopic_morseAttachingMap_diskBoundaryNeg_comp_of_det_eq_neg_one`: for a cell of
  index `1`, an orthogonal change of parametrization of determinant `-1` swaps the two attaching
  points.

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  Theorem 3.2 and Remark 3.3.
-/

public section

noncomputable section

open Function Set Metric Topology CategoryTheory
open LinearIsometry (piLpExtendByZero piLpExtendByZero_castLEEmb_apply
  range_piLpExtendByZero_castLEEmb)

universe u

namespace OpenPartialHomeomorph

open TauCeti

variable {M : Type u} [TopologicalSpace M] {n k : ℕ}
  {ψ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))} {f : M → ℝ} {c ε : ℝ}
  {w : EuclideanSpace ℝ (Fin k)}

/-- The parametrization `w ↦ ψ⁻¹(√ε • (w, 0))` of the cell `{‖y‖² ≤ ε, yⱼ = 0 for j ≥ k}` of a
chart `ψ`, where `(w, 0)` extends `w ∈ ℝᵏ` by zero onto the first `k` coordinates of `ℝⁿ`. On the
unit disc it is the characteristic map of the cell; see
`OpenPartialHomeomorph.morseCellMap_image_closedBall`. -/
def morseCellMap (ψ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))) (hk : k ≤ n) (ε : ℝ)
    (w : EuclideanSpace ℝ (Fin k)) : M :=
  ψ.symm (√ε • piLpExtendByZero 2 ℝ ℝ (Fin.castLEEmb hk) w)

/-- `OpenPartialHomeomorph.morseCellMap ψ hk ε w` is `ψ⁻¹(√ε • (w, 0))`. -/
theorem morseCellMap_def (hk : k ≤ n) (w : EuclideanSpace ℝ (Fin k)) :
    morseCellMap ψ hk ε w = ψ.symm (√ε • piLpExtendByZero 2 ℝ ℝ (Fin.castLEEmb hk) w) :=
  (rfl)

/-- The centre of the cell is the centre `ψ⁻¹ 0` of the chart. -/
@[simp]
theorem morseCellMap_zero (hk : k ≤ n) : morseCellMap ψ hk ε 0 = ψ.symm 0 := by
  simp [morseCellMap_def]

/-- Scaling the parameter of a characteristic disc rescales its width quadratically. -/
theorem morseCellMap_smul (hk : k ≤ n) {a : ℝ} (ha : 0 ≤ a)
    (w : EuclideanSpace ℝ (Fin k)) :
    morseCellMap ψ hk ε (a • w) = morseCellMap ψ hk (ε * a ^ 2) w := by
  simp only [morseCellMap_def, map_smul, smul_smul, Real.sqrt_mul' ε (sq_nonneg a),
    Real.sqrt_sq ha]

private theorem norm_smul_piLpExtendByZero (hk : k ≤ n) (w : EuclideanSpace ℝ (Fin k)) :
    ‖√ε • piLpExtendByZero 2 ℝ ℝ (Fin.castLEEmb hk) w‖ = √ε * ‖w‖ := by
  rw [norm_smul, LinearIsometry.norm_map, Real.norm_of_nonneg (Real.sqrt_nonneg _)]

private theorem norm_smul_piLpExtendByZero_sq (hk : k ≤ n) (hε : 0 ≤ ε)
    (w : EuclideanSpace ℝ (Fin k)) :
    ‖√ε • piLpExtendByZero 2 ℝ ℝ (Fin.castLEEmb hk) w‖ ^ 2 = ε * ‖w‖ ^ 2 := by
  rw [norm_smul_piLpExtendByZero, mul_pow, Real.sq_sqrt hε]

private theorem smul_piLpExtendByZero_apply_of_le (hk : k ≤ n) (a : ℝ)
    (w : EuclideanSpace ℝ (Fin k)) {j : Fin n} (hj : k ≤ j.val) :
    (a • piLpExtendByZero 2 ℝ ℝ (Fin.castLEEmb hk) w) j = 0 := by
  rw [PiLp.smul_apply, piLpExtendByZero_castLEEmb_apply, dite_eq_right (not_lt.2 hj), smul_zero]

variable (hball : closedBall 0 √ε ⊆ ψ.target)
include hball

private theorem smul_piLpExtendByZero_mem_target (hk : k ≤ n) (hw : ‖w‖ ≤ 1) :
    √ε • piLpExtendByZero 2 ℝ ℝ (Fin.castLEEmb hk) w ∈ ψ.target :=
  hball <| mem_closedBall_zero_iff.2 <| by
    rw [norm_smul_piLpExtendByZero]
    exact mul_le_of_le_one_right (Real.sqrt_nonneg _) hw

/-- A point of the unit disc is sent into the source of the chart. -/
theorem morseCellMap_mem_source (hk : k ≤ n) (hw : ‖w‖ ≤ 1) : morseCellMap ψ hk ε w ∈ ψ.source :=
  ψ.map_target (smul_piLpExtendByZero_mem_target hball hk hw)

/-- In the chart, a point of the unit disc is sent to `√ε • (w, 0)`. -/
theorem apply_morseCellMap (hk : k ≤ n) (hw : ‖w‖ ≤ 1) :
    ψ (morseCellMap ψ hk ε w) = √ε • piLpExtendByZero 2 ℝ ℝ (Fin.castLEEmb hk) w :=
  ψ.right_inv (smul_piLpExtendByZero_mem_target hball hk hw)

/-- In the chart, the coordinates of a point of the cell vanish beyond the first `k`. -/
theorem apply_morseCellMap_apply_eq_zero (hk : k ≤ n) (hw : ‖w‖ ≤ 1) {j : Fin n}
    (hj : k ≤ j.val) : ψ (morseCellMap ψ hk ε w) j = 0 := by
  rw [apply_morseCellMap hball hk hw, smul_piLpExtendByZero_apply_of_le hk _ _ hj]

/-- In the chart, the squared norm of the image of a point `w` of the unit disc is `ε ‖w‖²`. -/
theorem norm_apply_morseCellMap_sq (hk : k ≤ n) (hε : 0 ≤ ε) (hw : ‖w‖ ≤ 1) :
    ‖ψ (morseCellMap ψ hk ε w)‖ ^ 2 = ε * ‖w‖ ^ 2 := by
  rw [apply_morseCellMap hball hk hw, norm_smul_piLpExtendByZero_sq hk hε]

/-- The parametrization of the cell is continuous on the unit disc. -/
theorem continuousOn_morseCellMap (hk : k ≤ n) : ContinuousOn (morseCellMap ψ hk ε)
    (closedBall 0 1) :=
  ψ.continuousOn_symm.comp (by fun_prop) fun _ hw ↦
    smul_piLpExtendByZero_mem_target hball hk (mem_closedBall_zero_iff.1 hw)

/-- The parametrization of the cell is injective on the unit disc. -/
theorem injOn_morseCellMap (hk : k ≤ n) (hε : 0 < ε) : InjOn (morseCellMap ψ hk ε)
    (closedBall 0 1) := by
  intro v hv w hw hvw
  have h := congrArg ψ hvw
  rw [apply_morseCellMap hball hk (mem_closedBall_zero_iff.1 hv),
    apply_morseCellMap hball hk (mem_closedBall_zero_iff.1 hw)] at h
  exact (LinearIsometry.injective _) (smul_right_injective _ (Real.sqrt_pos.2 hε).ne' h)

/-- The parametrization of the cell is a closed embedding of the unit disc into a Hausdorff
space. -/
theorem isClosedEmbedding_domRestrict_morseCellMap [T2Space M] (hk : k ≤ n) (hε : 0 < ε) :
    IsClosedEmbedding ((closedBall (0 : EuclideanSpace ℝ (Fin k)) 1).domRestrict
      (morseCellMap ψ hk ε)) :=
  have := isCompact_iff_compactSpace.1 (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin k)) 1)
  ((continuousOn_morseCellMap hball hk).domRestrict).isClosedEmbedding
    ((injOn_morseCellMap hball hk hε).injective)

/-- The image of the unit disc is the cell `{‖ψ x‖² ≤ ε, (ψ x)ⱼ = 0 for j ≥ k}` of the chart. -/
theorem morseCellMap_image_closedBall (hk : k ≤ n) (hε : 0 < ε) :
    morseCellMap ψ hk ε '' closedBall 0 1 =
      ψ.source ∩ ψ ⁻¹' {y | ‖y‖ ^ 2 ≤ ε ∧ ∀ j : Fin n, k ≤ j.val → y j = 0} := by
  have hsε : 0 < √ε := Real.sqrt_pos.2 hε
  refine Set.ext fun x ↦ ⟨?_, fun ⟨hx, hxε, hxk⟩ ↦ ?_⟩
  · rintro ⟨w, hw, rfl⟩
    rw [mem_closedBall_zero_iff] at hw
    refine ⟨morseCellMap_mem_source hball hk hw, ?_, fun j hj ↦
      apply_morseCellMap_apply_eq_zero hball hk hw hj⟩
    rw [norm_apply_morseCellMap_sq hball hk hε.le hw]
    exact mul_le_of_le_one_right hε.le (pow_le_one₀ (norm_nonneg _) hw)
  · obtain ⟨v, hv⟩ : ψ x ∈ range (piLpExtendByZero 2 ℝ ℝ (Fin.castLEEmb hk)) := by
      rw [range_piLpExtendByZero_castLEEmb]
      exact hxk
    refine ⟨(√ε)⁻¹ • v, mem_closedBall_zero_iff.2 ?_, ?_⟩
    · rw [norm_smul, norm_inv, Real.norm_of_nonneg hsε.le, inv_mul_le_iff₀ hsε, mul_one,
        ← LinearIsometry.norm_map (piLpExtendByZero 2 ℝ ℝ (Fin.castLEEmb hk)), hv]
      exact Real.le_sqrt_of_sq_le hxε
    · rw [morseCellMap_def, map_smul, smul_inv_smul₀ hsε.ne', hv, ψ.left_inv hx]

variable (hf : ∀ y ∈ ψ.source, f y = c + ∑ j, (if j.val < k then -1 else 1) * ψ y j ^ 2)
include hf

/-- Where `f` has the normal form `c - Σ_{j < k} yⱼ² + Σ_{j ≥ k} yⱼ²` in the chart, `f` takes the
value `c - ε ‖w‖²` at the image of a point `w` of the unit disc. -/
theorem apply_morseCellMap_eq_sub_mul_norm_sq (hk : k ≤ n) (hε : 0 ≤ ε) (hw : ‖w‖ ≤ 1) :
    f (morseCellMap ψ hk ε w) = c - ε * ‖w‖ ^ 2 := by
  set y := √ε • piLpExtendByZero 2 ℝ ℝ (Fin.castLEEmb hk) w
  have hy : ∀ j : Fin n, ¬j.val < k → y j = 0 := fun j hj ↦
    smul_piLpExtendByZero_apply_of_le hk _ w (not_lt.1 hj)
  have hv := EuclideanSpace.snd_sumComplEquivProd_eq_zero_iff.2 hy
  have hnorm := EuclideanSpace.norm_fst_sumComplEquivProd_sq_add_norm_snd_sq
    (p := fun j : Fin n ↦ j.val < k) y
  rw [hv, norm_zero, zero_pow two_ne_zero, add_zero, norm_smul_piLpExtendByZero_sq hk hε] at hnorm
  rw [hf _ (morseCellMap_mem_source hball hk hw), apply_morseCellMap hball hk hw,
    EuclideanSpace.sum_ite_neg_one_mul_sq_eq, hv, hnorm, norm_zero]
  ring

/-- The unit disc is sent into the sublevel `{f ≤ c}`. -/
theorem apply_morseCellMap_le (hk : k ≤ n) (hε : 0 ≤ ε) (hw : ‖w‖ ≤ 1) :
    f (morseCellMap ψ hk ε w) ≤ c := by
  rw [apply_morseCellMap_eq_sub_mul_norm_sq hball hf hk hε hw]
  exact sub_le_self _ (by positivity)

/-- The boundary sphere of the unit disc is sent into the level `f⁻¹(c - ε)`. -/
theorem apply_morseCellMap_of_norm_eq_one (hk : k ≤ n) (hε : 0 ≤ ε) (hw : ‖w‖ = 1) :
    f (morseCellMap ψ hk ε w) = c - ε := by
  rw [apply_morseCellMap_eq_sub_mul_norm_sq hball hf hk hε hw.le, hw, one_pow, mul_one]

/-- A point of the unit disc is sent into the lower sublevel `{f ≤ c - ε}` exactly when it lies
on the boundary sphere. -/
theorem closedBall_inter_preimage_morseCellMap_sublevel (hk : k ≤ n) (hε : 0 < ε) :
    closedBall 0 1 ∩ morseCellMap ψ hk ε ⁻¹' {x | f x ≤ c - ε} = sphere 0 1 := by
  refine Set.ext fun w ↦ ⟨fun ⟨hw, hwε⟩ ↦ ?_, fun hw ↦ ?_⟩
  · rw [mem_closedBall_zero_iff] at hw
    rw [mem_preimage, mem_ofPred_eq,
      apply_morseCellMap_eq_sub_mul_norm_sq hball hf hk hε.le hw] at hwε
    have : 1 ≤ ‖w‖ ^ 2 := le_of_mul_le_mul_left (by linarith) hε
    exact mem_sphere_zero_iff_norm.2 (le_antisymm hw (one_le_pow_iff_of_nonneg (norm_nonneg _)
      two_ne_zero |>.1 this))
  · rw [mem_sphere_zero_iff_norm] at hw
    exact ⟨mem_closedBall_zero_iff.2 hw.le,
      (apply_morseCellMap_of_norm_eq_one hball hf hk hε.le hw).le⟩

/-- The characteristic map `(D^k, ∂D^k) → (M_{c+ε}, M_{c-ε})` of the cell of a chart `ψ` in which
`f = c - Σ_{j < k} yⱼ² + Σ_{j ≥ k} yⱼ²` and whose target contains the closed ball of radius `√ε`:
the map `w ↦ ψ⁻¹(√ε • (w, 0))` from the unit disc into the sublevel `{f ≤ c + ε}`. -/
def morseCharacteristicMap (ψ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))) (hk : k ≤ n)
    (hε : 0 ≤ ε) (hball : closedBall 0 √ε ⊆ ψ.target)
    (hf : ∀ y ∈ ψ.source, f y = c + ∑ j, (if j.val < k then -1 else 1) * ψ y j ^ 2) :
    TopCat.disk.{u} k ⟶ TopCat.of {x | f x ≤ c + ε} :=
  TopCat.ofHom
    { toFun w := ⟨morseCellMap ψ hk ε w.down, (apply_morseCellMap_le hball hf hk hε
        (mem_closedBall_zero_iff.1 w.down.2)).trans (le_add_of_nonneg_right hε)⟩
      continuous_toFun := ((continuousOn_morseCellMap hball hk).comp_continuous
        (continuous_subtype_val.comp continuous_uliftDown) fun w ↦ w.down.2).subtype_mk _ }

/-- The attaching map `∂D^k → M_{c-ε}` of the cell of a chart `ψ` in which
`f = c - Σ_{j < k} yⱼ² + Σ_{j ≥ k} yⱼ²` and whose target contains the closed ball of radius `√ε`:
the restriction of `w ↦ ψ⁻¹(√ε • (w, 0))` to the unit sphere, which it maps into the level
`f⁻¹(c - ε)`. -/
def morseAttachingMap (ψ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))) (hk : k ≤ n)
    (hε : 0 ≤ ε) (hball : closedBall 0 √ε ⊆ ψ.target)
    (hf : ∀ y ∈ ψ.source, f y = c + ∑ j, (if j.val < k then -1 else 1) * ψ y j ^ 2) :
    TopCat.diskBoundary.{u} k ⟶ TopCat.of {x | f x ≤ c - ε} :=
  TopCat.ofHom
    { toFun w := ⟨morseCellMap ψ hk ε w.down, (apply_morseCellMap_of_norm_eq_one hball hf hk hε
        (mem_sphere_zero_iff_norm.1 w.down.2)).le⟩
      continuous_toFun := ((continuousOn_morseCellMap hball hk).comp_continuous
        (continuous_subtype_val.comp continuous_uliftDown)
        fun w ↦ sphere_subset_closedBall w.down.2).subtype_mk _ }

@[simp]
theorem coe_morseCharacteristicMap_apply (hk : k ≤ n) (hε : 0 ≤ ε) (w : TopCat.disk.{u} k) :
    (morseCharacteristicMap ψ hk hε hball hf w : M) = morseCellMap ψ hk ε w.down :=
  (rfl)

@[simp]
theorem coe_morseAttachingMap_apply (hk : k ≤ n) (hε : 0 ≤ ε) (w : TopCat.diskBoundary.{u} k) :
    (morseAttachingMap ψ hk hε hball hf w : M) = morseCellMap ψ hk ε w.down :=
  (rfl)

/-- On the boundary sphere, the characteristic map of the cell is its attaching map. This is the
pointwise form of `OpenPartialHomeomorph.morseAttachingMap_comp_sublevelInclusion`. -/
theorem coe_morseCharacteristicMap_diskBoundaryInclusion (hk : k ≤ n) (hε : 0 ≤ ε)
    (s : TopCat.diskBoundary.{u} k) :
    (morseCharacteristicMap ψ hk hε hball hf (TopCat.diskBoundaryInclusion k s) : M) =
      morseAttachingMap ψ hk hε hball hf s :=
  congrArg (morseCellMap ψ hk ε) (TauCeti.TopCat.coe_diskBoundaryInclusion_apply_down k s)

/-- The attaching map is the restriction of the characteristic map to the boundary sphere: the
square formed with the inclusions `∂D^k ⊆ D^k` and `M_{c-ε} ⊆ M_{c+ε}` commutes. This is the
compatibility needed to glue the inclusion of `M_{c-ε}` and the characteristic map into a map
out of `M_{c-ε}` with the cell attached. -/
@[reassoc]
theorem morseAttachingMap_comp_sublevelInclusion (hk : k ≤ n) (hε : 0 ≤ ε) :
    morseAttachingMap ψ hk hε hball hf ≫
        TopCat.ofHom (sublevelInclusion f (c - ε) (c + ε) (by linarith)) =
      TopCat.diskBoundaryInclusion k ≫ morseCharacteristicMap ψ hk hε hball hf := by
  ext w
  simp only [TopCat.hom_comp, TopCat.hom_ofHom, ContinuousMap.comp_apply,
    coe_sublevelInclusion_apply]
  exact congrArg (morseCellMap ψ hk ε)
    (TauCeti.TopCat.coe_diskBoundaryInclusion_apply_down k w).symm

/-- The characteristic map of the cell is a closed embedding of the unit disc into the sublevel
`M_{c+ε}`, when `M` is Hausdorff. -/
theorem isClosedEmbedding_morseCharacteristicMap [T2Space M] (hk : k ≤ n) (hε : 0 < ε) :
    IsClosedEmbedding (morseCharacteristicMap ψ hk hε.le hball hf) :=
  (morseCharacteristicMap ψ hk hε.le hball hf).hom.continuous.isClosedEmbedding fun v w hvw ↦
    ULift.ext <| Subtype.ext <| injOn_morseCellMap hball hk hε v.down.2 w.down.2
      congr(($hvw : M))

/-- A point of the disc is sent by the characteristic map into the lower sublevel `M_{c-ε}`
exactly when it lies on the boundary sphere: the characteristic map is a map of pairs
`(D^k, ∂D^k) → (M_{c+ε}, M_{c-ε})`. -/
theorem preimage_morseCharacteristicMap_sublevel (hk : k ≤ n) (hε : 0 < ε) :
    morseCharacteristicMap ψ hk hε.le hball hf ⁻¹' {x | f x ≤ c - ε} =
      range (TopCat.diskBoundaryInclusion.{u} k) := by
  refine Set.ext fun w ↦ ?_
  rw [mem_range_diskBoundaryInclusion_iff, ← mem_sphere_zero_iff_norm,
    ← closedBall_inter_preimage_morseCellMap_sublevel hball hf hk hε]
  exact ⟨fun h ↦ ⟨w.down.2, h⟩, fun h ↦ h.2⟩

/-- The image of the characteristic map is the cell `{‖ψ x‖² ≤ ε, (ψ x)ⱼ = 0 for j ≥ k}` of the
chart, viewed in the sublevel `M_{c+ε}`. -/
theorem range_morseCharacteristicMap (hk : k ≤ n) (hε : 0 < ε) :
    range (morseCharacteristicMap ψ hk hε.le hball hf) =
      {x : ↥{x | f x ≤ c + ε} |
        (x : M) ∈ ψ.source ∩ ψ ⁻¹' {y | ‖y‖ ^ 2 ≤ ε ∧ ∀ j : Fin n, k ≤ j.val → y j = 0}} := by
  rw [← morseCellMap_image_closedBall hball hk hε]
  refine Set.ext fun x ↦ ⟨?_, fun hx ↦ ?_⟩
  · rintro ⟨w, rfl⟩
    exact ⟨w.down, w.down.2, rfl⟩
  · obtain ⟨w, hw, hwx⟩ := hx
    exact ⟨ULift.up ⟨w, hw⟩, Subtype.ext hwx⟩

end OpenPartialHomeomorph

namespace TauCeti

section Boundary

variable {M : Type u} [TopologicalSpace M] {n : ℕ} {f : M → ℝ} {c ε : ℝ}
  {ψ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))} {k : ℕ} (hk : k ≤ n)
  (hε : 0 < ε) (hball : closedBall 0 √ε ⊆ ψ.target)
  (hf : ∀ y ∈ ψ.source, f y = c + ∑ j, (if j.val < k then -1 else 1) * ψ y j ^ 2)
  {h : TopCat.disk.{u} k ⟶ TopCat.disk.{u} k}

/-- **A self-map of the disc whose composite with a characteristic map sends the boundary sphere
into the lower sublevel preserves the boundary sphere.** Let `χ` be the characteristic map of the
cell of a normal-form chart, with `0 < ε`. If `h` is a self-map of the disc such that `χ ∘ h` sends
the boundary sphere into the lower sublevel `M_{c-ε}`, then `h` sends the boundary sphere into
itself, so `h` is a self-map of the pair `(D^k, ∂D^k)`. -/
theorem mapsTo_range_diskBoundaryInclusion_of_morseCharacteristicMap_le
    (hh : ∀ s : TopCat.diskBoundary.{u} k,
      f (ψ.morseCharacteristicMap hk hε.le hball hf (h (TopCat.diskBoundaryInclusion k s))) ≤
        c - ε) :
    MapsTo h (range (TopCat.diskBoundaryInclusion k)) (range (TopCat.diskBoundaryInclusion k)) := by
  rintro _ ⟨s, rfl⟩
  rw [← OpenPartialHomeomorph.preimage_morseCharacteristicMap_sublevel hball hf hk hε]
  exact hh s

/-- **A homotopy of maps of pairs into `χ ∘ h` forces `h` to preserve the boundary sphere.** Let
`χ` be the characteristic map of the cell of a normal-form chart, with `0 < ε`, and let `h` be a
self-map of the disc. If `K` is a homotopy from some map `g : D^k → M_{c+ε}` to `χ ∘ h` keeping the
boundary sphere in the lower sublevel `M_{c-ε}`, then `h` sends the boundary sphere into itself.
This is the form of the hypotheses of `TauCeti.morseCellReattachment`. -/
theorem mapsTo_range_diskBoundaryInclusion_of_homotopy_morseCharacteristicMap
    {g : TopCat.disk.{u} k ⟶ TopCat.of {x | f x ≤ c + ε}}
    (K : g.hom.Homotopy (h ≫ ψ.morseCharacteristicMap hk hε.le hball hf).hom)
    (hK : ∀ t (s : TopCat.diskBoundary.{u} k),
      f (K (t, TopCat.diskBoundaryInclusion k s)) ≤ c - ε) :
    MapsTo h (range (TopCat.diskBoundaryInclusion k)) (range (TopCat.diskBoundaryInclusion k)) :=
  mapsTo_range_diskBoundaryInclusion_of_morseCharacteristicMap_le hk hε hball hf fun s ↦ by
    simpa [K.apply_one] using hK 1 s

end Boundary

section Orientation

variable {M : Type u} [TopologicalSpace M] {n : ℕ} {f : M → ℝ} {c ε : ℝ}
  {ψ₀ ψ₁ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))} {k : ℕ} (hk : k ≤ n)
  (hε : 0 ≤ ε) (hball₀ : closedBall 0 √ε ⊆ ψ₀.target) (hball₁ : closedBall 0 √ε ⊆ ψ₁.target)
  (hf₀ : ∀ y ∈ ψ₀.source, f y = c + ∑ j, (if j.val < k then -1 else 1) * ψ₀ y j ^ 2)
  (hf₁ : ∀ y ∈ ψ₁.source, f y = c + ∑ j, (if j.val < k then -1 else 1) * ψ₁ y j ^ 2)
  {g : EuclideanSpace ℝ (Fin k) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin k)}

/-- **An orientation-preserving change of parametrization of a Morse cell can be removed.** Let
`χ₀` and `χ₁` be the characteristic maps of the cells of two normal-form charts of the same index
`k`, and let `g` be a linear isometry of `ℝᵏ` with `det g = 1`. A homotopy of maps of pairs from
`χ₁` to `χ₀ ∘ g`, keeping the boundary sphere in the lower sublevel `M_{c-ε}`, can be replaced by
a homotopy of maps of pairs from `χ₁` to `χ₀` with the same property. Then
`TauCeti.morseCellReattachment` applies with the identity of the disc. -/
theorem exists_homotopy_morseCharacteristicMap_of_det_eq_one (hg : LinearMap.det g.toLinearMap = 1)
    (K : (ψ₁.morseCharacteristicMap hk hε hball₁ hf₁).hom.Homotopy
      (g.diskMap ≫ ψ₀.morseCharacteristicMap hk hε hball₀ hf₀).hom)
    (hK : ∀ t (s : TopCat.diskBoundary.{u} k),
      f (K (t, TopCat.diskBoundaryInclusion k s)) ≤ c - ε) :
    ∃ K' : (ψ₁.morseCharacteristicMap hk hε hball₁ hf₁).hom.Homotopy
        (ψ₀.morseCharacteristicMap hk hε hball₀ hf₀).hom,
      ∀ t (s : TopCat.diskBoundary.{u} k),
        f (K' (t, TopCat.diskBoundaryInclusion k s)) ≤ c - ε := by
  obtain ⟨H, hH⟩ := TauCeti.TopCat.exists_homotopy_diskMap_comp_of_det_eq_one hg
    (ψ₀.morseCharacteristicMap hk hε hball₀ hf₀) (S := {x | f x ≤ c - ε}) fun s ↦ by
      rw [mem_ofPred_eq, OpenPartialHomeomorph.coe_morseCharacteristicMap_diskBoundaryInclusion]
      exact (ψ₀.morseAttachingMap hk hε hball₀ hf₀ s).2
  refine ⟨K.trans H, fun t s ↦ ?_⟩
  rw [ContinuousMap.Homotopy.trans_apply]
  split_ifs
  exacts [hK _ s, hH _ s]

/-- **A homotopy of characteristic maps restricts to the attaching maps.** If the characteristic
map `χ₁` of one normal-form chart is homotopic, as a map of pairs into `(M_{c+ε}, M_{c-ε})`, to
`χ₀ ∘ g` for the characteristic map `χ₀` of another chart of the same index and a linear isometry
`g`, then the attaching map `α₁ : ∂D^k → M_{c-ε}` is homotopic to `α₀ ∘ g`, where `g` acts on the
boundary sphere by `LinearIsometryEquiv.diskBoundaryMap`. -/
theorem homotopic_morseAttachingMap_diskBoundaryMap_comp
    (K : (ψ₁.morseCharacteristicMap hk hε hball₁ hf₁).hom.Homotopy
      (g.diskMap ≫ ψ₀.morseCharacteristicMap hk hε hball₀ hf₀).hom)
    (hK : ∀ t (s : TopCat.diskBoundary.{u} k),
      f (K (t, TopCat.diskBoundaryInclusion k s)) ≤ c - ε) :
    (ψ₁.morseAttachingMap hk hε hball₁ hf₁).hom.Homotopic
      (g.diskBoundaryMap ≫ ψ₀.morseAttachingMap hk hε hball₀ hf₀).hom :=
  ⟨{ toFun p := ⟨K (p.1, TopCat.diskBoundaryInclusion k p.2), hK p.1 p.2⟩
     continuous_toFun := (continuous_subtype_val.comp (K.continuous.comp
       (continuous_fst.prodMk ((TopCat.diskBoundaryInclusion k).hom.continuous.comp
         continuous_snd)))).subtype_mk _
     map_zero_left s := Subtype.ext ((congrArg Subtype.val (K.apply_zero _)).trans
       (OpenPartialHomeomorph.coe_morseCharacteristicMap_diskBoundaryInclusion hball₁ hf₁ hk hε s))
     map_one_left s := Subtype.ext ((congrArg Subtype.val (K.apply_one _)).trans
       ((congrArg (fun w ↦ (ψ₀.morseCharacteristicMap hk hε hball₀ hf₀ w : M))
         (LinearIsometryEquiv.diskMap_diskBoundaryInclusion g s)).trans
         (OpenPartialHomeomorph.coe_morseCharacteristicMap_diskBoundaryInclusion hball₀ hf₀ hk hε
           _))) }⟩

/-- **Orientation-preserving changes of chart give homotopic attaching maps.** If the
characteristic map `χ₁` of one normal-form chart is homotopic, as a map of pairs into
`(M_{c+ε}, M_{c-ε})`, to `χ₀ ∘ g` for the characteristic map `χ₀` of another chart of the same
index and a linear isometry `g` with `det g = 1`, then the two attaching maps
`∂D^k → M_{c-ε}` are homotopic. -/
theorem homotopic_morseAttachingMap_of_det_eq_one (hg : LinearMap.det g.toLinearMap = 1)
    (K : (ψ₁.morseCharacteristicMap hk hε hball₁ hf₁).hom.Homotopy
      (g.diskMap ≫ ψ₀.morseCharacteristicMap hk hε hball₀ hf₀).hom)
    (hK : ∀ t (s : TopCat.diskBoundary.{u} k),
      f (K (t, TopCat.diskBoundaryInclusion k s)) ≤ c - ε) :
    (ψ₁.morseAttachingMap hk hε hball₁ hf₁).hom.Homotopic
      (ψ₀.morseAttachingMap hk hε hball₀ hf₀).hom := by
  have h := (ContinuousMap.Homotopic.refl (ψ₀.morseAttachingMap hk hε hball₀ hf₀).hom).comp
    (TopCat.homotopic_diskBoundaryMap_id_of_det_eq_one.{u} hg)
  rw [ContinuousMap.comp_id, ← TopCat.hom_comp] at h
  exact (homotopic_morseAttachingMap_diskBoundaryMap_comp hk hε hball₀ hball₁ hf₀ hf₁ K hK).trans h

end Orientation

section IndexOne

variable {M : Type u} [TopologicalSpace M] {n : ℕ} {f : M → ℝ} {c ε : ℝ}
  {ψ₀ ψ₁ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))} (hk : 1 ≤ n)
  (hε : 0 ≤ ε) (hball₀ : closedBall 0 √ε ⊆ ψ₀.target) (hball₁ : closedBall 0 √ε ⊆ ψ₁.target)
  (hf₀ : ∀ y ∈ ψ₀.source, f y = c + ∑ j, (if j.val < 1 then -1 else 1) * ψ₀ y j ^ 2)
  (hf₁ : ∀ y ∈ ψ₁.source, f y = c + ∑ j, (if j.val < 1 then -1 else 1) * ψ₁ y j ^ 2)
  {g : EuclideanSpace ℝ (Fin 1) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 1)}

/-- **An orientation-reversing change of chart swaps the attaching points of a cell of index
`1`.** If the characteristic map `χ₁` of one normal-form chart of index `1` is homotopic, as a map
of pairs into `(M_{c+ε}, M_{c-ε})`, to `χ₀ ∘ g` for the characteristic map `χ₀` of another and a
linear isometry `g` of `ℝ` with `det g = -1`, then the attaching map `α₁` is homotopic to `α₀`
composed with the antipodal map of `∂D¹ = {-1, 1}`, which swaps the two points. -/
theorem homotopic_morseAttachingMap_diskBoundaryNeg_comp_of_det_eq_neg_one
    (hg : LinearMap.det g.toLinearMap = -1)
    (K : (ψ₁.morseCharacteristicMap hk hε hball₁ hf₁).hom.Homotopy
      (g.diskMap ≫ ψ₀.morseCharacteristicMap hk hε hball₀ hf₀).hom)
    (hK : ∀ t (s : TopCat.diskBoundary.{u} 1),
      f (K (t, TopCat.diskBoundaryInclusion 1 s)) ≤ c - ε) :
    (ψ₁.morseAttachingMap hk hε hball₁ hf₁).hom.Homotopic
      (diskBoundaryNeg 1 ≫ ψ₀.morseAttachingMap hk hε hball₀ hf₀).hom := by
  simpa only [TopCat.diskBoundaryMap_eq_diskBoundaryNeg_of_det_eq_neg_one hg] using
    homotopic_morseAttachingMap_diskBoundaryMap_comp hk hε hball₀ hball₁ hf₀ hf₁ K hK

end IndexOne

end TauCeti
