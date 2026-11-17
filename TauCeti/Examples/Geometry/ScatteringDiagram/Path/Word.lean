/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antigravity (Gemini 4 Carbon)
-/
module

public import TauCeti.Geometry.ScatteringDiagram.Path.Word
import Mathlib.GroupTheory.FreeGroup.Reduce
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Worked example: crossing word of the square loop around the four half-axes in `ℝ × ℝ`

`TauCeti.FourHalfAxesExample` evaluates `Quiver.Path.crossingWord` on the counterclockwise boundary
`squareLoop` of `[-1, 1]²` in `ℝ × ℝ` across the four closed coordinate half-axes `halfAxis`
cooriented by `halfAxisNormal`:
* `singularSupport_halfAxis` identifies the singular support of `halfAxis` with `{(0, 0)}`;
* `crossingWord_squareLoop` computes the crossing word
  `(of 0)⁻¹ * ((of 3)⁻¹ * (of 2 * of 1))` in `FreeGroup (Fin 4)`;
* `crossingWord_squareLoop_restrict_posX` and `crossingWord_squareLoop_restrict_posX_ne_one` verify
  that restricting along `WallComplement.restrictPrefunctor` to the positive `x`-half-axis yields
  `(of ())⁻¹ ≠ 1`;
* `lift_oppositeHalfAxisLabel_crossingWord_squareLoop` and
  `lift_oppositeHalfAxisLabel_crossingWord_squareLoop_ne_one` check that identifying opposite
  half-axes via `oppositeHalfAxisLabel` produces the nontrivial commutator
  `(of false)⁻¹ * ((of true)⁻¹ * (of false * of true)) ≠ 1` in `FreeGroup Bool`.

## References

* M. Kontsevich and Y. Soibelman, *Wall-crossing structures in Donaldson–Thomas invariants,
  integrable systems and Mirror Symmetry*, §2.1.
* M. Gross, *Tropical Geometry and Mirror Symmetry*, §6.2.
-/

public section

noncomputable section

open Set

namespace TauCeti.FourHalfAxesExample

/-- The four closed coordinate half-axes in `ℝ × ℝ`:
`0` is `{(x, 0) | 0 ≤ x}`, `1` is `{(0, y) | 0 ≤ y}`,
`2` is `{(x, 0) | x ≤ 0}`, and `3` is `{(0, y) | y ≤ 0}`. -/
def halfAxis : Fin 4 → Set (ℝ × ℝ)
  | 0 => {p | 0 ≤ p.1 ∧ p.2 = 0}
  | 1 => {p | p.1 = 0 ∧ 0 ≤ p.2}
  | 2 => {p | p.1 ≤ 0 ∧ p.2 = 0}
  | 3 => {p | p.1 = 0 ∧ p.2 ≤ 0}

@[simp]
theorem halfAxis_zero : halfAxis 0 = {p | 0 ≤ p.1 ∧ p.2 = 0} := (rfl)

@[simp]
theorem halfAxis_one : halfAxis 1 = {p | p.1 = 0 ∧ 0 ≤ p.2} := (rfl)

@[simp]
theorem halfAxis_two : halfAxis 2 = {p | p.1 ≤ 0 ∧ p.2 = 0} := (rfl)

@[simp]
theorem halfAxis_three : halfAxis 3 = {p | p.1 = 0 ∧ p.2 ≤ 0} := (rfl)

/-- Standard coorientations of the four half-axes: `dy` on horizontal half-axes (`0`, `2`) and
`dx` on vertical half-axes (`1`, `3`). -/
def halfAxisNormal : Fin 4 → (ℝ × ℝ) →ₗ[ℝ] ℝ
  | 0 => LinearMap.snd ℝ ℝ ℝ
  | 1 => LinearMap.fst ℝ ℝ ℝ
  | 2 => LinearMap.snd ℝ ℝ ℝ
  | 3 => LinearMap.fst ℝ ℝ ℝ

@[simp]
theorem halfAxisNormal_zero : halfAxisNormal 0 = LinearMap.snd ℝ ℝ ℝ := (rfl)

@[simp]
theorem halfAxisNormal_one : halfAxisNormal 1 = LinearMap.fst ℝ ℝ ℝ := (rfl)

@[simp]
theorem halfAxisNormal_two : halfAxisNormal 2 = LinearMap.snd ℝ ℝ ℝ := (rfl)

@[simp]
theorem halfAxisNormal_three : halfAxisNormal 3 = LinearMap.fst ℝ ℝ ℝ := (rfl)

private theorem origin_notMem_intrinsicInterior (i : Fin 4) :
    ((0 : ℝ), (0 : ℝ)) ∉ intrinsicInterior ℝ (halfAxis i) := by
  intro h0
  fin_cases i
  · have h1 := TauCeti.eq_zero_of_nonneg_of_mem_intrinsicInterior
      (g := (LinearMap.fst ℝ ℝ ℝ).toAffineMap) (fun _ (hp : _ ∈ halfAxis 0) => hp.1) h0 rfl
      (show ((1 : ℝ), (0 : ℝ)) ∈ halfAxis 0 from ⟨zero_le_one, rfl⟩)
    exact one_ne_zero h1
  · have h1 := TauCeti.eq_zero_of_nonneg_of_mem_intrinsicInterior
      (g := (LinearMap.snd ℝ ℝ ℝ).toAffineMap) (fun _ (hp : _ ∈ halfAxis 1) => hp.2) h0 rfl
      (show ((0 : ℝ), (1 : ℝ)) ∈ halfAxis 1 from ⟨rfl, zero_le_one⟩)
    exact one_ne_zero h1
  · have h1 := TauCeti.eq_zero_of_nonneg_of_mem_intrinsicInterior
      (g := (-(LinearMap.fst ℝ ℝ ℝ)).toAffineMap)
      (fun _ (hp : _ ∈ halfAxis 2) => neg_nonneg.mpr hp.1) h0 (by simp)
      (show ((-1 : ℝ), (0 : ℝ)) ∈ halfAxis 2 from ⟨by norm_num, rfl⟩)
    norm_num at h1
  · have h1 := TauCeti.eq_zero_of_nonneg_of_mem_intrinsicInterior
      (g := (-(LinearMap.snd ℝ ℝ ℝ)).toAffineMap)
      (fun _ (hp : _ ∈ halfAxis 3) => neg_nonneg.mpr hp.2) h0 (by simp)
      (show ((0 : ℝ), (-1 : ℝ)) ∈ halfAxis 3 from ⟨rfl, by norm_num⟩)
    norm_num at h1

/-- Distinct coordinate half-axes meet only at `(0, 0)`, which lies in none of their intrinsic
interiors, so the four half-axes have pairwise disjoint intrinsic interiors. -/
theorem pairwise_disjoint_intrinsicInterior_halfAxis :
    Pairwise fun i j =>
      Disjoint (intrinsicInterior ℝ (halfAxis i)) (intrinsicInterior ℝ (halfAxis j)) := by
  intro i j hij
  refine Set.disjoint_left.mpr fun p hpi hpj => origin_notMem_intrinsicInterior i ?_
  have hi := intrinsicInterior_subset hpi
  have hj := intrinsicInterior_subset hpj
  have hp0 : p = (0, 0) := by
    fin_cases i <;> fin_cases j <;> simp at hi hj
    all_goals first | contradiction | (ext <;> linarith)
  exact hp0 ▸ hpi

private theorem direction_halfAxis_le (i : Fin 4) :
    (affineSpan ℝ (halfAxis i)).direction ≤ LinearMap.ker (halfAxisNormal i) := by
  rw [direction_affineSpan, vectorSpan_def, Submodule.span_le]
  rintro _ ⟨a, ha, b, hb, rfl⟩
  fin_cases i <;> simp_all

private theorem halfAxisNormal_eq_zero_of_mem_affineSpan (i : Fin 4) {q : ℝ × ℝ}
    (hq : q ∈ affineSpan ℝ (halfAxis i)) : halfAxisNormal i q = 0 := by
  have h0 : (0 : ℝ × ℝ) ∈ affineSpan ℝ (halfAxis i) :=
    subset_affineSpan ℝ _ (by fin_cases i <;> simp)
  have hv := direction_halfAxis_le i
    (direction_affineSpan ℝ (halfAxis i) ▸
      vsub_mem_vectorSpan_of_mem_affineSpan_of_mem_affineSpan hq h0)
  simpa using LinearMap.mem_ker.mp hv

private theorem mem_intrinsicInterior_halfAxis_of_ne_origin {i : Fin 4} {p : ℝ × ℝ}
    (hp : p ∈ halfAxis i) (hne : p ≠ (0, 0)) : p ∈ intrinsicInterior ℝ (halfAxis i) := by
  rw [TauCeti.mem_intrinsicInterior_iff_eventually]
  refine ⟨subset_affineSpan ℝ _ hp, ?_⟩
  fin_cases i
  · have hp1 : 0 < p.1 := lt_of_le_of_ne hp.1 fun h0 => hne (Prod.ext h0.symm hp.2)
    filter_upwards [(isOpen_lt continuous_const continuous_fst).mem_nhds hp1] with q hq1 hqA
    exact ⟨hq1.le, halfAxisNormal_eq_zero_of_mem_affineSpan 0 hqA⟩
  · have hp2 : 0 < p.2 := lt_of_le_of_ne hp.2 fun h0 => hne (Prod.ext hp.1 h0.symm)
    filter_upwards [(isOpen_lt continuous_const continuous_snd).mem_nhds hp2] with q hq2 hqA
    exact ⟨halfAxisNormal_eq_zero_of_mem_affineSpan 1 hqA, hq2.le⟩
  · have hp1 : p.1 < 0 := lt_of_le_of_ne hp.1 fun h0 => hne (Prod.ext h0 hp.2)
    filter_upwards [(isOpen_lt continuous_fst continuous_const).mem_nhds hp1] with q hq1 hqA
    exact ⟨hq1.le, halfAxisNormal_eq_zero_of_mem_affineSpan 2 hqA⟩
  · have hp2 : p.2 < 0 := lt_of_le_of_ne hp.2 fun h0 => hne (Prod.ext hp.1 h0)
    filter_upwards [(isOpen_lt continuous_snd continuous_const).mem_nhds hp2] with q hq2 hqA
    exact ⟨halfAxisNormal_eq_zero_of_mem_affineSpan 3 hqA, hq2.le⟩

/-- The singular support of the four coordinate half-axes is the origin `{(0, 0)}`. -/
@[simp]
theorem singularSupport_halfAxis : singularSupport halfAxis = {(0, 0)} := by
  refine Subset.antisymm (fun p hp => ?_) (Set.singleton_subset_iff.mpr ?_)
  · simp only [Set.mem_singleton_iff]
    by_contra hne
    rcases mem_singularSupport.mp hp with ⟨i, hfr⟩ | ⟨i, j, hdir, hi, hj⟩
    · have hcl : IsClosed (halfAxis i) := by
        fin_cases i
        · exact (isClosed_le continuous_const continuous_fst).inter
            (isClosed_eq continuous_snd continuous_const)
        · exact (isClosed_eq continuous_fst continuous_const).inter
            (isClosed_le continuous_const continuous_snd)
        · exact (isClosed_le continuous_fst continuous_const).inter
            (isClosed_eq continuous_snd continuous_const)
        · exact (isClosed_eq continuous_fst continuous_const).inter
            (isClosed_le continuous_snd continuous_const)
      have hp_mem : p ∈ halfAxis i := intrinsicFrontier_subset hcl hfr
      rw [← intrinsicClosure_sdiff_intrinsicInterior (𝕜 := ℝ)] at hfr
      exact hfr.2 (mem_intrinsicInterior_halfAxis_of_ne_origin hp_mem hne)
    · have hij : i ≠ j := fun heq => hdir (heq ▸ rfl)
      exact Set.disjoint_left.mp (pairwise_disjoint_intrinsicInterior_halfAxis hij)
        (mem_intrinsicInterior_halfAxis_of_ne_origin hi hne)
        (mem_intrinsicInterior_halfAxis_of_ne_origin hj hne)
  · refine mem_singularSupport.mpr (.inl ⟨0, ?_⟩)
    rw [← intrinsicClosure_sdiff_intrinsicInterior (𝕜 := ℝ)]
    exact ⟨subset_intrinsicClosure (show ((0 : ℝ), (0 : ℝ)) ∈ halfAxis 0 from ⟨le_rfl, rfl⟩),
      origin_notMem_intrinsicInterior 0⟩

/-- Top-right corner `(1, 1)` in the complement of the four half-axes. -/
def vPP : WallComplement halfAxis :=
  ⟨(1, 1), fun i h => by fin_cases i <;> simp at h⟩

@[simp]
theorem vPP_val : vPP.val = (1, 1) := (rfl)

/-- Top-left corner `(-1, 1)`. -/
def vNP : WallComplement halfAxis :=
  ⟨(-1, 1), fun i h => by fin_cases i <;> simp at h⟩

@[simp]
theorem vNP_val : vNP.val = (-1, 1) := (rfl)

/-- Bottom-left corner `(-1, -1)`. -/
def vNN : WallComplement halfAxis :=
  ⟨(-1, -1), fun i h => by fin_cases i <;> simp at h⟩

@[simp]
theorem vNN_val : vNN.val = (-1, -1) := (rfl)

/-- Bottom-right corner `(1, -1)`. -/
def vPN : WallComplement halfAxis :=
  ⟨(1, -1), fun i h => by fin_cases i <;> simp at h⟩

@[simp]
theorem vPN_val : vPN.val = (1, -1) := (rfl)

private theorem crossings_eq_singleton {u v : WallComplement halfAxis} {i₀ : Fin 4} {t₀ : ℝ}
    (honly : ∀ i t, AffineMap.lineMap u.val v.val t ∈ halfAxis i → i = i₀ ∧ t = t₀)
    (ht₀ : t₀ ∈ Set.Icc (0 : ℝ) 1)
    (hi₀ : AffineMap.lineMap u.val v.val t₀ ∈ halfAxis i₀) :
    WallComplement.crossings u v = {(i₀, t₀)} := by
  ext ⟨i, t⟩
  simp only [WallComplement.mem_crossings, Set.mem_singleton_iff, Prod.mk.injEq]
  exact ⟨fun ⟨_, hi⟩ => honly i t hi, by rintro ⟨rfl, rfl⟩; exact ⟨ht₀, hi₀⟩⟩

private theorem crossings_horizontal {u v : WallComplement halfAxis} {a b : ℝ}
    (ha : a ≠ 0) (hb : b ≠ 0) (hu : u.val = (a, b)) (hv : v.val = (-a, b)) :
    WallComplement.crossings u v = {(if 0 < b then 1 else 3, (1 / 2 : ℝ))} := by
  refine crossings_eq_singleton ?_ (by norm_num) ?_
  · intro i t hi
    have hpt : AffineMap.lineMap u.val v.val t = ((1 - 2 * t) * a, b) := by
      rw [AffineMap.lineMap_apply_module', hu, hv]
      ext <;> dsimp <;> ring
    rw [hpt] at hi
    fin_cases i
    · exact (hb hi.2).elim
    · have ht : t = 1 / 2 := by
        rcases mul_eq_zero.mp hi.1 with h | h
        · linarith
        · exact (ha h).elim
      exact ⟨by rw [ite_eq_left (lt_of_le_of_ne hi.2 hb.symm)]; rfl, ht⟩
    · exact (hb hi.2).elim
    · have ht : t = 1 / 2 := by
        rcases mul_eq_zero.mp hi.1 with h | h
        · linarith
        · exact (ha h).elim
      exact ⟨by rw [ite_eq_right (not_lt.mpr hi.2)]; rfl, ht⟩
  · have hpt : AffineMap.lineMap u.val v.val (1 / 2 : ℝ) = (0, b) := by
      rw [AffineMap.lineMap_apply_module', hu, hv]
      ext <;> dsimp <;> ring
    rw [hpt]
    split_ifs with hpos
    · exact ⟨rfl, hpos.le⟩
    · exact ⟨rfl, le_of_not_gt hpos⟩

private theorem crossings_vertical {u v : WallComplement halfAxis} {a b : ℝ}
    (ha : a ≠ 0) (hb : b ≠ 0) (hu : u.val = (a, b)) (hv : v.val = (a, -b)) :
    WallComplement.crossings u v = {(if 0 < a then 0 else 2, (1 / 2 : ℝ))} := by
  refine crossings_eq_singleton ?_ (by norm_num) ?_
  · intro i t hi
    have hpt : AffineMap.lineMap u.val v.val t = (a, (1 - 2 * t) * b) := by
      rw [AffineMap.lineMap_apply_module', hu, hv]
      ext <;> dsimp <;> ring
    rw [hpt] at hi
    fin_cases i
    · have ht : t = 1 / 2 := by
        rcases mul_eq_zero.mp hi.2 with h | h
        · linarith
        · exact (hb h).elim
      exact ⟨by rw [ite_eq_left (lt_of_le_of_ne hi.1 ha.symm)]; rfl, ht⟩
    · exact (ha hi.1).elim
    · have ht : t = 1 / 2 := by
        rcases mul_eq_zero.mp hi.2 with h | h
        · linarith
        · exact (hb h).elim
      exact ⟨by rw [ite_eq_right (not_lt.mpr hi.1)]; rfl, ht⟩
    · exact (ha hi.1).elim
  · have hpt : AffineMap.lineMap u.val v.val (1 / 2 : ℝ) = (a, 0) := by
      rw [AffineMap.lineMap_apply_module', hu, hv]
      ext <;> dsimp <;> ring
    rw [hpt]
    split_ifs with hpos
    · exact ⟨hpos.le, rfl⟩
    · exact ⟨le_of_not_gt hpos, rfl⟩

@[simp]
theorem crossings_segTop : WallComplement.crossings vPP vNP = {(1, (1 / 2 : ℝ))} := by
  simpa using crossings_horizontal (u := vPP) (v := vNP) one_ne_zero one_ne_zero rfl rfl

@[simp]
theorem crossings_segLeft : WallComplement.crossings vNP vNN = {(2, (1 / 2 : ℝ))} := by
  rw [crossings_vertical (u := vNP) (v := vNN) (by norm_num) one_ne_zero rfl rfl,
    ite_eq_right (by norm_num)]

@[simp]
theorem crossings_segBot : WallComplement.crossings vNN vPN = {(3, (1 / 2 : ℝ))} := by
  rw [crossings_horizontal (u := vNN) (v := vPN) (by norm_num) (by norm_num) rfl
      (by simp [vPN_val]),
    ite_eq_right (by norm_num)]

@[simp]
theorem crossings_segRight : WallComplement.crossings vPN vPP = {(0, (1 / 2 : ℝ))} := by
  simpa using crossings_vertical (u := vPN) (v := vPP) one_ne_zero (by norm_num) rfl
    (by simp [vPP_val])

/-- Any straight segment between off-wall points missing `(0, 0)` is admissible for `halfAxis`. -/
def mkAdmissibleEdge {u v : WallComplement halfAxis}
    (h0 : ∀ t ∈ Set.Icc (0 : ℝ) 1, AffineMap.lineMap u.val v.val t ≠ (0, 0)) : u ⟶ v :=
  ⟨(convex_segment u.val v.val).admissibleSegment_of_disjoint_singularSupport
    (by
      rw [singularSupport_halfAxis, Set.disjoint_singleton_right, segment_eq_image_lineMap]
      rintro ⟨t, ht, heq⟩
      exact h0 t ht heq)
    (left_mem_segment ℝ u.val v.val) (right_mem_segment ℝ u.val v.val)⟩

/-- Top edge `(1, 1) → (-1, 1)` of the counterclockwise square loop. -/
def segTop : vPP ⟶ vNP :=
  mkAdmissibleEdge fun _ _ h => by
    simpa [AffineMap.lineMap_apply_module'] using congrArg Prod.snd h

/-- Left edge `(-1, 1) → (-1, -1)` of the counterclockwise square loop. -/
def segLeft : vNP ⟶ vNN :=
  mkAdmissibleEdge fun _ _ h => by
    simpa [AffineMap.lineMap_apply_module'] using congrArg Prod.fst h

/-- Bottom edge `(-1, -1) → (1, -1)` of the counterclockwise square loop. -/
def segBot : vNN ⟶ vPN :=
  mkAdmissibleEdge fun _ _ h => by
    simpa [AffineMap.lineMap_apply_module'] using congrArg Prod.snd h

/-- Right edge `(1, -1) → (1, 1)` of the counterclockwise square loop. -/
def segRight : vPN ⟶ vPP :=
  mkAdmissibleEdge fun _ _ h => by
    simpa [AffineMap.lineMap_apply_module'] using congrArg Prod.fst h

/-- The counterclockwise boundary of `[-1, 1]²` based at `(1, 1)`. -/
def squareLoop : AdmissiblePLPath vPP vPP :=
  (((segTop.toPath.cons segLeft).cons segBot).cons segRight)

/-- Explicit edge decomposition of `squareLoop`. -/
theorem squareLoop_def :
    squareLoop = (((segTop.toPath.cons segLeft).cons segBot).cons segRight) :=
  (rfl)

/-- The counterclockwise square loop around `(0, 0)` crosses the positive `y`-, negative `x`-,
negative `y`-, and positive `x`-half-axes in order, producing the crossing word
`(of 0)⁻¹ * ((of 3)⁻¹ * (of 2 * of 1))` in `FreeGroup (Fin 4)`. -/
theorem crossingWord_squareLoop :
    squareLoop.crossingWord halfAxisNormal pairwise_disjoint_intrinsicInterior_halfAxis =
      (FreeGroup.of 0)⁻¹ * ((FreeGroup.of 3)⁻¹ * (FreeGroup.of 2 * FreeGroup.of 1)) := by
  have hTop : ¬ 0 < halfAxisNormal 1 (vNP.val - vPP.val) := by norm_num
  have hLeft : ¬ 0 < halfAxisNormal 2 (vNN.val - vNP.val) := by norm_num
  have hBot : 0 < halfAxisNormal 3 (vPN.val - vNN.val) := by norm_num
  have hRight : 0 < halfAxisNormal 0 (vPP.val - vPN.val) := by norm_num
  simp only [squareLoop_def, Quiver.Path.crossingWord_cons, Quiver.Path.crossingWord_toPath,
    WallComplement.segmentCrossingWord_of_crossings_eq_singleton _ _ segTop crossings_segTop,
    WallComplement.segmentCrossingWord_of_crossings_eq_singleton _ _ segLeft crossings_segLeft,
    WallComplement.segmentCrossingWord_of_crossings_eq_singleton _ _ segBot crossings_segBot,
    WallComplement.segmentCrossingWord_of_crossings_eq_singleton _ _ segRight crossings_segRight,
    ite_eq_right hTop, ite_eq_right hLeft, ite_eq_left hBot, ite_eq_left hRight, zpow_one,
    zpow_neg_one]

/-- Lifting `squareLoop.crossingWord` along `f : Fin 4 → G` multiplies the four generator images in
counterclockwise left-action order. -/
theorem lift_crossingWord_squareLoop {G : Type*} [Group G] (f : Fin 4 → G) :
    FreeGroup.lift f
        (squareLoop.crossingWord halfAxisNormal pairwise_disjoint_intrinsicInterior_halfAxis) =
      (f 0)⁻¹ * ((f 3)⁻¹ * (f 2 * f 1)) := by
  rw [crossingWord_squareLoop]
  simp

/-- Restricting the four half-axes to the single positive `x`-half-axis `{(x, 0) | 0 ≤ x}`
cooriented by `dy` sends the counterclockwise square loop's crossing word to `(of ())⁻¹`. -/
theorem crossingWord_squareLoop_restrict_posX :
    ((WallComplement.restrictPrefunctor halfAxis (fun _ : Unit => (0 : Fin 4))).mapPath
        squareLoop).crossingWord (halfAxisNormal ∘ fun _ : Unit => 0)
        (pairwise_disjoint_intrinsicInterior_halfAxis.comp_of_injective
          fun _ _ _ => Subsingleton.elim _ _) =
      (FreeGroup.of ())⁻¹ := by
  have hinj : Function.Injective (fun _ : Unit => (0 : Fin 4)) := fun _ _ _ => Subsingleton.elim _ _
  rw [Quiver.Path.crossingWord_restrictPrefunctor halfAxisNormal
      pairwise_disjoint_intrinsicInterior_halfAxis hinj squareLoop,
    lift_crossingWord_squareLoop]
  simp [hinj.extend_apply FreeGroup.of 1 (), Function.extend_apply']

/-- Restricting `squareLoop` to the positive `x`-half-axis produces a nontrivial crossing word,
distinct from the constant loop's word `1`. -/
theorem crossingWord_squareLoop_restrict_posX_ne_one :
    ((WallComplement.restrictPrefunctor halfAxis (fun _ : Unit => (0 : Fin 4))).mapPath
        squareLoop).crossingWord (halfAxisNormal ∘ fun _ : Unit => 0)
        (pairwise_disjoint_intrinsicInterior_halfAxis.comp_of_injective
          fun _ _ _ => Subsingleton.elim _ _) ≠ 1 := by
  rw [crossingWord_squareLoop_restrict_posX]
  exact inv_ne_one.mpr (FreeGroup.of_ne_one ())

/-- Generator map identifying opposite coordinate half-axes into horizontal (`false`) and vertical
(`true`) labels in `FreeGroup Bool`. -/
def oppositeHalfAxisLabel : Fin 4 → FreeGroup Bool
  | 0 => FreeGroup.of false
  | 1 => FreeGroup.of true
  | 2 => FreeGroup.of false
  | 3 => FreeGroup.of true

@[simp]
theorem oppositeHalfAxisLabel_zero : oppositeHalfAxisLabel 0 = FreeGroup.of false := (rfl)

@[simp]
theorem oppositeHalfAxisLabel_one : oppositeHalfAxisLabel 1 = FreeGroup.of true := (rfl)

@[simp]
theorem oppositeHalfAxisLabel_two : oppositeHalfAxisLabel 2 = FreeGroup.of false := (rfl)

@[simp]
theorem oppositeHalfAxisLabel_three : oppositeHalfAxisLabel 3 = FreeGroup.of true := (rfl)

/-- Identifying opposite half-axes via `oppositeHalfAxisLabel` maps the square loop's crossing word
to the commutator `(of false)⁻¹ * ((of true)⁻¹ * (of false * of true))` in `FreeGroup Bool`. -/
theorem lift_oppositeHalfAxisLabel_crossingWord_squareLoop :
    FreeGroup.lift oppositeHalfAxisLabel
        (squareLoop.crossingWord halfAxisNormal pairwise_disjoint_intrinsicInterior_halfAxis) =
      (FreeGroup.of false)⁻¹ *
        ((FreeGroup.of true)⁻¹ * (FreeGroup.of false * FreeGroup.of true)) := by
  simp [lift_crossingWord_squareLoop]

/-- Under `oppositeHalfAxisLabel`, the square loop's crossing word is nontrivial in
`FreeGroup Bool`. -/
theorem lift_oppositeHalfAxisLabel_crossingWord_squareLoop_ne_one :
    FreeGroup.lift oppositeHalfAxisLabel
        (squareLoop.crossingWord halfAxisNormal pairwise_disjoint_intrinsicInterior_halfAxis) ≠
      1 := by
  rw [lift_oppositeHalfAxisLabel_crossingWord_squareLoop]
  intro hcomm_eq
  have hab : FreeGroup.of false * FreeGroup.of true = FreeGroup.of true * FreeGroup.of false := by
    calc
      FreeGroup.of false * FreeGroup.of true =
          FreeGroup.of true * FreeGroup.of false *
            ((FreeGroup.of false)⁻¹ *
              ((FreeGroup.of true)⁻¹ * (FreeGroup.of false * FreeGroup.of true))) := by
        group
      _ = FreeGroup.of true * FreeGroup.of false := by rw [hcomm_eq, mul_one]
  exact Bool.false_ne_true (FreeGroup.eq_of_commute_of_of hab)

end TauCeti.FourHalfAxesExample
