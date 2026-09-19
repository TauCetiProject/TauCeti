/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Convex
public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import Mathlib.Analysis.Normed.Module.Connected
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.Topology.Compactification.OnePoint.Basic
public import TauCeti.AlgebraicTopology.SemilocallySimplyConnected.Basic
public import TauCeti.Topology.Algebra.Module.LocallyConvex

/-!
# The thrice-punctured sphere

The thrice-punctured sphere `ℙ¹(ℂ) ∖ {0, 1, ∞}` is the base of the three-point covers classified
by permutation triples and dessins d'enfants. This file fixes its affine model
`TauCeti.ThricePuncturedSphere := {z : ℂ // z ≠ 0 ∧ z ≠ 1}`, together with the point-set facts the
computation of its fundamental group and the classification of its finite covers run on.

* **The space.** It is an open subset of `ℂ`, hence Hausdorff, second countable, strongly locally
  contractible, locally path-connected and semilocally simply connected; it is path-connected
  because the complement of a countable set in `ℂ` is. The inclusion into the Riemann sphere
  `OnePoint ℂ` is an open embedding whose range is the complement of `{0, 1, ∞}`, which is what
  makes the name honest.
* **The basepoint and anharmonic maps.** The basepoint is `b = 1/2`, on the real segment between
  the punctures `0` and `1`. The six anharmonic maps permuting `{0, 1, ∞}` restrict to
  self-homeomorphisms; the involution `z ↦ 1 − z` is the unique nonidentity one fixing `b`.
* **The standard punctured-disc neighbourhoods** at `0`, `1`, and `∞`, including openness,
  pairwise disjointness, and their descriptions in the respective local coordinates.
* **The standard two-set cover** by `A = {z | re z < 1}` and `B = {z | 0 < re z}`. The set `A`
  is the convex half-plane `re z < 1` with the puncture `0` removed, `B` is the half-plane
  `0 < re z` with the puncture `1` removed, and `A ∩ B` is the open vertical strip
  `0 < re z < 1`, with no point removed because both punctures lie on its boundary lines. The
  strip is convex, so `A ∩ B` is path-connected and simply connected, and it contains `b`. These
  are the hypotheses on the intersection in the Seifert–van Kampen theorem for two open sets with
  simply connected intersection, through which `π₁` of the thrice-punctured sphere is computed to
  be free of rank two.

## Main declarations

* `TauCeti.ThricePuncturedSphere`: the space `ℂ ∖ {0, 1}`.
* `TauCeti.ThricePuncturedSphere.range_coe`, `TauCeti.ThricePuncturedSphere.isOpenEmbedding_coe`:
  the open embedding into `ℂ`, with range `{0, 1}ᶜ`.
* `TauCeti.ThricePuncturedSphere.toOnePoint`, `isOpenEmbedding_toOnePoint`,
  `range_toOnePoint`: the open embedding into the Riemann sphere, with range `{0, 1, ∞}ᶜ`.
* `TauCeti.ThricePuncturedSphere.basePt`: the basepoint `1/2`.
* `TauCeti.ThricePuncturedSphere.mob01`, `mob1Inf`, `mob0Inf`, `mobRot`, `mobRotInv`: the six
  anharmonic self-homeomorphisms (including `mobId`) that permute the three punctures.
* `TauCeti.ThricePuncturedSphere.puncturedDiscZero`, `puncturedDiscOne`, `puncturedDiscInf`: the
  three pairwise-disjoint standard punctured-disc neighbourhoods.
* `TauCeti.ThricePuncturedSphere.leftOpen`, `TauCeti.ThricePuncturedSphere.rightOpen`: the open
  sets `A` and `B` of the standard cover, with `leftOpen_union_rightOpen`, `image_coe_leftOpen`,
  `image_coe_rightOpen`, `image_coe_leftOpen_inter_rightOpen`,
  `isSimplyConnected_leftOpen_inter_rightOpen` and `isPathConnected_leftOpen_inter_rightOpen`.

## References

* E. Girondo and G. González-Diez, *Introduction to Compact Riemann Surfaces and Dessins
  d'Enfants*, London Mathematical Society Student Texts 79, Cambridge University Press, 2012,
  §2.4 (the thrice-punctured sphere as the base of three-point covers).
* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Theorem 1.20 (the
  Seifert–van Kampen theorem whose hypotheses the standard cover satisfies).
-/

public section

open Set Topology OnePoint

namespace TauCeti

/-- The **thrice-punctured sphere** `ℙ¹(ℂ) ∖ {0, 1, ∞}`, in its affine model `ℂ ∖ {0, 1}`. The
point `∞` is removed by working in `ℂ`; `TauCeti.ThricePuncturedSphere.range_toOnePoint` identifies
it with the complement of `{0, 1, ∞}` in the Riemann sphere `OnePoint ℂ`. -/
abbrev ThricePuncturedSphere : Type := {z : ℂ // z ≠ 0 ∧ z ≠ 1}

namespace ThricePuncturedSphere

/-- A point of the thrice-punctured sphere is not the puncture `0`. -/
@[simp]
theorem ne_zero (z : ThricePuncturedSphere) : (z : ℂ) ≠ 0 := z.2.1

/-- A point of the thrice-punctured sphere is not the puncture `1`. -/
@[simp]
theorem ne_one (z : ThricePuncturedSphere) : (z : ℂ) ≠ 1 := z.2.2

/-- The points of `ℂ` underlying the thrice-punctured sphere are those other than `0` and `1`. -/
theorem range_coe : range ((↑) : ThricePuncturedSphere → ℂ) = {0, 1}ᶜ := by
  ext z
  simp [Subtype.range_coe_subtype, not_or]

/-- The inclusion of the thrice-punctured sphere into `ℂ` is an open embedding. -/
theorem isOpenEmbedding_coe : IsOpenEmbedding ((↑) : ThricePuncturedSphere → ℂ) :=
  (isOpen_ne.inter isOpen_ne : IsOpen {z : ℂ | z ≠ 0 ∧ z ≠ 1}).isOpenEmbedding_subtypeVal

/-- The thrice-punctured sphere is strongly locally contractible, being an open subset of `ℂ`. In
particular it is locally path-connected and semilocally simply connected. -/
instance : StronglyLocallyContractibleSpace ThricePuncturedSphere :=
  isOpenEmbedding_coe.stronglyLocallyContractibleSpace

/-- The thrice-punctured sphere is path-connected: the complement of a countable set in `ℂ` is
path-connected, since `ℂ` has real dimension two. -/
instance : PathConnectedSpace ThricePuncturedSphere := by
  rw [pathConnectedSpace_iff_univ, isOpenEmbedding_coe.isInducing.isPathConnected_iff, image_univ,
    range_coe]
  refine (Set.toFinite _).countable.isPathConnected_compl_of_one_lt_rank ?_
  rw [Complex.rank_real_complex]
  exact Nat.one_lt_ofNat

/-! ### The Riemann sphere -/

/-- The inclusion of the thrice-punctured sphere into the Riemann sphere `OnePoint ℂ`. -/
def toOnePoint (z : ThricePuncturedSphere) : OnePoint ℂ := (z : ℂ)

@[simp]
theorem toOnePoint_apply (z : ThricePuncturedSphere) : toOnePoint z = ((z : ℂ) : OnePoint ℂ) :=
  (rfl)

/-- The thrice-punctured sphere is an open subspace of the Riemann sphere. -/
theorem isOpenEmbedding_toOnePoint : IsOpenEmbedding toOnePoint :=
  OnePoint.isOpenEmbedding_coe.comp isOpenEmbedding_coe

/-- The range of the inclusion into the Riemann sphere is the complement of the three punctures
`0`, `1` and `∞`. -/
theorem range_toOnePoint :
    range toOnePoint =
      ({((0 : ℂ) : OnePoint ℂ), ((1 : ℂ) : OnePoint ℂ), ∞} : Set (OnePoint ℂ))ᶜ := by
  ext w
  induction w using OnePoint.rec with
  | infty => simp [toOnePoint]
  | coe z => simp [toOnePoint, not_or]

/-! ### The basepoint -/

/-- The basepoint `b = 1/2` of the thrice-punctured sphere, on the real segment between the
punctures `0` and `1`. -/
noncomputable def basePt : ThricePuncturedSphere :=
  ⟨1 / 2, by norm_num, by norm_num⟩

@[simp]
theorem coe_basePt : (basePt : ℂ) = 1 / 2 :=
  (rfl)

/-! ### The standard two-set cover -/

/-- The open set `A = {z | re z < 1}` of the standard two-set cover of the thrice-punctured sphere:
the half-plane `re z < 1` with the puncture `0` removed. -/
def leftOpen : Set ThricePuncturedSphere :=
  {z | (z : ℂ).re < 1}

/-- The open set `B = {z | 0 < re z}` of the standard two-set cover of the thrice-punctured sphere:
the half-plane `0 < re z` with the puncture `1` removed. -/
def rightOpen : Set ThricePuncturedSphere :=
  {z | 0 < (z : ℂ).re}

@[simp]
theorem mem_leftOpen {z : ThricePuncturedSphere} : z ∈ leftOpen ↔ (z : ℂ).re < 1 :=
  Iff.rfl

@[simp]
theorem mem_rightOpen {z : ThricePuncturedSphere} : z ∈ rightOpen ↔ 0 < (z : ℂ).re :=
  Iff.rfl

/-- The set `leftOpen` is open in the thrice-punctured sphere. -/
theorem isOpen_leftOpen : IsOpen leftOpen :=
  isOpen_lt (Complex.continuous_re.comp continuous_subtype_val) continuous_const

/-- The set `rightOpen` is open in the thrice-punctured sphere. -/
theorem isOpen_rightOpen : IsOpen rightOpen :=
  isOpen_lt continuous_const (Complex.continuous_re.comp continuous_subtype_val)

/-- The two open sets `A` and `B` cover the thrice-punctured sphere: a point with `re z < 1` lies
in `A`, and otherwise `re z ≥ 1 > 0` puts it in `B`. -/
@[simp]
theorem leftOpen_union_rightOpen : leftOpen ∪ rightOpen = univ := by
  refine eq_univ_of_forall fun z ↦ ?_
  by_cases h : (z : ℂ).re < 1
  · exact Or.inl h
  · exact Or.inr (by simp only [mem_rightOpen]; linarith)

/-- In `ℂ`, the set `A` is the half-plane `re z < 1` with the puncture `0` removed. The point `1`
is not removed, as it does not lie in the half-plane. -/
theorem image_coe_leftOpen : (↑) '' leftOpen = {z : ℂ | z.re < 1} \ {0} := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨hw, w.ne_zero⟩
  · rintro ⟨hz, hz0 : z ≠ 0⟩
    refine ⟨⟨z, hz0, ?_⟩, hz, rfl⟩
    rintro rfl
    simp at hz

/-- In `ℂ`, the set `B` is the half-plane `0 < re z` with the puncture `1` removed. The point `0`
is not removed, as it does not lie in the half-plane. -/
theorem image_coe_rightOpen : (↑) '' rightOpen = {z : ℂ | 0 < z.re} \ {1} := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨hw, w.ne_one⟩
  · rintro ⟨hz, hz1 : z ≠ 1⟩
    refine ⟨⟨z, ?_, hz1⟩, hz, rfl⟩
    rintro rfl
    simp at hz

/-- In `ℂ`, the intersection `A ∩ B` is the open vertical strip `0 < re z < 1`, with no point
removed: both punctures lie on the boundary lines of the strip. -/
theorem image_coe_leftOpen_inter_rightOpen :
    (↑) '' (leftOpen ∩ rightOpen) = {z : ℂ | 0 < z.re ∧ z.re < 1} := by
  ext z
  constructor
  · rintro ⟨w, ⟨hw₁, hw₂⟩, rfl⟩
    exact ⟨hw₂, hw₁⟩
  · rintro ⟨hz₀, hz₁⟩
    refine ⟨⟨z, ?_, ?_⟩, ⟨hz₁, hz₀⟩, rfl⟩
    · rintro rfl
      simp at hz₀
    · rintro rfl
      simp at hz₁

/-- The intersection `A ∩ B` of the standard two-set cover is simply connected: it is
homeomorphic to the open vertical strip `0 < re z < 1`, which is convex and nonempty, hence
contractible. -/
theorem isSimplyConnected_leftOpen_inter_rightOpen :
    IsSimplyConnected (leftOpen ∩ rightOpen) := by
  rw [← isOpenEmbedding_coe.isEmbedding.isSimplyConnected_image,
    image_coe_leftOpen_inter_rightOpen]
  have hconv : Convex ℝ {z : ℂ | 0 < z.re ∧ z.re < 1} :=
    (convex_halfSpace_re_gt 0).inter (convex_halfSpace_re_lt 1)
  have := hconv.contractibleSpace ⟨1 / 2, by norm_num, by norm_num⟩
  exact SimplyConnectedSpace.ofContractible _

/-- The intersection `A ∩ B` of the standard two-set cover is path-connected. -/
theorem isPathConnected_leftOpen_inter_rightOpen :
    IsPathConnected (leftOpen ∩ rightOpen) :=
  isSimplyConnected_leftOpen_inter_rightOpen.isPathConnected

-- These are not simp lemmas: `mem_leftOpen`, `mem_rightOpen`, and `coe_basePt` already let
-- `simp` prove both statements, so extra simp attributes would fail the simpNF linter.
/-- The basepoint `1/2` lies in `leftOpen`. -/
theorem basePt_mem_leftOpen : basePt ∈ leftOpen := by
  simp only [mem_leftOpen, coe_basePt]
  norm_num

/-- The basepoint `1/2` lies in `rightOpen`. -/
theorem basePt_mem_rightOpen : basePt ∈ rightOpen := by
  simp only [mem_rightOpen, coe_basePt]
  norm_num

/-- The basepoint `1/2` lies in the strip `A ∩ B`. -/
theorem basePt_mem_leftOpen_inter_rightOpen : basePt ∈ leftOpen ∩ rightOpen :=
  ⟨basePt_mem_leftOpen, basePt_mem_rightOpen⟩

/-! ### Standard punctured-disc neighbourhoods -/

/-- The standard punctured-disc neighbourhood `0 < |z| < 1/2` of the puncture `0`. -/
def puncturedDiscZero : Set ThricePuncturedSphere :=
  {z | 0 < ‖(z : ℂ)‖ ∧ ‖(z : ℂ)‖ < 1 / 2}

/-- The standard punctured-disc neighbourhood `0 < |z - 1| < 1/2` of the puncture `1`. -/
def puncturedDiscOne : Set ThricePuncturedSphere :=
  {z | 0 < ‖(z : ℂ) - 1‖ ∧ ‖(z : ℂ) - 1‖ < 1 / 2}

/-- The standard punctured-disc neighbourhood `2 < |z|` of the puncture `∞`. Under the chart
`w = 1 / z` at infinity this is the punctured disc `0 < |w| < 1/2`. -/
def puncturedDiscInf : Set ThricePuncturedSphere :=
  {z | 2 < ‖(z : ℂ)‖}

/-- Membership in the standard punctured-disc neighbourhood of `0`. -/
@[simp]
theorem mem_puncturedDiscZero {z : ThricePuncturedSphere} :
    z ∈ puncturedDiscZero ↔ 0 < ‖(z : ℂ)‖ ∧ ‖(z : ℂ)‖ < 1 / 2 :=
  Iff.rfl

/-- Membership in the standard punctured-disc neighbourhood of `1`, in the chart `w = z - 1`. -/
@[simp]
theorem mem_puncturedDiscOne {z : ThricePuncturedSphere} :
    z ∈ puncturedDiscOne ↔ 0 < ‖(z : ℂ) - 1‖ ∧ ‖(z : ℂ) - 1‖ < 1 / 2 :=
  Iff.rfl

/-- Membership in the standard punctured-disc neighbourhood of `∞`. -/
@[simp]
theorem mem_puncturedDiscInf {z : ThricePuncturedSphere} :
    z ∈ puncturedDiscInf ↔ 2 < ‖(z : ℂ)‖ :=
  Iff.rfl

/-- In the chart `w = 1 / z` at infinity, `puncturedDiscInf` is the punctured disc of radius
`1/2` about `0`. -/
theorem mem_puncturedDiscInf_iff_inv {z : ThricePuncturedSphere} :
    z ∈ puncturedDiscInf ↔ 0 < ‖(z : ℂ)⁻¹‖ ∧ ‖(z : ℂ)⁻¹‖ < 1 / 2 := by
  rw [norm_inv]
  have hz : 0 < ‖(z : ℂ)‖ := norm_pos_iff.mpr z.ne_zero
  constructor
  · intro h
    rw [mem_puncturedDiscInf] at h
    constructor
    · positivity
    · simpa only [one_div] using (inv_lt_inv₀ hz (by norm_num)).mpr h
  · rintro ⟨_, h⟩
    rw [mem_puncturedDiscInf]
    exact (inv_lt_inv₀ hz (by norm_num)).mp (by simpa only [one_div] using h)

/-- The standard punctured-disc neighbourhood of `0` is open. -/
theorem isOpen_puncturedDiscZero : IsOpen puncturedDiscZero := by
  apply IsOpen.inter
  · exact isOpen_lt continuous_const (continuous_norm.comp continuous_subtype_val)
  · exact isOpen_lt (continuous_norm.comp continuous_subtype_val) continuous_const

/-- The standard punctured-disc neighbourhood of `1` is open. -/
theorem isOpen_puncturedDiscOne : IsOpen puncturedDiscOne := by
  apply IsOpen.inter
  · exact isOpen_lt continuous_const (continuous_norm.comp
      (continuous_subtype_val.sub continuous_const))
  · exact isOpen_lt (continuous_norm.comp
      (continuous_subtype_val.sub continuous_const)) continuous_const

/-- The standard punctured-disc neighbourhood of `∞` is open. -/
theorem isOpen_puncturedDiscInf : IsOpen puncturedDiscInf :=
  isOpen_lt continuous_const (continuous_norm.comp continuous_subtype_val)

/-- The standard neighbourhoods at `0` and `1` are disjoint; their boundary circles are tangent
at the basepoint, but the neighbourhoods use strict inequalities. -/
theorem disjoint_puncturedDiscZero_puncturedDiscOne :
    Disjoint puncturedDiscZero puncturedDiscOne := by
  rw [Set.disjoint_left]
  intro z hz0 hz1
  have htri : ‖(1 : ℂ)‖ ≤ ‖(z : ℂ)‖ + ‖(z : ℂ) - 1‖ := by
    calc
      ‖(1 : ℂ)‖ = ‖(z : ℂ) - ((z : ℂ) - 1)‖ := by ring_nf
      _ ≤ _ := norm_sub_le _ _
  norm_num [puncturedDiscZero, puncturedDiscOne] at hz0 hz1 htri
  linarith

/-- The standard neighbourhoods at `0` and `∞` are disjoint. -/
theorem disjoint_puncturedDiscZero_puncturedDiscInf :
    Disjoint puncturedDiscZero puncturedDiscInf := by
  rw [Set.disjoint_left]
  intro z hz0 hzInf
  rw [mem_puncturedDiscZero] at hz0
  rw [mem_puncturedDiscInf] at hzInf
  linarith

/-- The standard neighbourhoods at `1` and `∞` are disjoint. -/
theorem disjoint_puncturedDiscOne_puncturedDiscInf :
    Disjoint puncturedDiscOne puncturedDiscInf := by
  rw [Set.disjoint_left]
  intro z hz1 hzInf
  have htri : ‖(z : ℂ)‖ ≤ ‖(z : ℂ) - 1‖ + ‖(1 : ℂ)‖ := by
    calc
      ‖(z : ℂ)‖ = ‖((z : ℂ) - 1 + 1)‖ := by ring_nf
      _ ≤ _ := norm_add_le _ _
  norm_num [puncturedDiscOne, puncturedDiscInf] at hz1 hzInf htri
  linarith

/-! ### The anharmonic self-homeomorphisms -/

/-- The identity anharmonic self-homeomorphism. -/
noncomputable def mobId : ThricePuncturedSphere ≃ₜ ThricePuncturedSphere :=
  Homeomorph.refl _

/-- The self-homeomorphism `z ↦ 1 − z` of the thrice-punctured sphere. It is the anharmonic
transformation exchanging the punctures `0` and `1` and fixing `∞`, and among the six anharmonic
transformations it is the only nonidentity one fixing the basepoint `1/2`. -/
noncomputable def mob01 : ThricePuncturedSphere ≃ₜ ThricePuncturedSphere :=
  (IsometryEquiv.subLeft (1 : ℂ)).toHomeomorph.subtype fun z ↦ by
    simp only [ne_eq, IsometryEquiv.coe_toHomeomorph, IsometryEquiv.subLeft_apply]
    constructor <;> rintro ⟨h₀, h₁⟩ <;>
      exact ⟨fun h ↦ h₁ (by linear_combination -h), fun h ↦ h₀ (by linear_combination -h)⟩

@[simp]
theorem coe_mob01 (z : ThricePuncturedSphere) : (mob01 z : ℂ) = 1 - z := by
  unfold mob01
  rw [Homeomorph.subtype_apply_coe, IsometryEquiv.coe_toHomeomorph,
    IsometryEquiv.subLeft_apply]

/-- The involution `z ↦ 1 − z` carries `leftOpen` to `rightOpen`. -/
@[simp]
theorem preimage_mob01_leftOpen : mob01 ⁻¹' leftOpen = rightOpen := by
  ext z
  simp only [mem_preimage, mem_leftOpen, coe_mob01, Complex.sub_re, Complex.one_re,
    mem_rightOpen]
  constructor <;> intro h <;> linarith

/-- The involution `z ↦ 1 − z` carries `rightOpen` to `leftOpen`. -/
@[simp]
theorem preimage_mob01_rightOpen : mob01 ⁻¹' rightOpen = leftOpen := by
  ext z
  simp only [mem_preimage, mem_rightOpen, coe_mob01, Complex.sub_re, Complex.one_re,
    mem_leftOpen]
  constructor <;> intro h <;> linarith

/-- `z ↦ 1 − z` is an involution. -/
@[simp]
theorem mob01_mob01 (z : ThricePuncturedSphere) : mob01 (mob01 z) = z :=
  Subtype.ext (by simp)

@[simp]
theorem mob01_symm : mob01.symm = mob01 :=
  Homeomorph.ext fun z ↦ by rw [Homeomorph.symm_apply_eq, mob01_mob01]

/-- `z ↦ 1 − z` fixes the basepoint `1/2`. -/
@[simp]
theorem mob01_basePt : mob01 basePt = basePt :=
  Subtype.ext (by norm_num)

/-- The anharmonic involution `z ↦ z / (z - 1)`, which exchanges `1` and `∞` and fixes `0`. -/
noncomputable def mob1Inf : ThricePuncturedSphere ≃ₜ ThricePuncturedSphere where
  toFun z := ⟨z.1 / (z.1 - 1), div_ne_zero z.2.1 (sub_ne_zero.mpr z.2.2), by
    intro h
    exact one_ne_zero (sub_eq_self.mp ((div_eq_one_iff_eq (sub_ne_zero.mpr z.2.2)).mp h).symm)⟩
  invFun z := ⟨z.1 / (z.1 - 1), div_ne_zero z.2.1 (sub_ne_zero.mpr z.2.2), by
    intro h
    exact one_ne_zero (sub_eq_self.mp ((div_eq_one_iff_eq (sub_ne_zero.mpr z.2.2)).mp h).symm)⟩
  left_inv z := Subtype.ext (by
    field_simp [z.ne_zero, sub_ne_zero.mpr z.ne_one]
    ring)
  right_inv z := Subtype.ext (by
    field_simp [z.ne_zero, sub_ne_zero.mpr z.ne_one]
    ring)
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val.div (continuous_subtype_val.sub continuous_const)
      fun z ↦ sub_ne_zero.mpr z.2.2
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val.div (continuous_subtype_val.sub continuous_const)
      fun z ↦ sub_ne_zero.mpr z.2.2

@[simp]
theorem coe_mob1Inf (z : ThricePuncturedSphere) : (mob1Inf z : ℂ) = z / (z - 1) :=
  by unfold mob1Inf; rfl

/-- The order-three anharmonic map `z ↦ 1 / (1 - z)`. -/
noncomputable def mobRot : ThricePuncturedSphere ≃ₜ ThricePuncturedSphere :=
  mob1Inf.trans mob01

/-- The inverse order-three anharmonic map `z ↦ (z - 1) / z`. -/
noncomputable def mobRotInv : ThricePuncturedSphere ≃ₜ ThricePuncturedSphere :=
  mob01.trans mob1Inf

/-- The anharmonic involution `z ↦ 1 / z`, which exchanges `0` and `∞` and fixes `1`. -/
noncomputable def mob0Inf : ThricePuncturedSphere ≃ₜ ThricePuncturedSphere :=
  (mob01.trans mob1Inf).trans mob01

@[simp]
theorem coe_mobRot (z : ThricePuncturedSphere) : (mobRot z : ℂ) = 1 / (1 - z) := by
  simp only [mobRot, Homeomorph.trans_apply, coe_mob01, coe_mob1Inf]
  field_simp [sub_ne_zero.mpr z.ne_one, sub_ne_zero.mpr z.ne_one.symm]
  ring

@[simp]
theorem coe_mobRotInv (z : ThricePuncturedSphere) :
    (mobRotInv z : ℂ) = (z - 1) / z := by
  simp only [mobRotInv, Homeomorph.trans_apply, coe_mob01, coe_mob1Inf]
  field_simp [z.ne_zero]
  ring

@[simp]
theorem coe_mob0Inf (z : ThricePuncturedSphere) : (mob0Inf z : ℂ) = 1 / z := by
  simp only [mob0Inf, Homeomorph.trans_apply, coe_mob01, coe_mob1Inf]
  field_simp [z.ne_zero]
  ring

/-- The generator exchanging `1` and `∞` sends the basepoint to `-1`. -/
theorem coe_mob1Inf_basePt : (mob1Inf basePt : ℂ) = -1 := by
  norm_num

/-- The anharmonic involution exchanging `0` and `∞` sends the basepoint to `2`. -/
theorem coe_mob0Inf_basePt : (mob0Inf basePt : ℂ) = 2 := by
  norm_num

/-- The order-three anharmonic map sends the basepoint to `2`. -/
theorem coe_mobRot_basePt : (mobRot basePt : ℂ) = 2 := by
  norm_num

/-- The inverse order-three anharmonic map sends the basepoint to `-1`. -/
theorem coe_mobRotInv_basePt : (mobRotInv basePt : ℂ) = -1 := by
  norm_num

end ThricePuncturedSphere

end TauCeti
