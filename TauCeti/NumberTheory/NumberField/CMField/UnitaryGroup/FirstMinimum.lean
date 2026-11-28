/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.CMField.UnitaryGroup.AdelicFrame
public import Mathlib.Analysis.InnerProductSpace.PiL2
import TauCeti.NumberTheory.NumberField.Global.Adeles.Finite
import TauCeti.NumberTheory.NumberField.Global.Adeles.LocallyCompact
import TauCeti.RingTheory.DedekindDomain.AdicValuation.ValuativeRel

/-!
# The first minimum of a framed hermitian space

The archimedean coordinates of a rational vector in a framed hermitian space give its
Euclidean length. There are finitely many lattice vectors of bounded length. Consequently
the first minimum, truncated at one, is positive and is attained whenever it is less than
one. Its reciprocal on moved spaces defines the height used to measure growth on adelic
unitary groups.

The definitions of the first minimum and height follow `[ShortProof]`,
`src/Lib/Adelic/Reduction/FirstMinimumShortBases.lean` (`New.Space.firstMinimum`,
`New.Space.height`) in grh-lean, https://github.com/lsernau/grh-lean, at commit
`72fead102f663d5c7a407964a13dc0cf9d977207`. The proofs here use compactness and discreteness
of the rational points in the adeles.
-/

public noncomputable section

open IsDedekindDomain Matrix NumberField Set
open scoped NumberField.AdeleRing

namespace TauCeti.FramedHermitianSpace

variable {E : Type*} [Field E] [NumberField E] [IsCMField E]
  {ι : Type*} [Fintype ι] [DecidableEq ι] {s : ι → ℤˣ}
  (V : FramedHermitianSpace E s)

/-- The coordinates of a rational vector in the inverse archimedean frame, read in `ℂ`
at each infinite place, with the Euclidean norm on all coordinates together. -/
def archCoords (y : ι → E) : EuclideanSpace ℂ (ι × InfinitePlace E) :=
  WithLp.toLp 2 fun p ↦ InfinitePlace.Completion.extensionEmbedding p.2
    (((↑V.frame.1⁻¹ : Matrix ι ι (InfiniteAdeleRing E)) *ᵥ
      (algebraMap E (InfiniteAdeleRing E) ∘ y)) p.1 p.2)

/-- A single archimedean coordinate in the inverse frame. -/
@[simp]
theorem archCoords_apply (y : ι → E) (i : ι) (w : InfinitePlace E) :
    V.archCoords y (i, w) = InfinitePlace.Completion.extensionEmbedding w
      (((↑V.frame.1⁻¹ : Matrix ι ι (InfiniteAdeleRing E)) *ᵥ
        (algebraMap E (InfiniteAdeleRing E) ∘ y)) i w) :=
  (rfl)

/-- The zero vector has zero archimedean coordinates. -/
@[simp]
theorem archCoords_zero : V.archCoords 0 = 0 := by
  have h : algebraMap E (InfiniteAdeleRing E) ∘ (0 : ι → E) = 0 := by
    ext _
    exact map_zero _
  ext ⟨i, w⟩
  rw [archCoords_apply, h, mulVec_zero]
  exact map_zero _

/-- The archimedean coordinates are additive. -/
@[simp]
theorem archCoords_add (y z : ι → E) : V.archCoords (y + z) = V.archCoords y + V.archCoords z := by
  have h : algebraMap E (InfiniteAdeleRing E) ∘ (y + z) =
      algebraMap E (InfiniteAdeleRing E) ∘ y + algebraMap E (InfiniteAdeleRing E) ∘ z := by
    ext i
    exact map_add _ _ _
  ext ⟨i, w⟩
  simp only [PiLp.add_apply, archCoords_apply, h, mulVec_add, Pi.add_apply,
    InfiniteAdeleRing.add_apply, map_add]

/-- Negating a vector negates its archimedean coordinates. -/
@[simp]
theorem archCoords_neg (y : ι → E) : V.archCoords (-y) = -V.archCoords y := by
  apply eq_neg_of_add_eq_zero_left
  rw [← archCoords_add, neg_add_cancel, archCoords_zero]

/-- The archimedean coordinates determine the rational vector. -/
theorem archCoords_injective : Function.Injective V.archCoords := by
  intro y z h
  have hcoords :
      (↑V.frame.1⁻¹ : Matrix ι ι (InfiniteAdeleRing E)) *ᵥ
          (algebraMap E (InfiniteAdeleRing E) ∘ y) =
        (↑V.frame.1⁻¹ : Matrix ι ι (InfiniteAdeleRing E)) *ᵥ
          (algebraMap E (InfiniteAdeleRing E) ∘ z) := by
    funext i w
    apply (InfinitePlace.Completion.extensionEmbedding w).injective
    simpa only [archCoords_apply] using
      congrArg (fun a : EuclideanSpace ℂ (ι × InfinitePlace E) ↦ a (i, w)) h
  have heq := mulVec_injective_of_isUnit V.frame.1⁻¹.isUnit hcoords
  obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace E))
  funext i
  exact (algebraMap E w.Completion).injective (congrArg (fun a ↦ a i w) heq)

/-- The Euclidean length of a rational vector in the inverse archimedean frame. -/
def vectorLength (y : ι → E) : ℝ := ‖V.archCoords y‖

/-- The length is the norm of all archimedean coordinates together. -/
theorem vectorLength_def (y : ι → E) : V.vectorLength y = ‖V.archCoords y‖ :=
  (rfl)

/-- The zero vector has length zero. -/
@[simp]
theorem vectorLength_zero : V.vectorLength 0 = 0 := by
  rw [vectorLength_def, archCoords_zero, norm_zero]

/-- Lengths are nonnegative. -/
theorem vectorLength_nonneg (y : ι → E) : 0 ≤ V.vectorLength y := norm_nonneg _

/-- Only the zero vector has length zero. -/
@[simp]
theorem vectorLength_eq_zero_iff {y : ι → E} : V.vectorLength y = 0 ↔ y = 0 := by
  rw [vectorLength_def, norm_eq_zero, ← V.archCoords_zero, V.archCoords_injective.eq_iff]

/-- Negation preserves length. -/
@[simp]
theorem vectorLength_neg (y : ι → E) : V.vectorLength (-y) = V.vectorLength y := by
  rw [vectorLength_def, archCoords_neg, norm_neg, vectorLength_def]

/-- Every nonzero rational vector has positive length. -/
theorem vectorLength_pos {y : ι → E} (hy : y ≠ 0) : 0 < V.vectorLength y :=
  lt_of_le_of_ne (V.vectorLength_nonneg y) (Ne.symm (V.vectorLength_eq_zero_iff.not.2 hy))

/-- Length satisfies the triangle inequality. -/
theorem vectorLength_add_le (y z : ι → E) :
    V.vectorLength (y + z) ≤ V.vectorLength y + V.vectorLength z := by
  rw [vectorLength_def, archCoords_add]
  exact norm_add_le _ _

/-- Each local coordinate is bounded by the Euclidean length. -/
theorem norm_inv_frame_mulVec_apply_le_vectorLength (y : ι → E) (i : ι) (w : InfinitePlace E) :
    ‖((↑V.frame.1⁻¹ : Matrix ι ι (InfiniteAdeleRing E)) *ᵥ
      (algebraMap E (InfiniteAdeleRing E) ∘ y)) i w‖ ≤ V.vectorLength y := by
  have hnorm := (InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero
    (map_zero _) (((↑V.frame.1⁻¹ : Matrix ι ι (InfiniteAdeleRing E)) *ᵥ
      (algebraMap E (InfiniteAdeleRing E) ∘ y)) i w)
  rw [← hnorm, vectorLength_def, ← archCoords_apply]
  exact PiLp.norm_apply_le (V.archCoords y) (i, w)

/-- A rational lattice has only finitely many vectors of length at most a given bound. -/
theorem finite_setOf_mem_lattice_vectorLength_le (R : ℝ) :
    {y : ι → E | y ∈ V.lattice ∧ V.vectorLength y ≤ R}.Finite := by
  let B : Set (ι → InfiniteAdeleRing E) :=
    Set.pi univ fun _ ↦ Set.pi univ fun w : InfinitePlace E ↦ {z : w.Completion | ‖z‖ ≤ R}
  have hB : IsCompact B := by
    apply isCompact_univ_pi
    intro _
    apply isCompact_univ_pi
    intro w
    have h := (InfinitePlace.Completion.isometry_extensionEmbedding w).isClosedEmbedding
      |>.isCompact_preimage (isCompact_closedBall (0 : ℂ) R)
    simpa only [Metric.closedBall, preimage_ofPred_eq, dist_zero_right,
      (InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _)]
      using h
  let C : Set (ι → 𝔸ᶠ[E]) := Set.pi univ fun _ ↦ FiniteAdeleRing.integralAdeles (𝓞 E) E
  have hC : IsCompact C := isCompact_univ_pi fun _ ↦ FiniteAdeleRing.isCompact_integralAdeles
  let T (p : (ι → InfiniteAdeleRing E) × (ι → 𝔸ᶠ[E])) : ι → 𝔸[E] := fun i ↦
    (((↑V.frame.1 : Matrix ι ι (InfiniteAdeleRing E)) *ᵥ p.1) i,
      ((↑V.frame.2 : Matrix ι ι 𝔸ᶠ[E]) *ᵥ p.2) i)
  have hT : Continuous T := by
    fun_prop
  apply (AdeleRing.finite_preimage_algebraMap_pi ((hB.prod hC).image hT)).subset
  intro y hy
  let u := (↑V.frame.1⁻¹ : Matrix ι ι (InfiniteAdeleRing E)) *ᵥ
    (algebraMap E (InfiniteAdeleRing E) ∘ y)
  let v := (↑V.frame.2⁻¹ : Matrix ι ι 𝔸ᶠ[E]) *ᵥ (algebraMap E 𝔸ᶠ[E] ∘ y)
  have hu : u ∈ B := fun i _ w _ ↦
    (V.norm_inv_frame_mulVec_apply_le_vectorLength y i w).trans hy.2
  have hv : v ∈ C := fun i _ ↦ (V.mem_lattice_iff.1 hy.1) i
  refine ⟨(u, v), ⟨hu, hv⟩, ?_⟩
  have hu_inv : (↑V.frame.1 : Matrix ι ι (InfiniteAdeleRing E)) *ᵥ u =
      algebraMap E (InfiniteAdeleRing E) ∘ y := by
    simp only [u, mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]
  have hv_inv : (↑V.frame.2 : Matrix ι ι 𝔸ᶠ[E]) *ᵥ v = algebraMap E 𝔸ᶠ[E] ∘ y := by
    simp only [v, mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]
  funext i
  exact Prod.ext (congrFun hu_inv i) (congrFun hv_inv i)

/-- The first minimum of the rational lattice, truncated at one. In rank zero it is one. -/
def firstMinimum : ℝ :=
  sInf (insert 1 (V.vectorLength '' {y | y ∈ V.lattice ∧ y ≠ 0}))

/-- The defining infimum includes one, so it also applies to the zero-dimensional space. -/
theorem firstMinimum_def : V.firstMinimum =
    sInf (insert 1 (V.vectorLength '' {y | y ∈ V.lattice ∧ y ≠ 0})) :=
  (rfl)

/-- The truncated first minimum is a least element, not merely an infimum. -/
theorem isLeast_firstMinimum :
    IsLeast (insert 1 (V.vectorLength '' {y | y ∈ V.lattice ∧ y ≠ 0})) V.firstMinimum := by
  let S : Set ℝ := insert 1 (V.vectorLength ''
    {y | y ∈ V.lattice ∧ y ≠ 0 ∧ V.vectorLength y ≤ 1})
  have hS : S.Finite := by
    have hfinite : {y | y ∈ V.lattice ∧ y ≠ 0 ∧ V.vectorLength y ≤ 1}.Finite :=
      (V.finite_setOf_mem_lattice_vectorLength_le 1).subset fun _ hy ↦ ⟨hy.1, hy.2.2⟩
    exact (hfinite.image V.vectorLength).insert 1
  obtain ⟨a, ha, hmin⟩ := Set.exists_min_image S id hS (by exact ⟨1, mem_insert _ _⟩)
  have ha_one : a ≤ 1 := hmin 1 (mem_insert _ _)
  have hleast : IsLeast (insert 1 (V.vectorLength '' {y | y ∈ V.lattice ∧ y ≠ 0})) a := by
    constructor
    · rcases ha with rfl | ⟨y, hy, rfl⟩
      · exact mem_insert _ _
      · exact mem_insert_of_mem _ ⟨y, ⟨hy.1, hy.2.1⟩, rfl⟩
    · rintro b (rfl | ⟨y, hy, rfl⟩)
      · exact ha_one
      · by_cases hy_one : V.vectorLength y ≤ 1
        · exact hmin _ (mem_insert_of_mem _ ⟨y, ⟨hy.1, hy.2, hy_one⟩, rfl⟩)
        · exact ha_one.trans (le_of_not_ge hy_one)
  rw [firstMinimum_def, hleast.csInf_eq]
  exact hleast

/-- The first minimum is strictly positive. -/
theorem firstMinimum_pos : 0 < V.firstMinimum := by
  rcases V.isLeast_firstMinimum.1 with h | ⟨y, hy, h⟩
  · rw [h]
    exact zero_lt_one
  · rw [← h]
    exact V.vectorLength_pos hy.2

/-- Truncation bounds the first minimum above by one. -/
theorem firstMinimum_le_one : V.firstMinimum ≤ 1 :=
  V.isLeast_firstMinimum.2 (mem_insert _ _)

/-- The first minimum bounds the length of every nonzero lattice vector. -/
theorem firstMinimum_le_vectorLength {y : ι → E} (hy : y ∈ V.lattice) (hy_ne : y ≠ 0) :
    V.firstMinimum ≤ V.vectorLength y :=
  V.isLeast_firstMinimum.2 (mem_insert_of_mem _ ⟨y, ⟨hy, hy_ne⟩, rfl⟩)

/-- Characterization of lower bounds for the truncated first minimum. -/
theorem le_firstMinimum_iff {r : ℝ} : r ≤ V.firstMinimum ↔
    r ≤ 1 ∧ ∀ y ∈ V.lattice, y ≠ 0 → r ≤ V.vectorLength y := by
  constructor
  · intro h
    exact ⟨h.trans V.firstMinimum_le_one,
      fun _ hy hy_ne ↦ h.trans (V.firstMinimum_le_vectorLength hy hy_ne)⟩
  · rintro ⟨h_one, h⟩
    rcases V.isLeast_firstMinimum.1 with hmin | ⟨y, hy, hmin⟩
    · rwa [hmin]
    · rw [← hmin]
      exact h y hy.1 hy.2

/-- If the truncation is inactive, a nonzero lattice vector attains the first minimum. -/
theorem exists_vectorLength_eq_firstMinimum (h : V.firstMinimum < 1) :
    ∃ y ∈ V.lattice, y ≠ 0 ∧ V.vectorLength y = V.firstMinimum := by
  rcases V.isLeast_firstMinimum.1 with hmin | ⟨y, hy, hmin⟩
  · exact False.elim (h.ne hmin)
  · exact ⟨y, hy.1, hy.2, hmin⟩

/-- The first minimum is one precisely when all nonzero lattice vectors have length at least one. -/
@[simp]
theorem firstMinimum_eq_one_iff : V.firstMinimum = 1 ↔
    ∀ y ∈ V.lattice, y ≠ 0 → 1 ≤ V.vectorLength y := by
  rw [le_antisymm_iff, and_iff_right V.firstMinimum_le_one, V.le_firstMinimum_iff,
    and_iff_right le_rfl]

/-- A lattice vector shorter than the first minimum must be zero; zero is always shorter. -/
@[simp]
theorem vectorLength_lt_firstMinimum_iff {y : ι → E} (hy : y ∈ V.lattice) :
    V.vectorLength y < V.firstMinimum ↔ y = 0 := by
  constructor
  · intro h
    by_contra hy_ne
    exact h.not_ge (V.firstMinimum_le_vectorLength hy hy_ne)
  · rintro rfl
    rw [vectorLength_zero]
    exact V.firstMinimum_pos

/-- The height of an adelic unitary point is the reciprocal first minimum of the moved space. -/
def height (g : adelicUnitaryGroup E s) : ℝ :=
  (MulOpposite.op g • V).firstMinimum⁻¹

/-- The height is the reciprocal first minimum in the frame `x g`. -/
theorem height_def (g : adelicUnitaryGroup E s) :
    V.height g = (MulOpposite.op g • V).firstMinimum⁻¹ :=
  (rfl)

/-- The height at the identity is the reciprocal first minimum of the base space. -/
@[simp]
theorem height_one : V.height 1 = V.firstMinimum⁻¹ := by
  rw [height_def, MulOpposite.op_one, one_smul]

/-- Heights are positive. -/
theorem height_pos (g : adelicUnitaryGroup E s) : 0 < V.height g := by
  rw [height_def]
  exact inv_pos.2 (firstMinimum_pos _)

/-- The truncation of the first minimum ensures that every height is at least one. -/
theorem one_le_height (g : adelicUnitaryGroup E s) : 1 ≤ V.height g := by
  rw [height_def]
  exact (one_le_inv₀ (firstMinimum_pos _)).2 (firstMinimum_le_one _)

/-- Taking the reciprocal of height recovers the moved first minimum. -/
@[simp]
theorem inv_height (g : adelicUnitaryGroup E s) :
    (V.height g)⁻¹ = (MulOpposite.op g • V).firstMinimum := by
  rw [height_def, inv_inv]

/-- An upper height bound is a lower first-minimum bound. -/
theorem height_le_iff (g : adelicUnitaryGroup E s) {R : ℝ} (hR : 0 < R) :
    V.height g ≤ R ↔ R⁻¹ ≤ (MulOpposite.op g • V).firstMinimum := by
  rw [height_def]
  exact inv_le_comm₀ (firstMinimum_pos _) hR

/-- Moving the base frame is left translation of the height function. -/
theorem height_smul (g h : adelicUnitaryGroup E s) :
    (MulOpposite.op g • V).height h = V.height (g * h) := by
  simp only [height_def, ← mul_smul, ← MulOpposite.op_mul]

end TauCeti.FramedHermitianSpace
