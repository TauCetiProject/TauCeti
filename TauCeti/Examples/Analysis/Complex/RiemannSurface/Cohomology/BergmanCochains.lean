/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.RiemannSurface.Cohomology.BergmanLifting
public import TauCeti.Geometry.Manifold.CoordinateBall
public import TauCeti.Geometry.Manifold.Instances.OnePoint.Basic

/-!
# Finite coordinate covers and native Bergman coboundaries

Native finite coordinate covers give five nested families on the Riemann sphere and on the
sum of two Riemann spheres. Duplicating each chart gives a constant coboundary that reads one
at an actual overlap containing infinity. One positive constant controls all middle cocycles
on each fixed family, including this nonzero coboundary and zero data. The empty original is
also an application of the uniform lifting theorem.
-/

public noncomputable section

open CategoryTheory Metric Set TopologicalSpace MeasureTheory
open scoped Manifold ContDiff ENNReal Topology OnePoint

universe w u
namespace TauCeti.Examples.BergmanLifting
open TauCeti.RiemannSurface.ChartBergman

variable {X : Type w} [TopologicalSpace X] [ChartedSpace ℂ X]

/-- A finite coordinate-ball cover with six-radius target containment. -/
structure DiscCover (X : Type w) [TopologicalSpace X] [ChartedSpace ℂ X] where
  /-- Number of charts in the finite cover. -/
  size : ℕ
  /-- Actual native coordinate charts. -/
  chart : Fin size → OpenPartialHomeomorph X ℂ
  /-- Centers of the coordinate discs. -/
  center : Fin size → ℂ
  /-- Positive base radii of the coordinate discs. -/
  radius : Fin size → ℝ
  mem_atlas : ∀ i, chart i ∈ atlas ℂ X
  radius_pos : ∀ i, 0 < radius i
  closed_subset : ∀ i, closedBall (center i) (6 * radius i) ⊆ (chart i).target
  covers : ⋃ i, ((chart i).preimageBall (center i) (radius i) : Set X) = univ

/-- A chosen finite coordinate-ball cover with six-radius target containment. -/
def chosenDiscCover [CompactSpace X] : DiscCover X := Classical.choice <| by
  classical
  obtain ⟨ι, hι, e₀, c₀, r₀, he₀, hr₀, hclosed₀, _, hcover₀⟩ :=
    exists_finite_preimageBall_cover (H := ℂ) (X := X) 6
      (V := fun _ : Unit ↦ (⊤ : Opens X)) (by simp [IsOpenCover])
  let := hι
  let := Fintype.ofFinite ι
  let q := Fintype.equivFin ι
  refine ⟨⟨Fintype.card ι, (fun i ↦ e₀ (q.symm i)), (fun i ↦ c₀ (q.symm i)),
    (fun i ↦ r₀ (q.symm i)), (fun i ↦ he₀ (q.symm i)), (fun i ↦ hr₀ (q.symm i)),
    (fun i ↦ hclosed₀ (q.symm i)), ?_⟩⟩
  apply eq_univ_of_forall
  intro x
  obtain ⟨i, hi⟩ := (IsOpenCover.mk hcover₀).exists_mem x
  exact mem_iUnion.mpr ⟨q i, by simpa only [q.symm_apply_apply, SetLike.mem_coe] using hi⟩

namespace DiscCover

variable (D : DiscCover X)

/-- Duplicate each actual chart by two labels. -/
def chart₂ (i : Fin D.size × Fin 2) := D.chart i.1
/-- Both copies have the same actual center. -/
def center₂ (i : Fin D.size × Fin 2) := D.center i.1
/-- Both copies have the same actual radius. -/
def radius₂ (i : Fin D.size × Fin 2) := D.radius i.1
/-- The coordinate-ball family at a given multiple of the radius. -/
def level (a : ℝ) (i : Fin D.size × Fin 2) : Opens X :=
  (D.chart₂ i).preimageBall (D.center₂ i) (a * D.radius₂ i)

/-- The native inner family uses its literal radius. -/
def inner (i : Fin D.size × Fin 2) : Opens X :=
  (D.chart₂ i).preimageBall (D.center₂ i) (D.radius₂ i)

/-- Increasing the radius gives literal inclusion of these native opens. -/
theorem level_mono {a b : ℝ} (hab : a ≤ b) (i : Fin D.size × Fin 2) :
    D.level a i ≤ D.level b i :=
  (D.chart₂ i).preimageBall_mono (mul_le_mul_of_nonneg_right hab (D.radius_pos i.1).le)

/-- Each of the five nested coordinate-ball families covers the actual base. -/
theorem five_level_cover (k : Fin 5) :
    ⋃ i, (D.level ((k.val : ℝ) + 1) i : Set X) = univ := by
  apply eq_univ_of_forall
  intro x
  obtain ⟨i, hi⟩ := mem_iUnion.mp (D.covers.ge (mem_univ x))
  refine mem_iUnion.mpr ⟨(i, 0), D.level_mono (a := 1)
    (by linarith [Nat.cast_nonneg (α := ℝ) k.val]) (i, 0) ?_⟩
  simpa only [level, radius₂, center₂, chart₂, one_mul, SetLike.mem_coe] using hi

/-- The native outer opens lie in their own coordinate domains. -/
theorem outer_source (i : Fin D.size × Fin 2) :
    (D.level 4 i : Set X) ⊆ (D.chart₂ i).source :=
  (D.chart₂ i).preimageBall_subset_source

/-- The actual middle family is contained in the outer family. -/
theorem middle_le_outer (i : Fin D.size × Fin 2) : D.level 3 i ≤ D.level 4 i :=
  D.level_mono (by norm_num) i

/-- The actual inner family is contained in the middle family. -/
theorem inner_le_middle (i : Fin D.size × Fin 2) : D.inner i ≤ D.level 3 i := by
  simpa only [inner, level, one_mul] using D.level_mono (a := 1) (b := 3) (by norm_num) i

/-- The chosen five native families satisfy the complete uniform lifting conclusion. -/
theorem uniform_lift [IsManifold 𝓘(ℂ) 1 X] [T2Space X] :
    ∃ C > 0, ∀ ξ : cocycles₁ (e := D.chart₂) (W := D.level 3) 1
          (subset_source_of_le D.outer_source D.middle_le_outer),
      ∃ t : compatibleTriples (e := D.chart₂)
          (W := D.level 4) (W' := D.level 3) (W'' := D.inner)
          1 D.outer_source D.middle_le_outer D.inner_le_middle,
        middleProjection (e := D.chart₂)
          (W := D.level 4) (W' := D.level 3) (W'' := D.inner)
          1 D.outer_source D.middle_le_outer D.inner_le_middle t = ξ ∧
          ‖t‖ ≤ C * ‖ξ‖ := by
  have hcover : ⋃ i, ((D.chart₂ i).preimageBall (D.center₂ i) (D.radius₂ i) : Set X) =
      univ := by
    simpa only [Fin.val_zero, Nat.cast_zero, zero_add, level, one_mul] using D.five_level_cover 0
  have hcov : IsOpenCover fun i ↦
      (D.chart₂ i).preimageBall (D.center₂ i) (D.radius₂ i) :=
    IsOpenCover.of_sets (fun i ↦ ((D.chart₂ i).preimageBall (D.center₂ i)
      (D.radius₂ i)).isOpen) hcover
  exact exists_uniform_middle_lift_preimageBall D.chart₂ D.center₂ D.radius₂ 1
    (fun i ↦ IsManifold.subset_maximalAtlas (D.mem_atlas i.1))
    (fun i ↦ D.radius_pos i.1)
    (fun i ↦ (closedBall_subset_closedBall
      (mul_le_mul_of_nonneg_right (by norm_num : (5 : ℝ) ≤ 6)
        (D.radius_pos i.1).le)).trans (D.closed_subset i.1)) hcov
    (fun _ _ ↦ mdifferentiableOn_const) (fun _ _ _ ↦ rfl)
    (fun _ _ _ _ _ ↦ one_mul 1)

variable [T2Space X]

/-- Middle coordinate-ball overlap closures are compact. -/
theorem compact_middle_overlap (i j : Fin D.size × Fin 2) :
    IsCompact (closure ((D.level 3 i ⊓ D.level 3 j : Opens X) : Set X)) := by
  have hcl : closedBall (D.center₂ i) (3 * D.radius₂ i) ⊆ (D.chart₂ i).target :=
    (closedBall_subset_closedBall
      (mul_le_mul_of_nonneg_right (by norm_num : (3 : ℝ) ≤ 6)
        (D.radius_pos i.1).le)).trans (D.closed_subset i.1)
  exact ((D.chart₂ i).isCompact_closure_preimageBall hcl).of_isClosed_subset
    isClosed_closure (closure_mono inter_subset_left)

/-- The closure of each middle overlap remains in its first chart. -/
theorem middle_overlap_subset_source (i j : Fin D.size × Fin 2) :
    closure ((D.level 3 i ⊓ D.level 3 j : Opens X) : Set X) ⊆ (D.chart₂ i).source := by
  have hcl : closedBall (D.center₂ i) (3 * D.radius₂ i) ⊆ (D.chart₂ i).target :=
    (closedBall_subset_closedBall
      (mul_le_mul_of_nonneg_right (by norm_num : (3 : ℝ) ≤ 6)
        (D.radius_pos i.1).le)).trans (D.closed_subset i.1)
  exact (closure_mono inter_subset_left).trans
    (((D.chart₂ i).closure_preimageBall_subset hcl
      (mul_lt_mul_of_pos_right (by norm_num : (3 : ℝ) < 4) (D.radius_pos i.1))).trans
        (D.outer_source i))

/-- Every native middle overlap has genuinely finite coordinate Lebesgue measure. -/
theorem finite_middle_measure (i j : Fin D.size × Fin 2) :
    IsFiniteMeasure (volume.restrict
      ((D.chart₂ i).imageOpens (D.level 3 i ⊓ D.level 3 j) : Set ℂ)) := by
  have hKC := (D.chart₂ i).isCompact_closure_imageOpens
    (D.compact_middle_overlap i j) (D.middle_overlap_subset_source i j)
  exact isFiniteMeasure_restrict.2
    ((measure_mono subset_closure).trans_lt hKC.measure_lt_top).ne

/-- The actual native Bergman cochain of the constant coboundary δ(0,1). -/
def constantCochain (i j : Fin D.size × Fin 2) :
    bergmanSpace ℂ ((D.chart₂ i).imageOpens (D.level 3 i ⊓ D.level 3 j)) := by
  let := D.finite_middle_measure i j
  exact BergmanSpace.of (fun _ : ℂ ↦ (j.2.val : ℂ) - i.2.val)
    (differentiableOn_const _) (memLp_const _)

/-- The Bergman representative evaluates to the actual constant coboundary. -/
theorem representative_constantCochain (i j : Fin D.size × Fin 2) {x : X}
    (hx : x ∈ D.level 3 i ⊓ D.level 3 j) :
    BergmanSpace.representative (D.constantCochain i j) (D.chart₂ i x) =
      (j.2.val : ℂ) - i.2.val := by
  exact BergmanSpace.representative_of _ _ _
    ((D.chart₂ i).map_mem_imageOpens
      (OpenPartialHomeomorph.preimageBall_subset_source hx.1) hx)

/-- The constant coboundary satisfies the native middle cocycle equation. -/
def constantCocycle : cocycles₁ (e := D.chart₂) (W := D.level 3) 1
          (subset_source_of_le D.outer_source D.middle_le_outer) := by
  refine ⟨D.constantCochain, ?_⟩
  rw [mem_cocycles₁_iff]
  intro i j k x hx
  rw [D.representative_constantCochain j k ⟨hx.1.2, hx.2⟩,
    D.representative_constantCochain i k ⟨hx.1.1, hx.2⟩,
    D.representative_constantCochain i j hx.1]
  simp only [Pi.one_apply, one_mul]
  ring

/-- Every point lies in an actual duplicated middle overlap with cocycle reading one. -/
theorem constantCocycle_reading_one (x : X) :
    ∃ i j, x ∈ D.level 3 i ⊓ D.level 3 j ∧
      BergmanSpace.representative (D.constantCocycle.val i j) (D.chart₂ i x) = 1 := by
  obtain ⟨i, hi⟩ := mem_iUnion.mp (D.covers.ge (mem_univ x))
  have hm0 : x ∈ D.level 3 (i, 0) := D.inner_le_middle (i, 0)
    (by simpa only [inner, chart₂, center₂, radius₂, SetLike.mem_coe] using hi)
  have hm1 : x ∈ D.level 3 (i, 1) := hm0
  refine ⟨(i, 0), (i, 1), ⟨hm0, hm1⟩, ?_⟩
  exact (D.representative_constantCochain (i, 0) (i, 1) ⟨hm0, hm1⟩).trans (by norm_num)

end DiscCover

end TauCeti.Examples.BergmanLifting
