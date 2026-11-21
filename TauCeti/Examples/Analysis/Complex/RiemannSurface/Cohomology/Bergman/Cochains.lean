/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.RiemannSurface.Cohomology.Bergman.Cochains
public import TauCeti.Geometry.Manifold.CoordinateBall

/-!
# Finite coordinate covers and native Bergman coboundaries

Finite coordinate balls have five nested covering levels and compact overlap closures. Duplicating
each chart by two labels gives an actual native Bergman cocycle whose representative reads one
on a duplicated overlap through every point. The concrete compact-curve lifting applications are
in `TauCeti.Examples.Analysis.Complex.RiemannSurface.Cohomology.Bergman.Lifting`.
-/

public noncomputable section

open CategoryTheory Metric Set TopologicalSpace MeasureTheory
open scoped Manifold ContDiff ENNReal Topology

universe w
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
  closedBall_six_subset_target : ∀ i, closedBall (center i) (6 * radius i) ⊆ (chart i).target
  iUnion_preimageBall_eq_univ : ⋃ i, ((chart i).preimageBall (center i) (radius i) : Set X) = univ

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
abbrev level (a : ℝ) (i : Fin D.size × Fin 2) : Opens X :=
  (D.chart₂ i).preimageBall (D.center₂ i) (a * D.radius₂ i)

/-- The native inner family uses its literal radius. -/
abbrev inner (i : Fin D.size × Fin 2) : Opens X :=
  (D.chart₂ i).preimageBall (D.center₂ i) (D.radius₂ i)

/-- The duplicated chart remains in the actual atlas. -/
theorem mem_atlas_chart₂ (i : Fin D.size × Fin 2) : D.chart₂ i ∈ atlas ℂ X := by
  simpa only [chart₂] using D.mem_atlas i.1

/-- Every duplicated chart has a positive coordinate radius. -/
theorem radius₂_pos (i : Fin D.size × Fin 2) : 0 < D.radius₂ i := by
  simpa only [radius₂] using D.radius_pos i.1

/-- The duplicated family depends only on the original chart index. -/
@[simp]
theorem level_fst (a : ℝ) (i : Fin D.size) (k : Fin 2) :
    D.level a (i, k) = (D.chart i).preimageBall (D.center i) (a * D.radius i) := by
  simp only [level, chart₂, center₂, radius₂]

/-- Every smaller closed coordinate ball remains in the actual chart target. -/
theorem closedBall_subset_target (i : Fin D.size × Fin 2) {a : ℝ} (ha : a ≤ 6) :
    closedBall (D.center₂ i) (a * D.radius₂ i) ⊆ (D.chart₂ i).target :=
  (closedBall_subset_closedBall
    (mul_le_mul_of_nonneg_right ha (D.radius_pos i.1).le)).trans
      (D.closedBall_six_subset_target i.1)

/-- Increasing the radius gives literal inclusion of these native opens. -/
theorem level_mono {a b : ℝ} (hab : a ≤ b) (i : Fin D.size × Fin 2) :
    D.level a i ≤ D.level b i :=
  (D.chart₂ i).preimageBall_mono (mul_le_mul_of_nonneg_right hab (D.radius_pos i.1).le)

/-- Each of the five nested coordinate-ball families cover the actual base. -/
theorem iUnion_level_eq_univ (k : Fin 5) :
    ⋃ i, (D.level ((k.val : ℝ) + 1) i : Set X) = univ := by
  apply eq_univ_of_forall
  intro x
  obtain ⟨i, hi⟩ := mem_iUnion.mp (D.iUnion_preimageBall_eq_univ.ge (mem_univ x))
  refine mem_iUnion.mpr ⟨(i, 0), D.level_mono (a := 1)
    (by linarith [Nat.cast_nonneg (α := ℝ) k.val]) (i, 0) ?_⟩
  simpa only [level, radius₂, center₂, chart₂, one_mul, SetLike.mem_coe] using hi

/-- The native outer opens lie in their own coordinate domains. -/
theorem level_four_subset_source (i : Fin D.size × Fin 2) :
    (D.level 4 i : Set X) ⊆ (D.chart₂ i).source :=
  (D.chart₂ i).preimageBall_subset_source

/-- The actual middle family is contained in the outer family. -/
theorem level_three_le_level_four (i : Fin D.size × Fin 2) : D.level 3 i ≤ D.level 4 i :=
  D.level_mono (by norm_num) i

/-- The actual inner family is contained in the middle family. -/
theorem inner_le_level_three (i : Fin D.size × Fin 2) : D.inner i ≤ D.level 3 i := by
  simpa only [inner, level, one_mul] using D.level_mono (a := 1) (b := 3) (by norm_num) i


/-- The actual native middle cocycles for the chosen family. -/
abbrev cocycles := cocycles₁ (e := D.chart₂) (W := D.level 3) 1
  (subset_source_of_le D.level_four_subset_source D.level_three_le_level_four)

/-- The actual native compatible triples for the chosen outer, middle and inner families. -/
abbrev triples := compatibleTriples (e := D.chart₂)
  (W := D.level 4) (W' := D.level 3) (W'' := D.inner)
  1 D.level_four_subset_source D.level_three_le_level_four D.inner_le_level_three

/-- The actual native middle projection for these three families. -/
abbrev proj := middleProjection (e := D.chart₂)
  (W := D.level 4) (W' := D.level 3) (W'' := D.inner)
  1 D.level_four_subset_source D.level_three_le_level_four D.inner_le_level_three

variable [T2Space X]

/-- Middle coordinate-ball overlap closures are compact. -/
theorem isCompact_closure_level_three_inf (i j : Fin D.size × Fin 2) :
    IsCompact (closure ((D.level 3 i ⊓ D.level 3 j : Opens X) : Set X)) := by
  exact ((D.chart₂ i).isCompact_closure_preimageBall
    (D.closedBall_subset_target i (by norm_num : (3 : ℝ) ≤ 6))).of_isClosed_subset
    isClosed_closure (closure_mono inter_subset_left)

/-- The closure of each middle overlap remains in its first chart. -/
theorem closure_level_three_inf_subset_source (i j : Fin D.size × Fin 2) :
    closure ((D.level 3 i ⊓ D.level 3 j : Opens X) : Set X) ⊆ (D.chart₂ i).source := by
  exact (closure_mono inter_subset_left).trans
    (((D.chart₂ i).closure_preimageBall_subset
      (D.closedBall_subset_target i (by norm_num : (3 : ℝ) ≤ 6))
      (mul_lt_mul_of_pos_right (by norm_num : (3 : ℝ) < 4) (D.radius_pos i.1))).trans
        (D.level_four_subset_source i))

/-- Every native middle overlap has genuinely finite coordinate Lebesgue measure. -/
theorem isFiniteMeasure_restrict_imageOpens_level_three_inf (i j : Fin D.size × Fin 2) :
    IsFiniteMeasure (volume.restrict
      ((D.chart₂ i).imageOpens (D.level 3 i ⊓ D.level 3 j) : Set ℂ)) := by
  exact (D.chart₂ i).isFiniteMeasure_restrict_imageOpens volume
    (D.isCompact_closure_level_three_inf i j) (D.closure_level_three_inf_subset_source i j)

/-- The actual native Bergman cochain of the constant coboundary δ(0,1). -/
def constantCochain (i j : Fin D.size × Fin 2) :
    bergmanSpace ℂ ((D.chart₂ i).imageOpens (D.level 3 i ⊓ D.level 3 j)) := by
  let := D.isFiniteMeasure_restrict_imageOpens_level_three_inf i j
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
def constantCocycle : D.cocycles := by
  refine ⟨D.constantCochain, ?_⟩
  rw [mem_cocycles₁_iff]
  intro i j k x hx
  rw [D.representative_constantCochain j k ⟨hx.1.2, hx.2⟩,
    D.representative_constantCochain i k ⟨hx.1.1, hx.2⟩,
    D.representative_constantCochain i j hx.1]
  simp only [Pi.one_apply, one_mul]
  ring

/-- Every point lies in an actual duplicated middle overlap with cocycle reading one. -/
theorem exists_representative_constantCocycle_eq_one (x : X) :
    ∃ i j, x ∈ D.level 3 i ⊓ D.level 3 j ∧
      BergmanSpace.representative (D.constantCocycle.val i j) (D.chart₂ i x) = 1 := by
  obtain ⟨i, hi⟩ := mem_iUnion.mp (D.iUnion_preimageBall_eq_univ.ge (mem_univ x))
  have hm0 : x ∈ D.level 3 (i, 0) := D.inner_le_level_three (i, 0)
    (by simpa only [inner, chart₂, center₂, radius₂, SetLike.mem_coe] using hi)
  have hm1 : x ∈ D.level 3 (i, 1) := by
    simpa only [D.level_fst] using hm0
  refine ⟨(i, 0), (i, 1), ⟨hm0, hm1⟩, ?_⟩
  exact (D.representative_constantCochain (i, 0) (i, 1) ⟨hm0, hm1⟩).trans (by norm_num)

/-- The constant native coboundary is nonzero on every nonempty covered base. -/
theorem constantCocycle_ne_zero (x : X) : D.constantCocycle ≠ 0 := by
  intro h
  obtain ⟨i, j, hx, heval⟩ := D.exists_representative_constantCocycle_eq_one x
  have hξ : D.constantCocycle.val i j = 0 := by
    simpa only [ZeroMemClass.coe_zero, Pi.zero_apply] using
      congrArg (fun ξ ↦ ξ.val i j) h
  have hmem := (D.chart₂ i).map_mem_imageOpens
    (D.level_four_subset_source i (D.level_three_le_level_four i hx.1)) hx
  rw [hξ, BergmanSpace.representative_zero hmem] at heval
  exact zero_ne_one heval

end DiscCover

end TauCeti.Examples.BergmanLifting
