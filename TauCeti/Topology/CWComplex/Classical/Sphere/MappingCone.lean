/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Ball.RadialEquiv
public import TauCeti.Topology.CWComplex.Classical.Sphere.Basic

/-!
# Attaching a cell to a sphere

Let `f : Sⁿ → Sⁿ` be a continuous map from the unit sphere of `EuclideanSpace ℝ (Fin (n + 1))` to
the unit sphere of `EuclideanSpace ℝ ι`, for `ι` of cardinality `n + 1`. Attaching an
`(n + 1)`-cell to `Sⁿ` along `f` gives the mapping cone `Sⁿ ∪_f Dⁿ⁺¹` of `f`. This file realizes it
as a subset of the product `EuclideanSpace ℝ ι × EuclideanSpace ℝ (Fin (n + 1))`, and shows that it
is a finite CW complex with one more cell than `Sⁿ`.

More generally, for real normed spaces `E` and `F` and `f : S(E) → S(F)` between their unit
spheres, `TauCeti.sphereMappingCone f ⊆ F × E` is the union of `S(F) × {0}` with the image of the
closed unit ball of `E` under the map (`TauCeti.sphereMappingConeDiskMap f`)

  `x ↦ (‖x‖ • f (‖x‖⁻¹ • x), (1 - ‖x‖) • x)`.

On the unit sphere this map is `x ↦ (f x, 0)` (`TauCeti.sphereMappingConeDiskMap_coe_sphere`), so
the ball is attached along `f`. On the open ball it is injective and misses `S(F) × {0}`: the norm
of the first coordinate is `‖x‖` (`TauCeti.norm_sphereMappingConeDiskMap_fst`), and the second
coordinate then determines `x`. So no quotient space is needed, and the ambient space is Hausdorff.

The CW structure `TauCeti.sphereMappingConeCWComplex h f` on `Sⁿ ∪_f Dⁿ⁺¹` has the cells of the
CW structure `TauCeti.sphereCWComplex h` on `Sⁿ`, a `0`-cell and an `n`-cell
(`TauCeti.sphereMappingConeSphereCell`), and one `(n + 1)`-cell
(`TauCeti.sphereMappingConeTopCell`).
The characteristic map of the `(n + 1)`-cell (`TauCeti.sphereMappingConeTopCellMap f`) is
`TauCeti.sphereMappingConeDiskMap f` after the radial homeomorphism
`ContinuousLinearEquiv.unitBallHomeomorph` from the closed unit ball of the sup norm on
`Fin (n + 1) → ℝ` to the Euclidean disk; on the boundary sphere it is `f`.

These are the complexes `Sⁿ ∪_f eⁿ⁺¹` on which cellular boundary formulas are tested. For `n ≥ 1`
the only cellular differential that can be nonzero is the one from the `(n + 1)`-cell to the
`n`-cell, which is multiplication by the degree of `f`; this file supplies the CW structure, not
that computation. For `n ≥ 1` and `f` of degree `m ≠ 0` these spaces are the Moore spaces
`M(ℤ/m, n)`, and for `n = 1` and `f z = z²` the real projective plane.

## Main definitions and results

* `TauCeti.sphereMappingConeDiskMap f`: the map attaching the unit ball along `f`, continuous by
  `TauCeti.continuous_sphereMappingConeDiskMap`.
* `TauCeti.sphereMappingCone f`: the space obtained by attaching the unit ball along `f`.
* `TauCeti.sphereMappingConeTopCellMap f`: the characteristic map of the `(n + 1)`-cell.
* `TauCeti.sphereMappingConeCWComplex h f`: the CW structure, which is finite
  (`TauCeti.finite_sphereMappingConeCWComplex`) with cells in dimensions `0`, `n` and `n + 1`
  (`TauCeti.nat_card_cell_sphereMappingConeCWComplex`).
* `TauCeti.sphereMappingConeSkeletonHomeomorph h f`: the identification of the `n`-skeleton with
  `Sⁿ`, by `a ↦ (a, 0)`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Chapter 0 for attaching cells and mapping cones, and Section 2.2 for cellular homology and the
  Moore spaces `Sⁿ ∪_f eⁿ⁺¹` with `f` of degree `m`.
-/

public section

noncomputable section

open Metric Set Topology Topology.RelCWComplex

universe u

namespace TauCeti

section DiskMap

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] (f : C(sphere (0 : E) 1, sphere (0 : F) 1))

open scoped Classical in
/-- The map from the unit ball of `E` attaching it to the unit sphere of `F` along
`f : S(E) → S(F)`. It sends `x` to `(‖x‖ • f (‖x‖⁻¹ • x), (1 - ‖x‖) • x)` in `F × E`, and `0` to
`0`. It is `x ↦ (f x, 0)` on the unit sphere (`TauCeti.sphereMappingConeDiskMap_coe_sphere`), and on
the open unit ball it is injective and misses `S(F) × {0}`. -/
def sphereMappingConeDiskMap (x : E) : F × E :=
  (if hx : x = 0 then 0 else
      ‖x‖ • (f (homeomorphUnitSphereProd _ ⟨x, mem_compl_singleton_iff.2 hx⟩).1 : F),
    (1 - ‖x‖) • x)

@[simp]
theorem sphereMappingConeDiskMap_snd (x : E) :
    (sphereMappingConeDiskMap f x).2 = (1 - ‖x‖) • x :=
  (rfl)

@[simp]
theorem sphereMappingConeDiskMap_zero : sphereMappingConeDiskMap f 0 = 0 := by
  simp [sphereMappingConeDiskMap]

/-- The first coordinate of `TauCeti.sphereMappingConeDiskMap f x` has norm `‖x‖`. -/
@[simp]
theorem norm_sphereMappingConeDiskMap_fst (x : E) :
    ‖(sphereMappingConeDiskMap f x).1‖ = ‖x‖ := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · simp [sphereMappingConeDiskMap, hx, norm_smul]

/-- Away from the origin, the first coordinate of `TauCeti.sphereMappingConeDiskMap f` is
`(y, r) ↦ r • f y` in the polar coordinates `homeomorphUnitSphereProd`. -/
private theorem sphereMappingConeDiskMap_fst_of_ne_zero (x : ({0}ᶜ : Set E)) :
    (sphereMappingConeDiskMap f x).1 =
      ((homeomorphUnitSphereProd E x).2 : ℝ) • (f (homeomorphUnitSphereProd E x).1 : F) := by
  have hx : (x : E) ≠ 0 := x.2
  simp only [sphereMappingConeDiskMap, hx, ↓reduceDIte, homeomorphUnitSphereProd_apply_snd_coe]

/-- On the unit sphere, `TauCeti.sphereMappingConeDiskMap f` is `x ↦ (f x, 0)`: the ball is
attached along `f`. -/
@[simp]
theorem sphereMappingConeDiskMap_coe_sphere (x : sphere (0 : E) 1) :
    sphereMappingConeDiskMap f x = ((f x : F), 0) := by
  have hx : (x : E) ∈ ({0}ᶜ : Set E) := ne_zero_of_mem_unit_sphere x
  have h1 : ‖(x : E)‖ = 1 := norm_eq_of_mem_sphere x
  -- In polar coordinates, `x` is `(x, 1)`.
  have hpolar : (homeomorphUnitSphereProd E ⟨x, hx⟩).1 = x :=
    Subtype.ext (by simp [h1])
  ext1
  · rw [sphereMappingConeDiskMap_fst_of_ne_zero f ⟨x, hx⟩, hpolar,
      homeomorphUnitSphereProd_apply_snd_coe, h1, one_smul]
  · simp [h1]

/-- The map attaching the unit ball along `f` is continuous, including at the origin, where the
direction `‖x‖⁻¹ • x` is undefined. -/
theorem continuous_sphereMappingConeDiskMap : Continuous (sphereMappingConeDiskMap f) := by
  have h1 : Continuous fun x ↦ (sphereMappingConeDiskMap f x).1 := by
    refine continuous_iff_continuousAt.2 fun x ↦ ?_
    rcases eq_or_ne x 0 with rfl | hx
    · -- At the origin the first coordinate tends to `0`, since its norm is `‖x‖`.
      rw [ContinuousAt, sphereMappingConeDiskMap_zero, Prod.fst_zero]
      exact squeeze_zero_norm (fun y ↦ (norm_sphereMappingConeDiskMap_fst f y).le)
        (continuous_norm.tendsto' 0 0 norm_zero)
    -- Away from the origin the first coordinate is `(y, r) ↦ r • f y` in polar coordinates.
    have : ContinuousOn (fun x ↦ (sphereMappingConeDiskMap f x).1) {0}ᶜ := by
      rw [continuousOn_iff_continuous_domRestrict]
      have heq : ({0}ᶜ : Set E).domRestrict (fun x ↦ (sphereMappingConeDiskMap f x).1) =
          (fun p ↦ (p.2 : ℝ) • (f p.1 : F)) ∘ homeomorphUnitSphereProd E := by
        ext1 x
        rw [Set.domRestrict_apply, sphereMappingConeDiskMap_fst_of_ne_zero, Function.comp_apply]
      rw [heq]
      exact ((continuous_subtype_val.comp continuous_snd).smul
        (continuous_subtype_val.comp (f.continuous.comp continuous_fst))).comp
          (homeomorphUnitSphereProd E).continuous
    exact this.continuousAt (isOpen_compl_singleton.mem_nhds hx)
  exact h1.prodMk ((continuous_const.sub continuous_norm).smul continuous_id)

/-- On the open unit ball, the second coordinate of `TauCeti.sphereMappingConeDiskMap f`, rescaled
by the norm of the first, recovers the point. -/
private theorem inv_smul_sphereMappingConeDiskMap {x : E} (hx : ‖x‖ < 1) :
    (1 - ‖(sphereMappingConeDiskMap f x).1‖)⁻¹ • (sphereMappingConeDiskMap f x).2 = x := by
  rw [norm_sphereMappingConeDiskMap_fst, sphereMappingConeDiskMap_snd, smul_smul,
    inv_mul_cancel₀ (sub_ne_zero.2 hx.ne'), one_smul]

/-- On the open unit ball, `TauCeti.sphereMappingConeDiskMap f` misses `S(F) × {0}`. -/
private theorem sphereMappingConeDiskMap_notMem_sphere {x : E} (hx : ‖x‖ < 1) :
    sphereMappingConeDiskMap f x ∉ (fun a ↦ (a, (0 : E))) '' sphere (0 : F) 1 := by
  rintro ⟨a, ha, hax⟩
  have h2 : (1 - ‖x‖) • x = 0 := by rw [← sphereMappingConeDiskMap_snd f, ← hax]
  obtain rfl : x = 0 := (smul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 hx.ne')
  have h1 : ‖a‖ = 0 := by simpa using congrArg (fun p ↦ ‖p.1‖) hax
  simp [mem_sphere_zero_iff_norm.1 ha] at h1

/-- The space obtained from the unit sphere `S(F)` by attaching the closed unit ball of `E` along
`f : S(E) → S(F)`: the union of `S(F) × {0}` with the image of the closed unit ball under
`TauCeti.sphereMappingConeDiskMap f`, inside `F × E`. For `E` of finite dimension this is the
mapping cone of `f`. -/
def sphereMappingCone : Set (F × E) :=
  (fun a ↦ (a, 0)) '' sphere (0 : F) 1 ∪ sphereMappingConeDiskMap f '' closedBall 0 1

@[simp]
theorem mem_sphereMappingCone {p : F × E} :
    p ∈ sphereMappingCone f ↔ (∃ a ∈ sphere (0 : F) 1, (a, 0) = p) ∨
      ∃ x ∈ closedBall (0 : E) 1, sphereMappingConeDiskMap f x = p :=
  Iff.rfl

end DiskMap

variable {ι : Type u} [Fintype ι] {n : ℕ} (h : Fintype.card ι = n + 1)
  (f : C(sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1, sphere (0 : EuclideanSpace ℝ ι) 1))

/-- The characteristic map of the `(n + 1)`-cell of `Sⁿ ∪_f Dⁿ⁺¹`: the map
`TauCeti.sphereMappingConeDiskMap f` attaching the disk, after the radial
homeomorphism from the closed unit ball of the sup norm on `Fin (n + 1) → ℝ` to the Euclidean disk.
It maps the open unit ball bijectively onto the image of the open disk. -/
def sphereMappingConeTopCellMap :
    PartialEquiv (Fin (n + 1) → ℝ) (EuclideanSpace ℝ ι × EuclideanSpace ℝ (Fin (n + 1))) where
  toFun y :=
    sphereMappingConeDiskMap f ((EuclideanSpace.equiv (Fin (n + 1)) ℝ).unitBallHomeomorph.symm y)
  invFun p := (EuclideanSpace.equiv (Fin (n + 1)) ℝ).unitBallHomeomorph ((1 - ‖p.1‖)⁻¹ • p.2)
  source := ball 0 1
  target := sphereMappingConeDiskMap f '' ball 0 1
  map_source' y hy := mem_image_of_mem _ (mem_ball_zero_iff.2
    ((EuclideanSpace.equiv _ ℝ).norm_unitBallHomeomorph_symm_lt_one_iff.2 (mem_ball_zero_iff.1 hy)))
  map_target' := by
    rintro _ ⟨x, hx, rfl⟩
    rw [inv_smul_sphereMappingConeDiskMap f (mem_ball_zero_iff.1 hx)]
    exact mem_ball_zero_iff.2
      ((EuclideanSpace.equiv _ ℝ).norm_unitBallHomeomorph_lt_one_iff.2 (mem_ball_zero_iff.1 hx))
  left_inv' y hy := by
    rw [inv_smul_sphereMappingConeDiskMap f
      ((EuclideanSpace.equiv _ ℝ).norm_unitBallHomeomorph_symm_lt_one_iff.2
        (mem_ball_zero_iff.1 hy)), Homeomorph.apply_symm_apply]
  right_inv' := by
    rintro _ ⟨x, hx, rfl⟩
    rw [inv_smul_sphereMappingConeDiskMap f (mem_ball_zero_iff.1 hx), Homeomorph.symm_apply_apply]

@[simp]
theorem sphereMappingConeTopCellMap_source : (sphereMappingConeTopCellMap f).source = ball 0 1 :=
  (rfl)

@[simp]
theorem sphereMappingConeTopCellMap_target :
    (sphereMappingConeTopCellMap f).target = sphereMappingConeDiskMap f '' ball 0 1 :=
  (rfl)

theorem sphereMappingConeTopCellMap_apply (y : Fin (n + 1) → ℝ) :
    sphereMappingConeTopCellMap f y =
      sphereMappingConeDiskMap f
        ((EuclideanSpace.equiv (Fin (n + 1)) ℝ).unitBallHomeomorph.symm y) :=
  (rfl)

theorem sphereMappingConeTopCellMap_symm_apply
    (p : EuclideanSpace ℝ ι × EuclideanSpace ℝ (Fin (n + 1))) :
    (sphereMappingConeTopCellMap f).symm p =
      (EuclideanSpace.equiv (Fin (n + 1)) ℝ).unitBallHomeomorph ((1 - ‖p.1‖)⁻¹ • p.2) :=
  (rfl)

/-- Read through the radial homeomorphism, the characteristic map of the `(n + 1)`-cell is
`TauCeti.sphereMappingConeDiskMap f`. -/
@[simp]
theorem sphereMappingConeTopCellMap_unitBallHomeomorph (x : EuclideanSpace ℝ (Fin (n + 1))) :
    sphereMappingConeTopCellMap f ((EuclideanSpace.equiv (Fin (n + 1)) ℝ).unitBallHomeomorph x) =
      sphereMappingConeDiskMap f x := by
  rw [sphereMappingConeTopCellMap_apply, Homeomorph.symm_apply_apply]

/-- The closed `(n + 1)`-cell is the image of the closed disk under
`TauCeti.sphereMappingConeDiskMap f`. -/
theorem image_sphereMappingConeTopCellMap_closedBall :
    sphereMappingConeTopCellMap f '' closedBall 0 1 =
      sphereMappingConeDiskMap f '' closedBall 0 1 := by
  have : (EuclideanSpace.equiv (Fin (n + 1)) ℝ).unitBallHomeomorph.symm '' closedBall 0 1 =
      closedBall 0 1 := by
    ext x
    simp [Homeomorph.image_symm, ContinuousLinearEquiv.norm_unitBallHomeomorph_le_one_iff]
  rw [← this, ← image_comp]
  rfl

/-- The inclusion `a ↦ (a, 0)` of `EuclideanSpace ℝ ι` into the product, with inverse the first
projection on its image. -/
private def inlPartialEquiv :
    PartialEquiv (EuclideanSpace ℝ ι) (EuclideanSpace ℝ ι × EuclideanSpace ℝ (Fin (n + 1))) where
  toFun a := (a, 0)
  invFun := Prod.fst
  source := univ
  target := {p | p.2 = 0}
  map_source' _ _ := rfl
  map_target' _ _ := mem_univ _
  left_inv' _ _ := rfl
  right_inv' _ hp := Prod.ext rfl hp.symm

/-- The cells of dimension `m` of `Sⁿ ∪_f Dⁿ⁺¹`: the cells of `Sⁿ`, and one cell if `m = n + 1`. -/
private abbrev MappingConeCell (m : ℕ) : Type u :=
  (letI := sphereCWComplex h; cell (sphere (0 : EuclideanSpace ℝ ι) 1) m) ⊕
    ULift.{u} (PLift (m = n + 1))

include h in
/-- The characteristic maps of `Sⁿ ∪_f Dⁿ⁺¹`: those of `Sⁿ` followed by `a ↦ (a, 0)`, and
`TauCeti.sphereMappingConeTopCellMap f`. -/
private def mappingConeCellMap : (m : ℕ) → MappingConeCell h m →
    PartialEquiv (Fin m → ℝ) (EuclideanSpace ℝ ι × EuclideanSpace ℝ (Fin (n + 1)))
  | m, .inl i => (letI := sphereCWComplex h; map m i).trans inlPartialEquiv
  | _, .inr ⟨⟨rfl⟩⟩ => sphereMappingConeTopCellMap f

private theorem isEmpty_mappingConeCell {m : ℕ} (hm : n + 2 ≤ m) :
    IsEmpty (MappingConeCell h m) := by
  have := isEmpty_cell_sphereCWComplex h (m := m) (by lia)
  exact ⟨fun i ↦ by rcases i with i | ⟨⟨⟨hm'⟩⟩⟩; exacts [isEmptyElim i, by lia]⟩

/-- The closed cells of `Sⁿ`, viewed in `Sⁿ ∪_f Dⁿ⁺¹`. -/
private theorem image_mappingConeCellMap_inl {m : ℕ}
    (i : letI := sphereCWComplex h; cell (sphere (0 : EuclideanSpace ℝ ι) 1) m)
    (s : Set (Fin m → ℝ)) :
    mappingConeCellMap h f m (.inl i) '' s =
      (fun a ↦ (a, (0 : EuclideanSpace ℝ (Fin (n + 1))))) ''
        ((letI := sphereCWComplex h; map m i) '' s) := by
  rw [mappingConeCellMap, PartialEquiv.coe_trans, image_comp]
  rfl

/-- An open cell of `Sⁿ`, viewed in `Sⁿ ∪_f Dⁿ⁺¹`, lies in `Sⁿ × {0}`. -/
private theorem image_mappingConeCellMap_inl_ball_subset {m : ℕ}
    (i : letI := sphereCWComplex h; cell (sphere (0 : EuclideanSpace ℝ ι) 1) m) :
    mappingConeCellMap h f m (.inl i) '' ball 0 1 ⊆
      (fun a ↦ (a, 0)) '' sphere (0 : EuclideanSpace ℝ ι) 1 := by
  let _ := sphereCWComplex h
  rw [image_mappingConeCellMap_inl]
  exact image_mono (openCell_subset_complex m i)

/-- The open cells of `Sⁿ ∪_f Dⁿ⁺¹` are disjoint. -/
private theorem pairwiseDisjoint_mappingConeCellMap :
    (univ : Set (Σ m, MappingConeCell h m)).PairwiseDisjoint
      (fun i ↦ mappingConeCellMap h f i.1 i.2 '' ball 0 1) := by
  let _ := sphereCWComplex h
  have hinj : Function.Injective
      (fun a : EuclideanSpace ℝ ι ↦ (a, (0 : EuclideanSpace ℝ (Fin (n + 1))))) :=
    fun _ _ h ↦ congrArg Prod.fst h
  -- The open `(n + 1)`-cell misses `Sⁿ × {0}`, which contains the open cells of `Sⁿ`.
  have htop : Disjoint (sphereMappingConeTopCellMap f '' ball 0 1)
      ((fun a ↦ (a, 0)) '' sphere (0 : EuclideanSpace ℝ ι) 1) := by
    refine disjoint_left.2 ?_
    rintro _ ⟨y, hy, rfl⟩
    exact sphereMappingConeDiskMap_notMem_sphere f
      ((EuclideanSpace.equiv _ ℝ).norm_unitBallHomeomorph_symm_lt_one_iff.2
        (mem_ball_zero_iff.1 hy))
  rintro ⟨m, i | ⟨⟨⟨rfl⟩⟩⟩⟩ - ⟨m', i' | ⟨⟨⟨h'⟩⟩⟩⟩ - hne
  · have hne' : (⟨m, i⟩ : Σ m, cell (sphere (0 : EuclideanSpace ℝ ι) 1) m) ≠ ⟨m', i'⟩ := by
      rintro ⟨⟩
      exact hne rfl
    simp only [Function.onFun, image_mappingConeCellMap_inl]
    exact (disjoint_image_iff hinj).2 (CWComplex.disjoint_openCell_of_ne hne')
  · subst h'
    exact (htop.mono_right (image_mappingConeCellMap_inl_ball_subset h f i)).symm
  · exact htop.mono_right (image_mappingConeCellMap_inl_ball_subset h f i')
  · subst h'
    exact absurd rfl hne

/-- The boundary of every cell of `Sⁿ ∪_f Dⁿ⁺¹` lies in the closed cells of lower dimension. -/
private theorem mapsTo_mappingConeCellMap (m : ℕ) (i : MappingConeCell h m) :
    MapsTo (mappingConeCellMap h f m i) (sphere 0 1)
      (⋃ (k < m) (j : MappingConeCell h k), mappingConeCellMap h f k j '' closedBall 0 1) := by
  let _ := sphereCWComplex h
  rcases i with i | ⟨⟨⟨rfl⟩⟩⟩
  · -- The boundary of a cell of `Sⁿ` lies in closed cells of `Sⁿ` of lower dimension.
    obtain ⟨I, hI⟩ := CWComplex.mapsTo m i
    intro y hy
    obtain ⟨k, hk, j, -, hj⟩ : ∃ k < m, ∃ j ∈ I k, map m i y ∈ map k j '' closedBall 0 1 := by
      simpa using hI hy
    refine mem_iUnion₂.2 ⟨k, hk, mem_iUnion.2 ⟨.inl j, ?_⟩⟩
    rw [image_mappingConeCellMap_inl]
    exact ⟨_, hj, rfl⟩
  -- The boundary of the `(n + 1)`-cell goes to `Sⁿ × {0}` by `f`, and the cells of `Sⁿ` have
  -- dimension at most `n`.
  intro y hy
  set x := (EuclideanSpace.equiv (Fin (n + 1)) ℝ).unitBallHomeomorph.symm y
  have hx : x ∈ sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 := mem_sphere_zero_iff_norm.2
    ((EuclideanSpace.equiv _ ℝ).norm_unitBallHomeomorph_symm_eq_one_iff.2
      (mem_sphere_zero_iff_norm.1 hy))
  have hfx : (f ⟨x, hx⟩ : EuclideanSpace ℝ ι) ∈ ⋃ (k : ℕ) (j : cell (sphere 0 1) k), closedCell k j
    := by rw [CWComplex.union]; exact (f ⟨x, hx⟩).2
  obtain ⟨k, j, hj⟩ := mem_iUnion₂.1 hfx
  have hk : k < n + 1 := by
    by_contra hk
    exact (isEmpty_cell_sphereCWComplex h (not_lt.1 hk)).elim j
  refine mem_iUnion₂.2 ⟨k, hk, mem_iUnion.2 ⟨.inl j, ?_⟩⟩
  rw [image_mappingConeCellMap_inl]
  refine ⟨_, hj, ?_⟩
  rw [mappingConeCellMap, sphereMappingConeTopCellMap_apply,
    sphereMappingConeDiskMap_coe_sphere f ⟨x, hx⟩]

/-- The closed cells of `Sⁿ ∪_f Dⁿ⁺¹` cover it. -/
private theorem iUnion_mappingConeCellMap :
    ⋃ (m : ℕ) (j : MappingConeCell h m), mappingConeCellMap h f m j '' closedBall 0 1 =
      sphereMappingCone f := by
  let _ := sphereCWComplex h
  simp_rw [iUnion_sum]
  rw [iUnion_union_distrib, sphereMappingCone]
  congr 1
  · simp_rw [image_mappingConeCellMap_inl, ← image_iUnion]
    exact congrArg _ (CWComplex.union (C := sphere (0 : EuclideanSpace ℝ ι) 1))
  · refine subset_antisymm (iUnion₂_subset fun m j ↦ ?_) ?_
    · rcases j with ⟨⟨⟨rfl⟩⟩⟩
      exact (image_sphereMappingConeTopCellMap_closedBall f).le
    · rw [← image_sphereMappingConeTopCellMap_closedBall f]
      exact subset_iUnion₂_of_subset (n + 1) ⟨⟨rfl⟩⟩ subset_rfl

private theorem finite_mappingConeCell (m : ℕ) : Finite (MappingConeCell h m) := by
  let _ := sphereCWComplex h
  have := finite_sphereCWComplex h
  have := RelCWComplex.FiniteType.finite_cell (C := sphere (0 : EuclideanSpace ℝ ι) 1) (D := ∅) m
  infer_instance

/-- The CW structure on the mapping cone `Sⁿ ∪_f Dⁿ⁺¹` of `f : Sⁿ → Sⁿ`, for `ι` of cardinality
`n + 1`: the cells of `TauCeti.sphereCWComplex h`, included by `a ↦ (a, 0)`
(`TauCeti.sphereMappingConeSphereCell`), and one `(n + 1)`-cell with characteristic map
`TauCeti.sphereMappingConeTopCellMap f` (`TauCeti.sphereMappingConeTopCell`). -/
@[instance_reducible]
def sphereMappingConeCWComplex : CWComplex (sphereMappingCone f) :=
  CWComplex.mkFinite _ (MappingConeCell h) (mappingConeCellMap h f)
    (Filter.eventually_atTop.2 ⟨n + 2, fun _ ↦ isEmpty_mappingConeCell h⟩)
    (finite_mappingConeCell h)
    (by
      let _ := sphereCWComplex h
      rintro m (i | ⟨⟨⟨rfl⟩⟩⟩)
      · rw [mappingConeCellMap, PartialEquiv.trans_source, source_eq]
        exact inter_eq_left.2 fun _ _ ↦ mem_univ _
      · rfl)
    (by
      let _ := sphereCWComplex h
      rintro m (i | ⟨⟨⟨rfl⟩⟩⟩)
      · rw [mappingConeCellMap, PartialEquiv.coe_trans]
        exact (continuous_id.prodMk continuous_const).comp_continuousOn (continuousOn m i)
      · exact (continuous_sphereMappingConeDiskMap f).comp_continuousOn
          (Homeomorph.continuous _).continuousOn)
    (by
      let _ := sphereCWComplex h
      rintro m (i | ⟨⟨⟨rfl⟩⟩⟩)
      · rw [mappingConeCellMap, PartialEquiv.coe_trans_symm, PartialEquiv.trans_target]
        exact (continuousOn_symm m i).comp continuous_fst.continuousOn fun _ hp ↦ hp.2
      · -- On the open cell the norm of the first coordinate is less than `1`.
        have hne : ∀ p ∈ (sphereMappingConeTopCellMap f).target, 1 - ‖p.1‖ ≠ 0 := by
          rintro _ ⟨x, hx, rfl⟩
          rw [norm_sphereMappingConeDiskMap_fst]
          exact sub_ne_zero.2 (mem_ball_zero_iff.1 hx).ne'
        exact (Homeomorph.continuous _).comp_continuousOn
          (((continuous_const.sub (continuous_norm.comp continuous_fst)).continuousOn.inv₀
            hne).smul continuous_snd.continuousOn))
    (pairwiseDisjoint_mappingConeCellMap h f) (mapsTo_mappingConeCellMap h f)
    (iUnion_mappingConeCellMap h f)

/-- The CW structure on `Sⁿ ∪_f Dⁿ⁺¹` is finite. -/
theorem finite_sphereMappingConeCWComplex :
    letI := sphereMappingConeCWComplex h f
    RelCWComplex.Finite (sphereMappingCone f) :=
  CWComplex.finite_mkFinite _ _ _ _ _ _ _ _ _ _ _

/-- The CW structure on `Sⁿ ∪_f Dⁿ⁺¹` has one cell in each of the dimensions `0`, `n` and `n + 1`
(two `0`-cells when `n = 0`). -/
theorem nat_card_cell_sphereMappingConeCWComplex (m : ℕ) :
    letI := sphereMappingConeCWComplex h f
    Nat.card (cell (sphereMappingCone f) m) =
      (if m = 0 then 1 else 0) + (if m = n then 1 else 0) + if m = n + 1 then 1 else 0 := by
  let _ := sphereCWComplex h
  have := finite_sphereCWComplex h
  have := RelCWComplex.FiniteType.finite_cell (C := sphere (0 : EuclideanSpace ℝ ι) 1) (D := ∅) m
  -- `CWComplex.mkFinite` takes the supplied family as its `cell` field, so the cells of dimension
  -- `m` are `MappingConeCell h m` by definition.
  change Nat.card (MappingConeCell h m) = _
  rw [Nat.card_sum, nat_card_cell_sphereCWComplex h m, Nat.card_ulift]
  rcases eq_or_ne m (n + 1) with rfl | hm
  · simp
  · simp [hm]

/-- The `(n + 1)`-cell of `Sⁿ ∪_f Dⁿ⁺¹`. -/
def sphereMappingConeTopCell :
    letI := sphereMappingConeCWComplex h f
    cell (sphereMappingCone f) (n + 1) :=
  Sum.inr ⟨⟨rfl⟩⟩

/-- The characteristic map of the `(n + 1)`-cell of `Sⁿ ∪_f Dⁿ⁺¹` is
`TauCeti.sphereMappingConeTopCellMap f`. -/
@[simp]
theorem map_sphereMappingConeTopCell :
    letI := sphereMappingConeCWComplex h f
    map (n + 1) (sphereMappingConeTopCell h f) = sphereMappingConeTopCellMap f :=
  -- `CWComplex.mkFinite` takes the supplied characteristic maps as its `map` field.
  (rfl)

/-- On the boundary sphere, read through the radial homeomorphism, the characteristic map of the
`(n + 1)`-cell of `Sⁿ ∪_f Dⁿ⁺¹` is `x ↦ (f x, 0)`: the cell is attached along `f`. -/
theorem map_sphereMappingConeTopCell_unitBallHomeomorph_coe_sphere
    (x : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :
    letI := sphereMappingConeCWComplex h f
    map (n + 1) (sphereMappingConeTopCell h f)
        ((EuclideanSpace.equiv (Fin (n + 1)) ℝ).unitBallHomeomorph x) =
      ((f x : EuclideanSpace ℝ ι), 0) := by
  rw [map_sphereMappingConeTopCell, sphereMappingConeTopCellMap_unitBallHomeomorph,
    sphereMappingConeDiskMap_coe_sphere]

/-- The cells of `Sⁿ ∪_f Dⁿ⁺¹` of dimension less than `n + 1` make up `Sⁿ × {0}`. -/
theorem coe_skeletonLT_sphereMappingCone :
    letI := sphereMappingConeCWComplex h f
    (skeletonLT (sphereMappingCone f) ((n + 1 : ℕ) : ℕ∞) : Set _) =
      (fun a ↦ (a, (0 : EuclideanSpace ℝ (Fin (n + 1))))) '' sphere (0 : EuclideanSpace ℝ ι) 1 := by
  let _ := sphereCWComplex h
  let _ := sphereMappingConeCWComplex h f
  rw [coe_skeletonLT, empty_union]
  refine subset_antisymm (iUnion₂_subset fun m hm ↦ iUnion_subset fun j ↦ ?_) ?_
  · -- `CWComplex.mkFinite` takes the supplied characteristic maps as its `map` field, so the
    -- closed cells of dimension `m` are those of `Sⁿ` and, if `m = n + 1`, the top cell.
    rcases j with i | ⟨⟨⟨rfl⟩⟩⟩
    · change mappingConeCellMap h f m (.inl i) '' closedBall 0 1 ⊆ _
      rw [image_mappingConeCellMap_inl]
      exact image_mono (closedCell_subset_complex m i)
    · exact absurd hm (lt_irrefl _)
  · -- Every point of `Sⁿ` lies in a closed cell of `Sⁿ`, of dimension at most `n`.
    rintro _ ⟨a, ha, rfl⟩
    rw [← CWComplex.union (C := sphere (0 : EuclideanSpace ℝ ι) 1)] at ha
    obtain ⟨k, j, hj⟩ := mem_iUnion₂.1 ha
    have hk : k < n + 1 := by
      by_contra hk
      exact (isEmpty_cell_sphereCWComplex h (not_lt.1 hk)).elim j
    refine mem_iUnion₂.2 ⟨k, by exact_mod_cast hk, mem_iUnion.2 ⟨.inl j, ?_⟩⟩
    change _ ∈ mappingConeCellMap h f k (.inl j) '' closedBall 0 1
    rw [image_mappingConeCellMap_inl]
    exact ⟨_, hj, rfl⟩

/-- A point lies in the `n`-skeleton of `Sⁿ ∪_f Dⁿ⁺¹` if and only if it lies in `Sⁿ × {0}`. -/
private theorem mem_skeletonLT_sphereMappingCone_iff
    {p : EuclideanSpace ℝ ι × EuclideanSpace ℝ (Fin (n + 1))} :
    letI := sphereMappingConeCWComplex h f
    p ∈ (skeletonLT (sphereMappingCone f) ((n + 1 : ℕ) : ℕ∞) :
      Set (EuclideanSpace ℝ ι × EuclideanSpace ℝ (Fin (n + 1)))) ↔
      p.1 ∈ sphere (0 : EuclideanSpace ℝ ι) 1 ∧ p.2 = 0 := by
  rw [coe_skeletonLT_sphereMappingCone]
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨ha, rfl⟩
  · exact fun hp ↦ ⟨p.1, hp.1, Prod.ext rfl hp.2.symm⟩

/-- The `n`-skeleton of `Sⁿ ∪_f Dⁿ⁺¹`, the union of its cells of dimension less than `n + 1`, is
`Sⁿ`, included by `a ↦ (a, 0)` (`TauCeti.coe_skeletonLT_sphereMappingCone`). -/
def sphereMappingConeSkeletonHomeomorph :
    letI := sphereMappingConeCWComplex h f
    sphere (0 : EuclideanSpace ℝ ι) 1 ≃ₜ skeletonLT (sphereMappingCone f) ((n + 1 : ℕ) : ℕ∞) where
  toFun a := ⟨((a : EuclideanSpace ℝ ι), 0),
    (mem_skeletonLT_sphereMappingCone_iff h f).2 ⟨a.2, rfl⟩⟩
  invFun p := ⟨(p : EuclideanSpace ℝ ι × EuclideanSpace ℝ (Fin (n + 1))).1,
    ((mem_skeletonLT_sphereMappingCone_iff h f).1 p.2).1⟩
  left_inv _ := rfl
  right_inv p :=
    Subtype.ext (Prod.ext rfl ((mem_skeletonLT_sphereMappingCone_iff h f).1 p.2).2.symm)
  continuous_toFun := (continuous_subtype_val.prodMk continuous_const).subtype_mk _
  continuous_invFun := (continuous_fst.comp continuous_subtype_val).subtype_mk _

@[simp]
theorem coe_sphereMappingConeSkeletonHomeomorph_apply (a : sphere (0 : EuclideanSpace ℝ ι) 1) :
    (sphereMappingConeSkeletonHomeomorph h f a :
        EuclideanSpace ℝ ι × EuclideanSpace ℝ (Fin (n + 1))) =
      ((a : EuclideanSpace ℝ ι), 0) :=
  (rfl)

@[simp]
theorem coe_sphereMappingConeSkeletonHomeomorph_symm_apply
    (p : letI := sphereMappingConeCWComplex h f
      skeletonLT (sphereMappingCone f) ((n + 1 : ℕ) : ℕ∞)) :
    ((sphereMappingConeSkeletonHomeomorph h f).symm p : EuclideanSpace ℝ ι) =
      (p : EuclideanSpace ℝ ι × EuclideanSpace ℝ (Fin (n + 1))).1 :=
  (rfl)

/-- `Sⁿ ∪_f Dⁿ⁺¹` has a single cell of dimension `n + 1`. -/
theorem eq_sphereMappingConeTopCell
    (j : letI := sphereMappingConeCWComplex h f; cell (sphereMappingCone f) (n + 1)) :
    j = sphereMappingConeTopCell h f := by
  -- `CWComplex.mkFinite` takes the supplied family as its `cell` field, so `j` is a cell of `Sⁿ` of
  -- dimension `n + 1`, of which there are none, or the `(n + 1)`-cell.
  rcases j with i | ⟨⟨⟨_⟩⟩⟩
  · exact (isEmpty_cell_sphereCWComplex h le_rfl).elim i
  · rfl

/-- A cell of `Sⁿ`, as a cell of `Sⁿ ∪_f Dⁿ⁺¹`. -/
def sphereMappingConeSphereCell {m : ℕ}
    (i : letI := sphereCWComplex h; cell (sphere (0 : EuclideanSpace ℝ ι) 1) m) :
    letI := sphereMappingConeCWComplex h f
    cell (sphereMappingCone f) m :=
  Sum.inl i

/-- Distinct cells of `Sⁿ` are distinct cells of `Sⁿ ∪_f Dⁿ⁺¹`. -/
theorem sphereMappingConeSphereCell_injective {m : ℕ} :
    Function.Injective (sphereMappingConeSphereCell h f (m := m)) :=
  Sum.inl_injective

/-- Every cell of `Sⁿ ∪_f Dⁿ⁺¹` of dimension other than `n + 1` is a cell of `Sⁿ`. In dimension
`n + 1` the only cell is the top cell (`TauCeti.eq_sphereMappingConeTopCell`). -/
theorem exists_sphereMappingConeSphereCell_eq {m : ℕ} (hm : m ≠ n + 1)
    (j : letI := sphereMappingConeCWComplex h f; cell (sphereMappingCone f) m) :
    ∃ i, sphereMappingConeSphereCell h f i = j := by
  -- `CWComplex.mkFinite` takes the supplied family as its `cell` field, so `j` is a cell of `Sⁿ` or
  -- the `(n + 1)`-cell.
  rcases j with i | ⟨⟨⟨hm'⟩⟩⟩
  · exact ⟨i, rfl⟩
  · exact absurd hm' hm

/-- The characteristic map of a cell of `Sⁿ`, viewed in `Sⁿ ∪_f Dⁿ⁺¹`, is that of `Sⁿ` followed by
`a ↦ (a, 0)`. -/
@[simp]
theorem map_sphereMappingConeSphereCell_apply {m : ℕ}
    (i : letI := sphereCWComplex h; cell (sphere (0 : EuclideanSpace ℝ ι) 1) m)
    (y : Fin m → ℝ) :
    letI := sphereCWComplex h
    letI := sphereMappingConeCWComplex h f
    map m (sphereMappingConeSphereCell h f i) y = (map m i y, 0) :=
  -- `CWComplex.mkFinite` takes the supplied characteristic maps as its `map` field.
  (rfl)

end TauCeti
