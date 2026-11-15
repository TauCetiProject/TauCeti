/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Grading
public import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Topology.Instances.AddCircle.DenseSubgroup
import Mathlib.Tactic.Ring

/-!
# Dense periods and the support of Floer kernels

Two period models with the same dense area periods `a + √2 b` on spherical classes
`(a, b) ∈ ℤ × ℤ` show how the support of capped Floer kernels depends on the Chern-zero periods
rather than on the area periods alone.

* **A product of two spheres.** For `S² × S²` with a product symplectic form of areas `1` and
  `√2` on the two factors, the spherical classes are `ℤ × ℤ`, with area `a + √2 b` and first Chern
  number `2 a + 2 b`. The areas of its period group are dense in `ℝ`
  (`DensePeriodExample.dense_range_area_sphereProduct`). Since `√2 ≠ 1`, there are Chern-zero
  classes of nonzero area, so there is no energy ceiling of the monotone branch
  (`DensePeriodExample.not_ker_chern_le_ker_area`). Nevertheless the Chern-zero classes `(a, -a)`
  have the discrete areas `a (1 - √2)` (`DensePeriodExample.map_area_ker_chern_sphereProduct`),
  so in each Chern number only finitely many classes have area in a bounded window
  (`DensePeriodExample.finite_setOf_chern_eq_and_area_mem_Icc`). Hence the energy bound and
  the index of a product kernel already give its finiteness hypothesis
  (`TauCeti.Floer.mem_novikovModule_of_discreteTopology`, applied with
  `DensePeriodExample.discreteTopology_map_area_ker_chern_sphereProduct`).
* **A Chern-zero target.** If the first Chern class vanishes on spheres, as on a symplectic
  Calabi–Yau manifold, every class has Chern number zero. With area periods `a + √2 b` the
  Chern-zero periods are dense (`DensePeriodExample.dense_map_area_ker_chern_chernZero`), and every
  open window of areas contains infinitely many classes
  (`DensePeriodExample.infinite_setOf_area_mem_Ioo`). By
  `TauCeti.Floer.exists_notMem_novikovModule_of_dense`, energy bounds and gradings then do not
  give the finiteness hypothesis of a product kernel; it must come from compactness of the moduli
  spaces below each energy level.

## References

* H. Hofer and D. A. Salamon, *Floer homology and Novikov rings*, in *The Floer memorial
  volume*, Progr. Math. 133 (1995), 483–524.
* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, the chapter on
  Floer homology and Novikov rings.
-/

public section

noncomputable section

open Set

namespace TauCeti.Floer.DensePeriodExample

/-- The area `a + √2 b` of the spherical class `(a, b)`. -/
def area : ℤ × ℤ →+ ℝ where
  toFun s := s.1 + √2 * s.2
  map_zero' := by simp
  map_add' _ _ := by simp; ring

/-- The first Chern number `2 a + 2 b` of the class `(a, b)` in `π₂(S² × S²) = ℤ × ℤ`. -/
def chernSphereProduct : ℤ × ℤ →+ ℤ where
  toFun s := 2 * s.1 + 2 * s.2
  map_zero' := by simp
  map_add' _ _ := by simp; ring

@[simp]
theorem area_apply (s : ℤ × ℤ) : area s = s.1 + √2 * s.2 :=
  (rfl)

@[simp]
theorem chernSphereProduct_apply (s : ℤ × ℤ) : chernSphereProduct s = 2 * s.1 + 2 * s.2 :=
  (rfl)

/-- The areas `a + √2 b` are dense in `ℝ`. -/
theorem dense_range_area : Dense (range area) := by
  refine Dense.mono ?_ (dense_addSubgroupClosure_pair_iff.2 (by
    rw [div_one]; exact irrational_sqrt_two) : Dense ((AddSubgroup.closure {√2, (1 : ℝ)} :
      AddSubgroup ℝ) : Set ℝ))
  rw [← AddMonoidHom.coe_range, SetLike.coe_subset_coe, AddSubgroup.closure_le, pair_subset_iff]
  exact ⟨⟨(0, 1), by simp⟩, ⟨(1, 0), by simp⟩⟩

/-- In the product of two spheres with areas `1` and `√2`, the areas of the period group are
dense in `ℝ`. -/
theorem dense_range_area_sphereProduct :
    Dense (range (PeriodGroup.area area chernSphereProduct)) := by
  rw [← AddMonoidHom.coe_range, PeriodGroup.range_area, AddMonoidHom.coe_range]
  exact dense_range_area

/-- In the product of two spheres with areas `1` and `√2`, the class `(1, -1)` has vanishing first
Chern number but nonzero area, so the energy ceiling of the monotone branch
(`TauCeti.Floer.exists_abs_add_sub_le_of_ker_le`) does not apply. -/
theorem not_ker_chern_le_ker_area : ¬chernSphereProduct.ker ≤ area.ker := fun h => by
  have h1 : area (1, -1) = 0 := h (by simp [AddMonoidHom.mem_ker])
  have h2 : (1 : ℝ) < √2 := by
    rw [Real.lt_sqrt zero_le_one]
    norm_num
  simp only [area_apply, Int.cast_one, Int.cast_neg, mul_neg, mul_one] at h1
  linarith

/-- In the product of two spheres with areas `1` and `√2`, the Chern-zero classes `(a, -a)` have
the areas `a (1 - √2)`. -/
theorem map_area_ker_chern_sphereProduct :
    (PeriodGroup.chern area chernSphereProduct).ker.map
        (PeriodGroup.area area chernSphereProduct) =
      AddSubgroup.zmultiples (1 - √2) := by
  ext x
  simp only [AddSubgroup.mem_map, AddMonoidHom.mem_ker, AddSubgroup.mem_zmultiples_iff,
    QuotientAddGroup.mk_surjective.exists, PeriodGroup.chern_mk, PeriodGroup.area_mk,
    Prod.exists, area_apply, chernSphereProduct_apply, zsmul_eq_mul]
  constructor
  · rintro ⟨a, b, hc, rfl⟩
    obtain rfl : b = -a := by omega
    exact ⟨a, by push_cast; ring⟩
  · rintro ⟨a, rfl⟩
    exact ⟨a, -a, by ring, by push_cast; ring⟩

/-- In the product of two spheres with areas `1` and `√2`, the areas of the Chern-zero classes form
a discrete subgroup of `ℝ`. -/
theorem discreteTopology_map_area_ker_chern_sphereProduct :
    DiscreteTopology ((PeriodGroup.chern area chernSphereProduct).ker.map
      (PeriodGroup.area area chernSphereProduct)) := by
  rw [map_area_ker_chern_sphereProduct]
  infer_instance

/-- In the product of two spheres with areas `1` and `√2`, only finitely many classes of the period
group with a given first Chern number have area in a bounded window, although the areas of all
classes are dense. -/
theorem finite_setOf_chern_eq_and_area_mem_Icc (k : ℤ) (a b : ℝ) :
    {γ : PeriodGroup area chernSphereProduct |
      PeriodGroup.chern area chernSphereProduct γ = k ∧
        PeriodGroup.area area chernSphereProduct γ ∈ Icc a b}.Finite :=
  AddTorsor.finite_setOf_eq_and_mem_Icc (PeriodGroup.disjoint_ker_area_ker_chern _ _)
    discreteTopology_map_area_ker_chern_sphereProduct k a b

/-- If the first Chern number vanishes on spherical classes and their areas are `a + √2 b`, the
areas of the Chern-zero classes of the period group are dense in `ℝ`. -/
theorem dense_map_area_ker_chern_chernZero :
    Dense (((PeriodGroup.chern area 0).ker.map (PeriodGroup.area area 0) :
      AddSubgroup ℝ) : Set ℝ) := by
  have hker : (PeriodGroup.chern area (0 : ℤ × ℤ →+ ℤ)).ker = ⊤ :=
    eq_top_iff.2 fun γ _ => PeriodGroup.chern_eq_zero (fun _ => rfl) γ
  rw [hker, ← AddMonoidHom.range_eq_map, PeriodGroup.range_area, AddMonoidHom.coe_range]
  exact dense_range_area

/-- If the first Chern number vanishes on spherical classes and their areas are `a + √2 b`, every
open window of areas contains infinitely many classes of the period group. -/
theorem infinite_setOf_area_mem_Ioo {a b : ℝ} (hab : a < b) :
    {γ : PeriodGroup area 0 | PeriodGroup.area area 0 γ ∈ Ioo a b}.Infinite := by
  refine Infinite.mono ?_
    (AddTorsor.infinite_setOf_eq_zero_and_mem_Ioo dense_map_area_ker_chern_chernZero hab)
  exact fun γ hγ => hγ.2

end TauCeti.Floer.DensePeriodExample
