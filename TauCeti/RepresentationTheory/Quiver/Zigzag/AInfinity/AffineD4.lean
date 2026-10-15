/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.AffineDynkinType.Basic
public import TauCeti.RepresentationTheory.Quiver.Zigzag.AInfinity.Loop

/-!
# Liu--Wang's quartic `A∞` deformation of the affine `D₄` zigzag algebra

Liu and Wang (Example 4.7) exhibit a minimal `A∞` structure on the zigzag algebra of the affine
`D₄` graph whose only higher operation is a quartic operation `m₄` built from one closed walk. In
the numbering of `TauCeti.AffineDynkinType.graph (D 4)`, node `1` is the centre, of valency four,
and `0, 2, 3, 4` are leaves. Write `α_l` for the arrow from a leaf `l` to the centre and `β_l` for
the arrow from the centre to `l`. Liu--Wang's two leaves `1` and `4` are taken to be the nodes `0`
and `4`. For one common scalar `c`, the operation `m₄` vanishes on every arrow quadruple other than
the four cyclic rotations of the closed walk `β₄ α₁ β₁ α₄`, and on those it takes the values

```text
m₄(β₄, α₁, β₁, α₄) = c β₄ α₄,      m₄(α₄, β₄, α₁, β₁) = c α₁ β₁,
m₄(β₁, α₄, β₄, α₁) = c β₁ α₁,      m₄(α₁, β₁, α₄, β₄) = c α₄ β₄.
```

Products are in Tau Ceti's later-factor-first order, so the last input of each word is traversed
first, and each value is the volume class at the base of the walk. Each rotation of the walk gives
a loop operation `TauCeti.zigzagLoopOperation`, and `m₄` is `c` times their sum. The general
construction `TauCeti.zigzagLoopAInfinityAlgebra` therefore proves the Stasheff identities, with
arrows in cohomological degree `1`. It also shows that the resulting algebra is minimal and
strictly unital, and that `m₄` has bidegree `(-2, 2)` for the cohomological and Adams gradings.

This is a test case of a non-ADE minimal deformation. Its nontriviality modulo `A∞` isomorphism
is not proved here.

## Main definitions

* `TauCeti.liuWangAffineD4Walk`: the closed walk `β₄ α₁ β₁ α₄`, as four darts in product order.
* `TauCeti.liuWangAffineD4AInfinityAlgebra`: Liu--Wang's `A∞` algebra with scalar `c`.

## Main results

* `TauCeti.liuWangAffineD4AInfinityAlgebra_m_four_values`: the four displayed values of `m₄`.
* `TauCeti.liuWangAffineD4AInfinityAlgebra_m_four_eq_zero`: `m₄` vanishes on every other arrow
  quadruple.
* `TauCeti.liuWangAffineD4AInfinityAlgebra_m_eq_zero`: there are no other higher operations.
* `TauCeti.isMinimal_liuWangAffineD4AInfinityAlgebra`,
  `TauCeti.strictUnit_one_liuWangAffineD4AInfinityAlgebra` and
  `TauCeti.isHomogeneous_liuWangAffineD4AInfinityAlgebra_m_adams`: the algebra is minimal and
  strictly unital, and `m₄` has bidegree `(-2, 2)`.

## References

* Y. Liu and Z. Wang, *A-infinity deformations of zigzag algebras via Ginzburg dg algebras*,
  Example 4.7.
-/

public section

namespace TauCeti

open PathAlgebra DoubledQuiver

universe w

/-- **Liu--Wang's closed walk** `β₄ α₁ β₁ α₄` in the affine `D₄` graph, listed in product order:
the darts `1 → 4`, `0 → 1`, `1 → 0` and `4 → 1`. Read from the last entry, it is the walk
`4 → 1 → 0 → 1 → 4`. -/
def liuWangAffineD4Walk : Fin 4 → (AffineDynkinType.D 4).graph.Dart :=
  ![⟨(1, 4), (AffineDynkinType.graph_D_adj le_rfl).2 (by decide)⟩,
    ⟨(0, 1), (AffineDynkinType.graph_D_adj le_rfl).2 (by decide)⟩,
    ⟨(1, 0), (AffineDynkinType.graph_D_adj le_rfl).2 (by decide)⟩,
    ⟨(4, 1), (AffineDynkinType.graph_D_adj le_rfl).2 (by decide)⟩]

/-- The darts of Liu--Wang's walk are pairwise distinct. -/
theorem liuWangAffineD4Walk_injective : Function.Injective liuWangAffineD4Walk := by
  decide

/-- Consecutive darts of every cyclic rotation of Liu--Wang's walk are composable, cyclically. -/
theorem liuWangAffineD4Walk_sub_fst_eq_snd (i j : Fin 4) :
    (liuWangAffineD4Walk (i - j)).fst = (liuWangAffineD4Walk (i + 1 - j)).snd := by
  revert i j
  decide

variable (k : Type w) [CommRing k]

/-- The class in the affine `D₄` zigzag algebra of the arrow of the `i`-th dart of Liu--Wang's walk:
`β₄`, `α₁`, `β₁` and `α₄` for `i = 0, 1, 2, 3`. -/
noncomputable def liuWangAffineD4Arrow (i : Fin 4) :
    nonisolatedZigzagQuotient k (AffineDynkinType.D 4).graph :=
  zigzagMk k _ (ofArrow (arrow _ (liuWangAffineD4Walk i).adj))

/-- The coefficients of Liu--Wang's quartic operation: the scalar `c` on each of the four cyclic
rotations of the walk, and zero elsewhere. -/
noncomputable def liuWangAffineD4Coefficients (c : k) :
    (Fin 4 → (AffineDynkinType.D 4).graph.Dart) →₀ k :=
  ∑ j : Fin 4, Finsupp.single (fun i ↦ liuWangAffineD4Walk (i - j)) c

variable {k} in
open scoped Classical in
/-- The coefficient of four darts is `c` exactly when they form a cyclic rotation of Liu--Wang's
walk. -/
theorem liuWangAffineD4Coefficients_apply (c : k) (d : Fin 4 → (AffineDynkinType.D 4).graph.Dart) :
    liuWangAffineD4Coefficients k c d =
      if ∃ j, d = fun i ↦ liuWangAffineD4Walk (i - j) then c else 0 := by
  have hinj (j j' : Fin 4) :
      ((fun i ↦ liuWangAffineD4Walk (i - j)) = fun i ↦ liuWangAffineD4Walk (i - j')) ↔ j = j' := by
    refine ⟨fun h ↦ ?_, fun h ↦ h ▸ rfl⟩
    have h0 := liuWangAffineD4Walk_injective (congrFun h 0)
    simpa using h0
  simp only [liuWangAffineD4Coefficients, Finsupp.finsetSum_apply, Finsupp.single_apply]
  split_ifs with h
  · obtain ⟨j, rfl⟩ := h
    simp only [hinj]
    simp
  · refine Finset.sum_eq_zero fun j _ ↦ ite_eq_right fun hj ↦ h ⟨j, hj.symm⟩

variable {k} in
/-- Liu--Wang's coefficients are supported on closed walks, read in product order. -/
theorem fst_eq_snd_of_mem_support_liuWangAffineD4Coefficients (c : k) :
    ∀ w ∈ (liuWangAffineD4Coefficients k c).support, ∀ i, (w i).fst = (w (i + 1)).snd := by
  classical
  intro w hw i
  rw [Finsupp.mem_support_iff, liuWangAffineD4Coefficients_apply] at hw
  split_ifs at hw with h
  · obtain ⟨j, rfl⟩ := h
    exact liuWangAffineD4Walk_sub_fst_eq_snd i j
  · exact absurd rfl hw

/-- **Liu--Wang's `A∞` algebra on the affine `D₄` zigzag algebra**, with scalar `c`: the
path-length graded zigzag algebra with `m₂` the product and `m₄` equal to `c` times the sum of the
loop operations of the four cyclic rotations of the walk `β₄ α₁ β₁ α₄`. -/
noncomputable def liuWangAffineD4AInfinityAlgebra (c : k) :
    AInfinityAlgebra k (nonisolatedZigzagQuotient k (AffineDynkinType.D 4).graph) :=
  zigzagLoopAInfinityAlgebra (AffineDynkinType.exists_adj_graph (t := .D 4) (by decide))
    (liuWangAffineD4Coefficients k c) (fst_eq_snd_of_mem_support_liuWangAffineD4Coefficients c)

variable {k}

/-- The binary operation of Liu--Wang's algebra is the product of the zigzag algebra. -/
@[simp]
theorem liuWangAffineD4AInfinityAlgebra_m_two_apply (c : k)
    (x : Fin 2 → nonisolatedZigzagQuotient k (AffineDynkinType.D 4).graph) :
    (liuWangAffineD4AInfinityAlgebra k c).m 2 x = x 0 * x 1 :=
  zigzagLoopAInfinityAlgebra_m_two_apply _ _ x

/-- **Liu--Wang's algebra has no higher operations other than `m₄`.** -/
theorem liuWangAffineD4AInfinityAlgebra_m_eq_zero (c : k) {n : ℕ} (h₂ : n ≠ 2) (h₄ : n ≠ 4) :
    (liuWangAffineD4AInfinityAlgebra k c).m n = 0 :=
  zigzagLoopAInfinityAlgebra_m_eq_zero _ _ h₂ h₄

/-- On a cyclic rotation of Liu--Wang's walk, `m₄` is `c` times the volume class at the base of the
rotated walk. -/
theorem liuWangAffineD4AInfinityAlgebra_m_four_rotate (c : k) (j : Fin 4) :
    (liuWangAffineD4AInfinityAlgebra k c).m 4 (fun i ↦ liuWangAffineD4Arrow k (i - j)) =
      c • zigzagVolume k _ (liuWangAffineD4Walk (-j)).snd := by
  classical
  have h := zigzagLoopAInfinityAlgebra_m_four_ofArrow
    (hns := AffineDynkinType.exists_adj_graph (t := .D 4) (by decide))
    (liuWangAffineD4Coefficients k c)
    (fst_eq_snd_of_mem_support_liuWangAffineD4Coefficients c) fun i ↦ liuWangAffineD4Walk (i - j)
  rw [liuWangAffineD4Coefficients_apply, ite_eq_left ⟨j, rfl⟩, zero_sub] at h
  exact h

/-- **The four values of Liu--Wang's `m₄`**, in the order of Example 4.7:
`m₄(β₄, α₁, β₁, α₄) = c β₄ α₄`, `m₄(α₄, β₄, α₁, β₁) = c α₁ β₁`, `m₄(β₁, α₄, β₄, α₁) = c β₁ α₁` and
`m₄(α₁, β₁, α₄, β₄) = c α₄ β₄`, where `β₄, α₁, β₁, α₄` are the arrows
`TauCeti.liuWangAffineD4Arrow 0, 1, 2, 3`. -/
theorem liuWangAffineD4AInfinityAlgebra_m_four_values (c : k) :
    (liuWangAffineD4AInfinityAlgebra k c).m 4
        ![liuWangAffineD4Arrow k 0, liuWangAffineD4Arrow k 1, liuWangAffineD4Arrow k 2,
          liuWangAffineD4Arrow k 3] = c • (liuWangAffineD4Arrow k 0 * liuWangAffineD4Arrow k 3) ∧
      (liuWangAffineD4AInfinityAlgebra k c).m 4
        ![liuWangAffineD4Arrow k 3, liuWangAffineD4Arrow k 0, liuWangAffineD4Arrow k 1,
          liuWangAffineD4Arrow k 2] = c • (liuWangAffineD4Arrow k 1 * liuWangAffineD4Arrow k 2) ∧
      (liuWangAffineD4AInfinityAlgebra k c).m 4
        ![liuWangAffineD4Arrow k 2, liuWangAffineD4Arrow k 3, liuWangAffineD4Arrow k 0,
          liuWangAffineD4Arrow k 1] = c • (liuWangAffineD4Arrow k 2 * liuWangAffineD4Arrow k 1) ∧
      (liuWangAffineD4AInfinityAlgebra k c).m 4
        ![liuWangAffineD4Arrow k 1, liuWangAffineD4Arrow k 2, liuWangAffineD4Arrow k 3,
          liuWangAffineD4Arrow k 0] =
        c • (liuWangAffineD4Arrow k 3 * liuWangAffineD4Arrow k 0) := by
  -- each value is the volume class at the base of the rotated walk, which is the product of a
  -- dart of the walk with its reverse
  have hmul (d e : (AffineDynkinType.D 4).graph.Dart) (h : e = d.symm) :
      zigzagMk k _ (ofArrow (arrow _ d.adj)) * zigzagMk k _ (ofArrow (arrow _ e.adj)) =
        zigzagVolume k _ d.snd := by
    subst h
    exact zigzagMk_ofArrow_mul_ofArrow_symm k _ d
  have hsymm (i i' : Fin 4) (h : liuWangAffineD4Walk i' = (liuWangAffineD4Walk i).symm) :
      liuWangAffineD4Arrow k i * liuWangAffineD4Arrow k i' =
        zigzagVolume k _ (liuWangAffineD4Walk i).snd :=
    hmul _ _ h
  have hrot (j : Fin 4) (y : Fin 4 → nonisolatedZigzagQuotient k (AffineDynkinType.D 4).graph)
      (hy : y = fun i ↦ liuWangAffineD4Arrow k (i - j)) :
      (liuWangAffineD4AInfinityAlgebra k c).m 4 y =
        c • zigzagVolume k _ (liuWangAffineD4Walk (-j)).snd := by
    rw [hy]
    exact liuWangAffineD4AInfinityAlgebra_m_four_rotate c j
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hrot 0 _ (by ext i; fin_cases i <;> rfl), hsymm 0 3 (by decide)]
    rfl
  · rw [hrot 1 _ (by ext i; fin_cases i <;> rfl), hsymm 1 2 (by decide)]
    rfl
  · rw [hrot 2 _ (by ext i; fin_cases i <;> rfl), hsymm 2 1 (by decide)]
    rfl
  · rw [hrot 3 _ (by ext i; fin_cases i <;> rfl), hsymm 3 0 (by decide)]
    rfl

/-- **`m₄` vanishes on every other arrow quadruple**: on the arrows of four darts that do not form
a cyclic rotation of Liu--Wang's walk, the quartic operation is zero. -/
theorem liuWangAffineD4AInfinityAlgebra_m_four_eq_zero (c : k)
    (d : Fin 4 → (AffineDynkinType.D 4).graph.Dart)
    (hd : ∀ j, d ≠ fun i ↦ liuWangAffineD4Walk (i - j)) :
    (liuWangAffineD4AInfinityAlgebra k c).m 4
        (fun i ↦ zigzagMk k _ (ofArrow (arrow _ (d i).adj))) = 0 := by
  classical
  rw [liuWangAffineD4AInfinityAlgebra, zigzagLoopAInfinityAlgebra_m_four_ofArrow,
    liuWangAffineD4Coefficients_apply, ite_eq_right fun ⟨j, hj⟩ ↦ hd j hj, zero_smul]

/-- Liu--Wang's algebra is minimal. -/
theorem isMinimal_liuWangAffineD4AInfinityAlgebra (c : k) :
    (liuWangAffineD4AInfinityAlgebra k c).IsMinimal :=
  isMinimal_zigzagLoopAInfinityAlgebra _ _

/-- Liu--Wang's algebra is strictly unital, with the unit of the zigzag algebra as strict unit. -/
theorem strictUnit_one_liuWangAffineD4AInfinityAlgebra (c : k) :
    (liuWangAffineD4AInfinityAlgebra k c).StrictUnit 1 :=
  strictUnit_one_zigzagLoopAInfinityAlgebra _ _

/-- **The bidegree of Liu--Wang's operations**: for the Adams grading, the negative of path length,
`m n` is homogeneous of degree `n - 2`. With its cohomological degree `2 - n`, `m₄` has bidegree
`(-2, 2)` when each arrow has bidegree `(1, -1)`. -/
theorem isHomogeneous_liuWangAffineD4AInfinityAlgebra_m_adams (c : k) (n : ℕ) :
    MultilinearMap.IsHomogeneous ((liuWangAffineD4AInfinityAlgebra k c).m n)
      (fun _ q ↦ zigzagIntegerGrade k (AffineDynkinType.D 4).graph (-q))
      (fun q ↦ zigzagIntegerGrade k (AffineDynkinType.D 4).graph (-q)) ((n : ℤ) - 2) :=
  isHomogeneous_zigzagLoopAInfinityAlgebra_m_adams _ _ n

end TauCeti
