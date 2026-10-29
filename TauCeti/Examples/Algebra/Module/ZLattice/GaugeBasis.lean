/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.GroupTheory.Index
public import TauCeti.Algebra.Module.ZLattice.GaugeBasis

/-!
# Successive minima need not be attained by a basis

Let `L = ℤ⁵ + ℤ · (½, …, ½)` in `EuclideanSpace ℝ (Fin 5)`, measured by the Euclidean unit ball.
Every nonzero vector of `L` has norm at least `1`: a point of `L` has all coordinates in `ℤ` or all
coordinates in `½ + ℤ`, and in the second case its squared norm is at least `5 / 4`. The standard
basis vectors `e 0, …, e 4` lie in `L` and have norm `1`, so all five successive minima of `L` are
`1`, attained by the `e i`. But the `e i` span `ℤ⁵`, which has index two in `L`, so no basis of `L`
consists of them.

Cassels' basis lemma `ZLattice.exists_basis_gauge_le_max_one_mul`, applied to the `e i`, still
produces a basis `b` of `L` with `‖b i‖ ≤ max 1 ((i + 1) / 2)`. An explicit such basis is
`e 0, e 1, e 2, e 3, (½, …, ½)`, whose last vector has norm `√5 / 2 ≤ 5 / 2`.

## Main results

* `TauCeti.GaugeBasisExample.one_le_norm_of_mem_lattice`: nonzero vectors of `L` have norm `≥ 1`.
* `TauCeti.GaugeBasisExample.relIndex_stdLattice_lattice`: `ℤ⁵` has index two in `L`.
* `TauCeti.GaugeBasisExample.not_exists_basis_eq_single`: the `e i` are not a basis of `L`.
* `TauCeti.GaugeBasisExample.exists_basis_norm_le`: the basis given by Cassels' lemma.
* `TauCeti.GaugeBasisExample.norm_basis_le`: the explicit basis meets the same bounds.

## References

* J. W. S. Cassels, *An Introduction to the Geometry of Numbers*, Springer, 1959, Chapter V,
  Lemma 8.
-/

public section

open Module Submodule Set Metric

namespace TauCeti.GaugeBasisExample

/-- The point `(½, …, ½)` of `EuclideanSpace ℝ (Fin 5)`. -/
noncomputable def half : EuclideanSpace ℝ (Fin 5) := WithLp.toLp 2 fun _ ↦ 1 / 2

/-- The generators `e 0, e 1, e 2, e 3, (½, …, ½)` of `L`. -/
noncomputable def gen (k : Fin 5) : EuclideanSpace ℝ (Fin 5) :=
  if k = 4 then half else EuclideanSpace.single k 1

theorem gen_four : gen 4 = half := by
  simp [gen]

@[simp]
theorem gen_apply (k j : Fin 5) :
    gen k j = if k = 4 then 1 / 2 else if j = k then 1 else 0 := by
  unfold gen half
  split_ifs <;> simp_all [PiLp.single_apply]

theorem single_four_eq : EuclideanSpace.single (4 : Fin 5) (1 : ℝ) =
    gen 4 + gen 4 - gen 0 - gen 1 - gen 2 - gen 3 := by
  ext j
  fin_cases j <;> simp [gen_apply] <;> norm_num

/-- The standard lattice `ℤ⁵`, spanned by `e 0, …, e 4`. -/
noncomputable def stdLattice : Submodule ℤ (EuclideanSpace ℝ (Fin 5)) :=
  span ℤ (range fun i ↦ EuclideanSpace.single i 1)

/-- The lattice `L = ℤ⁵ + ℤ · (½, …, ½)`. -/
noncomputable def lattice : Submodule ℤ (EuclideanSpace ℝ (Fin 5)) :=
  span ℤ (range gen)

theorem mem_stdLattice_iff {x : EuclideanSpace ℝ (Fin 5)} :
    x ∈ stdLattice ↔ ∀ j, ∃ z : ℤ, (z : ℝ) = x j := by
  have h := (EuclideanSpace.basisFun (Fin 5) ℝ).toBasis.mem_span_iff_repr_mem ℤ x
  have hb : ⇑(EuclideanSpace.basisFun (Fin 5) ℝ) = fun i ↦ EuclideanSpace.single i 1 :=
    funext fun i ↦ EuclideanSpace.basisFun_apply ..
  simpa [stdLattice, hb] using h

theorem single_mem_lattice (i : Fin 5) : EuclideanSpace.single i (1 : ℝ) ∈ lattice := by
  have hgen (k : Fin 5) : gen k ∈ lattice := subset_span (mem_range_self k)
  by_cases hi : i = 4
  · subst hi
    rw [single_four_eq]
    exact sub_mem (sub_mem (sub_mem (sub_mem (add_mem (hgen 4) (hgen 4)) (hgen 0)) (hgen 1))
      (hgen 2)) (hgen 3)
  · simpa [gen, hi] using hgen i

theorem half_mem_lattice : half ∈ lattice := by
  rw [← gen_four]
  exact subset_span (mem_range_self 4)

theorem stdLattice_le_lattice : stdLattice ≤ lattice :=
  span_le.2 <| range_subset_iff.2 single_mem_lattice

theorem linearIndependent_gen : LinearIndependent ℝ gen := by
  refine linearIndependent_of_top_le_span_of_card_eq_finrank ?_ (by simp)
  rw [← (EuclideanSpace.basisFun (Fin 5) ℝ).toBasis.span_eq]
  refine span_le.2 <| range_subset_iff.2 fun i ↦ ?_
  simpa using span_le_restrictScalars ℤ ℝ (range gen) (single_mem_lattice i)

/-- `L` is discrete, since it is spanned by the real basis `gen`. -/
instance : DiscreteTopology lattice := by
  have h : DiscreteTopology (span ℤ (range
      (basisOfLinearIndependentOfCardEqFinrank linearIndependent_gen (by simp)))) :=
    inferInstance
  rwa [coe_basisOfLinearIndependentOfCardEqFinrank] at h

/-- Every point of `L` has its last coordinate in `½ℤ`, and all its coordinates differ from the
last one by integers. -/
theorem exists_intCast_of_mem_lattice {x : EuclideanSpace ℝ (Fin 5)} (hx : x ∈ lattice) :
    (∃ m : ℤ, (m : ℝ) = 2 * x 4) ∧ ∀ j, ∃ z : ℤ, (z : ℝ) = x j - x 4 := by
  induction hx using span_induction with
  | mem y hy =>
    obtain ⟨k, rfl⟩ := hy
    refine ⟨⟨if k = 4 then 1 else 0, ?_⟩, fun j ↦ ⟨if k = 4 then 0 else if j = k then 1 else 0, ?_⟩⟩
    · fin_cases k <;> simp [gen_apply]
    · fin_cases k <;> fin_cases j <;> simp [gen_apply]
  | zero => exact ⟨⟨0, by simp⟩, fun _ ↦ ⟨0, by simp⟩⟩
  | add x y _ _ hx hy =>
    obtain ⟨⟨m, hm⟩, hxz⟩ := hx
    obtain ⟨⟨n, hn⟩, hyz⟩ := hy
    refine ⟨⟨m + n, by simp [hm, hn]; ring⟩, fun j ↦ ?_⟩
    obtain ⟨a, ha⟩ := hxz j
    obtain ⟨b, hb⟩ := hyz j
    exact ⟨a + b, by simp [ha, hb]; ring⟩
  | smul c x _ hx =>
    obtain ⟨⟨m, hm⟩, hxz⟩ := hx
    refine ⟨⟨c * m, by simp [hm]; ring⟩, fun j ↦ ?_⟩
    obtain ⟨a, ha⟩ := hxz j
    exact ⟨c * a, by simp [ha]; ring⟩

/-- A point lies in `L` exactly when its last coordinate is in `½ℤ` and all its coordinates differ
from the last one by integers. -/
theorem mem_lattice_iff {x : EuclideanSpace ℝ (Fin 5)} :
    x ∈ lattice ↔ (∃ m : ℤ, (m : ℝ) = 2 * x 4) ∧ ∀ j, ∃ z : ℤ, (z : ℝ) = x j - x 4 := by
  refine ⟨exists_intCast_of_mem_lattice, fun ⟨⟨m, hm⟩, hz⟩ ↦ ?_⟩
  have hstd : x - m • half ∈ stdLattice := mem_stdLattice_iff.2 fun j ↦ by
    obtain ⟨z, hz⟩ := hz j
    exact ⟨z, by simp [half, hz, hm]; ring⟩
  simpa using add_mem (stdLattice_le_lattice hstd) (zsmul_mem half_mem_lattice m)

/-- **The first minimum of `L` is `1`.** Every nonzero vector of `L` has norm at least `1`. -/
theorem one_le_norm_of_mem_lattice {x : EuclideanSpace ℝ (Fin 5)} (hx : x ∈ lattice)
    (h0 : x ≠ 0) : 1 ≤ ‖x‖ := by
  obtain ⟨⟨m, hm⟩, hz⟩ := exists_intCast_of_mem_lattice hx
  choose z hz using hz
  rw [← one_le_sq_iff₀ (norm_nonneg _), EuclideanSpace.real_norm_sq_eq]
  rcases Int.even_or_odd' m with ⟨k, rfl | rfl⟩
  · -- All coordinates are integers, and one of them is nonzero.
    have hx4 : x 4 = k := by push_cast at hm; linarith
    obtain ⟨j, hj⟩ : ∃ j, x j ≠ 0 := by
      by_contra! h
      exact h0 (by ext j; simp [h j])
    have hxj : x j = ((z j + k : ℤ) : ℝ) := by push_cast; linarith [hz j]
    have hne : z j + k ≠ 0 := fun h ↦ hj (by rw [hxj, h, Int.cast_zero])
    have h1 : (1 : ℝ) ≤ x j ^ 2 := by
      rw [hxj, ← Int.cast_pow, ← Int.cast_one, Int.cast_le]
      exact (one_le_sq_iff_one_le_abs _).2 (Int.one_le_abs hne)
    exact h1.trans (Finset.single_le_sum (f := fun i ↦ x i ^ 2) (fun i _ ↦ sq_nonneg _)
      (Finset.mem_univ j))
  · -- All coordinates lie in `½ + ℤ`, so each square is at least `¼`.
    have hq (j : Fin 5) : (1 / 4 : ℝ) ≤ x j ^ 2 := by
      have hxj : x j = ((z j + k : ℤ) : ℝ) + 1 / 2 := by
        push_cast at hm ⊢; linarith [hz j]
      have hn : (0 : ℝ) ≤ ((z j + k : ℤ) : ℝ) * ((z j + k + 1 : ℤ) : ℝ) := by
        have : (0 : ℤ) ≤ (z j + k) * (z j + k + 1) := by
          rcases le_or_gt 0 (z j + k) with h | h
          · positivity
          · exact Int.mul_nonneg_of_nonpos_of_nonpos h.le (by omega)
        exact_mod_cast this
      rw [hxj]
      push_cast at hn ⊢
      nlinarith
    simp only [Fin.sum_univ_five]
    linarith [hq 0, hq 1, hq 2, hq 3, hq 4]

/-- **All five minima of `L` are `1`.** The standard basis vectors are linearly independent
vectors of `L` of norm `1`, and no nonzero vector of `L` is shorter. -/
example : LinearIndependent ℝ (fun i : Fin 5 ↦ EuclideanSpace.single i (1 : ℝ)) ∧
    (∀ i, EuclideanSpace.single i (1 : ℝ) ∈ lattice ∧ ‖EuclideanSpace.single i (1 : ℝ)‖ = 1) ∧
    ∀ x ∈ lattice, x ≠ 0 → 1 ≤ ‖x‖ :=
  ⟨by simpa [funext fun i ↦ EuclideanSpace.basisFun_apply (Fin 5) ℝ i] using
      (EuclideanSpace.basisFun (Fin 5) ℝ).toBasis.linearIndependent,
    fun i ↦ ⟨single_mem_lattice i, by simp⟩, fun _ hx h0 ↦ one_le_norm_of_mem_lattice hx h0⟩

/-- A point of `L` lies in `ℤ⁵` exactly when its last coordinate is an integer. -/
theorem mem_stdLattice_iff_of_mem_lattice {x : EuclideanSpace ℝ (Fin 5)} (hx : x ∈ lattice) :
    x ∈ stdLattice ↔ ∃ z : ℤ, (z : ℝ) = x 4 := by
  refine ⟨fun h ↦ mem_stdLattice_iff.1 h 4, fun ⟨z, hz⟩ ↦ mem_stdLattice_iff.2 fun j ↦ ?_⟩
  obtain ⟨a, ha⟩ := (exists_intCast_of_mem_lattice hx).2 j
  exact ⟨a + z, by push_cast; linarith⟩

/-- **The minima witnesses span a sublattice of index two.** `ℤ⁵` has index two in `L`, with
`(½, …, ½)` representing the nontrivial coset. -/
theorem relIndex_stdLattice_lattice :
    stdLattice.toAddSubgroup.relIndex lattice.toAddSubgroup = 2 := by
  refine AddSubgroup.relIndex_eq_two_iff.2 ⟨half, half_mem_lattice, fun b hb ↦ ?_⟩
  have hb' : b + half ∈ lattice := add_mem hb half_mem_lattice
  simp only [mem_toAddSubgroup, mem_stdLattice_iff_of_mem_lattice hb',
    mem_stdLattice_iff_of_mem_lattice hb]
  obtain ⟨m, hm⟩ := (exists_intCast_of_mem_lattice hb).1
  have h4 : (b + half) 4 = b 4 + 1 / 2 := by simp [half]
  rw [h4, xor_iff_iff_not]
  constructor
  · rintro ⟨z, hz⟩ ⟨w, hw⟩
    have : ((2 * z - 2 * w : ℤ) : ℝ) = 1 := by push_cast; linarith
    have : 2 * z - 2 * w = 1 := by exact_mod_cast this
    omega
  · intro h
    rcases Int.even_or_odd' m with ⟨k, rfl | rfl⟩
    · exact absurd ⟨k, by push_cast at hm; linarith⟩ h
    · exact ⟨k + 1, by push_cast at hm ⊢; linarith⟩

/-- **The minima witnesses are not a basis.** No basis of `L` consists of the vectors
`e 0, …, e 4`, although they realize all five successive minima of `L`. -/
theorem not_exists_basis_eq_single :
    ¬ ∃ b : Basis (Fin 5) ℤ lattice, ∀ i, (b i : EuclideanSpace ℝ (Fin 5)) =
      EuclideanSpace.single i 1 := by
  rintro ⟨b, hb⟩
  have h : lattice ≤ stdLattice := by
    intro x hx
    have hx' : x = ∑ i, b.repr ⟨x, hx⟩ i • (b i : EuclideanSpace ℝ (Fin 5)) := by
      have h := congrArg Subtype.val (b.sum_repr ⟨x, hx⟩)
      rw [Submodule.coe_sum] at h
      exact h.symm
    rw [hx']
    exact sum_mem fun i _ ↦ smul_mem _ _ (hb i ▸ subset_span (mem_range_self i))
  have := relIndex_stdLattice_lattice
  rw [AddSubgroup.relIndex_eq_one.2 ((toAddSubgroup_le _ _).2 h)] at this
  omega

/-- **Cassels' basis lemma on `L`.** Applied to the minima witnesses `e 0, …, e 4`, it gives a basis
`b` of `L` with `‖b i‖ ≤ max 1 ((i + 1) / 2)`. -/
theorem exists_basis_norm_le : ∃ b : Basis (Fin 5) ℤ lattice, ∀ i : Fin 5,
    ‖(b i : EuclideanSpace ℝ (Fin 5))‖ ≤ max 1 ((((i : ℕ) : ℝ) + 1) / 2) := by
  have hli : LinearIndependent ℝ fun i : Fin 5 ↦ EuclideanSpace.single i (1 : ℝ) := by
    simpa [funext fun i ↦ EuclideanSpace.basisFun_apply (Fin 5) ℝ i] using
      (EuclideanSpace.basisFun (Fin 5) ℝ).toBasis.linearIndependent
  obtain ⟨b, hb⟩ := ZLattice.exists_basis_gauge_le_max_one_mul lattice (convex_closedBall 0 1)
    (fun x hx ↦ by simpa using hx) ((absorbent_ball_zero zero_lt_one).mono ball_subset_closedBall)
    (by simp) single_mem_lattice hli (fun i j _ ↦ by simp)
  exact ⟨b, fun i ↦ by simpa [gauge_closedBall zero_le_one] using hb i⟩

@[simp]
theorem norm_half : ‖half‖ = √5 / 2 := by
  rw [EuclideanSpace.norm_eq]
  simp [half, div_eq_mul_inv]

/-- The basis `e 0, e 1, e 2, e 3, (½, …, ½)` of `L`. -/
noncomputable def basis : Basis (Fin 5) ℤ lattice :=
  Basis.span (linearIndependent_gen.restrict_scalars' ℤ)

@[simp]
theorem basis_apply (i : Fin 5) : (basis i : EuclideanSpace ℝ (Fin 5)) = gen i :=
  congrArg Subtype.val (Basis.span_apply _ i)

/-- **An explicit basis within Cassels' bounds.** The basis `e 0, e 1, e 2, e 3, (½, …, ½)`
satisfies `‖b i‖ ≤ max 1 ((i + 1) / 2)`; its last vector has norm `√5 / 2 ≤ 5 / 2`. -/
theorem norm_basis_le (i : Fin 5) :
    ‖(basis i : EuclideanSpace ℝ (Fin 5))‖ ≤ max 1 ((((i : ℕ) : ℝ) + 1) / 2) := by
  rw [basis_apply]
  by_cases hi : i = 4
  · subst hi
    have h5 : √5 ≤ 5 := Real.sqrt_le_iff.2 ⟨by norm_num, by norm_num⟩
    have h4 : (((4 : Fin 5) : ℕ) : ℝ) = 4 := by norm_num
    rw [gen_four, norm_half, h4]
    exact le_max_of_le_right (by linarith)
  · simp [gen, hi]

end TauCeti.GaugeBasisExample

end
