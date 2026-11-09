/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Symplectic.Diagonal.Basic
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Symplectic.TorusGeneration

/-!
# Perfectness of the standard symplectic group

The standard symplectic group `Sp₂ₘ` over a field is perfect except in three small cases:
`Sp₂(𝔽₂) ≅ S₃`, `Sp₂(𝔽₃) = SL₂(𝔽₃)` and `Sp₄(𝔽₂) ≅ S₆`. In each case below, every root element
`x_α(c)` is shown to lie in the commutator subgroup; the root subgroups generate the symplectic
group over a field, so the commutator subgroup is everything.

* Over a field containing a nonzero element whose square is not one, in every rank. Conjugation by
  a diagonal torus element scales each root subgroup through its root character, so the
  commutator of the torus element with `x_α(c)` is `x_α((α(t) - 1) c)`, and every root character
  is nontrivial on a suitable coordinate torus element. This covers every infinite field and
  every finite field with at least four elements.
* In rank at least three, over every field. Here the torus may be too small (over `𝔽₂` it is
  trivial), and the Chevalley commutator relations take its place. For pairwise distinct indices
  the structure-constant-one relation gives `x_{eᵢ-eⱼ}(c) = ⁅x_{eᵢ-eₖ}(c), x_{eₖ-eⱼ}(1)⁆`, and
  the long-root strings of the rank-two subsystems give
  ```text
  ⁅x_{eᵢ+eⱼ}(1), x_{-2eⱼ}(-c)⁆ = x_{eᵢ-eⱼ}(-c) x_{2eᵢ}(c),
  ⁅x_{-eᵢ-eⱼ}(1), x_{2eⱼ}(-c)⁆ = x_{eⱼ-eᵢ}(c) x_{-2eᵢ}(c),
  ```
  so the long-root elements are commutators as soon as the difference-root elements are. The
  difference roots and the long roots generate every root subgroup.
* In rank at least two, over a field of characteristic other than two. The structure-constant-two
  relation `⁅x_{eᵢ-eⱼ}(1), x_{eᵢ+eⱼ}(c / 2)⁆ = x_{2eᵢ}(c)` makes the positive long-root elements
  commutators, and the first long-root string above then makes the difference-root elements
  commutators. This covers `Sp₄(𝔽₃)`, which the torus argument misses.

Together these give the classical statement for rank at least two: `Sp₂ₘ(K)` is perfect unless
`m = 2` and `K = 𝔽₂`. In particular every finite symplectic group `Sp₂ᵣ(𝔽_q)` with `r ≥ 3` is
perfect, including those over `𝔽₂` and `𝔽₃`.

## Main results

* `TauCeti.GLSymplecticFin.commutatorElement_diagonal_rootSubgroup`: the commutator of a torus
  element with a root element, over every commutative ring.
* `TauCeti.GLSymplecticFin.RootSubgroupIndex.exists_character_ne_one`: every root character is
  nontrivial on some torus element once there is a unit whose square is not one.
* `TauCeti.GLSymplecticFin.rootSubgroup_mem_commutator`: every root element is in the commutator
  subgroup.
* `TauCeti.GLSymplecticFin.commutator_eq_top`: the standard symplectic group is perfect.
* `TauCeti.GLSymplecticFin.rootSubgroup_mem_commutator_of_difference`: in rank at least two,
  over every commutative ring, the commutator subgroup contains every root element once it
  contains the difference-root elements.
* `TauCeti.GLSymplecticFin.rootSubgroup_mem_commutator_of_three_le` and
  `TauCeti.GLSymplecticFin.rootSubgroup_mem_commutator_of_isUnit_two`: every root element is in
  the commutator subgroup in rank at least three, and in rank at least two when `2` is a unit.
* `TauCeti.GLSymplecticFin.commutator_eq_top_of_three_le`,
  `TauCeti.GLSymplecticFin.commutator_eq_top_of_two_ne_zero` and
  `TauCeti.GLSymplecticFin.commutator_eq_top_of_two_le`: the corresponding perfectness theorems,
  the last one in the classical form.

## References

* R. Steinberg, *Lectures on Chevalley Groups* (1968), §4.
* R. W. Carter, *Simple Groups of Lie Type* (1972), §11.1.
* J. S. Milne, *Algebraic Groups* (2017), §6d.

The torus argument follows the special-linear perfectness proof
`Matrix.SpecialLinearGroup.commutator_eq_top`, with the torus conjugation formula
`TauCeti.GLSymplecticFin.diagonal_mul_rootSubgroup_mul_inv` in place of diagonal conjugation of
transvections and `TauCeti.GLSymplecticFin.eq_top_of_root_subgroups` for generation. The
commutator-relation arguments use the relations of
`TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Symplectic.ChevalleyRelations` and the root
generation `TauCeti.GLSymplecticFin.RootSubgroupIndex.hom_apply_mem_of_difference_of_long`.
-/
public section

open scoped commutatorElement

namespace TauCeti.GLSymplecticFin

universe u

variable {m : ℕ}

/-- The commutator of a diagonal torus element with a root element is the root element whose
parameter is scaled by the root character minus one. -/
theorem commutatorElement_diagonal_rootSubgroup {R : Type u} [CommRing R]
    (root : RootSubgroupIndex m) (t : Fin m → Rˣ) (c : Multiplicative R) :
    ⁅diagonal t, root.hom c⁆ =
      root.hom (Multiplicative.ofAdd (((root.character t : R) - 1) * c.toAdd)) := by
  rw [commutatorElement_def, diagonal_mul_rootSubgroup_mul_inv, ← map_inv, ← map_mul]
  congr 1
  apply Multiplicative.toAdd.injective
  simp only [toAdd_mul, toAdd_ofAdd, toAdd_inv]
  ring

namespace RootSubgroupIndex

/-- **Root characters are nontrivial.** If the coefficient monoid has a unit whose square is not
one, then every root character takes a value different from one on the diagonal torus. -/
theorem exists_character_ne_one {R : Type u} [CommMonoid R] (root : RootSubgroupIndex m)
    {u : Rˣ} (hu : u * u ≠ 1) : ∃ t : Fin m → Rˣ, root.character t ≠ 1 := by
  classical
  have hu₁ : u ≠ 1 := by
    rintro rfl
    exact hu (mul_one 1)
  cases root with
  | positiveLong i => exact ⟨Pi.mulSingle i u, by simpa using hu⟩
  | negativeLong i =>
    exact ⟨Pi.mulSingle i u, by
      rw [character_negativeLong, Pi.mulSingle_eq_same]
      exact inv_ne_one.mpr hu⟩
  | difference i j hij =>
    exact ⟨Pi.mulSingle i u, by simpa [Pi.mulSingle_apply, hij.symm] using hu₁⟩
  | positiveSum i j hij =>
    exact ⟨Pi.mulSingle i u, by simpa [Pi.mulSingle_apply, hij.ne'] using hu₁⟩
  | negativeSum i j hij =>
    exact ⟨Pi.mulSingle i u, by simpa [Pi.mulSingle_apply, hij.ne'] using hu₁⟩

end RootSubgroupIndex

variable {K : Type u} [Field K]

/-- Every root element of the standard symplectic group is in the commutator subgroup if the
field contains a nonzero element whose square is not one. -/
theorem rootSubgroup_mem_commutator {a : K} (ha : a ≠ 0) (hasq : a ^ 2 ≠ 1)
    (root : RootSubgroupIndex m) (c : Multiplicative K) :
    root.hom c ∈ commutator (GLSymplecticFin m K) := by
  obtain ⟨t, ht⟩ := root.exists_character_ne_one (u := Units.mk0 a ha) (by
    rw [Ne, Units.ext_iff]
    simpa [pow_two] using hasq)
  have hχ : (root.character t : K) - 1 ≠ 0 :=
    sub_ne_zero.mpr (by simpa only [Ne, Units.val_eq_one] using ht)
  have hc : root.hom c =
      ⁅diagonal t, root.hom (Multiplicative.ofAdd (c.toAdd / ((root.character t : K) - 1)))⁆ := by
    rw [commutatorElement_diagonal_rootSubgroup, toAdd_ofAdd, mul_div_cancel₀ _ hχ, ofAdd_toAdd]
  rw [hc]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)

/-- **The standard symplectic group is perfect** over a field with a nonzero element whose square
is not one, in every rank, including rank zero. -/
theorem commutator_eq_top {a : K} (ha : a ≠ 0) (hasq : a ^ 2 ≠ 1) :
    commutator (GLSymplecticFin m K) = ⊤ :=
  eq_top_of_root_subgroups _ (rootSubgroup_mem_commutator ha hasq)

section CommRing

variable {R : Type u} [CommRing R]

/-- **Difference-root elements are commutators** when a third index is available: for pairwise
distinct `i`, `j`, `k`, the structure-constant-one Chevalley relation gives
`x_{eᵢ-eⱼ}(c) = ⁅x_{eᵢ-eₖ}(c), x_{eₖ-eⱼ}(1)⁆`. -/
theorem differenceShortRootUnit_mem_commutator {i j k : Fin m} (hij : i ≠ j) (hik : i ≠ k)
    (hkj : k ≠ j) (c : R) :
    differenceShortRootUnit hij c ∈ commutator (GLSymplecticFin m R) := by
  have h := commutatorElement_differenceShortRootUnit_differenceShortRootUnit hik hkj hij c 1
  rw [mul_one] at h
  rw [← h]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)

/-- A positive long-root element is a commutator once the matching difference-root element is:
`⁅x_{eᵢ+eⱼ}(1), x_{-2eⱼ}(-c)⁆ = x_{eᵢ-eⱼ}(-c) x_{2eᵢ}(c)`. -/
private theorem positiveLongRootTransvectionUnit_mem_commutator {i j : Fin m} (hij : i ≠ j)
    (c : R) (hdiff : differenceShortRootUnit hij (-c) ∈ commutator (GLSymplecticFin m R)) :
    positiveLongRootTransvectionUnit i c ∈ commutator (GLSymplecticFin m R) := by
  have h := commutatorElement_positiveSumShortRootUnit_negativeLongRootTransvectionUnit hij 1 (-c)
  rw [one_mul, one_pow, one_mul, neg_neg] at h
  rw [← Subgroup.mul_mem_cancel_left _ hdiff, ← h]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)

/-- A negative long-root element is a commutator once the matching difference-root element is:
`⁅x_{-eᵢ-eⱼ}(1), x_{2eⱼ}(-c)⁆ = x_{eⱼ-eᵢ}(c) x_{-2eᵢ}(c)`. -/
private theorem negativeLongRootTransvectionUnit_mem_commutator {i j : Fin m} (hij : i ≠ j)
    (c : R) (hdiff : differenceShortRootUnit hij.symm c ∈ commutator (GLSymplecticFin m R)) :
    negativeLongRootTransvectionUnit i c ∈ commutator (GLSymplecticFin m R) := by
  have h := commutatorElement_negativeSumShortRootUnit_positiveLongRootTransvectionUnit hij 1 (-c)
  rw [one_mul, one_pow, one_mul, neg_neg] at h
  rw [← Subgroup.mul_mem_cancel_left _ hdiff, ← h]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)

/-- **In rank at least two, the difference roots control the commutator subgroup.** If the
commutator subgroup of the standard symplectic group contains every difference-root element, then
it contains every root element: the long-root strings make the long-root elements commutators, and
the difference and long roots generate every root subgroup. -/
theorem rootSubgroup_mem_commutator_of_difference (hm : 2 ≤ m)
    (hdiff : ∀ {i j : Fin m} (hij : i ≠ j) (c : R),
      differenceShortRootUnit hij c ∈ commutator (GLSymplecticFin m R))
    (root : RootSubgroupIndex m) (c : Multiplicative R) :
    root.hom c ∈ commutator (GLSymplecticFin m R) := by
  have h01 : (⟨0, by omega⟩ : Fin m) ≠ ⟨1, by omega⟩ := by simp [Fin.ext_iff]
  exact RootSubgroupIndex.hom_apply_mem_of_difference_of_long _ _ hdiff
    (fun a => positiveLongRootTransvectionUnit_mem_commutator h01 a (hdiff h01 _))
    (fun a => negativeLongRootTransvectionUnit_mem_commutator h01 a (hdiff h01.symm _)) root c

/-- **In rank at least three, every root element of the standard symplectic group is in the
commutator subgroup**, over every commutative ring. -/
theorem rootSubgroup_mem_commutator_of_three_le (hm : 3 ≤ m) (root : RootSubgroupIndex m)
    (c : Multiplicative R) : root.hom c ∈ commutator (GLSymplecticFin m R) := by
  refine rootSubgroup_mem_commutator_of_difference (by omega) (fun {i j} hij a => ?_) root c
  obtain ⟨k, hki, hkj⟩ := Fin.exists_ne_and_ne_of_two_lt i j hm
  exact differenceShortRootUnit_mem_commutator hij hki.symm hkj a

/-- **In rank at least two, if `2` is a unit, every root element of the standard symplectic group
is in the commutator subgroup**, over every commutative ring. -/
theorem rootSubgroup_mem_commutator_of_isUnit_two (hm : 2 ≤ m) (h2 : IsUnit (2 : R))
    (root : RootSubgroupIndex m) (c : Multiplicative R) :
    root.hom c ∈ commutator (GLSymplecticFin m R) := by
  refine rootSubgroup_mem_commutator_of_difference hm (fun {i j} hij a => ?_) root c
  -- The structure-constant-two relation `⁅x_{eᵢ-eⱼ}(1), x_{eᵢ+eⱼ}(b / 2)⁆ = x_{2eᵢ}(b)` makes the
  -- positive long-root elements commutators; then
  -- `⁅x_{eᵢ+eⱼ}(1), x_{-2eⱼ}(a)⁆ = x_{eᵢ-eⱼ}(a) x_{2eᵢ}(-a)` does the same for `x_{eᵢ-eⱼ}(a)`.
  have hlong (b : R) : positiveLongRootTransvectionUnit i b ∈ commutator (GLSymplecticFin m R) := by
    obtain ⟨u, hu⟩ := h2
    have h := commutatorElement_differenceShortRootUnit_positiveSumShortRootUnit hij 1 (↑u⁻¹ * b)
    rw [mul_one, ← mul_assoc, ← hu, Units.mul_inv, one_mul] at h
    rw [← h]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
  have h := commutatorElement_positiveSumShortRootUnit_negativeLongRootTransvectionUnit hij 1 a
  rw [one_mul, one_pow, one_mul] at h
  rw [← Subgroup.mul_mem_cancel_right _ (hlong (-a)), ← h]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)

end CommRing

/-- **The standard symplectic group is perfect in rank at least three**, over every field,
including `𝔽₂` and `𝔽₃`. -/
theorem commutator_eq_top_of_three_le (hm : 3 ≤ m) : commutator (GLSymplecticFin m K) = ⊤ :=
  eq_top_of_root_subgroups _ (rootSubgroup_mem_commutator_of_three_le hm)

/-- **The standard symplectic group is perfect in rank at least two** over a field of
characteristic other than two, including `𝔽₃`. -/
theorem commutator_eq_top_of_two_ne_zero (hm : 2 ≤ m) (h2 : (2 : K) ≠ 0) :
    commutator (GLSymplecticFin m K) = ⊤ :=
  eq_top_of_root_subgroups _ (rootSubgroup_mem_commutator_of_isUnit_two hm h2.isUnit)

/-- **The standard symplectic group `Sp₂ₘ(K)` with `m ≥ 2` is perfect unless `m = 2` and
`K = 𝔽₂`.** The second hypothesis says that the rank is at least three or the field has an
element other than `0` and `1`. The exception is genuine: `Sp₄(𝔽₂) ≅ S₆` is not perfect. -/
theorem commutator_eq_top_of_two_le (hm : 2 ≤ m) (hK : 3 ≤ m ∨ ∃ a : K, a ≠ 0 ∧ a ≠ 1) :
    commutator (GLSymplecticFin m K) = ⊤ := by
  obtain hm3 | ⟨a, ha0, ha1⟩ := hK
  · exact commutator_eq_top_of_three_le hm3
  by_cases h2 : (2 : K) = 0
  · -- In characteristic two, `a ^ 2 = 1` forces `(a - 1) ^ 2 = 0`, so `a = 1`.
    refine commutator_eq_top ha0 fun hsq => ha1 ?_
    have h : (a - 1) ^ 2 = 0 := by linear_combination hsq + (1 - a) * h2
    exact sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h)
  · exact commutator_eq_top_of_two_ne_zero hm h2

end TauCeti.GLSymplecticFin
