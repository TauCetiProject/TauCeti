/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.OrderOfElement
public import TauCeti.Algebra.Module.ZLattice.LiftBaseChange
import Mathlib.Data.Finset.Finsupp
import Mathlib.Data.Set.Finite.Lemmas

/-!
# Finitely many curve classes below an area bound

Let `X` be a closed symplectic manifold with symplectic form `ω` and a compatible almost complex
structure `J`. Write `H = H₂(X; ℤ)` and `ω : H → ℝ` for the symplectic area. Choose closed
two-forms `ζ₁, …, ζₙ` whose de Rham classes span `H²(X; ℝ)` and let `l : H → ℝⁿ` record their
integrals. The real extension of `l` to `ℝ ⊗[ℤ] H = H₂(X; ℝ)` is injective. The class `C` of a
nonconstant `J`-holomorphic curve satisfies two numerical inequalities:

* its area is positive, `ω(C) > 0`, because `ω` restricts to a positive area form on every
  complex tangent line;
* its periods are bounded by its area, `‖l(C)‖ ≤ K ω(C)`, because the integral of `ζᵢ` over the
  curve is at most the comass of `ζᵢ` times its area, and the area of a `J`-holomorphic curve is
  its symplectic area `ω(C)`.

`TauCeti.IsComassBounded l ω K S` records these two inequalities for a set `S ⊆ H` of classes.
This file derives the finiteness statements that the bounded-window compactness of Taubes's curve
count needs, for any finitely generated abelian group `H` with such data:

* only finitely many classes of `S` have area at most `R`, torsion parts included
  (`TauCeti.IsComassBounded.finite_setOf_area_le`);
* the areas of the classes of `S` are bounded below by a positive constant
  (`TauCeti.IsComassBounded.exists_pos_forall_le_area`), even when the periods of `ω` are dense
  in `ℝ`;
* the class-level shadow of a positive cycle `∑ m_C C = A`, a multiplicity `m : H →₀ ℕ` supported
  in `S`, has total multiplicity bounded by a constant depending only on `A`
  (`TauCeti.IsComassBounded.exists_forall_sum_le`), and only finitely many such `m` represent a
  given class `A` (`TauCeti.IsComassBounded.finite_setOf_sum_smul_eq`);
* a class of nonpositive area, in particular a torsion class, is represented only by the empty
  cycle (`TauCeti.eq_zero_of_area_sum_smul_nonpos`, `TauCeti.eq_zero_of_isOfFinAddOrder_sum_smul`).
  These need only positivity of area. A nonzero torsion class therefore has no positive
  representative, although all its real periods vanish.

The lattice input is `LinearMap.finite_preimage_of_injective_liftBaseChange`. The geometric
inputs, positivity of area and the comass bound, are the fields of `TauCeti.IsComassBounded`.

## References

* M. Gromov, *Pseudo holomorphic curves in symplectic manifolds*, Invent. Math. 82 (1985),
  307–347.
* C. H. Taubes, *Counting pseudo-holomorphic submanifolds in dimension 4*, J. Differential Geom.
  44 (1996), 818–893.
-/

public section

namespace TauCeti

variable {H E : Type*} [AddCommGroup H] [NormedAddCommGroup E]

section Positive

variable {ω : H →+ ℝ} {S : Set H}

/-- Each class of a cycle supported in a set of classes of positive area has area at most that of
the cycle. -/
theorem area_le_area_sum_smul (hS : ∀ C ∈ S, 0 < ω C) {m : H →₀ ℕ}
    (hm : ↑m.support ⊆ S) {C : H} (hC : C ∈ m.support) :
    ω C ≤ ω (m.sum fun C k => k • C) := by
  classical
  have hpos : ∀ D ∈ m.support, 0 ≤ (m D : ℝ) * ω D := fun D hD =>
    mul_nonneg (Nat.cast_nonneg _) (hS D (hm hD)).le
  rw [map_finsuppSum, Finsupp.sum]
  simp only [map_nsmul, nsmul_eq_mul]
  calc ω C ≤ m C * ω C := le_mul_of_one_le_left (hS C (hm hC)).le
        (Nat.one_le_cast.2 (Nat.one_le_iff_ne_zero.2 (Finsupp.mem_support_iff.1 hC)))
    _ ≤ ∑ D ∈ m.support, (m D : ℝ) * ω D := Finset.single_le_sum hpos hC

/-- A class of nonpositive area is represented by no nonempty cycle supported in a set of classes
of positive area. -/
theorem eq_zero_of_area_sum_smul_nonpos (hS : ∀ C ∈ S, 0 < ω C) {m : H →₀ ℕ}
    (hm : ↑m.support ⊆ S) (hA : ω (m.sum fun C k => k • C) ≤ 0) : m = 0 := by
  by_contra hm0
  obtain ⟨C, hC⟩ := Finsupp.support_nonempty_iff.2 hm0
  exact (hS C (hm hC)).not_ge ((area_le_area_sum_smul hS hm hC).trans hA)

/-- A torsion class is represented by no nonempty cycle supported in a set of classes of positive
area. In particular a nonzero torsion class has no such representative. -/
theorem eq_zero_of_isOfFinAddOrder_sum_smul (hS : ∀ C ∈ S, 0 < ω C) {m : H →₀ ℕ}
    (hm : ↑m.support ⊆ S) (hA : IsOfFinAddOrder (m.sum fun C k => k • C)) : m = 0 :=
  eq_zero_of_area_sum_smul_nonpos hS hm (ω.isOfFinAddOrder hA).eq_zero'.le

end Positive

/-- A set `S` of classes in an abelian group `H`, with an area `ω : H → ℝ` and a period map
`l : H → E`, is *comass bounded* with constant `K` if every class of `S` has positive area and
periods of norm at most `K` times its area. For `H = H₂(X; ℤ)` these are the inequalities
satisfied by the classes of nonconstant `J`-holomorphic curves, with `K` bounding the comasses of
the closed forms defining `l`. -/
structure IsComassBounded (l : H →ₗ[ℤ] E) (ω : H →+ ℝ) (K : ℝ) (S : Set H) : Prop where
  /-- Every class of `S` has positive area. -/
  area_pos : ∀ C ∈ S, 0 < ω C
  /-- The periods of every class of `S` are bounded by `K` times its area. -/
  norm_le : ∀ C ∈ S, ‖l C‖ ≤ K * ω C

namespace IsComassBounded

variable {l : H →ₗ[ℤ] E} {ω : H →+ ℝ} {K : ℝ} {S : Set H}

/-- **Gromov's finiteness of classes.** If the real extension of the period map is injective,
only finitely many classes of a comass bounded set have area at most `R`. -/
theorem finite_setOf_area_le [AddGroup.FG H] [NormedSpace ℝ E] (h : IsComassBounded l ω K S)
    (hl : Function.Injective (l.liftBaseChange ℝ)) (R : ℝ) : {C ∈ S | ω C ≤ R}.Finite := by
  refine (l.finite_preimage_of_injective_liftBaseChange hl
    (Metric.isBounded_closedBall (x := 0) (r := |K| * R))).subset ?_
  rintro C ⟨hC, hCR⟩
  rw [Set.mem_preimage, mem_closedBall_zero_iff]
  calc ‖l C‖ ≤ K * ω C := h.norm_le C hC
    _ ≤ |K| * ω C := mul_le_mul_of_nonneg_right (le_abs_self K) (h.area_pos C hC).le
    _ ≤ |K| * R := mul_le_mul_of_nonneg_left hCR (abs_nonneg K)

/-- **Uniform positive area.** If the real extension of the period map is injective, the areas of
the classes of a comass bounded set are bounded below by a positive constant. -/
theorem exists_pos_forall_le_area [AddGroup.FG H] [NormedSpace ℝ E] (h : IsComassBounded l ω K S)
    (hl : Function.Injective (l.liftBaseChange ℝ)) : ∃ ε > 0, ∀ C ∈ S, ε ≤ ω C := by
  -- The minimum of `1` and of the finitely many areas at most `1`.
  have hfin : (insert 1 (ω '' {C ∈ S | ω C ≤ 1})).Finite :=
    ((h.finite_setOf_area_le hl 1).image ω).insert 1
  obtain ⟨ε, hε, hmin⟩ := Set.exists_min_image _ id hfin (Set.insert_nonempty _ _)
  refine ⟨ε, ?_, fun C hC => ?_⟩
  · rcases hε with rfl | ⟨C, ⟨hC, -⟩, rfl⟩
    exacts [one_pos, h.area_pos C hC]
  · rcases le_or_gt (ω C) 1 with hC1 | hC1
    · exact hmin _ (Set.mem_insert_of_mem _ ⟨C, ⟨hC, hC1⟩, rfl⟩)
    · exact (hmin 1 (Set.mem_insert _ _)).trans hC1.le

/-- **Bounded component count.** If the real extension of the period map is injective, the total
multiplicity of a cycle supported in a comass bounded set is bounded in terms of its class. -/
theorem exists_forall_sum_le [AddGroup.FG H] [NormedSpace ℝ E] (h : IsComassBounded l ω K S)
    (hl : Function.Injective (l.liftBaseChange ℝ)) (A : H) :
    ∃ N : ℕ, ∀ m : H →₀ ℕ, ↑m.support ⊆ S → (m.sum fun C k => k • C) = A →
      (m.sum fun _ k => k) ≤ N := by
  obtain ⟨ε, hε, hεS⟩ := h.exists_pos_forall_le_area hl
  refine ⟨⌊ω A / ε⌋₊, fun m hm hmA => Nat.le_floor ?_⟩
  rw [le_div_iff₀ hε, ← hmA, map_finsuppSum, Nat.cast_finsupp_sum, Finsupp.sum, Finsupp.sum,
    Finset.sum_mul]
  exact Finset.sum_le_sum fun C hC => by
    rw [map_nsmul, nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_left (hεS C (hm hC)) (Nat.cast_nonneg _)

/-- **Finitely many cycles in a class.** If the real extension of the period map is injective, only
finitely many multiplicity functions supported in a comass bounded set represent a given class. -/
theorem finite_setOf_sum_smul_eq [AddGroup.FG H] [NormedSpace ℝ E] (h : IsComassBounded l ω K S)
    (hl : Function.Injective (l.liftBaseChange ℝ)) (A : H) :
    {m : H →₀ ℕ | ↑m.support ⊆ S ∧ (m.sum fun C k => k • C) = A}.Finite := by
  classical
  obtain ⟨N, hN⟩ := h.exists_forall_sum_le hl A
  -- Every such cycle is supported in the finite window of classes of area at most `ω A`, with
  -- multiplicities at most `N`.
  let t := (h.finite_setOf_area_le hl (ω A)).toFinset
  refine (t.finsupp fun _ => Finset.range (N + 1)).finite_toSet.subset ?_
  rintro m ⟨hm, hmA⟩
  rw [Finset.mem_coe, Finset.mem_finsupp_iff]
  refine ⟨fun C hC => ?_, fun C _ => ?_⟩
  · rw [Set.Finite.mem_toFinset]
    exact ⟨hm hC, hmA ▸ area_le_area_sum_smul h.area_pos hm hC⟩
  · rw [Finset.mem_range, Nat.lt_succ_iff]
    by_cases hC : C ∈ m.support
    · exact (Finset.single_le_sum (fun _ _ => Nat.zero_le _) hC).trans (hN m hm hmA)
    · rw [Finsupp.notMem_support_iff.1 hC]
      exact Nat.zero_le _

end IsComassBounded

end TauCeti
