/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Quiver.Star
public import TauCeti.RepresentationTheory.Quiver.PathAlgebra.Augmentation
public import TauCeti.RepresentationTheory.Quiver.PathAlgebra.PathsInto
public import TauCeti.RepresentationTheory.Quiver.Preprojective.Signless
public import TauCeti.RepresentationTheory.Quiver.Preprojective.Signless.Grading

/-!
# The augmentation endpoint of the signless preprojective Koszul complex

The signless preprojective algebra augments onto the product of the coefficient rings at its
vertices. In the right vertex projective `e_v Π`, the kernel of the vertex coefficient is
exactly the image of the incoming-arrow map `(z_b) ↦ ∑ b z_b`. Every scalar occurs as a vertex
coefficient, so the cokernel of this map is one copy of the coefficient ring, not an unspecified
quotient. These statements complete the augmentation endpoint of the signless Koszul complex.
They work over every commutative ring, also for non-bipartite doubled graphs and in
characteristic two. The positive path-degree characterization below identifies the same
arrow image in a finite quiver with reversal. Injectivity at the left endpoint still
requires the non-backtracking hypothesis from the signless Koszul complex.

For a connected simple graph with at least three vertices, the signless algebra is the
quadratic dual of its zigzag algebra, whereas it need not be the signed preprojective algebra
on a non-bipartite graph. No signed/signless comparison is used here.

## References

* S. Huerfano and M. Khovanov, *A category for the adjoint representation*, Section 3,
  for the signless quadratic dual.
* P. Etingof and C.-H. Eu, *Koszulity and the Hilbert series of preprojective algebras*,
  Sections 2 and 3, for the vertex Koszul complex.
-/

public section

namespace TauCeti

open _root_.Quiver PathAlgebra

universe u v w

/-- Choose enumerations of the finite arrow types for the augmentation sums. -/
noncomputable local instance fintypeHomOfFiniteStar {R : Type u} [Quiver.{v} R]
    [∀ x : R, Fintype (Quiver.Star x)] (i j : R) : Fintype (i ⟶ j) :=
  Fintype.ofFinite _

section VertexAugmentation

variable (k : Type w) [CommRing k] {R : Type u} [Quiver.{v} R] [HasReverse R]
  [Finite R] [∀ x : R, Fintype (Quiver.Star x)]

local notation "Π" => signlessPreprojectiveAlgebra k R
local notation "π" => signlessPreprojectiveMk k R

/-- The signless relation ideal lies in the square of the arrow ideal, since each relator
is a sum of length-two backtracks. In particular the vertex coefficients survive the quotient. -/
theorem signlessPreprojectiveIdeal_le_arrowIdeal_sq :
    (signlessPreprojectiveIdeal k R).asIdeal ≤ arrowIdeal k R ^ 2 := by
  rw [← Ideal.asIdeal_toTwoSided (arrowIdeal k R ^ 2)]
  refine TwoSidedIdeal.asIdeal.monotone ?_
  rw [signlessPreprojectiveIdeal_eq_span, TwoSidedIdeal.span_le]
  rintro _ ⟨v, rfl⟩
  rw [SetLike.mem_coe, Ideal.mem_toTwoSided]
  dsimp only
  rw [signlessPreprojectiveRelator_def]
  refine sum_mem fun e _ => ?_
  exact Ideal.pow_le_pow_right (by simp) (ofPath_mem_arrowIdeal_pow _)

/-- The signless relation ideal lies in the arrow ideal, so vertex coefficients descend
to the signless preprojective algebra. -/
theorem signlessPreprojectiveIdeal_le_arrowIdeal :
    (signlessPreprojectiveIdeal k R).asIdeal ≤ arrowIdeal k R :=
  (signlessPreprojectiveIdeal_le_arrowIdeal_sq k).trans (Ideal.pow_le_self two_ne_zero)

/-- The augmentation of the signless preprojective algebra onto its vertex coefficients. -/
noncomputable def signlessPreprojectiveAugmentation : Π →ₐ[k] (R → k) :=
  quotientTrivialCoeff (signlessPreprojectiveIdeal_le_arrowIdeal k)

/-- The augmentation kernel is the image of the arrow ideal in the signless algebra. -/
theorem ker_signlessPreprojectiveAugmentation :
    RingHom.ker (signlessPreprojectiveAugmentation (R := R) k) =
      (arrowIdeal k R).map π := by
  rw [signlessPreprojectiveAugmentation, ker_quotientTrivialCoeff]
  congr 1
  ext f
  exact (signlessPreprojectiveMk_apply k R f).symm

/-- On quotient representatives, the augmentation reads the trivial-path coefficients. -/
@[simp]
theorem signlessPreprojectiveAugmentation_mk (f : pathAlgebra k R) :
    signlessPreprojectiveAugmentation k (π f) = trivialCoeff k R f := by
  rw [signlessPreprojectiveAugmentation, signlessPreprojectiveMk_apply,
    quotientTrivialCoeff_mk]

/-- Every arrow has zero augmentation. -/
theorem signlessPreprojectiveAugmentation_ofArrow {i j : R} (b : i ⟶ j) :
    signlessPreprojectiveAugmentation k (π (ofArrow b)) = 0 := by
  rw [signlessPreprojectiveAugmentation_mk, trivialCoeff_ofArrow]

/-- Every family of vertex coefficients occurs in the signless preprojective algebra. -/
theorem signlessPreprojectiveAugmentation_surjective :
    Function.Surjective (signlessPreprojectiveAugmentation (R := R) k) :=
  quotientTrivialCoeff_surjective (signlessPreprojectiveIdeal_le_arrowIdeal k)

/-- On the right vertex projective `e_v Π`, only the coefficient at `v` can be nonzero. -/
theorem signlessPreprojectiveAugmentation_eq_single [DecidableEq R] (v : R) {x : Π}
    (hx : π (vertexIdempotent k v) * x = x) :
    signlessPreprojectiveAugmentation k x =
      Pi.single v (signlessPreprojectiveAugmentation k x v) := by
  simpa only [signlessPreprojectiveAugmentation] using
    quotientTrivialCoeff_eq_single_of_vertexIdempotent_mul
      (signlessPreprojectiveIdeal_le_arrowIdeal k) v
      (by simpa only [signlessPreprojectiveMk_apply] using hx)

/-- Exactness at the augmentation endpoint of the signless vertex Koszul complex:
`x ∈ e_v Π` has vertex coefficient zero exactly when `x = ∑ b z_b` with `z_b ∈ e_i Π`.
This holds without a non-backtracking choice or a bipartiteness hypothesis. -/
theorem signlessPreprojectiveAugmentation_apply_eq_zero_iff_exists_eq_sum
    [Fintype R] (v : R) {x : Π}
    (hx : π (vertexIdempotent k v) * x = x) :
    signlessPreprojectiveAugmentation k x v = 0 ↔
      ∃ z : (i : R) → (i ⟶ v) → Π,
        (∀ i b, π (vertexIdempotent k i) * z i b = z i b) ∧
          x = ∑ i, ∑ b : i ⟶ v, π (ofArrow b) * z i b := by
  simpa only [signlessPreprojectiveAugmentation, signlessPreprojectiveMk_apply] using
    quotientTrivialCoeff_apply_eq_zero_iff_exists_eq_sum
      (signlessPreprojectiveIdeal_le_arrowIdeal k) v
      (by simpa only [signlessPreprojectiveMk_apply] using hx)

/-- Every scalar is the vertex coefficient of an element of the right vertex projective. -/
theorem exists_signlessPreprojectiveAugmentation_apply_eq (v : R) (c : k) :
    ∃ x : Π, π (vertexIdempotent k v) * x = x ∧
      signlessPreprojectiveAugmentation k x v = c := by
  simpa only [signlessPreprojectiveAugmentation, signlessPreprojectiveMk_apply] using
    exists_quotientTrivialCoeff_apply_eq
      (signlessPreprojectiveIdeal_le_arrowIdeal k) v c

end VertexAugmentation

section PositiveDegree

variable (k : Type w) (R : Type u) [CommRing k] [Quiver.{v} R] [HasReverse R]
  [Fintype R] [∀ x : R, Fintype (Quiver.Star x)]

/-- An element of the vertex corner has positive path degree exactly when it is a sum of
incoming arrows times elements of their source corners. This is exactness at the augmentation
endpoint of the signless Koszul complex. -/
theorem mem_iSup_signlessPreprojectiveGrade_add_one_iff_exists_eq_sum (v : R)
    {x : signlessPreprojectiveAlgebra k R}
    (hx : signlessPreprojectiveMk k R (vertexIdempotent k v) * x = x) :
    x ∈ ⨆ n, signlessPreprojectiveGrade k R (n + 1) ↔
      ∃ z : (i : R) → (i ⟶ v) → signlessPreprojectiveAlgebra k R,
        (∀ i b, signlessPreprojectiveMk k R (vertexIdempotent k i) * z i b = z i b) ∧
          x = ∑ i, ∑ b, signlessPreprojectiveMk k R (ofArrow b) * z i b := by
  refine ⟨fun h => ?_, ?_⟩
  · obtain ⟨z, hz, hxz⟩ : ∃ z : (i : R) → (i ⟶ v) → signlessPreprojectiveAlgebra k R,
        (∀ i b, signlessPreprojectiveMk k R (vertexIdempotent k i) * z i b = z i b) ∧
          signlessPreprojectiveMk k R (vertexIdempotent k v) * x =
            ∑ i, ∑ b, signlessPreprojectiveMk k R (ofArrow b) * z i b := by
      refine Submodule.iSup_induction (motive := fun x => ∃ z : (i : R) →
          (i ⟶ v) → signlessPreprojectiveAlgebra k R,
          (∀ i b, signlessPreprojectiveMk k R (vertexIdempotent k i) * z i b = z i b) ∧
            signlessPreprojectiveMk k R (vertexIdempotent k v) * x =
              ∑ i, ∑ b, signlessPreprojectiveMk k R (ofArrow b) * z i b) _ h
        (fun n x hx' => ?_) ⟨0, fun _ _ => mul_zero _, by simp⟩
        fun x x' hx hx' => ?_
      · obtain ⟨y, hy, rfl⟩ := (mem_signlessPreprojectiveGrade_iff k R).1 hx'
        obtain ⟨w, hw, hwy⟩ := exists_eq_sum_ofArrow_mul
          (vertexIdempotent_mul_mem_pathsInto v hy)
        refine ⟨fun i b => signlessPreprojectiveMk k R (w i b), fun i b => ?_, ?_⟩
        · rw [← map_mul, vertexIdempotent_mul_of_mem_pathsInto (hw i b)]
        · rw [← map_mul, hwy]
          simp only [map_sum, map_mul]
      · obtain ⟨z, hz, hxz⟩ := hx
        obtain ⟨z', hz', hxz'⟩ := hx'
        refine ⟨z + z', fun i b => ?_, ?_⟩
        · rw [Pi.add_apply, Pi.add_apply, mul_add, hz, hz']
        · simp only [mul_add, hxz, hxz', Pi.add_apply, Finset.sum_add_distrib]
    exact ⟨z, hz, hx.symm.trans hxz⟩
  · rintro ⟨z, -, rfl⟩
    exact sum_mem fun i _ => sum_mem fun b _ =>
      signlessPreprojectiveMk_ofArrow_mul_mem_iSup k R b (z i b)

end PositiveDegree

end TauCeti
