/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.SpecialLinear.Adjoint.Comodule

/-!
# The adjoint roots of the special linear group

The nontrivial weights of the adjoint comodule of `SL_{r+1}`, restricted to its diagonal
torus, are exactly the roots of `SpecialLinear.diagonalRootDatum`. Thus the abstract
type-`A_r` datum describes the full root set of the group, rather than only some of its
weights. The root indices are canonically equivalent to these nontrivial weights.

The classification holds over every nontrivial commutative base ring, including rings
with nilpotents and positive characteristic. Weight membership is tested by the torus
coaction, so it retains information that rational points alone may lose. The existing
integral root-space equivalences identify all the resulting root spaces with the base ring;
these are the root lines to which a pinning assigns generators.

## References

* J. S. Milne, *Algebraic Groups* (2017), §21.1 and Example 21.2.
* B. Conrad, *Reductive Group Schemes* (2014), §5.1.
* The entrywise argument and root-index API follow
  `TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Adjoint.Classification` and
  `TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Root.Adjoint`.
-/

public section

namespace TauCeti.SpecialLinear

universe u

noncomputable section

variable {R : Type u} [CommRing R] {r : ℕ}

/-- A nonzero entry of an adjoint weight vector determines its character, over any
commutative base ring. -/
theorem weightCharacter_eq_of_mem_adjointWeightSpace_of_apply_ne_zero
    {α : Multiplicative (ULift.{u} (Fin r) →₀ ℤ)}
    {x : Module.Dual R (Bialgebra.CotangentSpace R (coordinateHopfAlgebra R (r + 1)))}
    (hx : x ∈ Derivation.adjointWeightSpace (diagonalTorusCoordinateMap r R).hom α)
    {i j : Fin (r + 1)}
    (hentry : (tangentMatrix (r + 1) (Derivation.cotangentLinearEquiv (B := R) x) :
      Matrix (Fin (r + 1)) (Fin (r + 1)) R) i j ≠ 0) :
    SplitTorus.weightCharacter (diagonalTorusWeight r i - diagonalTorusWeight r j) = α := by
  by_contra hweight
  exact hentry ((mem_adjointWeightSpace_iff α x).mp hx i j hweight)

variable [Nontrivial R]

/-- Every root of the diagonal root datum occurs as a nontrivial adjoint weight of
`SL_{r+1}`. The normalized matrix unit witnesses that its weight space is nonzero. -/
@[simp↓ 1100]
theorem ofAdd_root_mem_nontrivialAdjointWeights
    (p : SplitTorus.CoordinateRootIndex (Fin (r + 1))) :
    Multiplicative.ofAdd ((diagonalRootDatum.{u} r).root p) ∈
      Derivation.nontrivialAdjointWeights (diagonalTorusCoordinateMap r R).hom := by
  rw [Derivation.mem_nontrivialAdjointWeights]
  refine ⟨?_, ?_⟩
  · intro h
    exact (diagonalRootDatum.{u} r).ne_zero p (congrArg Multiplicative.toAdd h)
  · -- The torus characters are stored as the indexed copy of the exponent lattice.
    erw [adjointWeightSpace_root_eq_span]
    exact (Submodule.ne_bot_iff _).mpr
      ⟨rootVector p, Submodule.mem_span_singleton_self _, rootVector_ne_zero p⟩

/-- The nontrivial adjoint weights of `SL_{r+1}` relative to its diagonal torus are
exactly the roots of its diagonal root datum. No field or reducedness assumption is needed. -/
theorem mem_nontrivialAdjointWeights_iff_exists_diagonalRoot
    (α : Multiplicative (ULift.{u} (Fin r) →₀ ℤ)) :
    α ∈ Derivation.nontrivialAdjointWeights (diagonalTorusCoordinateMap r R).hom ↔
      ∃ p : SplitTorus.CoordinateRootIndex (Fin (r + 1)),
        α = Multiplicative.ofAdd ((diagonalRootDatum.{u} r).root p) := by
  constructor
  · rw [Derivation.mem_nontrivialAdjointWeights]
    rintro ⟨hα, hspace⟩
    obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).mp hspace
    have hmatrix : (tangentMatrix (r + 1) (Derivation.cotangentLinearEquiv (B := R) x) :
        Matrix (Fin (r + 1)) (Fin (r + 1)) R) ≠ 0 := by
      intro hzero
      apply hx0
      apply (Derivation.cotangentLinearEquiv (R := R)
        (A := coordinateHopfAlgebra R (r + 1)) (B := R)).injective
      apply (tangentLieEquivSl (R := R) (B := R) (r + 1)).injective
      simp only [map_zero, LieEquiv.coe_toLieHom]
      -- The Lie equivalence stores the quotient-indexed coordinate presentation.
      erw [tangentLieEquivSl_apply]
      exact Subtype.ext hzero
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hmatrix
    obtain ⟨j, hij⟩ := Function.ne_iff.mp hi
    have hweight := weightCharacter_eq_of_mem_adjointWeightSpace_of_apply_ne_zero hx hij
    have hne : i ≠ j := by
      rintro rfl
      apply hα
      rw [← hweight]
      apply Multiplicative.toAdd.injective
      ext k
      simp
    refine ⟨⟨(i, j), hne⟩, ?_⟩
    exact hweight.symm.trans
      ((weightCharacter_diagonalTorusWeight_sub_eq_root_iff ⟨(i, j), hne⟩ i j).mpr
        ⟨rfl, rfl⟩)
  · rintro ⟨p, rfl⟩
    exact ofAdd_root_mem_nontrivialAdjointWeights p

/-- The root set of the diagonal root datum is the entire nontrivial adjoint weight
set of the special linear group. -/
theorem range_ofAdd_diagonalRootDatum_root_eq_nontrivialAdjointWeights :
    Set.range (fun p : SplitTorus.CoordinateRootIndex (Fin (r + 1)) ↦
        Multiplicative.ofAdd ((diagonalRootDatum.{u} r).root p)) =
      Derivation.nontrivialAdjointWeights (diagonalTorusCoordinateMap r R).hom := by
  ext α
  rw [Set.mem_range, mem_nontrivialAdjointWeights_iff_exists_diagonalRoot]
  exact exists_congr fun p ↦ eq_comm

/-- Ordered pairs of distinct matrix indices canonically index all nontrivial adjoint
weights of `SL_{r+1}`. -/
def diagonalRootIndexEquivNontrivialAdjointWeights :
    SplitTorus.CoordinateRootIndex (Fin (r + 1)) ≃
      {α // α ∈ Derivation.nontrivialAdjointWeights (diagonalTorusCoordinateMap r R).hom} :=
  (Equiv.ofInjective
    (fun p ↦ Multiplicative.ofAdd ((diagonalRootDatum.{u} r).root p))
    (Multiplicative.ofAdd.injective.comp (diagonalRootDatum.{u} r).root.injective)).trans
    (Set.equivOfEq range_ofAdd_diagonalRootDatum_root_eq_nontrivialAdjointWeights)

/-- The root-index equivalence sends an index to its root character. -/
@[simp]
theorem diagonalRootIndexEquivNontrivialAdjointWeights_apply
    (p : SplitTorus.CoordinateRootIndex (Fin (r + 1))) :
    (diagonalRootIndexEquivNontrivialAdjointWeights (R := R) p :
      Multiplicative (ULift.{u} (Fin r) →₀ ℤ)) =
      Multiplicative.ofAdd ((diagonalRootDatum.{u} r).root p) :=
  (rfl)

end

end TauCeti.SpecialLinear
