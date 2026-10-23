/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Commutation.Homotopy.Decomposition
public import TauCeti.KnotTheory.Grid.Commutation.Grading.Hexagon
public import TauCeti.KnotTheory.Grid.Grading.SimplyBlocked

/-!
# The simply blocked commutation homotopy

Setting the variable of a chosen `O`-marking to zero in the commutation hexagon map
retains exactly the empty hexagons avoiding that marking and all `X`-markings.
Both turn sides contribute. The resulting endomorphism of the simply blocked chain
module raises Maslov degree by one and preserves Alexander degree.

This supplies the specified hexagon map for the simply blocked commutation comparison.
The homotopy identity comparing the round trip of pentagon maps with the identity is
separate; no such identity is assumed or proved here. For a link, blocking just one
marking need not block every component, so the usual simply blocked knot interpretation
requires a knot diagram. The specialization and grading statements hold for arbitrary
diagrams (with an odd number of components for the integral Alexander grading).

## References

Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Sections 4.6 and 5.1,
and Manolescu--Ozsváth--Szabó--Thurston, *On combinatorial link Floer homology*,
Section 3.1 (arXiv:math/0610559). The construction specializes the existing
`GridDiagram.commutationHomotopy` using `simplyBlockedSpecialization`.
-/

public section

namespace TauCeti

open MvPolynomial

namespace GridDiagram

variable {n : ℕ} (G : GridDiagram n) (R : Type*) [CommSemiring R]
  (C : ColumnCommutationData G)

/-- The hexagon-counting endomorphism after setting the variable of column `i` to zero.
It counts both turn sides, with coefficients in the variables of the remaining columns. -/
noncomputable def simplyBlockedCommutationHomotopy (i : Fin n) :
    GridChainHat R n i →ₗ[MvPolynomial {c : Fin n // c ≠ i} R] GridChainHat R n i :=
  Finsupp.linearCombination _ fun x =>
    simplyBlockedSpecialization R i (G.commutationHomotopy R C (Finsupp.single x 1))

/-- On a generator, the simply blocked hexagon map specializes the unblocked hexagon map. -/
theorem simplyBlockedCommutationHomotopy_single (i : Fin n) (x : GridState n) :
    G.simplyBlockedCommutationHomotopy R C i (Finsupp.single x 1) =
      simplyBlockedSpecialization R i (G.commutationHomotopy R C (Finsupp.single x 1)) := by
  rw [simplyBlockedCommutationHomotopy, Finsupp.linearCombination_single, one_smul]

/-- The matrix entries of the simply blocked homotopy are the specialized hexagon counts. -/
@[simp]
theorem simplyBlockedCommutationHomotopy_single_apply (i : Fin n) (x y : GridState n) :
    G.simplyBlockedCommutationHomotopy R C i (Finsupp.single x 1) y =
      simplyBlockedRingHom R i (G.commutationHexagonCoefficient R C x y) := by
  rw [simplyBlockedCommutationHomotopy_single, simplyBlockedSpecialization_apply,
    commutationHomotopy_single_apply, simplyBlockedRingHom_apply]

/-- The simply blocked homotopy multiplies a chain by the specialized hexagon matrix. -/
@[simp 900] -- Prefer the generator formula to the general chain expansion.
theorem simplyBlockedCommutationHomotopy_apply_apply (i : Fin n)
    (c : GridChainHat R n i) (y : GridState n) :
    G.simplyBlockedCommutationHomotopy R C i c y =
      c.sum fun x p => p * simplyBlockedRingHom R i (G.commutationHexagonCoefficient R C x y) := by
  rw [simplyBlockedCommutationHomotopy, Finsupp.linearCombination_apply]
  simp only [Finsupp.sum_apply, Finsupp.smul_apply, smul_eq_mul,
    simplyBlockedSpecialization_apply, commutationHomotopy_single_apply,
    simplyBlockedRingHom_apply]

/-- Specialization at the blocked variable intertwines the two hexagon-counting maps. -/
@[simp]
theorem simplyBlockedSpecialization_commutationHomotopy (i : Fin n) (c : GridChainMinus R n) :
    simplyBlockedSpecialization R i (G.commutationHomotopy R C c) =
      G.simplyBlockedCommutationHomotopy R C i (simplyBlockedSpecialization R i c) := by
  apply Finsupp.ext
  intro y
  simp only [simplyBlockedSpecialization_apply, commutationHomotopy_apply_apply,
    simplyBlockedCommutationHomotopy_apply_apply, commutationHexagonCoefficient_def,
    simplyBlockedRingHom_apply]
  rw [Finsupp.sum_fintype _ _ (fun _ => zero_mul _),
    Finsupp.sum_fintype _ _ (fun _ => zero_mul _), map_sum]
  simp only [map_mul, simplyBlockedSpecialization_apply]

/-- Blocking a hexagon weight discards the term if the hexagon covers the chosen `O`-marking;
otherwise it is the product of the surviving marking variables. -/
theorem simplyBlockedRingHom_commutationHexagonWeight (i : Fin n) {x y : GridState n}
    (P : GridCommutationHexagonBetween C.column C.turnRow C.oppositeTurnRow x y) :
    simplyBlockedRingHom R i (G.commutationHexagonWeight C R P) =
      if i ∈ G.OColumnsOfSquares P.coveredSquares then 0 else
        ∏ c ∈ (G.OColumnsOfSquares P.coveredSquares).subtype (· ≠ i), MvPolynomial.X c := by
  classical
  have hw : G.commutationHexagonWeight C R P =
      monomial (∑ c ∈ G.OColumnsOfSquares P.coveredSquares, Finsupp.single c 1) 1 := by
    cases P with
    | inl P => rw [G.commutationHexagonWeight_inl, G.hexagonWeight_eq_monomial,
        GridCommutationHexagonBetween.coveredSquares_inl]
    | inr P => rw [G.commutationHexagonWeight_inr, G.initialHexagonWeight_eq_monomial,
        GridCommutationHexagonBetween.coveredSquares_inr]
  rw [simplyBlockedRingHom_apply]
  split_ifs with hi
  · rw [hw]
    refine killCompl_monomial_eq_zero_of_notMem_range _ 1 (a := i) ?_ (by simp)
    rw [Finsupp.support_sum_eq_biUnion _ (by simp)]
    simpa using hi
  · have hrename :
        rename (Subtype.val : {c : Fin n // c ≠ i} → Fin n)
            (∏ c ∈ (G.OColumnsOfSquares P.coveredSquares).subtype (· ≠ i),
              MvPolynomial.X (R := R) c) =
          G.commutationHexagonWeight C R P := by
      rw [map_prod, hw, monomial_sum_one]
      simp only [rename_X]
      simpa only [← X_pow_eq_monomial, pow_one] using
        Finset.prod_subtype_of_mem (s := G.OColumnsOfSquares P.coveredSquares)
          (p := fun c : Fin n => c ≠ i) (MvPolynomial.X (R := R))
          (fun c hc hci => hi (hci ▸ hc))
    rw [← hrename, killCompl_rename_app]

/-- A simply blocked matrix entry is the sum of the weights of exactly those counted
hexagons which avoid the blocked `O`-marking. -/
theorem simplyBlockedCommutationHomotopy_single_apply_eq_sum (i : Fin n)
    (x y : GridState n) :
    G.simplyBlockedCommutationHomotopy R C i (Finsupp.single x 1) y =
      ∑ P ∈ (G.commutationHexagons C x y).filter
          (fun P => i ∉ G.OColumnsOfSquares P.coveredSquares),
        ∏ c ∈ (G.OColumnsOfSquares P.coveredSquares).subtype (· ≠ i), MvPolynomial.X c := by
  classical
  rw [G.simplyBlockedCommutationHomotopy_single_apply,
    G.commutationHexagonCoefficient_eq_sum_weight C R, map_sum]
  simp only [G.simplyBlockedRingHom_commutationHexagonWeight R C, Finset.sum_filter]
  refine Finset.sum_congr rfl fun P _ => ?_
  split_ifs <;> simp_all

end GridDiagram

namespace OddComponentGridDiagram

variable {n : ℕ} (G : OddComponentGridDiagram n) (R : Type*) [CommSemiring R]
  (C : GridDiagram.ColumnCommutationData G.1)

/-- The simply blocked commutation homotopy has bidegree `(1, 0)` over any commutative
coefficient semiring: Maslov degree increases by one and Alexander degree is preserved. -/
theorem simplyBlockedCommutationHomotopy_mem_bigradedChainHatPiece (i : Fin n)
    {g : ℤ × ℤ} {c : GridChainHat R n i} (hc : c ∈ G.bigradedChainHatPiece R i g) :
    G.1.simplyBlockedCommutationHomotopy R C i c ∈
      G.bigradedChainHatPiece R i (g + (1, 0)) := by
  obtain ⟨b, hb, rfl⟩ := G.mem_bigradedChainHatPiece_iff_exists.mp hc
  rw [← GridDiagram.simplyBlockedSpecialization_commutationHomotopy]
  exact G.simplyBlockedSpecialization_mem_bigradedChainHatPiece i
    (G.commutationHomotopy_mem_bigradedChainMinusPiece C R hb)

/-- The simply blocked hexagon homotopy between homogeneous pieces at a fixed
Alexander degree, raising Maslov degree by one. -/
noncomputable def gradedSimplyBlockedCommutationHomotopy (i : Fin n) (a m : ℤ) :
    G.bigradedChainHatPiece R i (m, a) →ₗ[R] G.bigradedChainHatPiece R i (m + 1, a) :=
  ((G.1.simplyBlockedCommutationHomotopy R C i).restrictScalars R).restrict fun c hc => by
    simpa using G.simplyBlockedCommutationHomotopy_mem_bigradedChainHatPiece R C i hc

/-- Inclusion into the total chain module intertwines the graded and total hexagon maps. -/
@[simp]
theorem coe_gradedSimplyBlockedCommutationHomotopy (i : Fin n) (a m : ℤ)
    (c : G.bigradedChainHatPiece R i (m, a)) :
    (G.gradedSimplyBlockedCommutationHomotopy R C i a m c : GridChainHat R n i) =
      G.1.simplyBlockedCommutationHomotopy R C i c := (rfl)

end OddComponentGridDiagram

end TauCeti
