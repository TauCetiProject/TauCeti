/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.SmallGrid.SimplyBlocked.Differential
public import TauCeti.KnotTheory.Grid.Homology.SimplyBlocked
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.Polynomial.Div

/-!
# Simply blocked homology of the two-by-two unknot

The differential is `d(a · id + b · swap) = a V · swap`. Multiplication by `V` is
injective, even over a coefficient ring with zero divisors. Thus cycles are the multiples
of `swap`, and boundaries are exactly those whose coefficient has zero constant term.
Taking the constant term identifies the simply blocked homology with the coefficient
ring, on which the surviving variable acts by zero.

The class of `swap` corresponds to `1` and has bidegree `(0, 0)`; every homogeneous
cycle of another bidegree is a boundary. In particular, over `ZMod 2` the result is
one copy of the ground field concentrated in bidegree `(0, 0)`.

## References

Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Sections 4.4 and 4.6.
The quotient construction uses Mathlib's `LinearMap.quotKerEquivOfSurjective`.
-/

public section

open CategoryTheory MvPolynomial

namespace TauCeti.GridDiagram

variable (R : Type*) [CommRing R] [CharP R 2]

local notation "Poly" => MvPolynomial {c : Fin 2 // c ≠ 0} R
local notation "Cyc" => twoByTwo.isKnot_of_two.simplyBlockedCycles R 0
local notation "eChain" => twoByTwo.simplyBlockedChainEquiv R 0

/-- A chain is a cycle exactly when its identity-state coefficient vanishes. -/
theorem twoByTwo_mem_simplyBlockedCycles_iff (c : (twoByTwo.simplyBlockedComplex R 0).X ()) :
    c ∈ twoByTwo.isKnot_of_two.simplyBlockedCycles R 0 ↔
      eChain c GridState.twoByTwoId = 0 := by
  rw [IsKnot.mem_simplyBlockedCycles, twoByTwo_simplyBlockedDifferential_apply,
    Finsupp.single_eq_zero]
  simpa only [zero_mul] using (X_mul_cancel_right_iff
    (p := eChain c GridState.twoByTwoId) (q := 0) (i := twoByTwoSurvivingColumn))

private theorem cycle_eq_single (c : Cyc) :
    eChain c.val = Finsupp.single GridState.twoByTwoSwap
      (eChain c.val GridState.twoByTwoSwap) := by
  ext x : 1
  rcases GridState.eq_twoByTwoId_or_eq_twoByTwoSwap x with rfl | rfl
  · simpa using (twoByTwo_mem_simplyBlockedCycles_iff R c.val).mp c.property
  · simp

/-- A cycle is a boundary exactly when its transposition-state coefficient has zero
constant term. -/
theorem twoByTwo_mem_simplyBlockedBoundaries_iff (c : Cyc) :
    c ∈ twoByTwo.isKnot_of_two.simplyBlockedBoundaries R 0 ↔
      constantCoeff (eChain c.val GridState.twoByTwoSwap) = 0 := by
  constructor
  · rintro ⟨b, rfl⟩
    simp [IsKnot.simplyBlockedChainEquiv_boundaryMap]
  · intro hc
    let : Unique {c : Fin 2 // c ≠ 0} :=
      ⟨⟨twoByTwoSurvivingColumn⟩, fun c => Subtype.ext (by
        have h := c.property
        have hlt := c.val.isLt
        have hne : c.val.val ≠ 0 := by simpa using h
        apply Fin.ext
        dsimp [twoByTwoSurvivingColumn]
        omega)⟩
    let e := uniqueAlgEquiv R {c : Fin 2 // c ≠ 0}
    have hz : (e (eChain c.val GridState.twoByTwoSwap)).coeff 0 = 0 := by
      rw [coeff_uniqueAlgEquiv]
      simpa only [Finsupp.single_zero, ← constantCoeff_eq] using hc
    obtain ⟨q, hq⟩ := Polynomial.X_dvd_iff.mpr hz
    have he : eChain c.val GridState.twoByTwoSwap =
        e.symm q * MvPolynomial.X twoByTwoSurvivingColumn := by
      apply e.injective
      rw [map_mul, AlgEquiv.apply_symm_apply]
      have hx : e (MvPolynomial.X twoByTwoSurvivingColumn) = Polynomial.X := by
        simp [e]
      rw [hx, mul_comm]
      exact hq
    refine ⟨(eChain).symm (Finsupp.single GridState.twoByTwoId (e.symm q)), ?_⟩
    apply Subtype.ext
    apply (eChain).injective
    simp only [IsKnot.simplyBlockedChainEquiv_boundaryMap, LinearEquiv.apply_symm_apply]
    rw [twoByTwo_simplyBlockedDifferential_apply,
      Finsupp.single_eq_same, ← he, ← cycle_eq_single]

private noncomputable def cycleConstantCoeff :
    letI := Module.compHom R (constantCoeff : Poly →+* R)
    Cyc →ₗ[Poly] R :=
  letI := Module.compHom R (constantCoeff : Poly →+* R)
  { toFun c := constantCoeff (eChain c.val GridState.twoByTwoSwap)
    map_add' c d := by simp
    map_smul' a c := by
      simp only [SetLike.val_smul, LinearEquiv.map_smul]
      -- The target action is restriction along constantCoeff; write both actions explicitly
      -- to avoid selecting its induced coefficientwise action on the polynomial ring.
      change constantCoeff (a * eChain c.val GridState.twoByTwoSwap) =
        constantCoeff a * constantCoeff (eChain c.val GridState.twoByTwoSwap)
      exact map_mul _ _ _ }

private theorem ker_cycleConstantCoeff :
    letI := Module.compHom R (constantCoeff : Poly →+* R)
    LinearMap.ker (cycleConstantCoeff R) =
      twoByTwo.isKnot_of_two.simplyBlockedBoundaries R 0 := by
  ext c
  exact (twoByTwo_mem_simplyBlockedBoundaries_iff R c).symm

private theorem cycleConstantCoeff_surjective : Function.Surjective (cycleConstantCoeff R) := by
  intro r
  refine ⟨⟨(eChain).symm (Finsupp.single GridState.twoByTwoSwap (C r)), ?_⟩, ?_⟩
  · rw [twoByTwo_mem_simplyBlockedCycles_iff]
    simp
  · simp [cycleConstantCoeff]

/-- The simply blocked homology of the standard two-by-two unknot is the ground ring,
with the surviving polynomial variable acting by zero. The equivalence takes the constant
term of the transposition-state coefficient of a cycle representative. -/
noncomputable def twoByTwoSimplyBlockedHomologyEquiv :
    letI := Module.compHom R (constantCoeff : Poly →+* R)
    twoByTwo.isKnot_of_two.simplyBlockedHomology R 0 ≃ₗ[Poly] R :=
  letI := Module.compHom R (constantCoeff : Poly →+* R)
  (twoByTwo.isKnot_of_two.simplyBlockedHomologyIsoQuotient R 0).toLinearEquiv.trans
    ((Submodule.quotEquivOfEq _ _ (ker_cycleConstantCoeff R).symm).trans
      ((cycleConstantCoeff R).quotKerEquivOfSurjective (cycleConstantCoeff_surjective R)))

/-- The homology equivalence is computed on any cycle by its transposition coefficient. -/
@[simp]
theorem twoByTwoSimplyBlockedHomologyEquiv_class (c : Cyc) :
    twoByTwoSimplyBlockedHomologyEquiv R
        (twoByTwo.isKnot_of_two.simplyBlockedHomologyClass R 0 c) =
      constantCoeff (eChain c.val GridState.twoByTwoSwap) := by
  let := Module.compHom R (constantCoeff : Poly →+* R)
  simp only [twoByTwoSimplyBlockedHomologyEquiv, LinearEquiv.trans_apply]
  rw [Iso.toLinearEquiv_apply, IsKnot.simplyBlockedHomologyIsoQuotient_hom_class,
    Submodule.quotEquivOfEq_mk, LinearMap.quotKerEquivOfSurjective_apply_mk]
  rfl

/-- The inverse image of one is the class of the transposition-state cycle, which has
Maslov--Alexander bidegree `(0, 0)`. -/
@[simp]
theorem twoByTwoSimplyBlockedHomologyEquiv_symm_one :
    (twoByTwoSimplyBlockedHomologyEquiv R).symm 1 =
      twoByTwo.isKnot_of_two.simplyBlockedHomologyClass R 0
        ⟨(eChain).symm (twoByTwoSimplyBlockedCycle R),
          (IsKnot.mem_simplyBlockedCycles R _ _ _).mpr (by simp)⟩ := by
  apply (twoByTwoSimplyBlockedHomologyEquiv R).injective
  simp

/-- A homogeneous cycle in a bidegree other than `(0, 0)` represents zero in the
simply blocked homology of the standard two-by-two unknot. -/
theorem twoByTwo_simplyBlockedHomologyClass_eq_zero_of_bidegree_ne
    (c : Cyc) {g : ℤ × ℤ} (hg : g ≠ (0, 0))
    (hc : eChain c.val ∈ OddComponentGridDiagram.twoByTwo.bigradedChainHatPiece R 0 g) :
    twoByTwo.isKnot_of_two.simplyBlockedHomologyClass R 0 c = 0 := by
  rw [IsKnot.simplyBlockedHomologyClass_eq_zero_iff,
    twoByTwo_mem_simplyBlockedBoundaries_iff]
  by_contra h
  have hmem : (0 : {c : Fin 2 // c ≠ 0} →₀ ℕ) ∈
      (eChain c.val GridState.twoByTwoSwap).support := by
    simpa only [MvPolynomial.mem_support_iff, ← constantCoeff_eq] using h
  have hdegree := (OddComponentGridDiagram.twoByTwo.mem_bigradedChainHatPiece.mp hc)
    GridState.twoByTwoSwap 0 hmem
  apply hg
  simpa [OddComponentGridDiagram.bidegree_twoByTwo_twoByTwoSwap,
    Finsupp.degree_apply, Prod.ext_iff] using hdegree.symm

end TauCeti.GridDiagram
