/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.UnitSquareClasses
public import TauCeti.NumberTheory.QuadraticForm.OrthogonalGroup.SpinorNormImage
import TauCeti.LinearAlgebra.QuadraticForm.Diagonal.Basic
import TauCeti.LinearAlgebra.QuadraticForm.Witt.Decomposition
import TauCeti.Topology.Algebra.CliffordAlgebra.Spin.Proper
import TauCeti.Topology.Algebra.QuadraticForm.OrthogonalGroup.Compact

/-!
# Low-rank compact-open reference families

A nondegenerate quadratic space of dimension at most one is anisotropic over every field
extension. Consequently its full local orthogonal and Spin groups are compact as well as open,
and choosing both full groups gives compatible compact-open reference data.

For a one-dimensional rational quadratic space, the derived special orthogonal group is trivial.
Its local spinor-norm image is therefore trivial at every prime. At an odd prime this differs from
the subgroup of unit square classes, which has two elements. This gives a concrete rejection test
for any proposed identification of arbitrary compact-open spinor-norm images with unit square
classes: such an identification requires hypotheses on the integral family and on the dimension.

## Main declarations

* `TauCeti.QuadraticMap.OrthogonalCompactOpens.topOfFinrankLeOne`: compatible compact-open data
  obtained from the full local point groups in dimension at most one.
* `TauCeti.QuadraticMap.exists_localSpinorNormImage_ne_unitSquareClasses`: a one-dimensional
  family whose local spinor-norm images differ from the unit square classes at every odd prime.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms* (1963), §§101–102.
-/

public section

namespace TauCeti
namespace QuadraticMap

open Filter
open _root_.QuadraticMap
open scoped TensorProduct Topology

noncomputable section

/-- The canonical invertibility witness for two over the rationals. -/
local instance lowRankInvertibleTwoRat : Invertible (2 : ℚ) :=
  invertibleOfNonzero two_ne_zero

/-- The canonical invertibility witness for two over a `p`-adic field. -/
local instance lowRankInvertibleTwoPadic (p : Nat.Primes) : Invertible (2 : ℚ_[p]) :=
  invertibleOfNonzero two_ne_zero

/-- A direct witness keeps the base-change dimension calculation within the deterministic
instance-search budget. -/
private theorem lowRankStrongRankConditionPadic (p : Nat.Primes) : StrongRankCondition ℚ_[p] := by
  let hfield : Field ℚ_[p] := @NormedField.toField _ (Padic.normedField (p : ℕ))
  exact @commRing_strongRankCondition _ hfield.toCommRing (@Field.toNontrivial _ hfield)

variable {V : Type*} [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V]

namespace OrthogonalCompactOpens

/-- In dimension at most one, taking the full local orthogonal and Spin groups gives compatible
compact-open reference data.

Nondegeneracy makes the form anisotropic in these dimensions, including after scalar extension.
Compactness therefore follows from the compactness criteria for the local orthogonal and Spin
groups. -/
def topOfFinrankLeOne (Q : QuadraticForm ℚ V) (hQ : Q.Nondegenerate)
    (hV : Module.finrank ℚ V ≤ 1) : OrthogonalCompactOpens Q where
  orthogonal _ := ⊤
  spin _ := ⊤
  isOpen_orthogonal _ := isOpen_univ
  isCompact_orthogonal p := by
    let _ : StrongRankCondition ℚ_[p] := lowRankStrongRankConditionPadic p
    have hQp : (Q.baseChange ℚ_[p]).Nondegenerate :=
      QuadraticForm.Nondegenerate.baseChange hQ
    have hVp : Module.finrank ℚ_[p] (ℚ_[p] ⊗[ℚ] V) ≤ 1 := by
      simpa only [Module.finrank_baseChange] using hV
    have hani := QuadraticForm.anisotropic_of_finrank_le_one (Q.baseChange ℚ_[p]) hQp hVp
    -- The full subgroup is `univ` in the group subtype; its image under subtype inclusion
    -- is the orthogonal group as a set of ambient linear equivalences.
    rw [Subgroup.coe_top,
      Topology.IsInducing.subtypeVal.isCompact_iff, Set.image_univ, Subtype.range_coe]
    exact isCompact_orthogonalGroup (Q.baseChange ℚ_[p]) hani
  isOpen_spin _ := isOpen_univ
  isCompact_spin p := by
    let _ : StrongRankCondition ℚ_[p] := lowRankStrongRankConditionPadic p
    have hQp : (Q.baseChange ℚ_[p]).Nondegenerate :=
      QuadraticForm.Nondegenerate.baseChange hQ
    have hVp : Module.finrank ℚ_[p] (ℚ_[p] ⊗[ℚ] V) ≤ 1 := by
      simpa only [Module.finrank_baseChange] using hV
    have hani := QuadraticForm.anisotropic_of_finrank_le_one (Q.baseChange ℚ_[p]) hQp hVp
    -- The full subgroup is `univ` in the group subtype; its image under subtype inclusion
    -- is the Spin group as a set of ambient Clifford units.
    rw [Subgroup.coe_top,
      Topology.IsInducing.subtypeVal.isCompact_iff, Set.image_univ, Subtype.range_coe,
      CliffordAlgebra.isCompact_spinGroup_iff (Q.baseChange ℚ_[p]) hQp]
    exact hani
  spin_maps _ _ _ := Subgroup.mem_top _
  eventually_orthogonal _ := .of_forall fun _ ↦ Subgroup.mem_top _
  eventually_spin _ := .of_forall fun _ ↦ Subgroup.mem_top _

/-- The low-rank reference family contains the full local orthogonal group. -/
@[simp]
theorem topOfFinrankLeOne_orthogonal (Q : QuadraticForm ℚ V) (hQ : Q.Nondegenerate)
    (hV : Module.finrank ℚ V ≤ 1) (p : Nat.Primes) :
    (topOfFinrankLeOne Q hQ hV).orthogonal p = ⊤ := (rfl)

/-- The low-rank reference family contains the full local Spin group. -/
@[simp]
theorem topOfFinrankLeOne_spin (Q : QuadraticForm ℚ V) (hQ : Q.Nondegenerate)
    (hV : Module.finrank ℚ V ≤ 1) (p : Nat.Primes) :
    (topOfFinrankLeOne Q hQ hV).spin p = ⊤ := (rfl)

/-- In dimension at most one, the local spinor-norm image of any compatible compact-open family
differs from the unit square classes at every prime. -/
theorem localSpinorNormImage_ne_unitSquareClasses_of_finrank_le_one
    {Q : QuadraticForm ℚ V} (U : OrthogonalCompactOpens Q) (hQ : Q.Nondegenerate)
    (hV : Module.finrank ℚ V ≤ 1) (p : Nat.Primes) :
    U.localSpinorNormImage hQ p ≠ unitSquareClasses ℚ_[p] := by
  rw [U.localSpinorNormImage_eq_bot_of_finrank_le_one hQ hV p]
  intro h
  have hc := card_unitSquareClasses ℚ_[p] two_ne_zero
  have hcard := congrArg
    (fun H : Subgroup (Multiplicative (SquareClassGroup ℚ_[p])) ↦ Nat.card H) h
  have hbot : Nat.card
      (⊥ : Subgroup (Multiplicative (SquareClassGroup ℚ_[p]))) = 1 := Subgroup.card_bot
  have hone := hbot.symm.trans (hcard.trans hc)
  omega

end OrthogonalCompactOpens

/-- There is a compatible compact-open family on a one-dimensional rational quadratic space whose
local spinor-norm image differs from the unit square classes at every odd prime. -/
theorem exists_localSpinorNormImage_ne_unitSquareClasses :
    ∃ (Q : QuadraticForm ℚ (Fin 1 → ℚ)) (hQ : Q.Nondegenerate)
      (U : OrthogonalCompactOpens Q),
      ∀ p : Nat.Primes, (p : ℕ) ≠ 2 →
        U.localSpinorNormImage hQ p ≠ unitSquareClasses ℚ_[p] := by
  let Q : QuadraticForm ℚ (Fin 1 → ℚ) :=
    QuadraticMap.weightedSumSquares ℚ (fun _ ↦ 1)
  have hQ : Q.Nondegenerate :=
    QuadraticMap.nondegenerate_weightedSumSquares fun _ ↦ isRegular_one
  have hV : Module.finrank ℚ (Fin 1 → ℚ) ≤ 1 := by simp
  let U := OrthogonalCompactOpens.topOfFinrankLeOne Q hQ hV
  exact ⟨Q, hQ, U, fun p _ ↦
    U.localSpinorNormImage_ne_unitSquareClasses_of_finrank_le_one hQ hV p⟩

end

end QuadraticMap
end TauCeti
