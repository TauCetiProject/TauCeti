/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.LowerCentralSeries.Graded.Basic
public import Mathlib.Topology.Algebra.Group.TopologicalAbelianization

/-!
# The degree-zero graded piece and topological abelianization

The degree-zero piece of the closed lower central series is the quotient by the closure of the
commutator subgroup. This file identifies it, as a topological additive group, with Mathlib's
topological abelianization. The equivalence sends the class of an element to its abelianization
class, so computations in the first graded piece can use the usual quotient API.
-/

public section

namespace TauCeti

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The zero-th graded piece of the closed lower central series, with its quotient topology,
is the topological abelianization of `G` in additive notation. -/
noncomputable def lcsGradedPieceZeroEquiv :
    gradedPiece 0 G 0 ≃ₜ+ Additive (TopologicalAbelianization G) := by
  let e : gradedPiece 0 G 0 ≃+ Additive (TopologicalAbelianization G) :=
    (gradedPieceZeroEquiv 0 G).trans
      (QuotientGroup.quotientMulEquivOfEq (pLowerCentralSeries_one_zero (G := G))).toAdditive
  have he : Continuous e := by
    apply (QuotientGroup.isQuotientMap_mk
      ((pLowerCentralSeries 0 G 1).subgroupOf (pLowerCentralSeries 0 G 0))).continuous_iff.mpr
    have h : Continuous (fun x : pLowerCentralSeries 0 G 0 =>
        Additive.ofMul ((x : G) : TopologicalAbelianization G)) := by
      exact continuous_quotient_mk'.comp continuous_subtype_val
    convert h using 1
    funext x
    -- The source quotient is written additively, while its quotient map is multiplicative.
    change e (Additive.ofMul (QuotientGroup.mk x)) = _
    rw [← gradedMk_def 0 x]
    simp [e, QuotientGroup.quotientMulEquivOfEq_mk]
  have hmk : Continuous (gradedMkZero 0 G) := continuous_gradedMkZero
  have heval (g : G) : e (gradedMkZero 0 G g) = Additive.ofMul
      (g : TopologicalAbelianization G) := by
    simp [e, gradedPieceZeroEquiv_gradedMkZero,
      QuotientGroup.quotientMulEquivOfEq_mk]
  have heinv : Continuous e.symm := by
    apply (QuotientGroup.isQuotientMap_mk (commutator G).topologicalClosure).continuous_iff.mpr
    convert hmk using 1
    funext g
    -- The abelianization is a multiplicative quotient inside the additive target.
    change e.symm (Additive.ofMul (QuotientGroup.mk g)) = gradedMkZero 0 G g
    apply e.injective
    rw [e.apply_symm_apply, heval]
  exact ⟨e, he, heinv⟩

/-- The degree-zero equivalence sends the class of `g` to the class of `g` in the topological
abelianization. -/
@[simp]
theorem lcsGradedPieceZeroEquiv_mk (g : G) :
    lcsGradedPieceZeroEquiv (G := G) (gradedMkZero 0 G g) =
      Additive.ofMul (g : TopologicalAbelianization G) := by
  -- Reduce the constructed topological equivalence to its underlying quotient equivalence.
  change ((gradedPieceZeroEquiv 0 G).trans
    (QuotientGroup.quotientMulEquivOfEq (pLowerCentralSeries_one_zero (G := G))).toAdditive)
      (gradedMkZero 0 G g) = _
  simp [gradedPieceZeroEquiv_gradedMkZero, QuotientGroup.quotientMulEquivOfEq_mk]

/-- The inverse equivalence sends an abelianization class to its degree-zero graded class. -/
@[simp]
theorem lcsGradedPieceZeroEquiv_symm_mk (g : G) :
    (lcsGradedPieceZeroEquiv (G := G)).symm
      (Additive.ofMul (g : TopologicalAbelianization G)) = gradedMkZero 0 G g := by
  apply lcsGradedPieceZeroEquiv (G := G).injective
  simp

end TauCeti
