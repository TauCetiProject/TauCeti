/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Orthogonal.TypeD.SpinCarrier.Basic
public import TauCeti.Algebra.Lie.Orthogonal.TypeD.Pinned
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.KostantForm
import TauCeti.RepresentationTheory.Spin.Polarization.TypeD.Representation

/-!
# The admissible spin lattice for the pinned type-D algebra

Pull the native orthogonal spin action back along `TypeDStd.pinnedLieEquiv` to the independently
constructed pinned rational Lie algebra. The existing exterior coordinate lattice remains stable
under its Kostant form, and its basis retains the same integral weights. Both signs of every
numbered simple root act by the original spin operators, including the two fork nodes.

This supplies the action and admissibility inputs for realizing Chevalley data on the full spin
module, without replacing that module or its integral lattice. No faithfulness or identification
of group schemes is asserted here.

The construction uses `TypeDStd.pinnedLieEquiv`, the native orthogonal spin representation, and
`TypeDSpinCarrier.rep` with its Kostant-stable lattice and weight basis. Stability follows from
`UniversalEnvelopingAlgebra.kostantForm_apply_mem` and agreement of the generator operators.

## References

* C. Chevalley, *The Algebraic Theory of Spinors*, Chapter II.
* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 2.
* N. Bourbaki, *Lie Groups and Lie Algebras*, Chapters 4--6, Plate IV.
-/

public section

namespace TauCeti.TypeDSpinCarrier

open TauCeti.UniversalEnvelopingAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing
attribute [local instance] TauCeti.moduleNNRat

noncomputable section

variable (n : ℕ) (hn : 4 ≤ n)

/-- The full spin representation of the pinned rational type-D Lie algebra, extended to its
universal enveloping algebra. The exterior module and lattice are unchanged. -/
def pinnedRep :
    _root_.UniversalEnvelopingAlgebra ℚ
        ((DynkinType.D n).lieAlgebra (DynkinType.valid_D.mpr hn)) →ₐ[ℚ]
      Module.End ℚ (ExteriorAlgebra ℚ (polarization n).W) :=
  _root_.UniversalEnvelopingAlgebra.lift ℚ
    (((polarization n).typeDSpinLieRep (polarizationBasis n)
      (splitEvenPolarization_line ℚ n)).comp (TypeDStd.pinnedLieEquiv n hn).toLieHom)

/-- An included pinned Lie element acts by its native orthogonal spin operator. -/
theorem pinnedRep_ι (x : (DynkinType.D n).lieAlgebra (DynkinType.valid_D.mpr hn)) :
    pinnedRep n hn (_root_.UniversalEnvelopingAlgebra.ι ℚ x) =
      (polarization n).typeDSpinLieRep (polarizationBasis n)
        (splitEvenPolarization_line ℚ n) (TypeDStd.pinnedLieEquiv n hn x) := by
  rw [pinnedRep, _root_.UniversalEnvelopingAlgebra.lift_ι_apply,
    LieHom.comp_apply, LieEquiv.coe_toLieHom]

/-- A pinned Cartan generator acts by the original spin Cartan operator. -/
@[simp↓]
theorem pinnedRep_ι_h (i : Fin n) :
    pinnedRep n hn (_root_.UniversalEnvelopingAlgebra.ι ℚ
        (((DynkinType.D n).lieBasis (DynkinType.valid_D.mpr hn)).h i)) =
      rep n hn (_root_.UniversalEnvelopingAlgebra.ι ℚ
        (TauCeti.serreH ℚ (CartanMatrix.D n) i)) := by
  rw [pinnedRep_ι, TypeDStd.pinnedLieEquiv_lieBasis_h,
    SpinPolarizationData.typeDSpinLieRep_apply,
    SpinPolarizationData.typeDQuadraticEquiv_cartanGenerator]
  simp only [rep, SpinPolarizationData.typeDSpinRep_ι,
    SpinPolarizationData.typeDSpinSerreRepresentation_serreH]

/-- A pinned raising generator acts by the original spin raising operator. -/
@[simp↓]
theorem pinnedRep_ι_e (i : Fin n) :
    pinnedRep n hn (_root_.UniversalEnvelopingAlgebra.ι ℚ
        (((DynkinType.D n).lieBasis (DynkinType.valid_D.mpr hn)).e i)) =
      rep n hn (_root_.UniversalEnvelopingAlgebra.ι ℚ
        (TauCeti.serreE ℚ (CartanMatrix.D n) i)) := by
  rw [pinnedRep_ι, TypeDStd.pinnedLieEquiv_lieBasis_e,
    SpinPolarizationData.typeDSpinLieRep_apply,
    SpinPolarizationData.typeDQuadraticEquiv_rootGenerator]
  simp only [rep, SpinPolarizationData.typeDSpinRep_ι,
    SpinPolarizationData.typeDSpinSerreRepresentation_serreE]

/-- A pinned lowering generator acts by the original spin lowering operator. -/
@[simp↓]
theorem pinnedRep_ι_f (i : Fin n) :
    pinnedRep n hn (_root_.UniversalEnvelopingAlgebra.ι ℚ
        (((DynkinType.D n).lieBasis (DynkinType.valid_D.mpr hn)).f i)) =
      rep n hn (_root_.UniversalEnvelopingAlgebra.ι ℚ
        (TauCeti.serreF ℚ (CartanMatrix.D n) i)) := by
  rw [pinnedRep_ι, TypeDStd.pinnedLieEquiv_lieBasis_f,
    SpinPolarizationData.typeDSpinLieRep_apply,
    SpinPolarizationData.typeDQuadraticEquiv_rootGenerator]
  simp only [rep, SpinPolarizationData.typeDSpinRep_ι,
    SpinPolarizationData.typeDSpinSerreRepresentation_serreF]

/-- Both signs of a pinned simple root act by the native numbered spin root operator. -/
@[simp↓]
theorem pinnedRep_ι_rootGenerator (i : Fin n ⊕ Fin n) :
    pinnedRep n hn (_root_.UniversalEnvelopingAlgebra.ι ℚ
        (((DynkinType.D n).lieBasis (DynkinType.valid_D.mpr hn)).rootGenerator i)) =
      rep n hn (_root_.UniversalEnvelopingAlgebra.ι ℚ
        (TauCeti.serreRootGenerator (CartanMatrix.D n) i)) := by
  -- The signed generator family of the pinned basis uses the definitionally equal rank of D n.
  cases i with
  | inl i =>
    erw [LieAlgebra.Basis.rootGenerator_inl, pinnedRep_ι_e]
    rw [TauCeti.serreRootGenerator_inl]
  | inr i =>
    erw [LieAlgebra.Basis.rootGenerator_inr, pinnedRep_ι_f]
    rw [TauCeti.serreRootGenerator_inr]

/-- The pinned Kostant form preserves the existing integral exterior coordinate lattice. -/
theorem pinnedRep_kostantForm_mem_lattice
    (u : _root_.UniversalEnvelopingAlgebra ℚ
      ((DynkinType.D n).lieAlgebra (DynkinType.valid_D.mpr hn)))
    (hu : u ∈ kostantForm
      ((DynkinType.D n).lieBasis (DynkinType.valid_D.mpr hn)).rootGenerator
      ((DynkinType.D n).lieBasis (DynkinType.valid_D.mpr hn)).h)
    (v : ExteriorAlgebra ℚ (polarization n).W) (hv : v ∈ lattice n) :
    pinnedRep n hn u v ∈ lattice n := by
  refine kostantForm_apply_mem _ _ (pinnedRep n hn) (lattice n)
    (fun i k v hv => ?_) (fun i k v hv => ?_) u hu hv
  · -- Agreement on root operators also gives agreement on all their divided powers.
    erw [Associative.map_dividedPower, pinnedRep_ι_rootGenerator,
      ← Associative.map_dividedPower]
    exact rep_kostantForm_mem_lattice n hn _
      (dividedPower_mem_kostantForm _ _ i k) v hv
  · -- Cartan binomial operators, rather than just Cartan generators, must preserve the lattice.
    erw [Ring.map_choose, pinnedRep_ι_h, ← Ring.map_choose]
    exact rep_kostantForm_mem_lattice n hn _
      (ringChoose_mem_kostantForm _ _ i k) v hv

/-- Every pinned simple-root operator on the full spin module is nilpotent. -/
theorem isNilpotent_pinnedRep_rootGenerator (i : Fin n ⊕ Fin n) :
    IsNilpotent (pinnedRep n hn (_root_.UniversalEnvelopingAlgebra.ι ℚ
      (((DynkinType.D n).lieBasis (DynkinType.valid_D.mpr hn)).rootGenerator i))) := by
  rw [pinnedRep_ι_rootGenerator]
  exact isNilpotent_rep_rootGenerator n hn i

/-- The exterior lattice basis has the same integral fundamental-weight coordinates for the
pinned Cartan action as for the original Serre action. -/
theorem isCartanWeightVector_pinnedRep_latticeBasis (i : Fin (dimension n)) :
    IsCartanWeightVector ((DynkinType.D n).lieBasis (DynkinType.valid_D.mpr hn)).h
      (pinnedRep n hn) (basisWeight n i)
      ((latticeBasis n i : (lattice n).toAddSubgroup) :
        ExteriorAlgebra ℚ (polarization n).W) := by
  -- The pinned Cartan and the spin weights use definitionally equal rank index types.
  erw [isCartanWeightVector_iff]
  intro j
  erw [pinnedRep_ι_h]
  exact (isCartanWeightVector_iff _ _).mp
    (isCartanWeightVector_latticeBasis n hn i) j

end

end TauCeti.TypeDSpinCarrier
