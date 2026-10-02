/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Orthogonal.TypeD.SpinCarrier.IntegralMatrix
public import TauCeti.RepresentationTheory.Spin.Polarization.TypeD.RootBasis

/-!
# Root subgroup moves on the type-D spin coordinate basis

The root subgroup at a simple root moves a coordinate vector of coroot weight `-1` by a
signed multiple of its reflected coordinate vector. The negative root subgroup does the same
at weight `1`. The coefficient is the parameter times an integral unit, over any commutative
ring. In particular, parameter one gives a nonzero move over every field, including
characteristic two.

These formulas transfer the polarized spin-basis calculations to the integral matrix carrier.
Together with the two parity orbits of `typeDSpinReflection`, they provide the root moves
needed to propagate an invariant coordinate line throughout its half-spin summand.

## References

* C. Chevalley, *The Algebraic Theory of Spinors*, Chapter II.
* The matrix-to-coordinate calculation follows
  `TauCeti.Algebra.Lie.Orthogonal.TypeB.SpinCarrier.StandardComodule`.
-/

public section

open Multiplicative
open scoped Matrix

namespace TauCeti.TypeDSpinCarrier

universe v

variable (n : ℕ) (hn : 4 ≤ n)

/-- A signed root-generator column gives the root subgroup's displacement of the corresponding
coordinate vector, at every parameter over every commutative ring. -/
theorem rootSubgroupPoints_mulVec_single_sub_of_eq (j : Fin n ⊕ Fin n)
    {a a' : Fin (dimension n)} {c : ℤˣ}
    (h : rep n hn (_root_.UniversalEnvelopingAlgebra.ι ℚ
        (TauCeti.serreRootGenerator (CartanMatrix.D n) j))
        (latticeBasis n a : ExteriorAlgebra ℚ (polarization n).W) =
      c • (latticeBasis n a' : ExteriorAlgebra ℚ (polarization n).W))
    (A : Type v) [CommRing A] (u : Multiplicative A) :
    ((rootSubgroupPoints n hn j A u :
        Matrix.GeneralLinearGroup (Fin (dimension n)) A) :
          Matrix (Fin (dimension n)) (Fin (dimension n)) A) *ᵥ Pi.single a 1 -
        Pi.single a 1 =
      (toAdd u * ((c : ℤ) : A)) • Pi.single a' 1 := by
  rw [coe_rootSubgroupPoints_eq_one_add_smul, Matrix.add_mulVec, Matrix.one_mulVec,
    add_sub_cancel_left, Matrix.smul_mulVec, Matrix.mulVec_single_one]
  funext r
  simp [rootIntMatrix_apply_of_eq n hn j h, Pi.single_apply]

/-- At simple-coroot weight `-1`, the positive root subgroup moves a spin coordinate vector
by the reflected coordinate vector, with a fixed integral-unit sign at every parameter. -/
theorem exists_rootSubgroupPoints_inl_mulVec_single_sub (i : Fin n)
    {a a' : Fin (dimension n)} (ha : basisWeight n a i = -1)
    (ha' : DynkinType.typeDSpinReflection i (signSet n a) = signSet n a')
    (A : Type v) [CommRing A] :
    ∃ c : ℤˣ, ∀ u : Multiplicative A,
      ((rootSubgroupPoints n hn (.inl i) A u :
          Matrix.GeneralLinearGroup (Fin (dimension n)) A) :
            Matrix (Fin (dimension n)) (Fin (dimension n)) A) *ᵥ Pi.single a 1 -
          Pi.single a 1 =
        (toAdd u * ((c : ℤ) : A)) • Pi.single a' 1 := by
  obtain ⟨c, hc⟩ := (polarization n).exists_typeDSpinRep_serreE_exteriorBasis
    (polarizationBasis n) hn i (signSet n a) ha
  refine ⟨c, fun u => rootSubgroupPoints_mulVec_single_sub_of_eq n hn (.inl i) ?_ A u⟩
  simpa only [TauCeti.serreRootGenerator_inl, coe_latticeBasis, ha'] using hc

/-- At simple-coroot weight `1`, the negative root subgroup moves a spin coordinate vector
by the reflected coordinate vector, with a fixed integral-unit sign at every parameter. -/
theorem exists_rootSubgroupPoints_inr_mulVec_single_sub (i : Fin n)
    {a a' : Fin (dimension n)} (ha : basisWeight n a i = 1)
    (ha' : DynkinType.typeDSpinReflection i (signSet n a) = signSet n a')
    (A : Type v) [CommRing A] :
    ∃ c : ℤˣ, ∀ u : Multiplicative A,
      ((rootSubgroupPoints n hn (.inr i) A u :
          Matrix.GeneralLinearGroup (Fin (dimension n)) A) :
            Matrix (Fin (dimension n)) (Fin (dimension n)) A) *ᵥ Pi.single a 1 -
          Pi.single a 1 =
        (toAdd u * ((c : ℤ) : A)) • Pi.single a' 1 := by
  obtain ⟨c, hc⟩ := (polarization n).exists_typeDSpinRep_serreF_exteriorBasis
    (polarizationBasis n) hn i (signSet n a) ha
  refine ⟨c, fun u => rootSubgroupPoints_mulVec_single_sub_of_eq n hn (.inr i) ?_ A u⟩
  simpa only [TauCeti.serreRootGenerator_inr, coe_latticeBasis, ha'] using hc

end TauCeti.TypeDSpinCarrier
