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
needed to propagate an invariant coordinate line throughout its half-spin summand. Conversely, a
positive numbered root matrix has no entries other than these moves, since spin weights pair with
simple coroots in `{-1, 0, 1}`.

## Main declarations

* `TauCeti.TypeDSpinCarrier.basisReflection`: a simple reflection on finite-ordinal spin-basis
  indices.
* `TauCeti.TypeDSpinCarrier.exists_rootSubgroupPoints_inl_mulVec_single_sub` and its negative
  counterpart: the root subgroup move of a coordinate vector.
* `TauCeti.TypeDSpinCarrier.rootIntMatrix_inl_eq_zero_of_ne_basisReflection`: a positive numbered
  root matrix is supported on the raising moves.

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

/-- The `i`-th simple reflection on the finite-ordinal spin-basis indices. -/
noncomputable def basisReflection (i : Fin n) (a : Fin (dimension n)) : Fin (dimension n) :=
  Fintype.equivFin (Finset (Fin n)) (DynkinType.typeDSpinReflection i (signSet n a))

/-- Enumerating a reflected basis index recovers the reflected sign set. -/
@[simp]
theorem signSet_basisReflection (i : Fin n) (a : Fin (dimension n)) :
    signSet n (basisReflection n i a) = DynkinType.typeDSpinReflection i (signSet n a) := by
  simp [basisReflection, signSet]

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
  refine ⟨1, fun u => rootSubgroupPoints_mulVec_single_sub_of_eq n hn (.inl i) ?_ A u⟩
  simpa only [TauCeti.serreRootGenerator_inl, coe_latticeBasis, ha', one_smul] using
    (polarization n).typeDSpinRep_serreE_exteriorBasis
      (polarizationBasis n) hn i (signSet n a) ha

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
  refine ⟨1, fun u => rootSubgroupPoints_mulVec_single_sub_of_eq n hn (.inr i) ?_ A u⟩
  simpa only [TauCeti.serreRootGenerator_inr, coe_latticeBasis, ha', one_smul] using
    (polarization n).typeDSpinRep_serreF_exteriorBasis
      (polarizationBasis n) hn i (signSet n a) ha

/-- **A positive numbered root matrix only raises along simple reflections.** Its column at a
spin-basis index whose weight pairs to `-1` with the simple coroot is supported at the reflected
index, and every other column vanishes, since spin weights pair with simple coroots in
`{-1, 0, 1}`. -/
theorem rootIntMatrix_inl_eq_zero_of_ne_basisReflection (i : Fin n)
    {a b : Fin (dimension n)} (h : basisWeight n b i = -1 → a ≠ basisReflection n i b) :
    rootIntMatrix n hn (.inl i) a b = 0 := by
  have hpair (c : Fin (dimension n)) :
      basisWeight n c i = -1 ∨ basisWeight n c i = 0 ∨ basisWeight n c i = 1 :=
    DynkinType.typeDSpinWeight_apply_eq_neg_one_or_eq_zero_or_eq_one (signSet n c) i
  rcases hpair b with hneg | hb | hb
  · have hc : rep n hn (_root_.UniversalEnvelopingAlgebra.ι ℚ
          (TauCeti.serreRootGenerator (CartanMatrix.D n) (.inl i)))
          (latticeBasis n b : ExteriorAlgebra ℚ (polarization n).W) =
        (1 : ℤˣ) • (latticeBasis n (basisReflection n i b) :
          ExteriorAlgebra ℚ (polarization n).W) := by
      simpa only [TauCeti.serreRootGenerator_inl, coe_latticeBasis, signSet_basisReflection,
        one_smul] using
        (polarization n).typeDSpinRep_serreE_exteriorBasis
          (polarizationBasis n) hn i (signSet n b) hneg
    rw [rootIntMatrix_apply_of_eq n hn (.inl i) hc a, ite_eq_right (h hneg)]
  all_goals
    apply rootIntMatrix_eq_zero_of_weight_ne
    intro hw
    have hi := congrFun hw i
    rw [Pi.sub_apply, TypeDStd.rootGeneratorWeight_inl, CartanMatrix.D_diag] at hi
    rcases hpair a with ha | ha | ha <;> omega

end TauCeti.TypeDSpinCarrier
