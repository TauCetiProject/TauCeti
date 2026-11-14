/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.SpecialLinear.StandardCarrier.LieGeneration
public import TauCeti.Algebra.Lie.Presentation.Serre
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.LieAlgebra.Basic
import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.SerrePresentation
import TauCeti.Algebra.Lie.Sl2.WeightString
import TauCeti.Algebra.Lie.SpecialLinear.Diagonal
import TauCeti.Algebra.Lie.GeneralLinear.Finrank
import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.LieAlgebra.Dimension

/-!
# Equivalence between the pinned type-A Lie algebra and the special linear Lie algebra

The adjacent matrix units of `SlStd` satisfy the type-A Serre relations. They therefore
supply an equivalence from the independently constructed pinned Lie algebra to the native
special linear Lie algebra, matching both signs of the numbered generators and the Cartan
generators. Adjacent-root generation gives surjectivity, and the root-space dimension count
gives injectivity.

This is the Lie-algebra input for regarding the standard integral lattice as a Chevalley
datum. It does not identify either integral group scheme or assert point generation.
The construction uses `TauCeti.serreLift`, `DynkinType.serreLiftEquiv`, and
`TauCeti.lieSpan_specialLinear_adjacent_single_eq_top`.

## References

* J.-P. Serre, *Complex Semisimple Lie Algebras*, Chapter VI, appendix.
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4–6*, Plate I.
-/

public section

open scoped Matrix

namespace TauCeti.SlStd

open LieAlgebra LieAlgebra.SpecialLinear

attribute [local instance 100] LieRing.ofAssociativeRing

variable (r : ℕ)

private theorem lie_cartan_cartan (i j : Fin r) :
    ⁅cartanGenerator r i, cartanGenerator r j⁆ = 0 := by
  have h (k : Fin r) : cartanGenerator r k = (specialLinearCorootBasis r ℚ k).val := by
    apply Subtype.ext
    simp
  rw [h i, h j]
  exact lie_specialLinearCoroot_eq_zero r ℚ i j

private theorem lie_raising_lowering_of_ne (i j : Fin r) (hij : i ≠ j) :
    ⁅rootGenerator r (.inl i), rootGenerator r (.inr j)⁆ = 0 := by
  apply Subtype.ext
  have hcs : i.castSucc ≠ j.castSucc := by simpa using hij
  have hs : i.succ ≠ j.succ := by simpa using hij
  simp [LieSubalgebra.coe_bracket, val_rootGenerator, Matrix.lie_single_single,
    hs, hcs.symm]

/-- The standard adjacent generators form a Serre system for the transposed type-A
Cartan matrix, with the same numbering as the pinned Lie algebra. -/
theorem isSerreSystem_rootGenerator :
    IsSerreSystem ℚ (CartanMatrix.A r)ᵀ (cartanGenerator r)
      (fun i => rootGenerator r (.inl i)) (fun i => rootGenerator r (.inr i)) where
  lie_H_H := lie_cartan_cartan r
  lie_E_F_self i := (isSl2Triple_rootGenerator r i).lie_e_f
  lie_E_F_of_ne := lie_raising_lowering_of_ne r
  lie_H_E i j := by
    simpa only [rootGeneratorWeight_inl, Int.cast_smul_eq_zsmul,
      Matrix.transpose_apply] using lie_cartanGenerator_rootGenerator r (.inl j) i
  lie_H_F i j := by
    simpa only [rootGeneratorWeight_inr, Int.cast_neg, neg_smul,
      Int.cast_smul_eq_zsmul, Matrix.transpose_apply] using
      lie_cartanGenerator_rootGenerator r (.inr j) i
  ad_pow_lie_E_E i j := by
    rcases eq_or_ne i j with rfl | hij
    · simp
    · rw [Matrix.transpose_apply]
      exact ad_pow_lie_eq_zero_of_isSl2Triple_of_lie_h_eq_smul_of_lie_f_eq_zero
        (isSl2Triple_rootGenerator r i)
        (by rw [lie_cartanGenerator_rootGenerator, rootGeneratorWeight_inl])
        (by rw [← lie_skew, lie_raising_lowering_of_ne r j i hij.symm, neg_zero])
  ad_pow_lie_F_F i j := by
    rcases eq_or_ne i j with rfl | hij
    · simp
    · rw [Matrix.transpose_apply]
      exact ad_pow_lie_eq_zero_of_isSl2Triple_of_lie_h_eq_smul_of_lie_f_eq_zero
        (isSl2Triple_rootGenerator r i).symm
        (by rw [neg_lie, lie_cartanGenerator_rootGenerator, rootGeneratorWeight_inr,
            Int.cast_neg, neg_smul, neg_neg])
        (lie_raising_lowering_of_ne r i j hij)

private theorem isSerreSystem_pinned :
    IsSerreSystem ℚ (DynkinType.A r).cartanMatrixᵀ (cartanGenerator r)
      (fun i => rootGenerator r (.inl i)) (fun i => rootGenerator r (.inr i)) := by
  simpa only [DynkinType.rank, DynkinType.cartanMatrix_A] using isSerreSystem_rootGenerator r

private noncomputable def pinnedLieHom (ht : (DynkinType.A r).Valid) :
    (DynkinType.A r).lieAlgebra ht →ₗ⁅ℚ⁆ sl (Fin (r + 1)) ℚ :=
  (serreLift (isSerreSystem_pinned r)).comp ((DynkinType.A r).serreLiftEquiv ht).symm.toLieHom

private theorem pinnedLieHom_surjective (ht : (DynkinType.A r).Valid) :
    Function.Surjective (pinnedLieHom r ht) := by
  exact (serreLift_surjective (isSerreSystem_pinned r) (lieSpan_rootGenerator_eq_top r)).comp
      ((DynkinType.A r).serreLiftEquiv ht).symm.surjective

private theorem pinnedLieHom_injective (ht : (DynkinType.A r).Valid) :
    Function.Injective (pinnedLieHom r ht) := by
  have hdim : Module.finrank ℚ ((DynkinType.A r).lieAlgebra ht) =
      Module.finrank ℚ (sl (Fin (r + 1)) ℚ) := by
    rw [DynkinType.finrank_lieAlgebra, DynkinType.rank_A, DynkinType.numRoots_A,
      finrank_sl, Fintype.card_fin]
    have h : (r + 1) ^ 2 = r + r * (r + 1) + 1 := by ring
    omega
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mpr
    (pinnedLieHom_surjective r ht)

/-- The pinned type-A Lie algebra is the native special linear algebra, via the map matching
its numbered raising, lowering and Cartan generators with the standard matrices. -/
noncomputable def pinnedLieEquiv (ht : (DynkinType.A r).Valid) :
    (DynkinType.A r).lieAlgebra ht ≃ₗ⁅ℚ⁆ sl (Fin (r + 1)) ℚ :=
  LieEquiv.ofBijective (pinnedLieHom r ht)
    ⟨pinnedLieHom_injective r ht, pinnedLieHom_surjective r ht⟩

/-- The pinned equivalence sends the numbered Cartan generators to diagonal differences. -/
@[simp]
theorem pinnedLieEquiv_lieBasis_h (ht : (DynkinType.A r).Valid) (i : Fin r) :
    pinnedLieEquiv r ht (((DynkinType.A r).lieBasis ht).h i) = cartanGenerator r i := by
  -- The equivalence has the underlying function of the Serre lift; use the explicitly
  -- instantiated generator equation because the two spellings of the rank impede rewriting.
  exact (congrArg (serreLift (isSerreSystem_pinned r))
    ((DynkinType.A r).serreLiftEquiv_symm_lieBasis_h ht i)).trans
      (serreLift_serreH (isSerreSystem_pinned r) i)

/-- The pinned equivalence sends raising generators to upper adjacent matrix units. -/
@[simp]
theorem pinnedLieEquiv_lieBasis_e (ht : (DynkinType.A r).Valid) (i : Fin r) :
    pinnedLieEquiv r ht (((DynkinType.A r).lieBasis ht).e i) = rootGenerator r (.inl i) := by
  -- As for the Cartan equation, instantiate the generator equation at the native rank.
  exact (congrArg (serreLift (isSerreSystem_pinned r))
    ((DynkinType.A r).serreLiftEquiv_symm_lieBasis_e ht i)).trans
      (serreLift_serreE (isSerreSystem_pinned r) i)

/-- The pinned equivalence sends lowering generators to lower adjacent matrix units. -/
@[simp]
theorem pinnedLieEquiv_lieBasis_f (ht : (DynkinType.A r).Valid) (i : Fin r) :
    pinnedLieEquiv r ht (((DynkinType.A r).lieBasis ht).f i) = rootGenerator r (.inr i) := by
  -- As for the Cartan equation, instantiate the generator equation at the native rank.
  exact (congrArg (serreLift (isSerreSystem_pinned r))
    ((DynkinType.A r).serreLiftEquiv_symm_lieBasis_f ht i)).trans
      (serreLift_serreF (isSerreSystem_pinned r) i)

/-- The inverse equivalence sends standard diagonal differences to the pinned Cartan generators. -/
@[simp]
theorem pinnedLieEquiv_symm_cartanGenerator (ht : (DynkinType.A r).Valid) (i : Fin r) :
    (pinnedLieEquiv r ht).symm (cartanGenerator r i) =
      ((DynkinType.A r).lieBasis ht).h i := by
  apply (pinnedLieEquiv r ht).injective
  simp

/-- The inverse equivalence sends upper adjacent units to the pinned raising generators. -/
@[simp]
theorem pinnedLieEquiv_symm_rootGenerator_inl (ht : (DynkinType.A r).Valid) (i : Fin r) :
    (pinnedLieEquiv r ht).symm (rootGenerator r (.inl i)) =
      ((DynkinType.A r).lieBasis ht).e i := by
  apply (pinnedLieEquiv r ht).injective
  simp

/-- The inverse equivalence sends lower adjacent units to the pinned lowering generators. -/
@[simp]
theorem pinnedLieEquiv_symm_rootGenerator_inr (ht : (DynkinType.A r).Valid) (i : Fin r) :
    (pinnedLieEquiv r ht).symm (rootGenerator r (.inr i)) =
      ((DynkinType.A r).lieBasis ht).f i := by
  apply (pinnedLieEquiv r ht).injective
  simp

end TauCeti.SlStd
