/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.SpecialLinear.StandardCarrier.Basic
public import TauCeti.Algebra.Lie.Presentation.Serre
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.LieAlgebra.Basic
import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.SerrePresentation
import TauCeti.Algebra.Lie.SpecialLinear.Root.Generation
import TauCeti.Algebra.Lie.GeneralLinear.Finrank
import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.LieAlgebra.Dimension

/-!
# The pinned type-A Lie algebra on the standard module

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
  apply Subtype.ext
  simp only [LieSubalgebra.coe_bracket, val_cartanGenerator, ZeroMemClass.coe_zero]
  exact lie_eq_zero_of_isDiag
    (mem_diagonalCartan_iff_isDiag.mp
      (sub_mem (single_self_mem_diagonalCartan i.castSucc 1)
        (single_self_mem_diagonalCartan i.succ 1)))
    (mem_diagonalCartan_iff_isDiag.mp
      (sub_mem (single_self_mem_diagonalCartan j.castSucc 1)
        (single_self_mem_diagonalCartan j.succ 1)))

private theorem lie_raising_lowering_of_ne (i j : Fin r) (hij : i ≠ j) :
    ⁅rootGenerator r (.inl i), rootGenerator r (.inr j)⁆ = 0 := by
  apply Subtype.ext
  have hcs : i.castSucc ≠ j.castSucc := by simpa using hij
  have hs : i.succ ≠ j.succ := by simpa using hij
  simp [LieSubalgebra.coe_bracket, val_rootGenerator, Matrix.lie_single_single,
    hs, hcs.symm]

private theorem lie_raising_raising_of_not_adjacent (i j : Fin r)
    (hij : i.val + 1 ≠ j.val) (hji : j.val + 1 ≠ i.val) :
    ⁅rootGenerator r (.inl i), rootGenerator r (.inl j)⁆ = 0 := by
  apply Subtype.ext
  have h₁ : i.succ ≠ j.castSucc := by simpa [Fin.ext_iff] using hij
  have h₂ : j.succ ≠ i.castSucc := by simpa [Fin.ext_iff] using hji
  simp [LieSubalgebra.coe_bracket, val_rootGenerator, Matrix.lie_single_single, h₁, h₂]

private theorem lie_raising_raising_twice (i j : Fin r) :
    ⁅rootGenerator r (.inl i), ⁅rootGenerator r (.inl i), rootGenerator r (.inl j)⁆⁆ = 0 := by
  apply Subtype.ext
  simp only [LieSubalgebra.coe_bracket, val_rootGenerator, rootTarget_inl, rootSource_inl,
    Matrix.lie_single_single, ZeroMemClass.coe_zero]
  have hi : i.succ ≠ i.castSucc := (Fin.castSucc_lt_succ (i := i)).ne'
  split_ifs <;> simp_all [lie_sub, Matrix.lie_single_single]
  · have h₁ : i.val + 1 = j.val := congrArg Fin.val ‹i.succ = j.castSucc›
    have h₂ : j.val + 1 = i.val := congrArg Fin.val ‹j.succ = i.castSucc›
    omega

private theorem lie_lowering_lowering_of_not_adjacent (i j : Fin r)
    (hij : i.val + 1 ≠ j.val) (hji : j.val + 1 ≠ i.val) :
    ⁅rootGenerator r (.inr i), rootGenerator r (.inr j)⁆ = 0 := by
  apply Subtype.ext
  have h₁ : i.castSucc ≠ j.succ := by simpa [Fin.ext_iff, eq_comm] using hji
  have h₂ : j.castSucc ≠ i.succ := by simpa [Fin.ext_iff, eq_comm] using hij
  simp [LieSubalgebra.coe_bracket, val_rootGenerator, Matrix.lie_single_single, h₁, h₂]

private theorem lie_lowering_lowering_twice (i j : Fin r) :
    ⁅rootGenerator r (.inr i), ⁅rootGenerator r (.inr i), rootGenerator r (.inr j)⁆⁆ = 0 := by
  apply Subtype.ext
  simp only [LieSubalgebra.coe_bracket, val_rootGenerator, rootTarget_inr, rootSource_inr,
    Matrix.lie_single_single, ZeroMemClass.coe_zero]
  have hi : i.castSucc ≠ i.succ := (Fin.castSucc_lt_succ (i := i)).ne
  split_ifs <;> simp_all [lie_sub, Matrix.lie_single_single]
  · have h₁ : i.val = j.val + 1 := congrArg Fin.val ‹i.castSucc = j.succ›
    have h₂ : j.val = i.val + 1 := congrArg Fin.val ‹j.castSucc = i.succ›
    omega

/-- The standard adjacent generators form a Serre system for the transposed type-A
Cartan matrix, with the same numbering as the pinned Lie algebra. -/
theorem isSerreSystem :
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
    by_cases h : i = j
    · subst j
      simp
    · simp only [Matrix.transpose_apply, CartanMatrix.A, Matrix.of_apply]
      split_ifs with heq hadj
      · exact (h heq.symm).elim
      · simpa using lie_raising_raising_twice r i j
      · simp only [neg_zero, Int.toNat_zero, pow_zero, one_apply_eq_self]
        exact lie_raising_raising_of_not_adjacent r i j (by omega) (by omega)
  ad_pow_lie_F_F i j := by
    by_cases h : i = j
    · subst j
      simp
    · simp only [Matrix.transpose_apply, CartanMatrix.A, Matrix.of_apply]
      split_ifs with heq hadj
      · exact (h heq.symm).elim
      · simpa using lie_lowering_lowering_twice r i j
      · simp only [neg_zero, Int.toNat_zero, pow_zero, one_apply_eq_self]
        exact lie_lowering_lowering_of_not_adjacent r i j (by omega) (by omega)

private theorem isSerreSystem_pinned :
    IsSerreSystem ℚ (DynkinType.A r).cartanMatrixᵀ (cartanGenerator r)
      (fun i => rootGenerator r (.inl i)) (fun i => rootGenerator r (.inr i)) := by
  simpa only [DynkinType.rank, DynkinType.cartanMatrix_A] using isSerreSystem r

private theorem lieSpan_rootGenerator :
    LieSubalgebra.lieSpan ℚ (sl (Fin (r + 1)) ℚ)
      (Set.range (fun i => rootGenerator r (.inl i)) ∪
        Set.range (fun i => rootGenerator r (.inr i))) = ⊤ := by
  have he : (fun i : Fin r => rootGenerator r (.inl i)) = fun i =>
      single i.castSucc i.succ (Fin.castSucc_lt_succ (i := i)).ne (1 : ℚ) := by
    funext i
    apply Subtype.ext
    simp
  have hf : (fun i : Fin r => rootGenerator r (.inr i)) = fun i =>
      single i.succ i.castSucc (Fin.castSucc_lt_succ (i := i)).ne' (1 : ℚ) := by
    funext i
    apply Subtype.ext
    simp
  rw [he, hf]
  exact lieSpan_specialLinear_adjacent_single_eq_top r ℚ

private noncomputable def pinnedLieHom (ht : (DynkinType.A r).Valid) :
    (DynkinType.A r).lieAlgebra ht →ₗ⁅ℚ⁆ sl (Fin (r + 1)) ℚ :=
  (serreLift (isSerreSystem_pinned r)).comp ((DynkinType.A r).serreLiftEquiv ht).symm.toLieHom

private theorem pinnedLieHom_surjective (ht : (DynkinType.A r).Valid) :
    Function.Surjective (pinnedLieHom r ht) := by
  exact (serreLift_surjective (isSerreSystem_pinned r) (lieSpan_rootGenerator r)).comp
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
theorem pinnedLieEquiv_h (ht : (DynkinType.A r).Valid) (i : Fin r) :
    pinnedLieEquiv r ht (((DynkinType.A r).lieBasis ht).h i) = cartanGenerator r i := by
  -- The equivalence has the underlying function of the Serre lift; use the explicitly
  -- instantiated generator equation because the two spellings of the rank impede rewriting.
  exact (congrArg (serreLift (isSerreSystem_pinned r))
    ((DynkinType.A r).serreLiftEquiv_symm_lieBasis_h ht i)).trans
      (serreLift_serreH (isSerreSystem_pinned r) i)

/-- The pinned equivalence sends raising generators to upper adjacent matrix units. -/
@[simp]
theorem pinnedLieEquiv_e (ht : (DynkinType.A r).Valid) (i : Fin r) :
    pinnedLieEquiv r ht (((DynkinType.A r).lieBasis ht).e i) = rootGenerator r (.inl i) := by
  -- As for the Cartan equation, instantiate the generator equation at the native rank.
  exact (congrArg (serreLift (isSerreSystem_pinned r))
    ((DynkinType.A r).serreLiftEquiv_symm_lieBasis_e ht i)).trans
      (serreLift_serreE (isSerreSystem_pinned r) i)

/-- The pinned equivalence sends lowering generators to lower adjacent matrix units. -/
@[simp]
theorem pinnedLieEquiv_f (ht : (DynkinType.A r).Valid) (i : Fin r) :
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
