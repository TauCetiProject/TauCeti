/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.F4.ShortRoot.Modular.Matrix

/-!
# Divided adjoint squares on the modular F₄ short-root ideal

The second adjoint divided power is formed on the integral Chevalley lattice before reduction
modulo two. This file identifies its base change with the integral divided-square matrices used
in the pinned twenty-six-dimensional representation.

## References

* R. Steinberg, *Endomorphisms of linear algebraic groups*, Memoirs AMS 80 (1968), §11, for the
  special isogeny in characteristic two and its divided-power formulas.
* R. W. Carter, *Simple Groups of Lie Type*, §§4.4 and 12.3, for the divided powers of the
  adjoint action on a Chevalley lattice.
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate VIII, for the root
  coordinates and the simple-root numbering.
-/

public section

namespace TauCeti.DynkinType

open _root_.LieAlgebra _root_.LieAlgebra.IsKilling LieModule
open scoped TensorProduct
open TauCeti.F4ShortRoot

noncomputable section

/-- The second divided adjoint power of a signed simple root on the integral Chevalley lattice. -/
noncomputable def f4IntegralDividedAdjointSquare (k : Fin 4 ⊕ Fin 4) :
    Module.End ℤ f4ChevalleyLieLattice :=
  integralDividedPower
    (ad ℚ (F4.lieAlgebra valid_F4)
      (f4ChevalleyRootVector (f4KillingRoot (f4SignedSimpleRootIndex k))))
    f4ChevalleyLieLattice 2 (by
      intro y hy
      rw [Associative.dividedPower_def, Module.End.smul_def]
      exact IsChevalleySystem.inv_factorial_smul_ad_pow_mem_chevalleyLieLattice
        f4ChevalleyRootVector_isChevalleySystem
        (f4KillingRoot (f4SignedSimpleRootIndex k)) 2 hy)

/-- The integral divided square acts in the ambient Lie algebra by the second divided adjoint
power. -/
@[simp] theorem coe_f4IntegralDividedAdjointSquare_apply
    (k : Fin 4 ⊕ Fin 4) (y : f4ChevalleyLieLattice) :
    ((f4IntegralDividedAdjointSquare k y : f4ChevalleyLieLattice) :
      F4.lieAlgebra valid_F4) =
        Associative.dividedPower 2
          (ad ℚ (F4.lieAlgebra valid_F4)
            (f4ChevalleyRootVector (f4KillingRoot (f4SignedSimpleRootIndex k)))) •
          (y : F4.lieAlgebra valid_F4) := by
  rw [f4IntegralDividedAdjointSquare, coe_integralDividedPower_apply]

/-- The integral divided square has the expected exceptional opposite-root column. -/
theorem f4IntegralDividedAdjointSquare_rootVector_opposite (k : Fin 4 ⊕ Fin 4) :
    f4IntegralDividedAdjointSquare k
        (f4IntegralRootVector (f4OppositeRootIndex (f4SignedSimpleRootIndex k))) =
      -f4IntegralRootVector (f4SignedSimpleRootIndex k) := by
  apply Subtype.ext
  rw [coe_f4IntegralDividedAdjointSquare_apply, coe_f4IntegralRootVector]
  rw [NegMemClass.coe_neg, coe_f4IntegralRootVector]
  exact f4_dividedPower_two_ad_rootVector_opposite (f4SignedSimpleRootIndex k)

/-- The integral divided square vanishes on every other short-root column. -/
theorem f4IntegralDividedAdjointSquare_rootVector_eq_zero_of_short
    (k : Fin 4 ⊕ Fin 4) (i : Fin 48) (hi : f4Length i = 1)
    (hopp : i ≠ f4OppositeRootIndex (f4SignedSimpleRootIndex k)) :
    f4IntegralDividedAdjointSquare k (f4IntegralRootVector i) = 0 := by
  apply Subtype.ext
  rw [coe_f4IntegralDividedAdjointSquare_apply, coe_f4IntegralRootVector,
    ZeroMemClass.coe_zero]
  exact f4_dividedPower_two_ad_rootVector_eq_zero_of_short
    (f4SignedSimpleRootIndex k) i hi (by
      exact hopp)

/-- The integral divided square vanishes on each simple-coroot basis column. -/
theorem f4IntegralDividedAdjointSquare_simpleCoroot_eq_zero
    (k : Fin 4 ⊕ Fin 4) (i : Fin F4.rank) :
    f4IntegralDividedAdjointSquare k (f4IntegralSimpleCoroot i) = 0 := by
  let β : Weight ℚ (F4.cartanSubalgebra valid_F4) (F4.lieAlgebra valid_F4) :=
    ((F4.lieBasis valid_F4).baseSupportEquiv i :
      (F4.cartanSubalgebra valid_F4).root)
  have hcoe : (f4IntegralSimpleCoroot i : F4.lieAlgebra valid_F4) =
      ((coroot β : F4.cartanSubalgebra valid_F4) : F4.lieAlgebra valid_F4) := by
    simpa only [β] using coe_f4IntegralSimpleCoroot i
  apply Subtype.ext
  -- `Subtype.ext` leaves the goal stated with the anonymous subtype projection; restate it with
  -- the Lie-lattice coercion that the calculation below uses.
  change ((f4IntegralDividedAdjointSquare k (f4IntegralSimpleCoroot i) :
    f4ChevalleyLieLattice) : F4.lieAlgebra valid_F4) = 0
  calc
    _ = Associative.dividedPower 2
          (ad ℚ (F4.lieAlgebra valid_F4)
            (f4ChevalleyRootVector (f4KillingRoot (f4SignedSimpleRootIndex k)))) •
          (f4IntegralSimpleCoroot i : F4.lieAlgebra valid_F4) :=
      coe_f4IntegralDividedAdjointSquare_apply k (f4IntegralSimpleCoroot i)
    _ = Associative.dividedPower 2
          (ad ℚ (F4.lieAlgebra valid_F4)
            (f4ChevalleyRootVector (f4KillingRoot (f4SignedSimpleRootIndex k)))) •
          ((coroot β : F4.cartanSubalgebra valid_F4) : F4.lieAlgebra valid_F4) := by
      rw [hcoe]
    _ = 0 := f4_dividedPower_two_ad_cartan_eq_zero (f4SignedSimpleRootIndex k) (coroot β)

/-- The second divided adjoint power after reduction modulo two. -/
noncomputable def f4ModularDividedAdjointSquare (k : Fin 4 ⊕ Fin 4) :
    Module.End (ZMod 2) f4ModularChevalleyLieAlgebra :=
  (f4IntegralDividedAdjointSquare k).baseChange (ZMod 2)

/-- Reduction modulo two commutes with the integral divided square on pure tensors. -/
@[simp] theorem f4ModularDividedAdjointSquare_tmul (k : Fin 4 ⊕ Fin 4)
    (y : f4ChevalleyLieLattice) :
    f4ModularDividedAdjointSquare k (1 ⊗ₜ[ℤ] y) =
      1 ⊗ₜ[ℤ] f4IntegralDividedAdjointSquare k y := by
  rw [f4ModularDividedAdjointSquare, LinearMap.baseChange_tmul]

/-- Modulo two, the exceptional opposite-root column has coefficient one. -/
theorem f4ModularDividedAdjointSquare_rootVector_opposite (k : Fin 4 ⊕ Fin 4) :
    f4ModularDividedAdjointSquare k
        (f4ModularRootVector (f4OppositeRootIndex (f4SignedSimpleRootIndex k))) =
      f4ModularRootVector (f4SignedSimpleRootIndex k) := by
  rw [f4ModularRootVector_eq, f4ModularDividedAdjointSquare_tmul,
    f4IntegralDividedAdjointSquare_rootVector_opposite, TensorProduct.tmul_neg]
  rw [f4ModularRootVector_eq]
  congr 1

/-- Modulo two, every non-opposite short-root column of the divided square vanishes. -/
theorem f4ModularDividedAdjointSquare_rootVector_eq_zero_of_short
    (k : Fin 4 ⊕ Fin 4) (i : Fin 48) (hi : f4Length i = 1)
    (hopp : i ≠ f4OppositeRootIndex (f4SignedSimpleRootIndex k)) :
    f4ModularDividedAdjointSquare k (f4ModularRootVector i) = 0 := by
  rw [f4ModularRootVector_eq, f4ModularDividedAdjointSquare_tmul,
    f4IntegralDividedAdjointSquare_rootVector_eq_zero_of_short k i hi hopp,
    TensorProduct.tmul_zero]

/-- The modular divided square vanishes on every simple-coroot basis column. -/
theorem f4ModularDividedAdjointSquare_simpleCoroot_eq_zero
    (k : Fin 4 ⊕ Fin 4) (i : Fin F4.rank) :
    f4ModularDividedAdjointSquare k (f4ModularSimpleCoroot i) = 0 := by
  rw [f4ModularSimpleCoroot_eq, f4ModularDividedAdjointSquare_tmul,
    f4IntegralDividedAdjointSquare_simpleCoroot_eq_zero, TensorProduct.tmul_zero]

/-- The target coordinate in a divided-square matrix column. -/
def f4DividedSquareTarget : (Fin 4 ⊕ Fin 4) → Fin 26 → Fin 26
  | .inl i => raisingDividedSquareTarget i
  | .inr i => loweringDividedSquareTarget i

@[simp] theorem f4DividedSquareTarget_inl (i : Fin 4) (b : Fin 26) :
    f4DividedSquareTarget (.inl i) b = raisingDividedSquareTarget i b := (rfl)

@[simp] theorem f4DividedSquareTarget_inr (i : Fin 4) (b : Fin 26) :
    f4DividedSquareTarget (.inr i) b = loweringDividedSquareTarget i b := (rfl)

/-- The integral coefficient in a divided-square matrix column. -/
def f4DividedSquareCoeff : (Fin 4 ⊕ Fin 4) → Fin 26 → ℤ
  | .inl i => raisingDividedSquareCoeff i
  | .inr i => loweringDividedSquareCoeff i

@[simp] theorem f4DividedSquareCoeff_inl (i : Fin 4) (b : Fin 26) :
    f4DividedSquareCoeff (.inl i) b = raisingDividedSquareCoeff i b := (rfl)

@[simp] theorem f4DividedSquareCoeff_inr (i : Fin 4) (b : Fin 26) :
    f4DividedSquareCoeff (.inr i) b = loweringDividedSquareCoeff i b := (rfl)

/-- Each sparse divided-square matrix entry is its column coefficient at the target row. -/
@[simp] theorem rootDividedSquareMatrix_apply
    (k : Fin 4 ⊕ Fin 4) (a b : Fin 26) :
    rootDividedSquareMatrix k a b =
      if a = f4DividedSquareTarget k b then f4DividedSquareCoeff k b else 0 := by
  cases k with
  | inl i => rw [rootDividedSquareMatrix_inl, raisingDividedSquareMatrix_apply]; rfl
  | inr i => rw [rootDividedSquareMatrix_inr, loweringDividedSquareMatrix_apply]; rfl

/-- The coefficient vanishes modulo two exactly off the opposite-root weight. -/
theorem f4DividedSquareCoeff_mod_two_eq_zero_iff (k : Fin 4 ⊕ Fin 4) (b : Fin 26) :
    (f4DividedSquareCoeff k b : ZMod 2) = 0 ↔
      f4ShortRootWeight b ≠ f4Root (f4OppositeRootIndex (f4SignedSimpleRootIndex k)) := by
  cases k with
  | inl i =>
      simp only [f4DividedSquareCoeff, f4SignedSimpleRootIndex_inl, f4OppositeRootIndex_castAdd]
      revert i b
      decide +kernel
  | inr i =>
      simp only [f4DividedSquareCoeff, f4SignedSimpleRootIndex_inr,
        f4OppositeRootIndex_f4OppositeRootIndex]
      revert i b
      decide +kernel

/-- The divided-square coefficient vanishes modulo two for a long signed-simple source. -/
theorem f4DividedSquareCoeff_mod_two_eq_zero_of_long
    (k : Fin 4 ⊕ Fin 4)
    (hk : f4Length (f4SignedSimpleRootIndex k) = 2)
    (b : Fin 26) :
    (f4DividedSquareCoeff k b : ZMod 2) = 0 := by
  cases k with
  | inl i =>
      simp only [f4SignedSimpleRootIndex_inl, f4Length_def] at hk
      revert i b
      decide +kernel
  | inr i =>
      simp only [f4SignedSimpleRootIndex_inr, f4OppositeRootIndex_castAdd, f4Length_def] at hk
      revert i b
      decide +kernel

private theorem f4DividedSquareTable_nonzero (k : Fin 4 ⊕ Fin 4) (b : Fin 26)
    (h : (f4DividedSquareCoeff k b : ZMod 2) ≠ 0) :
    (f4DividedSquareCoeff k b : ZMod 2) = 1 ∧
      f4Length (f4SignedSimpleRootIndex k) = 1 ∧
      f4ShortRootWeight (f4DividedSquareTarget k b) =
        f4Root (f4SignedSimpleRootIndex k) := by
  cases k with
  | inl i =>
      simp only [f4DividedSquareCoeff, f4DividedSquareTarget,
        f4SignedSimpleRootIndex_inl] at h ⊢
      rw [f4Length_def]
      revert i b
      decide +kernel
  | inr i =>
      simp only [f4DividedSquareCoeff, f4DividedSquareTarget,
        f4SignedSimpleRootIndex_inr, f4OppositeRootIndex_castAdd] at h ⊢
      rw [f4Length_def]
      revert i b
      decide +kernel

/-- The divided-square matrix, viewed as an endomorphism of the canonical short-root ideal. -/
noncomputable def f4ShortRootDividedAdjointSquare (k : Fin 4 ⊕ Fin 4) :
    Module.End (ZMod 2) f4ShortRootLieIdeal :=
  Matrix.toLin f4ShortRootLieIdealBasis f4ShortRootLieIdealBasis
    ((rootDividedSquareMatrix k).map (Int.cast : ℤ → ZMod 2))

/-- The divided-square endomorphism is realized, in the canonical short-root basis, by the
reduction modulo two of the integral divided-square matrix. -/
theorem f4ShortRootDividedAdjointSquare_toMatrix (k : Fin 4 ⊕ Fin 4) :
    LinearMap.toMatrix f4ShortRootLieIdealBasis f4ShortRootLieIdealBasis
        (f4ShortRootDividedAdjointSquare k) =
      (rootDividedSquareMatrix k).map (Int.cast : ℤ → ZMod 2) := by
  unfold f4ShortRootDividedAdjointSquare
  exact LinearMap.toMatrix_toLin _ _ _

/-- Each basis column of the divided-square endomorphism has the advertised sparse form. -/
@[simp] theorem f4ShortRootDividedAdjointSquare_basis (k : Fin 4 ⊕ Fin 4) (b : Fin 26) :
    f4ShortRootDividedAdjointSquare k (f4ShortRootLieIdealBasis b) =
      (f4DividedSquareCoeff k b : ZMod 2) •
        f4ShortRootLieIdealBasis (f4DividedSquareTarget k b) := by
  apply f4ShortRootLieIdealBasis.repr.injective
  ext a
  have hentry : (f4ShortRootLieIdealBasis.repr
      (f4ShortRootDividedAdjointSquare k (f4ShortRootLieIdealBasis b))) a =
      ((rootDividedSquareMatrix k).map (Int.cast : ℤ → ZMod 2)) a b := by
    calc
      _ = (LinearMap.toMatrix f4ShortRootLieIdealBasis f4ShortRootLieIdealBasis
          (f4ShortRootDividedAdjointSquare k)) a b := by
        symm
        exact LinearMap.toMatrix_apply _ _ _ _ _
      _ = _ := congrArg (fun M : Matrix (Fin 26) (Fin 26) (ZMod 2) => M a b)
        (f4ShortRootDividedAdjointSquare_toMatrix k)
  have hmatrix : ((rootDividedSquareMatrix k).map (Int.cast : ℤ → ZMod 2)) a b =
      if a = f4DividedSquareTarget k b then
        (f4DividedSquareCoeff k b : ZMod 2) else 0 := by
    simp only [Matrix.map_apply, rootDividedSquareMatrix_apply]
    split_ifs <;> rfl
  have hrhs : (f4ShortRootLieIdealBasis.repr
      ((f4DividedSquareCoeff k b : ZMod 2) •
        f4ShortRootLieIdealBasis (f4DividedSquareTarget k b))) a =
      if a = f4DividedSquareTarget k b then
        (f4DividedSquareCoeff k b : ZMod 2) else 0 := by
    simp only [map_smul, Module.Basis.repr_self, Finsupp.smul_single]
    by_cases h : a = f4DividedSquareTarget k b
    · subst a
      simp
    · simp [h]
  exact hentry.trans (hmatrix.trans hrhs.symm)

private theorem f4ModularDividedAdjointSquare_basis_root
    (k : Fin 4 ⊕ Fin 4) (b : Fin 26) (i : Fin 48)
    (hi : f4Length i = 1) (h : f4ShortRootWeight b = f4Root i) :
    f4ModularDividedAdjointSquare k
        (f4ShortRootLieIdealBasis b : f4ModularChevalleyLieAlgebra) =
      (f4ShortRootDividedAdjointSquare k (f4ShortRootLieIdealBasis b) :
        f4ModularChevalleyLieAlgebra) := by
  have hbvec := coe_f4ShortRootLieIdealBasis_of_weight_eq_root b i hi h
  by_cases hcoeff : (f4DividedSquareCoeff k b : ZMod 2) = 0
  · have hneWeight := (f4DividedSquareCoeff_mod_two_eq_zero_iff k b).mp hcoeff
    have hne : i ≠ f4OppositeRootIndex (f4SignedSimpleRootIndex k) := by
      intro heq
      apply hneWeight
      rw [h, heq]
    have hzero : f4ShortRootDividedAdjointSquare k (f4ShortRootLieIdealBasis b) = 0 := by
      calc
        _ = (f4DividedSquareCoeff k b : ZMod 2) •
            f4ShortRootLieIdealBasis (f4DividedSquareTarget k b) :=
          f4ShortRootDividedAdjointSquare_basis k b
        _ = (0 : ZMod 2) •
            f4ShortRootLieIdealBasis (f4DividedSquareTarget k b) :=
          congrArg (fun c : ZMod 2 => c •
            f4ShortRootLieIdealBasis (f4DividedSquareTarget k b)) hcoeff
        _ = 0 := zero_smul _ _
    have hzeroCoe :
        (f4ShortRootDividedAdjointSquare k (f4ShortRootLieIdealBasis b) :
          f4ModularChevalleyLieAlgebra) = 0 :=
      congrArg (fun y : f4ShortRootLieIdeal =>
        (y : f4ModularChevalleyLieAlgebra)) hzero
    calc
      f4ModularDividedAdjointSquare k
          (f4ShortRootLieIdealBasis b : f4ModularChevalleyLieAlgebra) =
          f4ModularDividedAdjointSquare k (f4ModularRootVector i) :=
        congrArg (f4ModularDividedAdjointSquare k) hbvec
      _ = 0 := f4ModularDividedAdjointSquare_rootVector_eq_zero_of_short k i hi hne
      _ = (f4ShortRootDividedAdjointSquare k (f4ShortRootLieIdealBasis b) :
          f4ModularChevalleyLieAlgebra) := hzeroCoe.symm
  · have hwopp : f4ShortRootWeight b =
        f4Root (f4OppositeRootIndex (f4SignedSimpleRootIndex k)) := by
      by_contra hn
      exact hcoeff ((f4DividedSquareCoeff_mod_two_eq_zero_iff k b).2 hn)
    have hiopp : i = f4OppositeRootIndex (f4SignedSimpleRootIndex k) := by
      apply f4SimplyConnectedRootDatum.root.injective
      simpa only [f4SimplyConnectedRootDatum_root] using h.symm.trans hwopp
    have htable := f4DividedSquareTable_nonzero k b hcoeff
    have hcoeffOne : (f4DividedSquareCoeff k b : ZMod 2) = 1 := htable.1
    have hkshort : f4Length (f4SignedSimpleRootIndex k) = 1 := htable.2.1
    have htarget : f4ShortRootWeight (f4DividedSquareTarget k b) =
        f4Root (f4SignedSimpleRootIndex k) := htable.2.2
    have htargetvec := coe_f4ShortRootLieIdealBasis_of_weight_eq_root
      (f4DividedSquareTarget k b) (f4SignedSimpleRootIndex k) hkshort htarget
    calc
      f4ModularDividedAdjointSquare k
          (f4ShortRootLieIdealBasis b : f4ModularChevalleyLieAlgebra) =
          f4ModularRootVector (f4SignedSimpleRootIndex k) := by
        rw [hbvec, hiopp, f4ModularDividedAdjointSquare_rootVector_opposite]
      _ = (f4ShortRootDividedAdjointSquare k (f4ShortRootLieIdealBasis b) :
          f4ModularChevalleyLieAlgebra) := by
        rw [f4ShortRootDividedAdjointSquare_basis, hcoeffOne, one_smul, htargetvec]

private theorem f4DividedSquareCoeff_cartan_eq_zero (k : Fin 4 ⊕ Fin 4) (b : Fin 26)
    (hb : b = 12 ∨ b = 13) : (f4DividedSquareCoeff k b : ZMod 2) = 0 := by
  rcases hb with rfl | rfl <;> cases k with
  | inl i =>
      simp only [f4DividedSquareCoeff]
      revert i
      decide +kernel
  | inr i =>
      simp only [f4DividedSquareCoeff]
      revert i
      decide +kernel

private theorem f4ModularDividedAdjointSquare_basis_cartan
    (k : Fin 4 ⊕ Fin 4) (b : Fin 26) (i : Fin F4.rank)
    (hb : b = 12 ∨ b = 13)
    (hbasis : (f4ShortRootLieIdealBasis b : f4ModularChevalleyLieAlgebra) =
      f4ModularSimpleCoroot i) :
    f4ModularDividedAdjointSquare k
        (f4ShortRootLieIdealBasis b : f4ModularChevalleyLieAlgebra) =
      (f4ShortRootDividedAdjointSquare k (f4ShortRootLieIdealBasis b) :
        f4ModularChevalleyLieAlgebra) := by
  have hcoeff := f4DividedSquareCoeff_cartan_eq_zero k b hb
  have hzero : f4ShortRootDividedAdjointSquare k (f4ShortRootLieIdealBasis b) = 0 := by
    calc
      _ = (f4DividedSquareCoeff k b : ZMod 2) •
          f4ShortRootLieIdealBasis (f4DividedSquareTarget k b) :=
        f4ShortRootDividedAdjointSquare_basis k b
      _ = (0 : ZMod 2) • f4ShortRootLieIdealBasis (f4DividedSquareTarget k b) :=
        congrArg (fun c : ZMod 2 => c •
          f4ShortRootLieIdealBasis (f4DividedSquareTarget k b)) hcoeff
      _ = 0 := zero_smul _ _
  have hzeroCoe :
      (f4ShortRootDividedAdjointSquare k (f4ShortRootLieIdealBasis b) :
        f4ModularChevalleyLieAlgebra) = 0 :=
    congrArg (fun y : f4ShortRootLieIdeal =>
      (y : f4ModularChevalleyLieAlgebra)) hzero
  calc
    f4ModularDividedAdjointSquare k
        (f4ShortRootLieIdealBasis b : f4ModularChevalleyLieAlgebra) =
        f4ModularDividedAdjointSquare k (f4ModularSimpleCoroot i) :=
      congrArg (f4ModularDividedAdjointSquare k) hbasis
    _ = 0 := f4ModularDividedAdjointSquare_simpleCoroot_eq_zero k i
    _ = (f4ShortRootDividedAdjointSquare k (f4ShortRootLieIdealBasis b) :
        f4ModularChevalleyLieAlgebra) := hzeroCoe.symm

/-- The root-vector case of `f4ModularDividedAdjointSquare_basis`: the ambient divided square and
its matrix realization agree on a basis coordinate labelled by a short root. -/
private theorem f4ModularDividedAdjointSquare_basis_of_index_inl
    (k : Fin 4 ⊕ Fin 4) (b : Fin 26) (i : F4ShortRootIndex)
    (hb : f4ShortRootWeightIndexEquiv b = Sum.inl i) :
    f4ModularDividedAdjointSquare k
        (f4ShortRootLieIdealBasis b : f4ModularChevalleyLieAlgebra) =
      (f4ShortRootDividedAdjointSquare k (f4ShortRootLieIdealBasis b) :
        f4ModularChevalleyLieAlgebra) := by
  have hweight : f4ShortRootWeight b = f4Root i :=
    (f4ShortRootWeightIndexEquiv_apply_eq_inl_iff b i).mp hb
  exact f4ModularDividedAdjointSquare_basis_root k b i i.property hweight

/-- The Cartan case of `f4ModularDividedAdjointSquare_basis`: the ambient divided square and its
matrix realization agree on the two zero-weight basis coordinates. -/
private theorem f4ModularDividedAdjointSquare_basis_of_index_inr
    (k : Fin 4 ⊕ Fin 4) (b : Fin 26) (j : Fin 2)
    (hb : f4ShortRootWeightIndexEquiv b = Sum.inr j) :
    f4ModularDividedAdjointSquare k
        (f4ShortRootLieIdealBasis b : f4ModularChevalleyLieAlgebra) =
      (f4ShortRootDividedAdjointSquare k (f4ShortRootLieIdealBasis b) :
        f4ModularChevalleyLieAlgebra) := by
  have hb' : b = f4ShortRootWeightIndexEquiv.symm (Sum.inr j) := by
    apply f4ShortRootWeightIndexEquiv.injective
    rw [hb, Equiv.apply_symm_apply]
  have hj : j = 0 ∨ j = 1 := by omega
  rcases hj with rfl | rfl
  · simp only [f4ShortRootWeightIndexEquiv_symm_apply_inr_zero] at hb'
    subst b
    exact f4ModularDividedAdjointSquare_basis_cartan k 12
      (Fin.cast rank_F4.symm (2 : Fin 4)) (Or.inl rfl)
      coe_f4ShortRootLieIdealBasis_twelve
  · simp only [f4ShortRootWeightIndexEquiv_symm_apply_inr_one] at hb'
    subst b
    exact f4ModularDividedAdjointSquare_basis_cartan k 13
      (Fin.cast rank_F4.symm (3 : Fin 4)) (Or.inr rfl)
      coe_f4ShortRootLieIdealBasis_thirteen

/-- The ambient integral divided square and its matrix realization agree on every basis vector of
the modular short-root ideal. -/
theorem f4ModularDividedAdjointSquare_basis (k : Fin 4 ⊕ Fin 4) (b : Fin 26) :
    f4ModularDividedAdjointSquare k
        (f4ShortRootLieIdealBasis b : f4ModularChevalleyLieAlgebra) =
      (f4ShortRootDividedAdjointSquare k (f4ShortRootLieIdealBasis b) :
        f4ModularChevalleyLieAlgebra) := by
  let P : Prop :=
    f4ModularDividedAdjointSquare k
        (f4ShortRootLieIdealBasis b : f4ModularChevalleyLieAlgebra) =
      (f4ShortRootDividedAdjointSquare k (f4ShortRootLieIdealBasis b) :
        f4ModularChevalleyLieAlgebra)
  exact Sum.rec (motive := fun s => f4ShortRootWeightIndexEquiv b = s → P)
    (fun i h => f4ModularDividedAdjointSquare_basis_of_index_inl k b i h)
    (fun j h => f4ModularDividedAdjointSquare_basis_of_index_inr k b j h)
    (f4ShortRootWeightIndexEquiv b) rfl

/-- The ambient integral divided square agrees with its matrix realization on every element of
the modular short-root ideal. -/
@[simp] theorem coe_f4ShortRootDividedAdjointSquare_apply
    (k : Fin 4 ⊕ Fin 4) (y : f4ShortRootLieIdeal) :
    (f4ShortRootDividedAdjointSquare k y : f4ModularChevalleyLieAlgebra) =
      f4ModularDividedAdjointSquare k (y : f4ModularChevalleyLieAlgebra) := by
  have key : f4ShortRootLieIdeal.toSubmodule.subtype.comp
        (f4ShortRootDividedAdjointSquare k) =
      (f4ModularDividedAdjointSquare k).comp f4ShortRootLieIdeal.toSubmodule.subtype := by
    apply f4ShortRootLieIdealBasis.ext
    intro b
    simp only [LinearMap.comp_apply]
    exact (f4ModularDividedAdjointSquare_basis k b).symm
  exact LinearMap.congr_fun key y

end

end TauCeti.DynkinType
