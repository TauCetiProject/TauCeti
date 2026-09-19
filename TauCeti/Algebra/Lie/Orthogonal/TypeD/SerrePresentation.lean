/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Orthogonal.TypeD.RootGenerators
public import TauCeti.Algebra.Lie.Presentation.Serre

/-!
# The matrix realization of the type-D Serre presentation

The standard split orthogonal Lie algebra has explicit Bourbaki-numbered raising, lowering, and
Cartan generators in `TauCeti.TypeDStd`. This file packages their bracket relations as a
`TauCeti.IsSerreSystem` and names the resulting homomorphism from the type-`D` Serre presentation.

The only relations not already stated in the matrix API are the higher Serre relations in their
Cartan-matrix exponent form. For a type-`D` Cartan entry, the exponent is zero at a diagonal or a
nonadjacent pair and one at an adjacent pair. The proof therefore reduces to the existing
self-bracket, nonadjacent-bracket, and double-bracket calculations.

## Main definitions and results

* `TauCeti.TypeDStd.isSerreSystem_rootGenerator`: the standard matrix generators form a type-`D`
  Serre system.
* `TauCeti.TypeDStd.serreRepresentation`: the induced homomorphism from the type-`D` Serre
  presentation to the split orthogonal Lie algebra.
* `TauCeti.TypeDStd.serreRepresentation_serreH`,
  `TauCeti.TypeDStd.serreRepresentation_serreE`, and
  `TauCeti.TypeDStd.serreRepresentation_serreF`: the images of the presented generators.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate IV.
* J.-P. Serre, *Complex Semisimple Lie Algebras*, Chapter VI, Appendix.
-/

public section

namespace TauCeti.TypeDStd

variable {K : Type*} [CommRing K] (n : ℕ) (hn : 4 ≤ n)

private theorem neg_typeDCartan_toNat_of_ne_zero_of_ne (i j : Fin n)
    (hzero : CartanMatrix.D n i j ≠ 0) (hij : i ≠ j) :
    (-CartanMatrix.D n i j).toNat = 1 := by
  simp only [CartanMatrix.D, Matrix.of_apply] at hzero ⊢
  split_ifs <;> omega

/-- The higher Serre relation for the positive simple-root generators of the standard split
type-`D` Lie algebra. -/
@[simp]
theorem ad_pow_lie_rootGenerator_inl_rootGenerator_inl (i j : Fin n) :
    (_root_.LieAlgebra.ad K (LieAlgebra.Orthogonal.typeD (Fin n) K)
        (rootGenerator (K := K) n hn (.inl i)) ^
      (-CartanMatrix.D n i j).toNat)
        ⁅rootGenerator (K := K) n hn (.inl i), rootGenerator (K := K) n hn (.inl j)⁆ = 0 := by
  classical
  by_cases hzero : CartanMatrix.D n i j = 0
  · rw [hzero]
    simpa using lie_rootGenerator_inl_inl_of_cartan_eq_zero n hn hzero
  · by_cases hij : i = j
    · subst j
      simp
    · rw [neg_typeDCartan_toNat_of_ne_zero_of_ne n i j hzero hij, pow_one,
        _root_.LieAlgebra.ad_apply]
      exact lie_rootGenerator_inl_lie_rootGenerator_inl n hn i j

/-- The higher Serre relation for the negative simple-root generators of the standard split
type-`D` Lie algebra. -/
@[simp]
theorem ad_pow_lie_rootGenerator_inr_rootGenerator_inr (i j : Fin n) :
    (_root_.LieAlgebra.ad K (LieAlgebra.Orthogonal.typeD (Fin n) K)
        (rootGenerator (K := K) n hn (.inr i)) ^
      (-CartanMatrix.D n i j).toNat)
        ⁅rootGenerator (K := K) n hn (.inr i), rootGenerator (K := K) n hn (.inr j)⁆ = 0 := by
  classical
  by_cases hzero : CartanMatrix.D n i j = 0
  · rw [hzero]
    simpa using lie_rootGenerator_inr_inr_of_cartan_eq_zero n hn hzero
  · by_cases hij : i = j
    · subst j
      simp
    · rw [neg_typeDCartan_toNat_of_ne_zero_of_ne n i j hzero hij, pow_one,
        _root_.LieAlgebra.ad_apply]
      exact lie_rootGenerator_inr_lie_rootGenerator_inr n hn i j

/-- **The standard split type-`D` matrix generators satisfy the Serre relations.** -/
theorem isSerreSystem_rootGenerator :
    TauCeti.IsSerreSystem K (CartanMatrix.D n)
      (cartanGenerator (K := K) n hn)
      (fun i => rootGenerator (K := K) n hn (.inl i))
      (fun i => rootGenerator (K := K) n hn (.inr i)) where
  lie_H_H := lie_cartanGenerator_cartanGenerator n hn
  lie_E_F_self i := by simp
  lie_E_F_of_ne i j hij := by simp [hij]
  lie_H_E i j := by
    have h := lie_cartanGenerator_rootGenerator (K := K) n hn (.inl j) i
    rw [rootGeneratorWeight_inl] at h
    rw [← (CartanMatrix.D_isSymm n).apply i j]
    simpa only [eq_intCast, Int.cast_smul_eq_zsmul] using h
  lie_H_F i j := by
    have h := lie_cartanGenerator_rootGenerator (K := K) n hn (.inr j) i
    rw [rootGeneratorWeight_inr] at h
    rw [← (CartanMatrix.D_isSymm n).apply i j]
    simpa only [eq_intCast, Int.cast_smul_eq_zsmul, neg_smul] using h
  ad_pow_lie_E_E := ad_pow_lie_rootGenerator_inl_rootGenerator_inl n hn
  ad_pow_lie_F_F := ad_pow_lie_rootGenerator_inr_rootGenerator_inr n hn

/-- **The matrix realization of the type-`D` Serre presentation**, sending the presented Cartan,
positive, and negative generators to the corresponding explicit split orthogonal matrices. -/
noncomputable def serreRepresentation :
    Matrix.ToLieAlgebra K (CartanMatrix.D n) →ₗ⁅K⁆
      LieAlgebra.Orthogonal.typeD (Fin n) K :=
  TauCeti.serreLift (isSerreSystem_rootGenerator n hn)

/-- The matrix realization sends a presented Cartan generator to the corresponding explicit
coroot matrix. -/
@[simp]
theorem serreRepresentation_serreH (i : Fin n) :
    serreRepresentation (K := K) n hn (TauCeti.serreH K (CartanMatrix.D n) i) =
      cartanGenerator n hn i := by
  simp [serreRepresentation]

/-- The matrix realization sends a presented positive generator to the corresponding raising
matrix. -/
@[simp]
theorem serreRepresentation_serreE (i : Fin n) :
    serreRepresentation (K := K) n hn (TauCeti.serreE K (CartanMatrix.D n) i) =
      rootGenerator n hn (.inl i) := by
  simp [serreRepresentation]

/-- The matrix realization sends a presented negative generator to the corresponding lowering
matrix. -/
@[simp]
theorem serreRepresentation_serreF (i : Fin n) :
    serreRepresentation (K := K) n hn (TauCeti.serreF K (CartanMatrix.D n) i) =
      rootGenerator n hn (.inr i) := by
  simp [serreRepresentation]

end TauCeti.TypeDStd
