/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Basis.Fin
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import TauCeti.AlgebraicTopology.Cohomology.Cap.Kronecker
public import TauCeti.AlgebraicTopology.Cohomology.CrossProduct
public import TauCeti.AlgebraicTopology.Cohomology.Sphere.Basic

/-!
# The middle cup pairing of a product of two spheres

The pullbacks of the normalized top class of `Sⁿ` along the first and second projections
form a basis of `Hⁿ(Sⁿ × Sⁿ; k)` for `n > 0`, over any commutative ring. Their squares
vanish, and their ordered cup product evaluates to one on the cross product of the native
homology generators. The reverse order contributes the sign `(-1)^(n*n)`.

In even dimension the matrix is the hyperbolic plane. In particular this computes the
integral cup pairing of `S² × S²`, with the factor classes and their signs retained.
The homology class used here is explicitly the cross product of the standard generators;
no identification with a manifold orientation class is part of this file.

## References

* A. Hatcher, *Algebraic Topology*, Section 3.2, the cup product and the cohomology of
  products of spheres.
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory AlgebraicTopology

universe w

namespace TauCeti

variable (k : Type w) [CommRing k]

/-- The middle cohomology basis of `Sᵈ⁺¹ × Sᵈ⁺¹`, ordered by the first and second factor.
The sphere classes evaluate to one on the native standard homology generators. -/
def singularCohomologySphereSelfProdBasis (d : ℕ) :
    Module.Basis (Fin 2) k
      ((TopCat.sphere.{w} (d + 1) ⊗ TopCat.sphere.{w} (d + 1)).singularCohomology
        (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) (d + 1)) :=
  (Module.Basis.finTwoProd k).map
    (((LinearEquiv.prodComm k k k).trans
      ((singularCohomologyTopCatSphereEquiv k (𝟙_ (ModuleCat.{w} k)) d).symm.prodCongr
        (singularCohomologyZeroEvalEquiv (k := k) (sphereBasePoint d)).symm)).trans
      (TopCat.singularCohomologySphereProdEquiv (TopCat.sphere.{w} (d + 1)) d 0 (d + 1)
        (by omega)))

/-- The first basis class is pulled back along the first projection. -/
@[simp]
lemma singularCohomologySphereSelfProdBasis_zero (d : ℕ) :
    singularCohomologySphereSelfProdBasis k d 0 =
      TopCat.singularCohomologyMap (CartesianMonoidalCategory.fst _ _) (d + 1)
        (singularCohomologyTopCatSphereGenerator k d) := by
  simp only [singularCohomologySphereSelfProdBasis, Module.Basis.map_apply,
    Module.Basis.finTwoProd_zero, LinearEquiv.trans_apply, LinearEquiv.prodComm_apply,
    LinearEquiv.prodCongr_apply]
  rw [TopCat.singularCohomologySphereProdEquiv_apply]
  simp [singularCohomologyTopCatSphereEquiv_symm_eq_smul]

/-- The second basis class is pulled back along the second projection. -/
@[simp]
lemma singularCohomologySphereSelfProdBasis_one (d : ℕ) :
    singularCohomologySphereSelfProdBasis k d 1 =
      TopCat.singularCohomologyMap (CartesianMonoidalCategory.snd _ _) (d + 1)
        (singularCohomologyTopCatSphereGenerator k d) := by
  simp only [singularCohomologySphereSelfProdBasis, Module.Basis.map_apply,
    Module.Basis.finTwoProd_one, LinearEquiv.trans_apply, LinearEquiv.prodComm_apply,
    LinearEquiv.prodCongr_apply]
  rw [TopCat.singularCohomologySphereProdEquiv_apply]
  simp [singularCohomologyTopCatSphereEquiv_symm_eq_smul]

/-- The cross product of the two standard sphere homology generators, with coefficients
transported from `k ⊗ k` to `k` by the left unitor. -/
def singularHomologySphereSelfProdClass (d : ℕ) :
    ((singularHomologyFunctor (ModuleCat.{w} k) (d + 1 + (d + 1))).obj
      (𝟙_ (ModuleCat.{w} k))).obj (TopCat.sphere.{w} (d + 1) ⊗ TopCat.sphere.{w} (d + 1)) :=
  (((singularHomologyFunctor (ModuleCat.{w} k) (d + 1 + (d + 1))).map
    (λ_ (𝟙_ (ModuleCat.{w} k))).hom).app _)
      (TopCat.singularHomologyCross _ _ (𝟙_ (ModuleCat.{w} k)) (𝟙_ (ModuleCat.{w} k))
        (d + 1) (d + 1) (d + 1 + (d + 1)) rfl
        (singularHomologyTopCatSphereGenerator k d ⊗ₜ singularHomologyTopCatSphereGenerator k d))

/-- The product class is the homology cross product, transported along the left unitor. -/
lemma singularHomologySphereSelfProdClass_def (d : ℕ) :
    singularHomologySphereSelfProdClass k d =
      (((singularHomologyFunctor (ModuleCat.{w} k) (d + 1 + (d + 1))).map
        (λ_ (𝟙_ (ModuleCat.{w} k))).hom).app _)
        (TopCat.singularHomologyCross _ _ (𝟙_ (ModuleCat.{w} k)) (𝟙_ (ModuleCat.{w} k))
          (d + 1) (d + 1) (d + 1 + (d + 1)) rfl
          (singularHomologyTopCatSphereGenerator k d ⊗ₜ
            singularHomologyTopCatSphereGenerator k d)) :=
  (rfl)

/-- Each factor class has cup square zero. -/
@[simp]
lemma singularCup_sphereSelfProd_basis_self (d : ℕ) (i : Fin 2) :
    (TopCat.sphere.{w} (d + 1) ⊗ TopCat.sphere.{w} (d + 1)).singularCup k
      (λ_ _).inv (λ_ _).hom (d + 1) (d + 1) (d + 1 + (d + 1)) rfl
      (singularCohomologySphereSelfProdBasis k d i)
      (singularCohomologySphereSelfProdBasis k d i) = 0 := by
  fin_cases i <;>
    simp [singularCohomologySphereSelfProdBasis_zero,
      singularCohomologySphereSelfProdBasis_one, TopCat.singularCup_naturality,
      TopCat.singularCup_singularCohomologyTopCatSphereGenerator_self, map_zero]

/-- The ordered product of the factor classes evaluates to one on the cross product
of the standard homology generators. -/
lemma singularCupPairing_sphereSelfProd_basis_zero_one (d : ℕ) :
    (TopCat.sphere.{w} (d + 1) ⊗ TopCat.sphere.{w} (d + 1)).singularCupPairing k rfl
      (singularHomologySphereSelfProdClass k d)
      (singularCohomologySphereSelfProdBasis k d 0)
      (singularCohomologySphereSelfProdBasis k d 1) = 1 := by
  rw [singularCohomologySphereSelfProdBasis_zero, singularCohomologySphereSelfProdBasis_one,
    TopCat.singularCupPairing_apply, singularHomologySphereSelfProdClass_def,
    TopCat.singularKronecker_singularCup_fst_snd_singularHomologyCross]
  simp

/-- Reversing the order of the factor classes gives the middle-degree commutativity sign. -/
lemma singularCupPairing_sphereSelfProd_basis_one_zero (d : ℕ) :
    (TopCat.sphere.{w} (d + 1) ⊗ TopCat.sphere.{w} (d + 1)).singularCupPairing k rfl
      (singularHomologySphereSelfProdClass k d)
      (singularCohomologySphereSelfProdBasis k d 1)
      (singularCohomologySphereSelfProdBasis k d 0) = (-1 : k) ^ ((d + 1) * (d + 1)) := by
  rw [TopCat.singularCupPairing_gradedComm _ k rfl rfl _
    (singularCohomologySphereSelfProdBasis k d 0) (singularCohomologySphereSelfProdBasis k d 1),
    singularCupPairing_sphereSelfProd_basis_zero_one, mul_one]

/-- In the factor basis the middle cup pairing has zero diagonal and off-diagonal
entries one and the middle-degree commutativity sign. This also retains odd-dimensional
spheres, where the pairing is skew-symmetric. -/
theorem toMatrix_singularCupPairing_sphereSelfProd (d : ℕ) :
    LinearMap.BilinForm.toMatrix (singularCohomologySphereSelfProdBasis k d)
      ((TopCat.sphere.{w} (d + 1) ⊗ TopCat.sphere.{w} (d + 1)).singularCupPairing k rfl
        (singularHomologySphereSelfProdClass k d)) =
      !![0, 1; (-1 : k) ^ ((d + 1) * (d + 1)), 0] := by
  ext i j
  simp only [LinearMap.BilinForm.toMatrix_apply]
  fin_cases i <;> fin_cases j
  · rw [TopCat.singularCupPairing_apply, singularCup_sphereSelfProd_basis_self]
    simp
  · exact singularCupPairing_sphereSelfProd_basis_zero_one k d
  · exact singularCupPairing_sphereSelfProd_basis_one_zero k d
  · rw [TopCat.singularCupPairing_apply, singularCup_sphereSelfProd_basis_self]
    simp

/-- For even-dimensional spheres the middle cup pairing is the hyperbolic plane,
with the first and second factor classes as its displayed basis. -/
theorem toMatrix_singularCupPairing_sphereSelfProd_of_even (d : ℕ) (hd : Even (d + 1)) :
    LinearMap.BilinForm.toMatrix (singularCohomologySphereSelfProdBasis k d)
      ((TopCat.sphere.{w} (d + 1) ⊗ TopCat.sphere.{w} (d + 1)).singularCupPairing k rfl
        (singularHomologySphereSelfProdClass k d)) = !![0, 1; 1, 0] := by
  rw [toMatrix_singularCupPairing_sphereSelfProd, (hd.mul_right (d + 1)).neg_one_pow]

/-- The middle cup pairing in factor coordinates. In even dimension this is
`a₀ b₁ + a₁ b₀`, and a class of coordinates `(a₀,a₁)` has square `2 a₀ a₁`. -/
theorem singularCupPairing_sphereSelfProd_eq (d : ℕ)
    (α β : (TopCat.sphere.{w} (d + 1) ⊗ TopCat.sphere.{w} (d + 1)).singularCohomology
      (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) (d + 1)) :
    (TopCat.sphere.{w} (d + 1) ⊗ TopCat.sphere.{w} (d + 1)).singularCupPairing k rfl
      (singularHomologySphereSelfProdClass k d) α β =
      (singularCohomologySphereSelfProdBasis k d).repr α 0 *
          (singularCohomologySphereSelfProdBasis k d).repr β 1 +
        (-1 : k) ^ ((d + 1) * (d + 1)) *
          (singularCohomologySphereSelfProdBasis k d).repr α 1 *
          (singularCohomologySphereSelfProdBasis k d).repr β 0 := by
  rw [LinearMap.BilinForm.apply_eq_dotProduct_toMatrix_mulVec
    (singularCohomologySphereSelfProdBasis k d), toMatrix_singularCupPairing_sphereSelfProd]
  simp [dotProduct, Matrix.mulVec, Fin.sum_univ_two, mul_assoc, mul_left_comm]

/-- The even-dimensional middle cup matrix has determinant `-1`, in particular for the
integral pairing of `S² × S²`. -/
theorem det_toMatrix_singularCupPairing_sphereSelfProd_of_even (d : ℕ) (hd : Even (d + 1)) :
    (LinearMap.BilinForm.toMatrix (singularCohomologySphereSelfProdBasis k d)
      ((TopCat.sphere.{w} (d + 1) ⊗ TopCat.sphere.{w} (d + 1)).singularCupPairing k rfl
        (singularHomologySphereSelfProdClass k d))).det = -1 := by
  rw [toMatrix_singularCupPairing_sphereSelfProd_of_even k d hd]
  simp [Matrix.det_fin_two]

end TauCeti
