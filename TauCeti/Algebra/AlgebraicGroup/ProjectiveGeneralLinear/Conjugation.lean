/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Center
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.MultiplicativeMatrix
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Kernel
public import TauCeti.Algebra.AlgebraicGroup.ProjectiveGeneralLinear.Basic
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.InnerAut

/-!
# The conjugation homomorphism from `GLₙ` to `PGLₙ`

An invertible matrix `g` acts on the matrix algebra `Mₙ` by the inner automorphism
`x ↦ g x g⁻¹`. This file constructs the corresponding homomorphism of affine group schemes
`GLₙ → PGLₙ` over a commutative ring `R`, where `PGLₙ` is the automorphism group scheme of `Mₙ`
from `TauCeti.Algebra.AlgebraicGroup.ProjectiveGeneralLinear.Basic`, and identifies:

* its effect on points: over every commutative `R`-algebra `A`, a point `g` of `GLₙ` goes to the
  inner automorphism of `Mₙ(A)` defined by `g`;
* its kernel: a point lies in the scheme-theoretic kernel exactly when its matrix is central, and
  over a field the kernel Hopf ideal is the defining ideal of the center `Z(GLₙ)` (which is
  `𝔾ₘ` when `n > 0`, and trivial when `n = 0`);
* its image on points with values in a local ring, in particular a field: by the Skolem–Noether
  theorem every automorphism of `Mₙ(K)` over a local ring `K` is inner, so the map on `K`-points
  is surjective. Together with the kernel computation, the `K`-points of `PGLₙ` are Mathlib's
  `PGL(n, K) = GLₙ(K) / Z(GLₙ(K))` (`Matrix.ProjGenLinGroup.innerAut_bijective`).

The pointwise facts about conjugation (`Matrix.GeneralLinearGroup.innerAut`, its kernel and its
surjectivity over a local ring) are in
`TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.InnerAut`. In coordinates, the inner automorphism
by `g` has, in the matrix-unit basis, the matrix whose entry at `((p, q), (i, j))` is
`gₚᵢ (g⁻¹)ⱼq`. Over the coordinate algebra of `GLₙ`, this
`conjugationMatrix` of the generic matrix is multiplicative, so it defines a coordinate morphism
`O(GL_{n²}) → O(GLₙ)` which kills the defining ideal of `PGLₙ`.

## Main declarations

* `TauCeti.ProjectiveGeneralLinear.conjugationMatrix`: the matrix of `x ↦ X x Y` in the
  matrix-unit basis.
* `TauCeti.ProjectiveGeneralLinear.conjugationMap`: the coordinate morphism of `GLₙ → PGLₙ`.
* `TauCeti.ProjectiveGeneralLinear.map_genericMatrix_conjugationMap`: in coordinates, it sends the
  generic matrix of `GL_{n²}` to the conjugation matrix of the generic matrix of `GLₙ`.
* `TauCeti.ProjectiveGeneralLinear.pointsMulEquiv_conjugationMap`: on points, it is
  `Matrix.GeneralLinearGroup.innerAut`.
* `TauCeti.ProjectiveGeneralLinear.mem_quotientPointsSubgroup_kernelHopfIdeal_conjugationMap_iff`
  and `TauCeti.ProjectiveGeneralLinear.kernelHopfIdeal_conjugationMap`: its kernel is the center.
* `TauCeti.ProjectiveGeneralLinear.mapPointsFunctor_conjugationMap_app_surjective`: it is
  surjective on points with values in a local ring.

## References

* J. S. Milne, *Algebraic Groups* (2017), where, for `n > 0`, `PGLₙ` is the quotient of `GLₙ` by
  its center `𝔾ₘ` and is identified with the automorphism group functor of `Mₙ`.
-/

public section

open CategoryTheory Matrix WithConv

namespace TauCeti.ProjectiveGeneralLinear

universe u v w

noncomputable section

section ConjugationMatrix

variable {n : ℕ} {S : Type v} [CommRing S]

/-- The matrix, in the matrix-unit basis of `Mₙ(S)`, of the linear map `x ↦ X x Y`: the
Kronecker product `X ⊗ Yᵀ`, reindexed along `finProdFinEquiv`. Its entry at `((p, q), (i, j))` is
`Xₚᵢ Yⱼq`. -/
def conjugationMatrix (X Y : Matrix (Fin n) (Fin n) S) : Matrix (Fin (n * n)) (Fin (n * n)) S :=
  Matrix.reindex finProdFinEquiv finProdFinEquiv (Matrix.kronecker X Yᵀ)

/-- The entry of the conjugation matrix at `(a, c)` is `Xₚᵢ Yⱼq` for `(p, q)` and `(i, j)` the
pairs numbered by `a` and `c`. -/
@[simp]
theorem conjugationMatrix_apply (X Y : Matrix (Fin n) (Fin n) S) (a c : Fin (n * n)) :
    conjugationMatrix X Y a c = X (finProdFinEquiv.symm a).1 (finProdFinEquiv.symm c).1 *
      Y (finProdFinEquiv.symm c).2 (finProdFinEquiv.symm a).2 := by
  simp [conjugationMatrix, Matrix.kronecker]

/-- Entrywise ring homomorphisms commute with forming the conjugation matrix. -/
theorem conjugationMatrix_map {T : Type w} [CommRing T] {F : Type*} [FunLike F S T]
    [RingHomClass F S T] (f : F) (X Y : Matrix (Fin n) (Fin n) S) :
    (conjugationMatrix X Y).map f = conjugationMatrix (X.map f) (Y.map f) := by
  ext a c
  simp [conjugationMatrix_apply]

/-- `conjugationMatrix X Y` is the matrix of `x ↦ X x Y` in the matrix-unit basis. -/
theorem toMatrix_mulLeft_comp_mulRight (X Y : Matrix (Fin n) (Fin n) S) :
    LinearMap.toMatrix (matrixUnitBasis n S) (matrixUnitBasis n S)
        (LinearMap.mulLeft S X ∘ₗ LinearMap.mulRight S Y) = conjugationMatrix X Y := by
  ext a c
  simp [LinearMap.toMatrix_apply, conjugationMatrix_apply, Matrix.mul_apply, Matrix.single_apply,
    ite_and, Finset.sum_ite_eq]

/-- The conjugation matrix of the identity is the identity. -/
@[simp]
theorem conjugationMatrix_one : conjugationMatrix (1 : Matrix (Fin n) (Fin n) S) 1 = 1 := by
  rw [← toMatrix_mulLeft_comp_mulRight, LinearMap.mulLeft_one, LinearMap.mulRight_one,
    LinearMap.id_comp, LinearMap.toMatrix_id]

/-- Composing `x ↦ X₂ x Y₂` with `x ↦ X₁ x Y₁` gives `x ↦ (X₁ X₂) x (Y₂ Y₁)`. -/
theorem conjugationMatrix_mul (X₁ X₂ Y₁ Y₂ : Matrix (Fin n) (Fin n) S) :
    conjugationMatrix (X₁ * X₂) (Y₂ * Y₁) =
      conjugationMatrix X₁ Y₁ * conjugationMatrix X₂ Y₂ := by
  simp only [← toMatrix_mulLeft_comp_mulRight, ← LinearMap.toMatrix_comp]
  congr 1
  ext x
  simp [Matrix.mul_assoc]

variable (R : Type u) [CommRing R] [Algebra R S] in
/-- Conjugation `x ↦ X x Y` by a matrix `X` with left inverse `Y` preserves matrix
multiplication. -/
theorem preserves_conjugationMatrix {X Y : Matrix (Fin n) (Fin n) S} (h : Y * X = 1) :
    ConstantMultiplication.Preserves R (n * n) (structureMatrix n R) (conjugationMatrix X Y) := by
  rw [← toMatrix_mulLeft_comp_mulRight, preserves_toMatrix_iff n R]
  intro x z
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.mulRight_apply,
    LinearMap.mulLeft_apply]
  calc X * (x * z * Y) = X * x * (Y * X) * z * Y := by rw [h, Matrix.mul_one]; noncomm_ring
    _ = X * (x * Y) * (X * (z * Y)) := by noncomm_ring

end ConjugationMatrix

section InnerAutMatrix

variable {n : ℕ} {A : Type w} [CommRing A]

/-- The matrix of the inner automorphism by `g` is the conjugation matrix of `g` and `g⁻¹`. -/
theorem coe_autToGeneralLinear_innerAut (g : Matrix.GeneralLinearGroup (Fin n) A) :
    (autToGeneralLinear n A (Matrix.GeneralLinearGroup.innerAut g) :
        Matrix (Fin (n * n)) (Fin (n * n)) A) =
      conjugationMatrix (g : Matrix (Fin n) (Fin n) A) (g : Matrix (Fin n) (Fin n) A)⁻¹ := by
  rw [coe_autToGeneralLinear, ← toMatrix_mulLeft_comp_mulRight]
  congr 1
  ext x : 1
  simp [Matrix.mul_assoc]

end InnerAutMatrix

section Coordinate

variable (n : ℕ) (R : Type u) [CommRing R]

/-- The invertible matrix of a point of `GLₘ` is the generic matrix evaluated at the point. -/
private theorem coe_pointsMulEquiv {m : ℕ} {A : Type w} [CommRing A] [Algebra R A]
    (p : WithConv (GeneralLinear.coordinateHopfAlgebra R m →ₐ[R] A)) :
    (GeneralLinear.pointsMulEquiv m p : Matrix (Fin m) (Fin m) A) =
      (GeneralLinear.genericMatrix R m).map p.ofConv := by
  rw [GeneralLinear.map_genericMatrix_eq_coe_pointToGeneralLinear, toConv_ofConv,
    GeneralLinear.pointsMulEquiv_apply]

private theorem map_comul_conjugationMatrix_genericMatrix :
    (conjugationMatrix (GeneralLinear.genericMatrix R n) (GeneralLinear.genericMatrix R n)⁻¹).map
        (Bialgebra.comulAlgHom R (GeneralLinear.coordinateHopfAlgebra R n)) =
      (conjugationMatrix (GeneralLinear.genericMatrix R n)
          (GeneralLinear.genericMatrix R n)⁻¹).map
          (Algebra.TensorProduct.includeLeft (R := R) (S := R)) *
        (conjugationMatrix (GeneralLinear.genericMatrix R n)
          (GeneralLinear.genericMatrix R n)⁻¹).map
          (Algebra.TensorProduct.includeRight (R := R)) := by
  simp only [conjugationMatrix_map, GeneralLinear.map_inv_genericMatrix,
    GeneralLinear.map_comul_genericMatrix, Matrix.mul_inv_rev, ← conjugationMatrix_mul]

private theorem map_counit_conjugationMatrix_genericMatrix :
    (conjugationMatrix (GeneralLinear.genericMatrix R n) (GeneralLinear.genericMatrix R n)⁻¹).map
        (Bialgebra.counitAlgHom R (GeneralLinear.coordinateHopfAlgebra R n)) = 1 := by
  simp [conjugationMatrix_map, GeneralLinear.map_inv_genericMatrix]

/-- The coordinate morphism `O(GL_{n²}) → O(GLₙ)` of the conjugation representation of `GLₙ` on
`Mₙ`, determined by the multiplicative conjugation matrix of the generic matrix. -/
private def conjugationBialgHom :
    GeneralLinear.coordinateHopfAlgebra R (n * n) →ₐc[R] GeneralLinear.coordinateHopfAlgebra R n :=
  GeneralLinear.coordinateBialgHomOfMultiplicative R (n * n)
    (conjugationMatrix (GeneralLinear.genericMatrix R n) (GeneralLinear.genericMatrix R n)⁻¹)
    (map_comul_conjugationMatrix_genericMatrix n R) (map_counit_conjugationMatrix_genericMatrix n R)

private theorem map_genericMatrix_conjugationBialgHom :
    (GeneralLinear.genericMatrix R (n * n)).map (conjugationBialgHom n R) =
      conjugationMatrix (GeneralLinear.genericMatrix R n) (GeneralLinear.genericMatrix R n)⁻¹ :=
  GeneralLinear.map_genericMatrix_coordinateBialgHomOfMultiplicative _ _ _ _ _

private theorem definingHopfIdeal_le_ker_conjugationBialgHom :
    (definingHopfIdeal n R).toIdeal ≤ RingHom.ker
      (_root_.CommHopfAlgCat.ofHom (conjugationBialgHom n R)).hom.toAlgHom.toRingHom := by
  refine ConstantMultiplication.definingHopfIdeal_toIdeal_le_ker_of_preserves_map_genericMatrix
    R (n * n) (structureMatrix n R) (conjugationBialgHom n R).toAlgHom ?_
  rw [BialgHom.coe_toAlgHom, map_genericMatrix_conjugationBialgHom]
  exact preserves_conjugationMatrix R
    (Matrix.nonsing_inv_mul _ (GeneralLinear.isUnit_det_genericMatrix R n))

/-- **The conjugation homomorphism `GLₙ → PGLₙ`**, as a morphism of coordinate Hopf algebras
`O(PGLₙ) → O(GLₙ)`: the conjugation representation `GLₙ → GL_{n²}` on `Mₙ` lands in the
automorphism group scheme of `Mₙ`. -/
def conjugationMap : coordinateHopfAlgebra n R ⟶ GeneralLinear.coordinateHopfAlgebra R n :=
  CommHopfAlgCat.liftQuotient (definingHopfIdeal n R)
    (_root_.CommHopfAlgCat.ofHom (conjugationBialgHom n R))
    (definingHopfIdeal_le_ker_conjugationBialgHom n R)

/-- **`GLₙ → PGLₙ` in coordinates**: the conjugation homomorphism sends the generic matrix of
`GL_{n²}`, read in `O(PGLₙ)`, to the conjugation matrix of the generic matrix `X` of `GLₙ`, whose
entry at `((p, q), (i, j))` is `Xₚᵢ (X⁻¹)ⱼq`. -/
theorem map_genericMatrix_conjugationMap :
    (GeneralLinear.genericMatrix R (n * n)).map
        (CommHopfAlgCat.mkQuotient _ (definingHopfIdeal n R) ≫ conjugationMap n R).hom =
      conjugationMatrix (GeneralLinear.genericMatrix R n) (GeneralLinear.genericMatrix R n)⁻¹ := by
  rw [conjugationMap, CommHopfAlgCat.mkQuotient_comp_liftQuotient, CommHopfAlgCat.hom_ofHom]
  exact map_genericMatrix_conjugationBialgHom n R

/-- **On points, `GLₙ → PGLₙ` is conjugation**: a point `g` of `GLₙ` goes to the inner
automorphism of `Mₙ(A)` by its invertible matrix. -/
@[simp]
theorem pointsMulEquiv_conjugationMap (A : CommAlgCat.{w} R)
    (g : HopfAlgebra.points (R := R) (H := GeneralLinear.coordinateHopfAlgebra R n) A) :
    pointsMulEquiv n R A
        (toConv (g.ofConv.comp ((conjugationMap n R).hom :
          coordinateHopfAlgebra n R →ₐ[R] GeneralLinear.coordinateHopfAlgebra R n))) =
      Matrix.GeneralLinearGroup.innerAut (GeneralLinear.pointsMulEquiv n g) := by
  apply autToGeneralLinear_injective n
  rw [autToGeneralLinear_pointsMulEquiv]
  ext1
  have hq : (CommHopfAlgCat.quotientPointsHom _ (definingHopfIdeal n R) A
      (toConv (g.ofConv.comp ((conjugationMap n R).hom :
        coordinateHopfAlgebra n R →ₐ[R] GeneralLinear.coordinateHopfAlgebra R n)))).ofConv =
      g.ofConv.comp (conjugationBialgHom n R).toAlgHom := by
    ext h
    rw [CommHopfAlgCat.quotientPointsHom_apply_apply, ofConv_toConv, AlgHom.comp_apply,
      AlgHom.comp_apply, conjugationMap, BialgHom.coe_toAlgHom, BialgHom.coe_toAlgHom]
    exact congrArg g.ofConv (CommHopfAlgCat.liftQuotient_mk _ _ _ h)
  rw [coe_autToGeneralLinear_innerAut, coe_pointsMulEquiv, coe_pointsMulEquiv, hq,
    AlgHom.coe_comp, ← Matrix.map_map, BialgHom.coe_toAlgHom,
    map_genericMatrix_conjugationBialgHom, conjugationMatrix_map,
    GeneralLinear.map_inv_genericMatrix]

end Coordinate

section Kernel

variable (n : ℕ)

/-- **The kernel of `GLₙ → PGLₙ` on points**: a point of `GLₙ` lies in the scheme-theoretic
kernel exactly when its invertible matrix is central. -/
theorem mem_quotientPointsSubgroup_kernelHopfIdeal_conjugationMap_iff {R : Type u} [CommRing R]
    (A : CommAlgCat.{w} R)
    (g : HopfAlgebra.points (R := R) (H := GeneralLinear.coordinateHopfAlgebra R n) A) :
    g ∈ CommHopfAlgCat.quotientPointsSubgroup _
        (CommHopfAlgCat.kernelHopfIdeal (conjugationMap n R)) A ↔
      GeneralLinear.pointsMulEquiv n g ∈ Subgroup.center (Matrix.GeneralLinearGroup (Fin n) A) := by
  rw [← CommHopfAlgCat.mapPointsFunctor_app_eq_one_iff,
    ← Matrix.GeneralLinearGroup.innerAut_eq_one_iff,
    ← pointsMulEquiv_conjugationMap, MulEquiv.map_eq_one_iff]

/-- **The kernel of `GLₙ → PGLₙ` is the center of `GLₙ`**: over a field, the kernel Hopf ideal
of the conjugation homomorphism is the defining ideal of the center. -/
theorem kernelHopfIdeal_conjugationMap (k : Type u) [Field k] :
    CommHopfAlgCat.kernelHopfIdeal (conjugationMap n k) =
      CommHopfAlgCat.centerDefiningIdeal (GeneralLinear.coordinateHopfAlgebra k n) := by
  have hmem : ∀ (A : CommAlgCat.{u} k)
      (g : HopfAlgebra.points (R := k) (H := GeneralLinear.coordinateHopfAlgebra k n) A),
      g ∈ CommHopfAlgCat.quotientPointsSubgroup _
          (CommHopfAlgCat.kernelHopfIdeal (conjugationMap n k)) A ↔
        g ∈ CommHopfAlgCat.centerPointsSubgroup _ A := by
    intro A g
    rw [mem_quotientPointsSubgroup_kernelHopfIdeal_conjugationMap_iff,
      ← GeneralLinear.map_centerPointsSubgroup_pointsMulEquiv_eq_center]
    exact ⟨fun ⟨g', hg', h⟩ => (GeneralLinear.pointsMulEquiv n).injective h ▸ hg',
      fun hg => Subgroup.mem_map_of_mem _ hg⟩
  apply le_antisymm
  · -- Test the kernel ideal on the generic point of the center, the quotient map.
    let A : CommAlgCat.{u} k := CommAlgCat.of k (GeneralLinear.coordinateHopfAlgebra k n ⧸
      (CommHopfAlgCat.centerDefiningIdeal (GeneralLinear.coordinateHopfAlgebra k n)).toIdeal)
    let q : HopfAlgebra.points (R := k) (H := GeneralLinear.coordinateHopfAlgebra k n) A :=
      toConv (Ideal.Quotient.mkₐ k _)
    have hq : q ∈ CommHopfAlgCat.centerPointsSubgroup _ A :=
      (CommHopfAlgCat.mem_quotientPointsSubgroup_iff _ _ A q).mpr fun y hy =>
        Ideal.Quotient.eq_zero_iff_mem.mpr (HopfIdeal.mem_toIdeal.mpr hy)
    intro x hx
    have hx0 := (CommHopfAlgCat.mem_quotientPointsSubgroup_iff _ _ A q).mp ((hmem A q).mpr hq) x hx
    exact HopfIdeal.mem_toIdeal.mp (Ideal.Quotient.eq_zero_iff_mem.mp hx0)
  · rw [CommHopfAlgCat.centerDefiningIdeal_le_iff,
      CommHopfAlgCat.isCentral_iff_forall_isCentralPoint]
    intro A g hg
    exact (CommHopfAlgCat.mem_centerPointsSubgroup_iff _ A g).mp ((hmem A g).mp hg)

/-- **`GLₙ → PGLₙ` is surjective on points with values in a local ring**, in particular in a
field: by the Skolem–Noether theorem, every such point of `PGLₙ` comes from a point of `GLₙ`. -/
theorem mapPointsFunctor_conjugationMap_app_surjective {R : Type u} [CommRing R] (K : Type w)
    [CommRing K] [IsLocalRing K] [Algebra R K] :
    Function.Surjective
      ((CommHopfAlgCat.mapPointsFunctor (conjugationMap n R)).app (CommAlgCat.of R K)) := by
  intro q
  obtain ⟨G, hG⟩ := Matrix.GeneralLinearGroup.innerAut_surjective K (pointsMulEquiv n R _ q)
  refine ⟨(GeneralLinear.pointsMulEquiv n).symm G, (pointsMulEquiv n R _).injective ?_⟩
  rw [CommHopfAlgCat.mapPointsFunctor_app_apply, pointsMulEquiv_conjugationMap,
    MulEquiv.apply_symm_apply, hG]

end Kernel

end

end TauCeti.ProjectiveGeneralLinear
