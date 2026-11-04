/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Morita.Matrix
public import TauCeti.LinearAlgebra.Matrix.Module
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import TauCeti.RingTheory.Morita.ModuleEnd

/-!
# Matrix Morita equivalence and evaluation

For a module `M` over `Matrix ι ι R`, Mathlib's inverse matrix Morita functor selects
`Eⱼⱼ M`. Evaluation at the standard vector `eⱼ` identifies this corner with the multiplicity
space `Hom_(Matrix ι ι R)(R^ι, M)`. Under this identification Mathlib's counit
`(Eⱼⱼ M)^ι → M` is evaluation: its value on `(vᵢ T(eⱼ))ᵢ` is `T(v)`.

The column module uses the scoped `Matrix.Module.matrixModule` action. The scalar action
on `M` used by the native inverse functor is restriction along `Matrix.scalar`; it agrees
with any given `R`-action satisfying the scalar tower law. No finiteness assumption is
imposed on `M`.

## References

* Mathlib's `ModuleCat.matrixEquivalence`, `MatrixModCat.toModuleCat` and
  `toModuleCatFromModuleCatLinearEquiv` supply the functors and counit used here.
* T. Y. Lam, *Lectures on Modules and Rings*, GTM 189 (1999), Chapter 7.
* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §5.
-/

public section

open CategoryTheory Matrix
open scoped Matrix.Module TensorProduct

namespace MatrixModCat

variable {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]

/-- Restriction along the scalar-matrix homomorphism recovers a given scalar action
whenever it satisfies the scalar tower law. -/
theorem compHom_scalar_smul {E : Type*} [AddCommGroup E] [Module R E]
    [Module (Matrix ι ι R) E] [IsScalarTower R (Matrix ι ι R) E] (r : R) (x : E) :
    @SMul.smul R E (Module.compHom E (Matrix.scalar ι)).toSMul r x = r • x := by
  -- The restricted action is scalar-matrix multiplication, and a scalar matrix is r • 1.
  change Matrix.scalar ι r • x = r • x
  rw [Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, smul_assoc, one_smul]

variable (M : ModuleCat (Matrix ι ι R))

/-- The scalar structure selected by Mathlib's inverse matrix functor. -/
local instance nativeScalarModule : Module R M := Module.compHom M (Matrix.scalar ι)

/-- The scalar tower of the native inverse matrix functor. -/
local instance nativeScalarTower : IsScalarTower R (Matrix ι ι R) M :=
  isScalarTower_toModuleCat R M

/-- The matrix-unit relation underlying evaluation at a chosen standard vector. -/
theorem single_smul_map_single (T : (ι → R) →ₗ[Matrix ι ι R] M) (i j : ι) :
    (single i j 1 : Matrix ι ι R) • T (Pi.single j 1) = T (Pi.single i 1) := by
  rw [← T.map_smul]
  simp

/-- Evaluation at `eⱼ`, with codomain the actual corner used by the native inverse functor. -/
def homToCorner (j : ι) : ((ι → R) →ₗ[Matrix ι ι R] M) →ₗ[R] toModuleCatObj R M j where
  toFun T := ⟨T (Pi.single j 1), T (Pi.single j 1), single_smul_map_single M T j j⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem coe_homToCorner_apply (j : ι) (T : (ι → R) →ₗ[Matrix ι ι R] M) :
    (homToCorner M j T : M) = T (Pi.single j 1) := (rfl)

/-- A corner vector determines a matrix-linear map by the native Morita counit. -/
def cornerToHom (j : ι) : toModuleCatObj R M j →ₗ[R] ((ι → R) →ₗ[Matrix ι ι R] M) where
  toFun x := (toModuleCatFromModuleCatLinearEquiv R M j).symm.toLinearMap ∘ₗ
    (LinearMap.toSpanSingleton R (toModuleCatObj R M j) x).mapMatrixModule ι
  map_add' x y := by
    ext v
    simp [toModuleCatFromModuleCatLinearEquiv, smul_add, Finset.sum_add_distrib]
  map_smul' r x := by
    ext v
    simp [toModuleCatFromModuleCatLinearEquiv, smul_comm _ r, Finset.smul_sum]

/-- The inverse evaluation map reconstructs a homomorphism by matrix units. -/
theorem cornerToHom_apply (j : ι) (x : toModuleCatObj R M j) (v : ι → R) :
    cornerToHom M j x v = ∑ i, (single i j 1 : Matrix ι ι R) • (v i • (x : M)) := by
  rfl

@[simp]
theorem homToCorner_cornerToHom (j : ι) (x : toModuleCatObj R M j) :
    homToCorner M j (cornerToHom M j x) = x := by
  apply Subtype.ext
  obtain ⟨y, hy⟩ := x.property
  simp only [coe_homToCorner_apply, cornerToHom_apply]
  simp [Pi.single_apply, ← hy, ← mul_smul]

@[simp]
theorem cornerToHom_homToCorner (j : ι) (T : (ι → R) →ₗ[Matrix ι ι R] M) :
    cornerToHom M j (homToCorner M j T) = T := by
  ext v
  simp only [cornerToHom_apply, coe_homToCorner_apply]
  calc
    _ = ∑ i, T (v i • Pi.single i 1) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [smul_comm, single_smul_map_single, T.map_smul_of_tower]
    _ = T (∑ i, v i • Pi.single i 1) := (map_sum (T.restrictScalars R) _ _).symm
    _ = T v := by congr 1; ext i; simp [Pi.single_apply]

/-- The multiplicity space of a matrix module is the corner selected by the native inverse
Morita functor. Its forward map is evaluation at `eⱼ`; its inverse uses the native counit. -/
def homEquivCorner (j : ι) : ((ι → R) →ₗ[Matrix ι ι R] M) ≃ₗ[R] toModuleCatObj R M j :=
  LinearEquiv.ofLinearMap (homToCorner M j) (cornerToHom M j)
    (LinearMap.ext (homToCorner_cornerToHom M j))
    (LinearMap.ext (cornerToHom_homToCorner M j))

@[simp]
theorem homEquivCorner_apply (j : ι) (T : (ι → R) →ₗ[Matrix ι ι R] M) :
    homEquivCorner M j T = homToCorner M j T := (rfl)

@[simp]
theorem homEquivCorner_symm_apply (j : ι) (x : toModuleCatObj R M j) :
    (homEquivCorner M j).symm x = cornerToHom M j x := (rfl)

/-- The native matrix Morita counit is evaluation under the corner identification. -/
theorem counitIso_hom_apply_eq_eval (j : ι) (v : ι → R)
    (T : (ι → R) →ₗ[Matrix ι ι R] M) :
    ((counitIso R j).hom.app M).hom (fun i ↦ v i • homToCorner M j T) = T v := by
  -- Mathlib defines this counit as the inverse of its reconstruction equivalence.
  exact LinearMap.congr_fun (cornerToHom_homToCorner M j T) v

/-- Corner evaluation is natural in matrix-linear module maps. -/
@[simp]
theorem homToCorner_comp {N : ModuleCat (Matrix ι ι R)} (j : ι)
    (f : M →ₗ[Matrix ι ι R] N) (T : (ι → R) →ₗ[Matrix ι ι R] M) :
    homToCorner N j (f ∘ₗ T) = fromMatrixLinear j f (homToCorner M j T) := by
  rfl

/-- Changing the selected corner transports evaluation by the corresponding matrix unit. -/
@[simp]
theorem cornerToHom_apply_single (j k : ι) (x : toModuleCatObj R M j) :
    cornerToHom M j x (Pi.single k 1) =
      (single k j 1 : Matrix ι ι R) • (x : M) := by
  simp [cornerToHom_apply, Pi.single_apply]

/-- Tensor coordinates for evaluation, using the actual corner of the native inverse functor.
A pure tensor `v ⊗ T` has coordinates `vᵢ T(eⱼ)`. -/
def tensorEquivColumns (j : ι) :
    (ι → R) ⊗[R] ((ι → R) →ₗ[Matrix ι ι R] M) ≃ₗ[R] (ι → toModuleCatObj R M j) :=
  TensorProduct.congr (LinearEquiv.refl R _) (homEquivCorner M j) ≪≫ₗ
    TensorProduct.comm R _ _ ≪≫ₗ TensorProduct.piScalarRight R R _ ι

@[simp]
theorem tensorEquivColumns_tmul (j : ι) (v : ι → R)
    (T : (ι → R) →ₗ[Matrix ι ι R] M) :
    tensorEquivColumns M j (v ⊗ₜ T) = fun i ↦ v i • homToCorner M j T := by
  simp [tensorEquivColumns]

/-- The inverse tensor coordinates are characterized on vectors supported at one index. -/
@[simp]
theorem tensorEquivColumns_symm_single (j i : ι) (x : toModuleCatObj R M j) :
    (tensorEquivColumns M j).symm (Pi.single i x) = Pi.single i 1 ⊗ₜ cornerToHom M j x := by
  simp [tensorEquivColumns, TensorProduct.piScalarRight_symm_single]

/-- On arbitrary tensors, the counit of the native matrix equivalence is the algebraic Morita
evaluation isomorphism. Consequently the composite is independent of the chosen corner. -/
theorem counitIso_hom_tensorEquivColumns (j : ι)
    (z : (ι → R) ⊗[R] ((ι → R) →ₗ[Matrix ι ι R] M)) :
    ((counitIso R j).hom.app M).hom (tensorEquivColumns M j z) =
      TauCeti.isotypicTensorEquivOfBijective Matrix.Module.lsmul_bijective z := by
  rw [TauCeti.isotypicTensorEquivOfBijective_apply]
  induction z using TensorProduct.inductionOn with
  | tmul v T =>
    rw [tensorEquivColumns_tmul, TauCeti.isotypicEval_tmul]
    exact counitIso_hom_apply_eq_eval M j v T
  | add x y hx hy =>
    rw [map_add (tensorEquivColumns M j), map_add (TauCeti.isotypicEval R)]
    exact (map_add ((counitIso R j).hom.app M).hom _ _).trans (congrArg₂ (· + ·) hx hy)

end MatrixModCat
