/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.RepresentationTheory.Quiver.PathAlgebra.GradedExtEuler.Value
public import TauCeti.Algebra.Homology.EulerCharacteristic.ExtEuler.Graded.FiniteLength
public import Mathlib.LinearAlgebra.Matrix.SesquilinearForm

/-!
# The graded Ringel formula on all finite graded path-algebra modules

For a finite quiver with finite-dimensional path algebra, every pair of finite graded modules
is graded Euler-admissible. The first-arrow resolutions give admissibility on vertex simples;
internal shifts and graded composition series extend it to every finite graded source.

The categorical q-Euler form on the Laurent Grothendieck group is the graded Ringel form:
if `xᵢ` and `yᵢ` are the idempotent graded dimensions, then

`χ_q(x,y) = ∑ᵢ invert(xᵢ) yᵢ - q⁻¹ ∑_{a : i ⟶ j} invert(xᵢ) yⱼ`.

Rows are source vertices and columns are target vertices. The inverse power of `q` records
the shift of the projectives in the first-arrow resolution, and the involution in the first
argument records q-antilinearity. Neither the pairing nor its matrix is generally symmetric.

## References

* I. Assem, D. Simson and A. Skowroński, *Elements of the Representation Theory of Associative
  Algebras I*, Chapter III, Sections 2--3, for the first-arrow resolution and Ringel form.
* Z. Dancso and A. Licata, *Koszul algebras and flow lattices*, Section 2.2,
  for the q-antilinear convention.

The object-level entries are those of `gradedExtEuler_gradedVertexSimple_gradedVertexSimple`;
the extension to classes uses `gradedVertexSimpleClassBasis` and Mathlib's sesquilinear
matrix evaluation formula.
-/

public section

noncomputable section

namespace TauCeti.PathAlgebra

open CategoryTheory LaurentPolynomial

universe u v w

variable (k : Type w) (Q : Type u) [Field k] [Quiver.{v} Q]
  [Finite Q] [Module.Finite k (pathAlgebra k Q)]
  [HasExt.{max u v w} (GradedModuleCat.{max u v w} (integerGrade k Q))]

/-- Every pair of finite graded modules over a finite-dimensional path algebra is graded
Euler-admissible. Both cohomological and internal finiteness follow from the first-arrow
resolutions and graded composition series. -/
theorem isGradedEulerAdmissibleOn_gradedFiniteModules :
    IsGradedEulerAdmissibleOn (k := k) (e := GradedModuleCat.shift (integerGrade k Q))
      (gradedFiniteModules (integerGrade k Q)) (gradedFiniteModules (integerGrade k Q)) where
  isGradedEulerAdmissible X Y hX hY := by
    let _ := integerGradedAlgebra k Q
    have : Module.Finite (pathAlgebra k Q) X := gradedFiniteModules_iff.mp hX
    have : Module.Finite (pathAlgebra k Q) Y := gradedFiniteModules_iff.mp hY
    have : Module.Finite k X := Module.Finite.trans (pathAlgebra k Q) X
    have : Module.Finite k Y := Module.Finite.trans (pathAlgebra k Q) Y
    have : ∀ i j : Q, Finite (i ⟶ j) :=
      finite_hom_of_module_finite_pathAlgebra k Q inferInstance
    refine isGradedEulerAdmissible_of_finite_of_forall_simple _ Y (fun S hS hs ↦ ?_) X
    have : Module.Finite k S := hS
    have : Module.Finite (pathAlgebra k Q) S :=
      Module.Finite.of_restrictScalars_finite k (pathAlgebra k Q) S
    obtain ⟨i, d, ⟨e⟩⟩ :=
      (isExhaustiveGradedSimpleFamily_iff _).mp
        (isExhaustiveGradedSimpleFamily_gradedVertexSimple k Q)
        ⟨S, gradedFiniteModules_iff.mpr inferInstance⟩ hs
    exact ((isGradedEulerAdmissible_gradedVertexSimple k Q i Y).shiftObj d).of_iso k
      e.symm (Iso.refl Y)

/-- The categorical q-Euler form on `G₀^gr(mod kQ)`, q-antilinear in the first argument
and q-linear in the second. Admissibility is proved for every finite graded module pair. -/
def gradedExtEulerForm :
    LaurentK0.{max u v w} (gradedFiniteModulesExactStructure (integerGrade k Q))
      →ₛₗ[(invert (R := ℤ)).toRingEquiv.toRingHom]
    LaurentK0.{max u v w} (gradedFiniteModulesExactStructure (integerGrade k Q))
      →ₗ[LaurentPolynomial ℤ] LaurentPolynomial ℤ :=
  let _ := integerGradedAlgebra k Q
  gradedExtEulerSesquilinear.{max u v w}
    (C := GradedModuleCat.{max u v w} (integerGrade k Q)) (k := k)
    (e := GradedModuleCat.shift (integerGrade k Q))
    (P := gradedFiniteModules (integerGrade k Q))
    (Q := gradedFiniteModules (integerGrade k Q))
    isExtensionClosed_gradedFiniteModules_gradedAbelian
    isExtensionClosed_gradedFiniteModules_gradedAbelian
    gradedFiniteModules_gradedAbelian_shift gradedFiniteModules_gradedAbelian_shift
    (isGradedEulerAdmissibleOn_gradedFiniteModules k Q)

/-- On object classes the q-Euler form is the graded Ext-Euler characteristic. -/
@[simp]
theorem gradedExtEulerForm_of_of
    (X Y : (gradedFiniteModules (integerGrade k Q)).FullSubcategory) :
    gradedExtEulerForm k Q (LaurentK0.of _ X) (LaurentK0.of _ Y) =
      gradedExtEuler k (GradedModuleCat.shift (integerGrade k Q))
        ((isGradedEulerAdmissibleOn_gradedFiniteModules k Q).isGradedEulerAdmissible
          X.property Y.property) := by
  let _ := integerGradedAlgebra k Q
  rw [gradedExtEulerForm]
  exact gradedExtEulerSesquilinear_of_of _ _ _ _ _ X Y

variable [DecidableEq Q]

/-- The q-Euler matrix in the graded vertex-simple basis is `I - q⁻¹ A`, where the
`(i,j)` entry of `A` counts arrows `i ⟶ j`. -/
theorem gradedExtEulerForm_basis (i j : Q) :
    gradedExtEulerForm k Q (gradedVertexSimpleClassBasis k Q i)
      (gradedVertexSimpleClassBasis k Q j) =
      (if i = j then 1 else 0) - T (-1) * (Nat.card (i ⟶ j) : LaurentPolynomial ℤ) := by
  rw [gradedVertexSimpleClassBasis_apply, gradedVertexSimpleClassBasis_apply,
    gradedExtEulerForm_of_of]
  exact gradedExtEuler_gradedVertexSimple_gradedVertexSimple k Q i j _

variable [Fintype Q]

omit [DecidableEq Q] in
/-- **The graded Ringel formula on Grothendieck classes.** The vertex coordinates are the
idempotent graded dimensions, and the source coordinates are conjugated by `q ↦ q⁻¹`. -/
theorem gradedExtEulerForm_eq_sum
    (x y : LaurentK0.{max u v w} (gradedFiniteModulesExactStructure (integerGrade k Q))) :
    gradedExtEulerForm k Q x y =
      ∑ i, invert ((gradedVertexSimpleClassBasis k Q).repr x i) *
        (gradedVertexSimpleClassBasis k Q).repr y i -
      T (-1) * ∑ i, ∑ j, (Nat.card (i ⟶ j) : LaurentPolynomial ℤ) *
        invert ((gradedVertexSimpleClassBasis k Q).repr x i) *
          (gradedVertexSimpleClassBasis k Q).repr y j := by
  classical
  rw [apply_eq_dotProduct_toMatrix₂_mulVec
    (gradedVertexSimpleClassBasis k Q) (gradedVertexSimpleClassBasis k Q)]
  simp only [dotProduct, Matrix.mulVec, LinearMap.toMatrix₂_apply,
    gradedExtEulerForm_basis]
  simp only [Function.comp_apply, RingHom.id_apply]
  simp only [Finset.mul_sum, sub_mul, mul_sub, Finset.sum_sub_distrib]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    simp
  · apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    simp only [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
      AlgEquiv.coe_toRingEquiv]
    ring

omit [DecidableEq Q] in
/-- **The graded Ringel formula for finite-dimensional graded modules.** The coordinate at
vertex `i` is the graded dimension of the image of its vertex idempotent. The formula holds
for any admissibility witness, without choosing a composition series or support bounds. -/
theorem gradedExtEuler_eq_sum_smulGradedDimension
    (X Y : GradedModuleCat.{max u v w} (integerGrade k Q))
    [Module.Finite k X] [Module.Finite k Y]
    (h : IsGradedEulerAdmissible k (GradedModuleCat.shift (integerGrade k Q)) X Y) :
    gradedExtEuler k (GradedModuleCat.shift (integerGrade k Q)) h =
      ∑ i, invert (X.smulGradedDimension (vertexIdempotent k i)) *
        Y.smulGradedDimension (vertexIdempotent k i) -
      T (-1) * ∑ i, ∑ j, (Nat.card (i ⟶ j) : LaurentPolynomial ℤ) *
        invert (X.smulGradedDimension (vertexIdempotent k i)) *
          Y.smulGradedDimension (vertexIdempotent k j) := by
  let _ := integerGradedAlgebra k Q
  have : Module.Finite (pathAlgebra k Q) X :=
    Module.Finite.of_restrictScalars_finite k (pathAlgebra k Q) X
  have : Module.Finite (pathAlgebra k Q) Y :=
    Module.Finite.of_restrictScalars_finite k (pathAlgebra k Q) Y
  have hval := gradedExtEulerForm_eq_sum k Q
    (LaurentK0.of _ ⟨X, gradedFiniteModules_iff.mpr inferInstance⟩)
    (LaurentK0.of _ ⟨Y, gradedFiniteModules_iff.mpr inferInstance⟩)
  rw [gradedExtEulerForm_of_of] at hval
  have hcoord (Z : (gradedFiniteModules (integerGrade k Q)).FullSubcategory) (i : Q) :
      (gradedVertexSimpleClassBasis k Q).repr (LaurentK0.of _ Z) i =
        Z.obj.smulGradedDimension (vertexIdempotent k i) := by
    rw [gradedVertexSimpleClassBasis_repr_apply]
    exact gradedIdempotentCoordinate_of _ _ _
  simpa only [hcoord] using hval

end TauCeti.PathAlgebra
