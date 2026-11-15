/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.GrothendieckGroup.Quiver.ForgetGrading
public import TauCeti.RepresentationTheory.GrothendieckGroup.Quiver.ExtEuler
public import TauCeti.RepresentationTheory.Quiver.PathAlgebra.GradedExtEuler.Pairing
public import TauCeti.Algebra.Homology.EulerCharacteristic.ExtEuler.Graded.ForgetGrading.Pairing

/-!
# The graded quiver q-Euler form at `q = 1`

Let `Q` be a finite quiver with finite-dimensional path algebra `kQ`, graded by path length. For
finite-dimensional graded `kQ`-modules `X` and `Y`, evaluating the q-Euler characteristic
`χ_q(X, Y)` at `q = 1` gives the ordinary Ext-Euler characteristic `χ(X, Y)` of the underlying
ungraded modules. On Grothendieck groups, the q-Euler form specialized at `q = 1` is the ungraded
Ext-Euler pairing pulled back along the isomorphism
`G₀^gr(mod kQ) ⊗ ℤ[q = 1] ≃ G₀(mod kQ)` induced by forgetting the grading.
The isomorphism and the vertex-dimension comparison are supplied by
`TauCeti.RepresentationTheory.GrothendieckGroup.Quiver.ForgetGrading`.

On objects, both sides are computed by Ringel formulas, so no comparison of graded and ungraded
`Ext` groups is used. The graded formula
`TauCeti.PathAlgebra.gradedExtEuler_eq_sum_smulGradedDimension` has the idempotent graded
dimensions `gdim(eᵢ • X)` as coordinates. At `q = 1` these become the
vertex dimensions `dim_k(eᵢ X)` of the underlying module, and the factor `q⁻¹` on each arrow
becomes `1`. The result is the ungraded formula `TauCeti.extEuler_eq_eulerForm_dimVector`.

The graded/ungraded `Ext` comparison hypothesis `TauCeti.IsGradedExtComparison` gives the same
numerical identity in general. The identity on Grothendieck groups is the path-algebra case of
`TauCeti.gradedExtEulerSpecialized_one_eq_extEulerPairing_gradedFiniteModules`, since a
finite-dimensional path algebra is Noetherian.

## Main results

* `TauCeti.PathAlgebra.laurentEval_one_gradedExtEuler_eq_extEuler`: `χ_q(X, Y)` at `q = 1` is
  the Ext-Euler characteristic of the underlying modules.
* `TauCeti.PathAlgebra.laurentSpecialize_gradedExtEulerForm_eq_extEulerPairing`: the q-Euler
  form on `G₀^gr(mod kQ)` specialized at `q = 1` is the ungraded Ext-Euler pairing of the classes
  with their grading forgotten.

## References

* I. Assem, D. Simson and A. Skowroński, *Elements of the Representation Theory of Associative
  Algebras I*, Chapter III, Section 3, for the Ringel form.
* Z. Dancso and A. Licata, *Koszul algebras and flow lattices*, Section 2.2, for the graded
  Grothendieck group, the q-Euler form and its specialization at `q = 1`.
-/

public section

namespace TauCeti.PathAlgebra

open CategoryTheory LaurentPolynomial
open scoped ModuleCat Pointwise

universe u v w

variable (k : Type (max u v)) (Q : Type u) [Field k] [Quiver.{v} Q]
  [Finite Q] [FiniteDimensional k (pathAlgebra k Q)]
  [HasExt.{max u v} (GradedModuleCat.{max u v} (integerGrade k Q))]

/-- **The q-Euler characteristic of graded path-algebra modules at `q = 1` is the ungraded
Ext-Euler characteristic.** For finite-dimensional graded `kQ`-modules `X` and `Y`, evaluating
`χ_q(X, Y)` at `q = 1` gives `χ(X, Y)` of the underlying modules. The two admissibility witnesses
are arbitrary. -/
theorem laurentEval_one_gradedExtEuler_eq_extEuler
    (X Y : GradedModuleCat.{max u v} (integerGrade k Q)) [Module.Finite k X] [Module.Finite k Y]
    (h : IsGradedEulerAdmissible k (GradedModuleCat.shift (integerGrade k Q)) X Y)
    (h' : IsEulerAdmissible.{max u v} k (GradedModuleCat.toModuleCat.obj X)
      (GradedModuleCat.toModuleCat.obj Y)) :
    laurentEval (1 : ℤˣ) (gradedExtEuler k (GradedModuleCat.shift (integerGrade k Q)) h) =
      extEuler k h' := by
  have := Fintype.ofFinite Q
  have (a b : Q) : Fintype (a ⟶ b) :=
    have := finite_hom_of_module_finite_pathAlgebra k Q inferInstance a b
    Fintype.ofFinite _
  have : Module.Finite (pathAlgebra k Q) (GradedModuleCat.toModuleCat.obj X) :=
    Module.Finite.of_restrictScalars_finite k (pathAlgebra k Q) X.carrier
  have : Module.Finite (pathAlgebra k Q) (GradedModuleCat.toModuleCat.obj Y) :=
    Module.Finite.of_restrictScalars_finite k (pathAlgebra k Q) Y.carrier
  rw [gradedExtEuler_eq_sum_smulGradedDimension, extEuler_eq_eulerForm_dimVector,
    eulerForm_eq_sum_card]
  simp only [map_sub, map_sum, map_mul, laurentEval_invert, inv_one,
    laurentEval_one_smulGradedDimension_vertexIdempotent, laurentEval_T, one_zpow, Units.val_one,
    one_mul, map_natCast, Nat.card_eq_fintype_card]
  congr 1
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
  ring

/-- **The graded quiver q-Euler form at `q = 1` is the ungraded Ext-Euler pairing.** On
`G₀^gr(mod kQ)` specialized at `q = 1`, the q-Euler form is the Ext-Euler pairing on
`G₀(mod kQ)` of the classes with their grading forgotten. -/
theorem laurentSpecialize_gradedExtEulerForm_eq_extEulerPairing
    (x y : LaurentSpecialization (1 : ℤˣ)
      (LaurentK0.{max u v} (gradedFiniteModulesExactStructure (integerGrade k Q)))) :
    (gradedExtEulerForm k Q).laurentSpecialize inv_one x y =
      extEulerPairing (isExtensionClosed_finiteModules (pathAlgebra k Q))
        (isExtensionClosed_finiteModules (pathAlgebra k Q))
        (isEulerAdmissibleOn_isFG_pathAlgebra k Q)
        (finiteModulesExactK0Equiv (pathAlgebra k Q)
          (gradedFiniteModulesForgetK0 (integerGrade k Q) x))
        (finiteModulesExactK0Equiv (pathAlgebra k Q)
          (gradedFiniteModulesForgetK0 (integerGrade k Q) y)) := by
  let _ := integerGradedAlgebra k Q
  have : IsNoetherianRing (pathAlgebra k Q) := isNoetherian_of_tower k inferInstance
  -- Both forms are the specialized q-Euler form; compare them on object classes.
  have hform : (gradedExtEulerForm k Q).laurentSpecialize inv_one =
      gradedExtEulerSpecialized isExtensionClosed_gradedFiniteModules_gradedAbelian
        isExtensionClosed_gradedFiniteModules_gradedAbelian
        gradedFiniteModules_gradedAbelian_shift gradedFiniteModules_gradedAbelian_shift
        (isGradedEulerAdmissibleOn_gradedFiniteModules k Q) 1 := by
    refine LaurentK0.hom_ext_laurentSpecialization 1 fun X =>
      LaurentK0.hom_ext_laurentSpecialization 1 fun Y => ?_
    rw [LinearMap.laurentSpecialize_mk_mk, gradedExtEulerForm_of_of]
    exact (gradedExtEulerSpecialized_mk_of_mk_of _ _ _ _ _ 1 X Y).symm
  rw [hform]
  exact gradedExtEulerSpecialized_one_eq_extEulerPairing_gradedFiniteModules (integerGrade k Q)
    (isGradedEulerAdmissibleOn_gradedFiniteModules k Q) (isEulerAdmissibleOn_isFG_pathAlgebra k Q)
    x y

end TauCeti.PathAlgebra
