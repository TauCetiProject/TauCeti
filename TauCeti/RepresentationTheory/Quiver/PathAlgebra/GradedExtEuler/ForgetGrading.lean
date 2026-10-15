/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.GradedModuleCat.CartanMap.ForgetGrading
public import TauCeti.RepresentationTheory.GrothendieckGroup.Quiver.ExtEuler
public import TauCeti.RepresentationTheory.Quiver.PathAlgebra.GradedExtEuler.Pairing

/-!
# The graded quiver q-Euler form at `q = 1`

Let `Q` be a finite quiver with finite-dimensional path algebra `kQ`, graded by path length. For
finite-dimensional graded `kQ`-modules `X` and `Y`, evaluating the q-Euler characteristic
`χ_q(X, Y)` at `q = 1` gives the ordinary Ext-Euler characteristic `χ(X, Y)` of the underlying
ungraded modules. On Grothendieck groups, the q-Euler form specialized at `q = 1` is the ungraded
Ext-Euler pairing pulled back along the map `G₀^gr(mod kQ) ⊗ ℤ[q = 1] → G₀(mod kQ)` induced by
forgetting the grading.

Both sides are computed by Ringel formulas, so no comparison of graded and ungraded `Ext` groups
is used. The graded formula `TauCeti.PathAlgebra.gradedExtEuler_eq_sum_smulGradedDimension` has
the idempotent graded dimensions `gdim(eᵢ • X)` as coordinates. At `q = 1` these become the
vertex dimensions `dim_k(eᵢ X)` of the underlying module, and the factor `q⁻¹` on each arrow
becomes `1`. The result is the ungraded formula `TauCeti.extEuler_eq_eulerForm_dimVector`.

The graded/ungraded `Ext` comparison hypothesis `TauCeti.IsGradedExtComparison` would give the
same numerical identity in general. Here the identity is proved directly, and that hypothesis is
not verified.

## Main results

* `TauCeti.PathAlgebra.laurentEval_one_smulGradedDimension_vertexIdempotent`: at `q = 1` the
  idempotent graded dimension at a vertex is the dimension vector of the underlying module.
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

section VertexDimension

variable (k : Type w) (Q : Type u) [Field k] [Quiver.{v} Q]

/-- Two `k`-module structures on a `kQ`-module, each compatible with the `kQ`-action, coincide.
Hence the vertex components have the same dimension for both. This reconciles the `k`-structure
of a graded module with the one `ModuleCat.moduleOfAlgebraModule` puts on its underlying
module. -/
private theorem finrank_vertexComponent_congr [Finite Q] {M : Type*} [AddCommGroup M]
    [Module (pathAlgebra k Q) M] (m₁ m₂ : Module k M)
    (t₁ : letI := m₁; IsScalarTower k (pathAlgebra k Q) M)
    (t₂ : letI := m₂; IsScalarTower k (pathAlgebra k Q) M) (i : Q) :
    (letI := m₁; haveI := t₁; Module.finrank k (vertexComponent k M i)) =
      (letI := m₂; haveI := t₂; Module.finrank k (vertexComponent k M i)) := by
  obtain rfl : m₁ = m₂ := Module.ext' _ _ fun c x => by
    have e₁ := (letI := m₁; haveI := t₁; algebraMap_smul (pathAlgebra k Q) c x)
    have e₂ := (letI := m₂; haveI := t₂; algebraMap_smul (pathAlgebra k Q) c x)
    exact e₁.symm.trans e₂
  rfl

/-- **At `q = 1` the graded dimension at a vertex is the dimension vector** of the underlying
`kQ`-module: `gdim(eᵢ • X)` evaluated at `q = 1` is `dim_k(eᵢ X)`. -/
@[simp]
theorem laurentEval_one_smulGradedDimension_vertexIdempotent [Finite Q]
    (X : GradedModuleCat.{max u v w} (integerGrade k Q)) [Module.Finite k X] (i : Q) :
    laurentEval (1 : ℤˣ) (X.smulGradedDimension (vertexIdempotent k i)) =
      dimVector ((quiverRepFunctor k Q).obj (GradedModuleCat.toModuleCat.obj X)) i := by
  rw [GradedModuleCat.laurentEval_one_smulGradedDimension _
      (vertexIdempotent_mem_integerGrade_zero k Q i), quiverRepFunctor_obj,
    dimVector_quiverRepOfModule, ← vertexComponent_def]
  exact congrArg Nat.cast <| finrank_vertexComponent_congr k Q _ _ X.isScalarTower
    (ModuleCat.isScalarTower_of_algebra_moduleCat (GradedModuleCat.toModuleCat.obj X)) i

end VertexDimension

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
  obtain ⟨x, rfl⟩ := LaurentSpecialization.mk_surjective 1 x
  obtain ⟨y, rfl⟩ := LaurentSpecialization.mk_surjective 1 y
  obtain ⟨x, rfl⟩ := (LaurentK0.ofExactK0 _).surjective x
  obtain ⟨y, rfl⟩ := (LaurentK0.ofExactK0 _).surjective y
  induction x using ExactK0.induction_on with
  | zero => simp
  | add a b ha hb =>
    simp only [map_add, LinearMap.add_apply, AddMonoidHom.add_apply, ha, hb]
  | neg a ha => simp only [map_neg, LinearMap.neg_apply, AddMonoidHom.neg_apply, ha]
  | of X =>
    induction y using ExactK0.induction_on with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb]
    | neg a ha => simp only [map_neg, ha]
    | of Y =>
      simp only [LaurentK0.ofExactK0_exactK0_of, LinearMap.laurentSpecialize_mk_mk,
        gradedExtEulerForm_of_of, gradedFiniteModulesForgetK0_mk_of, finiteModulesExactK0Equiv_of,
        extEulerPairing_of_of]
      have : Module.Finite (pathAlgebra k Q) X.obj := gradedFiniteModules_iff.mp X.property
      have : Module.Finite (pathAlgebra k Q) Y.obj := gradedFiniteModules_iff.mp Y.property
      have : Module.Finite k X.obj := Module.Finite.trans (pathAlgebra k Q) X.obj
      have : Module.Finite k Y.obj := Module.Finite.trans (pathAlgebra k Q) Y.obj
      exact laurentEval_one_gradedExtEuler_eq_extEuler k Q X.obj Y.obj _ _

end TauCeti.PathAlgebra
