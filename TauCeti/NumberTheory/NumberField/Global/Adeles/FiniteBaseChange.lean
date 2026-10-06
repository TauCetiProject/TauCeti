/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.LocalGlobal.Semilocal.Basic
public import TauCeti.RingTheory.DedekindDomain.FiniteAdeleRing.Extension
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-!
# The scalar-extension map of finite adeles

For number fields `L/K`, the canonical map from `𝔸ᶠ_K ⊗[K] L` to `𝔸ᶠ_L` multiplies
an extended adele by a diagonal field element. It is injective: the semilocal decomposition
at every finite place detects the coordinates of a tensor in any scalar-extended field basis.
When the source carries its module topology over `𝔸ᶠ_K`, the map is continuous.

This file constructs the map and proves its faithfulness, not its surjectivity or that its
inverse is continuous. These are separate assertions about the restricted product.

The construction follows the infinite-adele comparison in
`TauCeti.NumberTheory.NumberField.Global.Adeles.InfiniteBaseChange`; the local input is
`TauCeti.semilocalEquiv`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter II, Proposition (8.3).
-/

public section
noncomputable section

open IsDedekindDomain NumberField
open scoped TensorProduct FiniteAdeleExtension AdicCompletionExtension

namespace TauCeti.GlobalNumberFields

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

private local instance (priority := 50) : Algebra K (FiniteAdeleRing (𝓞 L) L) :=
  Algebra.compHom _ (algebraMap K L)

private local instance (priority := 50) : IsScalarTower K L (FiniteAdeleRing (𝓞 L) L) :=
  IsScalarTower.of_algebraMap_eq' rfl

private local instance : IsScalarTower K (FiniteAdeleRing (𝓞 K) K)
    (FiniteAdeleRing (𝓞 L) L) :=
  IsScalarTower.of_algebraMap_eq fun x ↦ by
    rw [algebraMap_finiteAdeleExtensionAlgebra]
    exact (finiteAdeleExtension_algebraMap (𝓞 K) K (𝓞 L) L x).symm

/-- The canonical scalar-extension map of finite adeles over the finite adele ring of the
base field. -/
def finiteAdeleBaseChangeHom :
    FiniteAdeleRing (𝓞 K) K ⊗[K] L →ₐ[FiniteAdeleRing (𝓞 K) K]
      FiniteAdeleRing (𝓞 L) L :=
  Algebra.TensorProduct.lift (Algebra.ofId _ _)
    (IsScalarTower.toAlgHom K L (FiniteAdeleRing (𝓞 L) L)) fun _ _ ↦ .all _ _

/-- A pure tensor is sent to the extended adele times the diagonal field element. -/
@[simp]
theorem finiteAdeleBaseChangeHom_tmul (a : FiniteAdeleRing (𝓞 K) K) (x : L) :
    finiteAdeleBaseChangeHom K L (a ⊗ₜ x) =
      finiteAdeleExtension (𝓞 K) K (𝓞 L) L a *
        algebraMap L (FiniteAdeleRing (𝓞 L) L) x := by
  simp [finiteAdeleBaseChangeHom, Algebra.ofId_apply,
    algebraMap_finiteAdeleExtensionAlgebra]

/-- The component above `v` of the finite-adele comparison is the semilocal map after
scalar extension of evaluation at `v`. -/
@[simp]
theorem finiteAdeleBaseChangeHom_apply (s : FiniteAdeleRing (𝓞 K) K ⊗[K] L)
    (v : HeightOneSpectrum (𝓞 K))
    (w : {w : HeightOneSpectrum (𝓞 L) // w.asIdeal.LiesOver v.asIdeal}) :
    let f : FiniteAdeleRing (𝓞 K) K →ₗ[K] v.adicCompletion K :=
      { toFun := fun a ↦ a v
        map_add' := fun _ _ ↦ rfl
        map_smul' := fun c a ↦ by
          simp only [Algebra.smul_def, RingHom.id_apply]
          rfl }
    finiteAdeleBaseChangeHom K L s w.1 =
      semilocalHom L v (TensorProduct.map f (LinearMap.id : L →ₗ[K] L) s) w := by
  intro f
  induction s using TensorProduct.inductionOn with
  | tmul a x =>
    simp only [TensorProduct.map_tmul, LinearMap.id_apply, semilocalHom_tmul,
      finiteAdeleBaseChangeHom_tmul, FiniteAdeleRing.mul_apply,
      finiteAdeleExtension_apply, FiniteAdeleRing.algebraMap_apply]
    rcases w with ⟨w, hw⟩
    have hv : v = w.under (𝓞 K) := HeightOneSpectrum.asIdeal_injective hw.over
    subst v
    rw [HeightOneSpectrum.algebraMap_adicCompletionExtensionAlgebra]
    rfl
  | add t u ht hu =>
    simp only [map_add, Pi.add_apply]
    exact congrArg₂ (· + ·) ht hu

/-- The canonical scalar-extension map of finite adeles is injective. -/
theorem finiteAdeleBaseChangeHom_injective :
    Function.Injective (finiteAdeleBaseChangeHom K L) := by
  classical
  let b := Module.finBasis K L
  let B := b.baseChange (FiniteAdeleRing (𝓞 K) K)
  apply (injective_iff_map_eq_zero _).mpr
  intro t ht
  apply B.repr.injective
  apply Finsupp.ext
  intro i
  apply FiniteAdeleRing.ext
  intro v
  let f : FiniteAdeleRing (𝓞 K) K →ₗ[K] v.adicCompletion K :=
    { toFun := fun a ↦ a v
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun c a ↦ by
        simp only [Algebra.smul_def, RingHom.id_apply]
        rfl }
  let T := TensorProduct.map f (LinearMap.id : L →ₗ[K] L)
  -- A zero adelic image gives a zero tensor at `v` by semilocal injectivity.
  have hT : T t = 0 := by
    apply semilocalHom_injective L v
    funext w
    rw [← finiteAdeleBaseChangeHom_apply K L t v w, ht, map_zero]
    rfl
  -- Evaluation commutes with the scalar-extended basis coordinates.
  have hcoord (s : FiniteAdeleRing (𝓞 K) K ⊗[K] L) :
      (b.baseChange (v.adicCompletion K)).repr (T s) i = B.repr s i v := by
    induction s using TensorProduct.inductionOn with
    | tmul a x =>
      simp only [T, TensorProduct.map_tmul, LinearMap.id_apply, B,
        Module.Basis.baseChange_repr_tmul]
      exact (f.map_smul ((b.repr x) i) a).symm
    | add t u ht hu =>
      simp only [map_add, Finsupp.add_apply, ht, hu]
      rfl
  rw [← hcoord, hT]
  simp

variable [TopologicalSpace (FiniteAdeleRing (𝓞 K) K ⊗[K] L)]
  [IsModuleTopology (FiniteAdeleRing (𝓞 K) K) (FiniteAdeleRing (𝓞 K) K ⊗[K] L)]

/-- The canonical comparison is continuous for the module topology over the base finite
adele ring. -/
@[continuity, fun_prop]
theorem continuous_finiteAdeleBaseChangeHom : Continuous (finiteAdeleBaseChangeHom K L) := by
  let : ContinuousSMul (FiniteAdeleRing (𝓞 K) K) (FiniteAdeleRing (𝓞 L) L) :=
    continuousSMul_of_algebraMap _ _ (by
      rw [algebraMap_finiteAdeleExtensionAlgebra]
      exact continuous_finiteAdeleExtension (𝓞 K) K (𝓞 L) L)
  exact IsModuleTopology.continuous_of_linearMap (finiteAdeleBaseChangeHom K L).toLinearMap

end TauCeti.GlobalNumberFields
