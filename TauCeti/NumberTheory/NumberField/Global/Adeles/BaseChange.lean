/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Global.Adeles.FiniteBaseChange
public import TauCeti.NumberTheory.NumberField.Global.Adeles.InfiniteBaseChange
public import Mathlib.LinearAlgebra.TensorProduct.Prod

/-!
# The scalar-extension map of adeles

The canonical map `𝔸_K ⊗[K] L → 𝔸_L` for number fields `L/K` is an injective algebra
homomorphism over `𝔸_K`. Its finite and infinite components are the corresponding local
scalar-extension maps, after distributing the tensor product over the product defining `𝔸_K`.
The map is continuous when the source has its module topology over `𝔸_K`.

Injectivity combines `finiteAdeleBaseChangeHom_injective` with the existing bijective
archimedean comparison `infiniteAdeleBaseChangeHom`. This file does not assert surjectivity
or a topological equivalence.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter II, Proposition (8.3).
-/

public section
noncomputable section

open IsDedekindDomain NumberField
open scoped TensorProduct AdeleExtension InfiniteAdeleExtension FiniteAdeleExtension

namespace TauCeti.GlobalNumberFields

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

private local instance (priority := 50) : Algebra K (AdeleRing (𝓞 L) L) :=
  Algebra.compHom _ (algebraMap K L)

private local instance (priority := 50) : IsScalarTower K L (AdeleRing (𝓞 L) L) :=
  IsScalarTower.of_algebraMap_eq' rfl

private local instance : IsScalarTower K (AdeleRing (𝓞 K) K) (AdeleRing (𝓞 L) L) :=
  IsScalarTower.of_algebraMap_eq fun x ↦ by
    rw [algebraMap_adeleExtensionAlgebra]
    exact (adeleExtension_algebraMap (𝓞 K) K (𝓞 L) L x).symm

/-- The canonical scalar-extension map of full adeles over the adele ring of the base field. -/
def adeleBaseChangeHom :
    AdeleRing (𝓞 K) K ⊗[K] L →ₐ[AdeleRing (𝓞 K) K] AdeleRing (𝓞 L) L :=
  Algebra.TensorProduct.lift (Algebra.ofId _ _)
    (IsScalarTower.toAlgHom K L (AdeleRing (𝓞 L) L)) fun _ _ ↦ .all _ _

/-- A pure tensor maps to the extended adele times the diagonal field element. -/
@[simp]
theorem adeleBaseChangeHom_tmul (a : AdeleRing (𝓞 K) K) (x : L) :
    adeleBaseChangeHom K L (a ⊗ₜ x) =
      adeleExtension (𝓞 K) K (𝓞 L) L a * algebraMap L (AdeleRing (𝓞 L) L) x := by
  simp [adeleBaseChangeHom, Algebra.ofId_apply, algebraMap_adeleExtensionAlgebra]

/-- The infinite component of the full comparison is the infinite-adele comparison after
splitting the source tensor product into its two components. -/
@[simp]
theorem adeleBaseChangeHom_fst (t : AdeleRing (𝓞 K) K ⊗[K] L) :
    (adeleBaseChangeHom K L t).1 = infiniteAdeleBaseChangeHom K L
      ((TensorProduct.prodLeft K K (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K) L t).1) := by
  induction t using TensorProduct.inductionOn with
  | tmul a x =>
    rw [adeleBaseChangeHom_tmul, AdeleRing.fst_mul, adeleExtension_fst,
      AdeleRing.algebraMap_fst]
    exact (infiniteAdeleBaseChangeHom_tmul K L a.1 x).symm
  | add t u ht hu =>
    -- Type the distribution map on adeles: rewriting cannot unfold their type synonym
    -- at instances transparency.
    let e : AdeleRing (𝓞 K) K ⊗[K] L ≃ₗ[K]
        (InfiniteAdeleRing K ⊗[K] L) × (FiniteAdeleRing (𝓞 K) K ⊗[K] L) :=
      TensorProduct.prodLeft K K _ _ L
    calc
      _ = (adeleBaseChangeHom K L t).1 + (adeleBaseChangeHom K L u).1 :=
        congrArg Prod.fst (map_add _ t u)
      _ = infiniteAdeleBaseChangeHom K L (e t).1 +
          infiniteAdeleBaseChangeHom K L (e u).1 := congrArg₂ (· + ·) ht hu
      _ = _ := (map_add _ _ _).symm.trans
        (congrArg (fun p ↦ infiniteAdeleBaseChangeHom K L p.1) (e.map_add t u)).symm

/-- The finite component of the full comparison is the finite-adele comparison after
splitting the source tensor product into its two components. -/
@[simp]
theorem adeleBaseChangeHom_snd (t : AdeleRing (𝓞 K) K ⊗[K] L) :
    (adeleBaseChangeHom K L t).2 = finiteAdeleBaseChangeHom K L
      ((TensorProduct.prodLeft K K (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K) L t).2) := by
  induction t using TensorProduct.inductionOn with
  | tmul a x =>
    rw [adeleBaseChangeHom_tmul]
    -- The adele type synonym hides the product-ring second projection from rewriting.
    change (adeleExtension (𝓞 K) K (𝓞 L) L a).2 *
      (algebraMap L (AdeleRing (𝓞 L) L) x).2 = _
    rw [adeleExtension_snd, AdeleRing.algebraMap_snd]
    exact (finiteAdeleBaseChangeHom_tmul K L a.2 x).symm
  | add t u ht hu =>
    -- Type the distribution map on adeles: rewriting cannot unfold their type synonym
    -- at instances transparency.
    let e : AdeleRing (𝓞 K) K ⊗[K] L ≃ₗ[K]
        (InfiniteAdeleRing K ⊗[K] L) × (FiniteAdeleRing (𝓞 K) K ⊗[K] L) :=
      TensorProduct.prodLeft K K _ _ L
    calc
      _ = (adeleBaseChangeHom K L t).2 + (adeleBaseChangeHom K L u).2 :=
        congrArg Prod.snd (map_add _ t u)
      _ = finiteAdeleBaseChangeHom K L (e t).2 +
          finiteAdeleBaseChangeHom K L (e u).2 := congrArg₂ (· + ·) ht hu
      _ = _ := (map_add _ _ _).symm.trans
        (congrArg (fun p ↦ finiteAdeleBaseChangeHom K L p.2) (e.map_add t u)).symm

/-- The canonical scalar-extension map of full adeles is injective. -/
theorem adeleBaseChangeHom_injective : Function.Injective (adeleBaseChangeHom K L) := by
  intro t u h
  apply (TensorProduct.prodLeft K K (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K) L).injective
  apply Prod.ext
  · apply (infiniteAdeleBaseChangeHom_bijective K L).injective
    simpa only [adeleBaseChangeHom_fst] using congrArg Prod.fst h
  · apply finiteAdeleBaseChangeHom_injective K L
    simpa only [adeleBaseChangeHom_snd] using congrArg Prod.snd h

variable [TopologicalSpace (AdeleRing (𝓞 K) K ⊗[K] L)]
  [IsModuleTopology (AdeleRing (𝓞 K) K) (AdeleRing (𝓞 K) K ⊗[K] L)]

/-- The canonical full-adele comparison is continuous for the module topology over the base
adele ring. -/
@[continuity, fun_prop]
theorem continuous_adeleBaseChangeHom : Continuous (adeleBaseChangeHom K L) := by
  let : ContinuousSMul (AdeleRing (𝓞 K) K) (AdeleRing (𝓞 L) L) :=
    continuousSMul_of_algebraMap _ _ (by
      rw [algebraMap_adeleExtensionAlgebra]
      exact continuous_adeleExtension (𝓞 K) K (𝓞 L) L)
  exact IsModuleTopology.continuous_of_linearMap (adeleBaseChangeHom K L).toLinearMap

end TauCeti.GlobalNumberFields
