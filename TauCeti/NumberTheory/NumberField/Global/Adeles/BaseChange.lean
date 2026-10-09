/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Global.Adeles.FiniteBaseChange
public import TauCeti.NumberTheory.NumberField.Global.Adeles.InfiniteBaseChange
public import Mathlib.LinearAlgebra.TensorProduct.Prod
import Mathlib.LinearAlgebra.Countable
import TauCeti.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.Algebra.Group.OpenMapping
import Mathlib.Topology.Baire.LocallyCompactRegular
import TauCeti.NumberTheory.NumberField.Global.Adeles.LocallyCompact

/-!
# Base change of adeles

The canonical map `𝔸_K ⊗[K] L → 𝔸_L` for number fields `L/K` is an algebra equivalence over
`𝔸_K`. Its finite and infinite components are the corresponding local scalar-extension maps,
after distributing the tensor product over the product defining `𝔸_K`. When the source has its
module topology over `𝔸_K`, the map is a homeomorphism.

Bijectivity combines the finite-adele comparison `finiteAdeleBaseChangeAlgEquiv` with the
archimedean comparison `infiniteAdeleBaseChangeAlgEquiv`. The inverse is continuous by the open
mapping theorem for σ-compact groups.

## Main definitions

* `TauCeti.GlobalNumberFields.adeleBaseChangeHom`: the canonical map
  `𝔸_K ⊗[K] L →ₐ[𝔸_K] 𝔸_L`.
* `TauCeti.GlobalNumberFields.adeleBaseChangeAlgEquiv`: that map as an algebra equivalence.
* `TauCeti.GlobalNumberFields.adeleBaseChangeEquiv`: that map as a continuous algebra
  equivalence, for the module topology on the source.

## Main results

* `TauCeti.GlobalNumberFields.adeleBaseChangeHom_fst`,
  `TauCeti.GlobalNumberFields.adeleBaseChangeHom_snd`: the infinite and finite components are
  the infinite- and finite-adele comparisons.
* `TauCeti.GlobalNumberFields.adeleBaseChangeHom_bijective`: the map is bijective.
* `TauCeti.GlobalNumberFields.adeleBaseChangeEquiv_tmul_one`,
  `TauCeti.GlobalNumberFields.adeleBaseChangeEquiv_apply_prod`: the continuous comparison
  extends `𝔸_K → 𝔸_L` and is the product of the infinite- and finite-adele comparisons.
* `TauCeti.GlobalNumberFields.adeleBaseChangeEquiv_tower`: in a tower `K ⊆ L ⊆ M`, base change
  from `K` to `M` factors through base change from `K` to `L`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter II, Proposition (8.3).
* J. W. S. Cassels and A. Fröhlich, eds., *Algebraic Number Theory*, Chapter II, §14.
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

/-- The canonical scalar-extension map of full adeles is surjective. -/
theorem adeleBaseChangeHom_surjective : Function.Surjective (adeleBaseChangeHom K L) := by
  intro y
  obtain ⟨t₁, ht₁⟩ := (infiniteAdeleBaseChangeHom_bijective K L).surjective y.1
  obtain ⟨t₂, ht₂⟩ := finiteAdeleBaseChangeHom_surjective K L y.2
  -- Type the distribution map on adeles: rewriting cannot unfold their type synonym
  -- at instances transparency.
  let e : AdeleRing (𝓞 K) K ⊗[K] L ≃ₗ[K]
      (InfiniteAdeleRing K ⊗[K] L) × (FiniteAdeleRing (𝓞 K) K ⊗[K] L) :=
    TensorProduct.prodLeft K K _ _ L
  obtain ⟨t, ht⟩ := e.surjective (t₁, t₂)
  refine ⟨t, Prod.ext ?_ ?_⟩
  · rw [adeleBaseChangeHom_fst, ← ht₁]
    exact congrArg (fun p ↦ infiniteAdeleBaseChangeHom K L p.1) ht
  · rw [adeleBaseChangeHom_snd, ← ht₂]
    exact congrArg (fun p ↦ finiteAdeleBaseChangeHom K L p.2) ht

/-- The canonical scalar-extension map of full adeles is bijective. -/
theorem adeleBaseChangeHom_bijective : Function.Bijective (adeleBaseChangeHom K L) :=
  ⟨adeleBaseChangeHom_injective K L, adeleBaseChangeHom_surjective K L⟩

/-- Base change of adeles is an algebra equivalence over the adele ring of the base field,
independently of a topology on the tensor product. -/
def adeleBaseChangeAlgEquiv :
    AdeleRing (𝓞 K) K ⊗[K] L ≃ₐ[AdeleRing (𝓞 K) K] AdeleRing (𝓞 L) L :=
  AlgEquiv.ofBijective (adeleBaseChangeHom K L) (adeleBaseChangeHom_bijective K L)

/-- Forgetting invertibility recovers the canonical base-change homomorphism. -/
@[simp]
theorem adeleBaseChangeAlgEquiv_toAlgHom :
    (adeleBaseChangeAlgEquiv K L).toAlgHom = adeleBaseChangeHom K L :=
  (rfl)

/-- The algebraic inverse comparison sends a diagonal field element to `1 ⊗ x`. -/
@[simp]
theorem adeleBaseChangeAlgEquiv_symm_algebraMap (x : L) :
    (adeleBaseChangeAlgEquiv K L).symm (algebraMap L (AdeleRing (𝓞 L) L) x) = 1 ⊗ₜ[K] x := by
  apply (adeleBaseChangeAlgEquiv K L).injective
  simp [adeleBaseChangeAlgEquiv]

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

/-- **Base change of adeles** is a continuous algebra equivalence `𝔸_K ⊗[K] L ≃A[𝔸_K] 𝔸_L`
over the adele ring of the base field, for the module topology on the source. -/
def adeleBaseChangeEquiv :
    AdeleRing (𝓞 K) K ⊗[K] L ≃A[AdeleRing (𝓞 K) K] AdeleRing (𝓞 L) L := by
  let e := adeleBaseChangeAlgEquiv K L
  have hc : Continuous e := continuous_adeleBaseChangeHom K L
  -- The tensor product is σ-compact, as a finite free module over a σ-compact ring. The
  -- additive open mapping theorem then gives the inverse.
  letI := IsModuleTopology.isTopologicalAddGroup (AdeleRing (𝓞 K) K) (AdeleRing (𝓞 K) K ⊗[K] L)
  have : Countable (𝓞 K) := Finsupp.Countable.of_moduleFinite (R := ℤ)
  letI := TauCeti.ModuleTopology.sigmaCompactSpace
    ((Module.finBasis K L).baseChange (AdeleRing (𝓞 K) K))
  have ho : IsOpenMap e := e.toAddMonoidHom.isOpenMap_of_sigmaCompact e.surjective hc
  exact
    { toAlgEquiv := e
      continuous_toFun := hc
      continuous_invFun := (e.toEquiv.toHomeomorphOfContinuousOpen hc ho).symm.continuous }

/-- Forgetting continuity recovers the algebraic base-change equivalence. -/
@[simp]
theorem adeleBaseChangeEquiv_toAlgEquiv :
    (adeleBaseChangeEquiv K L).toAlgEquiv = adeleBaseChangeAlgEquiv K L :=
  (rfl)

/-- The continuous comparison sends a pure tensor to the extended adele times the diagonal
field element. -/
@[simp]
theorem adeleBaseChangeEquiv_tmul (a : AdeleRing (𝓞 K) K) (x : L) :
    adeleBaseChangeEquiv K L (a ⊗ₜ x) =
      adeleExtension (𝓞 K) K (𝓞 L) L a * algebraMap L (AdeleRing (𝓞 L) L) x := by
  have h : (adeleBaseChangeEquiv K L).toAlgHom = adeleBaseChangeHom K L := by simp
  exact (AlgHom.congr_fun h (a ⊗ₜ[K] x)).trans (adeleBaseChangeHom_tmul K L a x)

/-- The continuous comparison restricts on `𝔸_K ⊗ 1` to the extension map `𝔸_K → 𝔸_L`. -/
theorem adeleBaseChangeEquiv_tmul_one (a : AdeleRing (𝓞 K) K) :
    adeleBaseChangeEquiv K L (a ⊗ₜ 1) = adeleExtension (𝓞 K) K (𝓞 L) L a := by
  rw [adeleBaseChangeEquiv_tmul, map_one, mul_one]

/-- The continuous comparison is the pair of the infinite- and finite-adele comparisons, after
splitting the source tensor product into its two components. -/
theorem adeleBaseChangeEquiv_apply_prod (t : AdeleRing (𝓞 K) K ⊗[K] L) :
    adeleBaseChangeEquiv K L t =
      ((infiniteAdeleBaseChangeAlgEquiv K L
          (TensorProduct.prodLeft K K (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K) L t).1,
        finiteAdeleBaseChangeAlgEquiv K L
          (TensorProduct.prodLeft K K (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K) L t).2) :
        AdeleRing (𝓞 L) L) := by
  have h : (adeleBaseChangeEquiv K L).toAlgHom = adeleBaseChangeHom K L := by simp
  -- Rewriting cannot see through the adele type synonym, so chain the equalities instead.
  exact (AlgHom.congr_fun h t).trans <| Prod.ext
    ((adeleBaseChangeHom_fst K L t).trans
      (AlgHom.congr_fun (infiniteAdeleBaseChangeAlgEquiv_toAlgHom K L) _).symm)
    ((adeleBaseChangeHom_snd K L t).trans
      (AlgHom.congr_fun (finiteAdeleBaseChangeAlgEquiv_toAlgHom K L) _).symm)

/-- The inverse comparison sends a diagonal field element to `1 ⊗ x`. -/
@[simp]
theorem adeleBaseChangeEquiv_symm_algebraMap (x : L) :
    (adeleBaseChangeEquiv K L).symm (algebraMap L (AdeleRing (𝓞 L) L) x) = 1 ⊗ₜ[K] x :=
  adeleBaseChangeAlgEquiv_symm_algebraMap K L x

/-- **Base change of adeles in a tower** `K ⊆ L ⊆ M`: the comparison for `M/K` factors through
the comparison for `L/K`, followed by the comparison for `M/L`. -/
theorem adeleBaseChangeEquiv_tower (M : Type*) [Field M] [NumberField M] [Algebra K M]
    [Algebra L M] [IsScalarTower K L M] [TopologicalSpace (AdeleRing (𝓞 K) K ⊗[K] M)]
    [IsModuleTopology (AdeleRing (𝓞 K) K) (AdeleRing (𝓞 K) K ⊗[K] M)]
    [TopologicalSpace (AdeleRing (𝓞 L) L ⊗[L] M)]
    [IsModuleTopology (AdeleRing (𝓞 L) L) (AdeleRing (𝓞 L) L ⊗[L] M)]
    (a : AdeleRing (𝓞 K) K) (z : M) :
    adeleBaseChangeEquiv K M (a ⊗ₜ z) =
      adeleBaseChangeEquiv L M (adeleBaseChangeEquiv K L (a ⊗ₜ 1) ⊗ₜ z) := by
  rw [adeleBaseChangeEquiv_tmul, adeleBaseChangeEquiv_tmul_one, adeleBaseChangeEquiv_tmul,
    ← adeleExtension_comp (𝓞 K) K (𝓞 L) L (𝓞 M) M, RingHom.comp_apply]

end TauCeti.GlobalNumberFields
