/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.TensorProduct.Maps
public import TauCeti.RingTheory.Dagger.DaggerAlgebra.Map

import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.Topology.Baire.CompleteMetrizable
import TauCeti.RingTheory.Affinoid.FiniteMap
import TauCeti.RingTheory.Affinoid.Integral.Basic
import TauCeti.RingTheory.Dagger.DaggerAlgebra.FaithfullyFlat
import TauCeti.RingTheory.Dagger.DaggerAlgebra.ModuleTopology
import TauCeti.RingTheory.Huber.OpenMapping
import TauCeti.Topology.Algebra.Ring.Basic

/-!
# Finite morphisms of dagger algebras and their completions

Let `K` be a complete nontrivially normed ultrametric field and `φ : A → B` a finite morphism of
`K`-dagger algebras, with completions `τ_A : A → Â`, `τ_B : B → B̂` and completed morphism
`φ̂ = φ.daggerCompletionMap : Â → B̂`. Completion of a finite morphism is base change along `τ_A`:
the map `Â ⊗[A] B → B̂`, `x ⊗ b ↦ φ̂ x * τ_B b`, is an isomorphism
(`TauCeti.Dagger.completionTensorAlgEquiv`). Its inverse is the extension of `b ↦ 1 ⊗ b` to `B̂`
given by the universal property of `B̂`, which applies because `Â ⊗[A] B` is finite over the
affinoid algebra `Â`, hence itself affinoid. The isomorphism is `Â`-linear for the action of `Â`
on `B̂` through `φ̂` (`TauCeti.Dagger.completionTensorAlgEquiv_smul`).

Since `Â` is faithfully flat over `A` (`TauCeti.Dagger.faithfullyFlat_completionAlgebra`),
properties of `φ` are detected after this base change. For a finite morphism `φ` of dagger algebras:

* `φ̂` is finite (`AlgHom.Finite.daggerCompletionMap`);
* `φ̂` is injective iff `φ` is (`AlgHom.daggerCompletionMap_injective_iff`);
* `φ̂` is surjective iff `φ` is (`AlgHom.daggerCompletionMap_surjective_iff`), and likewise for
  bijectivity (`AlgHom.daggerCompletionMap_bijective_iff`).

Two of these implications hold without finiteness: if `φ̂` is injective then so is `φ`
(`AlgHom.injective_of_daggerCompletionMap_injective`), since `τ_A` is injective, and if `φ` is
surjective then so is `φ̂` (`AlgHom.daggerCompletionMap_surjective`), since a surjective morphism
is finite.

The isomorphism also compares topologies. Give `A` and `B` the topologies induced by `τ_A` and
`τ_B`, as in `TauCeti.RingTheory.Dagger.DaggerAlgebra.ModuleTopology`. Then the topology of a
finite `A`-algebra `B` is its `A`-module topology (`TauCeti.Dagger.isModuleTopology_of_isInducing`):
the `A`-module topology of `B` is induced from the `Â`-module topology of `Â ⊗[A] B`, which the
isomorphism identifies with the topology of the finite `Â`-module `B̂`. Consequently a finite
morphism `φ` is strict (`AlgHom.Finite.isStrictMap_of_isInducing`), and so is `φ̂`
(`AlgHom.isStrictMap_daggerCompletionMap`), by the open mapping theorem over the Tate ring `Â`.

## Main definitions

* `TauCeti.Dagger.completionTensorAlgEquiv`: for a finite `A`-algebra `B` that is a dagger algebra,
  the `K`-algebra isomorphism `Â ⊗[A] B ≃ₐ[K] B̂`.

## Main results

* `AlgHom.Finite.daggerCompletionMap`, `AlgHom.daggerCompletionMap_injective_iff`,
  `AlgHom.daggerCompletionMap_surjective_iff`, `AlgHom.daggerCompletionMap_bijective_iff`:
  finiteness, injectivity and surjectivity of a finite morphism and of its completion.
* `TauCeti.Dagger.isModuleTopology_of_isInducing`: a finite algebra carries its module topology.
* `AlgHom.Finite.isStrictMap_of_isInducing`, `AlgHom.isStrictMap_daggerCompletionMap`: a finite
  morphism and its completion are strict.

## References

* E. Grosse-Klönne, *Rigid analytic spaces with overconvergent structure sheaf*,
  J. reine angew. Math. 519 (2000), §1, Theorem 1.12 (a)–(e).
-/

public section

open scoped TensorProduct

namespace TauCeti.Dagger

section TensorEquiv

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B : Type*} [CommRing A] [Algebra K A] [IsDaggerAlgebra K A]
  [CommRing B] [Algebra K B] [IsDaggerAlgebra K B] [Algebra A B] [IsScalarTower K A B]

attribute [local instance] completionAlgebra

/-- The `A`-algebra structure on `completion K B` through `A → B → B̂`. -/
private noncomputable abbrev completionAlgebraOfTower : Algebra A (completion K B) :=
  ((toCompletion K B).toRingHom.comp (algebraMap A B)).toAlgebra

/-- The completed morphism `Â → B̂` of `A → B`, as an `A`-algebra homomorphism. -/
private noncomputable def daggerCompletionMapₐ :
    letI := completionAlgebraOfTower (K := K) (A := A) (B := B)
    completion K A →ₐ[A] completion K B :=
  letI := completionAlgebraOfTower (K := K) (A := A) (B := B)
  { (IsScalarTower.toAlgHom K A B).daggerCompletionMap with
    commutes' a := by simp [RingHom.algebraMap_toAlgebra] }

/-- The completion map of `B`, as an `A`-algebra homomorphism. -/
private noncomputable def toCompletionₐ :
    letI := completionAlgebraOfTower (K := K) (A := A) (B := B)
    B →ₐ[A] completion K B :=
  letI := completionAlgebraOfTower (K := K) (A := A) (B := B)
  { toCompletion K B with commutes' _ := rfl }

/-- The canonical `K`-algebra homomorphism `Â ⊗[A] B → B̂`, `x ⊗ b ↦ φ̂ x * τ_B b`. -/
private noncomputable def completionTensorToCompletion :
    completion K A ⊗[A] B →ₐ[K] completion K B :=
  letI := completionAlgebraOfTower (K := K) (A := A) (B := B)
  { (Algebra.TensorProduct.lift (daggerCompletionMapₐ (K := K)) (toCompletionₐ (K := K))
      fun _ _ ↦ Commute.all _ _).toRingHom with
    commutes' r := by simp [daggerCompletionMapₐ, toCompletionₐ] }

private theorem completionTensorToCompletion_tmul (x : completion K A) (b : B) :
    completionTensorToCompletion (x ⊗ₜ[A] b) =
      (IsScalarTower.toAlgHom K A B).daggerCompletionMap x * toCompletion K B b :=
  (rfl)

variable [Module.Finite A B]

omit [Algebra K B] [IsDaggerAlgebra K B] [IsScalarTower K A B] in
/-- A finite algebra over the completion of a dagger algebra is affinoid. -/
private theorem isAffinoidAlgebra_completion_tensor :
    IsAffinoidAlgebra K (completion K A ⊗[A] B) :=
  isAffinoidAlgebra_completion.of_finite (A := completion K A)

/-- The inverse `B̂ → Â ⊗[A] B` of `completionTensorToCompletion`, extending `b ↦ 1 ⊗ b`. -/
private noncomputable def completionToCompletionTensor :
    completion K B →ₐ[K] completion K A ⊗[A] B :=
  completionLift isAffinoidAlgebra_completion_tensor
    (Algebra.TensorProduct.includeRight.restrictScalars K)

private theorem completionToCompletionTensor_toCompletion (b : B) :
    completionToCompletionTensor (toCompletion K B b) = (1 : completion K A) ⊗ₜ[A] b := by
  simp [completionToCompletionTensor]

private theorem completionToCompletionTensor_daggerCompletionMap (x : completion K A) :
    completionToCompletionTensor ((IsScalarTower.toAlgHom K A B).daggerCompletionMap x) =
      x ⊗ₜ[A] (1 : B) := by
  have h := completion_algHom_ext_of_isAffinoidAlgebra isAffinoidAlgebra_completion_tensor
    (Φ₁ := completionToCompletionTensor.comp (IsScalarTower.toAlgHom K A B).daggerCompletionMap)
    (Φ₂ := Algebra.TensorProduct.includeLeft) fun a ↦ by
      simp [completionToCompletionTensor_toCompletion, ← Algebra.TensorProduct.algebraMap_apply']
  exact DFunLike.congr_fun h x

variable (K A B) in
/-- **Completion of a finite morphism is base change.** For a finite `A`-algebra `B` with `A` and
`B` dagger algebras, the map `Â ⊗[A] B → B̂`, `x ⊗ b ↦ φ̂ x * τ_B b`, is a `K`-algebra isomorphism,
where `φ̂` is the completion of the structure map `A → B`. -/
noncomputable def completionTensorAlgEquiv :
    letI := completionAlgebra K A
    completion K A ⊗[A] B ≃ₐ[K] completion K B :=
  AlgEquiv.ofAlgHom completionTensorToCompletion completionToCompletionTensor
    (completion_algHom_ext fun b ↦ by
      simp [completionToCompletionTensor_toCompletion, completionTensorToCompletion_tmul])
    (AlgHom.ext fun t ↦ by
      induction t with
      | tmul x b =>
        have hx : x ⊗ₜ[A] b = x ⊗ₜ[A] (1 : B) * (1 : completion K A) ⊗ₜ[A] b := by simp
        simp [completionTensorToCompletion_tmul, completionToCompletionTensor_daggerCompletionMap,
          completionToCompletionTensor_toCompletion, ← hx]
      | add t₁ t₂ h₁ h₂ => simp_all)

/-- `completionTensorAlgEquiv` sends `x ⊗ b` to `φ̂ x * τ_B b`. -/
@[simp]
theorem completionTensorAlgEquiv_tmul (x : completion K A) (b : B) :
    completionTensorAlgEquiv K A B (x ⊗ₜ[A] b) =
      (IsScalarTower.toAlgHom K A B).daggerCompletionMap x * toCompletion K B b :=
  completionTensorToCompletion_tmul x b

/-- The inverse of `completionTensorAlgEquiv` sends `τ_B b` to `1 ⊗ b`. -/
@[simp]
theorem completionTensorAlgEquiv_symm_toCompletion (b : B) :
    (completionTensorAlgEquiv K A B).symm (toCompletion K B b) = (1 : completion K A) ⊗ₜ[A] b :=
  completionToCompletionTensor_toCompletion (K := K) (A := A) b

/-- The inverse of `completionTensorAlgEquiv` sends `φ̂ x` to `x ⊗ 1`. -/
@[simp]
theorem completionTensorAlgEquiv_symm_daggerCompletionMap (x : completion K A) :
    (completionTensorAlgEquiv K A B).symm ((IsScalarTower.toAlgHom K A B).daggerCompletionMap x) =
      x ⊗ₜ[A] (1 : B) :=
  completionToCompletionTensor_daggerCompletionMap x

/-- `completionTensorAlgEquiv` is compatible with the `completion K A`-actions: it sends
`x • t` to `φ̂ x * e t`, where `e` is the isomorphism, so it is `Â`-linear for the action on `B̂`
through `φ̂`. -/
@[simp]
theorem completionTensorAlgEquiv_smul (x : completion K A) (t : completion K A ⊗[A] B) :
    completionTensorAlgEquiv K A B (x • t) =
      (IsScalarTower.toAlgHom K A B).daggerCompletionMap x * completionTensorAlgEquiv K A B t := by
  induction t with
  | tmul y b => simp [TensorProduct.smul_tmul', mul_assoc]
  | add t₁ t₂ h₁ h₂ => rw [smul_add, map_add, map_add, h₁, h₂, mul_add]

/-- The completed structure map `Â → B̂` factors as `x ↦ x ⊗ 1` followed by
`completionTensorAlgEquiv`. -/
private theorem daggerCompletionMap_eq_comp_includeLeft :
    ⇑(IsScalarTower.toAlgHom K A B).daggerCompletionMap =
      completionTensorAlgEquiv K A B ∘ (Algebra.linearMap A B).lTensor (completion K A) ∘
        (TensorProduct.rid A (completion K A)).symm := by
  ext x
  simp

/-- The completion of the structure map of a finite `A`-algebra is finite. -/
private theorem finite_daggerCompletionMap_toAlgHom :
    (IsScalarTower.toAlgHom K A B).daggerCompletionMap.Finite := by
  have h : (IsScalarTower.toAlgHom K A B).daggerCompletionMap.toRingHom =
      (completionTensorAlgEquiv K A B).toRingEquiv.toRingHom.comp
        (algebraMap (completion K A) (completion K A ⊗[A] B)) :=
    RingHom.ext fun x ↦ by simp
  have hf : RingHom.Finite (A := completion K A) (B := completion K A ⊗[A] B)
      (algebraMap (completion K A) (completion K A ⊗[A] B)) :=
    RingHom.finite_algebraMap.mpr (Module.Finite.base_change A (completion K A) B)
  unfold AlgHom.Finite
  rw [h]
  exact (RingHom.Finite.of_surjective _ (completionTensorAlgEquiv K A B).surjective).comp hf

private theorem daggerCompletionMap_toAlgHom_injective_iff :
    Function.Injective (IsScalarTower.toAlgHom K A B).daggerCompletionMap ↔
      Function.Injective (algebraMap A B) := by
  have := faithfullyFlat_completionAlgebra (K := K) (A := A)
  rw [daggerCompletionMap_eq_comp_includeLeft,
    (completionTensorAlgEquiv K A B).injective.of_comp_iff,
    Function.Injective.of_comp_iff' _ (TensorProduct.rid A (completion K A)).symm.bijective]
  exact Module.FaithfullyFlat.lTensor_injective_iff_injective A _ (Algebra.linearMap A B)

private theorem daggerCompletionMap_toAlgHom_surjective_iff :
    Function.Surjective (IsScalarTower.toAlgHom K A B).daggerCompletionMap ↔
      Function.Surjective (algebraMap A B) := by
  have := faithfullyFlat_completionAlgebra (K := K) (A := A)
  rw [daggerCompletionMap_eq_comp_includeLeft,
    Function.Surjective.of_comp_iff' (completionTensorAlgEquiv K A B).bijective,
    Function.Surjective.of_comp_iff _ (TensorProduct.rid A (completion K A)).symm.surjective]
  exact Module.FaithfullyFlat.lTensor_surjective_iff_surjective A _ (Algebra.linearMap A B)

end TensorEquiv

section Topology

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B : Type*} [CommRing A] [Algebra K A] [IsDaggerAlgebra K A]
  [CommRing B] [Algebra K B] [IsDaggerAlgebra K B] [Algebra A B] [IsScalarTower K A B]
  [Module.Finite A B]

attribute [local instance] completionAlgebra

/-- The `completion K A`-algebra structure on `completion K B` through the completed structure
map. -/
private noncomputable abbrev completionAlgebraOfMap : Algebra (completion K A) (completion K B) :=
  (IsScalarTower.toAlgHom K A B).daggerCompletionMap.toAlgebra

/-- `completionTensorAlgEquiv` as a `completion K A`-linear equivalence. -/
private noncomputable def completionTensorLinearEquiv :
    letI := completionAlgebraOfMap (K := K) (A := A) (B := B)
    completion K A ⊗[A] B ≃ₗ[completion K A] completion K B :=
  letI := completionAlgebraOfMap (K := K) (A := A) (B := B)
  { (completionTensorAlgEquiv K A B).toRingEquiv with
    map_smul' x t := by simp [Algebra.smul_def, RingHom.algebraMap_toAlgebra] }

/-- The `completion K A`-module topology on `completion K B` is its own topology. -/
private theorem isModuleTopology_completionAlgebraOfMap :
    letI := completionAlgebraOfMap (K := K) (A := A) (B := B)
    IsModuleTopology (completion K A) (completion K B) :=
  letI := completionAlgebraOfMap (K := K) (A := A) (B := B)
  have : Module.Finite (completion K A) (completion K B) := finite_daggerCompletionMap_toAlgHom
  have : ContinuousSMul (completion K A) (completion K B) :=
    continuousSMul_of_algebraMap _ _
      (IsScalarTower.toAlgHom K A B).continuous_daggerCompletionMap
  have := Huber.IsTateRing.of_normedAlgebra K (completion K A)
  -- Instance search fails to unify the topology of `completion K B` with the one coming from its
  -- seminormed ring structure, so the metrizability instance is passed by name.
  have : BaireSpace (completion K B) :=
    @BaireSpace.of_completelyPseudoMetrizable _ _
      (PseudoMetricSpace.toIsCompletelyPseudoMetrizableSpace (X := completion K B))
  Huber.IsTateRing.isModuleTopology (A := completion K A) (M := completion K B)

/-- The `A`-module topology on a finite `A`-algebra `B` is induced by `toCompletion K B`. -/
private theorem moduleTopology_eq_induced_toCompletion [TopologicalSpace A]
    (hA : Topology.IsInducing (toCompletion K A)) :
    moduleTopology A B = TopologicalSpace.induced (toCompletion K B) inferInstance := by
  let := completionAlgebraOfMap (K := K) (A := A) (B := B)
  let : TopologicalSpace (completion K A ⊗[A] B) :=
    moduleTopology (completion K A) (completion K A ⊗[A] B)
  have : IsModuleTopology (completion K A) (completion K A ⊗[A] B) := ⟨rfl⟩
  have := isModuleTopology_completionAlgebraOfMap (K := K) (A := A) (B := B)
  have := IsModuleTopology.toContinuousAdd (completion K A) (completion K A ⊗[A] B)
  let e := completionTensorLinearEquiv (K := K) (A := A) (B := B)
  -- `e` is a homeomorphism, both sides carrying their `completion K A`-module topologies.
  let h : completion K A ⊗[A] B ≃ₜ completion K B :=
    { e.toEquiv with
      continuous_toFun := IsModuleTopology.continuous_of_linearMap e.toLinearMap
      continuous_invFun := IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap }
  let : TopologicalSpace B := moduleTopology A B
  have : IsModuleTopology A B := ⟨rfl⟩
  have hemb := isEmbedding_toCompletionTensor (K := K) (A := A) (M := B) hA
  have hcomp : (h ∘ toCompletionTensor K A B : B → completion K B) = toCompletion K B := by
    ext b
    simp [h, e, completionTensorLinearEquiv]
  exact (hcomp ▸ h.isEmbedding.comp hemb).eq_induced

/-- **A finite algebra carries its module topology** (Grosse-Klönne, Theorem 1.12 (d)). If the
dagger algebras `A` and `B` carry the topologies induced by their completion maps and `B` is finite
over `A`, then the topology of `B` is the `A`-module topology. -/
theorem isModuleTopology_of_isInducing [TopologicalSpace A] [TopologicalSpace B]
    (hA : Topology.IsInducing (toCompletion K A)) (hB : Topology.IsInducing (toCompletion K B)) :
    IsModuleTopology A B :=
  ⟨hB.eq_induced.trans (moduleTopology_eq_induced_toCompletion hA).symm⟩

/-- The structure map of a finite algebra is strict for the topologies induced by the completion
maps of the dagger algebras `A` and `B`. -/
private theorem isStrictMap_algebraMap_of_isInducing [TopologicalSpace A] [TopologicalSpace B]
    (hA : Topology.IsInducing (toCompletion K A)) (hB : Topology.IsInducing (toCompletion K B)) :
    Topology.IsStrictMap (algebraMap A B) :=
  have := isModuleTopology_of_isInducing hA hB
  have : IsTopologicalRing A := hA.isTopologicalRing (toCompletion K A)
  isStrictMap_of_linearMap hA (Algebra.linearMap A B)

end Topology

end TauCeti.Dagger

namespace AlgHom

open TauCeti TauCeti.Dagger

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B : Type*} [CommRing A] [Algebra K A] [IsDaggerAlgebra K A]
  [CommRing B] [Algebra K B] [IsDaggerAlgebra K B] {φ : A →ₐ[K] B}

/-- A morphism of dagger algebras is injective if its completion is, since `A → Â` is injective. -/
theorem injective_of_daggerCompletionMap_injective
    (h : Function.Injective φ.daggerCompletionMap) : Function.Injective φ := fun x y hxy ↦
  toCompletion_injective (K := K) (A := A) <| h <| by simp [hxy]

/-- **The completion of a finite morphism of dagger algebras is finite.** -/
theorem Finite.daggerCompletionMap (hφ : φ.Finite) : φ.daggerCompletionMap.Finite := by
  let := φ.toAlgebra
  let := IsScalarTower.of_algHom φ
  have : Module.Finite A B := hφ
  -- Under `φ.toAlgebra`, `IsScalarTower.toAlgHom K A B` and `algebraMap A B` are `φ` by definition.
  exact finite_daggerCompletionMap_toAlgHom (K := K) (A := A) (B := B)

/-- **A finite morphism of dagger algebras is injective iff its completion is.** -/
theorem daggerCompletionMap_injective_iff (hφ : φ.Finite) :
    Function.Injective φ.daggerCompletionMap ↔ Function.Injective φ := by
  let := φ.toAlgebra
  let := IsScalarTower.of_algHom φ
  have : Module.Finite A B := hφ
  exact daggerCompletionMap_toAlgHom_injective_iff (K := K) (A := A) (B := B)

/-- **A finite morphism of dagger algebras is surjective iff its completion is.** -/
theorem daggerCompletionMap_surjective_iff (hφ : φ.Finite) :
    Function.Surjective φ.daggerCompletionMap ↔ Function.Surjective φ := by
  let := φ.toAlgebra
  let := IsScalarTower.of_algHom φ
  have : Module.Finite A B := hφ
  exact daggerCompletionMap_toAlgHom_surjective_iff (K := K) (A := A) (B := B)

/-- **A finite morphism of dagger algebras is bijective iff its completion is.** -/
theorem daggerCompletionMap_bijective_iff (hφ : φ.Finite) :
    Function.Bijective φ.daggerCompletionMap ↔ Function.Bijective φ :=
  and_congr (daggerCompletionMap_injective_iff hφ) (daggerCompletionMap_surjective_iff hφ)

/-- **The completion of a finite morphism of dagger algebras is strict** (Grosse-Klönne,
Theorem 1.12 (e)). -/
theorem isStrictMap_daggerCompletionMap (hφ : φ.Finite) :
    Topology.IsStrictMap φ.daggerCompletionMap :=
  have := (isAffinoidAlgebra_completion (K := K) (A := A)).isNoetherianRing
  IsAffinoidAlgebra.isStrictMap_of_finite (K := K) (A := completion K A) (B := completion K B)
    isAffinoidAlgebra_completion φ.daggerCompletionMap hφ.daggerCompletionMap

/-- **A finite morphism of dagger algebras is strict** (Grosse-Klönne, Theorem 1.12 (e)), for the
topologies induced by the completion maps. -/
theorem Finite.isStrictMap_of_isInducing [TopologicalSpace A] [TopologicalSpace B]
    (hφ : φ.Finite) (hA : Topology.IsInducing (toCompletion K A))
    (hB : Topology.IsInducing (toCompletion K B)) : Topology.IsStrictMap φ := by
  let := φ.toAlgebra
  let := IsScalarTower.of_algHom φ
  have : Module.Finite A B := hφ
  exact isStrictMap_algebraMap_of_isInducing (K := K) hA hB

/-- The completion of a surjective morphism of dagger algebras is surjective. -/
theorem daggerCompletionMap_surjective (hφ : Function.Surjective φ) :
    Function.Surjective φ.daggerCompletionMap :=
  (daggerCompletionMap_surjective_iff (AlgHom.Finite.of_surjective φ hφ)).mpr hφ

end AlgHom
