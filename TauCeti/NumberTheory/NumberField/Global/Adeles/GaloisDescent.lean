/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Global.Adeles.BaseChange
public import TauCeti.NumberTheory.NumberField.Global.Adeles.GaloisAction
import Mathlib.RingTheory.Flat.Basic
import TauCeti.RepresentationTheory.GaloisDescent.Range

/-!
# Galois descent for adeles

For an extension of number fields `L/K`, the extension map `𝔸_K → 𝔸_L` is injective
(`adeleExtension_injective`). When `L/K` is Galois, its image is the set of adeles of `L` fixed by
`Gal(L/K)` (`mem_range_adeleExtension_iff`):

```text
𝔸_K = (𝔸_L)^{Gal(L/K)}.
```

Both statements are read off the base change `𝔸_K ⊗[K] L ≃ 𝔸_L`
(`adeleBaseChangeHom_bijective`). For injectivity, `𝔸_K → 𝔸_K ⊗[K] L` is injective because `L`
is flat over `K`. For the image, `Gal(L/K)` acts semilinearly on `𝔸_L`, fixes the extended adeles,
and the scalar extension `L ⊗[K] 𝔸_K → 𝔸_L` of the extension map is surjective, so its image is
all the invariants by `TauCeti.GaloisDescent.range_eq_invariants_of_liftBaseChange_surjective`.

These are the adelic input to Galois descent for the ideles of a separable closure, where the
ideles of a finite Galois subextension are recovered as the fixed points of its Galois group.

## Main results

* `TauCeti.GlobalNumberFields.adeleExtension_injective`: the extension map of adeles is
  injective.
* `TauCeti.GlobalNumberFields.mem_range_adeleExtension_iff`: for `L/K` Galois, an adele of `L`
  is extended from `K` exactly when it is fixed by `Gal(L/K)`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VI, §2.
-/

public section

noncomputable section

open NumberField
open scoped TensorProduct

namespace TauCeti.GlobalNumberFields

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

private local instance (priority := 50) : Algebra K (AdeleRing (𝓞 L) L) :=
  Algebra.compHom _ (algebraMap K L)

private local instance (priority := 50) : IsScalarTower K L (AdeleRing (𝓞 L) L) :=
  IsScalarTower.of_algebraMap_eq' rfl

/-- **The extension map of adeles is injective.** -/
theorem adeleExtension_injective : Function.Injective (adeleExtension (𝓞 K) K (𝓞 L) L) := by
  intro a b h
  refine Algebra.TensorProduct.includeLeft_injective (S := K) (algebraMap K L).injective
    (adeleBaseChangeHom_injective K L ?_)
  simp only [Algebra.TensorProduct.includeLeft_apply, adeleBaseChangeHom_tmul, h]

/-- The extension map of adeles as a `K`-linear map. -/
private def adeleExtensionLinearMap : AdeleRing (𝓞 K) K →ₗ[K] AdeleRing (𝓞 L) L where
  toFun := adeleExtension (𝓞 K) K (𝓞 L) L
  map_add' := map_add _
  map_smul' c a := by
    rw [Algebra.smul_def, Algebra.smul_def, map_mul, adeleExtension_algebraMap, RingHom.id_apply,
      IsScalarTower.algebraMap_apply K L (AdeleRing (𝓞 L) L)]

private theorem adeleExtensionLinearMap_apply (a : AdeleRing (𝓞 K) K) :
    adeleExtensionLinearMap K L a = adeleExtension (𝓞 K) K (𝓞 L) L a :=
  (rfl)

/-- The Galois action on adeles as a `K`-linear representation. -/
private def adeleGaloisRep : Representation K (L ≃ₐ[K] L) (AdeleRing (𝓞 L) L) where
  toFun σ :=
    { toFun := adeleGaloisAction K L σ
      map_add' := map_add _
      map_smul' c a := by
        rw [Algebra.smul_def, Algebra.smul_def, map_mul, RingHom.id_apply,
          IsScalarTower.algebraMap_apply K L (AdeleRing (𝓞 L) L), adeleGaloisAction_algebraMap,
          AlgEquiv.commutes] }
  map_one' := LinearMap.ext fun a ↦ by simp
  map_mul' σ τ := LinearMap.ext fun a ↦ by simp

omit [NumberField K] in
private theorem adeleGaloisRep_apply (σ : L ≃ₐ[K] L) (a : AdeleRing (𝓞 L) L) :
    adeleGaloisRep K L σ a = adeleGaloisAction K L σ a :=
  (rfl)

/-- The scalar extension `L ⊗[K] 𝔸_K → 𝔸_L` of the extension map is base change of adeles, up to
the symmetry of the tensor product, so it is surjective. -/
private theorem surjective_liftBaseChange_adeleExtensionLinearMap :
    Function.Surjective ((adeleExtensionLinearMap K L).liftBaseChange L) := by
  intro y
  obtain ⟨t, rfl⟩ := adeleBaseChangeHom_surjective K L y
  refine ⟨TensorProduct.comm K _ L t, ?_⟩
  induction t using TensorProduct.inductionOn with
  | tmul a x =>
    rw [TensorProduct.comm_tmul, LinearMap.liftBaseChange_tmul, adeleBaseChangeHom_tmul,
      Algebra.smul_def, mul_comm, adeleExtensionLinearMap_apply]
  | add s t hs ht => rw [map_add, map_add, hs, ht, map_add]

variable [IsGalois K L]

/-- **Galois descent for adeles**: for a Galois extension `L/K`, an adele of `L` is extended from
an adele of `K` exactly when it is fixed by every element of `Gal(L/K)`. -/
theorem mem_range_adeleExtension_iff {a : AdeleRing (𝓞 L) L} :
    a ∈ (adeleExtension (𝓞 K) K (𝓞 L) L).range ↔
      ∀ σ : L ≃ₐ[K] L, adeleGaloisAction K L σ a = a := by
  have h := TauCeti.GaloisDescent.range_eq_invariants_of_liftBaseChange_surjective
    (ρ := adeleGaloisRep K L) (f := adeleExtensionLinearMap K L)
    (fun σ x v ↦ by
      rw [adeleGaloisRep_apply, adeleGaloisRep_apply, Algebra.smul_def, Algebra.smul_def, map_mul,
        adeleGaloisAction_algebraMap])
    (fun σ w ↦ adeleGaloisAction_adeleExtension K L σ w)
    (surjective_liftBaseChange_adeleExtensionLinearMap K L)
  rw [RingHom.mem_range, ← Set.mem_range]
  exact (SetLike.ext_iff.1 h a).trans ((Representation.mem_invariants _ _).trans
    (forall_congr' fun σ ↦ by rw [adeleGaloisRep_apply]))

end TauCeti.GlobalNumberFields
