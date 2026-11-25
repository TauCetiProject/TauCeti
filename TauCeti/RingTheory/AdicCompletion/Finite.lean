/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
public import Mathlib.RingTheory.AdicCompletion.Noetherian
public import TauCeti.RingTheory.AdicCompletion.Pi
import TauCeti.RingTheory.AdicCompletion.Pow
import TauCeti.RingTheory.Ideal.GoingUp
import TauCeti.RingTheory.LocalRing.Monogenic

/-!
# Adic completion of finite modules

Over an `I`-adically complete Noetherian ring, every finitely generated module is `I`-adically
complete. Precompleteness passes along surjective linear maps, because the adic completion functor
preserves surjections; a finite module is a quotient of a finite free module, which is complete by
`IsAdicComplete.pi`. Dually, adic separatedness passes along injective linear maps, hence to
submodules and to arbitrary free modules over an `I`-adically separated ring. Over a Noetherian
ring, Hausdorffness of all finite modules is the Krull intersection theorem
(`IsHausdorff.of_le_jacobson`), available because `I` lies in the Jacobson radical of a complete
ring.

This is what makes a finite algebra over a complete Noetherian ring Henselian along the extended
ideal, the input for lifting idempotents in such an algebra.

Over any commutative ring, the completion of a finite module is generated over the completed ring
by the image of the module, so linear maps over the completed ring out of it are determined by
their restrictions to the module.

## Main results

* `IsHausdorff.of_injective`: adic Hausdorffness passes along an injective linear map, hence to
  every submodule (`Submodule.isHausdorff`) and to every free module (`IsHausdorff.of_free`).
* `IsPrecomplete.of_surjective`: adic precompleteness passes along a surjective linear map.
* `IsPrecomplete.of_finite`: a finite module over an adically precomplete ring is precomplete.
* `Module.Finite.of_finite_quotient_smul_top`: Nakayama's lemma for complete rings, an adically
  separated module over an adically precomplete ring is finite once its reduction is.
* `IsAdicComplete.of_finite`: a finite module over an adically complete Noetherian ring is
  complete.
* `IsPrecomplete.of_finite_of_isLocalRing`: a finite local algebra over a precomplete local ring
  is precomplete at its own maximal ideal, without a Noetherian hypothesis.
* `IsAdicComplete.of_finite_of_isLocalRing`: a finite local algebra over a complete Noetherian
  local ring is complete at its own maximal ideal.
* `AdicCompletion.linearMap_ext_of_finite`: a linear map over the completion out of the completion
  of a finite module is determined on the image of the module, since
  `AdicCompletion.ofTensorProduct` is surjective.

## References

* M. F. Atiyah, I. G. Macdonald, *Introduction to Commutative Algebra*, Chapter 10.
-/

public section

open AdicCompletion

variable {R : Type*} [CommRing R] (I : Ideal R) {M N : Type*} [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N]

/-- Adic separatedness passes along an injective linear map. -/
theorem IsHausdorff.of_injective [IsHausdorff I N] (f : M →ₗ[R] N) (hf : Function.Injective f) :
    IsHausdorff I M :=
  AdicCompletion.of_injective_iff.mp fun _ _ hxy ↦ hf <| AdicCompletion.of_injective I N <| by
    rw [← AdicCompletion.map_of, ← AdicCompletion.map_of, hxy]

/-- Every submodule of an `I`-adically separated module is `I`-adically separated. -/
instance Submodule.isHausdorff [IsHausdorff I M] (P : Submodule R M) : IsHausdorff I P :=
  .of_injective I P.subtype P.injective_subtype

/-- Adic precompleteness passes along a surjective linear map: the adic completion functor
preserves surjections. -/
theorem IsPrecomplete.of_surjective [IsPrecomplete I M] (f : M →ₗ[R] N)
    (hf : Function.Surjective f) : IsPrecomplete I N := by
  refine AdicCompletion.of_surjective_iff.mp fun y ↦ ?_
  obtain ⟨z, rfl⟩ := map_surjective I hf y
  obtain ⟨x, rfl⟩ := AdicCompletion.of_surjective I M z
  exact ⟨f x, (map_of I f x).symm⟩

variable (M)

/-- Every free module over an `I`-adically separated ring is `I`-adically separated. -/
theorem IsHausdorff.of_free [IsHausdorff I R] [Module.Free R M] : IsHausdorff I M :=
  .of_injective I
    (LinearMap.pi fun i ↦ Finsupp.lapply i ∘ₗ (Module.Free.chooseBasis R M).repr.toLinearMap)
    fun _ _ h ↦ (Module.Free.chooseBasis R M).repr.injective (Finsupp.ext fun i ↦ congrFun h i)

/-- A finite module over an `I`-adically precomplete ring is `I`-adically precomplete. -/
theorem IsPrecomplete.of_finite [IsPrecomplete I R] [Module.Finite R M] : IsPrecomplete I M := by
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' R M
  exact IsPrecomplete.of_surjective I f hf

/-- **Nakayama's lemma for adically complete rings**: an `I`-adically separated module over an
`I`-adically precomplete ring is finite as soon as its reduction modulo `I` is. Lifting finitely
many generators of `M ⧸ I • M` gives a map from a finite free module which is surjective modulo
`I`, hence surjective (`surjective_of_mkQ_comp_surjective`). No Noetherian hypothesis is needed. -/
theorem Module.Finite.of_finite_quotient_smul_top [IsPrecomplete I R] [IsHausdorff I M]
    [Module.Finite R (M ⧸ (I • ⊤ : Submodule R M))] : Module.Finite R M := by
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' R (M ⧸ (I • ⊤ : Submodule R M))
  obtain ⟨g, hg⟩ := Module.projective_lifting_property (I • ⊤ : Submodule R M).mkQ f
    (Submodule.mkQ_surjective _)
  have : IsPrecomplete I (Fin n → R) := .of_finite I _
  exact .of_surjective g (surjective_of_mkQ_comp_surjective (I := I) (hg ▸ hf))

/-- A finite module over an `I`-adically complete Noetherian ring is `I`-adically complete. -/
theorem IsAdicComplete.of_finite [IsNoetherianRing R] [IsAdicComplete I R] [Module.Finite R M] :
    IsAdicComplete I M where
  toIsHausdorff := IsHausdorff.of_le_jacobson I M (IsAdicComplete.le_jacobson I)
  toIsPrecomplete := IsPrecomplete.of_finite I M

/-- A finite local algebra over a precomplete local ring is precomplete for its own maximal
ideal, without a Noetherian hypothesis. The two maximal-ideal-adic filtrations are cofinal. -/
theorem IsPrecomplete.of_finite_of_isLocalRing (R S : Type*) [CommRing R] [IsLocalRing R]
    [IsPrecomplete (IsLocalRing.maximalIdeal R) R]
    [CommRing S] [IsLocalRing S] [Algebra R S] [Module.Finite R S] :
    IsPrecomplete (IsLocalRing.maximalIdeal S) S := by
  have : IsPrecomplete (IsLocalRing.maximalIdeal R) S := .of_finite _ _
  have : IsPrecomplete ((IsLocalRing.maximalIdeal R).map (algebraMap R S)) S :=
    IsPrecomplete.map_algebraMap_iff.mpr inferInstance
  obtain ⟨n, hn⟩ := TauCeti.IsLocalRing.exists_maximalIdeal_pow_le_map (R := R) (S := S)
  exact IsPrecomplete.of_pow_le_of_pow_le (l := 1) hn (by
    rw [pow_one]
    exact Ideal.map_le_iff_le_comap.mpr
      (Ideal.comap_eq_maximalIdeal_of_isIntegral (IsLocalRing.maximalIdeal S)).ge)

/-- A finite local algebra over a complete Noetherian local ring is complete for its own
maximal ideal. The two maximal-ideal-adic filtrations are cofinal, even when the extension is
ramified. -/
theorem IsAdicComplete.of_finite_of_isLocalRing (R S : Type*) [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    [CommRing S] [IsLocalRing S] [Algebra R S] [Module.Finite R S] :
    IsAdicComplete (IsLocalRing.maximalIdeal S) S := by
  have : IsNoetherianRing S := .of_finite R S
  exact {
    toIsHausdorff := inferInstance
    toIsPrecomplete := IsPrecomplete.of_finite_of_isLocalRing R S }

variable {M} in
/-- Linear maps over the completion out of the completion of a finite module are determined by
their values on the image of the module. -/
theorem AdicCompletion.linearMap_ext_of_finite [Module.Finite R M] {P : Type*} [AddCommGroup P]
    [Module (AdicCompletion I R) P] {g₁ g₂ : AdicCompletion I M →ₗ[AdicCompletion I R] P}
    (h : ∀ x, g₁ (of I M x) = g₂ (of I M x)) : g₁ = g₂ := by
  refine LinearMap.ext fun y ↦ ?_
  obtain ⟨t, rfl⟩ := ofTensorProduct_surjective_of_finite I M y
  induction t using TensorProduct.inductionOn with
  | tmul a x => simp [ofTensorProduct_tmul, h]
  | add s t hs ht => simp [hs, ht]
