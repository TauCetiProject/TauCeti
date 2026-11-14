/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Shrink
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
`IsAdicComplete.pi`. Hausdorffness is the Krull intersection theorem
(`IsHausdorff.of_le_jacobson`), available because `I` lies in the Jacobson radical of a complete
ring.

This is what makes a finite algebra over a complete Noetherian ring Henselian along the extended
ideal, the input for lifting idempotents in such an algebra.

Over any commutative ring, the completion of a finite module is generated over the completed ring
by the image of the module, so it is a finite module over the completed ring and linear maps out of
it are determined by their restrictions to the module. Over a Noetherian ring, shrinking a finite
module into the universe of the ring lifts Mathlib's
`AdicCompletion.ofTensorProduct_bijective_of_finite_of_isNoetherian` to modules in an arbitrary
universe (`TauCeti.AdicCompletion.ofTensorProductEquiv`).

## Main results

* `IsPrecomplete.of_surjective`: adic precompleteness passes along a surjective linear map.
* `IsPrecomplete.of_finite`: a finite module over an adically precomplete ring is precomplete.
* `IsAdicComplete.of_finite`: a finite module over an adically complete Noetherian ring is
  complete.
* `IsPrecomplete.of_finite_of_isLocalRing`: a finite local algebra over a precomplete local ring
  is precomplete at its own maximal ideal, without a Noetherian hypothesis.
* `IsAdicComplete.of_finite_of_isLocalRing`: a finite local algebra over a complete Noetherian
  local ring is complete at its own maximal ideal.
* `AdicCompletion.linearMap_ext_of_finite`: a linear map over the completion out of the completion
  of a finite module is determined on the image of the module, since
  `AdicCompletion.ofTensorProduct` is surjective.
* `TauCeti.AdicCompletion.instFinite`: the adic completion of a finite `R`-module is finite over
  `AdicCompletion I R`.
* `TauCeti.AdicCompletion.ofTensorProductEquiv`: universe-polymorphic `AdicCompletion I R`-linear
  equivalence `AdicCompletion I R ⊗[R] N ≃ₗ[AdicCompletion I R] AdicCompletion I N` for finite `N`
  over Noetherian `R`.

## References

* M. F. Atiyah, I. G. Macdonald, *Introduction to Commutative Algebra*, Chapter 10.
-/

public section

open AdicCompletion TensorProduct

variable {R : Type*} [CommRing R] (I : Ideal R) {M N : Type*} [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N]

/-- Adic precompleteness passes along a surjective linear map: the adic completion functor
preserves surjections. -/
theorem IsPrecomplete.of_surjective [IsPrecomplete I M] (f : M →ₗ[R] N)
    (hf : Function.Surjective f) : IsPrecomplete I N := by
  refine AdicCompletion.of_surjective_iff.mp fun y ↦ ?_
  obtain ⟨z, rfl⟩ := map_surjective I hf y
  obtain ⟨x, rfl⟩ := AdicCompletion.of_surjective I M z
  exact ⟨f x, (map_of I f x).symm⟩

variable (M)

/-- A finite module over an `I`-adically precomplete ring is `I`-adically precomplete. -/
theorem IsPrecomplete.of_finite [IsPrecomplete I R] [Module.Finite R M] : IsPrecomplete I M := by
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' R M
  exact IsPrecomplete.of_surjective I f hf

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

namespace TauCeti.AdicCompletion

universe u v

/-- The adic completion of a finitely generated `R`-module is finitely generated over
`AdicCompletion I R`, as a quotient of `AdicCompletion I R ⊗[R] M`. -/
instance instFinite [Module.Finite R M] :
    Module.Finite (_root_.AdicCompletion I R) (_root_.AdicCompletion I M) :=
  .of_surjective (ofTensorProduct I M) (ofTensorProduct_surjective_of_finite I M)

section OfTensorProduct

variable {R₀ : Type u} [CommRing R₀] [IsNoetherianRing R₀] (J : Ideal R₀)
  (P : Type v) [AddCommGroup P] [Module R₀ P] [Module.Finite R₀ P]

/-- Universe-polymorphic form of
`AdicCompletion.ofTensorProduct_bijective_of_finite_of_isNoetherian`, allowing the module `P` to
live in an independent universe from `R₀`. -/
theorem ofTensorProduct_bijective_of_finite :
    Function.Bijective (ofTensorProduct J P) := by
  obtain ⟨_, f, hf⟩ := Module.Finite.exists_fin' R₀ P
  have : Small.{u} P := small_of_surjective hf
  let e : Shrink.{u} P ≃ₗ[R₀] P := Shrink.linearEquiv R₀ P
  have : Module.Finite R₀ (Shrink.{u} P) := .equiv e.symm
  have heq : ofTensorProduct J P = (congr J e).toLinearMap ∘ₗ ofTensorProduct J (Shrink.{u} P) ∘ₗ
      (AlgebraTensorModule.congr (LinearEquiv.refl (_root_.AdicCompletion J R₀) _)
        e.symm).toLinearMap := by
    refine LinearMap.restrictScalars_injective R₀ ?_
    refine TensorProduct.ext' fun a x ↦ ?_
    simp [map_of]
  rw [heq]
  exact (congr J e).bijective.comp
    ((ofTensorProduct_bijective_of_finite_of_isNoetherian J (Shrink.{u} P)).comp
      (AlgebraTensorModule.congr (LinearEquiv.refl (_root_.AdicCompletion J R₀) _)
        e.symm).bijective)

/-- Universe-polymorphic `AdicCompletion J R₀`-linear equivalence
`AdicCompletion J R₀ ⊗[R₀] P ≃ₗ[AdicCompletion J R₀] AdicCompletion J P` for a finitely generated
module `P` over a Noetherian ring `R₀`. -/
noncomputable def ofTensorProductEquiv :
    _root_.AdicCompletion J R₀ ⊗[R₀] P ≃ₗ[_root_.AdicCompletion J R₀]
      _root_.AdicCompletion J P :=
  LinearEquiv.ofBijective (ofTensorProduct J P) (ofTensorProduct_bijective_of_finite J P)

@[simp]
theorem ofTensorProductEquiv_apply (x : _root_.AdicCompletion J R₀ ⊗[R₀] P) :
    ofTensorProductEquiv J P x = ofTensorProduct J P x :=
  (rfl)

@[simp]
theorem ofTensorProductEquiv_symm_of (x : P) :
    (ofTensorProductEquiv J P).symm (of J P x) = 1 ⊗ₜ x := by
  have h : of J P x = ofTensorProductEquiv J P (1 ⊗ₜ x) := by simp
  rw [h, LinearEquiv.symm_apply_apply]

end OfTensorProduct

end TauCeti.AdicCompletion
