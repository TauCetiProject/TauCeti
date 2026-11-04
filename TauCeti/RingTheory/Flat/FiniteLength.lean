/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.FiniteLength
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.SimpleModule.Basic
public import TauCeti.LinearAlgebra.TensorProduct.Basic

/-!
# Flat modules tensored with modules of finite length

Let `N` be a flat `R`-module and `f : N → N` a linear map. Injectivity of `f ⊗ 𝟙 M` passes from
a submodule `P ≤ M` and the quotient `M ⧸ P` to `M`, by exactness of
`0 → N ⊗ P → N ⊗ M → N ⊗ (M ⧸ P) → 0`. Over a local ring, a module of finite length is built
from copies of the residue field `κ(R)` by such extensions, so injectivity of `f ⊗ 𝟙 κ(R)` gives
injectivity of `f ⊗ 𝟙 M` for every `R`-module `M` of finite length.

This is the first step of the proof that a nonzerodivisor on the closed fibre of a flat module
stays a nonzerodivisor after tensoring with any finite module.

## Main results

* `Module.Flat.injective_rTensor_of_injective_rTensor_submodule_quotient`: injectivity of
  `f ⊗ 𝟙` passes from `P` and `M ⧸ P` to `M`.
* `Module.Flat.injective_rTensor_of_isFiniteLength`: over a local ring, injectivity of
  `f ⊗ 𝟙 κ(R)` gives injectivity of `f ⊗ 𝟙 M` for every `M` of finite length.

## References

* H. Matsumura, *Commutative Ring Theory*, proof of Theorem 22.5.
-/

public section

open IsLocalRing TensorProduct

namespace Module.Flat

variable {R N : Type*} [CommRing R] [AddCommGroup N] [Module R N]

/-- Over a flat `N`, injectivity of `f ⊗ 𝟙` passes from a submodule `P` of `M` and the quotient
`M ⧸ P` to `M`, by exactness of `0 → N ⊗ P → N ⊗ M → N ⊗ (M ⧸ P) → 0`. -/
theorem injective_rTensor_of_injective_rTensor_submodule_quotient [Flat R N]
    {M : Type*} [AddCommGroup M] [Module R M] {f : N →ₗ[R] N} (P : Submodule R M)
    (hP : Function.Injective (f.rTensor P)) (hQ : Function.Injective (f.rTensor (M ⧸ P))) :
    Function.Injective (f.rTensor M) := by
  rw [injective_iff_map_eq_zero] at hP hQ ⊢
  intro z hz
  have hq : P.mkQ.lTensor N z = 0 := hQ _ <| by
    rw [← LinearMap.lTensor_rTensor_comm, hz, map_zero]
  obtain ⟨w, rfl⟩ := ((_root_.lTensor_exact N (LinearMap.exact_subtype_mkQ P)
    P.mkQ_surjective) z).mp hq
  have hw : P.subtype.lTensor N (f.rTensor P w) = 0 := by
    rwa [LinearMap.lTensor_rTensor_comm]
  rw [hP w ((injective_iff_map_eq_zero _).mp
    (lTensor_preserves_injective_linearMap _ P.injective_subtype) _ hw), map_zero]

/-- Over a local ring `R` and a flat `N`, if `f ⊗ 𝟙` is injective on `N ⊗[R] κ(R)`, it is
injective on `N ⊗[R] M` for every `R`-module `M` of finite length. -/
theorem injective_rTensor_of_isFiniteLength [IsLocalRing R] [Flat R N] {f : N →ₗ[R] N}
    (hκ : Function.Injective (f.rTensor (R ⧸ maximalIdeal R))) {M : Type*} [AddCommGroup M]
    [Module R M] (hM : IsFiniteLength R M) : Function.Injective (f.rTensor M) := by
  induction hM with
  | of_subsingleton => exact Function.injective_of_subsingleton _
  | @of_simple_quotient M _ _ P _ _ ih =>
    refine injective_rTensor_of_injective_rTensor_submodule_quotient P ih ?_
    -- A simple module over a local ring is the residue field.
    obtain ⟨I, hI, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp ‹IsSimpleModule R (M ⧸ P)›
    obtain rfl := IsLocalRing.eq_maximalIdeal hI
    exact (f.injective_rTensor_congr e).mpr hκ

end Module.Flat
