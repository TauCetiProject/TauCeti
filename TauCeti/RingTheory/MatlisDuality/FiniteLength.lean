/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.LeftExact
public import TauCeti.Algebra.Module.Injective.Envelope.Basic
public import TauCeti.Algebra.Module.Injective.Hom
public import TauCeti.RingTheory.Length

/-!
# Matlis duality for modules of finite length

Let `R` be a commutative local ring with residue field `κ`, and let `ι : κ → E` be an injective
envelope of `κ`. The Matlis dual of an `R`-module `M` is `D(M) = Hom_R(M, E)`. This file proves
the finite-length case of Matlis duality: `D` preserves length, and the evaluation map
`M → D(D(M))` is an isomorphism for every module of finite length. No Noetherian hypothesis is
needed. These are the base cases from which the duality between Artinian modules and finite
modules over the completion is built, by passing to the submodules killed by powers of the
maximal ideal.

## Main declarations

* `TauCeti.residueFieldLinearMapEquiv`: `D(κ) ≅ κ`. Every linear map `κ → E` is `ι` composed
  with multiplication by a residue, because the image of `ι` is the only simple submodule of an
  essential extension of `κ`. Injectivity of `E` is not used.
* `TauCeti.injective_applyₗ_of_injective`: as soon as `E` is injective and contains a copy of
  `κ`, the evaluation map `M → D(D(M))` is injective for every `M`, so `E` is a cogenerator.
* `TauCeti.IsInjectiveEnvelope.length_linearMap`: `length D(M) = length M` for every module `M`,
  of finite length or not.
* `TauCeti.IsInjectiveEnvelope.bijective_applyₗ` and `TauCeti.IsInjectiveEnvelope.evalEquiv`:
  biduality for modules of finite length.

## References

* The Stacks Project, Section 47.7, Matlis duality, Tag 08Z1.
* W. Bruns, J. Herzog, *Cohen–Macaulay rings*, Section 3.2.
-/

public section

noncomputable section

namespace TauCeti

open IsLocalRing LinearMap

universe u v w

variable {R : Type u} [CommRing R] [IsLocalRing R] {E : Type v} [AddCommGroup E] [Module R E]
  {ι : ResidueField R →ₗ[R] E}

/-- The Matlis dual of the residue field is the residue field: for an embedding `ι` of `κ` with
essential range, `a ↦ (b ↦ ι (a * b))` is an isomorphism `κ ≅ Hom_R(κ, E)`. -/
def residueFieldLinearMapEquiv (hι : Function.Injective ι)
    (hess : IsEssential (LinearMap.range ι)) :
    ResidueField R ≃ₗ[R] (ResidueField R →ₗ[R] E) :=
  have : IsSimpleModule R (ResidueField R) :=
    Module.length_eq_one_iff.mp length_quotient_maximalIdeal_eq_one
  LinearEquiv.ofBijective ((LinearMap.mul R (ResidueField R)).compr₂ ι) <| by
    refine ⟨(injective_iff_map_eq_zero _).mpr fun a ha => ?_, fun φ => ?_⟩
    · simpa using hι (by simpa using LinearMap.congr_fun ha 1)
    obtain rfl | hφ := eq_or_ne φ 0
    · exact ⟨0, map_zero _⟩
    -- The range of `φ` is a simple submodule, hence lies in the essential range of `ι`.
    have hatom : IsAtom (LinearMap.range φ) := isSimpleModule_iff_isAtom.mp <|
      IsSimpleModule.congr (LinearEquiv.ofInjective φ (LinearMap.injective_of_ne_zero hφ)).symm
    obtain ⟨a, ha⟩ := hess.atom_le hatom (LinearMap.mem_range_self φ 1)
    refine ⟨a, LinearMap.ext fun b => ?_⟩
    obtain ⟨r, rfl⟩ := residue_surjective b
    have hr : residue R r = r • (1 : ResidueField R) := by
      rw [Algebra.smul_def, mul_one, ResidueField.algebraMap_eq]
    rw [hr, map_smul, map_smul φ, ← ha]
    simp

@[simp]
theorem residueFieldLinearMapEquiv_apply_apply (hι : Function.Injective ι)
    (hess : IsEssential (LinearMap.range ι)) (a b : ResidueField R) :
    residueFieldLinearMapEquiv hι hess a b = ι (a * b) :=
  (rfl)

/-- The Matlis dual of a simple module has length one. -/
private theorem length_linearMap_of_isSimpleModule (hι : Function.Injective ι)
    (hess : IsEssential (LinearMap.range ι)) {S : Type w} [AddCommGroup S] [Module R S]
    [IsSimpleModule R S] : Module.length R (S →ₗ[R] E) = 1 := by
  obtain ⟨I, hI, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp ‹IsSimpleModule R S›
  rw [eq_maximalIdeal hI] at e
  let e' : S ≃ₗ[R] ResidueField R := e
  rw [(e'.arrowCongr (LinearEquiv.refl R E)).length_eq,
    ← (residueFieldLinearMapEquiv hι hess).length_eq]
  exact length_quotient_maximalIdeal_eq_one

variable [Small.{v} R]

/-- If `E` is injective and contains a copy of the residue field, then `E` is a cogenerator: the
evaluation map `M → Hom_R(Hom_R(M, E), E)` is injective for every module `M`. -/
theorem injective_applyₗ_of_injective [Module.Injective R E] (hι : Function.Injective ι)
    {M : Type w} [AddCommGroup M] [Module R M] :
    Function.Injective (LinearMap.applyₗ : M →ₗ[R] (M →ₗ[R] E) →ₗ[R] E) := by
  refine (injective_iff_map_eq_zero _).mpr fun m hm => ?_
  by_contra hm0
  -- A nonzero `m` has annihilator inside the maximal ideal, so it can be sent to `ι 1`.
  obtain ⟨f, hf⟩ := (exists_linearMap_apply_eq_iff_forall_smul_eq_zero (a := m) (x := ι 1)).mpr
    fun r hr => by
      have hr' : r ∈ maximalIdeal R := by
        by_contra h
        exact hm0 ((notMem_maximalIdeal.mp h).smul_eq_zero.mp hr)
      rw [← map_smul, Algebra.smul_def, mul_one, ResidueField.algebraMap_eq,
        (residue_eq_zero_iff r).mpr hr', map_zero]
  have h1 : ι 1 = ι 0 := by simpa [hf] using LinearMap.congr_fun hm f
  exact one_ne_zero (hι h1)

/-- The Matlis dual of a module of finite length has the same length. -/
private theorem IsInjectiveEnvelope.length_linearMap_of_isFiniteLength
    (hι : IsInjectiveEnvelope ι) {M : Type w} [AddCommGroup M] [Module R M]
    (hM : IsFiniteLength R M) : Module.length R (M →ₗ[R] E) = Module.length R M := by
  have := hι.moduleInjective
  induction hM with
  | of_subsingleton => simp [Module.length_eq_zero]
  | @of_simple_quotient M _ _ N _ _ ih =>
    -- Dualize `0 → N → M → M ⧸ N → 0` to the short exact `0 → D(M ⧸ N) → D(M) → D(N) → 0`.
    have hsurj : Function.Surjective (N.subtype.lcomp R E) := fun g =>
      Module.Injective.extension_property R E N M N.subtype N.injective_subtype g
    rw [Module.length_eq_add_of_exact _ _ N.injective_subtype N.mkQ_surjective
        (LinearMap.exact_subtype_mkQ N),
      Module.length_eq_add_of_exact _ _ (lcomp_injective_of_surjective _ N.mkQ_surjective) hsurj
        (exact_lcomp_of_exact_of_surjective E (LinearMap.exact_subtype_mkQ N) N.mkQ_surjective),
      ih, length_linearMap_of_isSimpleModule (S := M ⧸ N) hι.injective hι.isEssential_range,
      Module.length_eq_one R (M ⧸ N), add_comm]

/-- **Matlis duality preserves length.** For an injective envelope `E` of the residue field of a
local ring, `Hom_R(M, E)` has the same length as `M`, for every module `M`. In particular `M` has
finite length exactly when its Matlis dual does. -/
theorem IsInjectiveEnvelope.length_linearMap (hι : IsInjectiveEnvelope ι) (M : Type w)
    [AddCommGroup M] [Module R M] : Module.length R (M →ₗ[R] E) = Module.length R M := by
  by_cases hM : IsFiniteLength R M
  · exact hι.length_linearMap_of_isFiniteLength hM
  -- If `D(M)` had finite length, `M` would embed in the module `D(D(M))` of finite length.
  have := hι.moduleInjective
  have hD : ¬ IsFiniteLength R (M →ₗ[R] E) := fun hD => hM <| by
    refine IsFiniteLength.of_injective ?_ (injective_applyₗ_of_injective hι.injective)
    rw [← Module.length_ne_top_iff, hι.length_linearMap_of_isFiniteLength hD]
    exact Module.length_ne_top_iff.mpr hD
  rw [← Module.length_ne_top_iff, not_not] at hM hD
  rw [hM, hD]

/-- **Matlis biduality for modules of finite length.** For an injective envelope `E` of the
residue field of a local ring, the evaluation map `M → Hom_R(Hom_R(M, E), E)` is bijective for
every module `M` of finite length. -/
theorem IsInjectiveEnvelope.bijective_applyₗ (hι : IsInjectiveEnvelope ι) {M : Type w}
    [AddCommGroup M] [Module R M] (hM : IsFiniteLength R M) :
    Function.Bijective (LinearMap.applyₗ : M →ₗ[R] (M →ₗ[R] E) →ₗ[R] E) := by
  have := hι.moduleInjective
  have hinj := injective_applyₗ_of_injective (M := M) hι.injective
  refine ⟨hinj, surjective_of_injective_of_length_eq hinj (Module.length_ne_top_iff.mpr hM) ?_⟩
  rw [hι.length_linearMap, hι.length_linearMap]

/-- Matlis biduality for a module `M` of finite length, as the linear equivalence
`M ≃ Hom_R(Hom_R(M, E), E)` given by evaluation. -/
def IsInjectiveEnvelope.evalEquiv (hι : IsInjectiveEnvelope ι) {M : Type w} [AddCommGroup M]
    [Module R M] (hM : IsFiniteLength R M) : M ≃ₗ[R] ((M →ₗ[R] E) →ₗ[R] E) :=
  LinearEquiv.ofBijective LinearMap.applyₗ (hι.bijective_applyₗ hM)

@[simp]
theorem IsInjectiveEnvelope.evalEquiv_apply_apply (hι : IsInjectiveEnvelope ι) {M : Type w}
    [AddCommGroup M] [Module R M] (hM : IsFiniteLength R M) (m : M) (f : M →ₗ[R] E) :
    hι.evalEquiv hM m f = f m :=
  (rfl)

end TauCeti
