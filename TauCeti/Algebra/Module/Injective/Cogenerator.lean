/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.LeftExact
public import TauCeti.Algebra.Module.Injective.Hom
public import TauCeti.Algebra.Module.Torsion.QuotientLinearMap
public import TauCeti.RingTheory.Length

/-!
# Injective cogenerators over a commutative ring

Let `R` be a commutative ring and `E` an injective `R`-module, with dual `D(M) = Hom_R(M, E)`.
This file isolates what `E` must satisfy for `D` to behave like Matlis duality. If `E` receives a
nonzero map from `R ⧸ 𝔪` for every maximal ideal `𝔪`, then `E` is a cogenerator. If moreover each
`Hom_R(R ⧸ 𝔪, E)` has length one, then `D` preserves length, by induction on a composition series
and exactness of `Hom_R(-, E)`, and the evaluation map `M → D(D(M))` is bijective for every module
of finite length, an injective map between modules of the same finite length being bijective.

## Main results

* `TauCeti.injective_applyₗ_of_forall_isMaximal`: an injective module receiving a nonzero map from
  every `R ⧸ 𝔪` is a cogenerator.
* `TauCeti.length_linearMap_of_isSimpleModule`: if each `Hom_R(R ⧸ 𝔪, E)` has length one, then so
  does `Hom_R(S, E)` for every simple module `S`; injectivity of `E` is not needed.
* `TauCeti.length_linearMap_of_forall_isMaximal` and `TauCeti.bijective_applyₗ_of_forall_isMaximal`:
  if moreover `E` is injective, then `D` preserves length and biduality holds for modules of finite
  length.

## References

* M. Auslander, I. Reiten, S. O. Smalø, *Representation Theory of Artin Algebras*, Section II.3,
  Theorem 3.3.
* The Stacks Project, Section 47.7, Matlis duality, Tag 08Z1.
-/

public section

noncomputable section

namespace TauCeti

open LinearMap

universe u v w

section Cogenerator

variable {R : Type u} [CommRing R] {E : Type v} [AddCommGroup E] [Module R E]
  [Module.Injective R E] [Small.{v} R]

/-- **A cogenerator test.** An injective module `E` that receives a nonzero map from `R ⧸ 𝔪` for
every maximal ideal `𝔪` is a cogenerator: the evaluation map `M → Hom_R(Hom_R(M, E), E)` is
injective for every module `M`. -/
theorem injective_applyₗ_of_forall_isMaximal
    (hE : ∀ 𝔪 : Ideal R, 𝔪.IsMaximal → Nontrivial (R ⧸ 𝔪 →ₗ[R] E))
    {M : Type w} [AddCommGroup M] [Module R M] :
    Function.Injective (LinearMap.applyₗ : M →ₗ[R] (M →ₗ[R] E) →ₗ[R] E) := by
  refine (injective_iff_map_eq_zero _).mpr fun m hm => ?_
  by_contra hm0
  -- The annihilator of `m` is proper, so it lies in a maximal ideal `𝔪`.
  obtain ⟨𝔪, h𝔪, hle⟩ := Ideal.exists_le_maximal (LinearMap.ker (LinearMap.toSpanSingleton R M m))
    ((Ideal.ne_top_iff_one _).mpr fun h => hm0 (by simpa using h))
  -- A nonzero element `x` of `E` killed by `𝔪` is the image of `m` under some map `M → E`.
  have := hE 𝔪 h𝔪
  obtain ⟨φ, hφ⟩ := exists_ne (0 : R ⧸ 𝔪 →ₗ[R] E)
  let x := 𝔪.quotientLinearMapEquivTorsionBySet E φ
  have hx : (x : E) ≠ 0 := fun h => hφ <|
    (𝔪.quotientLinearMapEquivTorsionBySet E).map_eq_zero_iff.mp (Subtype.ext h)
  obtain ⟨g, hg⟩ := (exists_linearMap_apply_eq_iff_forall_smul_eq_zero (a := m)
    (x := (x : E))).mpr fun r hr =>
      (Submodule.mem_torsionBySet_iff _ _).mp x.prop ⟨r, hle (by simpa using hr)⟩
  exact hx (hg ▸ LinearMap.congr_fun hm g)

variable (hE : ∀ 𝔪 : Ideal R, 𝔪.IsMaximal → Module.length R (R ⧸ 𝔪 →ₗ[R] E) = 1)
include hE

omit [Module.Injective R E] [Small.{v} R] in
/-- If `Hom_R(R ⧸ 𝔪, E)` has length one for every maximal ideal `𝔪`, then `Hom_R(S, E)` has
length one for every simple module `S`. -/
theorem length_linearMap_of_isSimpleModule {S : Type w} [AddCommGroup S] [Module R S]
    [IsSimpleModule R S] : Module.length R (S →ₗ[R] E) = 1 := by
  obtain ⟨𝔪, h𝔪, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp ‹IsSimpleModule R S›
  rw [(e.arrowCongr (LinearEquiv.refl R E)).length_eq]
  exact hE 𝔪 h𝔪

omit [Module.Injective R E] [Small.{v} R] in
private theorem nontrivial_linearMap_of_isMaximal (𝔪 : Ideal R) (h𝔪 : 𝔪.IsMaximal) :
    Nontrivial (R ⧸ 𝔪 →ₗ[R] E) :=
  Module.length_pos_iff.mp (by rw [hE 𝔪 h𝔪]; exact zero_lt_one)

/-- The dual of a module of finite length has the same length. -/
private theorem length_linearMap_of_isFiniteLength {M : Type w} [AddCommGroup M] [Module R M]
    (hM : IsFiniteLength R M) : Module.length R (M →ₗ[R] E) = Module.length R M := by
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
      ih, length_linearMap_of_isSimpleModule hE (S := M ⧸ N), Module.length_eq_one R (M ⧸ N),
      add_comm]

/-- **The dual preserves length.** If `E` is injective and `Hom_R(R ⧸ 𝔪, E)` has length one for
every maximal ideal `𝔪`, then `Hom_R(M, E)` has the same length as `M`, for every module `M`. In
particular `M` has finite length exactly when its dual does. -/
theorem length_linearMap_of_forall_isMaximal (M : Type w) [AddCommGroup M] [Module R M] :
    Module.length R (M →ₗ[R] E) = Module.length R M := by
  by_cases hM : IsFiniteLength R M
  · exact length_linearMap_of_isFiniteLength hE hM
  -- If `D(M)` had finite length, `M` would embed in the module `D(D(M))` of finite length.
  have hD : ¬ IsFiniteLength R (M →ₗ[R] E) := fun hD => hM <| by
    refine IsFiniteLength.of_injective ?_
      (injective_applyₗ_of_forall_isMaximal (nontrivial_linearMap_of_isMaximal hE))
    rw [← Module.length_ne_top_iff, length_linearMap_of_isFiniteLength hE hD]
    exact Module.length_ne_top_iff.mpr hD
  rw [← Module.length_ne_top_iff, not_not] at hM hD
  rw [hM, hD]

/-- **Biduality for modules of finite length.** If `E` is injective and `Hom_R(R ⧸ 𝔪, E)` has
length one for every maximal ideal `𝔪`, then the evaluation map `M → Hom_R(Hom_R(M, E), E)` is
bijective for every module `M` of finite length. -/
theorem bijective_applyₗ_of_forall_isMaximal {M : Type w} [AddCommGroup M] [Module R M]
    (hM : IsFiniteLength R M) :
    Function.Bijective (LinearMap.applyₗ : M →ₗ[R] (M →ₗ[R] E) →ₗ[R] E) := by
  have hinj := injective_applyₗ_of_forall_isMaximal (nontrivial_linearMap_of_isMaximal hE)
    (M := M)
  refine ⟨hinj, surjective_of_injective_of_length_eq hinj (Module.length_ne_top_iff.mpr hM) ?_⟩
  rw [length_linearMap_of_forall_isMaximal hE, length_linearMap_of_forall_isMaximal hE]

end Cogenerator

end TauCeti
