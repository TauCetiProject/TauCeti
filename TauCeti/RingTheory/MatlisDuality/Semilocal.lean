/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.LeftExact
public import Mathlib.RingTheory.HopkinsLevitzki
public import TauCeti.Algebra.Module.Injective.Envelope.Existence
public import TauCeti.Algebra.Module.Injective.Hom
public import TauCeti.Algebra.Module.Torsion.QuotientLinearMap
public import TauCeti.RingTheory.Length

/-!
# Matlis duality over a semilocal ring

Let `R` be a commutative ring whose quotient `R ⧸ J(R)` by the Jacobson radical is a semisimple
ring, for instance a commutative Artinian ring. This file proves Matlis duality for modules of
finite length over `R`, with dualizing module an injective hull `E` of `R ⧸ J(R)`: the dual
`D(M) = Hom_R(M, E)` has the same length as `M`, and the evaluation map `M → D(D(M))` is an
isomorphism for every `M` of finite length. Over a commutative Artinian ring `E` itself has finite
length, so `D` sends modules of finite length to modules of finite length and is inverse to itself
there up to evaluation. No locality is assumed; over a local ring `R ⧸ J(R)` is the residue field,
the case treated in `TauCeti/RingTheory/MatlisDuality/FiniteLength.lean`.

The argument isolates what the dualizing module must satisfy. An injective module `E` such that
`Hom_R(R ⧸ 𝔪, E)` has length one for every maximal ideal `𝔪` is a cogenerator, and its dual
preserves the length of every module, by induction on a composition series and exactness of
`Hom_R(-, E)`. Biduality on modules of finite length follows, an injective map between modules of
the same finite length being bijective. For the injective hull of `R ⧸ J(R)`, every map from
`R ⧸ 𝔪` lands in the essential image of `R ⧸ J(R)`, and `Hom_R(R ⧸ 𝔪, R ⧸ J(R))` is simple:
it is nonzero because the semisimple module `R ⧸ J(R)` has `R ⧸ 𝔪` as a direct summand, and it is
at most one-dimensional over `R ⧸ 𝔪` because `J(R)` is a radical ideal.

## Main results

* `TauCeti.injective_applyₗ_of_forall_isMaximal`: an injective module receiving a nonzero map from
  every `R ⧸ 𝔪` is a cogenerator.
* `TauCeti.length_linearMap_of_forall_isMaximal` and `TauCeti.bijective_applyₗ_of_forall_isMaximal`:
  if moreover each `Hom_R(R ⧸ 𝔪, E)` has length one, then `D` preserves length and biduality holds
  for modules of finite length.
* `Ideal.length_linearMap_quotient_jacobson_eq_one`: `Hom_R(R ⧸ 𝔪, R ⧸ J(R))` has length one.
* `TauCeti.IsInjectiveEnvelope.length_linearMap_quotient_jacobson` and
  `TauCeti.IsInjectiveEnvelope.bijective_applyₗ_quotient_jacobson`: Matlis duality for modules of
  finite length over `R`.
* `TauCeti.IsInjectiveEnvelope.isFiniteLength_quotient_jacobson` and
  `TauCeti.exists_isInjectiveEnvelope_quotient_jacobson`: over a commutative Artinian ring, every
  injective hull of `R ⧸ J(R)` has finite length, and one exists in the universe of `R`.

## References

* M. Auslander, I. Reiten, S. O. Smalø, *Representation Theory of Artin Algebras*, Section II.3,
  Theorems 3.1 and 3.3.
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
/-- The dual of a simple module has length one. -/
private theorem length_linearMap_of_isSimpleModule {S : Type w} [AddCommGroup S] [Module R S]
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

namespace Ideal

variable {R : Type u} [CommRing R] [IsSemisimpleRing (R ⧸ Ring.jacobson R)]

/-- **Each simple module occurs once in `R ⧸ J(R)`.** If `R ⧸ J(R)` is a semisimple ring, then for
every maximal ideal `𝔪` the module `Hom_R(R ⧸ 𝔪, R ⧸ J(R))` is simple. -/
theorem length_linearMap_quotient_jacobson_eq_one (𝔪 : Ideal R) [h𝔪 : 𝔪.IsMaximal] :
    Module.length R (R ⧸ 𝔪 →ₗ[R] R ⧸ Ring.jacobson R) = 1 := by
  rw [(𝔪.quotientLinearMapEquivTorsionBySet (R ⧸ Ring.jacobson R)).length_eq,
    Module.length_eq_one_iff]
  -- `R ⧸ 𝔪` is a direct summand of the semisimple module `R ⧸ J(R)`, so the layer is nonzero.
  have : IsSemisimpleModule R (R ⧸ Ring.jacobson R) := (isSemisimpleModule_iff _ _).mpr <|
    (Submodule.orderIsoOfAlgebraMapSurjective (S := R ⧸ Ring.jacobson R)
      (M := R ⧸ Ring.jacobson R) Ideal.Quotient.mk_surjective).complementedLattice
  obtain ⟨s, hs⟩ := IsSemisimpleModule.lifting_property
    (Submodule.factor (Ring.jacobson_le_of_isMaximal 𝔪)) (Submodule.factor_surjective _)
    LinearMap.id
  have : Nontrivial (R ⧸ 𝔪 →ₗ[R] R ⧸ Ring.jacobson R) := ⟨s, 0, by
    rintro rfl
    simpa using LinearMap.congr_fun hs 1⟩
  -- Two elements of the layer are proportional, since `J(R)` is a radical ideal.
  refine isSimpleModule_iff_toSpanSingleton_surjective.mpr
    ⟨(𝔪.quotientLinearMapEquivTorsionBySet _).symm.toEquiv.nontrivial, fun x hx y => ?_⟩
  have hJ : (Ring.jacobson R).IsRadical := by
    simpa only [Ideal.jacobson_bot] using Ideal.isRadical_jacobson (⊥ : Ideal R)
  have hsmul (r : R) (z : R ⧸ Ring.jacobson R) : r • z = Ideal.Quotient.mk _ r * z := by
    rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq]
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (x : R ⧸ Ring.jacobson R)
  obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (y : R ⧸ Ring.jacobson R)
  have ha𝔪 : a ∉ 𝔪 := fun ha𝔪 => hx <| Subtype.ext <| by
    have h0 := (Submodule.mem_torsionBySet_iff _ _).mp x.prop ⟨a, ha𝔪⟩
    rw [hsmul, ← ha, ← map_mul, Ideal.Quotient.eq_zero_iff_mem, ← pow_two] at h0
    rw [Submodule.coe_zero, ← ha, Ideal.Quotient.eq_zero_iff_mem]
    exact hJ ⟨2, h0⟩
  obtain ⟨c, i, hi, hci⟩ := h𝔪.exists_inv ha𝔪
  have hiy := (Submodule.mem_torsionBySet_iff _ _).mp y.prop ⟨i, hi⟩
  rw [hsmul, ← hb, ← map_mul, Ideal.Quotient.eq_zero_iff_mem] at hiy
  refine ⟨c * b, Subtype.ext ?_⟩
  rw [LinearMap.toSpanSingleton_apply, Submodule.coe_smul, hsmul, ← ha, ← hb, ← map_mul,
    Ideal.Quotient.eq]
  have : c * b * a - b = -(i * b) := by linear_combination b * hci
  rw [this]
  exact neg_mem hiy

end Ideal

namespace TauCeti

open LinearMap

section Semilocal

variable {R : Type u} [CommRing R] [IsSemisimpleRing (R ⧸ Ring.jacobson R)]
  {E : Type v} [AddCommGroup E] [Module R E] [Small.{v} R]
  {f : R ⧸ Ring.jacobson R →ₗ[R] E}

omit [Small.{v} R] in
/-- In an injective hull of `R ⧸ J(R)`, each simple module occurs once: `Hom_R(R ⧸ 𝔪, E)` has
length one for every maximal ideal `𝔪`. -/
private theorem IsInjectiveEnvelope.length_quotient_linearMap (hf : IsInjectiveEnvelope f)
    (𝔪 : Ideal R) (h𝔪 : 𝔪.IsMaximal) : Module.length R (R ⧸ 𝔪 →ₗ[R] E) = 1 := by
  rw [← 𝔪.length_linearMap_quotient_jacobson_eq_one]
  -- Composing with `f` is bijective, as the range of a map out of `R ⧸ 𝔪` is simple or zero.
  refine (length_eq_of_bijective (LinearMap.compRight R f) ⟨fun g g' h => ?_, fun φ => ?_⟩).symm
  · exact LinearMap.ext fun z => hf.injective (LinearMap.congr_fun h z)
  obtain rfl | hφ := eq_or_ne φ 0
  · exact ⟨0, by simp⟩
  have : IsSimpleModule R (R ⧸ 𝔪) := isSimpleModule_iff_quot_maximal.mpr ⟨𝔪, h𝔪, ⟨.refl _ _⟩⟩
  have hatom : IsAtom (LinearMap.range φ) := isSimpleModule_iff_isAtom.mp <|
    IsSimpleModule.congr (LinearEquiv.ofInjective φ (LinearMap.injective_of_ne_zero hφ)).symm
  refine ⟨(LinearEquiv.ofInjective f hf.injective).symm ∘ₗ
    φ.codRestrict _ fun z => hf.isEssential_range.atom_le hatom (LinearMap.mem_range_self φ z),
    LinearMap.ext fun z => ?_⟩
  simp [LinearEquiv.ofInjective_symm_apply]

/-- **Matlis duality preserves length.** For an injective hull `E` of `R ⧸ J(R)`, where `R ⧸ J(R)`
is a semisimple ring, `Hom_R(M, E)` has the same length as `M`, for every module `M`. -/
theorem IsInjectiveEnvelope.length_linearMap_quotient_jacobson (hf : IsInjectiveEnvelope f)
    (M : Type w) [AddCommGroup M] [Module R M] :
    Module.length R (M →ₗ[R] E) = Module.length R M :=
  have := hf.moduleInjective
  length_linearMap_of_forall_isMaximal hf.length_quotient_linearMap M

/-- **Matlis biduality over a semilocal ring.** For an injective hull `E` of `R ⧸ J(R)`, where
`R ⧸ J(R)` is a semisimple ring, the evaluation map `M → Hom_R(Hom_R(M, E), E)` is bijective for
every module `M` of finite length. -/
theorem IsInjectiveEnvelope.bijective_applyₗ_quotient_jacobson (hf : IsInjectiveEnvelope f)
    {M : Type w} [AddCommGroup M] [Module R M] (hM : IsFiniteLength R M) :
    Function.Bijective (LinearMap.applyₗ : M →ₗ[R] (M →ₗ[R] E) →ₗ[R] E) :=
  have := hf.moduleInjective
  bijective_applyₗ_of_forall_isMaximal hf.length_quotient_linearMap hM

end Semilocal

section Artinian

variable {R : Type u} [CommRing R] [IsArtinianRing R]

/-- Over a commutative Artinian ring, every injective hull of `R ⧸ J(R)` has finite length. -/
theorem IsInjectiveEnvelope.isFiniteLength_quotient_jacobson {E : Type v} [AddCommGroup E]
    [Module R E] [Small.{v} R] {f : R ⧸ Ring.jacobson R →ₗ[R] E} (hf : IsInjectiveEnvelope f) :
    IsFiniteLength R E := by
  rw [← Module.length_ne_top_iff, ← (LinearMap.ringLmapEquivSelf R R E).length_eq,
    hf.length_linearMap_quotient_jacobson, Module.length_ne_top_iff]
  exact (isArtinianRing_iff_isFiniteLength (R := R)).mp ‹_›

variable (R) in
/-- **The injective cogenerator of a commutative Artinian ring.** `R ⧸ J(R)` has an injective hull
of finite length. -/
theorem exists_isInjectiveEnvelope_quotient_jacobson :
    ∃ (E : Type u) (_ : AddCommGroup E) (_ : Module R E) (f : R ⧸ Ring.jacobson R →ₗ[R] E),
      IsInjectiveEnvelope f ∧ IsFiniteLength R E := by
  obtain ⟨E, _, _, f, hf⟩ := exists_isInjectiveEnvelope R (R ⧸ Ring.jacobson R)
  exact ⟨E, _, _, f, hf, hf.isFiniteLength_quotient_jacobson⟩

end Artinian

end TauCeti
