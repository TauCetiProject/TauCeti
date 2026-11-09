/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.HopkinsLevitzki
public import TauCeti.Algebra.Module.Injective.Cogenerator
public import TauCeti.Algebra.Module.Injective.Envelope.Existence

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

The argument applies the cogenerator criteria of
`TauCeti/Algebra/Module/Injective/Cogenerator.lean`: an injective module `E` such that
`Hom_R(R ⧸ 𝔪, E)` has length one for every maximal ideal `𝔪` gives a duality preserving length,
with biduality on modules of finite length. For the injective hull of `R ⧸ J(R)`, every map from
`R ⧸ 𝔪` lands in the essential image of `R ⧸ J(R)`, and `Hom_R(R ⧸ 𝔪, R ⧸ J(R))` is simple:
it is nonzero because the semisimple module `R ⧸ J(R)` has `R ⧸ 𝔪` as a direct summand, and it is
at most one-dimensional over `R ⧸ 𝔪` because `J(R)` is a radical ideal.

## Main results

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

universe u v w

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
