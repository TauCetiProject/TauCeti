/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.Injective.Cogenerator
public import TauCeti.Algebra.Module.Injective.Envelope.Basic

/-!
# Matlis duality for modules of finite length

Let `R` be a commutative local ring with residue field `κ`, and let `ι : κ → E` be an injective
envelope of `κ`. The Matlis dual of an `R`-module `M` is `D(M) = Hom_R(M, E)`. This file proves
the finite-length case of Matlis duality: `D` preserves length, and the evaluation map
`M → D(D(M))` is an isomorphism for every module of finite length. No Noetherian hypothesis is
needed. These are the base cases from which the duality between Artinian modules and finite
modules over the completion is built, by passing to the submodules killed by powers of the
maximal ideal. Length preservation and biduality are the cogenerator criteria of
`TauCeti/Algebra/Module/Injective/Cogenerator.lean`, applied to the computation of `D(κ)`.

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
* `TauCeti.annihilator_torsionBySet_of_injective`: if `E` is injective and contains a copy of
  `κ`, then the annihilator of `E[J]` is `J`, for every ideal `J`.
* `TauCeti.IsInjectiveEnvelope.exists_eq_smul_subtype`: for an ideal `J` with `R ⧸ J` of finite
  length, every linear map `E[J] → E` is the inclusion multiplied by a scalar.

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
  have : IsSimpleModule R (ResidueField R) := Module.length_eq_one_iff.mp length_residueField_eq_one
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

/-- The quotient by a maximal ideal is the residue field. -/
private def quotientEquivResidueField {𝔪 : Ideal R} (h𝔪 : 𝔪.IsMaximal) :
    (R ⧸ 𝔪) ≃ₗ[R] ResidueField R :=
  -- `𝔪` is the maximal ideal, the kernel of `residue`.
  Submodule.quotEquivOfEq _ _ (by
      ext r
      simp [eq_maximalIdeal h𝔪, ResidueField.algebraMap_eq, residue_eq_zero_iff]) ≪≫ₗ
    (Algebra.linearMap R (ResidueField R)).quotKerEquivOfSurjective residue_surjective

/-- The Matlis dual of `R ⧸ 𝔪` has length one, for the maximal ideal `𝔪`. -/
private theorem length_quotient_linearMap (hι : Function.Injective ι)
    (hess : IsEssential (LinearMap.range ι)) (𝔪 : Ideal R) (h𝔪 : 𝔪.IsMaximal) :
    Module.length R (R ⧸ 𝔪 →ₗ[R] E) = 1 := by
  rw [((quotientEquivResidueField h𝔪).arrowCongr (LinearEquiv.refl R E)).length_eq,
    ← (residueFieldLinearMapEquiv hι hess).length_eq]
  exact length_residueField_eq_one

variable [Small.{v} R]

/-- If `E` is injective and contains a copy of the residue field, then `E` is a cogenerator: the
evaluation map `M → Hom_R(Hom_R(M, E), E)` is injective for every module `M`. -/
theorem injective_applyₗ_of_injective [Module.Injective R E] (hι : Function.Injective ι)
    {M : Type w} [AddCommGroup M] [Module R M] :
    Function.Injective (LinearMap.applyₗ : M →ₗ[R] (M →ₗ[R] E) →ₗ[R] E) :=
  injective_applyₗ_of_forall_isMaximal fun _ h𝔪 =>
    ⟨ι ∘ₗ (quotientEquivResidueField h𝔪).toLinearMap, 0, fun h => one_ne_zero <| hι <| by
      simpa using LinearMap.congr_fun h ((quotientEquivResidueField h𝔪).symm 1)⟩

/-- If `E` is injective and contains a copy of the residue field, then the elements of `E`
killed by an ideal `J` have annihilator exactly `J`. -/
theorem annihilator_torsionBySet_of_injective [Module.Injective R E]
    (hι : Function.Injective ι) (J : Ideal R) : (Submodule.torsionBySet R E J).annihilator = J := by
  refine le_antisymm (fun r hr => ?_) fun r hr => Submodule.mem_annihilator.mpr fun x hx =>
    (Submodule.mem_torsionBySet_iff _ _).mp hx ⟨r, hr⟩
  -- `E` cogenerates `R ⧸ J`, so the class of `r` is detected by a map `R ⧸ J → E`; that map
  -- sends `1` into `E[J]`, which `r` kills.
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  refine (injective_iff_map_eq_zero _).mp
    (injective_applyₗ_of_injective (M := R ⧸ J) hι) _ (LinearMap.ext fun f => ?_)
  simpa [f.apply_quotient_mk_eq_smul_apply_one] using
    Submodule.mem_annihilator.mp hr _ (J.quotientLinearMapEquivTorsionBySet E f).prop

/-- **Matlis duality preserves length.** For an injective envelope `E` of the residue field of a
local ring, `Hom_R(M, E)` has the same length as `M`, for every module `M`. In particular `M` has
finite length exactly when its Matlis dual does. -/
theorem IsInjectiveEnvelope.length_linearMap (hι : IsInjectiveEnvelope ι) (M : Type w)
    [AddCommGroup M] [Module R M] : Module.length R (M →ₗ[R] E) = Module.length R M :=
  have := hι.moduleInjective
  length_linearMap_of_forall_isMaximal (length_quotient_linearMap hι.injective hι.isEssential_range)
    M

/-- **Matlis biduality for modules of finite length.** For an injective envelope `E` of the
residue field of a local ring, the evaluation map `M → Hom_R(Hom_R(M, E), E)` is bijective for
every module `M` of finite length. -/
theorem IsInjectiveEnvelope.bijective_applyₗ (hι : IsInjectiveEnvelope ι) {M : Type w}
    [AddCommGroup M] [Module R M] (hM : IsFiniteLength R M) :
    Function.Bijective (LinearMap.applyₗ : M →ₗ[R] (M →ₗ[R] E) →ₗ[R] E) :=
  have := hι.moduleInjective
  bijective_applyₗ_of_forall_isMaximal
    (length_quotient_linearMap hι.injective hι.isEssential_range) hM

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

/-- **Linear maps out of a layer of the hull are scalar.** Let `E` be an injective envelope of the
residue field and `J` an ideal with `R ⧸ J` of finite length. Every linear map `E[J] → E` is the
inclusion multiplied by a scalar. -/
theorem IsInjectiveEnvelope.exists_eq_smul_subtype (hι : IsInjectiveEnvelope ι) {J : Ideal R}
    (hJ : IsFiniteLength R (R ⧸ J)) (g : Submodule.torsionBySet R E J →ₗ[R] E) :
    ∃ r : R, g = r • (Submodule.torsionBySet R E J).subtype := by
  -- `E[J]` is the Matlis dual of `R ⧸ J` through evaluation at `1`, and the composite of `g` with
  -- this identification is evaluation at some class `[r]`, by finite-length biduality.
  obtain ⟨m, hm⟩ := (hι.bijective_applyₗ hJ).2
    (g ∘ₗ (J.quotientLinearMapEquivTorsionBySet E).toLinearMap)
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective m
  refine ⟨r, LinearMap.ext fun x => ?_⟩
  simpa using (LinearMap.congr_fun hm ((J.quotientLinearMapEquivTorsionBySet E).symm x)).symm

end TauCeti
