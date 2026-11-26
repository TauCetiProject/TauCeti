/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Chebotarev.RamifiedPrimes
public import TauCeti.NumberTheory.NumberField.AbsoluteGaloisGroup.Decomposition
import TauCeti.NumberTheory.NumberField.Frobenius.DecompositionGroup

/-!
# Inertia groups of the absolute Galois group and finite subextensions

Let `F` be a number field, `G_F` its absolute Galois group and `O` the integral closure of `𝓞 F` in
`F^alg`. For an intermediate field `E` of `F^alg / F`, the inclusion `E → F^alg` restricts to an
`𝓞 F`-algebra map `𝓞 E → O` (`TauCeti.GaloisRep.ringOfIntegersToIntegralClosure`). For `E` normal
over `F` it intertwines the action of the restriction of `σ ∈ G_F` to `E` on `𝓞 E` with the action
of `σ` on `O`.

For a finite normal subextension `E`, the inertia group `I_Q ≤ G_F` at a prime `Q` of `O` therefore
restricts into the inertia group of `Q ∩ 𝓞 E` in `Gal(E/F)`. When the place `v` of `F` below `Q` is
unramified in `E` this inertia group is trivial (Tau Ceti's `isUnramifiedAt_iff_inertia_eq_bot`),
so `I_Q` fixes `E` pointwise.

## Main definitions

* `TauCeti.GaloisRep.ringOfIntegersToIntegralClosure E`: the inclusion `𝓞 E → O`, as a map of
  `𝓞 F`-algebras.

## Main results

* `TauCeti.GaloisRep.ringOfIntegersToIntegralClosure_smul`: the inclusion intertwines the actions of
  `G_F` on `𝓞 E` (through restriction to `E`) and on `O`.
* `TauCeti.GaloisRep.inertiaGroup_le_fixingSubgroup`: `I_Q` fixes every finite normal
  subextension in which the place below `Q` is unramified.
-/

public section

noncomputable section

open NumberField IsDedekindDomain

namespace TauCeti.GaloisRep

variable {F : Type*} [Field F]

/-- The inclusion of `𝓞 E` into the integral closure of `𝓞 F` in `F^alg`, for an intermediate field
`E` of `F^alg / F`, as a map of `𝓞 F`-algebras. -/
def ringOfIntegersToIntegralClosure (E : IntermediateField F (AlgebraicClosure F)) :
    𝓞 E →ₐ[𝓞 F] integralClosure (𝓞 F) (AlgebraicClosure F) :=
  ((E.val.restrictScalars (𝓞 F)).comp (IsScalarTower.toAlgHom (𝓞 F) (𝓞 E) E)).codRestrict
    (integralClosure (𝓞 F) (AlgebraicClosure F)) fun y ↦
      ((y.isIntegral_coe.map (IsScalarTower.toAlgHom ℤ E (AlgebraicClosure F))).tower_top :
        IsIntegral (𝓞 F) _)

@[simp]
theorem coe_ringOfIntegersToIntegralClosure (E : IntermediateField F (AlgebraicClosure F))
    (y : 𝓞 E) :
    (ringOfIntegersToIntegralClosure E y : AlgebraicClosure F) = ((y : E) : AlgebraicClosure F) :=
  (rfl)

/-- The inclusion `𝓞 E → O` is injective. -/
theorem ringOfIntegersToIntegralClosure_injective (E : IntermediateField F (AlgebraicClosure F)) :
    Function.Injective (ringOfIntegersToIntegralClosure E) := fun x y h ↦ by
  have h' := congrArg (fun z : integralClosure (𝓞 F) (AlgebraicClosure F) ↦
    (z : AlgebraicClosure F)) h
  simp only [coe_ringOfIntegersToIntegralClosure] at h'
  exact RingOfIntegers.ext (Subtype.val_injective h')

/-- For `E` normal over `F`, the inclusion `𝓞 E → O` intertwines the action on `𝓞 E` of the
restriction of `σ ∈ G_F` to `E` (`AlgEquiv.restrictNormalHom`) with the action of `σ` on `O`. -/
@[simp]
theorem ringOfIntegersToIntegralClosure_smul (E : IntermediateField F (AlgebraicClosure F))
    [Normal F E] (σ : Field.absoluteGaloisGroup F) (y : 𝓞 E) :
    ringOfIntegersToIntegralClosure E (AlgEquiv.restrictNormalHom E σ • y) =
      σ • ringOfIntegersToIntegralClosure E y :=
  Subtype.ext <| by
    rw [coe_smul_integralClosure, coe_ringOfIntegersToIntegralClosure,
      coe_ringOfIntegersToIntegralClosure, RingOfIntegers.coe_eq_algebraMap, algebraMap.smul',
      AlgEquiv.smul_def]
    -- `G_F` is defined as `Gal(F^alg/F)`, so `σ` is an argument of `restrictNormalHom_apply`
    exact AlgEquiv.restrictNormalHom_apply E σ _

variable [NumberField F]

/-- **Inertia fixes unramified subextensions.** Let `E` be a finite normal subextension of
`F^alg / F` and `Q` a prime of the integral closure `O` of `𝓞 F` in `F^alg` lying over a finite
place `v` of `F` that is unramified in `E`. Then `I_Q` fixes `E` pointwise: an element of `I_Q`
restricts to an element of the inertia group of `Q ∩ 𝓞 E` in `Gal(E/F)`, which is trivial. -/
theorem inertiaGroup_le_fixingSubgroup (E : IntermediateField F (AlgebraicClosure F))
    [NumberField E] [Normal F E]
    {Q : Ideal (integralClosure (𝓞 F) (AlgebraicClosure F))} [Q.IsPrime]
    {v : HeightOneSpectrum (𝓞 F)} (hQv : Q.under (𝓞 F) = v.asIdeal)
    (hv : v ∉ Chebotarev.ramifiedPrimes F E) :
    inertiaGroup F Q ≤ E.fixingSubgroup := by
  have : IsGalois F E := {}
  intro σ hσ
  rw [Ideal.mem_inertia] at hσ
  set ι := ringOfIntegersToIntegralClosure E
  let P : Ideal (𝓞 E) := Q.comap ι
  have : P.IsPrime := Ideal.comap_isPrime ι Q
  have : Q.LiesOver v.asIdeal := ⟨hQv.symm⟩
  have : P.LiesOver v.asIdeal := Ideal.comap_liesOver Q v.asIdeal ι
  -- the restriction `τ` of `σ` to `E` lies in the inertia group of `P` in `Gal(E/F)`
  set τ : E ≃ₐ[F] E := AlgEquiv.restrictNormalHom E σ with hτ
  have hτP : τ ∈ P.inertia (E ≃ₐ[F] E) := by
    rw [Ideal.mem_inertia]
    intro y
    rw [Ideal.mem_comap, map_sub, ringOfIntegersToIntegralClosure_smul]
    exact hσ (ι y)
  -- which is trivial since `v` is unramified in `E`
  have hur : Algebra.IsUnramifiedAt (𝓞 F) P := by
    rw [Chebotarev.mem_ramifiedPrimes_iff, not_not] at hv
    exact hv P
  rw [Ideal.isUnramifiedAt_iff_inertia_eq_bot P] at hur
  rw [hur, Subgroup.mem_bot] at hτP
  refine (IntermediateField.mem_fixingSubgroup_iff E σ).2 fun x hx ↦ ?_
  rw [← AlgEquiv.restrictNormalHom_apply E σ ⟨x, hx⟩, ← hτ, hτP, AlgEquiv.one_apply]

end TauCeti.GaloisRep
