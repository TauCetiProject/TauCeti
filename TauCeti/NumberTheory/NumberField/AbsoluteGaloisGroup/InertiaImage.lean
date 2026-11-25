/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.AbsoluteGaloisGroup.Inertia
import TauCeti.NumberTheory.NumberField.AbsoluteGaloisGroup.Transitivity
import TauCeti.NumberTheory.NumberField.Frobenius.DecompositionGroup
import TauCeti.RingTheory.Invariant.ProfiniteInertia

/-!
# The image of an inertia group in a finite Galois quotient

Let `F` be a field, `G_F` its absolute Galois group, `O` the integral closure of `𝓞 F` in `F^alg`,
and `E` a normal subextension of `F^alg / F`. Through the inclusion `ι : 𝓞 E → O`
(`TauCeti.GaloisRep.ringOfIntegersToIntegralClosure`), a prime `Q` of `O` lies over the prime
`Q ∩ 𝓞 E`. Restriction `G_F → Gal(E/F)` maps the inertia group `I_Q` onto the inertia group of
`Q ∩ 𝓞 E` in `Gal(E/F)` (`TauCeti.GaloisRep.map_inertiaGroup_restrictNormalHom`): the elements of
`O` fixed by `G_E` are those of `𝓞 E`, and `G_E` is a profinite group acting continuously on the
discrete ring `O`, so the profinite form of Mathlib's surjectivity theorem for inertia groups
applies (`Ideal.map_inertia_of_surjective_of_profinite`).

For `F` and `E` number fields this gives the converse of
`TauCeti.GaloisRep.inertiaGroup_le_fixingSubgroup`: `I_Q` fixes `E` exactly when `Q ∩ 𝓞 E` is
unramified over `𝓞 F`, and a finite place `v` of `F` is unramified in `E` exactly when every
inertia group at a maximal ideal of `O` above `v` fixes `E`.

## Main results

* `TauCeti.GaloisRep.map_inertiaGroup_restrictNormalHom`: the image of `I_Q` in `Gal(E/F)` is the
  inertia group of `Q ∩ 𝓞 E`.
* `TauCeti.GaloisRep.inertiaGroup_le_fixingSubgroup_iff`: `I_Q` fixes `E` iff `Q ∩ 𝓞 E` is
  unramified over `𝓞 F`.
* `TauCeti.GaloisRep.forall_inertiaGroup_le_fixingSubgroup_iff`: `v` is unramified in `E` iff
  every inertia group above `v` fixes `E`.
-/

public section

noncomputable section

open NumberField IsDedekindDomain

namespace TauCeti.GaloisRep

variable {F : Type*} [Field F]

/-- **The image of an inertia group in a Galois quotient.** For a normal subextension `E` of
`F^alg / F` over a perfect field `F` and a prime `Q` of the integral closure `O` of `𝓞 F` in
`F^alg`, restriction to `E` maps the inertia group `I_Q ≤ G_F` onto the inertia group of
`Q ∩ 𝓞 E` in `Gal(E/F)`. -/
theorem map_inertiaGroup_restrictNormalHom [PerfectField F]
    (E : IntermediateField F (AlgebraicClosure F)) [Normal F E]
    (Q : Ideal (integralClosure (𝓞 F) (AlgebraicClosure F))) [Q.IsPrime] :
    (inertiaGroup F Q).map (AlgEquiv.restrictNormalHom E) =
      (Q.comap (ringOfIntegersToIntegralClosure E)).inertia (E ≃ₐ[F] E) := by
  set ι := ringOfIntegersToIntegralClosure E
  let _ : Algebra (𝓞 E) (integralClosure (𝓞 F) (AlgebraicClosure F)) := ι.toRingHom.toAlgebra
  let _ : TopologicalSpace (integralClosure (𝓞 F) (AlgebraicClosure F)) := ⊥
  have : DiscreteTopology (integralClosure (𝓞 F) (AlgebraicClosure F)) := ⟨rfl⟩
  have : ContinuousSMul (AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F)
      (integralClosure (𝓞 F) (AlgebraicClosure F)) :=
    continuousSMul_integralClosure F
  set H := E.fixingSubgroup
  have : CompactSpace H :=
    isCompact_iff_compactSpace.1 (InfiniteGalois.fixingSubgroup_isClosed E).isCompact
  -- the elements of `O` fixed by `G_E` are those of `𝓞 E`
  have : Algebra.IsInvariant (𝓞 E) (integralClosure (𝓞 F) (AlgebraicClosure F)) H := ⟨fun x hx ↦ by
    have hxE : (x : AlgebraicClosure F) ∈ E := by
      rw [← InfiniteGalois.fixedField_fixingSubgroup E]
      exact fun σ ↦ (smul_integralClosure_eq_iff σ.val x).1 (hx σ)
    have hint : IsIntegral ℤ (x : AlgebraicClosure F) :=
      isIntegral_trans (R := ℤ) (A := 𝓞 F) _ x.property
    refine ⟨⟨⟨_, hxE⟩, ?_⟩, Subtype.ext (coe_ringOfIntegersToIntegralClosure E _)⟩
    exact (isIntegral_algHom_iff (E.val.restrictScalars ℤ) E.val.injective).1 hint⟩
  have : Q.LiesOver (Q.comap ι) := ⟨rfl⟩
  exact Ideal.map_inertia_of_surjective_of_profinite (AlgEquiv.restrictNormalHom E) H
    (Q.comap ι) Q (AlgEquiv.restrictNormalHom_surjective (AlgebraicClosure F))
    (E.restrictNormalHom_ker).ge (ringOfIntegersToIntegralClosure_smul E)

variable [NumberField F]

/-- **Inertia fixes a finite Galois subextension iff it is unramified there.** For a finite
normal subextension `E` of `F^alg / F` and a prime `Q` of `O`, the inertia group `I_Q` fixes `E`
pointwise exactly when the prime `Q ∩ 𝓞 E` of `𝓞 E` is unramified over `𝓞 F`. -/
theorem inertiaGroup_le_fixingSubgroup_iff (E : IntermediateField F (AlgebraicClosure F))
    [NumberField E] [Normal F E]
    (Q : Ideal (integralClosure (𝓞 F) (AlgebraicClosure F))) [Q.IsPrime] :
    inertiaGroup F Q ≤ E.fixingSubgroup ↔
      Algebra.IsUnramifiedAt (𝓞 F) (Q.comap (ringOfIntegersToIntegralClosure E)) := by
  have : IsGalois F E := {}
  rw [Ideal.isUnramifiedAt_iff_inertia_eq_bot, ← map_inertiaGroup_restrictNormalHom E Q]
  exact ((Subgroup.map_eq_bot_iff _).trans (by rw [E.restrictNormalHom_ker]; rfl)).symm

/-- **Unramified places of a finite Galois subextension.** A finite place `v` of `F` is
unramified in a finite normal subextension `E` of `F^alg / F` exactly when the inertia group at
every maximal ideal of `O` above `v` fixes `E` pointwise. -/
theorem forall_inertiaGroup_le_fixingSubgroup_iff (E : IntermediateField F (AlgebraicClosure F))
    [NumberField E] [Normal F E] (v : HeightOneSpectrum (𝓞 F)) :
    (∀ Q : Ideal (integralClosure (𝓞 F) (AlgebraicClosure F)), Q.IsMaximal →
        Q.under (𝓞 F) = v.asIdeal → inertiaGroup F Q ≤ E.fixingSubgroup) ↔
      v ∉ Chebotarev.ramifiedPrimes F E := by
  refine ⟨fun h ↦ ?_, fun hv Q hQ hQv ↦ have := hQ.isPrime; inertiaGroup_le_fixingSubgroup E hQv hv⟩
  set ι := ringOfIntegersToIntegralClosure E
  rw [Chebotarev.mem_ramifiedPrimes_iff, not_not]
  intro P _ _
  -- lift `P` to a maximal ideal `Q` of `O`, which is integral over `𝓞 E`
  let _ : Algebra (𝓞 E) (integralClosure (𝓞 F) (AlgebraicClosure F)) := ι.toRingHom.toAlgebra
  have : FaithfulSMul (𝓞 E) (integralClosure (𝓞 F) (AlgebraicClosure F)) :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (ringOfIntegersToIntegralClosure_injective E)
  have : Algebra.IsIntegral (𝓞 E) (integralClosure (𝓞 F) (AlgebraicClosure F)) := ⟨fun x ↦ by
    obtain ⟨p, hp, hpx⟩ := x.property
    refine ⟨p.map (algebraMap (𝓞 F) (𝓞 E)), hp.map _, ?_⟩
    rw [Polynomial.eval₂_map]
    have hcomp : (algebraMap (𝓞 E) (integralClosure (𝓞 F) (AlgebraicClosure F))).comp
        (algebraMap (𝓞 F) (𝓞 E)) = algebraMap (𝓞 F) (integralClosure (𝓞 F) (AlgebraicClosure F)) :=
      ι.comp_algebraMap
    rw [hcomp]
    exact Subtype.ext (by simpa [Polynomial.eval₂_eq_sum_range] using hpx)⟩
  have hPv : P.under (𝓞 F) = v.asIdeal := (Ideal.LiesOver.over (P := P) (p := v.asIdeal)).symm
  have hP0 : P ≠ ⊥ := fun h ↦ v.ne_bot (by rw [← hPv, h, Ideal.under_bot])
  have : P.IsMaximal := Ideal.IsPrime.isMaximal inferInstance hP0
  obtain ⟨Q, hQ, hQP⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral 
    (S := integralClosure (𝓞 F) (AlgebraicClosure F)) P
  have hQP : Q.comap ι = P := (hQP.over).symm
  have : Q.IsPrime := hQ.isPrime
  have hQv : Q.under (𝓞 F) = v.asIdeal := by
    rw [← hPv, ← hQP]
    ext x
    simp only [Ideal.under, Ideal.mem_comap, AlgHom.commutes]
  subst hQP
  exact (inertiaGroup_le_fixingSubgroup_iff E Q).1 (h Q hQ hQv)

end TauCeti.GaloisRep
