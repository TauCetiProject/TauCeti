/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Chebotarev.RamifiedPrimes
public import TauCeti.NumberTheory.GaloisRepresentation.GlobalRamification
import TauCeti.NumberTheory.NumberField.Frobenius.DecompositionGroup

/-!
# Galois representations with open kernel have finite ramification set

Let `F` be a number field, `G_F` its absolute Galois group and `O` the integral closure of `𝓞 F` in
`F^alg`. For a finite normal subextension `E` of `F^alg / F`, the inertia group `I_Q ≤ G_F` at a
maximal ideal `Q` of `O` restricts into the inertia group of `Q ∩ 𝓞 E` in `Gal(E/F)`. When the
place `v` of `F` below `Q` is unramified in `E` this inertia group is trivial (Tau Ceti's
`isUnramifiedAt_iff_inertia_eq_bot`), so `I_Q` fixes `E` pointwise
(`TauCeti.GaloisRep.inertiaGroup_le_fixingSubgroup`).

A continuous representation `ρ` of `G_F` whose kernel is open has a kernel containing the fixing
subgroup of some finite normal `E`, by the definition of the Krull topology. It is therefore
unramified at every place unramified in `E`, and since only finitely many places of `F` ramify in
`E` (`NumberField.Chebotarev.ramifiedPrimes`), its ramification set is finite
(`TauCeti.ContinuousRep.finite_ramificationSet_of_isOpen_ker`). Open kernel is the right
hypothesis: finite image alone does not suffice, since over an indiscrete coefficient ring the
kernel of a character with finite image can be dense.

## Main results

* `TauCeti.GaloisRep.inertiaGroup_le_fixingSubgroup`: `I_Q` fixes every finite normal
  subextension in which the place below `Q` is unramified.
* `TauCeti.ContinuousRep.ramificationSet_subset_ramifiedPrimes`: if the kernel of `ρ` contains the
  fixing subgroup of a finite normal `E`, then `Ram ρ` lies in the set of places ramified in `E`.
* `TauCeti.ContinuousRep.finite_ramificationSet_of_isOpen_ker`: the ramification set of a
  representation with open kernel is finite.
-/

public section

noncomputable section

open NumberField IsDedekindDomain

namespace TauCeti.GaloisRep

variable {F : Type*} [Field F]

/-- The inclusion of `𝓞 E` into the integral closure of `𝓞 F` in `F^alg`, for an intermediate field
`E` of `F^alg / F`. -/
@[expose] def ringOfIntegersToIntegralClosure (E : IntermediateField F (AlgebraicClosure F)) :
    𝓞 E →+* integralClosure (𝓞 F) (AlgebraicClosure F) :=
  ((algebraMap E (AlgebraicClosure F)).comp (algebraMap (𝓞 E) E)).codRestrict
    (integralClosure (𝓞 F) (AlgebraicClosure F)).toSubring fun y ↦
      ((y.isIntegral_coe.map (IsScalarTower.toAlgHom ℤ E (AlgebraicClosure F))).tower_top :
        IsIntegral (𝓞 F) _)

@[simp]
theorem coe_ringOfIntegersToIntegralClosure (E : IntermediateField F (AlgebraicClosure F))
    (y : 𝓞 E) :
    (ringOfIntegersToIntegralClosure E y : AlgebraicClosure F) = ((y : E) : AlgebraicClosure F) :=
  rfl

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
  set ι := ringOfIntegersToIntegralClosure E
  let P : Ideal (𝓞 E) := Q.comap ι
  have : P.IsPrime := Ideal.comap_isPrime ι Q
  have hι : ι.comp (algebraMap (𝓞 F) (𝓞 E)) =
      algebraMap (𝓞 F) (integralClosure (𝓞 F) (AlgebraicClosure F)) := by
    exact RingHom.ext fun x ↦ Subtype.ext rfl
  have : P.LiesOver v.asIdeal := ⟨by
    rw [← hQv, Ideal.under, Ideal.under, Ideal.comap_comap, hι]⟩
  -- the restriction of `σ` to `E`
  let τ : E ≃ₐ[F] E := AlgEquiv.restrictNormalHom E σ
  have hτ (x : E) : ((τ x : E) : AlgebraicClosure F) =
      DFunLike.coe (F := AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F) σ
        (x : AlgebraicClosure F) :=
    AlgEquiv.restrictNormal_commutes σ E x
  have hτP : τ ∈ P.inertia (E ≃ₐ[F] E) := by
    intro y
    change ι (τ • y - y) ∈ Q
    have hιτ : ι (τ • y) = σ • ι y := by
      apply Subtype.ext
      simp only [coe_smul_integralClosure]
      exact hτ y
    rw [map_sub, hιτ]
    exact hσ (ι y)
  have hur : Algebra.IsUnramifiedAt (𝓞 F) P := by
    rw [Chebotarev.mem_ramifiedPrimes_iff, not_not] at hv
    exact hv P
  rw [Ideal.isUnramifiedAt_iff_inertia_eq_bot P] at hur
  have hτ1 : τ = 1 := by
    rw [hur] at hτP
    exact hτP
  rintro ⟨x, hx⟩
  have := hτ ⟨x, hx⟩
  rw [hτ1] at this
  exact this.symm

end TauCeti.GaloisRep

namespace TauCeti.ContinuousRep

variable {F : Type*} [Field F] [NumberField F]
  {A M : Type*} [Semiring A] [AddCommMonoid M] [Module A M] [TopologicalSpace M]
  {ρ : ContinuousRep (Field.absoluteGaloisGroup F) A M}

/-- If the kernel of `ρ` contains the fixing subgroup of a finite normal subextension `E` of
`F^alg / F`, then `ρ` is unramified at every finite place of `F` unramified in `E`. -/
theorem ramificationSet_subset_ramifiedPrimes (E : IntermediateField F (AlgebraicClosure F))
    [NumberField E] [Normal F E] (hE : E.fixingSubgroup ≤ ρ.toRepresentation.ker) :
    ρ.ramificationSet ⊆ (Chebotarev.ramifiedPrimes F E : Set (HeightOneSpectrum (𝓞 F))) := by
  intro v hv
  by_contra hvE
  refine (mem_ramificationSet_iff.1 hv) (isUnramifiedAt_iff.2 fun Q hQ hQv ↦ ?_)
  have := hQ.isPrime
  exact fun σ hσ ↦ hE (GaloisRep.inertiaGroup_le_fixingSubgroup E hQv hvE hσ)

/-- **A representation with open kernel has finite ramification set.** The kernel contains the
fixing subgroup of a finite normal subextension `E` of `F^alg / F` (Krull topology), `ρ` is
unramified at the places unramified in `E`, and only finitely many places ramify in `E`. -/
theorem finite_ramificationSet_of_isOpen_ker
    (hρ : IsOpen (ρ.toRepresentation.ker : Set (Field.absoluteGaloisGroup F))) :
    ρ.ramificationSet.Finite := by
  obtain ⟨E, hfin, hnormal, hE⟩ := (krullTopology_mem_nhds_one_iff_of_normal F
    (AlgebraicClosure F) (ρ.toRepresentation.ker : Set (Field.absoluteGaloisGroup F))).1
      (hρ.mem_nhds (one_mem _))
  have : NumberField E := NumberField.of_module_finite F E
  exact (Chebotarev.ramifiedPrimes F E).finite_toSet.subset
    (ramificationSet_subset_ramifiedPrimes E hE)

end TauCeti.ContinuousRep
