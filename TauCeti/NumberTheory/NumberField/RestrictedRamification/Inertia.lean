/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.AbsoluteGaloisGroup.Inertia.Basic
public import TauCeti.NumberTheory.NumberField.RestrictedRamification.Basic
import TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.Basic
import TauCeti.NumberTheory.Chebotarev.RamifiedPrimes
import TauCeti.NumberTheory.NumberField.AbsoluteGaloisGroup.Inertia.Image

/-!
# `Gal(F^alg / K_S)` and the inertia groups outside `S`

Let `F` be a number field, `G_F` its absolute Galois group (on `F^alg = AlgebraicClosure F`), `S` a
set of finite places of `F` and `K_S ⊆ F^alg` the maximal extension of `F` unramified outside `S`.
The closed normal subgroup `H_S = Gal(F^alg / K_S)` of `G_F` is generated, as a closed normal
subgroup, by the inertia groups at the finite places outside `S`:

* every inertia group `I_Q` above a place `v ∉ S` fixes `K_S`, since each element of `K_S` lies in a
  finite normal subextension unramified at `v`, which `I_Q` fixes;
* if a closed normal subgroup `H` contains these inertia groups, its fixed field lies in `K_S`, by
  the inertia criterion for finite normal subextensions
  (`TauCeti.GaloisRep.forall_inertiaGroup_le_fixingSubgroup_iff`), so `H_S ≤ H`.

## Main results

* `TauCeti.RestrictedRamification.inertiaGroup_le_fixingSubgroup_maxUnramifiedOutside`: inertia
  above a place outside `S` fixes `K_S`.
* `TauCeti.RestrictedRamification.fixingSubgroup_maxUnramifiedOutside_le`: a closed normal
  subgroup containing the inertia outside `S` contains `Gal(F^alg / K_S)`.

## References

* J. S. Milne, *Arithmetic Duality Theorems*, 2nd ed., Chapter I, §4.
-/

public section

open IntermediateField IsDedekindDomain NumberField

namespace TauCeti.RestrictedRamification

variable {F : Type*} [Field F] [NumberField F]

/-- **Inertia outside `S` fixes `K_S`.** For a finite place `v ∉ S` and a maximal ideal `Q` of the
integral closure of `𝓞 F` in `F^alg` above `v`, the inertia group `I_Q` fixes the maximal extension
`K_S` unramified outside `S` pointwise. -/
theorem inertiaGroup_le_fixingSubgroup_maxUnramifiedOutside {S : Set (HeightOneSpectrum (𝓞 F))}
    {v : HeightOneSpectrum (𝓞 F)} (hv : v ∉ S)
    (Q : Ideal (integralClosure (𝓞 F) (AlgebraicClosure F))) [Q.IsPrime]
    (hQv : Q.under (𝓞 F) = v.asIdeal) :
    GaloisRep.inertiaGroup F Q ≤
      (maxUnramifiedOutside F (AlgebraicClosure F) S).fixingSubgroup := by
  refine fun σ hσ ↦ (IntermediateField.mem_fixingSubgroup_iff _ σ).2 fun x hx ↦ ?_
  -- `x` lies in a finite subextension unramified outside `S`, hence in its normal closure
  obtain ⟨E, hxE, _, hE⟩ := mem_maxUnramifiedOutside_iff.1 hx
  set E' := normalClosure F E (AlgebraicClosure F)
  have hEE' : E ≤ E' := le_normalClosure E
  have hE'S : E' ≤ maxUnramifiedOutside F (AlgebraicClosure F) S :=
    normalClosure_le_iff_of_normal.2 (le_maxUnramifiedOutside hE)
  have : NumberField E' := NumberField.of_module_finite F E'
  have hv' : v ∉ Chebotarev.ramifiedPrimes F E' :=
    (Chebotarev.notMem_ramifiedPrimes_iff_isUnramifiedIn v).2
      (le_maxUnramifiedOutside_iff.1 hE'S v hv)
  exact (IntermediateField.mem_fixingSubgroup_iff E' σ).1
    (GaloisRep.inertiaGroup_le_fixingSubgroup E' hQv hv' hσ) x (hEE' hxE)

/-- **`H_S` is the smallest closed normal subgroup containing the inertia outside `S`.** If a
closed normal subgroup `H` of `G_F` contains the inertia group `I_Q` at every maximal ideal `Q`
above every finite place `v ∉ S`, then `H` contains `Gal(F^alg / K_S)`. -/
theorem fixingSubgroup_maxUnramifiedOutside_le {S : Set (HeightOneSpectrum (𝓞 F))}
    {H : Subgroup (Field.absoluteGaloisGroup F)} [H.Normal]
    (hH : IsClosed (H : Set (Field.absoluteGaloisGroup F)))
    (hI : ∀ v ∉ S, ∀ Q : Ideal (integralClosure (𝓞 F) (AlgebraicClosure F)), Q.IsMaximal →
      Q.under (𝓞 F) = v.asIdeal → GaloisRep.inertiaGroup F Q ≤ H) :
    (maxUnramifiedOutside F (AlgebraicClosure F) S).fixingSubgroup ≤ H := by
  set E := fixedField H
  have hfix : E.fixingSubgroup = H := TauCeti.fixingSubgroup_fixedField hH
  -- the fixed field of the normal subgroup `H` is normal over `F`
  have : E.fixingSubgroup.Normal := hfix ▸ ‹H.Normal›
  have hEn : Normal F E := ((InfiniteGalois.normal_iff_isGalois E).1 this).to_normal
  -- the fixed field lies in `K_S`
  have hE : E ≤ maxUnramifiedOutside F (AlgebraicClosure F) S := by
    intro x hx
    set L := normalClosure F F⟮x⟯ (AlgebraicClosure F)
    have hxL : F⟮x⟯ ≤ L := le_normalClosure _
    have hLE : L ≤ E := normalClosure_le_iff_of_normal.2 (adjoin_simple_le_iff.2 hx)
    have : FiniteDimensional F F⟮x⟯ :=
      adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral x)
    have : NumberField L := NumberField.of_module_finite F L
    refine le_maxUnramifiedOutside (L := L) (fun v hv ↦ ?_) (hxL (mem_adjoin_simple_self F x))
    refine (Chebotarev.notMem_ramifiedPrimes_iff_isUnramifiedIn v).1
      ((GaloisRep.forall_inertiaGroup_le_fixingSubgroup_iff L v).1 fun Q hQ hQv ↦ ?_)
    exact (hI v hv Q hQ hQv).trans (hfix ▸ fixingSubgroup_antitone hLE)
  rw [← hfix]
  exact fixingSubgroup_antitone hE

end TauCeti.RestrictedRamification
