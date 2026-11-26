/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.GaloisRepresentation.GlobalRamification
public import TauCeti.NumberTheory.NumberField.RestrictedRamification.Restriction
import TauCeti.NumberTheory.NumberField.AbsoluteGaloisGroup.Inertia.Image

/-!
# Representations unramified outside `S` factor through `G_{F,S}`

Let `F` be a number field, `G_F` its absolute Galois group (on `F^alg = AlgebraicClosure F`), `S` a
set of finite places of `F`, `K_S ⊆ F^alg` the maximal extension of `F` unramified outside `S` and
`G_{F,S} = Gal(K_S / F)`. This file proves the unramified factorisation criterion: a continuous
representation `ρ` of `G_F` on a Hausdorff module is unramified outside `S`
(`TauCeti.ContinuousRep.IsUnramifiedOutside`) exactly when it factors, necessarily continuously,
through the restriction `G_F → G_{F,S}` (`TauCeti.RestrictedRamification.restrictionS`).

The arithmetic content is that the kernel `H_S = Gal(F^alg / K_S)` of the restriction is generated,
as a closed normal subgroup, by the inertia groups at the finite places outside `S`:

* every inertia group `I_Q` above a place `v ∉ S` fixes `K_S`, since each element of `K_S` lies in a
  finite normal subextension unramified at `v`, which `I_Q` fixes
  (`TauCeti.RestrictedRamification.inertiaGroup_le_fixingSubgroup_maxUnramifiedOutside`);
* if a closed normal subgroup `H` contains these inertia groups, its fixed field lies in `K_S`, by
  the inertia criterion for finite normal subextensions
  (`TauCeti.GaloisRep.forall_inertiaGroup_le_fixingSubgroup_iff`), so `H_S ≤ H`
  (`TauCeti.RestrictedRamification.fixingSubgroup_maxUnramifiedOutside_le`).

The kernel of a continuous representation on a Hausdorff module is closed, which gives the
criterion. The descended representation of `G_{F,S}` is
`TauCeti.ContinuousRep.descendS`; its action is continuous because `G_F → G_{F,S}` is an open
surjection.

## Main results

* `TauCeti.ContinuousRep.isUnramifiedOutside_iff_fixingSubgroup_le_ker`: `ρ` is unramified outside
  `S` iff `Gal(F^alg / K_S)` acts trivially.
* `TauCeti.ContinuousRep.descendS`: a representation unramified outside `S`, as a representation
  of `G_{F,S}`, with `res_descendS`.
* `TauCeti.ContinuousRep.isUnramifiedOutside_iff_exists_res_eq`: `ρ` is unramified outside `S` iff
  it is the restriction of a continuous representation of `G_{F,S}`.

## References

* J. S. Milne, *Arithmetic Duality Theorems*, 2nd ed., Chapter I, §4.
-/

public section

noncomputable section

open IntermediateField IsDedekindDomain NumberField

namespace TauCeti

namespace RestrictedRamification

variable {F : Type*} [Field F] [NumberField F]

/-- A finite place outside the ramified primes of a finite normal subextension is unramified in
it, in the sense of Mathlib's `Algebra.IsUnramifiedIn`. -/
private theorem notMem_ramifiedPrimes_iff (E : IntermediateField F (AlgebraicClosure F))
    [NumberField E] (v : HeightOneSpectrum (𝓞 F)) :
    v ∉ Chebotarev.ramifiedPrimes F E ↔ Algebra.IsUnramifiedIn (𝓞 E) v.asIdeal := by
  rw [Chebotarev.mem_ramifiedPrimes_iff, not_not]
  exact ⟨fun h P _ _ ↦ h P, fun h P _ _ ↦ h P ‹_› ‹_›⟩

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
    (notMem_ramifiedPrimes_iff E' v).2 (le_maxUnramifiedOutside_iff.1 hE'S v hv)
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
    refine (notMem_ramifiedPrimes_iff L v).1
      ((GaloisRep.forall_inertiaGroup_le_fixingSubgroup_iff L v).1 fun Q hQ hQv ↦ ?_)
    exact (hI v hv Q hQ hQv).trans (hfix ▸ fixingSubgroup_antitone hLE)
  rw [← hfix]
  exact fixingSubgroup_antitone hE

end RestrictedRamification

namespace ContinuousRep

open RestrictedRamification

variable {F : Type*} [Field F] [NumberField F] {S : Set (HeightOneSpectrum (𝓞 F))}
  {A M : Type*} [Semiring A] [AddCommMonoid M] [Module A M] [TopologicalSpace M]
  {ρ : ContinuousRep (Field.absoluteGaloisGroup F) A M}

omit [NumberField F] in
/-- The kernel of a continuous representation on a Hausdorff module is closed. -/
private theorem isClosed_ker [T2Space M] :
    IsClosed (ρ.toRepresentation.ker : Set (Field.absoluteGaloisGroup F)) := by
  have : (ρ.toRepresentation.ker : Set (Field.absoluteGaloisGroup F)) =
      ⋂ x : M, {g | ρ g x = x} := by
    ext g
    simp [MonoidHom.mem_ker, LinearMap.ext_iff]
  rw [this]
  exact isClosed_iInter fun x ↦ isClosed_eq (ρ.continuous_orbit x) continuous_const

/-- A representation on which `Gal(F^alg / K_S)` acts trivially is unramified outside `S`. -/
theorem IsUnramifiedOutside.of_fixingSubgroup_le_ker
    (h : (maxUnramifiedOutside F (AlgebraicClosure F) S).fixingSubgroup ≤
      ρ.toRepresentation.ker) :
    ρ.IsUnramifiedOutside S :=
  isUnramifiedOutside_iff.2 fun _ hv ↦ isUnramifiedAt_iff.2 fun Q hQ hQv σ hσ ↦ by
    have := hQ.isPrime
    exact MonoidHom.mem_ker.1 (h (inertiaGroup_le_fixingSubgroup_maxUnramifiedOutside hv Q hQv hσ))

/-- **Unramified outside `S` means trivial on `Gal(F^alg / K_S)`.** A continuous representation
of `G_F` on a Hausdorff module is unramified outside `S` exactly when the absolute Galois group of
the maximal extension `K_S` unramified outside `S` acts trivially. -/
theorem isUnramifiedOutside_iff_fixingSubgroup_le_ker [T2Space M] :
    ρ.IsUnramifiedOutside S ↔
      (maxUnramifiedOutside F (AlgebraicClosure F) S).fixingSubgroup ≤
        ρ.toRepresentation.ker :=
  ⟨fun h ↦ fixingSubgroup_maxUnramifiedOutside_le isClosed_ker
    fun v hv Q hQ hQv σ hσ ↦ by
      simpa using isUnramifiedAt_iff.1 (isUnramifiedOutside_iff.1 h v hv) Q hQ hQv σ hσ,
    IsUnramifiedOutside.of_fixingSubgroup_le_ker⟩

/-- **Descent to `G_{F,S}`.** A continuous representation of `G_F` unramified outside `S`, on a
Hausdorff module, as a continuous representation of `G_{F,S} = Gal(K_S / F)`: `σ|_{K_S}` acts by
`ρ σ`. -/
def descendS [T2Space M] (ρ : ContinuousRep (Field.absoluteGaloisGroup F) A M)
    (h : ρ.IsUnramifiedOutside S) :
    ContinuousRep (galoisGroupS F (AlgebraicClosure F) S) A M where
  toRepresentation :=
    ((QuotientGroup.lift (maxUnramifiedOutside F (AlgebraicClosure F) S).fixingSubgroup
      ρ.toRepresentation
      (isUnramifiedOutside_iff_fixingSubgroup_le_ker.1 h)).comp
        (quotientFixingSubgroupEquivS F (AlgebraicClosure F) S).symm.toMonoidHom)
  continuous_action := by
    -- `G_F × M → G_{F,S} × M` is an open surjection, hence a quotient map
    have hq : Topology.IsQuotientMap
        (Prod.map (restrictionS F (AlgebraicClosure F) S) (id : M → M)) :=
      ((isOpenMap_restrictionS F _ S).prodMap IsOpenMap.id).isQuotientMap
        ((restrictionS F _ S).continuous.prodMap continuous_id)
        ((restrictionS_surjective F _ S).prodMap Function.surjective_id)
    refine hq.continuous_iff.2 ?_
    have : (fun p : galoisGroupS F (AlgebraicClosure F) S × M ↦
        ((QuotientGroup.lift (maxUnramifiedOutside F (AlgebraicClosure F) S).fixingSubgroup
          ρ.toRepresentation (isUnramifiedOutside_iff_fixingSubgroup_le_ker.1 h)).comp
            (quotientFixingSubgroupEquivS F (AlgebraicClosure F) S).symm.toMonoidHom) p.1 p.2) ∘
          Prod.map (restrictionS F (AlgebraicClosure F) S) id =
        fun p : Gal(AlgebraicClosure F/F) × M ↦ ρ p.1 p.2 := by
      funext ⟨σ, x⟩
      change QuotientGroup.lift (maxUnramifiedOutside F (AlgebraicClosure F) S).fixingSubgroup
        ρ.toRepresentation (isUnramifiedOutside_iff_fixingSubgroup_le_ker.1 h)
          ((quotientFixingSubgroupEquivS F (AlgebraicClosure F) S).symm
            (restrictionS F (AlgebraicClosure F) S σ)) x = ρ σ x
      rw [quotientFixingSubgroupEquivS_symm_restrictionS]
      rfl
    rw [this]
    exact ρ.continuous_action

variable [T2Space M]

@[simp]
theorem descendS_restrictionS_apply (h : ρ.IsUnramifiedOutside S)
    (σ : Gal(AlgebraicClosure F/F)) :
    ρ.descendS h (restrictionS F (AlgebraicClosure F) S σ) = ρ σ := by
  change QuotientGroup.lift (maxUnramifiedOutside F (AlgebraicClosure F) S).fixingSubgroup
    ρ.toRepresentation (isUnramifiedOutside_iff_fixingSubgroup_le_ker.1 h)
      ((quotientFixingSubgroupEquivS F (AlgebraicClosure F) S).symm
        (restrictionS F (AlgebraicClosure F) S σ)) = ρ σ
  rw [quotientFixingSubgroupEquivS_symm_restrictionS]
  rfl

/-- The descended representation restricts back to `ρ` along `G_F → G_{F,S}`. -/
@[simp]
theorem res_descendS (h : ρ.IsUnramifiedOutside S) :
    (ρ.descendS h).res (restrictionS F (AlgebraicClosure F) S) = ρ :=
  ext fun σ x ↦ by
    rw [res_apply, descendS_restrictionS_apply (σ := σ)]
    rfl

/-- **The unramified factorisation criterion.** A continuous representation of `G_F` on a
Hausdorff module is unramified outside `S` exactly when it is the restriction of a continuous
representation of `G_{F,S}` along `G_F → G_{F,S}`. -/
theorem isUnramifiedOutside_iff_exists_res_eq :
    ρ.IsUnramifiedOutside S ↔ ∃ ρ' : ContinuousRep (galoisGroupS F (AlgebraicClosure F) S) A M,
      ρ'.res (restrictionS F (AlgebraicClosure F) S) = ρ := by
  refine ⟨fun h ↦ ⟨ρ.descendS h, res_descendS h⟩, ?_⟩
  rintro ⟨ρ', rfl⟩
  refine IsUnramifiedOutside.of_fixingSubgroup_le_ker fun σ hσ ↦ MonoidHom.mem_ker.2 ?_
  have := res_apply ρ' (restrictionS F (AlgebraicClosure F) S) σ
  rw [(restrictionS_eq_one_iff F _ S).2 hσ, map_one] at this
  exact this

/-- The descent to `G_{F,S}` does not depend on the proof of unramifiedness, and it is unique:
a representation of `G_{F,S}` restricting to `ρ` is `ρ.descendS h`. -/
theorem eq_descendS_of_res_eq (h : ρ.IsUnramifiedOutside S)
    {ρ' : ContinuousRep (galoisGroupS F (AlgebraicClosure F) S) A M}
    (h' : ρ'.res (restrictionS F (AlgebraicClosure F) S) = ρ) :
    ρ' = ρ.descendS h := by
  refine ext fun g x ↦ ?_
  obtain ⟨σ, rfl⟩ := restrictionS_surjective F (AlgebraicClosure F) S g
  rw [descendS_restrictionS_apply (σ := σ), ← h']
  exact (LinearMap.congr_fun (res_apply ρ' _ σ) x).symm

end ContinuousRep

end TauCeti
