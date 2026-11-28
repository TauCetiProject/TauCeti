/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Localization.Away.Basic
public import TauCeti.Algebra.Group.Submonoid.Saturation
public import TauCeti.Algebra.MonoidAlgebra.Face.Basic
import TauCeti.Algebra.MonoidAlgebra.Localization

/-!
# Face localizations and orbit coordinate maps of semigroup algebras

For an additive submonoid `S` of an abelian group `G` and a face `F : SaturatedAddSubmonoid S`:

* Inverting all coefficient-one monomials of `R[F]` along `F.toFaceSubgroup : F →+ F.faceSubgroup`
  yields `R[F.faceSubgroup]` (`SaturatedAddSubmonoid.isLocalization_addMonoidAlgebra_faceSubgroup`),
  and when `F.toAddSubmonoid.FG`, this is a principal localization away from a single monomial
  (`SaturatedAddSubmonoid.exists_isLocalization_away_faceSubgroup`).
* Composing face restriction `R[S] →ₐ[R] R[F]` with `F.toFaceSubgroup` defines the orbit
  coordinate-ring homomorphism `F.orbitMap R : R[S] →ₐ[R] R[F.faceSubgroup]` with kernel
  `F.toAddSubmonoid.faceIdeal R` (`SaturatedAddSubmonoid.ker_orbitMap`), which commutes with
  positive-multiple saturation (`orbitMap_comp_mapDomainAlgHom_inclusion_nsmulSaturation`).

## References

* W. Bruns and J. Gubeladze, *Polytopes, Rings, and K-Theory*, Chapters 2 and 4.
* W. Fulton, *Introduction to Toric Varieties*, §§1.3 and 3.1.
-/

public section

open AddMonoidAlgebra

namespace SaturatedAddSubmonoid

variable {G : Type*} [AddCommGroup G] {S : AddSubmonoid G} (F : SaturatedAddSubmonoid S)

/-- For any face `F` of `S`, `R[F.faceSubgroup]` is the localization of `R[F]` at all
coefficient-one monomials along `F.toFaceSubgroup`. -/
theorem isLocalization_addMonoidAlgebra_faceSubgroup (R : Type*) [CommSemiring R] :
    letI := (mapDomainRingHom R F.toFaceSubgroup).toAlgebra
    IsLocalization (MonoidHom.mrange (of R F)) (AddMonoidAlgebra R F.faceSubgroup) :=
  isLocalization_mrange_of_of_exists_add_eq F.toFaceSubgroup_injective
    F.exists_add_toFaceSubgroup_eq R

/-- When `F` is finitely generated, `R[F.faceSubgroup]` is a localization of the closed face
algebra `R[F]` away from a single monomial `single u 1`. -/
theorem exists_isLocalization_away_faceSubgroup (hF : F.toAddSubmonoid.FG) (R : Type*)
    [CommSemiring R] :
    ∃ u : F,
      letI := (mapDomainRingHom R F.toFaceSubgroup).toAlgebra
      IsLocalization.Away (single u (1 : R)) (AddMonoidAlgebra R F.faceSubgroup) :=
  have : AddMonoid.FG F := (AddMonoid.fg_iff_addSubmonoid_fg F.toAddSubmonoid).2 hF
  exists_isLocalization_away_of_exists_add_eq F.toFaceSubgroup_injective
    F.exists_add_toFaceSubgroup_eq R

/-- Coordinate-ring homomorphism of the diagonalizable-group orbit associated to a face `F` of `S`,
obtained by restricting `R[S]` to `R[F]` and localizing along `F.toFaceSubgroup : F →+
F.faceSubgroup`. -/
noncomputable def orbitMap (R : Type*) [CommSemiring R] :
    AddMonoidAlgebra R S →ₐ[R] AddMonoidAlgebra R F.faceSubgroup :=
  (mapDomainAlgHom R R F.toFaceSubgroup).comp (F.toAddSubmonoid.faceRestriction F.addSaturated R)

/-- Explicit definition of `SaturatedAddSubmonoid.orbitMap`. -/
theorem orbitMap_def (R : Type*) [CommSemiring R] :
    F.orbitMap R = (mapDomainAlgHom R R F.toFaceSubgroup).comp
      (F.toAddSubmonoid.faceRestriction F.addSaturated R) := (rfl)

/-- On a monomial whose exponent lies in `F`, `F.orbitMap R` sends `single s r` to
`single (F.toFaceSubgroup ⟨s, hs⟩) r`. -/
@[simp]
theorem orbitMap_single_of_mem (R : Type*) [CommSemiring R] {s : S} (hs : s ∈ F) (r : R) :
    F.orbitMap R (single s r) = single (F.toFaceSubgroup ⟨s, hs⟩) r := by
  rw [orbitMap_def, AlgHom.comp_apply,
    F.toAddSubmonoid.faceRestriction_single_of_mem F.addSaturated hs, mapDomainAlgHom_apply,
    mapDomain_single]

/-- On a monomial outside `F`, `F.orbitMap R` vanishes. -/
@[simp]
theorem orbitMap_single_of_notMem (R : Type*) [CommSemiring R] {s : S} (hs : s ∉ F) (r : R) :
    F.orbitMap R (single s r) = 0 := by
  simp [orbitMap, F.toAddSubmonoid.faceRestriction_single_of_notMem F.addSaturated hs]

/-- Over any commutative semiring `R`, the kernel of `F.orbitMap R` is `F.faceIdeal R`. -/
@[simp]
theorem ker_orbitMap (R : Type*) [CommSemiring R] :
    RingHom.ker (F.orbitMap R) = F.toAddSubmonoid.faceIdeal R := by
  ext p
  rw [RingHom.mem_ker, orbitMap_def, AlgHom.comp_apply, ← F.toAddSubmonoid.ker_faceRestriction
    F.addSaturated, RingHom.mem_ker]
  exact ⟨fun h ↦ mapDomain_injective F.toFaceSubgroup_injective (by simpa using h),
    fun h ↦ by simp [h]⟩

private theorem toFaceSubgroup_inclusion_nsmulSaturation {s : S} (hs : s ∈ F)
    (hs_sat : AddSubmonoid.inclusion (le_inf S.le_nsmulSaturation AddSubgroup.subset_closure) s ∈
      (S.nsmulSaturationInfClosureFaceOrderIso).symm F) :
    ((S.nsmulSaturationInfClosureFaceOrderIso).symm F).toFaceSubgroup ⟨_, hs_sat⟩ =
      F.faceSubgroupNSMulSaturationEquiv.symm.toAddMonoidHom
        (AddSubgroup.inclusion F.faceSubgroup.le_nsmulSaturation (F.toFaceSubgroup ⟨s, hs⟩)) :=
  F.faceSubgroupNSMulSaturationEquiv.eq_symm_apply.2 <| Subtype.ext <| Subtype.ext <| by
    rw [F.coe_faceSubgroupNSMulSaturationEquiv_apply, SaturatedAddSubmonoid.coe_toFaceSubgroup,
      AddSubmonoid.coe_toGroupClosure, AddSubgroup.coe_inclusion, F.coe_toFaceSubgroup,
      AddSubmonoid.coe_toGroupClosure]; rfl

/-- Under `faceSubgroupNSMulSaturationEquiv`, `F_sat.orbitMap R` and `F.orbitMap R` commute with
the saturation inclusion `R[S] →ₐ[R] R[S_sat]` and the transported face-subgroup inclusion
`F.faceSubgroup →+ F_sat.faceSubgroup`. -/
theorem orbitMap_comp_mapDomainAlgHom_inclusion_nsmulSaturation (R : Type*) [CommSemiring R] :
    (((S.nsmulSaturationInfClosureFaceOrderIso).symm F).orbitMap R).comp (mapDomainAlgHom R R
        (AddSubmonoid.inclusion (le_inf S.le_nsmulSaturation AddSubgroup.subset_closure))) =
      (mapDomainAlgHom R R (F.faceSubgroupNSMulSaturationEquiv.symm.toAddMonoidHom.comp
        (AddSubgroup.inclusion F.faceSubgroup.le_nsmulSaturation))).comp (F.orbitMap R) := by
  let inc := AddSubmonoid.inclusion (le_inf S.le_nsmulSaturation AddSubgroup.subset_closure)
  let Fsat := (S.nsmulSaturationInfClosureFaceOrderIso).symm F
  have hmem_iff (s : S) : inc s ∈ Fsat ↔ s ∈ F := by
    rw [← SaturatedAddSubmonoid.mem_comap, ← S.nsmulSaturationInfClosureFaceOrderIso_apply,
      S.nsmulSaturationInfClosureFaceOrderIso.apply_symm_apply]
  refine AddMonoidAlgebra.algHom_ext (fun s ↦ ?_) (Subsingleton.elim _ _)
  by_cases hs : s ∈ F
  · have hs_sat : inc s ∈ Fsat := (hmem_iff s).2 hs
    rw [AlgHom.comp_apply, mapDomainAlgHom_apply, mapDomain_single,
      Fsat.orbitMap_single_of_mem R hs_sat, AlgHom.comp_apply, F.orbitMap_single_of_mem R hs,
      mapDomainAlgHom_apply, mapDomain_single, F.toFaceSubgroup_inclusion_nsmulSaturation hs hs_sat]
    rfl
  · rw [AlgHom.comp_apply, mapDomainAlgHom_apply, mapDomain_single,
      Fsat.orbitMap_single_of_notMem R (fun h ↦ hs ((hmem_iff s).1 h)), AlgHom.comp_apply,
      F.orbitMap_single_of_notMem R hs, map_zero]

end SaturatedAddSubmonoid
