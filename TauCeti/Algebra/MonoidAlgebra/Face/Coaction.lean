/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.RingTheory.KrullDimension.Basic
public import TauCeti.Algebra.Group.Submonoid.Saturation
public import TauCeti.Algebra.MonoidAlgebra.Coaction
public import TauCeti.Algebra.MonoidAlgebra.Face.Basic
public import TauCeti.Algebra.MonoidAlgebra.GroupCompletion
public import TauCeti.Algebra.MonoidAlgebra.KrullDimension
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.RingTheory.FiniteType
import TauCeti.Algebra.Group.UniqueProds.TorsionFree
import TauCeti.Algebra.MonoidAlgebra.Localization
import TauCeti.RingTheory.KrullDimension.FiniteType

/-!
# Orbit localizations, torus coactions, and Krull dimensions of face algebras

Let `S` be an additive submonoid of an abelian group `G` and `F : SaturatedAddSubmonoid S` a face
of `S`.

1. **Orbit localizations.** Inverting all coefficient-one monomials of `R[F]` yields
   `R[F.faceSubgroup]` (`SaturatedAddSubmonoid.isLocalization_addMonoidAlgebra_faceSubgroup`). When
   `S.FG`, `R[F.faceSubgroup]` over `R[F]` is a principal localization
   `IsLocalization.Away (single u 1)` at an interior monomial
   (`SaturatedAddSubmonoid.exists_isLocalization_away_faceSubgroup`). Composing face restriction
   with `F.toFaceSubgroup` gives `F.orbitMap R : R[S] →ₐ[R] R[F.faceSubgroup]` with kernel
   `F.toAddSubmonoid.faceIdeal R` (`SaturatedAddSubmonoid.ker_orbitMap`).
2. **Torus coaction.** Specializing `AddMonoidAlgebra.gradedCoaction` to `S.toGroupClosure` gives
   `S.torusCoaction R`, the native coaction of `Spec R[AddSubgroup.closure S]` on `Spec R[S]`,
   for which face restriction, `F.orbitMap R`, and normalization are equivariant.
3. **Krull dimensions and ranks.** Over a field `k` and torsion-free `G`, for `S.FG` we prove
   `ringKrullDim k[F] = ringKrullDim k[F.faceSubgroup] = Module.finrank ℤ F.faceSubgroup`
   (`SaturatedAddSubmonoid.ringKrullDim_addMonoidAlgebra` and
   `SaturatedAddSubmonoid.ringKrullDim_addMonoidAlgebra_faceSubgroup`). For any abelian group `G`,
   `S.FG` gives strict monotonicity of `F ↦ Module.finrank ℤ F.faceSubgroup`
   (`SaturatedAddSubmonoid.finrank_faceSubgroup_strictMono`).

## Main declarations

* `SaturatedAddSubmonoid.isLocalization_addMonoidAlgebra_faceSubgroup` and
  `SaturatedAddSubmonoid.exists_isLocalization_away_faceSubgroup`: orbit localizations.
* `SaturatedAddSubmonoid.orbitMap` and `SaturatedAddSubmonoid.ker_orbitMap`: orbit coordinate hom.
* `AddSubmonoid.torusCoaction` and `AddMonoidAlgebra.map_faceRestriction_comp_gradedCoaction`:
  native torus coaction and equivariance.
* `SaturatedAddSubmonoid.ringKrullDim_addMonoidAlgebra`,
  `SaturatedAddSubmonoid.ringKrullDim_addMonoidAlgebra_faceSubgroup`, and
  `SaturatedAddSubmonoid.finrank_faceSubgroup_strictMono`: Krull dimensions and strict rank
  monotonicity of faces.

## References

* W. Bruns and J. Gubeladze, *Polytopes, Rings, and K-Theory*, Chapters 2 and 4.
* E. Miller and B. Sturmfels, *Combinatorial Commutative Algebra*, Chapter 7.
* W. Fulton, *Introduction to Toric Varieties*, §§1.3 and 3.1.
-/

public section

open scoped TensorProduct
open AddMonoidAlgebra

namespace SaturatedAddSubmonoid

section OrbitMap

variable {G : Type*} [AddCommGroup G] {S : AddSubmonoid G} (F : SaturatedAddSubmonoid S)

/-- For any face `F` of `S`, `R[F.faceSubgroup]` is the localization of `R[F]` at all
coefficient-one monomials along `F.toFaceSubgroup`. -/
theorem isLocalization_addMonoidAlgebra_faceSubgroup (R : Type*) [CommSemiring R] :
    letI := (mapDomainRingHom R F.toFaceSubgroup).toAlgebra
    IsLocalization (MonoidHom.mrange (of R F)) (AddMonoidAlgebra R F.faceSubgroup) :=
  isLocalization_mapDomain_of_single F.toFaceSubgroup_injective
    (fun s ↦ by
      obtain ⟨m, hm⟩ := s.property
      rw [← hm, of_apply, mapDomain_single]
      exact (Group.isUnit (Multiplicative.ofAdd (F.toFaceSubgroup m.toAdd))).map
        (of R F.faceSubgroup))
    (fun g ↦ by
      obtain ⟨a, b, hab⟩ := F.exists_add_toFaceSubgroup_eq g
      exact ⟨a, ⟨of R F (Multiplicative.ofAdd b), _, rfl⟩, by simp [of_apply, hab]⟩)

/-- When `S` is finitely generated, `R[F.faceSubgroup]` is a localization of the closed face
algebra `R[F]` away from a single monomial `single u 1`. -/
theorem exists_isLocalization_away_faceSubgroup (hS : S.FG) (R : Type*) [CommSemiring R] :
    ∃ u : F,
      letI := (mapDomainRingHom R F.toFaceSubgroup).toAlgebra
      IsLocalization.Away (single u (1 : R)) (AddMonoidAlgebra R F.faceSubgroup) := by
  have : AddMonoid.FG S := (AddMonoid.fg_iff_addSubmonoid_fg S).2 hS
  exact exists_isLocalization_away_of_exists_add_eq F.toFaceSubgroup_injective
    F.exists_add_toFaceSubgroup_eq R

/-- Coordinate-ring homomorphism of the torus orbit associated to a face `F` of `S`, obtained by
restricting `R[S]` to `R[F]` and localizing along `F.toFaceSubgroup : F →+ F.faceSubgroup`. -/
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

/-- On a monomial in `F`, `F.orbitMap R` sends `single a r` to `single (F.toFaceSubgroup a) r`. -/
theorem orbitMap_single_mem (R : Type*) [CommSemiring R] (a : F) (r : R) :
    F.orbitMap R (single (a : S) r) = single (F.toFaceSubgroup a) r :=
  F.orbitMap_single_of_mem R a.property r

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

end OrbitMap

end SaturatedAddSubmonoid

namespace AddMonoidAlgebra

/-- Restriction to a face `F` is equivariant with respect to `gradedCoaction`. -/
theorem map_faceRestriction_comp_gradedCoaction (R : Type*) [CommSemiring R] {M L : Type*}
    [AddCommMonoid M] [AddCommMonoid L] (w : M →+ L) (F : SaturatedAddSubmonoid M) :
    (Algebra.TensorProduct.map (AlgHom.id R (AddMonoidAlgebra R L))
      (F.toAddSubmonoid.faceRestriction F.addSaturated R)).comp (gradedCoaction R w) =
      (gradedCoaction R (w.comp F.toAddSubmonoid.subtype)).comp
        (F.toAddSubmonoid.faceRestriction F.addSaturated R) := by
  ext m
  by_cases hm : m ∈ F
  · rw [AlgHom.comp_apply, AlgHom.comp_apply, gradedCoaction_single, Algebra.TensorProduct.map_tmul,
      AlgHom.id_apply, F.toAddSubmonoid.faceRestriction_single_of_mem F.addSaturated hm]
    simp
  · simp [F.toAddSubmonoid.faceRestriction_single_of_notMem F.addSaturated hm]

end AddMonoidAlgebra

namespace AddSubmonoid

section TorusCoaction

variable {G : Type*} [AddCommGroup G] (S : AddSubmonoid G) (R : Type*) [CommSemiring R]

/-- The native coaction of the dense torus algebra `R[AddSubgroup.closure S]` on `R[S]`. -/
noncomputable def torusCoaction :
    AddMonoidAlgebra R S →ₐ[R]
      AddMonoidAlgebra R (AddSubgroup.closure (S : Set G)) ⊗[R] AddMonoidAlgebra R S :=
  gradedCoaction R S.toGroupClosure

/-- Explicit definition of `AddSubmonoid.torusCoaction`. -/
theorem torusCoaction_def : S.torusCoaction R = gradedCoaction R S.toGroupClosure := (rfl)

/-- `S.torusCoaction R` sends `single s r` to `single (S.toGroupClosure s) 1 ⊗ₜ single s r`. -/
@[simp]
theorem torusCoaction_single (s : S) (r : R) :
    S.torusCoaction R (single s r) = single (S.toGroupClosure s) 1 ⊗ₜ[R] single s r :=
  gradedCoaction_single R S.toGroupClosure s r

/-- For any face `F` of `S`, `F.orbitMap R` is equivariant for the ambient torus coaction of
`R[AddSubgroup.closure S]`. -/
theorem map_orbitMap_comp_torusCoaction (F : SaturatedAddSubmonoid S) :
    (Algebra.TensorProduct.map (AlgHom.id R _) (F.orbitMap R)).comp (S.torusCoaction R) =
      (gradedCoaction R F.faceSubgroup.subtype).comp (F.orbitMap R) := by
  ext s
  by_cases hs : s ∈ F
  · rw [AlgHom.comp_apply, AlgHom.comp_apply, torusCoaction_single, Algebra.TensorProduct.map_tmul,
      AlgHom.id_apply, F.orbitMap_single_of_mem R hs, gradedCoaction_single,
      AddSubgroup.coe_subtype, F.coe_toFaceSubgroup]
  · simp [F.orbitMap_single_of_notMem R hs]

/-- The normalization map from `R[S]` to `R[S.nsmulSaturation ⊓ AddSubgroup.closure S]` is
equivariant for the ambient torus `R[AddSubgroup.closure S]`. -/
theorem map_inclusion_nsmulSaturation_comp_torusCoaction :
    (Algebra.TensorProduct.map (AlgHom.id R _)
      (mapDomainAlgHom R R
        (inclusion (le_inf S.le_nsmulSaturation AddSubgroup.subset_closure)))).comp
      (S.torusCoaction R) =
      (gradedCoaction R S.nsmulSaturationInfClosureToGroupClosure).comp
        (mapDomainAlgHom R R
          (inclusion (le_inf S.le_nsmulSaturation AddSubgroup.subset_closure))) := by
  simpa [torusCoaction] using map_mapDomain_comp_gradedCoaction R (g := .id _)
    (AddMonoidHom.ext fun s ↦ S.nsmulSaturationInfClosureToGroupClosure_inclusion_apply s)

end TorusCoaction

end AddSubmonoid

namespace SaturatedAddSubmonoid

section KrullDimension

variable {G : Type*} [AddCommGroup G] [HasUniqueDiv G] {S : AddSubmonoid G}

/-- Over a field `k`, the localized orbit coordinate algebra `k[F.faceSubgroup]` of a face `F` of a
finitely generated submonoid `S` has Krull dimension `Module.finrank ℤ F.faceSubgroup`. -/
theorem ringKrullDim_addMonoidAlgebra_faceSubgroup (hS : S.FG) (F : SaturatedAddSubmonoid S)
    (k : Type*) [Field k] :
    ringKrullDim (AddMonoidAlgebra k F.faceSubgroup) = Module.finrank ℤ F.faceSubgroup := by
  have : AddMonoid.FG S := (AddMonoid.fg_iff_addSubmonoid_fg S).2 hS
  have : Module.Finite ℤ F.faceSubgroup := Module.Finite.iff_addGroup_fg.2
    ((AddGroup.fg_iff_addSubgroup_fg F.faceSubgroup).2 (F.fg_faceSubgroup F.fg_toAddSubmonoid))
  have : HasUniqueDiv F.faceSubgroup := Function.Injective.hasUniqueDiv
    ((AddSubgroup.closure (S : Set G)).subtype.comp F.faceSubgroup.subtype)
    ((AddSubgroup.closure (S : Set G)).subtype_injective.comp F.faceSubgroup.subtype_injective)
  exact AddMonoidAlgebra.ringKrullDim_of_free k F.faceSubgroup

/-- Over a field `k`, the closed face algebra `k[F]` of a face `F` of a finitely generated
submonoid `S` has Krull dimension `Module.finrank ℤ F.faceSubgroup`. -/
theorem ringKrullDim_addMonoidAlgebra (hS : S.FG) (F : SaturatedAddSubmonoid S)
    (k : Type*) [Field k] :
    ringKrullDim (AddMonoidAlgebra k F) = Module.finrank ℤ F.faceSubgroup := by
  have : AddMonoid.FG S := (AddMonoid.fg_iff_addSubmonoid_fg S).2 hS
  have : Algebra.FiniteType k (AddMonoidAlgebra k F) := AddMonoidAlgebra.finiteType_of_fg k F
  have : UniqueSums F := .of_injective_addHom (S.subtype.comp F.toAddSubmonoid.subtype).toAddHom
    (S.subtype_injective.comp F.toAddSubmonoid.subtype_injective) inferInstance
  obtain ⟨u, _⟩ := F.exists_isLocalization_away_faceSubgroup hS k
  let := (mapDomainRingHom k F.toFaceSubgroup).toAlgebra
  rw [← TauCeti.ringKrullDim_localization_away k
    (single_ne_zero.2 (one_ne_zero : (1 : k) ≠ 0) : single u (1 : k) ≠ 0)
    (AddMonoidAlgebra k F.faceSubgroup), F.ringKrullDim_addMonoidAlgebra_faceSubgroup hS k]

end KrullDimension

section Rank

variable {G : Type*} [AddCommGroup G] {S : AddSubmonoid G}

/-- Strict inclusion of faces of a finitely generated submonoid `S` of an abelian group strictly
increases the rank of `F.faceSubgroup`. -/
theorem finrank_faceSubgroup_strictMono (hS : S.FG) :
    StrictMono (fun F : SaturatedAddSubmonoid S ↦ Module.finrank ℤ F.faceSubgroup) := by
  intro F₁ F₂ hlt
  obtain ⟨s, hs₂, hs₁⟩ := IsConcreteLE.exists_of_lt hlt
  have : AddMonoid.FG S := (AddMonoid.fg_iff_addSubmonoid_fg S).2 hS
  have : Module.Finite ℤ F₂.faceSubgroup := Module.Finite.iff_addGroup_fg.2
    ((AddGroup.fg_iff_addSubgroup_fg F₂.faceSubgroup).2 (F₂.fg_faceSubgroup F₂.fg_toAddSubmonoid))
  let H : Submodule ℤ F₂.faceSubgroup :=
    F₁.faceSubgroup.toIntSubmodule.comap F₂.faceSubgroup.toIntSubmodule.subtype
  have hle : F₁.faceSubgroup.toIntSubmodule ≤ F₂.faceSubgroup.toIntSubmodule :=
    faceSubgroup_mono hlt.le
  have hrankH : Module.finrank ℤ H = Module.finrank ℤ F₁.faceSubgroup :=
    (Submodule.comapSubtypeEquivOfLe hle).finrank_eq
  let q : F₂.faceSubgroup ⧸ H := Submodule.Quotient.mk (F₂.toFaceSubgroup ⟨s, hs₂⟩)
  have hq_ind : LinearIndependent ℤ (fun _ : Unit ↦ q) := by
    rw [Fintype.linearIndependent_iff]
    intro c hc _
    by_contra hc0
    have hc_mem : (c () • F₂.toFaceSubgroup ⟨s, hs₂⟩) ∈ H :=
      (Submodule.Quotient.mk_eq_zero H).1 (by simpa [q] using hc)
    have hzsmul : c () • S.toGroupClosure s ∈ F₁.faceSubgroup := by
      rw [← F₂.coe_toFaceSubgroup ⟨s, hs₂⟩, ← AddSubgroup.coe_zsmul]
      exact Submodule.mem_comap.1 hc_mem
    have hnsmul : (c ()).natAbs • S.toGroupClosure s ∈ F₁.faceSubgroup := by
      rcases le_total 0 (c ()) with hcpos | hcneg
      · rwa [← natCast_zsmul, Int.natAbs_of_nonneg hcpos]
      · have hneg := F₁.faceSubgroup.neg_mem hzsmul
        have hnat : ((c ()).natAbs : ℤ) = -c () := Int.ofNat_natAbs_of_nonpos hcneg
        rwa [← neg_zsmul, ← hnat, natCast_zsmul] at hneg
    rw [← map_nsmul, F₁.toGroupClosure_mem_faceSubgroup_iff] at hnsmul
    exact hs₁ ((F₁.nsmulSaturated hnsmul).resolve_left (Int.natAbs_pos.2 hc0).ne')
  have hq_pos : 1 ≤ Module.finrank ℤ (F₂.faceSubgroup ⧸ H) := by
    simpa using hq_ind.fintype_card_le_finrank
  have hsplit := Submodule.finrank_quotient_add_finrank H
  dsimp only
  omega

end Rank

end SaturatedAddSubmonoid
