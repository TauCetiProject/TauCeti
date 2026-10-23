/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal

/-!
# Field-valued points and residue-field data

An algebra map to a field determines a prime ideal and an embedding of its
residue field. Conversely, these data determine the algebra map.
The forward map from residue-field data is defined for any commutative target algebra.

## References

* Stacks Project, Tag 04GW.
* Taylor Dupuy, Thomas Tucker, and Zhuoran Wang, pcfawd-formalization at `9a20b3f`,
  `lean/Pcf/Stacks/Abhyankar/StrictHenselizationConstruction.lean`,
  `PointedEtaleNeighborhood`.
-/

public section

namespace AlgHom

variable {R S Ω : Type*} [CommRing R] [CommRing S] [Field Ω] [Algebra R S] [Algebra R Ω]

local instance (point : S →ₐ[R] Ω) : (RingHom.ker point).IsPrime :=
  RingHom.ker_isPrime point

/-- The residue-field embedding induced by a field-valued point. -/
noncomputable def residueEmbedding (point : S →ₐ[R] Ω) :
    (RingHom.ker point).ResidueField →ₐ[R] Ω :=
  Ideal.ResidueField.liftₐ _ point le_rfl fun element hnonzero ↦ by
    exact isUnit_iff_ne_zero.mpr hnonzero

/-- The residue-field embedding recovers the original point. -/
@[simp]
theorem residueEmbedding_comp (point : S →ₐ[R] Ω) :
    (point.residueEmbedding).comp
      (IsScalarTower.toAlgHom R S (RingHom.ker point).ResidueField) = point :=
  Ideal.ResidueField.liftₐ_comp_toAlgHom _ _ _ _

/-- A field-valued point factors uniquely through the residue field of its kernel. -/
theorem existsUnique_residueEmbedding (point : S →ₐ[R] Ω) :
    ∃! embedding : (RingHom.ker point).ResidueField →ₐ[R] Ω,
      embedding.comp (IsScalarTower.toAlgHom R S (RingHom.ker point).ResidueField) = point := by
  refine ⟨point.residueEmbedding, point.residueEmbedding_comp, ?_⟩
  intro embedding equality
  exact Ideal.ResidueField.algHom_ext
    (equality.trans point.residueEmbedding_comp.symm)

end AlgHom

namespace Ideal

variable {R S Ω : Type*} [CommRing R] [CommRing S] [CommRing Ω]
  [Algebra R S] [Algebra R Ω]

/-- A residue-field embedding recovers the prime through its kernel. -/
@[simp]
theorem ker_residueEmbedding_comp (prime : Ideal S) [prime.IsPrime]
    [Nontrivial Ω] (embedding : prime.ResidueField →ₐ[R] Ω) :
    RingHom.ker (embedding.comp (IsScalarTower.toAlgHom R S prime.ResidueField)) = prime := by
  ext element
  simp only [RingHom.mem_ker, AlgHom.comp_apply,
    map_eq_zero_iff embedding embedding.injective, IsScalarTower.toAlgHom_apply]
  exact Ideal.algebraMap_residueField_eq_zero

/-- Compatibility of residue embeddings is exactly compatibility of the associated points. -/
theorem residueEmbedding_comp_map_iff {T : Type*} [CommRing T] [Algebra R T]
    (sourcePrime : Ideal S) [sourcePrime.IsPrime] (targetPrime : Ideal T) [targetPrime.IsPrime]
    (sourceEmbedding : sourcePrime.ResidueField →ₐ[R] Ω)
    (targetEmbedding : targetPrime.ResidueField →ₐ[R] Ω) (morphism : S →ₐ[R] T)
    (hprime : sourcePrime = targetPrime.comap morphism.toRingHom) :
    targetEmbedding.comp (Ideal.ResidueField.mapₐ sourcePrime targetPrime morphism hprime) =
      sourceEmbedding ↔
    (targetEmbedding.comp (IsScalarTower.toAlgHom R T targetPrime.ResidueField)).comp morphism =
      sourceEmbedding.comp (IsScalarTower.toAlgHom R S sourcePrime.ResidueField) := by
  constructor
  · intro equality
    ext element
    have result := DFunLike.congr_fun equality (algebraMap S sourcePrime.ResidueField element)
    simpa only [AlgHom.comp_apply, Ideal.ResidueField.mapₐ_apply,
      Ideal.ResidueField.map_algebraMap, IsScalarTower.toAlgHom_apply,
      AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] using result
  · intro equality
    apply Ideal.ResidueField.algHom_ext
    ext element
    have result := DFunLike.congr_fun equality element
    simpa only [AlgHom.comp_apply, Ideal.ResidueField.mapₐ_apply,
      Ideal.ResidueField.map_algebraMap, IsScalarTower.toAlgHom_apply,
      AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] using result

end Ideal

namespace TauCeti.ResidueField

section CommRing

variable {R S Ω : Type*} [CommRing R] [CommRing S] [CommRing Ω] [Algebra R S] [Algebra R Ω]

/-- A prime and an algebra map from its residue field to the chosen algebra. -/
abbrev PointData (R S Ω : Type*) [CommRing R] [CommRing S] [CommRing Ω]
    [Algebra R S] [Algebra R Ω] :=
  Σ prime : PrimeSpectrum S, prime.asIdeal.ResidueField →ₐ[R] Ω

/-- The algebra-valued point associated with residue-field data. -/
noncomputable def PointData.toAlgHom (data : PointData R S Ω) : S →ₐ[R] Ω :=
  data.2.comp (IsScalarTower.toAlgHom R S data.1.asIdeal.ResidueField)

/-- Evaluate the point induced by residue-field data. -/
@[simp]
theorem PointData.toAlgHom_apply (data : PointData R S Ω) (element : S) :
    data.toAlgHom element = data.2 (algebraMap S data.1.asIdeal.ResidueField element) := by
  simp only [PointData.toAlgHom, AlgHom.comp_apply, IsScalarTower.toAlgHom_apply]

end CommRing

section Nontrivial

variable {R S Ω : Type*} [CommRing R] [CommRing S] [CommRing Ω] [Nontrivial Ω]
  [Algebra R S] [Algebra R Ω]

/-- Residue-field data are determined by their algebra-valued point. -/
theorem PointData.toAlgHom_injective :
    Function.Injective (PointData.toAlgHom : PointData R S Ω → S →ₐ[R] Ω) := by
  rintro ⟨firstPrime, firstEmbedding⟩ ⟨secondPrime, secondEmbedding⟩ equality
  have hprime : firstPrime = secondPrime := by
    apply PrimeSpectrum.ext
    exact (Ideal.ker_residueEmbedding_comp _ firstEmbedding).symm.trans
      ((congrArg RingHom.ker equality).trans
        (Ideal.ker_residueEmbedding_comp _ secondEmbedding))
  subst secondPrime
  congr 1
  exact Ideal.ResidueField.algHom_ext equality

end Nontrivial

section Field

variable {R S Ω : Type*} [CommRing R] [CommRing S] [Field Ω] [Algebra R S] [Algebra R Ω]

local instance (point : S →ₐ[R] Ω) : (RingHom.ker point).IsPrime :=
  RingHom.ker_isPrime point

/-- Residue-field data determine the point bijectively. -/
theorem PointData.toAlgHom_bijective :
    Function.Bijective (PointData.toAlgHom : PointData R S Ω → S →ₐ[R] Ω) := by
  constructor
  · exact PointData.toAlgHom_injective
  · intro point
    exact ⟨⟨⟨RingHom.ker point, inferInstance⟩, point.residueEmbedding⟩,
      point.residueEmbedding_comp⟩

/-- Field-valued points are equivalent to a prime and a residue-field embedding. -/
noncomputable def pointDataEquiv : PointData R S Ω ≃ (S →ₐ[R] Ω) :=
  Equiv.ofBijective PointData.toAlgHom PointData.toAlgHom_bijective

/-- The forward correspondence is the point induced by the residue-field embedding. -/
@[simp]
theorem pointDataEquiv_apply (data : PointData R S Ω) :
    pointDataEquiv data = data.toAlgHom := by
  exact Equiv.ofBijective_apply _ _ _

/-- The inverse correspondence assigns a point its kernel and residue-field embedding. -/
@[simp]
theorem pointDataEquiv_symm_apply (point : S →ₐ[R] Ω) :
    pointDataEquiv.symm point =
      ⟨⟨RingHom.ker point, inferInstance⟩, point.residueEmbedding⟩ := by
  apply pointDataEquiv.injective
  simp only [Equiv.apply_symm_apply, pointDataEquiv_apply, PointData.toAlgHom,
    AlgHom.residueEmbedding_comp]

end Field

variable {R S Ω : Type*} [CommRing R] [CommRing S] [CommRing Ω] [Nontrivial Ω]
  [Algebra R S] [Algebra R Ω]

/-- Compatibility of induced points is compatibility of the prime and residue-field maps. -/
theorem PointData.toAlgHom_comp_iff {T : Type*} [CommRing T] [Algebra R T]
    (source : PointData R S Ω) (target : PointData R T Ω) (morphism : S →ₐ[R] T) :
    target.toAlgHom.comp morphism = source.toAlgHom ↔
      ∃ hprime : source.1.asIdeal = target.1.asIdeal.comap morphism.toRingHom,
        target.2.comp (Ideal.ResidueField.mapₐ source.1.asIdeal target.1.asIdeal morphism hprime) =
          source.2 := by
  constructor
  · intro equality
    have hkernel := congrArg RingHom.ker equality
    rw [← AlgHom.comap_ker] at hkernel
    have hprime : source.1.asIdeal = target.1.asIdeal.comap morphism.toRingHom := by
      have hprime' : source.1.asIdeal = target.1.asIdeal.comap morphism := by
        simpa only [PointData.toAlgHom, Ideal.ker_residueEmbedding_comp] using hkernel.symm
      exact hprime'
    exact ⟨hprime, (Ideal.residueEmbedding_comp_map_iff _ _ _ _ _ hprime).mpr equality⟩
  · rintro ⟨hprime, equality⟩
    exact (Ideal.residueEmbedding_comp_map_iff _ _ _ _ _ hprime).mp equality

end TauCeti.ResidueField
