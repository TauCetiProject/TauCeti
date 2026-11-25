/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.Hom.Set
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.Valuation.ValuationSubring

/-!
# Composite valuation subrings

Let `A` be a valuation subring of a field `K` with residue field `κ(A)`. For a valuation subring
`U` of `κ(A)`, the elements of `A` whose residue lies in `U` form a valuation subring
`A.comapResidue U` of `K`, the composite of `A` with `U`. It lies between the nonunits of `A` and
`A`, and it is `A` exactly when `U = κ(A)`.

Every valuation subring of `K` contained in `A` arises this way from exactly one `U`: the
valuation subrings of `K` contained in `A` are ordered like the valuation subrings of `κ(A)`.
This is the counterpart, for valuation subrings below `A`, of
`ValuationSubring.primeSpectrumOrderEquiv`, which describes those above `A` by the prime ideals
of `A`.

## Main definitions and results

* `ValuationSubring.comapResidue`: the composite of `A` with a valuation subring of `κ(A)`.
* `ValuationSubring.residue_inv`: residues of `x` and `x⁻¹` in `κ(A)` are inverse.
* `ValuationSubring.eq_of_le_of_surjective_residue`: a valuation subring `B ⊆ A` taking every
  residue in `κ(A)` is `A`.
* `ValuationSubring.mem_comapResidue_iff`: its elements are those of `A` with residue in `U`.
* `ValuationSubring.nonunits_subset_comapResidue`, `ValuationSubring.comapResidue_le`: it lies
  between the nonunits of `A` and `A`.
* `ValuationSubring.algebraMap_residueField_mem_of_isTrivialOn`: if the composite contains a field
  `k`, then `U` contains the residues of the elements of `k`.
* `ValuationSubring.comapResidue_eq_self_iff`: it equals `A` exactly when `U = ⊤`.
* `ValuationSubring.mapResidue`: the image in `κ(A)` of a valuation subring contained in `A`.
* `ValuationSubring.residue_mem_mapResidue_iff`: a residue lies in that image exactly when the
  element lies in the subring.
* `ValuationSubring.comapResidue_mapResidue`: every valuation subring contained in `A` is the
  composite of `A` with its image in `κ(A)`.
* `ValuationSubring.comapResidueOrderIso`: the order isomorphism between valuation subrings of
  `κ(A)` and valuation subrings of `K` contained in `A`, with inverse `mapResidue`.
-/

public section

open IsLocalRing

namespace ValuationSubring

variable {K : Type*} [Field K] (A : ValuationSubring K)

/-- The elements of a valuation subring `A` whose residue in `κ(A)` lies in `U`, as a subring. -/
private def comapResidueSubring (U : ValuationSubring (ResidueField A)) : Subring K :=
  (U.toSubring.comap (residue A)).map A.subtype

private theorem mem_comapResidueSubring_iff {U : ValuationSubring (ResidueField A)} {x : K} :
    x ∈ comapResidueSubring A U ↔ ∃ h : x ∈ A, residue A ⟨x, h⟩ ∈ U := by
  simp only [comapResidueSubring, Subring.mem_map, Subring.mem_comap, mem_toSubring]
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a.property, ha⟩
  · rintro ⟨h, hU⟩
    exact ⟨⟨x, h⟩, hU, rfl⟩

/-- The residue of `x⁻¹` is the inverse of the residue of `x` when both lie in `A`. -/
theorem residue_inv {x : K} (hx : x ∈ A) (hx' : x⁻¹ ∈ A) :
    residue A ⟨x⁻¹, hx'⟩ = (residue A ⟨x, hx⟩)⁻¹ := by
  rcases eq_or_ne x 0 with rfl | h0
  · simp [(Subtype.ext (ZeroMemClass.coe_zero A).symm : (⟨0, hx⟩ : A) = 0)]
  refine (eq_inv_of_mul_eq_one_left ?_)
  rw [← map_mul, ← map_one (residue A)]
  congr 1
  exact Subtype.ext (inv_mul_cancel₀ h0)

/-- A nonunit of `A` has residue `0` in `κ(A)`. -/
theorem residue_eq_zero_of_mem_nonunits {x : K} (h : x ∈ A.nonunits) :
    residue A ⟨x, nonunits_subset h⟩ = 0 :=
  (residue_eq_zero_iff _).mpr (coe_mem_nonunits_iff.mp h)

/-- Let `B ⊆ A`. An element of `A` with the same residue in `κ(A)` as an element of `B` lies in
`B`: their difference is a nonunit of `A`, hence of `B`. -/
theorem mem_of_le_of_residue_eq {B : ValuationSubring K} (hBA : B ≤ A) {x b : K} (hx : x ∈ A)
    (hb : b ∈ B) (h : residue A ⟨x, hx⟩ = residue A ⟨b, hBA hb⟩) : x ∈ B := by
  have hsub : x - b ∈ A.nonunits := by
    have : (⟨x, hx⟩ - ⟨b, hBA hb⟩ : A) ∈ maximalIdeal A := by
      rw [← residue_eq_zero_iff, map_sub, h, sub_self]
    exact coe_mem_nonunits_iff.mpr this
  simpa using B.add_mem _ _ (nonunits_subset (nonunits_le_nonunits.mpr hBA hsub)) hb

/-- A valuation subring `B ⊆ A` whose elements take every residue in `κ(A)` is `A` itself. -/
theorem eq_of_le_of_surjective_residue {B : ValuationSubring K} (hBA : B ≤ A)
    (h : Function.Surjective ((residue A).comp (inclusion B A hBA))) : B = A := by
  refine le_antisymm hBA fun x hx ↦ ?_
  obtain ⟨b, hb⟩ := h (residue A ⟨x, hx⟩)
  exact A.mem_of_le_of_residue_eq hBA hx b.property hb.symm

/-- The **composite** of a valuation subring `A` of `K` with a valuation subring `U` of its
residue field: the elements of `A` whose residue lies in `U`. -/
noncomputable def comapResidue (U : ValuationSubring (ResidueField A)) : ValuationSubring K :=
  ofSubring (comapResidueSubring A U) fun x ↦ by
    simp only [mem_comapResidueSubring_iff]
    by_cases hx : x ∈ A
    · by_cases hx' : x⁻¹ ∈ A
      · rcases U.mem_or_inv_mem (residue A ⟨x, hx⟩) with h | h
        · exact .inl ⟨hx, h⟩
        · exact .inr ⟨hx', (residue_inv A hx hx').symm ▸ h⟩
      · -- `x` is a nonunit of `A`, so its residue is `0`
        exact .inl ⟨hx, by
          simp [residue_eq_zero_of_mem_nonunits A (A.mem_nonunits_iff_or.mpr (.inr hx'))]⟩
    · -- `x⁻¹` is a nonunit of `A`, so its residue is `0`
      exact .inr ⟨(A.mem_or_inv_mem x).resolve_left hx, by
        simp [residue_eq_zero_of_mem_nonunits A (A.inv_mem_nonunits_iff.mpr (.inr hx))]⟩

variable {A} {U U' : ValuationSubring (ResidueField A)}

theorem mem_comapResidue_iff {x : K} :
    x ∈ A.comapResidue U ↔ ∃ h : x ∈ A, residue A ⟨x, h⟩ ∈ U :=
  (mem_ofSubring _ _ _).trans (mem_comapResidueSubring_iff A)

@[simp]
theorem coe_mem_comapResidue_iff {a : A} : (a : K) ∈ A.comapResidue U ↔ residue A a ∈ U :=
  mem_comapResidue_iff.trans ⟨fun ⟨_, h⟩ ↦ h, fun h ↦ ⟨a.property, h⟩⟩

theorem comapResidue_le : A.comapResidue U ≤ A :=
  fun _ hx ↦ (mem_comapResidue_iff.mp hx).1

/-- The composite contains every nonunit of `A`: their residues are `0`. -/
theorem nonunits_subset_comapResidue : (A.nonunits : Set K) ⊆ A.comapResidue U := fun x hx ↦
  mem_comapResidue_iff.mpr ⟨nonunits_subset hx, by simp [residue_eq_zero_of_mem_nonunits A hx]⟩

/-- If the composite of `A` with `U` contains a field `k`, then `U` contains the residues of the
elements of `k`. -/
theorem algebraMap_residueField_mem_of_isTrivialOn {k : Type*} [CommRing k] [Algebra k K]
    [A.valuation.IsTrivialOn k] [(A.comapResidue U).valuation.IsTrivialOn k] (c : k) :
    algebraMap k (ResidueField A) c ∈ U := by
  simpa [IsScalarTower.algebraMap_apply k A (ResidueField A), ← coe_mem_comapResidue_iff]
    using (A.comapResidue U).algebraMap_mem_of_isTrivialOn c

@[simp]
theorem comapResidue_le_comapResidue_iff : A.comapResidue U ≤ A.comapResidue U' ↔ U ≤ U' := by
  refine ⟨fun h y hy ↦ ?_, fun h x hx ↦ ?_⟩
  · obtain ⟨a, rfl⟩ := residue_surjective y
    exact coe_mem_comapResidue_iff.mp (h (coe_mem_comapResidue_iff.mpr hy))
  · obtain ⟨hxA, hU⟩ := mem_comapResidue_iff.mp hx
    exact mem_comapResidue_iff.mpr ⟨hxA, h hU⟩

theorem comapResidue_injective : Function.Injective (A.comapResidue) :=
  fun _ _ h ↦ le_antisymm (comapResidue_le_comapResidue_iff.mp h.le)
    (comapResidue_le_comapResidue_iff.mp h.ge)

@[simp]
theorem comapResidue_inj : A.comapResidue U = A.comapResidue U' ↔ U = U' :=
  comapResidue_injective.eq_iff

@[simp]
theorem comapResidue_top : A.comapResidue ⊤ = A :=
  le_antisymm comapResidue_le fun x hx ↦ coe_mem_comapResidue_iff (a := ⟨x, hx⟩) |>.mpr (mem_top _)

@[simp]
theorem comapResidue_eq_self_iff : A.comapResidue U = A ↔ U = ⊤ :=
  comapResidue_injective.eq_iff' comapResidue_top

variable (A) in
/-- The image in `κ(A)` of a valuation subring `B` contained in `A`, as a valuation subring of
`κ(A)`. Its composite with `A` is `B` again (`ValuationSubring.comapResidue_mapResidue`). -/
noncomputable def mapResidue {B : ValuationSubring K} (hBA : B ≤ A) :
    ValuationSubring (ResidueField A) :=
  ofSubring ((B.toSubring.comap A.subtype).map (residue A)) fun y ↦ by
    obtain ⟨a, rfl⟩ := residue_surjective y
    simp only [Subring.mem_map, Subring.mem_comap, mem_toSubring]
    rcases B.mem_or_inv_mem (a : K) with h | h
    · exact .inl ⟨a, h, rfl⟩
    · exact .inr ⟨⟨_, hBA h⟩, h, residue_inv A a.property (hBA h)⟩

/-- The elements of the image of `B` in `κ(A)` are the residues of elements of `B`. -/
theorem mem_mapResidue_iff {B : ValuationSubring K} {hBA : B ≤ A} {y : ResidueField A} :
    y ∈ A.mapResidue hBA ↔ ∃ (b : K) (hb : b ∈ B), residue A ⟨b, hBA hb⟩ = y := by
  simp only [mapResidue, mem_ofSubring, Subring.mem_map, Subring.mem_comap, mem_toSubring]
  exact ⟨fun ⟨a, ha, hy⟩ ↦ ⟨a, ha, hy⟩, fun ⟨b, hb, hy⟩ ↦ ⟨⟨b, hBA hb⟩, hb, hy⟩⟩

/-- An element of `A` has its residue in the image of `B ⊆ A` exactly when it lies in `B`. -/
@[simp]
theorem residue_mem_mapResidue_iff {B : ValuationSubring K} {hBA : B ≤ A} {a : A} :
    residue A a ∈ A.mapResidue hBA ↔ (a : K) ∈ B := by
  refine ⟨fun h ↦ ?_, fun h ↦ mem_mapResidue_iff.mpr ⟨a, h, rfl⟩⟩
  obtain ⟨b, hb, hba⟩ := mem_mapResidue_iff.mp h
  exact A.mem_of_le_of_residue_eq hBA a.property hb hba.symm

/-- Every valuation subring `B` contained in `A` is the composite of `A` with its image in
`κ(A)`. -/
@[simp]
theorem comapResidue_mapResidue {B : ValuationSubring K} (hBA : B ≤ A) :
    A.comapResidue (A.mapResidue hBA) = B := by
  refine ext _ _ fun x ↦ ⟨fun hx ↦ ?_, fun hx ↦ ?_⟩
  · obtain ⟨hxA, hU⟩ := mem_comapResidue_iff.mp hx
    obtain ⟨b, hb, hbx⟩ := mem_mapResidue_iff.mp hU
    exact A.mem_of_le_of_residue_eq hBA hxA hb hbx.symm
  · exact mem_comapResidue_iff.mpr ⟨hBA hx, mem_mapResidue_iff.mpr ⟨x, hx, rfl⟩⟩

/-- The image in `κ(A)` of the composite of `A` with `U` is `U`. -/
@[simp]
theorem mapResidue_comapResidue (U : ValuationSubring (ResidueField A)) :
    A.mapResidue (comapResidue_le (U := U)) = U :=
  comapResidue_injective (comapResidue_mapResidue _)

/-- The image of `A` itself in `κ(A)` is all of `κ(A)`. -/
@[simp]
theorem mapResidue_self : A.mapResidue le_rfl = ⊤ :=
  comapResidue_eq_self_iff.mp (comapResidue_mapResidue _)

/-- Every valuation subring `B` contained in `A` is the composite of `A` with a valuation subring
of `κ(A)`, namely the image of `B` in `κ(A)`. -/
theorem exists_comapResidue_eq {B : ValuationSubring K} (hBA : B ≤ A) :
    ∃ U : ValuationSubring (ResidueField A), A.comapResidue U = B :=
  ⟨_, comapResidue_mapResidue hBA⟩

variable (A) in
/-- The valuation subrings of `K` contained in a valuation subring `A` correspond, preserving
order, to the valuation subrings of the residue field `κ(A)`: a valuation subring `U` of `κ(A)`
goes to the composite `A.comapResidue U`, and a valuation subring `B ⊆ A` to its image
`A.mapResidue _` in `κ(A)`. -/
noncomputable def comapResidueOrderIso : ValuationSubring (ResidueField A) ≃o Set.Iic A where
  toFun U := ⟨A.comapResidue U, comapResidue_le⟩
  invFun B := A.mapResidue B.property
  left_inv := mapResidue_comapResidue
  right_inv B := Subtype.ext (comapResidue_mapResidue B.property)
  map_rel_iff' := comapResidue_le_comapResidue_iff

@[simp]
theorem coe_comapResidueOrderIso_apply (U : ValuationSubring (ResidueField A)) :
    (comapResidueOrderIso A U : ValuationSubring K) = A.comapResidue U :=
  (rfl)

@[simp]
theorem comapResidueOrderIso_symm_apply (B : Set.Iic A) :
    (comapResidueOrderIso A).symm B = A.mapResidue B.property :=
  (rfl)

end ValuationSubring
