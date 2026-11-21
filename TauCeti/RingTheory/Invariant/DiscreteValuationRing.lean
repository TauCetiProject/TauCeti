/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Invariant.Basic
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import TauCeti.RingTheory.Invariant.Basic

/-!
# Fixed-point rings of local rings and discrete valuation rings

For a monoid `G` acting on a ring `B` by ring endomorphisms, units of `B` that are invariant have
invariant inverses, so `FixedPoints.subring B G` and `FixedPoints.subalgebra A B G` are local
whenever `B` is local, with local inclusion homomorphisms. When `B` is a discrete valuation ring,
divisibility of invariant elements takes place inside `Bᴳ`, so `Bᴳ` is a principal ideal ring; if
`G` is a finite group, `B` is integral over `Bᴳ`, so `Bᴳ` is not a field and is hence a DVR.

## Main results

* `TauCeti.FixedPoints.isUnit_subring_iff`, `TauCeti.FixedPoints.isUnit_subalgebra_iff`
* `TauCeti.FixedPoints.isLocalRing_subring`, `TauCeti.FixedPoints.isLocalRing_subalgebra`
* `TauCeti.FixedPoints.dvd_subring_iff`, `TauCeti.FixedPoints.dvd_subalgebra_iff`
* `TauCeti.FixedPoints.isPrincipalIdealRing_subring`,
  `TauCeti.FixedPoints.isPrincipalIdealRing_subalgebra`
* `TauCeti.FixedPoints.isDiscreteValuationRing_subring`,
  `TauCeti.FixedPoints.isDiscreteValuationRing_subalgebra`
-/

public section

namespace TauCeti.FixedPoints

section LocalRing

section Equiv
variable (A B G : Type*) [CommSemiring A] [Ring B] [Algebra A B] [Monoid G]
  [MulSemiringAction G B] [SMulCommClass G A B]

/-- The canonical ring isomorphism between `FixedPoints.subalgebra A B G` and
`FixedPoints.subring B G`, forgetting the `A`-algebra structure. -/
def subalgebraEquivSubring : FixedPoints.subalgebra A B G ≃+* FixedPoints.subring B G where
  toFun x := ⟨x.1, x.2⟩
  invFun x := ⟨x.1, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

@[simp]
theorem coe_subalgebraEquivSubring (x : FixedPoints.subalgebra A B G) :
    (subalgebraEquivSubring A B G x : B) = x :=
  (rfl)

@[simp]
theorem coe_subalgebraEquivSubring_symm (x : FixedPoints.subring B G) :
    ((subalgebraEquivSubring A B G).symm x : B) = x :=
  (rfl)

end Equiv

section SubalgebraUnits
variable {A B G : Type*} [CommSemiring A] [Semiring B] [Algebra A B] [Monoid G]
  [MulSemiringAction G B] [SMulCommClass G A B]

/-- An element of a fixed-point subalgebra is a unit iff its image in `B` is a unit. -/
@[simp]
theorem isUnit_subalgebra_iff {x : FixedPoints.subalgebra A B G} :
    IsUnit x ↔ IsUnit (x : B) := by
  refine ⟨fun h ↦ h.map (FixedPoints.subalgebra A B G).val, fun ⟨u, hu⟩ ↦ ?_⟩
  have hinv : ((u⁻¹ : Bˣ) : B) ∈ FixedPoints.subalgebra A B G := fun g ↦ by
    calc g • ((u⁻¹ : Bˣ) : B) = ((u⁻¹ : Bˣ) : B) * ((x : B) * (g • ((u⁻¹ : Bˣ) : B))) := by
            rw [← hu, ← mul_assoc, Units.inv_mul, one_mul]
      _ = ((u⁻¹ : Bˣ) : B) * g • ((x : B) * ((u⁻¹ : Bˣ) : B)) := by rw [smul_mul', x.2 g]
      _ = ((u⁻¹ : Bˣ) : B) := by rw [← hu, Units.mul_inv, smul_one, mul_one]
  exact isUnit_iff_exists.2
    ⟨⟨((u⁻¹ : Bˣ) : B), hinv⟩, Subtype.ext (by simp [← hu]), Subtype.ext (by simp [← hu])⟩

/-- The inclusion of a fixed-point subalgebra into `B` is a local homomorphism. -/
instance isLocalHom_subalgebra_val : IsLocalHom (FixedPoints.subalgebra A B G).val where
  map_nonunit _ h := isUnit_subalgebra_iff.2 h

/-- If `A → B` is a local homomorphism, then so is `A → Bᴳ`. -/
instance isLocalHom_algebraMap_to_subalgebra [IsLocalHom (algebraMap A B)] :
    IsLocalHom (algebraMap A (FixedPoints.subalgebra A B G)) where
  map_nonunit _ h := isUnit_of_map_unit (algebraMap A B) _ (isUnit_subalgebra_iff.1 h)

/-- The fixed-point subalgebra of a local semiring is a local semiring. -/
instance isLocalRing_subalgebra [IsLocalRing B] :
    IsLocalRing (FixedPoints.subalgebra A B G) :=
  IsLocalRing.of_nonunits_add fun _ _ hx hy hxy ↦
    IsLocalRing.nonunits_add (mt isUnit_subalgebra_iff.2 hx) (mt isUnit_subalgebra_iff.2 hy)
      (isUnit_subalgebra_iff.1 hxy)

end SubalgebraUnits

/-- The inclusion of a fixed-point subalgebra as `algebraMap` is a local homomorphism. -/
instance isLocalHom_algebraMap_subalgebra {A B G : Type*} [CommSemiring A] [CommSemiring B]
    [Algebra A B] [Monoid G] [MulSemiringAction G B] [SMulCommClass G A B] :
    IsLocalHom (algebraMap (FixedPoints.subalgebra A B G) B) where
  map_nonunit _ h := isUnit_subalgebra_iff.2 h

section SubringUnits
variable {B G : Type*} [Ring B] [Monoid G] [MulSemiringAction G B]

/-- An element of a fixed-point subring is a unit iff its image in `B` is a unit. -/
@[simp]
theorem isUnit_subring_iff {x : FixedPoints.subring B G} : IsUnit x ↔ IsUnit (x : B) := by
  refine ⟨fun h ↦ h.map (FixedPoints.subring B G).subtype, fun h ↦ ?_⟩
  have h' : IsUnit ((subalgebraEquivSubring ℤ B G).symm x) := isUnit_subalgebra_iff.2 h
  simpa using h'.map (subalgebraEquivSubring ℤ B G)

/-- The inclusion of a fixed-point subring into `B` is a local homomorphism. -/
instance isLocalHom_subring_subtype : IsLocalHom (FixedPoints.subring B G).subtype where
  map_nonunit _ h := isUnit_subring_iff.2 h

/-- The fixed-point subring of a local ring is a local ring. -/
instance isLocalRing_subring [IsLocalRing B] : IsLocalRing (FixedPoints.subring B G) :=
  IsLocalRing.of_nonunits_add fun _ _ hx hy hxy ↦
    IsLocalRing.nonunits_add (mt isUnit_subring_iff.2 hx) (mt isUnit_subring_iff.2 hy)
      (isUnit_subring_iff.1 hxy)

end SubringUnits

/-- The inclusion of a fixed-point subring as `algebraMap` is a local homomorphism. -/
instance isLocalHom_algebraMap_subring {B G : Type*} [CommRing B] [Monoid G]
    [MulSemiringAction G B] : IsLocalHom (algebraMap (FixedPoints.subring B G) B) where
  map_nonunit _ h := isUnit_subring_iff.2 h

end LocalRing

section DiscreteValuationRing

/-- In an integral domain, divisibility in `Bᴳ` agrees with divisibility in `B`. -/
@[simp]
theorem dvd_subring_iff {B G : Type*} [CommRing B] [IsDomain B] [Monoid G]
    [MulSemiringAction G B] {x y : FixedPoints.subring B G} : x ∣ y ↔ (x : B) ∣ (y : B) := by
  refine ⟨map_dvd (FixedPoints.subring B G).subtype, fun ⟨b, hb⟩ ↦ ?_⟩
  rcases eq_or_ne x 0 with rfl | hx
  · exact ⟨0, Subtype.ext (by simpa using hb)⟩
  have hb' : b ∈ FixedPoints.subring B G := fun g ↦
    mul_left_cancel₀ (ZeroMemClass.coe_eq_zero.not.2 hx) <| by
      calc (x : B) * (g • b) = g • ((x : B) * b) := by rw [smul_mul', x.2 g]
        _ = (x : B) * b := by rw [← hb, y.2 g]
  exact ⟨⟨b, hb'⟩, Subtype.ext hb⟩

/-- In an integral domain, divisibility in a fixed-point subalgebra agrees with divisibility in
`B`. -/
@[simp]
theorem dvd_subalgebra_iff {A B G : Type*} [CommSemiring A] [CommRing B] [IsDomain B] [Algebra A B]
    [Monoid G] [MulSemiringAction G B] [SMulCommClass G A B] {x y : FixedPoints.subalgebra A B G} :
    x ∣ y ↔ (x : B) ∣ (y : B) := by
  simpa only [← coe_subalgebraEquivSubring A B G, ← dvd_subring_iff] using
    (map_dvd_iff (subalgebraEquivSubring A B G)).symm

/-- Every ideal of the fixed-point subring of a discrete valuation ring is principal. -/
instance isPrincipalIdealRing_subring {B G : Type*} [CommRing B] [IsDomain B]
    [IsDiscreteValuationRing B] [Monoid G] [MulSemiringAction G B] :
    IsPrincipalIdealRing (FixedPoints.subring B G) where
  principal I := by
    classical
    rcases eq_or_ne I ⊥ with rfl | hI
    · exact ⟨0, by simp⟩
    have hex : ∃ n : ℕ, ∃ x ∈ I, x ≠ 0 ∧ IsDiscreteValuationRing.addVal B (x : B) = n := by
      obtain ⟨z, hzI, hz0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
      obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 <|
        IsDiscreteValuationRing.addVal_eq_top_iff.not.2 (ZeroMemClass.coe_eq_zero.not.2 hz0)
      exact ⟨n, z, hzI, hz0, hn.symm⟩
    obtain ⟨x₀, hx₀I, _, hx₀val⟩ := Nat.find_spec hex
    refine ⟨x₀, le_antisymm (fun y hy ↦ ?_) ((Ideal.span_singleton_le_iff_mem I).2 hx₀I)⟩
    rw [Ideal.mem_span_singleton]
    rcases eq_or_ne y 0 with rfl | hy0
    · exact dvd_zero _
    obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.1 <|
      IsDiscreteValuationRing.addVal_eq_top_iff.not.2 (ZeroMemClass.coe_eq_zero.not.2 hy0)
    exact dvd_subring_iff.2 <| IsDiscreteValuationRing.addVal_le_iff_dvd.1 <| by
      rw [hx₀val, ← hk]
      exact_mod_cast Nat.find_min' hex ⟨y, hy, hy0, hk.symm⟩

/-- Every ideal of the fixed-point subalgebra of a discrete valuation ring is principal. -/
instance isPrincipalIdealRing_subalgebra {A B G : Type*} [CommSemiring A] [CommRing B]
    [IsDomain B] [IsDiscreteValuationRing B] [Algebra A B] [Monoid G] [MulSemiringAction G B]
    [SMulCommClass G A B] : IsPrincipalIdealRing (FixedPoints.subalgebra A B G) :=
  IsPrincipalIdealRing.of_surjective (subalgebraEquivSubring A B G).symm.toRingHom
    (subalgebraEquivSubring A B G).symm.surjective

/-- The fixed-point subring of a discrete valuation ring under a finite group action is a discrete
valuation ring. -/
instance isDiscreteValuationRing_subring {B G : Type*} [CommRing B] [IsDomain B]
    [IsDiscreteValuationRing B] [Group G] [Finite G] [MulSemiringAction G B] :
    IsDiscreteValuationRing (FixedPoints.subring B G) where
  not_a_field' hbot := by
    have : Algebra.IsIntegral (FixedPoints.subring B G) B :=
      Algebra.IsInvariant.isIntegral (FixedPoints.subring B G) B G
    exact IsDiscreteValuationRing.not_isField B <|
      (Algebra.IsIntegral.isField_iff_isField Subtype.val_injective).1
        (IsLocalRing.isField_iff_maximalIdeal_eq.2 hbot)

/-- The fixed-point subalgebra of a discrete valuation ring under a finite group action is a
discrete valuation ring. -/
instance isDiscreteValuationRing_subalgebra {A B G : Type*} [CommRing A] [CommRing B]
    [IsDomain B] [IsDiscreteValuationRing B] [Algebra A B] [Group G] [Finite G]
    [MulSemiringAction G B] [SMulCommClass G A B] :
    IsDiscreteValuationRing (FixedPoints.subalgebra A B G) :=
  IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing
    (subalgebraEquivSubring A B G).symm

end DiscreteValuationRing

end TauCeti.FixedPoints
