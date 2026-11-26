/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.DiscreteValuationRing.Herbrand.Quotient
public import TauCeti.RingTheory.LocalRing.Herbrand.Tower

/-!
# Tower transitivity and upper-numbering Herbrand's theorem for DVRs

Combining Herbrand's lower-numbering theorem in
`TauCeti.RingTheory.DiscreteValuationRing.Herbrand.Quotient` with the abstract local-ring tower
propagation in `TauCeti.RingTheory.LocalRing.Herbrand.Tower`, this file proves — for any finite
group `G` acting on a discrete valuation ring `B` over a local ring `A` with normal subgroup
`H ⊴ G` and separable residue extension `𝓀(B) / 𝓀(A)`, without completeness, residue finiteness,
faithfulness, or `A = B^G`:

* **Tower transitivity**: `φ_G = φ_{G ⧸ H} ∘ φ_H`, `ψ_G = ψ_H ∘ ψ_{G ⧸ H}`, and
  `ψℕ_G = ψℕ_H ∘ ψℕ_{G ⧸ H}`.
* **Herbrand's theorem in the upper numbering**: `(G ⧸ H)^v = G^v H / H` for all `v : ℝ`.
* **Upper numbering of a normal subgroup**: `H ∩ G^v = H^{ψ_{G ⧸ H}(v)}` for all `v : ℝ`.
* **Upper breaks in a tower**: `v` is an upper break of `G` iff it is an upper break of `G ⧸ H`
  or `ψ_{G ⧸ H}(v)` is an upper break of `H`.

## Main results

* `TauCeti.IsLocalRing.herbrandFun_tower`, `TauCeti.IsLocalRing.inverseHerbrandFun_tower`,
  `TauCeti.IsLocalRing.psiNat_tower`: tower transitivity on `FixedPoints.subalgebra A B H`.
* `TauCeti.IsLocalRing.upperRamificationGroup_quotient_eq_map`,
  `TauCeti.IsLocalRing.subgroupOf_upperRamificationGroup_quotient`,
  `TauCeti.IsLocalRing.upperJump_iff_upperJump_quotient_or`: upper numbering and upper breaks on
  `FixedPoints.subalgebra A B H` (plus `FixedPoints.subring` and Galois field corollaries).

## References

* [J.-P. Serre, *Corps Locaux*][serre1968], Chapter IV, §3, Propositions 14 and 15.
* J.-P. Serre, *Sur les corps locaux à corps résiduel algébriquement clos*, Bull. Soc. Math.
  France **89** (1961), 105–154, n° 3.1, Propositions 3 and 4.
-/

public section
noncomputable section

namespace TauCeti.IsLocalRing

/-! ### Tower and upper-numbering theorems for `FixedPoints.subalgebra A B H` -/

section Subalgebra

variable (A B : Type*) [CommRing A] [_root_.IsLocalRing A]
  [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Algebra A B]
  [IsLocalHom (algebraMap A B)]
  [Algebra.IsSeparable (_root_.IsLocalRing.ResidueField A) (_root_.IsLocalRing.ResidueField B)]
  (G : Type*) [Group G] [Finite G] [MulSemiringAction G B] [SMulCommClass G A B]
  (H : Subgroup G) [H.Normal]

/-- **Counting form of Herbrand's lemma** for `FixedPoints.subalgebra A B H`:
`#(G ⧸ H)_{φ_H(u)} · #H_u = #G_u` for every `u : ℝ`. -/
theorem natCard_ramificationGroupReal_quotient_mul (u : ℝ) :
    Nat.card (ramificationGroupReal (G ⧸ H) (FixedPoints.subalgebra A B H) (herbrandFun H B u)) *
        Nat.card (ramificationGroupReal H B u) =
      Nat.card (ramificationGroupReal G B u) :=
  natCard_ramificationGroupReal_herbrandFun_mul_of_map_eq (QuotientGroup.mk' H) H.subtype
    Subtype.val_injective (fun _ _ ↦ rfl)
    ((Subgroup.range_subtype H).trans (QuotientGroup.ker_mk' H).symm)
    (ramificationGroupReal_quotient_herbrandFun_eq_map A B G H u).symm

/-- **Tower transitivity of the Herbrand function** for `FixedPoints.subalgebra A B H`:
`φ_G(u) = φ_{G ⧸ H}(φ_H(u))` for every `u : ℝ`. -/
theorem herbrandFun_tower (u : ℝ) :
    herbrandFun G B u =
      herbrandFun (G ⧸ H) (FixedPoints.subalgebra A B H) (herbrandFun H B u) :=
  herbrandFun_eq_comp_of_map_ramificationGroupReal_eq (QuotientGroup.mk' H) H.subtype
    Subtype.val_injective (fun _ _ ↦ rfl)
    ((Subgroup.range_subtype H).trans (QuotientGroup.ker_mk' H).symm)
    (fun w _ ↦ (ramificationGroupReal_quotient_herbrandFun_eq_map A B G H w).symm) u

/-- **Tower transitivity of the inverse Herbrand function** for `FixedPoints.subalgebra A B H`:
`ψ_G(v) = ψ_H(ψ_{G ⧸ H}(v))` for every `v : ℝ`. -/
theorem inverseHerbrandFun_tower (v : ℝ) :
    inverseHerbrandFun G B v =
      inverseHerbrandFun H B (inverseHerbrandFun (G ⧸ H) (FixedPoints.subalgebra A B H) v) :=
  inverseHerbrandFun_eq_comp_of_map_ramificationGroupReal_eq (QuotientGroup.mk' H) H.subtype
    Subtype.val_injective (fun _ _ ↦ rfl)
    ((Subgroup.range_subtype H).trans (QuotientGroup.ker_mk' H).symm)
    (fun w _ ↦ (ramificationGroupReal_quotient_herbrandFun_eq_map A B G H w).symm) v

/-- **Tower transitivity of `psiNat`** for `FixedPoints.subalgebra A B H`:
`ψℕ_G(n) = ψℕ_H(ψℕ_{G ⧸ H}(n))`. -/
theorem psiNat_tower (n : ℕ) :
    psiNat G B n = psiNat H B (psiNat (G ⧸ H) (FixedPoints.subalgebra A B H) n) :=
  psiNat_eq_comp_of_map_ramificationGroupReal_eq (QuotientGroup.mk' H) H.subtype
    Subtype.val_injective (fun _ _ ↦ rfl)
    ((Subgroup.range_subtype H).trans (QuotientGroup.ker_mk' H).symm)
    (fun w _ ↦ (ramificationGroupReal_quotient_herbrandFun_eq_map A B G H w).symm) n

/-- **Herbrand's theorem in the upper numbering** for `FixedPoints.subalgebra A B H`:
`(G ⧸ H)^v = G^v H / H` for every `v : ℝ`. -/
theorem upperRamificationGroup_quotient_eq_map (v : ℝ) :
    upperRamificationGroup (G ⧸ H) (FixedPoints.subalgebra A B H) v =
      (upperRamificationGroup G B v).map (QuotientGroup.mk' H) :=
  (map_upperRamificationGroup_of_map_ramificationGroupReal_eq (QuotientGroup.mk' H) H.subtype
    Subtype.val_injective (fun _ _ ↦ rfl)
    ((Subgroup.range_subtype H).trans (QuotientGroup.ker_mk' H).symm)
    (fun w _ ↦ (ramificationGroupReal_quotient_herbrandFun_eq_map A B G H w).symm) v).symm

/-- **Upper numbering of a normal subgroup** for `FixedPoints.subalgebra A B H`:
`H ∩ G^v = H^{ψ_{G ⧸ H}(v)}` for every `v : ℝ`. -/
theorem subgroupOf_upperRamificationGroup_quotient (v : ℝ) :
    (upperRamificationGroup G B v).subgroupOf H =
      upperRamificationGroup H B (inverseHerbrandFun (G ⧸ H) (FixedPoints.subalgebra A B H) v) :=
  comap_upperRamificationGroup_of_map_ramificationGroupReal_eq (QuotientGroup.mk' H) H.subtype
    Subtype.val_injective (fun _ _ ↦ rfl)
    ((Subgroup.range_subtype H).trans (QuotientGroup.ker_mk' H).symm)
    (fun w _ ↦ (ramificationGroupReal_quotient_herbrandFun_eq_map A B G H w).symm) v

/-- **Upper breaks in a quotient** for `FixedPoints.subalgebra A B H`: `v` is an upper break of
`G` iff it is an upper break of `G ⧸ H` or `ψ_{G ⧸ H}(v)` is an upper break of `H`. -/
theorem upperJump_iff_upperJump_quotient_or (v : ℝ) :
    UpperJump G B v ↔
      UpperJump (G ⧸ H) (FixedPoints.subalgebra A B H) v ∨
        UpperJump H B (inverseHerbrandFun (G ⧸ H) (FixedPoints.subalgebra A B H) v) :=
  upperJump_iff_or_of_map_ramificationGroupReal_eq (QuotientGroup.mk' H) H.subtype
    Subtype.val_injective (fun _ _ ↦ rfl)
    ((Subgroup.range_subtype H).trans (QuotientGroup.ker_mk' H).symm)
    (fun w _ ↦ (ramificationGroupReal_quotient_herbrandFun_eq_map A B G H w).symm) v

end Subalgebra

/-! ### Base-free corollaries for `FixedPoints.subring B H` -/

section Subring

variable (B G : Type*) [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
  [Group G] [Finite G] [MulSemiringAction G B]
  (H : Subgroup G) [H.Normal]
  [Algebra.IsSeparable (_root_.IsLocalRing.ResidueField (FixedPoints.subring B G))
    (_root_.IsLocalRing.ResidueField B)]

/-- **Counting form of Herbrand's lemma** for `B^H`: `#(G ⧸ H)_{φ_H(u)} · #H_u = #G_u`. -/
theorem natCard_ramificationGroupReal_quotient_subring_mul (u : ℝ) :
    Nat.card (ramificationGroupReal (G ⧸ H) (FixedPoints.subring B H) (herbrandFun H B u)) *
        Nat.card (ramificationGroupReal H B u) =
      Nat.card (ramificationGroupReal G B u) :=
  natCard_ramificationGroupReal_herbrandFun_mul_of_map_eq (QuotientGroup.mk' H) H.subtype
    Subtype.val_injective (fun _ _ ↦ rfl)
    ((Subgroup.range_subtype H).trans (QuotientGroup.ker_mk' H).symm)
    (ramificationGroupReal_quotient_subring_herbrandFun_eq_map B G H u).symm

/-- **Tower transitivity of the Herbrand function** for `B^H`:
`φ_G(u) = φ_{G ⧸ H}(φ_H(u))` for every `u : ℝ`. -/
theorem herbrandFun_tower_subring (u : ℝ) :
    herbrandFun G B u =
      herbrandFun (G ⧸ H) (FixedPoints.subring B H) (herbrandFun H B u) :=
  herbrandFun_eq_comp_of_map_ramificationGroupReal_eq (QuotientGroup.mk' H) H.subtype
    Subtype.val_injective (fun _ _ ↦ rfl)
    ((Subgroup.range_subtype H).trans (QuotientGroup.ker_mk' H).symm)
    (fun w _ ↦ (ramificationGroupReal_quotient_subring_herbrandFun_eq_map B G H w).symm) u

/-- **Tower transitivity of the inverse Herbrand function** for `B^H`:
`ψ_G(v) = ψ_H(ψ_{G ⧸ H}(v))` for every `v : ℝ`. -/
theorem inverseHerbrandFun_tower_subring (v : ℝ) :
    inverseHerbrandFun G B v =
      inverseHerbrandFun H B (inverseHerbrandFun (G ⧸ H) (FixedPoints.subring B H) v) :=
  inverseHerbrandFun_eq_comp_of_map_ramificationGroupReal_eq (QuotientGroup.mk' H) H.subtype
    Subtype.val_injective (fun _ _ ↦ rfl)
    ((Subgroup.range_subtype H).trans (QuotientGroup.ker_mk' H).symm)
    (fun w _ ↦ (ramificationGroupReal_quotient_subring_herbrandFun_eq_map B G H w).symm) v

/-- **Tower transitivity of `psiNat`** for `B^H`: `ψℕ_G(n) = ψℕ_H(ψℕ_{G ⧸ H}(n))`. -/
theorem psiNat_tower_subring (n : ℕ) :
    psiNat G B n = psiNat H B (psiNat (G ⧸ H) (FixedPoints.subring B H) n) :=
  psiNat_eq_comp_of_map_ramificationGroupReal_eq (QuotientGroup.mk' H) H.subtype
    Subtype.val_injective (fun _ _ ↦ rfl)
    ((Subgroup.range_subtype H).trans (QuotientGroup.ker_mk' H).symm)
    (fun w _ ↦ (ramificationGroupReal_quotient_subring_herbrandFun_eq_map B G H w).symm) n

/-- **Herbrand's theorem in the upper numbering** for `B^H`:
`(G ⧸ H)^v = G^v H / H` for every `v : ℝ`. -/
theorem upperRamificationGroup_quotient_subring_eq_map (v : ℝ) :
    upperRamificationGroup (G ⧸ H) (FixedPoints.subring B H) v =
      (upperRamificationGroup G B v).map (QuotientGroup.mk' H) :=
  (map_upperRamificationGroup_of_map_ramificationGroupReal_eq (QuotientGroup.mk' H) H.subtype
    Subtype.val_injective (fun _ _ ↦ rfl)
    ((Subgroup.range_subtype H).trans (QuotientGroup.ker_mk' H).symm)
    (fun w _ ↦ (ramificationGroupReal_quotient_subring_herbrandFun_eq_map B G H w).symm) v).symm

/-- **Upper numbering of a normal subgroup** for `B^H`:
`H ∩ G^v = H^{ψ_{G ⧸ H}(v)}` for every `v : ℝ`. -/
theorem subgroupOf_upperRamificationGroup_subring (v : ℝ) :
    (upperRamificationGroup G B v).subgroupOf H =
      upperRamificationGroup H B (inverseHerbrandFun (G ⧸ H) (FixedPoints.subring B H) v) :=
  comap_upperRamificationGroup_of_map_ramificationGroupReal_eq (QuotientGroup.mk' H) H.subtype
    Subtype.val_injective (fun _ _ ↦ rfl)
    ((Subgroup.range_subtype H).trans (QuotientGroup.ker_mk' H).symm)
    (fun w _ ↦ (ramificationGroupReal_quotient_subring_herbrandFun_eq_map B G H w).symm) v

/-- **Upper breaks in a quotient** for `B^H`. -/
theorem upperJump_iff_upperJump_quotient_subring_or (v : ℝ) :
    UpperJump G B v ↔
      UpperJump (G ⧸ H) (FixedPoints.subring B H) v ∨
        UpperJump H B (inverseHerbrandFun (G ⧸ H) (FixedPoints.subring B H) v) :=
  upperJump_iff_or_of_map_ramificationGroupReal_eq (QuotientGroup.mk' H) H.subtype
    Subtype.val_injective (fun _ _ ↦ rfl)
    ((Subgroup.range_subtype H).trans (QuotientGroup.ker_mk' H).symm)
    (fun w _ ↦ (ramificationGroupReal_quotient_subring_herbrandFun_eq_map B G H w).symm) v

end Subring

/-! ### Field / integral-closure form -/

section GaloisField

variable (A K L : Type*) [CommRing A] [Field K] [Field L]
  [Algebra A K] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
  [_root_.IsLocalRing A] [FiniteDimensional K L] [IsGalois K L]
  [IsDiscreteValuationRing (integralClosure A L)] [IsLocalHom (algebraMap A (integralClosure A L))]
  [Algebra.IsSeparable (_root_.IsLocalRing.ResidueField A)
    (_root_.IsLocalRing.ResidueField (integralClosure A L))]
  (H : Subgroup (L ≃ₐ[K] L)) [H.Normal]

/-- **Herbrand's theorem in field form** via `IsGalois.normalAutEquivQuotient`:
`IsGalois.normalAutEquivQuotient H` maps `G^v H / H` onto `Gal(L^H / K)^v` for every `v : ℝ`. -/
theorem upperRamificationGroup_fixedField_eq_map_normalAutEquivQuotient (v : ℝ) :
    ((upperRamificationGroup (L ≃ₐ[K] L) (integralClosure A L) v).map (QuotientGroup.mk' H)).map
        (IsGalois.normalAutEquivQuotient H).toMonoidHom =
      upperRamificationGroup
        (IntermediateField.fixedField H ≃ₐ[K] IntermediateField.fixedField H)
        (integralClosure A (IntermediateField.fixedField H)) v := by
  rw [← upperRamificationGroup_quotient_eq_map A (integralClosure A L) (L ≃ₐ[K] L) H v]
  exact upperRamificationGroup_map_of_ringEquiv (IsGalois.normalAutEquivQuotient H)
    ((TauCeti.FixedPoints.subalgebraEquivSubring A (integralClosure A L) H).trans
      (TauCeti.fixedPointsIntegralClosureEquivFixedField A K L H))
    (fun q x ↦ by
      simp only [RingEquiv.trans_apply, TauCeti.FixedPoints.subalgebraEquivSubring_smul]
      exact TauCeti.fixedPointsIntegralClosureEquivFixedField_smul A K L H q _)
    v

/-- **Herbrand's theorem in field form** via `AlgEquiv.restrictNormalHom`: restriction from `L` to
`L^H` maps `Gal(L / K)^v` onto `Gal(L^H / K)^v` for every `v : ℝ`. -/
theorem map_restrictNormalHom_upperRamificationGroup_fixedField (v : ℝ) :
    (upperRamificationGroup (L ≃ₐ[K] L) (integralClosure A L) v).map
        (AlgEquiv.restrictNormalHom (IntermediateField.fixedField H)) =
      upperRamificationGroup
        (IntermediateField.fixedField H ≃ₐ[K] IntermediateField.fixedField H)
        (integralClosure A (IntermediateField.fixedField H)) v := by
  have hcomp : (IsGalois.normalAutEquivQuotient H).toMonoidHom.comp (QuotientGroup.mk' H) =
      AlgEquiv.restrictNormalHom (IntermediateField.fixedField H) :=
    MonoidHom.ext (IsGalois.normalAutEquivQuotient_apply H)
  rw [← hcomp, ← Subgroup.map_map]
  exact upperRamificationGroup_fixedField_eq_map_normalAutEquivQuotient A K L H v

end GaloisField

end TauCeti.IsLocalRing
