/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.DiscreteValuationRing.Herbrand.Quotient
import TauCeti.RingTheory.Invariant.Galois

/-!
# Tower transitivity and upper-numbering Herbrand's theorem for DVRs

Building on the lower-numbering Herbrand's lemma in
`TauCeti.RingTheory.DiscreteValuationRing.Herbrand.Quotient`, this file proves — for any finite
group `G` acting on a discrete valuation ring `B` with normal subgroup `H ⊴ G` and separable
residue extension `𝓀(B) / 𝓀(B^G)`, without completeness, residue finiteness, or faithfulness:

* **Tower transitivity**: `φ_G = φ_{G ⧸ H} ∘ φ_H`, `ψ_G = ψ_H ∘ ψ_{G ⧸ H}`, and
  `ψℕ_G = ψℕ_H ∘ ψℕ_{G ⧸ H}`.
* **Herbrand's theorem in the upper numbering**: `(G ⧸ H)^v = G^v H / H` for all `v : ℝ`.
* **Upper numbering of a normal subgroup**: `H ∩ G^v = H^{ψ_{G ⧸ H}(v)}` for all `v : ℝ`.

Each result is proved in base-free form for `FixedPoints.subring B H`, transferred to
`FixedPoints.subalgebra A B H` over any invariant local ring `A`, and stated in field form for
`integralClosure A L` and `IntermediateField.fixedField H` via `IsGalois.normalAutEquivQuotient`
and `AlgEquiv.restrictNormalHom`.

## References

* [J.-P. Serre, *Local Fields*][serre1979], Chapter IV, §3, Propositions 14 and 15.
* J.-P. Serre, *Sur les corps locaux à corps résiduel algébriquement clos*, Bull. Soc. Math.
  France **89** (1961), 105–154, n° 3.1, Propositions 3 and 4.
* Adapts `TauCeti/NumberTheory/LocalField/Herbrand/{Tower,UpperQuotient}.lean` to arbitrary DVRs.
-/

public section
noncomputable section

namespace TauCeti.IsLocalRing

section SubringTower

variable (B G : Type*) [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
  [Group G] [Finite G] [MulSemiringAction G B]
  (H : Subgroup G) [H.Normal]
  [Algebra.IsSeparable (_root_.IsLocalRing.ResidueField (FixedPoints.subring B G))
    (_root_.IsLocalRing.ResidueField B)]

/-- Inertia cardinality is multiplicative in a quotient: `#(G ⧸ H)_0 · #H_0 = #G_0`. -/
private theorem natCard_ramificationGroup_zero_quotient_mul :
    (Nat.card (ramificationGroup (G ⧸ H) (FixedPoints.subring B H) 0) : ℝ) *
        Nat.card (ramificationGroup H B 0) =
      Nat.card (ramificationGroup G B 0) := by
  have h0 := natCard_ramificationGroupReal_quotient_subring_mul B G H 0
  rw [herbrandFun_zero, ← Int.cast_zero, ramificationGroupReal_intCast,
    ramificationGroupReal_intCast, ramificationGroupReal_intCast] at h0
  exact_mod_cast h0

/-- If `G_t` is constant on `(a, b]`, then `(G ⧸ H)_t` is constant on `(φ_H(a), φ_H(b)]`. -/
private theorem ramificationGroupReal_quotient_eq_of_forall_eq {a b t : ℝ}
    (ht₁ : herbrandFun H B a < t) (ht₂ : t ≤ herbrandFun H B b)
    (hG : ∀ s : ℝ, a < s → s ≤ b → ramificationGroupReal G B s = ramificationGroupReal G B b) :
    ramificationGroupReal (G ⧸ H) (FixedPoints.subring B H) t =
      ramificationGroupReal (G ⧸ H) (FixedPoints.subring B H) (herbrandFun H B b) := by
  have hs₁ : a < inverseHerbrandFun H B t := by
    simpa only [inverseHerbrandFun_herbrandFun] using inverseHerbrandFun_strictMono H B ht₁
  have hs₂ : inverseHerbrandFun H B t ≤ b := by
    simpa only [inverseHerbrandFun_herbrandFun] using
      (inverseHerbrandFun_strictMono H B).monotone ht₂
  rw [← herbrandFun_inverseHerbrandFun H B t,
    ramificationGroupReal_quotient_subring_herbrandFun_eq_map,
    ramificationGroupReal_quotient_subring_herbrandFun_eq_map, hG _ hs₁ hs₂]

/-- Propagating `φ_G = φ_{G/H} ∘ φ_H` across an integer interval `[m, m + 1]`. -/
private theorem herbrandFun_tower_of_mem_Icc_of_eq (m : ℕ) {u : ℝ} (h₁ : (m : ℝ) ≤ u)
    (h₂ : u ≤ m + 1)
    (hm : herbrandFun G B m =
      herbrandFun (G ⧸ H) (FixedPoints.subring B H) (herbrandFun H B m)) :
    herbrandFun G B u = herbrandFun (G ⧸ H) (FixedPoints.subring B H) (herbrandFun H B u) := by
  have hG : ∀ t : ℝ, (m : ℝ) < t → t ≤ u →
      ramificationGroupReal G B t = ramificationGroupReal G B u := fun _ _ _ ↦ by
    rw [ramificationGroupReal_eq_of_sub_one_lt_of_le G B (i := (m + 1 : ℕ))
        (by push_cast; linarith) (by push_cast; linarith),
      ramificationGroupReal_eq_of_sub_one_lt_of_le G B (i := (m + 1 : ℕ))
        (by push_cast; linarith) (by push_cast; linarith)]
  have hH : ∀ t : ℝ, (m : ℝ) < t → t ≤ u →
      ramificationGroupReal H B t = ramificationGroupReal H B u := fun _ _ _ ↦ by
    rw [ramificationGroupReal_eq_of_sub_one_lt_of_le H B (i := (m + 1 : ℕ))
        (by push_cast; linarith) (by push_cast; linarith),
      ramificationGroupReal_eq_of_sub_one_lt_of_le H B (i := (m + 1 : ℕ))
        (by push_cast; linarith) (by push_cast; linarith)]
  have hGdiff := herbrandFun_sub_of_forall_eq G B h₁ hG
  have hHdiff := herbrandFun_sub_of_forall_eq H B h₁ hH
  have hQdiff := herbrandFun_sub_of_forall_eq (G ⧸ H) (FixedPoints.subring B H)
    ((herbrandFun_strictMono H B).monotone h₁) fun _ ht₁ ht₂ ↦
      ramificationGroupReal_quotient_eq_of_forall_eq B G H ht₁ ht₂ hG
  have hcard :
      (Nat.card (ramificationGroupReal (G ⧸ H) (FixedPoints.subring B H) (herbrandFun H B u)) : ℝ) *
        Nat.card (ramificationGroupReal H B u) = Nat.card (ramificationGroupReal G B u) := by
    exact_mod_cast natCard_ramificationGroupReal_quotient_subring_mul B G H u
  have hslope : (Nat.card (ramificationGroupReal G B u) : ℝ) / Nat.card (ramificationGroup G B 0) =
      (Nat.card (ramificationGroupReal H B u) / Nat.card (ramificationGroup H B 0)) *
        (Nat.card (ramificationGroupReal (G ⧸ H) (FixedPoints.subring B H) (herbrandFun H B u)) /
          Nat.card (ramificationGroup (G ⧸ H) (FixedPoints.subring B H) 0)) := by
    rw [div_mul_div_comm, ← hcard, ← natCard_ramificationGroup_zero_quotient_mul B G H,
      mul_comm (Nat.card (ramificationGroupReal H B u) : ℝ),
      mul_comm (Nat.card (ramificationGroup H B 0) : ℝ)]
  rw [hslope] at hGdiff
  rw [hHdiff] at hQdiff
  linear_combination hGdiff - hQdiff + hm

/-- Tower transitivity of the Herbrand function for `u ≤ -1`. -/
private theorem herbrandFun_tower_of_le_neg_one {u : ℝ} (hu1 : u ≤ -1) :
    herbrandFun G B u =
      herbrandFun (G ⧸ H) (FixedPoints.subring B H) (herbrandFun H B u) := by
  have hφH : herbrandFun H B u ≤ -1 := by
    rw [← herbrandFun_neg_one H B]
    exact (herbrandFun_strictMono H B).monotone hu1
  rw [herbrandFun_of_le_neg_one G B hu1, herbrandFun_of_le_neg_one (G ⧸ H) _ hφH,
    herbrandFun_of_le_neg_one H B hu1]
  have hcardG : (Nat.card (G ⧸ H) : ℝ) * Nat.card H = Nat.card G := by
    exact_mod_cast (by rw [← Subgroup.index_eq_card, mul_comm, Subgroup.card_mul_index] :
      Nat.card (G ⧸ H) * Nat.card H = Nat.card G)
  have hratio : (Nat.card G : ℝ) / Nat.card (ramificationGroup G B 0) =
      ((Nat.card H : ℝ) / Nat.card (ramificationGroup H B 0)) *
        ((Nat.card (G ⧸ H) : ℝ) /
          Nat.card (ramificationGroup (G ⧸ H) (FixedPoints.subring B H) 0)) := by
    rw [div_mul_div_comm, ← hcardG, ← natCard_ramificationGroup_zero_quotient_mul B G H,
      mul_comm (Nat.card H : ℝ), mul_comm (Nat.card (ramificationGroup H B 0) : ℝ)]
  rw [hratio]
  ring

/-- **Tower transitivity of the Herbrand function** for `B^H`:
`φ_G(u) = φ_{G ⧸ H}(φ_H(u))` for every `u : ℝ`. -/
theorem herbrandFun_tower_subring (u : ℝ) :
    herbrandFun G B u =
      herbrandFun (G ⧸ H) (FixedPoints.subring B H) (herbrandFun H B u) := by
  rcases le_or_gt u (-1) with hu1 | hu1
  · exact herbrandFun_tower_of_le_neg_one B G H hu1
  · rcases le_or_gt u 0 with hu0 | hu0
    · rw [herbrandFun_of_neg_one_le_of_le_zero H B hu1.le hu0,
        herbrandFun_of_neg_one_le_of_le_zero (G ⧸ H) _ hu1.le hu0,
        herbrandFun_of_neg_one_le_of_le_zero G B hu1.le hu0]
    · have hind : ∀ m : ℕ, ∀ x : ℝ, (m : ℝ) ≤ x → x ≤ m + 1 →
          herbrandFun G B x =
            herbrandFun (G ⧸ H) (FixedPoints.subring B H) (herbrandFun H B x) := by
        intro m
        induction m with
        | zero => exact fun _ hx₁ hx₂ ↦ herbrandFun_tower_of_mem_Icc_of_eq B G H 0 hx₁ hx₂ (by simp)
        | succ k ih =>
          exact fun _ hx₁ hx₂ ↦ herbrandFun_tower_of_mem_Icc_of_eq B G H (k + 1) hx₁ hx₂
            (ih _ (by push_cast; linarith) (by push_cast; linarith))
      exact hind ⌊u⌋₊ u (Nat.floor_le hu0.le) (Nat.lt_floor_add_one u).le

/-- **Tower transitivity of the inverse Herbrand function** for `B^H`:
`ψ_G(v) = ψ_H(ψ_{G ⧸ H}(v))` for every `v : ℝ`. -/
theorem inverseHerbrandFun_tower_subring (v : ℝ) :
    inverseHerbrandFun G B v =
      inverseHerbrandFun H B (inverseHerbrandFun (G ⧸ H) (FixedPoints.subring B H) v) := by
  apply (herbrandFun_strictMono G B).injective
  rw [herbrandFun_inverseHerbrandFun, herbrandFun_tower_subring B G H,
    herbrandFun_inverseHerbrandFun, herbrandFun_inverseHerbrandFun]

/-- **Tower transitivity of the integral inverse Herbrand function** for `B^H`:
`ψℕ_G(n) = ψℕ_H(ψℕ_{G ⧸ H}(n))`. -/
theorem psiNat_tower_subring (n : ℕ) :
    psiNat G B n = psiNat H B (psiNat (G ⧸ H) (FixedPoints.subring B H) n) := by
  apply Nat.cast_injective (R := ℝ)
  rw [coe_psiNat, coe_psiNat, coe_psiNat, inverseHerbrandFun_tower_subring B G H]

/-- **Herbrand's theorem in the upper numbering** for `B^H`:
`(G ⧸ H)^v = G^v H / H` for every `v : ℝ`. -/
theorem upperRamificationGroup_quotient_subring_eq_map (v : ℝ) :
    upperRamificationGroup (G ⧸ H) (FixedPoints.subring B H) v =
      (upperRamificationGroup G B v).map (QuotientGroup.mk' H) := by
  rw [upperRamificationGroup_def, upperRamificationGroup_def,
    inverseHerbrandFun_tower_subring B G H v,
    ← ramificationGroupReal_quotient_subring_herbrandFun_eq_map B G H,
    herbrandFun_inverseHerbrandFun]

/-- **Upper numbering of a normal subgroup** for `B^H`:
`H ∩ G^v = H^{ψ_{G ⧸ H}(v)}` for every `v : ℝ`. -/
theorem subgroupOf_upperRamificationGroup_subring (v : ℝ) :
    (upperRamificationGroup G B v).subgroupOf H =
      upperRamificationGroup H B (inverseHerbrandFun (G ⧸ H) (FixedPoints.subring B H) v) := by
  rw [upperRamificationGroup_def, subgroupOf_ramificationGroupReal, upperRamificationGroup_def,
    inverseHerbrandFun_tower_subring B G H v]

end SubringTower

section Subalgebra

/-- `FixedPoints.subalgebraEquivSubring` is equivariant for the quotient `G ⧸ H`-action. -/
private theorem subalgebraEquivSubring_smul (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]
    (G : Type*) [Group G] [MulSemiringAction G B] [SMulCommClass G A B] (H : Subgroup G)
    [H.Normal] (q : G ⧸ H) (x : FixedPoints.subalgebra A B H) :
    TauCeti.FixedPoints.subalgebraEquivSubring A B H (q • x) =
      MulEquiv.refl (G ⧸ H) q • TauCeti.FixedPoints.subalgebraEquivSubring A B H x :=
  QuotientGroup.induction_on q fun g ↦ Subtype.ext <| by
    change (TauCeti.FixedPoints.subalgebraEquivSubring A B H
        ((QuotientGroup.mk g : G ⧸ H) • x) : B) =
      g • (TauCeti.FixedPoints.subalgebraEquivSubring A B H x : B)
    simp; rfl

variable (A B : Type*) [CommRing A] [_root_.IsLocalRing A]
  [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Algebra A B]
  [IsLocalHom (algebraMap A B)]
  [Algebra.IsSeparable (_root_.IsLocalRing.ResidueField A) (_root_.IsLocalRing.ResidueField B)]
  (G : Type*) [Group G] [Finite G] [MulSemiringAction G B] [SMulCommClass G A B]
  [Algebra.IsInvariant A B G] (H : Subgroup G) [H.Normal]

/-- **Herbrand's lemma in the lower numbering** for `FixedPoints.subalgebra A B H`:
`(G ⧸ H)_{φ_H(u)} = G_u H / H` for every `u : ℝ`. -/
theorem ramificationGroupReal_quotient_herbrandFun_eq_map (u : ℝ) :
    ramificationGroupReal (G ⧸ H) (FixedPoints.subalgebra A B H) (herbrandFun H B u) =
      (ramificationGroupReal G B u).map (QuotientGroup.mk' H) := by
  have := isSeparable_residueField_subring_of_isInvariant A B G
  rw [← ramificationGroupReal_quotient_subring_herbrandFun_eq_map B G H u]
  simpa using ramificationGroupReal_map_of_ringEquiv (MulEquiv.refl (G ⧸ H))
    (TauCeti.FixedPoints.subalgebraEquivSubring A B H)
    (subalgebraEquivSubring_smul A B G H) (herbrandFun H B u)

/-- **Tower transitivity of the Herbrand function** for `FixedPoints.subalgebra A B H`. -/
theorem herbrandFun_tower (u : ℝ) :
    herbrandFun G B u =
      herbrandFun (G ⧸ H) (FixedPoints.subalgebra A B H) (herbrandFun H B u) := by
  have := isSeparable_residueField_subring_of_isInvariant A B G
  rw [herbrandFun_eq_of_ringEquiv (MulEquiv.refl (G ⧸ H))
    (TauCeti.FixedPoints.subalgebraEquivSubring A B H) (subalgebraEquivSubring_smul A B G H)]
  exact herbrandFun_tower_subring B G H u

/-- **Tower transitivity of the inverse Herbrand function** for `FixedPoints.subalgebra A B H`. -/
theorem inverseHerbrandFun_tower (v : ℝ) :
    inverseHerbrandFun G B v =
      inverseHerbrandFun H B (inverseHerbrandFun (G ⧸ H) (FixedPoints.subalgebra A B H) v) := by
  have := isSeparable_residueField_subring_of_isInvariant A B G
  rw [inverseHerbrandFun_eq_of_ringEquiv (MulEquiv.refl (G ⧸ H))
    (TauCeti.FixedPoints.subalgebraEquivSubring A B H) (subalgebraEquivSubring_smul A B G H)]
  exact inverseHerbrandFun_tower_subring B G H v

/-- **Tower transitivity of the integral inverse Herbrand function** for
`FixedPoints.subalgebra A B H`. -/
theorem psiNat_tower (n : ℕ) :
    psiNat G B n = psiNat H B (psiNat (G ⧸ H) (FixedPoints.subalgebra A B H) n) := by
  apply Nat.cast_injective (R := ℝ)
  rw [coe_psiNat, coe_psiNat, coe_psiNat, inverseHerbrandFun_tower A B G H]

/-- **Herbrand's theorem in the upper numbering** for `FixedPoints.subalgebra A B H`:
`(G ⧸ H)^v = G^v H / H` for every `v : ℝ`. -/
theorem upperRamificationGroup_quotient_eq_map (v : ℝ) :
    upperRamificationGroup (G ⧸ H) (FixedPoints.subalgebra A B H) v =
      (upperRamificationGroup G B v).map (QuotientGroup.mk' H) := by
  have := isSeparable_residueField_subring_of_isInvariant A B G
  rw [← upperRamificationGroup_quotient_subring_eq_map B G H v]
  simpa using upperRamificationGroup_map_of_ringEquiv (MulEquiv.refl (G ⧸ H))
    (TauCeti.FixedPoints.subalgebraEquivSubring A B H) (subalgebraEquivSubring_smul A B G H) v

/-- **Upper numbering of a normal subgroup** for `FixedPoints.subalgebra A B H`:
`H ∩ G^v = H^{ψ_{G ⧸ H}(v)}` for every `v : ℝ`. -/
theorem subgroupOf_upperRamificationGroup_quotient (v : ℝ) :
    (upperRamificationGroup G B v).subgroupOf H =
      upperRamificationGroup H B (inverseHerbrandFun (G ⧸ H) (FixedPoints.subalgebra A B H) v) := by
  rw [upperRamificationGroup_def, subgroupOf_ramificationGroupReal, upperRamificationGroup_def,
    inverseHerbrandFun_tower A B G H v]

end Subalgebra

section FieldForm

variable (A K L : Type*) [CommRing A] [Field K] [Field L]
  [Algebra A K] [Algebra K L] [Algebra A L] [IsScalarTower A K L]

/-- The canonical ring isomorphism identifying the `H`-fixed points of `integralClosure A L` with
`integralClosure A (IntermediateField.fixedField H)`. -/
def fixedPointsIntegralClosureEquivFixedField (H : Subgroup (L ≃ₐ[K] L)) :
    FixedPoints.subring (integralClosure A L) H ≃+*
      integralClosure A (IntermediateField.fixedField H) where
  toFun x :=
    ⟨⟨x.1.1, fun σ ↦ congrArg Subtype.val (x.2 σ)⟩,
      (isIntegral_algHom_iff ((IntermediateField.fixedField H).val.restrictScalars A)
        Subtype.val_injective).1 x.1.2⟩
  invFun y :=
    ⟨⟨y.1.1, (isIntegral_algHom_iff ((IntermediateField.fixedField H).val.restrictScalars A)
        Subtype.val_injective).2 y.2⟩,
      fun σ ↦ Subtype.ext (y.1.2 σ)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

/-- If `integralClosure A L` is a DVR and `H ≤ Gal(L/K)` is finite, then
`integralClosure A (IntermediateField.fixedField H)` is also a DVR. -/
instance isDiscreteValuationRing_integralClosure_fixedField
    [IsDiscreteValuationRing (integralClosure A L)] (H : Subgroup (L ≃ₐ[K] L)) [Finite H] :
    IsDiscreteValuationRing (integralClosure A (IntermediateField.fixedField H)) :=
  IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing
    (fixedPointsIntegralClosureEquivFixedField A K L H)

/-- Equivariance of `fixedPointsIntegralClosureEquivFixedField` along
`IsGalois.normalAutEquivQuotient`. -/
private theorem fixedPointsIntegralClosureEquivFixedField_smul
    [FiniteDimensional K L] [IsGalois K L] (H : Subgroup (L ≃ₐ[K] L)) [H.Normal]
    (q : (L ≃ₐ[K] L) ⧸ H) (x : FixedPoints.subring (integralClosure A L) H) :
    fixedPointsIntegralClosureEquivFixedField A K L H (q • x) =
      IsGalois.normalAutEquivQuotient H q •
        fixedPointsIntegralClosureEquivFixedField A K L H x := by
  refine QuotientGroup.induction_on q fun σ ↦ ?_
  ext
  simp only [fixedPointsIntegralClosureEquivFixedField, RingEquiv.coe_mk, Equiv.coe_fn_mk,
    integralClosure.coe_smul, IsGalois.normalAutEquivQuotient_apply]
  exact (AlgEquiv.restrictNormal_commutes σ (IntermediateField.fixedField H)
    ⟨x.1.1, fun τ ↦ congrArg Subtype.val (x.2 τ)⟩).symm

/-- If `A` is integrally closed in `K` and `L / K` is Galois, then `A → integralClosure A L` is
an invariant extension for `Gal(L/K)`. -/
private theorem isInvariant_integralClosure_of_isIntegrallyClosedIn [IsGalois K L]
    [IsIntegrallyClosedIn A K] :
    Algebra.IsInvariant A (integralClosure A L) (L ≃ₐ[K] L) where
  isInvariant x hx := by
    obtain ⟨a, ha⟩ := (TauCeti.InfiniteGalois.mem_range_algebraMap_iff_isIntegral_and_fixed K
      x.1).2 ⟨x.2, fun τ ↦ congrArg Subtype.val (hx τ)⟩
    exact ⟨a, Subtype.ext ha⟩

section GaloisField
variable [_root_.IsLocalRing A] [IsIntegrallyClosedIn A K] [FiniteDimensional K L] [IsGalois K L]
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
  have := isInvariant_integralClosure_of_isIntegrallyClosedIn A K L
  have := isSeparable_residueField_subring_of_isInvariant A (integralClosure A L) (L ≃ₐ[K] L)
  rw [← upperRamificationGroup_quotient_subring_eq_map (integralClosure A L) (L ≃ₐ[K] L) H v]
  exact upperRamificationGroup_map_of_ringEquiv (IsGalois.normalAutEquivQuotient H)
    (fixedPointsIntegralClosureEquivFixedField A K L H)
    (fixedPointsIntegralClosureEquivFixedField_smul A K L H) v

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

end FieldForm

end TauCeti.IsLocalRing
