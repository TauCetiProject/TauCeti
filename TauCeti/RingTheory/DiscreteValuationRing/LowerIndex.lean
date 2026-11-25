/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.DiscreteValuationRing.Invariant
public import TauCeti.RingTheory.LocalRing.RamificationGroup
public import TauCeti.RingTheory.RamificationInertia.DiscreteValuationRing
public import TauCeti.RingTheory.Valuation.AddValuation
import TauCeti.RingTheory.IsGaloisGroup.IntegralClosure

/-!
# Serre's lower-index quotient formula on discrete valuation rings

Let a finite group `G` act faithfully on a discrete valuation ring `B` by `A`-algebra
automorphisms over a local ring `A` with separable residue extension, and let `H` be a normal
subgroup. Serre's quotient formula compares Serre's lower index `i_G(σ) = min_x v_B(σ x - x)`
(`TauCeti.IsLocalRing.lowerIndex`) on `B` and on `B^H`:

`e · i_{G/H}(σ H) = ∑_{τ ∈ H} i_G(σ τ)`,

where `e` is the ramification index of `B` over `B^H`. Neither completeness of `A` nor finiteness
of its residue field is assumed. Adapts the coset formula and its counting form from
`TauCeti/NumberTheory/LocalField/LowerIndex.lean` and
`TauCeti/NumberTheory/LocalField/Herbrand/Quotient.lean`.

## Main results

* `TauCeti.IsLocalRing.ramificationIdx_mul_lowerIndex_eq_finsum_of_adjoin_eq_top`: the quotient
  formula `e · i(σ|_C) = ∑_{τ ∈ H} i(σ τ)` for a tower of monogenic discrete valuation rings.
* `TauCeti.IsLocalRing.ramificationIdx_mul_lowerIndex_quotient_mk'_eq_finsum` and
  `TauCeti.IsLocalRing.ramificationIdx_mul_lowerIndex_quotient_mk'_eq_sum_card`: **Serre's
  quotient formula** `e · i_{G/H}(σ H) = ∑_{τ ∈ H} i_G(σ τ)` and its counting form
  `e · i_{G/H}(σ H) = ∑_{k < j} #H_k` over a general local ring `A` using `QuotientGroup.mk' H`.

## References

* [J.-P. Serre, *Corps Locaux*][serre1968], Chapter IV, §1, Proposition 3, and §3, Lemma 5.
-/

public section

open IsLocalRing

namespace TauCeti

namespace IsLocalRing

section Monogenic

variable {A C B : Type*} [CommSemiring A] [CommRing C] [IsDomain C] [IsDiscreteValuationRing C]
  [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Algebra A C] [Algebra A B] [Algebra C B]
  {G G' H : Type*} [Group G] [MulSemiringAction G B] [SMulCommClass G A B]
  [Group G'] [MulSemiringAction G' C] [SMulCommClass G' A C]
  [Group H] [Finite H] [MulSemiringAction H B] [SMulCommClass H C B]
  [FaithfulSMul H B] [Algebra.IsInvariant C B H]

/-- **Serre's quotient formula for the lower index, monogenic form.** Let `C → B` be an extension
of discrete valuation rings, generated over a common base `A` by single elements `y` and `x`, with
`C` the invariants of a finite group `H` acting faithfully on `B` over `C` and `A`. Let `σ` act on
`B` and `σ'` on `C`, compatibly with `C → B`, and let `ι τ` act on `B` as `τ` does. Then
`e · i(σ') = ∑_{τ ∈ H} i(σ ι(τ))`, where `e` is the ramification index of `B` over `C`. -/
theorem ramificationIdx_mul_lowerIndex_eq_finsum_of_adjoin_eq_top {x : B}
    (hx : Algebra.adjoin A {x} = ⊤) {y : C} (hy : Algebra.adjoin A {y} = ⊤) {σ : G} {σ' : G'}
    (hσ : ∀ c : C, σ • algebraMap C B c = algebraMap C B (σ' • c)) {ι : H → G}
    (hι : ∀ (τ : H) (b : B), ι τ • b = τ • b) :
    ((maximalIdeal B).ramificationIdx C : ℕ∞) * lowerIndex C σ' =
      ∑ᶠ τ : H, lowerIndex B (σ * ι τ) := by
  have := Fintype.ofFinite H
  have : SMulCommClass H A B := ⟨fun τ a b ↦ by rw [← hι, smul_comm, hι]⟩
  -- `B` is integral over `C`, so `C → B` is injective and local.
  have := Algebra.IsInvariant.isIntegral C B H
  have := IsDiscreteValuationRing.faithfulSMul_of_isIntegral (R := C) (S := B)
  -- `σ y - y` and `(σ f)(x) = ∏_{τ ∈ H} (x - σ τ x)` divide each other in `B`, for `f` the
  -- characteristic polynomial of `x` under `H`: the `H`-invariants are the image of `C`,
  -- generated over `A` by `y`.
  have key : _root_.IsDiscreteValuationRing.addVal B
      (σ • algebraMap C B y - algebraMap C B y) =
      _root_.IsDiscreteValuationRing.addVal B ((σ • MulSemiringAction.charpoly H x).eval x) := by
    refine (_root_.IsDiscreteValuationRing.addVal_eq_iff_associated _ _).2 <|
      associated_of_dvd_dvd (MulSemiringAction.dvd_eval_smul_charpoly (fun c hc ↦ ?_) x)
        (dvd_sub_comm.1 (MulSemiringAction.eval_smul_charpoly_dvd_sub_smul
          (smul_left_injective_of_adjoin_singleton_eq_top hx) (hx ▸ Algebra.mem_top)
          (fun τ ↦ smul_algebraMap τ y) σ))
    obtain ⟨w, rfl⟩ := Algebra.IsInvariant.isInvariant (A := C) (G := H) c hc
    rw [hσ, hσ, ← map_sub, ← map_sub]
    exact map_dvd _ (smul_sub_dvd_smul_sub_of_adjoin_singleton_eq_top hy σ' w)
  rw [finsum_eq_sum_of_fintype, lowerIndex_eq_addVal_of_adjoin_singleton_eq_top hy, ← nsmul_eq_mul,
    ← IsDiscreteValuationRing.addVal_algebraMap, map_sub, ← hσ, key,
    MulSemiringAction.eval_smul_charpoly, AddValuation.map_prod]
  refine Finset.sum_congr rfl fun τ _ ↦ ?_
  rw [lowerIndex_eq_addVal_of_adjoin_singleton_eq_top hx, AddValuation.map_sub_swap, mul_smul,
    hι]

end Monogenic

section

private theorem fixedPointsSubalgebra_le {A B G : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [Group G] [MulSemiringAction G B] [SMulCommClass G A B] (H : Subgroup G) :
    FixedPoints.subalgebra A B G ≤ FixedPoints.subalgebra A B H :=
  fun _ hx h ↦ hx h.val

@[instance_reducible]
private def instAlgebraFixedPointsSubalgebra (A B : Type*) {G : Type*} [CommRing A] [CommRing B]
    [Algebra A B] [Group G] [MulSemiringAction G B] [SMulCommClass G A B] (H : Subgroup G) :
    Algebra (FixedPoints.subalgebra A B G) (FixedPoints.subalgebra A B H) :=
  (Subalgebra.inclusion (fixedPointsSubalgebra_le H)).toAlgebra

private theorem instIsScalarTowerFixedPointsSubalgebraH (A B : Type*) {G : Type*} [CommRing A]
    [CommRing B] [Algebra A B] [Group G] [MulSemiringAction G B] [SMulCommClass G A B]
    (H : Subgroup G) :
    letI := instAlgebraFixedPointsSubalgebra A B H
    IsScalarTower (FixedPoints.subalgebra A B G) (FixedPoints.subalgebra A B H) B :=
  let _ := instAlgebraFixedPointsSubalgebra A B H
  Subalgebra.inclusion.isScalarTower_right (fixedPointsSubalgebra_le H) B

private theorem instFaithfulSMulFixedPointsSubalgebraH (A B : Type*) {G : Type*} [CommRing A]
    [CommRing B] [Algebra A B] [Group G] [MulSemiringAction G B] [SMulCommClass G A B]
    (H : Subgroup G) :
    letI := instAlgebraFixedPointsSubalgebra A B H
    FaithfulSMul (FixedPoints.subalgebra A B G) (FixedPoints.subalgebra A B H) :=
  let _ := instAlgebraFixedPointsSubalgebra A B H
  Subalgebra.inclusion.faithfulSMul (fixedPointsSubalgebra_le H)

private theorem instIsLocalHomFixedPointsSubalgebraH (A B : Type*) {G : Type*} [CommRing A]
    [CommRing B] [Algebra A B] [Group G] [MulSemiringAction G B] [SMulCommClass G A B]
    (H : Subgroup G) :
    letI := instAlgebraFixedPointsSubalgebra A B H
    IsLocalHom (algebraMap (FixedPoints.subalgebra A B G) (FixedPoints.subalgebra A B H)) := by
  let _ := instAlgebraFixedPointsSubalgebra A B H
  let _ := instIsScalarTowerFixedPointsSubalgebraH A B H
  have : IsLocalHom ((algebraMap (FixedPoints.subalgebra A B H) B).comp
      (algebraMap (FixedPoints.subalgebra A B G) (FixedPoints.subalgebra A B H))) :=
    IsScalarTower.algebraMap_eq (FixedPoints.subalgebra A B G)
      (FixedPoints.subalgebra A B H) B ▸ inferInstance
  exact isLocalHom_of_comp _ (algebraMap (FixedPoints.subalgebra A B H) B)

private theorem instModuleFiniteFixedPointsSubalgebra (A B G : Type*) [CommRing A] [CommRing B]
    [IsDomain B] [_root_.IsDiscreteValuationRing B] [Algebra A B] [Group G] [Finite G]
    [MulSemiringAction G B] [SMulCommClass G A B] [FaithfulSMul G B] :
    Module.Finite (FixedPoints.subalgebra A B G) B :=
  let _ : IsGaloisGroup G (FixedPoints.subalgebra A B G) B :=
    ⟨inferInstance, inferInstance, inferInstance⟩
  IsGaloisGroup.moduleFinite_of_isIntegrallyClosed G (FixedPoints.subalgebra A B G) B

private theorem instModuleFiniteFixedPointsSubalgebraH (A B : Type*) {G : Type*} [CommRing A]
    [CommRing B] [IsDomain B] [_root_.IsDiscreteValuationRing B] [Algebra A B] [Group G] [Finite G]
    [MulSemiringAction G B] [SMulCommClass G A B] [FaithfulSMul G B] (H : Subgroup G) :
    letI := instAlgebraFixedPointsSubalgebra A B H
    Module.Finite (FixedPoints.subalgebra A B G) (FixedPoints.subalgebra A B H) :=
  let _ := instAlgebraFixedPointsSubalgebra A B H
  let _ := instIsScalarTowerFixedPointsSubalgebraH A B H
  let _ := instModuleFiniteFixedPointsSubalgebra A B G
  Module.Finite.of_injective (IsScalarTower.toAlgHom (FixedPoints.subalgebra A B G)
    (FixedPoints.subalgebra A B H) B).toLinearMap Subtype.val_injective

private theorem instIsSeparableResidueFieldFixedPointsSubalgebra (A B G : Type*) [CommRing A]
    [IsLocalRing A] [CommRing B] [IsLocalRing B] [Algebra A B] [IsLocalHom (algebraMap A B)]
    [Group G] [MulSemiringAction G B] [SMulCommClass G A B]
    [Algebra.IsSeparable (ResidueField A) (ResidueField B)] :
    Algebra.IsSeparable (ResidueField (FixedPoints.subalgebra A B G)) (ResidueField B) :=
  Algebra.isSeparable_tower_top_of_isSeparable (ResidueField A)
    (ResidueField (FixedPoints.subalgebra A B G)) (ResidueField B)

private theorem instIsSeparableResidueFieldFixedPointsSubalgebraH (A B : Type*) {G : Type*}
    [CommRing A] [IsLocalRing A] [CommRing B] [IsLocalRing B] [Algebra A B]
    [IsLocalHom (algebraMap A B)] [Group G] [MulSemiringAction G B] [SMulCommClass G A B]
    [Algebra.IsSeparable (ResidueField A) (ResidueField B)] (H : Subgroup G) :
    letI := instAlgebraFixedPointsSubalgebra A B H
    letI := instIsLocalHomFixedPointsSubalgebraH A B H
    Algebra.IsSeparable (ResidueField (FixedPoints.subalgebra A B G))
      (ResidueField (FixedPoints.subalgebra A B H)) :=
  let _ := instAlgebraFixedPointsSubalgebra A B H
  let _ := instIsScalarTowerFixedPointsSubalgebraH A B H
  let _ := instIsLocalHomFixedPointsSubalgebraH A B H
  let _ := instIsSeparableResidueFieldFixedPointsSubalgebra A B G
  Algebra.isSeparable_tower_bot_of_isSeparable (ResidueField (FixedPoints.subalgebra A B G))
    (ResidueField (FixedPoints.subalgebra A B H)) (ResidueField B)

attribute [local instance] instAlgebraFixedPointsSubalgebra
  instIsScalarTowerFixedPointsSubalgebraH
  instFaithfulSMulFixedPointsSubalgebraH instIsLocalHomFixedPointsSubalgebraH
  instModuleFiniteFixedPointsSubalgebra instModuleFiniteFixedPointsSubalgebraH
  instIsSeparableResidueFieldFixedPointsSubalgebra instIsSeparableResidueFieldFixedPointsSubalgebraH

variable (A B G : Type*) [CommRing A] [IsLocalRing A] [CommRing B] [IsDomain B]
  [_root_.IsDiscreteValuationRing B] [Algebra A B] [IsLocalHom (algebraMap A B)] [Group G]
  [Finite G] [MulSemiringAction G B] [SMulCommClass G A B] [FaithfulSMul G B]
  [Algebra.IsSeparable (ResidueField A) (ResidueField B)]

/-- **Serre's quotient formula for the lower index**: for normal `H ≤ G`,
`e(B / B^H) · i_{G ⧸ H}(g H) = ∑ᶠ h : H, i_G(g h)`. -/
theorem ramificationIdx_mul_lowerIndex_quotient_mk'_eq_finsum (H : Subgroup G) [H.Normal] (g : G) :
    ((maximalIdeal B).ramificationIdx (FixedPoints.subalgebra A B H) : ℕ∞) *
        lowerIndex (FixedPoints.subalgebra A B H) (QuotientGroup.mk' H g) =
      ∑ᶠ h : H, lowerIndex B (g * h) := by
  obtain ⟨x, hx⟩ := IsDiscreteValuationRing.exists_adjoin_eq_top
    (R := FixedPoints.subalgebra A B G) (S := B)
  obtain ⟨y, hy⟩ := IsDiscreteValuationRing.exists_adjoin_eq_top
    (R := FixedPoints.subalgebra A B G) (S := FixedPoints.subalgebra A B H)
  exact ramificationIdx_mul_lowerIndex_eq_finsum_of_adjoin_eq_top (G := G)
    (G' := G ⧸ H) (H := H) (A := FixedPoints.subalgebra A B G)
    (C := FixedPoints.subalgebra A B H) (B := B) hx hy
    (fun c ↦ (H.coe_mk_smul g c).symm) fun τ b ↦ (Subgroup.smul_def τ b).symm

/-- If `g` maximizes `lowerIndex` in `g H` with `i_G(g) = j`, then
`e(B / B^H) · i_{G ⧸ H}(g H) = ∑ k ∈ range j, #H_k`. -/
theorem ramificationIdx_mul_lowerIndex_quotient_mk'_eq_sum_card (H : Subgroup G) [H.Normal]
    (g : G) {j : ℕ} (hj : lowerIndex B g = j)
    (hg : ∀ h : H, lowerIndex B (g * h) ≤ lowerIndex B g) :
    ((maximalIdeal B).ramificationIdx (FixedPoints.subalgebra A B H) : ℕ∞) *
        lowerIndex (FixedPoints.subalgebra A B H) (QuotientGroup.mk' H g) =
      ∑ k ∈ Finset.range j, (Nat.card (ramificationGroup H B k) : ℕ∞) := by
  let _ := Fintype.ofFinite H
  rw [ramificationIdx_mul_lowerIndex_quotient_mk'_eq_finsum A B G H g, finsum_eq_sum_of_fintype,
    ← sum_min_lowerIndex_natCast (G := H) (S := B) j]
  refine Finset.sum_congr rfl fun h _ ↦ ?_
  rw [lowerIndex_mul_eq_min_of_le (hg h), lowerIndex_coe, hj]

end

section

variable (A B G : Type*) [CommRing A] [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
  [Algebra A B] [Group G] [MulSemiringAction G B] [SMulCommClass G A B] [FaithfulSMul G B]
  (H : Subgroup G) [H.Normal] [Finite H] (g : G)

/-- For a faithful action of `G` on a DVR `B` over `A` and a finite normal subgroup `H ≤ G`,
`i_{G ⧸ H}(g H) = ⊤` if and only if `g ∈ H`. -/
theorem lowerIndex_quotient_mk'_eq_top_iff :
    lowerIndex (FixedPoints.subalgebra A B H) (QuotientGroup.mk' H g) = ⊤ ↔ g ∈ H := by
  rw [lowerIndex_eq_top_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]

/-- If `g` maximizes `lowerIndex` in `g H` and `lowerIndex B g ≠ ⊤`, then
`lowerIndex B^H (QuotientGroup.mk' H g) ≠ ⊤`. -/
theorem lowerIndex_quotient_mk'_ne_top (hj : lowerIndex B g ≠ ⊤)
    (hg : ∀ h : H, lowerIndex B (g * h) ≤ lowerIndex B g) :
    lowerIndex (FixedPoints.subalgebra A B H) (QuotientGroup.mk' H g) ≠ ⊤ :=
  lowerIndex_ne_top_of_forall_mem_ker_le hj fun h hh ↦
    hg ⟨h, by simpa [QuotientGroup.ker_mk'] using hh⟩

end

end IsLocalRing

end TauCeti
