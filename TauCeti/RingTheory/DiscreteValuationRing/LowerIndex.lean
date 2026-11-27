/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.DiscreteValuationRing.Invariant
public import TauCeti.RingTheory.LocalRing.RamificationGroup.Basic
public import TauCeti.RingTheory.RamificationInertia.DiscreteValuationRing
public import TauCeti.RingTheory.Valuation.AddValuation
import TauCeti.RingTheory.LocalRing.FixedPoints

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
* `TauCeti.IsLocalRing.ramificationIdx_mul_lowerIndex_mk_eq_finsum` and
  `TauCeti.IsLocalRing.ramificationIdx_mul_lowerIndex_mk_eq_sum_card`: **Serre's
  quotient formula** `e · i_{G/H}(σ H) = ∑_{τ ∈ H} i_G(σ τ)` and its counting form
  `e · i_{G/H}(σ H) = ∑_{k < j} #H_k` over a general local ring `A`.

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

attribute [local instance] fixedPointsSubalgebraAlgebra isScalarTower_fixedPointsSubalgebra
  faithfulSMul_fixedPointsSubalgebra isLocalHom_algebraMap_fixedPointsSubalgebra
  FixedPoints.moduleFinite_subalgebra FixedPoints.moduleFinite_subalgebra_of_le
  isSeparable_residueField_fixedPointsSubalgebra
  isSeparable_residueField_fixedPointsSubalgebra_of_le

variable (A B G : Type*) [CommRing A] [IsLocalRing A] [CommRing B] [IsDomain B]
  [_root_.IsDiscreteValuationRing B] [Algebra A B] [IsLocalHom (algebraMap A B)] [Group G]
  [Finite G] [MulSemiringAction G B] [SMulCommClass G A B] [FaithfulSMul G B]
  [Algebra.IsSeparable (ResidueField A) (ResidueField B)]

/-- **Serre's quotient formula for the lower index**: for normal `H ≤ G`,
`e(B / B^H) · i_{G ⧸ H}(σ H) = ∑ᶠ τ : H, i_G(σ τ)`. -/
theorem ramificationIdx_mul_lowerIndex_mk_eq_finsum (H : Subgroup G) [H.Normal] (σ : G) :
    ((maximalIdeal B).ramificationIdx (FixedPoints.subalgebra A B H) : ℕ∞) *
        lowerIndex (FixedPoints.subalgebra A B H) (σ : G ⧸ H) =
      ∑ᶠ τ : H, lowerIndex B (σ * τ) := by
  obtain ⟨x, hx⟩ := IsDiscreteValuationRing.exists_adjoin_eq_top
    (R := FixedPoints.subalgebra A B G) (S := B)
  obtain ⟨y, hy⟩ := IsDiscreteValuationRing.exists_adjoin_eq_top
    (R := FixedPoints.subalgebra A B G) (S := FixedPoints.subalgebra A B H)
  exact ramificationIdx_mul_lowerIndex_eq_finsum_of_adjoin_eq_top (G := G)
    (G' := G ⧸ H) (H := H) (A := FixedPoints.subalgebra A B G)
    (C := FixedPoints.subalgebra A B H) (B := B) hx hy
    (fun c ↦ (H.coe_mk_smul σ c).symm) fun τ b ↦ (Subgroup.smul_def τ b).symm

/-- **Serre's lemma on the lower index of a quotient**, in counting form. If `σ` maximizes
`lowerIndex` in `σ H` with `i_G(σ) = j`, then
`e(B / B^H) · i_{G ⧸ H}(σ H) = ∑ k ∈ range j, #H_k`. -/
theorem ramificationIdx_mul_lowerIndex_mk_eq_sum_card (H : Subgroup G) [H.Normal]
    {σ : G} {j : ℕ} (hj : lowerIndex B σ = j)
    (hσ : ∀ τ ∈ H, lowerIndex B (σ * τ) ≤ lowerIndex B σ) :
    ((maximalIdeal B).ramificationIdx (FixedPoints.subalgebra A B H) : ℕ∞) *
        lowerIndex (FixedPoints.subalgebra A B H) (σ : G ⧸ H) =
      ∑ k ∈ Finset.range j, (Nat.card (ramificationGroup H B k) : ℕ∞) := by
  let _ := Fintype.ofFinite H
  rw [ramificationIdx_mul_lowerIndex_mk_eq_finsum A B G H σ, finsum_eq_sum_of_fintype,
    ← sum_min_lowerIndex_natCast (G := H) (S := B) j]
  refine Finset.sum_congr rfl fun τ _ ↦ ?_
  rw [lowerIndex_mul_eq_min_of_le (hσ τ τ.property), lowerIndex_coe, hj]

end

end IsLocalRing

end TauCeti
