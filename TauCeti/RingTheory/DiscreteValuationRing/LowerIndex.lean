/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.DiscreteValuationRing.Invariant
public import TauCeti.RingTheory.IsGaloisGroup.IntegralClosure
public import TauCeti.RingTheory.LocalRing.RamificationGroup
public import TauCeti.RingTheory.RamificationInertia.DiscreteValuationRing
public import TauCeti.RingTheory.Valuation.AddValuation

/-!
# The lower index of a quotient, over discrete valuation rings

Let a finite group `G` act faithfully on a discrete valuation ring `B` by `A`-algebra
automorphisms, with invariants the discrete valuation ring `A`, and let `H` be a normal subgroup.
Mathlib makes `G ⧸ H` act on the fixed ring `B^H = FixedPoints.subalgebra A B H`, with invariants
`A`; this is the integer ring of the fixed field `L^H` of a finite Galois extension `L/K`, with
`Gal(L^H/K) = G ⧸ H`. The ring `B^H` is again a discrete valuation ring
(`TauCeti.FixedPoints.isDiscreteValuationRing_subalgebra`), on which `G ⧸ H` acts faithfully
(`TauCeti.FixedPoints.faithfulSMul_quotient_subalgebra`). This file proves Serre's formula
comparing Serre's lower index `i_G(σ) = min_x v_B(σ x - x)` (`TauCeti.IsLocalRing.lowerIndex`) on
`B` and on `B^H`: when the residue extension of `B` over `A` is separable,

`e · i_{G/H}(σ H) = ∑_{τ ∈ H} i_G(σ τ)`,

where `e` is the ramification index of `B` over `B^H`. Neither completeness of `A` nor finiteness
of its residue field is assumed. Separability enters only through generators: `B` and `B^H` are
then generated over `A` by single elements `x` and `y`, at which the lower indices are read, and
`σ y - y` is associated in `B` with `(σ f)(x) = ∏_{τ ∈ H} (x - σ τ x)` for the characteristic
polynomial `f` of `x` under `H`. Without separability the formula fails.

The formula is the input to Herbrand's theorem `(G/H)_{φ(u)} = G_u H / H`, which relates the
lower numbering of `G ⧸ H` to that of `G` through the Herbrand function `φ` of `H`, and hence to
the compatibility of the upper numbering with quotients. The counting form records Serre's
lemma: if `σ` has the largest lower index `j` in its coset `σ H`, then
`i_G(σ τ) = min (i_H(τ), j)` for `τ ∈ H`, and so `e · i_{G/H}(σ H) = ∑_{k < j} #H_k`. The
nonarchimedean local field case is
`TauCeti.LocalFieldsRamification.ramificationIndex_mul_lowerIndex_restrictNormal_eq_sum`.

## Main results

* `TauCeti.IsLocalRing.ramificationIdx_mul_lowerIndex_mk_eq_finsum`: **Serre's quotient formula**
  `e · i_{G/H}(σ H) = ∑_{τ ∈ H} i_G(σ τ)`.
* `TauCeti.IsLocalRing.ramificationIdx_mul_lowerIndex_mk_eq_sum_card`: its counting form
  `e · i_{G/H}(σ H) = ∑_{k < j} #H_k` for `σ` of largest lower index `j` in `σ H`.

## References

* [J.-P. Serre, *Corps Locaux*][serre1968], Chapter IV, §1, Proposition 3, and §3, Lemma 5.
-/

public section

open IsLocalRing

namespace TauCeti

variable {A B : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Algebra A B]
  {G : Type*} [Group G] [Finite G] [MulSemiringAction G B] [SMulCommClass G A B]
  [Algebra.IsInvariant A B G] [FaithfulSMul G B]
  (H : Subgroup G) [H.Normal]

namespace IsLocalRing

variable (A B) in
/-- **Serre's quotient formula for the lower index.** Let a finite group `G` act faithfully on the
discrete valuation ring `B` by `A`-algebra automorphisms, with invariants the discrete valuation
ring `A` and separable residue extension, and let `H` be a normal subgroup. Then for every
`σ : G`, `e · i_{G/H}(σ H) = ∑_{τ ∈ H} i_G(σ τ)`, where `e` is the ramification index of `B` over
the invariants `B^H` and `i_{G/H}` is the lower index of the action of `G ⧸ H` on `B^H`. Both
sides are `⊤` for `σ ∈ H`. -/
theorem ramificationIdx_mul_lowerIndex_mk_eq_finsum [IsLocalHom (algebraMap A B)]
    [Algebra.IsSeparable (ResidueField A) (ResidueField B)] (σ : G) :
    ((maximalIdeal B).ramificationIdx (FixedPoints.subalgebra A B H) : ℕ∞) *
        lowerIndex (FixedPoints.subalgebra A B H) (σ : G ⧸ H) =
      ∑ᶠ τ : H, lowerIndex B (σ * τ) := by
  have := Fintype.ofFinite H
  -- The kernel of `A → B` is a prime ideal strictly below the contraction of `maximalIdeal B`.
  have : FaithfulSMul A B := by
    have := Algebra.IsInvariant.isIntegral A B G
    rw [faithfulSMul_iff_algebraMap_injective, RingHom.injective_iff_ker_eq_bot,
      RingHom.ker_eq_comap_bot]
    exact Ring.DimensionLEOne.eq_bot_of_lt _ _ <| Ideal.IsIntegral.under_lt_under (R := A) <|
      bot_lt_iff_ne_bot.2 (IsDiscreteValuationRing.not_a_field B)
  have : IsGaloisGroup G A B := ⟨inferInstance, inferInstance, inferInstance⟩
  have := IsGaloisGroup.moduleFinite_of_isIntegrallyClosed G A B
  obtain ⟨x, hx⟩ := IsDiscreteValuationRing.exists_adjoin_eq_top (R := A) (S := B)
  obtain ⟨y, hy⟩ := FixedPoints.exists_adjoin_eq_top A B H
  have hinj : Function.Injective fun τ : H ↦ τ • x :=
    (smul_left_injective_of_adjoin_singleton_eq_top (G := G) hx).comp Subtype.val_injective
  -- `σ y - y` and `(σ f)(x) = ∏_{τ ∈ H} (x - σ τ x)` divide each other in `B`, for `f` the
  -- characteristic polynomial of `x` under `H`: the `H`-invariants are the elements of `B^H`,
  -- generated over `A` by `y`.
  have key : _root_.IsDiscreteValuationRing.addVal B (σ • (y : B) - y) =
      _root_.IsDiscreteValuationRing.addVal B
        ((σ • MulSemiringAction.charpoly H x).eval x) := by
    refine (_root_.IsDiscreteValuationRing.addVal_eq_iff_associated _ _).2 <|
      associated_of_dvd_dvd
        (MulSemiringAction.smul_sub_dvd_eval_smul_charpoly (fun c hc ↦ ?_) x)
        (dvd_sub_comm.1 (MulSemiringAction.eval_smul_charpoly_dvd_sub_smul hx hinj
          (fun τ ↦ y.2 τ) σ))
    simpa using map_dvd (algebraMap (FixedPoints.subalgebra A B H) B)
      (smul_sub_dvd_smul_sub_of_adjoin_singleton_eq_top hy (σ : G ⧸ H) ⟨c, hc⟩)
  rw [finsum_eq_sum_of_fintype, lowerIndex_eq_addVal_of_adjoin_singleton_eq_top hy,
    ← nsmul_eq_mul, ← IsDiscreteValuationRing.addVal_algebraMap, map_sub]
  simp_rw [lowerIndex_eq_addVal_of_adjoin_singleton_eq_top hx, AddValuation.map_sub_swap _ _ x,
    ← AddValuation.map_prod, mul_smul]
  rw [MulSemiringAction.eval_smul_charpoly] at key
  simpa only [Subalgebra.algebraMap_apply, FixedPoints.coe_mk_smul, Subgroup.smul_def] using key

variable (A) in
/-- **Serre's lemma on the lower index of a quotient**, in counting form. Let a finite group `G`
act faithfully on the discrete valuation ring `B` by `A`-algebra automorphisms, with invariants the
discrete valuation ring `A` and separable residue extension, and let `H` be a normal subgroup. If
`σ` has the largest lower index in its coset `σ H`, and `i_G(σ) = j` is finite, then
`e · i_{G/H}(σ H) = ∑_{k < j} #H_k`, where `H_k` are the ramification groups of `H` acting on `B`
and `e` is the ramification index of `B` over `B^H`. -/
theorem ramificationIdx_mul_lowerIndex_mk_eq_sum_card [IsLocalHom (algebraMap A B)]
    [Algebra.IsSeparable (ResidueField A) (ResidueField B)] {σ : G} {j : ℕ}
    (hj : lowerIndex B σ = j) (hσ : ∀ τ ∈ H, lowerIndex B (σ * τ) ≤ lowerIndex B σ) :
    ((maximalIdeal B).ramificationIdx (FixedPoints.subalgebra A B H) : ℕ∞) *
        lowerIndex (FixedPoints.subalgebra A B H) (σ : G ⧸ H) =
      ∑ k ∈ Finset.range j, (Nat.card (ramificationGroup H B k) : ℕ∞) := by
  have := Fintype.ofFinite H
  rw [ramificationIdx_mul_lowerIndex_mk_eq_finsum A B, finsum_eq_sum_of_fintype,
    ← sum_min_lowerIndex_natCast (G := H) (S := B) j]
  refine Finset.sum_congr rfl fun τ _ ↦ ?_
  rw [lowerIndex_mul_eq_min_of_le (hσ τ τ.2), lowerIndex_coe, hj]

end IsLocalRing

end TauCeti
