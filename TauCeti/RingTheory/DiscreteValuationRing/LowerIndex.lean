/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.DiscreteValuationRing.Invariant
import TauCeti.NumberTheory.RamificationInertia.SeparableDegree
import TauCeti.RingTheory.IsGaloisGroup.IntegralClosure
import TauCeti.RingTheory.LocalRing.RingHom
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
(`Subgroup.faithfulSMul_quotient_subalgebra`). This file proves Serre's formula
comparing Serre's lower index `i_G(σ) = min_x v_B(σ x - x)` (`TauCeti.IsLocalRing.lowerIndex`) on
`B` and on `B^H`: when the residue extension of `B` over `A` is separable,

`e · i_{G/H}(σ H) = ∑_{τ ∈ H} i_G(σ τ)`,

where `e` is the ramification index of `B` over `B^H` (and `e = #H_0` by
`TauCeti.IsLocalRing.natCard_ramificationGroup_zero_eq_ramificationIdx`). Neither completeness of
`A` nor finiteness of its residue field is assumed. Separability enters only through generators:
`B` and `B^H` are then generated over `A` by single elements `x` and `y`, at which the lower
indices are read, and `σ y - y` is associated in `B` with `(σ f)(x) = ∏_{τ ∈ H} (x - σ τ x)` for
the characteristic polynomial `f` of `x` under `H`. Without separability the formula fails.

The formula is the input to Herbrand's theorem `(G/H)_{φ(u)} = G_u H / H`, which relates the
lower numbering of `G ⧸ H` to that of `G` through the Herbrand function `φ` of `H`, and hence to
the compatibility of the upper numbering with quotients. The counting form records Serre's
lemma: if `σ` has the largest lower index `j` in its coset `σ H`, then
`i_G(σ τ) = min (i_H(τ), j)` for `τ ∈ H`, and so `e · i_{G/H}(σ H) = ∑_{k < j} #H_k`. The
nonarchimedean local field case is
`TauCeti.LocalFieldsRamification.ramificationIndex_mul_lowerIndex_restrictNormal_eq_sum`.

The comparison of `σ y - y` with `(σ f)(x)` uses only the generators, so it is first proved for
any tower of discrete valuation rings `C → B` generated over `A` by single elements, with `C` the
ring of invariants of a finite group `H` acting faithfully on `B` and `σ` acting compatibly on
`B` and `C`. This monogenic form also gives the nonarchimedean local field case.

## Main results

* `TauCeti.IsLocalRing.ramificationIdx_mul_lowerIndex_eq_finsum_of_adjoin_eq_top`: the quotient
  formula `e · i(σ|_C) = ∑_{τ ∈ H} i(σ τ)` for a tower of monogenic discrete valuation rings.
* `TauCeti.IsLocalRing.ramificationIdx_mul_lowerIndex_mk_eq_finsum`: **Serre's quotient formula**
  `e · i_{G/H}(σ H) = ∑_{τ ∈ H} i_G(σ τ)`.
* `TauCeti.IsLocalRing.ramificationIdx_mul_lowerIndex_mk_eq_sum_card`: its counting form
  `e · i_{G/H}(σ H) = ∑_{k < j} #H_k` for `σ` of largest lower index `j` in `σ H`.
* `TauCeti.IsLocalRing.natCard_ramificationGroup_zero_mul_lowerIndex_mk_eq_sum`,
  `TauCeti.IsLocalRing.natCard_ramificationGroup_zero_mul_lowerIndex_mk_eq_sum_card`,
  `TauCeti.IsLocalRing.lowerIndex_mk_ne_top`: the same formulas with `#H_0` in place of `e`, and
  finiteness of `i_{G/H}(σ H)` when `σ` maximizes a finite `i_G(σ)` in `σ H`.

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

end IsLocalRing

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
  have := Algebra.IsInvariant.isIntegral A B G
  have := IsDiscreteValuationRing.faithfulSMul_of_isIntegral (R := A) (S := B)
  have : IsGaloisGroup G A B := ⟨inferInstance, inferInstance, inferInstance⟩
  have := IsGaloisGroup.moduleFinite_of_isIntegrallyClosed G A B
  obtain ⟨x, hx⟩ := IsDiscreteValuationRing.exists_adjoin_eq_top (R := A) (S := B)
  obtain ⟨y, hy⟩ := FixedPoints.exists_adjoin_eq_top A B H
  exact ramificationIdx_mul_lowerIndex_eq_finsum_of_adjoin_eq_top hx hy
    (fun c ↦ (H.coe_mk_smul σ c).symm) fun τ b ↦ (Subgroup.smul_def τ b).symm

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
  rw [lowerIndex_mul_eq_min_of_le (hσ τ τ.property), lowerIndex_coe, hj]

variable (A B G) in
/-- **Serre's quotient formula for the lower index** under a separable residue extension:
`#H_0 · i_{G/H}(σ H) = ∑_{τ ∈ H} i_G(σ τ)` in `ℕ∞`. -/
theorem natCard_ramificationGroup_zero_mul_lowerIndex_mk_eq_sum [IsLocalHom (algebraMap A B)]
    [Algebra.IsSeparable (ResidueField A) (ResidueField B)] [Fintype H] (σ : G) :
    (Nat.card (ramificationGroup H B 0) : ℕ∞) *
        lowerIndex (FixedPoints.subalgebra A B H) (σ : G ⧸ H) =
      ∑ τ : H, lowerIndex B (σ * (τ : G)) := by
  set C := FixedPoints.subalgebra A B H
  have : Algebra.IsSeparable (ResidueField C) (ResidueField B) :=
    Algebra.isSeparable_tower_top_of_isSeparable (ResidueField A) (ResidueField C) (ResidueField B)
  rw [natCard_ramificationGroup_zero_eq_ramificationIdx C B H, ← finsum_eq_sum_of_fintype]
  exact ramificationIdx_mul_lowerIndex_mk_eq_finsum A B H σ

variable (A B G) in
/-- **Serre's lemma** in counting form: if `σ` maximizes `lowerIndex B` in its coset `σ H` and
`i_G(σ) = j` is finite, then `#H_0 · i_{G/H}(σ H) = ∑_{k < j} #H_k`. -/
theorem natCard_ramificationGroup_zero_mul_lowerIndex_mk_eq_sum_card [IsLocalHom (algebraMap A B)]
    [Algebra.IsSeparable (ResidueField A) (ResidueField B)] (σ : G) {j : ℕ}
    (hj : lowerIndex B σ = j)
    (hσ : ∀ τ : H, lowerIndex B (σ * (τ : G)) ≤ lowerIndex B σ) :
    (Nat.card (ramificationGroup H B 0) : ℕ∞) *
        lowerIndex (FixedPoints.subalgebra A B H) (σ : G ⧸ H) =
      ∑ k ∈ Finset.range j, (Nat.card (ramificationGroup H B k) : ℕ∞) := by
  set C := FixedPoints.subalgebra A B H
  have : Algebra.IsSeparable (ResidueField C) (ResidueField B) :=
    Algebra.isSeparable_tower_top_of_isSeparable (ResidueField A) (ResidueField C) (ResidueField B)
  rw [natCard_ramificationGroup_zero_eq_ramificationIdx C B H]
  exact ramificationIdx_mul_lowerIndex_mk_eq_sum_card A H hj fun τ hτ ↦ hσ ⟨τ, hτ⟩

variable (A B G) in
/-- If `σ` maximizes `lowerIndex B` in its coset `σ H` and `i_G(σ) ≠ ⊤`, then `i_{G/H}(σ H) ≠ ⊤`. -/
theorem lowerIndex_mk_ne_top [IsLocalHom (algebraMap A B)]
    [Algebra.IsSeparable (ResidueField A) (ResidueField B)] (σ : G) (hj : lowerIndex B σ ≠ ⊤)
    (hσ : ∀ τ ∈ H, lowerIndex B (σ * τ) ≤ lowerIndex B σ) :
    lowerIndex (FixedPoints.subalgebra A B H) (σ : G ⧸ H) ≠ ⊤ := by
  obtain ⟨j, hj⟩ := ENat.ne_top_iff_exists.1 hj
  intro htop
  have hsum := natCard_ramificationGroup_zero_mul_lowerIndex_mk_eq_sum_card A B G H σ hj.symm
    fun τ ↦ hσ τ τ.property
  have h0 : (Nat.card (ramificationGroup H B 0) : ℕ∞) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := ramificationGroup H B 0)).ne'
  rw [htop, ENat.mul_top h0, ← Nat.cast_sum] at hsum
  exact ENat.natCast_ne_top _ hsum.symm

end IsLocalRing

end TauCeti
