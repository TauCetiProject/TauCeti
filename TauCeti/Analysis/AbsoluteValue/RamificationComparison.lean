/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.AbsoluteValue.Inertia
public import TauCeti.Analysis.AbsoluteValue.Place
public import TauCeti.Analysis.AbsoluteValue.ValuationSubring
public import TauCeti.RingTheory.Valuation.LocalizationAtCenter
public import TauCeti.RingTheory.Valuation.RamificationGroup

/-!
# Decomposition and inertia groups of places, valuation subrings and primes

Let a group `G` act on a field `L` by ring automorphisms. For a finite place `w` of `L` (a
`ℚ`-normalised nonarchimedean absolute value, `AbsoluteValue.Place L`), the decomposition group
of `w` is `MulAction.stabilizer G w` and its inertia group is `AbsoluteValue.inertia G w`
(`TauCeti/Analysis/AbsoluteValue/Inertia.lean`). This file compares them with the two other
descriptions of the same groups:

* **Valuation subrings.** The stabiliser of `w` is the stabiliser of its valuation subring
  `A_w = {x | w x ≤ 1}` (`AbsoluteValue.Place.stabilizer_valuationSubring`). For `G = L ≃ₐ[K] L`
  this is Mathlib's `ValuationSubring.decompositionSubgroup`, and the inertia group of `w` is the
  image of Mathlib's `ValuationSubring.inertiaSubgroup` under the inclusion of the decomposition
  subgroup into `L ≃ₐ[K] L` (`AbsoluteValue.Place.inertia_eq_map_inertiaSubgroup`). An element of
  the decomposition group satisfies `w (σ • x - x ^ q) < 1` whenever `w x ≤ 1` exactly when it acts
  on the residue field of `A_w` by `y ↦ y ^ q`
  (`AbsoluteValue.Place.mem_stabilizer_and_forall_iff_residue`).
* **Primes.** Let `B` be a ring with fraction field `L` on which `G` acts compatibly, and let the
  valuation subring `A_w` be centred at a prime `P` of `B` (`ValuationSubring.IsCenteredAt`), that
  is, `w ≤ 1` on `B` and `P = {b ∈ B | w b < 1}`. When the localization `B_P` is a valuation ring
  (for instance when `B` is a Prüfer domain), the stabiliser of `w` is the stabiliser of `P`
  (`AbsoluteValue.Place.stabilizer_eq_stabilizer_of_isCenteredAt`) and the inertia group of `w` is
  Mathlib's `Ideal.inertia` of `P` (`AbsoluteValue.Place.inertia_eq_inertia_of_isCenteredAt`).

The comparison of stabilisers needs `w` to be a place, not just an absolute value: an
automorphism can preserve `A_w` and move `w` to an equivalent absolute value. For places this
cannot happen, as equivalent places are equal (`AbsoluteValue.Place.eq_of_isEquiv`). The
residue-field form of the power-map congruences
(`AbsoluteValue.forall_residue_smul_eq_pow_iff`) holds for every nonarchimedean real absolute
value.

The specialisation to the absolute Galois group of a number field acting on its algebraic
integers, with Tau Ceti's `TauCeti.GaloisRep.decompositionGroup` and `inertiaGroup`, is in
`TauCeti/NumberTheory/NumberField/AbsoluteGaloisGroup/PlaceComparison.lean`; the infinite places
are compared with Mathlib's stabiliser lemmas in
`TauCeti/NumberTheory/NumberField/PlacesOver/InfinitePlace/Comparison.lean`.

## Main results

* `AbsoluteValue.Place.stabilizer_valuationSubring`: the stabiliser of a finite place is the
  stabiliser of its valuation subring.
* `AbsoluteValue.Place.stabilizer_eq_decompositionSubgroup`,
  `AbsoluteValue.Place.inertia_eq_map_inertiaSubgroup`: the decomposition and inertia groups in
  `L ≃ₐ[K] L` are Mathlib's decomposition and inertia subgroups of `A_w`.
* `AbsoluteValue.forall_residue_smul_eq_pow_iff`,
  `AbsoluteValue.Place.mem_stabilizer_and_forall_iff_residue`: the congruences
  `w (σ • x - x ^ q) < 1` as the action `y ↦ y ^ q` on the residue field of `A_w`.
* `AbsoluteValue.Place.stabilizer_eq_stabilizer_of_isCenteredAt`,
  `AbsoluteValue.Place.inertia_eq_inertia_of_isCenteredAt`: decomposition and inertia groups of
  `w` and of its centre `P`.

## Acknowledgments

The design (decomposition and inertia groups defined once for finite and infinite places through
absolute values, and compared with the valuation-subring and prime-ideal vocabularies) follows the
advice of Thomas Browning and Jz Pan on the Lean Zulip,
https://leanprover.zulipchat.com/#narrow/channel/658556-Riemann-Hypothesis/topic/Library.20design.20discrepancies.20between.20RH.2FMathlib.2FTauCeti/near/643780662
and
https://leanprover.zulipchat.com/#narrow/channel/658556-Riemann-Hypothesis/topic/Library.20design.20discrepancies.20between.20RH.2FMathlib.2FTauCeti/near/643806146.

## References

* J. Neukirch, *Algebraic Number Theory*, Springer, 1999, Ch. I, §9 and Ch. II, §9.
-/

public section

open IsLocalRing

open scoped Pointwise

namespace AbsoluteValue

variable {G L : Type*} [Group G] [Field L] [MulSemiringAction G L] {w : AbsoluteValue L ℝ}

/-! ### Valuation subrings -/

section Galois

variable {K : Type*} [Field K] [Algebra K L]

/-- **Residue action and congruences.** An element `σ` of the decomposition subgroup of the
valuation subring `A_w` of a nonarchimedean `w` acts on the residue field of `A_w` by `y ↦ y ^ q`
exactly when `w (σ • x - x ^ q) < 1` for every `x` with `w x ≤ 1`. -/
theorem forall_residue_smul_eq_pow_iff (hw : IsNonarchimedean w) {σ : L ≃ₐ[K] L}
    (hσ : σ ∈ (w.valuationSubring hw).decompositionSubgroup K) {q : ℕ} :
    (∀ y : ResidueField (w.valuationSubring hw),
        (⟨σ, hσ⟩ : (w.valuationSubring hw).decompositionSubgroup K) • y = y ^ q) ↔
      ∀ x, w x ≤ 1 → w (σ • x - x ^ q) < 1 := by
  simp only [residue_surjective.forall, Subtype.forall, ← ResidueField.residue_smul,
    ValuationSubring.residue_smul_eq_pow_iff, mem_valuationSubring_iff,
    mem_nonunits_valuationSubring_iff]

end Galois

/-! ### Places -/

namespace Place

variable [CharZero L]

/-- **The stabiliser of a finite place is the stabiliser of its valuation subring.** An element
of `G` fixes a finite place `w` exactly when it maps the valuation subring `A_w` to itself. -/
theorem stabilizer_valuationSubring (w : Place L) (hw : IsNonarchimedean w.val) :
    MulAction.stabilizer G (w.val.valuationSubring hw) = MulAction.stabilizer G w := by
  rw [stabilizer_eq]
  refine le_antisymm (fun σ hσ ↦ ?_) (stabilizer_le_stabilizer_valuationSubring hw)
  rw [MulAction.mem_stabilizer_iff] at hσ ⊢
  have h : (σ • w).val.IsEquiv w.val :=
    (isEquiv_iff_valuationSubring (isNonarchimedean_smul_iff.mpr hw) hw).mpr
      ((valuationSubring_smul σ hw).trans hσ)
  exact congrArg Subtype.val (eq_of_isEquiv h)

section Galois

variable {K : Type*} [Field K] [Algebra K L]

/-- **Decomposition groups.** The decomposition group of a finite place `w` in `L ≃ₐ[K] L` is
Mathlib's decomposition subgroup of its valuation subring. -/
theorem stabilizer_eq_decompositionSubgroup (w : Place L) (hw : IsNonarchimedean w.val) :
    MulAction.stabilizer (L ≃ₐ[K] L) w = (w.val.valuationSubring hw).decompositionSubgroup K :=
  (stabilizer_valuationSubring w hw).symm

/-- **Elements acting on residues by a power map.** For a finite place `w`, the two hypotheses
`σ ∈ MulAction.stabilizer (L ≃ₐ[K] L) w` and `w (σ • x - x ^ q) < 1` for all `x` with `w x ≤ 1`
say that `σ` lies in the decomposition subgroup of `A_w` and acts on the residue field of `A_w`
by `y ↦ y ^ q`. -/
theorem mem_stabilizer_and_forall_iff_residue (w : Place L) (hw : IsNonarchimedean w.val)
    {σ : L ≃ₐ[K] L} {q : ℕ} :
    (σ ∈ MulAction.stabilizer (L ≃ₐ[K] L) w ∧ ∀ x, w.val x ≤ 1 → w.val (σ • x - x ^ q) < 1) ↔
      ∃ hσ : σ ∈ (w.val.valuationSubring hw).decompositionSubgroup K,
        ∀ y : ResidueField (w.val.valuationSubring hw),
          (⟨σ, hσ⟩ : (w.val.valuationSubring hw).decompositionSubgroup K) • y = y ^ q := by
  rw [stabilizer_eq_decompositionSubgroup w hw]
  exact ⟨fun ⟨hσ, h⟩ ↦ ⟨hσ, (forall_residue_smul_eq_pow_iff hw hσ).mpr h⟩,
    fun ⟨hσ, h⟩ ↦ ⟨hσ, (forall_residue_smul_eq_pow_iff hw hσ).mp h⟩⟩

/-- **Inertia groups.** The inertia group of a finite place `w` in `L ≃ₐ[K] L` is the image of
Mathlib's inertia subgroup of its valuation subring under the inclusion of the decomposition
subgroup into `L ≃ₐ[K] L`. -/
theorem inertia_eq_map_inertiaSubgroup (w : Place L) (hw : IsNonarchimedean w.val) :
    w.val.inertia (L ≃ₐ[K] L) =
      ((w.val.valuationSubring hw).inertiaSubgroup K).map
        ((w.val.valuationSubring hw).decompositionSubgroup K).subtype := by
  ext σ
  have h := mem_stabilizer_and_forall_iff_residue w hw (σ := σ) (q := 1)
  simp only [pow_one] at h
  rw [mem_inertia_iff_of_isNonarchimedean hw, ← stabilizer_eq, h, Subgroup.mem_map]
  refine ⟨fun ⟨hσ, h⟩ ↦ ⟨⟨σ, hσ⟩, ?_, rfl⟩, ?_⟩
  · rw [ValuationSubring.mem_inertiaSubgroup_iff]
    exact fun x ↦ by rw [ResidueField.residue_smul, h]
  · rintro ⟨g, hg, rfl⟩
    refine ⟨g.property, residue_surjective.forall.mpr fun x ↦ ?_⟩
    rw [← ResidueField.residue_smul]
    exact (ValuationSubring.mem_inertiaSubgroup_iff _ g).mp hg x

end Galois

section Centre

variable {B : Type*} [CommRing B] [Algebra B L] [IsFractionRing B L] [MulSemiringAction G B]
  [SMulDistribClass G B L] {P : Ideal B} [P.IsPrime] [PreValuationRing (Localization.AtPrime P)]

/-- **Decomposition groups of a place and of its centre.** If the valuation subring of a finite
place `w` is centred at the prime `P` of `B` and `B_P` is a valuation ring, the stabiliser of `w`
is the stabiliser of `P`. -/
theorem stabilizer_eq_stabilizer_of_isCenteredAt (w : Place L) (hw : IsNonarchimedean w.val)
    (h : (w.val.valuationSubring hw).IsCenteredAt P) :
    MulAction.stabilizer G w = MulAction.stabilizer G P :=
  (stabilizer_valuationSubring w hw).symm.trans h.stabilizer_eq

/-- **Inertia groups of a place and of its centre.** If the valuation subring of a finite place
`w` is centred at the prime `P` of `B` and `B_P` is a valuation ring, the inertia group of `w` is
Mathlib's inertia subgroup `Ideal.inertia` of `P`. -/
theorem inertia_eq_inertia_of_isCenteredAt (w : Place L) (hw : IsNonarchimedean w.val)
    (h : (w.val.valuationSubring hw).IsCenteredAt P) :
    w.val.inertia G = P.inertia G := by
  ext σ
  have hiff := h.forall_smul_sub_pow_mem_iff (g := σ) (q := 1)
  simp only [pow_one, mem_valuationSubring_iff, mem_nonunits_valuationSubring_iff] at hiff
  rw [mem_inertia_iff_of_isNonarchimedean hw, ← stabilizer_eq,
    stabilizer_eq_stabilizer_of_isCenteredAt w hw h, ← hiff, Ideal.mem_inertia]
  exact ⟨And.right, fun hσ ↦ ⟨Ideal.inertia_le_stabilizer P (Ideal.mem_inertia.mpr hσ), hσ⟩⟩

end Centre

end Place

end AbsoluteValue
