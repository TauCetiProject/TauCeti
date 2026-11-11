/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LowDimTopology.Bordered.PointedMatchedCircle
public import TauCeti.LowDimTopology.Bordered.StrandsAlgebra.Occupancy
public import TauCeti.LowDimTopology.Bordered.StrandsAlgebra.StrandCount

/-!
# The torus algebra

The genus-one pointed matched circle `Z` has four points, written `0, 1, 2, 3` here and
`1, 2, 3, 4` by Lipshitz, Ozsváth and Thurston, matched as `{0, 2}` and `{1, 3}`
(`TauCeti.PointedMatchedCircle.genusOne`). Its algebra `A(Z)` is the matched subalgebra of the
strands algebra `A(4)` for the matching `Z.pair`, and the summand `A(Z, 0)` with one strand is the
**torus algebra**. By the basis of the one-strand part of a matched subalgebra
(`TauCeti.StrandsAlgebra.oneStrandBasis`), it has the basis consisting of the idempotents
`ι₀ = I({0}) + I({2})` and `ι₁ = I({1}) + I({3})` of the two pairs and the single strands of the
six chords, `ρ₁ = (0 ↦ 1)`, `ρ₂ = (1 ↦ 2)`, `ρ₃ = (2 ↦ 3)`, `ρ₁₂ = (0 ↦ 2)`, `ρ₂₃ = (1 ↦ 3)`
and `ρ₁₂₃ = (0 ↦ 3)`, so it is eight-dimensional (`TauCeti.StrandsAlgebra.finrank_genusOne`).

Two chords multiply to their concatenation when the first ends where the second starts, and to zero
otherwise: `ρ₁ ρ₂ = ρ₁₂` but `ρ₂ ρ₁ = 0`, since `ρ₂` ends at `2`, where `ρ₁` does not start. A
single strand has no crossing, so the differential vanishes on the torus algebra. These are
checked below.

As elements of the summand `matchedSummand R genusOne.pair 1`, a differential algebra with the
restricted differential `matchedSummandDifferential R genusOne.pair 1`, the idempotents are the
`I({p})` of the matched pairs `p` (`TauCeti.StrandsAlgebra.torusIdem`), and the chord `ρ₁₂`
(`TauCeti.StrandsAlgebra.torusRho₁₂`) runs between the two matched points `0` and `2`, so it
starts and ends at the idempotent `ι₀ = I({0, 2})`, and `d ρ₁₂ = 0` and `ρ₁₂ ρ₁₂ = 0`.

## Main definitions

* `TauCeti.StrandsAlgebra.torusIdem`: the idempotent `I({p})` of a matched pair `p` in the torus
  algebra.
* `TauCeti.StrandsAlgebra.torusRho₁₂`: the chord `ρ₁₂` in the torus algebra.

## Main results

* `TauCeti.StrandsAlgebra.finrank_genusOne`: the torus algebra is eight-dimensional.
* `TauCeti.StrandsAlgebra.torusIdem_mul_torusIdem`: the idempotents `I({p})` are orthogonal.
* `TauCeti.StrandsAlgebra.torusIdem_mul_torusRho₁₂`,
  `TauCeti.StrandsAlgebra.torusRho₁₂_mul_torusIdem`: `ρ₁₂` starts and ends at `ι₀`.
* `TauCeti.StrandsAlgebra.matchedSummandDifferential_torusRho₁₂`,
  `TauCeti.StrandsAlgebra.torusRho₁₂_mul_torusRho₁₂`: `d ρ₁₂ = 0` and `ρ₁₂ ρ₁₂ = 0`.

## References

* R. Lipshitz, P. Ozsváth and D. Thurston, *Bordered Heegaard Floer homology*, Mem. Amer. Math.
  Soc. **254** (2018), no. 1216, [arXiv:0810.0687](https://arxiv.org/abs/0810.0687), §3.2 (the
  genus-one pointed matched circle and its algebra).
-/

public section

namespace TauCeti

namespace StrandsAlgebra

open StrandDiagram PointedMatchedCircle

/-- **The torus algebra is eight-dimensional**: the one-strand part of the algebra of the genus-one
pointed matched circle has a basis of two idempotents and six chords. -/
theorem finrank_genusOne (R : Type*) [CommSemiring R] [StrongRankCondition R] :
    Module.finrank R ((matchedSubalgebra R genusOne.pair).toSubmodule ⊓ strandCountPart R 1 :
      Submodule R (StrandsAlgebra R (Fin 4))) = 8 := by
  have hpair : genusOne.pair = ![s(0, 2), s(1, 3), s(0, 2), s(1, 3)] := by
    funext i
    fin_cases i <;> rw [pair_def, genusOne_matching] <;> decide
  have h₁ : Fintype.card (Set.range genusOne.pair) = 2 := by
    rw [← Set.toFinset_card, Set.toFinset_range, hpair]
    decide
  have h₂ : Fintype.card {p : Fin 4 × Fin 4 // p.1 < p.2} = 6 := by
    decide
  rw [finrank_oneStrand, h₁, h₂]

section Elements

open Finset

variable (R : Type*) [CommRing R]

/-- The idempotent `I({p})` of a matched pair `p` of the genus-one pointed matched circle, as an
element of the torus algebra `A(Z, 0)`, the summand of `A(Z)` with one strand. For `p = {0, 2}` it
is `ι₀ = I({0}) + I({2})`, and for `p = {1, 3}` it is `ι₁ = I({1}) + I({3})`. -/
noncomputable def torusIdem (p : Set.range genusOne.pair) : matchedSummand R genusOne.pair 1 :=
  ⟨matchedIdem R genusOne.pair {p.1}, by
    simpa using matchedIdem_mem_matchedSummand (R := R) genusOne.pair {p.1}⟩

@[simp]
theorem coe_torusIdem (p : Set.range genusOne.pair) :
    (torusIdem R p : StrandsAlgebra R (Fin 4)) = matchedIdem R genusOne.pair {p.1} :=
  (rfl)

/-- The idempotents `I({p})` of the torus algebra are orthogonal: `I({p}) I({q})` is `I({p})` when
`p = q` and zero otherwise. -/
@[simp]
theorem torusIdem_mul_torusIdem (p q : Set.range genusOne.pair) :
    torusIdem R p * torusIdem R q = if p = q then torusIdem R p else 0 := by
  refine Subtype.ext ?_
  rw [MulMemClass.coe_mul, coe_torusIdem, coe_torusIdem, matchedIdem_mul_matchedIdem,
    apply_ite Subtype.val, coe_torusIdem, ZeroMemClass.coe_zero]
  exact if_congr (by rw [singleton_inj, Subtype.ext_iff]) rfl rfl

/-- Each `I({p})` is idempotent in the torus algebra. -/
theorem isIdempotentElem_torusIdem (p : Set.range genusOne.pair) :
    IsIdempotentElem (torusIdem R p) :=
  (torusIdem_mul_torusIdem R p p).trans (ite_eq_left rfl)

/-- The chord `ρ₁₂` of the torus algebra: the single strand from `0` to `2`, between the matched
points `0` and `2`. -/
noncomputable def torusRho₁₂ : matchedSummand R genusOne.pair 1 :=
  ⟨of (single 0 2 (by decide)), by
    refine mem_matchedSummand.2 ⟨?_, of_mem_strandSummand (by rw [source_single, card_singleton])⟩
    simpa using oneStrandFamily_mem_matchedSubalgebra (R := R) genusOne.pair
      (.inr ⟨(0, 2), by decide⟩)⟩

@[simp]
theorem coe_torusRho₁₂ :
    (torusRho₁₂ R : StrandsAlgebra R (Fin 4)) = of (single 0 2 (by decide)) :=
  (rfl)

/-- `ρ₁₂` is the generator `a(ρ₁₂, ∅)` of the algebra of the genus-one matching, with no horizontal
strands. -/
private theorem isMatchedGenerator_single_zero_two :
    IsMatchedGenerator genusOne.pair (single (0 : Fin 4) 2 (by decide)) ∅ where
  notMem_self i := by simp only [single_apply]; split_ifs with h <;> simp [h]
  injOn_source := by simp [source_single]
  injOn_target := by simp [target_single]
  disjoint_source := Finset.disjoint_empty_right _
  disjoint_target := Finset.disjoint_empty_right _

/-- `ρ₁₂` starts at the idempotent `ι₀ = I({0, 2})`: `I({p}) ρ₁₂` is `ρ₁₂` when `p = {0, 2}` and
zero otherwise. -/
@[simp]
theorem torusIdem_mul_torusRho₁₂ (p : Set.range genusOne.pair) :
    torusIdem R p * torusRho₁₂ R = if p.1 = s(0, 2) then torusRho₁₂ R else 0 := by
  refine Subtype.ext ?_
  rw [MulMemClass.coe_mul, apply_ite Subtype.val, ZeroMemClass.coe_zero, coe_torusIdem,
    coe_torusRho₁₂, ← horizontalCompletion_empty (M := genusOne.pair),
    matchedIdem_mul_horizontalCompletion _ isMatchedGenerator_single_zero_two]
  refine if_congr ?_ rfl rfl
  rw [source_single, image_singleton, union_empty, singleton_inj, pair_def, genusOne_matching]
  rfl

/-- `ρ₁₂` ends at the idempotent `ι₀ = I({0, 2})`: `ρ₁₂ I({p})` is `ρ₁₂` when `p = {0, 2}` and
zero otherwise. -/
@[simp]
theorem torusRho₁₂_mul_torusIdem (p : Set.range genusOne.pair) :
    torusRho₁₂ R * torusIdem R p = if p.1 = s(0, 2) then torusRho₁₂ R else 0 := by
  refine Subtype.ext ?_
  rw [MulMemClass.coe_mul, apply_ite Subtype.val, ZeroMemClass.coe_zero, coe_torusIdem,
    coe_torusRho₁₂, ← horizontalCompletion_empty (M := genusOne.pair),
    horizontalCompletion_mul_matchedIdem isMatchedGenerator_single_zero_two]
  refine if_congr ?_ rfl rfl
  rw [target_single, image_singleton, union_empty, singleton_inj, eq_comm, pair_def,
    genusOne_matching, Sym2.eq_swap]
  rfl

/-- `ρ₁₂ ρ₁₂ = 0`: `ρ₁₂` ends at `2`, where it does not start. -/
@[simp]
theorem torusRho₁₂_mul_torusRho₁₂ : torusRho₁₂ R * torusRho₁₂ R = 0 :=
  Subtype.ext (of_single_mul_of_single_of_ne _ _ (by decide))

/-- `d ρ₁₂ = 0`: a single strand has no crossing to resolve. -/
@[simp]
theorem matchedSummandDifferential_torusRho₁₂ :
    matchedSummandDifferential R genusOne.pair 1 (torusRho₁₂ R) = 0 :=
  Subtype.ext <| by
    rw [coe_matchedSummandDifferential, coe_torusRho₁₂, ZeroMemClass.coe_zero]
    exact differential_eq_zero_of_mem_strandCountPart le_rfl (by
      simpa using oneStrandFamily_mem_strandCountPart (R := R) genusOne.pair
        (.inr ⟨(0, 2), by decide⟩))

/-- Over a nontrivial ring the chord `ρ₁₂` is nonzero. -/
theorem torusRho₁₂_ne_zero [Nontrivial R] : torusRho₁₂ R ≠ 0 := fun h ↦
  (basis R (Fin 4)).ne_zero (single 0 2 (by decide)) (by
    simpa [basis_apply] using congrArg Subtype.val h)

end Elements

end StrandsAlgebra

end TauCeti

open TauCeti StrandsAlgebra StrandDiagram

/-! ### Products and the differential in the torus algebra -/

/-- `ρ₁ ρ₂ = ρ₁₂`. -/
example :
    (of (single 0 1 (by decide)) * of (single 1 2 (by decide)) :
      StrandsAlgebra (ZMod 2) (Fin 4)) = of (single 0 2 (by decide)) :=
  of_single_mul_of_single _ _

/-- `ρ₂ ρ₁ = 0`: `ρ₂` ends at `2`, where `ρ₁` does not start. -/
example :
    (of (single 1 2 (by decide)) * of (single 0 1 (by decide)) :
      StrandsAlgebra (ZMod 2) (Fin 4)) = 0 :=
  of_single_mul_of_single_of_ne _ _ (by decide)

/-- `ρ₁₂ ρ₃ = ρ₁ ρ₂₃ = ρ₁₂₃`. -/
example :
    (of (single 0 2 (by decide)) * of (single 2 3 (by decide)) :
      StrandsAlgebra (ZMod 2) (Fin 4)) = of (single 0 1 (by decide)) * of (single 1 3 (by decide)) ∧
    (of (single 0 1 (by decide)) * of (single 1 3 (by decide)) :
      StrandsAlgebra (ZMod 2) (Fin 4)) = of (single 0 3 (by decide)) := by
  simp

/-- The differential vanishes on the torus algebra. -/
example (x : StrandsAlgebra (ZMod 2) (Fin 4))
    (hx : x ∈ (matchedSubalgebra (ZMod 2) PointedMatchedCircle.genusOne.pair).toSubmodule ⊓
      strandCountPart (ZMod 2) 1) :
    differential (ZMod 2) (Fin 4) x = 0 :=
  differential_eq_zero_of_mem_strandCountPart le_rfl hx.2
