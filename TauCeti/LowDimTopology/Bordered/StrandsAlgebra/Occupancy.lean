/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LowDimTopology.Bordered.StrandsAlgebra.Matched
public import TauCeti.RingTheory.Idempotents.Corner.Basic

/-!
# The occupancy summands of the matched subalgebra

The idempotents `I(s)` form a complete family of orthogonal idempotents of the matched subalgebra.
Grouping them by the number `i` of strands gives the occupancy idempotents, which are central
because products preserve the number of strands. As an `R`-algebra, the matched subalgebra is
therefore the product of the corners `e_i A e_i` of the occupancy idempotents, its occupancy
summands (`TauCeti.StrandsAlgebra.OccupancySummand`); for a pointed matched circle these are the
summands `A(Z, j)` of Lipshitz, Ozsváth and Thurston. Resolving a crossing does not move the
endpoints of a diagram, so the differential commutes with the `I(s)` and preserves each summand
(`TauCeti.StrandsAlgebra.occupancyDifferential`), and the isomorphism intertwines the differentials
(`TauCeti.StrandsAlgebra.occupancyAlgEquiv_matchedDifferential`). Over a ring of characteristic
two, this makes each summand an ungraded differential algebra.

## Main definitions

* `TauCeti.StrandsAlgebra.matchedSubalgebraIdem R M s`: the idempotent `I(s)` as an element of
  the matched subalgebra.
* `TauCeti.StrandsAlgebra.occupancyIdem R M i`: the idempotent of the summand with `i` strands.
* `TauCeti.StrandsAlgebra.OccupancySummand R M i`: the summand with `i` strands, the corner of
  `occupancyIdem R M i`.
* `TauCeti.StrandsAlgebra.occupancyAlgEquiv R M`: as an `R`-algebra, the matched subalgebra is
  the product of its occupancy summands.
* `TauCeti.StrandsAlgebra.occupancyDifferential R M i`: the differential of the summand with `i`
  strands.

## Main results

* `TauCeti.StrandsAlgebra.completeOrthogonalIdempotents_matchedSubalgebraIdem`: the `I(s)` are a
  complete family of orthogonal idempotents of the matched subalgebra.
* `TauCeti.StrandsAlgebra.isMulCentral_occupancyIdem`,
  `TauCeti.StrandsAlgebra.completeOrthogonalIdempotents_occupancyIdem`: the occupancy idempotents
  are central and form a complete family of orthogonal idempotents.
* `TauCeti.StrandsAlgebra.occupancyIdem_mul_eq_self_iff`: an element lies in the summand with `i`
  strands exactly when all of its diagrams have `i` strands.
* `TauCeti.StrandsAlgebra.occupancyAlgEquiv_apply_coe`,
  `TauCeti.StrandsAlgebra.occupancyAlgEquiv_symm_apply`: the components of the occupancy
  decomposition are the corners `e_i x e_i`, and an element is the sum of its components.
* `TauCeti.StrandsAlgebra.isUngradedDGAlgebra_occupancyDifferential`: over a ring of
  characteristic two, each occupancy summand is an ungraded differential algebra.
* `TauCeti.StrandsAlgebra.occupancyAlgEquiv_matchedDifferential`: the occupancy decomposition
  intertwines the differentials.

## References

* R. Lipshitz, P. Ozsváth and D. Thurston, *Bordered Heegaard Floer homology*, Mem. Amer. Math.
  Soc. **254** (2018), no. 1216, [arXiv:0810.0687](https://arxiv.org/abs/0810.0687), §3.2 (the
  idempotents `I(s)` and the summands `A(Z, i)`).
-/

public section

noncomputable section

open Finset

namespace TauCeti

namespace StrandsAlgebra

open StrandDiagram

variable {R α β : Type*} [CommSemiring R] [LinearOrder α] [Fintype α]

variable {M : α → β} [DecidableEq β]

variable (R M) in
/-- The idempotent `I(s)`, `TauCeti.StrandsAlgebra.matchedIdem R M s`, as an element of the
matched subalgebra. -/
def matchedSubalgebraIdem (s : Finset β) : matchedSubalgebra R M :=
  ⟨matchedIdem R M s, matchedIdem_mem_matchedSubalgebra M s⟩

@[simp]
theorem coe_matchedSubalgebraIdem (s : Finset β) :
    (matchedSubalgebraIdem R M s : StrandsAlgebra R α) = matchedIdem R M s :=
  (rfl)

/-- The idempotents `I(s)` of the matched subalgebra are cycles. -/
@[simp]
theorem matchedDifferential_matchedSubalgebraIdem (s : Finset β) :
    matchedDifferential R M (matchedSubalgebraIdem R M s) = 0 :=
  Subtype.ext (by simp)

/-- The idempotents `I(s)` of the matched subalgebra are orthogonal: `I(s) I(t)` is `I(s)` when
`s = t` and zero otherwise. -/
@[simp]
theorem matchedSubalgebraIdem_mul_matchedSubalgebraIdem (s t : Finset β) :
    matchedSubalgebraIdem R M s * matchedSubalgebraIdem R M t =
      if s = t then matchedSubalgebraIdem R M s else 0 := by
  apply Subtype.ext
  split_ifs <;> simp [*]

/-- `I(s) x I(t)` vanishes in the matched subalgebra when `s` and `t` have different sizes. -/
theorem matchedSubalgebraIdem_mul_mul_matchedSubalgebraIdem_eq_zero_of_card_ne {s t : Finset β}
    (h : #s ≠ #t) (x : matchedSubalgebra R M) :
    matchedSubalgebraIdem R M s * x * matchedSubalgebraIdem R M t = 0 :=
  Subtype.ext (by simp [matchedIdem_mul_mul_matchedIdem_eq_zero_of_card_ne M h])

variable [Fintype β]

/-- **The idempotents `I(s)` of the matched subalgebra are a complete family of orthogonal
idempotents**: they are idempotent, pairwise orthogonal, and sum to the unit. -/
theorem completeOrthogonalIdempotents_matchedSubalgebraIdem :
    CompleteOrthogonalIdempotents (matchedSubalgebraIdem R M) where
  idem s := by simp [IsIdempotentElem]
  ortho s t hst := by simp [hst]
  complete := Subtype.ext (by simp [matchedOne_eq_sum])

variable (R M) in
/-- The idempotent of the summand of the matched subalgebra with `i` strands: the sum of the
idempotents `I(s)` over the sets `s` of size `i`. For the matching of a pointed matched circle with
`4k` points, `i = k + j` strands give the summand `A(Z, j)` of Lipshitz, Ozsváth and Thurston. -/
def occupancyIdem (i : Fin (Fintype.card β + 1)) : matchedSubalgebra R M :=
  ∑ s with #s = (i : ℕ), matchedSubalgebraIdem R M s

theorem occupancyIdem_def (i : Fin (Fintype.card β + 1)) :
    occupancyIdem R M i = ∑ s with #s = (i : ℕ), matchedSubalgebraIdem R M s :=
  (rfl)

/-- In the strands algebra, the idempotent of the summand with `i` strands is the sum of the
idempotents `I(s)` over the sets `s` of size `i`. -/
@[simp]
theorem coe_occupancyIdem (i : Fin (Fintype.card β + 1)) :
    (occupancyIdem R M i : StrandsAlgebra R α) = ∑ s with #s = (i : ℕ), matchedIdem R M s := by
  simp [occupancyIdem_def]

/-- The coefficients of `e_i x` are those of `x` at the diagrams with `i` strands, and zero at the
other diagrams. -/
theorem repr_coe_occupancyIdem_mul_apply (i : Fin (Fintype.card β + 1))
    (x : matchedSubalgebra R M) (φ : StrandDiagram α) :
    (basis R α).repr ((occupancyIdem R M i * x : matchedSubalgebra R M) : StrandsAlgebra R α) φ =
      if #φ.source = (i : ℕ) then (basis R α).repr (x : StrandsAlgebra R α) φ else 0 := by
  have := Fintype.ofFinite (StrandDiagram α)
  set y : StrandsAlgebra R α := ↑x with hy
  have hx := (mem_matchedSubalgebra.1 x.2).1
  have key : (∑ s with #s = (i : ℕ), matchedIdem R M s) * y =
      ∑ ψ, (if #ψ.source = (i : ℕ) then (basis R α).repr y ψ else 0) • basis R α ψ := by
    conv_lhs => rw [← (basis R α).sum_repr y]
    simp only [mul_sum, mul_smul_comm, basis_apply]
    refine sum_congr rfl fun ψ _ ↦ ?_
    by_cases h : (basis R α).repr y ψ = 0
    · simp [h]
    · simp only [sum_mul, matchedIdem_mul_of, ite_and, sum_ite_eq, mem_filter, mem_univ,
        true_and, card_image_of_injOn (hx ψ h).1, ite_true]
      split_ifs <;> simp
  rw [MulMemClass.coe_mul, coe_occupancyIdem, ← hy, key, (basis R α).repr_sum_self]

/-- **An element lies in the summand with `i` strands**, that is `e_i x = x`, exactly when all of
its diagrams have `i` strands. -/
theorem occupancyIdem_mul_eq_self_iff {i : Fin (Fintype.card β + 1)} {x : matchedSubalgebra R M} :
    occupancyIdem R M i * x = x ↔
      ∀ φ, (basis R α).repr (x : StrandsAlgebra R α) φ ≠ 0 → #φ.source = (i : ℕ) := by
  refine ⟨fun h φ hφ ↦ ?_, fun h ↦ Subtype.ext ((basis R α).ext_elem fun φ ↦ ?_)⟩
  · by_contra hne
    exact hφ (by rw [← h, repr_coe_occupancyIdem_mul_apply]; simp [hne])
  · rw [repr_coe_occupancyIdem_mul_apply]
    split_ifs with hφ
    · rfl
    · exact (not_not.1 (mt (h φ) hφ)).symm

/-- The occupancy idempotents are cycles. -/
@[simp]
theorem matchedDifferential_occupancyIdem (i : Fin (Fintype.card β + 1)) :
    matchedDifferential R M (occupancyIdem R M i) = 0 := by
  simp [occupancyIdem_def]

/-- The differential commutes with left multiplication by an occupancy idempotent. -/
theorem matchedDifferential_occupancyIdem_mul (i : Fin (Fintype.card β + 1))
    (x : matchedSubalgebra R M) :
    matchedDifferential R M (occupancyIdem R M i * x) =
      occupancyIdem R M i * matchedDifferential R M x :=
  Subtype.ext (by simp [sum_mul, differential_matchedIdem_mul])

/-- The differential commutes with right multiplication by an occupancy idempotent. -/
theorem matchedDifferential_mul_occupancyIdem (x : matchedSubalgebra R M)
    (i : Fin (Fintype.card β + 1)) :
    matchedDifferential R M (x * occupancyIdem R M i) =
      matchedDifferential R M x * occupancyIdem R M i :=
  Subtype.ext (by simp [mul_sum, differential_mul_matchedIdem])

/-- `e_i x e_j` vanishes for distinct occupancy idempotents `e_i` and `e_j`. -/
theorem occupancyIdem_mul_mul_occupancyIdem_eq_zero_of_ne {i j : Fin (Fintype.card β + 1)}
    (h : i ≠ j) (x : matchedSubalgebra R M) :
    occupancyIdem R M i * x * occupancyIdem R M j = 0 := by
  simp only [occupancyIdem_def, sum_mul, mul_sum]
  refine sum_eq_zero fun s hs ↦ sum_eq_zero fun t ht ↦
    matchedSubalgebraIdem_mul_mul_matchedSubalgebraIdem_eq_zero_of_card_ne ?_ x
  rw [(mem_filter.1 hs).2, (mem_filter.1 ht).2]
  exact Fin.val_injective.ne h

/-- **The occupancy idempotents are a complete family of orthogonal idempotents.** -/
theorem completeOrthogonalIdempotents_occupancyIdem :
    CompleteOrthogonalIdempotents (occupancyIdem R M) := by
  refine (CompleteOrthogonalIdempotents.iff_ortho_complete).2 ⟨fun i j hij ↦ ?_, ?_⟩
  · simpa [occupancyIdem_def, ← mul_assoc] using
      occupancyIdem_mul_mul_occupancyIdem_eq_zero_of_ne (R := R) (M := M) hij 1
  · rw [← completeOrthogonalIdempotents_matchedSubalgebraIdem.complete]
    have hlt (s : Finset β) : #s < Fintype.card β + 1 := Nat.lt_succ_of_le (card_le_univ s)
    rw [← sum_fiberwise univ (fun s ↦ (⟨#s, hlt s⟩ : Fin (Fintype.card β + 1)))
      (matchedSubalgebraIdem R M)]
    refine sum_congr rfl fun i _ ↦ sum_congr ?_ fun _ _ ↦ rfl
    ext s
    simp [Fin.ext_iff]

/-- **The occupancy idempotents are central**: the products in the matched subalgebra preserve the
number of strands. -/
theorem isMulCentral_occupancyIdem (i : Fin (Fintype.card β + 1)) :
    IsMulCentral (occupancyIdem R M i) :=
  completeOrthogonalIdempotents_occupancyIdem.isMulCentral_of_mul_mul_eq_zero
    (fun _ _ h x ↦ occupancyIdem_mul_mul_occupancyIdem_eq_zero_of_ne h x) i

variable (R M) in
/-- The occupancy summand of the matched subalgebra with `i` strands: the corner `e_i A e_i` of
the occupancy idempotent `e_i`, an `R`-algebra with unit `e_i`. For the matching of a pointed
matched circle with `4k` points, `i = k + j` strands give the summand `A(Z, j)` of Lipshitz,
Ozsváth and Thurston. -/
abbrev OccupancySummand (i : Fin (Fintype.card β + 1)) : Type _ :=
  ((completeOrthogonalIdempotents_occupancyIdem (R := R) (M := M)).idem i).Corner

variable (R M) in
/-- **The occupancy decomposition of the matched subalgebra.** As an `R`-algebra, the matched
subalgebra is the product of its occupancy summands, the corners `e_i A e_i` of its central
occupancy idempotents `e_i`. Its compatibility with the differential is
`occupancyAlgEquiv_matchedDifferential`. -/
def occupancyAlgEquiv : matchedSubalgebra R M ≃ₐ[R] Π i, OccupancySummand R M i :=
  completeOrthogonalIdempotents_occupancyIdem.algEquivOfIsMulCentral R isMulCentral_occupancyIdem

/-- The component of `x` in the summand with `i` strands is `e_i x e_i`. -/
@[simp]
theorem occupancyAlgEquiv_apply_coe (x : matchedSubalgebra R M) (i : Fin (Fintype.card β + 1)) :
    (occupancyAlgEquiv R M x i).1 = occupancyIdem R M i * x * occupancyIdem R M i :=
  completeOrthogonalIdempotents_occupancyIdem.val_algEquivOfIsMulCentral_apply _ x i

/-- An element is recovered from its occupancy components as their sum. -/
@[simp]
theorem occupancyAlgEquiv_symm_apply (y : Π i, OccupancySummand R M i) :
    (occupancyAlgEquiv R M).symm y = ∑ i, (y i).1 :=
  completeOrthogonalIdempotents_occupancyIdem.algEquivOfIsMulCentral_symm_apply _ y

variable (R M) in
/-- The differential of the occupancy summand with `i` strands: the restriction of the
differential of the matched subalgebra, which preserves the corner `e_i A e_i` because it commutes
with multiplication by `e_i`. -/
def occupancyDifferential (i : Fin (Fintype.card β + 1)) :
    OccupancySummand R M i →ₗ[R] OccupancySummand R M i where
  toFun y := ⟨matchedDifferential R M y.1, by
    obtain ⟨r, hr⟩ := y.2
    exact ⟨matchedDifferential R M r, by
      rw [← hr, matchedDifferential_mul_occupancyIdem, matchedDifferential_occupancyIdem_mul]⟩⟩
  map_add' y z := Subtype.ext (map_add (matchedDifferential R M) y.1 z.1)
  map_smul' r y := Subtype.ext (map_smul (matchedDifferential R M) r y.1)

@[simp]
theorem occupancyDifferential_apply_coe (i : Fin (Fintype.card β + 1))
    (y : OccupancySummand R M i) :
    (occupancyDifferential R M i y).1 = matchedDifferential R M y.1 :=
  (rfl)

/-- The differential of an occupancy summand squares to zero. -/
@[simp]
theorem occupancyDifferential_occupancyDifferential [CharP R 2] (i : Fin (Fintype.card β + 1))
    (y : OccupancySummand R M i) :
    occupancyDifferential R M i (occupancyDifferential R M i y) = 0 :=
  Subtype.ext (Subtype.ext (by simp [differential_differential]))

/-- **The Leibniz rule** for the differential of an occupancy summand. -/
theorem occupancyDifferential_mul [CharP R 2] (i : Fin (Fintype.card β + 1))
    (y z : OccupancySummand R M i) :
    occupancyDifferential R M i (y * z) =
      occupancyDifferential R M i y * z + y * occupancyDifferential R M i z :=
  Subtype.ext (matchedDifferential_mul y.1 z.1)

/-- Over a ring of characteristic two, each occupancy summand with its differential is an ungraded
differential algebra. -/
theorem isUngradedDGAlgebra_occupancyDifferential {R : Type*} [CommRing R] [CharP R 2]
    (i : Fin (Fintype.card β + 1)) :
    IsUngradedDGAlgebra (occupancyDifferential R M i) where
  map_mul := occupancyDifferential_mul i
  map_map := occupancyDifferential_occupancyDifferential i

/-- The occupancy decomposition intertwines the differential of the matched subalgebra with the
differentials of its occupancy summands. -/
theorem occupancyAlgEquiv_matchedDifferential (x : matchedSubalgebra R M)
    (i : Fin (Fintype.card β + 1)) :
    occupancyAlgEquiv R M (matchedDifferential R M x) i =
      occupancyDifferential R M i (occupancyAlgEquiv R M x i) :=
  Subtype.ext (by
    simp [matchedDifferential_mul_occupancyIdem, matchedDifferential_occupancyIdem_mul])

end StrandsAlgebra

end TauCeti
