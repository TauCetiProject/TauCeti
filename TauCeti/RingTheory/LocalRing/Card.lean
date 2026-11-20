/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- `IsLocalRing.ResidueField` occurs in the statements below.
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
-- Non-public: `TauCeti.quotientEquivResidueField` identifies `R ⧸ 𝔪` with the residue field.
import TauCeti.RingTheory.LocalRing.ResidueField.Quotient
-- `Module.IsUnimodular` occurs in the statements below; the coordinate criterion
-- `TauCeti.Module.isUnimodular_iff_exists_isUnit` is what the count runs on.
public import TauCeti.LinearAlgebra.Unimodular
-- `Nat.card` occurs in the statements below.
public import Mathlib.SetTheory.Cardinal.Finite
-- Non-public: the count `#R = #(R ⧸ 𝔪) · #𝔪` is used only inside the proofs.
import Mathlib.LinearAlgebra.Quotient.Card

/-!
# Counting units and unimodular vectors over a finite local ring

Let `R` be a finite commutative local ring with maximal ideal `𝔪` and residue field of size `q`.
The maximal ideal is the set of nonunits, and it has index `q` in `R`, so `#R = q · #𝔪`. Two counts
follow by taking complements:

* the units are the complement of `𝔪`, so `q · #Rˣ = #R · (q - 1)`;
* a vector `v : ι → R` with finitely many coordinates is unimodular exactly when one of its
  coordinates is a unit (`TauCeti.Module.isUnimodular_iff_exists_isUnit`), so the non-unimodular
  vectors are those of `𝔪^ι`, and with `n = #ι`, `qⁿ · #{unimodular v} = #Rⁿ · (qⁿ - 1)`.

Both are stated multiplied out, so that they hold in `ℕ` without division. For `R = ℤ/4` and
`n = 2` the second gives `4 · 12 = 16 · 3`: there are twelve unimodular rows in `(ℤ/4)²`, the
pairs not both even. These are the counts behind the indices of the congruence levels `K₀(I)` and
`K₁(I)` of `GL₂` over a local ring, whose right cosets are parametrized by unimodular rows.

## Main results

* `TauCeti.IsLocalRing.card_eq_card_maximalIdeal_mul_card_residueField`: `#R = #𝔪 · q`, for any
  local ring.
* `TauCeti.IsLocalRing.card_residueField_mul_card_units`: `q · #Rˣ = #R · (q - 1)`.
* `TauCeti.IsLocalRing.card_residueField_pow_mul_card_isUnimodular`:
  `qⁿ · #{v : ι → R | v unimodular} = #Rⁿ · (qⁿ - 1)` for `n = #ι`.

## References

* J. Voight, *Quaternion Algebras*, GTM 288, 26.4.3, for the count of the projective line over
  `O_v ⧸ 𝔭_v^e` that these counts recover.
-/

public section

namespace TauCeti.IsLocalRing

open _root_.IsLocalRing

variable {R : Type*} [CommRing R] [IsLocalRing R]

/-- The arithmetic shared by the two counts: if a finite set of size `r = q · m` splits into a
part of size `u` and a part of size `m`, then `q · u = r · (q - 1)`. -/
private theorem mul_eq_of_add_eq {q u m r : ℕ} (hr : r = m * q) (h : u + m = r) :
    q * u = r * (q - 1) := by
  have h' : q * u + r = q * r := by rw [hr, mul_comm m q, ← mul_add, h, hr, mul_comm m q]
  rw [Nat.mul_sub_one, mul_comm r q]
  omega

variable (R) in
/-- The maximal ideal has index `q` in `R`: `#R = #𝔪 · q`, as `R ⧸ 𝔪` is the residue field
(`TauCeti.quotientEquivResidueField`). -/
theorem card_eq_card_maximalIdeal_mul_card_residueField :
    Nat.card R = Nat.card (maximalIdeal R) * Nat.card (ResidueField R) := by
  rw [Submodule.card_eq_card_quotient_mul_card (maximalIdeal R),
    Nat.card_congr (quotientEquivResidueField (maximalIdeal.isMaximal R)).toEquiv]

variable (R) [Finite R]

/-- **The units of a finite local ring**: `q · #Rˣ = #R · (q - 1)`, where `q` is the size of the
residue field. The units are the complement of the maximal ideal, which has index `q`. -/
theorem card_residueField_mul_card_units :
    Nat.card (ResidueField R) * Nat.card Rˣ =
      Nat.card R * (Nat.card (ResidueField R) - 1) := by
  refine mul_eq_of_add_eq (m := Nat.card (maximalIdeal R))
    (card_eq_card_maximalIdeal_mul_card_residueField R) ?_
  classical
  rw [Nat.card_congr (Submonoid.unitsTypeEquivIsUnitSubmonoid.toEquiv.trans
      (Equiv.subtypeEquivRight fun _ ↦ notMem_maximalIdeal.symm)), add_comm, ← Nat.card_sum,
    Nat.card_congr (Equiv.sumCompl fun x : R ↦ x ∈ maximalIdeal R)]

/-- **The unimodular vectors over a finite local ring**: for a finite index type `ι` with `n`
elements, `qⁿ · #{v : ι → R | v unimodular} = #Rⁿ · (qⁿ - 1)`, where `q` is the size of the
residue field. A vector is unimodular exactly when it does not lie in `𝔪^ι`, and `#R = q · #𝔪`. -/
theorem card_residueField_pow_mul_card_isUnimodular (ι : Type*) [Fintype ι] :
    Nat.card (ResidueField R) ^ Fintype.card ι * Nat.card {v : ι → R // Module.IsUnimodular R v} =
      Nat.card R ^ Fintype.card ι * (Nat.card (ResidueField R) ^ Fintype.card ι - 1) := by
  -- A vector fails to be unimodular exactly when all of its coordinates lie in `𝔪`.
  have hcompl (v : ι → R) : ¬Module.IsUnimodular R v ↔ ∀ i, v i ∈ maximalIdeal R := by
    simp [TauCeti.Module.isUnimodular_iff_exists_isUnit, mem_maximalIdeal, mem_nonunits_iff]
  have hnon : Nat.card {v : ι → R // ¬Module.IsUnimodular R v} =
      Nat.card (maximalIdeal R) ^ Fintype.card ι := by
    rw [Nat.card_congr ((Equiv.subtypeEquivRight hcompl).trans Equiv.subtypePiEquivPi),
      Nat.card_fun, Nat.card_eq_fintype_card (α := ι)]
  refine mul_eq_of_add_eq (m := Nat.card (maximalIdeal R) ^ Fintype.card ι) ?_ ?_
  · rw [card_eq_card_maximalIdeal_mul_card_residueField R, mul_pow]
  · classical
    rw [← hnon, ← Nat.card_sum,
      Nat.card_congr (Equiv.sumCompl fun v : ι → R ↦ Module.IsUnimodular R v), Nat.card_fun,
      Nat.card_eq_fintype_card (α := ι)]

end TauCeti.IsLocalRing
