/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Nat.Factorization.Basic
public import TauCeti.RepresentationTheory.GroupAlgebra.DefectGroup.Basic
import TauCeti.Algebra.Group.Subgroup.Pointwise

/-!
# The defect of a block

The defect groups of a primitive idempotent `e` of `R[G]^G = Z(R[G])`, `R` an Artinian ring of
characteristic `p` (for instance a block idempotent of `k[G]`, `k` a field of characteristic `p`),
form one conjugacy class of `p`-subgroups (`TauCeti.isDefectGroup_conj`), so they all have the
same order `p ^ d`. The exponent `d` is the **defect** of `e` (`TauCeti.blockDefect`; Sambale,
Proposition 1.5, p. 14; Webb, §12.3, p. 235).

`TauCeti.blockDefect p e` is defined for every `e ∈ R[G]` as the exponent of `p` in the order of
a chosen defect group of `e`, and as `0` when `e` has none, that is when `e = 0`
(`TauCeti.exists_isDefectGroup`). For a primitive idempotent of `R[G]^G` every defect group has
order `p ^ blockDefect p e` (`TauCeti.card_eq_pow_blockDefect`), whichever defect group the
definition chose. The defect is `0` exactly when the trivial subgroup is a defect group, it is at
most the exponent `a` of `p` in `|G|`, and it equals `a` exactly when the defect groups are the
Sylow `p`-subgroups.

The defect is an exponent, not an order: for `C_p` at `p` the single block has defect group `C_p`
and defect `1`, where `|C_p| = p`.

## Main definitions

* `TauCeti.blockDefect p e`: the exponent `d` with `|D| = p ^ d` for a defect group `D` of `e`.

## Main results

* `TauCeti.blockDefect_eq_of_forall_card`: if every defect group of `e` has order `p ^ d`, then
  `blockDefect p e = d`; `TauCeti.blockDefect_zero`: `0` has defect `0`.
* `TauCeti.card_eq_pow_blockDefect`: every defect group of a primitive idempotent of `R[G]^G` has
  order `p ^ blockDefect p e`.
* `TauCeti.blockDefect_eq_zero_iff`: the defect is `0` exactly when `1` is a defect group.
* `TauCeti.blockDefect_le`: the defect of any `e ∈ R[G]` is at most the exponent of `p` in `|G|`.
* `TauCeti.blockDefect_eq_iff_forall_sylow`: the defect is that exponent exactly when every Sylow
  `p`-subgroup is a defect group.
* `TauCeti.IsBlockIdempotent.card_eq_pow_blockDefect`,
  `TauCeti.IsBlockIdempotent.blockDefect_eq_zero_iff`,
  `TauCeti.IsBlockIdempotent.blockDefect_eq_iff_forall_sylow`: the same for a block idempotent.

## References

* B. Sambale, *Blocks of finite groups and their invariants*, Proposition 1.5, p. 14.
* P. Webb, *A Course in Finite Group Representation Theory*, §12.3, p. 235.
-/

public section

namespace TauCeti

open MonoidAlgebra
open scoped Pointwise

section Def

variable {R G : Type*} [CommSemiring R] [Group G]

open Classical in
/-- The **defect** of `e ∈ R[G]` at the prime `p`: the exponent of `p` in the order of a chosen
defect group of `e`, and `0` if `e` has no defect group (only for `e = 0`). For a primitive
idempotent of `R[G]^G` with `R` Artinian of characteristic `p`, for instance a block idempotent of
`k[G]`, every defect group has order `p ^ blockDefect p e` (`TauCeti.card_eq_pow_blockDefect`;
Sambale, Proposition 1.5, p. 14; Webb, §12.3, p. 235). -/
noncomputable def blockDefect (p : ℕ) (e : MonoidAlgebra R G) : ℕ :=
  if h : ∃ D, IsDefectGroup R p e D then (Nat.card h.choose).factorization p else 0

open Classical in
/-- The defining formula of `TauCeti.blockDefect`. -/
theorem blockDefect_def (p : ℕ) (e : MonoidAlgebra R G) :
    blockDefect p e =
      if h : ∃ D, IsDefectGroup R p e D then (Nat.card h.choose).factorization p else 0 := by
  rw [blockDefect]

/-- An element with no defect group has defect `0`. -/
theorem blockDefect_of_forall_not_isDefectGroup {p : ℕ} {e : MonoidAlgebra R G}
    (h : ∀ D, ¬IsDefectGroup R p e D) : blockDefect p e = 0 := by
  simp [blockDefect_def, h]

/-- The element `0` has defect `0`: it has no defect group, since `Br_D(0) = 0`. -/
@[simp]
theorem blockDefect_zero (p : ℕ) : blockDefect p (0 : MonoidAlgebra R G) = 0 :=
  blockDefect_of_forall_not_isDefectGroup fun _ hD => hD.brauerProjection_ne_zero (map_zero _)

/-- **Computing the defect.** If `e` has a defect group and every defect group of `e` has order
`p ^ d`, then `e` has defect `d`. -/
theorem blockDefect_eq_of_forall_card {p : ℕ} [hp : Fact p.Prime] {e : MonoidAlgebra R G}
    {D : Subgroup G} (hD : IsDefectGroup R p e D) {d : ℕ}
    (h : ∀ D', IsDefectGroup R p e D' → Nat.card D' = p ^ d) : blockDefect p e = d := by
  have he : ∃ D, IsDefectGroup R p e D := ⟨D, hD⟩
  simp only [blockDefect_def, he, ↓reduceDIte]
  rw [h _ he.choose_spec, hp.out.factorization_pow, Finsupp.single_eq_same]

/-- **The defect is at most the Sylow exponent.** Every `e ∈ R[G]`, `G` finite, satisfies
`blockDefect p e ≤ a` where `|G|_p = p ^ a`: a defect group is a `p`-subgroup, so it lies in a
Sylow `p`-subgroup. -/
theorem blockDefect_le [Finite G] {p : ℕ} [hp : Fact p.Prime] (e : MonoidAlgebra R G) :
    blockDefect p e ≤ (Nat.card G).factorization p := by
  rw [blockDefect_def]
  split_ifs with h
  · obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 h.choose_spec.isPGroup
    obtain ⟨S, hS⟩ := h.choose_spec.isPGroup.exists_le_sylow
    have hdvd := Subgroup.card_dvd_of_le hS
    rw [hn, S.card_eq_multiplicity] at hdvd
    rw [hn, hp.out.factorization_pow, Finsupp.single_eq_same]
    exact (Nat.pow_dvd_pow_iff_le_right hp.out.one_lt).1 hdvd
  · exact Nat.zero_le _

end Def

section Primitive

variable {R G : Type*} [CommRing R] [IsArtinianRing R] [Group G] [Finite G] {p : ℕ}
  [hp : Fact p.Prime] [CharP R p] {e : conjInvariants R (⊤ : Subgroup G)}

/-- **The order of a defect group.** Every defect group `D` of a primitive idempotent `e` of
`R[G]^G`, with `R` an Artinian ring of characteristic `p`, has order `p ^ blockDefect p e`: the
defect groups are conjugate (`TauCeti.isDefectGroup_conj`), so all have the order of the one
chosen in the definition, a power of `p`. -/
theorem card_eq_pow_blockDefect (he : IsPrimitiveIdempotent e) {D : Subgroup G}
    (hD : IsDefectGroup R p (e : MonoidAlgebra R G) D) :
    Nat.card D = p ^ blockDefect p (e : MonoidAlgebra R G) := by
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hD.isPGroup
  rwa [blockDefect_eq_of_forall_card hD fun D' hD' => by
    obtain ⟨g, rfl⟩ := isDefectGroup_conj he hD hD'
    rw [card_conj_smul_eq, hn]]

/-- **Defect zero.** A primitive idempotent `e` of `R[G]^G`, with `R` an Artinian ring of
characteristic `p`, has defect `0` exactly when the trivial subgroup is a defect group of `e`. -/
theorem blockDefect_eq_zero_iff (he : IsPrimitiveIdempotent e) :
    blockDefect p (e : MonoidAlgebra R G) = 0 ↔ IsDefectGroup R p (e : MonoidAlgebra R G) ⊥ := by
  refine ⟨fun h0 => ?_, fun hD => ?_⟩
  · obtain ⟨D, hD⟩ := he.exists_isDefectGroup p
    rwa [← Subgroup.card_eq_one.1 (by rw [card_eq_pow_blockDefect he hD, h0, pow_zero])]
  · have := card_eq_pow_blockDefect he hD
    simp only [Subgroup.mem_bot, Nat.card_unique, eq_comm (a := 1)] at this
    exact (Nat.pow_eq_one.1 this).resolve_left hp.out.ne_one

/-- **Full defect.** For a primitive idempotent `e` of `R[G]^G`, with `R` an Artinian ring of
characteristic `p`, `blockDefect p e = a`, where `|G|_p = p ^ a`, exactly when every Sylow
`p`-subgroup of `G` is a defect group of `e`. A defect group of order `p ^ a` is a Sylow
subgroup, and the Sylow subgroups and the defect groups are each one conjugacy class. -/
theorem blockDefect_eq_iff_forall_sylow (he : IsPrimitiveIdempotent e) :
    blockDefect p (e : MonoidAlgebra R G) = (Nat.card G).factorization p ↔
      ∀ S : Sylow p G, IsDefectGroup R p (e : MonoidAlgebra R G) S := by
  refine ⟨fun h S => ?_, fun h => ?_⟩
  · obtain ⟨D, hD⟩ := he.exists_isDefectGroup p
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G
      (Sylow.ofCard D (by rw [card_eq_pow_blockDefect he hD, h])) S
    rw [← hg, Sylow.coe_subgroup_smul, Sylow.coe_ofCard]
    exact hD.conj (mem_conjInvariants_iff.1 e.property g (Subgroup.mem_top g))
  · obtain ⟨S⟩ := Sylow.nonempty (p := p) (G := G)
    have hS := card_eq_pow_blockDefect he (h S)
    rw [S.card_eq_multiplicity] at hS
    exact (Nat.pow_right_injective hp.out.two_le hS).symm

end Primitive

namespace IsBlockIdempotent

variable {R G : Type*} [CommRing R] [IsArtinianRing R] [Group G] [Finite G] {p : ℕ}
  [Fact p.Prime] [CharP R p] {b : Subalgebra.center R (MonoidAlgebra R G)}

/-- **The order of a defect group of a block.** Every defect group `D` of a block idempotent
`e_B` of `R[G]`, with `R` an Artinian ring of characteristic `p`, has order
`p ^ blockDefect p e_B` (Sambale, Proposition 1.5, p. 14). -/
theorem card_eq_pow_blockDefect (hb : IsBlockIdempotent b) {D : Subgroup G}
    (hD : IsDefectGroup R p (b : MonoidAlgebra R G) D) :
    Nat.card D = p ^ blockDefect p (b : MonoidAlgebra R G) :=
  TauCeti.card_eq_pow_blockDefect hb.isPrimitiveIdempotent_conjInvariants hD

/-- A block idempotent of `R[G]`, `R` Artinian of characteristic `p`, has defect `0` exactly when
the trivial subgroup is a defect group. -/
theorem blockDefect_eq_zero_iff (hb : IsBlockIdempotent b) :
    blockDefect p (b : MonoidAlgebra R G) = 0 ↔ IsDefectGroup R p (b : MonoidAlgebra R G) ⊥ :=
  TauCeti.blockDefect_eq_zero_iff hb.isPrimitiveIdempotent_conjInvariants

/-- The defect of a block idempotent of `R[G]`, `R` Artinian of characteristic `p`, is the
exponent `a` of `|G|_p = p ^ a` exactly when the Sylow `p`-subgroups are defect groups. -/
theorem blockDefect_eq_iff_forall_sylow (hb : IsBlockIdempotent b) :
    blockDefect p (b : MonoidAlgebra R G) = (Nat.card G).factorization p ↔
      ∀ S : Sylow p G, IsDefectGroup R p (b : MonoidAlgebra R G) S :=
  TauCeti.blockDefect_eq_iff_forall_sylow hb.isPrimitiveIdempotent_conjInvariants

end IsBlockIdempotent

end TauCeti
