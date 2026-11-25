/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Subgroup.Pointwise
public import Mathlib.GroupTheory.Sylow
public import Mathlib.Order.Minimal
public import TauCeti.RepresentationTheory.GroupAlgebra.Brauer.Projection
import TauCeti.GroupTheory.PGroup

/-!
# Defect groups

For an element `e` of the group algebra `R[G]` and a prime `p`, a **defect group** of `e` is a
`p`-subgroup `P` of `G` with `Br_P(e) ≠ 0`, maximal among the `p`-subgroups with this property
(`TauCeti.IsDefectGroup`). The case of interest is a block idempotent `e` of `k[G]`, `k` a field
of characteristic `p`. Any element fixed by conjugation by `g` has the conjugate defect groups
`gPg⁻¹` (`TauCeti.IsDefectGroup.conj`), and every nonzero element of `R[G]` has a
defect group (`TauCeti.exists_isDefectGroup`).

For `G` finite, every `x ∈ R[G]^G` has subgroups `P` minimal with `x ∈ Tr_P^G(R[G]^P)`
(`TauCeti.exists_minimal_mem_relTraceIdeal`), since `Tr_G^G(R[G]^G) = R[G]^G`. In characteristic
`p` each of them is a `p`-group (`TauCeti.isPGroup_of_minimal_mem_relTraceIdeal`), because
a Sylow `p`-subgroup `S` of `P` has `|P : S|` prime to `p`, so
`Tr_S^G(R[G]^S) = Tr_P^G(R[G]^P)` (`TauCeti.relTraceIdeal_eq_of_subgroupOf_eq_sylow`). For a block
idempotent, these minimal subgroups are its defect groups (Webb, Theorem 12.5.2, pp. 244–245),
which needs Rosenberg's lemma and the Mackey formula.

## Main definitions

* `TauCeti.IsDefectGroup R p e P`: `P` is a maximal `p`-subgroup of `G` with `Br_P(e) ≠ 0`.

## Main results

* `TauCeti.IsDefectGroup.conj`: defect groups of a `g`-fixed element are permuted by `g`.
* `TauCeti.exists_isDefectGroup`: every nonzero element of `R[G]` has a defect group.
* `TauCeti.exists_minimal_mem_relTraceIdeal`: every `x ∈ R[G]^G` has a subgroup `P` minimal
  with `x ∈ Tr_P^G(R[G]^P)`.
* `TauCeti.isPGroup_of_minimal_mem_relTraceIdeal`: in characteristic `p`, a subgroup `P` minimal
  with `x ∈ Tr_P^G(R[G]^P)` is a `p`-group.

## References

* P. Webb, *A Course in Finite Group Representation Theory*, Theorems 12.4.5 and 12.5.2,
  pp. 241–245, and Corollary 12.5.5, p. 246.
* B. Sambale, *Blocks of finite groups and their invariants*, Definition 1.4, p. 14.
-/

public section

namespace TauCeti

open MonoidAlgebra
open scoped Pointwise

section DefectGroup

variable {R G : Type*} [CommSemiring R] [Group G]

variable (R) in
/-- A **defect group** of `e ∈ R[G]` at the prime `p`: a `p`-subgroup `P` of `G` with
`Br_P(e) ≠ 0` that is maximal among the `p`-subgroups with this property (Webb, Theorem 12.5.2
and Corollary 12.5.5, pp. 244–246; Sambale, Definition 1.4, p. 14). The case of interest is a
block idempotent `e` of `k[G]`, `k` a field of characteristic `p`. -/
def IsDefectGroup (p : ℕ) (e : MonoidAlgebra R G) (P : Subgroup G) : Prop :=
  Maximal (fun Q : Subgroup G => IsPGroup p Q ∧ brauerProjection Q e ≠ 0) P

/-- `P` is a defect group of `e` when it is a `p`-group with `Br_P(e) ≠ 0` and every larger
`p`-subgroup `Q` with `Br_Q(e) ≠ 0` is `P`. -/
theorem isDefectGroup_iff {p : ℕ} {e : MonoidAlgebra R G} {P : Subgroup G} :
    IsDefectGroup R p e P ↔ IsPGroup p P ∧ brauerProjection P e ≠ 0 ∧
      ∀ Q : Subgroup G, IsPGroup p Q → brauerProjection Q e ≠ 0 → P ≤ Q → Q = P := by
  refine ⟨fun h => ⟨h.prop.1, h.prop.2, fun Q hQ hQe hPQ => (h.eq_of_le ⟨hQ, hQe⟩ hPQ).symm⟩,
    fun ⟨hP, hPe, h⟩ => ⟨⟨hP, hPe⟩, fun Q hQ hPQ => (h Q hQ.1 hQ.2 hPQ).le⟩⟩

namespace IsDefectGroup

variable {p : ℕ} {e : MonoidAlgebra R G} {P : Subgroup G}

/-- A defect group is a `p`-group. -/
theorem isPGroup (h : IsDefectGroup R p e P) : IsPGroup p P :=
  h.prop.1

/-- The Brauer projection of `e` at a defect group is nonzero. -/
theorem brauerProjection_ne_zero (h : IsDefectGroup R p e P) : brauerProjection P e ≠ 0 :=
  h.prop.2

/-- **Conjugate defect groups.** If `e` is fixed by conjugation by `g`, then `gPg⁻¹` is a defect
group of `e` whenever `P` is. This applies to every `g` when `e` is central. -/
theorem conj (h : IsDefectGroup R p e P) {g : G} (hg : conjRepresentation R G g e = e) :
    IsDefectGroup R p e (MulAut.conj g • P) := by
  have hg' : conjRepresentation R G g⁻¹ e = e :=
    (conjRepresentation R G).inv_apply_eq_iff.2 hg.symm
  refine isDefectGroup_iff.2
    ⟨h.isPGroup.of_equiv (Subgroup.equivSMul _ P), ?_, fun Q hQ hQe hPQ => ?_⟩
  · rw [Ne, ← hg, brauerProjection_conj_eq_zero_iff]
    exact h.brauerProjection_ne_zero
  · have hQ' : IsPGroup p (MulAut.conj g⁻¹ • Q : Subgroup G) :=
      hQ.of_equiv (Subgroup.equivSMul _ Q)
    have hQe' : brauerProjection (MulAut.conj g⁻¹ • Q) e ≠ 0 := by
      rwa [Ne, ← hg', brauerProjection_conj_eq_zero_iff]
    have hPQ' : P ≤ MulAut.conj g⁻¹ • Q := by
      rw [← Subgroup.pointwise_smul_le_pointwise_smul_iff (a := MulAut.conj g), map_inv,
        smul_inv_smul]
      exact hPQ
    rw [← (isDefectGroup_iff.1 h).2.2 _ hQ' hQe' hPQ', map_inv, smul_inv_smul]

end IsDefectGroup

/-- **Defect groups exist.** A nonzero element `e` of `R[G]` has a defect group for every `p`;
no finiteness of `G` is needed. -/
theorem exists_isDefectGroup (p : ℕ) {e : MonoidAlgebra R G} (he : e ≠ 0) :
    ∃ P, IsDefectGroup R p e P := by
  -- Zorn's lemma, starting from `Br_1(e) = e ≠ 0`: the supremum of a chain of `p`-subgroups `Q`
  -- with `Br_Q(e) ≠ 0` is another such subgroup.
  obtain ⟨P, -, hP⟩ := zorn_le_nonempty₀ {Q : Subgroup G | IsPGroup p Q ∧ brauerProjection Q e ≠ 0}
    (fun c hcS hc Q hQ => ⟨sSup c,
      ⟨IsPGroup.sSup_of_directedOn hc.directedOn fun T hT => (hcS hT).1,
        brauerProjection_sSup_ne_zero_of_directedOn ⟨Q, hQ⟩ hc.directedOn fun T hT => (hcS hT).2⟩,
      fun _ => le_sSup⟩)
    ⊥ ⟨IsPGroup.of_bot, mt brauerProjection_bot_eq_zero_iff.1 he⟩
  exact ⟨P, hP⟩

end DefectGroup

section MinimalTrace

variable {R G : Type*} [CommSemiring R] [Group G] {p : ℕ} [Fact p.Prime] [CharP R p] [Finite G]

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

/-- Every `x ∈ R[G]^G` has a subgroup `P` minimal with `x ∈ Tr_P^G(R[G]^P)`: since
`x ∈ Tr_G^G(R[G]^G)` and `G` is finite, some subgroup `P` is minimal with this property. -/
theorem exists_minimal_mem_relTraceIdeal (x : conjInvariants R (⊤ : Subgroup G)) :
    ∃ P : Subgroup G, Minimal (fun Q : Subgroup G => x ∈ relTraceIdeal R (le_top : Q ≤ ⊤)) P := by
  exact exists_minimal_of_wellFoundedLT _ ⟨⊤, by rw [relTraceIdeal_self]; trivial⟩

/-- **Minimal trace subgroups are `p`-groups.** In characteristic `p`, with `G` finite, a subgroup
`P` minimal with `x ∈ Tr_P^G(R[G]^P)` is a `p`-group. -/
theorem isPGroup_of_minimal_mem_relTraceIdeal {x : conjInvariants R (⊤ : Subgroup G)}
    {P : Subgroup G}
    (hP : Minimal (fun Q : Subgroup G => x ∈ relTraceIdeal R (le_top : Q ≤ ⊤)) P) :
    IsPGroup p P := by
  -- A Sylow `p`-subgroup `S` of `P` has `|P : S|` prime to `p`, so
  -- `Tr_S^G(R[G]^S) = Tr_P^G(R[G]^P)` and `S = P` by minimality.
  obtain ⟨S⟩ := Sylow.nonempty (p := p) (G := P)
  let S' : Subgroup G := (S : Subgroup P).map P.subtype
  have hSP : S' ≤ P := Subgroup.map_subtype_le _
  have hS : S'.subgroupOf P = S := by
    rw [← Subgroup.comap_subtype]
    exact Subgroup.comap_map_eq_self_of_injective P.subtype_injective _
  have hmem : x ∈ relTraceIdeal R (le_top : S' ≤ ⊤) := by
    rw [relTraceIdeal_eq_of_subgroupOf_eq_sylow hSP le_top S hS]
    exact hP.prop
  rw [← hP.eq_of_le hmem hSP]
  exact S.isPGroup.map P.subtype

end MinimalTrace

end TauCeti
