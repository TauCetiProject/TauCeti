/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Subgroup.Pointwise
public import Mathlib.GroupTheory.Sylow
public import Mathlib.Order.Minimal
public import TauCeti.RepresentationTheory.GroupAlgebra.Block.Basic
public import TauCeti.RepresentationTheory.GroupAlgebra.Brauer.Kernel
public import TauCeti.RingTheory.Idempotents.Corner.Local
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
`Tr_S^G(R[G]^S) = Tr_P^G(R[G]^P)` (`TauCeti.relTraceIdeal_eq_of_subgroupOf_eq_sylow`).

For a primitive idempotent `e` of `R[G]^G = Z(R[G])`, for instance a block idempotent, with `R` an
Artinian ring of characteristic `p`, these minimal subgroups are the defect groups of `e`, and they
form one conjugacy class (Webb, Theorem 12.5.2, pp. 244–245). For `P` minimal with
`e = Tr_P^G(a)`, `Br_P(e) ≠ 0`: otherwise `e = Tr_P^G(a) e` lies in `∑_{Q < P} Tr_Q^G(R[G]^Q)`,
and Rosenberg's lemma puts it in one summand. A `p`-subgroup `Q` with `Br_Q(e) ≠ 0` lies in a
conjugate of `P`, since by the Mackey formula the other summands of `Tr_P^G(a)` lie in the kernel of
`Br_Q`. So the defect groups are exactly the conjugates of `P`.

## Main definitions

* `TauCeti.IsDefectGroup R p e P`: `P` is a maximal `p`-subgroup of `G` with `Br_P(e) ≠ 0`.

## Main results

* `TauCeti.IsDefectGroup.conj`: defect groups of a `g`-fixed element are permuted by `g`.
* `TauCeti.exists_isDefectGroup`: every nonzero element of `R[G]` has a defect group.
* `TauCeti.exists_minimal_mem_relTraceIdeal`: every `x ∈ R[G]^G` has a subgroup `P` minimal
  with `x ∈ Tr_P^G(R[G]^P)`.
* `TauCeti.isPGroup_of_minimal_mem_relTraceIdeal`: in characteristic `p`, a subgroup `P` minimal
  with `x ∈ Tr_P^G(R[G]^P)` is a `p`-group.
* `TauCeti.exists_le_conj_of_mem_relTraceIdeal`: a `p`-subgroup `Q` with `Br_Q(x) ≠ 0` for
  `x ∈ Tr_P^G(R[G]^P)` lies in a conjugate of `P`.
* `TauCeti.eq_of_le_of_mem_relTraceIdeal`: such a `Q` containing `P` equals `P`.
* `TauCeti.brauerProjection_ne_zero_of_minimal_mem_relTraceIdeal`: for a primitive idempotent `e`
  of `R[G]^G` and `P` minimal with `e ∈ Tr_P^G(R[G]^P)`, `Br_P(e) ≠ 0`.
* `TauCeti.isDefectGroup_iff_exists_eq_conj`, `TauCeti.isDefectGroup_iff_minimal`,
  `TauCeti.isDefectGroup_conj`: the defect groups of a primitive idempotent of `R[G]^G` are the
  conjugates of a minimal trace subgroup, are exactly the minimal trace subgroups, and are
  conjugate; `TauCeti.IsBlockIdempotent.isDefectGroup_iff_minimal` and
  `TauCeti.IsBlockIdempotent.isDefectGroup_conj` state the last two for block idempotents.

## References

* P. Webb, *A Course in Finite Group Representation Theory*, Theorems 12.4.5 and 12.5.2,
  pp. 241–245, Lemma 12.5.1, p. 244, and Corollary 12.5.5, p. 246.
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
  · exact (brauerProjection_conj_eq_zero_iff_of_conjRepresentation_eq hg).not.2
      h.brauerProjection_ne_zero
  · have hQ' : IsPGroup p (MulAut.conj g⁻¹ • Q : Subgroup G) :=
      hQ.of_equiv (Subgroup.equivSMul _ Q)
    have hQe' : brauerProjection (MulAut.conj g⁻¹ • Q) e ≠ 0 := by
      rwa [Ne, brauerProjection_conj_eq_zero_iff_of_conjRepresentation_eq hg']
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

section Conjugacy

/-! ### Defect groups of a primitive central idempotent

For a primitive idempotent `e` of `R[G]^G = Z(R[G])`, `R` Artinian of characteristic `p`, the
defect groups of `e` are the conjugates of any subgroup `P` minimal with `e ∈ Tr_P^G(R[G]^P)`
(Webb, proof of Theorem 12.5.2, pp. 244–245). `Br_P(e) ≠ 0`, since otherwise `e = Tr_P^G(a) e`
lies in `∑_{Q < P} Tr_Q^G(R[G]^Q)` and Rosenberg's lemma puts it in one summand
(`TauCeti.brauerProjection_ne_zero_of_minimal_mem_relTraceIdeal`); and a `p`-subgroup `Q` with
`Br_Q(e) ≠ 0` lies in a conjugate of `P` by the Mackey formula
(`TauCeti.exists_le_conj_of_mem_relTraceIdeal`). -/

variable {R G : Type*} [CommSemiring R] [Group G]

/-- A block idempotent `b ∈ Z(R[G])`, viewed in `R[G]^G = Z(R[G])`, is a primitive idempotent
there. -/
theorem IsBlockIdempotent.isPrimitiveIdempotent_conjInvariants
    {b : Subalgebra.center R (MonoidAlgebra R G)} (hb : IsBlockIdempotent b) :
    IsPrimitiveIdempotent
      (⟨b, center_le_conjInvariants ⊤ b.property⟩ : conjInvariants R (⊤ : Subgroup G)) := by
  simpa using IsPrimitiveIdempotent.map
    (Subalgebra.equivOfEq _ _ conjInvariants_top.symm).toRingEquiv hb

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

variable [Finite G]

variable {p : ℕ} [Fact p.Prime] [CharP R p]

/-- **A `p`-subgroup detecting a trace lies in a conjugate of the source.** If
`x ∈ Tr_P^G(R[G]^P)` and `Q` is a `p`-subgroup with `Br_Q(x) ≠ 0`, then `Q ≤ gPg⁻¹` for some `g`:
by the Mackey formula `x` is a sum of traces `Tr_{Q ∩ gPg⁻¹}^Q`, and those with `Q ≰ gPg⁻¹` lie in
the kernel of `Br_Q` (Webb, Lemma 12.5.1(2), p. 244). -/
theorem exists_le_conj_of_mem_relTraceIdeal {P Q : Subgroup G}
    {x : conjInvariants R (⊤ : Subgroup G)} (hx : x ∈ relTraceIdeal R (le_top : P ≤ ⊤))
    (hQ : IsPGroup p Q) (hQx : brauerProjection Q (x : MonoidAlgebra R G) ≠ 0) :
    ∃ g : G, Q ≤ MulAut.conj g • P := by
  obtain ⟨a, rfl⟩ := (mem_relTraceIdeal_iff _).1 hx
  by_contra! h
  refine hQx ?_
  have hM := congrArg Subtype.val (inclusion_relTrace_eq_sum_doubleCoset (T := Q) le_top a)
  rw [Subalgebra.coe_inclusion] at hM
  rw [hM, AddSubmonoidClass.coe_finsetSum, map_sum]
  exact Finset.sum_eq_zero fun q _ =>
    brauerProjection_relTrace_eq_zero_of_not_le hQ (h (q.out : G)) _

/-- **A `p`-subgroup detecting a trace is no larger than the source.** If
`x ∈ Tr_P^G(R[G]^P)` and `Q ≥ P` is a `p`-subgroup with `Br_Q(x) ≠ 0`, then `Q = P`: `Q` lies in
a conjugate of `P` (`TauCeti.exists_le_conj_of_mem_relTraceIdeal`), which has the same order as
`P`. -/
theorem eq_of_le_of_mem_relTraceIdeal {P Q : Subgroup G}
    {x : conjInvariants R (⊤ : Subgroup G)} (hx : x ∈ relTraceIdeal R (le_top : P ≤ ⊤))
    (hQ : IsPGroup p Q) (hQx : brauerProjection Q (x : MonoidAlgebra R G) ≠ 0) (hPQ : P ≤ Q) :
    Q = P := by
  obtain ⟨g, hg⟩ := exists_le_conj_of_mem_relTraceIdeal hx hQ hQx
  exact (Subgroup.eq_of_le_of_card_ge hPQ
    ((Subgroup.card_le_of_le hg).trans (card_conj_smul_eq g P).le)).symm

end Conjugacy

section Minimal

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

variable {G : Type*} [Group G] [Finite G]

/-- **The Brauer projection at a minimal trace subgroup.** Let `e` be a primitive idempotent of
`R[G]^G`, with `R` an Artinian ring. If `P` is minimal with
`e ∈ Tr_P^G(R[G]^P)`, then `Br_P(e) ≠ 0` (Webb, proof of Theorem 12.5.2, pp. 244–245): otherwise
`e` lies in the kernel `∑_{Q < P} Tr_Q^P(R[G]^Q)` of `Br_P`, so `e = Tr_P^G(a) e = Tr_P^G(a e)`
lies in `∑_{Q < P} Tr_Q^G(R[G]^Q)`, and Rosenberg's lemma puts `e` in one `Tr_Q^G(R[G]^Q)` with
`Q < P`. -/
theorem brauerProjection_ne_zero_of_minimal_mem_relTraceIdeal {R : Type*} [CommRing R]
    [IsArtinianRing R] {e : conjInvariants R (⊤ : Subgroup G)}
    (he : IsPrimitiveIdempotent e) {P : Subgroup G}
    (hP : Minimal (fun Q : Subgroup G => e ∈ relTraceIdeal R (le_top : Q ≤ ⊤)) P) :
    brauerProjection P (e : MonoidAlgebra R G) ≠ 0 := by
  intro h0
  obtain ⟨a, ha⟩ := (mem_relTraceIdeal_iff _).1 hP.prop
  let eP : conjInvariants R P := Subalgebra.inclusion (conjInvariants_anti le_top) e
  have hker := mem_iSup_relTraceIdeal_of_brauerProjection_eq_zero eP h0
  rw [iSup_subtype'] at hker
  replace hker := Ideal.mul_mem_left _ a hker
  have he2 : relTrace R P ⊤ (a * eP) = e := by
    rw [← relTrace_mul le_top a e, ha, he.isIdempotentElem.eq]
  -- `Tr_P^G` carries `∑_{Q < P} Tr_Q^P(R[G]^Q)` into `∑_{Q < P} Tr_Q^G(R[G]^Q)`.
  have hmem : e ∈ ⨆ i : {Q : Subgroup G // Q < P},
      relTraceIdeal R (le_top : (i : Subgroup G) ≤ ⊤) := by
    rw [← he2]
    refine Submodule.iSup_induction _ (motive := fun y => relTrace R P ⊤ y ∈ _) hker
      (fun i y hy => ?_) (by rw [map_zero]; exact zero_mem _)
      (fun y z hy hz => by rw [map_add]; exact add_mem hy hz)
    obtain ⟨b, rfl⟩ := (mem_relTraceIdeal_iff _).1 hy
    rw [relTrace_relTrace i.property.le le_top]
    exact Ideal.mem_iSup_of_mem i (relTrace_mem_relTraceIdeal le_top b)
  have : IsNoetherian R (conjInvariants R (⊤ : Subgroup G)) :=
    isNoetherian_submodule' (Subalgebra.toSubmodule (conjInvariants R (⊤ : Subgroup G)))
  have : IsArtinianRing (conjInvariants R (⊤ : Subgroup G)) := IsArtinianRing.of_finite R _
  obtain ⟨i, hi⟩ := he.exists_mem_of_mem_iSup _ hmem
  exact i.property.ne (hP.eq_of_le hi i.property.le)

variable {R : Type*} [CommRing R] [IsArtinianRing R] {p : ℕ} [Fact p.Prime] [CharP R p]
  {e : conjInvariants R (⊤ : Subgroup G)}

/-- **Defect groups are the conjugates of a minimal trace subgroup.** Let `e` be a primitive
idempotent of `R[G]^G = Z(R[G])`, with `R` an Artinian ring of characteristic `p`, for instance a
block idempotent of `k[G]` for a field `k` of characteristic `p`. If `P` is minimal with
`e ∈ Tr_P^G(R[G]^P)`, then the defect groups of `e` are exactly the conjugates `gPg⁻¹` (Webb,
Theorem 12.5.2, pp. 244–245). -/
theorem isDefectGroup_iff_exists_eq_conj (he : IsPrimitiveIdempotent e) {P : Subgroup G}
    (hP : Minimal (fun Q : Subgroup G => e ∈ relTraceIdeal R (le_top : Q ≤ ⊤)) P)
    {D : Subgroup G} :
    IsDefectGroup R p (e : MonoidAlgebra R G) D ↔ ∃ g : G, D = MulAut.conj g • P := by
  have hPp : IsPGroup p P := isPGroup_of_minimal_mem_relTraceIdeal hP
  have hPe := brauerProjection_ne_zero_of_minimal_mem_relTraceIdeal he hP
  have hconj (g : G) : IsPGroup p (MulAut.conj g • P : Subgroup G) :=
    hPp.of_equiv (Subgroup.equivSMul _ P)
  have hconjPe (g : G) : brauerProjection (MulAut.conj g • P) (e : MonoidAlgebra R G) ≠ 0 :=
    (brauerProjection_conj_eq_zero_iff_of_conjRepresentation_eq
      (mem_conjInvariants_iff.1 e.property g (Subgroup.mem_top g))).not.2 hPe
  refine ⟨fun hD => ?_, ?_⟩
  · obtain ⟨g, hg⟩ := exists_le_conj_of_mem_relTraceIdeal hP.prop hD.isPGroup
      hD.brauerProjection_ne_zero
    exact ⟨g, hD.eq_of_le ⟨hconj g, hconjPe g⟩ hg⟩
  · rintro ⟨g, rfl⟩
    exact isDefectGroup_iff.2 ⟨hconj g, hconjPe g, fun Q hQ hQe hgQ =>
      eq_of_le_of_mem_relTraceIdeal (mem_relTraceIdeal_conj hP.prop g) hQ hQe hgQ⟩

/-- **Defect groups are the minimal trace subgroups.** For a primitive idempotent `e` of
`R[G]^G = Z(R[G])`, with `R` an Artinian ring of characteristic `p`, the defect groups of `e` are
exactly the subgroups `D` minimal with `e ∈ Tr_D^G(R[G]^D)` (Webb, Theorem 12.4.5, p. 241, and
Theorem 12.5.2, pp. 244–245). -/
theorem isDefectGroup_iff_minimal (he : IsPrimitiveIdempotent e) {D : Subgroup G} :
    IsDefectGroup R p (e : MonoidAlgebra R G) D ↔
      Minimal (fun Q : Subgroup G => e ∈ relTraceIdeal R (le_top : Q ≤ ⊤)) D := by
  refine ⟨fun hD => ?_, fun hD => (isDefectGroup_iff_exists_eq_conj he hD).2 ⟨1, by simp⟩⟩
  obtain ⟨P, hP⟩ := exists_minimal_mem_relTraceIdeal e
  obtain ⟨g, rfl⟩ := (isDefectGroup_iff_exists_eq_conj he hP).1 hD
  exact ⟨mem_relTraceIdeal_conj hP.prop g, fun Q hQ hQg =>
    (eq_of_le_of_mem_relTraceIdeal hQ hD.isPGroup hD.brauerProjection_ne_zero hQg).le⟩

/-- **Defect groups are conjugate.** Any two defect groups of a primitive idempotent `e` of
`R[G]^G = Z(R[G])`, with `R` an Artinian ring of characteristic `p`, are conjugate in `G` (Webb,
Theorem 12.5.2, pp. 244–245). -/
theorem isDefectGroup_conj (he : IsPrimitiveIdempotent e) {D D' : Subgroup G}
    (hD : IsDefectGroup R p (e : MonoidAlgebra R G) D)
    (hD' : IsDefectGroup R p (e : MonoidAlgebra R G) D') :
    ∃ g : G, D' = MulAut.conj g • D :=
  (isDefectGroup_iff_exists_eq_conj he ((isDefectGroup_iff_minimal he).1 hD)).1 hD'

namespace IsBlockIdempotent

variable {b : Subalgebra.center R (MonoidAlgebra R G)}

/-- **Defect groups of a block are the minimal trace subgroups.** For a block idempotent `e_B` of
`R[G]`, with `R` an Artinian ring of characteristic `p`, the defect groups of `e_B` are exactly
the subgroups `D` minimal with `e_B = Tr_D^G(a)` for some `a ∈ R[G]^D` (Webb, Theorem 12.4.5,
p. 241, and Theorem 12.5.2, pp. 244–245). -/
theorem isDefectGroup_iff_minimal (hb : IsBlockIdempotent b) {D : Subgroup G} :
    IsDefectGroup R p (b : MonoidAlgebra R G) D ↔
      Minimal (fun Q : Subgroup G => ∃ a : conjInvariants R Q,
        (relTrace R Q ⊤ a : MonoidAlgebra R G) = b) D := by
  simpa only [mem_relTraceIdeal_iff, Subtype.ext_iff] using
    TauCeti.isDefectGroup_iff_minimal (p := p) (D := D) hb.isPrimitiveIdempotent_conjInvariants

/-- **Defect groups of a block are conjugate.** Any two defect groups of a block idempotent of
`R[G]`, with `R` an Artinian ring of characteristic `p`, for instance a field of characteristic
`p`, are conjugate in `G` (Webb, Theorem 12.5.2, pp. 244–245). -/
theorem isDefectGroup_conj (hb : IsBlockIdempotent b) {D D' : Subgroup G}
    (hD : IsDefectGroup R p (b : MonoidAlgebra R G) D)
    (hD' : IsDefectGroup R p (b : MonoidAlgebra R G) D') :
    ∃ g : G, D' = MulAut.conj g • D :=
  TauCeti.isDefectGroup_conj hb.isPrimitiveIdempotent_conjInvariants hD hD'

end IsBlockIdempotent

end Minimal

end TauCeti
