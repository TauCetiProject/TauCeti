/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.ConjFinite
public import Mathlib.Algebra.Group.Subgroup.Pointwise
public import Mathlib.GroupTheory.Coset.Card
public import Mathlib.GroupTheory.GroupAction.ConjAct
public import Mathlib.GroupTheory.GroupAction.FixedPoints
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.Perm.Cycle.Type
public import TauCeti.Algebra.Group.Conj
public import TauCeti.Algebra.Group.Subgroup.Pointwise
public import TauCeti.GroupTheory.QuotientGroup.Basic

/-!
# Almost-conjugate subgroups

Two subgroups `H` and `K` of a group `G` are **almost conjugate** (also called *Gassmann
equivalent*, or *locally conjugate*) when they meet every conjugacy class of `G` in the same
number of elements. Conjugate subgroups are almost conjugate, but the converse fails: there are
finite groups with non-conjugate almost-conjugate subgroups. These are Gassmann's examples, and
they are the group-theoretic input to the construction of non-isomorphic arithmetically
equivalent number fields.

The notion is equivalently a statement about the coset spaces. For `g : G` the number of cosets
of `H` fixed by `g` is related to the number of elements of `H` conjugate to `g` by the
division-free identity

`#(G ⧸ H)^g · |H| = |C_G(g)| · #(H ∩ [g])`,

where `C_G(g)` is the centralizer of `g`, written as the stabilizer of `g` for the conjugation
action `ConjAct G`, and `[g]` is the conjugacy class of `g`. Both sides count the `x : G` with
`x⁻¹ g x ∈ H`: on the left they are grouped by their coset `x H`, which `g` then fixes, and on the
right by the conjugate `x⁻¹ g x`, whose fibre is a coset of the centralizer. Summing the defining
counts over the conjugacy classes shows that almost-conjugate subgroups of a finite group have the
same order, hence the same index. Dividing the fixed-coset identity by the common order then shows
that `H` and `K` are almost conjugate exactly when every `g : G` fixes as many cosets of `H` as of
`K`.
Through the classification of permutation representations by fixed-point counts this says that
`H` and `K` are almost conjugate exactly when the permutation representations on `G ⧸ H` and
`G ⧸ K` are equivalent in characteristic zero; that consequence is
`TauCeti.almostConjugate_iff_nonempty_equiv_ofMulAction`.

## Main definitions

* `Subgroup.AlmostConjugate H K`: `H` and `K` meet every conjugacy class of `G` in the same number
  of elements. It is decidable for a finite group with decidable equality and decidable subgroup
  membership.

## Main statements

* `Subgroup.AlmostConjugate.refl`, `.symm`, `.trans`: almost-conjugacy is an equivalence relation.
* `Subgroup.AlmostConjugate.map` and `Subgroup.AlmostConjugate.comap`: it is transported along
  group isomorphisms, by `Subgroup.natCard_mem_carrier_map_and_mem_map`, with
  `Subgroup.exists_map_conj_comap_eq_iff` the matching statement for conjugacy itself.
* `Subgroup.almostConjugate_conj_smul` and `Subgroup.almostConjugate_conj_smul_iff`: conjugate
  subgroups are almost conjugate, and almost-conjugacy is invariant under simultaneous
  conjugation.
* `Subgroup.natCard_stabilizer_mul_natCard_mem_carrier`: the `x` with `x⁻¹ g x ∈ H`, counted by
  the conjugate they produce; with `Subgroup.natCard_mul_natCard_fixedBy`, which counts them by
  their cosets, it gives `Subgroup.natCard_fixedBy_mul_natCard`, the fixed-coset identity above.
* `Subgroup.AlmostConjugate.natCard_eq` and `Subgroup.AlmostConjugate.index_eq`: almost-conjugate
  subgroups of a finite group have the same order and the same index.
* `Subgroup.almostConjugate_iff_forall_natCard_fixedBy_eq`: almost-conjugacy is equality of the
  fixed-coset counts.
* `Subgroup.almostConjugate_iff_forall_natCard_cycleType_eq`: two subgroups of a finite symmetric
  group are almost conjugate exactly when they contain equally many permutations of each cycle
  type.

## References

* F. Gassmann, *Bemerkungen zur vorstehenden Arbeit von Hurwitz*, Math. Z. **25** (1926), 665–675.
* R. Perlis, *On the equation `ζ_K(s) = ζ_K'(s)`*, J. Number Theory **9** (1977), 342–360.
-/

public section

open MulAction Pointwise

namespace Subgroup

variable {G Γ : Type*} [Group G] [Group Γ]

/-- Two subgroups `H` and `K` of `G` are **almost conjugate** when they meet every conjugacy class
of `G` in the same number of elements. -/
def AlmostConjugate (H K : Subgroup G) : Prop :=
  ∀ C : ConjClasses G,
    Nat.card {x : G // x ∈ C.carrier ∧ x ∈ H} = Nat.card {x : G // x ∈ C.carrier ∧ x ∈ K}

variable {H K L : Subgroup G}

/-- The defining property of almost-conjugacy. -/
theorem almostConjugate_iff :
    H.AlmostConjugate K ↔ ∀ C : ConjClasses G,
      Nat.card {x : G // x ∈ C.carrier ∧ x ∈ H} = Nat.card {x : G // x ∈ C.carrier ∧ x ∈ K} :=
  Iff.rfl

/-- Almost-conjugacy read on conjugacy classes through their representatives: `H` and `K` are
almost conjugate exactly when, for every `g : G`, they contain equally many conjugates of `g`. -/
theorem almostConjugate_iff_forall_natCard_isConj :
    H.AlmostConjugate K ↔ ∀ g : G,
      Nat.card {x : G // IsConj g x ∧ x ∈ H} = Nat.card {x : G // IsConj g x ∧ x ∈ K} := by
  have hmem (g x : G) : x ∈ (ConjClasses.mk g).carrier ↔ IsConj g x := by
    rw [ConjClasses.mem_carrier_iff_mk_eq, ConjClasses.mk_eq_mk_iff_isConj, isConj_comm]
  refine ⟨fun h g ↦ ?_, fun h C ↦ ?_⟩
  · simpa only [hmem] using h (ConjClasses.mk g)
  · obtain ⟨g, rfl⟩ := ConjClasses.mk_surjective C
    simpa only [hmem] using h g

instance [Fintype G] [DecidableEq G] [DecidablePred (· ∈ H)] [DecidablePred (· ∈ K)] :
    Decidable (H.AlmostConjugate K) :=
  decidable_of_iff (∀ g : G,
      Fintype.card {x : G // IsConj g x ∧ x ∈ H} = Fintype.card {x : G // IsConj g x ∧ x ∈ K}) (by
    simp only [almostConjugate_iff_forall_natCard_isConj, Nat.card_eq_fintype_card])

namespace AlmostConjugate

/-- Every subgroup is almost conjugate to itself. -/
@[refl, simp]
theorem refl (H : Subgroup G) : H.AlmostConjugate H :=
  fun _ ↦ rfl

/-- Every subgroup is almost conjugate to itself; the implicit form of
`Subgroup.AlmostConjugate.refl`. -/
theorem rfl : H.AlmostConjugate H :=
  refl H

/-- Almost-conjugacy is symmetric. -/
@[symm]
theorem symm (h : H.AlmostConjugate K) : K.AlmostConjugate H :=
  fun C ↦ (h C).symm

/-- Almost-conjugacy is symmetric, as an equivalence of propositions. -/
theorem comm : H.AlmostConjugate K ↔ K.AlmostConjugate H :=
  ⟨symm, symm⟩

/-- Almost-conjugacy is transitive. -/
@[trans]
theorem trans (h : H.AlmostConjugate K) (h' : K.AlmostConjugate L) : H.AlmostConjugate L :=
  fun C ↦ (h C).trans (h' C)

/-- Almost-conjugacy is an equivalence relation on the subgroups of `G`. -/
theorem equivalence : Equivalence (AlmostConjugate (G := G)) :=
  ⟨refl, symm, trans⟩

end AlmostConjugate

/-! ### Transport along isomorphisms and conjugation -/

/-- A group isomorphism `e` identifies the elements of `H` in a conjugacy class `C` with the
elements of `e(H)` in the conjugacy class `e(C)`. -/
theorem natCard_mem_carrier_map_and_mem_map (e : G ≃* Γ) (H : Subgroup G)
    (C : ConjClasses G) :
    Nat.card {y : Γ // y ∈ (C.map (e : G →* Γ)).carrier ∧ y ∈ H.map (e : G →* Γ)} =
      Nat.card {x : G // x ∈ C.carrier ∧ x ∈ H} := by
  refine (Nat.card_congr (e.toEquiv.subtypeEquiv fun x ↦ and_congr ?_ ?_)).symm
  · obtain ⟨g, rfl⟩ := ConjClasses.mk_surjective C
    rw [ConjClasses.mem_carrier_iff_mk_eq, ConjClasses.mem_carrier_iff_mk_eq, ConjClasses.map_mk,
      ConjClasses.mk_eq_mk_iff_isConj, ConjClasses.mk_eq_mk_iff_isConj]
    refine ⟨fun hx ↦ (e : G →* Γ).map_isConj hx, fun hx ↦ ?_⟩
    simpa using (e.symm : Γ →* G).map_isConj hx
  · simp

/-- **Almost-conjugacy is transported along group isomorphisms.** -/
theorem AlmostConjugate.map (h : H.AlmostConjugate K) (e : G ≃* Γ) :
    (H.map (e : G →* Γ)).AlmostConjugate (K.map (e : G →* Γ)) := by
  intro D
  obtain ⟨C, rfl⟩ := ConjClasses.map_surjective (f := (e : G →* Γ)) e.surjective D
  rw [natCard_mem_carrier_map_and_mem_map, natCard_mem_carrier_map_and_mem_map]
  exact h C

/-- **Almost-conjugacy is pulled back along group isomorphisms.** -/
theorem AlmostConjugate.comap {H K : Subgroup Γ} (h : H.AlmostConjugate K) (e : G ≃* Γ) :
    (H.comap (e : G →* Γ)).AlmostConjugate (K.comap (e : G →* Γ)) := by
  rw [comap_equiv_eq_map_symm, comap_equiv_eq_map_symm]
  exact h.map e.symm

/-- **Conjugacy of subgroups is pulled back along group isomorphisms.** For an isomorphism
`e : G ≃* Γ`, the preimages of two subgroups of `Γ` are conjugate in `G` exactly when the
subgroups themselves are conjugate in `Γ`. -/
theorem exists_map_conj_comap_eq_iff (e : G ≃* Γ) (H K : Subgroup Γ) :
    (∃ σ : G, (H.comap (e : G →* Γ)).map (MulAut.conj σ : G →* G) = K.comap (e : G →* Γ)) ↔
      ∃ τ : Γ, H.map (MulAut.conj τ : Γ →* Γ) = K := by
  have key (σ : G) : (H.comap (e : G →* Γ)).map (MulAut.conj σ : G →* G) =
      (H.map (MulAut.conj (e σ) : Γ →* Γ)).comap (e : G →* Γ) := by
    ext x
    simp only [mem_map, mem_comap, MonoidHom.coe_ofClass, MulAut.conj_apply]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨e y, hy, by simp⟩
    · rintro ⟨y, hy, hyx⟩
      refine ⟨e.symm y, by simpa using hy, e.injective ?_⟩
      simpa using hyx
  have hinj : Function.Injective (comap (e : G →* Γ)) := comap_injective e.surjective
  refine ⟨fun ⟨σ, hσ⟩ ↦ ⟨e σ, hinj (by rwa [← key])⟩, fun ⟨τ, hτ⟩ ↦ ⟨e.symm τ, ?_⟩⟩
  rw [key, MulEquiv.apply_symm_apply, hτ]

/-- **Conjugate subgroups are almost conjugate.** An inner automorphism maps every conjugacy class
to itself, so it does not change the number of elements a subgroup has in it. -/
@[simp]
theorem almostConjugate_conj_smul (g : G) (H : Subgroup G) :
    H.AlmostConjugate (MulAut.conj g • H) := by
  intro C
  -- The automorphism action on conjugacy classes is `ConjClasses.map` of the automorphism.
  have hC : C.map (MulAut.conj g : G →* G) = C := TauCeti.mulAut_conj_smul_conjClasses g C
  rw [← TauCeti.map_conj_eq_conj_smul,
    ← natCard_mem_carrier_map_and_mem_map (MulAut.conj g) H C, hC]

/-- **Almost-conjugacy is invariant under simultaneous conjugation.** -/
@[simp]
theorem almostConjugate_conj_smul_iff (g : G) :
    (MulAut.conj g • H).AlmostConjugate (MulAut.conj g • K) ↔ H.AlmostConjugate K :=
  ⟨fun h ↦ ((almostConjugate_conj_smul g H).trans h).trans (almostConjugate_conj_smul g K).symm,
    fun h ↦ ((almostConjugate_conj_smul g H).symm.trans h).trans (almostConjugate_conj_smul g K)⟩

/-! ### Fixed cosets -/

/-- The elements `x` of `G` with `x⁻¹ g x ∈ H`, counted by the conjugate they produce: there are
`|C_G(g)|` of them over each element of `H` conjugate to `g`, where the centralizer `C_G(g)` is the
stabilizer of `g` for the conjugation action. This is the companion of
`Subgroup.natCard_mul_natCard_fixedBy`, which counts the same elements by their cosets. -/
theorem natCard_stabilizer_mul_natCard_mem_carrier (H : Subgroup G) (g : G) :
    Nat.card (stabilizer (ConjAct G) g) *
        Nat.card {x : G // x ∈ (ConjClasses.mk g).carrier ∧ x ∈ H} =
      Nat.card {x : G // x⁻¹ * g * x ∈ H} := by
  -- Reparametrize by `c = x⁻¹` in `ConjAct G`, for which `x⁻¹ * g * x = c • g`.
  have e₁ : {x : G // x⁻¹ * g * x ∈ H} ≃ {c : ConjAct G // c • g ∈ H} :=
    (Equiv.inv G).trans ConjAct.toConjAct.toEquiv |>.subtypeEquiv fun x ↦ by
      simp [ConjAct.smul_def]
  -- The conjugates `c • g` are the points of the orbit of `g`, identified with `G ⧸ C_G(g)`.
  set T : Set (ConjAct G ⧸ stabilizer (ConjAct G) g) :=
    {q | ofQuotientStabilizer (ConjAct G) g q ∈ H}
  have hset : {c : ConjAct G | c • g ∈ H} = QuotientGroup.mk ⁻¹' T := by
    ext c
    simp [T, ofQuotientStabilizer_mk]
  have e₂ : T ≃ {x : G // x ∈ (ConjClasses.mk g).carrier ∧ x ∈ H} :=
    ((orbitEquivQuotientStabilizer (ConjAct G) g).symm.subtypeEquiv
        (p := (· ∈ T)) (q := fun y : orbit (ConjAct G) g ↦ (y : G) ∈ H) fun q ↦ by
          induction q using QuotientGroup.induction_on
          simp [T, ofQuotientStabilizer_mk]).trans <|
      (Equiv.subtypeSubtypeEquivSubtypeInter (· ∈ orbit (ConjAct G) g) (· ∈ H)).trans <|
        Equiv.subtypeEquivRight fun x ↦ by rw [ConjAct.orbit_eq_carrier_conjClasses]
  rw [Nat.card_congr e₁, ← Nat.card_congr e₂, ← Nat.card_prod,
    ← Nat.card_congr (QuotientGroup.preimageMkEquivSubgroupProdSet _ T), ← hset, Set.coe_ofPred]

/-- **The fixed-coset identity.** For a subgroup `H` of a group `G` and `g : G`,

`#(G ⧸ H)^g · |H| = |C_G(g)| · #(H ∩ [g])`,

where the centralizer `C_G(g)` is the stabilizer of `g` for the conjugation action and `[g]` is
the conjugacy class of `g`. Both sides count the `x : G` with `x⁻¹ g x ∈ H`; no finiteness is
needed, with the convention that `Nat.card` of an infinite type is `0`. -/
theorem natCard_fixedBy_mul_natCard (H : Subgroup G) (g : G) :
    Nat.card (fixedBy (G ⧸ H) g) * Nat.card H =
      Nat.card (stabilizer (ConjAct G) g) *
        Nat.card {x : G // x ∈ (ConjClasses.mk g).carrier ∧ x ∈ H} := by
  rw [mul_comm, natCard_mul_natCard_fixedBy, natCard_stabilizer_mul_natCard_mem_carrier]

section Finite

variable [Finite G]

/-- **Almost-conjugate subgroups have the same order.** A subgroup is the disjoint union of its
intersections with the conjugacy classes of `G`. -/
theorem AlmostConjugate.natCard_eq (h : H.AlmostConjugate K) : Nat.card H = Nat.card K := by
  classical
  have := Fintype.ofFinite (ConjClasses G)
  have hsum (H : Subgroup G) :
      Nat.card H = ∑ C : ConjClasses G, Nat.card {x : G // x ∈ C.carrier ∧ x ∈ H} := by
    rw [← Nat.card_sigma]
    refine Nat.card_congr <| (Equiv.sigmaFiberEquiv fun x : H ↦ ConjClasses.mk (x : G)).symm.trans
      (Equiv.sigmaCongrRight fun C ↦ ?_)
    exact
      { toFun := fun x ↦ ⟨x.1, ConjClasses.mem_carrier_iff_mk_eq.mpr x.2, x.1.2⟩
        invFun := fun x ↦ ⟨⟨x.1, x.2.2⟩, ConjClasses.mem_carrier_iff_mk_eq.mp x.2.1⟩ }
  rw [hsum H, hsum K]
  exact Finset.sum_congr _root_.rfl fun C _ ↦ h C

/-- **Almost-conjugate subgroups have the same index.** -/
theorem AlmostConjugate.index_eq (h : H.AlmostConjugate K) : H.index = K.index := by
  rw [index_eq_card_div, index_eq_card_div, h.natCard_eq]

/-- **Almost-conjugacy is equality of fixed-coset counts.** Two subgroups `H` and `K` of a finite
group `G` are almost conjugate exactly when every `g : G` fixes as many cosets of `H` as of `K`. -/
theorem almostConjugate_iff_forall_natCard_fixedBy_eq :
    H.AlmostConjugate K ↔
      ∀ g : G, Nat.card (fixedBy (G ⧸ H) g) = Nat.card (fixedBy (G ⧸ K) g) := by
  -- Both directions divide the fixed-coset identity `natCard_fixedBy_mul_natCard`: forwards by the
  -- common order, backwards by the order of a centralizer, once the counts at `g = 1` (the
  -- indices) have shown that `H` and `K` have the same order.
  refine ⟨fun h g ↦ ?_, fun h C ↦ ?_⟩
  · refine Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := H)) ?_
    rw [natCard_fixedBy_mul_natCard, h.natCard_eq, natCard_fixedBy_mul_natCard,
      h (ConjClasses.mk g)]
  · have hi : H.index = K.index := by
      simpa [index_eq_card, fixedBy_one_eq_univ, Nat.card_univ] using h 1
    have hc : Nat.card H = Nat.card K := by
      refine Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero (index_ne_zero_of_finite (H := H))) ?_
      rw [index_mul_card, hi, index_mul_card]
    obtain ⟨g, rfl⟩ := ConjClasses.mk_surjective C
    have : Finite (ConjAct G) := Finite.of_equiv G ConjAct.toConjAct.toEquiv
    refine Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := stabilizer (ConjAct G) g)) ?_
    rw [← natCard_fixedBy_mul_natCard, ← natCard_fixedBy_mul_natCard, h g, hc]

end Finite

/-! ### Subgroups of permutation groups -/

/-- **Almost-conjugacy of permutation groups is equality of cycle-type counts.** Two subgroups of
`Equiv.Perm α`, for a finite type `α`, are almost conjugate exactly when they contain equally many
permutations of each cycle type, because two permutations are conjugate exactly when they have the
same cycle type (`Equiv.Perm.isConj_iff_cycleType_eq`). -/
theorem almostConjugate_iff_forall_natCard_cycleType_eq {α : Type*} [Fintype α] [DecidableEq α]
    {H K : Subgroup (Equiv.Perm α)} :
    H.AlmostConjugate K ↔ ∀ m : Multiset ℕ,
      Nat.card {σ : Equiv.Perm α // σ.cycleType = m ∧ σ ∈ H} =
        Nat.card {σ : Equiv.Perm α // σ.cycleType = m ∧ σ ∈ K} := by
  have key (g : Equiv.Perm α) (L : Subgroup (Equiv.Perm α)) :
      Nat.card {x // IsConj g x ∧ x ∈ L} = Nat.card {σ // σ.cycleType = g.cycleType ∧ σ ∈ L} :=
    Nat.card_congr <| Equiv.subtypeEquivRight fun x ↦ by
      rw [isConj_comm, Equiv.Perm.isConj_iff_cycleType_eq]
  simp only [almostConjugate_iff_forall_natCard_isConj, key]
  refine ⟨fun h m ↦ ?_, fun h g ↦ h g.cycleType⟩
  by_cases hm : ∃ g : Equiv.Perm α, g.cycleType = m
  · obtain ⟨g, rfl⟩ := hm
    exact h g
  · have (L : Subgroup (Equiv.Perm α)) :
        IsEmpty {σ : Equiv.Perm α // σ.cycleType = m ∧ σ ∈ L} :=
      ⟨fun σ ↦ hm ⟨σ, σ.2.1⟩⟩
    rw [Nat.card_of_isEmpty, Nat.card_of_isEmpty]

end Subgroup
