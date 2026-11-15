/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.PGroup
public import TauCeti.RepresentationTheory.Homological.ContCohomology.CohomologicalDimension.Basic
public import TauCeti.RepresentationTheory.Homological.ContCohomology.CohomologicalDimension.ClassModule.Basic
import TauCeti.RepresentationTheory.Homological.ContCohomology.CohomologicalDimension.ClassModule.Cyclic.Kernel
import TauCeti.RepresentationTheory.Homological.ContCohomology.CohomologicalDimension.ClassModule.Transfer.StrictDimension
import TauCeti.RepresentationTheory.Homological.ContCohomology.FiniteCyclic

/-!
# Vanishing of `H¹` of the pro-p class module for a cyclic quotient

Let `G` be a profinite group with `scd_p G ≤ 2` and let `V` be an open normal subgroup such
that `G ⧸ V` is a cyclic `p`-group. Then `H¹(G ⧸ V, V^ab(p)) = 0`. This is the degree-one half
of NSW (3.6.4), (ii) ⇒ (iii), for a cyclic quotient. The vanishing of `H¹` is the analogue of
Hilbert's Theorem 90 among the class formation axioms, so it is one of the two conditions that
make the modules `V^ab(p)` a `p`-class formation for `G`. The prime-order case is the base case
of the induction over `p`-group quotients in NSW (3.6.4).

## Main results

* `TauCeti.subsingleton_h1_abelianizationProP_of_isCyclic`: `H¹(G ⧸ V, V^ab(p)) = 0` for a
  cyclic `p`-group quotient `G ⧸ V`.
* `TauCeti.subsingleton_h1_abelianizationProP_of_card_eq_prime`: the case `#(G ⧸ V) = p`,
  the base case of the induction over `p`-group quotients.

## References

* J. Neukirch, A. Schmidt and K. Wingberg, *Cohomology of Number Fields*, 2nd ed.,
  the proof of (3.6.4), (ii) ⇒ (iii).
-/

public section

namespace TauCeti

open ContCohomology

universe u

variable {p : ℕ} {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TotallyDisconnectedSpace G] {V : Subgroup G} [V.Normal]

/-- **The class module of a cyclic quotient has trivial `H¹`** (NSW (3.6.4), (ii) ⇒ (iii), in
degree one and `p`-primary form). For a profinite group `G` with `scd_p G ≤ 2` and an open normal
subgroup `V` whose quotient `G ⧸ V` is a cyclic `p`-group, `H¹(G ⧸ V, V^ab(p)) = 0`. -/
theorem subsingleton_h1_abelianizationProP_of_isCyclic (hp : p.Prime)
    (h : strictCohomologicalDimensionAt.{u} p G ≤ 2) (hV : IsOpen (V : Set G))
    (hpV : IsPGroup p (G ⧸ V)) [IsCyclic (G ⧸ V)] :
    Subsingleton (H1 (G ⧸ V) (Additive (abelianizationProP p G V))) := by
  have : Finite (G ⧸ V) := V.quotient_finite_of_isOpen hV
  have : V.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  let : Fintype (G ⧸ V) := Subgroup.fintypeQuotientOfFiniteIndex
  obtain ⟨σ, hσ⟩ := IsCyclic.exists_generator (α := G ⧸ V)
  have hs : ∀ q : G ⧸ V, q ∈ Subgroup.zpowers (σ.out : G ⧸ V) := by
    simpa only [QuotientGroup.out_eq'] using hσ
  refine subsingleton_H1_of_forall_mem_zpowers _ hs fun m hm ↦ ?_
  obtain ⟨v, hv⟩ := abelianizationProPMk_surjective p G V m.toMul
  -- The norm of `[v]` is its transfer, so `v` lies in the kernel of the transfer.
  have hVer : abelianizationProPTransfer p G V v = 1 := by
    rw [abelianizationProPTransfer_apply_of_mem, hv]
    simpa only [groupNorm_apply, toMul_sum, Additive.toMul_smul, toMul_zero] using
      congrArg Additive.toMul hm
  obtain ⟨b, hb⟩ := exists_abelianizationProPMk_eq_smul_div_of_mk_eq_one p V hV hpV σ.out hs v
    ((abelianizationProPTransfer_eq_one_iff hp h hV v).mp hVer)
  refine ⟨Additive.ofMul b, ?_⟩
  rw [← ofMul_toMul m, ← hv, hb, ofMul_div, Additive.ofMul_smul]

/-- **The class module of a quotient of prime order has trivial `H¹`.** For a profinite group `G`
with `scd_p G ≤ 2` and an open normal subgroup `V` of prime index `p`, `H¹(G ⧸ V, V^ab(p)) = 0`.
This is the base case of the induction over `p`-group quotients in NSW (3.6.4). -/
theorem subsingleton_h1_abelianizationProP_of_card_eq_prime (hp : p.Prime)
    (h : strictCohomologicalDimensionAt.{u} p G ≤ 2) (hV : IsOpen (V : Set G))
    (hcard : Nat.card (G ⧸ V) = p) :
    Subsingleton (H1 (G ⧸ V) (Additive (abelianizationProP p G V))) :=
  have : Fact p.Prime := ⟨hp⟩
  have : IsCyclic (G ⧸ V) := isCyclic_of_prime_card hcard
  subsingleton_h1_abelianizationProP_of_isCyclic hp h hV
    (.of_card (n := 1) (by rw [hcard, pow_one]))

end TauCeti
