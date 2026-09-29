/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Torsion
public import TauCeti.NumberTheory.Padics.RingHoms
public import TauCeti.Topology.Algebra.ContinuousMulEquiv
public import TauCeti.Topology.Algebra.Group.Profinite.Demushkin.Basic
public import TauCeti.Topology.Algebra.Group.Profinite.Presentation.Abelianization
import Mathlib.Topology.Algebra.Module.Equiv.Prod
import TauCeti.Topology.Algebra.Group.Profinite.ProP.Torsion

/-!
# The abelianization of a Demushkin group and Labute's `q`-invariant

A Demushkin group `G` of rank `n` is a one-relator pro-`p` group, presented on `n` generators by a
single relator `r` lying in the Frattini subgroup of the free pro-`p` group. Abelianizing that
presentation exhibits the topological abelianization as

`G^{ab} ≅ ℤ_p^{n-1} × ℤ_p ⧸ q ℤ_p`

for a coordinate `q` of the exponent vector of `r` (Labute, p. 106). Because `r` lies in the
Frattini subgroup, `q` is divisible by `p`, so the factor `ℤ_p ⧸ q ℤ_p` is either `ℤ_p` (when
`q = 0`) or a finite cyclic group of order `p ^ v_p(q) ≥ p`. Consequently the torsion subgroup of
`G^{ab}` is finite and cyclic, and it is trivial exactly when `q = 0`.

**Labute's `q`-invariant** `demushkinQ hG` is read off from the topological abelianization alone:
it is `0` when `G^{ab}` is torsion-free and the order of the torsion subgroup otherwise. The
structure theorem is then restated with this invariant as the modulus,
`G^{ab} ≅ ℤ_p^{n-1} × ℤ_p ⧸ (q(G))`, which shows that `q(G)` is the invariant `q` of Labute's
classification, an isomorphism invariant divisible by `p`. It is the first of the two invariants,
together with the rank, that classify Demushkin groups with `q ≠ 2`.

## Main definitions

* `TauCeti.demushkinQ`: Labute's `q`-invariant of a Demushkin group.

## Main results

* `TauCeti.IsDemushkin.finite_torsion_topologicalAbelianization`,
  `TauCeti.IsDemushkin.isCyclic_torsion_topologicalAbelianization`: the torsion subgroup of the
  abelianization of a Demushkin group is finite and cyclic.
* `TauCeti.IsDemushkin.nonempty_continuousMulEquiv_topologicalAbelianization`: the
  **abelianization structure theorem** `G^{ab} ≃ₜ* ℤ_p^{n-1} × ℤ_p ⧸ (q(G))`.
* `TauCeti.IsDemushkin.prime_dvd_demushkinQ`: `p ∣ q(G)`, because the relator of a minimal
  presentation lies in the Frattini subgroup.
* `TauCeti.demushkinQ_eq_zero_iff`: `q(G) = 0` exactly when `G^{ab}` is torsion-free.
* `TauCeti.demushkinQ_congr`: the `q`-invariant is invariant under topological isomorphism.

## References

* J. P. Labute, *Classification of Demushkin groups*, Canad. J. Math. 19 (1967), 106–132, p. 106.
* J.-P. Serre, *Galois Cohomology*, I §4.5.
-/

public section

namespace TauCeti

open CommGroup (torsion)
open Multiplicative

universe u v

variable {p : ℕ} [Fact p.Prime] {G : Type u} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G]

open scoped Classical in
/-- **Labute's `q`-invariant** of a Demushkin group. It is `0` when the topological abelianization
`G^{ab}` is torsion-free, which is Labute's `q = p^∞` convention, and the number of torsion elements
of `G^{ab}` otherwise. For a Demushkin group of rank `n` the torsion subgroup of `G^{ab}` is finite
and cyclic, and `G^{ab} ≅ ℤ_p^{n-1} × ℤ_p ⧸ (q)`
(`TauCeti.IsDemushkin.nonempty_continuousMulEquiv_topologicalAbelianization`). -/
noncomputable def demushkinQ (_hG : IsDemushkin p G) : ℕ :=
  if torsion (TopologicalAbelianization G) = ⊥ then 0
  else Nat.card (torsion (TopologicalAbelianization G))

variable (hG : IsDemushkin p G)

/-- The `q`-invariant vanishes when the abelianization is torsion-free. -/
theorem demushkinQ_of_isMulTorsionFree (h : IsMulTorsionFree (TopologicalAbelianization G)) :
    demushkinQ hG = 0 := by
  simp [demushkinQ, CommGroup.isMulTorsionFree_iff_torsion_eq_bot.mp h]

/-- When the abelianization is not torsion-free, the `q`-invariant is the number of its torsion
elements. -/
theorem demushkinQ_of_not_isMulTorsionFree
    (h : ¬ IsMulTorsionFree (TopologicalAbelianization G)) :
    demushkinQ hG = Nat.card (torsion (TopologicalAbelianization G)) := by
  simp [demushkinQ, CommGroup.isMulTorsionFree_iff_torsion_eq_bot.not.mp h]

/-- **The `q`-invariant is an isomorphism invariant.** -/
theorem demushkinQ_congr {H : Type v} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    (hH : IsDemushkin p H) (e : G ≃ₜ* H) :
    demushkinQ hG = demushkinQ hH := by
  let f := e.topologicalAbelianizationCongr.toMulEquiv
  have hcard : Nat.card (torsion (TopologicalAbelianization G)) =
      Nat.card (torsion (TopologicalAbelianization H)) :=
    Nat.card_congr
      ((f.subgroupMap (torsion _)).trans (MulEquiv.subgroupCongr f.map_torsion)).toEquiv
  have hfree : IsMulTorsionFree (TopologicalAbelianization G) ↔
      IsMulTorsionFree (TopologicalAbelianization H) :=
    ⟨fun _ ↦ Function.Injective.isMulTorsionFree f.symm.toMonoidHom f.symm.injective,
      fun _ ↦ Function.Injective.isMulTorsionFree f.toMonoidHom f.injective⟩
  by_cases h : IsMulTorsionFree (TopologicalAbelianization G)
  · rw [demushkinQ_of_isMulTorsionFree hG h, demushkinQ_of_isMulTorsionFree hH (hfree.mp h)]
  · rw [demushkinQ_of_not_isMulTorsionFree hG h,
      demushkinQ_of_not_isMulTorsionFree hH (hfree.not.mp h), hcard]

variable [CompactSpace G] [TotallyDisconnectedSpace G]

namespace IsDemushkin

include hG

/-- The one-relator presentation of a Demushkin group, abelianized: for some coordinate `q` of the
exponent vector of the relator, which is divisible by `p` because the relator lies in the Frattini
subgroup, `G^{ab} ≅ ℤ_p^{n-1} × ℤ_p ⧸ (q)`. The public form,
`nonempty_continuousMulEquiv_topologicalAbelianization`, replaces `q` by the `q`-invariant. -/
private theorem exists_dvd_nonempty_continuousMulEquiv_topologicalAbelianization :
    ∃ q : ℤ_[p], (p : ℤ_[p]) ∣ q ∧
      Nonempty (TopologicalAbelianization G ≃ₜ*
        Multiplicative ((Fin (demushkinRank hG - 1) → ℤ_[p]) × (ℤ_[p] ⧸ Ideal.span {q}))) := by
  obtain ⟨r, hr, ⟨e⟩⟩ := hG.exists_mem_proPFrattini_continuousMulEquiv_presentedProP
    (ULift.{u} (Fin (demushkinRank hG))) (by simp)
  have : Nonempty (ULift.{u} (Fin (demushkinRank hG))) := ⟨⟨⟨0, hG.demushkinRank_pos⟩⟩⟩
  obtain ⟨x₀, hx₀⟩ := PreValuationRing.exists_forall_dvd (freeProP.exponentSum p _ r).toAdd
  obtain ⟨w, hw, hv⟩ := exists_eq_smul_of_forall_dvd hx₀
  refine ⟨_, freeProP.dvd_exponentSum_of_mem_proPFrattini p _ hr x₀, ?_⟩
  -- Reindex the free factor `ℤ_p^{X ∖ {x₀}}` by `Fin (n - 1)`.
  have hcard : Nat.card {x : ULift.{u} (Fin (demushkinRank hG)) // x ≠ x₀} =
      demushkinRank hG - 1 := by
    have h := Nat.card_congr (Equiv.optionSubtypeNe x₀)
    rw [Finite.card_option, Nat.card_ulift, Nat.card_fin] at h
    omega
  let ι : Fin (demushkinRank hG - 1) ≃ {x : ULift.{u} (Fin (demushkinRank hG)) // x ≠ x₀} :=
    (finCongr hcard.symm).trans (Finite.equivFin _).symm
  let f := (ContinuousLinearEquiv.piCongrLeft ℤ_[p] (fun _ ↦ ℤ_[p]) ι).prodCongr
    (ContinuousLinearEquiv.refl ℤ_[p] (ℤ_[p] ⧸ Ideal.span {(freeProP.exponentSum p _ r).toAdd x₀}))
  exact ⟨e.symm.topologicalAbelianizationCongr.trans
    ((presentedProP.oneRelatorAbelianizationEquiv r x₀ w hw _ hv).trans
      f.toContinuousAddEquiv.toMultiplicative.symm)⟩

/-- The abelianization structure theorem together with the cyclicity of the torsion subgroup and
the divisibility of the `q`-invariant, all read off the model `ℤ_p^{n-1} × ℤ_p ⧸ (q)` with `p ∣ q`;
the public statements below are its projections. -/
private theorem torsion_spec :
    IsCyclic (torsion (TopologicalAbelianization G)) ∧ p ∣ demushkinQ hG ∧
      Nonempty (TopologicalAbelianization G ≃ₜ*
        Multiplicative ((Fin (demushkinRank hG - 1) → ℤ_[p]) ×
          (ℤ_[p] ⧸ Ideal.span {(demushkinQ hG : ℤ_[p])}))) := by
  obtain ⟨q, hpq, ⟨e⟩⟩ := hG.exists_dvd_nonempty_continuousMulEquiv_topologicalAbelianization
  by_cases hq : q = 0
  · -- `q = 0`: the abelianization is torsion-free and the `q`-invariant is `0`.
    subst hq
    have hfree : IsMulTorsionFree (TopologicalAbelianization G) := by
      have : IsAddTorsionFree (ℤ_[p] ⧸ Ideal.span {(0 : ℤ_[p])}) := by
        rw [Ideal.span_singleton_zero]
        exact (RingEquiv.quotientBot ℤ_[p]).injective.isAddTorsionFree
          (RingEquiv.quotientBot ℤ_[p]).toAddMonoidHom
      exact Function.Injective.isMulTorsionFree e.toMulEquiv.toMonoidHom e.toMulEquiv.injective
    have h0 := demushkinQ_of_isMulTorsionFree hG hfree
    rw [CommGroup.isMulTorsionFree_iff_torsion_eq_bot] at hfree
    have hcyc : IsCyclic (torsion (TopologicalAbelianization G)) := by rw [hfree]; infer_instance
    refine ⟨hcyc, h0 ▸ dvd_zero p, ?_⟩
    rw [h0, Nat.cast_zero]
    exact ⟨e⟩
  · -- `q ≠ 0`: the torsion subgroup is `ℤ_p ⧸ (q)`, of order `p ^ v_p(q)` with `v_p(q) ≥ 1`.
    have := PadicInt.finite_quotient_span hq
    have := PadicInt.isAddCyclic_quotient_span hq
    have hcard : Nat.card (torsion (TopologicalAbelianization G)) = p ^ q.valuation := by
      rw [natCard_torsion_of_mulEquiv isAddTorsion_of_finite e.toMulEquiv,
        PadicInt.natCard_quotient_span hq]
    obtain ⟨c, rfl⟩ := hpq
    have hc : c ≠ 0 := right_ne_zero_of_mul hq
    have hval := PadicInt.valuation_p_pow_mul 1 c hc
    rw [pow_one] at hval
    have hne : ¬ IsMulTorsionFree (TopologicalAbelianization G) := by
      rw [CommGroup.isMulTorsionFree_iff_torsion_eq_bot]
      intro hbot
      rw [hbot, Subgroup.card_bot] at hcard
      rcases Nat.pow_eq_one.mp hcard.symm with h | h
      · exact (Fact.out : p.Prime).one_lt.ne' h
      · omega
    have hQ := demushkinQ_of_not_isMulTorsionFree hG hne
    refine ⟨isCyclic_torsion_of_mulEquiv isAddTorsion_of_finite e.toMulEquiv, ?_, ?_⟩
    · rw [hQ, hcard, hval, pow_add, pow_one]
      exact dvd_mul_right p _
    · rw [hQ, hcard, Nat.cast_pow, ← PadicInt.span_singleton_eq_span_pow_valuation hq]
      exact ⟨e⟩

/-- **The torsion subgroup of the abelianization of a Demushkin group is finite**: the
abelianization is a topologically finitely generated abelian pro-`p` group. -/
theorem finite_torsion_topologicalAbelianization : Finite (torsion (TopologicalAbelianization G)) :=
  hG.isProP.topologicalAbelianization_self.finite_torsion
    (hG.isTopologicallyFinitelyGenerated.quotient _)

/-- **The torsion subgroup of the abelianization of a Demushkin group is cyclic.** -/
theorem isCyclic_torsion_topologicalAbelianization :
    IsCyclic (torsion (TopologicalAbelianization G)) :=
  hG.torsion_spec.1

/-- **The `q`-invariant of a Demushkin group is divisible by `p`**, because the relator of a
minimal presentation lies in the Frattini subgroup. -/
theorem prime_dvd_demushkinQ : p ∣ demushkinQ hG :=
  hG.torsion_spec.2.1

/-- **The abelianization structure theorem for Demushkin groups** (Labute, p. 106): for a Demushkin
group `G` of rank `n` with `q`-invariant `q`,

`G^{ab} ≃ₜ* ℤ_p^{n-1} × ℤ_p ⧸ q ℤ_p`

as topological groups. When `q = 0` the second factor is `ℤ_p` and `G^{ab} ≅ ℤ_p^n` is torsion-free;
otherwise it is the cyclic group of order `q`, which is the torsion subgroup of `G^{ab}`. -/
theorem nonempty_continuousMulEquiv_topologicalAbelianization :
    Nonempty (TopologicalAbelianization G ≃ₜ*
      Multiplicative ((Fin (demushkinRank hG - 1) → ℤ_[p]) ×
        (ℤ_[p] ⧸ Ideal.span {(demushkinQ hG : ℤ_[p])}))) :=
  hG.torsion_spec.2.2

end IsDemushkin

/-- **The `q`-invariant vanishes exactly when the abelianization is torsion-free.** -/
@[simp]
theorem demushkinQ_eq_zero_iff :
    demushkinQ hG = 0 ↔ IsMulTorsionFree (TopologicalAbelianization G) := by
  refine ⟨fun h ↦ by_contra fun hne ↦ ?_, demushkinQ_of_isMulTorsionFree hG⟩
  rw [demushkinQ_of_not_isMulTorsionFree hG hne] at h
  have := hG.finite_torsion_topologicalAbelianization
  exact Nat.card_pos.ne' h

end TauCeti
