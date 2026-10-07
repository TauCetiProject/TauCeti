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
public import TauCeti.Topology.Algebra.Group.Profinite.Free.DegreeOneForm
public import TauCeti.Topology.Algebra.Group.Profinite.Presentation.Abelianization
import Mathlib.Topology.Algebra.Module.Equiv.Prod
import TauCeti.NumberTheory.Padics.PadicIntegers
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
* `TauCeti.IsDemushkin.exists_demushkinQ_eq_pow`: a nonzero `q(G)` is a positive power of `p`;
  `TauCeti.IsDemushkin.exists_two_le_demushkinQ_eq_pow_of_ne`: if moreover `q(G) ≠ p`, the
  exponent is at least `2`.
* `TauCeti.demushkinQ_congr`: the `q`-invariant is invariant under topological isomorphism.
* `TauCeti.isMulTorsionFree_topologicalAbelianization_of_mulEquiv`,
  `TauCeti.demushkinQ_eq_zero_of_mulEquiv`, `TauCeti.demushkinQ_eq_pow_valuation_of_mulEquiv`:
  the torsion of `G^{ab}` read off a model `G^{ab} ≅ ℤ_p^ι × ℤ_p ⧸ (q)` with `p ∣ q`: `G^{ab}` is
  torsion-free and `q(G) = 0` when `q = 0`, and `q(G) = p^{v_p(q)}` otherwise.
* `TauCeti.demushkinQ_presentedProP_eq_zero_iff`,
  `TauCeti.demushkinQ_presentedProP_eq_zero_iff_mem_topologicalClosure_commutator`,
  `TauCeti.demushkinQ_presentedProP_eq_pow_valuation`: for a Demushkin group given by a
  one-relator presentation `⟨X ∣ r⟩` with `exponentSum r = q • w`, `w x₀ = 1` and `p ∣ q`, the
  `q`-invariant is `0` exactly when `q = 0`, that is when `r` lies in the closed commutator
  subgroup, and is `p^{v_p(q)}` otherwise.
* `TauCeti.demushkinQ_presentedProP_eq_iff_exists_not_dvd`,
  `TauCeti.demushkinQ_presentedProP_eq_iff_exists_degreeOneBasis_repr_inl_ne_zero`: for a relator
  `r ∈ Φ(F)` presenting a Demushkin group, `q = p` exactly when some exponent sum of `r` is not
  divisible by `p ^ 2`, that is, when the class of `r` in `gr_1(F)` has a nonzero `p`-power
  coordinate.

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

/-! ### The `q`-invariant read off a model of the abelianization -/

section Model

variable {ι : Type*} {q : ℤ_[p]}
  (e : TopologicalAbelianization G ≃* Multiplicative ((ι → ℤ_[p]) × (ℤ_[p] ⧸ Ideal.span {q})))

include e in
/-- **The model with `q = 0` is torsion-free.** If `G^{ab} ≅ ℤ_p^ι × ℤ_p ⧸ (q)` with `q = 0`, then
`G^{ab}` is torsion-free. -/
theorem isMulTorsionFree_topologicalAbelianization_of_mulEquiv (hq : q = 0) :
    IsMulTorsionFree (TopologicalAbelianization G) := by
  subst hq
  have : IsAddTorsionFree (ℤ_[p] ⧸ Ideal.span {(0 : ℤ_[p])}) := by
    rw [Ideal.span_singleton_zero]
    exact (RingEquiv.quotientBot ℤ_[p]).injective.isAddTorsionFree
      (RingEquiv.quotientBot ℤ_[p]).toAddMonoidHom
  exact Function.Injective.isMulTorsionFree e.toMonoidHom e.injective

include e in
/-- **The `q`-invariant vanishes on the torsion-free model.** If `G^{ab} ≅ ℤ_p^ι × ℤ_p ⧸ (q)` with
`q = 0`, then `q(G) = 0`. -/
theorem demushkinQ_eq_zero_of_mulEquiv (hq : q = 0) : demushkinQ hG = 0 :=
  demushkinQ_of_isMulTorsionFree hG (isMulTorsionFree_topologicalAbelianization_of_mulEquiv e hq)

include e in
/-- **The `q`-invariant is `p^{v_p(q)}` on the model with torsion.** If
`G^{ab} ≅ ℤ_p^ι × ℤ_p ⧸ (q)` with `q ≠ 0` divisible by `p`, then the torsion subgroup of `G^{ab}`
is the cyclic group `ℤ_p ⧸ (q)` of order `p^{v_p(q)}`, and that order is `q(G)`. -/
theorem demushkinQ_eq_pow_valuation_of_mulEquiv (hpq : (p : ℤ_[p]) ∣ q) (hq : q ≠ 0) :
    demushkinQ hG = p ^ q.valuation := by
  have := PadicInt.finite_quotient_span hq
  have hcard : Nat.card (torsion (TopologicalAbelianization G)) = p ^ q.valuation := by
    rw [natCard_torsion_of_mulEquiv isAddTorsion_of_finite e, PadicInt.natCard_quotient_span hq]
  have hne : ¬ IsMulTorsionFree (TopologicalAbelianization G) := by
    rw [CommGroup.isMulTorsionFree_iff_torsion_eq_bot]
    intro hbot
    rw [hbot, Subgroup.card_bot] at hcard
    exact (Fact.out : p.Prime).ne_one (Nat.dvd_one.1 (hcard ▸ dvd_pow_self p
      (Nat.one_le_iff_ne_zero.1 (PadicInt.one_le_valuation_of_dvd hq hpq))))
  rw [demushkinQ_of_not_isMulTorsionFree hG hne, hcard]

end Model

variable [CompactSpace G] [TotallyDisconnectedSpace G]

include hG in
/-- **The torsion subgroup of the abelianization of a Demushkin group is finite**: the
abelianization is a topologically finitely generated abelian pro-`p` group. -/
theorem IsDemushkin.finite_torsion_topologicalAbelianization :
    Finite (torsion (TopologicalAbelianization G)) :=
  hG.isProP.topologicalAbelianization_self.finite_torsion
    (hG.isTopologicallyFinitelyGenerated.quotient _)

/-- **The `q`-invariant vanishes exactly when the abelianization is torsion-free.** -/
@[simp]
theorem demushkinQ_eq_zero_iff :
    demushkinQ hG = 0 ↔ IsMulTorsionFree (TopologicalAbelianization G) := by
  refine ⟨fun h ↦ by_contra fun hne ↦ ?_, demushkinQ_of_isMulTorsionFree hG⟩
  rw [demushkinQ_of_not_isMulTorsionFree hG hne] at h
  have := hG.finite_torsion_topologicalAbelianization
  exact Nat.card_pos.ne' h

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
    have hfree := isMulTorsionFree_topologicalAbelianization_of_mulEquiv e.toMulEquiv rfl
    have h0 := demushkinQ_of_isMulTorsionFree hG hfree
    have hbot := CommGroup.isMulTorsionFree_iff_torsion_eq_bot.1 hfree
    refine ⟨by rw [hbot]; infer_instance, h0 ▸ dvd_zero p, ?_⟩
    rw [h0, Nat.cast_zero]
    exact ⟨e⟩
  · -- `q ≠ 0`: the torsion subgroup is `ℤ_p ⧸ (q)`, of order `p ^ v_p(q)` with `v_p(q) ≥ 1`.
    have := PadicInt.finite_quotient_span hq
    have := PadicInt.isAddCyclic_quotient_span hq
    have hQ := demushkinQ_eq_pow_valuation_of_mulEquiv hG e.toMulEquiv hpq hq
    refine ⟨isCyclic_torsion_of_mulEquiv isAddTorsion_of_finite e.toMulEquiv, ?_, ?_⟩
    · rw [hQ]
      exact dvd_pow_self p (Nat.one_le_iff_ne_zero.1 (PadicInt.one_le_valuation_of_dvd hq hpq))
    · rw [hQ, Nat.cast_pow, ← PadicInt.span_singleton_eq_span_pow_valuation hq]
      exact ⟨e⟩

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

/-- **A nonzero `q`-invariant is a positive power of `p`**: it is the order of the finite cyclic
`p`-group `ℤ_p ⧸ (q)`, the torsion subgroup of the abelianization. -/
theorem exists_demushkinQ_eq_pow (hq : demushkinQ hG ≠ 0) :
    ∃ k, 0 < k ∧ demushkinQ hG = p ^ k := by
  obtain ⟨e⟩ := hG.nonempty_continuousMulEquiv_topologicalAbelianization
  have hq' : (demushkinQ hG : ℤ_[p]) ≠ 0 := by exact_mod_cast hq
  have := PadicInt.finite_quotient_span hq'
  have hcard : demushkinQ hG = p ^ (demushkinQ hG : ℤ_[p]).valuation := by
    conv_lhs => rw [demushkinQ_of_not_isMulTorsionFree hG
      fun h ↦ hq (demushkinQ_of_isMulTorsionFree hG h)]
    rw [natCard_torsion_of_mulEquiv isAddTorsion_of_finite e.toMulEquiv,
      PadicInt.natCard_quotient_span hq']
  refine ⟨_, Nat.pos_of_ne_zero fun h0 ↦ ?_, hcard⟩
  rw [h0, pow_zero] at hcard
  exact (Fact.out : p.Prime).one_lt.ne' (Nat.dvd_one.mp (hcard ▸ hG.prime_dvd_demushkinQ))

/-- **A `q`-invariant other than `0` and `p` is `p ^ k` with `k ≥ 2`.** -/
theorem exists_two_le_demushkinQ_eq_pow_of_ne (hq0 : demushkinQ hG ≠ 0)
    (hqp : demushkinQ hG ≠ p) : ∃ k, 2 ≤ k ∧ demushkinQ hG = p ^ k := by
  obtain ⟨k, hk, hqk⟩ := hG.exists_demushkinQ_eq_pow hq0
  refine ⟨k, ?_, hqk⟩
  by_contra hlt
  have hk1 : k = 1 := by omega
  exact hqp (by rw [hqk, hk1, pow_one])

end IsDemushkin

/-! ### One-relator presentations

For a Demushkin group given by a one-relator presentation `⟨X ∣ r⟩`, the `q`-invariant is read off
the exponent vector `exponentSum r = q • w`, `w x₀ = 1`, of the relator, through the one-relator
abelianization structure theorem `TauCeti.presentedProP.oneRelatorAbelianizationEquiv`: it is `0`
when `q = 0`, that is when `r` lies in the closed commutator subgroup, and `p^{v_p(q)}` otherwise.
The hypothesis `p ∣ q` is not decoration: the presentation need not be minimal, and a relator with
a unit coordinate, such as `x₃ (x₁, x₂)` presenting `ℤ_p × ℤ_p`, has `q(G) = 0` while `ℤ_p ⧸ (q)`
is trivial. -/

section OneRelator

variable {X : Type u} [Finite X] {r : freeProP p X} {x₀ : X} {w : X → ℤ_[p]} {q : ℤ_[p]}
  (hw : w x₀ = 1) (hr : (freeProP.exponentSum p X r).toAdd = q • w)

include hw hr in
/-- **The `q`-invariant of a one-relator Demushkin group vanishes exactly when the exponent
coordinate `q` of its relator does**, for `p ∣ q`. -/
theorem demushkinQ_presentedProP_eq_zero_iff (hG : IsDemushkin p (presentedProP p X {r}))
    (hpq : (p : ℤ_[p]) ∣ q) : demushkinQ hG = 0 ↔ q = 0 := by
  refine ⟨fun h ↦ by_contra fun hq ↦ ?_, demushkinQ_eq_zero_of_mulEquiv hG
    (presentedProP.oneRelatorAbelianizationEquiv r x₀ w hw q hr).toMulEquiv⟩
  rw [demushkinQ_eq_pow_valuation_of_mulEquiv hG
    (presentedProP.oneRelatorAbelianizationEquiv r x₀ w hw q hr).toMulEquiv hpq hq] at h
  exact pow_ne_zero _ (Fact.out : p.Prime).ne_zero h

include hw hr in
/-- **The `q`-invariant of a one-relator Demushkin group vanishes exactly when the relator lies in
the closed commutator subgroup** of the free pro-`p` group, for `p ∣ q`. -/
theorem demushkinQ_presentedProP_eq_zero_iff_mem_topologicalClosure_commutator
    (hG : IsDemushkin p (presentedProP p X {r})) (hpq : (p : ℤ_[p]) ∣ q) :
    demushkinQ hG = 0 ↔ r ∈ (commutator (freeProP p X)).topologicalClosure := by
  rw [demushkinQ_presentedProP_eq_zero_iff hw hr hG hpq,
    presentedProP.oneRelator_q_eq_zero_iff_mem_topologicalClosure_commutator r x₀ w hw q hr]

include hw hr in
/-- **The `q`-invariant of a one-relator Demushkin group is `p^{v_p(q)}`** for the exponent
coordinate `q ≠ 0` of its relator, `p ∣ q`: the torsion subgroup of `G^{ab}` is `ℤ_p ⧸ (q)`. -/
theorem demushkinQ_presentedProP_eq_pow_valuation (hG : IsDemushkin p (presentedProP p X {r}))
    (hpq : (p : ℤ_[p]) ∣ q) (hq : q ≠ 0) : demushkinQ hG = p ^ q.valuation :=
  demushkinQ_eq_pow_valuation_of_mulEquiv hG
    (presentedProP.oneRelatorAbelianizationEquiv r x₀ w hw q hr).toMulEquiv hpq hq

/-- **The `q`-invariant of a one-relator Demushkin group is `p` exactly when some exponent sum of
the relator is not divisible by `p ^ 2`**, for a relator all of whose exponent sums are divisible
by `p`, as they are for a relator in `Φ(F)`. Writing the exponent vector as `q • w` with a
coordinate `w x₀ = 1`, the `q`-invariant is `p^{v_p(q)}`, and it is `p` exactly when
`v_p(q) = 1`. -/
theorem demushkinQ_presentedProP_eq_iff_exists_not_dvd (hG : IsDemushkin p (presentedProP p X {r}))
    (hpr : ∀ x, (p : ℤ_[p]) ∣ (freeProP.exponentSum p X r).toAdd x) :
    demushkinQ hG = p ↔ ∃ x, ¬ (p : ℤ_[p]) ^ 2 ∣ (freeProP.exponentSum p X r).toAdd x := by
  have hp : p.Prime := Fact.out
  have : Nonempty X := (Nat.card_pos_iff.1 hG.card_pos_presentedProP).1
  obtain ⟨x₀, q, w, hw, hv⟩ :=
    PadicInt.exists_apply_eq_one_and_eq_smul (freeProP.exponentSum p X r).toAdd
  have hqx₀ : (freeProP.exponentSum p X r).toAdd x₀ = q := by
    rw [hv, Pi.smul_apply, hw, smul_eq_mul, mul_one]
  have hq : (p : ℤ_[p]) ∣ q := hqx₀ ▸ hpr x₀
  -- Some exponent sum escapes `p ^ 2` exactly when `q` does.
  have hiff : (∃ x, ¬ (p : ℤ_[p]) ^ 2 ∣ (freeProP.exponentSum p X r).toAdd x) ↔
      ¬ (p : ℤ_[p]) ^ 2 ∣ q := by
    refine ⟨fun ⟨x, hx⟩ h ↦ hx ?_, fun h ↦ ⟨x₀, hqx₀ ▸ h⟩⟩
    rw [hv, Pi.smul_apply, smul_eq_mul]
    exact h.mul_right _
  rw [hiff]
  by_cases hq0 : q = 0
  · rw [(demushkinQ_presentedProP_eq_zero_iff hw hv hG hq).2 hq0, hq0]
    exact ⟨fun h ↦ absurd h.symm hp.ne_zero, fun h ↦ absurd (dvd_zero _) h⟩
  rw [demushkinQ_presentedProP_eq_pow_valuation hw hv hG hq hq0, ← Ideal.mem_span_singleton,
    PadicInt.mem_span_pow_iff_le_valuation q hq0, not_le]
  have h1 : 1 ≤ q.valuation := by
    rw [← PadicInt.mem_span_pow_iff_le_valuation q hq0, Ideal.mem_span_singleton, pow_one]
    exact hq
  constructor
  · intro h
    have := Nat.pow_right_injective hp.two_le (h.trans (pow_one p).symm)
    omega
  · intro h
    -- `p ∣ q` and `¬ p ^ 2 ∣ q` pin the valuation of `q` to `1`.
    have hval : q.valuation = 1 := by omega
    rw [hval, pow_one]

section DegreeOne

-- Preferring the ring path keeps a single additive structure on `ZMod p`, so that the coordinate
-- statement below is stated over the module structure of `ZMod p` on itself.
attribute [local instance 2000] Ring.toAddCommGroup

variable [LinearOrder X]

/-- **The `q`-invariant is `p` exactly when the relator has a `p`-power part.** For a relator
`r ∈ Φ(F)` presenting a Demushkin group, the `q`-invariant of the group is `p` exactly when the
class of `r` in `gr_1(F)` has a nonzero `p`-power coordinate, that is, when some exponent sum of
`r` is not divisible by `p ^ 2`. -/
theorem demushkinQ_presentedProP_eq_iff_exists_degreeOneBasis_repr_inl_ne_zero
    (hr : r ∈ proPFrattini p (freeProP p X)) (hG : IsDemushkin p (presentedProP p X {r})) :
    demushkinQ hG = p ↔ ∃ i, (freeProP.degreeOneBasis p X).repr (gradedMk p (freeProP p X) 1
      ⟨r, (pLowerCentralSeries_one_eq_proPFrattini Fact.out).symm.le hr⟩) (Sum.inl i) ≠ 0 := by
  rw [demushkinQ_presentedProP_eq_iff_exists_not_dvd hG
    (freeProP.dvd_exponentSum_of_mem_proPFrattini p X hr)]
  simp only [ne_eq, freeProP.degreeOneBasis_repr_gradedMk_inl_eq_zero_iff]

end DegreeOne

end OneRelator

end TauCeti
