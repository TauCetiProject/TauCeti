/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.LastArrow
public import TauCeti.RepresentationTheory.Quiver.Preprojective.Signless

/-!
# Bipartiteness and the signless preprojective relation

The local preprojective relator of a finite quiver `Q` at a vertex `v` carries a sign,

```text
ρ_v = ∑_{head a = v} a a* - ∑_{tail a = v} a* a,
```

whereas the signless relator `s_v = ∑_{head a = v} a a* + ∑_{tail a = v} a* a` of the doubled
quiver `Quiver.Symmetrify Q` — the relation which appears in the quadratic dual of a zigzag
algebra — carries none. Rescaling the arrows of `Q` by scalars `ε` replaces `ρ` by the gauged
relator `ρ_ε`, and for a *bipartite* `Q` the colour signs make the corner of `ρ_ε` at every vertex
a multiple of `s_v`, by `TauCeti.gaugedPreprojectiveRelator_bipartite_vertexCorner_eq_smul`.

This file proves the obstruction supplied by an odd closed walk. The backtracks at a fixed vertex
are distinct basis paths, so the corner equation `e_v ρ_ε e_v = c_v • s_v` reads off the gauge:
`ε_a` is the scalar `c` at the head of `a`, and `-c` at its tail. Hence `c` changes sign along
every arrow, is a unit as soon as `ε` is, and a closed walk of odd length in the doubled quiver
forces `2 = 0` in the coefficient ring. A loop is the smallest such walk.

Over a coefficient ring in which `2 = 0` the sign is invisible: the signless and the preprojective
local relators are then the same element, the two relation ideals coincide, and the signless
algebra is the preprojective algebra.

## Main results

* `TauCeti.gaugedPreprojectiveRelator_vertexCorner_eq_sum_sub_sum`: the corner of the gauged
  relator at a vertex.
* `TauCeti.gauge_eq_of_vertexCorner_eq_smul`: a cornerwise comparison with the signless relator
  reads off the gauge at every arrow meeting that vertex.
* `TauCeti.eq_neg_of_forall_vertexCorner_eq_smul`: the comparison scalars change sign along every
  arrow.
* `TauCeti.not_exists_forall_vertexCorner_eq_smul_of_odd_length`: **no unit gauge compares the
  preprojective relation cornerwise with the signless one when the doubled quiver carries a closed
  walk of odd length**, unless `2 = 0`.
* `TauCeti.signlessPreprojectiveIdeal_eq_preprojectiveIdeal_of_two_eq_zero` and
  `TauCeti.signlessPreprojectiveAlgebraEquivPreprojectiveOfTwoEqZero`: **in characteristic two the
  signless and the preprojective relations agree**, for every finite quiver.

## References

S. Huerfano and M. Khovanov, *A category for the adjoint representation*, Section 3,
https://arxiv.org/abs/math/0002060, for the signless relation of the quadratic dual of a zigzag
algebra and its comparison with the preprojective relation of a bipartite graph. The preprojective
conventions follow Crawley-Boevey, *Quiver algebras, weighted projective lines, and the
Deligne--Simpson problem*, Section 1.
-/

public section

namespace TauCeti

open _root_.Quiver PathAlgebra

universe u v w

/-! ### The corner of the gauged relator -/

section Corner

variable (k : Type w) {Q : Type u} [CommRing k] [Quiver.{v + 1} Q] [Fintype Q]
  [∀ i j : Q, Fintype (i ⟶ j)]

/-- **The corner of the gauged preprojective relator at a vertex**: conjugating `ρ_ε` by the
idempotent at `v` keeps the weighted head backtracks of the arrows into `v` and the weighted tail
backtracks of the arrows out of `v`. For the constant gauge this is
`TauCeti.preprojectiveRelator_vertexCorner_eq_localPreprojectiveRelator`. -/
theorem gaugedPreprojectiveRelator_vertexCorner_eq_sum_sub_sum
    (ε : ∀ ⦃i j : Q⦄, (i ⟶ j) → k) (v : Q) :
    doubledVertexIdempotent k v * gaugedPreprojectiveRelator k ε *
        doubledVertexIdempotent k v
      = (∑ i : Q, ∑ a : (i ⟶ v), ε a • headBacktrackElem k a) -
          ∑ j : Q, ∑ a : (v ⟶ j), ε a • tailBacktrackElem k a := by
  classical
  have key : ∀ (i j : Q) (a : i ⟶ j),
      doubledVertexIdempotent k v * (ε a • (headBacktrackElem k a - tailBacktrackElem k a)) *
          doubledVertexIdempotent k v
        = (if j = v then ε a • headBacktrackElem k a else 0) -
            if i = v then ε a • tailBacktrackElem k a else 0 := by
    intro i j a
    rw [mul_smul_comm, smul_mul_assoc, mul_sub, sub_mul, smul_sub]
    congr 1
    · by_cases h : j = v
      · subst h
        simp [doubledVertexIdempotent_mul_headBacktrackElem,
          headBacktrackElem_mul_doubledVertexIdempotent]
      · simp [h, doubledVertexIdempotent_mul_headBacktrackElem_of_ne k a (Ne.symm h)]
    · by_cases h : i = v
      · subst h
        simp [doubledVertexIdempotent_mul_tailBacktrackElem,
          tailBacktrackElem_mul_doubledVertexIdempotent]
      · simp [h, doubledVertexIdempotent_mul_tailBacktrackElem_of_ne k a (Ne.symm h)]
  rw [gaugedPreprojectiveRelator_def]
  simp only [Finset.mul_sum, Finset.sum_mul, key, Finset.sum_sub_distrib]
  congr 1
  · -- At each tail vertex `i`, only the arrows whose head is `v` survive.
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_eq_single v]
    · exact Finset.sum_congr rfl fun a _ => by simp
    · exact fun j _ hj => Finset.sum_eq_zero fun a _ => by simp [hj]
    · exact fun h => absurd (Finset.mem_univ v) h
  · -- Only the arrows whose tail is `v` survive, and their heads range over all vertices.
    rw [Finset.sum_eq_single v]
    · exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun a _ => by simp
    · exact fun i _ hi => Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun a _ => by simp [hi]
    · exact fun h => absurd (Finset.mem_univ v) h

end Corner

/-! ### Reading off the gauge -/

section Gauge

variable (k : Type w) {Q : Type u} [CommRing k] [Quiver.{v + 1} Q] [Fintype Q]
  [∀ i j : Q, Fintype (i ⟶ j)]

/-- **A cornerwise comparison of the gauged relator with the signless relator reads off the
gauge.** If the corner of `ρ_ε` at `v` is the multiple `c • s_v` of the signless relator, then `ε`
is `c` on every arrow into `v` and `-c` on every arrow out of `v`. -/
theorem gauge_eq_of_vertexCorner_eq_smul (ε : ∀ ⦃i j : Q⦄, (i ⟶ j) → k) {v : Q} {c : k}
    (hv : doubledVertexIdempotent k v * gaugedPreprojectiveRelator k ε *
        doubledVertexIdempotent k v
      = c • signlessPreprojectiveRelator k (Symmetrify.of.obj v)) :
    (∀ (i : Q) (a : i ⟶ v), ε a = c) ∧ ∀ (j : Q) (a : v ⟶ j), ε a = -c := by
  classical
  have hsum : (∑ i : Q, ∑ a : (i ⟶ v), headBacktrackElem k a) +
      ∑ j : Q, ∑ a : (v ⟶ j), tailBacktrackElem k a
      = signlessPreprojectiveRelator k (Symmetrify.of.obj v) :=
    (signlessPreprojectiveRelator_of k v).symm
  rw [gaugedPreprojectiveRelator_vertexCorner_eq_sum_sub_sum, ← hsum, smul_add] at hv
  have hzero := (Fintype.linearIndependent_iff.1 (linearIndependent_backtrackElem k v))
    (Sum.elim (fun x : Σ i : Q, (i ⟶ v) => ε x.2 - c)
      (fun x : Σ j : Q, (v ⟶ j) => -ε x.2 - c)) ?_
  · refine ⟨fun i a => ?_, fun j a => ?_⟩
    · simpa [sub_eq_zero] using hzero (Sum.inl ⟨i, a⟩)
    · have h := hzero (Sum.inr ⟨j, a⟩)
      simp only [Sum.elim_inr, sub_eq_zero] at h
      rw [← h, neg_neg]
  · rw [Fintype.sum_sum_type, Fintype.sum_sigma, Fintype.sum_sigma]
    simp only [Sum.elim_inl, Sum.elim_inr, sub_smul, neg_smul, Finset.sum_sub_distrib,
      Finset.sum_neg_distrib, ← Finset.smul_sum]
    rw [← sub_eq_zero_of_eq hv]
    abel

/-- **The comparison scalars change sign along every arrow.** If the corner of the gauged relator
at every vertex is the corresponding multiple of the signless relator, then the scalars `c` of that
comparison satisfy `c j = -c i` for every arrow `a : i ⟶ j`. -/
theorem eq_neg_of_forall_vertexCorner_eq_smul (ε : ∀ ⦃i j : Q⦄, (i ⟶ j) → k) {c : Q → k}
    (hc : ∀ w : Q, doubledVertexIdempotent k w * gaugedPreprojectiveRelator k ε *
        doubledVertexIdempotent k w
      = c w • signlessPreprojectiveRelator k (Symmetrify.of.obj w))
    {i j : Q} (a : i ⟶ j) : c j = -c i := by
  rw [← (gauge_eq_of_vertexCorner_eq_smul k ε (hc j)).1 i a,
    (gauge_eq_of_vertexCorner_eq_smul k ε (hc i)).2 j a]

/-- **The comparison scalar at the head of an arrow is the gauge of that arrow**, hence a unit
whenever the gauge is. -/
theorem isUnit_of_forall_vertexCorner_eq_smul {ε : ∀ ⦃i j : Q⦄, (i ⟶ j) → k}
    (hε : ∀ ⦃i j : Q⦄ (a : i ⟶ j), IsUnit (ε a)) {c : Q → k}
    (hc : ∀ w : Q, doubledVertexIdempotent k w * gaugedPreprojectiveRelator k ε *
        doubledVertexIdempotent k w
      = c w • signlessPreprojectiveRelator k (Symmetrify.of.obj w))
    {i j : Q} (a : i ⟶ j) : IsUnit (c j) := by
  rw [← (gauge_eq_of_vertexCorner_eq_smul k ε (hc j)).1 i a]
  exact hε a

end Gauge

section Obstruction

variable (k : Type w) {Q : Type u} [CommRing k] [Quiver.{v + 1} Q] [Fintype Q]
  [∀ i j : Q, Fintype (i ⟶ j)]

/-- **A closed walk of odd length obstructs the signless comparison.** If the doubled quiver has a
closed walk of odd length at some vertex, then over a coefficient ring in which `2 ≠ 0` no unit
gauge `ε` makes the corner of `ρ_ε` at every vertex a multiple of the signless relator there.
This complements the positive bipartite comparison
`TauCeti.gaugedPreprojectiveRelator_bipartite_vertexCorner_eq_smul`. -/
theorem not_exists_forall_vertexCorner_eq_smul_of_odd_length {ε : ∀ ⦃i j : Q⦄, (i ⟶ j) → k}
    (hε : ∀ ⦃i j : Q⦄ (a : i ⟶ j), IsUnit (ε a)) (h2 : (2 : k) ≠ 0) {v : Q}
    (p : Quiver.Path (Symmetrify.of.obj v) (Symmetrify.of.obj v)) (hp : Odd p.length) :
    ¬ ∃ c : Q → k, ∀ w : Q, doubledVertexIdempotent k w * gaugedPreprojectiveRelator k ε *
        doubledVertexIdempotent k w
      = c w • signlessPreprojectiveRelator k (Symmetrify.of.obj w) := by
  rintro ⟨c, hc⟩
  -- An arrow of the doubled quiver negates `c`, whichever way it is oriented in `Q`.
  have hsym : ∀ ⦃i j : Symmetrify Q⦄, (i ⟶ j) → c j = -c i := by
    intro i j e
    cases e with
    | inl a => exact eq_neg_of_forall_vertexCorner_eq_smul k ε hc a
    | inr a => rw [eq_neg_of_forall_vertexCorner_eq_smul k ε hc a, neg_neg]
  -- The walk has length at least one, so `v` meets an arrow of `Q` and `c v` is a unit.
  have hunit : IsUnit (c v) := by
    obtain ⟨n, hn⟩ := hp
    cases p with
    | nil => simp at hn
    | cons q e =>
      cases e with
      | inl a => exact isUnit_of_forall_vertexCorner_eq_smul k hε hc a
      | inr a =>
        have hεa : ε a = -c v := (gauge_eq_of_vertexCorner_eq_smul k ε (hc v)).2 _ a
        exact (IsUnit.neg_iff (c v)).1 (hεa ▸ hε a)
  -- Going round the walk negates `c v`.
  have hround : c v = -c v := by
    have h := eq_neg_one_pow_mul_of_path k hsym p
    rwa [hp.neg_one_pow, neg_one_mul] at h
  have h2c : (2 : k) * c v = 0 := by
    rw [two_mul]
    nth_rewrite 2 [hround]
    rw [add_neg_cancel]
  exact h2 (hunit.mul_left_eq_zero.1 h2c)

/-- **A quiver with a loop admits no signless comparison.** A loop is a closed walk of length one
in the doubled quiver, so it obstructs the comparison over every coefficient ring in which
`2 ≠ 0`. -/
theorem not_exists_forall_vertexCorner_eq_smul_of_loop {ε : ∀ ⦃i j : Q⦄, (i ⟶ j) → k}
    (hε : ∀ ⦃i j : Q⦄ (a : i ⟶ j), IsUnit (ε a)) (h2 : (2 : k) ≠ 0) {v : Q} (a : v ⟶ v) :
    ¬ ∃ c : Q → k, ∀ w : Q, doubledVertexIdempotent k w * gaugedPreprojectiveRelator k ε *
        doubledVertexIdempotent k w
      = c w • signlessPreprojectiveRelator k (Symmetrify.of.obj w) :=
  not_exists_forall_vertexCorner_eq_smul_of_odd_length k hε h2
    (Quiver.Hom.toPath (Symmetrify.of.map a))
    ⟨0, rfl⟩

end Obstruction

/-! ### Characteristic two -/

section CharTwo

variable (k : Type w) {Q : Type u} [CommRing k] [Quiver.{v + 1} Q] [Fintype Q]
  [∀ i j : Q, Fintype (i ⟶ j)]

/-- **In characteristic two the signless relator is the preprojective relator.** The two differ
only in the sign of the tail backtracks. -/
theorem signlessPreprojectiveRelator_eq_localPreprojectiveRelator_of_two_eq_zero
    (h2 : (2 : k) = 0) (v : Q) :
    signlessPreprojectiveRelator k (Symmetrify.of.obj v) = localPreprojectiveRelator k v := by
  have hneg : ∀ z : pathAlgebra k (Symmetrify Q), -z = z := fun z =>
    neg_eq_of_add_eq_zero_left (by rw [← two_smul k z, h2, zero_smul])
  rw [signlessPreprojectiveRelator_of, localPreprojectiveRelator_def, sub_eq_add_neg, hneg]

/-- **In characteristic two the signless and the preprojective relation ideals coincide**, for
every finite quiver, bipartite or not. -/
theorem signlessPreprojectiveIdeal_eq_preprojectiveIdeal_of_two_eq_zero (h2 : (2 : k) = 0) :
    signlessPreprojectiveIdeal k (Symmetrify Q) = preprojectiveIdeal k Q := by
  rw [signlessPreprojectiveIdeal_eq_span,
    preprojectiveIdeal_eq_span_range_localPreprojectiveRelator]
  congr 1
  ext x
  simp only [Set.mem_range]
  constructor
  · rintro ⟨w, rfl⟩
    exact ⟨w, (signlessPreprojectiveRelator_eq_localPreprojectiveRelator_of_two_eq_zero
      (Q := Q) k h2 w).symm⟩
  · rintro ⟨w, rfl⟩
    exact ⟨w, signlessPreprojectiveRelator_eq_localPreprojectiveRelator_of_two_eq_zero
      (Q := Q) k h2 w⟩

/-- **In characteristic two the signless algebra of a doubled quiver is its preprojective
algebra**, by the identity of the doubled path algebra. -/
noncomputable def signlessPreprojectiveAlgebraEquivPreprojectiveOfTwoEqZero (h2 : (2 : k) = 0) :
    signlessPreprojectiveAlgebra k (Symmetrify Q) ≃ₐ[k] preprojectiveAlgebra k Q :=
  Ideal.quotientEquivAlgOfEq k (congrArg TwoSidedIdeal.asIdeal
    (signlessPreprojectiveIdeal_eq_preprojectiveIdeal_of_two_eq_zero k h2))

/-- The characteristic-two comparison is induced by the identity of the doubled path algebra. -/
@[simp]
theorem signlessPreprojectiveAlgebraEquivPreprojectiveOfTwoEqZero_signlessPreprojectiveMk
    (h2 : (2 : k) = 0) (x : pathAlgebra k (Symmetrify Q)) :
    signlessPreprojectiveAlgebraEquivPreprojectiveOfTwoEqZero k h2
        (signlessPreprojectiveMk k _ x) = preprojectiveMk k Q x := by
  rw [signlessPreprojectiveAlgebraEquivPreprojectiveOfTwoEqZero, signlessPreprojectiveMk_apply,
    Ideal.quotientEquivAlgOfEq_mk, preprojectiveMk_apply]

/-- The inverse of the characteristic-two comparison is also induced by the identity of the
doubled path algebra. -/
@[simp]
theorem signlessPreprojectiveAlgebraEquivPreprojectiveOfTwoEqZero_symm_preprojectiveMk
    (h2 : (2 : k) = 0) (x : pathAlgebra k (Symmetrify Q)) :
    (signlessPreprojectiveAlgebraEquivPreprojectiveOfTwoEqZero k h2).symm
        (preprojectiveMk k Q x) = signlessPreprojectiveMk k _ x := by
  apply (signlessPreprojectiveAlgebraEquivPreprojectiveOfTwoEqZero k h2).injective
  rw [AlgEquiv.apply_symm_apply,
    signlessPreprojectiveAlgebraEquivPreprojectiveOfTwoEqZero_signlessPreprojectiveMk]

end CharTwo

end TauCeti
