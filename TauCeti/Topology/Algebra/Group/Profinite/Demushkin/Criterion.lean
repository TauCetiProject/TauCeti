/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.Profinite.Demushkin.Basic
public import TauCeti.Topology.Algebra.Group.Profinite.Free.RelatorFunctional

/-!
# Labute's criterion: the one-relator pro-`p` groups that are Demushkin

Let `F = freeProP p X` be the free pro-`p` group on a finite type `X`, let `r ∈ Φ(F)` be a relator
in its pro-`p` Frattini subgroup, and let `G ≅ ⟨X ∣ r⟩ = F ⧸ ⟪r⟫` be the one-relator pro-`p` group
it presents, a minimal presentation. The relator functional `TauCeti.freeProP.relatorFunctional`
of `r` is injective on `H²(G, 𝔽_p)` and sends the cup product `a ⌣ b` of two classes of
`H¹(G, 𝔽_p)` to minus the degree-one form `TauCeti.freeProP.degreeOneForm` of the class
`⟦r⟧ ∈ gr_1(F)`, evaluated at the characters of `F` attached to `a` and `b`. Since every
`𝔽_p`-character of `F` kills `Φ(F) ⊇ ⟪r⟫`, the characters of `G` are exactly the characters of `F`,
and the cup form of `G` on `H¹(G, 𝔽_p)` is, up to sign, the degree-one form of `⟦r⟧` on the
continuous dual of `F`: the cup product `a ⌣ b` vanishes exactly when `B_{⟦r⟧}(χ_a, χ_b)` does
(`TauCeti.freeProP.cupFp_eq_zero_iff_degreeOneForm_eq_zero`).

**Labute's criterion** follows: `G` is a Demushkin group exactly when `X` is nonempty and the
degree-one form of `⟦r⟧` is nondegenerate (`TauCeti.isDemushkin_iff_nondegenerate_degreeOneForm`),
and the cup form is alternating exactly when the degree-one form is
(`TauCeti.freeProP.isAlt_degreeOneForm_iff_forall_cupFp_self_eq_zero`). The consequences for the
relator of a Demushkin group, Labute's normal forms modulo `λ_2(F)`, are drawn in
`TauCeti.Topology.Algebra.Group.Profinite.Demushkin.NormalForm.Criterion`.

## Main results

* `TauCeti.freeProP.cupFp_eq_zero_iff_degreeOneForm_eq_zero`: the cup product of two classes of
  `H¹(G, 𝔽_p)` vanishes exactly when the degree-one form of the relator class vanishes at the
  attached characters of `F`.
* `TauCeti.freeProP.isAlt_degreeOneForm_iff_forall_cupFp_self_eq_zero`: the degree-one form of the
  relator class is alternating exactly when every cup square `a ⌣ a` on `H¹(G, 𝔽_p)` vanishes.
* `TauCeti.IsDemushkin.nondegenerate_degreeOneForm`,
  `TauCeti.isDemushkin_of_nondegenerate_degreeOneForm`,
  `TauCeti.isDemushkin_iff_nondegenerate_degreeOneForm`: **Labute's criterion**, a one-relator
  pro-`p` group `⟨X ∣ r⟩` with `r ∈ Φ(F)` is Demushkin exactly when `X` is nonempty and the
  degree-one form of `⟦r⟧` is nondegenerate.

## References

* J. P. Labute, *Classification of Demushkin groups*, Canad. J. Math. 19 (1967), 106–132, §3,
  Proposition 3.
* J.-P. Serre, *Galois Cohomology*, Chapter I, §4.5.
* J. Neukirch, A. Schmidt and K. Wingberg, *Cohomology of Number Fields*, 2nd ed., Chapter III, §9.
-/

public section

namespace TauCeti

open Subgroup

universe u v

-- Preferring the ring path keeps a single additive structure on `ZMod p`, so that the bilinear
-- forms below are stated over the module structure of `ZMod p` on itself.
attribute [local instance 2000] Ring.toAddCommGroup

variable {p : ℕ} [Fact p.Prime] {X : Type u} [Finite X] {r : freeProP p X}
  {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G]
  (hr : r ∈ proPFrattini p (freeProP p X)) (e : presentedProP p X {r} ≃ₜ* G)

omit [Fact p.Prime] [Finite X] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G] in
include hr in
/-- The closed normal closure of a relator in the Frattini subgroup lies in the Frattini
subgroup. -/
private theorem topologicalClosure_normalClosure_singleton_le_proPFrattini :
    (normalClosure {r}).topologicalClosure ≤ proPFrattini p (freeProP p X) :=
  (topologicalClosure_normalClosure_le_iff isClosed_proPFrattini).2 (Set.singleton_subset_iff.2 hr)

omit [Finite X] [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] in
include hr in
/-- Precomposition with `F → ⟨X ∣ r⟩ ≃ G` is a bijection from the continuous `𝔽_p`-dual of `G` onto
that of `F`, because `⟪r⟫ ≤ Φ(F)`. -/
private theorem dualMap_bijective :
    Function.Bijective (((e : presentedProP p X {r} →ₜ* G).comp
      (ContinuousMonoidHom.quotientMk
        (normalClosure {r}).topologicalClosure)).continuousZModDualMap (n := p)) := by
  rw [ContinuousMonoidHom.continuousZModDualMap_comp, LinearMap.coe_comp]
  exact (continuousZModDualMap_quotientMk_bijective
    (topologicalClosure_normalClosure_singleton_le_proPFrattini hr)).comp
    e.continuousZModDualMap_bijective

include hr e

namespace freeProP

omit [TotallyDisconnectedSpace G] in
/-- **The cup form of a one-relator pro-`p` group is the degree-one form of its relator.** Let `F`
be the free pro-`p` group on a finite type `X`, let `r ∈ Φ(F)`, and let `G ≅ ⟨X ∣ r⟩`. The cup
product `a ⌣ b` of two classes of `H¹(G, 𝔽_p)` vanishes exactly when the degree-one form of the
class of `r` in `gr_1(F)` vanishes at the characters of `F` obtained from `a` and `b` by composing
with `F → G`. -/
theorem cupFp_eq_zero_iff_degreeOneForm_eq_zero (a b : cohomFp p G 1) :
    cupFp p G a b = 0 ↔
      degreeOneForm (gradedMk p (freeProP p X) 1
          ⟨r, (pLowerCentralSeries_one_eq_proPFrattini Fact.out).symm.le hr⟩)
        (((e : presentedProP p X {r} →ₜ* G).comp (ContinuousMonoidHom.quotientMk
          (normalClosure {r}).topologicalClosure)).continuousZModDualMap
            (cohomFpLinearEquivContinuousZModDual p G a))
        (((e : presentedProP p X {r} →ₜ* G).comp (ContinuousMonoidHom.quotientMk
          (normalClosure {r}).topologicalClosure)).continuousZModDualMap
            (cohomFpLinearEquivContinuousZModDual p G b)) = 0 := by
  rw [← map_eq_zero_iff _ (relatorFunctional_injective (isClosed_topologicalClosure _)
    (topologicalClosure_normalClosure_singleton_le_proPFrattini hr) e
    ⟨r, le_topologicalClosure _ (subset_normalClosure (Set.mem_singleton r))⟩ rfl),
    relatorFunctional_cupFp, neg_eq_zero]

omit [TotallyDisconnectedSpace G] in
/-- **The cup form is alternating exactly when the degree-one form of the relator is.** For
`G ≅ ⟨X ∣ r⟩` with `r ∈ Φ(F)`, the degree-one form of the class of `r` in `gr_1(F)` is alternating
exactly when every cup square `a ⌣ a` on `H¹(G, 𝔽_p)` vanishes. -/
theorem isAlt_degreeOneForm_iff_forall_cupFp_self_eq_zero :
    (degreeOneForm (gradedMk p (freeProP p X) 1
        ⟨r, (pLowerCentralSeries_one_eq_proPFrattini Fact.out).symm.le hr⟩)).IsAlt ↔
      ∀ a : cohomFp p G 1, cupFp p G a a = 0 := by
  refine ⟨fun h a ↦ (cupFp_eq_zero_iff_degreeOneForm_eq_zero hr e a a).2 (h.self_eq_zero _),
    fun h χ ↦ ?_⟩
  obtain ⟨a', rfl⟩ := (dualMap_bijective hr e).2 χ
  obtain ⟨a, rfl⟩ := (cohomFpLinearEquivContinuousZModDual p G).surjective a'
  exact (cupFp_eq_zero_iff_degreeOneForm_eq_zero hr e a a).1 (h a)

end freeProP

open freeProP

omit [TotallyDisconnectedSpace G] in
/-- **The relator of a Demushkin group has nondegenerate degree-one form** (Labute,
Proposition 3). Let `G ≅ ⟨X ∣ r⟩` with `r ∈ Φ(F)` be a Demushkin group. Then the degree-one form
of the class of `r` in `gr_1(F)` is nondegenerate: it is the cup form of `G` up to sign, and the
cup form of a Demushkin group is nondegenerate. -/
theorem IsDemushkin.nondegenerate_degreeOneForm (hG : IsDemushkin p G) :
    (degreeOneForm (gradedMk p (freeProP p X) 1
      ⟨r, (pLowerCentralSeries_one_eq_proPFrattini Fact.out).symm.le hr⟩)).Nondegenerate := by
  refine (LinearMap.IsRefl.nondegenerate_iff_separatingLeft (isRefl_degreeOneForm
    (gradedMk p (freeProP p X) 1
      ⟨r, (pLowerCentralSeries_one_eq_proPFrattini Fact.out).symm.le hr⟩))).2 fun χ hχ ↦ ?_
  obtain ⟨a', rfl⟩ := (dualMap_bijective hr e).2 χ
  obtain ⟨a, rfl⟩ := (cohomFpLinearEquivContinuousZModDual p G).surjective a'
  by_contra hne
  have ha : a ≠ 0 := fun h ↦ hne (by rw [h, map_zero, map_zero])
  obtain ⟨b, hb⟩ := hG.cup_separatingLeft a ha
  exact hb ((cupFp_eq_zero_iff_degreeOneForm_eq_zero hr e a b).2 (hχ _))

/-- **Labute's criterion, sufficiency.** Let `F` be the free pro-`p` group on a nonempty finite type
`X`, let `r ∈ Φ(F)`, and suppose the degree-one form of the class of `r` in `gr_1(F)` is
nondegenerate. Then `G ≅ ⟨X ∣ r⟩` is a Demushkin group: it is pro-`p` and topologically finitely
generated, the relator functional of `r` is an isomorphism `H²(G, 𝔽_p) ≅ 𝔽_p`, and the cup form of
`G` is the degree-one form of `⟦r⟧` up to sign, hence nondegenerate. -/
theorem isDemushkin_of_nondegenerate_degreeOneForm [Nonempty X]
    (hnd : (degreeOneForm (gradedMk p (freeProP p X) 1
      ⟨r, (pLowerCentralSeries_one_eq_proPFrattini Fact.out).symm.le hr⟩)).Nondegenerate) :
    IsDemushkin p G := by
  have hP : IsProP p G := (isProP_congr e).1 (presentedProP.isProP p X {r})
  have hbij := dualMap_bijective hr e
  have hdual := (cohomFpLinearEquivContinuousZModDual p G).surjective
  -- The cup product vanishes exactly when the degree-one form does, at the attached characters.
  have hcup := cupFp_eq_zero_iff_degreeOneForm_eq_zero hr e
  -- The relator functional of `r` is a linear isomorphism `H²(G, 𝔽_p) ≅ 𝔽_p`.
  set Φr := relatorFunctional (isClosed_topologicalClosure _)
    (topologicalClosure_normalClosure_singleton_le_proPFrattini hr) e
    ⟨r, le_topologicalClosure _ (subset_normalClosure (Set.mem_singleton r))⟩ with hΦr
  have hinj : Function.Injective Φr := relatorFunctional_injective _ _ e _ rfl
  have hsurj : Function.Surjective Φr := by
    -- The form is nonzero on the nonzero space `Hom_cont(F, 𝔽_p)`, so some cup product is nonzero.
    have : Nontrivial (continuousZModDual p (freeProP p X)) :=
      nontrivial_of_ne _ _ ((dualBasis p X).ne_zero (Classical.arbitrary X))
    obtain ⟨χ, ψ, hne⟩ : ∃ χ ψ, degreeOneForm (gradedMk p (freeProP p X) 1
        ⟨r, (pLowerCentralSeries_one_eq_proPFrattini Fact.out).symm.le hr⟩) χ ψ ≠ 0 := by
      by_contra h
      exact hnd.ne_zero (LinearMap.ext₂ fun χ ψ ↦ by
        simpa using not_not.1 fun hne ↦ h ⟨χ, ψ, hne⟩)
    obtain ⟨a', rfl⟩ := hbij.2 χ
    obtain ⟨a, rfl⟩ := hdual a'
    obtain ⟨b', rfl⟩ := hbij.2 ψ
    obtain ⟨b, rfl⟩ := hdual b'
    have hval : Φr (cupFp p G a b) ≠ 0 := by
      rw [hΦr, relatorFunctional_cupFp, neg_ne_zero]
      exact hne
    intro c
    refine ⟨(c / Φr (cupFp p G a b)) • cupFp p G a b, ?_⟩
    rw [map_smul, smul_eq_mul, div_mul_cancel₀ c hval]
  refine ⟨hP, hP.finite_cohomFp_one_iff.2 ((isTopologicallyFinitelyGenerated_congr e).1
    presentedProP.isTopologicallyFinitelyGenerated), ?_, fun a ha ↦ ?_, fun b hb ↦ ?_⟩
  · rw [(LinearEquiv.ofBijective _ ⟨hinj, hsurj⟩).finrank_eq]
    exact Module.finrank_self (ZMod p)
  · by_contra hcon
    have hall : ∀ b, cupFp p G a b = 0 := fun b ↦ not_not.1 fun h ↦ hcon ⟨b, h⟩
    refine ha ((cohomFpLinearEquivContinuousZModDual p G).map_eq_zero_iff.1 (hbij.1 ?_))
    rw [map_zero]
    refine hnd.1 _ fun ψ ↦ ?_
    obtain ⟨b', rfl⟩ := hbij.2 ψ
    obtain ⟨b, rfl⟩ := hdual b'
    exact (hcup a b).1 (hall b)
  · by_contra hcon
    have hall : ∀ a, cupFp p G a b = 0 := fun a ↦ not_not.1 fun h ↦ hcon ⟨a, h⟩
    refine hb ((cohomFpLinearEquivContinuousZModDual p G).map_eq_zero_iff.1 (hbij.1 ?_))
    rw [map_zero]
    refine hnd.2 _ fun χ ↦ ?_
    obtain ⟨a', rfl⟩ := hbij.2 χ
    obtain ⟨a, rfl⟩ := hdual a'
    exact (hcup a b).1 (hall a)

/-- **Labute's criterion.** Let `F` be the free pro-`p` group on a finite type `X`, let `r ∈ Φ(F)`,
and let `G ≅ ⟨X ∣ r⟩`. Then `G` is a Demushkin group exactly when `X` is nonempty and the degree-one
form of the class of `r` in `gr_1(F)` is nondegenerate. -/
theorem isDemushkin_iff_nondegenerate_degreeOneForm :
    IsDemushkin p G ↔ Nonempty X ∧ (degreeOneForm (gradedMk p (freeProP p X) 1
      ⟨r, (pLowerCentralSeries_one_eq_proPFrattini Fact.out).symm.le hr⟩)).Nondegenerate := by
  refine ⟨fun hG ↦ ⟨?_, hG.nondegenerate_degreeOneForm hr e⟩, fun ⟨hX, hnd⟩ ↦
    haveI := hX; isDemushkin_of_nondegenerate_degreeOneForm hr e hnd⟩
  -- `X` is nonempty: the presentation is minimal, so `#X` is the rank of `G`, which is positive.
  have hcard := (presentedProP.subset_proPFrattini_iff_card_eq {r} e
    hG.isTopologicallyFinitelyGenerated).1 (Set.singleton_subset_iff.2 hr)
  have hpos := hG.demushkinRank_pos
  rw [demushkinRank_def, ← hcard] at hpos
  exact (Nat.card_pos_iff.1 hpos).1


end TauCeti
