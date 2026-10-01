/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.Cup.Duality.OpenSubgroup
public import TauCeti.Topology.Algebra.Group.Profinite.Demushkin.Duality
public import TauCeti.Topology.Algebra.Group.Profinite.Demushkin.Finite
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.CohomologicalDimension
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.EulerCharacteristic.ThreeTerm

/-!
# Open subgroups of Demushkin groups

An open subgroup `U` of an infinite Demushkin group `G` is again a Demushkin group, and its rank is
`n(U) = 2 + [G : U] (n(G) - 2)` (Serre's exposé, §9.2). Both statements are read off Tate's perfect
duality on the finite `𝔽_p[G]`-modules of `G`
(`TauCeti/Topology/Algebra/Group/Profinite/Demushkin/Duality.lean`), applied to the permutation
module `Coind_U^G 𝔽_p`, whose cohomology is that of `U` by Shapiro's lemma.

* `H²(U, 𝔽_p)` is one-dimensional: it is `H²(G, Coind_U^G 𝔽_p)`, which the duality map `α₂`
  identifies with the dual of `H⁰(G, Hom(Coind_U^G 𝔽_p, 𝔽_p))`; the dual of the permutation module
  is again the permutation module, so these invariants are `H⁰(U, 𝔽_p) = 𝔽_p`.
* The cup product of `U` is nondegenerate: a nonzero class of `H¹(U, 𝔽_p)` is a nonzero class of
  `H¹(G, Coind_U^G 𝔽_p)`, which the bijective duality map `α₁` pairs nontrivially with some class
  of `H¹(G, Hom(Coind_U^G 𝔽_p, 𝔽_p))`, and that pairing is the corestriction of the cup product of
  `U` (`TauCeti.ContCohomology.explicitDualityPairing11_explicitCoeff1_toInternalHom`).
* The rank formula is the three-term Euler formula
  `1 - d(U) + dim H²(U, 𝔽_p) = [G : U] (1 - d(G) + dim H²(G, 𝔽_p))` of
  `TauCeti/Topology/Algebra/Group/Profinite/ProP/EulerCharacteristic/ThreeTerm.lean`, which
  applies because `cd_p G ≤ 2`, itself a consequence of the duality, with both `H²` terms equal
  to `1`.

The hypothesis that `G` is infinite is used: `ℤ/2` is a finite Demushkin group whose trivial
subgroup is open and not Demushkin.

## Main results

* `TauCeti.IsDemushkin.finrank_cohomFp_two_openSubgroup`: `dim H²(U, 𝔽_p) = 1` for an open
  subgroup `U` of an infinite Demushkin group.
* `TauCeti.IsDemushkin.openSubgroup`: **an open subgroup of an infinite Demushkin group is
  Demushkin.**
* `TauCeti.IsDemushkin.demushkinRank_openSubgroup_sub_two`: `n(U) - 2 = [G : U] (n(G) - 2)` in
  `ℤ`.
* `TauCeti.IsDemushkin.demushkinRank_openSubgroup`: `n(U) = 2 + [G : U] (n(G) - 2)` in `ℕ`.

## References

* J.-P. Serre, *Structure de certains pro-p-groupes (d'après Demuškin)*, Séminaire Bourbaki 8
  (1962/63), exposé 252, §9.2.
* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., (3.9.15).
-/

public section

namespace TauCeti

open TauCeti.ContCohomology

universe u

-- Preferring the ring path keeps a single additive structure on `ZMod p`, so that the explicit
-- `H²(G, 𝔽_p)` below is the one `TauCeti.cohomFpAddEquivH2` is stated against.
attribute [local instance 2000] Ring.toAddCommGroup

namespace IsDemushkin

variable {p : ℕ} [hp : Fact p.Prime] {G : Type u} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] [Infinite G]
  (hG : IsDemushkin p G) (U : OpenSubgroup G)

include hG

section Explicit

variable [DistribMulAction G (ZMod p)] [ContinuousSMul G (ZMod p)]
  (htriv : ∀ (g : G) (m : ZMod p), g • m = m)

include htriv

/-- The explicit `H²(U, 𝔽_p)` of an open subgroup `U` of an infinite Demushkin group has `p`
elements: it is `H²(G, Coind_U^G 𝔽_p)`, dual under `α₂` to the invariants of
`Hom(Coind_U^G 𝔽_p, 𝔽_p) ≅ Coind_U^G 𝔽_p`, which are `H⁰(U, 𝔽_p) = 𝔽_p`. -/
private theorem natCard_H2_openSubgroup : Nat.card (H2 U.toSubgroup (ZMod p)) = p := by
  have hUc : IsClosed (U.toSubgroup : Set G) := U.isClosed
  have : NeZero p := ⟨hp.out.ne_zero⟩
  have htrivU : ∀ (u : U.toSubgroup) (m : ZMod p), u • m = m := fun u m ↦ htriv u m
  have hM : ∀ f : DiscreteCoind G U.toSubgroup (ZMod p), p • f = 0 :=
    DiscreteCoind.nsmul_eq_zero (ZModModule.char_nsmul_eq_zero p)
  -- `|H²(U, 𝔽_p)| = |H²(G, Coind_U^G 𝔽_p)| = |Hom(H⁰(G, M'), H²(G, 𝔽_p))| = |H⁰(G, M')|`, where
  -- `M' = Hom(Coind_U^G 𝔽_p, 𝔽_p)` is killed by `p`
  rw [← Nat.card_congr (explicitShapiro2 G U.toSubgroup (ZMod p) hUc).toEquiv,
    Nat.card_congr (Equiv.ofBijective _ (hG.dualityMap2_bijective htriv _ hM)),
    hG.natCard_addMonoidHom_H2 htriv _ fun v ↦ Subtype.ext (by
      simpa using InternalHom.nsmul_eq_zero (ZModModule.char_nsmul_eq_zero p)
        (v : InternalHom G (DiscreteCoind G U.toSubgroup (ZMod p)) (ZMod p)))]
  -- `H⁰(G, M') ≅ H⁰(G, Coind_U^G Hom(𝔽_p, 𝔽_p)) ≅ H⁰(U, Hom(𝔽_p, 𝔽_p)) = Hom(𝔽_p, 𝔽_p) ≅ 𝔽_p`
  rw [← Nat.card_congr (Equiv.ofBijective _ (explicitCoeff0_bijective G _
      (DiscreteCoind.toInternalHom_bijective U.toSubgroup (ZMod p) (ZMod p) U.isOpen))),
    Nat.card_congr
      (explicitShapiro0 G U.toSubgroup (InternalHom U.toSubgroup (ZMod p) (ZMod p))).toEquiv,
    H0_eq_top_of_smul_eq_self (InternalHom.smul_eq_self_of_smul_eq_self htrivU htrivU),
    AddSubgroup.card_top, Nat.card_congr (InternalHom.zmodEquiv U.toSubgroup).toEquiv,
    Nat.card_zmod]

end Explicit

/-- **`H²(U, 𝔽_p)` of an open subgroup `U` of an infinite Demushkin group is one-dimensional**:
its explicit model has `p` elements. -/
theorem finrank_cohomFp_two_openSubgroup :
    Module.finrank (ZMod p) (cohomFp p U.toSubgroup 2) = 1 := by
  -- The explicit models need an action of `G` on `𝔽_p`; the trivial one is installed for the
  -- duration of the proof and does not appear in the statement.
  let _ := trivialZModAction p G
  have htriv : ∀ (g : G) (m : ZMod p), g • m = m := fun _ _ ↦ rfl
  have : ContinuousSMul G (ZMod p) := ⟨continuous_snd⟩
  have : Finite (cohomFp p G 2) := hG.finite_cohomFp_two
  have : Finite (cohomFp p U.toSubgroup 2) := hG.isProP.finite_cohomFp_openSubgroup U
  have : Module.Finite (ZMod p) (cohomFp p U.toSubgroup 2) := Module.Finite.of_finite
  have h := hG.natCard_H2_openSubgroup U htriv
  rw [natCard_H2_eq_pow_finrank_cohomFp_two p U.toSubgroup fun u m ↦ htriv u m] at h
  exact Nat.pow_right_injective hp.out.two_le (h.trans (pow_one p).symm)

/-- **An open subgroup of an infinite Demushkin group is Demushkin** (Serre's exposé, §9.2). The
subgroup is pro-`p` and topologically finitely generated with `G`; its `H²(U, 𝔽_p)` is
one-dimensional by `TauCeti.IsDemushkin.finrank_cohomFp_two_openSubgroup`; and its cup product is
nondegenerate because a nonzero class of `H¹(U, 𝔽_p) ≅ H¹(G, Coind_U^G 𝔽_p)` is paired
nontrivially by Tate's duality map `α₁` of `G`, a pairing which is the corestriction of a cup
product of `U`. -/
theorem openSubgroup : IsDemushkin p U.toSubgroup := by
  -- The explicit models need an action of `G` on `𝔽_p`; the trivial one is installed for the
  -- duration of the proof and does not appear in the statement.
  let _ := trivialZModAction p G
  have htriv : ∀ (g : G) (m : ZMod p), g • m = m := fun _ _ ↦ rfl
  have : ContinuousSMul G (ZMod p) := ⟨continuous_snd⟩
  have htrivU : ∀ (u : U.toSubgroup) (m : ZMod p), u • m = m := fun _ _ ↦ rfl
  have hUc : IsClosed (U.toSubgroup : Set G) := U.isClosed
  have : NeZero p := ⟨hp.out.ne_zero⟩
  have hM : ∀ f : DiscreteCoind G U.toSubgroup (ZMod p), p • f = 0 :=
    DiscreteCoind.nsmul_eq_zero (ZModModule.char_nsmul_eq_zero p)
  have hsep : ∀ a : cohomFp p U.toSubgroup 1, a ≠ 0 → ∃ b, cupFp p U.toSubgroup a b ≠ 0 := by
    intro a ha
    -- the class of `a` in `H¹(G, Coind_U^G 𝔽_p)`, through Shapiro's lemma
    set x := cohomFpAddEquivH1 p U.toSubgroup htrivU a with hx
    have hx0 : (explicitShapiro1 G U.toSubgroup (ZMod p) hUc).symm x ≠ 0 :=
      (AddEquiv.map_ne_zero_iff _).2 ((AddEquiv.map_ne_zero_iff _).2 ha)
    -- `α₁` is injective on `Coind_U^G 𝔽_p`, so some class `c` of `H¹(G, Hom(Coind_U^G 𝔽_p, 𝔽_p))`
    -- pairs nontrivially with it
    obtain ⟨c, hc⟩ : ∃ c, dualityMap1 G (DiscreteCoind G U.toSubgroup (ZMod p)) (ZMod p)
        ((explicitShapiro1 G U.toSubgroup (ZMod p) hUc).symm x) c ≠ 0 := by
      by_contra! h
      exact hx0 ((hG.dualityMap1_bijective htriv _ hM).1
        ((AddMonoidHom.ext h).trans (map_zero _).symm))
    -- `c` is a class of `H¹(G, Coind_U^G Hom(𝔽_p, 𝔽_p))`, since the dual of the permutation module
    -- is the permutation module
    obtain ⟨F, rfl⟩ := (explicitCoeff1_bijective G _
      (DiscreteCoind.toInternalHom_bijective U.toSubgroup (ZMod p) (ZMod p) U.isOpen)).2 c
    -- `α₁` pairs the class of `a` with `c` to the corestriction of `x ⌣ y`, where `y` is the class
    -- of the Shapiro image of `F`; so `x ⌣ y ≠ 0`
    refine ⟨(cohomFpAddEquivH1 p U.toSubgroup htrivU).symm (H1InternalHomZModEquiv htrivU
      (explicitShapiro1 G U.toSubgroup _ hUc F)), fun h0 ↦ hc ?_⟩
    rw [cupFp_eq_zero_iff p U.toSubgroup htrivU, AddEquiv.apply_symm_apply, ← hx] at h0
    rw [dualityMap1_eq_neg_explicitDualityPairing11,
      explicitDualityPairing11_explicitCoeff1_toInternalHom G U.toSubgroup U.isOpen,
      AddEquiv.apply_symm_apply, neg_eq_zero]
    have key : explicitDualityPairing11 U.toSubgroup (ZMod p) (ZMod p)
        (explicitShapiro1 G U.toSubgroup _ hUc F) x = 0 := by
      rw [← neg_eq_zero, ← dualityMap1_eq_neg_explicitDualityPairing11, dualityMap1_zmod htrivU]
      exact h0
    rw [key, map_zero]
  exact
    { isProP := hG.isProP.subgroup U.toSubgroup
      finite_cohomFp_one := (hG.isProP.subgroup U.toSubgroup).finite_cohomFp_one_iff.2
        (hG.isTopologicallyFinitelyGenerated.of_openSubgroup U)
      finrank_cohomFp_two := hG.finrank_cohomFp_two_openSubgroup U
      cup_separatingLeft := hsep
      cup_separatingRight := fun b hb ↦ by
        obtain ⟨a, ha⟩ := hsep b hb
        exact ⟨a, fun h ↦ ha ((cupFp_eq_zero_comm p U.toSubgroup a b).1 h)⟩ }

/-- **The rank formula for an open subgroup of an infinite Demushkin group**, in `ℤ`:
`n(U) - 2 = [G : U] (n(G) - 2)`. This is the three-term Euler formula
`1 - d(U) + dim H²(U, 𝔽_p) = [G : U] (1 - d(G) + dim H²(G, 𝔽_p))`, which applies because
`cd_p G ≤ 2`, with both `H²` terms equal to `1`. -/
theorem demushkinRank_openSubgroup_sub_two :
    (demushkinRank (hG.openSubgroup U) : ℤ) - 2 =
      U.toSubgroup.index * ((demushkinRank hG : ℤ) - 2) := by
  -- The explicit models need an action of `G` on `𝔽_p`; the trivial one is installed for the
  -- duration of the proof and does not appear in the statement.
  let _ := trivialZModAction p G
  have htriv : ∀ (g : G) (m : ZMod p), g • m = m := fun _ _ ↦ rfl
  have : ContinuousSMul G (ZMod p) := ⟨continuous_snd⟩
  have htrivU : ∀ (u : U.toSubgroup) (m : ZMod p), u • m = m := fun _ _ ↦ rfl
  -- `cd_p G ≤ 2`, by Tate's duality criterion
  have hcd : CohomologicalDimensionLE.{u} p G 2 := (cohomologicalDimensionAt_le_iff p G 2).1 <|
    hG.isProP.cohomologicalDimensionAt_le_two_of_forall_dualityMap2_bijective (ZMod p)
      fun M _ _ _ _ _ _ hM ↦ hG.dualityMap2_bijective htriv M hM
  have : Module.Finite (ZMod p) (cohomFp p G 2) :=
    Module.finite_of_finrank_eq_succ hG.finrank_cohomFp_two
  have : Finite (H2 G (ZMod p)) := Nat.finite_of_card_ne_zero (by
    rw [natCard_H2_eq_pow_finrank_cohomFp_two p G htriv]; exact pow_ne_zero _ hp.out.ne_zero)
  have hE := CohomologicalDimensionLE.one_sub_topologicalGeneratorRankNat_add_finrank_H2 hG.isProP
    hG.isTopologicallyFinitelyGenerated htriv hcd U
  rw [← (cohomFpLinearEquivH2 p G htriv).finrank_eq, hG.finrank_cohomFp_two,
    ← (cohomFpLinearEquivH2 p U.toSubgroup htrivU).finrank_eq,
    hG.finrank_cohomFp_two_openSubgroup U] at hE
  rw [demushkinRank_def, demushkinRank_def]
  push_cast at hE ⊢
  linarith

/-- **The rank formula for an open subgroup of an infinite Demushkin group**, in `ℕ`:
`n(U) = 2 + [G : U] (n(G) - 2)`. The subtraction is not truncated, since an infinite Demushkin
group has rank at least `2`. -/
theorem demushkinRank_openSubgroup :
    demushkinRank (hG.openSubgroup U) = 2 + U.toSubgroup.index * (demushkinRank hG - 2) := by
  have h2 := hG.two_le_demushkinRank_of_infinite
  have h := hG.demushkinRank_openSubgroup_sub_two U
  zify [h2]
  linarith

end IsDemushkin

end TauCeti
