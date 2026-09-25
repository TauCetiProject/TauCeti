/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.FiniteQuotients
public import TauCeti.Topology.Algebra.Group.Profinite.Generation
public import TauCeti.Topology.Algebra.Group.Profinite.Hopfian
public import TauCeti.Topology.Algebra.Group.Profinite.Limit
public import TauCeti.Topology.Compactness.InverseSystem

/-!
# Finite-quotient determinacy of profinite groups

A topologically finitely generated profinite group is determined by its continuous finite
quotients (`TauCeti.IsFiniteContinuousQuotient`, defined in
`TauCeti.Topology.Algebra.Group.FiniteQuotients`): if `G` is topologically finitely generated and
the profinite groups `G` and `H` have the same continuous finite quotients, then `G ≃ₜ* H`. Finite
generation is assumed on one side only, and is a conclusion on the other.

The theorem is assembled from three implications between finite-quotient data and maps.

* **Finite generation descends.** If `G` is topologically finitely generated and every continuous
  finite quotient of the profinite group `H` is one of `G`, then `H` is topologically finitely
  generated (`IsTopologicallyFinitelyGenerated.of_forall_isFiniteContinuousQuotient`).
* **Finite-quotient data produces a surjection.** If `H` is a topologically finitely generated
  compact group and every quotient `G ⧸ N` of the profinite group `G` by an open normal subgroup
  occurs as a continuous quotient of `H`, then there is a continuous surjection `H ↠ G`
  (`exists_continuous_surjective_of_forall_isFiniteContinuousQuotient`).
* **Surjections in both directions are isomorphisms.** If `G` is topologically finitely generated
  and profinite, continuous surjections `G ↠ H` and `H ↠ G` make `G ↠ H` bijective
  (`IsTopologicallyFinitelyGenerated.bijective_of_surjective_of_surjective`, the Hopf property of
  `G`), hence a topological isomorphism when `H` is also compact Hausdorff.

Finite generation cannot be dropped on both sides: for a prime `p`, the products `∏_{i : ℕ} ℤ/p`
and `∏_{i : ℝ} ℤ/p` have the same continuous finite quotients, namely the finite elementary abelian
`p`-groups, but they have different cardinalities.

## Main results

* `TauCeti.IsTopologicallyFinitelyGenerated.of_forall_isFiniteContinuousQuotient`: a profinite
  group whose continuous finite quotients all occur for a topologically finitely generated one is
  topologically finitely generated.
* `TauCeti.exists_continuous_surjective_of_forall_isFiniteContinuousQuotient`: a topologically
  finitely generated compact group surjects continuously onto a profinite group all of whose
  finite quotients it has.
* `TauCeti.exists_surjective_and_exists_surjective_of_forall_isFiniteContinuousQuotient_iff`:
  two profinite groups with the same continuous finite quotients, one of them topologically
  finitely generated, admit continuous surjections in both directions.
* `TauCeti.nonempty_continuousMulEquiv_of_forall_isFiniteContinuousQuotient_iff`: **finite-quotient
  determinacy**: such groups are topologically isomorphic.

## References

* L. Ribes and P. Zalesskii, *Profinite Groups*, Section 3.2.
* J. D. Dixon, E. W. Formanek, J. C. Poland and L. Ribes, *Profinite completions and isomorphic
  finite quotients*, J. Pure Appl. Algebra 23 (1982), 227–231.
-/

public section

namespace TauCeti

universe u v

section FiniteGeneration

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {H : Type v} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [CompactSpace H]
  [TotallyDisconnectedSpace H]

/-- **Finite generation passes to a group with fewer continuous finite quotients.** If the
topological group `G` is topologically finitely generated and every continuous finite quotient of
the profinite group `H` occurs as a continuous finite quotient of `G`, then `H` is topologically
finitely generated. -/
theorem IsTopologicallyFinitelyGenerated.of_forall_isFiniteContinuousQuotient
    (hG : IsTopologicallyFinitelyGenerated G)
    (h : ∀ (Q : Type v) [Group Q] [Finite Q],
      IsFiniteContinuousQuotient H Q → IsFiniteContinuousQuotient G Q) :
    IsTopologicallyFinitelyGenerated H := by
  -- Each finite quotient of `H` is a finite quotient of `G`, so needs no more generators than `G`
  -- does, and a uniform bound on the ranks of the finite quotients is topological finite
  -- generation.
  obtain ⟨s, hs⟩ := isTopologicallyFinitelyGenerated_iff.mp hG
  refine isTopologicallyFinitelyGenerated_iff_exists_rank_le.mpr ⟨s.card, fun U ↦ ?_⟩
  obtain ⟨_, f, hsurj, hopen⟩ :=
    isFiniteContinuousQuotient_iff.mp (h _ U.isFiniteContinuousQuotient)
  -- The kernel of `f` is an open normal subgroup `K` of `G` with `G ⧸ K ≃* H ⧸ U`.
  let K : OpenNormalSubgroup G := ⟨⟨f.ker, hopen⟩, inferInstance⟩
  calc Group.rank (H ⧸ U.toSubgroup)
      = Group.rank (G ⧸ K.toSubgroup) :=
        (Group.rank_congr (QuotientGroup.quotientKerEquivOfSurjective f hsurj)).symm
    _ ≤ s.card := rank_quotient_le_card_of_topologicalClosure_closure_eq_top hs K

end FiniteGeneration

section Surjection

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G]
variable {H : Type v} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [CompactSpace H]

variable (H) in
/-- The surjections from `H` onto the finite quotient `G ⧸ N` with open kernel: the level-`N` data
of the inverse system whose compatible families are the continuous surjections `H ↠ G`. -/
private def LevelSurjection (N : OpenNormalSubgroup G) :=
  {f : H →* G ⧸ N.toSubgroup // Function.Surjective f ∧ IsOpen (f.ker : Set H)}

/-- The bonding map of the inverse system: composition with the quotient map
`G ⧸ N → G ⧸ N'`, for `N ≤ N'`. -/
private def levelSurjectionMap ⦃N N' : OpenNormalSubgroup G⦄ (hle : N ≤ N')
    (f : LevelSurjection H N) : LevelSurjection H N' :=
  ⟨(QuotientGroup.mapOfLE hle).comp f.1, (QuotientGroup.mapOfLE_surjective hle).comp f.2.1,
    Subgroup.isOpen_mono (fun a ha ↦ by
      rw [MonoidHom.mem_ker] at ha ⊢
      rw [MonoidHom.comp_apply, ha, map_one]) f.2.2⟩

private instance : DirectedSystem (LevelSurjection H (G := G))
    (levelSurjectionMap (G := G) (H := H)) where
  map_self _ _ := Subtype.ext <| by simp [levelSurjectionMap]
  map_map _ _ _ _ _ _ := Subtype.ext <| by simp [levelSurjectionMap, ← MonoidHom.comp_assoc]

/-- **A continuous surjection from finite-quotient data.** Let `H` be a topologically finitely
generated compact group and `G` a profinite group such that every quotient `G ⧸ N` of `G` by an
open normal subgroup occurs as a continuous finite quotient of `H`. Then there is a continuous
surjective homomorphism `H →* G`. -/
theorem exists_continuous_surjective_of_forall_isFiniteContinuousQuotient
    (hH : IsTopologicallyFinitelyGenerated H)
    (h : ∀ N : OpenNormalSubgroup G, IsFiniteContinuousQuotient H (G ⧸ N.toSubgroup)) :
    ∃ φ : H →* G, Continuous φ ∧ Function.Surjective φ := by
  -- Each level set is finite, because `H` has finitely many homomorphisms with open kernel into
  -- the finite group `G ⧸ N`, and nonempty by hypothesis.
  have : ∀ N, Finite (LevelSurjection H N) := fun N ↦
    have := hH.finite_monoidHom_isOpen_ker (G ⧸ N.toSubgroup)
    Finite.of_injective (fun f : LevelSurjection H N ↦
      (⟨f.1, f.2.2⟩ : {f : H →* G ⧸ N.toSubgroup // IsOpen (f.ker : Set H)}))
      fun _ _ hfg ↦ Subtype.ext (Subtype.mk.inj hfg)
  have : ∀ N, Nonempty (LevelSurjection H N) := fun N ↦
    let ⟨_, f, hf⟩ := isFiniteContinuousQuotient_iff.mp (h N)
    ⟨⟨f, hf⟩⟩
  -- Kőnig's lemma gives a compatible family of level surjections, and the limit description of
  -- `G` assembles it into a homomorphism `H →* G`.
  obtain ⟨x, hx⟩ :=
    exists_forall_map_eq_of_codirected_of_finite (levelSurjectionMap (G := G) (H := H))
  obtain ⟨φ, hφ, -⟩ := existsUnique_monoidHom_mk'_comp_eq (fun N ↦ (x N).1)
    fun _ _ hle ↦ congrArg Subtype.val (hx hle)
  -- Continuity is checked on the finite quotients, where the shadows have open kernels.
  have hcont : Continuous φ := by
    refine continuous_iff_forall_continuous_mk.mpr fun N ↦ ?_
    have hN : IsOpen (((QuotientGroup.mk' N.toSubgroup).comp φ).ker : Set H) := by
      rw [hφ N]
      exact (x N).2.2
    simpa [MonoidHom.coe_comp, Function.comp_def] using
      ((QuotientGroup.mk' N.toSubgroup).comp φ).continuous_iff_isOpen_ker.mpr hN
  refine ⟨φ, hcont, surjective_of_forall_surjective_mk'_comp hcont fun N ↦ ?_⟩
  rw [hφ N]
  exact (x N).2.1

end Surjection

section Determinacy

variable {G H : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G] [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  [CompactSpace H] [TotallyDisconnectedSpace H]

/-- **Two epimorphisms.** If `G` is topologically finitely generated and the profinite groups `G`
and `H` have the same continuous finite quotients, then there are continuous surjections `G ↠ H`
and `H ↠ G`. Finite generation of `H` is derived, not assumed. -/
theorem exists_surjective_and_exists_surjective_of_forall_isFiniteContinuousQuotient_iff
    (hG : IsTopologicallyFinitelyGenerated G)
    (h : ∀ (Q : Type u) [Group Q] [Finite Q],
      IsFiniteContinuousQuotient G Q ↔ IsFiniteContinuousQuotient H Q) :
    (∃ φ : G →* H, Continuous φ ∧ Function.Surjective φ) ∧
      ∃ ψ : H →* G, Continuous ψ ∧ Function.Surjective ψ := by
  have hH : IsTopologicallyFinitelyGenerated H :=
    hG.of_forall_isFiniteContinuousQuotient fun Q _ _ hQ ↦ (h Q).mpr hQ
  exact ⟨exists_continuous_surjective_of_forall_isFiniteContinuousQuotient hG
      fun N ↦ (h _).mpr N.isFiniteContinuousQuotient,
    exists_continuous_surjective_of_forall_isFiniteContinuousQuotient hH
      fun N ↦ (h _).mp N.isFiniteContinuousQuotient⟩

/-- **Finite-quotient determinacy.** If `G` is topologically finitely generated and the profinite
groups `G` and `H` have the same continuous finite quotients, then `G` and `H` are topologically
isomorphic. No finite-generation hypothesis is placed on `H`. -/
theorem nonempty_continuousMulEquiv_of_forall_isFiniteContinuousQuotient_iff
    (hG : IsTopologicallyFinitelyGenerated G)
    (h : ∀ (Q : Type u) [Group Q] [Finite Q],
      IsFiniteContinuousQuotient G Q ↔ IsFiniteContinuousQuotient H Q) :
    Nonempty (G ≃ₜ* H) := by
  obtain ⟨⟨φ, hφ, hφs⟩, ⟨ψ, hψ, hψs⟩⟩ :=
    exists_surjective_and_exists_surjective_of_forall_isFiniteContinuousQuotient_iff hG h
  have hb := hG.bijective_of_surjective_of_surjective hφ hφs hψ hψs
  -- A continuous bijective homomorphism of compact Hausdorff groups is a topological isomorphism.
  exact ⟨ContinuousMulEquiv.mk (MulEquiv.ofBijective φ hb) hφ
    (hφ.continuous_symm_of_equiv_compact_to_t2 (f := (MulEquiv.ofBijective φ hb).toEquiv))⟩

end Determinacy

end TauCeti
