/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.CharacterExtension
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Cup.Naturality
public import TauCeti.RepresentationTheory.Homological.ContCohomology.TrivialFp.Cup
public import TauCeti.Topology.Algebra.Group.Profinite.Demushkin.Basic
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.EulerCharacteristic.ThreeTerm

/-!
# Recognising Demushkin groups by the cohomology of their open subgroups

A Demushkin group is a pro-`p` group with finite-dimensional `H¹(G, 𝔽_p)`, one-dimensional
`H²(G, 𝔽_p)` and a nondegenerate cup product `H¹ × H¹ → H²`. This file proves that the cup product
condition can be replaced by conditions on the open normal subgroups of index `p`, for a group of
`p`-cohomological dimension at most `2` (NSW (3.9.15), due to Andozhskii and to Dummit–Labute):

* if `dim H²(U, 𝔽_p) = 1` for every open normal subgroup `U` of index `p`, then `G` is Demushkin
  (`TauCeti.CohomologicalDimensionLE.isDemushkin_of_finrank_cohomFp_two_openSubgroup`);
* if `d(U) - 2 = [G : U] (d(G) - 2)` for every open normal subgroup `U` of index `p`, where `d` is
  the topological generator rank, then `G` is Demushkin
  (`TauCeti.CohomologicalDimensionLE.isDemushkin_of_topologicalGeneratorRankNat_openSubgroup`).

The second statement reduces to the first through the three-term Euler formula
`1 - d(U) + dim H²(U, 𝔽_p) = [G : U] (1 - d(G) + dim H²(G, 𝔽_p))`.

The first is a counting argument. Suppose that a nonzero, hence surjective, character
`χ : G → 𝔽_p` cups trivially with every class of `H¹(G, 𝔽_p)`, and let `U = ker χ`. In the short
exact sequence `0 → 𝔽_p → E(χ) → 𝔽_p → 0` of the extension module `E(χ)` attached to `χ`, the
connecting map `H¹(G, 𝔽_p) → H²(G, 𝔽_p)` is the cup product with `χ`, hence zero, and
`H³(G, 𝔽_p) = 0` because `cd_p G ≤ 2`. So `H²(G, E(χ))` is an extension of `H²(G, 𝔽_p)` by
`H²(G, 𝔽_p)`, of order `|H²(G, 𝔽_p)|²`. On the other hand `E(χ)` is a quotient of the permutation
module `Coind_U^G 𝔽_p`, by a kernel killed by `p`, so `H²(G, E(χ))` is a quotient of
`H²(G, Coind_U^G 𝔽_p) ≅ H²(U, 𝔽_p)` (Shapiro). Hence `|H²(G, 𝔽_p)|² ≤ |H²(U, 𝔽_p)|`
(`TauCeti.CohomologicalDimensionLE.natCard_H2_sq_le_natCard_H2_ker`), which is impossible when both
groups have order `p`.

The converse implications, that a Demushkin group satisfies both conditions, rest on the theorem
that an open subgroup of an infinite Demushkin group is Demushkin, which is not proved here.

## Main results

* `TauCeti.CohomologicalDimensionLE.natCard_H2_sq_le_natCard_H2_ker`: a surjective character that
  cups trivially with `H¹(G, 𝔽_p)` has `|H²(G, 𝔽_p)|² ≤ |H²(ker χ, 𝔽_p)|`, when `cd_p G ≤ 2`.
* `TauCeti.CohomologicalDimensionLE.isDemushkin_of_finrank_cohomFp_two_openSubgroup`: the
  recognition criterion through `dim H²` of the open normal subgroups of index `p`.
* `TauCeti.CohomologicalDimensionLE.isDemushkin_of_topologicalGeneratorRankNat_openSubgroup`: the
  recognition criterion through the ranks of the open normal subgroups of index `p`.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., (3.9.15).
* D. S. Dummit, J. P. Labute, *On a new characterization of Demuškin groups*, Invent. Math. 73
  (1983), 413–418.
-/

public section

namespace TauCeti

open ContCohomology

universe u

-- Preferring the ring path keeps a single additive structure on `ZMod p`, so that the trivial
-- actions below are the ones the explicit cohomology is stated against.
attribute [local instance 2000] Ring.toAddCommGroup

variable {p : ℕ} [hp : Fact p.Prime] {G : Type u} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G]

namespace CohomologicalDimensionLE

section Counting

variable [DistribMulAction G (ZMod p)] [ContinuousSMul G (ZMod p)]
  (htriv : ∀ (g : G) (x : ZMod p), g • x = x) (hcd : CohomologicalDimensionLE.{u} p G 2)
include htriv hcd

/-- **A character that cups trivially with `H¹` doubles the order of `H²` on its kernel.** Let `G`
be a profinite group with `cd_p G ≤ 2` and let `χ : G → 𝔽_p` be a surjective continuous character
with `χ ⌣ y = 0` in `H²(G, 𝔽_p)` for every `y ∈ H¹(G, 𝔽_p)`. Then
`|H²(G, 𝔽_p)|² ≤ |H²(ker χ, 𝔽_p)|`, when the right-hand side is finite.

Proof: the connecting map of `0 → 𝔽_p → E(χ) → 𝔽_p → 0` is `χ ⌣ -`, so `H²(G, E(χ))` has order
`|H²(G, 𝔽_p)|²`, and it is a quotient of `H²(G, Coind_{ker χ}^G 𝔽_p) ≅ H²(ker χ, 𝔽_p)`. -/
theorem natCard_H2_sq_le_natCard_H2_ker (χ : G →ₜ* Multiplicative (ZMod p))
    (hχ : Function.Surjective χ)
    (hcup : ∀ y : H1 G (ZMod p), explicitCup11 G (ZMod p) (ZMod p) (ZMod p) AddMonoidHom.mul
      continuous_mul (smul_mul_smul_of_smul_eq_self htriv)
      ((H1EquivOfSmulEqSelf htriv).symm (Additive.ofMul χ)) y = 0)
    [Finite (H2 (χ : G →* Multiplicative (ZMod p)).ker (ZMod p))] :
    Nat.card (H2 G (ZMod p)) ^ 2 ≤
      Nat.card (H2 (χ : G →* Multiplicative (ZMod p)).ker (ZMod p)) := by
  set N := (χ : G →* Multiplicative (ZMod p)).ker
  have hN : ∀ n ∈ N, χ n = 1 := fun n hn ↦ hn
  have hNker : ∀ g : G, χ g = 1 → g ∈ N := fun g hg ↦ hg
  have hNopen : IsOpen (N : Set G) := (isOpen_discrete {1}).preimage χ.continuous
  have : Finite (G ⧸ N) := N.quotient_finite_of_isOpen hNopen
  have : N.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  -- `cd_p G ≤ 2` kills the canonical `H³` of every discrete module killed by `p`
  have h3 : ∀ (A : Type u) [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A]
      [DistribMulAction G A] [ContinuousSMul G A], (∀ a : A, p • a = 0) →
      Subsingleton (continuousCohomology 3 (ofDiscreteModule ℤ G A)) := fun A _ _ _ _ _ hA ↦
    cohomologicalDimensionLE_iff.mp hcd A (isPPrimaryTorsion_iff.2 fun a ↦ ⟨1, by rw [pow_one, hA]⟩)
      3 (by norm_num)
  have : ContinuousSMul G (ULift.{u} (ZMod p)) :=
    ⟨continuous_snd.congr fun q ↦ ULift.ext (htriv q.1 q.2.down).symm⟩
  -- the trivial modules `𝔽_p` in the universe of `G` have the `H²` of `𝔽_p`
  have hA : Nat.card (H2 G (ULift.{u} (ZMod p))) = Nat.card (H2 G (ZMod p)) :=
    Nat.card_congr (explicitMap2Equiv G (ULift.{u} (ZMod p)) G (ZMod p)
      (ContinuousMulEquiv.refl G) AddEquiv.ulift continuous_of_discreteTopology
      continuous_of_discreteTopology fun _ _ ↦ rfl).toEquiv
  -- the connecting map of `0 → 𝔽_p → E(χ) → 𝔽_p → 0` is `χ ⌣ -`, which vanishes
  set S := CharacterExtension.shortExact χ htriv
  have hδ : ∀ x, S.explicitDelta1 x = 0 := fun x ↦ by
    rw [CharacterExtension.explicitDelta1_shortExact]
    refine (explicitMap2Equiv G (ULift.{u} (ZMod p)) G (ZMod p) (ContinuousMulEquiv.refl G)
      AddEquiv.ulift continuous_of_discreteTopology continuous_of_discreteTopology
      fun _ _ ↦ rfl).injective ?_
    rw [map_zero]
    -- `erw`: the additive structure of `ZMod p` here is `Ring.toAddCommGroup`, preferred locally,
    -- which agrees with the one in `explicitMap2Equiv_apply` only up to unfolding instances
    erw [explicitMap2Equiv_apply]
    rw [explicitMap2_explicitCup11 (μ' := AddMonoidHom.mul) (hμ' := continuous_mul)
      (hequiv' := smul_mul_smul_of_smul_eq_self htriv)
      (φ := (ContinuousMulEquiv.refl G : G →ₜ* G)) (fM := AddMonoidHom.id (ZMod p))
      (fN := AddEquiv.ulift.toAddMonoidHom) (fP := AddEquiv.ulift.toAddMonoidHom)
      (hcM := continuous_id) (hcN := continuous_of_discreteTopology)
      (hcP := continuous_of_discreteTopology) (hfM := fun _ _ ↦ rfl) (hfN := fun _ _ ↦ rfl)
      (hfP := fun _ _ ↦ rfl) (hpair := fun _ _ ↦ rfl)]
    convert hcup _ using 2
    rw [H1EquivOfSmulEqSelf_symm_apply]
    -- `erw`: the cup product of `hcup` carries the continuity proof `continuous_mul` of
    -- multiplication, which matches the pairing `AddMonoidHom.mul` only up to unfolding
    erw [explicitMap1_mk]
    congr 2
    ext g
    exact cocyclesMap1_apply ..
  -- `H²(G, E(χ))` has order `|H²(G, 𝔽_p)|²`
  have h3A := h3 (ULift.{u} (ZMod p)) fun a ↦ ULift.ext (by simp)
  have hπ := S.explicitCoeff2_proj_surjective_of_subsingleton
  have hι : Function.Injective
      (explicitCoeff2 G _ S.inclDistribMulActionHom continuous_of_discreteTopology) := by
    rw [← AddMonoidHom.ker_eq_bot_iff, ← S.explicitLongExact_H2A, eq_bot_iff]
    rintro _ ⟨x, rfl⟩
    exact hδ x
  have hE : Nat.card (H2 G (CharacterExtension χ)) = Nat.card (H2 G (ZMod p)) ^ 2 := by
    rw [← AddSubgroup.card_ker_mul_card_of_surjective hπ, ← S.explicitLongExact_H2B,
      ← Nat.card_congr (AddMonoidHom.ofInjective hι).toEquiv, hA, sq]
  -- `E(χ)` is the quotient of `Coind_N^G 𝔽_p` by the kernel `K` of the trace map
  set T := CharacterExtension.coindTrace χ htriv hN
  set K := (T : DiscreteCoind G N (ZMod p) →+ CharacterExtension χ).ker
  have hT : ∀ f, (T : DiscreteCoind G N (ZMod p) →+ CharacterExtension χ) f = T f := fun f ↦
    congrFun (DistribMulActionHom.coe_fn_coe T) f
  have hK : ∀ g : G, ∀ f ∈ K, g • f ∈ K := fun g f hf ↦ by
    rw [AddMonoidHom.mem_ker, hT] at hf ⊢
    rw [map_smul, hf, smul_zero]
  let := K.restrictDistribMulAction hK
  have := K.restrictDistribMulAction_continuousSMul hK
  let S' : DiscreteShortExact G K (DiscreteCoind G N (ZMod p)) (CharacterExtension χ) :=
    { incl := K.subtype
      proj := T
      incl_equivariant := K.restrictDistribMulAction_coe_smul hK
      proj_equivariant := fun g f ↦ by rw [hT, hT, map_smul]
      incl_injective := K.subtype_injective
      proj_surjective := fun x ↦ by
        obtain ⟨f, hf⟩ := CharacterExtension.coindTrace_surjective χ htriv hN hNker hχ x
        exact ⟨f, (hT f).trans hf⟩
      exact := fun f ↦ ⟨fun hf ↦ ⟨⟨f, hf⟩, rfl⟩, by rintro ⟨a, rfl⟩; exact a.2⟩ }
  -- `Coind_N^G 𝔽_p`, hence `K`, is killed by `p`
  have hp0 : ∀ f : DiscreteCoind G N (ZMod p), p • f = 0 := fun f ↦ DiscreteCoind.ext fun g ↦ by
    rw [← DiscreteCoind.coe_toCoind, map_nsmul, AddSubgroup.coe_nsmul, Pi.smul_apply,
      DiscreteCoind.coe_toCoind, DiscreteCoind.coe_zero, Pi.zero_apply, nsmul_eq_mul,
      ZMod.natCast_self, zero_mul]
  have h3K := h3 K fun a ↦ Subtype.ext (by rw [AddSubgroup.coe_nsmul, hp0, AddSubgroup.coe_zero])
  have hπ' := S'.explicitCoeff2_proj_surjective_of_subsingleton
  -- Shapiro's lemma identifies `H²(G, Coind_N^G 𝔽_p)` with `H²(N, 𝔽_p)`
  have hSh := explicitShapiro2 G N (ZMod p) (N.isClosed_of_isOpen hNopen)
  have : Finite (H2 G (DiscreteCoind G N (ZMod p))) := Finite.of_equiv _ hSh.symm.toEquiv
  calc Nat.card (H2 G (ZMod p)) ^ 2 = Nat.card (H2 G (CharacterExtension χ)) := hE.symm
    _ ≤ Nat.card (H2 G (DiscreteCoind G N (ZMod p))) := Nat.card_le_card_of_surjective _ hπ'
    _ = Nat.card (H2 N (ZMod p)) := Nat.card_congr hSh.toEquiv

end Counting

section Recognition

/-- A one-dimensional `H²(H, 𝔽_p)` has order `p` on the explicit model. -/
private theorem natCard_H2_eq_of_finrank_cohomFp_two {H : Type u} [Group H] [TopologicalSpace H]
    [IsTopologicalGroup H] [LocallyCompactSpace H] [DistribMulAction H (ZMod p)]
    [ContinuousSMul H (ZMod p)] (htriv : ∀ (h : H) (x : ZMod p), h • x = x)
    (h2 : Module.finrank (ZMod p) (cohomFp p H 2) = 1) : Nat.card (H2 H (ZMod p)) = p := by
  have : Module.Finite (ZMod p) (cohomFp p H 2) := Module.finite_of_finrank_eq_succ h2
  rw [← Nat.card_congr (cohomFpAddEquivH2 p H htriv).toEquiv,
    Module.natCard_eq_pow_finrank (K := ZMod p), h2, pow_one, Nat.card_zmod]

variable (hcd : CohomologicalDimensionLE.{u} p G 2)
include hcd

/-- **Recognition of Demushkin groups by `H²` of the subgroups of index `p`** (NSW (3.9.15), the
implication from (ii) to (i), in the sharpened form over the subgroups of index `p`). Let `G` be a
topologically finitely generated pro-`p` group with `cd_p G ≤ 2` and `dim H²(G, 𝔽_p) = 1`. If
`dim H²(U, 𝔽_p) = 1` for every open normal subgroup `U` of index `p`, then `G` is a Demushkin
group.

A nonzero class `a ∈ H¹(G, 𝔽_p)` with `a ⌣ H¹(G, 𝔽_p) = 0` would give a character `χ` with
`|H²(G, 𝔽_p)|² ≤ |H²(ker χ, 𝔽_p)|` (`natCard_H2_sq_le_natCard_H2_ker`), that is `p² ≤ p`. -/
theorem isDemushkin_of_finrank_cohomFp_two_openSubgroup (hG : IsProP p G)
    (hfg : IsTopologicallyFinitelyGenerated G) (h2 : Module.finrank (ZMod p) (cohomFp p G 2) = 1)
    (hU : ∀ U : OpenSubgroup G, (U : Subgroup G).Normal → (U : Subgroup G).index = p →
      Module.finrank (ZMod p) (cohomFp p (U : Subgroup G) 2) = 1) :
    IsDemushkin p G := by
  -- The explicit models need an action of `G` on `𝔽_p`; the trivial one is installed for the
  -- duration of the proof and does not appear in the statement.
  let _ := trivialZModAction p G
  have htriv : ∀ (g : G) (m : ZMod p), g • m = m := fun _ _ ↦ rfl
  have : ContinuousSMul G (ZMod p) := ⟨continuous_snd⟩
  have hsep : ∀ a : cohomFp p G 1, a ≠ 0 → ∃ b, cupFp p G a b ≠ 0 := by
    intro a ha
    by_contra! hcon
    -- the character `χ` of `a`
    set x := cohomFpAddEquivH1 p G htriv a
    set χ := Additive.toMul (H1EquivOfSmulEqSelf htriv x)
    have hx : (H1EquivOfSmulEqSelf htriv).symm (Additive.ofMul χ) = x := by
      rw [ofMul_toMul, AddEquiv.symm_apply_apply]
    have hcup : ∀ y : H1 G (ZMod p), explicitCup11 G (ZMod p) (ZMod p) (ZMod p) AddMonoidHom.mul
        continuous_mul (smul_mul_smul_of_smul_eq_self htriv)
        ((H1EquivOfSmulEqSelf htriv).symm (Additive.ofMul χ)) y = 0 := fun y ↦ by
      have h := (cupFp_eq_zero_iff p G htriv a ((cohomFpAddEquivH1 p G htriv).symm y)).1 (hcon _)
      rw [AddEquiv.apply_symm_apply] at h
      rw [hx]
      exact h
    -- `χ` is nonzero, hence onto, `𝔽_p` having prime order
    have hχ : (χ : G →* Multiplicative (ZMod p)) ≠ 1 := fun h ↦ ha <| by
      have h' : χ = 1 := ContinuousMonoidHom.ext fun g ↦ DFunLike.congr_fun h g
      have hx0 : x = 0 := by rw [← hx, h', ofMul_one, map_zero]
      exact (cohomFpAddEquivH1 p G htriv).map_eq_zero_iff.1 hx0
    have : Fact (Nat.card (Multiplicative (ZMod p))).Prime :=
      ⟨by rw [show Nat.card (Multiplicative (ZMod p)) = p from Nat.card_zmod p]; exact hp.out⟩
    have hrange : (χ : G →* Multiplicative (ZMod p)).range = ⊤ :=
      ((χ : G →* Multiplicative (ZMod p)).range.eq_bot_or_eq_top_of_prime_card).resolve_left
        fun h ↦ hχ (MonoidHom.range_eq_bot_iff.1 h)
    -- its kernel is an open normal subgroup of index `p`
    set N := (χ : G →* Multiplicative (ZMod p)).ker
    have hNopen : IsOpen (N : Set G) := (isOpen_discrete {1}).preimage χ.continuous
    have hNindex : N.index = p := by
      rw [Subgroup.index_ker, hrange, Subgroup.card_top]
      exact Nat.card_zmod p
    have : CompactSpace N := isCompact_iff_compactSpace.mp (N.isClosed_of_isOpen hNopen).isCompact
    have hN2 := hU ⟨N, hNopen⟩ (MonoidHom.normal_ker _) hNindex
    have hcardN := natCard_H2_eq_of_finrank_cohomFp_two (H := N) (fun n m ↦ htriv n m) hN2
    have : Finite (H2 N (ZMod p)) :=
      Nat.finite_of_card_ne_zero (by rw [hcardN]; exact hp.out.ne_zero)
    have hle := natCard_H2_sq_le_natCard_H2_ker htriv hcd χ (MonoidHom.range_eq_top.1 hrange)
      hcup
    rw [natCard_H2_eq_of_finrank_cohomFp_two htriv h2, hcardN] at hle
    have := hp.out.two_le
    nlinarith
  exact
    { isProP := hG
      finite_cohomFp_one := hG.finite_cohomFp_one_iff.2 hfg
      finrank_cohomFp_two := h2
      cup_separatingLeft := hsep
      cup_separatingRight := fun b hb ↦ by
        obtain ⟨a, ha⟩ := hsep b hb
        exact ⟨a, fun h ↦ ha ((cupFp_eq_zero_comm p G a b).1 h)⟩ }

/-- **Recognition of Demushkin groups by the ranks of the subgroups of index `p`** (NSW (3.9.15),
the implication from (iii) to (i), in the sharpened form over the subgroups of index `p`). Let `G`
be a topologically finitely generated pro-`p` group with `cd_p G ≤ 2` and `dim H²(G, 𝔽_p) = 1`. If
`d(U) - 2 = [G : U] (d(G) - 2)` for every open normal subgroup `U` of index `p`, where `d` is the
topological generator rank, then `G` is a Demushkin group.

By the three-term Euler formula the rank condition says `dim H²(U, 𝔽_p) = 1`, which is
`isDemushkin_of_finrank_cohomFp_two_openSubgroup`. -/
theorem isDemushkin_of_topologicalGeneratorRankNat_openSubgroup (hG : IsProP p G)
    (hfg : IsTopologicallyFinitelyGenerated G) (h2 : Module.finrank (ZMod p) (cohomFp p G 2) = 1)
    (hU : ∀ U : OpenSubgroup G, (U : Subgroup G).Normal → (U : Subgroup G).index = p →
      (topologicalGeneratorRankNat (U : Subgroup G) (hfg.of_openSubgroup U) : ℤ) - 2 =
        p * ((topologicalGeneratorRankNat G hfg : ℤ) - 2)) :
    IsDemushkin p G := by
  refine isDemushkin_of_finrank_cohomFp_two_openSubgroup hcd hG hfg h2 fun U hUn hUi ↦ ?_
  -- The explicit models need an action of `G` on `𝔽_p`; the trivial one is installed for the
  -- duration of the proof and does not appear in the statement.
  let _ := trivialZModAction p G
  have htriv : ∀ (g : G) (m : ZMod p), g • m = m := fun _ _ ↦ rfl
  have : ContinuousSMul G (ZMod p) := ⟨continuous_snd⟩
  have : CompactSpace (U : Subgroup G) := isCompact_iff_compactSpace.mp U.isClosed.isCompact
  have hcardG := natCard_H2_eq_of_finrank_cohomFp_two htriv h2
  have : Finite (H2 G (ZMod p)) :=
    Nat.finite_of_card_ne_zero (by rw [hcardG]; exact hp.out.ne_zero)
  -- the three-term Euler formula for `U`
  have hE := one_sub_topologicalGeneratorRankNat_add_finrank_H2 hG hfg htriv hcd U
  rw [← (cohomFpLinearEquivH2 p G htriv).finrank_eq, h2, hUi] at hE
  rw [(cohomFpLinearEquivH2 p (U : Subgroup G) fun u m ↦ htriv u m).finrank_eq]
  have hrank := hU U hUn hUi
  have : (Module.finrank (ZMod p) (H2 (U : Subgroup G) (ZMod p)) : ℤ) = 1 := by
    push_cast at hE
    linarith
  exact_mod_cast this

end Recognition

end CohomologicalDimensionLE

end TauCeti
