/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.Profinite.Demushkin.Character.Basic
public import TauCeti.Topology.Algebra.Group.Profinite.Demushkin.CohomologicalDimension
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.Prescription.SecondCohomology

/-!
# The second cohomology of a Demushkin group with twisted coefficients

Let `G` be an infinite Demushkin group with canonical character `χ = demushkinCharacter hG`, and
let `I(χ)/pⁱ = TauCeti.ZModTwist χ i` be the twisted coefficients `ℤ/pⁱ` on which `G` acts through
`χ`. Then `H²(G, I(χ)/pⁱ)` is cyclic of order `pⁱ`, so that `H²(G, I(χ)/pⁱ) ≅ ℤ/pⁱ`. This is the
finite-level form of the statement that the dualizing module of `G` is `ℚ_p/ℤ_p` with `G` acting
through its orientation (Serre's exposé, §9), and it is the target group of the perfect pairings
`Hʲ(G, M) × H²⁻ʲ(G, Hom(M, I(χ)/pⁱ)) → H²(G, I(χ)/pⁱ)`.

The proof assembles three facts: the canonical character has the prescription property, so
multiplication by `p` is injective on `H²(G, I(χ)/pⁱ) → H²(G, I(χ)/pⁱ⁺¹)`; `cd_p G = 2`
(`TauCeti.IsDemushkin.cohomologicalDimensionAt_eq_two`), so the reductions on `H²` are surjective;
and `H²(G, I(χ)/p) = H²(G, 𝔽_p)` has order `p`, because the action of a pro-`p` group on `I(χ)/p`
is trivial. The general argument is
`TauCeti.HasPrescriptionProperty.isAddCyclic_H2_zModTwist` and its companions.

## Main results

* `TauCeti.IsDemushkin.natCard_H2_zModTwist_demushkinCharacter_one`: `H²(G, I(χ)/p)` has order `p`,
  for every Demushkin group.
* `TauCeti.IsDemushkin.surjective_explicitCoeff2_reduce_demushkinCharacter`: for an infinite
  Demushkin group, every reduction `H²(G, I(χ)/pⁿ) → H²(G, I(χ)/pʲ)` is surjective.
* `TauCeti.IsDemushkin.natCard_H2_zModTwist_demushkinCharacter`,
  `TauCeti.IsDemushkin.isAddCyclic_H2_zModTwist_demushkinCharacter`,
  `TauCeti.IsDemushkin.nonempty_addEquiv_H2_zModTwist_demushkinCharacter_zmod`: for an infinite
  Demushkin group, `H²(G, I(χ)/pⁱ)` is cyclic of order `pⁱ`, isomorphic to `ℤ/pⁱ`.
* `TauCeti.IsDemushkin.moduleBaer_H2_zModTwist_demushkinCharacter`: for an infinite Demushkin
  group, `H²(G, I(χ)/pⁱ)` satisfies Baer's criterion over `ℤ/pⁱ`.
* `TauCeti.IsDemushkin.exists_explicitCoeff2_mulPow_eq_of_nsmul_eq_zero`: for an infinite Demushkin
  group, the `pⁱ`-torsion of `H²(G, I(χ)/pⁱ⁺ʲ)` is the image of `H²(G, I(χ)/pⁱ)` under
  multiplication by `pʲ`.

## References

* J.-P. Serre, *Structure de certains pro-p-groupes (d'après Demuškin)*, Séminaire Bourbaki 8
  (1962/63), exposé 252, §9.
* J. P. Labute, *Classification of Demushkin groups*, Canad. J. Math. 19 (1967), 106–132, §2.
-/

public section

namespace TauCeti

open ContCohomology

universe u

-- Preferring the ring path keeps a single additive structure on `ZMod p`, so that the explicit
-- `H²(G, 𝔽_p)` below is the one `TauCeti.natCard_H2_eq_pow_finrank_cohomFp_two` is stated against.
attribute [local instance 2000] Ring.toAddCommGroup

variable {p : ℕ} [Fact p.Prime] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TotallyDisconnectedSpace G] (hG : IsDemushkin p G)

namespace IsDemushkin

include hG

/-- **`H²(G, I(χ)/p)` has order `p`** for a Demushkin group `G` with canonical character `χ`: a
pro-`p` group acts trivially on the bottom level `I(χ)/p`, which is therefore `𝔽_p`, and
`H²(G, 𝔽_p)` is one-dimensional. -/
theorem natCard_H2_zModTwist_demushkinCharacter_one :
    Nat.card (H2 G (ZModTwist (demushkinCharacter hG) 1)) = p := by
  -- The explicit `H²(G, 𝔽_p)` needs an action of `G` on `𝔽_p`; the trivial one is installed.
  let : DistribMulAction G (ZMod p) := DistribMulAction.compHom (ZMod p) (1 : G →* (ZMod p)ˣ)
  have htriv : ∀ (g : G) (m : ZMod p), g • m = m := fun _ m ↦ one_smul (ZMod p)ˣ m
  have : ContinuousSMul G (ZMod p) := ⟨continuous_snd.congr fun x ↦ (htriv x.1 x.2).symm⟩
  have : Module.Finite (ZMod p) (cohomFp p G 2) :=
    Module.finite_of_finrank_eq_succ hG.finrank_cohomFp_two
  let e : ZModTwist (demushkinCharacter hG) 1 ≃+ ZMod p :=
    (ZModTwist.equiv _ 1).trans (ZMod.ringEquivCongr (pow_one p)).toAddEquiv
  rw [Nat.card_congr (explicitCoeff2Equiv G (ZModTwist (demushkinCharacter hG) 1) e
      continuous_of_discreteTopology continuous_of_discreteTopology fun g m ↦ by
        rw [hG.isProP.smul_zModTwist_one_eq_self, htriv]).toEquiv,
    natCard_H2_eq_pow_finrank_cohomFp_two p G htriv, hG.finrank_cohomFp_two, pow_one]

variable [Infinite G]

/-- **`H²` is right exact on the twisted coefficients of an infinite Demushkin group**: every
reduction `H²(G, I(χ)/pⁿ) → H²(G, I(χ)/pʲ)`, `j ≤ n`, is surjective, because `cd_p G = 2`. -/
theorem surjective_explicitCoeff2_reduce_demushkinCharacter {j n : ℕ} (hj : j ≤ n) :
    Function.Surjective (explicitCoeff2 G (ZModTwist (demushkinCharacter hG) n)
      (ZModTwist.reduce _ hj) continuous_of_discreteTopology) :=
  ZModTwist.surjective_explicitCoeff2_reduce_of_cohomologicalDimensionAt_le_two _
    hG.cohomologicalDimensionAt_eq_two.le hj

/-- **The order of `H²(G, I(χ)/pⁱ)`** for an infinite Demushkin group `G` with canonical character
`χ`: it is `pⁱ`. -/
theorem natCard_H2_zModTwist_demushkinCharacter (i : ℕ) :
    Nat.card (H2 G (ZModTwist (demushkinCharacter hG) i)) = p ^ i :=
  (hasPrescriptionProperty_demushkinCharacter hG).natCard_H2_zModTwist
    (fun _ ↦ hG.surjective_explicitCoeff2_reduce_demushkinCharacter _)
    hG.natCard_H2_zModTwist_demushkinCharacter_one i


/-- **`H²(G, I(χ)/pⁱ)` is cyclic** for an infinite Demushkin group `G` with canonical character
`χ`. -/
theorem isAddCyclic_H2_zModTwist_demushkinCharacter (i : ℕ) :
    IsAddCyclic (H2 G (ZModTwist (demushkinCharacter hG) i)) :=
  (hasPrescriptionProperty_demushkinCharacter hG).isAddCyclic_H2_zModTwist
    (fun _ ↦ hG.surjective_explicitCoeff2_reduce_demushkinCharacter _)
    hG.natCard_H2_zModTwist_demushkinCharacter_one i


/-- **`H²(G, I(χ)/pⁱ) ≅ ℤ/pⁱ`** for an infinite Demushkin group `G` with canonical character `χ`:
the top cohomology of the twisted coefficients at level `i` is cyclic of order `pⁱ`. -/
theorem nonempty_addEquiv_H2_zModTwist_demushkinCharacter_zmod (i : ℕ) :
    Nonempty (H2 G (ZModTwist (demushkinCharacter hG) i) ≃+ ZMod (p ^ i)) :=
  (hasPrescriptionProperty_demushkinCharacter hG).nonempty_addEquiv_H2_zModTwist_zmod
    (fun _ ↦ hG.surjective_explicitCoeff2_reduce_demushkinCharacter _)
    hG.natCard_H2_zModTwist_demushkinCharacter_one i


/-- **`H²(G, I(χ)/pⁱ)` is self-injective over `ℤ/pⁱ`** for an infinite Demushkin group `G` with
canonical character `χ`: being `ℤ/pⁱ`, it satisfies Baer's criterion over `ℤ/pⁱ`, so that
`Hom(-, H²(G, I(χ)/pⁱ))` is exact on the groups killed by `pⁱ`. -/
theorem moduleBaer_H2_zModTwist_demushkinCharacter (i : ℕ) :
    Module.Baer (ZMod (p ^ i)) (H2 G (ZModTwist (demushkinCharacter hG) i)) :=
  (hasPrescriptionProperty_demushkinCharacter hG).moduleBaer_H2_zModTwist
    (fun _ ↦ hG.surjective_explicitCoeff2_reduce_demushkinCharacter _)
    hG.natCard_H2_zModTwist_demushkinCharacter_one i

/-- **The `pⁱ`-torsion of `H²(G, I(χ)/pⁿ)` is the image of `H²(G, I(χ)/pⁱ)`**, for `i + j = n` and
an infinite Demushkin group `G` with canonical character `χ`: multiplication by `pʲ` is injective on
`H²` by the prescription property, its image lies in the `pⁱ`-torsion, and the `pⁱ`-torsion of the
cyclic group `H²(G, I(χ)/pⁿ)` has at most `pⁱ` elements. -/
theorem exists_explicitCoeff2_mulPow_eq_of_nsmul_eq_zero {i j n : ℕ} (h : i + j = n)
    {y : H2 G (ZModTwist (demushkinCharacter hG) n)} (hy : p ^ i • y = 0) :
    ∃ x, explicitCoeff2 G (ZModTwist (demushkinCharacter hG) i)
      (ZModTwist.mulPow (demushkinCharacter hG) h) continuous_of_discreteTopology x = y := by
  classical
  have hp : p.Prime := Fact.out
  set F := explicitCoeff2 G (ZModTwist (demushkinCharacter hG) i)
    (ZModTwist.mulPow (demushkinCharacter hG) h) continuous_of_discreteTopology
  have hinj : Function.Injective F :=
    (hasPrescriptionProperty_demushkinCharacter hG).injective_explicitCoeff2_mulPow h
  have : Finite (H2 G (ZModTwist (demushkinCharacter hG) n)) :=
    Nat.finite_of_card_ne_zero ((hG.natCard_H2_zModTwist_demushkinCharacter n).trans_ne
      (pow_ne_zero n hp.ne_zero))
  have := hG.isAddCyclic_H2_zModTwist_demushkinCharacter n
  let := Fintype.ofFinite (H2 G (ZModTwist (demushkinCharacter hG) n))
  -- the image of `F` lies in the `pⁱ`-torsion `T`, which has at most `pⁱ` elements
  set T : Finset (H2 G (ZModTwist (demushkinCharacter hG) n)) := {z | p ^ i • z = 0} with hT
  have hsub : Set.range F ⊆ ↑T := by
    rintro _ ⟨x, rfl⟩
    simp only [hT, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq]
    rw [← map_nsmul, nsmul_H2_eq_zero (ZModTwist.pow_nsmul_eq_zero _ i), map_zero]
  have hcard : (T : Set (H2 G (ZModTwist (demushkinCharacter hG) n))).ncard ≤
      (Set.range F).ncard := by
    rw [Set.ncard_coe_finset, Set.ncard_range_of_injective hinj,
      hG.natCard_H2_zModTwist_demushkinCharacter i]
    exact IsAddCyclic.card_nsmul_eq_zero_le (pow_pos hp.pos i)
  have hy' : y ∈ Set.range F := by
    rw [Set.eq_of_subset_of_ncard_le hsub hcard]
    simpa [hT] using hy
  exact hy'

end IsDemushkin

end TauCeti
