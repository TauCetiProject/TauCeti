/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Hypergraph.Polyad.Energy.Gap
public import TauCeti.Combinatorics.Hypergraph.Triadic.Basic

/-!
# Top regularity over a coarse skeleton from a small energy gap

Let the lower skeleton of `D` refine that of `C`. This file shows that a coloring `H` which is
top-regular over most fine polyads is also top-regular over most coarse polyads as soon as the
polyad energy gap between the two skeletons is small. Slicing
(`Colored3Graph.TopRegularOverMostPolyads.of_refinement`) passes top regularity in the other
direction, from coarse polyads to their large fine children.

Each irregular coarse polyad is charged, through the local criterion
`Colored3Graph.isTopRegularOverPolyad_of_sum_coarsen_le`, to its irregular fine children and to
the support-weighted deviations of the fine densities from the coarse ones. By
`Colored3Graph.sum_card_support_mul_abs_relativeDensity_coarsen_le`, if
`H.polyadEnergy D.skeleton - H.polyadEnergy C.skeleton ≤ g`, each color has total deviation at
most `√g |V| (|V| - 1) (|V| - 2)`. Summing the charges gives, for polyad decompositions,

`H.exceptionalPolyadMass C δ r ≤ (H.exceptionalPolyadMass D η r + q √g) / (δ² - η)`,

where `q` is the number of top colors
(`Colored3Graph.exceptionalPolyadMass_le_of_polyadEnergy_sub_le`).

The coarse tolerance `δ` only has to satisfy `δ² > η` and to dominate the energy gap, so it can be
prescribed in terms of the complexity of the coarse skeleton alone. This is the mechanism behind
strong regularity: after iterating energy increments until the gap between two consecutive
skeletons is small compared with a schedule evaluated at the complexity of the coarser one, the
coarser skeleton is top-regular at that scheduled tolerance. A refinement
of the pair palette alone, as produced by `Colored3Graph.exists_topRegularOverMostPolyads`, is
one instance of the refinement hypothesis.

## Main results

* `TauCeti.Colored3Graph.exceptionalPolyadMass_le_of_polyadEnergy_sub_le`: the coarse
  exceptional mass is controlled by the fine exceptional mass and the polyad energy gap.
* `TauCeti.Colored3Graph.TopRegularOverMostPolyads.of_polyadEnergy_sub_le`: the same estimate
  for top regularity over most polyads.

## References

* V. Rödl and M. Schacht, *Regular partitions of hypergraphs: regularity lemmas*,
  Combin. Probab. Comput. 16 (2007).
* N. Alon, E. Fischer, M. Krivelevich and M. Szegedy, *Efficient testing of large graphs*,
  Combinatorica 20 (2000), the strong regularity lemma.
* T. Tao, *Szemerédi's regularity lemma revisited*, Contrib. Discrete Math. 1 (2006), the
  energy-gap stopping argument.
-/

public section

open Finset

namespace TauCeti.Colored3Graph

variable {κ V : Type*} [Fintype V] [DecidableEq V] [DecidableEq κ]
  {H : Colored3Graph κ V} {C D : TriadicComplex3 V} {η δ : ℝ} {r : ℕ}

open Classical in
/-- **Exceptional mass from an energy gap.** Let the skeleton of `D` refine that of `C` along the
color map `f`, both selecting polyad decompositions, and let the polyad energy gap of `H` between
them be at most `g`. If `0 ≤ η < δ²` and `0 < δ`, the proportion of the support carried by the
coarse polyads over which `H` is not `(δ, r)`-top-regular is at most
`(μ + q √g) / (δ² - η)`, where `μ` is the corresponding fine proportion at `(η, r)` and `q` is the
number of top colors. -/
theorem exceptionalPolyadMass_le_of_polyadEnergy_sub_le [Fintype κ]
    (hC : C.IsPolyadDecomposition) (hD : D.IsPolyadDecomposition)
    (hV : D.skeleton.vertexPart ≤ C.skeleton.vertexPart)
    (f : Fin D.pairColorCount → Fin C.pairColorCount)
    (hf : ∀ p, C.skeleton.pairColors.color p = f (D.skeleton.pairColors.color p)) {g : ℝ}
    (hgap : H.polyadEnergy D.skeleton - H.polyadEnergy C.skeleton ≤ g)
    (hη : 0 ≤ η) (hδ : 0 < δ) (hηδ : η < δ ^ 2) :
    H.exceptionalPolyadMass C δ r ≤
      (H.exceptionalPolyadMass D η r + Fintype.card κ * √g) / (δ ^ 2 - η) := by
  set θ := δ ^ 2 - η with hθdef
  have hθ : 0 < θ := sub_pos.2 hηδ
  set N : ℝ := ((Fintype.card V).descFactorial 3 : ℝ)
  -- The irregular fine support and the deviation of each color, collected by coarse parent.
  let irr (P : Polyad3 C.skeleton) : ℝ :=
    ∑ Q : Polyad3 D.skeleton with Q.coarsen hV f = P ∧ ¬H.IsTopRegularOverPolyad Q η r,
      (#Q.support : ℝ)
  let dev (c : κ) (P : Polyad3 C.skeleton) : ℝ :=
    ∑ Q : Polyad3 D.skeleton with Q.coarsen hV f = P,
      #Q.support * |(H.relativeDensity c Q : ℝ) - H.relativeDensity c P|
  have hdev₀ (c : κ) (P : Polyad3 C.skeleton) : 0 ≤ dev c P :=
    sum_nonneg fun _ _ ↦ mul_nonneg (Nat.cast_nonneg _) (abs_nonneg _)
  -- Every irregular coarse polyad is charged to its irregular children and deviations.
  have hcharge (P : Polyad3 C.skeleton) :
      (if ¬H.IsTopRegularOverPolyad P δ r then θ * #P.support else 0) ≤
        irr P + ∑ c, dev c P := by
    by_cases hP : H.IsTopRegularOverPolyad P δ r
    · simp only [hP, not_true_eq_false, ↓reduceIte]
      exact add_nonneg (sum_nonneg fun _ _ ↦ Nat.cast_nonneg _) (sum_nonneg fun c _ ↦ hdev₀ c P)
    · simp only [hP, not_false_eq_true, ↓reduceIte]
      -- The local criterion is stated with classical decidability of the parent condition,
      -- whereas `irr` and `dev` use the decidable equality of polyads; `convert` bridges them.
      have : ¬∀ c, irr P + dev c P ≤ θ * #P.support := fun h ↦
        hP (isTopRegularOverPolyad_of_sum_coarsen_le hV f hf hη hδ (θ := θ)
          (by rw [hθdef, add_sub_cancel])
          fun c ↦ by convert h c)
      obtain ⟨c, hc⟩ := not_forall.1 this
      exact (not_le.1 hc).le.trans
        (add_le_add le_rfl (single_le_sum (fun c _ ↦ hdev₀ c P) (mem_univ c)))
  have hirr : ∑ P, irr P =
      ∑ Q : Polyad3 D.skeleton with ¬H.IsTopRegularOverPolyad Q η r, (#Q.support : ℝ) := by
    rw [sum_filter, ← sum_fiberwise univ (fun Q : Polyad3 D.skeleton ↦ Q.coarsen hV f)]
    refine sum_congr rfl fun P _ ↦ ?_
    rw [← sum_filter, filter_filter]
  have hdev (c : κ) : ∑ P, dev c P ≤ √g * N := by
    refine le_of_eq_of_le ?_ (sum_card_support_mul_abs_relativeDensity_coarsen_le hV f hf hgap c)
    rw [← sum_fiberwise univ (fun Q : Polyad3 D.skeleton ↦ Q.coarsen hV f)]
    refine sum_congr rfl fun P _ ↦ sum_congr rfl fun Q hQ ↦ ?_
    rw [(mem_filter.1 hQ).2]
  -- Summing the charges over the coarse polyads.
  have htotal : θ * ∑ P : Polyad3 C.skeleton with ¬H.IsTopRegularOverPolyad P δ r,
      (#P.support : ℝ) ≤
      ∑ Q : Polyad3 D.skeleton with ¬H.IsTopRegularOverPolyad Q η r, (#Q.support : ℝ) +
        Fintype.card κ * (√g * N) := by
    rw [mul_sum, sum_filter]
    calc _ ≤ ∑ P, (irr P + ∑ c, dev c P) := sum_le_sum fun P _ ↦ by
            simpa only [apply_ite (θ * ·), mul_zero] using hcharge P
      _ = ∑ P, irr P + ∑ c, ∑ P, dev c P := by rw [sum_add_distrib, sum_comm]
      _ ≤ _ := by
          rw [hirr]
          grw [sum_le_sum fun c _ ↦ hdev c]
          simp
  rw [exceptionalPolyadMass_eq_sum_div hC, exceptionalPolyadMass_eq_sum_div hD]
  obtain hN | hN := (Nat.cast_nonneg (α := ℝ) ((Fintype.card V).descFactorial 3)).eq_or_lt
  · rw [← hN, div_zero, div_zero, zero_add]
    positivity
  · rw [div_le_div_iff₀ hN hθ, add_mul, div_mul_cancel₀ _ hN.ne']
    nlinarith

/-- **Top regularity over most coarse polyads.** If `H` is `(η, r)`-top-regular over all fine
polyads of `D` outside a `μ`-proportion of the support, and the polyad energy gap between the
skeletons of `D` and of the coarser `C` is at most `g`, then for `0 ≤ η < δ²` and `0 < δ`, `H` is
`(δ, r)`-top-regular over all coarse polyads outside a `(μ + q √g) / (δ² - η)`-proportion, where
`q` is the number of top colors. -/
theorem TopRegularOverMostPolyads.of_polyadEnergy_sub_le [Fintype κ] {μ : ℝ}
    (h : H.TopRegularOverMostPolyads D η μ r)
    (hC : C.IsPolyadDecomposition) (hD : D.IsPolyadDecomposition)
    (hV : D.skeleton.vertexPart ≤ C.skeleton.vertexPart)
    (f : Fin D.pairColorCount → Fin C.pairColorCount)
    (hf : ∀ p, C.skeleton.pairColors.color p = f (D.skeleton.pairColors.color p)) {g : ℝ}
    (hgap : H.polyadEnergy D.skeleton - H.polyadEnergy C.skeleton ≤ g)
    (hη : 0 ≤ η) (hδ : 0 < δ) (hηδ : η < δ ^ 2) :
    H.TopRegularOverMostPolyads C δ ((μ + Fintype.card κ * √g) / (δ ^ 2 - η)) r := by
  refine topRegularOverMostPolyads_iff.2
    ((exceptionalPolyadMass_le_of_polyadEnergy_sub_le hC hD hV f hf hgap hη hδ hηδ).trans ?_)
  exact div_le_div_of_nonneg_right (by linarith [topRegularOverMostPolyads_iff.1 h])
    (sub_pos.2 hηδ).le

end TauCeti.Colored3Graph
