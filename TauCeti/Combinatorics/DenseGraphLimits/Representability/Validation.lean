/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.Combinatorics.DenseGraphLimits.Representability.Moebius
public import TauCeti.Combinatorics.DenseGraphLimits.ExchangeableGraphLaw.Dissociated
import Mathlib.MeasureTheory.Measure.Dirac.Basic

/-!
# Adversarial checks of the Möbius calculus and the dissociation bridge

The random graph `L_f` attached to a graph parameter `f` rests on three facts about the Möbius
masses `f†` — nonnegativity, total mass one, and consistency along label injections — and on the
bridge `isDissociated_iff_upperMass_mul` between dissociation and multiplicativity of upper
masses.  The examples here compute the Möbius masses explicitly for a family of parameters, use
them to exhibit a parameter that is not reflection positive although it satisfies the other
structural conditions, and exhibit an exchangeable law that is not dissociated.

**The edge-power parameters.**  For a real `c`, the parameter `F ↦ c ^ e(F)` is isomorphism
invariant, multiplicative and normalized; for `c ∈ [0, 1]` it is the homomorphism density of the
constant graphon `c`.  Its Möbius transform is computed in closed form by the binomial theorem,
`f†(F) = c ^ e(F) * (1 - c) ^ (C(n, 2) - e(F))`: these are the binomial masses of the Erdős–Rényi
graph `G(n, c)`.  On `Fin 2` with `c = 2` they are `-1` at the
edgeless graph and `2` at the edge.  So the masses still sum to one and still restrict
consistently to `Fin 1` — the identities `graphParamMobius_sum_eq_one` and
`graphParamMobius_sum_comap`, which do not assume reflection positivity — but they are not
nonnegative, and `posSemidef_connectionMatrix_fullyLabeled_iff` then shows that this parameter
is not reflection positive.  Reflection positivity is therefore independent of the other three
structural conditions (`exists_not_isReflectionPositive`).

**A law that is not dissociated.**  The exchangeable graph law which, at every level, is the
complete or the edgeless graph with probability `1 / 2` each is not dissociated: its edges in two
disjoint windows are perfectly correlated.  Both sides of the bridge are computed directly: the two
windows of `Fin (2 + 2)` are never the edgeless graph and the edge, which has probability `1 / 4`
under the product law; and the pattern of two disjoint edges has upper mass `1 / 2`, not
`1 / 2 * 1 / 2`.

## Main definitions

* `TauCeti.DenseGraphLimits.edgePow` — the edge-power parameter `F ↦ c ^ e(F)`;
* `TauCeti.DenseGraphLimits.coinLaw` — the exchangeable graph law that is complete or edgeless with
  probability `1 / 2` each.

## Main results

* `graphParamMobius_edgePow` — the Möbius masses of `edgePow c` are binomial;
* `graphParamMobius_edgePow_two_bot`, `graphParamMobius_edgePow_two_top`,
  `graphParamMobius_edgePow_two_bot_add_top`, `graphParamMobius_edgePow_two_one_bot` — on `Fin 2`
  with `c = 2` the masses are `-1` and `2`, summing to one and restricting consistently to `Fin 1`;
* `graphParamMobius_edgePow_half` — for `c = 1 / 2` the masses are uniform;
* `TauCeti.DenseGraphLimits.exists_not_isReflectionPositive` — an isomorphism-invariant,
  multiplicative, normalized graph parameter need not be reflection positive;
* `upperMass_coinLaw_twoDisjointEdges_ne_mul` and `not_isDissociated_coinLaw` — the upper masses of
  `coinLaw` are not multiplicative, and `coinLaw` is not dissociated.

## References

* L. Lovász, B. Szegedy, *Limits of dense graph sequences*, JCTB 96 (2006), 933–957, Section 2.
* P. Diaconis, S. Janson, *Graph limits and exchangeable random graphs*, Rend. Mat. Appl. (7) 28
  (2008), 33–61, Section 5.
-/

public section

noncomputable section

open Finset MeasureTheory
open scoped ENNReal

namespace TauCeti.DenseGraphLimits

/-! ### The edge-power parameters -/

/-- The edge-power parameter `F ↦ c ^ e(F)`. -/
def edgePow (c : ℝ) : GraphParam := fun _ F ↦ c ^ Nat.card F.edgeSet

/-- The edge-power parameter evaluates to `c` raised to the number of edges. -/
@[simp] theorem edgePow_apply (c : ℝ) (n : ℕ) (F : SimpleGraph (Fin n)) :
    edgePow c n F = c ^ Nat.card F.edgeSet := (rfl)

/-- The edge-power parameter is isomorphism invariant. -/
theorem isIsoInvariant_edgePow (c : ℝ) : IsIsoInvariant (edgePow c) :=
  isIsoInvariant_iff.2 fun _ _ _ _ ⟨e⟩ ↦ by simp only [edgePow, Nat.card_congr e.mapEdgeSet]

/-- The edge-power parameter is multiplicative over disjoint unions. -/
theorem isMultiplicative_edgePow (c : ℝ) : IsMultiplicative (edgePow c) :=
  isMultiplicative_iff.2 fun _ _ F₁ F₂ ↦ by
    have h : Nat.card ((F₁ ⊕g F₂).map finSumFinEquiv.toEmbedding).edgeSet =
        Nat.card F₁.edgeSet + Nat.card F₂.edgeSet :=
      (Nat.card_congr (SimpleGraph.Iso.map finSumFinEquiv (F₁ ⊕g F₂)).mapEdgeSet).symm.trans <|
        (Nat.card_congr SimpleGraph.edgeSetSumEquiv).trans Nat.card_sum
    simp only [edgePow, h, pow_add]

/-- The edge-power parameter is normalized. -/
theorem isNormalized_edgePow (c : ℝ) : IsNormalized (edgePow c) := by
  simp [isNormalized_iff, edgePow]

/-- **The Möbius masses of the edge-power parameter are binomial**:
`f†(F) = c ^ e(F) * (1 - c) ^ (C(n, 2) - e(F))`.  By Möbius inversion it suffices that these sum to
`c ^ e(F)` over the supergraphs of `F`, which is the binomial theorem for `c + (1 - c)` over the
edges of the complete graph missing from `F`. -/
theorem graphParamMobius_edgePow (c : ℝ) (n : ℕ) (F : SimpleGraph (Fin n)) :
    graphParamMobius (edgePow c) n F =
      c ^ Nat.card F.edgeSet * (1 - c) ^ (n.choose 2 - Nat.card F.edgeSet) := by
  classical
  have hcard (G : SimpleGraph (Fin n)) : Nat.card G.edgeSet = #G.edgeFinset := by
    rw [Nat.card_eq_fintype_card, SimpleGraph.edgeFinset_card]
  have htop : n.choose 2 = #(⊤ : SimpleGraph (Fin n)).edgeFinset := by
    rw [SimpleGraph.card_edgeFinset_top_eq_card_choose_two, Fintype.card_fin]
  refine (congrFun ((eq_graphParamMobius_iff (edgePow c) fun G ↦ c ^ Nat.card G.edgeSet *
      (1 - c) ^ (n.choose 2 - Nat.card G.edgeSet)).2 fun F ↦ ?_) F).symm
  simp only [hcard, htop, edgePow]
  -- The supergraphs of `F` are the graphs between `F` and `⊤`, read through their edge sets.
  have hfilter : univ.filter (fun G : SimpleGraph (Fin n) ↦ F ≤ G) =
      univ.filter fun G ↦ F ≤ G ∧ G ≤ ⊤ := filter_congr fun G _ ↦ by simp
  rw [hfilter]
  trans ∑ s ∈ Icc F.edgeFinset (⊤ : SimpleGraph (Fin n)).edgeFinset,
    c ^ #s * (1 - c) ^ (#(⊤ : SimpleGraph (Fin n)).edgeFinset - #s)
  · -- The two sides carry different decidability instances for the filter.
    convert SimpleGraph.sum_filter_le_le_eq_sum_Icc_edgeFinset F ⊤
      fun s ↦ c ^ #s * (1 - c) ^ (#(⊤ : SimpleGraph (Fin n)).edgeFinset - #s)
  -- An edge set between `F` and `⊤` is `F`'s together with a subset of the missing edges.
  have hAB : F.edgeFinset ⊆ (⊤ : SimpleGraph (Fin n)).edgeFinset :=
    SimpleGraph.edgeFinset_mono le_top
  have hdisj : ∀ u ∈ ((⊤ : SimpleGraph (Fin n)).edgeFinset \ F.edgeFinset).powerset,
      Disjoint F.edgeFinset u := fun u hu ↦ disjoint_sdiff.mono_right (mem_powerset.1 hu)
  have hB : #(⊤ : SimpleGraph (Fin n)).edgeFinset =
      #F.edgeFinset + #((⊤ : SimpleGraph (Fin n)).edgeFinset \ F.edgeFinset) := by
    rw [card_sdiff_of_subset hAB, Nat.add_sub_cancel' (card_le_card hAB)]
  rw [Icc_eq_image_powerset hAB, sum_image fun u hu v hv huv ↦ by
    rw [← union_sdiff_cancel_left (hdisj u hu), huv, union_sdiff_cancel_left (hdisj v hv)]]
  -- Each summand is `c ^ e(F)` times a binomial term over the missing edges.
  have hterm : ∀ u ∈ ((⊤ : SimpleGraph (Fin n)).edgeFinset \ F.edgeFinset).powerset,
      c ^ #(F.edgeFinset ∪ u) * (1 - c) ^ (#(⊤ : SimpleGraph (Fin n)).edgeFinset -
        #(F.edgeFinset ∪ u)) = c ^ #F.edgeFinset *
          (c ^ #u * (1 - c) ^ (#((⊤ : SimpleGraph (Fin n)).edgeFinset \ F.edgeFinset) - #u)) :=
    fun u hu ↦ by
      rw [card_union_of_disjoint (hdisj u hu), pow_add, hB, Nat.add_sub_add_left, mul_assoc]
  -- The binomial theorem for `c + (1 - c) = 1` sums the binomial terms to one.
  rw [sum_congr rfl hterm, ← mul_sum, sum_pow_mul_eq_add_pow]
  simp

/-- On `Fin 2`, the edge-power parameter with `c = 2` has Möbius mass `-1` at the edgeless
graph. -/
theorem graphParamMobius_edgePow_two_bot :
    graphParamMobius (edgePow 2) 2 (⊥ : SimpleGraph (Fin 2)) = -1 := by
  rw [graphParamMobius_edgePow]
  norm_num

/-- On `Fin 2`, the edge-power parameter with `c = 2` has Möbius mass `2` at the edge. -/
theorem graphParamMobius_edgePow_two_top :
    graphParamMobius (edgePow 2) 2 (⊤ : SimpleGraph (Fin 2)) = 2 := by
  classical
  have h : Nat.card (⊤ : SimpleGraph (Fin 2)).edgeSet = 1 := by
    rw [Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card,
      SimpleGraph.card_edgeFinset_top_eq_card_choose_two]
    rfl
  rw [graphParamMobius_edgePow, h]
  norm_num

/-- The two computed masses sum to one, as `graphParamMobius_sum_eq_one` predicts without
reflection positivity. -/
theorem graphParamMobius_edgePow_two_bot_add_top :
    graphParamMobius (edgePow 2) 2 ⊥ + graphParamMobius (edgePow 2) 2 ⊤ = 1 := by
  rw [graphParamMobius_edgePow_two_bot, graphParamMobius_edgePow_two_top]
  norm_num

/-- The negative mass is a genuine Möbius mass of an isomorphism-invariant, multiplicative,
normalized parameter, and it is consistent: the mass of the one-vertex graph is the total mass of
the graphs on `Fin 2` restricting to it, here `-1 + 2`. -/
theorem graphParamMobius_edgePow_two_one_bot : graphParamMobius (edgePow 2) 1 ⊥ =
    graphParamMobius (edgePow 2) 2 ⊥ + graphParamMobius (edgePow 2) 2 ⊤ := by
  rw [graphParamMobius_edgePow_two_bot, graphParamMobius_edgePow_two_top, graphParamMobius_edgePow]
  norm_num

/-- For `c = 1 / 2` the masses are uniform: `G(n, 1 / 2)` is the uniform random graph. -/
theorem graphParamMobius_edgePow_half (n : ℕ) (F : SimpleGraph (Fin n)) :
    graphParamMobius (edgePow (1 / 2)) n F = (1 / 2) ^ n.choose 2 := by
  classical
  have hF : Nat.card F.edgeSet ≤ n.choose 2 := by
    rw [Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card]
    refine (card_le_card (SimpleGraph.edgeFinset_mono le_top)).trans_eq ?_
    rw [SimpleGraph.card_edgeFinset_top_eq_card_choose_two, Fintype.card_fin]
  have hhalf : (1 : ℝ) - 1 / 2 = 1 / 2 := by norm_num
  rw [graphParamMobius_edgePow, hhalf, ← pow_add, Nat.add_sub_cancel' hF]

/-- **Reflection positivity is independent of the other structural conditions.** The parameter
`F ↦ 2 ^ e(F)` is isomorphism invariant, multiplicative and normalized, but its Möbius mass at the
edgeless graph on `Fin 2` is `-1`, so its connection matrix on the fully labeled graphs on `Fin 2`
is not positive semidefinite. -/
theorem exists_not_isReflectionPositive :
    ∃ f : GraphParam, IsIsoInvariant f ∧ IsMultiplicative f ∧ IsNormalized f ∧
      ¬ IsReflectionPositive f := by
  refine ⟨edgePow 2, isIsoInvariant_edgePow 2, isMultiplicative_edgePow 2,
    isNormalized_edgePow 2, fun hrp ↦ ?_⟩
  have h := (posSemidef_connectionMatrix_fullyLabeled_iff _ (isIsoInvariant_edgePow 2) 2).1
    (hrp.posSemidef _) ⊥
  rw [graphParamMobius_edgePow_two_bot] at h
  norm_num at h

/-! ### A law that is not dissociated -/

/-- The level-`k` law that is the complete or the edgeless graph with probability `1 / 2` each. -/
def coinMeasure (k : ℕ) : Measure (SimpleGraph (Fin k)) :=
  (2⁻¹ : ℝ≥0∞) • Measure.dirac ⊥ + (2⁻¹ : ℝ≥0∞) • Measure.dirac ⊤

/-- The sum of the weighted membership indicators of `⊥` and `⊤` on `s`.
For `2 ≤ k`, their singleton masses are `1 / 2`; for `k ≤ 1`, they coincide and have mass `1`. -/
theorem coinMeasure_apply (k : ℕ) (s : Set (SimpleGraph (Fin k))) :
    coinMeasure k s = 2⁻¹ * s.indicator 1 ⊥ + 2⁻¹ * s.indicator 1 ⊤ := by
  simp [coinMeasure, Measure.dirac_apply' _ (MeasurableSet.of_discrete (s := s))]

/-- The exchangeable graph law that is complete or edgeless with probability `1 / 2` each: a
pullback of the complete graph along an injection is complete, and of the edgeless graph is
edgeless. -/
def coinLaw : ExchangeableGraphLaw where
  law := coinMeasure
  prob k := ⟨by simp [coinMeasure_apply, ENNReal.inv_two_add_inv_two]⟩
  consistent f := by
    have hf := SimpleGraph.measurable_comap (V := Fin _) ⇑f
    rw [coinMeasure, coinMeasure, Measure.map_add _ _ hf, Measure.map_smul, Measure.map_smul,
      Measure.map_dirac' hf, Measure.map_dirac' hf]
    · simp [SimpleGraph.comap_top f.injective]
    all_goals exact hf.aemeasurable

/-- The level-`k` law of `coinLaw` is `coinMeasure k`. -/
@[simp] theorem coinLaw_law (k : ℕ) : coinLaw.law k = coinMeasure k := (rfl)

/-- Every pattern other than the edgeless one has upper mass `1 / 2` under `coinLaw`: it is
contained in the complete graph but not in the edgeless one. -/
theorem upperMass_coinLaw_of_ne_bot {k : ℕ} {F : SimpleGraph (Fin k)} (hF : F ≠ ⊥) :
    coinLaw.upperMass F = 2⁻¹ := by
  rw [ExchangeableGraphLaw.upperMass_def, coinLaw_law]
  simp [coinMeasure_apply, hF, le_bot_iff]

/-- The disjoint union of two edges, as a pattern on `Fin (2 + 2)`: one edge in each of the two
windows `Fin.castAdd 2` and `Fin.natAdd 2`. -/
abbrev twoDisjointEdges : SimpleGraph (Fin (2 + 2)) :=
  ((⊤ : SimpleGraph (Fin 2)) ⊕g (⊤ : SimpleGraph (Fin 2))).map finSumFinEquiv.toEmbedding

/-- The pattern of two disjoint edges is not edgeless. -/
theorem twoDisjointEdges_ne_bot : twoDisjointEdges ≠ ⊥ := fun h ↦ by
  have hadj : twoDisjointEdges.Adj (finSumFinEquiv (Sum.inl 0)) (finSumFinEquiv (Sum.inl 1)) :=
    (SimpleGraph.map_adj _ _ _ _).2 ⟨Sum.inl 0, Sum.inl 1, by simp, rfl, rfl⟩
  rw [h] at hadj
  exact hadj

/-- **The upper masses of `coinLaw` are not multiplicative**: two disjoint edges are present with
probability `1 / 2`, not `1 / 2 * 1 / 2`. -/
theorem upperMass_coinLaw_twoDisjointEdges_ne_mul : coinLaw.upperMass twoDisjointEdges ≠
    coinLaw.upperMass (⊤ : SimpleGraph (Fin 2)) * coinLaw.upperMass (⊤ : SimpleGraph (Fin 2)) := by
  rw [upperMass_coinLaw_of_ne_bot twoDisjointEdges_ne_bot, upperMass_coinLaw_of_ne_bot top_ne_bot]
  norm_num

/-- **`coinLaw` is not dissociated, read off the definition**: the two windows of `Fin (2 + 2)`
are never the edgeless graph and the edge together, an event of probability `1 / 4` under the
product of the two marginals. -/
theorem not_isDissociated_coinLaw : ¬ coinLaw.IsDissociated := by
  intro h
  have hpair : (coinLaw.law (2 + 2)).map
        (fun G ↦ (SimpleGraph.comap (Fin.castAdd 2) G, SimpleGraph.comap (Fin.natAdd 2) G))
        {((⊥ : SimpleGraph (Fin 2)), (⊤ : SimpleGraph (Fin 2)))} =
      ((coinLaw.law 2).prod (coinLaw.law 2)) {((⊥ : SimpleGraph (Fin 2)), ⊤)} := by
    rw [(ExchangeableGraphLaw.isDissociated_iff _).1 h 2 2]
  rw [Measure.map_apply (by fun_prop) MeasurableSet.of_discrete, ← Set.singleton_prod_singleton,
    Measure.prod_prod, coinLaw_law, coinLaw_law] at hpair
  -- The complete graph has complete windows, so it is not in the event.
  have hmem : (⊤ : SimpleGraph (Fin (2 + 2))) ∉
      (fun G ↦ (G.comap (Fin.castAdd 2), G.comap (Fin.natAdd 2))) ⁻¹' {(⊥, ⊤)} := by
    simp [SimpleGraph.comap_top (Fin.castAdd_injective 2 2)]
  simp [coinMeasure_apply, Set.indicator_of_notMem hmem] at hpair

/-- **`coinLaw` is not dissociated, read off the bridge** `isDissociated_iff_upperMass_mul`, in
agreement with the direct computation `not_isDissociated_coinLaw`. -/
example : ¬ coinLaw.IsDissociated := fun h ↦ by
  have hmul := (isDissociated_iff_upperMass_mul coinLaw).1 h 2 2 ⊤ ⊤
  rw [upperMass_coinLaw_of_ne_bot twoDisjointEdges_ne_bot,
    upperMass_coinLaw_of_ne_bot top_ne_bot] at hmul
  norm_num at hmul

end TauCeti.DenseGraphLimits
