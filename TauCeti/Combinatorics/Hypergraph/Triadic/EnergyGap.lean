/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Hypergraph.Polyad.Coarsening
public import TauCeti.Combinatorics.Hypergraph.Polyad.Energy
public import TauCeti.Combinatorics.Hypergraph.Triadic.Basic

/-!
# Top regularity over a coarse skeleton from a small energy gap

Let the lower skeleton `T` refine `S`: its vertex cells refine those of `S`, and its pair colors
determine those of `S` through a map `f`. Every polyad `Q` over `T` then lies in its coarse
parent `Q.coarsen hV f` over `S`, and the fine supports with a given parent partition the support
of that parent. This file shows that a coloring `H` which is top-regular over most fine polyads
is also top-regular over most coarse polyads as soon as the polyad energy gap between `T` and `S`
is small. Slicing (`Colored3Graph.TopRegularOverMostPolyads.of_refinement`) passes top regularity
in the other direction, from coarse polyads to their large fine children.

Locally, fix a coarse polyad `P`, a top color `c`, and a union `U` of at most `r` subpolyads of
`P`. Its intersection with each fine child `Q` is a union of at most `r` subpolyads of `Q`, so on
the children over which `H` is `(η, r)`-top-regular the count of `c` on `U ∩ Q` is within
`η |Q|` of the count predicted by the density of `c` over `Q`. Replacing these fine densities by
the coarse one costs the support-weighted deviation `∑ Q, |Q| |d(c | Q) - d(c | P)|`, and the
irregular children cost their support. If these two costs together are at most `θ |P|` for
every color and `η + θ ≤ δ²`, then `H` is `(δ, r)`-top-regular over `P`
(`Colored3Graph.isTopRegularOverPolyad_of_sum_coarsen_le`).

Globally, the support-weighted deviations of all colors are controlled by the energy gap: if
`H.polyadEnergy T - H.polyadEnergy S ≤ g`, each color has total deviation at most
`√g |V| (|V| - 1) (|V| - 2)` (`Colored3Graph.polyadDensityDeviation_abs_le`). Charging every
irregular coarse polyad to its deviations and irregular children gives, for polyad
decompositions,

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

* `TauCeti.Colored3Graph.isTopRegularOverPolyad_of_sum_coarsen_le`: top regularity over a coarse
  polyad from top regularity over most of its fine children with nearly equal densities.
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

open Subpolyad3

variable {κ κ₂ κ₂' V : Type*} [Fintype V] [DecidableEq V] [DecidableEq κ]
  {H : Colored3Graph κ V} {S : PairSkeleton3 κ₂ V} {T : PairSkeleton3 κ₂' V} {η δ θ : ℝ} {r : ℕ}

/-- The count-scaled deviation of a color density on a finite set of injective triples splits
over the polyads of any lower skeleton. -/
private theorem relDensityOn_sub_mul_card_eq_sum [Fintype κ₂'] (c : κ)
    (s : Finset {x : Fin 3 → V // Function.Injective x}) (a : ℝ) :
    ((H.relDensityOn c s : ℝ) - a) * #s =
      ∑ Q : Polyad3 T, ((H.relDensityOn c (s ∩ Q.support) : ℝ) - a) * #(s ∩ Q.support) := by
  have hcount (t : Finset {x : Fin 3 → V // Function.Injective x}) :
      (H.relDensityOn c t : ℝ) * #t =
        #{x ∈ t | H.color (Set.powersetCard.ofFinEmb 3 V ⟨x.1, x.2⟩) = c} := by
    exact_mod_cast H.relDensityOn_mul_card c t
  simp_rw [sub_mul, hcount, ← filter_inter]
  rw [sum_sub_distrib, ← mul_sum, ← Nat.cast_sum, ← Nat.cast_sum, Polyad3.sum_card_inter_support,
    Polyad3.sum_card_inter_support]

open Classical in
/-- On a single fine polyad `Q`, the count-scaled deviation from a constant `a` of the density of
a color on the part of a union of subpolyads lying in `Q` is at most `η |Q|`, plus `|Q|` if `H`
is not `(η, r)`-top-regular over `Q`, plus `|Q|` times the deviation of the density over `Q`
from `a`. -/
private theorem abs_relDensityOn_inter_sub_mul_card_le (hη : 0 ≤ η) {P : Polyad3 S}
    (U : Fin r → Subpolyad3 P) (Q : Polyad3 T) (c : κ) (a : ℝ) :
    |((H.relDensityOn c (unionSupport U ∩ Q.support) : ℝ) - a) *
        #(unionSupport U ∩ Q.support)| ≤
      η * #Q.support + (if ¬H.IsTopRegularOverPolyad Q η r then (#Q.support : ℝ) else 0) +
        #Q.support * |(H.relativeDensity c Q : ℝ) - a| := by
  set W := unionSupport U ∩ Q.support
  have hWQ : (#W : ℝ) ≤ #Q.support := by exact_mod_cast card_le_card inter_subset_right
  have hW₀ : (0 : ℝ) ≤ #W := Nat.cast_nonneg _
  -- First compare the density on `W` with the density over `Q`.
  have hloc : |(H.relDensityOn c W : ℝ) - H.relativeDensity c Q| * #W ≤
      η * #Q.support + (if ¬H.IsTopRegularOverPolyad Q η r then (#Q.support : ℝ) else 0) := by
    split_ifs with hreg
    · -- The part of `U` in `Q` is the union of the restricted family.
      have := hreg.abs_relDensityOn_unionSupport_sub_mul_card_le_of_card_le c
        (Fintype.card_fin r).le fun i ↦ (U i).restrict Q
      rw [unionSupport_restrict] at this
      linarith
    · have h₀ : (0 : ℝ) ≤ H.relDensityOn c W := mod_cast H.relDensityOn_nonneg c W
      have h₁ : (H.relDensityOn c W : ℝ) ≤ 1 := mod_cast H.relDensityOn_le_one c W
      have h₀' : (0 : ℝ) ≤ H.relativeDensity c Q := mod_cast H.relativeDensity_nonneg c Q
      have h₁' : (H.relativeDensity c Q : ℝ) ≤ 1 := mod_cast H.relativeDensity_le_one c Q
      have hd : |(H.relDensityOn c W : ℝ) - H.relativeDensity c Q| ≤ 1 :=
        abs_sub_le_iff.2 ⟨by linarith, by linarith⟩
      nlinarith [mul_le_mul_of_nonneg_right hd hW₀,
        mul_nonneg hη (Nat.cast_nonneg (α := ℝ) #Q.support)]
  calc _ = |((H.relDensityOn c W : ℝ) - H.relativeDensity c Q) * #W +
          ((H.relativeDensity c Q : ℝ) - a) * #W| := by ring_nf
    _ ≤ |(H.relDensityOn c W : ℝ) - H.relativeDensity c Q| * #W +
          |(H.relativeDensity c Q : ℝ) - a| * #W := by
        grw [abs_add_le, abs_mul, abs_mul, abs_of_nonneg hW₀]
    _ ≤ _ := add_le_add hloc (by
        rw [mul_comm]
        exact mul_le_mul_of_nonneg_right hWQ (abs_nonneg _))

open Classical in
/-- **Top regularity over a coarse polyad.** Let the skeleton `T` refine `S` along the color map
`f`, and let `P` be a polyad over `S`. Suppose that for every top color `c`, the fine children
`Q` of `P` over which `H` is not `(η, r)`-top-regular, together with the support-weighted
deviation `∑ Q, |Q| |d(c | Q) - d(c | P)|` of the fine densities of `c` from the coarse one,
cost at most `θ |P|`. If `η + θ ≤ δ²`, then `H` is `(δ, r)`-top-regular over `P`. -/
theorem isTopRegularOverPolyad_of_sum_coarsen_le [Fintype κ₂']
    (hV : T.vertexPart ≤ S.vertexPart) (f : κ₂' → κ₂)
    (hf : ∀ p, S.pairColors.color p = f (T.pairColors.color p)) {P : Polyad3 S}
    (hη : 0 ≤ η) (hδ : 0 < δ) (hηθ : η + θ ≤ δ ^ 2)
    (hP : ∀ c, ∑ Q : Polyad3 T with Q.coarsen hV f = P ∧ ¬H.IsTopRegularOverPolyad Q η r,
        (#Q.support : ℝ) +
      ∑ Q : Polyad3 T with Q.coarsen hV f = P,
        #Q.support * |(H.relativeDensity c Q : ℝ) - H.relativeDensity c P| ≤ θ * #P.support) :
    H.IsTopRegularOverPolyad P δ r := by
  rw [isTopRegularOverPolyad_iff]
  intro c U hU
  set W := unionSupport U
  -- A fine polyad with another coarse parent misses the support of `P`.
  have hmiss (Q : Polyad3 T) (hQ : Q.coarsen hV f ≠ P) : W ∩ Q.support = ∅ := by
    refine disjoint_iff_inter_eq_empty.1 ((Polyad3.pairwise_disjoint_support hQ.symm).mono
      (unionSupport_subset U) (Polyad3.support_subset_coarsen hV f hf Q))
  have hcount : |(H.relDensityOn c W : ℝ) - H.relativeDensity c P| * #W ≤ δ * #W := by
    calc _ = |∑ Q : Polyad3 T, ((H.relDensityOn c (W ∩ Q.support) : ℝ) -
            H.relativeDensity c P) * #(W ∩ Q.support)| := by
          rw [← relDensityOn_sub_mul_card_eq_sum, abs_mul, Nat.abs_cast]
      _ ≤ ∑ Q : Polyad3 T with Q.coarsen hV f = P, (η * #Q.support +
            (if ¬H.IsTopRegularOverPolyad Q η r then (#Q.support : ℝ) else 0) +
            #Q.support * |(H.relativeDensity c Q : ℝ) - H.relativeDensity c P|) := by
          rw [sum_filter]
          refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun Q _ ↦ ?_)
          by_cases hQ : Q.coarsen hV f = P
          · simpa only [hQ, ↓reduceIte] using abs_relDensityOn_inter_sub_mul_card_le hη U Q c _
          · simp [hQ, hmiss Q hQ]
      _ = η * #P.support +
            (∑ Q : Polyad3 T with Q.coarsen hV f = P ∧ ¬H.IsTopRegularOverPolyad Q η r,
              (#Q.support : ℝ) +
            ∑ Q : Polyad3 T with Q.coarsen hV f = P,
              #Q.support * |(H.relativeDensity c Q : ℝ) - H.relativeDensity c P|) := by
          rw [sum_add_distrib, sum_add_distrib, ← mul_sum, ← sum_filter, filter_filter, add_assoc]
          congr 2
          exact_mod_cast Polyad3.sum_card_support_coarsen hV f hf P
      _ ≤ δ * (δ * #P.support) := by nlinarith [hP c, (Nat.cast_nonneg #P.support : (0 : ℝ) ≤ _)]
      _ ≤ δ * #W := mul_le_mul_of_nonneg_left hU hδ.le
  obtain hW | hW := (Nat.cast_nonneg (α := ℝ) #W).eq_or_lt
  · -- An empty test set passes the size threshold only over a polyad with empty support.
    have hW' : W = ∅ := card_eq_zero.1 (by exact_mod_cast hW.symm)
    have hP' : P.support = ∅ := by
      have := nonpos_of_mul_nonpos_right (hU.trans hW.symm.le) hδ
      exact card_eq_zero.1 (by exact_mod_cast this.antisymm (Nat.cast_nonneg _))
    rw [hW', relDensityOn_empty, H.relativeDensity_of_support_eq_empty c hP']
    simpa using hδ.le
  · exact le_of_mul_le_mul_right hcount hW

open Classical in
/-- The support-weighted deviation of the fine densities of a color from the coarse ones is at
most `√g` times the number of injective triples when the polyad energy gap is at most `g`. -/
private theorem sum_card_support_mul_abs_relativeDensity_coarsen_le [Fintype κ] [Fintype κ₂']
    (hV : T.vertexPart ≤ S.vertexPart) (f : κ₂' → κ₂)
    (hf : ∀ p, S.pairColors.color p = f (T.pairColors.color p)) {g : ℝ}
    (hgap : H.polyadEnergy T - H.polyadEnergy S ≤ g) (c : κ) :
    ∑ Q : Polyad3 T, #Q.support *
        |(H.relativeDensity c Q : ℝ) - H.relativeDensity c (Q.coarsen hV f)| ≤
      √g * (Fintype.card V).descFactorial 3 := by
  have h := H.polyadDensityDeviation_abs_le (S := S) (T := T)
    (fun x y hxy ↦ by rw [← Polyad3.coarsen_ofTriple hV f hf x, hxy,
      Polyad3.coarsen_ofTriple hV f hf y]) hgap c
  simp_rw [← Polyad3.coarsen_ofTriple hV f hf] at h
  rw [Polyad3.sum_comp_ofTriple
    (fun Q ↦ |(H.relativeDensity c Q : ℝ) - H.relativeDensity c (Q.coarsen hV f)|)] at h
  simpa only [nsmul_eq_mul] using h

variable {C D : TriadicComplex3 V}

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
