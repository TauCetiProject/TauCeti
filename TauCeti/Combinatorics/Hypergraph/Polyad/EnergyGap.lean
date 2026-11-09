/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Hypergraph.Polyad.Coarsening
public import TauCeti.Combinatorics.Hypergraph.Polyad.Energy
public import TauCeti.Combinatorics.Hypergraph.Polyad.TopRegular

/-!
# Top regularity over a coarse polyad from nearly equal fine densities

Let the lower skeleton `T` refine `S`: its vertex cells refine those of `S`, and its pair colors
determine those of `S` through a map `f`. Every polyad `Q` over `T` then lies in its coarse
parent `Q.coarsen hV f` over `S`, and the fine supports with a given parent partition the support
of that parent.

Fix a coarse polyad `P`, a top color `c`, and a union `U` of at most `r` subpolyads of `P`. Its
intersection with each fine child `Q` is a union of at most `r` subpolyads of `Q`, so on the
children over which `H` is `(η, r)`-top-regular the count of `c` on `U ∩ Q` is within `η |Q|` of
the count predicted by the density of `c` over `Q`. Replacing these fine densities by the coarse
one costs the support-weighted deviation `∑ Q, |Q| |d(c | Q) - d(c | P)|`, and the irregular
children cost their support. If these two costs together are at most `θ |P|` for every color and
`η + θ ≤ δ²`, then `H` is `(δ, r)`-top-regular over `P`.

The support-weighted deviations over all coarse polyads are controlled by the polyad energy gap:
if `H.polyadEnergy T - H.polyadEnergy S ≤ g`, each color has total deviation at most
`√g |V| (|V| - 1) (|V| - 2)`. The slicing lemma
(`TauCeti.Colored3Graph.IsTopRegularOverPolyad.of_pairSupport_subset`) passes top regularity in
the other direction, from a coarse polyad to its large fine children.

## Main results

* `TauCeti.Colored3Graph.isTopRegularOverPolyad_of_sum_coarsen_le`: top regularity over a coarse
  polyad from top regularity over most of its fine children with nearly equal densities.
* `TauCeti.Colored3Graph.sum_card_support_mul_abs_relativeDensity_coarsen_le`: the
  support-weighted deviation of the fine densities from the coarse ones is controlled by the
  polyad energy gap (via `TauCeti.Colored3Graph.polyadDensityDeviation_abs_le`).

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
    · refine (mul_le_mul_of_nonneg_right
        (H.abs_relDensityOn_sub_relativeDensity_le_one c W Q) hW₀).trans ?_
      linarith [mul_nonneg hη (Nat.cast_nonneg (α := ℝ) #Q.support)]
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
          rw [← H.relDensityOn_sub_mul_card_eq_sum_inter_support T, abs_mul, Nat.abs_cast]
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
theorem sum_card_support_mul_abs_relativeDensity_coarsen_le [Fintype κ] [Fintype κ₂']
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

end TauCeti.Colored3Graph
