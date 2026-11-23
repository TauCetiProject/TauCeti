/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Hypergraph.Polyad.Coarsening
public import TauCeti.Combinatorics.Hypergraph.Polyad.Energy.Basic
public import TauCeti.Combinatorics.Hypergraph.Polyad.TopRegular
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Topology.UnitInterval

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

More generally, for any assignment `π : Polyad3 T → Polyad3 S` of coarse parents, triples in the
set `M = {x | Polyad3.ofTriple S x ≠ π (Polyad3.ofTriple T x)}` account for all discrepancies
between `P.support` and the fine supports `Q.support` with `π Q = P`, and the fine densities may be
compared against any reference target `a : κ → ℝ` (such as the coarse densities of another coloring
before recoloring) at the cost of doubling the fine-deviation and moved-triple terms.

When `T` refines `S`, the support-weighted deviations over all coarse polyads are controlled by the
polyad energy gap: if `H.polyadEnergy T - H.polyadEnergy S ≤ g`, each color has total deviation at
most `√g |V| (|V| - 1) (|V| - 2)`, and the sum over all colors in `κ` is at most
`√(|κ| g) |V| (|V| - 1) (|V| - 2)`. The slicing lemma
(`TauCeti.Colored3Graph.IsTopRegularOverPolyad.of_pairSupport_subset`) passes top regularity in
the other direction, from a coarse polyad to its large fine children.

## Main results

* `TauCeti.Colored3Graph.isTopRegularOverPolyad_of_sum_polyadMap_le` and
  `TauCeti.Colored3Graph.isTopRegularOverPolyad_of_sum_coarsen_le`: top regularity over a coarse
  polyad from top regularity over most of its fine children with nearly equal densities.
* `TauCeti.Colored3Graph.isTopRegularOverPolyad_of_sum_abs_relativeDensity_sub_le` and
  `TauCeti.Colored3Graph.isTopRegularOverPolyad_of_sum_coarsen_abs_relativeDensity_sub_le`:
  variants comparing fine densities against an arbitrary reference target `a : κ → ℝ`, with doubled
  deviation and moved-triple coefficients.
* `TauCeti.Colored3Graph.sum_card_support_mul_abs_relativeDensity_coarsen_le_of_color_eq` and
  `TauCeti.Colored3Graph.sum_card_support_mul_sum_abs_relativeDensity_coarsen_le_of_color_eq`:
  single-color and palette-summed support-weighted deviation bounds from the polyad energy gap
  under exact pair-color refinement.

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
/-- Bound the count-scaled deviation on `unionSupport U` against a reference constant `a ∈ [0, 1]`
across the fibers of `π`, when `0 ≤ η ≤ 1`. -/
private theorem abs_relDensityOn_unionSupport_sub_ref_mul_card_le [Fintype κ₂']
    (H : Colored3Graph κ V) (π : Polyad3 T → Polyad3 S) {P : Polyad3 S} (hη₀ : 0 ≤ η) (hη₁ : η ≤ 1)
    (U : Fin r → Subpolyad3 P) (c : κ) {a : ℝ} (ha₀ : 0 ≤ a) (ha₁ : a ≤ 1) :
    |((H.relDensityOn c (unionSupport U) : ℝ) - a) * #(unionSupport U)| ≤
      η * #P.support +
        ∑ Q : Polyad3 T with π Q = P ∧ ¬H.IsTopRegularOverPolyad Q η r, (#Q.support : ℝ) +
        ∑ Q : Polyad3 T with π Q = P, #Q.support * |(H.relativeDensity c Q : ℝ) - a| +
        ∑ Q : Polyad3 T with π Q = P,
          (#(({x | Polyad3.ofTriple S x ≠ π (Polyad3.ofTriple T x)} : Finset _) ∩ Q.support) : ℝ) +
        #(({x | Polyad3.ofTriple S x ≠ π (Polyad3.ofTriple T x)} : Finset _) ∩ P.support) := by
  set W := unionSupport U
  set M : Finset {x : Fin 3 → V // Function.Injective x} :=
    {x | Polyad3.ofTriple S x ≠ π (Polyad3.ofTriple T x)}
  have hfib : (∑ Q : Polyad3 T with π Q = P, (#Q.support : ℝ)) ≤
      #P.support + ∑ Q : Polyad3 T with π Q = P, (#(M ∩ Q.support) : ℝ) := by
    exact_mod_cast Polyad3.sum_card_support_polyadMap_le π P
  have hηfib : η * ∑ Q : Polyad3 T with π Q = P, (#Q.support : ℝ) ≤
      η * #P.support + ∑ Q : Polyad3 T with π Q = P, (#(M ∩ Q.support) : ℝ) := by
    have hM₀ : 0 ≤ ∑ Q : Polyad3 T with π Q = P, (#(M ∩ Q.support) : ℝ) :=
      sum_nonneg fun _ _ ↦ Nat.cast_nonneg _
    nlinarith [mul_le_mul_of_nonneg_left hfib hη₀]
  have heq : ∑ Q : Polyad3 T with π Q = P,
        |((H.relDensityOn c (W ∩ Q.support) : ℝ) - a) * #(W ∩ Q.support)| ≤
      η * ∑ Q : Polyad3 T with π Q = P, (#Q.support : ℝ) +
        ∑ Q : Polyad3 T with π Q = P ∧ ¬H.IsTopRegularOverPolyad Q η r, (#Q.support : ℝ) +
        ∑ Q : Polyad3 T with π Q = P, #Q.support * |(H.relativeDensity c Q : ℝ) - a| := by
    refine (sum_le_sum fun Q _ ↦ abs_relDensityOn_inter_sub_mul_card_le hη₀ U Q c a).trans_eq ?_
    rw [sum_add_distrib, sum_add_distrib, ← mul_sum, ← sum_filter, filter_filter]
  have hsplit := H.abs_relDensityOn_sub_mul_card_le_sum_polyadMap π (unionSupport_subset U) c ha₀
    ha₁
  linarith

/-- Common count-to-density reduction for `(δ, r)`-top regularity over `P`. -/
private theorem isTopRegularOverPolyad_of_count_le (H : Colored3Graph κ V) {P : Polyad3 S}
    (hδ : 0 < δ) (hηθ : η + θ ≤ δ ^ 2) (hθ : ∀ _ : κ, 0 ≤ θ * (#P.support : ℝ))
    (hcount : ∀ c (U : Fin r → Subpolyad3 P), η ≤ 1 →
      |(H.relDensityOn c (unionSupport U) : ℝ) - H.relativeDensity c P| * #(unionSupport U) ≤
        (η + θ) * #P.support) :
    H.IsTopRegularOverPolyad P δ r := by
  obtain hδ₁ | hδ₁ := le_or_gt 1 δ
  · exact isTopRegularOverPolyad_of_one_le (H := H) (P := P) (r := r) hδ₁
  rw [isTopRegularOverPolyad_iff]
  intro c U hU
  set W := unionSupport U
  obtain hW | hW := (Nat.cast_nonneg (α := ℝ) #W).eq_or_lt
  · have hW' : W = ∅ := card_eq_zero.1 (by exact_mod_cast hW.symm)
    have hP' : P.support = ∅ := by
      have := nonpos_of_mul_nonpos_right (hU.trans hW.symm.le) hδ
      exact card_eq_zero.1 (by exact_mod_cast this.antisymm (Nat.cast_nonneg _))
    rw [hW', relDensityOn_empty, H.relativeDensity_of_support_eq_empty c hP']
    simpa using hδ.le
  have hPpos : (0 : ℝ) < #P.support :=
    hW.trans_le (Nat.cast_le.2 (card_le_card (unionSupport_subset U)))
  have hθ₀ : 0 ≤ θ := nonneg_of_mul_nonneg_left (hθ c) hPpos
  have hη₁ : η ≤ 1 := by nlinarith [pow_pos hδ 2]
  refine le_of_mul_le_mul_right ?_ hW
  calc |(H.relDensityOn c W : ℝ) - H.relativeDensity c P| * #W
      ≤ (η + θ) * #P.support := hcount c U hη₁
    _ ≤ δ * (δ * #P.support) := by nlinarith [hPpos.le]
    _ ≤ δ * #W := mul_le_mul_of_nonneg_left hU hδ.le

open Classical in
/-- **Top regularity over a coarse polyad along a polyad map.** Let `π : Polyad3 T → Polyad3 S`
assign coarse parents, and let `M = {x | Polyad3.ofTriple S x ≠ π (Polyad3.ofTriple T x)}`. Suppose
that for every top color `c`, the irregular fine children `π Q = P`, the support-weighted density
deviations from `H.relativeDensity c P`, and the moved triples in those children and in `P.support`
together cost at most `θ |P|`. If `0 ≤ η`, `0 < δ`, and `η + θ ≤ δ²`, then `H` is
`(δ, r)`-top-regular over `P`. -/
theorem isTopRegularOverPolyad_of_sum_polyadMap_le [Fintype κ₂']
    (π : Polyad3 T → Polyad3 S) {P : Polyad3 S}
    (hη : 0 ≤ η) (hδ : 0 < δ) (hηθ : η + θ ≤ δ ^ 2)
    (hP : ∀ c,
      ∑ Q : Polyad3 T with π Q = P ∧ ¬H.IsTopRegularOverPolyad Q η r, (#Q.support : ℝ) +
        ∑ Q : Polyad3 T with π Q = P,
          #Q.support * |(H.relativeDensity c Q : ℝ) - H.relativeDensity c P| +
        ∑ Q : Polyad3 T with π Q = P,
          (#(({x | Polyad3.ofTriple S x ≠ π (Polyad3.ofTriple T x)} : Finset _) ∩ Q.support) : ℝ) +
        #(({x | Polyad3.ofTriple S x ≠ π (Polyad3.ofTriple T x)} : Finset _) ∩ P.support) ≤
      θ * #P.support) :
    H.IsTopRegularOverPolyad P δ r := by
  refine isTopRegularOverPolyad_of_count_le H hδ hηθ
    (fun c ↦ (add_nonneg (add_nonneg (add_nonneg (sum_nonneg fun _ _ ↦ Nat.cast_nonneg _)
      (sum_nonneg fun _ _ ↦ mul_nonneg (Nat.cast_nonneg _) (abs_nonneg _)))
      (sum_nonneg fun _ _ ↦ Nat.cast_nonneg _)) (Nat.cast_nonneg _)).trans (hP c))
    fun c U hη₁ ↦ ?_
  have h₁ := abs_relDensityOn_unionSupport_sub_ref_mul_card_le H π hη hη₁ U c
    (a := (H.relativeDensity c P : ℝ))
    (mod_cast H.relativeDensity_nonneg c P) (mod_cast H.relativeDensity_le_one c P)
  rw [abs_mul, Nat.abs_cast] at h₁
  linarith [hP c]

open Classical in
/-- **Top regularity over a coarse polyad from a reference target.** Variant of
`Colored3Graph.isTopRegularOverPolyad_of_sum_polyadMap_le` in which the fine densities over
`π Q = P` are compared against an arbitrary target `a : κ → ℝ` rather than `H.relativeDensity · P`:
comparing both `unionSupport U` and `H.relativeDensity c P` to `a c` doubles (`2 *`) the
coefficients on the fine-density deviation and moved-triple terms. -/
theorem isTopRegularOverPolyad_of_sum_abs_relativeDensity_sub_le [Fintype κ₂']
    (π : Polyad3 T → Polyad3 S) {P : Polyad3 S} {a : κ → ℝ}
    (hη : 0 ≤ η) (hδ : 0 < δ) (hηθ : η + θ ≤ δ ^ 2)
    (hP : ∀ c,
      ∑ Q : Polyad3 T with π Q = P ∧ ¬H.IsTopRegularOverPolyad Q η r, (#Q.support : ℝ) +
        2 * ∑ Q : Polyad3 T with π Q = P, #Q.support * |(H.relativeDensity c Q : ℝ) - a c| +
        2 * ∑ Q : Polyad3 T with π Q = P,
          (#(({x | Polyad3.ofTriple S x ≠ π (Polyad3.ofTriple T x)} : Finset _) ∩ Q.support) : ℝ) +
        2 * #(({x | Polyad3.ofTriple S x ≠ π (Polyad3.ofTriple T x)} : Finset _) ∩ P.support) ≤
      θ * #P.support) :
    H.IsTopRegularOverPolyad P δ r := by
  refine isTopRegularOverPolyad_of_count_le H hδ hηθ
    (fun c ↦ (add_nonneg (add_nonneg (add_nonneg (sum_nonneg fun _ _ ↦ Nat.cast_nonneg _)
      (mul_nonneg zero_le_two (sum_nonneg fun _ _ ↦ mul_nonneg (Nat.cast_nonneg _) (abs_nonneg _))))
      (mul_nonneg zero_le_two (sum_nonneg fun _ _ ↦ Nat.cast_nonneg _)))
      (mul_nonneg zero_le_two (Nat.cast_nonneg _))).trans (hP c))
    fun c U hη₁ ↦ ?_
  set W := unionSupport U
  set a' := Set.projIcc 0 1 zero_le_one (a c)
  have hclamp : ∑ Q : Polyad3 T with π Q = P, #Q.support * |(H.relativeDensity c Q : ℝ) - a'| ≤
      ∑ Q : Polyad3 T with π Q = P, #Q.support * |(H.relativeDensity c Q : ℝ) - a c| := by
    refine sum_le_sum fun Q _ ↦ mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
    have hmem : (H.relativeDensity c Q : ℝ) ∈ Set.Icc (0 : ℝ) 1 :=
      ⟨mod_cast H.relativeDensity_nonneg c Q, mod_cast H.relativeDensity_le_one c Q⟩
    simpa only [Set.projIcc_of_mem zero_le_one hmem] using
      Set.abs_projIcc_sub_projIcc zero_le_one (c := (H.relativeDensity c Q : ℝ)) (d := a c)
  have hWP : (#W : ℝ) ≤ #P.support := Nat.cast_le.2 (card_le_card (unionSupport_subset U))
  have h₁ := abs_relDensityOn_unionSupport_sub_ref_mul_card_le H π hη hη₁ U c
    a'.property.1 a'.property.2
  have h₂ := mul_le_mul_of_nonneg_left hWP (abs_nonneg ((H.relativeDensity c P : ℝ) - a'))
  have h₃ := H.abs_relativeDensity_sub_mul_card_support_le_of_polyadMap π P c
    a'.property.1 a'.property.2
  have habs := abs_sub_le (H.relDensityOn c W : ℝ) (a' : ℝ) (H.relativeDensity c P)
  rw [abs_sub_comm (a' : ℝ)] at habs
  have htri : |(H.relDensityOn c W : ℝ) - H.relativeDensity c P| * #W ≤
      |((H.relDensityOn c W : ℝ) - a') * #W| + |(H.relativeDensity c P : ℝ) - a'| * #W := by
    rw [abs_mul, Nat.abs_cast]
    exact (mul_le_mul_of_nonneg_right habs (Nat.cast_nonneg _)).trans_eq (add_mul _ _ _)
  linarith [hP c]

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
  refine isTopRegularOverPolyad_of_sum_polyadMap_le (fun Q : Polyad3 T ↦ Q.coarsen hV f) hη hδ hηθ
    fun c ↦ ?_
  have hM : ({x | Polyad3.ofTriple S x ≠ (Polyad3.ofTriple T x).coarsen hV f} : Finset _) = ∅ := by
    ext x
    simp [Polyad3.coarsen_ofTriple hV f hf]
  simp only [hM, empty_inter, card_empty, Nat.cast_zero, sum_const_zero, add_zero]
  convert hP c

open Classical in
/-- **Top regularity over a coarse polyad from a reference target under exact refinement.** Let `T`
refine `S` along `f`, and let `a : κ → ℝ` be a reference target. If for every color `c` the
irregular fine children of `P` plus twice the support-weighted deviation of the fine densities of
`c` from `a c` cost at most `θ |P|`, and `η + θ ≤ δ²`, then `H` is `(δ, r)`-top-regular over `P`. -/
theorem isTopRegularOverPolyad_of_sum_coarsen_abs_relativeDensity_sub_le [Fintype κ₂']
    (hV : T.vertexPart ≤ S.vertexPart) (f : κ₂' → κ₂)
    (hf : ∀ p, S.pairColors.color p = f (T.pairColors.color p)) {P : Polyad3 S} {a : κ → ℝ}
    (hη : 0 ≤ η) (hδ : 0 < δ) (hηθ : η + θ ≤ δ ^ 2)
    (hP : ∀ c, ∑ Q : Polyad3 T with Q.coarsen hV f = P ∧ ¬H.IsTopRegularOverPolyad Q η r,
        (#Q.support : ℝ) +
      2 * ∑ Q : Polyad3 T with Q.coarsen hV f = P,
        #Q.support * |(H.relativeDensity c Q : ℝ) - a c| ≤ θ * #P.support) :
    H.IsTopRegularOverPolyad P δ r := by
  refine isTopRegularOverPolyad_of_sum_abs_relativeDensity_sub_le (a := a)
    (fun Q : Polyad3 T ↦ Q.coarsen hV f) hη hδ hηθ fun c ↦ ?_
  have hM : ({x | Polyad3.ofTriple S x ≠ (Polyad3.ofTriple T x).coarsen hV f} : Finset _) = ∅ := by
    ext x
    simp [Polyad3.coarsen_ofTriple hV f hf]
  simp only [hM, empty_inter, card_empty, Nat.cast_zero, sum_const_zero, mul_zero, add_zero]
  convert hP c

open Classical in
/-- The support-weighted deviation of the fine densities of a color from the coarse ones is at
most `√g` times the number of injective triples when `T` refines `S` with exact pair-color
agreement along `f` and the polyad energy gap is at most `g`. -/
theorem sum_card_support_mul_abs_relativeDensity_coarsen_le_of_color_eq [Fintype κ] [Fintype κ₂']
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

open Classical in
/-- The support-weighted total-variation deviation of the fine color densities from the coarse ones,
summed over all colors in `κ`, is at most `√(|κ| g)` times the number of injective triples when `T`
refines `S` with exact pair-color agreement along `f` and the polyad energy gap is at most `g`. -/
theorem sum_card_support_mul_sum_abs_relativeDensity_coarsen_le_of_color_eq [Fintype κ]
    [Fintype κ₂'] (hV : T.vertexPart ≤ S.vertexPart) (f : κ₂' → κ₂)
    (hf : ∀ p, S.pairColors.color p = f (T.pairColors.color p)) {g : ℝ}
    (hgap : H.polyadEnergy T - H.polyadEnergy S ≤ g) :
    ∑ Q : Polyad3 T, #Q.support * ∑ c,
        |(H.relativeDensity c Q : ℝ) - H.relativeDensity c (Q.coarsen hV f)| ≤
      √(Fintype.card κ * g) * (Fintype.card V).descFactorial 3 := by
  have h := H.polyadDensityDeviation_sum_abs_le (S := S) (T := T)
    (fun x y hxy ↦ by rw [← Polyad3.coarsen_ofTriple hV f hf x, hxy,
      Polyad3.coarsen_ofTriple hV f hf y]) hgap
  simp_rw [← Polyad3.coarsen_ofTriple hV f hf] at h
  rw [Polyad3.sum_comp_ofTriple
    (fun Q ↦ ∑ c, |(H.relativeDensity c Q : ℝ) - H.relativeDensity c (Q.coarsen hV f)|)] at h
  simpa only [nsmul_eq_mul] using h

end TauCeti.Colored3Graph
