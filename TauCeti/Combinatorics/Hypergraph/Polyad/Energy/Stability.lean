/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Hypergraph.Polyad.Coarsening
public import TauCeti.Combinatorics.Hypergraph.Polyad.Energy.Basic
public import TauCeti.Combinatorics.Hypergraph.Polyad.Repartition
import TauCeti.Algebra.BigOperators.Finset.Fiber
import TauCeti.Data.Fintype.Card.Embedding
import Mathlib.Data.Rat.BigOperators
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Stability and almost-monotonicity of polyad energy

Regularizing or rebalancing the lower skeleton of a 3-uniform hypergraph edits a small set of pairs
or vertices rather than refining the skeleton strictly: intra-cell pairs receive a fresh color,
irregular cell pairs are merged into a junk color, or padded vertices move between cells. Under
such edits, polyad supports do not nest cleanly, so exact refinement monotonicity
(`Colored3Graph.polyadEnergy_mono_of_refines`) and the exact refinement defect identity
(`Colored3Graph.polyadDensityDeviation_sq`) do not apply directly.

This file controls the polyad energy and the coarse-to-fine density deviations across arbitrary
lower-skeleton edits, with constants independent of the size of the top palette `κ` and without
finiteness assumptions on the coarse pair-color type:

1. **Almost-monotonicity and approximate energy-gap deviation bounds.** For any parent assignment
   `π : Polyad3 T → Polyad3 S` with moved-triple set
   `M = {x | Polyad3.ofTriple S x ≠ π (Polyad3.ofTriple T x)}` and
   `N = |V|.descFactorial 3`:
   * `H.polyadEnergy S - 3 #M / N ≤ H.polyadEnergy T`
     (`Colored3Graph.polyadEnergy_sub_le_polyadEnergy_of_polyadMap`), with specializations to
     approximate pair-color coarsenings
     (`Colored3Graph.polyadEnergy_sub_le_polyadEnergy_of_vertexPart_le`) and to vertex refinement
     combined with injective pair recoloring
     (`Colored3Graph.polyadEnergy_sub_le_polyadEnergy_of_vertexPart_le_of_injective`);
   * when `H.polyadEnergy T - H.polyadEnergy S ≤ g` and `κ₂'` is finite, the support-weighted `L¹`
     density deviations between each fine polyad `Q` and `π Q` are at most
     `√(g + 3 #M / N) N + 2 #M` for a single color
     (`Colored3Graph.sum_card_support_mul_abs_relativeDensity_polyadMap_le`) and at most
     `√(|κ| (g + 3 #M / N)) N + 4 #M` summed over all colors in `κ`
     (`Colored3Graph.sum_card_support_mul_sum_abs_relativeDensity_polyadMap_le`), specializing
     without loss to the exact refinement bounds when `M = ∅`.

2. **Two-sided Lipschitz stability under an injective polyad map.** For an injective map
   `f : Polyad3 S → Polyad3 T` with moved-triple set
   `M = {x | Polyad3.ofTriple T x ≠ f (Polyad3.ofTriple S x)}`,
   `|H.polyadEnergy T - H.polyadEnergy S| ≤ 3 #M / N`
   (`Colored3Graph.abs_polyadEnergy_sub_le_of_injective`), yielding explicit stability bounds under
   pair recolorings (`Colored3Graph.abs_polyadEnergy_sub_le_of_pairRecoloring`) and vertex-cell
   repartitions (`Colored3Graph.abs_polyadEnergy_sub_le_of_repartition`).

## Main results

* `TauCeti.Colored3Graph.polyadEnergy_sub_le_polyadEnergy_of_polyadMap`,
  `TauCeti.Colored3Graph.polyadEnergy_sub_le_polyadEnergy_of_vertexPart_le`, and
  `TauCeti.Colored3Graph.polyadEnergy_sub_le_polyadEnergy_of_vertexPart_le_of_injective`:
  almost-monotonicity of polyad energy under approximate coarsenings and refining pair recolorings.
* `TauCeti.Colored3Graph.abs_polyadEnergy_sub_le_of_injective`,
  `TauCeti.Colored3Graph.abs_polyadEnergy_sub_le_of_pairRecoloring`, and
  `TauCeti.Colored3Graph.abs_polyadEnergy_sub_le_of_repartition`: two-sided energy stability under
  injective polyad maps, pair recolorings, and vertex-cell repartitions.
* `TauCeti.Colored3Graph.sum_card_support_mul_abs_relativeDensity_polyadMap_le`,
  `TauCeti.Colored3Graph.sum_card_support_mul_sum_abs_relativeDensity_polyadMap_le`,
  `TauCeti.Colored3Graph.sum_card_support_mul_abs_relativeDensity_coarsen_le`, and
  `TauCeti.Colored3Graph.sum_card_support_mul_sum_abs_relativeDensity_coarsen_le`: single-color and
  palette-summed coarse-to-fine density-deviation bounds from an approximate energy gap.

## References

* V. Rödl and M. Schacht, *Regular partitions of hypergraphs: regularity lemmas*,
  Combin. Probab. Comput. 16 (2007).
* T. Tao, *Szemerédi's regularity lemma revisited*, Contrib. Discrete Math. 1 (2006).
-/

public section

open Finset

namespace TauCeti.Colored3Graph

variable {κ κ₂ κ₂' V : Type*} [Fintype V] [DecidableEq V] [DecidableEq κ] [Fintype κ]

/-! ### Almost-monotonicity along a polyad map -/

section PolyadMap

variable {S : PairSkeleton3 κ₂ V} {T : PairSkeleton3 κ₂' V}

open Classical in
/-- The fiber of injective triples assigned to a coarse polyad `P` through `π` and
`Polyad3.ofTriple T`. -/
private noncomputable def fiberSupport (π : Polyad3 T → Polyad3 S) (P : Polyad3 S) :
    Finset {x : Fin 3 → V // Function.Injective x} :=
  {x | π (Polyad3.ofTriple T x) = P}

open Classical in
@[simp]
private theorem mem_fiberSupport {π : Polyad3 T → Polyad3 S} {P : Polyad3 S}
    {x : {x : Fin 3 → V // Function.Injective x}} :
    x ∈ fiberSupport π P ↔ π (Polyad3.ofTriple T x) = P := by
  simp [fiberSupport]

open Classical in
/-- The finite set of coarse polyads over `S` realized either directly as `Polyad3.ofTriple S x`
or as `π (Polyad3.ofTriple T x)` for some injective triple `x`. Indexing coarse sums over this
finite set avoids any finiteness assumption on `κ₂`. -/
private noncomputable def activePolyads (π : Polyad3 T → Polyad3 S) : Finset (Polyad3 S) :=
  univ.image (Polyad3.ofTriple S) ∪ univ.image (fun x ↦ π (Polyad3.ofTriple T x))

private theorem ofTriple_mem_activePolyads (π : Polyad3 T → Polyad3 S)
    (x : {x : Fin 3 → V // Function.Injective x}) :
    Polyad3.ofTriple S x ∈ activePolyads π := by
  classical
  exact mem_union_left _ (mem_image_of_mem _ (mem_univ x))

private theorem apply_ofTriple_mem_activePolyads (π : Polyad3 T → Polyad3 S)
    (x : {x : Fin 3 → V // Function.Injective x}) :
    π (Polyad3.ofTriple T x) ∈ activePolyads π := by
  classical
  exact mem_union_right _ (mem_image_of_mem _ (mem_univ x))

open Classical in
private theorem filter_univ_ofTriple_eq (P : Polyad3 S) :
    {x ∈ (univ : Finset {x : Fin 3 → V // Function.Injective x}) | Polyad3.ofTriple S x = P} =
      P.support := by
  ext x
  simp only [mem_filter, mem_univ, true_and, Polyad3.mem_support_iff_eq_ofTriple, eq_comm]

open Classical in
private theorem filter_univ_fiberSupport_eq (π : Polyad3 T → Polyad3 S) (P : Polyad3 S) :
    {x ∈ (univ : Finset {x : Fin 3 → V // Function.Injective x}) |
        π (Polyad3.ofTriple T x) = P} =
      fiberSupport π P := by
  ext x
  simp

/-- Summing a function of `π (Polyad3.ofTriple T x)` over all injective triples gives the
`fiberSupport`-weighted sum over `activePolyads π`. -/
private theorem sum_comp_fiberSupport {M : Type*} [AddCommMonoid M]
    (π : Polyad3 T → Polyad3 S) (φ : Polyad3 S → M) :
    ∑ x : {x : Fin 3 → V // Function.Injective x}, φ (π (Polyad3.ofTriple T x)) =
      ∑ P ∈ activePolyads π, #(fiberSupport π P) • φ P := by
  classical
  rw [← TauCeti.sum_card_filter_nsmul_eq_sum_comp
    (fun x _ ↦ apply_ofTriple_mem_activePolyads π x) φ]
  refine sum_congr rfl fun P _ ↦ ?_
  rw [filter_univ_fiberSupport_eq]

/-- Express `H.polyadEnergy S` over the finite set `activePolyads π`, without `[Fintype κ₂]`. -/
private theorem polyadEnergy_eq_sum_activePolyads (H : Colored3Graph κ V)
    (π : Polyad3 T → Polyad3 S) :
    H.polyadEnergy S =
      (∑ P ∈ activePolyads π, ∑ c, (#P.support : ℝ) * (H.relDensityOn c P.support : ℝ) ^ 2) /
        (Fintype.card V).descFactorial 3 := by
  classical
  rw [polyadEnergy_def]
  congr 1
  have h := (TauCeti.sum_card_filter_nsmul_eq_sum_comp
    (s := (univ : Finset {x : Fin 3 → V // Function.Injective x})) (t := activePolyads π)
    (fun x _ ↦ ofTriple_mem_activePolyads π x)
    (fun P ↦ ∑ c, (H.relDensityOn c P.support : ℝ) ^ 2)).symm
  simp_rw [relativeDensity_def]
  rw [h]
  refine sum_congr rfl fun P _ ↦ ?_
  rw [filter_univ_ofTriple_eq, nsmul_eq_mul, mul_sum]

/-- Exact conditional-expectation defect identity between the fine polyads over `T` and the fibers
of `π : Polyad3 T → Polyad3 S`. -/
private theorem fiberDensityDeviation_sq (H : Colored3Graph κ V) (π : Polyad3 T → Polyad3 S) :
    (∑ x : {x : Fin 3 → V // Function.Injective x}, ∑ c,
        ((H.relativeDensity c (Polyad3.ofTriple T x) : ℝ) -
          H.relDensityOn c (fiberSupport π (π (Polyad3.ofTriple T x)))) ^ 2) /
        (Fintype.card V).descFactorial 3 =
      H.polyadEnergy T -
        (∑ P ∈ activePolyads π, ∑ c, (#(fiberSupport π P) : ℝ) *
          (H.relDensityOn c (fiberSupport π P) : ℝ) ^ 2) /
          (Fintype.card V).descFactorial 3 := by
  classical
  have hsq (c : κ) :
      ∑ x : {x : Fin 3 → V // Function.Injective x},
          (H.relDensityOn c (fiberSupport π (π (Polyad3.ofTriple T x))) : ℝ) ^ 2 =
        ∑ P ∈ activePolyads π, (#(fiberSupport π P) : ℝ) *
          (H.relDensityOn c (fiberSupport π P) : ℝ) ^ 2 := by
    simpa only [nsmul_eq_mul] using
      sum_comp_fiberSupport π fun P ↦ (H.relDensityOn c (fiberSupport π P) : ℝ) ^ 2
  have hcorr (c : κ) :
      ∑ x : {x : Fin 3 → V // Function.Injective x},
          (H.relativeDensity c (Polyad3.ofTriple T x) : ℝ) *
            H.relDensityOn c (fiberSupport π (π (Polyad3.ofTriple T x))) =
        ∑ P ∈ activePolyads π, (#(fiberSupport π P) : ℝ) *
          (H.relDensityOn c (fiberSupport π P) : ℝ) ^ 2 := by
    rw [H.sum_relativeDensity_ofTriple_mul (S := T) c _ fun x y hxy ↦ by rw [hxy],
      ← TauCeti.sum_card_filter_nsmul_eq_sum_comp (t := activePolyads π)
        (fun x _ ↦ apply_ofTriple_mem_activePolyads π x)
        (fun P ↦ (H.relDensityOn c (fiberSupport π P) : ℝ))]
    refine sum_congr rfl fun P _ ↦ ?_
    have hf : {x ∈ univ.filter
        (fun x : {x : Fin 3 → V // Function.Injective x} ↦
          H.color (Set.powersetCard.ofFinEmb 3 V ⟨x.1, x.2⟩) = c) |
        π (Polyad3.ofTriple T x) = P} =
        {x ∈ fiberSupport π P | H.color (Set.powersetCard.ofFinEmb 3 V ⟨x.1, x.2⟩) = c} := by
      ext x
      simp [and_comm]
    have hmul : (#{x ∈ fiberSupport π P |
        H.color (Set.powersetCard.ofFinEmb 3 V ⟨x.1, x.2⟩) = c} : ℝ) =
        (H.relDensityOn c (fiberSupport π P) : ℝ) * #(fiberSupport π P) := by
      exact_mod_cast (H.relDensityOn_mul_card c (fiberSupport π P)).symm
    rw [hf, nsmul_eq_mul, hmul]
    ring
  rw [polyadEnergy_def, ← sub_div, sum_comm,
    sum_comm (s := univ) (t := univ)
      (f := fun x c ↦ (H.relativeDensity c (Polyad3.ofTriple T x) : ℝ) ^ 2),
    sum_comm (s := activePolyads π) (t := univ)
      (f := fun P c ↦ (#(fiberSupport π P) : ℝ) * (H.relDensityOn c (fiberSupport π P) : ℝ) ^ 2),
    ← sum_sub_distrib]
  congr 1
  refine sum_congr rfl fun c _ ↦ ?_
  simp only [sub_sq, sum_add_distrib, sum_sub_distrib, mul_assoc, ← mul_sum]
  rw [hcorr c, hsq c]
  ring

open Classical in
/-- Triples in `P.support \ fiberSupport π P` satisfy
`Polyad3.ofTriple S x ≠ π (Polyad3.ofTriple T x)`. -/
private theorem card_sdiff_fiberSupport_le (π : Polyad3 T → Polyad3 S) (P : Polyad3 S) :
    #(P.support \ fiberSupport π P) ≤
      #(({x | Polyad3.ofTriple S x ≠ π (Polyad3.ofTriple T x)} : Finset _) ∩ P.support) := by
  refine card_le_card fun x hx ↦ ?_
  obtain ⟨hxP, hxF⟩ := mem_sdiff.1 hx
  rw [mem_fiberSupport] at hxF
  exact mem_inter.2 ⟨mem_filter.2 ⟨mem_univ _,
    fun h ↦ hxF ((Polyad3.mem_support_iff_eq_ofTriple.1 hxP).trans h).symm⟩, hxP⟩

open Classical in
/-- Triples in `fiberSupport π P \ P.support` satisfy
`Polyad3.ofTriple S x ≠ π (Polyad3.ofTriple T x)`. -/
private theorem card_fiberSupport_sdiff_le (π : Polyad3 T → Polyad3 S) (P : Polyad3 S) :
    #(fiberSupport π P \ P.support) ≤
      #(({x | Polyad3.ofTriple S x ≠ π (Polyad3.ofTriple T x)} : Finset _) ∩
        fiberSupport π P) := by
  refine card_le_card fun x hx ↦ ?_
  obtain ⟨hxF, hxP⟩ := mem_sdiff.1 hx
  exact mem_inter.2 ⟨mem_filter.2 ⟨mem_univ _, fun h ↦ hxP
    (Polyad3.mem_support_iff_eq_ofTriple.2 ((mem_fiberSupport.1 hxF).symm.trans h.symm))⟩, hxF⟩

open Classical in
/-- Across `activePolyads π`, the differences `P.support \ fiberSupport π P` contain at most the
moved triples. -/
private theorem sum_card_sdiff_fiberSupport_le (π : Polyad3 T → Polyad3 S) :
    ∑ P ∈ activePolyads π, #(P.support \ fiberSupport π P) ≤
      #{x | Polyad3.ofTriple S x ≠ π (Polyad3.ofTriple T x)} := by
  set M : Finset {x : Fin 3 → V // Function.Injective x} :=
    {x | Polyad3.ofTriple S x ≠ π (Polyad3.ofTriple T x)}
  calc ∑ P ∈ activePolyads π, #(P.support \ fiberSupport π P)
      ≤ ∑ P ∈ activePolyads π, #(M ∩ P.support) :=
        sum_le_sum fun P _ ↦ card_sdiff_fiberSupport_le π P
    _ = ∑ P ∈ activePolyads π, #{x ∈ M | Polyad3.ofTriple S x = P} := by
        refine sum_congr rfl fun P _ ↦ congrArg card ?_
        ext x
        simp only [mem_inter, mem_filter, Polyad3.mem_support_iff_eq_ofTriple, eq_comm]
    _ = #M := (card_eq_sum_card_fiberwise fun x _ ↦ ofTriple_mem_activePolyads π x).symm

open Classical in
/-- Across `activePolyads π`, the differences `fiberSupport π P \ P.support` contain at most the
moved triples. -/
private theorem sum_card_fiberSupport_sdiff_le (π : Polyad3 T → Polyad3 S) :
    ∑ P ∈ activePolyads π, #(fiberSupport π P \ P.support) ≤
      #{x | Polyad3.ofTriple S x ≠ π (Polyad3.ofTriple T x)} := by
  set M : Finset {x : Fin 3 → V // Function.Injective x} :=
    {x | Polyad3.ofTriple S x ≠ π (Polyad3.ofTriple T x)}
  calc ∑ P ∈ activePolyads π, #(fiberSupport π P \ P.support)
      ≤ ∑ P ∈ activePolyads π, #(M ∩ fiberSupport π P) :=
        sum_le_sum fun P _ ↦ card_fiberSupport_sdiff_le π P
    _ = ∑ P ∈ activePolyads π, #{x ∈ M | π (Polyad3.ofTriple T x) = P} := by
        refine sum_congr rfl fun P _ ↦ congrArg card ?_
        ext x
        simp
    _ = #M := (card_eq_sum_card_fiberwise fun x _ ↦ apply_ofTriple_mem_activePolyads π x).symm

open Classical in
/-- Comparing the polyad energy over `S` with the squared-density sum over the fibers of `π` costs
at most `3 #M / |V|.descFactorial 3`, where `M` is the set of triples with
`Polyad3.ofTriple S x ≠ π (Polyad3.ofTriple T x)`. -/
private theorem polyadEnergy_sub_fiberEnergy_le (H : Colored3Graph κ V)
    (π : Polyad3 T → Polyad3 S) :
    H.polyadEnergy S -
        (∑ P ∈ activePolyads π, ∑ c, (#(fiberSupport π P) : ℝ) *
          (H.relDensityOn c (fiberSupport π P) : ℝ) ^ 2) /
          (Fintype.card V).descFactorial 3 ≤
      3 * #{x | Polyad3.ofTriple S x ≠ π (Polyad3.ofTriple T x)} /
        (Fintype.card V).descFactorial 3 := by
  have hloc (P : Polyad3 S) :
      ∑ c, (#P.support : ℝ) * (H.relDensityOn c P.support : ℝ) ^ 2 -
        ∑ c, (#(fiberSupport π P) : ℝ) * (H.relDensityOn c (fiberSupport π P) : ℝ) ^ 2 ≤
      2 * (#(P.support \ fiberSupport π P) : ℝ) + #(fiberSupport π P \ P.support) := by
    exact_mod_cast H.sum_card_mul_sq_relDensityOn_sub_le P.support (fiberSupport π P)
  have hs₁ : ∑ P ∈ activePolyads π, (#(P.support \ fiberSupport π P) : ℝ) ≤
      #{x | Polyad3.ofTriple S x ≠ π (Polyad3.ofTriple T x)} := by
    exact_mod_cast sum_card_sdiff_fiberSupport_le π
  have hs₂ : ∑ P ∈ activePolyads π, (#(fiberSupport π P \ P.support) : ℝ) ≤
      #{x | Polyad3.ofTriple S x ≠ π (Polyad3.ofTriple T x)} := by
    exact_mod_cast sum_card_fiberSupport_sdiff_le π
  rw [H.polyadEnergy_eq_sum_activePolyads π, ← sub_div, ← sum_sub_distrib]
  refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)
  have hsum := sum_le_sum fun P (_ : P ∈ activePolyads π) ↦ hloc P
  rw [sum_add_distrib, ← mul_sum] at hsum
  linarith

open Classical in
/-- **Almost-monotonicity of polyad energy along a polyad map.** For any map
`π : Polyad3 T → Polyad3 S`, the polyad energy over `T` is at least the polyad energy over `S`
minus `3` times the proportion of injective triples with
`Polyad3.ofTriple S x ≠ π (Polyad3.ofTriple T x)`. -/
theorem polyadEnergy_sub_le_polyadEnergy_of_polyadMap (H : Colored3Graph κ V)
    (π : Polyad3 T → Polyad3 S) :
    H.polyadEnergy S -
        3 * #{x | Polyad3.ofTriple S x ≠ π (Polyad3.ofTriple T x)} /
          (Fintype.card V).descFactorial 3 ≤
      H.polyadEnergy T := by
  have hnonneg : 0 ≤ H.polyadEnergy T -
      (∑ P ∈ activePolyads π, ∑ c, (#(fiberSupport π P) : ℝ) *
        (H.relDensityOn c (fiberSupport π P) : ℝ) ^ 2) /
        (Fintype.card V).descFactorial 3 := by
    rw [← H.fiberDensityDeviation_sq π]
    exact div_nonneg (sum_nonneg fun _ _ ↦ sum_nonneg fun _ _ ↦ sq_nonneg _) (Nat.cast_nonneg _)
  linarith [H.polyadEnergy_sub_fiberEnergy_le π]

open Classical in
/-- **Almost-monotonicity under an approximate coarsening.** If `T.vertexPart ≤ S.vertexPart` and
the pair colors of `S` agree with `f ∘ T.pairColors.color` outside a set `E` of ordered pairs, then
`H.polyadEnergy S - 9 #E |V| / |V|.descFactorial 3 ≤ H.polyadEnergy T`. -/
theorem polyadEnergy_sub_le_polyadEnergy_of_vertexPart_le (H : Colored3Graph κ V)
    (hV : T.vertexPart ≤ S.vertexPart) (f : κ₂' → κ₂) :
    H.polyadEnergy S -
        9 * #{p | S.pairColors.color p ≠ f (T.pairColors.color p)} * Fintype.card V /
          (Fintype.card V).descFactorial 3 ≤
      H.polyadEnergy T := by
  refine le_trans ?_
    (H.polyadEnergy_sub_le_polyadEnergy_of_polyadMap fun Q : Polyad3 T ↦ Q.coarsen hV f)
  have hm : (#{x | Polyad3.ofTriple S x ≠ (Polyad3.ofTriple T x).coarsen hV f} : ℝ) ≤
      3 * #{p | S.pairColors.color p ≠ f (T.pairColors.color p)} * Fintype.card V := by
    exact_mod_cast Polyad3.card_filter_ofTriple_ne_coarsen_ofTriple_le hV f
  have hdiv : 3 * (#{x | Polyad3.ofTriple S x ≠ (Polyad3.ofTriple T x).coarsen hV f} : ℝ) /
      (Fintype.card V).descFactorial 3 ≤
      9 * #{p | S.pairColors.color p ≠ f (T.pairColors.color p)} * Fintype.card V /
        (Fintype.card V).descFactorial 3 :=
    div_le_div_of_nonneg_right (by linarith) (Nat.cast_nonneg _)
  linarith

/-! ### Approximate energy-gap deviation bounds -/

open Classical in
omit [Fintype κ] in
/-- Single-color `L¹` discrepancy between the fiber densities of `π` and the coarse polyad
densities. -/
private theorem sum_abs_relDensityOn_fiberSupport_sub_le (H : Colored3Graph κ V)
    (π : Polyad3 T → Polyad3 S) (c : κ) :
    ∑ x : {x : Fin 3 → V // Function.Injective x},
        |(H.relDensityOn c (fiberSupport π (π (Polyad3.ofTriple T x))) : ℝ) -
          H.relativeDensity c (π (Polyad3.ofTriple T x))| ≤
      2 * #{x | Polyad3.ofTriple S x ≠ π (Polyad3.ofTriple T x)} := by
  rw [sum_comp_fiberSupport π
    (fun P ↦ |(H.relDensityOn c (fiberSupport π P) : ℝ) - H.relativeDensity c P|)]
  have hloc (P : Polyad3 S) :
      #(fiberSupport π P) • |(H.relDensityOn c (fiberSupport π P) : ℝ) - H.relativeDensity c P| ≤
        (#(fiberSupport π P \ P.support) : ℝ) + #(P.support \ fiberSupport π P) := by
    rw [nsmul_eq_mul, mul_comm, relativeDensity_def]
    exact_mod_cast H.abs_relDensityOn_sub_mul_card_le c (fiberSupport π P) P.support
  have hs₁ : ∑ P ∈ activePolyads π, (#(fiberSupport π P \ P.support) : ℝ) ≤
      #{x | Polyad3.ofTriple S x ≠ π (Polyad3.ofTriple T x)} := by
    exact_mod_cast sum_card_fiberSupport_sdiff_le π
  have hs₂ : ∑ P ∈ activePolyads π, (#(P.support \ fiberSupport π P) : ℝ) ≤
      #{x | Polyad3.ofTriple S x ≠ π (Polyad3.ofTriple T x)} := by
    exact_mod_cast sum_card_sdiff_fiberSupport_le π
  have hsum := (sum_le_sum fun P (_ : P ∈ activePolyads π) ↦ hloc P).trans_eq sum_add_distrib
  linarith

open Classical in
/-- Palette-summed `L¹` discrepancy between the fiber densities of `π` and the coarse polyad
densities. -/
private theorem sum_sum_abs_relDensityOn_fiberSupport_sub_le (H : Colored3Graph κ V)
    (π : Polyad3 T → Polyad3 S) :
    ∑ x : {x : Fin 3 → V // Function.Injective x}, ∑ c,
        |(H.relDensityOn c (fiberSupport π (π (Polyad3.ofTriple T x))) : ℝ) -
          H.relativeDensity c (π (Polyad3.ofTriple T x))| ≤
      4 * #{x | Polyad3.ofTriple S x ≠ π (Polyad3.ofTriple T x)} := by
  rw [sum_comp_fiberSupport π
    (fun P ↦ ∑ c, |(H.relDensityOn c (fiberSupport π P) : ℝ) - H.relativeDensity c P|)]
  have hloc (P : Polyad3 S) :
      #(fiberSupport π P) •
          ∑ c, |(H.relDensityOn c (fiberSupport π P) : ℝ) - H.relativeDensity c P| ≤
        2 * ((#(fiberSupport π P \ P.support) : ℝ) + #(P.support \ fiberSupport π P)) := by
    rw [nsmul_eq_mul, mul_comm]
    simp_rw [relativeDensity_def]
    exact_mod_cast H.sum_abs_relDensityOn_sub_mul_card_le (fiberSupport π P) P.support
  have hs₁ : ∑ P ∈ activePolyads π, (#(fiberSupport π P \ P.support) : ℝ) ≤
      #{x | Polyad3.ofTriple S x ≠ π (Polyad3.ofTriple T x)} := by
    exact_mod_cast sum_card_fiberSupport_sdiff_le π
  have hs₂ : ∑ P ∈ activePolyads π, (#(P.support \ fiberSupport π P) : ℝ) ≤
      #{x | Polyad3.ofTriple S x ≠ π (Polyad3.ofTriple T x)} := by
    exact_mod_cast sum_card_sdiff_fiberSupport_le π
  have hsum := sum_le_sum fun P (_ : P ∈ activePolyads π) ↦ hloc P
  rw [← mul_sum, sum_add_distrib] at hsum
  linarith

open Classical in
/-- **Single-color density-deviation bound along a polyad map.** Suppose
`H.polyadEnergy T - H.polyadEnergy S ≤ g`, and let `π : Polyad3 T → Polyad3 S` have moved-triple
set `M = {x | Polyad3.ofTriple S x ≠ π (Polyad3.ofTriple T x)}`. Then for each top color `c`, the
support-weighted `L¹` deviation between `H.relativeDensity c Q` and `H.relativeDensity c (π Q)` is
at most `√(g + 3 #M / N) N + 2 #M`, where `N = |V|.descFactorial 3`. -/
theorem sum_card_support_mul_abs_relativeDensity_polyadMap_le [Fintype κ₂']
    {H : Colored3Graph κ V} (π : Polyad3 T → Polyad3 S) {g : ℝ}
    (hgap : H.polyadEnergy T - H.polyadEnergy S ≤ g) (c : κ) :
    ∑ Q : Polyad3 T, #Q.support *
        |(H.relativeDensity c Q : ℝ) - H.relativeDensity c (π Q)| ≤
      √(g + 3 * #{x | Polyad3.ofTriple S x ≠ π (Polyad3.ofTriple T x)} /
          (Fintype.card V).descFactorial 3) * (Fintype.card V).descFactorial 3 +
        2 * #{x | Polyad3.ofTriple S x ≠ π (Polyad3.ofTriple T x)} := by
  have hcard : #(univ : Finset {x : Fin 3 → V // Function.Injective x}) =
      (Fintype.card V).descFactorial 3 := by
    rw [card_univ, Fintype.card_subtype_injective, Fintype.card_fin]
  -- Bound the fine-to-fiber deviation via Cauchy--Schwarz and the conditional-expectation defect.
  have hpart₁ :
      ∑ x : {x : Fin 3 → V // Function.Injective x},
          |(H.relativeDensity c (Polyad3.ofTriple T x) : ℝ) -
            H.relDensityOn c (fiberSupport π (π (Polyad3.ofTriple T x)))| ≤
        √(g + 3 * #{x | Polyad3.ofTriple S x ≠ π (Polyad3.ofTriple T x)} /
            (Fintype.card V).descFactorial 3) * (Fintype.card V).descFactorial 3 := by
    rw [← hcard]
    refine univ.sum_abs_le_sqrt _ ?_
    rw [hcard]
    refine (div_le_div_of_nonneg_right (sum_le_sum fun x _ ↦ single_le_sum
      (f := fun c' ↦ ((H.relativeDensity c' (Polyad3.ofTriple T x) : ℝ) -
        H.relDensityOn c' (fiberSupport π (π (Polyad3.ofTriple T x)))) ^ 2)
      (fun _ _ ↦ sq_nonneg _) (mem_univ c)) (Nat.cast_nonneg _)).trans ?_
    rw [H.fiberDensityDeviation_sq π]
    linarith [H.polyadEnergy_sub_fiberEnergy_le π]
  -- Combine with the fiber-to-coarse perturbation bound via the triangle inequality.
  have htri : ∑ x : {x : Fin 3 → V // Function.Injective x},
      |(H.relativeDensity c (Polyad3.ofTriple T x) : ℝ) -
        H.relativeDensity c (π (Polyad3.ofTriple T x))| ≤
      √(g + 3 * #{x | Polyad3.ofTriple S x ≠ π (Polyad3.ofTriple T x)} /
          (Fintype.card V).descFactorial 3) * (Fintype.card V).descFactorial 3 +
        2 * #{x | Polyad3.ofTriple S x ≠ π (Polyad3.ofTriple T x)} := by
    refine (sum_le_sum fun x _ ↦ abs_sub_le
      (H.relativeDensity c (Polyad3.ofTriple T x) : ℝ)
      (H.relDensityOn c (fiberSupport π (π (Polyad3.ofTriple T x))))
      (H.relativeDensity c (π (Polyad3.ofTriple T x)))).trans ?_
    rw [sum_add_distrib]
    exact add_le_add hpart₁ (H.sum_abs_relDensityOn_fiberSupport_sub_le π c)
  rw [Polyad3.sum_comp_ofTriple
    (fun Q ↦ |(H.relativeDensity c Q : ℝ) - H.relativeDensity c (π Q)|)] at htri
  simpa only [nsmul_eq_mul] using htri

open Classical in
/-- **Palette-summed density-deviation bound along a polyad map.** Suppose
`H.polyadEnergy T - H.polyadEnergy S ≤ g`, and let `π : Polyad3 T → Polyad3 S` have moved-triple
set `M = {x | Polyad3.ofTriple S x ≠ π (Polyad3.ofTriple T x)}`. Summing over all fine polyads `Q`
and all colors `c : κ`, the support-weighted total-variation deviation between
`H.relativeDensity · Q` and `H.relativeDensity · (π Q)` is at most
`√(|κ| (g + 3 #M / N)) N + 4 #M`, where `N = |V|.descFactorial 3`. -/
theorem sum_card_support_mul_sum_abs_relativeDensity_polyadMap_le [Fintype κ₂']
    {H : Colored3Graph κ V} (π : Polyad3 T → Polyad3 S) {g : ℝ}
    (hgap : H.polyadEnergy T - H.polyadEnergy S ≤ g) :
    ∑ Q : Polyad3 T, #Q.support * ∑ c,
        |(H.relativeDensity c Q : ℝ) - H.relativeDensity c (π Q)| ≤
      √(Fintype.card κ *
          (g + 3 * #{x | Polyad3.ofTriple S x ≠ π (Polyad3.ofTriple T x)} /
            (Fintype.card V).descFactorial 3)) *
        (Fintype.card V).descFactorial 3 +
      4 * #{x | Polyad3.ofTriple S x ≠ π (Polyad3.ofTriple T x)} := by
  have hcard : #(univ : Finset {x : Fin 3 → V // Function.Injective x}) =
      (Fintype.card V).descFactorial 3 := by
    rw [card_univ, Fintype.card_subtype_injective, Fintype.card_fin]
  -- Bound the fine-to-fiber deviation via product Cauchy--Schwarz.
  have hpart₁ :
      ∑ x : {x : Fin 3 → V // Function.Injective x}, ∑ c,
          |(H.relativeDensity c (Polyad3.ofTriple T x) : ℝ) -
            H.relDensityOn c (fiberSupport π (π (Polyad3.ofTriple T x)))| ≤
        √(Fintype.card κ *
            (g + 3 * #{x | Polyad3.ofTriple S x ≠ π (Polyad3.ofTriple T x)} /
              (Fintype.card V).descFactorial 3)) *
          (Fintype.card V).descFactorial 3 := by
    have hsq : (∑ x : {x : Fin 3 → V // Function.Injective x}, ∑ c,
        ((H.relativeDensity c (Polyad3.ofTriple T x) : ℝ) -
          H.relDensityOn c (fiberSupport π (π (Polyad3.ofTriple T x)))) ^ 2) /
        #(univ : Finset {x : Fin 3 → V // Function.Injective x}) ≤
        g + 3 * #{x | Polyad3.ofTriple S x ≠ π (Polyad3.ofTriple T x)} /
          (Fintype.card V).descFactorial 3 := by
      rw [hcard, H.fiberDensityDeviation_sq π]
      linarith [H.polyadEnergy_sub_fiberEnergy_le π]
    simpa [card_univ, hcard] using univ.sum_sum_abs_le_sqrt univ
      (fun x c ↦ (H.relativeDensity c (Polyad3.ofTriple T x) : ℝ) -
        H.relDensityOn c (fiberSupport π (π (Polyad3.ofTriple T x)))) hsq
  -- Combine with the palette-summed fiber-to-coarse perturbation bound.
  have htri : ∑ x : {x : Fin 3 → V // Function.Injective x}, ∑ c,
      |(H.relativeDensity c (Polyad3.ofTriple T x) : ℝ) -
        H.relativeDensity c (π (Polyad3.ofTriple T x))| ≤
      √(Fintype.card κ *
          (g + 3 * #{x | Polyad3.ofTriple S x ≠ π (Polyad3.ofTriple T x)} /
            (Fintype.card V).descFactorial 3)) *
        (Fintype.card V).descFactorial 3 +
      4 * #{x | Polyad3.ofTriple S x ≠ π (Polyad3.ofTriple T x)} := by
    refine (sum_le_sum fun x _ ↦ (sum_le_sum fun c _ ↦ abs_sub_le
      (H.relativeDensity c (Polyad3.ofTriple T x) : ℝ)
      (H.relDensityOn c (fiberSupport π (π (Polyad3.ofTriple T x))))
      (H.relativeDensity c (π (Polyad3.ofTriple T x)))).trans_eq
      (sum_add_distrib (s := univ))).trans ?_
    rw [sum_add_distrib]
    exact add_le_add hpart₁ (H.sum_sum_abs_relDensityOn_fiberSupport_sub_le π)
  rw [Polyad3.sum_comp_ofTriple
    (fun Q ↦ ∑ c, |(H.relativeDensity c Q : ℝ) - H.relativeDensity c (π Q)|)] at htri
  simpa only [nsmul_eq_mul] using htri

open Classical in
/-- **Single-color density-deviation bound under an approximate coarsening.** Specializes
`Colored3Graph.sum_card_support_mul_abs_relativeDensity_polyadMap_le` to `Polyad3.coarsen hV f`,
bounding the moved triples by `3 #E |V|` where
`E = {p | S.pairColors.color p ≠ f (T.pairColors.color p)}`. -/
theorem sum_card_support_mul_abs_relativeDensity_coarsen_le [Fintype κ₂']
    {H : Colored3Graph κ V} (hV : T.vertexPart ≤ S.vertexPart) (f : κ₂' → κ₂) {g : ℝ}
    (hgap : H.polyadEnergy T - H.polyadEnergy S ≤ g) (c : κ) :
    ∑ Q : Polyad3 T, #Q.support *
        |(H.relativeDensity c Q : ℝ) - H.relativeDensity c (Q.coarsen hV f)| ≤
      √(g + 9 * #{p | S.pairColors.color p ≠ f (T.pairColors.color p)} * Fintype.card V /
          (Fintype.card V).descFactorial 3) * (Fintype.card V).descFactorial 3 +
        6 * #{p | S.pairColors.color p ≠ f (T.pairColors.color p)} * Fintype.card V := by
  refine (sum_card_support_mul_abs_relativeDensity_polyadMap_le
    (fun Q : Polyad3 T ↦ Q.coarsen hV f) hgap c).trans ?_
  have hm : (#{x | Polyad3.ofTriple S x ≠ (Polyad3.ofTriple T x).coarsen hV f} : ℝ) ≤
      3 * #{p | S.pairColors.color p ≠ f (T.pairColors.color p)} * Fintype.card V :=
    mod_cast Polyad3.card_filter_ofTriple_ne_coarsen_ofTriple_le hV f
  refine add_le_add (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt (add_le_add le_rfl ?_))
    (Nat.cast_nonneg _)) (by linarith)
  exact div_le_div_of_nonneg_right (by linarith) (Nat.cast_nonneg _)

open Classical in
/-- **Palette-summed density-deviation bound under an approximate coarsening.** Specializes
`Colored3Graph.sum_card_support_mul_sum_abs_relativeDensity_polyadMap_le` to `Polyad3.coarsen hV f`,
bounding the moved triples by `3 #E |V|` where
`E = {p | S.pairColors.color p ≠ f (T.pairColors.color p)}`. -/
theorem sum_card_support_mul_sum_abs_relativeDensity_coarsen_le [Fintype κ₂']
    {H : Colored3Graph κ V} (hV : T.vertexPart ≤ S.vertexPart) (f : κ₂' → κ₂) {g : ℝ}
    (hgap : H.polyadEnergy T - H.polyadEnergy S ≤ g) :
    ∑ Q : Polyad3 T, #Q.support * ∑ c,
        |(H.relativeDensity c Q : ℝ) - H.relativeDensity c (Q.coarsen hV f)| ≤
      √(Fintype.card κ *
          (g + 9 * #{p | S.pairColors.color p ≠ f (T.pairColors.color p)} * Fintype.card V /
            (Fintype.card V).descFactorial 3)) *
        (Fintype.card V).descFactorial 3 +
      12 * #{p | S.pairColors.color p ≠ f (T.pairColors.color p)} * Fintype.card V := by
  refine (sum_card_support_mul_sum_abs_relativeDensity_polyadMap_le
    (fun Q : Polyad3 T ↦ Q.coarsen hV f) hgap).trans ?_
  have hm : (#{x | Polyad3.ofTriple S x ≠ (Polyad3.ofTriple T x).coarsen hV f} : ℝ) ≤
      3 * #{p | S.pairColors.color p ≠ f (T.pairColors.color p)} * Fintype.card V :=
    mod_cast Polyad3.card_filter_ofTriple_ne_coarsen_ofTriple_le hV f
  refine add_le_add (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt
    (mul_le_mul_of_nonneg_left (add_le_add le_rfl ?_) (Nat.cast_nonneg _)))
    (Nat.cast_nonneg _)) (by linarith)
  exact div_le_div_of_nonneg_right (by linarith) (Nat.cast_nonneg _)

end PolyadMap

/-! ### Two-sided stability under an injective map of polyads -/

section Injective

variable {S : PairSkeleton3 κ₂ V} {T : PairSkeleton3 κ₂' V}

open Classical in
/-- **Energy stability under an injective map of polyads.** Let `f : Polyad3 S → Polyad3 T` be
injective. Then the polyad energies of `H` over `T` and over `S` differ by at most `3` times the
proportion of injective triples whose polyad over `T` is not the image under `f` of their polyad
over `S`, with no factor depending on the size of the palette `κ`. -/
theorem abs_polyadEnergy_sub_le_of_injective (H : Colored3Graph κ V)
    {f : Polyad3 S → Polyad3 T} (hf : Function.Injective f) :
    |H.polyadEnergy T - H.polyadEnergy S| ≤
      3 * #{x | Polyad3.ofTriple T x ≠ f (Polyad3.ofTriple S x)} /
        (Fintype.card V).descFactorial 3 := by
  rcases isEmpty_or_nonempty {x : Fin 3 → V // Function.Injective x} with hE | hN
  · simp [polyadEnergy_def, univ_eq_empty]
  -- Upper bound `H.polyadEnergy T - H.polyadEnergy S` by applying almost-monotonicity to `f`.
  have hup := H.polyadEnergy_sub_le_polyadEnergy_of_polyadMap f
  -- Lower bound via a classical left inverse of `f`.
  have : Nonempty (Polyad3 S) := hN.map (Polyad3.ofTriple S)
  let π : Polyad3 T → Polyad3 S := Function.invFun f
  have hleft : Function.LeftInverse π f := Function.leftInverse_invFun hf
  have hdn := H.polyadEnergy_sub_le_polyadEnergy_of_polyadMap π
  have hM : #{x | Polyad3.ofTriple S x ≠ π (Polyad3.ofTriple T x)} ≤
      #{x | Polyad3.ofTriple T x ≠ f (Polyad3.ofTriple S x)} :=
    card_le_card fun x hx ↦ mem_filter.2 ⟨mem_univ x, fun h ↦ (mem_filter.1 hx).2
      (by rw [h, hleft])⟩
  have hdiv : 3 * (#{x | Polyad3.ofTriple S x ≠ π (Polyad3.ofTriple T x)} : ℝ) /
      (Fintype.card V).descFactorial 3 ≤
      3 * #{x | Polyad3.ofTriple T x ≠ f (Polyad3.ofTriple S x)} /
        (Fintype.card V).descFactorial 3 :=
    div_le_div_of_nonneg_right (by exact_mod_cast Nat.mul_le_mul_left 3 hM) (Nat.cast_nonneg _)
  rw [abs_le]
  exact ⟨by linarith, by linarith⟩

open Classical in
/-- **Energy stability under pair recoloring.** Let `S` and `T` share the same vertex cells, and
suppose the pair colors of `T` agree with those of `S` mapped along an injective `g` outside a set
`E` of ordered pairs. Then `|H.polyadEnergy T - H.polyadEnergy S| ≤ 9 #E |V| / |V|.descFactorial 3`.
-/
theorem abs_polyadEnergy_sub_le_of_pairRecoloring (H : Colored3Graph κ V)
    (hV : S.vertexPart = T.vertexPart) {g : κ₂ → κ₂'} (hg : Function.Injective g) :
    |H.polyadEnergy T - H.polyadEnergy S| ≤
      9 * #{p | T.pairColors.color p ≠ g (S.pairColors.color p)} * Fintype.card V /
        (Fintype.card V).descFactorial 3 := by
  refine (H.abs_polyadEnergy_sub_le_of_injective (Polyad3.coarsen_injective hV hg)).trans ?_
  have hm : (#{x | Polyad3.ofTriple T x ≠ (Polyad3.ofTriple S x).coarsen hV.le g} : ℝ) ≤
      3 * #{p | T.pairColors.color p ≠ g (S.pairColors.color p)} * Fintype.card V := by
    exact_mod_cast Polyad3.card_filter_ofTriple_ne_coarsen_ofTriple_le hV.le g
  refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)
  linarith

/-- **Energy stability under vertex-cell repartition and pair recoloring.** If injective maps `f`
of vertex cells and `g` of pair colors match `S` to `T` outside at most `#B` vertices and `#E`
ordered pairs, then the polyad energy changes by at most
`(9 #B |V|² + 9 #E |V|) / |V|.descFactorial 3`. -/
theorem abs_polyadEnergy_sub_le_of_repartition (H : Colored3Graph κ V)
    {f : S.vertexPart.parts → T.vertexPart.parts} (hf : Function.Injective f)
    {g : κ₂ → κ₂'} (hg : Function.Injective g)
    (B : Finset V) (E : Finset {p : V × V // p.1 ≠ p.2})
    (hcell : ∀ v ∉ B,
      v ∈ (f ⟨S.vertexPart.part v, S.vertexPart.part_mem.2 (mem_univ _)⟩).val)
    (hcolor : ∀ p ∉ E, T.pairColors.color p = g (S.pairColors.color p)) :
    |H.polyadEnergy T - H.polyadEnergy S| ≤
      (9 * #B * Fintype.card V ^ 2 + 9 * #E * Fintype.card V) /
        (Fintype.card V).descFactorial 3 := by
  classical
  refine (H.abs_polyadEnergy_sub_le_of_injective (Polyad3.mapData_injective hf hg)).trans ?_
  have hm : (#{x | Polyad3.ofTriple T x ≠ (Polyad3.ofTriple S x).mapData f g} : ℝ) ≤
      3 * #B * Fintype.card V ^ 2 + 3 * #E * Fintype.card V := by
    exact_mod_cast Polyad3.card_filter_ofTriple_ne_mapData_ofTriple_le f g B E hcell hcolor
  refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)
  linarith

open Classical in
/-- **Almost-monotonicity under vertex refinement and injective pair recoloring.** If
`T.vertexPart ≤ S.vertexPart` and the pair colors of `T` agree with an injective image `g` of those
of `S` outside a set `E` of ordered pairs, then
`H.polyadEnergy S - 9 #E |V| / |V|.descFactorial 3 ≤ H.polyadEnergy T`. Neither a retraction
`κ₂' → κ₂` nor `Nonempty κ₂` is needed. -/
theorem polyadEnergy_sub_le_polyadEnergy_of_vertexPart_le_of_injective (H : Colored3Graph κ V)
    (hV : T.vertexPart ≤ S.vertexPart) {g : κ₂ → κ₂'} (hg : Function.Injective g) :
    H.polyadEnergy S -
        9 * #{p | T.pairColors.color p ≠ g (S.pairColors.color p)} * Fintype.card V /
          (Fintype.card V).descFactorial 3 ≤
      H.polyadEnergy T := by
  -- Factor through the skeleton combining the fine vertex cells with the coarse pair coloring.
  let S' : PairSkeleton3 κ₂ V := ⟨T.vertexPart, S.pairColors⟩
  have hmono : H.polyadEnergy S ≤ H.polyadEnergy S' :=
    H.polyadEnergy_mono_of_refines
      fun _ _ ↦ Polyad3.ofTriple_eq_ofTriple_of_le (S := S) (T := S') hV id fun _ ↦ rfl
  have hstab := (abs_le.1 (H.abs_polyadEnergy_sub_le_of_pairRecoloring (S := S') (T := T) rfl hg)).1
  linarith

end Injective

end TauCeti.Colored3Graph
