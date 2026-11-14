/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Hypergraph.Polyad.Coarsening
public import TauCeti.Combinatorics.Hypergraph.Polyad.Energy.Basic
public import TauCeti.Combinatorics.Hypergraph.Polyad.Repartition
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
lower-skeleton edits, with constants independent of the size of the top palette `κ`:

1. **Two-sided Lipschitz stability under an injective polyad map.** Given an injective map
   `f : Polyad3 S → Polyad3 T`, let `M` be the set of moved injective triples
   `{x | Polyad3.ofTriple T x ≠ f (Polyad3.ofTriple S x)}`. Applying the palette-independent
   squared-density perturbation estimate (`Colored3Graph.sum_card_mul_sq_relDensityOn_sub_le`) to
   each matched pair `(P.support, (f P).support)` and charging unmatched polyads over `T` to their
   moved triples yields
   `|H.polyadEnergy T - H.polyadEnergy S| ≤ 3 #M / |V|.descFactorial 3`
   (`Colored3Graph.abs_polyadEnergy_sub_le_of_injective`). Combining this with the moved-triple
   bounds in `Polyad/Coarsening.lean` and `Polyad/Repartition.lean` controls the energy change
   under pair recolorings and vertex-cell repartitions.

2. **Almost-monotonicity and approximate energy-gap deviation bounds.** Given any map
   `π : Polyad3 T → Polyad3 S`, its fibers `F_P = {x | π (Polyad3.ofTriple T x) = P}` form an
   exact coarsening of the polyads over `T`. Conditional expectation over `F_P` gives an exact
   mean-square defect identity between `T` and the fiber partition, while `F_P` and `P.support`
   differ only in triples of `M = {x | Polyad3.ofTriple S x ≠ π (Polyad3.ofTriple T x)}`. Hence:
   * `H.polyadEnergy S - 3 #M / |V|.descFactorial 3 ≤ H.polyadEnergy T`
     (`Colored3Graph.polyadEnergy_sub_le_of_polyadMap`), and similarly when `T.vertexPart` refines
     `S.vertexPart` and the pair colors of `S` embed injectively into those of `T` off a small
     edited pair set (`Colored3Graph.polyadEnergy_sub_le_of_vertexPart_le_of_injective`);
   * when `H.polyadEnergy T - H.polyadEnergy S ≤ g`, the support-weighted `L¹` density deviations
     between each fine polyad `Q` and `π Q` are bounded for a single color by
     `√(g + 3 #M / N) N + 2 #M`
     (`Colored3Graph.sum_card_support_mul_abs_relativeDensity_polyadMap_le`) and summed over all
     colors in `κ` by `√(|κ| (g + 3 #M / N)) N + 4 #M`
     (`Colored3Graph.sum_card_support_mul_sum_abs_relativeDensity_polyadMap_le`), where
     `N = |V|.descFactorial 3`. When `M = ∅`, both estimates specialize without loss to the exact
     refinement bounds.

## Main results

* `TauCeti.Colored3Graph.abs_polyadEnergy_sub_le_of_injective`: two-sided energy stability under an
  injective map of polyads.
* `TauCeti.Colored3Graph.abs_polyadEnergy_sub_le_of_pairRecoloring` and
  `TauCeti.Colored3Graph.abs_polyadEnergy_sub_le_of_mapData`: energy stability under pair
  recolorings and vertex-cell repartitions.
* `TauCeti.Colored3Graph.polyadEnergy_sub_le_of_polyadMap`,
  `TauCeti.Colored3Graph.polyadEnergy_sub_le_of_coarsen`, and
  `TauCeti.Colored3Graph.polyadEnergy_sub_le_of_vertexPart_le_of_injective`: almost-monotonicity of
  polyad energy under approximate coarsenings and refining pair recolorings.
* `TauCeti.Colored3Graph.sum_card_support_mul_abs_relativeDensity_polyadMap_le` and
  `TauCeti.Colored3Graph.sum_card_support_mul_sum_abs_relativeDensity_polyadMap_le`: single-color
  and palette-summed coarse-to-fine density-deviation bounds from an approximate energy gap.

## References

* V. Rödl and M. Schacht, *Regular partitions of hypergraphs: regularity lemmas*,
  Combin. Probab. Comput. 16 (2007).
* T. Tao, *Szemerédi's regularity lemma revisited*, Contrib. Discrete Math. 1 (2006).
-/

public section

open Finset

namespace TauCeti.Colored3Graph

/-! ### Support-weighted squared density helpers -/

/-- On any support `W`, the support-weighted sum of squared color densities is at most `#W`. -/
private theorem sum_card_mul_sq_relDensityOn_le_card {κ V : Type*} [DecidableEq κ] [Fintype κ]
    (H : Colored3Graph κ V) (W : Finset {x : Fin 3 → V // Function.Injective x}) :
    ∑ c, (#W : ℝ) * (H.relDensityOn c W : ℝ) ^ 2 ≤ #W := by
  rw [← mul_sum]
  refine mul_le_of_le_one_right (Nat.cast_nonneg _) ?_
  calc ∑ c, (H.relDensityOn c W : ℝ) ^ 2
      ≤ ∑ c, (H.relDensityOn c W : ℝ) :=
        sum_le_sum fun c _ ↦ pow_le_of_le_one (mod_cast H.relDensityOn_nonneg c W)
          (mod_cast H.relDensityOn_le_one c W) two_ne_zero
    _ ≤ 1 := mod_cast H.sum_relDensityOn_le_one W

variable {κ κ₂ κ₂' V : Type*} [Fintype V] [DecidableEq V] [DecidableEq κ] [Fintype κ]

/-- Express `polyadEnergy` with a single outer division by `|V|.descFactorial 3`. -/
private theorem polyadEnergy_eq_sum_support_div [Fintype κ₂] (H : Colored3Graph κ V)
    (S : PairSkeleton3 κ₂ V) :
    H.polyadEnergy S =
      (∑ P : Polyad3 S, ∑ c, (#P.support : ℝ) * (H.relDensityOn c P.support : ℝ) ^ 2) /
        (Fintype.card V).descFactorial 3 := by
  rw [H.polyadEnergy_eq_sum_polyad S, sum_div]
  refine sum_congr rfl fun P _ ↦ ?_
  rw [sum_div]
  refine sum_congr rfl fun c _ ↦ ?_
  rw [relativeDensity_def, div_mul_eq_mul_div]

/-! ### Two-sided stability under an injective map of polyads -/

section Injective

variable {S : PairSkeleton3 κ₂ V} {T : PairSkeleton3 κ₂' V}

/-- **Energy stability under an injective map of polyads.** Let `f : Polyad3 S → Polyad3 T` be
injective. Then the polyad energies of `H` over `T` and over `S` differ by at most `3` times the
proportion of injective triples whose polyad over `T` is not the image under `f` of their polyad
over `S`, with no factor depending on the size of the palette `κ`. -/
theorem abs_polyadEnergy_sub_le_of_injective [Finite κ₂] [Finite κ₂'] [DecidableEq κ₂']
    (H : Colored3Graph κ V) {f : Polyad3 S → Polyad3 T} (hf : Function.Injective f) :
    |H.polyadEnergy T - H.polyadEnergy S| ≤
      3 * #{x | Polyad3.ofTriple T x ≠ f (Polyad3.ofTriple S x)} /
        (Fintype.card V).descFactorial 3 := by
  cases nonempty_fintype κ₂
  cases nonempty_fintype κ₂'
  set M : Finset {x : Fin 3 → V // Function.Injective x} :=
    {x | Polyad3.ofTriple T x ≠ f (Polyad3.ofTriple S x)}
  set I : Finset (Polyad3 T) := univ.image f
  let E : Finset {x : Fin 3 → V // Function.Injective x} → ℝ :=
    fun W ↦ ∑ c, (#W : ℝ) * (H.relDensityOn c W : ℝ) ^ 2
  have hsplit (F : Polyad3 T → ℝ) : ∑ Q, F Q = ∑ Q ∈ univ \ I, F Q + ∑ P, F (f P) := by
    rw [← sum_sdiff (subset_univ I), sum_image hf.injOn]
  -- Unmatched polyads over `T` consist entirely of moved triples.
  have hout_le : ∀ Q ∈ univ \ I, E Q.support ≤ #(M ∩ Q.support) := by
    intro Q hQ
    have hsub : Q.support ⊆ M := fun x hx ↦ mem_filter.2 ⟨mem_univ _, fun h ↦
      (mem_sdiff.1 hQ).2 (mem_image.2 ⟨_, mem_univ _,
        h.symm.trans (Polyad3.mem_support_iff_eq_ofTriple.1 hx).symm⟩)⟩
    refine (H.sum_card_mul_sq_relDensityOn_le_card Q.support).trans_eq ?_
    rw [inter_eq_right.2 hsub]
  have hout_nonneg : ∀ Q ∈ univ \ I, 0 ≤ E Q.support :=
    fun _ _ ↦ sum_nonneg fun _ _ ↦ mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)
  -- Triples in the symmetric difference of `P.support` and `(f P).support` belong to `M`.
  have hsdiff₁ (P : Polyad3 S) : (#((f P).support \ P.support) : ℝ) ≤ #(M ∩ (f P).support) := by
    refine Nat.cast_le.2 (card_le_card fun x hx ↦ ?_)
    obtain ⟨hxQ, hxP⟩ := mem_sdiff.1 hx
    refine mem_inter.2 ⟨mem_filter.2 ⟨mem_univ _, fun h ↦ hxP ?_⟩, hxQ⟩
    exact Polyad3.mem_support_iff_eq_ofTriple.2
      (hf ((Polyad3.mem_support_iff_eq_ofTriple.1 hxQ).trans h))
  have hsdiff₂ (P : Polyad3 S) : (#(P.support \ (f P).support) : ℝ) ≤ #(M ∩ P.support) := by
    refine Nat.cast_le.2 (card_le_card fun x hx ↦ ?_)
    obtain ⟨hxP, hxQ⟩ := mem_sdiff.1 hx
    refine mem_inter.2 ⟨mem_filter.2 ⟨mem_univ _, fun h ↦ hxQ ?_⟩, hxP⟩
    rw [Polyad3.mem_support_iff_eq_ofTriple, Polyad3.mem_support_iff_eq_ofTriple.1 hxP]
    exact h.symm
  have hup (P : Polyad3 S) :
      E (f P).support - E P.support ≤ 2 * #(M ∩ (f P).support) + #(M ∩ P.support) := by
    have hq : E (f P).support - E P.support ≤
        2 * (#((f P).support \ P.support) : ℝ) + #(P.support \ (f P).support) := by
      dsimp only [E]
      exact_mod_cast H.sum_card_mul_sq_relDensityOn_sub_le (f P).support P.support
    linarith [hsdiff₁ P, hsdiff₂ P]
  have hdn (P : Polyad3 S) :
      E P.support - E (f P).support ≤ 2 * #(M ∩ P.support) + #(M ∩ (f P).support) := by
    have hq : E P.support - E (f P).support ≤
        2 * (#(P.support \ (f P).support) : ℝ) + #((f P).support \ P.support) := by
      dsimp only [E]
      exact_mod_cast H.sum_card_mul_sq_relDensityOn_sub_le P.support (f P).support
    linarith [hsdiff₁ P, hsdiff₂ P]
  have hMT : ∑ Q ∈ univ \ I, (#(M ∩ Q.support) : ℝ) + ∑ P, (#(M ∩ (f P).support) : ℝ) = #M := by
    rw [← hsplit fun Q ↦ (#(M ∩ Q.support) : ℝ)]
    exact_mod_cast Polyad3.sum_card_inter_support (S := T) M
  have hMS : ∑ P : Polyad3 S, (#(M ∩ P.support) : ℝ) = #M := by
    exact_mod_cast Polyad3.sum_card_inter_support (S := S) M
  have hMT_out_nonneg : 0 ≤ ∑ Q ∈ univ \ I, (#(M ∩ Q.support) : ℝ) :=
    sum_nonneg fun _ _ ↦ Nat.cast_nonneg _
  have hsum_up : ∑ Q : Polyad3 T, E Q.support - ∑ P : Polyad3 S, E P.support ≤ 3 * #M := by
    rw [hsplit fun Q ↦ E Q.support, add_sub_assoc, ← sum_sub_distrib]
    have h₁ := sum_le_sum hout_le
    have h₂ := sum_le_sum fun (P : Polyad3 S) (_ : P ∈ univ) ↦ hup P
    rw [sum_add_distrib, ← mul_sum, hMS] at h₂
    linarith
  have hsum_dn : ∑ P : Polyad3 S, E P.support - ∑ Q : Polyad3 T, E Q.support ≤ 3 * #M := by
    rw [hsplit fun Q ↦ E Q.support, sub_add_eq_sub_sub, sub_right_comm, ← sum_sub_distrib]
    have h₁ := sum_nonneg hout_nonneg
    have h₂ := sum_le_sum fun (P : Polyad3 S) (_ : P ∈ univ) ↦ hdn P
    rw [sum_add_distrib, ← mul_sum, hMS] at h₂
    linarith
  rw [H.polyadEnergy_eq_sum_support_div T, H.polyadEnergy_eq_sum_support_div S, ← sub_div,
    abs_div, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) ((Fintype.card V).descFactorial 3))]
  refine div_le_div_of_nonneg_right (abs_le.2 ⟨?_, hsum_up⟩) (Nat.cast_nonneg _)
  dsimp only [E] at hsum_dn
  linarith

/-- **Energy stability under pair recoloring.** Let `S` and `T` share the same vertex cells, and
suppose the pair colors of `T` agree with those of `S` mapped along an injective `g` outside a set
`E` of ordered pairs. Then `|H.polyadEnergy T - H.polyadEnergy S| ≤ 9 #E |V| / |V|.descFactorial 3`.
-/
theorem abs_polyadEnergy_sub_le_of_pairRecoloring [Finite κ₂] [Finite κ₂'] [DecidableEq κ₂']
    (H : Colored3Graph κ V) (hV : S.vertexPart = T.vertexPart)
    {g : κ₂ → κ₂'} (hg : Function.Injective g) :
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
theorem abs_polyadEnergy_sub_le_of_mapData [Finite κ₂] [Finite κ₂']
    (H : Colored3Graph κ V) {f : S.vertexPart.parts → T.vertexPart.parts}
    (hf : Function.Injective f) {g : κ₂ → κ₂'} (hg : Function.Injective g)
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

end Injective

/-! ### Almost-monotonicity and approximate energy-gap deviation bounds -/

section PolyadMap

variable {S : PairSkeleton3 κ₂ V} {T : PairSkeleton3 κ₂' V}

/-- The fiber of injective triples assigned to a coarse polyad `P` through `π` and
`Polyad3.ofTriple T`. -/
private noncomputable def fiberSupport [DecidableEq κ₂] (π : Polyad3 T → Polyad3 S)
    (P : Polyad3 S) : Finset {x : Fin 3 → V // Function.Injective x} :=
  {x | π (Polyad3.ofTriple T x) = P}

@[simp]
private theorem mem_fiberSupport [DecidableEq κ₂] {π : Polyad3 T → Polyad3 S} {P : Polyad3 S}
    {x : {x : Fin 3 → V // Function.Injective x}} :
    x ∈ fiberSupport π P ↔ π (Polyad3.ofTriple T x) = P := by
  simp [fiberSupport]

/-- Exact conditional-expectation defect identity between the fine polyads over `T` and the fibers
of `π : Polyad3 T → Polyad3 S`. -/
private theorem fiberDensityDeviation_sq [Fintype κ₂] [DecidableEq κ₂]
    (H : Colored3Graph κ V) (π : Polyad3 T → Polyad3 S) :
    (∑ x : {x : Fin 3 → V // Function.Injective x}, ∑ c,
        ((H.relativeDensity c (Polyad3.ofTriple T x) : ℝ) -
          H.relDensityOn c (fiberSupport π (π (Polyad3.ofTriple T x)))) ^ 2) /
        (Fintype.card V).descFactorial 3 =
      H.polyadEnergy T -
        (∑ P : Polyad3 S, ∑ c, (#(fiberSupport π P) : ℝ) *
          (H.relDensityOn c (fiberSupport π P) : ℝ) ^ 2) /
          (Fintype.card V).descFactorial 3 := by
  have hsq (c : κ) :
      ∑ x : {x : Fin 3 → V // Function.Injective x},
          (H.relDensityOn c (fiberSupport π (π (Polyad3.ofTriple T x))) : ℝ) ^ 2 =
        ∑ P : Polyad3 S, (#(fiberSupport π P) : ℝ) *
          (H.relDensityOn c (fiberSupport π P) : ℝ) ^ 2 := by
    rw [← sum_fiberwise univ (fun x ↦ π (Polyad3.ofTriple T x))]
    refine sum_congr rfl fun P _ ↦ ?_
    have hf : {x ∈ (univ : Finset {x : Fin 3 → V // Function.Injective x}) |
        π (Polyad3.ofTriple T x) = P} = fiberSupport π P := by
      ext x
      simp
    rw [hf, sum_congr rfl fun x hx ↦ by rw [mem_fiberSupport.1 hx], sum_const, nsmul_eq_mul]
  have hcorr (c : κ) :
      ∑ x : {x : Fin 3 → V // Function.Injective x},
          (H.relativeDensity c (Polyad3.ofTriple T x) : ℝ) *
            H.relDensityOn c (fiberSupport π (π (Polyad3.ofTriple T x))) =
        ∑ P : Polyad3 S, (#(fiberSupport π P) : ℝ) *
          (H.relDensityOn c (fiberSupport π P) : ℝ) ^ 2 := by
    rw [H.sum_relativeDensity_ofTriple_mul (S := T) c _ fun x y hxy ↦ by rw [hxy],
      ← sum_fiberwise _ (fun x ↦ π (Polyad3.ofTriple T x))]
    refine sum_congr rfl fun P _ ↦ ?_
    have hf : {x ∈ univ.filter
        (fun x : {x : Fin 3 → V // Function.Injective x} ↦
          H.color (Set.powersetCard.ofFinEmb 3 V ⟨x.1, x.2⟩) = c) |
        π (Polyad3.ofTriple T x) = P} =
        {x ∈ fiberSupport π P | H.color (Set.powersetCard.ofFinEmb 3 V ⟨x.1, x.2⟩) = c} := by
      ext x
      simp [and_comm]
    rw [hf, sum_congr rfl fun x hx ↦ by rw [mem_fiberSupport.1 (mem_filter.1 hx).1],
      sum_const, nsmul_eq_mul]
    have hmul : (#{x ∈ fiberSupport π P |
        H.color (Set.powersetCard.ofFinEmb 3 V ⟨x.1, x.2⟩) = c} : ℝ) =
        (H.relDensityOn c (fiberSupport π P) : ℝ) * #(fiberSupport π P) := by
      exact_mod_cast (H.relDensityOn_mul_card c (fiberSupport π P)).symm
    rw [hmul]
    ring
  rw [polyadEnergy_def, ← sub_div, sum_comm,
    sum_comm (s := univ) (t := univ)
      (f := fun x c ↦ (H.relativeDensity c (Polyad3.ofTriple T x) : ℝ) ^ 2),
    sum_comm (s := univ) (t := univ)
      (f := fun P c ↦ (#(fiberSupport π P) : ℝ) * (H.relDensityOn c (fiberSupport π P) : ℝ) ^ 2),
    ← sum_sub_distrib]
  congr 1
  refine sum_congr rfl fun c _ ↦ ?_
  simp only [sub_sq, sum_add_distrib, sum_sub_distrib, mul_assoc, ← mul_sum]
  rw [hcorr c, hsq c]
  ring

/-- Triples in `P.support \ fiberSupport π P` satisfy
`Polyad3.ofTriple S x ≠ π (Polyad3.ofTriple T x)`. -/
private theorem card_sdiff_fiberSupport_le [DecidableEq κ₂] (π : Polyad3 T → Polyad3 S)
    (P : Polyad3 S) :
    #(P.support \ fiberSupport π P) ≤
      #(({x | Polyad3.ofTriple S x ≠ π (Polyad3.ofTriple T x)} : Finset _) ∩ P.support) := by
  refine card_le_card fun x hx ↦ ?_
  obtain ⟨hxP, hxF⟩ := mem_sdiff.1 hx
  rw [mem_fiberSupport] at hxF
  exact mem_inter.2 ⟨mem_filter.2 ⟨mem_univ _,
    fun h ↦ hxF ((Polyad3.mem_support_iff_eq_ofTriple.1 hxP).trans h).symm⟩, hxP⟩

/-- Triples in `fiberSupport π P \ P.support` satisfy
`Polyad3.ofTriple S x ≠ π (Polyad3.ofTriple T x)`. -/
private theorem card_fiberSupport_sdiff_le [DecidableEq κ₂] (π : Polyad3 T → Polyad3 S)
    (P : Polyad3 S) :
    #(fiberSupport π P \ P.support) ≤
      #(({x | Polyad3.ofTriple S x ≠ π (Polyad3.ofTriple T x)} : Finset _) ∩
        fiberSupport π P) := by
  refine card_le_card fun x hx ↦ ?_
  obtain ⟨hxF, hxP⟩ := mem_sdiff.1 hx
  exact mem_inter.2 ⟨mem_filter.2 ⟨mem_univ _, fun h ↦ hxP
    (Polyad3.mem_support_iff_eq_ofTriple.2 ((mem_fiberSupport.1 hxF).symm.trans h.symm))⟩, hxF⟩

/-- The fibers `fiberSupport π P` partition every finite set of injective triples. -/
private theorem sum_card_inter_fiberSupport [Fintype κ₂] [DecidableEq κ₂]
    (π : Polyad3 T → Polyad3 S) (s : Finset {x : Fin 3 → V // Function.Injective x}) :
    ∑ P : Polyad3 S, #(s ∩ fiberSupport π P) = #s := by
  rw [card_eq_sum_card_fiberwise (s := s)
    (f := fun x ↦ π (Polyad3.ofTriple T x)) (t := univ) fun _ _ ↦ mem_univ _]
  refine sum_congr rfl fun P _ ↦ congrArg card ?_
  ext x
  simp

/-- Comparing the polyad energy over `S` with the squared-density sum over the fibers of `π` costs
at most `3 #M / |V|.descFactorial 3`, where `M` is the set of triples with
`Polyad3.ofTriple S x ≠ π (Polyad3.ofTriple T x)`. -/
private theorem polyadEnergy_sub_fiberEnergy_le [Fintype κ₂] [DecidableEq κ₂]
    (H : Colored3Graph κ V) (π : Polyad3 T → Polyad3 S) :
    H.polyadEnergy S -
        (∑ P : Polyad3 S, ∑ c, (#(fiberSupport π P) : ℝ) *
          (H.relDensityOn c (fiberSupport π P) : ℝ) ^ 2) /
          (Fintype.card V).descFactorial 3 ≤
      3 * #{x | Polyad3.ofTriple S x ≠ π (Polyad3.ofTriple T x)} /
        (Fintype.card V).descFactorial 3 := by
  set M : Finset {x : Fin 3 → V // Function.Injective x} :=
    {x | Polyad3.ofTriple S x ≠ π (Polyad3.ofTriple T x)}
  have hloc (P : Polyad3 S) :
      ∑ c, (#P.support : ℝ) * (H.relDensityOn c P.support : ℝ) ^ 2 -
        ∑ c, (#(fiberSupport π P) : ℝ) * (H.relDensityOn c (fiberSupport π P) : ℝ) ^ 2 ≤
      2 * #(M ∩ P.support) + #(M ∩ fiberSupport π P) := by
    have hq : ∑ c, (#P.support : ℝ) * (H.relDensityOn c P.support : ℝ) ^ 2 -
        ∑ c, (#(fiberSupport π P) : ℝ) * (H.relDensityOn c (fiberSupport π P) : ℝ) ^ 2 ≤
        2 * (#(P.support \ fiberSupport π P) : ℝ) + #(fiberSupport π P \ P.support) := by
      exact_mod_cast H.sum_card_mul_sq_relDensityOn_sub_le P.support (fiberSupport π P)
    have hs₁ : (#(P.support \ fiberSupport π P) : ℝ) ≤ #(M ∩ P.support) :=
      Nat.cast_le.2 (card_sdiff_fiberSupport_le π P)
    have hs₂ : (#(fiberSupport π P \ P.support) : ℝ) ≤ #(M ∩ fiberSupport π P) :=
      Nat.cast_le.2 (card_fiberSupport_sdiff_le π P)
    linarith
  have hMS : ∑ P : Polyad3 S, (#(M ∩ P.support) : ℝ) = #M := by
    exact_mod_cast Polyad3.sum_card_inter_support (S := S) M
  have hMF : ∑ P : Polyad3 S, (#(M ∩ fiberSupport π P) : ℝ) = #M := by
    exact_mod_cast sum_card_inter_fiberSupport π M
  rw [H.polyadEnergy_eq_sum_support_div S, ← sub_div, ← sum_sub_distrib]
  refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)
  have hsum := sum_le_sum fun (P : Polyad3 S) (_ : P ∈ univ) ↦ hloc P
  rw [sum_add_distrib, ← mul_sum, hMS, hMF] at hsum
  linarith

/-- **Almost-monotonicity of polyad energy along a polyad map.** For any map
`π : Polyad3 T → Polyad3 S`, the polyad energy over `T` is at least the polyad energy over `S`
minus `3` times the proportion of injective triples with
`Polyad3.ofTriple S x ≠ π (Polyad3.ofTriple T x)`. -/
theorem polyadEnergy_sub_le_of_polyadMap [Finite κ₂] [DecidableEq κ₂]
    (H : Colored3Graph κ V) (π : Polyad3 T → Polyad3 S) :
    H.polyadEnergy S -
        3 * #{x | Polyad3.ofTriple S x ≠ π (Polyad3.ofTriple T x)} /
          (Fintype.card V).descFactorial 3 ≤
      H.polyadEnergy T := by
  cases nonempty_fintype κ₂
  have hnonneg : 0 ≤ H.polyadEnergy T -
      (∑ P : Polyad3 S, ∑ c, (#(fiberSupport π P) : ℝ) *
        (H.relDensityOn c (fiberSupport π P) : ℝ) ^ 2) /
        (Fintype.card V).descFactorial 3 := by
    rw [← H.fiberDensityDeviation_sq π]
    exact div_nonneg (sum_nonneg fun _ _ ↦ sum_nonneg fun _ _ ↦ sq_nonneg _) (Nat.cast_nonneg _)
  linarith [H.polyadEnergy_sub_fiberEnergy_le π]

/-- **Almost-monotonicity under an approximate coarsening.** If `T.vertexPart ≤ S.vertexPart` and
the pair colors of `S` agree with `f ∘ T.pairColors.color` outside a set `E` of ordered pairs, then
`H.polyadEnergy S - 9 #E |V| / |V|.descFactorial 3 ≤ H.polyadEnergy T`. -/
theorem polyadEnergy_sub_le_of_coarsen [Finite κ₂] [DecidableEq κ₂]
    (H : Colored3Graph κ V) (hV : T.vertexPart ≤ S.vertexPart) (f : κ₂' → κ₂) :
    H.polyadEnergy S -
        9 * #{p | S.pairColors.color p ≠ f (T.pairColors.color p)} * Fintype.card V /
          (Fintype.card V).descFactorial 3 ≤
      H.polyadEnergy T := by
  refine le_trans ?_ (H.polyadEnergy_sub_le_of_polyadMap fun Q : Polyad3 T ↦ Q.coarsen hV f)
  have hm : (#{x | Polyad3.ofTriple S x ≠ (Polyad3.ofTriple T x).coarsen hV f} : ℝ) ≤
      3 * #{p | S.pairColors.color p ≠ f (T.pairColors.color p)} * Fintype.card V := by
    exact_mod_cast Polyad3.card_filter_ofTriple_ne_coarsen_ofTriple_le hV f
  have hdiv : 3 * (#{x | Polyad3.ofTriple S x ≠ (Polyad3.ofTriple T x).coarsen hV f} : ℝ) /
      (Fintype.card V).descFactorial 3 ≤
      9 * #{p | S.pairColors.color p ≠ f (T.pairColors.color p)} * Fintype.card V /
        (Fintype.card V).descFactorial 3 :=
    div_le_div_of_nonneg_right (by linarith) (Nat.cast_nonneg _)
  linarith

/-- **Almost-monotonicity under vertex refinement and injective pair recoloring.** If
`T.vertexPart ≤ S.vertexPart` and the pair colors of `T` agree with an injective image `g` of those
of `S` outside a set `E` of ordered pairs, then
`H.polyadEnergy S - 9 #E |V| / |V|.descFactorial 3 ≤ H.polyadEnergy T`. Neither a retraction
`κ₂' → κ₂` nor `Nonempty κ₂` is needed. -/
theorem polyadEnergy_sub_le_of_vertexPart_le_of_injective [Finite κ₂] [Finite κ₂']
    [DecidableEq κ₂'] (H : Colored3Graph κ V) (hV : T.vertexPart ≤ S.vertexPart)
    {g : κ₂ → κ₂'} (hg : Function.Injective g) :
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

omit [DecidableEq κ] [Fintype κ] in
/-- Uniform Cauchy--Schwarz bound over `{x : Fin 3 → V // Function.Injective x} × α`. -/
private theorem sum_abs_injective_le_sqrt {α : Type*} [Fintype α]
    (f : {x : Fin 3 → V // Function.Injective x} × α → ℝ) {g' : ℝ}
    (hgap : (∑ x, ∑ a, f (x, a) ^ 2) / (Fintype.card V).descFactorial 3 ≤ g') :
    ∑ x, ∑ a, |f (x, a)| ≤
      √(Fintype.card α * g') * (Fintype.card V).descFactorial 3 := by
  obtain hN | hN := eq_or_ne ((Fintype.card V).descFactorial 3) 0
  · have : IsEmpty {x : Fin 3 → V // Function.Injective x} := by
      rw [← Fintype.card_eq_zero_iff, Fintype.card_subtype_injective, Fintype.card_fin, hN]
    rw [univ_eq_empty, sum_empty, hN, Nat.cast_zero, mul_zero]
  set N : ℝ := ((Fintype.card V).descFactorial 3 : ℝ)
  set A : ℝ := (Fintype.card α : ℝ)
  have hN₀ : 0 < N := Nat.cast_pos.2 (Nat.pos_of_ne_zero hN)
  have hg₀ : 0 ≤ g' :=
    (div_nonneg (sum_nonneg fun _ _ ↦ sum_nonneg fun _ _ ↦ sq_nonneg _) hN₀.le).trans hgap
  have hsq : ∑ x : {x : Fin 3 → V // Function.Injective x}, ∑ a : α, f (x, a) ^ 2 ≤ g' * N :=
    (div_le_iff₀ hN₀).1 hgap
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt
    ((univ : Finset {x : Fin 3 → V // Function.Injective x}) ×ˢ (univ : Finset α))
    (fun p ↦ |f p|) 1
  simp only [Pi.one_apply, mul_one, sq_abs, one_pow, sum_const, card_product, card_univ,
    Fintype.card_subtype_injective, Fintype.card_fin, nsmul_one, Nat.cast_mul, sum_product] at hcs
  calc ∑ x, ∑ a, |f (x, a)|
      ≤ √(g' * N) * √(N * A) :=
        hcs.trans (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hsq) (Real.sqrt_nonneg _))
    _ = √((A * g') * N ^ 2) := by
        rw [← Real.sqrt_mul (mul_nonneg hg₀ hN₀.le)]
        congr 1
        ring
    _ = √(A * g') * N := by
        rw [Real.sqrt_mul (mul_nonneg (Nat.cast_nonneg _) hg₀), Real.sqrt_sq hN₀.le]

/-- **Single-color density-deviation bound along a polyad map.** Suppose
`H.polyadEnergy T - H.polyadEnergy S ≤ g`, and let `π : Polyad3 T → Polyad3 S` have moved-triple
set `M = {x | Polyad3.ofTriple S x ≠ π (Polyad3.ofTriple T x)}`. Then for each top color `c`, the
support-weighted `L¹` deviation between `H.relativeDensity c Q` and `H.relativeDensity c (π Q)` is
at most `√(g + 3 #M / N) N + 2 #M`, where `N = |V|.descFactorial 3`. -/
theorem sum_card_support_mul_abs_relativeDensity_polyadMap_le [Finite κ₂] [DecidableEq κ₂]
    [Fintype κ₂'] {H : Colored3Graph κ V} (π : Polyad3 T → Polyad3 S) {g : ℝ}
    (hgap : H.polyadEnergy T - H.polyadEnergy S ≤ g) (c : κ) :
    ∑ Q : Polyad3 T, #Q.support *
        |(H.relativeDensity c Q : ℝ) - H.relativeDensity c (π Q)| ≤
      √(g + 3 * #{x | Polyad3.ofTriple S x ≠ π (Polyad3.ofTriple T x)} /
          (Fintype.card V).descFactorial 3) * (Fintype.card V).descFactorial 3 +
        2 * #{x | Polyad3.ofTriple S x ≠ π (Polyad3.ofTriple T x)} := by
  cases nonempty_fintype κ₂
  set M : Finset {x : Fin 3 → V // Function.Injective x} :=
    {x | Polyad3.ofTriple S x ≠ π (Polyad3.ofTriple T x)}
  set N : ℝ := ((Fintype.card V).descFactorial 3 : ℝ)
  set g' : ℝ := g + 3 * #M / N
  have hfib_gap :
      (∑ x : {x : Fin 3 → V // Function.Injective x},
          ((H.relativeDensity c (Polyad3.ofTriple T x) : ℝ) -
            H.relDensityOn c (fiberSupport π (π (Polyad3.ofTriple T x)))) ^ 2) / N ≤ g' := by
    refine (div_le_div_of_nonneg_right (sum_le_sum fun x _ ↦ single_le_sum
      (f := fun c' ↦ ((H.relativeDensity c' (Polyad3.ofTriple T x) : ℝ) -
        H.relDensityOn c' (fiberSupport π (π (Polyad3.ofTriple T x)))) ^ 2)
      (fun _ _ ↦ sq_nonneg _) (mem_univ c)) (Nat.cast_nonneg _)).trans ?_
    rw [H.fiberDensityDeviation_sq π]
    linarith [H.polyadEnergy_sub_fiberEnergy_le π]
  have hpart₁ :
      ∑ x : {x : Fin 3 → V // Function.Injective x},
          |(H.relativeDensity c (Polyad3.ofTriple T x) : ℝ) -
            H.relDensityOn c (fiberSupport π (π (Polyad3.ofTriple T x)))| ≤ √g' * N := by
    have hcs := sum_abs_injective_le_sqrt (α := Unit)
      (fun p ↦ (H.relativeDensity c (Polyad3.ofTriple T p.1) : ℝ) -
        H.relDensityOn c (fiberSupport π (π (Polyad3.ofTriple T p.1))))
      (by simpa only [univ_unique, sum_singleton] using hfib_gap)
    simpa only [univ_unique, sum_singleton, Fintype.card_unit, Nat.cast_one, one_mul] using hcs
  have hpart₂ :
      ∑ x : {x : Fin 3 → V // Function.Injective x},
          |(H.relDensityOn c (fiberSupport π (π (Polyad3.ofTriple T x))) : ℝ) -
            H.relativeDensity c (π (Polyad3.ofTriple T x))| ≤ 2 * #M := by
    rw [← sum_fiberwise univ (fun x ↦ π (Polyad3.ofTriple T x))]
    have hloc (P : Polyad3 S) :
        ∑ x ∈ univ.filter (fun x ↦ π (Polyad3.ofTriple T x) = P),
            |(H.relDensityOn c (fiberSupport π (π (Polyad3.ofTriple T x))) : ℝ) -
              H.relativeDensity c (π (Polyad3.ofTriple T x))| ≤
          (#(M ∩ fiberSupport π P) : ℝ) + #(M ∩ P.support) := by
      have hf : {x ∈ (univ : Finset {x : Fin 3 → V // Function.Injective x}) |
          π (Polyad3.ofTriple T x) = P} = fiberSupport π P := by ext x; simp
      rw [hf, sum_congr rfl fun x hx ↦ by rw [mem_fiberSupport.1 hx], sum_const, nsmul_eq_mul,
        mul_comm, relativeDensity_def]
      have hd : |(H.relDensityOn c (fiberSupport π P) : ℝ) - H.relDensityOn c P.support| *
          #(fiberSupport π P) ≤
          (#(fiberSupport π P \ P.support) : ℝ) + #(P.support \ fiberSupport π P) := by
        exact_mod_cast H.abs_relDensityOn_sub_mul_card_le c (fiberSupport π P) P.support
      linarith [show (#(fiberSupport π P \ P.support) : ℝ) ≤ #(M ∩ fiberSupport π P) from
        Nat.cast_le.2 (card_fiberSupport_sdiff_le π P),
        show (#(P.support \ fiberSupport π P) : ℝ) ≤ #(M ∩ P.support) from
        Nat.cast_le.2 (card_sdiff_fiberSupport_le π P)]
    have hMS : ∑ P : Polyad3 S, (#(M ∩ P.support) : ℝ) = #M :=
      mod_cast Polyad3.sum_card_inter_support (S := S) M
    have hMF : ∑ P : Polyad3 S, (#(M ∩ fiberSupport π P) : ℝ) = #M :=
      mod_cast sum_card_inter_fiberSupport π M
    have hsum := sum_le_sum fun (P : Polyad3 S) (_ : P ∈ univ) ↦ hloc P
    rw [sum_add_distrib, hMF, hMS] at hsum
    linarith
  have htri : ∑ x : {x : Fin 3 → V // Function.Injective x},
      |(H.relativeDensity c (Polyad3.ofTriple T x) : ℝ) -
        H.relativeDensity c (π (Polyad3.ofTriple T x))| ≤ √g' * N + 2 * #M := by
    refine (sum_le_sum fun x _ ↦ abs_sub_le
      (H.relativeDensity c (Polyad3.ofTriple T x) : ℝ)
      (H.relDensityOn c (fiberSupport π (π (Polyad3.ofTriple T x))))
      (H.relativeDensity c (π (Polyad3.ofTriple T x)))).trans ?_
    rw [sum_add_distrib]
    exact add_le_add hpart₁ hpart₂
  rw [Polyad3.sum_comp_ofTriple
    (fun Q ↦ |(H.relativeDensity c Q : ℝ) - H.relativeDensity c (π Q)|)] at htri
  simpa only [nsmul_eq_mul] using htri

/-- **Palette-summed density-deviation bound along a polyad map.** Suppose
`H.polyadEnergy T - H.polyadEnergy S ≤ g`, and let `π : Polyad3 T → Polyad3 S` have moved-triple
set `M = {x | Polyad3.ofTriple S x ≠ π (Polyad3.ofTriple T x)}`. Summing over all fine polyads `Q`
and all colors `c : κ`, the support-weighted total-variation deviation between
`H.relativeDensity · Q` and `H.relativeDensity · (π Q)` is at most
`√(|κ| (g + 3 #M / N)) N + 4 #M`, where `N = |V|.descFactorial 3`. -/
theorem sum_card_support_mul_sum_abs_relativeDensity_polyadMap_le [Finite κ₂] [DecidableEq κ₂]
    [Fintype κ₂'] {H : Colored3Graph κ V} (π : Polyad3 T → Polyad3 S) {g : ℝ}
    (hgap : H.polyadEnergy T - H.polyadEnergy S ≤ g) :
    ∑ Q : Polyad3 T, #Q.support * ∑ c,
        |(H.relativeDensity c Q : ℝ) - H.relativeDensity c (π Q)| ≤
      √(Fintype.card κ *
          (g + 3 * #{x | Polyad3.ofTriple S x ≠ π (Polyad3.ofTriple T x)} /
            (Fintype.card V).descFactorial 3)) *
        (Fintype.card V).descFactorial 3 +
      4 * #{x | Polyad3.ofTriple S x ≠ π (Polyad3.ofTriple T x)} := by
  cases nonempty_fintype κ₂
  set M : Finset {x : Fin 3 → V // Function.Injective x} :=
    {x | Polyad3.ofTriple S x ≠ π (Polyad3.ofTriple T x)}
  set N : ℝ := ((Fintype.card V).descFactorial 3 : ℝ)
  set g' : ℝ := g + 3 * #M / N
  have hpart₁ :
      ∑ x : {x : Fin 3 → V // Function.Injective x}, ∑ c,
          |(H.relativeDensity c (Polyad3.ofTriple T x) : ℝ) -
            H.relDensityOn c (fiberSupport π (π (Polyad3.ofTriple T x)))| ≤
        √(Fintype.card κ * g') * N :=
    sum_abs_injective_le_sqrt
      (fun p ↦ (H.relativeDensity p.2 (Polyad3.ofTriple T p.1) : ℝ) -
        H.relDensityOn p.2 (fiberSupport π (π (Polyad3.ofTriple T p.1))))
      (by rw [H.fiberDensityDeviation_sq π]; linarith [H.polyadEnergy_sub_fiberEnergy_le π])
  have hpart₂ :
      ∑ x : {x : Fin 3 → V // Function.Injective x}, ∑ c,
          |(H.relDensityOn c (fiberSupport π (π (Polyad3.ofTriple T x))) : ℝ) -
            H.relativeDensity c (π (Polyad3.ofTriple T x))| ≤ 4 * #M := by
    rw [← sum_fiberwise univ (fun x ↦ π (Polyad3.ofTriple T x))]
    have hloc (P : Polyad3 S) :
        ∑ x ∈ univ.filter (fun x ↦ π (Polyad3.ofTriple T x) = P), ∑ c,
            |(H.relDensityOn c (fiberSupport π (π (Polyad3.ofTriple T x))) : ℝ) -
              H.relativeDensity c (π (Polyad3.ofTriple T x))| ≤
          2 * ((#(M ∩ fiberSupport π P) : ℝ) + #(M ∩ P.support)) := by
      have hf : {x ∈ (univ : Finset {x : Fin 3 → V // Function.Injective x}) |
          π (Polyad3.ofTriple T x) = P} = fiberSupport π P := by ext x; simp
      rw [hf, sum_congr rfl fun x hx ↦ by rw [mem_fiberSupport.1 hx], sum_const, nsmul_eq_mul,
        mul_comm]
      simp_rw [relativeDensity_def]
      have hd : (∑ c, |(H.relDensityOn c (fiberSupport π P) : ℝ) - H.relDensityOn c P.support|) *
          #(fiberSupport π P) ≤
          2 * ((#(fiberSupport π P \ P.support) : ℝ) + #(P.support \ fiberSupport π P)) := by
        exact_mod_cast H.sum_abs_relDensityOn_sub_mul_card_le (fiberSupport π P) P.support
      linarith [show (#(fiberSupport π P \ P.support) : ℝ) ≤ #(M ∩ fiberSupport π P) from
        Nat.cast_le.2 (card_fiberSupport_sdiff_le π P),
        show (#(P.support \ fiberSupport π P) : ℝ) ≤ #(M ∩ P.support) from
        Nat.cast_le.2 (card_sdiff_fiberSupport_le π P)]
    have hMS : ∑ P : Polyad3 S, (#(M ∩ P.support) : ℝ) = #M :=
      mod_cast Polyad3.sum_card_inter_support (S := S) M
    have hMF : ∑ P : Polyad3 S, (#(M ∩ fiberSupport π P) : ℝ) = #M :=
      mod_cast sum_card_inter_fiberSupport π M
    have hsum := sum_le_sum fun (P : Polyad3 S) (_ : P ∈ univ) ↦ hloc P
    rw [← mul_sum, sum_add_distrib, hMF, hMS] at hsum
    linarith
  have htri : ∑ x : {x : Fin 3 → V // Function.Injective x}, ∑ c,
      |(H.relativeDensity c (Polyad3.ofTriple T x) : ℝ) -
        H.relativeDensity c (π (Polyad3.ofTriple T x))| ≤
      √(Fintype.card κ * g') * N + 4 * #M := by
    refine (sum_le_sum fun x _ ↦ (sum_le_sum fun c _ ↦ abs_sub_le
      (H.relativeDensity c (Polyad3.ofTriple T x) : ℝ)
      (H.relDensityOn c (fiberSupport π (π (Polyad3.ofTriple T x))))
      (H.relativeDensity c (π (Polyad3.ofTriple T x)))).trans_eq
      (sum_add_distrib (s := univ))).trans ?_
    rw [sum_add_distrib]
    exact add_le_add hpart₁ hpart₂
  rw [Polyad3.sum_comp_ofTriple
    (fun Q ↦ ∑ c, |(H.relativeDensity c Q : ℝ) - H.relativeDensity c (π Q)|)] at htri
  simpa only [nsmul_eq_mul] using htri

/-- **Single-color density-deviation bound under an approximate coarsening.** Specializes
`Colored3Graph.sum_card_support_mul_abs_relativeDensity_polyadMap_le` to `Polyad3.coarsen hV f`,
bounding the moved triples by `3 #E |V|` where
`E = {p | S.pairColors.color p ≠ f (T.pairColors.color p)}`. -/
theorem sum_card_support_mul_abs_relativeDensity_coarsen_le_of_polyadEnergy_sub_le
    [Finite κ₂] [DecidableEq κ₂] [Fintype κ₂'] {H : Colored3Graph κ V}
    (hV : T.vertexPart ≤ S.vertexPart) (f : κ₂' → κ₂) {g : ℝ}
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

/-- **Palette-summed density-deviation bound under an approximate coarsening.** Specializes
`Colored3Graph.sum_card_support_mul_sum_abs_relativeDensity_polyadMap_le` to `Polyad3.coarsen hV f`,
bounding the moved triples by `3 #E |V|` where
`E = {p | S.pairColors.color p ≠ f (T.pairColors.color p)}`. -/
theorem sum_card_support_mul_sum_abs_relativeDensity_coarsen_le_of_polyadEnergy_sub_le
    [Finite κ₂] [DecidableEq κ₂] [Fintype κ₂'] {H : Colored3Graph κ V}
    (hV : T.vertexPart ≤ S.vertexPart) (f : κ₂' → κ₂) {g : ℝ}
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

end TauCeti.Colored3Graph
