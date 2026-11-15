/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Hypergraph.Polyad.Coarsening
public import TauCeti.Combinatorics.Hypergraph.Polyad.Energy.Basic
import Mathlib.Data.Rat.BigOperators
import Mathlib.Tactic.Linarith

/-!
# Stability of polyad energy under recoloring the lower skeleton

Refining the vertex partition or pair palette of a lower skeleton only increases the polyad energy
(`Colored3Graph.polyadEnergy_mono_of_refines`), whereas cleaning up irregular or diagonal pairs
edits the pair coloring on a small set of ordered pairs and therefore moves a small fraction of
injective triples between polyads.

Let `f : Polyad3 S → Polyad3 T` be an injective map of polyads. Comparing the coarse density of
each polyad `P` over `S` with the density over `f P` via the conditional-expectation identity
`Colored3Graph.sum_relativeDensity_ofTriple_mul` shows that the polyad energy of `H` drops from `S`
to `T` by at most twice the proportion of moved injective triples
`{x | Polyad3.ofTriple T x ≠ f (Polyad3.ofTriple S x)}`. When `T` refines the vertex partition of
`S` and its pair coloring agrees with that of `S` along an injective palette map outside a small
set of ordered pairs, combining monotonicity under vertex refinement with
`Polyad3.card_filter_ofTriple_ne_coarsen_ofTriple_le` bounds the energy drop in terms of the number
of edited pairs.

## Main results

* `TauCeti.Colored3Graph.polyadEnergy_sub_le_of_injective`: under an injective map `f` of polyads,
  `H.polyadEnergy S - H.polyadEnergy T` is at most twice the proportion of moved triples.
* `TauCeti.Colored3Graph.polyadEnergy_sub_le_of_pairRecoloring`: refining the vertex cells and
  recoloring `|E|` ordered pairs along an injective palette map lowers the polyad energy by at most
  `6 |E| |V| / |V|.descFactorial 3`.

## References

* V. Rödl and M. Schacht, *Regular partitions of hypergraphs: regularity lemmas*,
  Combin. Probab. Comput. 16 (2007).
* T. Tao, *Szemerédi's regularity lemma revisited*, Contrib. Discrete Math. 1 (2006).
-/

public section

open Finset

namespace TauCeti.Colored3Graph

variable {κ κ₂ κ₂' V : Type*} [Fintype V] [DecidableEq V] [Fintype κ] [DecidableEq κ]
  (H : Colored3Graph κ V)

open Classical in
/-- **Polyad energy drop under an injective polyad map.** For lower skeletons `S` and `T` and an
injective map `f : Polyad3 S → Polyad3 T`, the polyad energy of `H` over `S` exceeds that over `T`
by at most twice the proportion of injective triples `x` whose polyad over `T` differs from
`f (Polyad3.ofTriple S x)`. -/
theorem polyadEnergy_sub_le_of_injective {S : PairSkeleton3 κ₂ V} {T : PairSkeleton3 κ₂' V}
    {f : Polyad3 S → Polyad3 T} (hf : Function.Injective f) :
    H.polyadEnergy S - H.polyadEnergy T ≤
      2 * #{x | Polyad3.ofTriple T x ≠ f (Polyad3.ofTriple S x)} /
        (Fintype.card V).descFactorial 3 := by
  let a (c : κ) (x : {x : Fin 3 → V // Function.Injective x}) : ℝ :=
    H.relativeDensity c (Polyad3.ofTriple S x)
  let gPoly (Q : Polyad3 T) (c : κ) : ℝ :=
    if h : ∃ P : Polyad3 S, f P = Q then H.relativeDensity c (Classical.choose h) else 0
  let g (c : κ) (x : {x : Fin 3 → V // Function.Injective x}) : ℝ :=
    gPoly (Polyad3.ofTriple T x) c
  let b (c : κ) (x : {x : Fin 3 → V // Function.Injective x}) : ℝ :=
    H.relativeDensity c (Polyad3.ofTriple T x)
  let M : Finset {x : Fin 3 → V // Function.Injective x} :=
    {x | Polyad3.ofTriple T x ≠ f (Polyad3.ofTriple S x)}
  have hg_eq (c : κ) {x : {x : Fin 3 → V // Function.Injective x}} (hx : x ∉ M) :
      g c x = a c x := by
    have hfx : Polyad3.ofTriple T x = f (Polyad3.ofTriple S x) := by
      simpa [M] using hx
    have hex : ∃ P : Polyad3 S, f P = Polyad3.ofTriple T x := ⟨Polyad3.ofTriple S x, hfx.symm⟩
    have hchoose : Classical.choose hex = Polyad3.ofTriple S x :=
      hf ((Classical.choose_spec hex).trans hfx)
    simp [g, gPoly, hex, hchoose, a]
  have hg_nonneg (c : κ) (x : {x : Fin 3 → V // Function.Injective x}) : 0 ≤ g c x := by
    dsimp [g, gPoly]
    split_ifs with hex
    · exact_mod_cast H.relativeDensity_nonneg c _
    · exact le_rfl
  have hg_sum_le_one (x : {x : Fin 3 → V // Function.Injective x}) : ∑ c, g c x ^ 2 ≤ 1 := by
    dsimp [g, gPoly]
    by_cases hex : ∃ P : Polyad3 S, f P = Polyad3.ofTriple T x
    · simp only [dite_eq_left hex]
      set P := Classical.choose hex
      calc ∑ c, (H.relativeDensity c P : ℝ) ^ 2
          ≤ ∑ c, (H.relativeDensity c P : ℝ) :=
            sum_le_sum fun c _ ↦ pow_le_of_le_one (mod_cast H.relativeDensity_nonneg c P)
              (mod_cast H.relativeDensity_le_one c P) two_ne_zero
        _ ≤ 1 := by
          obtain hP | hP := P.support.eq_empty_or_nonempty
          · simp [H.relativeDensity_of_support_eq_empty _ hP]
          · have hsum1 : ∑ c, (H.relativeDensity c P : ℝ) = 1 := mod_cast H.sum_relativeDensity hP
            exact hsum1.le
    · simp [dite_eq_right hex]
  -- For each color `c`, use `0 ≤ (b c x - g c x)²` and the conditional-expectation law on `S` and
  -- `T` to bound `∑ x, (a c x² - b c x²)` by a sum supported on `M`.
  have hcolor (c : κ) :
      ∑ x, a c x ^ 2 - ∑ x, b c x ^ 2 ≤
        ∑ x, (2 * (if H.color (Set.powersetCard.ofFinEmb 3 V ⟨x.1, x.2⟩) = c
            then a c x - g c x else 0) + (g c x ^ 2 - a c x ^ 2)) := by
    have ha_id : ∑ x, a c x ^ 2 =
        2 * (∑ x with H.color (Set.powersetCard.ofFinEmb 3 V ⟨x.1, x.2⟩) = c, a c x) -
          ∑ x, a c x ^ 2 := by
      have hmul := H.sum_relativeDensity_ofTriple_mul (S := S) c (a c)
        fun x y hxy ↦ by simp [a, hxy]
      have hsq_eq : ∑ x, a c x ^ 2 =
          ∑ x with H.color (Set.powersetCard.ofFinEmb 3 V ⟨x.1, x.2⟩) = c, a c x := by
        simpa only [sq, a] using hmul
      linarith
    have hbg : 2 * (∑ x with H.color (Set.powersetCard.ofFinEmb 3 V ⟨x.1, x.2⟩) = c, g c x) -
        ∑ x, g c x ^ 2 ≤ ∑ x, b c x ^ 2 := by
      have hmul := H.sum_relativeDensity_ofTriple_mul (S := T) c (g c)
        fun x y hxy ↦ by simp [g, hxy]
      have hsq : ∑ x, (2 * (b c x * g c x) - g c x ^ 2) ≤ ∑ x, b c x ^ 2 :=
        sum_le_sum fun x _ ↦ by nlinarith [sq_nonneg (b c x - g c x)]
      rw [sum_sub_distrib, ← mul_sum] at hsq
      dsimp [b] at hsq
      rw [hmul] at hsq
      exact hsq
    have hrew : (2 * (∑ x with H.color (Set.powersetCard.ofFinEmb 3 V ⟨x.1, x.2⟩) = c, a c x) -
          ∑ x, a c x ^ 2) -
        (2 * (∑ x with H.color (Set.powersetCard.ofFinEmb 3 V ⟨x.1, x.2⟩) = c, g c x) -
          ∑ x, g c x ^ 2) =
        ∑ x, (2 * (if H.color (Set.powersetCard.ofFinEmb 3 V ⟨x.1, x.2⟩) = c
            then a c x - g c x else 0) + (g c x ^ 2 - a c x ^ 2)) := by
      rw [sum_filter, sum_filter, sum_add_distrib, ← mul_sum, sum_sub_distrib]
      have hite : ∑ x, (if H.color (Set.powersetCard.ofFinEmb 3 V ⟨x.1, x.2⟩) = c
            then a c x - g c x else 0) =
          (∑ x, if H.color (Set.powersetCard.ofFinEmb 3 V ⟨x.1, x.2⟩) = c then a c x else 0) -
            ∑ x, if H.color (Set.powersetCard.ofFinEmb 3 V ⟨x.1, x.2⟩) = c then g c x else 0 := by
        rw [← sum_sub_distrib]
        refine sum_congr rfl fun x _ ↦ ?_
        split_ifs <;> ring
      rw [hite]
      ring
    linarith
  rw [polyadEnergy_def, polyadEnergy_def, ← sub_div]
  refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)
  rw [sum_comm (f := fun x c ↦ a c x ^ 2), sum_comm (f := fun x c ↦ b c x ^ 2), ← sum_sub_distrib]
  calc ∑ c, (∑ x, a c x ^ 2 - ∑ x, b c x ^ 2)
      ≤ ∑ c, ∑ x, (2 * (if H.color (Set.powersetCard.ofFinEmb 3 V ⟨x.1, x.2⟩) = c
            then a c x - g c x else 0) + (g c x ^ 2 - a c x ^ 2)) :=
        sum_le_sum fun c _ ↦ hcolor c
    _ = ∑ x, ∑ c, (2 * (if H.color (Set.powersetCard.ofFinEmb 3 V ⟨x.1, x.2⟩) = c
            then a c x - g c x else 0) + (g c x ^ 2 - a c x ^ 2)) := sum_comm
    _ = ∑ x ∈ M, ∑ c, (2 * (if H.color (Set.powersetCard.ofFinEmb 3 V ⟨x.1, x.2⟩) = c
            then a c x - g c x else 0) + (g c x ^ 2 - a c x ^ 2)) := by
        refine (sum_subset (subset_univ M) fun x _ hx ↦ ?_).symm
        refine sum_eq_zero fun c _ ↦ ?_
        rw [hg_eq c hx]
        simp
    _ ≤ ∑ _x ∈ M, (2 : ℝ) := by
        refine sum_le_sum fun x _ ↦ ?_
        set c₀ := H.color (Set.powersetCard.ofFinEmb 3 V ⟨x.1, x.2⟩)
        have hsum_ite : ∑ c, 2 * (if c₀ = c then a c x - g c x else 0) =
            2 * (a c₀ x - g c₀ x) := by
          rw [← mul_sum, sum_ite_eq, ite_eq_left (mem_univ c₀)]
        rw [sum_add_distrib, hsum_ite, sum_sub_distrib]
        have ha_le : 2 * a c₀ x - ∑ c, a c x ^ 2 ≤ 1 := by
          have hsingle : a c₀ x ^ 2 ≤ ∑ c, a c x ^ 2 :=
            single_le_sum (fun c _ ↦ sq_nonneg (a c x)) (mem_univ c₀)
          nlinarith [sq_nonneg (1 - a c₀ x)]
        have hg_le : ∑ c, g c x ^ 2 - 2 * g c₀ x ≤ 1 := by
          linarith [hg_sum_le_one x, hg_nonneg c₀ x]
        linarith
    _ = 2 * #M := by
        rw [sum_const, nsmul_eq_mul, mul_comm]

open Classical in
/-- **Polyad energy drop under vertex refinement and pair recoloring.** Let the vertex partition of
`T` refine that of `S`, and let `g : κ₂ → κ₂'` be an injective palette map. The polyad energy of
`H` drops from `S` to `T` by at most `6 |E| |V| / |V|.descFactorial 3`, where `E` is the set of
ordered distinct pairs `p` at which `T.pairColors.color p ≠ g (S.pairColors.color p)`. -/
theorem polyadEnergy_sub_le_of_pairRecoloring {S : PairSkeleton3 κ₂ V} {T : PairSkeleton3 κ₂' V}
    (hV : T.vertexPart ≤ S.vertexPart) {g : κ₂ → κ₂'} (hg : Function.Injective g) :
    H.polyadEnergy S - H.polyadEnergy T ≤
      (6 * #{p | T.pairColors.color p ≠ g (S.pairColors.color p)} * Fintype.card V : ℕ) /
        (Fintype.card V).descFactorial 3 := by
  -- Refine `S` to the vertex partition of `T` without changing the pair coloring; this only
  -- increases `polyadEnergy`. Then compare with `T` on the common vertex partition.
  let S' : PairSkeleton3 κ₂ V := ⟨T.vertexPart, S.pairColors⟩
  have href : H.polyadEnergy S ≤ H.polyadEnergy S' :=
    H.polyadEnergy_mono_of_refines (S := S) (T := S') fun x y hxy ↦ by
      have hc := Polyad3.coarsen_ofTriple (S := S) (T := S') hV id (fun _ ↦ rfl)
      rw [← hc x, ← hc y, hxy]
  have hcoarsen_inj :
      Function.Injective (fun P : Polyad3 S' ↦ Polyad3.coarsen (S := T) P rfl.le g) :=
    Polyad3.coarsen_injective (S := T) (T := S') rfl hg
  have hdrop := H.polyadEnergy_sub_le_of_injective (S := S') (T := T) hcoarsen_inj
  have hmoved :
      #{x | Polyad3.ofTriple T x ≠ Polyad3.coarsen (S := T) (Polyad3.ofTriple S' x) rfl.le g} ≤
        3 * #{p | T.pairColors.color p ≠ g (S.pairColors.color p)} * Fintype.card V :=
    Polyad3.card_filter_ofTriple_ne_coarsen_ofTriple_le (S := T) (T := S') rfl.le g
  calc H.polyadEnergy S - H.polyadEnergy T
      ≤ H.polyadEnergy S' - H.polyadEnergy T := by linarith
    _ ≤ 2 *
          #{x | Polyad3.ofTriple T x ≠ Polyad3.coarsen (S := T) (Polyad3.ofTriple S' x) rfl.le g} /
            (Fintype.card V).descFactorial 3 := hdrop
    _ ≤ 2 * (3 * #{p | T.pairColors.color p ≠ g (S.pairColors.color p)} * Fintype.card V : ℕ) /
          (Fintype.card V).descFactorial 3 := by
        gcongr
    _ = (6 * #{p | T.pairColors.color p ≠ g (S.pairColors.color p)} * Fintype.card V : ℕ) /
          (Fintype.card V).descFactorial 3 := by
        push_cast
        ring

end TauCeti.Colored3Graph
