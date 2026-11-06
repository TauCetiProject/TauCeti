/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Hypergraph.Polyad.Coarsening
public import TauCeti.Combinatorics.Hypergraph.Polyad.SupportStability
public import TauCeti.Combinatorics.Hypergraph.Triadic.Basic
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Exceptional polyad mass after recoloring the pairs

A regular lower skeleton can be obtained from an arbitrary one by recoloring some of its pairs,
for instance the pairs inside the vertex cells and those between cells forming an irregular pair.
This file shows that a coloring `H` of the triples stays top-regular over most polyads of the
recolored skeleton, provided few pairs are recolored.

Fix lower skeletons `S` and `T` and an injective map `f` from polyads over `S` to polyads over
`T`. A triple is *moved* if its polyad over `T` is not the image under `f` of its polyad
over `S`. A polyad `f P` whose support and that of `P` differ in at most an `η`-fraction of each
inherits top regularity from `P`. Every other polyad over `T` is charged to its moved triples,
with a loss of `1 / η`. The support of the irregular polyads over `T` is therefore at most that
over `S` plus `(1 + 2 / η)` times the number of moved triples
(`Colored3Graph.sum_card_support_not_isTopRegularOverPolyad_le_of_injective`).

When `T` has the vertex cells of `S` and its pair colors are obtained by an injective map `g`
except on a set `E` of ordered pairs, taking `f P` to be the polyad with the same cells and the
colors mapped by `g` moves at most `3 |E| |V|` triples
(`Polyad3.card_filter_ofTriple_ne_coarsen_ofTriple_le` in `Polyad/Coarsening.lean`). The new
pair palette may be larger, for example by a fresh color for the pairs inside the cells. For
polyad decompositions of triadic complexes this yields
`Colored3Graph.TopRegularOverMostPolyads.of_pairRecoloring`.

## Main results

* `TauCeti.Colored3Graph.sum_card_support_not_isTopRegularOverPolyad_le_of_injective`: the
  support of the irregular polyads grows by at most a multiple of the moved triples.
* `TauCeti.Colored3Graph.exceptionalPolyadMass_le_of_injective`: the same bound for the
  exceptional mass of polyad decompositions.
* `TauCeti.Colored3Graph.TopRegularOverMostPolyads.of_pairRecoloring`: top regularity over
  most polyads survives recoloring few pairs of the lower skeleton.

## References

* V. Rödl and M. Schacht, *Regular partitions of hypergraphs: regularity lemmas*,
  Combin. Probab. Comput. 16 (2007).
-/

public section

open Finset

namespace TauCeti

variable {κ κ₂ κ₂' V : Type*} [Fintype V] [DecidableEq V]

namespace Colored3Graph

variable [DecidableEq κ] {S : PairSkeleton3 κ₂ V} {T : PairSkeleton3 κ₂' V} {H : Colored3Graph κ V}
  {f : Polyad3 S → Polyad3 T} {δ ε η : ℝ} {r : ℕ}

open Classical in
/-- One polyad and its image: if the image is irregular, it is charged to the irregular support
of the original polyad and to the moved triples, collected in `M`, in either support. -/
private theorem card_support_not_isTopRegularOverPolyad_le (hf : Function.Injective f)
    (hε : 0 < ε) (hη : 0 < η) (hbudget : δ + 2 * η + η / ε ≤ ε)
    {M : Finset {x : Fin 3 → V // Function.Injective x}}
    (hM : ∀ x, Polyad3.ofTriple T x ≠ f (Polyad3.ofTriple S x) → x ∈ M) (P : Polyad3 S) :
    (if ¬H.IsTopRegularOverPolyad (f P) ε r then (#(f P).support : ℝ) else 0) ≤
      (if ¬H.IsTopRegularOverPolyad P δ r then (#P.support : ℝ) else 0) +
        #(M ∩ (f P).support) + (#(M ∩ (f P).support) + #(M ∩ P.support)) / η := by
  -- Triples in exactly one of the two supports are moved.
  have hQ : (#((f P).support \ P.support) : ℝ) ≤ #(M ∩ (f P).support) := by
    refine Nat.cast_le.2 (card_le_card fun x hx ↦ ?_)
    obtain ⟨hxQ, hxP⟩ := mem_sdiff.1 hx
    refine mem_inter.2 ⟨hM x fun h ↦ hxP ?_, hxQ⟩
    exact Polyad3.mem_support_iff_eq_ofTriple.2
      (hf ((Polyad3.mem_support_iff_eq_ofTriple.1 hxQ).trans h))
  have hP : (#(P.support \ (f P).support) : ℝ) ≤ #(M ∩ P.support) := by
    refine Nat.cast_le.2 (card_le_card fun x hx ↦ ?_)
    obtain ⟨hxP, hxQ⟩ := mem_sdiff.1 hx
    refine mem_inter.2 ⟨hM x fun h ↦ hxQ ?_, hxP⟩
    rw [Polyad3.mem_support_iff_eq_ofTriple, Polyad3.mem_support_iff_eq_ofTriple.1 hxP]
    exact h.symm
  have hcard : (#(f P).support : ℝ) ≤ #((f P).support \ P.support) + #P.support := by
    exact_mod_cast card_le_card_sdiff_add_card
  have hMQ : (0 : ℝ) ≤ #(M ∩ (f P).support) / η := by positivity
  have hMP : (0 : ℝ) ≤ #(M ∩ P.support) / η := by positivity
  have hsum : (#(M ∩ (f P).support) + #(M ∩ P.support) : ℝ) / η =
      #(M ∩ (f P).support) / η + #(M ∩ P.support) / η := add_div _ _ _
  rw [hsum]
  by_cases hnew : H.IsTopRegularOverPolyad (f P) ε r
  · simp only [hnew, not_true_eq_false, ↓reduceIte]
    positivity
  simp only [hnew, not_false_eq_true, ↓reduceIte]
  by_cases hold : H.IsTopRegularOverPolyad P δ r
  · simp only [hold, not_true_eq_false, ↓reduceIte, zero_add]
    -- A regular original polyad passes regularity on unless a support difference is large.
    obtain h₁ | h₁ := le_or_gt (#((f P).support \ P.support) : ℝ) (η * #(f P).support)
    · obtain h₂ | h₂ := le_or_gt (#(P.support \ (f P).support) : ℝ) (η * #P.support)
      · exact absurd (hold.of_card_sdiff_support_le hε hη.le hbudget h₁ h₂) hnew
      · have : (#P.support : ℝ) ≤ #(M ∩ P.support) / η := by
          rw [le_div_iff₀ hη]
          linarith
        linarith
    · have : (#(f P).support : ℝ) ≤ #(M ∩ (f P).support) / η := by
        rw [le_div_iff₀ hη]
        linarith
      have : (0 : ℝ) ≤ #(M ∩ (f P).support) := Nat.cast_nonneg _
      linarith
  · simp only [hold, not_false_eq_true, ↓reduceIte]
    linarith

open Classical in
/-- **Exceptional support after recoloring the pairs.** Let `f` be an injective map from polyads
over `S` to polyads over `T`, and call a triple moved when its polyad over `T` is not the image
of its polyad over `S`. If the parameters satisfy `δ + 2η + η / ε ≤ ε`, the support of the
polyads over `T` that are not `(ε, r)`-top-regular is at most that of the polyads over `S` that
are not `(δ, r)`-top-regular, plus `(1 + 2 / η)` times the number of moved triples. -/
theorem sum_card_support_not_isTopRegularOverPolyad_le_of_injective [Fintype κ₂] [Fintype κ₂']
    [DecidableEq κ₂'] (hf : Function.Injective f)
    (hε : 0 < ε) (hη : 0 < η) (hbudget : δ + 2 * η + η / ε ≤ ε) :
    (∑ Q : Polyad3 T with ¬H.IsTopRegularOverPolyad Q ε r, (#Q.support : ℝ)) ≤
      (∑ P : Polyad3 S with ¬H.IsTopRegularOverPolyad P δ r, (#P.support : ℝ)) +
        (1 + 2 / η) * #{x | Polyad3.ofTriple T x ≠ f (Polyad3.ofTriple S x)} := by
  set M : Finset {x : Fin 3 → V // Function.Injective x} :=
    {x | Polyad3.ofTriple T x ≠ f (Polyad3.ofTriple S x)}
  set I : Finset (Polyad3 T) := univ.image f
  -- The polyads over `T` outside the image of `f` consist of moved triples.
  have hout : ∀ Q ∈ univ \ I, (if ¬H.IsTopRegularOverPolyad Q ε r then (#Q.support : ℝ) else 0) ≤
      #(M ∩ Q.support) := by
    intro Q hQ
    have hsub : Q.support ⊆ M := fun x hx ↦ mem_filter.2 ⟨mem_univ _, fun h ↦
      (mem_sdiff.1 hQ).2 (mem_image.2 ⟨_, mem_univ _,
        (h.symm.trans (Polyad3.mem_support_iff_eq_ofTriple.1 hx).symm)⟩)⟩
    rw [inter_eq_right.2 hsub]
    split_ifs <;> simp
  have hsplit (F : Polyad3 T → ℝ) : ∑ Q, F Q = ∑ Q ∈ univ \ I, F Q + ∑ P, F (f P) := by
    rw [← sum_sdiff (subset_univ I), sum_image hf.injOn]
  have hT := Polyad3.sum_card_inter_support (S := T) M
  have hS := Polyad3.sum_card_inter_support (S := S) M
  have hM : (0 : ℝ) ≤ #M := Nat.cast_nonneg _
  rw [sum_filter, sum_filter, hsplit]
  have hT' : ∑ Q ∈ univ \ I, (#(M ∩ Q.support) : ℝ) + ∑ P, (#(M ∩ (f P).support) : ℝ) = #M := by
    rw [← hsplit fun Q ↦ (#(M ∩ Q.support) : ℝ)]
    exact_mod_cast hT
  have hS' : ∑ P : Polyad3 S, (#(M ∩ P.support) : ℝ) = #M := by exact_mod_cast hS
  have hloc := sum_le_sum fun (P : Polyad3 S) (_ : P ∈ univ) ↦
    card_support_not_isTopRegularOverPolyad_le (H := H) (r := r) hf hε hη hbudget
      (fun x hx ↦ mem_filter.2 ⟨mem_univ x, hx⟩) P
  rw [sum_add_distrib, sum_add_distrib, ← sum_div, sum_add_distrib, hS'] at hloc
  have hout' := sum_le_sum hout
  have hle : ∑ P, (#(M ∩ (f P).support) : ℝ) ≤ #M := by
    have : (0 : ℝ) ≤ ∑ Q ∈ univ \ I, (#(M ∩ Q.support) : ℝ) := sum_nonneg fun _ _ ↦ by positivity
    linarith
  have hdiv : (∑ P, (#(M ∩ (f P).support) : ℝ) + #M) / η ≤ 2 / η * #M := by
    rw [div_mul_eq_mul_div, two_mul]
    gcongr
  linarith

open Classical in
/-- **Exceptional mass after recoloring the pairs.** For polyad decompositions `C` and `D` and
an injective map `f` from polyads over the skeleton of `C` to polyads over that of `D`,
the exceptional mass grows by at most `(1 + 2 / η)` times the proportion of moved triples among
all `|V| (|V| - 1) (|V| - 2)` injective triples, when `δ + 2η + η / ε ≤ ε`. -/
theorem exceptionalPolyadMass_le_of_injective {C D : TriadicComplex3 V}
    (hC : C.IsPolyadDecomposition) (hD : D.IsPolyadDecomposition)
    {f : Polyad3 C.skeleton → Polyad3 D.skeleton} (hf : Function.Injective f)
    (hε : 0 < ε) (hη : 0 < η) (hbudget : δ + 2 * η + η / ε ≤ ε) :
    H.exceptionalPolyadMass D ε r ≤ H.exceptionalPolyadMass C δ r +
      (1 + 2 / η) * #{x | Polyad3.ofTriple D.skeleton x ≠ f (Polyad3.ofTriple C.skeleton x)} /
        (Fintype.card V).descFactorial 3 := by
  rw [exceptionalPolyadMass_eq_sum_div hD, exceptionalPolyadMass_eq_sum_div hC, ← add_div]
  exact div_le_div_of_nonneg_right
    (sum_card_support_not_isTopRegularOverPolyad_le_of_injective hf hε hη hbudget)
    (Nat.cast_nonneg _)

/-- **Top regularity after recoloring few pairs.** Let `C` and `D` be polyad decompositions on
the same vertex cells, and suppose the pair colors of `D` are those of `C` mapped by an injective
`g`, except on a set `E` of ordered pairs. If `H` is `(δ, r)`-top-regular over all but an
`ε₀`-proportion of the polyads of `C`, then it is `(ε, r)`-top-regular over all but an
`ε₀ + (1 + 2 / η) 3 |E| |V| / (|V| (|V| - 1) (|V| - 2))`-proportion of those of `D`, provided
`δ + 2η + η / ε ≤ ε`. -/
theorem TopRegularOverMostPolyads.of_pairRecoloring {C D : TriadicComplex3 V} {ε₀ : ℝ}
    (h : H.TopRegularOverMostPolyads C δ ε₀ r) (hC : C.IsPolyadDecomposition)
    (hD : D.IsPolyadDecomposition) (hV : C.skeleton.vertexPart = D.skeleton.vertexPart)
    {g : Fin C.pairColorCount → Fin D.pairColorCount} (hg : Function.Injective g)
    (hε : 0 < ε) (hη : 0 < η) (hbudget : δ + 2 * η + η / ε ≤ ε) :
    H.TopRegularOverMostPolyads D ε (ε₀ + (1 + 2 / η) *
      (3 * #{p | D.skeleton.pairColors.color p ≠ g (C.skeleton.pairColors.color p)} *
        Fintype.card V : ℕ) / (Fintype.card V).descFactorial 3) r := by
  rw [topRegularOverMostPolyads_iff] at h ⊢
  refine (exceptionalPolyadMass_le_of_injective hC hD (Polyad3.coarsen_injective hV hg)
    hε hη hbudget).trans (add_le_add h ?_)
  gcongr
  exact Polyad3.card_filter_ofTriple_ne_coarsen_ofTriple_le hV.le g

end Colored3Graph

end TauCeti
