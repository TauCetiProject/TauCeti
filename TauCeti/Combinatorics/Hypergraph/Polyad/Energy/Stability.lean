/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Hypergraph.Polyad.Energy.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import TauCeti.Combinatorics.Hypergraph.Polyad.Coarsening

/-!
# Stability of polyad energy under pair recoloring

A lower skeleton `S` partitions the injective triples of `V` into the supports of its polyads,
and the polyad energy `H.polyadEnergy S` is the mean of `|P.support| · ∑ c, d_H(c | P)²` over
these supports, divided by `|V|.descFactorial 3`.

For any coloring `f : α → κ` with finite palette and any finite set `A : Finset α`, the
unnormalized fiber energy `Φ(A) = ∑ c, |{x ∈ A | f x = c}|² / |A|` satisfies `0 ≤ Φ(A) ≤ |A|`,
is subadditive on disjoint unions (`Φ(C ∪ D) ≤ Φ(C) + Φ(D)` by Cauchy–Schwarz), and drops by at
most `|D|` when `D` is adjoined to a disjoint set `C` (`Φ(C) - Φ(C ∪ D) ≤ |D|`). Comparing two
sets through their intersection therefore gives `|Φ(A) - Φ(B)| ≤ |A \ B| + |B \ A|`.

Summing over polyads along an injective correspondence `f : Polyad3 S → Polyad3 T` shows that
the polyad energies of `S` and `T` differ by at most twice the proportion of moved triples, those
whose polyad over `T` is not `f` of their polyad over `S`
(`Colored3Graph.abs_polyadEnergy_sub_polyadEnergy_le_of_injective`). When `T` has the same vertex
cells as `S` and recolors `E` ordered pairs along an injective palette map `g`, at most
`3 |E| |V|` triples move (`Polyad3.card_filter_ofTriple_ne_coarsen_ofTriple_le`), so the energy
changes by at most `6 |E| |V| / |V|.descFactorial 3`
(`Colored3Graph.abs_polyadEnergy_sub_polyadEnergy_le_of_pairRecoloring`). Refining the vertex
cells at the same time can only raise the energy before the pair recoloring, giving the one-sided
loss bound `Colored3Graph.polyadEnergy_sub_polyadEnergy_le_of_le_of_pairRecoloring`.

## Main results

* `TauCeti.Colored3Graph.abs_polyadEnergy_sub_polyadEnergy_le_of_injective`: polyad energy changes
  by at most twice the fraction of moved triples under an injective polyad map.
* `TauCeti.Colored3Graph.abs_polyadEnergy_sub_polyadEnergy_le_of_pairRecoloring`: polyad energy
  stability under recoloring few pairs on fixed vertex cells.
* `TauCeti.Colored3Graph.polyadEnergy_sub_polyadEnergy_le_of_le_of_pairRecoloring`: one-sided
  polyad energy stability under simultaneous vertex-cell refinement and pair recoloring.

## References

* V. Rödl and M. Schacht, *Regular partitions of hypergraphs: regularity lemmas*,
  Combin. Probab. Comput. 16 (2007), the energy-increment argument for hypergraph regularity.
* N. Alon, E. Fischer, M. Krivelevich and M. Szegedy, *Efficient testing of large graphs*,
  Combinatorica 20 (2000).
-/

public section

open Finset

namespace TauCeti.Colored3Graph

section FiberEnergy

variable {α κ : Type*} [DecidableEq κ] [Fintype κ]

/-- Unnormalized fiber energy `∑ c, |{x ∈ s | f x = c}|² / |s|` of a coloring `f` on `s`. -/
private noncomputable def fiberEnergy (f : α → κ) (s : Finset α) : ℝ :=
  ∑ c, (#{x ∈ s | f x = c} : ℝ) ^ 2 / #s

private theorem fiberEnergy_nonneg (f : α → κ) (s : Finset α) : 0 ≤ fiberEnergy f s :=
  sum_nonneg fun _ _ ↦ by positivity

private theorem fiberEnergy_empty (f : α → κ) : fiberEnergy f ∅ = 0 := by
  simp [fiberEnergy]

private theorem fiberEnergy_le_card (f : α → κ) (s : Finset α) : fiberEnergy f s ≤ #s := by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · simp [fiberEnergy_empty]
  have hs0 : (0 : ℝ) < #s := Nat.cast_pos.2 hs.card_pos
  calc fiberEnergy f s
      ≤ ∑ c, (#{x ∈ s | f x = c} : ℝ) := by
        refine sum_le_sum fun c _ ↦ ?_
        have hle : (#{x ∈ s | f x = c} : ℝ) ≤ #s := Nat.cast_le.2 (card_filter_le _ _)
        rw [div_le_iff₀ hs0, sq]
        exact mul_le_mul_of_nonneg_left hle (Nat.cast_nonneg _)
    _ = #s := by
        exact_mod_cast (card_eq_sum_card_fiberwise (f := f) (t := univ) fun _ _ ↦ mem_univ _).symm

/-- Two-term Cauchy–Schwarz inequality in ratio form, including zero denominators when the
corresponding numerators vanish. -/
private theorem add_sq_div_add_le {a b m k : ℝ} (hm : 0 ≤ m) (hk : 0 ≤ k)
    (ham : m = 0 → a = 0) (hbk : k = 0 → b = 0) :
    (a + b) ^ 2 / (m + k) ≤ a ^ 2 / m + b ^ 2 / k := by
  obtain rfl | hm' := hm.eq_or_lt
  · simp [ham rfl]
  obtain rfl | hk' := hk.eq_or_lt
  · simp [hbk rfl]
  rw [← sub_nonneg]
  have hEq : a ^ 2 / m + b ^ 2 / k - (a + b) ^ 2 / (m + k) =
      (k * a - m * b) ^ 2 / (m * k * (m + k)) := by
    field_simp
    ring
  rw [hEq]
  positivity

private theorem fiberEnergy_union_le_add [DecidableEq α] (f : α → κ) {s t : Finset α}
    (h : Disjoint s t) :
    fiberEnergy f (s ∪ t) ≤ fiberEnergy f s + fiberEnergy f t := by
  rw [fiberEnergy, fiberEnergy, fiberEnergy, ← sum_add_distrib]
  refine sum_le_sum fun c _ ↦ ?_
  have hd : Disjoint {x ∈ s | f x = c} {x ∈ t | f x = c} :=
    h.mono (filter_subset _ _) (filter_subset _ _)
  rw [filter_union, card_union_of_disjoint hd, card_union_of_disjoint h]
  push_cast
  refine add_sq_div_add_le (Nat.cast_nonneg _) (Nat.cast_nonneg _) (fun hs ↦ ?_) (fun ht ↦ ?_)
  · have hse : s = ∅ := card_eq_zero.1 (Nat.cast_eq_zero.1 hs)
    simp [hse]
  · have hte : t = ∅ := card_eq_zero.1 (Nat.cast_eq_zero.1 ht)
    simp [hte]

private theorem fiberEnergy_sub_union_le [DecidableEq α] (f : α → κ) {s t : Finset α}
    (h : Disjoint s t) :
    fiberEnergy f s - fiberEnergy f (s ∪ t) ≤ #t := by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · rw [fiberEnergy_empty, empty_union]
    linarith [fiberEnergy_nonneg f t, Nat.cast_nonneg (α := ℝ) #t]
  have hs0 : (0 : ℝ) < #s := Nat.cast_pos.2 hs.card_pos
  have hst0 : (0 : ℝ) < (#s : ℝ) + #t := add_pos_of_pos_of_nonneg hs0 (Nat.cast_nonneg _)
  have hle : fiberEnergy f s - fiberEnergy f (s ∪ t) ≤
      fiberEnergy f s * ((#t : ℝ) / ((#s : ℝ) + #t)) := by
    rw [fiberEnergy, fiberEnergy, ← sum_sub_distrib, sum_mul]
    refine sum_le_sum fun c _ ↦ ?_
    have hcnt : (#{x ∈ s | f x = c} : ℝ) ≤ #{x ∈ s ∪ t | f x = c} :=
      Nat.cast_le.2 (card_le_card (filter_subset_filter _ subset_union_left))
    have hcard : (#(s ∪ t) : ℝ) = (#s : ℝ) + #t := by exact_mod_cast card_union_of_disjoint h
    rw [hcard]
    have hsq : (#{x ∈ s | f x = c} : ℝ) ^ 2 / ((#s : ℝ) + #t) ≤
        (#{x ∈ s ∪ t | f x = c} : ℝ) ^ 2 / ((#s : ℝ) + #t) := by gcongr
    have hdiff : (#{x ∈ s | f x = c} : ℝ) ^ 2 / #s -
        (#{x ∈ s | f x = c} : ℝ) ^ 2 / ((#s : ℝ) + #t) =
        ((#{x ∈ s | f x = c} : ℝ) ^ 2 / #s) * ((#t : ℝ) / ((#s : ℝ) + #t)) := by
      field_simp
      ring
    linarith
  calc fiberEnergy f s - fiberEnergy f (s ∪ t)
      ≤ fiberEnergy f s * ((#t : ℝ) / ((#s : ℝ) + #t)) := hle
    _ ≤ (#s : ℝ) * ((#t : ℝ) / ((#s : ℝ) + #t)) :=
        mul_le_mul_of_nonneg_right (fiberEnergy_le_card f s) (by positivity)
    _ = (#t : ℝ) * ((#s : ℝ) / ((#s : ℝ) + #t)) := by ring
    _ ≤ (#t : ℝ) * 1 := mul_le_mul_of_nonneg_left
        ((div_le_one hst0).2 (le_add_of_nonneg_right (Nat.cast_nonneg _))) (Nat.cast_nonneg _)
    _ = #t := mul_one _

private theorem abs_fiberEnergy_sub_le [DecidableEq α] (f : α → κ) (A B : Finset α) :
    |fiberEnergy f A - fiberEnergy f B| ≤ (#(A \ B) : ℝ) + #(B \ A) := by
  have hA : (A ∩ B) ∪ (A \ B) = A := by rw [union_comm, sdiff_union_inter]
  have hB : (A ∩ B) ∪ (B \ A) = B := by rw [union_comm, inter_comm, sdiff_union_inter]
  have hdA : Disjoint (A ∩ B) (A \ B) := disjoint_sdiff_self_right.mono_left inter_subset_right
  have hdB : Disjoint (A ∩ B) (B \ A) := disjoint_sdiff_self_right.mono_left inter_subset_left
  have hA_up : fiberEnergy f A - fiberEnergy f (A ∩ B) ≤ #(A \ B) := by
    have h1 := fiberEnergy_union_le_add f hdA
    rw [hA] at h1
    linarith [fiberEnergy_le_card f (A \ B)]
  have hB_up : fiberEnergy f B - fiberEnergy f (A ∩ B) ≤ #(B \ A) := by
    have h1 := fiberEnergy_union_le_add f hdB
    rw [hB] at h1
    linarith [fiberEnergy_le_card f (B \ A)]
  have hA_dn : fiberEnergy f (A ∩ B) - fiberEnergy f A ≤ #(A \ B) := by
    have h1 := fiberEnergy_sub_union_le f hdA
    rwa [hA] at h1
  have hB_dn : fiberEnergy f (A ∩ B) - fiberEnergy f B ≤ #(B \ A) := by
    have h1 := fiberEnergy_sub_union_le f hdB
    rwa [hB] at h1
  rw [abs_sub_le_iff]
  constructor <;> linarith

private theorem sum_fiberEnergy_image_ofTriple {V κ₂ : Type*} [Fintype V] [DecidableEq V]
    [DecidableEq κ₂] (H : Colored3Graph κ V) (S : PairSkeleton3 κ₂ V) :
    ∑ P ∈ univ.image (Polyad3.ofTriple S),
        fiberEnergy (fun x : {x : Fin 3 → V // Function.Injective x} ↦
          H.color (Set.powersetCard.ofFinEmb 3 V ⟨x.1, x.2⟩)) P.support =
      ∑ x : {x : Fin 3 → V // Function.Injective x}, ∑ c,
        (H.relativeDensity c (Polyad3.ofTriple S x) : ℝ) ^ 2 := by
  rw [← sum_fiberwise_of_maps_to (t := univ.image (Polyad3.ofTriple S))
    (g := Polyad3.ofTriple S) (fun x _ ↦ mem_image_of_mem _ (mem_univ x))]
  refine sum_congr rfl fun P _ ↦ ?_
  have hfib : {x ∈ (univ : Finset {x : Fin 3 → V // Function.Injective x}) |
      Polyad3.ofTriple S x = P} = P.support := by
    ext x
    simp only [mem_filter, mem_univ, true_and, Polyad3.mem_support_iff_eq_ofTriple, eq_comm]
  rw [hfib, sum_congr rfl fun x hx ↦ by rw [← Polyad3.mem_support_iff_eq_ofTriple.1 hx],
    sum_const, nsmul_eq_mul, mul_sum, fiberEnergy]
  obtain hP | hP := P.support.eq_empty_or_nonempty
  · simp [hP]
  have hP0 : (#P.support : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hP.card_pos.ne'
  refine sum_congr rfl fun c _ ↦ ?_
  rw [relativeDensity_def, relDensityOn_def]
  push_cast
  field_simp

private theorem sum_card_inter_support_le {V κ₂ : Type*} [Fintype V] [DecidableEq V]
    {S : PairSkeleton3 κ₂ V} (M : Finset {x : Fin 3 → V // Function.Injective x})
    (F : Finset (Polyad3 S)) :
    ∑ R ∈ F, (#(M ∩ R.support) : ℝ) ≤ #M := by
  norm_cast
  rw [← card_biUnion fun R _ R' _ hne ↦
    (Polyad3.pairwise_disjoint_support hne).mono inter_subset_right inter_subset_right]
  exact card_le_card (biUnion_subset.2 fun _ _ ↦ inter_subset_left)

private theorem abs_fiberEnergy_support_sub_le {V κ₂ κ₂' : Type*} [Fintype V] [DecidableEq V]
    [DecidableEq κ₂'] (col : {x : Fin 3 → V // Function.Injective x} → κ)
    {S : PairSkeleton3 κ₂ V} {T : PairSkeleton3 κ₂' V}
    {f : Polyad3 S → Polyad3 T} (hf : Function.Injective f) (P : Polyad3 S) :
    let M : Finset {x : Fin 3 → V // Function.Injective x} :=
      {x | Polyad3.ofTriple T x ≠ f (Polyad3.ofTriple S x)}
    |fiberEnergy col (f P).support - fiberEnergy col P.support| ≤
      (#(M ∩ (f P).support) : ℝ) + #(M ∩ P.support) := by
  intro M
  have h1 : (f P).support \ P.support ⊆ M ∩ (f P).support := fun x hx ↦ by
    obtain ⟨hxQ, hxP⟩ := mem_sdiff.1 hx
    refine mem_inter.2 ⟨mem_filter.2 ⟨mem_univ x, fun h ↦ hxP ?_⟩, hxQ⟩
    exact Polyad3.mem_support_iff_eq_ofTriple.2
      (hf ((Polyad3.mem_support_iff_eq_ofTriple.1 hxQ).trans h))
  have h2 : P.support \ (f P).support ⊆ M ∩ P.support := fun x hx ↦ by
    obtain ⟨hxP, hxQ⟩ := mem_sdiff.1 hx
    refine mem_inter.2 ⟨mem_filter.2 ⟨mem_univ x, fun h ↦ hxQ ?_⟩, hxP⟩
    rw [Polyad3.mem_support_iff_eq_ofTriple, Polyad3.mem_support_iff_eq_ofTriple.1 hxP]
    exact h.symm
  exact (abs_fiberEnergy_sub_le col (f P).support P.support).trans
    (add_le_add (Nat.cast_le.2 (card_le_card h1)) (Nat.cast_le.2 (card_le_card h2)))

end FiberEnergy

section Stability

variable {κ κ₂ κ₂' V : Type*} [Fintype V] [DecidableEq V] [DecidableEq κ] [Fintype κ]
  (H : Colored3Graph κ V)

/-- **Polyad energy stability under an injective polyad map.** For lower skeletons `S` and `T` and
an injective map `f : Polyad3 S → Polyad3 T`, call an injective triple *moved* when its polyad over
`T` differs from `f` of its polyad over `S`. The polyad energies of `H` over `S` and `T` differ by
at most twice the proportion of moved triples among all `|V|.descFactorial 3` injective triples. -/
theorem abs_polyadEnergy_sub_polyadEnergy_le_of_injective [DecidableEq κ₂']
    {S : PairSkeleton3 κ₂ V} {T : PairSkeleton3 κ₂' V}
    {f : Polyad3 S → Polyad3 T} (hf : Function.Injective f) :
    |H.polyadEnergy S - H.polyadEnergy T| ≤
      2 * #{x | Polyad3.ofTriple T x ≠ f (Polyad3.ofTriple S x)} /
        (Fintype.card V).descFactorial 3 := by
  set M : Finset {x : Fin 3 → V // Function.Injective x} :=
    {x | Polyad3.ofTriple T x ≠ f (Polyad3.ofTriple S x)}
  set col : {x : Fin 3 → V // Function.Injective x} → κ :=
    fun x ↦ H.color (Set.powersetCard.ofFinEmb 3 V ⟨x.1, x.2⟩)
  have : DecidableEq κ₂ := Classical.decEq κ₂
  set imgS : Finset (Polyad3 S) := univ.image (Polyad3.ofTriple S)
  set imgT : Finset (Polyad3 T) := univ.image (Polyad3.ofTriple T)
  set img : Finset (Polyad3 T) := imgT ∪ imgS.image f
  have himgT : ∑ Q ∈ img, fiberEnergy col Q.support = ∑ Q ∈ imgT, fiberEnergy col Q.support := by
    refine (sum_subset subset_union_left fun Q _ hQ ↦ ?_).symm
    have hempty : Q.support = ∅ := eq_empty_iff_forall_notMem.2 fun x hx ↦
      hQ (mem_image.2 ⟨x, mem_univ x, (Polyad3.mem_support_iff_eq_ofTriple.1 hx).symm⟩)
    rw [hempty, fiberEnergy_empty]
  have hout (Q : Polyad3 T) (hQ : Q ∈ img \ imgS.image f) :
      fiberEnergy col Q.support ≤ #(M ∩ Q.support) := by
    have hsub : Q.support ⊆ M := fun x hx ↦ mem_filter.2 ⟨mem_univ x, fun h ↦
      (mem_sdiff.1 hQ).2 (mem_image.2 ⟨Polyad3.ofTriple S x, mem_image_of_mem _ (mem_univ x),
        h.symm.trans (Polyad3.mem_support_iff_eq_ofTriple.1 hx).symm⟩)⟩
    rw [inter_eq_right.2 hsub]
    exact fiberEnergy_le_card col Q.support
  have hsplit (φ : Polyad3 T → ℝ) :
      ∑ Q ∈ img, φ Q = ∑ Q ∈ img \ imgS.image f, φ Q + ∑ P ∈ imgS, φ (f P) := by
    rw [← sum_sdiff subset_union_right, sum_image hf.injOn]
  have hnum : |∑ Q ∈ img, fiberEnergy col Q.support - ∑ P ∈ imgS, fiberEnergy col P.support| ≤
      2 * (#M : ℝ) := by
    rw [hsplit (fun Q ↦ fiberEnergy col Q.support), add_sub_assoc, ← sum_sub_distrib]
    calc _ ≤ ∑ Q ∈ img \ imgS.image f, fiberEnergy col Q.support +
            ∑ P ∈ imgS, |fiberEnergy col (f P).support - fiberEnergy col P.support| := by
          refine (abs_add_le _ _).trans (add_le_add ?_ (abs_sum_le_sum_abs _ _))
          rw [abs_of_nonneg (sum_nonneg fun Q _ ↦ fiberEnergy_nonneg col Q.support)]
      _ ≤ ∑ Q ∈ img \ imgS.image f, (#(M ∩ Q.support) : ℝ) +
            ∑ P ∈ imgS, ((#(M ∩ (f P).support) : ℝ) + #(M ∩ P.support)) :=
          add_le_add (sum_le_sum hout)
            (sum_le_sum fun P _ ↦ abs_fiberEnergy_support_sub_le col hf P)
      _ = ∑ Q ∈ img, (#(M ∩ Q.support) : ℝ) + ∑ P ∈ imgS, (#(M ∩ P.support) : ℝ) := by
          rw [sum_add_distrib, ← add_assoc, ← hsplit fun Q ↦ (#(M ∩ Q.support) : ℝ)]
      _ ≤ (#M : ℝ) + #M := add_le_add (sum_card_inter_support_le M img)
          (sum_card_inter_support_le M imgS)
      _ = 2 * (#M : ℝ) := by ring
  rw [abs_sub_comm, polyadEnergy_def, polyadEnergy_def, ← sub_div, abs_div, Nat.abs_cast,
    ← sum_fiberEnergy_image_ofTriple H T, ← sum_fiberEnergy_image_ofTriple H S, ← himgT]
  exact div_le_div_of_nonneg_right hnum (Nat.cast_nonneg _)

/-- **Polyad energy stability under pair recoloring on fixed vertex cells.** If `S` and `T` share
their vertex cells and the pair colors of `T` agree with an injective map `g` of those of `S`
outside a set `E` of ordered pairs, then the polyad energies of `H` over `S` and `T` differ by at
most `6 |E| |V| / |V|.descFactorial 3`. -/
theorem abs_polyadEnergy_sub_polyadEnergy_le_of_pairRecoloring [DecidableEq κ₂']
    {S : PairSkeleton3 κ₂ V} {T : PairSkeleton3 κ₂' V}
    (hV : S.vertexPart = T.vertexPart) {g : κ₂ → κ₂'} (hg : Function.Injective g) :
    |H.polyadEnergy S - H.polyadEnergy T| ≤
      6 * #{p | T.pairColors.color p ≠ g (S.pairColors.color p)} * Fintype.card V /
        (Fintype.card V).descFactorial 3 := by
  refine (H.abs_polyadEnergy_sub_polyadEnergy_le_of_injective
    (Polyad3.coarsen_injective hV hg)).trans ?_
  have hmove : (#{x | Polyad3.ofTriple T x ≠ (Polyad3.ofTriple S x).coarsen hV.le g} : ℝ) ≤
      3 * #{p | T.pairColors.color p ≠ g (S.pairColors.color p)} * Fintype.card V := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using
      (Nat.cast_le (α := ℝ)).2 (Polyad3.card_filter_ofTriple_ne_coarsen_ofTriple_le hV.le g)
  refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)
  linarith

/-- **One-sided polyad energy stability under vertex refinement and pair recoloring.** If the
vertex cells of `T` refine those of `S` and the pair colors of `T` agree with an injective map `g`
of those of `S` outside a set `E` of ordered pairs, then passing from `S` to `T` lowers the polyad
energy of `H` by at most `6 |E| |V| / |V|.descFactorial 3`. -/
theorem polyadEnergy_sub_polyadEnergy_le_of_le_of_pairRecoloring [DecidableEq κ₂']
    {S : PairSkeleton3 κ₂ V} {T : PairSkeleton3 κ₂' V}
    (hV : T.vertexPart ≤ S.vertexPart) {g : κ₂ → κ₂'} (hg : Function.Injective g) :
    H.polyadEnergy S - H.polyadEnergy T ≤
      6 * #{p | T.pairColors.color p ≠ g (S.pairColors.color p)} * Fintype.card V /
        (Fintype.card V).descFactorial 3 := by
  let S' : PairSkeleton3 κ₂ V := ⟨T.vertexPart, S.pairColors⟩
  have hmono : H.polyadEnergy S ≤ H.polyadEnergy S' :=
    H.polyadEnergy_mono_of_refines fun x y hxy ↦
      Polyad3.ofTriple_eq_ofTriple_of_le (S := S) (T := S') hV id (fun _ ↦ rfl) hxy
  have hstab := H.abs_polyadEnergy_sub_polyadEnergy_le_of_pairRecoloring
    (S := S') (T := T) rfl hg
  linarith [(abs_le.1 hstab).2]

end Stability

end TauCeti.Colored3Graph
