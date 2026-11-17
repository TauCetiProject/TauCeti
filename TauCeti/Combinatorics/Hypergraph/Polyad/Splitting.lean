/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Hypergraph.Polyad.TopRegular
import TauCeti.Algebra.BigOperators.Finset.BoxCauchySchwarz
import TauCeti.Data.Fintype.BigOperators
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Quasirandom splitting of triple colors

A labelling `f : Set.powersetCard V 3 → ι` of the triples splits every color `c` of a coloring
`H` into the colors `(c, i)`, for `i : ι`; this is `Colored3Graph.split`, defined in
`TauCeti.Combinatorics.Hypergraph.Colored.Basic`. This file shows that some splitting is
quasirandom on every subpolyad of every polyad over a lower skeleton with large vertex cells: on a
subpolyad `Q` of a polyad `P`, each color `(c, i)` occupies a `1 / |ι|` share of the triples of
color `c`, up to an error `δ |P.c₀| |P.c₁| |P.c₂|`
(`Colored3Graph.exists_split_abs_card_sub_le`). The cells of a polyad may coincide.

The proof is an averaging argument over all labellings of the triples. The deviation of the
indicator of `(c, i)` from a `1 / |ι|` share of the indicator of `c` has mean zero at every
triple, independently over the triples. Its octahedral sum on three cells, a weighted count of the
octahedra `{x, x'} × {y, y'} × {z, z'}`, therefore averages to the contribution of the degenerate
octahedra, those in which one of `x'`, `y'` and `z'` lies in `{x, y, z}`; there are at most
`9 (|A| |B| |C|) ^ 2 / N` of them on cells of size at least `N`. Some labelling achieves at most
the average of the normalized octahedral sums over all cell triples and colors, and three
applications of the Cauchy–Schwarz inequality turn a small octahedral sum into a small
discrepancy on every set of triples cut out by three pair relations
(`Finset.sum_sum_sum_mul_pow_eight_le`), in particular on every subpolyad. No probability theory
is used.

Splitting preserves top regularity: if `H` is `(δ, 1)`-top-regular over `P` and the splitting is
quasirandom on the subpolyads of `P` at scale `δ ^ 2 / 2` relative to the support of `P`, then
`H.split f` is `(2 δ, 1)`-top-regular over `P` (`Colored3Graph.IsTopRegularOverPolyad.split`).
Since the discrepancy is measured against the cell volume, this applies to polyads whose support
fills a fixed proportion `γ` of their cell volume
(`Colored3Graph.exists_split_isTopRegularOverPolyad`); rank-one regularity then amplifies to every
rank (`Colored3Graph.IsTopRegularOverPolyad.of_rank_one`).

A regular approximation of a coloring of the triples has to move relative densities of top
colors over fine polyads to prescribed values without destroying regularity. Quasirandom
splittings supply the pieces for such edits: each split class is top-regular over the polyad
with approximately a `1 / |ι|` share of the density of its parent color, so recoloring a union of
classes moves densities in steps of approximately `1 / |ι|` times the parent density, and the
recolored coloring stays regular with the errors of the moved classes adding up.

## Main results

* `TauCeti.Colored3Graph.exists_split_abs_card_sub_le`: a splitting that is quasirandom on every
  subpolyad of every polyad over a skeleton with large cells.
* `TauCeti.Colored3Graph.IsTopRegularOverPolyad.split`: quasirandom splitting preserves rank-one
  top regularity.
* `TauCeti.Colored3Graph.exists_split_isTopRegularOverPolyad`: some splitting preserves the
  rank-one top regularity of every polyad of proportional support, with split densities close to
  a `1 / |ι|` share of the parent densities.

## References

* W. T. Gowers, *Quasirandomness, counting and regularity for 3-uniform hypergraphs*,
  Combin. Probab. Comput. 15 (2006): the octahedral norm controls discrepancy on triangles of
  pair graphs.
* V. Rödl and M. Schacht, *Regular partitions of hypergraphs: regularity lemmas*,
  Combin. Probab. Comput. 16 (2007): regular approximation by perfectly regular partitions.
-/

public section

open Finset

namespace TauCeti

namespace Colored3Graph

variable {κ ι V : Type*}

section Indicator

variable [DecidableEq V]

/-- The degenerate octahedra with a fixed vertex triple `T` of at most three vertices. -/
private theorem sum_indicator_le {T : Finset V} (hT : #T ≤ 3) (A B C : Finset V) :
    ∑ y' ∈ B, ∑ z' ∈ C, ∑ x' ∈ A, ((if x' ∈ T then (1 : ℝ) else 0) +
      (if y' ∈ T then 1 else 0) + (if z' ∈ T then 1 else 0)) ≤
    3 * (#B * #C + #A * #C + #A * #B) := by
  have hc (s : Finset V) : ∑ x ∈ s, (if x ∈ T then (1 : ℝ) else 0) ≤ 3 := by
    rw [sum_boole]
    exact_mod_cast (card_le_card (fun x hx ↦ (mem_filter.1 hx).2)).trans hT
  have e : ∑ y' ∈ B, ∑ z' ∈ C, ∑ x' ∈ A, ((if x' ∈ T then (1 : ℝ) else 0) +
      (if y' ∈ T then 1 else 0) + (if z' ∈ T then 1 else 0)) =
      #B * #C * ∑ x' ∈ A, (if x' ∈ T then (1 : ℝ) else 0) +
        #A * #C * ∑ y' ∈ B, (if y' ∈ T then (1 : ℝ) else 0) +
        #A * #B * ∑ z' ∈ C, (if z' ∈ T then (1 : ℝ) else 0) := by
    simp only [sum_add_distrib, sum_const, nsmul_eq_mul, ← mul_sum]
    ring
  rw [e]
  calc _ ≤ #B * #C * 3 + #A * #C * 3 + #A * #B * (3 : ℝ) := by gcongr <;> exact hc _
    _ = _ := by ring

end Indicator

section Deviation

variable [DecidableEq κ] [Fintype ι] [DecidableEq ι] (H : Colored3Graph κ V) (c : κ) (i : ι)

/-- The deviation, at a triple `e` with label `v`, of the indicator of the split color `(c, i)`
from a `1 / |ι|` share of the indicator of `c`. -/
private noncomputable def splitDev (e : Set.powersetCard V 3) (v : ι) : ℝ :=
  if H.color e = c then (if v = i then 1 else 0) - (Fintype.card ι : ℝ)⁻¹ else 0

section

variable [Nonempty ι]

/-- The deviation has mean zero over the labels. -/
private theorem sum_splitDev (e : Set.powersetCard V 3) : ∑ v, splitDev H c i e v = 0 := by
  unfold splitDev
  split_ifs
  · simp [sum_sub_distrib]
  · simp

private theorem abs_splitDev_le_one (e : Set.powersetCard V 3) (v : ι) :
    |splitDev H c i e v| ≤ 1 := by
  have hq : (1 : ℝ) ≤ Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have h₀ : 0 < (Fintype.card ι : ℝ)⁻¹ := by positivity
  have h₁ : (Fintype.card ι : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hq
  unfold splitDev
  split_ifs <;> rw [abs_le] <;> constructor <;> linarith

end

variable [DecidableEq V]

/-- The deviation of the split color `(c, i)` under the labelling `f` at the vertex set
`{x, y, z}`, and zero unless the three vertices are distinct. -/
private noncomputable def tripleDev (f : Set.powersetCard V 3 → ι) (x y z : V) : ℝ :=
  if h : #({x, y, z} : Finset V) = 3 then
    splitDev H c i (Set.powersetCard.ofCard h) (f (Set.powersetCard.ofCard h))
  else 0

/-- The deviation at `{x, y, z}` does not see the label of any other triple. -/
private theorem tripleDev_update_of_ne (f : Set.powersetCard V 3 → ι) (e : Set.powersetCard V 3)
    (v : ι) {x y z : V} (h : ({x, y, z} : Finset V) ≠ e.1) :
    tripleDev H c i (Function.update f e v) x y z = tripleDev H c i f x y z := by
  by_cases h₃ : #({x, y, z} : Finset V) = 3
  · simp only [tripleDev, h₃, ↓reduceDIte]
    rw [Function.update_of_ne]
    exact fun he ↦ h (by rw [← he, Set.powersetCard.val_ofCard])
  · simp only [tripleDev, h₃, ↓reduceDIte]

/-- The octahedral sum of the deviations of the split color `(c, i)` on three cells. -/
private noncomputable def splitOct (f : Set.powersetCard V 3 → ι) (A B C : Finset V) : ℝ :=
  ∑ y ∈ B, ∑ y' ∈ B, ∑ z ∈ C, ∑ z' ∈ C,
    (∑ x ∈ A, tripleDev H c i f x y z * tripleDev H c i f x y z' * tripleDev H c i f x y' z *
      tripleDev H c i f x y' z') ^ 2

private theorem splitOct_nonneg (f : Set.powersetCard V 3 → ι) (A B C : Finset V) :
    0 ≤ splitOct H c i f A B C :=
  sum_nonneg fun _ _ ↦ sum_nonneg fun _ _ ↦ sum_nonneg fun _ _ ↦ sum_nonneg fun _ _ ↦
    sq_nonneg _

variable [Nonempty ι]

private theorem abs_tripleDev_le_one (f : Set.powersetCard V 3 → ι) (x y z : V) :
    |tripleDev H c i f x y z| ≤ 1 := by
  unfold tripleDev
  split_ifs
  · exact abs_splitDev_le_one ..
  · simp

variable [Fintype V]

/-- One octahedron `(x, x') × (y, y') × (z, z')` contributes nothing on average unless one of
`x'`, `y'` and `z'` lies in `{x, y, z}`. -/
private theorem sum_octahedron_eq_zero {x y z x' y' z' : V}
    (hx : x' ∉ ({x, y, z} : Finset V)) (hy : y' ∉ ({x, y, z} : Finset V))
    (hz : z' ∉ ({x, y, z} : Finset V)) :
    ∑ f : Set.powersetCard V 3 → ι,
      tripleDev H c i f x y z * tripleDev H c i f x y z' * tripleDev H c i f x y' z *
        tripleDev H c i f x y' z' *
      (tripleDev H c i f x' y z * tripleDev H c i f x' y z' * tripleDev H c i f x' y' z *
        tripleDev H c i f x' y' z') = 0 := by
  by_cases h₃ : #({x, y, z} : Finset V) = 3
  · set e : Set.powersetCard V 3 := Set.powersetCard.ofCard h₃
    have he (f : Set.powersetCard V 3 → ι) : tripleDev H c i f x y z = splitDev H c i e (f e) :=
      by simp only [tripleDev, h₃, ↓reduceDIte, e]
    have hne {a b d : V} (hm : ∃ w ∈ ({a, b, d} : Finset V), w ∉ ({x, y, z} : Finset V)) :
        ({a, b, d} : Finset V) ≠ ({x, y, z} : Finset V) := by
      obtain ⟨w, hw, hw'⟩ := hm
      exact fun h ↦ hw' (h ▸ hw)
    have key := Fintype.sum_apply_mul_eq_zero e (sum_splitDev H c i e)
      (G := fun f ↦ tripleDev H c i f x y z' * tripleDev H c i f x y' z *
        tripleDev H c i f x y' z' *
        (tripleDev H c i f x' y z * tripleDev H c i f x' y z' * tripleDev H c i f x' y' z *
          tripleDev H c i f x' y' z'))
      fun f v ↦ by
        rw [tripleDev_update_of_ne H c i f e v (hne ⟨z', by simp, hz⟩),
          tripleDev_update_of_ne H c i f e v (hne ⟨y', by simp, hy⟩),
          tripleDev_update_of_ne H c i f e v (hne ⟨y', by simp, hy⟩),
          tripleDev_update_of_ne H c i f e v (hne ⟨x', by simp, hx⟩),
          tripleDev_update_of_ne H c i f e v (hne ⟨x', by simp, hx⟩),
          tripleDev_update_of_ne H c i f e v (hne ⟨x', by simp, hx⟩),
          tripleDev_update_of_ne H c i f e v (hne ⟨x', by simp, hx⟩)]
    rw [← key]
    refine sum_congr rfl fun f _ ↦ ?_
    rw [he]
    ring
  · refine sum_eq_zero fun f _ ↦ ?_
    simp [tripleDev, h₃]

/-- On average, an octahedron contributes at most one, and nothing unless it is degenerate. -/
private theorem sum_octahedron_le (x y z x' y' z' : V) :
    ∑ f : Set.powersetCard V 3 → ι,
      tripleDev H c i f x y z * tripleDev H c i f x y z' * tripleDev H c i f x y' z *
        tripleDev H c i f x y' z' *
      (tripleDev H c i f x' y z * tripleDev H c i f x' y z' * tripleDev H c i f x' y' z *
        tripleDev H c i f x' y' z') ≤
    Fintype.card (Set.powersetCard V 3 → ι) *
      ((if x' ∈ ({x, y, z} : Finset V) then 1 else 0) +
        (if y' ∈ ({x, y, z} : Finset V) then 1 else 0) +
        (if z' ∈ ({x, y, z} : Finset V) then 1 else 0)) := by
  by_cases hd : x' ∈ ({x, y, z} : Finset V) ∨ y' ∈ ({x, y, z} : Finset V) ∨
      z' ∈ ({x, y, z} : Finset V)
  · have hone : (1 : ℝ) ≤ (if x' ∈ ({x, y, z} : Finset V) then 1 else 0) +
        (if y' ∈ ({x, y, z} : Finset V) then 1 else 0) +
        (if z' ∈ ({x, y, z} : Finset V) then 1 else 0) := by
      split_ifs <;> norm_num; tauto
    have h₁ := abs_tripleDev_le_one H c i
    calc _ ≤ ∑ _f : Set.powersetCard V 3 → ι, (1 : ℝ) := by
          refine sum_le_sum fun f _ ↦ (le_abs_self _).trans ?_
          simp only [abs_mul]
          calc _ ≤ (1 : ℝ) * 1 * 1 * 1 * (1 * 1 * 1 * 1) := by
                gcongr <;> exact h₁ ..
            _ = 1 := by norm_num
      _ = Fintype.card (Set.powersetCard V 3 → ι) * 1 := by simp
      _ ≤ _ := by gcongr
  · push Not at hd
    rw [sum_octahedron_eq_zero H c i hd.1 hd.2.1 hd.2.2]
    positivity

/-- Averaged over all labellings, the octahedral sum on three cells is at most the number of
degenerate octahedra. -/
private theorem sum_splitOct_le (A B C : Finset V) :
    ∑ f : Set.powersetCard V 3 → ι, splitOct H c i f A B C ≤
      Fintype.card (Set.powersetCard V 3 → ι) *
        (#B * #C * #A * (3 * (#B * #C + #A * #C + #A * #B))) := by
  calc _ = ∑ y ∈ B, ∑ y' ∈ B, ∑ z ∈ C, ∑ z' ∈ C, ∑ x ∈ A, ∑ x' ∈ A,
        ∑ f : Set.powersetCard V 3 → ι,
          tripleDev H c i f x y z * tripleDev H c i f x y z' * tripleDev H c i f x y' z *
            tripleDev H c i f x y' z' *
          (tripleDev H c i f x' y z * tripleDev H c i f x' y z' * tripleDev H c i f x' y' z *
            tripleDev H c i f x' y' z') := by
        simp only [splitOct, sq, sum_mul_sum]
        rw [sum_comm]; refine sum_congr rfl fun y _ ↦ ?_
        rw [sum_comm]; refine sum_congr rfl fun y' _ ↦ ?_
        rw [sum_comm]; refine sum_congr rfl fun z _ ↦ ?_
        rw [sum_comm]; refine sum_congr rfl fun z' _ ↦ ?_
        rw [sum_comm]; refine sum_congr rfl fun x _ ↦ ?_
        rw [sum_comm]
    _ ≤ ∑ y ∈ B, ∑ y' ∈ B, ∑ z ∈ C, ∑ z' ∈ C, ∑ x ∈ A, ∑ x' ∈ A,
        Fintype.card (Set.powersetCard V 3 → ι) *
          ((if x' ∈ ({x, y, z} : Finset V) then (1 : ℝ) else 0) +
            (if y' ∈ ({x, y, z} : Finset V) then 1 else 0) +
            (if z' ∈ ({x, y, z} : Finset V) then 1 else 0)) := by
        gcongr
        exact sum_octahedron_le H c i ..
    _ = Fintype.card (Set.powersetCard V 3 → ι) * ∑ y ∈ B, ∑ z ∈ C, ∑ x ∈ A,
        ∑ y' ∈ B, ∑ z' ∈ C, ∑ x' ∈ A,
          ((if x' ∈ ({x, y, z} : Finset V) then (1 : ℝ) else 0) +
            (if y' ∈ ({x, y, z} : Finset V) then 1 else 0) +
            (if z' ∈ ({x, y, z} : Finset V) then 1 else 0)) := by
        simp only [mul_sum]
        refine sum_congr rfl fun y _ ↦ ?_
        rw [sum_comm]
        refine sum_congr rfl fun z _ ↦ ?_
        conv_lhs => enter [2, y']; rw [sum_comm]
        rw [sum_comm]
    _ ≤ Fintype.card (Set.powersetCard V 3 → ι) * ∑ _y ∈ B, ∑ _z ∈ C, ∑ _x ∈ A,
        3 * (#B * #C + #A * #C + #A * #B : ℝ) := by
        gcongr
        exact sum_indicator_le card_le_three A B C
    _ = _ := by simp only [sum_const, nsmul_eq_mul]; ring

/-- Normalized by the squared cell volume, the octahedral sum on three cells of size at least
`N` averages to at most `9 / N`. -/
private theorem sum_splitOct_div_le (A B C : Finset V) {N : ℕ} (hN₀ : 0 < N) (hNA : N ≤ #A)
    (hNB : N ≤ #B) (hNC : N ≤ #C) :
    ∑ f : Set.powersetCard V 3 → ι, splitOct H c i f A B C / (#A * #B * #C) ^ 2 ≤
      Fintype.card (Set.powersetCard V 3 → ι) * 9 / N := by
  have hN₀' : (0 : ℝ) < N := by exact_mod_cast hN₀
  have hA : (N : ℝ) ≤ #A := by exact_mod_cast hNA
  have hB : (N : ℝ) ≤ #B := by exact_mod_cast hNB
  have hC : (N : ℝ) ≤ #C := by exact_mod_cast hNC
  have hA₀ : (0 : ℝ) < #A := hN₀'.trans_le hA
  have hB₀ : (0 : ℝ) < #B := hN₀'.trans_le hB
  have hC₀ : (0 : ℝ) < #C := hN₀'.trans_le hC
  have key : (#B * #C * #A * (3 * (#B * #C + #A * #C + #A * #B)) * N : ℝ) ≤
      9 * (#A * #B * #C : ℝ) ^ 2 := by
    have h₁ : (#B * #C : ℝ) * N ≤ #A * #B * #C := by
      calc (#B * #C : ℝ) * N ≤ #B * #C * #A := by gcongr
        _ = _ := by ring
    have h₂ : (#A * #C : ℝ) * N ≤ #A * #B * #C := by
      calc (#A * #C : ℝ) * N ≤ #A * #C * #B := by gcongr
        _ = _ := by ring
    have h₃ : (#A * #B : ℝ) * N ≤ #A * #B * #C := by gcongr
    calc _ = 3 * (#B * #C * #A : ℝ) * ((#B * #C) * N + (#A * #C) * N + (#A * #B) * N) := by
          ring
      _ ≤ 3 * (#B * #C * #A : ℝ) * (#A * #B * #C + #A * #B * #C + #A * #B * #C) := by gcongr
      _ = _ := by ring
  rw [← sum_div, div_le_div_iff₀ (by positivity) hN₀']
  calc (∑ f, splitOct H c i f A B C) * N
      ≤ Fintype.card (Set.powersetCard V 3 → ι) *
          (#B * #C * #A * (3 * (#B * #C + #A * #C + #A * #B))) * N := by
        gcongr
        exact sum_splitOct_le H c i A B C
    _ ≤ Fintype.card (Set.powersetCard V 3 → ι) * (9 * (#A * #B * #C) ^ 2) := by
        rw [mul_assoc]
        gcongr
    _ = _ := by ring

end Deviation

section Coordinates

private theorem exists_mem_of_mem_map {q : Finset {p : V × V // p.1 ≠ p.2}} {a b : V}
    (h : (a, b) ∈ q.map (Function.Embedding.subtype _)) :
    ∃ hab : a ≠ b, (⟨(a, b), hab⟩ : {p : V × V // p.1 ≠ p.2}) ∈ q := by
  obtain ⟨⟨p, hp'⟩, hp, hpe⟩ := mem_map.1 h
  rw [Function.Embedding.subtype_apply] at hpe
  subst hpe
  exact ⟨hp', hp⟩

variable [DecidableEq V]

/-- The underlying vertex set of an injective triple. -/
private theorem val_ofFinEmb_eq (x : {x : Fin 3 → V // Function.Injective x}) :
    (Set.powersetCard.ofFinEmb 3 V ⟨x.1, x.2⟩ : Finset V) = {x.1 0, x.1 1, x.1 2} := by
  ext v
  simp [Fin.exists_fin_succ, eq_comm]

/-- The indicator of the ordered vertex pairs of a set of distinct pairs. -/
private noncomputable def pairInd (q : Finset {p : V × V // p.1 ≠ p.2}) (a b : V) : ℝ :=
  if (a, b) ∈ q.map (Function.Embedding.subtype _) then 1 else 0

private theorem abs_pairInd_le_one (q : Finset {p : V × V // p.1 ≠ p.2}) (a b : V) :
    |pairInd q a b| ≤ 1 := by
  unfold pairInd
  split_ifs <;> simp

variable [Fintype V]

/-- A sum over the support of a subpolyad of a function of the three coordinates is a box sum
over the cells of the parent polyad, weighted by the indicators of the three selected pair
sets. -/
private theorem sum_support_eq_sum_cells {κ₂ : Type*} {S : PairSkeleton3 κ₂ V} {P : Polyad3 S}
    (Q : Subpolyad3 P) (φ : V → V → V → ℝ) :
    ∑ x ∈ Q.support, φ (x.1 0) (x.1 1) (x.1 2) =
      ∑ a ∈ P.c₀, ∑ b ∈ P.c₁, ∑ d ∈ P.c₂,
        φ a b d * pairInd Q.pair₀₁ a b * pairInd Q.pair₀₂ a d * pairInd Q.pair₁₂ b d := by
  let m (q : Finset {p : V × V // p.1 ≠ p.2}) := q.map (Function.Embedding.subtype _)
  let pred : V × V × V → Prop := fun p ↦ (p.1, p.2.1) ∈ m Q.pair₀₁ ∧
    (p.1, p.2.2) ∈ m Q.pair₀₂ ∧ (p.2.1, p.2.2) ∈ m Q.pair₁₂
  calc _ = ∑ p ∈ (P.c₀ ×ˢ P.c₁ ×ˢ P.c₂).filter pred, φ p.1 p.2.1 p.2.2 := by
        refine sum_bij' (fun x _ ↦ (x.1 0, x.1 1, x.1 2))
          (fun p hp ↦ ⟨![p.1, p.2.1, p.2.2], ?_⟩) ?_ ?_ ?_ ?_ ?_
        · obtain ⟨-, h₀₁, h₀₂, h₁₂⟩ := mem_filter.1 hp
          obtain ⟨hab, -⟩ := exists_mem_of_mem_map h₀₁
          obtain ⟨had, -⟩ := exists_mem_of_mem_map h₀₂
          obtain ⟨hbd, -⟩ := exists_mem_of_mem_map h₁₂
          intro j k hjk
          fin_cases j <;> fin_cases k <;> simp_all [eq_comm]
        · intro x hx
          obtain ⟨hP, h₀₁, h₀₂, h₁₂⟩ := (Q.mem_support x).1 hx
          obtain ⟨h₀, h₁, h₂, -⟩ := (P.mem_support x).1 hP
          exact mem_filter.2 ⟨mem_product.2 ⟨h₀, mem_product.2 ⟨h₁, h₂⟩⟩,
            mem_map.2 ⟨_, h₀₁, by simp⟩, mem_map.2 ⟨_, h₀₂, by simp⟩, mem_map.2 ⟨_, h₁₂, by simp⟩⟩
        · intro p hp
          obtain ⟨-, h₀₁, h₀₂, h₁₂⟩ := mem_filter.1 hp
          obtain ⟨_, h₀₁⟩ := exists_mem_of_mem_map h₀₁
          obtain ⟨_, h₀₂⟩ := exists_mem_of_mem_map h₀₂
          obtain ⟨_, h₁₂⟩ := exists_mem_of_mem_map h₁₂
          refine (Q.mem_support_iff_coordPair_mem _).2 ⟨?_, ?_, ?_⟩
          · convert h₀₁ using 1
            exact Subtype.ext (by simp)
          · convert h₀₂ using 1
            exact Subtype.ext (by simp)
          · convert h₁₂ using 1
            exact Subtype.ext (by simp)
        · intro x _
          ext j
          fin_cases j <;> rfl
        · intro p _
          rfl
        · intro x _
          rfl
    _ = _ := by
        rw [sum_filter, sum_product]
        refine sum_congr rfl fun a _ ↦ ?_
        rw [sum_product]
        refine sum_congr rfl fun b _ ↦ sum_congr rfl fun d _ ↦ ?_
        simp only [pairInd, m]
        split_ifs <;> simp_all

end Coordinates

variable [DecidableEq κ] [Fintype ι] [DecidableEq ι]

/-- A bound on the count discrepancy of a split color, relative to the size of a set of
injective triples, bounds its density discrepancy. -/
theorem abs_relDensityOn_split_sub_le (H : Colored3Graph κ V) (f : Set.powersetCard V 3 → ι)
    (c : κ) (i : ι) (s : Finset {x : Fin 3 → V // Function.Injective x}) {b : ℝ} (hb : 0 ≤ b)
    (h : |(#{x ∈ s | (H.split f).color (Set.powersetCard.ofFinEmb 3 V ⟨x.1, x.2⟩) = (c, i)} : ℝ) -
        #{x ∈ s | H.color (Set.powersetCard.ofFinEmb 3 V ⟨x.1, x.2⟩) = c} / Fintype.card ι| ≤
      b * #s) :
    |((H.split f).relDensityOn (c, i) s : ℝ) - H.relDensityOn c s / Fintype.card ι| ≤ b := by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · simpa using hb
  have hs' : (0 : ℝ) < #s := by exact_mod_cast hs.card_pos
  have h₁ := congrArg (fun q : ℚ ↦ (q : ℝ)) ((H.split f).relDensityOn_mul_card (c, i) s)
  have h₂ := congrArg (fun q : ℚ ↦ (q : ℝ)) (H.relDensityOn_mul_card c s)
  push_cast at h₁ h₂
  rw [← mul_le_mul_iff_of_pos_right hs']
  calc _ = |(((H.split f).relDensityOn (c, i) s : ℝ) - H.relDensityOn c s / Fintype.card ι) *
        #s| := by rw [abs_mul, abs_of_pos hs']
    _ = _ := by rw [sub_mul, div_mul_eq_mul_div, h₁, h₂]
    _ ≤ _ := h

variable [DecidableEq V]

private theorem tripleDev_coord (H : Colored3Graph κ V) (c : κ) (i : ι)
    (f : Set.powersetCard V 3 → ι) (x : {x : Fin 3 → V // Function.Injective x}) :
    tripleDev H c i f (x.1 0) (x.1 1) (x.1 2) =
      splitDev H c i (Set.powersetCard.ofFinEmb 3 V ⟨x.1, x.2⟩)
        (f (Set.powersetCard.ofFinEmb 3 V ⟨x.1, x.2⟩)) := by
  have h₃ : #({x.1 0, x.1 1, x.1 2} : Finset V) = 3 := by
    rw [← val_ofFinEmb_eq]
    exact Set.powersetCard.card_eq _
  have he : Set.powersetCard.ofCard h₃ = Set.powersetCard.ofFinEmb 3 V ⟨x.1, x.2⟩ :=
    Subtype.ext (val_ofFinEmb_eq x).symm
  simp only [tripleDev, h₃, ↓reduceDIte, he]

/-- On a set of injective triples, the deviations add up to the count of the split color
`(c, i)` minus a `1 / |ι|` share of the count of `c`. -/
private theorem sum_tripleDev_coord (H : Colored3Graph κ V) (c : κ) (i : ι)
    (f : Set.powersetCard V 3 → ι) (s : Finset {x : Fin 3 → V // Function.Injective x}) :
    ∑ x ∈ s, tripleDev H c i f (x.1 0) (x.1 1) (x.1 2) =
      #{x ∈ s | (H.split f).color (Set.powersetCard.ofFinEmb 3 V ⟨x.1, x.2⟩) = (c, i)} -
        (#{x ∈ s | H.color (Set.powersetCard.ofFinEmb 3 V ⟨x.1, x.2⟩) = c} : ℝ) /
          Fintype.card ι := by
  simp only [card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero, sum_div,
    ← sum_sub_distrib, tripleDev_coord, color_split, Prod.mk.injEq]
  refine sum_congr rfl fun x _ ↦ ?_
  unfold splitDev
  split_ifs <;> simp_all [div_eq_mul_inv]

variable [Nonempty ι]

/-- Some labelling makes every normalized octahedral sum, over the cell triples of `𝒜` and the
colors of `κ × ι`, at most the average `9 |𝒜| ^ 3 |κ| |ι| / N`. -/
private theorem exists_forall_splitOct_le [Fintype κ] [Finite V] (H : Colored3Graph κ V)
    (𝒜 : Finset (Finset V)) {N : ℕ} (hN₀ : 0 < N) (hN : ∀ A ∈ 𝒜, N ≤ #A) :
    ∃ f : Set.powersetCard V 3 → ι, ∀ A ∈ 𝒜, ∀ B ∈ 𝒜, ∀ C ∈ 𝒜, ∀ (c : κ) (i : ι),
      splitOct H c i f A B C ≤
        9 * #𝒜 ^ 3 * Fintype.card κ * Fintype.card ι / N * (#A * #B * #C) ^ 2 := by
  have := Fintype.ofFinite V
  let D := 𝒜 ×ˢ 𝒜 ×ˢ 𝒜 ×ˢ (univ : Finset (κ × ι))
  let W (f : Set.powersetCard V 3 → ι) : ℝ :=
    ∑ p ∈ D, splitOct H p.2.2.2.1 p.2.2.2.2 f p.1 p.2.1 p.2.2.1 / (#p.1 * #p.2.1 * #p.2.2.1) ^ 2
  have hW : ∑ f, W f ≤ ∑ _f : Set.powersetCard V 3 → ι,
      (9 * #𝒜 ^ 3 * Fintype.card κ * Fintype.card ι / N : ℝ) := by
    rw [sum_comm]
    refine (sum_le_sum fun p hp ↦ ?_ :
      _ ≤ ∑ _p ∈ D, (Fintype.card (Set.powersetCard V 3 → ι) : ℝ) * 9 / N) |>.trans_eq ?_
    · simp only [D, mem_product] at hp
      exact sum_splitOct_div_le H _ _ _ _ _ hN₀ (hN _ hp.1) (hN _ hp.2.1) (hN _ hp.2.2.1)
    simp only [D, sum_const, card_product, card_univ, Fintype.card_prod, nsmul_eq_mul,
      Nat.cast_mul]
    ring
  obtain ⟨f, -, hf⟩ := exists_le_of_sum_le univ_nonempty hW
  refine ⟨f, fun A hA B hB C hC c i ↦ ?_⟩
  have hle := (single_le_sum (s := D)
    (fun p _ ↦ div_nonneg (splitOct_nonneg ..) (sq_nonneg _))
    (by simp [D, hA, hB, hC] : (A, B, C, c, i) ∈ D)).trans hf
  have hABC : (0 : ℝ) < (#A * #B * #C) ^ 2 := by
    have := hN₀.trans_le (hN A hA)
    have := hN₀.trans_le (hN B hB)
    have := hN₀.trans_le (hN C hC)
    positivity
  rwa [div_le_iff₀ hABC] at hle

variable [Fintype V]

/-- **Quasirandom splitting of triple colors.** Let `S` be a lower skeleton with `t` vertex
cells, each of size at least `N`. If `9 t ^ 3 |κ| |ι| ≤ δ ^ 8 N`, then some labelling
`f` of the triples by `ι` splits every color `c` of `H` evenly on every subpolyad `Q` of every
polyad `P` over `S`: the number of triples of `Q` of split color `(c, i)` is within
`δ |P.c₀| |P.c₁| |P.c₂|` of `1 / |ι|` times the number of triples of color `c`. -/
theorem exists_split_abs_card_sub_le [Fintype κ] (H : Colored3Graph κ V) {κ₂ : Type*}
    (S : PairSkeleton3 κ₂ V) {N : ℕ} {δ : ℝ} (hδ : 0 ≤ δ)
    (hN : ∀ A ∈ S.vertexPart.parts, N ≤ #A)
    (h : 9 * #S.vertexPart.parts ^ 3 * Fintype.card κ * Fintype.card ι ≤ δ ^ 8 * N) :
    ∃ f : Set.powersetCard V 3 → ι, ∀ (P : Polyad3 S) (Q : Subpolyad3 P) (c : κ) (i : ι),
      |(#{x ∈ Q.support |
          (H.split f).color (Set.powersetCard.ofFinEmb 3 V ⟨x.1, x.2⟩) = (c, i)} : ℝ) -
        #{x ∈ Q.support | H.color (Set.powersetCard.ofFinEmb 3 V ⟨x.1, x.2⟩) = c} /
          Fintype.card ι| ≤
      δ * #P.c₀ * #P.c₁ * #P.c₂ := by
  obtain rfl | hN₀ := Nat.eq_zero_or_pos N
  · -- With `N = 0`, the hypothesis forces the cells or the palette to be empty.
    refine ⟨fun _ ↦ Classical.arbitrary ι, fun P _ c _ ↦ absurd h (not_le.2 ?_)⟩
    have ht : (1 : ℝ) ≤ #S.vertexPart.parts := by exact_mod_cast card_pos.2 ⟨P.c₀, P.hc₀⟩
    have hκ : (1 : ℝ) ≤ Fintype.card κ := by
      have : Nonempty κ := ⟨c⟩
      exact_mod_cast Fintype.card_pos
    simp only [Nat.cast_zero, mul_zero]
    positivity
  obtain ⟨f, hf⟩ := exists_forall_splitOct_le (ι := ι) H S.vertexPart.parts hN₀ hN
  refine ⟨f, fun P Q c i ↦ ?_⟩
  -- Three applications of Cauchy–Schwarz bound the eighth power of the discrepancy by the
  -- octahedral sum.
  rw [← sum_tripleDev_coord, sum_support_eq_sum_cells]
  refine (pow_le_pow_iff_left₀ (abs_nonneg _) (by positivity) (by norm_num : 8 ≠ 0)).1 ?_
  rw [(by decide : Even 8).pow_abs]
  calc _ ≤ (#P.c₀ * #P.c₁ * #P.c₂ : ℝ) ^ 6 * splitOct H c i f P.c₀ P.c₁ P.c₂ :=
        sum_sum_sum_mul_pow_eight_le _ (fun _ _ _ _ ↦ abs_pairInd_le_one ..)
          (fun _ _ _ _ ↦ abs_pairInd_le_one ..) (fun _ _ _ _ ↦ abs_pairInd_le_one ..)
    _ ≤ (#P.c₀ * #P.c₁ * #P.c₂ : ℝ) ^ 6 * (δ ^ 8 * (#P.c₀ * #P.c₁ * #P.c₂) ^ 2) := by
        gcongr
        refine (hf _ P.hc₀ _ P.hc₁ _ P.hc₂ c i).trans ?_
        gcongr
        rwa [div_le_iff₀ (by exact_mod_cast hN₀)]
    _ = _ := by ring

variable {κ₂ : Type*} {S : PairSkeleton3 κ₂ V} {P : Polyad3 S} {H : Colored3Graph κ V} {δ : ℝ}
  {f : Set.powersetCard V 3 → ι}

/-- **Quasirandom splitting preserves top regularity.** If `H` is `(δ, 1)`-top-regular over `P`
and the splitting by `f` is quasirandom on the subpolyads of `P` at scale `δ ^ 2 / 2` relative to
the support of `P`, then the split coloring is `(2 δ, 1)`-top-regular over `P`. -/
theorem IsTopRegularOverPolyad.split (h : H.IsTopRegularOverPolyad P δ 1)
    (hdisc : ∀ (c : κ) (i : ι) (Q : Subpolyad3 P),
      |(#{x ∈ Q.support |
          (H.split f).color (Set.powersetCard.ofFinEmb 3 V ⟨x.1, x.2⟩) = (c, i)} : ℝ) -
        #{x ∈ Q.support | H.color (Set.powersetCard.ofFinEmb 3 V ⟨x.1, x.2⟩) = c} /
          Fintype.card ι| ≤
      δ ^ 2 / 2 * #P.support) :
    (H.split f).IsTopRegularOverPolyad P (2 * δ) 1 := by
  rw [isTopRegularOverPolyad_one_iff]
  rintro ⟨c, i⟩ Q hQ
  have : Nonempty κ := ⟨c⟩
  have hδ := h.nonneg
  obtain hδ₂ | hδ₂ := le_or_gt (1 / 2) δ
  · exact (H.split f).abs_relDensityOn_sub_relativeDensity_le_one _ _ P |>.trans (by linarith)
  have hq : (1 : ℝ) ≤ Fintype.card ι := by exact_mod_cast Fintype.card_pos
  -- The split densities are close to a `1 / |ι|` share of the original ones, on `Q` at scale
  -- `δ / 4` and on `P` at scale `δ ^ 2 / 2`.
  have e₁ := abs_relDensityOn_split_sub_le H f c i Q.support (b := δ / 4) (by positivity)
    ((hdisc c i Q).trans <| by
      calc δ ^ 2 / 2 * #P.support = δ / 4 * (2 * δ * #P.support) := by ring
        _ ≤ δ / 4 * #Q.support := by gcongr)
  have e₂ := abs_relDensityOn_split_sub_le H f c i P.support (b := δ ^ 2 / 2) (by positivity)
    (by simpa using hdisc c i (Subpolyad3.ofSubcells P P.c₀ P.c₁ P.c₂))
  have e₃ := isTopRegularOverPolyad_one_iff.1 h c Q
    (by linarith [mul_nonneg hδ (Nat.cast_nonneg (α := ℝ) #P.support)])
  have e₄ : |((H.relDensityOn c Q.support : ℝ) - H.relativeDensity c P) / Fintype.card ι| ≤ δ := by
    rw [abs_div, abs_of_pos (show (0 : ℝ) < Fintype.card ι by linarith)]
    exact (div_le_self (abs_nonneg _) hq).trans e₃
  rw [sub_div] at e₄
  rw [relativeDensity_def] at e₃ e₄ ⊢
  have hδ₄ : δ ^ 2 / 2 ≤ δ / 4 := by nlinarith
  rw [abs_le] at e₁ e₂ e₄ ⊢
  constructor <;> linarith

variable (H S) in
/-- **Top-regular polyads split quasirandomly.** Let `S` be a lower skeleton with `t` vertex
cells, each of size at least `N`, where `9 t ^ 3 |κ| |ι| ≤ (γ δ ^ 2 / 2) ^ 8 N`. Then some
labelling of the triples by `ι` has the following property on every polyad `P` over `S` whose
support fills at least a `γ`-proportion of its cell volume `|P.c₀| |P.c₁| |P.c₂|`: each split
color `(c, i)` has relative density over `P` within `δ ^ 2 / 2` of `1 / |ι|` times that of `c`,
and if `H` is `(δ, 1)`-top-regular over `P`, then the split coloring is `(2 δ, 1)`-top-regular
over `P`. -/
theorem exists_split_isTopRegularOverPolyad [Fintype κ] {N : ℕ} {γ : ℝ} (hγ : 0 ≤ γ)
    (hN : ∀ A ∈ S.vertexPart.parts, N ≤ #A)
    (h : 9 * #S.vertexPart.parts ^ 3 * Fintype.card κ * Fintype.card ι ≤
      (γ * δ ^ 2 / 2) ^ 8 * N) :
    ∃ f : Set.powersetCard V 3 → ι, ∀ P : Polyad3 S, γ * (#P.c₀ * #P.c₁ * #P.c₂) ≤ #P.support →
      (∀ c i, |((H.split f).relativeDensity (c, i) P : ℝ) -
        H.relativeDensity c P / Fintype.card ι| ≤ δ ^ 2 / 2) ∧
      (H.IsTopRegularOverPolyad P δ 1 → (H.split f).IsTopRegularOverPolyad P (2 * δ) 1) := by
  obtain ⟨f, hf⟩ := H.exists_split_abs_card_sub_le S (δ := γ * δ ^ 2 / 2) (by positivity) hN h
  refine ⟨f, fun P hP ↦ ?_⟩
  have hdisc (c : κ) (i : ι) (Q : Subpolyad3 P) :
      |(#{x ∈ Q.support |
          (H.split f).color (Set.powersetCard.ofFinEmb 3 V ⟨x.1, x.2⟩) = (c, i)} : ℝ) -
        #{x ∈ Q.support | H.color (Set.powersetCard.ofFinEmb 3 V ⟨x.1, x.2⟩) = c} /
          Fintype.card ι| ≤ δ ^ 2 / 2 * #P.support := by
    refine (hf P Q c i).trans ?_
    calc γ * δ ^ 2 / 2 * #P.c₀ * #P.c₁ * #P.c₂ = δ ^ 2 / 2 * (γ * (#P.c₀ * #P.c₁ * #P.c₂)) := by
          ring
      _ ≤ _ := by gcongr
  refine ⟨fun c i ↦ ?_, fun hreg ↦ hreg.split hdisc⟩
  rw [relativeDensity_def, relativeDensity_def]
  exact abs_relDensityOn_split_sub_le H f c i P.support (by positivity)
    (by simpa using hdisc c i (Subpolyad3.ofSubcells P P.c₀ P.c₁ P.c₂))

end Colored3Graph

end TauCeti
