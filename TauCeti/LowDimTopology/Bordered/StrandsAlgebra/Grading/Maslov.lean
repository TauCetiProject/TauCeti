/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LowDimTopology.Bordered.StrandsAlgebra.Grading.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Order

/-!
# The Maslov component of the grading of strand diagrams

The grading `gr(φ) = (inv(φ) - m([φ], S), [φ])` of a strand diagram `φ : S → T`
(`TauCeti.StrandDiagram.grading`) is defined through its crossing number and the multiplicity of
its class at its starting points. Lipshitz, Ozsváth and Thurston express its Maslov component
through the strands alone, as the quantity `ι(ρ)` of a set `ρ` of Reeb chords which enters the
index of holomorphic curves in bordered Heegaard diagrams:

  `ι(ρ) = -|ρ| / 2 - ∑_{{ρ_a, ρ_b} ⊆ ρ} |L(ρ_a, ρ_b)|`,

where `|ρ|` is the number of chords, that is of strands that are not horizontal, and `L` is the
bilinear form defining the product of the grading group (`TauCeti.StrandGradingGroup.linking`),
evaluated on the classes of single strands. This file proves that the Maslov component of `gr(φ)`
is `ι` of the strands of `φ` (`TauCeti.StrandDiagram.grading_maslov_eq`), for every strand diagram:
a horizontal strand has zero class, and its crossings with other strands are compensated by the
multiplicity term. For two strands starting at `a < b` the form `L` is nonnegative: it is `0` when
the strands are disjoint or nested, `1/2` when the first ends where the second starts, and `1`
when they interleave.

For a sequence `(ρ₁, …, ρₙ)` of sets of chords, the index uses
`ι(ρ₁, …, ρₙ) = ∑ᵢ ι(ρᵢ) + ∑_{i < j} L(ρᵢ, ρⱼ)`, which is the Maslov component of the product
`gr(ρ₁) ⋯ gr(ρₙ)` in the grading group (`TauCeti.StrandGradingGroup.maslov_prod_ofFn`).

## Main definitions

* `TauCeti.StrandDiagram.strandBoundary`: the boundary of the class of the strand of a diagram
  starting at a given point.

## Main results

* `TauCeti.StrandGradingGroup.boundary_list_prod`, `TauCeti.StrandGradingGroup.maslov_prod_ofFn`:
  the boundary and the Maslov component of a product of finitely many elements of the grading
  group.
* `TauCeti.StrandDiagram.sum_strandBoundary`: the class of a diagram is the sum of the classes of
  its strands.
* `TauCeti.StrandDiagram.linking_strandBoundary_nonneg`: `L` of two strands, taken in the order
  of their starting points, is nonnegative.
* `TauCeti.StrandDiagram.grading_maslov_eq`: the Maslov component of `gr(φ)` is
  `-|ρ| / 2 - ∑_{a < b} |L(ρ_a, ρ_b)|`.

## References

* R. Lipshitz, P. Ozsváth and D. Thurston, *Bordered Heegaard Floer homology*, Mem. Amer. Math.
  Soc. **254** (2018), no. 1216, [arXiv:0810.0687](https://arxiv.org/abs/0810.0687), §5.7.1 (the
  quantity `ι` of a sequence of sets of Reeb chords) and §3.3.1 (the grading of the strands
  algebra).
-/

public section

open Finset

namespace TauCeti

variable {α : Type*} [LinearOrder α] [Fintype α]

namespace StrandGradingGroup

/-- The boundary of the product of a list of elements of the grading group is the sum of their
boundaries. -/
@[simp]
theorem boundary_list_prod (l : List (StrandGradingGroup α)) :
    l.prod.boundary = (l.map boundary).sum := by
  induction l with
  | nil => simp
  | cons g l ih => simp [ih]

/-- **The Maslov component of a product.** The Maslov component of `g₁ ⋯ gₙ` is
`∑ᵢ maslov gᵢ + ∑_{i < j} L(∂gᵢ, ∂gⱼ)`. -/
theorem maslov_prod_ofFn {n : ℕ} (g : Fin n → StrandGradingGroup α) :
    (List.ofFn g).prod.maslov = ∑ i, (g i).maslov +
      ∑ i, ∑ j with i < j, linking (g i).boundary (g j).boundary := by
  induction n with
  | zero => simp
  | succ n ih =>
    -- The pairs `(0, j)` give `L(∂g₀, ∂(g₁ ⋯ gₙ))`, the others are the pairs of the tail.
    rw [List.ofFn_succ, List.prod_cons, mul_maslov, ih, boundary_list_prod, Fin.sum_univ_succ,
      Fin.sum_univ_succ]
    simp only [sum_filter, Fin.sum_univ_succ, lt_self_iff_false, ite_false, Fin.succ_pos, ite_true,
      Fin.succ_lt_succ_iff, Fin.not_lt_zero, zero_add, List.map_ofFn, List.sum_ofFn, map_sum,
      Function.comp_apply]
    ring

/-- The multiplicity at `p` of the class of a chord from `s` to `t`, whose boundary is
`[t] - [s]`. -/
theorem pointMultiplicity_single_sub_single (p s t : α) :
    pointMultiplicity p (Pi.single t 1 - Pi.single s 1) =
      (if s < p then 1 else 0) - (if t < p then 1 else 0) -
        ((if p = t then 1 else 0) - (if p = s then 1 else 0)) / 2 := by
  rw [pointMultiplicity_apply]
  simp only [Pi.sub_apply, Int.cast_sub, sum_sub_distrib, Pi.single_apply, Int.cast_ite,
    Int.cast_one, Int.cast_zero, sum_ite_eq', mem_filter, mem_univ, true_and]
  ring

/-- The form `L` on the class of a chord from `s` to `t`: `L([t] - [s], β) = m(β, t) - m(β, s)`. -/
theorem linking_single_sub_single (s t : α) (δ : α → ℤ) :
    linking (Pi.single t 1 - Pi.single s 1) δ = pointMultiplicity t δ - pointMultiplicity s δ := by
  simp [linking_apply, Pi.single_apply]

end StrandGradingGroup

namespace StrandDiagram

open StrandGradingGroup

/-- The boundary `[φ a] - [a]` of the class of the strand of `φ` starting at `a`. It is zero for
a horizontal strand and for a point `a` that is not a starting point of `φ`. -/
def strandBoundary (φ : StrandDiagram α) (a : α) : α → ℤ :=
  Pi.single (φ.endpoint a) 1 - Pi.single a 1

omit [Fintype α] in
theorem strandBoundary_def (φ : StrandDiagram α) (a : α) :
    φ.strandBoundary a = Pi.single (φ.endpoint a) 1 - Pi.single a 1 :=
  (rfl)

/-- **The class of a diagram is the sum of the classes of its strands.** -/
theorem sum_strandBoundary (φ : StrandDiagram α) :
    ∑ a ∈ φ.source, φ.strandBoundary a = φ.boundary := by
  ext x
  have hT : ∑ a ∈ φ.source, (Pi.single (φ.endpoint a) 1 : α → ℤ) x =
      if x ∈ φ.target then 1 else 0 := by
    have himage : φ.target = φ.source.image φ.endpoint := by
      rw [target_eq_image]
      exact image_congr fun a _ ↦ (endpoint_def φ a).symm
    rw [himage, ← sum_image (f := fun t ↦ (Pi.single t 1 : α → ℤ) x) φ.endpoint_injOn]
    simp [Pi.single_apply, eq_comm]
  simp only [strandBoundary_def, Finset.sum_apply, Pi.sub_apply, sum_sub_distrib, hT,
    boundary_apply]
  simp [Pi.single_apply, eq_comm]

variable {φ : StrandDiagram α} {a b : α}

/-- The multiplicity of the class of the strand from `a` at its own starting point is `1/2`,
unless the strand is horizontal. -/
private theorem pointMultiplicity_strandBoundary_self (ha : a ∈ φ.source) :
    pointMultiplicity a (φ.strandBoundary a) = if φ.endpoint a ≠ a then 1 / 2 else 0 := by
  have h := le_getD ha
  rw [← endpoint_def] at h
  rw [strandBoundary_def, pointMultiplicity_single_sub_single]
  simp only [ne_eq, ite_not]
  split_ifs <;> first | order | norm_num

/-- The class of a strand starting above `a` has multiplicity zero at `a`. -/
private theorem pointMultiplicity_strandBoundary_of_lt (hb : b ∈ φ.source) (hab : a < b) :
    pointMultiplicity a (φ.strandBoundary b) = 0 := by
  have h := le_getD hb
  rw [← endpoint_def] at h
  rw [strandBoundary_def, pointMultiplicity_single_sub_single]
  split_ifs <;> first | order | norm_num

/-- The form `L` of the strands starting at `a < b`: `m(ρ_b, φ a)`, which is `0` for disjoint or
nested strands, `1/2` for abutting ones and `1` for interleaved ones. -/
private theorem linking_strandBoundary_of_lt (ha : a ∈ φ.source) (hb : b ∈ φ.source)
    (hab : a < b) :
    linking (φ.strandBoundary a) (φ.strandBoundary b) =
      (if b < φ.endpoint a then 1 else 0) - (if φ.endpoint b < φ.endpoint a then 1 else 0) +
        (if φ.endpoint a = b then 1 else 0) / 2 := by
  have hne : φ.endpoint a ≠ φ.endpoint b := fun h ↦ hab.ne (φ.endpoint_injOn ha hb h)
  rw [strandBoundary_def φ a, linking_single_sub_single,
    pointMultiplicity_strandBoundary_of_lt hb hab, strandBoundary_def,
    pointMultiplicity_single_sub_single]
  split_ifs <;> first | order | norm_num

/-- **`L` of two strands is nonnegative** when they are taken in the order of their starting
points. -/
theorem linking_strandBoundary_nonneg (ha : a ∈ φ.source) (hb : b ∈ φ.source) (hab : a < b) :
    0 ≤ linking (φ.strandBoundary a) (φ.strandBoundary b) := by
  have h := le_getD hb
  rw [← endpoint_def] at h
  rw [linking_strandBoundary_of_lt ha hb hab]
  split_ifs <;> first | order | norm_num

/-- For strands starting at `a < b`, the crossing indicator minus the multiplicity of the class of
the strand from `a` at `b` is `-L`. -/
private theorem inversion_sub_pointMultiplicity_eq (ha : a ∈ φ.source) (hb : b ∈ φ.source)
    (hab : a < b) :
    (if (a, b) ∈ φ.inversions then 1 else 0) - pointMultiplicity b (φ.strandBoundary a) =
      -linking (φ.strandBoundary a) (φ.strandBoundary b) := by
  have h₁ := le_getD ha
  have h₂ := le_getD hb
  rw [← endpoint_def] at h₁ h₂
  have hne : φ.endpoint a ≠ φ.endpoint b := fun h ↦ hab.ne (φ.endpoint_injOn ha hb h)
  have hinv : (a, b) ∈ φ.inversions ↔ φ.endpoint b < φ.endpoint a := by
    rw [mem_inversions_iff_of_mem (endpoint_mem ha) (endpoint_mem hb)]
    exact and_iff_right hab
  rw [linking_strandBoundary_of_lt ha hb hab, strandBoundary_def,
    pointMultiplicity_single_sub_single]
  by_cases h : φ.endpoint b < φ.endpoint a
  · simp only [hinv.2 h, h, h₂.trans_lt h, hab, ite_true]
    split_ifs <;> first | order | norm_num
  · simp only [mt hinv.1 h, h, hab, ite_true, ite_false]
    split_ifs <;> first | order | norm_num

/-- The crossing number counts the pairs `a < b` of starting points whose strands cross. -/
private theorem inversionCount_eq_sum (φ : StrandDiagram α) :
    (φ.inversionCount : ℚ) =
      ∑ p ∈ φ.source ×ˢ φ.source with p.1 < p.2, if p ∈ φ.inversions then 1 else 0 := by
  rw [sum_boole, inversionCount_def]
  congr 2
  ext p
  simp only [mem_filter, mem_product]
  exact ⟨fun h ↦ ⟨⟨⟨fst_mem_source_of_mem_inversions h, snd_mem_source_of_mem_inversions h⟩,
    (mem_inversions.1 h).1⟩, h⟩, fun h ↦ h.2⟩

/-- The multiplicity of the class of `φ` summed over its starting points: half the number of
strands that are not horizontal, plus `m(ρ_a, b)` over the pairs `a < b`. -/
private theorem sum_pointMultiplicity_boundary (φ : StrandDiagram α) :
    ∑ s ∈ φ.source, pointMultiplicity s φ.boundary =
      (#φ.eraseHorizontal.source : ℚ) / 2 +
        ∑ p ∈ φ.source ×ˢ φ.source with p.1 < p.2,
          pointMultiplicity p.2 (φ.strandBoundary p.1) := by
  -- Split the double sum `∑_s ∑_a m(ρ_a, s)` into its diagonal and the terms with `a < s`; the
  -- terms with `s < a` vanish.
  have hsplit (s : α) (hs : s ∈ φ.source) :
      ∑ a ∈ φ.source, pointMultiplicity s (φ.strandBoundary a) =
        (if φ.endpoint s ≠ s then 1 / 2 else 0) +
          ∑ a ∈ φ.source, if a < s then pointMultiplicity s (φ.strandBoundary a) else 0 := by
    rw [← add_sum_erase _ _ hs, ← add_sum_erase _ _ hs, pointMultiplicity_strandBoundary_self hs]
    simp only [lt_self_iff_false, ite_false, zero_add]
    congr 1
    refine sum_congr rfl fun a ha ↦ ?_
    obtain ⟨hne, ha⟩ := mem_erase.1 ha
    rcases hne.lt_or_gt with h | h
    · simp [h]
    · simp [h.not_gt, pointMultiplicity_strandBoundary_of_lt ha h]
  have hdiag : ∑ s ∈ φ.source, (if φ.endpoint s ≠ s then 1 / 2 else 0 : ℚ) =
      (#φ.eraseHorizontal.source : ℚ) / 2 := by
    rw [← sum_filter, sum_const, nsmul_eq_mul, source_eraseHorizontal, mul_one_div]
    congr 3
    ext s
    simp only [mem_filter, mem_sdiff, mem_horizontals]
    exact and_congr_right fun hs ↦ not_congr
      ⟨fun h ↦ by simpa only [h] using endpoint_mem hs, fun h ↦ endpoint_eq_of_mem h⟩
  rw [← φ.sum_strandBoundary]
  simp only [map_sum]
  rw [sum_congr rfl hsplit, sum_add_distrib, hdiag, sum_comm, sum_filter, sum_product]

/-- **The Maslov component of the grading of a strand diagram** is
`ι(ρ) = -|ρ| / 2 - ∑_{a < b} |L(ρ_a, ρ_b)|`, where `|ρ|` is the number of strands of `φ` that
are not horizontal and `ρ_a` is the strand starting at `a`. -/
theorem grading_maslov_eq (φ : StrandDiagram α) :
    φ.grading.maslov = -(#φ.eraseHorizontal.source : ℚ) / 2 -
      ∑ p ∈ φ.source ×ˢ φ.source with p.1 < p.2,
        |linking (φ.strandBoundary p.1) (φ.strandBoundary p.2)| := by
  have hpair : ∀ p ∈ {p ∈ φ.source ×ˢ φ.source | p.1 < p.2},
      (if p ∈ φ.inversions then 1 else 0) - pointMultiplicity p.2 (φ.strandBoundary p.1) =
        -|linking (φ.strandBoundary p.1) (φ.strandBoundary p.2)| := by
    intro p hp
    obtain ⟨⟨h₁, h₂⟩, hlt⟩ := by simpa only [mem_filter, mem_product] using hp
    rw [abs_of_nonneg (linking_strandBoundary_nonneg h₁ h₂ hlt)]
    exact inversion_sub_pointMultiplicity_eq h₁ h₂ hlt
  rw [grading_maslov, sum_pointMultiplicity_boundary, inversionCount_eq_sum]
  have := sum_congr rfl hpair
  rw [sum_sub_distrib, sum_neg_distrib] at this
  linarith

end StrandDiagram

end TauCeti
