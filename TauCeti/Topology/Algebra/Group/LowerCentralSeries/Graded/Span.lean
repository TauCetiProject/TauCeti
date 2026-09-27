/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Span.Basic
public import TauCeti.Topology.Algebra.Group.LowerCentralSeries.Graded.Basic
public import TauCeti.Topology.Algebra.Group.Profinite.Basic

/-!
# Spanning the degree-one graded piece of the lower `p`-series

Let `G` be a topological group whose second lower `p`-series term `λ_2` is open, and let `s` be a
subset that topologically generates `G`. For `p ≠ 0`, the degree-zero classes of the elements of `s`
span `gr_0(G) = G ⧸ λ_1` over `ZMod p`, and the degree-one piece `gr_1(G) = λ_1 ⧸ λ_2` is spanned by
the `p`-power classes `π g'` and the brackets `[g', h']` for `g, h ∈ s`. The generating set `s`
is arbitrary: it need not be finite, and only the closure of the subgroup it generates matters.
The degree-zero statement holds for every `p` and needs only that `λ_1` is open. Both statements
bound `gr_0(G)` and `gr_1(G)` in terms of the generators, which is the first step in computing
the graded pieces of a group given by generators.

For a linearly ordered index type the generators are packaged as `TauCeti.degreeOneFamily`: the
`p`-power classes `π y'_i` together with the brackets `[y'_i, y'_j]` for `i < j`. For a free pro-`p`
group on a finite linearly ordered set this family is a basis, which is proved in
`TauCeti.Topology.Algebra.Group.Profinite.Free.Graded`.

The openness hypothesis holds in a topologically finitely generated profinite group
(`TauCeti.IsTopologicallyFinitelyGenerated.isOpen_pLowerCentralSeries`).

## Main definitions

* `TauCeti.degreeOneFamily`: the degree-one family of a family `y : ι → G`, indexed by
  `ι ⊕ {ij : ι × ι // ij.1 < ij.2}`.

## Main results

* `TauCeti.span_gradedMkZero_image_eq_top`: the degree-zero classes of a topological generating
  set span `gr_0(G)`, when `λ_1` is open.
* `TauCeti.span_gradedPow_gradedMkZero_union_gradedBracket_eq_top`: the `p`-power classes and
  brackets of a topological generating set span `gr_1(G)`, when `λ_2` is open.
* `TauCeti.span_range_degreeOneFamily_eq_top`: the ordered form of the previous statement.

## References

* J. Labute, *Classification of Demushkin groups*, Canadian J. Math. 19 (1967), §1.
-/

public section

open Subgroup Submodule
open scoped commutatorElement

namespace TauCeti

universe u

variable {p : ℕ} {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-! ### Degree zero -/

/-- **The degree-zero classes of a topological generating set span `gr_0(G)`**, when `λ_1` is
open: the image of a dense subgroup in the discrete quotient `G ⧸ λ_1` is everything. -/
theorem span_gradedMkZero_image_eq_top (h₁ : IsOpen (pLowerCentralSeries p G 1 : Set G))
    {s : Set G} (hs : (Subgroup.closure s).topologicalClosure = ⊤) :
    span (ZMod p) (gradedMkZero p G '' s) = ⊤ := by
  let U : OpenNormalSubgroup G := ⟨⟨pLowerCentralSeries p G 1, h₁⟩, inferInstance⟩
  have hmap : Subgroup.closure ((QuotientGroup.mk' U.toSubgroup) '' s) = ⊤ := by
    rw [← MonoidHom.map_closure, ← Subgroup.map_topologicalClosure_quotient_eq, hs]
    exact map_top_of_surjective _ (QuotientGroup.mk'_surjective _)
  rw [eq_top_iff]
  rintro x -
  obtain ⟨g, rfl⟩ := gradedMkZero_surjective x
  have hg : (g : G ⧸ pLowerCentralSeries p G 1) ∈
      Subgroup.closure ((QuotientGroup.mk' U.toSubgroup) '' s) :=
    hmap ▸ Subgroup.mem_top _
  -- Every element of `G ⧸ λ_1` is a word in the images of `s`; lift the word to `gr_0(G)`.
  refine closure_induction (p := fun q _ ↦ ∀ g : G, (g : G ⧸ pLowerCentralSeries p G 1) = q →
    gradedMkZero p G g ∈ span (ZMod p) (gradedMkZero p G '' s)) ?_ ?_ ?_ ?_ hg g rfl
  · rintro _ ⟨y, hy, rfl⟩ g hg
    rw [QuotientGroup.mk'_apply] at hg
    rw [gradedMkZero_eq_gradedMkZero_iff.mpr hg]
    exact subset_span ⟨y, hy, rfl⟩
  · intro g hg
    rw [gradedMkZero_eq_gradedMkZero_iff.mpr (hg.trans (QuotientGroup.mk_one _).symm),
      gradedMkZero_one]
    exact zero_mem _
  · intro x y _ _ ihx ihy g hg
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective y
    rw [gradedMkZero_eq_gradedMkZero_iff.mpr (hg.trans (QuotientGroup.mk_mul _ a b).symm),
      gradedMkZero_mul]
    exact add_mem (ihx a rfl) (ihy b rfl)
  · intro x _ ihx g hg
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
    rw [gradedMkZero_eq_gradedMkZero_iff.mpr (hg.trans (QuotientGroup.mk_inv _ a).symm),
      gradedMkZero_inv]
    exact neg_mem (ihx a rfl)

/-! ### Degree one -/

/-- **The bracket of two elements of a span** lies in any submodule containing the brackets of the
generators: the bracket is `ZMod p`-bilinear. -/
theorem gradedBracket_mem_of_mem_span (W : Submodule (ZMod p) (gradedPiece p G 1))
    {S : Set (gradedPiece p G 0)} (hS : ∀ x ∈ S, ∀ y ∈ S, gradedBracket p G 0 0 x y ∈ W)
    {x y : gradedPiece p G 0} (hx : x ∈ span (ZMod p) S) (hy : y ∈ span (ZMod p) S) :
    gradedBracket p G 0 0 x y ∈ W := by
  induction hx, hy using span_induction₂ with
  | mem_mem x y hx hy => exact hS x hx y hy
  | zero_left y _ => rw [map_zero, AddMonoidHom.zero_apply]; exact zero_mem _
  | zero_right x _ => rw [map_zero]; exact zero_mem _
  | add_left x y z _ _ _ hxz hyz => rw [map_add, AddMonoidHom.add_apply]; exact add_mem hxz hyz
  | add_right x y z _ _ _ hxy hxz => rw [map_add]; exact add_mem hxy hxz
  | smul_left r x y _ _ hxy =>
    rw [← AddMonoidHom.flip_apply, ZMod.map_smul, AddMonoidHom.flip_apply]
    exact W.smul_mem r hxy
  | smul_right r x y _ _ hxy => rw [ZMod.map_smul]; exact W.smul_mem r hxy

/-- **The `p`-power of an element of a span** lies in any submodule containing the `p`-powers and
the brackets of the generators: the degree-zero defect of additivity of `π` is a bracket. -/
theorem gradedPow_mem_of_mem_span [NeZero p] (W : Submodule (ZMod p) (gradedPiece p G 1))
    {S : Set (gradedPiece p G 0)} (hpow : ∀ x ∈ S, gradedPow p G 0 x ∈ W)
    (hS : ∀ x ∈ S, ∀ y ∈ S, gradedBracket p G 0 0 x y ∈ W)
    {x : gradedPiece p G 0} (hx : x ∈ span (ZMod p) S) : gradedPow p G 0 x ∈ W := by
  induction hx using span_induction with
  | mem x hx => exact hpow x hx
  | zero => rw [gradedPow_zero]; exact zero_mem _
  | add x y hx hy ihx ihy =>
    rw [gradedPow_add_zero]
    exact add_mem (add_mem ihx ihy) (nsmul_mem (gradedBracket_mem_of_mem_span W hS hy hx) _)
  | smul r x _ ih => rw [gradedPow_smul_zero]; exact W.smul_mem r ih

/-- **The `p`-power classes and the brackets of a topological generating set span `gr_1(G)`**,
when `λ_2` is open. -/
theorem span_gradedPow_gradedMkZero_union_gradedBracket_eq_top [NeZero p]
    (h₂ : IsOpen (pLowerCentralSeries p G 2 : Set G)) {s : Set G}
    (hs : (Subgroup.closure s).topologicalClosure = ⊤) :
    span (ZMod p) ((fun g ↦ gradedPow p G 0 (gradedMkZero p G g)) '' s ∪
      (fun gh : G × G ↦ gradedBracket p G 0 0 (gradedMkZero p G gh.1) (gradedMkZero p G gh.2)) ''
        (s ×ˢ s)) = ⊤ := by
  set W := span (ZMod p) ((fun g ↦ gradedPow p G 0 (gradedMkZero p G g)) '' s ∪
    (fun gh : G × G ↦ gradedBracket p G 0 0 (gradedMkZero p G gh.1) (gradedMkZero p G gh.2)) ''
      (s ×ˢ s)) with hW
  have h₁ : IsOpen (pLowerCentralSeries p G 1 : Set G) :=
    Subgroup.isOpen_mono (pLowerCentralSeries_antitone (by omega)) h₂
  have hmem (x : gradedPiece p G 0) : x ∈ span (ZMod p) (gradedMkZero p G '' s) := by
    rw [span_gradedMkZero_image_eq_top h₁ hs]
    exact Submodule.mem_top
  have hgen : ∀ x ∈ gradedMkZero p G '' s, ∀ y ∈ gradedMkZero p G '' s,
      gradedBracket p G 0 0 x y ∈ W := by
    rintro _ ⟨g, hg, rfl⟩ _ ⟨h, hh, rfl⟩
    exact subset_span (Or.inr ⟨(g, h), ⟨hg, hh⟩, rfl⟩)
  have hbracket (g h : G) : gradedBracket p G 0 0 (gradedMkZero p G g) (gradedMkZero p G h) ∈ W :=
    gradedBracket_mem_of_mem_span W hgen (hmem _) (hmem _)
  have hpow (g : G) : gradedPow p G 0 (gradedMkZero p G g) ∈ W := by
    refine gradedPow_mem_of_mem_span W ?_ hgen (hmem _)
    rintro _ ⟨g, hg, rfl⟩
    exact subset_span (Or.inl ⟨g, hg, rfl⟩)
  -- The preimage of `W` in `G`: a union of cosets of the open subgroup `λ_2`, hence closed.
  let U : Subgroup G :=
    { carrier := {g | ∃ w ∈ W, gradedPieceInclusion p G 1 w =
        Additive.ofMul (g : G ⧸ pLowerCentralSeries p G 2)}
      one_mem' := ⟨0, W.zero_mem, by rw [map_zero, QuotientGroup.mk_one, ofMul_one]⟩
      mul_mem' := by
        rintro a b ⟨v, hv, hva⟩ ⟨w, hw, hwb⟩
        exact ⟨v + w, W.add_mem hv hw, by rw [map_add, hva, hwb, QuotientGroup.mk_mul, ofMul_mul]⟩
      inv_mem' := by
        rintro a ⟨v, hv, hva⟩
        exact ⟨-v, W.neg_mem hv, by rw [map_neg, hva, QuotientGroup.mk_inv, ofMul_inv]⟩ }
  have hU : pLowerCentralSeries p G 2 ≤ U := fun g hg ↦
    ⟨0, W.zero_mem, by rw [map_zero, (QuotientGroup.eq_one_iff g).mpr hg, ofMul_one]⟩
  have hUclosed : IsClosed (U : Set G) := U.isClosed_of_isOpen (Subgroup.isOpen_mono hU h₂)
  have hlam₁ : pLowerCentralSeries p G 1 ≤ U := by
    rw [pLowerCentralSeries_succ, pLowerCentralSeries_zero]
    refine (pLowerCentralStep_le_iff hUclosed).mpr ⟨fun g _ ↦ ?_, commutator_le.mpr
      fun g _ h _ ↦ ?_⟩
    · exact ⟨_, hpow g, by rw [gradedPow_gradedMkZero, gradedPieceInclusion_gradedMk]⟩
    · exact ⟨_, hbracket g h, by rw [gradedBracket_gradedMkZero, gradedPieceInclusion_gradedMk]⟩
  rw [eq_top_iff]
  rintro y -
  obtain ⟨y, rfl⟩ := gradedMk_surjective 1 y
  obtain ⟨w, hw, hwy⟩ := hlam₁ y.2
  rw [← gradedPieceInclusion_gradedMk] at hwy
  exact gradedPieceInclusion_injective 1 hwy ▸ hw

/-! ### The degree-one family of an ordered family -/

variable (p) in
/-- **The degree-one family** of a family `y : ι → G` indexed by a linearly ordered type: the
`p`-power classes `π y'_i` and the brackets `[y'_i, y'_j]` for `i < j`, in `gr_1(G)`. When `y`
topologically generates `G` and `λ_2` is open it spans `gr_1(G)`
(`TauCeti.span_range_degreeOneFamily_eq_top`); for the canonical generators of a free pro-`p`
group on a finite linearly ordered type it is a basis. -/
def degreeOneFamily {ι : Type*} [LT ι] (y : ι → G) :
    ι ⊕ {ij : ι × ι // ij.1 < ij.2} → gradedPiece p G 1 :=
  Sum.elim (fun i ↦ gradedPow p G 0 (gradedMkZero p G (y i)))
    fun ij ↦ gradedBracket p G 0 0 (gradedMkZero p G (y ij.1.1)) (gradedMkZero p G (y ij.1.2))

section DegreeOneFamily

variable {ι : Type*} [LT ι] (y : ι → G)

@[simp]
theorem degreeOneFamily_inl (i : ι) :
    degreeOneFamily p y (Sum.inl i) = gradedPow p G 0 (gradedMkZero p G (y i)) := by
  rw [degreeOneFamily, Sum.elim_inl]

@[simp]
theorem degreeOneFamily_inr (ij : {ij : ι × ι // ij.1 < ij.2}) :
    degreeOneFamily p y (Sum.inr ij) =
      gradedBracket p G 0 0 (gradedMkZero p G (y ij.1.1)) (gradedMkZero p G (y ij.1.2)) := by
  rw [degreeOneFamily, Sum.elim_inr]

variable {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

/-- **Naturality of the degree-one family**: a continuous homomorphism carries the degree-one
family of `y` to the degree-one family of `f ∘ y`. -/
@[simp]
theorem gradedMap_degreeOneFamily (f : G →* H) (hf : Continuous f)
    (k : ι ⊕ {ij : ι × ι // ij.1 < ij.2}) :
    gradedMap p f hf 1 (degreeOneFamily p y k) = degreeOneFamily p (f ∘ y) k := by
  rcases k with i | ij
  · rw [degreeOneFamily_inl, degreeOneFamily_inl, Function.comp_apply, ← gradedMap_gradedMkZero,
      gradedMap_gradedPow]
  · rw [degreeOneFamily_inr, degreeOneFamily_inr, Function.comp_apply, Function.comp_apply,
      ← gradedMap_gradedMkZero, ← gradedMap_gradedMkZero]
    exact gradedMap_gradedBracket f hf (j := 0) (k := 0) _ _

end DegreeOneFamily

/-- **The degree-one family of a topological generating family spans `gr_1(G)`**, when `λ_2` is
open: the ordered form of `TauCeti.span_gradedPow_gradedMkZero_union_gradedBracket_eq_top`,
using that the bracket is alternating and skew-symmetric. -/
theorem span_range_degreeOneFamily_eq_top [NeZero p] {ι : Type*} [LinearOrder ι] {y : ι → G}
    (h₂ : IsOpen (pLowerCentralSeries p G 2 : Set G))
    (hy : (Subgroup.closure (Set.range y)).topologicalClosure = ⊤) :
    span (ZMod p) (Set.range (degreeOneFamily p y)) = ⊤ := by
  rw [eq_top_iff, ← span_gradedPow_gradedMkZero_union_gradedBracket_eq_top h₂ hy, span_le]
  rintro _ (⟨_, ⟨i, rfl⟩, rfl⟩ | ⟨⟨_, _⟩, ⟨⟨i, rfl⟩, ⟨j, rfl⟩⟩, rfl⟩)
  · exact subset_span ⟨Sum.inl i, degreeOneFamily_inl y i⟩
  · dsimp only
    rcases lt_trichotomy i j with hij | rfl | hji
    · exact subset_span ⟨Sum.inr ⟨(i, j), hij⟩, degreeOneFamily_inr y _⟩
    · rw [SetLike.mem_coe, gradedBracket_self]
      exact zero_mem _
    · have h := gradedCast_gradedBracket_swap (gradedMkZero p G (y j)) (gradedMkZero p G (y i))
      rw [gradedCast_rfl] at h
      rw [SetLike.mem_coe, h]
      exact neg_mem (subset_span ⟨Sum.inr ⟨(j, i), hji⟩, degreeOneFamily_inr y _⟩)

end TauCeti
