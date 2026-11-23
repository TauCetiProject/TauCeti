/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DeRham.MayerVietoris
public import TauCeti.Geometry.Manifold.LocallyFlat.Separation
import TauCeti.Geometry.Manifold.LocalDiffeomorph.OpenSubset

/-!
# Bicollared hypersurfaces separate manifolds with vanishing first de Rham cohomology

Let `f : N → M` be a map with closed image and a bicollar `b : N × ℝ → M`
(`TauCeti.IsBicollar f b`), with `N` preconnected and nonempty, into a smooth manifold `M` with
`H¹_dR(M) = 0`. Then the complement of the image of `f` is not preconnected
(`TauCeti.IsBicollar.not_isPreconnected_compl_range`). The proof is the degree-zero end of the
Mayer–Vietoris sequence for the cover of `M` by the open sets `A = M \ range f` and `B = range b`.
The intersection `A ∩ B` is the union of the two disjoint open sides `b (N × (0, ∞))` and
`b (N × (-∞, 0))`, and the function equal to `1` on one side and `0` on the other is locally
constant on it. Since `H¹(A ∪ B) = 0` and `B ≅ N × ℝ` is preconnected, this function is the
restriction of a locally constant function on `A` plus a constant
(`TauCeti.deRhamCohomology.exists_locallyConstant_eq_inclusion_add_const`), and that function
takes different values on the two sides, so `A` is not preconnected.

If moreover `M` is connected and boundaryless, the complement has at most two components, the
components of the two sides (`TauCeti.IsBicollar.compl_range_eq_union_connectedComponentIn`), so it
has exactly two: they are open, connected and disjoint, contain one side each, cover the
complement, and have closures obtained by adding the image of `f`
(`TauCeti.IsBicollar.separates_of_subsingleton_deRhamCohomology_one`). This is the separation
theorem for compact connected two-sided hypersurfaces once a unit normal field has been turned into
a bicollar, the normal collar of the hypersurface. The case `M = ℝⁿ` is the separation half of the
Jordan–Brouwer theorem for such hypersurfaces.

The Hausdorff hypothesis cannot be dropped. On the line with two origins `0₁` and `0₂`, a smooth
form is determined by its restriction to either copy of `ℝ`, so the first de Rham cohomology
vanishes; the point `0₁` is closed and bicollared by the first copy of `ℝ`, but its complement is
homeomorphic to `ℝ` (with `0₂` in place of `0₁`) and so is connected.

## Main results

* `TauCeti.IsBicollar.not_isPreconnected_compl_range`: with `H¹_dR(M) = 0`, a bicollared map with
  closed image and preconnected nonempty domain disconnects `M`.
* `TauCeti.IsBicollar.disjoint_connectedComponentIn_compl_range`: the components of the complement
  containing the two sides of the bicollar are disjoint.
* `TauCeti.IsBicollar.separates_of_subsingleton_deRhamCohomology_one`: in a connected boundaryless
  manifold, the complement has exactly these two components, with closures obtained by adding the
  image.

## References

* E. L. Lima, *The Jordan–Brouwer separation theorem for smooth hypersurfaces*, Amer. Math.
  Monthly 95 (1988), 39–42.
* R. Bott and L. W. Tu, *Differential Forms in Algebraic Topology*, GTM 82, Chapter I, §2 and §5.
-/

public section

noncomputable section

open Set TopologicalSpace
open scoped Manifold ContDiff

namespace TauCeti

namespace IsBicollar

variable {E H M N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M] [TopologicalSpace N]
  {f : N → M} {b : N × ℝ → M}

/-- **A bicollared hypersurface disconnects a manifold with `H¹_dR = 0`.** If `f : N → M` has
closed image and a bicollar `b`, `N` is preconnected and nonempty, and the first de Rham cohomology
of `M` vanishes, then the complement of the image of `f` is not preconnected. -/
theorem not_isPreconnected_compl_range (hH : Subsingleton (deRhamCohomology I M 1))
    [PreconnectedSpace N] [Nonempty N] (h : IsBicollar f b) (hclosed : IsClosed (range f)) :
    ¬IsPreconnected (range f)ᶜ := by
  intro hconn
  let A : Opens M := ⟨(range f)ᶜ, hclosed.isOpen_compl⟩
  let B : Opens M := ⟨range b, h.isOpenEmbedding.isOpen_range⟩
  have hAB : A ⊔ B = ⊤ := by
    refine eq_top_iff.2 fun x _ ↦ ?_
    by_cases hx : x ∈ range f
    · exact Or.inr (h.range_subset_range hx)
    · exact Or.inl hx
  have hH' : Subsingleton (deRhamCohomology I (A ⊔ B : Opens M) 1) :=
    (deRhamCohomology.equivOfDiffeomorph (Diffeomorph.ofTop (I := I) (n := ∞) _ hAB)
      1).symm.toEquiv.subsingleton
  have : PreconnectedSpace B :=
    Subtype.preconnectedSpace (isPreconnected_range h.isOpenEmbedding.continuous)
  -- The positive side, read in `A ⊓ B`, is clopen there: its complement is the negative side.
  set P := b '' (univ ×ˢ Ioi (0 : ℝ))
  set Q := b '' (univ ×ˢ Iio (0 : ℝ))
  have hP : IsOpen P := h.isOpenEmbedding.isOpenMap _ (isOpen_univ.prod isOpen_Ioi)
  have hQ : IsOpen Q := h.isOpenEmbedding.isOpenMap _ (isOpen_univ.prod isOpen_Iio)
  have hPQ : ∀ x : (A ⊓ B : Opens M), (x : M) ∈ P ∨ (x : M) ∈ Q := fun x ↦
    h.range_diff_range_eq_union.subset ⟨x.property.2, x.property.1⟩
  let S : Set (A ⊓ B : Opens M) := {x | (x : M) ∈ P}
  have hS : IsClopen S := by
    refine ⟨isOpen_compl_iff.1 ?_, hP.preimage continuous_subtypeVal⟩
    convert hQ.preimage continuous_subtypeVal using 1
    ext x
    exact ⟨fun hx ↦ (hPQ x).resolve_left hx, fun hx hxP ↦
      disjoint_left.1 h.disjoint_image_Ioi_Iio hxP hx⟩
  classical
  let φ : LocallyConstant (A ⊓ B : Opens M) ℝ :=
    (LocallyConstant.ofIsClopen hS).map fun i : Fin 2 ↦ (i : ℝ)
  obtain ⟨g, c, hg⟩ :=
    deRhamCohomology.exists_locallyConstant_eq_inclusion_add_const hH' φ
  -- The locally constant function `g` on the preconnected `A` takes different values at a point
  -- of each side.
  have : PreconnectedSpace A := Subtype.preconnectedSpace hconn
  obtain ⟨a⟩ := ‹Nonempty N›
  have hmem : ∀ t : ℝ, t ≠ 0 → b (a, t) ∈ (A ⊓ B : Opens M) := fun t ht ↦
    ⟨by simpa [A, h.apply_mem_range_iff] using ht, mem_range_self _⟩
  have hpos := hg ⟨b (a, 1), hmem 1 one_ne_zero⟩
  have hneg := hg ⟨b (a, -1), hmem (-1) (by norm_num)⟩
  rw [g.apply_eq_of_preconnectedSpace _
    (Opens.inclusion inf_le_left ⟨b (a, 1), hmem 1 one_ne_zero⟩), ← hpos] at hneg
  have h1 : (b (a, 1)) ∈ P := mem_image_of_mem b ⟨mem_univ _, mem_Ioi.2 one_pos⟩
  have h2 : (b (a, -1)) ∉ P := fun hP' ↦
    disjoint_left.1 h.disjoint_image_Ioi_Iio hP'
      (mem_image_of_mem b ⟨mem_univ _, mem_Iio.2 (by norm_num)⟩)
  simp [φ, LocallyConstant.ofIsClopen, S, h1, h2] at hneg

/-- **The two sides of a bicollared hypersurface lie in different components.** Under the
hypotheses of `TauCeti.IsBicollar.not_isPreconnected_compl_range`, with `M` preconnected, the
components of the complement of the image containing the two sides of the bicollar are
disjoint. -/
theorem disjoint_connectedComponentIn_compl_range (hH : Subsingleton (deRhamCohomology I M 1))
    [PreconnectedSpace M] [PreconnectedSpace N] (h : IsBicollar f b)
    (hclosed : IsClosed (range f)) (a : N) :
    Disjoint (connectedComponentIn (range f)ᶜ (b (a, 1)))
      (connectedComponentIn (range f)ᶜ (b (a, -1))) := by
  have : Nonempty N := ⟨a⟩
  have hne := mt (h.isPreconnected_compl_range_iff a).2
    (h.not_isPreconnected_compl_range hH hclosed)
  refine disjoint_left.2 fun z hz₁ hz₂ ↦ hne ?_
  rw [connectedComponentIn_eq hz₁, connectedComponentIn_eq hz₂]

/-- **Separation theorem for bicollared hypersurfaces.** Let `M` be a connected boundaryless
manifold with `H¹_dR(M) = 0`, and let `f : N → M` have closed image and a bicollar `b`, with `N`
preconnected. Then the complement of the image of `f` has exactly two components, those of the
points `b (a, 1)` and `b (a, -1)` for any `a : N`: they are open, connected and disjoint, cover
the complement, contain the positive and the negative side of the bicollar respectively, and the
closure of each is itself together with the image of `f`. -/
theorem separates_of_subsingleton_deRhamCohomology_one [I.Boundaryless] [ConnectedSpace M]
    (hH : Subsingleton (deRhamCohomology I M 1)) [PreconnectedSpace N] (h : IsBicollar f b)
    (hclosed : IsClosed (range f)) (a : N) :
    letI A := connectedComponentIn (range f)ᶜ (b (a, 1))
    letI B := connectedComponentIn (range f)ᶜ (b (a, -1))
    IsOpen A ∧ IsOpen B ∧ IsConnected A ∧ IsConnected B ∧ Disjoint A B ∧
      A ∪ B = (range f)ᶜ ∧ b '' (univ ×ˢ Ioi 0) ⊆ A ∧ b '' (univ ×ˢ Iio 0) ⊆ B ∧
      closure A = A ∪ range f ∧ closure B = B ∪ range f := by
  have : LocallyConnectedSpace H := I.toHomeomorph.locallyConnectedSpace
  have : LocallyConnectedSpace M := ChartedSpace.locallyConnectedSpace H M
  have hp : b (a, 1) ∈ (range f)ᶜ := by simp [h.apply_mem_range_iff]
  have hm : b (a, -1) ∈ (range f)ᶜ := by simp [h.apply_mem_range_iff]
  exact ⟨hclosed.isOpen_compl.connectedComponentIn, hclosed.isOpen_compl.connectedComponentIn,
    isConnected_connectedComponentIn_iff.2 hp, isConnected_connectedComponentIn_iff.2 hm,
    h.disjoint_connectedComponentIn_compl_range hH hclosed a,
    (h.compl_range_eq_union_connectedComponentIn a).symm,
    h.image_subset_connectedComponentIn isPreconnected_Ioi (lt_irrefl 0) a (mem_Ioi.2 one_pos),
    h.image_subset_connectedComponentIn isPreconnected_Iio (lt_irrefl 0) a
      (mem_Iio.2 (by norm_num)),
    h.closure_connectedComponentIn_compl_range_apply a one_ne_zero,
    h.closure_connectedComponentIn_compl_range_apply a (by norm_num)⟩

end IsBicollar

end TauCeti
