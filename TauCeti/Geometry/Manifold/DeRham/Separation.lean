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
(`TauCeti.IsBicollar f b`) into a smooth manifold `M` with `H¹_dR(M) = 0`. Then for every `a : N`
the points `b (a, 1)` and `b (a, -1)` on the two sides of the bicollar lie in different components
of the complement of the image of `f`
(`TauCeti.IsBicollar.disjoint_connectedComponentIn_compl_range_of_subsingleton_deRhamCohomology`),
so for nonempty `N` the complement is not preconnected
(`TauCeti.IsBicollar.not_isPreconnected_compl_range`). The proof is the degree-zero end of the
Mayer–Vietoris sequence for the cover of `M` by the open sets `A = M \ range f` and `B = range b`.
The intersection `A ∩ B` is the union of the two disjoint open sides `b (N × (0, ∞))` and
`b (N × (-∞, 0))`, and the indicator function of one side is locally constant on it. Since
`H¹(A ∪ B) = 0`, this function is `g - k` on `A ∩ B` for locally constant functions `g` on `A` and
`k` on `B` (`TauCeti.deRhamCohomology.exists_locallyConstant_eq_inclusion_sub_inclusion`). The
function `k` is constant along the line `t ↦ b (a, t)` in `B`, so `g` takes different values at
`b (a, 1)` and `b (a, -1)`, and these points lie in different components of `A`.

If moreover `M` is preconnected and `N` is nonempty and preconnected, the complement has at most
two components, the components of the two sides
(`TauCeti.IsBicollar.compl_range_eq_union_connectedComponentIn`), so it has exactly two: they are
open, connected and disjoint, contain one side each, cover the complement, and have closures
obtained by adding the image of `f`
(`TauCeti.IsBicollar.separates_of_subsingleton_deRhamCohomology_one`). This is the separation
theorem for compact connected two-sided hypersurfaces once a unit normal field has been turned into
a bicollar, the normal collar of the hypersurface. The case `M = ℝⁿ` is the separation half of the
Jordan–Brouwer theorem for such hypersurfaces.

The Hausdorff hypothesis cannot be dropped. On the line with two origins `0₁` and `0₂`, a smooth
form is determined by its restriction to either copy of `ℝ`, so the first de Rham cohomology
vanishes; the point `0₁` is closed and bicollared by the first copy of `ℝ`, but its complement is
homeomorphic to `ℝ` (with `0₂` in place of `0₁`) and so is connected.

## Main results

* `TauCeti.IsBicollar.disjoint_connectedComponentIn_compl_range_of_subsingleton_deRhamCohomology`:
  with `H¹_dR(M) = 0` and closed image, the components of the complement containing the two sides
  of the bicollar are disjoint.
* `TauCeti.IsBicollar.not_isPreconnected_compl_range`: with `H¹_dR(M) = 0`, a bicollared map with
  closed image and nonempty domain disconnects `M`.
* `TauCeti.IsBicollar.separates_of_subsingleton_deRhamCohomology_one`: in a preconnected manifold,
  for a nonempty preconnected domain, the complement has exactly these two components, with closures
  obtained by adding the image.

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

/-- With `H¹_dR(M) = 0`, a locally constant function on the complement of the image of a
bicollared map with closed image separates the two sides of the bicollar. -/
private theorem exists_locallyConstant_apply_ne (hH : Subsingleton (deRhamCohomology I M 1))
    (h : IsBicollar f b) (hclosed : IsClosed (range f)) (a : N) :
    ∃ g : LocallyConstant ((range f)ᶜ : Set M) ℝ, ∀ (hp : b (a, 1) ∈ (range f)ᶜ)
      (hm : b (a, -1) ∈ (range f)ᶜ), g ⟨b (a, 1), hp⟩ ≠ g ⟨b (a, -1), hm⟩ := by
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
  -- The positive side, read in `A ⊓ B`, is clopen there: its complement is the negative side.
  set P := b '' (univ ×ˢ Ioi (0 : ℝ))
  have hP : IsOpen P := h.isOpenEmbedding.isOpenMap _ (isOpen_univ.prod isOpen_Ioi)
  have hQ : IsOpen (b '' (univ ×ˢ Iio (0 : ℝ))) :=
    h.isOpenEmbedding.isOpenMap _ (isOpen_univ.prod isOpen_Iio)
  let S : Set (A ⊓ B : Opens M) := {x | (x : M) ∈ P}
  have hS : IsClopen S := by
    refine ⟨isOpen_compl_iff.1 ?_, hP.preimage continuous_subtypeVal⟩
    convert hQ.preimage continuous_subtypeVal using 1
    ext x
    exact ⟨fun hx ↦ (h.range_diff_range_eq_union.subset ⟨x.property.2, x.property.1⟩).resolve_left
      hx, fun hx hxP ↦ disjoint_left.1 h.disjoint_image_Ioi_Iio hxP hx⟩
  classical
  let φ : LocallyConstant (A ⊓ B : Opens M) ℝ :=
    (LocallyConstant.ofIsClopen hS).map fun i : Fin 2 ↦ (i : ℝ)
  -- `φ` is `0` on the positive side and `1` on the negative side, i.e. the indicator of the
  -- negative side; it is `g - k` for locally constant `g` on `A` and `k` on `B`.
  obtain ⟨g, k, hg⟩ :=
    deRhamCohomology.exists_locallyConstant_eq_inclusion_sub_inclusion hH' φ
  have hφS : ∀ x ∈ S, φ x = 0 := fun x hx ↦ by
    have : LocallyConstant.ofIsClopen hS x = 0 := by
      rwa [← mem_singleton_iff, ← mem_preimage, LocallyConstant.ofIsClopen_fiber_zero]
    simp [φ, this]
  have hφSc : ∀ x ∉ S, φ x = 1 := fun x hx ↦ by
    have : LocallyConstant.ofIsClopen hS x = 1 := by
      rwa [← mem_singleton_iff, ← mem_preimage, LocallyConstant.ofIsClopen_fiber_one]
    simp [φ, this]
  have hmem : ∀ t : ℝ, t ≠ 0 → b (a, t) ∈ (A ⊓ B : Opens M) := fun t ht ↦
    ⟨h.apply_mem_compl_range a ht, mem_range_self _⟩
  have h1 : (b (a, 1)) ∈ P := mem_image_of_mem b ⟨mem_univ _, mem_Ioi.2 one_pos⟩
  have h2 : (b (a, -1)) ∉ P := fun hP' ↦
    disjoint_left.1 h.disjoint_image_Ioi_Iio hP'
      (mem_image_of_mem b ⟨mem_univ _, mem_Iio.2 (by norm_num)⟩)
  have hpos : (0 : ℝ) = g ⟨b (a, 1), (hmem 1 one_ne_zero).1⟩ - k ⟨b (a, 1), mem_range_self _⟩ := by
    rw [← hg ⟨b (a, 1), hmem 1 one_ne_zero⟩, hφS _ h1]
  have hneg : (1 : ℝ) =
      g ⟨b (a, -1), (hmem (-1) (by norm_num)).1⟩ - k ⟨b (a, -1), mem_range_self _⟩ := by
    rw [← hg ⟨b (a, -1), hmem (-1) (by norm_num)⟩, hφSc _ h2]
  -- `k` is constant along the line `t ↦ b (a, t)` in `B`.
  have hk : k ⟨b (a, 1), mem_range_self _⟩ = k ⟨b (a, -1), mem_range_self _⟩ :=
    k.apply_eq_of_isPreconnected (isPreconnected_range (f := fun t : ℝ ↦
      (⟨b (a, t), mem_range_self _⟩ : B))
      ((h.isOpenEmbedding.continuous.comp (continuous_const.prodMk continuous_id)).subtype_mk _))
      ⟨1, rfl⟩ ⟨-1, rfl⟩
  exact ⟨g, fun _ _ ↦ by intro hne; linarith⟩

/-- **The two sides of a bicollared hypersurface lie in different components.** If `f : N → M`
has closed image and a bicollar `b`, and the first de Rham cohomology of `M` vanishes, then for
every `a : N` the components of the complement of the image of `f` containing `b (a, 1)` and
`b (a, -1)` are disjoint. -/
theorem disjoint_connectedComponentIn_compl_range_of_subsingleton_deRhamCohomology
    (hH : Subsingleton (deRhamCohomology I M 1)) (h : IsBicollar f b)
    (hclosed : IsClosed (range f)) (a : N) :
    Disjoint (connectedComponentIn (range f)ᶜ (b (a, 1)))
      (connectedComponentIn (range f)ᶜ (b (a, -1))) := by
  have hp : b (a, 1) ∈ (range f)ᶜ := h.apply_mem_compl_range a one_ne_zero
  have hm : b (a, -1) ∈ (range f)ᶜ := h.apply_mem_compl_range a (neg_ne_zero.2 one_ne_zero)
  obtain ⟨g, hg⟩ := exists_locallyConstant_apply_ne hH h hclosed a
  refine disjoint_left.2 fun z hz₁ hz₂ ↦ hg hp hm ?_
  -- `b (a, -1)` would lie in the component of `b (a, 1)`, on which `g` is constant.
  have hm' : b (a, -1) ∈ connectedComponentIn (range f)ᶜ (b (a, 1)) := by
    rw [connectedComponentIn_eq hz₁, ← connectedComponentIn_eq hz₂]
    exact mem_connectedComponentIn hm
  rw [connectedComponentIn_eq_image hp] at hm'
  obtain ⟨y, hy, hyv⟩ := hm'
  rw [g.apply_eq_of_isPreconnected isPreconnected_connectedComponent mem_connectedComponent hy]
  exact congrArg g (Subtype.ext hyv)

/-- **A bicollared hypersurface disconnects a manifold with `H¹_dR = 0`.** If `f : N → M` has
closed image and a bicollar `b`, `N` is nonempty, and the first de Rham cohomology of `M`
vanishes, then the complement of the image of `f` is not preconnected. -/
theorem not_isPreconnected_compl_range (hH : Subsingleton (deRhamCohomology I M 1))
    [Nonempty N] (h : IsBicollar f b) (hclosed : IsClosed (range f)) :
    ¬IsPreconnected (range f)ᶜ := by
  intro hconn
  obtain ⟨a⟩ := ‹Nonempty N›
  have hm := h.apply_mem_compl_range a (neg_ne_zero.2 one_ne_zero)
  refine disjoint_left.1
    (h.disjoint_connectedComponentIn_compl_range_of_subsingleton_deRhamCohomology hH hclosed a)
    (hconn.subset_connectedComponentIn (h.apply_mem_compl_range a one_ne_zero) subset_rfl hm)
    (mem_connectedComponentIn hm)

/-- **Separation theorem for bicollared hypersurfaces.** Let `M` be a preconnected manifold with
`H¹_dR(M) = 0`, and let `f : N → M` have closed image and a bicollar `b`, with `N` preconnected.
Then the complement of the image of `f` has exactly two components, those of the points
`b (a, 1)` and `b (a, -1)` for any `a : N`: they are open, connected and disjoint, cover the
complement, contain the positive and the negative side of the bicollar respectively, and the
closure of each is itself together with the image of `f`. -/
theorem separates_of_subsingleton_deRhamCohomology_one [PreconnectedSpace M]
    (hH : Subsingleton (deRhamCohomology I M 1)) [PreconnectedSpace N] (h : IsBicollar f b)
    (hclosed : IsClosed (range f)) (a : N) :
    letI A := connectedComponentIn (range f)ᶜ (b (a, 1))
    letI B := connectedComponentIn (range f)ᶜ (b (a, -1))
    IsOpen A ∧ IsOpen B ∧ IsConnected A ∧ IsConnected B ∧ Disjoint A B ∧
      A ∪ B = (range f)ᶜ ∧ b '' (univ ×ˢ Ioi 0) ⊆ A ∧ b '' (univ ×ˢ Iio 0) ⊆ B ∧
      closure A = A ∪ range f ∧ closure B = B ∪ range f := by
  have hp : b (a, 1) ∈ (range f)ᶜ := h.apply_mem_compl_range a one_ne_zero
  have hm : b (a, -1) ∈ (range f)ᶜ := h.apply_mem_compl_range a (neg_ne_zero.2 one_ne_zero)
  have hd := h.disjoint_connectedComponentIn_compl_range_of_subsingleton_deRhamCohomology hH
    hclosed a
  have hu := (h.compl_range_eq_union_connectedComponentIn a).symm
  have hcA := h.closure_connectedComponentIn_compl_range_apply a one_ne_zero
  have hcB := h.closure_connectedComponentIn_compl_range_apply a (t := -1) (by norm_num)
  -- Each component is the complement of the closure of the other in the open set `(range f)ᶜ`.
  have hopen {C D : Set M} (hCD : Disjoint C D) (hCDu : C ∪ D = (range f)ᶜ)
      (hD : closure D = D ∪ range f) : IsOpen C := by
    convert hclosed.isOpen_compl.inter isClosed_closure.isOpen_compl using 1
    rw [hD, compl_union, ← hCDu]
    ext x
    simp only [mem_inter_iff, mem_compl_iff, mem_union]
    exact ⟨fun hx ↦ ⟨Or.inl hx, disjoint_left.1 hCD hx, Or.inl hx⟩,
      fun ⟨hx, hxD, _⟩ ↦ hx.resolve_right hxD⟩
  exact ⟨hopen hd hu hcB, hopen hd.symm (union_comm _ _ ▸ hu) hcA,
    isConnected_connectedComponentIn_iff.2 hp, isConnected_connectedComponentIn_iff.2 hm, hd, hu,
    h.image_subset_connectedComponentIn isPreconnected_Ioi (lt_irrefl 0) a (mem_Ioi.2 one_pos),
    h.image_subset_connectedComponentIn isPreconnected_Iio (lt_irrefl 0) a
      (mem_Iio.2 (by norm_num)), hcA, hcB⟩

end IsBicollar

end TauCeti
