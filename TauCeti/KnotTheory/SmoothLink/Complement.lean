/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.SmoothEmbedding.SmoothAmbientIsotopy.Complement
public import TauCeti.KnotTheory.SmoothLink.Isotopy

/-!
# The complement of a smooth link

A smooth link `L` in a Hausdorff manifold `M` is a finite union of embedded circles, so the subset
`L.range` it occupies is compact, hence closed, and its complement `M ∖ L` is an open subset of `M`
(`TauCeti.SmoothLinkEmbedding.complement`). As an open subset it is a smooth manifold over the
model of `M`, boundaryless when `M` is (`BoundarylessManifold.open`); for a link in `S³` it is the
link complement, a boundaryless `3`-manifold. The complement of a one-component link is the
complement of its circle embedding (`TauCeti.SmoothLinkEmbedding.complement_singleton`), and the
complement does not see the labelling or the orientations of the components.

A diffeomorphism of the ambient manifolds carrying one link to another, component by component,
restricts to a diffeomorphism of their complements
(`TauCeti.SmoothLinkEmbedding.complementDiffeomorph`). Applied to the final diffeomorphism of the
shared diffeotopy, this shows that **smoothly ambient isotopic links have diffeomorphic
complements**
(`TauCeti.SmoothLinkEmbedding.SmoothAmbientIsotopic.nonempty_complementDiffeomorph`), the smooth
form of `TauCeti.SmoothLinkEmbedding.SmoothAmbientIsotopic.nonempty_complementHomeomorph`.

## Main definitions

* `TauCeti.SmoothLinkEmbedding.complement`: the complement of a smooth link, as an open subset.
* `TauCeti.SmoothLinkEmbedding.complementDiffeomorph`: the restriction to the complements of an
  ambient diffeomorphism carrying one link to the other.

## Main results

* `TauCeti.SmoothLinkEmbedding.isCompact_range`, `TauCeti.SmoothLinkEmbedding.isClosed_range`: a
  smooth link occupies a compact, and in a Hausdorff manifold closed, subset.
* `TauCeti.SmoothLinkEmbedding.SmoothAmbientIsotopic.nonempty_complementDiffeomorph`: smoothly
  ambient isotopic links have diffeomorphic complements.

## References

* G. Burde and H. Zieschang, *Knots*, 2nd ed., de Gruyter (2003), Chapter 1, for link
  complements as invariants of ambient isotopy.
* D. Rolfsen, *Knots and Links*, Publish or Perish (1976), Chapter 1.
-/

public section

noncomputable section

namespace TauCeti

open Set TopologicalSpace
open scoped _root_.Manifold ContDiff

namespace SmoothLinkEmbedding

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H : Type*} [TopologicalSpace H] {H' : Type*} [TopologicalSpace H']
  {I : ModelWithCorners ℝ E H} {I' : ModelWithCorners ℝ E' H'}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {P : Type*} [TopologicalSpace P] [ChartedSpace H' P]
  {n : ℕ} {k : ℕ∞ω}

/-- A smooth link occupies a compact subset of the ambient manifold: a finite union of circles. -/
theorem isCompact_range (L : SmoothLinkEmbedding I M n) : IsCompact L.range := by
  rw [← range_toContinuousMap]
  exact _root_.isCompact_range (map_continuous _)

/-- A smooth link in a Hausdorff manifold occupies a closed subset. -/
theorem isClosed_range [T2Space M] (L : SmoothLinkEmbedding I M n) : IsClosed L.range :=
  L.isCompact_range.isClosed

variable [T2Space M] [T2Space P]

/-- The **complement** of a smooth link `L` in a Hausdorff manifold `M`: the open subset `M ∖ L`
of the points lying on no component of `L`. -/
def complement (L : SmoothLinkEmbedding I M n) : Opens M :=
  ⟨L.rangeᶜ, L.isClosed_range.isOpen_compl⟩

/-- The complement of a smooth link, as a set, is the complement of the subset it occupies. -/
@[simp]
theorem coe_complement (L : SmoothLinkEmbedding I M n) : (L.complement : Set M) = L.rangeᶜ :=
  (rfl)

/-- A point lies in the complement of a smooth link exactly when it lies on no component. -/
@[simp]
theorem mem_complement {L : SmoothLinkEmbedding I M n} {y : M} :
    y ∈ L.complement ↔ y ∉ L.range :=
  Iff.rfl

/-- The complement of the empty link is the whole manifold. -/
@[simp]
theorem complement_empty : (empty (I := I) (M := M)).complement = ⊤ :=
  Opens.ext (by simp)

/-- The complement of a one-component link is the complement of its circle embedding. -/
@[simp]
theorem complement_singleton (f : SmoothCircleEmbedding I M) :
    (singleton f).complement = f.complement :=
  Opens.ext (by simp)

/-- Relabelling the components does not change the complement. -/
@[simp]
theorem complement_relabel (L : SmoothLinkEmbedding I M n) (e : Equiv.Perm (Fin n)) :
    (L.relabel e).complement = L.complement :=
  Opens.ext (by simp)

/-- Reversing the orientations of the components does not change the complement. -/
@[simp]
theorem complement_reverse (L : SmoothLinkEmbedding I M n) :
    L.reverse.complement = L.complement :=
  Opens.ext (by simp)

/-- A diffeomorphism `e` carrying every component of the link `L` to the corresponding component
of `K` maps a point into the complement of `K` exactly when the point lies in the complement of
`L`. -/
theorem apply_mem_complement_iff {L : SmoothLinkEmbedding I M n} {K : SmoothLinkEmbedding I' P n}
    (e : M ≃ₘ^k⟮I, I'⟯ P) (h : ∀ i x, e (L i x) = K i x) (y : M) :
    e y ∈ K.complement ↔ y ∈ L.complement := by
  simp only [mem_complement, mem_range_iff, not_exists]
  exact forall_congr' fun i ↦ forall_congr' fun x ↦ not_congr
    ⟨fun hx ↦ e.injective ((h i x).trans hx), fun hx ↦ (h i x).symm.trans (congrArg e hx)⟩

/-- The **diffeomorphism of link complements** induced by an ambient diffeomorphism: a
diffeomorphism `e : M ≃ P` carrying every component of `L` to the corresponding component of `K`
restricts to a diffeomorphism from the complement of `L` onto the complement of `K`. -/
def complementDiffeomorph {L : SmoothLinkEmbedding I M n} {K : SmoothLinkEmbedding I' P n}
    (e : M ≃ₘ^k⟮I, I'⟯ P) (h : ∀ i x, e (L i x) = K i x) :
    L.complement ≃ₘ^k⟮I, I'⟯ K.complement :=
  e.subtype fun y ↦ (apply_mem_complement_iff e h y).symm

/-- The diffeomorphism of link complements is the ambient diffeomorphism. -/
@[simp]
theorem coe_complementDiffeomorph_apply {L : SmoothLinkEmbedding I M n}
    {K : SmoothLinkEmbedding I' P n} (e : M ≃ₘ^k⟮I, I'⟯ P) (h : ∀ i x, e (L i x) = K i x)
    (y : L.complement) :
    (complementDiffeomorph e h y : P) = e y :=
  e.subtype_apply_coe _ y

/-- The inverse of the diffeomorphism of link complements is the inverse ambient
diffeomorphism. -/
@[simp]
theorem coe_complementDiffeomorph_symm_apply {L : SmoothLinkEmbedding I M n}
    {K : SmoothLinkEmbedding I' P n} (e : M ≃ₘ^k⟮I, I'⟯ P) (h : ∀ i x, e (L i x) = K i x)
    (y : K.complement) :
    ((complementDiffeomorph e h).symm y : M) = e.symm y :=
  e.subtype_symm_apply_coe _ y

/-- **Smoothly ambient isotopic links have diffeomorphic complements.** The final diffeomorphism
of a diffeotopy carrying every component of `L` to the corresponding component of `K` restricts to
a diffeomorphism from `M ∖ L` onto `M ∖ K`. -/
theorem SmoothAmbientIsotopic.nonempty_complementDiffeomorph {L K : SmoothLinkEmbedding I M n}
    (hLK : SmoothAmbientIsotopic L K) : Nonempty (L.complement ≃ₘ⟮I, I⟯ K.complement) := by
  obtain ⟨Φ, hΦ⟩ := smoothAmbientIsotopic_def.mp hLK
  exact ⟨complementDiffeomorph Φ.final hΦ⟩

end SmoothLinkEmbedding

end TauCeti
