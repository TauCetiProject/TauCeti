/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.SmoothEmbedding.Complement
public import TauCeti.KnotTheory.SmoothLink.Basic

/-!
# The complement of a smooth link

A smooth link `L` in a Hausdorff manifold `M` is a finite union of embedded circles, so the subset
`L.range` it occupies is compact, hence closed (`TauCeti.SmoothLinkEmbedding.isClosed_range`), and
its complement `M ∖ L` is an open subset of `M` (`TauCeti.SmoothLinkEmbedding.complement`). As an
open subset it is a smooth manifold over the model of `M`, boundaryless when `M` is
(`ModelWithCorners.BoundarylessManifold.open`); for a link in `S³` it is the link complement, a
boundaryless `3`-manifold. The complement of a link is the intersection of the complements of its
components (`TauCeti.SmoothLinkEmbedding.complement_eq_iInf`); the complement of a one-component
link is the complement of its circle embedding
(`TauCeti.SmoothLinkEmbedding.complement_singleton`), and the complement does not see the
labelling, the parametrisations or the orientations of the components.

A diffeomorphism of the ambient manifolds mapping the subset occupied by one link onto the subset
occupied by another restricts to a diffeomorphism of their complements
(`TauCeti.SmoothLinkEmbedding.complementDiffeomorph`). The two links may have different numbers of
components, and the diffeomorphism may permute, reparametrise or reverse them.

## Main definitions

* `TauCeti.SmoothLinkEmbedding.complement`: the complement of a smooth link, as an open subset.
* `TauCeti.SmoothLinkEmbedding.complementDiffeomorph`: the restriction to the complements of an
  ambient diffeomorphism mapping one link onto the other.

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

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H : Type*} [TopologicalSpace H] {H' : Type*} [TopologicalSpace H']
  {I : ModelWithCorners ℝ E H} {I' : ModelWithCorners ℝ E' H'}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  {P : Type*} [TopologicalSpace P] [ChartedSpace H' P] [T2Space P]
  {n m : ℕ} {k : ℕ∞ω}

namespace SmoothCircleEmbedding

/-- Rotating the parametrisation of a circle embedding does not change its complement. -/
@[simp]
theorem complement_rotate (f : SmoothCircleEmbedding I M) (a : Circle) :
    (f.rotate a).complement = f.complement :=
  Opens.ext (by simp)

/-- Reversing the orientation of a circle embedding does not change its complement. -/
@[simp]
theorem complement_reverse (f : SmoothCircleEmbedding I M) :
    f.reverse.complement = f.complement :=
  Opens.ext (by simp)

end SmoothCircleEmbedding

namespace SmoothLinkEmbedding

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

/-- The complement of a smooth link is the intersection of the complements of its components. -/
theorem complement_eq_iInf (L : SmoothLinkEmbedding I M n) :
    L.complement = ⨅ i, (L i).complement :=
  Opens.ext <| Set.ext fun y ↦ by simp [Opens.coe_iInf]

/-- The complement of a smooth link lies in the complement of each of its components. -/
theorem complement_le_component (L : SmoothLinkEmbedding I M n) (i : Fin n) :
    L.complement ≤ (L i).complement :=
  L.complement_eq_iInf.trans_le (iInf_le _ i)

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

/-- A diffeomorphism `e` mapping the subset occupied by the link `L` onto the subset occupied by
the link `K` maps a point into the complement of `K` exactly when the point lies in the complement
of `L`. -/
theorem apply_mem_complement_iff {L : SmoothLinkEmbedding I M n} {K : SmoothLinkEmbedding I' P m}
    (e : M ≃ₘ^k⟮I, I'⟯ P) (h : e '' L.range = K.range) (y : M) :
    e y ∈ K.complement ↔ y ∈ L.complement := by
  rw [mem_complement, mem_complement, ← h]
  exact not_congr (e.injective.mem_set_image (s := L.range))

/-- The **diffeomorphism of link complements** induced by an ambient diffeomorphism: a
diffeomorphism `e : M ≃ P` mapping the subset occupied by `L` onto the subset occupied by `K`
restricts to a diffeomorphism from the complement of `L` onto the complement of `K`. -/
def complementDiffeomorph {L : SmoothLinkEmbedding I M n} {K : SmoothLinkEmbedding I' P m}
    (e : M ≃ₘ^k⟮I, I'⟯ P) (h : e '' L.range = K.range) :
    L.complement ≃ₘ^k⟮I, I'⟯ K.complement :=
  e.subtype fun y ↦ (apply_mem_complement_iff e h y).symm

/-- The diffeomorphism of link complements is the ambient diffeomorphism. -/
@[simp]
theorem coe_complementDiffeomorph_apply {L : SmoothLinkEmbedding I M n}
    {K : SmoothLinkEmbedding I' P m} (e : M ≃ₘ^k⟮I, I'⟯ P) (h : e '' L.range = K.range)
    (y : L.complement) :
    (complementDiffeomorph e h y : P) = e y :=
  e.subtype_apply_coe _ y

/-- The inverse of the diffeomorphism of link complements is the inverse ambient
diffeomorphism. -/
@[simp]
theorem coe_complementDiffeomorph_symm_apply {L : SmoothLinkEmbedding I M n}
    {K : SmoothLinkEmbedding I' P m} (e : M ≃ₘ^k⟮I, I'⟯ P) (h : e '' L.range = K.range)
    (y : K.complement) :
    ((complementDiffeomorph e h).symm y : M) = e.symm y :=
  e.subtype_symm_apply_coe _ y

end SmoothLinkEmbedding

end TauCeti
