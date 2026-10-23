/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.DualGraph.Cutting
public import TauCeti.AlgebraicGeometry.Curves.StableMaps.DualGraph.Basic

/-!
# Cutting nodes of degree-decorated dual graphs

Normalizing the source curve of a stable map at a set `S` of nodes, and composing with the map,
gives a family of stable maps indexed by the connected pieces of the partial normalization. Each
piece carries the original markings on it together with one new marking for each branch of a cut
node, and the map on every component is unchanged. The dual graphs of the pieces are
`TauCeti.DualGraph.cutComponent`; this file carries the component degrees along.

A decoration of `G` restricts to a decoration of every piece, and conversely the decorations of
the pieces determine a unique decoration of `G`, since every component of `G` lies on exactly one
piece. The total degrees of the pieces add up to the total degree of `G`. Since cutting with
branch markings preserves every log-canonical degree, it preserves every weighted log-canonical
degree, so all pieces are stable exactly when the original decorated graph is. Summing the
weighted degrees over the pieces gives the numerical reconstruction of the type: if the piece `x`
has genus `gₓ`, `nₓ` markings and total degree `dₓ`, then

`∑ₓ (2gₓ - 2 + nₓ + 3dₓ) = 2g - 2 + n + 3d`.

## Main definitions

* `TauCeti.DualGraph.DegreeDecoration.cutComponent`: the decoration of a piece of a partial
  normalization, with the same component degrees.
* `TauCeti.DualGraph.DegreeDecoration.cutComponentAddEquiv`: decorations of `G` are exactly
  families of decorations of the pieces of its partial normalization at `S`.

## Main results

* `TauCeti.DualGraph.DegreeDecoration.sum_totalDegree_cutComponent`: the total degrees of the
  pieces add up to the total degree.
* `TauCeti.DualGraph.DegreeDecoration.forall_isStable_cutComponent_iff`: all pieces are stable
  exactly when the original decorated graph is.
* `sum_two_mul_arithmeticGenus_sub_two_add_card_add_three_mul_totalDegree_cutComponent` (in
  `TauCeti.DualGraph.DegreeDecoration`): the numerical types of the pieces satisfy
  `∑ₓ (2gₓ - 2 + nₓ + 3dₓ) = 2g - 2 + n + 3d`.

## References

* K. Behrend and Yu. Manin, *Stacks of stable maps and Gromov--Witten invariants*, Duke Math. J.
  85 (1996), 1--60, Sections 1 and 2, for modular graphs of stable maps.
* E. Arbarello, M. Cornalba and P. A. Griffiths, *Geometry of Algebraic Curves, Volume II*,
  Chapter X, for partial normalization and dual graphs of nodal curves.
-/

public section

namespace TauCeti

namespace DualGraph

namespace DegreeDecoration

open Finset

universe u v

variable {ι : Type v} {G : DualGraph.{u} ι} (S : Finset G.Edge) (D D' : G.DegreeDecoration)

/-- The degree decoration of the piece `x` of the partial normalization of `G` at `S`, with the
same component degrees as `D`. -/
def cutComponent (x : (G.smoothing Sᶜ).Vertex) : (G.cutComponent S x).DegreeDecoration :=
  ⟨fun v ↦ D.componentDegree v.1⟩

@[simp]
lemma componentDegree_cutComponent (x : (G.smoothing Sᶜ).Vertex)
    (v : (G.cutComponent S x).Vertex) :
    (D.cutComponent S x).componentDegree v = D.componentDegree v.1 :=
  (rfl)

/-- A decoration is determined by its restrictions to the pieces of a partial normalization. -/
@[simp]
theorem cutComponent_inj :
    (∀ x, D.cutComponent S x = D'.cutComponent S x) ↔ D = D' := by
  refine ⟨fun h ↦ DegreeDecoration.ext <| funext fun v ↦ ?_, fun h _ ↦ h ▸ rfl⟩
  have h' := congrArg (fun E ↦ E.componentDegree ⟨v, rfl⟩) (h (G.smoothingVertex Sᶜ v))
  simpa using h'

/-- Cutting a constant map gives constant maps. -/
@[simp]
lemma cutComponent_zero (x : (G.smoothing Sᶜ).Vertex) :
    (0 : G.DegreeDecoration).cutComponent S x = 0 :=
  (rfl)

@[simp]
lemma cutComponent_add (x : (G.smoothing Sᶜ).Vertex) :
    (D + D').cutComponent S x = D.cutComponent S x + D'.cutComponent S x :=
  (rfl)

@[simp]
lemma cutComponent_smul (m : ℕ) (x : (G.smoothing Sᶜ).Vertex) :
    (m • D).cutComponent S x = m • D.cutComponent S x :=
  (rfl)

variable (G) in
/-- **Reconstruction of the component degrees.** Decorations of `G` are exactly families of
decorations of the pieces of its partial normalization at `S`. -/
def cutComponentAddEquiv :
    G.DegreeDecoration ≃+ ∀ x : (G.smoothing Sᶜ).Vertex, (G.cutComponent S x).DegreeDecoration where
  toFun D x := D.cutComponent S x
  invFun D := ⟨fun v ↦ (D (G.smoothingVertex Sᶜ v)).componentDegree ⟨v, rfl⟩⟩
  left_inv _ := rfl
  right_inv D := funext fun x ↦ DegreeDecoration.ext <| funext fun ⟨v, hv⟩ ↦ by
    subst hv
    rfl
  map_add' D D' := funext fun x ↦ cutComponent_add S D D' x

@[simp]
lemma cutComponentAddEquiv_apply (x : (G.smoothing Sᶜ).Vertex) :
    cutComponentAddEquiv G S D x = D.cutComponent S x :=
  (rfl)

@[simp]
lemma componentDegree_cutComponentAddEquiv_symm_apply
    (D : ∀ x : (G.smoothing Sᶜ).Vertex, (G.cutComponent S x).DegreeDecoration) (v : G.Vertex) :
    ((cutComponentAddEquiv G S).symm D).componentDegree v =
      (D (G.smoothingVertex Sᶜ v)).componentDegree ⟨v, rfl⟩ :=
  (rfl)

/-- A sum over the vertices of all pieces of a partial normalization is a sum over the vertices
of `G`. -/
private lemma sum_sum_vertex_cutComponent {M : Type*} [AddCommMonoid M] (f : G.Vertex → M) :
    ∑ x : (G.smoothing Sᶜ).Vertex, ∑ v : (G.cutComponent S x).Vertex, f v.1 = ∑ v, f v := by
  rw [← Fintype.sum_sigma (fun p : Σ x, (G.cutComponent S x).Vertex ↦ f p.2.1)]
  rw [← (G.sigmaVertexCutComponentEquiv S).sum_comp f]
  exact sum_congr rfl fun p _ ↦ by rw [sigmaVertexCutComponentEquiv_apply]

/-- The total degrees of the pieces of a partial normalization add up to the total degree. -/
@[simp]
theorem sum_totalDegree_cutComponent :
    ∑ x : (G.smoothing Sᶜ).Vertex, (D.cutComponent S x).totalDegree = D.totalDegree := by
  simp only [totalDegree_def, componentDegree_cutComponent]
  exact sum_sum_vertex_cutComponent S D.componentDegree

variable [Fintype ι]

/-- Cutting with branch markings preserves every weighted log-canonical degree. -/
@[simp]
theorem weightedLogCanonicalDegree_cutComponent (x : (G.smoothing Sᶜ).Vertex)
    (v : (G.cutComponent S x).Vertex) :
    (D.cutComponent S x).weightedLogCanonicalDegree v = D.weightedLogCanonicalDegree v.1 := by
  rw [weightedLogCanonicalDegree_def, weightedLogCanonicalDegree_def,
    logCanonicalDegree_cutComponent, componentDegree_cutComponent]

/-- All pieces of a partial normalization of a decorated graph are stable exactly when the
decorated graph is. -/
@[simp]
theorem forall_isStable_cutComponent_iff :
    (∀ x : (G.smoothing Sᶜ).Vertex, (D.cutComponent S x).IsStable) ↔ D.IsStable := by
  simp only [isStable_iff_weightedLogCanonicalDegree_pos, weightedLogCanonicalDegree_cutComponent]
  exact ⟨fun h v ↦ h (G.smoothingVertex Sᶜ v) ⟨v, rfl⟩, fun h _ v ↦ h v.1⟩

/-- **The numerical types of the pieces.** If the piece `x` of the partial normalization at `S`
has genus `gₓ`, `nₓ` markings (the original ones on it and the branches of the cut nodes) and total
degree `dₓ`, then `∑ₓ (2gₓ - 2 + nₓ + 3dₓ) = 2g - 2 + n + 3d`. -/
theorem sum_two_mul_arithmeticGenus_sub_two_add_card_add_three_mul_totalDegree_cutComponent :
    ∑ x : (G.smoothing Sᶜ).Vertex,
        (2 * ((G.cutComponent S x).arithmeticGenus : ℤ) - 2 +
          Fintype.card {i : ι ⊕ (S × Fin 2) // G.smoothingVertex Sᶜ (G.cutMarking S i) = x} +
          3 * (D.cutComponent S x).totalDegree) =
      2 * G.arithmeticGenus - 2 + Fintype.card ι + 3 * D.totalDegree := by
  simp_rw [← sum_weightedLogCanonicalDegree, weightedLogCanonicalDegree_cutComponent]
  exact sum_sum_vertex_cutComponent S D.weightedLogCanonicalDegree

end DegreeDecoration

end DualGraph

end TauCeti
