/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.DualGraph.Iso
public import TauCeti.AlgebraicGeometry.Curves.StableMaps.DualGraph.Basic

/-!
# Moving degree decorations along isomorphisms of dual graphs

An isomorphism `f : G.Iso H` of dual graphs carries a degree decoration of `G` to one of `H`, by
giving the component `f.vertexEquiv v` the degree of `v`. Since `f` preserves log-canonical
degrees, the moved decoration has the same total degree and is stable exactly when the original
one is.

## Main definitions

* `TauCeti.DualGraph.DegreeDecoration.transport`: the decoration of `H` obtained from a
  decoration of `G` along `f : G.Iso H`.

## Main results

* `TauCeti.DualGraph.DegreeDecoration.eq_transport_iff`: the moved decoration is characterized by
  its component degrees at the images `f.vertexEquiv v`.
* `TauCeti.DualGraph.DegreeDecoration.totalDegree_transport`: moving a decoration preserves its
  total degree.
* `TauCeti.DualGraph.DegreeDecoration.isStable_transport_iff`: moving a decoration preserves
  stability.

## References

* W. Fulton and R. Pandharipande, *Notes on stable maps and quantum cohomology*, Proc. Sympos.
  Pure Math. 62 (1997), Part 2, 45--96, Section 1, on degree-decorated graphs of stable maps.
-/

public section

namespace TauCeti

namespace DualGraph

namespace DegreeDecoration

open Finset

universe u u' u'' v

variable {ι : Type v} {G : DualGraph.{u} ι} {H : DualGraph.{u'} ι} {K : DualGraph.{u''} ι}
  (D : G.DegreeDecoration) (f : G.Iso H)

/-- The decoration of `H` obtained by moving `D` along the isomorphism `f : G.Iso H`: the
component `f.vertexEquiv v` gets the degree of `v`. -/
def transport : H.DegreeDecoration :=
  ⟨fun w ↦ D.componentDegree (f.vertexEquiv.symm w)⟩

lemma componentDegree_transport (w : H.Vertex) :
    (D.transport f).componentDegree w = D.componentDegree (f.vertexEquiv.symm w) :=
  (rfl)

@[simp]
lemma componentDegree_transport_vertexEquiv (v : G.Vertex) :
    (D.transport f).componentDegree (f.vertexEquiv v) = D.componentDegree v := by
  simp [componentDegree_transport]

/-- A decoration of `H` is the one moved from `D` along `f` exactly when `f` carries each
component degree of `D` to it. -/
theorem eq_transport_iff {D' : H.DegreeDecoration} :
    D' = D.transport f ↔ ∀ v, D'.componentDegree (f.vertexEquiv v) = D.componentDegree v := by
  refine ⟨fun h v ↦ h ▸ D.componentDegree_transport_vertexEquiv f v, fun h ↦ ?_⟩
  ext w
  rw [componentDegree_transport, ← h, Equiv.apply_symm_apply]

/-- Moving a decoration along the identity isomorphism does not change it. -/
@[simp]
theorem transport_refl : D.transport (Iso.refl G) = D := by
  ext
  simp [componentDegree_transport]

/-- Moving a decoration along a composite isomorphism is moving it along each in turn. -/
@[simp]
theorem transport_trans (g : H.Iso K) : D.transport (f.trans g) = (D.transport f).transport g := by
  ext
  simp [componentDegree_transport]

/-- Moving a decoration along an isomorphism and back recovers it. -/
@[simp]
theorem transport_symm_transport : (D.transport f).transport f.symm = D := by
  ext
  simp [componentDegree_transport]

/-- Moving a decoration back along an isomorphism and then forward recovers it. -/
@[simp]
theorem transport_transport_symm (D : H.DegreeDecoration) :
    (D.transport f.symm).transport f = D := by
  ext
  simp [componentDegree_transport]

/-- Moving a decoration along an isomorphism preserves its total degree. -/
@[simp]
theorem totalDegree_transport : (D.transport f).totalDegree = D.totalDegree := by
  rw [totalDegree_def, totalDegree_def, ← f.vertexEquiv.sum_comp]
  simp

/-- Moving a decoration along an isomorphism preserves stability. -/
@[simp]
theorem isStable_transport_iff [Fintype ι] : (D.transport f).IsStable ↔ D.IsStable := by
  simp only [isStable_iff, ← f.vertexEquiv.forall_congr_right,
    componentDegree_transport_vertexEquiv, Iso.logCanonicalDegree_vertexEquiv]

end DegreeDecoration

end DualGraph

end TauCeti
