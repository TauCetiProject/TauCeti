/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Geometry.Symplectic.Lagrangian
public import TauCeti.Geometry.Symplectic.SymplecticTransport

/-!
# Transporting isotropic and Lagrangian subspaces

This file records the linear-change-of-coordinates API for the boundary subspaces used by the
analytic Heegaard Floer roadmap. A linear equivalence `e : V ≃ₗ[ℝ] W` transports a symplectic
form by pulling arguments back along `e.symm`; the corresponding transported subspace is the
image `L.map e.toLinearMap`. With those conventions, symplectic orthogonal complements commute
with transport:

`(ω.transport e).orthogonal (L.map e.toLinearMap) = (ω.orthogonal L).map e.toLinearMap`.

The isotropic, coisotropic, and Lagrangian predicates are therefore invariant under linear
coordinate changes. This is the pointwise naturality needed before later manifold, bundle, and
Floer-boundary versions state the same facts in local trivializations.

## Main declarations

* `TauCeti.SymplecticForm.orthogonal_map_transport`: symplectic complements commute with transport.
* `TauCeti.SymplecticForm.isIsotropic_map_transport_iff`: transported isotropy.
* `TauCeti.SymplecticForm.isCoisotropic_map_transport_iff`: transported coisotropy.
* `TauCeti.SymplecticForm.isLagrangian_map_transport_iff`: transported Lagrangian-ness.
* `TauCeti.SymplecticForm.IsLagrangian.map_transport`: one-way consumer form.

The conventions follow McDuff--Salamon, *J-holomorphic Curves and Symplectic Topology*,
Section 2.1: symplectic changes of linear coordinates preserve the linear symplectic boundary
conditions.
-/

public section

namespace TauCeti

namespace SymplecticForm

variable {V W : Type*}
variable [AddCommGroup V] [Module ℝ V]
variable [AddCommGroup W] [Module ℝ W]
variable {ω : SymplecticForm V} {L : Submodule ℝ V} {e : V ≃ₗ[ℝ] W}

/-- The symplectic complement of a transported subspace is the transport of the symplectic
complement. -/
@[simp]
lemma orthogonal_map_transport :
    (ω.transport e).orthogonal (L.map e.toLinearMap) = (ω.orthogonal L).map e.toLinearMap := by
  ext w
  constructor
  · intro hw
    rw [Submodule.mem_map]
    refine ⟨e.symm w, ?_, by simp⟩
    rw [mem_orthogonal_iff]
    intro v hv
    have h := mem_orthogonal_iff.1 hw (e v)
      (Submodule.mem_map.2 ⟨v, hv, rfl⟩)
    simpa [SymplecticForm.transport_apply] using h
  · intro hw
    rw [mem_orthogonal_iff]
    intro y hy
    rcases Submodule.mem_map.1 hw with ⟨v, hv, hvw⟩
    rcases Submodule.mem_map.1 hy with ⟨x, hx, hxy⟩
    subst hvw
    subst hxy
    simpa [SymplecticForm.transport_apply] using (mem_orthogonal_iff.1 hv x hx)

/-- Isotropy is invariant under transporting both the symplectic form and the subspace along a
linear equivalence. -/
@[simp]
lemma isIsotropic_map_transport_iff :
    (ω.transport e).IsIsotropic (L.map e.toLinearMap) ↔ ω.IsIsotropic L := by
  rw [isIsotropic_iff, isIsotropic_iff]
  constructor
  · intro h x hx y hy
    have hxy := h (e x) (Submodule.mem_map.2 ⟨x, hx, rfl⟩)
      (e y) (Submodule.mem_map.2 ⟨y, hy, rfl⟩)
    simpa [SymplecticForm.transport_apply] using hxy
  · intro h x hx y hy
    rcases Submodule.mem_map.1 hx with ⟨x', hx', rfl⟩
    rcases Submodule.mem_map.1 hy with ⟨y', hy', rfl⟩
    simpa [SymplecticForm.transport_apply] using h x' hx' y' hy'

/-- Coisotropy is invariant under transporting both the symplectic form and the subspace along a
linear equivalence. -/
@[simp]
lemma isCoisotropic_map_transport_iff :
    (ω.transport e).IsCoisotropic (L.map e.toLinearMap) ↔ ω.IsCoisotropic L := by
  rw [isCoisotropic_iff, isCoisotropic_iff]
  constructor
  · intro h x hx
    have hx' : e x ∈ (ω.transport e).orthogonal (L.map e.toLinearMap) := by
      rw [orthogonal_map_transport]
      exact Submodule.mem_map.2 ⟨x, hx, rfl⟩
    rcases Submodule.mem_map.1 (h (e x) hx') with ⟨y, hy, hyx⟩
    have : y = x := by simpa using congrArg e.symm hyx
    simpa [this] using hy
  · intro h y hy
    rw [orthogonal_map_transport] at hy
    rcases Submodule.mem_map.1 hy with ⟨x, hx, rfl⟩
    exact Submodule.mem_map.2 ⟨x, h x hx, rfl⟩

/-- Lagrangian-ness is invariant under transporting both the symplectic form and the subspace
along a linear equivalence. -/
@[simp]
lemma isLagrangian_map_transport_iff :
    (ω.transport e).IsLagrangian (L.map e.toLinearMap) ↔ ω.IsLagrangian L := by
  rw [isLagrangian_iff, isLagrangian_iff, isIsotropic_map_transport_iff,
    isCoisotropic_map_transport_iff]

namespace IsIsotropic

/-- Transport an isotropic subspace along a linear equivalence, together with the transported
symplectic form. -/
lemma map_transport (h : ω.IsIsotropic L) :
    (ω.transport e).IsIsotropic (L.map e.toLinearMap) :=
  isIsotropic_map_transport_iff.2 h

end IsIsotropic

namespace IsCoisotropic

/-- Transport a coisotropic subspace along a linear equivalence, together with the transported
symplectic form. -/
lemma map_transport (h : ω.IsCoisotropic L) :
    (ω.transport e).IsCoisotropic (L.map e.toLinearMap) :=
  isCoisotropic_map_transport_iff.2 h

end IsCoisotropic

namespace IsLagrangian

/-- Transport a Lagrangian subspace along a linear equivalence, together with the transported
symplectic form. -/
lemma map_transport (h : ω.IsLagrangian L) :
    (ω.transport e).IsLagrangian (L.map e.toLinearMap) :=
  isLagrangian_map_transport_iff.2 h

end IsLagrangian

end SymplecticForm

end TauCeti
