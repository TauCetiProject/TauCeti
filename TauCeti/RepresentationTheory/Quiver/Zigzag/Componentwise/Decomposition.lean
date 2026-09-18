/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.StdBasis
public import TauCeti.RepresentationTheory.Quiver.Zigzag.Componentwise.Basis

/-!
# The vertex–arrow–volume basis of the public zigzag algebra

The public zigzag algebra is a finite product of component algebras. Its basis has one
idempotent and one volume for every vertex, including isolated vertices, and one arrow for
every dart. On a singleton component the volume is the infinitesimal generator of the dual
numbers. On all other components it is the canonical backtrack class.

`zigzagAlgebraBasis` assembles the component bases with `Pi.basis` and reindexes them by
`ZigzagBasisIndex G`. Its coordinate theorem computes a coefficient by projecting to the
appropriate component. The projection lemmas describe both the supported component and
vanishing on the other components.

## References

See Huerfano–Khovanov, *A category for the adjoint representation*, Section 3, and
Ehrig–Tubbenhauer, *Algebraic properties of zigzag algebras*, Section 2.
-/

public section

namespace TauCeti

open SimpleGraph

universe u w

variable {V : Type u} (G : SimpleGraph V)

/-- Forgetting the component labels identifies componentwise vertex–arrow–volume indices with
those of the original graph. The endpoints of a dart lie in the same connected component. -/
def zigzagComponentBasisIndexEquiv :
    (Σ C : G.ConnectedComponent, ZigzagBasisIndex C.toSimpleGraph) ≃ ZigzagBasisIndex G where
  toFun b := match b.2 with
    | .inl i => .inl i.val
    | .inr (.inl d) => .inr (.inl ⟨(d.fst.val, d.snd.val), d.adj⟩)
    | .inr (.inr i) => .inr (.inr i.val)
  invFun b := match b with
    | .inl i => ⟨G.connectedComponentMk i, .inl ⟨i, rfl⟩⟩
    | .inr (.inl d) => ⟨G.connectedComponentMk d.fst,
        .inr (.inl ⟨(⟨d.fst, rfl⟩, ⟨d.snd, ConnectedComponent.sound d.adj.reachable.symm⟩),
          d.adj⟩)⟩
    | .inr (.inr i) => ⟨G.connectedComponentMk i, .inr (.inr ⟨i, rfl⟩)⟩
  left_inv := by
    rintro ⟨C, i | d | i⟩
    · obtain ⟨i, hi⟩ := i
      subst C
      rfl
    · obtain ⟨⟨⟨i, hi⟩, ⟨j, hj⟩⟩, hd⟩ := d
      subst C
      rfl
    · obtain ⟨i, hi⟩ := i
      subst C
      rfl
  right_inv := by
    rintro (i | d | i) <;> rfl

@[simp]
theorem zigzagComponentBasisIndexEquiv_inl (C : G.ConnectedComponent) (i : C) :
    zigzagComponentBasisIndexEquiv G ⟨C, .inl i⟩ = .inl i.val := (rfl)

@[simp]
theorem zigzagComponentBasisIndexEquiv_inr_inl (C : G.ConnectedComponent)
    (d : C.toSimpleGraph.Dart) :
    zigzagComponentBasisIndexEquiv G ⟨C, .inr (.inl d)⟩ =
      .inr (.inl ⟨(d.fst.val, d.snd.val), d.adj⟩) := (rfl)

@[simp]
theorem zigzagComponentBasisIndexEquiv_inr_inr (C : G.ConnectedComponent) (i : C) :
    zigzagComponentBasisIndexEquiv G ⟨C, .inr (.inr i)⟩ = .inr (.inr i.val) := (rfl)

@[simp]
theorem zigzagComponentBasisIndexEquiv_symm_inl (i : V) :
    (zigzagComponentBasisIndexEquiv G).symm (.inl i) =
      ⟨G.connectedComponentMk i, .inl ⟨i, rfl⟩⟩ := (rfl)

@[simp]
theorem zigzagComponentBasisIndexEquiv_symm_inr_inl (d : G.Dart) :
    (zigzagComponentBasisIndexEquiv G).symm (.inr (.inl d)) =
      ⟨G.connectedComponentMk d.fst,
        .inr (.inl ⟨(⟨d.fst, rfl⟩,
          ⟨d.snd, ConnectedComponent.sound d.adj.reachable.symm⟩), d.adj⟩)⟩ := (rfl)

@[simp]
theorem zigzagComponentBasisIndexEquiv_symm_inr_inr (i : V) :
    (zigzagComponentBasisIndexEquiv G).symm (.inr (.inr i)) =
      ⟨G.connectedComponentMk i, .inr (.inr ⟨i, rfl⟩)⟩ := (rfl)

variable (k : Type w) [CommRing k] [Finite V]

/-- The vertex–arrow–volume basis of the public zigzag algebra. Isolated vertices contribute
both the unit and the infinitesimal generator of their dual-number factor. -/
noncomputable def zigzagAlgebraBasis (k : Type w) [CommRing k] (G : SimpleGraph V) :
    Module.Basis (ZigzagBasisIndex G) k (zigzagAlgebra k G) := by
  let _ : Fintype G.ConnectedComponent := Fintype.ofFinite _
  exact ((Pi.basis (zigzagComponentBasis k G)).map
    (zigzagAlgebraPiAlgEquiv k G).symm.toLinearEquiv).reindex
      (zigzagComponentBasisIndexEquiv G)

open scoped Classical in
/-- A global basis vector is the corresponding component basis vector, extended by zero. -/
theorem zigzagAlgebraBasis_apply (b : ZigzagBasisIndex G) :
    zigzagAlgebraBasis k G b = zigzagAlgebraMk k G
      (Pi.single ((zigzagComponentBasisIndexEquiv G).symm b).1
        (zigzagComponentBasis k G ((zigzagComponentBasisIndexEquiv G).symm b).1
          ((zigzagComponentBasisIndexEquiv G).symm b).2)) := by
  simp [zigzagAlgebraBasis, Module.Basis.reindex_apply, Module.Basis.map_apply]

/-- The global coefficient at a component-labelled index is the coefficient of its projection
in the basis of that component. -/
@[simp]
theorem zigzagAlgebraBasis_repr (x : zigzagAlgebra k G)
    (b : Σ C : G.ConnectedComponent, ZigzagBasisIndex C.toSimpleGraph) :
    (zigzagAlgebraBasis k G).repr x (zigzagComponentBasisIndexEquiv G b) =
      (zigzagComponentBasis k G b.1).repr (zigzagComponentProjection k G b.1 x) b.2 := by
  simp [zigzagAlgebraBasis, Module.Basis.map_repr]

/-- Projection to the supporting component recovers the component basis vector. -/
@[simp]
theorem zigzagComponentProjection_zigzagAlgebraBasis (C : G.ConnectedComponent)
    (b : ZigzagBasisIndex C.toSimpleGraph) :
    zigzagComponentProjection k G C
      (zigzagAlgebraBasis k G (zigzagComponentBasisIndexEquiv G ⟨C, b⟩)) =
        zigzagComponentBasis k G C b := by
  classical
  rw [zigzagAlgebraBasis_apply, zigzagComponentProjection_zigzagAlgebraMk,
    Equiv.symm_apply_apply, Pi.single_eq_same]

/-- A basis vector vanishes on every component other than its supporting component. -/
@[simp]
theorem zigzagComponentProjection_zigzagAlgebraBasis_of_ne
    (C D : G.ConnectedComponent) (h : D ≠ C) (b : ZigzagBasisIndex C.toSimpleGraph) :
    zigzagComponentProjection k G D
      (zigzagAlgebraBasis k G (zigzagComponentBasisIndexEquiv G ⟨C, b⟩)) = 0 := by
  classical
  simp [zigzagAlgebraBasis_apply, h]

end TauCeti
