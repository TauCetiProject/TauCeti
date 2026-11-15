/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.Zigzag.Isomorphism
public import TauCeti.RepresentationTheory.Quiver.Zigzag.Signless

/-!
# Signless preprojective algebras under graph isomorphisms

A graph isomorphism relabels the doubled paths and their local signless relations, and hence
identifies the signless preprojective algebras. This allows algebraic properties to be
transported between different vertex labellings, including induced Dynkin subdiagrams.

The neighborhood `Fintype` instances are explicit parameters, matching those used to form the
caller's signless quotients. The quotient types retain their star enumerations as implicit
parameters, although the local relations are independent of the enumeration by
`TauCeti.signlessPreprojectiveRelator_congr`.

The construction descends `TauCeti.DoubledQuiver.pathAlgebraEquiv` through the quotient
universal property. The signless presentation follows Huerfano--Khovanov,
*A category for the adjoint representation*, Section 3, https://arxiv.org/abs/math/0002060.
-/

public section

namespace TauCeti

open DoubledQuiver

universe u v w

variable {V : Type u} {W : Type v}
  [Finite V] [Finite W] {G : SimpleGraph V} {H : SimpleGraph W}

section Relator

variable (k : Type w) [CommSemiring k]

/-- Relabelling a graph sends its local signless relation to the relation at the image vertex. -/
@[simp]
theorem DoubledQuiver.pathAlgebraEquiv_signlessPreprojectiveRelator
    (e : G ≃g H) (i : V) [Fintype (_root_.Quiver.Star (vertex G i))]
    [Fintype (_root_.Quiver.Star (vertex H (e i)))] :
    pathAlgebraEquiv k e (signlessPreprojectiveRelator k (vertex G i)) =
      signlessPreprojectiveRelator k (vertex H (e i)) := by
  classical
  let := Fintype.ofFinite (G.neighborSet i)
  let := Fintype.ofFinite (H.neighborSet (e i))
  rw [signlessPreprojectiveRelator_congr k (vertex G i) _ (instFintypeStarVertex G i),
    signlessPreprojectiveRelator_congr k (vertex H (e i)) _ (instFintypeStarVertex H (e i)),
    signlessPreprojectiveRelator_vertex, signlessPreprojectiveRelator_vertex, map_sum]
  let en : G.neighborSet i ≃ H.neighborSet (e i) :=
    e.toEquiv.subtypeEquiv fun _ => e.map_adj_iff.symm
  exact Fintype.sum_equiv en _ _ fun _ => pathAlgebraEquiv_backtrackElem k e _

end Relator

variable (k : Type w) [CommRing k]
  [∀ i, Fintype (G.neighborSet i)] [∀ j, Fintype (H.neighborSet j)]

private noncomputable def signlessPreprojectiveIsoHom (e : G ≃g H) :
    signlessPreprojectiveAlgebra k (DoubledQuiver G) →ₐ[k]
      signlessPreprojectiveAlgebra k (DoubledQuiver H) :=
  signlessPreprojectiveLift
    ((signlessPreprojectiveMk k _).comp (pathAlgebraEquiv k e).toAlgHom) fun i => by
      obtain ⟨i, rfl⟩ := exists_eq_vertex G i
      simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
        pathAlgebraEquiv_signlessPreprojectiveRelator]
      rw [signlessPreprojectiveRelator_congr k (vertex H (e i)) _
        (instFintypeStar (G := H) (vertex H (e i)))]
      exact signlessPreprojectiveMk_signlessPreprojectiveRelator k _

/-- A graph isomorphism identifies the signless preprojective algebras by relabelling paths. -/
noncomputable def signlessPreprojectiveAlgebraEquiv (e : G ≃g H) :
    signlessPreprojectiveAlgebra k (DoubledQuiver G) ≃ₐ[k]
      signlessPreprojectiveAlgebra k (DoubledQuiver H) :=
  AlgEquiv.ofAlgHom (signlessPreprojectiveIsoHom k e) (signlessPreprojectiveIsoHom k e.symm)
    (by
      ext y
      obtain ⟨x, rfl⟩ := signlessPreprojectiveMk_surjective k _ y
      simp [signlessPreprojectiveIsoHom, ← pathAlgebraEquiv_symm])
    (by
      ext y
      obtain ⟨x, rfl⟩ := signlessPreprojectiveMk_surjective k _ y
      simp [signlessPreprojectiveIsoHom, ← pathAlgebraEquiv_symm])

/-- The graph-isomorphism comparison sends a quotient class to the class of the relabelled path
algebra element. -/
@[simp]
theorem signlessPreprojectiveAlgebraEquiv_signlessPreprojectiveMk
    (e : G ≃g H) (x : pathAlgebra k (DoubledQuiver G)) :
    signlessPreprojectiveAlgebraEquiv k e (signlessPreprojectiveMk k _ x) =
      signlessPreprojectiveMk k _ (pathAlgebraEquiv k e x) := by
  simp [signlessPreprojectiveAlgebraEquiv, signlessPreprojectiveIsoHom]

/-- The inverse quotient isomorphism is induced by the inverse graph relabelling. -/
@[simp]
theorem signlessPreprojectiveAlgebraEquiv_symm (e : G ≃g H) :
    (signlessPreprojectiveAlgebraEquiv k e).symm =
      signlessPreprojectiveAlgebraEquiv k e.symm := by
  refine AlgEquiv.ext fun z => ?_
  obtain ⟨x, rfl⟩ := signlessPreprojectiveMk_surjective k _ z
  apply (signlessPreprojectiveAlgebraEquiv k e).injective
  rw [AlgEquiv.apply_symm_apply, signlessPreprojectiveAlgebraEquiv_signlessPreprojectiveMk,
    signlessPreprojectiveAlgebraEquiv_signlessPreprojectiveMk, ← pathAlgebraEquiv_symm,
    AlgEquiv.apply_symm_apply]

/-- The identity graph relabelling induces the identity of signless preprojective algebras. -/
@[simp]
theorem signlessPreprojectiveAlgebraEquiv_refl :
    signlessPreprojectiveAlgebraEquiv k (SimpleGraph.Iso.refl (G := G)) = AlgEquiv.refl := by
  refine AlgEquiv.ext fun z => ?_
  obtain ⟨x, rfl⟩ := signlessPreprojectiveMk_surjective k _ z
  rw [signlessPreprojectiveAlgebraEquiv_signlessPreprojectiveMk, pathAlgebraEquiv_refl]
  rfl

/-- Composing graph isomorphisms composes their induced signless preprojective equivalences. -/
theorem signlessPreprojectiveAlgebraEquiv_trans {X : Type*} [Finite X] {K : SimpleGraph X}
    [∀ i, Fintype (K.neighborSet i)] (e : G ≃g H) (f : H ≃g K) :
    signlessPreprojectiveAlgebraEquiv k (e.trans f) =
      (signlessPreprojectiveAlgebraEquiv k e).trans
        (signlessPreprojectiveAlgebraEquiv k f) := by
  refine AlgEquiv.ext fun z => ?_
  obtain ⟨x, rfl⟩ := signlessPreprojectiveMk_surjective k _ z
  rw [signlessPreprojectiveAlgebraEquiv_signlessPreprojectiveMk, pathAlgebraEquiv_trans,
    AlgEquiv.trans_apply, AlgEquiv.trans_apply,
    signlessPreprojectiveAlgebraEquiv_signlessPreprojectiveMk,
    signlessPreprojectiveAlgebraEquiv_signlessPreprojectiveMk]

end TauCeti
