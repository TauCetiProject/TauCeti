/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient
public import Mathlib.Topology.Algebra.Module.Equiv.Basic

/-!
# Quotients of topological modules

A continuous linear equivalence carrying one submodule onto another induces a continuous
linear equivalence of their quotients. This is the topological version of Mathlib's
`Submodule.Quotient.equiv`, and allows quotient fibres to be transported between coordinates.

The quotient of a topological module by an open submodule is discrete; in particular the quotient
of a discrete topological module by any submodule is discrete, since in a discrete module every
submodule is open.

Mathlib's `QuotientAddGroup.discreteTopology` is the statement for the quotient of a topological
additive group by an *open* subgroup, and supplies the whole proof; because it is a theorem
rather than an instance (Mathlib notes that `IsOpen` would have to be a class for that), instance
search cannot use it, so this file records it for `M ⧸ p` as a theorem, and the discrete case as
an instance. This is the same bridge from `QuotientAddGroup` to `Submodule.Quotient` that
Mathlib's own `Submodule.isTopologicalAddGroup_quotient` and `Submodule.t3_quotient_of_isClosed`
provide.
-/

public section

namespace Submodule.Quotient

variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M] [TopologicalSpace M]
  [SeparatelyContinuousAdd M]

/-- The quotient of a topological module by an open submodule is discrete. -/
theorem discreteTopology_of_isOpen (p : Submodule R M) (hp : IsOpen (p : Set M)) :
    DiscreteTopology (M ⧸ p) :=
  QuotientAddGroup.discreteTopology (N := p.toAddSubgroup) hp

omit [SeparatelyContinuousAdd M] in
/-- The quotient of a discrete topological module by a submodule is discrete. -/
instance discreteTopology [DiscreteTopology M] (p : Submodule R M) : DiscreteTopology (M ⧸ p) :=
  discreteTopology_of_isOpen p (isOpen_discrete _)

end Submodule.Quotient

namespace ContinuousLinearEquiv

variable {R M N : Type*} [Ring R] [AddCommGroup M] [Module R M] [TopologicalSpace M]
  [AddCommGroup N] [Module R N] [TopologicalSpace N]

/-- A continuous linear equivalence carrying `P` onto `Q` induces a continuous linear
equivalence of the quotient topological modules. -/
def quotientEquiv (e : M ≃L[R] N) (P : Submodule R M) (Q : Submodule R N)
    (h : P.map e.toLinearMap = Q) : (M ⧸ P) ≃L[R] (N ⧸ Q) where
  __ := Submodule.Quotient.equiv P Q e.toLinearEquiv h
  continuous_toFun := P.isQuotientMap_mkQL.continuous_iff.mpr (by
    convert Q.mkQL.continuous.comp e.continuous using 1
    funext x
    simp)
  continuous_invFun := Q.isQuotientMap_mkQL.continuous_iff.mpr (by
    convert P.mkQL.continuous.comp e.symm.continuous using 1
    funext x
    simp)

/-- The induced quotient equivalence sends the class of `x` to the class of `e x`. -/
@[simp]
theorem quotientEquiv_mk (e : M ≃L[R] N) (P : Submodule R M) (Q : Submodule R N)
    (h : P.map e.toLinearMap = Q) (x : M) :
    e.quotientEquiv P Q h (Submodule.Quotient.mk x) = Submodule.Quotient.mk (e x) := by
  simp [quotientEquiv]

/-- Inverting the induced quotient equivalence induces the inverse ambient equivalence. -/
@[simp]
theorem quotientEquiv_symm (e : M ≃L[R] N) (P : Submodule R M) (Q : Submodule R N)
    (h : P.map e.toLinearMap = Q) :
    (e.quotientEquiv P Q h).symm =
      e.symm.quotientEquiv Q P ((Submodule.map_symm_eq_iff e.toLinearEquiv).mpr h) := by
  ext x
  rfl

/-- The quotient equivalence induced by the identity is the identity. -/
@[simp]
theorem quotientEquiv_refl (P : Submodule R M) :
    (ContinuousLinearEquiv.refl R M).quotientEquiv P P (Submodule.map_id P) =
      ContinuousLinearEquiv.refl R (M ⧸ P) := by
  ext z
  obtain ⟨x, rfl⟩ := P.mkQ_surjective z
  exact quotientEquiv_mk (ContinuousLinearEquiv.refl R M) P P (Submodule.map_id P) x

/-- Inducing quotient equivalences commutes with composition. -/
theorem quotientEquiv_trans {O : Type*} [AddCommGroup O] [Module R O] [TopologicalSpace O]
    (e : M ≃L[R] N) (e' : N ≃L[R] O)
    (P : Submodule R M) (Q : Submodule R N) (S : Submodule R O)
    (he : P.map e.toLinearMap = Q) (he' : Q.map e'.toLinearMap = S) :
    (e.trans e').quotientEquiv P S (by
      -- Mathlib has no `trans_toLinearMap` lemma; this exposes the composite linear map
      -- underlying `trans` so `Submodule.map_comp` can rewrite the submodule image.
      change P.map (e'.toLinearMap.comp e.toLinearMap) = S
      rw [Submodule.map_comp, he, he']) =
      (e.quotientEquiv P Q he).trans (e'.quotientEquiv Q S he') := by
  ext z
  obtain ⟨x, rfl⟩ := P.mkQ_surjective z
  simp only [ContinuousLinearEquiv.trans_apply, Submodule.mkQ_apply, quotientEquiv_mk]

end ContinuousLinearEquiv
