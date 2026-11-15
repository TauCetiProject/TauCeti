/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient
public import Mathlib.Topology.Algebra.Module.Equiv.Basic
public import TauCeti.Algebra.Module.Submodule.OrbitRelQuotient

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

The orbit space `AddAction.orbitRel.Quotient p M` of translation by a submodule, the standard
carrier for quotients such as complex tori, is second countable when `M` is
(`Submodule.instSecondCountableTopologyOrbitRelQuotient`), by Mathlib's
`ContinuousConstVAdd.secondCountableTopology`. It is a topological additive group when `M` is
(`Submodule.instIsTopologicalAddGroupOrbitRelQuotient`), and it is isomorphic to `M ⧸ p` as a
topological additive group (`Submodule.orbitRelQuotientContinuousAddEquiv`). The map of orbit
spaces induced by a continuous semilinear map is continuous
(`Submodule.continuous_orbitRelQuotientMap`).
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

/-- The quotient of a second countable topological module by translations by a submodule is
second countable. -/
instance Submodule.instSecondCountableTopologyOrbitRelQuotient {R M : Type*} [Ring R]
    [AddCommGroup M] [Module R M] [TopologicalSpace M] [ContinuousAdd M]
    [SecondCountableTopology M] (p : Submodule R M) :
    SecondCountableTopology (AddAction.orbitRel.Quotient p M) :=
  ContinuousConstVAdd.secondCountableTopology

/-- The orbit space of translation by a submodule of a topological additive group, with the group
structure of `M ⧸ p` (`Submodule.instAddCommGroupOrbitRelQuotient`), is a topological additive
group: the orbit projection is an open quotient map, so its square is a quotient map. -/
instance Submodule.instIsTopologicalAddGroupOrbitRelQuotient {R M : Type*} [Ring R]
    [AddCommGroup M] [Module R M] [TopologicalSpace M] [IsTopologicalAddGroup M]
    (p : Submodule R M) : IsTopologicalAddGroup (AddAction.orbitRel.Quotient p M) where
  continuous_add :=
    (AddAction.isOpenQuotientMap_quotientMk.prodMap
        AddAction.isOpenQuotientMap_quotientMk).isQuotientMap.continuous_iff.2 <|
      (continuous_quotient_mk'.comp continuous_add).congr fun x ↦
        (p.orbitRelQuotient_mk_add x.1 x.2).symm
  continuous_neg :=
    AddAction.isOpenQuotientMap_quotientMk.isQuotientMap.continuous_iff.2 <|
      (continuous_quotient_mk'.comp continuous_neg).congr fun x ↦ (p.orbitRelQuotient_mk_neg x).symm

/-- `Submodule.orbitRelQuotientAddEquiv` as an isomorphism of topological additive groups: the
orbit space of translation by `p` and `M ⧸ p` are both quotients of `M` by the same relation. -/
def Submodule.orbitRelQuotientContinuousAddEquiv {R M : Type*} [Ring R] [AddCommGroup M]
    [Module R M] [TopologicalSpace M] (p : Submodule R M) :
    AddAction.orbitRel.Quotient p M ≃ₜ+ M ⧸ p where
  __ := p.orbitRelQuotientAddEquiv
  continuous_toFun := isQuotientMap_quotient_mk'.continuous_iff.2 <|
    continuous_quotient_mk'.congr fun x ↦ (p.orbitRelQuotientAddEquiv_mk x).symm
  continuous_invFun := p.isQuotientMap_mkQ.continuous_iff.2 <|
    continuous_quotient_mk'.congr fun x ↦ (p.orbitRelQuotientAddEquiv_symm_mk x).symm

/-- `Submodule.orbitRelQuotientContinuousAddEquiv` sends the orbit of `x` to the class of `x`. -/
@[simp]
theorem Submodule.orbitRelQuotientContinuousAddEquiv_mk {R M : Type*} [Ring R] [AddCommGroup M]
    [Module R M] [TopologicalSpace M] (p : Submodule R M) (x : M) :
    p.orbitRelQuotientContinuousAddEquiv (_root_.Quotient.mk (AddAction.orbitRel p M) x) =
      Submodule.Quotient.mk x :=
  p.orbitRelQuotientAddEquiv_mk x

/-- The inverse of `Submodule.orbitRelQuotientContinuousAddEquiv` sends the class of `x` to the
orbit of `x`. -/
@[simp]
theorem Submodule.orbitRelQuotientContinuousAddEquiv_symm_mk {R M : Type*} [Ring R]
    [AddCommGroup M] [Module R M] [TopologicalSpace M] (p : Submodule R M) (x : M) :
    p.orbitRelQuotientContinuousAddEquiv.symm (Submodule.Quotient.mk x) =
      _root_.Quotient.mk (AddAction.orbitRel p M) x :=
  p.orbitRelQuotientAddEquiv_symm_mk x

/-- If a closed submodule `S` contains `p`, its image `S / p` in the orbit space of translation by
`p` is closed. -/
theorem Submodule.isClosed_orbitRelQuotient_mk_image {R M : Type*} [Ring R] [AddCommGroup M]
    [Module R M] [TopologicalSpace M] {p S : Submodule R M} (hpS : p ≤ S)
    (hS : IsClosed (S : Set M)) :
    IsClosed (_root_.Quotient.mk (AddAction.orbitRel p M) '' S) := by
  rw [← isQuotientMap_quotient_mk'.isClosed_preimage]
  convert hS using 1
  refine Set.Subset.antisymm (fun x ⟨y, hy, hyx⟩ ↦ ?_) (Set.subset_preimage_image _ _)
  simpa using S.sub_mem hy (hpS (p.orbitRel_apply_iff_sub_mem.1 (_root_.Quotient.exact hyx)))

/-- The map of orbit spaces induced by a continuous semilinear map `f` carrying `p` into `q` is
continuous. -/
theorem Submodule.continuous_orbitRelQuotientMap {R M R₂ M₂ : Type*} [Ring R] [AddCommGroup M]
    [Module R M] [TopologicalSpace M] [Ring R₂] [AddCommGroup M₂] [Module R₂ M₂]
    [TopologicalSpace M₂] (p : Submodule R M) (q : Submodule R₂ M₂) {τ₁₂ : R →+* R₂}
    {f : M →ₛₗ[τ₁₂] M₂} (h : p ≤ q.comap f) (hf : Continuous f) :
    Continuous (p.orbitRelQuotientMap q f h) :=
  isQuotientMap_quotient_mk'.continuous_iff.2 <|
    (continuous_quotient_mk'.comp hf).congr fun x ↦ (p.orbitRelQuotientMap_mk q f h x).symm

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
