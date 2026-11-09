/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.ModuleTopology
public import Mathlib.Topology.Maps.Strict.Module
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Topology.Compactness.SigmaCompact
import Mathlib.Topology.Compactness.LocallyCompact

/-!
# Module topology in coordinates and presentations

The module topology on a module with a basis over a Hausdorff topological semiring is Hausdorff.
Its basis coordinates give a continuous injection into a product of copies of the scalars; the
basis may be infinite.

For a module over a topological semiring with a finite basis, the module topology is the
coordinate topology through that basis. This identifies the canonical topology used on quadratic
spaces and their endomorphisms with a finite product of copies of the scalars. In particular, over
a Hausdorff locally compact division ring equipped with a topological semiring structure, the
module topology of a finite-dimensional space is Hausdorff and locally compact; every subspace of
a module with the module topology is closed; over σ-compact scalars it is σ-compact. No norm or
completeness hypothesis on the scalars is needed.

Separation of the scalars cannot be dropped from the Hausdorff and closed-subspace statements:
over a semiring with the indiscrete topology, the module topology of every module is indiscrete
(`IndiscreteTopology.of_continuousSMul`), so `IsModuleTopology` on its own does not replace the
separation of the scalars.

Without a basis, any linear equivalence between modules with the module topology is a continuous
linear equivalence (`LinearEquiv.toContinuousLinearEquivOfIsModuleTopology`). The module topology
on `M` is the quotient topology along any linear surjection `q : F → M` from a module with its
module topology (`LinearMap.quotKerContinuousLinearEquivOfSurjective`), so any two presentations of
an untopologised module from modules with the module topology induce topologically isomorphic
quotients (`LinearMap.presentationContinuousLinearEquiv`), and `moduleTopology A M` is Hausdorff
exactly when `ker q` is closed (`TauCeti.t2Space_moduleTopology_iff_isClosed_ker`). Finally, a
linear map out of a module with the module topology is strict whenever its range carries the module
topology for the subspace topology (`LinearMap.isStrictMap_of_isModuleTopology_range`).

Restriction of scalars along a finite algebra carrying the module topology preserves the
module topology (`IsModuleTopology.restrictScalars`). No finiteness of the module is needed.

The basis-dependent API is grouped in `TauCeti.ModuleTopology`, alongside Mathlib's
organizational `ModuleTopology` namespace.
-/

public section

namespace IsModuleTopology

/-- In a continuous scalar tower, the module topology over the smaller scalar semiring is
also the module topology over the larger scalar semiring, provided the larger scalar action
is continuous for the given topology. No finiteness assumption is needed. -/
theorem of_restrictScalars {R S M : Type*} [Semiring R] [Semiring S]
    [TopologicalSpace R] [TopologicalSpace S] [SMul R S] [ContinuousSMul R S]
    [AddCommMonoid M] [Module R M] [Module S M] [IsScalarTower R S M]
    [TopologicalSpace M] [IsModuleTopology R M] [ContinuousSMul S M] :
    IsModuleTopology S M := by
  have := IsModuleTopology.toContinuousAdd R M
  refine ⟨le_antisymm ?_ (moduleTopology_le S M)⟩
  rw [eq_moduleTopology R M]
  let := moduleTopology S M
  have := IsModuleTopology.toContinuousAdd S M
  have : ContinuousSMul R M := IsScalarTower.continuousSMul S
  exact moduleTopology_le R M

/-- Restricting scalars along a finite algebra with its natural topology preserves the module
topology, even for modules that are not finitely generated. -/
theorem restrictScalars (R S M : Type*) [CommRing R] [Ring S] [Algebra R S]
    [TopologicalSpace R] [IsTopologicalRing R] [TopologicalSpace S]
    [IsModuleTopology R S] [Module.Finite R S] [AddCommGroup M]
    [Module S M] [Module R M] [IsScalarTower R S M]
    [τM : TopologicalSpace M] [hM : IsModuleTopology S M] : IsModuleTopology R M := by
  have : ContinuousAdd M := IsModuleTopology.toContinuousAdd S M
  have : ContinuousSMul R M := IsScalarTower.continuousSMul S
  apply IsModuleTopology.of_continuous_id
  let τ := moduleTopology R M
  have : @ContinuousSMul S M _ _ τ := by
    let _ : TopologicalSpace M := τ
    have : IsModuleTopology R M := inferInstance
    exact ⟨IsModuleTopology.continuous_bilinear_of_finite_left
      (Algebra.lsmul R (A := S) R M).toLinearMap⟩
  -- The source keeps its given topology; only the target has the `R`-module topology.
  exact @IsModuleTopology.continuous_of_linearMap S _ _ M _ _ τM hM
    M _ _ τ (ModuleTopology.continuousAdd R M) this (LinearMap.id : M →ₗ[S] M)

end IsModuleTopology

namespace LinearEquiv

variable {R M N : Type*} [Semiring R] [TopologicalSpace R]
  [AddCommMonoid M] [Module R M] [TopologicalSpace M] [IsModuleTopology R M]
  [AddCommMonoid N] [Module R N] [TopologicalSpace N] [IsModuleTopology R N]

/-- Any linear equivalence between modules carrying the module topology is a continuous linear
equivalence. -/
def toContinuousLinearEquivOfIsModuleTopology (e : M ≃ₗ[R] N) : M ≃L[R] N :=
  let _ : ContinuousAdd M := IsModuleTopology.toContinuousAdd R M
  let _ : ContinuousAdd N := IsModuleTopology.toContinuousAdd R N
  { e with
    continuous_toFun := IsModuleTopology.continuous_of_linearMap e.toLinearMap
    continuous_invFun := IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap }

/-- `LinearEquiv.toContinuousLinearEquivOfIsModuleTopology` has the same underlying function. -/
@[simp]
theorem coe_toContinuousLinearEquivOfIsModuleTopology (e : M ≃ₗ[R] N) :
    ⇑e.toContinuousLinearEquivOfIsModuleTopology = e := (rfl)

/-- The underlying linear equivalence of `LinearEquiv.toContinuousLinearEquivOfIsModuleTopology`
is the original equivalence. -/
@[simp]
theorem toLinearEquiv_toContinuousLinearEquivOfIsModuleTopology (e : M ≃ₗ[R] N) :
    e.toContinuousLinearEquivOfIsModuleTopology.toLinearEquiv = e := (rfl)

/-- Inverting `LinearEquiv.toContinuousLinearEquivOfIsModuleTopology` upgrades the inverse linear
equivalence. -/
@[simp]
theorem symm_toContinuousLinearEquivOfIsModuleTopology (e : M ≃ₗ[R] N) :
    e.toContinuousLinearEquivOfIsModuleTopology.symm =
      e.symm.toContinuousLinearEquivOfIsModuleTopology := (rfl)

end LinearEquiv

namespace LinearMap

section Surjective

variable {R M N : Type*} [Ring R] [TopologicalSpace R]
  [AddCommGroup M] [Module R M] [TopologicalSpace M] [IsModuleTopology R M]
  [AddCommGroup N] [Module R N] [TopologicalSpace N] [IsModuleTopology R N]

/-- **Topological first isomorphism theorem for the module topology.** For a surjective linear map
`f : M →ₗ[R] N` between modules carrying the module topology, `M ⧸ ker f ≃ₗ[R] N` is a continuous
linear equivalence. -/
noncomputable def quotKerContinuousLinearEquivOfSurjective (f : M →ₗ[R] N)
    (hf : Function.Surjective f) : (M ⧸ LinearMap.ker f) ≃L[R] N :=
  (f.quotKerEquivOfSurjective hf).toContinuousLinearEquivOfIsModuleTopology

/-- The topological first isomorphism sends the class of `x` to `f x`. -/
@[simp]
theorem quotKerContinuousLinearEquivOfSurjective_apply_mk (f : M →ₗ[R] N)
    (hf : Function.Surjective f) (x : M) :
    f.quotKerContinuousLinearEquivOfSurjective hf (Submodule.Quotient.mk x) = f x := (rfl)

/-- The inverse of `LinearMap.quotKerContinuousLinearEquivOfSurjective` sends `f x` to the class
of `x`. -/
@[simp]
theorem quotKerContinuousLinearEquivOfSurjective_symm_apply (f : M →ₗ[R] N)
    (hf : Function.Surjective f) (x : M) :
    (f.quotKerContinuousLinearEquivOfSurjective hf).symm (f x) = Submodule.Quotient.mk x :=
  f.quotKerEquivOfSurjective_symm_apply hf x

/-- The underlying linear equivalence of `LinearMap.quotKerContinuousLinearEquivOfSurjective` is
`LinearMap.quotKerEquivOfSurjective`. -/
@[simp]
theorem toLinearEquiv_quotKerContinuousLinearEquivOfSurjective (f : M →ₗ[R] N)
    (hf : Function.Surjective f) :
    (f.quotKerContinuousLinearEquivOfSurjective hf).toLinearEquiv =
      f.quotKerEquivOfSurjective hf := (rfl)

end Surjective

section Presentation

variable {R F₁ F₂ M : Type*} [Ring R] [TopologicalSpace R]
  [AddCommGroup F₁] [Module R F₁] [TopologicalSpace F₁] [IsModuleTopology R F₁]
  [AddCommGroup F₂] [Module R F₂] [TopologicalSpace F₂] [IsModuleTopology R F₂]
  [AddCommGroup M] [Module R M]

/-- **Independence of presentation for quotient topologies.** Two surjective linear maps onto the
same `R`-module `M` from modules carrying the module topology induce a continuous linear
equivalence between the corresponding quotient modules, compatible with both presentations. No
topology on `M` is needed. -/
noncomputable def presentationContinuousLinearEquiv (π₁ : F₁ →ₗ[R] M)
    (hπ₁ : Function.Surjective π₁) (π₂ : F₂ →ₗ[R] M) (hπ₂ : Function.Surjective π₂) :
    (F₁ ⧸ LinearMap.ker π₁) ≃L[R] (F₂ ⧸ LinearMap.ker π₂) :=
  ((π₁.quotKerEquivOfSurjective hπ₁).trans
    (π₂.quotKerEquivOfSurjective hπ₂).symm).toContinuousLinearEquivOfIsModuleTopology

/-- `LinearMap.presentationContinuousLinearEquiv` commutes with the maps to `M` induced by both
presentations. -/
@[simp]
theorem liftQ_presentationContinuousLinearEquiv (π₁ : F₁ →ₗ[R] M)
    (hπ₁ : Function.Surjective π₁) (π₂ : F₂ →ₗ[R] M) (hπ₂ : Function.Surjective π₂)
    (x : F₁ ⧸ LinearMap.ker π₁) :
    (LinearMap.ker π₂).liftQ π₂ le_rfl (π₁.presentationContinuousLinearEquiv hπ₁ π₂ hπ₂ x) =
      (LinearMap.ker π₁).liftQ π₁ le_rfl x := by
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨z, hz⟩ := hπ₂ (π₁ y)
  simp [presentationContinuousLinearEquiv, ← hz]

/-- Inverting `LinearMap.presentationContinuousLinearEquiv` swaps the two presentations. -/
@[simp]
theorem symm_presentationContinuousLinearEquiv (π₁ : F₁ →ₗ[R] M)
    (hπ₁ : Function.Surjective π₁) (π₂ : F₂ →ₗ[R] M) (hπ₂ : Function.Surjective π₂) :
    (π₁.presentationContinuousLinearEquiv hπ₁ π₂ hπ₂).symm =
      π₂.presentationContinuousLinearEquiv hπ₂ π₁ hπ₁ := by
  ext x
  rfl

/-- The underlying linear equivalence of `LinearMap.presentationContinuousLinearEquiv` is the
composite of the algebraic first isomorphisms. -/
@[simp]
theorem toLinearEquiv_presentationContinuousLinearEquiv (π₁ : F₁ →ₗ[R] M)
    (hπ₁ : Function.Surjective π₁) (π₂ : F₂ →ₗ[R] M) (hπ₂ : Function.Surjective π₂) :
    (π₁.presentationContinuousLinearEquiv hπ₁ π₂ hπ₂).toLinearEquiv =
      (π₁.quotKerEquivOfSurjective hπ₁).trans (π₂.quotKerEquivOfSurjective hπ₂).symm := (rfl)

end Presentation

/-- A linear map from a module with the module topology is strict whenever its range, equipped with
the subspace topology, carries the module topology. -/
theorem isStrictMap_of_isModuleTopology_range {R M N : Type*} [Ring R] [TopologicalSpace R]
    [AddCommGroup M] [Module R M] [TopologicalSpace M] [IsModuleTopology R M]
    [AddCommGroup N] [Module R N] [TopologicalSpace N] (f : M →ₗ[R] N)
    (hr : IsModuleTopology R (LinearMap.range f)) : Topology.IsStrictMap f := by
  have := IsModuleTopology.isTopologicalAddGroup R M
  rw [LinearMap.isStrictMap_iff_isOpenQuotientMap_rangeRestrict]
  exact IsModuleTopology.isOpenQuotientMap_of_surjective f.surjective_rangeRestrict

end LinearMap

namespace TauCeti

namespace ModuleTopology

variable {K V ι : Type*} [Semiring K] [TopologicalSpace K] [IsTopologicalSemiring K]
  [AddCommMonoid V] [Module K V] [TopologicalSpace V] [IsModuleTopology K V]

/-- The module topology is Hausdorff when the scalars are Hausdorff and the module has a basis,
including an infinite basis. -/
theorem t2Space (b : _root_.Module.Basis ι K V) [T2Space K] : T2Space V :=
  T2Space.of_injective_continuous
    (f := fun x i ↦ b.coord i x)
    (fun _ _ h ↦ b.ext_elem (congrFun h))
    (continuous_pi fun i ↦ IsModuleTopology.continuous_of_linearMap (b.coord i))

variable [Finite ι]

/-- Coordinates through a finite basis give a homeomorphism for the module topology. -/
noncomputable def equivFunHomeomorph (b : _root_.Module.Basis ι K V) : V ≃ₜ (ι → K) :=
  let _ : ContinuousAdd V := IsModuleTopology.toContinuousAdd K V
  { b.equivFun with
    continuous_toFun := IsModuleTopology.continuous_of_linearMap b.equivFun.toLinearMap
    continuous_invFun := IsModuleTopology.continuous_of_linearMap b.equivFun.symm.toLinearMap }

@[simp]
theorem equivFunHomeomorph_apply (b : _root_.Module.Basis ι K V) (v : V) :
    equivFunHomeomorph b v = b.equivFun v := by
  simp [equivFunHomeomorph]

@[simp]
theorem equivFunHomeomorph_symm_apply (b : _root_.Module.Basis ι K V) (c : ι → K) :
    (equivFunHomeomorph b).symm c = b.equivFun.symm c := by
  simp [equivFunHomeomorph]

/-- The module topology is locally compact when the scalars are locally compact and the module
has a finite basis. -/
theorem locallyCompactSpace (b : _root_.Module.Basis ι K V) [LocallyCompactSpace K] :
    LocallyCompactSpace V :=
  (equivFunHomeomorph b).isOpenEmbedding.locallyCompactSpace

/-- The module topology is σ-compact when the scalars are σ-compact and the module has a finite
basis. -/
theorem sigmaCompactSpace (b : _root_.Module.Basis ι K V) [SigmaCompactSpace K] :
    SigmaCompactSpace V :=
  (equivFunHomeomorph b).isClosedEmbedding.sigmaCompactSpace

end ModuleTopology

/-- The module topology on a free module over a Hausdorff topological semiring is Hausdorff. -/
theorem t2Space_moduleTopology {R V : Type*} [Semiring R] [TopologicalSpace R]
    [IsTopologicalSemiring R] [T2Space R] [AddCommMonoid V] [Module R V] [Module.Free R V] :
    @T2Space V (moduleTopology R V) := by
  let _ : TopologicalSpace V := moduleTopology R V
  exact ModuleTopology.t2Space (Module.Free.chooseBasis R V)

/-- **The module topology is Hausdorff exactly when the kernel of a presentation is closed.** For
a linear surjection `q : F → M` from a module with its module topology, `moduleTopology A M` is
Hausdorff if and only if `ker q` is closed in `F`. No finiteness is needed: the module topology on
`M` is the quotient topology along `q`. -/
theorem t2Space_moduleTopology_iff_isClosed_ker {A M F : Type*} [Ring A] [TopologicalSpace A]
    [AddCommGroup M] [Module A M] [AddCommGroup F] [Module A F] [TopologicalSpace F]
    [IsModuleTopology A F] {q : F →ₗ[A] M} (hq : Function.Surjective q) :
    @T2Space M (moduleTopology A M) ↔ IsClosed (LinearMap.ker q : Set F) := by
  let _ : TopologicalSpace M := moduleTopology A M
  have _ : IsModuleTopology A M := ⟨rfl⟩
  have _ : IsTopologicalAddGroup M := IsModuleTopology.isTopologicalAddGroup A M
  rw [IsTopologicalAddGroup.t2Space_iff_zero_closed,
    ← (IsModuleTopology.isQuotientMap_of_surjective hq).isClosed_preimage]
  rfl

variable {K V : Type*} [DivisionRing K] [TopologicalSpace K] [IsTopologicalSemiring K]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- The module topology of a finite-dimensional space over a locally compact division ring
equipped with a topological semiring structure is locally compact. -/
theorem locallyCompactSpace_moduleTopology [LocallyCompactSpace K] :
    @LocallyCompactSpace V (moduleTopology K V) := by
  let _ : TopologicalSpace V := moduleTopology K V
  let b := Module.finBasis K V
  exact ModuleTopology.locallyCompactSpace b

/-- The module topology of a finite-dimensional space over a σ-compact division ring equipped
with a topological semiring structure is σ-compact. -/
theorem sigmaCompactSpace_moduleTopology [SigmaCompactSpace K] :
    @SigmaCompactSpace V (moduleTopology K V) := by
  let _ : TopologicalSpace V := moduleTopology K V
  let b := Module.finBasis K V
  exact ModuleTopology.sigmaCompactSpace b

omit [FiniteDimensional K V] in
/-- Every subspace of a space over a Hausdorff division ring equipped with a topological semiring
structure is closed for the module topology. -/
theorem _root_.Submodule.isClosed_of_isModuleTopology [T2Space K] [TopologicalSpace V]
    [IsModuleTopology K V] (W : Submodule K V) : IsClosed (W : Set V) := by
  have : T2Space (V ⧸ W) := ModuleTopology.t2Space (Module.Free.chooseBasis K (V ⧸ W))
  have : ContinuousAdd (V ⧸ W) := IsModuleTopology.toContinuousAdd K (V ⧸ W)
  have hW : (W : Set V) = W.mkQ ⁻¹' {0} := by
    ext x
    simp [Submodule.Quotient.mk_eq_zero]
  rw [hW]
  exact isClosed_singleton.preimage (IsModuleTopology.continuous_of_linearMap W.mkQ)

/-- A space on which scalars with the indiscrete topology act continuously, with zero, is
indiscrete. In particular, over a semiring with the indiscrete topology, the module topology of
any module is indiscrete. -/
theorem _root_.IndiscreteTopology.of_continuousSMul (R M : Type*) [MonoidWithZero R]
    [TopologicalSpace R] [IndiscreteTopology R] [Zero M] [MulActionWithZero R M]
    [TopologicalSpace M] [ContinuousSMul R M] : IndiscreteTopology M := by
  -- The indiscrete scalars `0` and `1` are inseparable, so `0 = 0 • x` and `x = 1 • x` are.
  have h (x : M) : Inseparable (0 : M) x := by
    simpa using (Inseparable.all (0 : R) 1).smul (.refl x)
  exact .of_forall_inseparable fun x y ↦ (h x).symm.trans (h y)

end TauCeti
