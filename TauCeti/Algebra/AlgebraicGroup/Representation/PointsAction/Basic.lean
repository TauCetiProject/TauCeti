/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.FunctorOfPoints
public import TauCeti.Algebra.AlgebraicGroup.Hopf.Map
public import TauCeti.Algebra.AlgebraicGroup.PointsFunctor
public import TauCeti.Algebra.Coalgebra.Comodule.Finite.Corestrict
public import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.Basic
public import TauCeti.Algebra.Coalgebra.Comodule.PointAction
public import TauCeti.Algebra.Coalgebra.Comodule.Weight.Space
public import TauCeti.Algebra.Coalgebra.Subcomodule.Basic
public import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic
public import Mathlib.LinearAlgebra.Semisimple
import TauCeti.Algebra.Coalgebra.Comodule.Evaluation
import TauCeti.Algebra.Coalgebra.Subcomodule.PointSeparation
import TauCeti.LinearAlgebra.Eigenspace.JointEigenvector.Basic

/-!
# The points action of a comodule, by automorphisms

Over a Hopf algebra the points form a group under convolution — the points of the
corresponding affine group scheme, when `H` is commutative — so the points action of
a comodule (`TauCeti.Comodule.endOfPoint`,
`TauCeti.Comodule.pointsRepresentation`) lands in the units of the endomorphism
monoid: the action upgrades to linear automorphisms of the scalar extension via
`Representation.asGroupHom`, with inverses provided by the group structure rather
than by an antipode computation. For points valued in the base ring, the scalar-extension
action transports across `R ⊗[R] V ≃ₗ[R] V` to a representation on `V` itself.

## Main declarations

* `TauCeti.Comodule.pointsAction`: the action of the group of points by linear
  automorphisms of `A ⊗[R] V`.
* `TauCeti.Comodule.pointsAction_corestrict`: compatibility of point actions with
  corestriction and precomposition, also provided for bundled finite comodules by
  `TauCeti.Comodule.pointsAction_corestrict_obj`.
* `TauCeti.Comodule.basePointsRepresentation`: the action of base-valued points on the original
  comodule.
* `TauCeti.Comodule.basePointsRepresentation_apply_of_mem_weightSpace`: base-valued points act on
  a weight vector through the value of the point on its weight.
* `TauCeti.Comodule.coact_eq_tmul_one_iff_forall_pointsAction_tmul_eq`: geometric fixed-vector
  detection in terms of the convolution-group action.
* `TauCeti.Comodule.coact_eq_tmul_one_iff_forall_basePointsRepresentation_eq`: base-valued points
  detect fixed vectors over an algebraically closed base field.
* `Submodule.exists_mem_groupLikeWeightSpace_of_basePointsRepresentation_stable` and
  `TauCeti.Comodule.hasNonzeroWeightVector_of_basePointsRepresentation_stable`: a nonzero vector
  spanning a point-stable line is a weight vector.
* `TauCeti.Comodule.iSup_groupLikeWeightSpace_eq_top_of_isSemisimple`: a finite-dimensional
  comodule on which the base-valued points act by commuting semisimple operators is spanned by
  its weight spaces.
-/

public section

open scoped TensorProduct

namespace TauCeti

namespace Comodule

open _root_.Coalgebra WithConv _root_.TensorProduct

variable {R H V A : Type*} [CommSemiring R] [Semiring H] [HopfAlgebra R H]
  [AddCommMonoid V] [Module R V] [Comodule R H V]
  [CommSemiring A] [Algebra R A]

variable (V) in
/-- Over a Hopf algebra the points act by linear automorphisms of the scalar
extension: the group of points lands in the units of the endomorphism monoid, with
inverses provided by the group structure rather than by an antipode computation. -/
noncomputable def pointsAction :
    WithConv (H →ₐ[R] A) →* ((A ⊗[R] V) ≃ₗ[A] (A ⊗[R] V)) :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv A (A ⊗[R] V)).toMonoidHom.comp
    (pointsRepresentation V).asGroupHom

variable (V) in
@[simp]
lemma pointsAction_toLinearMap (g : WithConv (H →ₐ[R] A)) :
    (pointsAction V g : A ⊗[R] V →ₗ[A] A ⊗[R] V) = endOfPoint V g.ofConv := by
  -- `pointsAction` has no equation lemma to rewrite with; `change` spells out its
  -- definitional unfolding once, explicitly.
  change ((LinearMap.GeneralLinearGroup.generalLinearEquiv A (A ⊗[R] V))
    ((pointsRepresentation V).asGroupHom g) : A ⊗[R] V →ₗ[A] A ⊗[R] V) = _
  rw [LinearMap.GeneralLinearGroup.generalLinearEquiv_to_linearMap,
    Representation.asGroupHom_apply, pointsRepresentation_apply]

universe u v w x y

section BasePointsRepresentation

variable {R : Type u} {H : Type v}
variable [CommSemiring R] [Semiring H] [HopfAlgebra R H]

/-- The representation of the group of base-valued points on the original comodule.

`pointsRepresentation` acts on `R ⊗[R] M`; this is its transport across the canonical
equivalence `R ⊗[R] M ≃ₗ[R] M`. -/
noncomputable def basePointsRepresentation
    (M : Type w) [AddCommMonoid M] [Module R M] [Comodule R H M] :=
  (TensorProduct.lid R M).conjRingEquiv.toMonoidHom.comp
    (pointsRepresentation (R := R) (H := H) (A := R) M)

variable {M : Type w} [AddCommMonoid M] [Module R M] [Comodule R H M]

/-- A base-valued point acts on `m` by contracting the coefficient leg of its coaction. -/
theorem basePointsRepresentation_apply (g : WithConv (H →ₐ[R] R)) (m : M) :
    basePointsRepresentation (H := H) M g m =
      TensorProduct.lid R M (endOfPoint M g.ofConv (1 ⊗ₜ[R] m)) := by
  -- Unpack the `conjRingEquiv` transport to apply its characteristic evaluation lemma.
  change (TensorProduct.lid R M).conj
    (pointsRepresentation (R := R) (H := H) (A := R) M g) m = _
  rw [LinearEquiv.conj_apply_apply, pointsRepresentation_apply]
  simp

/-- Every subcomodule is stable under the action of base-valued points. -/
theorem basePointsRepresentation_mem (N : Subcomodule R H M)
    (g : WithConv (H →ₐ[R] R)) {m : M} (hm : m ∈ N) :
    basePointsRepresentation (H := H) M g m ∈ N := by
  rw [basePointsRepresentation_apply, endOfPoint_tmul, one_smul,
    TensorProduct.lid_comm]
  exact N.rid_lTensor_coact_mem g.ofConv.toLinearMap hm

/-- A base-valued point acts on a vector of group-like weight `c` by the scalar `g c`. -/
theorem basePointsRepresentation_apply_of_mem_weightSpace (g : WithConv (H →ₐ[R] R))
    {c : _root_.GroupLike R H} {m : M} (hm : m ∈ _root_.GroupLike.weightSpace (M := M) c) :
    basePointsRepresentation (H := H) M g m = g.ofConv c • m := by
  rw [basePointsRepresentation_apply, endOfPoint_tmul, _root_.GroupLike.mem_weightSpace.mp hm]
  simp

/-- The scalar-extension action of a base-valued point is the pure tensor of its action on the
original comodule. -/
@[simp]
theorem endOfPoint_one_tmul_eq_one_tmul_basePointsRepresentation
    (g : WithConv (H →ₐ[R] R)) (m : M) :
    (TensorProduct.comm R M R)
        ((LinearMap.lTensor M g.ofConv.toLinearMap) (coact (R := R) (C := H) m)) =
      1 ⊗ₜ[R] basePointsRepresentation (H := H) M g m := by
  apply (TensorProduct.lid R M).injective
  rw [basePointsRepresentation_apply]
  simp

/-- A constant algebra-valued point acts on a pure tensor by the original base-valued action. -/
theorem endOfPoint_mapValue_algebraOfId_tmul
    {A : Type*} [CommSemiring A] [Algebra R A]
    (g : WithConv (H →ₐ[R] R)) (a : A) (m : M) :
    endOfPoint M (AlgHom.mapValue (Algebra.ofId R A) g).ofConv (a ⊗ₜ[R] m) =
      a ⊗ₜ[R] basePointsRepresentation (H := H) M g m := by
  have h := LinearMap.congr_fun
    (rTensor_comp_endOfPoint M (Algebra.ofId R A) g.ofConv) (1 ⊗ₜ[R] m)
  simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply,
    LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply, map_one, endOfPoint_tmul,
    one_smul, endOfPoint_one_tmul_eq_one_tmul_basePointsRepresentation] at h
  rw [AlgHom.mapValue_apply, WithConv.ofConv_toConv, endOfPoint_tmul, ← h]
  simp [TensorProduct.smul_tmul']

/-- Evaluating a matrix coefficient at a base-valued point pairs the functional with the
point's action on the vector. -/
@[simp]
theorem apply_matrixCoefficient (g : WithConv (H →ₐ[R] R))
    (φ : Module.Dual R M) (m : M) :
    g.ofConv (matrixCoefficient (C := H) φ m) =
      φ (basePointsRepresentation (H := H) M g m) := by
  have h := baseChangeEvaluation_endOfPoint_tmul g.ofConv (1 : R) 1 φ m
  rw [endOfPoint_tmul, one_smul,
    endOfPoint_one_tmul_eq_one_tmul_basePointsRepresentation] at h
  simpa using h.symm

section Corestrict

variable {H₁ : Type v} {H₂ : Type x} [Semiring H₁] [Semiring H₂]
variable [HopfAlgebra R H₁] [HopfAlgebra R H₂]
variable {M : Type w} [AddCommMonoid M] [Module R M] [Comodule R H₁ M]

/-- Acting by a base-valued point on a corestricted comodule agrees with acting by the point
precomposed with the bialgebra morphism. -/
@[simp]
theorem basePointsRepresentation_corestrict (φ : H₁ →ₐc[R] H₂)
    (g : WithConv (H₂ →ₐ[R] R)) :
    (letI : Comodule R H₂ M := Corestrict φ.toCoalgHom
     basePointsRepresentation (R := R) (H := H₂) M g) =
      basePointsRepresentation (R := R) (H := H₁) M (BialgHom.mapDomain φ g) := by
  let _ : Comodule R H₂ M := Corestrict φ.toCoalgHom
  rw [BialgHom.mapDomain_apply]
  apply LinearMap.ext
  intro m
  rw [basePointsRepresentation_apply, basePointsRepresentation_apply]
  congr 1
  exact LinearMap.congr_fun (endOfPoint_corestrict φ g.ofConv) (1 ⊗ₜ[R] m)

end Corestrict

end BasePointsRepresentation

section BasePointsFixed

variable {R : Type u} {H : Type v} {M : Type w}
variable [CommSemiring R] [Semiring H] [HopfAlgebra R H]
variable [AddCommMonoid M] [Module R M] [Comodule R H M]

/-- A vector fixed by the coaction is fixed by every base-valued point. -/
theorem basePointsRepresentation_eq_of_coact_eq_tmul_one
    (m : M) (hm : coact (R := R) (C := H) m = m ⊗ₜ[R] (1 : H))
    (g : WithConv (H →ₐ[R] R)) :
    basePointsRepresentation (R := R) (H := H) M g m = m := by
  rw [basePointsRepresentation_apply, endOfPoint_tmul, hm]
  simp

end BasePointsFixed

section FixedVectorDetection

variable {k : Type u} {H : Type v} {M : Type w} {K : Type x}
variable [Field k] [CommRing H] [HopfAlgebra k H] [Algebra.FiniteType k H] [IsReduced H]
variable [AddCommGroup M] [Module k M] [Comodule k H M]
variable [Field K] [Algebra k K] [IsAlgClosed K]

/-- For a Hopf-algebra comodule, a vector is fixed by the coaction exactly when every point in the
convolution group fixes its scalar extension. -/
theorem coact_eq_tmul_one_iff_forall_pointsAction_tmul_eq (m : M) :
    coact (R := k) (C := H) m = m ⊗ₜ[k] (1 : H) ↔
      ∀ g : WithConv (H →ₐ[k] K),
        pointsAction M g ((1 : K) ⊗ₜ[k] m) = (1 : K) ⊗ₜ[k] m := by
  rw [coact_eq_tmul_one_iff_forall_endOfPoint_tmul_eq (K := K)]
  constructor
  · intro h g
    rw [← LinearEquiv.coe_toLinearMap, pointsAction_toLinearMap]
    exact h g.ofConv
  · intro h g
    have hg := h (toConv g)
    rw [← LinearEquiv.coe_toLinearMap, pointsAction_toLinearMap] at hg
    simpa only [ofConv_toConv] using hg

/-- Over an algebraically closed base field, base-valued points detect fixed vectors of a
reduced finite-type Hopf-algebra comodule. -/
theorem coact_eq_tmul_one_iff_forall_basePointsRepresentation_eq [IsAlgClosed k] (m : M) :
    coact (R := k) (C := H) m = m ⊗ₜ[k] (1 : H) ↔
      ∀ g : HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k),
        basePointsRepresentation (R := k) (H := H) M g m = m := by
  constructor
  · intro hm g
    exact basePointsRepresentation_eq_of_coact_eq_tmul_one m hm g
  · intro h
    rw [coact_eq_tmul_one_iff_forall_pointsAction_tmul_eq (K := k)]
    intro g
    rw [← LinearEquiv.coe_toLinearMap, pointsAction_toLinearMap,
      endOfPoint_tmul, one_smul,
      endOfPoint_one_tmul_eq_one_tmul_basePointsRepresentation, h g]

end FixedVectorDetection

section StableLineDetection

variable {k : Type u} {H : Type v} {M : Type w}
variable [Field k] [CommRing H] [HopfAlgebra k H]
variable [AddCommGroup M] [Module k M] [Comodule k H M]

/-- A nonzero vector spanning a submodule preserved by every base-valued point lies in a
group-like weight space. -/
theorem _root_.Submodule.exists_mem_groupLikeWeightSpace_of_basePointsRepresentation_stable
    [IsAlgClosed k] [Algebra.FiniteType k H] [IsReduced H]
    (p : Submodule k M) (v : M) (hv : v ≠ 0) (hspan : p = k ∙ v)
    (hact : ∀ (g : WithConv (H →ₐ[k] k)) {m : M}, m ∈ p →
      basePointsRepresentation (R := k) (H := H) M g m ∈ p) :
    ∃ c : GroupLike k H, v ∈ _root_.GroupLike.weightSpace (M := M) c := by
  have hstable : ∀ (g : H →ₐ[k] k) {m : M}, m ∈ p →
      Comodule.endOfPoint M g ((1 : k) ⊗ₜ[k] m) ∈ p.baseChange k := by
    intro g m hm
    rw [endOfPoint_tmul, one_smul,
      endOfPoint_one_tmul_eq_one_tmul_basePointsRepresentation]
    exact Submodule.tmul_mem_baseChange_of_mem _ (hact (toConv g) hm)
  obtain ⟨c, hc, hcoact⟩ := exists_isGroupLikeElem_coact_eq_tmul_of_toSubmodule_eq_span
    (Subcomodule.ofEndOfPointStable (K := k) p hstable) hv
    ((Subcomodule.ofEndOfPointStable_toSubmodule (K := k) p hstable).trans hspan)
  exact ⟨⟨c, hc⟩, _root_.GroupLike.mem_weightSpace.mpr hcoact⟩

/-- A nonzero vector spanning a submodule preserved by every base-valued point is a weight
vector. -/
theorem hasNonzeroWeightVector_of_basePointsRepresentation_stable
    [IsAlgClosed k] [Algebra.FiniteType k H] [IsReduced H]
    (p : Submodule k M) (v : M) (hv : v ≠ 0) (hspan : p = k ∙ v)
    (hact : ∀ (g : WithConv (H →ₐ[k] k)) {m : M}, m ∈ p →
      basePointsRepresentation (R := k) (H := H) M g m ∈ p) :
    HasNonzeroWeightVector k H M := by
  obtain ⟨c, hc⟩ :=
    p.exists_mem_groupLikeWeightSpace_of_basePointsRepresentation_stable v hv hspan hact
  exact hasNonzeroWeightVector_iff.mpr
    ⟨v, c.val, hv, c.isGroupLikeElem_val, _root_.GroupLike.mem_weightSpace.mp hc⟩

/-- If the base-valued points of a reduced finite-type Hopf algebra over an algebraically closed
field act on a finite-dimensional comodule by pairwise-commuting semisimple operators, then the
comodule is spanned by its group-like weight spaces. -/
theorem iSup_groupLikeWeightSpace_eq_top_of_isSemisimple
    [IsAlgClosed k] [Algebra.FiniteType k H] [IsReduced H] [FiniteDimensional k M]
    (hcomm : Pairwise fun g h : WithConv (H →ₐ[k] k) ↦
      Commute (basePointsRepresentation (R := k) (H := H) M g)
        (basePointsRepresentation (R := k) (H := H) M h))
    (hss : ∀ g : WithConv (H →ₐ[k] k),
      (basePointsRepresentation (R := k) (H := H) M g).IsSemisimple) :
    ⨆ c : GroupLike k H, _root_.GroupLike.weightSpace (M := M) c = ⊤ := by
  rw [eq_top_iff, ← iSup_iInf_eigenspace_eq_top_of_isSemisimple
    (fun g ↦ basePointsRepresentation (R := k) (H := H) M g) hcomm hss]
  refine iSup_le fun χ v hv ↦ ?_
  rcases eq_or_ne v 0 with rfl | hv0
  · exact zero_mem _
  obtain ⟨c, hc⟩ := (k ∙ v).exists_mem_groupLikeWeightSpace_of_basePointsRepresentation_stable
    v hv0 rfl fun g m hm ↦ by
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hm
      rw [map_smul, Module.End.mem_eigenspace_iff.mp ((Submodule.mem_iInf _).mp hv g),
        smul_smul]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v)
  exact Submodule.mem_iSup_of_mem c hc

end StableLineDetection

section Corestrict

variable {R : Type u} {H₁ : Type v} {H₂ : Type w} {A : Type x}
variable [CommSemiring R] [Semiring H₁] [Semiring H₂]
variable [CommSemiring A] [Algebra R A]

section HopfAlgebra

variable [HopfAlgebra R H₁] [HopfAlgebra R H₂]
variable {V : Type*} [AddCommMonoid V] [Module R V] [Comodule R H₁ V]

/-- The linear action of a precomposed point agrees with the action of the original point on
the corestricted comodule. -/
theorem pointsAction_corestrict (φ : H₁ →ₐc[R] H₂)
    (g : WithConv (H₂ →ₐ[R] A)) :
    (letI : Comodule R H₂ V := Corestrict φ.toCoalgHom
     pointsAction V g) = pointsAction V (BialgHom.mapDomain φ g) := by
  let : Comodule R H₂ V := Corestrict φ.toCoalgHom
  apply LinearEquiv.ext
  exact LinearMap.congr_fun <|
    (pointsAction_toLinearMap V g).trans <|
      (endOfPoint_corestrict φ g.ofConv).trans <|
        (by
          rw [BialgHom.mapDomain_apply, ofConv_toConv]
          exact (pointsAction_toLinearMap V
            (toConv (g.ofConv.comp (φ : H₁ →ₐ[R] H₂)))).symm)

/-- Simp-normal form of `pointsAction_corestrict`, with the precomposed point written
after normalization by `BialgHom.mapDomain_apply`. -/
@[simp]
theorem pointsAction_corestrict_toConv_comp (φ : H₁ →ₐc[R] H₂)
    (g : WithConv (H₂ →ₐ[R] A)) :
    (letI : Comodule R H₂ V := Corestrict φ.toCoalgHom
     pointsAction V g) =
      pointsAction V (toConv (g.ofConv.comp (φ : H₁ →ₐ[R] H₂))) := by
  simpa only [BialgHom.mapDomain_apply] using pointsAction_corestrict φ g

/-- Bundled finite-comodule form of `pointsAction_corestrict`. This avoids exposing the
definitionally equal comodule instance carried by the corestricted object to callers. -/
theorem pointsAction_corestrict_obj (φ : H₁ →ₐc[R] H₂)
    (M : FGComoduleCat.{u, v, y} R H₁) (g : WithConv (H₂ →ₐ[R] A)) :
    pointsAction ((FGComoduleCat.corestrict φ.toCoalgHom).obj M) g =
      pointsAction M (BialgHom.mapDomain φ g) := by
  -- The bundled object's comodule instance is definitionally `Corestrict`; expose that
  -- identification once here so downstream proofs can rewrite by a named theorem.
  change (letI : Comodule R H₂ M := Corestrict φ.toCoalgHom
    pointsAction M g) = pointsAction M (BialgHom.mapDomain φ g)
  exact pointsAction_corestrict φ g

/-- Simp-normal form of `pointsAction_corestrict_obj`, with the precomposed point written
after normalization by `BialgHom.mapDomain_apply`. -/
-- Prefer this bundled normal form before `corestrict_obj_coe` exposes the carrier.
@[simp↓ high]
theorem pointsAction_corestrict_obj_toConv_comp (φ : H₁ →ₐc[R] H₂)
    (M : FGComoduleCat.{u, v, y} R H₁) (g : WithConv (H₂ →ₐ[R] A)) :
    pointsAction ((FGComoduleCat.corestrict φ.toCoalgHom).obj M) g =
      pointsAction M (toConv (g.ofConv.comp (φ : H₁ →ₐ[R] H₂))) := by
  simpa only [BialgHom.mapDomain_apply] using pointsAction_corestrict_obj φ M g

end HopfAlgebra

end Corestrict

end Comodule

end TauCeti
