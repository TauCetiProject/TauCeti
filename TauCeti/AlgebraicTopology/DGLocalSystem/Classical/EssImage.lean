/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.DGLocalSystem.Classical.Full
public import TauCeti.AlgebraicTopology.LocalCoefficient.Representation

/-!
# The essential image of classical local systems

On a path-connected pointed space `(X, x)`, the DG local systems over `C_*(Ω_x X; R)` isomorphic
to the DG local system of a classical local system are exactly those concentrated in degree zero.
Together with full faithfulness, the functor from classical local systems is an equivalence onto
the DG local systems concentrated in degree zero.

Let `M` be a DG local system concentrated in degree zero.  Its differential vanishes, chains of
positive dimension act on it by zero for degree reasons, and so do boundaries of `1`-chains, by
the Leibniz rule.  Since the kernel of `loopChainToGroupAlgebra` consists of chains whose
`0`-dimensional component is a boundary (`loopZeroChainToGroupAlgebra_eq_zero_iff`), the action
factors through the group ring `R[π₁(X, x)]`, so it is a representation of `π₁(X, x)`
(`DGRightModuleCat.IsConcentratedInDegreeZero.representation`).  The local system of that
representation (`LocalCoefficientSystem.ofRepresentation`) has fiber `M` at `x`, and its DG local
system is `M`.

## Main definitions

* `TauCeti.DGRightModuleCat.IsConcentratedInDegreeZero.representation`: the representation of
  `π₁(X, x)` on a DG local system concentrated in degree zero.
* `TauCeti.DGRightModuleCat.IsConcentratedInDegreeZero.classicalDGLocalSystemIso`: such a DG local
  system is the DG local system of the local system of that representation.
* `TauCeti.classicalDGLocalSystemEquivalence`: on a path-connected space, classical local systems
  are equivalent to the DG local systems concentrated in degree zero.

## Main results

* `TauCeti.isConcentratedInDegreeZero_classicalDGLocalSystem`: the DG local system of a classical
  local system is concentrated in degree zero.
* `TauCeti.essImage_classicalDGLocalSystemFunctor`: on a path-connected space, the essential image
  of the functor from classical local systems is the DG local systems concentrated in degree zero.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, Chapters 2 and 7.
* G. W. Whitehead, *Elements of Homotopy Theory*, Graduate Texts in Mathematics 61, Springer,
  1978, Chapter VI, §1 (local systems on a path-connected space and `π₁`-modules).
-/

public section

noncomputable section

open CategoryTheory MulOpposite

namespace TauCeti

universe u w

variable {R : Type u} [CommRing R] {X : TopCat.{u}} {x : X}

/-- The DG local system of a classical local system is concentrated in degree zero. -/
theorem isConcentratedInDegreeZero_classicalDGLocalSystem
    (L : LocalCoefficientSystem.{u, u, w} R X) :
    (classicalDGLocalSystem x L).IsConcentratedInDegreeZero :=
  DGRightModuleCat.isConcentratedInDegreeZero_iff.2 fun _ hq ↦ trivialGrading_eq_bot R _ hq

namespace DGRightModuleCat.IsConcentratedInDegreeZero

variable {M : DGLocalSystem.{w} X x R} (hM : M.IsConcentratedInDegreeZero)
include hM

/-- On a DG local system concentrated in degree zero, a chain acts through its component of
dimension zero. -/
theorem op_smul_eq_op_smul_lof_zero (a : loopChainAlgebra X x R) (m : M) :
    op a • m = op (cubicalChainLof (MooreLoopSpace X x) R 0 (a 0)) • m := by
  induction a using DirectSum.induction_on with
  | zero => simp
  | of n y =>
    cases n with
    | zero => rw [DirectSum.of_eq_same, cubicalChainLof, DirectSum.lof_eq_of]
    | succ k =>
      rw [DirectSum.of_eq_of_ne _ _ _ k.succ_ne_zero.symm, map_zero, op_zero, zero_smul,
        ← DirectSum.lof_eq_of R]
      exact hM.op_smul_eq_zero (by omega) (cubicalChainLof_mem _ _ y) m
  | add a b ha hb =>
    rw [MulOpposite.op_add, add_smul, ha, hb, DirectSum.add_apply, map_add, MulOpposite.op_add,
      add_smul]

/-- On a DG local system concentrated in degree zero, the chains in the kernel of the degree-zero
ring map act by zero: their component of dimension zero is a boundary. -/
theorem op_smul_eq_zero_of_loopChainToGroupAlgebra_eq_zero {a : loopChainAlgebra X x R}
    (ha : loopChainToGroupAlgebra X x R a = 0) (m : M) : op a • m = 0 := by
  rw [loopChainToGroupAlgebra_apply, loopZeroChainToGroupAlgebra_eq_zero_iff] at ha
  obtain ⟨c, hc⟩ := ha
  rw [hM.op_smul_eq_op_smul_lof_zero, ← hc, ← cubicalChainDifferential_lof_succ]
  exact hM.op_smul_d_eq_zero _ m

omit hM in
/-- The right action of the chain algebra on a DG local system, as an algebra map to the opposite
of the endomorphism algebra. -/
private def opAction (M : DGLocalSystem.{w} X x R) :
    loopChainAlgebra X x R →ₐ[R] (Module.End R M)ᵐᵒᵖ :=
  (AlgHom.op (Algebra.lsmul R R M)).comp (AlgEquiv.opOp R (loopChainAlgebra X x R)).toAlgHom

omit hM in
/-- The algebra map `opAction` is the right action. -/
private theorem opAction_apply (a : loopChainAlgebra X x R) (m : M) :
    (opAction M a).unop m = op a • m :=
  (rfl)

/-- **The action of the group ring on a DG local system concentrated in degree zero**: the right
action of the chain algebra factors through the degree-zero ring map, which is surjective. -/
def groupAlgebraAction :
    MonoidAlgebra R (FundamentalGroup X x) →ₐ[R] (Module.End R M)ᵐᵒᵖ :=
  (Ideal.Quotient.liftₐ (RingHom.ker (loopChainToGroupAlgebra X x R)) (opAction M)
      fun a ha ↦ unop_injective (LinearMap.ext fun m ↦ (opAction_apply a m).trans
        (hM.op_smul_eq_zero_of_loopChainToGroupAlgebra_eq_zero ha m))).comp
    (Ideal.quotientKerAlgEquivOfSurjective loopChainToGroupAlgebra_surjective).symm.toAlgHom

/-- A chain acts through its image in the group ring. -/
@[simp]
theorem groupAlgebraAction_loopChainToGroupAlgebra (a : loopChainAlgebra X x R) (m : M) :
    (hM.groupAlgebraAction (loopChainToGroupAlgebra X x R a)).unop m = op a • m := by
  rw [groupAlgebraAction, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
    Ideal.quotientKerAlgEquivOfSurjective_symm_apply, ← Ideal.Quotient.mkₐ_eq_mk R,
    ← AlgHom.comp_apply, Ideal.Quotient.liftₐ_comp]
  exact opAction_apply a m

/-- **The representation of the fundamental group on a DG local system concentrated in degree
zero**: a class `g` acts as the group ring element `g⁻¹` does from the right, so that the
classical DG local system of this representation is the given one. -/
def representation : Representation R (FundamentalGroup X x) M where
  toFun g := (hM.groupAlgebraAction (MonoidAlgebra.of R _ g⁻¹)).unop
  map_one' := by rw [inv_one, map_one, map_one, unop_one]
  map_mul' g h := by rw [mul_inv_rev, map_mul, map_mul, unop_mul]

/-- A class `g` acts as the group ring element `g⁻¹` does from the right. -/
theorem representation_apply (g : FundamentalGroup X x) :
    hM.representation g = (hM.groupAlgebraAction (MonoidAlgebra.of R _ g⁻¹)).unop :=
  (rfl)

/-- The right action of the fundamental group on the fiber of the local system of the
representation is the action of the group ring. -/
theorem lift_fiberRightAction_ofRepresentation [PathConnectedSpace X] :
    MonoidAlgebra.lift R (Module.End R ((LocalCoefficientSystem.ofRepresentation x
        hM.representation).obj (FundamentalGroupoid.mk x)))ᵐᵒᵖ (FundamentalGroup X x)
        (LocalCoefficientSystem.fiberRightAction
          (LocalCoefficientSystem.ofRepresentation x hM.representation)) =
      hM.groupAlgebraAction :=
  MonoidAlgebra.algHom_ext (fun g ↦ by
    rw [MonoidAlgebra.lift_single, one_smul, LocalCoefficientSystem.fiberRightAction_apply,
      LocalCoefficientSystem.monodromyRepresentation_ofRepresentation]
    change op (hM.groupAlgebraAction (MonoidAlgebra.of R _ g⁻¹⁻¹)).unop = _
    rw [inv_inv, op_unop, MonoidAlgebra.of_apply]
    rfl) (Subsingleton.elim _ _)

/-- The chain algebra acts on the fiber of the local system of the representation as it acts on
the given DG local system. -/
@[simp]
theorem classicalAction_ofRepresentation [PathConnectedSpace X] (a : (loopChainAlgebra X x R)ᵐᵒᵖ)
    (m : M) :
    classicalAction (LocalCoefficientSystem.ofRepresentation x hM.representation) a m = a • m := by
  rw [← op_unop a, classicalAction_op_apply, hM.lift_fiberRightAction_ofRepresentation]
  exact hM.groupAlgebraAction_loopChainToGroupAlgebra a.unop m

/-- **A DG local system concentrated in degree zero is classical**: on a path-connected space, it
is the DG local system of the local system of its representation of the fundamental group. -/
def classicalDGLocalSystemIso [PathConnectedSpace X] :
    classicalDGLocalSystem x (LocalCoefficientSystem.ofRepresentation x hM.representation) ≅ M :=
  DGRightModuleCat.isoMk
    { toFun m := m
      invFun m := m
      map_add' _ _ := rfl
      map_smul' := hM.classicalAction_ofRepresentation
      left_inv _ := rfl
      right_inv _ := rfl }
    (fun _ _ ↦ (mem_trivialGrading_iff R ((LocalCoefficientSystem.ofRepresentation x
      hM.representation).obj (FundamentalGroupoid.mk x))).trans hM.mem_grading_iff.symm)
    (fun m ↦ by rw [hM.differential_eq_zero]; rfl)

/-- The inverse of `classicalDGLocalSystemIso` is the identity of the underlying module. -/
@[simp]
theorem classicalDGLocalSystemIso_inv_apply [PathConnectedSpace X] (m : M) :
    hM.classicalDGLocalSystemIso.inv m = m := by
  rw [classicalDGLocalSystemIso]
  exact DGRightModuleCat.isoMk_inv_apply _ _ _ m

/-- `classicalDGLocalSystemIso` is the identity of the underlying module. -/
@[simp]
theorem classicalDGLocalSystemIso_hom_apply [PathConnectedSpace X] (m : M) :
    hM.classicalDGLocalSystemIso.hom m = m :=
  calc hM.classicalDGLocalSystemIso.hom m
      = hM.classicalDGLocalSystemIso.hom (hM.classicalDGLocalSystemIso.inv m) := by
        rw [classicalDGLocalSystemIso_inv_apply]
    _ = m := by rw [← DGRightModuleCat.comp_apply, Iso.inv_hom_id, DGRightModuleCat.id_apply]

end DGRightModuleCat.IsConcentratedInDegreeZero

variable [PathConnectedSpace X]

/-- **The essential image of classical local systems**: on a path-connected space, a DG local
system is isomorphic to the DG local system of a classical local system exactly when it is
concentrated in degree zero. -/
theorem essImage_classicalDGLocalSystemFunctor :
    (classicalDGLocalSystemFunctor.{u, w} R x).essImage =
      DGRightModuleCat.IsConcentratedInDegreeZero := by
  funext M
  refine propext ⟨fun ⟨L, ⟨e⟩⟩ ↦ (isConcentratedInDegreeZero_classicalDGLocalSystem L).of_iso e,
    fun hM ↦ ⟨_, ⟨hM.classicalDGLocalSystemIso⟩⟩⟩

variable (R x) in
/-- **Classical local systems are the DG local systems concentrated in degree zero**: on a
path-connected space, the functor from classical local systems is an equivalence onto the full
subcategory of DG local systems concentrated in degree zero. -/
def classicalDGLocalSystemEquivalence :
    LocalCoefficientSystem.{u, u, w} R X ≌
      ObjectProperty.FullSubcategory (DGRightModuleCat.IsConcentratedInDegreeZero :
        ObjectProperty (DGLocalSystem.{w} X x R)) :=
  let hF := ((classicalDGLocalSystemFunctorFullyFaithful.{u, w} R x).ofIso
    (ObjectProperty.liftCompιIso _ _ isConcentratedInDegreeZero_classicalDGLocalSystem).symm
    ).ofCompFaithful
  haveI := hF.full
  haveI := hF.faithful
  haveI : (ObjectProperty.lift _ (classicalDGLocalSystemFunctor.{u, w} R x)
      isConcentratedInDegreeZero_classicalDGLocalSystem).EssSurj :=
    ⟨fun N ↦ ⟨_, ⟨ObjectProperty.fullyFaithfulι _ |>.preimageIso
      N.property.classicalDGLocalSystemIso⟩⟩⟩
  haveI : (ObjectProperty.lift _ (classicalDGLocalSystemFunctor.{u, w} R x)
      isConcentratedInDegreeZero_classicalDGLocalSystem).IsEquivalence := { }
  (ObjectProperty.lift _ (classicalDGLocalSystemFunctor.{u, w} R x)
    isConcentratedInDegreeZero_classicalDGLocalSystem).asEquivalence

/-- The functor of the equivalence is the functor to DG local systems, with values in the full
subcategory of those concentrated in degree zero. -/
@[simp]
theorem classicalDGLocalSystemEquivalence_functor :
    (classicalDGLocalSystemEquivalence R x).functor =
      ObjectProperty.lift _ (classicalDGLocalSystemFunctor.{u, w} R x)
        isConcentratedInDegreeZero_classicalDGLocalSystem :=
  (rfl)

end TauCeti
