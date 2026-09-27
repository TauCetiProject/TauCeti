/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.QuadraticForm.Transfer.Class
public import TauCeti.LinearAlgebra.QuadraticForm.Transfer.Frobenius
public import TauCeti.LinearAlgebra.QuadraticForm.Witt.BaseChange

/-!
# Scharlau transfer on Witt rings

Scharlau transfer along a nonzero linear functional sends hyperbolic forms to hyperbolic forms,
so its additive action on isometry classes descends to an additive homomorphism between Witt
rings. Frobenius reciprocity makes this homomorphism linear over the Witt ring of the base field,
where the source is regarded as a module by scalar extension.

Unlike scalar extension, Scharlau transfer is not generally multiplicative. It is therefore
packaged as an additive homomorphism, with the projection formula recording its module-linearity.

## Main definitions

* `TauCeti.WittRing.scharlauTransfer`: Scharlau transfer as an additive homomorphism on Witt
  rings.
* `TauCeti.WittRing.traceTransfer`: transfer along the algebra trace of a finite separable
  extension.

## Main results

* `TauCeti.RegularFormClass.scharlauTransfer_mul_baseChange`: Frobenius reciprocity on regular
  form classes.
* `TauCeti.RegularFormClass.scharlauTransfer_hyperbolicClass`: transfer of a hyperbolic plane is
  a sum of `[L : K]` hyperbolic planes.
* `TauCeti.WittRing.scharlauTransfer_wittClass`: the descended map agrees with form transfer.
* `TauCeti.WittRing.scharlauTransfer_baseChange_mul`: the projection formula on Witt rings.

## References

* W. Scharlau, *Quadratic and Hermitian Forms* (1985), Chapter 2, §5.
* T. Y. Lam, *Introduction to Quadratic Forms over Fields* (2005), Chapter VII, §1.
-/

public section
noncomputable section

open scoped TensorProduct
open QuadraticMap QuadraticForm

namespace TauCeti

universe u v w

variable {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [Invertible (2 : K)]

/-- **Frobenius reciprocity on regular-form classes.** Transfer of a class over `L` multiplied
by a scalar-extended class from `K` is the transfer multiplied by the original base class. -/
@[simp]
theorem RegularFormClass.scharlauTransfer_mul_baseChange (s : L →ₗ[K] K) (hs : s ≠ 0)
    (x : RegularFormClass L) (y : RegularFormClass K) :
    letI : Invertible (2 : L) :=
      (Invertible.map (algebraMap K L) 2).copy 2 (map_ofNat _ _).symm
    RegularFormClass.scharlauTransfer s hs (x * y.baseChange L) =
      RegularFormClass.scharlauTransfer s hs x * y := by
  let _ : Invertible (2 : L) :=
    (Invertible.map (algebraMap K L) 2).copy 2 (map_ofNat _ _).symm
  induction x using Quotient.inductionOn with
  | h p =>
    induction y using Quotient.inductionOn with
    | h q =>
      let _ : FiniteDimensional K
          ((Fin p.1 → L) ⊗[L] (L ⊗[K] (Fin q.1 → K))) :=
        FiniteDimensional.trans K L _
      rw [← formClass_presentedForm p, ← formClass_presentedForm q,
        ← QuadraticForm.formClass_baseChange, ← formClass_tmul,
        RegularFormClass.scharlauTransfer_formClass,
        RegularFormClass.scharlauTransfer_formClass, ← formClass_tmul]
      exact (formClass_eq_iff _ _ _ _).mpr
        ⟨QuadraticMap.IsometryEquiv.scharlauTransferTmulBaseChange
          (presentedForm p) (presentedForm q) s⟩

/-- Transfer of a hyperbolic plane over `L` is a sum of `[L : K]` hyperbolic planes over `K`.
This is the hyperbolic-preservation statement that makes transfer descend to Witt rings. -/
@[simp]
theorem RegularFormClass.scharlauTransfer_hyperbolicClass (s : L →ₗ[K] K) (hs : s ≠ 0) :
    letI : Invertible (2 : L) :=
      (Invertible.map (algebraMap K L) 2).copy 2 (map_ofNat _ _).symm
    RegularFormClass.scharlauTransfer s hs (hyperbolicClass L) =
      Module.finrank K L • hyperbolicClass K := by
  let _ : Invertible (2 : L) :=
    (Invertible.map (algebraMap K L) 2).copy 2 (map_ofNat _ _).symm
  calc
    RegularFormClass.scharlauTransfer s hs (hyperbolicClass L) =
        RegularFormClass.scharlauTransfer s hs
          (1 * RegularFormClass.baseChange L (hyperbolicClass K)) := by
            rw [one_mul, RegularFormClass.baseChange_hyperbolicClass]
    _ = RegularFormClass.scharlauTransfer s hs 1 * hyperbolicClass K :=
      RegularFormClass.scharlauTransfer_mul_baseChange s hs 1 (hyperbolicClass K)
    _ = RegularFormClass.rank (RegularFormClass.scharlauTransfer s hs 1) •
        hyperbolicClass K := RegularFormClass.mul_hyperbolicClass _
    _ = Module.finrank K L • hyperbolicClass K := by simp

/-- Scharlau transfer on Witt–Grothendieck rings. This is only an additive homomorphism:
transfer is not generally compatible with multiplication. -/
def WittGrothendieckRing.scharlauTransfer (s : L →ₗ[K] K) (hs : s ≠ 0) :
    letI : Invertible (2 : L) :=
      invertibleOfNonzero <| by
        rw [← map_ofNat (algebraMap K L) 2, ← map_zero (algebraMap K L)]
        exact (FaithfulSMul.algebraMap_injective K L).ne (Invertible.ne_zero (2 : K))
    WittGrothendieckRing L →+ WittGrothendieckRing K :=
  let _ : Invertible (2 : L) :=
    invertibleOfNonzero <| by
      rw [← map_ofNat (algebraMap K L) 2, ← map_zero (algebraMap K L)]
      exact (FaithfulSMul.algebraMap_injective K L).ne (Invertible.ne_zero (2 : K))
  (WittGrothendieckRing.equivGrothendieck (K := K)).symm.toAddEquiv.toAddMonoidHom.comp <|
    (Algebra.GrothendieckAddGroup.lift
      ((Algebra.GrothendieckAddGroup.of :
          RegularFormClass K →+ Algebra.GrothendieckAddGroup (RegularFormClass K)).comp
        (RegularFormClass.scharlauTransfer s hs))).comp
      (WittGrothendieckRing.equivGrothendieck (K := L)).toAddEquiv.toAddMonoidHom

/-- Transfer of the Witt–Grothendieck class of a form class is the class of its transfer. -/
@[simp]
theorem WittGrothendieckRing.scharlauTransfer_toWittGrothendieck (s : L →ₗ[K] K)
    (hs : s ≠ 0) (x : RegularFormClass L) :
    letI : Invertible (2 : L) :=
      invertibleOfNonzero <| by
        rw [← map_ofNat (algebraMap K L) 2, ← map_zero (algebraMap K L)]
        exact (FaithfulSMul.algebraMap_injective K L).ne (Invertible.ne_zero (2 : K))
    WittGrothendieckRing.scharlauTransfer s hs (toWittGrothendieck x) =
      toWittGrothendieck (RegularFormClass.scharlauTransfer s hs x) := by
  let _ : Invertible (2 : L) :=
    invertibleOfNonzero <| by
      rw [← map_ofNat (algebraMap K L) 2, ← map_zero (algebraMap K L)]
      exact (FaithfulSMul.algebraMap_injective K L).ne (Invertible.ne_zero (2 : K))
  apply (WittGrothendieckRing.equivGrothendieck (K := K)).injective
  rw [WittGrothendieckRing.scharlauTransfer, AddMonoidHom.comp_apply]
  -- Unfold the two Grothendieck equivalences so that `lift_apply_of` exposes the
  -- representative `x`; their additive coercions have no separate compatibility lemma.
  change
    (WittGrothendieckRing.equivGrothendieck (K := K))
        ((WittGrothendieckRing.equivGrothendieck (K := K)).symm
          ((Algebra.GrothendieckAddGroup.lift
            ((Algebra.GrothendieckAddGroup.of :
              RegularFormClass K →+ Algebra.GrothendieckAddGroup (RegularFormClass K)).comp
                (RegularFormClass.scharlauTransfer s hs)))
            ((WittGrothendieckRing.equivGrothendieck (K := L))
              (toWittGrothendieck x)))) = _
  rw [RingEquiv.apply_symm_apply, toWittGrothendieck_apply,
    Algebra.GrothendieckAddGroup.lift_apply_of, AddMonoidHom.comp_apply,
    toWittGrothendieck_apply]

/-- Scharlau transfer carries the hyperbolic ideal into the hyperbolic ideal. -/
theorem WittGrothendieckRing.scharlauTransfer_mem_hyperbolicIdeal (s : L →ₗ[K] K)
    (hs : s ≠ 0) {x : WittGrothendieckRing L} :
    letI : Invertible (2 : L) :=
      invertibleOfNonzero <| by
        rw [← map_ofNat (algebraMap K L) 2, ← map_zero (algebraMap K L)]
        exact (FaithfulSMul.algebraMap_injective K L).ne (Invertible.ne_zero (2 : K))
    x ∈ hyperbolicIdeal L →
    WittGrothendieckRing.scharlauTransfer s hs x ∈ hyperbolicIdeal K := by
  let _ : Invertible (2 : L) :=
    invertibleOfNonzero <| by
      rw [← map_ofNat (algebraMap K L) 2, ← map_zero (algebraMap K L)]
      exact (FaithfulSMul.algebraMap_injective K L).ne (Invertible.ne_zero (2 : K))
  intro hx
  obtain ⟨n, rfl⟩ := mem_hyperbolicIdeal_iff.mp hx
  have hhyper := RegularFormClass.scharlauTransfer_hyperbolicClass s hs
  have hinst : ((Invertible.map (algebraMap K L) 2).copy 2 (map_ofNat _ _).symm) =
      (inferInstance : Invertible (2 : L)) := Subsingleton.elim _ _
  rw [hinst] at hhyper
  rw [map_zsmul, WittGrothendieckRing.scharlauTransfer_toWittGrothendieck,
    hhyper, map_nsmul]
  apply mem_hyperbolicIdeal_iff.mpr
  refine ⟨n * Module.finrank K L, ?_⟩
  simp [mul_assoc]

private def WittRing.scharlauTransferDescentData (s : L →ₗ[K] K) (hs : s ≠ 0) :
    letI : Invertible (2 : L) :=
      invertibleOfNonzero <| by
        rw [← map_ofNat (algebraMap K L) 2, ← map_zero (algebraMap K L)]
        exact (FaithfulSMul.algebraMap_injective K L).ne (Invertible.ne_zero (2 : K))
    { f : WittGrothendieckRing L →+ WittRing K //
      (WittRing.mk (K := L)).toAddMonoidHom.ker ≤ f.ker } :=
  let _ : Invertible (2 : L) :=
    invertibleOfNonzero <| by
      rw [← map_ofNat (algebraMap K L) 2, ← map_zero (algebraMap K L)]
      exact (FaithfulSMul.algebraMap_injective K L).ne (Invertible.ne_zero (2 : K))
  ⟨(WittRing.mk (K := K)).toAddMonoidHom.comp
      (WittGrothendieckRing.scharlauTransfer s hs), fun x hx ↦ by
      rw [AddMonoidHom.mem_ker] at hx ⊢
      rw [AddMonoidHom.comp_apply]
      -- `RingHom.toAddMonoidHom` has the same underlying function as the ring homomorphism.
      change WittRing.mk (K := K) (WittGrothendieckRing.scharlauTransfer s hs x) = 0
      apply WittRing.mk_eq_zero_iff_mem.mpr
      apply WittGrothendieckRing.scharlauTransfer_mem_hyperbolicIdeal s hs
      exact WittRing.mk_eq_zero_iff_mem.mp hx⟩

/-- **Scharlau transfer on Witt rings.** Transfer along a nonzero `K`-linear functional
`s : L → K` descends to an additive homomorphism from `W(L)` to `W(K)`. -/
def WittRing.scharlauTransfer (s : L →ₗ[K] K) (hs : s ≠ 0) :
    letI : Invertible (2 : L) :=
      invertibleOfNonzero <| by
        rw [← map_ofNat (algebraMap K L) 2, ← map_zero (algebraMap K L)]
        exact (FaithfulSMul.algebraMap_injective K L).ne (Invertible.ne_zero (2 : K))
    WittRing L →+ WittRing K :=
  let _ : Invertible (2 : L) :=
    invertibleOfNonzero <| by
      rw [← map_ofNat (algebraMap K L) 2, ← map_zero (algebraMap K L)]
      exact (FaithfulSMul.algebraMap_injective K L).ne (Invertible.ne_zero (2 : K))
  (WittRing.mk (K := L)).toAddMonoidHom.liftOfSurjective WittRing.mk_surjective
      (WittRing.scharlauTransferDescentData s hs)

/-- Scharlau transfer commutes with the quotient map from the Witt–Grothendieck ring. -/
@[simp]
theorem WittRing.scharlauTransfer_mk (s : L →ₗ[K] K) (hs : s ≠ 0)
    (x : WittGrothendieckRing L) :
    letI : Invertible (2 : L) :=
      invertibleOfNonzero <| by
        rw [← map_ofNat (algebraMap K L) 2, ← map_zero (algebraMap K L)]
        exact (FaithfulSMul.algebraMap_injective K L).ne (Invertible.ne_zero (2 : K))
    WittRing.scharlauTransfer s hs (WittRing.mk x) =
      WittRing.mk (K := K) (WittGrothendieckRing.scharlauTransfer s hs x) := by
  let _ : Invertible (2 : L) :=
    invertibleOfNonzero <| by
      rw [← map_ofNat (algebraMap K L) 2, ← map_zero (algebraMap K L)]
      exact (FaithfulSMul.algebraMap_injective K L).ne (Invertible.ne_zero (2 : K))
  have hmk (z : WittGrothendieckRing L) :
      (WittRing.mk (K := L)).toAddMonoidHom z = WittRing.mk z := by
    exact DFunLike.congr_fun (RingHom.toAddMonoidHom_eq_coe (WittRing.mk (K := L))) z
  have hmk' (z : WittGrothendieckRing K) :
      (WittRing.mk (K := K)).toAddMonoidHom z = WittRing.mk z := by
    exact DFunLike.congr_fun (RingHom.toAddMonoidHom_eq_coe (WittRing.mk (K := K))) z
  rw [← hmk x, ← hmk' (WittGrothendieckRing.scharlauTransfer s hs x)]
  rw [WittRing.scharlauTransfer]
  unfold AddMonoidHom.liftOfSurjective
  simpa only [WittRing.scharlauTransferDescentData, AddMonoidHom.comp_apply,
    RingHom.toAddMonoidHom_eq_coe] using
      (AddMonoidHom.liftOfRightInverse_comp_apply
        (f := (WittRing.mk (K := L)).toAddMonoidHom)
        (f_neg := Function.surjInv WittRing.mk_surjective)
        (Function.rightInverse_surjInv WittRing.mk_surjective)
        (WittRing.scharlauTransferDescentData s hs) x)

/-- Scharlau transfer of the Witt class of a form class is the Witt class of its transfer. -/
@[simp]
theorem WittRing.scharlauTransfer_wittClass (s : L →ₗ[K] K) (hs : s ≠ 0)
    (x : RegularFormClass L) :
    letI : Invertible (2 : L) :=
      invertibleOfNonzero <| by
        rw [← map_ofNat (algebraMap K L) 2, ← map_zero (algebraMap K L)]
        exact (FaithfulSMul.algebraMap_injective K L).ne (Invertible.ne_zero (2 : K))
    WittRing.scharlauTransfer s hs (wittClass x) =
      wittClass (RegularFormClass.scharlauTransfer s hs x) := by
  let _ : Invertible (2 : L) :=
    invertibleOfNonzero <| by
      rw [← map_ofNat (algebraMap K L) 2, ← map_zero (algebraMap K L)]
      exact (FaithfulSMul.algebraMap_injective K L).ne (Invertible.ne_zero (2 : K))
  rw [wittClass_apply, wittClass_apply, WittRing.scharlauTransfer_mk,
    WittGrothendieckRing.scharlauTransfer_toWittGrothendieck]

/-- **Projection formula for Scharlau transfer on Witt rings.** Multiplication by a class from
the base field may be moved across transfer after scalar extension. -/
@[simp]
theorem WittRing.scharlauTransfer_baseChange_mul (s : L →ₗ[K] K) (hs : s ≠ 0)
    (a : WittRing K) :
    letI : Invertible (2 : L) :=
      invertibleOfNonzero <| by
        rw [← map_ofNat (algebraMap K L) 2, ← map_zero (algebraMap K L)]
        exact (FaithfulSMul.algebraMap_injective K L).ne (Invertible.ne_zero (2 : K))
    ∀ x : WittRing L,
    WittRing.scharlauTransfer s hs (WittRing.baseChange (L := L) a * x) =
      a * WittRing.scharlauTransfer s hs x := by
  let _ : Invertible (2 : L) :=
    invertibleOfNonzero <| by
      rw [← map_ofNat (algebraMap K L) 2, ← map_zero (algebraMap K L)]
      exact (FaithfulSMul.algebraMap_injective K L).ne (Invertible.ne_zero (2 : K))
  intro x
  obtain ⟨p, rfl⟩ := wittClass_surjective a
  obtain ⟨q, rfl⟩ := wittClass_surjective x
  rw [WittRing.baseChange_wittClass, ← map_mul, mul_comm,
    WittRing.scharlauTransfer_wittClass,
    RegularFormClass.scharlauTransfer_mul_baseChange,
    map_mul, mul_comm]
  rw [WittRing.scharlauTransfer_wittClass]

/-- Scharlau transfer bundled as a linear map over `W(K)`, with the `W(K)`-module structure on
`W(L)` induced by scalar extension. -/
def WittRing.scharlauTransferLinear (s : L →ₗ[K] K) (hs : s ≠ 0) :
    letI : Invertible (2 : L) :=
      invertibleOfNonzero <| by
        rw [← map_ofNat (algebraMap K L) 2, ← map_zero (algebraMap K L)]
        exact (FaithfulSMul.algebraMap_injective K L).ne (Invertible.ne_zero (2 : K))
    letI : Module (WittRing K) (WittRing L) :=
      Module.compHom (WittRing L) (WittRing.baseChange (L := L))
    WittRing L →ₗ[WittRing K] WittRing K := by
  letI : Invertible (2 : L) :=
    invertibleOfNonzero <| by
      rw [← map_ofNat (algebraMap K L) 2, ← map_zero (algebraMap K L)]
      exact (FaithfulSMul.algebraMap_injective K L).ne (Invertible.ne_zero (2 : K))
  letI : Module (WittRing K) (WittRing L) :=
    Module.compHom (WittRing L) (WittRing.baseChange (L := L))
  refine
    { __ := WittRing.scharlauTransfer s hs
      map_smul' := fun a x ↦ ?_ }
  -- The scalar action supplied by `Module.compHom` is multiplication after `baseChange`.
  change WittRing.scharlauTransfer s hs (WittRing.baseChange (L := L) a * x) = _
  exact WittRing.scharlauTransfer_baseChange_mul s hs a x

/-- The linear-map packaging of Scharlau transfer has the same underlying function. -/
@[simp]
theorem WittRing.scharlauTransferLinear_apply (s : L →ₗ[K] K) (hs : s ≠ 0)
    :
    letI : Invertible (2 : L) :=
      invertibleOfNonzero <| by
        rw [← map_ofNat (algebraMap K L) 2, ← map_zero (algebraMap K L)]
        exact (FaithfulSMul.algebraMap_injective K L).ne (Invertible.ne_zero (2 : K))
    ∀ x : WittRing L,
    letI : Module (WittRing K) (WittRing L) :=
      Module.compHom (WittRing L) (WittRing.baseChange (L := L))
    WittRing.scharlauTransferLinear s hs x = WittRing.scharlauTransfer s hs x := by
  let _ : Invertible (2 : L) :=
    invertibleOfNonzero <| by
      rw [← map_ofNat (algebraMap K L) 2, ← map_zero (algebraMap K L)]
      exact (FaithfulSMul.algebraMap_injective K L).ne (Invertible.ne_zero (2 : K))
  intro x
  rfl

/-- Scharlau transfer along the identity functional is the identity on the Witt ring. -/
@[simp]
theorem WittRing.scharlauTransfer_id :
    letI : Invertible (2 : K) := invertibleOfNonzero (Invertible.ne_zero (2 : K))
    WittRing.scharlauTransfer (LinearMap.id : K →ₗ[K] K) one_ne_zero =
      AddMonoidHom.id (WittRing K) := by
  let _ : Invertible (2 : K) := invertibleOfNonzero (Invertible.ne_zero (2 : K))
  ext x
  obtain ⟨q, rfl⟩ := wittClass_surjective x
  simp

section Tower

variable {E : Type w} [Field E] [Algebra L E] [Algebra K E] [IsScalarTower K L E]
  [FiniteDimensional L E]

/-- Scharlau transfers on Witt rings compose through a tower of finite field extensions. -/
@[simp]
theorem WittRing.scharlauTransfer_comp (s : L →ₗ[K] K) (hs : s ≠ 0)
    (t : E →ₗ[L] L) (ht : t ≠ 0) :
    letI : FiniteDimensional K E := FiniteDimensional.trans K L E
    letI : Invertible (2 : L) :=
      invertibleOfNonzero <| by
        rw [← map_ofNat (algebraMap K L) 2, ← map_zero (algebraMap K L)]
        exact (FaithfulSMul.algebraMap_injective K L).ne (Invertible.ne_zero (2 : K))
    letI : Invertible (2 : E) :=
      invertibleOfNonzero <| by
        rw [← map_ofNat (algebraMap K E) 2, ← map_zero (algebraMap K E)]
        exact (FaithfulSMul.algebraMap_injective K E).ne (Invertible.ne_zero (2 : K))
    (WittRing.scharlauTransfer s hs).comp (WittRing.scharlauTransfer t ht) =
      WittRing.scharlauTransfer (s.comp (t.restrictScalars K))
        (s.comp_restrictScalars_ne_zero t hs ht) := by
  let _ : FiniteDimensional K E := FiniteDimensional.trans K L E
  let _ : Invertible (2 : L) :=
    invertibleOfNonzero <| by
      rw [← map_ofNat (algebraMap K L) 2, ← map_zero (algebraMap K L)]
      exact (FaithfulSMul.algebraMap_injective K L).ne (Invertible.ne_zero (2 : K))
  let _ : Invertible (2 : E) :=
    invertibleOfNonzero <| by
      rw [← map_ofNat (algebraMap K E) 2, ← map_zero (algebraMap K E)]
      exact (FaithfulSMul.algebraMap_injective K E).ne (Invertible.ne_zero (2 : K))
  ext x
  obtain ⟨q, rfl⟩ := wittClass_surjective x
  rw [AddMonoidHom.comp_apply, WittRing.scharlauTransfer_wittClass,
    WittRing.scharlauTransfer_wittClass, WittRing.scharlauTransfer_wittClass]
  have h := DFunLike.congr_fun (RegularFormClass.scharlauTransfer_comp s hs t ht) q
  have hinst : ((Invertible.map (algebraMap K L) 2).copy 2 (map_ofNat _ _).symm) =
      (inferInstance : Invertible (2 : L)) := Subsingleton.elim _ _
  rw [hinst] at h
  rw [AddMonoidHom.comp_apply] at h
  exact congrArg wittClass h

end Tower

variable [Algebra.IsSeparable K L]

/-- Trace transfer on Witt rings for a finite separable field extension. -/
def WittRing.traceTransfer :
    letI : Invertible (2 : L) :=
      invertibleOfNonzero <| by
        rw [← map_ofNat (algebraMap K L) 2, ← map_zero (algebraMap K L)]
        exact (FaithfulSMul.algebraMap_injective K L).ne (Invertible.ne_zero (2 : K))
    WittRing L →+ WittRing K :=
  let _ : Invertible (2 : L) :=
    invertibleOfNonzero <| by
      rw [← map_ofNat (algebraMap K L) 2, ← map_zero (algebraMap K L)]
      exact (FaithfulSMul.algebraMap_injective K L).ne (Invertible.ne_zero (2 : K))
  WittRing.scharlauTransfer (Algebra.trace K L) (Algebra.trace_ne_zero K L)

/-- Trace transfer of a Witt class is the Witt class of the class-level trace transfer. -/
@[simp]
theorem WittRing.traceTransfer_wittClass (x : RegularFormClass L) :
    letI : Invertible (2 : L) :=
      invertibleOfNonzero <| by
        rw [← map_ofNat (algebraMap K L) 2, ← map_zero (algebraMap K L)]
        exact (FaithfulSMul.algebraMap_injective K L).ne (Invertible.ne_zero (2 : K))
    WittRing.traceTransfer (K := K) (L := L) (wittClass x) =
      wittClass (RegularFormClass.traceTransfer K x) := by
  let _ : Invertible (2 : L) :=
    invertibleOfNonzero <| by
      rw [← map_ofNat (algebraMap K L) 2, ← map_zero (algebraMap K L)]
      exact (FaithfulSMul.algebraMap_injective K L).ne (Invertible.ne_zero (2 : K))
  rw [WittRing.traceTransfer, WittRing.scharlauTransfer_wittClass,
    RegularFormClass.traceTransfer_eq_scharlauTransfer]

end TauCeti
