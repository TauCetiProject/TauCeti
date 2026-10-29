/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.QuadraticForm.Transfer.Class.Frobenius
public import TauCeti.LinearAlgebra.QuadraticForm.Witt.BaseChange

/-!
# Scharlau transfer on Witt rings

Scharlau transfer along a nonzero linear functional sends hyperbolic forms to hyperbolic forms,
so its additive action on isometry classes descends to an additive homomorphism between Witt
rings. Frobenius reciprocity makes this homomorphism linear over the Witt ring of the base field,
where the source is regarded as a module by scalar extension.

Unlike scalar extension, Scharlau transfer is not generally multiplicative. It is therefore
packaged as an additive homomorphism, with the projection formula recording its module-linearity.

Throughout, the Witt ring of an extension field is formed with respect to the invertibility of `2`
supplied by `TauCeti.invertibleTwoOfBaseField`.

## Main definitions

* `TauCeti.WittRing.scharlauTransfer`: Scharlau transfer as an additive homomorphism on Witt
  rings.
* `TauCeti.WittRing.traceTransfer`: transfer along the algebra trace of a finite separable
  extension.

## Main results

* `TauCeti.WittRing.scharlauTransfer_wittClass`: the descended map agrees with form transfer.
* `TauCeti.WittRing.scharlauTransfer_baseChange_mul`: the projection formula on Witt rings.
* `TauCeti.WittRing.scharlauTransfer_comp`: transfers compose in a tower of extensions.
* `TauCeti.WittRing.traceTransfer_eq_scharlauTransfer`: trace transfer is Scharlau transfer along
  the algebra trace.

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

/-- Invertibility of `2` in an extension field, induced from the base field. Every Witt ring in
this module is formed with respect to this instance.

The inverse is taken in the extension rather than transported along `algebraMap K L`, so that the
resulting instance does not mention the base field: the tower law compares the instances obtained
over `K` and over an intermediate field. -/
@[expose, instance_reducible]
def invertibleTwoOfBaseField (K : Type*) (L : Type*) [Field K] [Field L] [Algebra K L]
    [Invertible (2 : K)] : Invertible (2 : L) :=
  invertibleOfNonzero <|
    letI : Invertible (2 : L) := (Invertible.map (algebraMap K L) 2).copy 2 (map_ofNat _ _).symm
    Invertible.ne_zero (2 : L)

/-- Scharlau transfer on Witt–Grothendieck rings. This is only an additive homomorphism:
transfer is not generally compatible with multiplication. -/
def WittGrothendieckRing.scharlauTransfer (s : L →ₗ[K] K) (hs : s ≠ 0) :
    letI : Invertible (2 : L) := invertibleTwoOfBaseField K L
    WittGrothendieckRing L →+ WittGrothendieckRing K :=
  let _ : Invertible (2 : L) := invertibleTwoOfBaseField K L
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
    letI : Invertible (2 : L) := invertibleTwoOfBaseField K L
    WittGrothendieckRing.scharlauTransfer s hs (toWittGrothendieck x) =
      toWittGrothendieck (RegularFormClass.scharlauTransfer s hs x) := by
  let _ : Invertible (2 : L) := invertibleTwoOfBaseField K L
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
    letI : Invertible (2 : L) := invertibleTwoOfBaseField K L
    x ∈ hyperbolicIdeal L →
    WittGrothendieckRing.scharlauTransfer s hs x ∈ hyperbolicIdeal K := by
  let _ : Invertible (2 : L) := invertibleTwoOfBaseField K L
  intro hx
  obtain ⟨n, rfl⟩ := mem_hyperbolicIdeal_iff.mp hx
  have hhyper := RegularFormClass.scharlauTransfer_hyperbolicClass s hs
  -- `Transfer/Class/Frobenius` states its result for the transported instance; `Invertible` is a
  -- subsingleton, so it agrees with the instance used here.
  rw [Subsingleton.elim ((Invertible.map (algebraMap K L) 2).copy 2 (map_ofNat _ _).symm)
    (invertibleTwoOfBaseField K L)] at hhyper
  rw [map_zsmul, WittGrothendieckRing.scharlauTransfer_toWittGrothendieck,
    hhyper, map_nsmul]
  apply mem_hyperbolicIdeal_iff.mpr
  refine ⟨n * Module.finrank K L, ?_⟩
  simp [mul_assoc]

private def WittRing.scharlauTransferDescentData (s : L →ₗ[K] K) (hs : s ≠ 0) :
    letI : Invertible (2 : L) := invertibleTwoOfBaseField K L
    { f : WittGrothendieckRing L →+ WittRing K //
      (WittRing.mk (K := L)).toAddMonoidHom.ker ≤ f.ker } :=
  let _ : Invertible (2 : L) := invertibleTwoOfBaseField K L
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
    letI : Invertible (2 : L) := invertibleTwoOfBaseField K L
    WittRing L →+ WittRing K :=
  let _ : Invertible (2 : L) := invertibleTwoOfBaseField K L
  (WittRing.mk (K := L)).toAddMonoidHom.liftOfSurjective WittRing.mk_surjective
      (WittRing.scharlauTransferDescentData s hs)

/-- Scharlau transfer commutes with the quotient map from the Witt–Grothendieck ring. -/
@[simp]
theorem WittRing.scharlauTransfer_mk (s : L →ₗ[K] K) (hs : s ≠ 0)
    (x : WittGrothendieckRing L) :
    letI : Invertible (2 : L) := invertibleTwoOfBaseField K L
    WittRing.scharlauTransfer s hs (WittRing.mk x) =
      WittRing.mk (K := K) (WittGrothendieckRing.scharlauTransfer s hs x) := by
  let _ : Invertible (2 : L) := invertibleTwoOfBaseField K L
  have hmk (z : WittGrothendieckRing L) :
      (WittRing.mk (K := L)).toAddMonoidHom z = WittRing.mk z := by
    exact DFunLike.congr_fun (RingHom.toAddMonoidHom_eq_coe (WittRing.mk (K := L))) z
  have hmk' (z : WittGrothendieckRing K) :
      (WittRing.mk (K := K)).toAddMonoidHom z = WittRing.mk z := by
    exact DFunLike.congr_fun (RingHom.toAddMonoidHom_eq_coe (WittRing.mk (K := K))) z
  rw [← hmk x, ← hmk' (WittGrothendieckRing.scharlauTransfer s hs x),
    WittRing.scharlauTransfer]
  exact AddMonoidHom.liftOfRightInverse_comp_apply _ _ _ _ x

/-- Scharlau transfer of the Witt class of a form class is the Witt class of its transfer. -/
@[simp]
theorem WittRing.scharlauTransfer_wittClass (s : L →ₗ[K] K) (hs : s ≠ 0)
    (x : RegularFormClass L) :
    letI : Invertible (2 : L) := invertibleTwoOfBaseField K L
    WittRing.scharlauTransfer s hs (wittClass x) =
      wittClass (RegularFormClass.scharlauTransfer s hs x) := by
  let _ : Invertible (2 : L) := invertibleTwoOfBaseField K L
  rw [wittClass_apply, wittClass_apply, WittRing.scharlauTransfer_mk,
    WittGrothendieckRing.scharlauTransfer_toWittGrothendieck]

/-- **Projection formula for Scharlau transfer on Witt rings.** Multiplication by a class from
the base field may be moved across transfer after scalar extension. -/
@[simp]
theorem WittRing.scharlauTransfer_baseChange_mul (s : L →ₗ[K] K) (hs : s ≠ 0)
    (a : WittRing K) :
    letI : Invertible (2 : L) := invertibleTwoOfBaseField K L
    ∀ x : WittRing L,
    WittRing.scharlauTransfer s hs (WittRing.baseChange (L := L) a * x) =
      a * WittRing.scharlauTransfer s hs x := by
  let _ : Invertible (2 : L) := invertibleTwoOfBaseField K L
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
    letI : Invertible (2 : L) := invertibleTwoOfBaseField K L
    letI : Module (WittRing K) (WittRing L) :=
      Module.compHom (WittRing L) (WittRing.baseChange (L := L))
    WittRing L →ₗ[WittRing K] WittRing K := by
  letI : Invertible (2 : L) := invertibleTwoOfBaseField K L
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
    letI : Invertible (2 : L) := invertibleTwoOfBaseField K L
    ∀ x : WittRing L,
    letI : Module (WittRing K) (WittRing L) :=
      Module.compHom (WittRing L) (WittRing.baseChange (L := L))
    WittRing.scharlauTransferLinear s hs x = WittRing.scharlauTransfer s hs x := by
  let _ : Invertible (2 : L) := invertibleTwoOfBaseField K L
  intro x
  rfl

/-- Scharlau transfer along the identity functional is the identity on the Witt ring. -/
@[simp]
theorem WittRing.scharlauTransfer_id :
    letI : Invertible (2 : K) := invertibleTwoOfBaseField K K
    WittRing.scharlauTransfer (LinearMap.id : K →ₗ[K] K) one_ne_zero =
      AddMonoidHom.id (WittRing K) := by
  let _ : Invertible (2 : K) := invertibleTwoOfBaseField K K
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
    letI : Invertible (2 : L) := invertibleTwoOfBaseField K L
    letI : Invertible (2 : E) := invertibleTwoOfBaseField K E
    (WittRing.scharlauTransfer s hs).comp (WittRing.scharlauTransfer t ht) =
      WittRing.scharlauTransfer (s.comp (t.restrictScalars K))
        (s.comp_restrictScalars_ne_zero t hs ht) := by
  let _ : FiniteDimensional K E := FiniteDimensional.trans K L E
  let _ : Invertible (2 : L) := invertibleTwoOfBaseField K L
  let _ : Invertible (2 : E) := invertibleTwoOfBaseField K E
  ext x
  obtain ⟨q, rfl⟩ := wittClass_surjective x
  rw [AddMonoidHom.comp_apply, WittRing.scharlauTransfer_wittClass,
    WittRing.scharlauTransfer_wittClass, WittRing.scharlauTransfer_wittClass]
  have h := DFunLike.congr_fun (RegularFormClass.scharlauTransfer_comp s hs t ht) q
  -- As above, the class-level statement uses the transported instance.
  rw [Subsingleton.elim ((Invertible.map (algebraMap K L) 2).copy 2 (map_ofNat _ _).symm)
    (invertibleTwoOfBaseField K L)] at h
  rw [AddMonoidHom.comp_apply] at h
  exact congrArg wittClass h

end Tower

variable [Algebra.IsSeparable K L]

/-- Trace transfer on Witt rings for a finite separable field extension. -/
def WittRing.traceTransfer :
    letI : Invertible (2 : L) := invertibleTwoOfBaseField K L
    WittRing L →+ WittRing K :=
  let _ : Invertible (2 : L) := invertibleTwoOfBaseField K L
  WittRing.scharlauTransfer (Algebra.trace K L) (Algebra.trace_ne_zero K L)

/-- Trace transfer on Witt rings is Scharlau transfer along the algebra trace. This makes the
generic transfer results — the projection formula and the tower law — available for trace
transfer. -/
theorem WittRing.traceTransfer_eq_scharlauTransfer :
    letI : Invertible (2 : L) := invertibleTwoOfBaseField K L
    WittRing.traceTransfer (K := K) (L := L) =
      WittRing.scharlauTransfer (Algebra.trace K L) (Algebra.trace_ne_zero K L) := by
  let _ : Invertible (2 : L) := invertibleTwoOfBaseField K L
  rfl

/-- Trace transfer of a Witt class is the Witt class of the class-level trace transfer. -/
@[simp]
theorem WittRing.traceTransfer_wittClass (x : RegularFormClass L) :
    letI : Invertible (2 : L) := invertibleTwoOfBaseField K L
    WittRing.traceTransfer (K := K) (L := L) (wittClass x) =
      wittClass (RegularFormClass.traceTransfer K x) := by
  let _ : Invertible (2 : L) := invertibleTwoOfBaseField K L
  rw [WittRing.traceTransfer_eq_scharlauTransfer, WittRing.scharlauTransfer_wittClass,
    RegularFormClass.traceTransfer_eq_scharlauTransfer]

end TauCeti
