/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Central.Basic
public import TauCeti.Algebra.AlgebraicGroup.Connected.CommHopfAlgCat
public import Mathlib.RingTheory.Nilpotent.GeometricallyReduced
import TauCeti.Algebra.AlgebraicGroup.Center.BaseChange
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Normal.BaseChange
import TauCeti.RingTheory.Etale.Reduced
import TauCeti.RingTheory.FiniteType.Tensor.PointSeparation
import TauCeti.RingTheory.Idempotents.Connected.Pi
import Mathlib.RingTheory.TotallySplit

/-!
# Finite étale normal subgroups are central

A finite geometrically reduced normal subgroup of a geometrically connected affine group is
central over any field. This includes every finite étale normal subgroup.

Over an algebraically closed field the subgroup is a finite disjoint union of points.
For each of these points, conjugation by the universal ambient point defines a map from the
connected ambient group to this disjoint union. It is constant, and evaluation at the identity
determines its value. Point separation on the finite reduced subgroup yields scheme-theoretic
centrality. Descent from the algebraic closure gives the result over an arbitrary field.

## References

* J. S. Milne, *Algebraic Groups* (2017), Remark 12.39(a).
-/

public section

open CategoryTheory WithConv
open scoped TensorProduct

namespace TauCeti.HopfIdeal

universe u

section AlgebraicallyClosed

variable {k : Type u} [Field k] [IsAlgClosed k]
  {H : _root_.CommHopfAlgCat.{u} k}
  [ConnectedSpace (PrimeSpectrum H)] {I : HopfIdeal k H}
  [Module.Finite k (CommHopfAlgCat.quotient H I)] [IsReduced (CommHopfAlgCat.quotient H I)]

private theorem conjugate_generic_eq (hI : I.IsNormal) (t : WithConv (H →ₐ[k] k))
    (ht : t ∈ CommHopfAlgCat.quotientPointsSubgroup H I (CommAlgCat.of k k)) :
    toConv (AlgHom.id k H) * AlgHom.mapValue (Algebra.ofId k H) t *
      (toConv (AlgHom.id k H))⁻¹ = AlgHom.mapValue (Algebra.ofId k H) t := by
  let tH := AlgHom.mapValue (Algebra.ofId k H) t
  let generic := toConv (AlgHom.id k H)
  let p := generic * tH * generic⁻¹
  have htH : tH ∈ CommHopfAlgCat.quotientPointsSubgroup H I (CommAlgCat.of k H) := by
    rw [CommHopfAlgCat.mem_quotientPointsSubgroup_iff] at ht ⊢
    intro x hx
    simp [tH, ht x hx]
  let _ := CommHopfAlgCat.quotientPointsSubgroup_normal H I hI (CommAlgCat.of k H)
  have hp : p ∈ CommHopfAlgCat.quotientPointsSubgroup H I (CommAlgCat.of k H) :=
    Subgroup.Normal.conj_mem (H :=
      CommHopfAlgCat.quotientPointsSubgroup H I (CommAlgCat.of k H)) tH htH generic
  let q := (CommHopfAlgCat.liftQuotientPoint H I (CommAlgCat.of k H) p
    ((CommHopfAlgCat.mem_quotientPointsSubgroup_iff H I (CommAlgCat.of k H) p).mp hp)).ofConv
  have hq (x : H) : q (Ideal.Quotient.mkₐ k I.toIdeal x) = p.ofConv x :=
    CommHopfAlgCat.liftQuotientPoint_mk H I (CommAlgCat.of k H) p _ x
  let Q := CommHopfAlgCat.quotient H I
  let _ : Algebra.Etale k Q :=
    algebraEtale_iff_finite_and_isReduced.mpr ⟨inferInstance, inferInstance⟩
  obtain ⟨n, ⟨e⟩⟩ := Algebra.IsFiniteSplit.nonempty_algEquiv_fun k Q
  let ε := Bialgebra.counitAlgHom k H
  have hconst (z : Q) : q z = algebraMap k H (ε (q z)) := by
    have h := AlgHom.congr_fun ((q.comp e.symm.toAlgHom).eq_algebraMap_comp_of_connected ε) (e z)
    simpa only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, e.symm_apply_apply,
      Algebra.ofId_apply] using h
  have hone : toConv (Bialgebra.counitAlgHom k H) = (1 : WithConv (H →ₐ[k] k)) := by
    apply WithConv.ofConv_injective
    ext x
    simp [AlgHom.convOne_apply]
  have hε : AlgHom.mapValue ε p = t := by
    dsimp only [p]
    rw [map_mul, map_mul, map_inv]
    simp [generic, tH, ε, AlgHom.mapValue_apply, ← AlgHom.comp_assoc, Algebra.comp_ofId, hone]
  change p = tH
  apply WithConv.ofConv_injective
  ext x
  simp only [tH, AlgHom.mapValue_apply, ofConv_toConv, AlgHom.comp_apply, Algebra.ofId_apply]
  have hc := hconst (Ideal.Quotient.mkₐ k I.toIdeal x)
  rw [hq] at hc
  apply hc.trans
  apply congrArg (algebraMap k H)
  simpa only [AlgHom.mapValue_apply, ofConv_toConv, AlgHom.comp_apply] using
    congrArg (fun z ↦ (WithConv.ofConv z) x) hε

/-- A finite reduced normal subgroup of a connected affine group over an algebraically closed
field is central as a subgroup scheme. -/
theorem IsNormal.isCentral_of_finite_of_isReduced (hI : I.IsNormal) : I.IsCentral := by
  rw [isCentral_iff_conjugation_sub_mem]
  intro x
  rw [← Ideal.ker_tensorProduct_map_quotient_id I.toIdeal, RingHom.mem_ker, map_sub, sub_eq_zero]
  apply tensor_eq_of_forall_map_algHom_eq (K := k)
  intro t
  apply (TensorProduct.lid k H).injective
  let s := CommHopfAlgCat.quotientPointsHom H I (CommAlgCat.of k k) (toConv t)
  let sH := AlgHom.mapValue (Algebra.ofId k H) s
  let g := toConv (AlgHom.id k H)
  have ht := CommHopfAlgCat.quotientPointsHom_mem_quotientPointsSubgroup H I
    (CommAlgCat.of k k) (toConv t)
  have hc : Commute sH g :=
    ((commute_iff_eq _ _).mpr (mul_inv_eq_iff_eq_mul.mp (conjugate_generic_eq hI s ht))).symm
  have h := AlgHom.congr_fun (HopfAlgebra.productMap_comp_conjugationAlgHom sH g) x
  rw [mul_inv_eq_iff_eq_mul.mpr hc.eq] at h
  have heval (z : H ⊗[k] H) :
      TensorProduct.lid k H
        (TensorProduct.map t.toLinearMap LinearMap.id
          (Algebra.TensorProduct.map (Ideal.Quotient.mkₐ k I.toIdeal) (AlgHom.id k H) z)) =
        Algebra.TensorProduct.productMap sH.ofConv g.ofConv z := by
    induction z using TensorProduct.inductionOn with
    | add a b ha hb => simp_all
    | tmul a b => simp [sH, s, g, CommHopfAlgCat.quotientPointsHom_apply, Algebra.smul_def]
  simpa only [heval, Algebra.TensorProduct.includeRight_apply,
    Algebra.TensorProduct.productMap_right_apply, AlgHom.comp_apply] using h

end AlgebraicallyClosed

section Field

variable {k : Type u} [Field k] {H : _root_.CommHopfAlgCat.{u} k} {I : HopfIdeal k H}

/-- A finite geometrically reduced normal subgroup of a geometrically connected affine group
is central over any field. -/
theorem IsNormal.isCentral_of_finite_of_isGeometricallyReduced (hI : I.IsNormal)
    (hH : geometricallyConnectedCommHopfAlgProperty k H)
    [Module.Finite k (CommHopfAlgCat.quotient H I)]
    [Algebra.IsGeometricallyReduced k (CommHopfAlgCat.quotient H I)] : I.IsCentral := by
  let K := AlgebraicClosure k
  let H' := CommHopfAlgCat.baseChange (K := K) H
  let I' := CommHopfAlgCat.baseChangeHopfIdeal (K := K) I
  let Q' := CommHopfAlgCat.quotient H' I'
  let e := CommHopfAlgCat.quotientBaseChangeIso (K := K) I
  let _ : ConnectedSpace (PrimeSpectrum H') := hH.connectedSpace_algebraicClosureBaseChange
  let _ : Module.Finite K Q' :=
    Module.Finite.equiv (_root_.CommHopfAlgCat.ofIso e).symm.toLinearEquiv
  let _ : IsReduced Q' := isReduced_of_injective e.hom.hom
    (ConcreteCategory.bijective_of_isIso e.hom).1
  have hcentral : I'.IsCentral :=
    (CommHopfAlgCat.isNormal_baseChangeHopfIdeal hI).isCentral_of_finite_of_isReduced
  exact (CommHopfAlgCat.isCentral_baseChangeHopfIdeal_iff (K := K) I).mp hcentral

end Field

end TauCeti.HopfIdeal
