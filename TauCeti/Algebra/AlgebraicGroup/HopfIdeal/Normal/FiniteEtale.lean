/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Central
public import TauCeti.Algebra.AlgebraicGroup.Connected.CommHopfAlgCat
public import Mathlib.RingTheory.Nilpotent.GeometricallyReduced
import TauCeti.Algebra.AlgebraicGroup.Center.BaseChange
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Normal.BaseChange
import TauCeti.Algebra.AlgebraicGroup.FiniteType.BaseChange
import TauCeti.RingTheory.FiniteType.FiniteRange
import TauCeti.RingTheory.FiniteType.Tensor.PointSeparation
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix

/-!
# Finite étale normal subgroups are central

A finite reduced normal closed subgroup of a reduced connected affine group of finite type
over an algebraically closed field is central. Over an arbitrary field, the geometric version
says that a finite geometrically reduced normal subgroup of a geometrically reduced,
geometrically connected finite-type affine group is central. In particular this includes finite
étale subgroups.
Centrality concerns the whole subgroup scheme.

Conjugating a fixed rational subgroup point gives regular functions on the ambient group
with finite image. Connectedness makes these functions constant, and evaluation at the identity
determines their values. Point separation in both tensor factors upgrades this computation to
scheme-theoretic centrality. These results apply to separable isogeny kernels.

## References

* J. S. Milne, *Algebraic Groups* (2017), Remark 12.39(a).

The constancy argument uses `TauCeti.eq_algebraMap_of_finite_range_eval`, as in
`TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.Normal`.
-/

public section

open CategoryTheory WithConv
open scoped TensorProduct

namespace TauCeti.HopfIdeal

universe u


section AlgebraicallyClosed

variable {k : Type u} [Field k] [IsAlgClosed k]
  {H : _root_.CommHopfAlgCat.{u} k} [Algebra.FiniteType k H] [IsReduced H]
  [ConnectedSpace (PrimeSpectrum H)] {I : HopfIdeal k H}
  [Module.Finite k (CommHopfAlgCat.quotient H I)]

private theorem conjugate_basePoint_eq (hI : I.IsNormal)
    (t : WithConv (H →ₐ[k] k))
    (ht : t ∈ CommHopfAlgCat.quotientPointsSubgroup H I (CommAlgCat.of k k))
    (g : WithConv (H →ₐ[k] k)) : g * t * g⁻¹ = t := by
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
      CommHopfAlgCat.quotientPointsSubgroup H I (CommAlgCat.of k H)) inferInstance tH htH generic
  let q := (CommHopfAlgCat.liftQuotientPoint H I (CommAlgCat.of k H) p
    ((CommHopfAlgCat.mem_quotientPointsSubgroup_iff H I (CommAlgCat.of k H) p).mp hp)).ofConv
  have hq (x : H) : q (Ideal.Quotient.mkₐ k I.toIdeal x) = p.ofConv x := by
    exact CommHopfAlgCat.liftQuotientPoint_mk H I (CommAlgCat.of k H) p _ x
  have heval (f : H →ₐ[k] k) (x : H) :
      f (p.ofConv x) = (toConv f * t * (toConv f)⁻¹).ofConv x := by
    have h : AlgHom.mapValue f p = toConv f * t * (toConv f)⁻¹ := by
      dsimp only [p]
      rw [map_mul, map_mul, map_inv]
      simp [generic, tH, AlgHom.mapValue_apply, ← AlgHom.comp_assoc, Algebra.comp_ofId]
    simpa only [AlgHom.mapValue_apply, ofConv_toConv, AlgHom.comp_apply] using
      congrArg (fun z ↦ z.ofConv x) h
  apply WithConv.ofConv_injective
  ext x
  have hfinite : (Set.range fun f : H →ₐ[k] k ↦ f (p.ofConv x)).Finite := by
    apply (Set.finite_range (fun f : CommHopfAlgCat.quotient H I →ₐ[k] k ↦
      f (Ideal.Quotient.mkₐ k I.toIdeal x))).subset
    rintro _ ⟨f, rfl⟩
    exact ⟨f.comp q, congrArg f (hq x)⟩
  have hconstant := eq_algebraMap_of_finite_range_eval (p.ofConv x) hfinite
    (1 : WithConv (H →ₐ[k] k)).ofConv
  have hvalue : p.ofConv x = algebraMap k H (t.ofConv x) := by
    simpa only [heval, toConv_ofConv, one_mul, inv_one, mul_one] using hconstant
  rw [← heval, hvalue, AlgHom.commutes]
  simp

/-- A finite reduced normal closed subgroup of a reduced connected finite-type affine group
over an algebraically closed field is central as a subgroup scheme. -/
theorem IsNormal.isCentral_of_finite_of_isReduced [IsReduced (CommHopfAlgCat.quotient H I)]
    (hI : I.IsNormal) : I.IsCentral := by
  rw [isCentral_iff_conjugation_sub_mem]
  intro x
  rw [← ker_tensorProduct_map_quotient_id I.toIdeal, RingHom.mem_ker, map_sub, sub_eq_zero]
  apply tensor_eq_of_forall_map_algHom_eq (K := k)
  intro t
  apply (TensorProduct.lid k H).injective
  apply eq_of_forall_algHom_apply_eq (k := k) (K := k)
  intro g
  have ht := CommHopfAlgCat.quotientPointsHom_mem_quotientPointsSubgroup H I
    (CommAlgCat.of k k) (toConv t)
  let s := CommHopfAlgCat.quotientPointsHom H I (CommAlgCat.of k k) (toConv t)
  have hcomm : Commute s (toConv g) := by
    have h := conjugate_basePoint_eq hI s ht (toConv g)
    exact ((commute_iff_eq _ _).mpr (mul_inv_eq_iff_eq_mul.mp h)).symm
  have hconj : s * toConv g * s⁻¹ = toConv g :=
    mul_inv_eq_iff_eq_mul.mpr hcomm.eq
  have h := AlgHom.congr_fun (HopfAlgebra.productMap_comp_conjugationAlgHom s (toConv g)) x
  rw [hconj] at h
  have heval (z : H ⊗[k] H) :
      g (TensorProduct.lid k H
        (TensorProduct.map t.toLinearMap LinearMap.id
          (Algebra.TensorProduct.map (Ideal.Quotient.mkₐ k I.toIdeal) (AlgHom.id k H) z))) =
      Algebra.TensorProduct.productMap s.ofConv g z := by
    induction z using TensorProduct.inductionOn with
    | add a b ha hb => simp_all
    | tmul a b => simp [s, CommHopfAlgCat.quotientPointsHom_apply]
  simpa only [heval, Algebra.TensorProduct.includeRight_apply,
    Algebra.TensorProduct.productMap_right_apply, ofConv_toConv, AlgHom.comp_apply] using h

end AlgebraicallyClosed

section Field

variable {k : Type u} [Field k] {H : FiniteTypeCommHopfAlgCat.{u, u} k}
  [Algebra.IsGeometricallyReduced k H] {I : HopfIdeal k H}

/-- A finite geometrically reduced normal subgroup of a geometrically reduced,
geometrically connected finite-type affine group is central over any field. Neither perfectness of
the field nor
connectedness of the subgroup is required. -/
theorem IsNormal.isCentral_of_finite_of_isGeometricallyReduced (hI : I.IsNormal)
    (hH : geometricallyConnectedCommHopfAlgProperty k H.obj)
    [Module.Finite k (CommHopfAlgCat.quotient H.obj I)]
    [Algebra.IsGeometricallyReduced k (CommHopfAlgCat.quotient H.obj I)] : I.IsCentral := by
  let K := AlgebraicClosure k
  let H' := FiniteTypeCommHopfAlgCat.baseChange (K := K) H
  let I' := CommHopfAlgCat.baseChangeHopfIdeal (K := K) I
  let Q' := CommHopfAlgCat.quotient H'.obj I'
  let e := CommHopfAlgCat.quotientBaseChangeIso (K := K) I
  let _ : ConnectedSpace (PrimeSpectrum H') := hH.connectedSpace_algebraicClosureBaseChange
  -- The carrier of `FiniteTypeCommHopfAlgCat.baseChange` unfolds to `K ⊗[k] H`.
  let _ : IsReduced H' := inferInstanceAs (IsReduced (K ⊗[k] H))
  let _ : Module.Finite K Q' :=
    Module.Finite.equiv (_root_.CommHopfAlgCat.ofIso e).symm.toLinearEquiv
  let _ : IsReduced Q' := isReduced_of_injective e.hom.hom
    (ConcreteCategory.bijective_of_isIso e.hom).1
  have hcentral : I'.IsCentral :=
    (CommHopfAlgCat.isNormal_baseChangeHopfIdeal hI).isCentral_of_finite_of_isReduced
  exact (CommHopfAlgCat.isCentral_baseChangeHopfIdeal_iff (K := K) I).mp hcentral

end Field

end TauCeti.HopfIdeal
