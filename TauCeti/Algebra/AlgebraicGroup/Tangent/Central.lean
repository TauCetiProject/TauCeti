/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Tangent.Naturality

/-!
# Universally invariant tangent vectors

A tangent vector fixed under every adjoint action, after every change of coefficients,
defines a universally central dual-number point. We also characterize invariance under
a given point by commutation of the corresponding dual-number points. These criteria use
arbitrary value algebras, including nonreduced ones, and need neither smoothness nor
finite type.

The dual-number dictionary and adjoint calculation are those of
`TauCeti.derivationMulEquivTangentKer` and `Derivation.snd_conjugate_tangentPoint`.
The universal property `DualNumber.lift` allows specialization of the infinitesimal parameter
to any square-zero element, rather than testing centrality only against constant points.

## References

* J. S. Milne, *Algebraic Groups* (2017), §10, tangent spaces and the adjoint action.
* J. C. Jantzen, *Representations of Algebraic Groups*, I.7.
-/

public section

open TauCeti WithConv TrivSqZeroExt

namespace Derivation

universe u v w

section Fixed

variable {R : Type u} {H : Type v} {B : Type w}
  [CommSemiring R] [CommSemiring H] [HopfAlgebra R H] [CommSemiring B] [Algebra R B]

/-- A point fixes a tangent vector under the adjoint action exactly when its constant
dual-number lift commutes with the vector's tangent point. -/
theorem adDerivation_eq_self_iff_commute_tangentPoint
    (d : Derivation R H (Bialgebra.CounitAlgebra R H B))
    (g : WithConv (H →ₐ[R] Bialgebra.CounitAlgebra R H B)) :
    adDerivation B g d = d ↔
      Commute (AlgHom.mapValue
        (inlAlgHom R (Bialgebra.CounitAlgebra R H B) (Bialgebra.CounitAlgebra R H B)) g)
        (derivationMulEquivTangentKer R H B (Multiplicative.ofAdd d)).val := by
  let p := derivationMulEquivTangentKer R H B (Multiplicative.ofAdd d)
  let q := AlgHom.mapValue
    (inlAlgHom R (Bialgebra.CounitAlgebra R H B) (Bialgebra.CounitAlgebra R H B)) g
  let _ : (tangentKer R H B).Normal := by
    rw [tangentKer_def]
    infer_instance
  have hmem : q * p.val * q⁻¹ ∈ tangentKer R H B :=
    Subgroup.Normal.conj_mem (inferInstance : (tangentKer R H B).Normal) p.val p.property q
  constructor
  · intro h
    have he : q * p.val * q⁻¹ = p.val := by
      apply ofConv_injective
      apply AlgHom.ext
      intro a
      apply TrivSqZeroExt.ext
      · exact (fst_apply_of_mem_tangentKer hmem a).trans
          (fst_apply_of_mem_tangentKer p.property a).symm
      · exact (snd_conjugate_tangentPoint d g a).trans
          ((DFunLike.congr_fun h a).trans
            (derivationMulEquivTangentKer_apply_snd (Multiplicative.ofAdd d) a).symm)
    exact (mul_inv_eq_iff_eq_mul (G := WithConv (H →ₐ[R] DualNumber
      (Bialgebra.CounitAlgebra R H B)))).mp he
  · intro h
    ext a
    have he := congrArg (fun z ↦ snd (z.ofConv a))
      (Commute.mul_inv_cancel (G := WithConv (H →ₐ[R] DualNumber
      (Bialgebra.CounitAlgebra R H B))) h)
    exact (snd_conjugate_tangentPoint d g a).symm.trans
      (he.trans (derivationMulEquivTangentKer_apply_snd (Multiplicative.ofAdd d) a))

end Fixed

variable {R : Type u} {H : Type v} {B : Type w}
  [CommRing R] [CommRing H] [HopfAlgebra R H] [CommRing B] [Algebra R B]

/-- A tangent vector fixed by every adjoint action after every change of coefficients
defines a universally central dual-number point. The coefficient tests include nonreduced
algebras and arbitrary specializations of the dual-number parameter. -/
theorem isCentralPoint_tangentPoint_of_forall_adDerivation_eq_self
    (d : Derivation R H (Bialgebra.CounitAlgebra R H B))
    (hd : ∀ (A : Type (max v w)) [CommRing A] [Algebra R A] (φ : B →ₐ[R] A)
      (g : WithConv (H →ₐ[R] Bialgebra.CounitAlgebra R H A)),
      adDerivation A g (mapValue φ d) = mapValue φ d) :
    HopfAlgebra.IsCentralPoint
      (derivationMulEquivTangentKer R H B (Multiplicative.ofAdd d)).val := by
  rw [HopfAlgebra.isCentralPoint_def]
  intro A _ _ χ h
  let C := Bialgebra.CounitAlgebra R H B
  let D := Bialgebra.CounitAlgebra R H A
  let φ : B →ₐ[R] A :=
    (χ.comp (inlAlgHom R C C)).comp (Bialgebra.CounitAlgebra.algEquivSelf R H B).symm.toAlgHom
  let g := AlgHom.mapValue (Bialgebra.CounitAlgebra.algEquivSelf R H A).symm.toAlgHom h
  -- Specialize the dual-number parameter to its image under χ. This factors every
  -- value map through a dual-number algebra over the final coefficient ring.
  let e : DualNumber D →ₐ[R] A := DualNumber.lift
    ⟨((Bialgebra.CounitAlgebra.algEquivSelf R H A).toAlgHom, χ DualNumber.eps),
      by rw [← map_mul, DualNumber.eps_mul_eps, map_zero], fun _ ↦ Commute.all _ _⟩
  have hc := ((adDerivation_eq_self_iff_commute_tangentPoint (mapValue φ d) g).mp
    (hd A φ g)).map (AlgHom.mapValue (H := H) e)
  have hg : AlgHom.mapValue (H := H) e
      (AlgHom.mapValue (inlAlgHom R D D) g) = h := by
    apply ofConv_injective
    apply AlgHom.ext
    intro x
    simp only [AlgHom.mapValue_apply, ofConv_toConv, AlgHom.comp_apply, e, g,
      inlAlgHom_apply, DualNumber.lift_apply_inl, AlgEquiv.coe_toAlgHom,
      AlgEquiv.apply_symm_apply]
  -- Under this specialization the constant point becomes h and the extended tangent
  -- point becomes the image of the original tangent point.
  have hp : AlgHom.mapValue (H := H) e
      (derivationMulEquivTangentKer R H A (Multiplicative.ofAdd (mapValue φ d))).val =
      AlgHom.mapValue χ
        (derivationMulEquivTangentKer R H B (Multiplicative.ofAdd d)).val := by
    apply ofConv_injective
    apply AlgHom.ext
    intro x
    have hχ (z : DualNumber C) :
        χ z = χ (inl z.fst) + χ (inl z.snd) * χ DualNumber.eps := by
      have hz := congrArg (fun f : DualNumber C →ₐ[R] A ↦ f z)
        (DualNumber.lift.apply_symm_apply χ)
      simpa only [DualNumber.lift_apply_apply, DualNumber.coe_lift_symm_apply,
        AlgHom.comp_apply, inlAlgHom_apply] using hz.symm
    simp only [AlgHom.mapValue_apply, ofConv_toConv, AlgHom.comp_apply]
    have hscalar (r : R) : χ (inl (algebraMap R C r)) = algebraMap R A r := by
      rw [← inlAlgHom_apply R C C, (inlAlgHom R C C).commutes, χ.commutes]
    have hdval : Bialgebra.CounitAlgebra.algEquivSelf R H A (mapValue φ d x) =
        χ (inl (d x)) := by
      -- Coefficient change passes through the counit-algebra synonym. Its pointwise
      -- equation uses the underlying coefficient ring, so rewriting needs `erw` here.
      erw [mapValue_apply, Bialgebra.CounitAlgebra.algEquivSelf_apply]
      dsimp only [φ]
      erw [AlgHom.comp_apply, AlgHom.comp_apply, inlAlgHom_apply,
        Bialgebra.CounitAlgebra.algEquivSelf_symm_apply]
    dsimp only [e]
    rw [DualNumber.lift_apply_apply,
      hχ ((derivationMulEquivTangentKer R H B (Multiplicative.ofAdd d)).val.ofConv x)]
    erw [fst_apply_of_mem_tangentKer (SetLike.coe_mem _),
      fst_apply_of_mem_tangentKer (SetLike.coe_mem _),
      derivationMulEquivTangentKer_apply_snd,
      derivationMulEquivTangentKer_apply_snd]
    dsimp only
    simp only [toAdd_ofAdd, AlgEquiv.coe_toAlgHom]
    rw [hdval, hscalar]
    congr 1
    exact (Bialgebra.CounitAlgebra.algEquivSelf R H A).commutes _
  rw [hg, hp] at hc
  exact hc.symm

end Derivation
