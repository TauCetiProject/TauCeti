/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Dual.WeilPairing
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Hom.Torsion
public import TauCeti.RingTheory.RootsOfUnity.ZMod
import TauCeti.LinearAlgebra.Determinant

/-!
# The determinant of an endomorphism on torsion

Let `W` be an elliptic curve over a separably closed field `F` and `N` a positive integer
invertible in `F`. Then `E[N]` is free of rank two over `ZMod N`, and the Weil pairing is an
alternating, nondegenerate pairing on it. An endomorphism of `E[N]` scaling the Weil pairing by
`d` therefore has determinant `d`. A separable isogeny `φ : W → W` scales the Weil pairing by its
degree, so the determinant of its action on `E[N]` is `deg φ` modulo `N`: the finite-level form of
Silverman III.8.6, for separable `φ`.

This is how degrees become determinants of matrices over `ZMod N` in the Weil-pairing proof of the
Hasse bound: once a basis of `E[ℓ]` is chosen, `LinearMap.toMatrix` turns the action of the
pencil `r π - s` of the Frobenius `π`, for `s` not divisible by the characteristic (so that
`r π - s` is separable), into a `2 × 2` matrix whose determinant is the degree of `r π - s`, as
`TauCeti.Matrix.eq_quadratic_form_of_det_det_one_sub` requires.

## Main results

* `TauCeti.Isogeny.det_eq_of_weilPairing_eq_smul`: an endomorphism of `E[N]` scaling the Weil
  pairing by `d` has determinant `d`.
* `TauCeti.Isogeny.Hom.det_torsionLinearMap_ofIsogeny`: the determinant of the action of a
  separable isogeny on `E[N]` is its degree.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.8.6.
-/

public section

namespace TauCeti.Isogeny

open WeierstrassCurve.Affine

variable {F : Type*} [Field F] [DecidableEq F] [IsSepClosed F]
  {W : WeierstrassCurve.Affine F} [W.IsElliptic] {N : ℕ} [NeZero N] (hN : (N : F) ≠ 0)

include hN in
/-- **An endomorphism of `E[N]` scaling the Weil pairing by `d` has determinant `d`**, over a
separably closed field in which `N` is invertible. -/
theorem det_eq_of_weilPairing_eq_smul
    {f : Module.End (ZMod N) (AddSubgroup.torsionBy W.Point (N : ℤ))} {d : ZMod N}
    (hf : ∀ S T, weilPairing W N hN (f S) (f T) = d • weilPairing W N hN S T) :
    LinearMap.det f = d := by
  -- the Weil pairing, read as a `ZMod N`-bilinear form
  let ω := LinearMap.mk₂ (ZMod N)
    (fun S T : AddSubgroup.torsionBy W.Point (N : ℤ) ↦ weilPairing W N hN S T) (fun _ _ _ ↦ by simp)
      -- `ZMod N`-linearity in `S` is that of the additive map `e(·, T)`
      (fun c S T ↦ (AddMonoidHom.flip_apply _ _ _).symm.trans <|
        (ZMod.map_smul _ c S).trans (congrArg _ (AddMonoidHom.flip_apply _ _ _)))
      (fun _ _ _ ↦ map_add _ _ _) (fun c S T ↦ ZMod.map_smul (weilPairing W N hN S) c T)
  obtain ⟨b⟩ := WeierstrassCurve.nonempty_basis_torsionBy W N hN
  refine LinearMap.det_eq_of_compl₁₂_self_eq_smul_of_separatingLeft b
    (ω := ω) (fun S ↦ weilPairing_self W N hN S) (fun S hS ↦ weilPairing_nondegenerate W N hN hS)
    (LinearMap.ext₂ fun S T ↦ ?_)
  simp [ω, hf]

namespace Hom

include hN in
/-- **The determinant of the action of a separable isogeny on `E[N]` is its degree** modulo `N`,
over a separably closed field in which `N` is invertible (Silverman III.8.6). -/
theorem det_torsionLinearMap_ofIsogeny (φ : Isogeny W W)
    [Algebra.IsSeparable φ.fieldPullback.fieldRange W.FunctionField] :
    LinearMap.det ((ofIsogeny φ).torsionLinearMap N) = φ.degree :=
  det_eq_of_weilPairing_eq_smul hN fun _ _ ↦ (φ.weilPairing_eq_degree_nsmul_weilPairing N hN
    (torsionLinearMap_apply _ N _).symm (torsionLinearMap_apply _ N _).symm).trans
      (Nat.cast_smul_eq_nsmul _ _ _).symm

end Hom

end TauCeti.Isogeny

end
