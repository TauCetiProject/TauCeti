/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Dual.WeilPairing
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Hom.Torsion
public import TauCeti.RingTheory.RootsOfUnity.ZMod
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.WeilPairing.Bilinear
import TauCeti.LinearAlgebra.Determinant.Basic

/-!
# The determinant of an endomorphism on torsion

Let `W` be an elliptic curve over a separably closed field `F` and `N` a positive integer
invertible in `F`. Then `E[N]` is free of rank two over `ZMod N`, and the Weil pairing is an
alternating, nondegenerate pairing on it. An endomorphism of `E[N]` scaling the Weil pairing by
`d` therefore has determinant `d`. An isogeny `φ : W → W` scales the Weil pairing by its
degree, so the determinant of its action on `E[N]` is `deg φ` modulo `N`: the finite-level form of
Silverman III.8.6.

This is how degrees become determinants of matrices over `ZMod N` in the Weil-pairing proof of the
Hasse bound: once a basis of `E[ℓ]` is chosen, `LinearMap.toMatrix` turns the action of the
pencil `r π - s` of the Frobenius `π` into a `2 × 2` matrix whose determinant is the degree of
`r π - s`, as `TauCeti.Matrix.eq_quadratic_form_of_det_det_one_sub` requires.

## Main results

* `TauCeti.Isogeny.det_eq_of_weilPairing_eq_smul`: an endomorphism of `E[N]` scaling the Weil
  pairing by `d` has determinant `d`.
* `TauCeti.Isogeny.Hom.det_torsionLinearMap_ofIsogeny`: the determinant of the action of an
  isogeny on `E[N]` is its degree.
* `TauCeti.Isogeny.Hom.det_torsionLinearMap`: the same for a morphism, the zero morphism included.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.8.6.
-/

public section

namespace TauCeti.Isogeny

open WeierstrassCurve.Affine

variable {F : Type*} [Field F] [DecidableEq F] [IsSepClosed F]
  {W : WeierstrassCurve.Affine F} [W.IsElliptic] {N : ℕ} [NeZero N] (hN : (N : F) ≠ 0)

/-- **An endomorphism of `E[N]` scaling the Weil pairing by `d` has determinant `d`**, over a
separably closed field in which `N` is invertible. -/
theorem det_eq_of_weilPairing_eq_smul
    {f : Module.End (ZMod N) (AddSubgroup.torsionBy W.Point (N : ℤ))} {d : ZMod N}
    (hf : ∀ S T, weilPairing W N hN (f S) (f T) = d • weilPairing W N hN S T) :
    LinearMap.det f = d := by
  obtain ⟨b⟩ := WeierstrassCurve.nonempty_basis_torsionBy W N hN
  refine LinearMap.det_eq_of_compl₁₂_self_eq_smul_of_separatingLeft b
    (isAlt_weilPairingBilin W N hN) (separatingLeft_weilPairingBilin W N hN)
    (LinearMap.ext₂ fun S T ↦ ?_)
  simp [hf]

namespace Hom

include hN in
/-- **The determinant of the action of an isogeny on `E[N]` is its degree** modulo `N`,
over a separably closed field in which `N` is invertible (Silverman III.8.6). -/
theorem det_torsionLinearMap_ofIsogeny (φ : Isogeny W W) :
    LinearMap.det ((ofIsogeny φ).torsionLinearMap N) = φ.degree :=
  det_eq_of_weilPairing_eq_smul hN fun _ _ ↦ (φ.weilPairing_eq_degree_nsmul_weilPairing N hN
    (torsionLinearMap_apply _ N _).symm (torsionLinearMap_apply _ N _).symm).trans
      (Nat.cast_smul_eq_nsmul _ _ _).symm

include hN in
/-- The determinant of a morphism on `E[N]` is its degree modulo `N`, over a separably closed field
in which `N` is invertible. -/
theorem det_torsionLinearMap (f : Hom W W) :
    LinearMap.det (f.torsionLinearMap N) = f.degree := by
  rcases eq_or_ne f 0 with rfl | h
  · obtain ⟨b⟩ := WeierstrassCurve.nonempty_basis_torsionBy W N hN
    rw [torsionLinearMap_zero, LinearMap.det_zero' b, degree_zero, Nat.cast_zero]
  · simpa only [ofIsogeny_toIsogeny, ← degree_ofIsogeny] using
      det_torsionLinearMap_ofIsogeny hN (toIsogeny h)

end Hom

end TauCeti.Isogeny

end
