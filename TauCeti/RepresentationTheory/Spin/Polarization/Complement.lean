/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.QuadraticForm.TotallyIsotropic
public import TauCeti.RepresentationTheory.Spin.Polarization.Basic

/-!
# Polarizations from complementary isotropic subspaces

A finite-dimensional nondegenerate quadratic space which is the direct sum of two totally isotropic
subspaces `W` and `W'` is polarized by them, with no orthogonal remainder: the polar form pairs
`W'` perfectly with `W`. This file packages that observation as a constructor of
`TauCeti.SpinPolarizationData`, so that a polarization whose two summands are given by a formula
(for instance the two eigenspaces of a complexified orthogonal complex structure) can be produced
from the isotropy and the complementarity of the summands alone.

The perfect pairing is the only nonformal field. A vector of `W'` pairing to zero with `W` also
pairs to zero with the isotropic `W'`, hence with all of `V = W ⊕ W'`; being isotropic, it lies in
the radical, which vanishes. So the polar pairing is injective in each variable, the two summands
have the same dimension, and the injective map from `W'` to the dual of `W` is an isomorphism.
No assumption on the characteristic is needed.

Over a general commutative ring the perfect pairing has to be supplied:
`TauCeti.SpinPolarizationData.ofIsComplOfPairing` builds the polarization from two complementary
totally isotropic submodules together with a polar identification of `W'` with the dual of `W`
whose left radical is trivial. Both `ofIsCompl` and the hyperbolic polarization
`TauCeti.SpinPolarizationData.hyperbolic` are instances of it.

## Main definitions

* `TauCeti.SpinPolarizationData.ofIsComplOfPairing`: the polarization data with no orthogonal
  remainder determined by two complementary isotropic submodules and a polar pairing of them.
* `TauCeti.SpinPolarizationData.ofIsCompl`: the polarization data of a finite-dimensional
  nondegenerate quadratic space determined by two complementary isotropic subspaces.

## Main results

* `TauCeti.SpinPolarizationData.ofIsComplOfPairing_W`, `ofIsComplOfPairing_W'` and
  `ofIsComplOfPairing_line`, and `ofIsCompl_W`, `ofIsCompl_W'` and `ofIsCompl_line`: the summands
  of the constructed data.

## References

* C. Chevalley, *The Algebraic Theory of Spinors*, Chapter I, for the duality between complementary
  totally isotropic subspaces.
-/

public section

open Module QuadraticMap

namespace TauCeti

universe u v

namespace SpinPolarizationData

section CommRing

variable {K : Type u} [CommRing K] {V : Type v} [AddCommGroup V] [Module K V]
  {Q : QuadraticForm K V} {W W' : Submodule K V}

/-- **The polarization by two complementary isotropic submodules with a given pairing.** Over a
commutative ring, two complementary totally isotropic submodules `W` and `W'` of a quadratic space
are the two summands of a polarization with no orthogonal remainder, once an identification of
`W'` with the dual of `W` given by the polar form is supplied, and the polar pairing has trivial
left radical. -/
noncomputable def ofIsComplOfPairing (hWW' : IsCompl W W') (hW : Q.IsTotallyIsotropic W)
    (hW' : Q.IsTotallyIsotropic W') (e : W' ≃ₗ[K] Dual K W)
    (he : ∀ (y : W') (x : W), e y x = polar Q x y)
    (hsep : ∀ x : W, (∀ y : W', polar Q x y = 0) → x = 0) : SpinPolarizationData Q where
  W := W
  W' := W'
  line := ⊥
  decompositionEquiv := LinearEquiv.prodUnique ≪≫ₗ Submodule.prodEquivOfIsCompl W W' hWW'
  decompositionEquiv_apply x := by
    rw [LinearEquiv.trans_apply, LinearEquiv.prodUnique_apply, Submodule.coe_prodEquivOfIsCompl',
      (Submodule.mem_bot K).mp x.2.2, add_zero]
  isotropic_W x := hW.apply_eq_zero x.2
  isotropic_W' y := hW'.apply_eq_zero y.2
  pairingEquiv := e
  pairingEquiv_apply := he
  pairing_separatingLeft := hsep
  lineCoordinate := 0
  lineCoordinate_injective a b _ := Subsingleton.elim a b
  lineCoordinate_sq z := by
    rw [Subsingleton.elim z 0, map_zero, mul_zero, ZeroMemClass.coe_zero, map_zero]
  line_orthogonal_W z x := by
    rw [Subsingleton.elim z 0, ZeroMemClass.coe_zero, polar_zero_left]
  line_orthogonal_W' z y := by
    rw [Subsingleton.elim z 0, ZeroMemClass.coe_zero, polar_zero_left]

variable (hWW' : IsCompl W W') (hW : Q.IsTotallyIsotropic W) (hW' : Q.IsTotallyIsotropic W')
  (e : W' ≃ₗ[K] Dual K W) (he : ∀ (y : W') (x : W), e y x = polar Q x y)
  (hsep : ∀ x : W, (∀ y : W', polar Q x y = 0) → x = 0)

@[simp]
theorem ofIsComplOfPairing_W : (ofIsComplOfPairing hWW' hW hW' e he hsep).W = W :=
  -- `(rfl)`, not `rfl`: the body of `ofIsComplOfPairing` is not `@[expose]`d.
  (rfl)

@[simp]
theorem ofIsComplOfPairing_W' : (ofIsComplOfPairing hWW' hW hW' e he hsep).W' = W' := (rfl)

@[simp]
theorem ofIsComplOfPairing_line : (ofIsComplOfPairing hWW' hW hW' e he hsep).line = ⊥ := (rfl)

end CommRing

section Field

variable {K : Type u} [Field K] {V : Type v} [AddCommGroup V] [Module K V]
  {Q : QuadraticForm K V} {W W' : Submodule K V} [FiniteDimensional K V]

/-- **The polarization of a quadratic space by two complementary isotropic subspaces.** If a
finite-dimensional quadratic space `(V, Q)` with nondegenerate `Q` is the direct sum of two
totally isotropic subspaces `W` and `W'`, then `W` and `W'` are the two isotropic summands of a
polarization of `Q` with no orthogonal remainder; the polar form identifies `W'` with the dual
of `W`. -/
noncomputable def ofIsCompl (hQ : Q.Nondegenerate) (hWW' : IsCompl W W')
    (hW : Q.IsTotallyIsotropic W) (hW' : Q.IsTotallyIsotropic W') : SpinPolarizationData Q :=
  ofIsComplOfPairing hWW' hW hW'
    (((polarBilin Q).compl₁₂ W.subtype W'.subtype).flip.linearEquivOfInjective
      (hW'.polarBilin_compl₁₂_flip_injective hQ hWW'.codisjoint)
      (by rw [Subspace.dual_finrank_eq, hW.finrank_eq_of_codisjoint hW' hQ hWW'.codisjoint]))
    (fun y x => by
      rw [LinearMap.linearEquivOfInjective_apply, LinearMap.flip_apply, LinearMap.compl₁₂_apply,
        polarBilin_apply_apply, Submodule.subtype_apply, Submodule.subtype_apply])
    (fun x hx => Subtype.ext <|
      hW.eq_zero_of_polar_eq_zero hQ hWW'.symm.codisjoint x.2 fun y hy => by
        rw [polar_comm]
        exact hx ⟨y, hy⟩)

variable (hQ : Q.Nondegenerate) (hWW' : IsCompl W W') (hW : Q.IsTotallyIsotropic W)
  (hW' : Q.IsTotallyIsotropic W')

@[simp]
theorem ofIsCompl_W : (ofIsCompl hQ hWW' hW hW').W = W :=
  -- `(rfl)`, not `rfl`: the body of `ofIsCompl` is not `@[expose]`d.
  (rfl)

@[simp]
theorem ofIsCompl_W' : (ofIsCompl hQ hWW' hW hW').W' = W' := (rfl)

@[simp]
theorem ofIsCompl_line : (ofIsCompl hQ hWW' hW hW').line = ⊥ := (rfl)

end Field

end SpinPolarizationData

end TauCeti
