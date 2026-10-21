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

## Main definitions

* `TauCeti.SpinPolarizationData.ofIsCompl`: the polarization data of a finite-dimensional
  nondegenerate quadratic space determined by two complementary isotropic subspaces.

## Main results

* `TauCeti.SpinPolarizationData.ofIsCompl_W`, `ofIsCompl_W'` and `ofIsCompl_line`: the summands
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

variable {K : Type u} [Field K] {V : Type v} [AddCommGroup V] [Module K V]
  {Q : QuadraticForm K V} {W W' : Submodule K V}

/-- In a nondegenerate quadratic space which is the direct sum of `W` and a totally isotropic
subspace `W'`, a vector of `W'` orthogonal to `W` vanishes. -/
private theorem eq_zero_of_polar_eq_zero (hQ : Q.Nondegenerate) (hWW' : IsCompl W W')
    (hW' : Q.IsTotallyIsotropic W') {y : V} (hy : y ∈ W') (hyW : ∀ x ∈ W, polar Q x y = 0) :
    y = 0 := by
  have hpolar (z : V) : polar Q y z = 0 := by
    obtain ⟨x, hx, z', hz', rfl⟩ := Submodule.mem_sup.mp (hWW'.codisjoint.eq_top ▸
      Submodule.mem_top : z ∈ W ⊔ W')
    rw [polar_add_right, hW'.polar_eq_zero hy hz', polar_comm, hyW x hx, add_zero]
  have hrad : y ∈ Q.radical := ⟨hW'.apply_eq_zero hy, LinearMap.ext hpolar⟩
  simpa [hQ.radical_eq_bot] using hrad

/-- The polar pairing of a subspace `W'` with a subspace `W`, viewed as a map from `W'` into the
dual of `W`. -/
private noncomputable def polarPairing (Q : QuadraticForm K V) (W W' : Submodule K V) :
    W' →ₗ[K] Dual K W :=
  ((polarBilin Q).compl₁₂ W.subtype W'.subtype).flip

private theorem polarPairing_apply (y : W') (x : W) :
    polarPairing Q W W' y x = polar Q x y := (rfl)

private theorem polarPairing_injective (hQ : Q.Nondegenerate) (hWW' : IsCompl W W')
    (hW' : Q.IsTotallyIsotropic W') : Function.Injective (polarPairing Q W W') := by
  refine (injective_iff_map_eq_zero _).mpr fun y hy => Subtype.ext ?_
  refine eq_zero_of_polar_eq_zero hQ hWW' hW' y.2 fun x hx => ?_
  simpa [polarPairing_apply] using LinearMap.congr_fun hy ⟨x, hx⟩

variable [FiniteDimensional K V]

/-- Two complementary totally isotropic subspaces of a nondegenerate finite-dimensional quadratic
space have the same dimension. Once `ofIsCompl` is built, this is also
`TauCeti.SpinPolarizationData.finrank_W'_eq_finrank_W` for the constructed data. -/
private theorem finrank_eq_of_isCompl (hQ : Q.Nondegenerate) (hWW' : IsCompl W W')
    (hW : Q.IsTotallyIsotropic W) (hW' : Q.IsTotallyIsotropic W') :
    finrank K W' = finrank K W := by
  apply le_antisymm
  · simpa [Subspace.dual_finrank_eq] using
      LinearMap.finrank_le_finrank_of_injective (polarPairing_injective hQ hWW' hW')
  · simpa [Subspace.dual_finrank_eq] using
      LinearMap.finrank_le_finrank_of_injective (polarPairing_injective hQ hWW'.symm hW)

/-- **The polarization of a quadratic space by two complementary isotropic subspaces.** If a
finite-dimensional quadratic space `(V, Q)` with nondegenerate `Q` is the direct sum of two
totally isotropic subspaces `W` and `W'`, then `W` and `W'` are the two isotropic summands of a
polarization of `Q` with no orthogonal remainder; the polar form identifies `W'` with the dual
of `W`. -/
noncomputable def ofIsCompl (hQ : Q.Nondegenerate) (hWW' : IsCompl W W')
    (hW : Q.IsTotallyIsotropic W) (hW' : Q.IsTotallyIsotropic W') : SpinPolarizationData Q where
  W := W
  W' := W'
  line := ⊥
  decompositionEquiv := LinearEquiv.prodUnique ≪≫ₗ Submodule.prodEquivOfIsCompl W W' hWW'
  decompositionEquiv_apply x := by
    rw [LinearEquiv.trans_apply, LinearEquiv.prodUnique_apply, Submodule.coe_prodEquivOfIsCompl',
      (Submodule.mem_bot K).mp x.2.2, add_zero]
  isotropic_W x := hW.apply_eq_zero x.2
  isotropic_W' y := hW'.apply_eq_zero y.2
  pairingEquiv := (polarPairing Q W W').linearEquivOfInjective
    (polarPairing_injective hQ hWW' hW')
    (by rw [Subspace.dual_finrank_eq, finrank_eq_of_isCompl hQ hWW' hW hW'])
  pairingEquiv_apply y x := by
    rw [LinearMap.linearEquivOfInjective_apply, polarPairing_apply]
  pairing_separatingLeft x hx := Subtype.ext <|
    eq_zero_of_polar_eq_zero hQ hWW'.symm hW x.2 fun y hy => by
      rw [polar_comm]
      exact hx ⟨y, hy⟩
  lineCoordinate := 0
  lineCoordinate_injective a b _ := Subsingleton.elim a b
  lineCoordinate_sq z := by
    rw [Subsingleton.elim z 0, map_zero, mul_zero, ZeroMemClass.coe_zero, map_zero]
  line_orthogonal_W z x := by
    rw [Subsingleton.elim z 0, ZeroMemClass.coe_zero, polar_zero_left]
  line_orthogonal_W' z y := by
    rw [Subsingleton.elim z 0, ZeroMemClass.coe_zero, polar_zero_left]

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

end SpinPolarizationData

end TauCeti
