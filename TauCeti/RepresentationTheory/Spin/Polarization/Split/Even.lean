/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Spin.Polarization.Hyperbolic
public import Mathlib.LinearAlgebra.StdBasis

/-!
# The standard split even-dimensional polarization

For a commutative ring `K`, the hyperbolic quadratic space on a finite free module `M` is
`M* × M` with quadratic form `(f, x) ↦ f x`. This file gives the coordinate instance
`M = Fin n → K` its canonical polarization: the two coordinate axes are the isotropic summands,
their polar pairing is evaluation, and the orthogonal remainder is zero. It is the instance
`M = Fin n → K` of `TauCeti.SpinPolarizationData.hyperbolic`.

Unlike the existence construction for a nondegenerate quadratic form over a separably closed
field, this polarization uses the fixed coordinate summands. Its named coordinate basis can be fed
directly into the spin representation and Kostant-lattice constructions.

## Main declarations

* `TauCeti.SplitEvenSpace`: the standard hyperbolic quadratic space `M* × M`.
* `TauCeti.splitEvenForm`: its quadratic form `(f, x) ↦ f x`.
* `TauCeti.splitEvenPolarization`: the canonical polarization by the two coordinate axes.
* `TauCeti.splitEvenBasis`: the coordinate basis of the first isotropic summand.

## References

* C. Chevalley, *The Algebraic Theory of Spinors*, Chapter II.
* N. Bourbaki, *Groupes et algèbres de Lie*, Chapters 4--6, Plate IV.
-/

public section

namespace TauCeti

universe u

/-- The standard split even-dimensional quadratic space on `Fin n → K`: the product of its
dual coordinate module and coordinate module. -/
abbrev SplitEvenSpace (K : Type u) [CommRing K] (n : ℕ) :=
  Module.Dual K (Fin n → K) × (Fin n → K)

/-- The standard split quadratic form on `M* × M`, given by `(f, x) ↦ f x`. -/
def splitEvenForm (K : Type u) [CommRing K] (n : ℕ) :
    QuadraticForm K (SplitEvenSpace K n) :=
  QuadraticForm.dualProd K (Fin n → K)

/-- Evaluation formula for the standard split quadratic form. -/
@[simp]
theorem splitEvenForm_apply (K : Type u) [CommRing K] (n : ℕ)
    (x : SplitEvenSpace K n) : splitEvenForm K n x = x.1 x.2 := by
  simp [splitEvenForm]

/-- Polarization formula for the standard split quadratic form. -/
@[simp]
theorem polar_splitEvenForm (K : Type u) [CommRing K] (n : ℕ)
    (x y : SplitEvenSpace K n) :
    QuadraticMap.polar (splitEvenForm K n) x y = x.1 y.2 + y.1 x.2 := by
  rw [splitEvenForm, polar_dualProd]

/-- The canonical polarization of the standard split quadratic space.

The coordinate axis is the first isotropic summand, the dual-coordinate axis is the second,
and the orthogonal remainder is zero. -/
noncomputable def splitEvenPolarization (K : Type u) [CommRing K] (n : ℕ) :
    SpinPolarizationData (splitEvenForm K n) :=
  SpinPolarizationData.hyperbolic (Module.eval_apply_injective K)

/-- The first isotropic summand of the standard split polarization is `Submodule.snd`. -/
private theorem splitEvenPolarization_W_eq_snd (K : Type u) [CommRing K] (n : ℕ) :
    (splitEvenPolarization K n).W = Submodule.snd K (Module.Dual K (Fin n → K)) (Fin n → K) := by
  rw [splitEvenPolarization, SpinPolarizationData.hyperbolic_W]

/-- The first isotropic summand of the standard split polarization is the coordinate axis. -/
@[simp]
theorem splitEvenPolarization_W (K : Type u) [CommRing K] (n : ℕ) :
    (splitEvenPolarization K n).W =
      (⊥ : Submodule K (Module.Dual K (Fin n → K))).prod ⊤ := by
  rw [splitEvenPolarization_W_eq_snd]
  ext
  simp

/-- The second isotropic summand of the standard split polarization is the dual-coordinate
axis. -/
@[simp]
theorem splitEvenPolarization_W' (K : Type u) [CommRing K] (n : ℕ) :
    (splitEvenPolarization K n).W' =
      (⊤ : Submodule K (Module.Dual K (Fin n → K))).prod ⊥ := by
  rw [splitEvenPolarization, SpinPolarizationData.hyperbolic_W']
  ext
  simp

/-- The standard split even-dimensional polarization has no orthogonal remainder. -/
@[simp]
theorem splitEvenPolarization_line (K : Type u) [CommRing K] (n : ℕ) :
    (splitEvenPolarization K n).line = ⊥ :=
  SpinPolarizationData.hyperbolic_line _

/-- The coordinate basis of the first isotropic summand in the standard split polarization. -/
noncomputable def splitEvenBasis (K : Type u) [CommRing K] (n : ℕ) :
    Module.Basis (Fin n) K (splitEvenPolarization K n).W :=
  (SpinPolarizationData.hyperbolicBasis (Pi.basisFun K (Fin n))).map
    (LinearEquiv.ofEq _ _ (splitEvenPolarization_W_eq_snd K n).symm)

/-- A coordinate-basis vector of the first isotropic summand is the corresponding standard
coordinate vector on the second axis of the split space. -/
@[simp]
theorem coe_splitEvenBasis (K : Type u) [CommRing K] (n : ℕ) (i : Fin n) :
    ((splitEvenBasis K n i : (splitEvenPolarization K n).W) : SplitEvenSpace K n) =
      (0, Pi.single i 1) := by
  rw [splitEvenBasis, Module.Basis.map_apply, LinearEquiv.coe_ofEq_apply,
    SpinPolarizationData.coe_hyperbolicBasis_apply, Pi.basisFun_apply]

end TauCeti
