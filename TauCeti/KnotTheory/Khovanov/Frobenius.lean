/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.RingTheory.Coalgebra.Equiv
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.Coalgebra.TensorProduct
public import TauCeti.Algebra.DualNumber.TensorProduct
public import TauCeti.Algebra.DualNumber.Trace

/-!
# The Khovanov Frobenius algebra

Ordinary Khovanov homology assigns to each resolved circle a copy of the rank-two Frobenius
algebra `R[X]/(X²)`. Here it is the dual numbers `R[ε]`, with `X = ε`, together with the
comultiplication and counit

```text
Δ 1 = 1 ⊗ ε + ε ⊗ 1,     Δ ε = ε ⊗ ε,
counit 1 = 0,            counit ε = 1.
```

Merging two circles acts by multiplication and splitting one circle acts by `Δ`.

This coalgebra structure is a choice, not a canonical structure on every algebra of dual
numbers, so it is installed only as scoped instances in `TauCeti.Khovanov`; `open TauCeti.Khovanov`
(or `open scoped TauCeti.Khovanov`) to use it.

## Main definitions and results

* `TauCeti.Khovanov.coalgebra`: the Khovanov coalgebra structure on `R[ε]`.
* `TauCeti.Khovanov.comul_one`, `TauCeti.Khovanov.comul_eps`, `DualNumber.khovanov_counit_apply`:
  the values of the comultiplication and counit.
* `TauCeti.Khovanov.isCocomm`: the comultiplication is cocommutative.
* `TauCeti.Khovanov.isFrobenius`: `R[ε]` satisfies the Frobenius equation. Through Mathlib's
  `Coalgebra.IsFrobenius.left_eq_comul_comp_mul'` and
  `Coalgebra.IsFrobenius.right_eq_comul_comp_mul'` this identifies `Δ ∘ m` with both mixed
  composites `(m ⊗ id) ∘ (id ⊗ Δ)` and `(id ⊗ m) ∘ (Δ ⊗ id)`.
* `TauCeti.Khovanov.mul_compr₂_counit`: the Frobenius form `(a, b) ↦ counit (a * b)` is the
  perfect pairing `TauCeti.dualNumberTracePairing`.
* `TauCeti.Khovanov.counit_basis_mul_basis_rev`: the basis `ε, 1` is dual to the basis `1, ε`
  for that pairing; `DualNumber.khovanov_counit_eps_mul_smul_one_add_counit_smul_eps` is the
  resulting expansion `a = counit (ε * a) • 1 + counit a • ε`.
* `TauCeti.Khovanov.baseChangeCoalgEquiv`: for a commutative `R`-algebra `S`, the algebra
  isomorphism `S ⊗[R] R[ε] ≃ S[ε]` is an isomorphism of `S`-coalgebras, so the Khovanov
  Frobenius algebra over `S` is the base change of the one over `R`.

## References

* M. Khovanov, *A categorification of the Jones polynomial*, Duke Math. J. 101 (2000).
* D. Bar-Natan, *On Khovanov's categorification of the Jones polynomial*,
  Algebr. Geom. Topol. 2 (2002).
-/

public section

open TensorProduct DualNumber TrivSqZeroExt

namespace TauCeti.Khovanov

variable (R : Type*) [CommSemiring R]

/-- The Khovanov coalgebra structure on the dual numbers `R[ε]`: the comultiplication is
`Δ (a + b ε) = a • (1 ⊗ ε + ε ⊗ 1) + b • (ε ⊗ ε)` and the counit is `a + b ε ↦ b`. -/
noncomputable scoped instance coalgebra : Coalgebra R R[ε] where
  comul := (fstHom R R R).toLinearMap.smulRight (1 ⊗ₜ ε + ε ⊗ₜ 1) +
    (sndHom R R).smulRight (ε ⊗ₜ ε)
  counit := sndHom R R
  coassoc := by
    refine dualNumber_linearMap_ext ?_ ?_ <;> simp [tmul_add, add_tmul]
    abel
  rTensor_counit_comp_comul := by
    refine dualNumber_linearMap_ext ?_ ?_ <;> simp
  lTensor_counit_comp_comul := by
    refine dualNumber_linearMap_ext ?_ ?_ <;> simp

variable {R}

/-- The Khovanov comultiplication of a general dual number. -/
theorem _root_.DualNumber.khovanov_comul_apply (x : R[ε]) :
    Coalgebra.comul (R := R) x = x.fst • (1 ⊗ₜ ε + ε ⊗ₜ 1) + x.snd • (ε ⊗ₜ[R] ε) := by
  simp [Coalgebra.comul]

/-- The Khovanov counit reads off the coefficient of `ε`. -/
@[simp]
theorem _root_.DualNumber.khovanov_counit_apply (x : R[ε]) :
    Coalgebra.counit (R := R) x = x.snd := by
  simp [Coalgebra.counit]

variable (R)

/-- Splitting a circle labelled `1` gives `1 ⊗ ε + ε ⊗ 1`. -/
@[simp]
theorem comul_one : Coalgebra.comul (R := R) (1 : R[ε]) = 1 ⊗ₜ ε + ε ⊗ₜ 1 := by
  simp [DualNumber.khovanov_comul_apply]

/-- Splitting a circle labelled `ε` gives `ε ⊗ ε`. -/
@[simp]
theorem comul_eps : Coalgebra.comul (R := R) (ε : R[ε]) = ε ⊗ₜ ε := by
  simp [DualNumber.khovanov_comul_apply]

/-- The Khovanov comultiplication is cocommutative. -/
scoped instance isCocomm : Coalgebra.IsCocomm R R[ε] where
  comm_comp_comul := by
    refine dualNumber_linearMap_ext ?_ ?_ <;> simp [add_comm]

/-- The dual numbers with the Khovanov comultiplication satisfy the Frobenius equation. -/
scoped instance isFrobenius : Coalgebra.IsFrobenius R R[ε] where
  left_eq_right := by
    refine TensorProduct.ext (dualNumber_linearMap_ext ?_ ?_) <;>
      refine dualNumber_linearMap_ext ?_ ?_ <;>
      simp [Coalgebra.IsFrobenius.left_def, Coalgebra.IsFrobenius.right_def, tmul_add, add_tmul]

/-- The Frobenius form `(a, b) ↦ counit (a * b)` of the Khovanov coalgebra is the perfect trace
pairing of the dual numbers. -/
theorem mul_compr₂_counit :
    (LinearMap.mul R R[ε]).compr₂ Coalgebra.counit = dualNumberTracePairing R := by
  ext x y
  simp

/-- The basis `ε, 1` is dual to the basis `1, ε` of `R[ε]` for the Frobenius form. -/
theorem counit_basis_mul_basis_rev (i j : Fin 2) :
    Coalgebra.counit (R := R) (dualNumberBasis R i * dualNumberBasis R j.rev) =
      if i = j then 1 else 0 := by
  fin_cases i <;> fin_cases j <;> simp

variable {R}

/-- Expansion of a dual number in the basis `1, ε` with coefficients computed by the Frobenius
form against the dual basis `ε, 1`. -/
theorem _root_.DualNumber.khovanov_counit_eps_mul_smul_one_add_counit_smul_eps (a : R[ε]) :
    Coalgebra.counit (R := R) (ε * a) • (1 : R[ε]) + Coalgebra.counit (R := R) a • ε = a := by
  ext <;> simp

section BaseChange

variable (R) (S : Type*) [CommSemiring S] [Algebra R S]

/-- Base change of the Khovanov coalgebra: `S ⊗[R] R[ε] ≃ S[ε]` as `S`-coalgebras, where
`S ⊗[R] R[ε]` carries the base change of the Khovanov coalgebra over `R`. Its underlying map is
the algebra isomorphism `TauCeti.dualNumberAlgebraTensorAlgEquiv`. -/
noncomputable def baseChangeCoalgEquiv : S ⊗[R] R[ε] ≃ₗc[S] S[ε] :=
  { (dualNumberAlgebraTensorAlgEquiv R S).toLinearEquiv with
    counit_comp := by
      refine ((dualNumberBasis R).baseChange S).ext fun i => ?_
      fin_cases i <;> simp
    map_comp_comul := by
      refine ((dualNumberBasis R).baseChange S).ext fun i => ?_
      fin_cases i <;> simp [tmul_add] }

/-- The underlying map of `baseChangeCoalgEquiv` is the algebra isomorphism
`TauCeti.dualNumberAlgebraTensorAlgEquiv`. -/
@[simp]
theorem coe_baseChangeCoalgEquiv :
    ⇑(baseChangeCoalgEquiv R S) = dualNumberAlgebraTensorAlgEquiv R S := (rfl)

end BaseChange

end TauCeti.Khovanov
