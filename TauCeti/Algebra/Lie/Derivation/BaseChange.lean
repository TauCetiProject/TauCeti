/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.AdjointAction.Derivation
public import Mathlib.Algebra.Lie.Derivation.BaseChange
public import TauCeti.LinearAlgebra.TensorProduct.BaseChange
public import TauCeti.LinearAlgebra.TensorProduct.Range

/-!
# Lie derivations after extension of scalars

Let `L` be a Lie algebra over a commutative ring `R` and let `A` be a commutative `R`-algebra.
Mathlib's `Lie.Derivation.ofLieDerivation` extends a derivation `D` of `L` to the base change
`A ⊗[R] L`, but records the result only as a derivation over `R`.  The extension is in fact
`A`-linear, because it is `LinearMap.baseChange`, and `A` is the ring the extended Lie algebra is
an algebra over; `LieDerivation.baseChange` is that sharper packaging.  Every statement below is
about the `A`-linear form, which is the one that can be compared with `LieSubmodule.baseChange`,
whose ideals are ideals over `A`.

The point of the construction is descent.  Over a faithfully flat coefficient algebra a containment
between the image of a Lie ideal under a derivation and another Lie ideal may be *checked after
extending scalars*:

```text
(∀ z ∈ I.baseChange A, D.baseChange A z ∈ J.baseChange A) ↔ ∀ x ∈ I, D x ∈ J
```

This is the derivation half of the base-change toolkit that lets a structural statement about a
Lie algebra over a field of characteristic zero be proved over an algebraic closure, where
Mathlib's Lie theorem applies, and then descended.

## Main definitions

* `LieDerivation.baseChange`: the `A`-linear extension of a Lie derivation to `A ⊗[R] L`.

## Main results

* `LieDerivation.baseChange_ad`: the extension of an inner derivation `ad x` is the inner
  derivation at `1 ⊗ₜ x`, so the construction is compatible with the adjoint action.
* `LieDerivation.baseChange_zero`, `LieDerivation.baseChange_add` and
  `LieDerivation.baseChange_lie`: extension of scalars respects the additive and the bracket
  structure of the derivations.
* `LieDerivation.baseChange_injective`: over a faithfully flat coefficient algebra, two derivations
  agreeing after extension of scalars are equal.
* `LieDerivation.mapsTo_baseChange_lieIdeal_iff`: **over a faithfully flat coefficient algebra, a
  derivation maps one Lie ideal into another exactly when the extended derivation maps the
  extension of the first into the extension of the second.**

## Implementation notes

`LieDerivation.baseChange` and Mathlib's `Lie.Derivation.ofLieDerivation` have the same underlying
function, recorded as `LieDerivation.coe_ofLieDerivation`; only the ring over which each is
registered as linear differs.

The descent is not specific to derivations, so it lives one level down:
`LinearMap.mapsTo_baseChange_iff` and `LinearMap.range_baseChange_le_baseChange_iff` in
`TauCeti/LinearAlgebra/TensorProduct/Range.lean`, `LinearMap.baseChange_injective` and
`LinearMap.isNilpotent_baseChange_iff` in
`TauCeti/LinearAlgebra/TensorProduct/BaseChange.lean`.  These are the statements for a bare linear
map, and reach a derivation through `LieDerivation.baseChange_toLinearMap`.

Mathlib provides the extension for a derivation of `L` into `L` and not for one into a general
Lie module `M`, so that is the generality available by reuse and the generality used here; it is
also the one the descent statement needs, since it compares the extended derivation with the
extensions of ideals of `L`.
-/

public section

open TensorProduct

namespace LieDerivation

universe u v w

variable {R : Type u} {A : Type v} {L : Type w}
variable [CommRing R] [CommRing A] [Algebra R A] [LieRing L] [LieAlgebra R L]

variable (A) in
/-- The extension of a Lie derivation `D` of `L` to the base change `A ⊗[R] L`, as a derivation
over `A`.  Its underlying map is `LinearMap.baseChange`, so it sends `a ⊗ₜ x` to `a ⊗ₜ D x`. -/
def baseChange (D : LieDerivation R L L) : LieDerivation A (A ⊗[R] L) (A ⊗[R] L) where
  toLinearMap := D.toLinearMap.baseChange A
  leibniz' x y := by
    simpa only [Lie.Derivation.ofLieDerivation_apply, LinearMap.baseChange_eq_ltensor] using
      (Lie.Derivation.ofLieDerivation A D).apply_lie_eq_sub x y

/-- The extended derivation differentiates the second factor of a pure tensor. -/
@[simp]
theorem baseChange_apply_tmul (D : LieDerivation R L L) (a : A) (x : L) :
    D.baseChange A (a ⊗ₜ[R] x) = a ⊗ₜ[R] D x :=
  (rfl)

/-- The linear map underlying the extension of `D` is the extension of the linear map underlying
`D`; this is what lets the linear-algebraic base-change API apply to it. -/
@[simp]
theorem baseChange_toLinearMap (D : LieDerivation R L L) :
    (D.baseChange A).toLinearMap = D.toLinearMap.baseChange A :=
  (rfl)

/-- The `R`-linear extension `Lie.Derivation.ofLieDerivation` supplied by Mathlib and the
`A`-linear extension `LieDerivation.baseChange` are the same function: only the ring over which
each is recorded as linear differs. -/
theorem coe_ofLieDerivation (D : LieDerivation R L L) :
    ⇑(Lie.Derivation.ofLieDerivation A D) = ⇑(D.baseChange A) :=
  (rfl)

/-- The zero derivation extends to the zero derivation. -/
@[simp]
theorem baseChange_zero : (0 : LieDerivation R L L).baseChange A = 0 :=
  LieDerivation.ext fun z => by
    have h := congrFun (coe_ofLieDerivation (A := A) (0 : LieDerivation R L L)) z
    rw [map_zero] at h
    simpa using h.symm

/-- Extension of scalars is additive in the derivation. -/
@[simp]
theorem baseChange_add (D E : LieDerivation R L L) :
    (D + E).baseChange A = D.baseChange A + E.baseChange A :=
  LieDerivation.ext fun z => by
    have h := congrFun (coe_ofLieDerivation (A := A) (D + E)) z
    rw [map_add] at h
    simp only [LieDerivation.add_apply, coe_ofLieDerivation] at h
    rw [LieDerivation.add_apply]
    exact h.symm

/-- Extension of scalars is compatible with the bracket of derivations. -/
@[simp]
theorem baseChange_lie (D E : LieDerivation R L L) :
    (⁅D, E⁆ : LieDerivation R L L).baseChange A = ⁅D.baseChange A, E.baseChange A⁆ :=
  LieDerivation.ext fun z => by
    have h := congrFun (coe_ofLieDerivation (A := A) ⁅D, E⁆) z
    rw [LieHom.map_lie] at h
    simp only [LieDerivation.lie_apply, coe_ofLieDerivation] at h
    rw [LieDerivation.lie_apply]
    exact h.symm

/-- The extension of the inner derivation at `x` is the inner derivation at `1 ⊗ₜ x`. -/
@[simp]
theorem baseChange_ad (x : L) :
    (ad R L x).baseChange A = ad A (A ⊗[R] L) ((1 : A) ⊗ₜ[R] x) := by
  ext z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a y => simp [LieAlgebra.ExtendScalars.bracket_tmul]
  | add y z hy hz => simp [map_add, hy, hz]

section FaithfullyFlat

variable [Module.FaithfullyFlat R A]

/-- Over a faithfully flat coefficient algebra no information is lost by extending a derivation:
two derivations agreeing after extension of scalars are equal. -/
theorem baseChange_injective :
    Function.Injective (baseChange A : LieDerivation R L L → LieDerivation A _ _) := by
  intro D E h
  have hL : D.toLinearMap = E.toLinearMap :=
    LinearMap.baseChange_injective (A := A) (by
      rw [← baseChange_toLinearMap, ← baseChange_toLinearMap, h])
  exact LieDerivation.ext fun x => DFunLike.congr_fun hL x

variable (D : LieDerivation R L L)

/-- **A containment of Lie ideals under a derivation may be checked after extending scalars.**
This is the form in which the descent is used: a structural statement proved over an algebraic
closure, where it is available, descends to the original coefficient field. -/
theorem mapsTo_baseChange_lieIdeal_iff (I J : LieIdeal R L) :
    (∀ z ∈ I.baseChange A, D.baseChange A z ∈ J.baseChange A) ↔ ∀ x ∈ I, D x ∈ J := by
  simp only [← LieSubmodule.mem_toSubmodule, LieSubmodule.coe_baseChange]
  exact LinearMap.mapsTo_baseChange_iff D.toLinearMap _ _

end FaithfullyFlat

end LieDerivation
