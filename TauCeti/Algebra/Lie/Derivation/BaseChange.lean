/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.AdjointAction.Derivation
public import Mathlib.Algebra.Lie.Derivation.BaseChange
public import TauCeti.LinearAlgebra.LinearMap.BaseChange
public import TauCeti.LinearAlgebra.TensorProduct.Submodule

/-!
# Lie derivations after extension of scalars

Let `L` be a Lie algebra over a commutative ring `R` and let `A` be a commutative `R`-algebra.
A Lie derivation of `L` with values in a Lie `L`-module `M` extends to an `A`-linear derivation
from `A ⊗[R] L` into `A ⊗[R] M`, with underlying map `LinearMap.baseChange`. For endomorphism-valued
derivations this agrees as a function with Mathlib's `Lie.Derivation.ofLieDerivation`, which records
the extension over `R`. The `A`-linear form can be compared with `LieSubmodule.baseChange`, whose
ideals are ideals over `A`.

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
* `LieDerivation.baseChangeHom`: the same extension bundled as an `R`-linear Lie homomorphism.

## Main results

* `LieDerivation.baseChange_ad`: the extension of an inner derivation `ad x` is the inner
  derivation at `1 ⊗ₜ x`, so the construction is compatible with the adjoint action.
* `LieDerivation.baseChange_zero`, `LieDerivation.baseChange_add`,
  `LieDerivation.baseChange_smul` and
  `LieDerivation.baseChange_lie`: extension of scalars respects the additive and the bracket
  structure of the derivations.
* `LieDerivation.baseChange_injective`: over a faithfully flat coefficient algebra, two derivations
  agreeing after extension of scalars are equal.
* `LieDerivation.mapsTo_baseChange_lieIdeal_iff`: **over a faithfully flat coefficient algebra, a
  derivation maps one Lie ideal into another exactly when the extended derivation maps the
  extension of the first into the extension of the second.**

The core construction, additive compatibility, pure-tensor formula, underlying-map formula,
and injectivity apply to
any Lie `L`-module `M`. The comparison with Mathlib's endomorphism extension, the Lie-homomorphism
bundle, inner derivations, and ideal descent specialize to `M = L`.
-/

public section

open TensorProduct

namespace LieDerivation

universe u v w

variable {R : Type u} {A : Type v} {L : Type w}
variable [CommRing R] [CommRing A] [Algebra R A] [LieRing L] [LieAlgebra R L]

section LieModule

variable {M : Type*} [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

variable (A) in
/-- Extension of an `M`-valued Lie derivation of `L` to the scalar extensions of `L` and `M`,
as a derivation over `A`.  Its underlying map is `LinearMap.baseChange`, so it sends `a ⊗ₜ x` to
`a ⊗ₜ D x`. -/
def baseChange (D : LieDerivation R L M) : LieDerivation A (A ⊗[R] L) (A ⊗[R] M) where
  toLinearMap := D.toLinearMap.baseChange A
  leibniz' x y := by
    induction x using TensorProduct.inductionOn with
    | tmul a x =>
      induction y using TensorProduct.inductionOn with
      | tmul b y =>
        simp [LieAlgebra.ExtendScalars.bracket_tmul, D.apply_lie_eq_sub, tmul_sub, mul_comm]
      | add y z hy hz =>
        simp only [lie_add, add_lie, map_add, hy, hz, sub_add_sub_comm]
    | add x z hx hz =>
      simp only [add_lie, lie_add, map_add, hx, hz, sub_add_sub_comm]

/-- The extended derivation differentiates the second factor of a pure tensor. -/
@[simp]
theorem baseChange_tmul (D : LieDerivation R L M) (a : A) (x : L) :
    D.baseChange A (a ⊗ₜ[R] x) = a ⊗ₜ[R] D x := by
  exact LinearMap.baseChange_tmul D.toLinearMap a x

/-- The linear map underlying the extension of `D` is the extension of the linear map underlying
`D`; this is what lets the linear-algebraic base-change API apply to it. -/
@[simp]
theorem baseChange_toLinearMap (D : LieDerivation R L M) :
    (D.baseChange A).toLinearMap = D.toLinearMap.baseChange A :=
  (rfl)


/-- The zero derivation extends to the zero derivation. -/
@[simp]
theorem baseChange_zero : (0 : LieDerivation R L M).baseChange A = 0 := by
  apply LieDerivation.ext
  intro z
  exact DFunLike.congr_fun (LinearMap.baseChange_zero (A := A) (M := L) (N := M)) z

/-- Extension of scalars is additive in the derivation. -/
@[simp]
theorem baseChange_add (D E : LieDerivation R L M) :
    (D + E).baseChange A = D.baseChange A + E.baseChange A := by
  apply LieDerivation.ext
  intro z
  exact DFunLike.congr_fun (LinearMap.baseChange_add (A := A)
    (f := D.toLinearMap) (g := E.toLinearMap)) z

/-- Extension of scalars preserves the negative of a derivation. -/
@[simp]
theorem baseChange_neg (D : LieDerivation R L M) :
    (-D).baseChange A = -D.baseChange A := by
  apply LieDerivation.ext
  intro z
  exact DFunLike.congr_fun (LinearMap.baseChange_neg (A := A) (f := D.toLinearMap)) z

/-- Extension of scalars preserves the difference of two derivations. -/
@[simp]
theorem baseChange_sub (D E : LieDerivation R L M) :
    (D - E).baseChange A = D.baseChange A - E.baseChange A := by
  apply LieDerivation.ext
  intro z
  exact DFunLike.congr_fun (LinearMap.baseChange_sub (A := A)
    (f := D.toLinearMap) (g := E.toLinearMap)) z

/-- Extension of scalars preserves scalar multiplication by the original coefficient ring. -/
@[simp]
theorem baseChange_smul (r : R) (D : LieDerivation R L M) :
    (r • D).baseChange A = algebraMap R A r • D.baseChange A := by
  apply LieDerivation.ext
  intro z
  have hD : (r • D).toLinearMap = r • D.toLinearMap := by
    ext x
    rfl
  -- Evaluation hides the derivation's defining linear map under its function coercion.
  -- Expose that map so `hD` rewrites the source scalar action and `algebraMap_smul`
  -- identifies the target coefficient action; ordinary rewriting cannot reach it underneath.
  change (r • D).toLinearMap.baseChange A z =
    algebraMap R A r • D.toLinearMap.baseChange A z
  rw [hD, LinearMap.baseChange_smul, LinearMap.smul_apply, algebraMap_smul]



variable [Module.FaithfullyFlat R A]

/-- Over a faithfully flat coefficient algebra no information is lost by extending a derivation:
two derivations agreeing after extension of scalars are equal. -/
theorem baseChange_injective :
    Function.Injective (baseChange A : LieDerivation R L M → LieDerivation A _ _) := by
  intro D E h
  have hL : D.toLinearMap = E.toLinearMap :=
    LinearMap.baseChange_injective (A := A) (by
      rw [← baseChange_toLinearMap, ← baseChange_toLinearMap, h])
  exact LieDerivation.ext fun x => DFunLike.congr_fun hL x

end LieModule

/-- The `R`-linear extension `Lie.Derivation.ofLieDerivation` supplied by Mathlib and the
`A`-linear extension `LieDerivation.baseChange` are the same function: only the ring over which
each is recorded as linear differs. -/
@[simp]
theorem coe_ofLieDerivation (D : LieDerivation R L L) :
    ⇑(Lie.Derivation.ofLieDerivation A D) = ⇑(D.baseChange A) := by
  funext z
  rw [Lie.Derivation.ofLieDerivation_apply]
  exact (congrFun (LinearMap.baseChange_eq_lTensor D.toLinearMap) z).symm

variable (A) in
/-- Extension of scalars as an `R`-linear homomorphism of Lie algebras. The extended derivations
are `A`-linear, and their coefficient scalars are restricted to `R` for this homomorphism. -/
def baseChangeHom : LieDerivation R L L →ₗ⁅R⁆
    RestrictScalars R A (LieDerivation A (A ⊗[R] L) (A ⊗[R] L)) where
  toFun := baseChange A
  map_add' D E := baseChange_add D E
  map_smul' r D := by
    -- RestrictScalars defines the target action through the coefficient algebra map.
    change (r • D).baseChange A = algebraMap R A r • D.baseChange A
    exact baseChange_smul r D
  map_lie' {D E} := by
    apply LieDerivation.ext
    intro z
    have h := congrFun (coe_ofLieDerivation (A := A) ⁅D, E⁆) z
    rw [LieHom.map_lie] at h
    simp only [LieDerivation.lie_apply, coe_ofLieDerivation] at h
    exact h.symm

/-- The bundled scalar-extension homomorphism applies as the extended derivation. -/
@[simp]
theorem baseChangeHom_apply (D : LieDerivation R L L) : baseChangeHom A D = D.baseChange A :=
  (rfl)

/-- Extension of scalars is compatible with the bracket of derivations. -/
@[simp]
theorem baseChange_lie (D E : LieDerivation R L L) :
    (⁅D, E⁆ : LieDerivation R L L).baseChange A = ⁅D.baseChange A, E.baseChange A⁆ :=
  LieHom.map_lie (baseChangeHom A) D E

/-- The extension of the inner derivation at `x` is the inner derivation at `1 ⊗ₜ x`. -/
@[simp]
theorem baseChange_ad (x : L) :
    (ad R L x).baseChange A = ad A (A ⊗[R] L) ((1 : A) ⊗ₜ[R] x) := by
  ext z
  induction z using TensorProduct.inductionOn with
  | tmul a y => simp [LieAlgebra.ExtendScalars.bracket_tmul]
  | add y z hy hz => simp [map_add, hy, hz]

section FaithfullyFlat

variable [Module.FaithfullyFlat R A]


variable (D : LieDerivation R L L)

/-- Over a faithfully flat coefficient algebra, the extended derivation sends the extension of
`I` into the extension of `J` exactly when the original derivation sends `I` into `J`. -/
theorem mapsTo_baseChange_lieIdeal_iff (I J : LieIdeal R L) :
    (∀ z ∈ I.baseChange A, D.baseChange A z ∈ J.baseChange A) ↔ ∀ x ∈ I, D x ∈ J := by
  have h := Submodule.baseChange_le_iff (A := A)
    (p := I.toSubmodule.map D.toLinearMap) (q := J.toSubmodule)
  rw [Submodule.baseChange_map, Submodule.map_le_iff_le_comap,
    Submodule.map_le_iff_le_comap] at h
  simp only [← LieSubmodule.mem_toSubmodule, LieSubmodule.coe_baseChange]
  exact ⟨fun hD x hx => h.mp (fun z hz => hD z hz) hx,
    fun hD z hz => h.mpr (fun x hx => hD x hx) hz⟩

end FaithfullyFlat

end LieDerivation
