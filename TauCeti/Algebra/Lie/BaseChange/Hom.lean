/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.BaseChange
public import Mathlib.RingTheory.Flat.Equalizer
public import TauCeti.LinearAlgebra.TensorProduct.Kernel

/-!
# Extension of scalars of a homomorphism of Lie algebras

Mathlib extends the scalars of a Lie algebra `L` over `R` to `A ⊗[R] L` over an `R`-algebra `A`,
and `LieAlgebra.ExtendScalars.map` extends a homomorphism along a map of coefficient algebras.
That map is a homomorphism of Lie algebras over `R`, which is the right generality when the
coefficients move.  When the coefficients stay put -- the case a descent argument needs -- the
same underlying linear map `LinearMap.baseChange` is `A`-linear, and the resulting `A`-Lie
homomorphism `LieHom.baseChange` is what this file records.

The point of the `A`-linear form is that its kernel is a `LieIdeal A (A ⊗[R] L)`, and so may be
compared with `LieSubmodule.baseChange`.  The two agree over a flat coefficient algebra, and, for
a surjective homomorphism, over an arbitrary one.  Together with functoriality and the
preservation of surjectivity, that comparison is what lets a question about an ideal of
`A ⊗[R] L` be moved to one about `L`; its first use is the identification of a quotient of
`A ⊗[R] L` with the extension of a quotient of `L`.

## Main definitions

* `LieHom.baseChange`: the extension of scalars `A ⊗[R] L →ₗ⁅A⁆ A ⊗[R] L'` of a homomorphism of
  Lie algebras.

## Main results

* `LieHom.baseChange_id` and `LieHom.baseChange_comp`: extension of scalars is functorial.
* `LieHom.baseChange_surjective`: extension of scalars preserves surjectivity.
* `LieHom.ker_baseChange` and `LieHom.ker_baseChange_of_surjective`: **the kernel of an extended
  homomorphism is the extension of its kernel**, over a flat coefficient algebra, respectively for
  a surjective homomorphism over an arbitrary one.
-/

public section

open TensorProduct

namespace LieHom

universe u v w x y

variable {R : Type u} {L : Type w} {L' : Type x} {L'' : Type y}
variable [CommRing R] [LieRing L] [LieAlgebra R L] [LieRing L'] [LieAlgebra R L']
variable [LieRing L''] [LieAlgebra R L'']
variable (A : Type v) [CommRing A] [Algebra R A] (f : L →ₗ⁅R⁆ L')

/-- Mathlib's `LieAlgebra.ExtendScalars.map (AlgHom.id R A) f` and `LinearMap.baseChange A f` have
the same underlying function.  Recording the identification explicitly is what lets
`LieHom.baseChange` inherit Mathlib's proof that the former respects brackets. -/
private theorem extendScalars_map_apply (x : A ⊗[R] L) :
    LieAlgebra.ExtendScalars.map (AlgHom.id R A) f x =
      LinearMap.baseChange A (f : L →ₗ[R] L') x := by
  induction x with
  | zero => simp
  | tmul a x => simp
  | add x y hx hy => simp [hx, hy]

/-- **The extension of scalars of a homomorphism of Lie algebras**, as a homomorphism of Lie
algebras over the extended coefficients.

Its underlying map is `LinearMap.baseChange`, so it agrees with
`LieAlgebra.ExtendScalars.map (AlgHom.id R A) f`; the difference is that this form is linear over
`A` rather than over `R`, which is what makes its kernel an ideal of `A ⊗[R] L` over `A`. -/
def baseChange : A ⊗[R] L →ₗ⁅A⁆ A ⊗[R] L' where
  __ := LinearMap.baseChange A (f : L →ₗ[R] L')
  map_lie' {x y} := by
    simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, ← extendScalars_map_apply]
    exact (LieAlgebra.ExtendScalars.map (AlgHom.id R A) f).map_lie x y

@[simp]
theorem coe_baseChange :
    ((baseChange A f : A ⊗[R] L →ₗ⁅A⁆ A ⊗[R] L') : A ⊗[R] L →ₗ[A] A ⊗[R] L') =
      LinearMap.baseChange A (f : L →ₗ[R] L') :=
  (rfl)

@[simp]
theorem baseChange_tmul (a : A) (x : L) : baseChange A f (a ⊗ₜ[R] x) = a ⊗ₜ[R] f x :=
  LinearMap.baseChange_tmul (f : L →ₗ[R] L') a x

/-- Extension of scalars is functorial: it takes the identity to the identity. -/
@[simp]
theorem baseChange_id : baseChange A (LieHom.id : L →ₗ⁅R⁆ L) = LieHom.id := by
  ext x
  exact DFunLike.congr_fun (LinearMap.baseChange_id (R := R) (A := A) (M := L)) x

/-- Extension of scalars is functorial: it takes a composition to the composition. -/
theorem baseChange_comp (g : L' →ₗ⁅R⁆ L'') :
    baseChange A (g.comp f) = (baseChange A g).comp (baseChange A f) := by
  ext x
  exact DFunLike.congr_fun (LinearMap.baseChange_comp (A := A) (f := (f : L →ₗ[R] L'))
    (g := (g : L' →ₗ[R] L''))) x

/-- Extension of scalars preserves surjectivity: the tensor product is right exact. -/
theorem baseChange_surjective (hf : Function.Surjective f) :
    Function.Surjective (baseChange A f) :=
  LinearMap.baseChange_surjective A hf

/-- **Over a flat coefficient algebra, extension of scalars commutes with kernels**: the kernel of
the extended homomorphism is the extension of the kernel.

Flatness is what makes the containment `(ker f).baseChange A ≤ ker (baseChange A f)`, which holds
for any coefficient algebra, an equality.  For a surjective homomorphism it is an equality over
an arbitrary coefficient algebra, which is `LieHom.ker_baseChange_of_surjective`. -/
@[simp]
theorem ker_baseChange [Module.Flat R A] : (baseChange A f).ker = f.ker.baseChange A := by
  rw [← LieSubmodule.toSubmodule_inj, LieSubmodule.coe_baseChange, ker_toSubmodule,
    ker_toSubmodule, coe_baseChange]
  -- `LinearMap.baseChange` is `AlgebraTensorModule.lTensor` and `Submodule.baseChange` is the
  -- range of the extended inclusion, so this is Mathlib's statement verbatim.
  exact Module.Flat.ker_lTensor_eq A A (f : L →ₗ[R] L')

/-- **For a surjective homomorphism, extension of scalars commutes with kernels over an arbitrary
coefficient algebra.**  Surjectivity of `f` replaces the flatness of `A` that
`LieHom.ker_baseChange` assumes. -/
@[simp]
theorem ker_baseChange_of_surjective (hf : Function.Surjective f) :
    (baseChange A f).ker = f.ker.baseChange A := by
  rw [← LieSubmodule.toSubmodule_inj, LieSubmodule.coe_baseChange, ker_toSubmodule,
    ker_toSubmodule, coe_baseChange]
  exact LinearMap.ker_baseChange_of_surjective A (f : L →ₗ[R] L') hf

end LieHom
