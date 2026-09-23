/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.BaseChange
public import Mathlib.RingTheory.Flat.Basic
public import TauCeti.Algebra.Lie.Quotient
-- Private: the exactness of `ker f ↪ L → L'` and the exactness of tensoring a flat module with it
-- are used only inside the proof of `LieHom.ker_baseChange`.
import Mathlib.Algebra.Exact.Basic
-- Private: the kernel of a map lifted to a quotient is used only inside the construction of
-- `LieIdeal.quotientBaseChangeEquiv`.
import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Extension of scalars commutes with quotients of Lie algebras

Mathlib extends the scalars of a Lie algebra `L` over `R` to `A ⊗[R] L` over an `R`-algebra `A`,
and `LieAlgebra.ExtendScalars.map` extends a homomorphism along a map of coefficient algebras.
That map is a homomorphism of Lie algebras over `R`, which is the right generality when the
coefficients move.  When the coefficients stay put -- the case a descent argument needs -- the
same underlying linear map `LinearMap.baseChange` is `A`-linear, and the resulting `A`-Lie
homomorphism `LieHom.baseChange` is what this file records.

The point of the `A`-linear form is that its kernel is a `LieIdeal A (A ⊗[R] L)`, so it can be
compared with `LieSubmodule.baseChange`.  Over a flat coefficient algebra the comparison is an
equality: extension of scalars is exact, so it commutes with kernels.  Applied to the quotient
map of an ideal `I` this says that `A ⊗[R] L → A ⊗[R] (L ⧸ I)` presents `A ⊗[R] (L ⧸ I)` as the
quotient by `I.baseChange A`, the isomorphism

`(A ⊗[R] L) ⧸ I.baseChange A ≃ₗ⁅A⁆ A ⊗[R] (L ⧸ I)`.

Flatness is what keeps the kernel no larger than `I.baseChange A`; surjectivity, the other half,
is right-exactness of the tensor product and asks nothing of `A`.

## Main definitions

* `LieHom.baseChange`: the extension of scalars `A ⊗[R] L →ₗ⁅A⁆ A ⊗[R] L'` of a homomorphism of
  Lie algebras.
* `LieIdeal.quotientBaseChangeEquiv`: **extension of scalars commutes with quotients.**

## Main results

* `LieHom.baseChange_surjective`: extension of scalars preserves surjectivity.
* `LieHom.ker_baseChange`: **over a flat coefficient algebra the kernel of an extended
  homomorphism is the extension of its kernel.**

## References

* [N. Bourbaki, *Algebra I, Chapters 1-3*][bourbaki1989], Chapter II, §3, n°6, for the
  right-exactness of the tensor product that the kernel computation rests on.
-/

public section

open TensorProduct

namespace LieHom

universe u v w x

variable {R : Type u} {L : Type w} {L' : Type x}
variable [CommRing R] [LieRing L] [LieAlgebra R L] [LieRing L'] [LieAlgebra R L']
variable (A : Type v) [CommRing A] [Algebra R A] (f : L →ₗ⁅R⁆ L')

/-- **The extension of scalars of a homomorphism of Lie algebras**, as a homomorphism of Lie
algebras over the extended coefficients.

Its underlying map is `LinearMap.baseChange`, so it agrees with
`LieAlgebra.ExtendScalars.map (AlgHom.id R A) f`; the difference is that this form is linear over
`A` rather than over `R`, which is what makes its kernel an ideal of `A ⊗[R] L` over `A`. -/
def baseChange : A ⊗[R] L →ₗ⁅A⁆ A ⊗[R] L' where
  __ := LinearMap.baseChange A (f : L →ₗ[R] L')
  map_lie' {x y} := by
    simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom]
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a u =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul b v =>
        simp [LieAlgebra.ExtendScalars.bracket_tmul]
      | add y z hy hz => simp only [lie_add, map_add, hy, hz]
    | add x z hx hz => simp only [add_lie, map_add, hx, hz]

@[simp]
theorem coe_baseChange :
    ((baseChange A f : A ⊗[R] L →ₗ⁅A⁆ A ⊗[R] L') : A ⊗[R] L →ₗ[A] A ⊗[R] L') =
      LinearMap.baseChange A (f : L →ₗ[R] L') :=
  (rfl)

theorem baseChange_apply (x : A ⊗[R] L) :
    baseChange A f x = LinearMap.baseChange A (f : L →ₗ[R] L') x :=
  (rfl)

@[simp]
theorem baseChange_tmul (a : A) (x : L) : baseChange A f (a ⊗ₜ[R] x) = a ⊗ₜ[R] f x :=
  (rfl)

/-- Extension of scalars preserves surjectivity: the tensor product is right exact. -/
theorem baseChange_surjective (hf : Function.Surjective f) :
    Function.Surjective (baseChange A f) := fun y => by
  obtain ⟨x, hx⟩ := LinearMap.lTensor_surjective A hf y
  exact ⟨x, by simpa only [baseChange_apply, LinearMap.baseChange_eq_ltensor] using hx⟩

/-- **Over a flat coefficient algebra, extension of scalars commutes with kernels.**  The kernel
of the extended homomorphism is the extension of the kernel, because tensoring with a flat module
carries the exact pair `ker f ↪ L → L'` to an exact pair. -/
theorem ker_baseChange [Module.Flat R A] : (baseChange A f).ker = f.ker.baseChange A := by
  have hexact : Function.Exact
      (LinearMap.lTensor A (LinearMap.ker (f : L →ₗ[R] L')).subtype)
      (LinearMap.lTensor A (f : L →ₗ[R] L')) :=
    Module.Flat.lTensor_exact A (LinearMap.exact_subtype_ker_map (f : L →ₗ[R] L'))
  rw [← LieSubmodule.toSubmodule_inj, LieSubmodule.coe_baseChange, ker_toSubmodule,
    ker_toSubmodule]
  refine Submodule.ext fun x => ?_
  rw [LinearMap.mem_ker, coe_baseChange, LinearMap.baseChange_eq_ltensor]
  refine (hexact x).trans (exists_congr fun y => ?_)
  rw [LinearMap.baseChange_eq_ltensor]

end LieHom

namespace LieIdeal

universe u v w

variable {R : Type u} {L : Type w} [CommRing R] [LieRing L] [LieAlgebra R L]
variable (A : Type v) [CommRing A] [Algebra R A] (I : LieIdeal R L)

/-- Over a flat coefficient algebra the extension of scalars of the quotient map of `I` kills
exactly the extension of `I`. -/
theorem ker_baseChange_mkQ [Module.Flat R A] :
    (LieHom.baseChange A I.mkQ).ker = I.baseChange A := by
  rw [LieHom.ker_baseChange, ker_mkQ]

/-- **Extension of scalars commutes with quotients of Lie algebras.**  Over a flat coefficient
algebra the extended quotient map presents `A ⊗[R] (L ⧸ I)` as the quotient of `A ⊗[R] L` by the
extension of `I`.

The isomorphism is the obvious one, sending the class of `a ⊗ₜ x` to `a ⊗ₜ` the class of `x`;
that is `LieIdeal.quotientBaseChangeEquiv_mk_tmul`.  The characterizing lemmas below are phrased
with `LieSubmodule.Quotient.mk` rather than `LieIdeal.mkQ`, which is the form the quotient's
induction principle produces. -/
noncomputable def quotientBaseChangeEquiv [Module.Flat R A] :
    ((A ⊗[R] L) ⧸ I.baseChange A) ≃ₗ⁅A⁆ A ⊗[R] (L ⧸ I) :=
  LieEquiv.ofBijective (liftQ (I.baseChange A) (LieHom.baseChange A I.mkQ)
      (ker_baseChange_mkQ A I).ge) <| by
    refine ⟨(injective_iff_map_eq_zero _).mpr fun u hu => ?_, fun y => ?_⟩
    · obtain ⟨x, rfl⟩ := mkQ_surjective (I.baseChange A) u
      rw [mkQ_apply, liftQ_apply] at hu
      rw [mkQ_apply]
      refine (LieSubmodule.Quotient.mk_eq_zero _).mpr ?_
      rw [← ker_baseChange_mkQ A I]
      exact LieHom.mem_ker.mpr hu
    · obtain ⟨x, hx⟩ := LieHom.baseChange_surjective A I.mkQ I.mkQ_surjective y
      exact ⟨LieSubmodule.Quotient.mk x, by rw [liftQ_apply]; exact hx⟩

@[simp]
theorem quotientBaseChangeEquiv_mk [Module.Flat R A] (x : A ⊗[R] L) :
    quotientBaseChangeEquiv A I (LieSubmodule.Quotient.mk x) = LieHom.baseChange A I.mkQ x :=
  liftQ_apply (I.baseChange A) (LieHom.baseChange A I.mkQ) _ x

theorem quotientBaseChangeEquiv_mk_tmul [Module.Flat R A] (a : A) (x : L) :
    quotientBaseChangeEquiv A I (LieSubmodule.Quotient.mk (a ⊗ₜ[R] x)) =
      a ⊗ₜ[R] LieSubmodule.Quotient.mk x := by
  rw [quotientBaseChangeEquiv_mk, LieHom.baseChange_tmul, mkQ_apply]

end LieIdeal
