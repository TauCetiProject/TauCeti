/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.BaseChange
public import Mathlib.RingTheory.Flat.Equalizer
public import TauCeti.LinearAlgebra.TensorProduct.Kernel
public import TauCeti.RingTheory.TensorProduct.IsBaseChange

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

A homomorphism `f : L →ₗ⁅R⁆ L'` into a Lie algebra `L'` that is already a Lie algebra over `A`
also extends `A`-linearly to `A ⊗[R] L`, by `a ⊗ x ↦ a • f x`: this is the universal property of
extension of scalars, and its underlying map is `LinearMap.liftBaseChange`.  When `f` exhibits
`L'` as the base change of `L` in Mathlib's sense `IsBaseChange`, the extension is bijective, so
`A ⊗[R] L` and `L'` are isomorphic as Lie algebras over `A`.  This is how a Lie subalgebra over
`R` of a Lie algebra over `A` is recognised as an `R`-form of it, for instance a real form of a
complex Lie algebra.

## Main definitions

* `LieHom.baseChange`: the extension of scalars `A ⊗[R] L →ₗ⁅A⁆ A ⊗[R] L'` of a homomorphism of
  Lie algebras.
* `LieHom.liftBaseChange`: the extension `A ⊗[R] L →ₗ⁅A⁆ L'` of a homomorphism into a Lie algebra
  over `A`.
* `IsBaseChange.lieEquiv`: if `f` is a base change, the Lie algebra equivalence
  `A ⊗[R] L ≃ₗ⁅A⁆ L'` it induces.

## Main results

* `LieHom.baseChange_id` and `LieHom.baseChange_comp`: extension of scalars is functorial.
* `LieHom.baseChange_surjective`: extension of scalars preserves surjectivity.
* `LieHom.ker_baseChange` and `LieHom.ker_baseChange_of_surjective`: **the kernel of an extended
  homomorphism is the extension of its kernel**, over a flat coefficient algebra, respectively for
  a surjective homomorphism over an arbitrary one.
* `LieHom.baseChange_ext` and `LieHom.eq_liftBaseChange_iff`: a homomorphism out of `A ⊗[R] L` is
  determined by its values on `1 ⊗ x`, so `LieHom.liftBaseChange` is the unique extension.
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

section LiftBaseChange

variable {R A L L' : Type*} [CommRing R] [CommRing A] [Algebra R A]
  [LieRing L] [LieAlgebra R L] [LieRing L'] [LieAlgebra A L'] [LieAlgebra R L']
  [IsScalarTower R A L']

namespace LieHom

variable (A) (f : L →ₗ⁅R⁆ L')

/-- **Extension of scalars of a homomorphism into a Lie algebra over `A`.**  A homomorphism of Lie
algebras over `R` from `L` into a Lie algebra `L'` over the `R`-algebra `A` extends to the
homomorphism of Lie algebras over `A` sending `a ⊗ x` to `a • f x`.  Its underlying linear map is
`LinearMap.liftBaseChange`. -/
def liftBaseChange : A ⊗[R] L →ₗ⁅A⁆ L' where
  __ := (f : L →ₗ[R] L').liftBaseChange A
  map_lie' {x y} := by
    simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom]
    induction x with
    | add x₁ x₂ h₁ h₂ => simp only [add_lie, map_add, h₁, h₂]
    | tmul a x =>
      induction y with
      | add y₁ y₂ h₁ h₂ => simp only [lie_add, map_add, h₁, h₂]
      | tmul b y =>
        simp only [LieAlgebra.ExtendScalars.bracket_tmul, LinearMap.liftBaseChange_tmul,
          LieHom.coe_toLinearMap, map_lie, smul_lie, lie_smul, mul_smul]
        exact smul_comm a b _

@[simp]
theorem coe_liftBaseChange :
    ((liftBaseChange A f : A ⊗[R] L →ₗ⁅A⁆ L') : A ⊗[R] L →ₗ[A] L') =
      (f : L →ₗ[R] L').liftBaseChange A :=
  (rfl)

@[simp]
theorem liftBaseChange_tmul (a : A) (x : L) : liftBaseChange A f (a ⊗ₜ[R] x) = a • f x :=
  (rfl)

omit [LieAlgebra R L'] [IsScalarTower R A L'] in
variable {A} in
/-- Homomorphisms of Lie algebras over `A` out of `A ⊗[R] L` are determined by their values on
the elements `1 ⊗ x`, since `a ⊗ x = a • (1 ⊗ x)`. -/
@[ext]
theorem baseChange_ext ⦃g h : A ⊗[R] L →ₗ⁅A⁆ L'⦄ (H : ∀ x, g (1 ⊗ₜ[R] x) = h (1 ⊗ₜ[R] x)) :
    g = h := by
  ext u
  induction u with
  | tmul a x => rw [← mul_one a, ← smul_eq_mul, ← TensorProduct.smul_tmul', map_smul, map_smul, H]
  | add u v hu hv => rw [map_add, map_add, hu, hv]

/-- **Uniqueness in the universal property of extension of scalars**: `LieHom.liftBaseChange A f`
is the only homomorphism of Lie algebras over `A` out of `A ⊗[R] L` sending `1 ⊗ x` to `f x`. -/
theorem eq_liftBaseChange_iff {g : A ⊗[R] L →ₗ⁅A⁆ L'} :
    g = liftBaseChange A f ↔ ∀ x, g (1 ⊗ₜ[R] x) = f x :=
  ⟨fun h x ↦ by rw [h, liftBaseChange_tmul, one_smul], fun h ↦
    baseChange_ext fun x ↦ by rw [h, liftBaseChange_tmul, one_smul]⟩

end LieHom

namespace IsBaseChange

variable {f : L →ₗ⁅R⁆ L'} (h : IsBaseChange A (f : L →ₗ[R] L'))

/-- **A base change of Lie algebras is an isomorphism from the extension of scalars.**  If `f`
exhibits `L'` as the base change of `L` along `R → A`, then `a ⊗ x ↦ a • f x` is an isomorphism
of Lie algebras over `A` from `A ⊗[R] L` onto `L'`.  Its underlying linear equivalence is
`IsBaseChange.equiv`. -/
noncomputable def lieEquiv : A ⊗[R] L ≃ₗ⁅A⁆ L' :=
  LieEquiv.ofBijective (f.liftBaseChange A) h.liftBaseChange_bijective

@[simp]
theorem lieEquiv_tmul (a : A) (x : L) : h.lieEquiv (a ⊗ₜ[R] x) = a • f x :=
  (rfl)

@[simp]
theorem lieEquiv_symm_apply (x : L) : h.lieEquiv.symm (f x) = 1 ⊗ₜ[R] x := by
  rw [LieEquiv.symm_apply_eq, lieEquiv_tmul, one_smul]

@[simp]
theorem toLinearEquiv_lieEquiv : h.lieEquiv.toLinearEquiv = h.equiv := by
  ext t
  induction t with
  | tmul a x => simp
  | add t₁ t₂ h₁ h₂ => simp only [map_add, h₁, h₂]

end IsBaseChange

end LiftBaseChange
