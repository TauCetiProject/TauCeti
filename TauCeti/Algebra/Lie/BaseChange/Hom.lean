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
* `LieEquiv.baseChange`: the extension of scalars `A ⊗[R] L ≃ₗ⁅A⁆ A ⊗[R] L'` of an isomorphism of
  Lie algebras.
* `LieHom.liftBaseChange`: the extension `A ⊗[R] L →ₗ⁅A⁆ L'` of a homomorphism into a Lie algebra
  over `A`.
* `IsBaseChange.lieEquiv`: if `f` is a base change, the Lie algebra equivalence
  `A ⊗[R] L ≃ₗ⁅A⁆ L'` it induces.
* `IsBaseChange.lieEquivOfCodRestrict`: if the corestriction of `f` to a Lie subalgebra `P` over
  `A` is a base change, the Lie algebra equivalence `A ⊗[R] L ≃ₗ⁅A⁆ P` it induces.

## Main results

* `LieHom.baseChange_id` and `LieHom.baseChange_comp`: extension of scalars is functorial, and so
  is its version `LieEquiv.baseChange_refl`, `LieEquiv.baseChange_trans` for isomorphisms.
* `LieHom.baseChange_surjective`: extension of scalars preserves surjectivity.
* `LieHom.ker_baseChange` and `LieHom.ker_baseChange_of_surjective`: **the kernel of an extended
  homomorphism is the extension of its kernel**, over a flat coefficient algebra, respectively for
  a surjective homomorphism over an arbitrary one.
* `LieHom.baseChange_ext` and `LieHom.eq_liftBaseChange_iff`: a homomorphism out of `A ⊗[R] L` is
  determined by its values on `1 ⊗ x`, so `LieHom.liftBaseChange` is the unique extension.
* `IsBaseChange.liftBaseChange_injective_of_codRestrict` and
  `IsBaseChange.range_liftBaseChange_of_codRestrict`: if the corestriction of `f` to a Lie
  subalgebra `P` over `A` is a base change, then `LieHom.liftBaseChange A f` is injective with
  range `P`.
* `IsBaseChange.toLinearEquiv_lieEquiv` and `IsBaseChange.toLinearEquiv_lieEquivOfCodRestrict`:
  the underlying linear equivalences are those of `IsBaseChange.equiv`.
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

/-- Scalar extension preserves an intertwining equation. -/
theorem baseChange_intertwines {f : L →ₗ⁅R⁆ L} {g : L' →ₗ⁅R⁆ L'}
    (u : L →ₗ⁅R⁆ L') (h : g.comp u = u.comp f) :
    (g.baseChange A).comp (u.baseChange A) = (u.baseChange A).comp (f.baseChange A) := by
  rw [← baseChange_comp, h, baseChange_comp]

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

namespace LieEquiv

variable {R L L' L'' : Type*} [CommRing R] [LieRing L] [LieAlgebra R L] [LieRing L']
  [LieAlgebra R L'] [LieRing L''] [LieAlgebra R L'']
variable (A : Type*) [CommRing A] [Algebra R A]

/-- **The extension of scalars of an isomorphism of Lie algebras**, as an isomorphism of Lie
algebras over the extended coefficients.  Its forward map is `LieHom.baseChange`, and its
underlying linear equivalence is `LinearEquiv.baseChange`. -/
def baseChange (e : L ≃ₗ⁅R⁆ L') : A ⊗[R] L ≃ₗ⁅A⁆ A ⊗[R] L' where
  __ := LieHom.baseChange A (e : L →ₗ⁅R⁆ L')
  __ := e.toLinearEquiv.baseChange R A L L'

@[simp]
theorem baseChange_tmul (e : L ≃ₗ⁅R⁆ L') (a : A) (x : L) :
    baseChange A e (a ⊗ₜ[R] x) = a ⊗ₜ[R] e x :=
  (rfl)

@[simp]
theorem toLieHom_baseChange (e : L ≃ₗ⁅R⁆ L') :
    (baseChange A e).toLieHom = LieHom.baseChange A (e : L →ₗ⁅R⁆ L') :=
  (rfl)

@[simp]
theorem toLinearEquiv_baseChange (e : L ≃ₗ⁅R⁆ L') :
    (baseChange A e).toLinearEquiv = e.toLinearEquiv.baseChange R A L L' :=
  (rfl)

@[simp]
theorem baseChange_symm (e : L ≃ₗ⁅R⁆ L') : (baseChange A e).symm = baseChange A e.symm :=
  (rfl)

@[simp]
theorem baseChange_refl : baseChange A (LieEquiv.refl : L ≃ₗ⁅R⁆ L) = LieEquiv.refl :=
  toLinearEquiv_injective (LinearEquiv.baseChange_one R A L)

theorem baseChange_trans (e : L ≃ₗ⁅R⁆ L') (e' : L' ≃ₗ⁅R⁆ L'') :
    baseChange A (e.trans e') = (baseChange A e).trans (baseChange A e') :=
  toLinearEquiv_injective (LinearEquiv.baseChange_trans R A L L' e.toLinearEquiv e'.toLinearEquiv)

end LieEquiv

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

namespace LieHom

variable {f : L →ₗ⁅R⁆ L'} {P : LieSubalgebra A L'} {hfP : ∀ x, f x ∈ P}

/-- The values of the extension of scalars of the corestriction of `f` to `P`, read in `L'`, are
those of the extension of scalars `LieHom.liftBaseChange A f` of `f`. -/
theorem coe_liftBaseChange_codRestrict (u : A ⊗[R] L) :
    (((f : L →ₗ[R] L').codRestrict (P.toSubmodule.restrictScalars R) hfP).liftBaseChange A u :
      L') = f.liftBaseChange A u := by
  induction u with
  | tmul a x =>
    -- The `A`-action on `P.restrictScalars R` is `P`'s action, transported by the instance
    -- `Submodule.restrictScalars.origModule`; no simp lemma moves the coercion through it, so
    -- `rfl` unfolds the coercion of `a • ⟨f x, _⟩` by definition.
    rw [LinearMap.liftBaseChange_tmul, LieHom.liftBaseChange_tmul]
    rfl
  | add u v hu hv => simp only [map_add, Submodule.coe_add, hu, hv]

end LieHom

namespace IsBaseChange

variable {f : L →ₗ⁅R⁆ L'} {P : LieSubalgebra A L'} {hfP : ∀ x, f x ∈ P}
variable (h : IsBaseChange A ((f : L →ₗ[R] L').codRestrict (P.toSubmodule.restrictScalars R) hfP))
include h

/-- If the corestriction of `f` to a Lie subalgebra `P` over `A` is a base change, then the
extension of scalars `LieHom.liftBaseChange A f` of `f` is injective. -/
theorem liftBaseChange_injective_of_codRestrict :
    Function.Injective (f.liftBaseChange A) := fun u v huv ↦
  h.liftBaseChange_injective (Subtype.ext (by
    simpa only [LieHom.coe_liftBaseChange_codRestrict] using huv))

/-- If the corestriction of `f` to a Lie subalgebra `P` over `A` is a base change, then the range
of the extension of scalars `LieHom.liftBaseChange A f` of `f` is `P`. -/
theorem range_liftBaseChange_of_codRestrict : (f.liftBaseChange A).range = P := by
  ext y
  refine ⟨?_, fun hy ↦ ?_⟩
  · rintro ⟨u, rfl⟩
    exact LieHom.coe_liftBaseChange_codRestrict (hfP := hfP) u ▸ Subtype.prop _
  · obtain ⟨u, hu⟩ := h.liftBaseChange_bijective.2 ⟨y, hy⟩
    exact ⟨u, (LieHom.coe_liftBaseChange_codRestrict u).symm.trans (congrArg Subtype.val hu)⟩

/-- **A base change of Lie algebras onto a Lie subalgebra.**  Let `f` be a homomorphism of Lie
algebras over `R` into a Lie algebra `L'` over `A`, with values in a Lie subalgebra `P` over `A`.
If the corestriction of `f` to `P` exhibits `P` as the base change of `L` along `R → A`, then
`a ⊗ x ↦ a • f x` is an isomorphism of Lie algebras over `A` from `A ⊗[R] L` onto `P`.  This is
how an `R`-form of a Lie subalgebra of `L'` is recognised, for instance a real form of a complex
Lie subalgebra of a complex matrix algebra. -/
noncomputable def lieEquivOfCodRestrict : A ⊗[R] L ≃ₗ⁅A⁆ P :=
  (LieEquiv.ofInjective _ (liftBaseChange_injective_of_codRestrict h)).trans
    (LieEquiv.ofEq _ _ (by rw [range_liftBaseChange_of_codRestrict h]))

@[simp]
theorem coe_lieEquivOfCodRestrict_tmul (a : A) (x : L) :
    (h.lieEquivOfCodRestrict (a ⊗ₜ[R] x) : L') = a • f x := by
  simp [lieEquivOfCodRestrict]

@[simp]
theorem lieEquivOfCodRestrict_symm_apply (x : L) :
    h.lieEquivOfCodRestrict.symm ⟨f x, hfP x⟩ = 1 ⊗ₜ[R] x := by
  rw [LieEquiv.symm_apply_eq]
  exact Subtype.ext (by rw [coe_lieEquivOfCodRestrict_tmul, one_smul])

/-- The underlying linear equivalence of `IsBaseChange.lieEquivOfCodRestrict` is `h.equiv`,
followed by the identification of `P.restrictScalars R` with `P`. -/
@[simp]
theorem toLinearEquiv_lieEquivOfCodRestrict :
    h.lieEquivOfCodRestrict.toLinearEquiv =
      h.equiv.trans (Submodule.restrictScalarsEquiv R A L' P.toSubmodule) := by
  refine LinearEquiv.ext fun t ↦ ?_
  induction t with
  | tmul a x =>
    apply Subtype.ext
    simp only [LieEquiv.coe_toLinearEquiv, coe_lieEquivOfCodRestrict_tmul,
      LinearEquiv.trans_apply, IsBaseChange.equiv_tmul, map_smul, Submodule.coe_smul_of_tower]
    -- `Submodule.restrictScalarsEquiv` and the corestriction leave the underlying element `f x`
    -- unchanged by definition.
    rfl
  | add t₁ t₂ h₁ h₂ => simp only [map_add, h₁, h₂]

end IsBaseChange

end LiftBaseChange
