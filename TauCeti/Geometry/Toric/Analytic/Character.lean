/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Equiv.TypeTags
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import TauCeti.Algebra.Group.FreeAbelianCharacter

/-!
# Integral characters on the complex torus

For an additive character lattice `N`, its integral character lattice is `N →+ ℤ`.  The
corresponding complex torus is represented without coordinates as the additive characters of this
lattice with values
in `ℂˣ`.  Evaluation is therefore the canonical pairing between an additive character and its
argument.

This file records the multiplicative laws of that pairing, its contravariant naturality in the
character lattice (and hence covariance in `N`), and the fact that integral characters separate
torus points.  Given an identification of the character lattice with a free abelian group,
`complexTorusCoordinates` connects this coordinate-free carrier to Tau Ceti's existing
`freeAbelianCharEquiv`.

## Main declarations

* `TauCeti.Toric.IntegralCharacter`: the integral character lattice of `N`.
* `TauCeti.Toric.ComplexTorus`: its coordinate-free complex torus.
* `TauCeti.Toric.characterEvaluation`: evaluation of a character as a homomorphism on the torus.
* `TauCeti.Toric.complexTorusMap`: the torus map induced by an additive map of lattices.
* `TauCeti.Toric.exists_characterEvaluation_ne`: integral characters separate torus points.
* `TauCeti.Toric.complexTorusCoordinates`: coordinates supplied by a free presentation of the
  character lattice.

## References

* D. Cox, J. Little and H. Schenck, *Toric Varieties*, §1.1.
* W. Fulton, *Introduction to Toric Varieties*, §1.1.
-/

public section

namespace TauCeti.Toric

open Multiplicative

variable {N N' N'' : Type*}
  [AddCommGroup N] [Module.Free ℤ N] [Module.Finite ℤ N]
  [AddCommGroup N'] [Module.Free ℤ N'] [Module.Finite ℤ N']
  [AddCommGroup N''] [Module.Free ℤ N''] [Module.Finite ℤ N'']

/-- The lattice of integral characters of a finite free `ℤ`-module `N`. -/
abbrev IntegralCharacter (N : Type*) [AddCommGroup N] [Module.Free ℤ N] [Module.Finite ℤ N] :=
  let _ := (inferInstance : Module.Free ℤ N)
  let _ := (inferInstance : Module.Finite ℤ N)
  N →+ ℤ

/-- The coordinate-free complex torus with character lattice `N →+ ℤ`, for a finite free `ℤ`-
module `N`.

`AddChar` is the additive-domain form of the equivalent Mathlib carrier
`Multiplicative (N →+ ℤ) →* ℂˣ`; using it makes evaluation and pullback of characters direct. -/
abbrev ComplexTorus (N : Type*) [AddCommGroup N] [Module.Free ℤ N] [Module.Finite ℤ N] :=
  AddChar (IntegralCharacter N) ℂˣ

/-- Evaluation of the integral character `m` as a homomorphism on complex-torus points.

The map is the homomorphism obtained by evaluating an additive character at `m`. -/
def characterEvaluation (m : IntegralCharacter N) : ComplexTorus N →* ℂˣ :=
  (MonoidHom.eval (Multiplicative.ofAdd m)).comp AddChar.toMonoidHomMulEquiv.toMonoidHom

/-- Character evaluation is ordinary application of the underlying additive character. -/
@[simp]
theorem characterEvaluation_apply (m : IntegralCharacter N) (x : ComplexTorus N) :
    characterEvaluation m x = x m :=
  by simp [characterEvaluation, AddChar.toMonoidHomMulEquiv, AddChar.toMonoidHomEquiv]

/-- Evaluation of the zero integral character is the trivial monoid homomorphism. -/
@[simp]
theorem characterEvaluation_zero :
    characterEvaluation (0 : IntegralCharacter N) = 1 := by
  ext x
  simp only [characterEvaluation_apply, AddChar.map_zero_eq_one, MonoidHom.one_apply]

/-- Evaluation sends addition of integral characters to multiplication of monoid homomorphisms. -/
@[simp]
theorem characterEvaluation_add (m₁ m₂ : IntegralCharacter N) :
    characterEvaluation (m₁ + m₂) = characterEvaluation m₁ * characterEvaluation m₂ := by
  ext x
  simp only [characterEvaluation_apply, AddChar.map_add_eq_mul, MonoidHom.mul_apply]

/-- Evaluation sends negation of an integral character to inversion of a monoid homomorphism. -/
@[simp]
theorem characterEvaluation_neg (m : IntegralCharacter N) :
    characterEvaluation (-m) = (characterEvaluation m)⁻¹ := by
  ext x
  simp only [characterEvaluation_apply, AddChar.map_neg_eq_inv, MonoidHom.inv_apply]

/-- The map of complex tori induced covariantly by an additive map of lattices. -/
def complexTorusMap (f : N →+ N') : ComplexTorus N →* ComplexTorus N' where
  toFun x := x.compAddMonoidHom (AddMonoidHom.compHom' f)
  map_one' := by
    apply AddChar.ext
    intro m
    rfl
  map_mul' x y := by
    apply AddChar.ext
    intro m
    rfl

/-- The torus map induced by `f` evaluates by pulling the character back along `f`. -/
@[simp]
theorem complexTorusMap_apply (f : N →+ N') (x : ComplexTorus N)
    (m : IntegralCharacter N') :
    (complexTorusMap f x) m =
      characterEvaluation (AddMonoidHom.compHom' f m) x :=
  by simp [complexTorusMap]

/-- The identity lattice map induces the identity map of complex tori. -/
@[simp]
theorem complexTorusMap_id :
    complexTorusMap (AddMonoidHom.id N) = MonoidHom.id (ComplexTorus N) := by
  apply MonoidHom.ext
  intro x
  apply AddChar.ext
  intro m
  rfl

/-- Composition of lattice maps induces composition of the corresponding complex-torus maps. -/
theorem complexTorusMap_comp (g : N' →+ N'') (f : N →+ N') :
    complexTorusMap (g.comp f) = (complexTorusMap g).comp (complexTorusMap f) := by
  apply MonoidHom.ext
  intro x
  apply AddChar.ext
  intro m
  rfl

namespace ComplexTorus

/-- Two complex-torus points agreeing under every integral character are equal. -/
@[ext]
theorem ext {x y : ComplexTorus N}
    (h : ∀ m : IntegralCharacter N, characterEvaluation m x = characterEvaluation m y) : x = y :=
  AddChar.ext x y fun m ↦ by simpa only [characterEvaluation_apply] using h m

end ComplexTorus

/-- Integral characters separate distinct points of the coordinate-free complex torus. -/
theorem exists_characterEvaluation_ne {x y : ComplexTorus N} (h : x ≠ y) :
    ∃ m : IntegralCharacter N, characterEvaluation m x ≠ characterEvaluation m y := by
  simpa only [characterEvaluation_apply] using (DFunLike.ne_iff.mp h)

/-- A free presentation of the character lattice identifies the coordinate-free complex torus
with a product of copies of `ℂˣ`.  The last step is Tau Ceti's `freeAbelianCharEquiv`. -/
noncomputable def complexTorusCoordinates {σ : Type*}
    (e : IntegralCharacter N ≃+ (σ →₀ ℤ)) : ComplexTorus N ≃* (σ → ℂˣ) :=
  AddChar.toMonoidHomMulEquiv.trans
    (e.toMultiplicative.monoidHomCongrLeft (N := ℂˣ) |>.trans freeAbelianCharEquiv)

/-- A coordinate supplied by a free presentation is evaluation at the corresponding transported
standard generator of the character lattice. -/
@[simp]
theorem complexTorusCoordinates_apply {σ : Type*} (e : IntegralCharacter N ≃+ (σ →₀ ℤ))
    (x : ComplexTorus N) (i : σ) :
    complexTorusCoordinates e x i = x (e.symm (Finsupp.single i 1)) :=
  by simp [complexTorusCoordinates, AddChar.toMonoidHomMulEquiv]

end TauCeti.Toric
