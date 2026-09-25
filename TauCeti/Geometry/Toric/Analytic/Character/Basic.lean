/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Equiv.TypeTags
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.LinearAlgebra.Dual.Basis
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import TauCeti.Algebra.Group.FreeAbelianCharacter

/-!
# Integral characters on the complex torus

For an additive lattice `N`, its integral character lattice is `N →+ ℤ`.  The
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
* `Module.Basis.integralCharacterRepr`: the free presentation of the character lattice dual to an
  integral basis of `N`.
* `TauCeti.Toric.complexTorusCoordinates`: coordinates supplied by a free presentation of the
  character lattice.
* `TauCeti.Toric.complexTorus_apply_eq_prod_zpow`: the Laurent-monomial formula for evaluation of
  a character in those coordinates.
* `Module.Basis.complexTorusCoordinates`: coordinates supplied by an integral basis of the
  lattice, through its dual basis.

## References

* D. Cox, J. Little and H. Schenck, *Toric Varieties*, §1.1.
* W. Fulton, *Introduction to Toric Varieties*, §1.1.
-/

public section

namespace TauCeti.Toric

open Multiplicative

variable {N N' N'' : Type*}
  [AddCommGroup N] [AddCommGroup N'] [AddCommGroup N'']

/-- The group of integral characters of an additive commutative group `N`. -/
abbrev IntegralCharacter (N : Type*) [AddCommGroup N] :=
  N →+ ℤ

/-- The group of complex unit-valued characters on `N →+ ℤ`.

For a finite free `ℤ`-module `N`, this is its coordinate-free complex torus.
`AddChar` is the additive-domain form of the equivalent Mathlib carrier
`Multiplicative (N →+ ℤ) →* ℂˣ`; using it makes evaluation and pullback of characters direct. -/
abbrev ComplexTorus (N : Type*) [AddCommGroup N] :=
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
@[simp]
theorem complexTorusMap_comp (g : N' →+ N'') (f : N →+ N') :
    complexTorusMap (g.comp f) = (complexTorusMap g).comp (complexTorusMap f) := by
  apply MonoidHom.ext
  intro x
  apply AddChar.ext
  intro m
  rfl

/-- Integral characters separate distinct points of the coordinate-free complex torus. -/
theorem exists_characterEvaluation_ne {x y : ComplexTorus N} (h : x ≠ y) :
    ∃ m : IntegralCharacter N, characterEvaluation m x ≠ characterEvaluation m y := by
  simpa only [characterEvaluation_apply] using (DFunLike.ne_iff.mp h)

/-- The free presentation of the character lattice dual to an integral basis `B` of `N`: an
integral character corresponds to the family of its values on the basis vectors. -/
noncomputable def _root_.Module.Basis.integralCharacterRepr {ι : Type*} [Finite ι]
    (B : Module.Basis ι ℤ N) : IntegralCharacter N ≃+ (ι →₀ ℤ) := by
  classical
  exact ((addMonoidHomLequivInt ℤ).trans B.dualBasis.repr).toAddEquiv

/-- The coordinate of an integral character at a basis index is its value on that basis vector. -/
@[simp]
theorem _root_.Module.Basis.integralCharacterRepr_apply {ι : Type*} [Finite ι]
    (B : Module.Basis ι ℤ N) (m : IntegralCharacter N) (i : ι) :
    B.integralCharacterRepr m i = m (B i) := by
  classical
  simp [Module.Basis.integralCharacterRepr]

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

/-- The torus point with prescribed coordinates evaluates an integral character to the Laurent
monomial in those coordinates whose exponents are the coordinates of the character. -/
@[simp]
theorem complexTorusCoordinates_symm_apply {σ : Type*} (e : IntegralCharacter N ≃+ (σ →₀ ℤ))
    (c : σ → ℂˣ) (m : IntegralCharacter N) :
    (complexTorusCoordinates e).symm c m = (e m).prod fun i n ↦ c i ^ n := by
  simp [complexTorusCoordinates, AddChar.toMonoidHomMulEquiv]

/-- The Laurent-monomial formula: a torus point evaluates an integral character `m` to the
product of its coordinates, in the presentation `e`, raised to the coordinates of `m`. -/
theorem complexTorus_apply_eq_prod_zpow {σ : Type*} (e : IntegralCharacter N ≃+ (σ →₀ ℤ))
    (x : ComplexTorus N) (m : IntegralCharacter N) :
    x m = (e m).prod fun i n ↦ complexTorusCoordinates e x i ^ n := by
  conv_lhs => rw [← (complexTorusCoordinates e).symm_apply_apply x]
  exact complexTorusCoordinates_symm_apply e _ m

/-- The Laurent-monomial formula for a finite index type. -/
theorem complexTorus_apply_eq_prod_zpow_of_fintype {σ : Type*} [Fintype σ]
    (e : IntegralCharacter N ≃+ (σ →₀ ℤ)) (x : ComplexTorus N) (m : IntegralCharacter N) :
    x m = ∏ i, complexTorusCoordinates e x i ^ e m i := by
  rw [complexTorus_apply_eq_prod_zpow e, Finsupp.prod_fintype _ _ fun _ ↦ zpow_zero _]

end TauCeti.Toric

namespace Module.Basis

open TauCeti.Toric

variable {N κ : Type*} [AddCommGroup N] [Module.Finite ℤ N]

/-- The coordinates on the coordinate-free complex torus supplied by an integral basis of `N`: a
torus point corresponds to its values on the dual basis characters, the coordinate functionals of
the basis. -/
noncomputable def complexTorusCoordinates (b : Basis κ ℤ N) :
    ComplexTorus N ≃* (κ → ℂˣ) := by
  classical
  letI : Finite κ := Module.Finite.finite_basis b
  exact TauCeti.Toric.complexTorusCoordinates b.integralCharacterRepr

/-- The coordinate of a torus point indexed by a basis vector is its value on the coordinate
functional of that vector. -/
@[simp]
theorem complexTorusCoordinates_apply (b : Basis κ ℤ N)
    (x : ComplexTorus N) (c : κ) :
    b.complexTorusCoordinates x c = x (b.coord c).toAddMonoidHom := by
  classical
  have : Finite κ := Module.Finite.finite_basis b
  rw [complexTorusCoordinates, TauCeti.Toric.complexTorusCoordinates_apply]
  congr 1
  refine (AddEquiv.symm_apply_eq b.integralCharacterRepr).2 ?_
  ext j
  simp [Finsupp.single_apply, eq_comm]

/-- The torus point with prescribed basis coordinates takes the prescribed value on each coordinate
functional. -/
@[simp]
theorem complexTorusCoordinates_symm_apply (b : Basis κ ℤ N)
    (z : κ → ℂˣ) (c : κ) :
    b.complexTorusCoordinates.symm z (b.coord c).toAddMonoidHom = z c := by
  rw [← complexTorusCoordinates_apply, MulEquiv.apply_symm_apply]

end Module.Basis
