/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.QuadraticAlgebra.Discriminant
public import TauCeti.FieldTheory.SquareClassGroup.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-!
# Isomorphisms between the models `R(√d)`

For a commutative ring `R` and a unit `u` with `d = u² e`, rescaling the generator gives an
explicit `R`-algebra isomorphism `QuadraticAlgebra.smulOmegaEquiv u h` from
`QuadraticAlgebra R d 0` to `QuadraticAlgebra R e 0`, sending `ω` to `u • ω`; its inverse sends
`ω` to `u⁻¹ • ω`. These isomorphisms are closed under inverse and composition. When `2` is
regular in `R` every isomorphism between the two models is of this form, because an isomorphism
preserves traces and norms (`QuadraticAlgebra.trace_algHom_omega`,
`QuadraticAlgebra.norm_algHom_omega`). Over a field of characteristic other than `2` this
recovers the classification of the models `K(√d)`, for nonzero `d`, by the class of `d` in the
square-class group `Kˣ ⧸ (Kˣ)²`.

The isomorphisms are the specialisation of Mathlib's change of generator
`QuadraticAlgebra.changeGeneratorEquiv` to `ω ↦ u • ω`. The square-class criterion is the
`b = 0` form of Mathlib's classification of quadratic algebras by their discriminant modulo unit
squares, `QuadraticAlgebra.nonempty_algEquiv_iff_of_invertible_two`, read in the square-class
group; its squarefree-integer form over `ℚ` is
`QuadraticAlgebra.nonempty_algEquiv_iff_of_squarefree`.

## Main definitions and results

* `QuadraticAlgebra.smulOmegaEquiv`: the isomorphism `R(√d) ≃ₐ[R] R(√e)`, `ω ↦ u • ω`, for
  `d = u² e`, with `smulOmegaEquiv_omega` and `smulOmegaEquiv_symm_omega` giving its values on
  the generator in both directions.
* `QuadraticAlgebra.smulOmegaEquiv_symm`, `QuadraticAlgebra.smulOmegaEquiv_trans`,
  `QuadraticAlgebra.smulOmegaEquiv_one`: inverse, composition and identity.
* `QuadraticAlgebra.exists_eq_smulOmegaEquiv`: if `2` is regular, every isomorphism
  `R(√d) ≃ₐ[R] R(√e)` is `smulOmegaEquiv u h` for the unit `u = (f ω).im`.
* `QuadraticAlgebra.nonempty_algEquiv_iff_exists_eq_sq_mul`: if `2` is regular,
  `R(√d) ≃ₐ[R] R(√e)` exactly when `d = u² e` for a unit `u`.
* `QuadraticAlgebra.nonempty_algEquiv_iff_squareClass_eq`: over a field with `2 ≠ 0`, for
  nonzero `d` and `e`, `K(√d) ≃ₐ[K] K(√e)` exactly when `d` and `e` have the same square class.
-/

public section

namespace QuadraticAlgebra

section CommRing

variable {R : Type*} [CommRing R] {c d e : R}

/-- **Rescaling the generator.** For a unit `u` with `d = u² e`, the `R`-algebra isomorphism
`QuadraticAlgebra R d 0 ≃ₐ[R] QuadraticAlgebra R e 0` sending `ω` to `u • ω`, so that
`x + yω ↦ x + (u y)ω`. -/
def smulOmegaEquiv (u : Rˣ) (h : d = u ^ 2 * e) :
    QuadraticAlgebra R d 0 ≃ₐ[R] QuadraticAlgebra R e 0 :=
  changeGeneratorEquiv e 0 u 0 (by rw [h]; ring) (by ring)

@[simp]
theorem smulOmegaEquiv_apply_re (u : Rˣ) (h : d = u ^ 2 * e) (z : QuadraticAlgebra R d 0) :
    (smulOmegaEquiv u h z).re = z.re := by
  simp [smulOmegaEquiv]

@[simp]
theorem smulOmegaEquiv_apply_im (u : Rˣ) (h : d = u ^ 2 * e) (z : QuadraticAlgebra R d 0) :
    (smulOmegaEquiv u h z).im = u * z.im := by
  simp [smulOmegaEquiv, mul_comm]

/-- `smulOmegaEquiv u h` sends the generator `ω` to `u • ω`. -/
@[simp]
theorem smulOmegaEquiv_omega (u : Rˣ) (h : d = u ^ 2 * e) :
    smulOmegaEquiv u h ω = (u : R) • ω := by
  ext <;> simp

@[simp]
theorem smulOmegaEquiv_symm_apply_re (u : Rˣ) (h : d = u ^ 2 * e) (z : QuadraticAlgebra R e 0) :
    ((smulOmegaEquiv u h).symm z).re = z.re := by
  simpa using (smulOmegaEquiv_apply_re u h ((smulOmegaEquiv u h).symm z)).symm

@[simp]
theorem smulOmegaEquiv_symm_apply_im (u : Rˣ) (h : d = u ^ 2 * e) (z : QuadraticAlgebra R e 0) :
    ((smulOmegaEquiv u h).symm z).im = (u⁻¹ : Rˣ) * z.im := by
  have := smulOmegaEquiv_apply_im u h ((smulOmegaEquiv u h).symm z)
  rw [AlgEquiv.apply_symm_apply] at this
  rw [this, Units.inv_mul_cancel_left]

/-- The inverse of `smulOmegaEquiv u h` sends the generator `ω` to `u⁻¹ • ω`. -/
@[simp]
theorem smulOmegaEquiv_symm_omega (u : Rˣ) (h : d = u ^ 2 * e) :
    (smulOmegaEquiv u h).symm ω = ((u⁻¹ : Rˣ) : R) • ω := by
  ext <;> simp

/-- The inverse of rescaling the generator by `u` is rescaling it by `u⁻¹`. -/
theorem smulOmegaEquiv_symm (u : Rˣ) (h : d = u ^ 2 * e) :
    (smulOmegaEquiv u h).symm =
      smulOmegaEquiv u⁻¹ (by rw [h, ← mul_assoc, ← mul_pow, Units.inv_mul, one_pow, one_mul]) :=
  AlgEquiv.ext fun z => by ext <;> simp

/-- Rescaling the generator by `u` and then by `v` is rescaling it by `u * v`. -/
@[simp]
theorem smulOmegaEquiv_trans (u v : Rˣ) (h : d = u ^ 2 * e) (h' : e = v ^ 2 * c) :
    (smulOmegaEquiv u h).trans (smulOmegaEquiv v h') =
      smulOmegaEquiv (u * v) (by rw [h, h', Units.val_mul]; ring) :=
  AlgEquiv.ext fun z => by
    ext
    · simp
    · simp only [AlgEquiv.trans_apply, smulOmegaEquiv_apply_im, Units.val_mul]
      ring

/-- Rescaling the generator by `1` is the identity. -/
@[simp]
theorem smulOmegaEquiv_one (h : d = (1 : Rˣ) ^ 2 * d) :
    smulOmegaEquiv (1 : Rˣ) h = AlgEquiv.refl :=
  AlgEquiv.ext fun z => by ext <;> simp

/-- **Every isomorphism of the models rescales the generator.** If `2` is regular in `R`, every
`R`-algebra isomorphism `f : QuadraticAlgebra R d 0 ≃ₐ[R] QuadraticAlgebra R e 0` is
`smulOmegaEquiv u h` for the unit `u = (f ω).im`: the image of `ω` has trace `0` and norm `-d`,
so it is `u • ω` with `d = u² e`. -/
theorem exists_eq_smulOmegaEquiv (h2 : IsRegular (2 : R))
    (f : QuadraticAlgebra R d 0 ≃ₐ[R] QuadraticAlgebra R e 0) :
    ∃ (u : Rˣ) (h : d = u ^ 2 * e), (u : R) = (f ω).im ∧ f = smulOmegaEquiv u h := by
  set u := (isUnit_im_omega_of_algEquiv f).unit
  have hu : (u : R) = (f ω).im := IsUnit.unit_spec _
  have htr := trace_algHom_omega f.toAlgHom f.injective
  have hnm := norm_algHom_omega f.toAlgHom f.injective
  rw [AlgEquiv.toAlgHom_apply, trace_def] at htr
  rw [AlgEquiv.toAlgHom_apply, norm_def] at hnm
  have hre : (f ω).re = 0 := h2.left (by simpa using htr)
  have h : d = u ^ 2 * e := by
    rw [hu]
    linear_combination hnm - (f ω).re * hre
  refine ⟨u, h, hu, AlgEquiv.coe_toAlgHom_injective (algHom_ext ?_)⟩
  ext <;> simp [hre, hu]

/-- **Isomorphism of the models up to unit squares.** If `2` is regular in `R`, the models
`QuadraticAlgebra R d 0` and `QuadraticAlgebra R e 0` are isomorphic exactly when `d = u² e` for a
unit `u`. -/
theorem nonempty_algEquiv_iff_exists_eq_sq_mul (h2 : IsRegular (2 : R)) :
    Nonempty (QuadraticAlgebra R d 0 ≃ₐ[R] QuadraticAlgebra R e 0) ↔
      ∃ u : Rˣ, d = u ^ 2 * e :=
  ⟨fun ⟨f⟩ => (exists_eq_smulOmegaEquiv h2 f).imp fun _ ⟨h, _⟩ => h,
    fun ⟨u, h⟩ => ⟨smulOmegaEquiv u h⟩⟩

end CommRing

section Field

open TauCeti

variable {K : Type*} [Field K] [NeZero (2 : K)] {d e : K}

/-- **The square-class classification of the models.** Over a field with `2 ≠ 0`, for nonzero
`d` and `e`, the models `QuadraticAlgebra K d 0` and `QuadraticAlgebra K e 0` of `K(√d)` and
`K(√e)` are isomorphic exactly when `d` and `e` have the same class in `Kˣ ⧸ (Kˣ)²`. -/
theorem nonempty_algEquiv_iff_squareClass_eq (hd : d ≠ 0) (he : e ≠ 0) :
    Nonempty (QuadraticAlgebra K d 0 ≃ₐ[K] QuadraticAlgebra K e 0) ↔
      squareClass (Units.mk0 d hd) = squareClass (Units.mk0 e he) := by
  rw [nonempty_algEquiv_iff_exists_eq_sq_mul (.of_ne_zero two_ne_zero),
    squareClass_eq_iff_isSquare_mul]
  constructor
  · rintro ⟨u, rfl⟩
    exact ⟨u * Units.mk0 e he, Units.ext (by simp; ring)⟩
  · rintro ⟨r, hr⟩
    refine ⟨r * (Units.mk0 e he)⁻¹, ?_⟩
    have hr' : d * e = r * r := by simpa using congrArg Units.val hr
    rw [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mk0]
    field_simp
    linear_combination hr'
end Field

end QuadraticAlgebra
