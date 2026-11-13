/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.NumberTheory.DirichletCharacter.Bounds
public import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
public import TauCeti.NumberTheory.DirichletCharacter.Basic
public import TauCeti.NumberTheory.MulChar.Basic

/-!
# Quadratic Dirichlet characters under level changes and products, and at a prime level

Being quadratic is preserved by lifting a Dirichlet character to a multiple of its level, and
reflected by it when the target level is nonzero. Together with the fact that a product of
quadratic multiplicative characters is quadratic (`MulChar.IsQuadratic.mul`, in
`TauCeti.NumberTheory.MulChar.Basic`), this shows that the product `χ.mul ψ` of characters of
different levels, taken at their common level, is quadratic.

At a prime level `p`, a nonprincipal quadratic character takes the value `-1` at some unit, which
is then a nonsquare; since the product of two nonsquares is a square, it takes the value `-1` at
every nonsquare, and so it is the Legendre character `quadraticChar (ZMod p)`. For odd `p`, with
values in a nontrivial ring of characteristic other than `2`, the Legendre character is
nonprincipal, so its lift to any nonzero multiple of `p` has conductor `p`. (At `p = 2` the
Legendre character is principal and has conductor `1`.)

A complex Dirichlet character whose values are all real is quadratic, since its values at units
have absolute value one.

## Main results

* `MulChar.IsQuadratic.changeLevel`: lifting a quadratic Dirichlet character to a multiple of its
  level leaves it quadratic.
* `DirichletCharacter.isQuadratic_changeLevel_iff`: at a nonzero target level, a lifted
  character is quadratic exactly when the original character is quadratic.
* `DirichletCharacter.isQuadratic_mul`: the common-level product of two quadratic characters is
  quadratic.
* `DirichletCharacter.primitiveCharacter_sq_eq_one`, `MulChar.IsQuadratic.primitiveCharacter`:
  at a nonzero level, the primitive character of a character of order dividing two, or of a
  quadratic character, is again one.
* `DirichletCharacter.isQuadratic_iff_eq_one_or_eq_quadraticChar`: at a prime level, the quadratic
  characters are the principal one and the Legendre character.
* `DirichletCharacter.conductor_changeLevel_quadraticChar`: for odd `p`, with values in a
  nontrivial ring of characteristic other than `2`, the Legendre character lifted to a nonzero
  multiple of `p` has conductor `p`.
* `DirichletCharacter.isQuadratic_of_forall_im_eq_zero`: a complex Dirichlet character with real
  values is quadratic.

## References

H. L. Montgomery and R. C. Vaughan, *Multiplicative Number Theory I. Classical Theory*,
Cambridge University Press, 2007, §9.3, pp. 295–296.
-/

public section

/-- Lifting a quadratic Dirichlet character to a multiple of its level leaves it quadratic. -/
theorem MulChar.IsQuadratic.changeLevel {R : Type*} [CommRing R]
    {n m : ℕ} {χ : DirichletCharacter R n} (hχ : χ.IsQuadratic) (h : n ∣ m) :
    (DirichletCharacter.changeLevel h χ).IsQuadratic := by
  intro a
  by_cases ha : IsUnit a
  · rw [← ha.unit_spec, DirichletCharacter.changeLevel_eq_cast_of_dvd]
    exact hχ _
  · exact Or.inl (MulChar.map_nonunit _ ha)

namespace DirichletCharacter

/-- Lifting to a nonzero multiple of the level preserves and reflects being quadratic. -/
@[simp]
theorem isQuadratic_changeLevel_iff {R : Type*} [CommRing R]
    {n m : ℕ} [NeZero m] {χ : DirichletCharacter R n} (h : n ∣ m) :
    (changeLevel h χ).IsQuadratic ↔ χ.IsQuadratic := by
  refine ⟨?_, fun hχ ↦ hχ.changeLevel h⟩
  intro hχ a
  by_cases ha : IsUnit a
  · obtain ⟨u, hu⟩ := ZMod.unitsMap_surjective h ha.unit
    have hv := hχ (u : ZMod m)
    rw [changeLevel_eq_cast_of_dvd] at hv
    rw [← ha.unit_spec, ← hu, ZMod.unitsMap_val]
    exact hv
  · exact Or.inl (MulChar.map_nonunit χ ha)

/-- The product of two quadratic characters, taken at the least common multiple of their levels,
is quadratic. -/
theorem isQuadratic_mul {R : Type*} [CommRing R] {n m : ℕ} {χ : DirichletCharacter R n}
    {ψ : DirichletCharacter R m} (hχ : χ.IsQuadratic) (hψ : ψ.IsQuadratic) :
    (χ.mul ψ).IsQuadratic := by
  rw [DirichletCharacter.mul]
  exact (hχ.changeLevel _).mul (hψ.changeLevel _)

/-- The primitive character of a character of order dividing two at a nonzero level has order
dividing two. -/
theorem primitiveCharacter_sq_eq_one {R : Type*} [CommMonoidWithZero R] {N : ℕ} [NeZero N]
    {χ : DirichletCharacter R N} (hχ : χ ^ 2 = 1) : χ.primitiveCharacter ^ 2 = 1 :=
  primitiveCharacter_pow_eq_one hχ

/-- The primitive character of a quadratic Dirichlet character at a nonzero level is quadratic:
its values at units are values of `χ` at units lifting them. -/
theorem _root_.MulChar.IsQuadratic.primitiveCharacter {R : Type*} [CommRing R] {N : ℕ}
    [NeZero N] {χ : DirichletCharacter R N} (hχ : χ.IsQuadratic) :
    χ.primitiveCharacter.IsQuadratic := by
  rw [← isQuadratic_changeLevel_iff χ.conductor_dvd_level, changeLevel_primitiveCharacter]
  exact hχ

section Prime

variable {R : Type*} [CommRing R] {p : ℕ} [Fact p.Prime]

/-- **The quadratic characters at a prime level.** A quadratic Dirichlet character modulo a prime
`p` is either principal or the Legendre character `quadraticChar (ZMod p)`, with values pushed to
`R`. -/
theorem isQuadratic_iff_eq_one_or_eq_quadraticChar (ψ : DirichletCharacter R p) :
    ψ.IsQuadratic ↔
      ψ = 1 ∨ ψ = (quadraticChar (ZMod p)).ringHomComp (Int.castRingHom R) := by
  refine ⟨fun hψ ↦ or_iff_not_imp_left.mpr fun h1 ↦ ?_, ?_⟩
  · -- `ψ` is `1` at every square unit.
    have hsq (x : (ZMod p)ˣ) (hx : IsSquare (x : ZMod p)) : ψ x = 1 := by
      obtain ⟨s, hs⟩ := hx
      have hs' : IsUnit s := isUnit_of_mul_isUnit_left (hs ▸ x.isUnit)
      rw [hs, map_mul, ← sq, ← MulChar.pow_apply' ψ two_ne_zero, hψ.sq_eq_one,
        MulChar.one_apply hs']
    obtain ⟨u, hu⟩ := MulChar.ne_one_iff.mp h1
    have hu' : ψ u = -1 := by
      rcases hψ u with h | h | h
      · have : Subsingleton R := subsingleton_of_zero_eq_one
          (isUnit_zero_iff.mp (h ▸ u.isUnit.map ψ))
        exact absurd (Subsingleton.elim _ _) hu
      · exact absurd h hu
      · exact h
    have hun : ¬IsSquare (u : ZMod p) := fun h ↦ hu (hsq u h)
    refine MulChar.ext fun x ↦ ?_
    rw [MulChar.ringHomComp_apply, eq_intCast]
    by_cases hx : IsSquare (x : ZMod p)
    · rw [hsq x hx, (quadraticChar_one_iff_isSquare x.ne_zero).mpr hx, Int.cast_one]
    · rw [quadraticChar_neg_one_iff_not_isSquare.mpr hx]
      have hxu : ψ ↑(x * u) = 1 := by
        refine hsq _ ((quadraticChar_one_iff_isSquare (x * u).ne_zero).mp ?_)
        rw [Units.val_mul, map_mul, quadraticChar_neg_one_iff_not_isSquare.mpr hx,
          quadraticChar_neg_one_iff_not_isSquare.mpr hun]
        norm_num
      rw [Units.val_mul, map_mul, hu'] at hxu
      push_cast
      linear_combination -hxu
  · rintro (rfl | rfl)
    · exact MulChar.isQuadratic_one
    · exact quadraticChar_isQuadratic _ |>.comp _

/-- For an odd prime `p`, the Legendre character with values in a nontrivial ring `R` of
characteristic other than `2` is not principal. -/
theorem quadraticChar_ringHomComp_ne_one [Nontrivial R] (hR : ringChar R ≠ 2) (hp2 : p ≠ 2) :
    (quadraticChar (ZMod p)).ringHomComp (Int.castRingHom R) ≠ 1 := by
  obtain ⟨a, ha⟩ := quadraticChar_exists_neg_one' (F := ZMod p) (by rwa [ZMod.ringChar_zmod_n])
  refine MulChar.ne_one_iff.mpr ⟨a, ?_⟩
  rw [MulChar.ringHomComp_apply, ha, map_neg, map_one]
  exact mt neg_one_eq_one_iff.mp hR

/-- For an odd prime `p`, the Legendre character with values in a nontrivial ring `R` of
characteristic other than `2`, lifted to any nonzero multiple `N` of `p`, has conductor `p`. -/
theorem conductor_changeLevel_quadraticChar [Nontrivial R] (hR : ringChar R ≠ 2) (hp2 : p ≠ 2)
    {N : ℕ} [NeZero N] (h : p ∣ N) :
    (changeLevel h ((quadraticChar (ZMod p)).ringHomComp (Int.castRingHom R))).conductor = p := by
  have hp : p.Prime := Fact.out
  have : NeZero p := ⟨hp.ne_zero⟩
  rw [conductor_changeLevel]
  refine ((Nat.dvd_prime hp).mp (conductor_dvd_level _)).resolve_left fun h1 ↦ ?_
  exact quadraticChar_ringHomComp_ne_one hR hp2 (eq_one_iff_conductor_eq_one.mpr h1)

end Prime

/-- **A real character is quadratic.** A Dirichlet character with complex values whose values are
all real is quadratic: its values at units have absolute value one. -/
theorem isQuadratic_of_forall_im_eq_zero {N : ℕ} (χ : DirichletCharacter ℂ N)
    (hχ : ∀ a, (χ a).im = 0) : χ.IsQuadratic := by
  intro a
  by_cases ha : IsUnit a
  · have hnorm : |(χ a).re| = 1 := by
      rw [Complex.abs_re_eq_norm.mpr (hχ a), ← ha.unit_spec]
      exact χ.unit_norm_eq_one ha.unit
    have hre : χ a = ((χ a).re : ℂ) := Complex.ext rfl (by simp [hχ a])
    rcases abs_eq (zero_le_one' ℝ) |>.mp hnorm with h | h
    · exact Or.inr (Or.inl (by rw [hre, h, Complex.ofReal_one]))
    · exact Or.inr (Or.inr (by rw [hre, h, Complex.ofReal_neg, Complex.ofReal_one]))
  · exact Or.inl (MulChar.map_nonunit χ ha)

end DirichletCharacter
