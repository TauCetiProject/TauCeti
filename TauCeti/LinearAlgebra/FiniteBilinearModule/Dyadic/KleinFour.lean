/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.SpecificGroups.KleinFour
public import TauCeti.LinearAlgebra.FiniteBilinearModule.Dyadic.RankTwo.Basic
public import TauCeti.LinearAlgebra.FiniteBilinearModule.KleinFour

/-!
# Alternating quadratic modules on the Klein four-group

A nondegenerate finite quadratic module on a Klein four-group whose polar pairing is alternating
is isometric to one of the two rank-two dyadic generators of exponent two:
`u¹ = u⁽²⁾(2)` or `v¹ = v⁽²⁾(2)`.  This is the first rank-two case in the
dyadic generator decomposition.  It is also the point at which the two rank-two families become
necessary: neither alternating form has a nondegenerate cyclic subgroup.

Choose any two distinct nonzero generators `x, y`.  Nondegeneracy and alternation force
`b(x, y) = 1/2`.  Each of `q(x)` and `q(y)` is either `0` or `1/2`.  If both are `1/2`, all three
nonzero vectors have value `1/2`, giving `v¹`.  Otherwise a shear of the chosen basis makes both
basis vectors isotropic, giving `u¹`.

## Main declaration

* `TauCeti.FiniteQuadraticModule.nonempty_isometry_dyadicU_or_dyadicV_of_isAddKleinFour`:
  classification of the nondegenerate alternating quadratic modules on a Klein four-group.

## References

* V. V. Nikulin, *Integral symmetric bilinear forms and some of their applications*,
  Proposition 1.8.1.
* C. T. C. Wall, *Quadratic forms on finite groups, and related topics*, Topology 2 (1963),
  281–298.
-/

public section

open AddSubgroup

namespace TauCeti.FiniteQuadraticModule

private theorem one_div_two_add_self :
    ((1 / 2 : ℚ) : AddCircle (1 : ℚ)) + ((1 / 2 : ℚ) : AddCircle (1 : ℚ)) = 0 := by
  rw [← AddCircle.coe_add, AddCircle.coe_eq_zero_iff]
  exact ⟨1, by norm_num⟩

private theorem toRatAddCircle_two_one :
    ZMod.toRatAddCircle 2 (1 : ZMod 2) = ((1 / 2 : ℚ) : AddCircle (1 : ℚ)) := by
  simpa using ZMod.toRatAddCircle_natCast 2 1

private theorem one_add_one_zmod_two : (1 : ZMod 2) + 1 = 0 := by
  -- Writing the sum as a natural cast exposes the defining modulus of `ZMod 2`.
  change ((2 : ℕ) : ZMod 2) = 0
  exact ZMod.natCast_self 2

private theorem two_eq_zero_zmod_two : (2 : ZMod 2) = 0 := by
  -- The numeral is elaborated in `ZMod 2`; restating it as a natural cast exposes the modulus.
  change ((2 : ℕ) : ZMod 2) = 0
  exact ZMod.natCast_self 2

/-- The shear `(a, b) ↦ (a + b, b)` of the Klein four-group. -/
private def shearFirst : ZMod 2 × ZMod 2 ≃+ ZMod 2 × ZMod 2 where
  toFun x := (x.1 + x.2, x.2)
  invFun x := (x.1 + x.2, x.2)
  left_inv x := by
    ext <;> dsimp
    rw [add_assoc, ← two_mul, two_eq_zero_zmod_two, zero_mul, add_zero]
  right_inv x := by
    ext <;> dsimp
    rw [add_assoc, ← two_mul, two_eq_zero_zmod_two, zero_mul, add_zero]
  map_add' x y := by
    ext
    all_goals dsimp
    all_goals ring

/-- The shear `(a, b) ↦ (a, a + b)` of the Klein four-group. -/
private def shearSecond : ZMod 2 × ZMod 2 ≃+ ZMod 2 × ZMod 2 where
  toFun x := (x.1, x.1 + x.2)
  invFun x := (x.1, x.1 + x.2)
  left_inv x := by
    ext <;> dsimp
    rw [← add_assoc, ← two_mul, two_eq_zero_zmod_two, zero_mul, zero_add]
  right_inv x := by
    ext <;> dsimp
    rw [← add_assoc, ← two_mul, two_eq_zero_zmod_two, zero_mul, zero_add]
  map_add' x y := by
    ext
    all_goals dsimp
    all_goals ring

/-- An additive equivalence matching the three nonzero values of `u⁽²⁾(2)` gives an
isometry from `u⁽²⁾(2)`. -/
private noncomputable def dyadicUOneIsometryOfGenerators (A : FiniteQuadraticModule)
    (e : ZMod 2 × ZMod 2 ≃+ A) (h₁ : A.quadratic (e (1, 0)) = 0)
    (h₂ : A.quadratic (e (0, 1)) = 0)
    (h₃ : A.quadratic (e (1, 1)) = ((1 / 2 : ℚ) : AddCircle (1 : ℚ))) :
    Isometry (dyadicU 1) A := by
  have hu₁₀ : (dyadicU 1).quadratic (1, 0) = 0 := by simp
  have hu₀₁ : (dyadicU 1).quadratic (0, 1) = 0 := by simp
  have hu₁₁ : (dyadicU 1).quadratic (1, 1) =
      ((1 / 2 : ℚ) : AddCircle (1 : ℚ)) := by
    norm_num [dyadicU_quadratic]
    exact toRatAddCircle_two_one
  unfold dyadicU at hu₁₀ hu₀₁ hu₁₁ ⊢
  refine kleinFourIsometryOfGenerators _ _ e ?_ ?_ ?_
  · exact h₁.trans hu₁₀.symm
  · exact h₂.trans hu₀₁.symm
  · exact h₃.trans hu₁₁.symm

/-- An additive equivalence taking every nonzero vector to quadratic value `1/2` gives an
isometry from `v⁽²⁾(2)`. -/
private noncomputable def dyadicVOneIsometryOfGenerators (A : FiniteQuadraticModule)
    (e : ZMod 2 × ZMod 2 ≃+ A)
    (h₁ : A.quadratic (e (1, 0)) = ((1 / 2 : ℚ) : AddCircle (1 : ℚ)))
    (h₂ : A.quadratic (e (0, 1)) = ((1 / 2 : ℚ) : AddCircle (1 : ℚ)))
    (h₃ : A.quadratic (e (1, 1)) = ((1 / 2 : ℚ) : AddCircle (1 : ℚ))) :
    Isometry (dyadicV 1) A := by
  have hv₁₀ : (dyadicV 1).quadratic (1, 0) =
      ((1 / 2 : ℚ) : AddCircle (1 : ℚ)) := by
    norm_num [dyadicV_quadratic]
    exact toRatAddCircle_two_one
  have hv₀₁ : (dyadicV 1).quadratic (0, 1) =
      ((1 / 2 : ℚ) : AddCircle (1 : ℚ)) := by
    norm_num [dyadicV_quadratic]
    exact toRatAddCircle_two_one
  have hv₁₁ : (dyadicV 1).quadratic (1, 1) =
      ((1 / 2 : ℚ) : AddCircle (1 : ℚ)) := by
    norm_num [dyadicV_quadratic]
    -- Reduction modulo two identifies the remaining coefficient `3` with `1`.
    rw [show (3 : ZMod 2) = 1 by decide]
    exact toRatAddCircle_two_one
  unfold dyadicV at hv₁₀ hv₀₁ hv₁₁ ⊢
  refine kleinFourIsometryOfGenerators _ _ e ?_ ?_ ?_
  · exact h₁.trans hv₁₀.symm
  · exact h₂.trans hv₀₁.symm
  · exact h₃.trans hv₁₁.symm

/-- **The alternating quadratic modules on the Klein four-group are `u¹` and `v¹`.**

If `A` is nondegenerate, has underlying additive group a Klein four-group, and satisfies
`b(x, x) = 0` for every `x`, then `A` is isometric to `u⁽²⁾(2)` or to `v⁽²⁾(2)`. -/
theorem nonempty_isometry_dyadicU_or_dyadicV_of_isAddKleinFour
    (A : FiniteQuadraticModule) [IsAddKleinFour A] (hA : A.IsNondegenerate)
    (hAlt : ∀ x, A.toFiniteBilinearModule.pairing x x = 0) :
    Nonempty (Isometry (dyadicU 1) A) ∨ Nonempty (Isometry (dyadicV 1) A) := by
  obtain ⟨e : ZMod 2 × ZMod 2 ≃+ A⟩ :=
    IsAddKleinFour.nonempty_addEquiv (G₁ := ZMod 2 × ZMod 2) (G₂ := A)
  let x := e (1, 0)
  let y := e (0, 1)
  have he11 : e (1, 1) = x + y := by
    simpa [x, y] using e.map_add (1, 0) (0, 1)
  have hxne : x ≠ 0 := by
    rw [Ne, ← map_zero e, e.injective.eq_iff]
    decide
  have hxy : A.toFiniteBilinearModule.pairing x y ≠ 0 := by
    intro hxy
    -- If the cross term vanished, `x` would pair trivially with all four elements.
    have hxpair : A.toFiniteBilinearModule.pairing x = 0 := by
      apply AddMonoidHom.ext
      intro a
      obtain ⟨⟨c, d⟩, rfl⟩ := e.surjective a
      -- Expose evaluation at the four coordinate vectors of the Klein four-group.
      change A.toFiniteBilinearModule.pairing x (e (c, d)) =
        (0 : AddCircle (1 : ℚ))
      rcases (by decide : ∀ t : ZMod 2, t = 0 ∨ t = 1) c with rfl | rfl <;>
        rcases (by decide : ∀ t : ZMod 2, t = 0 ∨ t = 1) d with rfl | rfl
      · rw [show e (0, 0) = 0 by simp, map_zero]
      · simpa [y] using hxy
      · simpa [x] using hAlt x
      · rw [he11, A.toFiniteBilinearModule.pairing_add_right, hAlt x, hxy, add_zero]
    exact hxne (FiniteBilinearModule.IsNondegenerate.injective _ hA
      (hxpair.trans (map_zero _).symm))
  have htwoPair : (2 : ℤ) • A.toFiniteBilinearModule.pairing x y = 0 := by
    rw [← map_zsmul]
    have hy2 : (2 : ℤ) • y = 0 := by
      simpa only [ofNat_zsmul, IsAddKleinFour.exponent_two] using
        AddMonoid.exponent_nsmul_eq_zero y
    rw [hy2, map_zero]
  have hpair : A.toFiniteBilinearModule.pairing x y =
      ((1 / 2 : ℚ) : AddCircle (1 : ℚ)) :=
    (AddCircle.eq_zero_or_eq_coe_period_div_two (1 : ℚ) two_ne_zero htwoPair).resolve_left hxy
  have htwoQuad (a : A) : (2 : ℤ) • A.quadratic a = 0 := by
    have hpolar : (2 : ℕ) • A.quadratic a = 0 := by
      rw [← QuadraticMap.polar_self, A.polar_eq_pairing, hAlt]
    simpa only [ofNat_zsmul] using hpolar
  have hqadd : A.quadratic (x + y) =
      A.quadratic x + A.quadratic y + ((1 / 2 : ℚ) : AddCircle (1 : ℚ)) := by
    rw [QuadraticMap.map_add A.quadratic x y, A.polar_eq_pairing, hpair]
  rcases AddCircle.eq_zero_or_eq_coe_period_div_two (1 : ℚ) two_ne_zero (htwoQuad x)
      with hx | hx <;>
    rcases AddCircle.eq_zero_or_eq_coe_period_div_two (1 : ℚ) two_ne_zero (htwoQuad y)
      with hy | hy
  -- The four cases are the two possible quadratic values on each chosen generator.
  · left
    refine ⟨dyadicUOneIsometryOfGenerators A e (by simpa [x] using hx)
      (by simpa [y] using hy) ?_⟩
    rw [he11, hqadd, hx, hy, zero_add, zero_add]
  · left
    let e' := shearFirst.trans e
    have he'01 : e' (0, 1) = x + y := by
      simpa [e', shearFirst] using he11
    refine ⟨dyadicUOneIsometryOfGenerators A e' ?_ ?_ ?_⟩
    · simpa [e', shearFirst, x] using hx
    · rw [he'01, hqadd, hx, hy, zero_add, one_div_two_add_self]
    · simpa [e', shearFirst, one_add_one_zmod_two, y] using hy
  · left
    let e' := shearSecond.trans e
    have he'10 : e' (1, 0) = x + y := by
      simpa [e', shearSecond] using he11
    refine ⟨dyadicUOneIsometryOfGenerators A e' ?_ ?_ ?_⟩
    · rw [he'10, hqadd, hx, hy, add_zero, one_div_two_add_self]
    · simpa [e', shearSecond, y] using hy
    · simpa [e', shearSecond, one_add_one_zmod_two, x] using hx
  · right
    refine ⟨dyadicVOneIsometryOfGenerators A e (by simpa [x] using hx)
      (by simpa [y] using hy) ?_⟩
    rw [he11, hqadd, hx, hy, one_div_two_add_self, zero_add]

end TauCeti.FiniteQuadraticModule
