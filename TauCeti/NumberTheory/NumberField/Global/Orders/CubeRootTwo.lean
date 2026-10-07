/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Global.Orders.IdealClassMonoid
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Tactic.LinearCombination
import TauCeti.FieldTheory.GaloisGroups.Cubic

/-!
# A proper noninvertible ideal in a cubic order

Every invertible fractional ideal of an order is proper, but the converse fails for orders that
are not Gorenstein. This file verifies the standard counterexample. Let `K = ℚ(α)` with `α³ = 2`,
let `O = ℤ + 2ℤα + 2ℤα²`, and let `A = 8ℤ + 2ℤα + 2ℤα²`. Then:

* `O` is an order of `K`;
* `A` is an ideal of `O` whose multiplier ring is exactly `O`, so `A` is proper;
* `A` is not invertible: every element `b` with `b • A ⊆ O` has coordinates in `ℤ × ℤ × ½ℤ` in the
  basis `1, α, α²`, so every product of an element of `A` with such a `b` has even coordinates and
  `A * B` never contains `1`;
* consequently the class of `A` in `IdealClassMonoid O` is not a unit, so `A` is a proper ideal
  that has a class in the ideal class monoid but none in `Pic O`.

The statements are made for an arbitrary number field `K` of degree three over `ℚ` containing an
element `α` with `α³ = 2`; `exists_finrank_eq_three_properFractionalIdeal_not_isUnit` records that
`AdjoinRoot (X³ - 2)` is such a field.

## Main definitions

* `TauCeti.GlobalNumberFields.cubeRootTwoOrder`: the order `ℤ + 2ℤα + 2ℤα²`.
* `TauCeti.GlobalNumberFields.cubeRootTwoIdeal`: the fractional ideal `8ℤ + 2ℤα + 2ℤα²` of
  `cubeRootTwoOrder`.

## Main results

* `TauCeti.GlobalNumberFields.isProperFractionalIdeal_cubeRootTwoIdeal`: the multiplier ring of
  `cubeRootTwoIdeal` is `cubeRootTwoOrder`.
* `TauCeti.GlobalNumberFields.not_isUnit_cubeRootTwoIdeal`: `cubeRootTwoIdeal` is not invertible.
* `TauCeti.GlobalNumberFields.not_isUnit_mkIdealClassMonoid_cubeRootTwoIdeal`: its class in the
  ideal class monoid is not a unit.
* `TauCeti.GlobalNumberFields.exists_finrank_eq_three_properFractionalIdeal_not_isUnit`: some cubic
  number field has an order with a proper fractional ideal whose ideal class is not a unit.

## References

* G. S. Kopp and J. C. Lagarias, *Class Field Theory for Orders of Number Fields*, §2, where this
  order and ideal are the explicit proper noninvertible example.
-/

public section
noncomputable section

open Polynomial FractionalIdeal
open scoped nonZeroDivisors

namespace TauCeti.GlobalNumberFields

variable {K : Type*} [Field K] [NumberField K] {α : K}

/-! ### Coordinates in the basis `1, α, α²` -/

section Coordinates

/-- If `α³ = 2`, then `1, α, α²` are linearly independent over `ℚ`, since `X³ - 2` is irreducible
over `ℚ`. -/
private theorem linearIndependent_pow_of_pow_three_eq_two (hα : α ^ 3 = 2) :
    LinearIndependent ℚ fun i : Fin 3 => α ^ (i : ℕ) := by
  have hmin : minpoly ℚ α = X ^ 3 - 2 :=
    (minpoly.eq_of_irreducible_of_monic irreducible_X_pow_three_sub_two
      (by rw [map_sub, map_pow, aeval_X, map_ofNat, hα, sub_self]) (by monicity!)).symm
  have hdeg : (minpoly ℚ α).natDegree = 3 := by
    rw [hmin]
    compute_degree!
  have h := linearIndependent_pow (K := ℚ) α
  rwa [hdeg] at h

/-- Rational coordinates in the basis `1, α, α²` are unique. -/
private theorem coords_eq_of_pow_three_eq_two (hα : α ^ 3 = 2) {a b c a' b' c' : ℚ}
    (h : (a : K) + b * α + c * α ^ 2 = a' + b' * α + c' * α ^ 2) :
    a = a' ∧ b = b' ∧ c = c' := by
  have h0 := Fintype.linearIndependent_iff.mp (linearIndependent_pow_of_pow_three_eq_two hα)
    ![a - a', b - b', c - c'] (by
      simp only [Fin.sum_univ_three, Rat.smul_def, Fin.val_zero, Fin.val_one, Fin.val_two,
        pow_zero, pow_one]
      push_cast
      linear_combination h)
  refine ⟨?_, ?_, ?_⟩
  · simpa [sub_eq_zero] using h0 0
  · simpa [sub_eq_zero] using h0 1
  · simpa [sub_eq_zero] using h0 2

/-- In a cubic field containing `α` with `α³ = 2`, every element has rational coordinates in the
basis `1, α, α²`. -/
private theorem exists_coords_of_pow_three_eq_two (hα : α ^ 3 = 2)
    (hK : Module.finrank ℚ K = 3) (x : K) :
    ∃ a b c : ℚ, x = a + b * α + c * α ^ 2 := by
  have hspan := (linearIndependent_pow_of_pow_three_eq_two hα).span_eq_top_of_card_eq_finrank'
    (by simp [hK])
  obtain ⟨g, hg⟩ := (Submodule.mem_span_range_iff_exists_fun ℚ).mp
    (hspan ▸ Submodule.mem_top : x ∈ Submodule.span ℚ (Set.range fun i : Fin 3 => α ^ (i : ℕ)))
  refine ⟨g 0, g 1, g 2, ?_⟩
  rw [← hg]
  simp [Fin.sum_univ_three, Rat.smul_def]

end Coordinates

/-! ### The order `ℤ + 2ℤα + 2ℤα²` -/

section Order

/-- The `ℤ`-subalgebra `ℤ + 2ℤα + 2ℤα²` of `K`, for `α³ = 2`. -/
private def cubeRootTwoSubalgebra (hα : α ^ 3 = 2) : Subalgebra ℤ K where
  carrier := {x | ∃ a b c : ℤ, x = a + 2 * b * α + 2 * c * α ^ 2}
  mul_mem' := by
    rintro _ _ ⟨a, b, c, rfl⟩ ⟨a', b', c', rfl⟩
    refine ⟨a * a' + 8 * b * c' + 8 * c * b', a * b' + b * a' + 4 * c * c',
      a * c' + 2 * b * b' + c * a', ?_⟩
    push_cast
    linear_combination (4 * b * c' + 4 * c * b' + 4 * c * c' * α) * hα
  add_mem' := by
    rintro _ _ ⟨a, b, c, rfl⟩ ⟨a', b', c', rfl⟩
    exact ⟨a + a', b + b', c + c', by push_cast; ring⟩
  algebraMap_mem' n := ⟨n, 0, 0, by simp⟩

/-- The order `ℤ + 2ℤα + 2ℤα²` in a cubic field containing a cube root `α` of `2`. -/
def cubeRootTwoOrder (hα : α ^ 3 = 2) (hK : Module.finrank ℚ K = 3) : NumberFieldOrder K where
  toSubalgebra := cubeRootTwoSubalgebra hα
  finite := by
    let f : (Fin 3 → ℤ) →ₗ[ℤ] cubeRootTwoSubalgebra hα :=
      { toFun v := ⟨v 0 + 2 * v 1 * α + 2 * v 2 * α ^ 2, v 0, v 1, v 2, rfl⟩
        map_add' v w := Subtype.ext (by simp only [Pi.add_apply]; push_cast; ring)
        map_smul' n v := Subtype.ext (by
          simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply,
            zsmul_eq_mul]
          push_cast
          ring) }
    refine Module.Finite.of_surjective f ?_
    rintro ⟨x, a, b, c, rfl⟩
    exact ⟨![a, b, c], rfl⟩
  spans := by
    refine eq_top_iff.mpr fun x _ => ?_
    obtain ⟨a, b, c, rfl⟩ := exists_coords_of_pow_three_eq_two hα hK x
    have h1 : (1 : K) ∈ (cubeRootTwoSubalgebra hα : Set K) := ⟨1, 0, 0, by simp⟩
    have h2 : 2 * α ∈ (cubeRootTwoSubalgebra hα : Set K) := ⟨0, 1, 0, by simp⟩
    have h3 : 2 * α ^ 2 ∈ (cubeRootTwoSubalgebra hα : Set K) := ⟨0, 0, 1, by simp⟩
    have h := Submodule.add_mem _ (Submodule.add_mem _
      (Submodule.smul_mem _ a (Submodule.subset_span h1))
      (Submodule.smul_mem _ (b / 2) (Submodule.subset_span h2)))
      (Submodule.smul_mem _ (c / 2) (Submodule.subset_span h3))
    convert h using 1
    simp only [Rat.smul_def]
    push_cast
    ring

variable (hα : α ^ 3 = 2) (hK : Module.finrank ℚ K = 3)

/-- Membership in `cubeRootTwoOrder`: the elements `a + 2bα + 2cα²` with `a, b, c ∈ ℤ`. -/
@[simp]
theorem mem_cubeRootTwoOrder {x : K} :
    x ∈ (cubeRootTwoOrder hα hK).toSubalgebra ↔
      ∃ a b c : ℤ, x = a + 2 * b * α + 2 * c * α ^ 2 :=
  Iff.rfl

end Order

/-! ### The ideal `8ℤ + 2ℤα + 2ℤα²` -/

section Ideal

variable (hα : α ^ 3 = 2) (hK : Module.finrank ℚ K = 3)

/-- The `cubeRootTwoOrder`-submodule `8ℤ + 2ℤα + 2ℤα²` of `K`. -/
private def cubeRootTwoSubmodule : Submodule (cubeRootTwoOrder hα hK).toSubalgebra K where
  carrier := {x | ∃ a b c : ℤ, x = 8 * a + 2 * b * α + 2 * c * α ^ 2}
  add_mem' := by
    rintro _ _ ⟨a, b, c, rfl⟩ ⟨a', b', c', rfl⟩
    exact ⟨a + a', b + b', c + c', by push_cast; ring⟩
  zero_mem' := ⟨0, 0, 0, by simp⟩
  smul_mem' := by
    rintro ⟨_, a', b', c', rfl⟩ _ ⟨a, b, c, rfl⟩
    refine ⟨a * a' + c * b' + b * c', a' * b + 8 * a * b' + 4 * c * c',
      a' * c + 2 * b * b' + 8 * a * c', ?_⟩
    rw [Subalgebra.smul_def, smul_eq_mul]
    push_cast
    linear_combination (4 * c * b' + 4 * b * c' + 4 * c * c' * α) * hα

/-- The fractional ideal `8ℤ + 2ℤα + 2ℤα²` of the order `ℤ + 2ℤα + 2ℤα²`. It is contained in the
order, it is proper (`isProperFractionalIdeal_cubeRootTwoIdeal`), and it is not invertible
(`not_isUnit_cubeRootTwoIdeal`). -/
def cubeRootTwoIdeal : FractionalIdeal (cubeRootTwoOrder hα hK).toSubalgebra⁰ K :=
  ⟨cubeRootTwoSubmodule hα hK, 1, Submonoid.one_mem _, by
    rintro _ ⟨a, b, c, rfl⟩
    rw [one_smul]
    exact ⟨⟨8 * a + 2 * b * α + 2 * c * α ^ 2, 8 * a, b, c, by push_cast; ring⟩, rfl⟩⟩

/-- Membership in `cubeRootTwoIdeal`: the elements `8a + 2bα + 2cα²` with `a, b, c ∈ ℤ`. -/
@[simp]
theorem mem_cubeRootTwoIdeal {x : K} :
    x ∈ cubeRootTwoIdeal hα hK ↔ ∃ a b c : ℤ, x = 8 * a + 2 * b * α + 2 * c * α ^ 2 :=
  Iff.rfl

/-- The multiplier ring of `8ℤ + 2ℤα + 2ℤα²` is exactly `ℤ + 2ℤα + 2ℤα²`, so this ideal is a
proper fractional ideal of the order. -/
theorem isProperFractionalIdeal_cubeRootTwoIdeal :
    (cubeRootTwoOrder hα hK).IsProperFractionalIdeal (cubeRootTwoIdeal hα hK) := by
  rw [NumberFieldOrder.isProperFractionalIdeal_iff]
  intro x hx
  obtain ⟨q₀, q₁, q₂, rfl⟩ := exists_coords_of_pow_three_eq_two hα hK x
  -- Multiplying by `2α` forces `q₀, q₁ ∈ ℤ` and `q₂ ∈ 2ℤ`.
  obtain ⟨a, b, c, h⟩ := hx (2 * α) ((mem_cubeRootTwoIdeal hα hK).mpr ⟨0, 1, 0, by simp⟩)
  obtain ⟨ha, hb, _⟩ := coords_eq_of_pow_three_eq_two hα
    (a := 4 * q₂) (b := 2 * q₀) (c := 2 * q₁) (a' := 8 * a) (b' := 2 * b) (c' := 2 * c)
    (by push_cast; linear_combination h - 2 * q₂ * hα)
  -- Multiplying by `2α²` forces `q₁ ∈ 2ℤ`.
  obtain ⟨a', b', c', h'⟩ := hx (2 * α ^ 2) ((mem_cubeRootTwoIdeal hα hK).mpr ⟨0, 0, 1, by simp⟩)
  obtain ⟨ha', -, -⟩ := coords_eq_of_pow_three_eq_two hα
    (a := 4 * q₁) (b := 4 * q₂) (c := 2 * q₀) (a' := 8 * a') (b' := 2 * b') (c' := 2 * c')
    (by push_cast; linear_combination h' - (2 * q₁ + 2 * q₂ * α) * hα)
  refine (mem_cubeRootTwoOrder hα hK).mpr ⟨b, a', a, ?_⟩
  have hq₀ : q₀ = b := by linarith
  have hq₁ : q₁ = 2 * a' := by linarith
  have hq₂ : q₂ = 2 * a := by linarith
  rw [hq₀, hq₁, hq₂]
  push_cast
  ring

/-- If `x` multiplies `8ℤ + 2ℤα + 2ℤα²` into `ℤ + 2ℤα + 2ℤα²`, then every product of `x` with an
element of the ideal has even integer coordinates in the basis `1, α, α²`. -/
private theorem exists_even_coords_mul (x : K)
    (hx : ∀ y ∈ cubeRootTwoIdeal hα hK, y * x ∈ (cubeRootTwoOrder hα hK).toSubalgebra)
    {y : K} (hy : y ∈ cubeRootTwoIdeal hα hK) :
    ∃ a b c : ℤ, y * x = 2 * a + 2 * b * α + 2 * c * α ^ 2 := by
  obtain ⟨q₀, q₁, q₂, rfl⟩ := exists_coords_of_pow_three_eq_two hα hK x
  -- Multiplying by `2α` forces `q₀, q₁ ∈ ℤ` and `q₂ ∈ ¼ℤ`.
  obtain ⟨a, b, c, h⟩ := hx (2 * α) ((mem_cubeRootTwoIdeal hα hK).mpr ⟨0, 1, 0, by simp⟩)
  obtain ⟨-, hb, hc⟩ := coords_eq_of_pow_three_eq_two hα
    (a := 4 * q₂) (b := 2 * q₀) (c := 2 * q₁) (a' := a) (b' := 2 * b) (c' := 2 * c)
    (by push_cast; linear_combination h - 2 * q₂ * hα)
  -- Multiplying by `2α²` forces `q₂ ∈ ½ℤ`.
  obtain ⟨a', b', c', h'⟩ := hx (2 * α ^ 2) ((mem_cubeRootTwoIdeal hα hK).mpr ⟨0, 0, 1, by simp⟩)
  obtain ⟨-, hb', -⟩ := coords_eq_of_pow_three_eq_two hα
    (a := 4 * q₁) (b := 4 * q₂) (c := 2 * q₀) (a' := a') (b' := 2 * b') (c' := 2 * c')
    (by push_cast; linear_combination h' - (2 * q₁ + 2 * q₂ * α) * hα)
  have hq₀ : q₀ = b := by linarith
  have hq₁ : q₁ = c := by linarith
  have hq₂ : q₂ = b' / 2 := by linarith
  obtain ⟨u, v, w, rfl⟩ := (mem_cubeRootTwoIdeal hα hK).mp hy
  refine ⟨4 * u * b + v * b' + 2 * w * c, 4 * u * c + v * b + w * b',
    2 * u * b' + v * c + w * b, ?_⟩
  rw [hq₀, hq₁, hq₂]
  push_cast
  linear_combination (v * b' + 2 * w * c + w * b' * α) * hα

/-- The fractional ideal `8ℤ + 2ℤα + 2ℤα²` of `ℤ + 2ℤα + 2ℤα²` is not invertible, although it is
proper by `isProperFractionalIdeal_cubeRootTwoIdeal`. -/
theorem not_isUnit_cubeRootTwoIdeal : ¬ IsUnit (cubeRootTwoIdeal hα hK) := by
  intro hA
  obtain ⟨B, hAB⟩ := hA.exists_right_inv
  -- Every element of `A * B` has even integer coordinates.
  have hmem : ∀ z ∈ cubeRootTwoIdeal hα hK * B,
      ∃ a b c : ℤ, z = 2 * a + 2 * b * α + 2 * c * α ^ 2 := by
    intro z hz
    refine FractionalIdeal.mul_induction_on hz (fun y hy x hx => ?_) ?_
    · refine exists_even_coords_mul hα hK x (fun y' hy' => ?_) hy
      obtain ⟨r, hr⟩ := (FractionalIdeal.mem_one_iff _).mp (hAB ▸ mul_mem_mul hy' hx)
      exact hr ▸ r.2
    · rintro _ _ ⟨a, b, c, rfl⟩ ⟨a', b', c', rfl⟩
      exact ⟨a + a', b + b', c + c', by push_cast; ring⟩
  -- But `1 ∈ A * B = 1`, and `1` has odd constant coordinate.
  obtain ⟨a, b, c, h⟩ := hmem 1 (hAB ▸ FractionalIdeal.one_mem_one _)
  obtain ⟨h0, -, -⟩ := coords_eq_of_pow_three_eq_two hα
    (a := 1) (b := 0) (c := 0) (a' := 2 * a) (b' := 2 * b) (c' := 2 * c)
    (by push_cast; linear_combination h)
  have h0' : (1 : ℤ) = 2 * a := by exact_mod_cast h0
  omega

/-- The class of the proper ideal `8ℤ + 2ℤα + 2ℤα²` in the ideal class monoid of
`ℤ + 2ℤα + 2ℤα²` is not a unit, so it is not the image of any class in the Picard group. -/
theorem not_isUnit_mkIdealClassMonoid_cubeRootTwoIdeal :
    ¬ IsUnit ((cubeRootTwoOrder hα hK).mkIdealClassMonoid
      ⟨cubeRootTwoIdeal hα hK, isProperFractionalIdeal_cubeRootTwoIdeal hα hK⟩) := by
  rw [NumberFieldOrder.mkIdealClassMonoid_eq_mk, IdealClassMonoid.isUnit_mk_iff]
  exact not_isUnit_cubeRootTwoIdeal hα hK

end Ideal

/-! ### A cubic field containing a cube root of two -/

/-- Some cubic number field has an order with a proper fractional ideal whose class in the ideal
class monoid is not a unit. The field is `ℚ(∛2) = AdjoinRoot (X³ - 2)`, the order is
`ℤ + 2ℤ∛2 + 2ℤ∛4`, and the ideal is `8ℤ + 2ℤ∛2 + 2ℤ∛4`. -/
theorem exists_finrank_eq_three_properFractionalIdeal_not_isUnit :
    ∃ (F : Type) (_ : Field F) (_ : NumberField F), Module.finrank ℚ F = 3 ∧
      ∃ (O : NumberFieldOrder F) (I : O.properFractionalIdeals),
        ¬ IsUnit (O.mkIdealClassMonoid I) := by
  have : Fact (Irreducible (X ^ 3 - 2 : ℚ[X])) := ⟨irreducible_X_pow_three_sub_two⟩
  let F := AdjoinRoot (X ^ 3 - 2 : ℚ[X])
  have hf : (X ^ 3 - 2 : ℚ[X]) ≠ 0 := irreducible_X_pow_three_sub_two.ne_zero
  have hF : Module.finrank ℚ F = 3 := by
    rw [(AdjoinRoot.powerBasis hf).finrank, AdjoinRoot.powerBasis_dim]
    compute_degree!
  have : FiniteDimensional ℚ F := (AdjoinRoot.powerBasis hf).finite
  have : NumberField F := ⟨⟩
  have hα : AdjoinRoot.root (X ^ 3 - 2 : ℚ[X]) ^ 3 = 2 := by
    have h := AdjoinRoot.eval₂_root (X ^ 3 - 2 : ℚ[X])
    simp only [eval₂_sub, eval₂_X_pow, eval₂_ofNat] at h
    exact sub_eq_zero.mp h
  exact ⟨F, inferInstance, inferInstance, hF, cubeRootTwoOrder hα hF,
    ⟨_, isProperFractionalIdeal_cubeRootTwoIdeal hα hF⟩,
    not_isUnit_mkIdealClassMonoid_cubeRootTwoIdeal hα hF⟩

end TauCeti.GlobalNumberFields
