/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Units.Dirichlet
public import TauCeti.NumberTheory.NumberField.WorkedExamples.Sqrt2.Basic
import TauCeti.NumberTheory.NumberField.Index.PowerBasis
import TauCeti.NumberTheory.NumberField.Minpoly

/-!
# The real places of `ℚ(√2)`

For `K` generated over `ℚ` by an algebraic integer `θ` with `minpoly ℤ θ = X² − 2`, the real
number `√2` is a root of `X² − 2`, so there is a real infinite place `w` of `K` coming from the
real embedding sending `θ` to `√2`; at that place `1 + θ` has absolute value `1 + √2`. A real
quadratic field has unit rank one.

## Main results

* `TauCeti.NumberField.Sqrt2.exists_isReal_and_apply_eq_one_add_sqrt_two`: a real place where
  `1 + θ` has absolute value `1 + √2`.
* `TauCeti.NumberField.Sqrt2.units_rank_eq_one`: unit rank one.
-/

public section

open Polynomial NumberField NumberField.InfinitePlace NumberField.Units TauCeti.NumberField
open scoped NumberField

namespace TauCeti.NumberField.Sqrt2

variable {K : Type*} [Field K] [NumberField K] {θ : 𝓞 K}

/-- **The real place at `1 + √2`.** There is a real infinite place `w` of `ℚ(√2)` at which `1 + θ`
has absolute value `w (1 + θ) = 1 + √2`. -/
theorem exists_isReal_and_apply_eq_one_add_sqrt_two (hmin : minpoly ℤ θ = X ^ 2 - 2)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) :
    ∃ w : InfinitePlace K, w.IsReal ∧ w ((1 + θ : 𝓞 K) : K) = 1 + √2 := by
  let ϑ : IntegralPrimitiveElement K := ⟨θ, hgen⟩
  -- The real embedding sending `θ` to `√2`.
  have hroot : aeval √2 (minpoly ℚ (IntegralPrimitiveElement.powerBasis ϑ).gen) = 0 := by
    rw [IntegralPrimitiveElement.powerBasis_gen, RingOfIntegers.minpoly_rat_coe, hmin,
      aeval_map_algebraMap]
    simp [map_ofNat]
  let f : K →ₐ[ℚ] ℝ := (IntegralPrimitiveElement.powerBasis ϑ).lift √2 hroot
  let ψ : K →+* ℂ := Complex.ofRealHom.comp f.toRingHom
  have hψ : ComplexEmbedding.IsReal ψ := by
    rw [ComplexEmbedding.isReal_iff]
    ext x
    simp [ψ, ComplexEmbedding.conjugate_coe_eq, Complex.conj_ofReal]
  refine ⟨InfinitePlace.mk ψ, isReal_mk_iff.mpr hψ, ?_⟩
  have hfθ : f θ = √2 := by
    have := (IntegralPrimitiveElement.powerBasis ϑ).lift_gen √2 hroot
    rwa [IntegralPrimitiveElement.powerBasis_gen] at this
  rw [InfinitePlace.apply]
  simp only [ψ, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_add, map_one,
    hfθ, Complex.ofRealHom_eq_coe]
  rw [← Complex.ofReal_one, ← Complex.ofReal_add, Complex.norm_real, Real.norm_eq_abs]
  exact abs_of_pos (by positivity)

/-- `ℚ(√2)` has unit rank one. -/
theorem units_rank_eq_one (hmin : minpoly ℤ θ = X ^ 2 - 2)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) : rank K = 1 := by
  obtain ⟨w, hw, -⟩ := exists_isReal_and_apply_eq_one_add_sqrt_two hmin hgen
  exact rank_eq_one_of_finrank_eq_two_of_isReal (finrank_eq_two hmin hgen) hw

end TauCeti.NumberField.Sqrt2
