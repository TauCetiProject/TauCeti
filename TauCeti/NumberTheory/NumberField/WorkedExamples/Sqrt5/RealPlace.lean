/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
public import Mathlib.NumberTheory.Real.GoldenRatio
public import TauCeti.NumberTheory.NumberField.WorkedExamples.Sqrt5.Basic
import TauCeti.NumberTheory.NumberField.Index.PowerBasis

/-!
# The real places of `ℚ(√5)`

For `K` generated over `ℚ` by an algebraic integer `θ` with `minpoly ℤ θ = X² − X − 1`, the
golden ratio `Real.goldenRatio = (1 + √5)/2` is a real root of `X² − X − 1`, so there is a real
infinite place `w` with `w θ = Real.goldenRatio`; in degree two this forces two real places,
hence unit rank one.

## Main results

* `TauCeti.NumberField.Sqrt5.exists_isReal_and_apply_eq_goldenRatio`: a real place at the
  golden ratio.
* `TauCeti.NumberField.Sqrt5.rank_eq_one`: unit rank one.
-/

public section

open Polynomial NumberField NumberField.InfinitePlace NumberField.Units TauCeti.NumberField
open scoped NumberField

namespace TauCeti.NumberField.Sqrt5

variable {K : Type*} [Field K] [NumberField K] {θ : 𝓞 K}

/-- **The real place at the golden ratio.** There is a real infinite place `w` of `ℚ(√5)` with
`w θ = Real.goldenRatio`. -/
theorem exists_isReal_and_apply_eq_goldenRatio (hmin : minpoly ℤ θ = X ^ 2 - X - 1)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) :
    ∃ w : InfinitePlace K, w.IsReal ∧ w θ = Real.goldenRatio := by
  obtain ⟨φ, hφ⟩ : ∃ φ : ℝ, φ = Real.goldenRatio := ⟨_, rfl⟩
  have hφ2 : φ ^ 2 = φ + 1 := by rw [hφ]; exact Real.goldenRatio_sq
  have hφ0 : 0 < φ := by rw [hφ]; exact Real.goldenRatio_pos
  let ϑ : IntegralPrimitiveElement K := ⟨θ, hgen⟩
  -- The real embedding sending `θ` to `φ`.
  have hroot : aeval φ (minpoly ℚ (IntegralPrimitiveElement.powerBasis ϑ).gen) = 0 := by
    rw [IntegralPrimitiveElement.powerBasis_gen,
      minpoly.isIntegrallyClosed_eq_field_fractions' ℚ (RingOfIntegers.isIntegral_coe θ),
      minpoly.algebraMap_eq RingOfIntegers.coe_injective, hmin, aeval_map_algebraMap]
    simp only [map_sub, map_pow, aeval_X, map_one]
    linear_combination hφ2
  let f : K →ₐ[ℚ] ℝ := (IntegralPrimitiveElement.powerBasis ϑ).lift φ hroot
  let ψ : K →+* ℂ := Complex.ofRealHom.comp f.toRingHom
  have hψ : ComplexEmbedding.IsReal ψ := by
    rw [ComplexEmbedding.isReal_iff]
    ext x
    simp [ψ, ComplexEmbedding.conjugate_coe_eq, Complex.conj_ofReal]
  refine ⟨InfinitePlace.mk ψ, isReal_mk_iff.mpr hψ, ?_⟩
  have hfθ : f θ = φ := by
    have := (IntegralPrimitiveElement.powerBasis ϑ).lift_gen φ hroot
    rwa [IntegralPrimitiveElement.powerBasis_gen] at this
  rw [InfinitePlace.apply, ← hφ]
  simp only [ψ, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, hfθ,
    Complex.ofRealHom_eq_coe, Complex.norm_real, Real.norm_eq_abs]
  exact abs_of_pos hφ0

/-- `ℚ(√5)` has unit rank one. -/
theorem rank_eq_one (hmin : minpoly ℤ θ = X ^ 2 - X - 1)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) : rank K = 1 := by
  obtain ⟨w, hw, -⟩ := exists_isReal_and_apply_eq_goldenRatio hmin hgen
  -- Two places, one of which is real, in degree two means two real places.
  have hcard := card_add_two_mul_card_eq_rank K
  rw [finrank_eq_two hmin hgen] at hcard
  have hpos : nrRealPlaces K ≠ 0 := by
    classical
    have : Nonempty {w : InfinitePlace K // w.IsReal} := ⟨⟨w, hw⟩⟩
    exact Fintype.card_ne_zero
  rw [rank, card_eq_nrRealPlaces_add_nrComplexPlaces]
  omega

end TauCeti.NumberField.Sqrt5
