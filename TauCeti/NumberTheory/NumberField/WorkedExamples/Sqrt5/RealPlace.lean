/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Real.GoldenRatio
public import TauCeti.NumberTheory.NumberField.Units.Dirichlet
public import TauCeti.NumberTheory.NumberField.WorkedExamples.Sqrt5.Basic
import TauCeti.NumberTheory.NumberField.Index.PowerBasis
import TauCeti.NumberTheory.NumberField.Minpoly
import TauCeti.NumberTheory.NumberField.WorkedExamples.Sqrt5.Invariants

/-!
# The real places of `ℚ(√5)`

For `K` generated over `ℚ` by an algebraic integer `θ` with `minpoly ℤ θ = X² − X − 1`, the
golden ratio `Real.goldenRatio = (1 + √5)/2` is a real root of `X² − X − 1`, so there is a real
infinite place `w` with `w θ = Real.goldenRatio`; a real quadratic field has unit rank one.
At two distinct real places the values of `θ` are the two roots `(1 ± √5)/2`, so `θ` is positive
at one real place and negative at the other.

## Main results

* `TauCeti.NumberField.Sqrt5.exists_isReal_and_apply_eq_goldenRatio`: a real place at the
  golden ratio.
* `TauCeti.NumberField.Sqrt5.embedding_of_isReal_mul_embedding_of_isReal_eq_neg_one`: the real
  values of `θ` at two distinct real places multiply to `-1`.
* `TauCeti.NumberField.Sqrt5.exists_realPlaces_pos_neg`: the two real places, ordered so that
  `θ` is positive at the first and negative at the second.
* `TauCeti.NumberField.Sqrt5.units_rank_eq_one`: unit rank one.
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
    rw [IntegralPrimitiveElement.powerBasis_gen, RingOfIntegers.minpoly_rat_coe, hmin,
      aeval_map_algebraMap]
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

/-- **`θ` has opposite signs at the two real places.** At two distinct real places of `ℚ(√5)` the
real values of `θ` are the two distinct roots of `X² − X − 1`, so their product is `-1`. -/
theorem embedding_of_isReal_mul_embedding_of_isReal_eq_neg_one
    (hmin : minpoly ℤ θ = X ^ 2 - X - 1) (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤)
    {w₁ w₂ : InfinitePlace K} (hw₁ : w₁.IsReal) (hw₂ : w₂.IsReal) (hne : w₁ ≠ w₂) :
    embedding_of_isReal hw₁ (θ : K) * embedding_of_isReal hw₂ (θ : K) = -1 := by
  -- Every real value of `θ` is a root of `X² − X − 1`.
  have hθ : (θ : K) ^ 2 - θ - 1 = 0 := by
    have h := minpoly.aeval ℤ θ
    simp only [hmin, map_sub, map_pow, aeval_X, map_one] at h
    exact_mod_cast congrArg ((↑) : 𝓞 K → K) h
  have hroot (f : K →+* ℝ) : f θ ^ 2 = f θ + 1 := by
    have h := congrArg f hθ
    simp only [map_sub, map_pow, map_one, map_zero] at h
    linear_combination h
  -- Distinct real places have distinct real embeddings, which therefore differ at the generator.
  have hne' : embedding_of_isReal hw₁ (θ : K) ≠ embedding_of_isReal hw₂ θ := by
    intro h
    have hf : (embedding_of_isReal hw₁).toRatAlgHom = (embedding_of_isReal hw₂).toRatAlgHom :=
      AlgHom.ext_of_adjoin_eq_top hgen fun x hx => by
        rw [Set.mem_singleton_iff.mp hx]
        exact h
    refine hne (embedding_injective K (RingHom.ext fun x => ?_))
    rw [← embedding_of_isReal_apply hw₁, ← embedding_of_isReal_apply hw₂,
      ← RingHom.toRatAlgHom_apply, hf, RingHom.toRatAlgHom_apply]
  -- Two distinct roots of `X² − X − 1` sum to `1`, so their product is `-1`.
  have hsum : embedding_of_isReal hw₁ (θ : K) + embedding_of_isReal hw₂ θ = 1 :=
    mul_left_cancel₀ (sub_ne_zero.mpr hne') (by
      linear_combination hroot (embedding_of_isReal hw₁) - hroot (embedding_of_isReal hw₂))
  linear_combination embedding_of_isReal hw₁ (θ : K) * hsum - hroot (embedding_of_isReal hw₁)

open scoped Classical in
/-- The two real places of `ℚ(√5)`, ordered so that `θ` is positive at the first and negative at
the second. -/
theorem exists_realPlaces_pos_neg (hmin : minpoly ℤ θ = X ^ 2 - X - 1)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) :
    ∃ w₁ w₂ : {w : InfinitePlace K // w.IsReal}, w₁ ≠ w₂ ∧ Finset.univ = {w₁, w₂} ∧
      0 < embedding_of_isReal w₁.2 (θ : K) ∧ embedding_of_isReal w₂.2 (θ : K) < 0 := by
  obtain ⟨a, b, hab, hw⟩ := Finset.card_eq_two.mp (nrRealPlaces_eq_two hmin hgen)
  have hsign := embedding_of_isReal_mul_embedding_of_isReal_eq_neg_one hmin hgen a.2 b.2
    (Subtype.coe_injective.ne hab)
  have ha : embedding_of_isReal a.2 (θ : K) ≠ 0 := fun h => by simp [h] at hsign
  rcases lt_or_gt_of_ne ha with ha | ha
  · exact ⟨b, a, hab.symm, by rw [hw, Finset.pair_comm], by nlinarith, ha⟩
  · exact ⟨a, b, hab, hw, ha, by nlinarith⟩

/-- `ℚ(√5)` has unit rank one. -/
theorem units_rank_eq_one (hmin : minpoly ℤ θ = X ^ 2 - X - 1)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) : rank K = 1 := by
  obtain ⟨w, hw, -⟩ := exists_isReal_and_apply_eq_goldenRatio hmin hgen
  exact rank_eq_one_of_finrank_eq_two_of_isReal (finrank_eq_two hmin hgen) hw

end TauCeti.NumberField.Sqrt5
