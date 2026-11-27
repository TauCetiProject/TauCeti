/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import TauCeti.Analysis.Normed.Field.Powers
public import TauCeti.NumberTheory.NumberField.Global.Ideles.Basic

/-!
# Powers in the ideles

For `n ≠ 0`, an idele is an `n`-th power exactly when each of its local coordinates is an `n`-th
power. A root of a local unit of valuation one again has valuation one, so local roots chosen at
every place assemble to an idele. For a number field `K` the `n`-th powers of the local unit groups
`K_vˣ` are open subgroups, hence closed, and the coordinates of an idele are continuous; so the
`n`-th powers form a closed subgroup of the ideles. In the language of adelic points, the image of
the `n`-th power map of `𝔾ₘ` on `𝔾ₘ(𝔸_K) = 𝔸_K^×` is closed. For `K = ℚ` and `n = 2` this
image `(𝔸_ℚ^×)²` is not open, so the adelic power map is not open.

## Main statements

* `NumberField.IdeleGroup.mem_range_powMonoidHom_iff`: an idele is an `n`-th power if and only if
  each of its coordinates is.
* `NumberField.IdeleGroup.isClosed_range_powMonoidHom`: the `n`-th powers are closed in the ideles
  of a number field.
-/

public section

open IsDedekindDomain NumberField

namespace NumberField.IdeleGroup

section Coordinates

variable {K : Type*} [Field K]
variable {R : Type*} [CommRing R] [IsDedekindDomain R] [Algebra R K] [IsFractionRing R K]

/-- **An idele is an `n`-th power if and only if each of its coordinates is**, for `n ≠ 0`. An
`n`-th root of a local unit of valuation one has valuation one, so roots chosen at every place
form an idele. -/
theorem mem_range_powMonoidHom_iff {n : ℕ} (hn : n ≠ 0) (x : IdeleGroup R K) :
    x ∈ (powMonoidHom n : IdeleGroup R K →* IdeleGroup R K).range ↔
      (∀ w : InfinitePlace K,
        w.ideleInfiniteCoord x ∈ (powMonoidHom n : w.Completionˣ →* w.Completionˣ).range) ∧
      ∀ v : HeightOneSpectrum R, v.ideleFiniteCoord x ∈
        (powMonoidHom n : (v.adicCompletion K)ˣ →* (v.adicCompletion K)ˣ).range := by
  refine ⟨?_, fun ⟨hinf, hfin⟩ ↦ ?_⟩
  · rintro ⟨y, rfl⟩
    exact ⟨fun w ↦ ⟨w.ideleInfiniteCoord y, by simp⟩, fun v ↦ ⟨v.ideleFiniteCoord y, by simp⟩⟩
  choose zi hzi using hinf
  choose z hz using hfin
  -- `x` is a local unit of valuation one at almost every place, and so is its root `z v` there.
  have hx : ∀ᶠ v : HeightOneSpectrum R in Filter.cofinite,
      Valued.v (v.ideleFiniteCoord x : v.adicCompletion K) = 1 := by
    filter_upwards [(localUnitsEquiv R K x).2.property] with v hv
    rw [← localUnitsEquiv_apply_snd]
    exact HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one.1 hv
  have hz' : ∀ᶠ v : HeightOneSpectrum R in Filter.cofinite,
      z v ∈ (v.adicCompletionIntegers K).units := by
    filter_upwards [hx] with v hv
    rw [HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one]
    rw [← hz v, powMonoidHom_apply, Units.val_pow_eq_pow_val, map_pow] at hv
    exact (pow_eq_one_iff_left hn).1 hv
  refine ⟨TauCeti.GlobalNumberFields.ideleOfUnits zi z hz', NumberField.IdeleGroup.ext
    (fun w ↦ ?_) (fun v ↦ ?_)⟩
  · rw [powMonoidHom_apply, map_pow, TauCeti.GlobalNumberFields.ideleInfiniteCoord_ideleOfUnits,
      ← powMonoidHom_apply, hzi]
  · rw [powMonoidHom_apply, map_pow, TauCeti.GlobalNumberFields.ideleFiniteCoord_ideleOfUnits,
      ← powMonoidHom_apply, hz]

/-- The coordinate of an idele at an infinite place is continuous. -/
theorem continuous_ideleInfiniteCoord (w : InfinitePlace K) :
    Continuous (w.ideleInfiniteCoord : IdeleGroup R K → w.Completionˣ) := by
  have : (w.ideleInfiniteCoord : IdeleGroup R K → w.Completionˣ) =
      fun x ↦ (localUnitsEquiv R K x).1 w := funext fun x ↦ (localUnitsEquiv_apply_fst x w).symm
  rw [this]
  exact (continuous_apply w).comp (continuous_fst.comp (localUnitsEquiv R K).continuous)

/-- The coordinate of an idele at a finite place is continuous. -/
theorem continuous_ideleFiniteCoord (v : HeightOneSpectrum R) :
    Continuous (v.ideleFiniteCoord : IdeleGroup R K → (v.adicCompletion K)ˣ) := by
  have : (v.ideleFiniteCoord : IdeleGroup R K → (v.adicCompletion K)ˣ) =
      fun x ↦ (localUnitsEquiv R K x).2 v := funext fun x ↦ (localUnitsEquiv_apply_snd x v).symm
  rw [this]
  exact (RestrictedProduct.continuous_eval v).comp
    (continuous_snd.comp (localUnitsEquiv R K).continuous)

end Coordinates

variable {K : Type*} [Field K] [NumberField K]

/-- **The `n`-th powers are closed in the ideles of a number field**, for `n ≠ 0`. By
`mem_range_powMonoidHom_iff` they are the ideles whose coordinates are `n`-th powers, and the
`n`-th powers of each local unit group are an open, hence closed, subgroup
(`TauCeti.isOpen_range_powMonoidHom_units`). -/
theorem isClosed_range_powMonoidHom {n : ℕ} (hn : n ≠ 0) :
    IsClosed ((powMonoidHom n : IdeleGroup (𝓞 K) K →* IdeleGroup (𝓞 K) K).range :
      Set (IdeleGroup (𝓞 K) K)) := by
  have hS : ((powMonoidHom n : IdeleGroup (𝓞 K) K →* IdeleGroup (𝓞 K) K).range :
      Set (IdeleGroup (𝓞 K) K)) =
      (⋂ w : InfinitePlace K, w.ideleInfiniteCoord ⁻¹'
        (powMonoidHom n : w.Completionˣ →* w.Completionˣ).range) ∩
      ⋂ v : HeightOneSpectrum (𝓞 K), v.ideleFiniteCoord ⁻¹'
        (powMonoidHom n : (v.adicCompletion K)ˣ →* (v.adicCompletion K)ˣ).range := by
    ext x
    simp only [SetLike.mem_coe, Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage]
    exact mem_range_powMonoidHom_iff hn x
  rw [hS]
  refine (isClosed_iInter fun w ↦ ?_).inter (isClosed_iInter fun v ↦ ?_)
  · refine IsClosed.preimage (continuous_ideleInfiniteCoord w) (Subgroup.isClosed_of_isOpen _ ?_)
    refine TauCeti.isOpen_range_powMonoidHom_units ?_
    rw [← map_natCast (algebraMap K w.Completion)]
    exact (map_ne_zero _).2 (Nat.cast_ne_zero.2 hn)
  · refine IsClosed.preimage (continuous_ideleFiniteCoord v) (Subgroup.isClosed_of_isOpen _ ?_)
    refine TauCeti.isOpen_range_powMonoidHom_units ?_
    rw [← map_natCast (algebraMap K (v.adicCompletion K))]
    exact (map_ne_zero _).2 (Nat.cast_ne_zero.2 hn)

end NumberField.IdeleGroup
