/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Polydisc.GaussPoint
public import TauCeti.RingTheory.Huber.Normed

import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.Complete

/-!
# Gauss points of the discs in the closed unit disc

Let `K` be a complete nontrivially normed nonarchimedean field and `K⟨T⟩` the coordinate ring of
the closed unit disc `closedPolydisc 1 K`. For a centre `a` with `‖a‖ ≤ 1` and a radius
`0 < r ≤ 1`, the point `η_{a,r}` of the disc is the Gauss norm of radius `r` expanded about `a`:

```text
η_{a,r} : f = ∑ bₙ (T - a)ⁿ ↦ sup_n ‖bₙ‖ rⁿ.
```

These are the points of types (2) and (3) in Wedhorn's description of the closed unit disc
(Example 7.57), the points on its limbs. The point `η_{a,r}` is the pullback of the Gauss point
`η_r = gaussPoint` about the origin along the translation `T ↦ T + a` of `K⟨T⟩`.

The main result is that `η_{a,r}` depends only on the disc `D(a, r) = {y : ‖y - a‖ ≤ r}`, while
distinct radii give distinct points: `η_{a,r} = η_{b,s}` exactly when `r = s` and
`‖a - b‖ ≤ r`. The key input is that the Gauss norm of radius `r` is invariant under translation
by any `c` with `‖c‖ ≤ r`, which holds over any complete normed commutative ring with
multiplicative ultrametric norm. In particular, at `r = 1` every centre gives the Gauss point of the
disc. Like the Gauss point about the origin, `η_{a,r}` has trivial support and so is not a
classical point.

## Main definitions

* `TauCeti.ValuationSpectrum.discPoint`: the point `η_{a,r}` of the closed unit disc.

## Main results

* `TauCeti.ValuationSpectrum.closedDiscGaussValuation_translateHom`: the Gauss norm of radius `r`
  is invariant under translation by `c` with `‖c‖ ≤ r`.
* `TauCeti.ValuationSpectrum.discPoint_vle_iff`: `η_{a,r}` compares `f` and `g` by the Gauss
  norms of radius `r` of `f(T + a)` and `g(T + a)`.
* `TauCeti.ValuationSpectrum.discPoint_zero`: about the origin, `η_{0,r}` is the Gauss point
  `η_r`.
* `TauCeti.ValuationSpectrum.discPoint_eq_discPoint_iff`: `η_{a,r} = η_{b,s}` if and only if
  `r = s` and `‖a - b‖ ≤ r`.
* `TauCeti.ValuationSpectrum.discPoint_one`: at radius one every centre gives the Gauss point.
* `TauCeti.ValuationSpectrum.supp_discPoint` and
  `TauCeti.ValuationSpectrum.discPoint_ne_classicalPoint`: `η_{a,r}` has trivial support and is
  not a classical point.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Example 7.57.
* S. Bosch, U. Güntzer, R. Remmert, *Non-Archimedean Analysis*, §5.1, for the Gauss norm on
  restricted power series.
-/

public section

namespace TauCeti.ValuationSpectrum

open TauCeti.Huber
open scoped NNReal

/-! ### Translation invariance of the Gauss norm -/

section NormedRing

variable {R : Type*} [NormedCommRing R] [IsUltrametricDist R] [NonarchimedeanRing R]
  [NormMulClass R] [NormOneClass R] [CompleteSpace R] {r : ℝ}

/-- Translation `T ↦ T + c` with `‖c‖ ≤ r` does not increase the Gauss norm of radius `r`: for
`f = ∑ fₙ Tⁿ` every translated monomial `fₙ (T + c)ⁿ` has Gauss norm at most `‖fₙ‖ rⁿ`, and the
closed ball of the Gauss norm is a closed additive subgroup containing their sums. -/
private theorem closedDiscGaussValuation_translateHom_le (hr₀ : 0 < r) (hr₁ : r ≤ 1)
    (a : Fin 1 → R) (ha : ∀ i, IsPowerBounded (a i)) (har : ‖a 0‖ ≤ r)
    (f : weightedRestrictedSubring (fun _ : Fin 1 ↦ ({1} : Set R)) isWeightFamily_one_weight) :
    closedDiscGaussValuation hr₀ hr₁ (translateHom a ha f) ≤
      closedDiscGaussValuation hr₀ hr₁ f := by
  set v := closedDiscGaussValuation (R := R) hr₀ hr₁
  rcases eq_or_ne f 0 with rfl | hf
  · simp
  have hvf : v f ≠ 0 := (closedDiscGaussValuation_eq_zero_iff hr₀ hr₁).not.mpr hf
  have hclosed := AddSubgroup.isClosed_of_isOpen (v.leAddSubgroup (v f))
    ((isContinuous_closedDiscGaussValuation hr₀ hr₁).isOpen_le hvf)
  -- the shifted variable `T + a` has Gauss norm at most `r`
  have hX : (v (weightedX _ isWeightFamily_one_weight 0 +
      weightedC _ isWeightFamily_one_weight (a 0)) : ℝ) ≤ r := by
    refine (NNReal.coe_le_coe.mpr (v.map_add _ _)).trans ?_
    rw [NNReal.coe_max, coe_closedDiscGaussValuation_weightedX, closedDiscGaussValuation_weightedC,
      coe_nnnorm]
    exact max_le le_rfl har
  refine hclosed.mem_of_tendsto (hasSum_translateHom a ha f)
    (Filter.Eventually.of_forall fun _ ↦ (v.leAddSubgroup (v f)).sum_mem fun ν _ ↦ ?_)
  -- in one variable every multi-index is `n • e₀`
  obtain ⟨n, rfl⟩ : ∃ n, ν = Finsupp.single 0 n :=
    ⟨ν 0, Finsupp.ext fun i ↦ by rw [Subsingleton.elim i 0, Finsupp.single_eq_same]⟩
  rw [Valuation.mem_leAddSubgroup_iff, ← NNReal.coe_le_coe, map_mul, Fin.prod_univ_one, map_pow,
    NNReal.coe_mul, NNReal.coe_pow, closedDiscGaussValuation_weightedC, coe_nnnorm,
    Finsupp.single_eq_same]
  calc ‖MvPowerSeries.coeff (Finsupp.single 0 n) (f : MvPowerSeries (Fin 1) R)‖ *
        (v (weightedX _ _ 0 + weightedC _ isWeightFamily_one_weight (a 0)) : ℝ) ^ n
      ≤ ‖MvPowerSeries.coeff (Finsupp.single 0 n) (f : MvPowerSeries (Fin 1) R)‖ * r ^ n := by
        gcongr
    _ ≤ v f := norm_coeff_mul_pow_le_closedDiscGaussValuation hr₀ hr₁ f n

/-- **The Gauss norm of radius `r` is invariant under translation by `c` with `‖c‖ ≤ r`**: the
Gauss norms of `f(T)` and `f(T + c)` agree. Here `c` is the sole entry `a 0` of the tuple `a`. -/
theorem closedDiscGaussValuation_translateHom (hr₀ : 0 < r) (hr₁ : r ≤ 1) (a : Fin 1 → R)
    (ha : ∀ i, IsPowerBounded (a i)) (har : ‖a 0‖ ≤ r)
    (f : weightedRestrictedSubring (fun _ : Fin 1 ↦ ({1} : Set R)) isWeightFamily_one_weight) :
    closedDiscGaussValuation hr₀ hr₁ (translateHom a ha f) = closedDiscGaussValuation hr₀ hr₁ f :=
  le_antisymm (closedDiscGaussValuation_translateHom_le hr₀ hr₁ a ha har f) <| by
    simpa only [translateHom_neg_translateHom] using
      closedDiscGaussValuation_translateHom_le hr₀ hr₁ (-a) (fun i ↦ (ha i).neg)
        (by rwa [Pi.neg_apply, norm_neg]) (translateHom a ha f)

end NormedRing

/-! ### The points `η_{a,r}` -/

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [NonarchimedeanRing K]
  [CompleteSpace K] {r s : ℝ}

/-- **The point `η_{a,r}` of the closed unit disc**, for a centre `‖a‖ ≤ 1` and a radius
`0 < r ≤ 1`: the Gauss norm of radius `r` about `a`, `f ↦ sup_n ‖bₙ‖ rⁿ` where
`f = ∑ bₙ (T - a)ⁿ`. It is the pullback of the Gauss point `η_r` along the translation
`T ↦ T + a`. -/
noncomputable def discPoint (a : K) (ha : ‖a‖ ≤ 1) (hr₀ : 0 < r) (hr₁ : r ≤ 1) :
    closedPolydisc 1 K :=
  ⟨comap (translateHom (fun _ ↦ a) (fun _ ↦ isPowerBounded_iff_norm_le_one.mpr ha))
    (gaussPoint hr₀ hr₁).1, by
    obtain ⟨hcont, hle⟩ := (mem_closedPolydisc_iff _ _ _).mp (gaussPoint (K := K) hr₀ hr₁).2
    refine (mem_closedPolydisc_iff _ _ _).mpr
      ⟨hcont.comap (continuous_translateHom _ _), fun f hf ↦ ?_⟩
    rw [comap_vle, map_one]
    exact hle _ (translateHom_mem_powerBoundedSubring _ _ hf)⟩

/-- The underlying point in `Spv K⟨T⟩` is the pullback of the Gauss point `η_r` along the
translation `T ↦ T + a`. -/
theorem discPoint_val (a : K) (ha : ‖a‖ ≤ 1) (hr₀ : 0 < r) (hr₁ : r ≤ 1) :
    (discPoint a ha hr₀ hr₁).1 =
      comap (translateHom (fun _ ↦ a) (fun _ ↦ isPowerBounded_iff_norm_le_one.mpr ha))
        (gaussPoint hr₀ hr₁).1 :=
  (rfl)

/-- The point `η_{a,r}` compares `f` and `g` by the Gauss norms of radius `r` of `f(T + a)` and
`g(T + a)`. -/
@[simp]
theorem discPoint_vle_iff (a : K) (ha : ‖a‖ ≤ 1) (hr₀ : 0 < r) (hr₁ : r ≤ 1)
    (f g : weightedRestrictedSubring (fun _ : Fin 1 ↦ ({1} : Set K)) isWeightFamily_one_weight) :
    (discPoint a ha hr₀ hr₁).1.toValuativeRel.vle f g ↔
      closedDiscGaussValuation hr₀ hr₁
          (translateHom (fun _ ↦ a) (fun _ ↦ isPowerBounded_iff_norm_le_one.mpr ha) f) ≤
        closedDiscGaussValuation hr₀ hr₁
          (translateHom (fun _ ↦ a) (fun _ ↦ isPowerBounded_iff_norm_le_one.mpr ha) g) := by
  rw [discPoint_val, comap_vle, gaussPoint_vle_iff]

/-- **About the origin, `η_{0,r}` is the Gauss point `η_r`.** -/
@[simp]
theorem discPoint_zero (ha : ‖(0 : K)‖ ≤ 1) (hr₀ : 0 < r) (hr₁ : r ≤ 1) :
    discPoint 0 ha hr₀ hr₁ = gaussPoint hr₀ hr₁ := by
  -- translation by the zero tuple is the identity
  have h0 : translateHom (fun _ : Fin 1 ↦ (0 : K))
      (fun _ ↦ isPowerBounded_iff_norm_le_one.mpr ha) = RingHom.id _ :=
    translateHom_zero
  exact Subtype.ext (by rw [discPoint_val, h0, comap_id, id])

/-- **Recentring within the disc**: `η_{a,r} = η_r` whenever `‖a‖ ≤ r`, by translation invariance
of the Gauss norm of radius `r`. -/
private theorem discPoint_eq_gaussPoint_of_norm_le {a : K} (ha : ‖a‖ ≤ 1) (hr₀ : 0 < r)
    (hr₁ : r ≤ 1) (har : ‖a‖ ≤ r) : discPoint a ha hr₀ hr₁ = gaussPoint hr₀ hr₁ :=
  Subtype.ext <| ext' fun f g ↦ by
    rw [discPoint_vle_iff, gaussPoint_vle_iff, closedDiscGaussValuation_translateHom _ _ _ _ har,
      closedDiscGaussValuation_translateHom _ _ _ _ har]

/-- **`η_{a,r}` is the Gauss point `η_s` exactly when `r = s` and `‖a‖ ≤ r`.** If `‖a‖ > r`, then
`η_{a,r}` finds `T - a` strictly smaller than the constant `a`, while every Gauss point about the
origin finds it at least as large. -/
private theorem discPoint_eq_gaussPoint_iff {a : K} (ha : ‖a‖ ≤ 1) (hr₀ : 0 < r) (hr₁ : r ≤ 1)
    (hs₀ : 0 < s) (hs₁ : s ≤ 1) :
    discPoint a ha hr₀ hr₁ = gaussPoint hs₀ hs₁ ↔ r = s ∧ ‖a‖ ≤ r := by
  constructor
  swap
  · rintro ⟨rfl, har⟩
    exact discPoint_eq_gaussPoint_of_norm_le ha hr₀ hr₁ har
  intro h
  have har : ‖a‖ ≤ r := by
    by_contra! hlt
    have key := congrArg (fun p : closedPolydisc 1 K ↦ p.1.toValuativeRel.vle
      (weightedC _ isWeightFamily_one_weight a)
      (weightedX (fun _ : Fin 1 ↦ ({1} : Set K)) isWeightFamily_one_weight 0 -
        weightedC _ isWeightFamily_one_weight a)) h
    simp only [discPoint_vle_iff, gaussPoint_vle_iff, translateHom_weightedC, map_sub,
      translateHom_weightedX, add_sub_cancel_right, eq_iff_iff, ← NNReal.coe_le_coe,
      closedDiscGaussValuation_weightedC, coe_closedDiscGaussValuation_weightedX,
      coe_nnnorm] at key
    -- the constant coefficient of `T - a` bounds its Gauss norm of radius `s` below by `‖a‖`
    have hle := norm_coeff_mul_pow_le_closedDiscGaussValuation hs₀ hs₁
      (weightedX (fun _ : Fin 1 ↦ ({1} : Set K)) isWeightFamily_one_weight 0 -
        weightedC _ isWeightFamily_one_weight a) 0
    simp only [Finsupp.single_zero, pow_zero, mul_one, coe_weightedX, coe_weightedC,
      AddSubgroupClass.coe_sub, map_sub, MvPowerSeries.coeff_zero_X, MvPowerSeries.coeff_zero_C,
      zero_sub, norm_neg] at hle
    exact (key.mpr (by simpa using hle)).not_gt hlt
  refine ⟨?_, har⟩
  rw [discPoint_eq_gaussPoint_of_norm_le ha hr₀ hr₁ har] at h
  exact (gaussPoint_inj hr₀ hr₁ hs₀ hs₁).mp h

/-- **`η_{a,r}` depends only on the disc `D(a, r)`**: `η_{a,r} = η_{b,s}` if and only if `r = s`
and `‖a - b‖ ≤ r`, that is, the radii agree and each centre lies in the other's disc. -/
theorem discPoint_eq_discPoint_iff {a b : K} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) (hr₀ : 0 < r)
    (hr₁ : r ≤ 1) (hs₀ : 0 < s) (hs₁ : s ≤ 1) :
    discPoint a ha hr₀ hr₁ = discPoint b hb hs₀ hs₁ ↔ r = s ∧ ‖a - b‖ ≤ r := by
  have hab : ‖a - b‖ ≤ 1 := by
    simpa only [sub_eq_add_neg] using
      (IsUltrametricDist.norm_add_le_max a (-b)).trans (max_le ha (by rwa [norm_neg]))
  -- pulling back along translation by `-b` is injective, and carries `η_{c,t}` to `η_{c - b,t}`
  let τ := translateHom (-fun _ : Fin 1 ↦ b) fun _ ↦ (isPowerBounded_iff_norm_le_one.mpr hb).neg
  have hsurj : Function.Surjective τ := fun f ↦
    ⟨_, translateHom_neg_translateHom (fun _ : Fin 1 ↦ b)
      (fun _ ↦ isPowerBounded_iff_norm_le_one.mpr hb) f⟩
  have hshift (c : K) (hc : ‖c‖ ≤ 1) (hcb : ‖c - b‖ ≤ 1) {t : ℝ} (ht₀ : 0 < t) (ht₁ : t ≤ 1) :
      comap τ (discPoint c hc ht₀ ht₁).1 = (discPoint (c - b) hcb ht₀ ht₁).1 := by
    rw [discPoint_val, discPoint_val, ← Function.comp_apply (f := comap τ), ← comap_comp,
      translateHom_comp_translateHom]
    congr 2
    exact funext fun _ ↦ (sub_eq_add_neg c b).symm
  have hbb : ∀ hbb : ‖b - b‖ ≤ 1, discPoint (b - b) hbb hs₀ hs₁ = gaussPoint hs₀ hs₁ := by
    simp only [sub_self, discPoint_zero, implies_true]
  rw [← discPoint_eq_gaussPoint_iff hab hr₀ hr₁ hs₀ hs₁, Subtype.ext_iff, Subtype.ext_iff,
    ← (comap_injective hsurj).eq_iff, hshift a ha hab hr₀ hr₁, hshift b hb (by simp) hs₀ hs₁, hbb]

/-- **At radius one every centre gives the Gauss point of the disc**: `D(a, 1)` is the whole
closed unit disc. -/
theorem discPoint_one (a : K) (ha : ‖a‖ ≤ 1) :
    discPoint a ha zero_lt_one le_rfl = gaussPoint (K := K) zero_lt_one le_rfl :=
  discPoint_eq_gaussPoint_of_norm_le ha zero_lt_one le_rfl ha

/-- A point `η_{a,r}` kills only the zero series. -/
theorem discPoint_vle_zero_iff (a : K) (ha : ‖a‖ ≤ 1) (hr₀ : 0 < r) (hr₁ : r ≤ 1)
    {f : weightedRestrictedSubring (fun _ : Fin 1 ↦ ({1} : Set K)) isWeightFamily_one_weight} :
    (discPoint a ha hr₀ hr₁).1.toValuativeRel.vle f 0 ↔ f = 0 := by
  rw [discPoint_val, comap_vle, map_zero, gaussPoint_vle_zero_iff,
    map_eq_zero_iff _ (translateHom_injective _ _)]

/-- **The support of `η_{a,r}` is trivial.** -/
@[simp]
theorem supp_discPoint (a : K) (ha : ‖a‖ ≤ 1) (hr₀ : 0 < r) (hr₁ : r ≤ 1) :
    (discPoint a ha hr₀ hr₁).1.supp = ⊥ :=
  Ideal.ext fun _ ↦ by rw [mem_supp_iff, discPoint_vle_zero_iff, Ideal.mem_bot]

/-- **The points `η_{a,r}` are not classical points.** -/
theorem discPoint_ne_classicalPoint (a : K) (ha : ‖a‖ ≤ 1) (hr₀ : 0 < r) (hr₁ : r ≤ 1)
    (x : spa (powerBoundedSubring K)) (b : Fin 1 → K) (hb : ∀ i, IsPowerBounded (b i)) :
    discPoint a ha hr₀ hr₁ ≠ classicalPoint x b hb := by
  intro h
  have hvle := (classicalPoint_vle x b hb
    (weightedX (fun _ : Fin 1 ↦ ({1} : Set K)) isWeightFamily_one_weight 0 -
      weightedC _ isWeightFamily_one_weight (b 0)) 0).mpr (by simp)
  rw [← h, discPoint_vle_zero_iff, sub_eq_zero] at hvle
  -- the variable and a constant differ in their coefficient of `T`
  have hcoeff := congrArg (MvPowerSeries.coeff (Finsupp.single 0 1)) (congrArg Subtype.val hvle)
  simp [MvPowerSeries.coeff_X, MvPowerSeries.coeff_C] at hcoeff

end TauCeti.ValuationSpectrum
