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
# Gauss points of the discs in the closed unit disc and the points next to them

Let `K` be a complete nontrivially normed nonarchimedean field and `K⟨T⟩` the coordinate ring of
the closed unit disc `closedPolydisc 1 K`. For a centre `a` with `‖a‖ ≤ 1` and a radius
`0 < r ≤ 1`, the point `η_{a,r}` of the disc is the Gauss norm of radius `r` expanded about `a`:

```text
η_{a,r} : f = ∑ bₙ (T - a)ⁿ ↦ sup_n ‖bₙ‖ rⁿ.
```

These are the Gauss points of the `K`-rational discs in the closed unit disc. When `K` is
algebraically closed they are exactly the points of types (2) (`r ∈ |K^×|`) and (3)
(`r ∉ |K^×|`) in Wedhorn's description of the closed unit disc (Example 7.57); over a general `K`,
Gauss points of discs whose centres need a field extension are not of this form. The point
`η_{a,r}` is the pullback of the Gauss point `η_r = gaussPoint` about the origin along the
translation `T ↦ T + a` of `K⟨T⟩`.

The main result is that `η_{a,r}` depends only on the disc `D(a, r) = {y : ‖y - a‖ ≤ r}`, while
distinct radii give distinct points: `η_{a,r} = η_{b,s}` exactly when `r = s` and
`‖a - b‖ ≤ r`. The key input is that the Gauss norm of radius `r` is invariant under translation
by any `c` with `‖c‖ ≤ r`, which holds over any complete normed commutative ring with
multiplicative ultrametric norm. In particular, at `r = 1` every centre gives the Gauss point of the
disc. Like the Gauss point about the origin, `η_{a,r}` has trivial support and so is not a
classical point.

The same translation recentres the refined points `η_{r⁺}` and `η_{r⁻}` next to `η_r`, giving
points `η_{a,r⁺}` (for `r < 1`) and `η_{a,r⁻}` of the disc. When `K` is algebraically closed
and `r ∈ |K^×|`, these are the points of type (5) in Wedhorn's Example 7.57, written there
`a_{>r}` and `a_{<r}`. Both specialize from `η_{a,r}`, and for `r ∈ |K^×|` the three points are
pairwise distinct.

The Gauss valuation just above `r` is invariant under translation by every `c` with `‖c‖ ≤ r`:
translation preserves the last degree in which a series attains its Gauss norm. So `η_{a,r⁺}`
depends only on the closed disc `D(a, r)`, and there is one such point for each point `η_{a,r}`.
The Gauss valuation just below `r` is invariant only under translation by `c` with `‖c‖ < r`,
since translating `T` by an element of norm `r` moves the first degree attaining its Gauss norm
from `1` to `0`. So `η_{a,r⁻}` depends exactly on the open disc `{y : ‖y - a‖ < r}`, and the open
discs of radius `r` inside `D(a, r)` give pairwise distinct points next to `η_{a,r}`. All three
invariance statements come from `TauCeti.ValuationSpectrum.valuation_taylorHom_eq`: a continuous
valuation that bounds every monomial of a series by the series, and the shifted variables `T + c`
and `T - c` by `T`, is invariant under translation by `c`.

## Main definitions

* `TauCeti.ValuationSpectrum.discPoint`: the point `η_{a,r}` of the closed unit disc.
* `TauCeti.ValuationSpectrum.discPointAbove` and `TauCeti.ValuationSpectrum.discPointBelow`: the
  points `η_{a,r⁺}` and `η_{a,r⁻}` of the closed unit disc.

## Main results

* `TauCeti.ValuationSpectrum.closedDiscGaussValuation_taylorHom`: the Gauss norm of radius `r`
  is invariant under translation by `c` with `‖c‖ ≤ r`.
* `TauCeti.ValuationSpectrum.discPoint_vle_iff`: `η_{a,r}` compares `f` and `g` by the Gauss
  norms of radius `r` of `f(T + a)` and `g(T + a)`.
* `TauCeti.ValuationSpectrum.discPoint_zero`: about the origin, `η_{0,r}` is the Gauss point
  `η_r`.
* `TauCeti.ValuationSpectrum.comap_taylorHom_discPoint`: pulling `η_{c,r}` back along the
  translation `T ↦ T + b` gives `η_{c+b,r}`.
* `TauCeti.ValuationSpectrum.discPoint_eq_gaussPoint_iff`: `η_{a,r} = η_s` if and only if `r = s`
  and `‖a‖ ≤ r`.
* `TauCeti.ValuationSpectrum.discPoint_eq_discPoint_iff`: `η_{a,r} = η_{b,s}` if and only if
  `r = s` and `‖a - b‖ ≤ r`.
* `TauCeti.ValuationSpectrum.discPoint_radius_one`: at radius one every centre gives the Gauss
  point.
* `TauCeti.ValuationSpectrum.supp_discPoint` and
  `TauCeti.ValuationSpectrum.discPoint_ne_classicalPoint`: `η_{a,r}` has trivial support and is
  not a classical point.
* `TauCeti.ValuationSpectrum.closedDiscGaussValuationAbove_taylorHom` and
  `TauCeti.ValuationSpectrum.closedDiscGaussValuationBelow_taylorHom`: the Gauss valuations just
  above and just below `r` are invariant under translation by `c` with `‖c‖ ≤ r`, respectively
  `‖c‖ < r`.
* `TauCeti.ValuationSpectrum.discPointAbove_vle_iff` and
  `TauCeti.ValuationSpectrum.discPointBelow_vle_iff`: how `η_{a,r⁺}` and `η_{a,r⁻}` compare series.
* `TauCeti.ValuationSpectrum.discPointAbove_vle_weightedC_iff`,
  `TauCeti.ValuationSpectrum.discPointAbove_weightedC_vle_iff`,
  `TauCeti.ValuationSpectrum.discPointBelow_vle_weightedC_iff` and
  `TauCeti.ValuationSpectrum.discPointBelow_weightedC_vle_iff`: `η_{a,r⁺}` places `T - a` just
  above the constants of norm `r`, and `η_{a,r⁻}` just below them.
* `TauCeti.ValuationSpectrum.valuation_weightedX_sub_weightedC_of_lt`: a point at which `T - a` is
  never equal in value to a constant takes on `T - b` the value of `T - a` or of `b - a`.
* `TauCeti.ValuationSpectrum.valuation_weightedX_sub_weightedC_discPointAbove` and
  `TauCeti.ValuationSpectrum.valuation_weightedX_sub_weightedC_discPointBelow`: the values of
  `η_{a,r±}` on every linear polynomial `T - b`.
* `TauCeti.ValuationSpectrum.discPointAbove_eq_gaussPointAbove_iff` and
  `TauCeti.ValuationSpectrum.discPointBelow_eq_gaussPointBelow_iff`: `η_{a,r⁺} = η_{s⁺}` exactly
  when `r = s` and `‖a‖ ≤ r`, and `η_{a,r⁻} = η_{s⁻}` exactly when `r = s` and `‖a‖ < r`.
* `TauCeti.ValuationSpectrum.discPointAbove_eq_discPointAbove_iff` and
  `TauCeti.ValuationSpectrum.discPointBelow_eq_discPointBelow_iff`: `η_{a,r⁺} = η_{b,s⁺}` exactly
  when `r = s` and `‖a - b‖ ≤ r`, and `η_{a,r⁻} = η_{b,s⁻}` exactly when `r = s` and
  `‖a - b‖ < r`.
* `TauCeti.ValuationSpectrum.discPoint_specializes_discPointAbove` and
  `TauCeti.ValuationSpectrum.discPoint_specializes_discPointBelow`: both points lie in the closure
  of `η_{a,r}`.
* `TauCeti.ValuationSpectrum.discPointAbove_ne_discPoint`,
  `TauCeti.ValuationSpectrum.discPointBelow_ne_discPoint` and
  `TauCeti.ValuationSpectrum.discPointBelow_ne_discPointAbove`: for `r` the norm of an element of
  `K`, the three points at centre `a` and radius `r` are pairwise distinct.
* `TauCeti.ValuationSpectrum.supp_discPointAbove`, `TauCeti.ValuationSpectrum.supp_discPointBelow`
  and the corresponding `_ne_classicalPoint` lemmas: both points have trivial support and are not
  classical points.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Example 7.57.
* S. Bosch, U. Güntzer, R. Remmert, *Non-Archimedean Analysis*, §5.1, for the Gauss norm on
  restricted power series.
* P. Scholze, *Perfectoid spaces*, Publ. Math. IHÉS 116 (2012), Example 2.20, for the points of
  type (5).
-/

public section

namespace TauCeti.ValuationSpectrum

open TauCeti.Huber
open scoped NNReal

/-! ### Translation invariance of the Gauss valuations -/

section NormedRing

variable {R : Type*} [NormedCommRing R] [IsUltrametricDist R] [NonarchimedeanRing R]
  [NormMulClass R] [NormOneClass R] [CompleteSpace R] {r : ℝ}

omit [IsUltrametricDist R] [NormMulClass R] [NormOneClass R] [CompleteSpace R] in
/-- In one variable every multi-index is `n • e₀`, so a valuation on `R⟨T⟩` bounding every monomial
`fₙ Tⁿ` of a series by the series bounds every monomial `f_ν T^ν` in the form taken by
`valuation_taylorHom_eq`. -/
private theorem valuation_monomial_le_of_forall_pow {Γ₀ : Type*}
    [LinearOrderedCommGroupWithZero Γ₀]
    {v : Valuation (weightedRestrictedSubring (fun _ : Fin 1 ↦ ({1} : Set R))
      isWeightFamily_one_weight) Γ₀}
    (hmono : ∀ (f : weightedRestrictedSubring (fun _ : Fin 1 ↦ ({1} : Set R))
      isWeightFamily_one_weight) (n : ℕ), v (weightedC _ isWeightFamily_one_weight
        (MvPowerSeries.coeff (Finsupp.single 0 n) (f : MvPowerSeries (Fin 1) R)) *
      weightedX _ isWeightFamily_one_weight 0 ^ n) ≤ v f)
    (f : weightedRestrictedSubring (fun _ : Fin 1 ↦ ({1} : Set R)) isWeightFamily_one_weight)
    (ν : Fin 1 →₀ ℕ) : v (weightedC _ isWeightFamily_one_weight
        (MvPowerSeries.coeff ν (f : MvPowerSeries (Fin 1) R)) *
      ∏ i, weightedX _ isWeightFamily_one_weight i ^ ν i) ≤ v f := by
  obtain ⟨n, rfl⟩ : ∃ n, ν = Finsupp.single 0 n := ⟨ν 0, Finsupp.unique_single ν⟩
  simpa only [Fin.prod_univ_one, Finsupp.single_eq_same] using hmono f n

/-- **The Gauss norm of radius `r` is invariant under translation by `c` with `‖c‖ ≤ r`**: the
Gauss norms of `f(T)` and `f(T + c)` agree. Here `c` is the sole entry `a 0` of the tuple `a`. -/
theorem closedDiscGaussValuation_taylorHom (hr₀ : 0 < r) (hr₁ : r ≤ 1) (a : Fin 1 → R)
    (ha : ∀ i, IsPowerBounded (a i)) (har : ‖a 0‖ ≤ r)
    (f : weightedRestrictedSubring (fun _ : Fin 1 ↦ ({1} : Set R)) isWeightFamily_one_weight) :
    closedDiscGaussValuation hr₀ hr₁ (taylorHom a ha f) = closedDiscGaussValuation hr₀ hr₁ f := by
  set v := closedDiscGaussValuation (R := R) hr₀ hr₁
  -- the shifted variable `T + c` has Gauss norm at most `r` when `‖c‖ ≤ r`
  have hX {c : R} (hc : ‖c‖ ≤ r) : v (weightedX _ isWeightFamily_one_weight 0 +
      weightedC _ isWeightFamily_one_weight c) ≤ v (weightedX _ isWeightFamily_one_weight 0) := by
    refine (v.map_add _ _).trans ?_
    rw [← NNReal.coe_le_coe, NNReal.coe_max, coe_closedDiscGaussValuation_weightedX,
      closedDiscGaussValuation_weightedC, coe_nnnorm]
    exact max_le le_rfl hc
  refine valuation_taylorHom_eq a ha (isContinuous_closedDiscGaussValuation hr₀ hr₁)
    (Fin.forall_fin_one.2 (hX har)) (Fin.forall_fin_one.2 (hX (by rwa [norm_neg])))
    (valuation_monomial_le_of_forall_pow fun g n ↦ ?_) f
  rw [← NNReal.coe_le_coe, map_mul, map_pow, NNReal.coe_mul, NNReal.coe_pow,
    closedDiscGaussValuation_weightedC, coe_closedDiscGaussValuation_weightedX, coe_nnnorm]
  exact norm_coeff_mul_pow_le_closedDiscGaussValuation hr₀ hr₁ g n

/-- **The Gauss valuation just above `r` is invariant under translation by `c` with
`‖c‖ ≤ r`**: `f(T)` and `f(T + c)` have the same Gauss norm of radius `r` and the same last degree
attaining it. Here `c` is the sole entry `a 0` of the tuple `a`. -/
theorem closedDiscGaussValuationAbove_taylorHom (hr₀ : 0 < r) (hr₁ : r ≤ 1) (a : Fin 1 → R)
    (ha : ∀ i, IsPowerBounded (a i)) (har : ‖a 0‖ ≤ r)
    (f : weightedRestrictedSubring (fun _ : Fin 1 ↦ ({1} : Set R)) isWeightFamily_one_weight) :
    closedDiscGaussValuationAbove hr₀ hr₁ (taylorHom a ha f) =
      closedDiscGaussValuationAbove hr₀ hr₁ f :=
  valuation_taylorHom_eq (Γ₀ := WithZero (ℝ≥0ˣ ×ₗ Multiplicative ℤ))
    (v := closedDiscGaussValuationAbove hr₀ hr₁) a ha
    (isContinuous_closedDiscGaussValuationAbove hr₀ hr₁)
    (Fin.forall_fin_one.2 (closedDiscGaussValuationAbove_weightedX_add_weightedC hr₀ hr₁ har).le)
    (Fin.forall_fin_one.2 (closedDiscGaussValuationAbove_weightedX_add_weightedC hr₀ hr₁
      (c := -a 0) (by rwa [norm_neg])).le)
    (valuation_monomial_le_of_forall_pow
      (closedDiscGaussValuationAbove_weightedC_mul_weightedX_pow_le hr₀ hr₁)) f

/-- **The Gauss valuation just below `r` is invariant under translation by `c` with
`‖c‖ < r`**: `f(T)` and `f(T + c)` have the same Gauss norm of radius `r` and the same first degree
attaining it. Here `c` is the sole entry `a 0` of the tuple `a`. Translation by `c` with
`‖c‖ = r` moves the first degree: `T` attains its Gauss norm first in degree `1`, and `T + c` in
degree `0`. -/
theorem closedDiscGaussValuationBelow_taylorHom (hr₀ : 0 < r) (hr₁ : r ≤ 1) (a : Fin 1 → R)
    (ha : ∀ i, IsPowerBounded (a i)) (har : ‖a 0‖ < r)
    (f : weightedRestrictedSubring (fun _ : Fin 1 ↦ ({1} : Set R)) isWeightFamily_one_weight) :
    closedDiscGaussValuationBelow hr₀ hr₁ (taylorHom a ha f) =
      closedDiscGaussValuationBelow hr₀ hr₁ f :=
  valuation_taylorHom_eq (Γ₀ := WithZero (ℝ≥0ˣ ×ₗ Multiplicative ℤ))
    (v := closedDiscGaussValuationBelow hr₀ hr₁) a ha
    (isContinuous_closedDiscGaussValuationBelow hr₀ hr₁)
    (Fin.forall_fin_one.2 (closedDiscGaussValuationBelow_weightedX_add_weightedC hr₀ hr₁ har).le)
    (Fin.forall_fin_one.2 (closedDiscGaussValuationBelow_weightedX_add_weightedC hr₀ hr₁
      (c := -a 0) (by rwa [norm_neg])).le)
    (valuation_monomial_le_of_forall_pow
      (closedDiscGaussValuationBelow_weightedC_mul_weightedX_pow_le hr₀ hr₁)) f

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
  Homeomorph.setCongr (closedPolydisc_def 1 K).symm <|
    spaComap (taylorHom (fun _ ↦ a) (fun _ ↦ isPowerBounded_iff_norm_le_one.mpr ha))
      (continuous_taylorHom _ _) _ _ (fun _ hf ↦ taylorHom_mem_powerBoundedSubring _ _ hf)
      (Homeomorph.setCongr (closedPolydisc_def 1 K) (gaussPoint hr₀ hr₁))

/-- The underlying point in `Spv K⟨T⟩` is the pullback of the Gauss point `η_r` along the
translation `T ↦ T + a`. -/
theorem discPoint_val (a : K) (ha : ‖a‖ ≤ 1) (hr₀ : 0 < r) (hr₁ : r ≤ 1) :
    (discPoint a ha hr₀ hr₁).1 =
      comap (taylorHom (fun _ ↦ a) (fun _ ↦ isPowerBounded_iff_norm_le_one.mpr ha))
        (gaussPoint hr₀ hr₁).1 :=
  spaComap_val _ _ _ _ _ _

/-- The point `η_{a,r}` compares `f` and `g` by the Gauss norms of radius `r` of `f(T + a)` and
`g(T + a)`. -/
@[simp]
theorem discPoint_vle_iff (a : K) (ha : ‖a‖ ≤ 1) (hr₀ : 0 < r) (hr₁ : r ≤ 1)
    (f g : weightedRestrictedSubring (fun _ : Fin 1 ↦ ({1} : Set K)) isWeightFamily_one_weight) :
    (discPoint a ha hr₀ hr₁).1.toValuativeRel.vle f g ↔
      closedDiscGaussValuation hr₀ hr₁
          (taylorHom (fun _ ↦ a) (fun _ ↦ isPowerBounded_iff_norm_le_one.mpr ha) f) ≤
        closedDiscGaussValuation hr₀ hr₁
          (taylorHom (fun _ ↦ a) (fun _ ↦ isPowerBounded_iff_norm_le_one.mpr ha) g) := by
  rw [discPoint_val, comap_vle, gaussPoint_vle_iff]

/-- The Gauss norm of radius `r` about `a` takes the value `max r ‖b - a‖` on `T - b`: this is the
value of `η_{a,r}` on `T - b`. -/
theorem coe_closedDiscGaussValuation_taylorHom_weightedX_sub_weightedC {a : K} (ha : ‖a‖ ≤ 1)
    (hr₀ : 0 < r) (hr₁ : r ≤ 1) (b : K) :
    (closedDiscGaussValuation hr₀ hr₁
      (taylorHom (fun _ ↦ a) (fun _ ↦ isPowerBounded_iff_norm_le_one.mpr ha)
        (weightedX (fun _ : Fin 1 ↦ ({1} : Set K)) isWeightFamily_one_weight 0 -
          weightedC _ isWeightFamily_one_weight b)) : ℝ) =
      max r ‖b - a‖ := by
  have h : weightedX (fun _ : Fin 1 ↦ ({1} : Set K)) isWeightFamily_one_weight 0 +
      weightedC _ isWeightFamily_one_weight a - weightedC _ isWeightFamily_one_weight b =
      weightedX _ isWeightFamily_one_weight 0 - weightedC _ isWeightFamily_one_weight (b - a) := by
    rw [map_sub]
    ring
  rw [map_sub, taylorHom_weightedX, taylorHom_weightedC, h,
    coe_closedDiscGaussValuation_weightedX_sub_weightedC]

/-- **About the origin, `η_{0,r}` is the Gauss point `η_r`.** -/
@[simp]
theorem discPoint_zero (ha : ‖(0 : K)‖ ≤ 1) (hr₀ : 0 < r) (hr₁ : r ≤ 1) :
    discPoint 0 ha hr₀ hr₁ = gaussPoint hr₀ hr₁ := by
  -- translation by the zero tuple is the identity
  have h0 : taylorHom (fun _ : Fin 1 ↦ (0 : K))
      (fun _ ↦ isPowerBounded_iff_norm_le_one.mpr ha) = RingHom.id _ :=
    taylorHom_zero
  exact Subtype.ext (by rw [discPoint_val, h0, comap_id, id])

/-- **Translating recentres `η_{c,r}`**: pulling `η_{c,r}` back along the translation
`T ↦ T + b` gives `η_{c+b,r}`, since translations compose additively. -/
theorem comap_taylorHom_discPoint {b c : K} (hb : ‖b‖ ≤ 1) (hc : ‖c‖ ≤ 1) (hcb : ‖c + b‖ ≤ 1)
    (hr₀ : 0 < r) (hr₁ : r ≤ 1) :
    comap (taylorHom (fun _ ↦ b) fun _ ↦ isPowerBounded_iff_norm_le_one.mpr hb)
        (discPoint c hc hr₀ hr₁).1 = (discPoint (c + b) hcb hr₀ hr₁).1 := by
  rw [discPoint_val, discPoint_val, ← Function.comp_apply (f := comap _), ← comap_comp,
    taylorHom_comp_taylorHom]
  -- the tuple `(fun _ ↦ c) + (fun _ ↦ b)` is `fun _ ↦ c + b` by definition of `Pi.add`
  rfl

/-- **Recentring within the disc**: `η_{a,r} = η_r` whenever `‖a‖ ≤ r`, by translation invariance
of the Gauss norm of radius `r`. -/
theorem discPoint_eq_gaussPoint_of_norm_le {a : K} (ha : ‖a‖ ≤ 1) (hr₀ : 0 < r)
    (hr₁ : r ≤ 1) (har : ‖a‖ ≤ r) : discPoint a ha hr₀ hr₁ = gaussPoint hr₀ hr₁ :=
  Subtype.ext <| ext' fun f g ↦ by
    rw [discPoint_vle_iff, gaussPoint_vle_iff, closedDiscGaussValuation_taylorHom _ _ _ _ har,
      closedDiscGaussValuation_taylorHom _ _ _ _ har]

/-- **`η_{a,r}` is the Gauss point `η_s` exactly when `r = s` and `‖a‖ ≤ r`.** If `‖a‖ > r`, then
`η_{a,r}` finds `T - a` strictly smaller than the constant `a`, while every Gauss point about the
origin finds it at least as large. -/
theorem discPoint_eq_gaussPoint_iff {a : K} (ha : ‖a‖ ≤ 1) (hr₀ : 0 < r) (hr₁ : r ≤ 1)
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
    -- the Gauss norm of radius `s` of `T - a` is `max s ‖a‖ ≥ ‖a‖`
    simp only [discPoint_vle_iff, gaussPoint_vle_iff, taylorHom_weightedC, map_sub,
      taylorHom_weightedX, add_sub_cancel_right, eq_iff_iff, ← NNReal.coe_le_coe,
      closedDiscGaussValuation_weightedC, coe_closedDiscGaussValuation_weightedX,
      coe_closedDiscGaussValuation_weightedX_sub_weightedC, coe_nnnorm] at key
    exact (key.mpr (le_max_right _ _)).not_gt hlt
  refine ⟨?_, har⟩
  rw [discPoint_eq_gaussPoint_of_norm_le ha hr₀ hr₁ har] at h
  exact (gaussPoint_inj hr₀ hr₁ hs₀ hs₁).mp h

/-- **`η_{a,r}` depends only on the disc `D(a, r)`**: `η_{a,r} = η_{b,s}` if and only if `r = s`
and `‖a - b‖ ≤ r`, that is, the radii agree and each centre lies in the other's disc. -/
theorem discPoint_eq_discPoint_iff {a b : K} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) (hr₀ : 0 < r)
    (hr₁ : r ≤ 1) (hs₀ : 0 < s) (hs₁ : s ≤ 1) :
    discPoint a ha hr₀ hr₁ = discPoint b hb hs₀ hs₁ ↔ r = s ∧ ‖a - b‖ ≤ r := by
  have hb' : ‖-b‖ ≤ 1 := by rwa [norm_neg]
  have hab : ‖a + -b‖ ≤ 1 :=
    (IsUltrametricDist.norm_add_le_max a (-b)).trans (max_le ha hb')
  rw [← sub_eq_add_neg] at hab
  -- pulling back along translation by `-b` is injective, and carries `η_{c,t}` to `η_{c - b,t}`
  rw [← discPoint_eq_gaussPoint_iff hab hr₀ hr₁ hs₀ hs₁, Subtype.ext_iff, Subtype.ext_iff,
    ← (comap_injective (taylorHom_surjective (fun _ : Fin 1 ↦ -b)
      fun _ ↦ isPowerBounded_iff_norm_le_one.mpr hb')).eq_iff,
    comap_taylorHom_discPoint hb' ha (by rwa [← sub_eq_add_neg]),
    comap_taylorHom_discPoint hb' hb (by simp), ← Subtype.ext_iff, ← Subtype.ext_iff]
  simp only [← sub_eq_add_neg, sub_self, discPoint_zero]

/-- **At radius one every centre gives the Gauss point of the disc**: `D(a, 1)` is the whole
closed unit disc. -/
theorem discPoint_radius_one (a : K) (ha : ‖a‖ ≤ 1) :
    discPoint a ha zero_lt_one le_rfl = gaussPoint (K := K) zero_lt_one le_rfl :=
  discPoint_eq_gaussPoint_of_norm_le ha zero_lt_one le_rfl ha

/-- A point `η_{a,r}` kills only the zero series. -/
theorem discPoint_vle_zero_iff (a : K) (ha : ‖a‖ ≤ 1) (hr₀ : 0 < r) (hr₁ : r ≤ 1)
    {f : weightedRestrictedSubring (fun _ : Fin 1 ↦ ({1} : Set K)) isWeightFamily_one_weight} :
    (discPoint a ha hr₀ hr₁).1.toValuativeRel.vle f 0 ↔ f = 0 := by
  rw [discPoint_val, comap_vle, map_zero, gaussPoint_vle_zero_iff,
    map_eq_zero_iff _ (taylorHom_injective _ _)]

/-- **The support of `η_{a,r}` is trivial.** -/
@[simp]
theorem supp_discPoint (a : K) (ha : ‖a‖ ≤ 1) (hr₀ : 0 < r) (hr₁ : r ≤ 1) :
    (discPoint a ha hr₀ hr₁).1.supp = ⊥ :=
  Ideal.ext fun _ ↦ by rw [mem_supp_iff, discPoint_vle_zero_iff, Ideal.mem_bot]

/-- **The points `η_{a,r}` are not classical points.** -/
theorem discPoint_ne_classicalPoint (a : K) (ha : ‖a‖ ≤ 1) (hr₀ : 0 < r) (hr₁ : r ≤ 1)
    (x : spa (powerBoundedSubring K)) (b : Fin 1 → K) (hb : ∀ i, IsPowerBounded (b i)) :
    discPoint a ha hr₀ hr₁ ≠ classicalPoint x b hb :=
  ne_classicalPoint_of_supp_eq_bot _ (supp_discPoint a ha hr₀ hr₁) x b hb

/-! ### The points `η_{a,r⁺}` and `η_{a,r⁻}` -/

/-- **The point `η_{a,r⁺}` of the closed unit disc**, for a centre `‖a‖ ≤ 1` and a radius
`0 < r < 1`: the Gauss valuation just above `r` about `a`, `f ↦ (|f|_r, s)` with `s` the last degree
in which `f(T + a)` attains its Gauss norm `|f|_r`. It is the pullback of `η_{r⁺}` along the
translation `T ↦ T + a`. -/
noncomputable def discPointAbove (a : K) (ha : ‖a‖ ≤ 1) (hr₀ : 0 < r) (hr₁ : r < 1) :
    closedPolydisc 1 K :=
  Homeomorph.setCongr (closedPolydisc_def 1 K).symm <|
    spaComap (taylorHom (fun _ ↦ a) (fun _ ↦ isPowerBounded_iff_norm_le_one.mpr ha))
      (continuous_taylorHom _ _) _ _ (fun _ hf ↦ taylorHom_mem_powerBoundedSubring _ _ hf)
      (Homeomorph.setCongr (closedPolydisc_def 1 K) (gaussPointAbove hr₀ hr₁))

/-- **The point `η_{a,r⁻}` of the closed unit disc**, for a centre `‖a‖ ≤ 1` and a radius
`0 < r ≤ 1`: the Gauss valuation just below `r` about `a`, `f ↦ (|f|_r, -s)` with `s` the first
degree in which `f(T + a)` attains its Gauss norm `|f|_r`. It is the pullback of `η_{r⁻}` along the
translation `T ↦ T + a`. -/
noncomputable def discPointBelow (a : K) (ha : ‖a‖ ≤ 1) (hr₀ : 0 < r) (hr₁ : r ≤ 1) :
    closedPolydisc 1 K :=
  Homeomorph.setCongr (closedPolydisc_def 1 K).symm <|
    spaComap (taylorHom (fun _ ↦ a) (fun _ ↦ isPowerBounded_iff_norm_le_one.mpr ha))
      (continuous_taylorHom _ _) _ _ (fun _ hf ↦ taylorHom_mem_powerBoundedSubring _ _ hf)
      (Homeomorph.setCongr (closedPolydisc_def 1 K) (gaussPointBelow hr₀ hr₁))

/-- The underlying point of `η_{a,r⁺}` in `Spv K⟨T⟩` is the pullback of `η_{r⁺}` along the
translation `T ↦ T + a`. -/
theorem discPointAbove_val (a : K) (ha : ‖a‖ ≤ 1) (hr₀ : 0 < r) (hr₁ : r < 1) :
    (discPointAbove a ha hr₀ hr₁).1 =
      comap (taylorHom (fun _ ↦ a) (fun _ ↦ isPowerBounded_iff_norm_le_one.mpr ha))
        (gaussPointAbove hr₀ hr₁).1 :=
  spaComap_val _ _ _ _ _ _

/-- The underlying point of `η_{a,r⁻}` in `Spv K⟨T⟩` is the pullback of `η_{r⁻}` along the
translation `T ↦ T + a`. -/
theorem discPointBelow_val (a : K) (ha : ‖a‖ ≤ 1) (hr₀ : 0 < r) (hr₁ : r ≤ 1) :
    (discPointBelow a ha hr₀ hr₁).1 =
      comap (taylorHom (fun _ ↦ a) (fun _ ↦ isPowerBounded_iff_norm_le_one.mpr ha))
        (gaussPointBelow hr₀ hr₁).1 :=
  spaComap_val _ _ _ _ _ _

/-- The point `η_{a,r⁺}` compares `f` and `g` by the Gauss valuations just above `r` of
`f(T + a)` and `g(T + a)`. -/
@[simp]
theorem discPointAbove_vle_iff (a : K) (ha : ‖a‖ ≤ 1) (hr₀ : 0 < r) (hr₁ : r < 1)
    (f g : weightedRestrictedSubring (fun _ : Fin 1 ↦ ({1} : Set K)) isWeightFamily_one_weight) :
    (discPointAbove a ha hr₀ hr₁).1.toValuativeRel.vle f g ↔
      closedDiscGaussValuationAbove hr₀ hr₁.le
          (taylorHom (fun _ ↦ a) (fun _ ↦ isPowerBounded_iff_norm_le_one.mpr ha) f) ≤
        closedDiscGaussValuationAbove hr₀ hr₁.le
          (taylorHom (fun _ ↦ a) (fun _ ↦ isPowerBounded_iff_norm_le_one.mpr ha) g) := by
  rw [discPointAbove_val, comap_vle, gaussPointAbove_vle_iff]

/-- The point `η_{a,r⁻}` compares `f` and `g` by the Gauss valuations just below `r` of
`f(T + a)` and `g(T + a)`. -/
@[simp]
theorem discPointBelow_vle_iff (a : K) (ha : ‖a‖ ≤ 1) (hr₀ : 0 < r) (hr₁ : r ≤ 1)
    (f g : weightedRestrictedSubring (fun _ : Fin 1 ↦ ({1} : Set K)) isWeightFamily_one_weight) :
    (discPointBelow a ha hr₀ hr₁).1.toValuativeRel.vle f g ↔
      closedDiscGaussValuationBelow hr₀ hr₁
          (taylorHom (fun _ ↦ a) (fun _ ↦ isPowerBounded_iff_norm_le_one.mpr ha) f) ≤
        closedDiscGaussValuationBelow hr₀ hr₁
          (taylorHom (fun _ ↦ a) (fun _ ↦ isPowerBounded_iff_norm_le_one.mpr ha) g) := by
  rw [discPointBelow_val, comap_vle, gaussPointBelow_vle_iff]

/-- **About the origin, `η_{0,r⁺}` is `η_{r⁺}`.** -/
@[simp]
theorem discPointAbove_zero (ha : ‖(0 : K)‖ ≤ 1) (hr₀ : 0 < r) (hr₁ : r < 1) :
    discPointAbove 0 ha hr₀ hr₁ = gaussPointAbove hr₀ hr₁ := by
  -- translation by the zero tuple is the identity
  have h0 : taylorHom (fun _ : Fin 1 ↦ (0 : K))
      (fun _ ↦ isPowerBounded_iff_norm_le_one.mpr ha) = RingHom.id _ :=
    taylorHom_zero
  exact Subtype.ext (by rw [discPointAbove_val, h0, comap_id, id])

/-- **About the origin, `η_{0,r⁻}` is `η_{r⁻}`.** -/
@[simp]
theorem discPointBelow_zero (ha : ‖(0 : K)‖ ≤ 1) (hr₀ : 0 < r) (hr₁ : r ≤ 1) :
    discPointBelow 0 ha hr₀ hr₁ = gaussPointBelow hr₀ hr₁ := by
  -- translation by the zero tuple is the identity
  have h0 : taylorHom (fun _ : Fin 1 ↦ (0 : K))
      (fun _ ↦ isPowerBounded_iff_norm_le_one.mpr ha) = RingHom.id _ :=
    taylorHom_zero
  exact Subtype.ext (by rw [discPointBelow_val, h0, comap_id, id])

/-- **`η_{a,r⁺}` finds `T - a` at most a constant `c` exactly when `r < ‖c‖`**: the value of
`T - a` lies just above the constants of norm `r`. -/
theorem discPointAbove_vle_weightedC_iff (a : K) (ha : ‖a‖ ≤ 1) (hr₀ : 0 < r) (hr₁ : r < 1)
    (c : K) :
    (discPointAbove a ha hr₀ hr₁).1.toValuativeRel.vle
        (weightedX (fun _ : Fin 1 ↦ ({1} : Set K)) isWeightFamily_one_weight 0 -
          weightedC _ isWeightFamily_one_weight a) (weightedC _ isWeightFamily_one_weight c) ↔
      r < ‖c‖ := by
  rw [discPointAbove_vle_iff, map_sub, taylorHom_weightedX, taylorHom_weightedC,
    taylorHom_weightedC, add_sub_cancel_right]
  exact closedDiscGaussValuationAbove_weightedX_le_iff hr₀ hr₁.le c

/-- **`η_{a,r⁺}` finds a constant `c` at most `T - a` exactly when `‖c‖ ≤ r`.** -/
theorem discPointAbove_weightedC_vle_iff (a : K) (ha : ‖a‖ ≤ 1) (hr₀ : 0 < r) (hr₁ : r < 1)
    (c : K) :
    (discPointAbove a ha hr₀ hr₁).1.toValuativeRel.vle (weightedC _ isWeightFamily_one_weight c)
        (weightedX (fun _ : Fin 1 ↦ ({1} : Set K)) isWeightFamily_one_weight 0 -
          weightedC _ isWeightFamily_one_weight a) ↔
      ‖c‖ ≤ r := by
  rw [discPointAbove_vle_iff, map_sub, taylorHom_weightedX, taylorHom_weightedC,
    taylorHom_weightedC, add_sub_cancel_right]
  exact closedDiscGaussValuationAbove_weightedC_le_iff hr₀ hr₁.le c

/-- **`η_{a,r⁻}` finds `T - a` at most a constant `c` exactly when `r ≤ ‖c‖`.** -/
theorem discPointBelow_vle_weightedC_iff (a : K) (ha : ‖a‖ ≤ 1) (hr₀ : 0 < r) (hr₁ : r ≤ 1)
    (c : K) :
    (discPointBelow a ha hr₀ hr₁).1.toValuativeRel.vle
        (weightedX (fun _ : Fin 1 ↦ ({1} : Set K)) isWeightFamily_one_weight 0 -
          weightedC _ isWeightFamily_one_weight a) (weightedC _ isWeightFamily_one_weight c) ↔
      r ≤ ‖c‖ := by
  rw [discPointBelow_vle_iff, map_sub, taylorHom_weightedX, taylorHom_weightedC,
    taylorHom_weightedC, add_sub_cancel_right]
  exact closedDiscGaussValuationBelow_weightedX_le_iff hr₀ hr₁ c

/-- **`η_{a,r⁻}` finds a constant `c` at most `T - a` exactly when `‖c‖ < r`**: the value of
`T - a` lies just below the constants of norm `r`. -/
theorem discPointBelow_weightedC_vle_iff (a : K) (ha : ‖a‖ ≤ 1) (hr₀ : 0 < r) (hr₁ : r ≤ 1)
    (c : K) :
    (discPointBelow a ha hr₀ hr₁).1.toValuativeRel.vle (weightedC _ isWeightFamily_one_weight c)
        (weightedX (fun _ : Fin 1 ↦ ({1} : Set K)) isWeightFamily_one_weight 0 -
          weightedC _ isWeightFamily_one_weight a) ↔
      ‖c‖ < r := by
  rw [discPointBelow_vle_iff, map_sub, taylorHom_weightedX, taylorHom_weightedC,
    taylorHom_weightedC, add_sub_cancel_right]
  exact closedDiscGaussValuationBelow_weightedC_le_iff hr₀ hr₁ c

/-- If `x(T - a)` is strictly larger than `x(c)` for the constants with `Q c` and strictly smaller
for the others, then `x(T - b)` is `x(T - a)` when `Q (b - a)` and `x(b - a)` otherwise: write
`T - b = (T - a) - (b - a)` and apply the ultrametric equality. -/
theorem valuation_weightedX_sub_weightedC_of_lt {A : Type*} [CommRing A] [TopologicalSpace A]
    [NonarchimedeanRing A] {x : closedPolydisc 1 A} {a : A}
    (Q : A → Prop) [DecidablePred Q]
    (hlt : ∀ c : A, Q c →
      x.1.valuation (weightedC (fun _ : Fin 1 ↦ ({1} : Set A)) isWeightFamily_one_weight c) <
        x.1.valuation (weightedX (fun _ : Fin 1 ↦ ({1} : Set A)) isWeightFamily_one_weight 0 -
          weightedC _ isWeightFamily_one_weight a))
    (hgt : ∀ c : A, ¬ Q c →
      x.1.valuation (weightedX (fun _ : Fin 1 ↦ ({1} : Set A)) isWeightFamily_one_weight 0 -
          weightedC _ isWeightFamily_one_weight a) <
        x.1.valuation (weightedC (fun _ : Fin 1 ↦ ({1} : Set A)) isWeightFamily_one_weight c))
    (b : A) :
    x.1.valuation (weightedX (fun _ : Fin 1 ↦ ({1} : Set A)) isWeightFamily_one_weight 0 -
        weightedC _ isWeightFamily_one_weight b) =
      if Q (b - a) then
        x.1.valuation (weightedX (fun _ : Fin 1 ↦ ({1} : Set A)) isWeightFamily_one_weight 0 -
          weightedC _ isWeightFamily_one_weight a)
      else x.1.valuation (weightedC _ isWeightFamily_one_weight (b - a)) := by
  have hsplit : weightedX (fun _ : Fin 1 ↦ ({1} : Set A)) isWeightFamily_one_weight 0 -
      weightedC _ isWeightFamily_one_weight b =
      (weightedX _ isWeightFamily_one_weight 0 - weightedC _ isWeightFamily_one_weight a) -
        weightedC _ isWeightFamily_one_weight (b - a) := by
    rw [map_sub]
    ring
  rw [hsplit]
  split_ifs with hb
  · exact Valuation.map_sub_eq_of_lt_left _ (hlt _ hb)
  · exact Valuation.map_sub_eq_of_lt_right _ (hgt _ hb)

/-- **The value of `η_{a,r⁺}` on `T - b`** is its value on `T - a` when `‖b - a‖ ≤ r`, and the
value of the constant `b - a` otherwise: `T - b = (T - a) - (b - a)`, and `T - a` is strictly
larger than the constants of norm at most `r` and strictly smaller than the others. -/
theorem valuation_weightedX_sub_weightedC_discPointAbove (a : K) (ha : ‖a‖ ≤ 1) (hr₀ : 0 < r)
    (hr₁ : r < 1) (b : K) :
    (discPointAbove a ha hr₀ hr₁).1.valuation
        (weightedX (fun _ : Fin 1 ↦ ({1} : Set K)) isWeightFamily_one_weight 0 -
          weightedC _ isWeightFamily_one_weight b) =
      if ‖b - a‖ ≤ r then
        (discPointAbove a ha hr₀ hr₁).1.valuation
          (weightedX (fun _ : Fin 1 ↦ ({1} : Set K)) isWeightFamily_one_weight 0 -
            weightedC _ isWeightFamily_one_weight a)
      else
        (discPointAbove a ha hr₀ hr₁).1.valuation
          (weightedC _ isWeightFamily_one_weight (b - a)) := by
  exact valuation_weightedX_sub_weightedC_of_lt (fun c ↦ ‖c‖ ≤ r)
    (fun c hc ↦ lt_of_not_ge fun h ↦
      ((discPointAbove_vle_weightedC_iff a ha hr₀ hr₁ c).mp ((valuation_le_iff _ _ _).mp h)).not_ge
        hc)
    (fun c hc ↦ lt_of_not_ge fun h ↦
      hc ((discPointAbove_weightedC_vle_iff a ha hr₀ hr₁ c).mp ((valuation_le_iff _ _ _).mp h))) b

/-- **The value of `η_{a,r⁻}` on `T - b`** is its value on `T - a` when `‖b - a‖ < r`, and the
value of the constant `b - a` otherwise: `T - b = (T - a) - (b - a)`, and `T - a` is strictly
larger than the constants of norm less than `r` and strictly smaller than the others. -/
theorem valuation_weightedX_sub_weightedC_discPointBelow (a : K) (ha : ‖a‖ ≤ 1) (hr₀ : 0 < r)
    (hr₁ : r ≤ 1) (b : K) :
    (discPointBelow a ha hr₀ hr₁).1.valuation
        (weightedX (fun _ : Fin 1 ↦ ({1} : Set K)) isWeightFamily_one_weight 0 -
          weightedC _ isWeightFamily_one_weight b) =
      if ‖b - a‖ < r then
        (discPointBelow a ha hr₀ hr₁).1.valuation
          (weightedX (fun _ : Fin 1 ↦ ({1} : Set K)) isWeightFamily_one_weight 0 -
            weightedC _ isWeightFamily_one_weight a)
      else
        (discPointBelow a ha hr₀ hr₁).1.valuation
          (weightedC _ isWeightFamily_one_weight (b - a)) := by
  exact valuation_weightedX_sub_weightedC_of_lt (fun c ↦ ‖c‖ < r)
    (fun c hc ↦ lt_of_not_ge fun h ↦
      ((discPointBelow_vle_weightedC_iff a ha hr₀ hr₁ c).mp ((valuation_le_iff _ _ _).mp h)).not_gt
        hc)
    (fun c hc ↦ lt_of_not_ge fun h ↦
      hc ((discPointBelow_weightedC_vle_iff a ha hr₀ hr₁ c).mp ((valuation_le_iff _ _ _).mp h))) b

/-- **Translating recentres `η_{c,r⁺}`**: pulling `η_{c,r⁺}` back along the translation
`T ↦ T + b` gives `η_{c+b,r⁺}`. -/
theorem comap_taylorHom_discPointAbove {b c : K} (hb : ‖b‖ ≤ 1) (hc : ‖c‖ ≤ 1)
    (hcb : ‖c + b‖ ≤ 1) (hr₀ : 0 < r) (hr₁ : r < 1) :
    comap (taylorHom (fun _ ↦ b) fun _ ↦ isPowerBounded_iff_norm_le_one.mpr hb)
        (discPointAbove c hc hr₀ hr₁).1 = (discPointAbove (c + b) hcb hr₀ hr₁).1 := by
  rw [discPointAbove_val, discPointAbove_val, ← Function.comp_apply (f := comap _), ← comap_comp,
    taylorHom_comp_taylorHom]
  -- the tuple `(fun _ ↦ c) + (fun _ ↦ b)` is `fun _ ↦ c + b` by definition of `Pi.add`
  rfl

/-- **Translating recentres `η_{c,r⁻}`**: pulling `η_{c,r⁻}` back along the translation
`T ↦ T + b` gives `η_{c+b,r⁻}`. -/
theorem comap_taylorHom_discPointBelow {b c : K} (hb : ‖b‖ ≤ 1) (hc : ‖c‖ ≤ 1)
    (hcb : ‖c + b‖ ≤ 1) (hr₀ : 0 < r) (hr₁ : r ≤ 1) :
    comap (taylorHom (fun _ ↦ b) fun _ ↦ isPowerBounded_iff_norm_le_one.mpr hb)
        (discPointBelow c hc hr₀ hr₁).1 = (discPointBelow (c + b) hcb hr₀ hr₁).1 := by
  rw [discPointBelow_val, discPointBelow_val, ← Function.comp_apply (f := comap _), ← comap_comp,
    taylorHom_comp_taylorHom]
  -- the tuple `(fun _ ↦ c) + (fun _ ↦ b)` is `fun _ ↦ c + b` by definition of `Pi.add`
  rfl

/-- **`η_{a,r⁺}` is `η_{s⁺}` exactly when `r = s` and `‖a‖ ≤ r`.** If `‖a‖ > r`, then `η_{a,r⁺}`
finds `T - a` strictly smaller than the constant `a`, while `η_{s⁺}` finds `a`, a monomial of
`T - a`, at most `T - a`. -/
theorem discPointAbove_eq_gaussPointAbove_iff {a : K} (ha : ‖a‖ ≤ 1) (hr₀ : 0 < r)
    (hr₁ : r < 1) (hs₀ : 0 < s) (hs₁ : s < 1) :
    discPointAbove a ha hr₀ hr₁ = gaussPointAbove hs₀ hs₁ ↔ r = s ∧ ‖a‖ ≤ r := by
  -- recentring within the disc, by translation invariance just above `r`
  have hrec (har : ‖a‖ ≤ r) : discPointAbove a ha hr₀ hr₁ = gaussPointAbove hr₀ hr₁ :=
    Subtype.ext <| ext' fun f g ↦ by
      rw [discPointAbove_vle_iff, gaussPointAbove_vle_iff,
        closedDiscGaussValuationAbove_taylorHom _ _ _ _ har,
        closedDiscGaussValuationAbove_taylorHom _ _ _ _ har]
  constructor
  swap
  · rintro ⟨rfl, har⟩
    exact hrec har
  intro h
  have har : ‖a‖ ≤ r := by
    by_contra! hlt
    have key := congrArg (fun p : closedPolydisc 1 K ↦ p.1.toValuativeRel.vle
      (weightedC _ isWeightFamily_one_weight a)
      (weightedX (fun _ : Fin 1 ↦ ({1} : Set K)) isWeightFamily_one_weight 0 -
        weightedC _ isWeightFamily_one_weight a)) h
    simp only [discPointAbove_vle_iff, gaussPointAbove_vle_iff, taylorHom_weightedC, map_sub,
      taylorHom_weightedX, add_sub_cancel_right, eq_iff_iff] at key
    have hmono := closedDiscGaussValuationAbove_weightedC_mul_weightedX_pow_le hs₀ hs₁.le
      (weightedX (fun _ : Fin 1 ↦ ({1} : Set K)) isWeightFamily_one_weight 0 -
        weightedC _ isWeightFamily_one_weight a) 0
    -- the degree-`0` monomial of `T - a` is the constant `-a`, which has the value of `a`
    simp only [Finsupp.single_zero, AddSubgroupClass.coe_sub, coe_weightedX, coe_weightedC,
      MvPowerSeries.coeff_zero_eq_constantCoeff, map_sub, MvPowerSeries.constantCoeff_X,
      MvPowerSeries.constantCoeff_C, zero_sub, map_neg, pow_zero, mul_one,
      Valuation.map_neg] at hmono
    -- about `a`, the variable `T` has Gauss norm `r < ‖a‖`, so it is strictly smaller than `a`
    refine (closedDiscGaussValuationAbove_lt_of_lt hr₀ hr₁.le ?_).not_ge (key.mpr hmono)
    rw [← NNReal.coe_lt_coe, coe_closedDiscGaussValuation_weightedX,
      closedDiscGaussValuation_weightedC, coe_nnnorm]
    exact hlt
  exact ⟨(gaussPointAbove_inj hr₀ hr₁ hs₀ hs₁).mp ((hrec har).symm.trans h), har⟩

/-- **`η_{a,r⁻}` is `η_{s⁻}` exactly when `r = s` and `‖a‖ < r`.** If `‖a‖ ≥ r`, then `η_{a,r⁻}`
finds `T - a` strictly smaller than the constant `a`, while `η_{s⁻}` finds `a`, a monomial of
`T - a`, at most `T - a`. -/
theorem discPointBelow_eq_gaussPointBelow_iff {a : K} (ha : ‖a‖ ≤ 1) (hr₀ : 0 < r)
    (hr₁ : r ≤ 1) (hs₀ : 0 < s) (hs₁ : s ≤ 1) :
    discPointBelow a ha hr₀ hr₁ = gaussPointBelow hs₀ hs₁ ↔ r = s ∧ ‖a‖ < r := by
  -- recentring within the open disc, by translation invariance just below `r`
  have hrec (har : ‖a‖ < r) : discPointBelow a ha hr₀ hr₁ = gaussPointBelow hr₀ hr₁ :=
    Subtype.ext <| ext' fun f g ↦ by
      rw [discPointBelow_vle_iff, gaussPointBelow_vle_iff,
        closedDiscGaussValuationBelow_taylorHom _ _ _ _ har,
        closedDiscGaussValuationBelow_taylorHom _ _ _ _ har]
  constructor
  swap
  · rintro ⟨rfl, har⟩
    exact hrec har
  intro h
  have har : ‖a‖ < r := by
    by_contra! hle
    have key := congrArg (fun p : closedPolydisc 1 K ↦ p.1.toValuativeRel.vle
      (weightedC _ isWeightFamily_one_weight a)
      (weightedX (fun _ : Fin 1 ↦ ({1} : Set K)) isWeightFamily_one_weight 0 -
        weightedC _ isWeightFamily_one_weight a)) h
    simp only [discPointBelow_vle_iff, gaussPointBelow_vle_iff, taylorHom_weightedC, map_sub,
      taylorHom_weightedX, add_sub_cancel_right, eq_iff_iff] at key
    have hmono := closedDiscGaussValuationBelow_weightedC_mul_weightedX_pow_le hs₀ hs₁
      (weightedX (fun _ : Fin 1 ↦ ({1} : Set K)) isWeightFamily_one_weight 0 -
        weightedC _ isWeightFamily_one_weight a) 0
    -- the degree-`0` monomial of `T - a` is the constant `-a`, which has the value of `a`
    simp only [Finsupp.single_zero, AddSubgroupClass.coe_sub, coe_weightedX, coe_weightedC,
      MvPowerSeries.coeff_zero_eq_constantCoeff, map_sub, MvPowerSeries.constantCoeff_X,
      MvPowerSeries.constantCoeff_C, zero_sub, map_neg, pow_zero, mul_one,
      Valuation.map_neg] at hmono
    -- about `a`, the constant `a` of norm at least `r` is strictly larger than `T` just below `r`
    rcases hle.lt_or_eq with hlt | heq
    · refine (closedDiscGaussValuationBelow_lt_of_lt hr₀ hr₁ ?_).not_ge (key.mpr hmono)
      rw [← NNReal.coe_lt_coe, coe_closedDiscGaussValuation_weightedX,
        closedDiscGaussValuation_weightedC, coe_nnnorm]
      exact hlt
    · exact not_closedDiscGaussValuationBelow_weightedC_le hr₀ hr₁ heq.symm (key.mpr hmono)
  exact ⟨(gaussPointBelow_inj hr₀ hr₁ hs₀ hs₁).mp ((hrec har).symm.trans h), har⟩

/-- **`η_{a,r⁺}` depends only on the closed disc `D(a, r)`**: for `‖a‖, ‖b‖ ≤ 1`,
`η_{a,r⁺} = η_{b,s⁺}` if and only if `r = s` and `‖a - b‖ ≤ r`, that is, if and only if
`η_{a,r} = η_{b,s}` (`TauCeti.ValuationSpectrum.discPoint_eq_discPoint_iff`). -/
theorem discPointAbove_eq_discPointAbove_iff {a b : K} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1)
    (hr₀ : 0 < r) (hr₁ : r < 1) (hs₀ : 0 < s) (hs₁ : s < 1) :
    discPointAbove a ha hr₀ hr₁ = discPointAbove b hb hs₀ hs₁ ↔ r = s ∧ ‖a - b‖ ≤ r := by
  have hb' : ‖-b‖ ≤ 1 := by rwa [norm_neg]
  have hab : ‖a + -b‖ ≤ 1 :=
    (IsUltrametricDist.norm_add_le_max a (-b)).trans (max_le ha hb')
  rw [← sub_eq_add_neg] at hab
  -- pulling back along translation by `-b` is injective, and carries `η_{c,r⁺}` to `η_{c - b,r⁺}`
  rw [← discPointAbove_eq_gaussPointAbove_iff hab hr₀ hr₁ hs₀ hs₁, Subtype.ext_iff, Subtype.ext_iff,
    ← (comap_injective (taylorHom_surjective (fun _ : Fin 1 ↦ -b)
      fun _ ↦ isPowerBounded_iff_norm_le_one.mpr hb')).eq_iff,
    comap_taylorHom_discPointAbove hb' ha (by rwa [← sub_eq_add_neg]),
    comap_taylorHom_discPointAbove hb' hb (by simp), ← Subtype.ext_iff, ← Subtype.ext_iff]
  simp only [← sub_eq_add_neg, sub_self, discPointAbove_zero]

/-- **`η_{a,r⁻}` depends only on the open disc `D°(a, r)`**: for `‖a‖, ‖b‖ ≤ 1`,
`η_{a,r⁻} = η_{b,s⁻}` if and only if `r = s` and `‖a - b‖ < r`. So the open discs of radius `r`
inside `D(a, r)` give pairwise distinct points `η_{b,r⁻}`, all specializations of `η_{a,r}`. -/
theorem discPointBelow_eq_discPointBelow_iff {a b : K} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1)
    (hr₀ : 0 < r) (hr₁ : r ≤ 1) (hs₀ : 0 < s) (hs₁ : s ≤ 1) :
    discPointBelow a ha hr₀ hr₁ = discPointBelow b hb hs₀ hs₁ ↔ r = s ∧ ‖a - b‖ < r := by
  have hb' : ‖-b‖ ≤ 1 := by rwa [norm_neg]
  have hab : ‖a + -b‖ ≤ 1 :=
    (IsUltrametricDist.norm_add_le_max a (-b)).trans (max_le ha hb')
  rw [← sub_eq_add_neg] at hab
  -- pulling back along translation by `-b` is injective, and carries `η_{c,r⁻}` to `η_{c - b,r⁻}`
  rw [← discPointBelow_eq_gaussPointBelow_iff hab hr₀ hr₁ hs₀ hs₁, Subtype.ext_iff, Subtype.ext_iff,
    ← (comap_injective (taylorHom_surjective (fun _ : Fin 1 ↦ -b)
      fun _ ↦ isPowerBounded_iff_norm_le_one.mpr hb')).eq_iff,
    comap_taylorHom_discPointBelow hb' ha (by rwa [← sub_eq_add_neg]),
    comap_taylorHom_discPointBelow hb' hb (by simp), ← Subtype.ext_iff, ← Subtype.ext_iff]
  simp only [← sub_eq_add_neg, sub_self, discPointBelow_zero]

/-- **`η_{a,r⁺}` is a specialization of `η_{a,r}`**, as `η_{r⁺}` is of `η_r`: pullback along the
translation is continuous. -/
theorem discPoint_specializes_discPointAbove (a : K) (ha : ‖a‖ ≤ 1) (hr₀ : 0 < r) (hr₁ : r < 1) :
    discPoint a ha hr₀ hr₁.le ⤳ discPointAbove a ha hr₀ hr₁ :=
  (((gaussPoint_specializes_gaussPointAbove hr₀ hr₁).map (Homeomorph.continuous _)).map
    (continuous_spaComap _ _ _ _ _)).map (Homeomorph.continuous _)

/-- **`η_{a,r⁻}` is a specialization of `η_{a,r}`**, as `η_{r⁻}` is of `η_r`: pullback along the
translation is continuous. -/
theorem discPoint_specializes_discPointBelow (a : K) (ha : ‖a‖ ≤ 1) (hr₀ : 0 < r) (hr₁ : r ≤ 1) :
    discPoint a ha hr₀ hr₁ ⤳ discPointBelow a ha hr₀ hr₁ :=
  (((gaussPoint_specializes_gaussPointBelow hr₀ hr₁).map (Homeomorph.continuous _)).map
    (continuous_spaComap _ _ _ _ _)).map (Homeomorph.continuous _)

/-- **`η_{a,r⁺}` is not `η_{a,r}`** when `r` is the norm of an element of `K`. -/
theorem discPointAbove_ne_discPoint (a : K) (ha : ‖a‖ ≤ 1) (hr₀ : 0 < r) (hr₁ : r < 1)
    (hr : ∃ c : K, ‖c‖ = r) : discPointAbove a ha hr₀ hr₁ ≠ discPoint a ha hr₀ hr₁.le := by
  intro h
  have ha' : ‖-a‖ ≤ 1 := by rwa [norm_neg]
  -- pull back along translation by `-a`, which carries both points to the origin
  have hA := comap_taylorHom_discPointAbove ha' ha (by simp) hr₀ hr₁
  rw [h, comap_taylorHom_discPoint ha' ha (by simp)] at hA
  simp only [add_neg_cancel, discPointAbove_zero, discPoint_zero] at hA
  exact gaussPointAbove_ne_gaussPoint hr₀ hr₁ hr (Subtype.ext hA.symm)

/-- **`η_{a,r⁻}` is not `η_{a,r}`** when `r` is the norm of an element of `K`. -/
theorem discPointBelow_ne_discPoint (a : K) (ha : ‖a‖ ≤ 1) (hr₀ : 0 < r) (hr₁ : r ≤ 1)
    (hr : ∃ c : K, ‖c‖ = r) : discPointBelow a ha hr₀ hr₁ ≠ discPoint a ha hr₀ hr₁ := by
  intro h
  have ha' : ‖-a‖ ≤ 1 := by rwa [norm_neg]
  -- pull back along translation by `-a`, which carries both points to the origin
  have hB := comap_taylorHom_discPointBelow ha' ha (by simp) hr₀ hr₁
  rw [h, comap_taylorHom_discPoint ha' ha (by simp)] at hB
  simp only [add_neg_cancel, discPointBelow_zero, discPoint_zero] at hB
  exact gaussPointBelow_ne_gaussPoint hr₀ hr₁ hr (Subtype.ext hB.symm)

/-- **`η_{a,r⁻}` and `η_{a,r⁺}` are distinct** when `r` is the norm of an element of `K`. -/
theorem discPointBelow_ne_discPointAbove (a : K) (ha : ‖a‖ ≤ 1) (hr₀ : 0 < r) (hr₁ : r < 1)
    (hr : ∃ c : K, ‖c‖ = r) : discPointBelow a ha hr₀ hr₁.le ≠ discPointAbove a ha hr₀ hr₁ := by
  intro h
  have ha' : ‖-a‖ ≤ 1 := by rwa [norm_neg]
  -- pull back along translation by `-a`, which carries both points to the origin
  have hB := comap_taylorHom_discPointBelow ha' ha (by simp) hr₀ hr₁.le
  rw [h, comap_taylorHom_discPointAbove ha' ha (by simp)] at hB
  simp only [add_neg_cancel, discPointBelow_zero, discPointAbove_zero] at hB
  exact gaussPointBelow_ne_gaussPointAbove hr₀ hr₁ hr (Subtype.ext hB.symm)

/-- **The support of `η_{a,r⁺}` is trivial.** -/
@[simp]
theorem supp_discPointAbove (a : K) (ha : ‖a‖ ≤ 1) (hr₀ : 0 < r) (hr₁ : r < 1) :
    (discPointAbove a ha hr₀ hr₁).1.supp = ⊥ :=
  Ideal.ext fun _ ↦ by
    rw [mem_supp_iff, discPointAbove_vle_iff, map_zero, map_zero, le_zero_iff,
      closedDiscGaussValuationAbove_eq_zero_iff, map_eq_zero_iff _ (taylorHom_injective _ _),
      Ideal.mem_bot]

/-- **The support of `η_{a,r⁻}` is trivial.** -/
@[simp]
theorem supp_discPointBelow (a : K) (ha : ‖a‖ ≤ 1) (hr₀ : 0 < r) (hr₁ : r ≤ 1) :
    (discPointBelow a ha hr₀ hr₁).1.supp = ⊥ :=
  Ideal.ext fun _ ↦ by
    rw [mem_supp_iff, discPointBelow_vle_iff, map_zero, map_zero, le_zero_iff,
      closedDiscGaussValuationBelow_eq_zero_iff, map_eq_zero_iff _ (taylorHom_injective _ _),
      Ideal.mem_bot]

/-- **The points `η_{a,r⁺}` are not classical points.** -/
theorem discPointAbove_ne_classicalPoint (a : K) (ha : ‖a‖ ≤ 1) (hr₀ : 0 < r) (hr₁ : r < 1)
    (x : spa (powerBoundedSubring K)) (b : Fin 1 → K) (hb : ∀ i, IsPowerBounded (b i)) :
    discPointAbove a ha hr₀ hr₁ ≠ classicalPoint x b hb :=
  ne_classicalPoint_of_supp_eq_bot _ (supp_discPointAbove a ha hr₀ hr₁) x b hb

/-- **The points `η_{a,r⁻}` are not classical points.** -/
theorem discPointBelow_ne_classicalPoint (a : K) (ha : ‖a‖ ≤ 1) (hr₀ : 0 < r) (hr₁ : r ≤ 1)
    (x : spa (powerBoundedSubring K)) (b : Fin 1 → K) (hb : ∀ i, IsPowerBounded (b i)) :
    discPointBelow a ha hr₀ hr₁ ≠ classicalPoint x b hb :=
  ne_classicalPoint_of_supp_eq_bot _ (supp_discPointBelow a ha hr₀ hr₁) x b hb

end TauCeti.ValuationSpectrum
