/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FunctionField.AdjoinTower
public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.InvariantDifferential
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Hom.Ring
public import Mathlib.FieldTheory.RatFunc.IntermediateField

/-!
# The `x`-coordinate of an isogeny is a rational function of `x`

An isogeny `φ : W₁ → W₂` commutes with negation, and negation fixes the affine coordinate `x` of
`W₂`. So the pulled-back coordinate `x ∘ φ` is a function on `W₁` fixed by negation. The functions
fixed by negation are exactly the rational functions of `x`, because `F(W₁)` is a quadratic
extension of `F(x)` on which negation acts nontrivially. Hence `x ∘ φ = r(x)` for a unique rational
function `r`, written `φ.xRatFunc`.

Its degree, the larger of the degrees of its numerator and denominator in lowest terms, is the
degree of `φ`. Indeed `F(W₁)` and the pulled-back copy of `F(W₂)` both have degree two over the
copies of `F(x)` and `F(r)` they contain, and `[F(x) : F(r)]` is the degree of `r`
(`RatFunc.finrank_eq_max_natDegree`).

At a point the rational function computes the action of `φ`: `φ` sends an affine point `(x₀, y₀)`
to the point at infinity exactly when the denominator of `r` vanishes at `x₀`, and otherwise to a
point with `x`-coordinate `r(x₀)`. This is what makes `φ` a morphism of degree `deg φ` on the
`x`-line, the input to the comparison of heights along `φ`.

## Main definitions

* `TauCeti.Isogeny.xRatFunc`: the rational function `r` with `x ∘ φ = r(x)`.

## Main results

* `TauCeti.Isogeny.fieldPullback_negIsogeny_eq_self_iff`: a function is fixed by negation exactly
  when it is a rational function of `x`.
* `TauCeti.Isogeny.negIsogeny_comp`: an isogeny commutes with negation.
* `TauCeti.Isogeny.algebraMap_xRatFunc`: `x ∘ φ = r(x)`, with `eq_xRatFunc_iff` for uniqueness.
* `TauCeti.Isogeny.degree_eq_max_natDegree_xRatFunc`: `deg φ` is the degree of `r`.
* `TauCeti.Isogeny.pointMap_ofIsogeny_some_eq_zero_iff`: `φ` sends `(x₀, y₀)` to the point at
  infinity exactly when the denominator of `r` vanishes at `x₀`.
* `TauCeti.Isogeny.xCoord_pointMap_ofIsogeny_some`: otherwise the image has `x`-coordinate `r(x₀)`.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.4 (isogenies) and the
  proof of III.6.2(d), which computes `deg [m]` as the degree of `x ∘ [m]` in the same way.
-/

public section

open Polynomial IntermediateField WeierstrassCurve.Affine

open scoped RatFunc

namespace TauCeti.Isogeny

variable {F : Type*} [Field F]

section Neg

variable (W : WeierstrassCurve.Affine F) [W.IsElliptic]

/-- **The functions fixed by negation are the rational functions of `x`.** Negation fixes `x`,
hence all of `F(x)`, and does not fix `y`, so its fixed field lies strictly between `F(x)` and
`F(W)`, which has degree two over `F(x)`. -/
theorem fieldPullback_negIsogeny_eq_self_iff {z : W.FunctionField} :
    (negIsogeny W).fieldPullback z = z ↔ z ∈ ratFuncRange W := by
  -- the fixed field of negation
  let S : IntermediateField F W.FunctionField :=
    (AlgHom.equalizer (negIsogeny W).fieldPullback (AlgHom.id F _)).toIntermediateField
      fun w hw ↦ by
        rw [AlgHom.mem_equalizer, AlgHom.id_apply] at hw ⊢
        rw [map_inv₀, hw]
  have hS (w : W.FunctionField) : w ∈ S ↔ (negIsogeny W).fieldPullback w = w :=
    AlgHom.mem_equalizer _ _ w
  have hle : ratFuncRange W ≤ S := by
    rw [ratFuncRange_eq_map, ← RatFunc.adjoin_X, IntermediateField.adjoin_map,
      Set.image_singleton, toAlgHom_ratFuncX, adjoin_simple_le_iff, hS,
      ← genericX_eq_algebraMap]
    exact fieldPullback_negIsogeny_genericX W
  have htop : relfinrank S ⊤ ≠ 1 := by
    rw [Ne, relfinrank_eq_one_iff]
    intro h
    have hy := (hS _).mp (h (mem_top (x := genericY W)))
    refine invariantDifferentialDenom_ne_zero W ?_
    rw [fieldPullback_negIsogeny_genericY] at hy
    simp only [negY, WeierstrassCurve.baseChange, WeierstrassCurve.map_a₁,
      WeierstrassCurve.map_a₃] at hy
    rw [invariantDifferentialDenom_def]
    linear_combination -hy
  have h2 := relfinrank_mul_finrank_top hle
  rw [finrank_ratFuncRange, ← relfinrank_top_right] at h2
  have h1 : relfinrank (ratFuncRange W) S = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp (Dvd.intro_left _ h2) with hb | hb
    · exact absurd hb htop
    · rw [hb] at h2
      omega
  exact ⟨fun hz ↦ relfinrank_eq_one_iff.mp h1 ((hS z).mpr hz), fun hz ↦ (hS z).mp (hle hz)⟩

end Neg

variable {W₁ W₂ : WeierstrassCurve.Affine F} [W₁.IsElliptic] [W₂.IsElliptic]

/-- **An isogeny commutes with negation**: `[-1] ∘ φ = φ ∘ [-1]`. Both sides are `-φ` among the
morphisms, composition being additive in each variable. -/
theorem negIsogeny_comp (φ : Isogeny W₁ W₂) :
    (negIsogeny W₂).comp φ = φ.comp (negIsogeny W₁) := by
  classical
  apply Hom.ofIsogeny_injective
  rw [← Hom.ofIsogeny_comp_ofIsogeny, ← Hom.ofIsogeny_comp_ofIsogeny, ← Hom.neg_def,
    Hom.ofIsogeny_negIsogeny, Hom.comp_neg, Hom.one_def, Hom.comp_id]

/-- **The pulled-back `x`-coordinate is a rational function of `x`**: it is fixed by negation. -/
theorem fieldPullback_genericX_mem_ratFuncRange (φ : Isogeny W₁ W₂) :
    φ.fieldPullback (genericX W₂) ∈ ratFuncRange W₁ := by
  rw [← fieldPullback_negIsogeny_eq_self_iff, ← AlgHom.comp_apply, ← comp_fieldPullback,
    ← negIsogeny_comp, comp_fieldPullback, AlgHom.comp_apply, fieldPullback_negIsogeny_genericX]

/-- **The `x`-coordinate of an isogeny, as a rational function of `x`**: the rational function `r`
with `x ∘ φ = r(x)` (`algebraMap_xRatFunc`), unique by `eq_xRatFunc_iff`. -/
noncomputable def xRatFunc (φ : Isogeny W₁ W₂) : RatFunc F :=
  ((mem_ratFuncRange W₁).mp φ.fieldPullback_genericX_mem_ratFuncRange).choose

/-- **`x ∘ φ = r(x)`** for the rational function `r = φ.xRatFunc`. -/
theorem algebraMap_xRatFunc (φ : Isogeny W₁ W₂) :
    algebraMap (RatFunc F) W₁.FunctionField φ.xRatFunc = φ.fieldPullback (genericX W₂) := by
  rw [← IsScalarTower.toAlgHom_apply F]
  exact ((mem_ratFuncRange W₁).mp φ.fieldPullback_genericX_mem_ratFuncRange).choose_spec

/-- **`φ.xRatFunc` is the only rational function `r` with `x ∘ φ = r(x)`.** -/
theorem eq_xRatFunc_iff {φ : Isogeny W₁ W₂} {r : RatFunc F} :
    r = φ.xRatFunc ↔ algebraMap (RatFunc F) W₁.FunctionField r = φ.fieldPullback (genericX W₂) :=
  ⟨fun h ↦ h ▸ φ.algebraMap_xRatFunc, fun h ↦
    FaithfulSMul.algebraMap_injective (RatFunc F) W₁.FunctionField
      (h.trans φ.algebraMap_xRatFunc.symm)⟩

/-- **The degree of an isogeny is the degree of its `x`-coordinate**, the larger of the degrees of
the numerator and denominator of `φ.xRatFunc` in lowest terms (Silverman, proof of III.6.2(d)). -/
theorem degree_eq_max_natDegree_xRatFunc (φ : Isogeny W₁ W₂) :
    φ.degree = max φ.xRatFunc.num.natDegree φ.xRatFunc.denom.natDegree := by
  rw [degree_def, finrank_fieldRange_of_apply_X_eq W₁ φ.fieldPullback (g := φ.xRatFunc)
    (by rw [← genericX_eq_algebraMap, algebraMap_xRatFunc]), RatFunc.finrank_eq_max_natDegree]

/-! ### The action on points -/

section PointMap

local instance isDedekindDomain_coordinateRing_source : IsDedekindDomain W₁.CoordinateRing :=
  have := isIntegrallyClosed_coordinateRing W₁
  W₁.isDedekindDomain_coordinateRing_of_isIntegrallyClosed

/-- `x ∘ φ` as a quotient of the classes of the numerator and denominator of `φ.xRatFunc`. -/
private theorem fieldPullback_genericX_eq_div (φ : Isogeny W₁ W₂) :
    φ.fieldPullback (genericX W₂) =
      algebraMap W₁.CoordinateRing W₁.FunctionField (CoordinateRing.mk W₁ (C φ.xRatFunc.num)) /
        algebraMap W₁.CoordinateRing W₁.FunctionField
          (CoordinateRing.mk W₁ (C φ.xRatFunc.denom)) := by
  rw [← algebraMap_xRatFunc]
  nth_rewrite 1 [← RatFunc.num_div_denom φ.xRatFunc]
  rw [map_div₀,
    ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply,
    CoordinateRing.mk_C_eq_algebraMap, CoordinateRing.mk_C_eq_algebraMap,
    ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]

private theorem mk_C_denom_ne_zero (φ : Isogeny W₁ W₂) :
    CoordinateRing.mk W₁ (C φ.xRatFunc.denom) ≠ 0 := by
  rw [CoordinateRing.mk_C_eq_algebraMap, Ne,
    map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective F[X] W₁.CoordinateRing)]
  exact RatFunc.denom_ne_zero _

variable {φ : Isogeny W₁ W₂} {x y : F} (h : W₁.Equation x y)

/-- Where the denominator does not vanish, `x ∘ φ` has no pole. -/
private theorem valuation_fieldPullback_genericX_le_one (hd : φ.xRatFunc.denom.eval x ≠ 0) :
    (CoordinateRing.pointPlace h).valuation W₁.FunctionField
      (φ.fieldPullback (genericX W₂)) ≤ 1 := by
  rw [fieldPullback_genericX_eq_div]
  exact CoordinateRing.valuation_pointPlace_div_le_one _ h (by rwa [evalEval_C])

/-- Where the denominator does not vanish, `x ∘ φ` is congruent to the value `r(x₀)`. -/
private theorem valuation_fieldPullback_genericX_sub_lt_one (hd : φ.xRatFunc.denom.eval x ≠ 0) :
    (CoordinateRing.pointPlace h).valuation W₁.FunctionField (φ.fieldPullback (genericX W₂) -
      algebraMap F W₁.FunctionField (φ.xRatFunc.num.eval x / φ.xRatFunc.denom.eval x)) < 1 := by
  set c := φ.xRatFunc.num.eval x / φ.xRatFunc.denom.eval x
  have hD : algebraMap W₁.CoordinateRing W₁.FunctionField
      (CoordinateRing.mk W₁ (C φ.xRatFunc.denom)) ≠ 0 :=
    (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective W₁.CoordinateRing
      W₁.FunctionField)).mpr (mk_C_denom_ne_zero φ)
  have heq : φ.fieldPullback (genericX W₂) - algebraMap F W₁.FunctionField c =
      algebraMap W₁.CoordinateRing W₁.FunctionField
          (CoordinateRing.mk W₁ (C (φ.xRatFunc.num - Polynomial.C c * φ.xRatFunc.denom))) /
        algebraMap W₁.CoordinateRing W₁.FunctionField
          (CoordinateRing.mk W₁ (C φ.xRatFunc.denom)) := by
    rw [fieldPullback_genericX_eq_div, eq_div_iff hD, sub_mul, div_mul_cancel₀ _ hD, C_sub, C_mul,
      map_sub, map_sub, map_mul, map_mul, IsScalarTower.algebraMap_apply F W₁.CoordinateRing,
      CoordinateRing.mk_C_eq_algebraMap (W := W₁) (Polynomial.C c),
      IsScalarTower.algebraMap_apply F F[X] W₁.CoordinateRing, Polynomial.algebraMap_eq]
  rw [heq]
  refine CoordinateRing.valuation_pointPlace_div_lt_one _ h (by rwa [evalEval_C]) ?_
  rw [evalEval_C, eval_sub, eval_mul, eval_C, div_mul_cancel₀ _ hd, sub_self]

/-- Where the denominator vanishes, `x ∘ φ` has a pole. -/
private theorem one_lt_valuation_fieldPullback_genericX (hd : φ.xRatFunc.denom.eval x = 0) :
    1 < (CoordinateRing.pointPlace h).valuation W₁.FunctionField
      (φ.fieldPullback (genericX W₂)) := by
  rw [fieldPullback_genericX_eq_div]
  refine CoordinateRing.one_lt_valuation_pointPlace_div _ h ?_ (by rwa [evalEval_C])
    (mk_C_denom_ne_zero φ)
  rw [evalEval_C]
  obtain ⟨a, b, hab⟩ := RatFunc.isCoprime_num_denom φ.xRatFunc
  intro hn
  have := congrArg (eval x) hab
  rw [eval_add, eval_mul, eval_mul, hn, hd, eval_one] at this
  simp at this

variable [DecidableEq F]

/-- **`φ` sends `(x₀, y₀)` to the point at infinity exactly when the denominator of its
`x`-coordinate vanishes at `x₀`.** -/
theorem pointMap_ofIsogeny_some_eq_zero_iff (h : W₁.Nonsingular x y) :
    (Hom.ofIsogeny φ).pointMap (.some x y h) = 0 ↔ φ.xRatFunc.denom.eval x = 0 := by
  rw [Hom.pointMap_eq_iff, map_zero, map_zero, sub_zero, mem_polePoints_iff,
    coe_pointEquivDegreeOnePlace_some, Place.valuation_ofPrime, Hom.tautologicalPoint_ofIsogeny,
    CoordinatePullback.xCoord_tautologicalPoint, ← AdjoinRoot.mk_C, ← CoordinateRing.mk,
    ← fieldPullback_algebraMap, ← genericX_def,
    or_iff_right (CoordinatePullback.tautologicalPoint_ne_zero _)]
  refine ⟨fun hv ↦ by_contra fun hd ↦ ?_, one_lt_valuation_fieldPullback_genericX h.left⟩
  exact (valuation_fieldPullback_genericX_le_one h.left hd).not_gt hv

/-- **Away from the poles, the image of `(x₀, y₀)` under `φ` has `x`-coordinate `r(x₀)`**, for
`r = φ.xRatFunc`. -/
theorem xCoord_pointMap_ofIsogeny_some (h : W₁.Nonsingular x y)
    (hd : φ.xRatFunc.denom.eval x ≠ 0) :
    Point.xCoord ((Hom.ofIsogeny φ).pointMap (.some x y h)) =
      φ.xRatFunc.num.eval x / φ.xRatFunc.denom.eval x := by
  have hQ := (Hom.pointMap_eq_iff (f := Hom.ofIsogeny φ) (P := .some x y h)).mp rfl
  have hne : (Hom.ofIsogeny φ).pointMap (.some x y h) ≠ 0 :=
    (pointMap_ofIsogeny_some_eq_zero_iff h).not.mpr hd
  generalize (Hom.ofIsogeny φ).pointMap (.some x y h) = Q at hQ hne ⊢
  rcases Q with _ | ⟨c, d, hc⟩
  · exact absurd rfl hne
  rw [Point.xCoord_some]
  rw [Point.equivBaseChangeSelf_some, Hom.tautologicalPoint_ofIsogeny,
    ← Point.some_coords (CoordinatePullback.tautologicalPoint_ne_zero _),
    coe_pointEquivDegreeOnePlace_some, some_sub_baseChange_mem_polePoints_iff,
    Place.valuation_ofPrime, CoordinatePullback.xCoord_tautologicalPoint, ← AdjoinRoot.mk_C,
    ← CoordinateRing.mk, ← fieldPullback_algebraMap, ← genericX_def] at hQ
  by_contra hne'
  have h1 := Valuation.map_sub_lt _ hQ.1 (valuation_fieldPullback_genericX_sub_lt_one h.left hd)
  rw [sub_sub_sub_cancel_left, ← map_sub, ← Place.valuation_ofPrime (k := F),
    (Place.ofPrime F W₁.FunctionField _).isTrivialOn.eq_one _ (sub_ne_zero.mpr (Ne.symm hne'))]
    at h1
  exact lt_irrefl _ h1

end PointMap

end TauCeti.Isogeny
