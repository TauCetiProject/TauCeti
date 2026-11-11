/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.CartierDivisor.Effective.Degree
public import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Pullback
public import TauCeti.AlgebraicGeometry.IdealSheaf.BaseChange
public import TauCeti.AlgebraicGeometry.Morphisms.Finite.FlatDegree
import TauCeti.AlgebraicGeometry.Noetherian

/-!
# The degree of a line bundle under finite flat pullback

Let `f : X ⟶ Y` be a finite flat morphism of schemes over a field `k`, of constant rank `d`.
Suppose that `Y` is an integral scheme, proper over `k` with fibres of dimension at most one, and
that `H⁰` and `H¹` of the structure sheaves of `X` and `Y` are finite-dimensional. Then the
Euler-characteristic degree `deg L = χ(L) - χ(𝒪)` of line bundles satisfies

`deg f^* L = d · deg L`

for every line bundle `L` on `Y` (`LineBundleClass.eulerDegree_pullback_of_finrank_eq`). The curve
`Y` may be singular, and `X` need not be integral or reduced.

Every line bundle on `Y` is `𝒪_Y(E) ⊗ 𝒪_Y(F)⁻¹` for effective Cartier divisors `E` and `F`
(`Scheme.CartierDivisor.exists_isEffective_toLineBundleClass_mul_inv_eq`), and the degree of
`𝒪_Y(D)` for an effective divisor `D` is `dim_k Γ(D, 𝒪_D)`. Since `f` is flat, the inverse image
`f⁻¹ D` is an effective Cartier divisor on `X` with `f^* 𝒪_Y(D) ≅ 𝒪_X(f⁻¹ D)`
(`Scheme.IdealSheafData.IsEffectiveCartier.pullback_mk_toInvertibleSheaf`), and `f⁻¹ D ⟶ D` is
finite flat of rank `d`, so `dim_k Γ(f⁻¹ D, 𝒪) = d · dim_k Γ(D, 𝒪_D)`
(`Scheme.IdealSheafData.finrank_comap_subschemeι_comp`).

When `X` is integral as well and `f` is dominant, the rank `d` is the degree
`[K(X) : f^* K(Y)]` of the extension of function fields
(`AlgebraicGeometry.Scheme.Hom.finrank_eq_finrank_fieldRange_functionFieldMap`), which gives
`deg f^* L = [K(X) : K(Y)] · deg L`
(`LineBundleClass.eulerDegree_pullback_eq_finrank_functionField_mul`). Every dominant morphism from
an integral scheme to an integral scheme whose local rings are valuation rings, such as a normal
curve, is flat (`AlgebraicGeometry.Scheme.Hom.flat_of_isDominant_of_valuationRing`).

## Main results

* `LineBundleClass.eulerDegree_pullback_of_finrank_eq`: `deg f^* L = d · deg L` for a finite
  flat morphism `f` of constant rank `d` onto a proper integral curve.
* `LineBundleClass.eulerDegree_pullback_eq_finrank_functionField_mul`: the same with
  `d = [K(X) : f^* K(Y)]` when `X` is integral and `f` is dominant.

## References

* [The Stacks Project, Lemma 0AYZ](https://stacks.math.columbia.edu/tag/0AYZ): the degree of the
  pullback of a locally free sheaf along a nonconstant morphism of proper curves, proved by
  reducing to the line bundles of effective Cartier divisors.
* R. Hartshorne, *Algebraic Geometry*, Proposition II.6.9: `deg f^* D = deg f · deg D` for a finite
  morphism of nonsingular curves.
-/

public section

open CategoryTheory Limits AlgebraicGeometry
open TauCeti.AlgebraicGeometry.Scheme.Modules (Cohomology)

namespace TauCeti

namespace AlgebraicGeometry

universe u

noncomputable section

namespace LineBundleClass

variable (k : Type u) [Field k] {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
  {f : X ⟶ Y} [f.IsOver (Spec (.of k))] [IsFinite f] [Flat f]
  [FiniteDimensional k (Cohomology (InvertibleSheaf.trivial X).obj 0)]
  [FiniteDimensional k (Cohomology (InvertibleSheaf.trivial X).obj 1)]

/-- The degree on `X` of `f^* (𝒪_Y(D₁) ⊗ 𝒪_Y(-D₂))`, for effective Cartier divisors `D₁` and `D₂`
on `Y` finite over `k`, is `d · (deg D₁ - deg D₂)`. -/
private lemma eulerDegree_pullback_inv_mk_mul_mk {d : ℕ} (hf : ∀ y, f.finrank y = d)
    {I₁ I₂ : Y.IdealSheafData} (hI₁ : I₁.IsEffectiveCartier) (hI₂ : I₂.IsEffectiveCartier)
    [IsFinite (I₁.subschemeι ≫ Y ↘ Spec (.of k))] [IsFinite (I₂.subschemeι ≫ Y ↘ Spec (.of k))]
    (s : Spec (.of k)) :
    eulerDegree k (pullback f ((mk hI₁.toInvertibleSheaf)⁻¹ * mk hI₂.toInvertibleSheaf)) =
      d * (((I₁.subschemeι ≫ Y ↘ Spec (.of k)).finrank s : ℤ) -
        (I₂.subschemeι ≫ Y ↘ Spec (.of k)).finrank s) := by
  have hJ₁ := hI₁.comap f
  have hJ₂ := hI₂.comap f
  -- The divisors `f⁻¹ D₁` and `f⁻¹ D₂` are finite over `k`, of degrees `d · deg D₁`, `d · deg D₂`.
  have hfin (I : Y.IdealSheafData) [IsFinite (I.subschemeι ≫ Y ↘ Spec (.of k))] :
      IsFinite ((I.comap f).subschemeι ≫ X ↘ Spec (.of k)) := by
    rw [← comp_over f (Spec (.of k))]
    exact I.isFinite_comap_subschemeι_comp _ f
  have := hfin I₁
  have := hfin I₂
  -- `f^* 𝒪_Y(-D₂) = 𝒪_X(-f⁻¹ D₂)` has finite-dimensional `H⁰` and `H¹`.
  have := (I₂.comap f).finiteDimensional_cohomology_sheaf k (i := 0) (by norm_num)
  have := (I₂.comap f).finiteDimensional_cohomology_sheaf k (i := 1) (by norm_num)
  have : FiniteDimensional k (Cohomology hJ₂.toInvertibleSheaf.obj 0) := by
    rwa [Scheme.IdealSheafData.IsEffectiveCartier.toInvertibleSheaf_obj]
  have : FiniteDimensional k (Cohomology hJ₂.toInvertibleSheaf.obj 1) := by
    rwa [Scheme.IdealSheafData.IsEffectiveCartier.toInvertibleSheaf_obj]
  have hrank (I : Y.IdealSheafData) [IsFinite (I.subschemeι ≫ Y ↘ Spec (.of k))] :
      ((I.comap f).subschemeι ≫ X ↘ Spec (.of k)).finrank s =
        d * (I.subschemeι ≫ Y ↘ Spec (.of k)).finrank s := by
    rw [← comp_over f (Spec (.of k))]
    exact I.finrank_comap_subschemeι_comp _ f hf s
  rw [pullback_mul, pullback_inv, hI₁.pullback_mk_toInvertibleSheaf hJ₁,
    hI₂.pullback_mk_toInvertibleSheaf hJ₂, mul_comm,
    hJ₁.eulerDegree_mk_mul_inv_mk_toInvertibleSheaf k _ hJ₂.toInvertibleSheaf,
    hJ₁.eulerDegree_toInvertibleSheaf k _ s, hJ₂.eulerDegree_toInvertibleSheaf k _ s, hrank,
    hrank]
  push_cast
  ring

variable [IsIntegral Y] [IsProper (Y ↘ Spec (.of k))] [RelativeDimensionLE 1 (Y ↘ Spec (.of k))]
  [FiniteDimensional k (Cohomology (InvertibleSheaf.trivial Y).obj 0)]
  [FiniteDimensional k (Cohomology (InvertibleSheaf.trivial Y).obj 1)]

/-- **The degree under finite flat pullback.** Let `f : X ⟶ Y` be a finite flat morphism of
schemes over `k` of constant rank `d`, where `Y` is an integral scheme proper over `k` with fibres
of dimension at most one, and the structure sheaves of `X` and `Y` have finite-dimensional `H⁰`
and `H¹`. Then `deg f^* L = d · deg L` for every line bundle `L` on `Y`. The curve `Y` may be
singular, and `X` need not be integral. -/
theorem eulerDegree_pullback_of_finrank_eq {d : ℕ} (hf : ∀ y, f.finrank y = d)
    (a : LineBundleClass Y) :
    eulerDegree k (pullback f a) = d * eulerDegree k a := by
  have : IsNoetherian Y := isNoetherian_of_finiteType (Y ↘ Spec (.of k))
  obtain ⟨E, F, hE, hF, rfl⟩ :=
    Scheme.CartierDivisor.exists_isEffective_toLineBundleClass_mul_inv_eq
    (coheight_le_of_relativeDimensionLE_of_field (d := 1) (Y ↘ Spec (.of k))) a
  have hIE := hE.isEffectiveCartier_sectionsIdealSheaf
  have hIF := hF.isEffectiveCartier_sectionsIdealSheaf
  have : IsFinite (hE.sectionsIdealSheaf.subschemeι ≫ Y ↘ Spec (.of k)) :=
    hIE.isFinite_subschemeι_comp
  have : IsFinite (hF.sectionsIdealSheaf.subschemeι ≫ Y ↘ Spec (.of k)) :=
    hIF.isFinite_subschemeι_comp
  -- On `Y`, `deg (𝒪_Y(E) ⊗ 𝒪_Y(F)⁻¹) = deg E - deg F`.
  rw [eulerDegree_mul_of_isIntegral, eulerDegree_inv_of_isIntegral,
    hE.eulerDegree_toLineBundleClass k default, hF.eulerDegree_toLineBundleClass k default,
    ← sub_eq_add_neg, ← inv_inv E.toLineBundleClass, ← hE.mk_toInvertibleSheaf_sectionsIdealSheaf,
    ← hF.mk_toInvertibleSheaf_sectionsIdealSheaf]
  exact eulerDegree_pullback_inv_mk_mul_mk k hf hIE hIF default

/-- **The degree under pullback is multiplied by the degree of the function-field extension.**
Let `f : X ⟶ Y` be a finite flat dominant morphism of integral schemes over `k`, where `Y` is
proper over `k` with fibres of dimension at most one, and the structure sheaves of `X` and `Y`
have finite-dimensional `H⁰` and `H¹`. Then `deg f^* L = [K(X) : f^* K(Y)] · deg L` for every line
bundle `L` on `Y`. -/
theorem eulerDegree_pullback_eq_finrank_functionField_mul [IsIntegral X] [IsDominant f]
    (a : LineBundleClass Y) :
    eulerDegree k (pullback f a) =
      Module.finrank f.functionFieldMap.hom.fieldRange X.functionField * eulerDegree k a :=
  eulerDegree_pullback_of_finrank_eq k f.finrank_eq_finrank_fieldRange_functionFieldMap a

end LineBundleClass

end

end AlgebraicGeometry

end TauCeti
