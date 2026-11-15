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
public import TauCeti.AlgebraicGeometry.Morphisms.Flat.Dominant
import TauCeti.AlgebraicGeometry.Noetherian

/-!
# The degree of a pullback along a finite flat morphism of curves

Let `k` be a field, `C` an integral proper curve over `k` with finite-dimensional `H⁰(C, 𝒪_C)` and
`H¹(C, 𝒪_C)`, possibly singular, and `g : C' ⟶ C` a finite flat morphism over `k` of constant
rank `n`, where `H⁰(C', 𝒪_{C'})` and `H¹(C', 𝒪_{C'})` are finite-dimensional. Then pulling back
along `g` multiplies degrees by `n`:

`deg_k (g^* L) = n · deg_k L`

for every line bundle `L` on `C` (`LineBundleClass.eulerDegree_pullback_of_finrank_eq`). Writing
`L ≅ 𝒪_C(E) ⊗ 𝒪_C(F)⁻¹` with `E` and `F` effective Cartier divisors, the inverse images `g⁻¹ E`
and `g⁻¹ F` are effective Cartier divisors on `C'` because `g` is flat, and
`dim_k Γ(g⁻¹ E, 𝒪) = n · dim_k Γ(E, 𝒪)` because `g⁻¹ E ⟶ E` is finite flat of rank `n`
(`AlgebraicGeometry.Scheme.IdealSheafData.finrank_comap_subschemeι_comp`).

When the local rings of `C` are valuation rings, for instance when `C` is a regular curve, every
dominant morphism from an integral scheme to `C` is flat, and the rank of a finite dominant
morphism of integral schemes is the degree `[K(C') : K(C)]` of its function-field extension. So
for every finite dominant morphism `g : C' ⟶ C` from an integral scheme,
`deg_k (g^* L) = [K(C') : K(C)] · deg_k L`
(`LineBundleClass.eulerDegree_pullback_of_isDominant`).

## Main results

* `LineBundleClass.eulerDegree_pullback_of_finrank_eq`: `deg (g^* L) = n · deg L` for a finite flat
  morphism `g` of constant rank `n` onto an integral proper curve.
* `LineBundleClass.eulerDegree_pullback_eq_finrank_functionField_mul`: the finite flat dominant
  case, with the multiplier expressed as the degree of the function-field extension.
* `LineBundleClass.eulerDegree_pullback_of_isDominant`: `deg (g^* L) = [K(C') : K(C)] · deg L` for
  a finite dominant morphism of integral curves whose target has valuation rings as local rings.

## References

* [The Stacks Project, Section 33.44](https://stacks.math.columbia.edu/tag/0AYQ): degrees on
  proper curves.
* Q. Liu, *Algebraic Geometry and Arithmetic Curves*, Section 7.3 (the degree of the pullback of
  a divisor along a finite morphism of curves).
-/

public section

open CategoryTheory Limits AlgebraicGeometry
open TauCeti.AlgebraicGeometry.Scheme.Modules

namespace TauCeti.AlgebraicGeometry

universe u

noncomputable section

namespace LineBundleClass

variable (k : Type u) [Field k] {C C' : Scheme.{u}} [C.Over (Spec (.of k))]
  [C'.Over (Spec (.of k))] (g : C' ⟶ C) [g.IsOver (Spec (.of k))] [IsFinite g]

section Divisor

variable {I : C.IdealSheafData} [IsFinite (I.subschemeι ≫ C ↘ Spec (.of k))]

/-- The inverse image along `g` of a closed subscheme finite over `k` is finite over `k`. -/
private lemma isFinite_comap_subschemeι_comp :
    IsFinite ((I.comap g).subschemeι ≫ C' ↘ Spec (.of k)) :=
  comp_over g (Spec (.of k)) ▸ I.isFinite_comap_subschemeι_comp _ g

variable [Flat g] [FiniteDimensional k (Cohomology (InvertibleSheaf.trivial C').obj 0)]
  [FiniteDimensional k (Cohomology (InvertibleSheaf.trivial C').obj 1)]

/-- The ideal sheaf `𝒪_{C'}(-g⁻¹ D)` of the inverse image of an effective Cartier divisor `D` finite
over `k` has degree `-n · dim_k Γ(D, 𝒪_D)` on `C'` when `g` has constant rank `n`. -/
private lemma eulerDegree_comap_toInvertibleSheaf (hI : I.IsEffectiveCartier) {n : ℕ}
    (hg : ∀ x, g.finrank x = n) (s : Spec (.of k)) :
    (hI.comap g).toInvertibleSheaf.eulerDegree k =
      -(n * ((I.subschemeι ≫ C ↘ Spec (.of k)).finrank s : ℤ)) := by
  have := isFinite_comap_subschemeι_comp k g (I := I)
  rw [(hI.comap g).eulerDegree_toInvertibleSheaf k _ s, ← comp_over g (Spec (.of k)),
    I.finrank_comap_subschemeι_comp _ g hg s]
  push_cast
  ring

end Divisor

section Curve

variable [IsIntegral C] [IsProper (C ↘ Spec (.of k))] [RelativeDimensionLE 1 (C ↘ Spec (.of k))]
  [FiniteDimensional k (Cohomology (InvertibleSheaf.trivial C).obj 0)]
  [FiniteDimensional k (Cohomology (InvertibleSheaf.trivial C).obj 1)]
  [FiniteDimensional k (Cohomology (InvertibleSheaf.trivial C').obj 0)]
  [FiniteDimensional k (Cohomology (InvertibleSheaf.trivial C').obj 1)]

/-- **The degree of a pullback along a finite flat morphism.** Let `C` be an integral scheme,
proper over `k` with fibres of dimension at most one and with finite-dimensional `H⁰(C, 𝒪_C)` and
`H¹(C, 𝒪_C)`, and let `g : C' ⟶ C` be a finite flat morphism over `k` of constant rank `n`, where
`H⁰(C', 𝒪_{C'})` and `H¹(C', 𝒪_{C'})` are finite-dimensional. Then `deg (g^* L) = n · deg L` for
every line-bundle class on `C`. The curve `C` may be singular, and `C'` may be singular, reducible
or nonreduced. -/
theorem eulerDegree_pullback_of_finrank_eq [Flat g] {n : ℕ} (hg : ∀ x, g.finrank x = n)
    (a : LineBundleClass C) : eulerDegree k (pullback g a) = n * eulerDegree k a := by
  have : IsNoetherian C := isNoetherian_of_finiteType (C ↘ Spec (.of k))
  obtain ⟨E, F, hE, hF, rfl⟩ :=
    Scheme.CartierDivisor.exists_isEffective_toLineBundleClass_mul_inv_eq
    (coheight_le_of_relativeDimensionLE_of_field (d := 1) (C ↘ Spec (.of k))) a
  have hI := hE.isEffectiveCartier_sectionsIdealSheaf
  have hJ := hF.isEffectiveCartier_sectionsIdealSheaf
  have : IsFinite (hE.sectionsIdealSheaf.subschemeι ≫ C ↘ Spec (.of k)) :=
    hI.isFinite_subschemeι_comp
  have : IsFinite (hF.sectionsIdealSheaf.subschemeι ≫ C ↘ Spec (.of k)) :=
    hJ.isFinite_subschemeι_comp
  -- `𝒪_C(E) ⊗ 𝒪_C(F)⁻¹` is `𝒪_C(-F) ⊗ 𝒪_C(-E)⁻¹`, and its pullback is
  -- `𝒪_{C'}(-g⁻¹ F) ⊗ 𝒪_{C'}(-g⁻¹ E)⁻¹`.
  have ha : E.toLineBundleClass * F.toLineBundleClass⁻¹ =
      mk hJ.toInvertibleSheaf * (mk hI.toInvertibleSheaf)⁻¹ := by
    rw [hE.mk_toInvertibleSheaf_sectionsIdealSheaf, hF.mk_toInvertibleSheaf_sectionsIdealSheaf,
      inv_inv, mul_comm]
  have := isFinite_comap_subschemeι_comp k g (I := hE.sectionsIdealSheaf)
  -- `𝒪_{C'}(-g⁻¹ F)` has finite-dimensional `H⁰` and `H¹`, as `𝒪_{C'}` does.
  have hfin (i : ℕ) (hi : i < 2) :
      FiniteDimensional k (Cohomology (hJ.comap g).toInvertibleSheaf.obj i) := by
    have := isFinite_comap_subschemeι_comp k g (I := hF.sectionsIdealSheaf)
    rw [Scheme.IdealSheafData.IsEffectiveCartier.toInvertibleSheaf_obj]
    exact (hF.sectionsIdealSheaf.comap g).finiteDimensional_cohomology_sheaf k hi
  have := hfin 0 (by norm_num)
  have := hfin 1 (by norm_num)
  -- Both sides are now computed by the degrees `dim_k Γ(E, 𝒪_E)` and `dim_k Γ(F, 𝒪_F)`.
  have hdeg : eulerDegree k (mk hJ.toInvertibleSheaf * (mk hI.toInvertibleSheaf)⁻¹) =
      ((hE.sectionsIdealSheaf.subschemeι ≫ C ↘ Spec (.of k)).finrank default : ℤ) -
        (hF.sectionsIdealSheaf.subschemeι ≫ C ↘ Spec (.of k)).finrank default := by
    rw [eulerDegree_mul_of_isIntegral, eulerDegree_inv_of_isIntegral, eulerDegree_mk,
      eulerDegree_mk, hI.eulerDegree_toInvertibleSheaf k _ default,
      hJ.eulerDegree_toInvertibleSheaf k _ default]
    ring
  have hdeg' : eulerDegree k (pullback g (mk hJ.toInvertibleSheaf * (mk hI.toInvertibleSheaf)⁻¹)) =
      n * ((hE.sectionsIdealSheaf.subschemeι ≫ C ↘ Spec (.of k)).finrank default : ℤ) -
        n * ((hF.sectionsIdealSheaf.subschemeι ≫ C ↘ Spec (.of k)).finrank default : ℤ) := by
    rw [pullback_mul, pullback_inv, hJ.pullback_mk_toInvertibleSheaf (hJ.comap g),
      hI.pullback_mk_toInvertibleSheaf (hI.comap g),
      (hI.comap g).eulerDegree_mk_mul_inv_mk_toInvertibleSheaf k _ (hJ.comap g).toInvertibleSheaf,
      eulerDegree_comap_toInvertibleSheaf k g hI hg default,
      eulerDegree_comap_toInvertibleSheaf k g hJ hg default]
    ring
  rw [ha, hdeg', hdeg]
  ring

/-- **The degree under pullback is multiplied by the degree of the function-field extension.**
Let `g : C' ⟶ C` be a finite flat dominant morphism of integral schemes over `k`, where `C` is
proper over `k` with fibres of dimension at most one, and the structure sheaves of `C'` and `C`
have finite-dimensional `H⁰` and `H¹`. Then `deg g^* L = [K(C') : g^* K(C)] · deg L` for every line
bundle `L` on `C`. -/
theorem eulerDegree_pullback_eq_finrank_functionField_mul [Flat g] [IsIntegral C'] [IsDominant g]
    (a : LineBundleClass C) :
    eulerDegree k (pullback g a) =
      Module.finrank g.functionFieldMap.hom.fieldRange C'.functionField * eulerDegree k a :=
  eulerDegree_pullback_of_finrank_eq k g g.finrank_eq_finrank_fieldRange_functionFieldMap a

/-- **The degree of a pullback along a finite dominant morphism.** Let `C` be as in
`LineBundleClass.eulerDegree_pullback_of_finrank_eq`, with all local rings valuation rings, as for
a regular curve, and let `g : C' ⟶ C` be a finite dominant morphism over `k` from an integral
scheme with finite-dimensional `H⁰(C', 𝒪_{C'})` and `H¹(C', 𝒪_{C'})`. Then
`deg (g^* L) = [K(C') : K(C)] · deg L` for every line-bundle class on `C`, the degree of `g` being
that of the function field of `C'` over the image of the function field of `C`. -/
theorem eulerDegree_pullback_of_isDominant [IsIntegral C'] [IsDominant g]
    [∀ y : C, ValuationRing (C.presheaf.stalk y)] (a : LineBundleClass C) :
    eulerDegree k (pullback g a) =
      Module.finrank g.functionFieldMap.hom.fieldRange C'.functionField * eulerDegree k a :=
  have := g.flat_of_isDominant_of_valuationRing
  eulerDegree_pullback_of_finrank_eq k g g.finrank_eq_finrank_fieldRange_functionFieldMap a

end Curve

end LineBundleClass

end

end TauCeti.AlgebraicGeometry
