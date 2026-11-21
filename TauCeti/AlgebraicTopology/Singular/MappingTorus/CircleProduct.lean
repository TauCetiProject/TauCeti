/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.AddCircle
public import TauCeti.AlgebraicTopology.Cohomology.IntegralCup
public import TauCeti.AlgebraicTopology.Singular.MappingTorus.FirstCohomology
public import TauCeti.AlgebraicTopology.Singular.MappingTorus.SecondCohomology

/-!
# The second cohomology of a circle times a surface mapping torus

Let `φ` be an orientation-preserving homeomorphism of a closed connected oriented surface `F` with
`det (1 - φ_*) ≠ 0` on `H₁(F; ℤ)`, so that the mapping torus `Y_φ` has `b₁(Y_φ) = 1`, and let
`X = (ℝ / pℤ) × Y_φ`. This file shows that two explicit classes span `H²(X; ℤ)` modulo torsion and
identifies the torsion of `H²(X; ℤ)`.

Write `pr₁, pr₂` for the projections of `X` and `θ_p` for the angular class of `ℝ / pℤ`
(`AddCircle.angularClass`). Let `v ∈ H²(Y_φ; ℤ)` pair to one with the fibre class `i_*[F]`, and
let `α` generate `H¹(Y_φ; ℤ) ≅ ℤ` (`TauCeti.MappingTorus.cohomologyOneEquiv`). The class `v`
generates `H²(Y_φ; ℤ)` modulo torsion
(`TauCeti.MappingTorus.isOfFinAddOrder_sub_evalFundamentalClass_smul`), so by the slant
decomposition `H²(X; ℤ) ≅ H²(Y_φ; ℤ) × H¹(Y_φ; ℤ)`
(`TopCat.singularCohomologyAddCircleProdSlantEquiv`) the classes `pr₂^* v` and
`pr₁^* θ_p ⌣ pr₂^* α` span `H²(X; ℤ)` modulo torsion
(`TauCeti.MappingTorus.exists_isOfFinAddOrder_sub_smul_add_smul_addCircleProd`). Since
`H¹(Y_φ; ℤ) ≅ ℤ` is torsion-free, the classes of finite order of `H²(X; ℤ)` are exactly the
pullbacks of the classes of finite order of `H²(Y_φ; ℤ)`
(`TauCeti.MappingTorus.isOfFinAddOrder_iff_exists_singularCohomologyMap_snd_addCircleProd`).

For `p = 1` and `α` the integral class of the time form `dt`, these are the classes `v` and
`t = [ds ∧ dt]` in which the line labels of the symplectic suspension `(ℝ / ℤ)_s × Y_φ` are written
in `TauCeti.Geometry.Symplectic.Manifold.Suspension.Chamber`. The spanning statement is the
hypothesis `hspan` of the hyperbolic-pair lemmas of
`TauCeti.LinearAlgebra.BilinearForm.HyperbolicPair`, such as
`LinearMap.BilinForm.sigPos_toQuadraticMap_baseChange_eq_one_of_isOfFinAddOrder_span`. The
intersection numbers of `pr₂^* v` and `pr₁^* θ_p ⌣ pr₂^* α`, and the comparison of a generator `α`
with the class of `dt`, are not computed here.

The fibre class and the class `v` are taken in integral cohomology with chain coefficients
`ULift ℤ` (`TopCat.integralCohomology`), where `TauCeti.HomologicalOrientation.evalFundamentalClass`
pairs with fundamental classes. The cohomology of the product is taken with unit coefficients, the
convention of `TopCat.singularCohomologyAddCircleProdSlantEquiv`; the two are identified by
`TopCat.integralCohomologyEquiv`.

## Main results

* `TauCeti.MappingTorus.exists_isOfFinAddOrder_sub_smul_add_smul_addCircleProd`: `pr₂^* v` and
  `pr₁^* θ_p ⌣ pr₂^* α` span `H²((ℝ / pℤ) × Y_φ; ℤ)` modulo torsion.
* `TauCeti.MappingTorus.isOfFinAddOrder_iff_exists_singularCohomologyMap_snd_addCircleProd`: the
  classes of finite order of `H²((ℝ / pℤ) × Y_φ; ℤ)` are the pullbacks of those of `H²(Y_φ; ℤ)`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 2.2, Example 2.48 (the Wang sequence of a mapping torus), and Theorem 3.15 (the Künneth
  formula).
* C. H. Taubes, *The Seiberg–Witten and Gromov invariants*, Math. Res. Lett. 2 (1995), 221–238.
-/

public section

noncomputable section

open CategoryTheory MonoidalCategory AlgebraicTopology HomologicalComplex Module

-- The cohomology of products with circles is taken with the `ℤ`-linear structure of `ModuleCat ℤ`
-- as a category of modules, as in `TauCeti.AlgebraicTopology.Cohomology.AddCircle`; instance search
-- would otherwise find the structure `Linear.preadditiveIntLinear` of a preadditive category.
attribute [local instance 1100] ModuleCat.instLinear

namespace TauCeti.MappingTorus

variable {F : Type} [TopologicalSpace F] (φ : F ≃ₜ F) [PathConnectedSpace F]
  [Module.Free ℤ ((((singularChainComplexFunctor (ModuleCat.{0} ℤ)).obj
    (ModuleCat.of ℤ ℤ)).obj (TopCat.of F)).homology 1)]
  [Module.Finite ℤ ((((singularChainComplexFunctor (ModuleCat.{0} ℤ)).obj
    (ModuleCat.of ℤ ℤ)).obj (TopCat.of F)).homology 1)]

/-- **The classes of finite order of `H²((ℝ / pℤ) × T_φ; ℤ)`**: if `F` is path-connected, `H₁(F)`
is free of finite rank and `det (1 - φ_*) ≠ 0` on it, a class of `H²((ℝ / pℤ) × T_φ; ℤ)` has
finite order exactly when it is pulled back from a class of finite order of `H²(T_φ; ℤ)`. Indeed
`H¹(T_φ; ℤ) ≅ ℤ` is torsion-free (`TauCeti.MappingTorus.cohomologyOneEquiv`). -/
theorem isOfFinAddOrder_iff_exists_singularCohomologyMap_snd_addCircleProd {p : ℝ} [Fact (0 < p)]
    (hdet : (LinearMap.id -
      (homologyMap (monodromyChainMap φ (ModuleCat.of ℤ ℤ)) 1).hom).det ≠ 0)
    (x : (TopCat.of (AddCircle p) ⊗ TopCat.of (MappingTorus φ)).singularCohomology
      (𝟙_ (ModuleCat.{0} ℤ)) ℤ (𝟙_ (ModuleCat.{0} ℤ)) 2) :
    IsOfFinAddOrder x ↔ ∃ w, IsOfFinAddOrder w ∧
      TopCat.singularCohomologyMap (CartesianMonoidalCategory.snd _ _) 2 w = x := by
  have := Function.Injective.isAddTorsionFree
    (cohomologyOneEquiv φ (ModuleCat.of ℤ ℤ) hdet).toLinearMap.toAddMonoidHom
    (cohomologyOneEquiv φ (ModuleCat.of ℤ ℤ) hdet).injective
  exact TopCat.isOfFinAddOrder_iff_exists_singularCohomologyMap_snd_addCircle _ _ (n := 1) x

variable {E : Type} [T2Space F] [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [ChartedSpace E F] [CompactSpace F] (o : HomologicalOrientation F E 2) (hn : finrank ℝ E = 2)

/-- **Generators of `H²((ℝ / pℤ) × Y_φ; ℤ)` modulo torsion.** Let `φ` be an orientation-preserving
homeomorphism of a closed connected oriented surface `F` with `det (1 - φ_*) ≠ 0` on `H₁(F; ℤ)`.
Let `v ∈ H²(Y_φ; ℤ)` pair to one with the fibre class `i_*[F]`, and let `α` generate
`H¹(Y_φ; ℤ) ≅ ℤ`. Then every class of `H²((ℝ / pℤ) × Y_φ; ℤ)` differs from a combination of
`pr₂^* v` and `pr₁^* θ_p ⌣ pr₂^* α` by an element of finite order. -/
theorem exists_isOfFinAddOrder_sub_smul_add_smul_addCircleProd {p : ℝ} [Fact (0 < p)]
    (hφ : o.mapFundamentalClass hn ⟨φ, φ.continuous⟩ = o.fundamentalClass hn)
    (hdet : (LinearMap.id -
      (homologyMap (monodromyChainMap φ (ModuleCat.of ℤ ℤ)) 1).hom).det ≠ 0)
    {v : (TopCat.of (MappingTorus φ)).singularCohomology (𝟙_ (ModuleCat.{0} ℤ)) ℤ
      (𝟙_ (ModuleCat.{0} ℤ)) 2}
    (hv : o.evalFundamentalClass hn (ModuleCat.of ℤ ℤ) (incl φ)
      (((TopCat.of (MappingTorus φ)).integralCohomologyEquiv 2).symm v) = 1)
    {α : (TopCat.of (MappingTorus φ)).singularCohomology (𝟙_ (ModuleCat.{0} ℤ)) ℤ
      (𝟙_ (ModuleCat.{0} ℤ)) 1}
    (hα : IsUnit (cohomologyOneEquiv φ (ModuleCat.of ℤ ℤ) hdet α))
    (x : (TopCat.of (AddCircle p) ⊗ TopCat.of (MappingTorus φ)).singularCohomology
      (𝟙_ (ModuleCat.{0} ℤ)) ℤ (𝟙_ (ModuleCat.{0} ℤ)) 2) :
    ∃ a c : ℤ, IsOfFinAddOrder (x -
      (a • TopCat.singularCohomologyMap (CartesianMonoidalCategory.snd _ _) 2 v +
        c • (TopCat.of (AddCircle p) ⊗ TopCat.of (MappingTorus φ)).singularCup ℤ
          (λ_ (𝟙_ (ModuleCat.{0} ℤ))).inv (λ_ (𝟙_ (ModuleCat.{0} ℤ))).hom 1 1 2 rfl
          (TopCat.singularCohomologyMap (CartesianMonoidalCategory.fst _ _) 1
            (AddCircle.angularClass p))
          (TopCat.singularCohomologyMap (CartesianMonoidalCategory.snd _ _) 1 α))) := by
  refine TopCat.exists_isOfFinAddOrder_sub_smul_add_smul_addCircle _ _ (n := 1) (fun b ↦ ?_)
    (fun c ↦ ?_) x
  · -- `v` generates `H²(Y_φ; ℤ)` modulo torsion, read through the comparison of coefficients
    set e := (TopCat.of (MappingTorus φ)).integralCohomologyEquiv 2
    refine ⟨o.evalFundamentalClass hn (ModuleCat.of ℤ ℤ) (incl φ) (e.symm b), ?_⟩
    have h := e.toLinearMap.toAddMonoidHom.isOfFinAddOrder
      (isOfFinAddOrder_sub_evalFundamentalClass_smul φ o hn hφ hdet hv (e.symm b))
    rwa [LinearMap.toAddMonoidHom_coe, LinearEquiv.coe_coe, map_sub, map_zsmul,
      e.apply_symm_apply, e.apply_symm_apply] at h
  · -- `α` corresponds to a unit `u` of `ℤ`, and `c` to `(c / u) • α`
    obtain ⟨u, hu⟩ := hα
    set g := cohomologyOneEquiv φ (ModuleCat.of ℤ ℤ) hdet
    have hc : c = (g c * ↑u⁻¹) • α := g.injective <| by
      rw [map_zsmul, ← hu, smul_eq_mul, mul_assoc, Units.inv_mul, mul_one]
    exact ⟨g c * ↑u⁻¹, by rw [← hc, sub_self]; exact IsOfFinAddOrder.zero⟩

end TauCeti.MappingTorus
