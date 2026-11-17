/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.FundamentalClass
public import TauCeti.AlgebraicTopology.Cohomology.IntegralCup
public import TauCeti.AlgebraicTopology.Cohomology.Sphere.Product
import TauCeti.CategoryTheory.Linear.Int

/-!
# The integral intersection form of `Sᵈ⁺¹ × Y` is even

Let `Y` be a compact manifold and `x ∈ Hᵐ(Sᵈ⁺¹ × Y; ℤ)` an integral class of even degree `m`, with
`dim Y < 2 m`. In the slant decomposition of `Hᵐ(Sᵈ⁺¹ × Y)` the cup square of `x` is twice a class,
since its two cross terms agree and the square of the component pulled back from `Y` lies in a
vanishing cohomology group of `Y`
(`TopCat.two_dvd_singularKronecker_singularCup_self_of_compactSpace`, in
`TauCeti.AlgebraicTopology.Cohomology.Sphere.Product`). That statement is made for the
cohomology computed from singular chains with coefficients in the unit `ℤ` of `ModuleCat ℤ`.
Fundamental classes of manifolds (`TauCeti.HomologicalOrientation.mapFundamentalClass`) and the
integral cup product `TopCat.integralCup` instead use chains with coefficients in `ULift ℤ`. The
isomorphism `TauCeti.integralCoeffIso : ULift ℤ ≅ ℤ` of chain coefficients identifies the two cup
products (`TopCat.integralCup_singularCohomologyChainCoefficientMap`) and the two Kronecker
pairings (`TopCat.singularKronecker_singularCohomologyChainCoefficientMap`), so the divisibility
holds in the integral convention:

* `⟨x ⌣ x, z⟩` is divisible by `2` for every class `z ∈ H_{2m}(Sᵈ⁺¹ × Y; ℤ)`
  (`TopCat.two_dvd_singularKronecker_integralCup_self_of_compactSpace`);
* in particular `⟨x ⌣ x, f_*[N]⟩` is divisible by `2` for every compact oriented `2m`-manifold `N`
  and continuous map `f : N → Sᵈ⁺¹ × Y`
  (`TauCeti.HomologicalOrientation.two_dvd_evalFundamentalClass_integralCup_self`).

For a closed three-manifold `Y`, `d = 0` and `m = 2`, and `f` a homeomorphism from an oriented
four-manifold onto `S¹ × Y`, this says that the intersection form `x ↦ ⟨x ⌣ x, [S¹ × Y]⟩` on
`H²(S¹ × Y; ℤ)` is even. So no integral class of `S¹ × Y` has square `-1`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.2 (cup products) and Section 3.3 (fundamental classes and Poincaré duality).
-/

public section

noncomputable section

open AlgebraicTopology CategoryTheory MonoidalCategory TauCeti

namespace TopCat

/-- **The integral intersection form of `Sᵈ⁺¹ × Y` is even**: if `Y` is a compact manifold of
dimension below the degree of the cup square, then for an integral class `x` of even degree on
`Sᵈ⁺¹ × Y`, the integral cup square `x ⌣ x` takes values divisible by `2` on every integral
homology class `z` of `Sᵈ⁺¹ × Y`, in the coefficients `ULift ℤ` of fundamental classes. -/
theorem two_dvd_singularKronecker_integralCup_self_of_compactSpace {M E : Type}
    [TopologicalSpace M] [T2Space M] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [ChartedSpace E M] [CompactSpace M] {d n p : ℕ}
    (hn : Module.finrank ℝ E = n)
    (hnp : n < p + p + (d + 1) + (d + 1)) (hp : Even (p + (d + 1)))
    (x : (TopCat.sphere.{0} (d + 1) ⊗ TopCat.of M).integralCohomology (p + (d + 1)))
    (z : ((singularHomologyFunctor (ModuleCat.{0} ℤ) (p + p + (d + 1) + (d + 1))).obj
      (ModuleCat.of ℤ (ULift.{0} ℤ))).obj (TopCat.sphere.{0} (d + 1) ⊗ TopCat.of M)) :
    (2 : ℤ) ∣ ((TopCat.sphere.{0} (d + 1) ⊗ TopCat.of M).singularKronecker ℤ
      (p + p + (d + 1) + (d + 1))
      ((TopCat.sphere.{0} (d + 1) ⊗ TopCat.of M).integralCup (p + (d + 1)) (p + (d + 1))
        (p + p + (d + 1) + (d + 1)) (by omega) x x)).hom z := by
  -- Write `x` as the image of a class with chain coefficients `ℤ` under `integralCoeffIso`.
  obtain ⟨x', rfl⟩ : ∃ x', (TopCat.sphere.{0} (d + 1) ⊗
      TopCat.of M).singularCohomologyChainCoefficientMap ℤ _ integralCoeffIso.hom _ x' = x :=
    ⟨_, by rw [← singularCohomologyChainCoefficientIso_hom]; exact Iso.inv_hom_id_apply _ x⟩
  rw [integralCup_singularCohomologyChainCoefficientMap,
    singularKronecker_singularCohomologyChainCoefficientMap, ModuleCat.hom_comp,
    LinearMap.comp_apply]
  -- The divisibility for chain coefficients `ℤ` is stated for the `ℤ`-linear structure of
  -- `ModuleCat ℤ` as a category of modules, the integral cup product and the Kronecker map for
  -- the `ℤ`-linear structure of a preadditive category; these are the same structure.
  have := Linear.subsingletonInt (ModuleCat.{0} ℤ)
  convert two_dvd_singularKronecker_singularCup_self_of_compactSpace hn hnp hp x' _
  -- The remaining differences are the `Linear ℤ` instance and a proof of the degree equation.
  congr
  · exact Subsingleton.elim _ _
  · exact proof_irrel_heq _ _

end TopCat

namespace TauCeti.HomologicalOrientation

/-- **The integral intersection form of `Sᵈ⁺¹ × Y` on fundamental classes is even**: for a compact
manifold `Y` of dimension below the degree of the cup square, an integral class `x` of even degree
on `Sᵈ⁺¹ × Y`, a compact oriented manifold `N` of the dimension of `x ⌣ x` and a continuous map
`f : N → Sᵈ⁺¹ × Y`, the evaluation `⟨x ⌣ x, f_*[N]⟩` is divisible by `2`. -/
theorem two_dvd_evalFundamentalClass_integralCup_self {N F M E : Type} [TopologicalSpace N]
    [T2Space N] [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [ChartedSpace F N] [CompactSpace N] [TopologicalSpace M] [T2Space M] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [ChartedSpace E M] [CompactSpace M] {d n p : ℕ}
    (o : HomologicalOrientation N F (p + p + (d + 1) + (d + 1)))
    (hF : Module.finrank ℝ F = p + p + (d + 1) + (d + 1)) (hn : Module.finrank ℝ E = n)
    (hnp : n < p + p + (d + 1) + (d + 1)) (hp : Even (p + (d + 1)))
    (f : C(N, (TopCat.sphere.{0} (d + 1) ⊗ TopCat.of M : TopCat)))
    (x : (TopCat.sphere.{0} (d + 1) ⊗ TopCat.of M).integralCohomology (p + (d + 1))) :
    (2 : ℤ) ∣ o.evalFundamentalClass hF (ModuleCat.of ℤ ℤ) f
      ((TopCat.sphere.{0} (d + 1) ⊗ TopCat.of M).integralCup (p + (d + 1)) (p + (d + 1))
        (p + p + (d + 1) + (d + 1)) (by omega) x x) := by
  rw [evalFundamentalClass_apply]
  exact TopCat.two_dvd_singularKronecker_integralCup_self_of_compactSpace hn hnp hp x _

end TauCeti.HomologicalOrientation
