/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.Cap.Kronecker
public import TauCeti.AlgebraicTopology.Cohomology.Cap.Unit
public import TauCeti.AlgebraicTopology.Cohomology.UniversalCoefficient.Field
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.FundamentalClass
public import TauCeti.AlgebraicTopology.Singular.Reduced

/-!
# Capping with the rational fundamental class in degrees zero and top

Let `M` be a compact connected topological `n`-manifold with an orientation `o`
(`TauCeti.HomologicalOrientation M E n`) and rational fundamental class `[M] ∈ Hₙ(M; ℚ)`. This
file proves closed Poincaré duality over `ℚ` in the two extreme degrees: capping with `[M]` is
bijective

* from `H⁰(M; ℚ)` to `Hₙ(M; ℚ)`
  (`TauCeti.HomologicalOrientation.bijective_singularCap_rationalFundamentalClass_zero`), and
* from `Hⁿ(M; ℚ)` to `H₀(M; ℚ)`
  (`TauCeti.HomologicalOrientation.bijective_singularCap_rationalFundamentalClass_top`).

Connectedness is what these proofs use: on a compact connected manifold, `H⁰`, `H₀`, `Hₙ` and `Hⁿ`
are all one-dimensional over `ℚ`, so a surjective linear map between them is bijective. The argument
does not go through the general duality theorem. In degree zero, the class `1 ∈ H⁰(M; ℚ)` of the
constant cocycle caps `[M]` to `[M]` (`TauCeti.singularCap_unit`), and `[M]` spans `Hₙ(M; ℚ)`
(`TauCeti.HomologicalOrientation.rationalFundamentalClassEquiv`). In the top degree, the
augmentation `ε : H₀(M; ℚ) → ℚ` of `[M] ⌢ α` is the Kronecker pairing `⟨α, [M]⟩`
(`TopCat.singularCap_comp_singularHomology₀ε`), and over a field the Kronecker pairing identifies
`Hⁿ(M; ℚ)` with the dual of the line `Hₙ(M; ℚ)`.

All cohomology and homology here has coefficients in the tensor unit `𝟙_ (ModuleCat ℚ)`, that is
`ℚ` itself, and the cap product is taken along the unitors of `𝟙_ (ModuleCat ℚ)`, as in
`TopCat.singularCap_comp_singularKronecker`.

## Main results

* `TauCeti.HomologicalOrientation.bijective_singularCap_rationalFundamentalClass_zero` and
  `TauCeti.HomologicalOrientation.bijective_singularCap_rationalFundamentalClass_top`: closed
  rational duality in degrees `0` and `n` for a compact connected oriented manifold.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.3, Theorem 3.30.
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory AlgebraicTopology Module

universe w v u

namespace TauCeti.HomologicalOrientation

variable {M E : Type} [TopologicalSpace M] [T2Space M]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [ChartedSpace E M]
  {n : ℕ} (o : HomologicalOrientation M E n) (hn : finrank ℝ E = n)
  [CompactSpace M] [ConnectedSpace M]

include o hn in
/-- On a compact connected oriented manifold, top rational homology is one-dimensional. -/
private theorem finrank_singularHomology_top :
    finrank ℚ (((singularHomologyFunctor (ModuleCat.{0} ℚ) n).obj
      (𝟙_ (ModuleCat.{0} ℚ))).obj (TopCat.of M)) = 1 :=
  (o.rationalFundamentalClassEquiv hn).finrank_eq.symm.trans (finrank_self ℚ)

/-- **Closed rational Poincaré duality in degree zero**: on a compact connected oriented
`n`-manifold, capping with the rational fundamental class, `α ↦ [M] ⌢ α`, is bijective from
`H⁰(M; ℚ)` to `Hₙ(M; ℚ)`. The unit class caps `[M]` to `[M]`. -/
theorem bijective_singularCap_rationalFundamentalClass_zero :
    Function.Bijective fun α : (TopCat.of M).singularCohomology
        (𝟙_ (ModuleCat.{0} ℚ)) ℚ (𝟙_ (ModuleCat.{0} ℚ)) 0 ↦
      ((TopCat.of M).singularCap ℚ (λ_ (𝟙_ (ModuleCat.{0} ℚ))).inv
        (λ_ (𝟙_ (ModuleCat.{0} ℚ))).hom 0 n n (zero_add n) α).hom
        (o.rationalFundamentalClass hn) := by
  let X := TopCat.of M
  have := ChartedSpace.locallyPathConnectedSpace E M
  have : PathConnectedSpace X := PathConnectedSpace.of_locallyPathConnectedSpace (X := M)
  let f : X.singularCohomology (𝟙_ (ModuleCat.{0} ℚ)) ℚ (𝟙_ (ModuleCat.{0} ℚ)) 0 →ₗ[ℚ]
      ((singularHomologyFunctor (ModuleCat.{0} ℚ) n).obj (𝟙_ (ModuleCat.{0} ℚ))).obj X :=
    { toFun α := (X.singularCap ℚ (λ_ (𝟙_ (ModuleCat.{0} ℚ))).inv
        (λ_ (𝟙_ (ModuleCat.{0} ℚ))).hom 0 n n (zero_add n) α).hom
        (o.rationalFundamentalClass hn)
      map_add' α β := by simp
      map_smul' c α := by simp }
  -- The unit class caps `[M]` to `[M]`, and `[M]` spans `Hₙ(M; ℚ)`.
  have hsurj : Function.Surjective f := by
    intro x
    obtain ⟨c, rfl⟩ := (o.rationalFundamentalClassEquiv hn).surjective x
    refine ⟨c • (X.singularCochainComplex (𝟙_ (ModuleCat.{0} ℚ)) ℚ
      (𝟙_ (ModuleCat.{0} ℚ))).homologyπ 0 (X.constSingularCocycle ℚ (𝟙 _)), ?_⟩
    rw [map_smul, rationalFundamentalClassEquiv_apply]
    congr 1
    simp only [f, LinearMap.coe_mk, AddHom.coe_mk, TauCeti.singularCap_unit, ModuleCat.hom_id,
      LinearMap.id_apply]
  -- Both sides are lines: `H⁰(M; ℚ)` is dual to `H₀(M; ℚ)`.
  have h0 : finrank ℚ (X.singularCohomology (𝟙_ (ModuleCat.{0} ℚ)) ℚ
      (𝟙_ (ModuleCat.{0} ℚ)) 0) = 1 :=
    (X.finrank_singularCohomology 0).trans
      ((ModuleCat.finrank_singularHomology_zero_of_pathConnectedSpace _).trans (finrank_self ℚ))
  have : FiniteDimensional ℚ (X.singularCohomology (𝟙_ (ModuleCat.{0} ℚ)) ℚ
      (𝟙_ (ModuleCat.{0} ℚ)) 0) := Module.finite_of_finrank_eq_succ h0
  have : FiniteDimensional ℚ (((singularHomologyFunctor (ModuleCat.{0} ℚ) n).obj
      (𝟙_ (ModuleCat.{0} ℚ))).obj X) :=
    Module.finite_of_finrank_eq_succ (o.finrank_singularHomology_top hn)
  exact ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (h0.trans (o.finrank_singularHomology_top hn).symm)).2 hsurj, hsurj⟩

/-- **Closed rational Poincaré duality in the top degree**: on a compact connected oriented
`n`-manifold, capping with the rational fundamental class, `α ↦ [M] ⌢ α`, is bijective from
`Hⁿ(M; ℚ)` to `H₀(M; ℚ)`. The augmentation of `[M] ⌢ α` is the Kronecker pairing `⟨α, [M]⟩`. -/
theorem bijective_singularCap_rationalFundamentalClass_top :
    Function.Bijective fun α : (TopCat.of M).singularCohomology
        (𝟙_ (ModuleCat.{0} ℚ)) ℚ (𝟙_ (ModuleCat.{0} ℚ)) n ↦
      ((TopCat.of M).singularCap ℚ (λ_ (𝟙_ (ModuleCat.{0} ℚ))).inv
        (λ_ (𝟙_ (ModuleCat.{0} ℚ))).hom n 0 n (add_zero n) α).hom
        (o.rationalFundamentalClass hn) := by
  let X := TopCat.of M
  have := ChartedSpace.locallyPathConnectedSpace E M
  have : PathConnectedSpace X := PathConnectedSpace.of_locallyPathConnectedSpace (X := M)
  let f : X.singularCohomology (𝟙_ (ModuleCat.{0} ℚ)) ℚ (𝟙_ (ModuleCat.{0} ℚ)) n →ₗ[ℚ]
      ((singularHomologyFunctor (ModuleCat.{0} ℚ) 0).obj (𝟙_ (ModuleCat.{0} ℚ))).obj X :=
    { toFun α := (X.singularCap ℚ (λ_ (𝟙_ (ModuleCat.{0} ℚ))).inv
        (λ_ (𝟙_ (ModuleCat.{0} ℚ))).hom n 0 n (add_zero n) α).hom
        (o.rationalFundamentalClass hn)
      map_add' α β := by simp
      map_smul' c α := by simp }
  -- After the augmentation, capping with `[M]` is the Kronecker pairing with `[M]`, which is onto
  -- since a linear form on the line `Hₙ(M; ℚ)` may take any value on `[M]`.
  have hsurj : Function.Surjective f := by
    intro x
    let ε := asIso (X.singularHomology₀ε (𝟙_ (ModuleCat.{0} ℚ)))
    let φ : Dual ℚ (((singularHomologyFunctor (ModuleCat.{0} ℚ) n).obj
        (𝟙_ (ModuleCat.{0} ℚ))).obj X) :=
      X.singularHomology₀ε (𝟙_ (ModuleCat.{0} ℚ)) x •
        (o.rationalFundamentalClassEquiv hn).symm.toLinearMap
    refine ⟨(X.singularCohomologyDualEquiv n).symm φ, ε.toLinearEquiv.injective ?_⟩
    simp only [Iso.toLinearEquiv_apply, f, LinearMap.coe_mk, AddHom.coe_mk, ε, asIso_hom]
    rw [← ConcreteCategory.comp_apply, X.singularCap_comp_singularHomology₀ε ℚ n,
      TopCat.singularKronecker_singularCohomologyDualEquiv_symm]
    simp only [φ, ModuleCat.hom_ofHom, LinearMap.smul_apply, LinearEquiv.coe_coe]
    rw [rationalFundamentalClass_def, LinearEquiv.symm_apply_apply, smul_eq_mul, mul_one]
  have h0 : finrank ℚ (X.singularCohomology (𝟙_ (ModuleCat.{0} ℚ)) ℚ
      (𝟙_ (ModuleCat.{0} ℚ)) n) = 1 :=
    (X.finrank_singularCohomology n).trans (o.finrank_singularHomology_top hn)
  have : FiniteDimensional ℚ (X.singularCohomology (𝟙_ (ModuleCat.{0} ℚ)) ℚ
      (𝟙_ (ModuleCat.{0} ℚ)) n) := Module.finite_of_finrank_eq_succ h0
  have h₀ : finrank ℚ (((singularHomologyFunctor (ModuleCat.{0} ℚ) 0).obj
      (𝟙_ (ModuleCat.{0} ℚ))).obj X) = 1 :=
    (ModuleCat.finrank_singularHomology_zero_of_pathConnectedSpace _).trans (finrank_self ℚ)
  have : FiniteDimensional ℚ (((singularHomologyFunctor (ModuleCat.{0} ℚ) 0).obj
      (𝟙_ (ModuleCat.{0} ℚ))).obj X) := Module.finite_of_finrank_eq_succ h₀
  exact ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank (h0.trans h₀.symm)).2 hsurj,
    hsurj⟩

end TauCeti.HomologicalOrientation
