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

Connectedness is what makes both statements true: on a compact connected manifold, `H⁰`, `H₀`,
`Hₙ` and `Hⁿ` are all one-dimensional over `ℚ`. The argument does not go through the general
duality theorem. In degree zero, the class `1 ∈ H⁰(M; ℚ)` of the constant cocycle caps `[M]` to
`[M]` (`TauCeti.singularCap_unit`), and `[M]` spans `Hₙ(M; ℚ)`
(`TauCeti.HomologicalOrientation.rationalFundamentalClassEquiv`). In the top degree, the
augmentation `ε : H₀(M; ℚ) → ℚ` of `[M] ⌢ α` is the Kronecker pairing `⟨α, [M]⟩`
(`TopCat.singularCap_comp_singularHomology₀ε`), and over a field the Kronecker pairing identifies
`Hⁿ(M; ℚ)` with the dual of the line `Hₙ(M; ℚ)`.

The top-degree identity rests on a fact valid for every space and coefficient object: the
Kronecker pairing of the class of a constant `0`-cocycle with value `e` is the augmentation of
zeroth homology followed by `e` (`TopCat.singularKronecker_constSingularCocycle`). For `e` the
identity, the unit class `1 ∈ H⁰(X; R)` pairs with zeroth homology as the augmentation.

All cohomology and homology here has coefficients in the tensor unit `𝟙_ (ModuleCat ℚ)`, that is
`ℚ` itself, and the cap product is taken along the unitors of `𝟙_ (ModuleCat ℚ)`, as in
`TopCat.singularCap_comp_singularKronecker`.

## Main results

* `TopCat.singularKronecker_constSingularCocycle`: `⟨[const e], x⟩ = e (ε x)` on `H₀`.
* `TopCat.singularCap_comp_singularHomology₀ε`: `ε (x ⌢ α) = ⟨α, x⟩` for `α` of degree `n` and
  `x ∈ Hₙ`.
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

namespace TopCat

section Kronecker

variable {C : Type u} [Category.{v} C] [Abelian C] [HasCoproducts.{w} C] {R M : C}

/-- **The Kronecker pairing of a constant `0`-cocycle**: evaluating the class of the constant
`0`-cocycle with value `e : R ⟶ M` on zeroth homology is the augmentation followed by `e`. For `e`
the identity, the unit class of `H⁰(X; R)` pairs with zeroth homology as the augmentation. -/
lemma singularKronecker_constSingularCocycle (X : TopCat.{w}) (k : Type*) [Ring k] [Linear k C]
    (e : R ⟶ M) :
    X.singularKronecker k 0
        ((X.singularCochainComplex R k M).homologyπ 0 (X.constSingularCocycle k e)) =
      X.singularHomology₀ε R ≫ e := by
  apply (cancel_epi (((toSSet.obj X).chainComplex R).homologyπ 0)).1
  apply (cancel_epi (((toSSet.obj X).chainComplex R).cycles₀Iso.inv)).1
  refine SSet.chainComplex_hom_ext fun x ↦ ?_
  -- A vertex, viewed as a cycle, is evaluated by the constant cochain to `e`, and its class is
  -- sent by the augmentation to the identity.
  have hx : (toSSet.obj X).ιChainComplex x ≫ ((toSSet.obj X).chainComplex R).cycles₀Iso.inv =
      ((toSSet.obj X).chainComplex R).liftCycles ((toSSet.obj X).ιChainComplex x) 0
        (by simp) (by simp) := by
    apply (cancel_mono (((toSSet.obj X).chainComplex R).iCycles 0)).1
    simp
  simp only [reassoc_of% hx, singularHomology₀ε, singularKronecker_homologyπ,
    HomologicalComplex.liftCycles_i_assoc, iCycles_constSingularCocycle,
    SSet.ιChainComplex_constCochain]
  exact (SSet.liftCycles_ιChainComplex_homologyπ_homology₀ε_assoc (X := toSSet.obj X) R x e).symm

end Kronecker

section Cap

variable {C : Type u} [Category.{v} C] [Abelian C] [HasCoproducts.{w} C] [MonoidalCategory C]
  [MonoidalPreadditive C]

/-- **The augmentation of a cap product into degree zero**, `ε (x ⌢ α) = ⟨α, x⟩`: capping a class
of degree `n` with a class `α` of the same degree, along the unitors of the tensor unit, and then
applying the augmentation of zeroth homology is the Kronecker pairing with `α`. -/
theorem singularCap_comp_singularHomology₀ε (X : TopCat.{w}) (k : Type*) [CommRing k]
    [Linear k C] [MonoidalLinear k C] (n : ℕ) (h : n + 0 = n)
    (α : X.singularCohomology (𝟙_ C) k (𝟙_ C) n) :
    X.singularCap k (λ_ (𝟙_ C)).inv (λ_ (𝟙_ C)).hom n 0 n h α ≫
        X.singularHomology₀ε (𝟙_ C) =
      X.singularKronecker k n α := by
  have hε := X.singularKronecker_constSingularCocycle k (𝟙 (𝟙_ C))
  rw [Category.comp_id] at hε
  rw [← hε, singularCap_comp_singularKronecker,
    singularCup_constSingularCocycle_right X k (η := 𝟙 (𝟙_ C)) (by simp [unitors_inv_equal])
      (by simp [unitors_equal])]

end Cap

end TopCat

namespace TauCeti.HomologicalOrientation

variable {M E : Type} [TopologicalSpace M] [T2Space M]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [ChartedSpace E M]
  {n : ℕ} (o : HomologicalOrientation M E n) (hn : finrank ℝ E = n)
  [CompactSpace M] [ConnectedSpace M]

omit [T2Space M] [FiniteDimensional ℝ E] [CompactSpace M] in
include E in
/-- A connected manifold is path-connected. -/
private theorem pathConnectedSpace : PathConnectedSpace (TopCat.of M) :=
  have := ChartedSpace.locallyPathConnectedSpace E M
  PathConnectedSpace.of_locallyPathConnectedSpace (X := M)

omit [T2Space M] [FiniteDimensional ℝ E] [CompactSpace M] in
include E in
/-- On a connected manifold, zeroth rational homology is one-dimensional. -/
private theorem finrank_singularHomology_zero :
    finrank ℚ (((singularHomologyFunctor (ModuleCat.{0} ℚ) 0).obj
      (𝟙_ (ModuleCat.{0} ℚ))).obj (TopCat.of M)) = 1 := by
  have := pathConnectedSpace (M := M) (E := E)
  exact ((asIso ((TopCat.of M).singularHomology₀ε
    (𝟙_ (ModuleCat.{0} ℚ)))).toLinearEquiv.finrank_eq).trans (finrank_self ℚ)

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
    change (X.singularCap ℚ (λ_ (𝟙_ (ModuleCat.{0} ℚ))).inv
      (λ_ (𝟙_ (ModuleCat.{0} ℚ))).hom 0 n n (Nat.zero_add n) _).hom _ = _
    rw [TauCeti.singularCap_unit]
    rfl
  -- Both sides are lines: `H⁰(M; ℚ)` is dual to `H₀(M; ℚ)`.
  have h0 : finrank ℚ (X.singularCohomology (𝟙_ (ModuleCat.{0} ℚ)) ℚ
      (𝟙_ (ModuleCat.{0} ℚ)) 0) = 1 :=
    (X.finrank_singularCohomology 0).trans (finrank_singularHomology_zero (E := E))
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
  have := pathConnectedSpace (M := M) (E := E)
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
      ε.hom.hom x • (o.rationalFundamentalClassEquiv hn).symm.toLinearMap
    refine ⟨(X.singularCohomologyDualEquiv n).symm φ, ε.toLinearEquiv.injective ?_⟩
    change ε.hom ((X.singularCap ℚ (λ_ (𝟙_ (ModuleCat.{0} ℚ))).inv
      (λ_ (𝟙_ (ModuleCat.{0} ℚ))).hom n 0 n (add_zero n) _).hom _) = _
    rw [← ConcreteCategory.comp_apply]
    simp only [ε, asIso_hom]
    rw [X.singularCap_comp_singularHomology₀ε ℚ n,
      TopCat.singularKronecker_singularCohomologyDualEquiv_symm]
    simp only [φ, ModuleCat.hom_ofHom, LinearMap.smul_apply, LinearEquiv.coe_coe]
    rw [rationalFundamentalClass_def, LinearEquiv.symm_apply_apply, smul_eq_mul, mul_one]
    rfl
  have h0 : finrank ℚ (X.singularCohomology (𝟙_ (ModuleCat.{0} ℚ)) ℚ
      (𝟙_ (ModuleCat.{0} ℚ)) n) = 1 :=
    (X.finrank_singularCohomology n).trans (o.finrank_singularHomology_top hn)
  have : FiniteDimensional ℚ (X.singularCohomology (𝟙_ (ModuleCat.{0} ℚ)) ℚ
      (𝟙_ (ModuleCat.{0} ℚ)) n) := Module.finite_of_finrank_eq_succ h0
  have : FiniteDimensional ℚ (((singularHomologyFunctor (ModuleCat.{0} ℚ) 0).obj
      (𝟙_ (ModuleCat.{0} ℚ))).obj X) :=
    Module.finite_of_finrank_eq_succ (finrank_singularHomology_zero (E := E))
  exact ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (h0.trans (finrank_singularHomology_zero (E := E)).symm)).2 hsurj, hsurj⟩

end TauCeti.HomologicalOrientation
