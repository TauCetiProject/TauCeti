/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.UniversalCoefficient
public import TauCeti.AlgebraicTopology.Singular.ProdThomPair

/-!
# Relative cohomology of the Thom pair of a product bundle

Let `B` be a topological space and `F` a real normed space of finite dimension `r`. The relative
singular homology of the Thom pair `(B × F, B × (F ∖ {0}))` of the product bundle vanishes below
degree `r`, and `Hᵣ(B × F, B × (F ∖ {0})) ≅ H₀(B)` naturally in `B`
(`TauCeti.AlgebraicTopology.Singular.ProdThomPair`). This file computes the relative singular
cohomology up to degree `r`, with coefficients `Hom(C(-; R), M)` for modules `R` and `M` over a
commutative ring `k`, `R` projective (for instance `R = M = k = ℤ`):

* `Hⁿ(B × F, B × (F ∖ {0}); R, M) = 0` for `n < r`
  (`TauCeti.isZero_singularCohomology_prodThomPair`);
* `Hʳ(B × F, B × (F ∖ {0}); R, M) ≃ₗ[k] (H₀(B; R) ⟶ M)`, naturally in `B`
  (`TauCeti.prodThomPairSingularCohomologyEquiv`);
* consequently a class in `Hʳ(B × F, B × (F ∖ {0}))` is determined by its restrictions to the fibre
  pairs `(F, F ∖ {0})` over the points of `B`
  (`TauCeti.singularCohomology_prodThomPair_ext`).

Since the relative homology vanishes, and so is projective, below degree `r`, the relative
Kronecker map `Hⁿ ⟶ Hom(Hₙ, M)` is bijective up to degree `r`
(`TopPair.singularKronecker_bijective_of_projective_homology_lt`): no `Ext` term contributes. The
last statement then follows by naturality from the fact that the fibre pairs generate
`Hᵣ(B × F, B × (F ∖ {0}))` (`TauCeti.singularHomology_prodThomPair_hom_ext`).

These are the facts about a single trivializing open set used to construct Thom classes by
Mayer–Vietoris over unions of trivializing open sets: the vanishing below the rank makes the
restriction to the two pieces injective in degree `r`, and the determination by fibres makes local
Thom classes agree on overlaps.

## Main definitions and results

* `TauCeti.isZero_singularCohomology_prodThomPair`: `Hⁿ(B × F, B × (F ∖ {0})) = 0` for
  `n < dim F`.
* `TauCeti.prodThomPairSingularCohomologyEquiv`: `Hʳ(B × F, B × (F ∖ {0}); R, M) ≃ₗ[k]
  (H₀(B; R) ⟶ M)` for `r = dim F`, with its naturality
  `TauCeti.prodThomPairSingularCohomologyEquiv_naturality`.
* `TauCeti.singularCohomology_prodThomPair_ext`: classes in degree `dim F` agreeing on every fibre
  are equal.

## References

* A. Hatcher, *Algebraic Topology*, Section 4.D, Theorem 4D.10 and its proof (the Thom
  isomorphism, first over a trivializing open set and then by Mayer–Vietoris).
* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §10.
-/

public section

noncomputable section

open CategoryTheory Limits Module AlgebraicTopology

universe w

namespace TauCeti

variable {k : Type*} [CommRing k] (R M : ModuleCat.{w} k) [Module.Projective k R]
  (B : Type w) [TopologicalSpace B] {B' : Type w} [TopologicalSpace B']
  (F : Type w) [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

/-- The relative Kronecker map of the Thom pair of a product bundle is bijective up to the rank,
since the relative homology vanishes below it. -/
private theorem singularKronecker_prodThomPair_bijective [Linear k (ModuleCat.{w} k)] {n : ℕ}
    (hn : n ≤ finrank ℝ F) :
    Function.Bijective ((prodThomPair B F).singularKronecker (R := R) (M := M) k n) :=
  (prodThomPair B F).singularKronecker_bijective_of_projective_homology_lt R M n fun _ hj ↦
    (isZero_singularHomology_prodThomPair R B F (hj.trans_le hn)).projective

/-- **The relative cohomology of the Thom pair of a product bundle vanishes below the rank**:
`Hⁿ(B × F, B × (F ∖ {0}); R, M) = 0` for `n < dim F`. -/
theorem isZero_singularCohomology_prodThomPair [Linear k (ModuleCat.{w} k)] {n : ℕ}
    (hn : n < finrank ℝ F) :
    IsZero ((prodThomPair B F).singularCohomology R k M n) :=
  (prodThomPair B F).isZero_singularCohomology_of_isZero_singularHomology R M n fun _ hj ↦
    isZero_singularHomology_prodThomPair R B F (hj.trans_lt hn)

/-- **The top relative cohomology of the Thom pair of a product bundle**: for `F` of dimension
`r`, `Hʳ(B × F, B × (F ∖ {0}); R, M) ≃ₗ[k] (H₀(B; R) ⟶ M)`. A class goes to its evaluation on
`Hᵣ(B × F, B × (F ∖ {0}); R)`, read on `H₀(B; R)` through
`TauCeti.prodThomPairSingularHomologyIso`. -/
def prodThomPairSingularCohomologyEquiv :
    (prodThomPair B F).singularCohomology R k M (finrank ℝ F) ≃ₗ[k]
      (((singularHomologyFunctor (ModuleCat.{w} k) 0).obj R).obj (TopCat.of B) ⟶ M) :=
  (LinearEquiv.ofBijective _ (singularKronecker_prodThomPair_bijective R M B F le_rfl)).trans
    (Linear.homCongr k (prodThomPairSingularHomologyIso R B F 0 (finrank ℝ F)) (Iso.refl M))

/-- `TauCeti.prodThomPairSingularCohomologyEquiv` evaluates a class on relative homology and reads
the result on `H₀(B; R)`. -/
theorem prodThomPairSingularCohomologyEquiv_apply
    (u : (prodThomPair B F).singularCohomology R k M (finrank ℝ F)) :
    prodThomPairSingularCohomologyEquiv R M B F u =
      (prodThomPairSingularHomologyIso R B F 0 (finrank ℝ F)).inv ≫
        (prodThomPair B F).singularKronecker k _ u := by
  simp [prodThomPairSingularCohomologyEquiv, Linear.homCongr_apply]

omit [Module.Projective k R] in
variable {B F} in
/-- Evaluating a class on relative homology and reading the result on `H₀(B; R)` is natural in
continuous maps of the base, for any `k`-linear structure on `ModuleCat k`. -/
private theorem prodThomPairSingularHomologyIso_inv_comp_singularKronecker_naturality
    [Linear k (ModuleCat.{w} k)] (g : C(B, B'))
    (u : (prodThomPair B' F).singularCohomology R k M (finrank ℝ F)) :
    (prodThomPairSingularHomologyIso R B F 0 (finrank ℝ F)).inv ≫
        (prodThomPair B F).singularKronecker k _
          (TopPair.singularCohomologyMap (prodThomPairMap F g) _ u) =
      ((singularHomologyFunctor (ModuleCat.{w} k) 0).obj R).map (TopCat.ofHom g) ≫
        (prodThomPairSingularHomologyIso R B' F 0 (finrank ℝ F)).inv ≫
          (prodThomPair B' F).singularKronecker k _ u := by
  rw [TopPair.singularKronecker_naturality,
    prodThomPairSingularHomologyIso_inv_naturality_assoc R B F g 0 (finrank ℝ F)]

variable {B F} in
/-- The identification `Hʳ(B × F, B × (F ∖ {0}); R, M) ≃ₗ[k] (H₀(B; R) ⟶ M)` is natural in
continuous maps of the base. -/
theorem prodThomPairSingularCohomologyEquiv_naturality (g : C(B, B'))
    (u : (prodThomPair B' F).singularCohomology R k M (finrank ℝ F)) :
    prodThomPairSingularCohomologyEquiv R M B F
        (TopPair.singularCohomologyMap (prodThomPairMap F g) _ u) =
      ((singularHomologyFunctor (ModuleCat.{w} k) 0).obj R).map (TopCat.ofHom g) ≫
        prodThomPairSingularCohomologyEquiv R M B' F u := by
  rw [prodThomPairSingularCohomologyEquiv_apply, prodThomPairSingularCohomologyEquiv_apply]
  exact prodThomPairSingularHomologyIso_inv_comp_singularKronecker_naturality R M g u

variable {R M B F} in
/-- **Classes in the top degree are determined on the fibres**: two classes of
`Hʳ(B × F, B × (F ∖ {0}); R, M)`, `r = dim F`, whose restrictions to the fibre pair
`(F, F ∖ {0})` over every point of `B` agree, are equal. -/
theorem singularCohomology_prodThomPair_ext [Linear k (ModuleCat.{w} k)]
    {u v : (prodThomPair B F).singularCohomology R k M (finrank ℝ F)}
    (h : ∀ b, TopPair.singularCohomologyMap (prodThomPairFiberMap F b) _ u =
      TopPair.singularCohomologyMap (prodThomPairFiberMap F b) _ v) : u = v := by
  -- Compare the evaluations of `u` and `v` on relative homology, which are determined on the
  -- fibres.
  refine (singularKronecker_prodThomPair_bijective R M B F le_rfl).1
    (singularHomology_prodThomPair_hom_ext fun b ↦ ?_)
  rw [← TopPair.singularKronecker_naturality, ← TopPair.singularKronecker_naturality, h b]

end TauCeti
