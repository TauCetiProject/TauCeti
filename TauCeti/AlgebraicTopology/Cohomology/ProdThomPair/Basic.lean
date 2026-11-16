/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.UniversalCoefficient
public import TauCeti.AlgebraicTopology.Singular.ProdThomPair
import TauCeti.AlgebraicTopology.Cohomology.HomotopyInvariance

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

When `F` has a nonzero vector (positive rank), the cohomology of the punctured product bundle
`B × (F ∖ {0})` contains that of the base in every degree: pulling back along the projection is
injective, since the projection has a section
(`TauCeti.leftInverse_singularCohomologyMap_prodThomPairPuncturedSection` and
`TauCeti.injective_singularCohomologyMap_prodThomPairPuncturedProj`). The cohomology of the total
space `B × F` is that of the base when `F` is contractible
(`TauCeti.exists_singularCohomologyMap_prodThomPairProj_eq`). From the long exact sequence of the
pair, these two facts identify the cohomology of the Thom pair with a complement of the base in
that of `B × (F ∖ {0})`, through the connecting morphism
(`TauCeti.bijective_prodThomPair_singularCohomologyδ_comp_inr`). This computes the cohomology of
the Thom pair in degrees at least the rank
(`TauCeti.AlgebraicTopology.Cohomology.ProdThomPair.Sphere` and
`TauCeti.AlgebraicTopology.Cohomology.ProdThomPair.Line`).

## Main definitions and results

* `TauCeti.isZero_singularCohomology_prodThomPair`: `Hⁿ(B × F, B × (F ∖ {0})) = 0` for
  `n < dim F`.
* `TauCeti.prodThomPairSingularCohomologyEquiv`: `Hʳ(B × F, B × (F ∖ {0}); R, M) ≃ₗ[k]
  (H₀(B; R) ⟶ M)` for `r = dim F`, with its naturality
  `TauCeti.prodThomPairSingularCohomologyEquiv_naturality`.
* `TauCeti.singularCohomology_prodThomPair_ext`: classes in degree `dim F` agreeing on every fibre
  are equal.
* `TauCeti.leftInverse_singularCohomologyMap_prodThomPairPuncturedSection`,
  `TauCeti.injective_singularCohomologyMap_prodThomPairPuncturedProj` and
  `TauCeti.exists_singularCohomologyMap_prodThomPairProj_eq`: the cohomology of the base injects
  into that of `B × (F ∖ {0})` when `F` has a nonzero vector, and is all of that of `B × F` for
  contractible `F`.
* `TauCeti.bijective_prodThomPair_singularCohomologyδ_comp_inr`: for contractible `E` with a
  nonzero vector and a decomposition `D` of `Hⁿ(B × (E ∖ {0}))` whose first factor is `π^*`,
  `c ↦ δ (D (0, c))` is a bijection onto `Hⁿ⁺¹(B × E, B × (E ∖ {0}))`.

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

section Punctured

omit [Module.Projective k R]

variable {B} {E : Type w} [TopologicalSpace E] [Zero E]

/-- Pulling back along the projection `B × (E ∖ {0}) → B` and then along the section
`b ↦ (b, v)` at a nonzero vector `v` (`TauCeti.prodThomPairPuncturedSection`) is the identity. -/
theorem leftInverse_singularCohomologyMap_prodThomPairPuncturedSection [Linear k (ModuleCat.{w} k)]
    {v : E} (hv : v ≠ 0) (m : ℕ) :
    Function.LeftInverse
      (TopCat.singularCohomologyMap (R := R) (k := k) (M := M)
        (prodThomPairPuncturedSection B E hv) m)
      (TopCat.singularCohomologyMap (prodThomPairPuncturedProj B E) m) := fun b ↦ by
  rw [← ConcreteCategory.comp_apply, ← TopCat.singularCohomologyMap_comp,
    prodThomPairPuncturedSection_comp_prodThomPairPuncturedProj, TopCat.singularCohomologyMap_id,
    ConcreteCategory.id_apply]

/-- Pulling back along the projection `B × (E ∖ {0}) → B` is injective whenever `E` has a nonzero
vector, since the projection has a section. -/
theorem injective_singularCohomologyMap_prodThomPairPuncturedProj [Linear k (ModuleCat.{w} k)]
    {v : E} (hv : v ≠ 0) (m : ℕ) :
    Function.Injective (TopCat.singularCohomologyMap (R := R) (k := k) (M := M)
      (prodThomPairPuncturedProj B E) m) :=
  (leftInverse_singularCohomologyMap_prodThomPairPuncturedSection R M hv m).injective

/-- **Classes of a product bundle with contractible fibre come from the base**: every class of
`Hᵐ(B × E; R, M)` is pulled back along the projection `B × E → B`, since that projection is a
homotopy equivalence. -/
theorem exists_singularCohomologyMap_prodThomPairProj_eq [Linear k (ModuleCat.{w} k)]
    [ContractibleSpace E] (m : ℕ) (y : (prodThomPair B E).fst.singularCohomology R k M m) :
    ∃ b, TopCat.singularCohomologyMap (prodThomPairProj B E) m b = y := by
  have := (ContinuousMap.HomotopyEquiv.prodContractible B E).isIso_singularCohomologyMap R k M m
  rw [ContinuousMap.HomotopyEquiv.prodContractible_toFun] at this
  have hproj : TopCat.ofHom ContinuousMap.fst = prodThomPairProj B E :=
    TopCat.ext fun p ↦ (prodThomPairProj_apply E p).symm
  have : IsIso (TopCat.singularCohomologyMap (R := R) (k := k) (M := M)
    (prodThomPairProj B E) m) := hproj ▸ this
  refine ⟨inv (TopCat.singularCohomologyMap (prodThomPairProj B E) m) y, ?_⟩
  rw [← ConcreteCategory.comp_apply, IsIso.inv_hom_id, ConcreteCategory.id_apply]

/-- **The cohomology of the Thom pair from that of the punctured product.** Let
`E` be contractible with a nonzero vector, and let
`D : Hⁿ(B; R, M) × Hᵖ(B; R, M) ≃ Hⁿ(B × (E ∖ {0}); R, M)` be a linear equivalence that is the
pullback along the projection `π : B × (E ∖ {0}) → B` on the first factor. Then, for
`m = n + 1`, `c ↦ δ (D (0, c))` is a bijection `Hᵖ(B; R, M) → Hᵐ(B × E, B × (E ∖ {0}); R, M)`,
where `δ` is the connecting morphism of the pair: in its long exact sequence the restriction from
`B × E` to `B × (E ∖ {0})` is injective with image the first factor of `D`. -/
theorem bijective_prodThomPair_singularCohomologyδ_comp_inr [Linear k (ModuleCat.{w} k)]
    [ContractibleSpace E] {v : E} (hv : v ≠ 0) {n m p : ℕ} (h : n + 1 = m)
    (D : ((TopCat.of B).singularCohomology R k M n × (TopCat.of B).singularCohomology R k M p) ≃ₗ[k]
      (prodThomPair B E).snd.singularCohomology R k M n)
    (hD : ∀ b, D (b, 0) = TopCat.singularCohomologyMap (prodThomPairPuncturedProj B E) n b) :
    Function.Bijective (((prodThomPair B E).singularCohomologyδ R k M n m).hom ∘ₗ
      D.toLinearMap ∘ₗ LinearMap.inr k _ _) := by
  let P := prodThomPair B E
  -- `D (b, 0)` is the restriction of the class `π^* b` of `B × E`.
  have hD' (b) : D (b, 0) = TopCat.singularCohomologyMap P.map n
      (TopCat.singularCohomologyMap (prodThomPairProj B E) n b) := by
    rw [hD, ← ConcreteCategory.comp_apply, ← TopCat.singularCohomologyMap_comp,
      map_comp_prodThomPairProj]
  refine ⟨(injective_iff_map_eq_zero _).2 fun c hc ↦ ?_, fun z ↦ ?_⟩
  · -- If `δ (D (0, c)) = 0`, then `D (0, c)` is restricted from `B × E`, where every class is
    -- pulled back from `B`, so `D (0, c) = D (b, 0)` for some `b`.
    obtain ⟨y, hy⟩ := (ShortComplex.moduleCat_exact_iff _).1
      (P.singularCohomology_exact_subspace R k M n m h) _ hc
    obtain ⟨b, rfl⟩ := exists_singularCohomologyMap_prodThomPairProj_eq R M _ y
    rw [← hD'] at hy
    exact congrArg Prod.snd (D.injective hy).symm
  · -- A class `z` of the pair maps to a class of `B × E` pulled back from `B` whose restriction to
    -- `B × (E ∖ {0})` vanishes; since `π^*` is injective, `z` maps to zero, so `z = δ (D (b, c))`
    -- by exactness, and `δ (D (b, 0)) = 0` as `D (b, 0)` is restricted from `B × E`.
    obtain ⟨b, hb⟩ := exists_singularCohomologyMap_prodThomPairProj_eq R M _
      (P.singularCohomologyπ R k M m z)
    have hπ : P.singularCohomologyπ R k M m z = 0 := by
      have h0 := ConcreteCategory.congr_hom
        (P.singularCohomologyπ_comp_singularCohomologyMap R k M m) z
      rw [ConcreteCategory.comp_apply, ← hb, ← ConcreteCategory.comp_apply,
        ← TopCat.singularCohomologyMap_comp, map_comp_prodThomPairProj] at h0
      rw [← hb, injective_singularCohomologyMap_prodThomPairPuncturedProj R M hv m
        (h0.trans (map_zero _).symm), map_zero]
    obtain ⟨x, rfl⟩ : ∃ x, (P.singularCohomologyδ R k M n m h) x = z :=
      (ShortComplex.moduleCat_exact_iff _).1 (P.singularCohomology_exact_relative R k M n m h) z hπ
    obtain ⟨⟨b', c⟩, rfl⟩ := D.surjective x
    refine ⟨c, ?_⟩
    have hδ : (P.singularCohomologyδ R k M n m h) (D (b', 0)) = 0 := by
      rw [hD' b', ← ConcreteCategory.comp_apply,
        P.singularCohomologyMap_comp_singularCohomologyδ R k M n m h]
      simp only [ModuleCat.hom_zero, LinearMap.zero_apply]
    have hbc : ((b', c) : _ × _) = (b', 0) + (0, c) := by simp
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.inr_apply,
      LinearEquiv.coe_coe]
    rw [hbc, map_add, map_add, hδ, zero_add]

end Punctured

end TauCeti
