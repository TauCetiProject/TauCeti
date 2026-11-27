/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Monoidal.Cap.Connecting
public import TauCeti.AlgebraicTopology.Cohomology.Cap.Kronecker
public import TauCeti.AlgebraicTopology.Cohomology.HomotopyInvariance
public import TauCeti.AlgebraicTopology.Singular.MappingTorus.BaseCircle
public import TauCeti.AlgebraicTopology.Singular.MappingTorus.FibreClass

/-!
# The Wang connecting morphism and cap products

Let `T_φ` be the mapping torus of a homeomorphism `φ : F ≃ₜ F`, with fibre inclusion
`i : F → T_φ` (`TauCeti.MappingTorus.incl`) and Wang connecting morphism
`δ : Hₙ₊₁(T_φ) ⟶ Hₙ(F)` (`TauCeti.MappingTorus.wangδ`). This file shows that `δ` is a morphism of
modules over the cohomology ring of `T_φ`, up to the Koszul sign: for a class `α ∈ Hᵖ(T_φ)` and a
class `x ∈ Hₙ₊₁(T_φ)`,

`δ (x ⌢ α) = (-1)ᵖ δ x ⌢ i^*α`

(`TauCeti.MappingTorus.singularCap_comp_wangδ`). The connecting morphism is that of the short exact
sequence `0 ⟶ C(F × ℝ) ⟶ C(F × ℝ) ⟶ C(T_φ) ⟶ 0` of the infinite cyclic cover, followed by the
projection `F × ℝ → F`. Capping with `α` and with its pullback to the cover is compatible with
both maps of the sequence, since the covering map is invariant under the deck transformation; so
the cap product commutes with the connecting morphism up to sign
(`TauCeti.ChainComplex.cap_comp_δ`). The pullback of `α` to the cover is pulled back from `F`
along the projection, through the inclusion at height zero, which is a homotopy inverse of the
projection, and the projection formula moves it to `F`.

**The base class.** Together with the evaluation of the base class `[dt] ∈ H¹(T_φ; ℤ)`
(`TauCeti.MappingTorus.baseClass`) through the Wang class
(`TauCeti.MappingTorus.singularKronecker_baseClass_apply_eq_neg`), this computes cup products with
`[dt]`: there is a sign `s = ±1` (in fact `s = -1`), the same for every mapping torus, with

`⟨v ⌣ [dt], y⟩ = s (-1)ᵖ ⟨i^* v, δ y⟩`

for all `v ∈ Hᵖ(T_φ; ℤ)` and `y ∈ Hₚ₊₁(T_φ; ℤ)`
(`TauCeti.MappingTorus.exists_singularCupPairing_baseClass_apply`). Geometrically, capping with
`[dt]` intersects a cycle with a fibre.

**The fibre class.** Let `F` be a closed connected oriented `(n + 1)`-manifold and `φ` preserve its
fundamental class `[F]`. Then `φ` acts as the identity on `Hₙ₊₁(F; ℤ)`, so `δ` is onto
`Hₙ₊₁(F; ℤ)` by the exactness of the Wang sequence
(`TauCeti.MappingTorus.epi_wangδ_of_mapFundamentalClass_eq`), and some `y ∈ Hₙ₊₂(T_φ; ℤ)`
satisfies `⟨v ⌣ [dt], y⟩ = ⟨v, i_*[F]⟩` for every `v ∈ Hⁿ⁺¹(T_φ; ℤ)`
(`TauCeti.MappingTorus.exists_singularCupPairing_baseClass_eq_evalFundamentalClass`); it is a
class with `δ y = ±[F]`. For a surface mapping torus `Y_φ` and a class `v` pairing to one with
the fibre class this gives `⟨v ⌣ [dt], y⟩ = 1`. Against the class `[ℝ / pℤ] × y` of
`(ℝ / pℤ) × Y_φ`, the cup pairing of `pr₂^* v` with `t = θ_p ⌣ pr₂^* [dt]` is `⟨v ⌣ [dt], y⟩`
(`TopCat.singularCupPairing_snd_fst_snd_addCircle_singularHomologyCross`), and `pr₂^* v` and `t`
are isotropic (`TopCat.singularCupPairing_snd_snd_addCircle_singularHomologyCross`,
`TopCat.singularCupPairing_fst_snd_fst_snd_addCircle_singularHomologyCross`). So `pr₂^* v` and `t`
form a hyperbolic pair of that pairing, the input of
`LinearMap.BilinForm.sigPos_toQuadraticMap_baseChange_eq_one_of_isOfFinAddOrder_span`. That `y`
is the fundamental class of the mapping torus is not proved here.

## Main results

* `TauCeti.MappingTorus.singularCap_comp_wangδ`: `δ (x ⌢ α) = (-1)ᵖ δ x ⌢ i^*α`.
* `TauCeti.MappingTorus.exists_singularCupPairing_baseClass_apply`:
  `⟨v ⌣ [dt], y⟩ = s (-1)ᵖ ⟨i^* v, δ y⟩` for a universal sign `s = ±1`.
* `TauCeti.MappingTorus.exists_singularCupPairing_baseClass_eq_evalFundamentalClass`:
  `⟨v ⌣ [dt], y⟩ = ⟨v, i_*[F]⟩` for some `y ∈ Hₙ₊₂(T_φ; ℤ)` with `δ y = ±[F]` and every
  `v ∈ Hⁿ⁺¹(T_φ; ℤ)`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 2.2, Example 2.48 (the Wang sequence of a mapping torus), and Section 3.3 (the cap
  product).
* J. Milnor, *Infinite cyclic coverings*, Conference on the Topology of Manifolds (1968),
  Section 1.
* C. H. Taubes, *The Seiberg–Witten and Gromov invariants*, Math. Res. Lett. 2 (1995), 221–238.
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory AlgebraicTopology HomologicalComplex

universe w v u

namespace TauCeti.MappingTorus

attribute [local instance] hasFiniteCoproducts_of_hasCoproducts
attribute [local instance] HasFiniteBiproducts.of_hasFiniteCoproducts

section Cap

variable {F : Type w} [TopologicalSpace F] (φ : F ≃ₜ F)
  {C : Type u} [Category.{v} C] [Abelian C] [HasCoproducts.{w} C] {R S T M N : C}

/-- **Classes of a mapping torus on its infinite cyclic cover**: the pullback of a class `α` of
`T_φ` along the covering map `F × ℝ → T_φ` is the pullback, along the projection `F × ℝ → F`, of
the restriction `i^*α` of `α` to the fibre. -/
theorem singularCohomologyMap_coverMap (k : Type*) [Ring k] [Linear k C] (p : ℕ)
    (α : (TopCat.of (MappingTorus φ)).singularCohomology R k M p) :
    TopCat.singularCohomologyMap (TopCat.ofHom (coverMap φ)) p α =
      TopCat.singularCohomologyMap
        (TopCat.ofHom (ContinuousMap.HomotopyEquiv.prodZeroSection F ℝ).symm.toFun) p
        (TopCat.singularCohomologyMap (TopCat.ofHom (incl φ)) p α) := by
  set e := (ContinuousMap.HomotopyEquiv.prodZeroSection F ℝ).symm
  -- the covering map at height zero is the fibre inclusion
  have hs : TopCat.ofHom e.invFun ≫ TopCat.ofHom (coverMap φ) = TopCat.ofHom (incl φ) := by
    ext x
    simp [e, coverMap_apply, incl_apply]
  rw [← hs, TopCat.singularCohomologyMap_comp, ConcreteCategory.comp_apply]
  have hinv := (e.singularCohomologyIso R k M p).inv_hom_id_apply
    (TopCat.singularCohomologyMap (TopCat.ofHom (coverMap φ)) p α)
  rw [ContinuousMap.HomotopyEquiv.singularCohomologyIso_hom,
    ContinuousMap.HomotopyEquiv.singularCohomologyIso_inv] at hinv
  exact hinv.symm

variable [MonoidalCategory C] [MonoidalPreadditive C]
  [∀ J : Type w, PreservesColimitsOfShape (Discrete J) (tensorLeft M)]

/-! The Alexander–Whitney diagonals and coefficient pairings of the cylinder and of the mapping
torus, typed through `singularChainComplexFunctor` as are the maps of the cyclic cover sequence,
and their compatibility with those maps. -/

variable (F) in
/-- The Alexander–Whitney diagonal of the cylinder `F × ℝ`. -/
private abbrev cylinderDiagonal (u : T ⟶ R ⊗ S) :
    ((singularChainComplexFunctor C).obj T).obj (TopCat.of (F × ℝ)) ⟶
      HomologicalComplex.tensorObj
        (((singularChainComplexFunctor C).obj R).obj (TopCat.of (F × ℝ)))
        (((singularChainComplexFunctor C).obj S).obj (TopCat.of (F × ℝ))) :=
  (TopCat.of (F × ℝ)).alexanderWhitneyDiagonal u

/-- The Alexander–Whitney diagonal of the mapping torus. -/
private abbrev torusDiagonal (u : T ⟶ R ⊗ S) :
    ((singularChainComplexFunctor C).obj T).obj (TopCat.of (MappingTorus φ)) ⟶
      HomologicalComplex.tensorObj
        (((singularChainComplexFunctor C).obj R).obj (TopCat.of (MappingTorus φ)))
        (((singularChainComplexFunctor C).obj S).obj (TopCat.of (MappingTorus φ))) :=
  (TopCat.of (MappingTorus φ)).alexanderWhitneyDiagonal u

variable (F) in
/-- The coefficient pairing on the singular chains of the cylinder `F × ℝ`. -/
private abbrev cylinderPairing (μ : M ⊗ S ⟶ N) :
    ((tensorLeft M).mapHomologicalComplex _).obj
        (((singularChainComplexFunctor C).obj S).obj (TopCat.of (F × ℝ))) ⟶
      ((singularChainComplexFunctor C).obj N).obj (TopCat.of (F × ℝ)) :=
  (TopCat.toSSet.obj (TopCat.of (F × ℝ))).chainComplexPairing μ

/-- The coefficient pairing on the singular chains of the mapping torus. -/
private abbrev torusPairing (μ : M ⊗ S ⟶ N) :
    ((tensorLeft M).mapHomologicalComplex _).obj
        (((singularChainComplexFunctor C).obj S).obj (TopCat.of (MappingTorus φ))) ⟶
      ((singularChainComplexFunctor C).obj N).obj (TopCat.of (MappingTorus φ)) :=
  (TopCat.toSSet.obj (TopCat.of (MappingTorus φ))).chainComplexPairing μ

/-- The diagonal of the cylinder followed by the covering map on the first factor intertwines
`𝟙 - τ_*` on the source with `𝟙 - τ_*` on the second factor. -/
private lemma id_sub_deckChainMap_comp_cylinderDiagonal (u : T ⟶ R ⊗ S) :
    (𝟙 _ - deckChainMap φ T) ≫ cylinderDiagonal F u ≫
        HomologicalComplex.tensorHom (coverChainMap φ R) (𝟙 _) =
      cylinderDiagonal F u ≫
        HomologicalComplex.tensorHom (coverChainMap φ R) (𝟙 _ - deckChainMap φ S) := by
  have hdeck : deckChainMap φ T ≫ cylinderDiagonal F u =
      cylinderDiagonal F u ≫
        HomologicalComplex.tensorHom (deckChainMap φ R) (deckChainMap φ S) := by
    rw [deckChainMap_def, deckChainMap_def, deckChainMap_def]
    exact TopCat.alexanderWhitneyDiagonal_naturality _ u
  -- `τ_*` followed by the covering map is the covering map
  have hsub : HomologicalComplex.tensorHom (coverChainMap φ R) (𝟙 _ - deckChainMap φ S) =
      HomologicalComplex.tensorHom (coverChainMap φ R) (𝟙 _) -
        HomologicalComplex.tensorHom (deckChainMap φ R) (deckChainMap φ S) ≫
          HomologicalComplex.tensorHom (coverChainMap φ R) (𝟙 _) := by
    rw [← mapBifunctorMap_comp, deckChainMap_comp_coverChainMap, Category.comp_id]
    ext j : 1
    apply mapBifunctor.hom_ext
    intro i₁ i₂ hi
    simp [Preadditive.comp_sub]
  rw [hsub, Preadditive.comp_sub, Preadditive.sub_comp, Category.id_comp, reassoc_of% hdeck]

/-- The covering map intertwines the diagonal of the cylinder, followed by the covering map on the
first factor, with the diagonal of the mapping torus. -/
private lemma coverChainMap_comp_torusDiagonal (u : T ⟶ R ⊗ S) :
    coverChainMap φ T ≫ torusDiagonal φ u =
      (cylinderDiagonal F u ≫ HomologicalComplex.tensorHom (coverChainMap φ R) (𝟙 _)) ≫
        HomologicalComplex.tensorHom (𝟙 _) (coverChainMap φ S) := by
  have hcover : coverChainMap φ T ≫ torusDiagonal φ u =
      cylinderDiagonal F u ≫
        HomologicalComplex.tensorHom (coverChainMap φ R) (coverChainMap φ S) := by
    rw [coverChainMap_def, coverChainMap_def, coverChainMap_def]
    exact TopCat.alexanderWhitneyDiagonal_naturality _ u
  rw [hcover, Category.assoc, ← mapBifunctorMap_comp, Category.id_comp, Category.comp_id]

/-- The coefficient pairing of the cylinder commutes with `𝟙 - τ_*`. -/
private lemma cylinderPairing_comp_id_sub_deckChainMap (μ : M ⊗ S ⟶ N) :
    cylinderPairing F μ ≫ (𝟙 _ - deckChainMap φ N) =
      ((tensorLeft M).mapHomologicalComplex _).map (𝟙 _ - deckChainMap φ S) ≫
        cylinderPairing F μ := by
  have hnat : ((tensorLeft M).mapHomologicalComplex _).map (deckChainMap φ S) ≫
      cylinderPairing F μ = cylinderPairing F μ ≫ deckChainMap φ N := by
    rw [deckChainMap_def, deckChainMap_def]
    exact SSet.chainComplexPairing_naturality _ μ
  rw [Functor.map_sub, CategoryTheory.Functor.map_id, Preadditive.comp_sub, Preadditive.sub_comp,
    hnat, Category.comp_id, Category.id_comp]

/-- The coefficient pairings of the cylinder and of the mapping torus commute with the covering
map. -/
private lemma cylinderPairing_comp_coverChainMap (μ : M ⊗ S ⟶ N) :
    cylinderPairing F μ ≫ coverChainMap φ N =
      ((tensorLeft M).mapHomologicalComplex _).map (coverChainMap φ S) ≫ torusPairing φ μ := by
  rw [coverChainMap_def, coverChainMap_def]
  exact (SSet.chainComplexPairing_naturality _ μ).symm

/-- **The Wang connecting morphism is a morphism of modules over the cohomology of the mapping
torus**, up to the Koszul sign: for a class `α ∈ Hᵖ(T_φ)` and a class `x ∈ Hₙ₊₁(T_φ)`,
`δ (x ⌢ α) = (-1)ᵖ δ x ⌢ i^*α` in `H_q(F)`, where `δ` is the Wang connecting morphism, `i` the
fibre inclusion and `p + q = n`. -/
theorem singularCap_comp_wangδ (k : Type*) [Ring k] [Linear k C] [MonoidalLinear k C]
    (u : T ⟶ R ⊗ S) (μ : M ⊗ S ⟶ N) (p q n : ℕ) (h : p + q = n)
    (α : (TopCat.of (MappingTorus φ)).singularCohomology R k M p) :
    (TopCat.of (MappingTorus φ)).singularCap k u μ p (q + 1) (n + 1) (by omega) α ≫
        wangδ φ N q =
      ((-1 : ℤ) ^ p) • (wangδ φ T n ≫ (TopCat.of F).singularCap k u μ p q n h
        (TopCat.singularCohomologyMap (TopCat.ofHom (incl φ)) p α)) := by
  -- capping commutes with the connecting morphism of the cyclic cover
  have hδ := TauCeti.ChainComplex.cap_comp_δ (cyclicCoverShortComplex_shortExact φ T)
    (cyclicCoverShortComplex_shortExact φ N) (cylinderDiagonal F u)
    (cylinderDiagonal F u ≫ HomologicalComplex.tensorHom (coverChainMap φ R) (𝟙 _))
    (torusDiagonal φ u)
    (cylinderPairing F μ) (cylinderPairing F μ) (torusPairing φ μ) (coverChainMap φ R)
    (𝟙 _ - deckChainMap φ S) (coverChainMap φ S) (id_sub_deckChainMap_comp_cylinderDiagonal φ u)
    (cylinderPairing_comp_id_sub_deckChainMap φ μ) (coverChainMap_comp_torusDiagonal φ u)
    (cylinderPairing_comp_coverChainMap φ μ) p q n (q + 1) (n + 1) h (by omega) α
  -- the projection formula moves the cap product with the pulled-back class to the fibre
  have hcap := TopCat.singularCap_naturality
    (TopCat.ofHom (ContinuousMap.HomotopyEquiv.prodZeroSection F ℝ).symm.toFun) k u μ p q n h
    (TopCat.singularCohomologyMap (TopCat.ofHom (incl φ)) p α)
  rw [← singularCohomologyMap_coverMap, TopCat.singularCap_def, TopCat.singularCap_def] at hcap
  have hf : homologyMap ((TauCeti.ChainComplex.linearYonedaFunctor k M).map
      (coverChainMap φ R).op) p = TopCat.singularCohomologyMap (TopCat.ofHom (coverMap φ)) p := by
    rw [coverChainMap_def]
    -- `TopCat.singularCohomologyMap f` is the abbreviation
    -- `homologyMap ((linearYonedaFunctor k M).map (SSet.chainComplexMap (toSSet.map f) R).op)`
    -- (`SSet.cochainComplexMap`), and `singularChainComplexFunctor` sends `f` to
    -- `SSet.chainComplexMap (toSSet.map f) R` by definition
    rfl
  have key : TauCeti.ChainComplex.cap k (cylinderDiagonal F u) (cylinderPairing F μ) p q n h
      (homologyMap ((TauCeti.ChainComplex.linearYonedaFunctor k M).map
        (coverChainMap φ R).op) p α) ≫
        homologyMap (((singularChainComplexFunctor C).obj N).map (TopCat.ofHom
          (ContinuousMap.HomotopyEquiv.prodZeroSection F ℝ).symm.toFun)) q =
      homologyMap (((singularChainComplexFunctor C).obj T).map (TopCat.ofHom
          (ContinuousMap.HomotopyEquiv.prodZeroSection F ℝ).symm.toFun)) n ≫
        TauCeti.ChainComplex.cap k ((TopCat.of F).alexanderWhitneyDiagonal u)
          ((TopCat.toSSet.obj (TopCat.of F)).chainComplexPairing μ) p q n h
          (TopCat.singularCohomologyMap (TopCat.ofHom (incl φ)) p α) := by
    rw [hf]
    exact hcap
  -- term-mode steps: the homology objects of the two sides are written through different but
  -- definitionally equal functors, so `rw` cannot form the motives
  rw [wangδ_def, wangδ_def, TopCat.singularCap_def, TopCat.singularCap_def]
  refine (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) hδ).trans ?_)
  refine (Preadditive.zsmul_comp _ _ _).trans (congrArg _ ?_)
  exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) key).trans (Category.assoc _ _ _).symm)

end Cap

/-! ### The cup product with the base class -/

section BaseClass

-- As in `TauCeti.AlgebraicTopology.Singular.MappingTorus.BaseCircle`: morphisms of `ℤ`-modules are
-- scaled through the linear structure of `ModuleCat ℤ`.
attribute [local instance 1100] ModuleCat.instLinear

/-- **Cup products with the base class through the Wang sequence**: there is a sign `s = ±1`, the
same for every mapping torus, with `⟨v ⌣ [dt], y⟩ = s (-1)ᵖ ⟨i^* v, δ y⟩` for all
`v ∈ Hᵖ(T_φ; ℤ)` and `y ∈ Hₚ₊₁(T_φ; ℤ)`, where `[dt]` is the base class, `δ` the Wang connecting
morphism and `i` the fibre inclusion. The sign is `s = -1`, that of
`TauCeti.MappingTorus.singularKronecker_baseClass_apply_eq_neg`. -/
theorem exists_singularCupPairing_baseClass_apply :
    ∃ s : ℤ, (s = 1 ∨ s = -1) ∧ ∀ {F : Type} [TopologicalSpace F] (φ : F ≃ₜ F) (p : ℕ)
      (y : ((singularHomologyFunctor (ModuleCat.{0} ℤ) (p + 1)).obj
        (𝟙_ (ModuleCat.{0} ℤ))).obj (TopCat.of (MappingTorus φ)))
      (v : (TopCat.of (MappingTorus φ)).singularCohomology (𝟙_ (ModuleCat.{0} ℤ)) ℤ
        (𝟙_ (ModuleCat.{0} ℤ)) p),
      (TopCat.of (MappingTorus φ)).singularCupPairing ℤ rfl y v (baseClass φ) =
        s * (-1) ^ p * ((TopCat.of F).singularKronecker ℤ p
          (TopCat.singularCohomologyMap (TopCat.ofHom (incl φ)) p v)).hom
            ((wangδ φ (𝟙_ (ModuleCat.{0} ℤ)) p).hom y) := by
  refine ⟨-1, Or.inr rfl, fun {F} _ φ p y v ↦ ?_⟩
  -- `⟨v ⌣ [dt], y⟩ = ⟨[dt], y ⌢ v⟩ = s ε(δ (y ⌢ v))`, and `δ (y ⌢ v) = (-1)ᵖ δ y ⌢ i^* v`
  rw [TopCat.singularCupPairing_eq_singularKronecker_singularCapLinearMap,
    TopCat.singularCapLinearMap_apply]
  refine (singularKronecker_baseClass_apply_eq_neg φ _).trans ?_
  have hcap := singularCap_comp_wangδ φ ℤ (λ_ (𝟙_ (ModuleCat.{0} ℤ))).inv
    (λ_ (𝟙_ (ModuleCat.{0} ℤ))).hom p 0 p rfl v
  have hε := (TopCat.of F).singularCap_comp_singularHomology₀ε ℤ (R := 𝟙_ (ModuleCat.{0} ℤ))
    (M := 𝟙_ (ModuleCat.{0} ℤ)) p rfl (TopCat.singularCohomologyMap (TopCat.ofHom (incl φ)) p v)
  rw [← unitors_inv_equal, ← unitors_equal] at hε
  have key := (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) hcap).trans
    ((Preadditive.zsmul_comp _ _ _).trans (congrArg _ ((Category.assoc _ _ _).trans
      (congrArg (_ ≫ ·) hε)))))
  have hy := congrArg (fun f ↦ f.hom y) key
  rw [mul_assoc, neg_one_mul]
  exact congrArg Neg.neg hy

end BaseClass

variable {F E : Type} [TopologicalSpace F] [T2Space F] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [ChartedSpace E F] [CompactSpace F] [ConnectedSpace F]
  {n : ℕ} (o : HomologicalOrientation F E (n + 1)) (hn : Module.finrank ℝ E = n + 1)
  {φ : F ≃ₜ F}

/-- **The cup product with the base class evaluates on the fibre.** Let `φ` be a homeomorphism of a
closed connected oriented `(n + 1)`-manifold `F` preserving its fundamental class. Then there is a
class `y ∈ Hₙ₊₂(T_φ; ℤ)` with `⟨v ⌣ [dt], y⟩ = ⟨v, i_*[F]⟩` for every `v ∈ Hⁿ⁺¹(T_φ; ℤ)`, where
`[dt]` is the base class and the fibre class `i_*[F]` is read through the chains with
coefficients in `ULift ℤ` on which it is built. The class `y` is one whose image under the Wang
connecting morphism `δ` is `±[F]`. For a surface mapping torus `Y_φ` and a class `v` pairing to one
with the fibre class this gives `⟨v ⌣ [dt], y⟩ = 1`. -/
theorem exists_singularCupPairing_baseClass_eq_evalFundamentalClass
    (hφ : o.mapFundamentalClass hn ⟨φ, φ.continuous⟩ = o.fundamentalClass hn) :
    ∃ y : ((singularHomologyFunctor (ModuleCat.{0} ℤ) (n + 2)).obj (𝟙_ (ModuleCat.{0} ℤ))).obj
        (TopCat.of (MappingTorus φ)),
      (∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ (wangδ φ (𝟙_ (ModuleCat.{0} ℤ)) (n + 1)).hom y =
        ε • (uliftIntHomologyIso (TopCat.of F) (n + 1)).hom.hom (o.fundamentalClass hn)) ∧
      ∀ v : (TopCat.of (MappingTorus φ)).singularCohomology (𝟙_ (ModuleCat.{0} ℤ)) ℤ
        (𝟙_ (ModuleCat.{0} ℤ)) (n + 1),
        (TopCat.of (MappingTorus φ)).singularCupPairing ℤ (p := n + 1) (q := 1) (n := n + 2) rfl
            y v (baseClass φ) =
          o.evalFundamentalClass hn (𝟙_ (ModuleCat.{0} ℤ)) (incl φ)
            ((TopCat.of (MappingTorus φ)).singularCohomologyChainCoefficientMap ℤ
              (𝟙_ (ModuleCat.{0} ℤ)) uliftIntIso.hom (n + 1) v) := by
  obtain ⟨s, hs, h⟩ := exists_singularCupPairing_baseClass_apply
  -- the sign `ε = s (-1)ⁿ⁺¹` of the pairing is absorbed into `y`
  set ε : ℤ := s * (-1) ^ (n + 1)
  have hε : ε * ε = 1 := by
    rcases hs with rfl | rfl <;> simp [ε, ← pow_add, ← two_mul, pow_mul]
  have hε₁ : ε = 1 ∨ ε = -1 := by
    rcases hs with rfl | rfl <;> rcases neg_one_pow_eq_or ℤ (n + 1) with h | h <;> simp [ε, h]
  -- `ModuleCat.of ℤ ℤ` is by definition the unit object `𝟙_ (ModuleCat ℤ)`
  have hepi : Epi (wangδ φ (𝟙_ (ModuleCat.{0} ℤ)) (n + 1)) :=
    epi_wangδ_of_mapFundamentalClass_eq o hn hφ
  obtain ⟨y, hy⟩ := (ModuleCat.epi_iff_surjective _).1 hepi
    ((uliftIntHomologyIso (TopCat.of F) (n + 1)).hom.hom (o.fundamentalClass hn))
  have hδ : (wangδ φ (𝟙_ (ModuleCat.{0} ℤ)) (n + 1)).hom (ε • y) =
      ε • (uliftIntHomologyIso (TopCat.of F) (n + 1)).hom.hom (o.fundamentalClass hn) := by
    exact (map_zsmul _ ε y).trans (congrArg (ε • ·) hy)
  refine ⟨ε • y, ⟨ε, hε₁, hδ⟩, fun v ↦ ?_⟩
  set c := o.evalFundamentalClass hn (𝟙_ (ModuleCat.{0} ℤ)) (incl φ)
    ((TopCat.of (MappingTorus φ)).singularCohomologyChainCoefficientMap ℤ
      (𝟙_ (ModuleCat.{0} ℤ)) uliftIntIso.hom (n + 1) v)
  have e : ((TopCat.of F).singularKronecker ℤ (n + 1)
      (TopCat.singularCohomologyMap (TopCat.ofHom (incl φ)) (n + 1) v)).hom
        ((wangδ φ (𝟙_ (ModuleCat.{0} ℤ)) (n + 1)).hom (ε • y)) = ε * c := by
    rw [hδ]
    exact (map_zsmul _ ε _).trans
      (congrArg (ε • ·) (o.evalFundamentalClass_singularCohomologyChainCoefficientMap hn _
        (incl φ) v).symm)
  refine (h φ (n + 1) (ε • y) v).trans ?_
  refine (congrArg (fun f ↦ ε * ModuleCat.Hom.hom f
    ((wangδ φ (𝟙_ (ModuleCat.{0} ℤ)) (n + 1)).hom (ε • y)))
    (TopCat.singularKronecker_instLinear _ _ _ _)).trans ?_
  refine (congrArg (ε * ·) e).trans ?_
  linear_combination c * hε

end TauCeti.MappingTorus
