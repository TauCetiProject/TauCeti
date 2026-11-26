/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Monoidal.Homology.Kunneth.Projective
public import TauCeti.AlgebraicTopology.Singular.CrossProduct.Relative
public import TauCeti.AlgebraicTopology.Singular.Kunneth.Relative
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.Basic
public import TauCeti.Data.Set.Prod
public import TauCeti.Topology.Category.TopPair.ContinuousLinearEquiv
import TauCeti.Algebra.Module.Equiv.SpanSingleton

/-!
# The local homology cross product and cross products with a local generator

For `x₁ : V₁` and `x₂ : V₂`, pushing `TopCat.singularRelativeHomologyCross` forward along
`v : R ⊗ S ⟶ T` and `(Set.compl_singleton_prodMk_eq_union x₁ x₂).superset` defines
`TauCeti.complSingletonPairHomologyCross`:
`Hₚ(V₁, V₁ ∖ {x₁}; R) ⊗ H_q(V₂, V₂ ∖ {x₂}; S) ⟶ Hₙ(V₁ × V₂, (V₁ × V₂) ∖ {(x₁, x₂)}; T)`
(`p + q = n`), paired via `TopPair.singularKronecker` with `TauCeti.complSingletonPairCross` in
`TauCeti.AlgebraicTopology.Cohomology.Local.Cross`: when `{x₁}ᶜ` and `{x₂}ᶜ` are open (in
particular in `T₁` spaces) and `v ≫ u = 𝟙 (R ⊗ S)`, the Kronecker pairing is multiplicative
(`TauCeti.complSingletonPairHomologyCross_comp_singularKronecker_complSingletonPairCross`).
Kronecker evaluation on `TauCeti.complSingletonPairHomologyCross` proves generator preservation and
reflection for local cohomology cross products over arbitrary commutative rings without flatness or
Künneth hypotheses.

Every `complSingletonPairHomologyCross` declaration assumes discrete colimit preservation for
`tensorLeft`/`tensorRight`. For `WalkingParallelPair` colimit preservation,
`TauCeti.complSingletonPairHomologyCross` assumes it for `tensorLeft` of `Hₚ(V₁, {x₁}ᶜ; R)` and
`tensorRight` of `Z_q(V₂, {x₂}ᶜ; S)` and `C_{q+1}(V₂, {x₂}ᶜ; S)`, while the two naturality
theorems also assume the corresponding instances for the target pairs `(W₁, {y₁}ᶜ)` and
`(W₂, {y₂}ᶜ)` (or `(W₁, {0}ᶜ)` and `(W₂, {0}ᶜ)`).

Separately, let `x` be a point of a `T₁` space `M` in the source of an open partial homeomorphism
to a real normed space `E` of finite dimension `r`, and let `k` be a commutative ring. The local
homology `H_r(M, M ∖ x; k)` is a copy of `k` (`TauCeti.singularHomologyComplSingletonFinrankIso`),
so it has a generator (`TauCeti.exists_span_singularHomology_complSingleton_eq_top`) and each
generator `o` of it is a basis
(`TauCeti.bijective_toSpanSingleton_singularHomology_complSingleton`). Since the local homology
vanishes in the other degrees, the relative Künneth theorem leaves a single summand: the cross
product `y ↦ o × y` is a bijection `H_q(C) → H_{r+q}(C(M, M ∖ x; k) ⊗ C)` for every chain complex
`C` of `k`-modules
(`TauCeti.bijective_homologyCross_tmul_singularChainComplex_complSingleton`). With the relative
Eilenberg–Zilber theorem, the relative cross product `y ↦ o × y` of singular homology is a bijection
`H_q(Y; L) → H_{r+q}(M × Y, (M ∖ x) × Y; k ⊗ L)` for every space `Y`
(`TauCeti.bijective_singularHomologyCrossRel_tmul_complSingleton`). For `M = E` and `x = 0`, this
is the Thom isomorphism of a product bundle with fibre `E`.

## Main definitions and results

* `TauCeti.complSingletonPairHomologyCross` (with unfolding
  `TauCeti.complSingletonPairHomologyCross_def`): the local homology cross product on complements
  of singletons.
* `TauCeti.complSingletonPairHomologyCross_naturality`: naturality in continuous maps preserving
  singleton complements.
* `singularHomologyMap_complZeroPairIso_hom_tensorHom_complSingletonPairHomologyCross` (in
  `ContinuousLinearEquiv`): naturality at the origin under products of continuous linear
  equivalences.
* `TauCeti.exists_span_singularHomology_complSingleton_eq_top`,
  `TauCeti.bijective_toSpanSingleton_singularHomology_complSingleton`: existence of a local
  homology generator and basis property.
* `TauCeti.bijective_homologyCross_tmul_singularChainComplex_complSingleton`,
  `TauCeti.bijective_singularHomologyCrossRel_tmul_complSingleton`: bijectivity of cross products
  with a generator of local homology.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.3 (local orientations), Section 3.B (the relative cross product and Künneth formula)
  and Section 4.D (the Thom class of a product bundle).
-/

public section

noncomputable section

section PairCross

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicTopology

universe w v u

attribute [local instance] hasFiniteCoproducts_of_hasCoproducts
attribute [local instance] HasFiniteBiproducts.of_hasFiniteCoproducts

variable {C : Type u} [Category.{v} C] [Abelian C] [HasCoproducts.{w} C] [MonoidalCategory C]
  [MonoidalPreadditive C]
  [∀ (X : C) (J : Type w), PreservesColimitsOfShape (Discrete J) (tensorLeft X)]
  [∀ (X : C) (J : Type w), PreservesColimitsOfShape (Discrete J) (tensorRight X)]
  {R S T : C}

namespace TauCeti

section Basic

variable {V₁ V₂ : Type w} [TopologicalSpace V₁] [TopologicalSpace V₂]
  (x₁ : V₁) (x₂ : V₂) (v : R ⊗ S ⟶ T) (p q n : ℕ) (h : p + q = n)
  [PreservesColimitsOfShape WalkingParallelPair (tensorLeft
    (((TopPair.ofSubset ({x₁}ᶜ : Set (TopCat.of V₁))).singularChainComplex R).homology p))]
  [PreservesColimitsOfShape WalkingParallelPair (tensorRight
    (((TopPair.ofSubset ({x₂}ᶜ : Set (TopCat.of V₂))).singularChainComplex S).cycles q))]
  [PreservesColimitsOfShape WalkingParallelPair (tensorRight
    (((TopPair.ofSubset ({x₂}ᶜ : Set (TopCat.of V₂))).singularChainComplex S).X
      ((ComplexShape.down ℕ).prev q)))]

/-- **The relative homology cross product on complements of singletons**
`Hₚ(V₁, V₁ ∖ {x₁}; R) ⊗ H_q(V₂, V₂ ∖ {x₂}; S) ⟶ Hₙ(V₁ × V₂, (V₁ × V₂) ∖ {(x₁, x₂)}; T)`
(`p + q = n`), along `v : R ⊗ S ⟶ T` and `Set.compl_singleton_prodMk_eq_union`. -/
def complSingletonPairHomologyCross :
    (TopPair.ofSubset (X := TopCat.of V₁) ({x₁}ᶜ : Set V₁)).singularHomology R p ⊗
      (TopPair.ofSubset (X := TopCat.of V₂) ({x₂}ᶜ : Set V₂)).singularHomology S q ⟶
        (TopPair.ofSubset (X := TopCat.of (V₁ × V₂))
          ({(x₁, x₂)}ᶜ : Set (V₁ × V₂))).singularHomology T n :=
  TopCat.singularRelativeHomologyCross (TopCat.of V₁) (TopCat.of V₂) R S
      ({x₁}ᶜ : Set (TopCat.of V₁)) ({x₂}ᶜ : Set (TopCat.of V₂)) p q n h ≫
    (TopPair.ofSubset (fst (TopCat.of V₁) (TopCat.of V₂) ⁻¹' ({x₁}ᶜ : Set V₁) ∪
      snd (TopCat.of V₁) (TopCat.of V₂) ⁻¹' ({x₂}ᶜ : Set V₂))).singularHomologyCoefficientMap
      v n ≫
    TopPair.singularHomologyMap (TopPair.ofSubsetMap (𝟙 (TopCat.of V₁ ⊗ TopCat.of V₂))
      (B := fst (TopCat.of V₁) (TopCat.of V₂) ⁻¹' ({x₁}ᶜ : Set V₁) ∪
        snd (TopCat.of V₁) (TopCat.of V₂) ⁻¹' ({x₂}ᶜ : Set V₂)) (B' := ({(x₁, x₂)}ᶜ : Set _))
      (Set.compl_singleton_prodMk_eq_union x₁ x₂).superset) T n

/-- Definitional unfolding of `TauCeti.complSingletonPairHomologyCross`. -/
theorem complSingletonPairHomologyCross_def :
    complSingletonPairHomologyCross x₁ x₂ v p q n h =
      TopCat.singularRelativeHomologyCross (TopCat.of V₁) (TopCat.of V₂) R S
          ({x₁}ᶜ : Set (TopCat.of V₁)) ({x₂}ᶜ : Set (TopCat.of V₂)) p q n h ≫
        (TopPair.ofSubset (fst (TopCat.of V₁) (TopCat.of V₂) ⁻¹' ({x₁}ᶜ : Set V₁) ∪
          snd (TopCat.of V₁) (TopCat.of V₂) ⁻¹' ({x₂}ᶜ : Set V₂))).singularHomologyCoefficientMap
          v n ≫
        TopPair.singularHomologyMap (TopPair.ofSubsetMap (𝟙 (TopCat.of V₁ ⊗ TopCat.of V₂))
          (B := fst (TopCat.of V₁) (TopCat.of V₂) ⁻¹' ({x₁}ᶜ : Set V₁) ∪
            snd (TopCat.of V₁) (TopCat.of V₂) ⁻¹' ({x₂}ᶜ : Set V₂)) (B' := ({(x₁, x₂)}ᶜ : Set _))
          (Set.compl_singleton_prodMk_eq_union x₁ x₂).superset) T n :=
  (rfl)

end Basic

/-- **Naturality of `complSingletonPairHomologyCross`** in continuous maps `g₁ : V₁ ⟶ W₁` and
`g₂ : V₂ ⟶ W₂` carrying `{x₁}ᶜ` into `{y₁}ᶜ` and `{x₂}ᶜ` into `{y₂}ᶜ`. -/
@[reassoc]
theorem complSingletonPairHomologyCross_naturality
    {V₁ V₂ W₁ W₂ : Type w} [TopologicalSpace V₁] [TopologicalSpace V₂]
    [TopologicalSpace W₁] [TopologicalSpace W₂] {x₁ : V₁} {x₂ : V₂} {y₁ : W₁} {y₂ : W₂}
    (g₁ : TopCat.of V₁ ⟶ TopCat.of W₁) (g₂ : TopCat.of V₂ ⟶ TopCat.of W₂)
    (hg₁ : Set.MapsTo g₁ ({x₁}ᶜ : Set V₁) ({y₁}ᶜ : Set W₁))
    (hg₂ : Set.MapsTo g₂ ({x₂}ᶜ : Set V₂) ({y₂}ᶜ : Set W₂))
    (v : R ⊗ S ⟶ T) (p q n : ℕ) (h : p + q = n)
    [PreservesColimitsOfShape WalkingParallelPair (tensorLeft
      (((TopPair.ofSubset ({x₁}ᶜ : Set (TopCat.of V₁))).singularChainComplex R).homology p))]
    [PreservesColimitsOfShape WalkingParallelPair (tensorRight
      (((TopPair.ofSubset ({x₂}ᶜ : Set (TopCat.of V₂))).singularChainComplex S).cycles q))]
    [PreservesColimitsOfShape WalkingParallelPair (tensorRight
      (((TopPair.ofSubset ({x₂}ᶜ : Set (TopCat.of V₂))).singularChainComplex S).X
        ((ComplexShape.down ℕ).prev q)))]
    [PreservesColimitsOfShape WalkingParallelPair (tensorLeft
      (((TopPair.ofSubset ({y₁}ᶜ : Set (TopCat.of W₁))).singularChainComplex R).homology p))]
    [PreservesColimitsOfShape WalkingParallelPair (tensorRight
      (((TopPair.ofSubset ({y₂}ᶜ : Set (TopCat.of W₂))).singularChainComplex S).cycles q))]
    [PreservesColimitsOfShape WalkingParallelPair (tensorRight
      (((TopPair.ofSubset ({y₂}ᶜ : Set (TopCat.of W₂))).singularChainComplex S).X
        ((ComplexShape.down ℕ).prev q)))] :
    (TopPair.singularHomologyMap (TopPair.ofSubsetMap g₁ hg₁) R p ⊗ₘ
        TopPair.singularHomologyMap (TopPair.ofSubsetMap g₂ hg₂) S q) ≫
      complSingletonPairHomologyCross y₁ y₂ v p q n h =
    complSingletonPairHomologyCross x₁ x₂ v p q n h ≫
      TopPair.singularHomologyMap (TopPair.ofSubsetMap (g₁ ⊗ₘ g₂)
        (TopCat.mapsTo_tensorHom_compl_singleton g₁ g₂ hg₁ hg₂)) T n := by
  let uPair := TopPair.ofSubsetMap (g₁ ⊗ₘ g₂)
    (TopCat.mapsTo_tensorHom_preimage_union g₁ g₂ hg₁ hg₂)
  let idV := TopPair.ofSubsetMap (B := fst (TopCat.of V₁) (TopCat.of V₂) ⁻¹' ({x₁}ᶜ : Set V₁) ∪
      snd (TopCat.of V₁) (TopCat.of V₂) ⁻¹' ({x₂}ᶜ : Set V₂)) (B' := ({(x₁, x₂)}ᶜ : Set _))
    (𝟙 (TopCat.of V₁ ⊗ TopCat.of V₂)) (Set.compl_singleton_prodMk_eq_union x₁ x₂).superset
  let idW := TopPair.ofSubsetMap (B := fst (TopCat.of W₁) (TopCat.of W₂) ⁻¹' ({y₁}ᶜ : Set W₁) ∪
      snd (TopCat.of W₁) (TopCat.of W₂) ⁻¹' ({y₂}ᶜ : Set W₂)) (B' := ({(y₁, y₂)}ᶜ : Set _))
    (𝟙 (TopCat.of W₁ ⊗ TopCat.of W₂)) (Set.compl_singleton_prodMk_eq_union y₁ y₂).superset
  -- `TopCat.of W₁ ⊗ TopCat.of W₂` and `TopCat.of (W₁ × W₂)` are defeq at `default` (not `implicit`)
  have hpair : uPair ≫ idW = idV ≫ TopPair.ofSubsetMap (g₁ ⊗ₘ g₂)
      (TopCat.mapsTo_tensorHom_compl_singleton g₁ g₂ hg₁ hg₂) :=
    TopPair.ofSubsetMap_comp_ofSubsetMap_eq _ _ _ _ (by rw [Category.comp_id, Category.id_comp])
  have hmap : TopPair.singularHomologyMap uPair T n ≫ TopPair.singularHomologyMap idW T n =
      TopPair.singularHomologyMap idV T n ≫ TopPair.singularHomologyMap (TopPair.ofSubsetMap
        (g₁ ⊗ₘ g₂) (TopCat.mapsTo_tensorHom_compl_singleton g₁ g₂ hg₁ hg₂)) T n := by
    rw [← TopPair.singularHomologyMap_comp, hpair, TopPair.singularHomologyMap_comp]
  exact (TopCat.singularRelativeHomologyCross_naturality_assoc g₁ g₂ hg₁ hg₂ R S p q n h
    ((TopPair.ofSubset (fst (TopCat.of W₁) (TopCat.of W₂) ⁻¹' ({y₁}ᶜ : Set W₁) ∪
        snd (TopCat.of W₁) (TopCat.of W₂) ⁻¹' ({y₂}ᶜ : Set W₂))).singularHomologyCoefficientMap
        v n ≫ TopPair.singularHomologyMap idW T n)).trans <|
    (whisker_eq _ ((Category.assoc _ _ _).symm.trans
      ((eq_whisker (TopPair.singularHomologyCoefficientMap_naturality uPair v n) _).trans
      ((Category.assoc _ _ _).trans (whisker_eq _ hmap))))).trans
      ((Category.assoc _ _ _).trans (whisker_eq _ (Category.assoc _ _ _))).symm

end TauCeti

namespace ContinuousLinearEquiv

open TauCeti (complSingletonPairHomologyCross complSingletonPairHomologyCross_naturality)

/-- **Naturality of `complSingletonPairHomologyCross` at the origin** under products of continuous
linear equivalences `f₁ : V₁ ≃L W₁` and `f₂ : V₂ ≃L W₂`. -/
@[reassoc]
theorem singularHomologyMap_complZeroPairIso_hom_tensorHom_complSingletonPairHomologyCross
    {𝕜 : Type*} [Semiring 𝕜] {V₁ V₂ W₁ W₂ : Type w}
    [TopologicalSpace V₁] [AddCommMonoid V₁] [Module 𝕜 V₁]
    [TopologicalSpace V₂] [AddCommMonoid V₂] [Module 𝕜 V₂]
    [TopologicalSpace W₁] [AddCommMonoid W₁] [Module 𝕜 W₁]
    [TopologicalSpace W₂] [AddCommMonoid W₂] [Module 𝕜 W₂]
    (f₁ : V₁ ≃L[𝕜] W₁) (f₂ : V₂ ≃L[𝕜] W₂) (v : R ⊗ S ⟶ T) (p q n : ℕ) (h : p + q = n)
    [PreservesColimitsOfShape WalkingParallelPair (tensorLeft
      (((TopPair.ofSubset ({0}ᶜ : Set (TopCat.of V₁))).singularChainComplex R).homology p))]
    [PreservesColimitsOfShape WalkingParallelPair (tensorRight
      (((TopPair.ofSubset ({0}ᶜ : Set (TopCat.of V₂))).singularChainComplex S).cycles q))]
    [PreservesColimitsOfShape WalkingParallelPair (tensorRight
      (((TopPair.ofSubset ({0}ᶜ : Set (TopCat.of V₂))).singularChainComplex S).X
        ((ComplexShape.down ℕ).prev q)))]
    [PreservesColimitsOfShape WalkingParallelPair (tensorLeft
      (((TopPair.ofSubset ({0}ᶜ : Set (TopCat.of W₁))).singularChainComplex R).homology p))]
    [PreservesColimitsOfShape WalkingParallelPair (tensorRight
      (((TopPair.ofSubset ({0}ᶜ : Set (TopCat.of W₂))).singularChainComplex S).cycles q))]
    [PreservesColimitsOfShape WalkingParallelPair (tensorRight
      (((TopPair.ofSubset ({0}ᶜ : Set (TopCat.of W₂))).singularChainComplex S).X
        ((ComplexShape.down ℕ).prev q)))] :
    (TopPair.singularHomologyMap f₁.complZeroPairIso.hom R p ⊗ₘ
        TopPair.singularHomologyMap f₂.complZeroPairIso.hom S q) ≫
      complSingletonPairHomologyCross (0 : W₁) (0 : W₂) v p q n h =
    complSingletonPairHomologyCross (0 : V₁) (0 : V₂) v p q n h ≫
      TopPair.singularHomologyMap (f₁.prodCongr f₂).complZeroPairIso.hom T n := by
  rw [f₁.complZeroPairIso_hom, f₂.complZeroPairIso_hom, f₁.prodCongr_complZeroPairIso_hom f₂]
  exact complSingletonPairHomologyCross_naturality _ _ f₁.mapsTo_compl_zero f₂.mapsTo_compl_zero
    v p q n h

end ContinuousLinearEquiv

end PairCross

section GeneratorCross

open CategoryTheory Limits MonoidalCategory Module

universe w

namespace TauCeti

variable {k : Type w} [CommRing k] {M : Type w} [TopologicalSpace M] [T1Space M] {E : Type w}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  (φ : OpenPartialHomeomorph M E) {x : M} (hx : x ∈ φ.source)

include hx in
/-- **Local homology is cyclic**: at a point with a chart to a real normed space of finite
dimension `r`, the local homology `H_r(M, M ∖ x; k)` is generated by a single class. -/
theorem exists_span_singularHomology_complSingleton_eq_top {r : ℕ} (hr : finrank ℝ E = r) :
    ∃ o : (TopPair.ofSubset ({x}ᶜ : Set (TopCat.of M))).singularHomology
      (C := ModuleCat.{w} k) (𝟙_ _) r, Submodule.span k {o} = ⊤ := by
  subst hr
  let e := (singularHomologyComplSingletonFinrankIso (𝟙_ (ModuleCat.{w} k)) φ hx).toLinearEquiv
  refine ⟨e.symm 1, Submodule.eq_top_iff'.2 fun v ↦ Submodule.mem_span_singleton.2 ⟨e v, ?_⟩⟩
  rw [← map_smul, smul_eq_mul, mul_one, e.symm_apply_apply]

include hx in
/-- **A generator of local homology is a basis.** At a point with a chart to a real normed space
of finite dimension `r`, a generator `o` of `H_r(M, M ∖ x; k)` is a basis: `a ↦ a • o` is a
bijection `k → H_r(M, M ∖ x; k)`, since this module is a copy of `k`. -/
theorem bijective_toSpanSingleton_singularHomology_complSingleton {r : ℕ}
    (hr : finrank ℝ E = r)
    {o : (TopPair.ofSubset ({x}ᶜ : Set (TopCat.of M))).singularHomology
      (C := ModuleCat.{w} k) (𝟙_ _) r} (ho : Submodule.span k {o} = ⊤) :
    Function.Bijective (LinearMap.toSpanSingleton k _ o) := by
  subst hr
  exact (singularHomologyComplSingletonFinrankIso (𝟙_ (ModuleCat.{w} k)) φ hx).toLinearEquiv
    |>.bijective_toSpanSingleton_of_span_eq_top ho

include hx in
/-- **The cross product with a generator of local homology is bijective.** At a point with a chart
to a real normed space of finite dimension `r`, let `o` generate `H_r(M, M ∖ x; k)`. Then for every
chain complex `C` of `k`-modules, the cross product `y ↦ o × y` is a bijection
`H_q(C) → H_{r+q}(C(M, M ∖ x; k) ⊗ C)`: the local homology of `M` at `x` is one copy of `k`, in
degree `r`. -/
theorem bijective_homologyCross_tmul_singularChainComplex_complSingleton
    (C : ChainComplex (ModuleCat.{w} k) ℕ) {r : ℕ} (hr : finrank ℝ E = r)
    {o : (TopPair.ofSubset ({x}ᶜ : Set (TopCat.of M))).singularHomology
      (C := ModuleCat.{w} k) (𝟙_ _) r} (ho : Submodule.span k {o} = ⊤) (q n : ℕ) (hn : r + q = n) :
    Function.Bijective fun y : C.homology q ↦ HomologicalComplex.homologyCross
      ((TopPair.ofSubset ({x}ᶜ : Set (TopCat.of M))).singularChainComplex
        (𝟙_ (ModuleCat.{w} k))) C r q n hn (o ⊗ₜ y) := by
  have hK : ∀ p ≠ r, IsZero (((TopPair.ofSubset ({x}ᶜ : Set (TopCat.of M))).singularChainComplex
      (𝟙_ (ModuleCat.{w} k))).homology p) := fun p hp ↦
    isZero_singularHomology_complSingleton_of_ne _ φ hx hr hp
  -- The relative chains are a retract of the absolute chains, a sum of copies of `k`.
  have (p : ℕ) : Module.Projective k
      (((TopPair.ofSubset ({x}ᶜ : Set (TopCat.of M))).singularChainComplex
        (𝟙_ (ModuleCat.{w} k))).X p) :=
    have : Projective (𝟙_ (ModuleCat.{w} k)) :=
      @ModuleCat.projective_of_categoryTheory_projective _ _ _
        (inferInstanceAs (Module.Projective k k))
    have := SSetPair.projective_chainComplex_X (𝟙_ (ModuleCat.{w} k))
      (TopPair.toSSetPair.obj (TopPair.ofSubset ({x}ᶜ : Set (TopCat.of M)))) p
    ModuleCat.projective_of_module_projective _
  exact HomologicalComplex.bijective_homologyCross_tmul _ C hK
    (bijective_toSpanSingleton_singularHomology_complSingleton φ hx hr ho) q n hn

include hx in
/-- **The relative cross product with a generator of local homology is bijective.** At a point with
a chart to a real normed space of finite dimension `r`, let `o` generate `H_r(M, M ∖ x; k)`. Then
for every space `Y` and every module `L`, the relative cross product `y ↦ o × y` is a bijection
`H_q(Y; L) → H_{r+q}(M × Y, (M ∖ x) × Y; k ⊗ L)`. For `M = E` and `x = 0` this is the Thom
isomorphism of the product bundle `E × Y → Y`. -/
theorem bijective_singularHomologyCrossRel_tmul_complSingleton (Y : TopCat.{w})
    (L : ModuleCat.{w} k) {r : ℕ} (hr : finrank ℝ E = r)
    {o : (TopPair.ofSubset ({x}ᶜ : Set (TopCat.of M))).singularHomology
      (C := ModuleCat.{w} k) (𝟙_ _) r} (ho : Submodule.span k {o} = ⊤) (q n : ℕ) (hn : r + q = n) :
    Function.Bijective fun y : ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{w} k) q).obj
        L).obj Y ↦
      TopCat.singularHomologyCrossRel (TopCat.of M) Y {x}ᶜ (𝟙_ (ModuleCat.{w} k)) L r q n hn
        (o ⊗ₜ y) := by
  -- The relative cross product is the cross product of chain complexes followed by the relative
  -- shuffle map, a quasi-isomorphism.
  have hs := (quasiIsoAt_iff_isIso_homologyMap
    (TopCat.shuffleRel (TopCat.of M) Y {x}ᶜ (𝟙_ (ModuleCat.{w} k)) L) n).1 inferInstance
  simp only [TopCat.singularHomologyCrossRel_def]
  exact ((ConcreteCategory.isIso_iff_bijective _).1 hs).comp
    (bijective_homologyCross_tmul_singularChainComplex_complSingleton φ hx
      ((TopCat.toSSet.obj Y).chainComplex L) hr ho q n hn)

end TauCeti

end GeneratorCross
