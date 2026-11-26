/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.Cap.CrossRel
public import TauCeti.Geometry.Manifold.PontryaginThom.Basic
import Mathlib.Analysis.Convex.Contractible
import TauCeti.AlgebraicTopology.Cohomology.Point
import TauCeti.AlgebraicTopology.Singular.LocalHomology.OpenEmbedding
import Mathlib.AlgebraicTopology.SingularHomology.HomotopyInvariance

/-!
# Capping with the class pulled back by a Pontryagin–Thom collapse

Let `τ : S × V → M` be a framed tube around `f : S → M` (`TauCeti.IsFramedTube`), with `S`
compact, `M` Hausdorff and `V` a real topological vector space, and let `c : M → V⁺ = OnePoint V`
be its Pontryagin–Thom collapse (`TauCeti.pontryaginThomCollapseMap`). A cohomology class of `V⁺`
(the sphere `Sᵏ` for `V = ℝᵏ`) supported near the origin, that is a class
`u ∈ Hᵖ⁺¹(V⁺, V⁺ ∖ 0)` of the pair
(`TauCeti.onePointThomPair`), pulls back along `c` to a class of `(M, M ∖ f(S))`, since the core
`f(S)` is the preimage of the origin. This file computes the cap product with its image
`c^* u ∈ Hᵖ⁺¹(M)` in absolute cohomology: capping a class that restricts along the core to the
image of a cross product `o × x` with `c^* u` gives `⟨u, o⟩ • f_* x`. Informally, and only under
this restriction hypothesis, this says that `c^* u` behaves as a Poincaré dual of the submanifold;
no Poincaré duality statement is proved here.

Let `z ∈ Hₚ₊₁₊q(M)` be a class whose image in `Hₚ₊₁₊q(M, M ∖ f(S))` is the image under the tube of
a relative cross product `o × x`, with `o ∈ Hₚ₊₁(V, V ∖ 0)` and `x ∈ H_q(S)`. Then

`z ⌢ c^* u = ⟨u, o⟩ • f_* x`

in `H_q(M)` (`TauCeti.IsFramedTube.singularCap_pontryaginThomCollapse`), where `⟨u, o⟩` is the
Kronecker pairing of the restriction of `u` to `(V, V ∖ 0)` with `o`. For an oriented closed
manifold `M` of dimension `n + k`, a framed submanifold `S` of dimension `n`, the local orientation
`o ∈ Hₖ(ℝᵏ, ℝᵏ ∖ 0)` of the fibre and the class `u` taking the value `1` on it, take `z = [M]` and
`x = [S]`. The hypothesis then asks that the fundamental class `[M]` restricts along the core to
`o × [S]`, which is the orientation convention *the fibre followed by the core*; this file takes it
as an assumption and does not derive it from orientations of `M` and of the normal framing. Under
it, the formula is `[M] ⌢ c^* u = f_*[S]`, the image of the fundamental class of the submanifold.
With the opposite convention *the core followed by the fibre* of Barraud–Damian–Humilière–Oancea
(Remark 9.2.4), the cross product `[S] × o` differs from `o × [S]` by the sign `(-1)^(n k)` of the
exchange of the factors, so that the formula would read `[M] ⌢ c^* u = (-1)^(n k) f_*[S]`; that
exchange of factors is not proved here.

The proof is the chain of identities

`z ⌢ c^* u = j_* z ⌢ c^* u = T_*(o × x) ⌢ c^* u = T_*((o × x) ⌢ T^* c^* u) = f_*(x ⟨u, o⟩)`,

where `j_* : Hₚ₊₁₊q(M) → Hₚ₊₁₊q(M, M ∖ f(S))` and `T : (V × S, (V ∖ 0) × S) → (M, M ∖ f(S))` is
the tube with its factors exchanged (`TauCeti.IsFramedTube.tubePairMap`). The first step is the
compatibility of the absolute and relative cap products (`TopPair.singularCap_singularCohomologyπ`)
and the third is the projection formula (`TopPair.singularCap_naturality`). For the last, the
collapse reads in the tube as the projection to the fibre, so `T^* c^* u = pr₁^* u|_(V, V ∖ 0)`
(`TauCeti.IsFramedTube.tubePairMap_comp_pontryaginThomCollapsePairMap`); the tube is homotopic to
`f ∘ pr₂` by shrinking the fibre (`TauCeti.IsFramedTube.singularHomologyFunctor_map_tubePairMap`);
and `pr₂_*((o × x) ⌢ pr₁^* u) = ⟨u, o⟩ • x` because `V` is contractible
(`TopCat.singularCap_singularHomologyCrossRel_of_isZero`).

## Main definitions

* `TauCeti.onePointThomPair V`: the pair `(V⁺, V⁺ ∖ 0)`.
* `TauCeti.IsFramedTube.tubeMap`: the tube with its factors exchanged, `(v, x) ↦ τ (x, v)`.
* `TauCeti.IsFramedTube.tubePairMap`: the tube as a map of pairs
  `(V × S, (V ∖ 0) × S) → (M, M ∖ f(S))`.
* `TauCeti.IsFramedTube.pontryaginThomCollapsePairMap`: the collapse as a map of pairs
  `(M, M ∖ f(S)) → (V⁺, V⁺ ∖ 0)`.

## Main results

* `TauCeti.IsFramedTube.isIso_singularHomologyMap_tubePairMap`: excision along the tube, when the
  core is closed.
* `TauCeti.IsFramedTube.tubePairMap_comp_pontryaginThomCollapsePairMap`: the collapse reads in the
  tube as the projection to the fibre.
* `TauCeti.IsFramedTube.singularHomologyFunctor_map_tubePairMap`,
  `TauCeti.IsFramedTube.singularCohomologyMap_tubePairMap`: on singular homology and cohomology the
  tube induces the maps of `f ∘ pr₂`.
* `TauCeti.IsFramedTube.singularCap_pontryaginThomCollapse`: `z ⌢ c^* u = ⟨u, o⟩ • f_* x` when
  `z` restricts along the core to the image of `o × x`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.3 (cap products) and Section 4.D (the Thom class of a product bundle).
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, Remarks 9.2.4 and 9.2.5.
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicTopology Set
  Topology

universe w

namespace TauCeti

section Pairs

variable (V : Type w) [TopologicalSpace V] [Zero V]

/-- The pair `(V⁺, V⁺ ∖ 0)` of the one-point compactification of `V` and the complement of the
origin, the target of the Pontryagin–Thom collapse as a map of pairs. -/
abbrev onePointThomPair : TopPair.{w} :=
  TopPair.ofSubset (X := TopCat.of (OnePoint V)) {((0 : V) : OnePoint V)}ᶜ

/-- The inclusion `(V, V ∖ 0) → (V⁺, V⁺ ∖ 0)` of a space into its one-point compactification, as a
map of pairs. -/
abbrev onePointThomPairIncl :
    TopPair.ofSubset (X := TopCat.of V) {(0 : V)}ᶜ ⟶ onePointThomPair V :=
  TopPair.ofSubsetMap (TopCat.ofHom ⟨((↑) : V → OnePoint V), OnePoint.continuous_coe⟩)
    fun _ hv ↦ by simpa using hv

namespace IsFramedTube

variable {V} {S M : Type w} [TopologicalSpace S] [TopologicalSpace M] {f : S → M}
  {τ : S × V → M}

/-- The tube with its factors exchanged, `(v, x) ↦ τ (x, v)`, as a continuous map: the map of
ambient spaces of `TauCeti.IsFramedTube.tubePairMap`. -/
def tubeMap (h : IsFramedTube f τ) : C((TopCat.of V ⊗ TopCat.of S : TopCat), M) :=
  ⟨fun p ↦ τ (snd (TopCat.of V) (TopCat.of S) p, fst (TopCat.of V) (TopCat.of S) p),
    h.isOpenEmbedding.continuous.comp
      ((snd (TopCat.of V) (TopCat.of S)).hom.continuous.prodMk
        (fst (TopCat.of V) (TopCat.of S)).hom.continuous)⟩

/-- The tube with its factors exchanged sends `(v, x)` to `τ (x, v)`. -/
@[simp]
theorem tubeMap_apply (h : IsFramedTube f τ) (p : (TopCat.of V ⊗ TopCat.of S : TopCat)) :
    h.tubeMap p = τ (snd (TopCat.of V) (TopCat.of S) p, fst (TopCat.of V) (TopCat.of S) p) :=
  (rfl)

/-- The tube with its factors exchanged is an open embedding. -/
theorem isOpenEmbedding_tubeMap (h : IsFramedTube f τ) : IsOpenEmbedding h.tubeMap :=
  h.isOpenEmbedding.comp (Homeomorph.prodComm V S).isOpenEmbedding

/-- The core is the image of the zero section, and only of it. -/
theorem preimage_tubeMap_range (h : IsFramedTube f τ) :
    h.tubeMap ⁻¹' range f = fst (TopCat.of V) (TopCat.of S) ⁻¹' {0} := by
  ext p
  refine ⟨fun ⟨y, hy⟩ ↦ ?_, fun hp ↦ ⟨snd (TopCat.of V) (TopCat.of S) p, ?_⟩⟩
  · rw [← h.apply_zero] at hy
    exact (congrArg Prod.snd (h.isOpenEmbedding.injective hy)).symm
  · rw [← h.apply_zero]
    exact congrArg (fun v ↦ τ (snd (TopCat.of V) (TopCat.of S) p, v)) hp.symm

/-- **The framed tube as a map of pairs**: the tube with its factors exchanged,
`(v, x) ↦ τ (x, v)`, carries the Thom pair `(V × S, (V ∖ 0) × S)` of the product bundle into the
complement of the core, `(M, M ∖ f(S))`. -/
def tubePairMap (h : IsFramedTube f τ) :
    TopPair.ofSubset (fst (TopCat.of V) (TopCat.of S) ⁻¹' {(0 : V)}ᶜ) ⟶
      TopPair.ofSubset (X := TopCat.of M) (range f)ᶜ :=
  TopPair.ofSubsetMap (TopCat.ofHom h.tubeMap) fun _ hp hpf ↦
    hp ((h.preimage_tubeMap_range).subset hpf)

/-- The tube as a map of pairs is the map of pairs induced by the tube with its factors
exchanged. -/
theorem tubePairMap_def (h : IsFramedTube f τ) :
    h.tubePairMap = TopPair.ofSubsetMap (B := fst (TopCat.of V) (TopCat.of S) ⁻¹' {(0 : V)}ᶜ)
      (B' := (range f)ᶜ) (TopCat.ofHom h.tubeMap) fun _ hp hpf ↦
        hp ((h.preimage_tubeMap_range).subset hpf) :=
  (rfl)

/-- The tube as a map of pairs is the tube with its factors exchanged on the ambient spaces. -/
@[simp]
theorem tubePairMap_fst (h : IsFramedTube f τ) :
    TopPair.Hom.fst h.tubePairMap = TopCat.ofHom h.tubeMap :=
  TopPair.ofSubsetMap_fst _ _

/-- The tube as a map of pairs sends `(v, x)` to `τ (x, v)`. -/
theorem tubePairMap_fst_apply (h : IsFramedTube f τ)
    (p : (TopCat.of V ⊗ TopCat.of S : TopCat)) :
    TopPair.Hom.fst h.tubePairMap p =
      τ (snd (TopCat.of V) (TopCat.of S) p, fst (TopCat.of V) (TopCat.of S) p) :=
  TopPair.ofSubsetMap_fst_apply _ _ p

/-- **Excision along the tube**: when the core is closed, `(V × S, (V ∖ 0) × S) → (M, M ∖ f(S))`
induces isomorphisms on relative homology. -/
theorem isIso_singularHomologyMap_tubePairMap (h : IsFramedTube f τ) (hf : IsClosed (range f))
    {A : Type*} [Category* A] [HasCoproducts.{w} A] [Abelian A] (N : A) (n : ℕ) :
    IsIso (TopPair.singularHomologyMap h.tubePairMap N n) := by
  have := isIso_localHomologyMap N h.tubeMap h.isOpenEmbedding_tubeMap h.preimage_tubeMap_range hf
    (by rintro _ ⟨x, rfl⟩; exact ⟨((0 : V), x), h.apply_zero x⟩) n
  rwa [localHomologyMap_def] at this

variable [CompactSpace S] [T2Space M]

/-- **The Pontryagin–Thom collapse as a map of pairs**: the collapse `c : M → V⁺` carries the
complement of the core into the complement of the origin, since the core is the preimage of the
origin (`TauCeti.IsFramedTube.pontryaginThomCollapse_eq_zero_iff`). -/
def pontryaginThomCollapsePairMap (h : IsFramedTube f τ) :
    TopPair.ofSubset (X := TopCat.of M) (range f)ᶜ ⟶ onePointThomPair V :=
  TopPair.ofSubsetMap (TopCat.ofHom (pontryaginThomCollapseMap h.isOpenEmbedding))
    fun _ hm hc ↦ hm (h.pontryaginThomCollapse_eq_zero_iff.1 (by simpa using hc))

/-- The collapse as a map of pairs is the collapse on the ambient spaces. -/
@[simp]
theorem pontryaginThomCollapsePairMap_fst (h : IsFramedTube f τ) :
    TopPair.Hom.fst h.pontryaginThomCollapsePairMap =
      TopCat.ofHom (pontryaginThomCollapseMap h.isOpenEmbedding) :=
  TopPair.ofSubsetMap_fst _ _

/-- **The collapse reads in the tube as the projection to the fibre**: the tube followed by the
collapse is the projection `(V × S, (V ∖ 0) × S) → (V, V ∖ 0)` followed by the inclusion into
`(V⁺, V⁺ ∖ 0)`. -/
theorem tubePairMap_comp_pontryaginThomCollapsePairMap (h : IsFramedTube f τ) :
    h.tubePairMap ≫ h.pontryaginThomCollapsePairMap =
      TopPair.ofSubsetMap (fst (TopCat.of V) (TopCat.of S)) (mapsTo_preimage _ _) ≫
        onePointThomPairIncl V := by
  refine TopPair.ofSubsetMap_comp_ofSubsetMap_eq _ _ _ _ ?_
  refine ConcreteCategory.hom_ext _ _ fun p ↦ ?_
  simp only [ConcreteCategory.comp_apply, ConcreteCategory.hom_ofHom,
    ContinuousMap.coe_mk, coe_pontryaginThomCollapseMap]
  exact pontryaginThomCollapse_apply h.isOpenEmbedding.injective _ _

end IsFramedTube

end Pairs

namespace IsFramedTube

section Cap

variable {V : Type w} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V] [ContinuousSMul ℝ V]
  {S M : Type w} [TopologicalSpace S] [TopologicalSpace M] {f : S → M}
  {τ : S × V → M}

/-- **The tube is homotopic to the core composed with the projection.** Shrinking the fibre,
`(t, (v, x)) ↦ τ (x, t • v)`, joins the tube with its factors exchanged to `(v, x) ↦ f x`. -/
private noncomputable def tubePairMapHomotopy (h : IsFramedTube f τ) :
    TopCat.Homotopy (snd (TopCat.of V) (TopCat.of S) ≫ TopCat.ofHom ⟨f, h.continuous⟩)
      (TopPair.Hom.fst h.tubePairMap) where
  toFun tp := τ (snd (TopCat.of V) (TopCat.of S) tp.2,
    (tp.1 : ℝ) • fst (TopCat.of V) (TopCat.of S) tp.2)
  continuous_toFun := h.isOpenEmbedding.continuous.comp
    (((snd (TopCat.of V) (TopCat.of S)).hom.continuous.comp continuous_snd).prodMk
      ((continuous_subtypeVal.comp continuous_fst).smul
        ((fst (TopCat.of V) (TopCat.of S)).hom.continuous.comp continuous_snd)))
  map_zero_left p := by
    simp [h.apply_zero]
  map_one_left p := by
    dsimp
    rw [one_smul]
    exact (h.tubePairMap_fst_apply p).symm

/-- **The tube is homotopic to the core composed with the projection**, so on singular homology the
tube with its factors exchanged induces the map of `(v, x) ↦ f x`. -/
theorem singularHomologyFunctor_map_tubePairMap (h : IsFramedTube f τ) {C : Type*} [Category C]
    [Preadditive C] [HasCoproducts.{w} C] [CategoryWithHomology C] (A : C) (n : ℕ) :
    ((singularHomologyFunctor C n).obj A).map (TopPair.Hom.fst h.tubePairMap) =
      ((singularHomologyFunctor C n).obj A).map (snd (TopCat.of V) (TopCat.of S)) ≫
        ((singularHomologyFunctor C n).obj A).map (TopCat.ofHom ⟨f, h.continuous⟩) := by
  rw [← Functor.map_comp, singularHomologyFunctor_obj_map, singularHomologyFunctor_obj_map]
  -- `SSet.homologyMap` of the singular simplicial map is the homology of the map of singular
  -- chains by definition.
  exact (TopCat.Homotopy.congr_homologyMap_singularChainComplexFunctor
    (tubePairMapHomotopy h) A n).symm

/-- **The tube is homotopic to the core composed with the projection**, so on singular cohomology
the tube with its factors exchanged pulls classes back as `(v, x) ↦ f x` does. -/
theorem singularCohomologyMap_tubePairMap (h : IsFramedTube f τ) {C : Type*} [Category C]
    [HasCoproducts.{w} C] [Abelian C] (R : C) (k : Type*) [Ring k] [Linear k C] (N : C) (n : ℕ) :
    TopCat.singularCohomologyMap (R := R) (k := k) (M := N) (TopPair.Hom.fst h.tubePairMap) n =
      TopCat.singularCohomologyMap (TopCat.ofHom ⟨f, h.continuous⟩) n ≫
        TopCat.singularCohomologyMap (snd (TopCat.of V) (TopCat.of S)) n := by
  rw [← TopCat.singularCohomologyMap_comp]
  exact ((tubePairMapHomotopy h).congr_singularCohomologyMap R k N n).symm

variable [ContinuousAdd V] [CompactSpace S] [T2Space M] {k : Type w} [CommRing k]
  {R L : ModuleCat.{w} k} {p q : ℕ}

/-- **Capping with the class pulled back by a Pontryagin–Thom collapse.** Let `τ : S × V → M` be a
framed tube around `f : S → M`, with compact `S` and Hausdorff `M`, `c : M → V⁺` its collapse, and
`u ∈ Hᵖ⁺¹(V⁺, V⁺ ∖ 0)`. If the image in `Hₚ₊q₊₁(M, M ∖ f(S))` of a class `z ∈ Hₚ₊q₊₁(M)` is the
image under the tube of the relative cross product `o × x` of `o ∈ Hₚ₊₁(V, V ∖ 0)` and
`x ∈ H_q(S)`, then capping `z` with the pull-back `c^* u` of `u` to absolute cohomology gives
`⟨u, o⟩ • f_* x`, where `⟨u, o⟩` is the Kronecker pairing of the restriction of `u` to
`(V, V ∖ 0)` with `o`. -/
theorem singularCap_pontryaginThomCollapse (h : IsFramedTube f τ)
    (u : (onePointThomPair V).singularCohomology R k (𝟙_ (ModuleCat.{w} k)) (p + 1))
    (o : ((TopPair.ofSubset (X := TopCat.of V) {(0 : V)}ᶜ).singularHomology R (p + 1) :
      ModuleCat.{w} k))
    (x : ((singularHomologyFunctor (ModuleCat.{w} k) q).obj L).obj (TopCat.of S))
    (z : ((singularHomologyFunctor (ModuleCat.{w} k) (p + q + 1)).obj (R ⊗ L)).obj (TopCat.of M))
    (hz : (TopPair.ofSubset (X := TopCat.of M) (range f)ᶜ).singularHomologyπ (R ⊗ L) (p + q + 1) z =
      TopPair.singularHomologyMap h.tubePairMap (R ⊗ L) (p + q + 1)
        (TopCat.singularHomologyCrossRel (TopCat.of V) (TopCat.of S) {(0 : V)}ᶜ R L (p + 1) q
          (p + q + 1) (by omega) (o ⊗ₜ x))) :
    (TopCat.of M).singularCap k (𝟙 (R ⊗ L)) (λ_ L).hom (p + 1) q (p + q + 1) (by omega)
        (TopCat.singularCohomologyMap (TopCat.ofHom (pontryaginThomCollapseMap h.isOpenEmbedding))
          (p + 1) ((onePointThomPair V).singularCohomologyπ R k (𝟙_ _) (p + 1) u)) z =
      ((TopPair.ofSubset (X := TopCat.of V) {(0 : V)}ᶜ).singularKronecker k (p + 1)
          (TopPair.singularCohomologyMap (onePointThomPairIncl V) (p + 1) u) o : k) •
        ((singularHomologyFunctor (ModuleCat.{w} k) q).obj L).map
          (TopCat.ofHom ⟨f, h.continuous⟩) x := by
  have h₁ := ConcreteCategory.congr_hom (TopPair.singularCohomologyπ_naturality (R := R) (k := k)
    (M := 𝟙_ (ModuleCat.{w} k)) h.pontryaginThomCollapsePairMap (p + 1)) u
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply,
    h.pontryaginThomCollapsePairMap_fst] at h₁
  refine (congrArg (fun a ↦ (TopCat.of M).singularCap k (𝟙 (R ⊗ L)) (λ_ L).hom (p + 1) q
    (p + q + 1) (by omega) a z) h₁).trans ?_
  refine (ConcreteCategory.congr_hom (TopPair.singularCap_singularCohomologyπ
    (TopPair.ofSubset (X := TopCat.of M) (range f)ᶜ) k (𝟙 (R ⊗ L)) (λ_ L).hom (p + 1) q
    (p + q + 1) (by omega)
    (TopPair.singularCohomologyMap h.pontryaginThomCollapsePairMap (p + 1) u)) z).trans ?_
  refine ((ConcreteCategory.comp_apply _ _ z).trans (congrArg _ hz)).trans ?_
  have h₂ := ConcreteCategory.congr_hom (TopPair.singularCap_naturality h.tubePairMap k
    (𝟙 (R ⊗ L)) (λ_ L).hom (p + 1) q (p + q + 1) (by omega)
    (TopPair.singularCohomologyMap h.pontryaginThomCollapsePairMap (p + 1) u))
    (TopCat.singularHomologyCrossRel (TopCat.of V) (TopCat.of S) {(0 : V)}ᶜ R L (p + 1) q
          (p + q + 1) (by omega) (o ⊗ₜ x))
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at h₂
  refine h₂.symm.trans ?_
  rw [← TopPair.singularCohomologyMap_comp_apply,
    tubePairMap_comp_pontryaginThomCollapsePairMap, TopPair.singularCohomologyMap_comp_apply,
    h.singularHomologyFunctor_map_tubePairMap]
  refine (ConcreteCategory.comp_apply _ _ _).trans ?_
  have : ContractibleSpace (TopCat.of V) := inferInstanceAs (ContractibleSpace V)
  exact (congrArg _ (TopCat.singularCap_singularHomologyCrossRel_of_isZero
    (isZero_singularCohomology_of_contractibleSpace _ _ _ (TopCat.of V) (by omega)) _ o x)).trans
    (map_smul _ _ _)

end Cap

end IsFramedTube

end TauCeti
