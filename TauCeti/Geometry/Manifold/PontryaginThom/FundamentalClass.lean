/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Kunneth.Pair
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.IsFundamentalClass
public import TauCeti.Geometry.Manifold.PontryaginThom.Cap
import TauCeti.Algebra.Module.Equiv.SpanSingleton
import TauCeti.AlgebraicTopology.Singular.LocalHomology.Cross
import TauCeti.AlgebraicTopology.Singular.LocalHomology.OpenEmbedding

/-!
# Fundamental classes along a framed tube

Let `τ : S × V → M` be a framed tube around `f : S → M` (`TauCeti.IsFramedTube`), with `V` a real
normed space of finite dimension `r`, and let `o` generate the local homology
`H_r(V, V ∖ 0; k) ≅ k` with coefficients in a commutative ring `k`. The relative cross product with
`o`, followed by the tube, is the Thom isomorphism of the framed submanifold

`H_q(S; L) ≅ H_{r+q}(M, M ∖ f(S); k ⊗ L)`, `x ↦ τ_*(o × x)`,

for every coefficient module `L`, when the core `f(S)` is closed, as it is for compact `S` and
Hausdorff `M`
(`TauCeti.IsFramedTube.bijective_singularHomologyMap_tubePairMap_singularHomologyCrossRel`): by
excision (`TauCeti.IsFramedTube.isIso_singularHomologyMap_tubePairMap`) the right side is the
homology of `(V × S, (V ∖ 0) × S)`, and the relative Künneth theorem for the free local homology of
`V` at `0`
(`TauCeti.bijective_singularHomologyCrossRel_tmul_complSingleton`) gives the suspension
by `o`. Bundled as a linear equivalence, it is `TauCeti.IsFramedTube.homologyThomEquiv`. So every
class `z ∈ H_{r+q}(M; k ⊗ L)` determines a unique class `x ∈ H_q(S; L)` whose image under the tube
is the image of `z` in `H_{r+q}(M, M ∖ f(S))`: its image `x = i_!(z)` under the shriek map
`TauCeti.IsFramedTube.shriek`, the map to `H_{r+q}(M, M ∖ f(S))` followed by the inverse of the
Thom isomorphism (`TauCeti.IsFramedTube.singularHomologyπ_eq_shriek`,
`TauCeti.IsFramedTube.shriek_eq_iff`).

This class is local in `S`: at a point `s`, the image of `x` in the local homology
`H_q(S, S ∖ s; L)` generates it exactly when the image of `z` in `H_{r+q}(M, M ∖ f s; k ⊗ L)`
does (`TauCeti.IsFramedTube.span_singularHomologyToLocalHomology_eq_top_iff`). The cross product
with `o` of the pair `(S, S ∖ s)`, through the shuffle map of a product of pairs, is again a
bijection onto the local homology of `V × S` at `(0, s)`, which the tube carries onto the local
homology of `M` at `f s`; restriction to `s` commutes with all these maps
(`TopCat.singularHomologyCrossRel_comp_singularHomologyMap`). Hence the class of a
fundamental class of `M` is a fundamental class of `S`
(`TauCeti.IsFramedTube.isFundamentalClass_of_singularHomologyπ_eq`): the fundamental class of
`M`, localized along the core, is the cross product of the generator `o` of the fibre with a
fundamental class of `S`. No orientation is chosen on `S`: the fundamental class of `S` is the one
induced by `[M]` and `o`, and it depends on both.

This is the restriction hypothesis of `TauCeti.IsFramedTube.singularCap_pontryaginThomCollapse`,
derived rather than assumed. For a fundamental class `[M]` and a framing of codimension
`r = p + 1`, the class `c^* u` pulled back by the Pontryagin–Thom collapse `c : M → V⁺` caps `[M]`
to `⟨u, o⟩ • f_*[S]` for a fundamental class `[S]` of `S`
(`TauCeti.IsFramedTube.exists_isFundamentalClass_singularCap_pontryaginThomCollapse`). For the
class `u` taking the value `1` on `o`, this says that `c^* u` caps the fundamental class of `M` to
the image of a fundamental class of the submanifold.

The order of the factors is a convention. Barraud, Damian, Humilière and Oancea orient the
submanifold so that its orientation followed by that of the fibre is the orientation of `M`
(Remark 9.2.4): at each point `s`, the local class of `[M]` at `f s` is the image under the tube
of `[S]_s × o`, the core first (`TauCeti.IsFramedTube.localCross`, through the tube at `s`,
`TauCeti.IsFramedTube.localPairMap`). Exchanging the factors of the cross product of pairs costs
the Koszul sign (`TopCat.homologyCross_comp_homologyMap_shufflePair_comp_braiding`), so at every
point the class `x` induced in the order "fibre followed by core" satisfies the convention "core
followed by fibre" up to the sign `(-1)^(r * q)`
(`TauCeti.IsFramedTube.singularHomologyToLocalHomology_eq_neg_one_pow_smul`). In this
convention the cap formula reads `[M] ⌢ c^* u = (-1)^(r * q) ⟨u, o⟩ • f_*[S]` for a core of
dimension `q` and a fibre of dimension `r`: for every class satisfying the convention when `S` is
a compact manifold
(`TauCeti.IsFramedTube.singularCap_pontryaginThomCollapse_of_singularHomologyToLocalHomology_eq`),
and for a fundamental class of `S` that satisfies it, which always exists
(`IsFramedTube.exists_isFundamentalClass_singularHomologyToLocalHomology_eq_and_singularCap`).

## Main definitions

* `TauCeti.IsFramedTube.homologyThomEquiv`: the Thom isomorphism `x ↦ τ_*(o × x)`.
* `TauCeti.IsFramedTube.shriek`: the shriek map `i_!` of a framed submanifold, which sends a class
  of `M` to the class of the core it determines.

## Main results

* `TauCeti.IsFramedTube.bijective_singularHomologyMap_tubePairMap_singularHomologyCrossRel`: the
  Thom isomorphism `x ↦ τ_*(o × x)` of a framed submanifold is a bijection.
* `TauCeti.IsFramedTube.singularHomologyπ_eq_shriek`, `TauCeti.IsFramedTube.shriek_eq_iff`: the
  class `i_!(z)` of the core is the unique `x` with `z ↦ τ_*(o × x)`.
* `TauCeti.IsFramedTube.span_singularHomologyToLocalHomology_eq_top_iff`: that class generates the
  local homology of `S` at `s` exactly when the class of `M` generates it at `f s`.
* `TauCeti.IsFramedTube.isFundamentalClass_of_singularHomologyπ_eq`: the class of the core
  determined by a fundamental class of `M` is a fundamental class of `S`.
* `TauCeti.IsFramedTube.exists_isFundamentalClass_singularCap_pontryaginThomCollapse`:
  `[M] ⌢ c^* u = ⟨u, o⟩ • f_*[S]` for a fundamental class `[S]` of `S`.
* `TauCeti.IsFramedTube.singularHomologyToLocalHomology_eq_neg_one_pow_smul`: at each point, the
  local class of `z` is `(-1)^(r * q)` times the image under the tube of `x × o`, core first.
* `TauCeti.IsFramedTube.singularCap_pontryaginThomCollapse_of_singularHomologyToLocalHomology_eq`,
  `IsFramedTube.exists_isFundamentalClass_singularHomologyToLocalHomology_eq_and_singularCap`:
  `[M] ⌢ c^* u = (-1)^(r * q) ⟨u, o⟩ • f_*[S]` for `S` oriented by "core followed by fibre".

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.3 (fundamental classes through local homology), Section 3.B (the relative Künneth
  formula) and Section 4.D (the Thom class of a product bundle).
* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton University Press, 1974, §11 (the Thom isomorphism of a tubular neighbourhood).
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, Remarks 9.2.4 and 9.2.5.
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicTopology Set
  Topology Module

universe w

namespace TauCeti

namespace IsFramedTube

section Tube

variable {V : Type w} [NormedAddCommGroup V] {S M : Type w} [TopologicalSpace S]
  [TopologicalSpace M] {f : S → M} {τ : S × V → M}

/-- The tube with its factors exchanged carries the complement of `(0, s)` in `V × S`, written as
`(V ∖ 0) × S ∪ V × (S ∖ s)`, into the complement of `f s`. -/
theorem mapsTo_tubeMap_preimage_union (h : IsFramedTube f τ) (s : S) :
    MapsTo h.tubeMap (fst (TopCat.of V) (TopCat.of S) ⁻¹' {(0 : V)}ᶜ ∪
      snd (TopCat.of V) (TopCat.of S) ⁻¹' ({s}ᶜ : Set (TopCat.of S))) {f s}ᶜ := by
  rintro p hp (hps : h.tubeMap p = f s)
  rw [tubeMap_apply, ← h.apply_zero] at hps
  have := h.isOpenEmbedding.injective hps
  rcases hp with hp | hp
  · exact hp (congrArg Prod.snd this)
  · exact hp (congrArg Prod.fst this)

/-- The tube as a map from the pair `(V × S, V × S ∖ {(0, s)})`, written as in the cross product of
the pairs `(V, V ∖ 0)` and `(S, S ∖ s)`, to the local pair `(M, M ∖ {f s})`. -/
private def tubeLocalPairMap (h : IsFramedTube f τ) (s : S) :
    TopPair.ofSubset (fst (TopCat.of V) (TopCat.of S) ⁻¹' {(0 : V)}ᶜ ∪
      snd (TopCat.of V) (TopCat.of S) ⁻¹' ({s}ᶜ : Set (TopCat.of S))) ⟶
      TopPair.ofSubset ({f s}ᶜ : Set (TopCat.of M)) :=
  TopPair.ofSubsetMap (TopCat.ofHom h.tubeMap) (h.mapsTo_tubeMap_preimage_union s)

/-- **Excision at a point of the core**: the tube induces isomorphisms from the local homology of
`V × S` at `(0, s)` to that of `M` at `f s`. -/
private lemma isIso_singularHomologyMap_tubeLocalPairMap [T1Space M] (h : IsFramedTube f τ)
    (s : S) {A : Type*} [Category* A] [HasCoproducts.{w} A] [Abelian A] (N : A) (n : ℕ) :
    IsIso (TopPair.singularHomologyMap (tubeLocalPairMap h s) N n) := by
  have hU := TopCat.preimage_fst_compl_union_preimage_snd_compl (X := TopCat.of V)
    (Y := TopCat.of S) (0 : V) s
  -- Transport the excision isomorphism at `(0, s)` along the equality of subsets and along
  -- `h.tubeMap (0, s) = f s`.
  have key : ∀ (U : Set (TopCat.of V ⊗ TopCat.of S : TopCat)) (y : M), U = {((0 : V), s)}ᶜ →
      h.tubeMap ((0 : V), s) = y →
      ∀ hm : MapsTo (TopCat.ofHom h.tubeMap) U ({y}ᶜ : Set (TopCat.of M)),
      IsIso (TopPair.singularHomologyMap (TopPair.ofSubsetMap _ hm) N n) := by
    rintro U y rfl rfl _
    -- `rw [localHomologyIsoOfIsOpenEmbedding_hom]` finds no instance of its left side in
    -- `IsIso (localHomologyIsoOfIsOpenEmbedding ..).hom`, so the equation is applied with `▸`.
    have := localHomologyIsoOfIsOpenEmbedding_hom N h.isOpenEmbedding_tubeMap ((0 : V), s) n ▸
      (localHomologyIsoOfIsOpenEmbedding N h.isOpenEmbedding_tubeMap ((0 : V), s) n).isIso_hom
    rwa [localHomologyMap_def] at this
  exact key _ _ hU ((h.tubeMap_apply _).trans (h.apply_zero s)) _

/-- **The tube at a point of the core, as a map of pairs.** At `s : S`, the tube `τ : S × V → M`
maps the pair `(S × V, S × V ∖ {(s, 0)})`, written as in the cross product of the pairs
`(S, S ∖ s)` and `(V, V ∖ 0)`, with the core first, to the local pair `(M, M ∖ {f s})`. It is the
swap `S × V ⟶ V × S` followed by the tube with its factors exchanged. -/
def localPairMap (h : IsFramedTube f τ) (s : S) :
    TopPair.ofSubset (fst (TopCat.of S) (TopCat.of V) ⁻¹' ({s}ᶜ : Set (TopCat.of S)) ∪
      snd (TopCat.of S) (TopCat.of V) ⁻¹' {(0 : V)}ᶜ) ⟶
      TopPair.ofSubset ({f s}ᶜ : Set (TopCat.of M)) :=
  TopPair.ofSubsetMap (β_ (TopCat.of S) (TopCat.of V)).hom
    (TopCat.mapsTo_braiding_hom_preimage_union _ _ _ _) ≫ tubeLocalPairMap h s

/-- The tube at a point of the core, as a map of pairs, is induced by the swap `S × V ⟶ V × S`
followed by the tube with its factors exchanged. -/
theorem localPairMap_def (h : IsFramedTube f τ) (s : S) :
    h.localPairMap s = TopPair.ofSubsetMap
      ((β_ (TopCat.of S) (TopCat.of V)).hom ≫ TopCat.ofHom h.tubeMap)
      ((h.mapsTo_tubeMap_preimage_union s).comp
        (TopCat.mapsTo_braiding_hom_preimage_union _ _ _ _)) :=
  (TopPair.ofSubsetMap_comp _ _ _ _ _).symm

/-- The map of ambient spaces of `TauCeti.IsFramedTube.localPairMap` is the swap followed by the
tube with its factors exchanged. -/
@[simp]
theorem localPairMap_fst (h : IsFramedTube f τ) (s : S) :
    TopPair.Hom.fst (h.localPairMap s) =
      (β_ (TopCat.of S) (TopCat.of V)).hom ≫ TopCat.ofHom h.tubeMap := by
  rw [localPairMap_def, TopPair.ofSubsetMap_fst]

/-- The map of ambient spaces of `TauCeti.IsFramedTube.localPairMap` is the tube. -/
theorem localPairMap_fst_apply (h : IsFramedTube f τ) (s : S)
    (p : (TopCat.of S ⊗ TopCat.of V : TopCat)) :
    TopPair.Hom.fst (h.localPairMap s) p =
      τ (fst (TopCat.of S) (TopCat.of V) p, snd (TopCat.of S) (TopCat.of V) p) := by
  rw [localPairMap_def]
  refine (TopPair.ofSubsetMap_fst_apply _ _ p).trans ?_
  rw [TopCat.comp_app, TopCat.ofHom_apply, tubeMap_apply, ← ConcreteCategory.comp_apply,
    braiding_hom_snd, ← ConcreteCategory.comp_apply, braiding_hom_fst]

variable {k : Type w} [CommRing k] (L : ModuleCat.{w} k) [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-! ### The class of the core at a point -/

/-- At a point `s` of `S`, the cross product with `o`, followed by the tube, is a bijection from the
local homology of `S` at `s` to the local homology of `M` at `f s`. -/
private lemma bijective_localHomology [T1Space S] [T1Space M] (h : IsFramedTube f τ) (s : S)
    {r : ℕ} (hr : finrank ℝ V = r)
    {o : (TopPair.ofSubset (X := TopCat.of V) {(0 : V)}ᶜ).singularHomology
      (C := ModuleCat.{w} k) (𝟙_ _) r} (ho : Submodule.span k {o} = ⊤) (q n : ℕ) (hn : r + q = n) :
    Function.Bijective ((HomologicalComplex.homologyCross
          ((TopPair.ofSubset (X := TopCat.of V) {(0 : V)}ᶜ).singularChainComplex
            (𝟙_ (ModuleCat.{w} k)))
          ((TopPair.ofSubset ({s}ᶜ : Set (TopCat.of S))).singularChainComplex L) r q n hn ≫
        HomologicalComplex.homologyMap (TopCat.shufflePair (TopCat.of V) (TopCat.of S) {(0 : V)}ᶜ
          {s}ᶜ (𝟙_ (ModuleCat.{w} k)) L) n ≫
        TopPair.singularHomologyMap (tubeLocalPairMap h s) (𝟙_ (ModuleCat.{w} k) ⊗ L) n).hom ∘ₗ
      TensorProduct.mk k _ _ o) := by
  have := TopCat.quasiIso_shufflePair_of_isOpen (TopCat.of V) (TopCat.of S)
    (A := {(0 : V)}ᶜ) (B := ({s}ᶜ : Set (TopCat.of S))) (𝟙_ (ModuleCat.{w} k)) L
    isClosed_singleton.isOpen_compl isClosed_singleton.isOpen_compl
  have hs := (quasiIsoAt_iff_isIso_homologyMap
    (TopCat.shufflePair (TopCat.of V) (TopCat.of S) {(0 : V)}ᶜ ({s}ᶜ : Set (TopCat.of S))
      (𝟙_ (ModuleCat.{w} k)) L) n).1 inferInstance
  exact ((ConcreteCategory.isIso_iff_bijective _).1
      (isIso_singularHomologyMap_tubeLocalPairMap h s (𝟙_ (ModuleCat.{w} k) ⊗ L) n)).comp
    (((ConcreteCategory.isIso_iff_bijective _).1 hs).comp
      (bijective_homologyCross_tmul_singularChainComplex_complSingleton
        (OpenPartialHomeomorph.refl V) (mem_univ (0 : V)) _ hr ho q n hn))

omit [NormedSpace ℝ V] [FiniteDimensional ℝ V] in
/-- The image of `z` in the local homology of `M` at `f s` is the image under the tube of `o × x`,
restricted to `s`: restrict to `(V × S, V × S ∖ {(0, s)})` and apply the tube, or apply the tube and
restrict to `(M, M ∖ {f s})`. -/
private lemma singularHomologyToLocalHomology_eq_tubeLocalPairMap
    (h : IsFramedTube f τ) {r : ℕ}
    {o : (TopPair.ofSubset (X := TopCat.of V) {(0 : V)}ᶜ).singularHomology
      (C := ModuleCat.{w} k) (𝟙_ _) r} {q n : ℕ}
    (hn : r + q = n) {x : ((singularHomologyFunctor (ModuleCat.{w} k) q).obj L).obj (TopCat.of S)}
    {z : ((singularHomologyFunctor (ModuleCat.{w} k) n).obj (𝟙_ (ModuleCat.{w} k) ⊗ L)).obj
      (TopCat.of M)}
    (hz : (TopPair.ofSubset (X := TopCat.of M) (range f)ᶜ).singularHomologyπ
        (𝟙_ (ModuleCat.{w} k) ⊗ L) n z =
      TopPair.singularHomologyMap h.tubePairMap (𝟙_ (ModuleCat.{w} k) ⊗ L) n
        (TopCat.singularHomologyCrossRel (TopCat.of V) (TopCat.of S) {(0 : V)}ᶜ
          (𝟙_ (ModuleCat.{w} k)) L r q n hn (o ⊗ₜ x))) (s : S) :
    singularHomologyToLocalHomology (𝟙_ (ModuleCat.{w} k) ⊗ L) (f s) n z =
      (HomologicalComplex.homologyCross
          ((TopPair.ofSubset (X := TopCat.of V) {(0 : V)}ᶜ).singularChainComplex
            (𝟙_ (ModuleCat.{w} k)))
          ((TopPair.ofSubset ({s}ᶜ : Set (TopCat.of S))).singularChainComplex L) r q n hn ≫
        HomologicalComplex.homologyMap (TopCat.shufflePair (TopCat.of V) (TopCat.of S) {(0 : V)}ᶜ
          {s}ᶜ (𝟙_ (ModuleCat.{w} k)) L) n ≫
        TopPair.singularHomologyMap (tubeLocalPairMap h s) (𝟙_ (ModuleCat.{w} k) ⊗ L) n).hom
        (o ⊗ₜ singularHomologyToLocalHomology L s q x) := by
  have hmap : h.tubePairMap ≫ TopPair.ofSubsetMap (𝟙 (TopCat.of M))
      (compl_subset_compl.2 (singleton_subset_iff.2 (mem_range_self s))) =
      TopPair.ofSubsetMap (𝟙 _) (fun _ hz ↦ Or.inl hz) ≫ tubeLocalPairMap h s := by
    rw [h.tubePairMap_def]
    exact TopPair.ofSubsetMap_comp_ofSubsetMap_eq _ _ _ _
      ((Category.comp_id _).trans (Category.id_comp _).symm)
  have hcross := TopCat.singularHomologyCrossRel_comp_singularHomologyMap (TopCat.of V)
    (TopCat.of S) {(0 : V)}ᶜ ({s}ᶜ : Set (TopCat.of S)) (𝟙_ (ModuleCat.{w} k)) L r q n hn
  symm
  rw [singularHomologyToLocalHomology_eq_singularHomologyπ L s x,
    singularHomologyToLocalHomology_eq_localHomologyRestriction _ (mem_range_self s) z, hz,
    localHomologyRestriction_def, ← ConcreteCategory.comp_apply,
    ← TopPair.singularHomologyMap_comp, hmap, TopPair.singularHomologyMap_comp,
    ← ConcreteCategory.comp_apply (TopCat.singularHomologyCrossRel _ _ _ _ _ _ _ _ _),
    reassoc_of% hcross]
  -- Both sides apply `tube ∘ shuffle ∘ cross` to `o ⊗ x|_s`, where `(𝟙 ⊗ π) (o ⊗ x) = o ⊗ π x`.
  -- `simp` cannot evaluate the left side: there `x` lies in `H_q(S; L)` as a value of
  -- `singularHomologyFunctor`, which is the source of `singularHomologyπ` only up to unfolding.
  rfl

/-- **The class of the core is local.** Let `τ : S × V → M` be a framed tube around `f`, with `M` a
`T₁` space and `V` of dimension `r`, let `o` generate `H_r(V, V ∖ 0; k)`, and let the image in
`H_{r+q}(M, M ∖ f(S); k ⊗ L)` of a class `z ∈ H_{r+q}(M; k ⊗ L)` be the image under the tube of
`o × x`, for `x ∈ H_q(S; L)`. Then at each point `s` of `S`, the image of `x` generates the local
homology `H_q(S, S ∖ s; L)` exactly when the image of `z` generates `H_{r+q}(M, M ∖ f s; k ⊗ L)`. -/
theorem span_singularHomologyToLocalHomology_eq_top_iff [T1Space M] (h : IsFramedTube f τ)
    {r : ℕ} (hr : finrank ℝ V = r)
    {o : (TopPair.ofSubset (X := TopCat.of V) {(0 : V)}ᶜ).singularHomology
      (C := ModuleCat.{w} k) (𝟙_ _) r} (ho : Submodule.span k {o} = ⊤) {q n : ℕ}
    (hn : r + q = n) {x : ((singularHomologyFunctor (ModuleCat.{w} k) q).obj L).obj (TopCat.of S)}
    {z : ((singularHomologyFunctor (ModuleCat.{w} k) n).obj (𝟙_ (ModuleCat.{w} k) ⊗ L)).obj
      (TopCat.of M)}
    (hz : (TopPair.ofSubset (X := TopCat.of M) (range f)ᶜ).singularHomologyπ
        (𝟙_ (ModuleCat.{w} k) ⊗ L) n z =
      TopPair.singularHomologyMap h.tubePairMap (𝟙_ (ModuleCat.{w} k) ⊗ L) n
        (TopCat.singularHomologyCrossRel (TopCat.of V) (TopCat.of S) {(0 : V)}ᶜ
          (𝟙_ (ModuleCat.{w} k)) L r q n hn (o ⊗ₜ x))) (s : S) :
    Submodule.span k {singularHomologyToLocalHomology L s q x} = ⊤ ↔
      Submodule.span k {singularHomologyToLocalHomology (𝟙_ (ModuleCat.{w} k) ⊗ L) (f s) n z} =
        ⊤ := by
  have : T1Space S := h.isEmbedding.t1Space
  -- The bijection at `s` carries the local class of `x` to the local class of `z`, and a linear
  -- bijection preserves and reflects generators.
  let e := LinearEquiv.ofBijective (_ ∘ₗ TensorProduct.mk k _ _ o)
    (bijective_localHomology L h s hr ho q n hn)
  have hex : e (singularHomologyToLocalHomology L s q x) =
      singularHomologyToLocalHomology (𝟙_ (ModuleCat.{w} k) ⊗ L) (f s) n z :=
    (singularHomologyToLocalHomology_eq_tubeLocalPairMap L h hn hz s).symm
  rw [← hex, e.span_singleton_apply_eq_top_iff]

/-- **The class of the core of a fundamental class is a fundamental class.** Let `τ : S × V → M`
be a framed tube around `f`, with `M` a `T₁` space and `V` of dimension `r`, let `o` generate
`H_r(V, V ∖ 0; k)`, and let the image in `H_{r+q}(M, M ∖ f(S); k ⊗ L)` of a fundamental class
`z ∈ H_{r+q}(M; k ⊗ L)` be the image under the tube of `o × x`, for `x ∈ H_q(S; L)`. Then `x` is a
fundamental class of `S`. -/
theorem isFundamentalClass_of_singularHomologyπ_eq [T1Space M] (h : IsFramedTube f τ) {r : ℕ}
    (hr : finrank ℝ V = r)
    {o : (TopPair.ofSubset (X := TopCat.of V) {(0 : V)}ᶜ).singularHomology
      (C := ModuleCat.{w} k) (𝟙_ _) r} (ho : Submodule.span k {o} = ⊤) {q n : ℕ}
    (hn : r + q = n) {x : ((singularHomologyFunctor (ModuleCat.{w} k) q).obj L).obj (TopCat.of S)}
    {z : ((singularHomologyFunctor (ModuleCat.{w} k) n).obj (𝟙_ (ModuleCat.{w} k) ⊗ L)).obj
      (TopCat.of M)}
    (hz : (TopPair.ofSubset (X := TopCat.of M) (range f)ᶜ).singularHomologyπ
        (𝟙_ (ModuleCat.{w} k) ⊗ L) n z =
      TopPair.singularHomologyMap h.tubePairMap (𝟙_ (ModuleCat.{w} k) ⊗ L) n
        (TopCat.singularHomologyCrossRel (TopCat.of V) (TopCat.of S) {(0 : V)}ᶜ
          (𝟙_ (ModuleCat.{w} k)) L r q n hn (o ⊗ₜ x)))
    (hμ : IsFundamentalClass z) : IsFundamentalClass x :=
  (isFundamentalClass_iff x).2 fun s ↦
    (h.span_singularHomologyToLocalHomology_eq_top_iff L hr ho hn hz s).2
      ((isFundamentalClass_iff z).1 hμ (f s))

/-! ### The orientation convention "core followed by fibre" -/

omit [NormedSpace ℝ V] [FiniteDimensional ℝ V] in
/-- **The local cross product, core first.** At a point `s` of the core, the map
`H_q(S, S ∖ s; L) ⊗ H_r(V, V ∖ 0; k) ⟶ H_n(M, M ∖ f s; k ⊗ L)`, `w ⊗ o ↦ τ_*(w × o)`: the relative
cross product of `(S, S ∖ s)` and `(V, V ∖ 0)`, core first, followed by the coefficient braiding
`L ⊗ k ≅ k ⊗ L` and the tube (`TauCeti.IsFramedTube.localPairMap`). A class of `S` is related to a
class of `M` in the orientation convention "core followed by fibre" when at every point the local
class of the latter is the image of the local class of the former times `o` under this map. -/
def localCross (h : IsFramedTube f τ) (s : S) (q r n : ℕ) (hn : q + r = n) :
    ((TopPair.ofSubset ({s}ᶜ : Set (TopCat.of S))).singularChainComplex L).homology q ⊗
        ((TopPair.ofSubset (X := TopCat.of V) {(0 : V)}ᶜ).singularChainComplex
          (𝟙_ (ModuleCat.{w} k))).homology r ⟶
      (TopPair.ofSubset ({f s}ᶜ : Set (TopCat.of M))).singularHomology
        (𝟙_ (ModuleCat.{w} k) ⊗ L) n :=
  HomologicalComplex.homologyCross
      ((TopPair.ofSubset ({s}ᶜ : Set (TopCat.of S))).singularChainComplex L)
      ((TopPair.ofSubset (X := TopCat.of V) {(0 : V)}ᶜ).singularChainComplex
        (𝟙_ (ModuleCat.{w} k))) q r n hn ≫
    HomologicalComplex.homologyMap (TopCat.shufflePair (TopCat.of S) (TopCat.of V) {s}ᶜ
      {(0 : V)}ᶜ L (𝟙_ (ModuleCat.{w} k))) n ≫
    HomologicalComplex.homologyMap
      (((SSetPair.chainComplexFunctor (ModuleCat.{w} k)).map
        (β_ L (𝟙_ (ModuleCat.{w} k))).hom).app (TopPair.toSSetPair.obj
          (TopPair.ofSubset (fst (TopCat.of S) (TopCat.of V) ⁻¹' ({s}ᶜ : Set (TopCat.of S)) ∪
            snd (TopCat.of S) (TopCat.of V) ⁻¹' {(0 : V)}ᶜ)))) n ≫
    TopPair.singularHomologyMap (h.localPairMap s) (𝟙_ (ModuleCat.{w} k) ⊗ L) n

omit [NormedSpace ℝ V] [FiniteDimensional ℝ V] in
/-- The local cross product, core first, is the relative cross product followed by the shuffle map
of `(S, S ∖ s) × (V, V ∖ 0)`, the coefficient braiding and the tube. -/
theorem localCross_def (h : IsFramedTube f τ) (s : S) (q r n : ℕ) (hn : q + r = n) :
    h.localCross L s q r n hn =
      HomologicalComplex.homologyCross
          ((TopPair.ofSubset ({s}ᶜ : Set (TopCat.of S))).singularChainComplex L)
          ((TopPair.ofSubset (X := TopCat.of V) {(0 : V)}ᶜ).singularChainComplex
            (𝟙_ (ModuleCat.{w} k))) q r n hn ≫
        HomologicalComplex.homologyMap (TopCat.shufflePair (TopCat.of S) (TopCat.of V) {s}ᶜ
          {(0 : V)}ᶜ L (𝟙_ (ModuleCat.{w} k))) n ≫
        HomologicalComplex.homologyMap
          (((SSetPair.chainComplexFunctor (ModuleCat.{w} k)).map
            (β_ L (𝟙_ (ModuleCat.{w} k))).hom).app (TopPair.toSSetPair.obj
              (TopPair.ofSubset (fst (TopCat.of S) (TopCat.of V) ⁻¹' ({s}ᶜ : Set (TopCat.of S)) ∪
                snd (TopCat.of S) (TopCat.of V) ⁻¹' {(0 : V)}ᶜ)))) n ≫
        TopPair.singularHomologyMap (h.localPairMap s) (𝟙_ (ModuleCat.{w} k) ⊗ L) n :=
  (rfl)

variable (k) in
/-- The sign `(-1)^a` acts on a `k`-module through `ℤ` as it does through `k`. -/
private lemma neg_one_pow_zsmul_eq_smul {N : Type*} [AddCommGroup N] [Module k N] (a : ℕ)
    (x : N) : ((-1 : ℤ) ^ a) • x = ((-1 : k) ^ a) • x := by
  simp [← Int.cast_smul_eq_zsmul k]

omit [NormedSpace ℝ V] [FiniteDimensional ℝ V] in
/-- **Exchanging the factors of the local cross product.** At a point `s` of the core, the cross
product `w × o` of a local class `w ∈ H_q(S, S ∖ s; L)` with `o ∈ H_r(V, V ∖ 0; k)`, core first and
carried by the tube with the coefficients `L ⊗ k ≅ k ⊗ L` exchanged, is `(-1)^(q * r)` times the
cross product `o × w`, fibre first. -/
private lemma localCross_tmul_eq_neg_one_pow_smul (h : IsFramedTube f τ) (s : S) {r q n : ℕ}
    (hn : r + q = n)
    (o : (TopPair.ofSubset (X := TopCat.of V) {(0 : V)}ᶜ).singularHomology
      (C := ModuleCat.{w} k) (𝟙_ _) r)
    (x : (TopPair.ofSubset ({s}ᶜ : Set (TopCat.of S))).singularHomology
      (C := ModuleCat.{w} k) L q) :
    (h.localCross L s q r n (by omega)).hom (x ⊗ₜ o) =
      ((-1 : ℤ) ^ (q * r)) •
        (HomologicalComplex.homologyCross
            ((TopPair.ofSubset (X := TopCat.of V) {(0 : V)}ᶜ).singularChainComplex
              (𝟙_ (ModuleCat.{w} k)))
            ((TopPair.ofSubset ({s}ᶜ : Set (TopCat.of S))).singularChainComplex L) r q n hn ≫
          HomologicalComplex.homologyMap (TopCat.shufflePair (TopCat.of V) (TopCat.of S)
            {(0 : V)}ᶜ {s}ᶜ (𝟙_ (ModuleCat.{w} k)) L) n ≫
          TopPair.singularHomologyMap (tubeLocalPairMap h s) (𝟙_ (ModuleCat.{w} k) ⊗ L) n).hom
          (o ⊗ₜ x) := by
  rw [localCross_def, localPairMap, TopPair.singularHomologyMap_comp,
    TopCat.homologyCross_comp_homologyMap_shufflePair_comp_braiding_assoc]
  simp

omit [NormedSpace ℝ V] [FiniteDimensional ℝ V] in
/-- **The class of the core in the order "core followed by fibre".** Let `τ : S × V → M` be a
framed tube around `f`, and let the image in `H_{r+q}(M, M ∖ f(S); k ⊗ L)` of a class
`z ∈ H_{r+q}(M; k ⊗ L)` be the image under the tube of `o × x`, for `o ∈ H_r(V, V ∖ 0; k)` and
`x ∈ H_q(S; L)`, the fibre first. Then at each point `s` of `S`, the image of `z` in the local
homology `H_{r+q}(M, M ∖ f s; k ⊗ L)` is `(-1)^(r * q)` times the image under the tube of `x × o`,
the core first, with the coefficients `L ⊗ k ≅ k ⊗ L` exchanged. -/
theorem singularHomologyToLocalHomology_eq_neg_one_pow_smul (h : IsFramedTube f τ)
    {r : ℕ} {o : (TopPair.ofSubset (X := TopCat.of V) {(0 : V)}ᶜ).singularHomology
      (C := ModuleCat.{w} k) (𝟙_ _) r} {q n : ℕ}
    (hn : r + q = n) {x : ((singularHomologyFunctor (ModuleCat.{w} k) q).obj L).obj (TopCat.of S)}
    {z : ((singularHomologyFunctor (ModuleCat.{w} k) n).obj (𝟙_ (ModuleCat.{w} k) ⊗ L)).obj
      (TopCat.of M)}
    (hz : (TopPair.ofSubset (X := TopCat.of M) (range f)ᶜ).singularHomologyπ
        (𝟙_ (ModuleCat.{w} k) ⊗ L) n z =
      TopPair.singularHomologyMap h.tubePairMap (𝟙_ (ModuleCat.{w} k) ⊗ L) n
        (TopCat.singularHomologyCrossRel (TopCat.of V) (TopCat.of S) {(0 : V)}ᶜ
          (𝟙_ (ModuleCat.{w} k)) L r q n hn (o ⊗ₜ x))) (s : S) :
    singularHomologyToLocalHomology (𝟙_ (ModuleCat.{w} k) ⊗ L) (f s) n z =
      ((-1 : ℤ) ^ (r * q)) •
        (h.localCross L s q r n (by omega)).hom
          (singularHomologyToLocalHomology L s q x ⊗ₜ o) := by
  rw [singularHomologyToLocalHomology_eq_tubeLocalPairMap L h hn hz s,
    localCross_tmul_eq_neg_one_pow_smul L h s hn, smul_smul, mul_comm q r, ← mul_pow]
  simp

/-! ### The Thom isomorphism of a framed submanifold -/

/-- **The Thom isomorphism of a framed submanifold.** Let `τ : S × V → M` be a framed tube around
`f` with closed core `f(S)`, as when `S` is compact and `M` is Hausdorff
(`TauCeti.IsFramedTube.isClosed_range`), with `V` of dimension `r`, and let `o` generate
`H_r(V, V ∖ 0; k)`. Then the relative cross product with `o`, followed by the tube,
`x ↦ τ_*(o × x)`, is a bijection `H_q(S; L) → H_{r+q}(M, M ∖ f(S); k ⊗ L)`.

`TauCeti.TopCat.singularHomologyComplRangeIso` identifies the same groups through the local
homology of a Serre fibration along the core; that isomorphism is not compared with this one. -/
theorem bijective_singularHomologyMap_tubePairMap_singularHomologyCrossRel
    (h : IsFramedTube f τ) (hf : IsClosed (range f)) {r : ℕ} (hr : finrank ℝ V = r)
    {o : (TopPair.ofSubset (X := TopCat.of V) {(0 : V)}ᶜ).singularHomology
      (C := ModuleCat.{w} k) (𝟙_ _) r} (ho : Submodule.span k {o} = ⊤) (q n : ℕ) (hn : r + q = n) :
    Function.Bijective fun x : ((singularHomologyFunctor (ModuleCat.{w} k) q).obj L).obj
        (TopCat.of S) ↦
      TopPair.singularHomologyMap h.tubePairMap (𝟙_ (ModuleCat.{w} k) ⊗ L) n
        (TopCat.singularHomologyCrossRel (TopCat.of V) (TopCat.of S) {(0 : V)}ᶜ
          (𝟙_ (ModuleCat.{w} k)) L r q n hn (o ⊗ₜ x)) :=
  ((ConcreteCategory.isIso_iff_bijective _).1
      (h.isIso_singularHomologyMap_tubePairMap hf (𝟙_ (ModuleCat.{w} k) ⊗ L) n)).comp
    (bijective_singularHomologyCrossRel_tmul_complSingleton (OpenPartialHomeomorph.refl V)
      (mem_univ (0 : V)) (TopCat.of S) L hr ho q n hn)

/-! ### The shriek map -/

section ShriekMap

variable (h : IsFramedTube f τ) (hf : IsClosed (range f)) {r : ℕ} (hr : finrank ℝ V = r)
  (o : (TopPair.ofSubset (X := TopCat.of V) {(0 : V)}ᶜ).singularHomology
    (C := ModuleCat.{w} k) (𝟙_ _) r) (ho : Submodule.span k {o} = ⊤)

/-- **The Thom isomorphism of a framed submanifold**, as a linear equivalence
`H_q(S; L) ≃ H_n(M, M ∖ f(S); k ⊗ L)`, `x ↦ τ_*(o × x)`, for `r + q = n`
(`TauCeti.IsFramedTube.bijective_singularHomologyMap_tubePairMap_singularHomologyCrossRel`). -/
def homologyThomEquiv (q n : ℕ) (hn : r + q = n) :
    ((singularHomologyFunctor (ModuleCat.{w} k) q).obj L).obj (TopCat.of S) ≃ₗ[k]
      (TopPair.ofSubset (X := TopCat.of M) (range f)ᶜ).singularHomology (C := ModuleCat.{w} k)
        (𝟙_ (ModuleCat.{w} k) ⊗ L) n :=
  LinearEquiv.ofBijective
    ((TopPair.singularHomologyMap h.tubePairMap (𝟙_ (ModuleCat.{w} k) ⊗ L) n).hom ∘ₗ
      (TopCat.singularHomologyCrossRel (TopCat.of V) (TopCat.of S) {(0 : V)}ᶜ
        (𝟙_ (ModuleCat.{w} k)) L r q n hn).hom ∘ₗ TensorProduct.mk k _ _ o)
    (h.bijective_singularHomologyMap_tubePairMap_singularHomologyCrossRel L hf hr ho q n hn)

/-- The Thom isomorphism sends `x` to the image under the tube of `o × x`. -/
@[simp]
theorem homologyThomEquiv_apply (q n : ℕ) (hn : r + q = n)
    (x : ((singularHomologyFunctor (ModuleCat.{w} k) q).obj L).obj (TopCat.of S)) :
    h.homologyThomEquiv L hf hr o ho q n hn x =
      TopPair.singularHomologyMap h.tubePairMap (𝟙_ (ModuleCat.{w} k) ⊗ L) n
        (TopCat.singularHomologyCrossRel (TopCat.of V) (TopCat.of S) {(0 : V)}ᶜ
          (𝟙_ (ModuleCat.{w} k)) L r q n hn (o ⊗ₜ x)) :=
  (rfl)

/-- **The shriek map of a framed submanifold** `i_! : H_n(M; k ⊗ L) → H_q(S; L)`, for
`r + q = n`: the map to the homology of `M` relative to the complement of the core, followed by
the inverse of the Thom isomorphism `x ↦ τ_*(o × x)` (`TauCeti.IsFramedTube.homologyThomEquiv`).
It sends `z` to the unique class `x` with `z ↦ τ_*(o × x)`
(`TauCeti.IsFramedTube.shriek_eq_iff`).

`TauCeti.TopCat.singularHomologyComplPreimageCoreIso` reads the same relative homology as the
homology of the core through the local homology of a Serre fibration; that isomorphism is not
compared with this one. -/
def shriek (q n : ℕ) (hn : r + q = n) :
    ((singularHomologyFunctor (ModuleCat.{w} k) n).obj (𝟙_ (ModuleCat.{w} k) ⊗ L)).obj
        (TopCat.of M) →ₗ[k]
      ((singularHomologyFunctor (ModuleCat.{w} k) q).obj L).obj (TopCat.of S) :=
  (h.homologyThomEquiv L hf hr o ho q n hn).symm.toLinearMap ∘ₗ
    ((TopPair.ofSubset (X := TopCat.of M) (range f)ᶜ).singularHomologyπ
      (𝟙_ (ModuleCat.{w} k) ⊗ L) n).hom

/-- The shriek map is the inverse of the Thom isomorphism applied to the image of `z` in
`H_n(M, M ∖ f(S); k ⊗ L)`. -/
theorem shriek_apply (q n : ℕ) (hn : r + q = n)
    (z : ((singularHomologyFunctor (ModuleCat.{w} k) n).obj (𝟙_ (ModuleCat.{w} k) ⊗ L)).obj
      (TopCat.of M)) :
    h.shriek L hf hr o ho q n hn z = (h.homologyThomEquiv L hf hr o ho q n hn).symm
      ((TopPair.ofSubset (X := TopCat.of M) (range f)ᶜ).singularHomologyπ
        (𝟙_ (ModuleCat.{w} k) ⊗ L) n z) :=
  (rfl)

/-- **Characteristic property of the shriek map**: the image of `z` in
`H_n(M, M ∖ f(S); k ⊗ L)` is the image under the tube of `o × i_!(z)`. -/
theorem singularHomologyπ_eq_shriek (q n : ℕ) (hn : r + q = n)
    (z : ((singularHomologyFunctor (ModuleCat.{w} k) n).obj (𝟙_ (ModuleCat.{w} k) ⊗ L)).obj
      (TopCat.of M)) :
    (TopPair.ofSubset (X := TopCat.of M) (range f)ᶜ).singularHomologyπ
        (𝟙_ (ModuleCat.{w} k) ⊗ L) n z =
      TopPair.singularHomologyMap h.tubePairMap (𝟙_ (ModuleCat.{w} k) ⊗ L) n
        (TopCat.singularHomologyCrossRel (TopCat.of V) (TopCat.of S) {(0 : V)}ᶜ
          (𝟙_ (ModuleCat.{w} k)) L r q n hn (o ⊗ₜ h.shriek L hf hr o ho q n hn z)) :=
  -- The right side is the Thom isomorphism applied to its inverse applied to the left side.
  ((h.homologyThomEquiv L hf hr o ho q n hn).apply_symm_apply _).symm

/-- The shriek map sends `z` to `x` exactly when the image of `z` in `H_n(M, M ∖ f(S); k ⊗ L)` is
the image under the tube of `o × x`. -/
theorem shriek_eq_iff (q n : ℕ) (hn : r + q = n)
    (z : ((singularHomologyFunctor (ModuleCat.{w} k) n).obj (𝟙_ (ModuleCat.{w} k) ⊗ L)).obj
      (TopCat.of M))
    (x : ((singularHomologyFunctor (ModuleCat.{w} k) q).obj L).obj (TopCat.of S)) :
    h.shriek L hf hr o ho q n hn z = x ↔
      (TopPair.ofSubset (X := TopCat.of M) (range f)ᶜ).singularHomologyπ
          (𝟙_ (ModuleCat.{w} k) ⊗ L) n z =
        TopPair.singularHomologyMap h.tubePairMap (𝟙_ (ModuleCat.{w} k) ⊗ L) n
          (TopCat.singularHomologyCrossRel (TopCat.of V) (TopCat.of S) {(0 : V)}ᶜ
            (𝟙_ (ModuleCat.{w} k)) L r q n hn (o ⊗ₜ x)) := by
  rw [h.singularHomologyπ_eq_shriek L hf hr o ho q n hn z]
  -- Both sides of the right equation are values of the Thom isomorphism, which is injective.
  exact (h.homologyThomEquiv L hf hr o ho q n hn).injective.eq_iff.symm

end ShriekMap

/-- **Capping a fundamental class with the class pulled back by a Pontryagin–Thom collapse.** Let
`τ : S × V → M` be a framed tube around `f`, with `S` compact, `M` Hausdorff and `V` of dimension
`p + 1`, let `c : M → V⁺` be its collapse, `o` a generator of `H_{p+1}(V, V ∖ 0; k)` and
`u ∈ Hᵖ⁺¹(V⁺, V⁺ ∖ 0; k)`. For every fundamental class `[M] ∈ H_{p+q+1}(M; k ⊗ L)` there is a
fundamental class `[S] ∈ H_q(S; L)` with `[M] ⌢ c^* u = ⟨u, o⟩ • f_*[S]`, where `⟨u, o⟩` is the
Kronecker pairing of the restriction of `u` to `(V, V ∖ 0)` with `o`. -/
theorem exists_isFundamentalClass_singularCap_pontryaginThomCollapse [CompactSpace S] [T2Space M]
    (h : IsFramedTube f τ) {p q : ℕ} (hr : finrank ℝ V = p + 1)
    {o : (TopPair.ofSubset (X := TopCat.of V) {(0 : V)}ᶜ).singularHomology
      (C := ModuleCat.{w} k) (𝟙_ _) (p + 1)} (ho : Submodule.span k {o} = ⊤)
    (u : (onePointThomPair V).singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k))
      (p + 1))
    {z : ((singularHomologyFunctor (ModuleCat.{w} k) (p + q + 1)).obj
      (𝟙_ (ModuleCat.{w} k) ⊗ L)).obj (TopCat.of M)} (hz : IsFundamentalClass z) :
    ∃ x : ((singularHomologyFunctor (ModuleCat.{w} k) q).obj L).obj (TopCat.of S),
      IsFundamentalClass x ∧
        (TopCat.of M).singularCap k (𝟙 (𝟙_ (ModuleCat.{w} k) ⊗ L)) (λ_ L).hom (p + 1) q
            (p + q + 1) (by omega)
            (TopCat.singularCohomologyMap
              (TopCat.ofHom (pontryaginThomCollapseMap h.isOpenEmbedding)) (p + 1)
              ((onePointThomPair V).singularCohomologyπ (𝟙_ (ModuleCat.{w} k)) k (𝟙_ _) (p + 1)
                u)) z =
          ((TopPair.ofSubset (X := TopCat.of V) {(0 : V)}ᶜ).singularKronecker k (p + 1)
              (TopPair.singularCohomologyMap (onePointThomPairIncl V) (p + 1) u) o : k) •
            ((singularHomologyFunctor (ModuleCat.{w} k) q).obj L).map
              (TopCat.ofHom ⟨f, h.continuous⟩) x := by
  have hx := h.singularHomologyπ_eq_shriek L h.isClosed_range hr o ho q (p + q + 1) (by omega) z
  generalize h.shriek L h.isClosed_range hr o ho q (p + q + 1) _ z = x at hx
  exact ⟨x, h.isFundamentalClass_of_singularHomologyπ_eq L hr ho _ hx hz,
    h.singularCap_pontryaginThomCollapse u o x z hx⟩

/-- **The Pontryagin–Thom cap formula in the orientation convention "core followed by fibre".** Let
`τ : S × V → M` be a framed tube around `f`, with `S` a compact manifold of dimension `q`, `M`
Hausdorff and `V` of dimension `p + 1`, let `c : M → V⁺` be its collapse, `o` a generator of
`H_{p+1}(V, V ∖ 0; k)` and `u ∈ Hᵖ⁺¹(V⁺, V⁺ ∖ 0; k)`. Let `y ∈ H_q(S; L)` be related to
`z ∈ H_{p+q+1}(M; k ⊗ L)` by the convention "core followed by fibre": at every point `s` of `S`, the
image of `z` in the local homology at `f s` is the image under the tube of `y × o`, with the
coefficients `L ⊗ k ≅ k ⊗ L` exchanged. Then `z ⌢ c^* u = (-1)^((p + 1) * q) ⟨u, o⟩ • f_* y`,
where `⟨u, o⟩` is the Kronecker pairing of the restriction of `u` to `(V, V ∖ 0)` with `o`. For a
fundamental class `z = [M]` and `⟨u, o⟩ = 1`, with the core of dimension `n = q` and the fibre of
dimension `k = p + 1`, this is `[M] ⌢ c^* u = (-1)^(n k) i_*[N]` for the core oriented as in
Barraud, Damian, Humilière and Oancea, Remark 9.2.4. -/
theorem singularCap_pontryaginThomCollapse_of_singularHomologyToLocalHomology_eq [CompactSpace S]
    [T2Space M] {E : Type w} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [ChartedSpace E S] (h : IsFramedTube f τ) {p q : ℕ} (hr : finrank ℝ V = p + 1)
    (hS : finrank ℝ E = q)
    {o : (TopPair.ofSubset (X := TopCat.of V) {(0 : V)}ᶜ).singularHomology
      (C := ModuleCat.{w} k) (𝟙_ _) (p + 1)} (ho : Submodule.span k {o} = ⊤)
    (u : (onePointThomPair V).singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k))
      (p + 1))
    {z : ((singularHomologyFunctor (ModuleCat.{w} k) (p + q + 1)).obj
      (𝟙_ (ModuleCat.{w} k) ⊗ L)).obj (TopCat.of M)}
    {y : ((singularHomologyFunctor (ModuleCat.{w} k) q).obj L).obj (TopCat.of S)}
    (hy : ∀ s : S, singularHomologyToLocalHomology (𝟙_ (ModuleCat.{w} k) ⊗ L) (f s) (p + q + 1) z =
      (h.localCross L s q (p + 1) (p + q + 1) (by omega)).hom
          (singularHomologyToLocalHomology L s q y ⊗ₜ o)) :
    (TopCat.of M).singularCap k (𝟙 (𝟙_ (ModuleCat.{w} k) ⊗ L)) (λ_ L).hom (p + 1) q
            (p + q + 1) (by omega)
            (TopCat.singularCohomologyMap
              (TopCat.ofHom (pontryaginThomCollapseMap h.isOpenEmbedding)) (p + 1)
              ((onePointThomPair V).singularCohomologyπ (𝟙_ (ModuleCat.{w} k)) k (𝟙_ _) (p + 1)
                u)) z =
      ((-1) ^ ((p + 1) * q) *
          ((TopPair.ofSubset (X := TopCat.of V) {(0 : V)}ᶜ).singularKronecker k (p + 1)
              (TopPair.singularCohomologyMap (onePointThomPairIncl V) (p + 1) u) o : k)) •
        ((singularHomologyFunctor (ModuleCat.{w} k) q).obj L).map
          (TopCat.ofHom ⟨f, h.continuous⟩) y := by
  have : T2Space S := h.isEmbedding.t2Space
  have hx := h.singularHomologyπ_eq_shriek L h.isClosed_range hr o ho q (p + q + 1) (by omega) z
  generalize h.shriek L h.isClosed_range hr o ho q (p + q + 1) _ z = x at hx
  -- The class `x` of the convention "fibre followed by core" is `(-1)^((p + 1) * q) • y`: both
  -- have the same image at every point, by the injectivity of the local Thom isomorphism.
  have hxy : x = ((-1 : k) ^ ((p + 1) * q)) • y := by
    refine singularHomology_ext_of_singularHomologyToLocalHomology L hS (D := univ)
      (fun s ↦ ⟨s, mem_univ s, Joined.refl s⟩) fun s _ ↦
        (bijective_localHomology L h s hr ho q (p + q + 1) (by omega)).1 ?_
    have hy' : singularHomologyToLocalHomology L s q (((-1 : k) ^ ((p + 1) * q)) • y) =
        ((-1 : k) ^ ((p + 1) * q)) • singularHomologyToLocalHomology L s q y := map_smul _ _ _
    refine (singularHomologyToLocalHomology_eq_tubeLocalPairMap L h _ hx s).symm.trans
      ((hy s).trans ((localCross_tmul_eq_neg_one_pow_smul L h s (by omega) o _).trans ?_))
    rw [LinearMap.comp_apply, TensorProduct.mk_apply, hy', TensorProduct.tmul_smul, map_smul,
      neg_one_pow_zsmul_eq_smul k, mul_comm]
  rw [h.singularCap_pontryaginThomCollapse u o x z hx, hxy, map_smul, smul_smul, mul_comm]

/-- **A fundamental class of the core in the convention "core followed by fibre".** Let
`τ : S × V → M` be a framed tube around `f`, with `S` compact, `M` Hausdorff and `V` of dimension
`p + 1`, let `c : M → V⁺` be its collapse, `o` a generator of `H_{p+1}(V, V ∖ 0; k)` and
`u ∈ Hᵖ⁺¹(V⁺, V⁺ ∖ 0; k)`. Every fundamental class `[M] ∈ H_{p+q+1}(M; k ⊗ L)` induces a fundamental
class `[S] ∈ H_q(S; L)` by the convention "core followed by fibre": at every point `s` of `S`, the
image of `[M]` in the local homology at `f s` is the image under the tube of `[S] × o`, with the
coefficients `L ⊗ k ≅ k ⊗ L` exchanged. With this class,
`[M] ⌢ c^* u = (-1)^((p + 1) * q) ⟨u, o⟩ • f_*[S]`. -/
theorem exists_isFundamentalClass_singularHomologyToLocalHomology_eq_and_singularCap
    [CompactSpace S] [T2Space M] (h : IsFramedTube f τ) {p q : ℕ} (hr : finrank ℝ V = p + 1)
    {o : (TopPair.ofSubset (X := TopCat.of V) {(0 : V)}ᶜ).singularHomology
      (C := ModuleCat.{w} k) (𝟙_ _) (p + 1)} (ho : Submodule.span k {o} = ⊤)
    (u : (onePointThomPair V).singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k))
      (p + 1))
    {z : ((singularHomologyFunctor (ModuleCat.{w} k) (p + q + 1)).obj
      (𝟙_ (ModuleCat.{w} k) ⊗ L)).obj (TopCat.of M)} (hz : IsFundamentalClass z) :
    ∃ y : ((singularHomologyFunctor (ModuleCat.{w} k) q).obj L).obj (TopCat.of S),
      IsFundamentalClass y ∧
      (∀ s : S, singularHomologyToLocalHomology (𝟙_ (ModuleCat.{w} k) ⊗ L) (f s) (p + q + 1) z =
        (h.localCross L s q (p + 1) (p + q + 1) (by omega)).hom
          (singularHomologyToLocalHomology L s q y ⊗ₜ o)) ∧
      (TopCat.of M).singularCap k (𝟙 (𝟙_ (ModuleCat.{w} k) ⊗ L)) (λ_ L).hom (p + 1) q
            (p + q + 1) (by omega)
            (TopCat.singularCohomologyMap
              (TopCat.ofHom (pontryaginThomCollapseMap h.isOpenEmbedding)) (p + 1)
              ((onePointThomPair V).singularCohomologyπ (𝟙_ (ModuleCat.{w} k)) k (𝟙_ _) (p + 1)
                u)) z =
        ((-1) ^ ((p + 1) * q) *
            ((TopPair.ofSubset (X := TopCat.of V) {(0 : V)}ᶜ).singularKronecker k (p + 1)
              (TopPair.singularCohomologyMap (onePointThomPairIncl V) (p + 1) u) o : k)) •
          ((singularHomologyFunctor (ModuleCat.{w} k) q).obj L).map
            (TopCat.ofHom ⟨f, h.continuous⟩) y := by
  have hx := h.singularHomologyπ_eq_shriek L h.isClosed_range hr o ho q (p + q + 1) (by omega) z
  generalize h.shriek L h.isClosed_range hr o ho q (p + q + 1) _ z = x at hx
  -- The class of the convention "core followed by fibre" is `(-1)^((p + 1) * q) • x`.
  have hsq : (-1 : k) ^ ((p + 1) * q) * (-1) ^ ((p + 1) * q) = 1 := by
    simp [← mul_pow]
  refine ⟨((-1 : k) ^ ((p + 1) * q)) • x,
    (isFundamentalClass_smul_iff_of_isUnit (isUnit_one.neg.pow _)).2
      (h.isFundamentalClass_of_singularHomologyπ_eq L hr ho _ hx hz), fun s ↦ ?_, ?_⟩
  · have hx' : singularHomologyToLocalHomology L s q (((-1 : k) ^ ((p + 1) * q)) • x) =
        ((-1 : k) ^ ((p + 1) * q)) • singularHomologyToLocalHomology L s q x := map_smul _ _ _
    rw [singularHomologyToLocalHomology_eq_neg_one_pow_smul L h _ hx s, hx',
      ← TensorProduct.smul_tmul', map_smul, neg_one_pow_zsmul_eq_smul k]
  · rw [h.singularCap_pontryaginThomCollapse u o x z hx, map_smul, smul_smul, mul_right_comm, hsq,
      one_mul]

end Tube

end IsFramedTube

end TauCeti
