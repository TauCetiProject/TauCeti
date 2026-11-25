/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.LocalHomology.IsFundamentalClass
public import TauCeti.Geometry.Manifold.PontryaginThom.Cap
import TauCeti.Algebra.Module.Equiv.SpanSingleton
import TauCeti.AlgebraicTopology.Singular.Kunneth.Pair
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
excision the right side is the homology of `(V × S, (V ∖ 0) × S)`, and the relative Künneth theorem
for the free local homology of `V` at `0`
(`TauCeti.bijective_homologyCross_tmul_singularChainComplex_complSingleton`) gives the suspension
by `o`. So every class `z ∈ H_{r+q}(M; k ⊗ L)` determines a unique class
`x ∈ H_q(S; L)` whose image under the tube is the image of `z` in `H_{r+q}(M, M ∖ f(S))`
(`TauCeti.IsFramedTube.existsUnique_singularHomologyπ_eq_singularHomologyMap_tubePairMap`).

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

## Main results

* `TauCeti.IsFramedTube.bijective_singularHomologyMap_tubePairMap_singularHomologyCrossRel`: the
  Thom isomorphism `x ↦ τ_*(o × x)` of a framed submanifold.
* `TauCeti.IsFramedTube.existsUnique_singularHomologyπ_eq_singularHomologyMap_tubePairMap`: the
  class of the core determined by a class of `M`.
* `TauCeti.IsFramedTube.span_singularHomologyToLocalHomology_eq_top_iff`: that class generates the
  local homology of `S` at `s` exactly when the class of `M` generates it at `f s`.
* `TauCeti.IsFramedTube.isFundamentalClass_of_singularHomologyπ_eq`: the class of the core
  determined by a fundamental class of `M` is a fundamental class of `S`.
* `TauCeti.IsFramedTube.exists_isFundamentalClass_singularCap_pontryaginThomCollapse`:
  `[M] ⌢ c^* u = ⟨u, o⟩ • f_*[S]` for a fundamental class `[S]` of `S`.

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

/-- The tube with its factors exchanged, `(v, x) ↦ τ (x, v)`, as a continuous map: the map of
ambient spaces of `TauCeti.IsFramedTube.tubePairMap`. -/
private def tubeMap (h : IsFramedTube f τ) : C((TopCat.of V ⊗ TopCat.of S : TopCat), M) :=
  ⟨fun p ↦ τ (snd (TopCat.of V) (TopCat.of S) p, fst (TopCat.of V) (TopCat.of S) p),
    h.isOpenEmbedding.continuous.comp
      ((snd (TopCat.of V) (TopCat.of S)).hom.continuous.prodMk
        (fst (TopCat.of V) (TopCat.of S)).hom.continuous)⟩

private lemma isOpenEmbedding_tubeMap (h : IsFramedTube f τ) : IsOpenEmbedding (tubeMap h) :=
  h.isOpenEmbedding.comp (Homeomorph.prodComm V S).isOpenEmbedding

/-- The core is the image of the zero section, and only of it. -/
private lemma preimage_tubeMap_range (h : IsFramedTube f τ) :
    tubeMap h ⁻¹' range f = fst (TopCat.of V) (TopCat.of S) ⁻¹' {0} := by
  ext p
  refine ⟨fun ⟨y, hy⟩ ↦ ?_, fun hp ↦ ⟨snd (TopCat.of V) (TopCat.of S) p, ?_⟩⟩
  · rw [← h.apply_zero] at hy
    exact (congrArg Prod.snd (h.isOpenEmbedding.injective hy)).symm
  · rw [← h.apply_zero]
    exact congrArg (fun v ↦ τ (snd (TopCat.of V) (TopCat.of S) p, v)) hp.symm

private lemma range_subset_range_tubeMap (h : IsFramedTube f τ) : range f ⊆ range (tubeMap h) := by
  rintro _ ⟨x, rfl⟩
  exact ⟨((0 : V), x), h.apply_zero x⟩

/-- The tube as a map of pairs is the map of pairs induced by `TauCeti.IsFramedTube.tubeMap`. -/
private lemma mapsTo_tubeMap (h : IsFramedTube f τ) :
    MapsTo (TopCat.ofHom (tubeMap h)) (fst (TopCat.of V) (TopCat.of S) ⁻¹' {(0 : V)}ᶜ)
      ((range f)ᶜ : Set (TopCat.of M)) := by
  intro p hp hpf
  exact hp ((preimage_tubeMap_range h).subset hpf)

private lemma tubePairMap_eq (h : IsFramedTube f τ) :
    h.tubePairMap = TopPair.ofSubsetMap (TopCat.ofHom (tubeMap h)) (mapsTo_tubeMap h) :=
  TopPair.hom_ext_of_fst _ (ConcreteCategory.hom_ext _ _ fun p ↦ by
    rw [TopPair.ofSubsetMap_fst]
    -- Both sides are `τ (x, v)` at `p = (v, x)`.
    exact h.tubePairMap_fst_apply p)

/-- **Excision along the tube**: when the core is closed, `(V × S, (V ∖ 0) × S) → (M, M ∖ f(S))`
induces isomorphisms on relative homology. -/
private lemma isIso_singularHomologyMap_tubePairMap (h : IsFramedTube f τ)
    (hf : IsClosed (range f)) {A : Type*} [Category* A] [HasCoproducts.{w} A] [Abelian A] (N : A)
    (n : ℕ) : IsIso (TopPair.singularHomologyMap h.tubePairMap N n) := by
  have := isIso_localHomologyMap N (tubeMap h) (isOpenEmbedding_tubeMap h)
    (preimage_tubeMap_range h) hf (range_subset_range_tubeMap h) n
  rw [localHomologyMap_def] at this
  rwa [tubePairMap_eq]

/-- The tube as a map from the pair `(V × S, V × S ∖ {(0, s)})`, written as in the cross product of
the pairs `(V, V ∖ 0)` and `(S, S ∖ s)`, to the local pair `(M, M ∖ {f s})`. -/
private def tubeLocalPairMap (h : IsFramedTube f τ) (s : S) :
    TopPair.ofSubset (fst (TopCat.of V) (TopCat.of S) ⁻¹' {(0 : V)}ᶜ ∪
      snd (TopCat.of V) (TopCat.of S) ⁻¹' ({s}ᶜ : Set (TopCat.of S))) ⟶
      TopPair.ofSubset ({f s}ᶜ : Set (TopCat.of M)) :=
  TopPair.ofSubsetMap (TopCat.ofHom (tubeMap h)) (by
    rintro p hp (hps : tubeMap h p = f s)
    rw [← h.apply_zero] at hps
    have := h.isOpenEmbedding.injective hps
    rcases hp with hp | hp
    · exact hp (congrArg Prod.snd this)
    · exact hp (congrArg Prod.fst this))

/-- **Excision at a point of the core**: the tube induces isomorphisms from the local homology of
`V × S` at `(0, s)` to that of `M` at `f s`. -/
private lemma isIso_singularHomologyMap_tubeLocalPairMap [T1Space M] (h : IsFramedTube f τ)
    (s : S) {A : Type*} [Category* A] [HasCoproducts.{w} A] [Abelian A] (N : A) (n : ℕ) :
    IsIso (TopPair.singularHomologyMap (tubeLocalPairMap h s) N n) := by
  have hpre : tubeMap h ⁻¹' {f s} = {((0 : V), s)} := by
    rw [← h.apply_zero s]
    -- `τ (s, 0)` is `tubeMap h (0, s)`.
    exact (congrArg _ (image_singleton (f := tubeMap h) (a := ((0 : V), s)))).symm.trans
      ((isOpenEmbedding_tubeMap h).injective.preimage_image _)
  have hU : fst (TopCat.of V) (TopCat.of S) ⁻¹' {(0 : V)}ᶜ ∪
      snd (TopCat.of V) (TopCat.of S) ⁻¹' ({s}ᶜ : Set (TopCat.of S)) = ({((0 : V), s)})ᶜ := by
    ext ⟨v, x⟩
    -- The projections of the product in `TopCat` are those of `V × S`.
    change (v ≠ 0 ∨ x ≠ s) ↔ ¬((v, x) = ((0 : V), s))
    rw [Prod.ext_iff, not_and_or]
  -- Transport the excision isomorphism along the equality of subsets.
  have key : ∀ U : Set (TopCat.of V ⊗ TopCat.of S : TopCat), U = {((0 : V), s)}ᶜ →
      ∀ hm : MapsTo (TopCat.ofHom (tubeMap h)) U ({f s}ᶜ : Set (TopCat.of M)),
      IsIso (TopPair.singularHomologyMap (TopPair.ofSubsetMap _ hm) N n) := by
    rintro U rfl _
    have := isIso_localHomologyMap N (tubeMap h) (isOpenEmbedding_tubeMap h) hpre
      isClosed_singleton (singleton_subset_iff.2 ⟨((0 : V), s), h.apply_zero s⟩) n
    rwa [localHomologyMap_def] at this
  exact key _ hU _

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
  -- Both sides are images of `o × x`: restrict to `(V × S, V × S ∖ {(0, s)})` and apply the tube,
  -- or apply the tube and restrict to `(M, M ∖ {f s})`.
  have hmap : h.tubePairMap ≫ TopPair.ofSubsetMap (𝟙 (TopCat.of M))
      (compl_subset_compl.2 (singleton_subset_iff.2 (mem_range_self s))) =
      TopPair.ofSubsetMap (𝟙 _) (fun _ hz ↦ Or.inl hz) ≫ tubeLocalPairMap h s := by
    rw [tubePairMap_eq]
    exact TopPair.ofSubsetMap_comp_ofSubsetMap_eq _ _ _ _
      ((Category.comp_id _).trans (Category.id_comp _).symm)
  have hcross := TopCat.singularHomologyCrossRel_comp_singularHomologyMap (TopCat.of V)
    (TopCat.of S) {(0 : V)}ᶜ ({s}ᶜ : Set (TopCat.of S)) (𝟙_ (ModuleCat.{w} k)) L r q n hn
  have hex : e (singularHomologyToLocalHomology L s q x) =
      singularHomologyToLocalHomology (𝟙_ (ModuleCat.{w} k) ⊗ L) (f s) n z := by
    rw [singularHomologyToLocalHomology_eq_singularHomologyπ L s x,
      singularHomologyToLocalHomology_eq_localHomologyRestriction _ (mem_range_self s) z, hz,
      localHomologyRestriction_def, ← ConcreteCategory.comp_apply,
      ← TopPair.singularHomologyMap_comp, hmap, TopPair.singularHomologyMap_comp,
      ← ConcreteCategory.comp_apply (TopCat.singularHomologyCrossRel _ _ _ _ _ _ _ _ _),
      reassoc_of% hcross]
    -- Both sides apply `tube ∘ shuffle ∘ cross` to `o ⊗ x|_s`, where `(𝟙 ⊗ π) (o ⊗ x) = o ⊗ π x`.
    -- `simp` cannot evaluate the right side: there `x` lies in `H_q(S; L)` as a value of
    -- `singularHomologyFunctor`, which is the source of `singularHomologyπ` only up to unfolding.
    rfl
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
          (𝟙_ (ModuleCat.{w} k)) L r q n hn (o ⊗ₜ x)) := by
  have hs := (quasiIsoAt_iff_isIso_homologyMap
    (TopCat.shuffleRel (TopCat.of V) (TopCat.of S) {(0 : V)}ᶜ (𝟙_ (ModuleCat.{w} k)) L) n).1
      inferInstance
  have := ((ConcreteCategory.isIso_iff_bijective _).1
      (isIso_singularHomologyMap_tubePairMap h hf (𝟙_ (ModuleCat.{w} k) ⊗ L) n)).comp
    (((ConcreteCategory.isIso_iff_bijective _).1 hs).comp
      (bijective_homologyCross_tmul_singularChainComplex_complSingleton
        (OpenPartialHomeomorph.refl V) (mem_univ (0 : V))
        ((TopCat.toSSet.obj (TopCat.of S)).chainComplex L) hr ho q n hn))
  -- The relative cross product is the cross product of chain complexes followed by the relative
  -- shuffle map.
  simp only [TopCat.singularHomologyCrossRel_def]
  exact this

/-- **The class of the core determined by a class of the ambient space.** Let `τ : S × V → M` be a
framed tube around `f` with closed core `f(S)`, with `V` of dimension `r`, and let `o` generate
`H_r(V, V ∖ 0; k)`. Every class `z ∈ H_{r+q}(M; k ⊗ L)` maps in `H_{r+q}(M, M ∖ f(S); k ⊗ L)` to the
image under the tube of `o × x` for exactly one `x ∈ H_q(S; L)`. -/
theorem existsUnique_singularHomologyπ_eq_singularHomologyMap_tubePairMap (h : IsFramedTube f τ)
    (hf : IsClosed (range f)) {r : ℕ} (hr : finrank ℝ V = r)
    {o : (TopPair.ofSubset (X := TopCat.of V) {(0 : V)}ᶜ).singularHomology
      (C := ModuleCat.{w} k) (𝟙_ _) r} (ho : Submodule.span k {o} = ⊤) {q n : ℕ}
    (hn : r + q = n)
    (z : ((singularHomologyFunctor (ModuleCat.{w} k) n).obj (𝟙_ (ModuleCat.{w} k) ⊗ L)).obj
      (TopCat.of M)) :
    ∃! x : ((singularHomologyFunctor (ModuleCat.{w} k) q).obj L).obj (TopCat.of S),
      (TopPair.ofSubset (X := TopCat.of M) (range f)ᶜ).singularHomologyπ
          (𝟙_ (ModuleCat.{w} k) ⊗ L) n z =
        TopPair.singularHomologyMap h.tubePairMap (𝟙_ (ModuleCat.{w} k) ⊗ L) n
          (TopCat.singularHomologyCrossRel (TopCat.of V) (TopCat.of S) {(0 : V)}ᶜ
            (𝟙_ (ModuleCat.{w} k)) L r q n hn (o ⊗ₜ x)) :=
  have hb := h.bijective_singularHomologyMap_tubePairMap_singularHomologyCrossRel L hf hr ho q n hn
  let ⟨x, hx⟩ := hb.2 (((TopPair.ofSubset (X := TopCat.of M) (range f)ᶜ).singularHomologyπ
    (𝟙_ (ModuleCat.{w} k) ⊗ L) n) z)
  ⟨x, hx.symm, fun _ hy ↦ hb.1 (hy.symm.trans hx.symm)⟩

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
  obtain ⟨x, hx, -⟩ := h.existsUnique_singularHomologyπ_eq_singularHomologyMap_tubePairMap L
    h.isClosed_range hr ho (by omega : p + 1 + q = p + q + 1) z
  exact ⟨x, h.isFundamentalClass_of_singularHomologyπ_eq L hr ho _ hx hz,
    h.singularCap_pontryaginThomCollapse u o x z hx⟩

end Tube

end IsFramedTube

end TauCeti
