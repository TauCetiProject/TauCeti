/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Fibration.FiberInclusion
public import TauCeti.AlgebraicTopology.Singular.Fibration.LocalHomology
public import TauCeti.Geometry.Manifold.PontryaginThom.NormalCoordinate

/-!
# Local homology of a Serre fibration along the preimage of a framed submanifold

Let `p : E → B` be a Serre fibration and `Z ⊆ B` a closed subset with a **normal coordinate**: an
open neighbourhood `W` of `Z` and a Serre fibration `ν : W → K` onto a convex neighbourhood `K` of
`0` in a real normed space `V` of finite dimension `r`, whose zero set is `Z`. The main examples are
a framed submanifold, with `ν` the normal coordinate of a framed tube, and a point of a manifold,
with `ν` a chart. The local homology of `E` along `p⁻¹(Z)` is the shifted homology of `p⁻¹(Z)`:

* `Hₘ(E, E ∖ p⁻¹(Z); M) = 0` for `m < r`
  (`TauCeti.TopCat.isZero_singularHomology_complPreimage`);
* `Hₙ₊ᵣ(E, E ∖ p⁻¹(Z); M) ≅ Hₙ(p⁻¹(Z); M)`
  (`TauCeti.TopCat.singularHomologyComplPreimageIso`).

The composite `Hₙ₊ᵣ(E) → Hₙ₊ᵣ(E, E ∖ p⁻¹(Z)) ≅ Hₙ(p⁻¹(Z))` is the shriek map `j_!` of the
inclusion `j : Z → B` with coefficients in the fibration. For a point it is the shriek map of
`TauCeti.TopCat.singularHomologyComplFiberIso`, with which the construction agrees
(`TauCeti.TopCat.singularHomologyComplPreimageIso_chartBall`).

The isomorphism is natural for a map `g : E' → E` of fibrations over a map of the bases that
pulls the normal coordinate of `Z` back to a normal coordinate of `Z' ⊆ B'`
(`TauCeti.TopCat.singularHomologyComplPreimageIso_hom_naturality`).

## Framed submanifolds and transverse maps

A framed tube `τ : S × V → B` around `f : S → B` (`TauCeti.IsFramedTube`) gives the core
`Z = f(S)` the normal coordinate `τ(x, v) ↦ v` on the part `τ(S × D)` of the tube over a ball `D`
about `0` (`TauCeti.IsFramedTube.tubeBall`, `TauCeti.IsFramedTube.normalCoordinate`), so
`Hₙ₊ᵣ(E, E ∖ p⁻¹(f(S))) ≅ Hₙ(p⁻¹(f(S)))` (`TauCeti.TopCat.singularHomologyComplPreimageCoreIso`).

Let `s : B' → B` meet the core in a single point `b'`, `s⁻¹(f(S)) = {b'}`, and suppose that near
`b'` the normal coordinate of `s` is a chart `e` of `B'`: `s` maps the source of `e` into the
tube, with `s x = τ(y, e x - e b')` for some `y`. For a smooth map `s` transverse to the core this
is the inverse function theorem in the normal coordinate. Then for a map `g : E' → E` of Serre
fibrations over `s`, the shriek maps commute:

`j_{f(S)!} ∘ g_* = (g|)_* ∘ j_{b'!}`,

where `j_{b'!} : Hₙ₊ᵣ(E') → Hₙ(p'⁻¹(b'))` is the shriek map of the point `b'` for the chart `e` and
`g| : p'⁻¹(b') → p⁻¹(f(S))` is the restriction of `g`
(`TauCeti.TopCat.singularHomologyComplPreimageCoreIso_naturality`). This is the commutative square
in the proof of Lemma 7.7 of Barraud, Damian, Humilière and Oancea, which they deduce from the
fibration theorem and the relation `j_{Y!} s_* = j^{(Y)}_* j_!` for the transverse square of `s`
and the inclusion of `Y = f(S)`. In particular, when `g|` is injective on `Hₙ` a class of infinite
order of the fibre `p'⁻¹(b')` stays of infinite order along the core
(`TauCeti.TopCat.not_isOfFinAddOrder_singularHomologyComplPreimageCoreIso`). The injectivity holds
in degrees `n < N` when the core is `N`-connected at `s b'` and `g` is injective on the homology of
the fibres, since the fibre `p⁻¹(s b')` then carries the homology of `p⁻¹(f(S))` in low degrees
(`not_isOfFinAddOrder_singularHomologyComplPreimageCoreIso_of_subsingleton_homotopyGroup`).
In Barraud–Damian–Humilière–Oancea, `p` is the evaluation fibration `Map(S², Q) → Q` and `s` is an
embedded sphere meeting a highly connected framed submanifold of `Q` once.

## Main definitions and results

* `TauCeti.TopCat.singularHomologyComplPreimageIso`: `Hₙ₊ᵣ(E, E ∖ p⁻¹(Z)) ≅ Hₙ(p⁻¹(Z))` for a
  normal coordinate of `Z`, and `TauCeti.TopCat.singularHomologyComplPreimageIso_hom_naturality`.
* `TauCeti.TopCat.singularHomologyComplPreimageIso_chartBall`: for a point and a chart, it is
  `TauCeti.TopCat.singularHomologyComplFiberIso`.
* `TauCeti.TopCat.singularHomologyComplPreimageCoreIso`: the local homology along the core of a
  framed tube.
* `TauCeti.TopCat.singularHomologyComplPreimageCoreIso_naturality`,
  `TauCeti.TopCat.singularHomologyComplPreimageCoreIso_singularHomologyπ_homologyMap`: the shriek
  map of the core and the shriek map of a transverse point commute.
* `TauCeti.TopCat.not_isOfFinAddOrder_singularHomologyComplPreimageCoreIso`,
  `not_isOfFinAddOrder_singularHomologyComplPreimageCoreIso_of_subsingleton_homotopyGroup`:
  classes of infinite order along the core.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §7, Lemma 7.7.
* J.-P. Serre, *Homologie singulière des espaces fibrés. Applications*, Ann. of Math. 54 (1951),
  Chapter II.
-/

public section

noncomputable section

open CategoryTheory Limits Module Metric Set Topology

universe u

namespace TauCeti

namespace TopCat

/-! ### The local homology along the zero set of a normal coordinate -/

section NormalCoordinate

variable {V : Type u} [NormedAddCommGroup V] {K : Set V} {E B : _root_.TopCat.{u}}
  {W Z : Set B}

/-- The restriction `p⁻¹(W) → W` of `p` followed by a normal coordinate `ν : W → K`. -/
def normalCoordinateProj (p : E ⟶ B) (ν : _root_.TopCat.of W ⟶ _root_.TopCat.of K) :
    _root_.TopCat.of (p ⁻¹' W) ⟶ _root_.TopCat.of K :=
  _root_.TopCat.ofHom (p.hom.restrictPreimage W) ≫ ν

@[simp]
lemma normalCoordinateProj_apply (p : E ⟶ B) (ν : _root_.TopCat.of W ⟶ _root_.TopCat.of K)
    (z : _root_.TopCat.of (p ⁻¹' W)) :
    normalCoordinateProj p ν z = ν ⟨p z, z.2⟩ :=
  (rfl)

lemma mem_serreFibrations_normalCoordinateProj {p : E ⟶ B} (hp : serreFibrations p)
    {ν : _root_.TopCat.of W ⟶ _root_.TopCat.of K} (hν : serreFibrations ν) :
    serreFibrations (normalCoordinateProj p ν) :=
  serreFibrations.comp_mem _ _ (mem_serreFibrations_restrictPreimage hp W) hν

variable {p : E ⟶ B} {ν : _root_.TopCat.of W ⟶ _root_.TopCat.of K}
  (hZ : ∀ w : W, (ν w : V) = 0 ↔ (w : B) ∈ Z)

include hZ in
lemma normalCoordinateProj_eq_zero_iff (z : _root_.TopCat.of (p ⁻¹' W)) :
    (normalCoordinateProj p ν z : V) = 0 ↔ p z ∈ Z :=
  hZ ⟨p z, z.2⟩

/-- Over `W`, the complement of `p⁻¹(Z)` is the part of `p⁻¹(W)` over the punctured base of
`TauCeti.TopCat.normalCoordinateProj`. -/
def normalCoordinateComplPairIso :
    TopPair.interPair (X := E) (p ⁻¹' W) (p ⁻¹' Z)ᶜ ≅
      TopPair.ofSubset (normalCoordinateProj p ν ⁻¹' {x | (x : V) ≠ 0}) :=
  TopPair.ofSubsetIso (Homeomorph.refl _) fun z ↦
    (normalCoordinateProj_eq_zero_iff hZ z).not.symm

lemma normalCoordinateComplPairIso_hom :
    (normalCoordinateComplPairIso hZ).hom =
      TopPair.ofSubsetMap (_root_.TopCat.ofHom (Homeomorph.refl (p ⁻¹' W)))
        fun z hz ↦ (normalCoordinateProj_eq_zero_iff (p := p) hZ z).not.2 hz :=
  TopPair.ofSubsetIso_hom _ _

/-- The fibre over `0` of `TauCeti.TopCat.normalCoordinateProj` is `p⁻¹(Z)`. -/
def normalCoordinateProjFiberHomeomorph (hZW : Z ⊆ W) :
    (normalCoordinateProj p ν ⁻¹' {x | (x : V) = 0}) ≃ₜ (p ⁻¹' Z) where
  toFun z := ⟨z.1.1, (normalCoordinateProj_eq_zero_iff hZ z.1).1 z.2⟩
  invFun y := ⟨⟨y.1, hZW y.2⟩, (normalCoordinateProj_eq_zero_iff hZ _).2 y.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

lemma coe_normalCoordinateProjFiberHomeomorph_apply (hZW : Z ⊆ W)
    (z : normalCoordinateProj p ν ⁻¹' {x | (x : V) = 0}) :
    (normalCoordinateProjFiberHomeomorph hZ hZW z : E) = z.1.1 :=
  (rfl)

variable {R : Type*} [Ring R] (M : ModuleCat.{u} R) (hW : IsOpen W) (hZc : IsClosed Z)
  (hZW : Z ⊆ W)

include hW hZc hZW in
private lemma isIso_singularHomologyMap_excisionMap_preimage (m : ℕ) :
    IsIso (TopPair.singularHomologyMap
      (TopPair.excisionMap (X := E) (p ⁻¹' W) (p ⁻¹' Z)ᶜ) M m) :=
  TopPair.isIso_singularHomologyMap_excisionMap_of_isClosed_subset M
    (hW.preimage p.hom.continuous) (hZc.preimage p.hom.continuous) (preimage_mono hZW) m

/-- Excision onto `p⁻¹(W)`, followed by `TauCeti.TopCat.normalCoordinateComplPairIso`. -/
private def preimageExcisionIso (m : ℕ) :
    (TopPair.ofSubset (p ⁻¹' Z)ᶜ).singularHomology M m ≅
      (TopPair.ofSubset (normalCoordinateProj p ν ⁻¹' {x | (x : V) ≠ 0})).singularHomology M m :=
  haveI := isIso_singularHomologyMap_excisionMap_preimage (p := p) M hW hZc hZW m
  (asIso (TopPair.singularHomologyMap
      (TopPair.excisionMap (X := E) (p ⁻¹' W) (p ⁻¹' Z)ᶜ) M m)).symm ≪≫
    TopPair.singularHomologyMapIso _ (normalCoordinateComplPairIso hZ) m

@[reassoc]
private lemma singularHomologyMap_excisionMap_comp_preimageExcisionIso_hom (m : ℕ) :
    TopPair.singularHomologyMap (TopPair.excisionMap (X := E) (p ⁻¹' W) (p ⁻¹' Z)ᶜ) M m ≫
        (preimageExcisionIso hZ M hW hZc hZW m).hom =
      TopPair.singularHomologyMap (normalCoordinateComplPairIso hZ).hom M m := by
  simp [preimageExcisionIso]

variable [NormedSpace ℝ V] [FiniteDimensional ℝ V]

include hZ hW hZc hZW in
/-- **The local homology of a Serre fibration along the zero set of a normal coordinate vanishes
below the dimension.** Let `p : E ⟶ B` be a Serre fibration, `Z ⊆ B` closed and `ν : W → K` a
Serre fibration on an open neighbourhood `W` of `Z`, onto a convex neighbourhood `K` of `0` in a
real normed space of finite dimension `r`, with zero set `Z`. Then
`Hₘ(E, E ∖ p⁻¹(Z); M) = 0` for every `m < r`. -/
theorem isZero_singularHomology_complPreimage (hp : serreFibrations p) (hν : serreFibrations ν)
    (hK : Convex ℝ K) (hK₀ : K ∈ 𝓝 (0 : V)) {m : ℕ} (hm : m < finrank ℝ V) :
    IsZero ((TopPair.ofSubset (p ⁻¹' Z)ᶜ).singularHomology M m) :=
  (isZero_singularHomology_preimage_ne_zero M (mem_serreFibrations_normalCoordinateProj hp hν) hK
    hK₀ hm).of_iso (preimageExcisionIso hZ M hW hZc hZW m)

/-- **The local homology of a Serre fibration along the zero set of a normal coordinate.** Let
`p : E ⟶ B` be a Serre fibration, `Z ⊆ B` closed and `ν : W → K` a Serre fibration on an open
neighbourhood `W` of `Z`, onto a convex neighbourhood `K` of `0` in a real normed space of finite
dimension `r`, with zero set `Z`. Then `Hₘ(E, E ∖ p⁻¹(Z); M) ≅ Hₙ(p⁻¹(Z); M)` for `m = n + r`.

It is excision onto `p⁻¹(W)`, followed by `TauCeti.TopCat.singularHomologyPreimageNeZeroIso` for
the Serre fibration `p⁻¹(W) → W → K` and the identification of its fibre over `0` with
`p⁻¹(Z)`. Composed with the map `Hₘ(E) → Hₘ(E, E ∖ p⁻¹(Z))`, it is the shriek map of the inclusion
of `Z` with coefficients in the fibration. -/
def singularHomologyComplPreimageIso (hp : serreFibrations p) (hν : serreFibrations ν)
    (hK : Convex ℝ K) (hK₀ : K ∈ 𝓝 (0 : V)) (n m : ℕ) (h : n + finrank ℝ V = m) :
    (TopPair.ofSubset (p ⁻¹' Z)ᶜ).singularHomology M m ≅
      ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) n).obj
        M).obj (_root_.TopCat.of (p ⁻¹' Z)) :=
  preimageExcisionIso hZ M hW hZc hZW m ≪≫
    singularHomologyPreimageNeZeroIso M (mem_serreFibrations_normalCoordinateProj hp hν) hK hK₀
      n m h ≪≫
    ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) n).obj M).mapIso
      (_root_.TopCat.isoOfHomeo (normalCoordinateProjFiberHomeomorph hZ hZW))

/-- After excision onto `p⁻¹(W)`, `TauCeti.TopCat.singularHomologyComplPreimageIso` is
`TauCeti.TopCat.singularHomologyPreimageNeZeroIso` for the Serre fibration `p⁻¹(W) → K`, followed
by the identification of its fibre over `0` with `p⁻¹(Z)`. -/
@[reassoc]
lemma singularHomologyMap_excisionMap_comp_singularHomologyComplPreimageIso_hom
    (hp : serreFibrations p) (hν : serreFibrations ν) (hK : Convex ℝ K) (hK₀ : K ∈ 𝓝 (0 : V))
    (n m : ℕ) (h : n + finrank ℝ V = m) :
    TopPair.singularHomologyMap (TopPair.excisionMap (X := E) (p ⁻¹' W) (p ⁻¹' Z)ᶜ) M m ≫
        (singularHomologyComplPreimageIso hZ M hW hZc hZW hp hν hK hK₀ n m h).hom =
      TopPair.singularHomologyMap (normalCoordinateComplPairIso hZ).hom M m ≫
        (singularHomologyPreimageNeZeroIso M (mem_serreFibrations_normalCoordinateProj hp hν) hK
          hK₀ n m h).hom ≫
        ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) n).obj M).map
          (_root_.TopCat.isoOfHomeo (normalCoordinateProjFiberHomeomorph hZ hZW)).hom := by
  simp [singularHomologyComplPreimageIso,
    singularHomologyMap_excisionMap_comp_preimageExcisionIso_hom_assoc]

end NormalCoordinate

/-! ### Naturality -/

section Naturality

variable {V : Type u} [NormedAddCommGroup V] {K : Set V} {E B E' B' : _root_.TopCat.{u}}
  {W Z : Set B} {W' Z' : Set B'} {p : E ⟶ B} {p' : E' ⟶ B'}
  {ν : _root_.TopCat.of W ⟶ _root_.TopCat.of K} {ν' : _root_.TopCat.of W' ⟶ _root_.TopCat.of K}
  (hZ : ∀ w : W, (ν w : V) = 0 ↔ (w : B) ∈ Z) (hZ' : ∀ w : W', (ν' w : V) = 0 ↔ (w : B') ∈ Z')
  (hZW' : Z' ⊆ W') {g : E' ⟶ E} (hgW : MapsTo g (p' ⁻¹' W') (p ⁻¹' W))
  (hgν : ∀ (x : E') (hx : p' x ∈ W'), ν ⟨p (g x), hgW hx⟩ = ν' ⟨p' x, hx⟩)

include hZ hZ' hZW' hgν in
/-- A map `g` pulling the normal coordinate `ν` of `Z` back to the normal coordinate `ν'` of `Z'`
maps `p'⁻¹(Z')` into `p⁻¹(Z)`. -/
lemma mapsTo_preimage_of_normalCoordinate : MapsTo g (p' ⁻¹' Z') (p ⁻¹' Z) := fun x hx ↦ by
  have h := (hZ' ⟨p' x, hZW' hx⟩).2 hx
  rw [← hgν x (hZW' hx)] at h
  exact (hZ _).1 h

/-- The restriction `p'⁻¹(W') → p⁻¹(W)` of `g`. -/
private def restrictW : _root_.TopCat.of (p' ⁻¹' W') ⟶ _root_.TopCat.of (p ⁻¹' W) :=
  _root_.TopCat.ofHom ⟨hgW.restrict, g.hom.continuous.restrict hgW⟩

include hgν in
private lemma restrictW_comp_normalCoordinateProj :
    restrictW hgW ≫ normalCoordinateProj p ν = normalCoordinateProj p' ν' := by
  ext x
  exact congrArg Subtype.val (hgν x.1 x.2)

variable (hgZ : MapsTo g (p' ⁻¹' Z')ᶜ (p ⁻¹' Z)ᶜ)

include hgν in
private lemma interPairMap_comp_normalCoordinateComplPairIso_hom :
    TopPair.interPairMap g hgW hgZ ≫ (normalCoordinateComplPairIso hZ).hom =
      (normalCoordinateComplPairIso hZ').hom ≫
        TopPair.ofSubsetMap (restrictW hgW) ((restrictW hgW).mapsTo_preimage_of_comp_eq
          (restrictW_comp_normalCoordinateProj hgW hgν) _) := by
  refine TopPair.hom_ext_of_fst _ ?_
  ext x
  apply Subtype.ext
  rw [normalCoordinateComplPairIso_hom, normalCoordinateComplPairIso_hom, TopPair.Hom.fst_comp,
    TopPair.Hom.fst_comp]
  -- The ambient spaces of the pairs are `TopCat.of` of subtypes, which `rw` does not unfold.
  erw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, TopPair.ofSubsetMap_fst_apply,
    TopPair.ofSubsetMap_fst_apply, TopPair.ofSubsetMap_fst_apply]
  exact TopPair.interPairMap_fst_apply g hgW hgZ x

variable {R : Type*} [Ring R] (M : ModuleCat.{u} R) (hW : IsOpen W) (hZc : IsClosed Z)
  (hZW : Z ⊆ W) (hW' : IsOpen W') (hZc' : IsClosed Z')
  [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- **Naturality of the local homology along the zero set of a normal coordinate.** Let
`p : E ⟶ B` and `p' : E' ⟶ B'` be Serre fibrations with normal coordinates `ν : W → K` of
`Z ⊆ B` and `ν' : W' → K` of `Z' ⊆ B'`, onto the same convex neighbourhood `K` of `0`. Let
`g : E' ⟶ E` map `p'⁻¹(W')` into `p⁻¹(W)`, with `ν (p (g x)) = ν' (p' x)` there, and map the
complement of `p'⁻¹(Z')` into the complement of `p⁻¹(Z)`. Under the isomorphisms
`Hₙ₊ᵣ(E, E ∖ p⁻¹(Z)) ≅ Hₙ(p⁻¹(Z))` of `TauCeti.TopCat.singularHomologyComplPreimageIso`, the map
induced by `g` on relative homology is the map induced by its restriction `p'⁻¹(Z') → p⁻¹(Z)`. -/
@[reassoc]
theorem singularHomologyComplPreimageIso_hom_naturality (hp : serreFibrations p)
    (hp' : serreFibrations p') (hν : serreFibrations ν) (hν' : serreFibrations ν')
    (hK : Convex ℝ K) (hK₀ : K ∈ 𝓝 (0 : V)) (n m : ℕ) (h : n + finrank ℝ V = m) :
    TopPair.singularHomologyMap (TopPair.ofSubsetMap g hgZ) M m ≫
        (singularHomologyComplPreimageIso hZ M hW hZc hZW hp hν hK hK₀ n m h).hom =
      (singularHomologyComplPreimageIso hZ' M hW' hZc' hZW' hp' hν' hK hK₀ n m h).hom ≫
        ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) n).obj M).map
          (_root_.TopCat.ofHom ⟨(mapsTo_preimage_of_normalCoordinate hZ hZ' hZW' hgW hgν).restrict,
            g.hom.continuous.restrict _⟩) := by
  have := isIso_singularHomologyMap_excisionMap_preimage (p := p') M hW' hZc' hZW' m
  rw [← cancel_epi (TopPair.singularHomologyMap
      (TopPair.excisionMap (X := E') (p' ⁻¹' W') (p' ⁻¹' Z')ᶜ) M m),
    singularHomologyMap_excisionMap_comp_singularHomologyComplPreimageIso_hom_assoc,
    ← TopPair.singularHomologyMap_comp_assoc,
    ← TopPair.interPairMap_comp_excisionMap g hgW hgZ, TopPair.singularHomologyMap_comp_assoc,
    singularHomologyMap_excisionMap_comp_singularHomologyComplPreimageIso_hom,
    ← TopPair.singularHomologyMap_comp_assoc,
    interPairMap_comp_normalCoordinateComplPairIso_hom hZ hZ' hgW hgν hgZ,
    TopPair.singularHomologyMap_comp_assoc,
    singularHomologyPreimageNeZeroIso_hom_naturality_assoc M
      (mem_serreFibrations_normalCoordinateProj hp' hν')
      (mem_serreFibrations_normalCoordinateProj hp hν) hK hK₀
      (restrictW_comp_normalCoordinateProj hgW hgν)
      (_root_.TopCat.ofHom ⟨MapsTo.restrict (restrictW hgW) _ _
        ((restrictW hgW).mapsTo_preimage_of_comp_eq
          (restrictW_comp_normalCoordinateProj hgW hgν) _),
        (restrictW hgW).hom.continuous.restrict _⟩) (fun _ ↦ rfl) n m h,
    ← Functor.map_comp, ← Functor.map_comp]
  rfl

end Naturality

/-! ### The local homology along the core of a framed tube -/

section Core

variable {V : Type u} [NormedAddCommGroup V] {E B : _root_.TopCat.{u}} {p : E ⟶ B}
  {S : Type*} [TopologicalSpace S] {f : S → B} {τ : S × V → B} (hτ : IsFramedTube f τ)

/-- The normal coordinate of a framed tube is a Serre fibration. -/
lemma mem_serreFibrations_normalCoordinate (ε : ℝ) :
    serreFibrations (_root_.TopCat.ofHom (hτ.normalCoordinate ε) :
      _root_.TopCat.of (IsFramedTube.tubeBall τ ε) ⟶ _root_.TopCat.of (ball (0 : V) ε)) :=
  mem_serreFibrations_of_hasHomotopyLiftingProperty fun A _ ↦
    hτ.hasHomotopyLiftingProperty_normalCoordinate ε A

variable {R : Type*} [Ring R] (M : ModuleCat.{u} R) (hfc : IsClosed (range f)) {ε : ℝ}
  (hε₀ : 0 < ε) [NormedSpace ℝ V] [FiniteDimensional ℝ V]

include hτ hfc hε₀ in
/-- **The local homology of a Serre fibration along the core of a framed tube vanishes below the
codimension.** Let `τ : S × V → B` be a framed tube around `f : S → B` with closed core `f(S)`,
where `V` is a real normed space of finite dimension `r`, and let `p : E ⟶ B` be a Serre fibration.
Then `Hₘ(E, E ∖ p⁻¹(f(S)); M) = 0` for every `m < r`. -/
theorem isZero_singularHomology_complPreimage_range (hp : serreFibrations p) {m : ℕ}
    (hm : m < finrank ℝ V) :
    IsZero ((TopPair.ofSubset (p ⁻¹' range f)ᶜ).singularHomology M m) :=
  isZero_singularHomology_complPreimage (ν := _root_.TopCat.ofHom (hτ.normalCoordinate ε))
    hτ.normalCoordinate_eq_zero_iff M (hτ.isOpen_tubeBall ε) hfc (hτ.range_subset_tubeBall hε₀)
    hp (mem_serreFibrations_normalCoordinate hτ ε) (convex_ball 0 ε) (ball_mem_nhds 0 hε₀) hm

/-- **The local homology of a Serre fibration along the core of a framed tube.** Let
`τ : S × V → B` be a framed tube around `f : S → B` with closed core `f(S)`, where `V` is a real
normed space of finite dimension `r`, and let `p : E ⟶ B` be a Serre fibration. Then
`Hₘ(E, E ∖ p⁻¹(f(S)); M) ≅ Hₙ(p⁻¹(f(S)); M)` for `m = n + r`.

This is `TauCeti.TopCat.singularHomologyComplPreimageIso` for the normal coordinate
`τ(x, v) ↦ v` on the part of the tube over the ball of radius `ε` about `0`
(`TauCeti.IsFramedTube.normalCoordinate`). Composed with the map
`Hₘ(E) → Hₘ(E, E ∖ p⁻¹(f(S)))`, it is the shriek map `Hₘ(E) → Hₙ(p⁻¹(f(S)))` of the inclusion of
the framed submanifold `f(S)`, with coefficients in the fibration. -/
def singularHomologyComplPreimageCoreIso (hp : serreFibrations p) (n m : ℕ)
    (h : n + finrank ℝ V = m) :
    (TopPair.ofSubset (p ⁻¹' range f)ᶜ).singularHomology M m ≅
      ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) n).obj
        M).obj (_root_.TopCat.of (p ⁻¹' range f)) :=
  singularHomologyComplPreimageIso (ν := _root_.TopCat.ofHom (hτ.normalCoordinate ε))
    hτ.normalCoordinate_eq_zero_iff M (hτ.isOpen_tubeBall ε) hfc (hτ.range_subset_tubeBall hε₀)
    hp (mem_serreFibrations_normalCoordinate hτ ε) (convex_ball 0 ε) (ball_mem_nhds 0 hε₀) n m h

end Core

/-! ### Points of a manifold -/

section Chart

variable {V : Type u} [NormedAddCommGroup V] {E B : _root_.TopCat.{u}} {p : E ⟶ B}
  (e : OpenPartialHomeomorph B V) {b : B} (hb : b ∈ e.source) {ε : ℝ}
  (hε : ball (e b) ε ⊆ e.target)

include hb in
/-- The chart coordinate `x ↦ e x - e b` on `OpenPartialHomeomorph.chartBall e b ε` is a normal
coordinate of the point `b`. -/
lemma chartBallHomeomorph_eq_zero_iff (w : e.chartBall b ε) :
    ((_root_.TopCat.isoOfHomeo (X := _root_.TopCat.of (e.chartBall b ε))
      (Y := _root_.TopCat.of (ball (0 : V) ε)) (e.chartBallHomeomorph hε)).hom w : V) = 0 ↔
      (w : B) ∈ ({b} : Set B) := by
  have hw : ((_root_.TopCat.isoOfHomeo (X := _root_.TopCat.of (e.chartBall b ε))
      (Y := _root_.TopCat.of (ball (0 : V) ε)) (e.chartBallHomeomorph hε)).hom w : V) =
      e w - e b :=
    e.coe_chartBallHomeomorph_apply hε w
  rw [hw, mem_singleton_iff, ← e.injOn.eq_iff (e.chartBall_subset_source b ε w.2) hb]
  exact sub_eq_zero

variable [T1Space B] {R : Type*} [Ring R] (M : ModuleCat.{u} R) [NormedSpace ℝ V]
  [FiniteDimensional ℝ V]

/-- **The local homology along a fibre is the local homology along the zero set of a chart.** For
the normal coordinate `x ↦ e x - e b` of the point `b` given by a chart `e`,
`TauCeti.TopCat.singularHomologyComplPreimageIso` is the isomorphism
`Hₙ₊ᵣ(E, E ∖ p⁻¹(b)) ≅ Hₙ(p⁻¹(b))` of `TauCeti.TopCat.singularHomologyComplFiberIso`. -/
theorem singularHomologyComplPreimageIso_chartBall (hε₀ : 0 < ε) (hp : serreFibrations p)
    (n m : ℕ) (h : n + finrank ℝ V = m) :
    singularHomologyComplPreimageIso (chartBallHomeomorph_eq_zero_iff e hb hε) M
        (e.isOpen_chartBall b ε) isClosed_singleton
        (singleton_subset_iff.2 (e.mem_chartBall_self hb hε₀)) hp
        (serreFibrations.of_isIso _) (convex_ball 0 ε) (ball_mem_nhds 0 hε₀) n m h =
      singularHomologyComplFiberIso M e hb hε hε₀ hp n m h := by
  have hq : 𝟙 _ ≫ normalCoordinateProj p (_root_.TopCat.isoOfHomeo
      (X := _root_.TopCat.of (e.chartBall b ε)) (Y := _root_.TopCat.of (ball (0 : V) ε))
      (e.chartBallHomeomorph hε)).hom =
      e.chartBallProj hε p := by
    rw [Category.id_comp, OpenPartialHomeomorph.chartBallProj_def]
    rfl
  ext : 1
  have := isIso_singularHomologyMap_excisionMap_preimage (p := p) M (e.isOpen_chartBall b ε)
    isClosed_singleton (singleton_subset_iff.2 (e.mem_chartBall_self hb hε₀)) m
  rw [← cancel_epi (TopPair.singularHomologyMap
      (TopPair.excisionMap (X := E) (p ⁻¹' e.chartBall b ε) (p ⁻¹' {b})ᶜ) M m),
    singularHomologyMap_excisionMap_comp_singularHomologyComplPreimageIso_hom,
    singularHomologyMap_excisionMap_comp_singularHomologyComplFiberIso_hom]
  have hpair : (normalCoordinateComplPairIso (chartBallHomeomorph_eq_zero_iff e hb hε)).hom =
      (e.chartBallComplFiberPairIso hb hε p).hom ≫
        TopPair.ofSubsetMap (𝟙 _) (_root_.TopCat.Hom.mapsTo_preimage_of_comp_eq (𝟙 _) hq _) := by
    refine TopPair.hom_ext_of_fst _ ?_
    ext x
    rw [normalCoordinateComplPairIso_hom, OpenPartialHomeomorph.chartBallComplFiberPairIso_hom,
      TopPair.Hom.fst_comp]
    -- The ambient spaces of the pairs are `TopCat.of` of subtypes, which `rw` does not unfold.
    erw [ConcreteCategory.comp_apply, TopPair.ofSubsetMap_fst_apply, TopPair.ofSubsetMap_fst_apply,
      TopPair.ofSubsetMap_fst_apply]
  rw [hpair, TopPair.singularHomologyMap_comp_assoc,
    singularHomologyPreimageNeZeroIso_hom_naturality_assoc M
      (e.mem_serreFibrations_chartBallProj hε hp)
      (mem_serreFibrations_normalCoordinateProj hp (serreFibrations.of_isIso _)) (convex_ball 0 _)
      (ball_mem_nhds 0 hε₀) hq
      (_root_.TopCat.ofHom ⟨MapsTo.restrict (𝟙 (_root_.TopCat.of (p ⁻¹' e.chartBall b ε))) _ _
        (_root_.TopCat.Hom.mapsTo_preimage_of_comp_eq (𝟙 _) hq _),
        continuous_id.restrict _⟩) (fun _ ↦ rfl) n m h,
    ← Functor.map_comp]
  congr 3
  ext z
  -- The homeomorphisms are applied through `TopCat.isoOfHomeo`, which `rw` does not see through.
  erw [ConcreteCategory.comp_apply, coe_normalCoordinateProjFiberHomeomorph_apply,
    OpenPartialHomeomorph.coe_chartBallProjFiberHomeomorph_apply]
  rfl

end Chart

/-! ### Maps meeting the core of a framed tube once -/

section Transverse

variable {V : Type u} [NormedAddCommGroup V] {E B E' B' : _root_.TopCat.{u}} {p : E ⟶ B}
  {p' : E' ⟶ B'} {S : Type*} [TopologicalSpace S] {f : S → B} {τ : S × V → B}
  (hτ : IsFramedTube f τ) {s : B' ⟶ B} {g : E' ⟶ E} (hg : g ≫ p = p' ≫ s)
  (e : OpenPartialHomeomorph B' V) {b' : B'} (hb : b' ∈ e.source) {ε : ℝ}
  (hε : ball (e b') ε ⊆ e.target)
  (hs : ∀ x ∈ e.source, ∃ y, τ (y, e x - e b') = s x) (hsf : ∀ x, s x ∈ range f → x = b')

include hg in
private lemma apply_comp_eq (x : E') : p (g x) = s (p' x) :=
  ConcreteCategory.congr_hom hg x

omit [TopologicalSpace S] in
include hg hs in
private lemma mapsTo_chartBall_tubeBall :
    MapsTo g (p' ⁻¹' e.chartBall b' ε) (p ⁻¹' IsFramedTube.tubeBall τ ε) := fun x hx ↦ by
  obtain ⟨hxs, hxb⟩ := (e.mem_chartBall).1 hx
  obtain ⟨y, hy⟩ := hs _ hxs
  rw [mem_preimage, apply_comp_eq hg, ← hy]
  exact IsFramedTube.apply_mem_tubeBall y (by simpa [mem_ball, dist_eq_norm] using hxb)

include hg hs in
private lemma normalCoordinate_apply_comp (x : E') (hx : p' x ∈ e.chartBall b' ε) :
    _root_.TopCat.ofHom (hτ.normalCoordinate ε) ⟨p (g x), mapsTo_chartBall_tubeBall hg e hs hx⟩ =
      (_root_.TopCat.isoOfHomeo (X := _root_.TopCat.of (e.chartBall b' ε))
        (Y := _root_.TopCat.of (ball (0 : V) ε)) (e.chartBallHomeomorph hε)).hom ⟨p' x, hx⟩ := by
  obtain ⟨y, hy⟩ := hs _ ((e.mem_chartBall).1 hx).1
  apply Subtype.ext
  exact (hτ.normalCoordinate_eq_of_eq (x := y) ((apply_comp_eq hg x).trans hy.symm)).trans
    (e.coe_chartBallHomeomorph_apply hε ⟨p' x, hx⟩).symm

omit [TopologicalSpace S] in
include hg hsf in
/-- A map over `s`, where `s` meets the core of the tube only at `b'`, maps the complement of the
fibre over `b'` into the complement of the preimage of the core. -/
lemma mapsTo_compl_preimage_range :
    MapsTo g (p' ⁻¹' {b'})ᶜ (p ⁻¹' range f)ᶜ := fun x hx hxf ↦
  hx (hsf _ (by rw [← apply_comp_eq hg]; exact hxf))

include hτ hb hs in
/-- If near `b'` the normal coordinate of `s` is a chart at `b'`, then `s b'` lies on the core. -/
lemma apply_mem_range : s b' ∈ range f := by
  obtain ⟨y, hy⟩ := hs b' hb
  exact ⟨y, by rw [← hτ.apply_zero, ← hy, sub_self]⟩

omit [TopologicalSpace S] in
include hg in
/-- A map over `s` maps the fibre over `b'` into the fibre over `s b'`. -/
lemma mapsTo_preimage_singleton_preimage_singleton :
    MapsTo g (p' ⁻¹' {b'}) (p ⁻¹' {s b'}) := fun x hx ↦ by
  rw [mem_preimage, apply_comp_eq hg, mem_singleton_iff.1 hx]
  exact mem_singleton _

omit [TopologicalSpace S] in
include hg in
/-- A map over `s` maps the fibre over `b'` into the preimage of the core when `s b'` lies on the
core. -/
lemma mapsTo_preimage_singleton_preimage_range (hb' : s b' ∈ range f) :
    MapsTo g (p' ⁻¹' {b'}) (p ⁻¹' range f) := fun x hx ↦ by
  rw [mem_preimage, apply_comp_eq hg, mem_singleton_iff.1 hx]
  exact hb'

variable [T1Space B'] {R : Type*} [Ring R] (M : ModuleCat.{u} R) (hfc : IsClosed (range f))
  [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- **The shriek maps of a framed submanifold and of a transverse point commute**
(Barraud–Damian–Humilière–Oancea, proof of Lemma 7.7). Let `τ : S × V → B` be a framed tube around
`f : S → B` with closed core, let `s : B' → B` meet the core only at `b'`, and let `e` be a chart
of `B'` at `b'` such that every point `x` of its source is mapped to `τ (y, e x - e b')` for some
`y`: near `b'`, the normal coordinate of `s` is the chart. Let `g : E' ⟶ E` be a map of Serre
fibrations over `s`. Then the shriek map `Hₙ₊ᵣ(E, E ∖ p⁻¹(f(S))) ≅ Hₙ(p⁻¹(f(S)))` of the core
(`TauCeti.TopCat.singularHomologyComplPreimageCoreIso`) composed with the map induced by `g` is the
shriek map `Hₙ₊ᵣ(E', E' ∖ p'⁻¹(b')) ≅ Hₙ(p'⁻¹(b'))` of the point
(`TauCeti.TopCat.singularHomologyComplFiberIso`) composed with the map induced by the restriction
`p'⁻¹(b') → p⁻¹(f(S))` of `g`. -/
@[reassoc]
theorem singularHomologyComplPreimageCoreIso_naturality (hε₀ : 0 < ε) (hp : serreFibrations p)
    (hp' : serreFibrations p') (n m : ℕ) (h : n + finrank ℝ V = m) :
    TopPair.singularHomologyMap (TopPair.ofSubsetMap g (mapsTo_compl_preimage_range hg hsf)) M m ≫
        (singularHomologyComplPreimageCoreIso hτ M hfc hε₀ hp n m h).hom =
      (singularHomologyComplFiberIso M e hb hε hε₀ hp' n m h).hom ≫
        ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) n).obj M).map
          (_root_.TopCat.ofHom ⟨(mapsTo_preimage_singleton_preimage_range hg
            (apply_mem_range hτ e hb hs)).restrict, g.hom.continuous.restrict _⟩) := by
  rw [← singularHomologyComplPreimageIso_chartBall e hb hε M hε₀ hp']
  exact singularHomologyComplPreimageIso_hom_naturality hτ.normalCoordinate_eq_zero_iff
    (chartBallHomeomorph_eq_zero_iff e hb hε)
    (singleton_subset_iff.2 (e.mem_chartBall_self hb hε₀)) (mapsTo_chartBall_tubeBall hg e hs)
    (normalCoordinate_apply_comp hτ hg e hε hs) (mapsTo_compl_preimage_range hg hsf) M
    (hτ.isOpen_tubeBall ε) hfc (hτ.range_subset_tubeBall hε₀) (e.isOpen_chartBall b' ε)
    isClosed_singleton hp hp' (mem_serreFibrations_normalCoordinate hτ ε)
    (serreFibrations.of_isIso _) (convex_ball 0 ε) (ball_mem_nhds 0 hε₀) n m h

include hsf in
/-- **The shriek maps of a framed submanifold and of a transverse point commute, on classes**
(Barraud–Damian–Humilière–Oancea, proof of Lemma 7.7). In the setting of
`TauCeti.TopCat.singularHomologyComplPreimageCoreIso_naturality`, for `α ∈ Hₙ₊ᵣ(E')` the shriek
map of the core sends `g_* α` to the image under the restriction `p'⁻¹(b') → p⁻¹(f(S))` of `g`
of the shriek map `j_! α ∈ Hₙ(p'⁻¹(b'))` of the point: `j_{f(S)!} (g_* α) = (g|)_* (j_! α)`. -/
theorem singularHomologyComplPreimageCoreIso_singularHomologyπ_homologyMap (hε₀ : 0 < ε)
    (hp : serreFibrations p) (hp' : serreFibrations p') (n m : ℕ) (h : n + finrank ℝ V = m)
    (α : ((_root_.TopCat.toSSet.obj E').homology M m : ModuleCat.{u} R)) :
    (singularHomologyComplPreimageCoreIso hτ M hfc hε₀ hp n m h).hom.hom
        (((TopPair.ofSubset (p ⁻¹' range f)ᶜ).singularHomologyπ M m).hom
          ((SSet.homologyMap (_root_.TopCat.toSSet.map g) M m).hom α)) =
      (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) n).obj M).map
          (_root_.TopCat.ofHom ⟨(mapsTo_preimage_singleton_preimage_range hg
            (apply_mem_range hτ e hb hs)).restrict, g.hom.continuous.restrict _⟩)).hom
        ((singularHomologyComplFiberIso M e hb hε hε₀ hp' n m h).hom.hom
          ((fiberLocalization M p' b' m).hom α)) := by
  have hπ := TopPair.singularHomologyπ_naturality
    (TopPair.ofSubsetMap g (mapsTo_compl_preimage_range hg hsf)) M m
  rw [TopPair.ofSubsetMap_fst] at hπ
  have hsq := singularHomologyComplPreimageCoreIso_naturality hτ hg e hb hε hs hsf M hfc hε₀ hp hp'
    n m h
  have h₁ := congrArg (fun φ ↦ φ.hom α) hπ
  have h₂ := congrArg (fun φ ↦ φ.hom ((fiberLocalization M p' b' m).hom α)) hsq
  dsimp only at h₁ h₂
  -- `TopPair.singularHomologyπ_naturality` composes in the category of the coefficients, whose
  -- instances `rw` does not match against `ModuleCat.hom_comp`.
  erw [ModuleCat.hom_comp, ModuleCat.hom_comp, LinearMap.comp_apply, LinearMap.comp_apply] at h₁
  erw [ModuleCat.hom_comp, ModuleCat.hom_comp, LinearMap.comp_apply, LinearMap.comp_apply] at h₂
  -- The ambient spaces in `h₁` are `TopCat.of` of the carriers, which `rw` does not unfold.
  erw [h₁]
  exact h₂

include hsf in
/-- **Classes of infinite order along the core of a framed tube** (Barraud–Damian–Humilière–Oancea,
Lemma 7.7). In the setting of `TauCeti.TopCat.singularHomologyComplPreimageCoreIso_naturality`,
suppose the restriction `p'⁻¹(b') → p⁻¹(f(S))` of `g` is injective on `Hₙ`, as it is for the
fibration of maps `S² → Q` over a highly connected core. If the shriek map
`j_! α ∈ Hₙ(p'⁻¹(b'))` of the point has infinite order, then so does the shriek map of the core of
`g_* α`. -/
theorem not_isOfFinAddOrder_singularHomologyComplPreimageCoreIso (hε₀ : 0 < ε)
    (hp : serreFibrations p) (hp' : serreFibrations p') (n m : ℕ) (h : n + finrank ℝ V = m)
    (hinj : Function.Injective
      (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) n).obj M).map
        (_root_.TopCat.ofHom ⟨(mapsTo_preimage_singleton_preimage_range hg
          (apply_mem_range hτ e hb hs)).restrict, g.hom.continuous.restrict _⟩)).hom)
    {α : ((_root_.TopCat.toSSet.obj E').homology M m : ModuleCat.{u} R)}
    (hα : ¬ IsOfFinAddOrder ((singularHomologyComplFiberIso M e hb hε hε₀ hp' n m h).hom.hom
      ((fiberLocalization M p' b' m).hom α))) :
    ¬ IsOfFinAddOrder ((singularHomologyComplPreimageCoreIso hτ M hfc hε₀ hp n m h).hom.hom
      (((TopPair.ofSubset (p ⁻¹' range f)ᶜ).singularHomologyπ M m).hom
        ((SSet.homologyMap (_root_.TopCat.toSSet.map g) M m).hom α))) := by
  rw [singularHomologyComplPreimageCoreIso_singularHomologyπ_homologyMap hτ hg e hb hε hs hsf M
    hfc hε₀ hp hp' n m h]
  exact (Function.Injective.isOfFinAddOrder_iff (f := LinearMap.toAddMonoidHom _) hinj).not.2 hα

include hsf in
/-- **Classes of infinite order along a highly connected core** (Barraud–Damian–Humilière–Oancea,
Lemma 7.7). In the setting of `TauCeti.TopCat.singularHomologyComplPreimageCoreIso_naturality`,
with coefficients in a ring `R`, suppose that the core `f(S)` has trivial homotopy groups `π_k` at
`s b'` for every `k ≤ N`, and that `g` restricted to the fibres `p'⁻¹(b') → p⁻¹(s b')` is injective
on `Hₙ` for some `n < N`, for instance because `g` is the projection of the pullback of `p` along
`s`. If the shriek map `j_! α ∈ Hₙ(p'⁻¹(b'))` of the point has infinite order, then so does the
shriek map of the core of `g_* α`: the inclusion `p⁻¹(s b') → p⁻¹(f(S))` is injective on `Hₙ`
(`TauCeti.TopCat.isIso_singularHomologyMap_preimageInclusion`). -/
theorem not_isOfFinAddOrder_singularHomologyComplPreimageCoreIso_of_subsingleton_homotopyGroup
    {R : Type u} [Ring R] (hε₀ : 0 < ε) (hp : serreFibrations p) (hp' : serreFibrations p')
    {n m N : ℕ} (h : n + finrank ℝ V = m) (hn : n < N)
    (hY : ∀ k ≤ N, Subsingleton (π_ k (range f) ⟨s b', apply_mem_range hτ e hb hs⟩))
    (hinj : Function.Injective
      (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) n).obj
        (ModuleCat.of R R)).map (_root_.TopCat.ofHom
          ⟨(mapsTo_preimage_singleton_preimage_singleton (b' := b') hg).restrict,
            g.hom.continuous.restrict _⟩)).hom)
    {α : ((_root_.TopCat.toSSet.obj E').homology (ModuleCat.of R R) m : ModuleCat.{u} R)}
    (hα : ¬ IsOfFinAddOrder
      ((singularHomologyComplFiberIso (ModuleCat.of R R) e hb hε hε₀ hp' n m h).hom.hom
        ((fiberLocalization (ModuleCat.of R R) p' b' m).hom α))) :
    ¬ IsOfFinAddOrder
      ((singularHomologyComplPreimageCoreIso hτ (ModuleCat.of R R) hfc hε₀ hp n m h).hom.hom
        (((TopPair.ofSubset (p ⁻¹' range f)ᶜ).singularHomologyπ (ModuleCat.of R R) m).hom
          ((SSet.homologyMap (_root_.TopCat.toSSet.map g) (ModuleCat.of R R) m).hom α))) := by
  refine not_isOfFinAddOrder_singularHomologyComplPreimageCoreIso hτ hg e hb hε hs hsf
    (ModuleCat.of R R) hfc hε₀ hp hp' n m h ?_ hα
  have := isIso_singularHomologyMap_preimageInclusion R
    (mem_serreFibrations_restrictPreimage hp (range f)) (apply_mem_range hτ e hb hs) hY hn
  have hcomp : _root_.TopCat.ofHom ⟨(mapsTo_preimage_singleton_preimage_range hg
      (apply_mem_range hτ e hb hs)).restrict, g.hom.continuous.restrict _⟩ =
      _root_.TopCat.ofHom ⟨(mapsTo_preimage_singleton_preimage_singleton (b' := b') hg).restrict,
        g.hom.continuous.restrict _⟩ ≫ p.hom.preimageInclusion (apply_mem_range hτ e hb hs) := by
    ext x
    simp [ContinuousMap.hom_preimageInclusion]
  rw [hcomp, Functor.map_comp, ModuleCat.hom_comp, LinearMap.coe_comp]
  exact ((ModuleCat.mono_iff_injective _).1 inferInstance).comp hinj

end Transverse

end TopCat

end TauCeti
