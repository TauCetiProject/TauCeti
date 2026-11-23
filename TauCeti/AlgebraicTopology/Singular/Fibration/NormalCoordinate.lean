/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Excision
public import TauCeti.AlgebraicTopology.Singular.Fibration.Disk

/-!
# Local homology of a Serre fibration along the zero set of a normal coordinate

Let `p : E → B` be a Serre fibration and `Z ⊆ B` a closed subset with a **normal coordinate**: an
open neighbourhood `W` of `Z` and a Serre fibration `ν : W → K` onto a convex neighbourhood `K` of
`0` in a real normed space `V` of finite dimension `r`, whose zero set is `Z`. The main examples are
a point of a manifold, with `ν` a chart, and a framed submanifold, with `ν` the normal coordinate of
a framed tube. The local homology of `E` along `p⁻¹(Z)` is the shifted homology of `p⁻¹(Z)`, with
coefficients in a module `M` over a ring `R`:

* `Hₘ(E, E ∖ p⁻¹(Z); M) = 0` for `m < r`
  (`TauCeti.TopCat.isZero_singularHomology_complPreimage`);
* `Hₙ₊ᵣ(E, E ∖ p⁻¹(Z); M) ≅ Hₙ(p⁻¹(Z); M)`
  (`TauCeti.TopCat.singularHomologyComplPreimageIso`).

The composite `Hₙ₊ᵣ(E) → Hₙ₊ᵣ(E, E ∖ p⁻¹(Z)) ≅ Hₙ(p⁻¹(Z))` is the shriek map `j_!` of the
inclusion `j : Z → B` with coefficients in the fibration. The isomorphism is natural for a map
`g : E' → E` of fibrations over a map of the bases that pulls the normal coordinate of `Z` back to
a normal coordinate of `Z' ⊆ B'`
(`TauCeti.TopCat.singularHomologyComplPreimageIso_hom_naturality`).

## The computation

Excision onto the open set `p⁻¹(W)`, which contains the closed set `p⁻¹(Z)`, identifies
`Hₖ(E, E ∖ p⁻¹(Z))` with `Hₖ(p⁻¹(W), p⁻¹(W) ∖ p⁻¹(Z))`
(`TopPair.isIso_singularHomologyMap_excisionMap_of_isClosed_subset`). The restriction of `p` over
`W`, followed by `ν`, is a Serre fibration over `K` (`TauCeti.TopCat.normalCoordinateProj`) whose
fibre over `0` is `p⁻¹(Z)` (`TauCeti.TopCat.normalCoordinateProjFiberHomeomorph`), and the part of
`p⁻¹(W)` over `K ∖ {0}` is `p⁻¹(W) ∖ p⁻¹(Z)` (`TauCeti.TopCat.normalCoordinateComplPairIso`). The
homology of a Serre fibration over a convex neighbourhood of `0` modulo the part over the punctured
base is the shifted homology of the fibre (`TauCeti.TopCat.singularHomologyPreimageNeZeroIso`), and
vanishes below the dimension (`TauCeti.TopCat.isZero_singularHomology_preimage_ne_zero`).

## References

* J.-P. Serre, *Homologie singulière des espaces fibrés. Applications*, Ann. of Math. 54 (1951),
  Chapter II.
-/

public section

noncomputable section

open CategoryTheory Limits Module Set Topology

universe u

namespace TauCeti

namespace TopCat

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
    normalCoordinateProj p ν z = ν ⟨p z, z.property⟩ :=
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
  hZ ⟨p z, z.property⟩

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

lemma normalCoordinateComplPairIso_inv :
    (normalCoordinateComplPairIso hZ).inv =
      TopPair.ofSubsetMap (_root_.TopCat.ofHom (Homeomorph.refl (p ⁻¹' W)))
        fun z hz ↦ (normalCoordinateProj_eq_zero_iff (p := p) hZ z).not.1 hz :=
  TopPair.ofSubsetIso_inv _ _

/-- The fibre over `0` of `TauCeti.TopCat.normalCoordinateProj` is `p⁻¹(Z)`. -/
def normalCoordinateProjFiberHomeomorph (hZW : Z ⊆ W) :
    (normalCoordinateProj p ν ⁻¹' {x | (x : V) = 0}) ≃ₜ (p ⁻¹' Z) where
  toFun z := ⟨z.val.val, (normalCoordinateProj_eq_zero_iff hZ z.val).1 z.property⟩
  invFun y := ⟨⟨y.val, hZW y.property⟩, (normalCoordinateProj_eq_zero_iff hZ _).2 y.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtypeVal.comp continuous_subtypeVal).subtype_mk _
  continuous_invFun := (continuous_subtypeVal.subtype_mk _).subtype_mk _

lemma coe_normalCoordinateProjFiberHomeomorph_apply (hZW : Z ⊆ W)
    (z : normalCoordinateProj p ν ⁻¹' {x | (x : V) = 0}) :
    (normalCoordinateProjFiberHomeomorph hZ hZW z : E) = z.val.val :=
  (rfl)

lemma coe_normalCoordinateProjFiberHomeomorph_symm_apply (hZW : Z ⊆ W) (y : p ⁻¹' Z) :
    ((normalCoordinateProjFiberHomeomorph hZ hZW).symm y).val.val = y.val :=
  (rfl)

variable {R : Type*} [Ring R] (M : ModuleCat.{u} R) (hW : IsOpen W) (hZc : IsClosed Z)
  (hZW : Z ⊆ W)

include hW hZc hZW in
/-- Excision onto the open set `p⁻¹(W)`, which contains the closed set `p⁻¹(Z)`, is an isomorphism
on the homology of `(E, E ∖ p⁻¹(Z))`. -/
lemma isIso_singularHomologyMap_excisionMap_preimage (m : ℕ) :
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

/-- The inverse of `TauCeti.TopCat.singularHomologyComplPreimageIso` is the inverse of the
identification `TauCeti.TopCat.normalCoordinateProjFiberHomeomorph` of the fibre over `0` with
`p⁻¹(Z)`, followed by the inverse of `TauCeti.TopCat.singularHomologyPreimageNeZeroIso`, the inverse
of `TauCeti.TopCat.normalCoordinateComplPairIso` and the excision inclusion. -/
@[reassoc]
lemma singularHomologyComplPreimageIso_inv (hp : serreFibrations p) (hν : serreFibrations ν)
    (hK : Convex ℝ K) (hK₀ : K ∈ 𝓝 (0 : V)) (n m : ℕ) (h : n + finrank ℝ V = m) :
    (singularHomologyComplPreimageIso hZ M hW hZc hZW hp hν hK hK₀ n m h).inv =
      ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) n).obj M).map
          (_root_.TopCat.isoOfHomeo (normalCoordinateProjFiberHomeomorph hZ hZW)).inv ≫
        (singularHomologyPreimageNeZeroIso M (mem_serreFibrations_normalCoordinateProj hp hν) hK
          hK₀ n m h).inv ≫
        TopPair.singularHomologyMap (normalCoordinateComplPairIso hZ).inv M m ≫
        TopPair.singularHomologyMap (TopPair.excisionMap (X := E) (p ⁻¹' W) (p ⁻¹' Z)ᶜ) M m := by
  simp [singularHomologyComplPreimageIso, preimageExcisionIso]

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
  exact congrArg Subtype.val (hgν x.val x.property)

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
  -- Both composites of maps of fibres send a point `x` of `p'⁻¹(Z')` to `g x`.
  refine congrArg _ ?_
  ext x
  rfl

end Naturality

end TopCat

end TauCeti
