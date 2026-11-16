/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Fibration.Disk
public import TauCeti.AlgebraicTopology.Singular.Excision
public import TauCeti.Geometry.Manifold.PontryaginThom.Basic

/-!
# Local homology of a Serre fibration along a framed submanifold

Let `f : Y → B` be the core of a framed tube `τ : Y × V → B` (`TauCeti.IsFramedTube`), that is,
`τ` is an open embedding with `τ (y, 0) = f y`, for a real normed space `V` of finite dimension
`r`; for instance `f` embeds a submanifold of codimension `r` with trivialized normal bundle. Let
`p : E → B` be a Serre fibration and `E|_Y = p⁻¹(f(Y))` its part over the core. When the core
`f(Y)` is closed, for instance when `Y` is compact and `B` is Hausdorff
(`TauCeti.IsFramedTube.isClosed_range`), this file computes the local homology of `E` along
`E|_Y`, with coefficients in a ring `R`:

* `Hₘ(E, E ∖ E|_Y; R) = 0` for `m < r`
  (`TauCeti.IsFramedTube.isZero_singularHomology_complPreimage`);
* `Hₙ₊ᵣ(E, E ∖ E|_Y; R) ≅ Hₙ(E|_Y; R)`
  (`TauCeti.IsFramedTube.singularHomologyComplPreimageIso`).

The composite `Hₙ₊ᵣ(E) → Hₙ₊ᵣ(E, E ∖ E|_Y) ≅ Hₙ(E|_Y)` is the shriek map `j_{Y!}` of the
inclusion `j_Y` of the framed submanifold, with untwisted coefficients on the total space. It is a
Thom isomorphism for the trivialized normal bundle, read on the total space of a fibration. For `Y`
a point it is the analogue, built from a tube instead of a chart ball, of the shriek map of the
inclusion of a point (`TauCeti.TopCat.singularHomologyComplFiberIso`). Barraud, Damian,
Humilière and Oancea use the shriek map of a framed submanifold `Y` of a closed manifold `Q`, for
the evaluation fibration `Map(S², Q) → Q`, in their theorem on hypersurfaces of `T*Q` knotted with
spheres.

## The computation

The tube `U = τ(Y × V)` is an open neighbourhood of the closed set `f(Y)`, so excision onto the open
set `p⁻¹(U)` identifies `Hₖ(E, E ∖ E|_Y)` with `Hₖ(p⁻¹(U), p⁻¹(U) ∖ E|_Y)`
(`TopPair.isIso_singularHomologyMap_excisionMap_of_isClosed_subset`). The restriction of `p` over
`U`, followed by the inverse of `τ` and the projection `Y × V → V`, is a Serre fibration over `V`,
the **normal coordinate** of `p` (`TauCeti.IsFramedTube.normalProj`), as a composite of a
restriction of `p`, a homeomorphism and a product projection. Its fibre over `0` is `E|_Y`
(`TauCeti.IsFramedTube.normalProjFiberHomeomorph`), and the part of `p⁻¹(U)` over `V ∖ {0}` is
`p⁻¹(U) ∖ E|_Y` (`TauCeti.IsFramedTube.normalProjComplPreimagePairIso`), because `τ` is injective.
The homology of a Serre fibration over the convex neighbourhood `V` of `0` modulo the part over
`V ∖ {0}` is the homology of the fibre over `0`, shifted by `r`
(`TauCeti.TopCat.singularHomologyPreimageNeZeroIso`), and vanishes below `r`
(`TauCeti.TopCat.isZero_singularHomology_preimage_ne_zero`). These are the steps of the computation
at a point in `TauCeti.AlgebraicTopology.Singular.Fibration.LocalHomology`, with the tube in place
of a chart ball.

## Main definitions and results

* `TauCeti.IsFramedTube.normalProj`: the normal coordinate `p⁻¹(U) → V` of `p` over the tube, a
  Serre fibration (`TauCeti.IsFramedTube.mem_serreFibrations_normalProj`).
* `TauCeti.IsFramedTube.singularHomologyComplPreimageIso`: `Hₙ₊ᵣ(E, E ∖ E|_Y) ≅ Hₙ(E|_Y)`. After
  excision onto `p⁻¹(U)` it is `TauCeti.TopCat.singularHomologyPreimageNeZeroIso` for the normal
  coordinate.
* `TauCeti.IsFramedTube.isZero_singularHomology_complPreimage`: `Hₘ(E, E ∖ E|_Y) = 0` for `m < r`.
* `TauCeti.IsFramedTube.singularHomologyComplPreimageIso_hom_naturality`: the isomorphism is
  natural in maps of Serre fibrations over `B`.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §7, Lemma 7.7.
* J.-P. Serre, *Homologie singulière des espaces fibrés. Applications*, Ann. of Math. 54 (1951),
  Chapter II.
* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 4.D (the Thom isomorphism).
-/

public section

noncomputable section

open CategoryTheory Limits Module Set Topology TauCeti.TopCat

universe u

namespace TauCeti

namespace IsFramedTube

variable {Y : Type*} {V : Type u} [TopologicalSpace Y] [NormedAddCommGroup V]
  {E B : _root_.TopCat.{u}} {f : Y → B} {τ : Y × V → B}

/-- **The normal coordinate of a map over a framed tube.** The restriction of `p : E ⟶ B` over the
tube `τ(Y × V)`, followed by the inverse of `τ` and the projection `Y × V → V`, as a map to the
convex set `univ` of `V`. -/
def normalProj (h : IsFramedTube f τ) (p : E ⟶ B) :
    _root_.TopCat.of (p ⁻¹' range τ) ⟶ _root_.TopCat.of (univ : Set V) :=
  _root_.TopCat.ofHom
    { toFun z := ⟨(h.isOpenEmbedding.isEmbedding.toHomeomorph.symm
        (p.hom.restrictPreimage (range τ) z)).2, mem_univ _⟩
      continuous_toFun := (continuous_snd.comp
        (h.isOpenEmbedding.isEmbedding.toHomeomorph.symm.continuous.comp
          (p.hom.continuous.restrictPreimage))).subtype_mk _ }

/-- The normal coordinate of a point `z` over the tube is the `V`-coordinate of `τ⁻¹(p z)`. -/
@[simp]
lemma coe_normalProj_apply (h : IsFramedTube f τ) {p : E ⟶ B} (z : p ⁻¹' range τ) :
    (h.normalProj p z : V) = (h.isOpenEmbedding.isEmbedding.toHomeomorph.symm ⟨p z, z.2⟩).2 :=
  (rfl)

/-- A point over the tube lies over `0` in the normal coordinate exactly when it lies over the
core `f(Y)`. -/
lemma coe_normalProj_eq_zero_iff (h : IsFramedTube f τ) {p : E ⟶ B} (z : p ⁻¹' range τ) :
    (h.normalProj p z : V) = 0 ↔ p z ∈ range f := by
  rw [coe_normalProj_apply]
  set w := h.isOpenEmbedding.isEmbedding.toHomeomorph.symm ⟨p z, z.2⟩
  have hw : τ w = p z := by
    rw [← h.isOpenEmbedding.isEmbedding.toHomeomorph_apply_coe, Homeomorph.apply_symm_apply]
  refine ⟨fun h0 ↦ ⟨w.1, by rw [← h.apply_zero, ← h0, ← hw]⟩, ?_⟩
  rintro ⟨y, hy⟩
  rw [← h.apply_zero, ← hw] at hy
  exact (congrArg Prod.snd (h.isOpenEmbedding.injective hy)).symm

/-- **The normal coordinate of a Serre fibration over a framed tube is a Serre fibration.** It is
the restriction of `p` over the tube, followed by a homeomorphism onto `Y × V` and the product
projection onto `V`. -/
theorem mem_serreFibrations_normalProj (h : IsFramedTube f τ) {p : E ⟶ B}
    (hp : serreFibrations p) : serreFibrations (h.normalProj p) := by
  refine mem_serreFibrations_iff.2 fun n ↦ ?_
  let e := h.isOpenEmbedding.isEmbedding.toHomeomorph.symm
  have hc : Continuous (p.hom.restrictPreimage (range τ)) := p.hom.continuous.restrictPreimage
  -- The projection `Y × V → V` is the product projection `V × Y → V` after swapping the factors.
  have hsnd := (hasHomotopyLiftingProperty_fst Y
    (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)).comp
    ((Homeomorph.prodComm Y V).hasHomotopyLiftingProperty _) (Homeomorph.prodComm Y V).continuous
  exact ((Homeomorph.Set.univ V).symm.hasHomotopyLiftingProperty _).comp
    (hsnd.comp ((e.hasHomotopyLiftingProperty _).comp
      ((mem_serreFibrations_iff.1 hp n).restrictPreimage (range τ)) hc) (e.continuous.comp hc))
    (continuous_snd.comp (e.continuous.comp hc))

/-- Over the tube, the complement of the part of `E` over the core is the part over the punctured
normal coordinate `V ∖ {0}`. -/
def normalProjComplPreimagePairIso (h : IsFramedTube f τ) (p : E ⟶ B) :
    TopPair.interPair (X := E) (p ⁻¹' range τ) (p ⁻¹' range f)ᶜ ≅
      TopPair.ofSubset (h.normalProj p ⁻¹' {x | (x : V) ≠ 0}) :=
  TopPair.ofSubsetIso (Homeomorph.refl _) fun z ↦
    (h.coe_normalProj_eq_zero_iff z).not.symm

/-- The forward map of `TauCeti.IsFramedTube.normalProjComplPreimagePairIso` is induced by the
identity of `p⁻¹(τ(Y × V))`. -/
lemma normalProjComplPreimagePairIso_hom (h : IsFramedTube f τ) (p : E ⟶ B) :
    (h.normalProjComplPreimagePairIso p).hom =
      TopPair.ofSubsetMap (_root_.TopCat.ofHom (Homeomorph.refl (p ⁻¹' range τ)))
        fun z hz ↦ (h.coe_normalProj_eq_zero_iff z).not.2 hz :=
  TopPair.ofSubsetIso_hom _ _

/-- The inverse map of `TauCeti.IsFramedTube.normalProjComplPreimagePairIso` is induced by the
identity of `p⁻¹(τ(Y × V))`. -/
lemma normalProjComplPreimagePairIso_inv (h : IsFramedTube f τ) (p : E ⟶ B) :
    (h.normalProjComplPreimagePairIso p).inv =
      TopPair.ofSubsetMap (_root_.TopCat.ofHom (Homeomorph.refl (p ⁻¹' range τ)))
        fun z hz ↦ (h.coe_normalProj_eq_zero_iff z).not.1 hz :=
  TopPair.ofSubsetIso_inv _ _

/-- The fibre over `0` of the normal coordinate is the part `p⁻¹(f(Y))` of `E` over the core. -/
def normalProjFiberHomeomorph (h : IsFramedTube f τ) (p : E ⟶ B) :
    (h.normalProj p ⁻¹' {x | (x : V) = 0}) ≃ₜ (p ⁻¹' range f) where
  toFun z := ⟨z.1.1, (h.coe_normalProj_eq_zero_iff z.1).1 z.2⟩
  invFun y := ⟨⟨y.1, h.range_subset_range y.2⟩, (h.coe_normalProj_eq_zero_iff _).2 y.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

/-- `TauCeti.IsFramedTube.normalProjFiberHomeomorph` does not move the underlying point of `E`. -/
lemma coe_normalProjFiberHomeomorph_apply (h : IsFramedTube f τ) (p : E ⟶ B)
    (z : h.normalProj p ⁻¹' {x | (x : V) = 0}) :
    (h.normalProjFiberHomeomorph p z : E) = z.1.1 :=
  (rfl)

/-- The inverse of `TauCeti.IsFramedTube.normalProjFiberHomeomorph` does not move the underlying
point of `E`. -/
lemma coe_normalProjFiberHomeomorph_symm_apply (h : IsFramedTube f τ) (p : E ⟶ B)
    (y : p ⁻¹' range f) : ((h.normalProjFiberHomeomorph p).symm y).1.1 = y.1 :=
  (rfl)

variable {p : E ⟶ B} (R : Type u) [Ring R]

/-- Excision onto the part of `E` over the tube is an isomorphism on homology. -/
private lemma isIso_singularHomologyMap_excisionMap_tube (h : IsFramedTube f τ)
    (hf : IsClosed (range f)) (m : ℕ) :
    IsIso (TopPair.singularHomologyMap
      (TopPair.excisionMap (X := E) (p ⁻¹' range τ) (p ⁻¹' range f)ᶜ) (ModuleCat.of R R) m) :=
  TopPair.isIso_singularHomologyMap_excisionMap_of_isClosed_subset (ModuleCat.of R R)
    (X := E) (h.isOpenEmbedding.isOpen_range.preimage p.hom.continuous)
    (hf.preimage p.hom.continuous) (preimage_mono h.range_subset_range) m

/-- Excision onto the part of `E` over the tube, followed by
`TauCeti.IsFramedTube.normalProjComplPreimagePairIso`. -/
private def excisionIso (h : IsFramedTube f τ) (hf : IsClosed (range f)) (m : ℕ) :
    (TopPair.ofSubset (p ⁻¹' range f)ᶜ).singularHomology (ModuleCat.of R R) m ≅
      (TopPair.ofSubset (h.normalProj p ⁻¹' {x | (x : V) ≠ 0})).singularHomology
        (ModuleCat.of R R) m :=
  haveI := isIso_singularHomologyMap_excisionMap_tube (p := p) R h hf m
  (asIso (TopPair.singularHomologyMap
      (TopPair.excisionMap (X := E) (p ⁻¹' range τ) (p ⁻¹' range f)ᶜ) _ m)).symm ≪≫
    TopPair.singularHomologyMapIso _ (h.normalProjComplPreimagePairIso p) m

/-- The defining square of `excisionIso`: after the excision inclusion it is the map induced by
`TauCeti.IsFramedTube.normalProjComplPreimagePairIso`. -/
@[reassoc]
private lemma singularHomologyMap_excisionMap_comp_excisionIso_hom (h : IsFramedTube f τ)
    (hf : IsClosed (range f)) (m : ℕ) :
    TopPair.singularHomologyMap
        (TopPair.excisionMap (X := E) (p ⁻¹' range τ) (p ⁻¹' range f)ᶜ) (ModuleCat.of R R) m ≫
        (excisionIso R h hf m).hom =
      TopPair.singularHomologyMap (h.normalProjComplPreimagePairIso p).hom
        (ModuleCat.of R R) m := by
  simp [excisionIso]

variable [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- **The homology of a Serre fibration modulo the complement of the part over a framed
submanifold vanishes below the codimension.** Let `τ : Y × V → B` be a framed tube around
`f : Y → B` with closed image, and `p : E ⟶ B` a Serre fibration. Then
`Hₘ(E, E ∖ p⁻¹(f(Y)); R) = 0` for every `m < dim V`. -/
theorem isZero_singularHomology_complPreimage (h : IsFramedTube f τ) (hf : IsClosed (range f))
    (hp : serreFibrations p) {m : ℕ} (hm : m < finrank ℝ V) :
    IsZero ((TopPair.ofSubset (p ⁻¹' range f)ᶜ).singularHomology (ModuleCat.of R R) m) :=
  (isZero_singularHomology_preimage_ne_zero R (h.mem_serreFibrations_normalProj hp) convex_univ
    Filter.univ_mem hm).of_iso (excisionIso R h hf m)

/-- **The local homology of a Serre fibration along the part over a framed submanifold is the
shifted homology of that part.** Let `τ : Y × V → B` be a framed tube around `f : Y → B` with
closed image, with `V` a real normed space of finite dimension `r`, and let `p : E ⟶ B` be a Serre
fibration. Then `Hₘ(E, E ∖ p⁻¹(f(Y)); R) ≅ Hₙ(p⁻¹(f(Y)); R)` for `m = n + r`.

The isomorphism is excision onto the part of `E` over the tube, followed by
`TauCeti.TopCat.singularHomologyPreimageNeZeroIso` for the normal coordinate
`TauCeti.IsFramedTube.normalProj` of `p`
(`TauCeti.IsFramedTube.singularHomologyMap_excisionMap_comp_singularHomologyComplPreimageIso_hom`).
-/
def singularHomologyComplPreimageIso (h : IsFramedTube f τ) (hf : IsClosed (range f))
    (hp : serreFibrations p) (n m : ℕ) (hnm : n + finrank ℝ V = m) :
    (TopPair.ofSubset (p ⁻¹' range f)ᶜ).singularHomology (ModuleCat.of R R) m ≅
      ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) n).obj
        (ModuleCat.of R R)).obj (_root_.TopCat.of (p ⁻¹' range f)) :=
  excisionIso R h hf m ≪≫
    singularHomologyPreimageNeZeroIso R (h.mem_serreFibrations_normalProj hp) convex_univ
      Filter.univ_mem n m hnm ≪≫
    ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) n).obj
      (ModuleCat.of R R)).mapIso (_root_.TopCat.isoOfHomeo (h.normalProjFiberHomeomorph p))

/-- The isomorphism `TauCeti.IsFramedTube.singularHomologyComplPreimageIso` commutes with excision
onto the part of `E` over the tube: after excision it is
`TauCeti.TopCat.singularHomologyPreimageNeZeroIso` for the normal coordinate of `p`, followed by
the identification of its fibre over `0` with the part of `E` over the core. -/
@[reassoc]
lemma singularHomologyMap_excisionMap_comp_singularHomologyComplPreimageIso_hom
    (h : IsFramedTube f τ) (hf : IsClosed (range f)) (hp : serreFibrations p) (n m : ℕ)
    (hnm : n + finrank ℝ V = m) :
    TopPair.singularHomologyMap
        (TopPair.excisionMap (X := E) (p ⁻¹' range τ) (p ⁻¹' range f)ᶜ) (ModuleCat.of R R) m ≫
        (h.singularHomologyComplPreimageIso R hf hp n m hnm).hom =
      TopPair.singularHomologyMap (h.normalProjComplPreimagePairIso p).hom
          (ModuleCat.of R R) m ≫
        (singularHomologyPreimageNeZeroIso R (h.mem_serreFibrations_normalProj hp) convex_univ
          Filter.univ_mem n m hnm).hom ≫
        ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) n).obj
          (ModuleCat.of R R)).map
          (_root_.TopCat.isoOfHomeo (h.normalProjFiberHomeomorph p)).hom := by
  simp [singularHomologyComplPreimageIso, excisionIso]

/-- The inverse of `TauCeti.IsFramedTube.singularHomologyComplPreimageIso` is the inverse of the
identification of the fibre over `0` of the normal coordinate with the part of `E` over the core,
followed by the inverse of `TauCeti.TopCat.singularHomologyPreimageNeZeroIso` and the inclusion
of pairs of excision. -/
lemma singularHomologyComplPreimageIso_inv (h : IsFramedTube f τ) (hf : IsClosed (range f))
    (hp : serreFibrations p) (n m : ℕ) (hnm : n + finrank ℝ V = m) :
    (h.singularHomologyComplPreimageIso R hf hp n m hnm).inv =
      ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) n).obj
          (ModuleCat.of R R)).map
          (_root_.TopCat.isoOfHomeo (h.normalProjFiberHomeomorph p)).inv ≫
        (singularHomologyPreimageNeZeroIso R (h.mem_serreFibrations_normalProj hp) convex_univ
          Filter.univ_mem n m hnm).inv ≫
        TopPair.singularHomologyMap (h.normalProjComplPreimagePairIso p).inv
          (ModuleCat.of R R) m ≫
        TopPair.singularHomologyMap
          (TopPair.excisionMap (X := E) (p ⁻¹' range τ) (p ⁻¹' range f)ᶜ)
          (ModuleCat.of R R) m := by
  simp [singularHomologyComplPreimageIso, excisionIso]

/-! ### Naturality in maps of fibrations -/

section Naturality

variable {E' : _root_.TopCat.{u}} {p' : E' ⟶ B} {g : E ⟶ E'}

omit [NormedSpace ℝ V] [FiniteDimensional ℝ V] in
/-- Over the tube, the restriction of a map `g` over `B` is a map over `V`: it commutes with the
normal coordinates. -/
@[reassoc]
lemma preimageMap_comp_normalProj (h : IsFramedTube f τ) (hg : g ≫ p' = p) :
    g.preimageMap hg (range τ) ≫ h.normalProj p' = h.normalProj p := by
  ext z
  have hz : p' (g.preimageMap hg (range τ) z) = p z := by
    rw [TopCat.Hom.coe_preimageMap_apply, ← ConcreteCategory.comp_apply, hg]
  rw [ConcreteCategory.comp_apply, coe_normalProj_apply, coe_normalProj_apply]
  -- Both sides are the `V`-coordinate of `τ⁻¹` at the same point of the tube, by `hz`.
  congr 3

omit [NormedSpace ℝ V] [FiniteDimensional ℝ V] in
/-- The isomorphism `excisionIso` is natural in maps of fibrations over `B`: after excision, the
map induced by `g` is the map induced by its restriction over the tube. -/
@[reassoc]
private lemma excisionIso_hom_naturality (h : IsFramedTube f τ) (hf : IsClosed (range f))
    (hg : g ≫ p' = p) (m : ℕ) :
    TopPair.singularHomologyMap
        (TopPair.ofSubsetMap g (g.mapsTo_preimage_of_comp_eq hg (range f)ᶜ))
        (ModuleCat.of R R) m ≫ (excisionIso (p := p') R h hf m).hom =
      (excisionIso (p := p) R h hf m).hom ≫
        TopPair.singularHomologyMap (TopPair.ofSubsetMap (g.preimageMap hg (range τ))
          ((g.preimageMap hg (range τ)).mapsTo_preimage_of_comp_eq
            (h.preimageMap_comp_normalProj hg) _)) (ModuleCat.of R R) m := by
  -- The map of excision data induced by `g`.
  let Q := TopPair.interPairMap g (g.mapsTo_preimage_of_comp_eq hg (range τ))
    (g.mapsTo_preimage_of_comp_eq hg (range f)ᶜ)
  have hQ : TopPair.excisionMap (X := E) (p ⁻¹' range τ) (p ⁻¹' range f)ᶜ ≫
        TopPair.ofSubsetMap g (g.mapsTo_preimage_of_comp_eq hg (range f)ᶜ) =
      Q ≫ TopPair.excisionMap (X := E') (p' ⁻¹' range τ) (p' ⁻¹' range f)ᶜ :=
    (TopPair.interPairMap_comp_excisionMap g _ _).symm
  have hQ' : (h.normalProjComplPreimagePairIso p).hom ≫
        TopPair.ofSubsetMap (g.preimageMap hg (range τ))
          ((g.preimageMap hg (range τ)).mapsTo_preimage_of_comp_eq
            (h.preimageMap_comp_normalProj hg) _) =
      Q ≫ (h.normalProjComplPreimagePairIso p').hom :=
    TopPair.hom_ext_of_fst _ (by
      ext x
      apply Subtype.ext
      rw [normalProjComplPreimagePairIso_hom, normalProjComplPreimagePairIso_hom,
        TopPair.Hom.fst_comp, TopPair.Hom.fst_comp]
      -- The ambient spaces of the pairs are `TopCat.of` of subtypes, which `rw` does not unfold.
      erw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, TopPair.ofSubsetMap_fst_apply,
        TopPair.ofSubsetMap_fst_apply, TopPair.ofSubsetMap_fst_apply]
      exact (TopCat.Hom.coe_preimageMap_apply g hg _ x).trans
        (TopPair.interPairMap_fst_apply _ _ _ x).symm)
  have := isIso_singularHomologyMap_excisionMap_tube (p := p) R h hf m
  rw [← cancel_epi (TopPair.singularHomologyMap
      (TopPair.excisionMap (X := E) (p ⁻¹' range τ) (p ⁻¹' range f)ᶜ) (ModuleCat.of R R) m),
    singularHomologyMap_excisionMap_comp_excisionIso_hom_assoc,
    ← TopPair.singularHomologyMap_comp_assoc, hQ, TopPair.singularHomologyMap_comp_assoc,
    singularHomologyMap_excisionMap_comp_excisionIso_hom, ← TopPair.singularHomologyMap_comp,
    ← TopPair.singularHomologyMap_comp, hQ']

omit [NormedSpace ℝ V] [FiniteDimensional ℝ V] in
/-- The identifications `TauCeti.IsFramedTube.normalProjFiberHomeomorph` of the fibres over `0`
with the parts over the core carry the restriction of `g` over the tube to the restriction of `g`
over the core. -/
private lemma normalProjFiberHomeomorph_naturality (h : IsFramedTube f τ) (hg : g ≫ p' = p) :
    (_root_.TopCat.isoOfHomeo (h.normalProjFiberHomeomorph p)).hom ≫ g.preimageMap hg (range f) =
      (g.preimageMap hg (range τ)).preimageMap (h.preimageMap_comp_normalProj hg)
          {x | (x : V) = 0} ≫
        (_root_.TopCat.isoOfHomeo (h.normalProjFiberHomeomorph p')).hom := by
  ext x
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, TopCat.Hom.coe_preimageMap_apply]
  -- The homeomorphism is applied through `TopCat.isoOfHomeo`, which `rw` does not see through.
  erw [coe_normalProjFiberHomeomorph_apply]
  exact ((congrArg Subtype.val (TopCat.Hom.coe_preimageMap_apply _ _ _ x)).trans
    (TopCat.Hom.coe_preimageMap_apply _ _ _ x.1)).symm

/-- **The local homology of a Serre fibration along the part over a framed submanifold is natural
in maps of fibrations.** Let `p : E ⟶ B` and `p' : E' ⟶ B` be Serre fibrations, `τ` a framed tube
around `f : Y → B` with closed image and `g : E ⟶ E'` a map over `B`. Under the isomorphisms
`Hₙ₊ᵣ(E, E ∖ p⁻¹(f(Y)); R) ≅ Hₙ(p⁻¹(f(Y)); R)` of
`TauCeti.IsFramedTube.singularHomologyComplPreimageIso`, the map induced by `g` on relative
homology is the map induced by the restriction `p⁻¹(f(Y)) ⟶ p'⁻¹(f(Y))` of `g`. -/
@[reassoc]
theorem singularHomologyComplPreimageIso_hom_naturality (h : IsFramedTube f τ)
    (hf : IsClosed (range f)) (hp : serreFibrations p) (hp' : serreFibrations p')
    (hg : g ≫ p' = p) (n m : ℕ) (hnm : n + finrank ℝ V = m) :
    TopPair.singularHomologyMap
        (TopPair.ofSubsetMap g (g.mapsTo_preimage_of_comp_eq hg (range f)ᶜ))
        (ModuleCat.of R R) m ≫ (h.singularHomologyComplPreimageIso R hf hp' n m hnm).hom =
      (h.singularHomologyComplPreimageIso R hf hp n m hnm).hom ≫
        ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) n).obj
          (ModuleCat.of R R)).map (g.preimageMap hg (range f)) := by
  simp only [singularHomologyComplPreimageIso, Iso.trans_hom, Functor.mapIso_hom, Category.assoc]
  rw [excisionIso_hom_naturality_assoc R h hf hg m,
    singularHomologyPreimageNeZeroIso_hom_naturality_assoc R
      (h.mem_serreFibrations_normalProj hp) (h.mem_serreFibrations_normalProj hp') convex_univ
      Filter.univ_mem (h.preimageMap_comp_normalProj hg)
      ((g.preimageMap hg (range τ)).preimageMap (h.preimageMap_comp_normalProj hg)
        {x | (x : V) = 0}) (fun x ↦ TopCat.Hom.coe_preimageMap_apply _ _ _ x) n m hnm,
    ← Functor.map_comp, ← Functor.map_comp, normalProjFiberHomeomorph_naturality]

end Naturality

end IsFramedTube

end TauCeti
