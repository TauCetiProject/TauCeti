/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Fibration.LocalHomology
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
(`TauCeti.IsFramedTube.coe_normalProj_eq_zero_iff`), because `τ` is injective. The homology of
`E` modulo `E ∖ E|_Y` is then the homology of the fibre over `0`, shifted by `r`, and vanishes
below `r`, by the computation along a closed set with a normal coordinate
(`TauCeti.TopCat.singularHomologyComplPreimageIsoOfProj` and
`TauCeti.TopCat.isZero_singularHomology_complPreimage_of_proj`), which also gives the local
homology at a point from a chart ball.

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

variable {p : E ⟶ B} (R : Type u) [Ring R] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- **The homology of a Serre fibration modulo the complement of the part over a framed
submanifold vanishes below the codimension.** Let `τ : Y × V → B` be a framed tube around
`f : Y → B` with closed image, and `p : E ⟶ B` a Serre fibration. Then
`Hₘ(E, E ∖ p⁻¹(f(Y)); R) = 0` for every `m < dim V`. -/
theorem isZero_singularHomology_complPreimage (h : IsFramedTube f τ) (hf : IsClosed (range f))
    (hp : serreFibrations p) {m : ℕ} (hm : m < finrank ℝ V) :
    IsZero ((TopPair.ofSubset (p ⁻¹' range f)ᶜ).singularHomology (ModuleCat.of R R) m) :=
  isZero_singularHomology_complPreimage_of_proj R h.isOpenEmbedding.isOpen_range hf
    h.range_subset_range h.coe_normalProj_eq_zero_iff (h.mem_serreFibrations_normalProj hp)
    convex_univ Filter.univ_mem hm

/-- **The local homology of a Serre fibration along the part over a framed submanifold is the
shifted homology of that part.** Let `τ : Y × V → B` be a framed tube around `f : Y → B` with
closed image, with `V` a real normed space of finite dimension `r`, and let `p : E ⟶ B` be a Serre
fibration. Then `Hₘ(E, E ∖ p⁻¹(f(Y)); R) ≅ Hₙ(p⁻¹(f(Y)); R)` for `m = n + r`.

The isomorphism is `TauCeti.TopCat.singularHomologyComplPreimageIsoOfProj` for the normal
coordinate `TauCeti.IsFramedTube.normalProj` of `p`, that is, excision onto the part of `E` over
the tube, followed by `TauCeti.TopCat.singularHomologyPreimageNeZeroIso` for the normal coordinate
(`TauCeti.IsFramedTube.singularHomologyMap_excisionMap_comp_singularHomologyComplPreimageIso_hom`).
-/
def singularHomologyComplPreimageIso (h : IsFramedTube f τ) (hf : IsClosed (range f))
    (hp : serreFibrations p) (n m : ℕ) (hnm : n + finrank ℝ V = m) :
    (TopPair.ofSubset (p ⁻¹' range f)ᶜ).singularHomology (ModuleCat.of R R) m ≅
      ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) n).obj
        (ModuleCat.of R R)).obj (_root_.TopCat.of (p ⁻¹' range f)) :=
  singularHomologyComplPreimageIsoOfProj R h.isOpenEmbedding.isOpen_range hf h.range_subset_range
    h.coe_normalProj_eq_zero_iff (h.mem_serreFibrations_normalProj hp) convex_univ
    Filter.univ_mem n m hnm

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
      TopPair.singularHomologyMap (complPreimagePairIso h.coe_normalProj_eq_zero_iff).hom
          (ModuleCat.of R R) m ≫
        (singularHomologyPreimageNeZeroIso R (h.mem_serreFibrations_normalProj hp) convex_univ
          Filter.univ_mem n m hnm).hom ≫
        ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) n).obj
          (ModuleCat.of R R)).map (_root_.TopCat.isoOfHomeo
            (preimageZeroHomeomorph h.coe_normalProj_eq_zero_iff h.range_subset_range)).hom :=
  singularHomologyMap_excisionMap_comp_singularHomologyComplPreimageIsoOfProj_hom R _ _ _ _ _ _ _
    n m hnm

/-- The inverse of `TauCeti.IsFramedTube.singularHomologyComplPreimageIso` is the inverse of the
identification of the fibre over `0` of the normal coordinate with the part of `E` over the core,
followed by the inverse of `TauCeti.TopCat.singularHomologyPreimageNeZeroIso` and the inclusion
of pairs of excision. -/
@[reassoc]
lemma singularHomologyComplPreimageIso_inv (h : IsFramedTube f τ) (hf : IsClosed (range f))
    (hp : serreFibrations p) (n m : ℕ) (hnm : n + finrank ℝ V = m) :
    (h.singularHomologyComplPreimageIso R hf hp n m hnm).inv =
      ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) n).obj
          (ModuleCat.of R R)).map (_root_.TopCat.isoOfHomeo
            (preimageZeroHomeomorph h.coe_normalProj_eq_zero_iff h.range_subset_range)).inv ≫
        (singularHomologyPreimageNeZeroIso R (h.mem_serreFibrations_normalProj hp) convex_univ
          Filter.univ_mem n m hnm).inv ≫
        TopPair.singularHomologyMap (complPreimagePairIso h.coe_normalProj_eq_zero_iff).inv
          (ModuleCat.of R R) m ≫
        TopPair.singularHomologyMap
          (TopPair.excisionMap (X := E) (p ⁻¹' range τ) (p ⁻¹' range f)ᶜ)
          (ModuleCat.of R R) m :=
  singularHomologyComplPreimageIsoOfProj_inv R _ _ _ _ _ _ _ n m hnm

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
          (ModuleCat.of R R)).map (g.preimageMap hg (range f)) :=
  singularHomologyComplPreimageIsoOfProj_hom_naturality R h.isOpenEmbedding.isOpen_range hf
    h.range_subset_range _ _ _ _ convex_univ Filter.univ_mem hg (h.preimageMap_comp_normalProj hg)
    n m hnm

end Naturality

end IsFramedTube

end TauCeti
