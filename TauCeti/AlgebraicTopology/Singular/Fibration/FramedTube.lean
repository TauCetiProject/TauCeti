/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Excision
public import TauCeti.AlgebraicTopology.Singular.Fibration.Disk
public import TauCeti.Geometry.Manifold.PontryaginThom.Basic

/-!
# Local homology of a Serre fibration along a framed submanifold

Let `p : E → M` be a Serre fibration, and let `f : S → M` be the core of a framed tube
`τ : S × V → M` (`TauCeti.IsFramedTube`), with fibre a real normed space `V` of finite dimension
`r`. For a closed submanifold `Y = f(S)` of a manifold `M`, this is a trivialization `Y × ℝʳ` of a
tubular neighbourhood, so `Y` has trivial normal bundle. Write `E|_Y = p⁻¹(f(S))` for the part of
`E` over the core. When the core is closed, this file computes the local homology of `E` along
`E|_Y`, with coefficients in a ring `R`:

* `Hₘ(E, E ∖ E|_Y; R) = 0` for `m < r`
  (`TauCeti.IsFramedTube.isZero_singularHomology_complPreimage`);
* `Hₙ₊ᵣ(E, E ∖ E|_Y; R) ≅ Hₙ(E|_Y; R)`
  (`TauCeti.IsFramedTube.singularHomologyComplPreimageIso`).

The composite `Hₙ₊ᵣ(E) → Hₙ₊ᵣ(E, E ∖ E|_Y) ≅ Hₙ(E|_Y)` is the shriek map `j_!` of the inclusion
`j : Y → M`, with untwisted coefficients on the total space. Barraud, Damian, Humilière and Oancea
use this map in their Theorem G on hypersurfaces knotted with spheres, for a closed submanifold
`Y` with trivial normal bundle meeting an embedded sphere transversely in one point: their
Proposition 7.5 asks for a class `α` with `j_{Y!} α` not torsion, and their Lemma 7.7 detects such
classes through the fibre inclusion over `Y`. For the identity of `M` the computation is the Thom
isomorphism of the framed submanifold, `Hₙ₊ᵣ(M, M ∖ f(S)) ≅ Hₙ(S)`
(`TauCeti.IsFramedTube.singularHomologyComplRangeIso`). For a single point it recovers the local
homology of `E` along a fibre, computed from a chart in
`TauCeti.AlgebraicTopology.Singular.Fibration.LocalHomology`.

## The computation

The tube is an open embedding, so `τ` identifies `S × V` with the open set `range τ`, and the
**normal coordinate** `range τ → V` (`TauCeti.IsFramedTube.normalCoord`) reads off the
`V`-component; it vanishes exactly on the core (`TauCeti.IsFramedTube.normalCoord_eq_zero_iff`).
The normal coordinate is the projection `S × V → V` up to a homeomorphism, so it is a Serre
fibration, and so is its composite `TauCeti.IsFramedTube.normalProj` with the restriction of `p`
over `range τ`. Excision onto the open set `p⁻¹(range τ)`, which contains the closed set `E|_Y`,
identifies `Hₖ(E, E ∖ E|_Y)` with the homology of `p⁻¹(range τ)` modulo the part of it over the
complement of the core, which is the part of the composite over `V ∖ {0}`
(`TauCeti.IsFramedTube.complPreimagePairIso`). The homology of a Serre fibration over `V` modulo
the part over `V ∖ {0}` is the shifted homology of its fibre over `0`
(`TauCeti.TopCat.singularHomologyPreimageNeZeroIso`), and this fibre is `E|_Y`
(`TauCeti.IsFramedTube.normalProjFiberHomeomorph`).

## Main definitions and results

* `TauCeti.IsFramedTube.normalCoord`, `TauCeti.IsFramedTube.normalProj`: the normal coordinate of
  the tube, and its composite with the restriction of `p` over the tube.
* `TauCeti.IsFramedTube.mem_serreFibrations_normalProj`: this composite is a Serre fibration.
* `TauCeti.IsFramedTube.isZero_singularHomology_complPreimage`: `Hₘ(E, E ∖ E|_Y) = 0` for `m < r`.
* `TauCeti.IsFramedTube.singularHomologyComplPreimageIso`: `Hₙ₊ᵣ(E, E ∖ E|_Y) ≅ Hₙ(E|_Y)`, with
  its description after excision
  (`TauCeti.IsFramedTube.singularHomologyMap_excisionMap_comp_singularHomologyComplPreimageIso_hom`,
  `TauCeti.IsFramedTube.singularHomologyComplPreimageIso_inv`).
* `TauCeti.IsFramedTube.isZero_singularHomology_complRange`,
  `TauCeti.IsFramedTube.singularHomologyComplRangeIso`: the Thom isomorphism
  `Hₙ₊ᵣ(M, M ∖ f(S)) ≅ Hₙ(S)` of a framed submanifold, and the vanishing below the codimension.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §7 (Theorem 7.1, Proposition 7.5 and
  Lemma 7.7).
* J.-P. Serre, *Homologie singulière des espaces fibrés. Applications*, Ann. of Math. 54 (1951),
  Chapter II.
* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton University Press, 1974, §11 (the Thom isomorphism of a tubular neighbourhood).
-/

public section

noncomputable section

open CategoryTheory Limits Module Set Topology
open TauCeti.TopCat

universe u

namespace TauCeti

namespace IsFramedTube

variable {S V : Type u} [TopologicalSpace S] [NormedAddCommGroup V] {M E : _root_.TopCat.{u}}
  {f : S → M} {τ : S × V → M} (hτ : IsFramedTube f τ)

/-! ### The normal coordinate as a Serre fibration -/

/-- The normal coordinate of a framed tube, with values in `univ ⊆ V`, as a morphism of
topological spaces. -/
private def normalCoordHom :
    _root_.TopCat.of (range τ) ⟶ _root_.TopCat.of (univ : Set V) :=
  _root_.TopCat.ofHom ⟨fun y ↦ ⟨hτ.normalCoord y, mem_univ _⟩,
    hτ.continuous_normalCoord.subtype_mk _⟩

/-- The normal coordinate is a Serre fibration: up to the homeomorphism `τ : S × V ≃ range τ` it is
the projection `S × V → V`, along which a homotopy lifts by keeping the `S`-coordinate fixed. -/
private lemma mem_serreFibrations_normalCoordHom : serreFibrations (normalCoordHom hτ) := by
  let h := hτ.isOpenEmbedding.isEmbedding.toHomeomorph
  refine mem_serreFibrations_of_hasHomotopyLiftingProperty fun A _ g H hH ↦
    ⟨⟨fun q ↦ h ((h.symm (g q.2)).1, (H q : V)), by fun_prop⟩, funext fun q ↦ ?_, fun a ↦ ?_⟩
  · exact Subtype.ext (by simp [normalCoordHom, normalCoord_def, h])
  · have ha : ((H (0, a) : univ) : V) = hτ.normalCoord (g a) := congrArg Subtype.val (hH a)
    simp only [ContinuousMap.coe_mk, ha, normalCoord_def, h, Prod.mk.eta,
      Homeomorph.apply_symm_apply]

variable (p : E ⟶ M)

/-- The restriction of `p` over the tube `range τ`, followed by the normal coordinate of the tube,
with values in `univ ⊆ V`. -/
def normalProj :
    _root_.TopCat.of (p ⁻¹' range τ) ⟶ _root_.TopCat.of (univ : Set V) :=
  _root_.TopCat.ofHom (p.hom.restrictPreimage (range τ)) ≫ normalCoordHom hτ

@[simp]
lemma coe_normalProj_apply (z : _root_.TopCat.of (p ⁻¹' range τ)) :
    (hτ.normalProj p z : V) = hτ.normalCoord ⟨p z, z.2⟩ :=
  (rfl)

/-- A point of `E` over the tube lies over `0` for `normalProj` exactly when it lies over the core
of the tube. -/
lemma coe_normalProj_eq_zero_iff (z : _root_.TopCat.of (p ⁻¹' range τ)) :
    (hτ.normalProj p z : V) = 0 ↔ p z ∈ range f := by
  rw [coe_normalProj_apply, normalCoord_eq_zero_iff]

variable {p} in
/-- For a Serre fibration `p`, the composite `normalProj` of its restriction over the tube with the
normal coordinate is a Serre fibration. -/
lemma mem_serreFibrations_normalProj (hp : serreFibrations p) :
    serreFibrations (hτ.normalProj p) :=
  serreFibrations.comp_mem _ _ (mem_serreFibrations_restrictPreimage hp _)
    (mem_serreFibrations_normalCoordHom hτ)

/-- Over the tube, the complement of the part of `E` over the core of the tube is the part over the
complement of `0` of `normalProj`. -/
def complPreimagePairIso :
    TopPair.interPair (X := E) (p ⁻¹' range τ) (p ⁻¹' range f)ᶜ ≅
      TopPair.ofSubset (hτ.normalProj p ⁻¹' {x | (x : V) ≠ 0}) :=
  TopPair.ofSubsetIso (Homeomorph.refl _) fun z ↦
    (hτ.coe_normalProj_eq_zero_iff p z).not.symm

/-- The forward map of `complPreimagePairIso` is induced by the identity of `p⁻¹(range τ)`. -/
lemma complPreimagePairIso_hom :
    (hτ.complPreimagePairIso p).hom =
      TopPair.ofSubsetMap (_root_.TopCat.ofHom (Homeomorph.refl (p ⁻¹' range τ)))
        fun z hz ↦ (hτ.coe_normalProj_eq_zero_iff p z).not.2 hz :=
  TopPair.ofSubsetIso_hom _ _

/-- The inverse map of `complPreimagePairIso` is induced by the identity of `p⁻¹(range τ)`. -/
lemma complPreimagePairIso_inv :
    (hτ.complPreimagePairIso p).inv =
      TopPair.ofSubsetMap (_root_.TopCat.ofHom (Homeomorph.refl (p ⁻¹' range τ)))
        fun z hz ↦ (hτ.coe_normalProj_eq_zero_iff p z).not.1 hz :=
  TopPair.ofSubsetIso_inv _ _

/-- The fibre over `0` of `normalProj` is the part of `E` over the core of the tube. -/
def normalProjFiberHomeomorph :
    (hτ.normalProj p ⁻¹' {x | (x : V) = 0}) ≃ₜ (p ⁻¹' range f) where
  toFun z := ⟨z.1.1, (hτ.coe_normalProj_eq_zero_iff p z.1).1 z.2⟩
  invFun y :=
    ⟨⟨y.1, hτ.range_subset_range y.2⟩,
      (hτ.coe_normalProj_eq_zero_iff p _).2 y.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

lemma coe_normalProjFiberHomeomorph_apply (z : hτ.normalProj p ⁻¹' {x | (x : V) = 0}) :
    (hτ.normalProjFiberHomeomorph p z : E) = z.1.1 :=
  (rfl)

lemma coe_normalProjFiberHomeomorph_symm_apply (y : p ⁻¹' range f) :
    ((hτ.normalProjFiberHomeomorph p).symm y).1.1 = y.1 :=
  (rfl)

/-! ### Local homology along the part over the core -/

variable (R : Type u) [Ring R] {p}

/-- Excision onto the part of `E` over the tube, followed by
`TauCeti.IsFramedTube.complPreimagePairIso`. -/
private def excisionIso (hf : IsClosed (range f)) (m : ℕ) :
    (TopPair.ofSubset (p ⁻¹' range f)ᶜ).singularHomology (ModuleCat.of R R) m ≅
      (TopPair.ofSubset (hτ.normalProj p ⁻¹' {x | (x : V) ≠ 0})).singularHomology
        (ModuleCat.of R R) m :=
  haveI := TopPair.isIso_singularHomologyMap_excisionMap_of_isClosed_subset (ModuleCat.of R R)
    (X := E) (hτ.isOpenEmbedding.isOpen_range.preimage p.hom.continuous)
    (hf.preimage p.hom.continuous)
    (preimage_mono hτ.range_subset_range) m
  (asIso (TopPair.singularHomologyMap
      (TopPair.excisionMap (X := E) (p ⁻¹' range τ) (p ⁻¹' range f)ᶜ) _ m)).symm ≪≫
    TopPair.singularHomologyMapIso _ (hτ.complPreimagePairIso p) m

variable [NormedSpace ℝ V] [FiniteDimensional ℝ V]

include hτ in
/-- **The homology of a Serre fibration modulo the complement of the part over a framed
submanifold vanishes below the codimension.** Let `p : E ⟶ M` be a Serre fibration, and let
`f : S → M` be the core of a framed tube `τ : S × V → M` with fibre a finite-dimensional real
normed space, with closed range. Then `Hₘ(E, E ∖ p⁻¹(f(S)); R) = 0` for every `m < dim V`. -/
theorem isZero_singularHomology_complPreimage (hf : IsClosed (range f)) (hp : serreFibrations p)
    {m : ℕ} (hm : m < finrank ℝ V) :
    IsZero ((TopPair.ofSubset (p ⁻¹' range f)ᶜ).singularHomology (ModuleCat.of R R) m) :=
  (isZero_singularHomology_preimage_ne_zero R (hτ.mem_serreFibrations_normalProj hp) convex_univ
    Filter.univ_mem hm).of_iso (hτ.excisionIso R hf m)

/-- **The homology of a Serre fibration modulo the complement of the part over a framed
submanifold is the shifted homology of that part.** Let `p : E ⟶ M` be a Serre fibration, and let
`f : S → M` be the core of a framed tube `τ : S × V → M` with closed range, with fibre a real
normed space of finite dimension `r`. Then `Hₘ(E, E ∖ p⁻¹(f(S)); R) ≅ Hₙ(p⁻¹(f(S)); R)` for
`m = n + r`.

The isomorphism is excision onto the part of `E` over the tube, followed by
`TauCeti.TopCat.singularHomologyPreimageNeZeroIso` for the composite `normalProj` of the
restriction of `p` with the normal coordinate of the tube
(`TauCeti.IsFramedTube.singularHomologyMap_excisionMap_comp_singularHomologyComplPreimageIso_hom`).
-/
def singularHomologyComplPreimageIso (hf : IsClosed (range f)) (hp : serreFibrations p)
    (n m : ℕ) (h : n + finrank ℝ V = m) :
    (TopPair.ofSubset (p ⁻¹' range f)ᶜ).singularHomology (ModuleCat.of R R) m ≅
      ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) n).obj
        (ModuleCat.of R R)).obj (_root_.TopCat.of (p ⁻¹' range f)) :=
  hτ.excisionIso R hf m ≪≫
    singularHomologyPreimageNeZeroIso R (hτ.mem_serreFibrations_normalProj hp) convex_univ
      Filter.univ_mem n m h ≪≫
    ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) n).obj
      (ModuleCat.of R R)).mapIso (_root_.TopCat.isoOfHomeo (hτ.normalProjFiberHomeomorph p))

/-- After excision onto the part of `E` over the tube,
`TauCeti.IsFramedTube.singularHomologyComplPreimageIso` is
`TauCeti.TopCat.singularHomologyPreimageNeZeroIso` for `normalProj`, followed by the
identification of its fibre over `0` with the part of `E` over the core. -/
@[reassoc]
lemma singularHomologyMap_excisionMap_comp_singularHomologyComplPreimageIso_hom
    (hf : IsClosed (range f)) (hp : serreFibrations p) (n m : ℕ) (h : n + finrank ℝ V = m) :
    TopPair.singularHomologyMap
        (TopPair.excisionMap (X := E) (p ⁻¹' range τ) (p ⁻¹' range f)ᶜ) (ModuleCat.of R R) m ≫
        (hτ.singularHomologyComplPreimageIso R hf hp n m h).hom =
      TopPair.singularHomologyMap (hτ.complPreimagePairIso p).hom (ModuleCat.of R R) m ≫
        (singularHomologyPreimageNeZeroIso R (hτ.mem_serreFibrations_normalProj hp) convex_univ
          Filter.univ_mem n m h).hom ≫
        ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) n).obj
          (ModuleCat.of R R)).map
          (_root_.TopCat.isoOfHomeo (hτ.normalProjFiberHomeomorph p)).hom := by
  simp [singularHomologyComplPreimageIso, excisionIso]

/-- The inverse of `TauCeti.IsFramedTube.singularHomologyComplPreimageIso` is the inverse of the
identification of the fibre of `normalProj` over `0` with the part of `E` over the core, followed
by the inverse of `TauCeti.TopCat.singularHomologyPreimageNeZeroIso`, the inverse of
`TauCeti.IsFramedTube.complPreimagePairIso` and the excision inclusion. -/
@[reassoc]
lemma singularHomologyComplPreimageIso_inv
    (hf : IsClosed (range f)) (hp : serreFibrations p) (n m : ℕ) (h : n + finrank ℝ V = m) :
    (hτ.singularHomologyComplPreimageIso R hf hp n m h).inv =
      ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) n).obj
          (ModuleCat.of R R)).map
          (_root_.TopCat.isoOfHomeo (hτ.normalProjFiberHomeomorph p)).inv ≫
        (singularHomologyPreimageNeZeroIso R (hτ.mem_serreFibrations_normalProj hp) convex_univ
          Filter.univ_mem n m h).inv ≫
        TopPair.singularHomologyMap (hτ.complPreimagePairIso p).inv (ModuleCat.of R R) m ≫
        TopPair.singularHomologyMap
          (TopPair.excisionMap (X := E) (p ⁻¹' range τ) (p ⁻¹' range f)ᶜ) (ModuleCat.of R R) m := by
  simp [singularHomologyComplPreimageIso, excisionIso]

/-! ### The Thom isomorphism of a framed submanifold -/

/-- The part of `M` over the core of a framed tube, for the identity of `M`, is the source `S` of
the core. -/
private def preimageIdHomeomorph : ((𝟙 M : M ⟶ M) ⁻¹' range f) ≃ₜ S :=
  (Homeomorph.setCongr (by ext; simp)).trans hτ.isEmbedding.toHomeomorph.symm

include hτ in
/-- **The homology of a space modulo the complement of a framed submanifold vanishes below the
codimension.** If `f : S → M` is the core of a framed tube `τ : S × V → M` with closed range and
with fibre a finite-dimensional real normed space, then `Hₘ(M, M ∖ f(S); R) = 0` for every
`m < dim V`. -/
theorem isZero_singularHomology_complRange (hf : IsClosed (range f)) {m : ℕ}
    (hm : m < finrank ℝ V) :
    IsZero ((TopPair.ofSubset (range f)ᶜ).singularHomology (ModuleCat.of R R) m) :=
  hτ.isZero_singularHomology_complPreimage R (p := 𝟙 M) hf (serreFibrations.id_mem M) hm

/-- **The Thom isomorphism of a framed submanifold.** If `f : S → M` is the core of a framed tube
`τ : S × V → M` with closed range, with fibre a real normed space of finite dimension `r`, then
`Hₘ(M, M ∖ f(S); R) ≅ Hₙ(S; R)` for `m = n + r`. This is
`TauCeti.IsFramedTube.singularHomologyComplPreimageIso` for the identity of `M`, followed by the
homeomorphism of `f(S)` with `S`. -/
def singularHomologyComplRangeIso (hf : IsClosed (range f)) (n m : ℕ)
    (h : n + finrank ℝ V = m) :
    (TopPair.ofSubset (range f)ᶜ).singularHomology (ModuleCat.of R R) m ≅
      ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) n).obj
        (ModuleCat.of R R)).obj (_root_.TopCat.of S) :=
  hτ.singularHomologyComplPreimageIso R (p := 𝟙 M) hf (serreFibrations.id_mem M) n m h ≪≫
    ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) n).obj
      (ModuleCat.of R R)).mapIso (_root_.TopCat.isoOfHomeo hτ.preimageIdHomeomorph)

end IsFramedTube

end TauCeti
