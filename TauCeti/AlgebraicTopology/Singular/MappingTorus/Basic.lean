/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.MappingTorus.Basic
public import Mathlib.AlgebraicTopology.SingularHomology.HomotopyInvariance
public import TauCeti.Algebra.Homology.HomotopyCofiber

/-!
# Singular chains of a mapping torus

The fibre of the mapping torus of `φ : F ≃ₜ F` has a canonical inclusion at height zero.
Traversing the cylinder from height zero to height one gives a homotopy from this inclusion after
`φ` to the inclusion itself.  This file transfers that homotopy to singular chains and homology,
and constructs the resulting map from the mapping cone of `id - φ_*` to the singular chains of
the mapping torus.

Thus the inclusion coequalizes the identity and monodromy maps, first up to chain homotopy and
then on homology.  Equivalently, its composite with `id - φ_*` is null-homotopic.  The universal
property of the mapping cone then gives the chain map which underlies the Wang sequence.

## Main declarations

* `TauCeti.MappingTorus.singularChainHomotopy`: the composite of the monodromy chain map with
  the fibre-inclusion chain map is chain-homotopic to the fibre-inclusion map.
* `TauCeti.MappingTorus.homologyMap_monodromy_comp_incl`: the corresponding equality on singular
  homology.
* `TauCeti.MappingTorus.wangEndomorphism`: the chain endomorphism `id - φ_*` of the fibre.
* `TauCeti.MappingTorus.wangMappingConeMap`: the canonical map from the mapping cone of
  `id - φ_*` to the singular chains of the mapping torus.
* `TauCeti.MappingTorus.wangMappingConeMapOfSemiconj`: the functorial map between these cones
  induced by a map intertwining two monodromies.

The construction follows the mapping-torus derivation of the Wang sequence; see A. Hatcher,
*Algebraic Topology*, Section 2.2.  The chain homotopy itself is obtained from Mathlib's
homotopy invariance of singular chains, `TopCat.Homotopy.singularChainComplexFunctorObjMap`.
-/

public section

noncomputable section

open AlgebraicTopology CategoryTheory Limits

universe w v u

namespace TauCeti.MappingTorus

variable {F : Type w} [TopologicalSpace F] (φ : F ≃ₜ F)
  {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Preadditive C] (R : C)

/-- The endomorphism of singular chains induced by the monodromy of a mapping torus. -/
noncomputable def monodromyChainMap :
    ((singularChainComplexFunctor C).obj R).obj (TopCat.of F) ⟶
      ((singularChainComplexFunctor C).obj R).obj (TopCat.of F) :=
  ((singularChainComplexFunctor C).obj R).map
    (TopCat.ofHom (⟨φ, φ.continuous⟩ : C(F, F)))

/-- The monodromy chain map is the singular-chain functor applied to the monodromy. -/
lemma monodromyChainMap_def :
    monodromyChainMap φ R =
      ((singularChainComplexFunctor C).obj R).map
        (TopCat.ofHom (⟨φ, φ.continuous⟩ : C(F, F))) :=
  (rfl)

/-- The map on singular chains induced by inclusion of the fibre at height zero. -/
noncomputable def fibreInclusionChainMap :
    ((singularChainComplexFunctor C).obj R).obj (TopCat.of F) ⟶
      ((singularChainComplexFunctor C).obj R).obj (TopCat.of (TauCeti.MappingTorus φ)) :=
  ((singularChainComplexFunctor C).obj R).map
    (TopCat.ofHom (TauCeti.MappingTorus.incl φ))

/-- The fibre-inclusion chain map is the singular-chain functor applied to the fibre inclusion. -/
lemma fibreInclusionChainMap_def :
    fibreInclusionChainMap φ R =
      ((singularChainComplexFunctor C).obj R).map
        (TopCat.ofHom (TauCeti.MappingTorus.incl φ)) :=
  (rfl)

/-- The singular-chain map induced by monodromy followed by fibre inclusion is chain-homotopic
to the fibre-inclusion chain map. -/
def singularChainHomotopy :
    _root_.Homotopy
      (monodromyChainMap φ R ≫ fibreInclusionChainMap φ R)
      (fibreInclusionChainMap φ R) := by
  let f : TopCat.of F ⟶ TopCat.of F := TopCat.ofHom (⟨φ, φ.continuous⟩ : C(F, F))
  let i : TopCat.of F ⟶ TopCat.of (TauCeti.MappingTorus φ) :=
    TopCat.ofHom (TauCeti.MappingTorus.incl φ)
  refine (_root_.Homotopy.ofEq
    (((singularChainComplexFunctor C).obj R).map_comp f i).symm).trans ?_
  -- `TopCat.Homotopy (f ≫ i) i` unfolds to a homotopy between the underlying continuous maps,
  -- whose composite `(incl φ).comp φ` is exactly the source of `monodromyHomotopy φ`.
  exact (show TopCat.Homotopy (f ≫ i) i from
    TauCeti.MappingTorus.monodromyHomotopy φ).singularChainComplexFunctorObjMap R

/-- On singular homology, the map induced by the fibre inclusion is unchanged after
precomposition with the monodromy map. -/
@[simp]
lemma homologyMap_monodromy_comp_incl [CategoryWithHomology C] (n : ℕ) :
    HomologicalComplex.homologyMap
          (monodromyChainMap φ R) n ≫
        HomologicalComplex.homologyMap
          (fibreInclusionChainMap φ R) n =
      HomologicalComplex.homologyMap (fibreInclusionChainMap φ R) n := by
  rw [← HomologicalComplex.homologyMap_comp]
  exact (singularChainHomotopy φ R).homologyMap_eq n

/-- The Wang endomorphism `id - φ_*` on the singular chains of the fibre. -/
noncomputable def wangEndomorphism :
    ((singularChainComplexFunctor C).obj R).obj (TopCat.of F) ⟶
      ((singularChainComplexFunctor C).obj R).obj (TopCat.of F) :=
  𝟙 _ - monodromyChainMap φ R

/-- The Wang endomorphism is the identity minus the monodromy chain map. -/
lemma wangEndomorphism_def : wangEndomorphism φ R = 𝟙 _ - monodromyChainMap φ R :=
  (rfl)

/-- On homology, the Wang endomorphism is the identity minus the map induced by monodromy. -/
@[simp]
lemma homologyMap_wangEndomorphism [CategoryWithHomology C] (n : ℕ) :
    HomologicalComplex.homologyMap (wangEndomorphism φ R) n =
      𝟙 _ - HomologicalComplex.homologyMap (monodromyChainMap φ R) n := by
  rw [wangEndomorphism_def, HomologicalComplex.homologyMap_sub,
    HomologicalComplex.homologyMap_id]

/-- The fibre inclusion after `id - φ_*` is null-homotopic.  The sign is chosen so that the
endomorphism on the fibre is literally `id - φ_*`, rather than its negative. -/
noncomputable def wangNullHomotopy :
    _root_.Homotopy
      (wangEndomorphism φ R ≫ fibreInclusionChainMap φ R) 0 :=
  (_root_.Homotopy.ofEq
      (by rw [wangEndomorphism_def, Preadditive.sub_comp, Category.id_comp])).trans
    (_root_.Homotopy.equivSubZero (singularChainHomotopy φ R).symm)

/-- The null-homotopy used in the Wang mapping-cone map is the negative of the canonical
monodromy homotopy. -/
@[simp]
lemma wangNullHomotopy_hom (i j : ℕ) :
    (wangNullHomotopy φ R).hom i j = -(singularChainHomotopy φ R).hom i j := by
  simp [wangNullHomotopy, _root_.Homotopy.equivSubZero]

section WangMappingCone

variable [HasBinaryBiproducts C]

/-- The chain-level mapping cone of `id - φ_*` used in the mapping-cone formulation of the
Wang sequence. -/
noncomputable abbrev wangMappingCone : ChainComplex C ℕ :=
  HomologicalComplex.homotopyCofiber (wangEndomorphism φ R)

/-- The canonical chain map from the mapping cone of `id - φ_*` to singular chains of the
mapping torus.  It is induced by fibre inclusion and the canonical monodromy homotopy. -/
noncomputable def wangMappingConeMap :
    wangMappingCone φ R ⟶
      ((singularChainComplexFunctor C).obj R).obj (TopCat.of (TauCeti.MappingTorus φ)) :=
  HomologicalComplex.homotopyCofiber.desc (wangEndomorphism φ R)
    (fibreInclusionChainMap φ R) (wangNullHomotopy φ R)

/-- The Wang mapping-cone map restricts to fibre inclusion on the unsuspended summand. -/
@[reassoc (attr := simp)]
lemma homotopyCofiber_inr_comp_wangMappingConeMap :
    HomologicalComplex.homotopyCofiber.inr (wangEndomorphism φ R) ≫
      wangMappingConeMap φ R = fibreInclusionChainMap φ R := by
  simp [wangMappingConeMap]

/-- On the suspended fibre summand, the Wang mapping-cone map is the negative of the canonical
monodromy homotopy. -/
@[reassoc (attr := simp)]
lemma homotopyCofiber_inlX_comp_wangMappingConeMap_f (i j : ℕ)
    (hij : (ComplexShape.down ℕ).Rel j i) :
    HomologicalComplex.homotopyCofiber.inlX (wangEndomorphism φ R) i j hij ≫
        (wangMappingConeMap φ R).f j =
      -(singularChainHomotopy φ R).hom i j := by
  simp [wangMappingConeMap]

end WangMappingCone

section Map

variable {G : Type w} [TopologicalSpace G] (ψ : G ≃ₜ G) (g : C(F, G))
  (h : Function.Semiconj g φ ψ)

/-- The map on singular chains induced by a map between the fibres of two mapping tori. -/
noncomputable def fibreChainMap :
    ((singularChainComplexFunctor C).obj R).obj (TopCat.of F) ⟶
      ((singularChainComplexFunctor C).obj R).obj (TopCat.of G) :=
  ((singularChainComplexFunctor C).obj R).map (TopCat.ofHom g)

/-- The fibre chain map is the singular-chain functor applied to the map of fibres. -/
lemma fibreChainMap_def :
    fibreChainMap R g = ((singularChainComplexFunctor C).obj R).map (TopCat.ofHom g) :=
  (rfl)

/-- The map on singular chains induced by a map of mapping tori. -/
noncomputable def mappingTorusChainMap :
    ((singularChainComplexFunctor C).obj R).obj (TopCat.of (TauCeti.MappingTorus φ)) ⟶
      ((singularChainComplexFunctor C).obj R).obj (TopCat.of (TauCeti.MappingTorus ψ)) :=
  ((singularChainComplexFunctor C).obj R).map
    (TopCat.ofHom (TauCeti.MappingTorus.map φ ψ g h))

/-- The mapping-torus chain map is the singular-chain functor applied to the map of mapping
tori. -/
lemma mappingTorusChainMap_def :
    mappingTorusChainMap φ R ψ g h =
      ((singularChainComplexFunctor C).obj R).map
        (TopCat.ofHom (TauCeti.MappingTorus.map φ ψ g h)) :=
  (rfl)

/-- A map intertwining two monodromies gives a commuting square on singular chains. -/
@[reassoc]
lemma monodromyChainMap_comp_fibreChainMap (h : Function.Semiconj g φ ψ) :
    monodromyChainMap φ R ≫ fibreChainMap R g =
      fibreChainMap R g ≫ monodromyChainMap ψ R := by
  rw [monodromyChainMap_def, fibreChainMap_def, monodromyChainMap_def,
    ← Functor.map_comp, ← Functor.map_comp]
  congr 1
  ext x
  exact h x

/-- Fibre inclusion is natural for maps of mapping tori. -/
@[reassoc]
lemma fibreInclusionChainMap_comp_mappingTorusChainMap :
    fibreInclusionChainMap φ R ≫ mappingTorusChainMap φ R ψ g h =
      fibreChainMap R g ≫ fibreInclusionChainMap ψ R := by
  rw [fibreInclusionChainMap_def, mappingTorusChainMap_def, fibreChainMap_def,
    fibreInclusionChainMap_def, ← Functor.map_comp, ← Functor.map_comp]
  congr 1
  exact congrArg TopCat.ofHom (map_comp_incl φ ψ g h)

/-- The fibre chain map intertwines the Wang endomorphisms `id - φ_*` and `id - ψ_*`. -/
@[reassoc]
lemma wangEndomorphism_comp_fibreChainMap (h : Function.Semiconj g φ ψ) :
    wangEndomorphism φ R ≫ fibreChainMap R g =
      fibreChainMap R g ≫ wangEndomorphism ψ R := by
  simp only [wangEndomorphism_def, Preadditive.sub_comp, Preadditive.comp_sub,
    Category.id_comp, Category.comp_id]
  rw [monodromyChainMap_comp_fibreChainMap φ R ψ g h]

/-- The commuting square between the Wang endomorphisms associated to a map intertwining
monodromies. -/
noncomputable def wangArrowHom :
    Arrow.mk (wangEndomorphism φ R) ⟶ Arrow.mk (wangEndomorphism ψ R) :=
  Arrow.homMk' (fibreChainMap R g) (fibreChainMap R g)
    (wangEndomorphism_comp_fibreChainMap φ R ψ g h).symm

section WangMappingCone

variable [HasBinaryBiproducts C]

/-- The map between Wang mapping cones induced by a map intertwining the monodromies. -/
noncomputable def wangMappingConeMapOfSemiconj :
    wangMappingCone φ R ⟶ wangMappingCone ψ R :=
  HomologicalComplex.homotopyCofiber.mapArrowHom
    (wangEndomorphism φ R) (wangEndomorphism ψ R)
    (fun n ↦ ⟨n + 1, by simp⟩) (wangArrowHom φ R ψ g h)

/-- On the unsuspended fibre summand, the induced map of Wang cones is the fibre chain map. -/
@[reassoc (attr := simp)]
lemma homotopyCofiber_inr_comp_wangMappingConeMapOfSemiconj :
    HomologicalComplex.homotopyCofiber.inr (wangEndomorphism φ R) ≫
        wangMappingConeMapOfSemiconj φ R ψ g h =
      fibreChainMap R g ≫
        HomologicalComplex.homotopyCofiber.inr (wangEndomorphism ψ R) := by
  simp [wangMappingConeMapOfSemiconj, wangArrowHom]

/-- On the suspended fibre summand, the induced map of Wang cones is again the fibre chain map. -/
@[reassoc (attr := simp)]
lemma homotopyCofiber_inlX_comp_wangMappingConeMapOfSemiconj_f (i j : ℕ)
    (hij : (ComplexShape.down ℕ).Rel j i) :
    HomologicalComplex.homotopyCofiber.inlX (wangEndomorphism φ R) i j hij ≫
        (wangMappingConeMapOfSemiconj φ R ψ g h).f j =
      (fibreChainMap R g).f i ≫
        HomologicalComplex.homotopyCofiber.inlX (wangEndomorphism ψ R) i j hij := by
  simp [wangMappingConeMapOfSemiconj, wangArrowHom]

end WangMappingCone

end Map

end TauCeti.MappingTorus
