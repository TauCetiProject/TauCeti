/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Formation.Layer.Hom
import TauCeti.RepresentationTheory.Homological.GroupCohomology.Functoriality

/-!
# Isomorphisms of finite normal layers between formations

Let `F` be a formation on `G` and `F'` a formation on `G'`, with finite normal layers `V ◁ U` of
`G` and `V' ◁ U'` of `G'`. A **layer isomorphism** `LayerEquiv F L F' L'` is an isomorphism of
Galois groups `e : U/V ≃* U'/V'` together with an isomorphism of coefficient modules
`φ : A^V ≃ A'^{V'}` that intertwines the two Galois actions along `e`. This is purely
group- and module-theoretic data, not a field isomorphism; in field notation, an isomorphism of a
Galois extension `K/E` with a Galois extension `K'/E'` (living in a different separable closure,
or over a different base field) induces a layer isomorphism once the coefficient modules attached
to the two extensions are identified compatibly. The motivating example is a finite extension
`L/K` of local fields, whose absolute Galois group `G_L` is an open subgroup of `G_K`, so that each
finite Galois extension of `L` is a layer both of the formation of `L` and of that of `K`.
Conjugation of a layer by an element of `G` is another example
(`NormalLayer.conjugateLayerEquiv`).

A layer isomorphism is in particular a layer morphism (`LayerEquiv.toLayerHom`), so everything a
layer morphism acts on is transported by it, and here the transports are isomorphisms: ordinary
and Tate cohomology in the coefficient module (`LayerEquiv.cohomologyIso`,
`LayerEquiv.tateCohomologyIso`), the ground level (`LayerEquiv.groundEquiv`) and the norm quotient
(`LayerEquiv.normQuotientEquiv`). Tate cohomology with trivial integral coefficients is
transported by the isomorphism `LayerHom.trivialTateCohomologyIso` of the underlying morphism. The
transports are compatible with the norm, with cup product, and with the low-degree
identifications of Tate cohomology.

If `F` and `F'` carry class formations whose invariant maps correspond under the isomorphism of
`H²`, then the isomorphism carries the fundamental class to the fundamental class
(`ClassFormation.fundamentalClass_layerEquiv`), so Tate's isomorphism, the Nakayama map, Artin
reciprocity and the Artin map are all transported
(`ClassFormation.tateIso_layerEquiv`, `ClassFormation.nakayamaNegTwo_layerEquiv`,
`ClassFormation.artinEquiv_layerEquiv`, `ClassFormation.artinMap_layerEquiv`). This is how the
Artin map of one class formation is read as an Artin map of another: for a finite extension of
local fields it identifies the local Artin map of the extension with an abstract Artin map of the
formation of the base, once the two invariant maps are compared.

## Main definitions

* `TauCeti.ClassFieldTheory.LayerEquiv`: an isomorphism between a layer of one formation and a
  layer of another.
* `TauCeti.ClassFieldTheory.LayerEquiv.toLayerHom`: the layer morphism underlying a layer
  isomorphism.
* `TauCeti.ClassFieldTheory.LayerEquiv.cohomologyIso`,
  `TauCeti.ClassFieldTheory.LayerEquiv.tateCohomologyIso`: the induced isomorphisms of ordinary
  and of Tate cohomology.
* `TauCeti.ClassFieldTheory.LayerEquiv.groundEquiv`,
  `TauCeti.ClassFieldTheory.LayerEquiv.normQuotientEquiv`: the induced isomorphisms of ground
  levels and of norm quotients.
* `TauCeti.ClassFieldTheory.NormalLayer.conjugateLayerEquiv`: conjugation by `g` as a layer
  isomorphism.

## Main statements

* `TauCeti.ClassFieldTheory.LayerEquiv.norm_coeffEquiv`: the isomorphism commutes with the norms.
* `TauCeti.ClassFieldTheory.ClassFormation.fundamentalClass_layerEquiv`: an isomorphism matching
  the invariant maps matches the fundamental classes.
* `TauCeti.ClassFieldTheory.ClassFormation.artinMap_layerEquiv`: it then carries the Artin symbol
  of `a` to the Artin symbol of the image of `a`.

## References

* E. Artin and J. Tate, *Class Field Theory*, Chapter XIV, §§4–6.
* J.-P. Serre, *Local Fields*, Chapter XI, §3.
-/

public noncomputable section

open CategoryTheory MonoidalCategory Rep
open _root_.groupCohomology

namespace TauCeti.ClassFieldTheory

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G]
  {G' : Type} [Group G'] [TopologicalSpace G'] [IsTopologicalGroup G'] [CompactSpace G']
  [TotallyDisconnectedSpace G']

/-- An **isomorphism from the layer `L` of the formation `F` to the layer `L'` of the formation
`F'`**: an isomorphism of Galois groups and an isomorphism of coefficient modules that intertwines
the Galois actions along it. -/
@[ext]
structure LayerEquiv (F : Formation G) (L : NormalLayer G) (F' : Formation G')
    (L' : NormalLayer G') where
  /-- The isomorphism `U/V ≃* U'/V'` of Galois groups. -/
  galEquiv : L.Gal ≃* L'.Gal
  /-- The isomorphism `A^V ≃ A'^{V'}` of coefficient modules. -/
  coeffEquiv : F.level L.top ≃ₗ[ℤ] F'.level L'.top
  /-- The coefficient isomorphism intertwines the Galois actions along `galEquiv`. -/
  isIntertwiningMap : (L.rep F).ρ.IsIntertwiningMap
    ((L'.rep F').ρ.comp (galEquiv : L.Gal →* L'.Gal))
    (coeffEquiv : F.level L.top →ₗ[ℤ] F'.level L'.top)

namespace LayerEquiv

variable {F : Formation G} {L : NormalLayer G} {F' : Formation G'} {L' : NormalLayer G'}
  (E : LayerEquiv F L F' L')

/-- The coefficient isomorphism of a layer isomorphism intertwines the Galois actions. -/
theorem coeffEquiv_rep_apply (γ : L.Gal) (x : F.level L.top) :
    E.coeffEquiv ((L.rep F).ρ γ x) = (L'.rep F').ρ (E.galEquiv γ) (E.coeffEquiv x) :=
  E.isIntertwiningMap.isIntertwining γ x

/-- The **layer morphism underlying a layer isomorphism**: the same isomorphism of Galois groups,
with the coefficient isomorphism regarded as a homomorphism. -/
def toLayerHom : LayerHom F L F' L' where
  galEquiv := E.galEquiv
  coeffMap := E.coeffEquiv
  isIntertwiningMap := E.isIntertwiningMap

/-- The Galois-group isomorphism of the underlying layer morphism is that of the isomorphism. -/
@[simp]
theorem toLayerHom_galEquiv : E.toLayerHom.galEquiv = E.galEquiv :=
  (rfl)

/-- The coefficient homomorphism of the underlying layer morphism is the coefficient
isomorphism. -/
@[simp]
theorem toLayerHom_coeffMap : E.toLayerHom.coeffMap = (E.coeffEquiv : F.level L.top →ₗ[ℤ] _) :=
  (rfl)

include E in
/-- Isomorphic layers have the same degree. -/
theorem degree_eq : L'.degree = L.degree :=
  E.toLayerHom.degree_eq

/-! ### Cohomology -/

/-- The isomorphism `H^n(U/V, A^V) ≅ H^n(U'/V', A'^{V'})` of ordinary cohomology induced by a layer
isomorphism. -/
def cohomologyIso (n : ℕ) : L.H F n ≅ L'.H F' n :=
  groupCohomology.mapIso E.galEquiv E.coeffEquiv
    (fun γ ↦ LinearMap.ext fun x ↦ E.coeffEquiv_rep_apply γ x) n

/-- The isomorphism of ordinary cohomology induced by a layer isomorphism is Mathlib's
`groupCohomology.mapIso`. -/
theorem cohomologyIso_def (n : ℕ) :
    E.cohomologyIso n = groupCohomology.mapIso E.galEquiv E.coeffEquiv
      (fun γ ↦ LinearMap.ext fun x ↦ E.coeffEquiv_rep_apply γ x) n :=
  (rfl)

/-- The isomorphism of ordinary cohomology induced by a layer isomorphism is the map induced by its
underlying layer morphism. -/
@[simp]
theorem cohomologyIso_hom (n : ℕ) : (E.cohomologyIso n).hom = E.toLayerHom.cohomologyMap n := by
  rw [cohomologyIso_def, groupCohomology.mapIso_hom, LayerHom.cohomologyMap_def]
  exact groupCohomology.map_congr rfl
    (Representation.IsIntertwiningMap.ofRes_hom_toLinearMap E.toLayerHom.isIntertwiningMap).symm n

/-- The image of the class of a cocycle `c` under the isomorphism of second cohomology induced by a
layer isomorphism `E` is the class of the cocycle
`(γ, δ) ↦ E.coeffEquiv (c (E.galEquiv.symm γ, E.galEquiv.symm δ))`. -/
theorem exists_cohomologyIso_hom_H2π (c : cocycles₂ (L.rep F)) :
    ∃ c' : cocycles₂ (L'.rep F'), (E.cohomologyIso 2).hom (H2π _ c) = H2π _ c' ∧
      ∀ γ δ : L'.Gal, c' (γ, δ) = E.coeffEquiv (c (E.galEquiv.symm γ, E.galEquiv.symm δ)) := by
  rw [cohomologyIso_def, groupCohomology.mapIso_hom,
    groupCohomology.H2π_comp_map_apply]
  exact ⟨_, rfl, fun γ δ => rfl⟩

/-- The isomorphism `H^r(U/V, A^V) ≅ H^r(U'/V', A'^{V'})` of Tate cohomology induced by a layer
isomorphism, in every integer degree. -/
def tateCohomologyIso (r : ℤ) : L.TateH F r ≅ L'.TateH F' r :=
  TateCohomology.mapIso E.isIntertwiningMap r

/-- The isomorphism of Tate cohomology induced by a layer isomorphism is the map induced by its
underlying layer morphism. -/
@[simp]
theorem tateCohomologyIso_hom (r : ℤ) :
    (E.tateCohomologyIso r).hom = E.toLayerHom.tateCohomologyMap r :=
  (TateCohomology.mapIso_hom _ r).trans (E.toLayerHom.tateCohomologyMap_def r).symm

/-! ### The ground level and the norm -/

/-- The isomorphism of invariants of the coefficient modules induced by a layer isomorphism. -/
private def invariantsEquiv : (L.rep F).ρ.invariants ≃ₗ[ℤ] (L'.rep F').ρ.invariants :=
  LinearEquiv.ofLinearMap (TateCohomology.mapInvariants E.isIntertwiningMap)
    (TateCohomology.mapInvariants E.isIntertwiningMap.symm)
    (LinearMap.ext fun x ↦ Subtype.ext <| by
      rw [LinearMap.comp_apply, TateCohomology.mapInvariants_apply_coe,
        TateCohomology.mapInvariants_apply_coe]
      exact E.coeffEquiv.apply_symm_apply _)
    (LinearMap.ext fun x ↦ Subtype.ext <| by
      rw [LinearMap.comp_apply, TateCohomology.mapInvariants_apply_coe,
        TateCohomology.mapInvariants_apply_coe]
      exact E.coeffEquiv.symm_apply_apply _)

/-- The isomorphism of invariants is the coefficient isomorphism on underlying elements. -/
@[simp]
private theorem invariantsEquiv_apply_coe (x : (L.rep F).ρ.invariants) :
    ((E.invariantsEquiv x : (L'.rep F').ρ.invariants) : (L'.rep F').V) =
      E.coeffEquiv (x : (L.rep F).V) := by
  rw [invariantsEquiv, LinearEquiv.coe_ofLinearMap, TateCohomology.mapInvariants_apply_coe,
    LinearEquiv.coe_coe]

/-- The inverse isomorphism of invariants is the inverse coefficient isomorphism on underlying
elements. -/
@[simp]
private theorem invariantsEquiv_symm_apply_coe (y : (L'.rep F').ρ.invariants) :
    ((E.invariantsEquiv.symm y : (L.rep F).ρ.invariants) : (L.rep F).V) =
      E.coeffEquiv.symm (y : (L'.rep F').V) := by
  rw [invariantsEquiv, LinearEquiv.symm_ofLinearMap, LinearEquiv.coe_ofLinearMap,
    TateCohomology.mapInvariants_apply_coe, LinearEquiv.coe_coe]

/-- The isomorphism `A^U ≃ A'^{U'}` of ground levels induced by a layer isomorphism: an element of
the ground level is an invariant of the coefficient module, and its image is the image of that
invariant (`groundEquiv_apply_coe`). -/
def groundEquiv : F.level L.ground ≃ₗ[ℤ] F'.level L'.ground :=
  (L.groundLevelEquiv F).symm ≪≫ₗ E.invariantsEquiv ≪≫ₗ L'.groundLevelEquiv F'

-- The `simp` lemmas below state their left-hand sides through `dsimp% only`; see the
-- implementation notes of `Formation/Basic.lean`.
/-- The isomorphism of ground levels is the coefficient isomorphism, applied to the ground level
as a submodule of the top level. -/
@[simp]
theorem groundEquiv_apply_coe (a : F.level L.ground) :
    (dsimp% only ((E.groundEquiv a : F'.level L'.ground) : F'.toRep.V)) =
      E.coeffEquiv (Submodule.inclusion (L.level_ground_le_level_top F) a) := by
  simp only [groundEquiv, LinearEquiv.trans_apply, NormalLayer.groundLevelEquiv_apply_coe]
  rw [invariantsEquiv_apply_coe]
  exact congrArg (fun y ↦ ((E.coeffEquiv y : F'.level L'.top) : F'.toRep.V))
    (Subtype.ext (L.groundLevelEquiv_symm_apply_coe F a))

/-- The inverse isomorphism of ground levels is the inverse coefficient isomorphism, applied to
the ground level as a submodule of the top level. -/
@[simp]
theorem groundEquiv_symm_apply_coe (b : F'.level L'.ground) :
    (dsimp% only ((E.groundEquiv.symm b : F.level L.ground) : F.toRep.V)) =
      E.coeffEquiv.symm (Submodule.inclusion (L'.level_ground_le_level_top F') b) := by
  simp only [groundEquiv, LinearEquiv.symm_trans_apply, LinearEquiv.symm_symm,
    NormalLayer.groundLevelEquiv_apply_coe]
  rw [invariantsEquiv_symm_apply_coe]
  exact congrArg (fun y ↦ ((E.coeffEquiv.symm y : F.level L.top) : F.toRep.V))
    (Subtype.ext (L'.groundLevelEquiv_symm_apply_coe F' b))

-- `dsimp% only` on the left-hand side, as explained in the implementation notes of
-- `Formation/Basic.lean`.
/-- On ground levels, the underlying layer morphism acts as the isomorphism of ground levels. -/
@[simp]
theorem toLayerHom_groundMap (a : F.level L.ground) :
    (dsimp% only (E.toLayerHom.groundMap a)) = E.groundEquiv a :=
  Subtype.ext (by rw [LayerHom.groundMap_apply_coe, groundEquiv_apply_coe, toLayerHom_coeffMap,
    LinearEquiv.coe_coe])

/-- **A layer isomorphism commutes with the norms** `N_{U/V}` and `N_{U'/V'}`. -/
theorem norm_coeffEquiv (x : F.level L.top) :
    L'.norm F' (E.coeffEquiv x) = E.groundEquiv (L.norm F x) := by
  rw [← toLayerHom_groundMap]
  exact E.toLayerHom.norm_coeffMap x

/-- A layer isomorphism carries the norm subgroup of `L` onto the norm subgroup of `L'`. -/
theorem map_normSubgroup_groundEquiv :
    (L.normSubgroup F).map (E.groundEquiv : F.level L.ground →ₗ[ℤ] F'.level L'.ground) =
      L'.normSubgroup F' := by
  ext y
  simp only [Submodule.mem_map, NormalLayer.mem_normSubgroup]
  constructor
  · rintro ⟨z, ⟨x, rfl⟩, rfl⟩
    exact ⟨E.coeffEquiv x, E.norm_coeffEquiv x⟩
  · rintro ⟨w, rfl⟩
    refine ⟨L.norm F (E.coeffEquiv.symm w), ⟨_, rfl⟩, ?_⟩
    rw [LinearEquiv.coe_coe, ← E.norm_coeffEquiv, LinearEquiv.apply_symm_apply]

/-- The isomorphism `A^U / N_{U/V}(A^V) ≃ A'^{U'} / N_{U'/V'}(A'^{V'})` of norm quotients induced
by a layer isomorphism. -/
def normQuotientEquiv : L.NormQuotient F ≃+ L'.NormQuotient F' :=
  (Submodule.Quotient.equiv _ _ E.groundEquiv E.map_normSubgroup_groundEquiv).toAddEquiv

-- `dsimp% only` on the left-hand side, as explained in the implementation notes of
-- `Formation/Basic.lean`.
/-- The isomorphism of norm quotients sends the class of `a` to the class of its image. -/
@[simp]
theorem normQuotientEquiv_mk (a : F.level L.ground) :
    (dsimp% only (E.normQuotientEquiv (Submodule.Quotient.mk a))) =
      Submodule.Quotient.mk (E.groundEquiv a) := by
  simp [normQuotientEquiv]

/-- The inverse isomorphism of norm quotients sends the class of `b` to the class of its inverse
image. -/
@[simp]
theorem normQuotientEquiv_symm_mk (b : F'.level L'.ground) :
    (dsimp% only (E.normQuotientEquiv.symm (Submodule.Quotient.mk b))) =
      Submodule.Quotient.mk (E.groundEquiv.symm b) := by
  simp [normQuotientEquiv]

/-- On norm quotients, the underlying layer morphism acts as the isomorphism of norm quotients. -/
@[simp]
theorem toLayerHom_normQuotientMap (y : L.NormQuotient F) :
    E.toLayerHom.normQuotientMap y = E.normQuotientEquiv y := by
  induction y using Submodule.Quotient.induction_on with
  | H a => rw [LayerHom.normQuotientMap_mk, normQuotientEquiv_mk, toLayerHom_groundMap]

/-- **In degree zero the Tate transport is the transport of norm quotients**, through the
identifications `tateHZeroEquivNormQuotient` of the two layers. -/
theorem tateHZeroEquivNormQuotient_tateCohomologyIso_apply (x : L.TateH F 0) :
    L'.tateHZeroEquivNormQuotient F' ((E.tateCohomologyIso 0).hom x) =
      E.normQuotientEquiv (L.tateHZeroEquivNormQuotient F x) := by
  rw [tateCohomologyIso_hom, E.toLayerHom.tateHZeroEquivNormQuotient_tateCohomologyMap_apply,
    toLayerHom_normQuotientMap]

end LayerEquiv

/-! ### Conjugation -/

/-- **Conjugation by `g` as a layer isomorphism** from `V ◁ U` to `gVg⁻¹ ◁ gUg⁻¹`, within one
formation. -/
def NormalLayer.conjugateLayerEquiv (L : NormalLayer G) (F : Formation G) (g : G) :
    LayerEquiv F L F (L.conjugate g) where
  galEquiv := L.conjugateGalEquiv g
  coeffEquiv := L.conjugateCoefficientEquiv F g
  isIntertwiningMap := L.isIntertwiningMap_conjugateCoefficientEquiv F g

/-- On ordinary cohomology, conjugation as a layer isomorphism is `conjugateCohomologyIso`. -/
theorem NormalLayer.conjugateLayerEquiv_cohomologyIso (L : NormalLayer G) (F : Formation G)
    (g : G) (n : ℕ) :
    (L.conjugateLayerEquiv F g).cohomologyIso n = L.conjugateCohomologyIso F g n := by
  rw [LayerEquiv.cohomologyIso_def, NormalLayer.conjugateCohomologyIso_def]
  rfl

/-! ### Class formations -/

namespace ClassFormation

variable {F : Formation G} {L : NormalLayer G} {F' : Formation G'} {L' : NormalLayer G'}
  (cf : ClassFormation F) (cf' : ClassFormation F') (E : LayerEquiv F L F' L')

/-- **A layer isomorphism matching the invariant maps matches the fundamental classes.** -/
theorem fundamentalClass_layerEquiv
    (hinv : ∀ x, cf'.inv L' ((E.cohomologyIso 2).hom x) = cf.inv L x) :
    (E.cohomologyIso 2).hom (cf.fundamentalClass L) = cf'.fundamentalClass L' := by
  simp only [LayerEquiv.cohomologyIso_hom] at hinv ⊢
  exact fundamentalClass_layerHom cf cf' E.toLayerHom hinv

/-- **Tate's isomorphism is transported by a layer isomorphism matching the invariant maps**: the
image of `x ∪ u_{U/V}` is the cup product of the image of `x` with `u_{U'/V'}`. -/
theorem tateIso_layerEquiv
    (hinv : ∀ x, cf'.inv L' ((E.cohomologyIso 2).hom x) = cf.inv L x) (r : ℤ)
    (x : L.TrivialTateH r) :
    (E.tateCohomologyIso (r + 2)).hom (cf.tateIso L r x) =
      cf'.tateIso L' r ((E.toLayerHom.trivialTateCohomologyIso r).hom x) := by
  have hu := fundamentalClass_layerEquiv cf cf' E hinv
  rw [LayerEquiv.cohomologyIso_hom] at hu
  rw [LayerEquiv.tateCohomologyIso_hom]
  exact tateIso_layerHom cf cf' E.toLayerHom hu r x

/-- **The Nakayama map is transported by a layer isomorphism matching the invariant maps.** -/
theorem nakayamaNegTwo_layerEquiv
    (hinv : ∀ x, cf'.inv L' ((E.cohomologyIso 2).hom x) = cf.inv L x)
    (σ : Additive (Abelianization L.Gal)) :
    cf'.nakayamaNegTwo L' (E.galEquiv.abelianizationCongr.toAdditive σ) =
      E.normQuotientEquiv (cf.nakayamaNegTwo L σ) := by
  have hu := fundamentalClass_layerEquiv cf cf' E hinv
  rw [LayerEquiv.cohomologyIso_hom] at hu
  simpa using nakayamaNegTwo_layerHom cf cf' E.toLayerHom hu σ

/-- **Artin reciprocity is transported by a layer isomorphism matching the invariant maps.** -/
theorem artinEquiv_layerEquiv
    (hinv : ∀ x, cf'.inv L' ((E.cohomologyIso 2).hom x) = cf.inv L x) (y : L.NormQuotient F) :
    cf'.artinEquiv L' (E.normQuotientEquiv y) =
      E.galEquiv.abelianizationCongr.toAdditive (cf.artinEquiv L y) := by
  have hu := fundamentalClass_layerEquiv cf cf' E hinv
  rw [LayerEquiv.cohomologyIso_hom] at hu
  simpa using artinEquiv_layerHom cf cf' E.toLayerHom hu y

/-- **The Artin map is transported by a layer isomorphism matching the invariant maps**: the Artin
symbol in `L'` of the image of `a` is the image under `(U/V)^ab ≃ (U'/V')^ab` of the Artin symbol
of `a` in `L`. -/
theorem artinMap_layerEquiv
    (hinv : ∀ x, cf'.inv L' ((E.cohomologyIso 2).hom x) = cf.inv L x) (a : F.level L.ground) :
    cf'.artinMap L' (E.groundEquiv a) =
      E.galEquiv.abelianizationCongr.toAdditive (cf.artinMap L a) := by
  have hu := fundamentalClass_layerEquiv cf cf' E hinv
  rw [LayerEquiv.cohomologyIso_hom] at hu
  simpa using artinMap_layerHom cf cf' E.toLayerHom hu a

end ClassFormation

end TauCeti.ClassFieldTheory
