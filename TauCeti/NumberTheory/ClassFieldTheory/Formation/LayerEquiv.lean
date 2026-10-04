/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Formation.ArtinMap

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

Everything a layer carries is transported by such an isomorphism: ordinary and Tate cohomology in
the coefficient module (`LayerEquiv.cohomologyIso`, `LayerEquiv.tateCohomologyIso`), Tate
cohomology with trivial integral coefficients (`LayerEquiv.trivialTateCohomologyIso`), the ground
level (`LayerEquiv.groundEquiv`) and the norm quotient (`LayerEquiv.normQuotientEquiv`), and the
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
* `TauCeti.ClassFieldTheory.LayerEquiv.cohomologyIso`,
  `TauCeti.ClassFieldTheory.LayerEquiv.tateCohomologyIso`,
  `TauCeti.ClassFieldTheory.LayerEquiv.trivialTateCohomologyIso`: the induced isomorphisms of
  ordinary cohomology, of Tate cohomology, and of Tate cohomology with trivial coefficients.
* `TauCeti.ClassFieldTheory.LayerEquiv.groundEquiv`,
  `TauCeti.ClassFieldTheory.LayerEquiv.normQuotientEquiv`: the induced isomorphisms of ground
  levels and of norm quotients.
* `TauCeti.ClassFieldTheory.NormalLayer.conjugateLayerEquiv`: conjugation by `g` as a layer
  isomorphism.

## Main statements

* `TauCeti.ClassFieldTheory.LayerEquiv.norm_coeffEquiv`: the isomorphism commutes with the norms.
* `TauCeti.ClassFieldTheory.cupClass_layerEquiv`: cup product with a degree-two class
  is transported.
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

include E in
/-- Isomorphic layers have the same degree. -/
theorem degree_eq : L'.degree = L.degree := by
  rw [NormalLayer.degree_eq_natCard_gal, NormalLayer.degree_eq_natCard_gal,
    Nat.card_congr E.galEquiv.toEquiv]

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

/-- The isomorphism `H^r(U/V, A^V) ≅ H^r(U'/V', A'^{V'})` of Tate cohomology induced by a layer
isomorphism, in every integer degree. -/
def tateCohomologyIso (r : ℤ) : L.TateH F r ≅ L'.TateH F' r :=
  TateCohomology.mapIso E.isIntertwiningMap r

/-- The isomorphism of Tate cohomology induced by a layer isomorphism is the Tate map of its
compatible pair. -/
theorem tateCohomologyIso_hom (r : ℤ) :
    (E.tateCohomologyIso r).hom = TateCohomology.map E.isIntertwiningMap r :=
  TateCohomology.mapIso_hom _ r

/-- **In positive degrees the Tate and ordinary transports agree**, through the identifications
`tateHIsoH` of the two layers. -/
theorem tateCohomologyIso_hom_tateHIsoH_inv (n : ℕ) [NeZero n] (u : L.H F n) :
    (E.tateCohomologyIso n).hom ((L.tateHIsoH F n).inv u) =
      (L'.tateHIsoH F' n).inv ((E.cohomologyIso n).hom u) := by
  refine (ModuleCat.mono_iff_injective (L'.tateHIsoH F' n).hom).1 inferInstance ?_
  rw [Iso.inv_hom_id_apply, tateCohomologyIso_hom, NormalLayer.tateHIsoH_def,
    NormalLayer.tateHIsoH_def]
  -- The Tate map of the pair is, in positive degrees, the change-of-group map of ordinary
  -- cohomology along `galEquiv.symm`, which is how `cohomologyIso` is defined.
  have hm : (TateCohomology.isoGroupCohomology n).hom.app (L'.rep F')
      (TateCohomology.map E.isIntertwiningMap n
        (((TateCohomology.isoGroupCohomology n).app (L.rep F)).inv u)) =
      groupCohomology.map (E.galEquiv.symm : L'.Gal →* L.Gal)
        (Representation.IsIntertwiningMap.ofRes E.isIntertwiningMap)
        n ((TateCohomology.isoGroupCohomology n).hom.app (L.rep F)
          (((TateCohomology.isoGroupCohomology n).app (L.rep F)).inv u)) :=
    ConcreteCategory.congr_hom (TateCohomology.map_comp_isoGroupCohomology_hom
      E.isIntertwiningMap n) _
  refine hm.trans <| (congrArg _ (((TateCohomology.isoGroupCohomology n).app
    (L.rep F)).inv_hom_id_apply u)).trans ?_
  rw [cohomologyIso, groupCohomology.mapIso_hom]
  congr 3
  ext x
  simp

/-- The isomorphism `H^r(U/V, ℤ) ≅ H^r(U'/V', ℤ)` of Tate cohomology with trivial integral
coefficients induced by the isomorphism of Galois groups. -/
def trivialTateCohomologyIso (r : ℤ) : L.TrivialTateH r ≅ L'.TrivialTateH r :=
  TateCohomology.mapIso (e := E.galEquiv)
    (Rep.isIntertwiningMap_trivial ℤ (E.galEquiv : L.Gal →* L'.Gal)) r

/-- The transport of Tate cohomology with trivial coefficients is the Tate map of the pair formed
by the isomorphism of Galois groups and the identity of `ℤ`. -/
theorem trivialTateCohomologyIso_hom (r : ℤ) :
    (E.trivialTateCohomologyIso r).hom =
      TateCohomology.map (e := E.galEquiv)
        (Rep.isIntertwiningMap_trivial ℤ (E.galEquiv : L.Gal →* L'.Gal)) r :=
  TateCohomology.mapIso_hom _ r

/-- **In degree `-2` the transport is the induced isomorphism of abelianized Galois groups**,
under the identifications `H^{-2}(U/V, ℤ) ≃ (U/V)^ab` of the two layers. -/
@[simp]
theorem tateHMinusTwoEquivAbelianization_trivialTateCohomologyIso_apply
    (x : L.TrivialTateH (-2)) :
    L'.tateHMinusTwoEquivAbelianization ((E.trivialTateCohomologyIso (-2)).hom x) =
      E.galEquiv.abelianizationCongr.toAdditive (L.tateHMinusTwoEquivAbelianization x) := by
  rw [trivialTateCohomologyIso_hom, NormalLayer.tateHMinusTwoEquivAbelianization_apply,
    NormalLayer.tateHMinusTwoEquivAbelianization_apply, map_neg, neg_inj]
  exact TateCohomology.HNegTwoAddEquivAbelianization_map _ x

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

/-- **A layer isomorphism commutes with the norms** `N_{U/V}` and `N_{U'/V'}`. -/
theorem norm_coeffEquiv (x : F.level L.top) :
    L'.norm F' (E.coeffEquiv x) = E.groundEquiv (L.norm F x) := by
  refine Subtype.ext ?_
  rw [groundEquiv_apply_coe, NormalLayer.norm_apply_coe]
  have hx : Submodule.inclusion (L.level_ground_le_level_top F) (L.norm F x) =
      (L.rep F).ρ.norm x :=
    Subtype.ext (by simp [Representation.norm])
  have hn := LinearMap.congr_fun (Representation.IsIntertwiningMap.comp_norm E.isIntertwiningMap) x
  rw [LinearMap.comp_apply, LinearMap.comp_apply] at hn
  rw [hx, ← LinearEquiv.coe_coe, hn]
  simp [Representation.norm]

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

/-- **In degree zero the Tate transport is the transport of norm quotients**, through the
identifications `tateHZeroEquivNormQuotient` of the two layers. -/
theorem tateHZeroEquivNormQuotient_tateCohomologyIso_apply (x : L.TateH F 0) :
    L'.tateHZeroEquivNormQuotient F' ((E.tateCohomologyIso 0).hom x) =
      E.normQuotientEquiv (L.tateHZeroEquivNormQuotient F x) := by
  induction x using TateCohomology.H0_induction_on with
  | h y =>
    rw [tateCohomologyIso_hom, TauCeti.TateCohomology.H0π_comp_map_apply]
    simp [groundEquiv, invariantsEquiv]

end LayerEquiv

/-- **Cup product with a degree-two class is transported by a layer isomorphism**: the image of
`x ∪ u` is the cup product of the images of `x` and of `u`, in every degree. -/
@[simp]
theorem cupClass_layerEquiv {F : Formation G} {L : NormalLayer G} {F' : Formation G'}
    {L' : NormalLayer G'} (E : LayerEquiv F L F' L') (u : L.H F 2) (r : ℤ)
    (x : L.TrivialTateH r) :
    (E.tateCohomologyIso (r + 2)).hom (cupClass F L u r x) =
      cupClass F' L' ((E.cohomologyIso 2).hom u) r ((E.trivialTateCohomologyIso r).hom x) := by
  have hφ := E.isIntertwiningMap
  have h₀ := Rep.isIntertwiningMap_trivial (R := ℤ) ℤ (E.galEquiv : L.Gal →* L'.Gal)
  -- The pair commutes with the left unitors `ℤ ⊗ A^V ≅ A^V`.
  have hl := TateCohomology.tateCohomologyFunctor_map_comp_map (h₀.tensor hφ) hφ
    (λ_ (L.rep F)).hom (λ_ (L'.rep F')).hom (TensorProduct.ext' fun n c ↦ by simp) (r + 2)
  simp only [cupClass_apply, ← E.tateCohomologyIso_hom_tateHIsoH_inv 2,
    LayerEquiv.trivialTateCohomologyIso_hom, LayerEquiv.tateCohomologyIso_hom]
  rw [← ModuleCat.comp_apply, hl, ModuleCat.comp_apply]
  exact congrArg _ (TateCohomology.map_cup h₀ hφ r 2 (r + 2) _ x _)

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
  rw [eq_fundamentalClass_iff, hinv, inv_fundamentalClass, E.degree_eq]

/-- **Tate's isomorphism is transported by a layer isomorphism matching the invariant maps**: the
image of `x ∪ u_{U/V}` is the cup product of the image of `x` with `u_{U'/V'}`. -/
theorem tateIso_layerEquiv
    (hinv : ∀ x, cf'.inv L' ((E.cohomologyIso 2).hom x) = cf.inv L x) (r : ℤ)
    (x : L.TrivialTateH r) :
    (E.tateCohomologyIso (r + 2)).hom (cf.tateIso L r x) =
      cf'.tateIso L' r ((E.trivialTateCohomologyIso r).hom x) := by
  simp only [tateIso_apply, cupFundamentalClass_apply, cupClass_layerEquiv,
    fundamentalClass_layerEquiv cf cf' E hinv]

/-- **The Nakayama map is transported by a layer isomorphism matching the invariant maps.** -/
theorem nakayamaNegTwo_layerEquiv
    (hinv : ∀ x, cf'.inv L' ((E.cohomologyIso 2).hom x) = cf.inv L x)
    (σ : Additive (Abelianization L.Gal)) :
    cf'.nakayamaNegTwo L' (E.galEquiv.abelianizationCongr.toAdditive σ) =
      E.normQuotientEquiv (cf.nakayamaNegTwo L σ) := by
  obtain ⟨x, rfl⟩ := L.tateHMinusTwoEquivAbelianization.surjective σ
  rw [nakayamaNegTwo_apply, nakayamaNegTwo_apply, AddEquiv.symm_apply_apply,
    ← E.tateHMinusTwoEquivAbelianization_trivialTateCohomologyIso_apply x,
    AddEquiv.symm_apply_apply, ← tateIso_apply, ← tateIso_apply,
    ← tateIso_layerEquiv cf cf' E hinv (-2) x]
  exact E.tateHZeroEquivNormQuotient_tateCohomologyIso_apply _

/-- **Artin reciprocity is transported by a layer isomorphism matching the invariant maps.** -/
theorem artinEquiv_layerEquiv
    (hinv : ∀ x, cf'.inv L' ((E.cohomologyIso 2).hom x) = cf.inv L x) (y : L.NormQuotient F) :
    cf'.artinEquiv L' (E.normQuotientEquiv y) =
      E.galEquiv.abelianizationCongr.toAdditive (cf.artinEquiv L y) := by
  rw [← nakayamaNegTwo_artinEquiv cf L y, ← nakayamaNegTwo_layerEquiv cf cf' E hinv,
    artinEquiv_nakayamaNegTwo, nakayamaNegTwo_artinEquiv]

/-- **The Artin map is transported by a layer isomorphism matching the invariant maps**: the Artin
symbol in `L'` of the image of `a` is the image under `(U/V)^ab ≃ (U'/V')^ab` of the Artin symbol
of `a` in `L`. -/
theorem artinMap_layerEquiv
    (hinv : ∀ x, cf'.inv L' ((E.cohomologyIso 2).hom x) = cf.inv L x) (a : F.level L.ground) :
    cf'.artinMap L' (E.groundEquiv a) =
      E.galEquiv.abelianizationCongr.toAdditive (cf.artinMap L a) := by
  rw [artinMap_apply, artinMap_apply, ← artinEquiv_layerEquiv cf cf' E hinv]
  simp

end ClassFormation

end TauCeti.ClassFieldTheory
