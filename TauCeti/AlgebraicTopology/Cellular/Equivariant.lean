/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cellular.Map
public import TauCeti.RepresentationTheory.Rep.HomologicalComplex

/-!
# Cellular chains with a monoid action

A family of cellular self-maps satisfying the action laws induces representations on cellular
chains. Naturality of the cellular differential assembles these into a complex in `Rep`.
The forgetful isomorphism identifies it with the original cellular chain complex.

A cellular map intertwining two cellular monoid actions along a monoid homomorphism induces
morphisms of representations in every degree (`TauCeti.cellularActionGroupMap`) and a chain map
into the restricted target complex (`TauCeti.cellularActionComplexMap`), respecting identity,
composition, and the forgetful identifications
(`TauCeti.cellularActionComplexForget₂Iso_hom_naturality`).

The maps act on the CW subset itself; no extension to its ambient space or compatibility with
chosen characteristic maps is required.
-/

public section

noncomputable section

open CategoryTheory Set Topology

namespace TauCeti

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] (C : Set X) [CWComplex C]
  {G : Type u} [Monoid G] (ρ : G → (TopCat.of C ⟶ TopCat.of C))
  (hcell : ∀ g, IsCellular C C (ρ g))
  (hone : ρ 1 = 𝟙 _) (hmul : ∀ g h, ρ (g * h) = ρ h ≫ ρ g)
  (R : Type u) [Ring R]

/-- The representation induced on cellular chains by a cellular action. -/
def cellularActionRepresentation (n : ℕ) :
    Representation R G (cellularChainGroup C (ModuleCat.of R R) n : ModuleCat R) where
  toFun g := (cellularChainGroupMap C C (hcell g) (ModuleCat.of R R) n).hom
  map_one' := by
    simp only [hone, cellularChainGroupMap_id, ModuleCat.hom_id]
    rfl
  map_mul' g h := by
    simpa only [hmul, ModuleCat.hom_comp, Module.End.mul_eq_comp] using
      congrArg ModuleCat.Hom.hom
        (cellularChainGroupMap_comp C C (hcell h) C (hcell g) (ModuleCat.of R R) n)

/-- The action is induced by the given cellular self-map. -/
@[simp]
theorem cellularActionRepresentation_apply (n : ℕ) (g : G) :
    cellularActionRepresentation C ρ hcell hone hmul R n g =
      (cellularChainGroupMap C C (hcell g) (ModuleCat.of R R) n).hom := (rfl)

/-- The cellular differential as a morphism of representations. -/
def cellularActionDifferential (n : ℕ) :
    Rep.of (cellularActionRepresentation C ρ hcell hone hmul R (n + 1)) ⟶
      Rep.of (cellularActionRepresentation C ρ hcell hone hmul R n) :=
  Rep.ofHom
    { toLinearMap := (cellularDifferential C (ModuleCat.of R R) n).hom
      isIntertwining' g := by
        simpa only [cellularActionRepresentation_apply, ModuleCat.hom_comp] using
          congrArg ModuleCat.Hom.hom
            (cellularChainGroupMap_comp_cellularDifferential C C (hcell g)
              (ModuleCat.of R R) n) }

/-- The underlying linear map is the cellular differential. -/
@[simp]
theorem cellularActionDifferential_hom_toLinearMap (n : ℕ) :
    (cellularActionDifferential C ρ hcell hone hmul R n).hom.toLinearMap =
      (cellularDifferential C (ModuleCat.of R R) n).hom := (rfl)

/-- Cellular chains retaining a cellular monoid action. -/
def cellularActionComplex : ChainComplex (Rep R G) ℕ :=
  ChainComplex.of (fun n ↦ Rep.of (cellularActionRepresentation C ρ hcell hone hmul R n))
    (cellularActionDifferential C ρ hcell hone hmul R) fun n ↦ by
      ext x
      exact ConcreteCategory.congr_hom
        (cellularDifferential_comp_cellularDifferential C (ModuleCat.of R R) n) x

/-- The terms of the equivariant cellular complex. -/
@[simp]
theorem cellularActionComplex_X (n : ℕ) :
    (cellularActionComplex C ρ hcell hone hmul R).X n =
      Rep.of (cellularActionRepresentation C ρ hcell hone hmul R n) := (rfl)

/-- Its differential is the equivariant cellular differential. -/
@[simp]
theorem cellularActionComplex_d (n : ℕ) :
    (cellularActionComplex C ρ hcell hone hmul R).d (n + 1) n =
      eqToHom (cellularActionComplex_X C ρ hcell hone hmul R (n + 1)) ≫
        cellularActionDifferential C ρ hcell hone hmul R n ≫
      eqToHom (cellularActionComplex_X C ρ hcell hone hmul R n).symm := by
  -- Proof irrelevance normalizes the reflexive transports without exposing the complex API.
  have h : ∀ m, cellularActionComplex_X C ρ hcell hone hmul R m = rfl :=
    fun _ ↦ Subsingleton.elim _ _
  rw [h (n + 1), h n]
  unfold cellularActionComplex
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  exact ChainComplex.of_d _ _ n

/-- Forgetting the action recovers the geometric cellular chain complex. -/
def cellularActionComplexForget₂Iso :
    cellularChainComplex C (ModuleCat.of R R) ≅
      ((forget₂ (Rep R G) (ModuleCat R)).mapHomologicalComplex _).obj
        (cellularActionComplex C ρ hcell hone hmul R) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n ↦ eqToIso (by
      rw [Functor.mapHomologicalComplex_obj_X, cellularActionComplex_X,
        cellularChainComplex_X]
      rfl))
    fun i j hij ↦ by
      subst i
      simp only [cellularChainComplex_d, Functor.mapHomologicalComplex_obj_d,
        cellularActionComplex_d, eqToIso.hom, Functor.map_comp, eqToHom_map,
        Category.assoc, eqToHom_trans_assoc, eqToHom_trans]
      unfold cellularActionComplex
      simp only [eqToHom_refl, Category.comp_id,
        Rep.forget₂_moduleCat_map, cellularActionDifferential_hom_toLinearMap,
        ModuleCat.ofHom_hom]

/-- Components of the forgetful identification are the canonical cellular-term transports. -/
@[simp]
theorem cellularActionComplexForget₂Iso_hom_f (n : ℕ) :
    (cellularActionComplexForget₂Iso C ρ hcell hone hmul R).hom.f n =
      eqToHom (by
        rw [Functor.mapHomologicalComplex_obj_X, cellularActionComplex_X,
          cellularChainComplex_X]
        rfl) := (rfl)

/-- Inverse components of the forgetful identification are the reverse term transports. -/
@[simp]
theorem cellularActionComplexForget₂Iso_inv_f (n : ℕ) :
    (cellularActionComplexForget₂Iso C ρ hcell hone hmul R).inv.f n =
      eqToHom (by
        rw [Functor.mapHomologicalComplex_obj_X, cellularActionComplex_X,
          cellularChainComplex_X]
        rfl) := (rfl)

section Functoriality

variable {Y : Type u} [TopologicalSpace Y] [T2Space Y] (D : Set Y) [CWComplex D]
  {H : Type u} [Monoid H] (σ : H → (TopCat.of D ⟶ TopCat.of D))
  (hcell' : ∀ h, IsCellular D D (σ h))
  (hone' : σ 1 = 𝟙 _) (hmul' : ∀ g h, σ (g * h) = σ h ≫ σ g)

/-- A cellular map intertwining two cellular monoid actions along a monoid homomorphism induces
a morphism of cellular chain representations, with the target action restricted along that
homomorphism. -/
def cellularActionGroupMap (φ : G →* H) {f : TopCat.of C ⟶ TopCat.of D} (hf : IsCellular C D f)
    (heq : ∀ g, ρ g ≫ f = f ≫ σ (φ g)) (n : ℕ) :
    Rep.of (cellularActionRepresentation C ρ hcell hone hmul R n) ⟶
      Rep.res φ (Rep.of (cellularActionRepresentation D σ hcell' hone' hmul' R n)) :=
  Rep.ofHom
    { toLinearMap := (cellularChainGroupMap C D hf (ModuleCat.of R R) n).hom
      isIntertwining' g := by
        have hfg : cellularChainGroupMap C D (IsCellular.comp C C (hcell g) hf)
            (ModuleCat.of R R) n =
          cellularChainGroupMap C D (IsCellular.comp C D hf (hcell' (φ g)))
            (ModuleCat.of R R) n := by
          congr 1
          exact heq g
        rw [cellularChainGroupMap_comp C C (hcell g) D hf,
          cellularChainGroupMap_comp C D hf D (hcell' (φ g))] at hfg
        simpa only [Rep.res_obj_ρ, MonoidHom.comp_apply,
          cellularActionRepresentation_apply, ModuleCat.hom_comp] using
          congrArg ModuleCat.Hom.hom hfg }

/-- Forgetting equivariance recovers the underlying cellular chain-group map. -/
@[simp]
theorem cellularActionGroupMap_hom_toLinearMap (φ : G →* H) {f : TopCat.of C ⟶ TopCat.of D}
    (hf : IsCellular C D f) (heq : ∀ g, ρ g ≫ f = f ≫ σ (φ g)) (n : ℕ) :
    (cellularActionGroupMap C ρ hcell hone hmul R D σ hcell' hone' hmul' φ hf heq
      n).hom.toLinearMap = (cellularChainGroupMap C D hf (ModuleCat.of R R) n).hom := (rfl)

/-- Equal underlying cellular maps induce equal morphisms of cellular chain representations,
regardless of the cellularity and equivariance witnesses. -/
theorem cellularActionGroupMap_congr (φ : G →* H)
    {f f' : TopCat.of C ⟶ TopCat.of D} (hff' : f = f')
    (hf : IsCellular C D f) (heq : ∀ g, ρ g ≫ f = f ≫ σ (φ g))
    (hf' : IsCellular C D f') (heq' : ∀ g, ρ g ≫ f' = f' ≫ σ (φ g)) (n : ℕ) :
    cellularActionGroupMap C ρ hcell hone hmul R D σ hcell' hone' hmul' φ hf heq n =
      cellularActionGroupMap C ρ hcell hone hmul R D σ hcell' hone' hmul' φ hf' heq' n := by
  subst hff'
  have h1 : hf = hf' := Subsingleton.elim _ _
  subst h1
  rfl

/-- The identity cellular map induces the identity morphism of cellular chain representations. -/
@[simp]
theorem cellularActionGroupMap_id {hf : IsCellular C C (𝟙 _)}
    {heq : ∀ g, ρ g ≫ 𝟙 _ = 𝟙 _ ≫ ρ (MonoidHom.id G g)} (n : ℕ) :
    cellularActionGroupMap C ρ hcell hone hmul R C ρ hcell hone hmul (MonoidHom.id G) hf heq n =
      𝟙 (Rep.of (cellularActionRepresentation C ρ hcell hone hmul R n)) := by
  have hfid : hf = isCellular_id C := Subsingleton.elim _ _
  subst hfid
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  simpa only [cellularActionGroupMap_hom_toLinearMap, Rep.hom_id,
    Representation.IntertwiningMap.toLinearMap_id, ModuleCat.hom_id] using
    congrArg ModuleCat.Hom.hom (cellularChainGroupMap_id C (ModuleCat.of R R) n)

/-- Equivariant cellular chain-group maps respect composition, restricting the second morphism
along the first homomorphism. -/
@[reassoc]
theorem cellularActionGroupMap_comp {Z : Type u} [TopologicalSpace Z] [T2Space Z]
    (E : Set Z) [CWComplex E] {K : Type u} [Monoid K]
    (τ : K → (TopCat.of E ⟶ TopCat.of E)) (hcell'' : ∀ k, IsCellular E E (τ k))
    (hone'' : τ 1 = 𝟙 _) (hmul'' : ∀ g h, τ (g * h) = τ h ≫ τ g)
    (ψ : H →* K) (φ : G →* H)
    {f : TopCat.of C ⟶ TopCat.of D} (hf : IsCellular C D f)
    (heq : ∀ g, ρ g ≫ f = f ≫ σ (φ g))
    {g : TopCat.of D ⟶ TopCat.of E} (hg : IsCellular D E g)
    (heq' : ∀ h, σ h ≫ g = g ≫ τ (ψ h))
    {hfg : IsCellular C E (f ≫ g)}
    {heq'' : ∀ x, ρ x ≫ (f ≫ g) = (f ≫ g) ≫ τ ((ψ.comp φ) x)} (n : ℕ) :
    cellularActionGroupMap C ρ hcell hone hmul R E τ hcell'' hone'' hmul''
        (ψ.comp φ) hfg heq'' n =
      cellularActionGroupMap C ρ hcell hone hmul R D σ hcell' hone' hmul' φ hf heq n ≫
        (Rep.resFunctor φ).map
          (cellularActionGroupMap D σ hcell' hone' hmul' R E τ hcell'' hone'' hmul''
            ψ hg heq' n) := by
  have hcomp : hfg = IsCellular.comp C D hf hg := Subsingleton.elim _ _
  subst hcomp
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  simpa only [cellularActionGroupMap_hom_toLinearMap, Rep.hom_comp,
    Representation.IntertwiningMap.comp_toLinearMap, Rep.resMap_hom_toLinearMap,
    ModuleCat.hom_comp] using
    congrArg ModuleCat.Hom.hom
      (cellularChainGroupMap_comp C D hf E hg (ModuleCat.of R R) n)

/-- A cellular map intertwining two cellular monoid actions along a monoid homomorphism induces
a chain map of equivariant cellular chain complexes, with the target complex restricted along
that homomorphism. -/
def cellularActionComplexMap (φ : G →* H) {f : TopCat.of C ⟶ TopCat.of D} (hf : IsCellular C D f)
    (heq : ∀ g, ρ g ≫ f = f ≫ σ (φ g)) :
    cellularActionComplex C ρ hcell hone hmul R ⟶
      ((Rep.resFunctor φ).mapHomologicalComplex _).obj
        (cellularActionComplex D σ hcell' hone' hmul' R) where
  f n := eqToHom (cellularActionComplex_X C ρ hcell hone hmul R n) ≫
    cellularActionGroupMap C ρ hcell hone hmul R D σ hcell' hone' hmul' φ hf heq n ≫
    eqToHom (by rw [Functor.mapHomologicalComplex_obj_X, cellularActionComplex_X])
  comm' i j hij := by
    subst i
    simp only [Functor.mapHomologicalComplex_obj_d, cellularActionComplex_d,
      Rep.resMap_comp, Rep.resMap_eqToHom, ← Category.assoc]
    rw [cancel_mono]
    simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    apply (cancel_epi (eqToHom (cellularActionComplex_X C ρ hcell hone hmul R (j + 1)))).mpr
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    simpa only [Rep.hom_comp, Representation.IntertwiningMap.comp_toLinearMap,
      Rep.resMap_hom_toLinearMap, cellularActionGroupMap_hom_toLinearMap,
      cellularActionDifferential_hom_toLinearMap, ModuleCat.hom_comp] using
      congrArg ModuleCat.Hom.hom
        (cellularChainGroupMap_comp_cellularDifferential C D hf (ModuleCat.of R R) j)

/-- Components of the equivariant cellular chain map are the degreewise representation maps
between the canonical cellular-chain terms. -/
@[simp]
theorem cellularActionComplexMap_f (φ : G →* H) {f : TopCat.of C ⟶ TopCat.of D}
    (hf : IsCellular C D f) (heq : ∀ g, ρ g ≫ f = f ≫ σ (φ g)) (n : ℕ) :
    (cellularActionComplexMap C ρ hcell hone hmul R D σ hcell' hone' hmul' φ hf heq).f n =
      eqToHom (cellularActionComplex_X C ρ hcell hone hmul R n) ≫
        cellularActionGroupMap C ρ hcell hone hmul R D σ hcell' hone' hmul' φ hf heq n ≫
        eqToHom (by rw [Functor.mapHomologicalComplex_obj_X, cellularActionComplex_X]) := (rfl)

/-- Equal underlying cellular maps induce equal chain maps of equivariant cellular complexes. -/
theorem cellularActionComplexMap_congr (φ : G →* H)
    {f f' : TopCat.of C ⟶ TopCat.of D} (hff' : f = f')
    (hf : IsCellular C D f) (heq : ∀ g, ρ g ≫ f = f ≫ σ (φ g))
    (hf' : IsCellular C D f') (heq' : ∀ g, ρ g ≫ f' = f' ≫ σ (φ g)) :
    cellularActionComplexMap C ρ hcell hone hmul R D σ hcell' hone' hmul' φ hf heq =
      cellularActionComplexMap C ρ hcell hone hmul R D σ hcell' hone' hmul' φ hf' heq' := by
  subst hff'
  have h1 : hf = hf' := Subsingleton.elim _ _
  subst h1
  rfl

/-- The identity cellular map induces the identity chain map of equivariant cellular complexes. -/
@[simp]
theorem cellularActionComplexMap_id {hf : IsCellular C C (𝟙 _)}
    {heq : ∀ g, ρ g ≫ 𝟙 _ = 𝟙 _ ≫ ρ (MonoidHom.id G g)} :
    cellularActionComplexMap C ρ hcell hone hmul R C ρ hcell hone hmul (MonoidHom.id G) hf heq =
      𝟙 (cellularActionComplex C ρ hcell hone hmul R) := by
  ext n : 1
  simp only [cellularActionComplexMap_f, cellularActionGroupMap_id, Category.id_comp,
    HomologicalComplex.id_f, eqToHom_trans, eqToHom_refl]

/-- Equivariant cellular chain maps respect composition, restricting the second map along the
first homomorphism. -/
@[reassoc]
theorem cellularActionComplexMap_comp {Z : Type u} [TopologicalSpace Z] [T2Space Z]
    (E : Set Z) [CWComplex E] {K : Type u} [Monoid K]
    (τ : K → (TopCat.of E ⟶ TopCat.of E)) (hcell'' : ∀ k, IsCellular E E (τ k))
    (hone'' : τ 1 = 𝟙 _) (hmul'' : ∀ g h, τ (g * h) = τ h ≫ τ g)
    (ψ : H →* K) (φ : G →* H)
    {f : TopCat.of C ⟶ TopCat.of D} (hf : IsCellular C D f)
    (heq : ∀ g, ρ g ≫ f = f ≫ σ (φ g))
    {g : TopCat.of D ⟶ TopCat.of E} (hg : IsCellular D E g)
    (heq' : ∀ h, σ h ≫ g = g ≫ τ (ψ h))
    {hfg : IsCellular C E (f ≫ g)}
    {heq'' : ∀ x, ρ x ≫ (f ≫ g) = (f ≫ g) ≫ τ ((ψ.comp φ) x)} :
    cellularActionComplexMap C ρ hcell hone hmul R E τ hcell'' hone'' hmul''
        (ψ.comp φ) hfg heq'' =
      cellularActionComplexMap C ρ hcell hone hmul R D σ hcell' hone' hmul' φ hf heq ≫
        ((Rep.resFunctor φ).mapHomologicalComplex _).map
          (cellularActionComplexMap D σ hcell' hone' hmul' R E τ hcell'' hone'' hmul''
            ψ hg heq') := by
  ext n : 1
  simp only [cellularActionComplexMap_f, HomologicalComplex.comp_f,
    Functor.mapHomologicalComplex_map_f, Rep.resMap_comp, Rep.resMap_eqToHom]
  rw [cellularActionGroupMap_comp C ρ hcell hone hmul R D σ hcell' hone' hmul'
    E τ hcell'' hone'' hmul'' ψ φ hf heq hg heq' (hfg := hfg) (heq'' := heq'') n]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]

/-- Forgetting the group actions identifies the equivariant cellular chain map with the ordinary
geometric cellular chain map. -/
@[reassoc]
theorem cellularActionComplexForget₂Iso_hom_naturality (φ : G →* H)
    {f : TopCat.of C ⟶ TopCat.of D} (hf : IsCellular C D f)
    (heq : ∀ g, ρ g ≫ f = f ≫ σ (φ g)) :
    cellularChainComplexMap C D hf (ModuleCat.of R R) ≫
        (cellularActionComplexForget₂Iso D σ hcell' hone' hmul' R).hom =
      (cellularActionComplexForget₂Iso C ρ hcell hone hmul R).hom ≫
        ((forget₂ (Rep R G) (ModuleCat R)).mapHomologicalComplex _).map
          (cellularActionComplexMap C ρ hcell hone hmul R D σ hcell' hone' hmul' φ hf heq) ≫
        ((cellularActionComplex D σ hcell' hone' hmul' R).repResForget₂Iso φ).hom := by
  ext n : 1
  simp only [HomologicalComplex.comp_f, cellularChainComplexMap_f,
    cellularActionComplexForget₂Iso_hom_f, Functor.mapHomologicalComplex_map_f,
    cellularActionComplexMap_f, HomologicalComplex.repResForget₂Iso_hom_f,
    Functor.map_comp, eqToHom_map, Category.comp_id, Category.assoc,
    eqToHom_trans_assoc, eqToHom_trans]
  unfold cellularActionComplex
  simp only [eqToHom_refl, Category.comp_id, Rep.forget₂_moduleCat_map,
    cellularActionGroupMap_hom_toLinearMap, ModuleCat.ofHom_hom]

end Functoriality

end TauCeti
