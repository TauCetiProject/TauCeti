/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cellular.Map
public import TauCeti.RepresentationTheory.Rep.HomologicalComplex
import TauCeti.RepresentationTheory.Rep.Res

/-!
# Cellular chains with a monoid action

A family of cellular self-maps satisfying the action laws induces representations on cellular
chains. Naturality of the cellular differential assembles these into a complex in `Rep`.
The forgetful isomorphism identifies it with the original cellular chain complex.

A cellular map between two such CW subsets that intertwines the source action with the target
action along a monoid homomorphism `φ` induces intertwining maps in every degree, assembling
into a chain map to the restricted target complex. Forgetting the action recovers the ordinary
`cellularChainComplexMap`, up to `HomologicalComplex.repResForget₂Iso`.

The maps act on the CW subsets themselves; no extension to their ambient spaces or compatibility
with chosen characteristic maps is required.

## References

* A. Hatcher, *Algebraic Topology*, Section 2.2.
* K. S. Brown, *Cohomology of Groups*, Springer, 1982, Section I.4.
-/

public section

noncomputable section

open CategoryTheory Set Topology

namespace TauCeti

universe u

section Action

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

end Action

section Map

variable {X Y : Type u} [TopologicalSpace X] [T2Space X] [TopologicalSpace Y] [T2Space Y]
  (C : Set X) [CWComplex C] {G : Type u} [Monoid G]
  (ρ : G → (TopCat.of C ⟶ TopCat.of C)) (hcell : ∀ g, IsCellular C C (ρ g))
  (hone : ρ 1 = 𝟙 _) (hmul : ∀ g h, ρ (g * h) = ρ h ≫ ρ g)
  (C' : Set Y) [CWComplex C'] {H : Type u} [Monoid H]
  (ρ' : H → (TopCat.of C' ⟶ TopCat.of C')) (hcell' : ∀ h, IsCellular C' C' (ρ' h))
  (hone' : ρ' 1 = 𝟙 _) (hmul' : ∀ h₁ h₂, ρ' (h₁ * h₂) = ρ' h₂ ≫ ρ' h₁)
  {φ : G →* H} {f : TopCat.of C ⟶ TopCat.of C'}
  (hf : IsCellular C C' f) (hequiv : ∀ g, ρ g ≫ f = f ≫ ρ' (φ g))
  (R : Type u) [Ring R]

/-- A cellular map equivariant along a monoid homomorphism induces a morphism of cellular
representations in each degree, with the target action restricted along the homomorphism. -/
def cellularActionRepresentationMap (n : ℕ) :
    Rep.of (cellularActionRepresentation C ρ hcell hone hmul R n) ⟶
      Rep.res φ (Rep.of (cellularActionRepresentation C' ρ' hcell' hone' hmul' R n)) :=
  Rep.ofHom
    { toLinearMap := (cellularChainGroupMap C C' hf (ModuleCat.of R R) n).hom
      isIntertwining' g := by
        have hcomm :
            cellularChainGroupMap C C (hcell g) (ModuleCat.of R R) n ≫
                cellularChainGroupMap C C' hf (ModuleCat.of R R) n =
              cellularChainGroupMap C C' hf (ModuleCat.of R R) n ≫
                cellularChainGroupMap C' C' (hcell' (φ g)) (ModuleCat.of R R) n := by
          rw [← cellularChainGroupMap_comp, ← cellularChainGroupMap_comp]
          congr 1
          exact hequiv g
        simpa only [Rep.res_obj_ρ, MonoidHom.comp_apply, Rep.of_ρ,
          cellularActionRepresentation_apply, ModuleCat.hom_comp] using
          congrArg ModuleCat.Hom.hom hcomm }

/-- Forgetting equivariance recovers the underlying cellular chain-group map. -/
@[simp]
theorem cellularActionRepresentationMap_hom_toLinearMap (n : ℕ) :
    (cellularActionRepresentationMap C ρ hcell hone hmul C' ρ' hcell' hone' hmul'
      hf hequiv R n).hom.toLinearMap =
      (cellularChainGroupMap C C' hf (ModuleCat.of R R) n).hom := (rfl)

/-- Degreewise representation maps intertwine the equivariant cellular differentials. -/
@[reassoc]
theorem cellularActionRepresentationMap_comp_differential (n : ℕ) :
    cellularActionRepresentationMap C ρ hcell hone hmul C' ρ' hcell' hone' hmul'
        hf hequiv R (n + 1) ≫
      (Rep.resFunctor φ).map (cellularActionDifferential C' ρ' hcell' hone' hmul' R n) =
    cellularActionDifferential C ρ hcell hone hmul R n ≫
      cellularActionRepresentationMap C ρ hcell hone hmul C' ρ' hcell' hone' hmul'
        hf hequiv R n := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  ext x
  simp only [Rep.hom_comp, Representation.IntertwiningMap.comp_toLinearMap,
    Rep.resMap_hom_toLinearMap, cellularActionDifferential_hom_toLinearMap,
    cellularActionRepresentationMap_hom_toLinearMap, LinearMap.comp_apply]
  exact ConcreteCategory.congr_hom
    (cellularChainGroupMap_comp_cellularDifferential C C' hf (ModuleCat.of R R) n) x

/-- A cellular map equivariant along a monoid homomorphism induces a chain map of equivariant
cellular complexes, with the target complex restricted along the homomorphism. -/
def cellularActionComplexMap :
    cellularActionComplex C ρ hcell hone hmul R ⟶
      ((Rep.resFunctor φ).mapHomologicalComplex _).obj
        (cellularActionComplex C' ρ' hcell' hone' hmul' R) where
  f n :=
    eqToHom (cellularActionComplex_X C ρ hcell hone hmul R n) ≫
      cellularActionRepresentationMap C ρ hcell hone hmul C' ρ' hcell' hone' hmul'
        hf hequiv R n ≫
      (Rep.resFunctor φ).map
        (eqToHom (cellularActionComplex_X C' ρ' hcell' hone' hmul' R n).symm)
  comm' i j hij := by
    subst i
    simp only [Functor.mapHomologicalComplex_obj_d, cellularActionComplex_d,
      Rep.resMap_comp, Rep.resMap_eqToHom, Category.assoc, eqToHom_trans_assoc,
      eqToHom_refl, Category.id_comp,
      cellularActionRepresentationMap_comp_differential_assoc]

/-- Components of the equivariant cellular chain map are the degreewise representation maps,
up to the canonical term transports. -/
@[simp]
theorem cellularActionComplexMap_f (n : ℕ) :
    (cellularActionComplexMap C ρ hcell hone hmul C' ρ' hcell' hone' hmul' hf hequiv R).f n =
      eqToHom (cellularActionComplex_X C ρ hcell hone hmul R n) ≫
        cellularActionRepresentationMap C ρ hcell hone hmul C' ρ' hcell' hone' hmul'
          hf hequiv R n ≫
        (Rep.resFunctor φ).map
          (eqToHom (cellularActionComplex_X C' ρ' hcell' hone' hmul' R n).symm) := (rfl)

/-- Forgetting the monoid action intertwines the equivariant cellular chain map with the
ordinary geometric cellular chain map. -/
@[reassoc]
theorem cellularActionComplexForget₂Iso_hom_naturality :
    cellularChainComplexMap C C' hf (ModuleCat.of R R) ≫
        (cellularActionComplexForget₂Iso C' ρ' hcell' hone' hmul' R).hom =
      (cellularActionComplexForget₂Iso C ρ hcell hone hmul R).hom ≫
        ((forget₂ (Rep R G) (ModuleCat R)).mapHomologicalComplex _).map
          (cellularActionComplexMap C ρ hcell hone hmul C' ρ' hcell' hone' hmul'
            hf hequiv R) ≫
        ((cellularActionComplex C' ρ' hcell' hone' hmul' R).repResForget₂Iso φ).hom := by
  ext n : 1
  simp only [HomologicalComplex.comp_f, cellularChainComplexMap_f,
    cellularActionComplexForget₂Iso_hom_f, Functor.mapHomologicalComplex_map_f,
    cellularActionComplexMap_f, HomologicalComplex.repResForget₂Iso_hom_f,
    Functor.map_comp, Rep.resMap_eqToHom, eqToHom_map, Category.assoc,
    Category.comp_id, eqToHom_trans_assoc, eqToHom_trans]
  simp only [Rep.forget₂_moduleCat_map,
    cellularActionRepresentationMap_hom_toLinearMap, ModuleCat.ofHom_hom]

/-- Inverse form of forgetful compatibility for an equivariant cellular chain map. -/
@[reassoc]
theorem cellularActionComplexForget₂Iso_inv_naturality :
    ((forget₂ (Rep R G) (ModuleCat R)).mapHomologicalComplex _).map
        (cellularActionComplexMap C ρ hcell hone hmul C' ρ' hcell' hone' hmul'
          hf hequiv R) ≫
      ((cellularActionComplex C' ρ' hcell' hone' hmul' R).repResForget₂Iso φ).hom ≫
      (cellularActionComplexForget₂Iso C' ρ' hcell' hone' hmul' R).inv =
    (cellularActionComplexForget₂Iso C ρ hcell hone hmul R).inv ≫
      cellularChainComplexMap C C' hf (ModuleCat.of R R) := by
  rw [← Category.assoc]
  exact (CommSq.mk (cellularActionComplexForget₂Iso_hom_naturality C ρ hcell hone hmul
    C' ρ' hcell' hone' hmul' hf hequiv R)).vert_inv.w

/-- Equal equivariant cellular maps induce the same morphism on cellular representations,
regardless of the cellularity and equivariance proofs. -/
theorem cellularActionRepresentationMap_congr {f' : TopCat.of C ⟶ TopCat.of C'}
    (hff' : f = f') (hf' : IsCellular C C' f')
    (hequiv' : ∀ g, ρ g ≫ f' = f' ≫ ρ' (φ g)) (n : ℕ) :
    cellularActionRepresentationMap C ρ hcell hone hmul C' ρ' hcell' hone' hmul'
      hf hequiv R n =
      cellularActionRepresentationMap C ρ hcell hone hmul C' ρ' hcell' hone' hmul'
        hf' hequiv' R n := by
  subst hff'
  rfl

/-- Equal equivariant cellular maps induce the same chain map on cellular complexes,
regardless of the cellularity and equivariance proofs. -/
theorem cellularActionComplexMap_congr {f' : TopCat.of C ⟶ TopCat.of C'}
    (hff' : f = f') (hf' : IsCellular C C' f')
    (hequiv' : ∀ g, ρ g ≫ f' = f' ≫ ρ' (φ g)) :
    cellularActionComplexMap C ρ hcell hone hmul C' ρ' hcell' hone' hmul'
      hf hequiv R =
      cellularActionComplexMap C ρ hcell hone hmul C' ρ' hcell' hone' hmul'
        hf' hequiv' R := by
  subst hff'
  rfl

end Map

section Functoriality

variable {X : Type u} [TopologicalSpace X] [T2Space X]
  (C : Set X) [CWComplex C] {G : Type u} [Monoid G]
  (ρ : G → (TopCat.of C ⟶ TopCat.of C)) (hcell : ∀ g, IsCellular C C (ρ g))
  (hone : ρ 1 = 𝟙 _) (hmul : ∀ g h, ρ (g * h) = ρ h ≫ ρ g)

/-- The identity cellular map induces the identity on each cellular representation, regardless
of the proofs of cellularity and equivariance. -/
@[simp]
theorem cellularActionRepresentationMap_id
    (hf : IsCellular C C (𝟙 (TopCat.of C)))
    (hequiv : ∀ g, ρ g ≫ 𝟙 _ = 𝟙 _ ≫ ρ (MonoidHom.id G g))
    (R : Type u) [Ring R] (n : ℕ) :
    cellularActionRepresentationMap C ρ hcell hone hmul C ρ hcell hone hmul
      (φ := MonoidHom.id G) hf hequiv R n = 𝟙 _ := by
  have hhf : hf = isCellular_id C := Subsingleton.elim _ _
  subst hhf
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  simp only [cellularActionRepresentationMap_hom_toLinearMap, cellularChainGroupMap_id,
    ModuleCat.hom_id, Rep.hom_id]
  rfl

/-- The identity cellular map induces the identity chain map on the equivariant cellular
complex, regardless of the proofs of cellularity and equivariance. -/
@[simp]
theorem cellularActionComplexMap_id
    (hf : IsCellular C C (𝟙 (TopCat.of C)))
    (hequiv : ∀ g, ρ g ≫ 𝟙 _ = 𝟙 _ ≫ ρ (MonoidHom.id G g))
    (R : Type u) [Ring R] :
    cellularActionComplexMap C ρ hcell hone hmul C ρ hcell hone hmul
      (φ := MonoidHom.id G) hf hequiv R = 𝟙 (cellularActionComplex C ρ hcell hone hmul R) := by
  ext n : 1
  simp only [cellularActionComplexMap_f, cellularActionRepresentationMap_id,
    Category.id_comp, HomologicalComplex.id_f]
  rw [Rep.resMap_id]
  simp only [eqToHom_trans, eqToHom_refl]

variable {Y Z : Type u} [TopologicalSpace Y] [T2Space Y] [TopologicalSpace Z] [T2Space Z]
  (C' : Set Y) [CWComplex C'] {H : Type u} [Monoid H]
  (ρ' : H → (TopCat.of C' ⟶ TopCat.of C')) (hcell' : ∀ h, IsCellular C' C' (ρ' h))
  (hone' : ρ' 1 = 𝟙 _) (hmul' : ∀ h₁ h₂, ρ' (h₁ * h₂) = ρ' h₂ ≫ ρ' h₁)
  (C'' : Set Z) [CWComplex C''] {K : Type u} [Monoid K]
  (ρ'' : K → (TopCat.of C'' ⟶ TopCat.of C'')) (hcell'' : ∀ k, IsCellular C'' C'' (ρ'' k))
  (hone'' : ρ'' 1 = 𝟙 _) (hmul'' : ∀ k₁ k₂, ρ'' (k₁ * k₂) = ρ'' k₂ ≫ ρ'' k₁)
  {φ : G →* H} {ψ : H →* K}
  {f : TopCat.of C ⟶ TopCat.of C'} (hf : IsCellular C C' f)
  (hequiv : ∀ g, ρ g ≫ f = f ≫ ρ' (φ g))
  {g : TopCat.of C' ⟶ TopCat.of C''} (hg : IsCellular C' C'' g)
  (hgequiv : ∀ h, ρ' h ≫ g = g ≫ ρ'' (ψ h))

/-- Equivariant cellular representation maps respect composition of cellular maps and monoid
homomorphisms, with the second map restricted along the first homomorphism. -/
theorem cellularActionRepresentationMap_comp
    (hfg : IsCellular C C'' (f ≫ g))
    (hfg_equiv : ∀ x, ρ x ≫ (f ≫ g) = (f ≫ g) ≫ ρ'' ((ψ.comp φ) x))
    (R : Type u) [Ring R] (n : ℕ) :
    cellularActionRepresentationMap C ρ hcell hone hmul C'' ρ'' hcell'' hone'' hmul''
      (φ := ψ.comp φ) hfg hfg_equiv R n =
      cellularActionRepresentationMap C ρ hcell hone hmul C' ρ' hcell' hone' hmul'
          hf hequiv R n ≫
        (Rep.resFunctor φ).map
          (cellularActionRepresentationMap C' ρ' hcell' hone' hmul'
            C'' ρ'' hcell'' hone'' hmul'' hg hgequiv R n) := by
  have hhfg : hfg = IsCellular.comp C C' hf hg := Subsingleton.elim _ _
  subst hhfg
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  simpa only [cellularActionRepresentationMap_hom_toLinearMap, Rep.hom_comp,
    Representation.IntertwiningMap.comp_toLinearMap, Rep.resMap_hom_toLinearMap,
    ModuleCat.hom_comp] using
    congrArg ModuleCat.Hom.hom (cellularChainGroupMap_comp C C' hf C'' hg (ModuleCat.of R R) n)

/-- Equivariant cellular chain maps respect composition of cellular maps and monoid
homomorphisms, with the second map restricted along the first homomorphism. -/
@[reassoc]
theorem cellularActionComplexMap_comp
    (hfg : IsCellular C C'' (f ≫ g))
    (hfg_equiv : ∀ x, ρ x ≫ (f ≫ g) = (f ≫ g) ≫ ρ'' ((ψ.comp φ) x))
    (R : Type u) [Ring R] :
    cellularActionComplexMap C ρ hcell hone hmul C'' ρ'' hcell'' hone'' hmul''
      (φ := ψ.comp φ) hfg hfg_equiv R =
      cellularActionComplexMap C ρ hcell hone hmul C' ρ' hcell' hone' hmul'
          hf hequiv R ≫
        ((Rep.resFunctor φ).mapHomologicalComplex _).map
          (cellularActionComplexMap C' ρ' hcell' hone' hmul'
            C'' ρ'' hcell'' hone'' hmul'' hg hgequiv R) := by
  ext n : 1
  simp only [cellularActionComplexMap_f,
    cellularActionRepresentationMap_comp C ρ hcell hone hmul C' ρ' hcell' hone' hmul'
      C'' ρ'' hcell'' hone'' hmul'' hf hequiv hg hgequiv hfg hfg_equiv R n,
    HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
    Rep.resMap_comp, Rep.resMap_eqToHom, Category.assoc, eqToHom_trans_assoc,
    eqToHom_refl, Category.id_comp]

end Functoriality

end TauCeti
