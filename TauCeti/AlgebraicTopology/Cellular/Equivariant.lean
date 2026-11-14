/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.RepresentationTheory.Rep.Basic
public import TauCeti.AlgebraicTopology.Cellular.Augmentation
public import TauCeti.AlgebraicTopology.Cellular.Map
public import TauCeti.RepresentationTheory.Rep.HomologicalComplex

/-!
# Cellular chains with a monoid action

A family of cellular self-maps satisfying the action laws induces representations on cellular
chains. Naturality of the cellular differential assembles these into a complex in `Rep`.
The forgetful isomorphism identifies it with the original cellular chain complex, and
naturality of the cellular augmentation promotes `TauCeti.cellularAugmentation` to an
equivariant augmentation to the trivial representation.

A cellular map intertwining two cellular actions along a monoid homomorphism `φ : G →* H`
induces a chain map from the `G`-equivariant cellular complex to the restriction along `φ`
of the `H`-equivariant cellular complex, preserving the cellular augmentations and
respecting identities, composition, and forgetting the actions.

The maps act on the CW subsets themselves; no extension to their ambient spaces or
compatibility with chosen characteristic maps is required.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 2.2.
* K. S. Brown, *Cohomology of Groups*, GTM 87, Springer, 1982, Section I.4.
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

/-- The cellular augmentation in degree zero as a morphism to the trivial representation. -/
def cellularActionAugmentation :
    Rep.of (cellularActionRepresentation C ρ hcell hone hmul R 0) ⟶ Rep.trivial R G R :=
  Rep.ofHom
    { toLinearMap := (cellularAugmentation C (ModuleCat.of R R)).hom
      isIntertwining' g := LinearMap.ext fun x ↦ by
        rw [LinearMap.comp_apply, LinearMap.comp_apply, Representation.trivial_apply,
          cellularActionRepresentation_apply]
        exact ConcreteCategory.congr_hom
          (cellularChainGroupMap_comp_cellularAugmentation C C (hcell g) (ModuleCat.of R R)) x }

/-- The underlying linear map is the cellular augmentation in degree zero. -/
@[simp]
theorem cellularActionAugmentation_hom_toLinearMap :
    (cellularActionAugmentation C ρ hcell hone hmul R).hom.toLinearMap =
      (cellularAugmentation C (ModuleCat.of R R)).hom := (rfl)

/-- The equivariant cellular augmentation vanishes on the boundaries of `1`-cells. -/
@[reassoc (attr := simp)]
theorem cellularActionDifferential_comp_cellularActionAugmentation :
    cellularActionDifferential C ρ hcell hone hmul R 0 ≫
        cellularActionAugmentation C ρ hcell hone hmul R = 0 := by
  ext x
  exact ConcreteCategory.congr_hom
    (cellularDifferential_comp_cellularAugmentation C (ModuleCat.of R R)) x

/-- The cellular augmentation as a chain map of complexes of representations to the trivial
representation placed in degree zero. -/
def cellularActionComplexAugmentation :
    cellularActionComplex C ρ hcell hone hmul R ⟶
      (ChainComplex.single₀ (Rep R G)).obj (Rep.trivial R G R) :=
  ((cellularActionComplex C ρ hcell hone hmul R).toSingle₀Equiv _).symm
    ⟨eqToHom (cellularActionComplex_X C ρ hcell hone hmul R 0) ≫
      cellularActionAugmentation C ρ hcell hone hmul R, by
        simp [cellularActionComplex_d]⟩

/-- In degree zero the chain augmentation is the equivariant cellular augmentation. -/
@[simp]
theorem cellularActionComplexAugmentation_f_zero :
    (cellularActionComplexAugmentation C ρ hcell hone hmul R).f 0 =
      eqToHom (cellularActionComplex_X C ρ hcell hone hmul R 0) ≫
        cellularActionAugmentation C ρ hcell hone hmul R :=
  ChainComplex.toSingle₀Equiv_symm_apply_f_zero _ _

/-- Forgetting the action in degree zero recovers the module-level cellular augmentation. -/
@[reassoc]
theorem cellularActionComplexForget₂Iso_hom_f_zero_comp_augmentation :
    (cellularActionComplexForget₂Iso C ρ hcell hone hmul R).hom.f 0 ≫
        (forget₂ (Rep R G) (ModuleCat R)).map
          ((cellularActionComplexAugmentation C ρ hcell hone hmul R).f 0) =
      eqToHom (cellularChainComplex_X C (ModuleCat.of R R) 0) ≫
        cellularAugmentation C (ModuleCat.of R R) := by
  have h : (forget₂ (Rep R G) (ModuleCat R)).map
      (cellularActionAugmentation C ρ hcell hone hmul R) =
        cellularAugmentation C (ModuleCat.of R R) := by
    rw [Rep.forget₂_moduleCat_map, cellularActionAugmentation_hom_toLinearMap,
      ModuleCat.ofHom_hom]
  simp [-Rep.forget₂_moduleCat_map, eqToHom_map, h]

end Action

section Map

variable {X Y Z : Type u} [TopologicalSpace X] [T2Space X] [TopologicalSpace Y] [T2Space Y]
  [TopologicalSpace Z] [T2Space Z]
  (C : Set X) [CWComplex C] {G : Type u} [Monoid G]
  {ρ₁ : G → (TopCat.of C ⟶ TopCat.of C)} (hcell₁ : ∀ g, IsCellular C C (ρ₁ g))
  (hone₁ : ρ₁ 1 = 𝟙 _) (hmul₁ : ∀ g g', ρ₁ (g * g') = ρ₁ g' ≫ ρ₁ g)
  (D : Set Y) [CWComplex D] {H : Type u} [Monoid H]
  {ρ₂ : H → (TopCat.of D ⟶ TopCat.of D)} (hcell₂ : ∀ h, IsCellular D D (ρ₂ h))
  (hone₂ : ρ₂ 1 = 𝟙 _) (hmul₂ : ∀ h h', ρ₂ (h * h') = ρ₂ h' ≫ ρ₂ h)
  (φ : G →* H) {f : TopCat.of C ⟶ TopCat.of D} (hf : IsCellular C D f)
  (hcomm : ∀ g, ρ₁ g ≫ f = f ≫ ρ₂ (φ g))
  (R : Type u) [Ring R]

/-- A cellular map intertwining two cellular actions along `φ : G →* H` induces a morphism from
the `G`-representation on cellular chains to the restriction along `φ` of the `H`-representation. -/
def cellularActionRepresentationHom (n : ℕ) :
    Rep.of (cellularActionRepresentation C ρ₁ hcell₁ hone₁ hmul₁ R n) ⟶
      Rep.res φ (Rep.of (cellularActionRepresentation D ρ₂ hcell₂ hone₂ hmul₂ R n)) :=
  Rep.ofHom
    { toLinearMap := (cellularChainGroupMap C D hf (ModuleCat.of R R) n).hom
      isIntertwining' g := by
        have hcomp :
            cellularChainGroupMap C D (IsCellular.comp C C (hcell₁ g) hf)
                (ModuleCat.of R R) n =
              cellularChainGroupMap C D (IsCellular.comp C D hf (hcell₂ (φ g)))
                (ModuleCat.of R R) n := by
          congr 1
          exact hcomm g
        rw [cellularChainGroupMap_comp C C (hcell₁ g) D hf,
          cellularChainGroupMap_comp C D hf D (hcell₂ (φ g))] at hcomp
        simpa only [Rep.res_obj_ρ, MonoidHom.comp_apply, cellularActionRepresentation_apply,
          ModuleCat.hom_comp] using congrArg ModuleCat.Hom.hom hcomp }

/-- The underlying linear map is the cellular chain-group map. -/
@[simp]
theorem cellularActionRepresentationHom_hom_toLinearMap (n : ℕ) :
    (cellularActionRepresentationHom C hcell₁ hone₁ hmul₁ D hcell₂ hone₂ hmul₂ φ hf hcomm R
        n).hom.toLinearMap =
      (cellularChainGroupMap C D hf (ModuleCat.of R R) n).hom := (rfl)

/-- The identity cellular map and identity monoid homomorphism induce the identity morphism on
cellular chain representations. -/
@[simp]
theorem cellularActionRepresentationHom_id
    (hf_id : IsCellular C C (𝟙 (TopCat.of C)))
    (hcomm_id : ∀ g, ρ₁ g ≫ 𝟙 (TopCat.of C) = 𝟙 (TopCat.of C) ≫ ρ₁ (MonoidHom.id G g))
    (n : ℕ) :
    cellularActionRepresentationHom C hcell₁ hone₁ hmul₁ C hcell₁ hone₁ hmul₁
        (MonoidHom.id G) hf_id hcomm_id R n =
      𝟙 (Rep.of (cellularActionRepresentation C ρ₁ hcell₁ hone₁ hmul₁ R n)) := by
  refine Rep.hom_ext <| Representation.IntertwiningMap.ext ?_
  simp

/-- A cellular self-map equal to the identity, over `MonoidHom.id G`, induces the identity
morphism on cellular chain representations. -/
theorem cellularActionRepresentationHom_eq_id
    {f₀ : TopCat.of C ⟶ TopCat.of C} (hf₀ : IsCellular C C f₀)
    (hcomm₀ : ∀ g, ρ₁ g ≫ f₀ = f₀ ≫ ρ₁ (MonoidHom.id G g)) (hf_id : f₀ = 𝟙 _) (n : ℕ) :
    cellularActionRepresentationHom C hcell₁ hone₁ hmul₁ C hcell₁ hone₁ hmul₁
        (MonoidHom.id G) hf₀ hcomm₀ R n =
      𝟙 (Rep.of (cellularActionRepresentation C ρ₁ hcell₁ hone₁ hmul₁ R n)) := by
  subst hf_id
  simp

/-- Composition of equivariant cellular maps induces composition of cellular chain-representation
morphisms, restricting the second map along the first monoid homomorphism. -/
@[reassoc]
theorem cellularActionRepresentationHom_comp
    (E : Set Z) [CWComplex E] {K : Type u} [Monoid K]
    {ρ₃ : K → (TopCat.of E ⟶ TopCat.of E)} (hcell₃ : ∀ k, IsCellular E E (ρ₃ k))
    (hone₃ : ρ₃ 1 = 𝟙 _) (hmul₃ : ∀ k k', ρ₃ (k * k') = ρ₃ k' ≫ ρ₃ k)
    (ψ : H →* K) {f' : TopCat.of D ⟶ TopCat.of E} (hf' : IsCellular D E f')
    (hcomm' : ∀ h, ρ₂ h ≫ f' = f' ≫ ρ₃ (ψ h))
    {f'' : TopCat.of C ⟶ TopCat.of E} (hf_comp : IsCellular C E f'')
    (hcomm_comp : ∀ g, ρ₁ g ≫ f'' = f'' ≫ ρ₃ ((ψ.comp φ) g))
    (hcomp : f'' = f ≫ f') (n : ℕ) :
    cellularActionRepresentationHom C hcell₁ hone₁ hmul₁ E hcell₃ hone₃ hmul₃
        (ψ.comp φ) hf_comp hcomm_comp R n =
      cellularActionRepresentationHom C hcell₁ hone₁ hmul₁ D hcell₂ hone₂ hmul₂
          φ hf hcomm R n ≫
        (Rep.resFunctor φ).map
          (cellularActionRepresentationHom D hcell₂ hone₂ hmul₂ E hcell₃ hone₃ hmul₃
            ψ hf' hcomm' R n) := by
  subst hcomp
  refine Rep.hom_ext <| Representation.IntertwiningMap.ext ?_
  have hfc : hf_comp = IsCellular.comp C D hf hf' := Subsingleton.elim _ _
  simpa only [hfc, cellularActionRepresentationHom_hom_toLinearMap, Rep.hom_comp,
    Representation.IntertwiningMap.comp_toLinearMap, Rep.resMap_hom_toLinearMap,
    ModuleCat.hom_comp] using
    congrArg ModuleCat.Hom.hom (cellularChainGroupMap_comp C D hf E hf' (ModuleCat.of R R) n)

/-- Equivariant cellular chain-group maps commute with the equivariant cellular differential. -/
@[reassoc]
theorem cellularActionRepresentationHom_comp_cellularActionDifferential (n : ℕ) :
    cellularActionRepresentationHom C hcell₁ hone₁ hmul₁ D hcell₂ hone₂ hmul₂
        φ hf hcomm R (n + 1) ≫
      (Rep.resFunctor φ).map (cellularActionDifferential D ρ₂ hcell₂ hone₂ hmul₂ R n) =
    cellularActionDifferential C ρ₁ hcell₁ hone₁ hmul₁ R n ≫
      cellularActionRepresentationHom C hcell₁ hone₁ hmul₁ D hcell₂ hone₂ hmul₂
        φ hf hcomm R n := by
  refine Rep.hom_ext <| Representation.IntertwiningMap.ext ?_
  exact congrArg ModuleCat.Hom.hom
    (cellularChainGroupMap_comp_cellularDifferential C D hf (ModuleCat.of R R) n)

/-- Equivariant cellular maps preserve the cellular augmentation in degree zero. -/
@[reassoc (attr := simp)]
theorem cellularActionRepresentationHom_comp_cellularActionAugmentation :
    cellularActionRepresentationHom C hcell₁ hone₁ hmul₁ D hcell₂ hone₂ hmul₂ φ hf hcomm R 0 ≫
        (Rep.resFunctor φ).map (cellularActionAugmentation D ρ₂ hcell₂ hone₂ hmul₂ R) =
      cellularActionAugmentation C ρ₁ hcell₁ hone₁ hmul₁ R := by
  refine Rep.hom_ext <| Representation.IntertwiningMap.ext ?_
  exact congrArg ModuleCat.Hom.hom
    (cellularChainGroupMap_comp_cellularAugmentation C D hf (ModuleCat.of R R))

/-- A cellular map intertwining two cellular actions along `φ : G →* H` induces a chain map from
the `G`-equivariant cellular complex to the restriction along `φ` of the `H`-equivariant cellular
complex. -/
def cellularActionComplexMap :
    cellularActionComplex C ρ₁ hcell₁ hone₁ hmul₁ R ⟶
      ((Rep.resFunctor φ).mapHomologicalComplex _).obj
        (cellularActionComplex D ρ₂ hcell₂ hone₂ hmul₂ R) :=
  ChainComplex.ofHom
    (fun n ↦
      eqToHom (cellularActionComplex_X C ρ₁ hcell₁ hone₁ hmul₁ R n) ≫
        cellularActionRepresentationHom C hcell₁ hone₁ hmul₁ D hcell₂ hone₂ hmul₂ φ hf hcomm R n ≫
        eqToHom (by rw [Functor.mapHomologicalComplex_obj_X, cellularActionComplex_X]))
    fun n ↦ by
      unfold cellularActionComplex
      simp only [Functor.mapHomologicalComplex_obj_d, ChainComplex.of_d,
        eqToHom_refl, Category.comp_id]
      exact cellularActionRepresentationHom_comp_cellularActionDifferential
        C hcell₁ hone₁ hmul₁ D hcell₂ hone₂ hmul₂ φ hf hcomm R n

/-- In each degree the equivariant cellular chain map is the equivariant cellular chain-group map,
up to the canonical term transports. -/
@[simp]
theorem cellularActionComplexMap_f (n : ℕ) :
    (cellularActionComplexMap C hcell₁ hone₁ hmul₁ D hcell₂ hone₂ hmul₂ φ hf hcomm R).f n =
      eqToHom (cellularActionComplex_X C ρ₁ hcell₁ hone₁ hmul₁ R n) ≫
        cellularActionRepresentationHom C hcell₁ hone₁ hmul₁ D hcell₂ hone₂ hmul₂ φ hf hcomm R n ≫
        eqToHom (by rw [Functor.mapHomologicalComplex_obj_X, cellularActionComplex_X]) := (rfl)

/-- The identity cellular map and identity monoid homomorphism induce the identity chain map on
the equivariant cellular complex. -/
@[simp]
theorem cellularActionComplexMap_id
    (hf_id : IsCellular C C (𝟙 (TopCat.of C)))
    (hcomm_id : ∀ g, ρ₁ g ≫ 𝟙 (TopCat.of C) = 𝟙 (TopCat.of C) ≫ ρ₁ (MonoidHom.id G g)) :
    cellularActionComplexMap C hcell₁ hone₁ hmul₁ C hcell₁ hone₁ hmul₁
        (MonoidHom.id G) hf_id hcomm_id R =
      𝟙 (cellularActionComplex C ρ₁ hcell₁ hone₁ hmul₁ R) := by
  ext n : 1
  simp

/-- A cellular self-map equal to the identity, over `MonoidHom.id G`, induces the identity chain
map on the equivariant cellular complex. -/
theorem cellularActionComplexMap_eq_id
    {f₀ : TopCat.of C ⟶ TopCat.of C} (hf₀ : IsCellular C C f₀)
    (hcomm₀ : ∀ g, ρ₁ g ≫ f₀ = f₀ ≫ ρ₁ (MonoidHom.id G g)) (hf_id : f₀ = 𝟙 _) :
    cellularActionComplexMap C hcell₁ hone₁ hmul₁ C hcell₁ hone₁ hmul₁
        (MonoidHom.id G) hf₀ hcomm₀ R =
      𝟙 (cellularActionComplex C ρ₁ hcell₁ hone₁ hmul₁ R) := by
  subst hf_id
  exact cellularActionComplexMap_id C hcell₁ hone₁ hmul₁ R hf₀ hcomm₀

/-- Equivariant cellular chain maps respect composition, restricting the second map along the
first monoid homomorphism. -/
@[reassoc]
theorem cellularActionComplexMap_comp
    (E : Set Z) [CWComplex E] {K : Type u} [Monoid K]
    {ρ₃ : K → (TopCat.of E ⟶ TopCat.of E)} (hcell₃ : ∀ k, IsCellular E E (ρ₃ k))
    (hone₃ : ρ₃ 1 = 𝟙 _) (hmul₃ : ∀ k k', ρ₃ (k * k') = ρ₃ k' ≫ ρ₃ k)
    (ψ : H →* K) {f' : TopCat.of D ⟶ TopCat.of E} (hf' : IsCellular D E f')
    (hcomm' : ∀ h, ρ₂ h ≫ f' = f' ≫ ρ₃ (ψ h))
    {f'' : TopCat.of C ⟶ TopCat.of E} (hf_comp : IsCellular C E f'')
    (hcomm_comp : ∀ g, ρ₁ g ≫ f'' = f'' ≫ ρ₃ ((ψ.comp φ) g))
    (hcomp : f'' = f ≫ f') :
    cellularActionComplexMap C hcell₁ hone₁ hmul₁ E hcell₃ hone₃ hmul₃
        (ψ.comp φ) hf_comp hcomm_comp R =
      cellularActionComplexMap C hcell₁ hone₁ hmul₁ D hcell₂ hone₂ hmul₂ φ hf hcomm R ≫
        ((Rep.resFunctor φ).mapHomologicalComplex _).map
          (cellularActionComplexMap D hcell₂ hone₂ hmul₂ E hcell₃ hone₃ hmul₃ ψ hf' hcomm' R) := by
  subst hcomp
  ext n : 1
  rw [cellularActionComplexMap_f, HomologicalComplex.comp_f,
    Functor.mapHomologicalComplex_map_f, cellularActionComplexMap_f,
    cellularActionComplexMap_f, (Rep.resFunctor φ).map_comp,
    (Rep.resFunctor φ).map_comp, eqToHom_map, eqToHom_map,
    cellularActionRepresentationHom_comp C hcell₁ hone₁ hmul₁ D hcell₂ hone₂ hmul₂
      φ hf hcomm R E hcell₃ hone₃ hmul₃ ψ hf' hcomm' hf_comp hcomm_comp rfl n]
  dsimp only [Functor.mapHomologicalComplex_obj_X]
  simp [Category.assoc]

/-- Forgetting the actions intertwines `cellularActionComplexMap` with the underlying module
cellular chain map `cellularChainComplexMap`. -/
@[reassoc]
theorem cellularActionComplexForget₂Iso_hom_naturality :
    cellularChainComplexMap C D hf (ModuleCat.of R R) ≫
        (cellularActionComplexForget₂Iso D ρ₂ hcell₂ hone₂ hmul₂ R).hom =
      (cellularActionComplexForget₂Iso C ρ₁ hcell₁ hone₁ hmul₁ R).hom ≫
        ((forget₂ (Rep R G) (ModuleCat R)).mapHomologicalComplex _).map
          (cellularActionComplexMap C hcell₁ hone₁ hmul₁ D hcell₂ hone₂ hmul₂ φ hf hcomm R) ≫
        ((cellularActionComplex D ρ₂ hcell₂ hone₂ hmul₂ R).repResForget₂Iso φ).hom := by
  ext n : 1
  have h : (forget₂ (Rep R G) (ModuleCat R)).map
      (cellularActionRepresentationHom C hcell₁ hone₁ hmul₁ D hcell₂ hone₂ hmul₂ φ hf hcomm R n) =
        cellularChainGroupMap C D hf (ModuleCat.of R R) n := by
    rw [Rep.forget₂_moduleCat_map, cellularActionRepresentationHom_hom_toLinearMap,
      ModuleCat.ofHom_hom]
  simp only [HomologicalComplex.comp_f, cellularChainComplexMap_f,
    cellularActionComplexForget₂Iso_hom_f, Functor.mapHomologicalComplex_map_f,
    cellularActionComplexMap_f, HomologicalComplex.repResForget₂Iso_hom_f,
    Functor.map_comp, eqToHom_map, h]
  dsimp only [Functor.mapHomologicalComplex_obj_X, Rep.res_obj_V]
  simp [Category.assoc]

/-- In degree zero, `cellularActionComplexMap` commutes with the equivariant cellular
augmentations. -/
@[reassoc]
theorem cellularActionComplexMap_f_zero_comp_augmentation :
    (cellularActionComplexMap C hcell₁ hone₁ hmul₁ D hcell₂ hone₂ hmul₂ φ hf hcomm R).f 0 ≫
        (Rep.resFunctor φ).map
          ((cellularActionComplexAugmentation D ρ₂ hcell₂ hone₂ hmul₂ R).f 0) =
      (cellularActionComplexAugmentation C ρ₁ hcell₁ hone₁ hmul₁ R).f 0 := by
  rw [cellularActionComplexMap_f, cellularActionComplexAugmentation_f_zero,
    cellularActionComplexAugmentation_f_zero]
  change _ ≫ (Rep.resFunctor φ).map (Y := Rep.trivial R H R)
      (eqToHom (cellularActionComplex_X D ρ₂ hcell₂ hone₂ hmul₂ R 0) ≫
        cellularActionAugmentation D ρ₂ hcell₂ hone₂ hmul₂ R) =
    (_ : _ ⟶ Rep.trivial R G R)
  rw [(Rep.resFunctor φ).map_comp, eqToHom_map]
  dsimp only [Functor.mapHomologicalComplex_obj_X]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  exact congrArg (eqToHom _ ≫ ·)
    (cellularActionRepresentationHom_comp_cellularActionAugmentation
      C hcell₁ hone₁ hmul₁ D hcell₂ hone₂ hmul₂ φ hf hcomm R)

end Map

end TauCeti
