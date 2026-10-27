/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import TauCeti.AlgebraicGeometry.Cohomology.Module.Base
public import TauCeti.AlgebraicGeometry.Cohomology.OpenImmersion
public import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.Pushforward.Affine
public import TauCeti.CategoryTheory.Sites.SheafCohomology.Cech.Functor
public import TauCeti.Topology.Sheaves.Leray

/-!
# Čech cohomology of quasi-coherent sheaves for affine covers

Let `X` be a locally Noetherian scheme and let `M` be a quasi-coherent sheaf of modules on `X`.
Then `M` has no cohomology in positive degrees on affine opens. So every finite open cover `U` of
`X` whose nonempty finite intersections are affine is a Leray cover for `M`, and by Leray's theorem
(`TauCeti.Topology.homologyCechComplexIsoH`) the Čech cohomology `Hⁿ(U, M)` of the underlying
abelian sheaf of `M` is isomorphic to the cohomology `Hⁿ(X, M)`. When `X` has affine diagonal, for
instance when it is separated, finite intersections of affine opens are affine
(`AlgebraicGeometry.IsAffineOpen.biInf`), so `Hⁿ(X, M)` can be computed from the Čech complex of
any finite affine open cover.

The isomorphism is natural in the quasi-coherent sheaf `M`. In particular it intertwines the map
on Čech cohomology induced by multiplication by a global function `r` on `M` with the action of
`r` on `Hⁿ(X, M)` (`Scheme.Modules.cohomologyModule`), so it is compatible with the module
structures of both sides over the ring of global functions, and hence over any base ring.

## Main declarations

* `AlgebraicGeometry.Scheme.Modules.homologyCechComplexIsoCohomology`: for a finite open cover `U`
  of `X` with affine nonempty finite intersections, `Hⁿ(U, M) ≅ Hⁿ(X, M)` for every `n`;
* `AlgebraicGeometry.Scheme.Modules.homologyMap_comp_homologyCechComplexIsoCohomology_hom`: its
  naturality in `M`;
* `AlgebraicGeometry.Scheme.Modules.homologyCechComplexIsoCohomology_hom_globalSectionsSmul`: its
  compatibility with the action of global functions;
* `AlgebraicGeometry.Scheme.Hom.cohomologyPushforwardIsoOfIsAffineHom`: for an affine morphism
  `f : X ⟶ Y` of locally Noetherian schemes, where `Y` has affine diagonal and a finite affine
  open cover `U`, the isomorphism `Hⁿ(Y, f_* M) ≅ Hⁿ(X, M)` for quasi-coherent `M`;
* `AlgebraicGeometry.Scheme.Hom.cohomologyPushforwardIsoOfIsAffineHom_naturality`: its naturality
  in `M`;
* `AlgebraicGeometry.Scheme.Hom.cohomologyPushforwardBaseLinearEquivOfIsAffineHom`: the same
  isomorphism as a linear equivalence over a base ring.

## Cohomology along affine morphisms

Let `f : X ⟶ Y` be an affine morphism and `U` a finite affine open cover of `Y` whose finite
intersections are affine. The preimages `f⁻¹ U i` form a finite affine open cover of `X` with
affine finite intersections, and the sections of `f_* M` over a finite intersection of members of
`U` are the sections of `M` over its preimage. So the Čech complex of `f_* M` for `U` is the Čech
complex of `M` for `f⁻¹ U` (`TauCeti.CategoryTheory.cechComplexCompIso`), and computing both sides
by Čech cohomology gives `Hⁿ(Y, f_* M) ≅ Hⁿ(X, M)`. This is the computation of cohomology along an
affine morphism suggested by Hartshorne, Exercise III.4.1; it lets finiteness of cohomology be
transferred from `Y` to schemes finite over `Y`. The isomorphism is built from the chosen cover `U`.

## References

* R. Hartshorne, *Algebraic Geometry*, Theorem III.4.5 and Exercise III.4.1.
-/

public section

noncomputable section

open CategoryTheory Limits TopologicalSpace AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

open TauCeti TauCeti.AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} [IsLocallyNoetherian X] {ι : Type u} (U : ι → X.Opens)
  (hU : ∀ s : Finset ι, s.Nonempty → IsAffineOpen (s.inf U))

include hU in
/-- On a locally Noetherian scheme, a quasi-coherent sheaf has no cohomology in positive degrees on
a nonempty finite intersection of members of `U`, which is affine. -/
private lemma subsingleton_cohomologyOn_inf_succ (M : X.Modules) [M.IsQuasicoherent]
    (s : Finset ι) (hs : s.Nonempty) (k : ℕ) : Subsingleton (cohomologyOn M (k + 1) (s.inf U)) :=
  have : IsNoetherianRing Γ(X, s.inf U) := IsLocallyNoetherian.component_noetherian ⟨_, hU s hs⟩
  subsingleton_cohomologyOn_succ_of_isAffineOpen M (hU s hs) k

variable [Finite ι] (hcover : ⨆ i, U i = ⊤)

/-- **Čech cohomology computes the cohomology of a quasi-coherent sheaf.** Let `X` be a locally
Noetherian scheme, `M` a quasi-coherent sheaf of modules on `X`, and `U` a finite family of opens
covering `X` whose nonempty finite intersections are affine, for instance a finite affine open
cover when `X` has affine diagonal. Then the Čech cohomology `Hⁿ(U, M)` of the underlying abelian
sheaf of `M` is isomorphic to `Hⁿ(X, M)`, for every `n`, naturally in `M`
(`homologyMap_comp_homologyCechComplexIsoCohomology_hom`). -/
def homologyCechComplexIsoCohomology (M : X.Modules) [M.IsQuasicoherent] (n : ℕ) :
    ((cechComplexFunctor U).obj
        ((SheafOfModules.toSheaf X.ringCatSheaf).obj M).obj).homology n ≅
      AddCommGrpCat.of (Cohomology M n) :=
  TauCeti.Topology.homologyCechComplexIsoH U hcover _
    (subsingleton_cohomologyOn_inf_succ U hU M) n

/-- The comparison of Čech cohomology for a finite cover with affine intersections with the
cohomology of a quasi-coherent sheaf is natural in the sheaf. -/
@[reassoc]
theorem homologyMap_comp_homologyCechComplexIsoCohomology_hom {M N : X.Modules}
    [M.IsQuasicoherent] [N.IsQuasicoherent] (f : M ⟶ N) (n : ℕ) :
    HomologicalComplex.homologyMap
        ((cechComplexFunctor U).map ((SheafOfModules.toSheaf X.ringCatSheaf).map f).hom) n ≫
        (homologyCechComplexIsoCohomology U hU hcover N n).hom =
      (homologyCechComplexIsoCohomology U hU hcover M n).hom ≫ (cohomologyFunctor X n).map f :=
  TauCeti.Topology.homologyMap_comp_homologyCechComplexIsoH_hom U hcover _ _ _ n

/-- The comparison of Čech cohomology for a finite cover with affine intersections with the
cohomology of a quasi-coherent sheaf `M` is linear over the global functions: it carries the map
on Čech cohomology induced by multiplication by `r` on `M` to scalar multiplication by `r` on
`Hⁿ(X, M)`. -/
theorem homologyCechComplexIsoCohomology_hom_globalSectionsSmul (M : X.Modules)
    [M.IsQuasicoherent] (n : ℕ) (r : Γ(X, ⊤))
    (x : ((cechComplexFunctor U).obj
      ((SheafOfModules.toSheaf X.ringCatSheaf).obj M).obj).homology n) :
    (homologyCechComplexIsoCohomology U hU hcover M n).hom
        (HomologicalComplex.homologyMap ((cechComplexFunctor U).map
          ((SheafOfModules.toSheaf X.ringCatSheaf).map (M.globalSectionsSmul r)).hom) n x) =
      r • (homologyCechComplexIsoCohomology U hU hcover M n).hom x := by
  rw [cohomology_smul]
  exact ConcreteCategory.congr_hom
    (homologyMap_comp_homologyCechComplexIsoCohomology_hom U hU hcover (M.globalSectionsSmul r) n) x

end AlgebraicGeometry.Scheme.Modules

/-! ### Cohomology along affine morphisms -/

namespace AlgebraicGeometry.Scheme.Hom

open TauCeti TauCeti.AlgebraicGeometry.Scheme.Modules Scheme.Modules

variable {X Y : Scheme.{u}} (f : X ⟶ Y) {ι : Type u} (U : ι → Y.Opens)

/-- Preimage under `f` sends a product of opens of `Y` to the product of their preimages: both are
intersections, and preimage commutes with finite intersections. -/
private lemma nonempty_pi_preimage_hom (n : ℕ) (a : Fin (n + 1) → ι) :
    Nonempty ((∏ᶜ fun j ↦ (Opens.map f.base).obj (U (a j))) ⟶
      (Opens.map f.base).obj (∏ᶜ fun j ↦ U (a j))) := by
  refine ⟨homOfLE (le_of_eq ?_)⟩
  -- a finite product of opens is their intersection
  have h {Z : Scheme.{u}} (V : Fin (n + 1) → Z.Opens) : (∏ᶜ V) = Finset.univ.inf V :=
    (CompleteLattice.finite_limit_eq_finset_univ_inf _).trans <| by
      rw [Finset.inf_univ_eq_iInf, Finset.inf_univ_eq_iInf]
      exact discreteEquiv.iInf_comp (g := V)
  rw [h, h]
  exact (map_finset_inf (Opens.comap f.base.hom) _ _).symm

/-- The Čech complex of `f_* M` for the family `U` is the Čech complex of `M` for the family of
preimages `f⁻¹ U i`. -/
private def cechComplexPushforwardIso (M : X.Modules) :
    (cechComplexFunctor U).obj
        ((SheafOfModules.toSheaf Y.ringCatSheaf).obj ((pushforward f).obj M)).obj ≅
      (cechComplexFunctor fun i ↦ f ⁻¹ᵁ U i).obj
        ((SheafOfModules.toSheaf X.ringCatSheaf).obj M).obj :=
  -- the sections of `f_* M` over `V` are by definition the sections of `M` over `f⁻¹ V`
  (TauCeti.CategoryTheory.cechComplexCompIso (Opens.map f.base) U
    ((SheafOfModules.toSheaf X.ringCatSheaf).obj M).obj (nonempty_pi_preimage_hom f U)).symm

/-- The identification of Čech complexes `cechComplexPushforwardIso` is natural in `M`. -/
private lemma cechComplexPushforwardIso_naturality {M N : X.Modules} (α : M ⟶ N) :
    (cechComplexFunctor U).map
          ((SheafOfModules.toSheaf Y.ringCatSheaf).map ((pushforward f).map α)).hom ≫
        (cechComplexPushforwardIso f U N).hom =
      (cechComplexPushforwardIso f U M).hom ≫ (cechComplexFunctor fun i ↦ f ⁻¹ᵁ U i).map
        ((SheafOfModules.toSheaf X.ringCatSheaf).map α).hom :=
  (Iso.eq_inv_comp _).2 <| (Category.assoc _ _ _).symm.trans <| (Iso.comp_inv_eq _).2 <|
    (TauCeti.CategoryTheory.cechComplexFunctor_map_comp_cechComplexCompIso_hom (Opens.map f.base)
      U _ (nonempty_pi_preimage_hom f U) ((SheafOfModules.toSheaf X.ringCatSheaf).map α).hom).symm

variable [IsAffineHom f] [IsLocallyNoetherian X] (hU : ∀ i, IsAffineOpen (U i))

include hU in
/-- On a scheme with affine diagonal, the nonempty finite intersections of members of an affine
family `U` of opens are affine. -/
private lemma isAffineOpen_finset_inf [IsAffineHom (pullback.diagonal (terminal.from Y))]
    (s : Finset ι) (hs : s.Nonempty) : IsAffineOpen (s.inf U) := by
  rw [Finset.inf_eq_iInf]
  exact IsAffineOpen.biInf _ s.finite_toSet hs fun j _ ↦ hU j

include hU in
/-- On the cover of `X` by the preimages under the affine morphism `f` of an affine cover `U` of a
scheme with affine diagonal, a quasi-coherent sheaf has no cohomology in positive degrees on a
nonempty finite intersection: it is the preimage of an affine open, hence affine. -/
private lemma subsingleton_cohomologyOn_inf_preimage_succ
    [IsAffineHom (pullback.diagonal (terminal.from Y))] (M : X.Modules) [M.IsQuasicoherent]
    (s : Finset ι) (hs : s.Nonempty) (k : ℕ) :
    Subsingleton (cohomologyOn M (k + 1) (s.inf fun i ↦ f ⁻¹ᵁ U i)) := by
  have hW : IsAffineOpen (s.inf fun i ↦ f ⁻¹ᵁ U i) := by
    have h : (s.inf fun i ↦ f ⁻¹ᵁ U i) = f ⁻¹ᵁ s.inf U :=
      (map_finset_inf (Opens.comap f.base.hom) s U).symm
    rw [h]
    exact (isAffineOpen_finset_inf U hU s hs).preimage f
  have : IsNoetherianRing Γ(X, s.inf fun i ↦ f ⁻¹ᵁ U i) :=
    IsLocallyNoetherian.component_noetherian ⟨_, hW⟩
  exact subsingleton_cohomologyOn_succ_of_isAffineOpen M hW k

variable [IsAffineHom (pullback.diagonal (terminal.from Y))] [Finite ι] (hcover : ⨆ i, U i = ⊤)

/-- Leray's theorem for the cover of `X` by the preimages `f⁻¹ U i`. -/
private def homologyCechComplexPreimageIsoCohomology (M : X.Modules) [M.IsQuasicoherent]
    (n : ℕ) :
    ((cechComplexFunctor fun i ↦ f ⁻¹ᵁ U i).obj
        ((SheafOfModules.toSheaf X.ringCatSheaf).obj M).obj).homology n ≅
      AddCommGrpCat.of (Cohomology M n) :=
  TauCeti.Topology.homologyCechComplexIsoH (fun i ↦ f ⁻¹ᵁ U i) (f.iSup_preimage_eq_top hcover)
    _ (subsingleton_cohomologyOn_inf_preimage_succ f U hU M) n

/-- Leray's theorem for the cover of `X` by the preimages `f⁻¹ U i` is natural in `M`. -/
private lemma homologyMap_comp_homologyCechComplexPreimageIsoCohomology_hom {M N : X.Modules}
    [M.IsQuasicoherent] [N.IsQuasicoherent] (α : M ⟶ N) (n : ℕ) :
    HomologicalComplex.homologyMap ((cechComplexFunctor fun i ↦ f ⁻¹ᵁ U i).map
          ((SheafOfModules.toSheaf X.ringCatSheaf).map α).hom) n ≫
        (homologyCechComplexPreimageIsoCohomology f U hU hcover N n).hom =
      (homologyCechComplexPreimageIsoCohomology f U hU hcover M n).hom ≫
        (cohomologyFunctor X n).map α :=
  TauCeti.Topology.homologyMap_comp_homologyCechComplexIsoH_hom _ _ _ _ _ n

variable [IsLocallyNoetherian Y]

/-- **Cohomology along an affine morphism.** Let `f : X ⟶ Y` be an affine morphism of locally
Noetherian schemes, where `Y` has affine diagonal (for instance `Y` separated), and let `U` be a
finite family of affine opens covering `Y`. For a quasi-coherent sheaf `M` on `X`, the cohomology
`Hⁿ(Y, f_* M)` of its direct image is isomorphic to `Hⁿ(X, M)`, naturally in `M`
(`cohomologyPushforwardIsoOfIsAffineHom_naturality`). Both sides are computed by the same Čech
complex, for the cover `U` of `Y` and for the cover of `X` by the preimages `f⁻¹ U i`. -/
def cohomologyPushforwardIsoOfIsAffineHom (M : X.Modules) [M.IsQuasicoherent] (n : ℕ) :
    AddCommGrpCat.of (Cohomology ((pushforward f).obj M) n) ≅
      AddCommGrpCat.of (Cohomology M n) :=
  (homologyCechComplexIsoCohomology U (isAffineOpen_finset_inf U hU) hcover
      ((pushforward f).obj M) n).symm ≪≫
    HomologicalComplex.homologyMapIso (cechComplexPushforwardIso f U M) n ≪≫
    homologyCechComplexPreimageIsoCohomology f U hU hcover M n

/-- The cohomology comparison along an affine morphism commutes with maps of quasi-coherent
coefficient sheaves. -/
@[reassoc]
theorem cohomologyPushforwardIsoOfIsAffineHom_naturality {M N : X.Modules} [M.IsQuasicoherent]
    [N.IsQuasicoherent] (α : M ⟶ N) (n : ℕ) :
    (cohomologyFunctor Y n).map ((pushforward f).map α) ≫
        (cohomologyPushforwardIsoOfIsAffineHom f U hU hcover N n).hom =
      (cohomologyPushforwardIsoOfIsAffineHom f U hU hcover M n).hom ≫
        (cohomologyFunctor X n).map α := by
  -- each of the three comparisons composing the isomorphism is natural
  have hY := homologyMap_comp_homologyCechComplexIsoCohomology_hom U
    (isAffineOpen_finset_inf U hU) hcover ((pushforward f).map α) n
  have hC := congrArg (HomologicalComplex.homologyMap · n)
    (cechComplexPushforwardIso_naturality f U α)
  have hX := homologyMap_comp_homologyCechComplexPreimageIsoCohomology_hom f U hU hcover α n
  simp only [HomologicalComplex.homologyMap_comp] at hC
  simp only [cohomologyPushforwardIsoOfIsAffineHom, Iso.trans_hom, Iso.symm_hom,
    HomologicalComplex.homologyMapIso_hom]
  -- The cohomology groups appear both as `AddCommGrpCat.of (Cohomology M n)` and as objects of
  -- `cohomologyFunctor`, which agree only up to unfolding, so the reassociations are terms.
  refine Eq.trans ?_ (Category.assoc _ _ _).symm
  refine (Iso.eq_inv_comp _).2 ?_
  exact (Category.assoc _ _ _).symm.trans <| (hY.symm =≫ _).trans <|
    (Category.assoc _ _ _).trans <| (_ ≫= Iso.hom_inv_id_assoc _ _).trans <|
    (Category.assoc _ _ _).symm.trans <| (hC =≫ _).trans <| (Category.assoc _ _ _).trans <|
    (_ ≫= hX).trans (Category.assoc _ _ _).symm

/-- The cohomology comparison along an affine morphism carries the action of a global function on
`Y` to the action of its pullback along `f`. -/
lemma cohomologyPushforwardIsoOfIsAffineHom_hom_smul (M : X.Modules) [M.IsQuasicoherent] (n : ℕ)
    (r : Γ(Y, ⊤)) (x : Cohomology ((pushforward f).obj M) n) :
    (cohomologyPushforwardIsoOfIsAffineHom f U hU hcover M n).hom (r • x) =
      f.appTop r • (cohomologyPushforwardIsoOfIsAffineHom f U hU hcover M n).hom x := by
  have h := ConcreteCategory.congr_hom (cohomologyPushforwardIsoOfIsAffineHom_naturality f U hU
    hcover (M.globalSectionsSmul (f.appTop r)) n) x
  rw [pushforward_map_globalSectionsSmul] at h
  -- The functor objects are definitionally the displayed cohomology groups, but rewriting
  -- their concrete-category composites requires unfolding the functor-object wrappers.
  erw [AddCommGrpCat.comp_apply, AddCommGrpCat.comp_apply] at h
  rw [cohomology_smul, cohomology_smul]
  exact h

section BaseRing

variable (R : Type u) [CommRing R] [X.Over (Spec (.of R))] [Y.Over (Spec (.of R))]
  [f.IsOver (Spec (.of R))]

/-- **Cohomology along an affine morphism, over a base ring.** For an affine morphism `f` over a
commutative ring `R`, the comparison `Hⁿ(Y, f_* M) ≅ Hⁿ(X, M)` of
`cohomologyPushforwardIsoOfIsAffineHom` is `R`-linear. -/
def cohomologyPushforwardBaseLinearEquivOfIsAffineHom (M : X.Modules) [M.IsQuasicoherent]
    (n : ℕ) : Cohomology ((pushforward f).obj M) n ≃ₗ[R] Cohomology M n where
  __ := (cohomologyPushforwardIsoOfIsAffineHom f U hU hcover M n).addCommGroupIsoToAddEquiv
  map_smul' r x := by
    have hr : f.appTop (baseRingToGlobalSections R Y r) = baseRingToGlobalSections R X r := by
      rw [baseRingToGlobalSections_apply, baseRingToGlobalSections_apply,
        ← CommRingCat.comp_apply, ← comp_appTop, HomIsOver.comp_over]
    -- The inherited `toFun` field must be identified with the isomorphism's forward map
    -- before applying its scalar-compatibility lemma.
    change (cohomologyPushforwardIsoOfIsAffineHom f U hU hcover M n).hom (r • x) =
      r • (cohomologyPushforwardIsoOfIsAffineHom f U hU hcover M n).hom x
    simp only [base_smul_cohomology]
    rw [cohomologyPushforwardIsoOfIsAffineHom_hom_smul, hr]

@[simp]
lemma cohomologyPushforwardBaseLinearEquivOfIsAffineHom_apply (M : X.Modules) [M.IsQuasicoherent]
    (n : ℕ) (x : Cohomology ((pushforward f).obj M) n) :
    cohomologyPushforwardBaseLinearEquivOfIsAffineHom f U hU hcover R M n x =
      (cohomologyPushforwardIsoOfIsAffineHom f U hU hcover M n).hom x :=
  (rfl)

@[simp]
lemma cohomologyPushforwardBaseLinearEquivOfIsAffineHom_symm_apply (M : X.Modules)
    [M.IsQuasicoherent] (n : ℕ) (x : Cohomology M n) :
    (cohomologyPushforwardBaseLinearEquivOfIsAffineHom f U hU hcover R M n).symm x =
      (cohomologyPushforwardIsoOfIsAffineHom f U hU hcover M n).inv x :=
  (rfl)

end BaseRing

end AlgebraicGeometry.Scheme.Hom
