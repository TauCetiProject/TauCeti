/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Representation.ProjectiveOrbit.Quotient
public import TauCeti.Algebra.AlgebraicGroup.Representation.ProjectiveOrbit.Action
public import TauCeti.Algebra.AlgebraicGroup.Fppf.Quotient.Homogeneous.Scheme

/-!
# Functoriality and properness descent for projective orbit quotients

Let `G = Spec H` be an affine group scheme of finite type over an algebraically closed field `k`.
When `G` is reduced, Chevalley's coset criterion represents every homogeneous quotient `G/N` by a
projective orbit scheme `Comodule.projectiveOrbitScheme m hm`
(`Comodule.fppfHomogeneousQuotientIsoProjectiveOrbitPoints`).

Combining this representation with the represented-quotient descent API of
`CommHopfAlgCat.representedQuotientMap` yields scheme-level functoriality and properness descent
for projective orbit models of homogeneous quotients:

* **Closedness vs. properness (`isProper_projectiveOrbitToSpec_iff_isClosed`):** For an arbitrary
  finite-type affine group scheme `G` (without reducedness assumptions), the projective orbit
  scheme of a line is proper over `Spec k` if and only if its geometric orbit is closed in the
  ambient projective space, in which case `projectiveOrbitι` is a closed immersion.
* **Compatibility with orbit geometry:** For Chevalley's representing isomorphism
  `fppfHomogeneousQuotientIsoProjectiveOrbitPoints`, the descended quotient projection
  `Spec H ⟶ projectiveOrbitScheme m hm` agrees with `toProjectiveOrbit m hm`, and the descended
  left translation by `g ∈ G(k)` agrees with `projectiveOrbitTranslation m hm g`.
* **Subgroup functoriality (`projectiveOrbitQuotientMap`):** For closed subgroups `P ⊆ Q` defined
  by Hopf ideals `J ≤ I`, any projective-orbit representations of `G/P` and `G/Q` are linked by a
  canonical surjective `k`-scheme morphism `projectiveOrbitQuotientMap hJI eI eJ` compatible with
  identities, composition, canonical comparison isomorphisms (`projectiveOrbitQuotientIso`),
  orbit projections from `Spec H`, and left translations by `G(k)`.
* **Properness descent (`isProper_projectiveOrbitToSpec_of_le`):** If `P ⊆ Q` (`J ≤ I`) and a
  projective orbit representing `G/P` is proper over `Spec k` (equivalently, closed in projective
  space), then any projective orbit representing `G/Q` is also proper over `Spec k` and closed in
  its ambient projective space (`isClosed_range_projectiveOrbitMap_of_le`).

## Main declarations

* `TauCeti.Comodule.instIsSeparatedProjectiveOrbitToSpec`: a projective orbit scheme is separated
  over the base field.
* `TauCeti.Comodule.isClosedImmersion_projectiveOrbitι_of_isProper` and
  `TauCeti.Comodule.isProper_projectiveOrbitToSpec_iff_isClosed`: properness over `Spec k` is
  equivalent to closedness of the geometric orbit in projective space.
* `TauCeti.Comodule.projectiveOrbitQuotientMap`: the `k`-scheme morphism between projective-orbit
  models of `G/P` and `G/Q` induced by `J ≤ I` (`P ⊆ Q`).
* `TauCeti.Comodule.projectiveOrbitQuotientIso`: canonical `k`-scheme isomorphism between two
  projective-orbit models of the same homogeneous quotient `G/N`.
* `TauCeti.Comodule.instSurjectiveProjectiveOrbitQuotientMap`: `projectiveOrbitQuotientMap` is
  surjective when `G` is reduced.
* `TauCeti.Comodule.isProper_projectiveOrbitToSpec_of_le` and
  `TauCeti.Comodule.isClosed_range_projectiveOrbitMap_of_le`: properness and closedness descend
  from `G/P` to `G/Q` for `P ⊆ Q`.

## References

* J. S. Milne, *Algebraic Groups* (2017), Proposition 5.22 and §§7.c–7.f.
* A. Borel, *Linear Algebraic Groups* (2nd ed., 1991), §6.8 and §11.2.
-/

public section

open CategoryTheory AlgebraicGeometry Opposite

namespace TauCeti.Comodule

universe u

section Proper

variable {k H M : Type u} [Field k] [IsAlgClosed k] [CommRing H] [HopfAlgebra k H]
  [Algebra.FiniteType k H] [AddCommGroup M] [Module k M] [Comodule k H M] [Module.Finite k M]

/-- The projective orbit scheme is separated over the base field `k`, without reducedness
assumptions on the group. -/
instance instIsSeparatedProjectiveOrbitToSpec (m : M) (hm : Module.IsUnimodular k m) :
    IsSeparated (projectiveOrbitToSpec (H := H) m hm) := by
  rw [projectiveOrbitToSpec_def]
  infer_instance

/-- If the projective orbit scheme is proper over `Spec k`, its immersion into projective space is
a closed immersion. -/
theorem isClosedImmersion_projectiveOrbitι_of_isProper (m : M) (hm : Module.IsUnimodular k m)
    [IsProper (projectiveOrbitToSpec (H := H) m hm)] :
    IsClosedImmersion (projectiveOrbitι (H := H) m hm) := by
  have hcomp : IsProper (projectiveOrbitι (H := H) m hm ≫
      SymmetricAlgebra.projToSpec k (Module.Dual k M)) := by
    rwa [← projectiveOrbitToSpec_def]
  have : IsProper (projectiveOrbitι (H := H) m hm) :=
    IsProper.of_comp (projectiveOrbitι (H := H) m hm)
      (SymmetricAlgebra.projToSpec k (Module.Dual k M))
  exact IsClosedImmersion.of_isPreimmersion _
    (projectiveOrbitι (H := H) m hm).isClosedMap.isClosed_range

/-- If the projective orbit scheme is proper over `Spec k`, its geometric orbit is closed in the
ambient projective space. -/
theorem isClosed_range_projectiveOrbitMap_of_isProper (m : M) (hm : Module.IsUnimodular k m)
    [IsProper (projectiveOrbitToSpec (H := H) m hm)] :
    IsClosed (Set.range (projectiveOrbitMap (H := H) m hm)) := by
  let _ := isClosedImmersion_projectiveOrbitι_of_isProper (H := H) m hm
  rw [← range_projectiveOrbitι]
  exact (projectiveOrbitι (H := H) m hm).isClosedMap.isClosed_range

/-- **Properness criterion for projective orbits.** Over an algebraically closed field `k`, the
projective orbit scheme of a line under a finite-type affine group scheme is proper over `Spec k`
if and only if the geometric orbit is closed in projective space. -/
theorem isProper_projectiveOrbitToSpec_iff_isClosed (m : M) (hm : Module.IsUnimodular k m) :
    IsProper (projectiveOrbitToSpec (H := H) m hm) ↔
      IsClosed (Set.range (projectiveOrbitMap (H := H) m hm)) :=
  ⟨fun _ ↦ isClosed_range_projectiveOrbitMap_of_isProper (H := H) m hm,
   isProper_projectiveOrbitToSpec_of_isClosed M m hm⟩

end Proper

section QuotientFunctoriality

variable {k : Type u} [Field k] [IsAlgClosed k] {H : _root_.CommHopfAlgCat.{u} k}
  [Algebra.FiniteType k H]

section SingleOrbit

variable {M : Type u} [AddCommGroup M] [Module k M] [Comodule k H M] [Module.Finite k M]

/-- `projectiveOrbitPointsSheaf` agrees with `CommAlgCat.pointsSheaf` of the projective orbit
scheme over `Spec k`. -/
theorem projectiveOrbitPointsSheaf_eq_pointsSheaf (m : M) (hm : Module.IsUnimodular k m) :
    projectiveOrbitPointsSheaf (H := H) m hm =
      CommAlgCat.pointsSheaf (Over.mk (projectiveOrbitToSpec (H := H) m hm)) :=
  ObjectProperty.FullSubcategory.ext (projectiveOrbitPointsSheaf_obj (H := H) m hm)

/-- Canonical identification of `projectiveOrbitPointsSheaf` with `CommAlgCat.pointsSheaf` of the
projective orbit scheme over `Spec k`. -/
noncomputable def projectiveOrbitPointsSheafIsoPointsSheaf
    (m : M) (hm : Module.IsUnimodular k m) :
    projectiveOrbitPointsSheaf (H := H) m hm ≅
      CommAlgCat.pointsSheaf (Over.mk (projectiveOrbitToSpec (H := H) m hm)) :=
  eqToIso (projectiveOrbitPointsSheaf_eq_pointsSheaf (H := H) m hm)

private lemma eqToHom_app_symm_subst.{w} {C : Type*} [Category* C] {F G : C ⥤ Type w}
    (h : F = G) (A : C) (x : G.obj A) :
    (eqToHom h).app A (h.symm ▸ x) = x := by
  subst h
  rfl

private lemma fullSubcategory_eqToIso_hom_hom {C : Type*} [Category* C]
    {P : ObjectProperty C} {X Y : P.FullSubcategory} (h : X = Y) (hobj : X.obj = Y.obj) :
    (eqToIso h).hom.hom = eqToHom hobj := by
  subst h
  simp

private theorem specPointsHomEquiv_toProjectiveOrbit (m : M) (hm : Module.IsUnimodular k m) :
    CommHopfAlgCat.specPointsHomEquiv H (Over.mk (projectiveOrbitToSpec (H := H) m hm))
        (Over.homMk (toProjectiveOrbit (H := H) m hm)
          (toProjectiveOrbit_projectiveOrbitToSpec m hm)) =
      toProjectiveOrbitPoints (H := H) m hm ≫
        (projectiveOrbitPointsSheafIsoPointsSheaf (H := H) m hm).hom.hom := by
  let pOver :
      (Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of k)) ⟶
        Over.mk (projectiveOrbitToSpec (H := H) m hm) :=
    Over.homMk (toProjectiveOrbit (H := H) m hm) (toProjectiveOrbit_projectiveOrbitToSpec m hm)
  let hobj :
      (projectiveOrbitPointsSheaf (H := H) m hm).obj =
        (CommAlgCat.pointsSheaf (Over.mk (projectiveOrbitToSpec (H := H) m hm))).obj :=
    congrArg ObjectProperty.FullSubcategory.obj
      (projectiveOrbitPointsSheaf_eq_pointsSheaf (H := H) m hm)
  have hhom :
      (projectiveOrbitPointsSheafIsoPointsSheaf (H := H) m hm).hom.hom = eqToHom hobj :=
    fullSubcategory_eqToIso_hom_hom
      (projectiveOrbitPointsSheaf_eq_pointsSheaf (H := H) m hm) hobj
  ext ⟨⟨A⟩⟩ ⟨g⟩
  let g' : HopfAlgebra.points (R := k) (H := H) A := g
  apply ULift.ext
  have hlhs := CommHopfAlgCat.specPointsHomEquiv_apply_app_apply H pOver A g'
  have hrhs :
      ((toProjectiveOrbitPoints (H := H) m hm ≫
          (projectiveOrbitPointsSheafIsoPointsSheaf (H := H) m hm).hom.hom).app (op (op A)))
        (ULift.up g') =
        ULift.up (Over.homMk
          (Spec.map (CommRingCat.ofHom g'.ofConv.toRingHom) ≫
            toProjectiveOrbit (H := H) m hm)
          (SpecMap_toProjectiveOrbit_projectiveOrbitToSpec m hm g'.ofConv)) := by
    rw [hhom, NatTrans.comp_app, ConcreteCategory.comp_apply, toProjectiveOrbitPoints_app_apply]
    exact eqToHom_app_symm_subst hobj (op (op A)) _
  refine hlhs.trans ((Over.OverMorphism.ext ?_).trans (congrArg ULift.down hrhs).symm)
  exact congrArg (· ≫ toProjectiveOrbit (H := H) m hm)
    (TauCeti.CommHopfAlgCat.mapMulEquiv_left g')

/-- For Chevalley's representing isomorphism `fppfHomogeneousQuotientIsoProjectiveOrbitPoints`,
the descended quotient projection `Spec H ⟶ projectiveOrbitScheme m hm` is `toProjectiveOrbit`. -/
@[simp]
theorem representedQuotientProjection_fppfHomogeneousQuotientIsoProjectiveOrbitPoints_left
    [_root_.IsReduced H] (I : HopfIdeal k H) (m : M) (hm : Module.IsUnimodular k m)
    (hcoset : ∀ (A : CommAlgCat.{u} k) (g h : HopfAlgebra.points (R := k) (H := H) A),
      (QuotientGroup.mk g : HopfAlgebra.points (R := k) (H := H) A ⧸
          CommHopfAlgCat.quotientPointsSubgroup H I A) = QuotientGroup.mk h ↔
        ∃ c : Aˣ, ∀ φ : Module.Dual k M,
          h.ofConv (matrixCoefficient (C := H) φ m) =
            c * g.ofConv (matrixCoefficient (C := H) φ m)) :
    (CommHopfAlgCat.representedQuotientProjection H I
      (fppfHomogeneousQuotientIsoProjectiveOrbitPoints I m hm hcoset ≪≫
        projectiveOrbitPointsSheafIsoPointsSheaf m hm)).left =
      toProjectiveOrbit (H := H) m hm := by
  suffices h :
      CommHopfAlgCat.representedQuotientProjection H I
        (fppfHomogeneousQuotientIsoProjectiveOrbitPoints I m hm hcoset ≪≫
          projectiveOrbitPointsSheafIsoPointsSheaf m hm) =
      Over.homMk (toProjectiveOrbit (H := H) m hm)
        (toProjectiveOrbit_projectiveOrbitToSpec m hm) from
    congrArg Over.Hom.left h
  apply (CommHopfAlgCat.specPointsHomEquiv H _).injective
  rw [CommHopfAlgCat.specPointsHomEquiv_representedQuotientProjection,
    specPointsHomEquiv_toProjectiveOrbit]
  simp only [Iso.trans_hom, ObjectProperty.FullSubcategory.comp_hom,
    fppfHomogeneousQuotientIsoProjectiveOrbitPoints_hom,
    fppfHomogeneousQuotientProjection_comp_toProjectiveOrbitPoints_assoc]

/-- For Chevalley's representing isomorphism `fppfHomogeneousQuotientIsoProjectiveOrbitPoints`,
the descended left translation by `g ∈ G(k)` agrees with `projectiveOrbitTranslation`. -/
@[simp]
theorem representedQuotientTranslation_fppfHomogeneousQuotientIsoProjectiveOrbitPoints_hom_left
    [_root_.IsReduced H] (I : HopfIdeal k H) (m : M) (hm : Module.IsUnimodular k m)
    (hcoset : ∀ (A : CommAlgCat.{u} k) (g h : HopfAlgebra.points (R := k) (H := H) A),
      (QuotientGroup.mk g : HopfAlgebra.points (R := k) (H := H) A ⧸
          CommHopfAlgCat.quotientPointsSubgroup H I A) = QuotientGroup.mk h ↔
        ∃ c : Aˣ, ∀ φ : Module.Dual k M,
          h.ofConv (matrixCoefficient (C := H) φ m) =
            c * g.ofConv (matrixCoefficient (C := H) φ m))
    (g : HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k)) :
    (CommHopfAlgCat.representedQuotientTranslation H I
      (fppfHomogeneousQuotientIsoProjectiveOrbitPoints I m hm hcoset ≪≫
        projectiveOrbitPointsSheafIsoPointsSheaf m hm) g).hom.left =
      (projectiveOrbitTranslation (H := H) m hm g).hom := by
  let e := fppfHomogeneousQuotientIsoProjectiveOrbitPoints I m hm hcoset ≪≫
    projectiveOrbitPointsSheafIsoPointsSheaf m hm
  let tOver :
      Over.mk (projectiveOrbitToSpec (H := H) m hm) ⟶
        Over.mk (projectiveOrbitToSpec (H := H) m hm) :=
    Over.homMk (projectiveOrbitTranslation (H := H) m hm g).hom
      (projectiveOrbitTranslation_hom_toSpec m hm g)
  suffices h : (CommHopfAlgCat.representedQuotientTranslation H I e g).hom = tOver from
    congrArg Over.Hom.left h
  apply CommHopfAlgCat.representedQuotient_hom_ext H I e
  apply Over.OverMorphism.ext
  have hlhs :
      (CommHopfAlgCat.representedQuotientProjection H I e ≫
          (CommHopfAlgCat.representedQuotientTranslation H I e g).hom).left =
        Spec.map (CommRingCat.ofHom
          (HopfAlgebra.leftTranslationAlgEquiv g).toAlgHom.toRingHom) ≫
            toProjectiveOrbit (H := H) m hm := by
    refine (congrArg Over.Hom.left
      (CommHopfAlgCat.representedQuotientProjection_comp_translation_hom H I e g)).trans ?_
    exact (congrArg (· ≫ (CommHopfAlgCat.representedQuotientProjection H I e).left)
      (TauCeti.CommHopfAlgCat.mapMulEquiv_left
        (WithConv.toConv (HopfAlgebra.leftTranslationAlgEquiv g).toAlgHom))).trans
      (congrArg _
        (representedQuotientProjection_fppfHomogeneousQuotientIsoProjectiveOrbitPoints_left
          I m hm hcoset))
  have hrhs :
      (CommHopfAlgCat.representedQuotientProjection H I e ≫ tOver).left =
        toProjectiveOrbit (H := H) m hm ≫
          (projectiveOrbitTranslation (H := H) m hm g).hom :=
    congrArg (· ≫ (projectiveOrbitTranslation (H := H) m hm g).hom)
      (representedQuotientProjection_fppfHomogeneousQuotientIsoProjectiveOrbitPoints_left
        I m hm hcoset)
  exact hlhs.trans ((toProjectiveOrbit_projectiveOrbitTranslation_hom m hm g).symm.trans hrhs.symm)

end SingleOrbit

section SubgroupMaps

variable {M₁ : Type u} [AddCommGroup M₁] [Module k M₁] [Comodule k H M₁] [Module.Finite k M₁]
  {M₂ : Type u} [AddCommGroup M₂] [Module k M₂] [Comodule k H M₂] [Module.Finite k M₂]
  {M₃ : Type u} [AddCommGroup M₃] [Module k M₃] [Comodule k H M₃] [Module.Finite k M₃]
  {I J K : HopfIdeal k H}
  {m₁ : M₁} {hm₁ : Module.IsUnimodular k m₁}
  {m₂ : M₂} {hm₂ : Module.IsUnimodular k m₂}
  {m₃ : M₃} {hm₃ : Module.IsUnimodular k m₃}

/-- **Subgroup-induced morphism between projective-orbit quotient models**
(Milne, Proposition 5.22). For closed subgroups `P ⊆ Q` defined by Hopf ideals `J ≤ I`, any
projective-orbit representations `eI` and `eJ` of `G/P` and `G/Q` induce a canonical `k`-scheme
morphism between the corresponding projective orbit schemes. -/
noncomputable def projectiveOrbitQuotientMap (hJI : J ≤ I)
    (eI : CommHopfAlgCat.fppfHomogeneousQuotient H I ≅ projectiveOrbitPointsSheaf (H := H) m₁ hm₁)
    (eJ : CommHopfAlgCat.fppfHomogeneousQuotient H J ≅ projectiveOrbitPointsSheaf (H := H) m₂ hm₂) :
    projectiveOrbitScheme (H := H) m₁ hm₁ ⟶ projectiveOrbitScheme (H := H) m₂ hm₂ :=
  (CommHopfAlgCat.representedQuotientMap H hJI
    (eI ≪≫ projectiveOrbitPointsSheafIsoPointsSheaf m₁ hm₁)
    (eJ ≪≫ projectiveOrbitPointsSheafIsoPointsSheaf m₂ hm₂)).left

/-- `projectiveOrbitQuotientMap` preserves the structural morphism to `Spec k`. -/
@[reassoc (attr := simp)]
theorem projectiveOrbitQuotientMap_toSpec (hJI : J ≤ I)
    (eI : CommHopfAlgCat.fppfHomogeneousQuotient H I ≅ projectiveOrbitPointsSheaf (H := H) m₁ hm₁)
    (eJ : CommHopfAlgCat.fppfHomogeneousQuotient H J ≅ projectiveOrbitPointsSheaf (H := H) m₂ hm₂) :
    projectiveOrbitQuotientMap hJI eI eJ ≫ projectiveOrbitToSpec (H := H) m₂ hm₂ =
      projectiveOrbitToSpec (H := H) m₁ hm₁ :=
  Over.w _

/-- On a single projective-orbit model, `projectiveOrbitQuotientMap` for `le_refl I` is the
identity morphism. -/
@[simp]
theorem projectiveOrbitQuotientMap_refl (I : HopfIdeal k H)
    (eI : CommHopfAlgCat.fppfHomogeneousQuotient H I ≅
      projectiveOrbitPointsSheaf (H := H) m₁ hm₁) :
    projectiveOrbitQuotientMap (le_refl I) eI eI = 𝟙 (projectiveOrbitScheme (H := H) m₁ hm₁) := by
  simp [projectiveOrbitQuotientMap]

/-- Subgroup-induced morphisms between projective-orbit quotient models compose along chains
`K ≤ J ≤ I`. -/
@[reassoc (attr := simp)]
theorem projectiveOrbitQuotientMap_comp (hJI : J ≤ I) (hKJ : K ≤ J)
    (eI : CommHopfAlgCat.fppfHomogeneousQuotient H I ≅ projectiveOrbitPointsSheaf (H := H) m₁ hm₁)
    (eJ : CommHopfAlgCat.fppfHomogeneousQuotient H J ≅ projectiveOrbitPointsSheaf (H := H) m₂ hm₂)
    (eK : CommHopfAlgCat.fppfHomogeneousQuotient H K ≅ projectiveOrbitPointsSheaf (H := H) m₃ hm₃) :
    projectiveOrbitQuotientMap hJI eI eJ ≫ projectiveOrbitQuotientMap hKJ eJ eK =
      projectiveOrbitQuotientMap (hKJ.trans hJI) eI eK := by
  simp [projectiveOrbitQuotientMap, ← Over.comp_left]

/-- **Canonical isomorphism between projective-orbit models of the same homogeneous quotient.** -/
noncomputable def projectiveOrbitQuotientIso (I : HopfIdeal k H)
    (e₁ : CommHopfAlgCat.fppfHomogeneousQuotient H I ≅ projectiveOrbitPointsSheaf (H := H) m₁ hm₁)
    (e₂ : CommHopfAlgCat.fppfHomogeneousQuotient H I ≅ projectiveOrbitPointsSheaf (H := H) m₂ hm₂) :
    projectiveOrbitScheme (H := H) m₁ hm₁ ≅ projectiveOrbitScheme (H := H) m₂ hm₂ :=
  (Over.forget (Spec (CommRingCat.of k))).mapIso <|
    CommHopfAlgCat.representedQuotientIso H I
      (e₁ ≪≫ projectiveOrbitPointsSheafIsoPointsSheaf m₁ hm₁)
      (e₂ ≪≫ projectiveOrbitPointsSheafIsoPointsSheaf m₂ hm₂)

/-- The forward morphism of `projectiveOrbitQuotientIso` is `projectiveOrbitQuotientMap` for
`le_refl I`. -/
@[simp]
theorem projectiveOrbitQuotientIso_hom (I : HopfIdeal k H)
    (e₁ : CommHopfAlgCat.fppfHomogeneousQuotient H I ≅ projectiveOrbitPointsSheaf (H := H) m₁ hm₁)
    (e₂ : CommHopfAlgCat.fppfHomogeneousQuotient H I ≅ projectiveOrbitPointsSheaf (H := H) m₂ hm₂) :
    (projectiveOrbitQuotientIso I e₁ e₂).hom = projectiveOrbitQuotientMap (le_refl I) e₁ e₂ := by
  simp [projectiveOrbitQuotientIso, projectiveOrbitQuotientMap]

/-- The inverse morphism of `projectiveOrbitQuotientIso` is `projectiveOrbitQuotientMap` in the
reverse direction. -/
@[simp]
theorem projectiveOrbitQuotientIso_inv (I : HopfIdeal k H)
    (e₁ : CommHopfAlgCat.fppfHomogeneousQuotient H I ≅ projectiveOrbitPointsSheaf (H := H) m₁ hm₁)
    (e₂ : CommHopfAlgCat.fppfHomogeneousQuotient H I ≅ projectiveOrbitPointsSheaf (H := H) m₂ hm₂) :
    (projectiveOrbitQuotientIso I e₁ e₂).inv = projectiveOrbitQuotientMap (le_refl I) e₂ e₁ := by
  simp [projectiveOrbitQuotientIso, projectiveOrbitQuotientMap]

/-- Comparing a projective-orbit model with itself gives the identity isomorphism. -/
@[simp]
theorem projectiveOrbitQuotientIso_refl (I : HopfIdeal k H)
    (e₁ : CommHopfAlgCat.fppfHomogeneousQuotient H I ≅
      projectiveOrbitPointsSheaf (H := H) m₁ hm₁) :
    projectiveOrbitQuotientIso I e₁ e₁ = Iso.refl (projectiveOrbitScheme (H := H) m₁ hm₁) := by
  ext : 1
  simp

/-- Swapping the two projective-orbit models inverts `projectiveOrbitQuotientIso`. -/
@[simp]
theorem projectiveOrbitQuotientIso_symm (I : HopfIdeal k H)
    (e₁ : CommHopfAlgCat.fppfHomogeneousQuotient H I ≅ projectiveOrbitPointsSheaf (H := H) m₁ hm₁)
    (e₂ : CommHopfAlgCat.fppfHomogeneousQuotient H I ≅ projectiveOrbitPointsSheaf (H := H) m₂ hm₂) :
    (projectiveOrbitQuotientIso I e₁ e₂).symm = projectiveOrbitQuotientIso I e₂ e₁ := by
  ext : 1
  simp

/-- Canonical comparison isomorphisms between projective-orbit models compose transitively. -/
@[simp]
theorem projectiveOrbitQuotientIso_trans (I : HopfIdeal k H)
    (e₁ : CommHopfAlgCat.fppfHomogeneousQuotient H I ≅ projectiveOrbitPointsSheaf (H := H) m₁ hm₁)
    (e₂ : CommHopfAlgCat.fppfHomogeneousQuotient H I ≅ projectiveOrbitPointsSheaf (H := H) m₂ hm₂)
    (e₃ : CommHopfAlgCat.fppfHomogeneousQuotient H I ≅ projectiveOrbitPointsSheaf (H := H) m₃ hm₃) :
    projectiveOrbitQuotientIso I e₁ e₂ ≪≫ projectiveOrbitQuotientIso I e₂ e₃ =
      projectiveOrbitQuotientIso I e₁ e₃ := by
  ext : 1
  simp

/-- For Chevalley models of `G/P` and `G/Q` (`J ≤ I`), `projectiveOrbitQuotientMap` commutes with
the orbit projections from `Spec H`. -/
@[reassoc (attr := simp)]
theorem toProjectiveOrbit_projectiveOrbitQuotientMap [_root_.IsReduced H] (hJI : J ≤ I)
    (hcoset₁ : ∀ (A : CommAlgCat.{u} k) (g h : HopfAlgebra.points (R := k) (H := H) A),
      (QuotientGroup.mk g : HopfAlgebra.points (R := k) (H := H) A ⧸
          CommHopfAlgCat.quotientPointsSubgroup H I A) = QuotientGroup.mk h ↔
        ∃ c : Aˣ, ∀ φ : Module.Dual k M₁,
          h.ofConv (matrixCoefficient (C := H) φ m₁) =
            c * g.ofConv (matrixCoefficient (C := H) φ m₁))
    (hcoset₂ : ∀ (A : CommAlgCat.{u} k) (g h : HopfAlgebra.points (R := k) (H := H) A),
      (QuotientGroup.mk g : HopfAlgebra.points (R := k) (H := H) A ⧸
          CommHopfAlgCat.quotientPointsSubgroup H J A) = QuotientGroup.mk h ↔
        ∃ c : Aˣ, ∀ φ : Module.Dual k M₂,
          h.ofConv (matrixCoefficient (C := H) φ m₂) =
            c * g.ofConv (matrixCoefficient (C := H) φ m₂)) :
    toProjectiveOrbit (H := H) m₁ hm₁ ≫
        projectiveOrbitQuotientMap hJI
          (fppfHomogeneousQuotientIsoProjectiveOrbitPoints I m₁ hm₁ hcoset₁)
          (fppfHomogeneousQuotientIsoProjectiveOrbitPoints J m₂ hm₂ hcoset₂) =
      toProjectiveOrbit (H := H) m₂ hm₂ :=
  (congrArg (· ≫ projectiveOrbitQuotientMap hJI _ _)
    (representedQuotientProjection_fppfHomogeneousQuotientIsoProjectiveOrbitPoints_left
      I m₁ hm₁ hcoset₁)).symm.trans <|
    (congrArg Over.Hom.left <|
      CommHopfAlgCat.representedQuotientProjection_comp_map H hJI
        (fppfHomogeneousQuotientIsoProjectiveOrbitPoints I m₁ hm₁ hcoset₁ ≪≫
          projectiveOrbitPointsSheafIsoPointsSheaf m₁ hm₁)
        (fppfHomogeneousQuotientIsoProjectiveOrbitPoints J m₂ hm₂ hcoset₂ ≪≫
          projectiveOrbitPointsSheafIsoPointsSheaf m₂ hm₂)).trans
      (representedQuotientProjection_fppfHomogeneousQuotientIsoProjectiveOrbitPoints_left
        J m₂ hm₂ hcoset₂)

/-- `projectiveOrbitQuotientMap` on Chevalley models is uniquely characterized among all scheme
morphisms by compatibility with `toProjectiveOrbit`. -/
theorem eq_projectiveOrbitQuotientMap_iff [_root_.IsReduced H] (hJI : J ≤ I)
    (hcoset₁ : ∀ (A : CommAlgCat.{u} k) (g h : HopfAlgebra.points (R := k) (H := H) A),
      (QuotientGroup.mk g : HopfAlgebra.points (R := k) (H := H) A ⧸
          CommHopfAlgCat.quotientPointsSubgroup H I A) = QuotientGroup.mk h ↔
        ∃ c : Aˣ, ∀ φ : Module.Dual k M₁,
          h.ofConv (matrixCoefficient (C := H) φ m₁) =
            c * g.ofConv (matrixCoefficient (C := H) φ m₁))
    (hcoset₂ : ∀ (A : CommAlgCat.{u} k) (g h : HopfAlgebra.points (R := k) (H := H) A),
      (QuotientGroup.mk g : HopfAlgebra.points (R := k) (H := H) A ⧸
          CommHopfAlgCat.quotientPointsSubgroup H J A) = QuotientGroup.mk h ↔
        ∃ c : Aˣ, ∀ φ : Module.Dual k M₂,
          h.ofConv (matrixCoefficient (C := H) φ m₂) =
            c * g.ofConv (matrixCoefficient (C := H) φ m₂))
    (f : projectiveOrbitScheme (H := H) m₁ hm₁ ⟶ projectiveOrbitScheme (H := H) m₂ hm₂) :
    f = projectiveOrbitQuotientMap hJI
          (fppfHomogeneousQuotientIsoProjectiveOrbitPoints I m₁ hm₁ hcoset₁)
          (fppfHomogeneousQuotientIsoProjectiveOrbitPoints J m₂ hm₂ hcoset₂) ↔
      toProjectiveOrbit (H := H) m₁ hm₁ ≫ f = toProjectiveOrbit (H := H) m₂ hm₂ := by
  refine ⟨by rintro rfl; exact toProjectiveOrbit_projectiveOrbitQuotientMap hJI hcoset₁ hcoset₂,
    fun hf ↦ ?_⟩
  have : IsSeparated (Limits.terminal.from (projectiveOrbitScheme (H := H) m₂ hm₂)) := by
    rw [← Limits.terminal.comp_from (projectiveOrbitToSpec (H := H) m₂ hm₂)]
    infer_instance
  exact TauCeti.ext_of_isSchemeTheoreticallyDominant
    (toProjectiveOrbit (H := H) m₁ hm₁)
    (Limits.terminal.from (projectiveOrbitScheme (H := H) m₂ hm₂))
    (Limits.terminal.hom_ext _ _)
    (hf.trans (toProjectiveOrbit_projectiveOrbitQuotientMap hJI hcoset₁ hcoset₂).symm)

/-- On Chevalley models of `G/P` and `G/Q`, `projectiveOrbitQuotientMap` intertwines rational
orbit translations `projectiveOrbitTranslation`. -/
@[reassoc]
theorem projectiveOrbitTranslation_hom_projectiveOrbitQuotientMap
    [_root_.IsReduced H] (hJI : J ≤ I)
    (hcoset₁ : ∀ (A : CommAlgCat.{u} k) (g h : HopfAlgebra.points (R := k) (H := H) A),
      (QuotientGroup.mk g : HopfAlgebra.points (R := k) (H := H) A ⧸
          CommHopfAlgCat.quotientPointsSubgroup H I A) = QuotientGroup.mk h ↔
        ∃ c : Aˣ, ∀ φ : Module.Dual k M₁,
          h.ofConv (matrixCoefficient (C := H) φ m₁) =
            c * g.ofConv (matrixCoefficient (C := H) φ m₁))
    (hcoset₂ : ∀ (A : CommAlgCat.{u} k) (g h : HopfAlgebra.points (R := k) (H := H) A),
      (QuotientGroup.mk g : HopfAlgebra.points (R := k) (H := H) A ⧸
          CommHopfAlgCat.quotientPointsSubgroup H J A) = QuotientGroup.mk h ↔
        ∃ c : Aˣ, ∀ φ : Module.Dual k M₂,
          h.ofConv (matrixCoefficient (C := H) φ m₂) =
            c * g.ofConv (matrixCoefficient (C := H) φ m₂))
    (g : HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k)) :
    (projectiveOrbitTranslation (H := H) m₁ hm₁ g).hom ≫
        projectiveOrbitQuotientMap hJI
          (fppfHomogeneousQuotientIsoProjectiveOrbitPoints I m₁ hm₁ hcoset₁)
          (fppfHomogeneousQuotientIsoProjectiveOrbitPoints J m₂ hm₂ hcoset₂) =
      projectiveOrbitQuotientMap hJI
          (fppfHomogeneousQuotientIsoProjectiveOrbitPoints I m₁ hm₁ hcoset₁)
          (fppfHomogeneousQuotientIsoProjectiveOrbitPoints J m₂ hm₂ hcoset₂) ≫
        (projectiveOrbitTranslation (H := H) m₂ hm₂ g).hom := by
  have h := congrArg Over.Hom.left <|
    CommHopfAlgCat.representedQuotientTranslation_hom_comp_map H I
      (fppfHomogeneousQuotientIsoProjectiveOrbitPoints I m₁ hm₁ hcoset₁ ≪≫
        projectiveOrbitPointsSheafIsoPointsSheaf m₁ hm₁) hJI
      (fppfHomogeneousQuotientIsoProjectiveOrbitPoints J m₂ hm₂ hcoset₂ ≪≫
        projectiveOrbitPointsSheafIsoPointsSheaf m₂ hm₂) g
  simpa only [Over.comp_left, projectiveOrbitQuotientMap,
    representedQuotientTranslation_fppfHomogeneousQuotientIsoProjectiveOrbitPoints_hom_left] using h

attribute [local instance] Comodule.exteriorPower in
private theorem surjective_representedQuotientProjection_left [_root_.IsReduced H]
    (J : HopfIdeal k H)
    (eJ : CommHopfAlgCat.fppfHomogeneousQuotient H J ≅
      projectiveOrbitPointsSheaf (H := H) m₂ hm₂) :
    Surjective
      (CommHopfAlgCat.representedQuotientProjection H J
        (eJ ≪≫ projectiveOrbitPointsSheafIsoPointsSheaf m₂ hm₂)).left := by
  have := Algebra.FiniteType.isNoetherianRing k H
  obtain ⟨V, n, hV, m', hm', hcoset'⟩ :=
    J.exists_finite_subcomodule_exteriorPower_coset_matrixCoefficient.{u, u, u}
      (IsNoetherian.noetherian J.toIdeal)
  let : Module.Finite k V := hV
  let : AddCommGroup V := Module.addCommMonoidToAddCommGroup k
  let eJ' := fppfHomogeneousQuotientIsoProjectiveOrbitPoints J m' hm' hcoset'
  have hfac :
      (toProjectiveOrbit (H := H) m' hm' ≫
          (projectiveOrbitQuotientIso J eJ' eJ).hom :
        Spec (.of H) ⟶ projectiveOrbitScheme (H := H) m₂ hm₂) =
        (CommHopfAlgCat.representedQuotientProjection H J
          (eJ ≪≫ projectiveOrbitPointsSheafIsoPointsSheaf m₂ hm₂)).left :=
    (congrArg (· ≫ (projectiveOrbitQuotientIso J eJ' eJ).hom)
      (representedQuotientProjection_fppfHomogeneousQuotientIsoProjectiveOrbitPoints_left
        J m' hm' hcoset')).symm.trans <|
      (congrArg (fun f ↦
          (CommHopfAlgCat.representedQuotientProjection H J
            (eJ' ≪≫ projectiveOrbitPointsSheafIsoPointsSheaf m' hm')).left ≫ f)
        (projectiveOrbitQuotientIso_hom J eJ' eJ)).trans <|
        congrArg Over.Hom.left <|
          CommHopfAlgCat.representedQuotientProjection_comp_map H (le_refl J)
            (eJ' ≪≫ projectiveOrbitPointsSheafIsoPointsSheaf m' hm')
            (eJ ≪≫ projectiveOrbitPointsSheafIsoPointsSheaf m₂ hm₂)
  have hsurj :
      Surjective (toProjectiveOrbit (H := H) m' hm' ≫
        (projectiveOrbitQuotientIso J eJ' eJ).hom) :=
    inferInstance
  exact Eq.mp (congrArg Surjective hfac) hsurj

/-- **Surjectivity of subgroup-induced projective-orbit quotient maps.** For a reduced affine
group `G` of finite type over `k`, every `projectiveOrbitQuotientMap hJI eI eJ` is surjective. -/
instance instSurjectiveProjectiveOrbitQuotientMap [_root_.IsReduced H] (hJI : J ≤ I)
    (eI : CommHopfAlgCat.fppfHomogeneousQuotient H I ≅ projectiveOrbitPointsSheaf (H := H) m₁ hm₁)
    (eJ : CommHopfAlgCat.fppfHomogeneousQuotient H J ≅ projectiveOrbitPointsSheaf (H := H) m₂ hm₂) :
    Surjective (projectiveOrbitQuotientMap hJI eI eJ) := by
  let p :=
    (CommHopfAlgCat.representedQuotientProjection H I
      (eI ≪≫ projectiveOrbitPointsSheafIsoPointsSheaf m₁ hm₁)).left
  have hfac :
      p ≫ projectiveOrbitQuotientMap hJI eI eJ =
        (CommHopfAlgCat.representedQuotientProjection H J
          (eJ ≪≫ projectiveOrbitPointsSheafIsoPointsSheaf m₂ hm₂)).left :=
    congrArg Over.Hom.left <|
      CommHopfAlgCat.representedQuotientProjection_comp_map H hJI
        (eI ≪≫ projectiveOrbitPointsSheafIsoPointsSheaf m₁ hm₁)
        (eJ ≪≫ projectiveOrbitPointsSheafIsoPointsSheaf m₂ hm₂)
  have : Surjective (p ≫ projectiveOrbitQuotientMap hJI eI eJ) :=
    Eq.mpr (congrArg Surjective hfac) (surjective_representedQuotientProjection_left J eJ)
  exact Surjective.of_comp p (projectiveOrbitQuotientMap hJI eI eJ)

/-- **Properness descends from `G/P` to `G/Q` for `P ⊆ Q`.** If `J ≤ I` (`P ⊆ Q`) and a projective
orbit scheme representing `G/P` is proper over `Spec k`, then any projective orbit scheme
representing `G/Q` is also proper over `Spec k`. -/
theorem isProper_projectiveOrbitToSpec_of_le [_root_.IsReduced H] (hJI : J ≤ I)
    (eI : CommHopfAlgCat.fppfHomogeneousQuotient H I ≅ projectiveOrbitPointsSheaf (H := H) m₁ hm₁)
    (eJ : CommHopfAlgCat.fppfHomogeneousQuotient H J ≅ projectiveOrbitPointsSheaf (H := H) m₂ hm₂)
    [IsProper (projectiveOrbitToSpec (H := H) m₁ hm₁)] :
    IsProper (projectiveOrbitToSpec (H := H) m₂ hm₂) := by
  have : UniversallyClosed
      (projectiveOrbitQuotientMap hJI eI eJ ≫ projectiveOrbitToSpec (H := H) m₂ hm₂) := by
    rw [projectiveOrbitQuotientMap_toSpec]
    infer_instance
  have : UniversallyClosed (projectiveOrbitToSpec (H := H) m₂ hm₂) :=
    UniversallyClosed.of_comp_surjective
      (projectiveOrbitQuotientMap hJI eI eJ) (projectiveOrbitToSpec (H := H) m₂ hm₂)
  exact {}

/-- **Closedness of projective orbits descends from `G/P` to `G/Q` for `P ⊆ Q`.** If `J ≤ I`
(`P ⊆ Q`) and a projective orbit representing `G/P` is closed in projective space, then any
projective orbit representing `G/Q` is also closed in its ambient projective space. -/
theorem isClosed_range_projectiveOrbitMap_of_le [_root_.IsReduced H] (hJI : J ≤ I)
    (eI : CommHopfAlgCat.fppfHomogeneousQuotient H I ≅ projectiveOrbitPointsSheaf (H := H) m₁ hm₁)
    (eJ : CommHopfAlgCat.fppfHomogeneousQuotient H J ≅ projectiveOrbitPointsSheaf (H := H) m₂ hm₂)
    (hclosed : IsClosed (Set.range (projectiveOrbitMap (H := H) m₁ hm₁))) :
    IsClosed (Set.range (projectiveOrbitMap (H := H) m₂ hm₂)) := by
  have : IsProper (projectiveOrbitToSpec (H := H) m₁ hm₁) :=
    (isProper_projectiveOrbitToSpec_iff_isClosed m₁ hm₁).mpr hclosed
  have : IsProper (projectiveOrbitToSpec (H := H) m₂ hm₂) :=
    isProper_projectiveOrbitToSpec_of_le hJI eI eJ
  exact (isProper_projectiveOrbitToSpec_iff_isClosed m₂ hm₂).mp this

/-- Properness over `Spec k` is independent of the choice of projective orbit representing `G/N`. -/
theorem isProper_projectiveOrbitToSpec_iff_of_iso [_root_.IsReduced H] (I : HopfIdeal k H)
    (e₁ : CommHopfAlgCat.fppfHomogeneousQuotient H I ≅ projectiveOrbitPointsSheaf (H := H) m₁ hm₁)
    (e₂ : CommHopfAlgCat.fppfHomogeneousQuotient H I ≅ projectiveOrbitPointsSheaf (H := H) m₂ hm₂) :
    IsProper (projectiveOrbitToSpec (H := H) m₁ hm₁) ↔
      IsProper (projectiveOrbitToSpec (H := H) m₂ hm₂) :=
  ⟨fun _ ↦ isProper_projectiveOrbitToSpec_of_le (le_refl I) e₁ e₂,
   fun _ ↦ isProper_projectiveOrbitToSpec_of_le (le_refl I) e₂ e₁⟩

end SubgroupMaps

end QuotientFunctoriality

end TauCeti.Comodule
