/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Representation.ProjectiveOrbit.Quotient
public import TauCeti.Algebra.AlgebraicGroup.Representation.ProjectiveOrbit.Action
public import TauCeti.Algebra.AlgebraicGroup.Fppf.Quotient.Homogeneous.Scheme
public import TauCeti.Algebra.AlgebraicGroup.Representation.ProjectiveOrbit.ProperDescent

/-!
# Functoriality and properness descent for projective orbit quotients

Let `G = Spec H` be an affine group scheme of finite type over an algebraically closed field `k`.
Combining projective orbit schemes (`Comodule.isProper_projectiveOrbitToSpec_iff_isClosed`) with
`CommHopfAlgCat.fppfHomogeneousQuotientSchemeMap` yields scheme-level functoriality and properness
descent for projective orbit models of homogeneous quotients:

* **Subgroup functoriality (`projectiveOrbitQuotientMap`):** Without reducedness assumptions on `G`,
  for closed subgroups `P ⊆ Q` (`J ≤ I`), any projective-orbit models `eI` and `eJ` of `G/P` and
  `G/Q` induce a surjective `k`-scheme morphism `projectiveOrbitQuotientMap hJI eI eJ`, uniquely
  determined by compatibility with `projectiveOrbitQuotientProjection`
  (`eq_projectiveOrbitQuotientMap_iff`), functorial in subgroup chains, and giving canonical
  comparison isomorphisms `projectiveOrbitQuotientIso`.
* **Chevalley orbit compatibility:** When `G` is reduced (`[IsReduced H]`), on Chevalley's
  `fppfHomogeneousQuotientIsoProjectiveOrbitPoints`, `projectiveOrbitQuotientProjection` is
  `toProjectiveOrbit m hm`, descended left translation is `projectiveOrbitTranslation m hm g`, and
  `projectiveOrbitQuotientMap` intertwines both.
* **Properness and closedness descent:** Without reducedness assumptions on `G`, for `J ≤ I`, if a
  projective orbit representing `G/P` is proper over `Spec k` (equivalently, closed in projective
  space), then any projective orbit representing `G/Q` is also proper over `Spec k` and closed in
  its ambient projective space.

## Main declarations

* `TauCeti.Comodule.specPointsHomEquiv_toProjectiveOrbit`: identifies `toProjectiveOrbit` over
  `Spec k` with `toProjectiveOrbitPoints`.
* `TauCeti.Comodule.projectiveOrbitQuotientProjection`,
  `TauCeti.Comodule.projectiveOrbitQuotient_hom_ext`: the epimorphic scheme projection
  `Spec H ⟶ projectiveOrbitScheme m hm` and its morphism extensionality principle.
* `TauCeti.Comodule.projectiveOrbitQuotientMap`,
  `TauCeti.Comodule.eq_projectiveOrbitQuotientMap_iff`,
  `TauCeti.Comodule.instSurjectiveProjectiveOrbitQuotientMap`: the surjective `k`-scheme morphism
  between projective-orbit models induced by `J ≤ I` and its uniqueness characterization.
* `TauCeti.Comodule.projectiveOrbitQuotientIso`: canonical `k`-scheme isomorphism between two
  projective-orbit models of the same homogeneous quotient.
* `TauCeti.Comodule.isClosed_range_projectiveOrbitMap_of_le_of_fppfHomogeneousQuotient_iso`,
  `TauCeti.Comodule.isProper_projectiveOrbitToSpec_iff_of_fppfHomogeneousQuotient_iso`: properness
  and closedness descent and invariance for projective-orbit models.

## References

* J. S. Milne, *Algebraic Groups* (2017), Proposition 5.22 and §§7.c–7.f.
* A. Borel, *Linear Algebraic Groups* (2nd ed., 1991), §6.8 and §11.2.
-/

public section

open CategoryTheory AlgebraicGeometry Opposite

namespace TauCeti.Comodule

universe u

variable {k : Type u} [Field k] [IsAlgClosed k] {H : _root_.CommHopfAlgCat.{u} k}
  [Algebra.FiniteType k H]

section SingleOrbit

variable {M : Type u} [AddCommGroup M] [Module k M] [Comodule k H M] [Module.Finite k M]

/-- `specPointsHomEquiv` sends `toProjectiveOrbit` over `Spec k` to `toProjectiveOrbitPoints`. -/
@[simp] theorem specPointsHomEquiv_toProjectiveOrbit (m : M) (hm : Module.IsUnimodular k m) :
    CommHopfAlgCat.specPointsHomEquiv H (Over.mk (projectiveOrbitToSpec (H := H) m hm))
        (Over.homMk (toProjectiveOrbit (H := H) m hm)
          (toProjectiveOrbit_projectiveOrbitToSpec m hm)) =
      toProjectiveOrbitPoints (H := H) m hm := by
  ext A ⟨g⟩
  exact (CommHopfAlgCat.specPointsHomEquiv_apply_app_apply H _ A g).trans <|
    (congrArg ULift.up <| Over.OverMorphism.ext <|
      congrArg (· ≫ toProjectiveOrbit (H := H) m hm)
        (TauCeti.CommHopfAlgCat.mapMulEquiv_left g)).trans
      (toProjectiveOrbitPoints_app_apply m hm A g).symm

section OrbitProjection

variable (I : HopfIdeal k H) (m : M) (hm : Module.IsUnimodular k m)
  (e : CommHopfAlgCat.fppfHomogeneousQuotient H I ≅ projectiveOrbitPointsSheaf (H := H) m hm)

/-- **Canonical quotient projection `Spec H ⟶ projectiveOrbitScheme m hm`** induced by an
isomorphism `e : fppfHomogeneousQuotient H I ≅ projectiveOrbitPointsSheaf m hm`. -/
noncomputable def projectiveOrbitQuotientProjection :
    Spec (.of H) ⟶ projectiveOrbitScheme (H := H) m hm :=
  (CommHopfAlgCat.representedQuotientProjection H I e).left

/-- `projectiveOrbitQuotientProjection` is the underlying scheme morphism of
`CommHopfAlgCat.representedQuotientProjection`. -/
theorem projectiveOrbitQuotientProjection_def :
    projectiveOrbitQuotientProjection I m hm e =
      (CommHopfAlgCat.representedQuotientProjection H I e).left := (rfl)

/-- `projectiveOrbitQuotientProjection` is a morphism over `Spec k`. -/
@[reassoc (attr := simp)] theorem projectiveOrbitQuotientProjection_toSpec :
    projectiveOrbitQuotientProjection I m hm e ≫ projectiveOrbitToSpec (H := H) m hm =
      Spec.map (CommRingCat.ofHom (algebraMap k H)) := Over.w _

/-- Every `projectiveOrbitQuotientProjection` is surjective on underlying schemes. -/
instance instSurjectiveProjectiveOrbitQuotientProjection :
    Surjective (projectiveOrbitQuotientProjection I m hm e) :=
  CommHopfAlgCat.instSurjectiveRepresentedQuotientProjectionLeft H I e

/-- Every `projectiveOrbitQuotientProjection` is an epimorphism of schemes. -/
instance epi_projectiveOrbitQuotientProjection :
    Epi (projectiveOrbitQuotientProjection I m hm e) :=
  CommHopfAlgCat.epi_representedQuotientProjection_left H I e

/-- Scheme morphisms out of `projectiveOrbitScheme m hm` are determined by their composites with
`projectiveOrbitQuotientProjection I m hm e`. -/
theorem projectiveOrbitQuotient_hom_ext {Y : Scheme.{u}}
    {f₁ f₂ : projectiveOrbitScheme (H := H) m hm ⟶ Y}
    (h : projectiveOrbitQuotientProjection I m hm e ≫ f₁ =
      projectiveOrbitQuotientProjection I m hm e ≫ f₂) : f₁ = f₂ :=
  (cancel_epi (projectiveOrbitQuotientProjection I m hm e)).mp h

end OrbitProjection

section ChevalleySingleOrbit

variable [_root_.IsReduced H] (I : HopfIdeal k H) (m : M) (hm : Module.IsUnimodular k m)
  (hcoset : ∀ (A : CommAlgCat.{u} k) (g h : HopfAlgebra.points (R := k) (H := H) A),
    (QuotientGroup.mk g : HopfAlgebra.points (R := k) (H := H) A ⧸
        CommHopfAlgCat.quotientPointsSubgroup H I A) = QuotientGroup.mk h ↔
      ∃ c : Aˣ, ∀ φ : Module.Dual k M,
        h.ofConv (matrixCoefficient (C := H) φ m) = c * g.ofConv (matrixCoefficient (C := H) φ m))

/-- For a reduced group `G` and Chevalley's representing isomorphism
`fppfHomogeneousQuotientIsoProjectiveOrbitPoints`, the descended quotient projection in
`Over (Spec k)` is `toProjectiveOrbit` over `Spec k`. -/
@[simp] theorem representedQuotientProjection_fppfHomogeneousQuotientIsoProjectiveOrbitPoints :
    CommHopfAlgCat.representedQuotientProjection H I
      (fppfHomogeneousQuotientIsoProjectiveOrbitPoints I m hm hcoset) =
      Over.homMk (toProjectiveOrbit (H := H) m hm) (toProjectiveOrbit_projectiveOrbitToSpec m hm) :=
  (CommHopfAlgCat.specPointsHomEquiv H _).injective <| by
    rw [CommHopfAlgCat.specPointsHomEquiv_representedQuotientProjection,
      specPointsHomEquiv_toProjectiveOrbit, fppfHomogeneousQuotientIsoProjectiveOrbitPoints_hom,
      fppfHomogeneousQuotientProjection_comp_toProjectiveOrbitPoints]

/-- For a reduced group `G` and Chevalley's representing isomorphism, the underlying scheme morphism
of `representedQuotientProjection` is `toProjectiveOrbit`. -/
theorem representedQuotientProjection_fppfHomogeneousQuotientIsoProjectiveOrbitPoints_left :
    (CommHopfAlgCat.representedQuotientProjection H I
      (fppfHomogeneousQuotientIsoProjectiveOrbitPoints I m hm hcoset)).left =
      toProjectiveOrbit (H := H) m hm :=
  congrArg Over.Hom.left
    (representedQuotientProjection_fppfHomogeneousQuotientIsoProjectiveOrbitPoints I m hm hcoset)

/-- For a reduced group `G`, `projectiveOrbitQuotientProjection` on Chevalley's representing
isomorphism `fppfHomogeneousQuotientIsoProjectiveOrbitPoints` is `toProjectiveOrbit`. -/
@[simp] theorem projectiveOrbitQuotientProjection_fppfHomogeneousQuotientIsoProjectiveOrbitPoints :
    projectiveOrbitQuotientProjection I m hm
      (fppfHomogeneousQuotientIsoProjectiveOrbitPoints I m hm hcoset) =
      toProjectiveOrbit (H := H) m hm :=
  representedQuotientProjection_fppfHomogeneousQuotientIsoProjectiveOrbitPoints_left I m hm hcoset

/-- For a reduced group `G` and Chevalley's representing isomorphism, the descended left translation
by `g ∈ G(k)` agrees with `projectiveOrbitTranslation`. -/
@[simp] theorem
    representedQuotientTranslation_fppfHomogeneousQuotientIsoProjectiveOrbitPoints_hom_left
    (g : HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k)) :
    (CommHopfAlgCat.representedQuotientTranslation H I
      (fppfHomogeneousQuotientIsoProjectiveOrbitPoints I m hm hcoset) g).hom.left =
      (projectiveOrbitTranslation (H := H) m hm g).hom := by
  let e := fppfHomogeneousQuotientIsoProjectiveOrbitPoints I m hm hcoset
  let tOver : Over.mk (projectiveOrbitToSpec (H := H) m hm) ⟶
      Over.mk (projectiveOrbitToSpec (H := H) m hm) :=
    Over.homMk (projectiveOrbitTranslation (H := H) m hm g).hom
      (projectiveOrbitTranslation_hom_toSpec m hm g)
  suffices h : (CommHopfAlgCat.representedQuotientTranslation H I e g).hom = tOver from
    congrArg Over.Hom.left h
  apply CommHopfAlgCat.representedQuotient_hom_ext H I e
  rw [CommHopfAlgCat.representedQuotientProjection_comp_translation_hom]
  dsimp only [e]
  rw [representedQuotientProjection_fppfHomogeneousQuotientIsoProjectiveOrbitPoints]
  apply Over.OverMorphism.ext; dsimp [tOver]
  rw [TauCeti.CommHopfAlgCat.mapMulEquiv_left]
  exact (toProjectiveOrbit_projectiveOrbitTranslation_hom m hm g).symm

/-- For a reduced group `G` and Chevalley's representing isomorphism, the descended inverse left
translation by `g ∈ G(k)` agrees with `(projectiveOrbitTranslation m hm g).inv`. -/
@[simp] theorem
    representedQuotientTranslation_fppfHomogeneousQuotientIsoProjectiveOrbitPoints_inv_left
    (g : HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k)) :
    (CommHopfAlgCat.representedQuotientTranslation H I
      (fppfHomogeneousQuotientIsoProjectiveOrbitPoints I m hm hcoset) g).inv.left =
      (projectiveOrbitTranslation (H := H) m hm g).inv := by
  rw [← Iso.symm_hom, ← CommHopfAlgCat.representedQuotientTranslation_inv,
    ← Iso.symm_hom, ← projectiveOrbitTranslation_inv_eq_symm]
  exact representedQuotientTranslation_fppfHomogeneousQuotientIsoProjectiveOrbitPoints_hom_left
    I m hm hcoset g⁻¹

end ChevalleySingleOrbit

end SingleOrbit

section SubgroupMaps

variable {M₁ : Type u} [AddCommGroup M₁] [Module k M₁] [Comodule k H M₁] [Module.Finite k M₁]
  {M₂ : Type u} [AddCommGroup M₂] [Module k M₂] [Comodule k H M₂] [Module.Finite k M₂]
  {M₃ : Type u} [AddCommGroup M₃] [Module k M₃] [Comodule k H M₃] [Module.Finite k M₃]
  {I J K : HopfIdeal k H} {m₁ : M₁} {hm₁ : Module.IsUnimodular k m₁}
  {m₂ : M₂} {hm₂ : Module.IsUnimodular k m₂} {m₃ : M₃} {hm₃ : Module.IsUnimodular k m₃}

/-- **Subgroup-induced morphism between projective-orbit quotient models** (Milne, Prop. 5.22).
For closed subgroups `P ⊆ Q` defined by Hopf ideals `I` and `J` with `J ≤ I`, any projective-orbit
representations `eI` and `eJ` of `G/P` and `G/Q` induce a canonical `k`-scheme morphism between the
corresponding projective orbit schemes. -/
noncomputable def projectiveOrbitQuotientMap (hJI : J ≤ I)
    (eI : CommHopfAlgCat.fppfHomogeneousQuotient H I ≅ projectiveOrbitPointsSheaf (H := H) m₁ hm₁)
    (eJ : CommHopfAlgCat.fppfHomogeneousQuotient H J ≅ projectiveOrbitPointsSheaf (H := H) m₂ hm₂) :
    projectiveOrbitScheme (H := H) m₁ hm₁ ⟶ projectiveOrbitScheme (H := H) m₂ hm₂ :=
  (CommHopfAlgCat.fppfHomogeneousQuotientSchemeMap H hJI eI eJ).left

section MapLemmas

variable (hJI : J ≤ I)
  (eI : CommHopfAlgCat.fppfHomogeneousQuotient H I ≅ projectiveOrbitPointsSheaf (H := H) m₁ hm₁)
  (eJ : CommHopfAlgCat.fppfHomogeneousQuotient H J ≅ projectiveOrbitPointsSheaf (H := H) m₂ hm₂)

/-- `projectiveOrbitQuotientMap` is the underlying scheme morphism of
`CommHopfAlgCat.fppfHomogeneousQuotientSchemeMap`. -/
theorem projectiveOrbitQuotientMap_def :
    projectiveOrbitQuotientMap hJI eI eJ =
      (CommHopfAlgCat.fppfHomogeneousQuotientSchemeMap H hJI eI eJ).left := (rfl)

/-- `projectiveOrbitQuotientMap` preserves the structural morphism to `Spec k`. -/
@[reassoc (attr := simp)] theorem projectiveOrbitQuotientMap_toSpec :
    projectiveOrbitQuotientMap hJI eI eJ ≫ projectiveOrbitToSpec (H := H) m₂ hm₂ =
      projectiveOrbitToSpec (H := H) m₁ hm₁ := Over.w _

/-- `projectiveOrbitQuotientMap` commutes with `projectiveOrbitQuotientProjection` from `Spec H`. -/
@[reassoc (attr := simp)] theorem projectiveOrbitQuotientProjection_comp_map :
    projectiveOrbitQuotientProjection I m₁ hm₁ eI ≫ projectiveOrbitQuotientMap hJI eI eJ =
      projectiveOrbitQuotientProjection J m₂ hm₂ eJ :=
  congrArg Over.Hom.left
    (CommHopfAlgCat.representedQuotientProjection_comp_fppfHomogeneousQuotientSchemeMap H hJI eI eJ)

/-- `projectiveOrbitQuotientMap` is uniquely characterized among all scheme morphisms by
compatibility with `projectiveOrbitQuotientProjection`. -/
theorem eq_projectiveOrbitQuotientMap_iff
    (f : projectiveOrbitScheme (H := H) m₁ hm₁ ⟶ projectiveOrbitScheme (H := H) m₂ hm₂) :
    f = projectiveOrbitQuotientMap hJI eI eJ ↔
      projectiveOrbitQuotientProjection I m₁ hm₁ eI ≫ f =
        projectiveOrbitQuotientProjection J m₂ hm₂ eJ :=
  ⟨by rintro rfl; exact projectiveOrbitQuotientProjection_comp_map hJI eI eJ,
   fun hf ↦ projectiveOrbitQuotient_hom_ext I m₁ hm₁ eI
    (hf.trans (projectiveOrbitQuotientProjection_comp_map hJI eI eJ).symm)⟩

/-- **Surjectivity of subgroup-induced projective-orbit quotient maps.** Every
`projectiveOrbitQuotientMap hJI eI eJ` is surjective, without reducedness assumptions on `G`. -/
instance instSurjectiveProjectiveOrbitQuotientMap :
    Surjective (projectiveOrbitQuotientMap hJI eI eJ) :=
  CommHopfAlgCat.surjective_fppfHomogeneousQuotientSchemeMap H hJI eI eJ

end MapLemmas

/-- On a single projective-orbit model, `projectiveOrbitQuotientMap` for `le_refl I` is `𝟙 _`. -/
@[simp] theorem projectiveOrbitQuotientMap_refl (I : HopfIdeal k H)
    (eI : CommHopfAlgCat.fppfHomogeneousQuotient H I ≅
      projectiveOrbitPointsSheaf (H := H) m₁ hm₁) :
    projectiveOrbitQuotientMap (le_refl I) eI eI = 𝟙 (projectiveOrbitScheme (H := H) m₁ hm₁) := by
  simp [projectiveOrbitQuotientMap]

/-- Subgroup-induced morphisms between projective-orbit models compose along `K ≤ J ≤ I`. -/
@[reassoc (attr := simp)] theorem projectiveOrbitQuotientMap_comp (hJI : J ≤ I) (hKJ : K ≤ J)
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
  (Over.forget (Spec (CommRingCat.of k))).mapIso <| CommHopfAlgCat.representedQuotientIso H I e₁ e₂

section IsoLemmas

variable (I : HopfIdeal k H)
  (e₁ : CommHopfAlgCat.fppfHomogeneousQuotient H I ≅ projectiveOrbitPointsSheaf (H := H) m₁ hm₁)
  (e₂ : CommHopfAlgCat.fppfHomogeneousQuotient H I ≅ projectiveOrbitPointsSheaf (H := H) m₂ hm₂)

/-- `projectiveOrbitQuotientIso` is the underlying scheme isomorphism of
`CommHopfAlgCat.representedQuotientIso`. -/
theorem projectiveOrbitQuotientIso_def :
    projectiveOrbitQuotientIso I e₁ e₂ =
      (Over.forget (Spec (CommRingCat.of k))).mapIso
        (CommHopfAlgCat.representedQuotientIso H I e₁ e₂) := (rfl)

/-- The forward morphism of `projectiveOrbitQuotientIso` is `projectiveOrbitQuotientMap`. -/
@[simp] theorem projectiveOrbitQuotientIso_hom :
    (projectiveOrbitQuotientIso I e₁ e₂).hom = projectiveOrbitQuotientMap (le_refl I) e₁ e₂ := by
  simp [projectiveOrbitQuotientIso, projectiveOrbitQuotientMap]

/-- The inverse morphism of `projectiveOrbitQuotientIso` is `projectiveOrbitQuotientMap` in the
reverse direction. -/
@[simp] theorem projectiveOrbitQuotientIso_inv :
    (projectiveOrbitQuotientIso I e₁ e₂).inv = projectiveOrbitQuotientMap (le_refl I) e₂ e₁ := by
  simp [projectiveOrbitQuotientIso, projectiveOrbitQuotientMap]

/-- Swapping the two projective-orbit models inverts `projectiveOrbitQuotientIso`. -/
@[simp] theorem projectiveOrbitQuotientIso_symm :
    (projectiveOrbitQuotientIso I e₁ e₂).symm = projectiveOrbitQuotientIso I e₂ e₁ :=
  Iso.ext <| by simp

/-- Canonical comparison isomorphisms between projective-orbit models compose transitively. -/
@[simp] theorem projectiveOrbitQuotientIso_trans
    (e₃ : CommHopfAlgCat.fppfHomogeneousQuotient H I ≅ projectiveOrbitPointsSheaf (H := H) m₃ hm₃) :
    projectiveOrbitQuotientIso I e₁ e₂ ≪≫ projectiveOrbitQuotientIso I e₂ e₃ =
      projectiveOrbitQuotientIso I e₁ e₃ := Iso.ext <| by simp

end IsoLemmas

/-- Comparing a projective-orbit model with itself gives the identity isomorphism. -/
@[simp] theorem projectiveOrbitQuotientIso_refl (I : HopfIdeal k H)
    (e₁ : CommHopfAlgCat.fppfHomogeneousQuotient H I ≅
      projectiveOrbitPointsSheaf (H := H) m₁ hm₁) :
    projectiveOrbitQuotientIso I e₁ e₁ = Iso.refl (projectiveOrbitScheme (H := H) m₁ hm₁) :=
  Iso.ext <| by simp

section ChevalleySubgroupMaps

variable [_root_.IsReduced H] (hJI : J ≤ I)
  (hcoset₁ : ∀ (A : CommAlgCat.{u} k) (g h : HopfAlgebra.points (R := k) (H := H) A),
    (QuotientGroup.mk g : HopfAlgebra.points (R := k) (H := H) A ⧸
        CommHopfAlgCat.quotientPointsSubgroup H I A) = QuotientGroup.mk h ↔
      ∃ c : Aˣ, ∀ φ : Module.Dual k M₁,
        h.ofConv (matrixCoefficient (C := H) φ m₁) = c * g.ofConv (matrixCoefficient (C := H) φ m₁))
  (hcoset₂ : ∀ (A : CommAlgCat.{u} k) (g h : HopfAlgebra.points (R := k) (H := H) A),
    (QuotientGroup.mk g : HopfAlgebra.points (R := k) (H := H) A ⧸
        CommHopfAlgCat.quotientPointsSubgroup H J A) = QuotientGroup.mk h ↔
      ∃ c : Aˣ, ∀ φ : Module.Dual k M₂,
        h.ofConv (matrixCoefficient (C := H) φ m₂) = c * g.ofConv (matrixCoefficient (C := H) φ m₂))

/-- For a reduced group `G` and Chevalley models of `G/P` and `G/Q` (`J ≤ I`),
`projectiveOrbitQuotientMap` commutes with `toProjectiveOrbit` from `Spec H`. -/
@[reassoc (attr := simp)] theorem toProjectiveOrbit_projectiveOrbitQuotientMap :
    toProjectiveOrbit (H := H) m₁ hm₁ ≫
        projectiveOrbitQuotientMap hJI
          (fppfHomogeneousQuotientIsoProjectiveOrbitPoints I m₁ hm₁ hcoset₁)
          (fppfHomogeneousQuotientIsoProjectiveOrbitPoints J m₂ hm₂ hcoset₂) =
      toProjectiveOrbit (H := H) m₂ hm₂ := by
  rw [← projectiveOrbitQuotientProjection_fppfHomogeneousQuotientIsoProjectiveOrbitPoints
      I m₁ hm₁ hcoset₁,
    ← projectiveOrbitQuotientProjection_fppfHomogeneousQuotientIsoProjectiveOrbitPoints
      J m₂ hm₂ hcoset₂,
    projectiveOrbitQuotientProjection_comp_map]

/-- For a reduced group `G`, `projectiveOrbitQuotientMap` on Chevalley models is uniquely
characterized among all scheme morphisms by compatibility with `toProjectiveOrbit`. -/
theorem eq_projectiveOrbitQuotientMap_fppfHomogeneousQuotientIsoProjectiveOrbitPoints_iff
    (f : projectiveOrbitScheme (H := H) m₁ hm₁ ⟶ projectiveOrbitScheme (H := H) m₂ hm₂) :
    f = projectiveOrbitQuotientMap hJI
          (fppfHomogeneousQuotientIsoProjectiveOrbitPoints I m₁ hm₁ hcoset₁)
          (fppfHomogeneousQuotientIsoProjectiveOrbitPoints J m₂ hm₂ hcoset₂) ↔
      toProjectiveOrbit (H := H) m₁ hm₁ ≫ f = toProjectiveOrbit (H := H) m₂ hm₂ := by
  rw [eq_projectiveOrbitQuotientMap_iff,
    projectiveOrbitQuotientProjection_fppfHomogeneousQuotientIsoProjectiveOrbitPoints,
    projectiveOrbitQuotientProjection_fppfHomogeneousQuotientIsoProjectiveOrbitPoints]

/-- For a reduced group `G`, on Chevalley models of `G/P` and `G/Q`, `projectiveOrbitQuotientMap`
intertwines rational orbit translations `projectiveOrbitTranslation`. -/
@[reassoc] theorem projectiveOrbitTranslation_hom_projectiveOrbitQuotientMap
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
      (fppfHomogeneousQuotientIsoProjectiveOrbitPoints I m₁ hm₁ hcoset₁) hJI
      (fppfHomogeneousQuotientIsoProjectiveOrbitPoints J m₂ hm₂ hcoset₂) g
  simpa only [Over.comp_left, projectiveOrbitQuotientMap,
    representedQuotientTranslation_fppfHomogeneousQuotientIsoProjectiveOrbitPoints_hom_left] using h

/-- For a reduced group `G`, on Chevalley models of `G/P` and `G/Q`, `projectiveOrbitQuotientMap`
also intertwines inverse rational orbit translations. -/
@[reassoc] theorem projectiveOrbitTranslation_inv_projectiveOrbitQuotientMap
    (g : HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k)) :
    (projectiveOrbitTranslation (H := H) m₁ hm₁ g).inv ≫
        projectiveOrbitQuotientMap hJI
          (fppfHomogeneousQuotientIsoProjectiveOrbitPoints I m₁ hm₁ hcoset₁)
          (fppfHomogeneousQuotientIsoProjectiveOrbitPoints J m₂ hm₂ hcoset₂) =
      projectiveOrbitQuotientMap hJI
          (fppfHomogeneousQuotientIsoProjectiveOrbitPoints I m₁ hm₁ hcoset₁)
          (fppfHomogeneousQuotientIsoProjectiveOrbitPoints J m₂ hm₂ hcoset₂) ≫
        (projectiveOrbitTranslation (H := H) m₂ hm₂ g).inv := by
  rw [← Iso.symm_hom, ← projectiveOrbitTranslation_inv_eq_symm,
    ← Iso.symm_hom, ← projectiveOrbitTranslation_inv_eq_symm]
  exact projectiveOrbitTranslation_hom_projectiveOrbitQuotientMap hJI hcoset₁ hcoset₂ g⁻¹

end ChevalleySubgroupMaps

/-- **Closedness of projective orbits descends from `G/P` to `G/Q` for `P ⊆ Q`.** For `J ≤ I`, if a
projective orbit representing `G/P` is closed in projective space, then any projective orbit
representing `G/Q` is also closed in its ambient projective space. -/
theorem isClosed_range_projectiveOrbitMap_of_le_of_fppfHomogeneousQuotient_iso (hJI : J ≤ I)
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
theorem isProper_projectiveOrbitToSpec_iff_of_fppfHomogeneousQuotient_iso (I : HopfIdeal k H)
    (e₁ : CommHopfAlgCat.fppfHomogeneousQuotient H I ≅ projectiveOrbitPointsSheaf (H := H) m₁ hm₁)
    (e₂ : CommHopfAlgCat.fppfHomogeneousQuotient H I ≅ projectiveOrbitPointsSheaf (H := H) m₂ hm₂) :
    IsProper (projectiveOrbitToSpec (H := H) m₁ hm₁) ↔
      IsProper (projectiveOrbitToSpec (H := H) m₂ hm₂) :=
  CommHopfAlgCat.isProper_overHom_iff_of_fppfHomogeneousQuotient_iso H I e₁ e₂

end SubgroupMaps

end TauCeti.Comodule
