/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.RelativeSpec.Functor

/-!
# The relative spectrum of an equalizer of quasi-coherent algebras

Let `f g : A ⟶ B` be morphisms of quasi-coherent commutative `𝒪ₓ`-algebras on a scheme `X`.
Over each open `U` of `X`, the sections of `A` on which `f` and `g` agree form a
`Γ(X, U)`-subalgebra `CommMon.equalizerSections f g U` of `Γ(A.X, U)`. Over a basic open
`X.basicOpen r` of an affine open `U`, these sections are the localization away from `r` of the
sections over `U`. Hence, exactly as for the relative spectrum `CommMon.relativeSpec` of a
quasi-coherent algebra, the affine schemes `Spec` of these subalgebras glue, with Mathlib's
relative gluing on the small affine Zariski site, to a scheme `CommMon.relativeSpecEqualizer f g`
affine over `X`. The inclusions of the subalgebras glue to a morphism
`CommMon.relativeSpecEqualizerπ f g : A.relativeSpec ⟶ CommMon.relativeSpecEqualizer f g` over
`X`, which coequalizes `CommMon.relativeSpecMap f` and `CommMon.relativeSpecMap g`.

This is the quotient construction of faithfully flat descent: for a descent datum on a scheme
affine over the cover, the candidate descended scheme is the relative spectrum of the functions on
which the two pullbacks to the double overlap agree (`TauCeti.DescentDatum.descended`).

## Main declarations

* `CommMon.equalizerSectionsPresheaf f g`: the presheaf of rings `U ↦ CommMon.equalizerSections
  f g U` on `X`, under the structure presheaf and inside the sections of `A`;
* `CommMon.coequifibered_toEqualizerSectionsPresheaf`: on affine opens it is coequifibered over
  the structure presheaf, i.e. its sections over basic opens are localizations;
* `CommMon.relativeSpecEqualizer f g`, with the affine structure morphism
  `CommMon.relativeSpecEqualizerToBase f g` and the chart description
  `CommMon.isPullback_relativeSpecEqualizerCover`;
* `CommMon.relativeSpecEqualizerπ f g`, with `CommMon.relativeSpecMap_relativeSpecEqualizerπ`.

## References

* The Stacks Project, [Tag 01LL](https://stacks.math.columbia.edu/tag/01LL) (relative
  spectrum via gluing).
* A. Grothendieck, *Revêtements étales et groupe fondamental* (SGA 1), Exposé VIII, §1.
-/

public section

open CategoryTheory Limits Opposite AlgebraicGeometry
open Scheme.AffineZariskiSite

namespace TauCeti

universe u

noncomputable section

variable {X : Scheme.{u}} {A B : CommMon X.Modules}

/-- The algebra map on sections induced by a morphism of commutative `𝒪ₓ`-algebras commutes with
restriction of sections. -/
lemma _root_.CategoryTheory.CommMon.sectionsAlgHom_restrictSections (f : A ⟶ B) {U V : X.Opens}
    (i : V ⟶ U) (x : Γ(A.X, U)) :
    CommMon.sectionsAlgHom f V (A.restrictSections i x) =
      B.restrictSections i (CommMon.sectionsAlgHom f U x) := by
  rw [CommMon.sectionsAlgHom_apply, CommMon.sectionsAlgHom_apply, CommMon.restrictSections_apply]
  exact (PresheafOfModules.naturality_apply f.hom.hom.val i.op x).trans
    (B.restrictSections_apply i _).symm

variable (f g : A ⟶ B)

/-- The `Γ(X, U)`-subalgebra of sections of `A` over `U` on which the algebra morphisms `f` and
`g` agree. -/
def _root_.CategoryTheory.CommMon.equalizerSections (U : X.Opens) :
    Subalgebra Γ(X, U) Γ(A.X, U) :=
  AlgHom.equalizer (CommMon.sectionsAlgHom f U) (CommMon.sectionsAlgHom g U)

variable {f g} in
@[simp]
lemma _root_.CategoryTheory.CommMon.mem_equalizerSections {U : X.Opens} {x : Γ(A.X, U)} :
    x ∈ CommMon.equalizerSections f g U ↔
      CommMon.sectionsAlgHom f U x = CommMon.sectionsAlgHom g U x :=
  Iff.rfl

/-- Restriction of sections preserves the sections on which `f` and `g` agree. -/
lemma _root_.CategoryTheory.CommMon.restrictSections_mem_equalizerSections {U V : X.Opens}
    (i : V ⟶ U) {x : Γ(A.X, U)} (hx : x ∈ CommMon.equalizerSections f g U) :
    A.restrictSections i x ∈ CommMon.equalizerSections f g V := by
  rw [CommMon.mem_equalizerSections] at hx ⊢
  rw [CommMon.sectionsAlgHom_restrictSections, CommMon.sectionsAlgHom_restrictSections, hx]

/-- The presheaf of rings of sections of `A` on which `f` and `g` agree. -/
@[expose]
def _root_.CategoryTheory.CommMon.equalizerSectionsPresheaf : X.Opensᵒᵖ ⥤ CommRingCat.{u} where
  obj U := CommRingCat.of (CommMon.equalizerSections f g U.unop)
  map i := CommRingCat.ofHom ((A.restrictSections i.unop).restrict _ _
    fun _ ↦ CommMon.restrictSections_mem_equalizerSections f g i.unop)
  map_id U := by
    ext x
    exact ConcreteCategory.congr_hom (A.sectionsPresheaf.map_id U) x.1
  map_comp i j := by
    ext x
    exact ConcreteCategory.congr_hom (A.sectionsPresheaf.map_comp i j) x.1

@[simp]
lemma _root_.CategoryTheory.CommMon.equalizerSectionsPresheaf_obj (U : X.Opensᵒᵖ) :
    (CommMon.equalizerSectionsPresheaf f g).obj U =
      CommRingCat.of (CommMon.equalizerSections f g U.unop) :=
  (rfl)

@[simp]
lemma _root_.CategoryTheory.CommMon.equalizerSectionsPresheaf_map {U V : X.Opensᵒᵖ} (i : U ⟶ V) :
    (CommMon.equalizerSectionsPresheaf f g).map i =
      CommRingCat.ofHom ((A.restrictSections i.unop).restrict _ _
        fun _ ↦ CommMon.restrictSections_mem_equalizerSections f g i.unop) :=
  (rfl)

/-- The structure morphism from the structure presheaf of `X`: regular functions act on `A`
through the algebra map, and `f` and `g` agree on their images. -/
def _root_.CategoryTheory.CommMon.toEqualizerSectionsPresheaf :
    X.presheaf ⟶ CommMon.equalizerSectionsPresheaf f g where
  app U := CommRingCat.ofHom (algebraMap Γ(X, U.unop) (CommMon.equalizerSections f g U.unop))
  naturality {U V} i := by
    have h := A.toSectionsPresheaf.naturality i
    rw [CommMon.toSectionsPresheaf_app, CommMon.toSectionsPresheaf_app] at h
    ext r
    apply Subtype.ext
    exact congr($h r)

@[simp]
lemma _root_.CategoryTheory.CommMon.toEqualizerSectionsPresheaf_app (U : X.Opensᵒᵖ) :
    (CommMon.toEqualizerSectionsPresheaf f g).app U =
      CommRingCat.ofHom (algebraMap Γ(X, U.unop) (CommMon.equalizerSections f g U.unop)) :=
  (rfl)

/-- The inclusion of the sections on which `f` and `g` agree into all sections of `A`. -/
def _root_.CategoryTheory.CommMon.equalizerSectionsPresheafι :
    CommMon.equalizerSectionsPresheaf f g ⟶ A.sectionsPresheaf where
  app U := CommRingCat.ofHom (CommMon.equalizerSections f g U.unop).val.toRingHom
  naturality _ _ _ := (rfl)

@[simp]
lemma _root_.CategoryTheory.CommMon.equalizerSectionsPresheafι_app (U : X.Opensᵒᵖ) :
    (CommMon.equalizerSectionsPresheafι f g).app U =
      CommRingCat.ofHom (CommMon.equalizerSections f g U.unop).val.toRingHom :=
  (rfl)

/-- The inclusion of the equalizer sections is compatible with the structure maps from the
structure presheaf. -/
@[reassoc (attr := simp)]
lemma _root_.CategoryTheory.CommMon.toEqualizerSectionsPresheaf_comp_equalizerSectionsPresheafι :
    CommMon.toEqualizerSectionsPresheaf f g ≫ CommMon.equalizerSectionsPresheafι f g =
      A.toSectionsPresheaf := by
  ext U r
  rw [NatTrans.comp_app, CommMon.toSectionsPresheaf_app]
  rfl

/-- The inclusion of the equalizer sections equalizes the morphisms of section rings induced by
`f` and `g`. -/
@[reassoc]
lemma _root_.CategoryTheory.CommMon.equalizerSectionsPresheafι_comp_sectionsPresheafMap :
    CommMon.equalizerSectionsPresheafι f g ≫ CommMon.sectionsPresheafMap f =
      CommMon.equalizerSectionsPresheafι f g ≫ CommMon.sectionsPresheafMap g := by
  ext U x
  simp only [NatTrans.comp_app, CommMon.sectionsPresheafMap_app,
    CommMon.equalizerSectionsPresheafι_app]
  exact x.2

/-- Over the basic open `X.basicOpen r` of an affine open `U`, the sections of `A` on which `f`
and `g` agree are the localization away from `r` of those over `U`. This is the counterpart of
`CommMon.isLocalization_basicOpen` for the equalizer: localization is exact. -/
theorem _root_.CategoryTheory.CommMon.isLocalization_equalizerSections_basicOpen
    [A.X.IsQuasicoherent] [B.X.IsQuasicoherent] {U : X.Opens} (hU : IsAffineOpen U)
    (r : Γ(X, U)) :
    letI := ((A.restrictSections (homOfLE (X.basicOpen_le r))).restrict
      (CommMon.equalizerSections f g U) (CommMon.equalizerSections f g (X.basicOpen r))
      fun _ ↦ CommMon.restrictSections_mem_equalizerSections f g _).toAlgebra
    IsLocalization.Away (algebraMap Γ(X, U) (CommMon.equalizerSections f g U) r)
      (CommMon.equalizerSections f g (X.basicOpen r)) := by
  set i : X.basicOpen r ⟶ U := homOfLE (X.basicOpen_le r)
  set E := CommMon.equalizerSections f g U
  set E' := CommMon.equalizerSections f g (X.basicOpen r)
  let _ : Algebra E E' := ((A.restrictSections i).restrict E E'
    fun _ ↦ CommMon.restrictSections_mem_equalizerSections f g _).toAlgebra
  set a := algebraMap Γ(X, U) Γ(A.X, U) r
  set b := algebraMap Γ(X, U) Γ(B.X, U) r
  have ha : ∀ n : ℕ, ((algebraMap Γ(X, U) E r ^ n : E) : Γ(A.X, U)) = a ^ n := fun n ↦ by
    rw [SubmonoidClass.coe_pow, Subalgebra.coe_algebraMap]
  have hfa : ∀ n : ℕ, CommMon.sectionsAlgHom f U (a ^ n) = b ^ n := fun n ↦ by
    rw [map_pow, AlgHom.commutes]
  have hga : ∀ n : ℕ, CommMon.sectionsAlgHom g U (a ^ n) = b ^ n := fun n ↦ by
    rw [map_pow, AlgHom.commutes]
  have hA := A.isLocalization_basicOpen hU r
  have hB := B.isLocalization_basicOpen hU r
  refine (isLocalization_iff _ _).mpr ⟨?_, ?_, ?_⟩
  · -- The image of `r` is a unit, already in `Γ(X, X.basicOpen r)`.
    rintro ⟨_, n, rfl⟩
    have hres : A.restrictSections i a =
        algebraMap Γ(X, X.basicOpen r) Γ(A.X, X.basicOpen r) (X.presheaf.map i.op r) := by
      have h := A.toSectionsPresheaf.naturality i.op
      rw [CommMon.toSectionsPresheaf_app, CommMon.toSectionsPresheaf_app] at h
      exact congr($h r).symm
    have : algebraMap E E' (algebraMap Γ(X, U) E r ^ n) =
        algebraMap Γ(X, X.basicOpen r) E' (X.presheaf.map i.op r) ^ n := by
      rw [map_pow]
      congr 1
      exact Subtype.ext hres
    rw [this]
    exact ((X.toRingedSpace.isUnit_res_basicOpen r).map _).pow n
  · -- A section `z` with `z * r ^ n = x` has `f x` and `g x` equal away from `r`, hence
    -- `r ^ m * x` lies in the equalizer for some `m`.
    intro z
    let := (A.restrictSections i).toAlgebra
    obtain ⟨⟨x, _, n, rfl⟩, hx⟩ := IsLocalization.surj (Submonoid.powers a) z.1
    simp only [RingHom.algebraMap_toAlgebra] at hx
    have hfg : B.restrictSections i (CommMon.sectionsAlgHom f U x) =
        B.restrictSections i (CommMon.sectionsAlgHom g U x) := by
      rw [← CommMon.sectionsAlgHom_restrictSections, ← CommMon.sectionsAlgHom_restrictSections,
        ← hx, map_mul, map_mul, z.2, CommMon.sectionsAlgHom_restrictSections,
        CommMon.sectionsAlgHom_restrictSections, hfa, hga]
    let := (B.restrictSections i).toAlgebra
    obtain ⟨⟨_, m, rfl⟩, hm⟩ := IsLocalization.exists_of_eq (M := Submonoid.powers b) hfg
    refine ⟨⟨⟨a ^ m * x, ?_⟩, ⟨_, n + m, rfl⟩⟩, Subtype.ext ?_⟩
    · rw [CommMon.mem_equalizerSections, map_mul, map_mul, hfa, hga]
      exact hm
    · simp only [RingHom.algebraMap_toAlgebra, Subalgebra.coe_mul, SubmonoidClass.coe_pow,
        RingHom.coe_restrict_apply, Subalgebra.coe_algebraMap, map_mul, map_pow]
      rw [← hx, map_pow, pow_add]
      ring
  · -- Two sections that agree away from `r` agree after multiplication by a power of `r`.
    intro x y h
    let := (A.restrictSections i).toAlgebra
    obtain ⟨⟨_, n, rfl⟩, hn⟩ := IsLocalization.exists_of_eq (M := Submonoid.powers a)
      (congrArg Subtype.val h)
    refine ⟨⟨_, n, rfl⟩, Subtype.ext ?_⟩
    rw [Subalgebra.coe_mul, Subalgebra.coe_mul, ha]
    exact hn

/-- On the affine opens of `X`, the presheaf of sections on which `f` and `g` agree is
coequifibered over the structure presheaf: its sections over basic opens are localizations. This
is the condition under which Mathlib glues the spectra of its sections
(`AlgebraicGeometry.Scheme.AffineZariskiSite.relativeGluingData`). -/
theorem _root_.CategoryTheory.CommMon.coequifibered_toEqualizerSectionsPresheaf
    [A.X.IsQuasicoherent] [B.X.IsQuasicoherent] :
    ((toOpensFunctor X).op.whiskerLeft
      (CommMon.toEqualizerSectionsPresheaf f g)).Coequifibered := by
  apply coequifibered_iff_forall_isLocalizationAway.mpr
  intro U r
  exact CommMon.isLocalization_equalizerSections_basicOpen f g U.2 r

variable [A.X.IsQuasicoherent] [B.X.IsQuasicoherent]

/-- The relative gluing datum of the equalizer of `f` and `g`: the affine schemes
`Spec (CommMon.equalizerSections f g U)` over the affine opens `U` of `X`. -/
@[expose]
def _root_.CategoryTheory.CommMon.relativeSpecEqualizerGluingData :
    (directedCover X).RelativeGluingData :=
  relativeGluingData (CommMon.coequifibered_toEqualizerSectionsPresheaf f g)

/-- The gluing diagram of the relative spectrum of the equalizer is locally directed. -/
instance _root_.CategoryTheory.CommMon.isLocallyDirected_relativeSpecEqualizerGluingData :
    ((CommMon.relativeSpecEqualizerGluingData f g).functor ⋙ Scheme.forget).IsLocallyDirected :=
  Scheme.Cover.RelativeGluingData.instIsLocallyDirectedI₀CompFunctorForgetOfIsThin ..

/-- The relative spectrum of the equalizer of two morphisms `f g : A ⟶ B` of quasi-coherent
commutative `𝒪ₓ`-algebras, glued from the affine schemes `Spec (CommMon.equalizerSections f g U)`
over the affine opens `U` of `X`. -/
@[expose]
def _root_.CategoryTheory.CommMon.relativeSpecEqualizer : Scheme.{u} :=
  (CommMon.relativeSpecEqualizerGluingData f g).glued

/-- The structure morphism of the relative spectrum of the equalizer. -/
@[expose]
def _root_.CategoryTheory.CommMon.relativeSpecEqualizerToBase :
    CommMon.relativeSpecEqualizer f g ⟶ X :=
  (CommMon.relativeSpecEqualizerGluingData f g).toBase

/-- The open cover of the relative spectrum of the equalizer by the spectra of the equalizer
sections over the affine opens of `X`. -/
@[expose]
def _root_.CategoryTheory.CommMon.relativeSpecEqualizerCover :
    (CommMon.relativeSpecEqualizer f g).OpenCover :=
  (CommMon.relativeSpecEqualizerGluingData f g).cover

instance _root_.CategoryTheory.CommMon.isOpenImmersion_relativeSpecEqualizerCover_f
    (U : X.AffineZariskiSite) : IsOpenImmersion ((CommMon.relativeSpecEqualizerCover f g).f U) :=
  (CommMon.relativeSpecEqualizerCover f g).map_prop U

lemma _root_.CategoryTheory.CommMon.relativeSpecEqualizerCover_X (U : X.AffineZariskiSite) :
    (CommMon.relativeSpecEqualizerCover f g).X U =
      Spec (CommRingCat.of (CommMon.equalizerSections f g U.1)) :=
  (rfl)

/-- Over an affine open `U`, the structure morphism of the relative spectrum of the equalizer is
`Spec` of the structure map `Γ(X, U) ⟶ CommMon.equalizerSections f g U`. -/
@[reassoc]
lemma _root_.CategoryTheory.CommMon.relativeSpecEqualizerCover_f_relativeSpecEqualizerToBase
    (U : X.AffineZariskiSite) :
    (CommMon.relativeSpecEqualizerCover f g).f U ≫ CommMon.relativeSpecEqualizerToBase f g =
      Spec.map ((CommMon.toEqualizerSectionsPresheaf f g).app (op U.1)) ≫ U.2.fromSpec :=
  colimit.ι_desc _ _

/-- The preimage of an affine open `U` under the structure morphism of the relative spectrum of
the equalizer is the image of its chart over `U`. -/
lemma _root_.CategoryTheory.CommMon.relativeSpecEqualizerToBase_preimage
    (U : X.AffineZariskiSite) :
    CommMon.relativeSpecEqualizerToBase f g ⁻¹ᵁ U.1 =
      ((CommMon.relativeSpecEqualizerCover f g).f U).opensRange := by
  have h := (CommMon.relativeSpecEqualizerGluingData f g).toBase_preimage_eq_opensRange_ι U
  simp only [Scheme.Opens.opensRange_ι] at h
  exact h

/-- Over an affine open `U` of `X`, the relative spectrum of the equalizer is
`Spec (CommMon.equalizerSections f g U)`. -/
lemma _root_.CategoryTheory.CommMon.isPullback_relativeSpecEqualizerCover
    (U : X.AffineZariskiSite) :
    IsPullback (Spec.map ((CommMon.toEqualizerSectionsPresheaf f g).app (op U.1)) ≫
        U.2.isoSpec.inv)
      ((CommMon.relativeSpecEqualizerCover f g).f U) U.1.ι
      (CommMon.relativeSpecEqualizerToBase f g) :=
  (CommMon.relativeSpecEqualizerGluingData f g).isPullback_natTrans_ι_toBase U

/-- The structure morphism of the relative spectrum of the equalizer is affine. -/
instance _root_.CategoryTheory.CommMon.isAffineHom_relativeSpecEqualizerToBase :
    IsAffineHom (CommMon.relativeSpecEqualizerToBase f g) := by
  refine isAffineHom_of_forall_exists_isAffineOpen _ fun x ↦ ?_
  obtain ⟨U, hxU⟩ := TopologicalSpace.Opens.mem_iSup.mp
    ((iSup_affineOpens_eq_top X).ge (Set.mem_univ x))
  let V : X.AffineZariskiSite := ⟨U.1, U.2⟩
  refine ⟨V.1, hxU, V.2, ?_⟩
  have : IsAffine ((CommMon.relativeSpecEqualizerCover f g).X V) := by
    rw [CommMon.relativeSpecEqualizerCover_X]
    infer_instance
  rw [CommMon.relativeSpecEqualizerToBase_preimage f g V]
  exact isAffineOpen_opensRange _

/-- Maps out of the relative spectrum of the equalizer are determined on its affine charts. -/
lemma _root_.CategoryTheory.CommMon.relativeSpecEqualizer_hom_ext {T : Scheme.{u}}
    {u v : CommMon.relativeSpecEqualizer f g ⟶ T}
    (h : ∀ U : X.AffineZariskiSite, (CommMon.relativeSpecEqualizerCover f g).f U ≫ u =
      (CommMon.relativeSpecEqualizerCover f g).f U ≫ v) : u = v :=
  colimit.hom_ext h

/-- The morphism `Spec_X(A) ⟶ Spec_X(equalizer of f and g)` over `X`, given on each affine chart
by `Spec` of the inclusion `CommMon.equalizerSections f g U ⟶ Γ(A.X, U)`. -/
def _root_.CategoryTheory.CommMon.relativeSpecEqualizerπ :
    A.relativeSpec ⟶ CommMon.relativeSpecEqualizer f g :=
  colimMap (Functor.whiskerRight
    (((toOpensFunctor X).op.whiskerLeft (CommMon.equalizerSectionsPresheafι f g)).rightOp)
    Scheme.Spec)

/-- On an affine chart, `CommMon.relativeSpecEqualizerπ` is `Spec` of the inclusion of the
equalizer sections. -/
@[reassoc (attr := simp)]
lemma _root_.CategoryTheory.CommMon.relativeSpecCover_f_relativeSpecEqualizerπ
    (U : X.AffineZariskiSite) :
    A.relativeSpecCover.f U ≫ CommMon.relativeSpecEqualizerπ f g =
      Spec.map ((CommMon.equalizerSectionsPresheafι f g).app (op U.1)) ≫
        (CommMon.relativeSpecEqualizerCover f g).f U :=
  ι_colimMap _ U

/-- `CommMon.relativeSpecEqualizerπ` is a morphism over `X`. -/
@[reassoc (attr := simp)]
lemma _root_.CategoryTheory.CommMon.relativeSpecEqualizerπ_relativeSpecEqualizerToBase :
    CommMon.relativeSpecEqualizerπ f g ≫ CommMon.relativeSpecEqualizerToBase f g =
      A.relativeSpecToBase := by
  apply A.relativeSpec_hom_ext
  intro U
  -- Rebind the chart inclusions at their explicit spectrum sources, rather than the
  -- definitionally equal objects of the open covers, so that ordinary rewriting applies.
  let ιA : Spec (CommRingCat.of Γ(A.X, U.1)) ⟶ A.relativeSpec := A.relativeSpecCover.f U
  let ιE : Spec (CommRingCat.of (CommMon.equalizerSections f g U.1)) ⟶
      CommMon.relativeSpecEqualizer f g := (CommMon.relativeSpecEqualizerCover f g).f U
  have hπ : ιA ≫ CommMon.relativeSpecEqualizerπ f g =
      Spec.map ((CommMon.equalizerSectionsPresheafι f g).app (op U.1)) ≫ ιE :=
    CommMon.relativeSpecCover_f_relativeSpecEqualizerπ f g U
  have hE : ιE ≫ CommMon.relativeSpecEqualizerToBase f g =
      Spec.map ((CommMon.toEqualizerSectionsPresheaf f g).app (op U.1)) ≫ U.2.fromSpec :=
    CommMon.relativeSpecEqualizerCover_f_relativeSpecEqualizerToBase f g U
  have hA : ιA ≫ A.relativeSpecToBase =
      Spec.map (A.toSectionsPresheaf.app (op U.1)) ≫ U.2.fromSpec :=
    A.relativeSpecCover_f_relativeSpecToBase U
  have hcomp : (CommMon.toEqualizerSectionsPresheaf f g).app (op U.1) ≫
      (CommMon.equalizerSectionsPresheafι f g).app (op U.1) = A.toSectionsPresheaf.app (op U.1) :=
    (NatTrans.comp_app _ _ _).symm.trans (NatTrans.congr_app
      (CommMon.toEqualizerSectionsPresheaf_comp_equalizerSectionsPresheafι f g) (op U.1))
  have h : ιA ≫ CommMon.relativeSpecEqualizerπ f g ≫ CommMon.relativeSpecEqualizerToBase f g =
      ιA ≫ A.relativeSpecToBase :=
    (Category.assoc _ _ _).symm.trans <|
      ((congrArg (· ≫ _) hπ).trans (Category.assoc _ _ _)).trans <|
        (congrArg (_ ≫ ·) hE).trans <| ((Spec.map_comp_assoc _ _ _).symm.trans
          (congrArg (fun h ↦ Spec.map h ≫ U.2.fromSpec) hcomp)).trans hA.symm
  exact h

/-- `CommMon.relativeSpecEqualizerπ` coequalizes the morphisms of relative spectra induced by
`f` and `g`. -/
@[reassoc]
lemma _root_.CategoryTheory.CommMon.relativeSpecMap_relativeSpecEqualizerπ :
    CommMon.relativeSpecMap f ≫ CommMon.relativeSpecEqualizerπ f g =
      CommMon.relativeSpecMap g ≫ CommMon.relativeSpecEqualizerπ f g := by
  apply B.relativeSpec_hom_ext
  intro U
  -- Rebind the chart inclusions at their explicit spectrum sources, as above.
  let ιA : Spec (CommRingCat.of Γ(A.X, U.1)) ⟶ A.relativeSpec := A.relativeSpecCover.f U
  let ιB : Spec (CommRingCat.of Γ(B.X, U.1)) ⟶ B.relativeSpec := B.relativeSpecCover.f U
  have hπ : ιA ≫ CommMon.relativeSpecEqualizerπ f g =
      Spec.map ((CommMon.equalizerSectionsPresheafι f g).app (op U.1)) ≫
        (CommMon.relativeSpecEqualizerCover f g).f U :=
    CommMon.relativeSpecCover_f_relativeSpecEqualizerπ f g U
  -- On the chart over `U`, both composites are `Spec` of the inclusion of the equalizer
  -- sections followed by the algebra map on sections.
  have key : ∀ h : A ⟶ B, ιB ≫ CommMon.relativeSpecMap h ≫ CommMon.relativeSpecEqualizerπ f g =
      Spec.map ((CommMon.equalizerSectionsPresheafι f g).app (op U.1) ≫
        CommRingCat.ofHom (CommMon.sectionsAlgHom h U.1).toRingHom) ≫
        (CommMon.relativeSpecEqualizerCover f g).f U := fun h ↦
    calc ιB ≫ CommMon.relativeSpecMap h ≫ CommMon.relativeSpecEqualizerπ f g
        = (ιB ≫ CommMon.relativeSpecMap h) ≫ CommMon.relativeSpecEqualizerπ f g :=
          (Category.assoc _ _ _).symm
      _ = Spec.map (CommRingCat.ofHom (CommMon.sectionsAlgHom h U.1).toRingHom) ≫
            ιA ≫ CommMon.relativeSpecEqualizerπ f g :=
          (congrArg (· ≫ _) (CommMon.relativeSpecCover_f_relativeSpecMap h U)).trans
            (Category.assoc _ _ _)
      _ = _ := (congrArg (_ ≫ ·) hπ).trans (Spec.map_comp_assoc _ _ _).symm
  have hι := NatTrans.congr_app (CommMon.equalizerSectionsPresheafι_comp_sectionsPresheafMap f g)
    (op U.1)
  simp only [NatTrans.comp_app, CommMon.sectionsPresheafMap_app] at hι
  have h : ιB ≫ CommMon.relativeSpecMap f ≫ CommMon.relativeSpecEqualizerπ f g =
      ιB ≫ CommMon.relativeSpecMap g ≫ CommMon.relativeSpecEqualizerπ f g :=
    (key f).trans ((congrArg (fun h ↦ Spec.map h ≫ _) hι).trans (key g).symm)
  exact h

end

end TauCeti
