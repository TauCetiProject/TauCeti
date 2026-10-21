/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Invariant.Basic
public import TauCeti.AlgebraicGeometry.RelativeSpec.Equalizer
public import TauCeti.AlgebraicGeometry.RelativeSpec.MorphismProperties

/-!
# Relative invariant quotients by finite groups

Let `A` be a quasi-coherent commutative `𝒪ₓ`-algebra on a scheme `X`, so that `Y = Spec_X(A)` is
an arbitrary scheme affine over `X`, and let a finite group `G` act on `A` by algebra
automorphisms `ρ : G →* Aut A`, that is, on `Y` by automorphisms over `X`. This file constructs
the quotient `Y/G` over `X` by gluing the affine invariant quotients over the affine opens of `X`.

Over each open `U` of `X`, the sections of `A` fixed by every `g : G` form a `Γ(X, U)`-subalgebra
`CommMon.invariantSections ρ U` of `Γ(A.X, U)`. Over a basic open `X.basicOpen r` of an affine
open `U`, these invariants are the localization away from `r` of the invariants over `U`: a section
`x / rⁿ` fixed by every `g` satisfies `rᵐ (g • x - x) = 0` for some `m` depending on `g`, and
since `G` is finite a single `m` works for all `g`, so that `rᵐ x` is invariant. Hence the affine
schemes `Spec (CommMon.invariantSections ρ U)` glue, with Mathlib's relative gluing on the small
affine Zariski site, to a scheme `CommMon.relativeSpecInvariants ρ` affine over `X`. The
inclusions of the invariants glue to the quotient projection
`CommMon.relativeSpecInvariantsπ ρ : Spec_X(A) ⟶ CommMon.relativeSpecInvariants ρ` over `X`,
which is invariant under the action of `G` on `Spec_X(A)`.

Over every affine open `U` of `X`, the projection is the affine invariant quotient
`Spec Γ(A.X, U) ⟶ Spec Γ(A.X, U)ᴳ` (`CommMon.isPullback_relativeSpecInvariantsπ`). Since `G` is
finite, `Γ(A.X, U)` is integral over its invariants, so the projection is integral and
surjective, and it is finite when `Spec_X(A)` is of finite type over `X`. No flatness of the
projection is asserted: for actions which are not free it can fail.

The construction needs no hypothesis on `X`, and in particular the quotient of a scheme affine
over a non-affine base is obtained without choosing a global invariant affine cover: the
preimages of the affine opens of `X` form one. The universal property of the quotient and the
étaleness of the projection for free actions are not proved in this file.

The localization argument is that of `TauCeti.FixedPoints.isLocalization`, and the gluing follows
the relative spectrum of an equalizer, `CommMon.relativeSpecEqualizer`.

## Main definitions

* `CommMon.sectionsAction ρ U`: the action of `G` on `Γ(A.X, U)` by `Γ(X, U)`-algebra
  automorphisms.
* `CommMon.invariantSections ρ U`: the invariant sections over `U`.
* `CommMon.relativeSpecInvariants ρ`: the relative invariant quotient `Spec_X(A)/G`, with its
  affine structure morphism `CommMon.relativeSpecInvariantsToBase ρ` and its charts
  `CommMon.relativeSpecInvariantsCover ρ`.
* `CommMon.relativeSpecInvariantsπ ρ`: the quotient projection.

## Main results

* `CommMon.isLocalization_invariantSections_basicOpen`: invariants commute with localization at
  a basic open of an affine open.
* `CommMon.isPullback_relativeSpecInvariantsCover`: over an affine open `U` of `X`, the quotient
  is `Spec (CommMon.invariantSections ρ U)`.
* `CommMon.relativeSpecMap_relativeSpecInvariantsπ`: the projection is `G`-invariant.
* `CommMon.isPullback_relativeSpecInvariantsπ`: over an affine open of `X`, the projection is the
  affine invariant quotient.
* `CommMon.isIntegral_invariantSections`: the sections are integral over the invariant sections.
* The projection is integral and surjective, and `CommMon.isFinite_relativeSpecInvariantsπ`: it
  is finite when `Spec_X(A)` is locally of finite type over `X`.

## References

* M. Demazure and A. Grothendieck, *Schémas en groupes (SGA 3)*, Exposé V, §1 (quotients of
  affine schemes by finite groups).
* The Stacks Project, [Tag 01LL](https://stacks.math.columbia.edu/tag/01LL) (relative spectrum
  via gluing).
-/

public section

open CategoryTheory Limits Opposite AlgebraicGeometry
open Scheme.AffineZariskiSite

namespace CategoryTheory.CommMon

universe u v

noncomputable section

variable {X : Scheme.{u}}

variable {A : CommMon X.Modules} {G : Type v} [Group G] (ρ : G →* Aut A)

/-- The action of `G` on the sections of `A` over `U` through `ρ`, by `Γ(X, U)`-algebra
automorphisms. -/
def sectionsAction (U : X.Opens) : G →* (Γ(A.X, U) ≃ₐ[Γ(X, U)] Γ(A.X, U)) where
  toFun g := sectionsAlgEquiv (ρ g).asIso U
  map_one' := AlgEquiv.ext fun x ↦ by simp
  map_mul' g h := AlgEquiv.ext fun x ↦ by
    simp only [AlgEquiv.mul_apply, sectionsAlgEquiv_apply, map_mul, Aut.mul_asIso, Iso.trans_hom,
      sectionsAlgHom_comp, AlgHom.comp_apply]

@[simp]
lemma sectionsAction_apply (U : X.Opens) (g : G) (x : Γ(A.X, U)) :
    sectionsAction ρ U g x = sectionsAlgHom (ρ g).asIso.hom U x :=
  sectionsAlgEquiv_apply _ U x

/-- The `Γ(X, U)`-subalgebra of sections of `A` over `U` fixed by every element of `G`. -/
def invariantSections (U : X.Opens) : Subalgebra Γ(X, U) Γ(A.X, U) :=
  ⨅ g, CommMon.equalizerSections (ρ g).asIso.hom (𝟙 A) U

variable {ρ} in
@[simp]
lemma mem_invariantSections {U : X.Opens} {x : Γ(A.X, U)} :
    x ∈ invariantSections ρ U ↔ ∀ g, sectionsAlgHom (ρ g).asIso.hom U x = x := by
  simp [invariantSections]

/-- Restriction of sections preserves invariant sections. -/
lemma restrictSections_mem_invariantSections {U V : X.Opens} (i : V ⟶ U) {x : Γ(A.X, U)}
    (hx : x ∈ invariantSections ρ U) : A.restrictSections i x ∈ invariantSections ρ V := by
  rw [mem_invariantSections] at hx ⊢
  intro g
  rw [sectionsAlgHom_restrictSections, hx g]

/-- The presheaf of rings of invariant sections of `A`. -/
@[expose]
def invariantSectionsPresheaf : X.Opensᵒᵖ ⥤ CommRingCat.{u} where
  obj U := CommRingCat.of (invariantSections ρ U.unop)
  map i := CommRingCat.ofHom ((A.restrictSections i.unop).restrict _ _
    fun _ ↦ restrictSections_mem_invariantSections ρ i.unop)
  map_id U := by
    ext x
    exact ConcreteCategory.congr_hom (A.sectionsPresheaf.map_id U) x.1
  map_comp i j := by
    ext x
    exact ConcreteCategory.congr_hom (A.sectionsPresheaf.map_comp i j) x.1

@[simp]
lemma invariantSectionsPresheaf_obj (U : X.Opensᵒᵖ) :
    (invariantSectionsPresheaf ρ).obj U = CommRingCat.of (invariantSections ρ U.unop) :=
  (rfl)

@[simp]
lemma invariantSectionsPresheaf_map {U V : X.Opensᵒᵖ} (i : U ⟶ V) :
    (invariantSectionsPresheaf ρ).map i =
      CommRingCat.ofHom ((A.restrictSections i.unop).restrict _ _
        fun _ ↦ restrictSections_mem_invariantSections ρ i.unop) :=
  (rfl)

/-- The structure morphism from the structure presheaf of `X`: regular functions act on `A`
through the algebra map, and their images are invariant. -/
def toInvariantSectionsPresheaf : X.presheaf ⟶ invariantSectionsPresheaf ρ where
  app U := CommRingCat.ofHom (algebraMap Γ(X, U.unop) (invariantSections ρ U.unop))
  naturality {U V} i := by
    have h := A.toSectionsPresheaf.naturality i
    rw [toSectionsPresheaf_app, toSectionsPresheaf_app] at h
    ext r
    apply Subtype.ext
    exact congr($h r)

@[simp]
lemma toInvariantSectionsPresheaf_app (U : X.Opensᵒᵖ) :
    (toInvariantSectionsPresheaf ρ).app U =
      CommRingCat.ofHom (algebraMap Γ(X, U.unop) (invariantSections ρ U.unop)) :=
  (rfl)

/-- The inclusion of the invariant sections into all sections of `A`. -/
def invariantSectionsPresheafι : invariantSectionsPresheaf ρ ⟶ A.sectionsPresheaf where
  app U := CommRingCat.ofHom (invariantSections ρ U.unop).val.toRingHom
  naturality _ _ _ := (rfl)

@[simp]
lemma invariantSectionsPresheafι_app (U : X.Opensᵒᵖ) :
    (invariantSectionsPresheafι ρ).app U =
      CommRingCat.ofHom (invariantSections ρ U.unop).val.toRingHom :=
  (rfl)

/-- The inclusion of the invariant sections is compatible with the structure maps from the
structure presheaf. -/
@[reassoc (attr := simp)]
lemma toInvariantSectionsPresheaf_comp_invariantSectionsPresheafι :
    toInvariantSectionsPresheaf ρ ≫ invariantSectionsPresheafι ρ = A.toSectionsPresheaf := by
  ext U r
  rw [NatTrans.comp_app, toSectionsPresheaf_app]
  rfl

/-- The inclusion of the invariant sections is fixed by the morphisms of section rings induced by
the action. -/
@[reassoc]
lemma invariantSectionsPresheafι_comp_sectionsPresheafMap (g : G) :
    invariantSectionsPresheafι ρ ≫ sectionsPresheafMap (ρ g).asIso.hom =
      invariantSectionsPresheafι ρ := by
  ext U x
  rw [NatTrans.comp_app, sectionsPresheafMap_app]
  exact mem_invariantSections.mp x.2 g

/-- Over the basic open `X.basicOpen r` of an affine open `U`, the invariant sections of `A` are
the localization away from `r` of those over `U`. This is the counterpart of
`CommMon.isLocalization_basicOpen` for invariants, and uses that `G` is finite. -/
theorem isLocalization_invariantSections_basicOpen [Finite G] [A.X.IsQuasicoherent]
    {U : X.Opens} (hU : IsAffineOpen U) (r : Γ(X, U)) :
    letI := ((A.restrictSections (homOfLE (X.basicOpen_le r))).restrict
      (invariantSections ρ U) (invariantSections ρ (X.basicOpen r))
      fun _ ↦ restrictSections_mem_invariantSections ρ _).toAlgebra
    IsLocalization.Away (algebraMap Γ(X, U) (invariantSections ρ U) r)
      (invariantSections ρ (X.basicOpen r)) := by
  set i : X.basicOpen r ⟶ U := homOfLE (X.basicOpen_le r)
  set E := invariantSections ρ U
  set E' := invariantSections ρ (X.basicOpen r)
  let _ : Algebra E E' := ((A.restrictSections i).restrict E E'
    fun _ ↦ restrictSections_mem_invariantSections ρ _).toAlgebra
  set a := algebraMap Γ(X, U) Γ(A.X, U) r
  have ha : ∀ n : ℕ, ((algebraMap Γ(X, U) E r ^ n : E) : Γ(A.X, U)) = a ^ n := fun n ↦ by
    rw [SubmonoidClass.coe_pow, Subalgebra.coe_algebraMap]
  have hga : ∀ (g : G) (n : ℕ), sectionsAlgHom (ρ g).asIso.hom U (a ^ n) = a ^ n := fun g n ↦ by
    rw [map_pow, AlgHom.commutes]
  have hA := A.isLocalization_basicOpen hU r
  refine (isLocalization_iff _ _).mpr ⟨?_, ?_, ?_⟩
  · -- The image of `r` is a unit, already in `Γ(X, X.basicOpen r)`.
    rintro ⟨_, n, rfl⟩
    have hres : A.restrictSections i a =
        algebraMap Γ(X, X.basicOpen r) Γ(A.X, X.basicOpen r) (X.presheaf.map i.op r) := by
      have h := A.toSectionsPresheaf.naturality i.op
      rw [toSectionsPresheaf_app, toSectionsPresheaf_app] at h
      exact congr($h r).symm
    have : algebraMap E E' (algebraMap Γ(X, U) E r ^ n) =
        algebraMap Γ(X, X.basicOpen r) E' (X.presheaf.map i.op r) ^ n := by
      rw [map_pow]
      congr 1
      exact Subtype.ext hres
    rw [this]
    exact ((X.toRingedSpace.isUnit_res_basicOpen r).map _).pow n
  · -- A section `z` with `z * r ^ n = x` has `g • x` and `x` equal away from `r`, hence
    -- `r ^ m * x` is invariant for some `m` working for each of the finitely many `g`.
    intro z
    let := (A.restrictSections i).toAlgebra
    obtain ⟨⟨x, _, n, rfl⟩, hx⟩ := IsLocalization.surj (Submonoid.powers a) z.1
    simp only [RingHom.algebraMap_toAlgebra] at hx
    have hg (g : G) : A.restrictSections i (sectionsAlgHom (ρ g).asIso.hom U x) =
        A.restrictSections i x := by
      rw [← sectionsAlgHom_restrictSections, ← hx, map_mul, mem_invariantSections.mp z.2 g,
        sectionsAlgHom_restrictSections, hga]
    have hk (g : G) : ∃ k : ℕ, a ^ k * sectionsAlgHom (ρ g).asIso.hom U x = a ^ k * x := by
      obtain ⟨⟨_, k, rfl⟩, hk⟩ := IsLocalization.exists_of_eq (M := Submonoid.powers a) (hg g)
      exact ⟨k, hk⟩
    choose k hk using hk
    have := Fintype.ofFinite G
    set M := ∑ g, k g
    have hM (g : G) : a ^ M * sectionsAlgHom (ρ g).asIso.hom U x = a ^ M * x := by
      obtain ⟨c, hc⟩ : ∃ c, M = k g + c := Nat.exists_eq_add_of_le
        (Finset.single_le_sum (f := k) (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ g))
      rw [hc, pow_add, mul_comm (a ^ k g), mul_assoc, mul_assoc, hk g]
    refine ⟨⟨⟨a ^ M * x, mem_invariantSections.mpr fun g ↦ ?_⟩, ⟨_, n + M, rfl⟩⟩,
      Subtype.ext ?_⟩
    · rw [map_mul, hga, hM]
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

/-- On the affine opens of `X`, the presheaf of invariant sections is coequifibered over the
structure presheaf: its sections over basic opens are localizations. This is the condition under
which Mathlib glues the spectra of its sections
(`AlgebraicGeometry.Scheme.AffineZariskiSite.relativeGluingData`). -/
theorem coequifibered_toInvariantSectionsPresheaf [Finite G] [A.X.IsQuasicoherent] :
    ((toOpensFunctor X).op.whiskerLeft (toInvariantSectionsPresheaf ρ)).Coequifibered := by
  apply coequifibered_iff_forall_isLocalizationAway.mpr
  intro U r
  exact isLocalization_invariantSections_basicOpen ρ U.2 r

/-- The sections of `A` are integral over the invariant sections, since `G` is finite. -/
theorem isIntegral_invariantSections [Finite G] (U : X.Opens) :
    Algebra.IsIntegral (invariantSections ρ U) Γ(A.X, U) := by
  let _ : MulSemiringAction G Γ(A.X, U) := MulSemiringAction.compHom _ (sectionsAction ρ U)
  -- Through `MulSemiringAction.compHom`, `g • x` is `sectionsAction ρ U g x`; invariant sections
  -- act on `Γ(A.X, U)` by multiplication.
  have : SMulCommClass G (invariantSections ρ U) Γ(A.X, U) :=
    ⟨fun g a x ↦ (map_mul (sectionsAction ρ U g) (a : Γ(A.X, U)) x).trans
      (congrArg (· * _) ((sectionsAction_apply ρ U g a).trans (mem_invariantSections.mp a.2 g)))⟩
  have : Algebra.IsInvariant (invariantSections ρ U) Γ(A.X, U) G :=
    ⟨fun x hx ↦ ⟨⟨x, mem_invariantSections.mpr fun g ↦ (sectionsAction_apply ρ U g x).symm.trans
      (hx g)⟩, rfl⟩⟩
  exact Algebra.IsInvariant.isIntegral _ _ G

variable [Finite G] [A.X.IsQuasicoherent]

/-- The relative gluing datum of the invariant quotient: the affine schemes
`Spec (CommMon.invariantSections ρ U)` over the affine opens `U` of `X`. -/
@[expose]
def relativeSpecInvariantsGluingData : (directedCover X).RelativeGluingData :=
  relativeGluingData (coequifibered_toInvariantSectionsPresheaf ρ)

/-- The gluing diagram of the relative invariant quotient is locally directed. -/
instance isLocallyDirected_relativeSpecInvariantsGluingData :
    ((relativeSpecInvariantsGluingData ρ).functor ⋙ Scheme.forget).IsLocallyDirected :=
  isLocallyDirected_relativeGluingData _

/-- **The relative invariant quotient** `Spec_X(A)/G` of a finite group acting on a quasi-coherent
commutative `𝒪ₓ`-algebra, glued from the affine schemes `Spec (CommMon.invariantSections ρ U)`
over the affine opens `U` of `X`. -/
@[expose]
def relativeSpecInvariants : Scheme.{u} :=
  (relativeSpecInvariantsGluingData ρ).glued

/-- The structure morphism of the relative invariant quotient. -/
@[expose]
def relativeSpecInvariantsToBase : relativeSpecInvariants ρ ⟶ X :=
  (relativeSpecInvariantsGluingData ρ).toBase

/-- The open cover of the relative invariant quotient by the spectra of the invariant sections
over the affine opens of `X`. -/
@[expose]
def relativeSpecInvariantsCover : (relativeSpecInvariants ρ).OpenCover :=
  (relativeSpecInvariantsGluingData ρ).cover

instance isOpenImmersion_relativeSpecInvariantsCover_f (U : X.AffineZariskiSite) :
    IsOpenImmersion ((relativeSpecInvariantsCover ρ).f U) :=
  isOpenImmersion_relativeGluingData_cover_f _ U

lemma relativeSpecInvariantsCover_X (U : X.AffineZariskiSite) :
    (relativeSpecInvariantsCover ρ).X U = Spec (CommRingCat.of (invariantSections ρ U.1)) :=
  relativeGluingData_cover_X _ U

/-- Over an affine open `U`, the structure morphism of the relative invariant quotient is `Spec`
of the structure map `Γ(X, U) ⟶ CommMon.invariantSections ρ U`. -/
@[reassoc]
lemma relativeSpecInvariantsCover_f_relativeSpecInvariantsToBase (U : X.AffineZariskiSite) :
    (relativeSpecInvariantsCover ρ).f U ≫ relativeSpecInvariantsToBase ρ =
      Spec.map ((toInvariantSectionsPresheaf ρ).app (op U.1)) ≫ U.2.fromSpec :=
  relativeGluingData_cover_f_toBase (coequifibered_toInvariantSectionsPresheaf ρ) U

/-- The preimage of an affine open `U` under the structure morphism of the relative invariant
quotient is the image of its chart over `U`. -/
lemma relativeSpecInvariantsToBase_preimage (U : X.AffineZariskiSite) :
    relativeSpecInvariantsToBase ρ ⁻¹ᵁ U.1 = ((relativeSpecInvariantsCover ρ).f U).opensRange :=
  relativeGluingData_toBase_preimage (coequifibered_toInvariantSectionsPresheaf ρ) U

/-- Over an affine open `U` of `X`, the relative invariant quotient is
`Spec (CommMon.invariantSections ρ U)`. -/
lemma isPullback_relativeSpecInvariantsCover (U : X.AffineZariskiSite) :
    IsPullback (Spec.map ((toInvariantSectionsPresheaf ρ).app (op U.1)) ≫ U.2.isoSpec.inv)
      ((relativeSpecInvariantsCover ρ).f U) U.1.ι (relativeSpecInvariantsToBase ρ) :=
  isPullback_relativeGluingData_cover (coequifibered_toInvariantSectionsPresheaf ρ) U

/-- The structure morphism of the relative invariant quotient is affine. -/
instance isAffineHom_relativeSpecInvariantsToBase :
    IsAffineHom (relativeSpecInvariantsToBase ρ) :=
  isAffineHom_relativeGluingData_toBase (coequifibered_toInvariantSectionsPresheaf ρ)

/-- Maps out of the relative invariant quotient are determined on its affine charts. -/
lemma relativeSpecInvariants_hom_ext {T : Scheme.{u}} {f g : relativeSpecInvariants ρ ⟶ T}
    (h : ∀ U : X.AffineZariskiSite, (relativeSpecInvariantsCover ρ).f U ≫ f =
      (relativeSpecInvariantsCover ρ).f U ≫ g) : f = g :=
  colimit.hom_ext h

/-- **The quotient projection** `Spec_X(A) ⟶ Spec_X(A)/G` over `X`, given on each affine chart by
`Spec` of the inclusion `CommMon.invariantSections ρ U ⟶ Γ(A.X, U)`. -/
def relativeSpecInvariantsπ : A.relativeSpec ⟶ relativeSpecInvariants ρ :=
  colimMap (Functor.whiskerRight
    (((toOpensFunctor X).op.whiskerLeft (invariantSectionsPresheafι ρ)).rightOp) Scheme.Spec)

/-- On an affine chart, `CommMon.relativeSpecInvariantsπ` is `Spec` of the inclusion of the
invariant sections. -/
@[reassoc (attr := simp)]
lemma relativeSpecCover_f_relativeSpecInvariantsπ (U : X.AffineZariskiSite) :
    A.relativeSpecCover.f U ≫ relativeSpecInvariantsπ ρ =
      Spec.map ((invariantSectionsPresheafι ρ).app (op U.1)) ≫
        (relativeSpecInvariantsCover ρ).f U :=
  ι_colimMap _ U

/-- `CommMon.relativeSpecInvariantsπ` is a morphism over `X`. -/
@[reassoc (attr := simp)]
lemma relativeSpecInvariantsπ_relativeSpecInvariantsToBase :
    relativeSpecInvariantsπ ρ ≫ relativeSpecInvariantsToBase ρ = A.relativeSpecToBase := by
  apply A.relativeSpec_hom_ext
  intro U
  -- Rebind the chart inclusions and the ring maps at their explicit sources and targets,
  -- rather than the definitionally equal objects of the open covers and of the presheaves, so
  -- that ordinary rewriting applies.
  let ιA : Spec (CommRingCat.of Γ(A.X, U.1)) ⟶ A.relativeSpec := A.relativeSpecCover.f U
  let ιQ : Spec (CommRingCat.of (invariantSections ρ U.1)) ⟶ relativeSpecInvariants ρ :=
    (relativeSpecInvariantsCover ρ).f U
  let iU : CommRingCat.of (invariantSections ρ U.1) ⟶ CommRingCat.of Γ(A.X, U.1) :=
    (invariantSectionsPresheafι ρ).app (op U.1)
  let eU : CommRingCat.of Γ(X, U.1) ⟶ CommRingCat.of (invariantSections ρ U.1) :=
    (toInvariantSectionsPresheaf ρ).app (op U.1)
  let aU : CommRingCat.of Γ(X, U.1) ⟶ CommRingCat.of Γ(A.X, U.1) :=
    A.toSectionsPresheaf.app (op U.1)
  have hπ : ιA ≫ relativeSpecInvariantsπ ρ = Spec.map iU ≫ ιQ :=
    relativeSpecCover_f_relativeSpecInvariantsπ ρ U
  have hQ : ιQ ≫ relativeSpecInvariantsToBase ρ = Spec.map eU ≫ U.2.fromSpec :=
    relativeSpecInvariantsCover_f_relativeSpecInvariantsToBase ρ U
  have hA : ιA ≫ A.relativeSpecToBase = Spec.map aU ≫ U.2.fromSpec :=
    A.relativeSpecCover_f_relativeSpecToBase U
  have hcomp : eU ≫ iU = aU :=
    NatTrans.congr_app (toInvariantSectionsPresheaf_comp_invariantSectionsPresheafι ρ) (op U.1)
  change ιA ≫ relativeSpecInvariantsπ ρ ≫ relativeSpecInvariantsToBase ρ =
    ιA ≫ A.relativeSpecToBase
  rw [reassoc_of% hπ, hQ, ← Spec.map_comp_assoc, hcomp, hA]

/-- The quotient projection is invariant under the action of `G` on `Spec_X(A)`. -/
@[reassoc (attr := simp)]
lemma relativeSpecMap_relativeSpecInvariantsπ (g : G) :
    relativeSpecMap (ρ g).asIso.hom ≫ relativeSpecInvariantsπ ρ = relativeSpecInvariantsπ ρ := by
  apply A.relativeSpec_hom_ext
  intro U
  -- Rebind the chart inclusions and the ring maps at their explicit sources, as above.
  let ιA : Spec (CommRingCat.of Γ(A.X, U.1)) ⟶ A.relativeSpec := A.relativeSpecCover.f U
  let ιQ : Spec (CommRingCat.of (invariantSections ρ U.1)) ⟶ relativeSpecInvariants ρ :=
    (relativeSpecInvariantsCover ρ).f U
  let iU : CommRingCat.of (invariantSections ρ U.1) ⟶ CommRingCat.of Γ(A.X, U.1) :=
    (invariantSectionsPresheafι ρ).app (op U.1)
  let gU : CommRingCat.of Γ(A.X, U.1) ⟶ CommRingCat.of Γ(A.X, U.1) :=
    CommRingCat.ofHom (sectionsAlgHom (ρ g).asIso.hom U.1).toRingHom
  have hπ : ιA ≫ relativeSpecInvariantsπ ρ = Spec.map iU ≫ ιQ :=
    relativeSpecCover_f_relativeSpecInvariantsπ ρ U
  have hg : ιA ≫ relativeSpecMap (ρ g).asIso.hom = Spec.map gU ≫ ιA :=
    relativeSpecCover_f_relativeSpecMap _ U
  have hι : iU ≫ gU = iU := by
    have h := NatTrans.congr_app (invariantSectionsPresheafι_comp_sectionsPresheafMap ρ g) (op U.1)
    rwa [NatTrans.comp_app, sectionsPresheafMap_app] at h
  change ιA ≫ relativeSpecMap (ρ g).asIso.hom ≫ relativeSpecInvariantsπ ρ =
    ιA ≫ relativeSpecInvariantsπ ρ
  rw [reassoc_of% hg, hπ, ← Spec.map_comp_assoc, hι]

/-- Over an affine open `U` of `X`, the quotient projection is the affine invariant quotient
`Spec Γ(A.X, U) ⟶ Spec Γ(A.X, U)ᴳ`: the square formed with the two charts over `U` is a pullback
square. -/
lemma isPullback_relativeSpecInvariantsπ (U : X.AffineZariskiSite) :
    IsPullback (Spec.map ((invariantSectionsPresheafι ρ).app (op U.1))) (A.relativeSpecCover.f U)
      ((relativeSpecInvariantsCover ρ).f U) (relativeSpecInvariantsπ ρ) := by
  refine IsPullback.of_right ?_ (relativeSpecCover_f_relativeSpecInvariantsπ ρ U).symm
    (isPullback_relativeSpecInvariantsCover ρ U)
  rw [relativeSpecInvariantsπ_relativeSpecInvariantsToBase, ← Spec.map_comp_assoc,
    ← NatTrans.comp_app, toInvariantSectionsPresheaf_comp_invariantSectionsPresheafι]
  exact A.isPullback_relativeSpecCover U

/-- A morphism property which is local on the target holds for the quotient projection exactly
when it holds for the affine invariant quotients over the affine opens of `X`. -/
private lemma relativeSpecInvariantsπ_iff (P : MorphismProperty Scheme.{u})
    [IsZariskiLocalAtTarget P] :
    P (relativeSpecInvariantsπ ρ) ↔ ∀ U : X.AffineZariskiSite,
      P (Spec.map (CommRingCat.ofHom (algebraMap (invariantSections ρ U.1) Γ(A.X, U.1)))) := by
  rw [IsZariskiLocalAtTarget.iff_of_openCover (P := P) (relativeSpecInvariantsCover ρ)]
  refine forall_congr' fun (U : X.AffineZariskiSite) ↦ ?_
  have h := (isPullback_relativeSpecInvariantsπ ρ U).flip
  have key : P (pullback.snd (relativeSpecInvariantsπ ρ) ((relativeSpecInvariantsCover ρ).f U)) ↔
      P (Spec.map ((invariantSectionsPresheafι ρ).app (op U.1))) := by
    rw [← h.isoPullback_hom_snd, P.cancel_left_of_respectsIso]
    -- The two sides differ only in the proofs of `HasPullback` they carry.
    exact Iff.rfl
  -- `Scheme.Cover.pullbackHom` is defined as this second projection.
  exact key

/-- The quotient projection is integral. -/
instance : IsIntegralHom (relativeSpecInvariantsπ ρ) := by
  have : IsZariskiLocalAtTarget @IsIntegralHom.{u} :=
    @HasAffineProperty.instIsZariskiLocalAtTarget _ _ IsIntegralHom.hasAffineProperty
  refine (relativeSpecInvariantsπ_iff ρ @IsIntegralHom).mpr fun U ↦ ?_
  have := isIntegral_invariantSections ρ U.1
  exact IsIntegralHom.SpecMap_iff.mpr (algebraMap_isIntegral_iff.mpr inferInstance)

/-- The quotient projection is surjective. -/
instance : Surjective (relativeSpecInvariantsπ ρ) := by
  refine (relativeSpecInvariantsπ_iff ρ @Surjective).mpr fun U ↦ ?_
  have := isIntegral_invariantSections ρ U.1
  exact ⟨Algebra.IsIntegral.comap_surjective _ _⟩

/-- The quotient projection is finite when `Spec_X(A)` is locally of finite type over `X`. -/
theorem isFinite_relativeSpecInvariantsπ [LocallyOfFiniteType A.relativeSpecToBase] :
    IsFinite (relativeSpecInvariantsπ ρ) := by
  observe hasFiniteAffineProperty : HasAffineProperty @IsFinite.{u}
    (fun X _ f _ ↦ IsAffine X ∧ RingHom.Finite (f.appTop).hom)
  have : IsZariskiLocalAtTarget @IsFinite.{u} :=
    @HasAffineProperty.instIsZariskiLocalAtTarget _ _ hasFiniteAffineProperty
  refine (relativeSpecInvariantsπ_iff ρ @IsFinite).mpr fun U ↦ ?_
  have := isIntegral_invariantSections ρ U.1
  have : Algebra.FiniteType Γ(X, U.1) Γ(A.X, U.1) :=
    (A.relativeSpec_finiteType_iff.mp inferInstance) U.1 U.2
  have : Algebra.FiniteType (invariantSections ρ U.1) Γ(A.X, U.1) :=
    Algebra.FiniteType.of_restrictScalars_finiteType Γ(X, U.1) _ _
  exact IsFinite.SpecMap_iff _ |>.mpr (RingHom.finite_algebraMap.mpr Algebra.IsIntegral.finite)

end

end CategoryTheory.CommMon
