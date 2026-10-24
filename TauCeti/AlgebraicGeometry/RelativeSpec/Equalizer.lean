/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.RelativeSpec.SubalgebraPresheaf

/-!
# The relative spectrum of an equalizer of quasi-coherent algebras

Let `f g : A ⟶ B` be morphisms of quasi-coherent commutative `𝒪ₓ`-algebras on a scheme `X`.
Over each open `U` of `X`, the sections of `A` on which `f` and `g` agree form a
`Γ(X, U)`-subalgebra `CommMon.equalizerSections f g U` of `Γ(A.X, U)`, stable under restriction:
a presheaf of subalgebras `CommMon.equalizerSubalgebraPresheaf f g`. Over a basic open
`X.basicOpen r` of an affine open `U`, these sections are the localization away from `r` of the
sections over `U`. Hence, exactly as for the relative spectrum `CommMon.relativeSpec` of a
quasi-coherent algebra, the affine schemes `Spec` of these subalgebras glue to the relative
spectrum `(CommMon.equalizerSubalgebraPresheaf f g).relativeSpec` of the equalizer, affine over
`X` (`CommMon.SubalgebraPresheaf.relativeSpec`). The inclusions of the subalgebras glue to a
morphism `(CommMon.equalizerSubalgebraPresheaf f g).relativeSpecπ` from `A.relativeSpec` over
`X`, which coequalizes `CommMon.relativeSpecMap f` and `CommMon.relativeSpecMap g`.

This is the quotient construction of faithfully flat descent: for a descent datum on a scheme
affine over the cover, the candidate descended scheme is the relative spectrum of the functions on
which the two pullbacks to the double overlap agree (`TauCeti.DescentDatum.descended`).

## Main declarations

* `CommMon.equalizerSubalgebraPresheaf f g`: the presheaf of subalgebras
  `U ↦ CommMon.equalizerSections f g U` of the sections of `A`;
* `CommMon.isLocalization_equalizerSections_basicOpen`: over basic opens of affine opens its
  sections are localizations, so that it is coequifibered over the structure presheaf
  (`CommMon.isCoequifibered_equalizerSubalgebraPresheaf`);
* `CommMon.relativeSpecMap_equalizerSubalgebraPresheaf_relativeSpecπ`: the projection to the
  relative spectrum of the equalizer coequalizes `CommMon.relativeSpecMap f` and
  `CommMon.relativeSpecMap g`.

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

/-- The presheaf of subalgebras of sections of `A` on which `f` and `g` agree. -/
def _root_.CategoryTheory.CommMon.equalizerSubalgebraPresheaf : A.SubalgebraPresheaf where
  sections := CommMon.equalizerSections f g
  restrictSections_mem i _ := CommMon.restrictSections_mem_equalizerSections f g i

@[simp]
lemma _root_.CategoryTheory.CommMon.equalizerSubalgebraPresheaf_sections (U : X.Opens) :
    (CommMon.equalizerSubalgebraPresheaf f g).sections U = CommMon.equalizerSections f g U :=
  (rfl)

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
    have : algebraMap E E' (algebraMap Γ(X, U) E r ^ n) =
        algebraMap Γ(X, X.basicOpen r) E' (X.presheaf.map i.op r) ^ n := by
      rw [map_pow]
      congr 1
      exact Subtype.ext (A.restrictSections_algebraMap i r)
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
coequifibered over the structure presheaf: its sections over basic opens are localizations. -/
instance _root_.CategoryTheory.CommMon.isCoequifibered_equalizerSubalgebraPresheaf
    [A.X.IsQuasicoherent] [B.X.IsQuasicoherent] :
    (CommMon.equalizerSubalgebraPresheaf f g).IsCoequifibered :=
  .of_isLocalizationAway fun hU r ↦ CommMon.isLocalization_equalizerSections_basicOpen f g hU r

/-- The morphism `Spec_X(A) ⟶ Spec_X(equalizer of f and g)` coequalizes the morphisms of
relative spectra induced by `f` and `g`. -/
@[reassoc]
lemma _root_.CategoryTheory.CommMon.relativeSpecMap_equalizerSubalgebraPresheaf_relativeSpecπ
    [A.X.IsQuasicoherent] [B.X.IsQuasicoherent] :
    CommMon.relativeSpecMap f ≫ (CommMon.equalizerSubalgebraPresheaf f g).relativeSpecπ =
      CommMon.relativeSpecMap g ≫ (CommMon.equalizerSubalgebraPresheaf f g).relativeSpecπ :=
  CommMon.SubalgebraPresheaf.relativeSpecMap_relativeSpecπ _ fun _ _ hx ↦ hx

end

end TauCeti
