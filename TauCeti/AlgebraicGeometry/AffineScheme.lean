/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Comma.Over.Pullback
import TauCeti.RingTheory.Localization.Tower

/-!
# Affine schemes: the spectrum, fixed points, and actions on global sections

For an affine scheme `X`, Mathlib's `AlgebraicGeometry.Scheme.isoSpec` is the isomorphism
`X ≅ Spec Γ(X, ⊤)`. This file computes the map of global sections of its inverse: it is the
inverse of Mathlib's `AlgebraicGeometry.Scheme.ΓSpecIso`. It is the scheme-level companion of
Mathlib's `AlgebraicGeometry.IsAffineOpen.isoSpec_inv_appTop` for an affine open.

Through this isomorphism, the scheme-theoretic fixed locus of an endomorphism `f` of `X` is the
closed subscheme cut out by the elements `f^*(a) - a` of `Γ(X, ⊤)`. Hence these elements generate
the unit ideal exactly when `f` fixes no point of `X` with values in a nonempty scheme. This is the
form in which a free action of a finite group on an affine scheme enters the theory of invariant
quotients (`TauCeti.AffineInvariantQuotient.etale_projection`), once the group acts on `Γ(X, ⊤)` by
pullback along inverses (`AlgebraicGeometry.Scheme.globalSectionsMulSemiringAction`).

It also shows that for a compatible tower `R → B ↪ R_a`, localizing `B` at `a` gives `R_a`,
so `Spec B ⟶ Spec R` is an isomorphism over the basic open `D(a)`. The map from `R` need not
be injective. This is the local reason why an affine blowup changes nothing away from its center.

Morphisms into an affine scheme are determined by their maps on global sections. Hence if
`ι : X' ⟶ X` is an isomorphism on global sections and `X` is affine, every morphism from `X'` to
an affine scheme extends uniquely along `ι`. Over an affine base `S`, this shows that base change
along any `j : T ⟶ S` is bijective on morphisms between affine `S`-schemes `X` and `Y`, provided
the projection `X ×_S T ⟶ X` is an isomorphism on global sections. This is the algebraic Hartogs
argument for full faithfulness of restriction to an open subscheme whose preimage in `X` carries
the same functions as `X`.

## Main definitions

* `AlgebraicGeometry.Scheme.globalSectionsMulSemiringAction`: a group acting on a scheme `X` acts on
  `Γ(X, ⊤)` by `g • a = (σ g⁻¹)^*(a)`.

## Main results

* `AlgebraicGeometry.Scheme.isoSpec_inv_appTop`: the global sections of `X.isoSpec.inv` are
  `(Scheme.ΓSpecIso Γ(X, ⊤)).inv`.
* `AlgebraicGeometry.IsAffineOpen.fromSpec_comp_eq_SpecMap`: on an affine open `U` of `X`, a
  morphism `X ⟶ Spec R` restricted along `Spec Γ(X, U) ⟶ X` is the spectrum of the ring map
  `R → Γ(X, U)` it induces.
* `AlgebraicGeometry.Scheme.Hom.span_range_appTop_sub_eq_top_iff`: for an endomorphism `f` of an
  affine scheme, the elements `f^*(a) - a` generate the unit ideal if and only if every point of
  `X` fixed by `f` has values in an empty scheme.
* `AlgebraicGeometry.isIso_SpecMap_morphismRestrict_basicOpen_of_injective`: for an `R`-algebra `B`
  embedded in a localization of `R` away from `a`, the morphism `Spec B ⟶ Spec R` restricts to an
  isomorphism over `D(a)`.
* `AlgebraicGeometry.IsAffineOpen.mem_basicOpen_iff_notMem_primeIdealOf`: on an affine open, a
  point lies in the basic open of a section iff the section is not in the point's prime ideal.
* `AlgebraicGeometry.Scheme.Hom.bijective_comp_of_isIso_appTop`: if `ι : X' ⟶ X` is an
  isomorphism on global sections and `X` is affine, then composition with `ι` is a bijection
  from morphisms `X ⟶ Y` to morphisms `X' ⟶ Y`, for every affine `Y`.
* `AlgebraicGeometry.overPullback_map_bijective_of_isIso_appTop`: over an affine base, base change
  is bijective on morphisms between affine schemes when the projection from the base change of
  the source is an isomorphism on global sections.
-/

public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry

/-- The global sections of the inverse of `X ≅ Spec Γ(X, ⊤)`, for an affine scheme `X`. -/
theorem Scheme.isoSpec_inv_appTop (X : Scheme.{u}) [IsAffine X] :
    X.isoSpec.inv.appTop = (Scheme.ΓSpecIso Γ(X, ⊤)).inv := by
  have h : X.isoSpec.inv.appTop ≫ X.isoSpec.hom.appTop = 𝟙 _ := by
    rw [← Scheme.Hom.comp_appTop, Iso.hom_inv_id, Scheme.Hom.id_appTop]
  rw [← Iso.comp_hom_eq_id]
  simpa [Scheme.isoSpec] using h

/-- On an affine open `U` of `X`, the morphism `f : X ⟶ Spec R` restricted along
`Spec Γ(X, U) ⟶ X` is the spectrum of the ring map `R → Γ(X, U)` induced by `f`. -/
theorem IsAffineOpen.fromSpec_comp_eq_SpecMap {X : Scheme.{u}} {R : CommRingCat.{u}}
    (f : X ⟶ Spec R) {U : X.Opens} (hU : IsAffineOpen U) :
    hU.fromSpec ≫ f = Spec.map ((Scheme.ΓSpecIso R).inv ≫ f.appLE ⊤ U le_top) := by
  rw [← IsAffineOpen.SpecMap_appLE_fromSpec f (isAffineOpen_top _) hU le_top,
    IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp]

/-- **Fixed points of an endomorphism of an affine scheme.** For an endomorphism `f` of an affine
scheme `X`, the elements `f^*(a) - a` of `Γ(X, ⊤)` generate the unit ideal if and only if `f` fixes
no point of `X` with values in a nonempty scheme: a point `x : T ⟶ X` with `x ≫ f = x` forces `T`
to be empty. The ideal generated by these elements cuts out the scheme-theoretic fixed locus
of `f`. -/
theorem Scheme.Hom.span_range_appTop_sub_eq_top_iff {X : Scheme.{u}} [IsAffine X] (f : X ⟶ X) :
    Ideal.span (Set.range fun a : Γ(X, ⊤) ↦ f.appTop a - a) = ⊤ ↔
      ∀ (T : Scheme.{u}) (x : T ⟶ X), x ≫ f = x → IsEmpty T := by
  constructor
  · -- the global sections of a fixed point kill every `f^*(a) - a`, hence the unit ideal
    intro h T x hx
    by_contra hT
    have : Nonempty (⊤ : T.Opens) := ⟨⟨(not_isEmpty_iff.1 hT).some, trivial⟩⟩
    have hle : Ideal.span (Set.range fun a : Γ(X, ⊤) ↦ f.appTop a - a) ≤
        RingHom.ker x.appTop.hom := by
      rw [Ideal.span_le]
      rintro _ ⟨a, rfl⟩
      have := congrArg (fun g : T ⟶ X ↦ g.appTop a) hx
      simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply] at this
      simp [SetLike.mem_coe, RingHom.mem_ker, map_sub, this]
    have h1 : x.appTop (1 : Γ(X, ⊤)) = 0 := hle (h ▸ Submodule.mem_top)
    simp at h1
  · -- otherwise the fixed locus `Spec (Γ(X, ⊤) ⧸ I)` is a nonempty scheme of fixed points
    intro h
    by_contra hI
    let I := Ideal.span (Set.range fun a : Γ(X, ⊤) ↦ f.appTop a - a)
    have : Nontrivial (Γ(X, ⊤) ⧸ I) := Ideal.Quotient.nontrivial_iff.2 hI
    refine (h (Spec (.of (Γ(X, ⊤) ⧸ I)))
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ X.isoSpec.inv) ?_).false
      (Nonempty.some inferInstance)
    rw [Category.assoc, ← Scheme.isoSpec_inv_naturality, ← Category.assoc, ← Spec.map_comp]
    congr 2
    ext a
    exact Ideal.Quotient.eq.2 (Ideal.subset_span ⟨a, rfl⟩)

/-- **A group acting on a scheme acts on its global functions**, by pullback along inverses:
`g • a = (σ g⁻¹)^*(a)`. Pullback reverses composition, so pulling back along inverses makes this a
left action. For affine `X`, this is the ring action whose invariant quotient
`TauCeti.AffineInvariantQuotient` forms. -/
@[instance_reducible]
noncomputable def Scheme.globalSectionsMulSemiringAction {X : Scheme.{u}} {G : Type*} [Group G]
    (σ : G →* Aut X) : MulSemiringAction G Γ(X, ⊤) where
  smul g a := (σ g⁻¹).asIso.hom.appTop a
  -- In the two proofs below, `g • a` is `(σ g⁻¹)^*(a)` by the `smul` field above, and `show`
  -- states the goal in that form.
  one_smul a := show (σ 1⁻¹).asIso.hom.appTop a = a by simp
  mul_smul g h a := show (σ (g * h)⁻¹).asIso.hom.appTop a =
      (σ g⁻¹).asIso.hom.appTop ((σ h⁻¹).asIso.hom.appTop a) by
    simp only [mul_inv_rev, map_mul, Aut.mul_asIso, Iso.trans_hom, Scheme.Hom.comp_appTop,
      CommRingCat.comp_apply]
  smul_zero g := map_zero _
  smul_add g := map_add _
  smul_one g := map_one _
  smul_mul g := map_mul _

/-- Under `Scheme.globalSectionsMulSemiringAction σ`, `g` acts on a global function by pullback
along `σ g⁻¹`. -/
@[simp]
theorem Scheme.globalSectionsMulSemiringAction_smul_def {X : Scheme.{u}} {G : Type*} [Group G]
    (σ : G →* Aut X) (g : G) (a : Γ(X, ⊤)) :
    letI := Scheme.globalSectionsMulSemiringAction σ
    g • a = (σ g⁻¹).asIso.hom.appTop a :=
  (rfl)

/-- **`Spec` of an intermediate ring of a localization.** Let `S` be a localization of `R` away
from `a`, and let `B` be an `R`-algebra whose map to `S` is injective, for instance an
`R`-subalgebra of `S`. Then `Spec B ⟶ Spec R` restricts to an isomorphism over the basic open
`D(a)`. -/
theorem isIso_SpecMap_morphismRestrict_basicOpen_of_injective {R B : Type u} {S : Type*}
    [CommRing R] [CommRing B] [CommSemiring S] [Algebra R B] [Algebra B S] [Algebra R S]
    [IsScalarTower R B S] (a : R) [IsLocalization.Away a S]
    (h : Function.Injective (algebraMap B S)) :
    IsIso (Spec.map (CommRingCat.ofHom (algebraMap R B)) ∣_ PrimeSpectrum.basicOpen a) := by
  -- Over `D(a)`, the morphism is `Spec` of the isomorphism `R_a ≅ B_a`.
  have : IsIso (CommRingCat.ofHom (Localization.awayMap (algebraMap R B) a)) :=
    (RingEquiv.ofBijective _
      (IsLocalization.Away.bijective_awayMap_of_injective a h)).toCommRingCatIso.isIso_hom
  exact ((MorphismProperty.isomorphisms Scheme).arrow_mk_iso_iff
    (SpecMapRestrictBasicOpenIso (CommRingCat.ofHom (algebraMap R B)) a)).mpr
    (inferInstanceAs (IsIso (Spec.map _)))

/-- On an affine open `V`, a point `x ∈ V` lies in the basic open of a section `r` iff `r` is not
in the prime ideal of `Γ(X, V)` corresponding to `x`. -/
theorem IsAffineOpen.mem_basicOpen_iff_notMem_primeIdealOf {X : Scheme.{u}} {x : X}
    {V : X.Opens} (hV : IsAffineOpen V) (hx : x ∈ V) (r : Γ(X, V)) :
    x ∈ X.basicOpen r ↔ r ∉ (hV.primeIdealOf ⟨x, hx⟩).asIdeal := by
  let := X.presheaf.algebra_section_stalk ⟨x, hx⟩
  have := hV.isLocalization_stalk ⟨x, hx⟩
  exact (X.mem_basicOpen r x hx).trans
    (IsLocalization.AtPrime.isUnit_to_map_iff (X.presheaf.stalk x) _ r)

/-- Let `ι : X' ⟶ X` be an isomorphism on global sections, with `X` affine. Then every morphism
from `X'` to an affine scheme `Y` extends uniquely along `ι` to a morphism `X ⟶ Y`. -/
theorem Scheme.Hom.bijective_comp_of_isIso_appTop {X' X Y : Scheme.{u}} (ι : X' ⟶ X)
    [IsAffine X] [IsAffine Y] [IsIso ι.appTop] : Function.Bijective fun h : X ⟶ Y ↦ ι ≫ h := by
  refine ⟨fun h h' e ↦ ext_of_isAffine ?_, fun ψ ↦
    ⟨X.isoSpec.hom ≫ Spec.map (ψ.appTop ≫ inv ι.appTop) ≫ Y.isoSpec.inv, ?_⟩⟩
  · have := congrArg Scheme.Hom.appTop e
    simp only [Scheme.Hom.comp_appTop] at this
    exact (cancel_mono ι.appTop).mp this
  · simp only [Scheme.isoSpec_hom, Scheme.toSpecΓ_naturality_assoc, ← Spec.map_comp_assoc,
      Category.assoc, IsIso.inv_hom_id, Category.comp_id]
    rw [← Scheme.toSpecΓ_naturality_assoc, Scheme.toSpecΓ_isoSpec_inv, Category.comp_id]

/-- Let `X` and `Y` be affine schemes over an affine scheme `S`, and `j : T ⟶ S` a morphism such
that the projection `X ×_S T ⟶ X` is an isomorphism on global sections. Then base change along
`j` is a bijection from morphisms `X ⟶ Y` over `S` to morphisms `X ×_S T ⟶ Y ×_S T` over `T`.
For `j` the inclusion of an open subscheme, this is full faithfulness of restriction on such
`X`. -/
theorem overPullback_map_bijective_of_isIso_appTop {S T : Scheme.{u}} [IsAffine S] (j : T ⟶ S)
    {X Y : Over S} [IsAffine X.left] [IsAffine Y.left] [IsIso (pullback.fst X.hom j).appTop] :
    Function.Bijective ((Over.pullback j).map : (X ⟶ Y) → _) := by
  have hY := (pullback.fst X.hom j).bijective_comp_of_isIso_appTop (Y := Y.left)
  have hS := (pullback.fst X.hom j).bijective_comp_of_isIso_appTop (Y := S)
  refine ⟨fun h h' e ↦ Over.OverMorphism.ext (hY.1 ?_), fun φ ↦ ?_⟩
  · simpa using congrArg (fun k ↦ k.left ≫ pullback.fst Y.hom j) e
  · -- Extend the first component of `φ` to `X`; it lies over `S` because maps to `S` extend
    -- uniquely as well.
    obtain ⟨h, hh⟩ := hY.2 (φ.left ≫ pullback.fst Y.hom j)
    have hw : h ≫ Y.hom = X.hom := hS.1 <| by
      simp only at hh ⊢
      rw [reassoc_of% hh, pullback.condition, pullback.condition]
      simpa using congrArg (· ≫ j) (Over.w φ)
    refine ⟨Over.homMk h hw, ?_⟩
    ext1
    apply pullback.hom_ext
    · simpa using hh
    · simpa using (Over.w φ).symm

end AlgebraicGeometry
