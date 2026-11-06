/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.CategoryTheory.Sites.Spaces
public import Mathlib.RingTheory.Ideal.Pointwise
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

Morphisms into an affine scheme are determined by their effect on global sections. Hence, over an
affine base `S`, base change along `j : T ⟶ S` is bijective on morphisms `Y ⟶ Y'` into an affine
`Y'` whenever it does not change the global sections of `Y`.

It also shows that for a compatible tower `R → B ↪ R_a`, localizing `B` at `a` gives `R_a`,
so `Spec B ⟶ Spec R` is an isomorphism over the basic open `D(a)`. The map from `R` need not
be injective. This is the local reason why an affine blowup changes nothing away from its center.

## Main definitions

* `AlgebraicGeometry.Scheme.globalSectionsMulSemiringAction`: a group acting on a scheme `X` acts on
  `Γ(X, ⊤)` by `g • a = (σ g⁻¹)^*(a)`.

## Main results

* `AlgebraicGeometry.Scheme.isoSpec_inv_appTop`: the global sections of `X.isoSpec.inv` are
  `(Scheme.ΓSpecIso Γ(X, ⊤)).inv`.
* `AlgebraicGeometry.IsAffineOpen.fromSpec_comp_eq_SpecMap`: on an affine open `U` of `X`, a
  morphism `X ⟶ Spec R` restricted along `Spec Γ(X, U) ⟶ X` is the spectrum of the ring map
  `R → Γ(X, U)` it induces.
* `AlgebraicGeometry.IsAffineOpen.exists_SpecMap_comp_fromSpec_eq`: a morphism `Spec R ⟶ X` with
  image in an affine open `U` is the spectrum of a ring map `Γ(X, U) ⟶ R` followed by
  `Spec Γ(X, U) ⟶ X`.
* `AlgebraicGeometry.IsAffineOpen.isOpenImmersion_SpecMap_presheaf_map`: for affine opens
  `V ≤ U`, restriction induces an open immersion `Spec Γ(X, V) ⟶ Spec Γ(X, U)`.
* `AlgebraicGeometry.Scheme.Opens.ΓSpecIso_inv_comp_toSpecΓ_appLE`: on an open `U` of `X`, the
  morphism `U ⟶ Spec Γ(X, U)` induces restriction of functions on the sections over opens of `U`.
* `AlgebraicGeometry.Scheme.Hom.isBasis_range_affineOpens_le_preimage`: for `g : S' ⟶ S`, the
  affine opens of `S'` lying over affine opens of `S` form a basis.
* `AlgebraicGeometry.Scheme.toSpecΓ_apply_asIdeal_eq_smul`: for this action, the prime ideal of
  `Γ(X, ⊤)` at the point `σ g x` is the translate by `g` of the prime ideal at `x`.
* `AlgebraicGeometry.Scheme.Hom.span_range_appTop_sub_eq_top_iff`: for an endomorphism `f` of an
  affine scheme, the elements `f^*(a) - a` generate the unit ideal if and only if every point of
  `X` fixed by `f` has values in an empty scheme.
* `AlgebraicGeometry.isIso_SpecMap_morphismRestrict_basicOpen_of_injective`: for an `R`-algebra `B`
  embedded in a localization of `R` away from `a`, the morphism `Spec B ⟶ Spec R` restricts to an
  isomorphism over `D(a)`.
* `AlgebraicGeometry.IsAffineOpen.mem_basicOpen_iff_notMem_primeIdealOf`: on an affine open, a
  point lies in the basic open of a section iff the section is not in the point's prime ideal.
* `AlgebraicGeometry.IsAffineOpen.span_setOf_basicOpen_mem_sieve_eq_top`: the basic opens of an
  affine open `U` lying in a covering sieve of `U` are defined by functions generating the unit
  ideal of `Γ(X, U)`.
* `TauCeti.AlgebraicGeometry.overPullback_map_bijective_of_isIso_appTop`: over an affine base,
  base change along `j : T ⟶ S` is a bijection on morphisms `Y ⟶ Y'` into an affine `Y'` when
  `Γ(Y, 𝒪) → Γ(Y ×_S T, 𝒪)` is an isomorphism.
* `TauCeti.AlgebraicGeometry.Spec.exists_isIso_appTop_eq_comp_of_bijective`: when `S` is
  recovered from its sections over an open `W` of `Spec S`, the sections of a scheme identified
  with `W` over `Spec R` are `S`, compatibly with the maps from `R`.
-/

public section

open CategoryTheory

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

/-- A morphism `f : Spec R ⟶ X` whose image lies in an affine open `U` of `X` is the spectrum of a
ring map `Γ(X, U) ⟶ R` followed by `Spec Γ(X, U) ⟶ X`. -/
theorem IsAffineOpen.exists_SpecMap_comp_fromSpec_eq {X : Scheme.{u}} {R : CommRingCat.{u}}
    (f : Spec R ⟶ X) {U : X.Opens} (hU : IsAffineOpen U) (hf : Set.range f ⊆ U) :
    ∃ φ : Γ(X, U) ⟶ R, Spec.map φ ≫ hU.fromSpec = f := by
  have hle : (⊤ : (Spec R).Opens) ≤ f ⁻¹ᵁ U := fun x _ ↦ hf ⟨x, rfl⟩
  refine ⟨f.appLE U ⊤ hle ≫ (Scheme.ΓSpecIso R).hom, ?_⟩
  rw [Spec.map_comp_assoc, IsAffineOpen.SpecMap_appLE_fromSpec f hU (isAffineOpen_top _) hle,
    IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp_assoc, Iso.inv_hom_id,
    Spec.map_id, Category.id_comp]

/-- Pointwise form of `AlgebraicGeometry.IsAffineOpen.map_fromSpec`: for affine opens `V ≤ U`,
the point of `Spec Γ(X, U)` induced by restriction from a point `p` of `Spec Γ(X, V)` is the
same point of `X` as `p`. -/
theorem IsAffineOpen.map_fromSpec_apply {X : Scheme.{u}} {U V : X.Opens} (hU : IsAffineOpen U)
    (hV : IsAffineOpen V) (f : Opposite.op U ⟶ Opposite.op V) (p : Spec Γ(X, V)) :
    hU.fromSpec (Spec.map (X.presheaf.map f) p) = hV.fromSpec p := by
  rw [← Scheme.Hom.comp_apply, IsAffineOpen.map_fromSpec]

/-- For affine opens `V ≤ U`, restriction of sections induces an open immersion
`Spec Γ(X, V) ⟶ Spec Γ(X, U)`. -/
theorem IsAffineOpen.isOpenImmersion_SpecMap_presheaf_map {X : Scheme.{u}} {U V : X.Opens}
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (f : Opposite.op U ⟶ Opposite.op V) :
    IsOpenImmersion (Spec.map (X.presheaf.map f)) := by
  have : IsOpenImmersion (Spec.map (X.presheaf.map f) ≫ hU.fromSpec) := by
    rw [IsAffineOpen.map_fromSpec _ hV]
    infer_instance
  exact IsOpenImmersion.of_comp _ hU.fromSpec

/-- For an open `U` of `X`, the map `Γ(X, U) ≅ Γ(Spec Γ(X, U), ⊤) ⟶ Γ(U, T)` induced on the
sections over an open `T` of `U` by the canonical morphism `U ⟶ Spec Γ(X, U)` is restriction of
functions from `U` to `T`. -/
theorem Scheme.Opens.ΓSpecIso_inv_comp_toSpecΓ_appLE {X : Scheme.{u}} (U : X.Opens)
    (T : U.toScheme.Opens) :
    (Scheme.ΓSpecIso Γ(X, U)).inv ≫ U.toSpecΓ.appLE ⊤ T le_top = U.ι.appLE U T (by simp) := by
  rw [← Scheme.Hom.appLE_map U.toSpecΓ le_top (homOfLE (le_top : T ≤ ⊤)).op,
    ← Scheme.Hom.appLE_map U.ι (by simp) (homOfLE (le_top : T ≤ ⊤)).op, ← Category.assoc]
  congr 1
  have h₁ : U.toSpecΓ.appLE ⊤ ⊤ le_top = U.toSpecΓ.appTop := Scheme.Hom.appLE_eq_app _
  have h₂ : U.ι.appLE U ⊤ (by simp) = U.topIso.inv := by
    rw [Scheme.Opens.ι_appLE, Scheme.Opens.topIso_inv]
    -- Both sides restrict along the equality `U.ι ''ᵁ ⊤ = U`; morphisms of opens are unique.
    rfl
  rw [h₁, h₂, Scheme.Opens.toSpecΓ_appTop, Iso.inv_hom_id_assoc]

/-- For a morphism `g : S' ⟶ S`, the affine opens of `S'` contained in the preimage of an affine
open of `S` form a basis of the topology of `S'`. -/
theorem Scheme.Hom.isBasis_range_affineOpens_le_preimage {S S' : Scheme.{u}} (g : S' ⟶ S) :
    TopologicalSpace.Opens.IsBasis (Set.range fun i :
      {p : S'.affineOpens × S.affineOpens // (p.1 : S'.Opens) ≤ g ⁻¹ᵁ p.2} ↦
        (i.1.1 : S'.Opens)) := by
  refine TopologicalSpace.Opens.isBasis_iff_nbhd.mpr fun {U x} hx ↦ ?_
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
    S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (g x)) isOpen_univ
  obtain ⟨_, ⟨U', hU', rfl⟩, hxU', hU'U⟩ :=
    S'.isBasis_affineOpens.exists_subset_of_mem_open (⟨hx, hxV⟩ : x ∈ U ⊓ g ⁻¹ᵁ V)
      (U ⊓ g ⁻¹ᵁ V).isOpen
  exact ⟨U', ⟨⟨(⟨U', hU'⟩, ⟨V, hV⟩), fun y hy ↦ (hU'U hy).2⟩, rfl⟩, hxU', fun y hy ↦ (hU'U hy).1⟩

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

open Pointwise in
/-- For the action of `G` on global functions by `g • a = (σ g⁻¹)^*(a)`, the point of
`Spec Γ(X, ⊤)` under `σ g x` has prime ideal the translate by `g` of that of `x`: a function
vanishes at `σ g x` exactly when its translate by `g⁻¹` vanishes at `x`. -/
theorem Scheme.toSpecΓ_apply_asIdeal_eq_smul {X : Scheme.{u}} {G : Type*} [Group G]
    (σ : G →* Aut X) (g : G) (x : X) :
    letI := Scheme.globalSectionsMulSemiringAction σ
    (X.toSpecΓ ((σ g).asIso.hom x)).asIdeal = g • (X.toSpecΓ x).asIdeal := by
  let _ := Scheme.globalSectionsMulSemiringAction σ
  have h := congr($(Scheme.toSpecΓ_naturality (σ g).asIso.hom) x)
  rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply] at h
  ext a
  have hc := PrimeSpectrum.comap_asIdeal (σ g).asIso.hom.appTop.hom (X.toSpecΓ x)
  rw [h, Spec.map_apply, hc, Ideal.mem_comap, Ideal.mem_pointwise_smul_iff_inv_smul_mem,
    Scheme.globalSectionsMulSemiringAction_smul_def, inv_inv]

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

/-- The basic opens of an affine open `U` that lie in a covering sieve of `U` (for the Zariski
topology) are defined by functions generating the unit ideal of `Γ(X, U)`. -/
theorem IsAffineOpen.span_setOf_basicOpen_mem_sieve_eq_top {X : Scheme.{u}} {U : X.Opens}
    (hU : IsAffineOpen U) {S : Sieve U}
    (hS : S ∈ Opens.grothendieckTopology X U) :
    Ideal.span {f : Γ(X, U) | S (homOfLE (X.basicOpen_le f))} = ⊤ := by
  rw [← hU.iSup_basicOpen_eq_self_iff]
  refine le_antisymm (iSup_le fun f ↦ X.basicOpen_le f.1) fun x hx ↦ ?_
  obtain ⟨V, i, hi, hxV⟩ := hS x hx
  obtain ⟨f, hfV, hxf⟩ := hU.exists_basicOpen_le ⟨x, hxV⟩ hx
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨f, S.downward_closed hi (homOfLE hfV)⟩, hxf⟩

end AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry

open _root_.AlgebraicGeometry

/-- Let `j : T ⟶ S` be a morphism to an affine scheme, `Y` a scheme over `S` and `Y'` an affine
scheme over `S`. If restriction of global sections `Γ(Y, 𝒪) → Γ(Y ×_S T, 𝒪)` is an isomorphism,
then base change along `j` is a bijection from morphisms `Y ⟶ Y'` over `S` to morphisms
`Y ×_S T ⟶ Y' ×_S T` over `T`. -/
theorem overPullback_map_bijective_of_isIso_appTop {S T : Scheme.{u}} [IsAffine S] (j : T ⟶ S)
    {Y Y' : Over S} [IsAffine Y'.left] (h : IsIso (Limits.pullback.fst Y.hom j).appTop) :
    Function.Bijective (fun g : Y ⟶ Y' ↦ (Over.pullback j).map g) := by
  set e := Limits.pullback.fst Y.hom j
  have := h
  -- Morphisms from `Y` to an affine scheme are determined by their composites with `e`.
  have hcancel {Z : Scheme.{u}} [IsAffine Z] {g g' : Y.left ⟶ Z} (hg : e ≫ g = e ≫ g') :
      g = g' := by
    refine ext_of_isAffine ((cancel_mono e.appTop).mp ?_)
    rw [← Scheme.Hom.comp_appTop, ← Scheme.Hom.comp_appTop, hg]
  -- The base change of `g` is determined by its composite with the first projection.
  have hmap (g : Y ⟶ Y') : ((Over.pullback j).map g).left ≫ Limits.pullback.fst Y'.hom j =
      e ≫ g.left :=
    Limits.pullback.lift_fst _ _ _
  refine ⟨fun g g' hgg' ↦ ?_, fun φ ↦ ?_⟩
  · refine Over.OverMorphism.ext (hcancel ?_)
    rw [← hmap, ← hmap]
    exact congrArg (fun k ↦ k.left ≫ Limits.pullback.fst Y'.hom j) hgg'
  -- The composite `χ : Y ×_S T ⟶ Y'` corresponds to a ring map `Γ(Y', 𝒪) ⟶ Γ(Y ×_S T, 𝒪)`,
  -- which factors through the isomorphism `Γ(Y, 𝒪) ≅ Γ(Y ×_S T, 𝒪)`.
  set φ' : Limits.pullback Y.hom j ⟶ Limits.pullback Y'.hom j := φ.left
  have hw : φ' ≫ Limits.pullback.snd Y'.hom j = Limits.pullback.snd Y.hom j :=
    Over.w φ
  set χ := φ' ≫ Limits.pullback.fst Y'.hom j with hχ
  let ψ : Y.left ⟶ Y'.left :=
    Y.left.toSpecΓ ≫ Spec.map (χ.appTop ≫ inv e.appTop) ≫ Y'.left.isoSpec.inv
  have hψ : e ≫ ψ = χ := by
    rw [Scheme.toSpecΓ_naturality_assoc, ← Spec.map_comp_assoc, Category.assoc,
      IsIso.inv_hom_id, Category.comp_id, ← Scheme.toSpecΓ_naturality_assoc,
      Scheme.toSpecΓ_isoSpec_inv, Category.comp_id]
  have hψS : ψ ≫ Y'.hom = Y.hom := hcancel <| by
    calc e ≫ ψ ≫ Y'.hom = φ' ≫ Limits.pullback.snd Y'.hom j ≫ j := by
          rw [reassoc_of% hψ, hχ, Category.assoc, Limits.pullback.condition]
      _ = Limits.pullback.snd Y.hom j ≫ j := by rw [reassoc_of% hw]
      _ = e ≫ Y.hom := Limits.pullback.condition.symm
  refine ⟨Over.homMk ψ hψS, Over.OverMorphism.ext ?_⟩
  dsimp only
  apply Limits.pullback.hom_ext
  · exact (hmap _).trans hψ
  · exact (Limits.pullback.lift_snd _ _ _).trans hw.symm

/-- Let `f : R ⟶ S` be a ring map and `W` an open of `Spec S` from which `S` is recovered: the
restriction `Γ(Spec S, ⊤) → Γ(W, ⊤)` is bijective. If a scheme `X` over `Spec R` is identified
with `W` over `Spec R`, then the map `R → Γ(X, ⊤)` induced by `X ⟶ Spec R` is `f` followed by
an isomorphism. -/
theorem Spec.exists_isIso_appTop_eq_comp_of_bijective {R S : CommRingCat.{u}} (f : R ⟶ S)
    {X : Scheme.{u}} (p : X ⟶ Spec R) (W : (Spec S).Opens)
    (hW : Function.Bijective W.ι.appTop) (e : X ≅ W.toScheme)
    (he : e.hom ≫ W.ι ≫ Spec.map f = p) :
    ∃ σ : S ⟶ Γ(X, ⊤), IsIso σ ∧ (Scheme.ΓSpecIso R).inv ≫ p.appTop = f ≫ σ := by
  have : IsIso W.ι.appTop := (ConcreteCategory.isIso_iff_bijective _).mpr hW
  have : IsIso e.hom.appTop := Scheme.Γ.map_isIso e.hom.op
  refine ⟨(Scheme.ΓSpecIso S).inv ≫ W.ι.appTop ≫ e.hom.appTop, inferInstance, ?_⟩
  simp only [← he, Scheme.Hom.comp_appTop, Category.assoc, Scheme.ΓSpecIso_inv_naturality_assoc]

end TauCeti.AlgebraicGeometry
