/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Group.Affine

import TauCeti.AlgebraicGeometry.AffineScheme.Basic

/-!
# Schemes and morphisms over an affine base

For a scheme with an explicit structure morphism `π : X ⟶ Spec R`, sections over each open
carry an `R`-algebra structure, and restriction maps are algebra homomorphisms. These algebra
structures are supplied explicitly and can be installed locally, without a global instance.

For commutative `R`-algebras `A` and `B`, the scheme `Spec B` is a scheme over `Spec R` through
Mathlib's `AlgebraicGeometry.specOverSpec`. This file identifies the morphisms
`Spec B ⟶ Spec A` over `Spec R`, in the vocabulary `Scheme.Hom.IsOver` of schemes over a base,
with the `R`-algebra homomorphisms `A →ₐ[R] B`. It is the `OverClass` form of Mathlib's
`AlgebraicGeometry.Spec.homEquivAlgHom`, whose compatibility condition is the explicit equation
of structure morphisms.

In particular, for a field `K`, the `K`-points of an affine `K`-scheme `Spec A` in the
functor-of-points sense, the morphisms `Spec K ⟶ Spec A` over `Spec K`, are the
`K`-algebra homomorphisms `A →ₐ[K] K`. A bare scheme morphism `Spec K ⟶ Spec A` is a ring
homomorphism `A →+* K` and need not be `K`-linear.

A morphism `Spec B ⟶ X` over `Spec R` whose image lies in an affine open `Spec A ⟶ X` over
`Spec R` factors through it by a unique `R`-algebra homomorphism `A →ₐ[R] B`.

The same correspondence is stated for Mathlib's bundled spectrum functor
`AlgebraicGeometry.algSpec`, whose morphisms are morphisms in the category of schemes over
`Spec R`: maps `algSpec B ⟶ algSpec A` are the `R`-algebra homomorphisms `A →ₐ[R] B`.

## Main declarations

* `AlgebraicGeometry.Scheme.Hom.sectionsAlgebra`: the algebra of sections over an arbitrary
  open induced by an explicit morphism to `Spec R`.
* `AlgebraicGeometry.Scheme.Hom.algebraMap_sections`: the ring map underlying that algebra.
* `AlgebraicGeometry.Scheme.Hom.fromSpec_toSpec`: an affine open chart respects its induced
  algebra structure over `R`.
* `AlgebraicGeometry.Scheme.Hom.resₐ`: restriction of sections as an algebra homomorphism.
* `AlgebraicGeometry.Scheme.Hom.resₐ_toRingHom`: the underlying restriction ring homomorphism.
* `AlgebraicGeometry.Scheme.Hom.commSq_specMap_algebraMap_self`: a morphism over `Spec R` forms a
  commutative square with the structure morphisms and
  `Spec.map (CommRingCat.ofHom (algebraMap R R))`.
* `TauCeti.AlgebraicGeometry.specOverHomEquivAlgHom`: morphisms `Spec B ⟶ Spec A` over `Spec R`
  are the `R`-algebra homomorphisms `A →ₐ[R] B`.
* `TauCeti.AlgebraicGeometry.existsUnique_spec_map_comp_eq_of_range_subset`: a morphism over
  `Spec R` with image in an affine open over `Spec R` factors through it by a unique algebra
  homomorphism.
* `TauCeti.AlgebraicGeometry.exists_algHom_SpecMap_eq`: a morphism `Spec B ⟶ Spec A` over
  `Spec R` is `Spec.map` of an `R`-algebra homomorphism; `SpecMap_quotient_mk_comp_SpecMap_algHom`
  and `SpecMap_algHom_comp_quotient` compute its restriction to `Spec (B ⧸ I)`.
* `TauCeti.AlgebraicGeometry.algSpecHomEquivAlgHom`: morphisms `algSpec B ⟶ algSpec A` of schemes
  over `Spec R` are the `R`-algebra homomorphisms `A →ₐ[R] B`.
* `TauCeti.AlgebraicGeometry.algSpecObjIsoOverMk`: `algSpec A` is `Spec A` with structure
  morphism `Spec.algebraMap R A`.
-/

public section

open _root_.AlgebraicGeometry CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {R : Type u} [CommRing R] {X : Scheme.{u}} (π : X ⟶ Spec (.of R))

/-- The sections over an open `U` form an `R`-algebra through the structure morphism `π`.
Install this structure locally when using the associated restriction algebra homomorphisms. -/
@[instance_reducible]
noncomputable def sectionsAlgebra (U : X.Opens) : Algebra R Γ(X, U) :=
  ((Scheme.ΓSpecIso (.of R)).inv ≫ π.appLE ⊤ U fun _ _ ↦ trivial).hom.toAlgebra

/-- The algebra map on sections is the pullback from the global sections of `Spec R`. -/
theorem algebraMap_sections (U : X.Opens) :
    @algebraMap R Γ(X, U) _ _ (sectionsAlgebra π U) =
      ((Scheme.ΓSpecIso (.of R)).inv ≫ π.appLE ⊤ U fun _ _ ↦ trivial).hom := by
  rfl

/-- The inclusion `Spec Γ(X, U) ⟶ X` of an affine open respects its induced `R`-algebra. -/
theorem fromSpec_toSpec {U : X.Opens} (hU : IsAffineOpen U) :
    hU.fromSpec ≫ π =
      Spec.map (CommRingCat.ofHom (@algebraMap R Γ(X, U) _ _ (sectionsAlgebra π U))) := by
  rw [IsAffineOpen.fromSpec_comp_eq_SpecMap, algebraMap_sections, CommRingCat.ofHom_hom]

/-- Restriction of sections as a map of the `R`-algebras induced by `π`. -/
noncomputable def resₐ {U V : X.Opens} (h : V ≤ U) :
    letI := sectionsAlgebra π U
    letI := sectionsAlgebra π V
    Γ(X, U) →ₐ[R] Γ(X, V) := by
  letI := sectionsAlgebra π U
  letI := sectionsAlgebra π V
  exact {
    toRingHom := (X.presheaf.map (homOfLE h).op).hom
    commutes' := fun r ↦ by
      exact congr(($(π.appLE_map (U := ⊤) (fun _ _ ↦ trivial) (homOfLE h).op)).hom
        ((Scheme.ΓSpecIso (.of R)).inv.hom r)) }

/-- The ring homomorphism underlying algebraic restriction is presheaf restriction. -/
theorem resₐ_toRingHom {U V : X.Opens} (h : V ≤ U) :
    letI := sectionsAlgebra π U
    letI := sectionsAlgebra π V
    (π.resₐ h).toRingHom = (X.presheaf.map (homOfLE h).op).hom := by
  rfl

end AlgebraicGeometry.Scheme.Hom

namespace AlgebraicGeometry.Spec

/-- The scheme morphism underlying `Spec.homEquivAlgHom.symm φ` is `Spec.map φ`. -/
@[simp]
theorem homEquivAlgHom_symm_apply_val {R A B : Type u}
    [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B] (φ : A →ₐ[R] B) :
    (homEquivAlgHom.symm φ).val = Spec.map (CommRingCat.ofHom φ.toRingHom) :=
  -- The inverse equivalence forgets the algebra structure and applies `Spec.map` definitionally.
  (rfl)

end AlgebraicGeometry.Spec

namespace AlgebraicGeometry.Scheme.Hom

/-- A morphism `f : X ⟶ Y` over `Spec R` forms a commutative square with the structure morphisms
and `Spec.map (CommRingCat.ofHom (algebraMap R R))`. -/
theorem commSq_specMap_algebraMap_self {X Y : Scheme.{u}} (f : X ⟶ Y) (R : Type u) [CommRing R]
    [X.Over (Spec (.of R))] [Y.Over (Spec (.of R))] [hf : f.IsOver (Spec (.of R))] :
    CommSq f (X ↘ Spec (.of R)) (Y ↘ Spec (.of R))
      (Spec.map (CommRingCat.ofHom (algebraMap R R))) := by
  refine ⟨?_⟩
  rw [Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id, Category.comp_id]
  exact hf.comp_over

end AlgebraicGeometry.Scheme.Hom

namespace TauCeti.AlgebraicGeometry

variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]

/-- Morphisms `Spec B ⟶ Spec A` over `Spec R` are the `R`-algebra homomorphisms `A →ₐ[R] B`.
This is Mathlib's `AlgebraicGeometry.Spec.homEquivAlgHom`, with the compatibility with the
structure morphisms expressed by `Scheme.Hom.IsOver`. -/
noncomputable def specOverHomEquivAlgHom :
    {f : Spec (.of B) ⟶ Spec (.of A) // f.IsOver (Spec (.of R))} ≃ (A →ₐ[R] B) :=
  (Equiv.subtypeEquivRight fun f ↦ by
    rw [Scheme.Hom.isOver_iff, specOverSpec_over, specOverSpec_over]).trans
    Spec.homEquivAlgHom

/-- The inverse of `specOverHomEquivAlgHom` applies `Spec` to an algebra homomorphism. -/
@[simp]
theorem coe_specOverHomEquivAlgHom_symm_apply (φ : A →ₐ[R] B) :
    (specOverHomEquivAlgHom.symm φ).val = Spec.map (CommRingCat.ofHom (φ : A →+* B)) :=
  (rfl)

/-- Applying `Spec` to the algebra homomorphism of a morphism over `Spec R` recovers the
morphism. -/
@[simp]
theorem spec_map_specOverHomEquivAlgHom
    (f : {f : Spec (.of B) ⟶ Spec (.of A) // f.IsOver (Spec (.of R))}) :
    Spec.map (CommRingCat.ofHom (specOverHomEquivAlgHom f : A →+* B)) = f.val := by
  rw [← coe_specOverHomEquivAlgHom_symm_apply, Equiv.symm_apply_apply]

/-- A morphism `p : Spec B ⟶ X` over `Spec R` whose image lies in the image of an open immersion
`f : Spec A ⟶ X` over `Spec R` factors through `f` by a unique `R`-algebra homomorphism
`A →ₐ[R] B`. -/
theorem existsUnique_spec_map_comp_eq_of_range_subset {X : Scheme.{u}}
    [X.Over (Spec (.of R))] (f : Spec (.of A) ⟶ X) [IsOpenImmersion f] [f.IsOver (Spec (.of R))]
    (p : Spec (.of B) ⟶ X) [p.IsOver (Spec (.of R))] (h : Set.range p ⊆ Set.range f) :
    ∃! φ : A →ₐ[R] B, Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ f = p := by
  have hlift : (IsOpenImmersion.lift f p h).IsOver (Spec (.of R)) := by
    rw [Scheme.Hom.isOver_iff, ← comp_over f, IsOpenImmersion.lift_fac_assoc, comp_over]
  refine ⟨specOverHomEquivAlgHom ⟨_, hlift⟩, ?_, fun ψ hψ ↦ ?_⟩
  · beta_reduce
    rw [AlgHom.toRingHom_eq_coe, spec_map_specOverHomEquivAlgHom, IsOpenImmersion.lift_fac]
  · rw [← Equiv.symm_apply_eq]
    exact Subtype.ext <|
      (coe_specOverHomEquivAlgHom_symm_apply ψ).trans (IsOpenImmersion.lift_uniq f p h _ hψ)

/-- Every morphism `Spec B ⟶ Spec A` over `Spec R` is `Spec.map` of an `R`-algebra map
`A →ₐ[R] B`: the surjectivity half of Mathlib's `Spec.homEquivAlgHom`, in the form used to
rewrite a morphism of affine schemes. -/
theorem exists_algHom_SpecMap_eq (l : Spec (.of B) ⟶ Spec (.of A))
    (hl : l ≫ Spec.algebraMap R A = Spec.algebraMap R B) :
    ∃ f : A →ₐ[R] B, Spec.map (CommRingCat.ofHom f.toRingHom) = l :=
  ⟨Spec.homEquivAlgHom ⟨l, hl⟩, by
    rw [← Spec.homEquivAlgHom_symm_apply_val, Equiv.symm_apply_apply]⟩

/-- Restricting `Spec B ⟶ Spec A` along `Spec (B ⧸ I) ⟶ Spec B` composes the `R`-algebra map with
the quotient map. -/
theorem SpecMap_quotient_mk_comp_SpecMap_algHom (I : Ideal B) (f : A →ₐ[R] B) :
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ Spec.map (CommRingCat.ofHom f.toRingHom) =
      Spec.map (CommRingCat.ofHom ((Ideal.Quotient.mkₐ R I).comp f).toRingHom) := by
  rw [← Spec.map_comp]
  rfl

/-- The lifting problem for `Spec (B ⧸ I) ⟶ Spec B` over `Spec R` coming from an `R`-algebra map
`A →ₐ[R] B ⧸ I`. -/
theorem SpecMap_algHom_comp_quotient (I : Ideal B) (f : A →ₐ[R] B ⧸ I) :
    Spec.map (CommRingCat.ofHom f.toRingHom) ≫ Spec.algebraMap R A =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ Spec.algebraMap R B := by
  exact (Spec.homEquivAlgHom.symm f).property.trans (by rw [← Spec.map_comp]; rfl)

section algSpec

variable {R : CommRingCat.{u}} {A B : CommAlgCat.{u} R}

variable (A) in
/-- Mathlib's `algSpec R` sends an `R`-algebra `A` to `Spec A` over `Spec R`, with structure
morphism `Spec.algebraMap R A`. The underlying scheme morphism is the identity, since
`algSpec_obj_hom` computes the structure morphism of `algSpec` as `Spec.map` of the algebra map,
which is how `Spec.algebraMap` is defined. -/
noncomputable def algSpecObjIsoOverMk : (algSpec R).obj (op A) ≅ Over.mk (Spec.algebraMap R A) :=
  Over.isoMk (Iso.refl _) (by
    simp only [Iso.refl_hom, algSpec_obj_hom, Over.mk_hom, Spec.algebraMap]
    exact Category.id_comp _)

/-- The underlying scheme morphism of `algSpecObjIsoOverMk A` is the identity of `Spec A`. -/
@[simp]
theorem algSpecObjIsoOverMk_hom_left : (algSpecObjIsoOverMk A).hom.left = 𝟙 _ :=
  (rfl)

/-- The underlying scheme morphism of the inverse of `algSpecObjIsoOverMk A` is the identity of
`Spec A`. -/
@[simp]
theorem algSpecObjIsoOverMk_inv_left : (algSpecObjIsoOverMk A).inv.left = 𝟙 _ :=
  (rfl)

variable (A B) in
/-- Morphisms `algSpec B ⟶ algSpec A` of schemes over `Spec R` are the `R`-algebra homomorphisms
`A →ₐ[R] B`, since Mathlib's `algSpec` is fully faithful. -/
noncomputable def algSpecHomEquivAlgHom :
    ((algSpec R).obj (op B) ⟶ (algSpec R).obj (op A)) ≃ (A →ₐ[R] B) :=
  (algSpec.fullyFaithful.homEquiv (X := op B) (Y := op A)).symm.trans <|
    Quiver.Hom.opEquiv.symm.trans (ConcreteCategory.homEquiv (C := CommAlgCat R))

/-- The inverse of `algSpecHomEquivAlgHom` applies `algSpec` to an algebra homomorphism. -/
@[simp]
theorem algSpecHomEquivAlgHom_symm_apply (φ : A →ₐ[R] B) :
    (algSpecHomEquivAlgHom A B).symm φ = (algSpec R).map (CommAlgCat.ofHom φ).op :=
  (rfl)

/-- Applying `algSpec` to the algebra homomorphism of a morphism over `Spec R` recovers the
morphism. -/
@[simp]
theorem algSpec_map_algSpecHomEquivAlgHom (g : (algSpec R).obj (op B) ⟶ (algSpec R).obj (op A)) :
    (algSpec R).map (CommAlgCat.ofHom (algSpecHomEquivAlgHom A B g)).op = g := by
  rw [← algSpecHomEquivAlgHom_symm_apply, Equiv.symm_apply_apply]

/-- The algebra homomorphism of an affine morphism is its pullback on global functions,
transported along the canonical global-section isomorphisms. -/
theorem algSpecHomEquivAlgHom_eq_appTop
    (p : (algSpec R).obj (op B) ⟶ (algSpec R).obj (op A)) (a : A) :
    algSpecHomEquivAlgHom A B p a =
      (Scheme.ΓSpecIso (CommRingCat.of B)).hom
        (p.left.appTop ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a)) := by
  obtain ⟨φ, rfl⟩ := (algSpecHomEquivAlgHom A B).symm.surjective p
  rw [Equiv.apply_symm_apply, algSpecHomEquivAlgHom_symm_apply, algSpec_map_left]
  -- `algSpec_map_left` leaves the ring map as `Under.Hom.right` through
  -- `commAlgCatEquivUnder`. No public computation lemma reduces that projection, so
  -- unfold the equivalence here to expose the underlying ring map of `φ` for naturality.
  simp only [commAlgCatEquivUnder, Quiver.Hom.unop_op, CommAlgCat.hom_ofHom,
    AlgHom.toUnder, Under.homMk_right]
  have h := ConcreteCategory.congr_hom
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ.toRingHom)) a
  have h' := congrArg (Scheme.ΓSpecIso (CommRingCat.of B)).hom h
  simp only [CategoryTheory.comp_apply, CommRingCat.hom_ofHom, Iso.inv_hom_id_apply] at h'
  exact h'

/-- Composing with `algSpec` of an algebra homomorphism `h` precomposes the algebra homomorphism
with `h`. -/
@[simp]
theorem algSpecHomEquivAlgHom_comp {A' : CommAlgCat.{u} R} (h : A' ⟶ A)
    (g : (algSpec R).obj (op B) ⟶ (algSpec R).obj (op A)) :
    algSpecHomEquivAlgHom A' B (g ≫ (algSpec R).map h.op) =
      (algSpecHomEquivAlgHom A B g).comp h.hom := by
  rw [← Equiv.eq_symm_apply, algSpecHomEquivAlgHom_symm_apply, CommAlgCat.ofHom_comp,
    CommAlgCat.ofHom_hom, op_comp, Functor.map_comp, algSpec_map_algSpecHomEquivAlgHom]

/-- Changing the source test algebra postcomposes the corresponding algebra homomorphism. -/
@[simp]
theorem algSpecHomEquivAlgHom_map_comp {B' : CommAlgCat.{u} R} (h : B ⟶ B')
    (g : (algSpec R).obj (op B) ⟶ (algSpec R).obj (op A)) :
    algSpecHomEquivAlgHom A B' ((algSpec R).map h.op ≫ g) =
      h.hom.comp (algSpecHomEquivAlgHom A B g) := by
  rw [← Equiv.eq_symm_apply, algSpecHomEquivAlgHom_symm_apply, CommAlgCat.ofHom_comp,
    op_comp, Functor.map_comp, algSpec_map_algSpecHomEquivAlgHom, CommAlgCat.ofHom_hom]

end algSpec

end TauCeti.AlgebraicGeometry
