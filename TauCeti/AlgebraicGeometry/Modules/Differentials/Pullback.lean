/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Differentials.Quasicoherent
public import TauCeti.AlgebraicGeometry.Modules.Pullback.Sections
import Mathlib.RingTheory.Kaehler.TensorProduct
import TauCeti.AlgebraicGeometry.Modules.AffineRestriction
import TauCeti.AlgebraicGeometry.Modules.Pullback.BaseChange

/-!
# Pullback, cotangent map, and base change of relative differentials

Let `f : X ⟶ Y` be a morphism of schemes fitting into a commutative square over affine bases
`Spec S ⟶ Spec R` for a ring homomorphism `R → S`. Differentiating pulled-back local functions on
`X` defines an `R`-derivation from `𝒪_Y` into `f_* Ω_{X/S}`; by the universal property of `Ω_{Y/R}`
and the pullback–pushforward adjunction, this corresponds to a canonical morphism of `𝒪_X`-modules
`relativeDifferentialsPullbackHom : f^* Ω_{Y/R} ⟶ Ω_{X/S}` sending the pulled-back differential of
a local function `b` on `Y` to `d (f^♯ b)`.

Two special cases play central roles:

1. **The cotangent map over a fixed base `R`** (`cotangentMap R f : f^* Ω_{Y/R} ⟶ Ω_{X/R}`), for
   any morphism `f : X ⟶ Y` over `Spec R`. Over compatible affine opens `V ⊆ Y` and `U ⊆ f⁻¹ V`,
   its map on sections is `KaehlerDifferential.mapBaseChange` on
   `Γ(X, U) ⊗[Γ(Y, V)] Ω[Γ(Y, V)⁄R] → Ω[Γ(X, U)⁄R]`. Along an open immersion, `cotangentMap`
   recovers the restriction isomorphism `relativeDifferentialsRestrictIso`.

2. **Arbitrary base change of relative differentials** (`relativeDifferentialsBaseChangeIso`), when
   `X' = X ×_{Spec R} Spec S` is a cartesian base change along any ring map `R → S` (with no
   flatness or finiteness assumption). On the affine open cover `{g⁻¹ U}` induced by the affine
   opens of `X`, the section map identifies with `KaehlerDifferential.tensorKaehlerEquiv`, so
   `relativeDifferentialsPullbackHom` is an isomorphism `g^* Ω_{X/R} ≅ Ω_{X'/S}`.

Functoriality of `relativeDifferentialsPullbackHom` along composite squares implies that
`cotangentMap` commutes with arbitrary base change `R → S`
(`cotangentSourceBaseChangeIso_hom_comp_cotangentMap`).

## Main declarations

* `TauCeti.AlgebraicGeometry.pushforwardDerivationOfCommSq`: pushforward of an `S`-derivation along
  a morphism `f : X ⟶ Y` compatible with `Spec S ⟶ Spec R`, viewed as an `R`-derivation on `Y`;
* `TauCeti.AlgebraicGeometry.relativeDifferentialsPullbackHom`: the canonical morphism
  `f^* Ω_{Y/R} ⟶ Ω_{X/S}` for a commutative square over `Spec S ⟶ Spec R`;
* `TauCeti.AlgebraicGeometry.cotangentMap`: the cotangent map `f^* Ω_{Y/R} ⟶ Ω_{X/R}` for a
  morphism over `Spec R`;
* `TauCeti.AlgebraicGeometry.pullbackRelativeDifferentialsSectionsEquiv`: affine identification
  `Γ(X, U) ⊗[Γ(Y, V)] Ω[Γ(Y, V)⁄R] ≃ₗ[Γ(X, U)] Γ(f^* Ω_{Y/R}, U)` for `U ≤ f⁻¹ V`;
* `TauCeti.AlgebraicGeometry.isIso_relativeDifferentialsPullbackHom` and
  `TauCeti.AlgebraicGeometry.relativeDifferentialsBaseChangeIso`: arbitrary base change
  `g^* Ω_{X/R} ≅ Ω_{X'/S}` for a cartesian square over `Spec S ⟶ Spec R`;
* `TauCeti.AlgebraicGeometry.cotangentSourceBaseChangeIso_hom_comp_cotangentMap`: compatibility of
  `cotangentMap` with arbitrary base change `R → S`.

## References

* [The Stacks Project, Tag 01UM](https://stacks.math.columbia.edu/tag/01UM), especially Lemma
  29.33.4 (Tag 01UP, base change of differentials) and Lemma 29.33.8 (Tag 01UV, first exact
  sequence of differentials).
* R. Hartshorne, *Algebraic Geometry*, Proposition II.8.10 and Proposition II.8.11.
-/

public section

open CategoryTheory Limits AlgebraicGeometry Opposite TopologicalSpace
open scoped TensorProduct

namespace TauCeti.AlgebraicGeometry

universe u

noncomputable section

section CommSq

private lemma pullbackPushforwardAdjunction_homEquiv_app_apply
    {X Y : Scheme.{u}} (f : X ⟶ Y) {M : Y.Modules} {N : X.Modules}
    (φ : (Scheme.Modules.pullback f).obj M ⟶ N) (V : Y.Opens) (s : Γ(M, V)) :
    (((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv M N φ).app V) s =
      φ.app (f ⁻¹ᵁ V) (f.pullbackSections M V s) := by
  rw [Adjunction.homEquiv_unit]
  simp only [Scheme.Modules.Hom.comp_app, Scheme.Modules.pushforward_map_app]
  exact (ConcreteCategory.comp_apply _ _ s).trans
    (congrArg (φ.app (f ⁻¹ᵁ V)) (f.pullbackSections_apply M V s).symm)

private lemma pullbackComp_inv_comp_app_pullbackSections
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) {M : Z.Modules} {N : Y.Modules} {P : X.Modules}
    (α : (Scheme.Modules.pullback g).obj M ⟶ N) (β : (Scheme.Modules.pullback f).obj N ⟶ P)
    (W : Z.Opens) (s : Γ(M, W)) :
    ((Scheme.Modules.pullbackComp f g).inv.app M ≫ (Scheme.Modules.pullback f).map α ≫ β).app
        ((f ≫ g) ⁻¹ᵁ W) ((f ≫ g).pullbackSections M W s) =
      β.app (f ⁻¹ᵁ (g ⁻¹ᵁ W))
        (f.pullbackSections N (g ⁻¹ᵁ W)
          (α.app (g ⁻¹ᵁ W) (g.pullbackSections M W s))) := by
  simp only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply]
  rw [Scheme.Hom.pullbackSections_comp]
  -- `((f ≫ g) ⁻¹ᵁ W)` is definitionally `f ⁻¹ᵁ (g ⁻¹ᵁ W)`.
  exact congrArg (β.app (f ⁻¹ᵁ (g ⁻¹ᵁ W)))
    (Scheme.Hom.pullbackSections_naturality f _ (g ⁻¹ᵁ W) α (g.pullbackSections M W s))

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
  {X Y : Scheme.{u}} [X.Over (Spec (.of S))] [Y.Over (Spec (.of R))] {f : X ⟶ Y}

/-- Given a morphism `f : X ⟶ Y` fitting into a commutative square over `Spec S ⟶ Spec R`, an
`S`-derivation of `𝒪_X` into `M` induces an `R`-derivation of `𝒪_Y` into `f_* M` by differentiating
pulled-back local functions. -/
def pushforwardDerivationOfCommSq
    (C : CommSq f (X ↘ Spec (.of S)) (Y ↘ Spec (.of R))
      (Spec.map (CommRingCat.ofHom (algebraMap R S))))
    {M : X.Modules} (d : M.Derivation S) :
    ((Scheme.Modules.pushforward f).obj M).Derivation R where
  d {U} := d.d.comp (f.app U.unop).hom.toAddMonoidHom
  d_mul a b := by
    -- Pushforward restricts scalars along `f.app`; expose that action and additive composition.
    change d.d (f.app _ (a * b)) = f.app _ a • d.d (f.app _ b) +
      f.app _ b • d.d (f.app _ a)
    rw [map_mul, d.d_mul]
  d_map {U V} i a := by
    -- The underlying presheaf of `f_* M` precomposes with preimage on opens.
    change d.d (f.app V.unop (Y.presheaf.map i a)) =
      M.val.map ((Opens.map f.base).map i.unop).op (d.d (f.app U.unop a))
    rw [← ConcreteCategory.comp_apply, f.naturality i, ConcreteCategory.comp_apply, d.d_map]
    rfl
  d_app {U} r := by
    -- Expose the additive composition so we can rewrite the pulled-back constant from `R` via `S`.
    change d.d (f.app U.unop ((Y.baseRingToStructurePresheaf R).app U r)) = 0
    let : X.Over (Spec (.of R)) :=
      ⟨(X ↘ Spec (.of S)) ≫ Spec.map (CommRingCat.ofHom (algebraMap R S))⟩
    have : f.IsOver (Spec (.of R)) := ⟨C.w⟩
    have hr : f.app U.unop ((Y.baseRingToStructurePresheaf R).app U r) =
        (X.baseRingToStructurePresheaf S).app (op (f ⁻¹ᵁ U.unop)) (algebraMap R S r) :=
      (Scheme.Modules.app_baseRingToStructurePresheaf R f U.unop r).trans
        (X.baseRingToStructurePresheaf_app_algebraMap (R := R) (S := S) rfl
          (f ⁻¹ᵁ U.unop) r).symm
    rw [hr]
    exact d.d_app (algebraMap R S r)

/-- Evaluating `pushforwardDerivationOfCommSq` on a local function `a` differentiates `f.app U a`.
-/
@[simp]
lemma pushforwardDerivationOfCommSq_d
    (C : CommSq f (X ↘ Spec (.of S)) (Y ↘ Spec (.of R))
      (Spec.map (CommRingCat.ofHom (algebraMap R S))))
    {M : X.Modules} (d : M.Derivation S) (U : Y.Opens) (a : Γ(Y, U)) :
    (pushforwardDerivationOfCommSq C d).d a = d.d (f.app U a) :=
  (rfl)

/-- The canonical morphism `f^* Ω_{Y/R} ⟶ Ω_{X/S}` associated to a commutative square over
`Spec S ⟶ Spec R`, obtained by transposing the universal `S`-derivation of `X` across the universal
property of `Ω_{Y/R}` and the pullback–pushforward adjunction. -/
def relativeDifferentialsPullbackHom
    (C : CommSq f (X ↘ Spec (.of S)) (Y ↘ Spec (.of R))
      (Spec.map (CommRingCat.ofHom (algebraMap R S)))) :
    (Scheme.Modules.pullback f).obj (Y.relativeDifferentials R) ⟶ X.relativeDifferentials S :=
  ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).symm
    ((Y.relativeDifferentialsHomEquiv R _).symm
      (pushforwardDerivationOfCommSq C (X.universalDerivation S)))

private lemma pullbackPushforwardAdjunction_homEquiv_relativeDifferentialsPullbackHom
    (C : CommSq f (X ↘ Spec (.of S)) (Y ↘ Spec (.of R))
      (Spec.map (CommRingCat.ofHom (algebraMap R S)))) :
    (Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _
        (relativeDifferentialsPullbackHom C) =
      (Y.relativeDifferentialsHomEquiv R _).symm
        (pushforwardDerivationOfCommSq C (X.universalDerivation S)) :=
  Equiv.apply_symm_apply _ _

/-- On sections over `f⁻¹ V`, `relativeDifferentialsPullbackHom` sends the pulled-back differential
of `b ∈ Γ(Y, V)` to `d (f.app V b)`. -/
@[simp]
theorem relativeDifferentialsPullbackHom_app_pullbackSections_d
    (C : CommSq f (X ↘ Spec (.of S)) (Y ↘ Spec (.of R))
      (Spec.map (CommRingCat.ofHom (algebraMap R S))))
    (V : Y.Opens) (b : Γ(Y, V)) :
    (relativeDifferentialsPullbackHom C).app (f ⁻¹ᵁ V)
        (f.pullbackSections (Y.relativeDifferentials R) V
          ((Y.universalDerivation R).d (X := op V) b)) =
      (X.universalDerivation S).d (X := op (f ⁻¹ᵁ V)) (f.app V b) := by
  refine (pullbackPushforwardAdjunction_homEquiv_app_apply f
    (relativeDifferentialsPullbackHom C) V _).symm.trans ?_
  refine (congrArg (fun g ↦ g.app V ((Y.universalDerivation R).d (X := op V) b))
    (pullbackPushforwardAdjunction_homEquiv_relativeDifferentialsPullbackHom C)).trans ?_
  exact congrArg (fun D ↦ D.d b)
    (Y.relativeDifferentialsHomEquiv_symm_fac R
      (pushforwardDerivationOfCommSq C (X.universalDerivation S)))

/-- On sections over any open `U ≤ f⁻¹ V`, `relativeDifferentialsPullbackHom` sends the pulled-back
differential of `b ∈ Γ(Y, V)` to `d (f.appLE V U hUV b)`. -/
@[simp]
theorem relativeDifferentialsPullbackHom_app_pullbackSectionsLE_d
    (C : CommSq f (X ↘ Spec (.of S)) (Y ↘ Spec (.of R))
      (Spec.map (CommRingCat.ofHom (algebraMap R S))))
    (V : Y.Opens) (U : X.Opens) (hUV : U ≤ f ⁻¹ᵁ V) (b : Γ(Y, V)) :
    (relativeDifferentialsPullbackHom C).app U
        (f.pullbackSectionsLE (Y.relativeDifferentials R) V U hUV
          ((Y.universalDerivation R).d (X := op V) b)) =
      (X.universalDerivation S).d (X := op U) (f.appLE V U hUV b) := by
  -- Use transitivity rather than `rw` because `(Y.universalDerivation R).d` mentions `.val` on a
  -- `Y.Modules` object, which does not pass `rw`'s implicit-transparency check.
  refine (congrArg ((relativeDifferentialsPullbackHom C).app U)
    (f.pullbackSectionsLE_apply (Y.relativeDifferentials R) V U hUV _)).trans ?_
  refine ((relativeDifferentialsPullbackHom C).mapPresheaf.naturality_apply (homOfLE hUV).op
    (f.pullbackSections (Y.relativeDifferentials R) V
      ((Y.universalDerivation R).d (X := op V) b))).trans ?_
  refine (congrArg ((X.relativeDifferentials S).presheaf.map (homOfLE hUV).op)
    (relativeDifferentialsPullbackHom_app_pullbackSections_d C V b)).trans ?_
  exact ((X.universalDerivation S).d_map (homOfLE hUV).op (f.app V b)).symm

/-- Two morphisms out of `f^* Ω_{Y/R}` agree as soon as they agree on the pulled-back differentials
`f.pullbackSections _ V (d b)` of all local functions `b` on `Y`. -/
theorem pullback_relativeDifferentials_hom_ext {R : Type u} [CommRing R]
    {X Y : Scheme.{u}} [Y.Over (Spec (.of R))] {f : X ⟶ Y} {M : X.Modules}
    {φ ψ : (Scheme.Modules.pullback f).obj (Y.relativeDifferentials R) ⟶ M}
    (h : ∀ (V : Y.Opens) (b : Γ(Y, V)),
      φ.app (f ⁻¹ᵁ V) (f.pullbackSections (Y.relativeDifferentials R) V
        ((Y.universalDerivation R).d (X := op V) b)) =
      ψ.app (f ⁻¹ᵁ V) (f.pullbackSections (Y.relativeDifferentials R) V
        ((Y.universalDerivation R).d (X := op V) b))) :
    φ = ψ := by
  apply ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).injective
  apply Y.relativeDifferentials_hom_ext R
  intro V b
  exact (pullbackPushforwardAdjunction_homEquiv_app_apply f φ V.unop _).trans
    ((h V.unop b).trans (pullbackPushforwardAdjunction_homEquiv_app_apply f ψ V.unop _).symm)

/-- Along the identity morphism and identity ring map, `relativeDifferentialsPullbackHom` is the
canonical unitor `(𝟙 X)^* Ω_{X/R} ⟶ Ω_{X/R}`. -/
@[simp]
theorem relativeDifferentialsPullbackHom_id (R : Type u) [CommRing R]
    (X : Scheme.{u}) [X.Over (Spec (.of R))]
    (C : CommSq (𝟙 X) (X ↘ Spec (.of R)) (X ↘ Spec (.of R))
      (Spec.map (CommRingCat.ofHom (algebraMap R R)))) :
    relativeDifferentialsPullbackHom C =
      (Scheme.Modules.pullbackId X).hom.app (X.relativeDifferentials R) := by
  apply pullback_relativeDifferentials_hom_ext
  intro V b
  have hid : (Scheme.Modules.pullbackPushforwardAdjunction (𝟙 X)).homEquiv _ _
      ((Scheme.Modules.pullbackId X).hom.app (X.relativeDifferentials R)) =
      𝟙 (X.relativeDifferentials R) := by
    rw [Adjunction.homEquiv_unit]
    have hconj := CategoryTheory.unit_conjugateEquiv Adjunction.id
      (Scheme.Modules.pullbackPushforwardAdjunction (𝟙 X))
      (Scheme.Modules.pullbackId X).hom (X.relativeDifferentials R)
    rw [Scheme.Modules.conjugateEquiv_pullbackId_hom] at hconj
    exact hconj.symm
  have happ := (pullbackPushforwardAdjunction_homEquiv_app_apply (𝟙 X)
    ((Scheme.Modules.pullbackId X).hom.app (X.relativeDifferentials R)) V
      ((X.universalDerivation R).d (X := op V) b)).symm.trans
    (congrArg (fun g ↦ g.app V ((X.universalDerivation R).d (X := op V) b)) hid)
  refine (relativeDifferentialsPullbackHom_app_pullbackSections_d C V b).trans ?_
  refine Eq.trans ?_ happ.symm
  -- `(𝟙 X).app V` and `(𝟙 (X.relativeDifferentials R)).app V` both act as identities on sections.
  rfl

/-- `relativeDifferentialsPullbackHom` is compatible with composition of commutative squares, up to
`Scheme.Modules.pullbackComp`. -/
@[reassoc]
theorem relativeDifferentialsPullbackHom_comp
    {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra S T] [Algebra R T]
    {X Y Z : Scheme.{u}} [X.Over (Spec (.of T))] [Y.Over (Spec (.of S))] [Z.Over (Spec (.of R))]
    {f : X ⟶ Y} {g : Y ⟶ Z}
    (C_f : CommSq f (X ↘ Spec (.of T)) (Y ↘ Spec (.of S))
      (Spec.map (CommRingCat.ofHom (algebraMap S T))))
    (C_g : CommSq g (Y ↘ Spec (.of S)) (Z ↘ Spec (.of R))
      (Spec.map (CommRingCat.ofHom (algebraMap R S))))
    (C_fg : CommSq (f ≫ g) (X ↘ Spec (.of T)) (Z ↘ Spec (.of R))
      (Spec.map (CommRingCat.ofHom (algebraMap R T)))) :
    relativeDifferentialsPullbackHom C_fg =
      (Scheme.Modules.pullbackComp f g).inv.app (Z.relativeDifferentials R) ≫
        (Scheme.Modules.pullback f).map (relativeDifferentialsPullbackHom C_g) ≫
        relativeDifferentialsPullbackHom C_f := by
  apply pullback_relativeDifferentials_hom_ext
  intro W c
  refine (relativeDifferentialsPullbackHom_app_pullbackSections_d C_fg W c).trans ?_
  refine Eq.trans ?_
    (pullbackComp_inv_comp_app_pullbackSections f g
      (relativeDifferentialsPullbackHom C_g) (relativeDifferentialsPullbackHom C_f) W _).symm
  refine Eq.trans ?_
    (congrArg (fun x ↦ (relativeDifferentialsPullbackHom C_f).app (f ⁻¹ᵁ (g ⁻¹ᵁ W))
      (f.pullbackSections _ (g ⁻¹ᵁ W) x))
      (relativeDifferentialsPullbackHom_app_pullbackSections_d C_g W c)).symm
  exact (relativeDifferentialsPullbackHom_app_pullbackSections_d C_f (g ⁻¹ᵁ W) (g.app W c)).symm

/-- `relativeDifferentialsPullbackHom` respects equality of morphisms via `pullbackCongr`. -/
@[reassoc]
theorem relativeDifferentialsPullbackHom_congr
    {f' : X ⟶ Y} (h : f = f')
    (C : CommSq f (X ↘ Spec (.of S)) (Y ↘ Spec (.of R))
      (Spec.map (CommRingCat.ofHom (algebraMap R S))))
    (C' : CommSq f' (X ↘ Spec (.of S)) (Y ↘ Spec (.of R))
      (Spec.map (CommRingCat.ofHom (algebraMap R S)))) :
    (Scheme.Modules.pullbackCongr h).hom.app (Y.relativeDifferentials R) ≫
        relativeDifferentialsPullbackHom C' =
      relativeDifferentialsPullbackHom C := by
  subst h
  have : C = C' := Subsingleton.elim _ _
  subst this
  simp [Scheme.Modules.pullbackCongr]

end CommSq

section CotangentMap

variable (R : Type u) [CommRing R] {X Y Z : Scheme.{u}}
  [X.Over (Spec (.of R))] [Y.Over (Spec (.of R))] [Z.Over (Spec (.of R))]

private lemma commSq_of_isOver (f : X ⟶ Y) [hf : f.IsOver (Spec (.of R))] :
    CommSq f (X ↘ Spec (.of R)) (Y ↘ Spec (.of R))
      (Spec.map (CommRingCat.ofHom (algebraMap R R))) := by
  refine ⟨?_⟩
  rw [Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id, Category.comp_id]
  exact hf.comp_over

/-- The **cotangent map** `f^* Ω_{Y/R} ⟶ Ω_{X/R}` associated to a morphism `f : X ⟶ Y` over
`Spec R`: the first morphism in the relative cotangent exact sequence
`f^* Ω_{Y/R} ⟶ Ω_{X/R} ⟶ Ω_{X/Y} ⟶ 0`. -/
def cotangentMap (f : X ⟶ Y) [f.IsOver (Spec (.of R))] :
    (Scheme.Modules.pullback f).obj (Y.relativeDifferentials R) ⟶ X.relativeDifferentials R :=
  relativeDifferentialsPullbackHom (commSq_of_isOver R f)

/-- On `f⁻¹ V`, `cotangentMap R f` sends the pulled-back differential of `b ∈ Γ(Y, V)` to
`d (f.app V b)`. -/
@[simp]
theorem cotangentMap_app_pullbackSections_d (f : X ⟶ Y) [f.IsOver (Spec (.of R))]
    (V : Y.Opens) (b : Γ(Y, V)) :
    (cotangentMap R f).app (f ⁻¹ᵁ V)
        (f.pullbackSections (Y.relativeDifferentials R) V
          ((Y.universalDerivation R).d (X := op V) b)) =
      (X.universalDerivation R).d (X := op (f ⁻¹ᵁ V)) (f.app V b) :=
  relativeDifferentialsPullbackHom_app_pullbackSections_d _ V b

/-- On `U ≤ f⁻¹ V`, `cotangentMap R f` sends the pulled-back differential of `b ∈ Γ(Y, V)` to
`d (f.appLE V U hUV b)`. -/
@[simp]
theorem cotangentMap_app_pullbackSectionsLE_d (f : X ⟶ Y) [f.IsOver (Spec (.of R))]
    (V : Y.Opens) (U : X.Opens) (hUV : U ≤ f ⁻¹ᵁ V) (b : Γ(Y, V)) :
    (cotangentMap R f).app U
        (f.pullbackSectionsLE (Y.relativeDifferentials R) V U hUV
          ((Y.universalDerivation R).d (X := op V) b)) =
      (X.universalDerivation R).d (X := op U) (f.appLE V U hUV b) :=
  relativeDifferentialsPullbackHom_app_pullbackSectionsLE_d _ V U hUV b

/-- The cotangent map of the identity morphism is the canonical unitor
`(𝟙 X)^* Ω_{X/R} ⟶ Ω_{X/R}`. -/
@[simp]
theorem cotangentMap_id :
    cotangentMap R (𝟙 X) = (Scheme.Modules.pullbackId X).hom.app (X.relativeDifferentials R) :=
  relativeDifferentialsPullbackHom_id R X _

/-- The cotangent map of a composite `f ≫ g` over `Spec R` factors into the pullback of
`cotangentMap R g` followed by `cotangentMap R f`. -/
@[reassoc]
theorem cotangentMap_comp (f : X ⟶ Y) (g : Y ⟶ Z)
    [f.IsOver (Spec (.of R))] [g.IsOver (Spec (.of R))] :
    cotangentMap R (f ≫ g) =
      (Scheme.Modules.pullbackComp f g).inv.app (Z.relativeDifferentials R) ≫
        (Scheme.Modules.pullback f).map (cotangentMap R g) ≫
        cotangentMap R f :=
  relativeDifferentialsPullbackHom_comp
    (commSq_of_isOver R f) (commSq_of_isOver R g) (commSq_of_isOver R (f ≫ g))

/-- Equal morphisms over `Spec R` induce compatible cotangent maps. -/
@[reassoc]
theorem cotangentMap_congr {f f' : X ⟶ Y} (h : f = f')
    [f.IsOver (Spec (.of R))] [f'.IsOver (Spec (.of R))] :
    (Scheme.Modules.pullbackCongr h).hom.app (Y.relativeDifferentials R) ≫ cotangentMap R f' =
      cotangentMap R f :=
  relativeDifferentialsPullbackHom_congr h _ _

/-- Along an open immersion over `Spec R`, `cotangentMap R f` agrees with the restriction
isomorphism `relativeDifferentialsRestrictIso R f` through `restrictFunctorIsoPullback`. -/
theorem cotangentMap_of_isOpenImmersion (f : X ⟶ Y) [f.IsOver (Spec (.of R))]
    [IsOpenImmersion f] :
    cotangentMap R f =
      (Scheme.Modules.restrictFunctorIsoPullback f).inv.app (Y.relativeDifferentials R) ≫
        (relativeDifferentialsRestrictIso R f).hom := by
  apply ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).injective
  have hA :
      (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app (Y.relativeDifferentials R) ≫
        (Scheme.Modules.pushforward f).map
          ((Scheme.Modules.restrictFunctorIsoPullback f).inv.app (Y.relativeDifferentials R)) =
      (Scheme.Modules.restrictAdjunction f).unit.app (Y.relativeDifferentials R) :=
    Adjunction.unit_leftAdjointUniq_hom_app
      (Scheme.Modules.pullbackPushforwardAdjunction f)
      (Scheme.Modules.restrictAdjunction f) (Y.relativeDifferentials R)
  rw [cotangentMap, pullbackPushforwardAdjunction_homEquiv_relativeDifferentialsPullbackHom,
    Adjunction.homEquiv_unit, Functor.map_comp, ← Category.assoc, hA]
  apply Y.relativeDifferentials_hom_ext R
  intro V b
  refine (congrArg (fun D : ((Scheme.Modules.pushforward f).obj
      (X.relativeDifferentials R)).Derivation R ↦ D.d (X := V) b)
    (Y.relativeDifferentialsHomEquiv_symm_fac R _)).trans ?_
  -- Expose the evaluation of `restrictAdjunction.unit ≫ pushforward.map` on sections over `V`.
  change (X.universalDerivation R).d (X := op (f ⁻¹ᵁ V.unop)) (f.app V.unop b) =
    (relativeDifferentialsRestrictIso R f).hom.app (f ⁻¹ᵁ V.unop)
      ((Y.relativeDifferentials R).val.map (homOfLE (f.image_preimage_le V.unop)).op
        ((Y.universalDerivation R).d (X := V) b))
  have hd := (Y.universalDerivation R).d_map (homOfLE (f.image_preimage_le V.unop)).op b
  refine Eq.trans ?_
    (congrArg ((relativeDifferentialsRestrictIso R f).hom.app (f ⁻¹ᵁ V.unop)) hd.symm).symm
  refine Eq.trans ?_
    (relativeDifferentialsRestrictIso_hom_app_d R f (f ⁻¹ᵁ V.unop) _).symm
  apply congrArg (X.universalDerivation R).d
  rw [Scheme.Hom.appIso_hom, CommRingCat.comp_apply,
    ← CommRingCat.comp_apply (Y.presheaf.map (homOfLE (f.image_preimage_le V.unop)).op),
    f.naturality, CommRingCat.comp_apply, ← X.presheaf.map_comp_apply,
    Subsingleton.elim (_ ≫ _ : op (f ⁻¹ᵁ V.unop) ⟶ op (f ⁻¹ᵁ V.unop)) (𝟙 _), X.presheaf.map_id]
  rfl

/-- Along an open immersion over `Spec R`, `cotangentMap R f` is an isomorphism. -/
instance isIso_cotangentMap_of_isOpenImmersion (f : X ⟶ Y) [f.IsOver (Spec (.of R))]
    [IsOpenImmersion f] : IsIso (cotangentMap R f) := by
  rw [cotangentMap_of_isOpenImmersion]
  infer_instance

end CotangentMap

section AffineCharts

private lemma kaehlerBaseChange_linearMap_ext
    {R A B M : Type u} [CommRing R] [CommRing A] [CommRing B] [AddCommGroup M]
    [Algebra R A] [Algebra A B] [Module A M] [Module B M] [IsScalarTower A B M]
    {L₁ L₂ : B ⊗[A] Ω[A⁄R] →ₗ[B] M}
    (h : ∀ a : A, L₁ (1 ⊗ₜ[A] KaehlerDifferential.D R A a) =
      L₂ (1 ⊗ₜ[A] KaehlerDifferential.D R A a)) :
    L₁ = L₂ := by
  let : Module R M := Module.compHom M (algebraMap R A)
  have : IsScalarTower R A M := .of_algebraMap_smul fun _ _ ↦ rfl
  let j : Ω[A⁄R] →ₗ[A] B ⊗[A] Ω[A⁄R] :=
    { toFun ω := 1 ⊗ₜ[A] ω
      map_add' := TensorProduct.tmul_add 1
      map_smul' c ω := by rw [TensorProduct.tmul_smul]; rfl }
  have hj : L₁.restrictScalars A ∘ₗ j = L₂.restrictScalars A ∘ₗ j :=
    Derivation.liftKaehlerDifferential_unique _ _ (Derivation.ext fun a ↦ h a)
  refine TensorProduct.AlgebraTensorModule.ext fun b ω ↦ ?_
  have hb : b ⊗ₜ[A] ω = b • j ω := by
    change b ⊗ₜ[A] ω = b • (1 ⊗ₜ[A] ω)
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [hb, map_smul, map_smul]
  exact congrArg (b • ·) congr($hj ω)

/-- Over affine opens `V` of `Y` and `U ≤ f⁻¹ V` of `X`, the sections of `f^* Ω_{Y/R}` over `U`
identify with the tensor product `Γ(X, U) ⊗[Γ(Y, V)] Ω[Γ(Y, V)⁄R]`. -/
def pullbackRelativeDifferentialsSectionsEquiv (R : Type u) [CommRing R]
    {X Y : Scheme.{u}} [Y.Over (Spec (.of R))] (f : X ⟶ Y)
    (V : Y.affineOpens) (U : X.affineOpens) (hUV : U.1 ≤ f ⁻¹ᵁ V.1) :
    letI : Algebra R Γ(Y, V) := ((Y.baseRingToStructurePresheaf R).app (op V.1)).hom.toAlgebra
    letI : Algebra Γ(Y, V) Γ(X, U) := (f.appLE V.1 U.1 hUV).hom.toAlgebra
    Γ(X, U) ⊗[Γ(Y, V)] Ω[Γ(Y, V)⁄R] ≃ₗ[Γ(X, U)]
      Γ((Scheme.Modules.pullback f).obj (Y.relativeDifferentials R), U.1) := by
  letI : Algebra R Γ(Y, V) := ((Y.baseRingToStructurePresheaf R).app (op V.1)).hom.toAlgebra
  letI : Algebra Γ(Y, V) Γ(X, U) := (f.appLE V.1 U.1 hUV).hom.toAlgebra
  letI : Module Γ(Y, V) Γ((Scheme.Modules.pullback f).obj (Y.relativeDifferentials R), U.1) :=
    Module.compHom _ (algebraMap Γ(Y, V) Γ(X, U))
  haveI : IsScalarTower Γ(Y, V) Γ(X, U)
      Γ((Scheme.Modules.pullback f).obj (Y.relativeDifferentials R), U.1) :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  let φ : Γ(Y.relativeDifferentials R, V.1) →ₗ[Γ(Y, V)]
      Γ((Scheme.Modules.pullback f).obj (Y.relativeDifferentials R), U.1) :=
    { toFun := f.pullbackSectionsLE (Y.relativeDifferentials R) V.1 U.1 hUV
      map_add' := map_add _
      map_smul' := (f.pullbackSectionsLE (Y.relativeDifferentials R) V.1 U.1 hUV).map_smulₛₗ }
  have hBC : IsBaseChange Γ(X, U) φ :=
    f.isBaseChange_pullbackSectionsLE (Y.relativeDifferentials R) V.2 U.2 hUV
      (fun _ ↦ rfl) φ (fun _ ↦ rfl)
  exact ((relativeDifferentialsSectionsEquiv R Y V).baseChange Γ(Y, V) Γ(X, U)).trans hBC.equiv

/-- `pullbackRelativeDifferentialsSectionsEquiv` sends `a ⊗ₜ D b` to `a` times the pulled-back
differential `d b`. -/
@[simp]
theorem pullbackRelativeDifferentialsSectionsEquiv_tmul_D (R : Type u) [CommRing R]
    {X Y : Scheme.{u}} [Y.Over (Spec (.of R))] (f : X ⟶ Y)
    (V : Y.affineOpens) (U : X.affineOpens) (hUV : U.1 ≤ f ⁻¹ᵁ V.1)
    (a : Γ(X, U)) (b : Γ(Y, V)) :
    letI : Algebra R Γ(Y, V) := ((Y.baseRingToStructurePresheaf R).app (op V.1)).hom.toAlgebra
    letI : Algebra Γ(Y, V) Γ(X, U) := (f.appLE V.1 U.1 hUV).hom.toAlgebra
    pullbackRelativeDifferentialsSectionsEquiv R f V U hUV
        (a ⊗ₜ[Γ(Y, V)] KaehlerDifferential.D R Γ(Y, V) b) =
      a • f.pullbackSectionsLE (Y.relativeDifferentials R) V.1 U.1 hUV
        ((Y.universalDerivation R).d (X := op V.1) b) := by
  let : Algebra R Γ(Y, V) := ((Y.baseRingToStructurePresheaf R).app (op V.1)).hom.toAlgebra
  let : Algebra Γ(Y, V) Γ(X, U) := (f.appLE V.1 U.1 hUV).hom.toAlgebra
  dsimp [pullbackRelativeDifferentialsSectionsEquiv]
  exact congrArg (fun x ↦ a • f.pullbackSectionsLE (Y.relativeDifferentials R) V.1 U.1 hUV x)
    (relativeDifferentialsSectionsEquiv_D R Y V b)

/-- For a morphism `f : X ⟶ Y` over `Spec R` and opens `V` of `Y` and `U ≤ f⁻¹ V` of `X`,
`f.appLE V U hUV` makes `R → Γ(Y, V) → Γ(X, U)` a scalar tower. -/
lemma isScalarTower_baseRing_appLE (R : Type u) [CommRing R]
    {X Y : Scheme.{u}} [X.Over (Spec (.of R))] [Y.Over (Spec (.of R))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of R))]
    (V : Y.Opens) (U : X.Opens) (hUV : U ≤ f ⁻¹ᵁ V) :
    letI : Algebra R Γ(Y, V) := ((Y.baseRingToStructurePresheaf R).app (op V)).hom.toAlgebra
    letI : Algebra R Γ(X, U) := ((X.baseRingToStructurePresheaf R).app (op U)).hom.toAlgebra
    letI : Algebra Γ(Y, V) Γ(X, U) := (f.appLE V U hUV).hom.toAlgebra
    IsScalarTower R Γ(Y, V) Γ(X, U) := by
  let : Algebra R Γ(Y, V) := ((Y.baseRingToStructurePresheaf R).app (op V)).hom.toAlgebra
  let : Algebra R Γ(X, U) := ((X.baseRingToStructurePresheaf R).app (op U)).hom.toAlgebra
  let : Algebra Γ(Y, V) Γ(X, U) := (f.appLE V U hUV).hom.toAlgebra
  refine IsScalarTower.of_algebraMap_eq fun r ↦ ?_
  -- Expose `algebraMap` for `RingHom.toAlgebra` on both coordinate rings.
  change (X.baseRingToStructurePresheaf R).app (op U) r =
    f.appLE V U hUV ((Y.baseRingToStructurePresheaf R).app (op V) r)
  rw [Scheme.Hom.appLE, CommRingCat.comp_apply,
    Scheme.Modules.app_baseRingToStructurePresheaf R f V r]
  have hn := (X.baseRingToStructurePresheaf R).naturality_apply (homOfLE hUV).op r
  simp only [Functor.const_obj_obj, Functor.const_obj_map, ConcreteCategory.id_apply] at hn
  exact hn

/-- On compatible affine opens `V` of `Y` and `U ≤ f⁻¹ V` of `X`, `(cotangentMap R f).app U`
identifies under `pullbackRelativeDifferentialsSectionsEquiv` and
`relativeDifferentialsSectionsEquiv` with `KaehlerDifferential.mapBaseChange R Γ(Y, V) Γ(X, U)`. -/
theorem cotangentMap_app_pullbackRelativeDifferentialsSectionsEquiv
    (R : Type u) [CommRing R] {X Y : Scheme.{u}}
    [X.Over (Spec (.of R))] [Y.Over (Spec (.of R))] (f : X ⟶ Y) [f.IsOver (Spec (.of R))]
    (V : Y.affineOpens) (U : X.affineOpens) (hUV : U.1 ≤ f ⁻¹ᵁ V.1) :
    letI : Algebra R Γ(Y, V) := ((Y.baseRingToStructurePresheaf R).app (op V.1)).hom.toAlgebra
    letI : Algebra R Γ(X, U) := ((X.baseRingToStructurePresheaf R).app (op U.1)).hom.toAlgebra
    letI : Algebra Γ(Y, V) Γ(X, U) := (f.appLE V.1 U.1 hUV).hom.toAlgebra
    haveI : IsScalarTower R Γ(Y, V) Γ(X, U) := isScalarTower_baseRing_appLE R f V.1 U.1 hUV
    ∀ ω : Γ(X, U) ⊗[Γ(Y, V)] Ω[Γ(Y, V)⁄R],
      (relativeDifferentialsSectionsEquiv R X U).symm
          ((cotangentMap R f).app U.1
            (pullbackRelativeDifferentialsSectionsEquiv R f V U hUV ω)) =
        KaehlerDifferential.mapBaseChange R Γ(Y, V) Γ(X, U) ω := by
  let : Algebra R Γ(Y, V) := ((Y.baseRingToStructurePresheaf R).app (op V.1)).hom.toAlgebra
  let : Algebra R Γ(X, U) := ((X.baseRingToStructurePresheaf R).app (op U.1)).hom.toAlgebra
  let : Algebra Γ(Y, V) Γ(X, U) := (f.appLE V.1 U.1 hUV).hom.toAlgebra
  have : IsScalarTower R Γ(Y, V) Γ(X, U) := isScalarTower_baseRing_appLE R f V.1 U.1 hUV
  let φU : Γ((Scheme.Modules.pullback f).obj (Y.relativeDifferentials R), U.1) →ₗ[Γ(X, U)]
      Γ(X.relativeDifferentials R, U.1) :=
    { toFun := (cotangentMap R f).app U.1, map_add' := map_add _,
      map_smul' := (cotangentMap R f).app_smul }
  let L : Γ(X, U) ⊗[Γ(Y, V)] Ω[Γ(Y, V)⁄R] →ₗ[Γ(X, U)] Ω[Γ(X, U)⁄R] :=
    (relativeDifferentialsSectionsEquiv R X U).symm.toLinearMap ∘ₗ
      φU ∘ₗ (pullbackRelativeDifferentialsSectionsEquiv R f V U hUV).toLinearMap
  suffices hL : L = KaehlerDifferential.mapBaseChange R Γ(Y, V) Γ(X, U) from
    fun ω ↦ congr($hL ω)
  refine kaehlerBaseChange_linearMap_ext fun b ↦ ?_
  simp only [L, LinearMap.comp_apply, LinearEquiv.coe_coe,
    pullbackRelativeDifferentialsSectionsEquiv_tmul_D, one_smul, φU, LinearMap.coe_mk,
    AddHom.coe_mk, cotangentMap_app_pullbackSectionsLE_d,
    KaehlerDifferential.mapBaseChange_tmul, KaehlerDifferential.map_D]
  exact (LinearEquiv.symm_apply_eq _).mpr
    (relativeDifferentialsSectionsEquiv_D R X U (f.appLE V.1 U.1 hUV b)).symm

end AffineCharts

section BaseChange

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]

section SingleScheme

variable {X X' : Scheme.{u}} [X.Over (Spec (.of R))] [X'.Over (Spec (.of S))] {g : X' ⟶ X}
  (H : IsPullback g (X' ↘ Spec (.of S)) (X ↘ Spec (.of R))
    (Spec.map (CommRingCat.ofHom (algebraMap R S))))

include H in
/-- **Relative differentials commute with arbitrary base change of the affine base ring.**
For any cartesian square `X' = X ×_{Spec R} Spec S` along a ring homomorphism `R → S` (with no
flatness or finiteness assumption), `relativeDifferentialsPullbackHom : g^* Ω_{X/R} ⟶ Ω_{X'/S}` is
an isomorphism of `𝒪_{X'}`-modules. -/
theorem isIso_relativeDifferentialsPullbackHom :
    IsIso (relativeDifferentialsPullbackHom H.toCommSq) := by
  have : IsAffineHom g := MorphismProperty.of_isPullback H.flip inferInstance
  have hcover : ⨆ U : X.affineOpens, g ⁻¹ᵁ U.1 = ⊤ := by
    rw [← Scheme.Hom.preimage_iSup, iSup_affineOpens_eq_top X, Scheme.Hom.preimage_top]
  refine Scheme.Modules.Hom.isIso_of_bijective_app
    (relativeDifferentialsPullbackHom H.toCommSq)
    (fun U : X.affineOpens ↦ U.2.preimage g) hcover fun U ↦ ?_
  let U' : X'.affineOpens := ⟨g ⁻¹ᵁ U.1, U.2.preimage g⟩
  let : Algebra R Γ(X, U) := ((X.baseRingToStructurePresheaf R).app (op U.1)).hom.toAlgebra
  let : Algebra S Γ(X', U') := ((X'.baseRingToStructurePresheaf S).app (op U'.1)).hom.toAlgebra
  let : Algebra Γ(X, U) Γ(X', U') := (g.appLE U.1 U'.1 le_rfl).hom.toAlgebra
  have hpush : IsPushout (CommRingCat.ofHom (algebraMap R S))
      (CommRingCat.ofHom (algebraMap R Γ(X, U)))
      (CommRingCat.ofHom (algebraMap S Γ(X', U')))
      (CommRingCat.ofHom (algebraMap Γ(X, U) Γ(X', U'))) := by
    simpa only [U', RingHom.algebraMap_toAlgebra, CommRingCat.ofHom_hom,
      Scheme.Hom.appLE_eq_app] using
      Scheme.isPushout_baseRingToStructurePresheaf_of_isAffineOpen H U.2
  let : Algebra R Γ(X', U') := ((algebraMap S Γ(X', U')).comp (algebraMap R S)).toAlgebra
  have : IsScalarTower R S Γ(X', U') := .of_algebraMap_eq' rfl
  have hw := congrArg CommRingCat.Hom.hom hpush.w
  simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom] at hw
  have : IsScalarTower R Γ(X, U) Γ(X', U') := .of_algebraMap_eq' hw
  have : Algebra.IsPushout R S Γ(X, U) Γ(X', U') :=
    CommRingCat.isPushout_iff_isPushout.mp hpush
  let e₁ := pullbackRelativeDifferentialsSectionsEquiv R g U U' le_rfl
  let e₂ := relativeDifferentialsSectionsEquiv S X' U'
  let e₃ := KaehlerDifferential.tensorKaehlerEquiv R S Γ(X, U) Γ(X', U')
  let φ : Γ((Scheme.Modules.pullback g).obj (X.relativeDifferentials R), U'.1) →ₗ[Γ(X', U')]
      Γ(X'.relativeDifferentials S, U'.1) :=
    { toFun := (relativeDifferentialsPullbackHom H.toCommSq).app U'.1, map_add' := map_add _,
      map_smul' := (relativeDifferentialsPullbackHom H.toCommSq).app_smul }
  have hφ : e₂.symm.toLinearMap ∘ₗ φ ∘ₗ e₁.toLinearMap = e₃.toLinearMap := by
    refine kaehlerBaseChange_linearMap_ext fun a ↦ ?_
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, e₁, e₃,
      pullbackRelativeDifferentialsSectionsEquiv_tmul_D, one_smul, φ, LinearMap.coe_mk,
      AddHom.coe_mk, relativeDifferentialsPullbackHom_app_pullbackSectionsLE_d,
      KaehlerDifferential.tensorKaehlerEquiv_tmul_D]
    exact (LinearEquiv.symm_apply_eq _).mpr
      (relativeDifferentialsSectionsEquiv_D S X' U' (g.appLE U.1 U'.1 le_rfl a)).symm
  have hfun : ((relativeDifferentialsPullbackHom H.toCommSq).app U'.1 : _ → _) =
      e₁.symm.trans (e₃.trans e₂) := by
    ext x
    simpa [φ] using congrArg e₂ congr($hφ (e₁.symm x))
  rw [hfun]
  exact (e₁.symm.trans (e₃.trans e₂)).bijective

/-- **Base-change isomorphism for relative differentials**: for a cartesian square
`X' = X ×_{Spec R} Spec S` along any ring homomorphism `R → S`, the canonical comparison
`g^* Ω_{X/R} ≅ Ω_{X'/S}`. -/
def relativeDifferentialsBaseChangeIso :
    (Scheme.Modules.pullback g).obj (X.relativeDifferentials R) ≅ X'.relativeDifferentials S :=
  @asIso _ _ _ _ (relativeDifferentialsPullbackHom H.toCommSq)
    (isIso_relativeDifferentialsPullbackHom H)

/-- The forward map of `relativeDifferentialsBaseChangeIso` is
`relativeDifferentialsPullbackHom`. -/
@[simp]
lemma relativeDifferentialsBaseChangeIso_hom :
    (relativeDifferentialsBaseChangeIso H).hom = relativeDifferentialsPullbackHom H.toCommSq :=
  (rfl)

/-- On sections over `g⁻¹ U`, `relativeDifferentialsBaseChangeIso` sends the pulled-back
differential of `a ∈ Γ(X, U)` to `d (g.app U a)`. -/
lemma relativeDifferentialsBaseChangeIso_hom_app_pullbackSections_d (U : X.Opens) (a : Γ(X, U)) :
    (relativeDifferentialsBaseChangeIso H).hom.app (g ⁻¹ᵁ U)
        (g.pullbackSections (X.relativeDifferentials R) U
          ((X.universalDerivation R).d (X := op U) a)) =
      (X'.universalDerivation S).d (X := op (g ⁻¹ᵁ U)) (g.app U a) :=
  relativeDifferentialsPullbackHom_app_pullbackSections_d H.toCommSq U a

end SingleScheme

section MorphismSquare

variable {X Y X' Y' : Scheme.{u}}
  [X.Over (Spec (.of R))] [Y.Over (Spec (.of R))]
  [X'.Over (Spec (.of S))] [Y'.Over (Spec (.of S))]
  {f : X ⟶ Y} {f' : X' ⟶ Y'} [f.IsOver (Spec (.of R))] [f'.IsOver (Spec (.of S))]
  {g_X : X' ⟶ X} {g_Y : Y' ⟶ Y}

/-- Naturality of `cotangentMap` with respect to any commutative square of morphisms over a ring
homomorphism `R → S`. -/
@[reassoc]
theorem pullback_cotangentMap_comp_relativeDifferentialsPullbackHom
    (w : g_X ≫ f = f' ≫ g_Y)
    (C_X : CommSq g_X (X' ↘ Spec (.of S)) (X ↘ Spec (.of R))
      (Spec.map (CommRingCat.ofHom (algebraMap R S))))
    (C_Y : CommSq g_Y (Y' ↘ Spec (.of S)) (Y ↘ Spec (.of R))
      (Spec.map (CommRingCat.ofHom (algebraMap R S)))) :
    (Scheme.Modules.pullback g_X).map (cotangentMap R f) ≫
        relativeDifferentialsPullbackHom C_X =
      (Scheme.Modules.pullbackComp g_X f).hom.app (Y.relativeDifferentials R) ≫
        (Scheme.Modules.pullbackCongr w).hom.app (Y.relativeDifferentials R) ≫
        (Scheme.Modules.pullbackComp f' g_Y).inv.app (Y.relativeDifferentials R) ≫
        (Scheme.Modules.pullback f').map (relativeDifferentialsPullbackHom C_Y) ≫
        cotangentMap S f' := by
  have C_left : CommSq (g_X ≫ f) (X' ↘ Spec (.of S)) (Y ↘ Spec (.of R))
      (Spec.map (CommRingCat.ofHom (algebraMap R S))) :=
    ⟨by rw [Category.assoc, HomIsOver.comp_over, C_X.w]⟩
  have C_right : CommSq (f' ≫ g_Y) (X' ↘ Spec (.of S)) (Y ↘ Spec (.of R))
      (Spec.map (CommRingCat.ofHom (algebraMap R S))) :=
    ⟨by rw [Category.assoc, C_Y.w, ← Category.assoc, HomIsOver.comp_over]⟩
  have h₁ := relativeDifferentialsPullbackHom_comp
    (R := R) (S := R) (T := S) C_X (commSq_of_isOver R f) C_left
  have h₂ := relativeDifferentialsPullbackHom_comp
    (R := R) (S := S) (T := S) (commSq_of_isOver S f') C_Y C_right
  have hc := relativeDifferentialsPullbackHom_congr w C_left C_right
  rw [← cancel_epi ((Scheme.Modules.pullbackComp g_X f).inv.app (Y.relativeDifferentials R)),
    Iso.inv_hom_id_app_assoc]
  exact h₁.symm.trans (hc.symm.trans (congrArg _ h₂))

omit [X.Over (Spec (.of R))] [X'.Over (Spec (.of S))]
  [f.IsOver (Spec (.of R))] [f'.IsOver (Spec (.of S))] in
/-- When `Y' = Y ×_{Spec R} Spec S` is a base change and `g_X ≫ f = f' ≫ g_Y`, the canonical
isomorphism identifying `g_X^* (f^* Ω_{Y/R})` with `f'^* Ω_{Y'/S}`. -/
def cotangentSourceBaseChangeIso
    (H_Y : IsPullback g_Y (Y' ↘ Spec (.of S)) (Y ↘ Spec (.of R))
      (Spec.map (CommRingCat.ofHom (algebraMap R S))))
    (w : g_X ≫ f = f' ≫ g_Y) :
    (Scheme.Modules.pullback g_X).obj
        ((Scheme.Modules.pullback f).obj (Y.relativeDifferentials R)) ≅
      (Scheme.Modules.pullback f').obj (Y'.relativeDifferentials S) :=
  (Scheme.Modules.pullbackComp g_X f).app (Y.relativeDifferentials R) ≪≫
    (Scheme.Modules.pullbackCongr w).app (Y.relativeDifferentials R) ≪≫
    ((Scheme.Modules.pullbackComp f' g_Y).app (Y.relativeDifferentials R)).symm ≪≫
    (Scheme.Modules.pullback f').mapIso (relativeDifferentialsBaseChangeIso H_Y)

omit [X.Over (Spec (.of R))] [X'.Over (Spec (.of S))]
  [f.IsOver (Spec (.of R))] [f'.IsOver (Spec (.of S))] in
/-- The forward morphism of `cotangentSourceBaseChangeIso` factors through `pullbackComp`,
`pullbackCongr`, and `relativeDifferentialsPullbackHom`. -/
@[simp]
lemma cotangentSourceBaseChangeIso_hom
    (H_Y : IsPullback g_Y (Y' ↘ Spec (.of S)) (Y ↘ Spec (.of R))
      (Spec.map (CommRingCat.ofHom (algebraMap R S))))
    (w : g_X ≫ f = f' ≫ g_Y) :
    (cotangentSourceBaseChangeIso H_Y w).hom =
      (Scheme.Modules.pullbackComp g_X f).hom.app (Y.relativeDifferentials R) ≫
        (Scheme.Modules.pullbackCongr w).hom.app (Y.relativeDifferentials R) ≫
        (Scheme.Modules.pullbackComp f' g_Y).inv.app (Y.relativeDifferentials R) ≫
        (Scheme.Modules.pullback f').map (relativeDifferentialsPullbackHom H_Y.toCommSq) := by
  simp [cotangentSourceBaseChangeIso]

/-- **Base-change compatibility of the cotangent map**: for a morphism `f : X ⟶ Y` over `Spec R`
and its base change `f' : X' ⟶ Y'` along any ring homomorphism `R → S`, the cotangent map of `f'`
agrees with the pullback of `cotangentMap R f` under `cotangentSourceBaseChangeIso` and
`relativeDifferentialsBaseChangeIso`. No flatness or finiteness assumption is required. -/
@[reassoc]
theorem cotangentSourceBaseChangeIso_hom_comp_cotangentMap
    (H_X : IsPullback g_X (X' ↘ Spec (.of S)) (X ↘ Spec (.of R))
      (Spec.map (CommRingCat.ofHom (algebraMap R S))))
    (H_Y : IsPullback g_Y (Y' ↘ Spec (.of S)) (Y ↘ Spec (.of R))
      (Spec.map (CommRingCat.ofHom (algebraMap R S))))
    (w : g_X ≫ f = f' ≫ g_Y) :
    (cotangentSourceBaseChangeIso H_Y w).hom ≫ cotangentMap S f' =
      (Scheme.Modules.pullback g_X).map (cotangentMap R f) ≫
        (relativeDifferentialsBaseChangeIso H_X).hom := by
  rw [cotangentSourceBaseChangeIso_hom, relativeDifferentialsBaseChangeIso_hom, Category.assoc,
    Category.assoc, Category.assoc]
  exact (pullback_cotangentMap_comp_relativeDifferentialsPullbackHom w
    H_X.toCommSq H_Y.toCommSq).symm

end MorphismSquare

end BaseChange

end

end TauCeti.AlgebraicGeometry
