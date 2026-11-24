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
import TauCeti.AlgebraicGeometry.Scheme.SpecOver
import TauCeti.RingTheory.Kaehler.BaseChange

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

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
  {X Y : Scheme.{u}} [X.Over (Spec (.of S))] [Y.Over (Spec (.of R))] {f : X ⟶ Y}

/-- Given a morphism `f : X ⟶ Y` fitting into a commutative square over `Spec S ⟶ Spec R`, an
`S`-derivation of `𝒪_X` into `M` induces an `R`-derivation of `𝒪_Y` into `f_* M` by differentiating
pulled-back local functions. -/
def pushforwardDerivationOfCommSq
    (C : CommSq f (X ↘ Spec (.of S)) (Y ↘ Spec (.of R))
      (Spec.map (CommRingCat.ofHom (algebraMap R S))))
    {M : X.Modules} (d : M.Derivation S) :
    ((Scheme.Modules.pushforward f).obj M).Derivation R :=
  letI : X.Over (Spec (.of R)) :=
    ⟨(X ↘ Spec (.of S)) ≫ Spec.map (CommRingCat.ofHom (algebraMap R S))⟩
  haveI : f.IsOver (Spec (.of R)) := ⟨C.w⟩
  pushforwardDerivation R f
    { d := d.d
      d_mul := d.d_mul
      d_map := d.d_map
      d_app {U} r :=
        (congrArg (d.d (X := U))
          (X.baseRingToStructurePresheaf_app_algebraMap (R := R) (S := S) rfl U.unop r).symm).trans
          (d.d_app (algebraMap R S r)) }

/-- Evaluating `pushforwardDerivationOfCommSq` on a local function `a` differentiates `f.app U a`.
-/
@[simp]
lemma pushforwardDerivationOfCommSq_d
    (C : CommSq f (X ↘ Spec (.of S)) (Y ↘ Spec (.of R))
      (Spec.map (CommRingCat.ofHom (algebraMap R S))))
    {M : X.Modules} (d : M.Derivation S) (U : Y.Opens) (a : Γ(Y, U)) :
    (pushforwardDerivationOfCommSq C d).d a = d.d (f.app U a) :=
  letI : X.Over (Spec (.of R)) :=
    ⟨(X ↘ Spec (.of S)) ≫ Spec.map (CommRingCat.ofHom (algebraMap R S))⟩
  haveI : f.IsOver (Spec (.of R)) := ⟨C.w⟩
  pushforwardDerivation_d R f _ U a

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

/-- The pullback–pushforward adjunction transpose of `relativeDifferentialsPullbackHom C` is the
morphism induced by `pushforwardDerivationOfCommSq C (X.universalDerivation S)`. -/
@[simp]
theorem pullbackPushforwardAdjunction_homEquiv_relativeDifferentialsPullbackHom
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
  refine (Scheme.Modules.pullbackPushforwardAdjunction_homEquiv_app_apply f
    (relativeDifferentialsPullbackHom C) V _).symm.trans ?_
  refine (congrArg (fun g ↦ g.app V ((Y.universalDerivation R).d (X := op V) b))
    (pullbackPushforwardAdjunction_homEquiv_relativeDifferentialsPullbackHom C)).trans ?_
  exact (congrArg (fun D ↦ D.d b)
    (Y.relativeDifferentialsHomEquiv_symm_fac R
      (pushforwardDerivationOfCommSq C (X.universalDerivation S)))).trans
    (pushforwardDerivationOfCommSq_d C (X.universalDerivation S) V b)

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
  exact (Scheme.Modules.pullbackPushforwardAdjunction_homEquiv_app_apply f φ V.unop _).trans
    ((h V.unop b).trans
      (Scheme.Modules.pullbackPushforwardAdjunction_homEquiv_app_apply f ψ V.unop _).symm)

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
  have happ := (Scheme.Modules.pullbackPushforwardAdjunction_homEquiv_app_apply (𝟙 X)
    ((Scheme.Modules.pullbackId X).hom.app (X.relativeDifferentials R)) V
      ((X.universalDerivation R).d (X := op V) b)).symm.trans
    (congrArg (fun g ↦ g.app V ((X.universalDerivation R).d (X := op V) b)) hid)
  refine (relativeDifferentialsPullbackHom_app_pullbackSections_d C V b).trans ?_
  refine Eq.trans ?_ happ.symm
  have hb : Scheme.Hom.app (𝟙 X) V b = b :=
    (congrArg (fun φ : Γ(X, V) ⟶ Γ(X, V) ↦ φ b) (Scheme.Hom.id_app V)).trans
      (ConcreteCategory.id_apply b)
  exact (congrArg (X.universalDerivation R).d hb).trans
    ((congrArg (fun φ : Γ(X.relativeDifferentials R, V) ⟶ Γ(X.relativeDifferentials R, V) ↦
        φ ((X.universalDerivation R).d (X := op V) b))
      (Scheme.Modules.Hom.id_app (M := X.relativeDifferentials R))).trans
      (ConcreteCategory.id_apply _)).symm

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
    (Scheme.Modules.pullbackComp_inv_comp_app_pullbackSections f g
      (relativeDifferentialsPullbackHom C_g) (relativeDifferentialsPullbackHom C_f) W _).symm
  refine Eq.trans ?_
    (congrArg (fun x ↦ (relativeDifferentialsPullbackHom C_f).app (f ⁻¹ᵁ (g ⁻¹ᵁ W))
      (f.pullbackSections _ (g ⁻¹ᵁ W) x))
      (relativeDifferentialsPullbackHom_app_pullbackSections_d C_g W c)).symm
  have happ : (f ≫ g).app W c = f.app (g ⁻¹ᵁ W) (g.app W c) :=
    (congrArg (fun φ : Γ(Z, W) ⟶ Γ(X, f ⁻¹ᵁ g ⁻¹ᵁ W) ↦ φ c) (Scheme.Hom.comp_app f g W)).trans
      (CommRingCat.comp_apply _ _ c)
  exact (congrArg (X.universalDerivation T).d happ).trans
    (relativeDifferentialsPullbackHom_app_pullbackSections_d C_f (g ⁻¹ᵁ W) (g.app W c)).symm

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

/-- The **cotangent map** `f^* Ω_{Y/R} ⟶ Ω_{X/R}` associated to a morphism `f : X ⟶ Y` over
`Spec R`: the first morphism in the relative cotangent exact sequence
`f^* Ω_{Y/R} ⟶ Ω_{X/R} ⟶ Ω_{X/Y} ⟶ 0`. -/
def cotangentMap (f : X ⟶ Y) [f.IsOver (Spec (.of R))] :
    (Scheme.Modules.pullback f).obj (Y.relativeDifferentials R) ⟶ X.relativeDifferentials R :=
  relativeDifferentialsPullbackHom (f.commSq_specMap_algebraMap_self R)

/-- For any morphism `f : X ⟶ Y` over `Spec R` and its commuting square over `Spec R ⟶ Spec R`,
`cotangentMap R f` agrees with `relativeDifferentialsPullbackHom`. -/
theorem cotangentMap_eq_relativeDifferentialsPullbackHom (f : X ⟶ Y) [f.IsOver (Spec (.of R))]
    (C : CommSq f (X ↘ Spec (.of R)) (Y ↘ Spec (.of R))
      (Spec.map (CommRingCat.ofHom (algebraMap R R)))) :
    cotangentMap R f = relativeDifferentialsPullbackHom C := by
  rw [cotangentMap, Subsingleton.elim (f.commSq_specMap_algebraMap_self R) C]

/-- The pullback–pushforward adjunction transpose of `cotangentMap R f` is the morphism induced by
`pushforwardDerivation R f (X.universalDerivation R)`. -/
@[simp]
theorem pullbackPushforwardAdjunction_homEquiv_cotangentMap
    (f : X ⟶ Y) [f.IsOver (Spec (.of R))] :
    (Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _ (cotangentMap R f) =
      (Y.relativeDifferentialsHomEquiv R _).symm
        (pushforwardDerivation R f (X.universalDerivation R)) := by
  rw [cotangentMap, pullbackPushforwardAdjunction_homEquiv_relativeDifferentialsPullbackHom]
  congr 1
  ext U a
  exact (pushforwardDerivationOfCommSq_d _ _ U.unop a).trans
    (pushforwardDerivation_d R f _ U.unop a).symm

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
    (f.commSq_specMap_algebraMap_self R) (g.commSq_specMap_algebraMap_self R)
    ((f ≫ g).commSq_specMap_algebraMap_self R)

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
  refine (pushforwardDerivationOfCommSq_d _ (X.universalDerivation R) V.unop b).trans ?_
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
  exact (congrArg (fun φ : Γ(Y, V.unop) ⟶ Γ(X, f ⁻¹ᵁ V.unop) ↦ φ b)
    ((Iso.comp_inv_eq _).mp (f.app_appIso_inv V.unop))).trans (CommRingCat.comp_apply _ _ b)

/-- Along an open immersion over `Spec R`, `cotangentMap R f` is an isomorphism. -/
instance isIso_cotangentMap_of_isOpenImmersion (f : X ⟶ Y) [f.IsOver (Spec (.of R))]
    [IsOpenImmersion f] : IsIso (cotangentMap R f) := by
  rw [cotangentMap_of_isOpenImmersion]
  infer_instance

end CotangentMap

section AffineCharts

/-- Over affine opens `V` of `Y` and `U ≤ f⁻¹ V` of `X`, the sections of `f^* Ω_{Y/R}` over `U`
identify with the tensor product `Γ(X, U) ⊗[Γ(Y, V)] Ω[Γ(Y, V)⁄R]`. -/
def pullbackRelativeDifferentialsSectionsEquiv (R : Type u) [CommRing R]
    {X Y : Scheme.{u}} [Y.Over (Spec (.of R))] (f : X ⟶ Y)
    (V : Y.affineOpens) (U : X.affineOpens) (hUV : U.val ≤ f ⁻¹ᵁ V.val) :
    letI : Algebra R Γ(Y, V) := ((Y.baseRingToStructurePresheaf R).app (op V.val)).hom.toAlgebra
    letI : Algebra Γ(Y, V) Γ(X, U) := (f.appLE V.val U.val hUV).hom.toAlgebra
    Γ(X, U) ⊗[Γ(Y, V)] Ω[Γ(Y, V)⁄R] ≃ₗ[Γ(X, U)]
      Γ((Scheme.Modules.pullback f).obj (Y.relativeDifferentials R), U.val) := by
  letI : Algebra R Γ(Y, V) := ((Y.baseRingToStructurePresheaf R).app (op V.val)).hom.toAlgebra
  letI : Algebra Γ(Y, V) Γ(X, U) := (f.appLE V.val U.val hUV).hom.toAlgebra
  letI : Module Γ(Y, V) Γ((Scheme.Modules.pullback f).obj (Y.relativeDifferentials R), U.val) :=
    Module.compHom _ (algebraMap Γ(Y, V) Γ(X, U))
  haveI : IsScalarTower Γ(Y, V) Γ(X, U)
      Γ((Scheme.Modules.pullback f).obj (Y.relativeDifferentials R), U.val) :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  let φ : Γ(Y.relativeDifferentials R, V.val) →ₗ[Γ(Y, V)]
      Γ((Scheme.Modules.pullback f).obj (Y.relativeDifferentials R), U.val) :=
    { toFun := f.pullbackSectionsLE (Y.relativeDifferentials R) V.val U.val hUV
      map_add' := map_add _
      map_smul' := (f.pullbackSectionsLE (Y.relativeDifferentials R) V.val U.val hUV).map_smulₛₗ }
  have hBC : IsBaseChange Γ(X, U) φ :=
    f.isBaseChange_pullbackSectionsLE (Y.relativeDifferentials R) V.property U.property hUV
      (fun _ ↦ rfl) φ (fun _ ↦ rfl)
  exact ((relativeDifferentialsSectionsEquiv R Y V).baseChange Γ(Y, V) Γ(X, U)).trans hBC.equiv

/-- `pullbackRelativeDifferentialsSectionsEquiv` sends `a ⊗ₜ D b` to `a` times the pulled-back
differential `d b`. -/
@[simp]
theorem pullbackRelativeDifferentialsSectionsEquiv_tmul_D (R : Type u) [CommRing R]
    {X Y : Scheme.{u}} [Y.Over (Spec (.of R))] (f : X ⟶ Y)
    (V : Y.affineOpens) (U : X.affineOpens) (hUV : U.val ≤ f ⁻¹ᵁ V.val)
    (a : Γ(X, U)) (b : Γ(Y, V)) :
    letI : Algebra R Γ(Y, V) := ((Y.baseRingToStructurePresheaf R).app (op V.val)).hom.toAlgebra
    letI : Algebra Γ(Y, V) Γ(X, U) := (f.appLE V.val U.val hUV).hom.toAlgebra
    pullbackRelativeDifferentialsSectionsEquiv R f V U hUV
        (a ⊗ₜ[Γ(Y, V)] KaehlerDifferential.D R Γ(Y, V) b) =
      a • f.pullbackSectionsLE (Y.relativeDifferentials R) V.val U.val hUV
        ((Y.universalDerivation R).d (X := op V.val) b) := by
  let : Algebra R Γ(Y, V) := ((Y.baseRingToStructurePresheaf R).app (op V.val)).hom.toAlgebra
  let : Algebra Γ(Y, V) Γ(X, U) := (f.appLE V.val U.val hUV).hom.toAlgebra
  dsimp [pullbackRelativeDifferentialsSectionsEquiv]
  exact congrArg (fun x ↦ a • f.pullbackSectionsLE (Y.relativeDifferentials R) V.val U.val hUV x)
    (relativeDifferentialsSectionsEquiv_D R Y V b)

/-- The inverse of `pullbackRelativeDifferentialsSectionsEquiv` sends the pulled-back differential
of `b ∈ Γ(Y, V)` to `1 ⊗ₜ D b`. -/
@[simp]
theorem pullbackRelativeDifferentialsSectionsEquiv_symm_pullbackSectionsLE_d
    (R : Type u) [CommRing R] {X Y : Scheme.{u}} [Y.Over (Spec (.of R))] (f : X ⟶ Y)
    (V : Y.affineOpens) (U : X.affineOpens) (hUV : U.val ≤ f ⁻¹ᵁ V.val) (b : Γ(Y, V)) :
    letI : Algebra R Γ(Y, V) := ((Y.baseRingToStructurePresheaf R).app (op V.val)).hom.toAlgebra
    letI : Algebra Γ(Y, V) Γ(X, U) := (f.appLE V.val U.val hUV).hom.toAlgebra
    (pullbackRelativeDifferentialsSectionsEquiv R f V U hUV).symm
        (f.pullbackSectionsLE (Y.relativeDifferentials R) V.val U.val hUV
          ((Y.universalDerivation R).d (X := op V.val) b)) =
      (1 : Γ(X, U)) ⊗ₜ[Γ(Y, V)] KaehlerDifferential.D R Γ(Y, V) b := by
  let : Algebra R Γ(Y, V) := ((Y.baseRingToStructurePresheaf R).app (op V.val)).hom.toAlgebra
  let : Algebra Γ(Y, V) Γ(X, U) := (f.appLE V.val U.val hUV).hom.toAlgebra
  exact (LinearEquiv.symm_apply_eq _).mpr
    ((pullbackRelativeDifferentialsSectionsEquiv_tmul_D R f V U hUV 1 b).trans (one_smul _ _)).symm

/-- On compatible affine opens `V` of `Y` and `U ≤ f⁻¹ V` of `X`, `(cotangentMap R f).app U`
agrees under `pullbackRelativeDifferentialsSectionsEquiv` and `relativeDifferentialsSectionsEquiv`
with `KaehlerDifferential.mapBaseChange R Γ(Y, V) Γ(X, U)`. -/
theorem cotangentMap_app_pullbackRelativeDifferentialsSectionsEquiv
    (R : Type u) [CommRing R] {X Y : Scheme.{u}}
    [X.Over (Spec (.of R))] [Y.Over (Spec (.of R))] (f : X ⟶ Y) [f.IsOver (Spec (.of R))]
    (V : Y.affineOpens) (U : X.affineOpens) (hUV : U.val ≤ f ⁻¹ᵁ V.val) :
    letI : Algebra R Γ(Y, V) := ((Y.baseRingToStructurePresheaf R).app (op V.val)).hom.toAlgebra
    letI : Algebra R Γ(X, U) := ((X.baseRingToStructurePresheaf R).app (op U.val)).hom.toAlgebra
    letI : Algebra Γ(Y, V) Γ(X, U) := (f.appLE V.val U.val hUV).hom.toAlgebra
    haveI : IsScalarTower R Γ(Y, V) Γ(X, U) :=
      Scheme.Modules.isScalarTower_baseRingToStructurePresheaf_appLE R f V.val U.val hUV
    ∀ ω : Γ(X, U) ⊗[Γ(Y, V)] Ω[Γ(Y, V)⁄R],
      (cotangentMap R f).app U.val (pullbackRelativeDifferentialsSectionsEquiv R f V U hUV ω) =
        relativeDifferentialsSectionsEquiv R X U
          (KaehlerDifferential.mapBaseChange R Γ(Y, V) Γ(X, U) ω) := by
  let : Algebra R Γ(Y, V) := ((Y.baseRingToStructurePresheaf R).app (op V.val)).hom.toAlgebra
  let : Algebra R Γ(X, U) := ((X.baseRingToStructurePresheaf R).app (op U.val)).hom.toAlgebra
  let : Algebra Γ(Y, V) Γ(X, U) := (f.appLE V.val U.val hUV).hom.toAlgebra
  have : IsScalarTower R Γ(Y, V) Γ(X, U) :=
    Scheme.Modules.isScalarTower_baseRingToStructurePresheaf_appLE R f V.val U.val hUV
  let φU : Γ((Scheme.Modules.pullback f).obj (Y.relativeDifferentials R), U.val) →ₗ[Γ(X, U)]
      Γ(X.relativeDifferentials R, U.val) :=
    ((Scheme.Modules.sectionsFunctor U.val).map (cotangentMap R f)).hom
  let L₁ : Γ(X, U) ⊗[Γ(Y, V)] Ω[Γ(Y, V)⁄R] →ₗ[Γ(X, U)] Γ(X.relativeDifferentials R, U.val) :=
    φU ∘ₗ (pullbackRelativeDifferentialsSectionsEquiv R f V U hUV).toLinearMap
  let L₂ : Γ(X, U) ⊗[Γ(Y, V)] Ω[Γ(Y, V)⁄R] →ₗ[Γ(X, U)] Γ(X.relativeDifferentials R, U.val) :=
    (relativeDifferentialsSectionsEquiv R X U).toLinearMap ∘ₗ
      KaehlerDifferential.mapBaseChange R Γ(Y, V) Γ(X, U)
  suffices hL : L₁ = L₂ from fun ω ↦ congr($hL ω)
  refine TauCeti.kaehlerBaseChange_linearMap_ext fun b ↦ ?_
  dsimp only [L₁, L₂, LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [pullbackRelativeDifferentialsSectionsEquiv_tmul_D, one_smul,
    KaehlerDifferential.mapBaseChange_tmul, KaehlerDifferential.map_D, one_smul,
    relativeDifferentialsSectionsEquiv_D, RingHom.algebraMap_toAlgebra]
  exact cotangentMap_app_pullbackSectionsLE_d R f V.val U.val hUV b

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
  have hcover : ⨆ U : X.affineOpens, g ⁻¹ᵁ U.val = ⊤ := by
    rw [← Scheme.Hom.preimage_iSup, iSup_affineOpens_eq_top X, Scheme.Hom.preimage_top]
  refine Scheme.Modules.Hom.isIso_of_bijective_app
    (relativeDifferentialsPullbackHom H.toCommSq)
    (fun U : X.affineOpens ↦ U.property.preimage g) hcover fun U ↦ ?_
  let U' : X'.affineOpens := ⟨g ⁻¹ᵁ U.val, U.property.preimage g⟩
  let : Algebra R Γ(X, U) := ((X.baseRingToStructurePresheaf R).app (op U.val)).hom.toAlgebra
  let : Algebra S Γ(X', U') := ((X'.baseRingToStructurePresheaf S).app (op U'.val)).hom.toAlgebra
  let : Algebra Γ(X, U) Γ(X', U') := (g.app U.val).hom.toAlgebra
  let : Algebra R Γ(X', U') := ((g.app U.val).hom.comp (algebraMap R Γ(X, U))).toAlgebra
  have : IsScalarTower R Γ(X, U) Γ(X', U') := .of_algebraMap_eq' rfl
  have : IsScalarTower R S Γ(X', U') :=
    Scheme.Modules.isScalarTower_baseRingToStructurePresheaf_app g U.val H.toCommSq
  have : Algebra.IsPushout R S Γ(X, U) Γ(X', U') :=
    Scheme.algebraIsPushout_baseRingToStructurePresheaf_of_isAffineOpen H U.property
  let e₁ : Γ(X', U') ⊗[Γ(X, U)] Ω[Γ(X, U)⁄R] ≃ₗ[Γ(X', U')]
      Γ((Scheme.Modules.pullback g).obj (X.relativeDifferentials R), U'.val) :=
    ((relativeDifferentialsSectionsEquiv R X U).baseChange Γ(X, U) Γ(X', U')).trans
      (g.pullbackSectionsEquiv (X.relativeDifferentials R) U.property U'.property)
  let e₂ := relativeDifferentialsSectionsEquiv S X' U'
  let e₃ := KaehlerDifferential.tensorKaehlerEquiv R S Γ(X, U) Γ(X', U')
  let φ : Γ((Scheme.Modules.pullback g).obj (X.relativeDifferentials R), U'.val) →ₗ[Γ(X', U')]
      Γ(X'.relativeDifferentials S, U'.val) :=
    ((Scheme.Modules.sectionsFunctor U'.val).map
      (relativeDifferentialsPullbackHom H.toCommSq)).hom
  have hφ : e₂.symm.toLinearMap ∘ₗ φ ∘ₗ e₁.toLinearMap = e₃.toLinearMap := by
    refine TauCeti.kaehlerBaseChange_linearMap_ext fun a ↦ ?_
    have he₁ : e₁ ((1 : Γ(X', U')) ⊗ₜ[Γ(X, U)] KaehlerDifferential.D R Γ(X, U) a) =
        g.pullbackSections (X.relativeDifferentials R) U.val
          ((X.universalDerivation R).d (X := op U.val) a) :=
      (congrArg (g.pullbackSectionsEquiv (X.relativeDifferentials R) U.property U'.property)
        ((LinearEquiv.baseChange_tmul _ _ _ _ 1 _).trans
          (congrArg ((1 : Γ(X', U')) ⊗ₜ[Γ(X, U)] ·)
            (relativeDifferentialsSectionsEquiv_D R X U a)))).trans
        (g.pullbackSectionsEquiv_one_tmul (X.relativeDifferentials R) U.property U'.property _)
    refine (congrArg e₂.symm ((congrArg φ he₁).trans
      (relativeDifferentialsPullbackHom_app_pullbackSections_d H.toCommSq U.val a))).trans ?_
    refine ((LinearEquiv.symm_apply_eq e₂).mpr
      (relativeDifferentialsSectionsEquiv_D S X' U' (g.app U.val a)).symm).trans ?_
    exact ((KaehlerDifferential.tensorKaehlerEquiv_tmul_D R S Γ(X, U) Γ(X', U') 1 a).trans
      (one_smul _ _)).symm
  have hfun : ((relativeDifferentialsPullbackHom H.toCommSq).app U'.val : _ → _) =
      e₁.symm.trans (e₃.trans e₂) := by
    ext x
    have hx := congrArg e₂ congr($hφ (e₁.symm x))
    dsimp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.trans_apply] at hx ⊢
    rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply] at hx
    exact hx
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

/-- On sections over `g⁻¹ U`, `(relativeDifferentialsBaseChangeIso H).inv` sends `d (g.app U a)`
to the pulled-back differential of `a ∈ Γ(X, U)`. -/
@[simp]
theorem relativeDifferentialsBaseChangeIso_inv_app_d (U : X.Opens) (a : Γ(X, U)) :
    (relativeDifferentialsBaseChangeIso H).inv.app (g ⁻¹ᵁ U)
        ((X'.universalDerivation S).d (X := op (g ⁻¹ᵁ U)) (g.app U a)) =
      g.pullbackSections (X.relativeDifferentials R) U
        ((X.universalDerivation R).d (X := op U) a) := by
  rw [← relativeDifferentialsPullbackHom_app_pullbackSections_d H.toCommSq U a,
    ← relativeDifferentialsBaseChangeIso_hom H, ← ConcreteCategory.comp_apply,
    ← Scheme.Modules.Hom.comp_app, Iso.hom_inv_id, Scheme.Modules.Hom.id_app,
    ConcreteCategory.id_apply]

/-- On sections over `V ≤ g⁻¹ U`, `(relativeDifferentialsBaseChangeIso H).inv` sends
`d (g.appLE U V hUV a)` to the pulled-back differential of `a ∈ Γ(X, U)`. -/
@[simp]
theorem relativeDifferentialsBaseChangeIso_inv_app_d_appLE
    (U : X.Opens) (V : X'.Opens) (hUV : V ≤ g ⁻¹ᵁ U) (a : Γ(X, U)) :
    (relativeDifferentialsBaseChangeIso H).inv.app V
        ((X'.universalDerivation S).d (X := op V) (g.appLE U V hUV a)) =
      g.pullbackSectionsLE (X.relativeDifferentials R) U V hUV
        ((X.universalDerivation R).d (X := op U) a) := by
  rw [← relativeDifferentialsPullbackHom_app_pullbackSectionsLE_d H.toCommSq U V hUV a,
    ← relativeDifferentialsBaseChangeIso_hom H, ← ConcreteCategory.comp_apply,
    ← Scheme.Modules.Hom.comp_app, Iso.hom_inv_id, Scheme.Modules.Hom.id_app,
    ConcreteCategory.id_apply]

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
    (R := R) (S := R) (T := S) C_X (f.commSq_specMap_algebraMap_self R) C_left
  have h₂ := relativeDifferentialsPullbackHom_comp
    (R := R) (S := S) (T := S) (f'.commSq_specMap_algebraMap_self S) C_Y C_right
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

omit [X.Over (Spec (.of R))] [X'.Over (Spec (.of S))]
  [f.IsOver (Spec (.of R))] [f'.IsOver (Spec (.of S))] in
/-- The inverse morphism of `cotangentSourceBaseChangeIso` factors through
`(relativeDifferentialsBaseChangeIso H_Y).inv`, `pullbackComp`, and `pullbackCongr`. -/
lemma cotangentSourceBaseChangeIso_inv
    (H_Y : IsPullback g_Y (Y' ↘ Spec (.of S)) (Y ↘ Spec (.of R))
      (Spec.map (CommRingCat.ofHom (algebraMap R S))))
    (w : g_X ≫ f = f' ≫ g_Y) :
    (cotangentSourceBaseChangeIso H_Y w).inv =
      (Scheme.Modules.pullback f').map (relativeDifferentialsBaseChangeIso H_Y).inv ≫
        (Scheme.Modules.pullbackComp f' g_Y).hom.app (Y.relativeDifferentials R) ≫
        (Scheme.Modules.pullbackCongr w).inv.app (Y.relativeDifferentials R) ≫
        (Scheme.Modules.pullbackComp g_X f).inv.app (Y.relativeDifferentials R) := by
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
