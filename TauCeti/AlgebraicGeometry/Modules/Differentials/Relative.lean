/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Differentials.Presheaf
public import TauCeti.AlgebraicGeometry.Modules.Differentials.Pullback
import TauCeti.AlgebraicGeometry.Modules.AffineRestriction
import TauCeti.AlgebraicGeometry.Modules.Differentials.Quasicoherent
import TauCeti.AlgebraicGeometry.Modules.Pullback.BaseChange
import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.Cokernels
import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.Colimits
import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.FiniteType
import TauCeti.AlgebraicGeometry.Modules.Restriction.FinitePresentation
import TauCeti.RingTheory.Kaehler.BaseChange

/-!
# Relative differentials for morphisms of schemes

For a morphism `f : X ⟶ S`, the sheaf of relative differentials is the cokernel of the
absolute cotangent map `f^* Ω_{S/ℤ} ⟶ Ω_{X/ℤ}`. Over compatible affine opens, the
Jacobi–Zariski sequence identifies its sections with the Kähler differentials of the
coordinate-ring map (`Scheme.Hom.relativeDifferentialsSectionsEquiv`). The underlying
`TauCeti.AlgebraicGeometry.cotangentCokernelSectionsEquiv` works over any base ring.

The sheaf represents relative derivations (`Scheme.Hom.relativeDifferentialsHomEquiv`).
For a scheme over `Spec R`, `Scheme.relativeDifferentialsIsoOverSpec` compares it with the
sheaf of differentials over `R`. Over the inverse image of an affine open in the base,
`Scheme.Hom.relativeDifferentialsRestrictPreimageIso` gives the corresponding local comparison.
The sheaf is quasi-coherent and is of finite type or finite presentation when the morphism
is locally of finite type or locally of finite presentation, respectively.

A commutative square induces the canonical map `g'^* Ω_{X/S} ⟶ Ω_{X'/S'}`
(`Scheme.Hom.relativeDifferentialsPullbackHom`). For a cartesian square this map is an
isomorphism (`Scheme.Hom.relativeDifferentialsBaseChangeIso`).

## References

* The Stacks Project, [Section 29.33, Sheaf of differentials of a morphism](
  https://stacks.math.columbia.edu/tag/01UM).
-/

public section

noncomputable section

open CategoryTheory Limits Opposite AlgebraicGeometry TopologicalSpace

universe u

namespace TauCeti.AlgebraicGeometry

/-- Over compatible affine opens `V` of `Y` and `U ≤ f⁻¹ V` of `X`, the sections of
`cokernel (cotangentMap R f)` over `U` identify with the relative Kähler differentials
`Ω[Γ(X, U)⁄Γ(Y, V)]`. -/
def cotangentCokernelSectionsEquiv (R : Type u) [CommRing R] {X Y : Scheme.{u}}
    [X.Over (Spec (.of R))] [Y.Over (Spec (.of R))] (f : X ⟶ Y) [f.IsOver (Spec (.of R))]
    (V : Y.affineOpens) (U : X.affineOpens) (hUV : U.val ≤ f ⁻¹ᵁ V.val) :
    letI : Algebra Γ(Y, V) Γ(X, U) := (f.appLE V.val U.val hUV).hom.toAlgebra
    Ω[Γ(X, U)⁄Γ(Y, V)] ≃ₗ[Γ(X, U)] Γ(cokernel (cotangentMap R f), U.val) := by
  letI : Algebra R Γ(Y, V) := ((Y.baseRingToStructurePresheaf R).app (op V.val)).hom.toAlgebra
  letI : Algebra R Γ(X, U) := ((X.baseRingToStructurePresheaf R).app (op U.val)).hom.toAlgebra
  letI : Algebra Γ(Y, V) Γ(X, U) := (f.appLE V.val U.val hUV).hom.toAlgebra
  haveI : IsScalarTower R Γ(Y, V) Γ(X, U) :=
    Scheme.Modules.isScalarTower_baseRingToStructurePresheaf_appLE R f V.val U.val hUV
  let F := Scheme.Modules.sectionsFunctor U.val
  let eSrc := pullbackRelativeDifferentialsSectionsEquiv R f V U hUV
  let eTgt : Ω[Γ(X, U)⁄R] ≃ₗ[Γ(X, U)] F.obj (X.relativeDifferentials R) :=
    relativeDifferentialsSectionsEquiv R X U
  have hker : Submodule.map eTgt.toLinearMap
      (LinearMap.ker (KaehlerDifferential.map R Γ(Y, V) Γ(X, U) Γ(X, U))) =
      LinearMap.range (F.map (cotangentMap R f)).hom := by
    rw [← KaehlerDifferential.range_mapBaseChange R Γ(Y, V) Γ(X, U)]
    ext s
    constructor
    · rintro ⟨_, ⟨η, rfl⟩, rfl⟩
      exact ⟨eSrc η, cotangentMap_app_pullbackRelativeDifferentialsSectionsEquiv R f V U hUV η⟩
    · rintro ⟨t, rfl⟩
      refine ⟨KaehlerDifferential.mapBaseChange R Γ(Y, V) Γ(X, U) (eSrc.symm t),
        ⟨eSrc.symm t, rfl⟩, ?_⟩
      exact (cotangentMap_app_pullbackRelativeDifferentialsSectionsEquiv R f V U hUV
        (eSrc.symm t)).symm.trans
        (congrArg ((cotangentMap R f).app U.val) (eSrc.apply_symm_apply t))
  let eQuot := Submodule.Quotient.equiv
    (LinearMap.ker (KaehlerDifferential.map R Γ(Y, V) Γ(X, U) Γ(X, U)))
    (LinearMap.range (F.map (cotangentMap R f)).hom) eTgt hker
  exact (LinearMap.quotKerEquivOfSurjective _
    (KaehlerDifferential.map_surjective R Γ(Y, V) Γ(X, U))).symm.trans
      (eQuot.trans (cokernelSectionsEquiv (cotangentMap R f) U))

/-- `cotangentCokernelSectionsEquiv` sends the relative Kähler differential `D a` of `a ∈ Γ(X, U)`
to the image of `(X.universalDerivation R).d a` in `Γ(cokernel (cotangentMap R f), U)`. -/
@[simp]
theorem cotangentCokernelSectionsEquiv_D (R : Type u) [CommRing R] {X Y : Scheme.{u}}
    [X.Over (Spec (.of R))] [Y.Over (Spec (.of R))] (f : X ⟶ Y) [f.IsOver (Spec (.of R))]
    (V : Y.affineOpens) (U : X.affineOpens) (hUV : U.val ≤ f ⁻¹ᵁ V.val) (a : Γ(X, U)) :
    letI : Algebra Γ(Y, V) Γ(X, U) := (f.appLE V.val U.val hUV).hom.toAlgebra
    cotangentCokernelSectionsEquiv R f V U hUV (KaehlerDifferential.D Γ(Y, V) Γ(X, U) a) =
      (cokernel.π (cotangentMap R f)).app U.val ((X.universalDerivation R).d (X := op U.val) a)
          := by
  let : Algebra R Γ(Y, V) := ((Y.baseRingToStructurePresheaf R).app (op V.val)).hom.toAlgebra
  let : Algebra R Γ(X, U) := ((X.baseRingToStructurePresheaf R).app (op U.val)).hom.toAlgebra
  let : Algebra Γ(Y, V) Γ(X, U) := (f.appLE V.val U.val hUV).hom.toAlgebra
  have : IsScalarTower R Γ(Y, V) Γ(X, U) :=
    Scheme.Modules.isScalarTower_baseRingToStructurePresheaf_appLE R f V.val U.val hUV
  have hmk : (LinearMap.quotKerEquivOfSurjective
      (KaehlerDifferential.map R Γ(Y, V) Γ(X, U) Γ(X, U))
      (KaehlerDifferential.map_surjective R Γ(Y, V) Γ(X, U))).symm
        (KaehlerDifferential.D Γ(Y, V) Γ(X, U) a) =
      Submodule.Quotient.mk (KaehlerDifferential.D R Γ(X, U) a) :=
    LinearEquiv.symm_apply_eq _ |>.mpr (KaehlerDifferential.map_D R Γ(Y, V) Γ(X, U) Γ(X, U) a).symm
  dsimp only [cotangentCokernelSectionsEquiv, LinearEquiv.trans_apply]
  rw [hmk]
  let eTgt : Ω[Γ(X, U)⁄R] ≃ₗ[Γ(X, U)]
      (Scheme.Modules.sectionsFunctor U.val).obj (X.relativeDifferentials R) :=
    relativeDifferentialsSectionsEquiv R X U
  exact (congrArg (cokernelSectionsEquiv (cotangentMap R f) U)
    ((Submodule.Quotient.equiv_apply _ _ eTgt _ _).trans (Submodule.mapQ_apply _ _ _ _))).trans
    ((cokernelSectionsEquiv_mk (cotangentMap R f) U _).trans
      (congrArg ((cokernel.π (cotangentMap R f)).app U.val)
        (relativeDifferentialsSectionsEquiv_D R X U a)))

/-- The inverse of `cotangentCokernelSectionsEquiv` sends the image of
`(X.universalDerivation R).d a` in `Γ(cokernel (cotangentMap R f), U)` to the relative Kähler
differential `D a`. -/
@[simp]
theorem cotangentCokernelSectionsEquiv_symm_π_d (R : Type u) [CommRing R] {X Y : Scheme.{u}}
    [X.Over (Spec (.of R))] [Y.Over (Spec (.of R))] (f : X ⟶ Y) [f.IsOver (Spec (.of R))]
    (V : Y.affineOpens) (U : X.affineOpens) (hUV : U.val ≤ f ⁻¹ᵁ V.val) (a : Γ(X, U)) :
    letI : Algebra Γ(Y, V) Γ(X, U) := (f.appLE V.val U.val hUV).hom.toAlgebra
    (cotangentCokernelSectionsEquiv R f V U hUV).symm
        ((cokernel.π (cotangentMap R f)).app U.val ((X.universalDerivation R).d (X
            := op U.val) a)) =
      KaehlerDifferential.D Γ(Y, V) Γ(X, U) a := by
  let : Algebra Γ(Y, V) Γ(X, U) := (f.appLE V.val U.val hUV).hom.toAlgebra
  exact (LinearEquiv.symm_apply_eq _).mpr (cotangentCokernelSectionsEquiv_D R f V U hUV a).symm

end TauCeti.AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Hom

open TauCeti.AlgebraicGeometry

private local instance absoluteOver (X : Scheme.{u}) : X.Over (Spec (.of (ULift.{u} ℤ))) :=
  ⟨specULiftZIsTerminal.from X⟩

private local instance absoluteIsOver {X S : Scheme.{u}} (f : X ⟶ S) :
    f.IsOver (Spec (.of (ULift.{u} ℤ))) :=
  ⟨specULiftZIsTerminal.hom_ext _ _⟩

variable {X S X' S' : Scheme.{u}}

/-- The sheaf `Ω_{X/S}` of relative differentials of a morphism `f : X ⟶ S`. -/
def relativeDifferentials (f : X ⟶ S) : X.Modules :=
  cokernel (cotangentMap (ULift.{u} ℤ) f)

/-- Relative differentials are quasi-coherent for any morphism of schemes. -/
instance isQuasicoherent_relativeDifferentials (f : X ⟶ S) :
    f.relativeDifferentials.IsQuasicoherent :=
  Scheme.Modules.isQuasicoherent_cokernel _

private def absoluteToRelative (f : X ⟶ S) :
    X.relativeDifferentials (ULift.{u} ℤ) ⟶ f.relativeDifferentials :=
  cokernel.π (cotangentMap (ULift.{u} ℤ) f)

/-- The relative differential of a local function for a morphism `f : X ⟶ S`. -/
def relativeDifferential (f : X ⟶ S) (U : X.Opens) (a : Γ(X, U)) :
    Γ(f.relativeDifferentials, U) :=
  (absoluteToRelative f).app U
    ((X.universalDerivation (ULift.{u} ℤ)).d (X := op U) a)

/-- On affine opens `U ⊆ X` and `V ⊆ S` with `f(U) ⊆ V`, the sections of `Ω_{X/S}`
are the Kähler differentials of `Γ(X,U)` over `Γ(S,V)`. -/
def relativeDifferentialsSectionsEquiv (f : X ⟶ S)
    (V : S.affineOpens) (U : X.affineOpens) (hUV : U.val ≤ f ⁻¹ᵁ V.val) :
    letI : Algebra Γ(S, V) Γ(X, U) := (f.appLE V.val U.val hUV).hom.toAlgebra
    Ω[Γ(X, U)⁄Γ(S, V)] ≃ₗ[Γ(X, U)] Γ(f.relativeDifferentials, U.val) :=
  cotangentCokernelSectionsEquiv (ULift.{u} ℤ) f V U hUV

/-- The affine comparison sends the Kähler differential of a function to its sheaf differential. -/
@[simp]
theorem relativeDifferentialsSectionsEquiv_D (f : X ⟶ S)
    (V : S.affineOpens) (U : X.affineOpens) (hUV : U.val ≤ f ⁻¹ᵁ V.val) (a : Γ(X, U)) :
    letI : Algebra Γ(S, V) Γ(X, U) := (f.appLE V.val U.val hUV).hom.toAlgebra
    f.relativeDifferentialsSectionsEquiv V U hUV (KaehlerDifferential.D Γ(S, V) Γ(X, U) a) =
      f.relativeDifferential U.val a :=
  cotangentCokernelSectionsEquiv_D (ULift.{u} ℤ) f V U hUV a

/-- The inverse affine comparison sends a sheaf differential to the Kähler differential. -/
@[simp]
theorem relativeDifferentialsSectionsEquiv_symm_relativeDifferential (f : X ⟶ S)
    (V : S.affineOpens) (U : X.affineOpens) (hUV : U.val ≤ f ⁻¹ᵁ V.val) (a : Γ(X, U)) :
    letI : Algebra Γ(S, V) Γ(X, U) := (f.appLE V.val U.val hUV).hom.toAlgebra
    (f.relativeDifferentialsSectionsEquiv V U hUV).symm (f.relativeDifferential U.val a) =
      KaehlerDifferential.D Γ(S, V) Γ(X, U) a := by
  let : Algebra Γ(S, V) Γ(X, U) := (f.appLE V.val U.val hUV).hom.toAlgebra
  rw [← f.relativeDifferentialsSectionsEquiv_D V U hUV a, LinearEquiv.symm_apply_apply]

/-- The relative differential vanishes on functions pulled back from the base. -/
@[simp]
theorem relativeDifferential_appLE (f : X ⟶ S) (V : S.Opens) (U : X.Opens)
    (hUV : U ≤ f ⁻¹ᵁ V) (b : Γ(S, V)) :
    f.relativeDifferential U (f.appLE V U hUV b) = 0 := by
  let R := ULift.{u} ℤ
  have h : cotangentMap R f ≫ absoluteToRelative f = 0 :=
    cokernel.condition (cotangentMap R f)
  let t := f.pullbackSectionsLE (S.relativeDifferentials R) V U hUV
    ((S.universalDerivation R).d (X := op V) b)
  have e := congr(($h).app U t)
  refine (congrArg ((absoluteToRelative f).app U)
    (cotangentMap_app_pullbackSectionsLE_d R f V U hUV b).symm).trans ?_
  exact e

/-- The universal relative derivation of the structure sheaf for a morphism of schemes. -/
def relativeDerivation (f : X ⟶ S) :
    PresheafOfModulesOfCommRing.Derivation f.relativeDifferentials.val f.c where
  d := ((X.universalDerivation (ULift.{u} ℤ)).postcomp (absoluteToRelative f).val).d
  d_mul := ((X.universalDerivation (ULift.{u} ℤ)).postcomp (absoluteToRelative f).val).d_mul
  d_map := ((X.universalDerivation (ULift.{u} ℤ)).postcomp (absoluteToRelative f).val).d_map
  d_app {V} b := by
    have h := relativeDifferential_appLE f V.unop (f ⁻¹ᵁ V.unop) le_rfl b
    rw [Scheme.Hom.appLE_eq_app] at h
    exact h

/-- The universal relative derivation sends a local function to its relative differential. -/
@[simp]
theorem relativeDerivation_d (f : X ⟶ S) (U : X.Opens) (a : Γ(X, U)) :
    dsimp% only [CategoryTheory.ObjectProperty.ι_obj]
    (f.relativeDerivation.d (X := op U) a = f.relativeDifferential U a) := (rfl)

/-- A morphism out of the sheaf of relative differentials is determined by its values on the
differentials of local functions. -/
@[ext]
theorem relativeDifferentials_hom_ext (f : X ⟶ S) {M : X.Modules}
    {φ ψ : f.relativeDifferentials ⟶ M}
    (h : ∀ (U : X.Opens) (a : Γ(X, U)),
      φ.app U (f.relativeDifferential U a) = ψ.app U (f.relativeDifferential U a)) : φ = ψ := by
  have : Epi (absoluteToRelative f) :=
    inferInstanceAs (Epi (cokernel.π (cotangentMap (ULift.{u} ℤ) f)))
  apply (cancel_epi (absoluteToRelative f)).mp
  apply X.relativeDifferentials_hom_ext (ULift.{u} ℤ)
  intro U a
  exact h U.unop a

private def absoluteDerivation {f : X ⟶ S} {M : X.Modules}
    (D : PresheafOfModulesOfCommRing.Derivation M.val f.c) : M.Derivation (ULift.{u} ℤ) where
  d := D.d
  d_mul := D.d_mul
  d_map := D.d_map
  d_app {U} a := by
    obtain ⟨n⟩ := a
    have h := map_intCast (((X.baseRingToStructurePresheaf (ULift.{u} ℤ)).app U).hom.comp
      ULift.ringEquiv.symm.toRingHom) n
    refine (congrArg (D.d (X := U)) h).trans ?_
    rw [← zsmul_one, map_zsmul, D.d_one, smul_zero]

private theorem cotangentMap_comp_of_derivation {f : X ⟶ S} {M : X.Modules}
    (D : PresheafOfModulesOfCommRing.Derivation M.val f.c) :
    cotangentMap (ULift.{u} ℤ) f ≫
      (X.relativeDifferentialsHomEquiv (ULift.{u} ℤ) M).symm (absoluteDerivation D) = 0 := by
  apply pullback_relativeDifferentials_hom_ext (R := ULift.{u} ℤ) (f := f)
  intro V b
  let φ := (X.relativeDifferentialsHomEquiv (ULift.{u} ℤ) M).symm (absoluteDerivation D)
  have h := X.relativeDifferentialsHomEquiv_symm_fac (ULift.{u} ℤ) (absoluteDerivation D)
  have he := congr(($h).d (X := op (f ⁻¹ᵁ V)) (f.app V b))
  exact (congrArg (φ.app (f ⁻¹ᵁ V))
    (cotangentMap_app_pullbackSections_d (ULift.{u} ℤ) f V b)).trans
    (he.trans (D.d_app (X := op V) b))

private def relativeDifferentialsDesc {f : X ⟶ S} {M : X.Modules}
    (D : PresheafOfModulesOfCommRing.Derivation M.val f.c) : f.relativeDifferentials ⟶ M :=
  cokernel.desc (cotangentMap (ULift.{u} ℤ) f)
    ((X.relativeDifferentialsHomEquiv (ULift.{u} ℤ) M).symm (absoluteDerivation D))
    (cotangentMap_comp_of_derivation D)

private theorem relativeDifferentialsDesc_app_d {f : X ⟶ S} {M : X.Modules}
    (D : PresheafOfModulesOfCommRing.Derivation M.val f.c) (U : X.Opens) (a : Γ(X, U)) :
    (relativeDifferentialsDesc D).app U (f.relativeDifferential U a) = D.d (X := op U) a := by
  have hπ := cokernel.π_desc (cotangentMap (ULift.{u} ℤ) f)
    ((X.relativeDifferentialsHomEquiv (ULift.{u} ℤ) M).symm (absoluteDerivation D))
    (cotangentMap_comp_of_derivation D)
  have h := X.relativeDifferentialsHomEquiv_symm_fac (ULift.{u} ℤ) (absoluteDerivation D)
  exact (congr(($hπ).app U ((X.universalDerivation (ULift.{u} ℤ)).d (X := op U) a))).trans
    congr(($h).d (X := op U) a)

/-- Morphisms from the relative differential sheaf to a module correspond to derivations over
the base with values in that module, by composition with the universal derivation. -/
def relativeDifferentialsHomEquiv (f : X ⟶ S) (M : X.Modules) :
    (f.relativeDifferentials ⟶ M) ≃ PresheafOfModulesOfCommRing.Derivation M.val f.c where
  toFun φ := f.relativeDerivation.postcomp φ.val
  invFun := relativeDifferentialsDesc
  left_inv φ := f.relativeDifferentials_hom_ext fun U a ↦
    relativeDifferentialsDesc_app_d (f.relativeDerivation.postcomp φ.val) U a
  right_inv D := by
    ext U a
    exact relativeDifferentialsDesc_app_d D U.unop a

/-- The equivalence sends a morphism to its composition with the universal derivation. -/
@[simp]
theorem relativeDifferentialsHomEquiv_apply (f : X ⟶ S) {M : X.Modules}
    (φ : f.relativeDifferentials ⟶ M) :
    f.relativeDifferentialsHomEquiv M φ = f.relativeDerivation.postcomp φ.val := (rfl)

/-- The morphism associated to a derivation sends the differential of a function to its value
under that derivation. -/
@[simp]
theorem relativeDifferentialsHomEquiv_symm_app_relativeDifferential (f : X ⟶ S) {M : X.Modules}
    (D : PresheafOfModulesOfCommRing.Derivation M.val f.c) (U : X.Opens) (a : Γ(X, U)) :
    ((f.relativeDifferentialsHomEquiv M).symm D).app U (f.relativeDifferential U a) =
      D.d (X := op U) a :=
  relativeDifferentialsDesc_app_d D U a

section AffineBase

variable (R : Type u) [CommRing R] (X : Scheme.{u}) [X.Over (Spec (.of R))]

private def relativeDerivationOverSpec :
    ((X ↘ Spec (.of R)).relativeDifferentials).Derivation R where
  d := (X ↘ Spec (.of R)).relativeDerivation.d
  d_mul := (X ↘ Spec (.of R)).relativeDerivation.d_mul
  d_map := (X ↘ Spec (.of R)).relativeDerivation.d_map
  d_app {U} b := by
    have h := X.baseRingToStructurePresheaf_app_eq_appLE R U.unop
    exact (congrArg ((X ↘ Spec (.of R)).relativeDifferential U.unop)
      (congr($h b))).trans
      (relativeDifferential_appLE (X ↘ Spec (.of R)) ⊤ U.unop le_top
        ((Scheme.ΓSpecIso (.of R)).inv b))

private def relativeDifferentialsHomOverSpec :
    X.relativeDifferentials R ⟶ (X ↘ Spec (.of R)).relativeDifferentials :=
  (X.relativeDifferentialsHomEquiv R _).symm (relativeDerivationOverSpec R X)

private theorem relativeDifferentialsHomOverSpec_app_d (U : X.Opens) (a : Γ(X, U)) :
    (relativeDifferentialsHomOverSpec R X).app U ((X.universalDerivation R).d (X := op U) a) =
      (X ↘ Spec (.of R)).relativeDifferential U a := by
  have h := X.relativeDifferentialsHomEquiv_symm_fac R (relativeDerivationOverSpec R X)
  exact congr(($h).d (X := op U) a)

private theorem bijective_relativeDifferentialsHomOverSpec_app (U : X.affineOpens) :
    Function.Bijective ((relativeDifferentialsHomOverSpec R X).app U.val) := by
  let f := X ↘ Spec (.of R)
  let V : (Spec (.of R)).affineOpens := ⟨⊤, isAffineOpen_top _⟩
  let B := Γ(Spec (.of R), ⊤)
  let A := Γ(X, U)
  let : Algebra R A := ((X.baseRingToStructurePresheaf R).app (op U.val)).hom.toAlgebra
  let : Algebra R B := (Scheme.ΓSpecIso (.of R)).inv.hom.toAlgebra
  let : Algebra B A := (f.appLE ⊤ U.val le_top).hom.toAlgebra
  have : IsScalarTower R B A := .of_algebraMap_eq'
    (congrArg CommRingCat.Hom.hom (X.baseRingToStructurePresheaf_app_eq_appLE R U.val))
  have hsurj : Function.Surjective (algebraMap R B) :=
    (Scheme.ΓSpecIso (.of R)).commRingCatIsoToRingEquiv.symm.surjective
  have : Algebra.FormallyUnramified R B := .of_surjective (Algebra.ofId R B) hsurj
  have hmap : Function.Bijective (KaehlerDifferential.map R B A A) := by
    refine ⟨LinearMap.ker_eq_bot.mp ?_, KaehlerDifferential.map_surjective R B A⟩
    rw [← KaehlerDifferential.range_mapBaseChange]
    apply LinearMap.range_eq_bot.mpr
    exact LinearMap.ext fun x ↦ by
      rw [Subsingleton.elim x 0, map_zero, LinearMap.zero_apply]
  let e := TauCeti.AlgebraicGeometry.relativeDifferentialsSectionsEquiv R X U
  let e' := f.relativeDifferentialsSectionsEquiv V U le_top
  let φ : Γ(X.relativeDifferentials R, U.val) →ₗ[A] Γ(f.relativeDifferentials, U.val) :=
    { toFun := (relativeDifferentialsHomOverSpec R X).app U.val
      map_add' := map_add _
      map_smul' := (relativeDifferentialsHomOverSpec R X).app_smul }
  have he : φ.comp e.toLinearMap =
      e'.toLinearMap.comp (KaehlerDifferential.map R B A A) := by
    apply LinearMap.ext_on_range (KaehlerDifferential.span_range_derivation R A)
    intro a
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, KaehlerDifferential.map_D]
    refine (congrArg φ
      (TauCeti.AlgebraicGeometry.relativeDifferentialsSectionsEquiv_D R X U a)).trans ?_
    exact (relativeDifferentialsHomOverSpec_app_d R X U.val a).trans
      (f.relativeDifferentialsSectionsEquiv_D V U le_top a).symm
  exact (Function.Bijective.of_comp_iff φ e.bijective).mp
    (he.symm ▸ e'.bijective.comp hmap :
      Function.Bijective (φ.comp e.toLinearMap))

/-- For a scheme over an affine base, its relative differentials agree with the sheaf of
differentials over the base ring. -/
def _root_.AlgebraicGeometry.Scheme.relativeDifferentialsIsoOverSpec :
    X.relativeDifferentials R ≅ (X ↘ Spec (.of R)).relativeDifferentials :=
  letI := Scheme.Modules.Hom.isIso_of_bijective_app (relativeDifferentialsHomOverSpec R X)
    (fun U : X.affineOpens ↦ U.property) (iSup_affineOpens_eq_top X)
    (bijective_relativeDifferentialsHomOverSpec_app R X)
  asIso (relativeDifferentialsHomOverSpec R X)

/-- The affine-base comparison preserves the differential of every local function. -/
@[simp]
theorem _root_.AlgebraicGeometry.Scheme.relativeDifferentialsIsoOverSpec_hom_app_d
    (U : X.Opens) (a : Γ(X, U)) :
    (Scheme.relativeDifferentialsIsoOverSpec R X).hom.app U
        ((X.universalDerivation R).d (X := op U) a) =
      (X ↘ Spec (.of R)).relativeDifferential U a :=
  relativeDifferentialsHomOverSpec_app_d R X U a

end AffineBase

section CommSq

variable (g' : X' ⟶ X) {f : X ⟶ S} {f' : X' ⟶ S'} {g : S' ⟶ S}
  (H : CommSq g' f' f g)

include H in
private theorem cotangentMap_comp_π_of_commSq :
    (Scheme.Modules.pullback g').map (cotangentMap (ULift.{u} ℤ) f) ≫
      cotangentMap (ULift.{u} ℤ) g' ≫ cokernel.π (cotangentMap (ULift.{u} ℤ) f') = 0 := by
  rw [← cancel_epi ((Scheme.Modules.pullbackComp g' f).inv.app
    (S.relativeDifferentials (ULift.{u} ℤ))), comp_zero, ← cotangentMap_comp_assoc,
    ← cotangentMap_congr_assoc (ULift.{u} ℤ) H.w, cotangentMap_comp_assoc]
  simp only [cokernel.condition, comp_zero]

/-- The canonical map `g'^* Ω_{X/S} ⟶ Ω_{X'/S'}` associated to a commutative square. -/
def relativeDifferentialsPullbackHom :
    (Scheme.Modules.pullback g').obj f.relativeDifferentials ⟶ f'.relativeDifferentials :=
  (PreservesCokernel.iso (Scheme.Modules.pullback g') (cotangentMap (ULift.{u} ℤ) f)).hom ≫
    cokernel.desc _ (cotangentMap (ULift.{u} ℤ) g' ≫ cokernel.π (cotangentMap (ULift.{u} ℤ) f'))
      (cotangentMap_comp_π_of_commSq g' H)

private theorem pullback_π_comp_relativeDifferentialsPullbackHom :
    (Scheme.Modules.pullback g').map (absoluteToRelative f) ≫
        relativeDifferentialsPullbackHom g' H =
      cotangentMap (ULift.{u} ℤ) g' ≫ absoluteToRelative f' := by
  -- Work in the cokernel presentation so that the preservation lemma can match the projection.
  change (Scheme.Modules.pullback g').map (cokernel.π (cotangentMap (ULift.{u} ℤ) f)) ≫
      (PreservesCokernel.iso (Scheme.Modules.pullback g') (cotangentMap (ULift.{u} ℤ) f)).hom ≫
        cokernel.desc _ _ (cotangentMap_comp_π_of_commSq g' H) = _
  rw [PreservesCokernel.π_iso_hom_assoc, cokernel.π_desc]
  rfl

/-- The map on relative differentials sends the pullback of a differential to the differential
of the pulled-back function, also after restricting to a smaller open. -/
@[simp]
theorem relativeDifferentialsPullbackHom_app_pullbackSectionsLE_relativeDifferential
    (U : X.Opens) (U' : X'.Opens) (hU : U' ≤ g' ⁻¹ᵁ U) (a : Γ(X, U)) :
    (relativeDifferentialsPullbackHom g' H).app U'
        (g'.pullbackSectionsLE f.relativeDifferentials U U' hU (f.relativeDifferential U a)) =
      f'.relativeDifferential U' (g'.appLE U U' hU a) := by
  let R := ULift.{u} ℤ
  let d := (X.universalDerivation R).d (X := op U) a
  have h := g'.pullbackSectionsLE_naturality (X.relativeDifferentials R) U U' hU
    (absoluteToRelative f) d
  refine (congrArg ((relativeDifferentialsPullbackHom g' H).app U') h.symm).trans ?_
  have hπ := congr($(pullback_π_comp_relativeDifferentialsPullbackHom g' H).app U'
    (g'.pullbackSectionsLE (X.relativeDifferentials R) U U' hU d))
  refine hπ.trans ?_
  exact congrArg ((absoluteToRelative f').app U')
    (cotangentMap_app_pullbackSectionsLE_d R g' U U' hU a)

end CommSq

section BaseChange

open TensorProduct

variable {g' : X' ⟶ X} {f : X ⟶ S} {f' : X' ⟶ S'} {g : S' ⟶ S}

private theorem bijective_relativeDifferentialsPullbackHom_app (H : IsPullback g' f' f g)
    (V : S.affineOpens) (U : X.affineOpens) (V' : S'.affineOpens)
    (hU : U.val ≤ f ⁻¹ᵁ V.val) (hV' : V'.val ≤ g ⁻¹ᵁ V.val)
    (hW : IsAffineOpen (g' ⁻¹ᵁ U.val ⊓ f' ⁻¹ᵁ V'.val)) :
    Function.Bijective ((relativeDifferentialsPullbackHom g' H.toCommSq).app
      (g' ⁻¹ᵁ U.val ⊓ f' ⁻¹ᵁ V'.val)) := by
  let W := g' ⁻¹ᵁ U.val ⊓ f' ⁻¹ᵁ V'.val
  let R := Γ(S, V)
  let R' := Γ(S', V')
  let A := Γ(X, U)
  let B := Γ(X', W)
  let : Algebra R A := (f.appLE V.val U.val hU).hom.toAlgebra
  let : Algebra R R' := (g.appLE V.val V'.val hV').hom.toAlgebra
  let : Algebra A B := (g'.appLE U.val W inf_le_left).hom.toAlgebra
  let : Algebra R' B := (f'.appLE V'.val W inf_le_right).hom.toAlgebra
  let : Algebra R B := ((f.appLE V.val U.val hU ≫ g'.appLE U.val W inf_le_left).hom).toAlgebra
  have hP := (isIso_pushoutSection_iff H hV' hU (UY := W) rfl).mp
    (isIso_pushoutSection_of_isAffineOpen H hV' hU rfl V.property V'.property U.property)
  have : IsScalarTower R A B := .of_algebraMap_eq' rfl
  have : IsScalarTower R R' B := .of_algebraMap_eq' (congrArg CommRingCat.Hom.hom hP.w)
  have : Algebra.IsPushout R R' A B := CommRingCat.isPushout_iff_isPushout.mp hP.flip
  let M := f.relativeDifferentials
  let N := (Scheme.Modules.pullback g').obj M
  let : Module A Γ(N, W) := Module.compHom _ (algebraMap A B)
  have : IsScalarTower A B Γ(N, W) := .of_algebraMap_smul fun _ _ ↦ rfl
  let ρ : Γ(M, U.val) →ₗ[A] Γ(N, W) :=
    { toFun := g'.pullbackSectionsLE M U.val W inf_le_left
      map_add' := map_add _
      map_smul' := (g'.pullbackSectionsLE M U.val W inf_le_left).map_smulₛₗ }
  have hρ := g'.isBaseChange_pullbackSectionsLE M U.property hW inf_le_left
    (fun _ ↦ rfl) ρ (fun _ ↦ rfl)
  let e := ((f.relativeDifferentialsSectionsEquiv V U hU).baseChange A B).trans hρ.equiv
  let e' := (KaehlerDifferential.tensorKaehlerEquiv R R' A B).trans
    (f'.relativeDifferentialsSectionsEquiv V' ⟨W, hW⟩ inf_le_right)
  let φ : Γ(N, W) →ₗ[B] Γ(f'.relativeDifferentials, W) :=
    { toFun := (relativeDifferentialsPullbackHom g' H.toCommSq).app W
      map_add' := map_add _
      map_smul' := (relativeDifferentialsPullbackHom g' H.toCommSq).app_smul }
  have he : φ.comp e.toLinearMap = e'.toLinearMap := by
    apply TauCeti.kaehlerBaseChange_linearMap_ext
    intro a
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, e, e', LinearEquiv.trans_apply,
      LinearEquiv.baseChange_tmul]
    refine (congrArg φ ((hρ.equiv_tmul 1 _).trans ((one_smul B _).trans
      (congrArg ρ (f.relativeDifferentialsSectionsEquiv_D V U hU a))))).trans ?_
    refine (relativeDifferentialsPullbackHom_app_pullbackSectionsLE_relativeDifferential
      g' H.toCommSq U.val W inf_le_left a).trans ?_
    refine ((f'.relativeDifferentialsSectionsEquiv_D V' ⟨W, hW⟩ inf_le_right
      (g'.appLE U.val W inf_le_left a)).symm).trans ?_
    exact (congrArg (f'.relativeDifferentialsSectionsEquiv V' ⟨W, hW⟩ inf_le_right)
      ((KaehlerDifferential.tensorKaehlerEquiv_tmul_D R R' A B 1 a).trans
        (one_smul B _))).symm
  exact (Function.Bijective.of_comp_iff φ e.bijective).mp
    (he ▸ e'.bijective : Function.Bijective (φ.comp e.toLinearMap))

variable (g') in
/-- The canonical map on relative differentials for a cartesian square is an isomorphism.
The base-change morphism is arbitrary. -/
theorem isIso_relativeDifferentialsPullbackHom (H : IsPullback g' f' f g) :
    IsIso (relativeDifferentialsPullbackHom g' H.toCommSq) := by
  let I := Σ V : S.affineOpens,
    {U : X.affineOpens // U.val ≤ f ⁻¹ᵁ V.val} × {V' : S'.affineOpens // V'.val ≤ g ⁻¹ᵁ V.val}
  let W (i : I) := g' ⁻¹ᵁ i.2.1.val.val ⊓ f' ⁻¹ᵁ i.2.2.val.val
  have hW (i : I) : IsAffineOpen (W i) :=
    .of_isIso (isPullback_resLE H i.2.2.property i.2.1.property (UY := W i) rfl).isoPullback.hom
  refine Scheme.Modules.Hom.isIso_of_bijective_app _ hW ?_ (fun i ↦ ?_)
  · refine top_unique fun x _ ↦ ?_
    obtain ⟨V, hV, hxV, _⟩ := exists_isAffineOpen_mem_and_subset
      (x := f (g' x)) (U := ⊤) trivial
    have hxV' : g (f' x) ∈ V :=
      (congrArg (fun k : X' ⟶ S ↦ k x) H.w).symm ▸ hxV
    obtain ⟨U, hU, hxU, hUV⟩ := exists_isAffineOpen_mem_and_subset
      (U := f ⁻¹ᵁ V) hxV
    obtain ⟨V', hV', hxV', hV'V⟩ := exists_isAffineOpen_mem_and_subset
      (U := g ⁻¹ᵁ V) hxV'
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨⟨V, hV⟩, ⟨⟨U, hU⟩, hUV⟩, ⟨⟨V', hV'⟩, hV'V⟩⟩,
      TopologicalSpace.Opens.mem_inf.mpr ⟨hxU, hxV'⟩⟩
  · exact bijective_relativeDifferentialsPullbackHom_app H i.1 i.2.1.val i.2.2.val
      i.2.1.property i.2.2.property (hW i)

variable (g') in
/-- Canonical base change of the sheaf of relative differentials along a cartesian square. -/
def relativeDifferentialsBaseChangeIso (H : IsPullback g' f' f g) :
    (Scheme.Modules.pullback g').obj f.relativeDifferentials ≅ f'.relativeDifferentials :=
  let := isIso_relativeDifferentialsPullbackHom g' H
  asIso (relativeDifferentialsPullbackHom g' H.toCommSq)

variable (g') in
/-- The base-change isomorphism is given by the canonical map on relative differentials. -/
@[simp]
theorem relativeDifferentialsBaseChangeIso_hom (H : IsPullback g' f' f g) :
    (relativeDifferentialsBaseChangeIso g' H).hom =
      relativeDifferentialsPullbackHom g' H.toCommSq :=
  (rfl)

end BaseChange

/-- The scheme over `Spec Γ(S,V)` obtained by restricting `f` to an affine open `V` of `S`. -/
@[instance_reducible]
def restrictPreimageOverSpec (f : X ⟶ S) (V : S.affineOpens) :
    (f ⁻¹ᵁ V.val).toScheme.Over (Spec (.of Γ(S, V))) :=
  ⟨(f ∣_ V.val) ≫ V.property.isoSpec.hom⟩

/-- The induced structure morphism is the restriction of `f` followed by the affine-open
isomorphism. -/
theorem restrictPreimageOverSpec_over (f : X ⟶ S) (V : S.affineOpens) :
    CategoryTheory.over _ _ (f.restrictPreimageOverSpec V) =
      (f ∣_ V.val) ≫ V.property.isoSpec.hom :=
  (rfl)

section RestrictPreimage

variable (f : X ⟶ S) (V : S.affineOpens)

private theorem isPullback_restrictPreimageOverSpec :
    IsPullback (f ⁻¹ᵁ V.val).ι (CategoryTheory.over _ _ (f.restrictPreimageOverSpec V)) f
      (V.property.isoSpec.inv ≫ V.val.ι) :=
  (isPullback_morphismRestrict f V.val).flip.of_iso
    (.refl _) (.refl _) V.property.isoSpec (.refl _) (by simp)
    (by simp [restrictPreimageOverSpec_over]) (by simp) (by simp)

/-- On the inverse image of an affine open `V` of the base, the relative differentials are the
differentials over `Γ(S, V)` with the induced structure morphism. -/
def relativeDifferentialsRestrictPreimageIso :
    f.relativeDifferentials.restrict (f ⁻¹ᵁ V.val).ι ≅
      @Scheme.relativeDifferentials Γ(S, V) _ _ (f.restrictPreimageOverSpec V) :=
  (Scheme.Modules.restrictFunctorIsoPullback (f ⁻¹ᵁ V.val).ι).app f.relativeDifferentials ≪≫
    relativeDifferentialsBaseChangeIso (f ⁻¹ᵁ V.val).ι (isPullback_restrictPreimageOverSpec f V) ≪≫
      (@Scheme.relativeDifferentialsIsoOverSpec Γ(S, V) _ _ (f.restrictPreimageOverSpec V)).symm

/-- Restriction over an affine open of the base carries the differential of a local function
to the differential of its pullback to the inverse-image scheme. -/
@[simp]
theorem relativeDifferentialsRestrictPreimageIso_hom_app_relativeDifferential
    (W : (f ⁻¹ᵁ V.val).toScheme.Opens) (a : Γ(X, (f ⁻¹ᵁ V.val).ι ''ᵁ W)) :
    (f.relativeDifferentialsRestrictPreimageIso V).hom.app W
        ((f.relativeDifferentials.restrictAppIso (f ⁻¹ᵁ V.val).ι W).inv
          (f.relativeDifferential ((f ⁻¹ᵁ V.val).ι ''ᵁ W) a)) =
      (@Scheme.universalDerivation Γ(S, V) _ _ (f.restrictPreimageOverSpec V)).d
        (X := op W) (((f ⁻¹ᵁ V.val).ι.appIso W).hom a) := by
  let j := (f ⁻¹ᵁ V.val).ι
  let e := @Scheme.relativeDifferentialsIsoOverSpec Γ(S, V) _ _ (f.restrictPreimageOverSpec V)
  let b := (j.appIso W).hom a
  trans e.inv.app W ((CategoryTheory.over _ _ (f.restrictPreimageOverSpec V)).relativeDifferential
    W b)
  · simp only [relativeDifferentialsRestrictPreimageIso, Iso.trans_hom, Iso.app_hom,
      Scheme.Modules.Hom.comp_app, Iso.symm_hom, ConcreteCategory.comp_apply,
      Scheme.Modules.restrictFunctorIsoPullback_hom_app_restrictAppIso_inv,
      relativeDifferentialsBaseChangeIso_hom,
      relativeDifferentialsPullbackHom_app_pullbackSectionsLE_relativeDifferential,
      e, b, j, Scheme.Hom.appIso_hom']
  · have h := @Scheme.relativeDifferentialsIsoOverSpec_hom_app_d Γ(S, V) _ _
      (f.restrictPreimageOverSpec V) W b
    exact (congrArg (e.inv.app W) h.symm).trans (congr($(e.hom_inv_id).app W _))

/-- The inverse comparison sends a differential to the restriction of the differential of the
corresponding function on the image open. -/
@[simp]
theorem relativeDifferentialsRestrictPreimageIso_inv_app_d
    (W : (f ⁻¹ᵁ V.val).toScheme.Opens) (a : Γ((f ⁻¹ᵁ V.val).toScheme, W)) :
    (f.relativeDifferentialsRestrictPreimageIso V).inv.app W
        ((@Scheme.universalDerivation Γ(S, V) _ _ (f.restrictPreimageOverSpec V)).d (X := op W) a) =
      (f.relativeDifferentials.restrictAppIso (f ⁻¹ᵁ V.val).ι W).inv
        (f.relativeDifferential ((f ⁻¹ᵁ V.val).ι ''ᵁ W) (((f ⁻¹ᵁ V.val).ι.appIso W).inv a)) := by
  have h := f.relativeDifferentialsRestrictPreimageIso_hom_app_relativeDifferential V W
    (((f ⁻¹ᵁ V.val).ι.appIso W).inv a)
  simp only [Iso.inv_hom_id_apply] at h
  let e := f.relativeDifferentialsRestrictPreimageIso V
  exact (congrArg (e.inv.app W) h.symm).trans (congr($(e.hom_inv_id).app W _))

end RestrictPreimage

/-- Relative differentials of a morphism locally of finite type are of finite type. -/
instance isFiniteType_relativeDifferentials (f : X ⟶ S) [LocallyOfFiniteType f] :
    f.relativeDifferentials.IsFiniteType := by
  refine isFiniteType_of_isFiniteType_restrict _ (fun V : S.affineOpens ↦ f ⁻¹ᵁ V.val)
    (f.iSup_preimage_eq_top (iSup_affineOpens_eq_top S)) fun V ↦ ?_
  let U := f ⁻¹ᵁ V.val
  let : U.toScheme.Over (Spec (.of Γ(S, V))) := f.restrictPreimageOverSpec V
  have : LocallyOfFiniteType (U.toScheme ↘ Spec (.of Γ(S, V))) := by
    rw [restrictPreimageOverSpec_over]
    infer_instance
  have : (U.toScheme.relativeDifferentials Γ(S, V)).IsFiniteType :=
    Scheme.Modules.isFiniteType_of_finite_sections _ fun W hW ↦
      finite_relativeDifferentials_sections Γ(S, V) U.toScheme ⟨W, hW⟩
  exact SheafOfModules.IsFiniteType.of_iso (R := U.toScheme.ringCatSheaf)
    (f.relativeDifferentialsRestrictPreimageIso V).symm

/-- Relative differentials of a morphism locally of finite presentation are finitely presented. -/
instance isFinitePresentation_relativeDifferentials (f : X ⟶ S) [LocallyOfFinitePresentation f] :
    f.relativeDifferentials.IsFinitePresentation := by
  refine Scheme.Modules.isFinitePresentation_of_isFinitePresentation_restrict _
    (fun V : S.affineOpens ↦ f ⁻¹ᵁ V.val)
    (f.iSup_preimage_eq_top (iSup_affineOpens_eq_top S)) fun V ↦ ?_
  let U := f ⁻¹ᵁ V.val
  let : U.toScheme.Over (Spec (.of Γ(S, V))) := f.restrictPreimageOverSpec V
  have : LocallyOfFinitePresentation (U.toScheme ↘ Spec (.of Γ(S, V))) := by
    rw [restrictPreimageOverSpec_over]
    infer_instance
  exact (SheafOfModules.isFinitePresentation U.toScheme.ringCatSheaf).prop_of_iso
    (f.relativeDifferentialsRestrictPreimageIso V).symm inferInstance

end AlgebraicGeometry.Scheme.Hom

end
