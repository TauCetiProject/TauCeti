/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Smooth.Basic
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.FiniteType
public import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Invertible
public import TauCeti.AlgebraicGeometry.IdealSheaf.Image
public import TauCeti.AlgebraicGeometry.LineBundle.Dual
public import TauCeti.AlgebraicGeometry.LineBundle.Functoriality
public import TauCeti.AlgebraicGeometry.Modules.Differentials.Pullback
public import TauCeti.AlgebraicGeometry.Modules.Differentials.Rational
public import TauCeti.AlgebraicGeometry.Modules.FiniteType
public import TauCeti.AlgebraicGeometry.Modules.FittingIdeal.Basic
public import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.Cokernels
public import TauCeti.AlgebraicGeometry.Morphisms.Dominant
import Mathlib.RingTheory.Etale.Field
import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.ZeroLocus
import TauCeti.AlgebraicGeometry.Modules.FittingIdeal.Image
import TauCeti.AlgebraicGeometry.Modules.FittingIdeal.Invertible
import TauCeti.AlgebraicGeometry.Modules.FittingIdeal.Pullback
import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.Colimits
import TauCeti.RingTheory.Kaehler.BaseChange

/-!
# The ramification ideal sheaf and the Picard-group Riemann–Hurwitz relation

Let `f : X ⟶ Y` be a morphism of schemes over `Spec R`. The cotangent map
`cotangentMap R f : f^* Ω_{Y/R} ⟶ Ω_{X/R}` has quasi-coherent cokernel whose sections over
compatible affine opens `V ⊆ Y` and `U ⊆ f⁻¹(V)` are the relative Kähler differentials
`Ω[Γ(X, U)⁄Γ(Y, V)]` (`cotangentCokernelSectionsEquiv`), and whose formation commutes with
arbitrary base change `R → S` (`cotangentCokernelBaseChangeIso`).

Whenever `cokernel (cotangentMap R f)` is of finite type (in particular whenever `Ω_{X/R}` is of
finite type), its zeroth Fitting ideal sheaf is the **ramification ideal sheaf**
`ramificationIdealSheaf R f ⊆ 𝒪_X`. It restricts on compatible affine opens to
`Fitt₀(Ω[Γ(X, U)⁄Γ(Y, V)])` (`ramificationIdealSheaf_ideal_eq_fittingIdeal_kaehlerDifferential`)
and commutes with arbitrary base change `R → S` (`comap_ramificationIdealSheaf`). When `Ω_{X/R}`
and `Ω_{Y/R}` are invertible sheaves (for instance on smooth relative curves over `Spec R`),
`ramificationIdealSheaf R f` also equals the image ideal sheaf of `cotangentMap R f` twisted by
`(Ω_{X/R})∨` (`ramificationIdealSheaf_eq_imageIdealSheaf_twistedToUnit`).

When `Ω_{X/R}` and `Ω_{Y/R}` are invertible and `cotangentMap R f` is a monomorphism on an
arbitrary scheme `X`, `ramificationIdealSheaf R f` is an effective Cartier divisor `R_f`
(`isEffectiveCartier_ramificationIdealSheaf`) satisfying the Picard-group Riemann–Hurwitz identity
`[Ω_{X/R}] = f^* [Ω_{Y/R}] · [𝒪_X(-R_f)]⁻¹`
(`mk_relativeDifferentials_eq_pullback_mul_inv_ramification`). On an integral scheme `X`,
`cotangentMap R f ≠ 0` suffices for `Mono (cotangentMap R f)` (`mono_cotangentMap_of_ne_zero`),
and non-vanishing holds automatically for any dominant morphism of integral schemes whose
function-field extension is formally smooth and whose target has nontrivial rational differentials
(`cotangentMap_ne_zero_of_isDominant_of_formallySmooth`, specializing to separable extensions when
`Ω_{Y/R}` is invertible in `cotangentMap_ne_zero_of_isDominant_of_isSeparable`).

The Euler-characteristic degree specialization for proper integral curves over a field lives in
`TauCeti.AlgebraicGeometry.Curves.Degree.RiemannHurwitz`.

## References

* [The Stacks Project, Tag 02K4](https://stacks.math.columbia.edu/tag/02K4)
* [The Stacks Project, Tag 0C1B](https://stacks.math.columbia.edu/tag/0C1B)
* [The Stacks Project, Tag 0C3C](https://stacks.math.columbia.edu/tag/0C3C) (Fitting ideals of
  finite-type quasi-coherent modules)
* R. Hartshorne, *Algebraic Geometry*, Proposition IV.2.1 and Theorem IV.2.3
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory Opposite AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry

universe u

/-! ### Cokernel of the cotangent map -/

section CotangentCokernel

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

section BaseChange

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
  {X Y X' Y' : Scheme.{u}} [X.Over (Spec (.of R))] [Y.Over (Spec (.of R))]
  [X'.Over (Spec (.of S))] [Y'.Over (Spec (.of S))]
  {f : X ⟶ Y} [f.IsOver (Spec (.of R))] {f' : X' ⟶ Y'} [f'.IsOver (Spec (.of S))]
  {g_X : X' ⟶ X} {g_Y : Y' ⟶ Y}
  (H_X : IsPullback g_X (X' ↘ Spec (.of S)) (X ↘ Spec (.of R))
    (Spec.map (CommRingCat.ofHom (algebraMap R S))))
  (H_Y : IsPullback g_Y (Y' ↘ Spec (.of S)) (Y ↘ Spec (.of R))
    (Spec.map (CommRingCat.ofHom (algebraMap R S))))
  (w : g_X ≫ f = f' ≫ g_Y)

/-- Base change of `cokernel (cotangentMap R f)` along a ring map `R → S` for a commutative
diagram of pullbacks over `Spec S ⟶ Spec R`. -/
def cotangentCokernelBaseChangeIso :
    (Scheme.Modules.pullback g_X).obj (cokernel (cotangentMap R f)) ≅
      cokernel (cotangentMap S f') :=
  PreservesCokernel.iso (Scheme.Modules.pullback g_X) (cotangentMap R f) ≪≫
    cokernel.mapIso _ _ (cotangentSourceBaseChangeIso H_Y w)
      (relativeDifferentialsBaseChangeIso H_X)
      (cotangentSourceBaseChangeIso_hom_comp_cotangentMap H_X H_Y w).symm

/-- `cotangentCokernelBaseChangeIso` intertwines the pulled-back cokernel projection with
`relativeDifferentialsBaseChangeIso` followed by `cokernel.π (cotangentMap S f')`. -/
@[reassoc (attr := simp)]
theorem π_comp_cotangentCokernelBaseChangeIso_hom :
    (Scheme.Modules.pullback g_X).map (cokernel.π (cotangentMap R f)) ≫
        (cotangentCokernelBaseChangeIso H_X H_Y w).hom =
      (relativeDifferentialsBaseChangeIso H_X).hom ≫ cokernel.π (cotangentMap S f') := by
  dsimp [cotangentCokernelBaseChangeIso]
  rw [PreservesCokernel.π_iso_hom_assoc, cokernel.mapIso_hom, cokernel.π_desc]

/-- The inverse of `cotangentCokernelBaseChangeIso` intertwines `cokernel.π (cotangentMap S f')`
with `(relativeDifferentialsBaseChangeIso H_X).inv` followed by the pulled-back cokernel
projection. -/
@[reassoc (attr := simp)]
theorem π_comp_cotangentCokernelBaseChangeIso_inv :
    cokernel.π (cotangentMap S f') ≫ (cotangentCokernelBaseChangeIso H_X H_Y w).inv =
      (relativeDifferentialsBaseChangeIso H_X).inv ≫
        (Scheme.Modules.pullback g_X).map (cokernel.π (cotangentMap R f)) := by
  rw [Iso.comp_inv_eq, Category.assoc, π_comp_cotangentCokernelBaseChangeIso_hom,
    Iso.inv_hom_id_assoc]

end BaseChange

end CotangentCokernel

/-! ### The ramification ideal sheaf and base change -/

section RamificationIdealSheaf

section FixedBase

variable (R : Type u) [CommRing R] {X Y : Scheme.{u}}
  [X.Over (Spec (.of R))] [Y.Over (Spec (.of R))] (f : X ⟶ Y) [f.IsOver (Spec (.of R))]

/-- For a morphism `f : X ⟶ Y` over `Spec R` whose relative differential sheaf
`cokernel (cotangentMap R f)` is of finite type, the **ramification ideal sheaf**
`ramificationIdealSheaf R f` on `X` is the zeroth Fitting ideal sheaf of
`cokernel (cotangentMap R f)`. -/
def ramificationIdealSheaf [(cokernel (cotangentMap R f)).IsFiniteType] : X.IdealSheafData :=
  (cokernel (cotangentMap R f)).fittingIdeal
    (fun U ↦ Scheme.Modules.finite_sections_of_isAffineOpen _ U.val U.property) 0

/-- The ramification ideal sheaf equals the zeroth Fitting ideal sheaf of
`cokernel (cotangentMap R f)`. -/
theorem ramificationIdealSheaf_eq_fittingIdeal_cokernel
    [(cokernel (cotangentMap R f)).IsFiniteType] :
    ramificationIdealSheaf R f =
      (cokernel (cotangentMap R f)).fittingIdeal
        (fun U ↦ Scheme.Modules.finite_sections_of_isAffineOpen _ U.val U.property) 0 := by
  rfl

/-- When `Ω_{X/R}` and `Ω_{Y/R}` are invertible sheaves, `ramificationIdealSheaf R f` equals the
image ideal sheaf of `cotangentMap R f` twisted by `(Ω_{X/R})∨`. -/
theorem ramificationIdealSheaf_eq_imageIdealSheaf_twistedToUnit
    [SheafOfModules.isInvertible X (X.relativeDifferentials R)]
    [SheafOfModules.isInvertible Y (Y.relativeDifferentials R)] :
    ramificationIdealSheaf R f =
      Scheme.Modules.Hom.imageIdealSheaf
        (InvertibleSheaf.twistedToUnit
          ((InvertibleSheaf.pullback f).obj ⟨Y.relativeDifferentials R, inferInstance⟩)
          ⟨X.relativeDifferentials R, inferInstance⟩
          (cotangentMap R f)) := by
  let L₁ := (InvertibleSheaf.pullback f).obj ⟨Y.relativeDifferentials R, inferInstance⟩
  let L₂ : InvertibleSheaf X := ⟨X.relativeDifferentials R, inferInstance⟩
  rw [ramificationIdealSheaf_eq_fittingIdeal_cokernel R f,
    Scheme.Modules.Hom.imageIdealSheaf_eq_fittingIdeal_cokernel
      (InvertibleSheaf.twistedToUnit L₁ L₂ (cotangentMap R f))]
  exact ((Scheme.Modules.fittingIdeal_congr _
    (InvertibleSheaf.cokernelTwistedToUnitIso L₁ L₂ (cotangentMap R f)) 0).trans
    (Scheme.Modules.fittingIdeal_tensor_of_isInvertible (cokernel (cotangentMap R f))
      (InvertibleSheaf.dual L₂).obj 0)).symm

/-- When `cokernel (cotangentMap R f)` is of finite type, over compatible affine opens `V` of `Y`
and `U ≤ f⁻¹ V` of `X`, the ideal of `ramificationIdealSheaf R f` on `U` is the zeroth Fitting
ideal `Fitt₀(Ω[Γ(X, U)⁄Γ(Y, V)])`. -/
theorem ramificationIdealSheaf_ideal_eq_fittingIdeal_kaehlerDifferential
    [(cokernel (cotangentMap R f)).IsFiniteType]
    (V : Y.affineOpens) (U : X.affineOpens) (hUV : U.val ≤ f ⁻¹ᵁ V.val) :
    letI : Algebra Γ(Y, V) Γ(X, U) := (f.appLE V.val U.val hUV).hom.toAlgebra
    haveI : Module.Finite Γ(X, U) Ω[Γ(X, U)⁄Γ(Y, V)] :=
      letI := Scheme.Modules.finite_sections_of_isAffineOpen (cokernel
          (cotangentMap R f)) U.val U.property
      Module.Finite.equiv (cotangentCokernelSectionsEquiv R f V U hUV).symm
    (ramificationIdealSheaf R f).ideal U =
      TauCeti.fittingIdeal Γ(X, U) Ω[Γ(X, U)⁄Γ(Y, V)] 0 := by
  let : Algebra Γ(Y, V) Γ(X, U) := (f.appLE V.val U.val hUV).hom.toAlgebra
  have := Scheme.Modules.finite_sections_of_isAffineOpen (cokernel
      (cotangentMap R f)) U.val U.property
  have : Module.Finite Γ(X, U) Ω[Γ(X, U)⁄Γ(Y, V)] :=
    Module.Finite.equiv (cotangentCokernelSectionsEquiv R f V U hUV).symm
  rw [ramificationIdealSheaf_eq_fittingIdeal_cokernel R f, Scheme.Modules.fittingIdeal_ideal]
  exact (TauCeti.fittingIdeal_congr (cotangentCokernelSectionsEquiv R f V U hUV) 0).symm

end FixedBase

/-- **Base-change invariance of the ramification ideal sheaf.** Under any ring map `R → S`, when
`cokernel (cotangentMap R f)` is of finite type, pulling back `ramificationIdealSheaf R f` along
`g_X : X' ⟶ X` gives `ramificationIdealSheaf S f'`. -/
theorem comap_ramificationIdealSheaf {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    {X Y X' Y' : Scheme.{u}} [X.Over (Spec (.of R))] [Y.Over (Spec (.of R))]
    [X'.Over (Spec (.of S))] [Y'.Over (Spec (.of S))]
    {f : X ⟶ Y} [f.IsOver (Spec (.of R))] {f' : X' ⟶ Y'} [f'.IsOver (Spec (.of S))]
    {g_X : X' ⟶ X} {g_Y : Y' ⟶ Y}
    [(cokernel (cotangentMap R f)).IsFiniteType]
    (H_X : IsPullback g_X (X' ↘ Spec (.of S)) (X ↘ Spec (.of R))
      (Spec.map (CommRingCat.ofHom (algebraMap R S))))
    (H_Y : IsPullback g_Y (Y' ↘ Spec (.of S)) (Y ↘ Spec (.of R))
      (Spec.map (CommRingCat.ofHom (algebraMap R S))))
    (w : g_X ≫ f = f' ≫ g_Y) :
    haveI : (cokernel (cotangentMap S f')).IsFiniteType :=
      SheafOfModules.IsFiniteType.of_iso (R := X'.ringCatSheaf)
        (cotangentCokernelBaseChangeIso H_X H_Y w)
    (ramificationIdealSheaf R f).comap g_X = ramificationIdealSheaf S f' := by
  have : (cokernel (cotangentMap S f')).IsFiniteType :=
    SheafOfModules.IsFiniteType.of_iso (R := X'.ringCatSheaf)
      (cotangentCokernelBaseChangeIso H_X H_Y w)
  rw [ramificationIdealSheaf_eq_fittingIdeal_cokernel R f,
    ramificationIdealSheaf_eq_fittingIdeal_cokernel S f',
    ← Scheme.Modules.fittingIdeal_pullback g_X (cokernel (cotangentMap R f)) 0]
  exact Scheme.Modules.fittingIdeal_congr _ (cotangentCokernelBaseChangeIso H_X H_Y w) 0

end RamificationIdealSheaf

/-! ### Generic non-vanishing, Cartier property, and Riemann–Hurwitz formulas -/

section RiemannHurwitz

section GenericNonvanishing

variable (R : Type u) [CommRing R] {X Y : Scheme.{u}}
  [X.Over (Spec (.of R))] [Y.Over (Spec (.of R))]
  (f : X ⟶ Y) [f.IsOver (Spec (.of R))]

/-- For a dominant morphism `f : X ⟶ Y` of integral schemes over `Spec R` whose target has
nontrivial rational differentials `Ω[Y.functionField⁄R]`, if `X.functionField` is formally smooth
over `Y.functionField` along `f.functionFieldMap`, then `cotangentMap R f ≠ 0`. -/
theorem cotangentMap_ne_zero_of_isDominant_of_formallySmooth [IsIntegral X] [IsIntegral Y]
    [IsDominant f] [Nontrivial Ω[Y.functionField⁄R]]
    (hsm : letI : Algebra Y.functionField X.functionField := f.functionFieldMap.hom.toAlgebra
      Algebra.FormallySmooth Y.functionField X.functionField) :
    cotangentMap R f ≠ 0 := by
  let : Algebra Y.functionField X.functionField := f.functionFieldMap.hom.toAlgebra
  have : IsScalarTower R Y.functionField X.functionField :=
    .of_algebraMap_eq fun r ↦ (f.functionFieldMap_algebraMap R r).symm
  have : Algebra.FormallySmooth Y.functionField X.functionField := hsm
  have hne : ∃ z : Y.functionField, KaehlerDifferential.D R Y.functionField z ≠ 0 := by
    by_contra! hall
    exact (top_ne_bot (α := Submodule Y.functionField Ω[Y.functionField⁄R])) <| by
      rw [← KaehlerDifferential.span_range_derivation R Y.functionField, Submodule.span_eq_bot]
      rintro _ ⟨z, rfl⟩
      exact hall z
  obtain ⟨z, hz⟩ := hne
  obtain ⟨V, hV, b, rfl⟩ := Y.presheaf.exists_germ_eq z
  let _ : Nonempty V := ⟨⟨genericPoint Y, hV⟩⟩
  let _ : Nonempty (f ⁻¹ᵁ V) := f.nonempty_preimage_of_isDominant V
  intro hzero
  have hd : (X.universalDerivation R).d (X := op (f ⁻¹ᵁ V)) (f.app V b) = 0 := by
    have h0 : (cotangentMap R f).app (f ⁻¹ᵁ V) = 0 := by
      rw [hzero, Scheme.Modules.Hom.zero_app]
    exact (cotangentMap_app_pullbackSections_d R f V b).symm.trans <|
      (congr($h0 _)).trans <|
        (congrArg (fun f : _ →+ _ ↦ f _) AddCommGrpCat.hom_zero).trans (AddMonoidHom.zero_apply _)
  have hrat : rationalDifferential R (f ⁻¹ᵁ V)
      ((X.universalDerivation R).d (X := op (f ⁻¹ᵁ V)) (f.app V b)) = 0 :=
    (congrArg (rationalDifferential R (f ⁻¹ᵁ V)) hd).trans (map_zero _)
  have hgf : X.germToFunctionField (f ⁻¹ᵁ V) (f.app V b) =
      algebraMap Y.functionField X.functionField (Y.germToFunctionField V b) :=
    congr($(f.germToFunctionField_functionFieldMap V) b).symm
  rw [rationalDifferential_d, hgf,
    ← KaehlerDifferential.map_D R R Y.functionField X.functionField] at hrat
  exact hz ((map_eq_zero_iff _
    (TauCeti.injective_kaehlerDifferential_map_of_subsingleton_h1Cotangent
      R Y.functionField X.functionField)).mp hrat)

/-- For a dominant morphism `f : X ⟶ Y` of integral schemes over `Spec R` with invertible `Ω_{Y/R}`,
if `X.functionField` is separable over `Y.functionField` along `f.functionFieldMap`, then
`cotangentMap R f ≠ 0`. -/
theorem cotangentMap_ne_zero_of_isDominant_of_isSeparable [IsIntegral X] [IsIntegral Y]
    [IsDominant f] [SheafOfModules.isInvertible Y (Y.relativeDifferentials R)]
    (hsep : letI : Algebra Y.functionField X.functionField := f.functionFieldMap.hom.toAlgebra
      Algebra.IsSeparable Y.functionField X.functionField) :
    cotangentMap R f ≠ 0 := by
  have hfin : 0 < Module.finrank Y.functionField Ω[Y.functionField⁄R] := by
    rw [finrank_kaehlerDifferential_functionField_of_isInvertible (X := Y) R]
    exact Nat.zero_lt_one
  have : Nontrivial Ω[Y.functionField⁄R] := Module.nontrivial_of_finrank_pos hfin
  exact cotangentMap_ne_zero_of_isDominant_of_formallySmooth R f (by
    let : Algebra Y.functionField X.functionField := f.functionFieldMap.hom.toAlgebra
    have : Algebra.IsSeparable Y.functionField X.functionField := hsep
    have : Algebra.FormallyEtale Y.functionField X.functionField := .of_isSeparable _ _
    infer_instance)

end GenericNonvanishing

section OverCommRing

variable (R : Type u) [CommRing R] {X Y : Scheme.{u}}
  [X.Over (Spec (.of R))] [Y.Over (Spec (.of R))]
  (f : X ⟶ Y) [f.IsOver (Spec (.of R))]
  [SheafOfModules.isInvertible X (X.relativeDifferentials R)]
  [SheafOfModules.isInvertible Y (Y.relativeDifferentials R)]

/-- When `Ω_{X/R}` and `Ω_{Y/R}` are invertible and `cotangentMap R f` is a monomorphism,
`ramificationIdealSheaf R f` is an effective Cartier divisor on `X`. -/
theorem isEffectiveCartier_ramificationIdealSheaf [Mono (cotangentMap R f)] :
    (ramificationIdealSheaf R f).IsEffectiveCartier := by
  let L₁ := (InvertibleSheaf.pullback f).obj ⟨Y.relativeDifferentials R, inferInstance⟩
  let L₂ : InvertibleSheaf X := ⟨X.relativeDifferentials R, inferInstance⟩
  let L := InvertibleSheaf.tensorProduct L₁ (InvertibleSheaf.dual L₂)
  have : Mono (InvertibleSheaf.twistedToUnit L₁ L₂ (cotangentMap R f)) :=
    (InvertibleSheaf.mono_twistedToUnit_iff L₁ L₂ (cotangentMap R f)).mpr ‹_›
  rw [ramificationIdealSheaf_eq_imageIdealSheaf_twistedToUnit R f]
  exact L.isEffectiveCartier_imageIdealSheaf
    (InvertibleSheaf.twistedToUnit L₁ L₂ (cotangentMap R f))

/-- **The Picard-group Riemann–Hurwitz relation** for `𝒪_X(-R_f)`: when `Ω_{X/R}` and `Ω_{Y/R}` are
invertible and `cotangentMap R f` is a monomorphism, the line-bundle class of the ramification
ideal sheaf is `f^* [Ω_{Y/R}] · [Ω_{X/R}]⁻¹`. -/
@[simp]
theorem mk_toInvertibleSheaf_ramificationIdealSheaf [Mono (cotangentMap R f)] :
    LineBundleClass.mk (isEffectiveCartier_ramificationIdealSheaf R f).toInvertibleSheaf =
      LineBundleClass.pullback f
        (LineBundleClass.mk ⟨Y.relativeDifferentials R, inferInstance⟩) *
        (LineBundleClass.mk ⟨X.relativeDifferentials R, inferInstance⟩)⁻¹ := by
  let L₁ := (InvertibleSheaf.pullback f).obj ⟨Y.relativeDifferentials R, inferInstance⟩
  let L₂ : InvertibleSheaf X := ⟨X.relativeDifferentials R, inferInstance⟩
  let L := InvertibleSheaf.tensorProduct L₁ (InvertibleSheaf.dual L₂)
  have : Mono (InvertibleSheaf.twistedToUnit L₁ L₂ (cotangentMap R f)) :=
    (InvertibleSheaf.mono_twistedToUnit_iff L₁ L₂ (cotangentMap R f)).mpr ‹_›
  suffices ∀ hI : (ramificationIdealSheaf R f).IsEffectiveCartier,
      LineBundleClass.mk hI.toInvertibleSheaf =
        LineBundleClass.pullback f
          (LineBundleClass.mk ⟨Y.relativeDifferentials R, inferInstance⟩) *
          (LineBundleClass.mk ⟨X.relativeDifferentials R, inferInstance⟩)⁻¹ from
    this (isEffectiveCartier_ramificationIdealSheaf R f)
  rw [ramificationIdealSheaf_eq_imageIdealSheaf_twistedToUnit R f]
  intro _
  exact (L.mk_toInvertibleSheaf_imageIdealSheaf
    (InvertibleSheaf.twistedToUnit L₁ L₂ (cotangentMap R f))).trans
    (by rw [LineBundleClass.mk_tensorProduct, ← LineBundleClass.inv_mk,
      ← LineBundleClass.pullback_mk])

/-- **The Picard-group Riemann–Hurwitz formula**: when `Ω_{X/R}` and `Ω_{Y/R}` are invertible and
`cotangentMap R f` is a monomorphism, `[Ω_{X/R}] = f^* [Ω_{Y/R}] · [𝒪_X(-R_f)]⁻¹`. -/
theorem mk_relativeDifferentials_eq_pullback_mul_inv_ramification [Mono (cotangentMap R f)] :
    LineBundleClass.mk ⟨X.relativeDifferentials R, inferInstance⟩ =
      LineBundleClass.pullback f
        (LineBundleClass.mk ⟨Y.relativeDifferentials R, inferInstance⟩) *
        (LineBundleClass.mk
          (isEffectiveCartier_ramificationIdealSheaf R f).toInvertibleSheaf)⁻¹ := by
  rw [mk_toInvertibleSheaf_ramificationIdealSheaf R f, mul_inv_rev, inv_inv,
    mul_comm _ (LineBundleClass.pullback f _)⁻¹, mul_inv_cancel_left]

/-- On an integral scheme `X` with invertible `Ω_{X/R}` and `Ω_{Y/R}`, a nonzero cotangent map
`cotangentMap R f ≠ 0` is automatically a monomorphism. -/
theorem mono_cotangentMap_of_ne_zero [IsIntegral X] (hf : cotangentMap R f ≠ 0) :
    Mono (cotangentMap R f) := by
  let L₁ := (InvertibleSheaf.pullback f).obj ⟨Y.relativeDifferentials R, inferInstance⟩
  let L₂ : InvertibleSheaf X := ⟨X.relativeDifferentials R, inferInstance⟩
  let L := InvertibleSheaf.tensorProduct L₁ (InvertibleSheaf.dual L₂)
  have hne : InvertibleSheaf.twistedToUnit L₁ L₂ (cotangentMap R f) ≠ 0 :=
    mt (InvertibleSheaf.twistedToUnit_eq_zero_iff L₁ L₂ (cotangentMap R f)).mp hf
  have := L.mono_of_ne_zero_to_unit _ hne
  exact (InvertibleSheaf.mono_twistedToUnit_iff L₁ L₂ (cotangentMap R f)).mp this

/-- For a dominant morphism of integral schemes over `Spec R` with separable function-field
extension and invertible relative differential sheaves `Ω_{X/R}` and `Ω_{Y/R}`,
`ramificationIdealSheaf R f` is effective Cartier. -/
theorem isEffectiveCartier_ramificationIdealSheaf_of_isSeparable [IsIntegral X] [IsIntegral Y]
    [IsDominant f]
    (hsep : letI : Algebra Y.functionField X.functionField := f.functionFieldMap.hom.toAlgebra
      Algebra.IsSeparable Y.functionField X.functionField) :
    (ramificationIdealSheaf R f).IsEffectiveCartier :=
  have := mono_cotangentMap_of_ne_zero R f
    (cotangentMap_ne_zero_of_isDominant_of_isSeparable R f hsep)
  isEffectiveCartier_ramificationIdealSheaf R f

end OverCommRing

end RiemannHurwitz

end TauCeti.AlgebraicGeometry

end
