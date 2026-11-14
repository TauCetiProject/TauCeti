/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Degree.EulerCharacteristic
public import TauCeti.AlgebraicGeometry.LineBundle.Functoriality
public import TauCeti.AlgebraicGeometry.Modules.Differentials.Pullback
public import TauCeti.AlgebraicGeometry.Modules.FittingIdeal.Basic
public import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.Cokernels
public import TauCeti.AlgebraicGeometry.Morphisms.Dominant
import Mathlib.CategoryTheory.Monoidal.Closed.Braided
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Etale.Kaehler
import TauCeti.AlgebraicGeometry.CartierDivisor.Effective.Degree
import TauCeti.AlgebraicGeometry.Curves.Degree.Pullback
import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.ZeroLocus
import TauCeti.AlgebraicGeometry.Modules.Differentials.Rational
import TauCeti.AlgebraicGeometry.Modules.FittingIdeal.Pullback
import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.Colimits
import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.FiniteType
import TauCeti.AlgebraicGeometry.Modules.Tensor.AffineSections
import TauCeti.RingTheory.Kaehler.FormallyEtale

/-!
# The ramification ideal sheaf and the Picard-group Riemann–Hurwitz relation

Let `f : X ⟶ Y` be a morphism of schemes over `Spec R`. The cotangent map
`cotangentMap R f : f^* Ω_{Y/R} ⟶ Ω_{X/R}` has quasi-coherent cokernel whose sections over
compatible affine opens `V ⊆ Y` and `U ⊆ f⁻¹(V)` are the relative Kähler differentials
`Ω[Γ(X, U)⁄Γ(Y, V)]` (`cotangentCokernelSectionsEquiv`), and whose formation commutes with
arbitrary base change `R → S` (`cotangentCokernelBaseChangeIso`).

When `Ω_{X/R}` and `Ω_{Y/R}` are invertible sheaves (for instance on smooth relative curves over
`Spec R`), twisting `cotangentMap R f` by `(Ω_{X/R})∨` produces an `𝒪_X`-linear functional
`f^* Ω_{Y/R} ⊗ (Ω_{X/R})∨ ⟶ 𝒪_X` whose image ideal sheaf is the **ramification ideal sheaf**
`ramificationIdealSheaf R f ⊆ 𝒪_X`. Because `Fitt₀(R ⧸ I) = I` and zeroth Fitting ideals are
unchanged by tensoring with an invertible sheaf, this image ideal sheaf equals
`Fitt₀(cokernel (cotangentMap R f))` (`ramificationIdealSheaf_eq_fittingIdeal_cokernel`), restricts
on compatible affine opens to `Fitt₀(Ω[Γ(X, U)⁄Γ(Y, V)])`
(`ramificationIdealSheaf_ideal_eq_fittingIdeal_kaehlerDifferential`), and commutes with arbitrary
base change `R → S` (`ramificationIdealSheaf_comap_eq`).

When `X` is integral and `cotangentMap R f ≠ 0` — which holds automatically whenever `X` and `Y`
are integral, `f` is dominant, and `X.functionField / Y.functionField` is separable
(`cotangentMap_ne_zero_of_isDominant_of_isSeparable`) — `ramificationIdealSheaf R f` is an
effective Cartier divisor `R_f` (`isEffectiveCartier_ramificationIdealSheaf`) satisfying the
Picard-group Riemann–Hurwitz identity `[Ω_{X/R}] = f^* [Ω_{Y/R}] · [𝒪_X(-R_f)]⁻¹`
(`mk_relativeDifferentials_eq_pullback_mul_inv_ramification`). On proper integral curves over a
field `k`, this yields the Euler-characteristic degree formulas
`deg Ω_{X/k} = deg (f^* Ω_{Y/k}) + dim_k Γ(R_f, 𝒪_{R_f})`
(`eulerDegree_relativeDifferentials_eq_add_ramification_finrank`) and, for finite flat dominant
morphisms, `deg Ω_{X/k} = [K(X) : f^* K(Y)] · deg Ω_{Y/k} + dim_k Γ(R_f, 𝒪_{R_f})`
(`eulerDegree_relativeDifferentials_eq_finrank_mul_add_ramification`).

## References

* [The Stacks Project, Tag 02K4](https://stacks.math.columbia.edu/tag/02K4)
* [The Stacks Project, Tag 0C1B](https://stacks.math.columbia.edu/tag/0C1B)
* R. Hartshorne, *Algebraic Geometry*, Proposition IV.2.1 and Theorem IV.2.3
* H. Stichtenoth, *Algebraic Function Fields and Codes*, §3.4
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory Opposite AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry

universe u

/-! ### Cokernel of the cotangent map -/

section CotangentCokernel

private def cokernelSectionsEquiv {X : Scheme.{u}} {M N : X.Modules}
    [M.IsQuasicoherent] [N.IsQuasicoherent] (φ : M ⟶ N) (U : X.affineOpens) :
    (((Scheme.Modules.sectionsFunctor U.1).obj N) ⧸
        LinearMap.range ((Scheme.Modules.sectionsFunctor U.1).map φ).hom) ≃ₗ[Γ(X, U)]
      Γ(cokernel φ, U.1) := by
  let F := Scheme.Modules.sectionsFunctor U.1
  letI : F.PreservesZeroMorphisms := ⟨fun _ _ ↦ rfl⟩
  have hc := isColimitMapCoconeSectionsFunctor (K := parallelPair φ 0)
    (by rintro (_ | _) <;> dsimp <;> infer_instance) (cokernelIsCokernel φ) U.2
  haveI : PreservesColimit (parallelPair φ 0) F :=
    preservesColimit_of_preserves_colimit_cocone (cokernelIsCokernel φ) hc
  exact (PreservesCokernel.iso F φ ≪≫
    ModuleCat.cokernelIsoRangeQuotient (F.map φ)).symm.toLinearEquiv

private theorem cokernelSectionsEquiv_mk {X : Scheme.{u}} {M N : X.Modules}
    [M.IsQuasicoherent] [N.IsQuasicoherent] (φ : M ⟶ N) (U : X.affineOpens) (s : Γ(N, U.1)) :
    cokernelSectionsEquiv φ U (Submodule.Quotient.mk s) = (cokernel.π φ).app U.1 s := by
  let F := Scheme.Modules.sectionsFunctor U.1
  let : F.PreservesZeroMorphisms := ⟨fun _ _ ↦ rfl⟩
  have hc := isColimitMapCoconeSectionsFunctor (K := parallelPair φ 0)
    (by rintro (_ | _) <;> dsimp <;> infer_instance) (cokernelIsCokernel φ) U.2
  let : PreservesColimit (parallelPair φ 0) F :=
    preservesColimit_of_preserves_colimit_cocone (cokernelIsCokernel φ) hc
  let e := PreservesCokernel.iso F φ ≪≫ ModuleCat.cokernelIsoRangeQuotient (F.map φ)
  have hπ : ModuleCat.ofHom (LinearMap.range (F.map φ).hom).mkQ ≫ e.inv = F.map (cokernel.π φ) := by
    rw [Iso.comp_inv_eq]
    exact ((PreservesCokernel.π_iso_hom_assoc F φ _).trans
      (ModuleCat.cokernel_π_cokernelIsoRangeQuotient_hom (F.map φ))).symm
  exact congrArg (fun ψ : F.obj N ⟶ F.obj (cokernel φ) ↦ ψ s) hπ

/-- Over compatible affine opens `V` of `Y` and `U ≤ f⁻¹ V` of `X`, the sections of
`cokernel (cotangentMap R f)` over `U` identify with the relative Kähler differentials
`Ω[Γ(X, U)⁄Γ(Y, V)]`. -/
def cotangentCokernelSectionsEquiv (R : Type u) [CommRing R] {X Y : Scheme.{u}}
    [X.Over (Spec (.of R))] [Y.Over (Spec (.of R))] (f : X ⟶ Y) [f.IsOver (Spec (.of R))]
    (V : Y.affineOpens) (U : X.affineOpens) (hUV : U.1 ≤ f ⁻¹ᵁ V.1) :
    letI : Algebra Γ(Y, V) Γ(X, U) := (f.appLE V.1 U.1 hUV).hom.toAlgebra
    Ω[Γ(X, U)⁄Γ(Y, V)] ≃ₗ[Γ(X, U)] Γ(cokernel (cotangentMap R f), U.1) := by
  letI : Algebra R Γ(Y, V) := ((Y.baseRingToStructurePresheaf R).app (op V.1)).hom.toAlgebra
  letI : Algebra R Γ(X, U) := ((X.baseRingToStructurePresheaf R).app (op U.1)).hom.toAlgebra
  letI : Algebra Γ(Y, V) Γ(X, U) := (f.appLE V.1 U.1 hUV).hom.toAlgebra
  haveI : IsScalarTower R Γ(Y, V) Γ(X, U) := isScalarTower_baseRing_appLE R f V.1 U.1 hUV
  let F := Scheme.Modules.sectionsFunctor U.1
  let eSrc := pullbackRelativeDifferentialsSectionsEquiv R f V U hUV
  let eTgt : Ω[Γ(X, U)⁄R] ≃ₗ[Γ(X, U)] F.obj (X.relativeDifferentials R) :=
    { toFun x := relativeDifferentialsSectionsEquiv R X U x
      invFun y := (relativeDifferentialsSectionsEquiv R X U).symm y
      map_add' := map_add _
      map_smul' := map_smul _
      left_inv := (relativeDifferentialsSectionsEquiv R X U).left_inv
      right_inv := (relativeDifferentialsSectionsEquiv R X U).right_inv }
  have hker : Submodule.map eTgt.toLinearMap
      (LinearMap.ker (KaehlerDifferential.map R Γ(Y, V) Γ(X, U) Γ(X, U))) =
      LinearMap.range (F.map (cotangentMap R f)).hom := by
    rw [← KaehlerDifferential.range_mapBaseChange R Γ(Y, V) Γ(X, U)]
    ext s
    constructor
    · rintro ⟨_, ⟨η, rfl⟩, rfl⟩
      refine ⟨eSrc η, ?_⟩
      have h := cotangentMap_app_pullbackRelativeDifferentialsSectionsEquiv R f V U hUV η
      exact (eTgt.apply_symm_apply _).symm.trans (congrArg eTgt h)
    · rintro ⟨t, rfl⟩
      refine ⟨eTgt.symm ((cotangentMap R f).app U.1 t), ⟨eSrc.symm t, ?_⟩, eTgt.apply_symm_apply _⟩
      exact (cotangentMap_app_pullbackRelativeDifferentialsSectionsEquiv R f V U hUV
        (eSrc.symm t)).symm.trans
        (congrArg (fun x ↦ eTgt.symm ((cotangentMap R f).app U.1 x)) (eSrc.apply_symm_apply t))
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
    (V : Y.affineOpens) (U : X.affineOpens) (hUV : U.1 ≤ f ⁻¹ᵁ V.1) (a : Γ(X, U)) :
    letI : Algebra Γ(Y, V) Γ(X, U) := (f.appLE V.1 U.1 hUV).hom.toAlgebra
    cotangentCokernelSectionsEquiv R f V U hUV (KaehlerDifferential.D Γ(Y, V) Γ(X, U) a) =
      (cokernel.π (cotangentMap R f)).app U.1 ((X.universalDerivation R).d (X := op U.1) a) := by
  let : Algebra R Γ(Y, V) := ((Y.baseRingToStructurePresheaf R).app (op V.1)).hom.toAlgebra
  let : Algebra R Γ(X, U) := ((X.baseRingToStructurePresheaf R).app (op U.1)).hom.toAlgebra
  let : Algebra Γ(Y, V) Γ(X, U) := (f.appLE V.1 U.1 hUV).hom.toAlgebra
  have : IsScalarTower R Γ(Y, V) Γ(X, U) := isScalarTower_baseRing_appLE R f V.1 U.1 hUV
  have hmk : (LinearMap.quotKerEquivOfSurjective
      (KaehlerDifferential.map R Γ(Y, V) Γ(X, U) Γ(X, U))
      (KaehlerDifferential.map_surjective R Γ(Y, V) Γ(X, U))).symm
        (KaehlerDifferential.D Γ(Y, V) Γ(X, U) a) =
      Submodule.Quotient.mk (KaehlerDifferential.D R Γ(X, U) a) :=
    LinearEquiv.symm_apply_eq _ |>.mpr (KaehlerDifferential.map_D R Γ(Y, V) Γ(X, U) Γ(X, U) a).symm
  dsimp only [cotangentCokernelSectionsEquiv, LinearEquiv.trans_apply]
  rw [hmk, Submodule.Quotient.equiv_apply, Submodule.mapQ_apply]
  exact (cokernelSectionsEquiv_mk (cotangentMap R f) U _).trans
    (congrArg ((cokernel.π (cotangentMap R f)).app U.1)
      (relativeDifferentialsSectionsEquiv_D R X U a))

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
@[simp, reassoc]
theorem π_comp_cotangentCokernelBaseChangeIso_hom :
    (Scheme.Modules.pullback g_X).map (cokernel.π (cotangentMap R f)) ≫
        (cotangentCokernelBaseChangeIso H_X H_Y w).hom =
      (relativeDifferentialsBaseChangeIso H_X).hom ≫ cokernel.π (cotangentMap S f') := by
  dsimp [cotangentCokernelBaseChangeIso]
  rw [PreservesCokernel.π_iso_hom_assoc, cokernel.mapIso_hom, cokernel.π_desc]

end BaseChange

end CotangentCokernel

/-! ### Internal Fitting-ideal and line-bundle helpers -/

section Helpers

variable {X : Scheme.{u}}

private theorem isFiniteType_of_isInvertible (K : InvertibleSheaf X) : K.obj.IsFiniteType :=
  have : TauCeti.SheafOfModules.IsInvertible (R := X.ringCatSheaf) K.obj := K.property
  let F : _root_.SheafOfModules X.ringCatSheaf := K.obj
  inferInstanceAs F.IsFiniteType

private theorem isFiniteType_tensorObj (M N : X.Modules) [M.IsQuasicoherent] [N.IsQuasicoherent]
    [M.IsFiniteType] [N.IsFiniteType] : (M ⊗ N).IsFiniteType := by
  refine Scheme.Modules.isFiniteType_of_finite_sections (M ⊗ N) fun U hU ↦ ?_
  have := M.finite_sections_of_isAffineOpen U hU
  have := N.finite_sections_of_isAffineOpen U hU
  have : Module.Finite Γ(X, U)
      ↑((Scheme.Modules.sectionsFunctor U).obj M ⊗ (Scheme.Modules.sectionsFunctor U).obj N) :=
    inferInstanceAs (Module.Finite Γ(X, U) (TensorProduct Γ(X, U) Γ(M, U) Γ(N, U)))
  exact Module.Finite.equiv (LinearEquiv.ofBijective
    (Functor.LaxMonoidal.μ (Scheme.Modules.sectionsFunctor U) M N).hom
    (Scheme.Modules.bijective_μ_sectionsFunctor M N hU))

private theorem imageIdealSheaf_eq_fittingIdeal_cokernel {M : X.Modules} [M.IsQuasicoherent]
    (φ : M ⟶ 𝟙_ X.Modules) :
    haveI : (cokernel φ).IsFiniteType := Scheme.Modules.isFiniteType_of_epi (cokernel.π φ)
    φ.imageIdealSheaf =
      (cokernel φ).fittingIdeal
        (fun U ↦ Scheme.Modules.finite_sections_of_isAffineOpen _ U.1 U.2) 0 := by
  have : (cokernel φ).IsFiniteType := Scheme.Modules.isFiniteType_of_epi (cokernel.π φ)
  apply Scheme.IdealSheafData.ext
  funext U
  have := (cokernel φ).finite_sections_of_isAffineOpen U.1 U.2
  let eUnit : Γ(X, U.1) ≃ₗ[Γ(X, U.1)] (Scheme.Modules.sectionsFunctor U.1).obj (𝟙_ X.Modules) :=
    { toFun x := x, invFun x := x, map_add' _ _ := rfl, map_smul' _ _ := rfl,
      left_inv _ := rfl, right_inv _ := rfl }
  have hI : Submodule.map eUnit.toLinearMap (φ.imageIdeal U.1) =
      LinearMap.range ((Scheme.Modules.sectionsFunctor U.1).map φ).hom := by
    ext s
    exact ⟨fun ⟨_, hx, rfl⟩ ↦ φ.mem_imageIdeal.mp hx,
      fun ⟨t, ht⟩ ↦ ⟨s, φ.mem_imageIdeal.mpr ⟨t, ht⟩, rfl⟩⟩
  let e : (Γ(X, U.1) ⧸ φ.imageIdeal U.1) ≃ₗ[Γ(X, U.1)] Γ(cokernel φ, U.1) :=
    (Submodule.Quotient.equiv _ _ eUnit hI).trans (cokernelSectionsEquiv φ U)
  rw [φ.imageIdealSheaf_ideal U, Scheme.Modules.fittingIdeal_ideal]
  exact (TauCeti.fittingIdeal_quotient_zero (φ.imageIdeal U.1)).symm.trans
    (TauCeti.fittingIdeal_congr e 0)

private theorem fittingIdeal_tensor_of_isInvertible (N : X.Modules) [N.IsQuasicoherent]
    [N.IsFiniteType] (K : InvertibleSheaf X) (k : ℕ) :
    haveI : K.obj.IsFiniteType := isFiniteType_of_isInvertible K
    haveI : (N ⊗ K.obj).IsFiniteType := isFiniteType_tensorObj N K.obj
    (N ⊗ K.obj).fittingIdeal
        (fun U ↦ Scheme.Modules.finite_sections_of_isAffineOpen _ U.1 U.2) k =
      N.fittingIdeal
        (fun U ↦ Scheme.Modules.finite_sections_of_isAffineOpen _ U.1 U.2) k := by
  have : K.obj.IsFiniteType := isFiniteType_of_isInvertible K
  have : (N ⊗ K.obj).IsFiniteType := isFiniteType_tensorObj N K.obj
  obtain ⟨ι, W, hW, htriv⟩ :=
    (SheafOfModules.isInvertible_iff_exists_isOpenCover (X := X) (M := K.obj)).mp K.property
  refine Scheme.IdealSheafData.ext_of_comap_openCover (X.openCoverOfIsOpenCover W hW) fun i ↦ ?_
  -- `(X.openCoverOfIsOpenCover W hW).f i` is `(W i).ι`, whereas `rw` fails implicit checking on
  -- `U.2 : U ∈ X.affineOpens` inside the finiteness witness of `fittingIdeal`.
  change ((N ⊗ K.obj).fittingIdeal _ k).comap (W i).ι = (N.fittingIdeal _ k).comap (W i).ι
  rw [← Scheme.Modules.fittingIdeal_pullback (W i).ι (N ⊗ K.obj) k,
    ← Scheme.Modules.fittingIdeal_pullback (W i).ι N k]
  let eK : (Scheme.Modules.pullback (W i).ι).obj K.obj ≅ 𝟙_ (W i : Scheme).Modules :=
    ((Scheme.Modules.restrictFunctorIsoPullback (W i).ι).app K.obj).symm ≪≫ (htriv i).some.symm
  let e : (Scheme.Modules.pullback (W i).ι).obj (N ⊗ K.obj) ≅
      (Scheme.Modules.pullback (W i).ι).obj N :=
    asIso (Functor.OplaxMonoidal.δ (Scheme.Modules.pullback (W i).ι) N K.obj) ≪≫
      whiskerLeftIso ((Scheme.Modules.pullback (W i).ι).obj N) eK ≪≫
      ρ_ ((Scheme.Modules.pullback (W i).ι).obj N)
  exact Scheme.Modules.fittingIdeal_congr _ e k

private def evaluationDualIso (L : InvertibleSheaf X) :
    L.obj ⊗ (InvertibleSheaf.dual L).obj ≅ 𝟙_ X.Modules :=
  eqToIso (congrArg (L.obj ⊗ ·) (InvertibleSheaf.dual_obj L)) ≪≫
    Scheme.Modules.isoOfSheafIso X (InvertibleSheaf.evaluationDualIsoSheaf L)

private def twistedToUnit (L₁ L₂ : InvertibleSheaf X) (φ : L₁.obj ⟶ L₂.obj) :
    (InvertibleSheaf.tensorProduct L₁ (InvertibleSheaf.dual L₂)).obj ⟶ 𝟙_ X.Modules :=
  (InvertibleSheaf.tensorProductObjIso L₁ (InvertibleSheaf.dual L₂)).hom ≫
    whiskerRight φ (InvertibleSheaf.dual L₂).obj ≫
    (evaluationDualIso L₂).hom

private theorem twistedToUnit_eq_zero_iff (L₁ L₂ : InvertibleSheaf X) (φ : L₁.obj ⟶ L₂.obj) :
    twistedToUnit L₁ L₂ φ = 0 ↔ φ = 0 := by
  let : MonoidalPreadditive X.Modules := TauCeti.SheafOfModules.monoidalPreadditive X.sheaf
  constructor
  · intro h
    dsimp only [twistedToUnit] at h
    rw [Limits.comp_eq_zero_iff_of_epi
      (InvertibleSheaf.tensorProductObjIso L₁ (InvertibleSheaf.dual L₂)).hom,
      Limits.comp_eq_zero_iff_of_mono (evaluationDualIso L₂).hom] at h
    have hYZ : φ ▷ ((InvertibleSheaf.dual L₂).obj ⊗ L₂.obj) = 0 := by
      have hassoc :=
        MonoidalCategory.associator_naturality_left φ (InvertibleSheaf.dual L₂).obj L₂.obj
      rw [h, MonoidalPreadditive.zero_whiskerRight, zero_comp] at hassoc
      exact (Limits.comp_eq_zero_iff_of_epi
        (α_ L₁.obj (InvertibleSheaf.dual L₂).obj L₂.obj).hom).mp hassoc.symm
    let evSymm : (InvertibleSheaf.dual L₂).obj ⊗ L₂.obj ≅ 𝟙_ X.Modules :=
      β_ (InvertibleSheaf.dual L₂).obj L₂.obj ≪≫ evaluationDualIso L₂
    have hφ1 : φ ▷ 𝟙_ X.Modules = 0 := by
      have hex := MonoidalCategory.whisker_exchange φ evSymm.hom
      rw [hYZ, zero_comp] at hex
      exact (Limits.comp_eq_zero_iff_of_epi (L₁.obj ◁ evSymm.hom)).mp hex
    have hru := MonoidalCategory.rightUnitor_naturality φ
    rw [hφ1, zero_comp] at hru
    exact (Limits.comp_eq_zero_iff_of_epi (ρ_ L₁.obj).hom).mp hru.symm
  · rintro rfl
    simp [twistedToUnit]

private def cokernelTwistedToUnitIso (L₁ L₂ : InvertibleSheaf X) (φ : L₁.obj ⟶ L₂.obj) :
    cokernel (twistedToUnit L₁ L₂ φ) ≅ cokernel φ ⊗ (InvertibleSheaf.dual L₂).obj :=
  (cokernel.mapIso (twistedToUnit L₁ L₂ φ) ((tensorRight (InvertibleSheaf.dual L₂).obj).map φ)
      (InvertibleSheaf.tensorProductObjIso L₁ (InvertibleSheaf.dual L₂))
      (evaluationDualIso L₂).symm (by
        dsimp [twistedToUnit]
        simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id])) ≪≫
    (PreservesCokernel.iso (tensorRight (InvertibleSheaf.dual L₂).obj) φ).symm

end Helpers

/-! ### The ramification ideal sheaf and base change -/

section RamificationIdealSheaf

section FixedBase

variable (R : Type u) [CommRing R] {X Y : Scheme.{u}}
  [X.Over (Spec (.of R))] [Y.Over (Spec (.of R))] (f : X ⟶ Y) [f.IsOver (Spec (.of R))]
  [SheafOfModules.isInvertible X (X.relativeDifferentials R)]
  [SheafOfModules.isInvertible Y (Y.relativeDifferentials R)]

/-- For a morphism `f : X ⟶ Y` over `Spec R` with invertible relative differential sheaves
`Ω_{X/R}` and `Ω_{Y/R}`, the **ramification ideal sheaf** `ramificationIdealSheaf R f` on `X` is
the image ideal sheaf of `cotangentMap R f` twisted by `(Ω_{X/R})∨`. -/
def ramificationIdealSheaf : X.IdealSheafData :=
  (twistedToUnit
    ((InvertibleSheaf.pullback f).obj ⟨Y.relativeDifferentials R, inferInstance⟩)
    ⟨X.relativeDifferentials R, inferInstance⟩
    (cotangentMap R f)).imageIdealSheaf

omit [SheafOfModules.isInvertible Y (Y.relativeDifferentials R)] in
/-- When `Ω_{X/R}` is invertible, the sections of `cokernel (cotangentMap R f)` over any affine
open `U` of `X` form a finite `Γ(X, U)`-module. -/
theorem finite_sections_cokernel_cotangentMap (U : X.affineOpens) :
    Module.Finite Γ(X, U) Γ(cokernel (cotangentMap R f), U) := by
  have : (X.relativeDifferentials R).IsFiniteType :=
    isFiniteType_of_isInvertible ⟨X.relativeDifferentials R, inferInstance⟩
  have : (cokernel (cotangentMap R f)).IsFiniteType :=
    Scheme.Modules.isFiniteType_of_epi (cokernel.π (cotangentMap R f))
  exact (cokernel (cotangentMap R f)).finite_sections_of_isAffineOpen U.1 U.2

/-- The ramification ideal sheaf equals the zeroth Fitting ideal sheaf of
`cokernel (cotangentMap R f)`. -/
theorem ramificationIdealSheaf_eq_fittingIdeal_cokernel :
    ramificationIdealSheaf R f =
      (cokernel (cotangentMap R f)).fittingIdeal
        (finite_sections_cokernel_cotangentMap R f) 0 := by
  let L₁ := (InvertibleSheaf.pullback f).obj ⟨Y.relativeDifferentials R, inferInstance⟩
  let L₂ : InvertibleSheaf X := ⟨X.relativeDifferentials R, inferInstance⟩
  have : (X.relativeDifferentials R).IsFiniteType := isFiniteType_of_isInvertible L₂
  have : (cokernel (cotangentMap R f)).IsFiniteType :=
    Scheme.Modules.isFiniteType_of_epi (cokernel.π (cotangentMap R f))
  have : (InvertibleSheaf.dual L₂).obj.IsFiniteType :=
    isFiniteType_of_isInvertible (InvertibleSheaf.dual L₂)
  have : (cokernel (cotangentMap R f) ⊗ (InvertibleSheaf.dual L₂).obj).IsFiniteType :=
    isFiniteType_tensorObj (cokernel (cotangentMap R f)) (InvertibleSheaf.dual L₂).obj
  dsimp only [ramificationIdealSheaf]
  rw [imageIdealSheaf_eq_fittingIdeal_cokernel (twistedToUnit L₁ L₂ (cotangentMap R f))]
  exact (Scheme.Modules.fittingIdeal_congr _ (cokernelTwistedToUnitIso L₁ L₂ (cotangentMap R f))
    0).trans (fittingIdeal_tensor_of_isInvertible (cokernel (cotangentMap R f))
      (InvertibleSheaf.dual L₂) 0)

/-- Over compatible affine opens `V` of `Y` and `U ≤ f⁻¹ V` of `X`, the ideal of
`ramificationIdealSheaf R f` on `U` is the zeroth Fitting ideal `Fitt₀(Ω[Γ(X, U)⁄Γ(Y, V)])`. -/
theorem ramificationIdealSheaf_ideal_eq_fittingIdeal_kaehlerDifferential
    (V : Y.affineOpens) (U : X.affineOpens) (hUV : U.1 ≤ f ⁻¹ᵁ V.1) :
    letI : Algebra Γ(Y, V) Γ(X, U) := (f.appLE V.1 U.1 hUV).hom.toAlgebra
    haveI : Module.Finite Γ(X, U) Ω[Γ(X, U)⁄Γ(Y, V)] :=
      have := finite_sections_cokernel_cotangentMap R f U
      Module.Finite.equiv (cotangentCokernelSectionsEquiv R f V U hUV).symm
    (ramificationIdealSheaf R f).ideal U =
      TauCeti.fittingIdeal Γ(X, U) Ω[Γ(X, U)⁄Γ(Y, V)] 0 := by
  have := finite_sections_cokernel_cotangentMap R f U
  let : Algebra Γ(Y, V) Γ(X, U) := (f.appLE V.1 U.1 hUV).hom.toAlgebra
  have : Module.Finite Γ(X, U) Ω[Γ(X, U)⁄Γ(Y, V)] :=
    Module.Finite.equiv (cotangentCokernelSectionsEquiv R f V U hUV).symm
  rw [ramificationIdealSheaf_eq_fittingIdeal_cokernel R f, Scheme.Modules.fittingIdeal_ideal]
  exact (TauCeti.fittingIdeal_congr (cotangentCokernelSectionsEquiv R f V U hUV) 0).symm

end FixedBase

/-- **Base-change invariance of the ramification ideal sheaf.** Under any ring map `R → S`,
pulling back `ramificationIdealSheaf R f` along `g_X : X' ⟶ X` gives
`ramificationIdealSheaf S f'`. -/
theorem ramificationIdealSheaf_comap_eq {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    {X Y X' Y' : Scheme.{u}} [X.Over (Spec (.of R))] [Y.Over (Spec (.of R))]
    [X'.Over (Spec (.of S))] [Y'.Over (Spec (.of S))]
    {f : X ⟶ Y} [f.IsOver (Spec (.of R))] {f' : X' ⟶ Y'} [f'.IsOver (Spec (.of S))]
    {g_X : X' ⟶ X} {g_Y : Y' ⟶ Y}
    [SheafOfModules.isInvertible X (X.relativeDifferentials R)]
    [SheafOfModules.isInvertible Y (Y.relativeDifferentials R)]
    [SheafOfModules.isInvertible X' (X'.relativeDifferentials S)]
    [SheafOfModules.isInvertible Y' (Y'.relativeDifferentials S)]
    (H_X : IsPullback g_X (X' ↘ Spec (.of S)) (X ↘ Spec (.of R))
      (Spec.map (CommRingCat.ofHom (algebraMap R S))))
    (H_Y : IsPullback g_Y (Y' ↘ Spec (.of S)) (Y ↘ Spec (.of R))
      (Spec.map (CommRingCat.ofHom (algebraMap R S))))
    (w : g_X ≫ f = f' ≫ g_Y) :
    (ramificationIdealSheaf R f).comap g_X = ramificationIdealSheaf S f' := by
  have : (X.relativeDifferentials R).IsFiniteType :=
    isFiniteType_of_isInvertible ⟨X.relativeDifferentials R, inferInstance⟩
  have : (cokernel (cotangentMap R f)).IsFiniteType :=
    Scheme.Modules.isFiniteType_of_epi (cokernel.π (cotangentMap R f))
  rw [ramificationIdealSheaf_eq_fittingIdeal_cokernel R f,
    ramificationIdealSheaf_eq_fittingIdeal_cokernel S f',
    ← Scheme.Modules.fittingIdeal_pullback g_X (cokernel (cotangentMap R f)) 0]
  exact Scheme.Modules.fittingIdeal_congr _ (cotangentCokernelBaseChangeIso H_X H_Y w) 0

end RamificationIdealSheaf

/-! ### Separable dominant morphisms, Cartier property, and Riemann–Hurwitz formulas -/

section RiemannHurwitz

section OverCommRing

variable (R : Type u) [CommRing R] {X Y : Scheme.{u}}
  [X.Over (Spec (.of R))] [Y.Over (Spec (.of R))] [IsIntegral X]
  (f : X ⟶ Y) [f.IsOver (Spec (.of R))]
  [SheafOfModules.isInvertible X (X.relativeDifferentials R)]
  [SheafOfModules.isInvertible Y (Y.relativeDifferentials R)]

omit [SheafOfModules.isInvertible X (X.relativeDifferentials R)] in
/-- For a dominant morphism `f : X ⟶ Y` of integral schemes over `Spec R` with invertible `Ω_{Y/R}`,
if `X.functionField` is separable over `Y.functionField` along `f.functionFieldMap`, then
`cotangentMap R f ≠ 0`. -/
theorem cotangentMap_ne_zero_of_isDominant_of_isSeparable [IsIntegral Y] [IsDominant f]
    (hsep : letI : Algebra Y.functionField X.functionField := f.functionFieldMap.hom.toAlgebra
      Algebra.IsSeparable Y.functionField X.functionField) :
    cotangentMap R f ≠ 0 := by
  let : Algebra Y.functionField X.functionField := f.functionFieldMap.hom.toAlgebra
  have : IsScalarTower R Y.functionField X.functionField :=
    .of_algebraMap_eq fun r ↦ (f.functionFieldMap_algebraMap R r).symm
  have : Algebra.IsSeparable Y.functionField X.functionField := hsep
  have : Algebra.FormallyEtale Y.functionField X.functionField := .of_isSeparable _ _
  have hfin : 0 < Module.finrank Y.functionField Ω[Y.functionField⁄R] := by
    rw [finrank_kaehlerDifferential_functionField_of_isInvertible (X := Y) R]
    exact Nat.zero_lt_one
  have : Nontrivial Ω[Y.functionField⁄R] := Module.nontrivial_of_finrank_pos hfin
  have hne : ∃ z : Y.functionField, KaehlerDifferential.D R Y.functionField z ≠ 0 := by
    by_contra! hall
    obtain ⟨ω, hω⟩ := exists_ne (0 : Ω[Y.functionField⁄R])
    have htop : ω ∈ (⊤ : Submodule Y.functionField Ω[Y.functionField⁄R]) := trivial
    rw [← KaehlerDifferential.span_range_derivation R Y.functionField] at htop
    refine hω (Submodule.span_induction (fun _ ⟨z, hz⟩ ↦ hz ▸ hall z) rfl
      (fun _ _ _ _ hx hy ↦ by rw [hx, hy, add_zero])
      (fun c _ _ hx ↦ by rw [hx, smul_zero]) htop)
  obtain ⟨z, hz⟩ := hne
  obtain ⟨V, hV, b, rfl⟩ := Y.presheaf.exists_germ_eq z
  let _ : Nonempty V := ⟨⟨genericPoint Y, hV⟩⟩
  let _ : Nonempty (f ⁻¹ᵁ V) := f.nonempty_preimage_of_isDominant V
  intro hzero
  have hd : (X.universalDerivation R).d (X := op (f ⁻¹ᵁ V)) (f.app V b) = 0 := by
    rw [← cotangentMap_app_pullbackSections_d R f V b, hzero]
    rfl
  have hrat : rationalDifferential R (f ⁻¹ᵁ V)
      ((X.universalDerivation R).d (X := op (f ⁻¹ᵁ V)) (f.app V b)) = 0 := by
    rw [hd]
    exact map_zero _
  have hgf : X.germToFunctionField (f ⁻¹ᵁ V) (f.app V b) =
      algebraMap Y.functionField X.functionField (Y.germToFunctionField V b) :=
    congr($(f.germToFunctionField_functionFieldMap V) b).symm
  rw [rationalDifferential_d, hgf,
    ← KaehlerDifferential.map_D R R Y.functionField X.functionField] at hrat
  let bY := Module.Basis.ofVectorSpace Y.functionField Ω[Y.functionField⁄R]
  refine hz (bY.repr.injective ?_)
  rw [map_zero]
  ext i
  refine RingHom.injective (algebraMap Y.functionField X.functionField) ?_
  rw [Finsupp.coe_zero, Pi.zero_apply, map_zero,
    ← TauCeti.kaehlerBasisOfFormallyEtale_repr_map R Y.functionField X.functionField bY _ i,
    hrat, map_zero, Finsupp.coe_zero, Pi.zero_apply]

/-- When `X` is integral and `cotangentMap R f ≠ 0`, `ramificationIdealSheaf R f` is an effective
Cartier divisor on `X`. -/
theorem isEffectiveCartier_ramificationIdealSheaf (hf : cotangentMap R f ≠ 0) :
    (ramificationIdealSheaf R f).IsEffectiveCartier := by
  let L₁ := (InvertibleSheaf.pullback f).obj ⟨Y.relativeDifferentials R, inferInstance⟩
  let L₂ : InvertibleSheaf X := ⟨X.relativeDifferentials R, inferInstance⟩
  let L := InvertibleSheaf.tensorProduct L₁ (InvertibleSheaf.dual L₂)
  have hne : twistedToUnit L₁ L₂ (cotangentMap R f) ≠ 0 :=
    mt (twistedToUnit_eq_zero_iff L₁ L₂ (cotangentMap R f)).mp hf
  have := L.mono_of_ne_zero_to_unit _ hne
  exact L.isEffectiveCartier_imageIdealSheaf (twistedToUnit L₁ L₂ (cotangentMap R f))

/-- For a dominant morphism of integral schemes with separable function-field extension and
invertible relative differential sheaves, `ramificationIdealSheaf R f` is effective Cartier. -/
theorem isEffectiveCartier_ramificationIdealSheaf_of_isSeparable [IsIntegral Y] [IsDominant f]
    (hsep : letI : Algebra Y.functionField X.functionField := f.functionFieldMap.hom.toAlgebra
      Algebra.IsSeparable Y.functionField X.functionField) :
    (ramificationIdealSheaf R f).IsEffectiveCartier :=
  isEffectiveCartier_ramificationIdealSheaf R f
    (cotangentMap_ne_zero_of_isDominant_of_isSeparable R f hsep)

/-- **The Picard-group Riemann–Hurwitz relation** for `𝒪_X(-R_f)`: the line-bundle class of the
ramification ideal sheaf is `f^* [Ω_{Y/R}] · [Ω_{X/R}]⁻¹`. -/
theorem mk_toInvertibleSheaf_ramificationIdealSheaf (hf : cotangentMap R f ≠ 0) :
    LineBundleClass.mk (isEffectiveCartier_ramificationIdealSheaf R f hf).toInvertibleSheaf =
      LineBundleClass.pullback f
        (LineBundleClass.mk ⟨Y.relativeDifferentials R, inferInstance⟩) *
        (LineBundleClass.mk ⟨X.relativeDifferentials R, inferInstance⟩)⁻¹ := by
  let L₁ := (InvertibleSheaf.pullback f).obj ⟨Y.relativeDifferentials R, inferInstance⟩
  let L₂ : InvertibleSheaf X := ⟨X.relativeDifferentials R, inferInstance⟩
  let L := InvertibleSheaf.tensorProduct L₁ (InvertibleSheaf.dual L₂)
  have hne : twistedToUnit L₁ L₂ (cotangentMap R f) ≠ 0 :=
    mt (twistedToUnit_eq_zero_iff L₁ L₂ (cotangentMap R f)).mp hf
  have := L.mono_of_ne_zero_to_unit _ hne
  have hmk := L.mk_toInvertibleSheaf_imageIdealSheaf (twistedToUnit L₁ L₂ (cotangentMap R f))
  exact hmk.trans (by rw [LineBundleClass.mk_tensorProduct, ← LineBundleClass.inv_mk,
    ← LineBundleClass.pullback_mk])

/-- **The Picard-group Riemann–Hurwitz formula**: `[Ω_{X/R}] = f^* [Ω_{Y/R}] · [𝒪_X(-R_f)]⁻¹`. -/
theorem mk_relativeDifferentials_eq_pullback_mul_inv_ramification (hf : cotangentMap R f ≠ 0) :
    LineBundleClass.mk ⟨X.relativeDifferentials R, inferInstance⟩ =
      LineBundleClass.pullback f
        (LineBundleClass.mk ⟨Y.relativeDifferentials R, inferInstance⟩) *
        (LineBundleClass.mk
          (isEffectiveCartier_ramificationIdealSheaf R f hf).toInvertibleSheaf)⁻¹ := by
  rw [mk_toInvertibleSheaf_ramificationIdealSheaf R f hf, mul_inv_rev, inv_inv,
    mul_comm _ (LineBundleClass.pullback f _)⁻¹, mul_inv_cancel_left]

end OverCommRing

section OverField

variable (k : Type u) [Field k] {X Y : Scheme.{u}}
  [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))] [IsIntegral X]
  [FiniteDimensional k (Scheme.Modules.Cohomology (InvertibleSheaf.trivial X).obj 0)]
  [FiniteDimensional k (Scheme.Modules.Cohomology (InvertibleSheaf.trivial X).obj 1)]
  (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
  [SheafOfModules.isInvertible X (X.relativeDifferentials k)]
  [SheafOfModules.isInvertible Y (Y.relativeDifferentials k)]

/-- **The Euler-characteristic degree Riemann–Hurwitz relation** on a proper integral curve `X`
over a field `k`: `deg Ω_{X/k} = deg (f^* Ω_{Y/k}) + dim_k Γ(R_f, 𝒪_{R_f})`. -/
theorem eulerDegree_relativeDifferentials_eq_add_ramification_finrank
    [IsProper (X ↘ Spec (.of k))] [RelativeDimensionLE 1 (X ↘ Spec (.of k))]
    (hf : cotangentMap k f ≠ 0) :
    InvertibleSheaf.eulerDegree k ⟨X.relativeDifferentials k, inferInstance⟩ =
      InvertibleSheaf.eulerDegree k
        ((InvertibleSheaf.pullback f).obj ⟨Y.relativeDifferentials k, inferInstance⟩) +
        (((ramificationIdealSheaf k f).subschemeι ≫
          X ↘ Spec (.of k)).finrank default : ℤ) := by
  let hI := isEffectiveCartier_ramificationIdealSheaf k f hf
  have := hI.isFinite_subschemeι_comp (f := X ↘ Spec (.of k))
  rw [← LineBundleClass.eulerDegree_mk,
    mk_relativeDifferentials_eq_pullback_mul_inv_ramification k f hf,
    LineBundleClass.eulerDegree_mul_of_isIntegral, LineBundleClass.eulerDegree_inv_of_isIntegral,
    LineBundleClass.pullback_mk, LineBundleClass.eulerDegree_mk, LineBundleClass.eulerDegree_mk,
    hI.eulerDegree_toInvertibleSheaf k (ramificationIdealSheaf k f) default, neg_neg]

/-- **The Euler-characteristic degree Riemann–Hurwitz formula** for a finite flat dominant
morphism `f : X ⟶ Y` onto a proper integral curve `Y` over `k`:
`deg Ω_{X/k} = [K(X) : f^* K(Y)] · deg Ω_{Y/k} + dim_k Γ(R_f, 𝒪_{R_f})`. -/
theorem eulerDegree_relativeDifferentials_eq_finrank_mul_add_ramification
    [IsIntegral Y] [IsProper (Y ↘ Spec (.of k))] [RelativeDimensionLE 1 (Y ↘ Spec (.of k))]
    [FiniteDimensional k (Scheme.Modules.Cohomology (InvertibleSheaf.trivial Y).obj 0)]
    [FiniteDimensional k (Scheme.Modules.Cohomology (InvertibleSheaf.trivial Y).obj 1)]
    [IsFinite f] [Flat f] [IsDominant f] (hf : cotangentMap k f ≠ 0) :
    InvertibleSheaf.eulerDegree k ⟨X.relativeDifferentials k, inferInstance⟩ =
      Module.finrank f.functionFieldMap.hom.fieldRange X.functionField *
        InvertibleSheaf.eulerDegree k ⟨Y.relativeDifferentials k, inferInstance⟩ +
        (((ramificationIdealSheaf k f).subschemeι ≫
          X ↘ Spec (.of k)).finrank default : ℤ) := by
  have : IsProper (X ↘ Spec (.of k)) :=
    comp_over f (Spec (.of k)) ▸ inferInstanceAs (IsProper (f ≫ Y ↘ Spec (.of k)))
  have : RelativeDimensionLE 1 (X ↘ Spec (.of k)) := by
    rw [← comp_over f (Spec (.of k)), show (1 : ℕ) = 0 + 1 from rfl]
    infer_instance
  rw [eulerDegree_relativeDifferentials_eq_add_ramification_finrank k f hf,
    ← LineBundleClass.eulerDegree_mk, ← LineBundleClass.pullback_mk,
    LineBundleClass.eulerDegree_pullback_eq_finrank_functionField_mul k f,
    LineBundleClass.eulerDegree_mk]

end OverField

end RiemannHurwitz

end TauCeti.AlgebraicGeometry

end
