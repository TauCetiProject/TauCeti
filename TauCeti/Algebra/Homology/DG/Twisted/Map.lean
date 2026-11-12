/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DG.Twisted.Equivalence
public import TauCeti.Algebra.Homology.DG.Module.Right.Restriction.Basic

/-!
# Twisting cocycles along a morphism of DG algebras

The image of a twisting cocycle under a morphism `f : (𝒜, dA) → (ℬ, dB)` of differential graded
algebras is a twisting cocycle (`TauCeti.TwistingCocycle.map`): `f` preserves degrees, commutes
with the differentials and is multiplicative, so it carries the twisting equation over.

For a differential graded right `ℬ`-module `(ℳ, dM)` and its restriction of scalars `f^* ℳ`, the
twisted complex of `f^* ℳ` with a cocycle `m` is the twisted complex of `ℳ` with the cocycle
`f ∘ m`: on underlying elements the two twisted differentials coincide
(`TauCeti.val_twistedDifferential_restrictScalars`), so the identity of the underlying modules is
an isomorphism of twisted cochain complexes
(`TauCeti.TwistingCocycle.twistedCochainComplexRestrictScalarsIso`).  This is the algebraic part
of the twist of a twisted complex by a rank-one local system, the source's
Proposition `prop:FotimesL-mL`.

The same applies to the data comparing twisting cocycles. The image under `f` of a continuation
cocycle `ν : mP → mQ` is a continuation cocycle `f ∘ mP → f ∘ mQ`
(`TauCeti.ContinuationCocycle.map`), compatibly with the Kronecker cocycles and with composition,
and the image of a parametrized cocycle is a parametrized cocycle between the images
(`TauCeti.ParametrizedCocycle.map`). So homologous twisting cocycles have homologous images
(`TauCeti.Homologous.map`). The identification of twisted complexes above is natural for this
data: it carries the continuation map of `ν` on the twisted complexes of `f^* ℳ` to the
continuation map of `f ∘ ν` on those of `ℳ`
(`TauCeti.ContinuationCocycle.continuationHom_comp_twistedCochainComplexRestrictScalarsIso_hom`),
and likewise for the homotopies of parametrized cocycles and the homotopy equivalences of
homologous cocycles. This is what makes a comparison of twisted complexes through a morphism of
DG algebras independent of the choices that the twisting cocycles depend on, up to the specified
continuation maps.

## Main definitions

* `TauCeti.TwistingCocycle.map`: the image of a twisting cocycle under a DG algebra morphism.
* `TauCeti.ContinuationCocycle.map`, `TauCeti.ParametrizedCocycle.map`, `TauCeti.Homologous.map`:
  the images of continuation cocycles, parametrized cocycles and homologous pairs.
* `TauCeti.TwistingCocycle.twistedCochainComplexRestrictScalarsIso`: the isomorphism between the
  twisted complex of a restricted module and the twisted complex of the image cocycle.

## Main results

* `TauCeti.ContinuationCocycle.continuationHom_comp_twistedCochainComplexRestrictScalarsIso_hom`,
  `TauCeti.ParametrizedCocycle.homotopy_hom_comp_twistedCochainComplexRestrictScalarsIso_hom_f`:
  the identification of twisted complexes commutes with continuation maps and their homotopies.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §1.4, Definitions 1.10 and 1.11, and
  §2.3.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, Remark 4.6.
-/

public section

open CategoryTheory MulOpposite

namespace TauCeti

universe uR uA uB uM uP uQ uS

variable {R : Type uR} {A : Type uA} {B : Type uB}
  [CommRing R] [Ring A] [Ring B] [Algebra R A] [Algebra R B]
  {𝒜 : ℤ → Submodule R A} {ℬ : ℤ → Submodule R B}
  [GradedAlgebra 𝒜] [GradedAlgebra ℬ]
  {dA : A →ₗ[R] A} {dB : B →ₗ[R] B}
  {hA : IsDGAlgebra 𝒜 dA} {hB : IsDGAlgebra ℬ dB}
  {P : Type uP} {ind : P → ℤ}

namespace TwistingCocycle

variable [Fintype P]

/-- The **image of a twisting cocycle** under a morphism of differential graded algebras. -/
def map (f : DGAlgHom hA hB) (m : TwistingCocycle 𝒜 dA P ind) :
    TwistingCocycle ℬ dB P ind where
  m x y := f (m.m x y)
  mem_graded x y := Graded.map_mem f (m.mem_graded x y)
  twisting x y := by
    rw [DGAlgHom.map_d, m.twisting x y, map_sum]
    refine Finset.sum_congr rfl fun z _ ↦ ?_
    rw [map_zsmul_unit, _root_.map_mul]
  one_sided x y hxy := by rw [m.one_sided x y hxy, map_zero]

@[simp]
theorem map_m (f : DGAlgHom hA hB) (m : TwistingCocycle 𝒜 dA P ind) (x y : P) :
    (m.map f).m x y = f (m.m x y) := by
  rw [map]

/-- The image under the identity morphism is the cocycle itself. -/
@[simp]
theorem map_id (m : TwistingCocycle 𝒜 dA P ind) : m.map (DGAlgHom.id hA) = m := by
  ext x y
  simp

variable {C : Type*} [Ring C] [Algebra R C] {𝒞 : ℤ → Submodule R C} [GradedAlgebra 𝒞]
  {dC : C →ₗ[R] C} {hC : IsDGAlgebra 𝒞 dC}

/-- The image under a composite is the image of the image. -/
@[simp]
theorem map_map (g : DGAlgHom hB hC) (f : DGAlgHom hA hB) (m : TwistingCocycle 𝒜 dA P ind) :
    (m.map f).map g = m.map (g.comp f) := by
  ext x y
  simp [DGAlgHom.comp_apply]

end TwistingCocycle

/-! ### Continuation and parametrized cocycles along a morphism -/

namespace ContinuationCocycle

variable {Q : Type uQ} {S : Type uS} {indQ : Q → ℤ} {indS : S → ℤ} [Fintype P] [Fintype Q]
  [Fintype S] {mP : TwistingCocycle 𝒜 dA P ind} {mQ : TwistingCocycle 𝒜 dA Q indQ}
  {mS : TwistingCocycle 𝒜 dA S indS}

/-- The **image of a continuation cocycle** `ν : mP → mQ` under a morphism `f` of differential
graded algebras, a continuation cocycle `f ∘ mP → f ∘ mQ`. -/
def map (f : DGAlgHom hA hB) (ν : ContinuationCocycle mP mQ) :
    ContinuationCocycle (mP.map f) (mQ.map f) where
  ν x y := f (ν.ν x y)
  mem_graded x y := Graded.map_mem f (ν.mem_graded x y)
  continuation x y := by
    rw [DGAlgHom.map_d, ν.continuation x y, map_add, map_sum, map_sum]
    simp only [map_zsmul_unit, _root_.map_mul, TwistingCocycle.map_m]

@[simp]
theorem map_ν (f : DGAlgHom hA hB) (ν : ContinuationCocycle mP mQ) (x : P) (y : Q) :
    (ν.map f).ν x y = f (ν.ν x y) :=
  (rfl)

/-- The image of the Kronecker continuation cocycle is the Kronecker continuation cocycle. -/
@[simp]
theorem map_refl [DecidableEq P] (f : DGAlgHom hA hB) (m : TwistingCocycle 𝒜 dA P ind) :
    (refl hA.map_one_eq_zero m).map f = refl hB.map_one_eq_zero (m.map f) := by
  ext x y
  simp only [map_ν, refl_ν, Matrix.one_apply, apply_ite f, map_one, map_zero]

/-- The image of a composite of continuation cocycles is the composite of the images. -/
@[simp]
theorem map_comp (f : DGAlgHom hA hB) (ν₁ : ContinuationCocycle mP mQ)
    (ν₂ : ContinuationCocycle mQ mS) :
    (ν₁.comp hA ν₂).map f = (ν₁.map f).comp hB (ν₂.map f) := by
  ext x y
  simp only [map_ν, comp_ν, Matrix.mul_apply, Matrix.of_apply, map_sum, _root_.map_mul]

end ContinuationCocycle

namespace ParametrizedCocycle

variable {Q : Type uQ} {indQ : Q → ℤ} [Fintype P] [Fintype Q]
  {mP : TwistingCocycle 𝒜 dA P ind} {mQ : TwistingCocycle 𝒜 dA Q indQ}
  {ν₀ ν₁ : ContinuationCocycle mP mQ}

/-- The **image of a parametrized cocycle** between `ν₀` and `ν₁` under a morphism `f` of
differential graded algebras, a parametrized cocycle between the images of `ν₀` and `ν₁`. -/
def map (f : DGAlgHom hA hB) (η : ParametrizedCocycle ν₀ ν₁) :
    ParametrizedCocycle (ν₀.map f) (ν₁.map f) where
  h x y := f (η.h x y)
  mem_graded x y := Graded.map_mem f (η.mem_graded x y)
  parametrized x y := by
    rw [DGAlgHom.map_d, η.parametrized x y, map_add, map_add, map_sub, map_sum, map_sum]
    simp only [map_zsmul_unit, _root_.map_mul, TwistingCocycle.map_m,
      ContinuationCocycle.map_ν]

@[simp]
theorem map_h (f : DGAlgHom hA hB) (η : ParametrizedCocycle ν₀ ν₁) (x : P) (y : Q) :
    (η.map f).h x y = f (η.h x y) :=
  (rfl)

end ParametrizedCocycle

namespace Homologous

variable {Q : Type uP} {indQ : Q → ℤ} [Fintype P] [Fintype Q] [DecidableEq P] [DecidableEq Q]
  {mP : TwistingCocycle 𝒜 dA P ind} {mQ : TwistingCocycle 𝒜 dA Q indQ}

/-- **Homologous twisting cocycles have homologous images** under a morphism `f` of differential
graded algebras, through the images of the continuation and parametrized cocycles. -/
def map (f : DGAlgHom hA hB) (H : Homologous hA mP mQ) : Homologous hB (mP.map f) (mQ.map f) where
  ν := H.ν.map f
  ν' := H.ν'.map f
  homP := ContinuationCocycle.map_refl f mP ▸ ContinuationCocycle.map_comp f H.ν H.ν' ▸
    H.homP.map f
  homQ := ContinuationCocycle.map_refl f mQ ▸ ContinuationCocycle.map_comp f H.ν' H.ν ▸
    H.homQ.map f

@[simp]
theorem map_ν (f : DGAlgHom hA hB) (H : Homologous hA mP mQ) : (H.map f).ν = H.ν.map f :=
  (rfl)

@[simp]
theorem map_ν' (f : DGAlgHom hA hB) (H : Homologous hA mP mQ) : (H.map f).ν' = H.ν'.map f :=
  (rfl)

end Homologous

section Restrict

variable {M : Type uM} [AddCommGroup M] [Module R M]
  {ℳ : ℤ → Submodule R M} [DirectSum.Decomposition ℳ] (f : DGAlgHom hA hB)

/-- The identification of `P → f^* M` with `P → M` matches the total gradings. -/
theorem map_twistedTotalGrading_restrictScalarsPiEquiv (n : ℤ) :
    (twistedTotalGrading (IsDGRightModule.restrictScalarsGrading (ℳ := ℳ) f) ind n).map
        (restrictScalarsPiEquiv (M := M) (P := P) f :
          (P → DGRightModule.RestrictScalars f M) →ₗ[R] (P → M)) =
      twistedTotalGrading ℳ ind n := by
  ext g
  rw [Submodule.mem_map_equiv, mem_twistedTotalGrading_iff, mem_twistedTotalGrading_iff]
  refine forall_congr' fun x ↦ ?_
  rw [IsDGRightModule.mem_restrictScalarsGrading_iff,
    DGRightModule.RestrictScalars.linearEquiv_apply, ← restrictScalarsPiEquiv_apply,
    LinearEquiv.apply_symm_apply]

variable [Fintype P] [Module Bᵐᵒᵖ M] [IsScalarTower R Bᵐᵒᵖ M] {dM : M →ₗ[R] M} (m : P → P → A)

/-- On underlying elements, the twisted differential of a restricted module with the matrix `m` is
the twisted differential of the original module with the matrix `f ∘ m`. -/
theorem val_twistedDifferential_restrictScalars (g : P → DGRightModule.RestrictScalars f M)
    (y : P) :
    (twistedDifferential m (IsDGRightModule.restrictScalarsGrading (ℳ := ℳ) f)
        (IsDGRightModule.restrictScalarsDifferential (dM := dM) f) g y).val =
      twistedDifferential (fun x y ↦ f (m x y)) ℳ dM (fun x ↦ (g x).val) y := by
  rw [twistedDifferential_apply, twistedDifferential_apply, DGRightModule.RestrictScalars.val_add,
    IsDGRightModule.val_restrictScalarsDifferential]
  congr 1
  rw [← DGRightModule.RestrictScalars.linearEquiv_apply, map_sum]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  rw [DGRightModule.RestrictScalars.linearEquiv_apply, DGRightModule.RestrictScalars.val_op_smul,
    val_koszulTwist_restrictScalars]

/-- On underlying elements, the continuation map of a restricted module with the matrix `ν` is the
continuation map of the original module with the matrix `f ∘ ν`. -/
theorem restrictScalarsPiEquiv_continuationMap {Q : Type*} (ν : P → Q → A)
    (g : P → DGRightModule.RestrictScalars f M) :
    restrictScalarsPiEquiv (M := M) (P := Q) f (continuationMap R _ ν g) =
      continuationMap R M (fun x y ↦ f (ν x y)) (restrictScalarsPiEquiv (M := M) (P := P) f g) := by
  funext y
  rw [restrictScalarsPiEquiv_apply, continuationMap_apply, continuationMap_apply,
    ← DGRightModule.RestrictScalars.linearEquiv_apply, map_sum]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  rw [DGRightModule.RestrictScalars.linearEquiv_apply, DGRightModule.RestrictScalars.val_op_smul,
    restrictScalarsPiEquiv_apply]

/-- On underlying elements, the homotopy map of a restricted module with the matrix `η` is the
homotopy map of the original module with the matrix `f ∘ η`. -/
theorem restrictScalarsPiEquiv_homotopyMap {Q : Type*} (η : P → Q → A)
    (g : P → DGRightModule.RestrictScalars f M) :
    restrictScalarsPiEquiv (M := M) (P := Q) f
        (homotopyMap η (IsDGRightModule.restrictScalarsGrading (ℳ := ℳ) f) g) =
      homotopyMap (fun x y ↦ f (η x y)) ℳ (restrictScalarsPiEquiv (M := M) (P := P) f g) := by
  funext y
  rw [restrictScalarsPiEquiv_apply, homotopyMap_apply, homotopyMap_apply,
    ← DGRightModule.RestrictScalars.linearEquiv_apply, map_sum]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  rw [DGRightModule.RestrictScalars.linearEquiv_apply, DGRightModule.RestrictScalars.val_op_smul,
    val_koszulTwist_restrictScalars, restrictScalarsPiEquiv_apply]

namespace TwistingCocycle

variable [SetLike.GradedSMul (InternalGrading.ofDecomposition ℬ).opposite.piece ℳ]
  (m : TwistingCocycle 𝒜 dA P ind) (hM : IsDGRightModule hB ℳ dM)

/-- The degree-`n` part of the identification of the two twisted complexes. -/
noncomputable def twistedCochainComplexRestrictScalarsXEquiv (n : ℤ) :
    (m.twistedCochainComplex (IsDGRightModule.restrictScalarsDifferential (dM := dM) f)
      (hM.restrictScalars f)).X n ≃ₗ[R]
      ((m.map f).twistedCochainComplex dM hM).X n :=
  (twistedCochainComplexXEquiv m.mem_graded m.twisting (hM.restrictScalars f) n).trans <|
    ((restrictScalarsPiEquiv (M := M) (P := P) f).ofSubmodules _ _
      (map_twistedTotalGrading_restrictScalarsPiEquiv f n)).trans
      (twistedCochainComplexXEquiv (m.map f).mem_graded (m.map f).twisting hM n).symm

/-- The degree-`n` identification is the identity of the underlying elements. -/
theorem twistedCochainComplexXEquiv_restrictScalarsXEquiv (n : ℤ)
    (g : (m.twistedCochainComplex (IsDGRightModule.restrictScalarsDifferential (dM := dM) f)
      (hM.restrictScalars f)).X n) :
    (twistedCochainComplexXEquiv (m.map f).mem_graded (m.map f).twisting hM n
        (m.twistedCochainComplexRestrictScalarsXEquiv f hM n g) : P → M) =
      restrictScalarsPiEquiv (M := M) (P := P) f
        (twistedCochainComplexXEquiv m.mem_graded m.twisting (hM.restrictScalars f) n g) := by
  simp [twistedCochainComplexRestrictScalarsXEquiv]

/-- **The twisted complex of a restricted module** with the cocycle `m` is isomorphic to the
twisted complex of the original module with the image cocycle `f ∘ m`, through the identity of
the underlying modules. -/
noncomputable def twistedCochainComplexRestrictScalarsIso :
    m.twistedCochainComplex (IsDGRightModule.restrictScalarsDifferential (dM := dM) f)
      (hM.restrictScalars f) ≅ (m.map f).twistedCochainComplex dM hM :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n ↦ (m.twistedCochainComplexRestrictScalarsXEquiv f hM n).toModuleIso) fun i j hij ↦ by
      obtain rfl : i + 1 = j := hij
      ext g
      apply (twistedCochainComplexXEquiv (m.map f).mem_graded (m.map f).twisting hM
        (i + 1)).injective
      apply Subtype.ext
      funext y
      simp only [ModuleCat.hom_comp, LinearMap.comp_apply, LinearEquiv.toModuleIso_hom,
        ModuleCat.hom_ofHom, LinearEquiv.coe_coe]
      rw [twistedCochainComplexXEquiv_restrictScalarsXEquiv, twistedCochainComplexXEquiv_d,
        twistedCochainComplexXEquiv_d, restrictScalarsPiEquiv_apply,
        val_twistedDifferential_restrictScalars, twistedCochainComplexXEquiv_restrictScalarsXEquiv]
      exact congrArg (fun φ ↦ twistedDifferential (fun x y ↦ f (m.m x y)) ℳ dM φ y)
        (funext fun x ↦ restrictScalarsPiEquiv_apply f _ x)

/-- The isomorphism of twisted complexes is the degreewise identification. -/
@[simp]
theorem twistedCochainComplexRestrictScalarsIso_hom_f_apply (n : ℤ)
    (g : (m.twistedCochainComplex (IsDGRightModule.restrictScalarsDifferential (dM := dM) f)
      (hM.restrictScalars f)).X n) :
    ((m.twistedCochainComplexRestrictScalarsIso f hM).hom.f n).hom g =
      m.twistedCochainComplexRestrictScalarsXEquiv f hM n g := by
  simp only [twistedCochainComplexRestrictScalarsIso, HomologicalComplex.Hom.isoOfComponents_hom_f,
    LinearEquiv.toModuleIso_hom, ModuleCat.hom_ofHom, LinearEquiv.coe_coe]

/-- The inverse isomorphism of twisted complexes is the inverse degreewise identification. -/
@[simp]
theorem twistedCochainComplexRestrictScalarsIso_inv_f_apply (n : ℤ)
    (g : ((m.map f).twistedCochainComplex dM hM).X n) :
    ((m.twistedCochainComplexRestrictScalarsIso f hM).inv.f n).hom g =
      (m.twistedCochainComplexRestrictScalarsXEquiv f hM n).symm g := by
  simp only [twistedCochainComplexRestrictScalarsIso, HomologicalComplex.Hom.isoOfComponents_inv_f,
    LinearEquiv.toModuleIso_inv, ModuleCat.hom_ofHom, LinearEquiv.coe_coe]

end TwistingCocycle

variable [SetLike.GradedSMul (InternalGrading.ofDecomposition ℬ).opposite.piece ℳ]
  (hM : IsDGRightModule hB ℳ dM) {Q : Type uP} {indQ : Q → ℤ} [Fintype Q]
  {mP : TwistingCocycle 𝒜 dA P ind} {mQ : TwistingCocycle 𝒜 dA Q indQ}

namespace ContinuationCocycle

/-- **Continuation maps commute with restriction of scalars**: through the identifications
`twistedCochainComplexRestrictScalarsIso` of the twisted complexes of a restricted module `f^* ℳ`
with those of `ℳ` and the image cocycles, the continuation map of `ν` is the continuation map of
its image `f ∘ ν`. -/
@[reassoc]
theorem continuationHom_comp_twistedCochainComplexRestrictScalarsIso_hom
    (ν : ContinuationCocycle mP mQ) :
    ν.continuationHom (hM.restrictScalars f) ≫
        (mQ.twistedCochainComplexRestrictScalarsIso f hM).hom =
      (mP.twistedCochainComplexRestrictScalarsIso f hM).hom ≫ (ν.map f).continuationHom hM := by
  refine HomologicalComplex.hom_ext _ _ fun n ↦ ModuleCat.hom_ext (LinearMap.ext fun g ↦ ?_)
  apply (twistedCochainComplexXEquiv (mQ.map f).mem_graded (mQ.map f).twisting hM n).injective
  apply Subtype.ext
  simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply,
    TwistingCocycle.twistedCochainComplexRestrictScalarsIso_hom_f_apply,
    TwistingCocycle.twistedCochainComplexXEquiv_restrictScalarsXEquiv, continuationHom_f_apply]
  exact restrictScalarsPiEquiv_continuationMap f ν.ν _

end ContinuationCocycle

namespace ParametrizedCocycle

variable {ν₀ ν₁ : ContinuationCocycle mP mQ}

/-- **Homotopies of parametrized cocycles commute with restriction of scalars**: through the
identifications `twistedCochainComplexRestrictScalarsIso`, the homotopy of `η` between the
continuation maps of `ν₀` and `ν₁` on the twisted complexes of `f^* ℳ` is the homotopy of its
image `f ∘ η` on the twisted complexes of `ℳ`. -/
@[reassoc]
theorem homotopy_hom_comp_twistedCochainComplexRestrictScalarsIso_hom_f
    (η : ParametrizedCocycle ν₀ ν₁) (i j : ℤ) :
    (η.homotopy (hM.restrictScalars f)).hom i j ≫
        (mQ.twistedCochainComplexRestrictScalarsIso f hM).hom.f j =
      (mP.twistedCochainComplexRestrictScalarsIso f hM).hom.f i ≫
        ((η.map f).homotopy hM).hom i j := by
  by_cases hij : j + 1 = i
  · subst hij
    refine ModuleCat.hom_ext (LinearMap.ext fun g ↦ ?_)
    apply (twistedCochainComplexXEquiv (mQ.map f).mem_graded (mQ.map f).twisting hM j).injective
    apply Subtype.ext
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply,
      TwistingCocycle.twistedCochainComplexRestrictScalarsIso_hom_f_apply,
      TwistingCocycle.twistedCochainComplexXEquiv_restrictScalarsXEquiv, homotopy_hom_apply]
    exact restrictScalarsPiEquiv_homotopyMap f η.h _
  · rw [homotopy_hom_eq_zero _ _ hij, homotopy_hom_eq_zero _ _ hij, Limits.zero_comp,
      Limits.comp_zero]

end ParametrizedCocycle

namespace Homologous

variable [DecidableEq P] [DecidableEq Q]

/-- The homotopy equivalence of homologous twisting cocycles commutes with restriction of scalars:
through the identifications `twistedCochainComplexRestrictScalarsIso`, the homotopy equivalence of
`H` on the twisted complexes of `f^* ℳ` is that of its image `H.map f` on those of `ℳ`. -/
@[reassoc]
theorem homotopyEquiv_hom_comp_twistedCochainComplexRestrictScalarsIso_hom
    (H : Homologous hA mP mQ) :
    (H.homotopyEquiv (hM.restrictScalars f)).hom ≫
        (mQ.twistedCochainComplexRestrictScalarsIso f hM).hom =
      (mP.twistedCochainComplexRestrictScalarsIso f hM).hom ≫ ((H.map f).homotopyEquiv hM).hom := by
  rw [homotopyEquiv_hom, homotopyEquiv_hom, map_ν,
    ContinuationCocycle.continuationHom_comp_twistedCochainComplexRestrictScalarsIso_hom]

/-- The inverse of the homotopy equivalence of homologous twisting cocycles commutes with
restriction of scalars. -/
@[reassoc]
theorem homotopyEquiv_inv_comp_twistedCochainComplexRestrictScalarsIso_hom
    (H : Homologous hA mP mQ) :
    (H.homotopyEquiv (hM.restrictScalars f)).inv ≫
        (mP.twistedCochainComplexRestrictScalarsIso f hM).hom =
      (mQ.twistedCochainComplexRestrictScalarsIso f hM).hom ≫ ((H.map f).homotopyEquiv hM).inv := by
  rw [homotopyEquiv_inv, homotopyEquiv_inv, map_ν',
    ContinuationCocycle.continuationHom_comp_twistedCochainComplexRestrictScalarsIso_hom]

end Homologous

end Restrict

end TauCeti
