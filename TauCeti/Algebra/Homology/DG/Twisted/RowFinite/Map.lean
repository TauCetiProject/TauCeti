/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DG.Twisted.RowFinite.Equivalence
public import TauCeti.Algebra.Homology.DG.Twisted.Map
public import TauCeti.LinearAlgebra.Finsupp.LinearCombination

/-!
# Row-finite twisting cocycles along a morphism of DG algebras

Let `f : (𝒜, dA) → (ℬ, dB)` be a morphism of differential graded algebras. Applying `f` to every
coefficient of the finite rows of a row-finite twisting cocycle `m` gives a row-finite twisting
cocycle `f ∘ m` on the same graded generators (`TauCeti.RowFiniteTwistingCocycle.map`). The same
holds for row-finite continuation cocycles and parametrized cocycles
(`TauCeti.RowFiniteContinuationCocycle.map`, `TauCeti.RowFiniteParametrizedCocycle.map`), so
homologous row-finite cocycles have homologous images (`TauCeti.RowFiniteHomologous.map`). All
of this rests on one identity: applying `f` coefficientwise intertwines the twisted differentials
of the free left modules (`TauCeti.mapRange_rowFiniteTwistedDifferential`), and likewise the signed
extensions (`TauCeti.mapRange_rowFiniteSignedMap`) and the row substitutions
(`Finsupp.mapRange_linearCombination`).

For a differential graded right `ℬ`-module `ℳ` and its restriction of scalars `f^* ℳ`, the
row-finite twisted complex of `f^* ℳ` with the cocycle `m` is the row-finite twisted complex of
`ℳ` with the cocycle `f ∘ m`. Both live on finitely supported coefficient vectors, and the
coordinatewise identification of `P →₀ f^* M` with `P →₀ M` intertwines the two coefficient
differentials, so it is an isomorphism of coefficient complexes
(`TauCeti.RowFiniteTwistingCocycle.coefficientCochainComplexRestrictScalarsIso`). It is natural in
the cocycle: it intertwines the continuation maps of a continuation cocycle and of its image
(`continuationHom_comp_coefficientCochainComplexRestrictScalarsIso_hom`),
and the coordinatewise identification likewise intertwines the homotopies of a parametrized
cocycle and of its image.

This is the row-finite form of `TauCeti.Algebra.Homology.DG.Twisted.Map`, which treats finite
generator sets; the two agree through `TauCeti.TwistingCocycle.toRowFinite`
(`TauCeti.TwistingCocycle.toRowFinite_map`). Its use is the change of DG algebra under a twisted
complex with infinitely many generators: the twisted complex of a pulled-back DG local system,
restricted along the morphism of loop-chain algebras induced by a map of spaces, is the twisted
complex of the pushed-forward cocycle.

## Main definitions

* `TauCeti.RowFiniteTwistingCocycle.map`: the image of a row-finite twisting cocycle under a DG
  algebra morphism.
* `TauCeti.RowFiniteContinuationCocycle.map`, `TauCeti.RowFiniteParametrizedCocycle.map`,
  `TauCeti.RowFiniteHomologous.map`: the images of continuation cocycles, parametrized cocycles
  and homologous pairs.
* `TauCeti.RowFiniteTwistingCocycle.coefficientCochainComplexRestrictScalarsIso`: the isomorphism
  between the twisted complex of a restricted module and the twisted complex of the image
  cocycle.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §1.4, Definitions 1.10 and 1.11, and
  §2.3.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, Remark 4.6.
-/

public noncomputable section

open CategoryTheory MulOpposite

namespace TauCeti

universe uR uA uB uM uP uQ uS

variable {R : Type uR} {A : Type uA} {B : Type uB}
  [CommRing R] [Ring A] [Ring B] [Algebra R A] [Algebra R B]
  {𝒜 : ℤ → Submodule R A} {ℬ : ℤ → Submodule R B}
  [GradedAlgebra 𝒜] [GradedAlgebra ℬ]
  {dA : A →ₗ[R] A} {dB : B →ₗ[R] B}
  {hA : IsDGAlgebra 𝒜 dA} {hB : IsDGAlgebra ℬ dB}
  {P : Type uP} {Q : Type uQ} {S : Type uS} {indP : P → ℤ} {indQ : Q → ℤ} {indS : S → ℤ}

/-! ### Finite rows along a morphism -/

section Rows

/-- Applying a graded ring homomorphism coefficientwise commutes with the Koszul-signed extension
of the images of the generators. -/
theorem mapRange_rowFiniteSignedMap {F : Type*} [FunLike F A B] [GradedFunLike F 𝒜 ℬ]
    [RingHomClass F A B] (f : F) (h : P → Q →₀ A) (g : P →₀ A) :
    Finsupp.mapRange f (map_zero f) (rowFiniteSignedMap (𝒜 := 𝒜) h g) =
      rowFiniteSignedMap (𝒜 := ℬ) (fun x ↦ Finsupp.mapRange f (map_zero f) (h x))
        (Finsupp.mapRange f (map_zero f) g) := by
  refine DFunLike.congr_fun (Finsupp.addHom_ext_of_decomposition 𝒜
    (φ := (Finsupp.mapRange.addMonoidHom (f : A →+ B)).comp
      (rowFiniteSignedMap (𝒜 := 𝒜) h).toAddMonoidHom)
    (ψ := (rowFiniteSignedMap (𝒜 := ℬ) _).toAddMonoidHom.comp
      (Finsupp.mapRange.addMonoidHom (f : A →+ B))) fun x q c hc ↦ ?_) g
  classical
  simp only [AddMonoidHom.coe_comp, Function.comp_apply, LinearMap.toAddMonoidHom_coe,
    Finsupp.mapRange.addMonoidHom_apply, AddMonoidHom.coe_ofClass]
  rw [rowFiniteSignedMap_single h x hc, Finsupp.mapRange_single,
    rowFiniteSignedMap_single _ x (Graded.map_mem f hc)]
  ext z
  simp [Units.smul_def]

variable (f : DGAlgHom hA hB)

/-- **Applying a DG algebra morphism coefficientwise intertwines the twisted differentials** of
the free left modules: the image of `D_m g` is `D_{f ∘ m} (f ∘ g)`. -/
theorem mapRange_rowFiniteTwistedDifferential (m : P → P →₀ A) (g : P →₀ A) :
    Finsupp.mapRange f (map_zero f) (rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := dA) m g) =
      rowFiniteTwistedDifferential (𝒜 := ℬ) (d := dB)
        (fun x ↦ Finsupp.mapRange f (map_zero f) (m x)) (Finsupp.mapRange f (map_zero f) g) := by
  refine DFunLike.congr_fun (Finsupp.addHom_ext_of_decomposition 𝒜
    (φ := (Finsupp.mapRange.addMonoidHom (f : A →+ B)).comp
      (rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := dA) m).toAddMonoidHom)
    (ψ := (rowFiniteTwistedDifferential (𝒜 := ℬ) (d := dB) _).toAddMonoidHom.comp
      (Finsupp.mapRange.addMonoidHom (f : A →+ B))) fun x q c hc ↦ ?_) g
  classical
  simp only [AddMonoidHom.coe_comp, Function.comp_apply, LinearMap.toAddMonoidHom_coe,
    Finsupp.mapRange.addMonoidHom_apply, AddMonoidHom.coe_ofClass]
  rw [rowFiniteTwistedDifferential_single m x hc, Finsupp.mapRange_single,
    rowFiniteTwistedDifferential_single _ x (Graded.map_mem f hc)]
  ext z
  simp [Units.smul_def, Finsupp.single_apply, apply_ite f]

end Rows

/-! ### Twisting, continuation and parametrized cocycles along a morphism -/

namespace RowFiniteTwistingCocycle

/-- The **image of a row-finite twisting cocycle** under a morphism of differential graded
algebras: every coefficient of every row is replaced by its image. -/
def map (f : DGAlgHom hA hB) (m : RowFiniteTwistingCocycle 𝒜 dA P indP) :
    RowFiniteTwistingCocycle ℬ dB P indP where
  m x := Finsupp.mapRange f (map_zero f) (m.m x)
  mem_graded x y := by
    rw [Finsupp.mapRange_apply]
    exact Graded.map_mem f (m.mem_graded x y)
  twisting x := by
    ext z
    simp only [Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_apply, DGAlgHom.map_d]
    rw [m.twisting_apply, Finsupp.sum_mapRange_index (fun y ↦ by simp), Finsupp.sum_apply,
      Finsupp.sum, Finsupp.sum, map_sum]
    refine Finset.sum_congr rfl fun y _ ↦ ?_
    simp [map_zsmul_unit]

/-- The rows of the image cocycle are the coefficientwise images of the rows. -/
theorem map_m (f : DGAlgHom hA hB) (m : RowFiniteTwistingCocycle 𝒜 dA P indP) (x : P) :
    (m.map f).m x = Finsupp.mapRange f (map_zero f) (m.m x) :=
  (rfl)

@[simp]
theorem map_m_apply (f : DGAlgHom hA hB) (m : RowFiniteTwistingCocycle 𝒜 dA P indP) (x y : P) :
    (m.map f).m x y = f (m.m x y) :=
  (rfl)

/-- The rows of the image cocycle are supported in the rows of the cocycle, so the image of a
semi-free cocycle is semi-free. -/
theorem support_map_m_subset (f : DGAlgHom hA hB) (m : RowFiniteTwistingCocycle 𝒜 dA P indP)
    (x : P) : ((m.map f).m x).support ⊆ (m.m x).support :=
  Finsupp.support_mapRange (hf := map_zero f)

/-- The image under the identity morphism is the cocycle itself. -/
@[simp]
theorem map_id (m : RowFiniteTwistingCocycle 𝒜 dA P indP) : m.map (DGAlgHom.id hA) = m := by
  ext x y
  simp

variable {C : Type*} [Ring C] [Algebra R C] {𝒞 : ℤ → Submodule R C} [GradedAlgebra 𝒞]
  {dC : C →ₗ[R] C} {hC : IsDGAlgebra 𝒞 dC}

/-- The image under a composite is the image of the image. -/
@[simp]
theorem map_map (g : DGAlgHom hB hC) (f : DGAlgHom hA hB)
    (m : RowFiniteTwistingCocycle 𝒜 dA P indP) : (m.map f).map g = m.map (g.comp f) := by
  ext x y
  simp

end RowFiniteTwistingCocycle

/-- On finite generator sets, the image of a twisting cocycle is the image of its row-finite
form. -/
@[simp]
theorem TwistingCocycle.toRowFinite_map [Fintype P] (f : DGAlgHom hA hB)
    (m : TwistingCocycle 𝒜 dA P indP) : (m.map f).toRowFinite = m.toRowFinite.map f := by
  ext x y
  simp

namespace RowFiniteContinuationCocycle

variable {mP : RowFiniteTwistingCocycle 𝒜 dA P indP} {mQ : RowFiniteTwistingCocycle 𝒜 dA Q indQ}
  {mS : RowFiniteTwistingCocycle 𝒜 dA S indS}

/-- The **image of a row-finite continuation cocycle** `ν : mP → mQ` under a morphism `f` of
differential graded algebras, a continuation cocycle `f ∘ mP → f ∘ mQ`. -/
def map (f : DGAlgHom hA hB) (ν : RowFiniteContinuationCocycle mP mQ) :
    RowFiniteContinuationCocycle (mP.map f) (mQ.map f) where
  ν x := Finsupp.mapRange f (map_zero f) (ν.ν x)
  mem_graded x y := by
    rw [Finsupp.mapRange_apply]
    exact Graded.map_mem f (ν.mem_graded x y)
  continuation x := by
    have h := congrArg (Finsupp.mapRange f (map_zero f)) (ν.continuation x)
    rw [mapRange_rowFiniteTwistedDifferential, Finsupp.mapRange_linearCombination] at h
    exact h

@[simp]
theorem map_ν_apply (f : DGAlgHom hA hB) (ν : RowFiniteContinuationCocycle mP mQ) (x : P)
    (y : Q) : (ν.map f).ν x y = f (ν.ν x y) :=
  (rfl)

/-- The image of the identity continuation cocycle is the identity continuation cocycle. -/
@[simp]
theorem map_refl (f : DGAlgHom hA hB) (m : RowFiniteTwistingCocycle 𝒜 dA P indP) :
    (refl m hA).map f = refl (m.map f) hB := by
  classical
  ext x y
  simp [Finsupp.single_apply, apply_ite f]

/-- The image of a composite of continuation cocycles is the composite of the images. -/
@[simp]
theorem map_comp (f : DGAlgHom hA hB) (ν : RowFiniteContinuationCocycle mP mQ)
    (μ : RowFiniteContinuationCocycle mQ mS) : (ν.comp μ hA).map f = (ν.map f).comp (μ.map f) hB :=
  ext fun x y ↦ by
    rw [map_ν_apply, comp_ν, comp_ν]
    exact DFunLike.congr_fun (Finsupp.mapRange_linearCombination f μ.ν (ν.ν x)) y

end RowFiniteContinuationCocycle

namespace RowFiniteParametrizedCocycle

variable {mP : RowFiniteTwistingCocycle 𝒜 dA P indP} {mQ : RowFiniteTwistingCocycle 𝒜 dA Q indQ}
  {ν₀ ν₁ : RowFiniteContinuationCocycle mP mQ}

/-- The **image of a row-finite parametrized cocycle** between `ν₀` and `ν₁` under a morphism `f`
of differential graded algebras, a parametrized cocycle between the images of `ν₀` and `ν₁`. -/
def map (f : DGAlgHom hA hB) (η : RowFiniteParametrizedCocycle ν₀ ν₁) :
    RowFiniteParametrizedCocycle (ν₀.map f) (ν₁.map f) where
  h x := Finsupp.mapRange f (map_zero f) (η.h x)
  mem_graded x y := by
    rw [Finsupp.mapRange_apply]
    exact Graded.map_mem f (η.mem_graded x y)
  parametrized x := by
    have h := congrArg (Finsupp.mapRange f (map_zero f)) (η.parametrized x)
    rw [Finsupp.mapRange_add (map_add f), mapRange_rowFiniteTwistedDifferential,
      mapRange_rowFiniteSignedMap, Finsupp.mapRange_sub (map_sub f)] at h
    exact h

@[simp]
theorem map_h_apply (f : DGAlgHom hA hB) (η : RowFiniteParametrizedCocycle ν₀ ν₁) (x : P)
    (y : Q) : (η.map f).h x y = f (η.h x y) :=
  (rfl)

/-- The same homotopy rows, viewed as a parametrized cocycle between equal endpoint continuation
cocycles. -/
private def copyEndpoints {ν₀' ν₁' : RowFiniteContinuationCocycle mP mQ}
    (η : RowFiniteParametrizedCocycle ν₀ ν₁) (h₀ : ν₀ = ν₀') (h₁ : ν₁ = ν₁') :
    RowFiniteParametrizedCocycle ν₀' ν₁' where
  h := η.h
  mem_graded := η.mem_graded
  parametrized x := h₀ ▸ h₁ ▸ η.parametrized x

end RowFiniteParametrizedCocycle

namespace RowFiniteHomologous

variable {P Q : Type uP} {indP : P → ℤ} {indQ : Q → ℤ}
  {mP : RowFiniteTwistingCocycle 𝒜 dA P indP} {mQ : RowFiniteTwistingCocycle 𝒜 dA Q indQ}

/-- The images of homologous row-finite twisting cocycles under a morphism of differential graded
algebras are homologous, through the images of the continuation and parametrized cocycles. -/
def map (f : DGAlgHom hA hB) (H : RowFiniteHomologous hA mP mQ) :
    RowFiniteHomologous hB (mP.map f) (mQ.map f) where
  ν := H.ν.map f
  ν' := H.ν'.map f
  homP := (H.homP.map f).copyEndpoints (RowFiniteContinuationCocycle.map_refl f mP)
    (RowFiniteContinuationCocycle.map_comp f H.ν H.ν')
  homQ := (H.homQ.map f).copyEndpoints (RowFiniteContinuationCocycle.map_refl f mQ)
    (RowFiniteContinuationCocycle.map_comp f H.ν' H.ν)

@[simp]
theorem map_ν (f : DGAlgHom hA hB) (H : RowFiniteHomologous hA mP mQ) :
    (H.map f).ν = H.ν.map f :=
  (rfl)

@[simp]
theorem map_ν' (f : DGAlgHom hA hB) (H : RowFiniteHomologous hA mP mQ) :
    (H.map f).ν' = H.ν'.map f :=
  (rfl)

@[simp]
theorem map_homP_h_apply (f : DGAlgHom hA hB) (H : RowFiniteHomologous hA mP mQ) (x y : P) :
    (H.map f).homP.h x y = f (H.homP.h x y) :=
  (rfl)

@[simp]
theorem map_homQ_h_apply (f : DGAlgHom hA hB) (H : RowFiniteHomologous hA mP mQ) (x y : Q) :
    (H.map f).homQ.h x y = f (H.homQ.h x y) :=
  (rfl)

end RowFiniteHomologous

/-! ### Twisted complexes of a restricted module -/

section Restrict

variable {M : Type uM} [AddCommGroup M] [Module R M] [Module Bᵐᵒᵖ M] [IsScalarTower R Bᵐᵒᵖ M]
  {ℳ : ℤ → Submodule R M} [DirectSum.Decomposition ℳ]
  [SetLike.GradedSMul (InternalGrading.ofDecomposition ℬ).opposite.piece ℳ]
  {dM : M →ₗ[R] M} (f : DGAlgHom hA hB)

omit [Module Bᵐᵒᵖ M] [IsScalarTower R Bᵐᵒᵖ M]
  [SetLike.GradedSMul (InternalGrading.ofDecomposition ℬ).opposite.piece ℳ] in
/-- The coordinatewise identification of `P →₀ f^* M` with `P →₀ M` matches the total
gradings. -/
theorem mapRange_linearEquiv_mem_rowFiniteTotalGrading_iff {n : ℤ}
    {g : P →₀ DGRightModule.RestrictScalars f M} :
    Finsupp.mapRange.linearEquiv (DGRightModule.RestrictScalars.linearEquiv f M) g ∈
        rowFiniteTotalGrading ℳ indP n ↔
      g ∈ rowFiniteTotalGrading (IsDGRightModule.restrictScalarsGrading (ℳ := ℳ) f) indP n := by
  simp only [mem_rowFiniteTotalGrading_iff, Finsupp.mapRange.linearEquiv_apply,
    Finsupp.mapRange_apply, IsDGRightModule.mem_restrictScalarsGrading_iff]

namespace RowFiniteTwistingCocycle

variable (m : RowFiniteTwistingCocycle 𝒜 dA P indP) (hM : IsDGRightModule hB ℳ dM)

/-- On coefficient vectors, the twisted differential of a restricted module with the cocycle `m`
is the twisted differential of the original module with the image cocycle `f ∘ m`. -/
theorem mapRange_linearEquiv_coefficientDifferential_restrictScalars
    (g : P →₀ DGRightModule.RestrictScalars f M) :
    Finsupp.mapRange.linearEquiv (DGRightModule.RestrictScalars.linearEquiv f M)
        (m.coefficientDifferential (hM.restrictScalars f) g) =
      (m.map f).coefficientDifferential hM
        (Finsupp.mapRange.linearEquiv (DGRightModule.RestrictScalars.linearEquiv f M) g) := by
  classical
  set e := Finsupp.mapRange.linearEquiv (α := P) (DGRightModule.RestrictScalars.linearEquiv f M)
  have he (y : P) (β : DGRightModule.RestrictScalars f M) :
      e (Finsupp.single y β) = Finsupp.single y β.val := by
    simp [e]
  induction g using Finsupp.induction_linear with
  | zero => simp
  | add g g' hg hg' => simp only [map_add, hg, hg']
  | single x α =>
    induction α using DirectSum.Decomposition.inductionOn
        (IsDGRightModule.restrictScalarsGrading (ℳ := ℳ) f) with
    | zero => simp
    | @homogeneous q α =>
      have hα : (α : DGRightModule.RestrictScalars f M).val ∈ ℳ q := by
        have := (IsDGRightModule.mem_restrictScalarsGrading_iff (ℳ := ℳ) f).mp α.property
        rwa [DGRightModule.RestrictScalars.linearEquiv_apply] at this
      rw [m.coefficientDifferential_single (hM.restrictScalars f) x α.property,
        he x (α : DGRightModule.RestrictScalars f M),
        (m.map f).coefficientDifferential_single hM x hα]
      simp [he, map_finsuppSum, Units.smul_def, map_m, Finsupp.sum_mapRange_index]
    | add α β hα hβ => simp only [Finsupp.single_add, map_add, hα, hβ]

/-- The degree-`n` part of the identification of the two twisted complexes: the coordinatewise
identification of `P →₀ f^* M` with `P →₀ M`, on vectors of total degree `n`. -/
private def coefficientCochainComplexRestrictScalarsXEquiv (n : ℤ) :
    (m.coefficientCochainComplex (hM.restrictScalars f)).X n ≃ₗ[R]
      ((m.map f).coefficientCochainComplex hM).X n :=
  (m.coefficientCochainComplexXEquiv (hM.restrictScalars f) n).trans <|
    ((Finsupp.mapRange.linearEquiv (DGRightModule.RestrictScalars.linearEquiv f M)).ofSubmodules
      _ _ (by
        ext g
        rw [Submodule.mem_map_equiv, ← mapRange_linearEquiv_mem_rowFiniteTotalGrading_iff,
          LinearEquiv.apply_symm_apply])).trans
      ((m.map f).coefficientCochainComplexXEquiv hM n).symm

private theorem coefficientCochainComplexXEquiv_restrictScalarsXEquiv (n : ℤ)
    (g : (m.coefficientCochainComplex (hM.restrictScalars f)).X n) :
    ((m.map f).coefficientCochainComplexXEquiv hM n
        (m.coefficientCochainComplexRestrictScalarsXEquiv f hM n g) : P →₀ M) =
      Finsupp.mapRange.linearEquiv (DGRightModule.RestrictScalars.linearEquiv f M)
        (m.coefficientCochainComplexXEquiv (hM.restrictScalars f) n g) := by
  simp [coefficientCochainComplexRestrictScalarsXEquiv]

/-- **The twisted complex of a restricted module.** For a DG algebra morphism `f`, the row-finite
twisted complex of the restriction of scalars `f^* M` with the cocycle `m` is isomorphic to the
row-finite twisted complex of `M` with the image cocycle `f ∘ m`, through the coordinatewise
identification of the coefficient vectors. -/
def coefficientCochainComplexRestrictScalarsIso :
    m.coefficientCochainComplex (hM.restrictScalars f) ≅ (m.map f).coefficientCochainComplex hM :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n ↦ (m.coefficientCochainComplexRestrictScalarsXEquiv f hM n).toModuleIso)
    fun i j hij ↦ by
      obtain rfl : i + 1 = j := hij
      ext g
      apply ((m.map f).coefficientCochainComplexXEquiv hM (i + 1)).injective
      apply Subtype.ext
      simp only [ModuleCat.hom_comp, LinearMap.comp_apply, LinearEquiv.toModuleIso_hom,
        ModuleCat.hom_ofHom, LinearEquiv.coe_coe]
      rw [coefficientCochainComplexXEquiv_restrictScalarsXEquiv, coefficientCochainComplexXEquiv_d,
        coefficientCochainComplexXEquiv_d, coefficientCochainComplexXEquiv_restrictScalarsXEquiv,
        mapRange_linearEquiv_coefficientDifferential_restrictScalars]

/-- The components of the isomorphism of twisted complexes are the coordinatewise identification
of the coefficient vectors. -/
@[simp]
theorem coefficientCochainComplexXEquiv_restrictScalarsIso_hom_f_apply (n : ℤ)
    (g : (m.coefficientCochainComplex (hM.restrictScalars f)).X n) :
    ((m.map f).coefficientCochainComplexXEquiv hM n
        (((m.coefficientCochainComplexRestrictScalarsIso f hM).hom.f n).hom g) : P →₀ M) =
      Finsupp.mapRange.linearEquiv (DGRightModule.RestrictScalars.linearEquiv f M)
        (m.coefficientCochainComplexXEquiv (hM.restrictScalars f) n g) :=
  m.coefficientCochainComplexXEquiv_restrictScalarsXEquiv f hM n g

/-- The components of the inverse isomorphism of twisted complexes are the inverse coordinatewise
identification of the coefficient vectors. -/
@[simp]
theorem coefficientCochainComplexXEquiv_restrictScalarsIso_inv_f_apply (n : ℤ)
    (g : ((m.map f).coefficientCochainComplex hM).X n) :
    (m.coefficientCochainComplexXEquiv (hM.restrictScalars f) n
        (((m.coefficientCochainComplexRestrictScalarsIso f hM).inv.f n).hom g) :
          P →₀ DGRightModule.RestrictScalars f M) =
      (Finsupp.mapRange.linearEquiv (DGRightModule.RestrictScalars.linearEquiv f M)).symm
        ((m.map f).coefficientCochainComplexXEquiv hM n g) := by
  rw [LinearEquiv.eq_symm_apply, ← coefficientCochainComplexXEquiv_restrictScalarsIso_hom_f_apply,
    ← ModuleCat.comp_apply, ← HomologicalComplex.comp_f, Iso.inv_hom_id,
    HomologicalComplex.id_f, ModuleCat.id_apply]

end RowFiniteTwistingCocycle

/-! ### Continuation maps of a restricted module -/

namespace RowFiniteContinuationCocycle

section

variable {mP : RowFiniteTwistingCocycle 𝒜 dA P indP} {mQ : RowFiniteTwistingCocycle 𝒜 dA Q indQ}

/-- On coefficient vectors, the continuation map of a restricted module with the cocycle `ν` is
the continuation map of the original module with the image cocycle `f ∘ ν`. -/
theorem mapRange_linearEquiv_coefficientMap_restrictScalars (ν : RowFiniteContinuationCocycle mP mQ)
    (g : P →₀ DGRightModule.RestrictScalars f M) :
    Finsupp.mapRange.linearEquiv (DGRightModule.RestrictScalars.linearEquiv f M)
        (ν.coefficientMap g) =
      (ν.map f).coefficientMap
        (Finsupp.mapRange.linearEquiv (DGRightModule.RestrictScalars.linearEquiv f M) g) := by
  classical
  induction g using Finsupp.induction_linear with
  | zero => simp
  | add g g' hg hg' => simp only [map_add, hg, hg']
  | single x α =>
    ext y
    simp

end

variable {P Q : Type uP} {indP : P → ℤ} {indQ : Q → ℤ}
  {mP : RowFiniteTwistingCocycle 𝒜 dA P indP} {mQ : RowFiniteTwistingCocycle 𝒜 dA Q indQ}
  (hM : IsDGRightModule hB ℳ dM)

/-- The isomorphism of twisted complexes of a restricted module is natural in the cocycle: it
intertwines the continuation map of `ν` with the continuation map of the image cocycle
`f ∘ ν`. -/
@[reassoc]
theorem continuationHom_comp_coefficientCochainComplexRestrictScalarsIso_hom
    (ν : RowFiniteContinuationCocycle mP mQ) :
    ν.continuationHom (hM.restrictScalars f) ≫
        (mQ.coefficientCochainComplexRestrictScalarsIso f hM).hom =
      (mP.coefficientCochainComplexRestrictScalarsIso f hM).hom ≫
        (ν.map f).continuationHom hM := by
  ext n x
  apply ((mQ.map f).coefficientCochainComplexXEquiv hM n).injective
  apply Subtype.ext
  simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply,
    RowFiniteTwistingCocycle.coefficientCochainComplexXEquiv_restrictScalarsIso_hom_f_apply,
    continuationHom_f_apply, mapRange_linearEquiv_coefficientMap_restrictScalars]

end RowFiniteContinuationCocycle

/-! ### Homotopies of a restricted module -/

namespace RowFiniteParametrizedCocycle

variable {mP : RowFiniteTwistingCocycle 𝒜 dA P indP} {mQ : RowFiniteTwistingCocycle 𝒜 dA Q indQ}
  {ν₀ ν₁ : RowFiniteContinuationCocycle mP mQ}

/-- On coefficient vectors, the homotopy of a restricted module with the parametrized cocycle `η`
is the homotopy of the original module with the image cocycle `f ∘ η`. -/
theorem mapRange_linearEquiv_coefficientHomotopy_restrictScalars
    (η : RowFiniteParametrizedCocycle ν₀ ν₁) (g : P →₀ DGRightModule.RestrictScalars f M) :
    Finsupp.mapRange.linearEquiv (DGRightModule.RestrictScalars.linearEquiv f M)
        (η.coefficientHomotopy (IsDGRightModule.restrictScalarsGrading (ℳ := ℳ) f) g) =
      (η.map f).coefficientHomotopy ℳ
        (Finsupp.mapRange.linearEquiv (DGRightModule.RestrictScalars.linearEquiv f M) g) := by
  classical
  induction g using Finsupp.induction_linear with
  | zero => simp
  | add g g' hg hg' => simp only [map_add, hg, hg']
  | single x α =>
    ext y
    simp [val_koszulTwist_restrictScalars]

end RowFiniteParametrizedCocycle

end Restrict

end TauCeti
