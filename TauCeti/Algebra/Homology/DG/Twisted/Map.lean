/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DG.Twisted.Complex
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

## Main definitions

* `TauCeti.TwistingCocycle.map`: the image of a twisting cocycle under a DG algebra morphism.
* `TauCeti.TwistingCocycle.twistedCochainComplexRestrictScalarsIso`: the isomorphism between the
  twisted complex of a restricted module and the twisted complex of the image cocycle.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §2.3.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, Remark 4.6.
-/

public section

open MulOpposite

namespace TauCeti

universe uR uA uB uM uP

variable {R : Type uR} {A : Type uA} {B : Type uB}
  [CommRing R] [Ring A] [Ring B] [Algebra R A] [Algebra R B]
  {𝒜 : ℤ → Submodule R A} {ℬ : ℤ → Submodule R B}
  [GradedAlgebra 𝒜] [GradedAlgebra ℬ]
  {dA : A →ₗ[R] A} {dB : B →ₗ[R] B}
  {hA : IsDGAlgebra 𝒜 dA} {hB : IsDGAlgebra ℬ dB}
  {P : Type uP} [Fintype P] {ind : P → ℤ}

namespace TwistingCocycle

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

section Restrict

variable {M : Type uM} [AddCommGroup M] [Module R M] [Module Bᵐᵒᵖ M]
  [IsScalarTower R Bᵐᵒᵖ M]
  {ℳ : ℤ → Submodule R M} [DirectSum.Decomposition ℳ]
  [SetLike.GradedSMul (InternalGrading.ofDecomposition ℬ).opposite.piece ℳ]
  {dM : M →ₗ[R] M} (f : DGAlgHom hA hB)

variable (m : P → P → A)

omit [SetLike.GradedSMul (InternalGrading.ofDecomposition ℬ).opposite.piece ℳ] in
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

omit [Fintype P] [Module Bᵐᵒᵖ M] [IsScalarTower R Bᵐᵒᵖ M]
  [SetLike.GradedSMul (InternalGrading.ofDecomposition ℬ).opposite.piece ℳ] in
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

namespace TwistingCocycle

variable (m : TwistingCocycle 𝒜 dA P ind) (hM : IsDGRightModule hB ℳ dM)

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

end Restrict

end TauCeti
