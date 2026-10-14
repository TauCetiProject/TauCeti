/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DG.Module.Right.Extension.Basic
public import TauCeti.Algebra.Homology.DG.Module.Right.Restriction.Functor

/-!
# Extension of scalars is left adjoint to restriction of scalars

For a morphism `f : A ⟶ B` of differential graded algebras, a right DG `A`-module `M` and a
right DG `B`-module `P`, morphisms of right DG `B`-modules `M ⊗_A B ⟶ P` correspond to
morphisms of right DG `A`-modules `M ⟶ f^* P`.  A morphism `g` out of the extension is sent to
`m ↦ g(m ⊗ 1)`, and a morphism `φ` into the restriction is sent to `m ⊗ b ↦ φ(m) b`.
Both directions preserve degrees and differentials, so this is a bijection of DG module
morphisms, natural in `M` and `P`.

On the bundled categories of right DG modules, extension of scalars is therefore a functor,
left adjoint to the restriction functor `TauCeti.DGRightModuleCat.restrictScalars f`.  The
construction follows Mathlib's `ModuleCat.extendRestrictScalarsAdj`, with the additional
grading and differential conditions of DG modules.  Both functors are underived.

## Main definitions

* `TauCeti.DGRightModuleHom.toRestrictScalars`: the morphism `m ↦ g(m ⊗ 1)` into the
  restriction attached to a morphism `g` out of the extension.
* `TauCeti.DGRightModuleHom.fromExtendScalars`: the morphism `m ⊗ b ↦ φ(m) b` out of the
  extension attached to a morphism `φ` into the restriction.
* `TauCeti.DGRightModuleHom.extendRestrictScalarsEquiv`: the resulting bijection.
* `TauCeti.DGRightModuleCat.extendScalars`: extension of scalars as a functor.
* `TauCeti.DGRightModuleCat.extendRestrictScalarsAdj`: extension of scalars is left adjoint to
  restriction of scalars.

## References

* B. Keller, *Deriving DG categories*, Sections 2 and 6.
-/

public section

open CategoryTheory MulOpposite DirectSum

namespace TauCeti

universe uR uA uB uM uN uP

variable {R : Type uR} {A : Type uA} {B : Type uB}
  [CommRing R] [Ring A] [Ring B] [Algebra R A] [Algebra R B]
  {𝒜 : ℤ → Submodule R A} {ℬ : ℤ → Submodule R B}
  [GradedAlgebra 𝒜] [GradedAlgebra ℬ]
  {dA : A →ₗ[R] A} {dB : B →ₗ[R] B}
  {hA : IsDGAlgebra 𝒜 dA} {hB : IsDGAlgebra ℬ dB}

namespace DGRightModuleHom

variable {M : Type uM} {N : Type uN} {P : Type uP}
  [AddCommGroup M] [Module R M] [Module Aᵐᵒᵖ M] [IsScalarTower R Aᵐᵒᵖ M]
  [AddCommGroup N] [Module R N] [Module Aᵐᵒᵖ N] [IsScalarTower R Aᵐᵒᵖ N]
  [AddCommGroup P] [Module R P] [Module Bᵐᵒᵖ P] [IsScalarTower R Bᵐᵒᵖ P]
  {ℳ : ℤ → Submodule R M} {𝒩 : ℤ → Submodule R N} {ℳP : ℤ → Submodule R P}
  [SetLike.GradedSMul (InternalGrading.ofDecomposition 𝒜).opposite.piece ℳ]
  [SetLike.GradedSMul (InternalGrading.ofDecomposition 𝒜).opposite.piece 𝒩]
  [SetLike.GradedSMul (InternalGrading.ofDecomposition ℬ).opposite.piece ℳP]
  [DirectSum.Decomposition ℳ] [DirectSum.Decomposition 𝒩] [DirectSum.Decomposition ℳP]
  {dM : M →ₗ[R] M} {dN : N →ₗ[R] N} {dP : P →ₗ[R] P}
  {hM : IsDGRightModule hA ℳ dM} {hN : IsDGRightModule hA 𝒩 dN}
  {hP : IsDGRightModule hB ℳP dP}

variable (f : DGAlgHom hA hB)

/-- The morphism `m ↦ g(m ⊗ 1)` of right DG `A`-modules `M ⟶ f^* P` attached to a morphism
`g : M ⊗_A B ⟶ P` of right DG `B`-modules. -/
noncomputable def toRestrictScalars (g : DGRightModuleHom (hM.extendScalars f) hP) :
    DGRightModuleHom hM (hP.restrictScalars f) where
  toFun m := DGRightModule.RestrictScalars.mk
    (g (BalancedTensorProduct.tmul R A m (DGAlgHom.CodomainBimodule.mk 1)))
  map_add' m m' := by
    apply DGRightModule.RestrictScalars.ext
    simp [BalancedTensorProduct.add_tmul]
  map_smul' a m := by
    apply DGRightModule.RestrictScalars.ext
    have h : (BalancedTensorProduct.tmul R A (a • m) (DGAlgHom.CodomainBimodule.mk 1) :
        DGRightModule.ExtendScalars f M) =
        op (f a.unop) • BalancedTensorProduct.tmul R A m (DGAlgHom.CodomainBimodule.mk 1) := by
      rw [BalancedTensorProduct.smul_tmul_right, ← op_unop a, BalancedTensorProduct.balance]
      congr 1
      ext
      simp
    simp only [RingHom.id_apply, DGRightModule.RestrictScalars.val_smul_eq, h, map_smul,
      AlgHom.op_apply_apply, GradedAlgHom.coe_toAlgHom, DGAlgHom.coe_toGradedAlgHom]
  map_mem' {q m} hm := by
    rw [IsDGRightModule.mem_restrictScalarsGrading_iff,
      DGRightModule.RestrictScalars.linearEquiv_apply]
    have h1 := IsDGRightModule.tmul_mem_extendScalarsGrading f hm
      (x := DGAlgHom.CodomainBimodule.mk 1) SetLike.GradedOne.one_mem
    rw [add_zero] at h1
    exact Graded.map_mem g h1
  map_d' m := by
    apply DGRightModule.RestrictScalars.ext
    simp only [LinearMap.coe_mk, AddHom.coe_mk, IsDGRightModule.val_restrictScalarsDifferential]
    rw [g.map_d, IsDGRightModule.extendScalarsDifferential_tmul_one]

/-- The morphism into the restriction evaluates the original morphism on `m ⊗ 1`. -/
@[simp]
theorem val_toRestrictScalars (g : DGRightModuleHom (hM.extendScalars f) hP) (m : M) :
    (g.toRestrictScalars f m).val =
      g (BalancedTensorProduct.tmul R A m (DGAlgHom.CodomainBimodule.mk 1)) := by
  rfl

/-- The right action `(y, b) ↦ y b` of `B` on `P`, as an `R`-bilinear map out of `P` and the
codomain bimodule. -/
private noncomputable def actRight : P →ₗ[R] DGAlgHom.CodomainBimodule f →ₗ[R] P :=
  LinearMap.mk₂ R (fun y x ↦ op x.val • y)
    (fun y y' x ↦ smul_add _ y y')
    (fun r y x ↦ smul_comm _ r y)
    (fun y x x' ↦ by simp only [DGAlgHom.CodomainBimodule.val_add, op_add, add_smul])
    (fun r y x ↦ by
      simp only [DGAlgHom.CodomainBimodule.val_smul, op_smul, smul_assoc])

private theorem actRight_apply (y : P) (x : DGAlgHom.CodomainBimodule f) :
    actRight f y x = op x.val • y := rfl

/-- The morphism `m ⊗ b ↦ φ(m) b` of right DG `B`-modules `M ⊗_A B ⟶ P` attached to a morphism
`φ : M ⟶ f^* P` of right DG `A`-modules. -/
noncomputable def fromExtendScalars (hP : IsDGRightModule hB ℳP dP)
    (φ : DGRightModuleHom hM (hP.restrictScalars f)) :
    DGRightModuleHom (hM.extendScalars f) hP :=
  let F : M →ₗ[R] DGAlgHom.CodomainBimodule f →ₗ[R] P :=
    actRight f ∘ₗ (DGRightModule.RestrictScalars.linearEquiv f P).toLinearMap ∘ₗ
      φ.toLinearMap.restrictScalars R
  have hF (m : M) (x : DGAlgHom.CodomainBimodule f) : F m x = op x.val • (φ m).val := by
    simp only [F, LinearMap.comp_apply, actRight_apply, LinearEquiv.coe_coe,
      DGRightModule.RestrictScalars.linearEquiv_apply, LinearMap.coe_restrictScalars,
      coe_toLinearMap]
  have hFb (a : A) (m : M) (x : DGAlgHom.CodomainBimodule f) :
      F (op a • m) x = F m (a • x) := by
    rw [hF, hF, map_smul, DGRightModule.RestrictScalars.val_op_smul,
      DGAlgHom.CodomainBimodule.val_smul_left, op_mul, mul_smul]
  have hFs (b : Bᵐᵒᵖ) (m : M) (x : DGAlgHom.CodomainBimodule f) :
      F m (b • x) = b • F m x := by
    rw [hF, hF, DGAlgHom.CodomainBimodule.val_smul_right, ← mul_smul, smul_eq_mul_unop, op_mul,
      op_unop]
  { toFun := BalancedTensorProduct.lift F hFb
    map_add' := map_add _
    map_smul' := BalancedTensorProduct.lift_smul_right Bᵐᵒᵖ F hFb hFs
    map_mem' {q z} hz := by
      simpa only [add_zero, LinearMap.coe_mk, AddHom.coe_mk] using
        IsDGRightModule.map_mem_of_mem_extendScalarsGrading f ℳP
        (BalancedTensorProduct.lift F hFb) 0 (fun {p r m x} hm hx ↦ by
          rw [BalancedTensorProduct.lift_tmul, hF, add_zero, add_comm]
          have hφ := Graded.map_mem φ hm
          rw [IsDGRightModule.mem_restrictScalarsGrading_iff,
            DGRightModule.RestrictScalars.linearEquiv_apply] at hφ
          exact SetLike.GradedSMul.smul_mem
            (((InternalGrading.ofDecomposition ℬ).op_mem_opposite_piece_iff r x.val).2
              (by rwa [InternalGrading.ofDecomposition_piece])) hφ) hz
    map_d' z := by
      have key : dP ∘ₗ BalancedTensorProduct.lift F hFb =
          BalancedTensorProduct.lift F hFb ∘ₗ hM.extendScalarsDifferential f := by
        refine BalancedTensorProduct.hom_ext fun m x ↦ ?_
        induction m using DirectSum.Decomposition.inductionOn ℳ with
        | zero => simp
        | add m m' hm hm' =>
          simp only [LinearMap.comp_apply, BalancedTensorProduct.add_tmul, map_add] at hm hm' ⊢
          rw [hm, hm']
        | @homogeneous q m =>
          have hφm : (φ m).val ∈ ℳP q := by
            simpa only [IsDGRightModule.mem_restrictScalarsGrading_iff,
              DGRightModule.RestrictScalars.linearEquiv_apply] using Graded.map_mem φ m.2
          have hd : dP (φ m).val = (φ (dM m)).val := by
            simpa only [IsDGRightModule.val_restrictScalarsDifferential] using
              congrArg DGRightModule.RestrictScalars.val (φ.map_d m)
          rw [LinearMap.comp_apply, LinearMap.comp_apply, BalancedTensorProduct.lift_tmul, hF,
            hP.leibniz hφm x.val, hd,
            IsDGRightModule.extendScalarsDifferential_tmul_of_mem f hM m.2, map_add,
            map_smul (BalancedTensorProduct.lift F hFb),
            BalancedTensorProduct.lift_tmul, BalancedTensorProduct.lift_tmul, hF, hF,
            DGAlgHom.val_codomainBimoduleDifferential, Units.smul_def, Int.cast_smul_eq_zsmul]
      exact LinearMap.congr_fun key z }

/-- The morphism out of the extension sends `m ⊗ b` to `φ(m) b`. -/
@[simp]
theorem fromExtendScalars_tmul (φ : DGRightModuleHom hM (hP.restrictScalars f)) (m : M)
    (x : DGAlgHom.CodomainBimodule f) :
    φ.fromExtendScalars f hP (BalancedTensorProduct.tmul R A m x) = op x.val • (φ m).val := by
  simp only [fromExtendScalars, coe_mk, LinearMap.coe_mk, AddHom.coe_mk,
    BalancedTensorProduct.lift_tmul, LinearMap.comp_apply, actRight_apply, LinearEquiv.coe_coe,
    DGRightModule.RestrictScalars.linearEquiv_apply, LinearMap.coe_restrictScalars,
    coe_toLinearMap]

/-- The morphism out of the extension is natural in the source module. -/
theorem fromExtendScalars_comp (φ : DGRightModuleHom hN (hP.restrictScalars f))
    (g : DGRightModuleHom hM hN) :
    (φ.comp g).fromExtendScalars f hP = (φ.fromExtendScalars f hP).comp (g.extendScalars f) := by
  ext z
  induction z using BalancedTensorProduct.induction_on with
  | ht m x => simp
  | ha z z' hz hz' => simp only [map_add, hz, hz']

/-- The morphism into the restriction is natural in the target module. -/
theorem toRestrictScalars_comp {Q : Type*} [AddCommGroup Q] [Module R Q] [Module Bᵐᵒᵖ Q]
    [IsScalarTower R Bᵐᵒᵖ Q] {ℳQ : ℤ → Submodule R Q}
    [SetLike.GradedSMul (InternalGrading.ofDecomposition ℬ).opposite.piece ℳQ]
    [DirectSum.Decomposition ℳQ] {dQ : Q →ₗ[R] Q} {hQ : IsDGRightModule hB ℳQ dQ}
    (k : DGRightModuleHom hP hQ) (g : DGRightModuleHom (hM.extendScalars f) hP) :
    (k.comp g).toRestrictScalars f = (k.restrictScalars f).comp (g.toRestrictScalars f) := by
  ext m
  simp

/-- **The extension–restriction bijection.**  Morphisms of right DG `B`-modules
`M ⊗_A B ⟶ P` correspond to morphisms of right DG `A`-modules `M ⟶ f^* P`, by restricting
along `m ↦ m ⊗ 1`. -/
noncomputable def extendRestrictScalarsEquiv (hM : IsDGRightModule hA ℳ dM)
    (hP : IsDGRightModule hB ℳP dP) :
    DGRightModuleHom (hM.extendScalars f) hP ≃ DGRightModuleHom hM (hP.restrictScalars f) where
  toFun g := g.toRestrictScalars f
  invFun φ := φ.fromExtendScalars f hP
  left_inv g := by
    ext z
    induction z using BalancedTensorProduct.induction_on with
    | ht m x =>
      rw [fromExtendScalars_tmul, val_toRestrictScalars, ← map_smul,
        BalancedTensorProduct.smul_tmul_right]
      congr 2
      ext
      simp
    | ha z z' hz hz' => simp only [map_add, hz, hz']
  right_inv φ := by
    ext m
    simp

@[simp]
theorem extendRestrictScalarsEquiv_apply (g : DGRightModuleHom (hM.extendScalars f) hP) :
    extendRestrictScalarsEquiv f hM hP g = g.toRestrictScalars f := by rfl

@[simp]
theorem extendRestrictScalarsEquiv_symm_apply
    (φ : DGRightModuleHom hM (hP.restrictScalars f)) :
    (extendRestrictScalarsEquiv f hM hP).symm φ = φ.fromExtendScalars f hP := by rfl

end DGRightModuleHom

namespace DGRightModuleCat

-- Exposed, like `restrictScalars`, so that elements of an extended object are balanced tensors.
/-- **Extension of scalars** along a DG algebra morphism `f : A ⟶ B`, as a functor from right
DG `A`-modules to right DG `B`-modules: `M ↦ M ⊗_A B` and `g ↦ g ⊗ 1`. -/
@[expose]
noncomputable def extendScalars (f : DGAlgHom hA hB) :
    DGRightModuleCat.{uR, uA, max uB uM} hA ⥤ DGRightModuleCat.{uR, uB, max uB uM} hB where
  obj M := of (M.isDGRightModule.extendScalars f)
  map g := g.extendScalars f
  map_id _ := DGRightModuleHom.extendScalars_id f
  map_comp g k := DGRightModuleHom.extendScalars_comp f k g

/-- **Extension of scalars is left adjoint to restriction of scalars** along a DG algebra
morphism. -/
noncomputable def extendRestrictScalarsAdj (f : DGAlgHom hA hB) :
    extendScalars.{uR, uA, uB, uM} f ⊣ restrictScalars.{uR, uA, uB, max uB uM} f :=
  Adjunction.mkOfHomEquiv
    { homEquiv M P := DGRightModuleHom.extendRestrictScalarsEquiv f M.isDGRightModule
        P.isDGRightModule
      homEquiv_naturality_left_symm g k := DGRightModuleHom.fromExtendScalars_comp f k g
      homEquiv_naturality_right g k := DGRightModuleHom.toRestrictScalars_comp f k g }

/-- The adjunction sends a morphism `g` out of `M ⊗_A B` to `m ↦ g(m ⊗ 1)`. -/
@[simp]
theorem extendRestrictScalarsAdj_homEquiv_apply (f : DGAlgHom hA hB)
    {M : DGRightModuleCat.{uR, uA, max uB uM} hA} {P : DGRightModuleCat.{uR, uB, max uB uM} hB}
    (g : (extendScalars f).obj M ⟶ P) :
    (extendRestrictScalarsAdj f).homEquiv M P g = g.toRestrictScalars f := by
  rw [extendRestrictScalarsAdj, Adjunction.mkOfHomEquiv_homEquiv]
  rfl

/-- The inverse of the adjunction sends a morphism `φ` into `f^* P` to `m ⊗ b ↦ φ(m) b`. -/
@[simp]
theorem extendRestrictScalarsAdj_homEquiv_symm_apply (f : DGAlgHom hA hB)
    {M : DGRightModuleCat.{uR, uA, max uB uM} hA} {P : DGRightModuleCat.{uR, uB, max uB uM} hB}
    (φ : M ⟶ (restrictScalars f).obj P) :
    ((extendRestrictScalarsAdj f).homEquiv M P).symm φ =
      DGRightModuleHom.fromExtendScalars f P.isDGRightModule φ := by
  rw [extendRestrictScalarsAdj, Adjunction.mkOfHomEquiv_homEquiv]
  rfl

end DGRightModuleCat

end TauCeti
