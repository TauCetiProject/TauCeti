/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DG.Bimodule.Codomain
public import TauCeti.Algebra.Homology.DG.Bimodule.TensorProduct
public import TauCeti.Algebra.Homology.DG.Module.Right.Hom.Basic

/-!
# Extension of scalars for differential graded right modules

A morphism `f : A ⟶ B` of differential graded algebras turns every right DG `A`-module `M` into
the right DG `B`-module `M ⊗_A B`.  Here `B` is the DG `(A, B)`-bimodule
`TauCeti.DGAlgHom.CodomainBimodule f`, on which `A` acts on the left through `f`, and the tensor
product is the ordinary balanced tensor product.  Its grading is the total grading
`|m ⊗ b| = |m| + |b|`, its differential is
`d(m ⊗ b) = dM(m) ⊗ b + (-1)^|m| m ⊗ dB(b)`, and `B` acts by `(m ⊗ b) b' = m ⊗ b b'`.

A morphism of right DG `A`-modules `g` induces the morphism `g ⊗ 1` of extensions, and this
preserves identities and composition.  Extension of scalars is underived: no flatness or
cofibrancy hypothesis is needed.

## Main definitions

* `TauCeti.DGRightModule.ExtendScalars`: the carrier `M ⊗_A B` of the extended module.
* `TauCeti.IsDGRightModule.extendScalarsGrading`: its total grading.
* `TauCeti.IsDGRightModule.extendScalarsDifferential`: its tensor differential.
* `TauCeti.IsDGRightModule.extendScalars`: the extended right DG `B`-module.
* `TauCeti.DGRightModuleHom.extendScalars`: extension of a morphism of right DG modules.

## References

* B. Keller, *Deriving DG categories*, Sections 2 and 6.1.
-/

public section

open MulOpposite DirectSum

namespace TauCeti

universe uR uA uB uM uN uP

variable {R : Type uR} {A : Type uA} {B : Type uB}
  [CommRing R] [Ring A] [Ring B] [Algebra R A] [Algebra R B]
  {𝒜 : ℤ → Submodule R A} {ℬ : ℤ → Submodule R B}
  [GradedAlgebra 𝒜] [GradedAlgebra ℬ]
  {dA : A →ₗ[R] A} {dB : B →ₗ[R] B}
  {hA : IsDGAlgebra 𝒜 dA} {hB : IsDGAlgebra ℬ dB}

-- The tensor grading is stated for packaged gradings; transport the actions to them.
local instance {M : Type*} [AddCommGroup M] [Module R M] [Module Aᵐᵒᵖ M]
    {ℳ : ℤ → Submodule R M} [DirectSum.Decomposition ℳ]
    [SetLike.GradedSMul (InternalGrading.ofDecomposition 𝒜).opposite.piece ℳ] :
    SetLike.GradedSMul (InternalGrading.ofDecomposition 𝒜).opposite.piece
      (InternalGrading.ofDecomposition ℳ).piece := by
  rw [InternalGrading.ofDecomposition_piece]
  infer_instance

local instance (f : DGAlgHom hA hB) : SetLike.GradedSMul 𝒜
    (InternalGrading.ofDecomposition (DGAlgHom.codomainBimoduleGrading f)).piece := by
  rw [InternalGrading.ofDecomposition_piece]
  infer_instance

local instance (f : DGAlgHom hA hB) :
    SetLike.GradedSMul (InternalGrading.ofDecomposition ℬ).opposite.piece
      (InternalGrading.ofDecomposition (DGAlgHom.codomainBimoduleGrading f)).piece := by
  rw [InternalGrading.ofDecomposition_piece]
  infer_instance

namespace DGRightModule

/-- The carrier `M ⊗_A B` of the extension of scalars of a right `A`-module `M` along a DG
algebra morphism `f : A ⟶ B`: the balanced tensor product of `M` with the codomain bimodule
of `f`. -/
abbrev ExtendScalars (f : DGAlgHom hA hB) (M : Type uM)
    [AddCommGroup M] [Module R M] [Module Aᵐᵒᵖ M] : Type (max uM uB) :=
  BalancedTensorProduct R A M (DGAlgHom.CodomainBimodule f)

namespace ExtendScalars

variable (f : DGAlgHom hA hB) (M : Type uM)
  [AddCommGroup M] [Module R M] [Module Aᵐᵒᵖ M]

/-- The right `B`-action on `M ⊗_A B`, by right multiplication on the second factor. -/
instance : Module Bᵐᵒᵖ (ExtendScalars f M) :=
  BalancedTensorProduct.rightModule (k := R) (A := A) (M := M)
    (N := DGAlgHom.CodomainBimodule f) Bᵐᵒᵖ

instance : IsScalarTower R Bᵐᵒᵖ (ExtendScalars f M) :=
  BalancedTensorProduct.rightIsScalarTower (k := R) (A := A) (M := M)
    (N := DGAlgHom.CodomainBimodule f) Bᵐᵒᵖ

end ExtendScalars

end DGRightModule

namespace IsDGRightModule

variable {M : Type uM} [AddCommGroup M] [Module R M] [Module Aᵐᵒᵖ M]
  [IsScalarTower R Aᵐᵒᵖ M]
  {ℳ : ℤ → Submodule R M}
  [SetLike.GradedSMul (InternalGrading.ofDecomposition 𝒜).opposite.piece ℳ]
  [DirectSum.Decomposition ℳ]
  {dM : M →ₗ[R] M}

variable (f : DGAlgHom hA hB)

/-- The grading of the extended module `M ⊗_A B`: the total grading of the balanced tensor
product, with `|m ⊗ b| = |m| + |b|`. -/
noncomputable def extendScalarsGrading (q : ℤ) :
    Submodule R (DGRightModule.ExtendScalars f M) :=
  (BalancedTensorProduct.grading (𝒜 := 𝒜) (InternalGrading.ofDecomposition ℳ)
    (InternalGrading.ofDecomposition (DGAlgHom.codomainBimoduleGrading f))).piece q

/- The grading is by definition the grading of an `InternalGrading`, which carries a
decomposition; we read the instance off that definition. -/
/-- The total grading of the extended module is a direct-sum decomposition. -/
noncomputable instance : DirectSum.Decomposition (extendScalarsGrading (ℳ := ℳ) f) :=
  inferInstanceAs (DirectSum.Decomposition
    (BalancedTensorProduct.grading (𝒜 := 𝒜) (InternalGrading.ofDecomposition ℳ)
      (InternalGrading.ofDecomposition (DGAlgHom.codomainBimoduleGrading f))).piece)

/-- The right `B`-action on the extended module adds degrees. -/
instance : SetLike.GradedSMul (InternalGrading.ofDecomposition ℬ).opposite.piece
    (extendScalarsGrading (ℳ := ℳ) f) :=
  BalancedTensorProduct.gradedSMul_right (𝒜 := 𝒜) (InternalGrading.ofDecomposition ℳ)
    (InternalGrading.ofDecomposition (DGAlgHom.codomainBimoduleGrading f)) Bᵐᵒᵖ
    (InternalGrading.ofDecomposition ℬ).opposite.piece

omit [IsScalarTower R Aᵐᵒᵖ M] in
/-- Degrees add on homogeneous pure tensors of the extended module. -/
theorem tmul_mem_extendScalarsGrading {p q : ℤ} {m : M} {x : DGAlgHom.CodomainBimodule f}
    (hm : m ∈ ℳ p) (hx : x.val ∈ ℬ q) :
    BalancedTensorProduct.tmul R A m x ∈ extendScalarsGrading (ℳ := ℳ) f (p + q) :=
  BalancedTensorProduct.tmul_mem_grading (𝒜 := 𝒜) _ _
    (by rwa [InternalGrading.ofDecomposition_piece])
    (by rwa [InternalGrading.ofDecomposition_piece, DGAlgHom.mem_codomainBimoduleGrading_iff])

omit [IsScalarTower R Aᵐᵒᵖ M] in
/-- A linear map out of the extended module shifts degrees by `s` as soon as it does so on
homogeneous pure tensors. -/
theorem map_mem_of_mem_extendScalarsGrading {Q : Type*} [AddCommGroup Q] [Module R Q]
    (𝓠 : ℤ → Submodule R Q) (F : DGRightModule.ExtendScalars f M →ₗ[R] Q) (s : ℤ)
    (hF : ∀ {p q : ℤ} {m : M} {x : DGAlgHom.CodomainBimodule f},
      m ∈ ℳ p → x.val ∈ ℬ q → F (BalancedTensorProduct.tmul R A m x) ∈ 𝓠 (p + q + s))
    {p : ℤ} {z : DGRightModule.ExtendScalars f M}
    (hz : z ∈ extendScalarsGrading (ℳ := ℳ) f p) : F z ∈ 𝓠 (p + s) :=
  BalancedTensorProduct.map_mem_of_tmul (𝒜 := 𝒜) _ _ 𝓠 F s
    (fun hm hx ↦ hF (by rwa [InternalGrading.ofDecomposition_piece] at hm)
      (by rwa [InternalGrading.ofDecomposition_piece,
        DGAlgHom.mem_codomainBimoduleGrading_iff] at hx)) hz

/-- The differential of the extended module `M ⊗_A B`: the balanced tensor differential
`d(m ⊗ b) = dM(m) ⊗ b + (-1)^|m| m ⊗ dB(b)`. -/
noncomputable def extendScalarsDifferential (hM : IsDGRightModule hA ℳ dM) :
    DGRightModule.ExtendScalars f M →ₗ[R] DGRightModule.ExtendScalars f M :=
  BalancedTensorProduct.differential hM
    (DGAlgHom.isDGBimodule_codomainBimodule f).toIsDGLeftModule

/-- The differential of the extended module on a pure tensor with homogeneous first factor. -/
theorem extendScalarsDifferential_tmul_of_mem (hM : IsDGRightModule hA ℳ dM) {q : ℤ} {m : M}
    (hm : m ∈ ℳ q) (x : DGAlgHom.CodomainBimodule f) :
    hM.extendScalarsDifferential f (BalancedTensorProduct.tmul R A m x) =
      BalancedTensorProduct.tmul R A (dM m) x +
        ((q.negOnePow : ℤ) : R) • BalancedTensorProduct.tmul R A m
          (DGAlgHom.codomainBimoduleDifferential f x) :=
  BalancedTensorProduct.differential_tmul_of_mem hM _ hm x

/-- The extended differential of `m ⊗ 1` is `dM(m) ⊗ 1`, since the unit of `B` is a cycle. -/
@[simp]
theorem extendScalarsDifferential_tmul_one (hM : IsDGRightModule hA ℳ dM) (m : M) :
    hM.extendScalarsDifferential f
        (BalancedTensorProduct.tmul R A m (DGAlgHom.CodomainBimodule.mk 1)) =
      BalancedTensorProduct.tmul R A (dM m) (DGAlgHom.CodomainBimodule.mk 1) := by
  rw [extendScalarsDifferential, BalancedTensorProduct.differential_tmul]
  have h : DGAlgHom.codomainBimoduleDifferential f (DGAlgHom.CodomainBimodule.mk 1) = 0 :=
    DGAlgHom.CodomainBimodule.ext (by
      rw [DGAlgHom.val_codomainBimoduleDifferential, hB.map_one_eq_zero,
        DGAlgHom.CodomainBimodule.val_zero])
  simp only [h, BalancedTensorProduct.tmul_zero, add_zero]

/-- **Extension of scalars.**  For a DG algebra morphism `f : A ⟶ B` and a right DG
`A`-module `M`, the balanced tensor product `M ⊗_A B` is a right DG `B`-module. -/
theorem extendScalars (hM : IsDGRightModule hA ℳ dM) :
    IsDGRightModule hB (extendScalarsGrading (ℳ := ℳ) f) (hM.extendScalarsDifferential f) :=
  BalancedTensorProduct.isDGRightModule_tensorProduct hM
    (DGAlgHom.isDGBimodule_codomainBimodule f)

end IsDGRightModule

namespace DGRightModuleHom

variable {M : Type uM} {N : Type uN} {P : Type uP}
  [AddCommGroup M] [Module R M] [Module Aᵐᵒᵖ M] [IsScalarTower R Aᵐᵒᵖ M]
  [AddCommGroup N] [Module R N] [Module Aᵐᵒᵖ N] [IsScalarTower R Aᵐᵒᵖ N]
  [AddCommGroup P] [Module R P] [Module Aᵐᵒᵖ P] [IsScalarTower R Aᵐᵒᵖ P]
  {ℳ : ℤ → Submodule R M} {𝒩 : ℤ → Submodule R N} {ℳP : ℤ → Submodule R P}
  [SetLike.GradedSMul (InternalGrading.ofDecomposition 𝒜).opposite.piece ℳ]
  [SetLike.GradedSMul (InternalGrading.ofDecomposition 𝒜).opposite.piece 𝒩]
  [SetLike.GradedSMul (InternalGrading.ofDecomposition 𝒜).opposite.piece ℳP]
  [DirectSum.Decomposition ℳ] [DirectSum.Decomposition 𝒩] [DirectSum.Decomposition ℳP]
  {dM : M →ₗ[R] M} {dN : N →ₗ[R] N} {dP : P →ₗ[R] P}
  {hM : IsDGRightModule hA ℳ dM} {hN : IsDGRightModule hA 𝒩 dN}
  {hP : IsDGRightModule hA ℳP dP}

variable (f : DGAlgHom hA hB)

/-- **Extension of scalars of a morphism.**  A morphism `g : M ⟶ N` of right DG `A`-modules
induces the morphism `g ⊗ 1 : M ⊗_A B ⟶ N ⊗_A B` of right DG `B`-modules. -/
noncomputable def extendScalars (g : DGRightModuleHom hM hN) :
    DGRightModuleHom (hM.extendScalars f) (hN.extendScalars f) where
  toLinearMap :=
    { toFun := BalancedTensorProduct.map (A := A) (g.toLinearMap.restrictScalars R)
        (LinearMap.id : DGAlgHom.CodomainBimodule f →ₗ[R] DGAlgHom.CodomainBimodule f)
        (fun a m ↦ map_smul g (op a) m) (fun _ _ ↦ rfl)
      map_add' := map_add _
      map_smul' := BalancedTensorProduct.map_smul_right Bᵐᵒᵖ _ _ _ _ (fun _ _ ↦ rfl) }
  map_mem' {q x} hx := by
    have hg₀ : LinearMap.IsHomogeneous (g.toLinearMap.restrictScalars R)
        (InternalGrading.ofDecomposition ℳ).piece (InternalGrading.ofDecomposition 𝒩).piece 0 :=
      LinearMap.isHomogeneous_def.2 fun _ _ hx ↦ by
        rw [InternalGrading.ofDecomposition_piece] at hx ⊢
        simpa only [add_zero, LinearMap.coe_restrictScalars, coe_toLinearMap] using
          Graded.map_mem g hx
    simpa only [add_zero, IsDGRightModule.extendScalarsGrading, LinearMap.coe_mk,
      AddHom.coe_mk] using
      (BalancedTensorProduct.isHomogeneous_map (𝒜 := 𝒜) _ _ _ _ _ _ _ _ hg₀
        (LinearMap.isHomogeneous_id _)).map_mem hx
  map_d' x := by
    have hg₀ : LinearMap.IsHomogeneous (g.toLinearMap.restrictScalars R) ℳ 𝒩 0 :=
      LinearMap.isHomogeneous_def.2 fun _ _ hx ↦ by
        simpa only [add_zero, LinearMap.coe_restrictScalars, coe_toLinearMap] using
          Graded.map_mem g hx
    simp only [IsDGRightModule.extendScalarsDifferential, LinearMap.coe_mk, AddHom.coe_mk]
    have h := BalancedTensorProduct.differential_naturality hM
      (DGAlgHom.isDGBimodule_codomainBimodule f).toIsDGLeftModule hN
      (DGAlgHom.isDGBimodule_codomainBimodule f).toIsDGLeftModule _ LinearMap.id
      (fun a m ↦ map_smul g (op a) m) (fun _ _ ↦ rfl) hg₀ (LinearMap.ext g.map_d) rfl
    exact LinearMap.congr_fun h x

/-- Extension of scalars of a morphism acts on the first factor of a pure tensor. -/
@[simp]
theorem extendScalars_tmul (g : DGRightModuleHom hM hN) (m : M)
    (x : DGAlgHom.CodomainBimodule f) :
    g.extendScalars f (BalancedTensorProduct.tmul R A m x) =
      BalancedTensorProduct.tmul R A (g m) x :=
  BalancedTensorProduct.map_tmul _ _ _ _ m x

/-- Extension of scalars preserves identity morphisms. -/
@[simp]
theorem extendScalars_id :
    (DGRightModuleHom.id hM).extendScalars f = DGRightModuleHom.id (hM.extendScalars f) := by
  have h : (DGRightModuleHom.id hM).toLinearMap.restrictScalars R = LinearMap.id :=
    LinearMap.ext (id_apply hM)
  ext z
  simp only [extendScalars, h, id_apply]
  exact LinearMap.congr_fun BalancedTensorProduct.map_id z

/-- Extension of scalars preserves composition. -/
@[simp]
theorem extendScalars_comp (g : DGRightModuleHom hN hP) (k : DGRightModuleHom hM hN) :
    (g.comp k).extendScalars f = (g.extendScalars f).comp (k.extendScalars f) := by
  have h : (g.comp k).toLinearMap.restrictScalars R =
      g.toLinearMap.restrictScalars R ∘ₗ k.toLinearMap.restrictScalars R :=
    LinearMap.ext (comp_apply g k)
  ext z
  simp only [extendScalars, h, comp_apply]
  exact LinearMap.congr_fun (BalancedTensorProduct.map_comp (A := A)
    (k.toLinearMap.restrictScalars R) LinearMap.id (g.toLinearMap.restrictScalars R)
    LinearMap.id _ (fun _ _ ↦ rfl) _ (fun _ _ ↦ rfl)) z

end DGRightModuleHom

end TauCeti
