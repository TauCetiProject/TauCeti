/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Algebra.ComplexSmoothFunctions
public import TauCeti.Geometry.Manifold.VectorBundle.Complexification
public import TauCeti.Geometry.Manifold.VectorBundle.Section.Module

/-!
# Sections of complex vector bundles as modules over complex-valued smooth functions

Let `W` be a complex vector bundle over a real manifold `M`. Its `C^n` sections form a module
over the ring `C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯` of complex-valued real `C^n` functions, acting by
pointwise multiplication `(f • s) x = f x • s x`. Smoothness of `f • s` comes from
`ContMDiff.smul_totalSpace`: in a complex-linear trivialization, multiplication by a complex
scalar is a smooth map of the real model fibre.

This module structure extends both scalar actions already present on sections. Constant
functions act by the complex scalar action (`ContMDiffSection.complexSmoothConstants_smul`), and
real-valued functions act by the real smooth-function action of `Section/Module.lean`
(`ContMDiffSection.ofReal_smul`). Writing `f = u + i v` with real `u` and `v`, the action is
`f • s = u • s + v • (i • s)`, where `s ↦ i • s` is the fibrewise complex structure
(`ContMDiffSection.complexFunction_smul_eq_re_smul_add_im_smul`). The action commutes with
pullback and with restriction to open subsets.

For the complexification `ℂ ⊗[ℝ] E` of a real bundle `E`, the real and imaginary parts of
`f • σ` are computed from those of `σ` by complex multiplication, and the canonical
isomorphism `ℂ ⊗[ℝ] Cₛ^n⟮I; F, E⟯ ≃ Cₛ^n⟮I; Complexification F, ℂ ⊗[ℝ] E⟯` intertwines the real
function actions on both sides. Applied to the tangent bundle, this makes complex vector fields,
the sections of `ℂ ⊗[ℝ] TM`, a module over `C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯` whose real and imaginary parts
are pairs of real vector fields.

No dimension, compactness or boundary hypotheses are needed.

## References

* I. Kolář, P. W. Michor, J. Slovák, *Natural Operations in Differential Geometry*, Springer
  (1993), §§1.2 and 10.
* D. Huybrechts, *Complex Geometry: An Introduction*, Springer (2005), §1.2.
-/

public section

noncomputable section

open Bundle TopologicalSpace
open scoped Manifold ContDiff TensorProduct

namespace ContMDiffSection

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] {n : ℕ∞ω}
  {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedSpace ℂ G] [IsScalarTower ℝ ℂ G]
  {W : M → Type*} [∀ x, AddCommGroup (W x)] [∀ x, Module ℂ (W x)]
  [∀ x, TopologicalSpace (W x)] [TopologicalSpace (TotalSpace G W)] [FiberBundle G W]
  [VectorBundle ℂ G W]

section Module

-- Smoothness of the product is `ContMDiff.smul_totalSpace` for complex scalars.
/-- Complex-valued `C^n` functions on a real manifold act on `C^n` sections of a complex vector
bundle by pointwise multiplication. -/
instance instSMulComplexContMDiffMap : SMul C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ Cₛ^n⟮I; G, W⟯ :=
  ⟨fun f s ↦ ⟨fun x ↦ f x • s x, f.contMDiff.smul_totalSpace s.contMDiff⟩⟩

/-- Evaluation of complex smooth-function multiplication is fibrewise complex multiplication. -/
@[simp]
theorem complexFunction_smul_apply (f : C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯) (s : Cₛ^n⟮I; G, W⟯) (x : M) :
    (f • s) x = f x • s x := (rfl)

variable [∀ x, Module ℝ (W x)] [VectorBundle ℝ G W]

/-- Sections of a complex vector bundle form a module over the complex-valued functions of the
same regularity. -/
instance instModuleComplexContMDiffMap : Module C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ Cₛ^n⟮I; G, W⟯ where
  smul_add f s t := by ext x; simp [smul_add]
  add_smul f g s := by ext x; simp [add_smul]
  mul_smul f g s := by ext x; simp [mul_smul]
  one_smul s := by ext x; simp
  zero_smul s := by ext x; simp
  smul_zero f := by ext x; simp

/-- Complex scalars and complex smooth functions form a tower on sections. -/
instance instIsScalarTowerComplexContMDiffMap :
    IsScalarTower ℂ C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ Cₛ^n⟮I; G, W⟯ where
  smul_assoc z f s := by ext x; simp [mul_smul]

/-- Complex scalar multiplication commutes with complex smooth-function multiplication. -/
instance instSMulCommClassComplexContMDiffMap :
    SMulCommClass ℂ C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ Cₛ^n⟮I; G, W⟯ where
  smul_comm z f s := by ext x; simp [smul_comm z (f x)]

variable [∀ x, IsScalarTower ℝ ℂ (W x)]

/-- Real scalars and complex smooth functions form a tower on sections. -/
instance instIsScalarTowerRealComplexContMDiffMap :
    IsScalarTower ℝ C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ Cₛ^n⟮I; G, W⟯ where
  smul_assoc r f s := by
    ext x
    simp only [complexFunction_smul_apply, ContMDiffMap.coe_smul, Pi.smul_apply, coe_smul]
    exact smul_assoc r (f x) (s x)

/-- Real scalar multiplication commutes with complex smooth-function multiplication. -/
instance instSMulCommClassRealComplexContMDiffMap :
    SMulCommClass ℝ C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ Cₛ^n⟮I; G, W⟯ where
  smul_comm r f s := by ext x; simp [smul_comm r (f x)]

end Module

section Pullback

variable {E' H' N : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  [TopologicalSpace N] [ChartedSpace H' N]

/-- Pullback intertwines complex smooth-function multiplication with composition of
functions. -/
@[simp]
theorem pullback_smul_complexFunction (f : C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯) (s : Cₛ^n⟮I; G, W⟯)
    (g : C^n⟮I', N; I, M⟯) :
    (f • s).pullback g = f.comp g • s.pullback g := by
  ext x
  simp only [ContinuousMap.coe_ofClass, pullback_apply, complexFunction_smul_apply,
    ContMDiffMap.comp_apply]
  -- The sides differ only in how the pullback fibre `W (g x)` is written.
  exact rfl

/-- Restriction intertwines complex smooth-function multiplication with restriction of
functions. -/
@[simp]
theorem restrict_smul_complexFunction (f : C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯) (s : Cₛ^n⟮I; G, W⟯)
    (U : Opens M) :
    (f • s).restrict U =
      f.comp (⟨Subtype.val, contMDiff_subtype_val⟩ : C^n⟮I, U; I, M⟯) • s.restrict U := by
  ext x
  exact (restrict_apply (f • s) U x).trans (congrArg (f x • ·) (restrict_apply s U x).symm)

end Pullback

variable [∀ x, Module ℝ (W x)] [VectorBundle ℝ G W]

section Constants

/-- A constant complex function acts on sections by the complex scalar action. -/
@[simp]
theorem complexSmoothConstants_smul (z : ℂ) (s : Cₛ^n⟮I; G, W⟯) :
    TauCeti.complexSmoothConstants (I := I) (M := M) (n := n) z • s = z • s := by
  ext x; simp

variable [∀ x, IsScalarTower ℝ ℂ (W x)]

/-- A real-valued function acts on sections of a complex bundle through its inclusion into the
complex-valued functions. -/
@[simp]
theorem ofReal_smul (f : C^n⟮I, M; ℝ⟯) (s : Cₛ^n⟮I; G, W⟯) :
    ContMDiffMap.ofReal f • s = f • s := by
  ext x
  simp only [complexFunction_smul_apply, ContMDiffMap.ofReal_apply, smul_apply]
  exact (RCLike.real_smul_eq_coe_smul (K := ℂ) (f x) (s x)).symm

/-- Splitting a complex function `f = u + i v` into real and imaginary parts splits its action:
`f • s = u • s + v • (i • s)`, where `i • s` is the fibrewise complex structure applied to `s`. -/
theorem complexFunction_smul_eq_re_smul_add_im_smul (f : C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯)
    (s : Cₛ^n⟮I; G, W⟯) :
    f • s = f.re • s + f.im • (Complex.I • s) := by
  ext x
  simp only [complexFunction_smul_apply, coe_add, Pi.add_apply, smul_apply,
    coe_smul_of_normedAlgebra, Pi.smul_apply, ContMDiffMap.re_apply, ContMDiffMap.im_apply]
  conv_lhs => rw [← Complex.re_add_im (f x)]
  rw [add_smul, mul_smul]
  congr 1 <;> exact (RCLike.real_smul_eq_coe_smul (K := ℂ) _ _).symm

end Constants

section Complexification

open TauCeti

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [TopologicalSpace (TotalSpace F V)] [∀ x, TopologicalSpace (V x)] [FiberBundle F V]
  [VectorBundle ℝ F V] [∀ x, TopologicalSpace (ℂ ⊗[ℝ] V x)]
  [∀ x, IsComplexificationTopology (V x)]

/-- The real part of `f • σ` for a complexified section `σ` is
`re f • re σ - im f • im σ`. -/
@[simp]
theorem realPartLinearMap_complexFunction_smul (f : C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯)
    (σ : Cₛ^n⟮I; Complexification F, fun x ↦ ℂ ⊗[ℝ] V x⟯) :
    realPartLinearMap I F n V (f • σ) =
      f.re • realPartLinearMap I F n V σ - f.im • imaginaryPartLinearMap I F n V σ := by
  ext x; simp

/-- The imaginary part of `f • σ` for a complexified section `σ` is
`re f • im σ + im f • re σ`. -/
@[simp]
theorem imaginaryPartLinearMap_complexFunction_smul (f : C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯)
    (σ : Cₛ^n⟮I; Complexification F, fun x ↦ ℂ ⊗[ℝ] V x⟯) :
    imaginaryPartLinearMap I F n V (f • σ) =
      f.re • imaginaryPartLinearMap I F n V σ + f.im • realPartLinearMap I F n V σ := by
  ext x; simp

/-- Multiplying the complexification `1 ⊗ s` of a real section by `f = u + i v` gives
`1 ⊗ (u • s) + i ⊗ (v • s)`. -/
theorem complexFunction_smul_oneTmulLinearMap (f : C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯)
    (s : Cₛ^n⟮I; F, V⟯) :
    f • oneTmulLinearMap I F n V s =
      oneTmulLinearMap I F n V (f.re • s) + ITmulLinearMap I F n V (f.im • s) := by
  ext x
  simp only [complexFunction_smul_apply, oneTmulLinearMap_apply, coe_add, Pi.add_apply,
    smul_apply, ContMDiffMap.re_apply, ContMDiffMap.im_apply, ITmulLinearMap_apply,
    TensorProduct.tmul_smul, TensorProduct.smul_tmul']
  rw [← TensorProduct.add_tmul]
  congr 1
  apply Complex.ext <;> simp

/-- The canonical isomorphism `ℂ ⊗[ℝ] Cₛ^n⟮I; F, V⟯ ≃ Cₛ^n⟮I; Complexification F, ℂ ⊗[ℝ] V⟯`
intertwines the real function action on the right tensor factor with the action of real
functions viewed as complex-valued functions. -/
@[simp]
theorem complexificationEquiv_tmul_smul (z : ℂ) (f : C^n⟮I, M; ℝ⟯) (s : Cₛ^n⟮I; F, V⟯) :
    complexificationEquiv I F n V (z ⊗ₜ[ℝ] (f • s)) =
      ContMDiffMap.ofReal f • complexificationEquiv I F n V (z ⊗ₜ[ℝ] s) := by
  ext x
  simp [TensorProduct.smul_tmul', TensorProduct.tmul_smul]

end Complexification

end ContMDiffSection
