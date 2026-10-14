/-
Copyright (c) 2026 Wentao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wentao Li
-/
module

public import TauCeti.Algebra.Homology.Curved.Module.Right.DGCategory
public import TauCeti.CategoryTheory.DG.Preadditive

/-!
# Closed morphisms of curved differential graded right modules

This file gives element-level constructors and computations for Mathlib's closed degree-zero
category of the existing curved DG enrichment. A closed morphism is a right-linear map that
preserves the internal grading and commutes with the module differentials. A right-linear
equivalence preserving the grading and differential gives an isomorphism in that category.

The category and its morphisms remain `CategoryTheory.ForgetEnrichment`; the constructors use
the existing identification with zero-cocycles of the curved Hom complex.
-/

public section

open CategoryTheory MulOpposite

namespace TauCeti.CurvedDGRightModuleCat

universe u

-- The closed category keeps the original enriched object carrier.
attribute [local implicit_reducible] ForgetEnrichment

variable {R A : Type u} [CommRing R] [Ring A] [Algebra R A]
  {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] {d : A →ₗ[R] A} {w : A}
  {h : IsCurvedDGAlgebra 𝒜 d w}
  {M N P : CurvedDGRightModuleCat.{u, u, u} h}

/-- The underlying right-linear map of a morphism in the closed degree-zero category. -/
noncomputable def closedHom
    (f : ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) M ⟶
      ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) N) : M →ₗ[Aᵐᵒᵖ] N :=
  (dgClosedHomEquivZeroCocycles M N f).1.1

/-- The underlying map is the cochain of the closed degree-zero component. -/
theorem closedHom_eq
    (f : ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) M ⟶
      ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) N) :
    closedHom f = (dgHomLinearEquivCochains M N 0 (dgClosedHom R f)).1 := by
  ext x
  exact coe_dgClosedHomEquivZeroCocycles_apply f x

/-- Closed morphisms are determined by their underlying right-linear maps. -/
theorem closedHom_injective : Function.Injective (closedHom (M := M) (N := N)) := by
  intro f g hfg
  apply (dgClosedHomEquivZeroCocycles M N).injective
  exact Subtype.ext (Subtype.ext hfg)

/-- Closed morphisms are equal when their values agree. -/
@[ext]
theorem closedHom_ext
    {f g : ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) M ⟶
      ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) N}
    (hfg : ∀ x, closedHom f x = closedHom g x) : f = g :=
  closedHom_injective (LinearMap.ext hfg)

/-- Construct a closed morphism from a graded right-linear map commuting with differentials. -/
noncomputable def closedHomOf (f : M →ₗ[Aᵐᵒᵖ] N)
    (hf : ∀ p x, x ∈ M.grading p → f x ∈ N.grading p)
    (hd : ∀ x, N.differential (f x) = f (M.differential x)) :
    ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) M ⟶
      ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) N := by
  let c : dgRightModuleCochains (R := R) (A := A)
      (ℳ := M.grading) (ℳN := N.grading) 0 :=
    ⟨f, dgRightModuleCochains.mem_iff.mpr (by
      rw [LinearMap.isHomogeneous_def]
      simpa only [add_zero, LinearMap.restrictScalars_apply] using hf)⟩
  exact (dgClosedHomEquivZeroCocycles M N).symm
    ⟨c, LinearMap.mem_ker.mpr
      ((dgRightModuleCochains.curvedDifferential_zero_eq_zero_iff c).mpr hd)⟩

/-- The constructor retains its prescribed right-linear map. -/
@[simp]
theorem closedHom_closedHomOf (f : M →ₗ[Aᵐᵒᵖ] N)
    (hf : ∀ p x, x ∈ M.grading p → f x ∈ N.grading p)
    (hd : ∀ x, N.differential (f x) = f (M.differential x)) :
    closedHom (closedHomOf f hf hd) = f := by
  simp only [closedHom, closedHomOf, Equiv.apply_symm_apply]

/-- A closed morphism preserves homogeneous pieces. -/
theorem closedHom_mem
    (f : ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) M ⟶
      ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) N)
    {p : ℤ} {x : M} (hx : x ∈ M.grading p) : closedHom f x ∈ N.grading p := by
  simpa only [closedHom, add_zero] using dgRightModuleCochains.map_mem
    (dgClosedHomEquivZeroCocycles M N f).1 hx

/-- A closed morphism commutes with the differentials. -/
@[simp]
theorem differential_closedHom
    (f : ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) M ⟶
      ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) N) (x : M) :
    N.differential (closedHom f x) = closedHom f (M.differential x) :=
  (dgRightModuleCochains.curvedDifferential_zero_eq_zero_iff
    (dgClosedHomEquivZeroCocycles M N f).1).mp
      (LinearMap.mem_ker.mp (dgClosedHomEquivZeroCocycles M N f).2) x

/-- The identity closed morphism is the identity right-linear map. -/
@[simp]
theorem closedHom_id (M : CurvedDGRightModuleCat.{u, u, u} h) :
    closedHom (𝟙 (ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) M)) =
      LinearMap.id := by
  ext x
  simpa only [closedHom, dgRightModuleCochains.id_apply, LinearMap.id_apply] using
    congrArg (fun c : dgRightModuleCochains (R := R) (A := A)
    (ℳ := M.grading) (ℳN := M.grading) 0 ↦ c.1 x)
      (dgClosedHomEquivZeroCocycles_id (M := M))

/-- Composition of closed morphisms is composition of right-linear maps. -/
@[simp]
theorem closedHom_comp
    (f : ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) M ⟶
      ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) N)
    (g : ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) N ⟶
      ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) P) :
    closedHom (f ≫ g) = (closedHom g).comp (closedHom f) := by
  ext x
  simpa only [closedHom, dgRightModuleCochains.comp_apply, LinearMap.comp_apply] using
    congrArg (fun c : dgRightModuleCochains (R := R) (A := A)
    (ℳ := M.grading) (ℳN := P.grading) 0 ↦ c.1 x)
      (dgClosedHomEquivZeroCocycles_comp f g)

/-- The zero closed morphism has zero underlying linear map. -/
@[simp]
theorem closedHom_zero (M N : CurvedDGRightModuleCat.{u, u, u} h) :
    closedHom (0 : ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) M ⟶
      ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) N) = 0 := by
  rw [closedHom_eq, dgClosedHom_zero R _ _, map_zero]
  rfl

/-- Addition of closed morphisms is addition of their underlying linear maps. -/
@[simp]
theorem closedHom_add {M N : CurvedDGRightModuleCat.{u, u, u} h}
    (f g : ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) M ⟶
      ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) N) :
    closedHom (f + g) = closedHom f + closedHom g := by
  simp only [closedHom_eq]
  rw [dgClosedHom_add R f g, map_add]
  rfl

/-- A graded right-linear equivalence commuting with differentials is a closed isomorphism. -/
noncomputable def closedIsoOf (e : M ≃ₗ[Aᵐᵒᵖ] N)
    (he : ∀ p x, x ∈ M.grading p ↔ e x ∈ N.grading p)
    (hd : ∀ x, N.differential (e x) = e (M.differential x)) :
    ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) M ≅
      ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) N where
  hom := closedHomOf e.toLinearMap (fun p x hx ↦ (he p x).mp hx) hd
  inv := closedHomOf e.symm.toLinearMap
    (fun p x hx ↦ (he p (e.symm x)).mpr (by simpa only [e.apply_symm_apply] using hx))
    (fun x ↦ e.injective (by
      simp only [LinearEquiv.coe_toLinearMap, e.apply_symm_apply, ← hd]))
  hom_inv_id := by
    apply closedHom_ext
    intro x
    simp
  inv_hom_id := by
    apply closedHom_ext
    intro x
    simp

/-- The forward map of the closed isomorphism is the supplied equivalence. -/
@[simp]
theorem closedHom_closedIsoOf_hom (e : M ≃ₗ[Aᵐᵒᵖ] N)
    (he : ∀ p x, x ∈ M.grading p ↔ e x ∈ N.grading p)
    (hd : ∀ x, N.differential (e x) = e (M.differential x)) :
    closedHom (closedIsoOf e he hd).hom = e.toLinearMap := by
  simp only [closedIsoOf, closedHom_closedHomOf]

/-- The inverse map of the closed isomorphism is the inverse equivalence. -/
@[simp]
theorem closedHom_closedIsoOf_inv (e : M ≃ₗ[Aᵐᵒᵖ] N)
    (he : ∀ p x, x ∈ M.grading p ↔ e x ∈ N.grading p)
    (hd : ∀ x, N.differential (e x) = e (M.differential x)) :
    closedHom (closedIsoOf e he hd).inv = e.symm.toLinearMap := by
  simp only [closedIsoOf, closedHom_closedHomOf]

/-- Scalar multiplication of closed morphisms acts on their underlying right-linear maps. -/
@[simp]
theorem closedHom_smul (r : R)
    (f : ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) M ⟶
      ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) N) :
    closedHom (r • f) = r • closedHom f := by
  ext x
  simp only [closedHom_eq, dgClosedHom_smul R r f, map_smul,
    Submodule.coe_smul, LinearMap.smul_apply]

end TauCeti.CurvedDGRightModuleCat
