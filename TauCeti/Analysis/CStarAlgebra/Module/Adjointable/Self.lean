/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousMap
public import Mathlib.Topology.UnitInterval
public import TauCeti.Analysis.CStarAlgebra.Module.Adjointable.Basic
public import TauCeti.Analysis.CStarAlgebra.Module.Self

/-!
# Adjointable operators on the right self-module and non-adjointability counterexample

This file specializes `CStarModule.Adjointable` to a C⋆-algebra `A` viewed as a right Hilbert
`A`-module over itself (`CStarModule.instMulOpposite` in
`TauCeti.Analysis.CStarAlgebra.Module.Self`), and constructs Lance's counterexample showing bounded
module maps need not admit an adjoint:

* **Isometric left-multiplication embedding**: for any C⋆-algebra `A`, `mulLeft a` (`x ↦ a * x`)
  lies in `Adjointable Aᵐᵒᵖ A A` with adjoint `mulLeft (star a)` and norm `‖a‖`, giving an
  isometric embedding `mulLeftNonUnitalStarAlgHom : A →⋆ₙₐ[ℂ] Adjointable Aᵐᵒᵖ A A` and, when `A`
  is unital, a `⋆`-algebra isomorphism `mulLeftStarAlgEquiv : A ≃⋆ₐ[ℂ] Adjointable Aᵐᵒᵖ A A`.
* **Non-adjointable bounded module map** (`CStarModule.not_isAdjointable_vanishingAtZeroInclusion`):
  on `C(unitInterval, ℂ)`, the closed ideal `{f | f 0 = 0}` is a complete right Hilbert submodule
  whose isometric module inclusion into `C(unitInterval, ℂ)` is not adjointable.

## Main declarations

* `CStarModule.Adjointable.mulLeft`, `CStarModule.Adjointable.mulLeftNonUnitalStarAlgHom`,
  `CStarModule.Adjointable.mulLeftₗᵢ`, `CStarModule.Adjointable.mulLeftStarAlgEquiv`
* `CStarModule.vanishingAtZeroSubmodule`, `CStarModule.vanishingAtZeroInclusion`,
  `CStarModule.not_isAdjointable_vanishingAtZeroInclusion`

## References

* E. Christopher Lance, *Hilbert C⋆-Modules: A Toolkit for Operator Algebraists*, Ch. 1–2.
* Iain Raeburn and Dana P. Williams, *Morita Equivalence and Continuous-Trace C⋆-Algebras*,
  Example 2.19.
-/

public section

open MulOpposite

namespace CStarModule

namespace Adjointable

/-! ### Isometric left-multiplication embedding `A →⋆ₙₐ[ℂ] Adjointable Aᵐᵒᵖ A A` -/

section NonUnital

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- Left multiplication by `a : A` as an adjointable operator on the right self-module `A`, with
adjoint given by left multiplication by `star a`. -/
noncomputable def mulLeft (a : A) : Adjointable Aᵐᵒᵖ A A :=
  mkOfInner (ContinuousLinearMap.mul ℂ A a) (ContinuousLinearMap.mul ℂ A (star a)) fun _ _ ↦ by
    simp only [ContinuousLinearMap.mul_apply', inner_mulOpposite, star_mul, mul_assoc]

@[simp] theorem mulLeft_apply (a x : A) : mulLeft a x = a * x := by simp [mulLeft]

@[simp] theorem toContinuousLinearMap_mulLeft (a : A) :
    (mulLeft a).toContinuousLinearMap = ContinuousLinearMap.mul ℂ A a := by simp [mulLeft]

@[simp] theorem adjoint_mulLeft (a : A) : (mulLeft a).adjoint = mulLeft (star a) := by
  ext; simp [mulLeft]

@[simp] theorem mulLeft_zero : mulLeft (0 : A) = 0 := by ext; simp
theorem mulLeft_add (a b : A) : mulLeft (a + b) = mulLeft a + mulLeft b := by ext; simp [add_mul]
theorem mulLeft_mul (a b : A) : mulLeft (a * b) = mulLeft a * mulLeft b := by ext; simp [mul_assoc]
theorem mulLeft_smul (c : ℂ) (a : A) : mulLeft (c • a) = c • mulLeft a := by
  ext; simp [smul_mul_assoc]
theorem mulLeft_star (a : A) : mulLeft (star a) = star (mulLeft a) := by
  rw [star_def, adjoint_mulLeft]

/-- Left multiplication embeds any C⋆-algebra `A` into `Adjointable Aᵐᵒᵖ A A` as a non-unital
`⋆`-algebra homomorphism. -/
noncomputable def mulLeftNonUnitalStarAlgHom : A →⋆ₙₐ[ℂ] Adjointable Aᵐᵒᵖ A A where
  toFun := mulLeft
  map_smul' := mulLeft_smul
  map_zero' := mulLeft_zero
  map_add' := mulLeft_add
  map_mul' := mulLeft_mul
  map_star' := mulLeft_star

@[simp] theorem mulLeftNonUnitalStarAlgHom_apply (a : A) :
    mulLeftNonUnitalStarAlgHom a = mulLeft a := by rfl

/-- Left multiplication on the right self-module preserves the C⋆-norm: `‖mulLeft a‖ = ‖a‖`. -/
@[simp] theorem norm_mulLeft (a : A) : ‖mulLeft a‖ = ‖a‖ := by
  rw [norm_def, toContinuousLinearMap_mulLeft, ContinuousLinearMap.opNorm_mul_apply]

/-- Left multiplication bundled as a complex-linear isometry `A →ₗᵢ[ℂ] Adjointable Aᵐᵒᵖ A A`. -/
noncomputable def mulLeftₗᵢ : A →ₗᵢ[ℂ] Adjointable Aᵐᵒᵖ A A where
  toFun := mulLeft
  map_add' := mulLeft_add
  map_smul' := mulLeft_smul
  norm_map' := norm_mulLeft

@[simp] theorem mulLeftₗᵢ_apply (a : A) : mulLeftₗᵢ a = mulLeft a := by rfl

/-- Left multiplication `a ↦ mulLeft a` is an isometric embedding `A → Adjointable Aᵐᵒᵖ A A`. -/
theorem isometry_mulLeft : Isometry (mulLeft : A → Adjointable Aᵐᵒᵖ A A) := mulLeftₗᵢ.isometry

end NonUnital

section Unital

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

@[simp] theorem mulLeft_one : mulLeft (1 : A) = 1 := by ext; simp

/-- When `A` is unital, every adjointable operator `T` on the right self-module `A` is left
multiplication by `T 1`. -/
theorem eq_mulLeft_apply_one (T : Adjointable Aᵐᵒᵖ A A) : T = mulLeft (T 1) := by
  ext x
  calc T x = T (op x • (1 : A)) := by rw [smul_eq_mul_unop, unop_op, one_mul]
    _ = mulLeft (T 1) x := by rw [T.map_op_smul, smul_eq_mul_unop, unop_op, mulLeft_apply]

/-- For a unital C⋆-algebra `A`, left multiplication identifies `A` with `Adjointable Aᵐᵒᵖ A A`. -/
noncomputable def mulLeftStarAlgEquiv : A ≃⋆ₐ[ℂ] Adjointable Aᵐᵒᵖ A A where
  toFun := mulLeft
  invFun T := T 1
  left_inv a := by simp
  right_inv T := (eq_mulLeft_apply_one T).symm
  map_mul' := mulLeft_mul
  map_add' := mulLeft_add
  map_star' := mulLeft_star
  map_smul' := mulLeft_smul

@[simp] theorem mulLeftStarAlgEquiv_apply (a : A) : mulLeftStarAlgEquiv a = mulLeft a := by rfl

@[simp] theorem mulLeftStarAlgEquiv_symm_apply (T : Adjointable Aᵐᵒᵖ A A) :
    mulLeftStarAlgEquiv.symm T = T 1 := by rfl

end Unital

end Adjointable

/-! ### Counterexample: a bounded right module isometry with no adjoint -/

section Counterexample

open scoped ComplexOrder

/-- The closed right ideal `{f ∈ C(unitInterval, ℂ) | f 0 = 0}`, viewed as a right
`C(unitInterval, ℂ)`-submodule of the right self-module `C(unitInterval, ℂ)`. -/
def vanishingAtZeroSubmodule : Submodule C(unitInterval, ℂ)ᵐᵒᵖ C(unitInterval, ℂ) where
  carrier := {f : C(unitInterval, ℂ) | f 0 = 0}
  zero_mem' := by rfl
  add_mem' {f g} hf hg := by
    simp only [Set.mem_ofPred_eq, ContinuousMap.add_apply] at hf hg ⊢; rw [hf, hg, add_zero]
  smul_mem' a {f} hf := by
    simp only [Set.mem_ofPred_eq, smul_eq_mul_unop, ContinuousMap.mul_apply] at hf ⊢
    rw [hf, zero_mul]

@[simp] theorem mem_vanishingAtZeroSubmodule {f : C(unitInterval, ℂ)} :
    f ∈ vanishingAtZeroSubmodule ↔ f 0 = 0 := by rfl

/-- `vanishingAtZeroSubmodule` is closed in `C(unitInterval, ℂ)`, hence complete. -/
theorem isClosed_vanishingAtZeroSubmodule :
    IsClosed (vanishingAtZeroSubmodule : Set C(unitInterval, ℂ)) :=
  isClosed_eq (continuous_eval_const (0 : unitInterval)) continuous_const

instance instCompleteSpaceVanishingAtZeroSubmodule : CompleteSpace vanishingAtZeroSubmodule :=
  isClosed_vanishingAtZeroSubmodule.completeSpace_coe

/-- The bounded complex-linear inclusion `vanishingAtZeroSubmodule →L[ℂ] C(unitInterval, ℂ)`. -/
noncomputable def vanishingAtZeroInclusion : vanishingAtZeroSubmodule →L[ℂ] C(unitInterval, ℂ) :=
  (vanishingAtZeroSubmodule.restrictScalars ℂ).subtypeₗᵢ.toContinuousLinearMap

@[simp] theorem vanishingAtZeroInclusion_apply (f : vanishingAtZeroSubmodule) :
    vanishingAtZeroInclusion f = (f : C(unitInterval, ℂ)) := by rfl

/-- `vanishingAtZeroInclusion` is a right `C(unitInterval, ℂ)`-module homomorphism. -/
theorem vanishingAtZeroInclusion_op_smul (a : C(unitInterval, ℂ)) (f : vanishingAtZeroSubmodule) :
    vanishingAtZeroInclusion (op a • f) = op a • vanishingAtZeroInclusion f := by rfl

/-- `vanishingAtZeroInclusion` is isometric. -/
theorem isometry_vanishingAtZeroInclusion : Isometry vanishingAtZeroInclusion :=
  (vanishingAtZeroSubmodule.restrictScalars ℂ).subtypeₗᵢ.isometry

/-- **Lance's non-adjointability counterexample**: `vanishingAtZeroInclusion` is an isometric right
`C(unitInterval, ℂ)`-module homomorphism between complete Hilbert modules with no adjoint. -/
theorem not_isAdjointable_vanishingAtZeroInclusion :
    ¬ IsAdjointable C(unitInterval, ℂ)ᵐᵒᵖ vanishingAtZeroInclusion := by
  intro hadj
  obtain ⟨S, hS⟩ := (isAdjointable_iff_unop_inner (B := C(unitInterval, ℂ))).mp hadj
  let t₀ : C(unitInterval, ℂ) :=
    ⟨fun x : unitInterval ↦ ((x : ℝ) : ℂ), Complex.continuous_ofReal.comp continuous_subtype_val⟩
  let h : C(unitInterval, ℂ) := (S 1 : C(unitInterval, ℂ))
  have hh0 : h 0 = 0 := (S 1).2
  have hpair := hS ⟨t₀, by simp [t₀]⟩ 1
  simp only [vanishingAtZeroInclusion_apply, submodule_coe_inner, unop_inner_mulOpposite,
    mul_one] at hpair
  have hh_ne : ∀ x : unitInterval, x ≠ 0 → h x = 1 := fun x hx ↦ by
    have hstar : star (t₀ x) ≠ 0 :=
      star_ne_zero.mpr (Complex.ofReal_ne_zero.mpr fun h0 ↦ hx (Subtype.ext h0))
    have hx_eq : star (t₀ x) = star (t₀ x) * h x := by
      simpa only [ContinuousMap.mul_apply, ContinuousMap.star_apply] using congrArg (· x) hpair
    exact mul_left_cancel₀ hstar (by simpa only [mul_one] using hx_eq.symm)
  have hcompl : ({(0 : unitInterval)} : Set unitInterval)ᶜ = h ⁻¹' {(1 : ℂ)} := by
    ext x; simp only [Set.mem_compl_iff, Set.mem_singleton_iff, Set.mem_preimage]
    exact ⟨hh_ne x, by rintro hx1 rfl; exact zero_ne_one (hh0 ▸ hx1)⟩
  have hclopen : IsClopen ({(0 : unitInterval)} : Set unitInterval) :=
    ⟨isClosed_singleton, isClosed_compl_iff.mp (hcompl ▸ isClosed_singleton.preimage h.continuous)⟩
  rcases isClopen_iff.mp hclopen with h_empty | h_univ
  · exact Set.singleton_ne_empty (0 : unitInterval) h_empty
  · exact one_ne_zero <| Set.mem_singleton_iff.mp (h_univ ▸ Set.mem_univ (1 : unitInterval))

/-- No bundled `Adjointable` operator underlies `vanishingAtZeroInclusion`. -/
theorem not_exists_adjointable_eq_vanishingAtZeroInclusion :
    ¬ ∃ T : Adjointable C(unitInterval, ℂ)ᵐᵒᵖ vanishingAtZeroSubmodule C(unitInterval, ℂ),
      T.toContinuousLinearMap = vanishingAtZeroInclusion := by
  rintro ⟨T, hT⟩
  exact not_isAdjointable_vanishingAtZeroInclusion (congrArg DFunLike.coe hT ▸ T.isAdjointable)

end Counterexample

end CStarModule
