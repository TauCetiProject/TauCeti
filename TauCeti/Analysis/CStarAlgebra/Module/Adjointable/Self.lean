/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousMap
public import Mathlib.Topology.ContinuousMap.ContinuousSqrt
public import Mathlib.Topology.UnitInterval
public import TauCeti.Analysis.CStarAlgebra.Module.Adjointable.Basic
public import TauCeti.Analysis.CStarAlgebra.Module.Self

/-!
# Adjointable operators on the right self-module and non-adjointability counterexample

This file specializes bundled adjointable operators (`CStarModule.Adjointable`) to a C⋆-algebra `A`
regarded as a right Hilbert `A`-module over itself (`CStarModule.instMulOpposite` from
`TauCeti.Analysis.CStarAlgebra.Module.Self`), and constructs the standard counterexample showing
that bounded module maps between complete Hilbert C⋆-modules need not admit an adjoint:

* **Isometric left-multiplication embedding**: for any (possibly non-unital) C⋆-algebra `A`, left
  multiplication `x ↦ a * x` defines an adjointable operator
  `CStarModule.Adjointable.mulLeft a : Adjointable Aᵐᵒᵖ A A` with adjoint `mulLeft (star a)` and
  operator norm `‖mulLeft a‖ = ‖a‖`. Bundling yields an isometric non-unital `⋆`-algebra
  homomorphism `CStarModule.Adjointable.mulLeftNonUnitalStarAlgHom`
  (`A →⋆ₙₐ[ℂ] Adjointable Aᵐᵒᵖ A A`).
  When `A` is unital, every adjointable right `A`-module endomorphism of `A` is left multiplication
  by `T 1` (`CStarModule.Adjointable.eq_mulLeft_apply_one`), giving an isometric `⋆`-algebra
  isomorphism `CStarModule.Adjointable.mulLeftStarAlgEquiv : A ≃⋆ₐ[ℂ] Adjointable Aᵐᵒᵖ A A`.
* **Non-adjointable bounded module map** (`CStarModule.not_isAdjointable_vanishingAtZeroInclusion`):
  on `A = C(unitInterval, ℂ)`, the closed ideal `CStarModule.vanishingAtZeroSubmodule` of functions
  vanishing at `0` is a complete right Hilbert `A`-submodule, and its isometric `A`-linear
  inclusion into `C(unitInterval, ℂ)` has no adjoint. Indeed, any putative adjoint applied to `1`
  would vanish at `0` while equaling `1` at every nonzero point of `[0, 1]`, contradicting
  connectedness of `unitInterval`.

## Main declarations

* `CStarModule.Adjointable.mulLeft`, `CStarModule.Adjointable.mulLeftNonUnitalStarAlgHom`,
  `CStarModule.Adjointable.norm_mulLeft`, `CStarModule.Adjointable.isometry_mulLeft`: isometric
  left-multiplication embedding `A →⋆ₙₐ[ℂ] Adjointable Aᵐᵒᵖ A A`.
* `CStarModule.Adjointable.eq_mulLeft_apply_one`, `CStarModule.Adjointable.mulLeftStarAlgEquiv`:
  for unital `A`, `A ≃⋆ₐ[ℂ] Adjointable Aᵐᵒᵖ A A`.
* `CStarModule.vanishingAtZeroSubmodule`, `CStarModule.vanishingAtZeroInclusion`,
  `CStarModule.not_isAdjointable_vanishingAtZeroInclusion`: an isometric right module map between
  complete Hilbert `C([0, 1], ℂ)`-modules that is not adjointable.

## References

* E. Christopher Lance, *Hilbert C⋆-Modules: A Toolkit for Operator Algebraists*, Chapter 1, p. 8
  (non-adjointable inclusion `{f ∈ C([0, 1]) | f(0) = 0} ↪ C([0, 1])`) and Chapter 2.
* Iain Raeburn and Dana P. Williams, *Morita Equivalence and Continuous-Trace C⋆-Algebras*,
  Example 2.19 and Lemma 2.26.
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
  mkOfInner (ContinuousLinearMap.mul ℂ A a) (ContinuousLinearMap.mul ℂ A (star a)) fun x y ↦ by
    simp only [ContinuousLinearMap.mul_apply', inner_mulOpposite, star_mul, mul_assoc]

@[simp]
theorem mulLeft_apply (a x : A) : mulLeft a x = a * x := by
  simp [mulLeft]

@[simp]
theorem toContinuousLinearMap_mulLeft (a : A) :
    (mulLeft a).toContinuousLinearMap = ContinuousLinearMap.mul ℂ A a := by
  simp [mulLeft]

@[simp]
theorem adjoint_mulLeft (a : A) : (mulLeft a).adjoint = mulLeft (star a) := by
  ext x
  simp [mulLeft]

@[simp]
theorem mulLeft_zero : mulLeft (0 : A) = 0 := by
  ext x
  simp

theorem mulLeft_add (a b : A) : mulLeft (a + b) = mulLeft a + mulLeft b := by
  ext x
  simp [add_mul]

theorem mulLeft_mul (a b : A) : mulLeft (a * b) = mulLeft a * mulLeft b := by
  ext x
  simp [mul_assoc]

theorem mulLeft_smul (c : ℂ) (a : A) : mulLeft (c • a) = c • mulLeft a := by
  ext x
  simp [smul_mul_assoc]

/-- Left multiplication embeds any C⋆-algebra `A` into the C⋆-algebra `Adjointable Aᵐᵒᵖ A A` of
adjointable operators on its right self-module as a non-unital `⋆`-algebra homomorphism. -/
noncomputable def mulLeftNonUnitalStarAlgHom : A →⋆ₙₐ[ℂ] Adjointable Aᵐᵒᵖ A A where
  toFun := mulLeft
  map_smul' := mulLeft_smul
  map_zero' := mulLeft_zero
  map_add' := mulLeft_add
  map_mul' := mulLeft_mul
  map_star' a := by
    rw [star_def]
    exact (adjoint_mulLeft a).symm

@[simp]
theorem mulLeftNonUnitalStarAlgHom_apply (a : A) :
    mulLeftNonUnitalStarAlgHom a = mulLeft a := by rfl

/-- Left multiplication on the right self-module preserves the C⋆-norm: `‖mulLeft a‖ = ‖a‖`. -/
@[simp]
theorem norm_mulLeft (a : A) : ‖mulLeft a‖ = ‖a‖ := by
  rw [norm_def, toContinuousLinearMap_mulLeft, ContinuousLinearMap.opNorm_mul_apply]

/-- Left multiplication bundled as a complex-linear isometry `A →ₗᵢ[ℂ] Adjointable Aᵐᵒᵖ A A`. -/
noncomputable def mulLeftₗᵢ : A →ₗᵢ[ℂ] Adjointable Aᵐᵒᵖ A A where
  toFun := mulLeft
  map_add' := mulLeft_add
  map_smul' := mulLeft_smul
  norm_map' := norm_mulLeft

@[simp]
theorem mulLeftₗᵢ_apply (a : A) : mulLeftₗᵢ a = mulLeft a := by rfl

/-- Left multiplication `a ↦ mulLeft a` is an isometric embedding `A → Adjointable Aᵐᵒᵖ A A`. -/
theorem isometry_mulLeft : Isometry (mulLeft : A → Adjointable Aᵐᵒᵖ A A) :=
  mulLeftₗᵢ.isometry

end NonUnital

section Unital

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

@[simp]
theorem mulLeft_one : mulLeft (1 : A) = 1 := by
  ext x
  simp

/-- When `A` is unital, every adjointable operator `T` on the right self-module `A` is left
multiplication by `T 1`. -/
theorem eq_mulLeft_apply_one (T : Adjointable Aᵐᵒᵖ A A) : T = mulLeft (T 1) := by
  ext x
  calc T x = T (1 * x) := by rw [one_mul]
    _ = T (op x • (1 : A)) := by rw [smul_eq_mul_unop, unop_op]
    _ = op x • T 1 := T.map_op_smul x 1
    _ = T 1 * x := smul_eq_mul_unop _ _
    _ = mulLeft (T 1) x := (mulLeft_apply _ _).symm

/-- For a unital C⋆-algebra `A`, left multiplication identifies `A` with the unital C⋆-algebra
`Adjointable Aᵐᵒᵖ A A` of adjointable operators on its right self-module. -/
noncomputable def mulLeftStarAlgEquiv : A ≃⋆ₐ[ℂ] Adjointable Aᵐᵒᵖ A A where
  toFun := mulLeft
  invFun T := T 1
  left_inv a := by simp
  right_inv T := (eq_mulLeft_apply_one T).symm
  map_mul' := mulLeft_mul
  map_add' := mulLeft_add
  map_star' a := by
    rw [star_def]
    exact (adjoint_mulLeft a).symm
  map_smul' := mulLeft_smul

@[simp]
theorem mulLeftStarAlgEquiv_apply (a : A) : mulLeftStarAlgEquiv a = mulLeft a := by rfl

@[simp]
theorem mulLeftStarAlgEquiv_symm_apply (T : Adjointable Aᵐᵒᵖ A A) :
    mulLeftStarAlgEquiv.symm T = T 1 := by rfl

end Unital

end Adjointable

/-! ### Counterexample: a bounded right module isometry with no adjoint -/

section Counterexample

open scoped ComplexOrder

/-- The closed right ideal `{f ∈ C(unitInterval, ℂ) | f 0 = 0}`, viewed as a right
`C(unitInterval, ℂ)`-submodule of the right self-module `C(unitInterval, ℂ)`. By
`CStarModule.instSubmodule`, it inherits a Hilbert `C(unitInterval, ℂ)`-module structure. -/
def vanishingAtZeroSubmodule : Submodule C(unitInterval, ℂ)ᵐᵒᵖ C(unitInterval, ℂ) where
  carrier := {f : C(unitInterval, ℂ) | f 0 = 0}
  zero_mem' := by rfl
  add_mem' {f g} hf hg := by
    simp only [Set.mem_ofPred_eq, ContinuousMap.add_apply] at hf hg ⊢
    rw [hf, hg, add_zero]
  smul_mem' a {f} hf := by
    simp only [Set.mem_ofPred_eq, smul_eq_mul_unop, ContinuousMap.mul_apply] at hf ⊢
    rw [hf, zero_mul]

@[simp]
theorem mem_vanishingAtZeroSubmodule {f : C(unitInterval, ℂ)} :
    f ∈ vanishingAtZeroSubmodule ↔ f 0 = 0 := by rfl

/-- `vanishingAtZeroSubmodule` is closed in `C(unitInterval, ℂ)`, hence complete. -/
theorem isClosed_vanishingAtZeroSubmodule :
    IsClosed (vanishingAtZeroSubmodule : Set C(unitInterval, ℂ)) :=
  isClosed_eq (continuous_eval_const (0 : unitInterval)) continuous_const

instance instCompleteSpaceVanishingAtZeroSubmodule : CompleteSpace vanishingAtZeroSubmodule :=
  isClosed_vanishingAtZeroSubmodule.completeSpace_coe

/-- The inclusion `vanishingAtZeroSubmodule ↪ C(unitInterval, ℂ)` as a complex-linear isometry. -/
noncomputable def vanishingAtZeroInclusionₗᵢ :
    vanishingAtZeroSubmodule →ₗᵢ[ℂ] C(unitInterval, ℂ) where
  toFun f := (f : C(unitInterval, ℂ))
  map_add' _ _ := by rfl
  map_smul' _ _ := by rfl
  norm_map' _ := by rfl

/-- The bounded complex-linear inclusion `vanishingAtZeroSubmodule →L[ℂ] C(unitInterval, ℂ)`. -/
noncomputable def vanishingAtZeroInclusion : vanishingAtZeroSubmodule →L[ℂ] C(unitInterval, ℂ) :=
  vanishingAtZeroInclusionₗᵢ.toContinuousLinearMap

@[simp]
theorem vanishingAtZeroInclusion_apply (f : vanishingAtZeroSubmodule) :
    vanishingAtZeroInclusion f = (f : C(unitInterval, ℂ)) := by rfl

/-- `vanishingAtZeroInclusion` is a right `C(unitInterval, ℂ)`-module homomorphism. -/
theorem vanishingAtZeroInclusion_op_smul (a : C(unitInterval, ℂ)) (f : vanishingAtZeroSubmodule) :
    vanishingAtZeroInclusion (op a • f) = op a • vanishingAtZeroInclusion f := by rfl

/-- `vanishingAtZeroInclusion` is isometric. -/
theorem isometry_vanishingAtZeroInclusion : Isometry vanishingAtZeroInclusion :=
  vanishingAtZeroInclusionₗᵢ.isometry

/-- **Lance's non-adjointability counterexample**: although `vanishingAtZeroInclusion` is a bounded
(in fact isometric) right `C(unitInterval, ℂ)`-module homomorphism between complete Hilbert
`C(unitInterval, ℂ)`-modules, it does not admit an adjoint. -/
theorem not_isAdjointable_vanishingAtZeroInclusion :
    ¬ IsAdjointable C(unitInterval, ℂ)ᵐᵒᵖ vanishingAtZeroInclusion := by
  intro hadj
  obtain ⟨S, hS⟩ := (isAdjointable_mulOpposite_iff (B := C(unitInterval, ℂ))).mp hadj
  let t₀ : C(unitInterval, ℂ) :=
    ⟨fun x : unitInterval ↦ ((x : ℝ) : ℂ), Complex.continuous_ofReal.comp continuous_subtype_val⟩
  have ht₀ : t₀ ∈ vanishingAtZeroSubmodule := by
    simp [t₀]
  let h : C(unitInterval, ℂ) := (S 1 : C(unitInterval, ℂ))
  have hh0 : h 0 = 0 := (S 1).2
  have hpair := hS ⟨t₀, ht₀⟩ 1
  simp only [vanishingAtZeroInclusion_apply, submodule_coe_inner, unop_inner_mulOpposite,
    mul_one] at hpair
  have hh_ne : ∀ x : unitInterval, x ≠ 0 → h x = 1 := by
    intro x hx
    have hxR : (x : ℝ) ≠ 0 := fun h0 ↦ hx (Subtype.ext h0)
    have hstar : star (t₀ x) ≠ 0 := star_ne_zero.mpr (Complex.ofReal_ne_zero.mpr hxR)
    have hx_eq : star (t₀ x) = star (t₀ x) * h x := by
      simpa only [ContinuousMap.mul_apply, ContinuousMap.star_apply] using congrArg (· x) hpair
    exact (mul_left_cancel₀ hstar (by simpa only [mul_one] using hx_eq.symm))
  have hcompl : ({(0 : unitInterval)} : Set unitInterval)ᶜ = h ⁻¹' {(1 : ℂ)} := by
    ext x
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff, Set.mem_preimage]
    refine ⟨hh_ne x, ?_⟩
    rintro hx1 rfl
    rw [hh0] at hx1
    exact zero_ne_one hx1
  have hclopen : IsClopen ({(0 : unitInterval)} : Set unitInterval) :=
    ⟨isClosed_singleton, isClosed_compl_iff.mp (hcompl ▸ isClosed_singleton.preimage h.continuous)⟩
  rcases isClopen_iff.mp hclopen with h_empty | h_univ
  · exact Set.singleton_ne_empty (0 : unitInterval) h_empty
  · have h1 : (1 : unitInterval) ∈ ({(0 : unitInterval)} : Set unitInterval) := by
      rw [h_univ]
      exact Set.mem_univ _
    exact one_ne_zero (Set.mem_singleton_iff.mp h1)

/-- No bundled `Adjointable` operator underlies `vanishingAtZeroInclusion`. -/
theorem not_exists_adjointable_eq_vanishingAtZeroInclusion :
    ¬ ∃ T : Adjointable C(unitInterval, ℂ)ᵐᵒᵖ vanishingAtZeroSubmodule C(unitInterval, ℂ),
      T.toContinuousLinearMap = vanishingAtZeroInclusion := by
  rintro ⟨T, hT⟩
  have hcoe : ⇑T = ⇑vanishingAtZeroInclusion := congrArg DFunLike.coe hT
  exact not_isAdjointable_vanishingAtZeroInclusion (hcoe ▸ T.isAdjointable)

end Counterexample

end CStarModule
