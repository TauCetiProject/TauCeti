/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Module.Constructions
public import TauCeti.Analysis.CStarAlgebra.Module.AdjointPair

/-!
# Finite orthogonal sums and finite-sum inner-product estimates for C⋆-modules

Mathlib's `WithCStarModule` equips binary products `C⋆ᵐᵒᵈ(A, E × F)` and finite products
`C⋆ᵐᵒᵈ(A, Π i, E i)` with `CStarModule` structures over a (possibly nonunital) C⋆-algebra `A`.
This file supplies their coordinate inclusions (`inl`, `inr`, `single`) as complex linear
isometries and their coordinate projections (`fstCLM`, `sndCLM`, `evalCLM`) as contractive
continuous linear maps, proves that each inclusion/projection pair is a C⋆-module adjoint pair
commuting with the `A`-action, and constructs the inner-product-preserving linear isometric
equivalence `piFinTwoLinearIsometryEquiv` identifying the two-factor and `Fin 2`-indexed forms.

The second part derives finite-sum Cauchy–Schwarz and triangle inequalities for arbitrary families
of C⋆-modules by restricting to finite subsets, and deduces that unconditional norm summability
of diagonal inner products `⟪x i, x i⟫_A` implies unconditional norm summability of off-diagonal
inner products `⟪x i, y i⟫_A` and is preserved under coordinatewise addition. These estimates
underpin the arbitrary-index Hilbert direct sum in `TauCeti.Analysis.CStarAlgebra.Module.DirectSum`.

## Main declarations

* `WithCStarModule.inl`, `WithCStarModule.inr`, `WithCStarModule.fstCLM`,
  `WithCStarModule.sndCLM`: coordinate inclusions and projections for `C⋆ᵐᵒᵈ(A, E × F)`, with
  adjoint-pair identities `isAdjointPair_inl_fstCLM` and `isAdjointPair_inr_sndCLM`.
* `WithCStarModule.single`, `WithCStarModule.evalCLM`: coordinate inclusions and projections for
  `C⋆ᵐᵒᵈ(A, Π i, E i)` over `[Fintype ι]`, with `isAdjointPair_single_evalCLM`.
* `WithCStarModule.piFinTwoLinearIsometryEquiv`: inner-product-preserving linear isometric
  equivalence `C⋆ᵐᵒᵈ(A, ∀ i : Fin 2, M i) ≃ₗᵢ[ℂ] C⋆ᵐᵒᵈ(A, M 0 × M 1)`.
* `CStarModule.norm_sum_inner_le`, `CStarModule.sqrt_norm_sum_inner_add_le`: finite-sum
  Cauchy–Schwarz and triangle inequalities for a family of C⋆-modules.
* `CStarModule.summable_inner_of_summable_inner_self`, `CStarModule.summable_inner_add_self`:
  unconditional summability in the norm topology of `A` for off-diagonal and additive inner
  products.

## References

* E. Christopher Lance, *Hilbert C⋆-Modules: A Toolkit for Operator Algebraists*, Chapter 1,
  pp. 6–7.
* Iain Raeburn and Dana P. Williams, *Morita Equivalence and Continuous-Trace C⋆-Algebras*,
  Example 2.14.
-/

public section

noncomputable section

open Finset
open scoped WithCStarModule

/-! ### Coordinate inclusions, projections, and coherence for finite orthogonal sums -/

namespace WithCStarModule

section ProdExt

variable {A E F : Type*}

@[ext]
theorem prod_ext {x y : C⋆ᵐᵒᵈ(A, E × F)} (h₁ : x.fst = y.fst) (h₂ : x.snd = y.snd) : x = y :=
  (equiv A (E × F)).injective (Prod.ext h₁ h₂)

end ProdExt

section ProdProj

variable {A E F : Type*} [AddCommGroup E] [UniformSpace E] [Module ℂ E]
  [AddCommGroup F] [UniformSpace F] [Module ℂ F]

variable (A E F) in
/-- Projection onto the first summand of `C⋆ᵐᵒᵈ(A, E × F)` as a continuous linear map. -/
def fstCLM : C⋆ᵐᵒᵈ(A, E × F) →L[ℂ] E :=
  (ContinuousLinearMap.fst ℂ E F).comp (equivL ℂ (A := A) (E := E × F)).toContinuousLinearMap

variable (A E F) in
/-- Projection onto the second summand of `C⋆ᵐᵒᵈ(A, E × F)` as a continuous linear map. -/
def sndCLM : C⋆ᵐᵒᵈ(A, E × F) →L[ℂ] F :=
  (ContinuousLinearMap.snd ℂ E F).comp (equivL ℂ (A := A) (E := E × F)).toContinuousLinearMap

@[simp]
theorem fstCLM_apply (z : C⋆ᵐᵒᵈ(A, E × F)) : fstCLM A E F z = z.fst := (rfl)

@[simp]
theorem sndCLM_apply (z : C⋆ᵐᵒᵈ(A, E × F)) : sndCLM A E F z = z.snd := (rfl)

end ProdProj

section Prod

variable {A E F : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup E] [Module ℂ E] [SMul A E] [CStarModule A E]
  [NormedAddCommGroup F] [Module ℂ F] [SMul A F] [CStarModule A F]

variable (A E F) in
/-- Inclusion of the first summand into `C⋆ᵐᵒᵈ(A, E × F)` as a complex linear isometry. -/
def inl : E →ₗᵢ[ℂ] C⋆ᵐᵒᵈ(A, E × F) where
  toLinearMap := (linearEquiv ℂ A (E × F)).symm.toLinearMap.comp (LinearMap.inl ℂ E F)
  norm_map' x := by
    rw [prod_norm, CStarModule.norm_eq_sqrt_norm_inner_self (A := A) x]
    simp

variable (A E F) in
/-- Inclusion of the second summand into `C⋆ᵐᵒᵈ(A, E × F)` as a complex linear isometry. -/
def inr : F →ₗᵢ[ℂ] C⋆ᵐᵒᵈ(A, E × F) where
  toLinearMap := (linearEquiv ℂ A (E × F)).symm.toLinearMap.comp (LinearMap.inr ℂ E F)
  norm_map' y := by
    rw [prod_norm, CStarModule.norm_eq_sqrt_norm_inner_self (A := A) y]
    simp

@[simp]
theorem inl_fst (x : E) : (inl A E F x).fst = x := (rfl)

@[simp]
theorem inl_snd (x : E) : (inl A E F x).snd = 0 := (rfl)

@[simp]
theorem inr_fst (y : F) : (inr A E F y).fst = 0 := (rfl)

@[simp]
theorem inr_snd (y : F) : (inr A E F y).snd = y := (rfl)

@[simp]
theorem inner_inl_left (x : E) (z : C⋆ᵐᵒᵈ(A, E × F)) :
    inner A (inl A E F x) z = inner A x z.fst := by
  simp [prod_inner]

@[simp]
theorem inner_inl_right (z : C⋆ᵐᵒᵈ(A, E × F)) (x : E) :
    inner A z (inl A E F x) = inner A z.fst x := by
  simp [prod_inner]

@[simp]
theorem inner_inr_left (y : F) (z : C⋆ᵐᵒᵈ(A, E × F)) :
    inner A (inr A E F y) z = inner A y z.snd := by
  simp [prod_inner]

@[simp]
theorem inner_inr_right (z : C⋆ᵐᵒᵈ(A, E × F)) (y : F) :
    inner A z (inr A E F y) = inner A z.snd y := by
  simp [prod_inner]

/-- The first coordinate inclusion and projection on `C⋆ᵐᵒᵈ(A, E × F)` form a C⋆-module adjoint
pair. -/
theorem isAdjointPair_inl_fstCLM :
    LinearMap.IsAdjointPair (CStarModule.innerₛₗ (A := A)).flip
      (CStarModule.innerₛₗ (A := A)).flip (inl A E F) (fstCLM A E F) :=
  CStarModule.isAdjointPair_inner_iff.mpr fun _ _ ↦ by simp

/-- The second coordinate inclusion and projection on `C⋆ᵐᵒᵈ(A, E × F)` form a C⋆-module adjoint
pair. -/
theorem isAdjointPair_inr_sndCLM :
    LinearMap.IsAdjointPair (CStarModule.innerₛₗ (A := A)).flip
      (CStarModule.innerₛₗ (A := A)).flip (inr A E F) (sndCLM A E F) :=
  CStarModule.isAdjointPair_inner_iff.mpr fun _ _ ↦ by simp

@[simp]
theorem inl_smul (a : A) (x : E) : inl A E F (a • x) = a • inl A E F x :=
  isAdjointPair_inl_fstCLM.map_smul_coeff_cstarModule a x

@[simp]
theorem inr_smul (a : A) (y : F) : inr A E F (a • y) = a • inr A E F y :=
  isAdjointPair_inr_sndCLM.map_smul_coeff_cstarModule a y

@[simp]
theorem inl_fst_add_inr_snd (z : C⋆ᵐᵒᵈ(A, E × F)) :
    inl A E F z.fst + inr A E F z.snd = z := by
  ext <;> simp

end Prod

section ProdOpNorm

variable {A E F : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup E] [SMul A E] [NormedAddCommGroup F] [SMul A F]

/-- The first coordinate projection on `C⋆ᵐᵒᵈ(A, E × F)` is a contraction. -/
theorem norm_fstCLM_le [NormedSpace ℂ E] [CStarModule A E] [Module ℂ F] [CStarModule A F] :
    ‖fstCLM A E F‖ ≤ 1 :=
  (fstCLM A E F).opNorm_le_bound zero_le_one fun z ↦ by
    simpa only [one_mul, fstCLM_apply] using
      (le_max_left ‖z.fst‖ ‖z.snd‖).trans (max_le_prod_norm z)

/-- The second coordinate projection on `C⋆ᵐᵒᵈ(A, E × F)` is a contraction. -/
theorem norm_sndCLM_le [Module ℂ E] [CStarModule A E] [NormedSpace ℂ F] [CStarModule A F] :
    ‖sndCLM A E F‖ ≤ 1 :=
  (sndCLM A E F).opNorm_le_bound zero_le_one fun z ↦ by
    simpa only [one_mul, sndCLM_apply] using
      (le_max_right ‖z.fst‖ ‖z.snd‖).trans (max_le_prod_norm z)

end ProdOpNorm

section PiProj

variable {A ι : Type*} {E : ι → Type*}
  [∀ i, AddCommGroup (E i)] [∀ i, UniformSpace (E i)] [∀ i, Module ℂ (E i)]

variable (A E) in
/-- Coordinate projection from `C⋆ᵐᵒᵈ(A, Π j, E j)` onto the `i`-th summand. -/
def evalCLM (i : ι) : C⋆ᵐᵒᵈ(A, Π j, E j) →L[ℂ] E i :=
  (ContinuousLinearMap.proj i).comp (equivL ℂ (A := A) (E := Π j, E j)).toContinuousLinearMap

@[simp]
theorem evalCLM_apply (i : ι) (z : C⋆ᵐᵒᵈ(A, Π j, E j)) : evalCLM A E i z = z i := (rfl)

end PiProj

section Pi

variable {A ι : Type*} {E : ι → Type*} [Fintype ι]
  [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [∀ i, NormedAddCommGroup (E i)] [∀ i, Module ℂ (E i)]
  [∀ i, SMul A (E i)] [∀ i, CStarModule A (E i)]

variable (A E) in
/-- Coordinate inclusion of the `i`-th summand into the finite orthogonal sum
`C⋆ᵐᵒᵈ(A, Π j, E j)`. -/
def single [DecidableEq ι] (i : ι) : E i →ₗᵢ[ℂ] C⋆ᵐᵒᵈ(A, Π j, E j) where
  toLinearMap := (linearEquiv ℂ A (Π j, E j)).symm.toLinearMap.comp (LinearMap.single ℂ E i)
  norm_map' _ := by simp

/-- Evaluating `WithCStarModule.single A E i y` at coordinate `j` gives `Pi.single i y j`. -/
theorem single_apply [DecidableEq ι] (i : ι) (y : E i) (j : ι) :
    single A E i y j = Pi.single i y j := (rfl)

@[simp]
theorem single_apply_same [DecidableEq ι] (i : ι) (y : E i) :
    single A E i y i = y := by
  simp [single_apply]

@[simp]
theorem single_apply_of_ne [DecidableEq ι] {i j : ι} (h : j ≠ i) (y : E i) :
    single A E i y j = 0 := by
  simp [single_apply, h]

/-- The `i`-th coordinate inclusion and projection on `C⋆ᵐᵒᵈ(A, Π j, E j)` form a C⋆-module
adjoint pair. -/
theorem isAdjointPair_single_evalCLM [DecidableEq ι] (i : ι) :
    LinearMap.IsAdjointPair (CStarModule.innerₛₗ (A := A)).flip
      (CStarModule.innerₛₗ (A := A)).flip (single A E i) (evalCLM A E i) :=
  CStarModule.isAdjointPair_inner_iff.mpr fun _ _ ↦ by simp [WithCStarModule.single]

@[simp]
theorem single_smul [DecidableEq ι] (i : ι) (a : A) (y : E i) :
    single A E i (a • y) = a • single A E i y :=
  (isAdjointPair_single_evalCLM i).map_smul_coeff_cstarModule a y

/-- Every element of `C⋆ᵐᵒᵈ(A, Π j, E j)` is the finite sum of its coordinate inclusions. -/
@[simp]
theorem univ_sum_single [DecidableEq ι] (z : C⋆ᵐᵒᵈ(A, Π j, E j)) :
    ∑ i, single A E i (z i) = z := by
  apply (linearEquiv ℂ A (Π j, E j)).injective
  rw [map_sum]
  exact (Finset.sum_congr rfl fun i _ ↦ funext (single_apply (A := A) i (z i))).trans
    (LinearMap.sum_single_apply E (linearEquiv ℂ A (Π j, E j) z))

end Pi

section PiOpNorm

variable {A ι : Type*} {E : ι → Type*} [Fintype ι]
  [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℂ (E i)]
  [∀ i, SMul A (E i)] [∀ i, CStarModule A (E i)]

/-- Every coordinate projection `evalCLM A E i` on `C⋆ᵐᵒᵈ(A, Π j, E j)` is a contraction. -/
theorem norm_evalCLM_le (i : ι) : ‖evalCLM A E i‖ ≤ 1 :=
  (evalCLM A E i).opNorm_le_bound zero_le_one fun z ↦ by
    simpa only [one_mul, evalCLM_apply] using norm_apply_le_norm z i

end PiOpNorm

section PiFinTwo

variable {A : Type*} {M : Fin 2 → Type*}
  [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [∀ i, NormedAddCommGroup (M i)] [∀ i, Module ℂ (M i)]
  [∀ i, SMul A (M i)] [∀ i, CStarModule A (M i)]

variable (A M) in
/-- The finite-family orthogonal sum `C⋆ᵐᵒᵈ(A, ∀ i : Fin 2, M i)` agrees with the binary
orthogonal sum `C⋆ᵐᵒᵈ(A, M 0 × M 1)` via an `A`-equivariant, inner-product-preserving complex
linear isometric equivalence. -/
def piFinTwoLinearIsometryEquiv : C⋆ᵐᵒᵈ(A, ∀ i : Fin 2, M i) ≃ₗᵢ[ℂ] C⋆ᵐᵒᵈ(A, M 0 × M 1) where
  toLinearEquiv :=
    (linearEquiv ℂ A (∀ i : Fin 2, M i)).trans
      ((LinearEquiv.piFinTwo ℂ M).trans (linearEquiv ℂ A (M 0 × M 1)).symm)
  norm_map' _ := by
    simp [prod_norm, pi_norm, Fin.sum_univ_two]

@[simp]
theorem piFinTwoLinearIsometryEquiv_fst (x : C⋆ᵐᵒᵈ(A, ∀ i : Fin 2, M i)) :
    (piFinTwoLinearIsometryEquiv A M x).fst = x 0 := (rfl)

@[simp]
theorem piFinTwoLinearIsometryEquiv_snd (x : C⋆ᵐᵒᵈ(A, ∀ i : Fin 2, M i)) :
    (piFinTwoLinearIsometryEquiv A M x).snd = x 1 := (rfl)

@[simp]
theorem piFinTwoLinearIsometryEquiv_symm_zero (z : C⋆ᵐᵒᵈ(A, M 0 × M 1)) :
    (piFinTwoLinearIsometryEquiv A M).symm z 0 = z.fst := (rfl)

@[simp]
theorem piFinTwoLinearIsometryEquiv_symm_one (z : C⋆ᵐᵒᵈ(A, M 0 × M 1)) :
    (piFinTwoLinearIsometryEquiv A M).symm z 1 = z.snd := (rfl)

@[simp]
theorem inner_piFinTwoLinearIsometryEquiv (x y : C⋆ᵐᵒᵈ(A, ∀ i : Fin 2, M i)) :
    inner A (piFinTwoLinearIsometryEquiv A M x) (piFinTwoLinearIsometryEquiv A M y) =
      inner A x y := by
  simp [prod_inner, pi_inner, Fin.sum_univ_two]

@[simp]
theorem inner_piFinTwoLinearIsometryEquiv_symm (x y : C⋆ᵐᵒᵈ(A, M 0 × M 1)) :
    inner A ((piFinTwoLinearIsometryEquiv A M).symm x)
      ((piFinTwoLinearIsometryEquiv A M).symm y) = inner A x y := by
  rw [← inner_piFinTwoLinearIsometryEquiv (A := A) (M := M)]
  simp

@[simp]
theorem piFinTwoLinearIsometryEquiv_smul (a : A) (x : C⋆ᵐᵒᵈ(A, ∀ i : Fin 2, M i)) :
    piFinTwoLinearIsometryEquiv A M (a • x) = a • piFinTwoLinearIsometryEquiv A M x := by
  ext <;> simp

@[simp]
theorem piFinTwoLinearIsometryEquiv_symm_smul (a : A) (z : C⋆ᵐᵒᵈ(A, M 0 × M 1)) :
    (piFinTwoLinearIsometryEquiv A M).symm (a • z) =
      a • (piFinTwoLinearIsometryEquiv A M).symm z := by
  apply (piFinTwoLinearIsometryEquiv A M).injective
  simp

@[simp]
theorem piFinTwoLinearIsometryEquiv_single_zero (x₀ : M 0) :
    piFinTwoLinearIsometryEquiv A M (single A M 0 x₀) = inl A (M 0) (M 1) x₀ := by
  ext <;> simp

@[simp]
theorem piFinTwoLinearIsometryEquiv_single_one (x₁ : M 1) :
    piFinTwoLinearIsometryEquiv A M (single A M 1 x₁) = inr A (M 0) (M 1) x₁ := by
  ext <;> simp

@[simp]
theorem piFinTwoLinearIsometryEquiv_symm_inl (x₀ : M 0) :
    (piFinTwoLinearIsometryEquiv A M).symm (inl A (M 0) (M 1) x₀) = single A M 0 x₀ := by
  apply (piFinTwoLinearIsometryEquiv A M).injective
  simp

@[simp]
theorem piFinTwoLinearIsometryEquiv_symm_inr (x₁ : M 1) :
    (piFinTwoLinearIsometryEquiv A M).symm (inr A (M 0) (M 1) x₁) = single A M 1 x₁ := by
  apply (piFinTwoLinearIsometryEquiv A M).injective
  simp

end PiFinTwo

end WithCStarModule

/-! ### Finite-sum estimates and summability of inner products -/

namespace CStarModule

section RestrictFinset

variable {A ι : Type*} {E : ι → Type*}

/-- Restrict a coordinate family `z : ∀ i, E i` to a finite subset `s` as an element of
`C⋆ᵐᵒᵈ(A, ∀ i : s, E i)`. -/
private def restrictFinset (s : Finset ι) (z : ∀ i, E i) : C⋆ᵐᵒᵈ(A, ∀ i : s, E i) :=
  (WithCStarModule.equiv A (∀ i : s, E i)).symm fun i ↦ z i

private theorem restrictFinset_apply (s : Finset ι) (z : ∀ i, E i) (i : s) :
    restrictFinset (A := A) s z i = z i :=
  WithCStarModule.equiv_symm_pi_apply _ i

private theorem restrictFinset_add [∀ i, AddCommGroup (E i)] (s : Finset ι) (x y : ∀ i, E i) :
    restrictFinset (A := A) s x + restrictFinset (A := A) s y =
      restrictFinset (A := A) s (fun i ↦ x i + y i) :=
  WithCStarModule.ext fun i ↦ by simp [restrictFinset_apply]

variable [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [∀ i, NormedAddCommGroup (E i)] [∀ i, Module ℂ (E i)]
  [∀ i, SMul A (E i)] [∀ i, CStarModule A (E i)]

private theorem inner_restrictFinset (s : Finset ι) (x y : ∀ i, E i) :
    inner A (restrictFinset (A := A) s x) (restrictFinset (A := A) s y) =
      ∑ i ∈ s, inner A (x i) (y i) := by
  simp only [WithCStarModule.pi_inner, restrictFinset_apply]
  exact Finset.sum_attach s fun i ↦ inner A (x i) (y i)

private theorem norm_restrictFinset (s : Finset ι) (z : ∀ i, E i) :
    ‖restrictFinset (A := A) s z‖ = √‖∑ i ∈ s, inner A (z i) (z i)‖ := by
  rw [norm_eq_sqrt_norm_inner_self (A := A), inner_restrictFinset]

end RestrictFinset

variable {A ι : Type*} {E : ι → Type*}
  [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [∀ i, AddCommGroup (E i)] [∀ i, Norm (E i)] [∀ i, Module ℂ (E i)]
  [∀ i, SMul A (E i)] [∀ i, CStarModule A (E i)]

variable (A E) in
/-- Equip each summand `E i` with `CStarModule.normedAddCommGroup A` so that Mathlib's
`WithCStarModule` finite-product `Norm` and `CStarModule` instances (which require
`[∀ i, NormedAddCommGroup (E i)]`) apply under `[∀ i, AddCommGroup (E i)]` and `[∀ i, Norm (E i)]`.

Both `CStarModule.normedAddCommGroup` and `NormedAddCommGroup.ofCore` are `abbrev`s extending
`SeminormedAddCommGroup.ofCore`, which retains the preexisting `AddCommGroup` and `Norm` instances
without replacing them. Consequently, `(coordNormedAddCommGroup A E i).toAddCommGroup` and
`(coordNormedAddCommGroup A E i).toNorm` are definitionally equal to the given
`[AddCommGroup (E i)]` and `[Norm (E i)]` instances, so `[CStarModule A (E i)]`, `inner A`, and
`+` on `E i` remain definitionally unchanged when this instance is installed locally. -/
private abbrev coordNormedAddCommGroup (i : ι) : NormedAddCommGroup (E i) :=
  CStarModule.normedAddCommGroup A

/-- Finite-sum Cauchy–Schwarz inequality for a family of C⋆-modules:
`‖∑ i ∈ s, ⟪x i, y i⟫_A‖ ≤ √‖∑ i ∈ s, ⟪x i, x i⟫_A‖ * √‖∑ i ∈ s, ⟪y i, y i⟫_A‖`. -/
theorem norm_sum_inner_le (s : Finset ι) (x y : ∀ i, E i) :
    ‖∑ i ∈ s, inner A (x i) (y i)‖ ≤
      √‖∑ i ∈ s, inner A (x i) (x i)‖ * √‖∑ i ∈ s, inner A (y i) (y i)‖ := by
  let _ := coordNormedAddCommGroup A E
  simpa only [inner_restrictFinset, norm_restrictFinset] using
    norm_inner_le (A := A) (C⋆ᵐᵒᵈ(A, ∀ i : s, E i))
      (x := restrictFinset (A := A) s x) (y := restrictFinset (A := A) s y)

/-- Triangle inequality for the C⋆-module norm of finite coordinate sums:
`√‖∑ i ∈ s, ⟪x i + y i, x i + y i⟫_A‖ ≤ √‖∑ i ∈ s, ⟪x i, x i⟫_A‖ + √‖∑ i ∈ s, ⟪y i, y i⟫_A‖`. -/
theorem sqrt_norm_sum_inner_add_le (s : Finset ι) (x y : ∀ i, E i) :
    √‖∑ i ∈ s, inner A (x i + y i) (x i + y i)‖ ≤
      √‖∑ i ∈ s, inner A (x i) (x i)‖ + √‖∑ i ∈ s, inner A (y i) (y i)‖ := by
  let _ := coordNormedAddCommGroup A E
  simpa only [restrictFinset_add, norm_restrictFinset] using
    CStarModule.norm_triangle A (restrictFinset (A := A) s x) (restrictFinset (A := A) s y)

/-- If the diagonal inner products `⟪x i, x i⟫_A` and `⟪y i, y i⟫_A` are unconditionally summable
in the norm topology of `A`, then the off-diagonal inner products `⟪x i, y i⟫_A` are also
unconditionally summable in the norm topology of `A`. -/
theorem summable_inner_of_summable_inner_self {x y : ∀ i, E i}
    (hx : Summable fun i ↦ inner A (x i) (x i))
    (hy : Summable fun i ↦ inner A (y i) (y i)) :
    Summable fun i ↦ inner A (x i) (y i) := by
  classical
  rw [summable_iff_vanishing_norm] at hx hy ⊢
  intro ε hε
  obtain ⟨s₁, hs₁⟩ := hx (ε / 2) (half_pos hε)
  obtain ⟨s₂, hs₂⟩ := hy (ε / 2) (half_pos hε)
  refine ⟨s₁ ∪ s₂, fun t ht ↦ ?_⟩
  have h₁ : √‖∑ i ∈ t, inner A (x i) (x i)‖ ≤ √(ε / 2) :=
    Real.sqrt_le_sqrt (hs₁ t (ht.mono_right subset_union_left)).le
  have h₂ : √‖∑ i ∈ t, inner A (y i) (y i)‖ ≤ √(ε / 2) :=
    Real.sqrt_le_sqrt (hs₂ t (ht.mono_right subset_union_right)).le
  calc ‖∑ i ∈ t, inner A (x i) (y i)‖
      ≤ √‖∑ i ∈ t, inner A (x i) (x i)‖ * √‖∑ i ∈ t, inner A (y i) (y i)‖ :=
        norm_sum_inner_le t x y
    _ ≤ √(ε / 2) * √(ε / 2) := by gcongr
    _ = ε / 2 := Real.mul_self_sqrt (half_pos hε).le
    _ < ε := half_lt_self hε

/-- Unconditional summability of diagonal inner products in the norm topology of `A` is preserved
under coordinatewise addition. -/
theorem summable_inner_add_self {x y : ∀ i, E i}
    (hx : Summable fun i ↦ inner A (x i) (x i))
    (hy : Summable fun i ↦ inner A (y i) (y i)) :
    Summable fun i ↦ inner A (x i + y i) (x i + y i) := by
  simp_rw [inner_add_left, inner_add_right]
  exact (hx.add (summable_inner_of_summable_inner_self hx hy)).add
    ((summable_inner_of_summable_inner_self hy hx).add hy)

end CStarModule
