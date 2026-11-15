/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Module.Constructions
public import Mathlib.Analysis.Normed.Lp.lpSpace
public import Mathlib.LinearAlgebra.DFinsupp
public import TauCeti.Analysis.CStarAlgebra.Module.Action
public import TauCeti.Analysis.CStarAlgebra.Module.AdjointPair
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Topology.Algebra.InfiniteSum.Constructions
import Mathlib.Topology.Algebra.InfiniteSum.Order

/-!
# Finite and infinite Hilbert direct sums of C⋆-modules

Mathlib's `WithCStarModule` equips binary products `C⋆ᵐᵒᵈ(A, E × F)` and finite products
`C⋆ᵐᵒᵈ(A, Π i, E i)` with `CStarModule` structures over a (possibly nonunital) C⋆-algebra `A`.
The first part of this file supplies their coordinate inclusions (`inl`, `inr`, `single`) as
complex linear isometries and their coordinate projections (`fstCLM`, `sndCLM`, `evalCLM`) as
contractive continuous linear maps, proves that each inclusion/projection pair is a C⋆-module
adjoint pair commuting with the `A`-action, and constructs the inner-product-preserving linear
isometric equivalence `piFinTwoLinearIsometryEquiv` identifying the two-factor and `Fin 2`-indexed
forms.

For an arbitrary (possibly infinite or uncountable) index type `ι` and a family `E : ι → Type*`
of `CStarModule`s over `A`, the second part constructs the Hilbert direct sum
`TauCeti.HilbertDirectSum A E`, consisting of dependent families `x : ∀ i, E i` whose diagonal
inner products `⟪x i, x i⟫_A` are norm-summable in `A`. Off-diagonal inner products `⟪x i, y i⟫_A`
are norm-summable whenever the diagonal series converge, and norm-summability is preserved under
coordinatewise addition and scalar actions. Consequently `HilbertDirectSum A E` is a
`CStarModule A` under `⟪x, y⟫_A = ∑' i, ⟪x i, y i⟫_A`, complete whenever every summand `E i` is
complete.

Every element `x` is the unconditional norm sum `∑' i, single A E i (x i)` of its coordinates,
so finitely supported families are dense; when `ι` is finite, `HilbertDirectSum A E` agrees
isometrically and inner-product-preservingly with `C⋆ᵐᵒᵈ(A, Π i, E i)`. Finally, the Banach
`ℓ²`-sum `lp E 2` of families satisfying `∑' i, ‖x i‖ ^ 2 < ∞` embeds contractively, injectively,
and with dense range into `HilbertDirectSum A E`. Right Hilbert `B`-modules are covered
throughout by taking `A = Bᵐᵒᵖ`.

## Main declarations

* `WithCStarModule.inl`, `WithCStarModule.inr`, `WithCStarModule.fstCLM`,
  `WithCStarModule.sndCLM`: coordinate inclusions and projections for `C⋆ᵐᵒᵈ(A, E × F)`, with
  adjoint-pair identities `isAdjointPair_inl_fstCLM` and `isAdjointPair_inr_sndCLM`.
* `WithCStarModule.single`, `WithCStarModule.evalCLM`: coordinate inclusions and projections for
  `C⋆ᵐᵒᵈ(A, Π i, E i)` over `[Fintype ι]`, with `isAdjointPair_single_evalCLM`.
* `WithCStarModule.piFinTwoLinearIsometryEquiv`: inner-product-preserving linear isometric
  equivalence `C⋆ᵐᵒᵈ(A, ∀ i : Fin 2, M i) ≃ₗᵢ[ℂ] C⋆ᵐᵒᵈ(A, M 0 × M 1)`.
* `CStarModule.norm_sum_inner_le`, `CStarModule.summable_inner_of_summable_inner_self`: finite-sum
  Cauchy–Schwarz inequality and norm-summability of off-diagonal inner products.
* `TauCeti.HilbertDirectSum`: the Hilbert direct sum `⊕ᵢ E i` of a family of `CStarModule`s,
  equipped with `CStarModule A`, `NormedAddCommGroup`, `NormedSpace ℂ`, and `CompleteSpace`.
* `TauCeti.HilbertDirectSum.single`, `TauCeti.HilbertDirectSum.evalCLM`,
  `TauCeti.HilbertDirectSum.trunc`: coordinate inclusions, coordinate projections, and finite-set
  truncations, with `hasSum_single` and `denseRange_ofDFinsupp`.
* `TauCeti.HilbertDirectSum.equivWithCStarModulePi`: agreement with `C⋆ᵐᵒᵈ(A, Π i, E i)` when
  `[Fintype ι]`.
* `TauCeti.HilbertDirectSum.ofLp`: contractive, injective continuous linear map
  `lp E 2 →L[ℂ] HilbertDirectSum A E` with dense range (`denseRange_ofLp`).

## References

* E. Christopher Lance, *Hilbert C⋆-Modules: A Toolkit for Operator Algebraists*, Chapter 1,
  pp. 6–7.
* Iain Raeburn and Dana P. Williams, *Morita Equivalence and Continuous-Trace C⋆-Algebras*,
  Example 2.14.
-/

public section

noncomputable section

open Filter Topology Finset MulOpposite
open scoped ENNReal NNReal WithCStarModule

/-! ### Coordinate inclusions, projections, and coherence for finite orthogonal sums -/

namespace WithCStarModule

section ProdExt

variable {A E F : Type*}

@[ext]
theorem prod_ext {x y : C⋆ᵐᵒᵈ(A, E × F)} (h₁ : x.fst = y.fst) (h₂ : x.snd = y.snd) : x = y :=
  (equiv A (E × F)).injective (Prod.ext h₁ h₂)

end ProdExt

section ProdProj

variable {A E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

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

theorem fstCLM_smul [SMul A E] [SMul A F] (a : A) (z : C⋆ᵐᵒᵈ(A, E × F)) :
    fstCLM A E F (a • z) = a • fstCLM A E F z := (rfl)

theorem sndCLM_smul [SMul A E] [SMul A F] (a : A) (z : C⋆ᵐᵒᵈ(A, E × F)) :
    sndCLM A E F (a • z) = a • sndCLM A E F z := (rfl)

end ProdProj

section Prod

variable {A E F : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul A E] [CStarModule A E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul A F] [CStarModule A F]

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
  CStarModule.isAdjointPair_inner_iff.mpr fun x z ↦ inner_inl_left x z

/-- The second coordinate inclusion and projection on `C⋆ᵐᵒᵈ(A, E × F)` form a C⋆-module adjoint
pair. -/
theorem isAdjointPair_inr_sndCLM :
    LinearMap.IsAdjointPair (CStarModule.innerₛₗ (A := A)).flip
      (CStarModule.innerₛₗ (A := A)).flip (inr A E F) (sndCLM A E F) :=
  CStarModule.isAdjointPair_inner_iff.mpr fun y z ↦ inner_inr_left y z

@[simp]
theorem inl_smul (a : A) (x : E) : inl A E F (a • x) = a • inl A E F x :=
  isAdjointPair_inl_fstCLM.map_smul_coeff_cstarModule a x

@[simp]
theorem inr_smul (a : A) (y : F) : inr A E F (a • y) = a • inr A E F y :=
  isAdjointPair_inr_sndCLM.map_smul_coeff_cstarModule a y

theorem norm_fstCLM_le : ‖fstCLM A E F‖ ≤ 1 :=
  (fstCLM A E F).opNorm_le_bound zero_le_one fun z ↦ by
    simpa only [one_mul, fstCLM_apply] using
      (le_max_left ‖z.fst‖ ‖z.snd‖).trans (max_le_prod_norm z)

theorem norm_sndCLM_le : ‖sndCLM A E F‖ ≤ 1 :=
  (sndCLM A E F).opNorm_le_bound zero_le_one fun z ↦ by
    simpa only [one_mul, sndCLM_apply] using
      (le_max_right ‖z.fst‖ ‖z.snd‖).trans (max_le_prod_norm z)

@[simp]
theorem inl_fst_add_inr_snd (z : C⋆ᵐᵒᵈ(A, E × F)) :
    inl A E F z.fst + inr A E F z.snd = z := by
  ext <;> simp

end Prod

section PiProj

variable {A ι : Type*} {E : ι → Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℂ (E i)]

variable (A E) in
/-- Coordinate projection from `C⋆ᵐᵒᵈ(A, Π j, E j)` onto the `i`-th summand. -/
def evalCLM (i : ι) : C⋆ᵐᵒᵈ(A, Π j, E j) →L[ℂ] E i :=
  (ContinuousLinearMap.proj i).comp (equivL ℂ (A := A) (E := Π j, E j)).toContinuousLinearMap

@[simp]
theorem evalCLM_apply (i : ι) (z : C⋆ᵐᵒᵈ(A, Π j, E j)) : evalCLM A E i z = z i := (rfl)

theorem evalCLM_smul [∀ i, SMul A (E i)] (i : ι) (a : A) (z : C⋆ᵐᵒᵈ(A, Π j, E j)) :
    evalCLM A E i (a • z) = a • evalCLM A E i z := (rfl)

end PiProj

section Pi

variable {A ι : Type*} {E : ι → Type*} [Fintype ι]
  [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℂ (E i)]
  [∀ i, SMul A (E i)] [∀ i, CStarModule A (E i)]

variable (A E) in
/-- Coordinate inclusion of the `i`-th summand into the finite orthogonal sum
`C⋆ᵐᵒᵈ(A, Π j, E j)`. -/
def single [DecidableEq ι] (i : ι) : E i →ₗᵢ[ℂ] C⋆ᵐᵒᵈ(A, Π j, E j) where
  toLinearMap := (linearEquiv ℂ A (Π j, E j)).symm.toLinearMap.comp (LinearMap.single ℂ E i)
  norm_map' y := norm_single i y

theorem single_apply [DecidableEq ι] (i : ι) (y : E i) (j : ι) :
    single A E i y j = Pi.single i y j := (rfl)

@[simp]
theorem single_apply_same [DecidableEq ι] (i : ι) (y : E i) :
    single A E i y i = y :=
  Pi.single_eq_same i y

@[simp]
theorem single_apply_of_ne [DecidableEq ι] {i j : ι} (h : j ≠ i) (y : E i) :
    single A E i y j = 0 :=
  Pi.single_eq_of_ne h y

@[simp]
theorem inner_single_left' [DecidableEq ι] (i : ι) (y : E i) (z : C⋆ᵐᵒᵈ(A, Π j, E j)) :
    inner A (single A E i y) z = inner A y (z i) :=
  inner_single_left z y

@[simp]
theorem inner_single_right' [DecidableEq ι] (z : C⋆ᵐᵒᵈ(A, Π j, E j)) (i : ι) (y : E i) :
    inner A z (single A E i y) = inner A (z i) y :=
  inner_single_right z y

/-- The `i`-th coordinate inclusion and projection on `C⋆ᵐᵒᵈ(A, Π j, E j)` form a C⋆-module
adjoint pair. -/
theorem isAdjointPair_single_evalCLM [DecidableEq ι] (i : ι) :
    LinearMap.IsAdjointPair (CStarModule.innerₛₗ (A := A)).flip
      (CStarModule.innerₛₗ (A := A)).flip (single A E i) (evalCLM A E i) :=
  CStarModule.isAdjointPair_inner_iff.mpr fun y z ↦ inner_single_left' i y z

@[simp]
theorem single_smul [DecidableEq ι] (i : ι) (a : A) (y : E i) :
    single A E i (a • y) = a • single A E i y :=
  (isAdjointPair_single_evalCLM i).map_smul_coeff_cstarModule a y

theorem norm_evalCLM_le (i : ι) : ‖evalCLM A E i‖ ≤ 1 :=
  (evalCLM A E i).opNorm_le_bound zero_le_one fun z ↦ by
    simpa only [one_mul, evalCLM_apply] using norm_apply_le_norm z i

@[simp]
theorem sum_single_apply [DecidableEq ι] (z : C⋆ᵐᵒᵈ(A, Π j, E j)) :
    ∑ i, single A E i (z i) = z := by
  apply CStarModule.ext_inner_left (A := A)
  intro w
  rw [CStarModule.inner_sum_right (A := A)]
  simp only [inner_single_right']
  rw [pi_inner]

end Pi

section PiFinTwo

variable {A : Type*} {M : Fin 2 → Type*}
  [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [∀ i, NormedAddCommGroup (M i)] [∀ i, NormedSpace ℂ (M i)]
  [∀ i, SMul A (M i)] [∀ i, CStarModule A (M i)]

variable (A M) in
/-- The finite-family orthogonal sum `C⋆ᵐᵒᵈ(A, ∀ i : Fin 2, M i)` agrees with the binary
orthogonal sum `C⋆ᵐᵒᵈ(A, M 0 × M 1)` via an `A`-equivariant, inner-product-preserving complex
linear isometric equivalence. -/
def piFinTwoLinearIsometryEquiv : C⋆ᵐᵒᵈ(A, ∀ i : Fin 2, M i) ≃ₗᵢ[ℂ] C⋆ᵐᵒᵈ(A, M 0 × M 1) where
  toLinearEquiv :=
    (linearEquiv ℂ A (∀ i : Fin 2, M i)).trans
      ((LinearEquiv.piFinTwo ℂ M).trans (linearEquiv ℂ A (M 0 × M 1)).symm)
  norm_map' x := by
    rw [prod_norm, pi_norm, Fin.sum_univ_two]
    rfl

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
  rw [prod_inner, pi_inner, Fin.sum_univ_two]
  rfl

@[simp]
theorem piFinTwoLinearIsometryEquiv_smul (a : A) (x : C⋆ᵐᵒᵈ(A, ∀ i : Fin 2, M i)) :
    piFinTwoLinearIsometryEquiv A M (a • x) = a • piFinTwoLinearIsometryEquiv A M x := by
  ext <;> rfl

@[simp]
theorem piFinTwoLinearIsometryEquiv_single_zero (x₀ : M 0) :
    piFinTwoLinearIsometryEquiv A M (single A M 0 x₀) = inl A (M 0) (M 1) x₀ := by
  ext <;> simp

@[simp]
theorem piFinTwoLinearIsometryEquiv_single_one (x₁ : M 1) :
    piFinTwoLinearIsometryEquiv A M (single A M 1 x₁) = inr A (M 0) (M 1) x₁ := by
  ext <;> simp

end PiFinTwo

end WithCStarModule

/-! ### Finite-sum estimates and summability of inner products -/

namespace CStarModule

variable {A ι : Type*} {E : ι → Type*}
  [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [∀ i, NormedAddCommGroup (E i)] [∀ i, Module ℂ (E i)]
  [∀ i, SMul A (E i)] [∀ i, CStarModule A (E i)]

/-- Finite-sum Cauchy–Schwarz inequality for a family of C⋆-modules:
`‖∑ i ∈ s, ⟪x i, y i⟫_A‖ ≤ √‖∑ i ∈ s, ⟪x i, x i⟫_A‖ * √‖∑ i ∈ s, ⟪y i, y i⟫_A‖`. -/
theorem norm_sum_inner_le (s : Finset ι) (x y : ∀ i, E i) :
    ‖∑ i ∈ s, inner A (x i) (y i)‖ ≤
      √‖∑ i ∈ s, inner A (x i) (x i)‖ * √‖∑ i ∈ s, inner A (y i) (y i)‖ := by
  let x' : WithCStarModule A (∀ i : s, E i) := (WithCStarModule.equiv A _).symm fun i ↦ x i
  let y' : WithCStarModule A (∀ i : s, E i) := (WithCStarModule.equiv A _).symm fun i ↦ y i
  have hxy : inner A x' y' = ∑ i ∈ s, inner A (x i) (y i) := by
    rw [WithCStarModule.pi_inner]
    exact Finset.sum_attach s fun i ↦ inner A (x i) (y i)
  have hx : ‖x'‖ = √‖∑ i ∈ s, inner A (x i) (x i)‖ := by
    rw [WithCStarModule.pi_norm]
    exact congrArg (fun a : A ↦ √‖a‖) (Finset.sum_attach s fun i ↦ inner A (x i) (x i))
  have hy : ‖y'‖ = √‖∑ i ∈ s, inner A (y i) (y i)‖ := by
    rw [WithCStarModule.pi_norm]
    exact congrArg (fun a : A ↦ √‖a‖) (Finset.sum_attach s fun i ↦ inner A (y i) (y i))
  rw [← hxy, ← hx, ← hy]
  exact norm_inner_le _

/-- Triangle inequality for the C⋆-module norm of finite coordinate sums:
`√‖∑ i ∈ s, ⟪x i + y i, x i + y i⟫_A‖ ≤ √‖∑ i ∈ s, ⟪x i, x i⟫_A‖ + √‖∑ i ∈ s, ⟪y i, y i⟫_A‖`. -/
theorem sqrt_norm_sum_inner_add_le (s : Finset ι) (x y : ∀ i, E i) :
    √‖∑ i ∈ s, inner A (x i + y i) (x i + y i)‖ ≤
      √‖∑ i ∈ s, inner A (x i) (x i)‖ + √‖∑ i ∈ s, inner A (y i) (y i)‖ := by
  let x' : WithCStarModule A (∀ i : s, E i) := (WithCStarModule.equiv A _).symm fun i ↦ x i
  let y' : WithCStarModule A (∀ i : s, E i) := (WithCStarModule.equiv A _).symm fun i ↦ y i
  have hxy : ‖x' + y'‖ = √‖∑ i ∈ s, inner A (x i + y i) (x i + y i)‖ := by
    rw [WithCStarModule.pi_norm]
    exact congrArg (fun a : A ↦ √‖a‖)
      (Finset.sum_attach s fun i ↦ inner A (x i + y i) (x i + y i))
  have hx : ‖x'‖ = √‖∑ i ∈ s, inner A (x i) (x i)‖ := by
    rw [WithCStarModule.pi_norm]
    exact congrArg (fun a : A ↦ √‖a‖) (Finset.sum_attach s fun i ↦ inner A (x i) (x i))
  have hy : ‖y'‖ = √‖∑ i ∈ s, inner A (y i) (y i)‖ := by
    rw [WithCStarModule.pi_norm]
    exact congrArg (fun a : A ↦ √‖a‖) (Finset.sum_attach s fun i ↦ inner A (y i) (y i))
  rw [← hxy, ← hx, ← hy]
  exact CStarModule.norm_triangle A x' y'

/-- If the diagonal inner products `⟪x i, x i⟫_A` and `⟪y i, y i⟫_A` are norm-summable in `A`,
then the off-diagonal inner products `⟪x i, y i⟫_A` are also norm-summable in `A`. -/
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

/-- Norm-summability of diagonal inner products is preserved under coordinatewise addition. -/
theorem summable_inner_add_self {x y : ∀ i, E i}
    (hx : Summable fun i ↦ inner A (x i) (x i))
    (hy : Summable fun i ↦ inner A (y i) (y i)) :
    Summable fun i ↦ inner A (x i + y i) (x i + y i) := by
  classical
  rw [summable_iff_vanishing_norm] at hx hy ⊢
  intro ε hε
  obtain ⟨s₁, hs₁⟩ := hx (ε / 8) (by positivity)
  obtain ⟨s₂, hs₂⟩ := hy (ε / 8) (by positivity)
  refine ⟨s₁ ∪ s₂, fun t ht ↦ ?_⟩
  have h₁ : √‖∑ i ∈ t, inner A (x i) (x i)‖ ≤ √(ε / 8) :=
    Real.sqrt_le_sqrt (hs₁ t (ht.mono_right subset_union_left)).le
  have h₂ : √‖∑ i ∈ t, inner A (y i) (y i)‖ ≤ √(ε / 8) :=
    Real.sqrt_le_sqrt (hs₂ t (ht.mono_right subset_union_right)).le
  have hsum : √‖∑ i ∈ t, inner A (x i + y i) (x i + y i)‖ ≤ 2 * √(ε / 8) := by
    calc √‖∑ i ∈ t, inner A (x i + y i) (x i + y i)‖
        ≤ √‖∑ i ∈ t, inner A (x i) (x i)‖ + √‖∑ i ∈ t, inner A (y i) (y i)‖ :=
          sqrt_norm_sum_inner_add_le t x y
      _ ≤ √(ε / 8) + √(ε / 8) := add_le_add h₁ h₂
      _ = 2 * √(ε / 8) := (two_mul _).symm
  calc ‖∑ i ∈ t, inner A (x i + y i) (x i + y i)‖
      = (√‖∑ i ∈ t, inner A (x i + y i) (x i + y i)‖) ^ 2 :=
        (Real.sq_sqrt (norm_nonneg _)).symm
    _ ≤ (2 * √(ε / 8)) ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) hsum 2
    _ = ε / 2 := by
        rw [mul_pow, Real.sq_sqrt (by positivity)]
        ring
    _ < ε := half_lt_self hε

end CStarModule

/-! ### Hilbert direct sums over arbitrary index sets -/

namespace TauCeti

/-- The Hilbert direct sum `⊕ᵢ E i` of a family of `CStarModule`s over `A`, consisting of
dependent families `x : ∀ i, E i` whose diagonal inner products `⟪x i, x i⟫_A` are norm-summable
in `A`. For right Hilbert `B`-modules, take `A = Bᵐᵒᵖ`. -/
structure HilbertDirectSum (A : Type*) {ι : Type*} (E : ι → Type*)
    [TopologicalSpace A] [AddCommMonoid A] [∀ i, Inner A (E i)] where
  /-- The underlying coordinate family. -/
  toFun : ∀ i, E i
  /-- Norm-summability of the diagonal inner products `⟪x i, x i⟫_A` in `A`. -/
  summable_inner_self' : Summable fun i ↦ inner A (toFun i) (toFun i)

namespace HilbertDirectSum

section DFunLike

variable {A ι : Type*} {E : ι → Type*}
  [TopologicalSpace A] [AddCommMonoid A] [∀ i, Inner A (E i)]

instance instDFunLike : DFunLike (HilbertDirectSum A E) ι E where
  coe x := x.toFun
  coe_injective x y h := by cases x; cases y; congr

@[simp]
theorem mk_apply (f : ∀ i, E i) (hf : Summable fun i ↦ inner A (f i) (f i)) (i : ι) :
    (⟨f, hf⟩ : HilbertDirectSum A E) i = f i := (rfl)

@[ext]
theorem ext {x y : HilbertDirectSum A E} (h : ∀ i, x i = y i) : x = y :=
  DFunLike.ext x y h

/-- The diagonal inner products `⟪x i, x i⟫_A` of any `x : HilbertDirectSum A E` are
norm-summable in `A`. -/
theorem summable_inner_self (x : HilbertDirectSum A E) :
    Summable fun i ↦ inner A (x i) (x i) :=
  x.summable_inner_self'

instance instInner : Inner A (HilbertDirectSum A E) where
  inner x y := ∑' i, inner A (x i) (y i)

theorem inner_def (x y : HilbertDirectSum A E) :
    inner A x y = ∑' i, inner A (x i) (y i) := (rfl)

theorem unop_inner_def {B : Type*} {F : ι → Type*}
    [TopologicalSpace B] [T2Space B] [AddCommMonoid B] [∀ i, Inner Bᵐᵒᵖ (F i)]
    (x y : HilbertDirectSum Bᵐᵒᵖ F) :
    unop (inner Bᵐᵒᵖ x y) = ∑' i, unop (inner Bᵐᵒᵖ (x i) (y i)) :=
  tsum_unop.symm

end DFunLike

section Norm

variable {A ι : Type*} {E : ι → Type*}
  [TopologicalSpace A] [AddCommMonoid A] [Norm A] [∀ i, Inner A (E i)]

instance instNorm : Norm (HilbertDirectSum A E) where
  norm x := √‖inner A x x‖

theorem norm_def (x : HilbertDirectSum A E) :
    ‖x‖ = √‖∑' i, inner A (x i) (x i)‖ := (rfl)

end Norm

section Algebraic

variable {A ι : Type*} {E : ι → Type*}
  [NonUnitalCStarAlgebra A] [PartialOrder A]
  [∀ i, NormedAddCommGroup (E i)] [∀ i, Module ℂ (E i)]
  [∀ i, SMul A (E i)] [∀ i, CStarModule A (E i)]

instance instZero : Zero (HilbertDirectSum A E) where
  zero := ⟨0, by simp [summable_zero]⟩

instance instNeg : Neg (HilbertDirectSum A E) where
  neg x := ⟨fun i ↦ -x i, by simpa using x.summable_inner_self⟩

instance instSMulComplex : SMul ℂ (HilbertDirectSum A E) where
  smul c x := ⟨fun i ↦ c • x i, by
    have h : (fun i ↦ inner A (c • x i) (c • x i)) =
        fun i ↦ (star c * c) • inner A (x i) (x i) := by
      ext i; simp [smul_smul, mul_comm]
    rw [h]
    exact x.summable_inner_self.const_smul (star c * c)⟩

instance instSMulNat : SMul ℕ (HilbertDirectSum A E) where
  smul n x := ⟨fun i ↦ n • x i, by
    have h : (fun i ↦ inner A (n • x i) (n • x i)) =
        fun i ↦ inner A ((n : ℂ) • x i) ((n : ℂ) • x i) := by
      ext i; rw [Nat.cast_smul_eq_nsmul]
    rw [h]
    exact ((n : ℂ) • x).summable_inner_self⟩

instance instSMulInt : SMul ℤ (HilbertDirectSum A E) where
  smul z x := ⟨fun i ↦ z • x i, by
    have h : (fun i ↦ inner A (z • x i) (z • x i)) =
        fun i ↦ inner A ((z : ℂ) • x i) ((z : ℂ) • x i) := by
      ext i; rw [Int.cast_smul_eq_zsmul]
    rw [h]
    exact ((z : ℂ) • x).summable_inner_self⟩

instance instSMulCoeff : SMul A (HilbertDirectSum A E) where
  smul a x := ⟨fun i ↦ a • x i, by
    have h : (fun i ↦ inner A (a • x i) (a • x i)) =
        fun i ↦ ContinuousLinearMap.mulLeftRight ℂ A a (star a) (inner A (x i) (x i)) := by
      ext i
      simp [CStarModule.inner_op_smul_left, mul_assoc]
    rw [h]
    exact (ContinuousLinearMap.mulLeftRight ℂ A a (star a)).summable x.summable_inner_self⟩

@[simp] theorem zero_apply (i : ι) : (0 : HilbertDirectSum A E) i = 0 := (rfl)
@[simp] theorem neg_apply (x : HilbertDirectSum A E) (i : ι) : (-x) i = -x i := (rfl)
@[simp] theorem smul_complex_apply (c : ℂ) (x : HilbertDirectSum A E) (i : ι) :
    (c • x) i = c • x i := (rfl)
@[simp] theorem smul_coeff_apply (a : A) (x : HilbertDirectSum A E) (i : ι) :
    (a • x) i = a • x i := (rfl)

end Algebraic

section CStarModule

variable {A ι : Type*} {E : ι → Type*}
  [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [∀ i, NormedAddCommGroup (E i)] [∀ i, Module ℂ (E i)]
  [∀ i, SMul A (E i)] [∀ i, CStarModule A (E i)]

/-- For `x, y : HilbertDirectSum A E`, the coordinatewise inner products `⟪x i, y i⟫_A` are
norm-summable in `A`. -/
theorem summable_inner (x y : HilbertDirectSum A E) :
    Summable fun i ↦ inner A (x i) (y i) :=
  CStarModule.summable_inner_of_summable_inner_self x.summable_inner_self y.summable_inner_self

instance instAdd : Add (HilbertDirectSum A E) where
  add x y := ⟨fun i ↦ x i + y i,
    CStarModule.summable_inner_add_self x.summable_inner_self y.summable_inner_self⟩

instance instSub : Sub (HilbertDirectSum A E) where
  sub x y := x + -y

@[simp] theorem add_apply (x y : HilbertDirectSum A E) (i : ι) : (x + y) i = x i + y i := (rfl)
@[simp] theorem sub_apply (x y : HilbertDirectSum A E) (i : ι) : (x - y) i = x i - y i :=
  sub_eq_add_neg (x i) (y i) |>.symm

instance instAddCommGroup : AddCommGroup (HilbertDirectSum A E) :=
  DFunLike.coe_injective.addCommGroup _
    (rfl) (fun _ _ ↦ rfl) (fun _ ↦ rfl) (fun x y ↦ funext fun i ↦ sub_apply x y i)
    (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)

instance instModuleComplex : Module ℂ (HilbertDirectSum A E) :=
  DFunLike.coe_injective.module ℂ ⟨⟨DFunLike.coe, rfl⟩, fun _ _ ↦ rfl⟩ fun _ _ ↦ rfl

theorem hasSum_inner (x y : HilbertDirectSum A E) :
    HasSum (fun i ↦ inner A (x i) (y i)) (inner A x y) :=
  (summable_inner x y).hasSum

theorem hasSum_unop_inner {B : Type*} {F : ι → Type*}
    [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
    [∀ i, NormedAddCommGroup (F i)] [∀ i, Module ℂ (F i)]
    [∀ i, SMul Bᵐᵒᵖ (F i)] [∀ i, CStarModule Bᵐᵒᵖ (F i)] (x y : HilbertDirectSum Bᵐᵒᵖ F) :
    HasSum (fun i ↦ unop (inner Bᵐᵒᵖ (x i) (y i))) (unop (inner Bᵐᵒᵖ x y)) :=
  (hasSum_inner x y).unop

instance instCStarModule : CStarModule A (HilbertDirectSum A E) where
  inner_add_right {x y z} := by
    simp only [inner_def, add_apply, CStarModule.inner_add_right]
    exact (summable_inner x y).tsum_add (summable_inner x z)
  inner_self_nonneg {x} := tsum_nonneg fun i ↦ CStarModule.inner_self_nonneg
  inner_self {x} := by
    refine ⟨fun h ↦ ?_, fun h ↦ by simp [h, inner_def]⟩
    ext i
    refine (CStarModule.inner_self (A := A)).mp (le_antisymm ?_ CStarModule.inner_self_nonneg)
    exact (x.summable_inner_self.le_tsum i fun _ _ ↦ CStarModule.inner_self_nonneg).trans_eq h
  inner_op_smul_right {a x y} := by
    simp only [inner_def, smul_coeff_apply, CStarModule.inner_op_smul_right]
    exact ((ContinuousLinearMap.mul ℂ A a).map_tsum (summable_inner x y)).symm
  inner_smul_right_complex {c x y} := by
    simp only [inner_def, smul_complex_apply, CStarModule.inner_smul_right_complex]
    exact (summable_inner x y).tsum_const_smul c
  star_inner x y := by
    rw [inner_def, inner_def, ← (summable_inner x y).hasSum.star.tsum_eq]
    simp_rw [CStarModule.star_inner]
  norm_eq_sqrt_norm_inner_self _ := (rfl)

instance instNormedAddCommGroup : NormedAddCommGroup (HilbertDirectSum A E) :=
  NormedAddCommGroup.ofCore (CStarModule.normedSpaceCore A)

instance instNormedSpaceComplex : NormedSpace ℂ (HilbertDirectSum A E) :=
  NormedSpace.ofCore (CStarModule.normedSpaceCore A)

instance instIsScalarTowerComplex : IsScalarTower ℂ A (HilbertDirectSum A E) :=
  CStarModule.isScalarTower A (HilbertDirectSum A E)

instance instSMulCommClassComplex : SMulCommClass ℂ A (HilbertDirectSum A E) :=
  CStarModule.smulCommClass A (HilbertDirectSum A E)

instance instSMulCommClassCoeffComplex : SMulCommClass A ℂ (HilbertDirectSum A E) :=
  SMulCommClass.symm ℂ A (HilbertDirectSum A E)

/-- Every finite partial sum of diagonal inner products is bounded above by the full inner
product `⟪x, x⟫_A` in the C⋆-algebra order. -/
theorem sum_inner_self_le (s : Finset ι) (x : HilbertDirectSum A E) :
    ∑ i ∈ s, inner A (x i) (x i) ≤ inner A x x :=
  x.summable_inner_self.sum_le_tsum s fun _ _ ↦ CStarModule.inner_self_nonneg

/-- Every finite partial sum of diagonal inner products has norm at most `‖x‖ ^ 2`. -/
theorem norm_sum_inner_self_le_norm_sq (s : Finset ι) (x : HilbertDirectSum A E) :
    ‖∑ i ∈ s, inner A (x i) (x i)‖ ≤ ‖x‖ ^ 2 := by
  rw [CStarModule.norm_sq_eq A]
  refine CStarAlgebra.norm_le_norm_of_le_of_nonneg (sum_inner_self_le s x) ?_
  exact Finset.sum_nonneg fun _ _ ↦ CStarModule.inner_self_nonneg

/-- The finite-subset C⋆-module seminorm `√‖∑ i ∈ s, ⟪x i, x i⟫_A‖` is at most `‖x‖`. -/
theorem sqrt_norm_sum_inner_self_le_norm (s : Finset ι) (x : HilbertDirectSum A E) :
    √‖∑ i ∈ s, inner A (x i) (x i)‖ ≤ ‖x‖ := by
  calc √‖∑ i ∈ s, inner A (x i) (x i)‖
      ≤ √(‖x‖ ^ 2) := Real.sqrt_le_sqrt (norm_sum_inner_self_le_norm_sq s x)
    _ = ‖x‖ := Real.sqrt_sq (norm_nonneg x)

/-- Every coordinate of `x : HilbertDirectSum A E` has norm at most `‖x‖`. -/
theorem norm_apply_le (x : HilbertDirectSum A E) (i : ι) : ‖x i‖ ≤ ‖x‖ := by
  simpa [CStarModule.norm_eq_sqrt_norm_inner_self (A := A) (x i)] using
    sqrt_norm_sum_inner_self_le_norm {i} x

omit [StarOrderedRing A] in
/-- If `x : ∀ i, E i` lies in the Banach `ℓ²` sum (`Memℓp x 2`), then its diagonal inner products
`⟪x i, x i⟫_A` are norm-summable in `A`. -/
theorem _root_.Memℓp.summable_inner_self {x : ∀ i, E i} (hx : Memℓp x 2) :
    Summable fun i ↦ inner A (x i) (x i) := by
  have h2 : 0 < (2 : ℝ≥0∞).toReal := by norm_num
  refine Summable.of_norm ?_
  simpa [CStarModule.norm_sq_eq A] using (memℓp_gen_iff h2).mp hx

/-! #### Completeness -/

/-- If `u n i → lim i` for each coordinate `i` and `‖u m - u n‖ ≤ r` eventually in `n`, then
every finite subset `s` satisfies `√‖∑ i ∈ s, ⟪u m i - lim i, u m i - lim i⟫_A‖ ≤ r`. -/
private theorem sqrt_norm_sum_inner_sub_limit_le
    {u : ℕ → HilbertDirectSum A E} {lim : ∀ i, E i}
    (hlim : ∀ i, Tendsto (fun n ↦ u n i) atTop (𝓝 (lim i)))
    {m N : ℕ} {r : ℝ} (hr : ∀ n ≥ N, ‖u m - u n‖ ≤ r) (s : Finset ι) :
    √‖∑ i ∈ s, inner A (u m i - lim i) (u m i - lim i)‖ ≤ r := by
  have htend : Tendsto
      (fun n ↦ √‖∑ i ∈ s, inner A (u m i - u n i) (u m i - u n i)‖) atTop
      (𝓝 √‖∑ i ∈ s, inner A (u m i - lim i) (u m i - lim i)‖) := by
    refine (Real.continuous_sqrt.comp continuous_norm).tendsto _ |>.comp ?_
    refine tendsto_finsetSum s fun i _ ↦ ?_
    let _ : NormedSpace ℂ (E i) := .ofCore (CStarModule.normedSpaceCore A)
    have hsub : Tendsto (fun n ↦ u m i - u n i) atTop (𝓝 (u m i - lim i)) :=
      tendsto_const_nhds.sub (hlim i)
    exact CStarModule.continuous_inner.tendsto _ |>.comp (hsub.prodMk_nhds hsub)
  refine le_of_tendsto htend (eventually_atTop.mpr ⟨N, fun n hn ↦ ?_⟩)
  simpa only [sub_apply] using (sqrt_norm_sum_inner_self_le_norm s (u m - u n)).trans (hr n hn)

/-- The coordinatewise limit `lim` of a Cauchy sequence in `HilbertDirectSum A E` has
norm-summable diagonal inner products in `A`. -/
private theorem summable_inner_self_of_cauchySeq
    {u : ℕ → HilbertDirectSum A E} (hu : CauchySeq u) {lim : ∀ i, E i}
    (hlim : ∀ i, Tendsto (fun n ↦ u n i) atTop (𝓝 (lim i))) :
    Summable fun i ↦ inner A (lim i) (lim i) := by
  classical
  rw [summable_iff_vanishing_norm]
  intro ε hε
  set δ := √ε / 3
  have hδ : 0 < δ := by positivity
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hu δ hδ
  have hN_le : ∀ n ≥ N, ‖u N - u n‖ ≤ δ := fun n hn ↦
    (dist_eq_norm (u N) (u n) ▸ hN N le_rfl n hn).le
  obtain ⟨s₀, hs₀⟩ := (summable_iff_vanishing_norm.mp (u N).summable_inner_self) (δ ^ 2)
    (by positivity)
  refine ⟨s₀, fun t ht ↦ ?_⟩
  have h₁ : √‖∑ i ∈ t, inner A (lim i - u N i) (lim i - u N i)‖ ≤ δ := by
    have hsymm : (∑ i ∈ t, inner A (lim i - u N i) (lim i - u N i)) =
        ∑ i ∈ t, inner A (u N i - lim i) (u N i - lim i) :=
      Finset.sum_congr rfl fun i _ ↦ by
        rw [← neg_sub (u N i) (lim i), CStarModule.inner_neg_left, CStarModule.inner_neg_right,
          neg_neg]
    rw [hsymm]
    exact sqrt_norm_sum_inner_sub_limit_le hlim hN_le t
  have h₂ : √‖∑ i ∈ t, inner A (u N i) (u N i)‖ ≤ δ :=
    (Real.sqrt_le_sqrt (hs₀ t ht).le).trans_eq (Real.sqrt_sq hδ.le)
  have h₃ : √‖∑ i ∈ t, inner A (lim i) (lim i)‖ ≤ 2 * δ := by
    calc √‖∑ i ∈ t, inner A (lim i) (lim i)‖
        = √‖∑ i ∈ t, inner A ((lim i - u N i) + u N i) ((lim i - u N i) + u N i)‖ := by
          simp only [sub_add_cancel]
      _ ≤ √‖∑ i ∈ t, inner A (lim i - u N i) (lim i - u N i)‖ +
          √‖∑ i ∈ t, inner A (u N i) (u N i)‖ :=
        CStarModule.sqrt_norm_sum_inner_add_le t (fun i ↦ lim i - u N i) (u N)
      _ ≤ δ + δ := add_le_add h₁ h₂
      _ = 2 * δ := (two_mul δ).symm
  calc ‖∑ i ∈ t, inner A (lim i) (lim i)‖
      = (√‖∑ i ∈ t, inner A (lim i) (lim i)‖) ^ 2 := (Real.sq_sqrt (norm_nonneg _)).symm
    _ ≤ (2 * δ) ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) h₃ 2
    _ = 4 / 9 * ε := by
        dsimp [δ]
        rw [mul_pow, div_pow, Real.sq_sqrt hε.le]
        ring
    _ < ε := by linarith

/-- `HilbertDirectSum A E` is complete whenever every summand `E i` is complete. -/
instance instCompleteSpace [∀ i, CompleteSpace (E i)] :
    CompleteSpace (HilbertDirectSum A E) := by
  refine Metric.complete_of_cauchySeq_tendsto fun u hu ↦ ?_
  have hu_coord : ∀ i, CauchySeq (fun n ↦ u n i) := fun i ↦ by
    rw [Metric.cauchySeq_iff] at hu ⊢
    intro ε hε
    obtain ⟨N, hN⟩ := hu ε hε
    exact ⟨N, fun m hm n hn ↦ (by
      rw [dist_eq_norm, ← sub_apply]
      exact (norm_apply_le (u m - u n) i).trans_lt (dist_eq_norm (u m) (u n) ▸ hN m hm n hn))⟩
  choose lim hlim using fun i ↦ cauchySeq_tendsto_of_complete (hu_coord i)
  let y : HilbertDirectSum A E := ⟨lim, summable_inner_self_of_cauchySeq hu hlim⟩
  refine ⟨y, Metric.tendsto_atTop.mpr fun ε hε ↦ ?_⟩
  set r := ε / 2
  have hr_pos : 0 < r := half_pos hε
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hu r hr_pos
  refine ⟨N, fun m hm ↦ ?_⟩
  have hm_le : ∀ n ≥ N, ‖u m - u n‖ ≤ r := fun n hn ↦
    (dist_eq_norm (u m) (u n) ▸ hN m hm n hn).le
  have htsum : ‖inner A (u m - y) (u m - y)‖ ≤ r ^ 2 := by
    refine le_of_tendsto (continuous_norm.tendsto _ |>.comp (u m - y).summable_inner_self.hasSum)
      (Eventually.of_forall fun s ↦ ?_)
    have hs := sqrt_norm_sum_inner_sub_limit_le hlim hm_le s
    calc ‖∑ i ∈ s, inner A ((u m - y) i) ((u m - y) i)‖
        = (√‖∑ i ∈ s, inner A (u m i - lim i) (u m i - lim i)‖) ^ 2 := by
          simp only [sub_apply, y, mk_apply]
          exact (Real.sq_sqrt (norm_nonneg _)).symm
      _ ≤ r ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) hs 2
  rw [dist_eq_norm, CStarModule.norm_eq_sqrt_norm_inner_self (A := A)]
  exact (Real.sqrt_le_sqrt htsum).trans_eq (Real.sqrt_sq hr_pos.le) |>.trans_lt (half_lt_self hε)

end CStarModule

section NormedSpace

variable {A ι : Type*} {E : ι → Type*}
  [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℂ (E i)]
  [∀ i, SMul A (E i)] [∀ i, CStarModule A (E i)]

/-! #### Coordinate inclusions, projections, truncations, and finite-support density -/

variable (A E) in
/-- Coordinate projection from `HilbertDirectSum A E` onto the `i`-th summand `E i`. -/
def evalCLM (i : ι) : HilbertDirectSum A E →L[ℂ] E i :=
  LinearMap.mkContinuous
    { toFun := fun x ↦ x i
      map_add' := fun x y ↦ add_apply x y i
      map_smul' := fun c x ↦ smul_complex_apply c x i }
    1 (fun x ↦ by simpa [one_mul] using norm_apply_le x i)

@[simp]
theorem evalCLM_apply (i : ι) (x : HilbertDirectSum A E) : evalCLM A E i x = x i := (rfl)

theorem evalCLM_smul (i : ι) (a : A) (x : HilbertDirectSum A E) :
    evalCLM A E i (a • x) = a • evalCLM A E i x := (rfl)

theorem norm_evalCLM_le (i : ι) : ‖evalCLM A E i‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

variable (A E) in
/-- Coordinate inclusion of the `i`-th summand `E i` into `HilbertDirectSum A E` as a complex
linear isometry. -/
def single [DecidableEq ι] (i : ι) : E i →ₗᵢ[ℂ] HilbertDirectSum A E where
  toLinearMap :=
    { toFun := fun y ↦ ⟨Pi.single i y, summable_of_ne_finset_zero (s := {i}) fun j hj ↦ by
        rw [Finset.mem_singleton] at hj
        simp [Pi.single_eq_of_ne hj]⟩
      map_add' := fun y₁ y₂ ↦ by ext j; exact congrFun (Pi.single_add i y₁ y₂) j
      map_smul' := fun c y ↦ by ext j; exact congrFun (Pi.single_smul i c y) j }
  norm_map' y := by
    rw [norm_def, tsum_eq_single i (fun j hj ↦ by simp [Pi.single_eq_of_ne hj])]
    simp [CStarModule.norm_eq_sqrt_norm_inner_self (A := A) y]

theorem single_apply [DecidableEq ι] (i : ι) (y : E i) (j : ι) :
    single A E i y j = Pi.single i y j := (rfl)

@[simp]
theorem single_apply_same [DecidableEq ι] (i : ι) (y : E i) :
    single A E i y i = y :=
  Pi.single_eq_same i y

@[simp]
theorem single_apply_of_ne [DecidableEq ι] {i j : ι} (h : j ≠ i) (y : E i) :
    single A E i y j = 0 :=
  Pi.single_eq_of_ne h y

@[simp]
theorem inner_single_left [DecidableEq ι] (i : ι) (y : E i) (x : HilbertDirectSum A E) :
    inner A (single A E i y) x = inner A y (x i) := by
  rw [inner_def, tsum_eq_single i (fun j hj ↦ by simp [single_apply_of_ne hj])]
  simp

@[simp]
theorem inner_single_right [DecidableEq ι] (x : HilbertDirectSum A E) (i : ι) (y : E i) :
    inner A x (single A E i y) = inner A (x i) y := by
  rw [inner_def, tsum_eq_single i (fun j hj ↦ by simp [single_apply_of_ne hj])]
  simp

/-- The `i`-th coordinate inclusion and projection on `HilbertDirectSum A E` form a C⋆-module
adjoint pair. -/
theorem isAdjointPair_single_evalCLM [DecidableEq ι] (i : ι) :
    LinearMap.IsAdjointPair (CStarModule.innerₛₗ (A := A)).flip
      (CStarModule.innerₛₗ (A := A)).flip (single A E i) (evalCLM A E i) :=
  CStarModule.isAdjointPair_inner_iff.mpr fun y x ↦ by
    simpa only [evalCLM_apply] using inner_single_left i y x

@[simp]
theorem single_smul [DecidableEq ι] (i : ι) (a : A) (y : E i) :
    single A E i (a • y) = a • single A E i y :=
  (isAdjointPair_single_evalCLM i).map_smul_coeff_cstarModule a y

variable (A E) in
/-- Orthogonal projection onto the coordinates in a finite subset `s : Finset ι`. -/
def trunc [DecidableEq ι] (s : Finset ι) : HilbertDirectSum A E →L[ℂ] HilbertDirectSum A E :=
  ∑ i ∈ s, (single A E i).toContinuousLinearMap.comp (evalCLM A E i)

theorem trunc_eq_sum_single [DecidableEq ι] (s : Finset ι) (x : HilbertDirectSum A E) :
    trunc A E s x = ∑ i ∈ s, single A E i (x i) := by
  simp [trunc]

@[simp]
theorem trunc_apply [DecidableEq ι] (s : Finset ι) (x : HilbertDirectSum A E) (i : ι) :
    trunc A E s x i = if i ∈ s then x i else 0 := by
  rw [trunc_eq_sum_single]
  have hcoe : ∀ z : HilbertDirectSum A E, z i = evalCLM A E i z := fun _ ↦ rfl
  rw [hcoe, map_sum]
  by_cases hi : i ∈ s
  · simp only [hi, ↓reduceIte]
    rw [Finset.sum_eq_single i
      (fun j _ hji ↦ by simp [single_apply_of_ne hji.symm])
      (fun hni ↦ absurd hi hni)]
    simp
  · simp only [hi, ↓reduceIte]
    refine Finset.sum_eq_zero fun j hj ↦ ?_
    have hij : i ≠ j := fun h ↦ hi (h ▸ hj)
    simp [single_apply_of_ne hij]

theorem inner_trunc_left [DecidableEq ι] (s : Finset ι) (x y : HilbertDirectSum A E) :
    inner A (trunc A E s x) y = ∑ i ∈ s, inner A (x i) (y i) := by
  rw [trunc_eq_sum_single, CStarModule.inner_sum_left (A := A)]
  simp

theorem inner_trunc_right [DecidableEq ι] (s : Finset ι) (x y : HilbertDirectSum A E) :
    inner A x (trunc A E s y) = ∑ i ∈ s, inner A (x i) (y i) := by
  rw [trunc_eq_sum_single, CStarModule.inner_sum_right (A := A)]
  simp

/-- Every finite-coordinate truncation `trunc A E s` is self-adjoint as a C⋆-module operator. -/
theorem isAdjointPair_trunc [DecidableEq ι] (s : Finset ι) :
    LinearMap.IsAdjointPair (CStarModule.innerₛₗ (A := A)).flip
      (CStarModule.innerₛₗ (A := A)).flip (trunc A E s) (trunc A E s) :=
  CStarModule.isAdjointPair_inner_iff.mpr fun x y ↦
    (inner_trunc_left s x y).trans (inner_trunc_right s x y).symm

@[simp]
theorem trunc_smul [DecidableEq ι] (s : Finset ι) (a : A) (x : HilbertDirectSum A E) :
    trunc A E s (a • x) = a • trunc A E s x :=
  (isAdjointPair_trunc s).map_smul_coeff_cstarModule a x

@[simp]
theorem trunc_trunc [DecidableEq ι] (s : Finset ι) (x : HilbertDirectSum A E) :
    trunc A E s (trunc A E s x) = trunc A E s x := by
  ext i
  by_cases hi : i ∈ s <;> simp [trunc_apply, hi]

theorem norm_trunc_apply_le [DecidableEq ι] (s : Finset ι) (x : HilbertDirectSum A E) :
    ‖trunc A E s x‖ ≤ ‖x‖ := by
  rw [CStarModule.norm_eq_sqrt_norm_inner_self (A := A), inner_trunc_left]
  have hdiag : (∑ i ∈ s, inner A (x i) (trunc A E s x i)) = ∑ i ∈ s, inner A (x i) (x i) :=
    Finset.sum_congr rfl fun i hi ↦ by simp [trunc_apply, hi]
  rw [hdiag]
  exact sqrt_norm_sum_inner_self_le_norm s x

theorem norm_trunc_le [DecidableEq ι] (s : Finset ι) : ‖trunc A E s‖ ≤ 1 :=
  (trunc A E s).opNorm_le_bound zero_le_one fun x ↦ by
    simpa only [one_mul] using norm_trunc_apply_le s x

/-- Every vector `x : HilbertDirectSum A E` is the unconditional norm sum of its coordinate
vectors `single A E i (x i)`. -/
theorem hasSum_single [DecidableEq ι] (x : HilbertDirectSum A E) :
    HasSum (fun i ↦ single A E i (x i)) x := by
  rw [HasSum, tendsto_iff_norm_sub_tendsto_zero]
  have hnorm : ∀ s : Finset ι,
      ‖∑ i ∈ s, single A E i (x i) - x‖ = √‖inner A x x - ∑ i ∈ s, inner A (x i) (x i)‖ :=
    fun s ↦ by
      rw [← trunc_eq_sum_single, CStarModule.norm_eq_sqrt_norm_inner_self (A := A)]
      congr 2
      have h₁ : inner A (trunc A E s x) (trunc A E s x) = ∑ i ∈ s, inner A (x i) (x i) := by
        rw [inner_trunc_left]
        exact Finset.sum_congr rfl fun i hi ↦ by simp [trunc_apply, hi]
      simp only [CStarModule.inner_sub_left (A := A), CStarModule.inner_sub_right (A := A), h₁,
        inner_trunc_left, inner_trunc_right]
      abel
  simp_rw [hnorm]
  have hlim : Tendsto (fun s : Finset ι ↦ ‖inner A x x - ∑ i ∈ s, inner A (x i) (x i)‖)
      (SummationFilter.unconditional ι).filter (𝓝 0) := by
    simpa only [norm_sub_rev] using tendsto_iff_norm_sub_tendsto_zero.mp (hasSum_inner x x)
  simpa [Function.comp_def] using (Real.continuous_sqrt.tendsto 0).comp hlim

/-- Finite-coordinate truncations `trunc A E s x` converge in norm to `x` along `atTop`. -/
theorem tendsto_trunc [DecidableEq ι] (x : HilbertDirectSum A E) :
    Tendsto (fun s : Finset ι ↦ trunc A E s x) atTop (𝓝 x) := by
  have h := x.hasSum_single
  rwa [HasSum, SummationFilter.unconditional_filter,
    funext fun s ↦ (trunc_eq_sum_single s x).symm] at h

variable (A E) in
/-- Complex-linear inclusion of finitely supported dependent families `Π₀ i, E i` into
`HilbertDirectSum A E`. -/
def ofDFinsupp [DecidableEq ι] : (Π₀ i, E i) →ₗ[ℂ] HilbertDirectSum A E :=
  DFinsupp.lsum ℂ fun i ↦ (single A E i).toLinearMap

@[simp]
theorem ofDFinsupp_single [DecidableEq ι] (i : ι) (y : E i) :
    ofDFinsupp A E (DFinsupp.single i y) = single A E i y := by
  simp [ofDFinsupp]

@[simp]
theorem ofDFinsupp_apply [DecidableEq ι] (f : Π₀ i, E i) (i : ι) :
    ofDFinsupp A E f i = f i := by
  induction f using DFinsupp.induction with
  | h0 => simp
  | ha j y g hj hy ih =>
    simp only [map_add, ofDFinsupp_single, add_apply, ih, DFinsupp.add_apply]
    by_cases h : i = j
    · subst h; simp
    · rw [single_apply_of_ne h, DFinsupp.single_eq_of_ne h]

/-- Finitely supported families form a dense complex subspace of `HilbertDirectSum A E`. -/
theorem denseRange_ofDFinsupp [DecidableEq ι] : DenseRange (ofDFinsupp A E) := by
  intro x
  refine mem_closure_of_tendsto (tendsto_trunc x) (Eventually.of_forall fun s ↦ ?_)
  refine ⟨∑ i ∈ s, DFinsupp.single i (x i), ?_⟩
  simp [map_sum, trunc_eq_sum_single]

/-- Elements with finite coordinate support are dense in `HilbertDirectSum A E`. -/
theorem dense_setOf_finite_support :
    Dense {x : HilbertDirectSum A E | {i | x i ≠ 0}.Finite} := by
  classical
  refine denseRange_ofDFinsupp.mono ?_
  rintro _ ⟨f, rfl⟩
  refine f.finite_support.subset fun i hi ↦ ?_
  simpa [ofDFinsupp_apply] using hi

/-! #### Agreement with Mathlib's finite `WithCStarModule` product -/

section Finite

variable [Fintype ι]

variable (A E) in
/-- When `ι` is finite, `HilbertDirectSum A E` agrees with Mathlib's finite orthogonal sum
`C⋆ᵐᵒᵈ(A, Π i, E i)` via an `A`-equivariant, inner-product-preserving complex linear isometric
equivalence. -/
def equivWithCStarModulePi : HilbertDirectSum A E ≃ₗᵢ[ℂ] C⋆ᵐᵒᵈ(A, Π i, E i) where
  toFun x := (WithCStarModule.equiv A (Π i, E i)).symm ⇑x
  invFun z := ⟨⇑z, hasSum_fintype (fun i ↦ inner A (z i) (z i)) |>.summable⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv x := by ext i; rfl
  right_inv z := by refine WithCStarModule.ext fun i ↦ rfl
  norm_map' x := by
    rw [WithCStarModule.pi_norm, norm_def, tsum_fintype]
    rfl

@[simp]
theorem equivWithCStarModulePi_apply (x : HilbertDirectSum A E) (i : ι) :
    equivWithCStarModulePi A E x i = x i := (rfl)

@[simp]
theorem equivWithCStarModulePi_symm_apply (z : C⋆ᵐᵒᵈ(A, Π i, E i)) (i : ι) :
    (equivWithCStarModulePi A E).symm z i = z i := (rfl)

@[simp]
theorem inner_equivWithCStarModulePi (x y : HilbertDirectSum A E) :
    inner A (equivWithCStarModulePi A E x) (equivWithCStarModulePi A E y) = inner A x y := by
  rw [WithCStarModule.pi_inner, inner_def, tsum_fintype]
  rfl

@[simp]
theorem equivWithCStarModulePi_smul (a : A) (x : HilbertDirectSum A E) :
    equivWithCStarModulePi A E (a • x) = a • equivWithCStarModulePi A E x := by
  refine WithCStarModule.ext fun i ↦ rfl

@[simp]
theorem equivWithCStarModulePi_single [DecidableEq ι] (i : ι) (y : E i) :
    equivWithCStarModulePi A E (single A E i y) = WithCStarModule.single A E i y := by
  refine WithCStarModule.ext fun j ↦ rfl

end Finite

/-! #### Contractive dense embedding of the Banach `ℓ²` sum `lp E 2` -/

variable (A E) in
/-- The Banach `ℓ²` space `lp E 2` of families with `∑' i, ‖x i‖ ^ 2 < ∞` embeds contractively
into `HilbertDirectSum A E`. -/
def ofLp : lp E 2 →L[ℂ] HilbertDirectSum A E :=
  LinearMap.mkContinuous
    { toFun := fun x ↦ ⟨⇑x, x.prop.summable_inner_self⟩
      map_add' := fun _ _ ↦ by ext i; rfl
      map_smul' := fun _ _ ↦ by ext i; rfl }
    1 fun x ↦ by
      have h2 : 0 < (2 : ℝ≥0∞).toReal := by norm_num
      have hsum : Summable fun i ↦ ‖inner A (x i) (x i)‖ := by
        simpa [CStarModule.norm_sq_eq A] using (memℓp_gen_iff h2).mp x.prop
      have hsq : ‖∑' i, inner A (x i) (x i)‖ ≤ ‖x‖ ^ 2 := by
        calc ‖∑' i, inner A (x i) (x i)‖
            ≤ ∑' i, ‖inner A (x i) (x i)‖ := norm_tsum_le_tsum_norm hsum
          _ = ∑' i, ‖x i‖ ^ 2 := by simp_rw [CStarModule.norm_sq_eq A]
          _ = ‖x‖ ^ 2 := by
              simpa using (lp.norm_rpow_eq_tsum (p := 2) h2 x).symm
      simpa [one_mul, norm_def] using
        (Real.sqrt_le_sqrt hsq).trans_eq (Real.sqrt_sq (norm_nonneg x))

@[simp]
theorem ofLp_apply (x : lp E 2) (i : ι) : ofLp A E x i = x i := (rfl)

/-- The canonical inclusion `lp E 2 →L[ℂ] HilbertDirectSum A E` is a contraction. -/
theorem norm_ofLp_le : ‖ofLp A E‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

/-- The Hilbert direct sum norm of `ofLp A E x` is bounded above by the Banach `ℓ²` norm `‖x‖`. -/
theorem norm_ofLp_apply_le (x : lp E 2) : ‖ofLp A E x‖ ≤ ‖x‖ := by
  simpa only [one_mul] using (ofLp A E).le_of_opNorm_le norm_ofLp_le x

/-- The canonical inclusion `lp E 2 →L[ℂ] HilbertDirectSum A E` is injective. -/
theorem ofLp_injective : Function.Injective (ofLp A E) := fun x y h ↦ by
  ext i
  exact congrArg (fun z : HilbertDirectSum A E ↦ z i) h

@[simp]
theorem ofLp_single [DecidableEq ι] (i : ι) (y : E i) :
    ofLp A E (lp.single 2 i y) = single A E i y := by
  ext j; rfl

/-- The contractive inclusion `lp E 2 →L[ℂ] HilbertDirectSum A E` has dense range. -/
theorem denseRange_ofLp : DenseRange (ofLp A E) := by
  classical
  intro x
  refine mem_closure_of_tendsto (tendsto_trunc x) (Eventually.of_forall fun s ↦ ?_)
  exact ⟨∑ i ∈ s, lp.single 2 i (x i), by simp [map_sum, trunc_eq_sum_single]⟩

end NormedSpace

end HilbertDirectSum

end TauCeti
