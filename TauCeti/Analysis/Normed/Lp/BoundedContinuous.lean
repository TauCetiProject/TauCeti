/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Lp.LpEquiv
public import Mathlib.Analysis.Normed.Lp.PiLp
public import Mathlib.Topology.Algebra.ConstMulAction
public import TauCeti.Analysis.Normed.Lp.Dual
public import TauCeti.Analysis.Normed.Lp.LeftTranslation
import Mathlib.Analysis.Normed.Operator.Mul

/-!
# Bounded continuous functions in `ℓ∞` and the pairing with `ℓ¹`

Every bounded continuous function `f : α →ᵇ E` on an arbitrary topological space `α` is bounded as
a family of values, giving a linear isometry
`BoundedContinuousFunction.toLpInfty 𝕜 : (α →ᵇ E) →ₗᵢ[𝕜] lp (fun _ : α ↦ E) ∞` without any
discreteness hypothesis on `α`. When `α` is discrete, this is the inverse of Mathlib's isometric
equivalence `lpBCFₗᵢ`, and composing it with `lp.dualEquiv` identifies `α →ᵇ 𝕜` isometrically with
the continuous dual of `ℓ¹(α, 𝕜)` (`BoundedContinuousFunction.dualLpOneEquiv`).

Restricting `lp.dualPairing` along `BoundedContinuousFunction.toLpInfty` gives the continuous
bilinear pairing

```text
lp.pairingBCF 𝕜 : lp (fun _ : α ↦ 𝕜) 1 →L[𝕜] (α →ᵇ 𝕜) →L[𝕜] 𝕜,
lp.pairingBCF 𝕜 a f = ∑' x, a x * f x,
```

of norm at most one. On a point mass `lp.single 1 x c`, it evaluates `c * f x`. For a continuous
group action on `α`, left translation on `ℓ¹` is adjoint to precomposition on `α →ᵇ 𝕜`:
`lp.pairingBCF 𝕜 (L_g a) f = lp.pairingBCF 𝕜 a (x ↦ f (g • x))`.

## Main definitions

* `BoundedContinuousFunction.toLpInfty`: the isometric inclusion `(α →ᵇ E) →ₗᵢ[𝕜] ℓ∞(α, E)`.
* `BoundedContinuousFunction.dualLpOneEquiv`: on a discrete space, the linear isometry equivalence
  `(α →ᵇ 𝕜) ≃ₗᵢ[𝕜] StrongDual 𝕜 (ℓ¹(α, 𝕜))`.
* `lp.pairingBCF`: the continuous bilinear pairing between `ℓ¹(α, 𝕜)` and `α →ᵇ 𝕜`.
* `ContinuousLinearMap.piLpCoordBCF`: coordinate bounded functions `y ↦ Λ (PiLp.single p i δ_y)`
  associated to a continuous linear functional `Λ` on `PiLp p (fun _ : ι ↦ ℓ¹(α, 𝕜))`.

## Main results

* `BoundedContinuousFunction.leftTranslation_toLpInfty`: `toLpInfty` intertwines precomposition by
  `g⁻¹ • ·` with `lp.leftTranslation ∞`.
* `lp.norm_pairingBCF_le`, `lp.norm_pairingBCF_apply_le`: `‖lp.pairingBCF 𝕜‖ ≤ 1` and
  `‖lp.pairingBCF 𝕜 a f‖ ≤ ‖a‖ * ‖f‖`.
* `lp.pairingBCF_single`: `lp.pairingBCF 𝕜 (lp.single 1 x c) f = c * f x`.
* `lp.pairingBCF_leftTranslation`: adjointness of `lp.leftTranslation 1` with respect to
  `lp.pairingBCF`.
* `lp.pairingBCF_eq_dualLpOneEquiv`: on a discrete space, `lp.pairingBCF 𝕜 a f` coincides with
  `BoundedContinuousFunction.dualLpOneEquiv 𝕜 f a`.
* `ContinuousLinearMap.norm_piLpCoordBCF_le`, `ContinuousLinearMap.apply_eq_sum_pairingBCF`:
  each coordinate bounded function `Λ.piLpCoordBCF i` has norm at most `‖Λ‖`, and
  `Λ v = ∑ i, lp.pairingBCF 𝕜 (v i) (Λ.piLpCoordBCF i)`.
-/

public section

noncomputable section

open scoped ENNReal NNReal BoundedContinuousFunction

namespace BoundedContinuousFunction

section ToLpInfty

variable (𝕜 : Type*) {α E : Type*} [TopologicalSpace α] [NormedAddCommGroup E] [NormedRing 𝕜]
  [Module 𝕜 E] [IsBoundedSMul 𝕜 E]

/-- The inclusion of bounded continuous functions `α →ᵇ E` into `ℓ∞(α, E)`, as a linear isometry.
Unlike `lpBCFₗᵢ`, no discreteness assumption on `α` is needed. -/
def toLpInfty : (α →ᵇ E) →ₗᵢ[𝕜] lp (fun _ : α ↦ E) ∞ where
  toFun f := ⟨⇑f, f.bddAbove_range_norm_comp⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  norm_map' f := by
    rw [lp.norm_eq_ciSup, norm_eq_iSup_norm]
    rfl

variable {𝕜}

/-- The inclusion of `α →ᵇ E` into `ℓ∞(α, E)` preserves pointwise values. -/
@[simp]
theorem toLpInfty_apply (f : α →ᵇ E) (x : α) : toLpInfty 𝕜 f x = f x :=
  (rfl)

/-- On a discrete space, `toLpInfty` agrees with the inverse of Mathlib's `lpBCFₗᵢ`. -/
theorem toLpInfty_eq_lpBCFₗᵢ_symm {𝕜 : Type*} [DiscreteTopology α] [NontriviallyNormedField 𝕜]
    [NormedSpace 𝕜 E] (f : α →ᵇ E) : toLpInfty 𝕜 f = (lpBCFₗᵢ E 𝕜).symm f := by
  ext x
  rfl

/-- `toLpInfty` intertwines left translation on `ℓ∞` with precomposition by `x ↦ g⁻¹ • x`. -/
theorem leftTranslation_toLpInfty {G : Type*} [Group G] [MulAction G α] [ContinuousConstSMul G α]
    (g : G) (f : α →ᵇ E) :
    lp.leftTranslation ∞ 𝕜 g (toLpInfty 𝕜 f) =
      toLpInfty 𝕜 (f.compContinuous (Homeomorph.smul (α := α) g⁻¹ : C(α, α))) := by
  ext x
  simp

end ToLpInfty

section Dual

variable (𝕜 : Type*) {α : Type*} [TopologicalSpace α] [DiscreteTopology α] [RCLike 𝕜]

/-- On a discrete space, bounded functions `α →ᵇ 𝕜` are isometrically identified with the
continuous dual of `ℓ¹(α, 𝕜)` via `f ↦ (a ↦ ∑' x, f x * a x)`. -/
def dualLpOneEquiv : (α →ᵇ 𝕜) ≃ₗᵢ[𝕜] StrongDual 𝕜 (lp (fun _ : α ↦ 𝕜) 1) :=
  (lpBCFₗᵢ 𝕜 𝕜).symm.trans (lp.dualEquiv 𝕜 α ∞ 1 ENNReal.one_ne_top)

variable {𝕜}

/-- Evaluating `dualLpOneEquiv 𝕜 f` at `a ∈ ℓ¹` gives the series `∑' x, f x * a x`. -/
theorem dualLpOneEquiv_apply (f : α →ᵇ 𝕜) (a : lp (fun _ : α ↦ 𝕜) 1) :
    dualLpOneEquiv 𝕜 f a = ∑' x, f x * a x :=
  lp.dualEquiv_apply ENNReal.one_ne_top ((lpBCFₗᵢ 𝕜 𝕜).symm f) a

/-- Evaluating `dualLpOneEquiv 𝕜 f` at a point mass `lp.single 1 x c` gives `f x * c`. -/
@[simp]
theorem dualLpOneEquiv_apply_single [DecidableEq α] (f : α →ᵇ 𝕜) (x : α) (c : 𝕜) :
    dualLpOneEquiv 𝕜 f (lp.single 1 x c) = f x * c :=
  lp.dualEquiv_apply_single ENNReal.one_ne_top ((lpBCFₗᵢ 𝕜 𝕜).symm f) x c

/-- The inverse of `dualLpOneEquiv` recovers a bounded function from the values of a functional on
unit point masses `lp.single 1 x 1`. -/
@[simp]
theorem dualLpOneEquiv_symm_apply [DecidableEq α]
    (Λ : StrongDual 𝕜 (lp (fun _ : α ↦ 𝕜) 1)) (x : α) :
    (dualLpOneEquiv 𝕜).symm Λ x = Λ (lp.single 1 x 1) := by
  simp [dualLpOneEquiv, coe_lpBCFₗᵢ]

end Dual

end BoundedContinuousFunction

namespace lp

section PairingBCF

variable (𝕜 : Type*) {α : Type*} [TopologicalSpace α] [RCLike 𝕜]

private theorem opNorm_mul_le_one :
    ‖ContinuousLinearMap.mul 𝕜 𝕜‖ ≤ ((1 : ℝ≥0) : ℝ) := by
  simpa only [NNReal.coe_one] using ContinuousLinearMap.opNorm_mul_le 𝕜 𝕜

/-- The continuous bilinear pairing `(a, f) ↦ ∑' x, a x * f x` between `ℓ¹(α, 𝕜)` and bounded
continuous functions `α →ᵇ 𝕜`. -/
def pairingBCF : lp (fun _ : α ↦ 𝕜) 1 →L[𝕜] (α →ᵇ 𝕜) →L[𝕜] 𝕜 :=
  ((ContinuousLinearMap.compL 𝕜 (α →ᵇ 𝕜) (lp (fun _ : α ↦ 𝕜) ∞) 𝕜).flip
      (BoundedContinuousFunction.toLpInfty 𝕜).toContinuousLinearMap).comp
    (dualPairing (𝕜 := 𝕜) 1 ∞ (fun _ : α ↦ ContinuousLinearMap.mul 𝕜 𝕜)
      (fun _ ↦ opNorm_mul_le_one 𝕜))

variable {𝕜}

/-- The pairing of `a ∈ ℓ¹(α, 𝕜)` with `f : α →ᵇ 𝕜` is the sum `∑' x, a x * f x`. -/
theorem pairingBCF_apply (a : lp (fun _ : α ↦ 𝕜) 1) (f : α →ᵇ 𝕜) :
    pairingBCF 𝕜 a f = ∑' x, a x * f x := by
  simp [pairingBCF, dualPairing_apply]

/-- The bilinear pairing between `ℓ¹(α, 𝕜)` and `α →ᵇ 𝕜` has operator norm at most `1`. -/
theorem norm_pairingBCF_le : ‖pairingBCF (α := α) 𝕜‖ ≤ 1 := by
  have hdual :
      ‖dualPairing (𝕜 := 𝕜) 1 ∞ (fun _ : α ↦ ContinuousLinearMap.mul 𝕜 𝕜)
        (fun _ ↦ opNorm_mul_le_one 𝕜)‖ ≤ 1 := by
    simpa only [NNReal.coe_one] using
      norm_dualPairing (p := 1) (q := ∞) (fun _ : α ↦ ContinuousLinearMap.mul 𝕜 𝕜)
        (fun _ ↦ opNorm_mul_le_one 𝕜)
  have hcomp :
      ‖(ContinuousLinearMap.compL 𝕜 (α →ᵇ 𝕜) (lp (fun _ : α ↦ 𝕜) ∞) 𝕜).flip
          (BoundedContinuousFunction.toLpInfty 𝕜).toContinuousLinearMap‖ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun φ ↦ ?_
    rw [one_mul]
    exact (φ.opNorm_comp_le _).trans
      (mul_le_of_le_one_right (norm_nonneg φ) (LinearIsometry.norm_toContinuousLinearMap_le _))
  calc ‖pairingBCF (α := α) 𝕜‖
      ≤ ‖(ContinuousLinearMap.compL 𝕜 (α →ᵇ 𝕜) (lp (fun _ : α ↦ 𝕜) ∞) 𝕜).flip
          (BoundedContinuousFunction.toLpInfty 𝕜).toContinuousLinearMap‖ *
        ‖dualPairing (𝕜 := 𝕜) 1 ∞ (fun _ : α ↦ ContinuousLinearMap.mul 𝕜 𝕜)
          (fun _ ↦ opNorm_mul_le_one 𝕜)‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * 1 := by gcongr
    _ = 1 := one_mul 1

/-- The pairing of `a ∈ ℓ¹(α, 𝕜)` and `f : α →ᵇ 𝕜` has norm at most `‖a‖ * ‖f‖`. -/
theorem norm_pairingBCF_apply_le (a : lp (fun _ : α ↦ 𝕜) 1) (f : α →ᵇ 𝕜) :
    ‖pairingBCF 𝕜 a f‖ ≤ ‖a‖ * ‖f‖ :=
  calc ‖pairingBCF 𝕜 a f‖ ≤ ‖pairingBCF (α := α) 𝕜‖ * ‖a‖ * ‖f‖ := (pairingBCF 𝕜).le_opNorm₂ a f
    _ ≤ 1 * ‖a‖ * ‖f‖ := by gcongr; exact norm_pairingBCF_le
    _ = ‖a‖ * ‖f‖ := by rw [one_mul]

/-- Pairing a point mass `lp.single 1 x c` with `f : α →ᵇ 𝕜` gives `c * f x`. -/
@[simp]
theorem pairingBCF_single [DecidableEq α] (x : α) (c : 𝕜) (f : α →ᵇ 𝕜) :
    pairingBCF 𝕜 (lp.single 1 x c) f = c * f x := by
  simp [pairingBCF_apply, lp.single_apply, Pi.single_apply]

/-- Pairing `a ∈ ℓ¹` with the constant function `1` sums the coordinates of `a`. -/
@[simp]
theorem pairingBCF_one (a : lp (fun _ : α ↦ 𝕜) 1) :
    pairingBCF 𝕜 a 1 = ∑' x, a x := by
  simp [pairingBCF_apply]

/-- Pairing a nonnegative real `ℓ¹` sequence with a nonnegative bounded continuous function is
nonnegative. -/
theorem pairingBCF_nonneg {a : lp (fun _ : α ↦ ℝ) 1} {f : α →ᵇ ℝ}
    (ha : ∀ x, 0 ≤ a x) (hf : 0 ≤ f) : 0 ≤ pairingBCF ℝ a f :=
  tsum_nonneg fun x ↦ mul_nonneg (ha x) (hf x)

/-- For a continuous group action on `α`, left translation on `ℓ¹` moves to precomposition by
`x ↦ g • x` on `α →ᵇ 𝕜`. -/
theorem pairingBCF_leftTranslation {G : Type*} [Group G] [MulAction G α] [ContinuousConstSMul G α]
    (g : G) (a : lp (fun _ : α ↦ 𝕜) 1) (f : α →ᵇ 𝕜) :
    pairingBCF 𝕜 (leftTranslation 1 𝕜 g a) f =
      pairingBCF 𝕜 a (f.compContinuous (Homeomorph.smul (α := α) g : C(α, α))) := by
  have h := dualPairing_leftTranslation_left (p := 1) (q := ∞) (ContinuousLinearMap.mul 𝕜 𝕜)
    (opNorm_mul_le_one 𝕜) g a (BoundedContinuousFunction.toLpInfty 𝕜 f)
  simpa only [pairingBCF, ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.compL_apply, LinearIsometry.coe_toContinuousLinearMap,
    BoundedContinuousFunction.leftTranslation_toLpInfty, inv_inv] using h

/-- On a discrete space, `lp.pairingBCF` agrees with `BoundedContinuousFunction.dualLpOneEquiv`. -/
theorem pairingBCF_eq_dualLpOneEquiv [DiscreteTopology α] (a : lp (fun _ : α ↦ 𝕜) 1)
    (f : α →ᵇ 𝕜) :
    pairingBCF 𝕜 a f = BoundedContinuousFunction.dualLpOneEquiv 𝕜 f a := by
  rw [pairingBCF_apply, BoundedContinuousFunction.dualLpOneEquiv_apply]
  exact tsum_congr fun x ↦ mul_comm (a x) (f x)

end PairingBCF

end lp

namespace ContinuousLinearMap

section PiLpCoordBCF

variable {ι α 𝕜 : Type*} [Fintype ι] [TopologicalSpace α] [DiscreteTopology α]
  [RCLike 𝕜] {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The isometric inclusion of the `i`-th coordinate into `PiLp p (fun _ : ι ↦ E)`. -/
private def piLpSingleLI (p : ℝ≥0∞) [Fact (1 ≤ p)] (𝕜 : Type*) {E : Type*}
    [SeminormedAddCommGroup E] [Semiring 𝕜] [Module 𝕜 E] (i : ι) :
    E →ₗᵢ[𝕜] PiLp p (fun _ : ι ↦ E) :=
  open scoped Classical in
  { toLinearMap :=
      (WithLp.linearEquiv p 𝕜 (ι → E)).symm.toLinearMap.comp
        (LinearMap.single 𝕜 (fun _ : ι ↦ E) i)
    norm_map' := PiLp.norm_single p (fun _ : ι ↦ E) i }

private lemma piLpSingleLI_apply_same (p : ℝ≥0∞) [Fact (1 ≤ p)] (𝕜 : Type*) {E : Type*}
    [SeminormedAddCommGroup E] [Semiring 𝕜] [Module 𝕜 E] (i : ι) (x : E) :
    piLpSingleLI p 𝕜 i x i = x :=
  open scoped Classical in Pi.single_eq_same (M := fun _ : ι ↦ E) i x

private lemma piLpSingleLI_apply_ne (p : ℝ≥0∞) [Fact (1 ≤ p)] (𝕜 : Type*) {E : Type*}
    [SeminormedAddCommGroup E] [Semiring 𝕜] [Module 𝕜 E] {i j : ι} (h : j ≠ i) (x : E) :
    piLpSingleLI p 𝕜 i x j = 0 :=
  open scoped Classical in Pi.single_eq_of_ne (M := fun _ : ι ↦ E) h x

/-- For a continuous linear functional `Λ` on the finite `Lᵖ` product of `ℓ¹(α, 𝕜)` spaces, the
`i`-th coordinate bounded function `y ↦ Λ (PiLp.single p i (lp.single 1 y 1))`. -/
def piLpCoordBCF (Λ : StrongDual 𝕜 (PiLp p (fun _ : ι ↦ lp (fun _ : α ↦ 𝕜) 1))) (i : ι) :
    α →ᵇ 𝕜 :=
  (BoundedContinuousFunction.dualLpOneEquiv 𝕜).symm
    (Λ.comp (piLpSingleLI p 𝕜 i).toContinuousLinearMap)

/-- The `i`-th coordinate bounded function of `Λ` evaluates at `y` to
`Λ (PiLp.single p i (lp.single 1 y 1))`. -/
@[simp]
theorem piLpCoordBCF_apply [DecidableEq ι] [DecidableEq α]
    (Λ : StrongDual 𝕜 (PiLp p (fun _ : ι ↦ lp (fun _ : α ↦ 𝕜) 1))) (i : ι) (y : α) :
    Λ.piLpCoordBCF i y = Λ (PiLp.single p i (lp.single 1 y 1)) := by
  rw [piLpCoordBCF, BoundedContinuousFunction.dualLpOneEquiv_symm_apply]
  change Λ (piLpSingleLI p 𝕜 i (lp.single 1 y 1)) = _
  congr 1
  refine PiLp.ext fun j ↦ ?_
  by_cases h : j = i
  · subst h
    rw [piLpSingleLI_apply_same, PiLp.single_eq_same]
  · rw [piLpSingleLI_apply_ne p 𝕜 h, PiLp.single_eq_of_ne _ h]

/-- Each coordinate bounded function of `Λ` has supremum norm at most `‖Λ‖`. -/
theorem norm_piLpCoordBCF_le
    (Λ : StrongDual 𝕜 (PiLp p (fun _ : ι ↦ lp (fun _ : α ↦ 𝕜) 1))) (i : ι) :
    ‖Λ.piLpCoordBCF i‖ ≤ ‖Λ‖ := by
  rw [piLpCoordBCF, LinearIsometryEquiv.norm_map]
  exact (Λ.opNorm_comp_le _).trans
    (mul_le_of_le_one_right (norm_nonneg Λ) (LinearIsometry.norm_toContinuousLinearMap_le _))

/-- Every pointwise value of a coordinate bounded function of `Λ` has norm at most `‖Λ‖`. -/
theorem norm_piLpCoordBCF_apply_le
    (Λ : StrongDual 𝕜 (PiLp p (fun _ : ι ↦ lp (fun _ : α ↦ 𝕜) 1))) (i : ι) (y : α) :
    ‖Λ.piLpCoordBCF i y‖ ≤ ‖Λ‖ :=
  ((Λ.piLpCoordBCF i).norm_coe_le_norm y).trans (Λ.norm_piLpCoordBCF_le i)

/-- A continuous linear functional on `PiLp p (fun _ : ι ↦ ℓ¹(α, 𝕜))` is the sum over `i` of the
`ℓ¹`-pairings with its coordinate bounded functions `Λ.piLpCoordBCF i`. -/
theorem apply_eq_sum_pairingBCF
    (Λ : StrongDual 𝕜 (PiLp p (fun _ : ι ↦ lp (fun _ : α ↦ 𝕜) 1)))
    (v : PiLp p (fun _ : ι ↦ lp (fun _ : α ↦ 𝕜) 1)) :
    Λ v = ∑ i : ι, lp.pairingBCF 𝕜 (v i) (Λ.piLpCoordBCF i) := by
  have hv : v = ∑ i : ι, piLpSingleLI p 𝕜 i (v i) := by
    refine PiLp.ext fun j ↦ ?_
    rw [WithLp.ofLp_sum, Finset.sum_apply, Finset.sum_eq_single j]
    · exact (piLpSingleLI_apply_same p 𝕜 j (v j)).symm
    · intro i _ hij
      exact piLpSingleLI_apply_ne p 𝕜 hij.symm (v i)
    · intro hj
      exact absurd (Finset.mem_univ j) hj
  conv_lhs => rw [hv]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [lp.pairingBCF_eq_dualLpOneEquiv]
  have h := congrArg (fun φ : StrongDual 𝕜 (lp (fun _ : α ↦ 𝕜) 1) ↦ φ (v i))
    ((BoundedContinuousFunction.dualLpOneEquiv 𝕜).apply_symm_apply
      (Λ.comp (piLpSingleLI p 𝕜 i).toContinuousLinearMap))
  exact h.symm

end PiLpCoordBCF

end ContinuousLinearMap
