/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Lp.LpEquiv
public import TauCeti.Analysis.Normed.Lp.Dual
public import TauCeti.Analysis.Normed.Lp.Finsupp
public import TauCeti.Analysis.Normed.Lp.PiLp
import TauCeti.Analysis.Normed.Lp.Basic
import TauCeti.Topology.ContinuousMap.Bounded.Normed

/-!
# Bounded continuous functions in `ℓ∞` and their pairing with `ℓ¹`

On any topological space `α`, every bounded continuous function `f : α →ᵇ E` has bounded pointwise
norms (`BoundedContinuousFunction.bddAbove_range_norm_comp`) and supremum norm
`‖f‖ = ⨆ x, ‖f x‖` (`BoundedContinuousFunction.norm_eq_iSup_norm`). Unlike Mathlib's `lpBCFₗᵢ`,
which assumes `[DiscreteTopology α]` to obtain surjectivity, the forward inclusion into
`lp (fun _ : α ↦ E) ∞` is a linear isometry on every topological space
(`BoundedContinuousFunction.toLpInfty`).

Pairing `u ∈ ℓ¹(α, 𝕜)` with `f : α →ᵇ E` into a complete normed space `E` over a nontrivially
normed field `𝕜` by the absolutely convergent series `∑' x, u x • f x` defines the continuous
bilinear map `lp.bcfPairing 𝕜 α E : lp (fun _ : α ↦ 𝕜) 1 →L[𝕜] (α →ᵇ E) →L[𝕜] E`, of operator
norm at most `1`. On a finitely supported probability `s : Convexity.StdSimplex ℝ α`,
`bcfPairing ℝ α ℝ (s.toLp 1)` is a positive normalized functional of norm at most `1` evaluating
`f` to `s.weights.sum fun x r ↦ r * f x`.

When `α` carries the discrete topology and `𝕜` is `ℝ` or `ℂ`, `toLpInfty` is surjective (`lpBCFₗᵢ`)
and `lp.dualEquiv` identifies `ℓ∞(α, 𝕜)` with the strong dual of `ℓ¹(α, 𝕜)`, giving the isometric
identification `lp.bcfDualEquiv : (α →ᵇ 𝕜) ≃ₗᵢ[𝕜] StrongDual 𝕜 (lp (fun _ : α ↦ 𝕜) 1)` whose
inverse evaluates a functional on the unit coordinate vectors `lp.single 1 x 1`. Pulling back a
continuous linear functional `Λ` on a finite `Lᵖ` product `PiLp p (fun i ↦ ℓ¹(α i, 𝕜))` along
the coordinate inclusions `PiLp.singleCLM` gives coordinate bounded functions
`Λ.piLpCoordBCF i : α i →ᵇ 𝕜` satisfying
`Λ v = ∑ i, lp.bcfPairing 𝕜 (α i) 𝕜 (v i) (Λ.piLpCoordBCF i)`.

## Main definitions

* `BoundedContinuousFunction.toLpInfty`: isometric inclusion `(α →ᵇ E) →ₗᵢ[𝕜] lp (fun _ : α ↦ E) ∞`
  on an arbitrary topological space.
* `lp.bcfPairing`: for a complete normed space `E` over a nontrivially normed field `𝕜`, the
  continuous bilinear pairing `lp (fun _ : α ↦ 𝕜) 1 →L[𝕜] (α →ᵇ E) →L[𝕜] E` given by
  `∑' x, u x • f x`.
* `lp.bcfDualEquiv`: on a discrete space over `RCLike 𝕜`, the linear isometry equivalence
  `(α →ᵇ 𝕜) ≃ₗᵢ[𝕜] StrongDual 𝕜 (lp (fun _ : α ↦ 𝕜) 1)`.
* `StrongDual.piLpCoordBCF`: coordinate bounded functions `y ↦ Λ (PiLp.single p i δ_y)`
  associated to a continuous linear functional `Λ` on `PiLp p (fun i ↦ ℓ¹(α i, 𝕜))`.
-/

public section

noncomputable section

open scoped ENNReal BoundedContinuousFunction

namespace BoundedContinuousFunction

section Module

variable (𝕜 : Type*) {α E : Type*} [TopologicalSpace α] [NormedAddCommGroup E]
  [NormedRing 𝕜] [Module 𝕜 E] [IsBoundedSMul 𝕜 E]

/-- Isometric inclusion of bounded continuous functions `α →ᵇ E` into `lp (fun _ : α ↦ E) ∞`, on
any topological space `α`. -/
def toLpInfty : (α →ᵇ E) →ₗᵢ[𝕜] lp (fun _ : α ↦ E) ∞ where
  toFun f := ⟨⇑f, memℓp_infty f.bddAbove_range_norm_comp⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  norm_map' f := by
    rw [lp.norm_eq_ciSup, norm_eq_iSup_norm]
    rfl

variable {𝕜}

@[simp]
theorem coeFn_toLpInfty (f : α →ᵇ E) : ⇑(toLpInfty 𝕜 f) = ⇑f := by
  rfl

theorem toLpInfty_apply (f : α →ᵇ E) (x : α) : toLpInfty 𝕜 f x = f x := by
  rfl

theorem toLpInfty_injective : Function.Injective (toLpInfty (α := α) (E := E) 𝕜) :=
  (toLpInfty 𝕜).injective

end Module

@[simp]
theorem toLpInfty_one {𝕜 α B : Type*} [TopologicalSpace α] [NormedRing 𝕜] [NormedRing B]
    [NormOneClass B] [Module 𝕜 B] [IsBoundedSMul 𝕜 B] :
    toLpInfty 𝕜 (1 : α →ᵇ B) = 1 := by
  ext x
  simp

/-- On a discrete space, `toLpInfty` agrees with `(lpBCFₗᵢ E 𝕜).symm`. -/
theorem toLpInfty_eq_lpBCFₗᵢ_symm {𝕜 α E : Type*} [TopologicalSpace α] [DiscreteTopology α]
    [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] :
    (toLpInfty 𝕜 : (α →ᵇ E) →ₗᵢ[𝕜] lp (fun _ : α ↦ E) ∞) =
      (lpBCFₗᵢ E 𝕜).symm.toLinearIsometry := by
  ext f x
  simp [coe_lpBCFₗᵢ_symm]

end BoundedContinuousFunction

namespace lp

section Summable

variable {𝕜 α E : Type*} [NormedAddCommGroup 𝕜] [TopologicalSpace α]
  [SeminormedAddCommGroup E] [SMulZeroClass 𝕜 E] [IsBoundedSMul 𝕜 E]

/-- Pointwise scalar multiplication of `f : α →ᵇ E` by `u ∈ ℓ¹(α, 𝕜)` is norm-summable. -/
theorem summable_norm_smul_bcf (u : lp (fun _ : α ↦ 𝕜) 1) (f : α →ᵇ E) :
    Summable fun x ↦ ‖u x • f x‖ :=
  Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun x ↦ f.norm_smul_apply_le (u x) x)
    ((lp.hasSum_norm_one u).summable.mul_right ‖f‖)

/-- When `E` is complete, pointwise scalar multiplication of `f : α →ᵇ E` by `u ∈ ℓ¹(α, 𝕜)` is
summable. -/
theorem summable_smul_bcf [CompleteSpace E] (u : lp (fun _ : α ↦ 𝕜) 1) (f : α →ᵇ E) :
    Summable fun x ↦ u x • f x :=
  (summable_norm_smul_bcf u f).of_norm

end Summable

section Pairing

variable (𝕜 α E : Type*) [NontriviallyNormedField 𝕜] [TopologicalSpace α]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]

/-- The continuous bilinear pairing between `ℓ¹(α, 𝕜)` and bounded continuous functions `α →ᵇ E`,
sending `(u, f)` to `∑' x, u x • f x`. -/
def bcfPairing : lp (fun _ : α ↦ 𝕜) 1 →L[𝕜] (α →ᵇ E) →L[𝕜] E :=
  LinearMap.mkContinuous₂
    (LinearMap.mk₂ 𝕜 (fun u f ↦ ∑' x, u x • f x)
      (fun u₁ u₂ f ↦ by
        simp_rw [lp.coeFn_add, Pi.add_apply, add_smul]
        exact (summable_smul_bcf u₁ f).tsum_add (summable_smul_bcf u₂ f))
      (fun c u f ↦ by
        simp_rw [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, mul_smul]
        exact tsum_const_smul'' c)
      (fun u f₁ f₂ ↦ by
        simp_rw [FunLike.coe_add, Pi.add_apply, smul_add]
        exact (summable_smul_bcf u f₁).tsum_add (summable_smul_bcf u f₂))
      (fun c u f ↦ by
        simp_rw [FunLike.coe_smul, Pi.smul_apply, smul_comm _ c]
        exact tsum_const_smul'' c))
    1 fun u f ↦ by
      simpa using tsum_of_norm_bounded ((lp.hasSum_norm_one u).mul_right ‖f‖)
        fun x ↦ f.norm_smul_apply_le (u x) x

variable {𝕜 α E}

theorem bcfPairing_apply (u : lp (fun _ : α ↦ 𝕜) 1) (f : α →ᵇ E) :
    bcfPairing 𝕜 α E u f = ∑' x, u x • f x := by
  rfl

theorem norm_bcfPairing_le : ‖bcfPairing 𝕜 α E‖ ≤ 1 :=
  LinearMap.mkContinuous₂_norm_le _ zero_le_one _

theorem norm_bcfPairing_apply_le (u : lp (fun _ : α ↦ 𝕜) 1) :
    ‖bcfPairing 𝕜 α E u‖ ≤ ‖u‖ :=
  ((bcfPairing 𝕜 α E).le_opNorm u).trans
    (by simpa using mul_le_mul_of_nonneg_right norm_bcfPairing_le (norm_nonneg u))

theorem norm_bcfPairing_apply_apply_le (u : lp (fun _ : α ↦ 𝕜) 1) (f : α →ᵇ E) :
    ‖bcfPairing 𝕜 α E u f‖ ≤ ‖u‖ * ‖f‖ :=
  ((bcfPairing 𝕜 α E u).le_opNorm f).trans
    (mul_le_mul_of_nonneg_right (norm_bcfPairing_apply_le u) (norm_nonneg f))

@[simp]
theorem bcfPairing_single [DecidableEq α] (x : α) (c : 𝕜) (f : α →ᵇ E) :
    bcfPairing 𝕜 α E (lp.single 1 x c) f = c • f x := by
  simp [bcfPairing_apply, lp.single_apply, Pi.single_apply, ite_smul]

@[simp]
theorem bcfPairing_finsupp_toLp (w : α →₀ 𝕜) (f : α →ᵇ E) :
    bcfPairing 𝕜 α E (w.toLp 1) f = w.sum fun x c ↦ c • f x := by
  rw [bcfPairing_apply, Finsupp.sum]
  simp_rw [Finsupp.coeFn_toLp]
  exact tsum_eq_sum fun x hx ↦ by simp [Finsupp.notMem_support_iff.mp hx]

@[simp]
theorem bcfPairing_const [CompleteSpace 𝕜] (u : lp (fun _ : α ↦ 𝕜) 1) (v : E) :
    bcfPairing 𝕜 α E u (BoundedContinuousFunction.const α v) = (∑' x, u x) • v := by
  rw [bcfPairing_apply]
  simp_rw [BoundedContinuousFunction.const_apply]
  exact (lp.memℓp u).summable_of_one.tsum_smul_const v

end Pairing

@[simp]
theorem bcfPairing_one {𝕜 α : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
    [TopologicalSpace α] (u : lp (fun _ : α ↦ 𝕜) 1) :
    bcfPairing 𝕜 α 𝕜 u 1 = ∑' x, u x := by
  have h1 : (1 : α →ᵇ 𝕜) = BoundedContinuousFunction.const α 1 := by ext; simp
  rw [h1, bcfPairing_const, smul_eq_mul, mul_one]

section StdSimplex

variable {α E : Type*} [TopologicalSpace α] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E]

/-- Pairing a finitely supported probability `s : StdSimplex ℝ α` with `f : α →ᵇ E` yields the
weighted finite sum of `f` against `s.weights`. -/
theorem bcfPairing_stdSimplex_toLp (s : Convexity.StdSimplex ℝ α) (f : α →ᵇ E) :
    bcfPairing ℝ α E (s.toLp 1) f = s.weights.sum fun x r ↦ r • f x := by
  rw [s.toLp_def]
  exact bcfPairing_finsupp_toLp s.weights f

theorem norm_bcfPairing_stdSimplex_toLp_le (s : Convexity.StdSimplex ℝ α) :
    ‖bcfPairing ℝ α E (s.toLp 1)‖ ≤ 1 :=
  (norm_bcfPairing_apply_le (s.toLp 1)).trans_eq s.norm_toLp_one

end StdSimplex

section Real

variable {α : Type*} [TopologicalSpace α]

/-- Pairing a nonnegative sequence in `ℓ¹(α, ℝ)` with a nonnegative bounded continuous function
gives a nonnegative real number. -/
theorem bcfPairing_nonneg {u : lp (fun _ : α ↦ ℝ) 1} (hu : 0 ≤ ⇑u) {f : α →ᵇ ℝ} (hf : 0 ≤ f) :
    0 ≤ bcfPairing ℝ α ℝ u f := by
  rw [bcfPairing_apply]
  exact tsum_nonneg fun x ↦ smul_nonneg (hu x) (hf x)

/-- Pairing with a nonnegative sequence in `ℓ¹(α, ℝ)` is monotone on `α →ᵇ ℝ`. -/
theorem bcfPairing_mono_right {u : lp (fun _ : α ↦ ℝ) 1} (hu : 0 ≤ ⇑u) {f g : α →ᵇ ℝ}
    (hfg : f ≤ g) : bcfPairing ℝ α ℝ u f ≤ bcfPairing ℝ α ℝ u g := by
  rw [← sub_nonneg, ← map_sub]
  exact bcfPairing_nonneg hu (sub_nonneg.2 hfg)

end Real

/-- Under `lp.dualEquiv`, `f.toLpInfty 𝕜` corresponds to the continuous linear functional
`u ↦ bcfPairing 𝕜 α 𝕜 u f`. -/
theorem dualEquiv_toLpInfty {𝕜 α : Type*} [RCLike 𝕜] [TopologicalSpace α] (f : α →ᵇ 𝕜) :
    dualEquiv 𝕜 α ∞ 1 ENNReal.one_ne_top (BoundedContinuousFunction.toLpInfty 𝕜 f) =
      (bcfPairing 𝕜 α 𝕜).flip f := by
  ext u
  simp [dualEquiv_apply, bcfPairing_apply, mul_comm]

section DiscreteDual

variable (𝕜 α : Type*) [RCLike 𝕜] [TopologicalSpace α] [DiscreteTopology α]

/-- On a discrete space over `RCLike 𝕜`, bounded functions `α →ᵇ 𝕜` identify isometrically with
the strong dual of `ℓ¹(α, 𝕜)` via `bcfPairing`. -/
def bcfDualEquiv : (α →ᵇ 𝕜) ≃ₗᵢ[𝕜] StrongDual 𝕜 (lp (fun _ : α ↦ 𝕜) 1) :=
  (lpBCFₗᵢ 𝕜 𝕜).symm.trans (dualEquiv 𝕜 α ∞ 1 ENNReal.one_ne_top)

variable {𝕜 α}

/-- Forward evaluation of `bcfDualEquiv` agrees with `bcfPairing`. -/
@[simp]
theorem bcfDualEquiv_apply (f : α →ᵇ 𝕜) (u : lp (fun _ : α ↦ 𝕜) 1) :
    bcfDualEquiv 𝕜 α f u = bcfPairing 𝕜 α 𝕜 u f := by
  simp only [bcfDualEquiv, LinearIsometryEquiv.trans_apply, dualEquiv_apply, coe_lpBCFₗᵢ_symm,
    bcfPairing_apply, smul_eq_mul, mul_comm]

/-- The inverse of `bcfDualEquiv` evaluates a functional on the unit coordinate vectors
`lp.single 1 x 1`. -/
@[simp]
theorem bcfDualEquiv_symm_apply [DecidableEq α]
    (φ : StrongDual 𝕜 (lp (fun _ : α ↦ 𝕜) 1)) (x : α) :
    (bcfDualEquiv 𝕜 α).symm φ x = φ (lp.single 1 x 1) := by
  simp [bcfDualEquiv, coe_lpBCFₗᵢ]

@[simp]
theorem bcfPairing_bcfDualEquiv_symm (u : lp (fun _ : α ↦ 𝕜) 1)
    (φ : StrongDual 𝕜 (lp (fun _ : α ↦ 𝕜) 1)) :
    bcfPairing 𝕜 α 𝕜 u ((bcfDualEquiv 𝕜 α).symm φ) = φ u := by
  rw [← bcfDualEquiv_apply, LinearIsometryEquiv.apply_symm_apply]

/-- On a discrete space, `lp.dualEquiv` applied to `f.toLpInfty 𝕜` equals `bcfDualEquiv 𝕜 α f`. -/
theorem dualEquiv_toLpInfty_eq_bcfDualEquiv (f : α →ᵇ 𝕜) :
    dualEquiv 𝕜 α ∞ 1 ENNReal.one_ne_top (BoundedContinuousFunction.toLpInfty 𝕜 f) =
      bcfDualEquiv 𝕜 α f := by
  ext u
  simp [dualEquiv_toLpInfty]

end DiscreteDual

end lp

namespace StrongDual

section PiLpCoordBCF

variable {ι : Type*} {α : ι → Type*} {𝕜 : Type*} [DecidableEq ι]
  [∀ i, TopologicalSpace (α i)] [∀ i, DiscreteTopology (α i)] [RCLike 𝕜] {p : ℝ≥0∞}

/-- For a continuous linear functional `Λ` on the `Lᵖ` product of `ℓ¹(α i, 𝕜)` spaces, the
`i`-th coordinate bounded function `y ↦ Λ (PiLp.single p i (lp.single 1 y 1))`. -/
def piLpCoordBCF (Λ : StrongDual 𝕜 (PiLp p (fun i ↦ lp (fun _ : α i ↦ 𝕜) 1))) (i : ι) :
    α i →ᵇ 𝕜 :=
  (lp.bcfDualEquiv 𝕜 (α i)).symm
    (Λ.comp (PiLp.singleCLM p 𝕜 (fun i ↦ lp (fun _ : α i ↦ 𝕜) 1) i))

/-- The `i`-th coordinate bounded function of `Λ` evaluates at `y` to
`Λ (PiLp.single p i (lp.single 1 y 1))`. -/
@[simp]
theorem piLpCoordBCF_apply
    (Λ : StrongDual 𝕜 (PiLp p (fun i ↦ lp (fun _ : α i ↦ 𝕜) 1))) (i : ι)
    [DecidableEq (α i)] (y : α i) :
    Λ.piLpCoordBCF i y = Λ (PiLp.single p i (lp.single 1 y 1)) := by
  simp [piLpCoordBCF]

/-- Evaluating `Λ` on a single coordinate vector `PiLp.single p i u` agrees with the
`ℓ¹`-pairing of `u` against `Λ.piLpCoordBCF i`. -/
theorem apply_piLp_single
    (Λ : StrongDual 𝕜 (PiLp p (fun i ↦ lp (fun _ : α i ↦ 𝕜) 1))) (i : ι)
    (u : lp (fun _ : α i ↦ 𝕜) 1) :
    Λ (PiLp.single p i u) = lp.bcfPairing 𝕜 (α i) 𝕜 u (Λ.piLpCoordBCF i) := by
  simp [piLpCoordBCF]

/-- When the coordinate index type `ι` is finite and `1 ≤ p`, each coordinate bounded function of
`Λ` has supremum norm at most `‖Λ‖`. -/
theorem norm_piLpCoordBCF_le [Fintype ι] [Fact (1 ≤ p)]
    (Λ : StrongDual 𝕜 (PiLp p (fun i ↦ lp (fun _ : α i ↦ 𝕜) 1))) (i : ι) :
    ‖Λ.piLpCoordBCF i‖ ≤ ‖Λ‖ := by
  rw [piLpCoordBCF, LinearIsometryEquiv.norm_map]
  exact (Λ.opNorm_comp_le _).trans
    (mul_le_of_le_one_right (norm_nonneg Λ) (PiLp.norm_singleCLM_le i))

/-- When `ι` is finite, a continuous linear functional on `PiLp p (fun i ↦ ℓ¹(α i, 𝕜))` is the
sum over `i` of the `ℓ¹`-pairings with its coordinate bounded functions `Λ.piLpCoordBCF i`. -/
theorem apply_eq_sum_bcfPairing [Fintype ι]
    (Λ : StrongDual 𝕜 (PiLp p (fun i ↦ lp (fun _ : α i ↦ 𝕜) 1)))
    (v : PiLp p (fun i ↦ lp (fun _ : α i ↦ 𝕜) 1)) :
    Λ v = ∑ i : ι, lp.bcfPairing 𝕜 (α i) 𝕜 (v i) (Λ.piLpCoordBCF i) := by
  rw [← Λ.sum_comp_piLpSingleCLM v]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  simpa only [ContinuousLinearMap.comp_apply, PiLp.singleCLM_apply] using
    Λ.apply_piLp_single i (v i)

end PiLpCoordBCF

end StrongDual
