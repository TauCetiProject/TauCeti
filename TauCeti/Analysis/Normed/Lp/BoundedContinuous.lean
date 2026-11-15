/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Lp.LpEquiv
public import TauCeti.Analysis.Normed.Lp.Dual
public import TauCeti.Analysis.Normed.Lp.LeftTranslation

/-!
# Bounded continuous functions in `ℓ∞` and their pairing with `ℓ¹`

Every bounded continuous function `f : α →ᵇ E` on an arbitrary topological space `α` has bounded
range and supremum norm equal to its `ℓ∞` coordinate norm. Bundling this inclusion gives a linear
isometry `BoundedContinuousFunction.toLpInfty 𝕜 : (α →ᵇ E) →ₗᵢ[𝕜] lp (fun _ : α ↦ E) ∞`, the
bounded-continuous counterpart of `ZeroAtInftyContinuousMap.toLpInfty`. On a discrete space it is
the inverse of Mathlib's `lpBCFₗᵢ`, and under a continuous group action on `α` it intertwines
precomposition by `g⁻¹ • ·` with `lp.leftTranslation`.

Composing `toLpInfty` with `lp.dualEquiv` over `ℝ` or `ℂ` yields the isometric pairing
`BoundedContinuousFunction.toLpOneDual 𝕜 α : (α →ᵇ 𝕜) →ₗᵢ[𝕜] StrongDual 𝕜 (lp (fun _ : α ↦ 𝕜) 1)`,
sending `f` to `p ↦ ∑' x, f x * p x`. Against a finitely supported probability distribution
`w : Convexity.StdSimplex ℝ α`, this pairing computes the finite expectation
`w.weights.sum fun x r ↦ r * f x`, preserves pointwise lower bounds, and satisfies the adjoint
identity

```text
⟨f, L_g p⟩ = ⟨f (g • ·), p⟩.
```

When `α` carries the discrete topology, `BoundedContinuousFunction.lpOneDualEquiv 𝕜 α` upgrades
`toLpOneDual` to a linear isometric equivalence
`(α →ᵇ 𝕜) ≃ₗᵢ[𝕜] StrongDual 𝕜 (lp (fun _ : α ↦ 𝕜) 1)` whose inverse sends `Λ` to the bounded
function `x ↦ Λ (lp.single 1 x 1)`. More generally, for a finite index type `ι`,
`BoundedContinuousFunction.piLpOneDualEquiv 𝕜 ι α` identifies `PiLp ∞ (fun _ : ι ↦ α →ᵇ 𝕜)`
isometrically with the continuous dual of the sum-norm product
`PiLp 1 (fun _ : ι ↦ lp (fun _ : α ↦ 𝕜) 1)`.

## Main definitions

* `BoundedContinuousFunction.toLpInfty 𝕜`: the linear isometry
  `(α →ᵇ E) →ₗᵢ[𝕜] lp (fun _ : α ↦ E) ∞`.
* `BoundedContinuousFunction.toLpOneDual 𝕜 α`: the isometric pairing
  `(α →ᵇ 𝕜) →ₗᵢ[𝕜] StrongDual 𝕜 (lp (fun _ : α ↦ 𝕜) 1)`.
* `BoundedContinuousFunction.toPiLpOneDual 𝕜 ι α`: for finite `ι`, the isometric pairing
  `PiLp ∞ (fun _ : ι ↦ α →ᵇ 𝕜) →ₗᵢ[𝕜] StrongDual 𝕜 (PiLp 1 fun _ : ι ↦ lp (fun _ : α ↦ 𝕜) 1)`.
* `BoundedContinuousFunction.lpOneDualEquiv 𝕜 α`: on a discrete space, the linear isometric
  equivalence `(α →ᵇ 𝕜) ≃ₗᵢ[𝕜] StrongDual 𝕜 (lp (fun _ : α ↦ 𝕜) 1)`.
* `BoundedContinuousFunction.piLpOneDualEquiv 𝕜 ι α`: on a discrete space and finite `ι`, the
  linear isometric equivalence
  `PiLp ∞ (fun _ : ι ↦ α →ᵇ 𝕜) ≃ₗᵢ[𝕜] StrongDual 𝕜 (PiLp 1 fun _ : ι ↦ lp (fun _ : α ↦ 𝕜) 1)`.

## Main results

* `BoundedContinuousFunction.leftTranslation_toLpInfty`: `L_g (toLpInfty 𝕜 f)` is the image of
  `x ↦ f (g⁻¹ • x)`.
* `BoundedContinuousFunction.toLpOneDual_apply_stdSimplex`: pairing `f` with `w.toLp 1` computes
  `w.weights.sum fun x r ↦ r * f x`.
* `BoundedContinuousFunction.toLpOneDual_leftTranslation`: `⟨f, L_g p⟩ = ⟨f (g • ·), p⟩`.
* `BoundedContinuousFunction.lpOneDualEquiv_symm_apply`: on a discrete space, the bounded function
  representing `Λ` evaluates at `x` to `Λ (lp.single 1 x 1)`.
* `BoundedContinuousFunction.piLpOneDualEquiv_symm_apply`: on a discrete space, the `i`-th bounded
  function representing a functional `Λ` on `PiLp 1 (fun _ : ι ↦ lp (fun _ : α ↦ 𝕜) 1)` evaluates
  at `x` to `Λ (PiLp.single 1 i (lp.single 1 x 1))`.

## References

* F. Albiac and N. J. Kalton, *Topics in Banach Space Theory*, Chapter 1.
* B. Bekka, P. de la Harpe, A. Valette, *Kazhdan's Property (T)*, Appendix G.1 and G.3.
-/

public section

noncomputable section

open Convexity
open scoped ENNReal BoundedContinuousFunction

namespace BoundedContinuousFunction

section LpInfty

variable (𝕜 : Type*) {α E : Type*} [TopologicalSpace α] [NormedAddCommGroup E] [NormedRing 𝕜]
  [Module 𝕜 E] [IsBoundedSMul 𝕜 E]

/-- The inclusion of bounded continuous functions `α →ᵇ E` into `lp (fun _ : α ↦ E) ∞`, as a
linear isometry. -/
def toLpInfty : (α →ᵇ E) →ₗᵢ[𝕜] lp (fun _ : α ↦ E) ∞ where
  toFun f := ⟨⇑f, f.bddAbove_range_norm_comp⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  norm_map' f := by
    rw [lp.norm_eq_ciSup, norm_eq_iSup_norm]
    rfl

variable {𝕜}

/-- `BoundedContinuousFunction.toLpInfty` preserves pointwise values. -/
@[simp]
theorem toLpInfty_apply (f : α →ᵇ E) (x : α) : toLpInfty 𝕜 f x = f x :=
  (rfl)

/-- `toLpInfty` sends the constant function `1` to `1` in `ℓ∞`. -/
@[simp]
theorem toLpInfty_one : toLpInfty ℝ (1 : α →ᵇ ℝ) = 1 :=
  lp.ext rfl

/-- Under a continuous group action on `α`, `toLpInfty` intertwines precomposition by `g⁻¹ • ·`
with `lp.leftTranslation`. -/
theorem leftTranslation_toLpInfty {G : Type*} [Group G] [MulAction G α] [ContinuousConstSMul G α]
    (g : G) (f : α →ᵇ E) :
    lp.leftTranslation α ∞ 𝕜 E g (toLpInfty 𝕜 f) =
      toLpInfty 𝕜 (f.compContinuous ⟨(g⁻¹ • ·), continuous_const_smul g⁻¹⟩) := by
  ext x
  simp

section Discrete

variable {𝔽 : Type*} [NontriviallyNormedField 𝔽] [NormedSpace 𝔽 E] [DiscreteTopology α]

@[simp]
theorem lpBCFₗᵢ_toLpInfty (f : α →ᵇ E) : lpBCFₗᵢ E 𝔽 (toLpInfty 𝔽 f) = f := by
  ext x
  rfl

@[simp]
theorem toLpInfty_lpBCFₗᵢ (a : lp (fun _ : α ↦ E) ∞) : toLpInfty 𝔽 (lpBCFₗᵢ E 𝔽 a) = a := by
  ext x
  rfl

theorem toLpInfty_eq_lpBCFₗᵢ_symm :
    (toLpInfty 𝔽 : (α →ᵇ E) →ₗᵢ[𝔽] lp (fun _ : α ↦ E) ∞) = (lpBCFₗᵢ E 𝔽).symm.toLinearIsometry :=
  LinearIsometry.ext fun _ ↦ lp.ext rfl

end Discrete

end LpInfty

section LpOneDual

variable (𝕜 : Type*) {ι : Type*} [Fintype ι] (α : Type*) [RCLike 𝕜] [TopologicalSpace α]

/-- The isometric pairing of bounded continuous functions `α →ᵇ 𝕜` with `ℓ¹(α, 𝕜)`, sending `f`
to `p ↦ ∑' x, f x * p x`. -/
def toLpOneDual : (α →ᵇ 𝕜) →ₗᵢ[𝕜] StrongDual 𝕜 (lp (fun _ : α ↦ 𝕜) 1) :=
  (lp.dualEquiv 𝕜 α ∞ 1 ENNReal.one_ne_top).toLinearIsometry.comp (toLpInfty 𝕜)

variable {𝕜 α}

/-- `toLpOneDual` acts on `p ∈ ℓ¹(α, 𝕜)` by the series `∑' x, f x * p x`. -/
theorem toLpOneDual_apply (f : α →ᵇ 𝕜) (p : lp (fun _ : α ↦ 𝕜) 1) :
    toLpOneDual 𝕜 α f p = ∑' x, f x * p x :=
  lp.dualEquiv_apply ENNReal.one_ne_top (toLpInfty 𝕜 f) p

/-- Against a coordinate vector `lp.single 1 x z`, `toLpOneDual` evaluates to `f x * z`. -/
@[simp]
theorem toLpOneDual_apply_single [DecidableEq α] (f : α →ᵇ 𝕜) (x : α) (z : 𝕜) :
    toLpOneDual 𝕜 α f (lp.single 1 x z) = f x * z := by
  simp [toLpOneDual]

/-- Against `p.toLp 1` for a finitely supported function `p : α →₀ 𝕜`, `toLpOneDual` computes the
finite sum `p.sum fun x z ↦ f x * z`. -/
theorem toLpOneDual_apply_finsupp (f : α →ᵇ 𝕜) (p : α →₀ 𝕜) :
    toLpOneDual 𝕜 α f (p.toLp 1) = p.sum fun x z ↦ f x * z := by
  rw [toLpOneDual_apply, Finsupp.sum]
  simp only [Finsupp.coeFn_toLp]
  exact tsum_eq_sum fun x hx ↦ by simp [Finsupp.notMem_support_iff.mp hx]

/-- Against `w.toLp 1` for `w : StdSimplex ℝ α`, `toLpOneDual` computes the finite expectation
`w.weights.sum fun x r ↦ r * f x`. -/
theorem toLpOneDual_apply_stdSimplex (f : α →ᵇ ℝ) (w : StdSimplex ℝ α) :
    toLpOneDual ℝ α f (w.toLp 1) = w.weights.sum fun x r ↦ r * f x := by
  rw [StdSimplex.toLp_def, toLpOneDual_apply_finsupp]
  exact Finsupp.sum_congr fun x _ ↦ mul_comm _ _

/-- Pairing the constant function `1` with any finitely supported probability distribution gives
`1`. -/
@[simp]
theorem toLpOneDual_one_stdSimplex (w : StdSimplex ℝ α) :
    toLpOneDual ℝ α 1 (w.toLp 1) = 1 := by
  simp [toLpOneDual_apply_stdSimplex]

/-- Pairing against a finitely supported probability distribution is monotone in `f`. -/
theorem toLpOneDual_mono_stdSimplex {f g : α →ᵇ ℝ} (h : f ≤ g) (w : StdSimplex ℝ α) :
    toLpOneDual ℝ α f (w.toLp 1) ≤ toLpOneDual ℝ α g (w.toLp 1) := by
  rw [toLpOneDual_apply_stdSimplex, toLpOneDual_apply_stdSimplex]
  exact Finset.sum_le_sum fun x _ ↦ mul_le_mul_of_nonneg_left (h x) (w.weights_nonneg x)

/-- If `c ≤ f x` for all `x`, then `c ≤ ⟨f, w.toLp 1⟩` for every finitely supported probability
distribution `w`. -/
theorem le_toLpOneDual_stdSimplex {f : α →ᵇ ℝ} {c : ℝ} (hc : ∀ x, c ≤ f x) (w : StdSimplex ℝ α) :
    c ≤ toLpOneDual ℝ α f (w.toLp 1) := by
  calc c = c * 1 := (mul_one c).symm
    _ = toLpOneDual ℝ α (const α c) (w.toLp 1) := by
      rw [toLpOneDual_apply_stdSimplex, ← w.total, Finsupp.sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ ↦ mul_comm _ _
    _ ≤ toLpOneDual ℝ α f (w.toLp 1) := toLpOneDual_mono_stdSimplex hc w

/-- **Adjointness of left translation.** Pairing `f` against `L_g p` equals pairing `x ↦ f (g • x)`
against `p`. -/
theorem toLpOneDual_leftTranslation {G : Type*} [Group G] [MulAction G α]
    [ContinuousConstSMul G α] (g : G) (f : α →ᵇ 𝕜) (p : lp (fun _ : α ↦ 𝕜) 1) :
    toLpOneDual 𝕜 α f (lp.leftTranslation α 1 𝕜 𝕜 g p) =
      toLpOneDual 𝕜 α (f.compContinuous ⟨(g • ·), continuous_const_smul g⟩) p := by
  simp only [toLpOneDual_apply, lp.leftTranslation_apply]
  rw [← (MulAction.toPerm g).tsum_eq]
  refine tsum_congr fun x ↦ ?_
  simp

/-- Pairing `f` against a translation difference `L_g p - p` equals pairing `f (g • ·) - f` against
`p`. -/
theorem toLpOneDual_leftTranslation_sub {G : Type*} [Group G] [MulAction G α]
    [ContinuousConstSMul G α] (g : G) (f : α →ᵇ 𝕜) (p : lp (fun _ : α ↦ 𝕜) 1) :
    toLpOneDual 𝕜 α f (lp.leftTranslation α 1 𝕜 𝕜 g p - p) =
      toLpOneDual 𝕜 α (f.compContinuous ⟨(g • ·), continuous_const_smul g⟩ - f) p := by
  rw [map_sub, toLpOneDual_leftTranslation, map_sub, sub_apply]

variable (𝕜 ι α)

/-- Underlying linear map of `BoundedContinuousFunction.toPiLpOneDual`. -/
private def toPiLpOneDualLinearMap :
    PiLp ∞ (fun _ : ι ↦ α →ᵇ 𝕜) →ₗ[𝕜]
      StrongDual 𝕜 (PiLp 1 fun _ : ι ↦ lp (fun _ : α ↦ 𝕜) 1) where
  toFun f := ∑ i, (toLpOneDual 𝕜 α (f i)).comp (PiLp.proj 1 (fun _ : ι ↦ lp (fun _ : α ↦ 𝕜) 1) i)
  map_add' _ _ := by
    ext v
    simp [Finset.sum_add_distrib]
  map_smul' _ _ := by
    ext v
    simp [Finset.mul_sum]

variable {𝕜 ι α}

private theorem toPiLpOneDualLinearMap_apply_single [DecidableEq ι]
    (f : PiLp ∞ (fun _ : ι ↦ α →ᵇ 𝕜)) (i : ι) (u : lp (fun _ : α ↦ 𝕜) 1) :
    toPiLpOneDualLinearMap 𝕜 ι α f (PiLp.single 1 i u) = toLpOneDual 𝕜 α (f i) u := by
  simp only [toPiLpOneDualLinearMap, LinearMap.coe_mk, AddHom.coe_mk, sum_apply,
    ContinuousLinearMap.comp_apply, PiLp.proj_apply]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    simp [hji]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

variable (𝕜 ι α)

/-- For a finite index type `ι`, the isometric pairing of supremum-normed families
`PiLp ∞ (fun _ : ι ↦ α →ᵇ 𝕜)` with the sum-normed product
`PiLp 1 (fun _ : ι ↦ lp (fun _ : α ↦ 𝕜) 1)`, sending `f` to `v ↦ ∑ i, ⟨f i, v i⟩`. -/
def toPiLpOneDual :
    PiLp ∞ (fun _ : ι ↦ α →ᵇ 𝕜) →ₗᵢ[𝕜]
      StrongDual 𝕜 (PiLp 1 fun _ : ι ↦ lp (fun _ : α ↦ 𝕜) 1) where
  __ := toPiLpOneDualLinearMap 𝕜 ι α
  norm_map' f := by
    classical
    refine le_antisymm ?_ ?_
    · refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg f) fun v ↦ ?_
      simp only [toPiLpOneDualLinearMap, LinearMap.coe_mk, AddHom.coe_mk, sum_apply,
        ContinuousLinearMap.comp_apply, PiLp.proj_apply]
      calc ‖∑ i, toLpOneDual 𝕜 α (f i) (v i)‖
          ≤ ∑ i, ‖toLpOneDual 𝕜 α (f i) (v i)‖ := norm_sum_le _ _
        _ ≤ ∑ i, ‖toLpOneDual 𝕜 α (f i)‖ * ‖v i‖ :=
          Finset.sum_le_sum fun i _ ↦ (toLpOneDual 𝕜 α (f i)).le_opNorm (v i)
        _ = ∑ i, ‖f i‖ * ‖v i‖ := by simp only [LinearIsometry.norm_map]
        _ ≤ ∑ i, ‖f‖ * ‖v i‖ :=
          Finset.sum_le_sum fun i _ ↦
            mul_le_mul_of_nonneg_right (PiLp.norm_apply_le f i) (norm_nonneg _)
        _ = ‖f‖ * ‖v‖ := by rw [← Finset.mul_sum, PiLp.norm_eq_of_L1]
    · rw [PiLp.norm_eq_ciSup]
      refine Real.iSup_le (fun i ↦ ?_) (norm_nonneg (toPiLpOneDualLinearMap 𝕜 ι α f))
      rw [← (toLpOneDual 𝕜 α).norm_map (f i)]
      refine ContinuousLinearMap.opNorm_le_bound _
        (norm_nonneg (toPiLpOneDualLinearMap 𝕜 ι α f)) fun u ↦ ?_
      rw [← toPiLpOneDualLinearMap_apply_single f i u]
      simpa using (toPiLpOneDualLinearMap 𝕜 ι α f).le_opNorm (PiLp.single 1 i u)

variable {𝕜 ι α}

/-- `toPiLpOneDual` acts by summing the coordinate pairings `⟨f i, v i⟩`. -/
theorem toPiLpOneDual_apply (f : PiLp ∞ (fun _ : ι ↦ α →ᵇ 𝕜))
    (v : PiLp 1 fun _ : ι ↦ lp (fun _ : α ↦ 𝕜) 1) :
    toPiLpOneDual 𝕜 ι α f v = ∑ i, toLpOneDual 𝕜 α (f i) (v i) := by
  simp [toPiLpOneDual, toPiLpOneDualLinearMap]

/-- On a single-factor vector `PiLp.single 1 i u`, `toPiLpOneDual` evaluates `f i` against `u`. -/
@[simp]
theorem toPiLpOneDual_apply_single [DecidableEq ι] (f : PiLp ∞ (fun _ : ι ↦ α →ᵇ 𝕜))
    (i : ι) (u : lp (fun _ : α ↦ 𝕜) 1) :
    toPiLpOneDual 𝕜 ι α f (PiLp.single 1 i u) = toLpOneDual 𝕜 α (f i) u :=
  toPiLpOneDualLinearMap_apply_single f i u

end LpOneDual

section DiscreteDual

variable (𝕜 : Type*) {ι : Type*} [Fintype ι] (α : Type*) [RCLike 𝕜] [TopologicalSpace α]
  [DiscreteTopology α]

/-- On a discrete space `α`, bounded functions `α →ᵇ 𝕜` are isometrically isomorphic to the
continuous dual of `ℓ¹(α, 𝕜)` via `f ↦ (p ↦ ∑' x, f x * p x)`. -/
def lpOneDualEquiv : (α →ᵇ 𝕜) ≃ₗᵢ[𝕜] StrongDual 𝕜 (lp (fun _ : α ↦ 𝕜) 1) :=
  (lpBCFₗᵢ 𝕜 𝕜).symm.trans (lp.dualEquiv 𝕜 α ∞ 1 ENNReal.one_ne_top)

variable {𝕜 α}

@[simp]
theorem lpOneDualEquiv_toLinearIsometry :
    (lpOneDualEquiv 𝕜 α).toLinearIsometry = toLpOneDual 𝕜 α :=
  LinearIsometry.ext fun _ ↦ ContinuousLinearMap.ext fun _ ↦ rfl

@[simp]
theorem coe_lpOneDualEquiv :
    ⇑(lpOneDualEquiv 𝕜 α) = toLpOneDual 𝕜 α :=
  (rfl)

theorem lpOneDualEquiv_apply (f : α →ᵇ 𝕜) (p : lp (fun _ : α ↦ 𝕜) 1) :
    lpOneDualEquiv 𝕜 α f p = ∑' x, f x * p x :=
  toLpOneDual_apply f p

/-- On a discrete space, the bounded function corresponding to a continuous linear functional `Λ` on
`ℓ¹(α, 𝕜)` takes `x` to `Λ (lp.single 1 x 1)`. -/
@[simp]
theorem lpOneDualEquiv_symm_apply [DecidableEq α] (Λ : StrongDual 𝕜 (lp (fun _ : α ↦ 𝕜) 1))
    (x : α) : (lpOneDualEquiv 𝕜 α).symm Λ x = Λ (lp.single 1 x 1) := by
  simp [lpOneDualEquiv, coe_lpBCFₗᵢ]

/-- Every value of `(lpOneDualEquiv 𝕜 α).symm Λ` has norm at most `‖Λ‖`. -/
theorem norm_lpOneDualEquiv_symm_apply_le (Λ : StrongDual 𝕜 (lp (fun _ : α ↦ 𝕜) 1)) (x : α) :
    ‖(lpOneDualEquiv 𝕜 α).symm Λ x‖ ≤ ‖Λ‖ :=
  ((lpOneDualEquiv 𝕜 α).symm Λ).norm_coe_le_norm x |>.trans_eq
    ((lpOneDualEquiv 𝕜 α).symm.norm_map Λ)

variable (𝕜 ι α)

/-- On a discrete space `α` and finite index type `ι`, the supremum-normed family
`PiLp ∞ (fun _ : ι ↦ α →ᵇ 𝕜)` is isometrically isomorphic to the continuous dual of the sum-normed
product `PiLp 1 (fun _ : ι ↦ lp (fun _ : α ↦ 𝕜) 1)` via `f ↦ (v ↦ ∑ i, ⟨f i, v i⟩)`. -/
def piLpOneDualEquiv :
    PiLp ∞ (fun _ : ι ↦ α →ᵇ 𝕜) ≃ₗᵢ[𝕜]
      StrongDual 𝕜 (PiLp 1 fun _ : ι ↦ lp (fun _ : α ↦ 𝕜) 1) :=
  LinearIsometryEquiv.ofSurjective (toPiLpOneDual 𝕜 ι α) fun Λ ↦ by
    classical
    let ιMap (i : ι) : lp (fun _ : α ↦ 𝕜) 1 →L[𝕜] PiLp 1 (fun _ : ι ↦ lp (fun _ : α ↦ 𝕜) 1) :=
      (PiLp.continuousLinearEquiv 1 𝕜
        (fun _ : ι ↦ lp (fun _ : α ↦ 𝕜) 1)).symm.toContinuousLinearMap.comp
        (ContinuousLinearMap.single 𝕜 (fun _ : ι ↦ lp (fun _ : α ↦ 𝕜) 1) i)
    refine ⟨WithLp.toLp ∞ fun i ↦ (lpOneDualEquiv 𝕜 α).symm (Λ.comp (ιMap i)),
      ContinuousLinearMap.ext fun v ↦ ?_⟩
    have hv : ∑ i, PiLp.single 1 i (v i) = v := by
      ext j
      simp [Finset.sum_apply, Pi.single_apply]
    conv_rhs => rw [← hv, map_sum]
    rw [toPiLpOneDual_apply]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    simp [ιMap, ← coe_lpOneDualEquiv]

variable {𝕜 ι α}

@[simp]
theorem coe_piLpOneDualEquiv :
    ⇑(piLpOneDualEquiv 𝕜 ι α) = toPiLpOneDual 𝕜 ι α :=
  LinearIsometryEquiv.coe_ofSurjective _ _

@[simp]
theorem piLpOneDualEquiv_toLinearIsometry :
    (piLpOneDualEquiv 𝕜 ι α).toLinearIsometry = toPiLpOneDual 𝕜 ι α :=
  LinearIsometry.ext fun f ↦ congrFun coe_piLpOneDualEquiv f

/-- `piLpOneDualEquiv` acts by summing the coordinate pairings `⟨f i, v i⟩`. -/
theorem piLpOneDualEquiv_apply (f : PiLp ∞ (fun _ : ι ↦ α →ᵇ 𝕜))
    (v : PiLp 1 fun _ : ι ↦ lp (fun _ : α ↦ 𝕜) 1) :
    piLpOneDualEquiv 𝕜 ι α f v = ∑ i, toLpOneDual 𝕜 α (f i) (v i) := by
  rw [coe_piLpOneDualEquiv, toPiLpOneDual_apply]

/-- The `i`-th coordinate bounded function of `(piLpOneDualEquiv 𝕜 ι α).symm Λ` evaluates at `x`
to `Λ (PiLp.single 1 i (lp.single 1 x 1))`. -/
@[simp]
theorem piLpOneDualEquiv_symm_apply [DecidableEq ι] [DecidableEq α]
    (Λ : StrongDual 𝕜 (PiLp 1 fun _ : ι ↦ lp (fun _ : α ↦ 𝕜) 1)) (i : ι) (x : α) :
    (piLpOneDualEquiv 𝕜 ι α).symm Λ i x = Λ (PiLp.single 1 i (lp.single 1 x 1)) := by
  have h := congrArg (fun φ : StrongDual 𝕜 (PiLp 1 fun _ : ι ↦ lp (fun _ : α ↦ 𝕜) 1) ↦
      φ (PiLp.single 1 i (lp.single 1 x 1)))
    ((piLpOneDualEquiv 𝕜 ι α).apply_symm_apply Λ)
  simpa only [coe_piLpOneDualEquiv, toPiLpOneDual_apply_single, toLpOneDual_apply_single,
    mul_one] using h

/-- Each coordinate bounded function of `(piLpOneDualEquiv 𝕜 ι α).symm Λ` has norm at most `‖Λ‖`. -/
theorem norm_piLpOneDualEquiv_symm_apply_le
    (Λ : StrongDual 𝕜 (PiLp 1 fun _ : ι ↦ lp (fun _ : α ↦ 𝕜) 1)) (i : ι) :
    ‖(piLpOneDualEquiv 𝕜 ι α).symm Λ i‖ ≤ ‖Λ‖ :=
  (PiLp.norm_apply_le ((piLpOneDualEquiv 𝕜 ι α).symm Λ) i).trans_eq
    ((piLpOneDualEquiv 𝕜 ι α).symm.norm_map Λ)

/-- Every value of `(piLpOneDualEquiv 𝕜 ι α).symm Λ i` has norm at most `‖Λ‖`. -/
theorem norm_piLpOneDualEquiv_symm_apply_apply_le
    (Λ : StrongDual 𝕜 (PiLp 1 fun _ : ι ↦ lp (fun _ : α ↦ 𝕜) 1)) (i : ι) (x : α) :
    ‖(piLpOneDualEquiv 𝕜 ι α).symm Λ i x‖ ≤ ‖Λ‖ :=
  (((piLpOneDualEquiv 𝕜 ι α).symm Λ i).norm_coe_le_norm x).trans
    (norm_piLpOneDualEquiv_symm_apply_le Λ i)

end DiscreteDual

end BoundedContinuousFunction
