/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import TauCeti.Analysis.InnerProductSpace.ExternalProductBlock
public import TauCeti.Analysis.Pseudodifferential.HomogeneousSymbol

/-!
# The external product of two homogeneous symbols

Let `σ_P(x, ξ) : V₀ → V₁` and `σ_Q(y, η) : W₀ → W₁` be principal symbols of two elliptic
operators of order `1` on two bases, normalized so that `σ_P* σ_P = σ_P σ_P* = ‖ξ‖²` and
`σ_Q* σ_Q = σ_Q σ_Q* = ‖η‖²`. Their external product is the symbol on the product base

`A = [[σ_P ⊗ 1, -(1 ⊗ σ_Q*)], [1 ⊗ σ_Q, σ_P* ⊗ 1]] : (V₀ ⊗ W₀) ⊕ (V₁ ⊗ W₁) → (V₁ ⊗ W₀) ⊕ (V₀ ⊗ W₁)`

(`ContinuousLinearMap.externalProductBlock`), which satisfies `A* A = A A* = ‖ξ‖² + ‖η‖²`. It is
positively homogeneous of degree `1` in `(ξ, η)`, but it is not smooth away from `(ξ, η) = 0`:
its entries are only continuous along the axes `ξ = 0` and `η = 0`, where `σ_P` and `σ_Q` have
their singularities.

The remedy is a *conic cutoff* `χ : ℝ → ℝ` (`TauCeti.ConicCutoff`), smooth with values in
`[0, 1]`, vanishing on `t ≤ 1/4` and equal to `1` on `t ≥ 1/2`. Writing `ρ² = ‖ξ‖² + ‖η‖²`, replace
`σ_P` by `χ(‖ξ‖² / ρ²) σ_P` and `σ_Q` by `χ(‖η‖² / ρ²) σ_Q`
(`HomogeneousSymbol.conicCutoffFst` and `HomogeneousSymbol.conicCutoffSnd`). Each factor now
vanishes near the axis on which it is singular, so it is smooth on all of `(ξ, η) ≠ 0`, and the
cut-off external product `A_χ` (`HomogeneousSymbol.externalProduct`) is a homogeneous symbol on
the product base. The cutoffs keep it elliptic: since `‖ξ‖² / ρ² + ‖η‖² / ρ² = 1`, at least one of
the two cutoffs equals `1`, and

`A_χ* A_χ = A_χ A_χ* = χ(‖ξ‖² / ρ²)² ‖ξ‖² + χ(‖η‖² / ρ²)² ‖η‖²`,

a scalar between `ρ² / 2` and `ρ²`. So `A_χ` is an elliptic homogeneous symbol of degree `1` on
the product. The first cut-off factor agrees with `σ_P` on the cone `‖ξ‖ ≥ ‖η‖`, and the second
with `σ_Q` on the cone `‖η‖ ≥ ‖ξ‖`.

## Main declarations

* `TauCeti.ConicCutoff`: smooth cutoffs `ℝ → [0, 1]` vanishing on `t ≤ 1/4` and equal to `1` on
  `t ≥ 1/2`; `TauCeti.ConicCutoff.ofSmoothTransition` shows they exist.
* `TauCeti.ConicCutoff.add_le_two_mul` and `TauCeti.ConicCutoff.sq_mul_add_sq_mul_le`: the
  scalar `χ(a / (a + b))² a + χ(b / (a + b))² b` lies between `(a + b) / 2` and `a + b`.
* `TauCeti.HomogeneousSymbol.conicCutoffFst`, `TauCeti.HomogeneousSymbol.conicCutoffSnd`: a
  homogeneous symbol on one factor, cut off near the axis where it is singular, as a homogeneous
  symbol on the product.
* `TauCeti.HomogeneousSymbol.externalProduct`: the cut-off external product `A_χ`.
* `TauCeti.HomogeneousSymbol.adjoint_comp_coefficient_externalProduct`,
  `TauCeti.HomogeneousSymbol.coefficient_externalProduct_comp_adjoint`: `A_χ* A_χ` and `A_χ A_χ*`
  are the scalar above, for normalized factors.
* `TauCeti.HomogeneousSymbol.le_two_mul_norm_coefficient_externalProduct_apply_sq`,
  `TauCeti.HomogeneousSymbol.le_two_mul_norm_adjoint_coefficient_externalProduct_apply_sq`: the
  ellipticity bounds `ρ² ‖w‖² ≤ 2 ‖A_χ w‖²` and `ρ² ‖w‖² ≤ 2 ‖A_χ* w‖²`.

## References

* M. F. Atiyah and I. M. Singer, *The index of elliptic operators: I*, Ann. of Math. 87 (1968),
  §2, p. 490 (the external product of symbol complexes) and §9 (the product of two elliptic
  operators).
-/

public section

noncomputable section

open Set Filter
open scoped ContDiff Topology TensorProduct

namespace TauCeti

/-! ### Conic cutoffs -/

/-- A conic cutoff: a smooth function `ℝ → ℝ` with values in `[0, 1]` that vanishes on
`t ≤ 1/4` and equals `1` on `t ≥ 1/2`. Evaluated at `‖ξ‖² / (‖ξ‖² + ‖η‖²)`, it cuts a function of
`(ξ, η)` off near the axis `ξ = 0` while keeping it unchanged on the cone `‖ξ‖ ≥ ‖η‖`. -/
structure ConicCutoff where
  /-- The underlying function. Use the coercion to a function instead. -/
  toFun : ℝ → ℝ
  contDiff' : ContDiff ℝ ∞ toFun
  eq_zero_of_le_one_div_four' : ∀ t, t ≤ 1 / 4 → toFun t = 0
  eq_one_of_one_div_two_le' : ∀ t, 1 / 2 ≤ t → toFun t = 1
  nonneg' : ∀ t, 0 ≤ toFun t
  le_one' : ∀ t, toFun t ≤ 1

namespace ConicCutoff

instance : FunLike ConicCutoff ℝ ℝ where
  coe := toFun
  coe_injective χ₁ χ₂ h := by cases χ₁; cases χ₂; congr

@[simp]
theorem toFun_eq_coe (χ : ConicCutoff) : χ.toFun = χ :=
  rfl

@[ext]
theorem ext {χ₁ χ₂ : ConicCutoff} (h : ∀ t, χ₁ t = χ₂ t) : χ₁ = χ₂ :=
  DFunLike.ext _ _ h

variable (χ : ConicCutoff)

theorem contDiff {n : ℕ∞} : ContDiff ℝ n χ :=
  χ.contDiff'.of_le (mod_cast le_top)

theorem continuous : Continuous χ :=
  (χ.contDiff (n := 0)).continuous

theorem apply_eq_zero_of_le_one_div_four {t : ℝ} (ht : t ≤ 1 / 4) : χ t = 0 :=
  χ.eq_zero_of_le_one_div_four' t ht

theorem apply_eq_one_of_one_div_two_le {t : ℝ} (ht : 1 / 2 ≤ t) : χ t = 1 :=
  χ.eq_one_of_one_div_two_le' t ht

@[simp]
theorem apply_zero : χ 0 = 0 :=
  χ.apply_eq_zero_of_le_one_div_four (by norm_num)

theorem nonneg (t : ℝ) : 0 ≤ χ t :=
  χ.nonneg' t

theorem le_one (t : ℝ) : χ t ≤ 1 :=
  χ.le_one' t

/-- `t ↦ smoothTransition (4 t - 1)` is a conic cutoff. -/
def ofSmoothTransition : ConicCutoff where
  toFun t := Real.smoothTransition (4 * t - 1)
  contDiff' :=
    Real.smoothTransition.contDiff.comp ((contDiff_const.mul contDiff_id).sub contDiff_const)
  eq_zero_of_le_one_div_four' t ht := Real.smoothTransition.zero_of_nonpos (by linarith)
  eq_one_of_one_div_two_le' t ht := Real.smoothTransition.one_of_one_le (by linarith)
  nonneg' _ := Real.smoothTransition.nonneg _
  le_one' _ := Real.smoothTransition.le_one _

@[simp]
theorem ofSmoothTransition_apply (t : ℝ) :
    ofSmoothTransition t = Real.smoothTransition (4 * t - 1) :=
  (rfl)

instance : Inhabited ConicCutoff :=
  ⟨ofSmoothTransition⟩

/-- Since `a / (a + b) + b / (a + b) = 1`, one of the two cutoffs is `1`, so the weighted sum
`χ(a / (a + b))² a + χ(b / (a + b))² b` is at least `(a + b) / 2`. -/
theorem add_le_two_mul {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    a + b ≤ 2 * (χ (a / (a + b)) ^ 2 * a + χ (b / (a + b)) ^ 2 * b) := by
  have h₁ := χ.nonneg (a / (a + b))
  have h₂ := χ.nonneg (b / (a + b))
  rcases (add_nonneg ha hb).eq_or_lt with hab | hab
  · rw [← hab]
    positivity
  rcases le_total b a with hle | hle
  · rw [χ.apply_eq_one_of_one_div_two_le (by rw [le_div_iff₀ hab]; linarith)]
    nlinarith
  · rw [χ.apply_eq_one_of_one_div_two_le (t := b / (a + b)) (by rw [le_div_iff₀ hab]; linarith)]
    nlinarith

/-- Since the cutoff takes values in `[0, 1]`, the weighted sum
`χ(a / (a + b))² a + χ(b / (a + b))² b` is at most `a + b`. -/
theorem sq_mul_add_sq_mul_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    χ (a / (a + b)) ^ 2 * a + χ (b / (a + b)) ^ 2 * b ≤ a + b := by
  have h₁ : χ (a / (a + b)) ^ 2 ≤ 1 := pow_le_one₀ (χ.nonneg _) (χ.le_one _)
  have h₂ : χ (b / (a + b)) ^ 2 ≤ 1 := pow_le_one₀ (χ.nonneg _) (χ.le_one _)
  nlinarith

end ConicCutoff

/-! ### Cutting off a homogeneous symbol near an axis -/

namespace HomogeneousSymbol

variable {X Y E F : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y]
  [NormedSpace ℝ Y] [NormedAddCommGroup E] [InnerProductSpace ℝ E] [NormedAddCommGroup F]
  [InnerProductSpace ℝ F] {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [NormedAddCommGroup W] [NormedSpace ℂ W] {m : ℝ}

/-- The conic ratio `‖u‖² / (‖u‖² + ‖v‖²)` is invariant under positive dilations. -/
private theorem conicRatio_smul {G G' : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedAddCommGroup G'] [NormedSpace ℝ G'] (u : G) (v : G') {t : ℝ} (ht : 0 < t) :
    ‖t • u‖ ^ 2 / (‖t • u‖ ^ 2 + ‖t • v‖ ^ 2) = ‖u‖ ^ 2 / (‖u‖ ^ 2 + ‖v‖ ^ 2) := by
  simp only [norm_smul, Real.norm_of_nonneg ht.le, mul_pow, ← mul_add]
  exact mul_div_mul_left _ _ (pow_ne_zero 2 ht.ne')

/-- For smooth maps `σ`, `π` and `π'` out of `Q`, and `g` smooth away from the zero frequency,
the function `q ↦ χ(‖π q‖² / (‖π q‖² + ‖π' q‖²)) • g (σ q, π q)` is smooth wherever
`(π q, π' q) ≠ 0`: where `π q ≠ 0` all its factors are smooth, and near a point with `π q = 0`
the cutoff vanishes. -/
private theorem contDiffOn_conicCutoff_smul {Q P G G' : Type*} [NormedAddCommGroup Q]
    [NormedSpace ℝ Q] [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedAddCommGroup G]
    [InnerProductSpace ℝ G] [NormedAddCommGroup G'] [InnerProductSpace ℝ G'] (χ : ConicCutoff)
    {σ : Q → P} {π : Q → G} {π' : Q → G'} (hσ : ContDiff ℝ ∞ σ) (hπ : ContDiff ℝ ∞ π)
    (hπ' : ContDiff ℝ ∞ π') {g : P × G → V →L[ℂ] W} (hg : ContDiffOn ℝ ∞ g {p | p.2 ≠ 0}) :
    ContDiffOn ℝ ∞ (fun q ↦ χ (‖π q‖ ^ 2 / (‖π q‖ ^ 2 + ‖π' q‖ ^ 2)) • g (σ q, π q))
      {q | π q ≠ 0 ∨ π' q ≠ 0} := by
  intro q hq
  refine ContDiffAt.contDiffWithinAt ?_
  have hnum : ContDiff ℝ ∞ fun q ↦ ‖π q‖ ^ 2 := (contDiff_norm_sq ℝ).comp hπ
  have hden : ContDiff ℝ ∞ fun q ↦ ‖π q‖ ^ 2 + ‖π' q‖ ^ 2 :=
    hnum.add ((contDiff_norm_sq ℝ).comp hπ')
  by_cases hq0 : π q = 0
  · -- Near `q` the ratio is below `1 / 4`, so the cutoff and the whole function vanish.
    have hq' : π' q ≠ 0 := hq.resolve_left (not_not.2 hq0)
    have hpos : ‖π q‖ ^ 2 + ‖π' q‖ ^ 2 ≠ 0 := by positivity
    have hratio : ContinuousAt (fun q ↦ ‖π q‖ ^ 2 / (‖π q‖ ^ 2 + ‖π' q‖ ^ 2)) q :=
      hnum.continuous.continuousAt.div hden.continuous.continuousAt hpos
    have hlt : ∀ᶠ q' in 𝓝 q, ‖π q'‖ ^ 2 / (‖π q'‖ ^ 2 + ‖π' q'‖ ^ 2) < 1 / 4 :=
      hratio.eventually (gt_mem_nhds (by simp [hq0]))
    refine contDiffAt_const (c := (0 : V →L[ℂ] W)).congr_of_eventuallyEq ?_
    filter_upwards [hlt] with q' hq'
    rw [χ.apply_eq_zero_of_le_one_div_four hq'.le, zero_smul]
  · have hpos : ‖π q‖ ^ 2 + ‖π' q‖ ^ 2 ≠ 0 := by positivity
    have hgq : ContDiffAt ℝ ∞ g (σ q, π q) :=
      hg.contDiffAt ((isOpen_compl_singleton.preimage continuous_snd).mem_nhds hq0)
    exact (χ.contDiff.contDiffAt.comp q (hnum.contDiffAt.div hden.contDiffAt hpos)).smul
      (hgq.comp q (hσ.prodMk hπ).contDiffAt)

/-- A homogeneous symbol `a` on the first factor, as a homogeneous symbol on the product cut off
near the axis `ξ = 0`: its coefficient at `((x, y), (ξ, η))` is
`χ(‖ξ‖² / (‖ξ‖² + ‖η‖²)) • a (x, ξ)`. The cutoff vanishes near every point with `ξ = 0` and
`η ≠ 0`, where `a` need not be smooth, so this is smooth on all of `(ξ, η) ≠ 0`; it equals `a` on
the cone `‖ξ‖ ≥ ‖η‖`. -/
def conicCutoffFst (χ : ConicCutoff) (a : HomogeneousSymbol X E V W m) :
    HomogeneousSymbol (X × Y) (E × F) V W m where
  coefficient p := χ (‖p.2.1‖ ^ 2 / (‖p.2.1‖ ^ 2 + ‖p.2.2‖ ^ 2)) • a.coefficient (p.1.1, p.2.1)
  zero_covector _ := by simp
  contDiffOn_coefficient :=
    (contDiffOn_conicCutoff_smul χ contDiff_fst.fst contDiff_snd.fst contDiff_snd.snd
      a.contDiffOn_coefficient).mono
      fun p hp ↦ by simpa [Prod.ext_iff, or_iff_not_imp_left] using hp
  homogeneous x ξ t ht := by
    simp only [Prod.smul_fst, Prod.smul_snd, conicRatio_smul _ _ ht, a.homogeneous _ _ t ht]
    exact smul_comm _ _ _

@[simp]
theorem coefficient_conicCutoffFst (χ : ConicCutoff) (a : HomogeneousSymbol X E V W m) (x : X)
    (y : Y) (ξ : E) (η : F) :
    (a.conicCutoffFst χ).coefficient ((x, y), (ξ, η)) =
      χ (‖ξ‖ ^ 2 / (‖ξ‖ ^ 2 + ‖η‖ ^ 2)) • a.coefficient (x, ξ) :=
  (rfl)

/-- On the cone `‖η‖ ≤ ‖ξ‖` the cutoff equals `1`, so the cut-off symbol agrees with `a`. -/
theorem coefficient_conicCutoffFst_of_norm_le (χ : ConicCutoff) (a : HomogeneousSymbol X E V W m)
    (x : X) (y : Y) {ξ : E} {η : F} (h : ‖η‖ ≤ ‖ξ‖) :
    (a.conicCutoffFst χ).coefficient ((x, y), (ξ, η)) = a.coefficient (x, ξ) := by
  rcases eq_or_ne ξ 0 with rfl | hξ
  · simp
  have hpos : 0 < ‖ξ‖ ^ 2 + ‖η‖ ^ 2 := by positivity
  have hle : ‖η‖ ^ 2 ≤ ‖ξ‖ ^ 2 := by gcongr
  rw [coefficient_conicCutoffFst,
    χ.apply_eq_one_of_one_div_two_le (by rw [le_div_iff₀ hpos]; linarith), one_smul]

/-- A homogeneous symbol `b` on the second factor, as a homogeneous symbol on the product cut
off near the axis `η = 0`: its coefficient at `((x, y), (ξ, η))` is
`χ(‖η‖² / (‖ξ‖² + ‖η‖²)) • b (y, η)`. -/
def conicCutoffSnd (χ : ConicCutoff) (b : HomogeneousSymbol Y F V W m) :
    HomogeneousSymbol (X × Y) (E × F) V W m where
  coefficient p := χ (‖p.2.2‖ ^ 2 / (‖p.2.1‖ ^ 2 + ‖p.2.2‖ ^ 2)) • b.coefficient (p.1.2, p.2.2)
  zero_covector _ := by simp
  contDiffOn_coefficient :=
    ((contDiffOn_conicCutoff_smul χ contDiff_fst.snd contDiff_snd.snd contDiff_snd.fst
      b.contDiffOn_coefficient).mono
      fun p hp ↦ by simpa [Prod.ext_iff, or_iff_not_imp_right] using hp).congr
      fun p _ ↦ by simp [add_comm]
  homogeneous x ξ t ht := by
    simp only [Prod.smul_fst, Prod.smul_snd, add_comm (‖t • ξ.1‖ ^ 2), add_comm (‖ξ.1‖ ^ 2),
      conicRatio_smul _ _ ht, b.homogeneous _ _ t ht]
    exact smul_comm _ _ _

@[simp]
theorem coefficient_conicCutoffSnd (χ : ConicCutoff) (b : HomogeneousSymbol Y F V W m) (x : X)
    (y : Y) (ξ : E) (η : F) :
    (b.conicCutoffSnd χ).coefficient ((x, y), (ξ, η)) =
      χ (‖η‖ ^ 2 / (‖ξ‖ ^ 2 + ‖η‖ ^ 2)) • b.coefficient (y, η) :=
  (rfl)

/-- On the cone `‖ξ‖ ≤ ‖η‖` the cutoff equals `1`, so the cut-off symbol agrees with `b`. -/
theorem coefficient_conicCutoffSnd_of_norm_le (χ : ConicCutoff) (b : HomogeneousSymbol Y F V W m)
    (x : X) (y : Y) {ξ : E} {η : F} (h : ‖ξ‖ ≤ ‖η‖) :
    (b.conicCutoffSnd χ).coefficient ((x, y), (ξ, η)) = b.coefficient (y, η) := by
  rcases eq_or_ne η 0 with rfl | hη
  · simp
  have hpos : 0 < ‖ξ‖ ^ 2 + ‖η‖ ^ 2 := by positivity
  have hle : ‖ξ‖ ^ 2 ≤ ‖η‖ ^ 2 := by gcongr
  rw [coefficient_conicCutoffSnd,
    χ.apply_eq_one_of_one_div_two_le (by rw [le_div_iff₀ hpos]; linarith), one_smul]

/-! ### The cut-off external product -/

section ExternalProduct

variable {V₀ V₁ W₀ W₁ : Type*} [NormedAddCommGroup V₀] [InnerProductSpace ℂ V₀] [CompleteSpace V₀]
  [NormedAddCommGroup V₁] [InnerProductSpace ℂ V₁] [CompleteSpace V₁] [NormedAddCommGroup W₀]
  [InnerProductSpace ℂ W₀] [CompleteSpace W₀] [NormedAddCommGroup W₁] [InnerProductSpace ℂ W₁]
  [CompleteSpace W₁]

open ContinuousLinearMap

/-- The cut-off external product of homogeneous symbols `a` on `X` and `b` on `Y` of the same
degree: the homogeneous symbol on `X × Y` whose coefficient at `((x, y), (ξ, η))` is the
external product block

`[[a' ⊗ 1, -(1 ⊗ b'*)], [1 ⊗ b', a'* ⊗ 1]] : (V₀ ⊗ W₀) ⊕ (V₁ ⊗ W₁) → (V₁ ⊗ W₀) ⊕ (V₀ ⊗ W₁)`

of the cut-off factors `a' = χ(‖ξ‖² / ρ²) a (x, ξ)` and `b' = χ(‖η‖² / ρ²) b (y, η)`, where
`ρ² = ‖ξ‖² + ‖η‖²`. -/
def externalProduct (χ : ConicCutoff) (a : HomogeneousSymbol X E V₀ V₁ m)
    (b : HomogeneousSymbol Y F W₀ W₁ m) :
    HomogeneousSymbol (X × Y) (E × F) (WithLp 2 ((V₀ ⊗[ℂ] W₀) × (V₁ ⊗[ℂ] W₁)))
      (WithLp 2 ((V₁ ⊗[ℂ] W₀) × (V₀ ⊗[ℂ] W₁))) m where
  coefficient p :=
    externalProductBlock ((a.conicCutoffFst χ).coefficient p) ((b.conicCutoffSnd χ).coefficient p)
  zero_covector _ := by simp
  contDiffOn_coefficient := contDiff_externalProductBlock.comp_contDiffOn
    ((a.conicCutoffFst χ).contDiffOn_coefficient.prodMk (b.conicCutoffSnd χ).contDiffOn_coefficient)
  homogeneous x ξ t ht := by
    rw [homogeneous _ _ _ _ ht, homogeneous _ _ _ _ ht, ← Complex.coe_smul, ← Complex.coe_smul,
      ← RCLike.ofReal_eq_complex_ofReal]
    -- The real action on block operators is the restriction of the complex one, so the right side
    -- `t ^ m • _` is `((t ^ m : ℝ) : ℂ) • _` by definition. `Complex.coe_smul` cannot rewrite it,
    -- because that action is reached through a different, definitionally equal instance path.
    exact externalProductBlock_ofReal_smul (t ^ m) _ _

@[simp]
theorem coefficient_externalProduct (χ : ConicCutoff) (a : HomogeneousSymbol X E V₀ V₁ m)
    (b : HomogeneousSymbol Y F W₀ W₁ m) (x : X) (y : Y) (ξ : E) (η : F) :
    (a.externalProduct χ b).coefficient ((x, y), (ξ, η)) =
      externalProductBlock (χ (‖ξ‖ ^ 2 / (‖ξ‖ ^ 2 + ‖η‖ ^ 2)) • a.coefficient (x, ξ))
        (χ (‖η‖ ^ 2 / (‖ξ‖ ^ 2 + ‖η‖ ^ 2)) • b.coefficient (y, η)) :=
  (rfl)

variable [CompleteSpace (V₀ ⊗[ℂ] W₀)] [CompleteSpace (V₁ ⊗[ℂ] W₁)] [CompleteSpace (V₁ ⊗[ℂ] W₀)]
  [CompleteSpace (V₀ ⊗[ℂ] W₁)] {a : HomogeneousSymbol X E V₀ V₁ 1}
  {b : HomogeneousSymbol Y F W₀ W₁ 1}

/-- For factors normalized by `a* a = a a* = ‖ξ‖²` and `b* b = b b* = ‖η‖²`, the cut-off external
product satisfies `A_χ* A_χ = χ(‖ξ‖² / ρ²)² ‖ξ‖² + χ(‖η‖² / ρ²)² ‖η‖²`, with
`ρ² = ‖ξ‖² + ‖η‖²`. -/
theorem adjoint_comp_coefficient_externalProduct (χ : ConicCutoff)
    (x : X) (y : Y) (ξ : E) (η : F)
    (ha : (a.coefficient (x, ξ)).adjoint ∘L a.coefficient (x, ξ) = ((‖ξ‖ ^ 2 : ℝ) : ℂ) • 1)
    (ha' : a.coefficient (x, ξ) ∘L (a.coefficient (x, ξ)).adjoint = ((‖ξ‖ ^ 2 : ℝ) : ℂ) • 1)
    (hb : (b.coefficient (y, η)).adjoint ∘L b.coefficient (y, η) = ((‖η‖ ^ 2 : ℝ) : ℂ) • 1)
    (hb' : b.coefficient (y, η) ∘L (b.coefficient (y, η)).adjoint = ((‖η‖ ^ 2 : ℝ) : ℂ) • 1) :
    ((a.externalProduct χ b).coefficient ((x, y), (ξ, η))).adjoint ∘L
        (a.externalProduct χ b).coefficient ((x, y), (ξ, η)) =
      ((χ (‖ξ‖ ^ 2 / (‖ξ‖ ^ 2 + ‖η‖ ^ 2)) ^ 2 * ‖ξ‖ ^ 2 +
        χ (‖η‖ ^ 2 / (‖ξ‖ ^ 2 + ‖η‖ ^ 2)) ^ 2 * ‖η‖ ^ 2 : ℝ) : ℂ) • 1 := by
  rw [← RCLike.ofReal_eq_complex_ofReal] at ha ha' hb hb'
  simp only [coefficient_externalProduct, ← Complex.coe_smul, ← RCLike.ofReal_eq_complex_ofReal]
  rw [adjoint_externalProductBlock_comp_self_of_eq_smul (adjoint_ofReal_smul_comp_ofReal_smul ha _)
    (ofReal_smul_comp_adjoint_ofReal_smul ha' _) (adjoint_ofReal_smul_comp_ofReal_smul hb _)
    (ofReal_smul_comp_adjoint_ofReal_smul hb' _), RCLike.ofReal_add]

/-- For factors normalized by `a* a = a a* = ‖ξ‖²` and `b* b = b b* = ‖η‖²`, the cut-off external
product satisfies `A_χ A_χ* = χ(‖ξ‖² / ρ²)² ‖ξ‖² + χ(‖η‖² / ρ²)² ‖η‖²`, with
`ρ² = ‖ξ‖² + ‖η‖²`. -/
theorem coefficient_externalProduct_comp_adjoint (χ : ConicCutoff)
    (x : X) (y : Y) (ξ : E) (η : F)
    (ha : (a.coefficient (x, ξ)).adjoint ∘L a.coefficient (x, ξ) = ((‖ξ‖ ^ 2 : ℝ) : ℂ) • 1)
    (ha' : a.coefficient (x, ξ) ∘L (a.coefficient (x, ξ)).adjoint = ((‖ξ‖ ^ 2 : ℝ) : ℂ) • 1)
    (hb : (b.coefficient (y, η)).adjoint ∘L b.coefficient (y, η) = ((‖η‖ ^ 2 : ℝ) : ℂ) • 1)
    (hb' : b.coefficient (y, η) ∘L (b.coefficient (y, η)).adjoint = ((‖η‖ ^ 2 : ℝ) : ℂ) • 1) :
    (a.externalProduct χ b).coefficient ((x, y), (ξ, η)) ∘L
        ((a.externalProduct χ b).coefficient ((x, y), (ξ, η))).adjoint =
      ((χ (‖ξ‖ ^ 2 / (‖ξ‖ ^ 2 + ‖η‖ ^ 2)) ^ 2 * ‖ξ‖ ^ 2 +
        χ (‖η‖ ^ 2 / (‖ξ‖ ^ 2 + ‖η‖ ^ 2)) ^ 2 * ‖η‖ ^ 2 : ℝ) : ℂ) • 1 := by
  rw [← RCLike.ofReal_eq_complex_ofReal] at ha ha' hb hb'
  simp only [coefficient_externalProduct, ← Complex.coe_smul, ← RCLike.ofReal_eq_complex_ofReal]
  rw [externalProductBlock_comp_adjoint_of_eq_smul (adjoint_ofReal_smul_comp_ofReal_smul ha _)
    (ofReal_smul_comp_adjoint_ofReal_smul ha' _) (adjoint_ofReal_smul_comp_ofReal_smul hb _)
    (ofReal_smul_comp_adjoint_ofReal_smul hb' _), RCLike.ofReal_add]

/-- Ellipticity of the cut-off external product of normalized factors:
`(‖ξ‖² + ‖η‖²) ‖w‖² ≤ 2 ‖A_χ w‖²`. -/
theorem le_two_mul_norm_coefficient_externalProduct_apply_sq (χ : ConicCutoff)
    (x : X) (y : Y) (ξ : E) (η : F)
    (ha : (a.coefficient (x, ξ)).adjoint ∘L a.coefficient (x, ξ) = ((‖ξ‖ ^ 2 : ℝ) : ℂ) • 1)
    (ha' : a.coefficient (x, ξ) ∘L (a.coefficient (x, ξ)).adjoint = ((‖ξ‖ ^ 2 : ℝ) : ℂ) • 1)
    (hb : (b.coefficient (y, η)).adjoint ∘L b.coefficient (y, η) = ((‖η‖ ^ 2 : ℝ) : ℂ) • 1)
    (hb' : b.coefficient (y, η) ∘L (b.coefficient (y, η)).adjoint = ((‖η‖ ^ 2 : ℝ) : ℂ) • 1)
    (w : WithLp 2 ((V₀ ⊗[ℂ] W₀) × (V₁ ⊗[ℂ] W₁))) :
    (‖ξ‖ ^ 2 + ‖η‖ ^ 2) * ‖w‖ ^ 2 ≤
      2 * ‖(a.externalProduct χ b).coefficient ((x, y), (ξ, η)) w‖ ^ 2 := by
  rw [norm_apply_sq_of_adjoint_comp_eq_smul
    (adjoint_comp_coefficient_externalProduct χ x y ξ η ha ha' hb hb') w, ← mul_assoc]
  gcongr
  exact χ.add_le_two_mul (by positivity) (by positivity)

/-- Ellipticity of the adjoint of the cut-off external product of normalized factors:
`(‖ξ‖² + ‖η‖²) ‖w‖² ≤ 2 ‖A_χ* w‖²`. -/
theorem le_two_mul_norm_adjoint_coefficient_externalProduct_apply_sq (χ : ConicCutoff)
    (x : X) (y : Y) (ξ : E) (η : F)
    (ha : (a.coefficient (x, ξ)).adjoint ∘L a.coefficient (x, ξ) = ((‖ξ‖ ^ 2 : ℝ) : ℂ) • 1)
    (ha' : a.coefficient (x, ξ) ∘L (a.coefficient (x, ξ)).adjoint = ((‖ξ‖ ^ 2 : ℝ) : ℂ) • 1)
    (hb : (b.coefficient (y, η)).adjoint ∘L b.coefficient (y, η) = ((‖η‖ ^ 2 : ℝ) : ℂ) • 1)
    (hb' : b.coefficient (y, η) ∘L (b.coefficient (y, η)).adjoint = ((‖η‖ ^ 2 : ℝ) : ℂ) • 1)
    (w : WithLp 2 ((V₁ ⊗[ℂ] W₀) × (V₀ ⊗[ℂ] W₁))) :
    (‖ξ‖ ^ 2 + ‖η‖ ^ 2) * ‖w‖ ^ 2 ≤
      2 * ‖((a.externalProduct χ b).coefficient ((x, y), (ξ, η))).adjoint w‖ ^ 2 := by
  rw [norm_apply_sq_of_adjoint_comp_eq_smul (by
    rw [adjoint_adjoint]; exact coefficient_externalProduct_comp_adjoint χ x y ξ η ha ha' hb hb') w,
    ← mul_assoc]
  gcongr
  exact χ.add_le_two_mul (by positivity) (by positivity)

end ExternalProduct

end HomogeneousSymbol

end TauCeti
