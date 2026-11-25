/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Lp.ProdLp
public import Mathlib.Analysis.Normed.Operator.NNNorm
public import Mathlib.LinearAlgebra.Dimension.LinearMap
public import Mathlib.Algebra.Algebra.Spectrum.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Invertible
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Analysis.Normed.Operator.Prod
import Mathlib.Topology.MetricSpace.Thickening
import TauCeti.LinearAlgebra.Dimension.Submodule
import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Invertible

/-!
# The `ℓ^p` product: coordinate bounds, components of indicators, and block sums

Mathlib bounds each factor of `WithLp p (α × β)` by the whole (`WithLp.norm_fst_le` and
`WithLp.norm_snd_le`) and computes the norm exactly for `p = 1` and `p = 2`.  This file records
the opposite bound, valid for every exponent `1 ≤ p ≤ ∞`: the `ℓ^p` norm of a pair is at most the
sum of the norms of its two components.  For `p = 1` the bound is an identity for every pair.
It also records that the `ℓ^p` norm is monotone and positively homogeneous in the component norms.
An open set containing `K × {0}`, for a compact set `K`, contains a whole tube
`{(x', y) | dist x' x < δ, ‖y‖ < δ}` around it.

It also records that taking a component of `WithLp p (α × β)` commutes with `Set.indicator`, as
Mathlib's `norm_indicator_eq_indicator_norm` does for the norm, that an indexed family of pairs in
`WithLp p (α × β)` has bounded range if and only if each coordinate family does, and that a graph
map `x ↦ (f x, u x)` into `WithLp p (E × V)` is the sum of `f` and `u` followed by the inclusions
of the two factors. The dimension of `WithLp p (M × M')` is the sum of the dimensions of the
factors.

Finally, it bundles the componentwise action of two continuous linear maps `f` and `g` on
`WithLp p (α × β)` as a continuous linear map `f.withLpProdMap p g`, the continuous counterpart of
Mathlib's `LinearIsometry.withLpProdMap`. For `p = 2` and inner product spaces this is the
orthogonal block sum `f ⊕ g`. It is compatible with the algebraic operations on the pair
`(f, g)` and continuous in it, its rank is the sum of the ranks of `f` and `g`, it is invertible
exactly when `f` and `g` are, so the spectrum of a block sum of endomorphisms is the union of
their spectra, and its operator norm is the larger of the two operator norms. The
projections onto the factors and the inclusions of the factors are contractions, and fixing one
coordinate embeds the other factor isometrically into `WithLp p (α × β)`. A kernel on
`WithLp p (X × Y)` consisting of the pairs whose components lie in the ranges of two injective
linear maps is identified with the product of their sources.

## Main statements

* `WithLp.prod_norm_le_norm_fst_add_norm_snd` — the bound `‖x‖ ≤ ‖x.fst‖ + ‖x.snd‖`.
* `WithLp.prod_norm_eq_norm_fst_of_snd_eq_zero`, `WithLp.prod_norm_eq_norm_snd_of_fst_eq_zero` —
  a pair with one vanishing component has the norm of the other.
* `IsCompact.exists_pos_forall_toLp_mem` — an open set containing `K × {0}`, for a compact set
  `K`, contains a tube `{(x', y) | dist x' x < δ, ‖y‖ < δ}` around it.
* `WithLp.prod_norm_nonneg` — the norm of a pair is nonnegative, in possibly noncommutative
  seminormed groups.
* `WithLp.prod_mul_norm_le_mul_norm` — componentwise bounds `c * ‖x.i‖ ≤ d * ‖y.i‖` give
  `c * ‖x‖ ≤ d * ‖y‖`.
* `TauCeti.snd_lt_one` — a unit vector in `E × ℝ` other than `(0, 1)` has last coordinate
  strictly less than `1`.
* `WithLp.fst_indicator`, `WithLp.snd_indicator` — a component of an indicator is the indicator
  of the component.
* `TauCeti.isBounded_range_toLp` — `Set.range (fun i ↦ WithLp.toLp p (f i, g i))` is bounded if
  and only if `Set.range f` and `Set.range g` are bounded.
* `TauCeti.toLp_prodMk_eq_add` — `x ↦ (f x, u x)` is `x ↦ ι₁ (f x) + ι₂ (u x)`.
* `ContinuousLinearMap.withLpProdMap` — the block sum `f ⊕ g` on `WithLp p (α × β)`.
* `LinearMap.rank_withLpMap` — lifting a linear map to `WithLp` preserves its rank.
* `WithLp.finrank_prod` — `WithLp p (M × M')` has dimension `finrank M + finrank M'`.
* `ContinuousLinearMap.rank_withLpProdMap` — `rank (f ⊕ g) = rank f + rank g`.
* `ContinuousLinearMap.finrank_range_withLpProdMap`,
  `ContinuousLinearMap.finiteDimensional_range_withLpProdMap_iff` — the same for finite ranks.
* `ContinuousLinearMap.isInvertible_withLpProdMap_iff` — `f ⊕ g` is invertible exactly when `f`
  and `g` are.
* `ContinuousLinearMap.spectrum_withLpProdMap` — the spectrum of `f ⊕ g` is the union of the
  spectra of `f` and `g`.
* `ContinuousLinearMap.norm_withLpProdMap` — `‖f ⊕ g‖ = max ‖f‖ ‖g‖`.
* `ContinuousLinearMap.kerEquivProdOfInjective` — a kernel on `WithLp p (X × Y)` that is the
  product of the ranges of two injective linear maps is equivalent to the product of their
  sources.
* `WithLp.norm_fstL_le_one`, `WithLp.norm_sndL_le_one`,
  `WithLp.norm_prodContinuousLinearEquiv_symm_comp_inl_le_one`,
  `WithLp.norm_prodContinuousLinearEquiv_symm_comp_inr_le_one` — the projections onto and the
  inclusions of the factors are contractions.
* `WithLp.isometry_toLp_prodMk_left`, `WithLp.isometry_toLp_prodMk_right` — fixing one coordinate
  embeds the other factor isometrically into `WithLp p (α × β)`.
-/

public section

open scoped ENNReal NNReal

universe u v

namespace TauCeti

variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {α β : Type*}

/-- A pair whose second component vanishes has the norm of its first component. -/
theorem _root_.WithLp.prod_norm_eq_norm_fst_of_snd_eq_zero [SeminormedAddCommGroup α]
    [SeminormedAddCommGroup β] {x : WithLp p (α × β)} (hx : x.snd = 0) : ‖x‖ = ‖x.fst‖ := by
  obtain ⟨a, b⟩ := x
  simp only [WithLp.toLp_snd] at hx
  subst hx
  simp only [WithLp.toLp_fst, WithLp.norm_toLp_fst]

/-- A pair whose first component vanishes has the norm of its second component. -/
theorem _root_.WithLp.prod_norm_eq_norm_snd_of_fst_eq_zero [SeminormedAddCommGroup α]
    [SeminormedAddCommGroup β] {x : WithLp p (α × β)} (hx : x.fst = 0) : ‖x‖ = ‖x.snd‖ := by
  obtain ⟨a, b⟩ := x
  simp only [WithLp.toLp_fst] at hx
  subst hx
  simp only [WithLp.toLp_snd, WithLp.norm_toLp_snd]

/-- The `ℓ^p` norm of a pair is at most the sum of the norms of its two components. -/
theorem _root_.WithLp.prod_norm_le_norm_fst_add_norm_snd [SeminormedAddCommGroup α]
    [SeminormedAddCommGroup β] (x : WithLp p (α × β)) :
    ‖x‖ ≤ ‖x.fst‖ + ‖x.snd‖ :=
  calc ‖x‖ = ‖WithLp.idemFst x + WithLp.idemSnd x‖ :=
        congrArg norm ((DFunLike.congr_fun WithLp.idemFst_add_idemSnd x).trans
          (AddMonoid.End.one_apply x)).symm
    _ ≤ ‖WithLp.idemFst x‖ + ‖WithLp.idemSnd x‖ := norm_add_le _ _
    _ = ‖x.fst‖ + ‖x.snd‖ := by
        rw [WithLp.idemFst_apply, WithLp.idemSnd_apply, WithLp.norm_toLp_fst,
          WithLp.norm_toLp_snd]

/-- An open set of `WithLp p (α × β)` containing `K × {0}` for a compact set `K` contains a tube
`{(x', y) | dist x' x < δ, ‖y‖ < δ}` around it. -/
theorem _root_.IsCompact.exists_pos_forall_toLp_mem [SeminormedAddCommGroup α]
    [SeminormedAddCommGroup β] {K : Set α} (hK : IsCompact K) {G : Set (WithLp p (α × β))}
    (hG : IsOpen G) (hKG : ∀ x ∈ K, WithLp.toLp p (x, (0 : β)) ∈ G) :
    ∃ δ > 0, ∀ x ∈ K, ∀ (x' : α) (y : β), dist x' x < δ → ‖y‖ < δ →
      WithLp.toLp p (x', y) ∈ G := by
  have hc : Continuous fun x : α ↦ WithLp.toLp p (x, (0 : β)) :=
    (WithLp.prod_continuous_toLp p α β).comp (continuous_id.prodMk continuous_const)
  obtain ⟨ε, hε, hεG⟩ := (hK.image hc).exists_cthickening_subset_open hG
    (Set.image_subset_iff.2 hKG)
  refine ⟨ε / 2, half_pos hε, fun x hx x' y hx' hy ↦ hεG ?_⟩
  refine Metric.mem_cthickening_of_dist_le _ _ _ _ (Set.mem_image_of_mem _ hx) ?_
  rw [dist_eq_norm, ← WithLp.toLp_sub, Prod.mk_sub_mk, sub_zero]
  refine (WithLp.prod_norm_le_norm_fst_add_norm_snd _).trans ?_
  rw [WithLp.toLp_fst, WithLp.toLp_snd, ← dist_eq_norm]
  linarith

/-- The `ℓ^p` norm of a pair is nonnegative, in any seminormed additive groups, which need not be
commutative. -/
theorem _root_.WithLp.prod_norm_nonneg [SeminormedAddGroup α] [SeminormedAddGroup β]
    (x : WithLp p (α × β)) : 0 ≤ ‖x‖ := by
  rcases p.dichotomy with rfl | hp
  · rw [WithLp.prod_norm_eq_sup]
    exact le_sup_of_le_left (norm_nonneg _)
  · rw [WithLp.prod_norm_eq_add (zero_lt_one.trans_le hp)]
    positivity

/-- The case `0 ≤ c, d` of `WithLp.prod_mul_norm_le_mul_norm`. -/
private theorem prod_mul_norm_le_mul_norm_of_nonneg {γ δ : Type*} [SeminormedAddGroup α]
    [SeminormedAddGroup β] [SeminormedAddGroup γ] [SeminormedAddGroup δ] {c d : ℝ} (hc : 0 ≤ c)
    (hd : 0 ≤ d) {x : WithLp p (α × β)} {y : WithLp p (γ × δ)} (h₁ : c * ‖x.fst‖ ≤ d * ‖y.fst‖)
    (h₂ : c * ‖x.snd‖ ≤ d * ‖y.snd‖) :
    c * ‖x‖ ≤ d * ‖y‖ := by
  rcases p.dichotomy with rfl | hp
  · rw [WithLp.prod_norm_eq_sup, WithLp.prod_norm_eq_sup, mul_max_of_nonneg _ _ hc,
      mul_max_of_nonneg _ _ hd]
    exact max_le_max h₁ h₂
  -- For finite `p`, move the constant inside the `p`-th root and compare termwise.
  have hp₀ : 0 < p.toReal := zero_lt_one.trans_le hp
  have key {e a b : ℝ} (he : 0 ≤ e) (ha : 0 ≤ a) (hb : 0 ≤ b) :
      e * (a ^ p.toReal + b ^ p.toReal) ^ (1 / p.toReal) =
        ((e * a) ^ p.toReal + (e * b) ^ p.toReal) ^ (1 / p.toReal) := by
    rw [Real.mul_rpow he ha, Real.mul_rpow he hb, ← mul_add,
      Real.mul_rpow (Real.rpow_nonneg he _) (by positivity), ← Real.rpow_mul he,
      mul_one_div_cancel hp₀.ne', Real.rpow_one]
  rw [WithLp.prod_norm_eq_add hp₀, WithLp.prod_norm_eq_add hp₀, key hc (norm_nonneg _)
    (norm_nonneg _), key hd (norm_nonneg _) (norm_nonneg _)]
  gcongr

/-- The `ℓ^p` norm of a pair is monotone and positively homogeneous in the norms of its
components: a componentwise bound `c * ‖x.i‖ ≤ d * ‖y.i‖` gives `c * ‖x‖ ≤ d * ‖y‖`. -/
theorem _root_.WithLp.prod_mul_norm_le_mul_norm {γ δ : Type*} [SeminormedAddGroup α]
    [SeminormedAddGroup β] [SeminormedAddGroup γ] [SeminormedAddGroup δ] {c d : ℝ}
    {x : WithLp p (α × β)} {y : WithLp p (γ × δ)} (h₁ : c * ‖x.fst‖ ≤ d * ‖y.fst‖)
    (h₂ : c * ‖x.snd‖ ≤ d * ‖y.snd‖) :
    c * ‖x‖ ≤ d * ‖y‖ := by
  rcases le_or_gt 0 d with hd | hd
  · rcases le_or_gt 0 c with hc | hc
    · exact prod_mul_norm_le_mul_norm_of_nonneg hc hd h₁ h₂
    · exact (mul_nonpos_of_nonpos_of_nonneg hc.le (WithLp.prod_norm_nonneg x)).trans
        (mul_nonneg hd (WithLp.prod_norm_nonneg y))
  · -- the bounds force `y = 0`, so both sides vanish when `0 ≤ c`
    rcases le_or_gt 0 c with hc | hc
    · have hy₁ : 1 * ‖y.fst‖ ≤ 0 * ‖x.fst‖ := by
        nlinarith [mul_nonneg hc (norm_nonneg x.fst), norm_nonneg y.fst]
      have hy₂ : 1 * ‖y.snd‖ ≤ 0 * ‖x.snd‖ := by
        nlinarith [mul_nonneg hc (norm_nonneg x.snd), norm_nonneg y.snd]
      have hx₁ : c * ‖x.fst‖ ≤ 0 * ‖y.fst‖ := by
        nlinarith [mul_nonneg (neg_nonneg.mpr hd.le) (norm_nonneg y.fst)]
      have hx₂ : c * ‖x.snd‖ ≤ 0 * ‖y.snd‖ := by
        nlinarith [mul_nonneg (neg_nonneg.mpr hd.le) (norm_nonneg y.snd)]
      have hy := prod_mul_norm_le_mul_norm_of_nonneg zero_le_one le_rfl hy₁ hy₂
      have hx := prod_mul_norm_le_mul_norm_of_nonneg hc le_rfl hx₁ hx₂
      nlinarith
    · have := prod_mul_norm_le_mul_norm_of_nonneg (neg_nonneg.mpr hd.le) (neg_nonneg.mpr hc.le)
        (x := y) (y := x) (by linarith) (by linarith)
      linarith

section Real

variable {E : Type*} [NormedAddCommGroup E]

/-- A unit vector of `E × ℝ` other than the vertical one `(0, 1)` has height less than `1`. -/
theorem snd_lt_one {u : WithLp 2 (E × ℝ)} (hnorm : ‖u‖ = 1)
    (hu : u ≠ WithLp.toLp 2 (0, 1)) : u.snd < 1 := by
  have hle : u.snd ≤ 1 := (le_abs_self _).trans ((WithLp.norm_snd_le (x := u)).trans hnorm.le)
  refine hle.lt_of_ne fun h ↦ hu ((WithLp.ext_iff 2).2 (Prod.ext ?_ (by simpa using h)))
  have hsq := WithLp.prod_norm_sq_eq_of_L2 u
  rw [hnorm, h] at hsq
  simpa using hsq

end Real

section Indicator

variable {p : ℝ≥0∞} {ι α β : Type*} [AddCommGroup α] [AddCommGroup β] {s : Set ι}

/-- The first component of an indicator function is the indicator of the first components. -/
theorem _root_.WithLp.fst_indicator (f : ι → WithLp p (α × β)) (x : ι) :
    (s.indicator f x).fst = s.indicator (fun y => (f y).fst) x :=
  (congr_fun (Set.indicator_comp_of_zero (g := WithLp.fst) WithLp.zero_fst) x).symm

/-- The second component of an indicator function is the indicator of the second components. -/
theorem _root_.WithLp.snd_indicator (f : ι → WithLp p (α × β)) (x : ι) :
    (s.indicator f x).snd = s.indicator (fun y => (f y).snd) x :=
  (congr_fun (Set.indicator_comp_of_zero (g := WithLp.snd) WithLp.zero_snd) x).symm

end Indicator

section Bornology

variable {p : ℝ≥0∞} {ι : Sort*} {α β : Type*} [Bornology α] [Bornology β]

/-- A family of pairs in `WithLp p (α × β)` has bounded range if and only if each coordinate
family has bounded range. -/
@[simp]
theorem isBounded_range_toLp {f : ι → α} {g : ι → β} :
    Bornology.IsBounded (Set.range fun i ↦ WithLp.toLp p (f i, g i)) ↔
      Bornology.IsBounded (Set.range f) ∧ Bornology.IsBounded (Set.range g) := by
  have hfst : Prod.fst '' (WithLp.ofLp '' Set.range fun i ↦ WithLp.toLp p (f i, g i)) =
      Set.range f := by
    rw [Set.image_image, ← Set.range_comp]; rfl
  have hsnd : Prod.snd '' (WithLp.ofLp '' Set.range fun i ↦ WithLp.toLp p (f i, g i)) =
      Set.range g := by
    rw [Set.image_image, ← Set.range_comp]; rfl
  rw [Bornology.isBounded_induced, ← Bornology.isBounded_image_fst_and_snd, hfst, hsnd]

end Bornology

section Graph

variable {p : ℝ≥0∞} {𝕜 : Type*} [NormedField 𝕜]

/-- The map `x ↦ (f x, u x)` into the `Lᵖ` product is `x ↦ ι₁ (f x) + ι₂ (u x)`, read through the
identification `WithLp p (E × V) ≃L E × V`; for `f = id` this is the graph of `u`. -/
theorem toLp_prodMk_eq_add {α E V : Type*} [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
    [SeminormedAddCommGroup V] [NormedSpace 𝕜 V] (f : α → E) (u : α → V) :
    (fun x ↦ WithLp.toLp p (f x, u x)) = fun x ↦
      (WithLp.prodContinuousLinearEquiv p 𝕜 E V).symm.toContinuousLinearMap
          (ContinuousLinearMap.inl 𝕜 E V (f x)) +
        (WithLp.prodContinuousLinearEquiv p 𝕜 E V).symm.toContinuousLinearMap
          (ContinuousLinearMap.inr 𝕜 E V (u x)) := by
  funext x
  simp [WithLp.ext_iff]

end Graph

end TauCeti

namespace LinearMap

/-- Lifting a linear map to `WithLp` does not change its rank. -/
theorem rank_withLpMap {p : ℝ≥0∞} {K V V' : Type*} [Semiring K] [AddCommGroup V] [Module K V]
    [AddCommGroup V'] [Module K V'] (f : V →ₗ[K] V') : (f.withLpMap p).rank = f.rank := by
  -- Conjugating by the linear equivalences `WithLp.linearEquiv` does not change the range's rank.
  rw [LinearMap.rank, LinearMap.withLpMap, LinearMap.range_comp,
    LinearMap.range_comp_of_range_eq_top _ (LinearEquiv.range _)]
  exact LinearEquiv.rank_map_eq _ _

end LinearMap

/-- The `L^p` product of two finite free modules has the sum of their dimensions. -/
@[simp]
theorem WithLp.finrank_prod {p : ℝ≥0∞} {R M M' : Type*} [Ring R] [StrongRankCondition R]
    [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M]
    [AddCommGroup M'] [Module R M'] [Module.Free R M'] [Module.Finite R M'] :
    Module.finrank R (WithLp p (M × M')) = Module.finrank R M + Module.finrank R M' := by
  rw [(WithLp.linearEquiv p R (M × M')).finrank_eq, Module.finrank_prod]

namespace ContinuousLinearMap

section Topological

variable (p : ℝ≥0∞) {𝕜 α β α' β' : Type*} [Semiring 𝕜]
  [TopologicalSpace α] [AddCommGroup α] [Module 𝕜 α]
  [TopologicalSpace β] [AddCommGroup β] [Module 𝕜 β]
  [TopologicalSpace α'] [AddCommGroup α'] [Module 𝕜 α']
  [TopologicalSpace β'] [AddCommGroup β'] [Module 𝕜 β']

/-- The `L^p` product of two continuous linear maps: the block sum `f ⊕ g`, acting componentwise
on `WithLp p (α × β)`. -/
def withLpProdMap (f : α →L[𝕜] α') (g : β →L[𝕜] β') :
    WithLp p (α × β) →L[𝕜] WithLp p (α' × β') :=
  (WithLp.prodContinuousLinearEquiv p 𝕜 α' β').symm.toContinuousLinearMap ∘L f.prodMap g ∘L
    (WithLp.prodContinuousLinearEquiv p 𝕜 α β).toContinuousLinearMap

/-- The block sum `f ⊕ g` is `f.prodMap g`, conjugated by the identification of
`WithLp p (α × β)` with `α × β`. -/
theorem withLpProdMap_def (f : α →L[𝕜] α') (g : β →L[𝕜] β') :
    f.withLpProdMap p g =
      (WithLp.prodContinuousLinearEquiv p 𝕜 α' β').symm.toContinuousLinearMap ∘L f.prodMap g ∘L
        (WithLp.prodContinuousLinearEquiv p 𝕜 α β).toContinuousLinearMap :=
  (rfl)

variable {p}

@[simp]
theorem withLpProdMap_apply (f : α →L[𝕜] α') (g : β →L[𝕜] β') (x : WithLp p (α × β)) :
    f.withLpProdMap p g x = WithLp.toLp p (f x.fst, g x.snd) :=
  (rfl)

@[simp]
theorem coe_withLpProdMap (f : α →L[𝕜] α') (g : β →L[𝕜] β') :
    (f.withLpProdMap p g : WithLp p (α × β) →ₗ[𝕜] WithLp p (α' × β')) =
      ((f : α →ₗ[𝕜] α').prodMap (g : β →ₗ[𝕜] β')).withLpMap p :=
  (rfl)

/-- The block sum of zero maps is zero. -/
@[simp]
theorem withLpProdMap_zero :
    (0 : α →L[𝕜] α').withLpProdMap p (0 : β →L[𝕜] β') = 0 := by
  ext x
  simp

/-- The block sum of the identities is the identity. -/
@[simp]
theorem withLpProdMap_id :
    (ContinuousLinearMap.id 𝕜 α).withLpProdMap p (ContinuousLinearMap.id 𝕜 β) =
      ContinuousLinearMap.id 𝕜 (WithLp p (α × β)) :=
  (rfl)

/-- The block sum of the units is the unit. -/
@[simp]
theorem withLpProdMap_one : (1 : α →L[𝕜] α).withLpProdMap p (1 : β →L[𝕜] β) = 1 :=
  (rfl)

/-- The block sum of composites is the composite of the block sums. -/
theorem withLpProdMap_comp {α'' β'' : Type*} [TopologicalSpace α''] [AddCommGroup α'']
    [Module 𝕜 α''] [TopologicalSpace β''] [AddCommGroup β''] [Module 𝕜 β''] (f' : α' →L[𝕜] α'')
    (f : α →L[𝕜] α') (g' : β' →L[𝕜] β'') (g : β →L[𝕜] β') :
    (f'.comp f).withLpProdMap p (g'.comp g) = (f'.withLpProdMap p g').comp (f.withLpProdMap p g) :=
  (rfl)

/-- The block sum of products is the product of the block sums. -/
theorem withLpProdMap_mul (f f' : α →L[𝕜] α) (g g' : β →L[𝕜] β) :
    (f * f').withLpProdMap p (g * g') = f.withLpProdMap p g * f'.withLpProdMap p g' :=
  (rfl)

/-- A block sum is invertible exactly when both blocks are. -/
@[simp]
theorem isInvertible_withLpProdMap_iff {f : α →L[𝕜] α'} {g : β →L[𝕜] β'} :
    (f.withLpProdMap p g).IsInvertible ↔ f.IsInvertible ∧ g.IsInvertible := by
  simp only [withLpProdMap_def, isInvertible_equiv_comp, isInvertible_comp_equiv,
    isInvertible_prodMap_iff]

/-- A block sum of endomorphisms is a unit exactly when both blocks are. -/
@[simp]
theorem isUnit_withLpProdMap_iff {f : α →L[𝕜] α} {g : β →L[𝕜] β} :
    IsUnit (f.withLpProdMap p g) ↔ IsUnit f ∧ IsUnit g := by
  simp only [← isInvertible_iff_isUnit, isInvertible_withLpProdMap_iff]

end Topological

section Seminormed

-- `Fact (1 ≤ p)` and the seminorms on `α'` and `β'` provide the topological additive group
-- structure on `WithLp p (α' × β')`, which the operations on continuous linear maps into it need.
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {𝕜 α β α' β' : Type*} [Semiring 𝕜]
  [TopologicalSpace α] [AddCommGroup α] [Module 𝕜 α]
  [TopologicalSpace β] [AddCommGroup β] [Module 𝕜 β]
  [SeminormedAddCommGroup α'] [Module 𝕜 α'] [SeminormedAddCommGroup β'] [Module 𝕜 β']

/-- The block sum of sums is the sum of the block sums. -/
theorem withLpProdMap_add (f f' : α →L[𝕜] α') (g g' : β →L[𝕜] β') :
    (f + f').withLpProdMap p (g + g') = f.withLpProdMap p g + f'.withLpProdMap p g' := by
  ext x
  simp [← WithLp.toLp_add]

end Seminormed

section SeminormedRing

variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {𝕜 α β α' β' : Type*} [Ring 𝕜]
  [TopologicalSpace α] [AddCommGroup α] [Module 𝕜 α]
  [TopologicalSpace β] [AddCommGroup β] [Module 𝕜 β]
  [SeminormedAddCommGroup α'] [Module 𝕜 α'] [SeminormedAddCommGroup β'] [Module 𝕜 β']

/-- The block sum of negations is the negation of the block sum. -/
theorem withLpProdMap_neg (f : α →L[𝕜] α') (g : β →L[𝕜] β') :
    (-f).withLpProdMap p (-g) = -f.withLpProdMap p g := by
  ext x
  simp [← WithLp.toLp_neg]

/-- The block sum of differences is the difference of the block sums. -/
theorem withLpProdMap_sub (f f' : α →L[𝕜] α') (g g' : β →L[𝕜] β') :
    (f - f').withLpProdMap p (g - g') = f.withLpProdMap p g - f'.withLpProdMap p g' := by
  ext x
  simp [← WithLp.toLp_sub]

end SeminormedRing

/-- The rank of a block sum with free ranges is the sum of the ranks of the blocks. -/
theorem rank_withLpProdMap {p : ℝ≥0∞} {𝕜 α β : Type*} {α' : Type u} {β' : Type v}
    [Semiring 𝕜] [StrongRankCondition 𝕜] [TopologicalSpace α] [AddCommGroup α] [Module 𝕜 α]
    [TopologicalSpace β] [AddCommGroup β] [Module 𝕜 β]
    [TopologicalSpace α'] [AddCommGroup α'] [Module 𝕜 α']
    [TopologicalSpace β'] [AddCommGroup β'] [Module 𝕜 β'] (f : α →L[𝕜] α') (g : β →L[𝕜] β')
    [Module.Free 𝕜 f.range] [Module.Free 𝕜 g.range] :
    (f.withLpProdMap p g).rank = Cardinal.lift.{v} f.rank + Cardinal.lift.{u} g.rank := by
  rw [coe_withLpProdMap, LinearMap.rank_withLpMap, LinearMap.rank_prodMap]

section DivisionRing

variable {p : ℝ≥0∞} {𝕜 α β α' β' : Type*} [DivisionRing 𝕜]
  [TopologicalSpace α] [AddCommGroup α] [Module 𝕜 α]
  [TopologicalSpace β] [AddCommGroup β] [Module 𝕜 β]
  [TopologicalSpace α'] [AddCommGroup α'] [Module 𝕜 α']
  [TopologicalSpace β'] [AddCommGroup β'] [Module 𝕜 β']

/-- The rank of a block sum is the sum of the ranks of its blocks, when these are finite. -/
theorem finrank_range_withLpProdMap (f : α →L[𝕜] α') (g : β →L[𝕜] β')
    [FiniteDimensional 𝕜 f.range] [FiniteDimensional 𝕜 g.range] :
    Module.finrank 𝕜 (f.withLpProdMap p g).range =
      Module.finrank 𝕜 f.range + Module.finrank 𝕜 g.range := by
  have h := rank_withLpProdMap (p := p) f g
  rw [LinearMap.rank, LinearMap.rank, LinearMap.rank] at h
  rw [Module.finrank, Module.finrank, Module.finrank, h]
  exact Cardinal.toNat_lift_add_lift (Module.rank_lt_aleph0 _ _) (Module.rank_lt_aleph0 _ _)

/-- A block sum has finite rank exactly when both blocks do. -/
@[simp]
theorem finiteDimensional_range_withLpProdMap_iff {f : α →L[𝕜] α'} {g : β →L[𝕜] β'} :
    FiniteDimensional 𝕜 (f.withLpProdMap p g).range ↔
      FiniteDimensional 𝕜 f.range ∧ FiniteDimensional 𝕜 g.range := by
  have h := rank_withLpProdMap (p := p) f g
  rw [LinearMap.rank, LinearMap.rank, LinearMap.rank] at h
  simp only [← Module.rank_lt_aleph0_iff, h, Cardinal.add_lt_aleph0_iff, Cardinal.lift_lt_aleph0]

end DivisionRing

section Normed

variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {𝕜 α β α' β' : Type*} [NontriviallyNormedField 𝕜]
  [SeminormedAddCommGroup α] [NormedSpace 𝕜 α] [SeminormedAddCommGroup β] [NormedSpace 𝕜 β]
  [SeminormedAddCommGroup α'] [NormedSpace 𝕜 α'] [SeminormedAddCommGroup β'] [NormedSpace 𝕜 β']

/-- The operator norm of an `L^p` block sum is the larger of the operator norms of the blocks. -/
@[simp]
theorem norm_withLpProdMap (f : α →L[𝕜] α') (g : β →L[𝕜] β') :
    ‖f.withLpProdMap p g‖ = max ‖f‖ ‖g‖ := by
  refine le_antisymm (opNorm_le_bound _ (by positivity) fun x ↦ ?_) (max_le ?_ ?_)
  · rw [← one_mul ‖_‖]
    refine WithLp.prod_mul_norm_le_mul_norm ?_ ?_ <;>
      rw [withLpProdMap_apply, one_mul]
    · exact (f.le_opNorm _).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
    · exact (g.le_opNorm _).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _))
  · refine opNorm_le_bound _ (norm_nonneg _) fun x ↦ ?_
    simpa using (f.withLpProdMap p g).le_opNorm (WithLp.toLp p (x, 0))
  · refine opNorm_le_bound _ (norm_nonneg _) fun x ↦ ?_
    simpa using (f.withLpProdMap p g).le_opNorm (WithLp.toLp p (0, x))

/-- The operator norm of an `L^p` block sum is the larger of the operator norms of the blocks,
stated for `‖·‖₊`. -/
@[simp]
theorem nnnorm_withLpProdMap (f : α →L[𝕜] α') (g : β →L[𝕜] β') :
    ‖f.withLpProdMap p g‖₊ = max ‖f‖₊ ‖g‖₊ :=
  NNReal.eq <| by simp

/-- The block sum of scalar multiples is the scalar multiple of the block sum. -/
theorem withLpProdMap_smul (c : 𝕜) (f : α →L[𝕜] α') (g : β →L[𝕜] β') :
    (c • f).withLpProdMap p (c • g) = c • f.withLpProdMap p g :=
  (rfl)

/-- The block sum depends continuously on its blocks. -/
@[fun_prop]
theorem _root_.Continuous.withLpProdMap {X : Type*} [TopologicalSpace X] {f : X → α →L[𝕜] α'}
    {g : X → β →L[𝕜] β'} (hf : Continuous f) (hg : Continuous g) :
    Continuous fun x ↦ (f x).withLpProdMap p (g x) :=
  continuous_const.clm_comp
    (((prodMapL 𝕜 α α' β β').continuous.comp (hf.prodMk hg)).clm_comp continuous_const)

/-- The block sum depends continuously on its blocks. -/
@[fun_prop]
theorem _root_.ContinuousOn.withLpProdMap {X : Type*} [TopologicalSpace X] {f : X → α →L[𝕜] α'}
    {g : X → β →L[𝕜] β'} {s : Set X} (hf : ContinuousOn f s) (hg : ContinuousOn g s) :
    ContinuousOn (fun x ↦ (f x).withLpProdMap p (g x)) s :=
  continuousOn_const.clm_comp
    (((prodMapL 𝕜 α α' β β').continuous.comp_continuousOn (hf.prodMk hg)).clm_comp
      continuousOn_const)

/-- The spectrum of a block sum of endomorphisms is the union of the spectra of its blocks. -/
@[simp]
theorem spectrum_withLpProdMap {R : Type*} [CommSemiring R] [Algebra R 𝕜] [Algebra R (α →L[𝕜] α)]
    [Algebra R (β →L[𝕜] β)] [Algebra R (WithLp p (α × β) →L[𝕜] WithLp p (α × β))]
    [IsScalarTower R 𝕜 (α →L[𝕜] α)] [IsScalarTower R 𝕜 (β →L[𝕜] β)]
    [IsScalarTower R 𝕜 (WithLp p (α × β) →L[𝕜] WithLp p (α × β))] (f : α →L[𝕜] α)
    (g : β →L[𝕜] β) :
    spectrum R (f.withLpProdMap p g) = spectrum R f ∪ spectrum R g := by
  ext r
  have h : algebraMap R (WithLp p (α × β) →L[𝕜] WithLp p (α × β)) r =
      (algebraMap R (α →L[𝕜] α) r).withLpProdMap p (algebraMap R (β →L[𝕜] β) r) := by
    rw [IsScalarTower.algebraMap_apply R 𝕜, IsScalarTower.algebraMap_apply R 𝕜 (α →L[𝕜] α),
      IsScalarTower.algebraMap_apply R 𝕜 (β →L[𝕜] β)]
    generalize algebraMap R 𝕜 r = k
    simp only [Algebra.algebraMap_eq_smul_one, withLpProdMap_smul, withLpProdMap_one]
  simp only [spectrum.mem_iff, Set.mem_union, h, ← withLpProdMap_sub, isUnit_withLpProdMap_iff,
    not_and_or]

end Normed

section KerEquivProd

variable {p : ℝ≥0∞} {R X Y Z M₁ M₂ : Type*} [Semiring R] [AddCommGroup X] [Module R X]
  [TopologicalSpace X] [AddCommGroup Y] [Module R Y] [TopologicalSpace Y] [AddCommGroup Z]
  [Module R Z] [TopologicalSpace Z] [AddCommMonoid M₁] [Module R M₁] [AddCommMonoid M₂]
  [Module R M₂] (T : WithLp p (X × Y) →L[R] Z) {ι₁ : M₁ →ₗ[R] X} {ι₂ : M₂ →ₗ[R] Y}
  (h₁ : Function.Injective ι₁) (h₂ : Function.Injective ι₂)
  (hT : ∀ w, T w = 0 ↔ w.fst ∈ LinearMap.range ι₁ ∧ w.snd ∈ LinearMap.range ι₂)

/-- The kernel of an operator on `WithLp p (X × Y)`, when it consists of the pairs whose components
lie in the ranges of two injective linear maps, is linearly equivalent to the product of their
sources. -/
noncomputable def kerEquivProdOfInjective : T.ker ≃ₗ[R] M₁ × M₂ :=
  (LinearEquiv.ofInjective ((WithLp.linearEquiv p R _).symm.toLinearMap ∘ₗ ι₁.prodMap ι₂)
      ((WithLp.linearEquiv p R _).symm.injective.comp <| Prod.map_injective.mpr ⟨h₁, h₂⟩) ≪≫ₗ
    LinearEquiv.ofEq _ _ (by
      ext w
      rw [LinearMap.mem_ker, coe_coe, hT]
      constructor
      · rintro ⟨⟨x, y⟩, rfl⟩
        exact ⟨⟨x, rfl⟩, ⟨y, rfl⟩⟩
      · rintro ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
        exact ⟨(x, y),
          WithLp.ofLp_injective p <| Prod.ext (by simpa using hx) (by simpa using hy)⟩)).symm

/-- `kerEquivProdOfInjective` sends a pair to the pair of its images under the two injections. -/
@[simp]
theorem coe_kerEquivProdOfInjective_symm_apply (q : M₁ × M₂) :
    ((kerEquivProdOfInjective T h₁ h₂ hT).symm q : WithLp p (X × Y)) =
      WithLp.toLp p (ι₁ q.1, ι₂ q.2) := by
  simp [kerEquivProdOfInjective]

/-- The first component of `kerEquivProdOfInjective w` is the preimage of the first component of
`w` under the first injection. -/
@[simp]
theorem apply_kerEquivProdOfInjective_apply_fst (w : T.ker) :
    ι₁ (kerEquivProdOfInjective T h₁ h₂ hT w).1 = (w : WithLp p (X × Y)).fst := by
  obtain ⟨q, rfl⟩ := (kerEquivProdOfInjective T h₁ h₂ hT).symm.surjective w
  simp

/-- The second component of `kerEquivProdOfInjective w` is the preimage of the second component of
`w` under the second injection. -/
@[simp]
theorem apply_kerEquivProdOfInjective_apply_snd (w : T.ker) :
    ι₂ (kerEquivProdOfInjective T h₁ h₂ hT w).2 = (w : WithLp p (X × Y)).snd := by
  obtain ⟨q, rfl⟩ := (kerEquivProdOfInjective T h₁ h₂ hT).symm.surjective w
  simp

end KerEquivProd

end ContinuousLinearMap

namespace WithLp

section Contraction

variable (p : ℝ≥0∞) [Fact (1 ≤ p)] (𝕜 α β : Type*) [NontriviallyNormedField 𝕜]
  [SeminormedAddCommGroup α] [NormedSpace 𝕜 α] [SeminormedAddCommGroup β] [NormedSpace 𝕜 β]

/-- The projection of `WithLp p (α × β)` onto its first factor is a contraction. -/
theorem norm_fstL_le_one : ‖fstL p 𝕜 α β‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x ↦ by simpa using norm_fst_le (x := x)

/-- The projection of `WithLp p (α × β)` onto its second factor is a contraction. -/
theorem norm_sndL_le_one : ‖sndL p 𝕜 α β‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x ↦ by simpa using norm_snd_le (x := x)

/-- The inclusion of the first factor into `WithLp p (α × β)` is a contraction. -/
theorem norm_prodContinuousLinearEquiv_symm_comp_inl_le_one :
    ‖(prodContinuousLinearEquiv p 𝕜 α β).symm.toContinuousLinearMap ∘L
      ContinuousLinearMap.inl 𝕜 α β‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x ↦ by simp

/-- The inclusion of the second factor into `WithLp p (α × β)` is a contraction. -/
theorem norm_prodContinuousLinearEquiv_symm_comp_inr_le_one :
    ‖(prodContinuousLinearEquiv p 𝕜 α β).symm.toContinuousLinearMap ∘L
      ContinuousLinearMap.inr 𝕜 α β‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x ↦ by simp

end Contraction

/-- Fixing the first coordinate, `y ↦ WithLp.toLp p (x, y)` is an isometry into
`WithLp p (α × β)`. -/
theorem isometry_toLp_prodMk_left (p : ℝ≥0∞) [Fact (1 ≤ p)] {α β : Type*}
    [PseudoEMetricSpace α] [PseudoEMetricSpace β] (x : α) :
    Isometry fun y : β ↦ toLp p (x, y) := by
  intro y₁ y₂
  rcases p.dichotomy with rfl | hp
  · simp [prod_edist_eq_sup]
  · have hp₀ : 0 < p.toReal := zero_lt_one.trans_le hp
    simp [prod_edist_eq_add hp₀, ENNReal.zero_rpow_of_pos hp₀, ENNReal.rpow_rpow_inv hp₀.ne']

/-- Fixing the second coordinate, `x ↦ WithLp.toLp p (x, y)` is an isometry into
`WithLp p (α × β)`. -/
theorem isometry_toLp_prodMk_right (p : ℝ≥0∞) [Fact (1 ≤ p)] {α β : Type*}
    [PseudoEMetricSpace α] [PseudoEMetricSpace β] (y : β) :
    Isometry fun x : α ↦ toLp p (x, y) := by
  simpa [Function.comp_def] using
    (IsometryEquiv.withLpProdComm p β α).isometry.comp (isometry_toLp_prodMk_left p y)

end WithLp
