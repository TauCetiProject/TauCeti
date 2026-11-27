/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Module.Seminorm.WeightedSup
public import TauCeti.Analysis.Pseudodifferential.Symbol.Homogeneous
public import TauCeti.Analysis.Pseudodifferential.Symbol.Topology
import Mathlib.Analysis.Normed.Module.Normalize
import TauCeti.Analysis.Calculus.IteratedFDeriv.Parametric
import TauCeti.Analysis.Pseudodifferential.HomogeneousSymbol.IteratedFDeriv
import TauCeti.Analysis.SpecialFunctions.JapaneseBracket.Bounds
import TauCeti.Analysis.SpecialFunctions.JapaneseBracket.Peetre
import TauCeti.Analysis.SpecialFunctions.Pow.Bounds

/-!
# The topology of the homogeneous symbols

The homogeneous symbols of degree `m` on `ℝⁿ` carry the C^∞ topology on compact sets of positions
times the unit sphere of frequencies: for a compact set `K` and words `α`, `β` of coordinate
indices, the seminorm `TauCeti.HomogeneousSymbol.seminorm K α β a` is the best constant `C` in

`‖∂_x^α ∂_ξ^β a(x, ξ)‖ ≤ C ‖ξ‖ ^ (m - |β|)` for `x ∈ K` and `ξ ≠ 0`.

Since `∂_x^α ∂_ξ^β a` is homogeneous of degree `m - |β|`, this is the supremum of
`‖∂_x^α ∂_ξ^β a(x, ξ)‖` over `x ∈ K` and `‖ξ‖ = 1`
(`TauCeti.HomogeneousSymbol.seminorm_le_iff_norm_eq_one`). The cut-off term `χ(ξ) a(x, ξ)`, which
lifts a homogeneous symbol to a symbol of order `m`, depends continuously on `a` in this topology.

## Main results

* `TauCeti.HomogeneousSymbol.seminorm`, `TauCeti.HomogeneousSymbol.withSeminorms`: the seminorms
  and the locally convex topology they induce on the homogeneous symbols of degree `m`; it is
  Hausdorff (`TauCeti.HomogeneousSymbol.instT1Space`).
* `TauCeti.HomogeneousSymbol.mixedDerivCLM`: every mixed derivative at a point with nonzero
  frequency is a continuous linear function of the homogeneous symbol.
* `TauCeti.HomogeneousSymbol.continuous_iff_forall_continuousOn_iteratedFDeriv`: a family of
  homogeneous symbols is continuous in this topology exactly when its jets are jointly continuous
  in the parameter, the position and the frequency away from the zero frequency.
* `TauCeti.HomogeneousSymbol.continuous_of_contDiffOn`: in particular a family whose coefficient
  is jointly smooth in a real parameter, the position and the frequency is continuous. So the
  jointly smooth homotopies of elliptic symbols used in index theory are continuous paths in every
  seminorm `p_{K,α,β}`, and by `TauCeti.HomogeneousSymbol.continuous_cutoffSymbol` their cut-off
  terms are continuous paths of symbols of order `m`.
* `TauCeti.HomogeneousSymbol.exists_seminorm_cutoffSymbol_le`: the seminorm `p_{K,α,β}` of the
  cut-off term `χ(ξ) a(x, ξ)` in the symbol class `S^m_{1,0}` is bounded by finitely many
  seminorms `p_{K,α,β'}(a)` with `|β'| ≤ |β|`, with a constant depending only on `χ`, `m` and `β`.
* `TauCeti.HomogeneousSymbol.cutoffSymbolCLM`: the cut-off term as a continuous linear map from
  the homogeneous symbols of degree `m` to the symbols of order `m`.

## Implementation notes

A family is continuous exactly when its jets are jointly continuous because, at a nonzero
frequency, the mixed derivatives of order `k` and the Fréchet derivative of order `k` bound each
other (`TauCeti.HomogeneousSymbol.norm_mixedDeriv_coefficient_le`,
`TauCeti.HomogeneousSymbol.norm_iteratedFDeriv_coefficient_le_sum`), while uniform convergence on a
compact set of positions times the unit sphere follows from joint continuity there
(`IsCompact.mem_uniformity_of_prod`).

The seminorms are the best constants `Seminorm.weightedSup` of the weighted estimates above, like
the seminorms `TauCeti.Symbol.seminorm` of the symbol classes.

A homogeneous symbol is not smooth at the zero frequency, so the Leibniz rule for the cut-off
term is applied, near a frequency `ξ₀ ≠ 0`, to a smooth function with the same germ as `a`
(`TauCeti.HomogeneousSymbol.exists_contDiff_eventuallyEq_coefficient`). The cutoff `χ` satisfies
the symbol estimates of order zero
(`TauCeti.FrequencyCutoff.exists_norm_iteratedFDeriv_comp_inv_smul_le`) and vanishes on the unit
ball; outside it `‖ξ‖` and `⟨ξ⟩` are comparable.

## References

* R. B. Melrose, *Introduction to Microlocal Analysis*, §5.3, Proposition 5.2: the quantization of
  principal symbols by frequency cutoffs.
* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, §18.1.
-/

public section

noncomputable section

open Filter Topology
open scoped ContDiff
open TopologicalSpace (Compacts)

namespace TauCeti

variable {n : ℕ} {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W]
  [NormedSpace ℂ W] {m : ℝ}

namespace HomogeneousSymbol

/-! ### The seminorms -/

section Seminorm

/-- The mixed derivative `a ↦ ∂_x^α ∂_ξ^β a(x, ξ)` at a nonzero frequency, as a linear map. -/
private def mixedDerivLinearMap (α β : List (Fin n)) (x : CoordinateSpace n)
    (ξ : {ξ : CoordinateSpace n // ξ ≠ 0}) :
    HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W m →ₗ[ℂ] V →L[ℂ] W where
  toFun a := mixedDeriv α β a.coefficient x ξ
  map_add' a b := mixedDeriv_coefficient_add a b α β x ξ.property
  map_smul' c a := by
    rw [coefficient_smul, mixedDeriv_const_smul, RingHom.id_apply]

/-- The seminorm `p_{K,α,β}` on the homogeneous symbols of degree `m`: the best constant `C` in
the estimate `‖∂_x^α ∂_ξ^β a(x, ξ)‖ ≤ C ‖ξ‖ ^ (m - |β|)` for all positions `x ∈ K` and all
nonzero frequencies `ξ`. It is the supremum of `‖∂_x^α ∂_ξ^β a‖` over `K` times the unit sphere
(`HomogeneousSymbol.seminorm_le_iff_norm_eq_one`). -/
protected def seminorm (K : Compacts (CoordinateSpace n)) (α β : List (Fin n)) :
    Seminorm ℂ (HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W m) :=
  Seminorm.weightedSup
    (fun i : K × {ξ : CoordinateSpace n // ξ ≠ 0} => mixedDerivLinearMap α β i.1 i.2)
    (fun i => ‖(i.2 : CoordinateSpace n)‖ ^ (m - β.length))
    (fun i => Real.rpow_pos_of_pos (norm_pos_iff.2 i.2.property) _)

/-- Every homogeneous symbol satisfies the weighted estimates defining
`HomogeneousSymbol.seminorm K α β`. -/
private theorem exists_bound_mixedDerivLinearMap (K : Compacts (CoordinateSpace n))
    (α β : List (Fin n)) (a : HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W m) :
    ∃ C, ∀ i : K × {ξ : CoordinateSpace n // ξ ≠ 0},
      ‖mixedDerivLinearMap α β i.1 i.2 a‖ ≤ C * ‖(i.2 : CoordinateSpace n)‖ ^ (m - β.length) :=
  let ⟨C, _, h⟩ := a.exists_norm_mixedDeriv_le K.isCompact α β
  ⟨C, fun i => h i.1 i.1.property i.2 i.2.property⟩

/-- The seminorm `p_{K,α,β}(a)` bounds `‖∂_x^α ∂_ξ^β a(x, ξ)‖ / ‖ξ‖ ^ (m - |β|)` for `x ∈ K`
and `ξ ≠ 0`. -/
theorem le_seminorm (K : Compacts (CoordinateSpace n)) (α β : List (Fin n))
    (a : HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W m)
    {x : CoordinateSpace n} (hx : x ∈ K) {ξ : CoordinateSpace n} (hξ : ξ ≠ 0) :
    ‖mixedDeriv α β a.coefficient x ξ‖ ≤
      HomogeneousSymbol.seminorm K α β a * ‖ξ‖ ^ (m - β.length) :=
  Seminorm.norm_le_weightedSup
    (fun i : K × {ξ : CoordinateSpace n // ξ ≠ 0} => mixedDerivLinearMap α β i.1 i.2) _ _
    (exists_bound_mixedDerivLinearMap K α β) a (⟨x, hx⟩, ⟨ξ, hξ⟩)

/-- A constant in the estimate of `∂_x^α ∂_ξ^β a` on `K` bounds the seminorm `p_{K,α,β}(a)`. -/
theorem seminorm_le_bound (K : Compacts (CoordinateSpace n)) (α β : List (Fin n))
    (a : HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W m) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ x ∈ K, ∀ ξ, ξ ≠ 0 →
      ‖mixedDeriv α β a.coefficient x ξ‖ ≤ C * ‖ξ‖ ^ (m - β.length)) :
    HomogeneousSymbol.seminorm K α β a ≤ C :=
  Seminorm.weightedSup_le _ _ _ hC fun i => h i.1 i.1.property i.2 i.2.property

/-- The seminorm `p_{K,α,β}(a)` is at most `C ≥ 0` exactly when `C` is a constant in the estimate
of `∂_x^α ∂_ξ^β a` on `K`. -/
theorem seminorm_le_iff {K : Compacts (CoordinateSpace n)} {α β : List (Fin n)}
    {a : HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W m} {C : ℝ} (hC : 0 ≤ C) :
    HomogeneousSymbol.seminorm K α β a ≤ C ↔ ∀ x ∈ K, ∀ ξ, ξ ≠ 0 →
      ‖mixedDeriv α β a.coefficient x ξ‖ ≤ C * ‖ξ‖ ^ (m - β.length) := by
  refine ⟨fun h x hx ξ hξ => (le_seminorm K α β a hx hξ).trans ?_, seminorm_le_bound K α β a hC⟩
  exact mul_le_mul_of_nonneg_right h (Real.rpow_nonneg (norm_nonneg ξ) _)

/-- **The seminorms are the C^∞ seminorms on the unit sphere.** The seminorm `p_{K,α,β}(a)` is at
most `C ≥ 0` exactly when `‖∂_x^α ∂_ξ^β a(x, ξ)‖ ≤ C` for `x ∈ K` and `‖ξ‖ = 1`. -/
theorem seminorm_le_iff_norm_eq_one {K : Compacts (CoordinateSpace n)} {α β : List (Fin n)}
    {a : HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W m} {C : ℝ} (hC : 0 ≤ C) :
    HomogeneousSymbol.seminorm K α β a ≤ C ↔ ∀ x ∈ K, ∀ ξ, ‖ξ‖ = 1 →
      ‖mixedDeriv α β a.coefficient x ξ‖ ≤ C := by
  rw [seminorm_le_iff hC]
  refine ⟨fun h x hx ξ hξ => by simpa [hξ] using h x hx ξ (norm_ne_zero_iff.1 (by simp [hξ])),
    fun h x hx ξ hξ => ?_⟩
  -- Rescale `ξ` to the unit sphere and use the homogeneity of `∂_x^α ∂_ξ^β a`.
  have hn : 0 < ‖ξ‖ := norm_pos_iff.2 hξ
  have hscale : mixedDeriv α β a.coefficient x ξ =
      ‖ξ‖ ^ (m - β.length) • mixedDeriv α β a.coefficient x (NormedSpace.normalize ξ) := by
    rw [← mixedDeriv_coefficient_smul_frequency a α β x
      ((NormedSpace.normalize_eq_zero_iff ξ).not.2 hξ) hn, NormedSpace.norm_smul_normalize]
  rw [hscale, norm_smul, Real.norm_of_nonneg (Real.rpow_nonneg hn.le _), mul_comm]
  exact mul_le_mul_of_nonneg_right (h x hx _ (NormedSpace.norm_normalize_eq_one_iff.2 hξ))
    (Real.rpow_nonneg hn.le _)

end Seminorm

/-! ### The topology -/

section Topology

variable (n V W m) in
/-- The family of all seminorms `p_{K,α,β}` on the homogeneous symbols of degree `m`, indexed by
the compact sets `K` of positions and the words `α`, `β` of coordinate indices. -/
def seminormFamily :
    SeminormFamily ℂ (HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W m)
      (Compacts (CoordinateSpace n) × List (Fin n) × List (Fin n)) :=
  fun i => HomogeneousSymbol.seminorm i.1 i.2.1 i.2.2

@[simp]
theorem seminormFamily_apply (K : Compacts (CoordinateSpace n)) (α β : List (Fin n)) :
    seminormFamily n V W m (K, α, β) = HomogeneousSymbol.seminorm K α β := (rfl)

/-- The topology of the homogeneous symbols of degree `m`: the locally convex topology of the
seminorms `p_{K,α,β}`, that is, of uniform convergence of all mixed derivatives on compact sets of
positions times the unit sphere of frequencies. -/
instance instTopologicalSpace :
    TopologicalSpace (HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W m) :=
  (seminormFamily n V W m).moduleFilterBasis.topology'

/-- The topology of the homogeneous symbols is induced by the seminorms `p_{K,α,β}`. -/
theorem withSeminorms : WithSeminorms (seminormFamily n V W m) :=
  ⟨rfl⟩

instance instIsTopologicalAddGroup :
    IsTopologicalAddGroup (HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W m) :=
  (seminormFamily n V W m).addGroupFilterBasis.isTopologicalAddGroup

instance instContinuousSMul :
    ContinuousSMul ℂ (HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W m) :=
  withSeminorms.continuousSMul

instance instLocallyConvexSpace :
    LocallyConvexSpace ℝ (HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W m) :=
  withSeminorms.toLocallyConvexSpace

/-- The homogeneous symbols form a T1, hence Hausdorff, space: the seminorms `p_{K,[],[]}` over
the singletons `K = {x}` separate them. -/
instance instT1Space :
    T1Space (HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W m) := by
  refine withSeminorms.T1_of_separating fun a ha => ?_
  obtain ⟨x, ξ, hξ, hxξ⟩ : ∃ x ξ, ξ ≠ 0 ∧ a.coefficient (x, ξ) ≠ 0 := by
    by_contra! h
    exact ha (ext_of_ne_zero fun x ξ hξ => by simpa using h x ξ hξ)
  refine ⟨({x}, [], []), fun h0 => hxξ (norm_le_zero_iff.1 ?_)⟩
  have h := le_seminorm {x} [] [] a rfl hξ
  rwa [← seminormFamily_apply, h0, zero_mul, mixedDeriv_nil_nil] at h

variable (V W m) in
/-- The mixed derivative `a ↦ ∂_x^α ∂_ξ^β a(x, ξ)` at a nonzero frequency `ξ`, as a continuous
linear map on the homogeneous symbols of degree `m`; in particular the value `a ↦ a(x, ξ)` for
`α = β = []`. -/
def mixedDerivCLM (α β : List (Fin n)) (x : CoordinateSpace n) {ξ : CoordinateSpace n}
    (hξ : ξ ≠ 0) :
    HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W m →L[ℂ] V →L[ℂ] W where
  toLinearMap := mixedDerivLinearMap α β x ⟨ξ, hξ⟩
  cont := WithSeminorms.continuous_of_isBounded withSeminorms (norm_withSeminorms ℂ _) _
    (Seminorm.IsBounded.of_real fun _ => ⟨{({x}, α, β)}, ‖ξ‖ ^ (m - β.length), fun a => by
      simpa [mixedDerivLinearMap, mul_comm] using le_seminorm {x} α β a rfl hξ⟩)

@[simp]
theorem mixedDerivCLM_apply (α β : List (Fin n)) (x : CoordinateSpace n) {ξ : CoordinateSpace n}
    (hξ : ξ ≠ 0) (a : HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W m) :
    mixedDerivCLM V W m α β x hξ a = mixedDeriv α β a.coefficient x ξ := (rfl)

end Topology

/-! ### Continuous families of homogeneous symbols -/

section Family

/-- Near a nonzero frequency `ξ₀`, frequencies are nonzero and every power of their norm is
bounded by the same power of `‖ξ₀‖ / 2` plus that of `3 ‖ξ₀‖ / 2`. -/
private theorem eventually_rpow_norm_le {ξ₀ : CoordinateSpace n} (hξ₀ : ξ₀ ≠ 0) :
    ∀ᶠ ξ in 𝓝 ξ₀, ξ ≠ 0 ∧ ∀ e : ℝ, ‖ξ‖ ^ e ≤ (‖ξ₀‖ / 2) ^ e + (3 * (‖ξ₀‖ / 2)) ^ e := by
  have hr : 0 < ‖ξ₀‖ / 2 := by positivity
  filter_upwards [Metric.ball_mem_nhds ξ₀ hr] with ξ hξ
  rw [Metric.mem_ball, dist_eq_norm] at hξ
  have hlo : ‖ξ₀‖ / 2 ≤ ‖ξ‖ := by linarith [norm_sub_norm_le ξ₀ ξ, norm_sub_rev ξ₀ ξ]
  have hhi : ‖ξ‖ ≤ 3 * (‖ξ₀‖ / 2) := by linarith [norm_sub_norm_le ξ ξ₀]
  refine ⟨norm_pos_iff.1 (hr.trans_le hlo), fun e ↦ ?_⟩
  rcases le_total 0 e with he | he
  · exact (Real.rpow_le_rpow (norm_nonneg _) hhi he).trans
      (le_add_of_nonneg_left (Real.rpow_nonneg hr.le _))
  · exact (Real.rpow_le_rpow_of_nonpos hr hlo he).trans
      (le_add_of_nonneg_right (Real.rpow_nonneg (by positivity) _))

/-- Continuous families of homogeneous symbols have jointly continuous jets. -/
private theorem continuousOn_iteratedFDeriv_of_continuous {Y : Type*} [TopologicalSpace Y]
    {a : Y → HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W m} (ha : Continuous a)
    (k : ℕ) :
    ContinuousOn
      (fun p : Y × (CoordinateSpace n × CoordinateSpace n) ↦
        iteratedFDeriv ℝ k (a p.1).coefficient p.2)
      (Set.univ ×ˢ {p | p.2 ≠ 0}) := by
  rintro ⟨y₀, x₀, ξ₀⟩ ⟨-, hξ₀ : ξ₀ ≠ 0⟩
  refine ContinuousAt.continuousWithinAt ?_
  -- Split `D^k (a y)` as `D^k (a y - a y₀) + D^k (a y₀)`; the second term is continuous.
  have hG : ContinuousAt (fun p : Y × (CoordinateSpace n × CoordinateSpace n) ↦
      iteratedFDeriv ℝ k (a y₀).coefficient p.2) (y₀, x₀, ξ₀) :=
    (((a y₀).contDiffAt_coefficient hξ₀).continuousAt_iteratedFDeriv
      (by exact_mod_cast le_top)).comp continuous_snd.continuousAt
  -- Near `(x₀, ξ₀)`, positions lie in the closed unit ball `K` about `x₀` and the powers of the
  -- frequency norms are bounded.
  set K : Compacts (CoordinateSpace n) := ⟨Metric.closedBall x₀ 1, isCompact_closedBall _ _⟩
  set α : (Fin k → Fin n ⊕ Fin n) → List (Fin n) := fun w ↦ (List.ofFn w).filterMap Sum.getLeft?
  set β : (Fin k → Fin n ⊕ Fin n) → List (Fin n) := fun w ↦ (List.ofFn w).filterMap Sum.getRight?
  set C : ℝ → ℝ := fun e ↦ (‖ξ₀‖ / 2) ^ e + (3 * (‖ξ₀‖ / 2)) ^ e
  have hnear : ∀ᶠ p : Y × (CoordinateSpace n × CoordinateSpace n) in 𝓝 (y₀, x₀, ξ₀),
      p.2.1 ∈ K ∧ p.2.2 ≠ 0 ∧ ∀ e : ℝ, ‖p.2.2‖ ^ e ≤ C e :=
    ((continuous_snd.fst.tendsto (y₀, x₀, ξ₀)).eventually
        (Metric.closedBall_mem_nhds x₀ one_pos)).and
      ((continuous_snd.snd.tendsto (y₀, x₀, ξ₀)).eventually (eventually_rpow_norm_le hξ₀))
  -- The difference is bounded by seminorms of `a y - a y₀`, which tend to `0`.
  have hF : Tendsto (fun p : Y × (CoordinateSpace n × CoordinateSpace n) ↦
      iteratedFDeriv ℝ k (a p.1 - a y₀).coefficient p.2) (𝓝 (y₀, x₀, ξ₀)) (𝓝 0) := by
    have hc : Continuous fun p : Y × (CoordinateSpace n × CoordinateSpace n) ↦
        ∑ w, HomogeneousSymbol.seminorm K (α w) (β w) (a p.1 - a y₀) * C (m - (β w).length) :=
      continuous_finsetSum _ fun w _ ↦
        ((withSeminorms.continuous_seminorm (K, α w, β w)).comp
          ((ha.comp continuous_fst).sub continuous_const)).mul continuous_const
    refine squeeze_zero_norm' ?_ (by simpa using hc.tendsto (y₀, x₀, ξ₀))
    filter_upwards [hnear] with p ⟨hpK, hp0, hpC⟩
    refine (norm_iteratedFDeriv_coefficient_le_sum _ k p.2.1 hp0).trans
      (Finset.sum_le_sum fun w _ ↦ ?_)
    exact (le_seminorm K (α w) (β w) _ hpK hp0).trans
      (mul_le_mul_of_nonneg_left (hpC _) (apply_nonneg _ _))
  have h := hF.add hG
  rw [zero_add] at h
  refine h.congr' ?_
  filter_upwards [hnear] with p ⟨_, hp0, _⟩
  rw [iteratedFDeriv_coefficient_sub _ _ _ hp0, sub_add_cancel]

/-- Families of homogeneous symbols with jointly continuous jets are continuous: as `y` tends to
`y₀`, every mixed derivative of `a y` converges to that of `a y₀` uniformly on compact sets of
positions times the unit sphere. -/
private theorem continuous_of_continuousOn_iteratedFDeriv {Y : Type*} [TopologicalSpace Y]
    {a : Y → HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W m}
    (ha : ∀ k : ℕ, ContinuousOn
      (fun p : Y × (CoordinateSpace n × CoordinateSpace n) ↦
        iteratedFDeriv ℝ k (a p.1).coefficient p.2)
      (Set.univ ×ˢ {p | p.2 ≠ 0})) :
    Continuous a := by
  refine continuous_iff_continuousAt.2 fun y₀ ↦ (withSeminorms.tendsto_nhds _ _).2 ?_
  rintro ⟨K, α, β⟩ ε hε
  -- The jets of order `|α| + |β|` converge uniformly on `K` times the unit sphere.
  have hsub : (Set.univ : Set Y) ×ˢ ((K : Set (CoordinateSpace n)) ×ˢ Metric.sphere 0 1) ⊆
      Set.univ ×ˢ {p : CoordinateSpace n × CoordinateSpace n | p.2 ≠ 0} :=
    Set.prod_mono subset_rfl fun p hp ↦
      ne_zero_of_norm_ne_zero (by simp [mem_sphere_zero_iff_norm.1 hp.2])
  obtain ⟨v, hv, hvε⟩ := (K.isCompact.prod (isCompact_sphere 0 1)).mem_uniformity_of_prod
    (f := fun y q ↦ iteratedFDeriv ℝ (α.length + β.length) (a y).coefficient q)
    ((ha _).mono hsub) (Set.mem_univ y₀) (Metric.dist_mem_uniformity (half_pos hε))
  rw [nhdsWithin_univ] at hv
  filter_upwards [hv] with y hy
  rw [seminormFamily_apply]
  refine lt_of_le_of_lt ((seminorm_le_iff_norm_eq_one (half_pos hε).le).2 fun x hx ξ hξ ↦ ?_)
    (half_lt_self hε)
  have hξ0 : ξ ≠ 0 := ne_zero_of_norm_ne_zero (by simp [hξ])
  refine (norm_mixedDeriv_coefficient_le _ α β x hξ0).trans ?_
  rw [iteratedFDeriv_coefficient_sub _ _ _ hξ0, ← dist_eq_norm]
  exact (hvε y hy (x, ξ) ⟨hx, mem_sphere_zero_iff_norm.2 hξ⟩).le

/-- **The topology of the homogeneous symbols is that of joint continuity of jets.** A family
`y ↦ a y` of homogeneous symbols of degree `m` is continuous exactly when each Fréchet derivative
`D^k (a y)(x, ξ)` in the position and the frequency depends continuously on `(y, x, ξ)` away from
the zero frequency. -/
theorem continuous_iff_forall_continuousOn_iteratedFDeriv {Y : Type*} [TopologicalSpace Y]
    {a : Y → HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W m} :
    Continuous a ↔ ∀ k : ℕ, ContinuousOn
      (fun p : Y × (CoordinateSpace n × CoordinateSpace n) ↦
        iteratedFDeriv ℝ k (a p.1).coefficient p.2)
      (Set.univ ×ˢ {p | p.2 ≠ 0}) :=
  ⟨continuousOn_iteratedFDeriv_of_continuous, continuous_of_continuousOn_iteratedFDeriv⟩

/-- **Smooth families are continuous.** A family `a t` of homogeneous symbols of degree `m`, indexed
by a real normed space, whose coefficient `(t, x, ξ) ↦ (a t)(x, ξ)` is jointly smooth away from the
zero frequency, is continuous for the topology of the homogeneous symbols. This applies to the
smoothed homotopies of elliptic symbols of `HomogeneousSymbol.exists_contDiffOn_isElliptic_homotopy`
and `HomogeneousSymbol.exists_contDiffOn_isElliptic_equivariant_homotopy`, which are therefore
continuous paths in every seminorm `p_{K,α,β}`. -/
theorem continuous_of_contDiffOn {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {a : P → HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W m}
    (ha : ContDiffOn ℝ ∞
      (fun p : P × CoordinateSpace n × CoordinateSpace n ↦ (a p.1).coefficient p.2)
      {p | p.2.2 ≠ 0}) :
    Continuous a := by
  refine continuous_iff_forall_continuousOn_iteratedFDeriv.2 fun k p hp ↦ ?_
  have hU : {q : P × CoordinateSpace n × CoordinateSpace n | q.2.2 ≠ 0} ∈ 𝓝 p :=
    (isOpen_ne_fun (continuous_snd.comp continuous_snd) continuous_const).mem_nhds hp.2
  exact ((ha.contDiffAt hU).iteratedFDeriv_snd (f := fun t ↦ (a t).coefficient) (m := 0)
    (by simp)).continuousAt.continuousWithinAt

end Family

/-! ### The cut-off term depends continuously on the homogeneous symbol -/

section Cutoff

/-- **Seminorm estimate for the cut-off term.** For a frequency cutoff `χ`, the seminorm
`p_{K,α,β}` of the symbol `χ(ξ) a(x, ξ)` of order `m` is at most a constant times the sum of the
seminorms `p_{K,α,β'}(a)` of the homogeneous symbol `a` over all words `β'` with `|β'| ≤ |β|`.
The constant depends only on `χ`, `m` and `β`. -/
theorem exists_seminorm_cutoffSymbol_le (χ : FrequencyCutoff (CoordinateSpace n))
    (β : List (Fin n)) :
    ∃ C, 0 ≤ C ∧ ∀ (K : Compacts (CoordinateSpace n)) (α : List (Fin n))
      (a : HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W m),
      Symbol.seminorm K α β (cutoffSymbol χ a) ≤
        C * ∑ i ∈ Finset.range (β.length + 1), ∑ w : Fin (β.length - i) → Fin n,
          HomogeneousSymbol.seminorm K α (List.ofFn w) a := by
  set k := β.length
  -- The order-zero symbol estimates `‖D^i χ ξ‖ ⟨ξ⟩ ^ i ≤ B i` of the cutoff.
  choose B hB0 hB using fun i : ℕ => χ.exists_norm_iteratedFDeriv_comp_inv_smul_le i
  have hB' (i : ℕ) (ξ : CoordinateSpace n) :
      ‖iteratedFDeriv ℝ i χ ξ‖ * (1 + ‖ξ‖ ^ 2) ^ ((i : ℝ) / 2) ≤ B i := by
    have h := hB i 1 le_rfl ξ
    simp only [inv_one, one_smul] at h
    calc ‖iteratedFDeriv ℝ i χ ξ‖ * (1 + ‖ξ‖ ^ 2) ^ ((i : ℝ) / 2)
        ≤ B i * (1 + ‖ξ‖ ^ 2) ^ (-(i : ℝ) / 2) * (1 + ‖ξ‖ ^ 2) ^ ((i : ℝ) / 2) := by gcongr
      _ = B i := by rw [mul_assoc, one_add_norm_sq_rpow_neg_mul_rpow, mul_one]
  -- The constant in front of `∑_{|β'| = k - i} p_{K,α,β'}(a)`.
  set c : ℕ → ℝ := fun i => k.choose i * B i * 2 ^ (|m - ↑(k - i)| / 2)
  have hc (i : ℕ) : 0 ≤ c i := by have := hB0 i; positivity
  refine ⟨∑ i ∈ Finset.range (k + 1), c i, Finset.sum_nonneg fun i _ => hc i, fun K α a => ?_⟩
  set S := ∑ i ∈ Finset.range (k + 1), ∑ w : Fin (k - i) → Fin n,
    HomogeneousSymbol.seminorm K α (List.ofFn w) a
  have hS : 0 ≤ S := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => apply_nonneg _ _
  refine Symbol.seminorm_le_bound K α β _
    (mul_nonneg (Finset.sum_nonneg fun i _ => hc i) hS) fun x hx ξ => ?_
  rcases lt_or_ge ‖ξ‖ 1 with hξ | hξ
  · -- On the unit ball the cut-off term vanishes near `(x, ξ)`.
    have h0 : (cutoffSymbol χ a).coefficient =ᶠ[𝓝 (x, ξ)] 0 := by
      filter_upwards [continuous_snd.continuousAt.eventually
        (χ.eventuallyEq_zero_of_norm_lt_one hξ)] with q hq
      simp [hq]
    rw [h0.mixedDeriv_eq, mixedDeriv_zero, norm_zero]
    exact mul_nonneg (mul_nonneg (Finset.sum_nonneg fun i _ => hc i) hS) (rpow_weight_pos ξ _).le
  have hξ0 : ξ ≠ 0 := norm_pos_iff.1 (one_pos.trans_le hξ)
  -- Near `(x, ξ)`, replace `a` by a smooth function `f` with the same germ and apply the Leibniz
  -- rule.
  obtain ⟨f, hf, hfa⟩ := a.exists_contDiff_eventuallyEq_coefficient hξ0
  have heq : (cutoffSymbol χ a).coefficient =ᶠ[𝓝 (x, ξ)] fun p => χ p.2 • f p := by
    filter_upwards [hfa x] with q hq
    rw [coefficient_cutoffSymbol, hq]
  rw [heq.mixedDeriv_eq]
  refine (norm_mixedDeriv_comp_snd_smul_le_mul_rpow_weight χ.contDiff hf (m := m) (B := B)
    (D := fun w => 2 ^ (|m - w.length| / 2) * HomogeneousSymbol.seminorm K α w a)
    (fun i => hB' i ξ) (fun w => ?_) β).trans ?_
  · rw [(hfa x).mixedDeriv_eq, mul_comm (2 ^ _), mul_assoc]
    exact (le_seminorm K α w a hx hξ0).trans (mul_le_mul_of_nonneg_left (by
      simpa only [abs_norm] using Real.abs_rpow_le_two_rpow_mul_one_add_sq_rpow (t := ‖ξ‖)
        (by rwa [abs_norm]) (m - w.length)) (apply_nonneg _ _))
  refine mul_le_mul_of_nonneg_right ?_ (rpow_weight_pos ξ _).le
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i hi => ?_
  simp_rw [List.length_ofFn, ← Finset.mul_sum]
  refine (mul_assoc _ _ _).symm.trans_le (mul_le_mul_of_nonneg_left ?_ (hc i))
  exact Finset.single_le_sum (f := fun i => ∑ w : Fin (k - i) → Fin n,
    HomogeneousSymbol.seminorm K α (List.ofFn w) a)
    (fun _ _ => Finset.sum_nonneg fun _ _ => apply_nonneg _ _) hi

variable (V W m) in
/-- **Continuity of the cut-off term.** The symbol `χ(ξ) a(x, ξ)` of order `m` depends
continuously on the homogeneous symbol `a` of degree `m`. -/
theorem continuous_cutoffSymbol (χ : FrequencyCutoff (CoordinateSpace n)) :
    Continuous (cutoffSymbol (V := V) (W := W) (m := m) χ) := by
  refine WithSeminorms.continuous_of_isBounded withSeminorms Symbol.withSeminorms _
    (.of_real fun ⟨K, α, β⟩ => ?_)
  classical
  obtain ⟨C, hC, h⟩ := exists_seminorm_cutoffSymbol_le (V := V) (W := W) (m := m) χ β
  set k := β.length
  -- The finitely many seminorms `p_{K,α,β'}` with `|β'| ≤ |β|`, and their number.
  let s : Finset (Compacts (CoordinateSpace n) × List (Fin n) × List (Fin n)) :=
    (Finset.range (k + 1)).biUnion fun i =>
      Finset.univ.image fun w : Fin (k - i) → Fin n => (K, α, List.ofFn w)
  set N : ℝ := ∑ i ∈ Finset.range (k + 1), (Fintype.card (Fin (k - i) → Fin n) : ℝ)
  refine ⟨s, C * N, fun a => ?_⟩
  rw [Symbol.seminormFamily_apply, mul_assoc]
  refine (h K α a).trans (mul_le_mul_of_nonneg_left ?_ hC)
  calc ∑ i ∈ Finset.range (k + 1), ∑ w : Fin (k - i) → Fin n,
        HomogeneousSymbol.seminorm K α (List.ofFn w) a
      ≤ ∑ i ∈ Finset.range (k + 1), ∑ _w : Fin (k - i) → Fin n,
          (s.sup (seminormFamily n V W m)) a := by
        refine Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun w _ => ?_
        rw [← seminormFamily_apply]
        exact Seminorm.le_finset_sup_apply
          (Finset.mem_biUnion.2 ⟨i, hi, Finset.mem_image.2 ⟨w, Finset.mem_univ _, rfl⟩⟩)
    _ = N * (s.sup (seminormFamily n V W m)) a := by
        simp [N, Finset.sum_mul, Finset.card_univ]

/-- The cut-off term `a ↦ χ(ξ) a(x, ξ)` as a continuous linear map from the homogeneous symbols of
degree `m` to the symbols of order `m`. -/
def cutoffSymbolCLM (χ : FrequencyCutoff (CoordinateSpace n)) :
    HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W m →L[ℂ] Symbol n V W m where
  toLinearMap := cutoffSymbol χ
  cont := continuous_cutoffSymbol V W m χ

@[simp]
theorem cutoffSymbolCLM_apply (χ : FrequencyCutoff (CoordinateSpace n))
    (a : HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W m) :
    cutoffSymbolCLM χ a = cutoffSymbol χ a := (rfl)

end Cutoff

end HomogeneousSymbol

end TauCeti
