/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.RingOpNorm
import Mathlib.Topology.Baire.CompleteMetrizable

/-!
# Uniform boundedness over Tate rings

Mathlib proves the Banach–Steinhaus theorem (`banach_steinhaus`) for continuous semilinear maps
over a nontrivially normed field via barrelled locally convex spaces. For modules over a general
Tate normed ring (`TauCeti.NormedRing.IsTate`), the locally convex machinery does not apply,
because the scalar ring need not be a field. Instead, the Baire category theorem on the complete
pseudometrizable domain produces an open ball on which the family is uniformly bounded by an
integer constant, and rescaling into that ball by powers of a multiplicative pseudo-uniformiser
converts that local constant bound into a global operator-norm bound.

This file establishes:
* local-to-global operator-norm bounds (`ContinuousLinearMap.ringOpNorm_le_of_ball`,
  `ContinuousLinearMap.ringOpNorm_le_of_nhds_zero`, and the quantitative bound from a constant
  bound on a ball `TauCeti.NormedRing.PseudoUniformizer.ringOpNorm_le_of_forall_norm_lt`);
* the **Banach–Steinhaus theorem** (`TauCeti.NormedRing.IsTate.banach_steinhaus`) for pointwise
  bounded families of continuous linear maps from a complete seminormed module over a Tate ring;
* continuity and operator-norm bounds for pointwise limits of continuous linear maps along a
  filter (`LinearMap.continuous_of_tendsto_of_pointwise_bounded`,
  `LinearMap.continuous_of_tendsto_of_isTate`, `ContinuousLinearMap.ofTendstoOfPointwiseBounded`,
  `ContinuousLinearMap.ofTendstoOfIsTate`, and `ContinuousLinearMap.ringOpNorm_le_of_tendsto`).

No commutativity or ultrametric hypothesis on the Tate ring is required in this file.

## Main results

* `ContinuousLinearMap.ringOpNorm_le_of_ball`, `ContinuousLinearMap.ringOpNorm_le_of_nhds_zero`:
  if `‖f x‖ ≤ C * ‖x‖` holds near `0` over a Tate ring, then `‖f‖ ≤ C`.
* `TauCeti.NormedRing.PseudoUniformizer.ringOpNorm_le_of_forall_norm_lt`: if `‖f x‖ ≤ B` on the
  ball of radius `δ > ‖ϖ‖ ^ k`, then `‖f‖ ≤ B * (‖ϖ‖ ^ (k + 1))⁻¹`.
* `TauCeti.NormedRing.IsTate.banach_steinhaus`: a pointwise bounded family of continuous linear
  maps from a complete seminormed module over a Tate ring is uniformly bounded in operator norm.
* `ContinuousLinearMap.ofTendstoOfPointwiseBounded`, `ContinuousLinearMap.ofTendstoOfIsTate`:
  pointwise limits of continuous linear maps from a complete seminormed module over a Tate ring
  are continuous linear maps.

## References

* K. Buzzard, *The Analytic Continuation of p-adic Modular Forms* (eigenbook), §2.
* C. Johansson and J. Newton, *Extended eigenvarieties for overconvergent cohomology*,
  arXiv:1604.07739, §2.1.
* P. Schneider, *Nonarchimedean Functional Analysis*, Springer, 2002, Proposition 6.2.
-/

public section

open Filter Metric Set
open scoped Topology TauCeti.RingOpNorm

namespace ContinuousLinearMap

variable {R E F : Type*} [SeminormedRing R] [TauCeti.NormedRing.IsTate R]
  [SeminormedAddCommGroup E] [Module R E] [IsBoundedSMul R E]
  [SeminormedAddCommGroup F] [Module R F] [IsBoundedSMul R F]

/-- Over a Tate ring, a linear norm bound `‖f x‖ ≤ C * ‖x‖` on a ball around `0` extends to all of
`E` and bounds the operator norm `‖f‖` by `C`. -/
theorem ringOpNorm_le_of_ball (f : E →L[R] F) {ε C : ℝ} (hε : 0 < ε) (hC : 0 ≤ C)
    (hf : ∀ x ∈ ball (0 : E) ε, ‖f x‖ ≤ C * ‖x‖) :
    ‖f‖ ≤ C := by
  obtain ⟨ϖ⟩ := TauCeti.NormedRing.IsTate.nonempty_pseudoUniformizer (R := R)
  refine f.ringOpNorm_le_bound hC fun x ↦ ?_
  obtain ⟨k, hk⟩ : ∃ k : ℕ, ‖(ϖ.unit : R)‖ ^ k * ‖x‖ < ε := by
    rcases le_or_gt ‖x‖ 0 with hx | hx
    · refine ⟨0, lt_of_le_of_lt ?_ hε⟩
      simpa using hx
    · obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (div_pos hε hx) ϖ.norm_lt_one
      exact ⟨k, (lt_div_iff₀ hx).mp hk⟩
  have hmem : ((ϖ.unit ^ (k : ℤ) : Rˣ) : R) • x ∈ ball (0 : E) ε := by
    rw [mem_ball_zero_iff, ϖ.norm_zpow_smul, zpow_natCast]
    exact hk
  have hfk := hf _ hmem
  rw [map_smul, ϖ.norm_zpow_smul, ϖ.norm_zpow_smul, zpow_natCast] at hfk
  have hrk : 0 < ‖(ϖ.unit : R)‖ ^ k := pow_pos ϖ.norm_pos k
  exact le_of_mul_le_mul_left (by simpa [mul_left_comm] using hfk) hrk

/-- Over a Tate ring, if `‖f x‖ ≤ C * ‖x‖` holds in a neighbourhood of `0`, then `‖f‖ ≤ C`. -/
theorem ringOpNorm_le_of_nhds_zero (f : E →L[R] F) {C : ℝ} (hC : 0 ≤ C)
    (hf : ∀ᶠ x in 𝓝 (0 : E), ‖f x‖ ≤ C * ‖x‖) :
    ‖f‖ ≤ C := by
  obtain ⟨ε, hε, hfε⟩ := Metric.eventually_nhds_iff_ball.mp hf
  exact f.ringOpNorm_le_of_ball hε hC hfε

end ContinuousLinearMap

namespace TauCeti

namespace NormedRing.PseudoUniformizer

variable {R E F : Type*} [SeminormedRing R]
  [SeminormedAddCommGroup E] [Module R E] [IsBoundedSMul R E]
  [SeminormedAddCommGroup F] [Module R F] [IsBoundedSMul R F]

/-- **Quantitative local-to-global operator-norm bound.** If `ϖ` is a multiplicative
pseudo-uniformiser on `R`, `‖(ϖ.unit : R)‖ ^ k < δ`, and `‖f x‖ ≤ B` for every `x` of norm `< δ`,
then `‖f‖ ≤ B * (‖(ϖ.unit : R)‖ ^ (k + 1))⁻¹`. -/
theorem ringOpNorm_le_of_forall_norm_lt (ϖ : PseudoUniformizer R) (f : E →L[R] F)
    {δ B : ℝ} (k : ℤ) (hδ : ‖(ϖ.unit : R)‖ ^ k < δ) (hB : 0 ≤ B)
    (hf : ∀ x : E, ‖x‖ < δ → ‖f x‖ ≤ B) :
    ‖f‖ ≤ B * (‖(ϖ.unit : R)‖ ^ (k + 1))⁻¹ := by
  exact f.ringOpNorm_le_bound (by positivity)
    (ϖ.bound_of_forall_norm_lt f k hδ hB hf)

end NormedRing.PseudoUniformizer

namespace NormedRing.IsTate

variable {R E F : Type*} [SeminormedRing R] [IsTate R]
  [SeminormedAddCommGroup E] [Module R E] [IsBoundedSMul R E]
  [SeminormedAddCommGroup F] [Module R F] [IsBoundedSMul R F]

/-- **Banach–Steinhaus theorem (Uniform Boundedness Principle) over a Tate ring.**
If a family `g : ι → E →L[R] F` of continuous linear maps from a complete seminormed module `E`
over a Tate ring `R` is pointwise bounded, then the operator norms `‖g i‖` are uniformly
bounded. -/
theorem banach_steinhaus [CompleteSpace E] {ι : Type*} (g : ι → E →L[R] F)
    (h : ∀ x : E, ∃ C : ℝ, ∀ i : ι, ‖g i x‖ ≤ C) :
    ∃ C : ℝ, ∀ i : ι, ‖g i‖ ≤ C := by
  obtain ⟨ϖ⟩ := nonempty_pseudoUniformizer (R := R)
  have hclosed : ∀ n : ℕ, IsClosed {x : E | ∀ i : ι, ‖g i x‖ ≤ n} := fun n ↦ by
    simp only [ofPred_forall]
    exact isClosed_iInter fun i ↦ isClosed_le (g i).continuous.norm continuous_const
  have hcover : (⋃ n : ℕ, {x : E | ∀ i : ι, ‖g i x‖ ≤ n}) = univ := by
    refine eq_univ_of_forall fun x ↦ mem_iUnion.mpr ?_
    obtain ⟨C, hC⟩ := h x
    obtain ⟨n, hn⟩ := exists_nat_ge C
    exact ⟨n, fun i ↦ (hC i).trans hn⟩
  obtain ⟨n, x₀, hx₀⟩ := nonempty_interior_of_iUnion_of_closed hclosed hcover
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hx₀)
  obtain ⟨k, hk⟩ : ∃ k : ℕ, ‖(ϖ.unit : R)‖ ^ k < ε :=
    exists_pow_lt_of_lt_one hε ϖ.norm_lt_one
  refine ⟨2 * n * (‖(ϖ.unit : R)‖ ^ ((k : ℤ) + 1))⁻¹, fun i ↦ ?_⟩
  refine ϖ.ringOpNorm_le_of_forall_norm_lt (g i) k (by simpa using hk) (by positivity)
    fun x hx ↦ ?_
  have hmem : x + x₀ ∈ ball x₀ ε := by simpa [mem_ball, dist_eq_norm] using hx
  have hx1 : ‖g i (x + x₀)‖ ≤ n := hball hmem i
  have hx0 : ‖g i x₀‖ ≤ n := hball (mem_ball_self hε) i
  calc ‖g i x‖ = ‖g i (x + x₀) - g i x₀‖ := by rw [map_add, add_sub_cancel_right]
    _ ≤ ‖g i (x + x₀)‖ + ‖g i x₀‖ := norm_sub_le _ _
    _ ≤ n + n := add_le_add hx1 hx0
    _ = 2 * n := by ring

/-- Pointwise form of `TauCeti.NormedRing.IsTate.banach_steinhaus`: a pointwise bounded family of
continuous linear maps from a complete seminormed module over a Tate ring satisfies a uniform
linear bound `‖g i x‖ ≤ C * ‖x‖` with `C > 0`. -/
theorem banach_steinhaus_apply [CompleteSpace E] {ι : Type*} (g : ι → E →L[R] F)
    (h : ∀ x : E, ∃ C : ℝ, ∀ i : ι, ‖g i x‖ ≤ C) :
    ∃ C > 0, ∀ (i : ι) (x : E), ‖g i x‖ ≤ C * ‖x‖ := by
  obtain ⟨C, hC⟩ := banach_steinhaus g h
  refine ⟨max C 1, by positivity, fun i x ↦ ?_⟩
  exact (g i).le_of_ringOpNorm_le ((hC i).trans (le_max_left C 1)) x

end NormedRing.IsTate

end TauCeti

namespace LinearMap

variable {R E F : Type*} [SeminormedRing R] [TauCeti.NormedRing.IsTate R]
  [SeminormedAddCommGroup E] [Module R E] [IsBoundedSMul R E]
  [SeminormedAddCommGroup F] [Module R F] [IsBoundedSMul R F]

/-- If a family `g : α → E →L[R] F` of continuous linear maps on a complete seminormed module over
a Tate ring is pointwise bounded and converges pointwise along a nontrivial filter `l` to a linear
map `f`, then `f` is continuous. -/
theorem continuous_of_tendsto_of_pointwise_bounded [CompleteSpace E] {α : Type*} {l : Filter α}
    [l.NeBot] (f : E →ₗ[R] F) (g : α → E →L[R] F)
    (hf : ∀ x : E, Tendsto (fun a ↦ g a x) l (𝓝 (f x)))
    (hb : ∀ x : E, ∃ C : ℝ, ∀ a : α, ‖g a x‖ ≤ C) :
    Continuous f := by
  obtain ⟨C, -, hC⟩ := TauCeti.NormedRing.IsTate.banach_steinhaus_apply g hb
  refine AddMonoidHomClass.continuous_of_bound f C fun x ↦ ?_
  exact le_of_tendsto (hf x).norm (Eventually.of_forall fun a ↦ hC a x)

/-- If a family `g : α → E →L[R] F` of continuous linear maps on a complete seminormed module over
a Tate ring converges pointwise along a countably generated nontrivial filter `l` (for instance, a
sequence along `atTop`) to a linear map `f`, then `f` is continuous. -/
theorem continuous_of_tendsto_of_isTate [CompleteSpace E] {α : Type*} {l : Filter α}
    [l.IsCountablyGenerated] [l.NeBot] (f : E →ₗ[R] F) (g : α → E →L[R] F)
    (hf : ∀ x : E, Tendsto (fun a ↦ g a x) l (𝓝 (f x))) :
    Continuous f := by
  obtain ⟨u, hu⟩ := l.exists_seq_tendsto
  refine f.continuous_of_tendsto_of_pointwise_bounded (g ∘ u) (fun x ↦ (hf x).comp hu) fun x ↦ ?_
  obtain ⟨C, hC⟩ := ((hf x).comp hu).norm.bddAbove_range
  exact ⟨C, fun n ↦ hC ⟨n, rfl⟩⟩

end LinearMap

namespace ContinuousLinearMap

variable {R E F : Type*} [SeminormedRing R] [TauCeti.NormedRing.IsTate R]
  [SeminormedAddCommGroup E] [Module R E] [IsBoundedSMul R E]

section Seminormed

variable [SeminormedAddCommGroup F] [Module R F] [IsBoundedSMul R F]

/-- If a family `g : α → E →L[R] F` converges pointwise to `f : E →L[R] F` along a nontrivial
filter `l` and eventually satisfies `‖g a‖ ≤ C` with `0 ≤ C`, then `‖f‖ ≤ C`. -/
theorem ringOpNorm_le_of_tendsto {α : Type*} {l : Filter α} [l.NeBot]
    (f : E →L[R] F) (g : α → E →L[R] F) {C : ℝ} (hC : 0 ≤ C)
    (hf : ∀ x : E, Tendsto (fun a ↦ g a x) l (𝓝 (f x)))
    (hg : ∀ᶠ a in l, ‖g a‖ ≤ C) :
    ‖f‖ ≤ C :=
  f.ringOpNorm_le_bound hC fun x ↦
    le_of_tendsto (hf x).norm (hg.mono fun a ha ↦ (g a).le_of_ringOpNorm_le ha x)

end Seminormed

section Normed

variable [NormedAddCommGroup F] [Module R F] [IsBoundedSMul R F]

/-- Construct a bundled continuous linear map from the pointwise limit of a pointwise bounded
family of continuous linear maps on a complete seminormed module over a Tate ring. -/
def ofTendstoOfPointwiseBounded [CompleteSpace E] {α : Type*} {l : Filter α} [l.NeBot]
    (f : E → F) (g : α → E →L[R] F)
    (hf : Tendsto (fun a x ↦ g a x) l (𝓝 f))
    (hb : ∀ x : E, ∃ C : ℝ, ∀ a : α, ‖g a x‖ ≤ C) :
    E →L[R] F where
  toLinearMap := linearMapOfTendsto f (fun a ↦ (g a).toLinearMap) hf
  cont := LinearMap.continuous_of_tendsto_of_pointwise_bounded
    (linearMapOfTendsto f (fun a ↦ (g a).toLinearMap) hf) g (tendsto_pi_nhds.mp hf) hb

@[simp]
theorem coe_ofTendstoOfPointwiseBounded [CompleteSpace E] {α : Type*} {l : Filter α} [l.NeBot]
    (f : E → F) (g : α → E →L[R] F)
    (hf : Tendsto (fun a x ↦ g a x) l (𝓝 f))
    (hb : ∀ x : E, ∃ C : ℝ, ∀ a : α, ‖g a x‖ ≤ C) :
    ⇑(ofTendstoOfPointwiseBounded f g hf hb) = f :=
  (rfl)

@[simp]
theorem ofTendstoOfPointwiseBounded_apply [CompleteSpace E] {α : Type*} {l : Filter α} [l.NeBot]
    (f : E → F) (g : α → E →L[R] F)
    (hf : Tendsto (fun a x ↦ g a x) l (𝓝 f))
    (hb : ∀ x : E, ∃ C : ℝ, ∀ a : α, ‖g a x‖ ≤ C) (x : E) :
    ofTendstoOfPointwiseBounded f g hf hb x = f x :=
  (rfl)

@[simp]
theorem toLinearMap_ofTendstoOfPointwiseBounded [CompleteSpace E] {α : Type*} {l : Filter α}
    [l.NeBot] (f : E → F) (g : α → E →L[R] F)
    (hf : Tendsto (fun a x ↦ g a x) l (𝓝 f))
    (hb : ∀ x : E, ∃ C : ℝ, ∀ a : α, ‖g a x‖ ≤ C) :
    (ofTendstoOfPointwiseBounded f g hf hb).toLinearMap =
      linearMapOfTendsto f (fun a ↦ (g a).toLinearMap) hf :=
  (rfl)

/-- Construct a bundled continuous linear map from the pointwise limit along a countably generated
nontrivial filter (in particular, a pointwise convergent sequence) of continuous linear maps on a
complete seminormed module over a Tate ring. -/
def ofTendstoOfIsTate [CompleteSpace E] {α : Type*} {l : Filter α}
    [l.IsCountablyGenerated] [l.NeBot] (f : E → F) (g : α → E →L[R] F)
    (hf : Tendsto (fun a x ↦ g a x) l (𝓝 f)) :
    E →L[R] F where
  toLinearMap := linearMapOfTendsto f (fun a ↦ (g a).toLinearMap) hf
  cont := (linearMapOfTendsto f (fun a ↦ (g a).toLinearMap) hf).continuous_of_tendsto_of_isTate
    g (tendsto_pi_nhds.mp hf)

@[simp]
theorem coe_ofTendstoOfIsTate [CompleteSpace E] {α : Type*} {l : Filter α}
    [l.IsCountablyGenerated] [l.NeBot] (f : E → F) (g : α → E →L[R] F)
    (hf : Tendsto (fun a x ↦ g a x) l (𝓝 f)) :
    ⇑(ofTendstoOfIsTate f g hf) = f :=
  (rfl)

@[simp]
theorem ofTendstoOfIsTate_apply [CompleteSpace E] {α : Type*} {l : Filter α}
    [l.IsCountablyGenerated] [l.NeBot] (f : E → F) (g : α → E →L[R] F)
    (hf : Tendsto (fun a x ↦ g a x) l (𝓝 f)) (x : E) :
    ofTendstoOfIsTate f g hf x = f x :=
  (rfl)

@[simp]
theorem toLinearMap_ofTendstoOfIsTate [CompleteSpace E] {α : Type*} {l : Filter α}
    [l.IsCountablyGenerated] [l.NeBot] (f : E → F) (g : α → E →L[R] F)
    (hf : Tendsto (fun a x ↦ g a x) l (𝓝 f)) :
    (ofTendstoOfIsTate f g hf).toLinearMap =
      linearMapOfTendsto f (fun a ↦ (g a).toLinearMap) hf :=
  (rfl)

end Normed

end ContinuousLinearMap
