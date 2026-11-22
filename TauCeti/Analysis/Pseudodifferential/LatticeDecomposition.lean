/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Composition.Basic
public import TauCeti.Analysis.Pseudodifferential.SchwartzMapping
public import TauCeti.Analysis.Pseudodifferential.Symbol.Map
public import TauCeti.Analysis.Calculus.BumpFunction.LatticePartition
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import TauCeti.Analysis.Calculus.SmoothSeries
import TauCeti.Analysis.Normed.Lp.PiLp
import TauCeti.Analysis.SpecialFunctions.JapaneseBracket.Bounds
import TauCeti.Analysis.SpecialFunctions.JapaneseBracket.Peetre

/-!
# Lattice decompositions of uniform symbols

A symbol `a` of order `m` on `ℝⁿ` whose estimates hold uniformly in the position
(`TauCeti.Symbol.IsUniform`) need not vanish outside any compact set, so the constructions of the
calculus that use the Fourier transforms of the position slices of a symbol, such as the
composition symbol `TauCeti.Symbol.sharp` or the left symbol `TauCeti.Symbol.ofRight` of a right
quantization, do not apply to it directly. Cutting `a` by the integer translates of a bump
function gives pieces `aⱼ(x, ξ) = χ(x - j) a(x, ξ)`, `j ∈ ℤⁿ`, which vanish outside the balls of a
fixed radius about the lattice points and whose estimates do not depend on `j`
(`TauCeti.Symbol.isBallFamily_smulLeft_latticeBump`). This file develops the two ends of this
argument: such families of pieces, and sums of series of symbols.

* `TauCeti.Symbol.IsBallFamily`: families of symbols supported in balls of a fixed radius, with
  estimates independent of the member. They are stable under position and frequency derivatives
  and under multiplication by a coordinate of the displacement from the centre, and the Fourier
  transforms of their position slices decay faster than every power, uniformly in the family
  (`TauCeti.Symbol.IsBallFamily.exists_norm_fourier_le_rpow`).
* `TauCeti.Symbol.exists_isUniform_hasSum_coefficient`: a series of symbols whose derivatives are
  bounded by summable weights in the position sums to a symbol with uniform estimates, and
  `TauCeti.Symbol.hasSum_quantizeSchwartzValue_of_hasSum_coefficient`: its quantization is the sum
  of the quantizations.

For the pieces `aⱼ`, a construction applied to each piece typically decays away from the lattice
point `j` like `(1 + ‖x - j‖²) ^ (-n)`, whose sum over `j ∈ ℤⁿ` is bounded; the two ends then
assemble the pieces into a symbol with uniform estimates. This gives the composition of uniform
symbols (`TauCeti.Analysis.Pseudodifferential.Composition.Uniform`) and the left symbol of the
right quantization of a uniform symbol (`TauCeti.Analysis.Pseudodifferential.Adjoint.Uniform`).

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, §18.1.
-/

public section

noncomputable section

open MeasureTheory Real FourierTransform Metric
open scoped ContDiff RealInnerProductSpace SchwartzMap Topology

namespace TauCeti

namespace Symbol

variable {n : ℕ} {m : ℝ} {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [NormedAddCommGroup W] [NormedSpace ℂ W]

/-! ### Series of symbols -/

section Series

variable [CompleteSpace W] {ι : Type*} {μ : ℝ}

omit [CompleteSpace W] in
/-- If the mixed derivatives of symbols `aᵢ` are bounded by `C_{α,β} wᵢ(x) ⟨ξ⟩ ^ (μ - |β|)` with
weights `wᵢ` bounded on each unit ball by a summable family, then near each point the Fréchet
derivatives of every order of the `aᵢ` have summable bounds. -/
private theorem exists_locally_summable_iteratedFDeriv (a : ι → Symbol n V W μ)
    (w : ι → CoordinateSpace n → ℝ) (hw0 : ∀ i x, 0 ≤ w i x)
    (hloc : ∀ x, ∃ v : ι → ℝ, Summable v ∧ ∀ i, ∀ y ∈ ball x 1, w i y ≤ v i)
    {C : List (Fin n) → List (Fin n) → ℝ} (hC0 : ∀ α β, 0 ≤ C α β)
    (hC : ∀ α β i x ξ, ‖mixedDeriv α β (a i).coefficient x ξ‖ ≤
      C α β * w i x * (1 + ‖ξ‖ ^ 2) ^ ((μ - β.length) / 2))
    (q₀ : CoordinateSpace n × CoordinateSpace n) : ∃ r > 0, ∀ k : ℕ, (k : ℕ∞) ≤ ⊤ →
      ∃ u : ι → ℝ, Summable u ∧ ∀ i, ∀ q ∈ ball q₀ r,
        ‖iteratedFDeriv ℝ k (a i).coefficient q‖ ≤ u i := by
  obtain ⟨v, hv, hvw⟩ := hloc q₀.1
  let K : ℕ → ℝ := fun k ↦ ∑ r : Fin k → Fin n ⊕ Fin n,
    C ((List.ofFn r).filterMap Sum.getLeft?) ((List.ofFn r).filterMap Sum.getRight?) *
      (2 : ℝ) ^ |μ - ((List.ofFn r).filterMap Sum.getRight?).length| *
      (1 + ‖q₀.2‖ ^ 2) ^ ((μ - ((List.ofFn r).filterMap Sum.getRight?).length) / 2)
  refine ⟨1, one_pos, fun k _ ↦ ⟨fun i ↦ K k * v i, hv.mul_left (K k), fun i q hq ↦ ?_⟩⟩
  rw [mem_ball, Prod.dist_eq, max_lt_iff] at hq
  have hq₁ : q.1 ∈ ball q₀.1 1 := hq.1
  have hq₂ : ‖q.2 - q₀.2‖ ≤ 1 := by
    rw [← dist_eq_norm]
    exact hq.2.le
  refine ((norm_iteratedFDeriv_le_sum_mixedDeriv
    ((a i).contDiff_coefficient.of_le (by exact_mod_cast le_top)) q).trans ?_)
  simp only [K]
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun r _ ↦ ?_
  set α := (List.ofFn r).filterMap Sum.getLeft?
  set β := (List.ofFn r).filterMap Sum.getRight?
  refine (hC α β i q.1 q.2).trans ?_
  calc C α β * w i q.1 * (1 + ‖q.2‖ ^ 2) ^ ((μ - β.length) / 2)
      ≤ C α β * v i * (2 ^ |μ - β.length| * (1 + ‖q₀.2‖ ^ 2) ^ ((μ - β.length) / 2)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left (hvw i q.1 hq₁) (hC0 α β))
          (one_add_norm_sq_rpow_le_of_norm_sub_le_one hq₂ _) (by positivity)
          (mul_nonneg (hC0 α β) ((hw0 i q.1).trans (hvw i q.1 hq₁)))
    _ = _ := by ring

/-- The mixed derivatives of a series of symbols whose Fréchet derivatives have locally summable
bounds are the sums of the mixed derivatives. -/
private theorem mixedDeriv_tsum_coefficient (a : ι → Symbol n V W μ)
    (hloc : ∀ q₀ : CoordinateSpace n × CoordinateSpace n, ∃ r > 0, ∀ k : ℕ, (k : ℕ∞) ≤ ⊤ →
      ∃ u : ι → ℝ, Summable u ∧ ∀ i, ∀ q ∈ ball q₀ r,
        ‖iteratedFDeriv ℝ k (a i).coefficient q‖ ≤ u i)
    (α β : List (Fin n)) (x ξ : CoordinateSpace n) :
    mixedDeriv α β (fun q ↦ ∑' i, (a i).coefficient q) x ξ =
      ∑' i, mixedDeriv α β (a i).coefficient x ξ := by
  obtain ⟨r, hr, hu⟩ := hloc (x, ξ)
  obtain ⟨u, hus, hu⟩ := hu (mixedDirections α β).length le_top
  have hs : Summable fun i ↦ iteratedFDeriv ℝ (mixedDirections α β).length
      (a i).coefficient (x, ξ) :=
    .of_norm_bounded hus fun i ↦ hu i _ (mem_ball_self hr)
  rw [mixedDeriv_eq_iteratedFDeriv α β ((contDiff_tsum_of_locally_summable
      (fun i ↦ (a i).contDiff_coefficient) hloc).of_le (by exact_mod_cast le_top)),
    iteratedFDeriv_tsum_of_locally_summable (fun i ↦ (a i).contDiff_coefficient) hloc le_top,
    ← ContinuousMultilinearMap.apply_apply (𝕜 := ℝ), (ContinuousMultilinearMap.apply ℝ _ _
      _).map_tsum hs]
  refine tsum_congr fun i ↦ ?_
  rw [ContinuousMultilinearMap.apply_apply, mixedDeriv_eq_iteratedFDeriv α β
    ((a i).contDiff_coefficient.of_le (by exact_mod_cast le_top))]

/-- **A series of symbols with summable weights is a uniform symbol.** Let `a i` be symbols of
order `μ` whose mixed derivatives are bounded by `C_{α,β} wᵢ(x) ⟨ξ⟩ ^ (μ - |β|)`, where the
weights `wᵢ` are bounded on each unit ball by a summable family and have sums bounded by `S` at
every position. Then `∑ᵢ aᵢ` converges at every point to the coefficient of a symbol of order `μ`
with estimates uniform in the position. -/
theorem exists_isUniform_hasSum_coefficient (a : ι → Symbol n V W μ)
    (w : ι → CoordinateSpace n → ℝ) (hw0 : ∀ i x, 0 ≤ w i x)
    (hloc : ∀ x, ∃ v : ι → ℝ, Summable v ∧ ∀ i, ∀ y ∈ ball x 1, w i y ≤ v i) {S : ℝ}
    (hS : ∀ x, ∑' i, w i x ≤ S)
    (hbound : ∀ α β : List (Fin n), ∃ C, 0 ≤ C ∧ ∀ i x ξ, ‖mixedDeriv α β (a i).coefficient x ξ‖ ≤
      C * w i x * (1 + ‖ξ‖ ^ 2) ^ ((μ - β.length) / 2)) :
    ∃ b : Symbol n V W μ, b.IsUniform ∧ ∀ q, HasSum (fun i ↦ (a i).coefficient q) (b.coefficient q)
    := by
  choose C hC0 hC using hbound
  have hloc' := exists_locally_summable_iteratedFDeriv a w hw0 hloc hC0 hC
  have hw : ∀ x, Summable fun i ↦ w i x := fun x ↦ by
    obtain ⟨v, hv, hvw⟩ := hloc x
    exact Summable.of_nonneg_of_le (fun i ↦ hw0 i x) (fun i ↦ hvw i x (mem_ball_self one_pos)) hv
  -- The series of mixed derivatives converges absolutely, with the sum of the bounds.
  have hsum : ∀ α β x ξ, Summable fun i ↦ ‖mixedDeriv α β (a i).coefficient x ξ‖ :=
    fun α β x ξ ↦ Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (hC α β · x ξ)
      (((hw x).mul_left (C α β)).mul_right _)
  have hS0 : 0 ≤ S := (tsum_nonneg fun i ↦ hw0 i 0).trans (hS 0)
  have hb : ∀ α β x ξ, ‖mixedDeriv α β (fun q ↦ ∑' i, (a i).coefficient q) x ξ‖ ≤
      C α β * S * (1 + ‖ξ‖ ^ 2) ^ ((μ - β.length) / 2) := by
    intro α β x ξ
    rw [mixedDeriv_tsum_coefficient a hloc']
    refine (norm_tsum_le_tsum_norm (hsum α β x ξ)).trans ?_
    refine ((hsum α β x ξ).tsum_le_tsum (hC α β · x ξ)
      (((hw x).mul_left (C α β)).mul_right _)).trans ?_
    rw [tsum_mul_right, tsum_mul_left]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hS x) (hC0 α β))
      (by positivity)
  refine ⟨⟨fun q ↦ ∑' i, (a i).coefficient q, contDiff_tsum_of_locally_summable
    (fun i ↦ (a i).contDiff_coefficient) hloc', fun K _ α β ↦
    ⟨C α β * S, mul_nonneg (hC0 α β) hS0, fun x _ ξ ↦ hb α β x ξ⟩⟩,
    isUniform_iff.2 fun α β ↦ ⟨C α β * S, mul_nonneg (hC0 α β) hS0, fun x ξ ↦ hb α β x ξ⟩,
    fun q ↦ ?_⟩
  refine (Summable.of_norm ?_).hasSum
  simpa using hsum [] [] q.1 q.2

omit [CompleteSpace W] in
/-- **Quantizing a series of symbols.** If symbols `Fᵢ` sum to `b` pointwise, with
`‖Fᵢ(x, ξ)‖ ≤ C wᵢ ⟨ξ⟩ ^ μ` at a position `x` for summable `wᵢ`, then
`Op(b) u (x) = ∑ᵢ Op(Fᵢ) u (x)`, by dominated convergence in the frequency. -/
theorem hasSum_quantizeSchwartzValue_of_hasSum_coefficient [Countable ι] {μ' : ℝ}
    {F : ι → Symbol n V W μ} {b : Symbol n V W μ'}
    (hFb : ∀ q, HasSum (fun i ↦ (F i).coefficient q) (b.coefficient q)) {w : ι → ℝ}
    (hw : Summable w) {C : ℝ} {x : CoordinateSpace n}
    (hC : ∀ i ξ, ‖(F i).coefficient (x, ξ)‖ ≤ C * w i * (1 + ‖ξ‖ ^ 2) ^ (μ / 2))
    (u : 𝓢(CoordinateSpace n, V)) :
    HasSum (fun i ↦ quantizeSchwartzValue (F i).coefficient u x)
      (quantizeSchwartzValue b.coefficient u x) := by
  simp only [quantizeSchwartzValue_def]
  refine hasSum_integral_of_dominated_convergence
    (fun i ζ ↦ C * w i * ((1 + ‖(2 * π) • ζ‖ ^ 2) ^ (μ / 2) * ‖𝓕 u ζ‖))
    (fun i ↦ ?_) (fun i ↦ .of_forall fun ζ ↦ ?_) (.of_forall fun ζ ↦ (hw.mul_left C).mul_right _)
    ?_ (.of_forall fun ζ ↦ ((hFb (x, (2 * π) • ζ)).mapL
      (ContinuousLinearMap.apply ℂ W (𝓕 u ζ))).const_smul (𝐞 ⟪ζ, x⟫))
  · obtain ⟨C', -, hC'⟩ := (F i).exists_bound_coefficient_slice x
    exact (integrable_quantizeSchwartzValue_integrand
      ((F i).continuous_coefficient_slice x).aestronglyMeasurable hC' (𝓕 u)).aestronglyMeasurable
  · rw [Circle.smul_def, norm_smul, Circle.norm_coe, one_mul]
    refine ((F i).coefficient (x, (2 * π) • ζ)).le_opNorm _ |>.trans ?_
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right (hC i _) (norm_nonneg _)
  · have e : (fun ζ ↦ ∑' i, C * w i * ((1 + ‖(2 * π) • ζ‖ ^ 2) ^ (μ / 2) * ‖𝓕 u ζ‖)) =
        fun ζ ↦ (C * ∑' i, w i) * ((1 + ‖(2 * π) • ζ‖ ^ 2) ^ (μ / 2) * ‖𝓕 u ζ‖) :=
      funext fun ζ ↦ by rw [tsum_mul_right, tsum_mul_left]
    rw [e]
    exact ((𝓕 u).integrable_one_add_norm_smul_sq_rpow_mul_norm (2 * π) μ).const_mul _

end Series

/-! ### Families of symbols supported in balls of a fixed radius -/

section BallFamily

variable {ι : Type*}

/-- A family of symbols `c i` of order `m`, each vanishing at the positions outside the closed
ball of radius `r` about `z i`, whose symbol estimates hold with constants independent of the
position and of `i`. Cutting a uniform symbol by the lattice translates of a bump function gives
such a family (`TauCeti.Symbol.isBallFamily_smulLeft_latticeBump`). -/
structure IsBallFamily (z : ι → CoordinateSpace n) (r : ℝ) (c : ι → Symbol n V W m) :
    Prop where
  /-- Each member vanishes at the positions at distance more than `r` from its centre. -/
  coefficient_eq_zero : ∀ i x ξ, r < dist x (z i) → (c i).coefficient (x, ξ) = 0
  /-- The symbol estimates hold with constants independent of the position and of the member. -/
  exists_norm_mixedDeriv_le : ∀ α β : List (Fin n), ∃ C, ∀ i x ξ,
    ‖mixedDeriv α β (c i).coefficient x ξ‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ ((m - β.length) / 2)

variable {z : ι → CoordinateSpace n} {r : ℝ} {c : ι → Symbol n V W m}

/-- A member of a ball family vanishes near every position at distance more than `r` from its
centre. -/
theorem IsBallFamily.eventually_eq_zero (hc : IsBallFamily z r c) (i : ι)
    {x : CoordinateSpace n} (hx : r < dist x (z i)) :
    ∀ᶠ y in nhds x, ∀ ξ, (c i).coefficient (y, ξ) = 0 :=
  Filter.eventually_of_mem ((isOpen_lt continuous_const (continuous_id.dist
    continuous_const)).mem_nhds hx) fun _ hy ξ ↦ hc.coefficient_eq_zero i _ ξ hy

/-- Each member of a ball family has compact spatial support. -/
theorem IsBallFamily.hasCompactSpatialSupport (hc : IsBallFamily z r c) (i : ι) :
    (c i).HasCompactSpatialSupport :=
  hasCompactSpatialSupport_iff.2 ⟨closedBall (z i) r, isCompact_closedBall _ _, fun x hx ξ ↦
    hc.coefficient_eq_zero i x ξ (not_le.1 fun h ↦ hx (mem_closedBall.2 h))⟩

/-- The position derivatives of the members of a ball family form a ball family. -/
theorem IsBallFamily.map_spatialDeriv (hc : IsBallFamily z r c) (j : Fin n) :
    IsBallFamily z r fun i ↦ spatialDeriv j (c i) := by
  refine ⟨fun i x ξ hx ↦ ?_, fun α β ↦ ?_⟩
  · have h : (fun y ↦ (c i).coefficient (y, ξ)) =ᶠ[nhds x] fun _ ↦ 0 :=
      (hc.eventually_eq_zero i hx).mono fun y hy ↦ hy ξ
    rw [coefficient_spatialDeriv, (h.coordinateDeriv [j]).eq_of_nhds,
      coordinateDeriv_const _ (List.cons_ne_nil j [])]
    rfl
  · obtain ⟨C, hC⟩ := hc.exists_norm_mixedDeriv_le (α ++ [j]) β
    exact ⟨C, fun i x ξ ↦ by simpa using hC i x ξ⟩

/-- The frequency derivatives of the members of a ball family form a ball family, of order one
less. -/
theorem IsBallFamily.map_frequencyDeriv (hc : IsBallFamily z r c) (j : Fin n) :
    IsBallFamily z r fun i ↦ frequencyDeriv j (c i) := by
  refine ⟨fun i x ξ hx ↦ ?_, fun α β ↦ ?_⟩
  · have h : (fun η ↦ (c i).coefficient (x, η)) = fun _ ↦ 0 :=
      funext (hc.coefficient_eq_zero i x · hx)
    rw [coefficient_frequencyDeriv, h, coordinateDeriv_const _ (List.cons_ne_nil j [])]
    rfl
  · obtain ⟨C, hC⟩ := hc.exists_norm_mixedDeriv_le α (β ++ [j])
    refine ⟨C, fun i x ξ ↦ ?_⟩
    rw [mixedDeriv_frequencyDeriv, order_sub_one_sub_length]
    exact hC i x ξ

private theorem hasFDerivAt_coordSub (z : CoordinateSpace n) (j : Fin n) (y : CoordinateSpace n) :
    HasFDerivAt (fun y' : CoordinateSpace n ↦ (y' - z) j • ContinuousLinearMap.id ℂ W)
      ((EuclideanSpace.proj j : CoordinateSpace n →L[ℝ] ℝ).smulRight
        (ContinuousLinearMap.id ℂ W)) y := by
  have h := ((EuclideanSpace.proj j : CoordinateSpace n →L[ℝ] ℝ).hasFDerivAt (x := y)).sub_const
    (z j)
  convert h.smul_const (ContinuousLinearMap.id ℂ W) using 1
  funext y'
  simp [sub_smul]

/-- The coordinate derivatives of `y ↦ (y - z)ⱼ id` are bounded by `max r 1` on the closed ball
of radius `r` about `z`. -/
private theorem norm_coordinateDeriv_coordSub_le {z x : CoordinateSpace n} {r : ℝ}
    (hx : dist x z ≤ r) (j : Fin n) (s : List (Fin n)) :
    ‖coordinateDeriv s (fun y : CoordinateSpace n ↦ (y - z) j • ContinuousLinearMap.id ℂ W) x‖ ≤
      max r 1 := by
  have hid : ‖ContinuousLinearMap.id ℂ W‖ ≤ 1 := ContinuousLinearMap.norm_id_le
  have h1 (l : Fin n) : coordinateDeriv [l]
      (fun y : CoordinateSpace n ↦ (y - z) j • ContinuousLinearMap.id ℂ W) =
      fun _ ↦ (EuclideanSpace.single l (1 : ℝ)) j • ContinuousLinearMap.id ℂ W := by
    funext y
    rw [coordinateDeriv_cons, coordinateDeriv_nil, (hasFDerivAt_coordSub z j y).fderiv]
    simp
  rcases List.eq_nil_or_concat' s with rfl | ⟨s, l, rfl⟩
  · refine le_max_of_le_left ?_
    rw [coordinateDeriv_nil, norm_smul]
    calc ‖(x - z) j‖ * ‖ContinuousLinearMap.id ℂ W‖ ≤ ‖x - z‖ * 1 :=
          mul_le_mul (PiLp.norm_apply_le (x - z) j) hid (norm_nonneg _) (norm_nonneg _)
      _ ≤ r := by rw [mul_one, ← dist_eq_norm]; exact hx
  · rw [coordinateDeriv_append, h1]
    rcases eq_or_ne s [] with rfl | hs
    · refine le_max_of_le_right ?_
      rw [coordinateDeriv_nil, norm_smul]
      calc ‖(EuclideanSpace.single l (1 : ℝ)) j‖ * ‖ContinuousLinearMap.id ℂ W‖ ≤ 1 * 1 :=
            mul_le_mul ((PiLp.norm_apply_le _ j).trans (by simp)) hid (norm_nonneg _)
              zero_le_one
        _ = 1 := one_mul 1
    · rw [coordinateDeriv_const _ hs, Pi.zero_apply, norm_zero]
      exact zero_le_one.trans (le_max_right _ _)

/-- Multiplying a symbol `a` by a symbol `b(x, ξ) = f(x)` of the position whose coordinate
derivatives at `x` are bounded by `B s` keeps the symbol estimates of `a` at `(x, ξ)`. -/
private theorem norm_mixedDeriv_comp_le_of_coefficient_eq {b : Symbol n W W 0}
    {f : CoordinateSpace n → W →L[ℂ] W} (hbf : ∀ p, b.coefficient p = f p.1) (a : Symbol n V W m)
    {x ξ : CoordinateSpace n} {B : List (Fin n) → ℝ} (hB0 : ∀ s, 0 ≤ B s)
    (hB : ∀ s, ‖coordinateDeriv s f x‖ ≤ B s) {D : List (Fin n) → List (Fin n) → ℝ}
    (hD : ∀ s t, ‖mixedDeriv s t a.coefficient x ξ‖ ≤ D s t * (1 + ‖ξ‖ ^ 2) ^ ((m - t.length) / 2))
    (α β : List (Fin n)) :
    ‖mixedDeriv α β (b.comp a).coefficient x ξ‖ ≤
      max ((β.sublists'.revzip.map fun t =>
        (α.sublists'.revzip.map fun s => B s.1 * D s.2 t.2).sum).sum) 0 *
        (1 + ‖ξ‖ ^ 2) ^ ((0 + m - β.length) / 2) := by
  have hC (s t : List (Fin n)) : ‖mixedDeriv s t b.coefficient x ξ‖ ≤
      B s * (1 + ‖ξ‖ ^ 2) ^ (((0 : ℝ) - t.length) / 2) := by
    rcases eq_or_ne t [] with rfl | ht
    · rw [funext hbf, mixedDeriv_nil_comp_fst f]
      simpa using hB s
    · rw [funext hbf, mixedDeriv_comp_fst f s ht, norm_zero]
      exact mul_nonneg (hB0 s) (by positivity)
  rw [funext (coefficient_comp b a)]
  refine (norm_mixedDeriv_comp_le (m' := 0) (C := fun s _ ↦ B s) b.contDiff_coefficient
    a.contDiff_coefficient hC hD α β).trans ?_
  gcongr
  exact le_max_left _ _

/-- Multiplying the members of a ball family by the `j`-th coordinate of the displacement from
their centres gives a ball family. -/
theorem IsBallFamily.comp_coordSubSymbol (hc : IsBallFamily z r c) (j : Fin n) :
    IsBallFamily z r fun i ↦ (coordSubSymbol (z i) j).comp (c i) := by
  refine ⟨fun i x ξ hx ↦ by simp [coefficient_comp, hc.coefficient_eq_zero i x ξ hx], fun α β ↦ ?_⟩
  choose D hD using hc.exists_norm_mixedDeriv_le
  set K := (β.sublists'.revzip.map fun t =>
    (α.sublists'.revzip.map fun s => max r 1 * D s.2 t.2).sum).sum
  refine ⟨max K 0, fun i x ξ ↦ ?_⟩
  rcases le_or_gt (dist x (z i)) r with hx | hx
  · exact norm_mixedDeriv_comp_le_of_coefficient_eq (b := coordSubSymbol (z i) j)
      (f := fun y ↦ (y - z i) j • ContinuousLinearMap.id ℂ W) (coefficient_coordSubSymbol (z i) j)
      (c i) (fun _ ↦ zero_le_one.trans (le_max_right _ _)) (norm_coordinateDeriv_coordSub_le hx j)
      (fun s t ↦ hD s t i x ξ) α β
  · rw [funext (coefficient_comp (coordSubSymbol (z i) j) (c i)), mixedDeriv_eq_zero_of_eventually
      (by filter_upwards [hc.eventually_eq_zero i hx] with y hy ξ'; simp [hy ξ']) α β ξ, norm_zero]
    positivity

/-- Cutting a uniform symbol off by smooth functions `φᵢ`, vanishing outside the closed balls of
radius `r` about the points `zᵢ` and with derivatives bounded independently of `i`, gives a ball
family. -/
theorem isBallFamily_smulLeft (z : ι → CoordinateSpace n) (r : ℝ)
    (φ : ι → CoordinateSpace n → ℝ) (hφ : ∀ i, ContDiff ℝ ∞ (φ i))
    (hφB : ∀ k : ℕ, ∃ B, ∀ i x, ‖iteratedFDeriv ℝ k (φ i) x‖ ≤ B)
    (hφz : ∀ i x, r < dist x (z i) → φ i x = 0) {a : Symbol n V W m} (ha : a.IsUniform) :
    IsBallFamily z r fun i ↦ smulLeft (Complex.ofRealCLM.contDiff.comp (hφ i)) a := by
  refine ⟨fun i x ξ hx ↦ by simp [hφz i x hx], fun α β ↦ ?_⟩
  choose B hB using hφB
  choose D _ hD using isUniform_iff.1 ha
  -- The real scalars acting on `W →L[ℂ] W` by multiples of the identity.
  set L : ℝ →L[ℝ] W →L[ℂ] W :=
    (ContinuousLinearMap.id ℝ ℝ).smulRight (ContinuousLinearMap.id ℂ W)
  have hL : ‖L‖ ≤ 1 := L.opNorm_le_bound zero_le_one fun t ↦ by
    simpa [L, norm_smul] using mul_le_mul_of_nonneg_left
      (ContinuousLinearMap.norm_id_le (𝕜 := ℂ) (E := W)) (norm_nonneg t)
  set K := (β.sublists'.revzip.map fun t =>
    (α.sublists'.revzip.map fun s => max (B s.1.length) 0 * D s.2 t.2).sum).sum
  refine ⟨max K 0, fun i x ξ ↦ ?_⟩
  have hLφ : ContDiff ℝ ∞ (L ∘ φ i) := L.contDiff.comp (hφ i)
  have hf (s : List (Fin n)) : ‖coordinateDeriv s (fun y ↦ L (φ i y)) x‖ ≤ max (B s.length) 0 :=
    calc ‖coordinateDeriv s (fun y ↦ L (φ i y)) x‖
        ≤ ‖iteratedFDeriv ℝ s.length (L ∘ φ i) x‖ :=
          norm_coordinateDeriv_le s (hLφ.of_le (by exact_mod_cast le_top)) x
      _ ≤ ‖L‖ * ‖iteratedFDeriv ℝ s.length (φ i) x‖ :=
          L.norm_iteratedFDeriv_comp_left (hφ i).contDiffAt (by exact_mod_cast le_top)
      _ ≤ 1 * max (B s.length) 0 := mul_le_mul hL ((hB _ i x).trans (le_max_left _ _))
          (norm_nonneg _) zero_le_one
      _ = _ := one_mul _
  -- `φᵢ a` has the coefficient of the composition of `a` with the cutoff symbol of `φᵢ`.
  have hc : (smulLeft (Complex.ofRealCLM.contDiff.comp (hφ i)) a).coefficient =
      ((cutoff W (hφ i)).comp a).coefficient := funext fun p ↦ by
    simp [ContinuousLinearMap.smul_comp]
  simpa only [hc, zero_add] using norm_mixedDeriv_comp_le_of_coefficient_eq
    (f := fun y ↦ L (φ i y)) (B := fun s ↦ max (B s.length) 0) (fun p ↦ by simp [L]) a
    (fun _ ↦ le_max_right _ _) hf (fun s t ↦ hD s t x ξ) α β

end BallFamily

/-! ### Uniform decay of the Fourier transforms of the slices -/

section Decay

variable {ι : Type*} {z : ι → CoordinateSpace n} {r : ℝ}

/-- The Fourier transforms of the position slices of a ball family are bounded by `D ⟨ξ⟩ ^ m`,
uniformly in the family: they are bounded by the `L¹` norms of the slices. -/
private theorem IsBallFamily.exists_norm_fourier_le {c : ι → Symbol n V W m}
    (hc : IsBallFamily z r c) :
    ∃ D, ∀ i η ξ, ‖𝓕 (fun y ↦ (c i).coefficient (y, ξ)) η‖ ≤ D * (1 + ‖ξ‖ ^ 2) ^ (m / 2) := by
  obtain ⟨C, hC⟩ := hc.exists_norm_mixedDeriv_le [] []
  set v := (volume : Measure (CoordinateSpace n)).real (closedBall 0 r)
  refine ⟨v * C, fun i η ξ ↦ ?_⟩
  set w := (1 + ‖ξ‖ ^ 2) ^ (m / 2)
  have hle (y : CoordinateSpace n) : ‖(c i).coefficient (y, ξ)‖ ≤
      (closedBall (z i) r).indicator (fun _ ↦ C * w) y := by
    by_cases hy : y ∈ closedBall (z i) r
    · rw [Set.indicator_of_mem hy]
      simpa [w] using hC i y ξ
    · rw [Set.indicator_of_notMem hy,
        hc.coefficient_eq_zero i y ξ (not_le.1 fun h ↦ hy (mem_closedBall.2 h)),
        norm_zero]
  have hint : Integrable ((closedBall (z i) r).indicator fun _ ↦ C * w) :=
    (integrableOn_const (measure_closedBall_lt_top (x := z i) (r := r)).ne).integrable_indicator
      measurableSet_closedBall
  refine (Real.norm_fourier_le_integral_norm _ η).trans ?_
  refine (integral_mono_of_nonneg (.of_forall fun _ ↦ norm_nonneg _) hint
    (.of_forall hle)).trans_eq ?_
  rw [integral_indicator_const _ measurableSet_closedBall,
    Measure.addHaar_real_closedBall_center, smul_eq_mul]
  ring

/-- Even powers of the frequency times the Fourier transforms of the position slices of a ball
family are bounded by `D ⟨ξ⟩ ^ m`, uniformly in the family. -/
private theorem IsBallFamily.exists_norm_pow_mul_norm_fourier_le (N : ℕ) :
    ∀ {m : ℝ} {c : ι → Symbol n V W m}, IsBallFamily z r c →
      ∃ D, ∀ i η ξ, ‖η‖ ^ (2 * N) * ‖𝓕 (fun y ↦ (c i).coefficient (y, ξ)) η‖ ≤
        D * (1 + ‖ξ‖ ^ 2) ^ (m / 2) := by
  induction N with
  | zero =>
    intro m c hc
    simpa using hc.exists_norm_fourier_le
  | succ N ih =>
    intro m c hc
    choose D hD using fun j : Fin n ↦ ih ((hc.map_spatialDeriv j).map_spatialDeriv j)
    refine ⟨((2 * π) ^ 2)⁻¹ * ∑ j, D j, fun i η ξ ↦ ?_⟩
    -- `𝓕 (∂ⱼ² c) = (2πi ηⱼ)² 𝓕 c`, so `ηⱼ² ‖𝓕 c‖ = (2π)⁻² ‖𝓕 (∂ⱼ² c)‖`.
    have hj (j : Fin n) : η j ^ 2 * ‖𝓕 (fun y ↦ (c i).coefficient (y, ξ)) η‖ =
        ((2 * π) ^ 2)⁻¹ *
          ‖𝓕 (fun y ↦
            (Symbol.spatialDeriv j (Symbol.spatialDeriv j (c i))).coefficient (y, ξ)) η‖ := by
      rw [((hc.hasCompactSpatialSupport i).spatialDeriv j).fourier_spatialDeriv_slice,
        (hc.hasCompactSpatialSupport i).fourier_spatialDeriv_slice, smul_smul, norm_smul,
        EuclideanSpace.inner_single_right]
      simp only [one_mul, conj_trivial, norm_mul, Complex.norm_real, Complex.norm_I,
        Complex.norm_ofNat, Real.norm_eq_abs, mul_one]
      rw [abs_of_pos pi_pos]
      field_simp
      rw [sq_abs]
      ring
    calc ‖η‖ ^ (2 * (N + 1)) * ‖𝓕 (fun y ↦ (c i).coefficient (y, ξ)) η‖
        = ‖η‖ ^ 2 * (‖η‖ ^ (2 * N) * ‖𝓕 (fun y ↦ (c i).coefficient (y, ξ)) η‖) := by ring
      _ ≤ ∑ j, ((2 * π) ^ 2)⁻¹ * (D j * (1 + ‖ξ‖ ^ 2) ^ (m / 2)) :=
          PiLp.norm_sq_mul_le_sum fun j ↦ by
            rw [Real.norm_eq_abs, sq_abs]
            refine (mul_left_comm _ _ _).trans_le ?_
            rw [hj, mul_left_comm]
            exact mul_le_mul_of_nonneg_left (hD j i η ξ) (by positivity)
      _ = _ := by rw [← Finset.mul_sum, ← Finset.sum_mul, mul_assoc]

/-- **Rapid decay of the Fourier transforms of the slices, uniformly in the family.** For every
`s`, the Fourier transforms of the position slices of a ball family satisfy
`‖𝓕 cᵢ(η, ξ)‖ ≤ D ⟨ξ⟩ ^ m ⟨η⟩ ^ (-s)` with `D` independent of `i`. -/
theorem IsBallFamily.exists_norm_fourier_le_rpow {c : ι → Symbol n V W m}
    (hc : IsBallFamily z r c) (s : ℝ) :
    ∃ D, ∀ i η ξ, ‖𝓕 (fun y ↦ (c i).coefficient (y, ξ)) η‖ ≤
      D * (1 + ‖ξ‖ ^ 2) ^ (m / 2) * (1 + ‖η‖ ^ 2) ^ (-s / 2) := by
  set N := ⌈s / 2⌉₊
  obtain ⟨D₀, hD₀⟩ := hc.exists_norm_fourier_le
  obtain ⟨D, hD⟩ := IsBallFamily.exists_norm_pow_mul_norm_fourier_le N hc
  refine ⟨2 ^ (N - 1) * (D₀ + D), fun i η ξ ↦ ?_⟩
  set F := ‖𝓕 (fun y ↦ (c i).coefficient (y, ξ)) η‖
  set w := (1 + ‖ξ‖ ^ 2) ^ (m / 2)
  have hη : 1 ≤ 1 + ‖η‖ ^ 2 := le_add_of_nonneg_right (by positivity)
  have hF := Real.le_mul_one_add_sq_pow_inv (norm_nonneg _) (hD₀ i η ξ) (hD i η ξ)
  have hinv : 0 < ((1 + ‖η‖ ^ 2) ^ N)⁻¹ := by positivity
  -- `((1 + ‖η‖²) ^ N)⁻¹ = (1 + ‖η‖²) ^ (-N) ≤ (1 + ‖η‖²) ^ (-s / 2)` since `N ≥ s / 2`.
  have hN : ((1 + ‖η‖ ^ 2) ^ N)⁻¹ ≤ (1 + ‖η‖ ^ 2) ^ (-s / 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_neg (by positivity)]
    exact Real.rpow_le_rpow_of_exponent_le hη (by linarith [Nat.le_ceil (s / 2)])
  exact hF.trans (mul_le_mul_of_nonneg_left hN
    ((mul_nonneg_iff_of_pos_right hinv).1 ((norm_nonneg _).trans hF)))

end Decay

/-! ### The lattice decomposition of a uniform symbol -/

/-- The cut-off pieces `χ(x - j) a(x, ξ)` of a uniform symbol `a` form a ball family centred at
the lattice points, with radius `√n`. -/
theorem isBallFamily_smulLeft_latticeBump {a : Symbol n V W m} (ha : a.IsUniform) :
    IsBallFamily (fun j : Fin n → ℤ ↦ latticePoint j) √n fun j ↦
      smulLeft (Complex.ofRealCLM.contDiff.comp (contDiff_latticeBump_sub j)) a :=
  isBallFamily_smulLeft _ _ (fun j y ↦ latticeBump n (y - latticePoint j))
    contDiff_latticeBump_sub exists_norm_iteratedFDeriv_latticeBump_sub_le
    (fun _ _ hx ↦ by_contra fun h ↦ (mem_closedBall.1
      (mem_closedBall_of_latticeBump_sub_ne_zero h)).not_gt hx) ha

end Symbol

end TauCeti
