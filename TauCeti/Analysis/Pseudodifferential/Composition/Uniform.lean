/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Composition.Expansion
public import TauCeti.Analysis.Pseudodifferential.SchwartzMapping
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import TauCeti.Analysis.Calculus.BumpFunction.LatticePartition
import TauCeti.Analysis.Calculus.SmoothSeries
import TauCeti.Analysis.Distribution.SchwartzSpace.Cutoff
import TauCeti.Analysis.Pseudodifferential.OutputSupport.Basic
import TauCeti.Analysis.SpecialFunctions.JapaneseBracket.Basic
import TauCeti.Analysis.SpecialFunctions.JapaneseBracket.Peetre

/-!
# Composition of symbols with uniform estimates

Let `p` and `a` be symbols of orders `m'` and `m` on `ℝⁿ` whose estimates
`‖∂_x^α ∂_ξ^β a(x, ξ)‖ ≤ C_{α,β} ⟨ξ⟩^(m - |β|)` hold uniformly in the position
(`TauCeti.Symbol.IsUniform`). Their quantizations act on Schwartz space
(`TauCeti.Symbol.quantizeUniformCLM`), and this file shows that `Op(p) ∘ Op(a)` is again the
quantization of a symbol of order `m' + m` with estimates uniform in the position
(`TauCeti.Symbol.IsUniform.exists_quantizeUniformCLM_comp`). The composition symbol `p # a` of
`TauCeti.Symbol.sharp` is only defined when `a` has compact spatial support, since it is built
from the Fourier transforms of the position slices of `a`; a uniform symbol such as `a = 1` has
no such Fourier transforms. With this theorem the uniform symbols form an algebra under
composition; for instance `J^t ∘ Op(a)` is the quantization of a uniform symbol for every Bessel
multiplier `J^t`, which gives the Sobolev mapping of uniform symbols at every order
(`TauCeti.Symbol.hasSobolevExtension_quantizeUniformCLM`).

## The construction

Cut `a` into the pieces `aⱼ(x, ξ) = χ(x - j) a(x, ξ)`, `j ∈ ℤⁿ`, by the integer translates of
the bump `χ = TauCeti.latticeBump n`, a smooth partition of unity. The pieces have compact
spatial support in balls of radius `√n` about the lattice points, with symbol estimates
independent of `j`, so `p # aⱼ` is defined. Its estimates are uniform in `j`, because the Fourier
transforms of the slices of `aⱼ` are bounded by the `L¹` norms of the slices and their
derivatives, which do not depend on where the piece sits. Away from `j`, `p # aⱼ` decays faster
than every power of the distance: the commutator identity

`(x - z)ⱼ (p # b) = p # ((y - z)ⱼ b) + i (∂_{ξⱼ} p) # b`,

which comes from the commutator of `Op(p)` with a coordinate function
(`TauCeti.Symbol.coordSub_smul_coefficient_sharp`), trades a factor `(x - j)ₖ`
for a frequency derivative of `p` or a factor bounded on the support of `aⱼ`. So every mixed
derivative of `p # aⱼ` is bounded by `C ⟨x - j⟩^(-2n) ⟨ξ⟩^(m' + m - |β|)`, and these bounds are
summable over the lattice uniformly in `x`. The series `c = ∑ⱼ p # aⱼ` therefore converges, with
all its derivatives, to a symbol of order `m' + m` with uniform estimates; the derivatives of the
sum are the sums of the derivatives because the bounds are summable near each point
(`TauCeti.iteratedFDeriv_tsum_of_locally_summable`).

Finally `Op(c) = Op(p) ∘ Op(a)`. On a Schwartz function `u`, `Op(p # aⱼ) u = Op(p) (χ(· - j) w)`
with `w = Op(a) u`, and the series `∑ⱼ χ(· - j) w` converges to `w` in Schwartz space
(`SchwartzMap.hasSum_smulLeftCLM_latticeBump_sub`), on which `Op(p)` is continuous. On the other
side `∑ⱼ Op(p # aⱼ) u (x) = Op(c) u (x)` by dominated convergence in the frequency.

## Main results

* `TauCeti.Symbol.IsUniform.exists_quantizeUniformCLM_comp`: **composition of uniform symbols**.
  The composition of the quantizations of two uniform symbols of orders `m'` and `m` is the
  quantization of a uniform symbol of order `m' + m`. The symbol is unique
  (`TauCeti.Symbol.quantizeSchwartzValue_injective`); when `a` has compact spatial support it is
  `p # a` (`TauCeti.Symbol.coefficient_eq_sharp_of_forall_quantizeSchwartzValue_eq`).
* `TauCeti.Symbol.IsUniform.isUniformAsymptoticSum_sharpTerm_of_comp_eq`: **the asymptotic
  expansion of the composition**. The symbol `c` of `Op(p) ∘ Op(a)` satisfies
  `c ∼ ∑ₖ sharpTerm p a k` with remainders `c - ∑_{k < N} sharpTerm p a k` of order `m' + m - N`
  whose estimates are uniform in the position.

## The expansion

The remainder of `c` after `N` terms is the series `∑ⱼ rⱼ` of the remainders
`rⱼ = p # aⱼ - ∑_{k < N} sharpTerm p aⱼ k` of the pieces, because near each position only finitely
many pieces are nonzero and they sum to `a`. The remainder estimates of the composition expansion
hold uniformly over the pieces
(`TauCeti.Symbol.IsUniform.exists_norm_mixedDeriv_sharpRemainder_le`), since its proof only uses
bounds on the Fourier transforms of the slices of `aⱼ`. Away from `j`
the terms `sharpTerm p aⱼ k` vanish, so `rⱼ = p # aⱼ` there for every `N`: it is bounded both by
`C ‖x - j‖ ^ (-4n) ⟨ξ⟩ ^ (m' + m)` and by `C ⟨ξ⟩ ^ (m' + m - 2N)`, and the geometric mean of these
bounds gives `C ‖x - j‖ ^ (-2n) ⟨ξ⟩ ^ (m' + m - N)`. The same holds for all derivatives, so the
series `∑ⱼ rⱼ` converges to a uniform symbol of order `m' + m - N`.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, §18.1,
  Theorem 18.1.8 (composition in the symbol classes with estimates uniform on `ℝⁿ`).
* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture I,
  (2.5)–(2.7).
-/

public section

noncomputable section

open MeasureTheory Real FourierTransform Metric
open scoped ContDiff RealInnerProductSpace SchwartzMap Topology

namespace TauCeti

namespace Symbol

variable {n : ℕ} {m m' : ℝ} {V W U : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [NormedAddCommGroup W] [NormedSpace ℂ W] [NormedAddCommGroup U] [NormedSpace ℂ U]

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
private theorem exists_isUniform_hasSum_coefficient (a : ι → Symbol n V W μ)
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
private theorem hasSum_quantizeSchwartzValue_of_hasSum_coefficient [Countable ι] {μ' : ℝ}
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
position and of `i`. -/
private def IsBallFamily (z : ι → CoordinateSpace n) (r : ℝ) (c : ι → Symbol n V W m) : Prop :=
  (∀ i x ξ, r < dist x (z i) → (c i).coefficient (x, ξ) = 0) ∧
    ∀ α β : List (Fin n), ∃ C, ∀ i x ξ,
      ‖mixedDeriv α β (c i).coefficient x ξ‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ ((m - β.length) / 2)

variable {z : ι → CoordinateSpace n} {r : ℝ} {c : ι → Symbol n V W m}

/-- A member of a ball family vanishes near every position at distance more than `r` from its
centre. -/
private theorem IsBallFamily.eventually_eq_zero (hc : IsBallFamily z r c) (i : ι)
    {x : CoordinateSpace n} (hx : r < dist x (z i)) :
    ∀ᶠ y in nhds x, ∀ ξ, (c i).coefficient (y, ξ) = 0 :=
  Filter.eventually_of_mem ((isOpen_lt continuous_const (continuous_id.dist
    continuous_const)).mem_nhds hx) fun _ hy ξ ↦ hc.1 i _ ξ hy

private theorem IsBallFamily.hasCompactSpatialSupport (hc : IsBallFamily z r c) (i : ι) :
    (c i).HasCompactSpatialSupport :=
  hasCompactSpatialSupport_iff.2 ⟨closedBall (z i) r, isCompact_closedBall _ _, fun x hx ξ ↦
    hc.1 i x ξ (not_le.1 fun h ↦ hx (mem_closedBall.2 h))⟩

private theorem IsBallFamily.map_spatialDeriv (hc : IsBallFamily z r c) (j : Fin n) :
    IsBallFamily z r fun i ↦ spatialDeriv j (c i) := by
  refine ⟨fun i x ξ hx ↦ ?_, fun α β ↦ ?_⟩
  · have h : (fun y ↦ (c i).coefficient (y, ξ)) =ᶠ[nhds x] fun _ ↦ 0 :=
      (hc.eventually_eq_zero i hx).mono fun y hy ↦ hy ξ
    rw [coefficient_spatialDeriv, (h.coordinateDeriv [j]).eq_of_nhds,
      coordinateDeriv_const _ (List.cons_ne_nil j [])]
    rfl
  · obtain ⟨C, hC⟩ := hc.2 (α ++ [j]) β
    exact ⟨C, fun i x ξ ↦ by simpa using hC i x ξ⟩

private theorem IsBallFamily.map_frequencyDeriv (hc : IsBallFamily z r c) (j : Fin n) :
    IsBallFamily z r fun i ↦ frequencyDeriv j (c i) := by
  refine ⟨fun i x ξ hx ↦ ?_, fun α β ↦ ?_⟩
  · have h : (fun η ↦ (c i).coefficient (x, η)) = fun _ ↦ 0 := funext (hc.1 i x · hx)
    rw [coefficient_frequencyDeriv, h, coordinateDeriv_const _ (List.cons_ne_nil j [])]
    rfl
  · obtain ⟨C, hC⟩ := hc.2 α (β ++ [j])
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
private theorem IsBallFamily.comp_coordSubSymbol (hc : IsBallFamily z r c) (j : Fin n) :
    IsBallFamily z r fun i ↦ (coordSubSymbol (z i) j).comp (c i) := by
  refine ⟨fun i x ξ hx ↦ by simp [coefficient_comp, hc.1 i x ξ hx], fun α β ↦ ?_⟩
  choose D hD using hc.2
  set K := (β.sublists'.revzip.map fun t =>
    (α.sublists'.revzip.map fun s => max r 1 * D s.2 t.2).sum).sum
  refine ⟨max K 0, fun i x ξ ↦ ?_⟩
  beta_reduce
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
private theorem isBallFamily_ofSpatial_comp (z : ι → CoordinateSpace n) (r : ℝ)
    (φ : ι → CoordinateSpace n → ℝ) (hφ : ∀ i, ContDiff ℝ ∞ (φ i))
    (hφB : ∀ k : ℕ, ∃ B, ∀ i x, ‖iteratedFDeriv ℝ k (φ i) x‖ ≤ B)
    (hφz : ∀ i x, r < dist x (z i) → φ i x = 0) {a : Symbol n V W m} (ha : a.IsUniform) :
    IsBallFamily z r fun i ↦
      (ofSpatial (fun x ↦ φ i x • ContinuousLinearMap.id ℂ W) ((hφ i).smul contDiff_const)).comp
        a := by
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
  refine ⟨max K 0, fun i x ξ ↦ norm_mixedDeriv_comp_le_of_coefficient_eq
    (f := fun y ↦ L (φ i y)) (B := fun s ↦ max (B s.length) 0) (fun p ↦ by simp [L]) a
    (fun _ ↦ le_max_right _ _) (fun s ↦ ?_) (fun s t ↦ hD s t x ξ) α β⟩
  have hLφ : ContDiff ℝ ∞ (L ∘ φ i) := L.contDiff.comp (hφ i)
  calc ‖coordinateDeriv s (fun y ↦ L (φ i y)) x‖
      ≤ ‖iteratedFDeriv ℝ s.length (L ∘ φ i) x‖ :=
        norm_coordinateDeriv_le s (hLφ.of_le (by exact_mod_cast le_top)) x
    _ ≤ ‖L‖ * ‖iteratedFDeriv ℝ s.length (φ i) x‖ :=
        L.norm_iteratedFDeriv_comp_left (hφ i).contDiffAt (by exact_mod_cast le_top)
    _ ≤ 1 * max (B s.length) 0 := mul_le_mul hL ((hB _ i x).trans (le_max_left _ _))
        (norm_nonneg _) zero_le_one
    _ = _ := one_mul _

end BallFamily

/-! ### Uniform decay of the Fourier transforms of the slices -/

section Decay

/-- Expanding one factor `‖v‖²` in coordinates:
`‖v‖ ^ (2 (N + 1)) F = ∑ⱼ ‖v‖ ^ (2N) (vⱼ² F)`. -/
private theorem norm_pow_two_mul_succ_mul_eq_sum (v : CoordinateSpace n) (N : ℕ) (F : ℝ) :
    ‖v‖ ^ (2 * (N + 1)) * F = ∑ j, ‖v‖ ^ (2 * N) * (v j ^ 2 * F) := by
  rw [← Finset.mul_sum, ← Finset.sum_mul, ← EuclideanSpace.real_norm_sq_eq]
  ring

/-- Bounds `F ≤ C₀ w` and `‖v‖ ^ (2N) F ≤ C₁ w` combine to the weighted bound
`F ≤ 2 ^ (N - 1) (C₀ + C₁) w ((1 + ‖v‖²) ^ N)⁻¹`. -/
private theorem le_mul_one_add_norm_sq_pow_inv {v : CoordinateSpace n} {N : ℕ} {F C₀ C₁ w : ℝ}
    (hF : 0 ≤ F) (h₀ : F ≤ C₀ * w) (h₁ : ‖v‖ ^ (2 * N) * F ≤ C₁ * w) :
    F ≤ 2 ^ (N - 1) * (C₀ + C₁) * w * ((1 + ‖v‖ ^ 2) ^ N)⁻¹ := by
  rw [← div_eq_mul_inv, le_div_iff₀ (by positivity), mul_comm F]
  calc (1 + ‖v‖ ^ 2) ^ N * F ≤ 2 ^ (N - 1) * (1 ^ N + (‖v‖ ^ 2) ^ N) * F :=
        mul_le_mul_of_nonneg_right (add_pow_le zero_le_one (by positivity) N) hF
    _ = 2 ^ (N - 1) * (F + ‖v‖ ^ (2 * N) * F) := by rw [one_pow, ← pow_mul]; ring
    _ ≤ 2 ^ (N - 1) * (C₀ * w + C₁ * w) :=
        mul_le_mul_of_nonneg_left (add_le_add h₀ h₁) (by positivity)
    _ = 2 ^ (N - 1) * (C₀ + C₁) * w := by ring

variable {ι : Type*} {z : ι → CoordinateSpace n} {r : ℝ}

/-- The Fourier transforms of the position slices of a ball family are bounded by `D ⟨ξ⟩ ^ m`,
uniformly in the family: they are bounded by the `L¹` norms of the slices. -/
private theorem IsBallFamily.exists_norm_fourier_le {c : ι → Symbol n V W m}
    (hc : IsBallFamily z r c) :
    ∃ D, ∀ i η ξ, ‖𝓕 (fun y ↦ (c i).coefficient (y, ξ)) η‖ ≤ D * (1 + ‖ξ‖ ^ 2) ^ (m / 2) := by
  obtain ⟨C, hC⟩ := hc.2 [] []
  set v := (volume : Measure (CoordinateSpace n)).real (closedBall 0 r)
  refine ⟨v * C, fun i η ξ ↦ ?_⟩
  set w := (1 + ‖ξ‖ ^ 2) ^ (m / 2)
  have hle (y : CoordinateSpace n) : ‖(c i).coefficient (y, ξ)‖ ≤
      (closedBall (z i) r).indicator (fun _ ↦ C * w) y := by
    by_cases hy : y ∈ closedBall (z i) r
    · rw [Set.indicator_of_mem hy]
      simpa [w] using hC i y ξ
    · rw [Set.indicator_of_notMem hy, hc.1 i y ξ (not_le.1 fun h ↦ hy (mem_closedBall.2 h)),
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
        = ∑ j, ‖η‖ ^ (2 * N) * (η j ^ 2 * ‖𝓕 (fun y ↦ (c i).coefficient (y, ξ)) η‖) :=
          norm_pow_two_mul_succ_mul_eq_sum η N _
      _ ≤ ∑ j, ((2 * π) ^ 2)⁻¹ * (D j * (1 + ‖ξ‖ ^ 2) ^ (m / 2)) :=
          Finset.sum_le_sum fun j _ ↦ by
            rw [hj, mul_left_comm]
            exact mul_le_mul_of_nonneg_left (hD j i η ξ) (by positivity)
      _ = _ := by rw [← Finset.mul_sum, ← Finset.sum_mul, mul_assoc]

/-- **Rapid decay of the Fourier transforms of the slices, uniformly in the family.** For every
`s`, the Fourier transforms of the position slices of a ball family satisfy
`‖𝓕 cᵢ(η, ξ)‖ ≤ D ⟨ξ⟩ ^ m ⟨η⟩ ^ (-s)` with `D` independent of `i`. -/
private theorem IsBallFamily.exists_norm_fourier_le_rpow {c : ι → Symbol n V W m}
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
  have hF := le_mul_one_add_norm_sq_pow_inv (norm_nonneg _) (hD₀ i η ξ) (hD i η ξ)
  have hinv : 0 < ((1 + ‖η‖ ^ 2) ^ N)⁻¹ := by positivity
  -- `((1 + ‖η‖²) ^ N)⁻¹ = (1 + ‖η‖²) ^ (-N) ≤ (1 + ‖η‖²) ^ (-s / 2)` since `N ≥ s / 2`.
  have hN : ((1 + ‖η‖ ^ 2) ^ N)⁻¹ ≤ (1 + ‖η‖ ^ 2) ^ (-s / 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_neg (by positivity)]
    exact Real.rpow_le_rpow_of_exponent_le hη (by linarith [Nat.le_ceil (s / 2)])
  exact hF.trans (mul_le_mul_of_nonneg_left hN
    ((mul_nonneg_iff_of_pos_right hinv).1 ((norm_nonneg _).trans hF)))

end Decay

/-! ### The composition with a member of a ball family -/

section Sharp

variable {ι : Type*} {z : ι → CoordinateSpace n} {r : ℝ}

/-- **The shifted composition integrals are bounded uniformly in the family.** If `p` is a symbol
of order `m'` with estimates uniform in the position and `c` is a ball family of order `m`, then
`‖∫ sharpIntegrand p cᵢ s (x, ξ) η dη‖ ≤ C ⟨ξ⟩ ^ (m' + m)` with `C` independent of `i`, of `x` and
of the frequency scaling `|s| ≤ R`. -/
private theorem IsBallFamily.exists_norm_integral_sharpIntegrand_le {p : Symbol n W U m'}
    (hp : p.IsUniform) {c : ι → Symbol n V W m} (hc : IsBallFamily z r c) {R : ℝ} (hR : 1 ≤ R) :
    ∃ C, 0 ≤ C ∧ ∀ i, ∀ s : ℝ, |s| ≤ R → ∀ x ξ,
      ‖∫ η, sharpIntegrand p (c i) s (x, ξ) η‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ ((m' + m) / 2) := by
  obtain ⟨Cp, hCp0, hCp⟩ := hp.exists_bound_coefficient
  obtain ⟨D, hD⟩ := hc.exists_norm_fourier_le_rpow (|m'| + n + 1)
  set I := ∫ η : CoordinateSpace n, (1 + ‖η‖ ^ 2) ^ (-((n : ℝ) + 1) / 2)
  have hI : 0 ≤ I := integral_nonneg fun η ↦ by positivity
  set K := Cp * 2 ^ (|m'| / 2) * R ^ |m'| * max D 0
  have hK : 0 ≤ K := by have := zero_le_one.trans hR; positivity
  refine ⟨K * I, mul_nonneg hK hI, fun i s hs x ξ ↦ ?_⟩
  have hbound (η : CoordinateSpace n) : ‖sharpIntegrand p (c i) s (x, ξ) η‖ ≤
      K * (1 + ‖ξ‖ ^ 2) ^ ((m' + m) / 2) * (1 + ‖η‖ ^ 2) ^ (-((n : ℝ) + 1) / 2) := by
    rw [sharpIntegrand_apply, norm_smul, Circle.norm_coe, one_mul]
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    have hshift : (1 + ‖ξ + s • η‖ ^ 2) ^ (m' / 2) ≤
        2 ^ (|m'| / 2) * R ^ |m'| * (1 + ‖ξ‖ ^ 2) ^ (m' / 2) * (1 + ‖η‖ ^ 2) ^ (|m'| / 2) := by
      refine (one_add_norm_add_sq_rpow_le_mul m' ξ (s • η)).trans ?_
      have hsη : (1 + ‖s • η‖ ^ 2) ^ (|m'| / 2) ≤ R ^ |m'| * (1 + ‖η‖ ^ 2) ^ (|m'| / 2) := by
        have hle : ‖s • η‖ ≤ ‖R • η‖ := by
          rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_of_nonneg (zero_le_one.trans hR)]
          gcongr
        refine (Real.rpow_le_rpow (by positivity)
          (show 1 + ‖s • η‖ ^ 2 ≤ 1 + ‖R • η‖ ^ 2 by gcongr) (by positivity)).trans ?_
        simpa only [abs_abs] using one_add_norm_smul_sq_rpow_le hR |m'| η
      calc 2 ^ (|m'| / 2) * (1 + ‖ξ‖ ^ 2) ^ (m' / 2) * (1 + ‖s • η‖ ^ 2) ^ (|m'| / 2)
          ≤ 2 ^ (|m'| / 2) * (1 + ‖ξ‖ ^ 2) ^ (m' / 2) *
              (R ^ |m'| * (1 + ‖η‖ ^ 2) ^ (|m'| / 2)) := by gcongr
        _ = _ := by ring
    have hξ : (1 + ‖ξ‖ ^ 2) ^ (m' / 2) * (1 + ‖ξ‖ ^ 2) ^ (m / 2) =
        (1 + ‖ξ‖ ^ 2) ^ ((m' + m) / 2) := by
      rw [← Real.rpow_add (by positivity)]
      ring_nf
    have hη : (1 + ‖η‖ ^ 2) ^ (|m'| / 2) * (1 + ‖η‖ ^ 2) ^ (-(|m'| + n + 1) / 2) =
        (1 + ‖η‖ ^ 2) ^ (-((n : ℝ) + 1) / 2) := by
      rw [← Real.rpow_add (by positivity)]
      ring_nf
    calc ‖p.coefficient (x, ξ + s • η)‖ * ‖𝓕 (fun y ↦ (c i).coefficient (y, ξ)) η‖
        ≤ (Cp * (2 ^ (|m'| / 2) * R ^ |m'| * (1 + ‖ξ‖ ^ 2) ^ (m' / 2) *
            (1 + ‖η‖ ^ 2) ^ (|m'| / 2))) *
          (max D 0 * (1 + ‖ξ‖ ^ 2) ^ (m / 2) * (1 + ‖η‖ ^ 2) ^ (-(|m'| + n + 1) / 2)) := by
          gcongr
          · exact (hCp x _).trans (mul_le_mul_of_nonneg_left hshift hCp0)
          · exact (hD i η ξ).trans (by gcongr; exact le_max_left _ _)
      _ = K * ((1 + ‖ξ‖ ^ 2) ^ (m' / 2) * (1 + ‖ξ‖ ^ 2) ^ (m / 2)) *
          ((1 + ‖η‖ ^ 2) ^ (|m'| / 2) * (1 + ‖η‖ ^ 2) ^ (-(|m'| + n + 1) / 2)) := by ring
      _ = _ := by rw [hξ, hη]
  refine (norm_integral_le_of_norm_le (integrable_one_add_norm_sq_rpow_neg_succ_div_two.const_mul
    (K * (1 + ‖ξ‖ ^ 2) ^ ((m' + m) / 2))) (.of_forall hbound)).trans_eq ?_
  rw [integral_const_mul]
  ring

/-- **The composition symbol is bounded uniformly in the family.** If `p` is a symbol of order `m'`
with estimates uniform in the position and `c` is a ball family of order `m`, then
`‖(p # cᵢ)(x, ξ)‖ ≤ C ⟨ξ⟩ ^ (m' + m)` with `C` independent of `i` and `x`. -/
private theorem IsBallFamily.exists_norm_sharp_le {p : Symbol n W U m'} (hp : p.IsUniform)
    {c : ι → Symbol n V W m} (hc : IsBallFamily z r c) :
    ∃ C, ∀ i x ξ, ‖(p.sharp (c i) (hc.hasCompactSpatialSupport i)).coefficient (x, ξ)‖ ≤
      C * (1 + ‖ξ‖ ^ 2) ^ ((m' + m) / 2) := by
  obtain ⟨C, -, hC⟩ := hc.exists_norm_integral_sharpIntegrand_le hp (R := 2 * π)
    (by linarith [Real.two_le_pi])
  refine ⟨C, fun i x ξ ↦ ?_⟩
  simpa only [coefficient_sharp, sharpIntegrand_apply] using
    hC i (2 * π) (abs_of_pos Real.two_pi_pos).le x ξ

variable [CompleteSpace V] [CompleteSpace W] [CompleteSpace U]

/-- Applying the commutator with a coordinate function twice:
`(x - z)ⱼ² (p # b) = p # ((y - z)ⱼ² b) + 2i (∂_{ξⱼ} p) # ((y - z)ⱼ b) - (∂_{ξⱼ}² p) # b`, which
bounds `(x - z)ⱼ² ‖(p # b)(x, ξ)‖` by the norms of the three terms. -/
private theorem sq_coordSub_mul_norm_coefficient_sharp_le (p : Symbol n W U m')
    {b : Symbol n V W m} (hb : b.HasCompactSpatialSupport) (z : CoordinateSpace n) (j : Fin n)
    (x ξ : CoordinateSpace n) :
    ((x - z) j) ^ 2 * ‖(p.sharp b hb).coefficient (x, ξ)‖ ≤
      ‖(p.sharp ((coordSubSymbol z j).comp ((coordSubSymbol z j).comp b))
          ((hb.comp_left _).comp_left _)).coefficient (x, ξ)‖ +
        2 * ‖((frequencyDeriv j p).sharp ((coordSubSymbol z j).comp b)
          (hb.comp_left _)).coefficient (x, ξ)‖ +
        ‖((frequencyDeriv j (frequencyDeriv j p)).sharp b hb).coefficient (x, ξ)‖ := by
  set a : ℂ := ((x - z) j : ℂ)
  have e₁ := coordSub_smul_coefficient_sharp p hb z j x ξ
  have e₂ := coordSub_smul_coefficient_sharp p (hb.comp_left (coordSubSymbol z j)) z j x ξ
  have e₃ := coordSub_smul_coefficient_sharp (frequencyDeriv j p) hb z j x ξ
  have hsq : a • a • (p.sharp b hb).coefficient (x, ξ) =
      (p.sharp ((coordSubSymbol z j).comp ((coordSubSymbol z j).comp b))
        ((hb.comp_left _).comp_left _)).coefficient (x, ξ) +
      (2 * Complex.I) • ((frequencyDeriv j p).sharp ((coordSubSymbol z j).comp b)
        (hb.comp_left _)).coefficient (x, ξ) -
      ((frequencyDeriv j (frequencyDeriv j p)).sharp b hb).coefficient (x, ξ) := by
    rw [e₁, smul_add, e₂, smul_comm a Complex.I, e₃, smul_add, smul_smul Complex.I Complex.I,
      Complex.I_mul_I, two_mul, add_smul, neg_one_smul]
    abel
  have hnorm : ‖a • a • (p.sharp b hb).coefficient (x, ξ)‖ =
      ((x - z) j) ^ 2 * ‖(p.sharp b hb).coefficient (x, ξ)‖ := by
    rw [norm_smul, norm_smul, Complex.norm_real, Real.norm_eq_abs, ← mul_assoc, ← sq, sq_abs]
  have h2I : ‖(2 * Complex.I)‖ = 2 := by simp
  rw [← hnorm, hsq]
  refine (norm_sub_le _ _).trans (add_le_add ((norm_add_le _ _).trans_eq ?_) le_rfl)
  rw [norm_smul, h2I]

/-- **Decay away from the centres.** If `p` is a symbol of order `m'` with estimates uniform in
the position and `c` is a ball family of order `m`, then `(p # cᵢ)(x, ξ)` decays in the distance
from `x` to the centre `zᵢ` faster than every power, uniformly in `i`:
`‖x - zᵢ‖ ^ (2N) ‖(p # cᵢ)(x, ξ)‖ ≤ C ⟨ξ⟩ ^ (m' + m)`. -/
private theorem IsBallFamily.exists_norm_sub_pow_mul_norm_sharp_le (N : ℕ) :
    ∀ {m' : ℝ} {p : Symbol n W U m'}, p.IsUniform → ∀ {m : ℝ} {c : ι → Symbol n V W m}
      (hc : IsBallFamily z r c), ∃ C, 0 ≤ C ∧ ∀ i x ξ, ‖x - z i‖ ^ (2 * N) *
        ‖(p.sharp (c i) (hc.hasCompactSpatialSupport i)).coefficient (x, ξ)‖ ≤
          C * (1 + ‖ξ‖ ^ 2) ^ ((m' + m) / 2) := by
  induction N with
  | zero =>
    intro m' p hp m c hc
    obtain ⟨C, hC⟩ := hc.exists_norm_sharp_le hp
    refine ⟨max C 0, le_max_right _ _, fun i x ξ ↦ ?_⟩
    rw [mul_zero, pow_zero, one_mul]
    exact (hC i x ξ).trans (by gcongr; exact le_max_left _ _)
  | succ N ih =>
    intro m' p hp m c hc
    have hc' (j : Fin n) := hc.comp_coordSubSymbol j
    have hp' (j : Fin n) := hp.frequencyDeriv j
    choose A hA0 hA using fun j ↦ ih hp ((hc' j).comp_coordSubSymbol j)
    choose B hB0 hB using fun j ↦ ih (hp' j) (hc' j)
    choose C hC0 hC using fun j ↦ ih ((hp' j).frequencyDeriv j) hc
    refine ⟨∑ j, (A j + 2 * B j + C j), Finset.sum_nonneg fun j _ ↦ by
      linarith [hA0 j, hB0 j, hC0 j], fun i x ξ ↦ ?_⟩
    set w := (1 + ‖ξ‖ ^ 2) ^ ((m' + m) / 2)
    have hci := hc.hasCompactSpatialSupport i
    have hj (j : Fin n) : ‖x - z i‖ ^ (2 * N) * (((x - z i) j) ^ 2 *
        ‖(p.sharp (c i) hci).coefficient (x, ξ)‖) ≤ (A j + 2 * B j + C j) * w := by
      have hA' := hA j i x ξ
      have ewA : (m' + (0 + (0 + m))) / 2 = (m' + m) / 2 := by ring
      rw [ewA] at hA'
      have hwB : (1 + ‖ξ‖ ^ 2) ^ ((m' - 1 + (0 + m)) / 2) ≤ w :=
        rpow_weight_le_rpow_weight ξ (by linarith)
      have hwC : (1 + ‖ξ‖ ^ 2) ^ ((m' - 1 - 1 + m) / 2) ≤ w :=
        rpow_weight_le_rpow_weight ξ (by linarith)
      refine (mul_le_mul_of_nonneg_left (sq_coordSub_mul_norm_coefficient_sharp_le p hci (z i) j
        x ξ) (by positivity)).trans ?_
      rw [mul_add, mul_add, mul_left_comm _ 2]
      exact (add_le_add (add_le_add hA' (mul_le_mul_of_nonneg_left
        ((hB j i x ξ).trans (mul_le_mul_of_nonneg_left hwB (hB0 j))) zero_le_two))
        ((hC j i x ξ).trans (mul_le_mul_of_nonneg_left hwC (hC0 j)))).trans_eq (by ring)
    calc ‖x - z i‖ ^ (2 * (N + 1)) * ‖(p.sharp (c i) hci).coefficient (x, ξ)‖
        = ∑ j, ‖x - z i‖ ^ (2 * N) * (((x - z i) j) ^ 2 *
            ‖(p.sharp (c i) hci).coefficient (x, ξ)‖) :=
          norm_pow_two_mul_succ_mul_eq_sum (x - z i) N _
      _ ≤ ∑ j, (A j + 2 * B j + C j) * w := Finset.sum_le_sum fun j _ ↦ hj j
      _ = _ := by rw [Finset.sum_mul]

/-- **Decay of the derivatives away from the centres.** Every mixed derivative
`∂ₓ^α ∂_ξ^β (p # cᵢ)` satisfies `‖x - zᵢ‖ ^ (2N) ‖∂ₓ^α ∂_ξ^β (p # cᵢ)(x, ξ)‖ ≤
C ⟨ξ⟩ ^ (m' + m - |β|)`, uniformly in `i`. -/
private theorem IsBallFamily.exists_norm_sub_pow_mul_norm_mixedDeriv_sharp_le (N : ℕ)
    (α β : List (Fin n)) :
    ∀ {m' : ℝ} {p : Symbol n W U m'}, p.IsUniform → ∀ {m : ℝ} {c : ι → Symbol n V W m}
      (hc : IsBallFamily z r c), ∃ C, 0 ≤ C ∧ ∀ i x ξ, ‖x - z i‖ ^ (2 * N) *
        ‖mixedDeriv α β (p.sharp (c i) (hc.hasCompactSpatialSupport i)).coefficient x ξ‖ ≤
          C * (1 + ‖ξ‖ ^ 2) ^ ((m' + m - β.length) / 2) := by
  obtain ⟨D, hD⟩ : ∃ D, α.length + β.length = D := ⟨_, rfl⟩
  induction D generalizing α β with
  | zero =>
    obtain ⟨rfl, rfl⟩ : α = [] ∧ β = [] := by simpa [List.length_eq_zero_iff] using hD
    intro m' p hp m c hc
    simpa using IsBallFamily.exists_norm_sub_pow_mul_norm_sharp_le N hp hc
  | succ D ih =>
    intro m' p hp m c hc
    rcases List.eq_nil_or_concat' β with rfl | ⟨β', j, rfl⟩
    · rcases List.eq_nil_or_concat' α with rfl | ⟨α', j, rfl⟩
      · simp at hD
      · obtain ⟨C₁, hC₁0, hC₁⟩ := ih α' [] (by simpa using hD) (hp.spatialDeriv j) hc
        obtain ⟨C₂, hC₂0, hC₂⟩ := ih α' [] (by simpa using hD) hp (hc.map_spatialDeriv j)
        refine ⟨C₁ + C₂, add_nonneg hC₁0 hC₂0, fun i x ξ ↦ ?_⟩
        rw [← mixedDeriv_spatialDeriv, spatialDeriv_sharp, coefficient_add,
          mixedDeriv_add (Symbol.contDiff_coefficient _) (Symbol.contDiff_coefficient _)]
        refine (mul_le_mul_of_nonneg_left (norm_add_le _ _) (by positivity)).trans ?_
        rw [mul_add, add_mul]
        exact add_le_add (hC₁ i x ξ) (hC₂ i x ξ)
    · have hlen : α.length + β'.length = D := by
        simp only [List.length_append, List.length_singleton] at hD
        omega
      obtain ⟨C₁, hC₁0, hC₁⟩ := ih α β' hlen (hp.frequencyDeriv j) hc
      obtain ⟨C₂, hC₂0, hC₂⟩ := ih α β' hlen hp (hc.map_frequencyDeriv j)
      refine ⟨C₁ + C₂, add_nonneg hC₁0 hC₂0, fun i x ξ ↦ ?_⟩
      have hci := hc.hasCompactSpatialSupport i
      have hfun : (frequencyDeriv j (p.sharp (c i) hci)).coefficient =
          ((frequencyDeriv j p).sharp (c i) hci).coefficient +
            (p.sharp (frequencyDeriv j (c i)) (hci.frequencyDeriv j)).coefficient :=
        funext fun q ↦ coefficient_frequencyDeriv_sharp hci j q.1 q.2
      have e₁ : (m' - 1 + m - β'.length) / 2 = (m' + m - (β' ++ [j]).length) / 2 := by
        simp only [List.length_append, List.length_singleton, Nat.cast_add, Nat.cast_one]
        ring
      have e₂ : (m' + (m - 1) - β'.length) / 2 = (m' + m - (β' ++ [j]).length) / 2 := by
        simp only [List.length_append, List.length_singleton, Nat.cast_add, Nat.cast_one]
        ring
      have h₁ := hC₁ i x ξ
      have h₂ := hC₂ i x ξ
      rw [e₁] at h₁
      rw [e₂] at h₂
      rw [← mixedDeriv_frequencyDeriv, hfun,
        mixedDeriv_add (Symbol.contDiff_coefficient _) (Symbol.contDiff_coefficient _)]
      refine (mul_le_mul_of_nonneg_left (norm_add_le _ _) (by positivity)).trans ?_
      rw [mul_add, add_mul]
      exact add_le_add h₁ h₂

/-- The derivative estimates of `p # cᵢ` with the weight `(1 + ‖x - zᵢ‖²) ^ (-n)` in the
position. -/
private theorem IsBallFamily.exists_norm_mixedDeriv_sharp_le {p : Symbol n W U m'}
    (hp : p.IsUniform) {c : ι → Symbol n V W m} (hc : IsBallFamily z r c)
    (α β : List (Fin n)) :
    ∃ C, 0 ≤ C ∧ ∀ i x ξ,
      ‖mixedDeriv α β (p.sharp (c i) (hc.hasCompactSpatialSupport i)).coefficient x ξ‖ ≤
        C * ((1 + ‖x - z i‖ ^ 2) ^ n)⁻¹ * (1 + ‖ξ‖ ^ 2) ^ ((m' + m - β.length) / 2) := by
  obtain ⟨C₀, hC₀0, hC₀⟩ :=
    IsBallFamily.exists_norm_sub_pow_mul_norm_mixedDeriv_sharp_le 0 α β hp hc
  obtain ⟨C₁, hC₁0, hC₁⟩ :=
    IsBallFamily.exists_norm_sub_pow_mul_norm_mixedDeriv_sharp_le n α β hp hc
  refine ⟨2 ^ (n - 1) * (C₀ + C₁), by positivity, fun i x ξ ↦ ?_⟩
  have h₀ := hC₀ i x ξ
  rw [mul_zero, pow_zero, one_mul] at h₀
  exact (le_mul_one_add_norm_sq_pow_inv (norm_nonneg _) h₀ (hC₁ i x ξ)).trans_eq (by ring)


omit [CompleteSpace V] in
/-- Away from the closed ball of a member of a ball family, the remainders of the composition
expansion are the composition symbol itself, with all their derivatives: the terms of the expansion
only involve the member near the position, where it vanishes. -/
private theorem IsBallFamily.mixedDeriv_sharpRemainder_eq {p : Symbol n W U m'}
    {c : ι → Symbol n V W m} (hc : IsBallFamily z r c) (N : ℕ) (α β : List (Fin n)) {i : ι}
    {x : CoordinateSpace n} (hx : r < dist x (z i)) (ξ : CoordinateSpace n) :
    mixedDeriv α β (p.sharpRemainder (c i) (hc.hasCompactSpatialSupport i) N).coefficient x ξ =
      mixedDeriv α β (p.sharp (c i) (hc.hasCompactSpatialSupport i)).coefficient x ξ := by
  refine mixedDeriv_congr_of_eventually ?_ α β ξ
  filter_upwards [(isOpen_lt continuous_const (continuous_id.dist continuous_const)).mem_nhds hx]
    with y hy η
  rw [coefficient_sharpRemainder, Pi.sub_apply, Finset.sum_apply, sub_eq_self]
  exact Finset.sum_eq_zero fun k _ ↦ coefficient_sharpTerm_eq_zero_of_eventuallyEq_zero_right
    (((hc.eventually_eq_zero i hy).prod_inl_nhds η).mono fun q hq ↦ hq q.2) p k

omit [CompleteSpace V] in
/-- The remainder estimates of the composition expansion hold uniformly over a ball family: every
mixed derivative of `p # cᵢ - ∑_{k < N} sharpTerm p cᵢ k` is bounded by
`C ⟨ξ⟩ ^ (m' + m - N - |β|)`, with `C` independent of `i` and the position. -/
private theorem IsBallFamily.exists_norm_mixedDeriv_sharpRemainder_le_rpow {p : Symbol n W U m'}
    (hp : p.IsUniform) {c : ι → Symbol n V W m} (hc : IsBallFamily z r c) (N : ℕ)
    (α β : List (Fin n)) :
    ∃ C, 0 ≤ C ∧ ∀ i x ξ,
      ‖mixedDeriv α β (p.sharpRemainder (c i) (hc.hasCompactSpatialSupport i) N).coefficient x ξ‖ ≤
        C * (1 + ‖ξ‖ ^ 2) ^ ((m' + m - N - β.length) / 2) :=
  hp.exists_norm_mixedDeriv_sharpRemainder_le (fun c ↦ IsBallFamily z r c)
    (fun hc i ↦ hc.hasCompactSpatialSupport i) (fun hc j ↦ hc.map_spatialDeriv j)
    (fun hc j ↦ hc.map_frequencyDeriv j)
    (fun ha hc ↦ hc.exists_norm_integral_sharpIntegrand_le ha (by linarith [Real.two_le_pi]))
    hc N α β

/-- **Decay of the composition away from the centres, at every order.** Outside the closed ball
of radius `r` about `zᵢ`, the mixed derivatives of `p # cᵢ` satisfy
`‖x - zᵢ‖ ^ (2n) ‖∂ₓ^α ∂_ξ^β (p # cᵢ)(x, ξ)‖ ≤ C ⟨ξ⟩ ^ (m' + m - N - |β|)` for every `N`,
uniformly in `i`. There `p # cᵢ` agrees with the remainder after `2N` terms, of order
`m' + m - 2N`, and it decays like `‖x - zᵢ‖ ^ (-4n) ⟨ξ⟩ ^ (m' + m - |β|)`; the bound is the
geometric mean of these two. -/
private theorem IsBallFamily.exists_norm_sub_pow_mul_norm_mixedDeriv_sharp_le_of_lt
    {p : Symbol n W U m'} (hp : p.IsUniform) {c : ι → Symbol n V W m} (hc : IsBallFamily z r c)
    (N : ℕ) (α β : List (Fin n)) :
    ∃ C, 0 ≤ C ∧ ∀ i x ξ, r < dist x (z i) → ‖x - z i‖ ^ (2 * n) *
      ‖mixedDeriv α β (p.sharp (c i) (hc.hasCompactSpatialSupport i)).coefficient x ξ‖ ≤
        C * (1 + ‖ξ‖ ^ 2) ^ ((m' + m - N - β.length) / 2) := by
  obtain ⟨B, hB0, hB⟩ := hc.exists_norm_mixedDeriv_sharpRemainder_le_rpow hp (2 * N) α β
  obtain ⟨A, hA0, hA⟩ :=
    IsBallFamily.exists_norm_sub_pow_mul_norm_mixedDeriv_sharp_le (2 * n) α β hp hc
  refine ⟨√(A * B), Real.sqrt_nonneg _, fun i x ξ hx ↦ ?_⟩
  set F := ‖mixedDeriv α β (p.sharp (c i) (hc.hasCompactSpatialSupport i)).coefficient x ξ‖
  set w := (1 + ‖ξ‖ ^ 2) ^ ((m' + m - N - β.length) / 2)
  have hFB : F ≤ B * (1 + ‖ξ‖ ^ 2) ^ ((m' + m - ((2 * N : ℕ) : ℝ) - β.length) / 2) := by
    simpa only [F, hc.mixedDeriv_sharpRemainder_eq _ _ _ hx] using hB i x ξ
  have hw : (1 + ‖ξ‖ ^ 2) ^ ((m' + m - β.length) / 2) *
      (1 + ‖ξ‖ ^ 2) ^ ((m' + m - ((2 * N : ℕ) : ℝ) - β.length) / 2) = w * w := by
    rw [← Real.rpow_add (by positivity), ← Real.rpow_add (by positivity)]
    congr 1
    push_cast
    ring
  have hsq : (‖x - z i‖ ^ (2 * n) * F) ^ 2 ≤ (√(A * B) * w) ^ 2 := by
    calc (‖x - z i‖ ^ (2 * n) * F) ^ 2 = (‖x - z i‖ ^ (2 * (2 * n)) * F) * F := by ring
      _ ≤ (A * (1 + ‖ξ‖ ^ 2) ^ ((m' + m - β.length) / 2)) *
          (B * (1 + ‖ξ‖ ^ 2) ^ ((m' + m - ((2 * N : ℕ) : ℝ) - β.length) / 2)) :=
        mul_le_mul (hA i x ξ) hFB (norm_nonneg _) (by positivity)
      _ = (√(A * B) * w) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt (mul_nonneg hA0 hB0), pow_two w, ← hw]
        ring
  exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).1 hsq

/-- **The remainders decay away from the centres.** If `p` is a symbol of order `m'` with estimates
uniform in the position and `c` is a ball family of order `m`, every mixed derivative
`∂ₓ^α ∂_ξ^β` of the remainder `p # cᵢ - ∑_{k < N} sharpTerm p cᵢ k` is bounded by
`C (1 + ‖x - zᵢ‖²) ^ (-n) ⟨ξ⟩ ^ (m' + m - N - |β|)`, with `C` independent of `i`: near the centre
by the uniform remainder estimate, and away from it, where the remainder is `p # cᵢ`, by
`IsBallFamily.exists_norm_sub_pow_mul_norm_mixedDeriv_sharp_le_of_lt`. -/
private theorem IsBallFamily.exists_norm_mixedDeriv_sharpRemainder_le {p : Symbol n W U m'}
    (hp : p.IsUniform) {c : ι → Symbol n V W m} (hc : IsBallFamily z r c) (N : ℕ)
    (α β : List (Fin n)) :
    ∃ C, 0 ≤ C ∧ ∀ i x ξ,
      ‖mixedDeriv α β (p.sharpRemainder (c i) (hc.hasCompactSpatialSupport i) N).coefficient x ξ‖ ≤
        C * ((1 + ‖x - z i‖ ^ 2) ^ n)⁻¹ * (1 + ‖ξ‖ ^ 2) ^ ((m' + m - N - β.length) / 2) := by
  obtain ⟨B, hB0, hB⟩ := hc.exists_norm_mixedDeriv_sharpRemainder_le_rpow hp N α β
  obtain ⟨A, hA0, hA⟩ := hc.exists_norm_sub_pow_mul_norm_mixedDeriv_sharp_le_of_lt hp N α β
  refine ⟨2 ^ (n - 1) * (B + (|r| ^ (2 * n) * B + A)), by positivity, fun i x ξ ↦ ?_⟩
  set F := ‖mixedDeriv α β (p.sharpRemainder (c i) (hc.hasCompactSpatialSupport i) N).coefficient
    x ξ‖
  set w := (1 + ‖ξ‖ ^ 2) ^ ((m' + m - N - β.length) / 2)
  have h₁ : ‖x - z i‖ ^ (2 * n) * F ≤ (|r| ^ (2 * n) * B + A) * w := by
    rcases le_or_gt (dist x (z i)) r with hx | hx
    · have hxr : ‖x - z i‖ ^ (2 * n) ≤ |r| ^ (2 * n) :=
        pow_le_pow_left₀ (norm_nonneg _) ((dist_eq_norm x (z i) ▸ hx).trans (le_abs_self r)) _
      calc ‖x - z i‖ ^ (2 * n) * F ≤ |r| ^ (2 * n) * (B * w) :=
            mul_le_mul hxr (hB i x ξ) (norm_nonneg _) (by positivity)
        _ ≤ (|r| ^ (2 * n) * B + A) * w := by
            rw [← mul_assoc, add_mul]
            exact le_add_of_nonneg_right (by positivity)
    · calc ‖x - z i‖ ^ (2 * n) * F ≤ A * w := by
            simpa only [F, hc.mixedDeriv_sharpRemainder_eq _ _ _ hx] using hA i x ξ hx
        _ ≤ (|r| ^ (2 * n) * B + A) * w :=
            mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (by positivity)) (by positivity)
  exact (le_mul_one_add_norm_sq_pow_inv (norm_nonneg _) (hB i x ξ) h₁).trans_eq (by ring)

end Sharp

/-! ### The composition of two uniform symbols -/

section Composition

variable [CompleteSpace V] [CompleteSpace W] [CompleteSpace U]

variable (W) in
/-- The lattice piece `χ(x - j) a(x, ξ)` of a symbol `a`, cut off by the integer translate of the
bump `χ = TauCeti.latticeBump n` centred at the lattice point `j ∈ ℤⁿ`. -/
private def latticePiece (a : Symbol n V W m) (j : Fin n → ℤ) : Symbol n V W (0 + m) :=
  (ofSpatial (fun x ↦ latticeBump n (x - latticePoint j) • ContinuousLinearMap.id ℂ W)
    ((contDiff_latticeBump_sub j).smul contDiff_const)).comp a

omit [CompleteSpace V] [CompleteSpace W] [CompleteSpace U] in
private theorem coefficient_latticePiece (a : Symbol n V W m) (j : Fin n → ℤ)
    (q : CoordinateSpace n × CoordinateSpace n) :
    (latticePiece W a j).coefficient q =
      latticeBump n (q.1 - latticePoint j) • a.coefficient q := by
  simp [latticePiece, coefficient_comp, coefficient_ofSpatial]

omit [CompleteSpace V] [CompleteSpace W] [CompleteSpace U] in
/-- The lattice pieces of a uniform symbol `a` form a ball family centred at the lattice points,
with radius `√n`. -/
private theorem isBallFamily_latticePiece {a : Symbol n V W m} (ha : a.IsUniform) :
    IsBallFamily (fun j : Fin n → ℤ ↦ latticePoint j) √n (latticePiece W a) :=
  isBallFamily_ofSpatial_comp _ _ (fun j y ↦ latticeBump n (y - latticePoint j))
    contDiff_latticeBump_sub exists_norm_iteratedFDeriv_latticeBump_sub_le
    (fun _ _ hx ↦ by_contra fun h ↦ (mem_closedBall.1
      (mem_closedBall_of_latticeBump_sub_ne_zero h)).not_gt hx) ha

omit [CompleteSpace V] in
/-- The quantization of `p # (χ(· - j) a)` is `Op(p)` applied to `χ(· - j) Op(a) u`. -/
private theorem quantizeSchwartzValue_sharp_latticePiece (p : Symbol n W U m')
    {a : Symbol n V W m} (ha : a.IsUniform) (u : 𝓢(CoordinateSpace n, V))
    (x : CoordinateSpace n) (j : Fin n → ℤ) :
    quantizeSchwartzValue (p.sharp _
      ((isBallFamily_latticePiece ha).hasCompactSpatialSupport j)).coefficient u x =
      quantizeSchwartzValue p.coefficient (SchwartzMap.smulLeftCLM W
        (fun y ↦ latticeBump n (y - latticePoint j)) (quantizeUniformCLM a ha u)) x := by
  rw [quantizeSchwartzValue_sharp_eq_quantizeSchwartzValue]
  congr 1
  ext y
  rw [HasCompactSupport.toSchwartzMap_toFun, latticePiece,
    quantizeSchwartzValue_ofSpatial_smul_id_comp,
    SchwartzMap.smulLeftCLM_apply_apply (hasTemperateGrowth_latticeBump_sub j), Complex.coe_smul,
    quantizeUniformCLM_apply]

/-- The series `∑ⱼ p # χⱼ a` over the lattice pieces of `a` converges to a symbol of order
`m' + m` with estimates uniform in the position, whose quantization is `Op(p) ∘ Op(a)`. -/
private theorem IsUniform.exists_hasSum_sharp_latticePiece {p : Symbol n W U m'}
    (hp : p.IsUniform) {a : Symbol n V W m} (ha : a.IsUniform) :
    ∃ (c : Symbol n V U (m' + m)) (hc : c.IsUniform),
      (∀ q, HasSum (fun j ↦ (p.sharp (latticePiece W a j)
        ((isBallFamily_latticePiece ha).hasCompactSpatialSupport j)).coefficient q)
          (c.coefficient q)) ∧
      quantizeUniformCLM p hp ∘L quantizeUniformCLM a ha = quantizeUniformCLM c hc := by
  have hfam := isBallFamily_latticePiece ha
  set F : (Fin n → ℤ) → Symbol n V U (m' + (0 + m)) := fun j ↦ p.sharp _
    (hfam.hasCompactSpatialSupport j)
  obtain ⟨b, hb, hbsum⟩ := exists_isUniform_hasSum_coefficient F
    (fun j x ↦ ((1 + ‖x - latticePoint j‖ ^ 2) ^ n)⁻¹) (fun _ _ ↦ by positivity)
    exists_summable_forall_one_add_norm_sub_latticePoint_sq_pow_inv_le
    tsum_one_add_norm_sub_latticePoint_sq_pow_inv_le (hfam.exists_norm_mixedDeriv_sharp_le hp)
  have hord : m' + (0 + m) = m' + m := by ring
  refine ⟨Symbol.inclusion hord.le b, hb.inclusion hord.le, fun q ↦ ?_, ?_⟩
  · rw [coefficient_inclusion]
    exact hbsum q
  ext u x
  rw [ContinuousLinearMap.comp_apply, quantizeUniformCLM_apply, quantizeUniformCLM_apply,
    coefficient_inclusion]
  -- Both sides are the sum of the series `∑ⱼ Op(p # χⱼ a) u (x)`.
  obtain ⟨C, -, hC⟩ := hfam.exists_norm_mixedDeriv_sharp_le hp [] []
  simp only [mixedDeriv_nil_nil, List.length_nil, CharP.cast_eq_zero, sub_zero] at hC
  refine ((hasSum_quantizeSchwartzValue_of_hasSum_coefficient hbsum
    (summable_one_add_norm_sub_latticePoint_sq_pow_inv x) (hC · x) u).unique ?_).symm
  -- The lattice partition of unity converges in Schwartz space, on which `Op(p)` is continuous.
  simp only [F, quantizeSchwartzValue_sharp_latticePiece p ha u x]
  have h := (SchwartzMap.hasSum_smulLeftCLM_latticeBump_sub (F := W)
    (quantizeUniformCLM a ha u)).mapL ((BoundedContinuousFunction.evalCLM ℂ x) ∘L
      (SchwartzMap.toBoundedContinuousFunctionCLM ℂ (CoordinateSpace n) U) ∘L
        quantizeUniformCLM p hp)
  simp only [ContinuousLinearMap.comp_apply, BoundedContinuousFunction.evalCLM_apply,
    SchwartzMap.toBoundedContinuousFunctionCLM_apply, quantizeUniformCLM_apply] at h
  exact h

/-- **Composition of uniform symbols.** If `p` and `a` are symbols of orders `m'` and `m` whose
estimates hold uniformly in the position, then `Op(p) ∘ Op(a)` is the quantization of a symbol of
order `m' + m` whose estimates hold uniformly in the position. No compact spatial support is
assumed for either symbol. The symbol has the asymptotic expansion `∑ₖ sharpTerm p a k`
(`TauCeti.Symbol.IsUniform.isUniformAsymptoticSum_sharpTerm_of_comp_eq`). -/
theorem IsUniform.exists_quantizeUniformCLM_comp {p : Symbol n W U m'} (hp : p.IsUniform)
    {a : Symbol n V W m} (ha : a.IsUniform) :
    ∃ (c : Symbol n V U (m' + m)) (hc : c.IsUniform),
      quantizeUniformCLM p hp ∘L quantizeUniformCLM a ha = quantizeUniformCLM c hc :=
  let ⟨c, hc, _, h⟩ := hp.exists_hasSum_sharp_latticePiece ha
  ⟨c, hc, h⟩

omit [CompleteSpace V] [CompleteSpace W] [CompleteSpace U] in
/-- The terms of the composition expansion with the lattice pieces of `b` sum to the terms with
`b`: near each position only finitely many pieces are nonzero, and they sum to `b` there. -/
private theorem hasSum_coefficient_sharpTerm_latticePiece (p : Symbol n W U m')
    (b : Symbol n V W m) (k : ℕ) (q : CoordinateSpace n × CoordinateSpace n) :
    HasSum (fun j ↦ (p.sharpTerm (latticePiece W b j) k).coefficient q)
      ((p.sharpTerm b k).coefficient q) := by
  obtain ⟨x, ξ⟩ := q
  set R := ‖x‖ + √n + 1
  have hfin := finite_setOf_norm_latticePoint_lt (ι := Fin n) R
  have hs : ∀ j, ‖latticePoint j‖ < R → j ∈ hfin.toFinset := fun j hj ↦ hfin.mem_toFinset.2 hj
  have hnear : ∀ᶠ y in 𝓝 x, ‖y‖ + √n < R :=
    (isOpen_lt (continuous_norm.add continuous_const) continuous_const).mem_nhds (by simp [R])
  -- Near `x`, the pieces centred at the lattice points of `hfin.toFinset` sum to `b`.
  have hsum : (p.sharpTerm b k).coefficient (x, ξ) =
      ∑ j ∈ hfin.toFinset, (p.sharpTerm (latticePiece W b j) k).coefficient (x, ξ) := by
    rw [← coefficient_sharpTerm_congr_of_eventually
      (b' := ∑ j ∈ hfin.toFinset, latticePiece W b j) ?_ p k ξ]
    · simpa using congrFun (coefficient_sharpTerm_eq_sum_right hfin.toFinset (fun _ ↦ 1)
        (latticePiece W b) (b₀ := ∑ j ∈ hfin.toFinset, latticePiece W b j)
        (by simp [coefficient_sum]) p k) (x, ξ)
    · filter_upwards [hnear] with y hy η
      rw [coefficient_sum, Finset.sum_apply]
      simp only [coefficient_latticePiece]
      rw [← Finset.sum_smul, sum_latticeBump_sub_eq_one hs hy, one_smul]
  rw [hsum]
  -- The other pieces vanish near `x`.
  refine hasSum_sum_of_ne_finset_zero fun j hj ↦
    coefficient_sharpTerm_eq_zero_of_eventuallyEq_zero_right ?_ p k
  filter_upwards [hnear.prod_inl_nhds ξ] with ⟨y, η⟩ hy
  rw [Pi.zero_apply, coefficient_latticePiece,
    latticeBump_sub_eq_zero_of_notMem (s := (hfin.toFinset : Set (Fin n → ℤ))) hs hy hj, zero_smul]

/-- **The asymptotic expansion of the composition of uniform symbols.** Let `p` and `a` be symbols
of orders `m'` and `m` whose estimates hold uniformly in the position, and let `c` be the symbol of
order `m' + m` with `Op(p) ∘ Op(a) = Op(c)`
(`TauCeti.Symbol.IsUniform.exists_quantizeUniformCLM_comp`). Then `c ∼ ∑ₖ sharpTerm p a k` in the
uniform symbol classes: for every `N`, the remainder
`c - ∑_{k < N} sharpTerm p a k` is a symbol of order `m' + m - N` whose estimates hold uniformly in
the position. No compact spatial support is assumed for either symbol; with compact spatial
support of `a`, `c` is the composition symbol `p # a` and this is
`TauCeti.Symbol.IsUniform.sharpRemainder`. -/
theorem IsUniform.isUniformAsymptoticSum_sharpTerm_of_comp_eq {p : Symbol n W U m'}
    (hp : p.IsUniform) {a : Symbol n V W m} (ha : a.IsUniform) {c : Symbol n V U (m' + m)}
    (hc : c.IsUniform)
    (h : quantizeUniformCLM p hp ∘L quantizeUniformCLM a ha = quantizeUniformCLM c hc) :
    IsUniformAsymptoticSum (m := fun k : ℕ ↦ m' + m - k) (Symbol.inclusion (by simp) c)
      (p.sharpTerm a) := by
  obtain ⟨b, hb, hbsum, hbq⟩ := hp.exists_hasSum_sharp_latticePiece ha
  -- By uniqueness of symbols, `c` is the sum `b` of the series `∑ⱼ p # χⱼ a`.
  obtain rfl : c = b := quantizeSchwartzValue_injective <| funext fun u ↦ funext fun x ↦ by
    simpa only [quantizeUniformCLM_apply] using congrArg (fun T ↦ T u x) (h.symm.trans hbq)
  have hfam := isBallFamily_latticePiece ha
  refine isUniformAsymptoticSum_iff.2 fun N ↦ ?_
  -- The remainders of the pieces decay away from their lattice points, so their series converges
  -- to a uniform symbol of order `m' + m - N`.
  obtain ⟨r, hr, hrsum⟩ := exists_isUniform_hasSum_coefficient
    (fun j ↦ p.sharpRemainder (latticePiece W a j) (hfam.hasCompactSpatialSupport j) N)
    (fun j x ↦ ((1 + ‖x - latticePoint j‖ ^ 2) ^ n)⁻¹) (fun _ _ ↦ by positivity)
    exists_summable_forall_one_add_norm_sub_latticePoint_sq_pow_inv_le
    tsum_one_add_norm_sub_latticePoint_sq_pow_inv_le
    (hfam.exists_norm_mixedDeriv_sharpRemainder_le hp N)
  refine ⟨Symbol.inclusion (by simp) r, hr.inclusion _, funext fun q ↦ ?_⟩
  have hq := hrsum q
  simp only [coefficient_sharpRemainder, Pi.sub_apply, Finset.sum_apply] at hq
  simp only [coefficient_inclusion, Pi.sub_apply, Finset.sum_apply]
  exact ((hbsum q).sub (hasSum_sum fun k _ ↦
    hasSum_coefficient_sharpTerm_latticePiece p a k q)).unique hq

end Composition

end Symbol

end TauCeti
