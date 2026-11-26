/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Symbol.Parameter.Basic
public import TauCeti.Analysis.Pseudodifferential.Symbol.Topology
import TauCeti.Analysis.Calculus.IteratedFDeriv.Prod

/-!
# Parameter-dependent symbols at a fixed spectral parameter

A strongly parameter-dependent symbol `a((x, ξ), z)` of order `m` (`TauCeti.ParameterSymbol`)
is, at each fixed spectral parameter `z`, an ordinary symbol `x, ξ ↦ a((x, ξ), z)` of order `m`
(`TauCeti.ParameterSymbol.toSymbol`). This is how the parameter-dependent calculus is quantized:
`Op(a(z))` is the quantization of this ordinary symbol.

The point of the parameter-dependent class is the dependence of these symbols on `z`. On each
compact set of positions, every spatial and frequency derivative of `a` is bounded by
`C (1 + ‖ξ‖ + ‖z‖ ^ (1 / 2)) ^ (m - |β|)`, with `C` depending on the compact set, uniformly in
`z ∈ Λ` (`TauCeti.ParameterSymbol.exists_norm_mixedDeriv_coefficient_le`), and the weight is at
least both `⟨ξ⟩ = (1 + ‖ξ‖²) ^ (1 / 2)` and `1 + ‖z‖ ^ (1 / 2)`. So for `m ≤ m' ≤ 0` a symbol of
order `m` trades `m' - m` frequency orders for decay in the spectral parameter: as a symbol of
order `m'`, `a(z)` has seminorms

`p_{K,α,β}(a(z)) ≤ C (1 + ‖z‖ ^ (1 / 2)) ^ (m - m')`

uniformly on `Λ` (`TauCeti.ParameterSymbol.exists_seminorm_inclusion_toSymbol_le`). For instance
the seminorms of order `0` of a remainder of order `-N` in a resolvent parametrix decay like
`‖z‖ ^ (-N / 2)`. The corresponding bound of the operators on Sobolev spaces, for symbols vanishing
outside a fixed compact set of positions, is
`TauCeti.ParameterSymbol.exists_norm_quantizeSobolev_inclusion_toSymbol_le`. At fixed `z` the
frequency estimates of order `m` hold with a constant that depends on `z`, since then the weight is
at most a multiple of `⟨ξ⟩`.

The symbols `a(z)` depend continuously on `z ∈ Λ` as soon as they are viewed in a class of strictly
larger order `m' > m` (`TauCeti.ParameterSymbol.continuousOn_inclusion_toSymbol`): at high
frequencies the difference `a(z) - a(z₀)` is small relative to `⟨ξ⟩ ^ m'` because it has order `m`,
uniformly for `z` near `z₀`, and at bounded frequencies the coefficient is uniformly continuous.
Combined with the continuity of quantization in the symbol, this makes `z ↦ Op(a(z))` continuous in
operator norm, as needed to integrate the operators along a contour.

## Main declarations

* `TauCeti.ParameterSymbol.exists_norm_mixedDeriv_coefficient_le`: the estimates of the mixed
  derivatives `∂ₓ^α ∂_ξ^β a((x, ξ), z)` at a fixed spectral parameter on a compact set of
  positions, uniformly on `Λ`.
* `TauCeti.ParameterSymbol.toSymbol`: the ordinary symbol of order `m` at a spectral parameter;
  it is linear in the symbol and commutes with the order inclusions and the composition.
* `TauCeti.ParameterSymbol.exists_seminorm_inclusion_toSymbol_le`: the decay of its seminorms of
  order `m' ∈ [m, 0]` in the spectral parameter.
* `TauCeti.ParameterSymbol.continuousOn_inclusion_toSymbol`: its continuity in the spectral
  parameter, in the topology of the symbols of any order `m' > m`.

## References

* M. A. Shubin, *Pseudodifferential Operators and Spectral Theory*, Chapter II, §9.
-/

public section

noncomputable section

open Set Filter
open scoped ContDiff Topology

namespace TauCeti

variable {n : ℕ}

namespace ParameterSymbol

variable {Λ : TopologicalSpace.Opens ℂ} {V W U : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [NormedAddCommGroup W] [NormedSpace ℂ W] [NormedAddCommGroup U] [NormedSpace ℂ U] {m m' : ℝ}

/-! ### Slices at a fixed spectral parameter -/

/-- At a spectral parameter outside `Λ` the coefficient vanishes in the position and the
frequency. -/
theorem coefficient_slice_of_notMem (a : ParameterSymbol n Λ V W m) {z : ℂ} (hz : z ∉ Λ) :
    (fun q : CoordinateSpace n × CoordinateSpace n => a.coefficient (q, z)) = 0 :=
  funext fun q => a.coefficient_of_notMem (q, z) hz

/-- At a fixed spectral parameter the coefficient is smooth in the position and the frequency. -/
theorem contDiff_coefficient_slice (a : ParameterSymbol n Λ V W m) (z : ℂ) :
    ContDiff ℝ ∞ fun q : CoordinateSpace n × CoordinateSpace n => a.coefficient (q, z) := by
  by_cases hz : z ∈ Λ
  · exact contDiff_iff_contDiffAt.2 fun q =>
      (a.contDiffAt_coefficient (p := (q, z)) hz).comp q (contDiff_prodMk_left z).contDiffAt
  · rw [a.coefficient_slice_of_notMem hz]
    exact contDiff_const

/-- In terms of the dilated derivatives defining the class, a mixed derivative `∂ₓ^α ∂_ξ^β` of
the coefficient takes `|β|` frequency directions, each the image under the dilation by the weight
`t` of a vector of norm `t⁻¹`. -/
private theorem norm_mixedDeriv_coefficient_le_aux (a : ParameterSymbol n Λ V W m)
    (α β : List (Fin n)) {x ξ : CoordinateSpace n} {z : ℂ} (hz : z ∈ Λ) :
    ‖mixedDeriv α β (fun q => a.coefficient (q, z)) x ξ‖ ≤
      ‖parameterIteratedFDeriv (α.length + β.length) a.coefficient ((x, ξ), z)‖ *
        (parameterWeight ξ z)⁻¹ ^ β.length := by
  set t := parameterWeight ξ z
  have ht : 0 < t := parameterWeight_pos ξ z
  -- The directions of the mixed derivative, and their preimages under the dilation.
  set d : Fin (α.length + β.length) → CoordinateSpace n × CoordinateSpace n :=
    Fin.append (fun i => (EuclideanSpace.single (α.get i) 1, 0))
      fun i => (0, EuclideanSpace.single (β.get i) 1)
  have hd : ∀ i, parameterDilation n t (((d i).1, t⁻¹ • (d i).2), 0) = ((d i), 0) := fun i => by
    simp [smul_smul, mul_inv_cancel₀ ht.ne']
  rw [mixedDeriv_eq_iteratedFDeriv_append α β
      ((a.contDiff_coefficient_slice z).of_le (by exact_mod_cast le_top)),
    (a.contDiffAt_coefficient (p := ((x, ξ), z)) hz).iteratedFDeriv_prod_left _
      (by exact_mod_cast le_top), ContinuousMultilinearMap.compContinuousLinearMap_apply]
  have heq : (iteratedFDeriv ℝ (α.length + β.length) a.coefficient ((x, ξ), z))
      (fun i => ContinuousLinearMap.inl ℝ _ ℂ (d i)) =
      parameterIteratedFDeriv (α.length + β.length) a.coefficient ((x, ξ), z)
        (fun i => (((d i).1, t⁻¹ • (d i).2), 0)) := by
    rw [parameterIteratedFDeriv_apply]
    simp only [hd, ContinuousLinearMap.inl_apply, t]
  rw [heq]
  refine (ContinuousMultilinearMap.le_opNorm _ _).trans_eq ?_
  congr 1
  -- A spatial direction has norm `1`, a rescaled frequency direction norm `t⁻¹`.
  simp [d, Fin.prod_univ_add, Prod.norm_def, norm_smul, abs_of_pos ht, ht.le]

/-- **Estimates at a fixed spectral parameter.** On a compact set of positions, the mixed
derivatives of a parameter-dependent symbol of order `m` in the position and the frequency satisfy
`‖∂ₓ^α ∂_ξ^β a((x, ξ), z)‖ ≤ C (1 + ‖ξ‖ + ‖z‖ ^ (1 / 2)) ^ (m - |β|)`, uniformly in the spectral
parameter `z ∈ Λ`. -/
theorem exists_norm_mixedDeriv_coefficient_le (a : ParameterSymbol n Λ V W m)
    {K : Set (CoordinateSpace n)} (hK : IsCompact K) (α β : List (Fin n)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ K, ∀ ξ, ∀ z ∈ Λ,
      ‖mixedDeriv α β (fun q => a.coefficient (q, z)) x ξ‖ ≤
        C * parameterWeight ξ z ^ (m - β.length) := by
  obtain ⟨C, hC, h⟩ := a.exists_bound K hK (α.length + β.length)
  refine ⟨C, hC, fun x hx ξ z hz => (a.norm_mixedDeriv_coefficient_le_aux α β hz).trans ?_⟩
  have ht := parameterWeight_pos ξ z
  calc _ ≤ C * parameterWeight ξ z ^ m * (parameterWeight ξ z)⁻¹ ^ β.length :=
        mul_le_mul_of_nonneg_right (h x hx ξ z hz) (by positivity)
    _ = C * parameterWeight ξ z ^ (m - β.length) := by
        rw [Real.rpow_sub ht, Real.rpow_natCast, inv_pow, div_eq_mul_inv, mul_assoc]

/-- **The symbol at a spectral parameter.** At a fixed spectral parameter `z`, a
parameter-dependent symbol of order `m` is the ordinary symbol `(x, ξ) ↦ a((x, ξ), z)` of order
`m`, its quantization being the operator `Op(a(z))` of the family. The constants of its estimates
depend on `z`; for `z ∉ Λ` it is `0`. -/
def toSymbol (a : ParameterSymbol n Λ V W m) (z : ℂ) : Symbol n V W m where
  coefficient q := a.coefficient (q, z)
  contDiff_coefficient := a.contDiff_coefficient_slice z
  exists_bound K hK α β := by
    by_cases hz : z ∈ Λ
    · obtain ⟨C, hC, h⟩ := a.exists_norm_mixedDeriv_coefficient_le hK α β
      refine ⟨C * (3 * (1 + ‖z‖)) ^ (|m - β.length| / 2), by positivity, fun x hx ξ => ?_⟩
      rw [mul_assoc]
      exact (h x hx ξ z hz).trans
        (mul_le_mul_of_nonneg_left (parameterWeight_rpow_le_mul_one_add_norm_sq_rpow ξ z _) hC)
    · refine ⟨0, le_rfl, fun x _ ξ => ?_⟩
      rw [a.coefficient_slice_of_notMem hz, mixedDeriv_zero, norm_zero, zero_mul]

@[simp]
theorem coefficient_toSymbol (a : ParameterSymbol n Λ V W m) (z : ℂ)
    (q : CoordinateSpace n × CoordinateSpace n) :
    (a.toSymbol z).coefficient q = a.coefficient (q, z) :=
  (rfl)

/-- Outside `Λ` the symbol at a spectral parameter is `0`. -/
theorem toSymbol_of_notMem (a : ParameterSymbol n Λ V W m) {z : ℂ} (hz : z ∉ Λ) :
    a.toSymbol z = 0 :=
  Symbol.ext (a.coefficient_slice_of_notMem hz)

@[simp]
theorem toSymbol_zero (z : ℂ) : (0 : ParameterSymbol n Λ V W m).toSymbol z = 0 :=
  (rfl)

@[simp]
theorem toSymbol_add (a b : ParameterSymbol n Λ V W m) (z : ℂ) :
    (a + b).toSymbol z = a.toSymbol z + b.toSymbol z :=
  (rfl)

@[simp]
theorem toSymbol_smul (c : ℂ) (a : ParameterSymbol n Λ V W m) (z : ℂ) :
    (c • a).toSymbol z = c • a.toSymbol z :=
  (rfl)

@[simp]
theorem toSymbol_neg (a : ParameterSymbol n Λ V W m) (z : ℂ) : (-a).toSymbol z = -a.toSymbol z :=
  Symbol.ext <| funext fun q => by simp

@[simp]
theorem toSymbol_sub (a b : ParameterSymbol n Λ V W m) (z : ℂ) :
    (a - b).toSymbol z = a.toSymbol z - b.toSymbol z :=
  Symbol.ext <| funext fun q => by simp

@[simp]
theorem toSymbol_nsmul (k : ℕ) (a : ParameterSymbol n Λ V W m) (z : ℂ) :
    (k • a).toSymbol z = k • a.toSymbol z :=
  Symbol.ext <| funext fun q => by simp

@[simp]
theorem toSymbol_zsmul (k : ℤ) (a : ParameterSymbol n Λ V W m) (z : ℂ) :
    (k • a).toSymbol z = k • a.toSymbol z :=
  Symbol.ext <| funext fun q => by simp

@[simp]
theorem toSymbol_sum {ι : Type*} (s : Finset ι) (a : ι → ParameterSymbol n Λ V W m) (z : ℂ) :
    (∑ i ∈ s, a i).toSymbol z = ∑ i ∈ s, (a i).toSymbol z :=
  map_sum (AddMonoidHom.mk' (toSymbol · z) (toSymbol_add · · z)) a s

/-- Evaluation at a spectral parameter commutes with the inclusion of orders. -/
@[simp]
theorem toSymbol_inclusion (h : m ≤ m') (a : ParameterSymbol n Λ V W m) (z : ℂ) :
    (inclusion h a).toSymbol z = Symbol.inclusion h (a.toSymbol z) :=
  Symbol.ext <| funext fun q => by simp

/-- Evaluation at a spectral parameter commutes with the pointwise composition. -/
@[simp]
theorem toSymbol_comp (b : ParameterSymbol n Λ W U m') (a : ParameterSymbol n Λ V W m) (z : ℂ) :
    (b.comp a).toSymbol z = (b.toSymbol z).comp (a.toSymbol z) :=
  Symbol.ext <| funext fun q => by simp

/-- At a spectral parameter in `Λ`, the symbol of a function of the position is the ordinary symbol
of that function. -/
@[simp]
theorem toSymbol_ofSpatial (f : CoordinateSpace n → V →L[ℂ] W) (hf : ContDiff ℝ ∞ f) {z : ℂ}
    (hz : z ∈ Λ) :
    (ofSpatial f hf : ParameterSymbol n Λ V W 0).toSymbol z = Symbol.ofSpatial f hf :=
  Symbol.ext <| funext fun q => by
    rw [coefficient_toSymbol, ← q.eta, coefficient_ofSpatial f hf _ _ hz,
      Symbol.coefficient_ofSpatial]

/-- If a parameter-dependent symbol vanishes, at a spectral parameter `z`, at the positions outside
a compact set `K` for every frequency, then its symbol at `z` has compact spatial support. -/
theorem hasCompactSpatialSupport_toSymbol (a : ParameterSymbol n Λ V W m) (z : ℂ)
    {K : Set (CoordinateSpace n)} (hK : IsCompact K)
    (ha : ∀ x ∉ K, ∀ ξ, a.coefficient ((x, ξ), z) = 0) :
    (a.toSymbol z).HasCompactSpatialSupport :=
  Symbol.hasCompactSpatialSupport_iff.2 ⟨K, hK, ha⟩

/-- **Decay in the spectral parameter.** For orders `m ≤ m' ≤ 0`, a parameter-dependent symbol of
order `m`, viewed at each spectral parameter as an ordinary symbol of order `m'`, has seminorms
`p_{K,α,β}(a(z)) ≤ C (1 + ‖z‖ ^ (1 / 2)) ^ (m - m')`, uniformly in `z ∈ Λ`. -/
theorem exists_seminorm_inclusion_toSymbol_le (a : ParameterSymbol n Λ V W m) (h : m ≤ m')
    (h' : m' ≤ 0) (K : TopologicalSpace.Compacts (CoordinateSpace n)) (α β : List (Fin n)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ Λ,
      Symbol.seminorm K α β (Symbol.inclusion h (a.toSymbol z)) ≤
        C * (1 + Real.sqrt ‖z‖) ^ (m - m') := by
  obtain ⟨C, hC, hb⟩ := a.exists_norm_mixedDeriv_coefficient_le K.isCompact α β
  refine ⟨C, hC, fun z hz => Symbol.seminorm_le_bound K α β _ (by positivity) fun x hx ξ => ?_⟩
  have ht := parameterWeight_pos ξ z
  have hβ : m' - β.length ≤ 0 := by linarith [(Nat.cast_nonneg β.length : (0 : ℝ) ≤ _)]
  rw [Symbol.coefficient_inclusion]
  calc _ ≤ C * parameterWeight ξ z ^ (m - β.length) := hb x hx ξ z hz
    _ = C * (parameterWeight ξ z ^ (m' - β.length) * parameterWeight ξ z ^ (m - m')) := by
        rw [← Real.rpow_add ht]
        ring_nf
    _ ≤ C * ((1 + ‖ξ‖ ^ 2) ^ ((m' - β.length) / 2) * (1 + Real.sqrt ‖z‖) ^ (m - m')) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul (parameterWeight_rpow_le_one_add_norm_sq_rpow ξ z hβ)
            (parameterWeight_rpow_le_one_add_sqrt_rpow ξ z (by linarith)) (by positivity)
            (by positivity)) hC
    _ = _ := by ring

/-! ### Continuity in the spectral parameter -/

/-- The mixed derivatives of the coefficient in the position and the frequency depend jointly
continuously on the spectral parameter in `Λ`, the position and the frequency. -/
private theorem continuousOn_mixedDeriv_coefficient (a : ParameterSymbol n Λ V W m)
    (α β : List (Fin n)) :
    ContinuousOn (fun p : ℂ × (CoordinateSpace n × CoordinateSpace n) =>
      mixedDeriv α β (fun q => a.coefficient (q, p.1)) p.2.1 p.2.2) ((Λ : Set ℂ) ×ˢ univ) := by
  have hN : ((mixedDirections α β).length : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast le_top
  refine fun p hp => ContinuousAt.continuousWithinAt ?_
  -- Near `p`, the mixed derivative is a derivative of the coefficient of order
  -- `|α| + |β|`, restricted to the position and frequency directions.
  have heq : (fun p : ℂ × (CoordinateSpace n × CoordinateSpace n) =>
      mixedDeriv α β (fun q => a.coefficient (q, p.1)) p.2.1 p.2.2) =ᶠ[𝓝 p]
      fun p => (ContinuousMultilinearMap.compContinuousLinearMapL
        (fun _ => ContinuousLinearMap.inl ℝ (CoordinateSpace n × CoordinateSpace n) ℂ)
        (iteratedFDeriv ℝ (mixedDirections α β).length a.coefficient (p.2, p.1)))
        fun i => (mixedDirections α β).get i := by
    filter_upwards [(Λ.isOpen.preimage continuous_fst).mem_nhds hp.1] with p hp'
    rw [mixedDeriv_eq_iteratedFDeriv α β ((a.contDiff_coefficient_slice p.1).of_le
      (by exact_mod_cast le_top)),
      (a.contDiffAt_coefficient (p := (p.2, p.1)) hp').iteratedFDeriv_prod_left _ hN]
    rfl
  refine ContinuousAt.congr ?_ heq.symm
  have hc : ContinuousAt (fun p : ℂ × (CoordinateSpace n × CoordinateSpace n) =>
      iteratedFDeriv ℝ (mixedDirections α β).length a.coefficient (p.2, p.1)) p :=
    ((a.contDiffAt_coefficient (p := (p.2, p.1)) hp.1).continuousAt_iteratedFDeriv hN).comp
      (f := Prod.swap) continuous_swap.continuousAt
  exact ((ContinuousMultilinearMap.apply ℝ _ _ _).continuous.comp
    (ContinuousMultilinearMap.compContinuousLinearMapL _).continuous).continuousAt.comp hc

/-- **High frequencies.** For `m < m'`, near a spectral parameter `z₀ ∈ Λ` the derivatives
`∂ₓ^α ∂_ξ^β a((x, ξ), z)` and `∂ₓ^α ∂_ξ^β a((x, ξ), z₀)` differ by at most `ε ⟨ξ⟩ ^ (m' - |β|)` at
the positions of a compact set and all large frequencies: each of them is bounded by a multiple of
`⟨ξ⟩ ^ (m - |β|)`, uniformly for `z` near `z₀`. -/
private theorem exists_eventually_norm_sub_mixedDeriv_le_of_le_norm (a : ParameterSymbol n Λ V W m)
    (h : m < m') {K : Set (CoordinateSpace n)} (hK : IsCompact K) (α β : List (Fin n)) {z₀ : ℂ}
    (hz₀ : z₀ ∈ Λ) {ε : ℝ} (hε : 0 < ε) :
    ∃ R : ℝ, ∀ᶠ z in 𝓝 z₀, ∀ x ∈ K, ∀ ξ : CoordinateSpace n, R ≤ ‖ξ‖ →
      ‖mixedDeriv α β (fun q => a.coefficient (q, z)) x ξ -
          mixedDeriv α β (fun q => a.coefficient (q, z₀)) x ξ‖ ≤
        ε * (1 + ‖ξ‖ ^ 2) ^ ((m' - β.length) / 2) := by
  set μ := m - β.length
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 Λ.isOpen z₀ hz₀
  obtain ⟨D, hD0, hD⟩ := a.exists_norm_mixedDeriv_coefficient_le hK α β
  set E := (3 * (1 + (‖z₀‖ + r))) ^ (|μ| / 2)
  -- On the ball around `z₀`, the derivatives are bounded by `D E ⟨ξ⟩ ^ μ`.
  have hbound : ∀ z ∈ Metric.ball z₀ r, ∀ x ∈ K, ∀ ξ,
      ‖mixedDeriv α β (fun q => a.coefficient (q, z)) x ξ‖ ≤
        D * E * (1 + ‖ξ‖ ^ 2) ^ (μ / 2) := fun z hz x hx ξ => by
    have hz' : ‖z‖ ≤ ‖z₀‖ + r := by
      have := norm_le_norm_add_norm_sub' z z₀
      rw [← dist_eq_norm] at this
      linarith [Metric.mem_ball.1 hz]
    refine (hD x hx ξ z (hball hz)).trans ?_
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ((parameterWeight_rpow_le_mul_one_add_norm_sq_rpow ξ z μ).trans
      (mul_le_mul_of_nonneg_right (Real.rpow_le_rpow (by positivity) (by linarith)
        (by positivity)) (by positivity))) hD0
  -- The factor `⟨ξ⟩ ^ (m - m')` tends to `0`.
  have ht : Tendsto (fun R : ℝ => 2 * (D * E) * (1 + R ^ 2) ^ ((m - m') / 2)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun R : ℝ => 1 + R ^ 2) atTop atTop :=
      tendsto_atTop_add_const_left _ _ (tendsto_pow_atTop two_ne_zero)
    have h2 := (tendsto_rpow_neg_atTop (y := (m' - m) / 2) (by linarith)).comp h1
    simpa [Function.comp_def, show -((m' - m) / 2) = (m - m') / 2 by ring] using
      h2.const_mul (2 * (D * E))
  obtain ⟨R, hR⟩ := eventually_atTop.1 (ht.eventually (ge_mem_nhds hε))
  refine ⟨R, ?_⟩
  filter_upwards [Metric.ball_mem_nhds z₀ hr] with z hzr x hx ξ hξ
  have hsplit : (1 + ‖ξ‖ ^ 2) ^ (μ / 2) =
      (1 + ‖ξ‖ ^ 2) ^ ((m' - β.length) / 2) * (1 + ‖ξ‖ ^ 2) ^ ((m - m') / 2) := by
    rw [← Real.rpow_add (by positivity)]
    congr 1
    simp only [μ]
    ring
  calc _ ≤ ‖mixedDeriv α β (fun q => a.coefficient (q, z)) x ξ‖ +
        ‖mixedDeriv α β (fun q => a.coefficient (q, z₀)) x ξ‖ := norm_sub_le _ _
    _ ≤ D * E * (1 + ‖ξ‖ ^ 2) ^ (μ / 2) + D * E * (1 + ‖ξ‖ ^ 2) ^ (μ / 2) :=
        add_le_add (hbound z hzr x hx ξ) (hbound z₀ (Metric.mem_ball_self hr) x hx ξ)
    _ = 2 * (D * E) * (1 + ‖ξ‖ ^ 2) ^ ((m - m') / 2) * (1 + ‖ξ‖ ^ 2) ^ ((m' - β.length) / 2) := by
        rw [hsplit]
        ring
    _ ≤ ε * (1 + ‖ξ‖ ^ 2) ^ ((m' - β.length) / 2) :=
        mul_le_mul_of_nonneg_right (hR ‖ξ‖ hξ) (by positivity)

/-- **Bounded frequencies.** Near a spectral parameter `z₀ ∈ Λ`, the derivatives
`∂ₓ^α ∂_ξ^β a((x, ξ), z)` and `∂ₓ^α ∂_ξ^β a((x, ξ), z₀)` differ by less than `ε ⟨ξ⟩ ^ r` at the
positions of a compact set and the frequencies of a ball, by uniform continuity on a compact set. -/
private theorem eventually_norm_sub_mixedDeriv_lt_of_norm_le (a : ParameterSymbol n Λ V W m)
    {K : Set (CoordinateSpace n)} (hK : IsCompact K) (α β : List (Fin n)) {z₀ : ℂ}
    (hz₀ : z₀ ∈ Λ) {ε : ℝ} (hε : 0 < ε) (r R : ℝ) :
    ∀ᶠ z in 𝓝 z₀, ∀ x ∈ K, ∀ ξ : CoordinateSpace n, ‖ξ‖ ≤ R →
      ‖mixedDeriv α β (fun q => a.coefficient (q, z)) x ξ -
          mixedDeriv α β (fun q => a.coefficient (q, z₀)) x ξ‖ < ε * (1 + ‖ξ‖ ^ 2) ^ r := by
  -- The derivatives divided by `⟨ξ⟩ ^ (2 r)` are jointly continuous.
  set G : ℂ → CoordinateSpace n × CoordinateSpace n → V →L[ℂ] W :=
    fun z q => ((1 + ‖q.2‖ ^ 2) ^ r)⁻¹ • mixedDeriv α β (fun q => a.coefficient (q, z)) q.1 q.2
  have hG : ContinuousOn (Function.uncurry G) ((Λ : Set ℂ) ×ˢ (K ×ˢ Metric.closedBall 0 R)) := by
    have hw : ContinuousOn (fun p : ℂ × (CoordinateSpace n × CoordinateSpace n) =>
        ((1 + ‖p.2.2‖ ^ 2) ^ r)⁻¹) univ :=
      ((Continuous.rpow_const (by fun_prop) fun _ => Or.inl (by positivity)).continuousOn).inv₀
        fun _ _ => (by positivity)
    exact (hw.mono (subset_univ _)).smul ((a.continuousOn_mixedDeriv_coefficient α β).mono
      (prod_mono le_rfl (subset_univ _)))
  obtain ⟨v, hv, hvG⟩ := (hK.prod (isCompact_closedBall 0 R)).mem_uniformity_of_prod hG hz₀
    (Metric.dist_mem_uniformity hε)
  rw [Λ.isOpen.nhdsWithin_eq hz₀] at hv
  filter_upwards [hv] with z hzv x hx ξ hξ
  have hw : 0 < (1 + ‖ξ‖ ^ 2) ^ r := by positivity
  have h' := hvG z hzv (x, ξ) ⟨hx, mem_closedBall_zero_iff.2 hξ⟩
  rw [Set.mem_ofPred_eq, dist_eq_norm] at h'
  have h'' : ((1 + ‖ξ‖ ^ 2) ^ r)⁻¹ * ‖mixedDeriv α β (fun q => a.coefficient (q, z)) x ξ -
      mixedDeriv α β (fun q => a.coefficient (q, z₀)) x ξ‖ < ε := by
    simpa only [G, ← smul_sub, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hw.le)] using h'
  rwa [inv_mul_lt_iff₀ hw, mul_comm] at h''

/-- **Continuity in the spectral parameter.** For `m < m'`, the symbols `a(z)` of a
parameter-dependent symbol of order `m` at the spectral parameters `z ∈ Λ`, viewed as symbols of
order `m'`, depend continuously on `z` in the topology of `S^{m'}`. -/
theorem continuousOn_inclusion_toSymbol (a : ParameterSymbol n Λ V W m) (h : m < m') :
    ContinuousOn (fun z => Symbol.inclusion h.le (a.toSymbol z)) Λ := by
  refine fun z₀ hz₀ => ContinuousAt.continuousWithinAt ?_
  rw [ContinuousAt, Symbol.withSeminorms.tendsto_nhds]
  rintro ⟨K, α, β⟩ ε hε
  rw [Symbol.seminormFamily_apply]
  -- Split the frequencies at a radius `R` beyond which the order gap makes both terms small.
  obtain ⟨R, hR⟩ := a.exists_eventually_norm_sub_mixedDeriv_le_of_le_norm h K.isCompact α β hz₀
    (half_pos hε)
  filter_upwards [hR, a.eventually_norm_sub_mixedDeriv_lt_of_norm_le K.isCompact α β hz₀
    (half_pos hε) ((m' - β.length) / 2) R] with z hzR hzr
  refine (Symbol.seminorm_le_bound K α β _ (half_pos hε).le fun x hx ξ => ?_).trans_lt
    (half_lt_self hε)
  have hneg : ContDiff ℝ ∞ (-(Symbol.inclusion h.le (a.toSymbol z₀)).coefficient) :=
    (Symbol.contDiff_coefficient _).neg
  have hc (w : ℂ) : (Symbol.inclusion h.le (a.toSymbol w)).coefficient =
      fun q => a.coefficient (q, w) := funext fun q => by simp
  rw [Symbol.coefficient_sub, sub_eq_add_neg, mixedDeriv_add (Symbol.contDiff_coefficient _) hneg,
    mixedDeriv_neg, ← sub_eq_add_neg, hc, hc]
  rcases le_or_gt R ‖ξ‖ with hξ | hξ
  · exact hzR x hx ξ hξ
  · exact (hzr x hx ξ hξ.le).le

end ParameterSymbol

end TauCeti
