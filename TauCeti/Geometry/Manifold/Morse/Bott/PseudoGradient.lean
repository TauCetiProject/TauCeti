/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Geometry.Manifold.IntegralCurve.Basic
public import TauCeti.Geometry.Manifold.Morse.Bott.Chart.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
import TauCeti.Geometry.Manifold.IntegralCurve.Monotone
import TauCeti.Geometry.Manifold.MFDeriv.Chart.Basic
import TauCeti.Geometry.Manifold.MFDeriv.Curve
import TauCeti.Geometry.Manifold.MFDeriv.ModelChart
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# Pseudo-gradient fields adapted to a Morse–Bott function

Let `f` be a real function on a boundaryless smooth manifold `M` modelled on a finite-dimensional
real normed space `E`. A vector field `X` on `M` is a **pseudo-gradient field adapted to `f` in the
Morse–Bott sense** (`TauCeti.IsBottAdaptedPseudoGradient`) when

* `X` is smooth;
* `f` strictly decreases along `X` away from the critical points: `df(X) < 0` wherever `df ≠ 0`;
* near each critical point `x` there is a Morse–Bott chart (`TauCeti.MorseBottChart`) in which
  `X` is the negative gradient of the normal form: if `f = f x + (1/2) Σᵢ wᵢ zᵢ²` in the
  coordinates `z = L (ψ y)`, with weights `wᵢ ∈ {-1, 0, 1}`, then `X` reads `z ↦ (-wᵢ zᵢ)ᵢ`.

These are the standard normal fields of Morse–Bott theory. Near a critical point, in the
coordinates of the chart, the flow of `X` is the linear flow `z ↦ (e^{-wᵢ t} zᵢ)ᵢ`
(`TauCeti.MorseBottChart.isMIntegralCurveOn_toChart_symm_linearFlow`): it fixes the coordinates of
weight `0`, which run along the critical submanifold
(`TauCeti.MorseBottChart.linearFlow_of_weight_eq_zero`), and is linear in the normal
coordinates, expanding those of weight `-1` and contracting those of weight `1`. So each point of
the critical submanifold is fixed (`TauCeti.MorseBottChart.linearFlow_eq_self`), and nearby orbits
move in the coordinate slice through it on which the weight-zero coordinates are constant. For a
Morse function the weights are all nonzero, and an adapted pseudo-gradient in the sense of Audin
and Damian (`TauCeti.IsAdaptedPseudoGradient`) is adapted in the Morse–Bott sense
(`TauCeti.IsAdaptedPseudoGradient.isBottAdaptedPseudoGradient`, in
`TauCeti.Geometry.Manifold.Morse.PseudoGradient.Basic`); the linear flow of a Morse chart and the
basic properties of Morse pseudo-gradients are the ones proved here.

## Main declarations

* `TauCeti.IsBottAdaptedPseudoGradient`: the definition.
* `TauCeti.IsBottAdaptedPseudoGradient.eq_zero_iff`: the zeros of an adapted pseudo-gradient are
  exactly the critical points of `f`.
* `TauCeti.IsBottAdaptedPseudoGradient.neg`: `-X` is adapted to `-f`.
* `TauCeti.IsBottAdaptedPseudoGradient.strictAnti_comp`: `f` is strictly antitone along an integral
  curve that never meets a critical point.
* `TauCeti.IsBottAdaptedPseudoGradient.mdifferentiable` and
  `TauCeti.IsBottAdaptedPseudoGradient.antitone_comp`: `f` is differentiable, and antitone along
  every integral curve.
* `TauCeti.MorseBottChart.linearFlow`: the linear flow in the coordinates of a Morse–Bott chart,
  with its flow law `TauCeti.MorseBottChart.linearFlow_add`.
* `TauCeti.MorseBottChart.isMIntegralCurveOn_toChart_symm_linearFlow`: when `X` is linear in the
  chart, the linear orbit read on the manifold is an integral curve of `X`.

## References

* M. Hutchings, *Lecture notes on Morse homology (with an eye towards Floer theory and
  pseudoholomorphic curves)*, 2002, Section 6.2 (Morse–Bott functions and their gradient flows).
* A. Banyaga and D. E. Hurtubise, *Lectures on Morse Homology*, Kluwer, 2004, Section 3.5
  (Morse–Bott functions).
* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Definition 2.2.1 (pseudo-gradient fields adapted to a Morse function).
-/

public section

open Function Set
open scoped ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  {f : M → ℝ} {x : M} {X : (x : M) → TangentSpace 𝓘(ℝ, E) x} {γ : ℝ → M}

namespace MorseBottChart

variable (φ : MorseBottChart E f x)

/-- In a Morse–Bott chart for `f` in which `X` is the linear field `z ↦ (-wᵢ zᵢ)ᵢ`, the reversed
field `-X` is the linear field of the negated chart for `-f`. -/
theorem coord_mfderiv_neg
    (hφ : ∀ y ∈ φ.toChart.source, φ.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ.toChart y (X y)) =
      fun i ↦ -(φ.weight i * φ.coord (φ.toChart y) i)) :
    ∀ y ∈ φ.neg.toChart.source,
      φ.neg.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ.neg.toChart y ((-X) y)) =
        fun i ↦ -(φ.neg.weight i * φ.neg.coord (φ.neg.toChart y) i) := by
  intro y hy
  rw [neg_toChart] at hy
  rw [neg_coord, neg_toChart, neg_weight, Pi.neg_apply, map_neg]
  refine (φ.coord.map_neg _).trans ((congrArg Neg.neg (hφ y hy)).trans ?_)
  ext i
  simp

/-- The linear flow `z ↦ (e^{-wᵢ t} zᵢ)ᵢ` of the negative gradient of the quadratic normal form, in
the coordinates of a Morse–Bott chart. -/
noncomputable def linearFlow (t : ℝ) (z : Fin (Module.finrank ℝ E) → ℝ) :
    Fin (Module.finrank ℝ E) → ℝ :=
  fun i ↦ Real.exp (-(φ.weight i * t)) * z i

/-- The coordinates of the linear flow. -/
@[simp]
theorem linearFlow_apply (t : ℝ) (z : Fin (Module.finrank ℝ E) → ℝ)
    (i : Fin (Module.finrank ℝ E)) :
    φ.linearFlow t z i = Real.exp (-(φ.weight i * t)) * z i := by
  rw [linearFlow]

/-- At time zero the linear flow is the identity. -/
@[simp]
theorem linearFlow_zero (z : Fin (Module.finrank ℝ E) → ℝ) : φ.linearFlow 0 z = z := by
  ext i
  simp

/-- The flow law of the linear flow. -/
theorem linearFlow_add (s t : ℝ) (z : Fin (Module.finrank ℝ E) → ℝ) :
    φ.linearFlow (s + t) z = φ.linearFlow s (φ.linearFlow t z) := by
  ext i
  simp only [linearFlow_apply, ← mul_assoc, ← Real.exp_add]
  ring_nf

/-- The linear flow fixes the origin. -/
@[simp]
theorem linearFlow_zero_right (t : ℝ) : φ.linearFlow t 0 = 0 := by
  ext i
  simp

/-- The linear flow is linear in the coordinates. -/
theorem linearFlow_add_right (t : ℝ) (z z' : Fin (Module.finrank ℝ E) → ℝ) :
    φ.linearFlow t (z + z') = φ.linearFlow t z + φ.linearFlow t z' := by
  ext i
  simp only [linearFlow_apply, Pi.add_apply]
  ring

/-- The linear flow commutes with scalar multiplication. -/
theorem linearFlow_smul (t a : ℝ) (z : Fin (Module.finrank ℝ E) → ℝ) :
    φ.linearFlow t (a • z) = a • φ.linearFlow t z := by
  ext i
  simp only [linearFlow_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- **The linear flow fixes the coordinates along the critical set**: a coordinate of weight `0`
does not move. -/
theorem linearFlow_of_weight_eq_zero {i : Fin (Module.finrank ℝ E)} (hi : φ.weight i = 0)
    (t : ℝ) (z : Fin (Module.finrank ℝ E) → ℝ) : φ.linearFlow t z i = z i := by
  rw [linearFlow_apply, hi, zero_mul, neg_zero, Real.exp_zero, one_mul]

/-- A coordinate of weight `1` decays like `e^{-t}`. -/
theorem linearFlow_of_weight_eq_one {i : Fin (Module.finrank ℝ E)} (hi : φ.weight i = 1) (t : ℝ)
    (z : Fin (Module.finrank ℝ E) → ℝ) : φ.linearFlow t z i = Real.exp (-t) * z i := by
  rw [linearFlow_apply, hi, one_mul]

/-- The linear flow multiplies the coordinate vector of a coordinate of weight `1` by `e^{-t}`. -/
theorem linearFlow_single_of_weight_eq_one {j : Fin (Module.finrank ℝ E)} (hj : φ.weight j = 1)
    (t : ℝ) : φ.linearFlow t (Pi.single j 1) = Real.exp (-t) • Pi.single j 1 := by
  funext i
  rw [linearFlow_apply, Pi.smul_apply, smul_eq_mul]
  by_cases hi : i = j
  · subst hi
    rw [hj, one_mul]
  · simp [hi]

/-- A coordinate of weight `-1` grows like `e^{t}`. -/
theorem linearFlow_of_weight_eq_neg_one {i : Fin (Module.finrank ℝ E)} (hi : φ.weight i = -1)
    (t : ℝ) (z : Fin (Module.finrank ℝ E) → ℝ) : φ.linearFlow t z i = Real.exp t * z i := by
  rw [linearFlow_apply, hi, neg_one_mul, neg_neg]

/-- For times `t > -log 2`, a coordinate of positive weight grows at most by a factor `2`. -/
theorem norm_linearFlow_lt_of_weight_eq_one {r : ℝ} {z : Fin (Module.finrank ℝ E) → ℝ}
    (hz : ‖z‖ < r / 2) {i : Fin (Module.finrank ℝ E)} (hi : φ.weight i = 1) {t : ℝ}
    (ht : -Real.log 2 < t) : ‖φ.linearFlow t z i‖ < r := by
  have hexp : Real.exp (-t) < 2 := by
    rw [← Real.exp_log two_pos]
    exact Real.exp_lt_exp.2 (by linarith)
  rw [φ.linearFlow_of_weight_eq_one hi, norm_mul, Real.norm_of_nonneg (Real.exp_pos _).le]
  calc Real.exp (-t) * ‖z i‖ ≤ 2 * ‖z‖ := by
        gcongr
        · exact norm_le_pi_norm z i
    _ < r := by linarith

/-- **The linear orbit stays in the `r`-cube.** If `‖z‖ < r / 2`, then at a time `t > -log 2` at
which every coordinate of negative weight still has size less than `r`, the linear flow of `z` lies
in the open `r`-cube. -/
theorem norm_linearFlow_lt {r : ℝ} {z : Fin (Module.finrank ℝ E) → ℝ} (hz : ‖z‖ < r / 2) {t : ℝ}
    (ht : -Real.log 2 < t) (hneg : ∀ i, φ.weight i < 0 → Real.exp t * |z i| < r) :
    ‖φ.linearFlow t z‖ < r := by
  refine (pi_norm_lt_iff (by linarith [norm_nonneg z])).2 fun i ↦ ?_
  rcases φ.weight_eq_neg_one_or_eq_zero_or_eq_one i with hi | hi | hi
  · rw [φ.linearFlow_of_weight_eq_neg_one hi, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
    exact hneg i (by rw [hi]; norm_num)
  · rw [φ.linearFlow_of_weight_eq_zero hi]
    exact (norm_le_pi_norm z i).trans_lt (by linarith [norm_nonneg z])
  · exact φ.norm_linearFlow_lt_of_weight_eq_one hz hi ht

/-- **The quadratic normal form at the exit time.** If every coordinate of `z` has size at most
`ε` and, at a time `T ≥ 0`, the linear flow has grown a coordinate `j` of negative weight to size
`c`, then `Σᵢ wᵢ (e^{-wᵢ T} zᵢ)² ≤ n ε² - c²`, where `n` is the dimension. -/
theorem sum_weight_mul_linearFlow_sq_le {z : Fin (Module.finrank ℝ E) → ℝ} {ε c T : ℝ}
    (hz : ∀ i, |z i| ≤ ε) {j : Fin (Module.finrank ℝ E)} (hj : φ.weight j = -1) (hT : 0 ≤ T)
    (hc : Real.exp T * |z j| = c) :
    ∑ i, φ.weight i * φ.linearFlow T z i ^ 2 ≤ Module.finrank ℝ E * ε ^ 2 - c ^ 2 := by
  -- Every coordinate contributes at most `ε²`, except `j`, which contributes `-c²`.
  have hsum : ∑ i, φ.weight i * φ.linearFlow T z i ^ 2 ≤
      ∑ i, (ε ^ 2 + if i = j then -c ^ 2 - ε ^ 2 else 0) := by
    refine Finset.sum_le_sum fun i _ ↦ ?_
    split_ifs with hij
    · subst hij
      have hci : φ.linearFlow T z i ^ 2 = c ^ 2 := by
        rw [φ.linearFlow_of_weight_eq_neg_one hj, ← hc, ← sq_abs, abs_mul,
          abs_of_pos (Real.exp_pos T)]
      rw [hj, hci]
      linarith
    · rcases φ.weight_eq_neg_one_or_eq_zero_or_eq_one i with hi | hi | hi
      · rw [hi]
        nlinarith [sq_nonneg (φ.linearFlow T z i), sq_nonneg ε]
      · rw [hi, zero_mul, add_zero]
        exact sq_nonneg ε
      · rw [hi, one_mul, φ.linearFlow_of_weight_eq_one hi, mul_pow, add_zero]
        have hexp1 : Real.exp (-T) ^ 2 ≤ 1 := by
          rw [← Real.exp_natCast_mul, Real.exp_le_one_iff]; push_cast; linarith
        have hzi2 : z i ^ 2 ≤ ε ^ 2 := by
          rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hz i) 2
        nlinarith [sq_nonneg (z i), sq_nonneg (Real.exp (-T))]
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, nsmul_eq_mul] at hsum
  linarith [sq_nonneg ε]

open Filter Topology in
/-- **The linear flow on the stable slice converges.** If the coordinates of negative weight of `z`
vanish, the linear flow of `z` converges, as `t → ∞`, to the projection of `z` onto the coordinates
of weight `0`: those coordinates do not move, and the coordinates of positive weight decay like
`e^{-t}`. -/
theorem tendsto_linearFlow_atTop {z : Fin (Module.finrank ℝ E) → ℝ}
    (hu : ∀ i, φ.weight i < 0 → z i = 0) :
    Tendsto (fun t ↦ φ.linearFlow t z) atTop (𝓝 fun i ↦ if φ.weight i = 0 then z i else 0) := by
  refine tendsto_pi_nhds.2 fun i ↦ ?_
  rcases φ.weight_eq_neg_one_or_eq_zero_or_eq_one i with hi | hi | hi
  · have hzi : z i = 0 := hu i (by rw [hi]; norm_num)
    simp only [φ.linearFlow_of_weight_eq_neg_one hi, hzi, mul_zero, ite_self]
    exact tendsto_const_nhds
  · simp only [φ.linearFlow_of_weight_eq_zero hi, hi, ↓reduceIte]
    exact tendsto_const_nhds
  · simp only [φ.linearFlow_of_weight_eq_one hi, hi, one_ne_zero, ↓reduceIte]
    simpa using Real.tendsto_exp_neg_atTop_nhds_zero.mul_const (z i)

/-- **The linear flow fixes the critical points of the normal form**, the points whose coordinates
of nonzero weight vanish. -/
theorem linearFlow_eq_self {z : Fin (Module.finrank ℝ E) → ℝ} (hz : ∀ i, φ.weight i ≠ 0 → z i = 0)
    (t : ℝ) : φ.linearFlow t z = z := by
  ext i
  by_cases hi : φ.weight i = 0
  · exact φ.linearFlow_of_weight_eq_zero hi t z
  · rw [linearFlow_apply, hz i hi, mul_zero]

/-- The linear flow of the negated Morse–Bott chart runs the linear flow backwards. -/
theorem neg_linearFlow (t : ℝ) (z : Fin (Module.finrank ℝ E) → ℝ) :
    φ.neg.linearFlow t z = φ.linearFlow (-t) z := by
  ext i
  simp only [linearFlow_apply, neg_weight, Pi.neg_apply]
  ring_nf

/-- The linear flow is jointly continuous in the coordinates and the time. -/
theorem continuous_linearFlow_uncurry :
    Continuous fun p : (Fin (Module.finrank ℝ E) → ℝ) × ℝ ↦ φ.linearFlow p.2 p.1 := by
  refine continuous_pi fun i ↦ ?_
  simp only [linearFlow_apply]
  fun_prop

/-- The linear flow solves the ODE `z' = (-wᵢ zᵢ)ᵢ`. -/
theorem hasDerivAt_linearFlow (z : Fin (Module.finrank ℝ E) → ℝ) (t : ℝ) :
    HasDerivAt (fun t ↦ φ.linearFlow t z) (fun i ↦ -(φ.weight i * φ.linearFlow t z i)) t := by
  refine hasDerivAt_pi.2 fun i ↦ ?_
  simp only [linearFlow_apply]
  convert ((((hasDerivAt_id' t).const_mul (φ.weight i)).neg.exp).mul_const (z i)) using 1
  simp only [Pi.neg_apply]
  ring

/-- **The linear orbit is an integral curve.** If `X` is the linear field `z ↦ (-wᵢ zᵢ)ᵢ` in the
Morse–Bott chart `φ` and the linear orbit of `z` stays in the chart for times in `s`, then the
linear orbit, read on the manifold, is an integral curve of `X` on `s`. -/
theorem isMIntegralCurveOn_toChart_symm_linearFlow
    (hφ : ∀ y ∈ φ.toChart.source, φ.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ.toChart y (X y)) =
      fun i ↦ -(φ.weight i * φ.coord (φ.toChart y) i))
    {z : Fin (Module.finrank ℝ E) → ℝ} {s : Set ℝ}
    (hz : ∀ t ∈ s, φ.coord.symm (φ.linearFlow t z) ∈ φ.toChart.target) :
    IsMIntegralCurveOn (fun t ↦ φ.toChart.symm (φ.coord.symm (φ.linearFlow t z))) X s := by
  have := φ.finiteDimensional
  set ℓ : ℝ → E := fun t ↦ φ.coord.symm (φ.linearFlow t z)
  have hℓd (t : ℝ) :
      HasDerivAt ℓ (φ.coord.symm fun i ↦ -(φ.weight i * φ.linearFlow t z i)) t := by
    simpa [ℓ, Function.comp_def] using
      φ.coordL.symm.hasFDerivAt.comp_hasDerivAt t (φ.hasDerivAt_linearFlow z t)
  have hmd : φ.toChart.MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ, E) :=
    mdifferentiable_of_mem_maximalAtlas φ.mem_maximalAtlas_one
  intro t ht
  have htT : ℓ t ∈ φ.toChart.target := hz t ht
  have hy : φ.toChart.symm (ℓ t) ∈ φ.toChart.source := φ.toChart.map_target htT
  have hψy : φ.toChart (φ.toChart.symm (ℓ t)) = ℓ t := φ.toChart.right_inv htT
  have h1 : HasMFDerivAt 𝓘(ℝ) 𝓘(ℝ, E) ℓ t ((1 : ℝ →L[ℝ] ℝ).smulRight
      (φ.coord.symm fun i ↦ -(φ.weight i * φ.linearFlow t z i))) :=
    hasMFDerivAt_iff_hasFDerivAt.2 (hℓd t).hasFDerivAt
  have h2 := (hmd.mdifferentiableAt_symm htT).hasMFDerivAt
  refine ((h2.comp t h1).hasMFDerivWithinAt).congr_mfderiv ?_
  refine ContinuousLinearMap.ext_ring ?_
  have hXy : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ.toChart (φ.toChart.symm (ℓ t))
      (X (φ.toChart.symm (ℓ t))) = φ.coord.symm fun i ↦ -(φ.weight i * φ.linearFlow t z i) := by
    apply φ.coord.injective
    rw [hφ _ hy, hψy, LinearEquiv.apply_symm_apply]
    simp
  have hinv := congr($(hmd.symm_comp_deriv hy) (X (φ.toChart.symm (ℓ t))))
  rw [ContinuousLinearMap.comp_apply, hXy, hψy, ContinuousLinearMap.id_apply] at hinv
  -- Both sides are `smulRight 1 v` applied to `1`. The domain of these maps is
  -- `TangentSpace 𝓘(ℝ) t`, whose topology is not syntactically that of `ℝ`, so
  -- `ContinuousLinearMap.comp_apply` and `ContinuousLinearMap.smulRight_apply` do not rewrite
  -- here; both sides are `1 • v` by definition.
  change mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ.toChart.symm (ℓ t)
      ((1 : ℝ) • φ.coord.symm fun i ↦ -(φ.weight i * φ.linearFlow t z i)) =
    (1 : ℝ) • X (φ.toChart.symm (ℓ t))
  rw [one_smul, one_smul]
  exact hinv

end MorseBottChart

variable [IsManifold 𝓘(ℝ, E) ∞ M]

/-- A vector field `X` is a **pseudo-gradient field adapted to `f` in the Morse–Bott sense** when it
is smooth, `f` strictly decreases along it away from the critical points (`d f_x (X x) < 0`, with
the differential read in `ℝ` through `mvfderiv`), and near each critical point there is a Morse–Bott
chart in which it is the negative gradient `z ↦ (-wᵢ zᵢ)ᵢ` of the normal form
`(1/2) Σᵢ wᵢ zᵢ²`. -/
structure IsBottAdaptedPseudoGradient (f : M → ℝ) (X : (x : M) → TangentSpace 𝓘(ℝ, E) x) :
    Prop where
  contMDiff : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E).tangent ∞
    (fun x ↦ (⟨x, X x⟩ : TangentBundle 𝓘(ℝ, E) M))
  mvfderiv_apply_lt_zero : ∀ x, mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f x ≠ 0 → mvfderiv 𝓘(ℝ, E) f x (X x) < 0
  exists_morseBottChart : ∀ x, mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f x = 0 →
    ∃ φ : MorseBottChart E f x, ∀ y ∈ φ.toChart.source,
      φ.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ.toChart y (X y)) =
        fun i ↦ -(φ.weight i * φ.coord (φ.toChart y) i)

namespace IsBottAdaptedPseudoGradient

/-- `f` does not increase along an adapted pseudo-gradient: `d f_x (X x) ≤ 0` everywhere. -/
theorem mvfderiv_apply_nonpos (hX : IsBottAdaptedPseudoGradient f X) (x : M) :
    mvfderiv 𝓘(ℝ, E) f x (X x) ≤ 0 := by
  by_cases hx : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f x = 0
  · simp [mvfderiv, hx]
  · exact (hX.mvfderiv_apply_lt_zero x hx).le

/-- An adapted pseudo-gradient does not vanish at a regular point of `f`. -/
theorem ne_zero_of_mfderiv_ne_zero (hX : IsBottAdaptedPseudoGradient f X) {x : M}
    (hx : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f x ≠ 0) : X x ≠ 0 := by
  intro h0
  have := hX.mvfderiv_apply_lt_zero x hx
  rw [h0, map_zero] at this
  exact lt_irrefl _ this

/-- An adapted pseudo-gradient vanishes at every critical point of `f`: in the Morse–Bott chart
centred there it is the linear field `z ↦ (-wᵢ zᵢ)ᵢ`, which vanishes at the centre. -/
theorem eq_zero_of_mfderiv_eq_zero (hX : IsBottAdaptedPseudoGradient f X) {x : M}
    (hx : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f x = 0) : X x = 0 := by
  obtain ⟨φ, hφ⟩ := hX.exists_morseBottChart x hx
  have h := hφ x φ.mem_source
  rw [φ.apply_self, map_zero] at h
  simp only [Pi.zero_apply, mul_zero, neg_zero] at h
  have h0 : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ.toChart x (X x) = 0 := φ.coord.map_eq_zero_iff.1 h
  have hinv := isInvertible_mfderiv_chart φ.mem_maximalAtlas_one φ.mem_source
  rw [← hinv.inverse_apply_self (X x), h0, map_zero]

/-- **The zeros of an adapted pseudo-gradient are the critical points of `f`.** -/
theorem eq_zero_iff (hX : IsBottAdaptedPseudoGradient f X) {x : M} :
    X x = 0 ↔ mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f x = 0 :=
  ⟨fun h ↦ by_contra fun hx ↦ hX.ne_zero_of_mfderiv_ne_zero hx h, hX.eq_zero_of_mfderiv_eq_zero⟩

/-- **`f` is strictly antitone along an integral curve of an adapted pseudo-gradient** that never
meets a critical point. Differentiability of `f` along the curve is automatic, since `mfderiv`
vanishes where `f` is not differentiable. -/
theorem strictAnti_comp (hX : IsBottAdaptedPseudoGradient f X) (hγ : IsMIntegralCurve γ X)
    (hcrit : ∀ t, mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f (γ t) ≠ 0) : StrictAnti (f ∘ γ) :=
  strictAnti_of_hasDerivAt_neg
    (fun t ↦ Manifold.hasDerivAt_comp_curve
      (by_contra fun h ↦ hcrit t (mfderiv_zero_of_not_mdifferentiableAt h)) (hγ t))
    fun t ↦ hX.mvfderiv_apply_lt_zero _ (hcrit t)

/-- **`f` is differentiable.** If `X` is adapted to `f` in the Morse–Bott sense, then `f` is
differentiable; this need not be assumed separately. -/
theorem mdifferentiable (hX : IsBottAdaptedPseudoGradient f X) : MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ) f :=
  fun p ↦ by
  -- Where `mfderiv` is nonzero, `f` is differentiable by definition of `mfderiv`; a zero of the
  -- derivative has a Morse–Bott chart, in which `f` is the smooth quadratic normal form.
  by_contra hd
  obtain ⟨φ, -⟩ := hX.exists_morseBottChart p (mfderiv_zero_of_not_mdifferentiableAt hd)
  exact hd ((φ.contMDiffAt φ.mem_source).mdifferentiableAt (by simp))

/-- **`f` is antitone along every integral curve of an adapted pseudo-gradient.** -/
theorem antitone_comp (hX : IsBottAdaptedPseudoGradient f X) (hγ : IsMIntegralCurve γ X) :
    Antitone (f ∘ γ) :=
  hγ.antitone_comp (fun t ↦ hX.mdifferentiable (γ t)) fun t ↦ hX.mvfderiv_apply_nonpos (γ t)

/-- **Reversing a pseudo-gradient.** If `X` is adapted to `f` in the Morse–Bott sense, then `-X`
is adapted to `-f`. -/
theorem neg (hX : IsBottAdaptedPseudoGradient f X) : IsBottAdaptedPseudoGradient (-f) (-X) where
  contMDiff := ContMDiff.neg_section hX.contMDiff
  mvfderiv_apply_lt_zero y hy := by
    have hy' : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f y ≠ 0 := fun h ↦ hy (mfderiv_neg_eq_zero_iff.2 h)
    rw [mvfderiv_neg, Pi.neg_apply, neg_apply, map_neg, neg_neg]
    exact hX.mvfderiv_apply_lt_zero y hy'
  exists_morseBottChart y hy := by
    obtain ⟨φ, hφ⟩ := hX.exists_morseBottChart y (mfderiv_neg_eq_zero_iff.1 hy)
    exact ⟨φ.neg, φ.coord_mfderiv_neg hφ⟩

end IsBottAdaptedPseudoGradient

end TauCeti
