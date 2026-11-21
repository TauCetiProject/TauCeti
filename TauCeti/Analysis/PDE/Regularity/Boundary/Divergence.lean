/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Regularity.Boundary.Oscillation
import TauCeti.Analysis.PDE.Ellipticity.Extension
import TauCeti.Analysis.PDE.Regularity.Inhomogeneous
import TauCeti.MeasureTheory.Measure.Haar.NormedSpace
import TauCeti.MeasureTheory.Measure.OpenPos
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# De Giorgi's oscillation decay at the boundary with a divergence datum

Let `a` be measurable and uniformly elliptic on an open set `Ω ⊆ ℝⁿ` with constants
`0 < λ ≤ Λ`, let `F ∈ L^q(Ω; ℝⁿ)` with `q > 2` and `q > n`, and let `u ∈ H¹(Ω)` be a weak
subsolution of

`-∂ᵢ(aⁱʲ ∂ⱼu) ≤ ∂ᵢFⁱ` in `Ω`,

meaning `a(u, v) ≤ -∫_Ω ⟪F, ∇v⟫` for every nonnegative `v ∈ H¹₀(Ω)`, with `u ≤ 0` on `∂Ω` in the
sense that `u⁺ ∈ H¹₀(Ω)`. Nothing is assumed about the regularity of `∂Ω`. This file proves
De Giorgi's estimate at boundary points with this divergence datum: if the complement of `Ω` fills
a fixed proportion `θ > 0` of `B(x₀, R)`, then

`u ≤ (1 - δ) M + K R^(1 - n/q) ‖F‖_{L^q(Ω ∩ B(x₀, 2R))} / λ` on `Ω ∩ B(x₀, R/2)`

whenever `u ≤ M` on `Ω ∩ B(x₀, 2R)`, and if the complement fills that proportion of every ball
`B(x₀, r)`, `r ≤ R`, the supremum decays like a power of the radius,

`u ≤ C (ρ/R)^α (M + R^(1 - n/q) ‖F‖_{L^q(Ω ∩ B(x₀, R))} / λ)` on `Ω ∩ B(x₀, ρ)`.

For weak solutions `u ∈ H¹₀(Ω)` the same bound holds for `|u|`. This boundary decay, together
with the interior oscillation estimate, is the input of the global Hölder estimate for the
Dirichlet problem with a divergence datum.

## The argument

The estimate without datum,
`TauCeti.PDE.exists_ae_value_le_mul_of_mul_measureReal_le_measureReal_ball_diff`, extends `u⁺`
by zero to a subsolution on the whole space. That extension does not carry a divergence datum
along: the zero extension of `u⁺` is in general not a subsolution of
`-∂ᵢ(aⁱʲ ∂ⱼ·) ≤ ∂ᵢ(1_{u > 0} F)ⁱ`, since Kato's inequality needs an integrable right-hand side.
The datum is therefore split off on the ball first.

* **Splitting.** On `D = B(x₀, 2R)`, extend `a` by `λ I` off `Ω` to a field `a'` uniformly elliptic
  on `D`, and let `w ∈ H¹₀(D)` solve `-∂ᵢ(a'ⁱʲ ∂ⱼw) = ∂ᵢ(1_Ω F)ⁱ`
  (`TauCeti.PDE.exists_forall_energyFormH1_eq_ae_abs_le_divergence`). Stampacchia's estimate
  `TauCeti.PDE.exists_ae_abs_value_le_mul_div_mul_rpow_divergence` bounds
  `|w| ≤ K₀ = O(R^(1 - n/q) ‖F‖_{L^q(Ω ∩ D)} / λ)`.
* **A subsolution on the ball.** With `ū` the zero extension of `u⁺` to `D`, the function
  `H = (ū - w - K₀)⁺` vanishes off `Ω` and lies below `u⁺` on `Ω`. It is a weak subsolution of
  `-∂ᵢ(a'ⁱʲ ∂ⱼH) ≤ 0` on `D`: by `TauCeti.PDE.energyFormH1_posPart_left_nonpos_of_forall_pos` it
  suffices to test `ū - w - K₀` against the truncations `m = min(H, ε v)`, `v ≥ 0` in `H¹₀(D)`.
  Such an `m` lies in `H¹₀(D)` below `ε v`, and its zero extension to `Ω` lies in `H¹₀(Ω)` below
  `u⁺` (`TauCeti.W1p.mem_w1p0Submodule_of_nonneg_of_le`), so the weak formulations of `u` on `Ω`
  and of `w` on `D` may both be tested against it. Their data terms are the same integral
  `∫_{Ω ∩ D} ⟪F, ∇m⟫` and cancel.
* **Reduction.** De Giorgi's interior reduction of the supremum
  (`TauCeti.PDE.exists_ae_value_le_sub_mul_sub`) applies to `H` on `D` at the level `0`, which `H`
  does not exceed on the proportion `θ` of `B(x₀, R)` outside `Ω`. Then `u ≤ H + 2 K₀`.
* **Iteration.** Along the radii `R / 4ʲ` the datum term shrinks by `4^(-(1 - n/q))` per step,
  which gives geometric decay with ratio `max (1 - δ/2) 4^(-(1 - n/q))`, and hence the power law.

## Main declarations

All in the namespace `TauCeti.PDE`.

* `exists_ae_value_le_mul_add_of_mul_measureReal_le_measureReal_ball_diff_divergence`: the
  reduction of the supremum at the boundary.
* `exists_ae_value_le_pow_mul_add_of_mul_measureReal_le_measureReal_ball_diff_divergence`: its
  iteration along the radii `R / 4ʲ`.
* `exists_ae_value_le_mul_rpow_mul_add_of_mul_measureReal_le_measureReal_ball_diff_divergence`:
  the power decay for subsolutions.
* `exists_ae_abs_value_le_mul_rpow_mul_add_of_mul_measureReal_le_measureReal_ball_diff_divergence`:
  the power decay of `|u|` for weak solutions in `H¹₀(Ω)`.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Theorems 8.25, 8.27 and 8.29.
* Q. Han, F. Lin, *Elliptic Partial Differential Equations*, Chapter 4.
* G. Stampacchia, *Le problème de Dirichlet pour les équations elliptiques du second ordre à
  coefficients discontinus*, Ann. Inst. Fourier 15 (1965), 189–258.
-/

public section

noncomputable section

open Filter MeasureTheory Matrix Metric Set TopologicalSpace
open scoped ENNReal NNReal RealInnerProductSpace Topology

namespace TauCeti

namespace PDE

variable {ι : Type*} [Fintype ι] {mu : Measure (EuclideanSpace ℝ ι)}
  [mu.IsAddHaarMeasure] {lam Lam : ℝ} {Omega : Opens (EuclideanSpace ℝ ι)}
  {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ}

/-- Moving a truncation from the ball `D` to `Ω`: let `ū` be the zero extension of `u⁺` to `D`,
let `a'` agree with `a` on `Ω`, and let `m ∈ H¹₀(D)` have vanishing gradient where `u ≤ 0` in
`Ω`. Then the energy of `ū` against `m` on `D` is the energy of `u` against the zero extension of
`m` on `Ω`: both are the integral of `⟨a ∇u, ∇m⟩` over `Ω ∩ D`. -/
private theorem energyFormH1_restrictL_extendByZeroL_posPart_eq
    {D : Opens (EuclideanSpace ℝ ι)} {a' : EuclideanSpace ℝ ι → Matrix ι ι ℝ}
    (haa' : EqOn a' a (Omega : Set (EuclideanSpace ℝ ι))) {u : W1p mu Omega 2}
    (hb : W1p.posPart (by norm_num) u ∈ w1p0Submodule mu Omega 2) (m : W1p0 mu D 2)
    (hgrad : ∀ᵐ x ∂mu.restrict D, x ∈ (Omega : Set (EuclideanSpace ℝ ι)) →
      W1p.value u x ≤ 0 → W1p.gradient (m : W1p mu D 2) x = 0) :
    energyFormH1 a' 0 0 (W1p.restrictL (le_top : D ≤ ⊤)
        (W1p0.extendByZeroL (le_top : Omega ≤ ⊤)
          (⟨W1p.posPart (p := 2) (by norm_num) u, hb⟩ : W1p0 mu Omega 2) : W1p mu ⊤ 2))
        (m : W1p mu D 2) =
      energyFormH1 a 0 0 u (W1p.restrictL (le_top : Omega ≤ ⊤)
        (W1p0.extendByZeroL (le_top : D ≤ ⊤) m : W1p mu ⊤ 2)) := by
  have hO := Omega.isOpen.measurableSet
  have hD := D.isOpen.measurableSet
  have h₁ := W1p0.setIntegral_gradient_restrictL_extendByZeroL le_top (le_top : D ≤ ⊤)
    (⟨W1p.posPart (p := 2) (by norm_num) u, hb⟩ : W1p0 mu Omega 2)
    (fun x g => matrixBilinearForm (a' x) (W1p.gradient (m : W1p mu D 2) x) g) fun _ => map_zero _
  have h₂ := W1p0.setIntegral_gradient_restrictL_extendByZeroL le_top (le_top : Omega ≤ ⊤) m
    (fun x g => matrixBilinearForm (a x) g (W1p.gradient u x)) fun _ => by simp
  rw [energyFormH1_zero_zero_eq_setIntegral, energyFormH1_zero_zero_eq_setIntegral, h₁, h₂,
    inter_comm]
  refine setIntegral_congr_ae (hO.inter hD) ?_
  filter_upwards [(ae_restrict_iff' hD).1 hgrad,
    (ae_restrict_iff' hO).1 (W1p.gradient_posPart_ae (by norm_num) u)] with x h2 h4 hx
  rw [haa' hx.1, h4 hx.1]
  by_cases hu : 0 < W1p.value u x
  · rw [indicator_of_mem (s := {y | 0 < W1p.value u y}) hu]
  · rw [indicator_of_notMem (s := {y | 0 < W1p.value u y}) hu, map_zero,
      h2 hx.2 hx.1 (not_lt.1 hu), map_zero, zero_apply]

/-- Moving the divergence datum from `Ω` to the ball `D`: for `m ∈ H¹₀(D)` with zero extension
`m₀` to `Ω`, `∫_Ω ⟪F, ∇m₀⟫ = ∫_D ⟪1_Ω F, ∇m⟫`, both being the integral over `Ω ∩ D`. -/
private theorem setIntegral_inner_gradient_restrictL_extendByZeroL
    {D : Opens (EuclideanSpace ℝ ι)} (F : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι)
    (m : W1p0 mu D 2) :
    ∫ x in Omega, ⟪F x, W1p.gradient (W1p.restrictL (le_top : Omega ≤ ⊤)
        (W1p0.extendByZeroL (le_top : D ≤ ⊤) m : W1p mu ⊤ 2)) x⟫ ∂mu =
      ∫ x in D, ⟪(Omega : Set (EuclideanSpace ℝ ι)).indicator F x,
        W1p.gradient (m : W1p mu D 2) x⟫ ∂mu := by
  have h₂ : (fun x => ⟪(Omega : Set (EuclideanSpace ℝ ι)).indicator F x,
      W1p.gradient (m : W1p mu D 2) x⟫) = (Omega : Set (EuclideanSpace ℝ ι)).indicator
        fun x => ⟪F x, W1p.gradient (m : W1p mu D 2) x⟫ := by
    funext x
    by_cases hxO : x ∈ (Omega : Set (EuclideanSpace ℝ ι))
    · rw [indicator_of_mem hxO, indicator_of_mem hxO]
    · rw [indicator_of_notMem hxO, indicator_of_notMem hxO, inner_zero_left]
  rw [W1p0.setIntegral_gradient_restrictL_extendByZeroL le_top le_top m (fun x g => ⟪F x, g⟫)
    fun _ => inner_zero_right _, h₂, setIntegral_indicator Omega.isOpen.measurableSet, inter_comm]

/-- The value of `ū - (w + K)` on `D`, where `ū` is the zero extension of `u⁺`. -/
private theorem value_restrictL_extendByZeroL_posPart_sub_ae
    {D : Opens (EuclideanSpace ℝ ι)} [IsFiniteMeasure (mu.restrict (D : Set (EuclideanSpace ℝ ι)))]
    {u : W1p mu Omega 2} (hb : W1p.posPart (by norm_num) u ∈ w1p0Submodule mu Omega 2)
    (w : W1p mu D 2) (K : ℝ) :
    ∀ᵐ x ∂mu, x ∈ (D : Set (EuclideanSpace ℝ ι)) →
      W1p.value (W1p.restrictL (le_top : D ≤ ⊤) (W1p0.extendByZeroL (le_top : Omega ≤ ⊤)
        (⟨W1p.posPart (p := 2) (by norm_num) u, hb⟩ : W1p0 mu Omega 2) : W1p mu ⊤ 2) -
          (w + W1p.const K)) x =
        (Omega : Set (EuclideanSpace ℝ ι)).indicator (fun y => max (W1p.value u y) 0) x -
          (W1p.value w x + K) := by
  have hO := Omega.isOpen.measurableSet
  rw [← ae_restrict_iff' D.isOpen.measurableSet]
  filter_upwards [W1p.value_sub_ae (W1p.restrictL (le_top : D ≤ ⊤)
      (W1p0.extendByZeroL (le_top : Omega ≤ ⊤)
        (⟨W1p.posPart (p := 2) (by norm_num) u, hb⟩ : W1p0 mu Omega 2) : W1p mu ⊤ 2))
      (w + W1p.const K), W1p.value_add_const_ae w K,
    W1p0.value_restrictL_extendByZeroL_ae (V := D) le_top le_top
      (⟨W1p.posPart (p := 2) (by norm_num) u, hb⟩ : W1p0 mu Omega 2),
    ae_restrict_of_ae ((ae_restrict_iff' hO).1 (Lp.coeFn_posPart (W1p.value u)))]
    with x h1 h2 h3 h4
  rw [h1, Pi.sub_apply, h2, h3]
  by_cases hxO : x ∈ (Omega : Set (EuclideanSpace ℝ ι))
  · rw [indicator_of_mem hxO, indicator_of_mem hxO, W1p.value_posPart, h4 hxO]
  · rw [indicator_of_notMem hxO, indicator_of_notMem hxO]

variable [DecidableEq ι]

omit [DecidableEq ι] in
/-- A function `0 ≤ m ≤ u⁺` in `H¹₀(D)`, extended by zero to `Ω`, is a nonnegative element of
`H¹₀(Ω)` when `u⁺ ∈ H¹₀(Ω)`. -/
private theorem mem_w1p0Submodule_restrictL_extendByZeroL_of_le
    {D : Opens (EuclideanSpace ℝ ι)} {u : W1p mu Omega 2}
    (hb : W1p.posPart (by norm_num) u ∈ w1p0Submodule mu Omega 2) (m : W1p0 mu D 2)
    (hm0 : ∀ᵐ x ∂mu, x ∈ (D : Set (EuclideanSpace ℝ ι)) → 0 ≤ W1p.value (m : W1p mu D 2) x)
    (hmu : ∀ᵐ x ∂mu, x ∈ (D : Set (EuclideanSpace ℝ ι)) →
      x ∈ (Omega : Set (EuclideanSpace ℝ ι)) →
        W1p.value (m : W1p mu D 2) x ≤ max (W1p.value u x) 0) :
    (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (W1p.restrictL (le_top : Omega ≤ ⊤)
      (W1p0.extendByZeroL (le_top : D ≤ ⊤) m : W1p mu ⊤ 2)) x) ∧
    W1p.restrictL (le_top : Omega ≤ ⊤) (W1p0.extendByZeroL (le_top : D ≤ ⊤) m : W1p mu ⊤ 2) ∈
      w1p0Submodule mu Omega 2 := by
  have hval := W1p0.value_restrictL_extendByZeroL_ae (V := Omega) le_top le_top m
  have hnn : ∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (W1p.restrictL (le_top : Omega ≤ ⊤)
      (W1p0.extendByZeroL (le_top : D ≤ ⊤) m : W1p mu ⊤ 2)) x := by
    filter_upwards [hval, ae_restrict_of_ae hm0] with x h1 h2
    rw [h1]
    by_cases hxD : x ∈ (D : Set (EuclideanSpace ℝ ι))
    · rw [indicator_of_mem hxD]
      exact h2 hxD
    · rw [indicator_of_notMem hxD]
  refine ⟨hnn, W1p.mem_w1p0Submodule_of_nonneg_of_le (by norm_num) hb hnn ?_⟩
  filter_upwards [hval, ae_restrict_of_ae hmu, Lp.coeFn_posPart (W1p.value u),
    self_mem_ae_restrict Omega.isOpen.measurableSet] with x h1 h2 h3 hxO
  rw [h1, W1p.value_posPart, h3]
  by_cases hxD : x ∈ (D : Set (EuclideanSpace ℝ ι))
  · rw [indicator_of_mem hxD]
    exact h2 hxD hxO
  · rw [indicator_of_notMem hxD]
    exact le_max_right _ _

/-- The energy step of the splitting: test the weak formulation of `u` on `Ω` against the zero
extension of a truncation `m ∈ H¹₀(D)`, and that of `w` on `D` against `m`. If the energy of
`ū` against `m` on `D` is that of `u` against the extension on `Ω`, then the energy of
`ū - w - K` against `m` is nonpositive: the two data terms cancel. -/
private theorem energyFormH1_sub_add_const_nonpos_of_eq
    {D : Opens (EuclideanSpace ℝ ι)} [IsFiniteMeasure (mu.restrict (D : Set (EuclideanSpace ℝ ι)))]
    {a' : EuclideanSpace ℝ ι → Matrix ι ι ℝ}
    (h' : UniformlyEllipticOn (D : Set (EuclideanSpace ℝ ι)) a' lam Lam)
    (ha' : AEStronglyMeasurable a' (mu.restrict D))
    {F : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} {u : W1p mu Omega 2}
    (hu : ∀ v : W1p0 mu Omega 2,
      (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (v : W1p mu Omega 2) x) →
        energyFormH1 a 0 0 u (v : W1p mu Omega 2) ≤
          -∫ x in Omega, ⟪F x, W1p.gradient (v : W1p mu Omega 2) x⟫ ∂mu)
    {w : W1p0 mu D 2}
    (hw : ∀ v : W1p0 mu D 2, energyFormH1 a' 0 0 (w : W1p mu D 2) (v : W1p mu D 2) =
      -∫ x in D, ⟪(Omega : Set (EuclideanSpace ℝ ι)).indicator F x,
        W1p.gradient (v : W1p mu D 2) x⟫ ∂mu)
    (ub : W1p mu D 2) (K : ℝ) (m : W1p0 mu D 2)
    (hE : energyFormH1 a' 0 0 ub (m : W1p mu D 2) = energyFormH1 a 0 0 u
      (W1p.restrictL (le_top : Omega ≤ ⊤) (W1p0.extendByZeroL (le_top : D ≤ ⊤) m : W1p mu ⊤ 2)))
    (hmΩnn : ∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (W1p.restrictL (le_top : Omega ≤ ⊤)
      (W1p0.extendByZeroL (le_top : D ≤ ⊤) m : W1p mu ⊤ 2)) x)
    (hmΩ : W1p.restrictL (le_top : Omega ≤ ⊤) (W1p0.extendByZeroL (le_top : D ≤ ⊤) m :
      W1p mu ⊤ 2) ∈ w1p0Submodule mu Omega 2) :
    energyFormH1 a' 0 0 (ub - ((w : W1p mu D 2) + W1p.const K)) (m : W1p mu D 2) ≤ 0 := by
  have hu' : energyFormH1 a 0 0 u (W1p.restrictL (le_top : Omega ≤ ⊤)
      (W1p0.extendByZeroL (le_top : D ≤ ⊤) m : W1p mu ⊤ 2)) ≤
      -∫ x in Omega, ⟪F x, W1p.gradient (W1p.restrictL (le_top : Omega ≤ ⊤)
        (W1p0.extendByZeroL (le_top : D ≤ ⊤) m : W1p mu ⊤ 2)) x⟫ ∂mu :=
    hu ⟨_, hmΩ⟩ hmΩnn
  have hF : ∫ x in Omega, ⟪F x, W1p.gradient (W1p.restrictL (le_top : Omega ≤ ⊤)
      (W1p0.extendByZeroL (le_top : D ≤ ⊤) m : W1p mu ⊤ 2)) x⟫ ∂mu =
      ∫ x in D, ⟪(Omega : Set (EuclideanSpace ℝ ι)).indicator F x,
        W1p.gradient (m : W1p mu D 2) x⟫ ∂mu :=
    setIntegral_inner_gradient_restrictL_extendByZeroL (mu := mu) (Omega := Omega) (D := D) F m
  have hcoeff := memLp_energyIntegrand_of_bounds (b := 0) (c := 0) (beta := 0) (gamma := 0)
    h'.upper_nonneg ha' aestronglyMeasurable_const aestronglyMeasurable_const
    (fun _x hx eta xi => h'.upper_bound hx eta xi) (fun _ _ => by simp) (fun _ _ => by simp)
  have hsplit : energyFormH1 a' 0 0 (ub - ((w : W1p mu D 2) + W1p.const K)) (m : W1p mu D 2) =
      energyFormH1 a' 0 0 ub m - energyFormH1 a' 0 0 (w : W1p mu D 2) m := by
    rw [energyFormH1_sub_left hcoeff, energyFormH1_add_const_left]
  linarith [hw m]

/-- **Splitting off the divergence datum on a ball keeps a subsolution.** Let `u ∈ H¹(Ω)` be a
weak subsolution of `-∂ᵢ(aⁱʲ ∂ⱼu) ≤ ∂ᵢFⁱ` with `u⁺ ∈ H¹₀(Ω)`, and let `ū` be the zero extension of
`u⁺` to an open set `D` of finite measure. Let `a'` be uniformly elliptic on `D` and agree with
`a` on `Ω`, and let `w ∈ H¹₀(D)` solve `-∂ᵢ(a'ⁱʲ ∂ⱼw) = ∂ᵢ(1_Ω F)ⁱ` on `D` with `w ≥ -K`. Then
`(ū - w - K)⁺` is a weak subsolution of `-∂ᵢ(a'ⁱʲ ∂ⱼ·) ≤ 0` on `D`. -/
private theorem energyFormH1_posPart_restrictL_extendByZeroL_sub_nonpos
    {D : Opens (EuclideanSpace ℝ ι)} [IsFiniteMeasure (mu.restrict (D : Set (EuclideanSpace ℝ ι)))]
    {a' : EuclideanSpace ℝ ι → Matrix ι ι ℝ}
    (h' : UniformlyEllipticOn (D : Set (EuclideanSpace ℝ ι)) a' lam Lam)
    (ha' : AEStronglyMeasurable a' (mu.restrict D))
    (haa' : EqOn a' a (Omega : Set (EuclideanSpace ℝ ι)))
    {F : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} {u : W1p mu Omega 2}
    (hb : W1p.posPart (by norm_num) u ∈ w1p0Submodule mu Omega 2)
    (hu : ∀ v : W1p0 mu Omega 2,
      (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (v : W1p mu Omega 2) x) →
        energyFormH1 a 0 0 u (v : W1p mu Omega 2) ≤
          -∫ x in Omega, ⟪F x, W1p.gradient (v : W1p mu Omega 2) x⟫ ∂mu)
    {w : W1p0 mu D 2}
    (hw : ∀ v : W1p0 mu D 2, energyFormH1 a' 0 0 (w : W1p mu D 2) (v : W1p mu D 2) =
      -∫ x in D, ⟪(Omega : Set (EuclideanSpace ℝ ι)).indicator F x,
        W1p.gradient (v : W1p mu D 2) x⟫ ∂mu)
    {K : ℝ} (hwK : ∀ᵐ x ∂mu.restrict D, -K ≤ W1p.value (w : W1p mu D 2) x)
    {v : W1p0 mu D 2} (hv : ∀ᵐ x ∂mu.restrict D, 0 ≤ W1p.value (v : W1p mu D 2) x) :
    energyFormH1 a' 0 0 (W1p.posPart (by norm_num) (W1p.restrictL (le_top : D ≤ ⊤)
        (W1p0.extendByZeroL (le_top : Omega ≤ ⊤)
          (⟨W1p.posPart (p := 2) (by norm_num) u, hb⟩ : W1p0 mu Omega 2) : W1p mu ⊤ 2) -
        ((w : W1p mu D 2) + W1p.const K))) (v : W1p mu D 2) ≤ 0 := by
  have hD := D.isOpen.measurableSet
  have hUval := value_restrictL_extendByZeroL_posPart_sub_ae hb (w : W1p mu D 2) K
  have hE := energyFormH1_restrictL_extendByZeroL_posPart_eq (D := D) haa' hb
  generalize W1p.restrictL (le_top : D ≤ ⊤) (W1p0.extendByZeroL (le_top : Omega ≤ ⊤)
      (⟨W1p.posPart (p := 2) (by norm_num) u, hb⟩ : W1p0 mu Omega 2) : W1p mu ⊤ 2) = ub
    at hUval hE ⊢
  refine energyFormH1_posPart_left_nonpos_of_forall_pos h' ha' hv fun ε hε => ?_
  have hεv : ∀ᵐ x ∂mu.restrict D, 0 ≤ ε * W1p.value (v : W1p mu D 2) x := by
    filter_upwards [hv] with x hx using mul_nonneg hε.le hx
  have hmval := W1p.value_posPart_sub_posPart_sub_smul_ae (by norm_num)
    (ub - ((w : W1p mu D 2) + W1p.const K)) (v : W1p mu D 2) ε
  have hmgrad := W1p.gradient_posPart_sub_posPart_sub_smul_eq_zero_ae (by norm_num)
    (ub - ((w : W1p mu D 2) + W1p.const K)) (v : W1p mu D 2) hεv
  generalize W1p.posPart (by norm_num) (ub - ((w : W1p mu D 2) + W1p.const K)) -
      W1p.posPart (by norm_num) (W1p.posPart (by norm_num) (ub - ((w : W1p mu D 2) +
        W1p.const K)) - ε • (v : W1p mu D 2)) = m at hmval hmgrad ⊢
  -- The truncation `m = min((ū - w - K)⁺, ε v)` lies in `H¹₀(D)`, below `ε v`.
  have hm0 : ∀ᵐ x ∂mu.restrict D, 0 ≤ W1p.value m x := by
    filter_upwards [hmval, hεv] with x h1 h2 using h1 ▸ le_min (le_max_right _ _) h2
  have hmD : m ∈ w1p0Submodule mu D 2 :=
    W1p.mem_w1p0Submodule_of_nonneg_of_le (u := ε • (v : W1p mu D 2)) (by norm_num)
      ((w1p0Submodule mu D 2).toSubmodule.smul_mem ε v.property) hm0
      (by
        filter_upwards [hmval, W1p.value_smul_ae ε (v : W1p mu D 2)] with x h1 h2
        rw [h1, h2, Pi.smul_apply, smul_eq_mul]
        exact min_le_right _ _)
  -- It lies below `u⁺` on `Ω`, so its zero extension to `Ω` lies in `H¹₀(Ω)`.
  obtain ⟨hmΩnn, hmΩ⟩ := mem_w1p0Submodule_restrictL_extendByZeroL_of_le hb ⟨m, hmD⟩
    ((ae_restrict_iff' hD).1 hm0)
    (by
      filter_upwards [(ae_restrict_iff' hD).1 hmval, hUval, (ae_restrict_iff' hD).1 hwK]
        with x h1 h2 h3 hxD hxO
      rw [h1 hxD, h2 hxD, indicator_of_mem hxO]
      have := h3 hxD
      exact (min_le_left _ _).trans (max_le (by linarith [le_max_left (W1p.value u x) 0])
        (le_max_right _ _)))
  -- Where `u ≤ 0` in `Ω`, or off `Ω`, `ū - w - K ≤ 0` and the gradient of `m` vanishes.
  have hgrad : ∀ᵐ x ∂mu.restrict D, x ∈ (Omega : Set (EuclideanSpace ℝ ι)) →
      W1p.value u x ≤ 0 → W1p.gradient (m : W1p mu D 2) x = 0 := by
    filter_upwards [hmgrad, (ae_restrict_iff' hD).2 hUval, hwK] with x h1 h2 h3 hxO hu0
    refine h1 ?_
    rw [h2, indicator_of_mem hxO, max_eq_right hu0]
    linarith
  exact energyFormH1_sub_add_const_nonpos_of_eq h' ha' hu hw ub K ⟨m, hmD⟩ (hE ⟨m, hmD⟩ hgrad)
    hmΩnn hmΩ

/-- **Splitting off the divergence datum at a boundary point.** For `q > 2`, `q > n` there is
`K > 0`, depending only on `q`, the dimension and `mu`, such that the following holds. Let `u`
be a weak subsolution of `-∂ᵢ(aⁱʲ ∂ⱼu) ≤ ∂ᵢFⁱ` on `Ω` with `u⁺ ∈ H¹₀(Ω)`, and let
`D = B(x₀, 2R)`. Then there are a coefficient field `a'` on `D`, uniformly elliptic with the
constants of `a`, and `U ∈ H¹(D)` with `U⁺` a weak subsolution of `-∂ᵢ(a'ⁱʲ ∂ⱼ·) ≤ 0` on `D`,
such that `U ≤ 1_Ω u⁺ ≤ U + K R^(1 - n/q) ‖F‖_{L^q(Ω ∩ D)} / λ` on `D`. -/
private theorem exists_posPart_subsolution_ball_divergence [Nonempty ι] {q : ℝ≥0}
    (hq : 2 < (q : ℝ)) (hqn : (Fintype.card ι : ℝ) < q) :
    ∃ K : ℝ, 0 < K ∧ ∀ {Omega : Opens (EuclideanSpace ℝ ι)}
      {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {F : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}
      {u : W1p mu Omega 2} {x₀ : EuclideanSpace ℝ ι} {R : ℝ},
      UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam →
      AEStronglyMeasurable a (mu.restrict Omega) →
      MemLp F q (mu.restrict ((Omega : Set (EuclideanSpace ℝ ι)) ∩ ball x₀ (2 * R))) →
      (hb : W1p.posPart (by norm_num) u ∈ w1p0Submodule mu Omega 2) →
      (∀ v : W1p0 mu Omega 2,
        (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (v : W1p mu Omega 2) x) →
          energyFormH1 a 0 0 u (v : W1p mu Omega 2) ≤
            -∫ x in Omega, ⟪F x, W1p.gradient (v : W1p mu Omega 2) x⟫ ∂mu) →
      0 < R →
      ∃ (a' : EuclideanSpace ℝ ι → Matrix ι ι ℝ) (U : W1p mu ⟨ball x₀ (2 * R), isOpen_ball⟩ 2),
        UniformlyEllipticOn (ball x₀ (2 * R)) a' lam Lam ∧
        AEStronglyMeasurable a' (mu.restrict (ball x₀ (2 * R))) ∧
        (∀ v : W1p0 mu ⟨ball x₀ (2 * R), isOpen_ball⟩ 2,
          (∀ᵐ x ∂mu.restrict (ball x₀ (2 * R)),
            0 ≤ W1p.value (v : W1p mu ⟨ball x₀ (2 * R), isOpen_ball⟩ 2) x) →
          energyFormH1 a' 0 0 (W1p.posPart (by norm_num) U)
            (v : W1p mu ⟨ball x₀ (2 * R), isOpen_ball⟩ 2) ≤ 0) ∧
        ∀ᵐ x ∂mu, x ∈ ball x₀ (2 * R) →
          W1p.value U x ≤ (Omega : Set (EuclideanSpace ℝ ι)).indicator
              (fun y => max (W1p.value u y) 0) x ∧
            (Omega : Set (EuclideanSpace ℝ ι)).indicator (fun y => max (W1p.value u y) 0) x ≤
              W1p.value U x + K * R ^ (1 - (Fintype.card ι : ℝ) / q) *
                (eLpNorm F q (mu.restrict ((Omega : Set (EuclideanSpace ℝ ι)) ∩
                  ball x₀ (2 * R)))).toReal / lam := by
  obtain ⟨C, hC, hsplit⟩ := exists_forall_energyFormH1_eq_ae_abs_le_divergence (mu := mu) hq hqn
  set n : ℝ := (Fintype.card ι : ℝ)
  set e : ℝ := n⁻¹ - (q : ℝ)⁻¹
  refine ⟨2 * C * mu.real (ball (0 : EuclideanSpace ℝ ι) 1) ^ e * 2 ^ (1 - n / q),
    mul_pos (mul_pos (mul_pos two_pos hC) (Real.rpow_pos_of_pos (measureReal_ball_pos _ _ one_pos)
      _)) (Real.rpow_pos_of_pos two_pos _), ?_⟩
  intro Omega a F u x₀ R h ha hF hb hu hR
  have hO := Omega.isOpen.measurableSet
  -- Split off the datum on `D = B(x₀, 2R)`, with `a` extended by `λ I` off `Ω`.
  set D : Opens (EuclideanSpace ℝ ι) := ⟨ball x₀ (2 * R), isOpen_ball⟩
  have hDfin : mu D ≠ ∞ := measure_ball_lt_top.ne
  have : IsFiniteMeasure (mu.restrict (D : Set (EuclideanSpace ℝ ι))) :=
    isFiniteMeasure_restrict.2 hDfin
  obtain ⟨a', h', ha', haa'⟩ := h.exists_aestronglyMeasurable_eqOn ha
  have hD' : UniformlyEllipticOn (D : Set (EuclideanSpace ℝ ι)) a' lam Lam :=
    h'.mono_set (subset_univ _)
  have hFD : MemLp ((Omega : Set (EuclideanSpace ℝ ι)).indicator F) q (mu.restrict D) := by
    rw [memLp_indicator_iff_restrict hO.nullMeasurableSet, Measure.restrict_restrict hO]
    exact hF
  obtain ⟨w, hw, hwbd⟩ := hsplit hDfin hD' ha'.restrict hFD
  -- The bound `K₀` on the split-off part is half the datum term.
  set K₀ : ℝ := C * (eLpNorm ((Omega : Set (EuclideanSpace ℝ ι)).indicator F) q
    (mu.restrict D)).toReal / lam * mu.real (D : Set (EuclideanSpace ℝ ι)) ^ e
  have hK₀ : 2 * K₀ = 2 * C * mu.real (ball (0 : EuclideanSpace ℝ ι) 1) ^ e * 2 ^ (1 - n / q) *
      R ^ (1 - n / q) * (eLpNorm F q (mu.restrict ((Omega : Set (EuclideanSpace ℝ ι)) ∩
        ball x₀ (2 * R)))).toReal / lam := by
    have hn : n ≠ 0 := by positivity
    have hne : (Module.finrank ℝ (EuclideanSpace ℝ ι) : ℝ) * e = 1 - n / q := by
      rw [finrank_euclideanSpace, mul_sub, mul_inv_cancel₀ hn, div_eq_mul_inv]
    simp only [K₀, D, Opens.coe_mk]
    rw [eLpNorm_indicator_eq_eLpNorm_restrict hO.nullMeasurableSet,
      Measure.restrict_restrict hO, Measure.addHaar_real_ball_rpow _ _ (by positivity), hne,
      Real.mul_rpow zero_le_two hR.le]
    ring
  have hwK : ∀ᵐ x ∂mu.restrict D, -K₀ ≤ W1p.value (w : W1p mu D 2) x := by
    filter_upwards [hwbd] with x hx using (abs_le.1 hx).1
  -- `U = ū - w - K₀`, where `ū` is the zero extension of `u⁺`.
  refine ⟨a', _, hD', ha'.restrict, fun v hv =>
    energyFormH1_posPart_restrictL_extendByZeroL_sub_nonpos hD' ha'.restrict haa' hb hu hw hwK
      (v := v) hv, ?_⟩
  filter_upwards [value_restrictL_extendByZeroL_posPart_sub_ae hb (w : W1p mu D 2) K₀,
    (ae_restrict_iff' measurableSet_ball).1 hwbd] with x h1 h2 hxB
  rw [h1 hxB, ← hK₀]
  have := abs_le.1 (h2 hxB)
  constructor <;> linarith

/-- **Reduction of the supremum at the boundary with a divergence datum (De Giorgi).** Let
`n ≥ 1` be the dimension, fix a proportion `θ > 0` and an exponent `q > 2` with `q > n`. There
are `δ ∈ (0, 1)`, depending only on `λ`, `Λ`, `θ`, the dimension and the normalization of the
additive Haar measure `mu`, and `K > 0`, depending only on `q`, the dimension and `mu`, such that
the following holds. Let `a` be measurable and uniformly elliptic on `Ω` with constants `λ, Λ`,
and let `u ∈ H¹(Ω)` be a weak subsolution of `-∂ᵢ(aⁱʲ ∂ⱼu) ≤ ∂ᵢFⁱ`, that is
`a(u, v) ≤ -∫_Ω ⟪F, ∇v⟫` for every nonnegative `v ∈ H¹₀(Ω)`, with `u ≤ 0` on `∂Ω` in the sense
that `u⁺ ∈ H¹₀(Ω)`, and `F ∈ L^q(Ω ∩ B(x₀, 2R); ℝⁿ)`. If `u ≤ M` almost everywhere on
`Ω ∩ B(x₀, 2R)` and the complement of `Ω` fills the proportion `θ` of `B(x₀, R)`, then almost
everywhere on `Ω ∩ B(x₀, R/2)`

`u ≤ (1 - δ) M + K R^(1 - n/q) ‖F‖_{L^q(Ω ∩ B(x₀, 2R))} / λ`.

The ball `B(x₀, 2R)` need not lie in `Ω`, and no regularity of `∂Ω` is assumed. -/
theorem exists_ae_value_le_mul_add_of_mul_measureReal_le_measureReal_ball_diff_divergence
    [Nonempty ι] {θ : ℝ} (hθ : 0 < θ) {q : ℝ≥0} (hq : 2 < (q : ℝ))
    (hqn : (Fintype.card ι : ℝ) < q) :
    ∃ δ K : ℝ, 0 < δ ∧ δ < 1 ∧ 0 < K ∧ ∀ {Omega : Opens (EuclideanSpace ℝ ι)}
      {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {F : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}
      {u : W1p mu Omega 2} {x₀ : EuclideanSpace ℝ ι} {R M : ℝ},
      UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam →
      AEStronglyMeasurable a (mu.restrict Omega) →
      MemLp F q (mu.restrict ((Omega : Set (EuclideanSpace ℝ ι)) ∩ ball x₀ (2 * R))) →
      W1p.posPart (by norm_num) u ∈ w1p0Submodule mu Omega 2 →
      (∀ v : W1p0 mu Omega 2,
        (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (v : W1p mu Omega 2) x) →
          energyFormH1 a 0 0 u (v : W1p mu Omega 2) ≤
            -∫ x in Omega, ⟪F x, W1p.gradient (v : W1p mu Omega 2) x⟫ ∂mu) →
      0 < R →
      (∀ᵐ x ∂mu.restrict ((Omega : Set (EuclideanSpace ℝ ι)) ∩ ball x₀ (2 * R)),
        W1p.value u x ≤ M) →
      θ * mu.real (ball x₀ R) ≤ mu.real (ball x₀ R \ (Omega : Set (EuclideanSpace ℝ ι))) →
      ∀ᵐ x ∂mu.restrict ((Omega : Set (EuclideanSpace ℝ ι)) ∩ ball x₀ (R / 2)),
        W1p.value u x ≤ (1 - δ) * M + K * R ^ (1 - (Fintype.card ι : ℝ) / q) *
          (eLpNorm F q (mu.restrict ((Omega : Set (EuclideanSpace ℝ ι)) ∩
            ball x₀ (2 * R)))).toReal / lam := by
  obtain ⟨δ, hδ0, hδ1, hred⟩ :=
    exists_ae_value_le_sub_mul_sub (mu := mu) (lam := lam) (Lam := Lam) hθ
  obtain ⟨K, hK, hsplit⟩ := exists_posPart_subsolution_ball_divergence (mu := mu) (lam := lam)
    (Lam := Lam) hq hqn
  refine ⟨δ, K, hδ0, hδ1, hK, ?_⟩
  intro Omega a F u x₀ R M h ha hF hb hu hR hle hθR
  have hO := Omega.isOpen.measurableSet
  have hlam := h.pos
  rcases lt_or_ge M 0 with hM | hM
  · -- For `M < 0` the claim is weaker than the hypothesis.
    filter_upwards [ae_restrict_of_ae_restrict_of_subset
      (inter_subset_inter_right _ (ball_subset_ball (by linarith))) hle] with x hx
    nlinarith [show 0 ≤ K * R ^ (1 - (Fintype.card ι : ℝ) / q) * (eLpNorm F q (mu.restrict
      ((Omega : Set (EuclideanSpace ℝ ι)) ∩ ball x₀ (2 * R)))).toReal / lam by positivity]
  obtain ⟨a', U, hD', ha', hsub, hval⟩ := hsplit h ha hF hb hu hR
  -- `U⁺` is a subsolution on `B(x₀, 2R)`, below `M`, vanishing off `Ω`.
  have hHval : ∀ᵐ x ∂mu, x ∈ ball x₀ (2 * R) →
      W1p.value (W1p.posPart (by norm_num) U) x = max (W1p.value U x) 0 := by
    rw [← ae_restrict_iff' measurableSet_ball]
    filter_upwards [Lp.coeFn_posPart (W1p.value U)] with x hx
    rw [W1p.value_posPart, hx]
  have hHM : ∀ᵐ x ∂mu.restrict (ball x₀ (2 * R)),
      W1p.value (W1p.posPart (by norm_num) U) x ≤ M := by
    rw [ae_restrict_iff' measurableSet_ball]
    filter_upwards [hHval, hval, (ae_restrict_iff' (hO.inter measurableSet_ball)).1 hle]
      with x h1 h2 h3 hxB
    rw [h1 hxB]
    refine max_le ((h2 hxB).1.trans ?_) hM
    by_cases hxO : x ∈ (Omega : Set (EuclideanSpace ℝ ι))
    · rw [indicator_of_mem hxO]
      exact max_le (h3 ⟨hxO, hxB⟩) hM
    · rw [indicator_of_notMem hxO]
      exact hM
  have hRB : ball x₀ R ⊆ ball x₀ (2 * R) := ball_subset_ball (by linarith)
  have hHθ := mul_measureReal_ball_le_measureReal_setOf_le_zero
    (g := fun x => W1p.value (W1p.posPart (by norm_num) U) x) hθR (by
    filter_upwards [hHval, hval] with x h1 h2 hxB hxc
    rw [h1 (hRB hxB)]
    have := (h2 (hRB hxB)).1
    rw [indicator_of_notMem hxc] at this
    exact max_le this le_rfl)
  have hred' := hred hD' ha' hsub hR subset_rfl hM hHM hHθ
  -- Back on `Ω ∩ B(x₀, R/2)`: `u ≤ u⁺ = 1_Ω u⁺ ≤ U⁺ + datum term`.
  have hR2 : ball x₀ (R / 2) ⊆ ball x₀ (2 * R) := ball_subset_ball (by linarith)
  rw [ae_restrict_iff' (hO.inter measurableSet_ball)]
  filter_upwards [(ae_restrict_iff' measurableSet_ball).1 hred', hHval, hval] with x h1 h2 h3 hx
  obtain ⟨hxO, hxB⟩ := hx
  have h1 := h1 hxB
  rw [h2 (hR2 hxB)] at h1
  have h3 := (h3 (hR2 hxB)).2
  rw [indicator_of_mem hxO] at h3
  linarith [le_max_left (W1p.value U x) 0, le_max_left (W1p.value u x) 0]

/-- One step of the decay of the supremum: with `τ ≥ 1 - δ / 2` and `δ c = 2 K`, the bound
`(1 - δ) P Q + K P A` obtained from `P Q`, `Q = M + c A`, is at most `τ P Q`. -/
private theorem one_sub_mul_mul_add_mul_mul_le {δ τ K c P M A : ℝ} (hδ : 0 < δ)
    (hτ : 1 - δ / 2 ≤ τ) (hc : δ * c = 2 * K) (hP : 0 ≤ P) (hM : 0 ≤ M) (hcA : 0 ≤ c * A) :
    (1 - δ) * (P * (M + c * A)) + K * P * A ≤ τ * (P * (M + c * A)) := by
  have hQ : 0 ≤ P * (M + c * A) := mul_nonneg hP (by linarith)
  have h1 : (1 - δ / 2) * (P * (M + c * A)) ≤ τ * (P * (M + c * A)) :=
    mul_le_mul_of_nonneg_right hτ hQ
  have h2 : K * P * A = δ / 2 * (P * (c * A)) := by linear_combination (P * A / 2) * hc.symm
  nlinarith [mul_nonneg hδ.le (mul_nonneg hP hM)]

/-- The induction step of the decay: from `u ≤ (1 - δ) τʲ (M + c A) + K r^γ N' / λ`, with
`A = R^γ N / λ`, `r^γ ≤ τʲ R^γ` and `N' ≤ N`, to `u ≤ τʲ⁺¹ (M + c A)`. -/
private theorem one_sub_mul_add_mul_rpow_le_pow_succ_mul {δ τ K c M R r γ lam N N' : ℝ} {j : ℕ}
    (hδ : 0 < δ) (hτ : 1 - δ / 2 ≤ τ) (hτ0 : 0 ≤ τ) (hc : δ * c = 2 * K) (hc0 : 0 ≤ c)
    (hK : 0 ≤ K) (hM : 0 ≤ M) (hlam : 0 < lam) (hRγ : 0 ≤ R ^ γ) (hN' : 0 ≤ N') (hN : N' ≤ N)
    (hrγ : r ^ γ ≤ τ ^ j * R ^ γ) :
    (1 - δ) * (τ ^ j * (M + c * R ^ γ * N / lam)) + K * r ^ γ * N' / lam ≤
      τ ^ (j + 1) * (M + c * R ^ γ * N / lam) := by
  have hA : 0 ≤ R ^ γ * N / lam := div_nonneg (mul_nonneg hRγ (hN'.trans hN)) hlam.le
  have hdatum : K * r ^ γ * N' / lam ≤ K * τ ^ j * (R ^ γ * N / lam) :=
    calc _ ≤ K * (τ ^ j * R ^ γ) * N / lam := by gcongr
      _ = _ := by ring
  have hstep := one_sub_mul_mul_add_mul_mul_le (τ := τ) (P := τ ^ j) (M := M)
    (A := R ^ γ * N / lam) hδ hτ hc (by positivity) hM (mul_nonneg hc0 hA)
  rw [pow_succ', mul_assoc]
  simp only [mul_div_assoc] at hstep hdatum ⊢
  linarith

/-- The datum term at the radius `R / 4ʲ / 2` is at most `τʲ` times the one at `R`, for
`4^(-γ) ≤ τ` and `γ > 0`. -/
private theorem div_pow_div_two_rpow_le {R γ τ : ℝ} (hR : 0 < R) (hγ : 0 < γ)
    (hτ : (4 : ℝ) ^ (-γ) ≤ τ) (j : ℕ) :
    (R / 4 ^ j / 2) ^ γ ≤ τ ^ j * R ^ γ := by
  have h4 : (0 : ℝ) < 4 ^ j := by positivity
  calc (R / 4 ^ j / 2) ^ γ ≤ (R / 4 ^ j) ^ γ :=
        Real.rpow_le_rpow (by positivity) (div_le_self (by positivity) one_le_two) hγ.le
    _ = ((4 : ℝ) ^ (-γ)) ^ j * R ^ γ := by
        rw [Real.div_rpow hR.le h4.le, ← Real.rpow_pow_comm (by norm_num), Real.rpow_neg
          (by norm_num), inv_pow, div_eq_mul_inv, mul_comm]
    _ ≤ τ ^ j * R ^ γ := by gcongr

/-- **Geometric decay of the supremum at the boundary with a divergence datum (De Giorgi).** Let
`n ≥ 1` be the dimension, fix a proportion `θ > 0` and an exponent `q > 2` with `q > n`. There are
`τ ∈ (0, 1)` and `C > 0`, depending only on `λ`, `Λ`, `θ`, `q`, the dimension and the
normalization of `mu`, such that the following holds. Let `a` be measurable and uniformly elliptic
on `Ω` with constants `λ, Λ`, and let `u ∈ H¹(Ω)` be a weak subsolution of `-∂ᵢ(aⁱʲ ∂ⱼu) ≤ ∂ᵢFⁱ`
with `u⁺ ∈ H¹₀(Ω)` and `F ∈ L^q(Ω ∩ B(x₀, R); ℝⁿ)`. If `u ≤ M` almost everywhere on
`Ω ∩ B(x₀, R)`, `M ≥ 0`, and the complement of `Ω` fills the proportion `θ` of every ball
`B(x₀, r)`, `0 < r ≤ R`, then for every `j`, almost everywhere on `Ω ∩ B(x₀, R / 4ʲ)`,

`u ≤ τʲ (M + C R^(1 - n/q) ‖F‖_{L^q(Ω ∩ B(x₀, R))} / λ)`. -/
theorem exists_ae_value_le_pow_mul_add_of_mul_measureReal_le_measureReal_ball_diff_divergence
    [Nonempty ι] {θ : ℝ} (hθ : 0 < θ) {q : ℝ≥0} (hq : 2 < (q : ℝ))
    (hqn : (Fintype.card ι : ℝ) < q) :
    ∃ τ C : ℝ, 0 < τ ∧ τ < 1 ∧ 0 < C ∧ ∀ {Omega : Opens (EuclideanSpace ℝ ι)}
      {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {F : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}
      {u : W1p mu Omega 2} {x₀ : EuclideanSpace ℝ ι} {R M : ℝ},
      UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam →
      AEStronglyMeasurable a (mu.restrict Omega) →
      MemLp F q (mu.restrict ((Omega : Set (EuclideanSpace ℝ ι)) ∩ ball x₀ R)) →
      W1p.posPart (by norm_num) u ∈ w1p0Submodule mu Omega 2 →
      (∀ v : W1p0 mu Omega 2,
        (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (v : W1p mu Omega 2) x) →
          energyFormH1 a 0 0 u (v : W1p mu Omega 2) ≤
            -∫ x in Omega, ⟪F x, W1p.gradient (v : W1p mu Omega 2) x⟫ ∂mu) →
      0 < R → 0 ≤ M →
      (∀ᵐ x ∂mu.restrict ((Omega : Set (EuclideanSpace ℝ ι)) ∩ ball x₀ R), W1p.value u x ≤ M) →
      (∀ r, 0 < r → r ≤ R →
        θ * mu.real (ball x₀ r) ≤ mu.real (ball x₀ r \ (Omega : Set (EuclideanSpace ℝ ι)))) →
      ∀ j : ℕ, ∀ᵐ x ∂mu.restrict ((Omega : Set (EuclideanSpace ℝ ι)) ∩ ball x₀ (R / 4 ^ j)),
        W1p.value u x ≤ τ ^ j * (M + C * R ^ (1 - (Fintype.card ι : ℝ) / q) *
          (eLpNorm F q (mu.restrict ((Omega : Set (EuclideanSpace ℝ ι)) ∩
            ball x₀ R))).toReal / lam) := by
  obtain ⟨δ, K, hδ0, hδ1, hK, hred⟩ :=
    exists_ae_value_le_mul_add_of_mul_measureReal_le_measureReal_ball_diff_divergence
      (mu := mu) (lam := lam) (Lam := Lam) hθ hq hqn
  set γ : ℝ := 1 - (Fintype.card ι : ℝ) / q
  have hγ : 0 < γ := by
    have : (Fintype.card ι : ℝ) / q < 1 := (div_lt_one (by positivity)).2 hqn
    simp only [γ]
    linarith
  set τ : ℝ := max (1 - δ / 2) ((4 : ℝ) ^ (-γ))
  have hτ1 : τ < 1 := max_lt (by linarith) (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num)
    (by linarith))
  have hτ0 : 0 < τ := lt_max_of_lt_left (by linarith)
  refine ⟨τ, 2 * K / δ, hτ0, hτ1, by positivity, ?_⟩
  intro Omega a F u x₀ R M h ha hF hb hu hR hM hle hext j
  have hc : δ * (2 * K / δ) = 2 * K := by field_simp
  induction j with
  | zero =>
    have hlam := h.pos
    have hA : 0 ≤ 2 * K / δ * R ^ γ * (eLpNorm F q (mu.restrict
        ((Omega : Set (EuclideanSpace ℝ ι)) ∩ ball x₀ R))).toReal / lam := by positivity
    simp only [pow_zero, div_one, one_mul]
    filter_upwards [hle] with x hx
    linarith
  | succ j ih =>
    -- One reduction step from `B(x₀, 2r)` to `B(x₀, r / 2)`, with `2r = R / 4ʲ`.
    set r := R / 4 ^ j / 2 with hr_def
    have h2r : R / 4 ^ j = 2 * r := by rw [hr_def]; ring
    have hr2 : R / 4 ^ (j + 1) = r / 2 := by rw [hr_def, pow_succ]; ring
    have hr : 0 < r := by positivity
    have hrR : 2 * r ≤ R := h2r ▸ div_le_self hR.le (one_le_pow₀ (by norm_num))
    have hsub : (Omega : Set (EuclideanSpace ℝ ι)) ∩ ball x₀ (2 * r) ⊆
        (Omega : Set (EuclideanSpace ℝ ι)) ∩ ball x₀ R :=
      inter_subset_inter_right _ (ball_subset_ball hrR)
    rw [h2r] at ih
    rw [hr2]
    refine (hred h ha (hF.mono_measure (Measure.restrict_mono hsub le_rfl)) hb hu hr ih
      (hext r hr (by linarith))).mono fun x hx => hx.trans ?_
    -- The datum term on `B(x₀, 2r)` is at most `τʲ` times the one on `B(x₀, R)`.
    have hrγ := div_pow_div_two_rpow_le (τ := τ) hR hγ (le_max_right _ _) j
    rw [← hr_def] at hrγ
    exact one_sub_mul_add_mul_rpow_le_pow_succ_mul hδ0 (le_max_left _ _)
      (hτ0.le) hc (by positivity) hK.le hM h.pos (by positivity) ENNReal.toReal_nonneg
      (ENNReal.toReal_mono hF.eLpNorm_ne_top
        (eLpNorm_mono_measure _ (Measure.restrict_mono hsub le_rfl))) hrγ

/-- From the dyadic radii to all radii: if `R / ρ < 4^(j + 1)`, then
`(4^(-α))ʲ ≤ 4^α (ρ / R)^α`. -/
private theorem inv_rpow_pow_le_rpow_mul_div_rpow {α ρ R : ℝ} (hα : 0 ≤ α) (hρ : 0 < ρ)
    (hR : 0 < R) {j : ℕ} (hj : R / ρ < 4 ^ (j + 1)) :
    (((4 : ℝ) ^ α)⁻¹) ^ j ≤ 4 ^ α * (ρ / R) ^ α := by
  have h1 : 1 ≤ 4 ^ (j + 1) * (ρ / R) := by
    have := (div_lt_iff₀ hρ).1 hj
    rw [mul_div_assoc', le_div_iff₀ hR, one_mul]
    linarith
  have h2 := Real.one_le_rpow h1 hα
  rw [Real.mul_rpow (by positivity) (by positivity), pow_succ,
    Real.mul_rpow (by positivity) (by norm_num)] at h2
  have hpos : 0 < ((4 : ℝ) ^ j) ^ α := by positivity
  rw [inv_pow, Real.rpow_pow_comm (by norm_num), inv_eq_one_div, div_le_iff₀ hpos]
  linarith [show ((4 : ℝ) ^ j) ^ α * 4 ^ α * (ρ / R) ^ α = 4 ^ α * (ρ / R) ^ α *
    ((4 : ℝ) ^ j) ^ α by ring]

/-- **Power decay at the boundary with a divergence datum (De Giorgi).** Let `n ≥ 1` be the
dimension, fix a proportion `θ > 0` and an exponent `q > 2` with `q > n`. There are `α > 0` and
`C > 0`, depending only on `λ`, `Λ`, `θ`, `q`, the dimension and the normalization of `mu`, such
that the following holds. Let `a` be measurable and uniformly elliptic on `Ω` with constants
`λ, Λ`, and let `u ∈ H¹(Ω)` be a weak subsolution of `-∂ᵢ(aⁱʲ ∂ⱼu) ≤ ∂ᵢFⁱ` with `u⁺ ∈ H¹₀(Ω)` and
`F ∈ L^q(Ω ∩ B(x₀, R); ℝⁿ)`. If `u ≤ M` almost everywhere on `Ω ∩ B(x₀, R)`, `M ≥ 0`, and the
complement of `Ω` fills the proportion `θ` of every ball `B(x₀, r)`, `0 < r ≤ R`, then for
`0 < ρ ≤ R`, almost everywhere on `Ω ∩ B(x₀, ρ)`,

`u ≤ C (ρ / R)^α (M + R^(1 - n/q) ‖F‖_{L^q(Ω ∩ B(x₀, R))} / λ)`. -/
theorem exists_ae_value_le_mul_rpow_mul_add_of_mul_measureReal_le_measureReal_ball_diff_divergence
    [Nonempty ι] {θ : ℝ} (hθ : 0 < θ) {q : ℝ≥0} (hq : 2 < (q : ℝ))
    (hqn : (Fintype.card ι : ℝ) < q) :
    ∃ α C : ℝ, 0 < α ∧ 0 < C ∧ ∀ {Omega : Opens (EuclideanSpace ℝ ι)}
      {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {F : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}
      {u : W1p mu Omega 2} {x₀ : EuclideanSpace ℝ ι} {R M ρ : ℝ},
      UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam →
      AEStronglyMeasurable a (mu.restrict Omega) →
      MemLp F q (mu.restrict ((Omega : Set (EuclideanSpace ℝ ι)) ∩ ball x₀ R)) →
      W1p.posPart (by norm_num) u ∈ w1p0Submodule mu Omega 2 →
      (∀ v : W1p0 mu Omega 2,
        (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (v : W1p mu Omega 2) x) →
          energyFormH1 a 0 0 u (v : W1p mu Omega 2) ≤
            -∫ x in Omega, ⟪F x, W1p.gradient (v : W1p mu Omega 2) x⟫ ∂mu) →
      0 < R → 0 ≤ M →
      (∀ᵐ x ∂mu.restrict ((Omega : Set (EuclideanSpace ℝ ι)) ∩ ball x₀ R), W1p.value u x ≤ M) →
      (∀ r, 0 < r → r ≤ R →
        θ * mu.real (ball x₀ r) ≤ mu.real (ball x₀ r \ (Omega : Set (EuclideanSpace ℝ ι)))) →
      0 < ρ → ρ ≤ R →
      ∀ᵐ x ∂mu.restrict ((Omega : Set (EuclideanSpace ℝ ι)) ∩ ball x₀ ρ),
        W1p.value u x ≤ C * (ρ / R) ^ α * (M + R ^ (1 - (Fintype.card ι : ℝ) / q) *
          (eLpNorm F q (mu.restrict ((Omega : Set (EuclideanSpace ℝ ι)) ∩
            ball x₀ R))).toReal / lam) := by
  obtain ⟨τ, c, hτ0, hτ1, hc, hdisc⟩ :=
    exists_ae_value_le_pow_mul_add_of_mul_measureReal_le_measureReal_ball_diff_divergence
      (mu := mu) (lam := lam) (Lam := Lam) hθ hq hqn
  set α : ℝ := -Real.logb 4 τ
  have hα : 0 < α := neg_pos.2 (Real.logb_neg (by norm_num) hτ0 hτ1)
  have hτα : τ = ((4 : ℝ) ^ α)⁻¹ := by
    rw [← Real.rpow_neg (by norm_num), neg_neg, Real.rpow_logb (by norm_num) (by norm_num) hτ0]
  refine ⟨α, 4 ^ α * max 1 c, hα, by positivity, ?_⟩
  intro Omega a F u x₀ R M ρ h ha hF hb hu hR hM hle hext hρ hρR
  have hlam : 0 < lam := h.pos
  obtain ⟨j, hj1, hj2⟩ := exists_nat_pow_near ((one_le_div hρ).2 hρR) (by norm_num : (1 : ℝ) < 4)
  have hρj : ρ ≤ R / 4 ^ j := by
    rw [le_div_iff₀ (by positivity), mul_comm]
    exact (le_div_iff₀ hρ).1 hj1
  filter_upwards [ae_restrict_of_ae_restrict_of_subset
    (inter_subset_inter_right _ (ball_subset_ball hρj))
    (hdisc h ha hF hb hu hR hM hle hext j)] with x hx
  refine hx.trans ?_
  set A : ℝ := R ^ (1 - (Fintype.card ι : ℝ) / q) * (eLpNorm F q (mu.restrict
    ((Omega : Set (EuclideanSpace ℝ ι)) ∩ ball x₀ R))).toReal / lam
  have hA : 0 ≤ A := by positivity
  have hτj : τ ^ j ≤ 4 ^ α * (ρ / R) ^ α :=
    hτα ▸ inv_rpow_pow_le_rpow_mul_div_rpow hα.le hρ hR hj2
  have hMA : M + c * A ≤ max 1 c * (M + A) := by
    nlinarith [le_max_left 1 c, le_max_right 1 c]
  calc _ = τ ^ j * (M + c * A) := by simp only [A]; ring
    _ ≤ (4 ^ α * (ρ / R) ^ α) * (max 1 c * (M + A)) :=
        mul_le_mul hτj hMA (by positivity) (by positivity)
    _ = _ := by simp only [A]; ring

/-- **Power decay of weak solutions at the boundary with a divergence datum (De Giorgi).** Let
`n ≥ 1` be the dimension, fix a proportion `θ > 0` and an exponent `q > 2` with `q > n`. There
are `α > 0` and `C > 0`, depending only on `λ`, `Λ`, `θ`, `q`, the dimension and the normalization
of `mu`, such that the following holds. Let `a` be measurable and uniformly elliptic on `Ω` with
constants `λ, Λ`, and let `u ∈ H¹₀(Ω)` be a weak solution of `-∂ᵢ(aⁱʲ ∂ⱼu) = ∂ᵢFⁱ` with
`F ∈ L^q(Ω ∩ B(x₀, R); ℝⁿ)`. If `|u| ≤ M` almost everywhere on `Ω ∩ B(x₀, R)` and the complement
of `Ω` fills the proportion `θ` of every ball `B(x₀, r)`, `0 < r ≤ R`, then for `0 < ρ ≤ R`,
almost everywhere on `Ω ∩ B(x₀, ρ)`,

`|u| ≤ C (ρ / R)^α (M + R^(1 - n/q) ‖F‖_{L^q(Ω ∩ B(x₀, R))} / λ)`. -/
theorem
    exists_ae_abs_value_le_mul_rpow_mul_add_of_mul_measureReal_le_measureReal_ball_diff_divergence
    [Nonempty ι] {θ : ℝ} (hθ : 0 < θ) {q : ℝ≥0} (hq : 2 < (q : ℝ))
    (hqn : (Fintype.card ι : ℝ) < q) :
    ∃ α C : ℝ, 0 < α ∧ 0 < C ∧ ∀ {Omega : Opens (EuclideanSpace ℝ ι)}
      {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {F : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}
      {u : W1p mu Omega 2} {x₀ : EuclideanSpace ℝ ι} {R M ρ : ℝ},
      UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam →
      AEStronglyMeasurable a (mu.restrict Omega) →
      MemLp F q (mu.restrict ((Omega : Set (EuclideanSpace ℝ ι)) ∩ ball x₀ R)) →
      u ∈ w1p0Submodule mu Omega 2 →
      (∀ v : W1p0 mu Omega 2, energyFormH1 a 0 0 u (v : W1p mu Omega 2) =
        -∫ x in Omega, ⟪F x, W1p.gradient (v : W1p mu Omega 2) x⟫ ∂mu) →
      0 < R →
      (∀ᵐ x ∂mu.restrict ((Omega : Set (EuclideanSpace ℝ ι)) ∩ ball x₀ R),
        |W1p.value u x| ≤ M) →
      (∀ r, 0 < r → r ≤ R →
        θ * mu.real (ball x₀ r) ≤ mu.real (ball x₀ r \ (Omega : Set (EuclideanSpace ℝ ι)))) →
      0 < ρ → ρ ≤ R →
      ∀ᵐ x ∂mu.restrict ((Omega : Set (EuclideanSpace ℝ ι)) ∩ ball x₀ ρ),
        |W1p.value u x| ≤ C * (ρ / R) ^ α * (M + R ^ (1 - (Fintype.card ι : ℝ) / q) *
          (eLpNorm F q (mu.restrict ((Omega : Set (EuclideanSpace ℝ ι)) ∩
            ball x₀ R))).toReal / lam) := by
  obtain ⟨α, C, hα, hC, hdecay⟩ :=
    exists_ae_value_le_mul_rpow_mul_add_of_mul_measureReal_le_measureReal_ball_diff_divergence
      (mu := mu) (lam := lam) (Lam := Lam) hθ hq hqn
  refine ⟨α, C, hα, hC, ?_⟩
  intro Omega a F u x₀ R M ρ h ha hF hu0 hu hR hle hext hρ hρR
  have hsub : (Omega : Set (EuclideanSpace ℝ ι)) ∩ ball x₀ ρ ⊆
      (Omega : Set (EuclideanSpace ℝ ι)) ∩ ball x₀ R :=
    inter_subset_inter_right _ (ball_subset_ball hρR)
  rcases lt_or_ge M 0 with hM | hM
  · -- For `M < 0` the hypothesis says that `Ω ∩ B(x₀, R)` is null.
    have h0 : mu.restrict ((Omega : Set (EuclideanSpace ℝ ι)) ∩ ball x₀ R) = 0 :=
      ae_eq_bot.1 (eventually_false_iff_eq_bot.1
        (hle.mono fun x hx => absurd ((abs_nonneg _).trans hx) (not_le.2 hM)))
    rw [Measure.restrict_eq_zero.2 (measure_mono_null hsub (Measure.restrict_eq_zero.1 h0))]
    simp
  have hneg : ∀ᵐ x ∂mu.restrict ((Omega : Set (EuclideanSpace ℝ ι)) ∩ ball x₀ R),
      W1p.value (-u) x = -W1p.value u x :=
    ae_restrict_of_ae_restrict_of_subset inter_subset_left (W1p.value_neg_ae u)
  -- Both `u` and `-u` are subsolutions vanishing on the boundary, with data `F` and `-F`.
  have hpos := hdecay h ha hF (W1p.posPart_mem_w1p0Submodule (by norm_num) hu0)
    (fun v _ => (hu v).le) hR hM (by filter_upwards [hle] with x hx using (abs_le.1 hx).2)
    hext hρ hρR
  have hneg' := hdecay (F := -F) (u := -u) h ha hF.neg
    (W1p.posPart_mem_w1p0Submodule (by norm_num)
      ((w1p0Submodule mu Omega 2).toSubmodule.neg_mem hu0))
    (fun v _ => by
      rw [energyFormH1_neg_left, hu v]
      simp only [Pi.neg_apply, inner_neg_left, integral_neg, neg_neg, le_refl])
    hR hM (by
      filter_upwards [hle, hneg] with x hx hx'
      rw [hx']
      exact neg_le.1 (abs_le.1 hx).1) hext hρ hρR
  rw [eLpNorm_neg] at hneg'
  filter_upwards [hpos, hneg', ae_restrict_of_ae_restrict_of_subset hsub hneg] with x h1 h2 h3
  rw [h3] at h2
  exact abs_le.2 ⟨neg_le.1 h2, h1⟩

end PDE

end TauCeti
