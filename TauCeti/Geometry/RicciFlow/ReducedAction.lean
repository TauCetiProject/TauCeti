/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.FirstVariation.MovingMetric
public import TauCeti.Geometry.Manifold.MFDeriv.Variation
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Scalar.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Basic
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# The reduced action and its intrinsic first variation

For a smooth family `g(t)` and terminal time `T`, the backward action of `γ` is
`∫ √τ (Scal_(g(T - τ))(γ(τ)) + g(T - τ)(γ'(τ), γ'(τ))) dτ`.
Under `τ = s²` and `γ = α ∘ sqrt`, it equals the regularized action
`∫ [g(T - s²)(α', α') / 2 + 2s² Scal_(g(T - s²))(α)] ds`.
This law permits initial square time zero; it uses differentiability only in the open segment.

The first variation of the regularized action has endpoint momentum `g(V, α')` and interior
pairing `g(V, D_s α') + 4s Ric(V, α') - 2s² dScal(V)`. The coefficient `4s` follows from the
actual forward Ricci equation `∂_t g = -2 Ric` and the time map `T - s²`.
All geometric quantities are the native curvature and Levi-Civita operators of the metric at
that time. The scalar curvature's joint `C¹` regularity is explicit along the central path.

The same derivative and integral stationarity at a local minimum hold for the backward action
of the reparametrized variation `F u ∘ sqrt` on `a²..b²`, for `0 ≤ a ≤ b`. These are statements
for smooth path segments and a supplied variation; they do not assert minimizer existence or a
pointwise Euler–Lagrange equation.

## References

* J. Morgan and G. Tian, *Ricci Flow and the Poincaré Conjecture*, Chapters 6–7.
* The reduced-action development in `frenzymath/lean-eval-submissions` and
  `frenzymath/PoincareConjecture`.
-/

public section

open Bundle CovariantDerivative Filter MeasureTheory Set
open scoped ContDiff Manifold Topology

noncomputable section

namespace TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {F : ℝ → ℝ → M}
  {g : ℝ → ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)}

variable [T2Space M]

variable (I g) in
/-- Perelman's backward path action, with the metric evaluated at `T - τ`. -/
def backwardReducedAction (T : ℝ) (γ : ℝ → M) (a b : ℝ) : ℝ :=
  ∫ τ in a..b, Real.sqrt τ * ((g (T - τ)).scalarCurvature (γ τ) +
    (g (T - τ)).inner (γ τ) (curveVelocity I γ τ) (curveVelocity I γ τ))

variable (I g) in
/-- The square-time reduced action, whose kinetic density is regular at square time zero. -/
def regularizedReducedAction (T : ℝ) (α : ℝ → M) (a b : ℝ) : ℝ :=
  ∫ s in a..b, (g (T - s ^ 2)).inner (α s) (curveVelocity I α s) (curveVelocity I α s) / 2 +
    2 * s ^ 2 * (g (T - s ^ 2)).scalarCurvature (α s)

variable (I g) in
/-- The defining integral of the backward reduced action. -/
@[simp] theorem backwardReducedAction_def (T : ℝ) (γ : ℝ → M) (a b : ℝ) :
    backwardReducedAction I g T γ a b =
      ∫ τ in a..b, Real.sqrt τ * ((g (T - τ)).scalarCurvature (γ τ) +
        (g (T - τ)).inner (γ τ) (curveVelocity I γ τ) (curveVelocity I γ τ)) := by
  rfl

variable (I g) in
/-- The defining integral of the regularized reduced action. -/
@[simp] theorem regularizedReducedAction_def (T : ℝ) (α : ℝ → M) (a b : ℝ) :
    regularizedReducedAction I g T α a b =
      ∫ s in a..b, (g (T - s ^ 2)).inner (α s) (curveVelocity I α s)
        (curveVelocity I α s) / 2 + 2 * s ^ 2 * (g (T - s ^ 2)).scalarCurvature (α s) := by
  rfl

/-- Square-time pullback preserves the metric and scalar-potential regularity along the path. -/
private theorem regularized_family_regularity {s T : ℝ}
    (hg : ContMDiffAt (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) 1
      (fun p : ℝ × M ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
        p.2 ((g p.1).inner p.2)) (T - s ^ 2, F 0 s))
    (hR : ContMDiffAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1
      (fun p : ℝ × M ↦ (g p.1).scalarCurvature p.2) (T - s ^ 2, F 0 s)) :
    ContMDiffAt (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) 1
      (fun p : ℝ × M ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
        p.2 ((g (T - p.1 ^ 2)).inner p.2)) (s, F 0 s) ∧
    ContMDiffAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1
      (fun p : ℝ × M ↦ 2 * p.1 ^ 2 * (g (T - p.1 ^ 2)).scalarCurvature p.2) (s, F 0 s) := by
  have htime : ContMDiff (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod I) 1
      (fun p : ℝ × M ↦ (T - p.1 ^ 2, p.2)) :=
    (contMDiff_const.sub (contMDiff_fst.pow 2)).prodMk contMDiff_snd
  exact ⟨hg.comp (s, F 0 s) (htime (s, F 0 s)),
    (contMDiffAt_const.mul (contMDiffAt_fst.pow 2)).mul
      (hR.comp (s, F 0 s) (htime (s, F 0 s)))⟩

/-- The first variation of the regularized reduced action, with both endpoint momenta,
under the actual forward Ricci equation contracted with the variation field and velocity. -/
theorem hasDerivAt_regularizedReducedAction {a b T : ℝ}
    (hF : ∀ s ∈ uIcc a b,
      ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 2 (fun z : ℝ × ℝ ↦ F z.1 z.2) (0, s))
    (hg : ∀ s ∈ uIcc a b,
      ContMDiffAt (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) 1
        (fun p : ℝ × M ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
          (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
          p.2 ((g p.1).inner p.2)) (T - s ^ 2, F 0 s))
    (hR : ∀ s ∈ uIcc a b,
      ContMDiffAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1
        (fun p : ℝ × M ↦ (g p.1).scalarCurvature p.2) (T - s ^ 2, F 0 s))
    (hflow : ∀ s ∈ uIcc a b,
      HasDerivAt (fun r ↦ (g r).inner (F 0 s) (variationField I F s)
        (curveVelocity I (F 0) s))
        (-2 * (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
          ⟨(g (T - s ^ 2)).toRiemannianMetric⟩;
          (leviCivitaConnection I M).ricciTensor (F 0 s) (variationField I F s)
            (curveVelocity I (F 0) s))) (T - s ^ 2)) :
    HasDerivAt (fun u ↦ regularizedReducedAction I g T (F u) a b)
      ((g (T - b ^ 2)).inner (F 0 b) (variationField I F b) (curveVelocity I (F 0) b) -
        (g (T - a ^ 2)).inner (F 0 a) (variationField I F a) (curveVelocity I (F 0) a) -
        ∫ s in a..b,
          letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
            ⟨(g (T - s ^ 2)).toRiemannianMetric⟩
          inner ℝ (variationField I F s) (acceleration (leviCivitaConnection I M) (F 0) s) +
            4 * s * (leviCivitaConnection I M).ricciTensor (F 0 s) (variationField I F s)
              (curveVelocity I (F 0) s) -
            2 * s ^ 2 * mvfderiv I (g (T - s ^ 2)).scalarCurvature (F 0 s)
              (variationField I F s)) 0 := by
  let G := fun s ↦ g (T - s ^ 2)
  let U := fun (s : ℝ) (x : M) ↦ 2 * s ^ 2 * (G s).scalarCurvature x
  have hregular := fun s hs ↦ regularized_family_regularity (hg s hs) (hR s hs)
  have hG := fun s hs ↦ (hregular s hs).1
  have hU := fun s hs ↦ (hregular s hs).2
  have hpair : ∀ s ∈ uIcc a b,
      HasDerivAt (fun r ↦ (G r).inner (F 0 s) (variationField I F s)
        (curveVelocity I (F 0) s))
        (4 * s * (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
          ⟨(G s).toRiemannianMetric⟩;
          (leviCivitaConnection I M).ricciTensor (F 0 s) (variationField I F s)
            (curveVelocity I (F 0) s))) s := by
    intro s hs
    apply ((hflow s hs).comp s ((hasDerivAt_pow 2 s).const_sub T)).congr_deriv
    ring
  have h := hasDerivAt_movingMetricAction (g := fun s ↦ (G s).ofLE (by norm_num))
    (U := U) hF (by simpa only [ContMDiffRiemannianMetric.ofLE_inner] using hG) hU
    (by simpa only [ContMDiffRiemannianMetric.ofLE_inner,
      ContMDiffRiemannianMetric.toRiemannianMetric_ofLE] using hpair)
  simp only [movingMetricAction_def, ContMDiffRiemannianMetric.ofLE_inner] at h
  refine h.congr_deriv ?_
  congr 1
  apply intervalIntegral.integral_congr
  intro s _
  -- The local potential abbreviation must be opened before applying scalar linearity.
  change _ - mvfderiv I (fun x ↦ 2 * s ^ 2 * (G s).scalarCurvature x)
    (F 0 s) (variationField I F s) = _
  have hv : mvfderiv I (fun x ↦ 2 * s ^ 2 * (G s).scalarCurvature x)
      (F 0 s) (variationField I F s) =
      2 * s ^ 2 * mvfderiv I (G s).scalarCurvature (F 0 s) (variationField I F s) := by
    rw [show (fun x ↦ 2 * s ^ 2 * (G s).scalarCurvature x) =
        (2 * s ^ 2) • (G s).scalarCurvature from rfl,
      TauCeti.mvfderiv_const_smul_field (R := ℝ), smul_apply, smul_eq_mul]
  rw [hv]
  simp only [G]
  congr 1
  · congr 1
    simp only [ContMDiffRiemannianMetric.inner_eq,
      ContMDiffRiemannianMetric.ofLE_inner]
    -- Compare the installed bundles before transporting the proof-dependent connection.
    have hconn :
        (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
          ⟨((G s).ofLE (m := 1) (by norm_num)).toRiemannianMetric⟩;
          leviCivitaConnection I M) =
        (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
          ⟨(G s).toRiemannianMetric⟩; leviCivitaConnection I M) := by
      congr! 1
      exact congrArg RiemannianBundle.mk
        (ContMDiffRiemannianMetric.toRiemannianMetric_ofLE (G s) _)
    exact congrArg (fun cov : CovariantDerivative I E (TangentSpace I) ↦
      (G s).inner (F 0 s) (variationField I F s) (acceleration cov (F 0) s)) hconn

/-- Square-time substitution identifies the backward action of `α ∘ sqrt` on `a²..b²`
with the regularized action of `α` on `a..b`, allowing `a = 0`. -/
theorem backwardReducedAction_comp_sqrt {α : ℝ → M} {a b T : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b)
    (hα : ∀ s ∈ Ioo a b, MDifferentiableAt 𝓘(ℝ, ℝ) I α s) :
    backwardReducedAction I g T (α ∘ Real.sqrt) (a ^ 2) (b ^ 2) =
      regularizedReducedAction I g T α a b := by
  let L : ℝ → ℝ := fun τ ↦ Real.sqrt τ * ((g (T - τ)).scalarCurvature (α (Real.sqrt τ)) +
    (g (T - τ)).inner (α (Real.sqrt τ))
      (curveVelocity I (α ∘ Real.sqrt) τ) (curveVelocity I (α ∘ Real.sqrt) τ))
  have hpow : ContinuousOn (fun s : ℝ ↦ s ^ 2) (uIcc a b) :=
    continuousOn_pow 2
  have hderiv : ∀ s ∈ Ioo (min a b) (max a b),
      HasDerivAt (fun r : ℝ ↦ r ^ 2) (2 * s) s := by
    intro s _
    simpa using hasDerivAt_pow 2 s
  have hnonneg : ∀ s ∈ Ioo (min a b) (max a b), 0 ≤ 2 * s := by
    intro s hs
    have hspos : 0 < s := ha.trans_lt (by simpa [min_eq_left hab] using hs.1)
    exact mul_nonneg (by norm_num) hspos.le
  have hsub := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
    (a := a) (b := b) (f := fun s : ℝ ↦ s ^ 2) (f' := fun s ↦ 2 * s) (g := L)
    hpow hderiv hnonneg
  rw [backwardReducedAction_def]
  -- The local density `L` is precisely the backward-action integrand.
  change (∫ τ in a ^ 2..b ^ 2, L τ) = _
  rw [← hsub]
  apply intervalIntegral.integral_congr_Ioo_of_le hab
  intro s hs
  have hspos : 0 < s := ha.trans_lt hs.1
  have hsqrt : Real.sqrt (s ^ 2) = s := Real.sqrt_sq hspos.le
  have hα' : MDifferentiableAt 𝓘(ℝ, ℝ) I α (Real.sqrt (s ^ 2)) := by
    simpa only [hsqrt] using hα s hs
  have hvel : curveVelocity I (α ∘ Real.sqrt) (s ^ 2) =
      (1 / (2 * s)) • curveVelocity I α s := by
    have h := curveVelocity_comp
      (Real.hasDerivAt_sqrt (ne_of_gt (sq_pos_of_pos hspos))) hα'
    -- Function composition and the square-time point are hidden by the native chain rule.
    change curveVelocity I (α ∘ Real.sqrt) (s ^ 2) =
      (1 / (2 * Real.sqrt (s ^ 2))) • curveVelocity I α (Real.sqrt (s ^ 2)) at h
    rw [hsqrt] at h
    exact h
  dsimp only [L, Function.comp_apply]
  rw [hsqrt, hvel]
  simp only [map_smul, smul_apply, smul_eq_mul]
  field_simp [ne_of_gt hspos]
  ring

/-- For a fixed-endpoint variation, both momentum terms vanish in the reduced first variation. -/
theorem IsFixedEndpointVariation.hasDerivAt_regularizedReducedAction {a b T : ℝ}
    (hF : IsFixedEndpointVariation I 2 F a b)
    (hg : ∀ s ∈ uIcc a b,
      ContMDiffAt (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) 1
        (fun p : ℝ × M ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
          (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
          p.2 ((g p.1).inner p.2)) (T - s ^ 2, F 0 s))
    (hR : ∀ s ∈ uIcc a b,
      ContMDiffAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1
        (fun p : ℝ × M ↦ (g p.1).scalarCurvature p.2) (T - s ^ 2, F 0 s))
    (hflow : ∀ s ∈ uIcc a b,
      HasDerivAt (fun r ↦ (g r).inner (F 0 s) (variationField I F s)
        (curveVelocity I (F 0) s))
        (-2 * (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
          ⟨(g (T - s ^ 2)).toRiemannianMetric⟩;
          (leviCivitaConnection I M).ricciTensor (F 0 s) (variationField I F s)
            (curveVelocity I (F 0) s))) (T - s ^ 2)) :
    HasDerivAt (fun u ↦ regularizedReducedAction I g T (F u) a b)
      (-∫ s in a..b,
          letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
            ⟨(g (T - s ^ 2)).toRiemannianMetric⟩
          inner ℝ (variationField I F s) (acceleration (leviCivitaConnection I M) (F 0) s) +
            4 * s * (leviCivitaConnection I M).ricciTensor (F 0 s) (variationField I F s)
              (curveVelocity I (F 0) s) -
            2 * s ^ 2 * mvfderiv I (g (T - s ^ 2)).scalarCurvature (F 0 s)
              (variationField I F s)) 0 := by
  refine (TauCeti.Manifold.hasDerivAt_regularizedReducedAction
    hF.contMDiffAt hg hR hflow).congr_deriv ?_
  rw [hF.variationField_left_eq_zero, hF.variationField_right_eq_zero]
  simp only [map_zero, zero_apply, sub_self, zero_sub]

/-- At a local minimum of the regularized action along a fixed-endpoint variation,
the integral of the reduced Euler–Lagrange pairing with its variation field vanishes. -/
theorem IsFixedEndpointVariation.integral_eq_zero_of_isLocalMin_regularizedReducedAction {a b T : ℝ}
    (hF : IsFixedEndpointVariation I 2 F a b)
    (hg : ∀ s ∈ uIcc a b,
      ContMDiffAt (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) 1
        (fun p : ℝ × M ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
          (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
          p.2 ((g p.1).inner p.2)) (T - s ^ 2, F 0 s))
    (hR : ∀ s ∈ uIcc a b,
      ContMDiffAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1
        (fun p : ℝ × M ↦ (g p.1).scalarCurvature p.2) (T - s ^ 2, F 0 s))
    (hflow : ∀ s ∈ uIcc a b,
      HasDerivAt (fun r ↦ (g r).inner (F 0 s) (variationField I F s)
        (curveVelocity I (F 0) s))
        (-2 * (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
          ⟨(g (T - s ^ 2)).toRiemannianMetric⟩;
          (leviCivitaConnection I M).ricciTensor (F 0 s) (variationField I F s)
            (curveVelocity I (F 0) s))) (T - s ^ 2))
    (hmin : IsLocalMin (fun u ↦ regularizedReducedAction I g T (F u) a b) 0) :
    (∫ s in a..b,
      letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
        ⟨(g (T - s ^ 2)).toRiemannianMetric⟩
      inner ℝ (variationField I F s) (acceleration (leviCivitaConnection I M) (F 0) s) +
        4 * s * (leviCivitaConnection I M).ricciTensor (F 0 s) (variationField I F s)
          (curveVelocity I (F 0) s) -
        2 * s ^ 2 * mvfderiv I (g (T - s ^ 2)).scalarCurvature (F 0 s)
          (variationField I F s)) = 0 := by
  exact neg_eq_zero.mp (hmin.hasDerivAt_eq_zero
    (IsFixedEndpointVariation.hasDerivAt_regularizedReducedAction hF hg hR hflow))

/-- The backward action of the square-time reparametrized variation has the same intrinsic
first variation, including both endpoint momenta. This permits initial square time zero. -/
theorem hasDerivAt_backwardReducedAction_comp_sqrt {a b T : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b)
    (hF : ∀ s ∈ uIcc a b,
      ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 2 (fun z : ℝ × ℝ ↦ F z.1 z.2) (0, s))
    (hg : ∀ s ∈ uIcc a b,
      ContMDiffAt (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) 1
        (fun p : ℝ × M ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
          (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
          p.2 ((g p.1).inner p.2)) (T - s ^ 2, F 0 s))
    (hR : ∀ s ∈ uIcc a b,
      ContMDiffAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1
        (fun p : ℝ × M ↦ (g p.1).scalarCurvature p.2) (T - s ^ 2, F 0 s))
    (hflow : ∀ s ∈ uIcc a b,
      HasDerivAt (fun r ↦ (g r).inner (F 0 s) (variationField I F s)
        (curveVelocity I (F 0) s))
        (-2 * (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
          ⟨(g (T - s ^ 2)).toRiemannianMetric⟩;
          (leviCivitaConnection I M).ricciTensor (F 0 s) (variationField I F s)
            (curveVelocity I (F 0) s))) (T - s ^ 2)) :
    HasDerivAt (fun u ↦ backwardReducedAction I g T (F u ∘ Real.sqrt) (a ^ 2) (b ^ 2))
      ((g (T - b ^ 2)).inner (F 0 b) (variationField I F b) (curveVelocity I (F 0) b) -
        (g (T - a ^ 2)).inner (F 0 a) (variationField I F a) (curveVelocity I (F 0) a) -
        ∫ s in a..b,
          letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
            ⟨(g (T - s ^ 2)).toRiemannianMetric⟩
          inner ℝ (variationField I F s) (acceleration (leviCivitaConnection I M) (F 0) s) +
            4 * s * (leviCivitaConnection I M).ricciTensor (F 0 s) (variationField I F s)
              (curveVelocity I (F 0) s) -
            2 * s ^ 2 * mvfderiv I (g (T - s ^ 2)).scalarCurvature (F 0 s)
              (variationField I F s)) 0 := by
  apply (hasDerivAt_regularizedReducedAction hF hg hR hflow).congr_of_eventuallyEq
  filter_upwards [TauCeti.eventually_mdifferentiableAt_slice isCompact_uIcc
    (fun s hs ↦ (hF s hs).of_le (by norm_num))] with u hu
  exact backwardReducedAction_comp_sqrt ha hab fun s hs ↦ hu s (by
    rw [uIcc_of_le hab]
    exact ⟨hs.1.le, hs.2.le⟩)

/-- At a local minimum of the backward action of `F u ∘ sqrt`, the intrinsic reduced
Euler–Lagrange pairing integrates to zero against the supplied fixed-endpoint variation. -/
theorem IsFixedEndpointVariation.integral_eq_zero_of_isLocalMin_backwardReducedAction_comp_sqrt
    {a b T : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b)
    (hF : IsFixedEndpointVariation I 2 F a b)
    (hg : ∀ s ∈ uIcc a b,
      ContMDiffAt (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) 1
        (fun p : ℝ × M ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
          (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
          p.2 ((g p.1).inner p.2)) (T - s ^ 2, F 0 s))
    (hR : ∀ s ∈ uIcc a b,
      ContMDiffAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1
        (fun p : ℝ × M ↦ (g p.1).scalarCurvature p.2) (T - s ^ 2, F 0 s))
    (hflow : ∀ s ∈ uIcc a b,
      HasDerivAt (fun r ↦ (g r).inner (F 0 s) (variationField I F s)
        (curveVelocity I (F 0) s))
        (-2 * (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
          ⟨(g (T - s ^ 2)).toRiemannianMetric⟩;
          (leviCivitaConnection I M).ricciTensor (F 0 s) (variationField I F s)
            (curveVelocity I (F 0) s))) (T - s ^ 2))
    (hmin : IsLocalMin (fun u ↦ backwardReducedAction I g T (F u ∘ Real.sqrt) (a ^ 2) (b ^ 2)) 0) :
    (∫ s in a..b,
      letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
        ⟨(g (T - s ^ 2)).toRiemannianMetric⟩
      inner ℝ (variationField I F s) (acceleration (leviCivitaConnection I M) (F 0) s) +
        4 * s * (leviCivitaConnection I M).ricciTensor (F 0 s) (variationField I F s)
          (curveVelocity I (F 0) s) -
        2 * s ^ 2 * mvfderiv I (g (T - s ^ 2)).scalarCurvature (F 0 s)
          (variationField I F s)) = 0 := by
  apply hF.integral_eq_zero_of_isLocalMin_regularizedReducedAction hg hR hflow
  apply hmin.congr
  filter_upwards [TauCeti.eventually_mdifferentiableAt_slice isCompact_uIcc
    (fun s hs ↦ (hF.contMDiffAt s hs).of_le (by norm_num))] with u hu
  exact backwardReducedAction_comp_sqrt ha hab fun s hs ↦ hu s (by
    rw [uIcc_of_le hab]
    exact ⟨hs.1.le, hs.2.le⟩)

end TauCeti.Manifold
