/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Harmonic.Decay
public import TauCeti.Analysis.InnerProductSpace.Harmonic.Reflection
import TauCeti.Analysis.InnerProductSpace.Harmonic.Deriv
import TauCeti.MeasureTheory.Function.Lp.Norm
import TauCeti.MeasureTheory.Integral.Average
import TauCeti.MeasureTheory.Integral.Bochner.Basic

/-!
# Decay estimates for harmonic functions on half-balls

Let `H = normalHalfSpace a = {x | a < x.fst}` in the Euclidean product `ℝ × E`, of dimension `n`,
let `x₀` be a point of its boundary hyperplane `{a} × E`, and write `B_t⁺ = ball x₀ t ∩ H` for
the half-balls centred at `x₀`. This file proves the Campanato decay estimates on half-balls for
the gradient of a harmonic function vanishing on the flat part of the boundary. In the form
used for boundary regularity, `w` is weakly harmonic on `B_r⁺` and has zero boundary values on
`ball x₀ r ∩ ({a} × E)` in the Sobolev sense, with weak gradient `G`. Then for `0 ≤ t ≤ r`,

`∫_{B_t⁺} ‖G‖² ≤ 2ⁿ (t / r)ⁿ ∫_{B_r⁺} ‖G‖²`,

`∫_{B_t⁺} ‖G - m_t‖² ≤ 2^(3n + 8) (n + 1)² (t / r)^(n + 2) ∫_{B_r⁺} ‖G - (c, 0)‖²`

for every `c : ℝ`, where `m_t = ((G_t).fst, 0)` is the normal part of the average `G_t` of `G`
over `B_t⁺`. The constants are those of the interior estimates on balls.

Only constants normal to the hyperplane are compared with `G` on the right. The tangential
derivatives of `w` vanish on the flat boundary, so a tangential constant cannot approximate `G`
near `x₀`. The decay is therefore bounded by the square mean distance from `G` to the normal
constants on `B_r⁺`, not by the plain oscillation of `G` on `B_r⁺`, which also allows tangential
constants. The vector `m_t` is the best normal constant on `B_t⁺` in square mean
(`TauCeti.setIntegral_norm_sub_toLp_fst_setAverage_sq_le`), so the left-hand side, as a function
of `t`, is nondecreasing and dominates the square mean oscillation of `G` on `B_t⁺`. It is the
quantity iterated in Campanato's approach to Schauder estimates up to a flat boundary, where a
solution of Poisson's equation on a half-ball with zero boundary values is compared with its
harmonic replacement; the comparison step is
`InnerProductSpace.HarmonicOnNhd.setIntegral_ball_inter_normalHalfSpace_norm_sub_sq_le_add`.

## The argument

By the Schwarz reflection principle
(`TauCeti.WeaklyHarmonicOn.exists_harmonicOnNhd_ae_eq_of_inf_normalHalfSpace`) the odd reflection
of `w` is a harmonic function `h` on the whole ball `ball x₀ r`, with `∇h = G` on `B_r⁺`. Let
`ρ` be the reflection in `{a} × E` and `R` its linear part. Since `h ∘ ρ = -h`, the gradient
`K = ∇h`, which is harmonic, satisfies `K ∘ ρ = -R ∘ K`
(`TauCeti.gradient_normalReflection_of_forall_eq_neg`). For a normal vector `m` we have
`R m = -m`, so `‖K (ρ x) - m‖ = ‖K x - m‖`, and the ball `ball x₀ t` is invariant under `ρ`.
Hence each square integral over `ball x₀ t` is twice the one over `B_t⁺`
(`TauCeti.setIntegral_eq_two_smul_setIntegral_inter_normalHalfSpace`). The average of `K` over
`ball x₀ t` is a normal vector, because `ρ` preserves the ball and the measure. The interior decay
estimates on `ball x₀ t ⊆ ball x₀ r`
(`InnerProductSpace.HarmonicOnNhd.setIntegral_ball_norm_sq_le` and
`InnerProductSpace.HarmonicOnNhd.setIntegral_ball_norm_sub_setAverage_sq_le`) then give the
estimates on half-balls.

## Main declarations

* `InnerProductSpace.HarmonicOnNhd.setIntegral_ball_inter_normalHalfSpace_norm_sq_le`: decay of
  the `L²` mass on half-balls, with exponent `n`, for a harmonic function whose norm is invariant
  under `ρ`.
* `InnerProductSpace.HarmonicOnNhd.setIntegral_ball_inter_normalHalfSpace_norm_sub_sq_le`: decay
  of the `L²` distance to the best normal constant on half-balls, with exponent `n + 2`, for a
  harmonic vector field `K` with `K ∘ ρ = -R ∘ K`.
* `InnerProductSpace.HarmonicOnNhd.setIntegral_ball_inter_normalHalfSpace_norm_sub_sq_le_add`:
  the comparison step. A field close in `L²(B_r⁺)` to such a harmonic `K` inherits its decay, up
  to the distance between them.
* `TauCeti.WeaklyHarmonicOn.exists_harmonicOnNhd_ball_ae_eq`: the weak gradient of a weakly
  harmonic function vanishing on the flat boundary agrees on `B_r⁺` with a harmonic field `K`
  on `ball x₀ r` with `K ∘ ρ = -R ∘ K`, to which the results above apply.
* `TauCeti.WeaklyHarmonicOn.setIntegral_ball_inter_normalHalfSpace_norm_sq_le` and
  `TauCeti.WeaklyHarmonicOn.setIntegral_ball_inter_normalHalfSpace_norm_sub_sq_le`: the two decay
  estimates for the weak gradient of a weakly harmonic function vanishing on the flat boundary.

## References

* M. Giaquinta, L. Martinazzi, *An Introduction to the Regularity Theory for Elliptic Systems,
  Harmonic Maps and Minimal Graphs*, 2nd ed., Section 5.1 and Section 5.4 (decay estimates at a
  flat boundary and boundary regularity by Campanato's method).
* S. Campanato, *Equazioni ellittiche del II ordine e spazi `𝓛^{(2,λ)}`*, Ann. Mat. Pura Appl.
  69 (1965), 321–381.
-/

public section

open InnerProductSpace MeasureTheory Metric Module Set TopologicalSpace
open scoped Gradient

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {a : ℝ}

/-! ### Harmonic fields on half-balls -/

section HalfBall

variable {x₀ : WithLp 2 (ℝ × E)} {r t : ℝ}

omit [MeasurableSpace E] [BorelSpace E] in
/-- If `K ∘ ρ = -R ∘ K` on the ball, the distance from `K` to a normal vector `(c, 0)` is
invariant under the reflection `ρ`. -/
private theorem norm_comp_normalReflection_sub_toLp {K : WithLp 2 (ℝ × E) → WithLp 2 (ℝ × E)}
    (hodd : ∀ x ∈ ball x₀ r, K (normalReflection E a x) = -normalLinearReflection E (K x))
    {x : WithLp 2 (ℝ × E)} (hx : x ∈ ball x₀ r) (c : ℝ) :
    ‖K (normalReflection E a x) - WithLp.toLp 2 (c, 0)‖ = ‖K x - WithLp.toLp 2 (c, 0)‖ := by
  rw [hodd x hx, ← (normalLinearReflection E).norm_map (K x - WithLp.toLp 2 (c, 0)),
    ← norm_neg (normalLinearReflection E (K x - WithLp.toLp 2 (c, 0)))]
  congr 1
  obtain ⟨⟨s, y⟩⟩ := K x
  simp only [normalLinearReflection_apply, WithLp.toLp_fst, WithLp.toLp_snd, ← WithLp.toLp_sub,
    ← WithLp.toLp_neg, Prod.mk_sub_mk, Prod.neg_mk, sub_zero, neg_neg, neg_sub]

/-- If `K ∘ ρ = -R ∘ K` on `ball x₀ r` with `x₀` on the hyperplane, the average of `K` over a
smaller concentric ball is normal to the hyperplane. -/
private theorem setAverage_ball_eq_toLp_fst {K : WithLp 2 (ℝ × E) → WithLp 2 (ℝ × E)}
    (hx₀ : x₀.fst = a)
    (hodd : ∀ x ∈ ball x₀ r, K (normalReflection E a x) = -normalLinearReflection E (K x))
    (htr : t ≤ r) :
    ⨍ x in ball x₀ t, K x = WithLp.toLp 2 ((⨍ x in ball x₀ t, K x).fst, 0) := by
  -- Changing variables by `ρ`, which maps the ball onto itself, the integral `m` of `K` over the
  -- ball satisfies `m = -R m`.
  have hpre : normalReflection E a ⁻¹' ball x₀ t = ball x₀ t :=
    Subset.antisymm (fun x hx =>
      normalReflection_normalReflection a x ▸ mapsTo_normalReflection_ball hx₀ t hx)
      (mapsTo_normalReflection_ball hx₀ t)
  have hcv : ∫ x in ball x₀ t, K (normalReflection E a x) = ∫ x in ball x₀ t, K x := by
    conv_lhs => rw [← hpre]
    exact (measurePreserving_normalReflection a).setIntegral_preimage_emb
      (normalReflection E a).toHomeomorph.measurableEmbedding K (ball x₀ t)
  have hneg : ∫ x in ball x₀ t, K (normalReflection E a x) =
      -normalLinearReflection E (∫ x in ball x₀ t, K x) := by
    rw [setIntegral_congr_fun measurableSet_ball fun x hx => hodd x (ball_subset_ball htr hx),
      integral_neg, neg_inj]
    exact (normalLinearReflection E).toLinearIsometry.integral_comp_comm K
  have hsnd : (∫ x in ball x₀ t, K x).snd = 0 := by
    have h := congrArg WithLp.snd (hcv.symm.trans hneg)
    simp only [WithLp.neg_snd, normalLinearReflection_apply, WithLp.toLp_snd] at h
    generalize (∫ x in ball x₀ t, K x).snd = v at h ⊢
    have h2 : (2 : ℝ) • v = 0 := by
      rw [two_smul]
      nth_rewrite 2 [h]
      exact add_neg_cancel v
    exact (smul_eq_zero.1 h2).resolve_left two_ne_zero
  have havg : (⨍ x in ball x₀ t, K x).snd = 0 := by
    rw [setAverage_eq, WithLp.smul_snd, hsnd, smul_zero]
  apply WithLp.ofLp_injective
  ext
  · simp
  · simpa using havg

end HalfBall

end TauCeti

namespace InnerProductSpace.HarmonicOnNhd

open MeasureTheory Metric Module Set TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {a : ℝ} {x₀ : WithLp 2 (ℝ × E)} {r t : ℝ}

/-- **Decay of the `L²` mass on half-balls.** Let `x₀` lie on the hyperplane `{a} × E` and let
`u` be harmonic on `ball x₀ r`, with `‖u‖` invariant under the reflection `ρ` in the hyperplane,
as for a harmonic function that is odd or even under `ρ`, and with `‖u‖²` integrable on
`ball x₀ r ∩ H`. Then for every `0 ≤ t ≤ r`,

`∫_{ball x₀ t ∩ H} ‖u‖² ≤ 2ⁿ (t / r)ⁿ ∫_{ball x₀ r ∩ H} ‖u‖²`,

where `n` is the dimension of `ℝ × E`. -/
theorem setIntegral_ball_inter_normalHalfSpace_norm_sq_le
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {u : WithLp 2 (ℝ × E) → F} (hu : HarmonicOnNhd u (ball x₀ r)) (hx₀ : x₀.fst = a)
    (hsymm : ∀ x ∈ ball x₀ r, ‖u (normalReflection E a x)‖ = ‖u x‖)
    (hint : IntegrableOn (fun x => ‖u x‖ ^ 2) (ball x₀ r ∩ (normalHalfSpace (E := E) a : Set _)))
    (ht : 0 ≤ t) (htr : t ≤ r) :
    ∫ x in ball x₀ t ∩ (normalHalfSpace (E := E) a : Set _), ‖u x‖ ^ 2 ≤
      2 ^ finrank ℝ (WithLp 2 (ℝ × E)) * (t / r) ^ finrank ℝ (WithLp 2 (ℝ × E)) *
        ∫ x in ball x₀ r ∩ (normalHalfSpace (E := E) a : Set _), ‖u x‖ ^ 2 := by
  have hsq (s : ℝ) (hs : s ≤ r) : ∀ x ∈ ball x₀ s, ‖u (normalReflection E a x)‖ ^ 2 = ‖u x‖ ^ 2 :=
    fun x hx => by rw [hsymm x (ball_subset_ball hs hx)]
  have hintt : IntegrableOn (fun x => ‖u x‖ ^ 2)
      (ball x₀ t ∩ (normalHalfSpace (E := E) a : Set _)) :=
    hint.mono_set (inter_subset_inter_left _ (ball_subset_ball htr))
  have hdecay := hu.setIntegral_ball_norm_sq_le (μ := volume)
    (integrableOn_of_integrableOn_inter_normalHalfSpace measurableSet_ball
      (mapsTo_normalReflection_ball hx₀ r) (hsq r le_rfl) hint) ht htr
  rw [setIntegral_eq_two_smul_setIntegral_inter_normalHalfSpace measurableSet_ball
      (mapsTo_normalReflection_ball hx₀ t) (hsq t htr) hintt,
    setIntegral_eq_two_smul_setIntegral_inter_normalHalfSpace measurableSet_ball
      (mapsTo_normalReflection_ball hx₀ r) (hsq r le_rfl) hint, smul_eq_mul, smul_eq_mul] at hdecay
  linarith

/-- **Decay on half-balls of the distance to the best normal constant.** Let `x₀` lie on the
hyperplane `{a} × E`, and let `K` be a harmonic vector field on `ball x₀ r` which transforms
under the reflection `ρ` in the hyperplane by minus its linear part `R`, `K ∘ ρ = -R ∘ K`, as the
gradient of a harmonic function odd under `ρ` does. Write `B_s⁺ = ball x₀ s ∩ H`. If
`‖K - (c, 0)‖²` is integrable on `B_r⁺`, then for every `0 ≤ t ≤ r`,

`∫_{B_t⁺} ‖K - m_t‖² ≤ 2^(3n + 8) (n + 1)² (t / r)^(n + 2) ∫_{B_r⁺} ‖K - (c, 0)‖²`,

where `m_t = ((K_t).fst, 0)` is the normal part of the average `K_t` of `K` over `B_t⁺`, and `n`
is the dimension of `ℝ × E`. -/
theorem setIntegral_ball_inter_normalHalfSpace_norm_sub_sq_le
    {K : WithLp 2 (ℝ × E) → WithLp 2 (ℝ × E)} (hK : HarmonicOnNhd K (ball x₀ r))
    (hx₀ : x₀.fst = a)
    (hodd : ∀ x ∈ ball x₀ r, K (normalReflection E a x) = -normalLinearReflection E (K x))
    {c : ℝ} (hint : IntegrableOn (fun x => ‖K x - WithLp.toLp 2 (c, 0)‖ ^ 2)
      (ball x₀ r ∩ (normalHalfSpace (E := E) a : Set _)))
    (ht : 0 ≤ t) (htr : t ≤ r) :
    ∫ x in ball x₀ t ∩ (normalHalfSpace (E := E) a : Set _),
        ‖K x - WithLp.toLp 2
          ((⨍ y in ball x₀ t ∩ (normalHalfSpace (E := E) a : Set _), K y).fst, 0)‖ ^ 2 ≤
      2 ^ (3 * finrank ℝ (WithLp 2 (ℝ × E)) + 8) * (finrank ℝ (WithLp 2 (ℝ × E)) + 1) ^ 2 *
        (t / r) ^ (finrank ℝ (WithLp 2 (ℝ × E)) + 2) *
          ∫ x in ball x₀ r ∩ (normalHalfSpace (E := E) a : Set _),
            ‖K x - WithLp.toLp 2 (c, 0)‖ ^ 2 := by
  have hsq (d s : ℝ) (hs : s ≤ r) : ∀ x ∈ ball x₀ s,
      ‖K (normalReflection E a x) - WithLp.toLp 2 (d, 0)‖ ^ 2 =
        ‖K x - WithLp.toLp 2 (d, 0)‖ ^ 2 := fun x hx => by
    rw [norm_comp_normalReflection_sub_toLp hodd (ball_subset_ball hs hx)]
  have hintB : IntegrableOn (fun x => ‖K x - WithLp.toLp 2 (c, 0)‖ ^ 2) (ball x₀ r) :=
    integrableOn_of_integrableOn_inter_normalHalfSpace measurableSet_ball
      (mapsTo_normalReflection_ball hx₀ r) (hsq c r le_rfl) hint
  -- `K` is square integrable on the ball.
  have hmem : MemLp K 2 (volume.restrict (ball x₀ r)) := by
    have : IsFiniteMeasure (volume.restrict (ball x₀ r)) :=
      isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
    have hm : AEStronglyMeasurable (fun x => K x - WithLp.toLp 2 (c, 0))
        (volume.restrict (ball x₀ r)) :=
      (hK.continuousOn.aestronglyMeasurable measurableSet_ball).sub aestronglyMeasurable_const
    simpa only [Pi.add_def, sub_add_cancel] using
      ((memLp_two_iff_integrable_sq_norm hm).2 hintB).add (memLp_const (WithLp.toLp 2 (c, 0)))
  have hsub : ball x₀ t ∩ (normalHalfSpace (E := E) a : Set _) ⊆ ball x₀ r :=
    inter_subset_left.trans (ball_subset_ball htr)
  have hfin : volume (ball x₀ t ∩ (normalHalfSpace (E := E) a : Set _)) ≠ ⊤ :=
    ((measure_mono inter_subset_left).trans_lt measure_ball_lt_top).ne
  -- Interior decay on the ball, where the average of `K` is normal.
  have hdecay := hK.setIntegral_ball_norm_sub_setAverage_sq_le (μ := volume) hintB ht htr
  rw [setAverage_ball_eq_toLp_fst hx₀ hodd htr] at hdecay
  set d := (⨍ x in ball x₀ t, K x).fst
  rw [setIntegral_eq_two_smul_setIntegral_inter_normalHalfSpace measurableSet_ball
      (mapsTo_normalReflection_ball hx₀ t) (hsq d t htr)
      (hmem.integrableOn_norm_sub_sq_of_subset hsub hfin _),
    setIntegral_eq_two_smul_setIntegral_inter_normalHalfSpace measurableSet_ball
      (mapsTo_normalReflection_ball hx₀ r) (hsq c r le_rfl) hint, smul_eq_mul, smul_eq_mul]
    at hdecay
  have hbest := setIntegral_norm_sub_toLp_fst_setAverage_sq_le hfin
    (hmem.mono_measure (Measure.restrict_mono hsub le_rfl)) d
  linarith

/-- **Comparison with a harmonic field on half-balls.** Let `x₀` lie on the hyperplane `{a} × E`
and let `K` be harmonic on `ball x₀ r` with `K ∘ ρ = -R ∘ K`, where `ρ` is the reflection in the
hyperplane and `R` its linear part. Let `f` and `K` be square integrable on `B_r⁺ = ball x₀ r ∩ H`.
For `0 ≤ t ≤ r`, the square distance `φ(s) = ∫_{B_s⁺} ‖f - ((f_s).fst, 0)‖²` of `f` to its best
normal constant on `B_s⁺`, where `f_s` is the average of `f` over `B_s⁺`, decays like that of
`K`, up to the distance `∫_{B_r⁺} ‖f - K‖²` between them:

`φ(t) ≤ 4D (t / r)^(n + 2) φ(r) + (4D + 2) ∫_{B_r⁺} ‖f - K‖²`,

where `D = 2^(3n + 8) (n + 1)²` and `n` is the dimension of `ℝ × E`. -/
theorem setIntegral_ball_inter_normalHalfSpace_norm_sub_sq_le_add
    {K f : WithLp 2 (ℝ × E) → WithLp 2 (ℝ × E)} (hK : HarmonicOnNhd K (ball x₀ r))
    (hx₀ : x₀.fst = a)
    (hodd : ∀ x ∈ ball x₀ r, K (normalReflection E a x) = -normalLinearReflection E (K x))
    (hf : MemLp f 2 (volume.restrict (ball x₀ r ∩ (normalHalfSpace (E := E) a : Set _))))
    (hKm : MemLp K 2 (volume.restrict (ball x₀ r ∩ (normalHalfSpace (E := E) a : Set _))))
    (ht : 0 ≤ t) (htr : t ≤ r) :
    ∫ x in ball x₀ t ∩ (normalHalfSpace (E := E) a : Set _),
        ‖f x - WithLp.toLp 2
          ((⨍ y in ball x₀ t ∩ (normalHalfSpace (E := E) a : Set _), f y).fst, 0)‖ ^ 2 ≤
      4 * (2 ^ (3 * finrank ℝ (WithLp 2 (ℝ × E)) + 8) * (finrank ℝ (WithLp 2 (ℝ × E)) + 1) ^ 2) *
          (t / r) ^ (finrank ℝ (WithLp 2 (ℝ × E)) + 2) *
          (∫ x in ball x₀ r ∩ (normalHalfSpace (E := E) a : Set _),
            ‖f x - WithLp.toLp 2
              ((⨍ y in ball x₀ r ∩ (normalHalfSpace (E := E) a : Set _), f y).fst, 0)‖ ^ 2) +
        (4 * (2 ^ (3 * finrank ℝ (WithLp 2 (ℝ × E)) + 8) *
            (finrank ℝ (WithLp 2 (ℝ × E)) + 1) ^ 2) + 2) *
          ∫ x in ball x₀ r ∩ (normalHalfSpace (E := E) a : Set _), ‖f x - K x‖ ^ 2 := by
  have hsub : ball x₀ t ∩ (normalHalfSpace (E := E) a : Set _) ⊆
      ball x₀ r ∩ (normalHalfSpace (E := E) a : Set _) :=
    inter_subset_inter_left _ (ball_subset_ball htr)
  have hfinr : volume (ball x₀ r ∩ (normalHalfSpace (E := E) a : Set _)) ≠ ⊤ :=
    ((measure_mono inter_subset_left).trans_lt measure_ball_lt_top).ne
  have hfint : volume (ball x₀ t ∩ (normalHalfSpace (E := E) a : Set _)) ≠ ⊤ :=
    ((measure_mono hsub).trans_lt hfinr.lt_top).ne
  -- On `B_t⁺`, the best normal constant of `f` approximates `f` at least as well as that of `K`.
  have hbest := setIntegral_norm_sub_toLp_fst_setAverage_sq_le hfint
    (hf.mono_measure (Measure.restrict_mono hsub le_rfl))
    (⨍ y in ball x₀ t ∩ (normalHalfSpace (E := E) a : Set _), K y).fst
  -- The decay of `K` from `B_r⁺` to `B_t⁺`, measured against the best normal constant of `f`.
  exact MeasureTheory.setIntegral_norm_sub_sq_le_add_of_le hsub (by positivity)
    (pow_nonneg (div_nonneg ht (ht.trans htr)) _)
    (pow_le_one₀ (div_nonneg ht (ht.trans htr)) (div_le_one_of_le₀ htr (ht.trans htr)))
    (hf.integrableOn_norm_sub_sq_of_subset subset_rfl hfinr _)
    (hKm.integrableOn_norm_sub_sq_of_subset hsub hfint _)
    ((hf.sub hKm).integrable_norm_pow two_ne_zero) hbest
    (hK.setIntegral_ball_inter_normalHalfSpace_norm_sub_sq_le hx₀ hodd
      (hKm.integrableOn_norm_sub_sq_of_subset subset_rfl hfinr _) ht htr)

end InnerProductSpace.HarmonicOnNhd

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {a : ℝ}

/-! ### Weakly harmonic functions vanishing on the flat boundary -/

section WeaklyHarmonic

variable {U : Opens (WithLp 2 (ℝ × E))} {w : WithLp 2 (ℝ × E) → ℝ}
  {G : WithLp 2 (ℝ × E) → WithLp 2 (ℝ × E)} {x₀ : WithLp 2 (ℝ × E)} {r t : ℝ}

/-- **Harmonic representative of the weak gradient.** Let `w` be weakly harmonic on `U ∩ H`, where
`U` is an open set mapped into itself by the reflection `ρ` in `{a} × E`, with zero boundary
values on the flat part: `w` is weakly differentiable on `U` with weak gradient `G`, and `w` and
`G` vanish almost everywhere on `U` off `H`. If `ball x₀ r ⊆ U`, then `G` agrees almost
everywhere on `ball x₀ r ∩ H` with a harmonic field `K` on `ball x₀ r` satisfying
`K ∘ ρ = -R ∘ K`, where `R` is the linear part of `ρ`: the gradient of the odd reflection of `w`.
Such a `K` satisfies the hypotheses of the half-ball decay estimates for harmonic fields. -/
theorem WeaklyHarmonicOn.exists_harmonicOnNhd_ball_ae_eq
    (hharm : WeaklyHarmonicOn volume (U ⊓ normalHalfSpace a) w)
    (hU : MapsTo (normalReflection E a) U U)
    (hw : HasWeakFDerivOn volume U w fun x => innerSL ℝ (G x))
    (hG0 : ∀ᵐ x ∂volume.restrict U, x ∉ normalHalfSpace (E := E) a → G x = 0)
    (hw0 : ∀ᵐ x ∂volume.restrict U, x ∉ normalHalfSpace (E := E) a → w x = 0)
    (hball : ball x₀ r ⊆ U) :
    ∃ K : WithLp 2 (ℝ × E) → WithLp 2 (ℝ × E), HarmonicOnNhd K (ball x₀ r) ∧
      (∀ x ∈ ball x₀ r, K (normalReflection E a x) = -normalLinearReflection E (K x)) ∧
      K =ᵐ[volume.restrict (ball x₀ r ∩ (normalHalfSpace (E := E) a : Set _))] G := by
  obtain ⟨h, hh, hodd, -, hgrad⟩ :=
    hharm.exists_harmonicOnNhd_ae_eq_of_inf_normalHalfSpace hU hw hG0 hw0
  refine ⟨∇ h, (hh.mono hball).gradient, fun x hx => ?_, ?_⟩
  · have hρx : normalReflection E a x ∈ U := hU (hball hx)
    exact gradient_normalReflection_of_forall_eq_neg U.isOpen hodd (hball hx)
      ((hh _ hρx).1.differentiableAt (by norm_num))
  · refine ae_restrict_of_ae_restrict_of_subset ?_ hgrad
    rw [Opens.coe_inf]
    exact inter_subset_inter_left _ hball

/-- **Decay of the `L²` mass of the gradient on half-balls.** Let `w` be weakly harmonic on
`U ∩ H`, where `U` is an open set mapped into itself by the reflection `ρ` in `{a} × E`, with zero
boundary values on the flat part: `w` is weakly differentiable on `U` with weak gradient `G`, and
`w` and `G` vanish almost everywhere on `U` off `H`. If `x₀` lies on the hyperplane,
`ball x₀ r ⊆ U` and `‖G‖²` is integrable on `ball x₀ r ∩ H`, then for every `0 ≤ t ≤ r`,

`∫_{ball x₀ t ∩ H} ‖G‖² ≤ 2ⁿ (t / r)ⁿ ∫_{ball x₀ r ∩ H} ‖G‖²`,

where `n` is the dimension of `ℝ × E`. -/
theorem WeaklyHarmonicOn.setIntegral_ball_inter_normalHalfSpace_norm_sq_le
    (hharm : WeaklyHarmonicOn volume (U ⊓ normalHalfSpace a) w)
    (hU : MapsTo (normalReflection E a) U U)
    (hw : HasWeakFDerivOn volume U w fun x => innerSL ℝ (G x))
    (hG0 : ∀ᵐ x ∂volume.restrict U, x ∉ normalHalfSpace (E := E) a → G x = 0)
    (hw0 : ∀ᵐ x ∂volume.restrict U, x ∉ normalHalfSpace (E := E) a → w x = 0)
    (hx₀ : x₀.fst = a) (hball : ball x₀ r ⊆ U)
    (hint : IntegrableOn (fun x => ‖G x‖ ^ 2) (ball x₀ r ∩ (normalHalfSpace (E := E) a : Set _)))
    (ht : 0 ≤ t) (htr : t ≤ r) :
    ∫ x in ball x₀ t ∩ (normalHalfSpace (E := E) a : Set _), ‖G x‖ ^ 2 ≤
      2 ^ finrank ℝ (WithLp 2 (ℝ × E)) * (t / r) ^ finrank ℝ (WithLp 2 (ℝ × E)) *
        ∫ x in ball x₀ r ∩ (normalHalfSpace (E := E) a : Set _), ‖G x‖ ^ 2 := by
  obtain ⟨K, hK, hodd, hKG⟩ := hharm.exists_harmonicOnNhd_ball_ae_eq hU hw hG0 hw0 hball
  have hKGt : K =ᵐ[volume.restrict (ball x₀ t ∩ (normalHalfSpace (E := E) a : Set _))] G :=
    ae_restrict_of_ae_restrict_of_subset (inter_subset_inter_left _ (ball_subset_ball htr)) hKG
  have hsq (S : Set (WithLp 2 (ℝ × E))) (h : K =ᵐ[volume.restrict S] G) :
      ∫ x in S, ‖G x‖ ^ 2 = ∫ x in S, ‖K x‖ ^ 2 :=
    integral_congr_ae (h.mono fun x hx => by simp only [hx])
  rw [hsq _ hKG, hsq _ hKGt]
  refine hK.setIntegral_ball_inter_normalHalfSpace_norm_sq_le hx₀ (fun x hx => ?_)
    (hint.congr_fun_ae (hKG.mono fun x hx => by simp only [hx])) ht htr
  rw [hodd x hx, norm_neg, LinearIsometryEquiv.norm_map]

/-- **Decay of the gradient on half-balls.** Let `w` be weakly harmonic on `U ∩ H`, where `U` is
an open set mapped into itself by the reflection `ρ` in `{a} × E`, with zero boundary values on
the flat part: `w` is weakly differentiable on `U` with weak gradient `G`, and `w` and `G` vanish
almost everywhere on `U` off `H`. Write `B_s⁺ = ball x₀ s ∩ H`. If `x₀` lies on the hyperplane,
`ball x₀ r ⊆ U` and `‖G - (c, 0)‖²` is integrable on `B_r⁺`, then for every `0 ≤ t ≤ r`,

`∫_{B_t⁺} ‖G - m_t‖² ≤ 2^(3n + 8) (n + 1)² (t / r)^(n + 2) ∫_{B_r⁺} ‖G - (c, 0)‖²`,

where `m_t = ((G_t).fst, 0)` is the normal part of the average `G_t` of `G` over `B_t⁺`, and `n`
is the dimension of `ℝ × E`. -/
theorem WeaklyHarmonicOn.setIntegral_ball_inter_normalHalfSpace_norm_sub_sq_le
    (hharm : WeaklyHarmonicOn volume (U ⊓ normalHalfSpace a) w)
    (hU : MapsTo (normalReflection E a) U U)
    (hw : HasWeakFDerivOn volume U w fun x => innerSL ℝ (G x))
    (hG0 : ∀ᵐ x ∂volume.restrict U, x ∉ normalHalfSpace (E := E) a → G x = 0)
    (hw0 : ∀ᵐ x ∂volume.restrict U, x ∉ normalHalfSpace (E := E) a → w x = 0)
    (hx₀ : x₀.fst = a) (hball : ball x₀ r ⊆ U) {c : ℝ}
    (hint : IntegrableOn (fun x => ‖G x - WithLp.toLp 2 (c, 0)‖ ^ 2)
      (ball x₀ r ∩ (normalHalfSpace (E := E) a : Set _)))
    (ht : 0 ≤ t) (htr : t ≤ r) :
    ∫ x in ball x₀ t ∩ (normalHalfSpace (E := E) a : Set _),
        ‖G x - WithLp.toLp 2
          ((⨍ y in ball x₀ t ∩ (normalHalfSpace (E := E) a : Set _), G y).fst, 0)‖ ^ 2 ≤
      2 ^ (3 * finrank ℝ (WithLp 2 (ℝ × E)) + 8) * (finrank ℝ (WithLp 2 (ℝ × E)) + 1) ^ 2 *
        (t / r) ^ (finrank ℝ (WithLp 2 (ℝ × E)) + 2) *
          ∫ x in ball x₀ r ∩ (normalHalfSpace (E := E) a : Set _),
            ‖G x - WithLp.toLp 2 (c, 0)‖ ^ 2 := by
  obtain ⟨K, hK, hodd, hKG⟩ := hharm.exists_harmonicOnNhd_ball_ae_eq hU hw hG0 hw0 hball
  have hKGt : K =ᵐ[volume.restrict (ball x₀ t ∩ (normalHalfSpace (E := E) a : Set _))] G :=
    ae_restrict_of_ae_restrict_of_subset (inter_subset_inter_left _ (ball_subset_ball htr)) hKG
  have havg : ⨍ y in ball x₀ t ∩ (normalHalfSpace (E := E) a : Set _), G y =
      ⨍ y in ball x₀ t ∩ (normalHalfSpace (E := E) a : Set _), K y := by
    simp only [setAverage_eq]
    rw [integral_congr_ae hKGt]
  have hsq (S : Set (WithLp 2 (ℝ × E))) (h : K =ᵐ[volume.restrict S] G) (v : WithLp 2 (ℝ × E)) :
      ∫ x in S, ‖G x - v‖ ^ 2 = ∫ x in S, ‖K x - v‖ ^ 2 :=
    integral_congr_ae (h.mono fun x hx => by simp only [hx])
  rw [havg, hsq _ hKG, hsq _ hKGt]
  exact hK.setIntegral_ball_inter_normalHalfSpace_norm_sub_sq_le hx₀ hodd
    (hint.congr_fun_ae (hKG.mono fun x hx => by simp only [hx])) ht htr

end WeaklyHarmonic

end TauCeti
