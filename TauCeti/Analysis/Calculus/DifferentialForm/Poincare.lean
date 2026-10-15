/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.DifferentialForm.Basic
public import Mathlib.Analysis.Convex.Star
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.AddTorsor.AffineMap
import Mathlib.Analysis.Calculus.Deriv.AffineMap
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import TauCeti.Analysis.Calculus.ParametricIntegral
import TauCeti.Analysis.Normed.Module.Alternating.Uncurry.Fin
import TauCeti.MeasureTheory.Constructions.UnitInterval

/-!
# The Poincaré lemma for differential forms on star-convex open sets

Let `s` be an open subset of a real normed space `E`, star-convex with respect to a point `x₀`,
and let `ω` be a `C¹` differential `(n + 1)`-form on `s` with values in a Banach space `F`. The
*Poincaré homotopy operator* (`TauCeti.poincareHomotopy`) contracts `ω` along the rays from `x₀`:

`(K ω)(x)(v₁, …, vₙ) = ∫₀¹ tⁿ ω(x₀ + t (x - x₀))(x - x₀, v₁, …, vₙ) dt`.

It satisfies the homotopy formula `d (K ω) + K (d ω) = ω` on `s`
(`StarConvex.extDeriv_poincareHomotopy_add_poincareHomotopy_extDeriv`). Consequently every closed
`C¹` form of positive degree on `s` is exact: if `d ω = 0` on `s`, then `K ω` is a primitive of `ω`
(`StarConvex.extDeriv_poincareHomotopy`). The primitive is as smooth as `ω`
(`StarConvex.contDiffOn_poincareHomotopy`) and vanishes at `x₀` (`TauCeti.poincareHomotopy_self`).

Mathlib proves the Poincaré lemma for `1`-forms on convex sets by integrating along segments
(`Convex.exists_forall_hasFDerivAt_of_fderiv_symmetric`); this file treats forms of every
positive degree with Mathlib's exterior derivative `extDeriv`. A smooth primitive vanishing at the
centre of a ball is what Moser's deformation argument integrates, for instance in the proof of
Darboux's theorem.

The homotopy formula is the integral over `t ∈ [0, 1]` of the identity
`d/dt (tⁿ⁺¹ ω(x₀ + t (x - x₀))) = tⁿ⁺¹ Dω(…)(x - x₀) + (n + 1) tⁿ ω(…)`, after the derivative
term is split by the constant-coefficient Cartan formula
`ContinuousAlternatingMap.alternatizeUncurryFin_curryLeft_comp_add_curryLeft`.

## Main declarations

* `TauCeti.poincareHomotopy`: the Poincaré homotopy operator with centre `x₀`.
* `StarConvex.contDiffOn_poincareHomotopy`: it preserves `C^r` regularity on `s`.
* `StarConvex.extDeriv_poincareHomotopy_add_poincareHomotopy_extDeriv`: the homotopy formula.
* `StarConvex.extDeriv_poincareHomotopy` and `StarConvex.exists_contDiffOn_forall_extDeriv_eq`: the
  Poincaré lemma.

## References

* M. Spivak, *Calculus on Manifolds*, Theorem 4-11, whose proof uses this homotopy operator.
* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Chapter 17 (the Poincaré lemma).
-/

public section

noncomputable section

open AffineMap MeasureTheory Set
open scoped unitInterval

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {n : ℕ}

namespace TauCeti

/-- The **Poincaré homotopy operator** with centre `x₀`: the `n`-form
`x ↦ ∫₀¹ tⁿ ω(x₀ + t (x - x₀))(x - x₀, ·) dt` built from a differential `(n + 1)`-form `ω`.
When `ω` is `C¹` on an open set star-convex with respect to `x₀` and takes values in a Banach
space, it satisfies `d (K ω) + K (d ω) = ω` there. -/
def poincareHomotopy (x₀ : E) (ω : E → E [⋀^Fin (n + 1)]→L[ℝ] F) (x : E) :
    E [⋀^Fin n]→L[ℝ] F :=
  ∫ t in (0 : ℝ)..1, t ^ n • (ω (lineMap x₀ x t)).curryLeft (x - x₀)

theorem poincareHomotopy_apply (x₀ : E) (ω : E → E [⋀^Fin (n + 1)]→L[ℝ] F) (x : E) :
    poincareHomotopy x₀ ω x =
      ∫ t in (0 : ℝ)..1, t ^ n • (ω (lineMap x₀ x t)).curryLeft (x - x₀) :=
  (rfl)

/-- The Poincaré homotopy operator vanishes at its centre. -/
@[simp]
theorem poincareHomotopy_self (x₀ : E) (ω : E → E [⋀^Fin (n + 1)]→L[ℝ] F) :
    poincareHomotopy x₀ ω x₀ = 0 := by
  simp [poincareHomotopy_apply]

/-- The integrand of the homotopy operator is as smooth as the form, on the open set of pairs
`(x, t)` with `x₀ + t (x - x₀) ∈ s`. -/
private theorem contDiffOn_integrand {x₀ : E} {s : Set E} {ω : E → E [⋀^Fin (n + 1)]→L[ℝ] F}
    {r : WithTop ℕ∞} (hω : ContDiffOn ℝ r ω s) :
    ContDiffOn ℝ r (fun p : E × ℝ ↦ (ω (lineMap x₀ p.1 p.2)).curryLeft (p.1 - x₀))
      {p : E × ℝ | lineMap x₀ p.1 p.2 ∈ s} := by
  have hcomp : ContDiffOn ℝ r (fun p : E × ℝ ↦ ω (lineMap x₀ p.1 p.2))
      {p : E × ℝ | lineMap x₀ p.1 p.2 ∈ s} :=
    hω.comp (contDiff_const.lineMap contDiff_fst contDiff_snd).contDiffOn fun _ hp ↦ hp
  exact (ContinuousAlternatingMap.curryLeftLI (𝕜 := ℝ) (E := E) (F := F)
    (n := n)).toContinuousLinearMap.contDiff.comp_contDiffOn hcomp |>.clm_apply
      ((contDiff_fst.sub contDiff_const).contDiffOn)

/-- The partial derivative in `x` of the integrand of the homotopy operator. -/
private theorem hasFDerivAt_integrand {x₀ : E} {s : Set E} {ω : E → E [⋀^Fin (n + 1)]→L[ℝ] F}
    (hso : IsOpen s) (hω : ContDiffOn ℝ 1 ω s) {x : E} {t : ℝ} (hxt : lineMap x₀ x t ∈ s) :
    HasFDerivAt (fun x' ↦ (ω (lineMap x₀ x' t)).curryLeft (x' - x₀))
      (t • ((ContinuousAlternatingMap.curryLeftLI (𝕜 := ℝ) (E := E) (F := F)
          (n := n)).toContinuousLinearMap.flip (x - x₀) ∘L fderiv ℝ ω (lineMap x₀ x t)) +
        (ContinuousAlternatingMap.curryLeftLI (𝕜 := ℝ) (E := E) (F := F)
          (n := n)).toContinuousLinearMap (ω (lineMap x₀ x t))) x := by
  set L := (ContinuousAlternatingMap.curryLeftLI (𝕜 := ℝ) (E := E) (F := F)
    (n := n)).toContinuousLinearMap
  have hω' : HasFDerivAt ω (fderiv ℝ ω (lineMap x₀ x t)) (lineMap x₀ x t) :=
    ((hω.differentiableOn one_ne_zero _ hxt).differentiableAt
      (hso.mem_nhds hxt)).hasFDerivAt
  have hray : HasFDerivAt (fun x' ↦ lineMap x₀ x' t) (t • ContinuousLinearMap.id ℝ E) x := by
    simp only [lineMap_apply_module']
    exact (((hasFDerivAt_id x).sub_const x₀).const_smul t).add_const x₀
  refine (L.hasFDerivAt_of_bilinear (hω'.comp x hray)
    ((hasFDerivAt_id x).sub_const x₀)).congr_fderiv ?_
  ext h v
  simp [L, add_comm]

end TauCeti

open TauCeti

namespace StarConvex

variable {x₀ : E} {s : Set E} {ω : E → E [⋀^Fin (n + 1)]→L[ℝ] F}

/-- The Poincaré homotopy operator of a `C^r` form on an open star-convex set is `C^r` there. -/
theorem contDiffOn_poincareHomotopy (hs : StarConvex ℝ x₀ s) (hso : IsOpen s) {r : ℕ∞}
    (hω : ContDiffOn ℝ r ω s) : ContDiffOn ℝ r (poincareHomotopy x₀ ω) s := by
  have hpow : Integrable (fun t : I ↦ (t : ℝ) ^ n) volume :=
    (continuous_subtype_val.pow n).integrable_of_hasCompactSupport (.of_compactSpace _)
  refine (contDiffOn_integral_smul_of_contDiffOn (μ := (volume : Measure I))
    hpow continuous_subtype_val
    (hso.preimage (by fun_prop : Continuous fun p : E × ℝ ↦ lineMap x₀ p.1 p.2))
    (contDiffOn_integrand hω) hso fun x hx t ↦
      hs.segment_subset hx (lineMap_mem_segment ℝ x₀ x t.2)).congr
      fun x _ ↦ ?_
  rw [poincareHomotopy_apply, intervalIntegral_eq_integral_unitInterval]

variable [CompleteSpace F]

/-- The exterior derivative of the Poincaré homotopy operator, as an integral over `[0, 1]`. -/
private theorem extDeriv_poincareHomotopy_eq (hs : StarConvex ℝ x₀ s) (hso : IsOpen s)
    (hω : ContDiffOn ℝ 1 ω s) {x : E} (hx : x ∈ s) :
    extDeriv (poincareHomotopy x₀ ω) x =
      ∫ t in (0 : ℝ)..1, t ^ n •
        (t • ContinuousAlternatingMap.alternatizeUncurryFin
            ((ContinuousAlternatingMap.curryLeftLI (𝕜 := ℝ) (E := E) (F := F)
              (n := n)).toContinuousLinearMap.flip (x - x₀) ∘L fderiv ℝ ω (lineMap x₀ x t)) +
          (n + 1) • ω (lineMap x₀ x t)) := by
  have hW : IsOpen {p : E × ℝ | lineMap x₀ p.1 p.2 ∈ s} :=
    hso.preimage (by fun_prop : Continuous fun p : E × ℝ ↦ lineMap x₀ p.1 p.2)
  have hpow : Integrable (fun t : I ↦ (t : ℝ) ^ n) volume :=
    (continuous_subtype_val.pow n).integrable_of_hasCompactSupport (.of_compactSpace _)
  have hF := contDiffOn_integrand (x₀ := x₀) hω
  have hmem (t : I) : (x, (t : ℝ)) ∈ {p : E × ℝ | lineMap x₀ p.1 p.2 ∈ s} :=
    hs.segment_subset hx (lineMap_mem_segment ℝ x₀ x t.2)
  have h : HasFDerivAt
      (fun x ↦ ∫ t : I, (t : ℝ) ^ n • (ω (lineMap x₀ x (t : ℝ))).curryLeft (x - x₀))
      (∫ t : I, (t : ℝ) ^ n •
        fderiv ℝ (fun x' ↦ (ω (lineMap x₀ x' (t : ℝ))).curryLeft (x' - x₀)) x) x :=
    hasFDerivAt_integral_smul_of_contDiffOn (μ := (volume : Measure I))
      hpow continuous_subtype_val hW hF hmem
  have h' := h.congr_of_eventuallyEq (f₁ := poincareHomotopy x₀ ω) <|
    Filter.Eventually.of_forall fun x ↦ by
      rw [poincareHomotopy_apply, intervalIntegral_eq_integral_unitInterval]
  -- the derivative of the integrand is integrable, so the alternatization commutes with `∫`
  have hint := integrable_smul_of_continuousOn (μ := (volume : Measure I))
    hpow continuous_subtype_val
    ((hF.fderiv_partial_of_isOpen (m := 0) (by simpa using hW)).continuousOn) hmem
  calc extDeriv (poincareHomotopy x₀ ω) x
      = ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ E F (∫ t : I, (t : ℝ) ^ n •
          fderiv ℝ (fun x' ↦ (ω (lineMap x₀ x' (t : ℝ))).curryLeft (x' - x₀)) x) := by
        rw [extDeriv, h'.fderiv, ContinuousAlternatingMap.alternatizeUncurryFinCLM_apply]
    _ = ∫ t : I, ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ E F ((t : ℝ) ^ n •
          fderiv ℝ (fun x' ↦ (ω (lineMap x₀ x' (t : ℝ))).curryLeft (x' - x₀)) x) :=
        (ContinuousLinearMap.integral_comp_comm _ hint).symm
    _ = _ := by
        rw [intervalIntegral_eq_integral_unitInterval]
        refine integral_congr_ae (ae_of_all _ fun t ↦ ?_)
        dsimp only
        rw [(hasFDerivAt_integrand hso hω (hmem t)).fderiv]
        simp

/-- The fundamental theorem of calculus for `t ↦ tⁿ⁺¹ ω(x₀ + t (x - x₀))` on `[0, 1]`. -/
private theorem integral_pow_smul_fderiv_add_eq (hs : StarConvex ℝ x₀ s) (hso : IsOpen s)
    (hω : ContDiffOn ℝ 1 ω s) {x : E} (hx : x ∈ s) :
    ∫ t in (0 : ℝ)..1, (t ^ (n + 1) • fderiv ℝ ω (lineMap x₀ x t) (x - x₀) +
      ((n + 1 : ℝ) * t ^ n) • ω (lineMap x₀ x t)) = ω x := by
  have hmaps : MapsTo (lineMap x₀ x) (uIcc (0 : ℝ) 1) s := fun _ ht ↦
    hs.segment_subset hx (lineMap_mem_segment ℝ x₀ x (by rwa [uIcc_of_le zero_le_one] at ht))
  have hderiv (t : ℝ) (ht : t ∈ uIcc (0 : ℝ) 1) :
      HasDerivAt (fun t : ℝ ↦ t ^ (n + 1) • ω (lineMap x₀ x t))
        (t ^ (n + 1) • fderiv ℝ ω (lineMap x₀ x t) (x - x₀) +
          ((n + 1 : ℝ) * t ^ n) • ω (lineMap x₀ x t)) t := by
    have hmem := hmaps ht
    have hω' : HasFDerivAt ω (fderiv ℝ ω (lineMap x₀ x t)) (lineMap x₀ x t) :=
      ((hω.differentiableOn one_ne_zero _ hmem).differentiableAt (hso.mem_nhds hmem)).hasFDerivAt
    refine ((hasDerivAt_pow (n + 1) t).smul
      (hω'.comp_hasDerivAt t hasDerivAt_lineMap)).congr_deriv ?_
    simp
  have hint : IntervalIntegrable (fun t : ℝ ↦ t ^ (n + 1) • fderiv ℝ ω (lineMap x₀ x t) (x - x₀) +
      ((n + 1 : ℝ) * t ^ n) • ω (lineMap x₀ x t)) volume 0 1 :=
    (((continuousOn_pow (n + 1)).smul
      ((ContinuousLinearMap.apply ℝ _ (x - x₀)).continuous.comp_continuousOn
        ((hω.continuousOn_fderiv_of_isOpen hso le_rfl).comp lineMap_continuous.continuousOn
          hmaps))).add
      ((continuousOn_const.mul (continuousOn_pow n)).smul
        (hω.continuousOn.comp lineMap_continuous.continuousOn hmaps))).intervalIntegrable
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  simp

/-- **The homotopy formula** `d (K ω) + K (d ω) = ω` for the Poincaré homotopy operator `K` of a
`C¹` form on an open set star-convex with respect to the centre of `K`. -/
theorem extDeriv_poincareHomotopy_add_poincareHomotopy_extDeriv (hs : StarConvex ℝ x₀ s)
    (hso : IsOpen s) (hω : ContDiffOn ℝ 1 ω s) {x : E} (hx : x ∈ s) :
    extDeriv (poincareHomotopy x₀ ω) x + poincareHomotopy x₀ (extDeriv ω) x = ω x := by
  set L := (ContinuousAlternatingMap.curryLeftLI (𝕜 := ℝ) (E := E) (F := F)
    (n := n)).toContinuousLinearMap
  set y := x - x₀
  have hmaps : MapsTo (lineMap x₀ x) (uIcc (0 : ℝ) 1) s := fun _ ht ↦
    hs.segment_subset hx (lineMap_mem_segment ℝ x₀ x (by rwa [uIcc_of_le zero_le_one] at ht))
  have hDω_cont := (hω.continuousOn_fderiv_of_isOpen hso le_rfl).comp
    lineMap_continuous.continuousOn hmaps
  have hD_int : IntervalIntegrable (fun t : ℝ ↦ t ^ n •
      (t • ContinuousAlternatingMap.alternatizeUncurryFin
          (L.flip y ∘L fderiv ℝ ω (lineMap x₀ x t)) +
        (n + 1) • ω (lineMap x₀ x t))) volume 0 1 :=
    ContinuousOn.intervalIntegrable ((continuousOn_pow n).smul ((continuousOn_id.smul
      ((ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ E F).continuous.comp_continuousOn
        ((ContinuousLinearMap.compL ℝ E _ _ (L.flip y)).continuous.comp_continuousOn
          hDω_cont))).add
        ((hω.continuousOn.comp lineMap_continuous.continuousOn hmaps).const_smul _)))
  have hcurry := (((ContinuousAlternatingMap.curryLeftLI (𝕜 := ℝ) (E := E) (F := F)
    (n := n + 1)).toContinuousLinearMap.flip y).comp
      (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ E F)).continuous.comp_continuousOn
        hDω_cont
  have hdω_int : IntervalIntegrable (fun t : ℝ ↦ t ^ (n + 1) •
      (extDeriv ω (lineMap x₀ x t)).curryLeft y) volume 0 1 := by
    refine ContinuousOn.intervalIntegrable ((continuousOn_pow (n + 1)).smul ?_)
    refine hcurry.congr fun t _ ↦ ?_
    simp [extDeriv]
  rw [extDeriv_poincareHomotopy_eq hs hso hω hx, poincareHomotopy_apply,
    ← intervalIntegral.integral_add hD_int hdω_int, ← integral_pow_smul_fderiv_add_eq hs hso hω hx]
  -- pointwise, this is the constant-coefficient Cartan formula for `Dω` and `y = x - x₀`
  refine intervalIntegral.integral_congr fun t _ ↦ ?_
  have key := ContinuousAlternatingMap.alternatizeUncurryFin_curryLeft_comp_add_curryLeft
    (fderiv ℝ ω (lineMap x₀ x t)) y
  simp only [extDeriv, L]
  rw [← Nat.cast_smul_eq_nsmul ℝ]
  linear_combination (norm := module) t ^ (n + 1) • key

/-- **The Poincaré lemma.** On an open set star-convex with respect to `x₀`, the Poincaré
homotopy operator with centre `x₀` of a closed `C¹` form is a primitive of it. -/
theorem extDeriv_poincareHomotopy (hs : StarConvex ℝ x₀ s) (hso : IsOpen s)
    (hω : ContDiffOn ℝ 1 ω s) (hclosed : ∀ y ∈ s, extDeriv ω y = 0) {x : E} (hx : x ∈ s) :
    extDeriv (poincareHomotopy x₀ ω) x = ω x := by
  have h0 : poincareHomotopy x₀ (extDeriv ω) x = 0 := by
    rw [poincareHomotopy_apply]
    refine (intervalIntegral.integral_congr (g := fun _ ↦ 0) fun t ht ↦ ?_).trans
      intervalIntegral.integral_zero
    simp [hclosed _ (hs.segment_subset hx
      (lineMap_mem_segment ℝ x₀ x (by rwa [uIcc_of_le zero_le_one] at ht)))]
  simpa [h0] using hs.extDeriv_poincareHomotopy_add_poincareHomotopy_extDeriv hso hω hx

/-- **The Poincaré lemma.** A closed `C^r` form, `r ≥ 1`, on an open star-convex set is the
exterior derivative of a `C^r` form, which can be chosen to vanish at the centre. -/
theorem exists_contDiffOn_forall_extDeriv_eq (hs : StarConvex ℝ x₀ s) (hso : IsOpen s) {r : ℕ∞}
    (hr : 1 ≤ r) (hω : ContDiffOn ℝ r ω s) (hclosed : ∀ y ∈ s, extDeriv ω y = 0) :
    ∃ α : E → E [⋀^Fin n]→L[ℝ] F, ContDiffOn ℝ r α s ∧ α x₀ = 0 ∧
      ∀ x ∈ s, extDeriv α x = ω x :=
  ⟨poincareHomotopy x₀ ω, hs.contDiffOn_poincareHomotopy hso hω, poincareHomotopy_self x₀ ω,
    fun _ hx ↦ hs.extDeriv_poincareHomotopy hso (hω.of_le (by exact_mod_cast hr)) hclosed hx⟩

end StarConvex
