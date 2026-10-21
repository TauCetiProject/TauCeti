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
# The Poincaré lemma for differential forms on star-convex sets

Let `s` be an open subset of a real normed space `E`, star-convex with respect to a point `x₀`,
and let `ω` be a `C¹` differential `(n + 1)`-form on `s` with values in a Banach space `F`. The
*Poincaré homotopy operator* (`TauCeti.poincareHomotopy`) contracts `ω` along the rays from `x₀`:

`(K ω)(x)(v₁, …, vₙ) = ∫₀¹ tⁿ ω(x₀ + t (x - x₀))(x - x₀, v₁, …, vₙ) dt`.

It satisfies the homotopy formula `d (K ω) + K (d ω) = ω` on `s`
(`StarConvex.extDeriv_poincareHomotopy_add_poincareHomotopy_extDeriv`). Consequently every closed
`C¹` form of positive degree on `s` is exact: if `d ω = 0` on `s`, then `K ω` is a primitive of `ω`
(`StarConvex.extDeriv_poincareHomotopy`). The primitive is as smooth as `ω`
(`StarConvex.contDiffOn_poincareHomotopy`) and vanishes at `x₀` (`TauCeti.poincareHomotopy_self`).

The same holds relative to a convex set `s` with unique derivatives that need not be open, such as
a closed half-ball, the image of a boundary chart of a manifold with boundary. There the
derivatives are taken within `s`, and the homotopy formula reads
`extDerivWithin (K ω) s + K (extDerivWithin ω s) = ω` on `s`
(`Convex.extDerivWithin_poincareHomotopy_add_poincareHomotopy_extDerivWithin`). Differentiating
`K ω` within `s` uses Mathlib's mean value inequality along the segments of `s`, which is why the
relative statements ask for convexity rather than star-convexity.

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
* `Convex.contDiffOn_poincareHomotopy`,
  `Convex.extDerivWithin_poincareHomotopy_add_poincareHomotopy_extDerivWithin`,
  `Convex.extDerivWithin_poincareHomotopy` and `Convex.exists_contDiffOn_forall_extDerivWithin_eq`:
  the relative versions on convex sets with unique derivatives.

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

/-- The Poincaré homotopy operator at `x` only depends on the form along the segment `[x₀, x]`. -/
theorem poincareHomotopy_congr {x₀ x : E} {ω₁ ω₂ : E → E [⋀^Fin (n + 1)]→L[ℝ] F}
    (h : EqOn ω₁ ω₂ (segment ℝ x₀ x)) : poincareHomotopy x₀ ω₁ x = poincareHomotopy x₀ ω₂ x := by
  rw [poincareHomotopy_apply, poincareHomotopy_apply]
  refine intervalIntegral.integral_congr fun t ht ↦ ?_
  simp only [h (lineMap_mem_segment ℝ x₀ x (by rwa [uIcc_of_le zero_le_one] at ht))]

/-- The Poincaré homotopy operator of the zero form is zero. -/
@[simp]
theorem poincareHomotopy_zero (x₀ : E) :
    poincareHomotopy x₀ (0 : E → E [⋀^Fin (n + 1)]→L[ℝ] F) = 0 := by
  funext x
  simp [poincareHomotopy_apply]

/-- The Poincaré homotopy operator commutes with real scalar multiplication of forms. -/
theorem poincareHomotopy_smul (x₀ : E) (c : ℝ) (ω : E → E [⋀^Fin (n + 1)]→L[ℝ] F) :
    poincareHomotopy x₀ (c • ω) = c • poincareHomotopy x₀ ω := by
  funext x
  simp only [poincareHomotopy_apply, Pi.smul_apply, ContinuousAlternatingMap.curryLeft_smul,
    smul_apply, ← intervalIntegral.integral_smul, smul_comm c]

/-- The Poincaré homotopy operator is additive on forms that are continuous along the segment
`[x₀, x]`. -/
theorem poincareHomotopy_add_apply {x₀ x : E} {ω₁ ω₂ : E → E [⋀^Fin (n + 1)]→L[ℝ] F}
    (h₁ : ContinuousOn ω₁ (segment ℝ x₀ x)) (h₂ : ContinuousOn ω₂ (segment ℝ x₀ x)) :
    poincareHomotopy x₀ (ω₁ + ω₂) x = poincareHomotopy x₀ ω₁ x + poincareHomotopy x₀ ω₂ x := by
  have hmaps : MapsTo (lineMap x₀ x) (uIcc (0 : ℝ) 1) (segment ℝ x₀ x) := fun _ ht ↦
    lineMap_mem_segment ℝ x₀ x (by rwa [uIcc_of_le zero_le_one] at ht)
  have hint {ω : E → E [⋀^Fin (n + 1)]→L[ℝ] F} (hω : ContinuousOn ω (segment ℝ x₀ x)) :
      IntervalIntegrable (fun t : ℝ ↦ t ^ n • (ω (lineMap x₀ x t)).curryLeft (x - x₀))
        volume 0 1 :=
    ((continuousOn_pow n).smul (((ContinuousAlternatingMap.curryLeftLI (𝕜 := ℝ) (E := E)
      (F := F) (n := n)).toContinuousLinearMap.flip (x - x₀)).continuous.comp_continuousOn
        (hω.comp lineMap_continuous.continuousOn hmaps))).intervalIntegrable
  rw [poincareHomotopy_apply, poincareHomotopy_apply, poincareHomotopy_apply,
    ← intervalIntegral.integral_add (hint h₁) (hint h₂)]
  simp only [Pi.add_apply, ContinuousAlternatingMap.curryLeft_add, add_apply,
    smul_add]

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

/-- The partial derivative in `x` of the integrand of the homotopy operator at a parameter `t`,
within a set `u` that `x' ↦ x₀ + t (x' - x₀)` maps into a set `v` on which `ω` has derivative
`ω'` at `x₀ + t (x - x₀)`. -/
private theorem hasFDerivWithinAt_integrand {x₀ : E} {u v : Set E}
    {ω : E → E [⋀^Fin (n + 1)]→L[ℝ] F} {ω' : E →L[ℝ] E [⋀^Fin (n + 1)]→L[ℝ] F} {x : E} {t : ℝ}
    (hω : HasFDerivWithinAt ω ω' v (lineMap x₀ x t))
    (huv : MapsTo (fun x' ↦ lineMap x₀ x' t) u v) :
    HasFDerivWithinAt (fun x' ↦ (ω (lineMap x₀ x' t)).curryLeft (x' - x₀))
      (t • ((ContinuousAlternatingMap.curryLeftLI (𝕜 := ℝ) (E := E) (F := F)
          (n := n)).toContinuousLinearMap.flip (x - x₀) ∘L ω') +
        (ContinuousAlternatingMap.curryLeftLI (𝕜 := ℝ) (E := E) (F := F)
          (n := n)).toContinuousLinearMap (ω (lineMap x₀ x t))) u x := by
  set L := (ContinuousAlternatingMap.curryLeftLI (𝕜 := ℝ) (E := E) (F := F)
    (n := n)).toContinuousLinearMap
  have hray : HasFDerivAt (fun x' ↦ lineMap x₀ x' t) (t • ContinuousLinearMap.id ℝ E) x := by
    simp only [lineMap_apply_module']
    exact (((hasFDerivAt_id x).sub_const x₀).const_smul t).add_const x₀
  refine (L.hasFDerivWithinAt_of_bilinear (hω.comp x hray.hasFDerivWithinAt huv)
    ((hasFDerivAt_id x).sub_const x₀).hasFDerivWithinAt).congr_fderiv ?_
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
              (n := n)).toContinuousLinearMap.flip (x - x₀) ∘L
                fderivWithin ℝ ω s (lineMap x₀ x t)) +
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
        have hy := hmem t
        have hω' : HasFDerivAt ω (fderivWithin ℝ ω s (lineMap x₀ x (t : ℝ)))
            (lineMap x₀ x (t : ℝ)) :=
          (hω.differentiableOn one_ne_zero _ hy).hasFDerivWithinAt.hasFDerivAt
            (hso.mem_nhds hy)
        dsimp only
        rw [(hasFDerivWithinAt_univ.1 (hasFDerivWithinAt_integrand hω'.hasFDerivWithinAt
          (mapsTo_univ _ _))).fderiv]
        simp

/-- The fundamental theorem of calculus for `t ↦ tⁿ⁺¹ ω(x₀ + t (x - x₀))` on `[0, 1]`, for a
form `C¹` on a star-convex set with unique derivatives. -/
private theorem integral_pow_smul_fderivWithin_add_eq (hs : StarConvex ℝ x₀ s)
    (hsu : UniqueDiffOn ℝ s) (hω : ContDiffOn ℝ 1 ω s) {x : E} (hx : x ∈ s) :
    ∫ t in (0 : ℝ)..1, (t ^ (n + 1) • fderivWithin ℝ ω s (lineMap x₀ x t) (x - x₀) +
      ((n + 1 : ℝ) * t ^ n) • ω (lineMap x₀ x t)) = ω x := by
  have hmaps : MapsTo (lineMap x₀ x) (Icc (0 : ℝ) 1) s := fun _ ht ↦
    hs.segment_subset hx (lineMap_mem_segment ℝ x₀ x ht)
  have hderiv (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
      HasDerivAt (fun t : ℝ ↦ t ^ (n + 1) • ω (lineMap x₀ x t))
        (t ^ (n + 1) • fderivWithin ℝ ω s (lineMap x₀ x t) (x - x₀) +
          ((n + 1 : ℝ) * t ^ n) • ω (lineMap x₀ x t)) t := by
    have hmem := hmaps (Ioo_subset_Icc_self ht)
    have hω' : HasDerivWithinAt (fun t : ℝ ↦ ω (lineMap x₀ x t))
        (fderivWithin ℝ ω s (lineMap x₀ x t) (x - x₀)) (Icc 0 1) t :=
      (hω.differentiableOn one_ne_zero _ hmem).hasFDerivWithinAt.comp_hasDerivWithinAt t
        hasDerivAt_lineMap.hasDerivWithinAt hmaps
    refine ((hasDerivAt_pow (n + 1) t).smul
      (hω'.hasDerivAt (Icc_mem_nhds ht.1 ht.2))).congr_deriv ?_
    simp
  have hcont : ContinuousOn (fun t : ℝ ↦ t ^ (n + 1) • ω (lineMap x₀ x t)) (Icc 0 1) :=
    (continuousOn_pow (n + 1)).smul (hω.continuousOn.comp lineMap_continuous.continuousOn hmaps)
  have hint : IntervalIntegrable (fun t : ℝ ↦
      t ^ (n + 1) • fderivWithin ℝ ω s (lineMap x₀ x t) (x - x₀) +
        ((n + 1 : ℝ) * t ^ n) • ω (lineMap x₀ x t)) volume 0 1 :=
    (((continuousOn_pow (n + 1)).smul
      ((ContinuousLinearMap.apply ℝ _ (x - x₀)).continuous.comp_continuousOn
        ((hω.continuousOn_fderivWithin hsu le_rfl).comp lineMap_continuous.continuousOn
          hmaps))).add
      ((continuousOn_const.mul (continuousOn_pow n)).smul
        (hω.continuousOn.comp lineMap_continuous.continuousOn hmaps))).intervalIntegrable_of_Icc
      zero_le_one
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one hcont hderiv hint]
  simp

/-- The homotopy formula with the exterior derivative of the homotopy operator replaced by its
integral expression, for a form `C¹` on a star-convex set with unique derivatives. -/
private theorem integral_add_poincareHomotopy_extDerivWithin_eq (hs : StarConvex ℝ x₀ s)
    (hsu : UniqueDiffOn ℝ s) (hω : ContDiffOn ℝ 1 ω s) {x : E} (hx : x ∈ s) :
    (∫ t in (0 : ℝ)..1, t ^ n •
        (t • ContinuousAlternatingMap.alternatizeUncurryFin
            ((ContinuousAlternatingMap.curryLeftLI (𝕜 := ℝ) (E := E) (F := F)
              (n := n)).toContinuousLinearMap.flip (x - x₀) ∘L
                fderivWithin ℝ ω s (lineMap x₀ x t)) +
          (n + 1) • ω (lineMap x₀ x t))) + poincareHomotopy x₀ (extDerivWithin ω s) x = ω x := by
  set L := (ContinuousAlternatingMap.curryLeftLI (𝕜 := ℝ) (E := E) (F := F)
    (n := n)).toContinuousLinearMap
  set y := x - x₀
  have hmaps : MapsTo (lineMap x₀ x) (uIcc (0 : ℝ) 1) s := fun _ ht ↦
    hs.segment_subset hx (lineMap_mem_segment ℝ x₀ x (by rwa [uIcc_of_le zero_le_one] at ht))
  have hDω_cont := (hω.continuousOn_fderivWithin hsu le_rfl).comp
    lineMap_continuous.continuousOn hmaps
  have hD_int : IntervalIntegrable (fun t : ℝ ↦ t ^ n •
      (t • ContinuousAlternatingMap.alternatizeUncurryFin
          (L.flip y ∘L fderivWithin ℝ ω s (lineMap x₀ x t)) +
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
      (extDerivWithin ω s (lineMap x₀ x t)).curryLeft y) volume 0 1 := by
    refine ContinuousOn.intervalIntegrable ((continuousOn_pow (n + 1)).smul ?_)
    refine hcurry.congr fun t _ ↦ ?_
    simp [extDerivWithin]
  rw [poincareHomotopy_apply, ← intervalIntegral.integral_add hD_int hdω_int,
    ← integral_pow_smul_fderivWithin_add_eq hs hsu hω hx]
  -- pointwise, this is the constant-coefficient Cartan formula for `Dω` and `y = x - x₀`
  refine intervalIntegral.integral_congr fun t _ ↦ ?_
  have key := ContinuousAlternatingMap.alternatizeUncurryFin_curryLeft_comp_add_curryLeft
    (fderivWithin ℝ ω s (lineMap x₀ x t)) y
  simp only [extDerivWithin, L]
  rw [← Nat.cast_smul_eq_nsmul ℝ]
  linear_combination (norm := module) t ^ (n + 1) • key

/-- **The homotopy formula** `d (K ω) + K (d ω) = ω` for the Poincaré homotopy operator `K` of a
`C¹` form on an open set star-convex with respect to the centre of `K`. -/
theorem extDeriv_poincareHomotopy_add_poincareHomotopy_extDeriv (hs : StarConvex ℝ x₀ s)
    (hso : IsOpen s) (hω : ContDiffOn ℝ 1 ω s) {x : E} (hx : x ∈ s) :
    extDeriv (poincareHomotopy x₀ ω) x + poincareHomotopy x₀ (extDeriv ω) x = ω x := by
  have hK : poincareHomotopy x₀ (extDeriv ω) x = poincareHomotopy x₀ (extDerivWithin ω s) x :=
    poincareHomotopy_congr fun y hy ↦ by
      rw [extDerivWithin, extDeriv, fderivWithin_of_isOpen hso (hs.segment_subset hx hy)]
  rw [extDeriv_poincareHomotopy_eq hs hso hω hx, hK]
  exact integral_add_poincareHomotopy_extDerivWithin_eq hs hso.uniqueDiffOn hω hx

/-- **The Poincaré lemma.** On an open set star-convex with respect to `x₀`, the Poincaré
homotopy operator with centre `x₀` of a closed `C¹` form is a primitive of it. -/
theorem extDeriv_poincareHomotopy (hs : StarConvex ℝ x₀ s) (hso : IsOpen s)
    (hω : ContDiffOn ℝ 1 ω s) (hclosed : ∀ y ∈ s, extDeriv ω y = 0) {x : E} (hx : x ∈ s) :
    extDeriv (poincareHomotopy x₀ ω) x = ω x := by
  have h0 : poincareHomotopy x₀ (extDeriv ω) x = 0 := by
    rw [poincareHomotopy_congr (ω₂ := 0) fun y hy ↦ hclosed y (hs.segment_subset hx hy),
      poincareHomotopy_zero, Pi.zero_apply]
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

/-! ### Convex sets that need not be open

On a convex set `s` with unique derivatives, such as a closed half-ball (the image of a boundary
chart), derivatives are taken within `s` and the exterior derivative is `extDerivWithin`. -/

namespace Convex

variable {x₀ : E} {s : Set E} {ω : E → E [⋀^Fin (n + 1)]→L[ℝ] F}

/-- The Poincaré homotopy operator of a `C^r` form on a convex set with unique derivatives, with
centre in that set, is `C^r` there. -/
theorem contDiffOn_poincareHomotopy (hs : Convex ℝ s) (hsu : UniqueDiffOn ℝ s) (hx₀ : x₀ ∈ s)
    {r : ℕ∞} (hω : ContDiffOn ℝ r ω s) : ContDiffOn ℝ r (poincareHomotopy x₀ ω) s := by
  have hpow : Integrable (fun t : I ↦ (t : ℝ) ^ n) volume :=
    (continuous_subtype_val.pow n).integrable_of_hasCompactSupport (.of_compactSpace _)
  refine (hs.contDiffOn_integral_smul_of_contDiffOn (μ := (volume : Measure I)) hpow
    continuous_subtype_val hsu (hsu.prod uniqueDiffOn_Icc_zero_one)
    ((contDiffOn_integrand hω).mono fun p hp ↦
      (hs.starConvex hx₀).segment_subset hp.1 (lineMap_mem_segment ℝ x₀ p.1 hp.2))
    fun x hx t ↦ ⟨hx, t.2⟩).congr fun x _ ↦ ?_
  rw [poincareHomotopy_apply, intervalIntegral_eq_integral_unitInterval]

variable [CompleteSpace F]

/-- The exterior derivative within a convex set of the Poincaré homotopy operator, as an
integral over `[0, 1]`. -/
private theorem extDerivWithin_poincareHomotopy_eq (hs : Convex ℝ s) (hsu : UniqueDiffOn ℝ s)
    (hx₀ : x₀ ∈ s) (hω : ContDiffOn ℝ 1 ω s) {x : E} (hx : x ∈ s) :
    extDerivWithin (poincareHomotopy x₀ ω) s x =
      ∫ t in (0 : ℝ)..1, t ^ n •
        (t • ContinuousAlternatingMap.alternatizeUncurryFin
            ((ContinuousAlternatingMap.curryLeftLI (𝕜 := ℝ) (E := E) (F := F)
              (n := n)).toContinuousLinearMap.flip (x - x₀) ∘L
                fderivWithin ℝ ω s (lineMap x₀ x t)) +
          (n + 1) • ω (lineMap x₀ x t)) := by
  set L := (ContinuousAlternatingMap.curryLeftLI (𝕜 := ℝ) (E := E) (F := F)
    (n := n)).toContinuousLinearMap
  have hstar := hs.starConvex hx₀
  have hpow : Integrable (fun t : I ↦ (t : ℝ) ^ n) volume :=
    (continuous_subtype_val.pow n).integrable_of_hasCompactSupport (.of_compactSpace _)
  have hmaps (t : I) : MapsTo (fun x' ↦ lineMap x₀ x' (t : ℝ)) s s := fun x' hx' ↦
    hstar.segment_subset hx' (lineMap_mem_segment ℝ x₀ x' t.2)
  have h := hs.hasFDerivWithinAt_integral_smul_of_contDiffOn (μ := (volume : Measure I)) hpow
    continuous_subtype_val (hsu.prod uniqueDiffOn_Icc_zero_one)
    ((contDiffOn_integrand (x₀ := x₀) hω).mono fun p hp ↦
      hstar.segment_subset hp.1 (lineMap_mem_segment ℝ x₀ p.1 hp.2))
    (fun x hx t ↦ ⟨hx, t.2⟩) hx (hsu x hx)
  have hK : poincareHomotopy x₀ ω =
      fun x ↦ ∫ t : I, (t : ℝ) ^ n • (ω (lineMap x₀ x (t : ℝ))).curryLeft (x - x₀) :=
    funext fun x ↦ by rw [poincareHomotopy_apply, intervalIntegral_eq_integral_unitInterval]
  -- the partial derivative of the integrand, explicitly
  set D : ℝ → E →L[ℝ] E [⋀^Fin n]→L[ℝ] F := fun t ↦
    t • (L.flip (x - x₀) ∘L fderivWithin ℝ ω s (lineMap x₀ x t)) + L (ω (lineMap x₀ x t))
  have hD (t : I) : fderivWithin ℝ (fun x' ↦ (ω (lineMap x₀ x' (t : ℝ))).curryLeft (x' - x₀)) s x =
      D t :=
    (hasFDerivWithinAt_integrand ((hω.differentiableOn one_ne_zero _
      (hmaps t hx)).hasFDerivWithinAt) (hmaps t)).fderivWithin (hsu x hx)
  have hDc : ContinuousOn D (Icc 0 1) := by
    have hseg : MapsTo (lineMap x₀ x) (Icc (0 : ℝ) 1) s := fun t ht ↦ hmaps ⟨t, ht⟩ hx
    exact (continuousOn_id.smul ((ContinuousLinearMap.compL ℝ E _ _
      (L.flip (x - x₀))).continuous.comp_continuousOn
        ((hω.continuousOn_fderivWithin hsu le_rfl).comp lineMap_continuous.continuousOn
          hseg))).add (L.continuous.comp_continuousOn
            (hω.continuousOn.comp lineMap_continuous.continuousOn hseg))
  have hint := integrable_smul_of_continuousOn (μ := (volume : Measure I)) (x := x) hpow
    continuous_subtype_val (F := fun p : E × ℝ ↦ D p.2) (W := {p | p.2 ∈ Icc 0 1})
    (hDc.comp continuous_snd.continuousOn fun _ hp ↦ hp) fun t ↦ t.2
  calc extDerivWithin (poincareHomotopy x₀ ω) s x
      = ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ E F
          (∫ t : I, (t : ℝ) ^ n • D t) := by
        rw [extDerivWithin, hK, h.fderivWithin (hsu x hx),
          ContinuousAlternatingMap.alternatizeUncurryFinCLM_apply]
        simp only [hD]
    _ = ∫ t : I, ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ E F ((t : ℝ) ^ n • D t) :=
        (ContinuousLinearMap.integral_comp_comm (𝕜 := ℝ)
          (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ E F (n := n)) hint).symm
    _ = _ := by
        rw [intervalIntegral_eq_integral_unitInterval]
        refine integral_congr_ae (ae_of_all _ fun t ↦ ?_)
        simp [D, L]

/-- **The homotopy formula** `d (K ω) + K (d ω) = ω`, with exterior derivatives within `s`, for
the Poincaré homotopy operator `K` of a `C¹` form on a convex set `s` with unique derivatives,
whose centre lies in `s`. -/
theorem extDerivWithin_poincareHomotopy_add_poincareHomotopy_extDerivWithin (hs : Convex ℝ s)
    (hsu : UniqueDiffOn ℝ s) (hx₀ : x₀ ∈ s) (hω : ContDiffOn ℝ 1 ω s) {x : E} (hx : x ∈ s) :
    extDerivWithin (poincareHomotopy x₀ ω) s x + poincareHomotopy x₀ (extDerivWithin ω s) x =
      ω x := by
  rw [extDerivWithin_poincareHomotopy_eq hs hsu hx₀ hω hx]
  exact (hs.starConvex hx₀).integral_add_poincareHomotopy_extDerivWithin_eq hsu hω hx

/-- **The relative Poincaré lemma.** On a convex set with unique derivatives, the Poincaré
homotopy operator, centred in the set, of a form closed within the set is a primitive of it
within the set. -/
theorem extDerivWithin_poincareHomotopy (hs : Convex ℝ s) (hsu : UniqueDiffOn ℝ s)
    (hx₀ : x₀ ∈ s) (hω : ContDiffOn ℝ 1 ω s) (hclosed : ∀ y ∈ s, extDerivWithin ω s y = 0)
    {x : E} (hx : x ∈ s) : extDerivWithin (poincareHomotopy x₀ ω) s x = ω x := by
  have h0 : poincareHomotopy x₀ (extDerivWithin ω s) x = 0 := by
    rw [poincareHomotopy_congr (ω₂ := 0) fun y hy ↦
        hclosed y ((hs.starConvex hx₀).segment_subset hx hy),
      poincareHomotopy_zero, Pi.zero_apply]
  simpa [h0] using
    hs.extDerivWithin_poincareHomotopy_add_poincareHomotopy_extDerivWithin hsu hx₀ hω hx

/-- **The relative Poincaré lemma.** A `C^r` form, `r ≥ 1`, closed within a convex set with unique
derivatives is the exterior derivative within the set of a `C^r` form, which can be chosen to
vanish at any given point of the set. The set need not be open: a closed half-ball, the image of
a boundary chart, is allowed. -/
theorem exists_contDiffOn_forall_extDerivWithin_eq (hs : Convex ℝ s) (hsu : UniqueDiffOn ℝ s)
    (hx₀ : x₀ ∈ s) {r : ℕ∞} (hr : 1 ≤ r) (hω : ContDiffOn ℝ r ω s)
    (hclosed : ∀ y ∈ s, extDerivWithin ω s y = 0) :
    ∃ α : E → E [⋀^Fin n]→L[ℝ] F, ContDiffOn ℝ r α s ∧ α x₀ = 0 ∧
      ∀ x ∈ s, extDerivWithin α s x = ω x :=
  ⟨poincareHomotopy x₀ ω, hs.contDiffOn_poincareHomotopy hsu hx₀ hω, poincareHomotopy_self x₀ ω,
    fun _ hx ↦ hs.extDerivWithin_poincareHomotopy hsu hx₀ (hω.of_le (by exact_mod_cast hr))
      hclosed hx⟩

end Convex
