/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Regularity.Hessian.HalfSpace.Basic
public import TauCeti.Analysis.PDE.Regularity.Hessian.IntegrabilityGain
import TauCeti.Analysis.InnerProductSpace.Trace.Free
import TauCeti.Analysis.Sobolev.Trace.OddReflection
import TauCeti.Analysis.Sobolev.Wkp.Chain
import TauCeti.Analysis.Sobolev.Wkp.ChangeOfVariables.Linear
import TauCeti.Analysis.Sobolev.Wkp.Restriction
import TauCeti.MeasureTheory.Function.Lp.Dilation

/-!
# Integrability gain on a half-space

Let `E` be a finite-dimensional real inner product space, `1 < p, r < ∞`, and let
`H = {x | a < x.fst}` be a half-space of `ℝ × E`. This file proves the half-space form of the core
step of Gilbarg–Trudinger, Lemma 9.16: a strong solution `u ∈ W^{2,p}(H)` of

`tr (b D²u) = f` in `H`, `u = 0` on `∂H`,

whose first-order part lies in `W^{1,p}_0(H)`, and with `u, f ∈ Lʳ(H)`, lies in `W^{2,r}(H)`, as
soon as the coefficient field `b` is uniformly close to a constant elliptic operator `A`: there is
`δ > 0`, depending only on `E`, `p` and `r`, such that `‖b(x) - A‖ ≤ δ λ` almost everywhere on `H`
suffices, where `λ ‖ξ‖² ≤ ⟪A ξ, ξ⟫`
(`TauCeti.exists_wkp_value_ae_eq_of_traceCLM_comp_eq_of_norm_sub_le_of_normalHalfSpace`). The
case `A = 1` is
`TauCeti.exists_wkp_value_ae_eq_of_traceCLM_comp_eq_of_norm_sub_id_le_of_normalHalfSpace`. No
smoothness of `b` is needed, only measurability, and the exponents `p` and `r` are unrelated.
This is the boundary counterpart of the whole-space integrability gain
`TauCeti.exists_wkp_value_ae_eq_of_trace_comp_iteratedGradient_eq_of_norm_sub_le`: after a
cutoff near a point of a flat boundary portion and freezing a continuous coefficient there, it
upgrades the integrability of strong solutions that vanish on the boundary.

## The argument

* **Coefficients close to the identity.** The odd reflection `w` of `u` across the boundary
  hyperplane lies in `W^{2,p}(ℝ × E)`, with weak Hessian `D²u` on `H` and `-R ∘ D²u(ρ x) ∘ R` on the
  other side, where `ρ` is the reflection in the hyperplane and `R` its linear part
  (`TauCeti.Wkp.exists_value_ae_eq_sub_comp_normalReflection`). Reflect the coefficient in the
  same way, `b'(x) = R ∘ b(ρ x) ∘ R` below the hyperplane. Since `R` is an isometric involution,
  `b'` stays within `δ` of `1`, and since `tr (R ∘ M ∘ R) = tr M`, `w` solves `tr (b' D²w) = f'` for
  the odd reflection `f'` of `f`. The value of `w` and `f'` lie in `Lʳ(ℝ × E)`, as `ρ` preserves
  volume. The whole-space integrability gain places `w` in `W^{2,r}(ℝ × E)`, and `w = u` on `H`.
* **A general frozen coefficient.** Only the symmetric part `S = (A + A†) / 2` of `A` matters,
  since `D²u` is self-adjoint. Write `S = e e†` for a linear automorphism `e` whose adjoint maps the
  normal `(1, 0)` to a positive multiple of itself
  (`TauCeti.exists_continuousLinearEquiv_preimage_normalHalfSpace`). Then `e` maps a half-space
  `H'` onto `H`, and `v = u ∘ e` solves on `H'` an equation whose coefficient
  `e⁻¹ ((b + b†) / 2)(e ·) e⁻†` lies within `δ` of the identity
  (`TauCeti.norm_conj_symmPart_sub_id_le`), with zero boundary values. The first case applies to
  `v`, and composing with `e⁻¹` returns to `u`.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Lemma 9.16, §9.5 (reflection across a flat boundary portion, Lemma 9.12) and Section 6.1
  (reduction of a constant-coefficient operator to the Laplacian by a linear change of variables).
-/

public section

noncomputable section

namespace TauCeti

open _root_.MeasureTheory Set TopologicalSpace
open scoped ENNReal NNReal InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {p r : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ r)]

/-! ### Coefficients close to the identity -/

section Reflection

/-- The odd reflection of a coefficient field on the half-space `H`: it is `b` on `H`,
`R ∘ b(ρ x) ∘ R` below the boundary hyperplane, and `1` on it, where `ρ` is the reflection in the
hyperplane and `R` its linear part. It is written as `1 + c x + R ∘ c(ρ x) ∘ R` with `c` the
deviation `b - 1` on `H`, extended by zero. -/
private def reflectCoeff (a : ℝ)
    (b : WithLp 2 (ℝ × E) → WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E)) (x : WithLp 2 (ℝ × E)) :
    WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E) :=
  ContinuousLinearMap.id ℝ _ +
    (normalHalfSpace (E := E) a : Set (WithLp 2 (ℝ × E))).indicator
      (fun y => b y - ContinuousLinearMap.id ℝ _) x +
    (normalLinearReflection E : WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E)) ∘L
      (normalHalfSpace (E := E) a : Set (WithLp 2 (ℝ × E))).indicator
        (fun y => b y - ContinuousLinearMap.id ℝ _) (normalReflection E a x) ∘L
      (normalLinearReflection E : WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E))

omit [MeasurableSpace E] [BorelSpace E] in
/-- The linear normal reflection, as a continuous linear map, is an involution. -/
private theorem normalLinearReflection_comp_self :
    (normalLinearReflection E : WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E)) ∘L
      (normalLinearReflection E : WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E)) =
      ContinuousLinearMap.id ℝ _ := by
  ext x
  exact normalLinearReflection_normalLinearReflection x

omit [MeasurableSpace E] [BorelSpace E] in
/-- Conjugating by the linear normal reflection does not increase the operator norm. -/
private theorem norm_normalLinearReflection_comp_comp_le
    (M : WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E)) :
    ‖(normalLinearReflection E : WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E)) ∘L M ∘L
      (normalLinearReflection E : WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E))‖ ≤ ‖M‖ := by
  have hR : ‖(normalLinearReflection E : WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E))‖ ≤ 1 :=
    (normalLinearReflection E).toLinearIsometry.norm_toContinuousLinearMap_le
  calc _ ≤ ‖(normalLinearReflection E : WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E))‖ *
        (‖M‖ * ‖(normalLinearReflection E : WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E))‖) :=
        (ContinuousLinearMap.opNorm_comp_le _ _).trans
          (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
    _ ≤ 1 * (‖M‖ * 1) := by gcongr
    _ = ‖M‖ := by ring

omit [MeasurableSpace E] [BorelSpace E] in
/-- Conjugating by the linear normal reflection commutes with subtracting the identity. -/
private theorem normalLinearReflection_comp_comp_sub_id
    (M : WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E)) :
    (normalLinearReflection E : WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E)) ∘L M ∘L
        (normalLinearReflection E : WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E)) -
        ContinuousLinearMap.id ℝ _ =
      (normalLinearReflection E : WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E)) ∘L
        (M - ContinuousLinearMap.id ℝ _) ∘L
        (normalLinearReflection E : WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E)) := by
  rw [ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_sub, ContinuousLinearMap.id_comp,
    normalLinearReflection_comp_self]

omit [MeasurableSpace E] [BorelSpace E] in
/-- The trace pairing is invariant under conjugating both factors by the linear normal
reflection: `tr ((R ∘ B ∘ R) ∘ (R ∘ D ∘ R)) = tr (B ∘ D)`. -/
private theorem traceCLM_normalLinearReflection_conj_comp
    (B D : WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E)) :
    traceCLM ℝ (WithLp 2 (ℝ × E))
        (((normalLinearReflection E : WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E)) ∘L B ∘L
            (normalLinearReflection E : WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E))) ∘L
          ((normalLinearReflection E : WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E)) ∘L D ∘L
            (normalLinearReflection E : WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E)))) =
      traceCLM ℝ (WithLp 2 (ℝ × E)) (B ∘L D) := by
  have hRR : ((normalLinearReflection E : WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E)) ∘L B ∘L
          (normalLinearReflection E : WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E))) ∘L
        ((normalLinearReflection E : WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E)) ∘L D ∘L
          (normalLinearReflection E : WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E))) =
      (normalLinearReflection E : WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E)) ∘L (B ∘L D) ∘L
        (normalLinearReflection E : WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E)) := by
    simp only [ContinuousLinearMap.comp_assoc]
    rw [← ContinuousLinearMap.comp_assoc
      (normalLinearReflection E : WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E))
      (normalLinearReflection E : WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E)),
      normalLinearReflection_comp_self, ContinuousLinearMap.id_comp]
  rw [hRR, ContinuousLinearMap.traceCLM_comp_comp_of_comp_eq_id normalLinearReflection_comp_self]

omit [MeasurableSpace E] [BorelSpace E] in
/-- On the half-space the reflected coefficient is the coefficient itself. -/
private theorem reflectCoeff_of_mem {a : ℝ}
    (b : WithLp 2 (ℝ × E) → WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E)) {x : WithLp 2 (ℝ × E)}
    (hx : x ∈ (normalHalfSpace (E := E) a : Set (WithLp 2 (ℝ × E)))) :
    reflectCoeff a b x = b x := by
  have hρx : normalReflection E a x ∉ (normalHalfSpace (E := E) a : Set (WithLp 2 (ℝ × E))) := by
    rw [SetLike.mem_coe, normalReflection_mem_normalHalfSpace_iff]
    exact ((mem_normalHalfSpace a x).1 hx).not_gt
  rw [reflectCoeff, indicator_of_mem hx, indicator_of_notMem hρx, ContinuousLinearMap.zero_comp,
    ContinuousLinearMap.comp_zero, add_zero, add_sub_cancel]

omit [MeasurableSpace E] [BorelSpace E] in
/-- Below the boundary hyperplane the reflected coefficient is `R ∘ b(ρ x) ∘ R`. -/
private theorem reflectCoeff_of_mem_normalReflection {a : ℝ}
    (b : WithLp 2 (ℝ × E) → WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E)) {x : WithLp 2 (ℝ × E)}
    (hx : x ∉ (normalHalfSpace (E := E) a : Set (WithLp 2 (ℝ × E))))
    (hρx : normalReflection E a x ∈ (normalHalfSpace (E := E) a : Set (WithLp 2 (ℝ × E)))) :
    reflectCoeff a b x =
      (normalLinearReflection E : WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E)) ∘L
        b (normalReflection E a x) ∘L
        (normalLinearReflection E : WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E)) := by
  rw [reflectCoeff, indicator_of_notMem hx, indicator_of_mem hρx, add_zero,
    ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_sub, ContinuousLinearMap.id_comp,
    normalLinearReflection_comp_self, add_sub_cancel]

omit [MeasurableSpace E] [BorelSpace E] in
/-- Off the half-space and its reflection, the reflected coefficient is the identity. -/
private theorem reflectCoeff_of_notMem {a : ℝ}
    (b : WithLp 2 (ℝ × E) → WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E)) {x : WithLp 2 (ℝ × E)}
    (hx : x ∉ (normalHalfSpace (E := E) a : Set (WithLp 2 (ℝ × E))))
    (hρx : normalReflection E a x ∉ (normalHalfSpace (E := E) a : Set (WithLp 2 (ℝ × E)))) :
    reflectCoeff a b x = ContinuousLinearMap.id ℝ _ := by
  rw [reflectCoeff, indicator_of_notMem hx, indicator_of_notMem hρx,
    ContinuousLinearMap.zero_comp, ContinuousLinearMap.comp_zero, add_zero, add_zero]

/-- The reflected coefficient is measurable when `b` is measurable on the half-space. -/
private theorem aestronglyMeasurable_reflectCoeff {a : ℝ}
    {b : WithLp 2 (ℝ × E) → WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E)}
    (hb : AEStronglyMeasurable b
      ((volume : Measure (WithLp 2 (ℝ × E))).restrict (normalHalfSpace (E := E) a))) :
    AEStronglyMeasurable (reflectCoeff a b) volume := by
  have hc : AEStronglyMeasurable ((normalHalfSpace (E := E) a : Set (WithLp 2 (ℝ × E))).indicator
      fun y => b y - ContinuousLinearMap.id ℝ _) volume :=
    (aestronglyMeasurable_indicator_iff (normalHalfSpace (E := E) a).isOpen.measurableSet).2
      (hb.sub aestronglyMeasurable_const)
  have hconj : Continuous fun M : WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E) =>
      (normalLinearReflection E : WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E)) ∘L M ∘L
        (normalLinearReflection E : WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E)) :=
    continuous_const.clm_comp (continuous_id.clm_comp continuous_const)
  exact (aestronglyMeasurable_const.add hc).add (hconj.comp_aestronglyMeasurable
    (hc.comp_measurePreserving (measurePreserving_normalReflection a)))

/-- If `b` is within `δ` of the identity almost everywhere on the half-space, so is its odd
reflection almost everywhere on the whole space. -/
private theorem ae_norm_reflectCoeff_sub_id_le {a δ : ℝ} (hδ : 0 ≤ δ)
    {b : WithLp 2 (ℝ × E) → WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E)}
    (hbδ : ∀ᵐ x ∂(volume : Measure (WithLp 2 (ℝ × E))).restrict (normalHalfSpace (E := E) a),
      ‖b x - ContinuousLinearMap.id ℝ _‖ ≤ δ) :
    ∀ᵐ x ∂volume, ‖reflectCoeff a b x - ContinuousLinearMap.id ℝ _‖ ≤ δ := by
  have hS := (normalHalfSpace (E := E) a).isOpen.measurableSet
  have hb := (ae_restrict_iff' hS).1 hbδ
  filter_upwards [hb, (measurePreserving_normalReflection a).quasiMeasurePreserving.ae hb]
    with x h₁ h₂
  by_cases hx : x ∈ (normalHalfSpace (E := E) a : Set (WithLp 2 (ℝ × E)))
  · rw [reflectCoeff_of_mem b hx]
    exact h₁ hx
  · by_cases hρx : normalReflection E a x ∈ (normalHalfSpace (E := E) a : Set (WithLp 2 (ℝ × E)))
    · rw [reflectCoeff_of_mem_normalReflection b hx hρx, normalLinearReflection_comp_comp_sub_id]
      exact (norm_normalLinearReflection_comp_comp_le _).trans (h₂ hρx)
    · rw [reflectCoeff_of_notMem b hx hρx, sub_self, ContinuousLinearMap.opNorm_zero]
      exact hδ

/-- **The reflected equation.** If `tr (b D²u) = f` almost everywhere on the half-space and `D` is
the odd reflection `D²u(x) - R ∘ D²u(ρ x) ∘ R` of the weak Hessian of `u`, then
`tr (b' D) = f'` almost everywhere, where `b'` is the reflected coefficient and `f'` is the odd
reflection `f(x) - f(ρ x)` of `f`, both extended by zero off the half-space. -/
private theorem ae_traceCLM_reflectCoeff_comp_eq {a : ℝ}
    {b D G : WithLp 2 (ℝ × E) → WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E)} {f : WithLp 2 (ℝ × E) → ℝ}
    (htr : ∀ᵐ x ∂(volume : Measure (WithLp 2 (ℝ × E))).restrict (normalHalfSpace (E := E) a),
      traceCLM ℝ (WithLp 2 (ℝ × E)) (b x ∘L G x) = f x)
    (hD : D =ᵐ[volume] fun x =>
      (normalHalfSpace (E := E) a : Set (WithLp 2 (ℝ × E))).indicator G x -
        (normalLinearReflection E : WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E)) ∘L
          (normalHalfSpace (E := E) a : Set (WithLp 2 (ℝ × E))).indicator G
            (normalReflection E a x) ∘L
          (normalLinearReflection E : WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E))) :
    ∀ᵐ x ∂volume, traceCLM ℝ (WithLp 2 (ℝ × E)) (reflectCoeff a b x ∘L D x) =
      (normalHalfSpace (E := E) a : Set (WithLp 2 (ℝ × E))).indicator f x -
        (normalHalfSpace (E := E) a : Set (WithLp 2 (ℝ × E))).indicator f
          (normalReflection E a x) := by
  set S : Set (WithLp 2 (ℝ × E)) := (normalHalfSpace (E := E) a : Set (WithLp 2 (ℝ × E)))
  have ht := (ae_restrict_iff' (normalHalfSpace (E := E) a).isOpen.measurableSet).1 htr
  filter_upwards [hD, ht, (measurePreserving_normalReflection a).quasiMeasurePreserving.ae ht]
    with x hDx h₁ h₂
  rw [hDx]
  by_cases hx : x ∈ S
  · -- `ρ` maps `H` off itself.
    have hρx : normalReflection E a x ∉ S := by
      rw [SetLike.mem_coe, normalReflection_mem_normalHalfSpace_iff]
      exact ((mem_normalHalfSpace a x).1 hx).not_gt
    rw [reflectCoeff_of_mem b hx, indicator_of_mem hx, indicator_of_notMem hρx,
      indicator_of_mem hx, indicator_of_notMem hρx, ContinuousLinearMap.zero_comp,
      ContinuousLinearMap.comp_zero, sub_zero, sub_zero, h₁ hx]
  · by_cases hρx : normalReflection E a x ∈ S
    · rw [reflectCoeff_of_mem_normalReflection b hx hρx, indicator_of_notMem hx,
        indicator_of_mem hρx, indicator_of_notMem hx, indicator_of_mem hρx, zero_sub, zero_sub,
        ContinuousLinearMap.comp_neg, map_neg, traceCLM_normalLinearReflection_conj_comp,
        h₂ hρx]
    · rw [reflectCoeff_of_notMem b hx hρx, indicator_of_notMem hx, indicator_of_notMem hρx,
        indicator_of_notMem hx, indicator_of_notMem hρx, ContinuousLinearMap.zero_comp,
        ContinuousLinearMap.comp_zero, sub_zero, sub_zero, ContinuousLinearMap.comp_zero,
        map_zero]

/-- **Integrability gain on a half-space for coefficients close to the identity.** Let
`1 < p, r < ∞`. There is `δ > 0`, depending only on `E`, `p` and `r`, with the following property.
Let `H = {x | a < x.fst}` be a half-space of `ℝ × E`, and let `b` be a field of endomorphisms of
`ℝ × E`, measurable on `H`, with `‖b(x) - 1‖ ≤ δ` for almost every `x ∈ H`. Let `u ∈ W^{2,p}(H)`,
whose first-order part lies in `W^{1,p}_0(H)`, solve `tr (b D²u) = f` almost everywhere on `H`,
where `u, f ∈ Lʳ(H)`. Then `u ∈ W^{2,r}(H)`: its value is the value of an element `v` of
`W^{2,r}(H)`, and the weak Hessians of `u` and `v` agree almost everywhere on `H`. -/
theorem exists_wkp_value_ae_eq_of_traceCLM_comp_eq_of_norm_sub_id_le_of_normalHalfSpace
    (hp : 1 < p) (hp_top : p ≠ ⊤) (hr : 1 < r) (hr_top : r ≠ ⊤) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (a : ℝ) {b : WithLp 2 (ℝ × E) → WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E)},
      AEStronglyMeasurable b
        ((volume : Measure (WithLp 2 (ℝ × E))).restrict (normalHalfSpace (E := E) a)) →
      (∀ᵐ x ∂(volume : Measure (WithLp 2 (ℝ × E))).restrict (normalHalfSpace (E := E) a),
        ‖b x - ContinuousLinearMap.id ℝ _‖ ≤ δ) →
      ∀ (u : Wkp (volume : Measure (WithLp 2 (ℝ × E))) (normalHalfSpace a) p 2)
        {f : WithLp 2 (ℝ × E) → ℝ},
        Wkp.firstOrder 1 u ∈ w1p0Submodule volume (normalHalfSpace a) p →
        MemLp f r ((volume : Measure (WithLp 2 (ℝ × E))).restrict (normalHalfSpace (E := E) a)) →
        MemLp (Wkp.value 2 u : WithLp 2 (ℝ × E) → ℝ) r
          ((volume : Measure (WithLp 2 (ℝ × E))).restrict (normalHalfSpace (E := E) a)) →
        (∀ᵐ x ∂(volume : Measure (WithLp 2 (ℝ × E))).restrict (normalHalfSpace (E := E) a),
          traceCLM ℝ (WithLp 2 (ℝ × E)) (b x ∘L Wkp.iteratedGradient 1 u x) = f x) →
        ∃ v : Wkp (volume : Measure (WithLp 2 (ℝ × E))) (normalHalfSpace a) r 2,
          (Wkp.value 2 v : WithLp 2 (ℝ × E) → ℝ)
              =ᵐ[(volume : Measure (WithLp 2 (ℝ × E))).restrict (normalHalfSpace (E := E) a)]
            Wkp.value 2 u ∧
          (Wkp.iteratedGradient 1 v : WithLp 2 (ℝ × E) → IteratedGradient (WithLp 2 (ℝ × E)) 1)
              =ᵐ[(volume : Measure (WithLp 2 (ℝ × E))).restrict (normalHalfSpace (E := E) a)]
            Wkp.iteratedGradient 1 u := by
  obtain ⟨δ, hδ, hgain⟩ :=
    exists_wkp_value_ae_eq_of_trace_comp_iteratedGradient_eq_of_norm_sub_id_le
      (E := WithLp 2 (ℝ × E)) hp hp_top hr hr_top
  refine ⟨δ, hδ, fun a {b} hb hbδ u {f} hu hf hur htr => ?_⟩
  set S : Set (WithLp 2 (ℝ × E)) := (normalHalfSpace (E := E) a : Set (WithLp 2 (ℝ × E)))
  have hS : MeasurableSet S := (normalHalfSpace (E := E) a).isOpen.measurableSet
  have hρ := measurePreserving_normalReflection (E := E) a
  -- The odd reflection `w` of `u` lies in `W^{2,p}(ℝ × E)` and solves the reflected equation,
  -- whose coefficient stays within `δ` of the identity and whose data lie in `Lʳ`.
  obtain ⟨w, hwv, hwD⟩ := Wkp.exists_value_ae_eq_sub_comp_normalReflection u hu
  have hfS : MemLp (S.indicator f) r volume :=
    (memLp_indicator_iff_restrict hS.nullMeasurableSet).2 hf
  have huS : MemLp (S.indicator (Wkp.value 2 u : WithLp 2 (ℝ × E) → ℝ)) r volume :=
    (memLp_indicator_iff_restrict hS.nullMeasurableSet).2 hur
  obtain ⟨v₀, hv₀, -⟩ := hgain (reflectCoeff a b) (aestronglyMeasurable_reflectCoeff hb)
    (ae_norm_reflectCoeff_sub_id_le hδ.le hbδ) w _ (hfS.sub (hfS.comp_measurePreserving hρ))
    ((huS.sub (huS.comp_measurePreserving hρ)).ae_eq hwv.symm)
    ((ae_traceCLM_reflectCoeff_comp_eq htr hwD).mono fun x hx => by rwa [← traceCLM_apply])
  -- On `H` the value of `w` is that of `u`, since `ρ` maps `H` off itself.
  have hle : normalHalfSpace (E := E) a ≤ ⊤ := le_top
  have hv : (Wkp.value 2 (Wkp.restrictL hle 2 v₀) : WithLp 2 (ℝ × E) → ℝ)
      =ᵐ[(volume : Measure (WithLp 2 (ℝ × E))).restrict S] Wkp.value 2 u := by
    filter_upwards [Wkp.value_restrictL_ae hle 2 v₀, ae_restrict_of_ae hv₀,
      ae_restrict_of_ae hwv, ae_restrict_mem hS] with x h₁ h₂ h₃ hx
    have hρx : normalReflection E a x ∉ S := by
      rw [SetLike.mem_coe, normalReflection_mem_normalHalfSpace_iff]
      exact ((mem_normalHalfSpace a x).1 hx).not_gt
    rw [h₁, h₂, h₃, indicator_of_mem hx, indicator_of_notMem hρx, sub_zero]
  exact ⟨Wkp.restrictL hle 2 v₀, hv, Wkp.iteratedGradient_ae_eq_of_value_ae_eq 1 hv⟩

end Reflection

/-! ### A general frozen coefficient -/

/-- **Integrability gain on a half-space for coefficients close to a frozen elliptic operator.**
Let `1 < p, r < ∞`. There is `δ > 0`, depending only on `E`, `p` and `r`, with the following
property. Let `H = {x | a < x.fst}` be a half-space of `ℝ × E`, let `A` be an operator on `ℝ × E`
with `λ ‖ξ‖² ≤ ⟪A ξ, ξ⟫` and `0 < λ`, and let `b` be a field of endomorphisms of `ℝ × E`,
measurable on `H`, with `‖b(x) - A‖ ≤ δ λ` for almost every `x ∈ H`. Let `u ∈ W^{2,p}(H)`, whose
first-order part lies in `W^{1,p}_0(H)`, solve `tr (b D²u) = f` almost everywhere on `H`, where
`u, f ∈ Lʳ(H)`. Then `u ∈ W^{2,r}(H)`: its value is the value of an element `v` of `W^{2,r}(H)`,
and the weak Hessians of `u` and `v` agree almost everywhere on `H`.

Neither `A` nor `b` need be symmetric. -/
theorem exists_wkp_value_ae_eq_of_traceCLM_comp_eq_of_norm_sub_le_of_normalHalfSpace
    (hp : 1 < p) (hp_top : p ≠ ⊤) (hr : 1 < r) (hr_top : r ≠ ⊤) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (a : ℝ) {A : WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E)} {lam : ℝ},
      0 < lam → (∀ ξ, lam * ‖ξ‖ ^ 2 ≤ ⟪A ξ, ξ⟫_ℝ) →
      ∀ {b : WithLp 2 (ℝ × E) → WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E)},
      AEStronglyMeasurable b
        ((volume : Measure (WithLp 2 (ℝ × E))).restrict (normalHalfSpace (E := E) a)) →
      (∀ᵐ x ∂(volume : Measure (WithLp 2 (ℝ × E))).restrict (normalHalfSpace (E := E) a),
        ‖b x - A‖ ≤ δ * lam) →
      ∀ (u : Wkp (volume : Measure (WithLp 2 (ℝ × E))) (normalHalfSpace a) p 2)
        {f : WithLp 2 (ℝ × E) → ℝ},
        Wkp.firstOrder 1 u ∈ w1p0Submodule volume (normalHalfSpace a) p →
        MemLp f r ((volume : Measure (WithLp 2 (ℝ × E))).restrict (normalHalfSpace (E := E) a)) →
        MemLp (Wkp.value 2 u : WithLp 2 (ℝ × E) → ℝ) r
          ((volume : Measure (WithLp 2 (ℝ × E))).restrict (normalHalfSpace (E := E) a)) →
        (∀ᵐ x ∂(volume : Measure (WithLp 2 (ℝ × E))).restrict (normalHalfSpace (E := E) a),
          traceCLM ℝ (WithLp 2 (ℝ × E)) (b x ∘L Wkp.iteratedGradient 1 u x) = f x) →
        ∃ v : Wkp (volume : Measure (WithLp 2 (ℝ × E))) (normalHalfSpace a) r 2,
          (Wkp.value 2 v : WithLp 2 (ℝ × E) → ℝ)
              =ᵐ[(volume : Measure (WithLp 2 (ℝ × E))).restrict (normalHalfSpace (E := E) a)]
            Wkp.value 2 u ∧
          (Wkp.iteratedGradient 1 v : WithLp 2 (ℝ × E) → IteratedGradient (WithLp 2 (ℝ × E)) 1)
              =ᵐ[(volume : Measure (WithLp 2 (ℝ × E))).restrict (normalHalfSpace (E := E) a)]
            Wkp.iteratedGradient 1 u := by
  obtain ⟨δ, hδ, hid⟩ :=
    exists_wkp_value_ae_eq_of_traceCLM_comp_eq_of_norm_sub_id_le_of_normalHalfSpace (E := E) hp
      hp_top hr hr_top
  refine ⟨δ, hδ, fun a {A lam} hlam hA {b} hb hbA u {f} hu hf hur htr => ?_⟩
  -- A linear change of variables `e` with `e e† = (A + A†) / 2` maps the half-space
  -- `H' = {a / c < x.fst}` onto `H = {a < x.fst}`.
  obtain ⟨e, c, hee, he, hH⟩ := exists_continuousLinearEquiv_preimage_normalHalfSpace hlam hA
  have hHe : ((normalHalfSpace (E := E) a : Opens (WithLp 2 (ℝ × E))) :
      Set (WithLp 2 (ℝ × E))) = e.symm ⁻¹' (normalHalfSpace (E := E) (a / c)) := by
    rw [hH a]; ext x; simp
  have hq := quasiMeasurePreserving_restrict_of_coe_eq_preimage (mu := volume) e (hH a)
  have hq' := quasiMeasurePreserving_restrict_of_coe_eq_preimage (mu := volume) e.symm hHe
  have hMN : (e : WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E)) ∘L
      (e.symm : WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E)) = ContinuousLinearMap.id ℝ _ := by
    ext x; simp
  -- `w = u ∘ e ∈ W^{2,p}(H')` has zero boundary values and weak Hessian `e† D²u(e ·) e`.
  obtain ⟨w, hwv, hwD, hw0⟩ := Wkp.exists_value_ae_eq_comp_continuousLinearEquiv hp_top e (hH a) u
  -- It solves `tr (B D²w) = f ∘ e` with `B(y) = e⁻¹ ((b + b†) / 2)(e y) e⁻†` close to `1`.
  obtain ⟨v', hv', -⟩ := hid (a / c) (aestronglyMeasurable_conj_symmPart hb e hq)
    (by
      filter_upwards [hq.ae hbA] with y hy
      refine (norm_conj_symmPart_sub_id_le hlam e hee he (b (e y))).trans ?_
      calc lam⁻¹ * ‖b (e y) - A‖ ≤ lam⁻¹ * (δ * lam) := by gcongr
        _ = δ := by field_simp)
    w (hw0 hu) (hH a ▸ hf.comp_continuousLinearEquiv_restrict_preimage e)
    ((hH a ▸ hur.comp_continuousLinearEquiv_restrict_preimage e).ae_eq hwv.symm)
    (by
      filter_upwards [hwD, hq.ae (Wkp.adjoint_iteratedGradient_one_ae_eq u), hq.ae htr]
        with y h₁ h₂ h₃
      rw [h₁, ContinuousLinearMap.traceCLM_comp_adjoint_comp_comp_of_comp_eq_id hMN,
        ContinuousLinearMap.traceCLM_symmPart_comp _ _ h₂, h₃])
  -- Composing with `e⁻¹` returns to `u`.
  obtain ⟨v, hv, -, -⟩ := Wkp.exists_value_ae_eq_comp_continuousLinearEquiv hr_top e.symm hHe v'
  have hvu : (Wkp.value 2 v : WithLp 2 (ℝ × E) → ℝ)
      =ᵐ[(volume : Measure (WithLp 2 (ℝ × E))).restrict (normalHalfSpace (E := E) a)]
        Wkp.value 2 u := by
    filter_upwards [hv, hq'.ae (hv'.trans hwv)] with x h₁ h₂
    rw [h₁, h₂, ContinuousLinearEquiv.apply_symm_apply]
  exact ⟨v, hvu, Wkp.iteratedGradient_ae_eq_of_value_ae_eq 1 hvu⟩

end TauCeti
