/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Regularity.Hessian.HalfSpace.Basic
public import TauCeti.Analysis.PDE.Regularity.Hessian.IntegrabilityGain
import TauCeti.Analysis.InnerProductSpace.Trace.Free
import TauCeti.Analysis.Sobolev.Wkp.Chain
import TauCeti.Analysis.Sobolev.Wkp.ChangeOfVariables.Linear
import TauCeti.Analysis.Sobolev.Wkp.Restriction
import TauCeti.MeasureTheory.Measure.Haar.Unique
import TauCeti.MeasureTheory.Function.Lp.Dilation

/-!
# Integrability gain on a half-space for strong solutions vanishing on the boundary

Let `E` be a finite-dimensional real inner product space, let `1 < p, r < ∞`, and let
`H = {x | a < x.fst}` be a half-space of the Euclidean product `ℝ × E`. This file proves the
flat-boundary form of Gilbarg–Trudinger, Lemma 9.16: there is `δ > 0`, depending only on `E`, `p`
and `r`, with the following property. Let `A₀` be an operator on `ℝ × E` with
`λ ‖ξ‖² ≤ ⟪A₀ ξ, ξ⟫` and `0 < λ`, and let `A` be a field of endomorphisms of `ℝ × E`, almost
everywhere strongly measurable on `H`, with `‖A x - A₀‖ ≤ δ λ` almost everywhere on `H`. Let
`u ∈ W^{2,p}(H)`, whose first-order part lies in `W^{1,p}_0(H)`, solve

`tr (A D²u) = f` almost everywhere on `H`,

where `u, f ∈ Lʳ(H)`. Then `u ∈ W^{2,r}(H)`: its value is the value of an element `v` of
`W^{2,r}(H)`, and the weak Hessians of `u` and `v` agree almost everywhere on `H` (in namespace
`TauCeti`,
`exists_wkp_value_ae_eq_of_trace_comp_iteratedGradient_eq_of_norm_sub_le_of_normalHalfSpace`).
Neither `A₀` nor `A` need be symmetric, and no continuity of `A` is assumed.

This is the counterpart, near a flat boundary portion, of the whole-space integrability gain
`TauCeti.exists_wkp_value_ae_eq_of_trace_comp_iteratedGradient_eq_of_norm_sub_le`. After
flattening the boundary of a `C^{1,1}` domain and freezing a continuous coefficient at a boundary
point, it is the step of Lemma 9.16 that raises the integrability of a strong solution of the
Dirichlet problem up to the boundary. The zero boundary condition cannot be dropped: it is what
makes the odd reflection of `u` a function in `W^{2,p}` of the whole space.

## The argument

* **Coefficients close to the identity.** Let `ρ` be the reflection in the boundary hyperplane
  and `R` its linear part. The odd reflection `w` of `u` lies in `W^{2,p}(ℝ × E)`, with weak
  Hessian `D²u` on `H` and `-R ∘ D²u(ρ x) ∘ R` on the other side
  (`TauCeti.Wkp.exists_value_ae_eq_sub_comp_normalReflection`). Extend the coefficient field by
  `R ∘ A(ρ x) ∘ R` on the other side, and by the identity on the boundary hyperplane. Since `R` is
  an involutive isometry, the extension stays within `δ` of the identity, and since
  `tr (R ∘ M ∘ R) = tr M`, the reflected `w` solves `tr (A₁ D²w) = f₁` for the odd reflection `f₁`
  of `f`. Both `w` and `f₁` lie in `Lʳ(ℝ × E)`, so the whole-space integrability gain
  (`TauCeti.exists_wkp_value_ae_eq_of_trace_comp_iteratedGradient_eq_of_norm_sub_id_le`) places
  `w` in `W^{2,r}(ℝ × E)`, and its restriction to `H` is the required `v`.
* **A general frozen coefficient.** Only the symmetric part of `A` enters, since the weak Hessian
  is self-adjoint. Write `(A₀ + A₀†) / 2 = e e†` for a linear automorphism `e` with
  `‖e⁻¹‖ ≤ λ^{-1/2}` that maps a half-space `{a / c < x.fst}` onto `H`
  (`TauCeti.exists_continuousLinearEquiv_preimage_normalHalfSpace`). Then `u ∘ e` vanishes on the
  boundary of `{a / c < x.fst}` and solves `tr (b D²(u ∘ e)) = f ∘ e` with
  `b = e⁻¹ ((A + A†) / 2)(e ·) e⁻†` within `δ` of the identity
  (`TauCeti.norm_conj_symmPart_sub_id_le`), and composing back with `e⁻¹` preserves `W^{2,r}`.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Lemma 9.16 (the integrability gain), Lemma 9.12 (odd reflection across a flat boundary
  portion), and Section 6.1 (reduction of a constant-coefficient operator to the Laplacian by a
  linear change of variables).
-/

public section

noncomputable section

open MeasureTheory Set TopologicalSpace
open scoped ENNReal NNReal InnerProductSpace

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {p r : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ r)]

omit [Fact (1 ≤ p)] [Fact (1 ≤ r)] in
/-- The odd reflection `x ↦ g x - g (ρ x)` across the boundary of `H = {a < x.fst}` of a function
`g ∈ Lʳ(H)` extended by zero lies in `Lʳ(ℝ × E)`. -/
private theorem memLp_indicator_sub_indicator_comp_normalReflection {a : ℝ}
    {g : WithLp 2 (ℝ × E) → ℝ}
    (hg : MemLp g r ((volume : Measure (WithLp 2 (ℝ × E))).restrict (normalHalfSpace (E := E) a))) :
    MemLp (fun x => (normalHalfSpace (E := E) a : Set (WithLp 2 (ℝ × E))).indicator g x -
      (normalHalfSpace (E := E) a : Set (WithLp 2 (ℝ × E))).indicator g (normalReflection E a x))
      r volume := by
  have h := (memLp_indicator_iff_restrict
    (normalHalfSpace (E := E) a).isOpen.measurableSet.nullMeasurableSet).2 hg
  exact h.sub (h.comp_measurePreserving (measurePreserving_normalReflection a))

omit [MeasurableSpace E] [BorelSpace E] in
/-- The reflection `ρ` in the boundary hyperplane of `H = {a < x.fst}` maps `H` off itself. -/
private theorem normalReflection_notMem_normalHalfSpace {a : ℝ} {x : WithLp 2 (ℝ × E)}
    (hx : x ∈ normalHalfSpace (E := E) a) :
    normalReflection E a x ∉ normalHalfSpace (E := E) a := by
  rw [mem_normalHalfSpace] at hx
  rw [normalReflection_mem_normalHalfSpace_iff]
  exact hx.not_gt

omit [MeasurableSpace E] [BorelSpace E] in
/-- Conjugating by the linear normal reflection `R`, an isometric involution, does not increase
the distance to the identity. -/
private theorem norm_conj_normalLinearReflection_sub_id_le
    (B : WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E)) :
    ‖(normalLinearReflection E : WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E)) ∘L B ∘L
        (normalLinearReflection E : WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E)) -
      ContinuousLinearMap.id ℝ (WithLp 2 (ℝ × E))‖ ≤
      ‖B - ContinuousLinearMap.id ℝ (WithLp 2 (ℝ × E))‖ := by
  set R : WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E) :=
    (normalLinearReflection E : WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E))
  have hRR (z : WithLp 2 (ℝ × E)) : R (R z) = z := normalLinearReflection_normalLinearReflection z
  have hconj : R ∘L B ∘L R - ContinuousLinearMap.id ℝ (WithLp 2 (ℝ × E)) =
      R ∘L (B - ContinuousLinearMap.id ℝ (WithLp 2 (ℝ × E))) ∘L R := by
    ext z; simp [hRR]
  have hR : ‖R‖ ≤ 1 := ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun z => by
    rw [one_mul]
    exact ((normalLinearReflection E).norm_map z).le
  rw [hconj]
  calc ‖R ∘L (B - ContinuousLinearMap.id ℝ (WithLp 2 (ℝ × E))) ∘L R‖
      ≤ ‖R‖ * (‖B - ContinuousLinearMap.id ℝ (WithLp 2 (ℝ × E))‖ * ‖R‖) :=
        (ContinuousLinearMap.opNorm_comp_le _ _).trans
          (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
    _ ≤ 1 * (‖B - ContinuousLinearMap.id ℝ (WithLp 2 (ℝ × E))‖ * 1) := by gcongr
    _ = _ := by ring

omit [MeasurableSpace E] [BorelSpace E] in
/-- Across the boundary hyperplane the reflected equation is the negative of the original one:
`tr ((R B R) ∘ (0 - R D R)) = -tr (B D)`, since `R ∘ R = 1` and conjugation preserves traces. -/
private theorem traceCLM_conj_normalLinearReflection_comp_zero_sub
    (B D : WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E)) :
    traceCLM ℝ (WithLp 2 (ℝ × E))
        (((normalLinearReflection E : WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E)) ∘L B ∘L
          (normalLinearReflection E : WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E))) ∘L
          (0 - (normalLinearReflection E : WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E)) ∘L D ∘L
            (normalLinearReflection E : WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E)))) =
      -traceCLM ℝ (WithLp 2 (ℝ × E)) (B ∘L D) := by
  have h := (normalLinearReflection E).toContinuousLinearEquiv.traceCLM_comp_comp_symm (-(B ∘L D))
  rw [← LinearIsometryEquiv.toContinuousLinearEquiv_symm, normalLinearReflection_symm] at h
  rw [← map_neg, ← h]
  congr 1
  ext z
  simp only [ContinuousLinearMap.comp_apply, zero_sub, FunLike.coe_neg, Pi.neg_apply, map_neg,
    ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
    normalLinearReflection_normalLinearReflection]

open Classical in
/-- The coefficient field reflected across the boundary of `H = {a < x.fst}`: `A` on `H`,
`R ∘ A (ρ x) ∘ R` on the other side, and the identity on the boundary hyperplane. -/
private def reflectedCoeff (a : ℝ)
    (A : WithLp 2 (ℝ × E) → WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E)) :
    WithLp 2 (ℝ × E) → WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E) :=
  (normalHalfSpace (E := E) a : Set (WithLp 2 (ℝ × E))).piecewise A
    ((normalReflection E a ⁻¹' (normalHalfSpace (E := E) a : Set (WithLp 2 (ℝ × E)))).piecewise
      (fun x => (normalLinearReflection E : WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E)) ∘L
        A (normalReflection E a x) ∘L
          (normalLinearReflection E : WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E)))
      fun _ => ContinuousLinearMap.id ℝ (WithLp 2 (ℝ × E)))

private theorem stronglyMeasurable_reflectedCoeff {a : ℝ}
    {A : WithLp 2 (ℝ × E) → WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E)}
    (hA : StronglyMeasurable A) : StronglyMeasurable (reflectedCoeff a A) := by
  have hS := (normalHalfSpace (E := E) a).isOpen.measurableSet
  rw [reflectedCoeff]
  refine hA.piecewise hS (StronglyMeasurable.piecewise
    (hS.preimage (normalReflection E a).continuous.measurable) ?_ stronglyMeasurable_const)
  exact (continuous_const.clm_comp (continuous_id.clm_comp continuous_const))
    |>.comp_stronglyMeasurable (hA.comp_measurable (normalReflection E a).continuous.measurable)

/-- The reflected coefficient field stays within `δ` of the identity. -/
private theorem ae_norm_reflectedCoeff_sub_id_le {a δ : ℝ} (hδ : 0 ≤ δ)
    {A : WithLp 2 (ℝ × E) → WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E)}
    (hAδ : ∀ᵐ x ∂(volume : Measure (WithLp 2 (ℝ × E))).restrict (normalHalfSpace (E := E) a),
      ‖A x - ContinuousLinearMap.id ℝ (WithLp 2 (ℝ × E))‖ ≤ δ) :
    ∀ᵐ x ∂(volume : Measure (WithLp 2 (ℝ × E))),
      ‖reflectedCoeff a A x - ContinuousLinearMap.id ℝ (WithLp 2 (ℝ × E))‖ ≤ δ := by
  classical
  rw [ae_restrict_iff' (normalHalfSpace (E := E) a).isOpen.measurableSet] at hAδ
  filter_upwards [hAδ, (measurePreserving_normalReflection a).quasiMeasurePreserving.ae hAδ]
    with x h₁ h₂
  rw [reflectedCoeff]
  by_cases hx : x ∈ (normalHalfSpace (E := E) a : Set (WithLp 2 (ℝ × E)))
  · rw [piecewise_eq_of_mem _ _ _ hx]
    exact h₁ hx
  rw [piecewise_eq_of_notMem _ _ _ hx]
  by_cases hx' : x ∈ normalReflection E a ⁻¹' (normalHalfSpace (E := E) a : Set (WithLp 2 (ℝ × E)))
  · rw [piecewise_eq_of_mem _ _ _ hx']
    exact (norm_conj_normalLinearReflection_sub_id_le _).trans (h₂ hx')
  · rw [piecewise_eq_of_notMem _ _ _ hx']
    rw [sub_self, ContinuousLinearMap.opNorm_zero]
    exact hδ

/-- **The reflected equation.** If `w` is the odd reflection of `u` and `tr (A D²u) = f` on `H`,
then `tr (A₁ D²w) = f₁` on the whole space, for the reflected coefficient field `A₁` and the odd
reflection `f₁ = f - f ∘ ρ` of `f`, both extended by zero off `H`. -/
private theorem ae_trace_reflectedCoeff_comp_eq {a : ℝ}
    {A : WithLp 2 (ℝ × E) → WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E)}
    {u : Wkp (volume : Measure (WithLp 2 (ℝ × E))) (normalHalfSpace a) p 2}
    {f : WithLp 2 (ℝ × E) → ℝ}
    (htr : ∀ᵐ x ∂(volume : Measure (WithLp 2 (ℝ × E))).restrict (normalHalfSpace (E := E) a),
      LinearMap.trace ℝ (WithLp 2 (ℝ × E)) ((A x).comp (Wkp.iteratedGradient 1 u x)) = f x)
    {w : Wkp (volume : Measure (WithLp 2 (ℝ × E))) ⊤ p 2}
    (hwD : Wkp.iteratedGradient 1 w =ᵐ[volume] fun x =>
      (normalHalfSpace (E := E) a : Set (WithLp 2 (ℝ × E))).indicator
          (Wkp.iteratedGradient 1 u) x -
        (normalLinearReflection E : WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E)) ∘L
          (normalHalfSpace (E := E) a : Set (WithLp 2 (ℝ × E))).indicator
            (Wkp.iteratedGradient 1 u) (normalReflection E a x) ∘L
          (normalLinearReflection E : WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E))) :
    ∀ᵐ x ∂(volume : Measure (WithLp 2 (ℝ × E))),
      LinearMap.trace ℝ (WithLp 2 (ℝ × E))
          ((reflectedCoeff a A x).comp (Wkp.iteratedGradient 1 w x)) =
        (normalHalfSpace (E := E) a : Set (WithLp 2 (ℝ × E))).indicator f x -
          (normalHalfSpace (E := E) a : Set (WithLp 2 (ℝ × E))).indicator f
            (normalReflection E a x) := by
  classical
  set S : Set (WithLp 2 (ℝ × E)) := (normalHalfSpace (E := E) a : Set (WithLp 2 (ℝ × E)))
  rw [ae_restrict_iff' (normalHalfSpace (E := E) a).isOpen.measurableSet] at htr
  filter_upwards [hwD, htr, (measurePreserving_normalReflection a).quasiMeasurePreserving.ae htr]
    with x hD h₁ h₂
  rw [hD, ← traceCLM_apply, reflectedCoeff]
  by_cases hx : x ∈ S
  · -- On `H` the reflected equation is the equation of `u`.
    have hρx := normalReflection_notMem_normalHalfSpace hx
    rw [piecewise_eq_of_mem _ _ _ hx, indicator_of_mem hx, indicator_of_notMem hρx,
      indicator_of_mem hx, indicator_of_notMem hρx, traceCLM_apply, ← h₁ hx]
    simp
  rw [piecewise_eq_of_notMem _ _ _ hx, indicator_of_notMem hx, indicator_of_notMem hx]
  by_cases hx' : x ∈ normalReflection E a ⁻¹' S
  · -- Across the hyperplane, `tr (R A R ∘ (-R D R)) = -tr (A D)`.
    have hρx : normalReflection E a x ∈ S := hx'
    rw [piecewise_eq_of_mem _ _ _ hx', indicator_of_mem hρx, indicator_of_mem hρx,
      traceCLM_conj_normalLinearReflection_comp_zero_sub, traceCLM_apply, h₂ hx', zero_sub]
  · -- On the hyperplane both sides vanish.
    have hρx : normalReflection E a x ∉ S := hx'
    rw [piecewise_eq_of_notMem _ _ _ hx', indicator_of_notMem hρx, indicator_of_notMem hρx]
    simp

/-- The case of a strongly measurable coefficient field close to the identity, by odd reflection
across the boundary hyperplane. -/
private theorem exists_wkp_value_ae_eq_of_norm_sub_id_le_of_normalHalfSpace_aux
    (hp : 1 < p) (hp_top : p ≠ ⊤) (hr : 1 < r) (hr_top : r ≠ ⊤) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (a : ℝ) (A : WithLp 2 (ℝ × E) → WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E)),
      StronglyMeasurable A →
      (∀ᵐ x ∂(volume : Measure (WithLp 2 (ℝ × E))).restrict (normalHalfSpace (E := E) a),
        ‖A x - ContinuousLinearMap.id ℝ (WithLp 2 (ℝ × E))‖ ≤ δ) →
      ∀ (u : Wkp (volume : Measure (WithLp 2 (ℝ × E))) (normalHalfSpace a) p 2)
        (f : WithLp 2 (ℝ × E) → ℝ),
        MemLp f r ((volume : Measure (WithLp 2 (ℝ × E))).restrict (normalHalfSpace (E := E) a)) →
        MemLp (Wkp.value 2 u : WithLp 2 (ℝ × E) → ℝ) r
          ((volume : Measure (WithLp 2 (ℝ × E))).restrict (normalHalfSpace (E := E) a)) →
        Wkp.firstOrder 1 u ∈ w1p0Submodule volume (normalHalfSpace a) p →
        (∀ᵐ x ∂(volume : Measure (WithLp 2 (ℝ × E))).restrict (normalHalfSpace (E := E) a),
          LinearMap.trace ℝ (WithLp 2 (ℝ × E)) ((A x).comp (Wkp.iteratedGradient 1 u x)) =
            f x) →
        ∃ v : Wkp (volume : Measure (WithLp 2 (ℝ × E))) (normalHalfSpace a) r 2,
          (Wkp.value 2 v : WithLp 2 (ℝ × E) → ℝ) =ᵐ[(volume : Measure (WithLp 2 (ℝ × E))).restrict
            (normalHalfSpace (E := E) a)] Wkp.value 2 u := by
  obtain ⟨δ, hδ, hgain⟩ :=
    exists_wkp_value_ae_eq_of_trace_comp_iteratedGradient_eq_of_norm_sub_id_le
      (E := WithLp 2 (ℝ × E)) hp hp_top hr hr_top
  refine ⟨δ, hδ, fun a A hA hAδ u f hf hur hu0 htr => ?_⟩
  -- The odd reflection `w` of `u` lies in `W^{2,p}(ℝ × E)` and solves the reflected equation, to
  -- which the whole-space integrability gain applies.
  obtain ⟨w, hwv, hwD⟩ := Wkp.exists_value_ae_eq_sub_comp_normalReflection u hu0
  obtain ⟨v, hv, -⟩ := hgain (reflectedCoeff a A)
    (stronglyMeasurable_reflectedCoeff hA).aestronglyMeasurable
    (ae_norm_reflectedCoeff_sub_id_le hδ.le hAδ) w _
    (memLp_indicator_sub_indicator_comp_normalReflection hf)
    ((memLp_indicator_sub_indicator_comp_normalReflection hur).ae_eq hwv.symm)
    (ae_trace_reflectedCoeff_comp_eq htr hwD)
  -- On `H` the value of `w` is that of `u`.
  refine ⟨Wkp.restrictL le_top 2 v, ?_⟩
  have hS := (normalHalfSpace (E := E) a).isOpen.measurableSet
  filter_upwards [Wkp.value_restrictL_ae le_top 2 v, ae_restrict_of_ae hv, ae_restrict_of_ae hwv,
    ae_restrict_mem hS] with x h₁ h₂ h₃ hx
  rw [h₁, h₂, h₃, indicator_of_mem hx,
    indicator_of_notMem (normalReflection_notMem_normalHalfSpace hx), sub_zero]

/-- The coefficient field `y ↦ e⁻¹ ((A + A†) / 2)(e y) e⁻†` of the equation for `u ∘ e` is
strongly measurable. -/
private theorem stronglyMeasurable_conj_symmPart
    {A : WithLp 2 (ℝ × E) → WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E)}
    (hA : StronglyMeasurable A) (e : WithLp 2 (ℝ × E) ≃L[ℝ] WithLp 2 (ℝ × E)) :
    StronglyMeasurable fun y => (e.symm : WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E)) ∘L
      ((2⁻¹ : ℝ) • (A (e y) + (A (e y)).adjoint)) ∘L
        (e.symm : WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E)).adjoint := by
  have hΦ : Continuous fun X : WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E) =>
      (e.symm : WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E)) ∘L ((2⁻¹ : ℝ) • (X + X.adjoint)) ∘L
        (e.symm : WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E)).adjoint :=
    continuous_const.clm_comp
      (((continuous_id.add ContinuousLinearMap.adjoint.continuous).const_smul (2⁻¹ : ℝ)).clm_comp
        continuous_const)
  exact hΦ.comp_stronglyMeasurable (hA.comp_measurable e.continuous.measurable)

/-- A linear automorphism `e` mapping `H' = e⁻¹(H)` onto `H`, and its inverse, carry almost
everywhere statements on `H` and `H'` to each other. -/
private theorem quasiMeasurePreserving_restrict_normalHalfSpace
    (e : WithLp 2 (ℝ × E) ≃L[ℝ] WithLp 2 (ℝ × E)) {a a' : ℝ}
    (h : (normalHalfSpace (E := E) a' : Set (WithLp 2 (ℝ × E))) =
      e ⁻¹' (normalHalfSpace (E := E) a : Set (WithLp 2 (ℝ × E))))
    (h' : (normalHalfSpace (E := E) a : Set (WithLp 2 (ℝ × E))) =
      e.symm ⁻¹' (normalHalfSpace (E := E) a' : Set (WithLp 2 (ℝ × E)))) :
    QuasiMeasurePreserving e
        ((volume : Measure (WithLp 2 (ℝ × E))).restrict (normalHalfSpace (E := E) a'))
        ((volume : Measure (WithLp 2 (ℝ × E))).restrict (normalHalfSpace (E := E) a)) ∧
      QuasiMeasurePreserving e.symm
        ((volume : Measure (WithLp 2 (ℝ × E))).restrict (normalHalfSpace (E := E) a))
        ((volume : Measure (WithLp 2 (ℝ × E))).restrict (normalHalfSpace (E := E) a')) := by
  have hqe := e.toContinuousAddEquiv.quasiMeasurePreserving_addHaar
    (volume : Measure (WithLp 2 (ℝ × E))) volume
  have hqe' := e.symm.toContinuousAddEquiv.quasiMeasurePreserving_addHaar
    (volume : Measure (WithLp 2 (ℝ × E))) volume
  rw [ContinuousLinearEquiv.toContinuousAddEquiv_coe] at hqe hqe'
  exact ⟨hqe.restrict (h ▸ mapsTo_preimage _ _), hqe'.restrict (h' ▸ mapsTo_preimage _ _)⟩

/-- **Integrability gain on a half-space for strong solutions vanishing on the boundary**
(Gilbarg–Trudinger, Lemma 9.16, near a flat boundary portion). Let `1 < p, r < ∞`. There is
`δ > 0`, depending only on `E`, `p` and `r`, with the following property. Let `H = {x | a < x.fst}`
be a half-space of `ℝ × E`, let `A₀` be an operator on `ℝ × E` with `λ ‖ξ‖² ≤ ⟪A₀ ξ, ξ⟫` and
`0 < λ`, and let `A` be an almost everywhere strongly measurable field of endomorphisms of `ℝ × E`
on `H` with `‖A x - A₀‖ ≤ δ λ` for almost every `x ∈ H`. Let `u ∈ W^{2,p}(H)`, whose first-order
part lies in `W^{1,p}_0(H)`, solve `tr (A D²u) = f` almost everywhere on `H`, where
`u, f ∈ Lʳ(H)`. Then `u ∈ W^{2,r}(H)`: its value is the value of an element `v` of `W^{2,r}(H)`,
and the weak Hessians of `u` and `v` agree almost everywhere on `H`.

Neither `A₀` nor `A` need be symmetric. -/
theorem exists_wkp_value_ae_eq_of_trace_comp_iteratedGradient_eq_of_norm_sub_le_of_normalHalfSpace
    (hp : 1 < p) (hp_top : p ≠ ⊤) (hr : 1 < r) (hr_top : r ≠ ⊤) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (a : ℝ) (A₀ : WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E)) (lam : ℝ),
      0 < lam → (∀ ξ, lam * ‖ξ‖ ^ 2 ≤ ⟪A₀ ξ, ξ⟫_ℝ) →
      ∀ A : WithLp 2 (ℝ × E) → WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E),
      AEStronglyMeasurable A
        ((volume : Measure (WithLp 2 (ℝ × E))).restrict (normalHalfSpace (E := E) a)) →
      (∀ᵐ x ∂(volume : Measure (WithLp 2 (ℝ × E))).restrict (normalHalfSpace (E := E) a),
        ‖A x - A₀‖ ≤ δ * lam) →
      ∀ (u : Wkp (volume : Measure (WithLp 2 (ℝ × E))) (normalHalfSpace a) p 2)
        (f : WithLp 2 (ℝ × E) → ℝ),
        MemLp f r ((volume : Measure (WithLp 2 (ℝ × E))).restrict (normalHalfSpace (E := E) a)) →
        MemLp (Wkp.value 2 u : WithLp 2 (ℝ × E) → ℝ) r
          ((volume : Measure (WithLp 2 (ℝ × E))).restrict (normalHalfSpace (E := E) a)) →
        Wkp.firstOrder 1 u ∈ w1p0Submodule volume (normalHalfSpace a) p →
        (∀ᵐ x ∂(volume : Measure (WithLp 2 (ℝ × E))).restrict (normalHalfSpace (E := E) a),
          LinearMap.trace ℝ (WithLp 2 (ℝ × E)) ((A x).comp (Wkp.iteratedGradient 1 u x)) =
            f x) →
        ∃ v : Wkp (volume : Measure (WithLp 2 (ℝ × E))) (normalHalfSpace a) r 2,
          (Wkp.value 2 v : WithLp 2 (ℝ × E) → ℝ) =ᵐ[(volume : Measure (WithLp 2 (ℝ × E))).restrict
            (normalHalfSpace (E := E) a)] Wkp.value 2 u ∧
          (Wkp.iteratedGradient 1 v : WithLp 2 (ℝ × E) → IteratedGradient (WithLp 2 (ℝ × E)) 1)
            =ᵐ[(volume : Measure (WithLp 2 (ℝ × E))).restrict (normalHalfSpace (E := E) a)]
            Wkp.iteratedGradient 1 u := by
  obtain ⟨δ, hδ, hid⟩ :=
    exists_wkp_value_ae_eq_of_norm_sub_id_le_of_normalHalfSpace_aux (E := E) hp hp_top hr hr_top
  refine ⟨δ, hδ, fun a A₀ lam hlam hA₀ A hA hAδ u f hf hur hu0 htr => ?_⟩
  -- A linear change of variables `e` with `e e† = (A₀ + A₀†) / 2` maps the half-space
  -- `H' = {a / c < x.fst}` onto `H`; almost everywhere statements transfer along `e` and `e⁻¹`.
  obtain ⟨e, c, hee, he, hH⟩ := exists_continuousLinearEquiv_preimage_normalHalfSpace hlam hA₀
  have hHH' : (normalHalfSpace (E := E) a : Set (WithLp 2 (ℝ × E))) =
      e.symm ⁻¹' (normalHalfSpace (E := E) (a / c) : Set (WithLp 2 (ℝ × E))) := by
    rw [hH a, ← preimage_comp]
    ext x
    simp
  obtain ⟨hpull, hpush⟩ := quasiMeasurePreserving_restrict_normalHalfSpace e (hH a) hHH'
  -- `w = u ∘ e ∈ W^{2,p}(H')` has weak Hessian `e† D²u(e ·) e` and zero boundary values.
  obtain ⟨w, hwv, hwD, h0⟩ := Wkp.exists_value_ae_eq_comp_continuousLinearEquiv hp_top e (hH a) u
  -- It solves `tr (b D²w) = f ∘ e` with `b(y) = e⁻¹ ((A + A†) / 2)(e y) e⁻†` close to `1`, where
  -- `A` is replaced by a strongly measurable version.
  obtain ⟨A', hA', hAA'⟩ : ∃ A' : WithLp 2 (ℝ × E) → WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E),
      StronglyMeasurable A' ∧ A =ᵐ[(volume : Measure (WithLp 2 (ℝ × E))).restrict
        (normalHalfSpace (E := E) a)] A' :=
    ⟨hA.mk A, hA.stronglyMeasurable_mk, hA.ae_eq_mk⟩
  have hMN : (e : WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E)) ∘L
      (e.symm : WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E)) =
        ContinuousLinearMap.id ℝ (WithLp 2 (ℝ × E)) := by
    ext x; simp
  obtain ⟨v', hv'⟩ := hid (a / c)
    (fun y => (e.symm : WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E)) ∘L
      ((2⁻¹ : ℝ) • (A' (e y) + (A' (e y)).adjoint)) ∘L
        (e.symm : WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E)).adjoint)
    (stronglyMeasurable_conj_symmPart hA' e)
    (by
      filter_upwards [hpull.ae hAδ, hpull.ae hAA'] with y h₁ h₂
      refine (norm_conj_symmPart_sub_id_le hlam e hee he (A' (e y))).trans ?_
      rw [← h₂]
      calc lam⁻¹ * ‖A (e y) - A₀‖ ≤ lam⁻¹ * (δ * lam) := by gcongr
        _ = δ := by field_simp)
    w (fun y => f (e y)) (hH a ▸ hf.comp_continuousLinearEquiv_restrict_preimage e)
    ((hH a ▸ hur.comp_continuousLinearEquiv_restrict_preimage e).ae_eq hwv.symm) (h0 hu0)
    (by
      filter_upwards [hwD, hpull.ae (Wkp.adjoint_iteratedGradient_one_ae_eq u), hpull.ae htr,
        hpull.ae hAA'] with y h₁ h₂ h₃ h₄
      rw [h₁, ← traceCLM_apply, ContinuousLinearMap.traceCLM_comp_adjoint_comp_comp_of_comp_eq_id
        hMN, ContinuousLinearMap.traceCLM_symmPart_comp _ _ h₂, traceCLM_apply, ← h₄, h₃])
  -- Composing back with `e⁻¹` gives `v ∈ W^{2,r}(H)` with value `u`.
  obtain ⟨v, hv, -, -⟩ :=
    Wkp.exists_value_ae_eq_comp_continuousLinearEquiv hr_top e.symm (U := normalHalfSpace a)
      (W := normalHalfSpace (a / c)) hHH' v'
  have hval : (Wkp.value 2 v : WithLp 2 (ℝ × E) → ℝ)
      =ᵐ[(volume : Measure (WithLp 2 (ℝ × E))).restrict (normalHalfSpace (E := E) a)]
        Wkp.value 2 u := by
    filter_upwards [hv, hpush.ae (hv'.trans hwv)] with x h₁ h₂
    rw [h₁, h₂, ContinuousLinearEquiv.apply_symm_apply]
  exact ⟨v, hval, Wkp.iteratedGradient_ae_eq_of_value_ae_eq 1 hval⟩

end TauCeti
