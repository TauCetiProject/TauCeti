/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Convex.MongeAmpere.Basic
import TauCeti.Analysis.InnerProductSpace.Adjoint

/-!
# Affine renormalization of the Monge–Ampère measure

Adding the affine function `x ↦ ⟪x, q⟫ + c` to a function `f : E → EReal` translates every
subdifferential, and hence every subgradient image, by `q`
(`TauCeti.subgradientImage_add_affine`). It also preserves convexity of the real epigraph and
the effective domain, so the Aleksandrov Monge–Ampère measure with respect to an additive Haar
measure is unchanged.

This invariance permits the standard normalization of a convex function by subtracting a
supporting plane before studying its sections.

Precomposing with an affine equivalence `A` of linear part `L` changes coordinates in the domain:
the subgradients of `f ∘ A` at `x` are the images under the adjoint `L*` of the subgradients of
`f` at `A x` (`TauCeti.subdifferential_comp_affineEquiv`). Since `L*` multiplies Haar measure by
`|det L|`, the Monge–Ampère measure transforms by `MA_{f ∘ A}(s) = |det L| MA_f(A '' s)`. So a
lower bound `MA_f ≥ λ μ` on a set `s` becomes `MA_{f ∘ A} ≥ λ |det L|² μ` on `A⁻¹(s)`, since
`μ(A '' t) = |det L| μ(t)`: this is how an estimate proved for a normalized convex domain
transfers to an arbitrary one.

## Main statements

* `TauCeti.mongeAmpereMeasure_mul_of_pos` gives the homogeneity of the Monge–Ampère measure
  under positive scaling of an extended-real potential, and
  `TauCeti.mongeAmpereMeasure_ite_mul_of_pos` is its form for a real function on a set.
* `TauCeti.mongeAmpereMeasure_add_affine` proves invariance of the Aleksandrov Monge–Ampère
  measure under addition of an affine function, and `TauCeti.mongeAmpereMeasure_ite_add_linearMap`
  is its form for a finite convex function on a set and an affine function given by a linear
  functional.
* `TauCeti.mongeAmpereMeasure_comp_affineEquiv_apply` and
  `TauCeti.mongeAmpereMeasure_comp_affineEquiv` give the change of variables formula for the
  Monge–Ampère measure under an affine equivalence of the domain, and
  `TauCeti.mongeAmpereMeasure_ite_comp_symm_apply` is its form for a finite function on a set
  transported to the image of the set.

## References

* C. E. Gutiérrez, *The Monge–Ampère Equation*, 2nd ed., Progress in Nonlinear Differential
  Equations and Their Applications 89, Birkhäuser, 2016, §1.1.
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory Measure Set Module

open scoped ENNReal Pointwise

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Precomposing with an affine equivalence `A` maps the subdifferential at `A x` onto the
subdifferential at `x` by the adjoint of the linear part of `A`. -/
theorem subdifferential_comp_affineEquiv (f : E → EReal) (A : E ≃ᵃ[ℝ] E) (x : E) :
    subdifferential (innerₗ E) (f ∘ A) x =
      LinearMap.adjoint (A.linear : E →ₗ[ℝ] E) '' subdifferential (innerₗ E) f (A x) := by
  have hlin (e : E ≃ᵃ[ℝ] E) (a b : E) : (e.linear : E →ₗ[ℝ] E) (a - b) = e a - e b := by
    simpa using (e : E →ᵃ[ℝ] E).linear_apply_vsub a b
  ext p
  constructor
  · intro hp
    obtain ⟨hb, ht, h⟩ := (mem_subdifferential_iff _).1 hp
    refine ⟨LinearMap.adjoint (A.symm.linear : E →ₗ[ℝ] E) p,
      (mem_subdifferential_iff _).2 ⟨hb, ht, fun y => ?_⟩, ?_⟩
    · -- `⟪y - A x, (L⁻¹)* p⟫ = ⟪A⁻¹ y - x, p⟫`
      have hy := h (A.symm y)
      simp only [Function.comp_apply, AffineEquiv.apply_symm_apply, innerₗ_apply_apply] at hy
      simpa only [innerₗ_apply_apply, LinearMap.adjoint_inner_right, hlin,
        AffineEquiv.symm_apply_apply] using hy
    · rw [← LinearMap.comp_apply, ← LinearMap.adjoint_comp, AffineEquiv.linear_symm,
        LinearEquiv.symm_comp, LinearMap.adjoint_id, LinearMap.id_apply]
  · rintro ⟨q, hq, rfl⟩
    obtain ⟨hb, ht, h⟩ := (mem_subdifferential_iff _).1 hq
    refine (mem_subdifferential_iff _).2 ⟨hb, ht, fun x' => ?_⟩
    simpa only [Function.comp_apply, innerₗ_apply_apply, LinearMap.adjoint_inner_right,
      hlin] using h (A x')

variable [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]

/-- **Affine invariance of the Aleksandrov Monge–Ampère measure.** Adding an affine function
`x ↦ ⟪x, q⟫ + c` to `f : E → EReal` does not change its Monge–Ampère measure with respect to an
additive Haar measure. -/
theorem mongeAmpereMeasure_add_affine (f : E → EReal) (q : E) (c : ℝ) :
    mongeAmpereMeasure μ (fun x ↦ f x + ((inner ℝ x q + c : ℝ) : EReal)) =
      mongeAmpereMeasure μ f := by
  set g : E → EReal := fun x ↦ f x + ((inner ℝ x q + c : ℝ) : EReal)
  have hconv : Convex ℝ {p : E × ℝ | g p.1 ≤ p.2} ↔ Convex ℝ {p : E × ℝ | f p.1 ≤ p.2} := by
    simpa only [innerₗ_apply_apply] using convex_epigraph_add_affine_iff (innerₗ E) (f := f) q c
  by_cases hf : Convex ℝ {p : E × ℝ | f p.1 ≤ p.2}
  swap
  · have hg : ¬Convex ℝ {p : E × ℝ | g p.1 ≤ p.2} := fun hg ↦ hf (hconv.1 hg)
    rw [mongeAmpereMeasure_eq_zero_of_not_convex μ hf,
      mongeAmpereMeasure_eq_zero_of_not_convex μ hg]
  by_cases hbot : ∀ x, f x ≠ ⊥
  swap
  · obtain ⟨x, hx⟩ := not_forall_not.1 hbot
    rw [mongeAmpereMeasure_eq_zero_of_eq_bot μ hx,
      mongeAmpereMeasure_eq_zero_of_eq_bot μ (x := x) (by simp [g, hx])]
  have hgbot (x : E) : g x ≠ ⊥ := by simp [g, hbot x]
  have hdom : {x | g x ≠ ⊤} = {x | f x ≠ ⊤} := by
    ext x
    exact EReal.add_ne_top_iff_ne_top_left (EReal.coe_ne_bot _) (EReal.coe_ne_top _)
  ext s hs
  rw [mongeAmpereMeasure_apply μ (hconv.2 hf) hgbot AbsolutelyContinuous.rfl hs,
    mongeAmpereMeasure_apply μ hf hbot AbsolutelyContinuous.rfl hs, hdom]
  have h := subgradientImage_add_affine (innerₗ E) (f := f) q c (s ∩ interior {x | f x ≠ ⊤})
  simp only [innerₗ_apply_apply] at h
  rw [h]
  simpa only [sub_eq_add_neg, add_comm] using
    measure_preimage_add μ (-q) (subgradientImage (innerₗ E) f (s ∩ interior {x | f x ≠ ⊤}))

/-- **Affine invariance for a finite convex function on a set.** Adding a linear functional `ℓ`
and a constant to a real function `u`, extended by `⊤` off `U`, does not change its Monge–Ampère
measure with respect to an additive Haar measure. This is the form in which a supporting plane
`y ↦ u x + ℓ (y - x)` is subtracted from `u` to normalize a section. -/
theorem mongeAmpereMeasure_ite_add_linearMap {U : Set E} [DecidablePred (· ∈ U)] (u : E → ℝ)
    (ℓ : E →ₗ[ℝ] ℝ) (c : ℝ) :
    mongeAmpereMeasure μ (fun y => if y ∈ U then ((u y + ℓ y + c : ℝ) : EReal) else ⊤) =
      mongeAmpereMeasure μ (fun y => if y ∈ U then (u y : EReal) else ⊤) := by
  -- Represent `ℓ` by the inner product with a vector `q`.
  set q := (InnerProductSpace.toDual ℝ E).symm (LinearMap.toContinuousLinearMap ℓ)
  have hq (y : E) : ℓ y = inner ℝ y q := by
    rw [real_inner_comm, InnerProductSpace.toDual_symm_apply, LinearMap.coe_toContinuousLinearMap']
  conv_rhs => rw [← mongeAmpereMeasure_add_affine μ _ q c]
  congr 1
  funext y
  split_ifs <;> simp [hq, add_assoc]

/-- Multiplying an extended-real potential by a positive scalar `c` multiplies its Aleksandrov
Monge–Ampère measure with respect to additive Haar measure by `c ^ finrank ℝ E`. -/
theorem mongeAmpereMeasure_mul_of_pos (f : E → EReal) {c : ℝ} (hc : 0 < c) :
    mongeAmpereMeasure μ (fun x ↦ (c : EReal) * f x) =
      ENNReal.ofReal (c ^ finrank ℝ E) • mongeAmpereMeasure μ f := by
  set g : E → EReal := fun x ↦ (c : EReal) * f x
  have hc' : 0 < (c : EReal) := EReal.coe_pos.2 hc
  have hle (a b : EReal) : (c : EReal) * a ≤ (c : EReal) * b ↔ a ≤ b := by
    rw [← EReal.div_le_iff_le_mul hc' (EReal.coe_ne_top c), ← EReal.mul_div,
      EReal.mul_div_cancel (EReal.coe_ne_bot c) (EReal.coe_ne_top c) hc'.ne']
  have heq (a b : EReal) : (c : EReal) * a = (c : EReal) * b ↔ a = b := by
    simp only [le_antisymm_iff, hle]
  have hbot (x : E) : g x ≠ ⊥ ↔ f x ≠ ⊥ := by
    simpa only [g, EReal.coe_mul_bot_of_pos hc] using (heq (f x) ⊥).not
  have htop (x : E) : g x ≠ ⊤ ↔ f x ≠ ⊤ := by
    simpa only [g, EReal.coe_mul_top_of_pos hc] using (heq (f x) ⊤).not
  -- Scaling the height coordinate carries one real epigraph onto the other.
  let scaleHeight (a : ℝ) : E × ℝ →ₗ[ℝ] E × ℝ :=
    LinearMap.prodMap LinearMap.id (a • LinearMap.id)
  have hheight (x : E) (t : ℝ) : g x ≤ ((c * t : ℝ) : EReal) ↔ f x ≤ (t : EReal) := by
    simp only [g, EReal.coe_mul, hle]
  have hpreimage : scaleHeight c ⁻¹' {p : E × ℝ | g p.1 ≤ p.2} =
      {p : E × ℝ | f p.1 ≤ p.2} :=
    Set.ext fun p ↦ hheight p.1 p.2
  have hpreimageInv : scaleHeight c⁻¹ ⁻¹' {p : E × ℝ | f p.1 ≤ p.2} =
      {p : E × ℝ | g p.1 ≤ p.2} := by
    ext p
    simp only [mem_preimage, mem_ofPred_eq, scaleHeight, LinearMap.prodMap_apply,
      LinearMap.id_apply, LinearMap.smul_apply, smul_eq_mul]
    rw [← hheight, mul_inv_cancel_left₀ hc.ne']
  have hconv : Convex ℝ {p : E × ℝ | g p.1 ≤ p.2} ↔ Convex ℝ {p : E × ℝ | f p.1 ≤ p.2} :=
    ⟨fun h ↦ hpreimage ▸ h.linear_preimage (scaleHeight c),
      fun h ↦ hpreimageInv ▸ h.linear_preimage (scaleHeight c⁻¹)⟩
  by_cases hf : Convex ℝ {p : E × ℝ | f p.1 ≤ p.2}
  swap
  · rw [mongeAmpereMeasure_eq_zero_of_not_convex μ hf,
      mongeAmpereMeasure_eq_zero_of_not_convex μ (mt hconv.1 hf), smul_zero]
  by_cases hfbot : ∀ x, f x ≠ ⊥
  swap
  · obtain ⟨x, hx⟩ := not_forall_not.1 hfbot
    have hgx : g x = ⊥ := by
      simp only [g, hx, EReal.coe_mul_bot_of_pos hc]
    rw [mongeAmpereMeasure_eq_zero_of_eq_bot μ hx,
      mongeAmpereMeasure_eq_zero_of_eq_bot μ hgx, smul_zero]
  have hdom : {x | g x ≠ ⊤} = {x | f x ≠ ⊤} := Set.ext htop
  have hsub (x p : E) : c • p ∈ subdifferential (innerₗ E) g x ↔
      p ∈ subdifferential (innerₗ E) f x := by
    have hineq (y : E) : g x + (inner ℝ (y - x) (c • p) : EReal) ≤ g y ↔
        f x + (inner ℝ (y - x) p : EReal) ≤ f y := by
      simp only [g, real_inner_smul_right, EReal.coe_mul,
        ← EReal.left_distrib_of_nonneg_of_ne_top hc'.le (EReal.coe_ne_top c), hle]
    simp only [mem_subdifferential_iff, hbot, htop, innerₗ_apply_apply, hineq]
  have himage (s : Set E) : subgradientImage (innerₗ E) g s =
      c • subgradientImage (innerₗ E) f s := by
    ext p
    rw [← smul_inv_smul₀ hc.ne' p, smul_mem_smul_set_iff₀ hc.ne']
    simp only [mem_subgradientImage_iff, hsub]
  ext s hs
  rw [_root_.smul_apply, smul_eq_mul,
    mongeAmpereMeasure_apply μ (hconv.2 hf) (fun x ↦ (hbot x).2 (hfbot x))
      AbsolutelyContinuous.rfl hs,
    mongeAmpereMeasure_apply μ hf hfbot AbsolutelyContinuous.rfl hs, hdom, himage,
    addHaar_smul, abs_of_pos (pow_pos hc _)]

/-- Positive scaling of a real potential on a set, extended by `⊤` off that set. -/
theorem mongeAmpereMeasure_ite_mul_of_pos {Ω : Set E} [DecidablePred (· ∈ Ω)] {u : E → ℝ}
    {c : ℝ} (hc : 0 < c) :
    mongeAmpereMeasure μ (fun x => if x ∈ Ω then ((c * u x : ℝ) : EReal) else ⊤) =
      ENNReal.ofReal (c ^ finrank ℝ E) •
        mongeAmpereMeasure μ (fun x => if x ∈ Ω then (u x : EReal) else ⊤) := by
  have hscale : (fun x ↦ (c : EReal) * (if x ∈ Ω then (u x : EReal) else ⊤)) =
      (fun x ↦ if x ∈ Ω then ((c * u x : ℝ) : EReal) else ⊤) := by
    funext x
    split_ifs <;> simp only [EReal.coe_mul, EReal.coe_mul_top_of_pos hc]
  rw [← hscale, mongeAmpereMeasure_mul_of_pos μ _ hc]

/-- Positive scaling and a constant shift of a real potential on a set, extended by `⊤` off that
set: the Monge–Ampère measure is multiplied by `c ^ finrank ℝ E`. -/
theorem mongeAmpereMeasure_ite_mul_add_of_pos {Ω : Set E} [DecidablePred (· ∈ Ω)] {u : E → ℝ}
    {c : ℝ} (hc : 0 < c) (b : ℝ) :
    mongeAmpereMeasure μ (fun x => if x ∈ Ω then ((c * u x + b : ℝ) : EReal) else ⊤) =
      ENNReal.ofReal (c ^ finrank ℝ E) •
        mongeAmpereMeasure μ (fun x => if x ∈ Ω then (u x : EReal) else ⊤) := by
  have hshift := mongeAmpereMeasure_ite_add_linearMap μ (U := Ω) (fun y => c * u y) 0 b
  rw [mongeAmpereMeasure_ite_mul_of_pos μ hc] at hshift
  simpa only [LinearMap.zero_apply, add_zero] using hshift

/-- **Change of variables for the Aleksandrov Monge–Ampère measure.** For an affine equivalence
`A` of `E` with linear part `L` and a measurable set `s`,
`MA_{f ∘ A}(s) = |det L| MA_f(A '' s)` for the Monge–Ampère measures with respect to an additive
Haar measure. -/
theorem mongeAmpereMeasure_comp_affineEquiv_apply (f : E → EReal) (A : E ≃ᵃ[ℝ] E) {s : Set E}
    (hs : MeasurableSet s) :
    mongeAmpereMeasure μ (f ∘ A) s =
      ENNReal.ofReal |LinearMap.det (A.linear : E →ₗ[ℝ] E)| * mongeAmpereMeasure μ f (A '' s) := by
  -- Convexity of the epigraph and the absence of `⊥` transfer along `A` in both directions.
  have hconv (g : E → EReal) (e : E ≃ᵃ[ℝ] E) (hg : Convex ℝ {p : E × ℝ | g p.1 ≤ p.2}) :
      Convex ℝ {p : E × ℝ | (g ∘ e) p.1 ≤ p.2} := by
    intro p hp q hq a b ha hb hab
    have h := hg (x := (e p.1, p.2)) hp (y := (e q.1, q.2)) hq ha hb hab
    have he : e (a • p.1 + b • q.1) = a • e p.1 + b • e q.1 :=
      Convex.combo_affine_apply (f := (e : E →ᵃ[ℝ] E)) hab
    simpa [he] using h
  have hconv' : Convex ℝ {p : E × ℝ | (f ∘ A) p.1 ≤ p.2} ↔
      Convex ℝ {p : E × ℝ | f p.1 ≤ p.2} :=
    ⟨fun h => by simpa [Function.comp_def] using hconv _ A.symm h, hconv f A⟩
  have hbot' : (∀ x, (f ∘ A) x ≠ ⊥) ↔ ∀ x, f x ≠ ⊥ :=
    ⟨fun h y => by simpa using h (A.symm y), fun h x => h (A x)⟩
  -- `A` is a homeomorphism, since `E` is finite-dimensional.
  let H := (AffineEquiv.toContinuousAffineEquiv A).toHomeomorph
  have hAs : MeasurableSet (A '' s) := H.toMeasurableEquiv.measurableSet_image.2 hs
  by_cases hf : Convex ℝ {p : E × ℝ | f p.1 ≤ p.2}
  swap
  · rw [mongeAmpereMeasure_eq_zero_of_not_convex μ hf,
      mongeAmpereMeasure_eq_zero_of_not_convex μ (mt hconv'.1 hf)]
    simp
  by_cases hbot : ∀ x, f x ≠ ⊥
  swap
  · obtain ⟨y, hy⟩ := not_forall_not.1 hbot
    rw [mongeAmpereMeasure_eq_zero_of_eq_bot μ hy,
      mongeAmpereMeasure_eq_zero_of_eq_bot μ (x := A.symm y) (by simpa using hy)]
    simp
  rw [mongeAmpereMeasure_apply μ (hconv'.2 hf) (hbot'.2 hbot) AbsolutelyContinuous.rfl hs,
    mongeAmpereMeasure_apply μ hf hbot AbsolutelyContinuous.rfl hAs]
  -- The interior of the effective domain of `f ∘ A` is the preimage of that of `f`.
  have hdom : interior {x | (f ∘ A) x ≠ ⊤} = A ⁻¹' interior {y | f y ≠ ⊤} :=
    -- `⇑H` is `⇑A` by definition.
    (H.preimage_interior {y | f y ≠ ⊤}).symm
  have himage : subgradientImage (innerₗ E) (f ∘ A) (s ∩ interior {x | (f ∘ A) x ≠ ⊤}) =
      LinearMap.adjoint (A.linear : E →ₗ[ℝ] E) ''
        subgradientImage (innerₗ E) f (A '' s ∩ interior {y | f y ≠ ⊤}) := by
    rw [hdom, ← image_inter_preimage]
    ext p
    simp only [mem_subgradientImage_iff, mem_image, subdifferential_comp_affineEquiv]
    constructor
    · rintro ⟨x, hx, q, hq, rfl⟩
      exact ⟨q, ⟨A x, ⟨x, hx, rfl⟩, hq⟩, rfl⟩
    · rintro ⟨q, ⟨-, ⟨x, hx, rfl⟩, hq⟩, rfl⟩
      exact ⟨x, hx, q, hq, rfl⟩
  rw [himage, addHaar_image_linearMap, LinearMap.det_adjoint, star_trivial]

/-- Transport of the Monge–Ampère measure of a function on `G` to the function `v ∘ T⁻¹` on
`T '' G = T⁻¹ ⁻¹' G`: the measure of `s` is `|det L|` times the Monge–Ampère measure of `v` on
`G` of `T⁻¹ '' s`, where `L` is the linear part of `T⁻¹`. -/
theorem mongeAmpereMeasure_ite_comp_symm_apply (T : E ≃ᵃ[ℝ] E) (G : Set E)
    [DecidablePred (· ∈ G)] [DecidablePred (· ∈ T.symm ⁻¹' G)] (v : E → ℝ) {s : Set E}
    (hs : MeasurableSet s) :
    mongeAmpereMeasure μ (fun y => if y ∈ T.symm ⁻¹' G then (v (T.symm y) : EReal) else ⊤) s =
      ENNReal.ofReal |LinearMap.det (T.symm.linear : E →ₗ[ℝ] E)| *
        mongeAmpereMeasure μ (fun x => if x ∈ G then (v x : EReal) else ⊤) (T.symm '' s) := by
  have hfun : (fun y => if y ∈ T.symm ⁻¹' G then (v (T.symm y) : EReal) else ⊤) =
      (fun x => if x ∈ G then (v x : EReal) else ⊤) ∘ T.symm := by
    funext y
    by_cases hy : T.symm y ∈ G <;> simp only [Function.comp_apply, mem_preimage, hy, ↓reduceIte]
  rw [hfun, mongeAmpereMeasure_comp_affineEquiv_apply μ _ T.symm hs]

/-- **Change of variables for the Aleksandrov Monge–Ampère measure**, as an identity of measures:
for an affine equivalence `A` of `E` with linear part `L`, the Monge–Ampère measure of `f ∘ A`
is `|det L|` times the pullback of that of `f` along `A`. -/
theorem mongeAmpereMeasure_comp_affineEquiv (f : E → EReal) (A : E ≃ᵃ[ℝ] E) :
    mongeAmpereMeasure μ (f ∘ A) =
      ENNReal.ofReal |LinearMap.det (A.linear : E →ₗ[ℝ] E)| •
        (mongeAmpereMeasure μ f).map A.symm := by
  ext s hs
  have hA : Measurable A.symm := (AffineEquiv.toContinuousAffineEquiv A.symm).continuous.measurable
  rw [mongeAmpereMeasure_comp_affineEquiv_apply μ f A hs, _root_.smul_apply,
    Measure.map_apply hA hs, smul_eq_mul, ← AffineEquiv.image_symm]
  simp

end TauCeti
