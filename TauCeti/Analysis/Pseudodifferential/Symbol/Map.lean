/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Symbol.Basic

/-!
# Images of symbols under maps of the coefficient spaces

The image of a symbol under a continuous linear map of the coefficient spaces, such as conjugation
by isomorphisms of `V` and `W`, has the same order (`TauCeti.Symbol.map`), and commutes with
spatial and frequency derivatives (`TauCeti.Symbol.spatialDeriv_map`,
`TauCeti.Symbol.frequencyDeriv_map`). In particular, if every value of a symbol commutes with an
operator `T`, so do the values of its derivatives
(`TauCeti.Symbol.commute_coefficient_spatialDeriv`,
`TauCeti.Symbol.commute_coefficient_frequencyDeriv`).

The image of a symbol with estimates uniform in the position, or with compact spatial support, has
the same property (`TauCeti.Symbol.IsUniform.map`, `TauCeti.Symbol.HasCompactSpatialSupport.map`).
-/

public section

noncomputable section

namespace TauCeti

namespace Symbol

variable {n : ℕ} {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W]
  [NormedSpace ℂ W] {m : ℝ}

section Map

variable {V' W' : Type*} [NormedAddCommGroup V'] [NormedSpace ℂ V'] [NormedAddCommGroup W']
  [NormedSpace ℂ W']

/-- The image `x, ξ ↦ Φ (a(x, ξ))` of a symbol under a continuous linear map `Φ` of the coefficient
spaces is a symbol of the same order. For isomorphisms `e₁ : V ≃L[ℂ] V'` and `e₂ : W ≃L[ℂ] W'`,
conjugation `T ↦ e₂ ∘ T ∘ e₁⁻¹` transports symbols with coefficients in `V →L[ℂ] W` to symbols
with coefficients in `V' →L[ℂ] W'`. -/
def map (Φ : (V →L[ℂ] W) →L[ℝ] (V' →L[ℂ] W')) (a : Symbol n V W m) : Symbol n V' W' m where
  coefficient := Φ ∘ a.coefficient
  contDiff_coefficient := Φ.contDiff.comp a.contDiff_coefficient
  exists_bound K hK α β := by
    obtain ⟨C, hC0, hC⟩ := a.exists_bound K hK α β
    refine ⟨‖Φ‖ * C, by positivity, fun x hx ξ ↦ ?_⟩
    rw [Φ.mixedDeriv_comp_left a.contDiff_coefficient, mul_assoc]
    exact Φ.le_opNorm_of_le (hC x hx ξ)

@[simp]
theorem coefficient_map (Φ : (V →L[ℂ] W) →L[ℝ] (V' →L[ℂ] W')) (a : Symbol n V W m)
    (p : CoordinateSpace n × CoordinateSpace n) : (a.map Φ).coefficient p = Φ (a.coefficient p) :=
  (rfl)

/-- The coefficient of the symbol transported by conjugation `T ↦ e₂ ∘ T ∘ e₁⁻¹` along
isomorphisms `e₁ : V ≃L[ℂ] V'` and `e₂ : W ≃L[ℂ] W'` is the conjugated coefficient. -/
theorem coefficient_map_arrowCongr (e₁ : V ≃L[ℂ] V') (e₂ : W ≃L[ℂ] W') (a : Symbol n V W m) :
    (a.map ((e₁.arrowCongr e₂).toContinuousLinearMap.restrictScalars ℝ)).coefficient =
      fun p ↦ e₁.arrowCongr e₂ (a.coefficient p) :=
  funext fun p ↦ by simp

theorem HasCompactSpatialSupport.map {a : Symbol n V W m} (ha : a.HasCompactSpatialSupport)
    (Φ : (V →L[ℂ] W) →L[ℝ] (V' →L[ℂ] W')) : (a.map Φ).HasCompactSpatialSupport := by
  obtain ⟨K, hK, hKa⟩ := hasCompactSpatialSupport_iff.1 ha
  exact hasCompactSpatialSupport_iff.2
    ⟨K, hK, fun x hx ξ ↦ by rw [coefficient_map, hKa x hx ξ, map_zero]⟩

/-- Spatial derivatives commute with the image under a continuous linear map. -/
@[simp]
theorem spatialDeriv_map (Φ : (V →L[ℂ] W) →L[ℝ] (V' →L[ℂ] W')) (a : Symbol n V W m) (j : Fin n) :
    spatialDeriv j (a.map Φ) = (spatialDeriv j a).map Φ :=
  Symbol.ext (funext fun ⟨x, ξ⟩ ↦ by
    rw [coefficient_spatialDeriv, coefficient_map, coefficient_spatialDeriv]
    exact Φ.coordinateDeriv_comp_left [j] ((a.contDiff_coefficient_slice ξ).of_le (by simp)) x)

/-- Frequency derivatives commute with the image under a continuous linear map. -/
@[simp]
theorem frequencyDeriv_map (Φ : (V →L[ℂ] W) →L[ℝ] (V' →L[ℂ] W')) (a : Symbol n V W m)
    (j : Fin n) : frequencyDeriv j (a.map Φ) = (frequencyDeriv j a).map Φ :=
  Symbol.ext (funext fun ⟨x, ξ⟩ ↦ by
    rw [coefficient_frequencyDeriv, coefficient_map, coefficient_frequencyDeriv]
    exact Φ.coordinateDeriv_comp_left [j]
      ((a.contDiff_coefficient.comp (contDiff_const.prodMk contDiff_id)).of_le (by simp)) ξ)

/-- A symbol commutes with `T` at every point exactly when its images under right and left
composition with `T` agree. -/
private theorem map_compL_flip_eq_map_compL {a : Symbol n V V m} {T : V →L[ℂ] V}
    (h : ∀ p, Commute (a.coefficient p) T) :
    a.map (((ContinuousLinearMap.compL ℂ V V V).flip T).restrictScalars ℝ) =
      a.map ((ContinuousLinearMap.compL ℂ V V V T).restrictScalars ℝ) :=
  Symbol.ext (funext fun p ↦ by simpa [← ContinuousLinearMap.mul_def] using (h p).eq)

private theorem commute_of_coefficient_map_compL_flip_eq {a : Symbol n V V m} {T : V →L[ℂ] V}
    {p : CoordinateSpace n × CoordinateSpace n}
    (h : (a.map (((ContinuousLinearMap.compL ℂ V V V).flip T).restrictScalars ℝ)).coefficient p =
      (a.map ((ContinuousLinearMap.compL ℂ V V V T).restrictScalars ℝ)).coefficient p) :
    Commute (a.coefficient p) T := by simpa [commute_iff_eq, ContinuousLinearMap.mul_def] using h

/-- If every value of a symbol commutes with an operator `T`, so does every value of its spatial
derivatives. -/
theorem commute_coefficient_spatialDeriv {a : Symbol n V V m} {T : V →L[ℂ] V}
    (h : ∀ p, Commute (a.coefficient p) T) (j : Fin n) (p : CoordinateSpace n × CoordinateSpace n) :
    Commute ((spatialDeriv j a).coefficient p) T :=
  commute_of_coefficient_map_compL_flip_eq (by
    rw [← spatialDeriv_map, ← spatialDeriv_map, map_compL_flip_eq_map_compL h])

/-- If every value of a symbol commutes with an operator `T`, so does every value of its frequency
derivatives. -/
theorem commute_coefficient_frequencyDeriv {a : Symbol n V V m} {T : V →L[ℂ] V}
    (h : ∀ p, Commute (a.coefficient p) T) (j : Fin n) (p : CoordinateSpace n × CoordinateSpace n) :
    Commute ((frequencyDeriv j a).coefficient p) T :=
  commute_of_coefficient_map_compL_flip_eq (by
    rw [← frequencyDeriv_map, ← frequencyDeriv_map, map_compL_flip_eq_map_compL h])

/-- The image of a symbol with estimates uniform in the position under a continuous linear map of
the coefficient spaces again has estimates uniform in the position. -/
theorem IsUniform.map {a : Symbol n V W m} (ha : a.IsUniform)
    (Φ : (V →L[ℂ] W) →L[ℝ] (V' →L[ℂ] W')) : (a.map Φ).IsUniform := by
  refine isUniform_iff.2 fun α β ↦ ?_
  obtain ⟨C, hC0, hC⟩ := isUniform_iff.1 ha α β
  refine ⟨‖Φ‖ * C, by positivity, fun x ξ ↦ ?_⟩
  rw [show (a.map Φ).coefficient = Φ ∘ a.coefficient from funext (coefficient_map Φ a),
    Φ.mixedDeriv_comp_left a.contDiff_coefficient, mul_assoc]
  exact Φ.le_opNorm_of_le (hC x ξ)

end Map

end Symbol

end TauCeti
