/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Linearization.Basic
import TauCeti.Topology.UniformSpace.HeineCantor

/-!
# The zeroth-order coefficient of the linearized operator for a cylindrical datum

For the cylindrical Floer datum `K = H_t dt` with almost complex structures `J_t(y)` independent
of `s`, the zeroth-order part of the linearized Floer operator along a map `w` at `z = (s, t)`
(`TauCeti.SymplecticForm.floerLinearizationCoeff`) is

`C(t, y, η) = (dJ_t(y) ·) (η - X_{H_t}(y)) - J_t(y) dX_{H_t}(y)`,

evaluated at the value `y = w z` and the slice velocity `η = ∂t w z`
(`TauCeti.SymplecticForm.floerLinearizationCoeff_eq_cylindricalLinearizationCoeff`). This file
names `C` (`TauCeti.SymplecticForm.cylindricalLinearizationCoeff`) and proves that it is uniformly
continuous at the jets of an orbit: over a compact set of times, `J_t(y)` and `C(t, y, η)` are
uniformly close to their values at the jet `(x t, X_{H_t}(x t))` of a continuous loop `x`, at every
jet `(y, η)` close enough to it
(`exists_pos_forall_norm_sub_lt_and_norm_cylindricalLinearizationCoeff_sub_lt`).
At such a jet the term with `dJ` vanishes
(`TauCeti.SymplecticForm.cylindricalLinearizationCoeff_hamiltonianVectorField`), so near an orbit
the linearized operator along any map is close to the one along the stationary cylinder. This is
how linearized operators along pre-glued maps and along the ends of Floer cylinders are compared
with the translation-invariant operators at the asymptotic orbits.
-/

public section

open Set Function ContinuousLinearMap

namespace TauCeti.SymplecticForm

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {J : ℝ → V → V →L[ℝ] V} {H : ℝ → V → ℝ} {x : ℝ → V}

/-- The zeroth-order coefficient of the linearized Floer operator for the cylindrical datum
`K = H_t dt`, as a function of the time `t`, the value `y` and the slice velocity `η`:
`(dJ_t(y) ·) (η - X_{H_t}(y)) - J_t(y) dX_{H_t}(y)`. -/
noncomputable def cylindricalLinearizationCoeff (ω : SymplecticForm V) (J : ℝ → V → V →L[ℝ] V)
    (H : ℝ → V → ℝ) (t : ℝ) (y η : V) : V →L[ℝ] V :=
  (fderiv ℝ (J t) y).flip (η - ω.hamiltonianVectorField (H t) y) -
    (J t y).comp (fderiv ℝ (ω.hamiltonianVectorField (H t)) y)

/-- The definition of the zeroth-order coefficient for a cylindrical datum. -/
theorem cylindricalLinearizationCoeff_def (ω : SymplecticForm V) (J : ℝ → V → V →L[ℝ] V)
    (H : ℝ → V → ℝ) (t : ℝ) (y η : V) :
    ω.cylindricalLinearizationCoeff J H t y η =
      (fderiv ℝ (J t) y).flip (η - ω.hamiltonianVectorField (H t) y) -
        (J t y).comp (fderiv ℝ (ω.hamiltonianVectorField (H t)) y) :=
  (rfl)

/-- At a slice velocity equal to the Hamiltonian vector field, as along an orbit, the term with
the derivative of `J` vanishes and the coefficient is `-J_t(y) dX_{H_t}(y)`. -/
@[simp]
theorem cylindricalLinearizationCoeff_hamiltonianVectorField (ω : SymplecticForm V)
    (J : ℝ → V → V →L[ℝ] V) (H : ℝ → V → ℝ) (t : ℝ) (y : V) :
    ω.cylindricalLinearizationCoeff J H t y (ω.hamiltonianVectorField (H t) y) =
      -(J t y).comp (fderiv ℝ (ω.hamiltonianVectorField (H t)) y) := by
  simp [cylindricalLinearizationCoeff_def]

/-- The zeroth-order coefficient of the linearized operator along `w` at `z`, for the datum
`K = H_t dt`, depends only on the time `z.2`, the value `w z` and the slice velocity `∂t w z`. -/
theorem floerLinearizationCoeff_eq_cylindricalLinearizationCoeff (ω : SymplecticForm V)
    (J : ℝ → V → V →L[ℝ] V) (H : ℝ → V → ℝ) (w : ℝ × ℝ → V) (z : ℝ × ℝ) :
    ω.floerLinearizationCoeff (fun p ↦ J p.2) (fun _ _ ↦ 0) (fun p ↦ H p.2) w z =
      ω.cylindricalLinearizationCoeff J H z.2 (w z) (fderiv ℝ w z stdComplexLineImag) := by
  ext y
  simp [floerLinearizationCoeff_apply, cylindricalLinearizationCoeff_def]

/-- **The coefficients near an orbit.** For a continuous loop `x` and a compact set `T` of times,
the coefficients `J_t(y)` and `C(t, y, η)` of the linearized operator are uniformly close to their
values at the jet `(x t, X_{H_t}(x t))` of `x`, at every jet `(y, η)` close enough to it. -/
theorem exists_pos_forall_norm_sub_lt_and_norm_cylindricalLinearizationCoeff_sub_lt
    (ω : SymplecticForm V) (hJ : ContDiff ℝ 1 (uncurry J)) (hH : ContDiff ℝ 2 (uncurry H))
    {T : Set ℝ} (hT : IsCompact T) (hx : ContinuousOn x T) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ t ∈ T, ∀ y η, ‖y - x t‖ < δ → ‖η - ω.hamiltonianVectorField (H t) (x t)‖ < δ →
      ‖J t y - J t (x t)‖ < ε ∧
        ‖ω.cylindricalLinearizationCoeff J H t y η -
          ω.cylindricalLinearizationCoeff J H t (x t) (ω.hamiltonianVectorField (H t) (x t))‖ <
            ε := by
  -- The coefficient fields `X_H`, `dJ` and `J dX_H` are continuous in `(t, y)`.
  have hX := ω.contDiff_hamiltonianVectorField_uncurry (n := 1) hH
  have hdJ := (ContDiff.fderiv (f := fun (p : ℝ × V) (y : V) ↦ J p.1 y) (g := Prod.snd) (n := 0)
    (hJ.comp (contDiff_fst.fst.prodMk contDiff_snd)) contDiff_snd (by norm_num)).continuous
  have hJS := hJ.continuous.clm_comp (ContDiff.fderiv (f := fun (p : ℝ × V) (y : V) ↦
    ω.hamiltonianVectorField (H p.1) y) (g := Prod.snd) (n := 0)
    (hX.comp (contDiff_fst.fst.prodMk contDiff_snd)) contDiff_snd (by norm_num)).continuous
  -- `dJ` is bounded along the orbit, by `M`, and hence by `M' = |M| + 1` near it.
  obtain ⟨M, hM⟩ := (hT.image_of_continuousOn
    ((continuousOn_id' _).prodMk hx)).exists_bound_of_continuousOn hdJ.continuousOn
  set M' := |M| + 1
  have hM'0 : 0 < M' := by positivity
  set ε' := ε / (4 * M')
  obtain ⟨δ₁, hδ₁, h₁⟩ := hT.exists_pos_forall_dist_lt hx (fun _ _ ↦ hJ.continuous.continuousAt) hε
  obtain ⟨δ₂, hδ₂, h₂⟩ := hT.exists_pos_forall_dist_lt hx (fun _ _ ↦ hJS.continuousAt)
    (half_pos hε)
  obtain ⟨δ₃, hδ₃, h₃⟩ := hT.exists_pos_forall_dist_lt hx (fun _ _ ↦ hX.continuous.continuousAt)
    (by positivity : 0 < ε')
  obtain ⟨δ₄, hδ₄, h₄⟩ := hT.exists_pos_forall_dist_lt hx (fun _ _ ↦ hdJ.continuousAt) one_pos
  simp only [dist_eq_norm] at h₁ h₂ h₃ h₄
  refine ⟨min (min δ₁ δ₂) (min (min δ₃ δ₄) ε'), by positivity, fun t ht y η hy hη ↦ ?_⟩
  simp only [lt_min_iff] at hy hη
  obtain ⟨e₂, e₃, e₄, hMt⟩ := And.intro (h₂ t ht y hy.1.2) <| And.intro (h₃ t ht y hy.2.1.1) <|
    And.intro (h₄ t ht y hy.2.1.2) (hM _ (mem_image_of_mem _ ht))
  simp only [uncurry_apply_pair] at e₂ e₃ e₄ hMt
  refine ⟨h₁ t ht y hy.1.1, ?_⟩
  -- The term `dJ(y) (η - X(y))` is at most `M' ‖η - X(y)‖ ≤ ε / 2`, and the term `J(y) dX(y)` is
  -- within `ε / 2` of its value along `x`.
  have hdJy : ‖fderiv ℝ (J t) y‖ ≤ M' := by
    linarith [norm_le_insert' (fderiv ℝ (J t) y) (fderiv ℝ (J t) (x t)), le_abs_self M]
  have hd : ‖η - ω.hamiltonianVectorField (H t) y‖ ≤ 2 * ε' := by
    linarith [norm_sub_le_norm_sub_add_norm_sub η (ω.hamiltonianVectorField (H t) (x t))
      (ω.hamiltonianVectorField (H t) y), norm_sub_rev (ω.hamiltonianVectorField (H t) (x t))
      (ω.hamiltonianVectorField (H t) y)]
  have hF : ‖(fderiv ℝ (J t) y).flip (η - ω.hamiltonianVectorField (H t) y)‖ ≤ ε / 2 := by
    calc _ ≤ ‖(fderiv ℝ (J t) y).flip‖ * ‖η - ω.hamiltonianVectorField (H t) y‖ := le_opNorm _ _
      _ ≤ M' * (2 * ε') := by
          rw [opNorm_flip]
          exact mul_le_mul hdJy hd (norm_nonneg _) hM'0.le
      _ = ε / 2 := by simp only [ε']; field_simp; ring
  have hc : ω.cylindricalLinearizationCoeff J H t y η -
      ω.cylindricalLinearizationCoeff J H t (x t) (ω.hamiltonianVectorField (H t) (x t)) =
        (fderiv ℝ (J t) y).flip (η - ω.hamiltonianVectorField (H t) y) -
          ((J t y).comp (fderiv ℝ (ω.hamiltonianVectorField (H t)) y) -
            (J t (x t)).comp (fderiv ℝ (ω.hamiltonianVectorField (H t)) (x t))) := by
    simp only [cylindricalLinearizationCoeff_def, sub_self, map_zero]
    abel
  rw [hc]
  exact (norm_sub_le _ _).trans_lt (by linarith)

end TauCeti.SymplecticForm
