/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.DivergenceTheorem
public import TauCeti.Analysis.BoxIntegral.Integrability
import TauCeti.MeasureTheory.Integral.Bochner.Affine
import TauCeti.MeasureTheory.Integral.Bochner.Basic
import TauCeti.MeasureTheory.Integral.Bochner.Set

/-!
# Boundary flux on boxes

`boxBoundarySum` is the front-minus-back face sum in Mathlib's Bochner divergence theorem.
The face parametrizations insert the omitted coordinate, in increasing coordinate order.
The codomain may be any real normed space, so quaternion-valued fluxes need no separate
integration theory.

This file provides the algebraic and geometric calculus of `boxBoundarySum`:
* vanishing on constant fields and on degenerate boxes with `a k = b k`;
* scalar multiplication, negation, additivity, rescaling to the unit cube
  (`boxBoundarySum_eq_boxBoundarySum_zero_one`) and face-volume norm bounds;
* rectangular subdivision additivity (`boxBoundarySum_update_add_boxBoundarySum_update`,
  `boxBoundarySum_update_add_boxBoundarySum_update_of_continuousOn`) when a box is split along
  `x k = t`, with cancellation of the paired internal facets;
* compatibility (`boxBoundarySum_eq_boxIntegral`) with `BoxIntegral.integral` on `Box.face`;
* `boxBoundarySum_eq_zero_of_hasFDerivAt`, giving vanishing boundary flux for a continuous field
  with pointwise derivatives and zero divergence in the open box, without continuity of the
  derivatives and including degenerate boxes.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace TauCeti

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The oriented boundary flux of a family of fields on a box: the integral on each front
face minus the integral on the corresponding back face. -/
noncomputable def boxBoundarySum (a b : Fin (n + 1) → ℝ)
    (F : Fin (n + 1) → (Fin (n + 1) → ℝ) → E) : E :=
  ∑ i, ((∫ x in Icc (a ∘ i.succAbove) (b ∘ i.succAbove), F i (i.insertNth (b i) x)) -
    ∫ x in Icc (a ∘ i.succAbove) (b ∘ i.succAbove), F i (i.insertNth (a i) x))

/-- The defining front-minus-back expansion of the boundary flux. -/
theorem boxBoundarySum_def (a b : Fin (n + 1) → ℝ)
    (F : Fin (n + 1) → (Fin (n + 1) → ℝ) → E) :
    boxBoundarySum a b F =
      ∑ i, ((∫ x in Icc (a ∘ i.succAbove) (b ∘ i.succAbove), F i (i.insertNth (b i) x)) -
        ∫ x in Icc (a ∘ i.succAbove) (b ∘ i.succAbove), F i (i.insertNth (a i) x)) := (rfl)

/-- On the unit cube, the boundary flux is the sum of front-minus-back integrals over
unit cubes of one lower dimension. -/
theorem boxBoundarySum_zero_one (F : Fin (n + 1) → (Fin (n + 1) → ℝ) → E) :
    boxBoundarySum 0 1 F =
      ∑ i, ((∫ x in Icc (0 : Fin n → ℝ) 1, F i (i.insertNth 1 x)) -
        ∫ x in Icc (0 : Fin n → ℝ) 1, F i (i.insertNth 0 x)) := by
  simp only [boxBoundarySum_def, Function.comp_def, Pi.zero_def, Pi.one_def]

/-- The boundary flux of the zero field family vanishes. For the pointwise lambda form
`fun _ _ ↦ 0`, see `boxBoundarySum_const`. -/
@[simp]
theorem boxBoundarySum_zero (a b : Fin (n + 1) → ℝ) :
    boxBoundarySum a b (0 : Fin (n + 1) → (Fin (n + 1) → ℝ) → E) = 0 := by
  simp [boxBoundarySum_def]

/-- Constant flux components cancel between opposite faces, without ordering or regularity
hypotheses on the box. -/
@[simp]
theorem boxBoundarySum_const (a b : Fin (n + 1) → ℝ) (c : Fin (n + 1) → E) :
    boxBoundarySum a b (fun i _ ↦ c i) = 0 := by
  simp [boxBoundarySum_def]

/-- If a box has zero width along some coordinate `k`, its boundary flux vanishes for every field
family: the `k`-faces coincide, while every other face has Lebesgue measure zero. -/
theorem boxBoundarySum_eq_zero_of_eq {a b : Fin (n + 1) → ℝ} {k : Fin (n + 1)} (hk : a k = b k)
    (F : Fin (n + 1) → (Fin (n + 1) → ℝ) → E) :
    boxBoundarySum a b F = 0 := by
  rw [boxBoundarySum_def]
  refine Finset.sum_eq_zero fun i _ ↦ ?_
  by_cases hik : i = k
  · subst hik
    rw [hk, sub_self]
  · obtain ⟨r, hr⟩ := Fin.exists_succAbove_eq (Ne.symm hik)
    have hvol : volume (Icc (a ∘ i.succAbove) (b ∘ i.succAbove)) = 0 := by
      rw [Real.volume_Icc_pi]
      exact Finset.prod_eq_zero (Finset.mem_univ r) (by simp [Function.comp_apply, hr, hk])
    rw [setIntegral_measure_zero _ hvol, setIntegral_measure_zero _ hvol, sub_self]

@[simp]
theorem boxBoundarySum_self (a : Fin (n + 1) → ℝ)
    (F : Fin (n + 1) → (Fin (n + 1) → ℝ) → E) :
    boxBoundarySum a a F = 0 :=
  boxBoundarySum_eq_zero_of_eq (k := 0) rfl F

/-- Rescaling a closed rectangular box `Set.Icc a b` (`a ≤ b`) to the unit cube `[0, 1]ⁿ⁺¹`
rewrites `boxBoundarySum a b F` as a unit-cube `boxBoundarySum`, with each `j`-face scaled by its
`n`-dimensional face volume `∏ r, (b (j.succAbove r) - a (j.succAbove r))`, including on
degenerate boxes and without continuity, measurability or completeness hypotheses. -/
theorem boxBoundarySum_eq_boxBoundarySum_zero_one {a b : Fin (n + 1) → ℝ} (hab : a ≤ b)
    (F : Fin (n + 1) → (Fin (n + 1) → ℝ) → E) :
    boxBoundarySum a b F =
      boxBoundarySum 0 1 fun j u ↦
        (∏ r : Fin n, (b (j.succAbove r) - a (j.succAbove r))) •
          F j (fun i ↦ a i + (b i - a i) * u i) := by
  rw [boxBoundarySum_def, boxBoundarySum_zero_one]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  have hface : a ∘ j.succAbove ≤ b ∘ j.succAbove := fun r ↦ hab (j.succAbove r)
  have hfront (x : Fin n → ℝ) :
      (fun i ↦ a i + (b i - a i) * j.insertNth (α := fun _ ↦ ℝ) 1 x i) =
        j.insertNth (b j)
          (fun r ↦ a (j.succAbove r) + (b (j.succAbove r) - a (j.succAbove r)) * x r) := by
    ext i
    exact j.succAboveCases (by simp) (fun r ↦ by simp) i
  have hback (x : Fin n → ℝ) :
      (fun i ↦ a i + (b i - a i) * j.insertNth (α := fun _ ↦ ℝ) 0 x i) =
        j.insertNth (a j)
          (fun r ↦ a (j.succAbove r) + (b (j.succAbove r) - a (j.succAbove r)) * x r) := by
    ext i
    exact j.succAboveCases (by simp) (fun r ↦ by simp) i
  simp_rw [integral_smul, hfront, hback]
  rw [setIntegral_Icc_eq_smul_setIntegral_Icc_zero_one hface (fun y ↦ F j (j.insertNth (b j) y)),
    setIntegral_Icc_eq_smul_setIntegral_Icc_zero_one hface (fun y ↦ F j (j.insertNth (a j) y))]
  simp only [Function.comp_apply]

/-- Real scalars commute with `boxBoundarySum`, without integrability hypotheses. -/
theorem boxBoundarySum_smul (a b : Fin (n + 1) → ℝ) (r : ℝ)
    (F : Fin (n + 1) → (Fin (n + 1) → ℝ) → E) :
    boxBoundarySum a b (fun i x ↦ r • F i x) = r • boxBoundarySum a b F := by
  simp [boxBoundarySum_def, integral_smul, smul_sub, Finset.smul_sum]

/-- Negating every component of a field negates `boxBoundarySum`. -/
theorem boxBoundarySum_neg (a b : Fin (n + 1) → ℝ)
    (F : Fin (n + 1) → (Fin (n + 1) → ℝ) → E) :
    boxBoundarySum a b (fun i x ↦ -F i x) = -boxBoundarySum a b F := by
  simpa using boxBoundarySum_smul a b (-1 : ℝ) F

/-- `boxBoundarySum` is additive when both field families are integrable on every face. -/
theorem boxBoundarySum_add (a b : Fin (n + 1) → ℝ)
    {F G : Fin (n + 1) → (Fin (n + 1) → ℝ) → E}
    (hFb : ∀ i, IntegrableOn (fun x ↦ F i (i.insertNth (b i) x))
      (Icc (a ∘ i.succAbove) (b ∘ i.succAbove)))
    (hFa : ∀ i, IntegrableOn (fun x ↦ F i (i.insertNth (a i) x))
      (Icc (a ∘ i.succAbove) (b ∘ i.succAbove)))
    (hGb : ∀ i, IntegrableOn (fun x ↦ G i (i.insertNth (b i) x))
      (Icc (a ∘ i.succAbove) (b ∘ i.succAbove)))
    (hGa : ∀ i, IntegrableOn (fun x ↦ G i (i.insertNth (a i) x))
      (Icc (a ∘ i.succAbove) (b ∘ i.succAbove))) :
    boxBoundarySum a b (fun i x ↦ F i x + G i x) =
      boxBoundarySum a b F + boxBoundarySum a b G := by
  simp only [boxBoundarySum_def]
  simp_rw [integral_add (hFb _) (hGb _), integral_add (hFa _) (hGa _),
    add_sub_add_comm, Finset.sum_add_distrib]

/-- `boxBoundarySum` is additive for field families continuous on the closed box `Set.Icc a b`. -/
theorem boxBoundarySum_add_of_continuousOn {a b : Fin (n + 1) → ℝ} (hab : a ≤ b)
    {F G : Fin (n + 1) → (Fin (n + 1) → ℝ) → E}
    (hF : ∀ i, ContinuousOn (F i) (Icc a b)) (hG : ∀ i, ContinuousOn (G i) (Icc a b)) :
    boxBoundarySum a b (fun i x ↦ F i x + G i x) =
      boxBoundarySum a b F + boxBoundarySum a b G :=
  boxBoundarySum_add a b
    (fun i ↦ (hF i).integrableOn_insertNth_Icc i (right_mem_Icc.mpr (hab i)))
    (fun i ↦ (hF i).integrableOn_insertNth_Icc i (left_mem_Icc.mpr (hab i)))
    (fun i ↦ (hG i).integrableOn_insertNth_Icc i (right_mem_Icc.mpr (hab i)))
    (fun i ↦ (hG i).integrableOn_insertNth_Icc i (left_mem_Icc.mpr (hab i)))

/-- Norm bound on `boxBoundarySum` from uniform bounds `M i` on the components `F i` along each
front and back face: each pair of opposite `i`-faces contributes at most `2 * M i` times the
`n`-dimensional face volume. No integrability hypothesis is needed. -/
theorem norm_boxBoundarySum_le {a b : Fin (n + 1) → ℝ} (hab : a ≤ b)
    {F : Fin (n + 1) → (Fin (n + 1) → ℝ) → E} {M : Fin (n + 1) → ℝ}
    (hFb : ∀ i, ∀ x ∈ Icc (a ∘ i.succAbove) (b ∘ i.succAbove), ‖F i (i.insertNth (b i) x)‖ ≤ M i)
    (hFa : ∀ i, ∀ x ∈ Icc (a ∘ i.succAbove) (b ∘ i.succAbove), ‖F i (i.insertNth (a i) x)‖ ≤ M i) :
    ‖boxBoundarySum a b F‖ ≤
      ∑ i, 2 * M i * ∏ r : Fin n, (b (i.succAbove r) - a (i.succAbove r)) := by
  rw [boxBoundarySum_def]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ ↦ ?_)
  have hface : a ∘ i.succAbove ≤ b ∘ i.succAbove := fun r ↦ hab (i.succAbove r)
  have hvol : volume.real (Icc (a ∘ i.succAbove) (b ∘ i.succAbove)) =
      ∏ r : Fin n, (b (i.succAbove r) - a (i.succAbove r)) := by
    simp only [measureReal_def, Real.volume_Icc_pi_toReal hface, Function.comp_apply]
  have hfin : volume (Icc (a ∘ i.succAbove) (b ∘ i.succAbove)) < ∞ := isCompact_Icc.measure_lt_top
  have hupper : ‖∫ x in Icc (a ∘ i.succAbove) (b ∘ i.succAbove), F i (i.insertNth (b i) x)‖ ≤
      M i * volume.real (Icc (a ∘ i.succAbove) (b ∘ i.succAbove)) :=
    norm_setIntegral_le_of_norm_le_const hfin (hFb i)
  have hlower : ‖∫ x in Icc (a ∘ i.succAbove) (b ∘ i.succAbove), F i (i.insertNth (a i) x)‖ ≤
      M i * volume.real (Icc (a ∘ i.succAbove) (b ∘ i.succAbove)) :=
    norm_setIntegral_le_of_norm_le_const hfin (hFa i)
  calc
    ‖(∫ x in Icc (a ∘ i.succAbove) (b ∘ i.succAbove), F i (i.insertNth (b i) x)) -
        ∫ x in Icc (a ∘ i.succAbove) (b ∘ i.succAbove), F i (i.insertNth (a i) x)‖
      ≤ M i * volume.real (Icc (a ∘ i.succAbove) (b ∘ i.succAbove)) +
          M i * volume.real (Icc (a ∘ i.succAbove) (b ∘ i.succAbove)) :=
        norm_sub_le_of_le hupper hlower
    _ = 2 * M i * ∏ r : Fin n, (b (i.succAbove r) - a (i.succAbove r)) := by
        rw [hvol]
        ring

/-- Rectangular subdivision additivity of `boxBoundarySum`: splitting `Set.Icc a b` along
coordinate `k` at `t ∈ Set.Icc (a k) (b k)` cancels the paired internal facets at `x k = t` and
splits every transverse face `i ≠ k` into two sub-faces. -/
theorem boxBoundarySum_update_add_boxBoundarySum_update {a b : Fin (n + 1) → ℝ}
    (k : Fin (n + 1)) {t : ℝ} (ht : t ∈ Icc (a k) (b k))
    {F : Fin (n + 1) → (Fin (n + 1) → ℝ) → E}
    (hFb : ∀ i, i ≠ k → IntegrableOn (fun x ↦ F i (i.insertNth (b i) x))
      (Icc (a ∘ i.succAbove) (b ∘ i.succAbove)))
    (hFa : ∀ i, i ≠ k → IntegrableOn (fun x ↦ F i (i.insertNth (a i) x))
      (Icc (a ∘ i.succAbove) (b ∘ i.succAbove))) :
    boxBoundarySum a (Function.update b k t) F + boxBoundarySum (Function.update a k t) b F =
      boxBoundarySum a b F := by
  simp only [boxBoundarySum_def, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have hrem (c : Fin (n + 1) → ℝ) : i.removeNth c = c ∘ i.succAbove :=
    funext (i.removeNth_apply c)
  by_cases hik : i = k
  · subst hik
    have hcomp (c : Fin (n + 1) → ℝ) : Function.update c i t ∘ i.succAbove = c ∘ i.succAbove := by
      simpa only [hrem] using i.removeNth_update t c
    simp only [hcomp, Function.update_self]
    abel
  · obtain ⟨r, hr⟩ := Fin.exists_succAbove_eq (Ne.symm hik)
    have hcomp (c : Fin (n + 1) → ℝ) :
        Function.update c k t ∘ i.succAbove = Function.update (c ∘ i.succAbove) r t := by
      simpa only [hrem, hr] using i.removeNth_update_succAbove r t c
    have htr : t ∈ Icc ((a ∘ i.succAbove) r) ((b ∘ i.succAbove) r) := by
      simpa only [Function.comp_apply, hr] using ht
    simp only [Function.update_of_ne hik, hcomp]
    rw [sub_add_sub_comm,
      setIntegral_Icc_update_add_setIntegral_Icc_update r htr
        (f := fun x ↦ F i (i.insertNth (b i) x)) (hFb i hik),
      setIntegral_Icc_update_add_setIntegral_Icc_update r htr
        (f := fun x ↦ F i (i.insertNth (a i) x)) (hFa i hik)]

/-- Rectangular subdivision additivity of `boxBoundarySum` for fields continuous on
`Set.Icc a b`. -/
theorem boxBoundarySum_update_add_boxBoundarySum_update_of_continuousOn
    {a b : Fin (n + 1) → ℝ} (hab : a ≤ b) (k : Fin (n + 1)) {t : ℝ} (ht : t ∈ Icc (a k) (b k))
    {F : Fin (n + 1) → (Fin (n + 1) → ℝ) → E} (hF : ∀ i, ContinuousOn (F i) (Icc a b)) :
    boxBoundarySum a (Function.update b k t) F + boxBoundarySum (Function.update a k t) b F =
      boxBoundarySum a b F :=
  boxBoundarySum_update_add_boxBoundarySum_update k ht
    (fun i _ ↦ (hF i).integrableOn_insertNth_Icc i (right_mem_Icc.mpr (hab i)))
    (fun i _ ↦ (hF i).integrableOn_insertNth_Icc i (left_mem_Icc.mpr (hab i)))

/-- For a Banach-valued field family whose components `F i` are continuous along each closed front
and back face of a box `I`, each Bochner face integral in `boxBoundarySum` equals the native
`BoxIntegral.integral` over `I.face i` for any `BoxIntegral.IntegrationParams`. -/
theorem boxBoundarySum_eq_boxIntegral [CompleteSpace E] (I : BoxIntegral.Box (Fin (n + 1)))
    (l : BoxIntegral.IntegrationParams) {F : Fin (n + 1) → (Fin (n + 1) → ℝ) → E}
    (hFu : ∀ i, ContinuousOn (fun x ↦ F i (i.insertNth (I.upper i) x))
      (Icc (I.lower ∘ i.succAbove) (I.upper ∘ i.succAbove)))
    (hFl : ∀ i, ContinuousOn (fun x ↦ F i (i.insertNth (I.lower i) x))
      (Icc (I.lower ∘ i.succAbove) (I.upper ∘ i.succAbove))) :
    boxBoundarySum I.lower I.upper F =
      ∑ i, (BoxIntegral.integral (I.face i) l (fun x ↦ F i (i.insertNth (I.upper i) x))
          BoxIntegral.BoxAdditiveMap.volume -
        BoxIntegral.integral (I.face i) l (fun x ↦ F i (i.insertNth (I.lower i) x))
          BoxIntegral.BoxAdditiveMap.volume) := by
  rw [boxBoundarySum_def]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [I.integral_face_eq_setIntegral_Icc (hFu i) l,
    I.integral_face_eq_setIntegral_Icc (hFl i) l]

/-- A continuous field with pointwise derivatives of zero divergence in the open box has
zero boundary flux. Continuity of the derivatives is not assumed. -/
theorem boxBoundarySum_eq_zero_of_hasFDerivAt {a b : Fin (n + 1) → ℝ} (hab : a ≤ b)
    {F : Fin (n + 1) → (Fin (n + 1) → ℝ) → E}
    {D : Fin (n + 1) → (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ) →L[ℝ] E}
    (hc : ∀ i, ContinuousOn (F i) (Icc a b))
    (hd : ∀ x ∈ pi univ (fun i ↦ Ioo (a i) (b i)), ∀ i, HasFDerivAt (F i) (D i x) x)
    (hzero : ∀ x ∈ pi univ (fun i ↦ Ioo (a i) (b i)), ∑ i, D i x (Pi.single i 1) = 0) :
    boxBoundarySum a b F = 0 := by
  have hae : (fun x ↦ ∑ i, D i x (Pi.single i 1)) =ᵐ[volume.restrict (Icc a b)] 0 := by
    rw [volume_pi, ← Measure.restrict_congr_set Measure.univ_pi_Ioo_ae_eq_Icc]
    exact (ae_restrict_mem (isOpen_set_pi finite_univ fun _ _ ↦ isOpen_Ioo).measurableSet).mono
      fun x hx ↦ hzero x hx
  have hi : IntegrableOn (fun x ↦ ∑ i, D i x (Pi.single i 1)) (Icc a b) :=
    (integrable_zero _ E _).congr hae.symm
  have h := integral_divergence_of_hasFDerivAt_off_countable' a b hab F D ∅ countable_empty hc
    (fun x hx ↦ hd x hx.1) hi
  rw [integral_congr_ae hae] at h
  simpa only [Pi.zero_apply, integral_zero, boxBoundarySum_def] using h.symm

end TauCeti
