/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.DivergenceTheorem
public import TauCeti.Analysis.BoxIntegral.Integrability

/-!
# Boundary flux on boxes

`boxBoundarySum` is the front-minus-back face sum in Mathlib's Bochner divergence theorem.
The face parametrizations insert the omitted coordinate, in increasing coordinate order.
The codomain may be any real normed space, so quaternion-valued fluxes need no separate
integration theory.

This file provides the algebraic and geometric calculus of `boxBoundarySum`:
* vanishing on constant fields and on degenerate boxes with `a k = b k`;
* scalar multiplication, negation, additivity and face-volume norm bounds;
* rectangular subdivision additivity (`boxBoundarySum_split`,
  `boxBoundarySum_split_of_continuousOn`) when a box is split along `x k = t`, with cancellation of
  the paired internal facets;
* compatibility (`boxBoundarySum_eq_boxIntegral`) with `BoxIntegral.integral` on `Box.face`;
* `boxBoundarySum_eq_zero_of_hasFDerivAt`, giving vanishing boundary flux for a continuous field
  with pointwise derivatives and zero divergence in the open box, without continuity of the
  derivatives and including degenerate boxes.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace TauCeti

section IccSplit

/-- Splitting a closed box `Set.Icc a b` along the coordinate `k` at `t ∈ Set.Icc (a k) (b k)`
decomposes it as the union of its lower and upper sub-boxes. -/
theorem Icc_update_union_Icc_update {ι α : Type*} [DecidableEq ι] [LinearOrder α]
    (a b : ι → α) (k : ι) {t : α} (ht : t ∈ Icc (a k) (b k)) :
    Icc a (Function.update b k t) ∪ Icc (Function.update a k t) b = Icc a b := by
  ext x
  simp only [mem_union, mem_Icc]
  constructor
  · rintro (⟨h₁, h₂⟩ | ⟨h₁, h₂⟩)
    · refine ⟨h₁, fun i ↦ (h₂ i).trans ?_⟩
      by_cases hik : i = k
      · subst hik
        simpa using ht.2
      · simp [hik]
    · refine ⟨fun i ↦ ?_, h₂⟩
      by_cases hik : i = k
      · subst hik
        exact ht.1.trans (by simpa using h₁ i)
      · exact (by simp [hik] : a i ≤ Function.update a k t i).trans (h₁ i)
  · rintro ⟨h₁, h₂⟩
    rcases le_total (x k) t with hxt | htx
    · left
      refine ⟨h₁, fun i ↦ ?_⟩
      by_cases hik : i = k
      · subst hik
        simpa using hxt
      · simpa [hik] using h₂ i
    · right
      refine ⟨fun i ↦ ?_, h₂⟩
      by_cases hik : i = k
      · subst hik
        simpa using htx
      · simpa [hik] using h₁ i

/-- The two sub-boxes obtained by splitting `Set.Icc a b` along coordinate `k` at `t` meet in the
hyperplane slice `x k = t` of Lebesgue measure zero, hence are almost-everywhere disjoint. -/
theorem aeDisjoint_Icc_update {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a b : ι → ℝ) (k : ι) (t : ℝ) :
    AEDisjoint volume (Icc a (Function.update b k t)) (Icc (Function.update a k t) b) := by
  have hsub : Icc a (Function.update b k t) ∩ Icc (Function.update a k t) b ⊆
      Icc (Function.update a k t) (Function.update b k t) := by
    rintro x ⟨⟨_, hx₁⟩, ⟨hx₂, _⟩⟩
    exact ⟨hx₂, hx₁⟩
  have hzero : volume (Icc (Function.update a k t) (Function.update b k t)) = 0 := by
    rw [Real.volume_Icc_pi]
    exact Finset.prod_eq_zero (Finset.mem_univ k) (by simp)
  exact measure_mono_null hsub hzero

/-- Splitting a closed box `Set.Icc a b` in `ι → ℝ` along coordinate `k` at
`t ∈ Set.Icc (a k) (b k)` splits the Bochner set integral of any integrable function. -/
theorem setIntegral_Icc_split {ι E : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup E] [NormedSpace ℝ E] {a b : ι → ℝ} (k : ι) {t : ℝ}
    (ht : t ∈ Icc (a k) (b k)) {f : (ι → ℝ) → E} (hf : IntegrableOn f (Icc a b)) :
    (∫ x in Icc a (Function.update b k t), f x) + ∫ x in Icc (Function.update a k t) b, f x =
      ∫ x in Icc a b, f x := by
  have hunion := Icc_update_union_Icc_update a b k ht
  have hf₁ : IntegrableOn f (Icc a (Function.update b k t)) :=
    hf.mono_set (hunion ▸ subset_union_left)
  have hf₂ : IntegrableOn f (Icc (Function.update a k t) b) :=
    hf.mono_set (hunion ▸ subset_union_right)
  rw [← setIntegral_union₀ (aeDisjoint_Icc_update a b k t)
    measurableSet_Icc.nullMeasurableSet hf₁ hf₂, hunion]

end IccSplit

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

@[simp]
theorem boxBoundarySum_zero (a b : Fin (n + 1) → ℝ) :
    boxBoundarySum a b (fun _ _ ↦ (0 : E)) = 0 := by
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

omit [NormedSpace ℝ E] in
/-- Continuity of `f` on the closed box `Set.Icc a b` gives integrability on every slice `x i = c`
for `c ∈ Set.Icc (a i) (b i)`. -/
theorem integrableOn_boxFace {a b : Fin (n + 1) → ℝ} {f : (Fin (n + 1) → ℝ) → E}
    (hf : ContinuousOn f (Icc a b)) (i : Fin (n + 1)) {c : ℝ} (hc : c ∈ Icc (a i) (b i)) :
    IntegrableOn (fun x ↦ f (i.insertNth c x)) (Icc (a ∘ i.succAbove) (b ∘ i.succAbove)) := by
  refine ContinuousOn.integrableOn_compact isCompact_Icc ?_
  exact hf.comp (continuousOn_const.finInsertNth i continuousOn_id) fun x hx ↦
    Fin.insertNth_mem_Icc.mpr ⟨hc, hx⟩

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
    (fun i ↦ integrableOn_boxFace (hF i) i (right_mem_Icc.mpr (hab i)))
    (fun i ↦ integrableOn_boxFace (hF i) i (left_mem_Icc.mpr (hab i)))
    (fun i ↦ integrableOn_boxFace (hG i) i (right_mem_Icc.mpr (hab i)))
    (fun i ↦ integrableOn_boxFace (hG i) i (left_mem_Icc.mpr (hab i)))

/-- Norm bound on `boxBoundarySum` from uniform bounds `M i` on the components `F i` over the
closed box: each pair of opposite `i`-faces contributes at most `2 * M i` times the `n`-dimensional
face volume. No integrability hypothesis is needed. -/
theorem norm_boxBoundarySum_le {a b : Fin (n + 1) → ℝ} (hab : a ≤ b)
    {F : Fin (n + 1) → (Fin (n + 1) → ℝ) → E} {M : Fin (n + 1) → ℝ}
    (hF : ∀ i, ∀ x ∈ Icc a b, ‖F i x‖ ≤ M i) :
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
    norm_setIntegral_le_of_norm_le_const hfin fun x hx ↦
      hF i _ (Fin.insertNth_mem_Icc.mpr ⟨right_mem_Icc.mpr (hab i), hx⟩)
  have hlower : ‖∫ x in Icc (a ∘ i.succAbove) (b ∘ i.succAbove), F i (i.insertNth (a i) x)‖ ≤
      M i * volume.real (Icc (a ∘ i.succAbove) (b ∘ i.succAbove)) :=
    norm_setIntegral_le_of_norm_le_const hfin fun x hx ↦
      hF i _ (Fin.insertNth_mem_Icc.mpr ⟨left_mem_Icc.mpr (hab i), hx⟩)
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
theorem boxBoundarySum_split {a b : Fin (n + 1) → ℝ} (k : Fin (n + 1)) {t : ℝ}
    (ht : t ∈ Icc (a k) (b k)) {F : Fin (n + 1) → (Fin (n + 1) → ℝ) → E}
    (hFb : ∀ i, i ≠ k → IntegrableOn (fun x ↦ F i (i.insertNth (b i) x))
      (Icc (a ∘ i.succAbove) (b ∘ i.succAbove)))
    (hFa : ∀ i, i ≠ k → IntegrableOn (fun x ↦ F i (i.insertNth (a i) x))
      (Icc (a ∘ i.succAbove) (b ∘ i.succAbove))) :
    boxBoundarySum a (Function.update b k t) F + boxBoundarySum (Function.update a k t) b F =
      boxBoundarySum a b F := by
  simp only [boxBoundarySum_def, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  by_cases hik : i = k
  · subst hik
    have hcomp (c : Fin (n + 1) → ℝ) : Function.update c i t ∘ i.succAbove = c ∘ i.succAbove := by
      ext r
      exact Function.update_of_ne (i.succAbove_ne r) t c
    simp only [hcomp, Function.update_self]
    abel
  · obtain ⟨r, hr⟩ := Fin.exists_succAbove_eq (Ne.symm hik)
    have hcomp (c : Fin (n + 1) → ℝ) :
        Function.update c k t ∘ i.succAbove = Function.update (c ∘ i.succAbove) r t := by
      ext s
      simp only [Function.comp_apply]
      by_cases hsr : s = r
      · subst hsr
        rw [hr, Function.update_self, Function.update_self]
      · have hsk : i.succAbove s ≠ k := hr ▸ i.succAbove_right_injective.ne hsr
        rw [Function.update_of_ne hsk, Function.update_of_ne hsr, Function.comp_apply]
    have htr : t ∈ Icc ((a ∘ i.succAbove) r) ((b ∘ i.succAbove) r) := by
      simpa only [Function.comp_apply, hr] using ht
    simp only [Function.update_of_ne hik, hcomp]
    rw [sub_add_sub_comm,
      setIntegral_Icc_split r htr (f := fun x ↦ F i (i.insertNth (b i) x)) (hFb i hik),
      setIntegral_Icc_split r htr (f := fun x ↦ F i (i.insertNth (a i) x)) (hFa i hik)]

/-- Rectangular subdivision additivity of `boxBoundarySum` for fields continuous on
`Set.Icc a b`. -/
theorem boxBoundarySum_split_of_continuousOn {a b : Fin (n + 1) → ℝ} (hab : a ≤ b)
    (k : Fin (n + 1)) {t : ℝ} (ht : t ∈ Icc (a k) (b k))
    {F : Fin (n + 1) → (Fin (n + 1) → ℝ) → E} (hF : ∀ i, ContinuousOn (F i) (Icc a b)) :
    boxBoundarySum a (Function.update b k t) F + boxBoundarySum (Function.update a k t) b F =
      boxBoundarySum a b F :=
  boxBoundarySum_split k ht
    (fun i _ ↦ integrableOn_boxFace (hF i) i (right_mem_Icc.mpr (hab i)))
    (fun i _ ↦ integrableOn_boxFace (hF i) i (left_mem_Icc.mpr (hab i)))

/-- For a Banach-valued field family continuous on a nondegenerate closed box `Box.Icc I`, each
Bochner face integral in `boxBoundarySum` equals the native `BoxIntegral.integral` over `I.face i`
for any `BoxIntegral.IntegrationParams`. -/
theorem boxBoundarySum_eq_boxIntegral [CompleteSpace E] (I : BoxIntegral.Box (Fin (n + 1)))
    (l : BoxIntegral.IntegrationParams) {F : Fin (n + 1) → (Fin (n + 1) → ℝ) → E}
    (hF : ∀ i, ContinuousOn (F i) (Icc I.lower I.upper)) :
    boxBoundarySum I.lower I.upper F =
      ∑ i, (BoxIntegral.integral (I.face i) l (fun x ↦ F i (i.insertNth (I.upper i) x))
          BoxIntegral.BoxAdditiveMap.volume -
        BoxIntegral.integral (I.face i) l (fun x ↦ F i (i.insertNth (I.lower i) x))
          BoxIntegral.BoxAdditiveMap.volume) := by
  rw [boxBoundarySum_def]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [I.integral_face_eq_setIntegral_Icc (hF i) i (right_mem_Icc.mpr (I.lower_le_upper i)) l,
    I.integral_face_eq_setIntegral_Icc (hF i) i (left_mem_Icc.mpr (I.lower_le_upper i)) l]

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
