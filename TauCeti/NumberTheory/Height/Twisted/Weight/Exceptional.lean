/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Height.Twisted.Weight.Global

/-!
# The exceptional subspace of a weighted system of forms

The exceptional subspace is the smallest-dimensional proper subspace maximizing
`(weight U - weight ⊤) / codim U`. Finite support makes the set of possible
ratios finite. Supermodularity then makes this optimizer unique; in fact it is
contained in every maximizing proper subspace. With zero total weight, the
exceptional subspace is zero exactly when every proper subspace has nonpositive
weight. This is the semistability criterion used in twisted-height estimates.

The construction works for spanning, possibly redundant, finite systems of forms
over any field and an arbitrary index type of places. Its value is zero if the
ambient space is zero or the spanning or finite-support conditions fail.

## References

* J.-H. Evertse and R. G. Ferretti, *A further improvement of the Quantitative
  Subspace Theorem*, §15, (15.6) and Lemma 15.2.
-/

public noncomputable section

open Function Module Submodule Set

namespace TauCeti

variable {K V ι Ω : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Fintype ι]

/-- The weight gain per codimension. The value at the whole space is zero. -/
def weightRatio (L : Ω → ι → Module.Dual K V) (c : Ω → ι → ℝ)
    (U : Submodule K V) : ℝ :=
  (weight L c U - weight L c ⊤) / (finrank K V - (finrank K U : ℝ))

/-- The defining quotient for the weight ratio. -/
theorem weightRatio_def (L : Ω → ι → Module.Dual K V) (c : Ω → ι → ℝ)
    (U : Submodule K V) : weightRatio L c U =
      (weight L c U - weight L c ⊤) / (finrank K V - (finrank K U : ℝ)) :=
  (rfl)

/-- The whole space has weight ratio zero by the division-by-zero convention. -/
@[simp]
theorem weightRatio_top (L : Ω → ι → Module.Dual K V) (c : Ω → ι → ℝ) :
    weightRatio L c (⊤ : Submodule K V) = 0 := by
  simp [weightRatio_def]

/-- The zero subspace has weight ratio minus the total weight per ambient dimension. -/
@[simp]
theorem weightRatio_bot (L : Ω → ι → Module.Dual K V) (c : Ω → ι → ℝ) :
    weightRatio L c (⊥ : Submodule K V) = -weight L c ⊤ / finrank K V := by
  simp [weightRatio_def]

/-- Under zero total weight, the numerator of the ratio is just the subspace weight. -/
theorem weightRatio_eq_of_weight_top_eq_zero {L : Ω → ι → Module.Dual K V}
    {c : Ω → ι → ℝ} (h : weight L c (⊤ : Submodule K V) = 0)
    (U : Submodule K V) : weightRatio L c U =
      weight L c U / (finrank K V - (finrank K U : ℝ)) := by
  simp [weightRatio_def, h]

/-- Zero weights give weight ratio zero on every subspace. -/
@[simp]
theorem weightRatio_zero (L : Ω → ι → Module.Dual K V) (U : Submodule K V) :
    weightRatio L 0 U = 0 := by
  simp [weightRatio_def]

variable [FiniteDimensional K V]

/-- Multiplying the weight ratio by codimension recovers the weight gain. -/
theorem weightRatio_mul_codim (L : Ω → ι → Module.Dual K V) (c : Ω → ι → ℝ)
    (U : Submodule K V) :
    weightRatio L c U * (finrank K V - (finrank K U : ℝ)) =
      weight L c U - weight L c ⊤ := by
  by_cases hU : U = ⊤
  · subst U; simp
  · rw [weightRatio_def, div_mul_cancel₀]
    exact sub_ne_zero.mpr (by exact_mod_cast (ne_of_gt (finrank_lt hU)))

/-- An upper bound on a proper-subspace ratio is a linear weight bound. -/
theorem weightRatio_le_iff {L : Ω → ι → Module.Dual K V} {c : Ω → ι → ℝ}
    {U : Submodule K V} (hU : U ≠ ⊤) {a : ℝ} :
    weightRatio L c U ≤ a ↔ weight L c U - weight L c ⊤ ≤
      a * (finrank K V - (finrank K U : ℝ)) := by
  rw [weightRatio_def]
  exact div_le_iff₀ (sub_pos.mpr (by exact_mod_cast (finrank_lt hU)))

/-- A lower bound on a proper-subspace ratio is a linear weight bound. -/
theorem le_weightRatio_iff {L : Ω → ι → Module.Dual K V} {c : Ω → ι → ℝ}
    {U : Submodule K V} (hU : U ≠ ⊤) {a : ℝ} :
    a ≤ weightRatio L c U ↔ a * (finrank K V - (finrank K U : ℝ)) ≤
      weight L c U - weight L c ⊤ := by
  rw [weightRatio_def]
  exact le_div_iff₀ (sub_pos.mpr (by exact_mod_cast (finrank_lt hU)))

/-- A uniform upper bound on proper-subspace ratios is a linear weight bound,
including equality at the whole space. -/
theorem forall_weightRatio_le_iff {L : Ω → ι → Module.Dual K V} {c : Ω → ι → ℝ}
    {a : ℝ} :
    (∀ U : Submodule K V, U ≠ ⊤ → weightRatio L c U ≤ a) ↔
      ∀ U : Submodule K V, weight L c U - weight L c ⊤ ≤
        a * (finrank K V - (finrank K U : ℝ)) := by
  constructor
  · intro h U
    by_cases hU : U = ⊤
    · subst U; simp
    · exact (weightRatio_le_iff hU).mp (h U hU)
  · intro h U hU
    exact (weightRatio_le_iff hU).mpr (h U)

/-- Only finitely many weight ratios occur for finitely supported weights. -/
theorem finite_range_weightRatio (L : Ω → ι → Module.Dual K V) {c : Ω → ι → ℝ}
    (hc : HasFiniteSupport c) : (range (weightRatio L c)).Finite := by
  have hd : (range fun U : Submodule K V ↦ finrank K U).Finite :=
    (Set.finite_Iic (finrank K V)).subset (by rintro _ ⟨U, rfl⟩; exact finrank_le U)
  exact ((finite_range_weight L hc).image2
    (fun w (d : ℕ) ↦ (w - weight L c ⊤) / (finrank K V - (d : ℝ))) hd).subset
    (by rintro _ ⟨U, rfl⟩; exact ⟨_, ⟨U, rfl⟩, _, ⟨U, rfl⟩, rfl⟩)

/-- There is a proper maximum-ratio subspace of minimum dimension. -/
theorem exists_exceptionalSubspace [Nontrivial V]
    (L : Ω → ι → Module.Dual K V) {c : Ω → ι → ℝ} (hc : HasFiniteSupport c) :
    ∃ T : Submodule K V, T ≠ ⊤ ∧
      (∀ U, U ≠ ⊤ → weightRatio L c U ≤ weightRatio L c T) ∧
      ∀ U, U ≠ ⊤ → weightRatio L c U = weightRatio L c T → finrank K T ≤ finrank K U := by
  have hne : ({U : Submodule K V | U ≠ ⊤}).Nonempty := ⟨⊥, bot_ne_top⟩
  obtain ⟨a, ⟨T, hT, rfl⟩, ha⟩ :=
    Set.exists_max_image _ id
      ((finite_range_weightRatio L hc).subset (image_subset_range _ _))
      (hne.image (weightRatio L c))
  let s := {U : Submodule K V | U ≠ ⊤ ∧ weightRatio L c U = weightRatio L c T}
  have hs : ((fun U : Submodule K V ↦ finrank K U) '' s).Nonempty :=
    ⟨_, T, ⟨hT, rfl⟩, rfl⟩
  have hf : ((fun U : Submodule K V ↦ finrank K U) '' s).Finite :=
    (Set.finite_Iic (finrank K V)).subset (by rintro _ ⟨U, _, rfl⟩; exact finrank_le U)
  obtain ⟨_, ⟨S, hS, rfl⟩, hmin⟩ := Set.exists_min_image _ id hf hs
  refine ⟨S, hS.1, ?_, ?_⟩
  · intro U hU
    rw [hS.2]
    exact ha _ ⟨U, hU, rfl⟩
  · intro U hU heq
    exact hmin _ ⟨U, ⟨hU, heq.trans hS.2⟩, rfl⟩

/-- Intersecting a proper maximizer with a subspace of at least its ratio preserves the ratio. -/
theorem weightRatio_inf_eq_of_maximal {L : Ω → ι → Module.Dual K V}
    (hL : ∀ v, span K (range (L v)) = ⊤) {c : Ω → ι → ℝ}
    (hc : HasFiniteSupport c) {T U : Submodule K V} (hT : T ≠ ⊤)
    (hmax : ∀ W, W ≠ ⊤ → weightRatio L c W ≤ weightRatio L c T)
    (hUT : weightRatio L c T ≤ weightRatio L c U) :
    weightRatio L c (T ⊓ U) = weightRatio L c T := by
  have hI : T ⊓ U ≠ ⊤ := ne_top_of_le_ne_top hT inf_le_left
  have hbound := forall_weightRatio_le_iff.mp hmax
  have hdim := finrank_sup_add_finrank_inf_eq T U
  have hdimR : (finrank K ↥(T ⊔ U) : ℝ) + finrank K ↥(T ⊓ U) =
      finrank K T + finrank K U := by exact_mod_cast hdim
  have hTeq := (weightRatio_mul_codim L c T).symm
  have hcodim : 0 ≤ (finrank K V : ℝ) - finrank K U :=
    sub_nonneg.mpr (by exact_mod_cast (finrank_le U))
  have hUle := mul_le_mul_of_nonneg_right hUT hcodim
  rw [weightRatio_mul_codim] at hUle
  apply le_antisymm (hmax _ hI)
  apply (le_weightRatio_iff hI).mpr
  have hsuper := weight_inf_add_weight_sup hL hc T U
  have hsup := hbound (T ⊔ U)
  have hmul := congrArg (fun x : ℝ ↦ weightRatio L c T * x) hdimR
  simp only [mul_add] at hmul
  nlinarith only [hTeq, hUle, hsuper, hsup, hmul]

/-- A minimum-dimensional proper maximizer is contained in every subspace of at least its ratio. -/
theorem le_of_minimal_maximal_weightRatio {L : Ω → ι → Module.Dual K V}
    (hL : ∀ v, span K (range (L v)) = ⊤) {c : Ω → ι → ℝ}
    (hc : HasFiniteSupport c) {T U : Submodule K V} (hT : T ≠ ⊤)
    (hmax : ∀ W, W ≠ ⊤ → weightRatio L c W ≤ weightRatio L c T)
    (hmin : ∀ W, W ≠ ⊤ → weightRatio L c W = weightRatio L c T →
      finrank K T ≤ finrank K W)
    (hUT : weightRatio L c T ≤ weightRatio L c U) : T ≤ U := by
  have hI : T ⊓ U ≠ ⊤ := ne_top_of_le_ne_top hT inf_le_left
  have heq := weightRatio_inf_eq_of_maximal hL hc hT hmax hUT
  have hrank : finrank K ↥(T ⊓ U) = finrank K T :=
    le_antisymm (Submodule.finrank_mono (inf_le_left : T ⊓ U ≤ T)) (hmin _ hI heq)
  have hTI : T ⊓ U = T :=
    Submodule.eq_of_le_of_finrank_eq (inf_le_left : T ⊓ U ≤ T) hrank
  exact inf_eq_left.mp hTI

/-- The exceptional subspace is the minimum-dimensional proper weight-ratio maximizer.
It is zero when the space is zero or the spanning or finite-support conditions fail. -/
def exceptionalSubspace (L : Ω → ι → Module.Dual K V) (c : Ω → ι → ℝ) : Submodule K V := by
  classical
  exact if h : Nontrivial V ∧ (∀ v, span K (range (L v)) = ⊤) ∧ HasFiniteSupport c then
    letI := h.1
    (exists_exceptionalSubspace L h.2.2).choose
  else ⊥

/-- Failure of spanning gives the zero exceptional subspace. -/
@[simp]
theorem exceptionalSubspace_eq_bot_of_not_forall_span_eq_top
    {L : Ω → ι → Module.Dual K V} {c : Ω → ι → ℝ}
    (hL : ¬∀ v, span K (range (L v)) = ⊤) : exceptionalSubspace L c = ⊥ := by
  classical
  unfold exceptionalSubspace
  exact dite_eq_right (fun h ↦ hL h.2.1)

/-- Failure of finite weight support gives the zero exceptional subspace. -/
@[simp]
theorem exceptionalSubspace_eq_bot_of_not_hasFiniteSupport
    {L : Ω → ι → Module.Dual K V} {c : Ω → ι → ℝ}
    (hc : ¬HasFiniteSupport c) : exceptionalSubspace L c = ⊥ := by
  classical
  unfold exceptionalSubspace
  exact dite_eq_right (fun h ↦ hc h.2.2)

/-- The exceptional subspace is proper, maximizes the weight ratio, and has the
smallest dimension among the proper maximizers. -/
theorem exceptionalSubspace_spec [Nontrivial V] {L : Ω → ι → Module.Dual K V}
    (hL : ∀ v, span K (range (L v)) = ⊤) {c : Ω → ι → ℝ}
    (hc : HasFiniteSupport c) :
    exceptionalSubspace L c ≠ ⊤ ∧
      (∀ U, U ≠ ⊤ → weightRatio L c U ≤ weightRatio L c (exceptionalSubspace L c)) ∧
      ∀ U, U ≠ ⊤ → weightRatio L c U = weightRatio L c (exceptionalSubspace L c) →
        finrank K (exceptionalSubspace L c) ≤ finrank K U := by
  classical
  have heq : exceptionalSubspace L c = (exists_exceptionalSubspace L hc).choose := by
    unfold exceptionalSubspace
    exact dite_eq_left ⟨inferInstance, hL, hc⟩
  rw [heq]
  exact (exists_exceptionalSubspace L hc).choose_spec

/-- The exceptional subspace is proper on every nonzero space, even for invalid data. -/
theorem exceptionalSubspace_ne_top [Nontrivial V]
    (L : Ω → ι → Module.Dual K V) (c : Ω → ι → ℝ) : exceptionalSubspace L c ≠ ⊤ := by
  by_cases hL : ∀ v, span K (range (L v)) = ⊤
  · by_cases hc : HasFiniteSupport c
    · exact (exceptionalSubspace_spec hL hc).1
    · rw [exceptionalSubspace_eq_bot_of_not_hasFiniteSupport hc]
      exact bot_ne_top
  · rw [exceptionalSubspace_eq_bot_of_not_forall_span_eq_top hL]
    exact bot_ne_top

/-- Every proper subspace has weight ratio at most that of the exceptional subspace. -/
theorem weightRatio_le_weightRatio_exceptionalSubspace {L : Ω → ι → Module.Dual K V}
    (hL : ∀ v, span K (range (L v)) = ⊤) {c : Ω → ι → ℝ}
    (hc : HasFiniteSupport c) {U : Submodule K V} (hU : U ≠ ⊤) :
    weightRatio L c U ≤ weightRatio L c (exceptionalSubspace L c) := by
  cases subsingleton_or_nontrivial V
  · exact (hU (Subsingleton.elim _ _)).elim
  · exact (exceptionalSubspace_spec hL hc).2.1 U hU

/-- The exceptional subspace is contained in every subspace of at least its weight ratio. -/
theorem exceptionalSubspace_le {L : Ω → ι → Module.Dual K V}
    (hL : ∀ v, span K (range (L v)) = ⊤) {c : Ω → ι → ℝ}
    (hc : HasFiniteSupport c) {U : Submodule K V}
    (hle : weightRatio L c (exceptionalSubspace L c) ≤ weightRatio L c U) :
    exceptionalSubspace L c ≤ U := by
  cases subsingleton_or_nontrivial V
  · exact le_of_eq (Subsingleton.elim _ _)
  · obtain ⟨hT, hmax, hmin⟩ := exceptionalSubspace_spec hL hc
    exact le_of_minimal_maximal_weightRatio hL hc hT hmax hmin hle

/-- Any proper maximum-ratio subspace of minimum dimension is the exceptional subspace. -/
theorem eq_exceptionalSubspace_iff [Nontrivial V] {L : Ω → ι → Module.Dual K V}
    (hL : ∀ v, span K (range (L v)) = ⊤) {c : Ω → ι → ℝ}
    (hc : HasFiniteSupport c) (T : Submodule K V) :
    T = exceptionalSubspace L c ↔ T ≠ ⊤ ∧
      (∀ U, U ≠ ⊤ → weightRatio L c U ≤ weightRatio L c T) ∧
      ∀ U, U ≠ ⊤ → weightRatio L c U = weightRatio L c T → finrank K T ≤ finrank K U := by
  constructor
  · rintro rfl
    exact exceptionalSubspace_spec hL hc
  · rintro ⟨hT, hmax, hmin⟩
    have hE := exceptionalSubspace_ne_top L c
    have heq := le_antisymm (hmax _ hE)
      (weightRatio_le_weightRatio_exceptionalSubspace hL hc hT)
    exact le_antisymm (le_of_minimal_maximal_weightRatio hL hc hT hmax hmin heq.ge)
      (exceptionalSubspace_le hL hc heq.le)

/-- The exceptional subspace is zero exactly when the zero subspace maximizes the ratio. -/
theorem exceptionalSubspace_eq_bot_iff {L : Ω → ι → Module.Dual K V}
    (hL : ∀ v, span K (range (L v)) = ⊤) {c : Ω → ι → ℝ}
    (hc : HasFiniteSupport c) : exceptionalSubspace L c = ⊥ ↔
      ∀ U, U ≠ ⊤ → weightRatio L c U ≤ weightRatio L c ⊥ := by
  constructor
  · intro heq U hU
    simpa only [heq] using weightRatio_le_weightRatio_exceptionalSubspace hL hc hU
  · intro h
    cases subsingleton_or_nontrivial V
    · exact Subsingleton.elim _ _
    · exact le_bot_iff.mp (exceptionalSubspace_le hL hc
        (h _ (exceptionalSubspace_ne_top L c)))

/-- With total weight zero, the exceptional subspace is zero exactly when every
proper subspace has nonpositive weight (semistability). -/
theorem exceptionalSubspace_eq_bot_iff_of_weight_top_eq_zero
    {L : Ω → ι → Module.Dual K V}
    (hL : ∀ v, span K (range (L v)) = ⊤) {c : Ω → ι → ℝ}
    (hc : HasFiniteSupport c) (htop : weight L c (⊤ : Submodule K V) = 0) :
    exceptionalSubspace L c = ⊥ ↔ ∀ U, U ≠ ⊤ → weight L c U ≤ 0 := by
  rw [exceptionalSubspace_eq_bot_iff hL hc]
  simp only [weightRatio_bot, htop, neg_zero, zero_div]
  apply forall_congr'
  intro U
  apply imp_congr_right
  intro hU
  rw [weightRatio_le_iff hU]
  simp [htop]

/-- On a zero-dimensional space the exceptional subspace is zero. -/
@[simp]
theorem exceptionalSubspace_eq_bot_of_subsingleton [Subsingleton V]
    (L : Ω → ι → Module.Dual K V) (c : Ω → ι → ℝ) : exceptionalSubspace L c = ⊥ :=
  Subsingleton.elim _ _

/-- Zero weights give the zero exceptional subspace, for any system of forms. -/
@[simp]
theorem exceptionalSubspace_zero (L : Ω → ι → Module.Dual K V) :
    exceptionalSubspace L 0 = ⊥ := by
  classical
  by_cases hL : ∀ v, span K (range (L v)) = ⊤
  · exact (exceptionalSubspace_eq_bot_iff hL (by simp [HasFiniteSupport])).mpr (by simp)
  · exact exceptionalSubspace_eq_bot_of_not_forall_span_eq_top hL

end TauCeti
