/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
public import Mathlib.Analysis.RCLike.Lemmas
public import TauCeti.Analysis.Normed.Operator.ContinuousLinearEquiv

/-!
# The Banach–Mazur distance

The Banach–Mazur distance between two normed spaces `E` and `F` is
`d(E, F) = inf ‖T‖ ‖T⁻¹‖`, the infimum over continuous linear equivalences `T : E ≃L[𝕜] F`.
It measures how far `E` and `F` are from being isometric, and is the distance used to compare
finite-dimensional spaces with Euclidean spaces in the local theory of Banach spaces.

`TauCeti.banachMazurDist 𝕜 E F` is this infimum, as a real number. When `E` and `F` are not
isomorphic the infimum is over the empty set and its value is the junk value `0`; two
finite-dimensional spaces over a complete field are isomorphic exactly when they have the same
dimension (`FiniteDimensional.nonempty_continuousLinearEquiv_iff_finrank_eq`).

## Main results

* `TauCeti.banachMazurDist_comm`: the distance is symmetric.
* `TauCeti.banachMazurDist_triangle`: the multiplicative triangle inequality
  `d(E, G) ≤ d(E, F) d(F, G)`.
* `TauCeti.one_le_banachMazurDist`: between isomorphic nonzero spaces the distance is at least `1`.
* `LinearIsometryEquiv.banachMazurDist_congr_left` and
  `LinearIsometryEquiv.banachMazurDist_congr_right`: the distance is invariant under replacing
  either space by an isometric copy.
* `TauCeti.exists_norm_mul_norm_symm_eq_banachMazurDist`: over a locally compact field, the
  infimum is attained when the spaces are finite-dimensional.
* `TauCeti.banachMazurDist_eq_one_iff`: over `ℝ` or `ℂ`, two nonzero finite-dimensional spaces
  are at distance one exactly when they are isometric.

Over a general locally compact field the last statement fails, since the norms of scalars need
not fill out the positive reals: rescaling the norm of a field such as `ℚ_[p]` by a factor that is
not the norm of a scalar gives a space at distance one from `ℚ_[p]` but not isometric to it.

## References

* F. Albiac and N. J. Kalton, *Topics in Banach Space Theory*, Chapter 12.
-/

public section

open Set

namespace TauCeti

variable (𝕜 E F : Type*)

section Definition

variable [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- The **Banach–Mazur distance** between normed spaces `E` and `F`: the infimum of
`‖T‖ * ‖T⁻¹‖` over all continuous linear equivalences `T : E ≃L[𝕜] F`. It takes the junk value
`0` when there is no such equivalence. -/
noncomputable def banachMazurDist : ℝ :=
  ⨅ T : E ≃L[𝕜] F, ‖(T : E →L[𝕜] F)‖ * ‖(T.symm : F →L[𝕜] E)‖

/-- The defining formula of `banachMazurDist`, as an infimum over continuous linear
equivalences. -/
theorem banachMazurDist_def :
    banachMazurDist 𝕜 E F = ⨅ T : E ≃L[𝕜] F, ‖(T : E →L[𝕜] F)‖ * ‖(T.symm : F →L[𝕜] E)‖ :=
  (rfl)

end Definition

variable {𝕜 E F}

section Basic

variable {G : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup G] [NormedSpace 𝕜 G]

private theorem bddBelow_range_norm_mul_norm_symm :
    BddBelow (range fun T : E ≃L[𝕜] F ↦ ‖(T : E →L[𝕜] F)‖ * ‖(T.symm : F →L[𝕜] E)‖) :=
  ⟨0, forall_mem_range.2 fun _ ↦ by positivity⟩

/-- The Banach–Mazur distance is nonnegative. -/
theorem banachMazurDist_nonneg : 0 ≤ banachMazurDist 𝕜 E F :=
  Real.iInf_nonneg fun _ ↦ by positivity

/-- Without continuous linear equivalences, the Banach–Mazur distance takes the junk value `0`. -/
theorem banachMazurDist_of_isEmpty [IsEmpty (E ≃L[𝕜] F)] : banachMazurDist 𝕜 E F = 0 :=
  Real.iInf_of_isEmpty _

/-- Each continuous linear equivalence bounds the Banach–Mazur distance from above. -/
theorem banachMazurDist_le (T : E ≃L[𝕜] F) :
    banachMazurDist 𝕜 E F ≤ ‖(T : E →L[𝕜] F)‖ * ‖(T.symm : F →L[𝕜] E)‖ :=
  ciInf_le bddBelow_range_norm_mul_norm_symm T

/-- Lower bounds for the Banach–Mazur distance between isomorphic spaces are the common lower
bounds of `‖T‖ * ‖T⁻¹‖`. -/
theorem le_banachMazurDist_iff [Nonempty (E ≃L[𝕜] F)] {r : ℝ} :
    r ≤ banachMazurDist 𝕜 E F ↔
      ∀ T : E ≃L[𝕜] F, r ≤ ‖(T : E →L[𝕜] F)‖ * ‖(T.symm : F →L[𝕜] E)‖ :=
  le_ciInf_iff bddBelow_range_norm_mul_norm_symm

/-- The Banach–Mazur distance between isomorphic spaces is less than `r` exactly when some
continuous linear equivalence has `‖T‖ * ‖T⁻¹‖ < r`. -/
theorem banachMazurDist_lt_iff [Nonempty (E ≃L[𝕜] F)] {r : ℝ} :
    banachMazurDist 𝕜 E F < r ↔
      ∃ T : E ≃L[𝕜] F, ‖(T : E →L[𝕜] F)‖ * ‖(T.symm : F →L[𝕜] E)‖ < r :=
  ciInf_lt_iff bddBelow_range_norm_mul_norm_symm

/-- The Banach–Mazur distance is symmetric. -/
theorem banachMazurDist_comm : banachMazurDist 𝕜 E F = banachMazurDist 𝕜 F E :=
  Equiv.iInf_congr ⟨ContinuousLinearEquiv.symm, ContinuousLinearEquiv.symm,
    ContinuousLinearEquiv.symm_symm, ContinuousLinearEquiv.symm_symm⟩ fun T ↦ by
      simp [mul_comm]

/-- The **multiplicative triangle inequality** for the Banach–Mazur distance. The hypothesis
excludes the junk value `0` of `banachMazurDist 𝕜 E F`; when `F` and `G` are not isomorphic but
`E` and `F` are, both sides vanish. -/
theorem banachMazurDist_triangle (h : Nonempty (E ≃L[𝕜] F)) :
    banachMazurDist 𝕜 E G ≤ banachMazurDist 𝕜 E F * banachMazurDist 𝕜 F G := by
  rcases isEmpty_or_nonempty (F ≃L[𝕜] G) with hFG | hFG
  · have : IsEmpty (E ≃L[𝕜] G) := ⟨fun S ↦ hFG.false (h.some.symm.trans S)⟩
    rw [banachMazurDist_of_isEmpty]
    exact mul_nonneg banachMazurDist_nonneg banachMazurDist_nonneg
  rw [banachMazurDist_def 𝕜 E F, Real.iInf_mul_of_nonneg banachMazurDist_nonneg]
  refine le_ciInf fun T ↦ ?_
  rw [banachMazurDist_def 𝕜 F G, Real.mul_iInf_of_nonneg (by positivity)]
  refine le_ciInf fun S ↦ (banachMazurDist_le (T.trans S)).trans ?_
  have hsymm : ((T.trans S).symm : G →L[𝕜] E) =
      (T.symm : F →L[𝕜] E).comp (S.symm : G →L[𝕜] F) :=
    ContinuousLinearMap.ext fun x ↦ ContinuousLinearEquiv.symm_trans_apply S T x
  rw [← ContinuousLinearEquiv.comp_coe, hsymm]
  calc ‖(S : F →L[𝕜] G).comp (T : E →L[𝕜] F)‖ *
        ‖(T.symm : F →L[𝕜] E).comp (S.symm : G →L[𝕜] F)‖
    _ ≤ (‖(S : F →L[𝕜] G)‖ * ‖(T : E →L[𝕜] F)‖) *
          (‖(T.symm : F →L[𝕜] E)‖ * ‖(S.symm : G →L[𝕜] F)‖) := by
      gcongr <;> exact ContinuousLinearMap.opNorm_comp_le _ _
    _ = _ := by ring

/-- Between isomorphic nonzero spaces, the Banach–Mazur distance is at least `1`. -/
theorem one_le_banachMazurDist [Nontrivial E] (h : Nonempty (E ≃L[𝕜] F)) :
    1 ≤ banachMazurDist 𝕜 E F := by
  refine le_banachMazurDist_iff.2 fun T ↦ ?_
  calc (1 : ℝ) = ‖(T.symm : F →L[𝕜] E).comp (T : E →L[𝕜] F)‖ := by simp
    _ ≤ _ := (ContinuousLinearMap.opNorm_comp_le _ _).trans_eq (mul_comm _ _)

/-- A nonzero space is at Banach–Mazur distance `1` from itself. -/
@[simp]
theorem banachMazurDist_self [Nontrivial E] : banachMazurDist 𝕜 E E = 1 :=
  le_antisymm ((banachMazurDist_le (ContinuousLinearEquiv.refl 𝕜 E)).trans_eq (by simp))
    (one_le_banachMazurDist ⟨ContinuousLinearEquiv.refl 𝕜 E⟩)

end Basic

end TauCeti

namespace LinearIsometryEquiv

open TauCeti

variable {𝕜 E F : Type*} {E' : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup E']
  [NormedSpace 𝕜 E']

/-- Isometric spaces are at Banach–Mazur distance at most `1`. -/
theorem banachMazurDist_le_one (e : E ≃ₗᵢ[𝕜] F) : banachMazurDist 𝕜 E F ≤ 1 :=
  (banachMazurDist_le e.toContinuousLinearEquiv).trans <|
    (mul_le_mul e.toLinearIsometry.norm_toContinuousLinearMap_le
      e.symm.toLinearIsometry.norm_toContinuousLinearMap_le (norm_nonneg _) zero_le_one).trans_eq
      (one_mul 1)

/-- Isometric nonzero spaces are at Banach–Mazur distance `1`. -/
theorem banachMazurDist_eq_one [Nontrivial E] (e : E ≃ₗᵢ[𝕜] F) : banachMazurDist 𝕜 E F = 1 :=
  le_antisymm e.banachMazurDist_le_one (one_le_banachMazurDist ⟨e.toContinuousLinearEquiv⟩)

/-- The Banach–Mazur distance is unchanged when the first space is replaced by an isometric
copy. -/
theorem banachMazurDist_congr_left (e : E ≃ₗᵢ[𝕜] E') :
    banachMazurDist 𝕜 E F = banachMazurDist 𝕜 E' F := by
  refine le_antisymm ((banachMazurDist_triangle ⟨e.toContinuousLinearEquiv⟩).trans ?_)
    ((banachMazurDist_triangle ⟨e.symm.toContinuousLinearEquiv⟩).trans ?_)
  · exact mul_le_of_le_one_left banachMazurDist_nonneg e.banachMazurDist_le_one
  · exact mul_le_of_le_one_left banachMazurDist_nonneg e.symm.banachMazurDist_le_one

/-- The Banach–Mazur distance is unchanged when the second space is replaced by an isometric
copy. -/
theorem banachMazurDist_congr_right (e : F ≃ₗᵢ[𝕜] E') :
    banachMazurDist 𝕜 E F = banachMazurDist 𝕜 E E' := by
  rw [banachMazurDist_comm, e.banachMazurDist_congr_left, banachMazurDist_comm]

end LinearIsometryEquiv

namespace TauCeti

variable {𝕜 E F : Type*}

section Attained

variable [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- Over a locally compact field, the infimum defining the Banach–Mazur distance between
isomorphic finite-dimensional spaces is attained. -/
theorem exists_norm_mul_norm_symm_eq_banachMazurDist [LocallyCompactSpace 𝕜]
    [FiniteDimensional 𝕜 E] (h : Nonempty (E ≃L[𝕜] F)) :
    ∃ T : E ≃L[𝕜] F,
      ‖(T : E →L[𝕜] F)‖ * ‖(T.symm : F →L[𝕜] E)‖ = banachMazurDist 𝕜 E F := by
  obtain ⟨T₀⟩ := h
  rcases subsingleton_or_nontrivial E with hE | hE
  · -- On the zero space every operator has norm `0`, so every equivalence attains the value `0`.
    exact ⟨T₀, by simp [banachMazurDist_def, ContinuousLinearMap.opNorm_subsingleton]⟩
  -- Minimize `‖A‖ * ‖B‖` over the compact set of mutually inverse pairs `(A, B)` with
  -- `‖A‖ ≤ 1` and `‖B‖ ≤ ‖c‖ * P`; every equivalence with `‖T‖ * ‖T⁻¹‖ ≤ ‖T₀‖ * ‖T₀⁻¹‖` rescales
  -- into this set.
  have : FiniteDimensional 𝕜 F := T₀.toLinearEquiv.finiteDimensional
  have : ProperSpace (E →L[𝕜] F) := FiniteDimensional.proper 𝕜 _
  have : ProperSpace (F →L[𝕜] E) := FiniteDimensional.proper 𝕜 _
  obtain ⟨c, hc⟩ := NormedField.exists_one_lt_norm 𝕜
  set P := ‖(T₀ : E →L[𝕜] F)‖ * ‖(T₀.symm : F →L[𝕜] E)‖
  set g : (E →L[𝕜] F) × (F →L[𝕜] E) → ℝ := fun p ↦ ‖p.1‖ * ‖p.2‖
  set K : Set ((E →L[𝕜] F) × (F →L[𝕜] E)) :=
    (Metric.closedBall 0 1 ×ˢ Metric.closedBall 0 (‖c‖ * P)) ∩
      {p | p.1.comp p.2 = .id 𝕜 F ∧ p.2.comp p.1 = .id 𝕜 E}
  have hK : IsCompact K := by
    refine (isCompact_closedBall _ _).prod (isCompact_closedBall _ _) |>.inter_right ?_
    exact (isClosed_eq (continuous_fst.clm_comp continuous_snd) continuous_const).inter
      (isClosed_eq (continuous_snd.clm_comp continuous_fst) continuous_const)
  have hmem {T : E ≃L[𝕜] F} (hT : ‖(T : E →L[𝕜] F)‖ * ‖(T.symm : F →L[𝕜] E)‖ ≤ P) :
      ∃ p ∈ K, g p = ‖(T : E →L[𝕜] F)‖ * ‖(T.symm : F →L[𝕜] E)‖ := by
    obtain ⟨U, hU₁, hU₂, hU⟩ := T.exists_norm_le_one_and_norm_symm_le hc
    refine ⟨((U : E →L[𝕜] F), (U.symm : F →L[𝕜] E)), ⟨⟨?_, ?_⟩, ?_, ?_⟩, hU⟩
    · simpa using hU₁
    · simpa using hU₂.trans (by gcongr)
    · exact U.coe_comp_coe_symm
    · exact U.coe_symm_comp_coe
  obtain ⟨p₀, hp₀K, -⟩ := hmem le_rfl
  obtain ⟨p, ⟨-, hp₁, hp₂⟩, hmin⟩ := hK.exists_isMinOn ⟨p₀, hp₀K⟩
    ((continuous_fst.norm.mul continuous_snd.norm).continuousOn)
  refine ⟨.equivOfInverse' p.1 p.2 hp₁ hp₂, le_antisymm ?_ (banachMazurDist_le _)⟩
  simp only [ContinuousLinearEquiv.toContinuousLinearMap_equivOfInverse',
    ContinuousLinearEquiv.symm_equivOfInverse']
  have : Nonempty (E ≃L[𝕜] F) := ⟨T₀⟩
  refine le_ciInf fun T ↦ ?_
  rcases le_or_gt (‖(T : E →L[𝕜] F)‖ * ‖(T.symm : F →L[𝕜] E)‖) P with hT | hT
  · obtain ⟨q, hqK, hq⟩ := hmem hT
    exact (hmin hqK).trans_eq hq
  · obtain ⟨q, hqK, hq⟩ := hmem (T := T₀) le_rfl
    exact ((hmin hqK).trans_eq hq).trans hT.le

end Attained

section RCLike

variable [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F]
  [NormedSpace 𝕜 F]

/-- Two nonzero finite-dimensional real or complex normed spaces are at Banach–Mazur distance `1`
if and only if they are isometric. -/
theorem banachMazurDist_eq_one_iff [FiniteDimensional 𝕜 E] [Nontrivial E] :
    banachMazurDist 𝕜 E F = 1 ↔ Nonempty (E ≃ₗᵢ[𝕜] F) := by
  refine ⟨fun h ↦ ?_, fun ⟨e⟩ ↦ e.banachMazurDist_eq_one⟩
  have hne : Nonempty (E ≃L[𝕜] F) := by
    by_contra hne
    rw [not_nonempty_iff] at hne
    simp [banachMazurDist_of_isEmpty] at h
  obtain ⟨T, hT⟩ := exists_norm_mul_norm_symm_eq_banachMazurDist hne
  rw [h] at hT
  -- Rescale a minimizer `T` to norm one; then its inverse also has norm one.
  set a := ‖(T : E →L[𝕜] F)‖
  have ha : a ≠ 0 := left_ne_zero_of_mul_eq_one hT
  obtain ⟨U, hU, hUs⟩ := T.exists_coe_eq_smul (inv_ne_zero (RCLike.ofReal_ne_zero.2 ha))
  have hU₁ : ‖(U : E →L[𝕜] F)‖ ≤ 1 := by
    rw [hU, norm_smul, norm_inv, RCLike.norm_ofReal, abs_of_nonneg (norm_nonneg _),
      inv_mul_cancel₀ ha]
  have hUs₁ : ‖(U.symm : F →L[𝕜] E)‖ ≤ 1 := by
    rw [hUs, inv_inv, norm_smul, RCLike.norm_ofReal, abs_of_nonneg (norm_nonneg _), hT]
  exact ⟨.ofBounds U.toLinearEquiv
    (fun x ↦ ((U : E →L[𝕜] F).le_of_opNorm_le hU₁ x).trans_eq (one_mul _))
    (fun y ↦ ((U.symm : F →L[𝕜] E).le_of_opNorm_le hUs₁ y).trans_eq (one_mul _))⟩

end RCLike

end TauCeti
