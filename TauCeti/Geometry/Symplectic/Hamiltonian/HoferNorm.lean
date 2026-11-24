/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import TauCeti.Topology.Semicontinuity.CompactInfimum
public import Mathlib.Basic.Real.Pointwise

/-!
# The Hofer norm of a time-dependent Hamiltonian

Let `H : ℝ → M → ℝ` be a time-dependent Hamiltonian on a space `M`, run for times `t ∈ [0, 1]`.
Its **Hofer norm** is the integrated oscillation

`‖H‖ = ∫₀¹ (max_x H(t, x) - min_x H(t, x)) dt`,

and it splits into the **positive and negative parts**

`E⁺(H) = ∫₀¹ max_x H(t, x) dt`, `E⁻(H) = -∫₀¹ min_x H(t, x) dt = E⁺(-H)`,

so that `‖H‖ = E⁺(H) + E⁻(H)` (`TauCeti.hoferPlus`, `TauCeti.hoferMinus`, `TauCeti.hoferNorm`).
These are the quantities by which Floer continuation maps shift the action filtration: along a
continuation cylinder from `H₀` to `H₁` the action increases by at most `E⁺(H₀ - H₁)`, so the
filtration moves by at most the Hofer norm `‖H₀ - H₁‖`, and spectral invariants are Lipschitz
for the Hofer distance `‖H₀ - H₁‖`.

The definitions type-check for any `M`, the maxima being supremums `⨆ x, H t x`, but they are junk
values unless each `H t` is bounded above and `t ↦ ⨆ x, H t x` is integrable on `[0, 1]`: the real
supremum of an unbounded or empty family is `0`, and so is the integral of a non-integrable
function. The results are therefore stated for a compact space `M` and a jointly continuous `H`, as
for Hamiltonians on a closed manifold, where the maxima are attained and depend continuously on
`t` (`Continuous.le_ciSup_of_compactSpace`, `Continuous.iSup_apply_of_compactSpace`).

* `E⁺` is monotone, subadditive, positively homogeneous, and shifted by `∫₀¹ c` when a function
  `c(t)` of time alone is added (`TauCeti.hoferPlus_mono`, `TauCeti.hoferPlus_add_le`,
  `TauCeti.hoferPlus_smul`, `TauCeti.hoferPlus_add_const`).
* The Hofer norm is nonnegative, symmetric, subadditive and absolutely homogeneous
  (`TauCeti.hoferNorm_nonneg`, `TauCeti.hoferNorm_neg`, `TauCeti.hoferNorm_add_le`,
  `TauCeti.hoferNorm_smul`). It does not see functions of time alone
  (`TauCeti.hoferNorm_add_const`), and it vanishes exactly when each `H t`, `t ∈ [0, 1]`, is
  constant on `M` (`TauCeti.hoferNorm_eq_zero_iff`). So `‖H₀ - H₁‖` is a pseudometric on
  jointly continuous Hamiltonians on a compact `M` (`TauCeti.hoferNorm_sub_comm`,
  `TauCeti.hoferNorm_sub_le_hoferNorm_sub_add_hoferNorm_sub`), the Hofer distance, which
  identifies two Hamiltonians exactly when, at each time `t ∈ [0, 1]`, they differ by a constant.
* When `H t` changes sign at every time, for instance when it is normalized to have mean zero
  for a volume form or vanishes somewhere, both parts are nonnegative and hence at most the
  Hofer norm (`TauCeti.hoferPlus_le_hoferNorm`, `TauCeti.hoferMinus_le_hoferNorm`).

## Main definitions

* `TauCeti.hoferPlus H`: `E⁺(H) = ∫₀¹ max_x H(t, x) dt`.
* `TauCeti.hoferMinus H`: `E⁻(H) = E⁺(-H) = -∫₀¹ min_x H(t, x) dt`.
* `TauCeti.hoferNorm H`: `‖H‖ = E⁺(H) + E⁻(H)`.

## References

* H. Hofer, *On the topological properties of symplectic maps*, Proc. Roy. Soc. Edinburgh
  Sect. A 115 (1990), 25–38.
* L. Polterovich, *The geometry of the group of symplectic diffeomorphisms*, Lectures in
  Mathematics ETH Zürich, Birkhäuser, 2001, §§1.3 and 5.1.
* D. McDuff, D. Salamon, *J-holomorphic curves and symplectic topology*, 2nd ed., AMS Colloquium
  Publications 52, 2012, §12.3, on the energy shift of continuation maps.
-/

public section

noncomputable section

open Function MeasureTheory Set

namespace TauCeti

variable {M : Type*}

/-- The **positive part of the Hofer norm** of a time-dependent Hamiltonian `H : ℝ → M → ℝ`,
`E⁺(H) = ∫₀¹ max_x H(t, x) dt`, the maximum being the supremum `⨆ x, H t x`. -/
def hoferPlus (H : ℝ → M → ℝ) : ℝ :=
  ∫ t in Icc (0 : ℝ) 1, ⨆ x, H t x

/-- The **negative part of the Hofer norm** of a time-dependent Hamiltonian `H`,
`E⁻(H) = E⁺(-H) = -∫₀¹ min_x H(t, x) dt` (`TauCeti.hoferMinus_eq`). -/
def hoferMinus (H : ℝ → M → ℝ) : ℝ :=
  hoferPlus (-H)

/-- The **Hofer norm** of a time-dependent Hamiltonian `H`, the integrated oscillation
`‖H‖ = E⁺(H) + E⁻(H) = ∫₀¹ (max_x H(t, x) - min_x H(t, x)) dt` (`TauCeti.hoferNorm_eq`). -/
def hoferNorm (H : ℝ → M → ℝ) : ℝ :=
  hoferPlus H + hoferMinus H

theorem hoferPlus_def (H : ℝ → M → ℝ) : hoferPlus H = ∫ t in Icc (0 : ℝ) 1, ⨆ x, H t x :=
  (rfl)

theorem hoferMinus_def (H : ℝ → M → ℝ) : hoferMinus H = hoferPlus (-H) :=
  (rfl)

theorem hoferNorm_def (H : ℝ → M → ℝ) : hoferNorm H = hoferPlus H + hoferMinus H :=
  (rfl)

@[simp]
theorem hoferPlus_zero : hoferPlus (0 : ℝ → M → ℝ) = 0 := by
  simp [hoferPlus_def]

@[simp]
theorem hoferMinus_zero : hoferMinus (0 : ℝ → M → ℝ) = 0 := by
  simp [hoferMinus_def]

@[simp]
theorem hoferNorm_zero : hoferNorm (0 : ℝ → M → ℝ) = 0 := by
  simp [hoferNorm_def]

@[simp]
theorem hoferPlus_neg (H : ℝ → M → ℝ) : hoferPlus (-H) = hoferMinus H :=
  (rfl)

@[simp]
theorem hoferMinus_neg (H : ℝ → M → ℝ) : hoferMinus (-H) = hoferPlus H := by
  rw [hoferMinus_def, neg_neg]

@[simp]
theorem hoferNorm_neg (H : ℝ → M → ℝ) : hoferNorm (-H) = hoferNorm H := by
  rw [hoferNorm_def, hoferNorm_def, hoferPlus_neg, hoferMinus_neg, add_comm]

/-- **Symmetry of the Hofer distance.** `‖F - G‖ = ‖G - F‖`. -/
theorem hoferNorm_sub_comm (F G : ℝ → M → ℝ) : hoferNorm (F - G) = hoferNorm (G - F) := by
  rw [← neg_sub, hoferNorm_neg]

/-- The negative part of the Hofer norm is minus the integral of the minimum,
`E⁻(H) = -∫₀¹ min_x H(t, x) dt`. -/
theorem hoferMinus_eq (H : ℝ → M → ℝ) :
    hoferMinus H = -∫ t in Icc (0 : ℝ) 1, ⨅ x, H t x := by
  rw [hoferMinus_def, hoferPlus_def, ← integral_neg]
  refine setIntegral_congr_fun measurableSet_Icc fun t _ ↦ ?_
  simpa using (Real.mul_iInf_of_nonpos (r := -1) (by norm_num) (H t)).symm

/-- **Positive homogeneity of `E⁺`.** `E⁺(c • H) = c E⁺(H)` for `c ≥ 0`. -/
theorem hoferPlus_smul {c : ℝ} (hc : 0 ≤ c) (H : ℝ → M → ℝ) :
    hoferPlus (c • H) = c * hoferPlus H := by
  rw [hoferPlus_def, hoferPlus_def, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Icc fun t _ ↦ ?_
  simp [Real.mul_iSup_of_nonneg hc]

/-- **Absolute homogeneity of the Hofer norm.** `‖c • H‖ = |c| ‖H‖`. -/
theorem hoferNorm_smul (c : ℝ) (H : ℝ → M → ℝ) : hoferNorm (c • H) = |c| * hoferNorm H := by
  rcases le_total 0 c with hc | hc
  · rw [hoferNorm_def, hoferNorm_def, hoferMinus_def, hoferMinus_def, ← smul_neg,
      hoferPlus_smul hc, hoferPlus_smul hc, abs_of_nonneg hc, mul_add]
  · have h : c • H = -((-c) • H) := by rw [neg_smul, neg_neg]
    rw [h, hoferNorm_neg, hoferNorm_def, hoferNorm_def, hoferMinus_def, hoferMinus_def,
      ← smul_neg, hoferPlus_smul (neg_nonneg.2 hc), hoferPlus_smul (neg_nonneg.2 hc),
      abs_of_nonpos hc, mul_add]

/-- If `H t` takes a nonpositive value at every time `t ∈ [0, 1]`, for instance because it
vanishes somewhere or has mean zero for a volume form, then `E⁻(H) ≥ 0`. -/
theorem hoferMinus_nonneg {H : ℝ → M → ℝ} (h : ∀ t ∈ Icc (0 : ℝ) 1, ∃ x, H t x ≤ 0) :
    0 ≤ hoferMinus H :=
  setIntegral_nonneg measurableSet_Icc fun t ht ↦
    Real.iSup_nonneg' <| (h t ht).imp fun _ hx ↦ by simpa using hx

/-- If `H t` takes a nonnegative value at every time `t ∈ [0, 1]`, then `E⁺(H) ≥ 0`. -/
theorem hoferPlus_nonneg {H : ℝ → M → ℝ} (h : ∀ t ∈ Icc (0 : ℝ) 1, ∃ x, 0 ≤ H t x) :
    0 ≤ hoferPlus H :=
  setIntegral_nonneg measurableSet_Icc fun t ht ↦ Real.iSup_nonneg' (h t ht)

/-- If `H t` takes a nonpositive value at every time `t ∈ [0, 1]`, then `E⁺(H) ≤ ‖H‖`. -/
theorem hoferPlus_le_hoferNorm {H : ℝ → M → ℝ} (h : ∀ t ∈ Icc (0 : ℝ) 1, ∃ x, H t x ≤ 0) :
    hoferPlus H ≤ hoferNorm H :=
  le_add_of_nonneg_right (hoferMinus_nonneg h)

/-- If `H t` takes a nonnegative value at every time `t ∈ [0, 1]`, then `E⁻(H) ≤ ‖H‖`. -/
theorem hoferMinus_le_hoferNorm {H : ℝ → M → ℝ} (h : ∀ t ∈ Icc (0 : ℝ) 1, ∃ x, 0 ≤ H t x) :
    hoferMinus H ≤ hoferNorm H :=
  le_add_of_nonneg_left (hoferPlus_nonneg h)

variable [TopologicalSpace M] [CompactSpace M]

variable {F G H : ℝ → M → ℝ}

/-- **Monotonicity of `E⁺`.** If `F ≤ G` on `[0, 1] × M`, then `E⁺(F) ≤ E⁺(G)`. -/
theorem hoferPlus_mono (hF : Continuous (uncurry F)) (hG : Continuous (uncurry G))
    (h : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x, F t x ≤ G t x) : hoferPlus F ≤ hoferPlus G := by
  refine setIntegral_mono_on hF.iSup_apply_of_compactSpace.integrableOn_Icc
    hG.iSup_apply_of_compactSpace.integrableOn_Icc measurableSet_Icc fun t ht ↦ ?_
  rcases isEmpty_or_nonempty M with _ | _
  · simp
  · exact ciSup_mono (hG.uncurry_left t).bddAbove_range_of_compactSpace (h t ht)

/-- **Subadditivity of `E⁺`.** `E⁺(F + G) ≤ E⁺(F) + E⁺(G)`. -/
theorem hoferPlus_add_le (hF : Continuous (uncurry F)) (hG : Continuous (uncurry G)) :
    hoferPlus (F + G) ≤ hoferPlus F + hoferPlus G := by
  have hFi : IntegrableOn (fun t ↦ ⨆ x, F t x) (Icc (0 : ℝ) 1) :=
    hF.iSup_apply_of_compactSpace.integrableOn_Icc
  have hGi : IntegrableOn (fun t ↦ ⨆ x, G t x) (Icc (0 : ℝ) 1) :=
    hG.iSup_apply_of_compactSpace.integrableOn_Icc
  rw [hoferPlus_def, hoferPlus_def, hoferPlus_def, ← integral_add hFi hGi]
  have hFG : Continuous (uncurry (F + G)) := hF.add hG
  refine setIntegral_mono_on hFG.iSup_apply_of_compactSpace.integrableOn_Icc (hFi.add hGi)
    measurableSet_Icc fun t _ ↦ ?_
  rcases isEmpty_or_nonempty M with _ | _
  · simp
  · exact ciSup_le fun x ↦ add_le_add ((hF.uncurry_left t).le_ciSup_of_compactSpace x)
      ((hG.uncurry_left t).le_ciSup_of_compactSpace x)

/-- **Adding a function of time alone.** If `c : ℝ → ℝ` is integrable on `[0, 1]`, then
`E⁺(H + c) = E⁺(H) + ∫₀¹ c`, where `(H + c)(t, x) = H(t, x) + c(t)`. -/
theorem hoferPlus_add_const [Nonempty M] (hH : Continuous (uncurry H)) {c : ℝ → ℝ}
    (hc : IntegrableOn c (Icc (0 : ℝ) 1)) :
    hoferPlus (fun t x ↦ H t x + c t) = hoferPlus H + ∫ t in Icc (0 : ℝ) 1, c t := by
  rw [hoferPlus_def, hoferPlus_def,
    ← integral_add hH.iSup_apply_of_compactSpace.integrableOn_Icc hc]
  refine setIntegral_congr_fun measurableSet_Icc fun t _ ↦ ?_
  exact ((OrderIso.addRight (c t)).map_ciSup
    (hH.uncurry_left t).bddAbove_range_of_compactSpace).symm

/-- The Hofer norm is the integrated oscillation,
`‖H‖ = ∫₀¹ (max_x H(t, x) - min_x H(t, x)) dt`. -/
theorem hoferNorm_eq (hH : Continuous (uncurry H)) :
    hoferNorm H = ∫ t in Icc (0 : ℝ) 1, ((⨆ x, H t x) - ⨅ x, H t x) := by
  rw [hoferNorm_def, hoferMinus_eq, integral_sub hH.iSup_apply_of_compactSpace.integrableOn_Icc
    hH.iInf_apply_of_compactSpace.integrableOn_Icc, hoferPlus_def, sub_eq_add_neg]

/-- The integrand of the Hofer norm, the oscillation `max_x H(t, x) - min_x H(t, x)`, written as
`max_x H(t, x) + max_x (-H(t, x))`. It is nonnegative. -/
private theorem iSup_add_iSup_neg_nonneg (hH : Continuous (uncurry H)) (t : ℝ) :
    0 ≤ (⨆ x, H t x) + ⨆ x, (-H) t x := by
  rcases isEmpty_or_nonempty M with _ | ⟨⟨x⟩⟩
  · simp
  · have h₁ := (hH.uncurry_left t).le_ciSup_of_compactSpace x
    have h₂ := (Continuous.uncurry_left (f := -H) t hH.neg).le_ciSup_of_compactSpace x
    simp only [Pi.neg_apply] at h₂ ⊢
    linarith

private theorem hoferNorm_eq_integral_iSup_add (hH : Continuous (uncurry H)) :
    hoferNorm H = ∫ t in Icc (0 : ℝ) 1, ((⨆ x, H t x) + ⨆ x, (-H) t x) := by
  rw [hoferNorm_def, hoferMinus_def, hoferPlus_def, hoferPlus_def,
    integral_add hH.iSup_apply_of_compactSpace.integrableOn_Icc
      ((Continuous.iSup_apply_of_compactSpace (f := -H) hH.neg).integrableOn_Icc)]

/-- The Hofer norm is nonnegative. -/
theorem hoferNorm_nonneg (hH : Continuous (uncurry H)) : 0 ≤ hoferNorm H := by
  rw [hoferNorm_eq_integral_iSup_add hH]
  exact setIntegral_nonneg measurableSet_Icc fun t _ ↦ iSup_add_iSup_neg_nonneg hH t

/-- **The triangle inequality for the Hofer norm.** `‖F + G‖ ≤ ‖F‖ + ‖G‖`. -/
theorem hoferNorm_add_le (hF : Continuous (uncurry F)) (hG : Continuous (uncurry G)) :
    hoferNorm (F + G) ≤ hoferNorm F + hoferNorm G := by
  have h₁ := hoferPlus_add_le hF hG
  have h₂ := hoferPlus_add_le (F := -F) (G := -G) hF.neg hG.neg
  rw [← neg_add, hoferPlus_neg, hoferPlus_neg, hoferPlus_neg] at h₂
  rw [hoferNorm_def, hoferNorm_def, hoferNorm_def]
  linarith

/-- **The triangle inequality for the Hofer distance.** `‖F - G‖ ≤ ‖F - K‖ + ‖K - G‖`. -/
theorem hoferNorm_sub_le_hoferNorm_sub_add_hoferNorm_sub {K : ℝ → M → ℝ}
    (hF : Continuous (uncurry F)) (hG : Continuous (uncurry G)) (hK : Continuous (uncurry K)) :
    hoferNorm (F - G) ≤ hoferNorm (F - K) + hoferNorm (K - G) := by
  simpa using hoferNorm_add_le (F := F - K) (G := K - G) (hF.sub hK) (hK.sub hG)

/-- **The Hofer norm does not see functions of time alone.** If `c : ℝ → ℝ` is integrable on
`[0, 1]`, then `‖H + c‖ = ‖H‖`, where `(H + c)(t, x) = H(t, x) + c(t)`. -/
theorem hoferNorm_add_const (hH : Continuous (uncurry H)) {c : ℝ → ℝ}
    (hc : IntegrableOn c (Icc (0 : ℝ) 1)) :
    hoferNorm (fun t x ↦ H t x + c t) = hoferNorm H := by
  rcases isEmpty_or_nonempty M with _ | _
  · simp [hoferNorm_def, hoferMinus_def, hoferPlus_def]
  have hneg : -(fun t x ↦ H t x + c t) = fun t x ↦ (-H) t x + (-c) t := by
    ext t x
    simp [add_comm]
  rw [hoferNorm_def, hoferNorm_def, hoferMinus_def, hoferMinus_def, hneg,
    hoferPlus_add_const hH hc, hoferPlus_add_const hH.neg hc.neg]
  simp only [Pi.neg_apply, integral_neg]
  ring

/-- **The Hofer norm vanishes exactly on the Hamiltonians that are constant on `M` at every
time.** For a jointly continuous `H` on `ℝ × M`, `‖H‖ = 0` if and only if `H t` is constant on
`M` for every `t ∈ [0, 1]`. -/
theorem hoferNorm_eq_zero_iff (hH : Continuous (uncurry H)) :
    hoferNorm H = 0 ↔ ∀ t ∈ Icc (0 : ℝ) 1, ∀ x y, H t x = H t y := by
  set g : ℝ → ℝ := fun t ↦ (⨆ x, H t x) + ⨆ x, (-H) t x with hg
  have hgc : Continuous g :=
    hH.iSup_apply_of_compactSpace.add (Continuous.iSup_apply_of_compactSpace (f := -H) hH.neg)
  have hgi : IntegrableOn g (Icc (0 : ℝ) 1) := hgc.integrableOn_Icc
  have hg0 : 0 ≤ᵐ[volume.restrict (Icc (0 : ℝ) 1)] g :=
    Filter.Eventually.of_forall fun t ↦ iSup_add_iSup_neg_nonneg hH t
  rw [hoferNorm_eq_integral_iSup_add hH, setIntegral_eq_zero_iff_of_nonneg_ae hg0 hgi]
  constructor
  · intro h t ht x y
    have hzero : g t = 0 := Measure.eqOn_Icc_of_ae_eq volume zero_ne_one h hgc.continuousOn
      continuousOn_const ht
    have hx := (hH.uncurry_left t).le_ciSup_of_compactSpace x
    have hy := (Continuous.uncurry_left (f := -H) t hH.neg).le_ciSup_of_compactSpace y
    have hy' := (hH.uncurry_left t).le_ciSup_of_compactSpace y
    have hx' := (Continuous.uncurry_left (f := -H) t hH.neg).le_ciSup_of_compactSpace x
    simp only [hg, Pi.neg_apply] at hzero hy hx'
    linarith
  · intro h
    refine (ae_restrict_iff' measurableSet_Icc).2 (Filter.Eventually.of_forall fun t ht ↦ ?_)
    rcases isEmpty_or_nonempty M with _ | hM
    · simp [hg]
    obtain ⟨x₀⟩ := id hM
    have hconst : H t = fun _ ↦ H t x₀ := funext fun x ↦ h t ht x x₀
    simp only [hg, Pi.neg_apply, Pi.zero_apply]
    rw [hconst]
    simp

end TauCeti
