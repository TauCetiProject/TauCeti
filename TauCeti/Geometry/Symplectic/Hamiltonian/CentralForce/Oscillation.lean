/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.CentralForce.TurningPoint

import Mathlib.Analysis.Calculus.Deriv.MeanValue
import TauCeti.Analysis.Calculus.Deriv.Slope
import TauCeti.Analysis.Calculus.Deriv.TurningPoint
import TauCeti.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Periodicity of the radial motion in a potential well

A particle of mass `m > 0` with angular momentum `ℓ` in a central potential `U` moves radially
according to the reduced Hamiltonian `H_ℓ(r, p_r) = p_r² / (2m) + U_ℓ(r)`, with effective potential
`U_ℓ(r) = ℓ² / (2 m r²) + U(r)` (`TauCeti.effectivePotential`), and Hamilton's equations
`r' = p_r / m`, `p_r' = -U_ℓ'(r)`. Let `0 < r₁ < r₂` be *simple turning points* of energy `E`:
`U_ℓ(r₁) = U_ℓ(r₂) = E`, `U_ℓ < E` on `(r₁, r₂)`, and `U_ℓ'(rᵢ) ≠ 0`, for a potential `U`
differentiable near the potential well `[r₁, r₂]`. This file shows that every motion of energy `E`
defined for all times and starting in the well is periodic, with period the radial period

`T = 2 ∫_{r₁}^{r₂} m dr / |p_r| = 2 ∫_{r₁}^{r₂} dr / √((2 / m) (E - U_ℓ(r)))`

(`TauCeti.radialPeriod`), twice the time quadrature between the turning points.

* **Confinement.** Just outside the well the effective potential exceeds `E`, because the turning
  points are simple, and the energy is conserved, so the motion never leaves `[r₁, r₂]`
  (`TauCeti.mem_Icc_of_forall_hasDerivAt_effectivePotential`). Its radial momentum vanishes exactly
  at the turning points.
* **Oscillation.** While `p_r ≠ 0` the radius is monotone, so such a passage lasts at most the
  time quadrature, which converges at simple turning points. At a turning point `p_r = 0` and
  `p_r' = -U_ℓ'(rᵢ) ≠ 0`, so the radial momentum changes sign there. Hence, by the oscillation
  between two turning points of `TauCeti.Analysis.Calculus.Deriv.TurningPoint`, every motion
  reaches the inner turning point
  (`TauCeti.exists_fst_eq_of_forall_hasDerivAt_effectivePotential`), and from there the radius
  rises to `r₂` and falls back to `r₁` in exactly the time `T`
  (`TauCeti.exists_mem_Ioo_fst_eq_of_forall_hasDerivAt_effectivePotential`).
* **Periodicity.** Along a rising stretch from `r₁` the elapsed time is the quadrature
  `∫_{r₁}^{r} m dr / |p_r|`, a strictly increasing function of the radius `r` reached, and along a
  falling stretch to `r₁` the remaining time is the same function of `r`. So the time since the last
  passage through `r₁` determines the state `(r, p_r)`, and the motion is `T`-periodic
  (`TauCeti.periodic_of_forall_hasDerivAt_effectivePotential`). The potential need only be
  differentiable near the well: no Lipschitz condition on `U'` is assumed.
* **Precession.** If the polar angle satisfies `θ' = ℓ / (m r²)`, it advances by twice the apsidal
  angle `TauCeti.apsidalAngle` during every radial period, starting at any time
  (`TauCeti.sub_eq_two_mul_apsidalAngle_of_forall_hasDerivAt_effectivePotential`).

## References

* V. I. Arnold, *Mathematical Methods of Classical Mechanics*, 2nd ed., Graduate Texts in
  Mathematics 60, Springer, 1989, Section 8.
* L. D. Landau, E. M. Lifshitz, *Mechanics*, 3rd ed., Pergamon, 1976, Sections 11 and 14.
-/

public section

open Function Set Filter MeasureTheory intervalIntegral
open scoped Topology

namespace TauCeti

variable {m ℓ E r₁ r₂ : ℝ} {U : ℝ → ℝ}

/-- On the closed half-line `r ≥ 0`, the reduced Hamiltonian is `p_r² / (2m) + U_ℓ(r)`. -/
private theorem reducedHamiltonian_eq {r : ℝ} (hr : 0 ≤ r) (p : ℝ) :
    centralForceHamiltonian m (effectivePotential m ℓ U) (r, p) =
      p ^ 2 / (2 * m) + effectivePotential m ℓ U r := by
  rw [centralForceHamiltonian_effectivePotential_apply hr, effectivePotential_apply, add_assoc]

/-- For `U` differentiable near `[r₁, r₂]` with `r₁ > 0`, the effective potential is
differentiable on `[r₁, r₂]`. -/
private theorem hasDerivAt_deriv_effectivePotential (hr₁ : 0 < r₁)
    (hU : ∀ᶠ r in 𝓝ˢ (Icc r₁ r₂), DifferentiableAt ℝ U r) {r : ℝ} (hr : r ∈ Icc r₁ r₂) :
    HasDerivAt (effectivePotential m ℓ U) (deriv (effectivePotential m ℓ U) r) r :=
  (hasDerivAt_effectivePotential (hU.self_of_nhdsSet r hr).hasDerivAt
    (hr₁.trans_le hr.1).ne').differentiableAt.hasDerivAt

section Well

variable (hm : 0 < m) (hr₁ : 0 < r₁) (h₁₂ : r₁ < r₂)
  (hU : ∀ᶠ r in 𝓝ˢ (Icc r₁ r₂), DifferentiableAt ℝ U r)
  (hE₁ : effectivePotential m ℓ U r₁ = E) (hE₂ : effectivePotential m ℓ U r₂ = E)
  (hlt : ∀ r ∈ Ioo r₁ r₂, effectivePotential m ℓ U r < E)
  (hd₁ : deriv (effectivePotential m ℓ U) r₁ ≠ 0) (hd₂ : deriv (effectivePotential m ℓ U) r₂ ≠ 0)

include hr₁ h₁₂ hU hE₂ hlt hd₂ in
/-- At the outer turning point the effective potential increases. -/
private theorem deriv_effectivePotential_pos : 0 < deriv (effectivePotential m ℓ U) r₂ := by
  refine lt_of_le_of_ne (not_lt.1 fun hneg ↦ ?_) hd₂.symm
  -- Otherwise `U_ℓ` would exceed `U_ℓ(r₂) = E` just to the left of `r₂`.
  have h := ((hasDerivAt_deriv_effectivePotential hr₁ hU
    (right_mem_Icc.2 h₁₂.le)).neg.hasDerivWithinAt (s := Iio r₂)).eventually_nhdsLT_lt_of_pos
    (neg_pos.2 hneg)
  obtain ⟨r, hr, hr'⟩ := (h.and (Ioo_mem_nhdsLT h₁₂)).exists
  simp only [Pi.neg_apply, neg_lt_neg_iff] at hr
  linarith [hlt r hr']

include hr₁ h₁₂ hU hE₁ hlt hd₁ in
/-- At the inner turning point the effective potential decreases. -/
private theorem deriv_effectivePotential_neg : deriv (effectivePotential m ℓ U) r₁ < 0 := by
  refine lt_of_le_of_ne (not_lt.1 fun hpos ↦ ?_) hd₁
  -- Otherwise `U_ℓ` would exceed `U_ℓ(r₁) = E` just to the right of `r₁`.
  have h := ((hasDerivAt_deriv_effectivePotential hr₁ hU (left_mem_Icc.2 h₁₂.le)).hasDerivWithinAt
    (s := Ioi r₁)).eventually_nhdsGT_lt_of_pos hpos
  obtain ⟨r, hr, hr'⟩ := (h.and (Ioo_mem_nhdsGT h₁₂)).exists
  linarith [hlt r hr']

include hr₁ h₁₂ hU hE₁ hE₂ hlt hd₁ hd₂ in
/-- **The well is isolated.** There are radii `0 ≤ a < r₁` and `b > r₂` such that `U` is
differentiable on `(a, b)` and the effective potential exceeds `E` on `(a, r₁)` and on `(r₂, b)`. -/
private theorem exists_lt_effectivePotential :
    ∃ a b, 0 ≤ a ∧ a < r₁ ∧ r₂ < b ∧ (∀ r ∈ Ioo a b, DifferentiableAt ℝ U r) ∧
      (∀ r ∈ Ioo a r₁, E < effectivePotential m ℓ U r) ∧
      ∀ r ∈ Ioo r₂ b, E < effectivePotential m ℓ U r := by
  have h₁ := (((hasDerivAt_deriv_effectivePotential hr₁ hU
    (left_mem_Icc.2 h₁₂.le)).neg.hasDerivWithinAt (s := Iio r₁)).eventually_nhdsLT_lt_of_pos
    (neg_pos.2 (deriv_effectivePotential_neg hr₁ h₁₂ hU hE₁ hlt hd₁))).and
    (hU.filter_mono (nhdsWithin_le_nhds.trans (nhds_le_nhdsSet (left_mem_Icc.2 h₁₂.le))))
  have h₂ := (((hasDerivAt_deriv_effectivePotential hr₁ hU
    (right_mem_Icc.2 h₁₂.le)).hasDerivWithinAt (s := Ioi r₂)).eventually_nhdsGT_lt_of_pos
    (deriv_effectivePotential_pos hr₁ h₁₂ hU hE₂ hlt hd₂)).and
    (hU.filter_mono (nhdsWithin_le_nhds.trans (nhds_le_nhdsSet (right_mem_Icc.2 h₁₂.le))))
  obtain ⟨a, ha, has⟩ := mem_nhdsLT_iff_exists_Ioo_subset.1 h₁
  obtain ⟨b, hb, hbs⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 h₂
  refine ⟨max a 0, b, le_max_right _ _, max_lt ha hr₁, hb, fun r hr ↦ ?_, fun r hr ↦ ?_,
    fun r hr ↦ ?_⟩
  · -- `U` is differentiable on `(a, r₁)`, on `[r₁, r₂]` and on `(r₂, b)`.
    rcases lt_or_ge r r₁ with h | h
    · exact (has ⟨(le_max_left _ _).trans_lt hr.1, h⟩).2
    rcases le_or_gt r r₂ with h' | h'
    · exact hU.self_of_nhdsSet r ⟨h, h'⟩
    · exact (hbs ⟨h', hr.2⟩).2
  · have h : -effectivePotential m ℓ U r < -effectivePotential m ℓ U r₁ :=
      (has ⟨(le_max_left _ _).trans_lt hr.1, hr.2⟩).1
    linarith
  · have h : effectivePotential m ℓ U r₂ < effectivePotential m ℓ U r := (hbs hr).1
    linarith

include hm hr₁ h₁₂ hU hlt hd₁ hd₂ in
/-- The time quadrature converges on the well. -/
private theorem intervalIntegrable_div_absRadialMomentum_well :
    IntervalIntegrable (fun r ↦ m / absRadialMomentum m U ℓ E r) volume r₁ r₂ :=
  intervalIntegrable_div_absRadialMomentum hm hr₁ h₁₂
    (fun r hr ↦ (hU.self_of_nhdsSet r hr).continuousAt.continuousWithinAt) hlt
    (fun _ ↦ ⟨_, hd₁, (hasDerivAt_deriv_effectivePotential hr₁ hU
      (left_mem_Icc.2 h₁₂.le)).hasDerivWithinAt⟩)
    (fun _ ↦ ⟨_, hd₂, (hasDerivAt_deriv_effectivePotential hr₁ hU
      (right_mem_Icc.2 h₁₂.le)).hasDerivWithinAt⟩)

include hm hr₁ h₁₂ hU hlt hd₁ hd₂ in
/-- The radial period of the well is positive. -/
private theorem radialPeriod_pos_well : 0 < radialPeriod m U ℓ E r₁ r₂ :=
  radialPeriod_pos hm hr₁ h₁₂
    (fun r hr ↦ (hU.self_of_nhdsSet r hr).continuousAt.continuousWithinAt) hlt
    (fun _ ↦ ⟨_, hd₁, (hasDerivAt_deriv_effectivePotential hr₁ hU
      (left_mem_Icc.2 h₁₂.le)).hasDerivWithinAt⟩)
    (fun _ ↦ ⟨_, hd₂, (hasDerivAt_deriv_effectivePotential hr₁ hU
      (right_mem_Icc.2 h₁₂.le)).hasDerivWithinAt⟩)

include hm hr₁ h₁₂ hU hlt hd₁ hd₂ in
/-- **The time to reach a radius.** The quadrature `ρ ↦ ∫_{r₁}^{ρ} m dr / |p_r|` is strictly
increasing on the well. -/
private theorem strictMonoOn_integral_div_absRadialMomentum :
    StrictMonoOn (fun ρ ↦ ∫ r in r₁..ρ, m / absRadialMomentum m U ℓ E r) (Icc r₁ r₂) :=
  TauCeti.intervalIntegral.strictMonoOn_primitive_of_pos
    (fun _ hr ↦ div_absRadialMomentum_pos hm (hlt _ hr))
    (intervalIntegrable_div_absRadialMomentum_well hm hr₁ h₁₂ hU hlt hd₁ hd₂)

/-! ### Motions in the well -/

variable {γ : ℝ → ℝ × ℝ} {t₀ : ℝ}

/-- The hypotheses shared by the lemmas on motions in the well: `0 < r₁ < r₂` are simple turning
points of energy `E` for a potential `U` differentiable near `[r₁, r₂]`, with `U_ℓ < E` in
between, and `γ` is an integral curve of the reduced Hamiltonian vector field defined at all times,
with energy `E` and radius in `[r₁, r₂]` at the time `t₀`. -/
private structure WellMotion (m ℓ E r₁ r₂ : ℝ) (U : ℝ → ℝ) (γ : ℝ → ℝ × ℝ) (t₀ : ℝ) : Prop where
  hm : 0 < m
  hr₁ : 0 < r₁
  h₁₂ : r₁ < r₂
  hU : ∀ᶠ r in 𝓝ˢ (Icc r₁ r₂), DifferentiableAt ℝ U r
  hE₁ : effectivePotential m ℓ U r₁ = E
  hE₂ : effectivePotential m ℓ U r₂ = E
  hlt : ∀ r ∈ Ioo r₁ r₂, effectivePotential m ℓ U r < E
  hd₁ : deriv (effectivePotential m ℓ U) r₁ ≠ 0
  hd₂ : deriv (effectivePotential m ℓ U) r₂ ≠ 0
  hγ : ∀ t, HasDerivAt γ ((stdSymplecticForm (V := ℝ)).hamiltonianVectorField
    (centralForceHamiltonian m (effectivePotential m ℓ U)) (γ t)) t
  h₀ : (γ t₀).1 ∈ Icc r₁ r₂
  hE : centralForceHamiltonian m (effectivePotential m ℓ U) (γ t₀) = E

/-- A motion of energy `E` in the well stays in the well, with energy `E`, for times near `t`. -/
private theorem WellMotion.eventually_mem_Icc_and_eq (hM : WellMotion m ℓ E r₁ r₂ U γ t₀)
    {t : ℝ} (ht : (γ t).1 ∈ Icc r₁ r₂)
    (hEt : centralForceHamiltonian m (effectivePotential m ℓ U) (γ t) = E) :
    ∀ᶠ s in 𝓝 t, (γ s).1 ∈ Icc r₁ r₂ ∧
      centralForceHamiltonian m (effectivePotential m ℓ U) (γ s) = E := by
  obtain ⟨a, b, ha0, har, hrb, hdiff, hla, hlb⟩ :=
    exists_lt_effectivePotential hM.hr₁ hM.h₁₂ hM.hU hM.hE₁ hM.hE₂ hM.hlt hM.hd₁ hM.hd₂
  -- For times near `t` the radius stays in `(a, b)`, where `U` is differentiable.
  have hnear : ∀ᶠ s in 𝓝 t, (γ s).1 ∈ Ioo a b :=
    (hM.hγ t).continuousAt.fst.eventually
      (Ioo_mem_nhds (har.trans_le ht.1) (ht.2.trans_lt hrb))
  obtain ⟨l, u, hlu, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.1 hnear
  filter_upwards [Ioo_mem_nhds hlu.1 hlu.2] with s hs
  -- The energy is conserved on the interval between `t` and `s`.
  have hIcc : Icc (min t s) (max t s) ⊆ Ioo l u :=
    (ordConnected_Ioo).out (min_rec' (· ∈ Ioo l u) hlu hs) (max_rec' (· ∈ Ioo l u) hlu hs)
  have hpos (w : ℝ) (hw : w ∈ Icc (min t s) (max t s)) : 0 < (γ w).1 :=
    ha0.trans_lt (hsub (hIcc hw)).1
  have hcons := centralForceHamiltonian_effectivePotential_eq_of_hasDerivAt
    (fun w _ ↦ hM.hγ w) hpos fun w hw ↦ hdiff _ (hsub (hIcc hw))
  have hEs : centralForceHamiltonian m (effectivePotential m ℓ U) (γ s) = E := by
    rw [hcons s ⟨min_le_right _ _, le_max_right _ _⟩, ← hcons t ⟨min_le_left _ _, le_max_left _ _⟩,
      hEt]
  refine ⟨?_, hEs⟩
  -- At energy `E` the effective potential is at most `E`, so the radius cannot leave the well.
  have hle : effectivePotential m ℓ U (γ s).1 ≤ E := by
    rw [← hEs, ← Prod.mk.eta (p := γ s), reducedHamiltonian_eq (hpos s ⟨min_le_right _ _,
      le_max_right _ _⟩).le]
    exact le_add_of_nonneg_left (div_nonneg (sq_nonneg _) (by linarith [hM.hm]))
  have hab := hsub hs
  refine ⟨not_lt.1 fun h ↦ ?_, not_lt.1 fun h ↦ ?_⟩
  · exact (hla _ ⟨hab.1, h⟩).not_ge hle
  · exact (hlb _ ⟨h, hab.2⟩).not_ge hle

/-- A motion of energy `E` defined at all times and starting in the well stays in the well, with
energy `E`. -/
private theorem WellMotion.mem_Icc_and_eq (hM : WellMotion m ℓ E r₁ r₂ U γ t₀) (t : ℝ) :
    (γ t).1 ∈ Icc r₁ r₂ ∧ centralForceHamiltonian m (effectivePotential m ℓ U) (γ t) = E := by
  set S := {s | (γ s).1 ∈ Icc r₁ r₂ ∧
    centralForceHamiltonian m (effectivePotential m ℓ U) (γ s) = E}
  have hopen : IsOpen S := isOpen_iff_mem_nhds.2 fun s hs ↦
    hM.eventually_mem_Icc_and_eq hs.1 hs.2
  have hclosed : IsClosed S := by
    refine isOpen_compl_iff.1 (isOpen_iff_mem_nhds.2 fun s hs ↦ ?_)
    by_cases hs₁ : (γ s).1 ∈ Icc r₁ r₂
    · -- The energy is continuous at `γ s`, and differs from `E` there.
      have hs₂ : centralForceHamiltonian m (effectivePotential m ℓ U) (γ s) ≠ E :=
        fun h ↦ hs ⟨hs₁, h⟩
      have hpos : 0 < (γ s).1 := hM.hr₁.trans_le hs₁.1
      have hHc : ContinuousAt (centralForceHamiltonian m (effectivePotential m ℓ U)) (γ s) := by
        rw [← Prod.mk.eta (p := γ s)]
        exact (differentiableAt_centralForceHamiltonian_effectivePotential hpos
          (hM.hU.self_of_nhdsSet _ hs₁) _).continuousAt
      filter_upwards [(hHc.comp (hM.hγ s).continuousAt).eventually_ne hs₂] with w hw hwS
      exact hw hwS.2
    · filter_upwards [(hM.hγ s).continuousAt.fst.eventually
        (isClosed_Icc.isOpen_compl.mem_nhds hs₁)] with w hw hwS
      exact hw hwS.1
  exact ((IsClopen.eq_univ ⟨hclosed, hopen⟩ ⟨t₀, hM.h₀, hM.hE⟩).symm ▸ mem_univ t : t ∈ S)

/-- A motion of energy `E` defined at all times and starting in the well stays in the well. -/
private theorem WellMotion.fst_mem_Icc (hM : WellMotion m ℓ E r₁ r₂ U γ t₀)
    (t : ℝ) : (γ t).1 ∈ Icc r₁ r₂ :=
  (hM.mem_Icc_and_eq t).1

/-- Along the motion, the radius is positive. -/
private theorem WellMotion.fst_pos (hM : WellMotion m ℓ E r₁ r₂ U γ t₀) (t : ℝ) : 0 < (γ t).1 :=
  hM.hr₁.trans_le (hM.fst_mem_Icc t).1

/-- Along the motion, the potential is differentiable at the radius. -/
private theorem WellMotion.differentiableAt (hM : WellMotion m ℓ E r₁ r₂ U γ t₀) (t : ℝ) :
    DifferentiableAt ℝ U (γ t).1 :=
  hM.hU.self_of_nhdsSet _ (hM.fst_mem_Icc t)

/-- Along the motion, the radius moves with velocity `m⁻¹ p_r`. -/
private theorem WellMotion.hasDerivAt_radius (hM : WellMotion m ℓ E r₁ r₂ U γ t₀) (t : ℝ) :
    HasDerivAt (fun s ↦ (γ s).1) (m⁻¹ * (γ t).2) t := by
  have hpos := hM.fst_pos t
  exact (hasDerivAt_fst_of_hasDerivAt_hamiltonianVectorField_effectivePotential (hM.hγ t) hpos
    (hM.differentiableAt t)).congr_deriv (div_eq_inv_mul _ _)

/-- Along the motion, the radial momentum moves with velocity `-U_ℓ'(r)`. -/
private theorem WellMotion.hasDerivAt_momentum (hM : WellMotion m ℓ E r₁ r₂ U γ t₀) (t : ℝ) :
    HasDerivAt (fun s ↦ (γ s).2) (-deriv (effectivePotential m ℓ U) (γ t).1) t := by
  have hpos := hM.fst_pos t
  have hUd := hM.differentiableAt t
  refine (hasDerivAt_snd_of_hasDerivAt_hamiltonianVectorField_effectivePotential (hM.hγ t) hpos
    hUd).congr_deriv ?_
  rw [(hasDerivAt_effectivePotential (m := m) (ℓ := ℓ) hUd.hasDerivAt hpos.ne').deriv]
  ring

/-- Along the motion, the radial momentum is continuous. -/
private theorem WellMotion.continuous_momentum (hM : WellMotion m ℓ E r₁ r₂ U γ t₀)
    : Continuous fun s ↦ (γ s).2 :=
  continuous_iff_continuousAt.2 fun t ↦ (hM.hasDerivAt_momentum t).continuousAt

/-- Along the motion, the radial momentum vanishes exactly at the turning points. -/
private theorem WellMotion.momentum_ne_zero_iff (hM : WellMotion m ℓ E r₁ r₂ U γ t₀)
    (t : ℝ) : (γ t).2 ≠ 0 ↔ (γ t).1 ∈ Ioo r₁ r₂ := by
  obtain ⟨hmem, hEt⟩ := hM.mem_Icc_and_eq t
  rw [← Prod.mk.eta (p := γ t), reducedHamiltonian_eq (hM.hr₁.trans_le hmem.1).le] at hEt
  constructor
  · intro hp
    have hk : 0 < (γ t).2 ^ 2 / (2 * m) := by have := hM.hm; positivity
    refine ⟨lt_of_le_of_ne hmem.1 fun h ↦ ?_, lt_of_le_of_ne hmem.2 fun h ↦ ?_⟩
    · rw [← h, hM.hE₁] at hEt
      linarith
    · rw [h, hM.hE₂] at hEt
      linarith
  · intro hr hp
    rw [hp, zero_pow two_ne_zero, zero_div, zero_add] at hEt
    linarith [hM.hlt _ hr]

/-- Along the motion, the radius stays in `(r₁, r₂)` during a rise with positive radial momentum
followed by a fall with negative radial momentum. -/
private theorem WellMotion.fst_mem_Ioo (hM : WellMotion m ℓ E r₁ r₂ U γ t₀)
    {t₁ t₂ t₃ u : ℝ} (hpos : ∀ u ∈ Ioo t₁ t₂, 0 < (γ u).2)
    (hneg : ∀ u ∈ Ioo t₂ t₃, (γ u).2 < 0) (hu : u ∈ Ioo t₁ t₂ ∨ u ∈ Ioo t₂ t₃) :
    (γ u).1 ∈ Ioo r₁ r₂ :=
  (hM.momentum_ne_zero_iff u).1 <| hu.elim (fun hu ↦ (hpos u hu).ne') fun hu ↦ (hneg u hu).ne

/-- Along the motion, the absolute radial momentum is `|p_r|(r)`. -/
private theorem WellMotion.abs_momentum (hM : WellMotion m ℓ E r₁ r₂ U γ t₀)
    (t : ℝ) : |(γ t).2| = absRadialMomentum m U ℓ E (γ t).1 := by
  obtain ⟨hmem, hEt⟩ := hM.mem_Icc_and_eq t
  rw [← Prod.mk.eta (p := γ t)] at hEt
  exact (absRadialMomentum_eq_abs hM.hm.ne' (hM.hr₁.trans_le hmem.1) hEt).symm

/-- **Time along a rising stretch.** While the radial momentum is positive on `(s, t)`, the elapsed
time is the quadrature `t - s = ∫_{r(s)}^{r(t)} m dr / |p_r|`. -/
private theorem WellMotion.sub_eq_integral_of_pos (hM : WellMotion m ℓ E r₁ r₂ U γ t₀)
    {s t : ℝ} (hst : s ≤ t) (hp : ∀ u ∈ Ioo s t, 0 < (γ u).2) :
    t - s = ∫ r in (γ s).1..(γ t).1, m / absRadialMomentum m U ℓ E r := by
  have hmem := hM.mem_Icc_and_eq
  have hmono := strictMonoOn_Icc_of_forall_hasDerivAt_mul (inv_pos.2 hM.hm)
    (fun u _ ↦ hM.hasDerivAt_radius u) hp
  exact sub_eq_integral_div_absRadialMomentum hM.hm hst (fun u _ ↦ hM.hγ u)
    (fun u _ ↦ hM.fst_pos u) (fun u _ ↦ hM.differentiableAt u)
    (hmem s).2 (fun r hr ↦ hM.hlt r ⟨(hmem s).1.1.trans_lt hr.1, hr.2.trans_le (hmem t).1.2⟩)
    (Or.inl ⟨rfl, rfl⟩) fun u hu ↦ ⟨hmono ⟨le_rfl, hst⟩ (Ioo_subset_Icc_self hu) hu.1,
      hmono (Ioo_subset_Icc_self hu) ⟨hst, le_rfl⟩ hu.2⟩

/-- **Time along a falling stretch.** While the radial momentum is negative on `(s, t)`, the
elapsed time is the quadrature `t - s = ∫_{r(t)}^{r(s)} m dr / |p_r|`. -/
private theorem WellMotion.sub_eq_integral_of_neg (hM : WellMotion m ℓ E r₁ r₂ U γ t₀)
    {s t : ℝ} (hst : s ≤ t) (hp : ∀ u ∈ Ioo s t, (γ u).2 < 0) :
    t - s = ∫ r in (γ t).1..(γ s).1, m / absRadialMomentum m U ℓ E r := by
  have hmem := hM.mem_Icc_and_eq
  have hanti := strictAntiOn_Icc_of_forall_hasDerivAt_mul (inv_pos.2 hM.hm)
    (fun u _ ↦ hM.hasDerivAt_radius u) hp
  exact sub_eq_integral_div_absRadialMomentum hM.hm hst (fun u _ ↦ hM.hγ u)
    (fun u _ ↦ hM.fst_pos u) (fun u _ ↦ hM.differentiableAt u)
    (hmem s).2 (fun r hr ↦ hM.hlt r ⟨(hmem t).1.1.trans_lt hr.1, hr.2.trans_le (hmem s).1.2⟩)
    (Or.inr ⟨rfl, rfl⟩) fun u hu ↦ ⟨hanti (Ioo_subset_Icc_self hu) ⟨hst, le_rfl⟩ hu.2,
      hanti ⟨le_rfl, hst⟩ (Ioo_subset_Icc_self hu) hu.1⟩

/-- **Passages are short.** During a time interval on which the radial momentum does not vanish,
the radius runs monotonically inside the well, so the interval lasts at most the time quadrature
`∫_{r₁}^{r₂} m dr / |p_r|`. -/
private theorem WellMotion.sub_le_integral (hM : WellMotion m ℓ E r₁ r₂ U γ t₀)
    {s t : ℝ} (hst : s ≤ t) (hp : ∀ u ∈ Ioo s t, (γ u).2 ≠ 0) :
    t - s ≤ ∫ r in r₁..r₂, m / absRadialMomentum m U ℓ E r :=
  sub_le_integral_of_forall_hasDerivAt_mul (inv_pos.2 hM.hm) hM.hasDerivAt_radius
    hM.continuous_momentum hM.fst_mem_Icc
    (intervalIntegrable_div_absRadialMomentum_well hM.hm hM.hr₁ hM.h₁₂ hM.hU hM.hlt hM.hd₁ hM.hd₂)
    (fun _ _ ↦ div_nonneg hM.hm.le (absRadialMomentum_nonneg _ _ _ _ _))
    (fun _ _ ↦ hM.sub_eq_integral_of_pos) (fun _ _ ↦ hM.sub_eq_integral_of_neg) hst hp

/-- At the inner turning point the radial momentum has positive derivative `-U_ℓ'(r₁)`. -/
private theorem WellMotion.exists_hasDerivAt_momentum_pos (hM : WellMotion m ℓ E r₁ r₂ U γ t₀)
    {t : ℝ} (h : (γ t).1 = r₁) :
    ∃ d, 0 < d ∧ HasDerivAt (fun s ↦ (γ s).2) d t :=
  ⟨_, by
    rw [h, neg_pos]
    exact deriv_effectivePotential_neg hM.hr₁ hM.h₁₂ hM.hU hM.hE₁ hM.hlt hM.hd₁,
    hM.hasDerivAt_momentum t⟩

/-- At the outer turning point the radial momentum has negative derivative `-U_ℓ'(r₂)`. -/
private theorem WellMotion.exists_hasDerivAt_momentum_neg (hM : WellMotion m ℓ E r₁ r₂ U γ t₀)
    {t : ℝ} (h : (γ t).1 = r₂) :
    ∃ d, d < 0 ∧ HasDerivAt (fun s ↦ (γ s).2) d t :=
  ⟨_, by
    rw [h, neg_lt_zero]
    exact deriv_effectivePotential_pos hM.hr₁ hM.h₁₂ hM.hU hM.hE₂ hM.hlt hM.hd₂,
    hM.hasDerivAt_momentum t⟩

/-- From the inner turning point the radius rises to the outer one, with positive radial momentum
in between. -/
private theorem WellMotion.exists_outer (hM : WellMotion m ℓ E r₁ r₂ U γ t₀)
    {t₁ : ℝ} (h₁ : (γ t₁).1 = r₁) :
    ∃ t₂, t₁ < t₂ ∧ (γ t₂).1 = r₂ ∧ ∀ u ∈ Ioo t₁ t₂, 0 < (γ u).2 :=
  exists_gt_eq_and_forall_pos_of_forall_hasDerivAt_mul (inv_pos.2 hM.hm) hM.hasDerivAt_radius
    hM.continuous_momentum hM.fst_mem_Icc hM.momentum_ne_zero_iff
    (fun _ ↦ hM.exists_hasDerivAt_momentum_pos) (fun _ _ ↦ hM.sub_le_integral) h₁

/-- From the outer turning point the radius falls to the inner one, with negative radial momentum
in between. -/
private theorem WellMotion.exists_inner (hM : WellMotion m ℓ E r₁ r₂ U γ t₀)
    {t₂ : ℝ} (h₂ : (γ t₂).1 = r₂) :
    ∃ t₃, t₂ < t₃ ∧ (γ t₃).1 = r₁ ∧ ∀ u ∈ Ioo t₂ t₃, (γ u).2 < 0 :=
  exists_gt_eq_and_forall_neg_of_forall_hasDerivAt_mul (inv_pos.2 hM.hm) hM.hasDerivAt_radius
    hM.continuous_momentum hM.fst_mem_Icc hM.momentum_ne_zero_iff
    (fun _ ↦ hM.exists_hasDerivAt_momentum_neg) (fun _ _ ↦ hM.sub_le_integral) h₂

/-- After any time `a`, the radius reaches the inner turning point within the time
`1 + 2 ∫_{r₁}^{r₂} m dr / |p_r|`. -/
private theorem WellMotion.exists_mem_Ioo_fst_eq (hM : WellMotion m ℓ E r₁ r₂ U γ t₀) (a : ℝ) :
    ∃ s ∈ Ioo a (a + 1 + 2 * ∫ r in r₁..r₂, m / absRadialMomentum m U ℓ E r), (γ s).1 = r₁ :=
  exists_mem_Ioo_eq_of_forall_hasDerivAt_mul (inv_pos.2 hM.hm) hM.hasDerivAt_radius
    hM.continuous_momentum hM.fst_mem_Icc hM.momentum_ne_zero_iff
    (fun _ ↦ hM.exists_hasDerivAt_momentum_neg) (fun _ _ ↦ hM.sub_le_integral) a

/-- There is a time at which the radius is the inner turning point `r₁`. -/
private theorem WellMotion.exists_fst_eq (hM : WellMotion m ℓ E r₁ r₂ U γ t₀) : ∃ t, (γ t).1 = r₁ :=
  let ⟨s, _, hs⟩ := hM.exists_mem_Ioo_fst_eq 0
  ⟨s, hs⟩

/-- **One radial oscillation.** If the radius is `r₁` at time `t₁`, it rises to `r₂` at a time `t₂`
with `t₁ < t₂ < t₁ + T` and falls back to `r₁` at time `t₁ + T`, where `T` is the radial period. -/
private theorem WellMotion.exists_oscillation (hM : WellMotion m ℓ E r₁ r₂ U γ t₀)
    {t₁ : ℝ} (h₁ : (γ t₁).1 = r₁) :
    ∃ t₂ ∈ Ioo t₁ (t₁ + radialPeriod m U ℓ E r₁ r₂), (γ t₂).1 = r₂ ∧
      (γ (t₁ + radialPeriod m U ℓ E r₁ r₂)).1 = r₁ ∧ (∀ u ∈ Ioo t₁ t₂, 0 < (γ u).2) ∧
      ∀ u ∈ Ioo t₂ (t₁ + radialPeriod m U ℓ E r₁ r₂), (γ u).2 < 0 := by
  obtain ⟨t₂, h₁₂', h₂, hpos⟩ := hM.exists_outer h₁
  obtain ⟨t₃, h₂₃, h₃, hneg⟩ := hM.exists_inner h₂
  have hmem (u : ℝ) := hM.fst_mem_Ioo hpos hneg (u := u)
  have hT := sub_eq_radialPeriod hM.hm h₁₂'.le h₂₃.le (fun u _ ↦ hM.hγ u)
    (fun u _ ↦ hM.fst_pos u) (fun u _ ↦ hM.differentiableAt u)
    (hM.mem_Icc_and_eq t₁).2 hM.hlt (Or.inl ⟨h₁, h₂⟩)
    (h₃.trans h₁.symm) (fun u hu ↦ hmem u (Or.inl hu)) fun u hu ↦ hmem u (Or.inr hu)
  obtain rfl : t₃ = t₁ + radialPeriod m U ℓ E r₁ r₂ := by linarith
  exact ⟨t₂, ⟨h₁₂', h₂₃⟩, h₂, h₃, hpos, hneg⟩

/-- **A rising stretch from the inner turning point.** If the radius is `r₁` at time `a` and the
radial momentum is positive on `(a, b)`, then at every time `u ∈ [a, b]` the elapsed time is the
quadrature `u - a = ∫_{r₁}^{r(u)} m dr / |p_r|`, and the radial momentum is nonnegative. -/
private theorem WellMotion.sub_eq_integral_and_nonneg (hM : WellMotion m ℓ E r₁ r₂ U γ t₀)
    {a b u : ℝ} (ha : (γ a).1 = r₁)
    (hp : ∀ w ∈ Ioo a b, 0 < (γ w).2) (hu : u ∈ Icc a b) :
    u - a = (∫ r in r₁..(γ u).1, m / absRadialMomentum m U ℓ E r) ∧ 0 ≤ (γ u).2 := by
  refine ⟨?_, ?_⟩
  · rw [hM.sub_eq_integral_of_pos hu.1 (fun w hw ↦ hp w ⟨hw.1, hw.2.trans_le hu.2⟩), ha]
  rcases hu.1.eq_or_lt with rfl | h₁
  · exact (eq_zero_of_eq_or_eq_of_forall_ne_zero_iff hM.momentum_ne_zero_iff (Or.inl ha)).ge
  rcases hu.2.eq_or_lt with rfl | h₂
  · -- At the end of the stretch, the momentum is a limit of positive values.
    exact ge_of_tendsto (((hM.hasDerivAt_momentum _).continuousAt.tendsto).mono_left
      nhdsWithin_le_nhds) (eventually_of_mem (Ioo_mem_nhdsLT h₁) fun w hw ↦ (hp w hw).le)
  · exact (hp u ⟨h₁, h₂⟩).le

/-- **A falling stretch to the inner turning point.** If the radius is `r₁` at time `b` and the
radial momentum is negative on `(a, b)`, then at every time `u ∈ [a, b]` the remaining time is the
quadrature `b - u = ∫_{r₁}^{r(u)} m dr / |p_r|`, and the radial momentum is nonpositive. -/
private theorem WellMotion.sub_eq_integral_and_nonpos (hM : WellMotion m ℓ E r₁ r₂ U γ t₀)
    {a b u : ℝ} (hb : (γ b).1 = r₁)
    (hp : ∀ w ∈ Ioo a b, (γ w).2 < 0) (hu : u ∈ Icc a b) :
    b - u = (∫ r in r₁..(γ u).1, m / absRadialMomentum m U ℓ E r) ∧ (γ u).2 ≤ 0 := by
  refine ⟨?_, ?_⟩
  · rw [hM.sub_eq_integral_of_neg hu.2 (fun w hw ↦ hp w ⟨hu.1.trans_lt hw.1, hw.2⟩), hb]
  rcases hu.2.eq_or_lt with rfl | h₂
  · exact (eq_zero_of_eq_or_eq_of_forall_ne_zero_iff hM.momentum_ne_zero_iff (Or.inl hb)).le
  rcases hu.1.eq_or_lt with rfl | h₁
  · -- At the start of the stretch, the momentum is a limit of negative values.
    exact le_of_tendsto (((hM.hasDerivAt_momentum _).continuousAt.tendsto).mono_left
      nhdsWithin_le_nhds) (eventually_of_mem (Ioo_mem_nhdsGT h₂) fun w hw ↦ (hp w hw).le)
  · exact (hp u ⟨h₁, h₂⟩).le

/-- After a passage through the inner turning point at time `s`, the motion repeats itself one
radial period later, at every time of the following radial period. -/
private theorem WellMotion.apply_add_radialPeriod_of_fst_eq (hM : WellMotion m ℓ E r₁ r₂ U γ t₀)
    {s t : ℝ} (hs : (γ s).1 = r₁)
    (ht : t ∈ Icc s (s + radialPeriod m U ℓ E r₁ r₂)) :
    γ (t + radialPeriod m U ℓ E r₁ r₂) = γ t := by
  set T := radialPeriod m U ℓ E r₁ r₂
  have hmem := hM.fst_mem_Icc
  -- The time to reach a radius from `r₁` determines the radius.
  have hF := (strictMonoOn_integral_div_absRadialMomentum hM.hm hM.hr₁ hM.h₁₂ hM.hU hM.hlt hM.hd₁
    hM.hd₂).injOn
  have hrise {a b u : ℝ} (ha : (γ a).1 = r₁) (hp : ∀ w ∈ Ioo a b, 0 < (γ w).2)
      (hu : u ∈ Icc a b) :=
    hM.sub_eq_integral_and_nonneg ha hp hu
  have hfall {a b u : ℝ} (hb : (γ b).1 = r₁) (hp : ∀ w ∈ Ioo a b, (γ w).2 < 0)
      (hu : u ∈ Icc a b) :=
    hM.sub_eq_integral_and_nonpos hb hp hu
  -- Two consecutive radial oscillations, the second one starting at `s + T`.
  obtain ⟨t₂, ⟨hs₂, -⟩, h₂, hT, hpos, hneg⟩ := hM.exists_oscillation hs
  obtain ⟨t₄, ⟨hT₄, -⟩, h₄, hTT, hpos', hneg'⟩ := hM.exists_oscillation hT
  -- Both rises take the time `∫_{r₁}^{r₂} m dr / |p_r|`.
  have ht₄ : t₄ = t₂ + T := by
    have e₁ := (hrise hs hpos (right_mem_Icc.2 hs₂.le)).1
    have e₂ := (hrise hT hpos' (right_mem_Icc.2 hT₄.le)).1
    rw [h₂] at e₁
    rw [h₄] at e₂
    linarith
  -- The radii at `t` and `t + T` have the same quadrature, and the momenta the same sign.
  have hr : (γ (t + T)).1 = (γ t).1 ∧ ((0 ≤ (γ t).2 ∧ 0 ≤ (γ (t + T)).2) ∨
      ((γ t).2 ≤ 0 ∧ (γ (t + T)).2 ≤ 0)) := by
    rcases le_total t t₂ with htt | htt
    · have e₁ := hrise hs hpos ⟨ht.1, htt⟩
      have e₂ := hrise hT hpos' (u := t + T) ⟨by linarith [ht.1], by linarith⟩
      exact ⟨hF (hmem _) (hmem _) (by dsimp only; linarith [e₁.1, e₂.1]), Or.inl ⟨e₁.2, e₂.2⟩⟩
    · have e₁ := hfall hT hneg ⟨htt, ht.2⟩
      have e₂ := hfall hTT hneg' (u := t + T) ⟨by linarith, by linarith [ht.2]⟩
      exact ⟨hF (hmem _) (hmem _) (by dsimp only; linarith [e₁.1, e₂.1]), Or.inr ⟨e₁.2, e₂.2⟩⟩
  -- The absolute radial momentum is a function of the radius.
  have habs : |(γ (t + T)).2| = |(γ t).2| := by
    rw [hM.abs_momentum, hM.abs_momentum, hr.1]
  refine Prod.ext hr.1 ?_
  rcases hr.2 with ⟨h, h'⟩ | ⟨h, h'⟩
  · rwa [abs_of_nonneg h, abs_of_nonneg h'] at habs
  · rw [abs_of_nonpos h, abs_of_nonpos h'] at habs
    linarith

/-- The motion is periodic, with period the radial period. -/
private theorem WellMotion.periodic (hM : WellMotion m ℓ E r₁ r₂ U γ t₀)
    : Periodic γ (radialPeriod m U ℓ E r₁ r₂) := by
  intro t
  set T := radialPeriod m U ℓ E r₁ r₂
  have hT : 0 < T := radialPeriod_pos_well hM.hm hM.hr₁ hM.h₁₂ hM.hU hM.hlt hM.hd₁ hM.hd₂
  -- A passage through the inner turning point before `t`, and its translates by multiples of `T`.
  obtain ⟨s, hs, hs₁⟩ :=
    hM.exists_mem_Ioo_fst_eq (t - (1 + 2 * ∫ r in r₁..r₂, m / absRadialMomentum m U ℓ E r))
  have hst : s ≤ t := by linarith [hs.2]
  have hiter (n : ℕ) : (γ (s + n * T)).1 = r₁ := by
    induction n with
    | zero => simpa using hs₁
    | succ n ih =>
      obtain ⟨-, -, -, h, -⟩ := hM.exists_oscillation ih
      rwa [Nat.cast_succ, add_one_mul, ← add_assoc]
  -- The last such passage `s + n T` before `t` lies within one period of `t`.
  set n := ⌊(t - s) / T⌋₊
  have h₁ : (n : ℝ) * T ≤ t - s :=
    (le_div_iff₀ hT).1 (Nat.floor_le (div_nonneg (sub_nonneg.2 hst) hT.le))
  have h₂ : t - s < (n + 1) * T := (div_lt_iff₀ hT).1 (Nat.lt_floor_add_one _)
  exact hM.apply_add_radialPeriod_of_fst_eq (hiter n) ⟨by linarith, by linarith⟩

/-- If the polar angle satisfies `θ' = ℓ / (m r²)`, then during every radial period the angle
advances by twice the apsidal angle. -/
private theorem WellMotion.sub_eq_two_mul_apsidalAngle (hM : WellMotion m ℓ E r₁ r₂ U γ t₀)
    {θ : ℝ → ℝ}
    (hθ : ∀ t, HasDerivAt θ (ℓ / (m * (γ t).1 ^ 2)) t) (t : ℝ) :
    θ (t + radialPeriod m U ℓ E r₁ r₂) - θ t = 2 * apsidalAngle m U ℓ E r₁ r₂ := by
  set T := radialPeriod m U ℓ E r₁ r₂
  -- The advance `θ(u + T) - θ(u)` has zero derivative, since the radius is `T`-periodic.
  have hd (u : ℝ) : HasDerivAt (fun u ↦ θ (u + T) - θ u) 0 u := by
    have h := ((hθ (u + T)).comp_add_const u T).sub (hθ u)
    rwa [hM.periodic u, sub_self] at h
  have hconst := is_const_of_deriv_eq_zero (fun u ↦ (hd u).differentiableAt) fun u ↦ (hd u).deriv
  -- At a passage through the inner turning point it is twice the apsidal angle.
  obtain ⟨s, hs⟩ := hM.exists_fst_eq
  obtain ⟨t₂, ⟨hs₂, h₂T⟩, h₂, hT, hpos, hneg⟩ := hM.exists_oscillation hs
  have hmem (u : ℝ) := hM.fst_mem_Ioo hpos hneg (u := u)
  rw [hconst t s]
  exact _root_.TauCeti.sub_eq_two_mul_apsidalAngle hM.hm hs₂.le h₂T.le (fun u _ ↦ hM.hγ u)
    (fun u _ ↦ hM.fst_pos u) (fun u _ ↦ hM.differentiableAt u)
    (hM.mem_Icc_and_eq s).2 hM.hlt (Or.inl ⟨hs, h₂⟩) (hT.trans hs.symm)
    (fun u hu ↦ hmem u (Or.inl hu)) (fun u hu ↦ hmem u (Or.inr hu)) fun u _ ↦ hθ u

variable (hγ : ∀ t, HasDerivAt γ ((stdSymplecticForm (V := ℝ)).hamiltonianVectorField
    (centralForceHamiltonian m (effectivePotential m ℓ U)) (γ t)) t)
  (h₀ : (γ t₀).1 ∈ Icc r₁ r₂)
  (hE : centralForceHamiltonian m (effectivePotential m ℓ U) (γ t₀) = E)

include hm hr₁ h₁₂ hU hE₁ hE₂ hlt hd₁ hd₂ hγ h₀ hE

/-- **Confinement to the potential well.** Let `0 < r₁ < r₂` be simple turning points of energy
`E` for a potential `U` differentiable near `[r₁, r₂]`, with `U_ℓ < E` in between. A radial motion
of energy `E` defined at all times and with radius in `[r₁, r₂]` at one time has radius in
`[r₁, r₂]` at all times. -/
theorem mem_Icc_of_forall_hasDerivAt_effectivePotential (t : ℝ) : (γ t).1 ∈ Icc r₁ r₂ :=
  WellMotion.fst_mem_Icc ⟨hm, hr₁, h₁₂, hU, hE₁, hE₂, hlt, hd₁, hd₂, hγ, h₀, hE⟩ t

/-- **The motion reaches the inner turning point.** Under the hypotheses of
`TauCeti.mem_Icc_of_forall_hasDerivAt_effectivePotential`, there is a time at which the radius is
the inner turning point `r₁`. -/
theorem exists_fst_eq_of_forall_hasDerivAt_effectivePotential : ∃ t, (γ t).1 = r₁ :=
  WellMotion.exists_fst_eq ⟨hm, hr₁, h₁₂, hU, hE₁, hE₂, hlt, hd₁, hd₂, hγ, h₀, hE⟩

/-- **One radial oscillation.** Under the hypotheses of
`TauCeti.mem_Icc_of_forall_hasDerivAt_effectivePotential`, let the radius be the inner turning
point `r₁` at time `t₁`. Then it rises to the outer turning point `r₂` at a time `t₂` with
`t₁ < t₂ < t₁ + T`, with positive radial momentum in between, and falls back to `r₁` at time
`t₁ + T`, with negative radial momentum in between, where `T` is the radial period. -/
theorem exists_mem_Ioo_fst_eq_of_forall_hasDerivAt_effectivePotential {t₁ : ℝ}
    (h₁ : (γ t₁).1 = r₁) :
    ∃ t₂ ∈ Ioo t₁ (t₁ + radialPeriod m U ℓ E r₁ r₂), (γ t₂).1 = r₂ ∧
      (γ (t₁ + radialPeriod m U ℓ E r₁ r₂)).1 = r₁ ∧ (∀ u ∈ Ioo t₁ t₂, 0 < (γ u).2) ∧
      ∀ u ∈ Ioo t₂ (t₁ + radialPeriod m U ℓ E r₁ r₂), (γ u).2 < 0 :=
  WellMotion.exists_oscillation ⟨hm, hr₁, h₁₂, hU, hE₁, hE₂, hlt, hd₁, hd₂, hγ, h₀, hE⟩ h₁

/-- **The radial motion in a potential well is periodic.** Let `0 < r₁ < r₂` be simple turning
points of energy `E` for a potential `U` differentiable near `[r₁, r₂]`: `U_ℓ(r₁) = U_ℓ(r₂) = E`,
`U_ℓ'(rᵢ) ≠ 0` and `U_ℓ < E` in between. Then every integral curve of the reduced Hamiltonian vector
field defined at all times, with energy `E` and radius in `[r₁, r₂]` at one time, is periodic, with
period the radial period `T = 2 ∫_{r₁}^{r₂} m dr / |p_r|`. -/
theorem periodic_of_forall_hasDerivAt_effectivePotential :
    Periodic γ (radialPeriod m U ℓ E r₁ r₂) :=
  WellMotion.periodic ⟨hm, hr₁, h₁₂, hU, hE₁, hE₂, hlt, hd₁, hd₂, hγ, h₀, hE⟩

/-- **Precession of the orbit.** Under the hypotheses of
`TauCeti.periodic_of_forall_hasDerivAt_effectivePotential`, let the polar angle satisfy
`θ' = ℓ / (m r²)`. Then during every radial period, starting at any time `t`, the angle advances by
twice the apsidal angle: `θ(t + T) - θ(t) = 2 Δθ`. -/
theorem sub_eq_two_mul_apsidalAngle_of_forall_hasDerivAt_effectivePotential {θ : ℝ → ℝ}
    (hθ : ∀ t, HasDerivAt θ (ℓ / (m * (γ t).1 ^ 2)) t) (t : ℝ) :
    θ (t + radialPeriod m U ℓ E r₁ r₂) - θ t = 2 * apsidalAngle m U ℓ E r₁ r₂ :=
  WellMotion.sub_eq_two_mul_apsidalAngle ⟨hm, hr₁, h₁₂, hU, hE₁, hE₂, hlt, hd₁, hd₂, hγ, h₀, hE⟩
    hθ t

end Well

end TauCeti
