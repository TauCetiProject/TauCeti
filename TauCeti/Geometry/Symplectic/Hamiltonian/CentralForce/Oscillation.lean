/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.CentralForce.TurningPoint

import Mathlib.Analysis.Calculus.Deriv.MeanValue
import TauCeti.Analysis.Calculus.Deriv.Slope
import TauCeti.Topology.Order.IntermediateValue

/-!
# Periodicity of the radial motion in a potential well

A particle of mass `m > 0` with angular momentum `ℓ` in a central potential `U` moves radially
according to the reduced Hamiltonian `H_ℓ(r, p_r) = p_r² / (2m) + U_ℓ(r)`, with effective potential
`U_ℓ(r) = ℓ² / (2 m r²) + U(r)` (`TauCeti.effectivePotential`), and Hamilton's equations
`r' = p_r / m`, `p_r' = -U_ℓ'(r)`. Let `U` be differentiable on the half-line `r > 0`, and let
`0 < r₁ < r₂` be *simple turning points* of energy `E`: `U_ℓ(r₁) = U_ℓ(r₂) = E`, `U_ℓ < E` on
`(r₁, r₂)`, and `U_ℓ'(rᵢ) ≠ 0`. This file shows that every motion of energy `E` defined for all
times and starting in the potential well `[r₁, r₂]` is periodic, with period the radial period

`T = 2 ∫_{r₁}^{r₂} m dr / |p_r| = 2 ∫_{r₁}^{r₂} dr / √((2 / m) (E - U_ℓ(r)))`

(`TauCeti.radialPeriod`), twice the time quadrature between the turning points.

* **Confinement.** Just outside the well the effective potential exceeds `E`, because the turning
  points are simple, and the energy is conserved, so the motion never leaves `[r₁, r₂]`
  (`TauCeti.mem_Icc_of_forall_hasDerivAt_effectivePotential`). Its radial momentum vanishes exactly
  at the turning points.
* **Oscillation.** While `p_r ≠ 0` the radius is monotone, so such a passage lasts at most the
  time quadrature, which converges at simple turning points. At a turning point `p_r = 0` and
  `p_r' = -U_ℓ'(rᵢ) ≠ 0`, so the radial momentum changes sign there. Hence every motion reaches the
  inner turning point (`TauCeti.exists_fst_eq_of_forall_hasDerivAt_effectivePotential`), and from
  there the radius rises to `r₂` and falls back to `r₁` in exactly the time `T`
  (`TauCeti.exists_mem_Ioo_fst_eq_of_forall_hasDerivAt_effectivePotential`).
* **Periodicity.** Along a rising stretch from `r₁` the elapsed time is the quadrature
  `∫_{r₁}^{r} m dr / |p_r|`, a strictly increasing function of the radius `r` reached, and along a
  falling stretch to `r₁` the remaining time is the same function of `r`. So the time since the last
  passage through `r₁` determines the state `(r, p_r)`, and the motion is `T`-periodic
  (`TauCeti.periodic_of_forall_hasDerivAt_effectivePotential`). The potential need only be
  differentiable: no Lipschitz condition on `U'` is assumed.
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

/-- For `U` differentiable on the half-line, the effective potential is differentiable there. -/
private theorem hasDerivAt_deriv_effectivePotential (hU : DifferentiableOn ℝ U (Ioi 0)) {r : ℝ}
    (hr : 0 < r) :
    HasDerivAt (effectivePotential m ℓ U) (deriv (effectivePotential m ℓ U) r) r :=
  (hasDerivAt_effectivePotential (hU.differentiableAt (Ioi_mem_nhds hr)).hasDerivAt
    hr.ne').differentiableAt.hasDerivAt

section Well

variable (hm : 0 < m) (hr₁ : 0 < r₁) (h₁₂ : r₁ < r₂) (hU : DifferentiableOn ℝ U (Ioi 0))
  (hE₁ : effectivePotential m ℓ U r₁ = E) (hE₂ : effectivePotential m ℓ U r₂ = E)
  (hlt : ∀ r ∈ Ioo r₁ r₂, effectivePotential m ℓ U r < E)
  (hd₁ : deriv (effectivePotential m ℓ U) r₁ ≠ 0) (hd₂ : deriv (effectivePotential m ℓ U) r₂ ≠ 0)

include hr₁ h₁₂ hU hE₂ hlt hd₂ in
/-- At the outer turning point the effective potential increases. -/
private theorem deriv_effectivePotential_pos : 0 < deriv (effectivePotential m ℓ U) r₂ := by
  refine lt_of_le_of_ne (not_lt.1 fun hneg ↦ ?_) hd₂.symm
  -- Otherwise `U_ℓ` would exceed `U_ℓ(r₂) = E` just to the left of `r₂`.
  have h := ((hasDerivAt_deriv_effectivePotential hU (hr₁.trans h₁₂)).neg.hasDerivWithinAt
    (s := Iio r₂)).eventually_nhdsLT_lt_of_pos (neg_pos.2 hneg)
  obtain ⟨r, hr, hr'⟩ := (h.and (Ioo_mem_nhdsLT h₁₂)).exists
  simp only [Pi.neg_apply, neg_lt_neg_iff] at hr
  linarith [hlt r hr']

include hr₁ h₁₂ hU hE₁ hlt hd₁ in
/-- At the inner turning point the effective potential decreases. -/
private theorem deriv_effectivePotential_neg : deriv (effectivePotential m ℓ U) r₁ < 0 := by
  refine lt_of_le_of_ne (not_lt.1 fun hpos ↦ ?_) hd₁
  -- Otherwise `U_ℓ` would exceed `U_ℓ(r₁) = E` just to the right of `r₁`.
  have h := ((hasDerivAt_deriv_effectivePotential hU hr₁).hasDerivWithinAt
    (s := Ioi r₁)).eventually_nhdsGT_lt_of_pos hpos
  obtain ⟨r, hr, hr'⟩ := (h.and (Ioo_mem_nhdsGT h₁₂)).exists
  linarith [hlt r hr']

include hr₁ h₁₂ hU hE₁ hE₂ hlt hd₁ hd₂ in
/-- **The well is isolated.** There are radii `0 ≤ a < r₁` and `b > r₂` such that the effective
potential exceeds `E` on `(a, r₁)` and on `(r₂, b)`. -/
private theorem exists_lt_effectivePotential :
    ∃ a b, 0 ≤ a ∧ a < r₁ ∧ r₂ < b ∧ (∀ r ∈ Ioo a r₁, E < effectivePotential m ℓ U r) ∧
      ∀ r ∈ Ioo r₂ b, E < effectivePotential m ℓ U r := by
  have h₁ := ((hasDerivAt_deriv_effectivePotential hU hr₁).neg.hasDerivWithinAt
    (s := Iio r₁)).eventually_nhdsLT_lt_of_pos
    (neg_pos.2 (deriv_effectivePotential_neg hr₁ h₁₂ hU hE₁ hlt hd₁))
  have h₂ := ((hasDerivAt_deriv_effectivePotential hU (hr₁.trans h₁₂)).hasDerivWithinAt
    (s := Ioi r₂)).eventually_nhdsGT_lt_of_pos
    (deriv_effectivePotential_pos hr₁ h₁₂ hU hE₂ hlt hd₂)
  obtain ⟨a, ha, has⟩ := mem_nhdsLT_iff_exists_Ioo_subset.1 h₁
  obtain ⟨b, hb, hbs⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 h₂
  refine ⟨max a 0, b, le_max_right _ _, max_lt ha hr₁, hb, fun r hr ↦ ?_, fun r hr ↦ ?_⟩
  · have h : -effectivePotential m ℓ U r < -effectivePotential m ℓ U r₁ :=
      has ⟨(le_max_left _ _).trans_lt hr.1, hr.2⟩
    linarith
  · have h : effectivePotential m ℓ U r₂ < effectivePotential m ℓ U r := hbs hr
    linarith

include hm hr₁ h₁₂ hU hlt hd₁ hd₂ in
/-- The time quadrature converges on the well. -/
private theorem intervalIntegrable_div_absRadialMomentum_well :
    IntervalIntegrable (fun r ↦ m / absRadialMomentum m U ℓ E r) volume r₁ r₂ :=
  intervalIntegrable_div_absRadialMomentum hm hr₁ h₁₂
    (hU.continuousOn.mono fun _ hr ↦ hr₁.trans_le hr.1) hlt
    (fun _ ↦ ⟨_, hd₁, (hasDerivAt_deriv_effectivePotential hU hr₁).hasDerivWithinAt⟩)
    (fun _ ↦ ⟨_, hd₂, (hasDerivAt_deriv_effectivePotential hU (hr₁.trans h₁₂)).hasDerivWithinAt⟩)

include hm hr₁ h₁₂ hU hlt hd₁ hd₂ in
/-- **The time to reach a radius.** The quadrature `ρ ↦ ∫_{r₁}^{ρ} m dr / |p_r|` is strictly
increasing on the well. -/
private theorem strictMonoOn_integral_div_absRadialMomentum :
    StrictMonoOn (fun ρ ↦ ∫ r in r₁..ρ, m / absRadialMomentum m U ℓ E r) (Icc r₁ r₂) := by
  have hint := intervalIntegrable_div_absRadialMomentum_well hm hr₁ h₁₂ hU hlt hd₁ hd₂
  intro a ha b hb hab
  have hia : IntervalIntegrable (fun r ↦ m / absRadialMomentum m U ℓ E r) volume r₁ a :=
    hint.mono_set (uIcc_subset_uIcc_left (Icc_subset_uIcc ha))
  have hib : IntervalIntegrable (fun r ↦ m / absRadialMomentum m U ℓ E r) volume r₁ b :=
    hint.mono_set (uIcc_subset_uIcc_left (Icc_subset_uIcc hb))
  rw [← sub_pos, integral_interval_sub_left hib hia]
  refine intervalIntegral_pos_of_pos_on ((hia.symm.trans hib)) (fun r hr ↦ ?_) hab
  have hr' : r ∈ Ioo r₁ r₂ := ⟨ha.1.trans_lt hr.1, hr.2.trans_le hb.2⟩
  rw [absRadialMomentum_eq_sqrt hm.ne']
  exact div_pos hm (Real.sqrt_pos.2 (mul_pos (by positivity) (sub_pos.2 (hlt r hr'))))

/-! ### Motions in the well -/

variable {γ : ℝ → ℝ × ℝ} {t₀ : ℝ}
  (hγ : ∀ t, HasDerivAt γ ((stdSymplecticForm (V := ℝ)).hamiltonianVectorField
    (centralForceHamiltonian m (effectivePotential m ℓ U)) (γ t)) t)
  (h₀ : (γ t₀).1 ∈ Icc r₁ r₂)
  (hE : centralForceHamiltonian m (effectivePotential m ℓ U) (γ t₀) = E)

include hm hr₁ h₁₂ hU hE₁ hE₂ hlt hd₁ hd₂ hγ in
/-- A motion of energy `E` in the well stays in the well, with energy `E`, for times near `t`. -/
private theorem eventually_mem_Icc_and_eq {t : ℝ} (ht : (γ t).1 ∈ Icc r₁ r₂)
    (hEt : centralForceHamiltonian m (effectivePotential m ℓ U) (γ t) = E) :
    ∀ᶠ s in 𝓝 t, (γ s).1 ∈ Icc r₁ r₂ ∧
      centralForceHamiltonian m (effectivePotential m ℓ U) (γ s) = E := by
  obtain ⟨a, b, ha0, har, hrb, hla, hlb⟩ :=
    exists_lt_effectivePotential hr₁ h₁₂ hU hE₁ hE₂ hlt hd₁ hd₂
  -- For times near `t` the radius stays in `(a, b)`, where `U` is differentiable.
  have hnear : ∀ᶠ s in 𝓝 t, (γ s).1 ∈ Ioo a b :=
    (hγ t).continuousAt.fst.eventually
      (Ioo_mem_nhds (har.trans_le ht.1) (ht.2.trans_lt hrb))
  obtain ⟨l, u, hlu, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.1 hnear
  filter_upwards [Ioo_mem_nhds hlu.1 hlu.2] with s hs
  -- The energy is conserved on the interval between `t` and `s`.
  have hIcc : Icc (min t s) (max t s) ⊆ Ioo l u :=
    (ordConnected_Ioo).out (min_rec' (· ∈ Ioo l u) hlu hs) (max_rec' (· ∈ Ioo l u) hlu hs)
  have hpos (w : ℝ) (hw : w ∈ Icc (min t s) (max t s)) : 0 < (γ w).1 :=
    ha0.trans_lt (hsub (hIcc hw)).1
  have hcons := centralForceHamiltonian_effectivePotential_eq_of_hasDerivAt
    (fun w _ ↦ hγ w) hpos fun w hw ↦ hU.differentiableAt (Ioi_mem_nhds (hpos w hw))
  have hEs : centralForceHamiltonian m (effectivePotential m ℓ U) (γ s) = E := by
    rw [hcons s ⟨min_le_right _ _, le_max_right _ _⟩, ← hcons t ⟨min_le_left _ _, le_max_left _ _⟩,
      hEt]
  refine ⟨?_, hEs⟩
  -- At energy `E` the effective potential is at most `E`, so the radius cannot leave the well.
  have hle : effectivePotential m ℓ U (γ s).1 ≤ E := by
    rw [← hEs, ← Prod.mk.eta (p := γ s), reducedHamiltonian_eq (hpos s ⟨min_le_right _ _,
      le_max_right _ _⟩).le]
    exact le_add_of_nonneg_left (div_nonneg (sq_nonneg _) (by positivity))
  have hab := hsub hs
  refine ⟨not_lt.1 fun h ↦ ?_, not_lt.1 fun h ↦ ?_⟩
  · exact (hla _ ⟨hab.1, h⟩).not_ge hle
  · exact (hlb _ ⟨h, hab.2⟩).not_ge hle

include hm hr₁ h₁₂ hU hE₁ hE₂ hlt hd₁ hd₂ hγ h₀ hE in
/-- A motion of energy `E` defined at all times and starting in the well stays in the well, with
energy `E`. -/
private theorem mem_Icc_and_eq (t : ℝ) :
    (γ t).1 ∈ Icc r₁ r₂ ∧ centralForceHamiltonian m (effectivePotential m ℓ U) (γ t) = E := by
  set S := {s | (γ s).1 ∈ Icc r₁ r₂ ∧
    centralForceHamiltonian m (effectivePotential m ℓ U) (γ s) = E}
  have hopen : IsOpen S := isOpen_iff_mem_nhds.2 fun s hs ↦
    eventually_mem_Icc_and_eq hm hr₁ h₁₂ hU hE₁ hE₂ hlt hd₁ hd₂ hγ hs.1 hs.2
  have hclosed : IsClosed S := by
    refine isOpen_compl_iff.1 (isOpen_iff_mem_nhds.2 fun s hs ↦ ?_)
    by_cases hs₁ : (γ s).1 ∈ Icc r₁ r₂
    · -- The energy is continuous at `γ s`, and differs from `E` there.
      have hs₂ : centralForceHamiltonian m (effectivePotential m ℓ U) (γ s) ≠ E :=
        fun h ↦ hs ⟨hs₁, h⟩
      have hpos : 0 < (γ s).1 := hr₁.trans_le hs₁.1
      have hHc : ContinuousAt (centralForceHamiltonian m (effectivePotential m ℓ U)) (γ s) := by
        rw [← Prod.mk.eta (p := γ s)]
        exact (differentiableAt_centralForceHamiltonian_effectivePotential hpos
          (hU.differentiableAt (Ioi_mem_nhds hpos)) _).continuousAt
      filter_upwards [(hHc.comp (hγ s).continuousAt).eventually_ne hs₂] with w hw hwS
      exact hw hwS.2
    · filter_upwards [(hγ s).continuousAt.fst.eventually (isClosed_Icc.isOpen_compl.mem_nhds hs₁)]
        with w hw hwS
      exact hw hwS.1
  exact ((IsClopen.eq_univ ⟨hclosed, hopen⟩ ⟨t₀, h₀, hE⟩).symm ▸ mem_univ t : t ∈ S)

include hm hr₁ h₁₂ hU hE₁ hE₂ hlt hd₁ hd₂ hγ h₀ hE in
/-- **Confinement to the potential well.** Let `0 < r₁ < r₂` be simple turning points of energy
`E` for a potential `U` differentiable on the half-line, with `U_ℓ < E` in between. A radial motion
of energy `E` defined at all times and with radius in `[r₁, r₂]` at one time has radius in
`[r₁, r₂]` at all times. -/
theorem mem_Icc_of_forall_hasDerivAt_effectivePotential (t : ℝ) : (γ t).1 ∈ Icc r₁ r₂ :=
  (mem_Icc_and_eq hm hr₁ h₁₂ hU hE₁ hE₂ hlt hd₁ hd₂ hγ h₀ hE t).1

include hm hr₁ h₁₂ hU hE₁ hE₂ hlt hd₁ hd₂ hγ h₀ hE in
/-- Along the motion, the radius moves with velocity `p_r / m`. -/
private theorem hasDerivAt_radius (t : ℝ) :
    HasDerivAt (fun s ↦ (γ s).1) ((γ t).2 / m) t := by
  have hpos := hr₁.trans_le (mem_Icc_of_forall_hasDerivAt_effectivePotential hm hr₁ h₁₂ hU hE₁ hE₂
    hlt hd₁ hd₂ hγ h₀ hE t).1
  exact hasDerivAt_fst_of_hasDerivAt_hamiltonianVectorField_effectivePotential (hγ t) hpos
    (hU.differentiableAt (Ioi_mem_nhds hpos))

include hm hr₁ h₁₂ hU hE₁ hE₂ hlt hd₁ hd₂ hγ h₀ hE in
/-- Along the motion, the radial momentum moves with velocity `-U_ℓ'(r)`. -/
private theorem hasDerivAt_momentum (t : ℝ) :
    HasDerivAt (fun s ↦ (γ s).2) (-deriv (effectivePotential m ℓ U) (γ t).1) t := by
  have hpos := hr₁.trans_le (mem_Icc_of_forall_hasDerivAt_effectivePotential hm hr₁ h₁₂ hU hE₁ hE₂
    hlt hd₁ hd₂ hγ h₀ hE t).1
  have hUd := hU.differentiableAt (Ioi_mem_nhds hpos)
  refine (hasDerivAt_snd_of_hasDerivAt_hamiltonianVectorField_effectivePotential (hγ t) hpos
    hUd).congr_deriv ?_
  rw [(hasDerivAt_effectivePotential (m := m) (ℓ := ℓ) hUd.hasDerivAt hpos.ne').deriv]
  ring

include hm hr₁ h₁₂ hU hE₁ hE₂ hlt hd₁ hd₂ hγ h₀ hE in
/-- Along the motion, the radial momentum vanishes exactly at the turning points. -/
private theorem momentum_ne_zero_iff (t : ℝ) : (γ t).2 ≠ 0 ↔ (γ t).1 ∈ Ioo r₁ r₂ := by
  obtain ⟨hmem, hEt⟩ := mem_Icc_and_eq hm hr₁ h₁₂ hU hE₁ hE₂ hlt hd₁ hd₂ hγ h₀ hE t
  rw [← Prod.mk.eta (p := γ t), reducedHamiltonian_eq (hr₁.trans_le hmem.1).le] at hEt
  constructor
  · intro hp
    have hk : 0 < (γ t).2 ^ 2 / (2 * m) := by positivity
    refine ⟨lt_of_le_of_ne hmem.1 fun h ↦ ?_, lt_of_le_of_ne hmem.2 fun h ↦ ?_⟩
    · rw [← h] at hEt
      linarith
    · rw [h] at hEt
      linarith
  · intro hr hp
    rw [hp] at hEt
    have := hlt _ hr
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div,
      zero_add] at hEt
    linarith

include hm hr₁ h₁₂ hU hE₁ hE₂ hlt hd₁ hd₂ hγ h₀ hE in
/-- Where the radial momentum vanishes, the radius is a turning point. -/
private theorem radius_eq_or_eq {t : ℝ} (hp : (γ t).2 = 0) : (γ t).1 = r₁ ∨ (γ t).1 = r₂ := by
  have hmem := mem_Icc_of_forall_hasDerivAt_effectivePotential hm hr₁ h₁₂ hU hE₁ hE₂ hlt hd₁ hd₂
    hγ h₀ hE t
  have hnot := mt (momentum_ne_zero_iff hm hr₁ h₁₂ hU hE₁ hE₂ hlt hd₁ hd₂ hγ h₀ hE t).2
    (not_not.2 hp)
  rcases hmem.1.eq_or_lt with h | h
  · exact Or.inl h.symm
  · exact Or.inr (le_antisymm hmem.2 (not_lt.1 fun h' ↦ hnot ⟨h, h'⟩))

include hm hr₁ h₁₂ hU hE₁ hE₂ hlt hd₁ hd₂ hγ h₀ hE in
/-- At the turning points the radial momentum vanishes. -/
private theorem momentum_eq_zero {u : ℝ} (h : (γ u).1 = r₁ ∨ (γ u).1 = r₂) : (γ u).2 = 0 :=
  not_not.1 fun hp ↦ by
    have := (momentum_ne_zero_iff hm hr₁ h₁₂ hU hE₁ hE₂ hlt hd₁ hd₂ hγ h₀ hE u).1 hp
    rcases h with h | h <;> rw [h] at this
    exacts [this.1.false, this.2.false]

include hm hr₁ h₁₂ hU hE₁ hE₂ hlt hd₁ hd₂ hγ h₀ hE in
/-- Along the motion, the absolute radial momentum is `|p_r|(r)`. -/
private theorem abs_momentum (t : ℝ) : |(γ t).2| = absRadialMomentum m U ℓ E (γ t).1 := by
  obtain ⟨hmem, hEt⟩ := mem_Icc_and_eq hm hr₁ h₁₂ hU hE₁ hE₂ hlt hd₁ hd₂ hγ h₀ hE t
  rw [← Prod.mk.eta (p := γ t)] at hEt
  exact (absRadialMomentum_eq_abs hm.ne' (hr₁.trans_le hmem.1) hEt).symm

include hm hr₁ h₁₂ hU hE₁ hE₂ hlt hd₁ hd₂ hγ h₀ hE in
/-- While the radial momentum is positive, the radius increases strictly. -/
private theorem strictMonoOn_radius {s t : ℝ} (hp : ∀ u ∈ Ioo s t, 0 < (γ u).2) :
    StrictMonoOn (fun u ↦ (γ u).1) (Icc s t) :=
  strictMonoOn_of_deriv_pos (convex_Icc s t)
    (fun u _ ↦ (hasDerivAt_radius hm hr₁ h₁₂ hU hE₁ hE₂ hlt hd₁ hd₂ hγ h₀ hE u).continuousAt
      |>.continuousWithinAt) fun u hu ↦ by
      rw [interior_Icc] at hu
      rw [(hasDerivAt_radius hm hr₁ h₁₂ hU hE₁ hE₂ hlt hd₁ hd₂ hγ h₀ hE u).deriv]
      exact div_pos (hp u hu) hm

include hm hr₁ h₁₂ hU hE₁ hE₂ hlt hd₁ hd₂ hγ h₀ hE in
/-- While the radial momentum is negative, the radius decreases strictly. -/
private theorem strictAntiOn_radius {s t : ℝ} (hp : ∀ u ∈ Ioo s t, (γ u).2 < 0) :
    StrictAntiOn (fun u ↦ (γ u).1) (Icc s t) :=
  strictAntiOn_of_deriv_neg (convex_Icc s t)
    (fun u _ ↦ (hasDerivAt_radius hm hr₁ h₁₂ hU hE₁ hE₂ hlt hd₁ hd₂ hγ h₀ hE u).continuousAt
      |>.continuousWithinAt) fun u hu ↦ by
      rw [interior_Icc] at hu
      rw [(hasDerivAt_radius hm hr₁ h₁₂ hU hE₁ hE₂ hlt hd₁ hd₂ hγ h₀ hE u).deriv]
      exact div_neg_of_neg_of_pos (hp u hu) hm

include hm hr₁ h₁₂ hU hE₁ hE₂ hlt hd₁ hd₂ hγ h₀ hE in
/-- **Time along a rising stretch.** While the radial momentum is positive on `(s, t)`, the elapsed
time is the quadrature `t - s = ∫_{r(s)}^{r(t)} m dr / |p_r|`. -/
private theorem sub_eq_integral_of_pos {s t : ℝ} (hst : s ≤ t) (hp : ∀ u ∈ Ioo s t, 0 < (γ u).2) :
    t - s = ∫ r in (γ s).1..(γ t).1, m / absRadialMomentum m U ℓ E r := by
  have hmem := mem_Icc_and_eq hm hr₁ h₁₂ hU hE₁ hE₂ hlt hd₁ hd₂ hγ h₀ hE
  have hmono := strictMonoOn_radius hm hr₁ h₁₂ hU hE₁ hE₂ hlt hd₁ hd₂ hγ h₀ hE hp
  have hpos (u : ℝ) : 0 < (γ u).1 := hr₁.trans_le (hmem u).1.1
  exact sub_eq_integral_div_absRadialMomentum hm hst (fun u _ ↦ hγ u) (fun u _ ↦ hpos u)
    (fun u _ ↦ hU.differentiableAt (Ioi_mem_nhds (hpos u))) (hmem s).2
    (fun r hr ↦ hlt r ⟨(hmem s).1.1.trans_lt hr.1, hr.2.trans_le (hmem t).1.2⟩)
    (Or.inl ⟨rfl, rfl⟩) fun u hu ↦ ⟨hmono ⟨le_rfl, hst⟩ (Ioo_subset_Icc_self hu) hu.1,
      hmono (Ioo_subset_Icc_self hu) ⟨hst, le_rfl⟩ hu.2⟩

include hm hr₁ h₁₂ hU hE₁ hE₂ hlt hd₁ hd₂ hγ h₀ hE in
/-- **Time along a falling stretch.** While the radial momentum is negative on `(s, t)`, the
elapsed time is the quadrature `t - s = ∫_{r(t)}^{r(s)} m dr / |p_r|`. -/
private theorem sub_eq_integral_of_neg {s t : ℝ} (hst : s ≤ t) (hp : ∀ u ∈ Ioo s t, (γ u).2 < 0) :
    t - s = ∫ r in (γ t).1..(γ s).1, m / absRadialMomentum m U ℓ E r := by
  have hmem := mem_Icc_and_eq hm hr₁ h₁₂ hU hE₁ hE₂ hlt hd₁ hd₂ hγ h₀ hE
  have hanti := strictAntiOn_radius hm hr₁ h₁₂ hU hE₁ hE₂ hlt hd₁ hd₂ hγ h₀ hE hp
  have hpos (u : ℝ) : 0 < (γ u).1 := hr₁.trans_le (hmem u).1.1
  exact sub_eq_integral_div_absRadialMomentum hm hst (fun u _ ↦ hγ u) (fun u _ ↦ hpos u)
    (fun u _ ↦ hU.differentiableAt (Ioi_mem_nhds (hpos u))) (hmem s).2
    (fun r hr ↦ hlt r ⟨(hmem t).1.1.trans_lt hr.1, hr.2.trans_le (hmem s).1.2⟩)
    (Or.inr ⟨rfl, rfl⟩) fun u hu ↦ ⟨hanti (Ioo_subset_Icc_self hu) ⟨hst, le_rfl⟩ hu.2,
      hanti ⟨le_rfl, hst⟩ (Ioo_subset_Icc_self hu) hu.1⟩

include hm hr₁ h₁₂ hU hE₁ hE₂ hlt hd₁ hd₂ hγ h₀ hE in
/-- **Passages are short.** During a time interval on which the radial momentum does not vanish,
the radius runs monotonically inside the well, so the interval lasts at most the time quadrature
`∫_{r₁}^{r₂} m dr / |p_r|`. -/
private theorem sub_le_integral {s t : ℝ} (hst : s ≤ t) (hp : ∀ u ∈ Ioo s t, (γ u).2 ≠ 0) :
    t - s ≤ ∫ r in r₁..r₂, m / absRadialMomentum m U ℓ E r := by
  have hint := intervalIntegrable_div_absRadialMomentum_well hm hr₁ h₁₂ hU hlt hd₁ hd₂
  have hnn : 0 ≤ᵐ[volume.restrict (Ioc r₁ r₂)] fun r ↦ m / absRadialMomentum m U ℓ E r :=
    ae_of_all _ fun r ↦ div_nonneg hm.le (absRadialMomentum_nonneg _ _ _ _ _)
  have hmem := mem_Icc_of_forall_hasDerivAt_effectivePotential hm hr₁ h₁₂ hU hE₁ hE₂ hlt hd₁ hd₂
    hγ h₀ hE
  have hpc : Continuous fun u ↦ (γ u).2 := continuous_iff_continuousAt.2 fun u ↦
    (hasDerivAt_momentum hm hr₁ h₁₂ hU hE₁ hE₂ hlt hd₁ hd₂ hγ h₀ hE u).continuousAt
  rcases hst.eq_or_lt with rfl | hst'
  · rw [sub_self]
    exact intervalIntegral.integral_nonneg h₁₂.le fun r _ ↦
      div_nonneg hm.le (absRadialMomentum_nonneg _ _ _ _ _)
  -- The radial momentum has a constant sign on `(s, t)`.
  have hsign {u w : ℝ} (hu : u ∈ Ioo s t) (hw : w ∈ Ioo s t) :
      SignType.sign (γ u).2 = SignType.sign (γ w).2 :=
    isPreconnected_Ioo.sign_eq_of_continuousOn hpc.continuousOn hp hu hw
  have hmid : (s + t) / 2 ∈ Ioo s t := ⟨by linarith, by linarith⟩
  rcases (hp _ hmid).lt_or_gt with hneg | hpos
  · have hp' (u : ℝ) (hu : u ∈ Ioo s t) : (γ u).2 < 0 :=
      sign_eq_neg_one_iff.1 ((hsign hu hmid).trans (sign_eq_neg_one_iff.2 hneg))
    have hlt' := strictAntiOn_radius hm hr₁ h₁₂ hU hE₁ hE₂ hlt hd₁ hd₂ hγ h₀ hE hp'
      ⟨le_rfl, hst⟩ ⟨hst, le_rfl⟩ hst'
    rw [sub_eq_integral_of_neg hm hr₁ h₁₂ hU hE₁ hE₂ hlt hd₁ hd₂ hγ h₀ hE hst hp']
    exact intervalIntegral.integral_mono_interval (hmem t).1 hlt'.le (hmem s).2 hnn hint
  · have hp' (u : ℝ) (hu : u ∈ Ioo s t) : 0 < (γ u).2 :=
      sign_eq_one_iff.1 ((hsign hu hmid).trans (sign_eq_one_iff.2 hpos))
    have hlt' := strictMonoOn_radius hm hr₁ h₁₂ hU hE₁ hE₂ hlt hd₁ hd₂ hγ h₀ hE hp'
      ⟨le_rfl, hst⟩ ⟨hst, le_rfl⟩ hst'
    rw [sub_eq_integral_of_pos hm hr₁ h₁₂ hU hE₁ hE₂ hlt hd₁ hd₂ hγ h₀ hE hst hp']
    exact intervalIntegral.integral_mono_interval (hmem s).1 hlt'.le (hmem t).2 hnn hint

include hm hr₁ h₁₂ hU hE₁ hE₂ hlt hd₁ hd₂ hγ h₀ hE in
/-- **The next turning time.** If the radial momentum vanishes at time `t₁` and `σ p_r` has
positive derivative there, then `p_r` vanishes again at a later time `t₂`, and `σ p_r` is positive
in between. -/
private theorem exists_next_turning {σ t₁ : ℝ} (hσ : σ ≠ 0) (hp₀ : (γ t₁).2 = 0)
    (hd : 0 < σ * -deriv (effectivePotential m ℓ U) (γ t₁).1) :
    ∃ t₂, t₁ < t₂ ∧ (γ t₂).2 = 0 ∧ ∀ u ∈ Ioo t₁ t₂, 0 < σ * (γ u).2 := by
  have hfd (t : ℝ) :=
    (hasDerivAt_momentum hm hr₁ h₁₂ hU hE₁ hE₂ hlt hd₁ hd₂ hγ h₀ hE t).const_mul σ
  have hfc : Continuous fun t ↦ σ * (γ t).2 :=
    continuous_iff_continuousAt.2 fun t ↦ (hfd t).continuousAt
  have hL : 0 ≤ ∫ r in r₁..r₂, m / absRadialMomentum m U ℓ E r :=
    intervalIntegral.integral_nonneg h₁₂.le fun r _ ↦
      div_nonneg hm.le (absRadialMomentum_nonneg _ _ _ _ _)
  obtain ⟨t₂, ⟨h₁₂', -⟩, hf₂, hpos⟩ := hfc.continuousOn.exists_mem_Ioo_eq_and_forall_gt
    (b := t₁ + 1 + ∫ r in r₁..r₂, m / absRadialMomentum m U ℓ E r)
    -- `σ p_r` vanishes at `t₁` with positive derivative, so it is positive right after `t₁`.
    (by simpa [hp₀] using (hfd t₁).hasDerivWithinAt.eventually_nhdsGT_lt_of_pos hd) <| by
    -- Passages are short, so `σ p_r` does not stay positive.
    by_contra! hfpos
    have := sub_le_integral hm hr₁ h₁₂ hU hE₁ hE₂ hlt hd₁ hd₂ hγ h₀ hE (s := t₁) (by linarith)
      fun w hw ↦ right_ne_zero_of_mul (hfpos w hw).ne'
    linarith
  exact ⟨t₂, h₁₂', (mul_eq_zero.1 hf₂).resolve_left hσ, hpos⟩

include hm hr₁ h₁₂ hU hE₁ hE₂ hlt hd₁ hd₂ hγ h₀ hE in
/-- From the inner turning point the radius rises to the outer one, with positive radial momentum
in between. -/
private theorem exists_outer {t₁ : ℝ} (h₁ : (γ t₁).1 = r₁) :
    ∃ t₂, t₁ < t₂ ∧ (γ t₂).1 = r₂ ∧ ∀ u ∈ Ioo t₁ t₂, 0 < (γ u).2 := by
  have hp₁ := momentum_eq_zero hm hr₁ h₁₂ hU hE₁ hE₂ hlt hd₁ hd₂ hγ h₀ hE (Or.inl h₁)
  obtain ⟨t₂, h₁₂', hp₂, hpos⟩ := exists_next_turning hm hr₁ h₁₂ hU hE₁ hE₂ hlt hd₁ hd₂ hγ h₀ hE
    one_ne_zero hp₁ (by
      rw [one_mul, h₁, neg_pos]
      exact deriv_effectivePotential_neg hr₁ h₁₂ hU hE₁ hlt hd₁)
  simp only [one_mul] at hpos
  refine ⟨t₂, h₁₂', ?_, hpos⟩
  refine (radius_eq_or_eq hm hr₁ h₁₂ hU hE₁ hE₂ hlt hd₁ hd₂ hγ h₀ hE hp₂).resolve_left fun h₂ ↦ ?_
  have := strictMonoOn_radius hm hr₁ h₁₂ hU hE₁ hE₂ hlt hd₁ hd₂ hγ h₀ hE hpos
    ⟨le_rfl, h₁₂'.le⟩ ⟨h₁₂'.le, le_rfl⟩ h₁₂'
  simp only [h₁, h₂, lt_self_iff_false] at this

include hm hr₁ h₁₂ hU hE₁ hE₂ hlt hd₁ hd₂ hγ h₀ hE in
/-- From the outer turning point the radius falls to the inner one, with negative radial momentum
in between. -/
private theorem exists_inner {t₂ : ℝ} (h₂ : (γ t₂).1 = r₂) :
    ∃ t₃, t₂ < t₃ ∧ (γ t₃).1 = r₁ ∧ ∀ u ∈ Ioo t₂ t₃, (γ u).2 < 0 := by
  have hp₂ := momentum_eq_zero hm hr₁ h₁₂ hU hE₁ hE₂ hlt hd₁ hd₂ hγ h₀ hE (Or.inr h₂)
  obtain ⟨t₃, h₂₃, hp₃, hneg⟩ := exists_next_turning hm hr₁ h₁₂ hU hE₁ hE₂ hlt hd₁ hd₂ hγ h₀ hE
    (neg_ne_zero.2 one_ne_zero) hp₂ (by
      rw [h₂, neg_one_mul, neg_neg]
      exact deriv_effectivePotential_pos hr₁ h₁₂ hU hE₂ hlt hd₂)
  simp only [neg_one_mul, neg_pos] at hneg
  refine ⟨t₃, h₂₃, ?_, hneg⟩
  refine (radius_eq_or_eq hm hr₁ h₁₂ hU hE₁ hE₂ hlt hd₁ hd₂ hγ h₀ hE hp₃).resolve_right
    fun h₃ ↦ ?_
  have := strictAntiOn_radius hm hr₁ h₁₂ hU hE₁ hE₂ hlt hd₁ hd₂ hγ h₀ hE hneg
    ⟨le_rfl, h₂₃.le⟩ ⟨h₂₃.le, le_rfl⟩ h₂₃
  simp only [h₂, h₃, lt_self_iff_false] at this

include hm hr₁ h₁₂ hU hE₁ hE₂ hlt hd₁ hd₂ hγ h₀ hE in
/-- After any time `a`, the radius reaches the inner turning point within the time
`1 + 2 ∫_{r₁}^{r₂} m dr / |p_r|`. -/
private theorem exists_mem_Ioo_fst_eq (a : ℝ) :
    ∃ s ∈ Ioo a (a + 1 + 2 * ∫ r in r₁..r₂, m / absRadialMomentum m U ℓ E r), (γ s).1 = r₁ := by
  have hL : 0 ≤ ∫ r in r₁..r₂, m / absRadialMomentum m U ℓ E r :=
    intervalIntegral.integral_nonneg h₁₂.le fun r _ ↦
      div_nonneg hm.le (absRadialMomentum_nonneg _ _ _ _ _)
  -- Passages are short, so the radial momentum vanishes at some time, at a turning point.
  obtain ⟨u, hu, hpu⟩ : ∃ u ∈ Ioo a (a + 1 + ∫ r in r₁..r₂, m / absRadialMomentum m U ℓ E r),
      (γ u).2 = 0 := by
    by_contra! hne
    have := sub_le_integral hm hr₁ h₁₂ hU hE₁ hE₂ hlt hd₁ hd₂ hγ h₀ hE (by linarith) hne
    linarith
  rcases radius_eq_or_eq hm hr₁ h₁₂ hU hE₁ hE₂ hlt hd₁ hd₂ hγ h₀ hE hpu with hu' | hu'
  · exact ⟨u, ⟨hu.1, by linarith [hu.2]⟩, hu'⟩
  · obtain ⟨t, hut, ht, hneg⟩ := exists_inner hm hr₁ h₁₂ hU hE₁ hE₂ hlt hd₁ hd₂ hγ h₀ hE hu'
    have := sub_le_integral hm hr₁ h₁₂ hU hE₁ hE₂ hlt hd₁ hd₂ hγ h₀ hE hut.le
      fun w hw ↦ (hneg w hw).ne
    exact ⟨t, ⟨hu.1.trans hut, by linarith [hu.2]⟩, ht⟩

include hm hr₁ h₁₂ hU hE₁ hE₂ hlt hd₁ hd₂ hγ h₀ hE in
/-- **The motion reaches the inner turning point.** Under the hypotheses of
`TauCeti.mem_Icc_of_forall_hasDerivAt_effectivePotential`, there is a time at which the radius is
the inner turning point `r₁`. -/
theorem exists_fst_eq_of_forall_hasDerivAt_effectivePotential : ∃ t, (γ t).1 = r₁ :=
  let ⟨s, _, hs⟩ := exists_mem_Ioo_fst_eq hm hr₁ h₁₂ hU hE₁ hE₂ hlt hd₁ hd₂ hγ h₀ hE 0
  ⟨s, hs⟩

include hm hr₁ h₁₂ hU hE₁ hE₂ hlt hd₁ hd₂ hγ h₀ hE in
/-- **One radial oscillation.** Under the hypotheses of
`TauCeti.mem_Icc_of_forall_hasDerivAt_effectivePotential`, let the radius be the inner turning
point `r₁` at time `t₁`. Then it rises to the outer turning point `r₂` at a time `t₂` with
`t₁ < t₂ < t₁ + T`, with positive radial momentum in between, and falls back to `r₁` at time
`t₁ + T`, with negative radial momentum in between, where `T` is the radial period. -/
theorem exists_mem_Ioo_fst_eq_of_forall_hasDerivAt_effectivePotential {t₁ : ℝ}
    (h₁ : (γ t₁).1 = r₁) :
    ∃ t₂ ∈ Ioo t₁ (t₁ + radialPeriod m U ℓ E r₁ r₂), (γ t₂).1 = r₂ ∧
      (γ (t₁ + radialPeriod m U ℓ E r₁ r₂)).1 = r₁ ∧ (∀ u ∈ Ioo t₁ t₂, 0 < (γ u).2) ∧
      ∀ u ∈ Ioo t₂ (t₁ + radialPeriod m U ℓ E r₁ r₂), (γ u).2 < 0 := by
  obtain ⟨t₂, h₁₂', h₂, hpos⟩ := exists_outer hm hr₁ h₁₂ hU hE₁ hE₂ hlt hd₁ hd₂ hγ h₀ hE h₁
  obtain ⟨t₃, h₂₃, h₃, hneg⟩ := exists_inner hm hr₁ h₁₂ hU hE₁ hE₂ hlt hd₁ hd₂ hγ h₀ hE h₂
  have hmem (u : ℝ) (hu : u ∈ Ioo t₁ t₂ ∨ u ∈ Ioo t₂ t₃) : (γ u).1 ∈ Ioo r₁ r₂ :=
    (momentum_ne_zero_iff hm hr₁ h₁₂ hU hE₁ hE₂ hlt hd₁ hd₂ hγ h₀ hE u).1 <|
      hu.elim (fun hu ↦ (hpos u hu).ne') fun hu ↦ (hneg u hu).ne
  have hpos' (u : ℝ) : 0 < (γ u).1 := hr₁.trans_le (mem_Icc_of_forall_hasDerivAt_effectivePotential
    hm hr₁ h₁₂ hU hE₁ hE₂ hlt hd₁ hd₂ hγ h₀ hE u).1
  have hT := sub_eq_radialPeriod hm h₁₂'.le h₂₃.le (fun u _ ↦ hγ u) (fun u _ ↦ hpos' u)
    (fun u _ ↦ hU.differentiableAt (Ioi_mem_nhds (hpos' u)))
    (mem_Icc_and_eq hm hr₁ h₁₂ hU hE₁ hE₂ hlt hd₁ hd₂ hγ h₀ hE t₁).2 hlt (Or.inl ⟨h₁, h₂⟩)
    (h₃.trans h₁.symm) (fun u hu ↦ hmem u (Or.inl hu)) fun u hu ↦ hmem u (Or.inr hu)
  obtain rfl : t₃ = t₁ + radialPeriod m U ℓ E r₁ r₂ := by linarith
  exact ⟨t₂, ⟨h₁₂', h₂₃⟩, h₂, h₃, hpos, hneg⟩

include hm hr₁ h₁₂ hU hE₁ hE₂ hlt hd₁ hd₂ hγ h₀ hE in
/-- **A rising stretch from the inner turning point.** If the radius is `r₁` at time `a` and the
radial momentum is positive on `(a, b)`, then at every time `u ∈ [a, b]` the elapsed time is the
quadrature `u - a = ∫_{r₁}^{r(u)} m dr / |p_r|`, and the radial momentum is nonnegative. -/
private theorem sub_eq_integral_and_nonneg {a b u : ℝ} (ha : (γ a).1 = r₁)
    (hp : ∀ w ∈ Ioo a b, 0 < (γ w).2) (hu : u ∈ Icc a b) :
    u - a = (∫ r in r₁..(γ u).1, m / absRadialMomentum m U ℓ E r) ∧ 0 ≤ (γ u).2 := by
  refine ⟨?_, ?_⟩
  · rw [sub_eq_integral_of_pos hm hr₁ h₁₂ hU hE₁ hE₂ hlt hd₁ hd₂ hγ h₀ hE hu.1
      (fun w hw ↦ hp w ⟨hw.1, hw.2.trans_le hu.2⟩), ha]
  rcases hu.1.eq_or_lt with rfl | h₁
  · exact (momentum_eq_zero hm hr₁ h₁₂ hU hE₁ hE₂ hlt hd₁ hd₂ hγ h₀ hE (Or.inl ha)).ge
  rcases hu.2.eq_or_lt with rfl | h₂
  · -- At the end of the stretch, the momentum is a limit of positive values.
    exact ge_of_tendsto (((hasDerivAt_momentum hm hr₁ h₁₂ hU hE₁ hE₂ hlt hd₁ hd₂ hγ h₀ hE
      _).continuousAt.tendsto).mono_left nhdsWithin_le_nhds)
      (eventually_of_mem (Ioo_mem_nhdsLT h₁) fun w hw ↦ (hp w hw).le)
  · exact (hp u ⟨h₁, h₂⟩).le

include hm hr₁ h₁₂ hU hE₁ hE₂ hlt hd₁ hd₂ hγ h₀ hE in
/-- **A falling stretch to the inner turning point.** If the radius is `r₁` at time `b` and the
radial momentum is negative on `(a, b)`, then at every time `u ∈ [a, b]` the remaining time is the
quadrature `b - u = ∫_{r₁}^{r(u)} m dr / |p_r|`, and the radial momentum is nonpositive. -/
private theorem sub_eq_integral_and_nonpos {a b u : ℝ} (hb : (γ b).1 = r₁)
    (hp : ∀ w ∈ Ioo a b, (γ w).2 < 0) (hu : u ∈ Icc a b) :
    b - u = (∫ r in r₁..(γ u).1, m / absRadialMomentum m U ℓ E r) ∧ (γ u).2 ≤ 0 := by
  refine ⟨?_, ?_⟩
  · rw [sub_eq_integral_of_neg hm hr₁ h₁₂ hU hE₁ hE₂ hlt hd₁ hd₂ hγ h₀ hE hu.2
      (fun w hw ↦ hp w ⟨hu.1.trans_lt hw.1, hw.2⟩), hb]
  rcases hu.2.eq_or_lt with rfl | h₂
  · exact (momentum_eq_zero hm hr₁ h₁₂ hU hE₁ hE₂ hlt hd₁ hd₂ hγ h₀ hE (Or.inl hb)).le
  rcases hu.1.eq_or_lt with rfl | h₁
  · -- At the start of the stretch, the momentum is a limit of negative values.
    exact le_of_tendsto (((hasDerivAt_momentum hm hr₁ h₁₂ hU hE₁ hE₂ hlt hd₁ hd₂ hγ h₀ hE
      _).continuousAt.tendsto).mono_left nhdsWithin_le_nhds)
      (eventually_of_mem (Ioo_mem_nhdsGT h₂) fun w hw ↦ (hp w hw).le)
  · exact (hp u ⟨h₁, h₂⟩).le

include hm hr₁ h₁₂ hU hE₁ hE₂ hlt hd₁ hd₂ hγ h₀ hE in
/-- After a passage through the inner turning point at time `s`, the motion repeats itself one
radial period later, at every time of the following radial period. -/
private theorem apply_add_radialPeriod_of_fst_eq {s t : ℝ} (hs : (γ s).1 = r₁)
    (ht : t ∈ Icc s (s + radialPeriod m U ℓ E r₁ r₂)) :
    γ (t + radialPeriod m U ℓ E r₁ r₂) = γ t := by
  set T := radialPeriod m U ℓ E r₁ r₂
  have hmem := mem_Icc_of_forall_hasDerivAt_effectivePotential hm hr₁ h₁₂ hU hE₁ hE₂ hlt hd₁ hd₂
    hγ h₀ hE
  -- The time to reach a radius from `r₁` determines the radius.
  have hF := (strictMonoOn_integral_div_absRadialMomentum hm hr₁ h₁₂ hU hlt hd₁ hd₂).injOn
  have hrise {a b u : ℝ} (ha : (γ a).1 = r₁) (hp : ∀ w ∈ Ioo a b, 0 < (γ w).2)
      (hu : u ∈ Icc a b) :=
    sub_eq_integral_and_nonneg hm hr₁ h₁₂ hU hE₁ hE₂ hlt hd₁ hd₂ hγ h₀ hE ha hp hu
  have hfall {a b u : ℝ} (hb : (γ b).1 = r₁) (hp : ∀ w ∈ Ioo a b, (γ w).2 < 0)
      (hu : u ∈ Icc a b) :=
    sub_eq_integral_and_nonpos hm hr₁ h₁₂ hU hE₁ hE₂ hlt hd₁ hd₂ hγ h₀ hE hb hp hu
  -- Two consecutive radial oscillations, the second one starting at `s + T`.
  obtain ⟨t₂, ⟨hs₂, -⟩, h₂, hT, hpos, hneg⟩ :=
    exists_mem_Ioo_fst_eq_of_forall_hasDerivAt_effectivePotential hm hr₁ h₁₂ hU hE₁ hE₂ hlt hd₁
      hd₂ hγ h₀ hE hs
  obtain ⟨t₄, ⟨hT₄, -⟩, h₄, hTT, hpos', hneg'⟩ :=
    exists_mem_Ioo_fst_eq_of_forall_hasDerivAt_effectivePotential hm hr₁ h₁₂ hU hE₁ hE₂ hlt hd₁
      hd₂ hγ h₀ hE hT
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
    rw [abs_momentum hm hr₁ h₁₂ hU hE₁ hE₂ hlt hd₁ hd₂ hγ h₀ hE,
      abs_momentum hm hr₁ h₁₂ hU hE₁ hE₂ hlt hd₁ hd₂ hγ h₀ hE, hr.1]
  refine Prod.ext hr.1 ?_
  rcases hr.2 with ⟨h, h'⟩ | ⟨h, h'⟩
  · rwa [abs_of_nonneg h, abs_of_nonneg h'] at habs
  · rw [abs_of_nonpos h, abs_of_nonpos h'] at habs
    linarith

include hm hr₁ h₁₂ hU hE₁ hE₂ hlt hd₁ hd₂ hγ h₀ hE in
/-- **The radial motion in a potential well is periodic.** Let `0 < r₁ < r₂` be simple turning
points of energy `E` for a potential `U` differentiable on the half-line: `U_ℓ(r₁) = U_ℓ(r₂) = E`,
`U_ℓ'(rᵢ) ≠ 0` and `U_ℓ < E` in between. Then every integral curve of the reduced Hamiltonian vector
field defined at all times, with energy `E` and radius in `[r₁, r₂]` at one time, is periodic, with
period the radial period `T = 2 ∫_{r₁}^{r₂} m dr / |p_r|`. -/
theorem periodic_of_forall_hasDerivAt_effectivePotential :
    Periodic γ (radialPeriod m U ℓ E r₁ r₂) := by
  intro t
  set T := radialPeriod m U ℓ E r₁ r₂
  have hT : 0 < T := radialPeriod_pos hm hr₁ h₁₂
    (hU.continuousOn.mono fun _ hr ↦ hr₁.trans_le hr.1) hlt
    (fun _ ↦ ⟨_, hd₁, (hasDerivAt_deriv_effectivePotential hU hr₁).hasDerivWithinAt⟩)
    (fun _ ↦ ⟨_, hd₂, (hasDerivAt_deriv_effectivePotential hU (hr₁.trans h₁₂)).hasDerivWithinAt⟩)
  -- A passage through the inner turning point before `t`, and its translates by multiples of `T`.
  obtain ⟨s, hs, hs₁⟩ := exists_mem_Ioo_fst_eq hm hr₁ h₁₂ hU hE₁ hE₂ hlt hd₁ hd₂ hγ h₀ hE
    (t - (1 + 2 * ∫ r in r₁..r₂, m / absRadialMomentum m U ℓ E r))
  have hst : s ≤ t := by linarith [hs.2]
  have hiter (n : ℕ) : (γ (s + n * T)).1 = r₁ := by
    induction n with
    | zero => simpa using hs₁
    | succ n ih =>
      obtain ⟨-, -, -, h, -⟩ := exists_mem_Ioo_fst_eq_of_forall_hasDerivAt_effectivePotential hm hr₁
        h₁₂ hU hE₁ hE₂ hlt hd₁ hd₂ hγ h₀ hE ih
      rwa [Nat.cast_succ, add_one_mul, ← add_assoc]
  -- The last such passage `s + n T` before `t` lies within one period of `t`.
  set n := ⌊(t - s) / T⌋₊
  have h₁ : (n : ℝ) * T ≤ t - s :=
    (le_div_iff₀ hT).1 (Nat.floor_le (div_nonneg (sub_nonneg.2 hst) hT.le))
  have h₂ : t - s < (n + 1) * T := (div_lt_iff₀ hT).1 (Nat.lt_floor_add_one _)
  exact apply_add_radialPeriod_of_fst_eq hm hr₁ h₁₂ hU hE₁ hE₂ hlt hd₁ hd₂ hγ h₀ hE (hiter n)
    ⟨by linarith, by linarith⟩

include hm hr₁ h₁₂ hU hE₁ hE₂ hlt hd₁ hd₂ hγ h₀ hE in
/-- **Precession of the orbit.** Under the hypotheses of
`TauCeti.periodic_of_forall_hasDerivAt_effectivePotential`, let the polar angle satisfy
`θ' = ℓ / (m r²)`. Then during every radial period, starting at any time `t`, the angle advances by
twice the apsidal angle: `θ(t + T) - θ(t) = 2 Δθ`. -/
theorem sub_eq_two_mul_apsidalAngle_of_forall_hasDerivAt_effectivePotential {θ : ℝ → ℝ}
    (hθ : ∀ t, HasDerivAt θ (ℓ / (m * (γ t).1 ^ 2)) t) (t : ℝ) :
    θ (t + radialPeriod m U ℓ E r₁ r₂) - θ t = 2 * apsidalAngle m U ℓ E r₁ r₂ := by
  set T := radialPeriod m U ℓ E r₁ r₂
  have hper := periodic_of_forall_hasDerivAt_effectivePotential hm hr₁ h₁₂ hU hE₁ hE₂ hlt hd₁ hd₂
    hγ h₀ hE
  -- The advance `θ(u + T) - θ(u)` has zero derivative, since the radius is `T`-periodic.
  have hd (u : ℝ) : HasDerivAt (fun u ↦ θ (u + T) - θ u) 0 u := by
    have h := ((hθ (u + T)).comp_add_const u T).sub (hθ u)
    rwa [hper u, sub_self] at h
  have hconst := is_const_of_deriv_eq_zero (fun u ↦ (hd u).differentiableAt) fun u ↦ (hd u).deriv
  -- At a passage through the inner turning point it is twice the apsidal angle.
  obtain ⟨s, hs⟩ := exists_fst_eq_of_forall_hasDerivAt_effectivePotential hm hr₁ h₁₂ hU hE₁ hE₂
    hlt hd₁ hd₂ hγ h₀ hE
  obtain ⟨t₂, ⟨hs₂, h₂T⟩, h₂, hT, hpos, hneg⟩ :=
    exists_mem_Ioo_fst_eq_of_forall_hasDerivAt_effectivePotential hm hr₁ h₁₂ hU hE₁ hE₂ hlt hd₁
      hd₂ hγ h₀ hE hs
  have hmem (u : ℝ) (hu : u ∈ Ioo s t₂ ∨ u ∈ Ioo t₂ (s + T)) : (γ u).1 ∈ Ioo r₁ r₂ :=
    (momentum_ne_zero_iff hm hr₁ h₁₂ hU hE₁ hE₂ hlt hd₁ hd₂ hγ h₀ hE u).1 <|
      hu.elim (fun hu ↦ (hpos u hu).ne') fun hu ↦ (hneg u hu).ne
  have hpos' (u : ℝ) : 0 < (γ u).1 := hr₁.trans_le (mem_Icc_of_forall_hasDerivAt_effectivePotential
    hm hr₁ h₁₂ hU hE₁ hE₂ hlt hd₁ hd₂ hγ h₀ hE u).1
  rw [hconst t s]
  exact sub_eq_two_mul_apsidalAngle hm hs₂.le h₂T.le (fun u _ ↦ hγ u) (fun u _ ↦ hpos' u)
    (fun u _ ↦ hU.differentiableAt (Ioi_mem_nhds (hpos' u)))
    (mem_Icc_and_eq hm hr₁ h₁₂ hU hE₁ hE₂ hlt hd₁ hd₂ hγ h₀ hE s).2 hlt (Or.inl ⟨hs, h₂⟩)
    (hT.trans hs.symm) (fun u hu ↦ hmem u (Or.inl hu)) (fun u hu ↦ hmem u (Or.inr hu))
    fun u _ ↦ hθ u

end Well

end TauCeti
