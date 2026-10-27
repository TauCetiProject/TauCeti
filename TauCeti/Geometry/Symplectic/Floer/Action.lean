/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Energy
import TauCeti.Geometry.Symplectic.Area.Basic

/-!
# The Hamiltonian action and the energy of cylindrical Floer solutions

Let `(V, ω)` be a symplectic vector space and `H : ℝ → V → ℝ` a time-dependent Hamiltonian. For
a loop `x : [0, 1] → V` with `x 1 = x 0`, the symplectic area of the loop is
`a(x) = ½ ∫₀¹ ω(x(t), x'(t)) dt` (`TauCeti.SymplecticForm.loopArea`). It is the symplectic area
`∫ D^* ω` of the cone `D(r, t) = r x(t)` bounding the loop
(`SymplecticForm.integral_symplecticForm_fderiv_smul_eq_loopArea`). The Hamiltonian action of the
loop capped by this disc is

`A_H(x) = a(x) + ∫₀¹ H(t, x(t)) dt`

(`TauCeti.SymplecticForm.hamiltonianAction`), the convention `A_H(x, D) = ∫ D^* ω + ∫ H dt` of
capped Floer theory with positive ends as inputs.

On a region of the domain where the Hamiltonian perturbation is cylindrical, `K = H_t dt`, such as
a strip-like end or a neck of a punctured Floer domain, the curvature of `K` vanishes and the
boundary terms of the Floer energy identity combine into actions. For a map `u` on
`[a, b] × [0, 1]` whose bottom and top sides agree, so that each `t ↦ u(s, t)` is a loop:

* the symplectic area of `u` is `a(u(b, ·)) - a(u(a, ·))`
  (`SymplecticForm.integral_symplecticForm_fderiv_eq_loopArea_sub`), by Green's formula for the
  primitive `λₓ(v) = ½ ω(x, v)` (`SymplecticForm.integral_fderiv_apply_prod_Icc`);
* the Floer energy of `u` is `A_H(u(b, ·)) - A_H(u(a, ·))`
  (`SymplecticForm.integral_floerEnergyDensity_eq_hamiltonianAction_sub`), by the energy identity
  `TauCeti.SymplecticForm.integral_floerEnergyDensity`.

For a solution of the Floer equation `∂_s u + J (∂_t u - X_{H_t}(u)) = 0` with `J` tamed by `ω`,
the energy density is nonnegative, so the action increases along the cylinder
(`SymplecticForm.hamiltonianAction_le_hamiltonianAction`), and the energy of a Floer solution on
the whole cylinder `ℝ × [0, 1]` is the difference of the limiting actions at its two ends
(`SymplecticForm.lintegral_floerEnergyDensity_eq_of_tendsto`). These are the end and neck terms of
the energy identity `E = A₁ + A₂ - A₀ + ω(A) - ∫ R_K` for pairs of pants.

## Main definitions

* `TauCeti.SymplecticForm.loopArea`: the symplectic area `½ ∫₀¹ ω(x, x')` of a loop.
* `TauCeti.SymplecticForm.hamiltonianAction`: the Hamiltonian action of a loop.

## Main results

* `SymplecticForm.integral_symplecticForm_fderiv_eq_loopArea_sub`: the symplectic area of a map
  on `[a, b] × [0, 1]` with matching bottom and top sides.
* `SymplecticForm.integral_symplecticForm_fderiv_smul_eq_loopArea`: the loop area is the area of
  the cone over the loop.
* `SymplecticForm.integral_floerEnergyDensity_eq_hamiltonianAction_sub`: the energy of a map over
  `[a, b] × [0, 1]` for a cylindrical perturbation is the change of action.
* `SymplecticForm.hamiltonianAction_le_hamiltonianAction`: the action increases along Floer
  solutions.
* `SymplecticForm.lintegral_floerEnergyDensity_eq_of_tendsto`: the energy of a Floer solution on
  the whole cylinder is the difference of its limiting actions.

## References

* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, Section 8.1 and the
  chapter on Floer homology, on the action functional and the energy identity.
* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lecture 1.
-/

public section

open Function MeasureTheory Set Filter Topology

namespace TauCeti.SymplecticForm

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

section Action

/-- The symplectic area `½ ∫₀¹ ω(x(t), x'(t)) dt` of a loop `x : [0, 1] → V`: the integral of the
primitive `λₓ(v) = ½ ω(x, v)` of `ω` along the loop. For a closed loop it is the symplectic area
of the cone `r x(t)` bounding it (`SymplecticForm.integral_symplecticForm_fderiv_smul_eq_loopArea`).
-/
noncomputable def loopArea (ω : SymplecticForm V) (x : ℝ → V) : ℝ :=
  (1 / 2 : ℝ) * ∫ t in (0 : ℝ)..1, ω (x t) (deriv x t)

theorem loopArea_def (ω : SymplecticForm V) (x : ℝ → V) :
    ω.loopArea x = (1 / 2 : ℝ) * ∫ t in (0 : ℝ)..1, ω (x t) (deriv x t) :=
  (rfl)

/-- A constant loop has zero symplectic area. -/
@[simp]
theorem loopArea_const (ω : SymplecticForm V) (v : V) : ω.loopArea (fun _ ↦ v) = 0 := by
  simp [loopArea_def]

/-- The Hamiltonian action `A_H(x) = ½ ∫₀¹ ω(x, x') dt + ∫₀¹ H(t, x(t)) dt` of a loop `x`, for a
time-dependent Hamiltonian `H`. It is the action `∫ D^* ω + ∫ H dt` of the loop capped by the
cone `D(r, t) = r x(t)`, with the sign convention in which the action increases along Floer
solutions, so that positive ends are inputs. -/
noncomputable def hamiltonianAction (ω : SymplecticForm V) (H : ℝ → V → ℝ) (x : ℝ → V) : ℝ :=
  ω.loopArea x + ∫ t in (0 : ℝ)..1, H t (x t)

theorem hamiltonianAction_def (ω : SymplecticForm V) (H : ℝ → V → ℝ) (x : ℝ → V) :
    ω.hamiltonianAction H x = ω.loopArea x + ∫ t in (0 : ℝ)..1, H t (x t) :=
  (rfl)

/-- The action of a constant loop is the time average of the Hamiltonian at that point. -/
@[simp]
theorem hamiltonianAction_const (ω : SymplecticForm V) (H : ℝ → V → ℝ) (v : V) :
    ω.hamiltonianAction H (fun _ ↦ v) = ∫ t in (0 : ℝ)..1, H t v := by
  simp [hamiltonianAction_def]

end Action

section Area

variable [FiniteDimensional ℝ V] {u : ℝ × ℝ → V} {a b : ℝ}

/-- **The symplectic area of a cylinder.** Let `u` be `C²` near `[a, b] × [0, 1]`, with
`u(s, 1) = u(s, 0)` for `s ∈ [a, b]`, so that each `t ↦ u(s, t)` is a loop. Then the symplectic
area of `u` over the rectangle is the area of the loop at `s = b` minus the area of the loop at
`s = a`. -/
theorem integral_symplecticForm_fderiv_eq_loopArea_sub (ω : SymplecticForm V) (hab : a ≤ b)
    (hu : ∀ z ∈ Icc a b ×ˢ Icc 0 1, ContDiffAt ℝ 2 u z)
    (hper : ∀ s ∈ Icc a b, u (s, 1) = u (s, 0)) :
    ∫ z in Icc a b ×ˢ Icc 0 1,
        ω (fderiv ℝ u z stdComplexLineReal) (fderiv ℝ u z stdComplexLineImag) =
      ω.loopArea (fun t ↦ u (b, t)) - ω.loopArea (fun t ↦ u (a, t)) := by
  have hR : Icc a b ×ˢ Icc (0 : ℝ) 1 = Icc (a, 0) (b, 1) := (Icc_prod_Icc _ _ _ _)
  -- The partial derivatives of `u` are the derivatives of its restrictions to lines.
  have hpartial {s t : ℝ} (hs : s ∈ Icc a b) (ht : t ∈ Icc (0 : ℝ) 1) :
      HasDerivAt (fun s ↦ u (s, t)) (fderiv ℝ u (s, t) (1, 0)) s ∧
        HasDerivAt (fun t ↦ u (s, t)) (fderiv ℝ u (s, t) (0, 1)) t := by
    have hd := ((hu (s, t) ⟨hs, ht⟩).differentiableAt (by norm_num)).hasFDerivAt
    exact ⟨hd.comp_hasDerivAt s ((hasDerivAt_id s).prodMk (hasDerivAt_const s t)),
      hd.comp_hasDerivAt t ((hasDerivAt_const t s).prodMk (hasDerivAt_id t))⟩
  -- The vertical sides integrate the primitive along the loops `t ↦ u(s, t)`.
  have hvert {s : ℝ} (hs : s ∈ Icc a b) :
      ∫ t in (0 : ℝ)..1, ω (u (s, t)) (fderiv ℝ u (s, t) (0, 1)) =
        ∫ t in (0 : ℝ)..1, ω (u (s, t)) (deriv (fun t ↦ u (s, t)) t) := by
    refine intervalIntegral.integral_congr fun t ht ↦ ?_
    rw [uIcc_of_le zero_le_one] at ht
    rw [(hpartial hs ht).2.deriv]
  -- The bottom and top sides agree, so their contributions cancel.
  have hhor : ∫ s in a..b, ω (u (s, 1)) (fderiv ℝ u (s, 1) (1, 0)) =
      ∫ s in a..b, ω (u (s, 0)) (fderiv ℝ u (s, 0) (1, 0)) := by
    rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab,
      integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
    refine setIntegral_congr_fun measurableSet_Ioo fun s hs ↦ ?_
    have hs' : s ∈ Icc a b := Ioo_subset_Icc_self hs
    have heq : (fun s ↦ u (s, 1)) =ᶠ[𝓝 s] fun s ↦ u (s, 0) :=
      eventually_of_mem (Icc_mem_nhds hs.1 hs.2) hper
    rw [← (hpartial hs' ⟨zero_le_one, le_rfl⟩).1.deriv,
      ← (hpartial hs' ⟨le_rfl, zero_le_one⟩).1.deriv, heq.deriv_eq, hper s hs']
  have harea := ω.integral_fderiv_apply_prod_Icc (Prod.mk_le_mk.2 ⟨hab, zero_le_one⟩) (hR ▸ hu)
  rw [hvert ⟨hab, le_rfl⟩, hvert ⟨le_rfl, hab⟩, hhor, ← hR] at harea
  rw [loopArea_def, loopArea_def, stdComplexLineReal_eq, stdComplexLineImag_eq, harea]
  ring

/-- **The loop area is the area of a cap.** For a loop `x` that is `C²` near `[0, 1]` with
`x 1 = x 0`, the symplectic area of the cone `D(r, t) = r x(t)` over `[0, 1] × [0, 1]`, a disc
bounding `x`, is the loop area of `x`. -/
theorem integral_symplecticForm_fderiv_smul_eq_loopArea (ω : SymplecticForm V) {x : ℝ → V}
    (hx : ∀ t ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ 2 x t) (hx₁ : x 1 = x 0) :
    ∫ z in Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1,
        ω (fderiv ℝ (fun w : ℝ × ℝ ↦ w.1 • x w.2) z stdComplexLineReal)
          (fderiv ℝ (fun w : ℝ × ℝ ↦ w.1 • x w.2) z stdComplexLineImag) =
      ω.loopArea x := by
  rw [integral_symplecticForm_fderiv_eq_loopArea_sub (u := fun w : ℝ × ℝ ↦ w.1 • x w.2) ω
    zero_le_one
    (fun z hz ↦ contDiffAt_fst.smul ((hx z.2 hz.2).comp z contDiffAt_snd))
    (fun s _ ↦ by simp only [hx₁])]
  simp

end Area

section Energy

variable [FiniteDimensional ℝ V] {H : ℝ → V → ℝ} {u : ℝ × ℝ → V} {U : Set (ℝ × ℝ)} {a b : ℝ}

omit [FiniteDimensional ℝ V] in
/-- The cylindrical perturbation `K = H_t dt` of a `C¹` Hamiltonian is `C¹`. -/
private theorem contDiff_uncurry_cylindrical (hH : ContDiff ℝ 1 (uncurry H)) :
    ContDiff ℝ 1 (uncurry fun (w : ℝ × ℝ) ↦ H w.2) :=
  hH.comp ((contDiff_snd.comp contDiff_fst).prodMk contDiff_snd)

/-- **The energy identity for a cylindrical perturbation.** Let `H` be a `C¹` time-dependent
Hamiltonian and let `u` be `C²` on an open neighbourhood `U` of `[a, b] × [0, 1]`, with
`u(s, 1) = u(s, 0)` for `s ∈ [a, b]`. For the cylindrical perturbation `K = H_t dt`, the Floer
energy of `u` over the rectangle is the action of the loop at `s = b` minus the action of the loop
at `s = a`. -/
theorem integral_floerEnergyDensity_eq_hamiltonianAction_sub (ω : SymplecticForm V)
    (hH : ContDiff ℝ 1 (uncurry H)) (hU : IsOpen U) (hu : ContDiffOn ℝ 2 u U) (hab : a ≤ b)
    (hRU : Icc a b ×ˢ Icc 0 1 ⊆ U) (hper : ∀ s ∈ Icc a b, u (s, 1) = u (s, 0)) :
    ∫ z in Icc a b ×ˢ Icc 0 1, ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u z =
      ω.hamiltonianAction H (fun t ↦ u (b, t)) - ω.hamiltonianAction H (fun t ↦ u (a, t)) := by
  have hR : Icc a b ×ˢ Icc (0 : ℝ) 1 = Icc (a, 0) (b, 1) := (Icc_prod_Icc _ _ _ _)
  have h := ω.integral_floerEnergyDensity (Ks := fun _ _ ↦ 0) (Kt := fun w ↦ H w.2) hU
    (hu.of_le one_le_two) contDiffOn_const (contDiff_uncurry_cylindrical hH).contDiffOn
    (Prod.mk_le_mk.2 ⟨hab, zero_le_one⟩) (hR ▸ hRU)
  simp only [hamiltonianCurvature_cylindrical, intervalIntegral.integral_zero, integral_zero,
    ← hR] at h
  rw [h, ω.integral_symplecticForm_fderiv_eq_loopArea_sub hab
      (fun z hz ↦ hu.contDiffAt (hU.mem_nhds (hRU hz))) hper,
    hamiltonianAction_def, hamiltonianAction_def]
  ring

/-- The Floer energy density of a solution of the Floer equation
`∂_s u + J (∂_t u - X_{H_t}(u)) = 0` for the cylindrical perturbation `K = H_t dt` is
nonnegative when `J` is tamed by `ω`. -/
theorem floerEnergyDensity_cylindrical_nonneg (ω : SymplecticForm V) {J : AlmostComplexStructure V}
    (hJ : ω.Tames J) {z : ℝ × ℝ}
    (hfloer : fderiv ℝ u z stdComplexLineReal +
      J (fderiv ℝ u z stdComplexLineImag - ω.hamiltonianVectorField (H z.2) (u z)) = 0) :
    0 ≤ ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u z :=
  ω.floerEnergyDensity_nonneg hJ <|
    (ω.isComplexLinearMap_perturbedFDeriv_iff J _ _ u z).2 (by simpa using hfloer)

/-- **The action increases along Floer solutions.** Under the hypotheses of
`TauCeti.SymplecticForm.integral_floerEnergyDensity_eq_hamiltonianAction_sub`, if `u` solves the
Floer equation `∂_s u + J (∂_t u - X_{H_t}(u)) = 0` on the rectangle for an almost complex
structure `J` tamed by `ω`, then the action of the loop at `s = a` is at most that of the loop at
`s = b`. -/
theorem hamiltonianAction_le_hamiltonianAction (ω : SymplecticForm V)
    {J : AlmostComplexStructure V} (hJ : ω.Tames J) (hH : ContDiff ℝ 1 (uncurry H))
    (hU : IsOpen U) (hu : ContDiffOn ℝ 2 u U) (hab : a ≤ b) (hRU : Icc a b ×ˢ Icc 0 1 ⊆ U)
    (hper : ∀ s ∈ Icc a b, u (s, 1) = u (s, 0))
    (hfloer : ∀ z ∈ Icc a b ×ˢ Icc 0 1, fderiv ℝ u z stdComplexLineReal +
      J (fderiv ℝ u z stdComplexLineImag - ω.hamiltonianVectorField (H z.2) (u z)) = 0) :
    ω.hamiltonianAction H (fun t ↦ u (a, t)) ≤ ω.hamiltonianAction H (fun t ↦ u (b, t)) := by
  have h := ω.integral_floerEnergyDensity_eq_hamiltonianAction_sub hH hU hu hab hRU hper
  have hnonneg := setIntegral_nonneg (μ := volume) (measurableSet_Icc.prod measurableSet_Icc)
    fun z hz ↦ ω.floerEnergyDensity_cylindrical_nonneg hJ (hfloer z hz)
  linarith

/-- **The energy of a Floer cylinder.** Let `H` be a `C¹` time-dependent Hamiltonian and let `u`
be `C²` on an open neighbourhood `U` of `ℝ × [0, 1]`, with `u(s, 1) = u(s, 0)` for all `s`,
solving the Floer equation `∂_s u + J (∂_t u - X_{H_t}(u)) = 0` there for an almost complex
structure `J` tamed by `ω`. If the actions of the loops `t ↦ u(s, t)` tend to `A₁` as `s → -∞`
and to `A₂` as `s → ∞`, then the energy of `u` is `A₂ - A₁`. -/
theorem lintegral_floerEnergyDensity_eq_of_tendsto (ω : SymplecticForm V)
    {J : AlmostComplexStructure V} (hJ : ω.Tames J) (hH : ContDiff ℝ 1 (uncurry H))
    (hU : IsOpen U) (hu : ContDiffOn ℝ 2 u U) (hRU : (univ : Set ℝ) ×ˢ Icc 0 1 ⊆ U)
    (hper : ∀ s, u (s, 1) = u (s, 0))
    (hfloer : ∀ z ∈ (univ : Set ℝ) ×ˢ Icc 0 1, fderiv ℝ u z stdComplexLineReal +
      J (fderiv ℝ u z stdComplexLineImag - ω.hamiltonianVectorField (H z.2) (u z)) = 0)
    {A₁ A₂ : ℝ}
    (hbot : Tendsto (fun s ↦ ω.hamiltonianAction H (fun t ↦ u (s, t))) atBot (𝓝 A₁))
    (htop : Tendsto (fun s ↦ ω.hamiltonianAction H (fun t ↦ u (s, t))) atTop (𝓝 A₂)) :
    ∫⁻ z in (univ : Set ℝ) ×ˢ Icc 0 1,
        ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u z) =
      ENNReal.ofReal (A₂ - A₁) := by
  -- Exhaust the cylinder by the rectangles `[-n, n] × [0, 1]`.
  set R : ℕ → Set (ℝ × ℝ) := fun n ↦ Icc (-(n : ℝ)) n ×ˢ Icc 0 1
  have hRsub (n : ℕ) : R n ⊆ (univ : Set ℝ) ×ˢ Icc 0 1 := prod_mono (subset_univ _) le_rfl
  have hmono : Monotone R := fun m n hmn ↦ prod_mono
    (Icc_subset_Icc (neg_le_neg (Nat.cast_le.mpr hmn)) (Nat.cast_le.mpr hmn)) le_rfl
  have hunion : ⋃ n, R n = (univ : Set ℝ) ×ˢ Icc 0 1 := by
    refine (iUnion_subset hRsub).antisymm fun z hz ↦ ?_
    obtain ⟨n, hn⟩ := exists_nat_ge |z.1|
    exact mem_iUnion.mpr ⟨n, ⟨abs_le.mp hn, hz.2⟩⟩
  have hcont := ω.continuousOn_floerEnergyDensity (Ks := fun _ _ ↦ 0) (Kt := fun w ↦ H w.2) hU
    (hu.of_le one_le_two) contDiffOn_const (contDiff_uncurry_cylindrical hH).contDiffOn
  -- On each rectangle the energy is the change of action.
  have hE (n : ℕ) : ∫⁻ z in R n,
      ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u z) =
        ENNReal.ofReal (ω.hamiltonianAction H (fun t ↦ u (n, t)) -
          ω.hamiltonianAction H (fun t ↦ u (-(n : ℝ), t))) := by
    rw [← ω.integral_floerEnergyDensity_eq_hamiltonianAction_sub hH hU hu
        (neg_le_self n.cast_nonneg) ((hRsub n).trans hRU) fun s _ ↦ hper s,
      ofReal_integral_eq_lintegral_ofReal
        ((hcont.mono ((hRsub n).trans hRU)).integrableOn_compact
          (isCompact_Icc.prod isCompact_Icc))
        (ae_restrict_of_forall_mem (measurableSet_Icc.prod measurableSet_Icc)
          fun z hz ↦ ω.floerEnergyDensity_cylindrical_nonneg hJ (hfloer z (hRsub n hz)))]
  -- The energies of the rectangles increase to the energy of the cylinder.
  have hlim : Tendsto (fun n ↦ ∫⁻ z in R n,
      ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u z)) atTop
      (𝓝 (∫⁻ z in (univ : Set ℝ) ×ˢ Icc 0 1,
        ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u z))) := by
    rw [← hunion, setLIntegral_iUnion_of_directed _ hmono.directed_le]
    exact tendsto_atTop_iSup fun m n hmn ↦ lintegral_mono' (Measure.restrict_mono (hmono hmn)
      le_rfl) le_rfl
  refine tendsto_nhds_unique hlim ?_
  simp only [hE]
  exact (ENNReal.continuous_ofReal.tendsto _).comp
    ((htop.comp tendsto_natCast_atTop_atTop).sub
      (hbot.comp (tendsto_neg_atTop_atBot.comp tendsto_natCast_atTop_atTop)))

end Energy

end TauCeti.SymplecticForm
