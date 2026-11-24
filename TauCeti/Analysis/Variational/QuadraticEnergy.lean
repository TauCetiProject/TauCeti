/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.LaxMilgram
public import Mathlib.Algebra.QuadraticDiscriminant
public import Mathlib.Analysis.Calculus.FDeriv.Basic

/-!
# Quadratic energies of Hermitian forms

Let `a : V →L⋆[𝕜] V →L[𝕜] 𝕜` be a bounded Hermitian form (`a u v = star (a v u)`) on a normed
space over `𝕜 = ℝ` or `ℂ`, conjugate linear in its first argument, and let `ℓ : StrongDual 𝕜 V`
be a forcing functional. The **quadratic energy**

`E(u) = re (a u u) - 2 re (ℓ u)`

(`ContinuousLinearMap.quadraticEnergy`) is a real-valued function whose minimizers solve the weak
equation `a u v = ℓ v` (and conversely when `re (a w w) ≥ 0`). This file proves:

* the exact expansion `E(u + h) = E(u) + 2 re (a u h - ℓ h) + re (a h h)`, and along a real line
  `E(u + t v) = E(u) + 2 t re (a u v - ℓ v) + t² re (a v v)`
  (`ContinuousLinearMap.quadraticEnergy_add`, `ContinuousLinearMap.quadraticEnergy_add_smul`);
* the real Fréchet derivative `dE(u) v = 2 re (a u v - ℓ v)` on the real restriction of scalars
  (`ContinuousLinearMap.hasFDerivAt_quadraticEnergy`);
* a minimizer of `E` on an affine subspace `u + W` solves the weak equation `a u v = ℓ v` for
  every `v ∈ W` (`ContinuousLinearMap.apply_eq_of_forall_le_quadraticEnergy_add`). The real part
  of the equation comes from the expansion; over `ℂ` the imaginary part comes from testing with
  `I • v`, since the real-part identity alone does not determine `a u v`;
* conversely, at a weak solution the energy gap is exactly `E(u + h) - E(u) = re (a h h)`, so the
  weak equation and the minimum property are equivalent when the energy of the form is nonnegative
  on `W` (`ContinuousLinearMap.forall_le_quadraticEnergy_add_iff`,
  `ContinuousLinearMap.isMinOn_quadraticEnergy_iff`);
* for a form with nonnegative energy, the Cauchy–Schwarz inequality
  `‖a u v‖² ≤ re (a u u) re (a v v)` (`ContinuousLinearMap.norm_apply_sq_le_of_hermitian`) and
  the kernel identity `re (a u u) = 0 ↔ a u = 0`
  (`ContinuousLinearMap.re_apply_self_eq_zero_iff`);
* for a coercive form, `c ‖w - u‖² ≤ E(w) - E(u)` at the weak solution `u`, uniqueness of weak
  solutions, norm convergence of near-minimizers, and Lipschitz dependence of the solution on the
  forcing;
* on a Hilbert space, the minimizer is the Lax–Milgram solution
  `InnerProductSpace.solutionOfFunctional` (and `InnerProductSpace.formSolutionMap` for the
  forcing `v ↦ ⟪h, j v⟫`), and over `ℝ` it is `IsCoercive.solutionOfFunctional`
  (`IsCoercive.isMinOn_quadraticEnergy_iff_eq_solutionOfFunctional`). The identification with
  `IsCoercive.formSolutionMap` is `IsCoercive.isMinOn_quadraticEnergy_iff_eq_formSolutionMap`,
  in `TauCeti.Analysis.InnerProductSpace.Variational.Spectrum`, where that map is defined.

These are the first-variation facts needed to derive Euler–Lagrange equations of quadratic
energies on constraint sets, and to identify their minima with eigenvectors.

## References

* J. K. Hunter, *Notes on Partial Differential Equations*, Proposition 4.5, Corollary 4.6 and
  Theorem 4.20 (the Dirichlet energy and the Lax–Milgram theorem).
-/

public section

open RCLike Filter Topology Set

namespace ContinuousLinearMap

section Seminormed

variable {𝕜 V : Type*} [RCLike 𝕜] [SeminormedAddCommGroup V] [NormedSpace 𝕜 V]

/-- The **quadratic energy** `E(u) = re (a u u) - 2 re (ℓ u)` of a bounded sesquilinear form `a`
with forcing functional `ℓ`. When `a` is Hermitian, its minimizers on `u + W` solve the weak
equation `a u v = ℓ v` on `W`; the converse holds when `re (a w w) ≥ 0` on `W`. -/
def quadraticEnergy (a : V →L⋆[𝕜] V →L[𝕜] 𝕜) (ℓ : StrongDual 𝕜 V) (u : V) : ℝ :=
  re (a u u) - 2 * re (ℓ u)

variable (a : V →L⋆[𝕜] V →L[𝕜] 𝕜) (ℓ : StrongDual 𝕜 V)

theorem quadraticEnergy_apply (u : V) :
    a.quadraticEnergy ℓ u = re (a u u) - 2 * re (ℓ u) :=
  (rfl)

@[simp]
theorem quadraticEnergy_apply_zero : a.quadraticEnergy ℓ 0 = 0 := by
  simp [quadraticEnergy_apply]

variable {a}

/-- **The exact expansion of a quadratic energy.** -/
theorem quadraticEnergy_add (ha : ∀ u v, a u v = star (a v u)) (u h : V) :
    a.quadraticEnergy ℓ (u + h) =
      a.quadraticEnergy ℓ u + 2 * re (a u h - ℓ h) + re (a h h) := by
  have hre : re (a h u) = re (a u h) := by rw [ha h u, star_def, conj_re]
  simp only [quadraticEnergy_apply, map_add, add_apply, map_sub]
  linarith

/-- **The expansion of a quadratic energy along a real line.** -/
theorem quadraticEnergy_add_smul (ha : ∀ u v, a u v = star (a v u)) (u v : V) (t : ℝ) :
    a.quadraticEnergy ℓ (u + (t : 𝕜) • v) =
      a.quadraticEnergy ℓ u + 2 * t * re (a u v - ℓ v) + t ^ 2 * re (a v v) := by
  rw [quadraticEnergy_add ℓ ha]
  simp only [map_smulₛₗ, smul_apply, smul_eq_mul, conj_ofReal, RingHom.id_apply,
    ← mul_sub, mul_assoc, re_ofReal_mul]
  ring

/-- **The weak equation at a minimizer on an affine subspace.** If `u` minimizes the quadratic
energy of a Hermitian form on `u + W`, then `a u v = ℓ v` for every `v ∈ W`. -/
theorem apply_eq_of_forall_le_quadraticEnergy_add (ha : ∀ u v, a u v = star (a v u))
    {W : Submodule 𝕜 V} {u : V}
    (hmin : ∀ w ∈ W, a.quadraticEnergy ℓ u ≤ a.quadraticEnergy ℓ (u + w)) {v : V} (hv : v ∈ W) :
    a u v = ℓ v := by
  -- The real part of `a u v - ℓ v` vanishes in every direction of `W`, by the expansion.
  have hre : ∀ v ∈ W, re (a u v - ℓ v) = 0 := fun v hv => by
    have hd := discrim_le_zero (K := ℝ) (a := re (a v v)) (b := 2 * re (a u v - ℓ v)) (c := 0)
      fun t => by
        have := hmin _ (W.smul_mem (t : 𝕜) hv)
        rw [quadraticEnergy_add_smul ℓ ha] at this
        nlinarith
    rw [discrim] at hd
    nlinarith [sq_nonneg (re (a u v - ℓ v))]
  -- Its imaginary part is minus the real part in the direction `I • v`.
  have him := hre _ (W.smul_mem I hv)
  simp only [map_smul, smul_eq_mul, ← mul_sub, I_mul_re, neg_eq_zero] at him
  rw [← sub_eq_zero]
  exact RCLike.ext (by simpa using hre v hv) (by simpa using him)

/-- **The energy gap at a weak solution.** If `a u v = ℓ v` for every `v ∈ W`, then the energy
increases from `u` to `u + h` by exactly `re (a h h)` for every `h ∈ W`. -/
theorem quadraticEnergy_add_of_forall_apply_eq (ha : ∀ u v, a u v = star (a v u))
    {W : Submodule 𝕜 V} {u h : V} (hu : ∀ v ∈ W, a u v = ℓ v) (hh : h ∈ W) :
    a.quadraticEnergy ℓ (u + h) = a.quadraticEnergy ℓ u + re (a h h) := by
  rw [quadraticEnergy_add ℓ ha, hu h hh, sub_self, map_zero, mul_zero, add_zero]

/-- For a Hermitian form whose energy is nonnegative on `W`, `u` minimizes the quadratic energy on
`u + W` if and only if it solves the weak equation `a u v = ℓ v` for every `v ∈ W`. -/
theorem forall_le_quadraticEnergy_add_iff (ha : ∀ u v, a u v = star (a v u))
    {W : Submodule 𝕜 V} (hq : ∀ w ∈ W, 0 ≤ re (a w w)) {u : V} :
    (∀ w ∈ W, a.quadraticEnergy ℓ u ≤ a.quadraticEnergy ℓ (u + w)) ↔ ∀ v ∈ W, a u v = ℓ v :=
  ⟨fun hmin _ hv => apply_eq_of_forall_le_quadraticEnergy_add ℓ ha hmin hv, fun hu w hw => by
    rw [quadraticEnergy_add_of_forall_apply_eq ℓ ha hu hw]
    linarith [hq w hw]⟩

/-- For a Hermitian form with nonnegative energy, `u` is a global minimizer of the quadratic
energy if and only if it solves the weak equation `a u = ℓ`. -/
theorem isMinOn_quadraticEnergy_iff (ha : ∀ u v, a u v = star (a v u))
    (hq : ∀ w, 0 ≤ re (a w w)) {u : V} :
    IsMinOn (a.quadraticEnergy ℓ) univ u ↔ a u = ℓ := by
  have h := forall_le_quadraticEnergy_add_iff ℓ ha (W := ⊤) (fun w _ => hq w) (u := u)
  simp only [Submodule.mem_top, forall_const] at h
  rw [ContinuousLinearMap.ext_iff, ← h, isMinOn_univ_iff]
  exact ⟨fun hmin w => hmin (u + w), fun hmin w => by simpa using hmin (w - u)⟩

/-- **Cauchy–Schwarz inequality for a nonnegative Hermitian form**:
`‖a u v‖² ≤ re (a u u) re (a v v)`. -/
theorem norm_apply_sq_le_of_hermitian (ha : ∀ u v, a u v = star (a v u))
    (hq : ∀ w, 0 ≤ re (a w w)) (u v : V) :
    ‖a u v‖ ^ 2 ≤ re (a u u) * re (a v v) := by
  -- A nonnegative Hermitian form is a pre-inner product, whose Cauchy–Schwarz inequality applies.
  let _ : PreInnerProductSpace.Core 𝕜 V :=
    { inner x y := a x y
      conj_inner_symm x y := by rw [ha x y, starRingEnd_apply]
      re_inner_nonneg := hq
      add_left x y z := by simp
      smul_left x y r := by simp }
  -- The inner product of this core is `a` by construction.
  have h : ‖a u v‖ * ‖a v u‖ ≤ re (a u u) * re (a v v) :=
    InnerProductSpace.Core.inner_mul_inner_self_le u v
  rwa [show ‖a v u‖ = ‖a u v‖ by rw [ha v u, norm_star], ← sq] at h

/-- **The kernel identity for a nonnegative Hermitian form**: `u` lies in the kernel
(`a u v = 0` for all `v`) exactly when its energy vanishes. -/
theorem re_apply_self_eq_zero_iff (ha : ∀ u v, a u v = star (a v u))
    (hq : ∀ w, 0 ≤ re (a w w)) {u : V} :
    re (a u u) = 0 ↔ a u = 0 := by
  refine ⟨fun hu => ContinuousLinearMap.ext fun v => ?_, fun hu => by simp [hu]⟩
  have h := norm_apply_sq_le_of_hermitian ha hq u v
  rw [hu, zero_mul] at h
  exact norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp (le_antisymm h (sq_nonneg _)))

/-- **Coercive energy gap.** If the energy of a Hermitian form dominates `c ‖w‖²` on `W` and `u`
solves the weak equation on `W`, then `c ‖w - u‖² ≤ E(w) - E(u)` for every `w ∈ u + W`. -/
theorem mul_norm_sub_sq_le_quadraticEnergy_sub (ha : ∀ u v, a u v = star (a v u))
    {W : Submodule 𝕜 V} {c : ℝ} (hc : ∀ w ∈ W, c * ‖w‖ ^ 2 ≤ re (a w w)) {u w : V}
    (hu : ∀ v ∈ W, a u v = ℓ v) (hw : w - u ∈ W) :
    c * ‖w - u‖ ^ 2 ≤ a.quadraticEnergy ℓ w - a.quadraticEnergy ℓ u := by
  have h := quadraticEnergy_add_of_forall_apply_eq ℓ ha hu hw
  rw [add_sub_cancel] at h
  linarith [hc _ hw]

/-- **Near-minimizers converge in norm.** For a Hermitian form whose energy dominates `c ‖w‖²`
on `W` with `0 < c`, points of `u + W` whose energies tend to the energy of the weak solution `u`
converge to `u` in norm. -/
theorem tendsto_of_tendsto_quadraticEnergy (ha : ∀ u v, a u v = star (a v u))
    {W : Submodule 𝕜 V} {c : ℝ} (hc0 : 0 < c) (hc : ∀ w ∈ W, c * ‖w‖ ^ 2 ≤ re (a w w)) {u : V}
    (hu : ∀ v ∈ W, a u v = ℓ v) {ι : Type*} {l : Filter ι} {x : ι → V} (hx : ∀ i, x i - u ∈ W)
    (hE : Tendsto (fun i => a.quadraticEnergy ℓ (x i)) l (𝓝 (a.quadraticEnergy ℓ u))) :
    Tendsto x l (𝓝 u) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hlim : Tendsto (fun i => √((a.quadraticEnergy ℓ (x i) - a.quadraticEnergy ℓ u) / c)) l
      (𝓝 0) := by
    have := ((hE.sub_const (a.quadraticEnergy ℓ u)).div_const c).sqrt
    rwa [sub_self, zero_div, Real.sqrt_zero] at this
  refine squeeze_zero (fun _ => norm_nonneg _) (fun i => ?_) hlim
  rw [← abs_norm]
  refine Real.abs_le_sqrt ?_
  rw [le_div_iff₀ hc0, mul_comm]
  exact mul_norm_sub_sq_le_quadraticEnergy_sub ℓ ha hc hu (hx i)

/-- **Lipschitz dependence on the forcing.** If the energy of `a` dominates `c ‖w‖²` on `W`, then
solutions of the weak equations `a u v = ℓ v` and `a u' v = ℓ' v` on `W` that differ by an element
of `W` satisfy `c ‖u - u'‖ ≤ ‖ℓ - ℓ'‖`. -/
theorem mul_norm_sub_le_norm_sub_of_coercive {W : Submodule 𝕜 V} {c : ℝ}
    (hc : ∀ w ∈ W, c * ‖w‖ ^ 2 ≤ re (a w w)) {u u' : V} {ℓ' : StrongDual 𝕜 V}
    (hu : ∀ v ∈ W, a u v = ℓ v) (hu' : ∀ v ∈ W, a u' v = ℓ' v) (h : u - u' ∈ W) :
    c * ‖u - u'‖ ≤ ‖ℓ - ℓ'‖ := by
  rcases (norm_nonneg (u - u')).eq_or_lt with h0 | hpos
  · rw [← h0, mul_zero]
    exact norm_nonneg _
  have h' : c * ‖u - u'‖ ^ 2 ≤ ‖ℓ - ℓ'‖ * ‖u - u'‖ := by
    calc c * ‖u - u'‖ ^ 2 ≤ re (a (u - u') (u - u')) := hc _ h
      _ = re ((ℓ - ℓ') (u - u')) := by rw [map_sub a, sub_apply, hu _ h, hu' _ h, sub_apply]
      _ ≤ ‖(ℓ - ℓ') (u - u')‖ := re_le_norm _
      _ ≤ ‖ℓ - ℓ'‖ * ‖u - u'‖ := le_opNorm _ _
  rw [sq, ← mul_assoc] at h'
  exact le_of_mul_le_mul_right h' hpos

end Seminormed

section Normed

variable {𝕜 V : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [NormedSpace 𝕜 V]
  {a : V →L⋆[𝕜] V →L[𝕜] 𝕜} {ℓ : StrongDual 𝕜 V}

/-- **Uniqueness of weak solutions.** If the energy of `a` dominates `c ‖w‖²` on `W` with
`0 < c`, two solutions of the weak equation on `W` that differ by an element of `W` agree. -/
theorem eq_of_forall_apply_eq_of_coercive {W : Submodule 𝕜 V} {c : ℝ} (hc0 : 0 < c)
    (hc : ∀ w ∈ W, c * ‖w‖ ^ 2 ≤ re (a w w)) {u u' : V} (hu : ∀ v ∈ W, a u v = ℓ v)
    (hu' : ∀ v ∈ W, a u' v = ℓ v) (h : u' - u ∈ W) : u' = u := by
  have h0 : re (a (u' - u) (u' - u)) = 0 := by
    rw [map_sub a u' u, sub_apply, hu' _ h, hu _ h, sub_self, map_zero]
  have := hc _ h
  rw [h0] at this
  exact sub_eq_zero.mp <| norm_eq_zero.mp <| pow_eq_zero_iff two_ne_zero |>.mp <|
    le_antisymm (nonpos_of_mul_nonpos_right this hc0) (sq_nonneg _)

variable [NormedSpace ℝ V] [IsScalarTower ℝ 𝕜 V] (ℓ) in
/-- **The first variation of a quadratic energy.** On the real restriction of scalars, the
quadratic energy of a Hermitian form has Fréchet derivative `v ↦ 2 re (a u v - ℓ v)` at `u`. -/
theorem hasFDerivAt_quadraticEnergy (ha : ∀ u v, a u v = star (a v u)) (u : V) :
    HasFDerivAt (a.quadraticEnergy ℓ) ((2 : ℝ) • reCLM.comp ((a u - ℓ).restrictScalars ℝ)) u := by
  refine (hasFDerivAt_iff_isLittleO_nhds_zero (𝕜 := ℝ)).mpr ?_
  have hrem : ∀ h : V, a.quadraticEnergy ℓ (u + h) - a.quadraticEnergy ℓ u -
      ((2 : ℝ) • reCLM.comp ((a u - ℓ).restrictScalars ℝ)) h = re (a h h) := fun h => by
    rw [quadraticEnergy_add ℓ ha]
    simp only [smul_apply, comp_apply, coe_restrictScalars', reCLM_apply, smul_eq_mul, sub_apply]
    ring
  simp_rw [hrem]
  refine (Asymptotics.IsBigO.of_bound ‖a‖ (Eventually.of_forall fun h => ?_)).trans_isLittleO
    (Asymptotics.isLittleO_norm_pow_id one_lt_two)
  rw [Real.norm_eq_abs, norm_pow, norm_norm, sq, ← mul_assoc]
  exact (abs_re_le_norm _).trans (le_opNorm₂ a h h)

end Normed

section Complete

variable {𝕜 V : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [CompleteSpace V]
  {a : V →L⋆[𝕜] V →L[𝕜] 𝕜}

open InnerProductSpace

/-- On a Hilbert space, the global minimizer of the quadratic energy of a nonnegative Hermitian
form with invertible Fréchet–Riesz operator is the Lax–Milgram solution `solutionOfFunctional`. -/
theorem isMinOn_quadraticEnergy_iff_eq_solutionOfFunctional (ha : ∀ u v, a u v = star (a v u))
    (hq : ∀ w, 0 ≤ re (a w w)) (hB : IsUnit (continuousLinearMapOfBilin a))
    (ℓ : StrongDual 𝕜 V) {u : V} :
    IsMinOn (a.quadraticEnergy ℓ) univ u ↔ u = solutionOfFunctional a hB ℓ := by
  rw [isMinOn_quadraticEnergy_iff ℓ ha hq]
  exact ⟨fun hu => eq_solutionOfFunctional a hB fun v => by rw [hu], fun hu => by
    rw [hu, apply_solutionOfFunctional]⟩

/-- For the forcing `v ↦ ⟪h, j v⟫`, the global minimizer of the quadratic energy of a nonnegative
Hermitian form is the `H`-forcing solution `formSolutionMap a hB j h`. -/
theorem isMinOn_quadraticEnergy_iff_eq_formSolutionMap (ha : ∀ u v, a u v = star (a v u))
    (hq : ∀ w, 0 ≤ re (a w w)) (hB : IsUnit (continuousLinearMapOfBilin a))
    {H : Type*} [SeminormedAddCommGroup H] [InnerProductSpace 𝕜 H] (j : V →L[𝕜] H) (h : H)
    {u : V} :
    IsMinOn (a.quadraticEnergy (toSesqForm j h)) univ u ↔ u = formSolutionMap a hB j h := by
  rw [formSolutionMap_apply]
  exact isMinOn_quadraticEnergy_iff_eq_solutionOfFunctional ha hq hB _

end Complete

end ContinuousLinearMap

namespace IsCoercive

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  {B : V →L[ℝ] V →L[ℝ] ℝ}

/-- Over `ℝ`, the global minimizer of the quadratic energy `B u u - 2 ℓ u` of a symmetric
coercive bilinear form is the Lax–Milgram solution `IsCoercive.solutionOfFunctional`. -/
theorem isMinOn_quadraticEnergy_iff_eq_solutionOfFunctional (hB : IsCoercive B)
    (hsymm : ∀ u v, B u v = B v u) (ℓ : StrongDual ℝ V) {u : V} :
    IsMinOn (B.quadraticEnergy ℓ) univ u ↔ u = hB.solutionOfFunctional ℓ := by
  rw [hB.solutionOfFunctional_eq]
  exact ContinuousLinearMap.isMinOn_quadraticEnergy_iff_eq_solutionOfFunctional
    (fun u v => by rw [hsymm, star_trivial])
    (fun w => by rw [re_to_real]; exact hB.apply_self_nonneg w) _ ℓ

end IsCoercive
