/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.QuadraticDiscriminant
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import TauCeti.Analysis.InnerProductSpace.LaxMilgram
public import TauCeti.Analysis.LocallyConvex.WeakSpace.Basic
public import TauCeti.Analysis.RCLike.SesquilinearForm
public import TauCeti.Analysis.Variational.DirectMethod
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import TauCeti.Algebra.Group.Subgroup.Pointwise
import TauCeti.Algebra.Group.Subsemigroup.Pointwise
import TauCeti.Topology.MetricSpace.Pseudo.Lemmas

/-!
# Quadratic energies, weak Euler--Lagrange equations, and coercive minimization

Let `a : V →L⋆[𝕜] V →L[𝕜] 𝕜` be a bounded sesquilinear form on a seminormed space `V` over
`𝕜 = ℝ` or `ℂ` (`[RCLike 𝕜]`), conjugate linear in its first argument, and let
`ℓ : StrongDual 𝕜 V` be a forcing functional. The **quadratic energy**

`E(u) = re (a u u) - 2 re (ℓ u)`

(`ContinuousLinearMap.quadraticEnergy`) is a real-valued functional whose minimizers solve the weak
equation `a u v = ℓ v` when `a` is Hermitian (and conversely when `re (a w w) ≥ 0`). This file
develops the algebraic, differential, variational, and direct-method properties of
`a.quadraticEnergy ℓ`:

* **Expansions, affine datum shift, and smoothness.** For a Hermitian form, expanding `E(u + h)`
  separates the linear variation `2 re (a u h - ℓ h)` from the quadratic remainder `re (a h h)`
  (`ContinuousLinearMap.quadraticEnergy_add`), along scalar and real lines
  (`ContinuousLinearMap.quadraticEnergy_add_smul_norm_sq`,
  `ContinuousLinearMap.quadraticEnergy_add_smul`,
  `ContinuousLinearMap.quadraticEnergy_add_real_smul`), and under translation by a datum `g`, which
  shifts the forcing from `ℓ` to `ℓ - a g`
  (`ContinuousLinearMap.quadraticEnergy_add_eq_add_quadraticEnergy_sub`). On a normed space over `𝕜`
  with its compatible real scalar action, `a.quadraticEnergy ℓ` is `C^n` over `ℝ` for every `n`,
  with strict Fréchet derivative `v ↦ 2 re (a u v - ℓ v)` when `a` is Hermitian
  (`ContinuousLinearMap.hasStrictFDerivAt_quadraticEnergy`,
  `ContinuousLinearMap.hasFDerivAt_quadraticEnergy`).
* **Convexity and weak lower semicontinuity.** Even without symmetry of `a`, the Jensen deficit of
  `E` along `t₁ • u + t₂ • v` (`t₁ + t₂ = 1`) is `t₁ t₂ re (a (u - v) (u - v))`
  (`ContinuousLinearMap.quadraticEnergy_combo_add_mul_sub`), so `E` is convex and relatively weakly
  lower semicontinuous on any convex set `C` on whose differences `re (a w w) ≥ 0`
  (`ContinuousLinearMap.lowerSemicontinuousOn_quadraticEnergy_comp_toWeakSpace_symm`).
* **Variational inequalities, weak Euler--Lagrange equations, and exact energy gap.** For Hermitian
  `a`, local minimizers on convex sets satisfy the variational inequality
  `re (ℓ (v - u)) ≤ re (a u (v - u))`
  (`ContinuousLinearMap.le_re_apply_sub_of_isLocalMinOn_quadraticEnergy_convex`), and local or
  global minimizers on affine cosets `g +ᵥ W` or `u + W` solve the full `𝕜`-valued weak equation
  `a u v = ℓ v` on `W` (`ContinuousLinearMap.apply_eq_of_forall_le_quadraticEnergy_add`,
  `ContinuousLinearMap.apply_eq_of_isLocalMinOn_quadraticEnergy_vadd`) via the `I`-test. Conversely,
  at a weak solution `E(u + h) = E(u) + re (a h h)`
  (`ContinuousLinearMap.quadraticEnergy_add_of_forall_apply_eq`), making minimality and the weak
  equation equivalent when `re (a w w) ≥ 0` on `W`
  (`ContinuousLinearMap.forall_le_quadraticEnergy_add_iff`,
  `ContinuousLinearMap.isMinOn_quadraticEnergy_vadd_iff`,
  `ContinuousLinearMap.isMinOn_quadraticEnergy_iff`).
* **Coercive stability and direct-method existence.** Coercive forms yield quadratic energy-gap
  bounds, norm convergence of near-minimizers, bounded sublevels
  (`ContinuousLinearMap.hasBoundedSublevelsOn_quadraticEnergy_of_sub_coercive`), forcing stability
  (`ContinuousLinearMap.mul_norm_sub_le_norm_comp_subtypeL_of_coercive`,
  `ContinuousLinearMap.mul_norm_sub_le_norm_sub_of_coercive`), uniqueness, and—on reflexive normed
  spaces—direct-method existence and uniqueness of constrained minimizers and weak solutions
  (`ContinuousLinearMap.existsUnique_isMinOn_quadraticEnergy_of_isClosed_convex`,
  `ContinuousLinearMap.existsUnique_vadd_forall_apply_eq_of_isClosed_of_coercive`).
* **Dirichlet's principle with a lifting.** For a symmetric real form `B` on `H`, nonnegative on the
  image of `S : V →L[ℝ] H`, `w₀` minimizes `B(g + S w, g + S w) / 2 - ℓ w` exactly when
  `B(g + S w₀, S v) = ℓ v` for every `v` (`ContinuousLinearMap.isMinOn_iff_forall_apply_eq`).
* **Hilbert-space Lax--Milgram identifications.** On a Hilbert space, global minimizers coincide
  with `InnerProductSpace.solutionOfFunctional`, `InnerProductSpace.formSolutionMap`, and over `ℝ`
  with `IsCoercive.solutionOfFunctional`, `IsCoercive.continuousLinearEquivOfBilin.symm`, and
  `IsCoercive.solutionOfInner` (and with `IsCoercive.formSolutionMap` in
  `TauCeti.Analysis.InnerProductSpace.Variational.Spectrum`).

## References

* J. K. Hunter, *Notes on Partial Differential Equations*, Chapter 4: Definition 4.3,
  Proposition 4.5, Corollary 4.6, and Theorem 4.20.
* L. C. Evans, *Partial Differential Equations*, 2nd ed., §2.2.5, Theorem 17 (Dirichlet's
  principle).
-/

public section

noncomputable section

open RCLike Filter Topology Set Bornology NormedSpace
open scoped Pointwise InnerProductSpace

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

/-- With zero forcing, `a.quadraticEnergy 0` is the pure quadratic form `u ↦ re (a u u)`. -/
@[simp]
theorem quadraticEnergy_zero (u : V) : a.quadraticEnergy 0 u = re (a u u) := by
  simp [quadraticEnergy_apply]

/-- With zero form, `(0 : V →L⋆[𝕜] V →L[𝕜] 𝕜).quadraticEnergy ℓ u` is `-2 * re (ℓ u)`. -/
@[simp]
theorem zero_quadraticEnergy (u : V) :
    (0 : V →L⋆[𝕜] V →L[𝕜] 𝕜).quadraticEnergy ℓ u = -2 * re (ℓ u) := by
  simp [quadraticEnergy_apply]

/-- Negating both the forcing and the vector leaves `a.quadraticEnergy` unchanged. -/
@[simp]
theorem quadraticEnergy_neg_apply_neg (u : V) :
    a.quadraticEnergy (-ℓ) (-u) = a.quadraticEnergy ℓ u := by
  simp [quadraticEnergy_apply]

/-- Evaluating `a.quadraticEnergy ℓ` at `-u` flips the sign of the forcing. -/
theorem quadraticEnergy_neg_apply (u : V) :
    a.quadraticEnergy ℓ (-u) = a.quadraticEnergy (-ℓ) u := by
  simp [quadraticEnergy_apply]

/-- Negating both the form `a` and the forcing `ℓ` negates `quadraticEnergy`. -/
@[simp]
theorem neg_quadraticEnergy_neg (u : V) :
    (-a).quadraticEnergy (-ℓ) u = -a.quadraticEnergy ℓ u := by
  simp only [quadraticEnergy_apply, neg_apply, map_neg]
  ring

/-- Scaling both the form `a` and the forcing `ℓ` by `r : ℝ` scales `quadraticEnergy` by `r`. -/
@[simp]
theorem smul_quadraticEnergy_smul (r : ℝ) (u : V) :
    (r • a).quadraticEnergy (r • ℓ) u = r * a.quadraticEnergy ℓ u := by
  simp only [quadraticEnergy_apply, smul_apply, Algebra.smul_def,
    algebraMap_eq_ofReal, re_ofReal_mul]
  ring

/-- Pullback of `quadraticEnergy` along a continuous `𝕜`-linear map `L : W →L[𝕜] V`. -/
@[simp]
theorem bilinearComp_quadraticEnergy_comp {W : Type*} [SeminormedAddCommGroup W] [NormedSpace 𝕜 W]
    (L : W →L[𝕜] V) (w : W) :
    (a.bilinearComp L L).quadraticEnergy (ℓ.comp L) w = a.quadraticEnergy ℓ (L w) := by
  simp [quadraticEnergy_apply]

/-- Viewing `V` over `ℝ`, the real quadratic energy of `a.reBilin` and `re ∘ ℓ` coincides with
`a.quadraticEnergy ℓ`. -/
@[simp]
theorem reBilin_quadraticEnergy [NormedSpace ℝ V] [IsScalarTower ℝ 𝕜 V] (u : V) :
    a.reBilin.quadraticEnergy (reCLM.comp (ℓ.restrictScalars ℝ)) u = a.quadraticEnergy ℓ u := by
  rw [quadraticEnergy_apply, ContinuousLinearMap.quadraticEnergy_apply, reBilin_apply_apply]
  simp

/-- Increment of `a.quadraticEnergy ℓ` from `u` to `u + v` without assuming symmetry of `a`. -/
theorem quadraticEnergy_add_sub (u v : V) :
    a.quadraticEnergy ℓ (u + v) - a.quadraticEnergy ℓ u =
      re (a u v) + re (a v u) - 2 * re (ℓ v) + re (a v v) := by
  simp only [quadraticEnergy_apply, map_add, add_apply]
  ring

/-- `a.quadraticEnergy ℓ` is norm-continuous for every continuous sesquilinear form `a` and
continuous linear functional `ℓ`. -/
@[fun_prop]
theorem continuous_quadraticEnergy : Continuous (a.quadraticEnergy ℓ) :=
  a.continuous_re_apply_self.sub (continuous_const.mul (reCLM.continuous.comp ℓ.continuous))

variable {a ℓ} in
/-- `quadraticEnergy` is additive jointly in the form `a` and the forcing `ℓ`. -/
theorem add_quadraticEnergy_add (a₁ a₂ : V →L⋆[𝕜] V →L[𝕜] 𝕜) (ℓ₁ ℓ₂ : StrongDual 𝕜 V) (u : V) :
    (a₁ + a₂).quadraticEnergy (ℓ₁ + ℓ₂) u =
      a₁.quadraticEnergy ℓ₁ u + a₂.quadraticEnergy ℓ₂ u := by
  simp only [quadraticEnergy_apply, add_apply, map_add]
  ring

variable {a ℓ} in
/-- `quadraticEnergy` preserves subtraction jointly in the form `a` and the forcing `ℓ`. -/
theorem sub_quadraticEnergy_sub (a₁ a₂ : V →L⋆[𝕜] V →L[𝕜] 𝕜) (ℓ₁ ℓ₂ : StrongDual 𝕜 V) (u : V) :
    (a₁ - a₂).quadraticEnergy (ℓ₁ - ℓ₂) u =
      a₁.quadraticEnergy ℓ₁ u - a₂.quadraticEnergy ℓ₂ u := by
  simp only [quadraticEnergy_apply, sub_apply, map_sub]
  ring

/-- Over `ℝ`, `B.quadraticEnergy ℓ u` is `B u u - 2 * ℓ u`. -/
theorem quadraticEnergy_real_apply {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    (B : E →L[ℝ] E →L[ℝ] ℝ) (ℓ : StrongDual ℝ E) (u : E) :
    B.quadraticEnergy ℓ u = B u u - 2 * ℓ u := by
  simp [quadraticEnergy_apply]

variable {a}

/-- **The exact expansion of a quadratic energy.** -/
theorem quadraticEnergy_add (ha : ∀ u v, a u v = star (a v u)) (u h : V) :
    a.quadraticEnergy ℓ (u + h) =
      a.quadraticEnergy ℓ u + 2 * re (a u h - ℓ h) + re (a h h) := by
  have hre : re (a h u) = re (a u h) := by rw [ha h u, star_def, conj_re]
  simp only [quadraticEnergy_apply, map_add, add_apply, map_sub]
  linarith

/-- **Affine datum shift** for a Hermitian quadratic energy: translating the argument by `g` shifts
the forcing functional from `ℓ` to `ℓ - a g` up to the additive constant `E(g)`. This reduces
minimization on an inhomogeneous coset `g +ᵥ W` to minimization on the subspace `W`. -/
theorem quadraticEnergy_add_eq_add_quadraticEnergy_sub (ha : ∀ u v, a u v = star (a v u))
    (g w : V) :
    a.quadraticEnergy ℓ (g + w) = a.quadraticEnergy ℓ g + a.quadraticEnergy (ℓ - a g) w := by
  rw [quadraticEnergy_add ℓ ha g w]
  simp only [quadraticEnergy_apply, sub_apply, map_sub]
  ring

/-- **Scalar-line expansion** of a quadratic energy for a Hermitian form `a` and `c : 𝕜`. -/
theorem quadraticEnergy_add_smul_norm_sq (ha : ∀ u v, a u v = star (a v u)) (u v : V) (c : 𝕜) :
    a.quadraticEnergy ℓ (u + c • v) =
      a.quadraticEnergy ℓ u + 2 * re (c * (a u v - ℓ v)) + ‖c‖ ^ 2 * re (a v v) := by
  rw [quadraticEnergy_add ℓ ha u (c • v), map_smul, map_smul, smul_eq_mul, smul_eq_mul, ← mul_sub]
  congr 1
  exact a.toLinearMap₁₂.re_apply_smul_self c v

/-- **The expansion of a quadratic energy along a real line.** -/
theorem quadraticEnergy_add_smul (ha : ∀ u v, a u v = star (a v u)) (u v : V) (t : ℝ) :
    a.quadraticEnergy ℓ (u + (t : 𝕜) • v) =
      a.quadraticEnergy ℓ u + 2 * t * re (a u v - ℓ v) + t ^ 2 * re (a v v) := by
  rw [quadraticEnergy_add_smul_norm_sq ℓ ha u v (t : 𝕜), re_ofReal_mul, norm_ofReal, sq_abs]
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
    Tendsto x l (𝓝 u) :=
  TauCeti.tendsto_of_dist_pow_le_of_tendsto_zero (n := 2)
    (g := fun i => (a.quadraticEnergy ℓ (x i) - a.quadraticEnergy ℓ u) / c)
    (Eventually.of_forall fun i => by
      rw [dist_eq_norm, le_div_iff₀ hc0, mul_comm]
      exact mul_norm_sub_sq_le_quadraticEnergy_sub ℓ ha hc hu (hx i))
    (by simpa only [sub_self, zero_div] using (hE.sub_const (a.quadraticEnergy ℓ u)).div_const c)

/-- **Lipschitz dependence of constrained weak solutions on the restricted forcing.** If the real
quadratic part of `a` dominates `c * ‖w‖ ^ 2` on a submodule `W`, then solutions of `a u v = ℓ v`
and `a u' v = ℓ' v` on `W` that differ by an element of `W` satisfy
`c * ‖u - u'‖ ≤ ‖(ℓ - ℓ').comp W.subtypeL‖`. No symmetry of `a` or positivity of `c` is
required. -/
theorem mul_norm_sub_le_norm_comp_subtypeL_of_coercive {W : Submodule 𝕜 V} {c : ℝ}
    (hc : ∀ w ∈ W, c * ‖w‖ ^ 2 ≤ re (a w w)) {u u' : V} {ℓ' : StrongDual 𝕜 V}
    (hu : ∀ v ∈ W, a u v = ℓ v) (hu' : ∀ v ∈ W, a u' v = ℓ' v) (h : u - u' ∈ W) :
    c * ‖u - u'‖ ≤ ‖(ℓ - ℓ').comp W.subtypeL‖ := by
  rcases (norm_nonneg (u - u')).eq_or_lt with h0 | hpos
  · rw [← h0, mul_zero]
    exact norm_nonneg _
  · have hpair : a (u - u') (u - u') = ((ℓ - ℓ').comp W.subtypeL) ⟨u - u', h⟩ := by
      rw [a.map_sub, sub_apply, hu (u - u') h, hu' (u - u') h]
      simp
    have hle : c * ‖u - u'‖ ^ 2 ≤ ‖(ℓ - ℓ').comp W.subtypeL‖ * ‖u - u'‖ := by
      calc c * ‖u - u'‖ ^ 2 ≤ re (a (u - u') (u - u')) := hc (u - u') h
        _ ≤ ‖a (u - u') (u - u')‖ := re_le_norm _
        _ = ‖((ℓ - ℓ').comp W.subtypeL) ⟨u - u', h⟩‖ := by rw [hpair]
        _ ≤ ‖(ℓ - ℓ').comp W.subtypeL‖ * ‖(⟨u - u', h⟩ : W)‖ :=
            le_opNorm ((ℓ - ℓ').comp W.subtypeL) ⟨u - u', h⟩
        _ = ‖(ℓ - ℓ').comp W.subtypeL‖ * ‖u - u'‖ := by simp
    rw [sq, ← mul_assoc] at hle
    exact le_of_mul_le_mul_right hle hpos

/-- **Lipschitz dependence on the forcing.** If the energy of `a` dominates `c ‖w‖²` on `W`, then
solutions of the weak equations `a u v = ℓ v` and `a u' v = ℓ' v` on `W` that differ by an element
of `W` satisfy `c ‖u - u'‖ ≤ ‖ℓ - ℓ'‖`. -/
theorem mul_norm_sub_le_norm_sub_of_coercive {W : Submodule 𝕜 V} {c : ℝ}
    (hc : ∀ w ∈ W, c * ‖w‖ ^ 2 ≤ re (a w w)) {u u' : V} {ℓ' : StrongDual 𝕜 V}
    (hu : ∀ v ∈ W, a u v = ℓ v) (hu' : ∀ v ∈ W, a u' v = ℓ' v) (h : u - u' ∈ W) :
    c * ‖u - u'‖ ≤ ‖ℓ - ℓ'‖ := by
  refine (a.mul_norm_sub_le_norm_comp_subtypeL_of_coercive ℓ hc hu hu' h).trans ?_
  refine opNorm_le_bound _ (norm_nonneg (ℓ - ℓ')) fun w => ?_
  simpa only [comp_apply, Submodule.coe_subtypeL, Submodule.subtype_apply,
    ← Submodule.norm_coe] using le_opNorm (ℓ - ℓ') (w : V)

section RealScalar

variable [Module ℝ V] [IsScalarTower ℝ 𝕜 V]

/-- **Real-line expansion** of `a.quadraticEnergy ℓ` under a compatible `Module ℝ V` action. -/
theorem quadraticEnergy_add_real_smul (ha : ∀ u v, a u v = star (a v u)) (u v : V) (t : ℝ) :
    a.quadraticEnergy ℓ (u + t • v) =
      a.quadraticEnergy ℓ u + 2 * t * re (a u v - ℓ v) + t ^ 2 * re (a v v) := by
  rw [← algebraMap_smul 𝕜 t v, algebraMap_eq_ofReal]
  exact quadraticEnergy_add_smul ℓ ha u v t

/-- Along a two-point affine combination `t₁ • u + t₂ • v` with `t₁ + t₂ = 1`, the Jensen deficit of
`a.quadraticEnergy ℓ` equals `t₁ * t₂ * re (a (u - v) (u - v))`, independent of `ℓ` and without
assuming symmetry of `a`. -/
theorem quadraticEnergy_combo_add_mul_sub (a : V →L⋆[𝕜] V →L[𝕜] 𝕜) (ℓ : StrongDual 𝕜 V)
    {t₁ t₂ : ℝ} (ht : t₁ + t₂ = 1) (u v : V) :
    a.quadraticEnergy ℓ (t₁ • u + t₂ • v) +
        t₁ * t₂ * re (a (u - v) (u - v)) =
      t₁ * a.quadraticEnergy ℓ u + t₂ * a.quadraticEnergy ℓ v := by
  have hq := a.toLinearMap₁₂.re_apply_combo_self_add_mul_sub ht u v
  simp only [toLinearMap₁₂_apply_apply_apply] at hq
  have hℓ : re (ℓ (t₁ • u + t₂ • v)) = t₁ * re (ℓ u) + t₂ * re (ℓ v) := by
    rw [map_add, ← algebraMap_smul 𝕜 t₁ u, ← algebraMap_smul 𝕜 t₂ v, map_smul, map_smul,
      algebraMap_eq_ofReal]
    simp
  simp only [quadraticEnergy_apply, hℓ]
  linarith

/-- One-dimensional derivative of `s ↦ a.quadraticEnergy ℓ (u + s • v)` at `t : ℝ` for a Hermitian
form `a`. -/
theorem hasDerivAt_quadraticEnergy_add_smul (ha : ∀ u v, a u v = star (a v u)) (u v : V) (t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ a.quadraticEnergy ℓ (u + s • v))
      (2 * re (a u v - ℓ v) + 2 * t * re (a v v)) t := by
  have hpoly : (fun s : ℝ ↦ a.quadraticEnergy ℓ (u + s • v)) =
      fun s : ℝ ↦ a.quadraticEnergy ℓ u +
        2 * re (a u v - ℓ v) * s + re (a v v) * s ^ 2 := by
    ext s
    rw [quadraticEnergy_add_real_smul ℓ ha u v s]
    ring
  rw [hpoly]
  have hd := ((hasDerivAt_const t (a.quadraticEnergy ℓ u)).add
    ((hasDerivAt_id' t).const_mul (2 * re (a u v - ℓ v)))).add
    ((hasDerivAt_pow 2 t).const_mul (re (a v v)))
  exact (by ring : 0 + 2 * re (a u v - ℓ v) * 1 +
    re (a v v) * ((2 : ℕ) * t ^ (2 - 1)) =
    2 * re (a u v - ℓ v) + 2 * t * re (a v v)) ▸ hd

/-- If `a` is nonnegative on differences of points of a convex set `C`, then `a.quadraticEnergy ℓ`
is convex on `C`. No symmetry of `a` is required. -/
theorem convexOn_quadraticEnergy_of_sub_nonneg {C : Set V} (hC : Convex ℝ C)
    (hpos : ∀ u ∈ C, ∀ v ∈ C, 0 ≤ re (a (u - v) (u - v))) (ℓ : StrongDual 𝕜 V) :
    ConvexOn ℝ C (a.quadraticEnergy ℓ) := by
  refine ⟨hC, fun u hu v hv t₁ t₂ ht₁ ht₂ ht ↦ ?_⟩
  simp only [smul_eq_mul]
  have hdiff : 0 ≤ t₁ * t₂ * re (a (u - v) (u - v)) :=
    mul_nonneg (mul_nonneg ht₁ ht₂) (hpos u hu v hv)
  linarith [a.quadraticEnergy_combo_add_mul_sub ℓ ht u v]

/-- If `∀ u, 0 ≤ re (a u u)`, then `a.quadraticEnergy ℓ` is convex on `V`. No symmetry of `a` is
required. -/
theorem convexOn_quadraticEnergy (hpos : ∀ u, 0 ≤ re (a u u)) (ℓ : StrongDual 𝕜 V) :
    ConvexOn ℝ univ (a.quadraticEnergy ℓ) :=
  a.convexOn_quadraticEnergy_of_sub_nonneg convex_univ (fun u _ v _ ↦ hpos (u - v)) ℓ

/-- If `a` is nonnegative on differences of points in a convex set `C`, then `a.quadraticEnergy ℓ`
is lower semicontinuous on `toWeakSpace 𝕜 V '' C` in the `𝕜`-weak topology; neither symmetry of `a`,
nonnegativity outside `C`, nor closedness of `C` is required. -/
theorem lowerSemicontinuousOn_quadraticEnergy_comp_toWeakSpace_symm {C : Set V} (hC : Convex ℝ C)
    (hpos : ∀ u ∈ C, ∀ v ∈ C, 0 ≤ re (a (u - v) (u - v))) (ℓ : StrongDual 𝕜 V) :
    LowerSemicontinuousOn
      (fun u : WeakSpace 𝕜 V ↦ a.quadraticEnergy ℓ ((toWeakSpace 𝕜 V).symm u))
      (toWeakSpace 𝕜 V '' C) := by
  have : LocallyConvexSpace ℝ V := NormedSpace.toLocallyConvexSpace' 𝕜
  exact (a.convexOn_quadraticEnergy_of_sub_nonneg hC hpos ℓ).quasiconvexOn
    |>.lowerSemicontinuousOn_comp_toWeakSpace_symm
      (a.continuous_quadraticEnergy ℓ).continuousOn.lowerSemicontinuousOn

end RealScalar

/-- For a continuous sesquilinear form `a` with nonnegative real diagonal, `a.quadraticEnergy ℓ` is
lower semicontinuous with respect to `WeakSpace 𝕜 V`. No symmetry of `a` is required. -/
theorem lowerSemicontinuous_quadraticEnergy_comp_toWeakSpace_symm
    (hpos : ∀ u, 0 ≤ re (a u u)) (ℓ : StrongDual 𝕜 V) :
    LowerSemicontinuous
      (fun u : WeakSpace 𝕜 V ↦ a.quadraticEnergy ℓ ((toWeakSpace 𝕜 V).symm u)) := by
  let : NormedSpace ℝ V := NormedSpace.restrictScalars ℝ 𝕜 V
  have : IsScalarTower ℝ 𝕜 V := IsScalarTower.restrictScalars ℝ 𝕜 V
  exact (a.convexOn_quadraticEnergy hpos ℓ).quasiconvexOn.lowerSemicontinuous_comp_toWeakSpace_symm
    (a.continuous_quadraticEnergy ℓ).lowerSemicontinuous

end Seminormed

/-! ### First variation on rays, convex sets, and affine cosets `g +ᵥ W` -/

section FirstVariation

variable {𝕜 V : Type*} [RCLike 𝕜] [SeminormedAddCommGroup V] [NormedSpace 𝕜 V]
  {a : V →L⋆[𝕜] V →L[𝕜] 𝕜} {ℓ : StrongDual 𝕜 V}

/-- **One-sided ray variation.** For a Hermitian form `a`, if `u` is a local minimizer of
`a.quadraticEnergy ℓ` on `S` and `u + (t : 𝕜) • w ∈ S` for all sufficiently small `t > 0`, then
`re (ℓ w) ≤ re (a u w)`. -/
theorem le_re_apply_of_isLocalMinOn_quadraticEnergy_ray
    (ha : ∀ x y, a x y = star (a y x)) {S : Set V} {u w : V}
    (hmin : IsLocalMinOn (a.quadraticEnergy ℓ) S u)
    (hray : ∀ᶠ t : ℝ in 𝓝[>] 0, u + (t : 𝕜) • w ∈ S) :
    re (ℓ w) ≤ re (a u w) := by
  have hcont : Continuous (fun t : ℝ ↦ u + (t : 𝕜) • w) :=
    continuous_const.add ((continuous_ofReal.comp continuous_id).smul continuous_const)
  have htend : Tendsto (fun t : ℝ ↦ u + (t : 𝕜) • w) (𝓝[>] 0) (𝓝[S] u) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, hray⟩
    simpa only [ofReal_zero, zero_smul, add_zero] using
      (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
  have hle : ∀ᶠ t : ℝ in 𝓝[>] 0, -(t / 2 * re (a w w)) ≤ re (a u w - ℓ w) := by
    filter_upwards [htend.eventually hmin, self_mem_nhdsWithin] with t ht htpos
    have hexp := a.quadraticEnergy_add_smul ℓ ha u w t
    have hmul : 0 ≤ 2 * t * (re (a u w - ℓ w) + t / 2 * re (a w w)) := by linarith
    have hpos2 : (0 : ℝ) < 2 * t := mul_pos zero_lt_two htpos
    linarith [nonneg_of_mul_nonneg_right hmul hpos2]
  have hlim : Tendsto (fun t : ℝ ↦ -(t / 2 * re (a w w))) (𝓝[>] 0) (𝓝 0) := by
    have hc : Continuous (fun t : ℝ ↦ -(t / 2 * re (a w w))) := by fun_prop
    simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  have h0 : 0 ≤ re (a u w - ℓ w) := le_of_tendsto hlim hle
  rwa [map_sub, sub_nonneg] at h0

/-- **Two-sided line variation.** For a Hermitian form `a`, if `u` is a local minimizer of
`a.quadraticEnergy ℓ` on `S` and `u + (t : 𝕜) • w ∈ S` for all `t : ℝ` near `0`, then
`re (a u w) = re (ℓ w)`. -/
theorem re_apply_eq_re_of_isLocalMinOn_quadraticEnergy_line
    (ha : ∀ x y, a x y = star (a y x)) {S : Set V} {u w : V}
    (hmin : IsLocalMinOn (a.quadraticEnergy ℓ) S u)
    (hline : ∀ᶠ t : ℝ in 𝓝 0, u + (t : 𝕜) • w ∈ S) :
    re (a u w) = re (ℓ w) := by
  have h₁ := a.le_re_apply_of_isLocalMinOn_quadraticEnergy_ray ha hmin (nhdsWithin_le_nhds hline)
  have hneg : ∀ᶠ t : ℝ in 𝓝[>] 0, u + (t : 𝕜) • (-w) ∈ S := by
    have hnt : Tendsto (fun t : ℝ ↦ -t) (𝓝[>] 0) (𝓝 0) := by
      simpa only [neg_zero] using (continuous_neg.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
    filter_upwards [hnt.eventually hline] with t ht
    have ht' : u + ((-t : ℝ) : 𝕜) • w ∈ S := ht
    simpa only [ofReal_neg, neg_smul, smul_neg] using ht'
  have h₂ := a.le_re_apply_of_isLocalMinOn_quadraticEnergy_ray ha hmin hneg
  simp only [map_neg] at h₂
  linarith

/-- **Variational inequality on a convex constraint** for a Hermitian form `a`: if `u ∈ C` is a
local minimizer of `a.quadraticEnergy ℓ` on a convex set `C`, then
`re (ℓ (v - u)) ≤ re (a u (v - u))` for every `v ∈ C`. -/
theorem le_re_apply_sub_of_isLocalMinOn_quadraticEnergy_convex [Module ℝ V] [IsScalarTower ℝ 𝕜 V]
    (ha : ∀ x y, a x y = star (a y x)) {C : Set V} (hC : Convex ℝ C) {u : V} (hu : u ∈ C)
    (hmin : IsLocalMinOn (a.quadraticEnergy ℓ) C u) {v : V} (hv : v ∈ C) :
    re (ℓ (v - u)) ≤ re (a u (v - u)) := by
  refine a.le_re_apply_of_isLocalMinOn_quadraticEnergy_ray ha hmin ?_
  filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with t ht
  rw [← algebraMap_eq_ofReal, algebraMap_smul]
  exact hC.add_smul_sub_mem hu hv (Ioo_subset_Icc_self ht)

/-- **Two-sided real-part variation** along a real affine subspace for a Hermitian form `a`: at a
local minimizer `u ∈ g +ᵥ W` of `a.quadraticEnergy ℓ` on `g +ᵥ W` (`W : Submodule ℝ V`),
`re (a u w) = re (ℓ w)` for all `w ∈ W`. -/
theorem re_apply_eq_re_of_isLocalMinOn_quadraticEnergy_vadd_real
    [Module ℝ V] [IsScalarTower ℝ 𝕜 V] (ha : ∀ x y, a x y = star (a y x))
    {W : Submodule ℝ V} {g u : V} (hu : u ∈ g +ᵥ (W : Set V))
    (hmin : IsLocalMinOn (a.quadraticEnergy ℓ) (g +ᵥ (W : Set V)) u) {w : V} (hw : w ∈ W) :
    re (a u w) = re (ℓ w) := by
  refine a.re_apply_eq_re_of_isLocalMinOn_quadraticEnergy_line ha hmin
    (Eventually.of_forall fun t ↦ ?_)
  rw [← algebraMap_eq_ofReal, algebraMap_smul]
  exact TauCeti.add_mem_vadd_set hu (W.smul_mem t hw)

/-- **Weak Euler--Lagrange equation** on an affine coset `g +ᵥ W` for a Hermitian form `a`: if
`u ∈ g +ᵥ W` is a local minimizer of `a.quadraticEnergy ℓ` on `g +ᵥ W` (`W : Submodule 𝕜 V`), then
`a u w = ℓ w` for every `w ∈ W` (Hunter, Definition 4.3 and Proposition 4.5). -/
theorem apply_eq_of_isLocalMinOn_quadraticEnergy_vadd
    (ha : ∀ x y, a x y = star (a y x)) {W : Submodule 𝕜 V} {g u : V}
    (hu : u ∈ g +ᵥ (W : Set V))
    (hmin : IsLocalMinOn (a.quadraticEnergy ℓ) (g +ᵥ (W : Set V)) u) {w : V} (hw : w ∈ W) :
    a u w = ℓ w := by
  let : NormedSpace ℝ V := NormedSpace.restrictScalars ℝ 𝕜 V
  have : IsScalarTower ℝ 𝕜 V := IsScalarTower.restrictScalars ℝ 𝕜 V
  exact apply_eq_of_re_eq_of_re_I_smul_eq
    (a.re_apply_eq_re_of_isLocalMinOn_quadraticEnergy_vadd_real (W := W.restrictScalars ℝ) ha hu
      hmin hw)
    (a.re_apply_eq_re_of_isLocalMinOn_quadraticEnergy_vadd_real (W := W.restrictScalars ℝ) ha hu
      hmin (W.smul_mem I hw))

/-- **Unconstrained weak Euler--Lagrange equation** at a local minimizer of `a.quadraticEnergy ℓ`
for a Hermitian form `a`: `a u v = ℓ v` for every `v : V` (without requiring `re (a w w) ≥ 0`). -/
theorem apply_eq_of_isLocalMin_quadraticEnergy
    (ha : ∀ x y, a x y = star (a y x)) {u : V}
    (hmin : IsLocalMin (a.quadraticEnergy ℓ) u) (v : V) :
    a u v = ℓ v := by
  have hvadd : (0 : V) +ᵥ ((⊤ : Submodule 𝕜 V) : Set V) = univ := by
    ext x
    simp
  refine a.apply_eq_of_isLocalMinOn_quadraticEnergy_vadd (W := ⊤) (g := 0) ha (by simp) ?_ trivial
  rw [hvadd]
  exact hmin.isLocalMinOn univ

/-- At a vector `u` satisfying `a u u = ℓ u` (in particular, a homogeneous weak solution on `W`
with `u ∈ W`), the energy value is `E(u) = -re (a u u)`. -/
theorem quadraticEnergy_eq_neg_re_of_apply_self_eq {u : V} (h : a u u = ℓ u) :
    a.quadraticEnergy ℓ u = -re (a u u) := by
  rw [quadraticEnergy_apply, ← h]
  ring

/-- **Equivalence of the variational inequality and minimality** on a convex set `C` when `a` is
Hermitian and nonnegative on differences of points in `C`. -/
theorem isMinOn_quadraticEnergy_iff_of_convex [Module ℝ V] [IsScalarTower ℝ 𝕜 V]
    (ha : ∀ x y, a x y = star (a y x)) {C : Set V} (hC : Convex ℝ C)
    (hpos : ∀ x ∈ C, ∀ y ∈ C, 0 ≤ re (a (y - x) (y - x))) {u : V} (hu : u ∈ C) :
    IsMinOn (a.quadraticEnergy ℓ) C u ↔
      ∀ v ∈ C, re (ℓ (v - u)) ≤ re (a u (v - u)) := by
  refine ⟨fun hmin v hv ↦ a.le_re_apply_sub_of_isLocalMinOn_quadraticEnergy_convex ha hC hu
    hmin.isLocalMinOn hv, fun hvi ↦ isMinOn_iff.mpr fun v hv ↦ ?_⟩
  have hexp := a.quadraticEnergy_add ℓ ha u (v - u)
  rw [add_sub_cancel, map_sub] at hexp
  linarith [hvi v hv, hpos u hu v hv]

/-- **Equivalence of the weak Euler--Lagrange equation and minimality** on an affine coset
`g +ᵥ W` for a Hermitian form `a` when `re (a w w) ≥ 0` for all `w ∈ W` (Hunter, Corollary 4.6). -/
theorem isMinOn_quadraticEnergy_vadd_iff
    (ha : ∀ x y, a x y = star (a y x)) {W : Submodule 𝕜 V}
    (hpos : ∀ w ∈ W, 0 ≤ re (a w w)) {g u : V} (hu : u ∈ g +ᵥ (W : Set V)) :
    IsMinOn (a.quadraticEnergy ℓ) (g +ᵥ (W : Set V)) u ↔ ∀ w ∈ W, a u w = ℓ w := by
  refine ⟨fun hmin w hw ↦ a.apply_eq_of_isLocalMinOn_quadraticEnergy_vadd ha hu
    hmin.isLocalMinOn hw, fun hsol ↦ isMinOn_iff.mpr fun v hv ↦ ?_⟩
  have hvu : v - u ∈ W := TauCeti.sub_mem_of_mem_vadd_set hv hu
  have hgap := a.quadraticEnergy_add_of_forall_apply_eq ℓ ha hsol hvu
  rw [add_sub_cancel] at hgap
  linarith [hpos (v - u) hvu]

end FirstVariation

/-! ### Non-Hermitian coercive growth, near-minimizer rates, and bounded sublevels -/

section Coercive

variable {𝕜 V : Type*} [RCLike 𝕜] [SeminormedAddCommGroup V] [NormedSpace 𝕜 V]
  {a : V →L⋆[𝕜] V →L[𝕜] 𝕜} {ℓ : StrongDual 𝕜 V}

/-- **Quadratic energy-gap lower bound on a convex set** around a local minimizer `u ∈ C`: for
every `v ∈ C`, `re (a (v - u) (v - u)) ≤ E(v) - E(u)`. No symmetry of `a` is required. -/
theorem re_apply_sub_self_le_quadraticEnergy_sub_of_isLocalMinOn_convex
    [Module ℝ V] [IsScalarTower ℝ 𝕜 V] {C : Set V} (hC : Convex ℝ C) {u v : V}
    (hu : u ∈ C) (hv : v ∈ C) (hmin : IsLocalMinOn (a.quadraticEnergy ℓ) C u) :
    re (a (v - u) (v - u)) ≤ a.quadraticEnergy ℓ v - a.quadraticEnergy ℓ u := by
  have hpath_eq (t : ℝ) : u + (t : 𝕜) • (v - u) = t • v + (1 - t) • u := by
    rw [← algebraMap_eq_ofReal, algebraMap_smul]
    module
  have hcont : Continuous (fun t : ℝ ↦ u + (t : 𝕜) • (v - u)) :=
    continuous_const.add ((continuous_ofReal.comp continuous_id).smul continuous_const)
  have htend : Tendsto (fun t : ℝ ↦ u + (t : 𝕜) • (v - u)) (𝓝[>] 0) (𝓝[C] u) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · simpa only [ofReal_zero, zero_smul, add_zero] using
        (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
    · filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with t ht
      rw [← algebraMap_eq_ofReal, algebraMap_smul]
      exact hC.add_smul_sub_mem hu hv (Ioo_subset_Icc_self ht)
  have hle : ∀ᶠ t : ℝ in 𝓝[>] 0,
      (1 - t) * re (a (v - u) (v - u)) ≤ a.quadraticEnergy ℓ v - a.quadraticEnergy ℓ u := by
    filter_upwards [htend.eventually hmin, self_mem_nhdsWithin] with t ht htpos
    have ht' : a.quadraticEnergy ℓ u ≤ a.quadraticEnergy ℓ (u + (t : 𝕜) • (v - u)) := ht
    rw [hpath_eq t] at ht'
    have hcombo := a.quadraticEnergy_combo_add_mul_sub ℓ (by ring : t + (1 - t) = 1) v u
    have hmul : t * ((1 - t) * re (a (v - u) (v - u))) ≤
        t * (a.quadraticEnergy ℓ v - a.quadraticEnergy ℓ u) := by
      linarith
    exact le_of_mul_le_mul_left hmul htpos
  have hlim : Tendsto (fun t : ℝ ↦ (1 - t) * re (a (v - u) (v - u))) (𝓝[>] 0)
      (𝓝 (re (a (v - u) (v - u)))) := by
    have hc : Continuous (fun t : ℝ ↦ (1 - t) * re (a (v - u) (v - u))) := by fun_prop
    simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  exact le_of_tendsto hlim hle

/-- **Quantitative quadratic growth on a convex set** around a local minimizer `u ∈ C`: if
`c * ‖y - x‖² ≤ re (a (y - x) (y - x))` on `C`, then `c * ‖v - u‖² ≤ E(v) - E(u)` for all `v ∈ C`.
No symmetry of `a` is required. -/
theorem mul_norm_sub_sq_le_quadraticEnergy_sub_of_isLocalMinOn_convex
    [Module ℝ V] [IsScalarTower ℝ 𝕜 V] {C : Set V} (hC : Convex ℝ C)
    {c : ℝ} (hcoer : ∀ x ∈ C, ∀ y ∈ C, c * ‖y - x‖ ^ 2 ≤ re (a (y - x) (y - x)))
    {u v : V} (hu : u ∈ C) (hv : v ∈ C) (hmin : IsLocalMinOn (a.quadraticEnergy ℓ) C u) :
    c * ‖v - u‖ ^ 2 ≤ a.quadraticEnergy ℓ v - a.quadraticEnergy ℓ u :=
  (hcoer u hu v hv).trans
    (a.re_apply_sub_self_le_quadraticEnergy_sub_of_isLocalMinOn_convex hC hu hv hmin)

/-- **Near-minimizer distance rate on a convex set** `C`: for `c > 0`, every `v ∈ C` satisfies
`‖v - u‖² ≤ (E(v) - E(u)) / c` around a local minimizer `u ∈ C`. No symmetry of `a` is required. -/
theorem norm_sub_sq_le_quadraticEnergy_sub_div_of_isLocalMinOn_convex
    [Module ℝ V] [IsScalarTower ℝ 𝕜 V] {C : Set V} (hC : Convex ℝ C) {c : ℝ} (hc : 0 < c)
    (hcoer : ∀ x ∈ C, ∀ y ∈ C, c * ‖y - x‖ ^ 2 ≤ re (a (y - x) (y - x)))
    {u v : V} (hu : u ∈ C) (hv : v ∈ C) (hmin : IsLocalMinOn (a.quadraticEnergy ℓ) C u) :
    ‖v - u‖ ^ 2 ≤ (a.quadraticEnergy ℓ v - a.quadraticEnergy ℓ u) / c := by
  rw [le_div_iff₀ hc, mul_comm]
  exact a.mul_norm_sub_sq_le_quadraticEnergy_sub_of_isLocalMinOn_convex hC hcoer hu hv hmin

/-- **Near-minimizer distance rate** on `g +ᵥ W`: for `c > 0`, every admissible `v ∈ g +ᵥ W`
satisfies `‖v - u‖² ≤ (E(v) - E(u)) / c` around a local minimizer `u ∈ g +ᵥ W`. No symmetry of `a`
is required. -/
theorem norm_sub_sq_le_quadraticEnergy_sub_div_of_isLocalMinOn_vadd
    {W : Submodule 𝕜 V} {c : ℝ} (hc : 0 < c)
    (hcoer : ∀ w ∈ W, c * ‖w‖ ^ 2 ≤ re (a w w)) {g u v : V}
    (hu : u ∈ g +ᵥ (W : Set V)) (hv : v ∈ g +ᵥ (W : Set V))
    (hmin : IsLocalMinOn (a.quadraticEnergy ℓ) (g +ᵥ (W : Set V)) u) :
    ‖v - u‖ ^ 2 ≤ (a.quadraticEnergy ℓ v - a.quadraticEnergy ℓ u) / c := by
  let : NormedSpace ℝ V := NormedSpace.restrictScalars ℝ 𝕜 V
  have : IsScalarTower ℝ 𝕜 V := IsScalarTower.restrictScalars ℝ 𝕜 V
  exact a.norm_sub_sq_le_quadraticEnergy_sub_div_of_isLocalMinOn_convex
    ((W.restrictScalars ℝ).convex.vadd g) hc
    (fun _ hx _ hy ↦ hcoer _ (TauCeti.sub_mem_of_mem_vadd_set hy hx)) hu hv hmin

/-- **Norm convergence of near-minimizers on a convex set** `C`: if `a` is `c`-coercive on
differences in `C` (`c > 0`), `u ∈ C` locally minimizes `a.quadraticEnergy ℓ` on `C`, and
`x i ∈ C` satisfies `E(x i) → E(u)`, then `x i → u` in norm. No symmetry of `a` is required. -/
theorem tendsto_of_tendsto_quadraticEnergy_convex [Module ℝ V] [IsScalarTower ℝ 𝕜 V]
    {ι : Type*} {l : Filter ι} {C : Set V} (hC : Convex ℝ C) {c : ℝ} (hc : 0 < c)
    (hcoer : ∀ x ∈ C, ∀ y ∈ C, c * ‖y - x‖ ^ 2 ≤ re (a (y - x) (y - x)))
    {u : V} (hu : u ∈ C) (hmin : IsLocalMinOn (a.quadraticEnergy ℓ) C u)
    {x : ι → V} (hx : ∀ᶠ i in l, x i ∈ C)
    (hE : Tendsto (fun i ↦ a.quadraticEnergy ℓ (x i)) l (𝓝 (a.quadraticEnergy ℓ u))) :
    Tendsto x l (𝓝 u) :=
  TauCeti.tendsto_of_dist_pow_le_of_tendsto_zero
    (hx.mono fun _ hi ↦ by
      simpa only [← dist_eq_norm] using
        a.norm_sub_sq_le_quadraticEnergy_sub_div_of_isLocalMinOn_convex hC hc hcoer hu hi hmin)
    (by simpa only [sub_self, zero_div] using (hE.sub_const (a.quadraticEnergy ℓ u)).div_const c)

/-- **Norm convergence of near-minimizers on `g +ᵥ W`** around a local minimizer `u ∈ g +ᵥ W`,
without assuming symmetry of `a`. -/
theorem tendsto_of_tendsto_quadraticEnergy_vadd {ι : Type*} {l : Filter ι}
    {W : Submodule 𝕜 V} {c : ℝ} (hc : 0 < c)
    (hcoer : ∀ w ∈ W, c * ‖w‖ ^ 2 ≤ re (a w w)) {g u : V}
    (hu : u ∈ g +ᵥ (W : Set V)) (hmin : IsLocalMinOn (a.quadraticEnergy ℓ) (g +ᵥ (W : Set V)) u)
    {x : ι → V} (hx : ∀ᶠ i in l, x i ∈ g +ᵥ (W : Set V))
    (hE : Tendsto (fun i ↦ a.quadraticEnergy ℓ (x i)) l (𝓝 (a.quadraticEnergy ℓ u))) :
    Tendsto x l (𝓝 u) :=
  TauCeti.tendsto_of_dist_pow_le_of_tendsto_zero
    (hx.mono fun _ hi ↦ by
      simpa only [← dist_eq_norm] using
        a.norm_sub_sq_le_quadraticEnergy_sub_div_of_isLocalMinOn_vadd hc hcoer hu hi hmin)
    (by simpa only [sub_self, zero_div] using (hE.sub_const (a.quadraticEnergy ℓ u)).div_const c)

/-- **Bounded sublevels** of a coercive quadratic energy on `S`: if `c * ‖u‖² ≤ re (a u u)` on `S`
with `c > 0`, then `TauCeti.HasBoundedSublevelsOn (a.quadraticEnergy ℓ) S`. No symmetry of `a` is
required. -/
theorem hasBoundedSublevelsOn_quadraticEnergy (a : V →L⋆[𝕜] V →L[𝕜] 𝕜) (ℓ : StrongDual 𝕜 V)
    {S : Set V} {c : ℝ} (hc : 0 < c) (hcoer : ∀ u ∈ S, c * ‖u‖ ^ 2 ≤ re (a u u)) :
    TauCeti.HasBoundedSublevelsOn (a.quadraticEnergy ℓ) S := by
  rw [TauCeti.hasBoundedSublevelsOn_iff_forall_exists_le_of_le_norm]
  intro b
  refine ⟨max 1 ((2 * ‖ℓ‖ + max b 0) / c), fun u hu hR ↦ ?_⟩
  have h1 : 1 ≤ ‖u‖ := (le_max_left _ _).trans hR
  have h2 : 2 * ‖ℓ‖ + max b 0 ≤ ‖u‖ * c :=
    (div_le_iff₀ hc).mp ((le_max_right _ _).trans hR)
  have hℓ : re (ℓ u) ≤ ‖ℓ‖ * ‖u‖ :=
    (re_le_norm (ℓ u)).trans (ℓ.le_opNorm u)
  have hb0 : 0 ≤ max b 0 := le_max_right b 0
  have hb1 : b ≤ max b 0 := le_max_left b 0
  have hquad := hcoer u hu
  rw [quadraticEnergy_apply]
  nlinarith

/-- **Bounded sublevels from coercivity on differences.** If `c * ‖y - x‖² ≤ re (a (y - x) (y - x))`
for all `x, y ∈ C` (`c > 0`), then `a.quadraticEnergy ℓ` has bounded sublevels on `C`. Neither
symmetry of `a` nor nonemptiness of `C` is required. -/
theorem hasBoundedSublevelsOn_quadraticEnergy_of_sub_coercive (a : V →L⋆[𝕜] V →L[𝕜] 𝕜)
    (ℓ : StrongDual 𝕜 V) {C : Set V} {c : ℝ} (hc : 0 < c)
    (hcoer : ∀ x ∈ C, ∀ y ∈ C, c * ‖y - x‖ ^ 2 ≤ re (a (y - x) (y - x))) :
    TauCeti.HasBoundedSublevelsOn (a.quadraticEnergy ℓ) C := by
  rcases C.eq_empty_or_nonempty with rfl | ⟨u₀, hu₀⟩
  · exact TauCeti.hasBoundedSublevelsOn_empty
  · rw [TauCeti.hasBoundedSublevelsOn_iff_forall_exists_le_of_le_norm]
    intro b
    let M : ℝ := 2 * ‖a‖ * ‖u₀‖ + 2 * ‖ℓ‖
    refine ⟨‖u₀‖ + max 1 ((M + max (b - a.quadraticEnergy ℓ u₀) 0) / c), fun u hu hR ↦ ?_⟩
    set w : V := u - u₀
    have htri : ‖u‖ ≤ ‖u₀‖ + ‖w‖ := by
      simpa only [w, add_sub_cancel] using norm_add_le u₀ (u - u₀)
    have hw_ge : max 1 ((M + max (b - a.quadraticEnergy ℓ u₀) 0) / c) ≤ ‖w‖ := by linarith
    have hw1 : 1 ≤ ‖w‖ := (le_max_left _ _).trans hw_ge
    have hw2 : M + max (b - a.quadraticEnergy ℓ u₀) 0 ≤ ‖w‖ * c :=
      (div_le_iff₀ hc).mp ((le_max_right _ _).trans hw_ge)
    dsimp only [M] at hw2
    have ha₁ : -(‖a‖ * ‖u₀‖ * ‖w‖) ≤ re (a u₀ w) :=
      neg_le_of_abs_le ((abs_re_le_norm _).trans (a.le_opNorm₂ u₀ w))
    have ha₂ : -(‖a‖ * ‖w‖ * ‖u₀‖) ≤ re (a w u₀) :=
      neg_le_of_abs_le ((abs_re_le_norm _).trans (a.le_opNorm₂ w u₀))
    have hℓw : re (ℓ w) ≤ ‖ℓ‖ * ‖w‖ :=
      (re_le_norm _).trans (ℓ.le_opNorm w)
    have hquad : c * ‖w‖ ^ 2 ≤ re (a w w) := hcoer u₀ hu₀ u hu
    have hinc := a.quadraticEnergy_add_sub ℓ u₀ w
    have huw : u₀ + w = u := add_sub_cancel u₀ u
    rw [huw] at hinc
    have hb0 : 0 ≤ max (b - a.quadraticEnergy ℓ u₀) 0 := le_max_right _ _
    have hb1 : b - a.quadraticEnergy ℓ u₀ ≤ max (b - a.quadraticEnergy ℓ u₀) 0 := le_max_left _ _
    nlinarith

/-- **Bounded sublevels on an inhomogeneous affine coset** `g +ᵥ W`: it suffices that `a` be
`c`-coercive (`c > 0`) on the direction submodule `W` alone; `a` need not be symmetric and may
vanish or be indefinite on the datum `g`. -/
theorem hasBoundedSublevelsOn_quadraticEnergy_vadd (a : V →L⋆[𝕜] V →L[𝕜] 𝕜)
    (ℓ : StrongDual 𝕜 V) {W : Submodule 𝕜 V} (g : V)
    {c : ℝ} (hc : 0 < c) (hcoer : ∀ w ∈ W, c * ‖w‖ ^ 2 ≤ re (a w w)) :
    TauCeti.HasBoundedSublevelsOn (a.quadraticEnergy ℓ) (g +ᵥ (W : Set V)) :=
  a.hasBoundedSublevelsOn_quadraticEnergy_of_sub_coercive ℓ hc fun _ hx _ hy ↦
    hcoer _ (TauCeti.sub_mem_of_mem_vadd_set hy hx)

end Coercive

section Lifting

variable {H V : Type*} [SeminormedAddCommGroup H] [NormedSpace ℝ H]
  [SeminormedAddCommGroup V] [NormedSpace ℝ V]

/-- **Dirichlet's principle with a lifting.** Let `B` be a symmetric bounded bilinear form on `H`,
nonnegative on the image of `S : V →L[ℝ] H`. For a lifting `g : H` and a forcing `ℓ`, the energy
`J(w) = B(g + S w, g + S w) / 2 - ℓ w` has a minimum on `V` at `w₀` exactly when `u = g + S w₀`
solves the variational equation `B(u, S v) = ℓ v` for every `v : V`. -/
theorem isMinOn_iff_forall_apply_eq (B : H →L[ℝ] H →L[ℝ] ℝ) (S : V →L[ℝ] H)
    (hsymm : ∀ x y, B x y = B y x) (hnonneg : ∀ w, 0 ≤ B (S w) (S w)) (g : H)
    (ℓ : StrongDual ℝ V) (w₀ : V) :
    IsMinOn (fun w => B (g + S w) (g + S w) / 2 - ℓ w) univ w₀ ↔
      ∀ v, B (g + S w₀) (S v) = ℓ v := by
  -- `J` is `B(g, g) / 2` plus half the quadratic energy of `B(S ·, S ·)` with forcing
  -- `ℓ - B(g, S ·)`.
  have hJ (w : V) : B (g + S w) (g + S w) / 2 - ℓ w =
      B g g / 2 + (B.bilinearComp S S).quadraticEnergy (ℓ - (B g).comp S) w / 2 := by
    simp only [quadraticEnergy_apply, re_to_real, bilinearComp_apply, sub_apply, comp_apply,
      map_add, add_apply, hsymm (S w) g]
    ring
  have hmin := isMinOn_quadraticEnergy_iff (a := B.bilinearComp S S) (ℓ - (B g).comp S)
    (fun u v => by rw [bilinearComp_apply, bilinearComp_apply, hsymm, star_trivial])
    (fun w => by rw [re_to_real]; exact hnonneg w) (u := w₀)
  simp only [isMinOn_univ_iff, hJ, add_le_add_iff_left,
    div_le_div_iff_of_pos_right (two_pos : (0 : ℝ) < 2)] at hmin ⊢
  rw [hmin, ContinuousLinearMap.ext_iff]
  simp only [bilinearComp_apply, sub_apply, comp_apply, map_add, add_apply, eq_sub_iff_add_eq,
    add_comm (B g _)]

end Lifting

/-! ### Normed spaces: uniqueness, smoothness, Fréchet derivatives, and direct-method existence -/

section Normed

variable {𝕜 V : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [NormedSpace 𝕜 V]
  {a : V →L⋆[𝕜] V →L[𝕜] 𝕜} {ℓ : StrongDual 𝕜 V}

/-- **Uniqueness of weak solutions.** If the energy of `a` dominates `c ‖w‖²` on `W` with
`0 < c`, two solutions of the weak equation on `W` that differ by an element of `W` agree. -/
theorem eq_of_forall_apply_eq_of_coercive {W : Submodule 𝕜 V} {c : ℝ} (hc0 : 0 < c)
    (hc : ∀ w ∈ W, c * ‖w‖ ^ 2 ≤ re (a w w)) {u u' : V} (hu : ∀ v ∈ W, a u v = ℓ v)
    (hu' : ∀ v ∈ W, a u' v = ℓ v) (h : u' - u ∈ W) : u' = u := by
  have hbound := a.mul_norm_sub_le_norm_sub_of_coercive ℓ hc hu' hu h
  simp only [sub_self, norm_zero] at hbound
  exact sub_eq_zero.mp (norm_le_zero_iff.mp (nonpos_of_mul_nonpos_right hbound hc0))

section Calculus

variable [NormedSpace ℝ V] [IsScalarTower ℝ 𝕜 V] {n : WithTop ℕ∞}

/-- `a.quadraticEnergy ℓ` is `C^n` over `ℝ` for every `n`, without assuming symmetry of `a`. -/
@[fun_prop]
theorem contDiff_quadraticEnergy (a : V →L⋆[𝕜] V →L[𝕜] 𝕜) (ℓ : StrongDual 𝕜 V) :
    ContDiff ℝ n (a.quadraticEnergy ℓ) :=
  a.contDiff_re_apply_self.sub
    (contDiff_const.mul (reCLM.contDiff.comp (ℓ.restrictScalars ℝ).contDiff))

/-- `a.quadraticEnergy ℓ` is Fréchet differentiable over `ℝ`, without assuming symmetry of `a`. -/
@[fun_prop]
theorem differentiable_quadraticEnergy (a : V →L⋆[𝕜] V →L[𝕜] 𝕜) (ℓ : StrongDual 𝕜 V) :
    Differentiable ℝ (a.quadraticEnergy ℓ) :=
  (a.contDiff_quadraticEnergy (n := 1) ℓ).differentiable one_ne_zero

/-- **Strict real Fréchet derivative** of `a.quadraticEnergy ℓ` for a Hermitian form `a`: at `u`,
the derivative is `v ↦ 2 * re (a u v - ℓ v)`. -/
theorem hasStrictFDerivAt_quadraticEnergy (ℓ : StrongDual 𝕜 V)
    (ha : ∀ u v, a u v = star (a v u)) (u : V) :
    HasStrictFDerivAt (a.quadraticEnergy ℓ)
      ((2 : ℝ) • reCLM.comp ((a u - ℓ).restrictScalars ℝ)) u := by
  have hq := a.hasStrictFDerivAt_re_apply_self_of_eq_star ha u
  have hℓ : HasStrictFDerivAt (fun w ↦ 2 * re (ℓ w))
      ((2 : ℝ) • reCLM.comp (ℓ.restrictScalars ℝ)) u :=
    ((2 : ℝ) • reCLM.comp (ℓ.restrictScalars ℝ)).hasStrictFDerivAt.congr_of_eventuallyEq
      (Eventually.of_forall fun _ ↦ by simp)
  have hderiv : (2 : ℝ) • reCLM.comp ((a u).restrictScalars ℝ) -
      (2 : ℝ) • reCLM.comp (ℓ.restrictScalars ℝ) =
      (2 : ℝ) • reCLM.comp ((a u - ℓ).restrictScalars ℝ) := by
    ext v
    simp
    ring
  exact hderiv ▸ hq.sub hℓ

/-- **The first variation of a quadratic energy.** On the real restriction of scalars, the
quadratic energy of a Hermitian form has Fréchet derivative `v ↦ 2 re (a u v - ℓ v)` at `u`. -/
theorem hasFDerivAt_quadraticEnergy (ℓ : StrongDual 𝕜 V)
    (ha : ∀ u v, a u v = star (a v u)) (u : V) :
    HasFDerivAt (a.quadraticEnergy ℓ) ((2 : ℝ) • reCLM.comp ((a u - ℓ).restrictScalars ℝ)) u :=
  (a.hasStrictFDerivAt_quadraticEnergy ℓ ha u).hasFDerivAt

/-- Differential `fderiv ℝ (a.quadraticEnergy ℓ) u` for a Hermitian form `a`. -/
theorem fderiv_quadraticEnergy (ℓ : StrongDual 𝕜 V)
    (ha : ∀ u v, a u v = star (a v u)) (u : V) :
    fderiv ℝ (a.quadraticEnergy ℓ) u = (2 : ℝ) • reCLM.comp ((a u - ℓ).restrictScalars ℝ) :=
  (a.hasFDerivAt_quadraticEnergy ℓ ha u).fderiv

/-- Directional formula for `fderiv ℝ (a.quadraticEnergy ℓ) u v` for a Hermitian form `a`. -/
theorem fderiv_quadraticEnergy_apply (ℓ : StrongDual 𝕜 V)
    (ha : ∀ u v, a u v = star (a v u)) (u v : V) :
    fderiv ℝ (a.quadraticEnergy ℓ) u v = 2 * re (a u v - ℓ v) := by
  rw [a.fderiv_quadraticEnergy ℓ ha]
  simp

end Calculus

/-- **Uniqueness of local minimizers on a convex set** `C` when `a` is `c`-coercive on differences
in `C` (`c > 0`). No symmetry of `a` is required. -/
theorem eq_of_isLocalMinOn_quadraticEnergy_convex [Module ℝ V] [IsScalarTower ℝ 𝕜 V]
    {C : Set V} (hC : Convex ℝ C) {c : ℝ} (hc : 0 < c)
    (hcoer : ∀ x ∈ C, ∀ y ∈ C, c * ‖y - x‖ ^ 2 ≤ re (a (y - x) (y - x)))
    {u₁ u₂ : V} (hu₁ : u₁ ∈ C) (hu₂ : u₂ ∈ C)
    (hmin₁ : IsLocalMinOn (a.quadraticEnergy ℓ) C u₁)
    (hmin₂ : IsLocalMinOn (a.quadraticEnergy ℓ) C u₂) : u₁ = u₂ := by
  have h₁ := a.mul_norm_sub_sq_le_quadraticEnergy_sub_of_isLocalMinOn_convex hC hcoer hu₁ hu₂ hmin₁
  have h₂ := a.mul_norm_sub_sq_le_quadraticEnergy_sub_of_isLocalMinOn_convex hC hcoer hu₂ hu₁ hmin₂
  rw [norm_sub_rev u₂ u₁] at h₁
  have hsq : ‖u₁ - u₂‖ ^ 2 ≤ 0 := by nlinarith
  exact sub_eq_zero.mp (norm_le_zero_iff.mp (sq_eq_zero_iff.mp (le_antisymm hsq (sq_nonneg _))).le)

/-- **Uniqueness of local minimizers on an affine coset** `g +ᵥ W` when `a` is `c`-coercive on `W`
(`c > 0`). No symmetry of `a` is required. -/
theorem eq_of_isLocalMinOn_quadraticEnergy_vadd
    {W : Submodule 𝕜 V} {c : ℝ} (hc : 0 < c)
    (hcoer : ∀ w ∈ W, c * ‖w‖ ^ 2 ≤ re (a w w)) {g u₁ u₂ : V}
    (hu₁ : u₁ ∈ g +ᵥ (W : Set V)) (hu₂ : u₂ ∈ g +ᵥ (W : Set V))
    (hmin₁ : IsLocalMinOn (a.quadraticEnergy ℓ) (g +ᵥ (W : Set V)) u₁)
    (hmin₂ : IsLocalMinOn (a.quadraticEnergy ℓ) (g +ᵥ (W : Set V)) u₂) : u₁ = u₂ := by
  let : NormedSpace ℝ V := NormedSpace.restrictScalars ℝ 𝕜 V
  have : IsScalarTower ℝ 𝕜 V := IsScalarTower.restrictScalars ℝ 𝕜 V
  exact a.eq_of_isLocalMinOn_quadraticEnergy_convex ((W.restrictScalars ℝ).convex.vadd g) hc
    (fun _ hx _ hy ↦ hcoer _ (TauCeti.sub_mem_of_mem_vadd_set hy hx)) hu₁ hu₂ hmin₁ hmin₂

/-- **Direct-method existence and uniqueness on a closed convex set.** In a reflexive normed space
over `𝕜`, if `a` is `c`-coercive on differences of points in a nonempty closed convex set `C`
(`c > 0`), then `a.quadraticEnergy ℓ` attains a unique global minimum on `C`. No symmetry of `a` is
required. -/
theorem existsUnique_isMinOn_quadraticEnergy_of_isClosed_convex
    [Module ℝ V] [IsScalarTower ℝ 𝕜 V]
    (hV : Function.Surjective (inclusionInDoubleDual 𝕜 V))
    (a : V →L⋆[𝕜] V →L[𝕜] 𝕜) {C : Set V} (hne : C.Nonempty) (hC : Convex ℝ C) (hclosed : IsClosed C)
    {c : ℝ} (hc : 0 < c)
    (hcoer : ∀ x ∈ C, ∀ y ∈ C, c * ‖y - x‖ ^ 2 ≤ re (a (y - x) (y - x)))
    (ℓ : StrongDual 𝕜 V) :
    ∃! u, u ∈ C ∧ IsMinOn (a.quadraticEnergy ℓ) C u := by
  have : LocallyConvexSpace ℝ V := NormedSpace.toLocallyConvexSpace' 𝕜
  have hwclosed : IsClosed (toWeakSpace 𝕜 V '' C) := hC.isClosed_toWeakSpace_image 𝕜 hclosed
  have hpos : ∀ u ∈ C, ∀ v ∈ C, 0 ≤ re (a (u - v) (u - v)) := fun u hu v hv ↦
    (mul_nonneg hc.le (sq_nonneg _)).trans (hcoer v hv u hu)
  obtain ⟨u, hu, hmin⟩ := TauCeti.exists_isMinOn_of_weak_closed hV hne hwclosed
    (a.lowerSemicontinuousOn_quadraticEnergy_comp_toWeakSpace_symm hC hpos ℓ)
    (a.hasBoundedSublevelsOn_quadraticEnergy_of_sub_coercive ℓ hc hcoer)
  exact ⟨u, ⟨hu, hmin⟩, fun y ⟨hy, hminy⟩ ↦
    a.eq_of_isLocalMinOn_quadraticEnergy_convex hC hc hcoer hy hu
      hminy.isLocalMinOn hmin.isLocalMinOn⟩

/-- **Unconstrained direct-method existence and uniqueness.** In a reflexive normed space over `𝕜`,
if `∀ w, c * ‖w‖² ≤ re (a w w)` (`c > 0`), then `a.quadraticEnergy ℓ` attains a unique global
minimum on `V`. No symmetry of `a` is required. -/
theorem existsUnique_isMinOn_quadraticEnergy_univ_of_coercive
    (hV : Function.Surjective (inclusionInDoubleDual 𝕜 V))
    (a : V →L⋆[𝕜] V →L[𝕜] 𝕜) {c : ℝ} (hc : 0 < c)
    (hcoer : ∀ w, c * ‖w‖ ^ 2 ≤ re (a w w)) (ℓ : StrongDual 𝕜 V) :
    ∃! u, IsMinOn (a.quadraticEnergy ℓ) univ u := by
  let : NormedSpace ℝ V := NormedSpace.restrictScalars ℝ 𝕜 V
  have : IsScalarTower ℝ 𝕜 V := IsScalarTower.restrictScalars ℝ 𝕜 V
  simpa only [mem_univ, true_and] using
    a.existsUnique_isMinOn_quadraticEnergy_of_isClosed_convex hV univ_nonempty convex_univ
      isClosed_univ hc (fun x _ y _ ↦ hcoer (y - x)) ℓ

/-- **Direct-method existence and uniqueness of constrained weak solutions** on an affine coset
`g +ᵥ W` of a closed `𝕜`-submodule `W` in a reflexive normed space over `𝕜`, when `a` is Hermitian
and `c`-coercive on `W` (`c > 0`); `a` need not be nonnegative outside `W`. -/
theorem existsUnique_vadd_forall_apply_eq_of_isClosed_of_coercive
    (hV : Function.Surjective (inclusionInDoubleDual 𝕜 V))
    (ha : ∀ x y, a x y = star (a y x))
    {W : Submodule 𝕜 V} (hW : IsClosed (W : Set V))
    {c : ℝ} (hc : 0 < c) (hcoer : ∀ w ∈ W, c * ‖w‖ ^ 2 ≤ re (a w w))
    (g : V) (ℓ : StrongDual 𝕜 V) :
    ∃! u, u ∈ g +ᵥ (W : Set V) ∧ ∀ w ∈ W, a u w = ℓ w := by
  let : NormedSpace ℝ V := NormedSpace.restrictScalars ℝ 𝕜 V
  have : IsScalarTower ℝ 𝕜 V := IsScalarTower.restrictScalars ℝ 𝕜 V
  have hpos : ∀ w ∈ W, 0 ≤ re (a w w) := fun w hw ↦
    (mul_nonneg hc.le (sq_nonneg _)).trans (hcoer w hw)
  refine (existsUnique_congr fun u ↦ and_congr_right fun hu ↦
    a.isMinOn_quadraticEnergy_vadd_iff ha hpos hu).mp ?_
  exact a.existsUnique_isMinOn_quadraticEnergy_of_isClosed_convex hV
    ⟨g + 0, vadd_mem_vadd_set W.zero_mem⟩ ((W.restrictScalars ℝ).convex.vadd g) (hW.vadd g) hc
    (fun _ hx _ hy ↦ hcoer _ (TauCeti.sub_mem_of_mem_vadd_set hy hx)) ℓ

/-- **Global direct-method existence and uniqueness of weak solutions** in a reflexive normed space
over `𝕜` for a Hermitian form satisfying `∀ w, c * ‖w‖² ≤ re (a w w)` (`c > 0`). -/
theorem existsUnique_forall_apply_eq_of_coercive
    (hV : Function.Surjective (inclusionInDoubleDual 𝕜 V))
    (ha : ∀ x y, a x y = star (a y x))
    {c : ℝ} (hc : 0 < c) (hcoer : ∀ w, c * ‖w‖ ^ 2 ≤ re (a w w))
    (ℓ : StrongDual 𝕜 V) :
    ∃! u, ∀ v, a u v = ℓ v := by
  simpa using a.existsUnique_vadd_forall_apply_eq_of_isClosed_of_coercive (W := ⊤) hV ha
    (by simp) hc (fun w _ ↦ hcoer w) 0 ℓ

end Normed

/-! ### Hilbert-space Lax--Milgram identifications -/

section Complete

variable {𝕜 V : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [CompleteSpace V]
  {a : V →L⋆[𝕜] V →L[𝕜] 𝕜}

open InnerProductSpace

/-- On a Hilbert space, the global minimizer of the quadratic energy of a nonnegative Hermitian
form with invertible Fréchet--Riesz operator is the Lax--Milgram solution `solutionOfFunctional`. -/
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

/-- Value of `a.quadraticEnergy ℓ` at the Lax--Milgram solution `solutionOfFunctional a hB ℓ`
(its global minimum value when `a` is Hermitian and nonnegative). -/
@[simp]
theorem quadraticEnergy_solutionOfFunctional (a : V →L⋆[𝕜] V →L[𝕜] 𝕜)
    (hB : IsUnit (continuousLinearMapOfBilin a)) (ℓ : StrongDual 𝕜 V) :
    a.quadraticEnergy ℓ (solutionOfFunctional a hB ℓ) = -re (ℓ (solutionOfFunctional a hB ℓ)) := by
  rw [quadraticEnergy_apply, apply_solutionOfFunctional]
  ring

/-- Value of `a.quadraticEnergy ((innerSL 𝕜 h).comp j)` at `formSolutionMap a hB j h`, stated in
`simp`-normal form for `toSesqForm j h` (`toSesqForm_apply_coe`). -/
@[simp]
theorem quadraticEnergy_innerSL_comp_formSolutionMap (a : V →L⋆[𝕜] V →L[𝕜] 𝕜)
    (hB : IsUnit (continuousLinearMapOfBilin a))
    {H : Type*} [SeminormedAddCommGroup H] [InnerProductSpace 𝕜 H] (j : V →L[𝕜] H) (h : H) :
    a.quadraticEnergy ((innerSL 𝕜 h).comp j) (formSolutionMap a hB j h) =
      -re ⟪h, j (formSolutionMap a hB j h)⟫_𝕜 := by
  rw [quadraticEnergy_apply, apply_formSolutionMap]
  simp only [comp_apply, innerSL_apply_apply]
  ring

end Complete

end ContinuousLinearMap

namespace IsCoercive

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  {B : V →L[ℝ] V →L[ℝ] ℝ}

/-- Over `ℝ`, the global minimizer of the quadratic energy `B u u - 2 ℓ u` of a symmetric
coercive bilinear form is the Lax--Milgram solution `IsCoercive.solutionOfFunctional`. -/
theorem isMinOn_quadraticEnergy_iff_eq_solutionOfFunctional (hB : IsCoercive B)
    (hsymm : ∀ u v, B u v = B v u) (ℓ : StrongDual ℝ V) {u : V} :
    IsMinOn (B.quadraticEnergy ℓ) univ u ↔ u = hB.solutionOfFunctional ℓ := by
  rw [hB.solutionOfFunctional_eq]
  exact ContinuousLinearMap.isMinOn_quadraticEnergy_iff_eq_solutionOfFunctional
    (fun u v => by rw [hsymm, star_trivial])
    (fun w => by rw [re_to_real]; exact hB.apply_self_nonneg w) _ ℓ

/-- Over `ℝ`, `u` minimizes `B.quadraticEnergy ℓ` on `univ` for symmetric coercive `B` if and only
if `u` equals the inverse Lax--Milgram operator `hB.continuousLinearEquivOfBilin.symm` applied to
the Fréchet--Riesz representative of `ℓ`. -/
theorem isMinOn_quadraticEnergy_iff_eq_continuousLinearEquivOfBilin_symm (hB : IsCoercive B)
    (hsymm : ∀ u v, B u v = B v u) (ℓ : StrongDual ℝ V) {u : V} :
    IsMinOn (B.quadraticEnergy ℓ) univ u ↔
      u = hB.continuousLinearEquivOfBilin.symm ((InnerProductSpace.toDual ℝ V).symm ℓ) := by
  rw [hB.isMinOn_quadraticEnergy_iff_eq_solutionOfFunctional hsymm ℓ,
    solutionOfFunctional_apply, solutionOfInner_def]

/-- Over `ℝ`, for represented forcing `InnerProductSpace.toDual ℝ V F`, `u` minimizes
`B.quadraticEnergy (InnerProductSpace.toDual ℝ V F)` on `univ` for symmetric coercive `B` if and
only if `u = hB.solutionOfInner F`. -/
theorem isMinOn_quadraticEnergy_toDual_iff_eq_solutionOfInner (hB : IsCoercive B)
    (hsymm : ∀ u v, B u v = B v u) (F : V) {u : V} :
    IsMinOn (B.quadraticEnergy (InnerProductSpace.toDual ℝ V F)) univ u ↔
      u = hB.solutionOfInner F := by
  rw [hB.isMinOn_quadraticEnergy_iff_eq_solutionOfFunctional hsymm, solutionOfFunctional_toDual]

/-- Value of `B.quadraticEnergy ℓ` at `hB.solutionOfFunctional ℓ` (its global minimum value when
`B` is symmetric). -/
@[simp]
theorem quadraticEnergy_solutionOfFunctional (hB : IsCoercive B) (ℓ : StrongDual ℝ V) :
    B.quadraticEnergy ℓ (hB.solutionOfFunctional ℓ) = -ℓ (hB.solutionOfFunctional ℓ) := by
  rw [ContinuousLinearMap.quadraticEnergy_real_apply, hB.apply_solutionOfFunctional_eq]
  ring

/-- Value of `B.quadraticEnergy (InnerProductSpace.toDual ℝ V F)` at `hB.solutionOfInner F` (its
global minimum value when `B` is symmetric). -/
@[simp]
theorem quadraticEnergy_toDual_solutionOfInner (hB : IsCoercive B) (F : V) :
    B.quadraticEnergy (InnerProductSpace.toDual ℝ V F) (hB.solutionOfInner F) =
      -⟪F, hB.solutionOfInner F⟫_ℝ := by
  rw [← solutionOfFunctional_toDual, quadraticEnergy_solutionOfFunctional,
    solutionOfFunctional_toDual, InnerProductSpace.toDual_apply_apply]

end IsCoercive

end
