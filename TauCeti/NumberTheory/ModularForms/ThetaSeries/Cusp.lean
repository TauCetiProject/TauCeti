/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.ModularForms.CuspFormSubmodule
public import Mathlib.NumberTheory.ModularForms.QExpansion
public import TauCeti.NumberTheory.ModularForms.ThetaSeries.Translation
import Mathlib.Analysis.Normed.Group.Tannery
import TauCeti.Algebra.Module.ZLattice.Summable

/-!
# Theta series at the cusp `∞`

Let `L` be a discrete subgroup of a finite-dimensional real normed space `E`. This file studies
the theta series `Θ_L(τ) = ∑_{v ∈ L} exp (π i ‖v‖² τ)` and the theta series
`θ_{γ+L}(τ) = ∑_{v ∈ L} exp (π i ‖γ + v‖² τ)` of a translate as `im τ → ∞`, and on the imaginary
axis.

The term of index `v` has norm `exp (-π ‖γ + v‖² im τ)`. On a half-plane `{τ | y ≤ im τ}`,
`0 < y`, the terms are therefore dominated by the summable Gaussian `exp (-π y ‖γ + v‖²)`, so the
series are bounded at `i∞`; and as `im τ → ∞` every term tends to `0`, except the term of the
vector `v = -γ`, which is constantly `1` and exists only when `γ ∈ L`. By dominated convergence,
`Θ_L(τ) → 1`, while `θ_{γ+L}(τ) → 0` for `γ ∉ L`. Together with holomorphy and periodicity this
identifies the constant term of the `q`-expansion of `Θ_L`: it is `1`, in `q = exp (2 π i τ)` for
an even lattice and in `exp (π i τ)` for an integral one. It also shows that `Θ_L` is never a cusp
form, for any group having `∞` as a cusp.

On the imaginary axis `τ = i y` every term is the positive real number `exp (-π y ‖γ + v‖²)`, so
`θ_{γ+L}(i y)` is a positive real number and `Θ_L(i y) ≥ 1`. In particular `Θ_L` does not vanish
there; this is the nonvanishing used to show that the rank of an even unimodular lattice is
divisible by `8`. Splitting a discrete subgroup `L` into the cosets of `M ≤ L` further shows that
`θ_{γ+M}(i y) ≤ θ_{γ+L}(i y)` and `Θ_M(i y) ≤ Θ_L(i y)` on real parts, with equality if and only
if `M = L`.

## Main statements

* `ZLattice.tendsto_tsum_mul_thetaTerm_atImInfty`: a theta sum weighted by coefficients of norm at
  most `1` tends at `i∞` to the sum of the weights of the vectors `v ∈ L` with `γ + v = 0`.
* `ZLattice.isBoundedAtImInfty_thetaCoset`, `ZLattice.isBoundedAtImInfty_thetaSeries`: the theta
  series are bounded at `i∞`.
* `ZLattice.tendsto_thetaSeries_atImInfty`, `ZLattice.valueAtInfty_thetaSeries`: `Θ_L(τ) → 1` as
  `im τ → ∞`.
* `ZLattice.not_isZeroAtImInfty_thetaSeries`, `ZLattice.coe_ne_thetaSeries`,
  `ZLattice.not_isCuspForm_of_coe_eq_thetaSeries`: `Θ_L` does not vanish at `∞`, so it is not a
  cusp form on any group having `∞` as a cusp.
* `ZLattice.isZeroAtImInfty_thetaCoset`: `θ_{γ+L}(τ) → 0` as `im τ → ∞` when `γ ∉ L`.
* `ZLattice.IsEven.qExpansion_thetaSeries_coeff_zero`: for even `L` the constant term of the
  `q`-expansion of `Θ_L` is `1`; `ZLattice.IsIntegral.qExpansion_two_thetaSeries_coeff_zero` is
  the same statement in `exp (π i τ)` for integral `L`.
* `ZLattice.thetaCoset_eq_ofReal_of_re_eq_zero`, `ZLattice.re_thetaCoset_pos`,
  `ZLattice.one_le_re_thetaSeries`: on the imaginary axis `θ_{γ+L}` is real and positive, and
  `Θ_L ≥ 1`.
* `ZLattice.re_thetaCoset_mono`, `ZLattice.re_thetaCoset_strictMono`,
  `ZLattice.re_thetaSeries_mono`, `ZLattice.re_thetaSeries_strictMono`,
  `ZLattice.thetaSeries_eq_iff_eq_of_re_eq_zero`: on the imaginary axis `θ_{γ+L}` and `Θ_L` are
  strictly monotone in `L`.

## References

* J.-P. Serre, *A Course in Arithmetic*, Ch. VII §6.
* W. Ebeling, *Lattices and Codes*, Ch. 2.
-/

public section

open Complex Filter Topology
open UpperHalfPlane (atImInfty IsBoundedAtImInfty IsZeroAtImInfty valueAtInfty qExpansion
  ofComplex)
open scoped Real UpperHalfPlane

namespace ZLattice

section Normed

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  (L : Submodule ℤ E) [DiscreteTopology L]

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [DiscreteTopology L] in
/-- On the half-plane `{τ | y ≤ im τ}`, the theta series of `γ + L` is bounded in norm
by `∑_{v ∈ L} exp (-π y ‖γ + v‖²)`, its value at `i y`, provided this Gaussian sum converges (it
does for a discrete `L`, by `summable_exp_neg_mul_norm_add_sq`). -/
theorem norm_thetaCoset_le (γ : E) {y : ℝ}
    (hs : Summable fun v : L => Real.exp (-(π * y) * ‖γ + (v : E)‖ ^ 2)) {τ : ℍ}
    (hτ : y ≤ τ.im) :
    ‖thetaCoset L γ τ‖ ≤ ∑' v : L, Real.exp (-(π * y) * ‖γ + (v : E)‖ ^ 2) := by
  rw [thetaCoset_apply]
  exact tsum_of_norm_bounded hs.hasSum
    fun _ => norm_exp_pi_mul_I_mul_ofReal_mul_le (by positivity) hτ

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [DiscreteTopology L] in
/-- The theta series of a translate of a subgroup is bounded at `i∞`. -/
theorem isBoundedAtImInfty_thetaCoset (γ : E) : IsBoundedAtImInfty (thetaCoset L γ) := by
  by_cases h : ∃ y : ℝ, 0 < y ∧ Summable fun v : L => Real.exp (-(π * y) * ‖γ + (v : E)‖ ^ 2)
  · obtain ⟨y, _, hs⟩ := h
    exact UpperHalfPlane.isBoundedAtImInfty_iff.mpr
      ⟨_, y, fun _ hτ => norm_thetaCoset_le L γ hs hτ⟩
  · rw [thetaCoset_eq_zero_of_forall_not_summable L γ fun y hy hs => h ⟨y, hy, hs⟩]
    exact UpperHalfPlane.isBoundedAtImInfty_iff.mpr ⟨0, 0, fun _ _ => by simp⟩

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [DiscreteTopology L] in
/-- The theta series of a subgroup is bounded at `i∞`. -/
theorem isBoundedAtImInfty_thetaSeries : IsBoundedAtImInfty (thetaSeries L) := by
  simpa using isBoundedAtImInfty_thetaCoset L 0

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [DiscreteTopology L] in
open Classical in
/-- **Weighted theta sums at `i∞`.** For weights `w v` of norm at most `1`, the weighted theta
sum `∑_{v ∈ L} w v exp (π i ‖γ + v‖² τ)` tends at `i∞` to the sum of the weights of the vectors
`v ∈ L` with `γ + v = 0`, by dominated convergence: the term of such a `v` is constantly `w v`,
and every other term tends to `0`. The Gaussian sum `∑_{v ∈ L} exp (-π y ‖γ + v‖²)` has to
converge for some `y`, as it does for a discrete `L`, by `summable_exp_neg_mul_norm_add_sq`. -/
theorem tendsto_tsum_mul_thetaTerm_atImInfty (γ : E) (w : L → ℂ) (hw : ∀ v, ‖w v‖ ≤ 1)
    {y : ℝ} (hs : Summable fun v : L => Real.exp (-(π * y) * ‖γ + (v : E)‖ ^ 2)) :
    Tendsto (fun τ : ℍ => ∑' v : L, w v * cexp (π * I * (‖γ + (v : E)‖ ^ 2 : ℝ) * τ))
      atImInfty (𝓝 (∑' v : L, if γ + (v : E) = 0 then w v else 0)) := by
  refine tendsto_tsum_of_dominated_convergence hs (fun v => ?_) ?_
  · split_ifs with hv
    · simp [hv]
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero (fun _ => norm_nonneg _)
      (fun τ => (norm_mul_le _ _).trans (mul_le_of_le_one_left (norm_nonneg _) (hw v))) ?_
    simp_rw [norm_exp_pi_mul_I_mul_ofReal_mul, UpperHalfPlane.coe_im]
    exact Real.tendsto_exp_atBot.comp <|
      (tendsto_comap : Tendsto UpperHalfPlane.im atImInfty atTop).const_mul_atTop_of_neg
        (neg_lt_zero.mpr (mul_pos Real.pi_pos (pow_pos (norm_pos_iff.mpr hv) 2)))
  · filter_upwards [(UpperHalfPlane.atImInfty_mem {τ : ℍ | y ≤ τ.im}).mpr ⟨y, fun _ h => h⟩]
      with τ hτ v
    exact (norm_mul_le _ _).trans <| (mul_le_of_le_one_left (norm_nonneg _) (hw v)).trans <|
      norm_exp_pi_mul_I_mul_ofReal_mul_le (by positivity) hτ

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [DiscreteTopology L] in
open Classical in
/-- The theta series of `γ + L` tends at `i∞` to the number of vectors `v ∈ L` with `γ + v = 0`,
provided the Gaussian sum `∑_{v ∈ L} exp (-π y ‖γ + v‖²)` converges for some `y`. -/
private theorem tendsto_thetaCoset_atImInfty_tsum_ite (γ : E) {y : ℝ}
    (hs : Summable fun v : L => Real.exp (-(π * y) * ‖γ + (v : E)‖ ^ 2)) :
    Tendsto (thetaCoset L γ) atImInfty (𝓝 (∑' v : L, if γ + (v : E) = 0 then 1 else 0)) :=
  (tendsto_tsum_mul_thetaTerm_atImInfty L γ (fun _ => 1) (fun _ => norm_one.le) hs).congr
    fun τ => by simp [thetaCoset_apply]

/-- The theta series of a discrete subgroup tends to `1` at `i∞`: every term except the term
`exp 0 = 1` of the zero vector tends to `0`. -/
theorem tendsto_thetaSeries_atImInfty : Tendsto (thetaSeries L) atImInfty (𝓝 1) := by
  classical
  convert tendsto_thetaCoset_atImInfty_tsum_ite L 0
    (summable_exp_neg_mul_norm_add_sq L (c := π * 1) (by positivity) 0) using 2
  · simp
  · rw [← tsum_ite_eq (0 : L) fun _ => (1 : ℂ)]
    exact tsum_congr fun v => by split_ifs <;> simp_all

/-- The value of the theta series of a discrete subgroup at the cusp `∞` is `1`. -/
@[simp]
theorem valueAtInfty_thetaSeries : valueAtInfty (thetaSeries L) = 1 :=
  (tendsto_thetaSeries_atImInfty L).limUnder_eq

/-- The theta series of a discrete subgroup does not vanish at `i∞`, since it tends to `1`. -/
@[simp]
theorem not_isZeroAtImInfty_thetaSeries : ¬ IsZeroAtImInfty (thetaSeries L) := fun h =>
  one_ne_zero <| tendsto_nhds_unique (tendsto_thetaSeries_atImInfty L) h

/-- **The theta series is never a cusp form.** For a subgroup `Γ` of `GL(2, ℝ)` having `∞` as
a cusp, no cusp form on `Γ`, of any weight, has `Θ_L` as its underlying function, because `Θ_L`
does not vanish at `∞`. -/
theorem coe_ne_thetaSeries {F : Type*} [FunLike F ℍ ℂ] {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ}
    [CuspFormClass F Γ k] [Fact (IsCusp OnePoint.infty Γ)] (f : F) :
    ⇑f ≠ thetaSeries L := fun h =>
  not_isZeroAtImInfty_thetaSeries L (h ▸ CuspFormClass.zero_at_infty f)

/-- A modular form whose underlying function is `Θ_L`, on a subgroup `Γ` of `GL(2, ℝ)` having
`∞` as a cusp, is not a cusp form. -/
theorem not_isCuspForm_of_coe_eq_thetaSeries {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.HasDetOne]
    [Fact (IsCusp OnePoint.infty Γ)] {k : ℤ} {f : ModularForm Γ k}
    (hf : ⇑f = thetaSeries L) : ¬ ModularForm.IsCuspForm f := by
  rintro ⟨g, rfl⟩
  exact coe_ne_thetaSeries L g <| funext fun z =>
    (CuspForm.toModularFormₗ_apply g z).symm.trans (congrFun hf z)

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [DiscreteTopology L] in
/-- For `γ ∉ L` the theta series of the translate `γ + L` tends to `0` at `i∞`, since no vector
of `γ + L` is zero. -/
theorem isZeroAtImInfty_thetaCoset {γ : E} (hγ : γ ∉ L) : IsZeroAtImInfty (thetaCoset L γ) := by
  have h (v : L) : γ + (v : E) ≠ 0 := fun h0 => hγ <| by
    rw [eq_neg_of_add_eq_zero_left h0]
    exact neg_mem v.2
  by_cases hex : ∃ y : ℝ, 0 < y ∧ Summable fun v : L => Real.exp (-(π * y) * ‖γ + (v : E)‖ ^ 2)
  · obtain ⟨y, _, hs⟩ := hex
    simpa [h, UpperHalfPlane.IsZeroAtImInfty, ZeroAtFilter] using
      tendsto_thetaCoset_atImInfty_tsum_ite L γ hs
  · rw [thetaCoset_eq_zero_of_forall_not_summable L γ fun y hy hs => hex ⟨y, hy, hs⟩]
    exact tendsto_const_nhds

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [DiscreteTopology L] in
/-- For `γ ∉ L` the value of the theta series of `γ + L` at the cusp `∞` is `0`. -/
theorem valueAtInfty_thetaCoset {γ : E} (hγ : γ ∉ L) : valueAtInfty (thetaCoset L γ) = 0 :=
  (isZeroAtImInfty_thetaCoset L hγ).valueAtInfty_eq_zero

/-- The constant term of the `q`-expansion with period `h` of the theta series of a discrete
subgroup is `1`, whenever the theta series has period `h`. -/
theorem qExpansion_thetaSeries_coeff_zero {h : ℝ} (hh : 0 < h)
    (hper : ∀ τ : ℍ, thetaSeries L (h +ᵥ τ) = thetaSeries L τ) :
    (qExpansion h (thetaSeries L)).coeff 0 = 1 := by
  have hper' := UpperHalfPlane.periodic_comp_ofComplex hper
  rw [UpperHalfPlane.qExpansion_coeff_zero hh (UpperHalfPlane.analyticAt_cuspFunction_zero hh hper'
    (mdifferentiable_thetaSeries L) (isBoundedAtImInfty_thetaSeries L)) hper',
    valueAtInfty_thetaSeries]

variable {L} in
omit [DiscreteTopology L] in
/-- For an even lattice, the constant term of the `q`-expansion of `Θ_L` in
`q = exp (2 π i τ)` is `1`. -/
theorem IsEven.qExpansion_thetaSeries_coeff_zero (hL : IsEven L) :
    (qExpansion 1 (thetaSeries L)).coeff 0 = 1 := by
  have := hL.discreteTopology
  exact ZLattice.qExpansion_thetaSeries_coeff_zero L one_pos hL.thetaSeries_one_vadd

end Normed

section InnerProduct

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {L : Submodule ℤ E} [DiscreteTopology L]

omit [DiscreteTopology L] in
/-- For an integral lattice, the constant term of the `q`-expansion of `Θ_L` with period `2`, in
`exp (π i τ)`, is `1`. -/
theorem IsIntegral.qExpansion_two_thetaSeries_coeff_zero (hL : IsIntegral L) :
    (qExpansion 2 (thetaSeries L)).coeff 0 = 1 := by
  have := hL.discreteTopology
  exact ZLattice.qExpansion_thetaSeries_coeff_zero L two_pos hL.thetaSeries_two_vadd

end InnerProduct

section ImaginaryAxis

variable {E : Type*} [NormedAddCommGroup E] (L : Submodule ℤ E)

/-- On the imaginary axis the theta series of `γ + L` is real:
`θ_{γ+L}(i y) = ∑_{v ∈ L} exp (-π y ‖γ + v‖²)`. -/
theorem thetaCoset_eq_ofReal_of_re_eq_zero (γ : E) {τ : ℍ} (hτ : τ.re = 0) :
    thetaCoset L γ τ = ((∑' v : L, Real.exp (-(π * τ.im) * ‖γ + (v : E)‖ ^ 2) : ℝ) : ℂ) := by
  have hτ' : (τ : ℂ) = τ.im * I := Complex.ext (by simp [hτ]) (by simp)
  rw [thetaCoset_apply, ofReal_tsum]
  refine tsum_congr fun v => ?_
  rw [hτ', ofReal_exp]
  congr 1
  push_cast
  linear_combination (π * ‖γ + (v : E)‖ ^ 2 * τ.im : ℂ) * I_sq

/-- On the imaginary axis the theta series of `L` is real:
`Θ_L(i y) = ∑_{v ∈ L} exp (-π y ‖v‖²)`. -/
theorem thetaSeries_eq_ofReal_of_re_eq_zero {τ : ℍ} (hτ : τ.re = 0) :
    thetaSeries L τ = ((∑' v : L, Real.exp (-(π * τ.im) * ‖(v : E)‖ ^ 2) : ℝ) : ℂ) := by
  simpa using thetaCoset_eq_ofReal_of_re_eq_zero L 0 hτ

/-- On the imaginary axis the theta series of `γ + L` has zero imaginary part. -/
theorem im_thetaCoset_eq_zero_of_re_eq_zero (γ : E) {τ : ℍ} (hτ : τ.re = 0) :
    (thetaCoset L γ τ).im = 0 := by
  rw [thetaCoset_eq_ofReal_of_re_eq_zero L γ hτ, ofReal_im]

/-- On the imaginary axis the theta series of `L` has zero imaginary part. -/
theorem im_thetaSeries_eq_zero_of_re_eq_zero {τ : ℍ} (hτ : τ.re = 0) :
    (thetaSeries L τ).im = 0 := by
  simpa using im_thetaCoset_eq_zero_of_re_eq_zero L 0 hτ

/-- On the imaginary axis `θ_{γ+L}(τ)` equals the coercion of its real part. -/
theorem ofReal_re_thetaCoset_of_re_eq_zero (γ : E) {τ : ℍ} (hτ : τ.re = 0) :
    ((thetaCoset L γ τ).re : ℂ) = thetaCoset L γ τ :=
  Complex.ext (ofReal_re _) ((ofReal_im _).trans (im_thetaCoset_eq_zero_of_re_eq_zero L γ hτ).symm)

/-- On the imaginary axis `Θ_L(τ)` equals the coercion of its real part. -/
theorem ofReal_re_thetaSeries_of_re_eq_zero {τ : ℍ} (hτ : τ.re = 0) :
    ((thetaSeries L τ).re : ℂ) = thetaSeries L τ := by
  simpa using ofReal_re_thetaCoset_of_re_eq_zero L 0 hτ

variable [NormedSpace ℝ E] [FiniteDimensional ℝ E] [DiscreteTopology L]

/-- On the imaginary axis the theta series of `γ + L` has positive real part (and is real, by
`ZLattice.thetaCoset_eq_ofReal_of_re_eq_zero`). -/
theorem re_thetaCoset_pos (γ : E) {τ : ℍ} (hτ : τ.re = 0) : 0 < (thetaCoset L γ τ).re := by
  rw [thetaCoset_eq_ofReal_of_re_eq_zero L γ hτ, ofReal_re]
  exact (summable_exp_neg_mul_norm_add_sq L (by positivity) γ).tsum_pos
    (fun _ => (Real.exp_pos _).le) 0 (Real.exp_pos _)

/-- On the imaginary axis the theta series of a discrete subgroup has real part at least `1`, the
contribution of the zero vector (and is real, by `ZLattice.thetaCoset_eq_ofReal_of_re_eq_zero`). -/
theorem one_le_re_thetaSeries {τ : ℍ} (hτ : τ.re = 0) : 1 ≤ (thetaSeries L τ).re := by
  rw [← thetaCoset_zero, thetaCoset_eq_ofReal_of_re_eq_zero L 0 hτ, ofReal_re]
  simpa using (summable_exp_neg_mul_norm_add_sq L (c := π * τ.im) (by positivity) 0).le_tsum 0
    fun _ _ => (Real.exp_pos _).le

/-- The theta series of a discrete subgroup does not vanish on the imaginary axis. -/
theorem thetaSeries_ne_zero_of_re_eq_zero {τ : ℍ} (hτ : τ.re = 0) : thetaSeries L τ ≠ 0 :=
  fun h => (one_le_re_thetaSeries L hτ).not_gt (by rw [h, zero_re]; exact one_pos)

section Sublattice

variable {M : Submodule ℤ E} {L}

/-- On the imaginary axis, the real part of a translate theta series is strictly monotone in the
subgroup: every nontrivial coset of `M` in `L` contributes a strictly positive Gaussian sum. -/
theorem re_thetaCoset_strictMono (hML : M < L) (γ : E) {τ : ℍ} (hτ : τ.re = 0) :
    (thetaCoset M γ τ).re < (thetaCoset L γ τ).re := by
  have : DiscreteTopology M :=
    SetLike.isDiscrete_iff_discreteTopology.mp
      ((SetLike.isDiscrete_iff_discreteTopology.mpr ‹DiscreteTopology L›).mono hML.le)
  have hsum : HasSum (fun y : L ⧸ M.submoduleOf L ↦
      (thetaCoset M (γ + ((Quotient.out y : L) : E)) τ).re) (thetaCoset L γ τ).re :=
    Complex.reCLM.hasSum (hasSum_thetaCoset_add_out L hML.le γ τ)
  have hzero : thetaCoset M (γ + ((Quotient.out (0 : L ⧸ M.submoduleOf L) : L) : E)) τ =
      thetaCoset M γ τ := by
    refine congrFun (thetaCoset_eq_of_sub_mem M ?_) τ
    rw [add_sub_cancel_left]
    have h0 : Submodule.Quotient.mk (Quotient.out (0 : L ⧸ M.submoduleOf L)) =
        (0 : L ⧸ M.submoduleOf L) := Submodule.Quotient.mk_out 0
    simpa [Submodule.submoduleOf] using (Submodule.Quotient.mk_eq_zero _).mp h0
  obtain ⟨x, hxL, hxM⟩ := IsConcreteLE.exists_of_lt hML
  let q : L ⧸ M.submoduleOf L := Submodule.Quotient.mk ⟨x, hxL⟩
  have hq : q ≠ 0 := by
    rw [Ne, Submodule.Quotient.mk_eq_zero, Submodule.submoduleOf, Submodule.mem_comap,
      Submodule.subtype_apply]
    exact hxM
  rw [← hzero]
  exact lt_hasSum hsum 0 (fun _ _ ↦ (re_thetaCoset_pos M _ hτ).le) q hq
    (re_thetaCoset_pos M _ hτ)

/-- On the imaginary axis, the real part of a translate theta series is monotone in the
subgroup. -/
theorem re_thetaCoset_mono (hML : M ≤ L) (γ : E) {τ : ℍ} (hτ : τ.re = 0) :
    (thetaCoset M γ τ).re ≤ (thetaCoset L γ τ).re := by
  rcases hML.eq_or_lt with rfl | hlt
  · exact le_rfl
  · exact (re_thetaCoset_strictMono hlt γ hτ).le

/-- On the imaginary axis, for `M ≤ L`, `(thetaCoset M γ τ).re < (thetaCoset L γ τ).re` holds if
and only if `M < L`. -/
theorem re_thetaCoset_lt_iff_lt (hML : M ≤ L) (γ : E) {τ : ℍ} (hτ : τ.re = 0) :
    (thetaCoset M γ τ).re < (thetaCoset L γ τ).re ↔ M < L := by
  refine ⟨fun h ↦ hML.lt_of_ne ?_, fun h ↦ re_thetaCoset_strictMono h γ hτ⟩
  rintro rfl
  exact lt_irrefl _ h

/-- On the imaginary axis, for `M ≤ L`, `(thetaCoset M γ τ).re = (thetaCoset L γ τ).re` holds if
and only if `M = L`. -/
theorem re_thetaCoset_eq_iff_eq (hML : M ≤ L) (γ : E) {τ : ℍ} (hτ : τ.re = 0) :
    (thetaCoset M γ τ).re = (thetaCoset L γ τ).re ↔ M = L := by
  rw [← not_iff_not, ← ne_eq, (re_thetaCoset_mono hML γ hτ).lt_iff_ne.symm,
    re_thetaCoset_lt_iff_lt hML γ hτ, hML.lt_iff_ne]

/-- On the imaginary axis, for `M ≤ L`, `thetaCoset M γ τ = thetaCoset L γ τ` holds if and only if
`M = L`. -/
theorem thetaCoset_eq_iff_eq_of_re_eq_zero (hML : M ≤ L) (γ : E) {τ : ℍ} (hτ : τ.re = 0) :
    thetaCoset M γ τ = thetaCoset L γ τ ↔ M = L := by
  refine ⟨fun h ↦ (re_thetaCoset_eq_iff_eq hML γ hτ).mp (congrArg Complex.re h), ?_⟩
  rintro rfl
  rfl

/-- On the imaginary axis, a proper subgroup `M < L` has `θ_{γ+M}(τ) ≠ θ_{γ+L}(τ)`. -/
theorem thetaCoset_ne_of_lt_of_re_eq_zero (hML : M < L) (γ : E) {τ : ℍ} (hτ : τ.re = 0) :
    thetaCoset M γ τ ≠ thetaCoset L γ τ :=
  mt (thetaCoset_eq_iff_eq_of_re_eq_zero hML.le γ hτ).mp hML.ne

/-- On the imaginary axis, the real part of the theta series is strictly monotone in the
subgroup. -/
theorem re_thetaSeries_strictMono (hML : M < L) {τ : ℍ} (hτ : τ.re = 0) :
    (thetaSeries M τ).re < (thetaSeries L τ).re := by
  simpa using re_thetaCoset_strictMono hML 0 hτ

/-- On the imaginary axis, the real part of the theta series is monotone in the subgroup. -/
theorem re_thetaSeries_mono (hML : M ≤ L) {τ : ℍ} (hτ : τ.re = 0) :
    (thetaSeries M τ).re ≤ (thetaSeries L τ).re := by
  simpa using re_thetaCoset_mono hML 0 hτ

/-- On the imaginary axis, for `M ≤ L`, `(thetaSeries M τ).re < (thetaSeries L τ).re` holds if and
only if `M < L`. -/
theorem re_thetaSeries_lt_iff_lt (hML : M ≤ L) {τ : ℍ} (hτ : τ.re = 0) :
    (thetaSeries M τ).re < (thetaSeries L τ).re ↔ M < L := by
  simpa using re_thetaCoset_lt_iff_lt hML 0 hτ

/-- On the imaginary axis, for `M ≤ L`, `(thetaSeries M τ).re = (thetaSeries L τ).re` holds if and
only if `M = L`. -/
theorem re_thetaSeries_eq_iff_eq (hML : M ≤ L) {τ : ℍ} (hτ : τ.re = 0) :
    (thetaSeries M τ).re = (thetaSeries L τ).re ↔ M = L := by
  simpa using re_thetaCoset_eq_iff_eq hML 0 hτ

/-- On the imaginary axis, for `M ≤ L`, `thetaSeries M τ = thetaSeries L τ` holds if and only if
`M = L`. -/
theorem thetaSeries_eq_iff_eq_of_re_eq_zero (hML : M ≤ L) {τ : ℍ} (hτ : τ.re = 0) :
    thetaSeries M τ = thetaSeries L τ ↔ M = L := by
  simpa using thetaCoset_eq_iff_eq_of_re_eq_zero hML 0 hτ

/-- On the imaginary axis, a proper subgroup `M < L` has `Θ_M(τ) ≠ Θ_L(τ)`. -/
theorem thetaSeries_ne_of_lt_of_re_eq_zero (hML : M < L) {τ : ℍ} (hτ : τ.re = 0) :
    thetaSeries M τ ≠ thetaSeries L τ :=
  mt (thetaSeries_eq_iff_eq_of_re_eq_zero hML.le hτ).mp hML.ne

end Sublattice

end ImaginaryAxis

end ZLattice
