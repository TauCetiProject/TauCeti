/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.DSlope
import TauCeti.Analysis.Calculus.Deriv.Mul

/-!
# Elementary facts about `dslope`

Elementary divided-slope facts. Away from its base point `dslope` is the plain difference quotient,
so most of these are statements about a normed field and its norm. The product rule, germ
congruence, and coordinate factorization also use the derivative at the base point.

## Main results

* `TauCeti.dslope_comm`: `dslope` is symmetric in its two point arguments.
* `TauCeti.norm_dslope_eq_one_of_norm_sub_map_eq`: a map that moves two points exactly as far
  apart as they already are has unimodular difference quotient between them. This is the
  hypothesis the equality case of Schwarz's lemma
  (`Complex.affine_of_mapsTo_ball_of_norm_dslope_eq_div`) takes, and the two Tau Ceti consumers of
  that equality case — the Schwarz--Pick rigidity theorem and the classification of the disc
  rotations — reach it by exactly this route, at base point `0`.
* `TauCeti.sum_add_pow_sub_smul_iterate_dslope`: Taylor's formula with divided-difference
  remainder, `f b = Σ_{j<n} (b - a)^j • c_j + (b - a)^n • q_n b`, where `c_j` is the value at `a`
  of the `j`-th iterated divided difference `(swap dslope a)^[j] f` and `q_n` is the `n`-th one.
  For an analytic `f` the `c_j` are its Taylor coefficients at `a` and `q_n` is analytic.
* `TauCeti.dslope_mul`: the product rule for divided differences.
* `Filter.EventuallyEq.dslope`: divided differences at `a` of functions with the same germ at `a`
  have the same germ at `a`.
* `TauCeti.eventuallyEq_dslope_update_of_factorization`: a local coordinate factorization
  identifies the coordinate divided difference with its factor.
-/

public section

namespace TauCeti

/-- A function is its value at the base point plus the displacement times its divided
difference. -/
theorem eq_const_add_sub_smul_dslope {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] (f : 𝕜 → E) (a : 𝕜) :
    f = (fun _ ↦ f a) + (fun z ↦ z - a) • dslope f a := by
  funext z
  exact eq_add_of_sub_eq' (sub_smul_dslope f a z).symm

/-- `dslope` is symmetric in its two point arguments: off the diagonal both sides are the same
difference quotient, and on the diagonal they coincide trivially. -/
theorem dslope_comm {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] (f : 𝕜 → E) (a b : 𝕜) : dslope f a b = dslope f b a := by
  rcases eq_or_ne b a with rfl | h
  · rfl
  · rw [dslope_of_ne f h, dslope_of_ne f h.symm, slope_comm]

/-- **A map preserving the distance between two points has unit difference quotient between
them.** For `y ≠ x` with `‖g y - g x‖ = ‖y - x‖`, the difference quotient `dslope g x y` is
unimodular.

No differentiability is involved: away from the base point `dslope` is the plain difference
quotient. -/
lemma norm_dslope_eq_one_of_norm_sub_map_eq {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] {g : 𝕜 → E} {x y : 𝕜} (hxy : y ≠ x)
    (hnorm : ‖g y - g x‖ = ‖y - x‖) : ‖dslope g x y‖ = 1 := by
  rw [dslope_of_ne _ hxy, slope_def_module, norm_smul, norm_inv, hnorm,
    inv_mul_cancel₀ (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hxy))]

/-- **Taylor's formula with divided-difference remainder.** For every function `f` and every `n`,
`f b = Σ_{j<n} (b - a)^j • c_j + (b - a)^n • q_n b`, where `c_j = (swap dslope a)^[j] f a` and
`q_n = (swap dslope a)^[n] f`. This is `n` applications of `f b = f a + (b - a) • dslope f a b`.
When the `c_j` vanish this is Mathlib's `pow_sub_smul_iterate_dslope_of_zero`. -/
theorem sum_add_pow_sub_smul_iterate_dslope {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] (f : 𝕜 → E) (a b : 𝕜) (n : ℕ) :
    ∑ j ∈ Finset.range n, (b - a) ^ j • (Function.swap dslope a)^[j] f a +
      (b - a) ^ n • (Function.swap dslope a)^[n] f b = f b := by
  induction n generalizing f with
  | zero => simp
  | succ n ih =>
    simp only [Finset.sum_range_succ', Function.iterate_succ_apply, pow_succ', mul_smul,
      ← Finset.smul_sum, pow_zero, one_smul, Function.iterate_zero_apply]
    rw [add_right_comm, ← smul_add, ih]
    exact eq_sub_iff_add_eq.1 (sub_smul_dslope f a b)

/-- **Product rule for divided differences.** If `f` and `g` are differentiable at `a`, then
`dslope (f * g) a b = f a * dslope g a b + dslope f a b * g b` for every `b`. -/
theorem dslope_mul {𝕜 A : Type*} [NontriviallyNormedField 𝕜] [NormedRing A] [NormedAlgebra 𝕜 A]
    {f g : 𝕜 → A} {a : 𝕜} (hf : DifferentiableAt 𝕜 f a) (hg : DifferentiableAt 𝕜 g a) (b : 𝕜) :
    dslope (f * g) a b = f a * dslope g a b + dslope f a b * g b := by
  rcases eq_or_ne b a with rfl | hb
  · rw [dslope_same, dslope_same, dslope_same, deriv_mul hf hg, add_comm]
  · simp only [dslope_of_ne _ hb, slope_def_module, Pi.mul_apply, mul_smul_comm, smul_mul_assoc,
      ← smul_add]
    congr 1
    noncomm_ring

/-- Divided differences at `a` of functions with the same germ at `a` have the same germ at `a`. -/
theorem _root_.Filter.EventuallyEq.dslope {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] {f g : 𝕜 → E} {a : 𝕜} (h : f =ᶠ[nhds a] g) :
    dslope f a =ᶠ[nhds a] dslope g a := by
  filter_upwards [h] with b hb
  rcases eq_or_ne b a with rfl | hba
  · rw [dslope_same, dslope_same, h.deriv_eq]
  · rw [dslope_of_ne _ hba, dslope_of_ne _ hba, slope_def_module, slope_def_module, hb,
      h.eq_of_nhds]

/-- A local factorization by a coordinate difference identifies the coordinate divided
difference with its factor. On the base hyperplane only continuity of the factor's
one-dimensional slices is needed; the index type can be infinite. -/
theorem eventuallyEq_dslope_update_of_factorization {𝕜 ι F : Type*}
    [NontriviallyNormedField 𝕜] [DecidableEq ι]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {f g : (ι → 𝕜) → F} {x : ι → 𝕜} {i : ι}
    (hg : ∀ᶠ z in nhds x, z i = x i →
      ContinuousAt (fun w ↦ g (Function.update z i w)) (x i))
    (hfg : (fun z ↦ f z - f (Function.update z i (x i))) =ᶠ[nhds x]
      fun z ↦ (z i - x i) • g z) :
    (fun z ↦ dslope (fun w ↦ f (Function.update z i w)) (x i) (z i)) =ᶠ[nhds x] g := by
  filter_upwards [hfg.eventually_nhds, hg] with z hz hgz
  by_cases hzi : z i = x i
  · have huz : Function.update z i (x i) = z := by rw [← hzi, Function.update_eq_self]
    have hu : ContinuousAt (Function.update z i) (x i) :=
      continuousAt_const.update i continuousAt_id
    have heq := hu.tendsto.eventually (huz ▸ hz)
    have heq' : (fun w ↦ f (Function.update z i w) - f z) =ᶠ[nhds (x i)]
        (fun w ↦ (w - x i) • g (Function.update z i w)) := by
      filter_upwards [heq] with w hw
      simpa only [Function.update_self, Function.update_idem, huz] using hw
    have hd : HasDerivAt (fun w ↦ (w - x i) • g (Function.update z i w))
        (g z) (x i) := by
      simpa only [id_eq, one_smul, huz] using
        ((hasDerivAt_id (x i)).sub_const (x i)).smul_of_eq_zero (hgz hzi) (sub_self (x i))
    have hd' : HasDerivAt (fun w ↦ f (Function.update z i w)) (g z) (x i) :=
      (hasDerivAt_sub_const_iff (f z)).mp (hd.congr_of_eventuallyEq heq')
    simpa only [hzi, dslope_same] using hd'.deriv
  · have hmul : (z i - x i) •
        dslope (fun w ↦ f (Function.update z i w)) (x i) (z i) =
          (z i - x i) • g z := by
      rw [sub_smul_dslope, Function.update_eq_self]
      exact mem_of_mem_nhds hz
    exact smul_right_injective _ (sub_ne_zero.mpr hzi) hmul

end TauCeti
