/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Haar.Basic
public import TauCeti.Analysis.Calculus.Morse.BirthDeath
-- Private: used only inside proofs.
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Prod
import TauCeti.Analysis.Calculus.ContDiff.Prod
import TauCeti.Analysis.Calculus.FDeriv.Add
import TauCeti.Analysis.Calculus.FDeriv.Prod
import TauCeti.Analysis.Calculus.LineDeriv.Basic
import TauCeti.Analysis.Fredholm.LevelSet.FiniteDimensional
import TauCeti.Analysis.Normed.Module.Annihilator
import TauCeti.Analysis.Normed.Module.FiniteDimension

/-!
# Generic one-parameter families have a transverse critical locus

A one-parameter family of functions `f t : E → ℝ` cannot in general be made Morse for every
parameter at once: as `t` varies, pairs of critical points are born and die, and at the parameter
of a birth or a death the family has a degenerate critical point. Cerf's theorem says that for a
generic family these degeneracies are as mild as possible. This file proves the first step of that
theorem on a finite-dimensional real normed space `E`: the critical locus of a generic family is
cut out transversally.

The critical points of the family are the zeros of the *parametrized differential*
`G (t, x) = d(f t)_x`, a map from `ℝ × E` to the dual of `E`. Its derivative at `(t, x)` is

`(τ, ξ) ↦ τ • ∂ₜ (d(f t)_x) + Hess(f t)_x ξ`,

and the family is transverse at a critical point when this derivative is surjective. Since the
Hessian is symmetric, its range is the annihilator of its kernel, and surjectivity says exactly
that no nonzero vector `v` lies both in the kernel of the Hessian and in the kernel of the parameter
derivative `∂ₜ (d(f t)_x)` (`ContinuousLinearMap.surjective_smul_add_apply_iff`,
`TauCeti.surjective_fderiv_fderiv_iff`). Two consequences follow at
every transverse critical point:

* the Hessian has corank at most one (`TauCeti.finrank_ker_fderiv_fderiv_le_one`);
* along a nonzero vector `v` of its kernel, the parameter derivative of the differential does not
  vanish, `∂ₜ (d(f t)_x) v ≠ 0`.

These are the corank-one and parameter-transversality conditions of a birth–death point. The
model family `x³ / 3 - t x` of `TauCeti.Analysis.Calculus.Morse.BirthDeath` is transverse at its
degenerate critical point (`TauCeti.surjective_fderiv_fderiv_birthDeathPotential`), whereas the
constant family `x³ / 3` is not (`TauCeti.not_surjective_fderiv_fderiv_birthDeathPotential_zero`).

Genericity is proved for any linear map `P` from a finite-dimensional space `Λ` to functions on
`E` that is jointly smooth in the parameter and the point and whose members realize every
differential at the points considered. Subtracting `P p` from every member of the family gives the
parametrized differential `Φ ((t, x), p) = d(f t - P p)_x`, whose derivative in the direction of
the parameter `p` is onto. For each `p`, the slice `(t, x) ↦ Φ ((t, x), p)` goes from `ℝ × E`, of
dimension `dim E + 1`, to the dual of `E`, of dimension `dim E`, so the parametric transversality
theorem `TauCeti.ae_isRegularParameterOn` applies once `Φ` is `C²`, that is once the family is
jointly `C³`. Hence for almost every `p` the family `f t - P p` is transverse at all of its
critical points (`TauCeti.ae_forall_surjective_fderiv_fderiv_sub_of_forall_exists_fderiv_eq`).
Unlike the Morse case, one derivative more than the Hessian is needed, because the source of each
slice has one dimension more than its target. The linear functionals themselves form such a
family, so for almost every `a` the family `f t - a` is transverse at all of its critical points
(`TauCeti.ae_forall_surjective_fderiv_fderiv_sub`). Subtracting `a` shifts `G` by the constant `a`
and leaves its derivative alone (`TauCeti.fderiv_fderiv_sub_eq`).

The cubic condition of Cerf's theorem, that the third derivative along the kernel of a degenerate
Hessian is nonzero, needs perturbations by quadratic and cubic functions as well and is proved in
`TauCeti.Analysis.Calculus.Morse.Cerf.Cubic`. The remaining condition, that the degenerate
parameters are isolated, is not treated here.

## Main declarations

* `TauCeti.surjective_fderiv_fderiv_iff`: a family is transverse at `(t, x)` exactly when no nonzero
  vector is killed by both the Hessian and the parameter derivative of the differential.
* `TauCeti.finrank_ker_fderiv_fderiv_le_one`: at a transverse point the Hessian has corank at most
  one.
* `TauCeti.ae_forall_surjective_fderiv_fderiv_sub_of_forall_exists_fderiv_eq`: for almost every
  member `P p` of a linear family of perturbations realizing every differential, the family
  `f t - P p` is transverse at all of its critical points.
* `TauCeti.ae_forall_surjective_fderiv_fderiv_sub`: **for almost every linear functional `a`, the
  family `f t - a` is transverse at all of its critical points.**
* `TauCeti.ae_forall_finrank_ker_fderiv_fderiv_sub_le_one`,
  `TauCeti.ae_forall_deriv_fderiv_sub_apply_ne_zero`: for almost every `a`, the Hessians of
  `f t - a` at its critical points have corank at most one, and the parameter derivative of the
  differential does not vanish on their kernels.
* `TauCeti.exists_norm_lt_forall_surjective_fderiv_fderiv_sub`: the perturbation can be taken
  arbitrarily small.

## References

* J. Cerf, *La stratification naturelle des espaces de fonctions différentiables réelles et le
  théorème de la pseudo-isotopie*, Publ. Math. IHÉS **39** (1970), 5–173, Chapter III.
* M. Hutchings, *Lecture notes on Morse homology (with an eye towards Floer theory and
  pseudoholomorphic curves)*, 2002, §4 (generic one-parameter families and bifurcations).
-/

public section

open Function MeasureTheory MeasureTheory.Measure Module Set Filter
open scoped Topology

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : ℝ → E → ℝ} {t : ℝ} {x : E}

/-! ### The derivative of the parametrized differential -/

/-- Subtracting a functional from every member of a family keeps it jointly `C^n`. -/
private theorem contDiffAt_uncurry_sub {n : WithTop ℕ∞} {z : ℝ × E}
    (hf : ContDiffAt ℝ n (uncurry f) z) (a : StrongDual ℝ E) :
    ContDiffAt ℝ n (uncurry fun s y ↦ f s y - a y) z :=
  hf.sub (a.contDiff.contDiffAt.comp z contDiffAt_snd)

/-- At a point where the family is jointly `C¹`, subtracting a functional `a` from `f s` shifts
its differential by `a`. -/
private theorem fderiv_sub_eq_of_contDiffAt {s : ℝ} {y : E}
    (hf : ContDiffAt ℝ 1 (uncurry f) (s, y)) (a : StrongDual ℝ E) :
    fderiv ℝ (fun y ↦ f s y - a y) y = fderiv ℝ (f s) y - a := by
  have hd : DifferentiableAt ℝ (f s) y :=
    (hf.comp y ((contDiffAt_const (c := s)).prodMk contDiffAt_id)).differentiableAt one_ne_zero
  simpa using fderiv_fun_sub hd a.differentiableAt

/-- **The derivative of the parametrized differential** `(t, x) ↦ d(f t)_x` at `(t, x)` sends
`(τ, ξ)` to `τ • ∂ₜ (d(f t)_x) + Hess(f t)_x ξ`. -/
theorem fderiv_fderiv_apply (hf : ContDiffAt ℝ 2 (uncurry f) (t, x)) (p : ℝ × E) :
    fderiv ℝ (fun w : ℝ × E ↦ fderiv ℝ (f w.1) w.2) (t, x) p =
      p.1 • deriv (fun s ↦ fderiv ℝ (f s) x) t + fderiv ℝ (fderiv ℝ (f t)) x p.2 := by
  have hG : DifferentiableAt ℝ (fun w : ℝ × E ↦ fderiv ℝ (f w.1) w.2) (t, x) :=
    (hf.fderiv_slice (m := 1) le_rfl).differentiableAt one_ne_zero
  rw [fderiv_apply_eq_fderiv_slice_left_add_fderiv_slice_right hG, fderiv_eq_smul_deriv]

/-- **Subtracting a functional does not change the derivative of the parametrized differential.**
Subtracting `a` from every member of the family shifts `(t, x) ↦ d(f t)_x` by the constant `a`
near any point at which the family is jointly `C¹`. -/
theorem fderiv_fderiv_sub_eq {z : ℝ × E} (hf : ContDiffAt ℝ 1 (uncurry f) z)
    (a : StrongDual ℝ E) :
    fderiv ℝ (fun w : ℝ × E ↦ fderiv ℝ (fun y ↦ f w.1 y - a y) w.2) z =
      fderiv ℝ (fun w : ℝ × E ↦ fderiv ℝ (f w.1) w.2) z := by
  have hev : (fun w : ℝ × E ↦ fderiv ℝ (fun y ↦ f w.1 y - a y) w.2) =ᶠ[𝓝 z]
      fun w ↦ fderiv ℝ (f w.1) w.2 - a := by
    filter_upwards [hf.eventually (by simp)] with w hw
    exact fderiv_sub_eq_of_contDiffAt hw a
  rw [hev.fderiv_eq, fderiv_sub_const]

/-! ### Transversality at a point -/

section FiniteDimensional

variable [FiniteDimensional ℝ E]

/-- **A family is transverse at `(t, x)` exactly when no nonzero vector lies in the kernels of both
the Hessian and the parameter derivative of the differential.** For a family that is jointly `C²`
near `(t, x)`, the derivative of the parametrized differential `(t, x) ↦ d(f t)_x` is onto exactly
when every `v` with `Hess(f t)_x v = 0` and `∂ₜ (d(f t)_x) v = 0` is zero. -/
theorem surjective_fderiv_fderiv_iff (hf : ContDiffAt ℝ 2 (uncurry f) (t, x)) :
    Surjective (fderiv ℝ (fun w : ℝ × E ↦ fderiv ℝ (f w.1) w.2) (t, x)) ↔
      ∀ v, fderiv ℝ (fderiv ℝ (f t)) x v = 0 → deriv (fun s ↦ fderiv ℝ (f s) x) t v = 0 →
        v = 0 := by
  have hft : ContDiffAt ℝ 2 (f t) x :=
    hf.comp x ((contDiffAt_const (c := t)).prodMk contDiffAt_id)
  rw [← ContinuousLinearMap.surjective_smul_add_apply_iff
    (fun u v ↦ hft.isSymmSndFDerivAt (by simp) u v), ← funext (fderiv_fderiv_apply hf)]

/-- **At a transverse point the Hessian has corank at most one.** If the derivative of the
parametrized differential `(t, x) ↦ d(f t)_x` is onto at `(t, x)`, the parameter derivative
`∂ₜ (d(f t)_x)` is injective on the kernel of the Hessian of `f t` at `x`, which therefore has
dimension at most one. -/
theorem finrank_ker_fderiv_fderiv_le_one (hf : ContDiffAt ℝ 2 (uncurry f) (t, x))
    (hs : Surjective (fderiv ℝ (fun w : ℝ × E ↦ fderiv ℝ (f w.1) w.2) (t, x))) :
    finrank ℝ (LinearMap.ker (fderiv ℝ (fderiv ℝ (f t)) x).toLinearMap) ≤ 1 := by
  have hk := (surjective_fderiv_fderiv_iff hf).1 hs
  let K := LinearMap.ker (fderiv ℝ (fderiv ℝ (f t)) x).toLinearMap
  let w : StrongDual ℝ E := deriv (fun s ↦ fderiv ℝ (f s) x) t
  have hinj : Injective ((w : E →ₗ[ℝ] ℝ) ∘ₗ K.subtype) :=
    (injective_iff_map_eq_zero _).2 fun v hv ↦ Subtype.ext (hk v v.2 hv)
  simpa using LinearMap.finrank_le_finrank_of_injective hinj

/-! ### Genericity -/

/-- **For almost every member of a rich linear family of perturbations, the family is transverse
at all of its critical points.** Let `f t` be a family of functions on a finite-dimensional real
normed space `E`, jointly `C³` at every point of a set `W ⊆ ℝ × E`, and let `P` be a linear map
from a finite-dimensional space `Λ` to functions on `E`, jointly `C³` in the parameter and the
point, whose members realize every differential at the points of `W`. For a Haar measure `ν` on
`Λ` and `ν`-almost every `p`, at every `(t, x) ∈ W` at which `x` is a critical point of
`f t - P p`, the derivative of the parametrized differential `(t, x) ↦ d(f t - P p)_x` is onto.

This is the parametric transversality theorem `TauCeti.ae_isRegularParameterOn` for the map
`((t, x), p) ↦ d(f t - P p)_x`, whose derivative in the direction of the parameter is onto. -/
theorem ae_forall_surjective_fderiv_fderiv_sub_of_forall_exists_fderiv_eq {Λ : Type*}
    [NormedAddCommGroup Λ] [NormedSpace ℝ Λ] [FiniteDimensional ℝ Λ] [MeasurableSpace Λ]
    [BorelSpace Λ] (ν : Measure Λ) [ν.IsAddHaarMeasure] {P : Λ →ₗ[ℝ] E → ℝ} {W : Set (ℝ × E)}
    (hf : ∀ z ∈ W, ContDiffAt ℝ 3 (uncurry f) z) (hP : ContDiff ℝ 3 fun q : Λ × E ↦ P q.1 q.2)
    (hjet : ∀ z ∈ W, ∀ a : E →L[ℝ] ℝ, ∃ q, fderiv ℝ (P q) z.2 = a) :
    ∀ᵐ p ∂ν, ∀ z ∈ W, fderiv ℝ (fun y ↦ f z.1 y - P p y) z.2 = 0 →
      Surjective (fderiv ℝ (fun w : ℝ × E ↦ fderiv ℝ (fun y ↦ f w.1 y - P p y) w.2) z) := by
  set G : (ℝ × E) × Λ → E →L[ℝ] ℝ := fun w ↦ fderiv ℝ (fun y ↦ f w.1.1 y - P w.2 y) w.1.2
  set U : Set ((ℝ × E) × Λ) := {w | w.1 ∈ W}
  -- `G` is `C²` at the points over `W`.
  have hGc : ∀ w ∈ U, ContDiffAt ℝ 2 G w := by
    rintro ⟨⟨t, x⟩, p⟩ hw
    exact (((hf (t, x) hw).sub_uncurry_prod hP.contDiffAt).fderiv_slice
      (m := 2) le_rfl).comp ((t, x), p)
        ((contDiffAt_fst.fst.prodMk contDiffAt_snd).prodMk contDiffAt_fst.snd)
  -- Its derivative in the direction of the coefficients is onto.
  have htotal : ∀ w ∈ U, G w = 0 → Surjective (fderiv ℝ G w) := by
    rintro ⟨⟨t, x⟩, p⟩ hw - a
    obtain ⟨q, hq⟩ := hjet (t, x) hw (-a)
    have hu : DifferentiableAt ℝ (fun y ↦ f t y - P p y) x :=
      (((hf (t, x) hw).sub_uncurry_prod hP.contDiffAt).comp x
        (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt (by norm_num)
    have hw' : DifferentiableAt ℝ (P q) x :=
      (hP.comp (contDiff_const.prodMk contDiff_id)).differentiable (by norm_num) x
    -- Along the line in the direction of `q`, the map `G` moves by `s • a`.
    refine ⟨((0, 0), q),
      ((hGc _ hw).differentiableAt (by norm_num)).fderiv_apply_eq_of_add_smul
        (.of_forall fun s ↦ ?_)⟩
    simp only [G, Prod.mk_add_mk, Prod.smul_mk, smul_zero, add_zero]
    rw [P.fderiv_sub_map_add_smul hu hw', hq, smul_neg, sub_neg_eq_add]
  have hreg := ae_isRegularParameterOn ν (U := U) (c := 0) (n := 2) (fun w hw _ ↦ hGc w hw)
    htotal (by
      rw [Module.finrank_prod, Module.finrank_self, ContinuousLinearMap.dual_finrank_eq]
      norm_num)
  filter_upwards [hreg] with p hp z hz hz0
  have hs := isRegularParameterOn_iff.1 hp z hz hz0
  rwa [← fderiv_slice_left ((hGc (z, p) hz).differentiableAt (by norm_num))] at hs

/-- **For almost every functional `a`, the family `f t - a` is transverse at all of its critical
points.** Let `f t` be a family of functions on a finite-dimensional real normed space `E`, jointly
`C³` at every point of a set `W ⊆ ℝ × E`. For a Haar measure `ν` on the dual of `E`, for
`ν`-almost every `a`, at every point `(t, x) ∈ W` at which `x` is a critical point of `f t - a`, the
derivative of the parametrized differential `(t, x) ↦ d(f t - a)_x` is onto.

This is the case of `TauCeti.ae_forall_surjective_fderiv_fderiv_sub_of_forall_exists_fderiv_eq`
in which the perturbations are the linear functionals themselves. -/
theorem ae_forall_surjective_fderiv_fderiv_sub [MeasurableSpace (StrongDual ℝ E)]
    [BorelSpace (StrongDual ℝ E)] (ν : Measure (StrongDual ℝ E)) [ν.IsAddHaarMeasure]
    {W : Set (ℝ × E)} (hf : ∀ z ∈ W, ContDiffAt ℝ 3 (uncurry f) z) :
    ∀ᵐ a ∂ν, ∀ z ∈ W, fderiv ℝ (fun y ↦ f z.1 y - a y) z.2 = 0 →
      Surjective (fderiv ℝ (fun w : ℝ × E ↦ fderiv ℝ (fun y ↦ f w.1 y - a y) w.2) z) := by
  simpa using ae_forall_surjective_fderiv_fderiv_sub_of_forall_exists_fderiv_eq ν
    (P := LinearMap.ltoFun ℝ E ℝ ℝ ∘ₗ ContinuousLinearMap.coeLM ℝ) hf
    (by simpa using contDiff_fst.clm_apply contDiff_snd) fun _ _ a ↦ ⟨a, by simp⟩

/-- **For almost every functional `a`, the Hessians of `f t - a` at its critical points have corank
at most one.** This holds on every set `W ⊆ ℝ × E` at whose points the family is jointly `C³`. -/
theorem ae_forall_finrank_ker_fderiv_fderiv_sub_le_one [MeasurableSpace (StrongDual ℝ E)]
    [BorelSpace (StrongDual ℝ E)] (ν : Measure (StrongDual ℝ E)) [ν.IsAddHaarMeasure]
    {W : Set (ℝ × E)} (hf : ∀ z ∈ W, ContDiffAt ℝ 3 (uncurry f) z) :
    ∀ᵐ a ∂ν, ∀ z ∈ W, fderiv ℝ (fun y ↦ f z.1 y - a y) z.2 = 0 →
      finrank ℝ (LinearMap.ker
        (fderiv ℝ (fderiv ℝ (fun y ↦ f z.1 y - a y)) z.2).toLinearMap) ≤ 1 := by
  filter_upwards [ae_forall_surjective_fderiv_fderiv_sub ν hf] with a ha z hz hz0
  exact finrank_ker_fderiv_fderiv_le_one (f := fun s y ↦ f s y - a y)
    (contDiffAt_uncurry_sub ((hf z hz).of_le (by norm_num)) a) (ha z hz hz0)

/-- **For almost every functional `a`, the parameter derivative of the differential of `f t - a`
does not vanish on the kernel of the Hessian at its critical points.** At every critical point
`(t, x) ∈ W` of `f t - a` and for every nonzero `v` in the kernel of the Hessian there, the
parameter derivative `∂ₜ (d(f t - a)_x) v` is nonzero. This holds on every set `W ⊆ ℝ × E` at
whose points the family is jointly `C³`. -/
theorem ae_forall_deriv_fderiv_sub_apply_ne_zero [MeasurableSpace (StrongDual ℝ E)]
    [BorelSpace (StrongDual ℝ E)] (ν : Measure (StrongDual ℝ E)) [ν.IsAddHaarMeasure]
    {W : Set (ℝ × E)} (hf : ∀ z ∈ W, ContDiffAt ℝ 3 (uncurry f) z) :
    ∀ᵐ a ∂ν, ∀ z ∈ W, fderiv ℝ (fun y ↦ f z.1 y - a y) z.2 = 0 → ∀ v ≠ 0,
      fderiv ℝ (fderiv ℝ (fun y ↦ f z.1 y - a y)) z.2 v = 0 →
        deriv (fun s ↦ fderiv ℝ (fun y ↦ f s y - a y) z.2) z.1 v ≠ 0 := by
  filter_upwards [ae_forall_surjective_fderiv_fderiv_sub ν hf] with a ha z hz hz0 v hv hHv hdv
  exact hv ((surjective_fderiv_fderiv_iff (f := fun s y ↦ f s y - a y)
    (contDiffAt_uncurry_sub ((hf z hz).of_le (by norm_num)) a)).1 (ha z hz hz0) v hHv hdv)

/-- **A family is made transverse at all of its critical points by an arbitrarily small linear
perturbation**: for every `ε > 0` there is a functional of operator norm less than `ε` whose
subtraction from every member of the family makes the derivative of the parametrized differential
onto at every critical point in `W`. No measurable structure appears in the statement: the Haar
measure that produces the perturbation is an auxiliary object of the proof. -/
theorem exists_norm_lt_forall_surjective_fderiv_fderiv_sub {W : Set (ℝ × E)}
    (hf : ∀ z ∈ W, ContDiffAt ℝ 3 (uncurry f) z) {ε : ℝ} (hε : 0 < ε) :
    ∃ a : StrongDual ℝ E, ‖a‖ < ε ∧ ∀ z ∈ W, fderiv ℝ (fun y ↦ f z.1 y - a y) z.2 = 0 →
      Surjective (fderiv ℝ (fun w : ℝ × E ↦ fderiv ℝ (fun y ↦ f w.1 y - a y) w.2) z) := by
  borelize (StrongDual ℝ E)
  obtain ⟨a, hmem, hball⟩ :=
    (dense_of_ae (ae_forall_surjective_fderiv_fderiv_sub (addHaar : Measure (StrongDual ℝ E))
      hf)).exists_mem_open Metric.isOpen_ball ⟨0, Metric.mem_ball_self hε⟩
  exact ⟨a, by simpa [Metric.mem_ball, dist_zero_right] using hball, hmem⟩

end FiniteDimensional

/-! ### The birth–death family -/

/-- **The birth–death family is transverse at its degenerate critical point.** The family
`x³ / 3 - t x` has a degenerate critical point at `(t, x) = (0, 0)`
(`TauCeti.not_isNondegenerateCriticalPoint_birthDeathPotential_zero`), yet the derivative of its
parametrized differential is onto there: the parameter derivative `∂ₜ (d(f t)_0) = -1` does not
vanish on the kernel of the Hessian. Transversality of the critical locus is weaker than being Morse
at every parameter. -/
theorem surjective_fderiv_fderiv_birthDeathPotential :
    Surjective (fderiv ℝ (fun w : ℝ × ℝ ↦ fderiv ℝ (birthDeathPotential w.1) w.2) (0, 0)) := by
  refine (surjective_fderiv_fderiv_iff contDiff_birthDeathPotential_uncurry.contDiffAt).2
    fun v _ hv ↦ ?_
  have hd : HasDerivAt (fun s ↦ fderiv ℝ (birthDeathPotential s) 0)
      ((-1 : ℝ) • ContinuousLinearMap.id ℝ ℝ) 0 := by
    simp_rw [fderiv_birthDeathPotential]
    exact ((hasDerivAt_id' (0 : ℝ)).const_sub _).smul_const (ContinuousLinearMap.id ℝ ℝ)
  rw [hd.deriv] at hv
  simpa using hv

/-- **The constant family `x³ / 3` is not transverse at its degenerate critical point.** Without
the parameter, the vector `1` lies in the kernels of both the Hessian of `x ↦ x³ / 3` at `0` and
the parameter derivative of the differential, which vanishes. -/
theorem not_surjective_fderiv_fderiv_birthDeathPotential_zero :
    ¬ Surjective (fderiv ℝ (fun w : ℝ × ℝ ↦ fderiv ℝ (birthDeathPotential 0) w.2) (0, 0)) := by
  rw [surjective_fderiv_fderiv_iff (f := fun _ ↦ birthDeathPotential 0)
    ((contDiff_birthDeathPotential 0).comp contDiff_snd).contDiffAt]
  intro h
  refine one_ne_zero (h 1 ?_ (by simp))
  have hd : HasDerivAt (fderiv ℝ (birthDeathPotential 0)) ((2 * 0 : ℝ) • ContinuousLinearMap.id ℝ ℝ)
      0 := by
    rw [funext (fderiv_birthDeathPotential 0)]
    simpa using ((hasDerivAt_pow 2 (0 : ℝ)).sub_const 0).smul_const (ContinuousLinearMap.id ℝ ℝ)
  simp [← toSpanSingleton_deriv, hd.deriv]

end TauCeti
