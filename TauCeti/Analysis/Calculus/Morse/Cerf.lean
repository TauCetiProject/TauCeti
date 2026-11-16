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
import TauCeti.Analysis.Calculus.Sard.OutermostStratum
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
  vanish, `∂ₜ (d(f t)_x) v ≠ 0`: a degenerate critical point moves with nonzero speed in the
  parameter.

These are the corank-one and speed conditions of a birth–death point. The model family
`x³ / 3 - t x` of `TauCeti.Analysis.Calculus.Morse.BirthDeath` is transverse at its degenerate
critical point (`TauCeti.surjective_fderiv_fderiv_birthDeathPotential`), whereas the constant
family `x³ / 3` is not (`TauCeti.not_surjective_fderiv_fderiv_cube`).

Genericity is proved as in `TauCeti.Analysis.Calculus.Morse.Generic`. Subtracting a linear
functional `a` from every member of the family shifts `G` by the constant `a` and leaves its
derivative alone (`TauCeti.fderiv_fderiv_sub_eq`). So the perturbed family `f t - a` is transverse
at all of its critical points exactly when `a` is a regular value of `G`. The map `G` goes from a
space of dimension `dim E + 1` to one of dimension `dim E`, so the Morse–Sard theorem
`TauCeti.addHaar_image_criticalPoints_eq_zero` applies once `G` is `C²`, that is once the family
is jointly `C³`. Hence for almost every `a` the family `f t - a` is transverse at all of its
critical points (`TauCeti.ae_forall_surjective_fderiv_fderiv_sub`). Unlike the Morse case, one
derivative more than the Hessian is needed, because the source of `G` has one dimension more than
its target.

The remaining conditions of Cerf's theorem, that the third derivative along the kernel of a
degenerate Hessian is nonzero and that the degenerate parameters are isolated, need perturbations
by quadratic functions as well and are not treated here.

## Main declarations

* `TauCeti.surjective_fderiv_fderiv_iff`: a family is transverse at `(t, x)` exactly when no nonzero
  vector is killed by both the Hessian and the parameter derivative of the differential.
* `TauCeti.finrank_ker_fderiv_fderiv_le_one`: at a transverse point the Hessian has corank at most
  one.
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

/-- The parametrized differential `(t, x) ↦ d(f t)_x` of a family that is jointly `C^(n + 1)` is
`C^n`. -/
private theorem contDiffAt_fderiv_uncurry {n : ℕ} {z : ℝ × E}
    (hf : ContDiffAt ℝ (n + 1) (uncurry f) z) :
    ContDiffAt ℝ n (fun w : ℝ × E ↦ fderiv ℝ (f w.1) w.2) z :=
  ContDiffAt.fderiv (f := fun w : ℝ × E ↦ f w.1) (g := Prod.snd)
    (hf.comp (z, z.2) (contDiffAt_fst.fst.prodMk contDiffAt_snd)) contDiffAt_snd le_rfl

/-- Subtracting a functional from every member of a family keeps it jointly `C^n`. -/
private theorem contDiffAt_uncurry_sub {n : WithTop ℕ∞} {z : ℝ × E}
    (hf : ContDiffAt ℝ n (uncurry f) z) (a : StrongDual ℝ E) :
    ContDiffAt ℝ n (uncurry fun s y ↦ f s y - a y) z :=
  hf.sub (a.contDiff.contDiffAt.comp z contDiffAt_snd)

/-- **The derivative of the parametrized differential** `(t, x) ↦ d(f t)_x` at `(t, x)` sends
`(τ, ξ)` to `τ • ∂ₜ (d(f t)_x) + Hess(f t)_x ξ`. -/
theorem fderiv_fderiv_apply (hf : ContDiffAt ℝ 2 (uncurry f) (t, x)) (p : ℝ × E) :
    fderiv ℝ (fun w : ℝ × E ↦ fderiv ℝ (f w.1) w.2) (t, x) p =
      p.1 • deriv (fun s ↦ fderiv ℝ (f s) x) t + fderiv ℝ (fderiv ℝ (f t)) x p.2 := by
  set G : ℝ × E → StrongDual ℝ E := fun w ↦ fderiv ℝ (f w.1) w.2
  have hG : HasFDerivAt G (fderiv ℝ G (t, x)) (t, x) :=
    ((contDiffAt_fderiv_uncurry (n := 1) hf).differentiableAt one_ne_zero).hasFDerivAt
  -- The two partial derivatives of `G` are the restrictions of its derivative to the axes. The
  -- composites `G ∘ (·, x)` and `G ∘ (t, ·)` are `s ↦ d(f s)_x` and `d(f t)` by definition of `G`.
  have hpar : deriv (fun s ↦ fderiv ℝ (f s) x) t = fderiv ℝ G (t, x) ((1 : ℝ), (0 : E)) := by
    have h := hG.comp_hasDerivAt t (HasDerivAt.prodMk (hasDerivAt_id' t) (hasDerivAt_const t x))
    exact h.deriv
  have hfib : fderiv ℝ (fderiv ℝ (f t)) x = fderiv ℝ G (t, x) ∘L ContinuousLinearMap.inr ℝ ℝ E :=
    (hG.comp x (hasFDerivAt_prodMk_right t x)).fderiv
  have hp : p = p.1 • ((1 : ℝ), (0 : E)) + ((0 : ℝ), p.2) := by ext <;> simp
  conv_lhs => rw [hp, map_add, map_smul]
  rw [hpar, hfib, ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply]

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
    have hd : DifferentiableAt ℝ (f w.1) w.2 :=
      ((hw.comp w.2 ((contDiffAt_const (c := w.1)).prodMk contDiffAt_id)).differentiableAt
        one_ne_zero)
    simpa using fderiv_fun_sub hd a.differentiableAt
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

/-- **For almost every functional `a`, the family `f t - a` is transverse at all of its critical
points.** Let `f t` be a family of functions on a finite-dimensional real normed space `E`, jointly
`C³` at every point of a set `W ⊆ ℝ × E`. For a Haar measure `ν` on the dual of `E`, for
`ν`-almost every `a`, at every point `(t, x) ∈ W` at which `x` is a critical point of `f t - a`, the
derivative of the parametrized differential `(t, x) ↦ d(f t - a)_x` is onto.

The parametrized differential of `f t - a` is that of `f t` shifted by `a`, so the exceptional
functionals are the critical values on `W` of `(t, x) ↦ d(f t)_x`, a `C²` map from a space of
dimension `dim E + 1` to one of dimension `dim E`. They form a null set by the Morse–Sard
theorem. -/
theorem ae_forall_surjective_fderiv_fderiv_sub [MeasurableSpace (StrongDual ℝ E)]
    [BorelSpace (StrongDual ℝ E)] (ν : Measure (StrongDual ℝ E)) [ν.IsAddHaarMeasure]
    {W : Set (ℝ × E)} (hf : ∀ z ∈ W, ContDiffAt ℝ 3 (uncurry f) z) :
    ∀ᵐ a ∂ν, ∀ z ∈ W, fderiv ℝ (fun y ↦ f z.1 y - a y) z.2 = 0 →
      Surjective (fderiv ℝ (fun w : ℝ × E ↦ fderiv ℝ (fun y ↦ f w.1 y - a y) w.2) z) := by
  set G : ℝ × E → StrongDual ℝ E := fun w ↦ fderiv ℝ (f w.1) w.2
  have hG : ∀ z ∈ W, ContDiffAt ℝ 2 G z := fun z hz ↦ contDiffAt_fderiv_uncurry (hf z hz)
  have hnull : ν (G '' (W ∩ {z | ¬ Surjective (fderiv ℝ G z)})) = 0 := by
    refine addHaar_image_criticalPoints_eq_zero ν hG ?_
    rw [Module.finrank_prod, Module.finrank_self, ContinuousLinearMap.dual_finrank_eq]
    norm_num
  rw [ae_iff]
  refine measure_mono_null (fun a ha ↦ ?_) hnull
  obtain ⟨z, hzW, hz0, hzs⟩ : ∃ z ∈ W, fderiv ℝ (fun y ↦ f z.1 y - a y) z.2 = 0 ∧
      ¬ Surjective (fderiv ℝ (fun w : ℝ × E ↦ fderiv ℝ (fun y ↦ f w.1 y - a y) w.2) z) := by
    simpa using ha
  have hf1 : ContDiffAt ℝ 1 (uncurry f) z := (hf z hzW).of_le (by norm_num)
  have hd : DifferentiableAt ℝ (f z.1) z.2 :=
    (hf1.comp z.2 ((contDiffAt_const (c := z.1)).prodMk contDiffAt_id)).differentiableAt
      one_ne_zero
  rw [fderiv_fderiv_sub_eq hf1 a] at hzs
  refine ⟨z, ⟨hzW, hzs⟩, ?_⟩
  have h := fderiv_fun_sub hd a.differentiableAt
  rw [hz0, ContinuousLinearMap.fderiv] at h
  exact (sub_eq_zero.1 h.symm)

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

/-- **For almost every functional `a`, the degenerate critical points of `f t - a` move with
nonzero speed in the parameter.** At every critical point `(t, x) ∈ W` of `f t - a` and for every
nonzero `v` in the kernel of the Hessian there, the parameter derivative `∂ₜ (d(f t - a)_x) v` is
nonzero. This holds on every set `W ⊆ ℝ × E` at whose points the family is jointly `C³`. -/
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

/-- The differential of the birth–death potential `x ↦ x³ / 3 - s x` at `y` is multiplication by
`y² - s`. -/
private theorem fderiv_birthDeathPotential_eq (s : ℝ) :
    fderiv ℝ (birthDeathPotential s) = fun y ↦ (y ^ 2 - s) • ContinuousLinearMap.id ℝ ℝ := by
  funext y
  ext
  simp [← toSpanSingleton_deriv]

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
    simp_rw [fderiv_birthDeathPotential_eq]
    exact ((hasDerivAt_id' (0 : ℝ)).const_sub _).smul_const (ContinuousLinearMap.id ℝ ℝ)
  simpa [hd.deriv] using hv

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
    rw [fderiv_birthDeathPotential_eq]
    simpa using ((hasDerivAt_pow 2 (0 : ℝ)).sub_const 0).smul_const (ContinuousLinearMap.id ℝ ℝ)
  simp [← toSpanSingleton_deriv, hd.deriv]

end TauCeti
