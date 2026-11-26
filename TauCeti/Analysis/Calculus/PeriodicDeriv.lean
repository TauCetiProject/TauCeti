/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.Periodic
public import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Calculus.LogDeriv

import Mathlib.Algebra.Order.ToIntervalMod
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Topology.EMetricSpace.Lipschitz
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Periodicity of the derivative and the logarithmic derivative

Differentiation commutes with translation of the domain, so the Fréchet and the
one-variable derivative of a periodic function are periodic with the same period, and
hence so are the iterated and the logarithmic derivatives. All these statements are
unconditional: `fderiv`, `deriv`, and with them `iteratedDeriv` and `logDeriv` take their junk
values at non-differentiable points, and the translation identities hold there too.

These extensions of Mathlib's periodicity API live in the root `Function` namespace as
`Periodic.*`, so that `hf.deriv` and its analogues resolve by receiver notation. They remain
protected so that opening `Function.Periodic` does not shadow `deriv` and `logDeriv` themselves.

## Main declarations

* `Function.Periodic.fderiv`: the Fréchet derivative of a periodic function is
  periodic.
* `Function.Periodic.iteratedFDeriv`: the iterated Fréchet derivatives of a periodic function are
  periodic.
* `TauCeti.periodic_fderiv_of_apply_add_eq_add`: the Fréchet derivative of a function with
  `f (x + c) = f x + d` is `c`-periodic.
* `TauCeti.periodic_deriv_of_apply_add_eq_add`: its one-variable form; for instance the derivative
  of a lift of a degree one circle map is `1`-periodic.
* `Function.Periodic.deriv`: the derivative of a periodic function is periodic.
* `Function.Periodic.iteratedDeriv`: the iterated derivatives of a periodic function are
  periodic.
* `Function.Periodic.logDeriv`: the logarithmic derivative of a periodic
  function is periodic.
* `Function.Periodic.exists_lipschitzWith`: a continuously differentiable periodic function of a
  real variable is Lipschitz.
* `TauCeti.fderiv_add_eq_smul`: a scalar twist `f (x + c) = a • f x` under translation, by a
  scalar from any division semiring acting on the codomain, passes to the Fréchet derivative.
* `TauCeti.fderiv_apply_eq_zero_of_forall_periodic_smul`: a function invariant under all
  translations along a vector `v` has derivative vanishing on `v`.
* `TauCeti.fderiv_add_snd_of_periodic_snd`: a map on a product of period `c` in the second
  coordinate has a Fréchet derivative of period `c` in it.
* `TauCeti.exists_mem_Ico_fderiv_comp_add_right_eq`: for such a map on `E × ℝ`, translation in
  the first coordinate moves every point to `{0} × [0, c)` without changing the derivative.
* `TauCeti.hasDerivAt_of_periodic_of_hasDerivWithinAt`: a periodic function solving `x' = Y` for a
  periodic `Y` within a single closed period interval `[a, a + T]` solves it everywhere.
-/

public section

namespace TauCeti

/-- The Fréchet derivative of a function with `f (x + c) = f x + d` is `c`-periodic: translating
the argument by `c` only adds the constant `d`. For `d = 0` this is `Function.Periodic.fderiv`. -/
theorem periodic_fderiv_of_apply_add_eq_add {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {f : E → F} {c : E} {d : F} (h : ∀ x, f (x + c) = f x + d) :
    Function.Periodic (fderiv 𝕜 f) c := fun x ↦ by
  rw [← fderiv_comp_add_right, funext h, fderiv_add_const]

/-- The derivative of a function with `f (x + c) = f x + d`, such as a lift of a degree one circle
map (`c = d = 1`), is `c`-periodic. This is the one-variable form of
`TauCeti.periodic_fderiv_of_apply_add_eq_add`; for `d = 0` it is `Function.Periodic.deriv`. -/
theorem periodic_deriv_of_apply_add_eq_add {𝕜 F : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] {f : 𝕜 → F} {c : 𝕜} {d : F}
    (h : ∀ x, f (x + c) = f x + d) : Function.Periodic (deriv f) c := fun x ↦ by
  simp only [← fderiv_apply_one_eq_deriv, periodic_fderiv_of_apply_add_eq_add h x]

end TauCeti

namespace Function

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

/-- The Fréchet derivative of a periodic function is periodic. -/
protected theorem Periodic.fderiv {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] {f : E → F} {c : E}
    (hf : Periodic f c) : Periodic (fderiv 𝕜 f) c := fun x ↦ by
  rw [← fderiv_comp_add_right, hf.funext]

/-- The iterated Fréchet derivatives of a periodic function are periodic. -/
protected theorem Periodic.iteratedFDeriv {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] {f : E → F} {c : E}
    (hf : Periodic f c) (n : ℕ) : Periodic (iteratedFDeriv 𝕜 n f) c := fun x ↦ by
  rw [← congr_fun (iteratedFDeriv_comp_add_right' n c) x, hf.funext]

/-- The derivative of a periodic function is periodic. -/
protected theorem Periodic.deriv {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {f : 𝕜 → F} {c : 𝕜} (hf : Periodic f c) : Periodic (deriv f) c :=
  TauCeti.periodic_deriv_of_apply_add_eq_add (d := 0) fun x ↦ by rw [hf x, add_zero]

/-- The iterated derivatives of a periodic function are periodic. -/
protected theorem Periodic.iteratedDeriv {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {f : 𝕜 → F} {c : 𝕜} (hf : Periodic f c) (n : ℕ) : Periodic (iteratedDeriv n f) c := fun x ↦ by
  simp only [iteratedDeriv_eq_iteratedFDeriv, hf.iteratedFDeriv n x]

/-- The logarithmic derivative of a periodic function is periodic. -/
protected theorem Periodic.logDeriv {𝕜' : Type*} [NontriviallyNormedField 𝕜']
    [NormedAlgebra 𝕜 𝕜'] {f : 𝕜 → 𝕜'} {c : 𝕜} (hf : Periodic f c) :
    Periodic (logDeriv f) c :=
  hf.deriv.div hf

/-- **A periodic `C¹` function is Lipschitz.** A continuously differentiable periodic function of
a real variable with nonzero period is Lipschitz. -/
theorem Periodic.exists_lipschitzWith {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : ℝ → F} {c : ℝ} (hf : Periodic f c) (hc : c ≠ 0) (hf₁ : ContDiff ℝ 1 f) :
    ∃ K, LipschitzWith K f := by
  obtain ⟨C, hC⟩ :=
    (hf.deriv.isBounded_of_continuous hc (hf₁.continuous_deriv le_rfl)).exists_norm_le
  refine ⟨C.toNNReal,
    lipschitzWith_of_nnNorm_deriv_le (hf₁.differentiable one_ne_zero) fun x ↦ ?_⟩
  rw [← NNReal.coe_le_coe, coe_nnNorm]
  exact (hC _ (Set.mem_range_self x)).trans (Real.le_coe_toNNReal C)

end Function

namespace TauCeti

/-- A scalar twist under translation, `f (x + c) = a • f x`, passes to the Fréchet derivative.
The scalar `a` may come from any division semiring `R` acting on `F` compatibly with `𝕜`, such as
a phase `a : ℂ` for a complex-valued function differentiated over `ℝ`. For `a = 1` this is
`Function.Periodic.fderiv`, and for `a = -1` it covers antiperiodic maps. -/
theorem fderiv_add_eq_smul {𝕜 R E F : Type*} [NontriviallyNormedField 𝕜] [DivisionSemiring R]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F] [Module R F]
    [SMulCommClass 𝕜 R F] [ContinuousConstSMul R F] {f : E → F} {c : E} {a : R}
    (h : ∀ x, f (x + c) = a • f x) (x : E) : fderiv 𝕜 f (x + c) = a • fderiv 𝕜 f x := by
  have hfun : (fun y ↦ f (y + c)) = a • f := funext h
  rw [← fderiv_comp_add_right, hfun, fderiv_const_smul_field, Pi.smul_apply]

/-- A function invariant under all translations along a vector `v`, that is periodic with every
period `τ • v`, has Fréchet derivative vanishing on `v` at every point. Since `fderiv` is again
invariant (`Function.Periodic.fderiv`), the same holds for the iterated derivatives. -/
theorem fderiv_apply_eq_zero_of_forall_periodic_smul {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {f : E → F} {v : E} (h : ∀ τ : 𝕜, Function.Periodic f (τ • v)) (x : E) :
    fderiv 𝕜 f x v = 0 := by
  by_cases hd : DifferentiableAt 𝕜 f x
  · -- Along the line `τ ↦ x + τ • v` the function `f` is constant, so its line derivative is `0`.
    have hline : HasLineDerivAt 𝕜 f 0 x v := by
      simpa [HasLineDerivAt, fun τ : 𝕜 ↦ h τ x] using hasDerivAt_const (0 : 𝕜) (f x)
    exact (hd.hasFDerivAt.hasLineDerivAt v).unique hline
  · simp [fderiv_zero_of_not_differentiableAt hd]

/-- A map on a product of period `c` in the second coordinate has a Fréchet derivative of period
`c` in it. This is `Function.Periodic.fderiv` for the period `(0, c)`. -/
theorem fderiv_add_snd_of_periodic_snd {𝕜 E F G : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    [NormedAddCommGroup G] [NormedSpace 𝕜 G] {f : E × F → G} {c : F}
    (hf : ∀ x y, f (x, y + c) = f (x, y)) (x : E) (y : F) :
    fderiv 𝕜 f (x, y + c) = fderiv 𝕜 f (x, y) := by
  have hp : Function.Periodic f (0, c) := fun ⟨p, q⟩ ↦ by simpa using hf p q
  simpa using hp.fderiv (x, y)

/-- **Moving a point of a periodic map into one period.** For a map `u` on `E × ℝ` of period
`c > 0` in the second coordinate, every point `z` is moved, by translation in the first coordinate
and periodicity in the second, to a point `(0, t)` with `t ∈ [0, c)` at which the translate
`w ↦ u (w + (z.1, 0))` has the same Fréchet derivative as `u` at `z`. -/
theorem exists_mem_Ico_fderiv_comp_add_right_eq {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {u : E × ℝ → F} {c : ℝ}
    (hc : 0 < c) (hu : ∀ x y, u (x, y + c) = u (x, y)) (z : E × ℝ) :
    ∃ t ∈ Set.Ico 0 c, fderiv ℝ (fun w ↦ u (w + (z.1, 0))) (0, t) = fderiv ℝ u z := by
  have hpd : Function.Periodic (fun t ↦ fderiv ℝ u (z.1, t)) c :=
    fun t ↦ fderiv_add_snd_of_periodic_snd hu _ t
  obtain ⟨t, ht, heq⟩ := hpd.exists_mem_Ico₀ hc z.2
  refine ⟨t, ht, ?_⟩
  rw [fderiv_comp_add_right, Prod.mk_add_mk, zero_add, add_zero]
  exact heq.symm

open Set in
/-- **Periodic solutions of a differential equation on one period.** Let `x` and `Y` be
`T`-periodic, with `T > 0`. If `x` has derivative `Y t` within `[a, a + T]` at every
`t ∈ [a, a + T]`, then `x` has derivative `Y t` at every `t`. -/
theorem hasDerivAt_of_periodic_of_hasDerivWithinAt {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {x Y : ℝ → E} {T : ℝ} (hT : 0 < T) (hxper : Function.Periodic x T)
    (hYper : Function.Periodic Y T) (a : ℝ)
    (hx : ∀ t ∈ Icc a (a + T), HasDerivWithinAt x (Y t) (Icc a (a + T)) t)
    (t : ℝ) : HasDerivAt x (Y t) t := by
  -- Translating by a multiple of the period, it suffices to treat `t ∈ [a, a + T)`.
  obtain ⟨r, hr, n, rfl⟩ : ∃ r ∈ Ico a (a + T), ∃ n : ℤ, t = r + n • T :=
    ⟨toIcoMod hT a t, toIcoMod_mem_Ico hT a t, toIcoDiv hT a t,
      (toIcoMod_add_toIcoDiv_zsmul hT a t).symm⟩
  suffices h : HasDerivAt x (Y r) r by
    have h' := HasDerivAt.comp_add_const (r + n • T) (-(n • T)) (by simpa using h)
    have hxn : (fun s ↦ x (s + -(n • T))) = x :=
      funext fun s ↦ by rw [← sub_eq_add_neg]; exact (hxper.zsmul n).sub_eq s
    rwa [hxn, ← (hYper.zsmul n) r] at h'
  have haT : a < a + T := lt_add_of_pos_right a hT
  rcases hr.1.eq_or_lt with rfl | h0
  · -- At `a`, glue the derivative from the right at `a` to the derivative from the left at `a + T`.
    have hright := (hx a ⟨le_rfl, haT.le⟩).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE haT)
    have hleft := ((hx (a + T) ⟨haT.le, le_rfl⟩).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsLE haT)).scomp_of_eq a
      (((hasDerivAt_id' a).add_const T).hasDerivWithinAt (s := Iic a))
      (fun s hs ↦ by simpa using hs) rfl
    have hxT : (x ∘ fun s ↦ s + T) = x := funext fun s ↦ hxper s
    rw [hxT, one_smul, hYper a] at hleft
    simpa using hleft.union hright
  · exact (hx r ⟨hr.1, hr.2.le⟩).hasDerivAt (Icc_mem_nhds h0 hr.2)

end TauCeti

end
