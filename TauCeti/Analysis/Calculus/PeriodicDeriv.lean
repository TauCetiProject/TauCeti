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
import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Topology.EMetricSpace.Lipschitz
import Mathlib.Topology.Instances.Real.Lemmas
import TauCeti.Analysis.Calculus.FDeriv.ConstantDirection

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
* `TauCeti.periodic_deriv_of_apply_add_eq_add`: the derivative of a function with
  `f (x + c) = f x + d`, such as a lift of a degree one circle map, is `c`-periodic.
* `Function.Periodic.deriv`: the derivative of a periodic function is periodic.
* `Function.Periodic.iteratedDeriv`: the iterated derivatives of a periodic function are
  periodic.
* `Function.Periodic.logDeriv`: the logarithmic derivative of a periodic
  function is periodic.
* `Function.Periodic.exists_lipschitzWith`: a continuously differentiable periodic function of a
  real variable is Lipschitz.
* `TauCeti.fderiv_add_eq_smul`: a scalar twist `f (x + c) = a • f x` under translation passes to
  the Fréchet derivative.
* `TauCeti.fderiv_apply_eq_zero_of_forall_periodic_smul`: a function invariant under all
  translations along a vector `v` has derivative vanishing on `v`.
* `TauCeti.fderiv_add_snd_of_periodic_snd`: a map on a product of period `c` in the second
  coordinate has a Fréchet derivative of period `c` in it.
* `TauCeti.hasDerivAt_of_periodic_of_hasDerivWithinAt`: a periodic function solving `x' = Y` for a
  periodic `Y` within a single period solves it everywhere.
-/

public section

namespace TauCeti

/-- The derivative of a function with `f (x + c) = f x + d`, such as a lift of a degree one circle
map (`c = d = 1`), is `c`-periodic. For `d = 0` this is `Function.Periodic.deriv`. -/
theorem periodic_deriv_of_apply_add_eq_add {𝕜 F : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] {f : 𝕜 → F} {c : 𝕜} {d : F}
    (h : ∀ x, f (x + c) = f x + d) : Function.Periodic (deriv f) c := fun x ↦ by
  rw [← deriv_comp_add_const, funext h, deriv_add_const]

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
    {f : 𝕜 → F} {c : 𝕜} (hf : Periodic f c) (n : ℕ) : Periodic (iteratedDeriv n f) c := by
  induction n with
  | zero => simpa using hf
  | succ n ih => simpa only [iteratedDeriv_succ] using ih.deriv

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
For `a = 1` this is `Function.Periodic.fderiv`, and for `a = -1` it covers antiperiodic maps. -/
theorem fderiv_add_eq_smul {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F] {f : E → F} {c : E} {a : 𝕜}
    (h : ∀ x, f (x + c) = a • f x) (x : E) : fderiv 𝕜 f (x + c) = a • fderiv 𝕜 f x := by
  have hfun : (fun y ↦ f (y + c)) = a • f := funext h
  rcases eq_or_ne a 0 with rfl | ha
  · have hf : f = 0 := funext fun y ↦ by simpa using h (y - c)
    simp [hf]
  · let _ := invertibleOfNonzero ha
    rw [← fderiv_comp_add_right, hfun, fderiv_const_smul_of_invertible]

/-- A function invariant under all translations along a vector `v`, that is periodic with every
period `τ • v`, has Fréchet derivative vanishing on `v` at every point. Since `fderiv` is again
invariant (`Function.Periodic.fderiv`), the same holds for the iterated derivatives. Such an `f`
is even along every line in the direction `v` (`fderiv_apply_eq_zero_of_apply_add_smul_neg`). -/
theorem fderiv_apply_eq_zero_of_forall_periodic_smul {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} {v : E}
    (h : ∀ τ : ℝ, Function.Periodic f (τ • v)) (x : E) : fderiv ℝ f x v = 0 :=
  fderiv_apply_eq_zero_of_apply_add_smul_neg v fun τ ↦ (h τ x).trans (h (-τ) x).symm

/-- A map on a product of period `c` in the second coordinate has a Fréchet derivative of period
`c` in it. This is `Function.Periodic.fderiv` for the period `(0, c)`. -/
theorem fderiv_add_snd_of_periodic_snd {𝕜 E F G : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    [NormedAddCommGroup G] [NormedSpace 𝕜 G] {f : E × F → G} {c : F}
    (hf : ∀ x y, f (x, y + c) = f (x, y)) (x : E) (y : F) :
    fderiv 𝕜 f (x, y + c) = fderiv 𝕜 f (x, y) := by
  have hp : Function.Periodic f (0, c) := fun ⟨p, q⟩ ↦ by simpa using hf p q
  simpa using hp.fderiv (x, y)

open Set in
/-- **Periodic solutions of a differential equation on one period.** Let `x` and `Y` be
`T`-periodic, with `T > 0`. If `x` has derivative `Y t` within `[0, T]` at every `t ∈ [0, T]`,
then `x` has derivative `Y t` at every `t`. -/
theorem hasDerivAt_of_periodic_of_hasDerivWithinAt {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {x Y : ℝ → E} {T : ℝ} (hT : 0 < T) (hxper : Function.Periodic x T)
    (hYper : Function.Periodic Y T) (hx : ∀ t ∈ Icc 0 T, HasDerivWithinAt x (Y t) (Icc 0 T) t)
    (t : ℝ) : HasDerivAt x (Y t) t := by
  -- Translating by a multiple of the period, it suffices to treat `t ∈ [0, T)`.
  obtain ⟨r, hr, n, rfl⟩ : ∃ r ∈ Ico 0 T, ∃ n : ℤ, t = r + n • T :=
    ⟨toIcoMod hT 0 t, by simpa using toIcoMod_mem_Ico hT 0 t, toIcoDiv hT 0 t,
      (toIcoMod_add_toIcoDiv_zsmul hT 0 t).symm⟩
  suffices h : HasDerivAt x (Y r) r by
    have h' := HasDerivAt.comp_add_const (r + n • T) (-(n • T)) (by simpa using h)
    have hxn : (fun s ↦ x (s + -(n • T))) = x :=
      funext fun s ↦ by rw [← sub_eq_add_neg]; exact (hxper.zsmul n).sub_eq s
    rwa [hxn, ← (hYper.zsmul n) r] at h'
  rcases hr.1.eq_or_lt with rfl | h0
  · -- At `0`, glue the derivative from the right at `0` to the derivative from the left at `T`.
    have hright := (hx 0 ⟨le_rfl, hT.le⟩).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE hT)
    have hleft := ((hx T ⟨hT.le, le_rfl⟩).mono_of_mem_nhdsWithin (Icc_mem_nhdsLE hT)).scomp_of_eq
      0 (((hasDerivAt_id' (0 : ℝ)).add_const T).hasDerivWithinAt (s := Iic 0))
      (fun s hs ↦ by simpa using hs) (by simp)
    have hxT : (x ∘ fun s ↦ s + T) = x := funext fun s ↦ hxper s
    rw [hxT, one_smul, ← zero_add T, hYper 0] at hleft
    simpa using hleft.union hright
  · exact (hx r ⟨hr.1, hr.2.le⟩).hasDerivAt (Icc_mem_nhds h0 hr.2)

end TauCeti

end
