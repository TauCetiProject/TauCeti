/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Geometry.Manifold.ContMDiffMap

/-!
# Basic lemmas on bundled `C^n` maps

This file evaluates Mathlib's basic bundled `C^n` maps (`ContMDiffMap.id`, `ContMDiffMap.const`,
`ContMDiffMap.fst`, `ContMDiffMap.snd`, and `ContMDiffMap.prodMk`) pointwise, and defines the
`C^n` function `e^{t f}` of a real `C^n` function `f` (`ContMDiffMap.expMul`), with inverse
`e^{-t f}` (`ContMDiffMap.expMul_mul_expMul_neg`). A continuous map is a `C⁰` map
(`ContMDiffMap.ofContinuous`), with the order written as the cast of the natural number `0`.
-/

public section

open scoped Manifold

namespace ContMDiffMap

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {H' : Type*} [TopologicalSpace H']
  {I' : ModelWithCorners 𝕜 E' H'} {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] {G : Type*} [TopologicalSpace G]
  {J : ModelWithCorners 𝕜 F G} {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  {n : WithTop ℕ∞}

/-- The identity `C^n` map evaluates to the identity at every point. -/
@[simp, grind =]
theorem id_apply (x : M) : (ContMDiffMap.id : C^n⟮I, M; I, M⟯) x = x :=
  rfl

/-- The constant `C^n` map with value `y` takes the value `y` at every point. -/
@[simp, grind =]
theorem const_apply (y : M') (x : M) : (const y : C^n⟮I, M; I', M'⟯) x = y :=
  rfl

/-- The first projection `C^n` map evaluates to `Prod.fst`. -/
@[simp, grind =]
theorem fst_apply (p : M × M') : (fst : C^n⟮I.prod I', M × M'; I, M⟯) p = p.1 :=
  rfl

/-- The second projection `C^n` map evaluates to `Prod.snd`. -/
@[simp, grind =]
theorem snd_apply (p : M × M') : (snd : C^n⟮I.prod I', M × M'; I', M'⟯) p = p.2 :=
  rfl

/-- The product of two `C^n` maps evaluates to the pair of their values. -/
@[simp, grind =]
theorem prodMk_apply (f : C^n⟮J, N; I, M⟯) (g : C^n⟮J, N; I', M'⟯) (x : N) :
    f.prodMk g x = (f x, g x) :=
  rfl

/-- A continuous map as a `C⁰` map, with the order written as the cast of the natural number `0`,
the form in which `TauCeti.CompactChartAtlas.CkHolderSpace 0` asks for it. -/
def ofContinuous (f : M → M') (hf : Continuous f) : C^(0 : ℕ)⟮I, M; I', M'⟯ :=
  ⟨f, by
    rw [Nat.cast_zero]
    exact contMDiff_zero_iff.mpr hf⟩

@[simp]
theorem coe_ofContinuous (f : M → M') (hf : Continuous f) :
    ⇑(ofContinuous (I := I) (I' := I') f hf) = f :=
  (rfl)

section Exp

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {n : WithTop ℕ∞}

/-- The `C^n` function `e^{t f}` of a real `C^n` function `f`. -/
noncomputable def expMul (f : C^n⟮I, M; ℝ⟯) (t : ℝ) : C^n⟮I, M; ℝ⟯ :=
  ⟨fun x ↦ Real.exp (t * f x),
    ((Real.contDiff_exp.comp (contDiff_const.mul contDiff_id)).comp_contMDiff f.contMDiff :)⟩

/-- The value of `e^{t f}` at `x` is `Real.exp (t * f x)`. -/
@[simp]
theorem expMul_apply (f : C^n⟮I, M; ℝ⟯) (t : ℝ) (x : M) :
    expMul f t x = Real.exp (t * f x) :=
  (rfl)

/-- `e^{t f} e^{-t f} = 1`. -/
theorem expMul_mul_expMul_neg (f : C^n⟮I, M; ℝ⟯) (t : ℝ) (x : M) :
    expMul f t x * expMul f (-t) x = 1 := by
  rw [expMul_apply, expMul_apply, ← Real.exp_add, neg_mul, add_neg_cancel, Real.exp_zero]

end Exp

end ContMDiffMap
